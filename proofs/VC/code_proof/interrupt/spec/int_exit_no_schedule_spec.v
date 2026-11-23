Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.lib.timer Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_timer_region.
Require Export Coq.Bool.Bool Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Export Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A smaller, already-masked specialization of the SAME OSIntExit C
    body.  The original full contract is retained separately.  The guard
    below is precisely the source's decision not to select a task after
    its nesting decrement; it includes boot, nested ISR and locked cases.
    No Timer, ready-table, Task or Event cells are acquired by this call.

    The caller already owns these three cells. Nested Save/Restore use
    the existing masked platform contract also used by OSTimeTick: they
    do not open or close the shared region. This is not an interrupt-entry
    acquisition rule, nor a proof of the later ARM exception return. *)
Definition os_int_exit_no_schedule_running (observed : bool) : Z :=
  if observed then 1 else 0.

Definition os_int_exit_no_schedule_addresses (sg : StableGlobVars)
  (running nesting locks : Z) : Prop :=
  running = sg.(g_OSRunning) /\ nesting = sg.(g_OSIntNesting) /\ locks = sg.(g_OSLockNesting).

Definition os_int_exit_no_schedule_cells (sg : StableGlobVars)
  (observed : bool) (counters : InterruptAbstractState) : Assertion :=
  sg.(g_OSRunning) # UChar |-> os_int_exit_no_schedule_running observed **
  store_int_state sg counters.

Definition os_int_exit_no_schedule_pre (platform : InterruptPlatformResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
  (observed : bool) (counters : InterruptAbstractState) : Assertion :=
  coq_prop (interrupt_exit_requests_schedule observed counters = false) &&
  (interrupt_platform_running platform invocation origin 192 **
   os_int_exit_no_schedule_cells sg observed counters).

Definition os_int_exit_no_schedule_post (platform : InterruptPlatformResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
  (observed : bool) (counters : InterruptAbstractState) : Assertion :=
  interrupt_platform_running platform invocation origin 192 **
  os_int_exit_no_schedule_cells sg observed (interrupt_exit_state observed counters).

Definition os_int_exit_no_schedule_counted (counters : InterruptAbstractState) : Z :=
  (interrupt_exit_state true counters).(intNesting).

Lemma os_int_exit_no_schedule_counted_guard : forall observed counters,
  os_int_exit_no_schedule_running observed = 1 ->
  interrupt_exit_requests_schedule observed counters = false ->
  os_int_exit_no_schedule_counted counters <> 0 \/ counters.(lockNesting) <> 0.
Proof.
  intros [] counters Hrunning Hschedule; [|discriminate].
  change (((os_int_exit_no_schedule_counted counters =? 0) &&
    (counters.(lockNesting) =? 0))%bool = false) in Hschedule.
  apply Bool.andb_false_iff in Hschedule.
  destruct Hschedule as [Hnesting|Hlock]; [left|right]; apply Z.eqb_neq; assumption.
Qed.

Lemma os_int_exit_no_schedule_open : forall platform sg invocation origin observed counters,
  os_int_exit_no_schedule_pre platform sg invocation origin observed counters |--
  coq_prop (interrupt_exit_requests_schedule observed counters = false /\
    0 <= counters.(intNesting) <= 255 /\ 0 <= counters.(lockNesting) <= 255) &&
  (interrupt_platform_running platform invocation origin 192 **
   sg.(g_OSRunning) # UChar |-> os_int_exit_no_schedule_running observed **
   sg.(g_OSIntNesting) # UChar |-> counters.(intNesting) **
   sg.(g_OSLockNesting) # UChar |-> counters.(lockNesting)).
Proof.
  intros; unfold os_int_exit_no_schedule_pre, os_int_exit_no_schedule_cells, store_int_state.
  Intros.
  prop_apply_p (store_uchar_range sg.(g_OSIntNesting) counters.(intNesting)).
  prop_apply_p (store_uchar_range sg.(g_OSLockNesting) counters.(lockNesting)).
  entailer!.
Qed.

Lemma os_int_exit_no_schedule_running_unsigned : forall observed,
  unsigned_last_nbits (os_int_exit_no_schedule_running observed) 32 =
    os_int_exit_no_schedule_running observed.
Proof. intros []; reflexivity. Qed.

Lemma os_int_exit_no_schedule_positive_lock : forall observed counters,
  counters.(lockNesting) <> 0 -> interrupt_exit_requests_schedule observed counters = false.
Proof.
  intros observed counters Hlock.
  unfold interrupt_exit_requests_schedule; apply Z.eqb_neq in Hlock.
  rewrite Hlock, Bool.andb_false_r; reflexivity.
Qed.

Lemma os_int_exit_no_schedule_boot : forall counters,
  interrupt_exit_requests_schedule false counters = false.
Proof. reflexivity. Qed.

(** The actual frame left by the three-cell C contract when the Timer
    body is owned by the interrupted caller. It retains the ready tables,
    scheduler metadata, Timer type/service cells and every other module;
    none of those resources is supplied by the platform token. *)
Definition os_int_exit_timer_residual (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  timer_images_type_rep sg s.(TimerState) **
  timer_service_globals_rep sg s.(TimerState) **
  sched_raw_rep_without_running sg s.(TskState) s.(SchedState) **
  UCOS2_selected_rep sg s (fun m =>
    match m with TimerModule | InterruptModule | SchedModule => false | _ => true end).

Lemma os_int_exit_timer_region_split_cells : forall sg s,
  UCOS2_raw_rep_missing_timer_pool_body sg s --||--
    os_int_exit_no_schedule_cells sg s.(SchedState).(isRunning) s.(IntrState) **
    os_int_exit_timer_residual sg s.
Proof.
  intros sg s.
  unfold UCOS2_raw_rep_missing_timer_pool_body, UCOS2_raw_rep_missing_timer,
    UCOS2_raw_rep_missing_module, os_int_exit_timer_residual, UCOS2_selected_rep.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep].
  rewrite sched_raw_rep_split_running.
  unfold os_int_exit_no_schedule_cells, os_int_exit_no_schedule_running.
  split.
  - unfold interrupt_inv; entailer!.
  - sep_apply_l_atomic (interrupt_inv_merge_counters sg s.(IntrState)); entailer!.
Qed.

Lemma os_int_exit_timer_region_call_pre : forall platform sg invocation origin entry,
  interrupt_exit_requests_schedule entry.(SchedState).(isRunning) entry.(IntrState) = false ->
  interrupt_platform_running platform invocation origin 192 **
    UCOS2_inv_missing_timer_pool_body sg entry |--
  coq_prop (UCOS2_state_inv sg entry) &&
    (os_int_exit_no_schedule_pre platform sg invocation origin
       entry.(SchedState).(isRunning) entry.(IntrState) **
     os_int_exit_timer_residual sg entry).
Proof.
  intros platform sg invocation origin entry Hdisabled.
  unfold UCOS2_inv_missing_timer_pool_body, os_int_exit_no_schedule_pre.
  rewrite os_int_exit_timer_region_split_cells; entailer!.
Qed.

Lemma os_int_exit_timer_region_call_post : forall platform sg invocation origin entry,
  UCOS2_state_inv sg entry ->
  interrupt_exit_requests_schedule entry.(SchedState).(isRunning) entry.(IntrState) = false ->
  os_int_exit_no_schedule_post platform sg invocation origin
      entry.(SchedState).(isRunning) entry.(IntrState) **
    os_int_exit_timer_residual sg entry |--
  interrupt_platform_running platform invocation origin 192 **
    UCOS2_inv_missing_timer_pool_body sg
      (os_int_exit_ready_checkpoint entry.(SchedState).(isRunning) entry).
Proof.
  intros platform sg invocation origin entry Hvalid Hdisabled.
  rewrite (os_int_exit_no_schedule_checkpoint_eq _ _ Hdisabled).
  unfold os_int_exit_no_schedule_post, UCOS2_inv_missing_timer_pool_body.
  rewrite UCOS2_validity_replace_interrupt_eq, os_int_exit_timer_region_split_cells.
  cbn [replace_IntrS SchedState IntrState].
  change (interrupt_platform_running platform invocation origin 192 **
      os_int_exit_no_schedule_cells sg entry.(SchedState).(isRunning)
        (interrupt_exit_state entry.(SchedState).(isRunning) entry.(IntrState)) **
      os_int_exit_timer_residual sg entry |--
    interrupt_platform_running platform invocation origin 192 **
      (coq_prop (UCOS2_state_inv sg entry) &&
       (os_int_exit_no_schedule_cells sg entry.(SchedState).(isRunning)
          (interrupt_exit_state entry.(SchedState).(isRunning) entry.(IntrState)) **
        os_int_exit_timer_residual sg entry))).
  entailer!.
Qed.
