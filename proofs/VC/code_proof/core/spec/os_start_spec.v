Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Export AUXLib.ListLib.
Require Import SumLib.ZRange.
From SimpleC.SL Require Export Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.ucos2_spatial.
Require Export Ucos2Verify.lib.task_stack.
Require Export Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.lib.timer.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.kernel_start.
Require Export Ucos2Verify.lib.kernel_heap_execution.
Require Export Ucos2Verify.lib.kernel_heap_observation.
Require Export Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Export Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Export Ucos2Verify.VC.code.core.spec.kernel_start_stack_spec.
Import ListNotations UCOS2_C_Rules TaskStateDef SchedStateDef KernelHeapObservation.
Import Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** V2.93.01 OSStart, timer-v2.93.01, ARM32 little-endian.  The four
    writes below are separate source steps.  The raw table observation
    retains PTFree/PTReserved as well as PTTask; no empty-ready test is
    added to the program.  Stable-state reconstruction is used only on
    the documented initialized, nonempty startup protocol. *)
Definition os_start_write_priority (s : UCOS2_Verify_State) :=
  replace_SchedS (sched_priority_write_state s.(TskState) s.(SchedState)) s.

Definition os_start_write_current_priority (s : UCOS2_Verify_State) :=
  let c := s.(SchedState) in
  replace_SchedS
    {| readyList := c.(readyList); curTaskID := c.(curTaskID);
       curSchedPrio := c.(highRdyPrio); highRdyTid := c.(highRdyTid);
       highRdyPrio := c.(highRdyPrio); ctxSwCtr := c.(ctxSwCtr);
       isRunning := c.(isRunning) |} s.

Definition os_start_table_task (s : UCOS2_Verify_State) : option TaskID :=
  match s.(TskState).(prioTbl) (sched_priority_byte s.(SchedState).(highRdyPrio)) with
  | PTTask tid => Some tid
  | _ => None
  end.

Definition os_start_write_high_pointer (s : UCOS2_Verify_State) :=
  replace_SchedS (sched_write_high_pointer s.(SchedState) (os_start_table_task s)) s.

Definition os_start_write_current_pointer (s : UCOS2_Verify_State) :=
  let c := s.(SchedState) in
  replace_SchedS
    {| readyList := c.(readyList); curTaskID := c.(highRdyTid);
       curSchedPrio := c.(curSchedPrio); highRdyTid := c.(highRdyTid);
       highRdyPrio := c.(highRdyPrio); ctxSwCtr := c.(ctxSwCtr);
       isRunning := c.(isRunning) |} s.

Definition os_start_prefix_state (s : UCOS2_Verify_State) :=
  os_start_write_current_pointer
    (os_start_write_high_pointer
      (os_start_write_current_priority (os_start_write_priority s))).

Definition os_start_prefix_program : program UCOS2_Verify_State unit :=
  bind (update' os_start_write_priority) (fun _ =>
  bind (update' os_start_write_current_priority) (fun _ =>
  bind (update' os_start_write_high_pointer) (fun _ =>
    update' os_start_write_current_pointer))).

Definition os_start_prefix_writes (sg : StableGlobVars) (s : UCOS2_Verify_State)
  : list (Z * Z) :=
  [(sg.(g_OSPrioHighRdy), sched_selected_priority s.(TskState) s.(SchedState));
   (sg.(g_OSPrioCur), sched_selected_priority s.(TskState) s.(SchedState));
   (sg.(g_OSTCBHighRdy), sched_selected_pointer sg s.(TskState) s.(SchedState));
   (sg.(g_OSTCBCur), sched_selected_pointer sg s.(TskState) s.(SchedState))].

Lemma os_start_prefix_program_result : forall s r after,
  os_start_prefix_program s r after <-> after = os_start_prefix_state s.
Proof.
  intros s [] after.
  (* Expose the bind cuts while keeping the concrete state updates folded. *)
  change ((exists (a : unit) s1,
    s1 = os_start_write_priority s /\
    exists (b : unit) s2,
      s2 = os_start_write_current_priority s1 /\
      exists (c : unit) s3,
        s3 = os_start_write_high_pointer s2 /\
        after = os_start_write_current_pointer s3) <->
    after = os_start_write_current_pointer
      (os_start_write_high_pointer
        (os_start_write_current_priority (os_start_write_priority s)))).
  split.
  - intros [a [s1 [-> [b [s2 [-> [c [s3 [-> H]]]]]]]]]; exact H.
  - intro H; exists tt, (os_start_write_priority s); split; [reflexivity|].
    exists tt, (os_start_write_current_priority (os_start_write_priority s));
      split; [reflexivity|].
    exists tt, (os_start_write_high_pointer
      (os_start_write_current_priority (os_start_write_priority s)));
      split; [reflexivity|exact H].
Qed.

Lemma os_start_prefix_state_eq_ready : forall sg s,
  UCOS2_state_inv sg s -> s.(SchedState).(readyList) <> [] ->
  os_start_prefix_state s = kernel_start_ready_state s.
Proof.
  intros sg s Hvalid Hnonempty.
  destruct s.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
  pose proof (proj1 (proj1 (proj2 (proj2 Hvalid)))) as Hready.
  destruct (proj1 Hready head ltac:(rewrite Hlist; left; reflexivity))
    as [node [Hnode Hrest]].
  assert (Hsg : valid_stable_glob_vars sg).
  { exact (proj1 (proj1 Hvalid)). }
  assert (Hregistered : task_current_prio_registered s.(TskState)).
  { pose proof (proj1 (proj2 Hvalid)) as Htask; unfold task_in_range in Htask; tauto. }
  pose proof (sched_selected_priority_eq_head sg _ _ head tail node Hsg Hready Hlist Hnode)
    as Hpriority.
  pose proof (Hregistered head node Hnode) as Htable.
  unfold os_start_prefix_state, os_start_write_priority,
    os_start_write_current_priority, os_start_write_high_pointer,
    os_start_write_current_pointer, os_start_table_task, sched_priority_write_state,
    sched_write_high_priority, sched_write_high_pointer, kernel_start_ready_state,
    sched_install_selected, sched_refresh_high.
  cbn; rewrite Hpriority, Htable, Hlist, Hnode; reflexivity.
Qed.

(** A source observation, not a new C return value.  Handoff identifies
    the actual first frame, including lease/generation, SP, CPSR, R0-R12,
    LR and PC.  It does not claim that that task eventually returns. *)
Inductive OsStartObservation : Type :=
| start_returned
| start_handoff (saved : Armv7aContinuation).

Definition os_start_selected_frame (s : UCOS2_Verify_State)
  (saved : Armv7aContinuation) : Prop :=
  exists node,
    s.(SchedState).(highRdyTid) = Some saved.(armv7a_continuation_stack).(stackLeaseSlot) /\
    s.(TskState).(inUsedTaskStates) saved.(armv7a_continuation_stack).(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = saved.(armv7a_continuation_stack).(stackLeaseGeneration) /\
    node.(tcbStkPtr) = saved.(armv7a_continuation_sp) /\
    s.(TskState).(parkedTaskStacks) (task_stack_key saved.(armv7a_continuation_stack)) =
      Some (saved.(armv7a_continuation_stack).(stackLeaseRegion),
        saved.(armv7a_continuation_fragments)).

Definition os_start_initial_ready (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (saved : Armv7aContinuation) : Prop :=
  armv7a_initial_frame_binding saved /\
  os_start_selected_frame s saved /\
  (exists node,
    sched_current_ready_at s.(TskState) s.(SchedState)
      saved.(armv7a_continuation_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = saved.(armv7a_continuation_stack).(stackLeaseGeneration) /\
    node.(tcbStkPtr) = saved.(armv7a_continuation_sp)) /\
  tcb_field_address (task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot) /\
  task_idle_tail sg s.(TskState) /\
  (sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized s.(TimerState)).

Definition os_start_high_program (external : OsSchedExternalResources) (sg : StableGlobVars)
  : program UCOS2_Verify_State OsStartObservation :=
  fun ready result after => exists hooked saved,
    kernel_client_step external.(os_sched_hook_action) sg ready hooked /\
    os_start_selected_frame hooked saved /\
    result = start_handoff saved /\
    after = kernel_start_take_stack_state (kernel_running_store hooked)
      saved.(armv7a_continuation_stack).

Definition os_start_program (external : OsSchedExternalResources) (sg : StableGlobVars)
  (running : Z) : program UCOS2_Verify_State OsStartObservation :=
  if Z.eq_dec running 0 then
    bind os_start_prefix_program (fun _ => os_start_high_program external sg)
  else ret start_returned.

Lemma os_start_safe_return : forall external sg running entry X,
  running <> 0 -> safeExec (eq entry) (os_start_program external sg running) X ->
  safeExec (eq entry) (ret start_returned) X.
Proof. intros; unfold os_start_program in H0; destruct (Z.eq_dec running 0); congruence. Qed.

Lemma os_start_safe_high : forall external sg entry X,
  safeExec (eq entry) (os_start_program external sg 0) X ->
  safeExec (eq (os_start_prefix_state entry)) (os_start_high_program external sg) X.
Proof.
  intros external sg entry X Hsafe.
  unfold os_start_program in Hsafe; destruct (Z.eq_dec 0 0); [|contradiction].
  eapply highstepbind_derive with (a := tt) (P := eq entry)
    (c1 := os_start_prefix_program) (c2 := fun _ => os_start_high_program external sg).
  - intros s <-; exists (os_start_prefix_state entry); split; [|reflexivity].
    apply os_start_prefix_program_result; reflexivity.
  - exact Hsafe.
Qed.

Lemma os_start_safe_handoff : forall external sg ready hooked saved X,
  kernel_client_step external.(os_sched_hook_action) sg ready hooked ->
  os_start_selected_frame hooked saved ->
  safeExec (eq ready) (os_start_high_program external sg) X ->
  safeExec (eq (kernel_start_take_stack_state (kernel_running_store hooked)
      saved.(armv7a_continuation_stack))) (ret (start_handoff saved)) X.
Proof.
  intros external sg ready hooked saved X Hhook Hselected [s [<- Hsafe]].
  exists (kernel_start_take_stack_state (kernel_running_store hooked)
    saved.(armv7a_continuation_stack)); split; [reflexivity|].
  change (forall result after,
    result = start_handoff saved /\
    kernel_start_take_stack_state (kernel_running_store hooked)
      saved.(armv7a_continuation_stack) = after -> X result after).
  intros result after [-> <-].
  apply Hsafe; exists hooked, saved; repeat split; assumption || reflexivity.
Qed.

(** The explicitly conditional CPU prefix is only MSR CPSR_c,#0xD3;
    CLREX.  The upper CPSR bits are preserved, not set to 211.  The banked
    SVC stack has its own descriptor and actual fragments.  A distinct
    old active stack is released; aliasing is permitted only when the
    two descriptors and fragments are equal.  No saved-CPSR token exists. *)
Record OsStartCpuState : Type := {
  os_start_cpsr : Z;
  os_start_exclusive : bool;
  os_start_active_stack : TaskStackLease;
  os_start_svc_stack : TaskStackLease
}.

Definition os_start_msr_svc (cpu : OsStartCpuState) : OsStartCpuState :=
  {| os_start_cpsr := Z.lor (Z.land cpu.(os_start_cpsr) (Z.lnot 255)) 211;
     os_start_exclusive := cpu.(os_start_exclusive);
     os_start_active_stack := cpu.(os_start_svc_stack);
     os_start_svc_stack := cpu.(os_start_svc_stack) |}.

Definition os_start_clrex (cpu : OsStartCpuState) : OsStartCpuState :=
  {| os_start_cpsr := cpu.(os_start_cpsr); os_start_exclusive := false;
     os_start_active_stack := cpu.(os_start_active_stack);
     os_start_svc_stack := cpu.(os_start_svc_stack) |}.

Definition os_start_cpu_prefix_execution (before after : OsStartCpuState) : Prop :=
  exists masked, masked = os_start_msr_svc before /\ after = os_start_clrex masked.

Record OsStartBootstrap : Type := {
  os_start_boot_call : OsSchedCallContext;
  os_start_svc_call : OsSchedCallContext;
  os_start_cpu_before : OsStartCpuState;
  os_start_same_stack : bool
}.

Definition os_start_bootstrap_binding (boot : OsStartBootstrap) : Prop :=
  boot.(os_start_boot_call).(os_sched_call_origin) = BootInvocation /\
  boot.(os_start_svc_call).(os_sched_call_origin) = BootInvocation /\
  boot.(os_start_svc_call).(os_sched_call_invocation) =
    boot.(os_start_boot_call).(os_sched_call_invocation) /\
  boot.(os_start_cpu_before).(os_start_active_stack) = boot.(os_start_boot_call).(os_sched_call_stack) /\
  boot.(os_start_cpu_before).(os_start_svc_stack) = boot.(os_start_svc_call).(os_sched_call_stack) /\
  (boot.(os_start_same_stack) = true ->
    boot.(os_start_svc_call).(os_sched_call_stack) = boot.(os_start_boot_call).(os_sched_call_stack) /\
    boot.(os_start_svc_call).(os_sched_call_fragments) = boot.(os_start_boot_call).(os_sched_call_fragments)).

Definition os_start_banked_stack (boot : OsStartBootstrap) : Assertion :=
  if boot.(os_start_same_stack) then emp else
    task_stack_fragments_rep boot.(os_start_svc_call).(os_sched_call_stack).(stackLeaseRegion)
      boot.(os_start_svc_call).(os_sched_call_fragments).

Definition os_start_released_stack (boot : OsStartBootstrap) : Assertion :=
  if boot.(os_start_same_stack) then emp else
    task_stack_fragments_rep boot.(os_start_boot_call).(os_sched_call_stack).(stackLeaseRegion)
      boot.(os_start_boot_call).(os_sched_call_fragments).

Definition os_start_bootstrap_owned external platform boot : Assertion :=
  kernel_call_execution_owned external platform boot.(os_start_boot_call)
    (armv7a_irq_fiq_mask boot.(os_start_cpu_before).(os_start_cpsr)) **
  os_start_banked_stack boot.

Record OsStartCpuPrefixABI external platform : Type := {
  os_start_cpu_prefix_transition : OsStartBootstrap -> OsStartCpuState -> model -> model -> Prop;
  os_start_cpu_prefix_source : forall boot returned_cpu before after,
    os_start_cpu_prefix_transition boot returned_cpu before after ->
    os_start_cpu_prefix_execution boot.(os_start_cpu_before) returned_cpu /\
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem);
  os_start_cpu_prefix_resources : forall boot returned_cpu (frame : Assertion) before after,
    os_start_bootstrap_binding boot ->
    (os_start_bootstrap_owned external platform boot ** frame) before ->
    os_start_cpu_prefix_transition boot returned_cpu before after ->
    (kernel_call_execution_owned external platform boot.(os_start_svc_call) 192 **
      os_start_released_stack boot ** frame) after
}.

(** Conditional contract for the CALLED OSTaskSwHook.  There is no known
    selected port C body in this input, so no empty-hook instance is asserted.
    The endpoint protocol is an explicit supported-hook condition; it is
    not a consequence of KernelClientCertificate or of CPU instructions.
    The actual return relation, kernel heap, CPU/stack, selected frame and
    disjoint caller frame all use one returned endpoint. *)
Record OsStartHookABI external platform : Type := {
  os_start_hook_transition : StableGlobVars -> OsSchedCallContext ->
    UCOS2_Verify_State -> model -> OsSchedCallContext -> UCOS2_Verify_State ->
    Armv7aContinuation -> model -> Prop;
  os_start_hook_resources : forall sg boot ready saved_before (frame : Assertion) before
    returned hooked saved after,
    boot.(os_sched_call_origin) = BootInvocation ->
    os_start_initial_ready sg ready saved_before ->
    (UCOS2_inv sg ready ** (kernel_call_execution_owned external platform boot 192 ** frame)) before ->
    os_start_hook_transition sg boot ready before returned hooked saved after ->
    kernel_client_step external.(os_sched_hook_action) sg ready hooked /\
    returned.(os_sched_call_origin) = BootInvocation /\
    returned.(os_sched_call_invocation) = boot.(os_sched_call_invocation) /\
    returned.(os_sched_call_stack) = boot.(os_sched_call_stack) /\
    os_start_initial_ready sg hooked saved /\
    (UCOS2_inv sg hooked ** (kernel_call_execution_owned external platform returned 192 ** frame)) after
}.

Record OsStartEnvironment : Type := {
  os_start_external : OsSchedExternalResources;
  os_start_platform : InterruptPlatformResources;
  os_start_irq_port : OsIntExitPlatformResources;
  os_start_continuation_abi : Armv7aContinuationABI os_start_external os_start_platform os_start_irq_port;
  os_start_restore_abi : Armv7aStartRestoreABI os_start_external os_start_platform
    os_start_irq_port os_start_continuation_abi;
  os_start_prefix_abi : OsStartCpuPrefixABI os_start_external os_start_platform;
  os_start_hook_abi : OsStartHookABI os_start_external os_start_platform;
  os_start_globals : StableGlobVars;
  os_start_bootstrap : OsStartBootstrap
}.

(* The carrier keeps the environment opaque at the C boundary.  Exposing
   this projection avoids making the annotation depend on record-field
   syntax while retaining the exact global-address binding. *)
Definition os_start_sg (env : OsStartEnvironment) : StableGlobVars :=
  env.(os_start_globals).

Definition os_start_running_address (env : OsStartEnvironment) : Z :=
  g_OSRunning (os_start_sg env).

Definition os_start_high_safe (env : OsStartEnvironment) (ready : UCOS2_Verify_State)
  (X : OsStartObservation -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq ready) (os_start_high_program env.(os_start_external) env.(os_start_globals)) X.

Definition os_start_safe (env : OsStartEnvironment) (running : Z) (entry : UCOS2_Verify_State)
  (X : OsStartObservation -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq entry) (os_start_program env.(os_start_external) env.(os_start_globals) running) X.

Definition os_start_return_safe (entry : UCOS2_Verify_State)
  (X : OsStartObservation -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq entry) (ret start_returned) X.

Definition os_start_startup (env : OsStartEnvironment) (entry : UCOS2_Verify_State) : Prop :=
  UCOS2_state_inv env.(os_start_globals) entry /\
  entry.(SchedState).(isRunning) = false /\ entry.(SchedState).(readyList) <> [] /\
  os_start_bootstrap_binding env.(os_start_bootstrap) /\
  exists saved, os_start_initial_ready env.(os_start_globals) (kernel_start_ready_state entry) saved.

Definition os_start_entry_frame (env : OsStartEnvironment) (frame : Assertion) : Assertion :=
  os_start_bootstrap_owned env.(os_start_external) env.(os_start_platform) env.(os_start_bootstrap) **
  unmap_table_rep env.(os_start_globals) ** frame.

Definition os_start_entry_remainder env entry running (frame : Assertion) : Assertion :=
  if Z.eq_dec running 0 then
    UCOS2_raw_rep_missing_running env.(os_start_globals) entry ** os_start_entry_frame env frame
  else frame.

Definition os_start_entry_facts env entry running : Prop :=
  running = 0 -> os_start_startup env entry.

Definition os_start_pre env entry running X (frame : Assertion) : Assertion :=
  coq_prop (os_start_safe env running entry X /\ os_start_entry_facts env entry running) &&
  (env.(os_start_globals).(g_OSRunning) # UChar |-> running **
    os_start_entry_remainder env entry running frame).

Definition os_start_post env entry running X (frame : Assertion) : Assertion :=
  coq_prop (running <> 0 /\ os_start_return_safe entry X) &&
  (env.(os_start_globals).(g_OSRunning) # UChar |-> running ** frame).

(** These two ordinary-memory proofs are local leaf adaptations of the
    generic STRB/reload arguments in the permitted Timer reference.
    They import no Timer caller, SemPend precondition, or non-Idle fact. *)
Lemma os_start_running_store : forall sg state (frame : Assertion) heap,
  task_idle_tail sg state.(TskState) ->
  (sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized state.(TimerState)) ->
  (UCOS2_inv sg state ** frame) heap ->
  exists after,
    kernel_heap_execution [(sg.(g_OSRunning), 1)] heap after /\
    (UCOS2_inv sg (kernel_running_store state) ** frame) after.
Proof.
  intros sg state frame heap Hidle Htimer Hpre.
  assert (Hsplit : UCOS2_inv sg state ** frame |--
    coq_prop (UCOS2_state_inv sg state) &&
    (sg.(g_OSRunning) # UChar |-> (if state.(SchedState).(isRunning) then 1 else 0) **
     (UCOS2_raw_rep_missing_running sg state ** frame))).
  { rewrite UCOS2_inv_split_running; entailer!. }
  destruct (Hsplit heap Hpre) as [Hvalid Howned].
  destruct (kernel_heap_framed_uchar_store _ _ 1 _ heap ltac:(lia) Howned)
    as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  assert (Hmerge : sg.(g_OSRunning) # UChar |-> 1 **
      (UCOS2_raw_rep_missing_running sg state ** frame) |--
    UCOS2_inv sg (kernel_running_store state) ** frame).
  { unfold UCOS2_inv; rewrite UCOS2_raw_rep_split_running.
    assert (Hnew : UCOS2_state_inv sg (kernel_running_store state))
      by (apply kernel_running_store_preserves_validity; assumption).
    change (UCOS2_raw_rep_missing_running sg (kernel_running_store state))
      with (UCOS2_raw_rep_missing_running sg state).
    change ((kernel_running_store state).(SchedState).(isRunning)) with true; entailer!. }
  exact (Hmerge after Hafter).
Qed.

Lemma os_start_selected_reads : forall sg state slot node (frame : Assertion) heap,
  state.(SchedState).(highRdyTid) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  (UCOS2_inv sg state ** frame) heap ->
  pointer_load sg.(g_OSTCBHighRdy) (task_slot_addr sg slot) heap /\
  pointer_load (task_slot_addr sg slot) node.(tcbStkPtr) heap.
Proof.
  intros sg state slot node frame heap Hhigh Hnode Haddress
    [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]].
  assert (Hfocus : UCOS2_raw_rep sg state |--
    sg.(g_OSTCBHighRdy) # Ptr |-> task_slot_addr sg slot ** TT).
  { rewrite (UCOS2_raw_rep_split_module sg state SchedModule).
    cbn [UCOS2_module_rep]; unfold sched_raw_rep, sched_physical_rep.
    rewrite Hhigh; cbn [encode_task_link]; entailer!; intros ? ?; exact I. }
  split.
  - eapply pointer_load_frame; [|exact Hjoin].
    exact (framed_pointer_store_load _ _ _ owned (Hfocus owned Hraw)).
  - eapply pointer_load_frame; [|exact Hjoin].
    exact (armv7a_irq_raw_live_stack_pointer_load sg state slot node owned
      Hnode Haddress Hraw).
Qed.

Lemma os_start_initial_frame_complete : forall saved,
  armv7a_initial_frame_binding saved -> exists words,
  saved.(armv7a_continuation_fragments) =
    task_stack_complete_fragments saved.(armv7a_continuation_stack).(stackLeaseRegion) words.
Proof.
  intros saved [top [entry [argument [task_return [lower [upper [Heq Hrest]]]]]]].
  rewrite Heq; eexists; reflexivity.
Qed.

(** From the actual post-hook heap, execute the running byte write,
    reload the high pointer/SP, and take the same existing parked frame.
    The returned CPU owner is not constructed here. *)
Lemma os_start_prepare_restore : forall external platform sg hooked boot saved (frame : Assertion) heap,
  os_start_initial_ready sg hooked saved ->
  (UCOS2_inv sg hooked ** (kernel_call_execution_owned external platform boot 192 ** frame)) heap ->
  exists written,
    kernel_heap_execution [(sg.(g_OSRunning), 1)] heap written /\
    pointer_load sg.(g_OSTCBHighRdy)
      (task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot)) written /\
    pointer_load (task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp) written /\
    armv7a_continuation_restore_reads saved written /\
    (kernel_call_execution_owned external platform boot 192 **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) **
      (UCOS2_inv sg (kernel_start_take_stack_state (kernel_running_store hooked)
        saved.(armv7a_continuation_stack)) ** frame)) written.
Proof.
  intros external platform sg hooked boot saved frame heap
    [Hinitial [[selected [Hhigh [Hselected [Hgen0 [Hsp0 Hparked]]]]]
      [[node [Hready [Hgen Hsp]]] [Haddress [Hidle Htimer]]]]] Hpre.
  destruct (os_start_running_store sg hooked _ heap Hidle Htimer Hpre)
    as [written [Hstore Hwritten]].
  destruct (os_start_selected_reads sg (kernel_running_store hooked)
    saved.(armv7a_continuation_stack).(stackLeaseSlot) node _ written
    Hhigh (proj1 Hready) Haddress Hwritten) as [Hhighread Hspread].
  rewrite Hsp in Hspread.
  destruct (os_start_initial_frame_complete saved Hinitial) as [words Hwords].
  pose proof (kernel_start_take_stack_resources sg (kernel_running_store hooked)
    saved.(armv7a_continuation_stack) words node Hready eq_refl Hhigh Hgen
    ltac:(rewrite <- Hwords; exact Hparked)) as Htake.
  assert (Hprepare : UCOS2_inv sg (kernel_running_store hooked) **
      (kernel_call_execution_owned external platform boot 192 ** frame) |--
    kernel_call_execution_owned external platform boot 192 **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) **
    (UCOS2_inv sg (kernel_start_take_stack_state (kernel_running_store hooked)
      saved.(armv7a_continuation_stack)) ** frame)).
  { sep_apply_l_atomic Htake; Intros.
    rewrite Hwords, task_stack_fragments_rep_complete; entailer!. }
  pose proof (Hprepare written Hwritten) as Hprepared.
  assert (Hreorder : kernel_call_execution_owned external platform boot 192 **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) **
      (UCOS2_inv sg (kernel_start_take_stack_state (kernel_running_store hooked)
        saved.(armv7a_continuation_stack)) ** frame) |--
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) **
    (kernel_call_execution_owned external platform boot 192 **
      UCOS2_inv sg (kernel_start_take_stack_state (kernel_running_store hooked)
        saved.(armv7a_continuation_stack)) ** frame)) by entailer!.
  exists written; split; [exact Hstore|]. split; [exact Hhighread|].
  split; [exact Hspread|]. split; [|exact Hprepared].
  exact (armv7a_initial_frame_restore_reads saved _ written Hinitial
    (Hreorder written Hprepared)).
Qed.

Definition os_start_transfer_frame (env : OsStartEnvironment) (frame : Assertion) : Assertion :=
  os_start_released_stack env.(os_start_bootstrap) **
  unmap_table_rep env.(os_start_globals) ** frame.

Definition os_start_handoff_resources env returned hooked saved (frame : Assertion) : Assertion :=
  armv7a_initial_execution env.(os_start_continuation_abi) saved **
  task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
    saved.(armv7a_continuation_fragments) **
  task_stack_fragments_rep returned.(os_sched_call_stack).(stackLeaseRegion)
    returned.(os_sched_call_fragments) **
  (UCOS2_inv env.(os_start_globals)
    (kernel_start_take_stack_state (kernel_running_store hooked) saved.(armv7a_continuation_stack)) **
    os_start_transfer_frame env frame).

(** One actual source execution, in port order.  Hook endpoint, store
    endpoint and restored frame share the same witnesses.  The ordinary
    memory store is NOT a field of either CPU contract. *)
Definition os_start_port_execution env ready before returned hooked saved after : Prop :=
  exists returned_cpu masked hook_heap written,
    os_start_cpu_prefix_transition _ _ env.(os_start_prefix_abi)
      env.(os_start_bootstrap) returned_cpu before masked /\
    os_start_hook_transition _ _ env.(os_start_hook_abi) env.(os_start_globals)
      env.(os_start_bootstrap).(os_start_svc_call) ready masked returned hooked saved hook_heap /\
    kernel_heap_execution [(env.(os_start_globals).(g_OSRunning), 1)] hook_heap written /\
    armv7a_start_restore_transition env.(os_start_restore_abi) returned
      env.(os_start_globals).(g_OSTCBHighRdy) saved written after.

Definition os_start_high_entry env ready (frame : Assertion) : Assertion :=
  coq_prop (os_start_bootstrap_binding env.(os_start_bootstrap) /\
    exists saved, os_start_initial_ready env.(os_start_globals) ready saved) &&
  (UCOS2_inv env.(os_start_globals) ready ** os_start_entry_frame env frame).

Lemma os_start_port_transfer : forall env ready X (frame : Assertion) before returned hooked saved after,
  os_start_high_safe env ready X ->
  os_start_high_entry env ready frame before ->
  os_start_port_execution env ready before returned hooked saved after ->
  safeExec (eq (kernel_start_take_stack_state (kernel_running_store hooked)
    saved.(armv7a_continuation_stack))) (ret (start_handoff saved)) X /\
  os_start_handoff_resources env returned hooked saved frame after.
Proof.
  intros env ready X frame before returned hooked saved after Hsafe
    [[Hboot [initial Hinitial]] Hpre]
    [returned_cpu [masked [hook_heap [written [Hprefix [Hhook [Hstore Hrestore]]]]]]].
  assert (Hprefix_order : UCOS2_inv env.(os_start_globals) ready ** os_start_entry_frame env frame |--
    os_start_bootstrap_owned env.(os_start_external) env.(os_start_platform) env.(os_start_bootstrap) **
    (UCOS2_inv env.(os_start_globals) ready ** unmap_table_rep env.(os_start_globals) ** frame)).
  { unfold os_start_entry_frame; entailer!. }
  pose proof (os_start_cpu_prefix_resources _ _ env.(os_start_prefix_abi)
    env.(os_start_bootstrap) returned_cpu _ before masked Hboot (Hprefix_order before Hpre) Hprefix) as Hmasked.
  assert (Hhook_order : kernel_call_execution_owned env.(os_start_external) env.(os_start_platform)
      env.(os_start_bootstrap).(os_start_svc_call) 192 **
      os_start_released_stack env.(os_start_bootstrap) **
      (UCOS2_inv env.(os_start_globals) ready ** unmap_table_rep env.(os_start_globals) ** frame) |--
    UCOS2_inv env.(os_start_globals) ready **
      (kernel_call_execution_owned env.(os_start_external) env.(os_start_platform)
        env.(os_start_bootstrap).(os_start_svc_call) 192 ** os_start_transfer_frame env frame)).
  { unfold os_start_transfer_frame; entailer!. }
  destruct (os_start_hook_resources _ _ env.(os_start_hook_abi) env.(os_start_globals)
    env.(os_start_bootstrap).(os_start_svc_call) ready initial _ masked returned hooked saved hook_heap
    (proj1 (proj2 Hboot)) Hinitial (Hhook_order masked Hmasked) Hhook)
    as [Haction [Horigin [Hinvocation [Hstack [Hselected Hhooked]]]]].
  destruct (os_start_prepare_restore env.(os_start_external) env.(os_start_platform)
    env.(os_start_globals) hooked returned saved _ hook_heap Hselected Hhooked)
    as [actual [Hactual [Hhigh [Hsp [Hreads Hprepared]]]]].
  assert (written = actual) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst written.
  destruct (armv7a_start_restore_resources _ _ _ env.(os_start_continuation_abi)
    env.(os_start_restore_abi) returned env.(os_start_globals).(g_OSTCBHighRdy) saved
    (UCOS2_inv env.(os_start_globals)
      (kernel_start_take_stack_state (kernel_running_store hooked) saved.(armv7a_continuation_stack)) **
      os_start_transfer_frame env frame) actual after Horigin (proj1 Hselected)
    Hreads Hprepared Hrestore) as [Hmemory Hafter].
  split; [|exact Hafter].
  eapply os_start_safe_handoff; [exact Haction|exact (proj1 (proj2 Hselected))|exact Hsafe].
Qed.

(** The C frontend has an ordinary-return post only.  The actual call
    consumes this independently proved typed transfer certificate together
    with its real entry resources.  False below projects only the absence
    of an ordinary return; it does not stand in for the transfer proof. *)
Definition os_start_transfer_contract env ready X (frame : Assertion) : Prop :=
  forall before returned hooked saved after,
    os_start_high_entry env ready frame before ->
    os_start_port_execution env ready before returned hooked saved after ->
    safeExec (eq (kernel_start_take_stack_state (kernel_running_store hooked)
      saved.(armv7a_continuation_stack))) (ret (start_handoff saved)) X /\
    os_start_handoff_resources env returned hooked saved frame after.

Definition os_start_high_pre env ready X (frame : Assertion) : Assertion :=
  coq_prop (os_start_high_safe env ready X /\ os_start_transfer_contract env ready X frame) &&
  os_start_high_entry env ready frame.

Lemma os_start_high_pre_from_entry : forall env ready X frame,
  os_start_high_safe env ready X ->
  os_start_high_entry env ready frame |-- os_start_high_pre env ready X frame.
Proof.
  intros env ready X frame Hsafe heap Hentry; split; [split; [exact Hsafe|]|exact Hentry].
  intros before returned hooked saved after Hpre Hsource.
  eapply os_start_port_transfer; eassumption.
Qed.

Definition os_start_global_addresses env unmap group rows high priority table current high_task running : Prop :=
  sched_new_global_addresses env.(os_start_globals) unmap group rows high /\
  priority = env.(os_start_globals).(g_OSPrioCur) /\
  table = env.(os_start_globals).(g_OSTCBPrioTbl) /\
  current = env.(os_start_globals).(g_OSTCBCur) /\
  high_task = env.(os_start_globals).(g_OSTCBHighRdy) /\
  running = env.(os_start_globals).(g_OSRunning).

Definition os_start_group (s : UCOS2_Verify_State) :=
  encode_ready_grp s.(SchedState).(readyList) s.(TskState).
Definition os_start_rows (s : UCOS2_Verify_State) :=
  sched_row_values s.(TskState) s.(SchedState).(readyList).
Definition os_start_priority (s : UCOS2_Verify_State) :=
  sched_new_priority (os_start_group s) (os_start_rows s).
Definition os_start_old_high (s : UCOS2_Verify_State) := sched_priority_byte s.(SchedState).(highRdyPrio).
Definition os_start_old_priority (s : UCOS2_Verify_State) := sched_priority_byte s.(SchedState).(curSchedPrio).
Definition os_start_old_current env (s : UCOS2_Verify_State) :=
  encode_task_link env.(os_start_globals) s.(SchedState).(curTaskID).
Definition os_start_old_high_task env (s : UCOS2_Verify_State) :=
  encode_task_link env.(os_start_globals) s.(SchedState).(highRdyTid).
Definition os_start_table_values env (s : UCOS2_Verify_State) :=
  map (fun p => prio_tbl_entry_to_addr env.(os_start_globals) (s.(TskState).(prioTbl) p)) (Zrange 0 64).
Definition os_start_pointer env s :=
  Znth (os_start_priority s) (os_start_table_values env s) 0.

Definition os_start_sched_frame env entry (frame : Assertion) : Assertion :=
  env.(os_start_globals).(g_OSPrioCur) # UChar |-> os_start_old_priority entry **
  env.(os_start_globals).(g_OSTCBCur) # Ptr |-> os_start_old_current env entry **
  env.(os_start_globals).(g_OSTCBHighRdy) # Ptr |-> os_start_old_high_task env entry **
  env.(os_start_globals).(g_OSCtxSwCtr) # UInt |-> entry.(SchedState).(ctxSwCtr) **
  env.(os_start_globals).(g_OSRunning) # UChar |-> 0 **
  task_public_storage env.(os_start_globals) entry.(TskState) **
  UCOS2_raw_rep_missing_task_storage_sched env.(os_start_globals) entry **
  os_start_bootstrap_owned env.(os_start_external) env.(os_start_platform) env.(os_start_bootstrap) ** frame.

Definition os_start_c_remainder env entry (frame : Assertion) : Assertion :=
  env.(os_start_globals).(g_OSRdyGrp) # UChar |-> os_start_group entry **
  UCharArray.full env.(os_start_globals).(g_OSRdyTbl) 8 (os_start_rows entry) **
  env.(os_start_globals).(g_OSCtxSwCtr) # UInt |-> entry.(SchedState).(ctxSwCtr) **
  env.(os_start_globals).(g_OSRunning) # UChar |-> 0 **
  task_public_storage_without_prio_tbl env.(os_start_globals) entry.(TskState) **
  UCOS2_raw_rep_missing_task_storage_sched env.(os_start_globals) entry **
  os_start_entry_frame env frame.

Definition os_start_cache_cells env entry priority high current high_task (frame : Assertion) : Assertion :=
  env.(os_start_globals).(g_OSPrioCur) # UChar |-> priority **
  env.(os_start_globals).(g_OSPrioHighRdy) # UChar |-> high **
  env.(os_start_globals).(g_OSTCBCur) # Ptr |-> current **
  env.(os_start_globals).(g_OSTCBHighRdy) # Ptr |-> high_task **
  PtrArray.full env.(os_start_globals).(g_OSTCBPrioTbl) 64 (os_start_table_values env entry) **
  os_start_c_remainder env entry frame.

(** Focused residuals used by the four concrete OSStart stores.  Each
    residual removes exactly the cell consumed by the next source access;
    no residual duplicates a live cell hidden inside a larger assertion. *)
Definition os_start_sched_new_remainder (env : OsStartEnvironment)
  (entry : UCOS2_Verify_State) (frame : Assertion) : Assertion :=
  (os_start_sg env).(g_OSRdyGrp) # UChar |-> os_start_group entry **
  UCharArray.full (os_start_sg env).(g_OSRdyTbl) 8 (os_start_rows entry) **
  unmap_table_rep (os_start_sg env) **
  os_start_sched_frame env entry frame.

Definition os_start_cache_without_high (env : OsStartEnvironment)
  (entry : UCOS2_Verify_State) (priority high current high_task : Z)
  (frame : Assertion) : Assertion :=
  (os_start_sg env).(g_OSPrioCur) # UChar |-> priority **
  (os_start_sg env).(g_OSTCBCur) # Ptr |-> current **
  (os_start_sg env).(g_OSTCBHighRdy) # Ptr |-> high_task **
  PtrArray.full (os_start_sg env).(g_OSTCBPrioTbl) 64 (os_start_table_values env entry) **
  os_start_c_remainder env entry frame.

Definition os_start_cache_without_high_cur (env : OsStartEnvironment)
  (entry : UCOS2_Verify_State) (current high_task : Z)
  (frame : Assertion) : Assertion :=
  (os_start_sg env).(g_OSTCBCur) # Ptr |-> current **
  (os_start_sg env).(g_OSTCBHighRdy) # Ptr |-> high_task **
  PtrArray.full (os_start_sg env).(g_OSTCBPrioTbl) 64 (os_start_table_values env entry) **
  os_start_c_remainder env entry frame.

Definition os_start_cache_without_high_cur_highptr (env : OsStartEnvironment)
  (entry : UCOS2_Verify_State) (current : Z) (frame : Assertion) : Assertion :=
  (os_start_sg env).(g_OSTCBCur) # Ptr |-> current **
  PtrArray.full (os_start_sg env).(g_OSTCBPrioTbl) 64 (os_start_table_values env entry) **
  os_start_c_remainder env entry frame.

Definition os_start_cache_table_remainder (env : OsStartEnvironment)
  (entry : UCOS2_Verify_State) (frame : Assertion) : Assertion :=
  PtrArray.missing_i (os_start_sg env).(g_OSTCBPrioTbl) (os_start_priority entry)
    0 64 (os_start_table_values env entry) ** os_start_c_remainder env entry frame.

Lemma os_start_sched_new_focus : forall env entry frame,
  sched_new_rep (os_start_sg env) (os_start_group entry) (os_start_rows entry)
      (os_start_old_high entry) ** os_start_sched_frame env entry frame |--
  (os_start_sg env).(g_OSPrioHighRdy) # UChar |-> os_start_old_high entry **
    os_start_sched_new_remainder env entry frame.
Proof. intros; unfold sched_new_rep, os_start_sched_new_remainder, os_start_sg; entailer!. Qed.

Lemma os_start_cache_focus_high : forall env entry frame,
  os_start_cache_cells env entry (os_start_old_priority entry)
      (os_start_priority entry) (os_start_old_current env entry)
      (os_start_old_high_task env entry) frame |--
  (os_start_sg env).(g_OSPrioHighRdy) # UChar |-> os_start_priority entry **
    os_start_cache_without_high env entry (os_start_old_priority entry)
      (os_start_old_high_task env entry) (os_start_old_current env entry)
      (os_start_old_high_task env entry) frame.
Proof. intros; unfold os_start_cache_cells, os_start_cache_without_high, os_start_sg; entailer!. Qed.

Lemma os_start_cache_focus_cur : forall env entry priority high current high_task frame,
  (os_start_sg env).(g_OSPrioHighRdy) # UChar |-> high **
    os_start_cache_without_high env entry priority high current high_task frame |--
  (os_start_sg env).(g_OSPrioHighRdy) # UChar |-> high **
    (os_start_sg env).(g_OSPrioCur) # UChar |-> priority **
    os_start_cache_without_high_cur env entry current high_task frame.
Proof. intros; unfold os_start_cache_without_high, os_start_cache_without_high_cur, os_start_sg; entailer!. Qed.

Lemma os_start_cache_focus_highptr : forall env entry current high frame,
  (os_start_sg env).(g_OSPrioHighRdy) # UChar |-> high **
    (os_start_sg env).(g_OSPrioCur) # UChar |-> os_start_priority entry **
    os_start_cache_without_high_cur env entry current high frame |--
  (os_start_sg env).(g_OSPrioHighRdy) # UChar |-> high **
    (os_start_sg env).(g_OSPrioCur) # UChar |-> os_start_priority entry **
    (os_start_sg env).(g_OSTCBHighRdy) # Ptr |-> high **
    os_start_cache_without_high_cur_highptr env entry current frame.
Proof.
  intros; unfold os_start_cache_without_high_cur,
    os_start_cache_without_high_cur_highptr, os_start_sg; entailer!.
Qed.

Lemma os_start_priority_in_range : forall entry, 0 <= os_start_priority entry < 64.
Proof. intros; apply sched_new_priority_in_range. Qed.

Lemma os_start_pointer_eq_selected : forall env entry,
  os_start_pointer env entry = sched_selected_pointer env.(os_start_globals) entry.(TskState) entry.(SchedState).
Proof.
  intros; unfold os_start_pointer, os_start_priority, os_start_group, os_start_rows,
    os_start_table_values.
  rewrite sched_new_priority_eq_selected.
  rewrite prio_table_values_Znth by apply sched_selected_priority_in_range; reflexivity.
Qed.

Lemma os_start_entry_split : forall env entry running X frame,
  os_start_pre env entry running X frame |--
  coq_prop (os_start_safe env running entry X /\ os_start_entry_facts env entry running) &&
  (env.(os_start_globals).(g_OSRunning) # UChar |-> running **
    os_start_entry_remainder env entry running frame).
Proof. intros; unfold os_start_pre; entailer!. Qed.

Lemma os_start_zero_sched_resources : forall env entry frame,
  os_start_startup env entry ->
  env.(os_start_globals).(g_OSRunning) # UChar |-> 0 **
    os_start_entry_remainder env entry 0 frame |--
  sched_new_rep env.(os_start_globals) (os_start_group entry) (os_start_rows entry)
    (os_start_old_high entry) ** os_start_sched_frame env entry frame.
Proof.
  intros env entry frame [Hvalid [Hrunning Hrest]].
  unfold os_start_entry_remainder; destruct (Z.eq_dec 0 0); [|contradiction].
  assert (Hmerge : env.(os_start_globals).(g_OSRunning) # UChar |-> 0 **
      UCOS2_raw_rep_missing_running env.(os_start_globals) entry |--
      UCOS2_raw_rep env.(os_start_globals) entry).
  { rewrite UCOS2_raw_rep_split_running, Hrunning; entailer!. }
  sep_apply_l_atomic Hmerge.
  unfold UCOS2_raw_rep, task_shared_rep, sched_raw_rep, sched_physical_rep,
    sched_new_rep, os_start_sched_frame, UCOS2_raw_rep_missing_task_storage_sched,
    os_start_entry_frame, os_start_group, os_start_rows, os_start_old_high,
    os_start_old_priority, os_start_old_current, os_start_old_high_task.
  rewrite sched_rows_array_equiv, Hrunning; entailer!.
Qed.

Lemma os_start_select_cache_resources : forall env entry frame,
  sched_new_rep env.(os_start_globals) (os_start_group entry) (os_start_rows entry)
    (os_start_priority entry) ** os_start_sched_frame env entry frame |--
  os_start_cache_cells env entry (os_start_old_priority entry) (os_start_priority entry)
    (os_start_old_current env entry) (os_start_old_high_task env entry) frame.
Proof.
  intros; unfold os_start_cache_cells, os_start_c_remainder, os_start_entry_frame,
    os_start_sched_frame, sched_new_rep, os_start_table_values.
  rewrite task_public_storage_prio_tbl_equiv.
  unfold store_prio_tbl; entailer!.
Qed.

Lemma os_start_complete_cache_resources : forall env entry frame,
  os_start_startup env entry ->
  os_start_cache_cells env entry (os_start_priority entry) (os_start_priority entry)
    (os_start_pointer env entry) (os_start_pointer env entry) frame |--
  os_start_high_entry env (kernel_start_ready_state entry) frame.
Proof.
  intros env entry frame [Hvalid [Hrunning [Hnonempty [Hboot Hinitial]]]].
  assert (Hsg : valid_stable_glob_vars env.(os_start_globals)) by exact (proj1 (proj1 Hvalid)).
  pose proof (proj1 (proj1 (proj2 (proj2 Hvalid)))) as Hready.
  destruct entry.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
  destruct (proj1 Hready head ltac:(rewrite Hlist; left; reflexivity)) as [node [Hnode Hrest]].
  assert (Hregistered : task_current_prio_registered entry.(TskState)).
  { pose proof (proj1 (proj2 Hvalid)) as Htask; unfold task_in_range in Htask; tauto. }
  assert (Hpriority : os_start_priority entry = node.(curPrio)).
  { unfold os_start_priority, os_start_group, os_start_rows.
    eapply sched_new_priority_eq_head; eassumption. }
  assert (Hpointer : os_start_pointer env entry = task_slot_addr env.(os_start_globals) head).
  { rewrite os_start_pointer_eq_selected; eapply sched_selected_pointer_eq_head; eassumption. }
  assert (Hnew : UCOS2_state_inv env.(os_start_globals) (kernel_start_ready_state entry))
    by (apply kernel_start_ready_preserves_validity; exact Hvalid).
  assert (Hresources :
    os_start_cache_cells env entry (os_start_priority entry) (os_start_priority entry)
      (os_start_pointer env entry) (os_start_pointer env entry) frame |--
    UCOS2_raw_rep env.(os_start_globals) (kernel_start_ready_state entry) **
    os_start_entry_frame env frame).
  { unfold os_start_cache_cells, os_start_c_remainder, UCOS2_raw_rep,
      task_shared_rep, task_public_storage, task_public_storage_without_prio_tbl,
      UCOS2_raw_rep_missing_task_storage_sched, sched_raw_rep, sched_physical_rep,
      store_prio_tbl, os_start_table_values, os_start_group, os_start_rows.
    rewrite Hpriority, Hpointer.
    unfold kernel_start_ready_state, sched_install_selected, sched_refresh_high.
    cbn [replace_SchedS IntrState TskState SchedState EventState TickState
      FlagState MemoryState TimerState StatsState ControlState NameState
      readyList curTaskID curSchedPrio highRdyTid highRdyPrio ctxSwCtr isRunning
      sched_priority_byte encode_task_link hd_error].
    rewrite Hlist, Hnode.
    cbn [replace_SchedS IntrState TskState SchedState EventState TickState
      FlagState MemoryState TimerState StatsState ControlState NameState
      readyList curTaskID curSchedPrio highRdyTid highRdyPrio ctxSwCtr isRunning
      sched_priority_byte encode_task_link hd_error].
    rewrite <- Hlist.
    rewrite sched_rows_array_equiv, Hrunning; entailer!. }
  intros heap Hcells.
  destruct (Hresources heap Hcells) as [owned [rest [Hjoin [Howned Hframe]]]].
  unfold os_start_high_entry; split; [exact (conj Hboot Hinitial)|].
  exists owned, rest; split; [exact Hjoin|].
  split; [exact (conj Hnew Howned)|exact Hframe].
Qed.

Lemma os_start_complete_high_pre : forall env entry X frame,
  os_start_startup env entry -> os_start_safe env 0 entry X ->
  os_start_cache_cells env entry (os_start_priority entry) (os_start_priority entry)
    (os_start_pointer env entry) (os_start_pointer env entry) frame |--
  os_start_high_pre env (kernel_start_ready_state entry) X frame.
Proof.
  intros env entry X frame Hstartup Hsafe heap Hcells.
  pose proof (os_start_complete_cache_resources env entry frame Hstartup heap Hcells) as Hentry.
  apply (os_start_high_pre_from_entry env (kernel_start_ready_state entry) X frame); [|exact Hentry].
  unfold os_start_high_safe.
  rewrite <- (os_start_prefix_state_eq_ready env.(os_start_globals) entry
    (proj1 Hstartup) (proj1 (proj2 (proj2 Hstartup)))).
  apply os_start_safe_high; exact Hsafe.
Qed.

Lemma os_start_nonzero_return_resources : forall env entry running X frame,
  running <> 0 -> os_start_safe env running entry X ->
  env.(os_start_globals).(g_OSRunning) # UChar |-> running **
    os_start_entry_remainder env entry running frame |-- os_start_post env entry running X frame.
Proof.
  intros env entry running X frame Hrunning Hsafe.
  unfold os_start_entry_remainder; destruct (Z.eq_dec running 0); [contradiction|].
  assert (Hreturn : os_start_return_safe entry X).
  { eapply os_start_safe_return; eassumption. }
  unfold os_start_post; entailer!.
Qed.

Definition os_start_table_remainder env entry (frame : Assertion) : Assertion :=
  PtrArray.missing_i env.(os_start_globals).(g_OSTCBPrioTbl) (os_start_priority entry)
    0 64 (os_start_table_values env entry) ** os_start_c_remainder env entry frame.

Lemma os_start_table_split : forall env entry frame,
  PtrArray.full env.(os_start_globals).(g_OSTCBPrioTbl) 64 (os_start_table_values env entry) **
    os_start_c_remainder env entry frame |--
  (env.(os_start_globals).(g_OSTCBPrioTbl) + os_start_priority entry * sizeof(PTR))
    # Ptr |-> os_start_pointer env entry ** os_start_table_remainder env entry frame.
Proof.
  intros; unfold os_start_pointer, os_start_table_remainder.
  sep_apply_l_atomic (PtrArray.full_split_to_missing_i
    env.(os_start_globals).(g_OSTCBPrioTbl) (os_start_priority entry) 64
    (os_start_table_values env entry) 0 (os_start_priority_in_range entry)); entailer!.
Qed.

Lemma os_start_table_merge : forall env entry frame,
  (env.(os_start_globals).(g_OSTCBPrioTbl) + os_start_priority entry * sizeof(PTR))
    # Ptr |-> os_start_pointer env entry ** os_start_table_remainder env entry frame |--
  PtrArray.full env.(os_start_globals).(g_OSTCBPrioTbl) 64 (os_start_table_values env entry) **
    os_start_c_remainder env entry frame.
Proof.
  intros; unfold os_start_pointer, os_start_table_remainder.
  assert (Hfocus :
    (env.(os_start_globals).(g_OSTCBPrioTbl) + os_start_priority entry * sizeof(PTR))
      # Ptr |-> Znth (os_start_priority entry) (os_start_table_values env entry) 0 **
    (PtrArray.missing_i env.(os_start_globals).(g_OSTCBPrioTbl)
      (os_start_priority entry) 0 64 (os_start_table_values env entry) **
      os_start_c_remainder env entry frame) |--
    ((env.(os_start_globals).(g_OSTCBPrioTbl) + os_start_priority entry * sizeof(PTR))
      # Ptr |-> Znth (os_start_priority entry) (os_start_table_values env entry) 0 **
      PtrArray.missing_i env.(os_start_globals).(g_OSTCBPrioTbl)
        (os_start_priority entry) 0 64 (os_start_table_values env entry)) **
    os_start_c_remainder env entry frame) by entailer!.
  pose proof (PtrArray.missing_i_merge_to_full
    env.(os_start_globals).(g_OSTCBPrioTbl) (os_start_priority entry) 64
    (Znth (os_start_priority entry) (os_start_table_values env entry) 0)
    (os_start_table_values env entry) (os_start_priority_in_range entry)) as Hmerge.
  rewrite replace_Znth_Znth in Hmerge.
  intros heap Hpre.
  destruct (Hfocus heap Hpre) as [owned [rest [Hjoin [Htable Hframe]]]].
  exists owned, rest; split; [exact Hjoin|].
  split; [exact (Hmerge owned Htable)|exact Hframe].
Qed.
