Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_init_task_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_ext_timer_phase_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.lib.timer_execution.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

Definition tmr_init_task_timer_phase_eq (before after : UCOS2_Verify_State) : Prop :=
  before.(TimerState).(timerInitPhase) = after.(TimerState).(timerInitPhase).

(** NameSet's actual ordered result retains both real intervals. This leaf
    deliberately does not import the downstream TimerInit caller library. *)
Lemma tmr_init_task_interval_timer_phase_eq : forall critical sg invocation before after,
  critical_region_interval critical sg invocation before after ->
  tmr_init_task_timer_phase_eq before after.
Proof.
  intros; symmetry; exact (proj1 (timer_public_trace_public_storage_frame sg _ _
    (critical_region_interval_timer_public_trace _ _ _ _ _ H))).
Qed.

Lemma tmr_init_task_name_result_timer_phase_eq :
  forall critical sg invocation request name before error after,
  task_name_set_result critical sg invocation request name before error after ->
  tmr_init_task_timer_phase_eq before after.
Proof.
  intros critical sg invocation request name before error after Hresult.
  destruct Hresult as [[_ [_ ->]]|[[_ [_ [_ ->]]]|[[_ [_ [_ [_ ->]]]]|Hprotected]]];
    try reflexivity.
  destruct Hprotected as [_ [_ [_ [acquired [prio [released [Hacquire [_ [Hstep Hreturn]]]]]]]]].
  pose proof (tmr_init_task_interval_timer_phase_eq _ _ _ _ _ Hacquire) as Hfirst.
  pose proof (tmr_init_task_interval_timer_phase_eq _ _ _ _ _ Hreturn) as Hlast.
  unfold tmr_init_task_timer_phase_eq in *; destruct Hstep; cbn in *; congruence.
Qed.

Lemma tmr_init_task_name_post_timer_phase_eq :
  forall critical sg invocation request name before error after X,
  task_name_set_post critical sg invocation request name before error after X ->
  tmr_init_task_timer_phase_eq before after.
Proof. intros; eapply tmr_init_task_name_result_timer_phase_eq; exact (proj1 H). Qed.

(** This receipt describes the constructor's exact publication endpoint,
    allocation and generation. It neither looks up the final priority/name nor
    asserts that the newly published task remains live at the eventual return. *)
Definition tmr_init_task_publication_receipt sg region args task_return lower upper name
  invocation origin initial released (receipt : option (TaskID * nat)) : Prop :=
  exists acquired current slot image lease,
    receipt = Some (slot, acquired.(TskState).(taskLifecycle).(taskNextGeneration)) /\
    released = task_create_stack_publication_state sg
      (task_tcb_init_stack_publication region args task_return lower upper name
        invocation origin acquired slot image lease) current /\
    task_tcb_init_call_result sg (task_tcb_init_stack_call_args args name)
      invocation origin initial 0
      (task_tcb_init_published_state sg (task_tcb_init_stack_call_args args name)
        invocation acquired current slot image) /\
    task_create_stack_publication_input sg
      (task_tcb_init_stack_publication region args task_return lower upper name
        invocation origin acquired slot image lease) current /\
    task_tcb_init_commit_binding (task_tcb_init_stack_call_args args name)
      invocation origin acquired current slot /\
    task_publication_happened released.(TskState) invocation slot
      acquired.(TskState).(taskLifecycle).(taskNextGeneration).

Lemma tmr_init_task_stack_result_publication_receipt :
  forall critical sg region args task_return lower upper name invocation origin initial released,
  task_tcb_init_stack_call_result critical sg region args task_return lower upper name
    invocation origin initial 0 released ->
  exists receipt, tmr_init_task_publication_receipt sg region args task_return lower upper name
    invocation origin initial released receipt.
Proof.
  intros critical sg region args task_return lower upper name invocation origin initial released Hresult.
  inversion Hresult as [|acquired current slot image lease Hraw Hinput]; subst.
  exists (Some (slot, acquired.(TskState).(taskLifecycle).(taskNextGeneration))).
  exists acquired, current, slot, image, lease.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hraw|].
  split; [exact Hinput|]. split.
  - exact (proj1 (proj2 (proj2 Hinput))).
  - change (task_publication_happened
      (task_commit current.(TskState) (task_tcb_init_stack_call_args args name).(initPrio)
        invocation (task_tcb_init_commit_node (task_tcb_init_stack_call_args args name) acquired slot image))
      invocation slot acquired.(TskState).(taskLifecycle).(taskNextGeneration)).
    apply task_commit_records_history.
Qed.

(** The original TCB source payload, retaining its SAME released witness and
    an observation of that witness's successful publication constructor. *)
Definition tmr_init_task_tcb_receipt_output critical sg region args task_return lower upper name
  original initial returned current receipt : Prop :=
  exists released,
    task_tcb_init_stack_call_result critical sg region args task_return lower upper name
      original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 0 released /\
    UCOS2_state_inv sg released /\
    task_tcb_init_stack_source_preserved original initial released /\
    task_tcb_init_stack_same_call returned original /\
    task_tcb_init_stack_return_preserved original released current /\
    (0 = 0 -> current.(SchedState).(readyList) <> []) /\
    task_tcb_init_runtime_history sg original initial returned current /\
    initial.(NameState) = current.(NameState) /\
    tmr_init_task_publication_receipt sg region args task_return lower upper name
      original.(os_sched_call_invocation) original.(os_sched_call_origin) initial released receipt.

Lemma tmr_init_task_tcb_source_has_receipt :
  forall critical sg region args task_return lower upper name original initial returned current,
  task_create_tcb_program critical sg region args task_return lower upper name original
    initial (returned, 0) current ->
  exists receipt, tmr_init_task_tcb_receipt_output critical sg region args task_return
    lower upper name original initial returned current receipt.
Proof.
  intros critical sg region args task_return lower upper name original initial returned current
    [released [Hresult Hrest]].
  destruct (tmr_init_task_stack_result_publication_receipt _ _ _ _ _ _ _ _ _ _ _ _ Hresult)
    as [receipt Hreceipt].
  exists receipt, released; cbn in *; tauto.
Qed.

Lemma tmr_init_task_restore_return_code : forall environment critical sg call code before result after,
  task_create_restore_return_program environment critical sg call code before result after -> result = code.
Proof. intros environment critical sg call code before result after [value [middle [Hsource [Hcode Hafter]]]]; exact Hcode. Qed.

Lemma tmr_init_task_tcb_return_code : forall environment critical sg args call mask code before result after,
  (code = 0 \/ code = 66) ->
  task_create_tcb_return_program environment critical sg args call mask code before result after -> result = code.
Proof.
  intros environment critical sg args call mask code before result after Hcodes Hrun.
  destruct Hcodes as [Hcode|Hcode]; subst code.
  - destruct Hrun as [running [middle [Hget Htail]]].
    destruct running.
    + destruct Htail as [value [current [Hsched [Hcode Hafter]]]]; exact Hcode.
    + exact (proj1 Htail).
  - destruct Hrun as [saved [acquired [Hsave [value [released [Hupdate Hrestore]]]]]].
    eapply tmr_init_task_restore_return_code; exact Hrestore.
Qed.

(** A source decomposition, not a new execution semantics: every conjunct is
    one existing program relation from the very same successful Create trace.
    The TCB payload above owns the exact released/publication witness. *)
Definition tmr_init_task_success_source environment critical sg entry base task_return
  lower old_frame upper original mask LitMap initial final receipt : Prop :=
  let args := tmr_init_task_create_args entry base in
  exists saved acquired stack_call checkpoint stack_result tcb_initial returned current,
    unsigned_last_nbits args.(createPriority) 32 <= 63 /\
    task_create_save_program environment critical sg original mask initial saved acquired /\
    task_create_stack_nesting acquired <= 0 /\
    task_create_stack_priority sg args acquired = 0 /\
    task_create_restore_program environment critical sg (fst saved)
      (task_create_stack_reserved args original acquired) stack_call checkpoint /\
    task_create_stack_init_program sg args stack_call checkpoint stack_result tcb_initial /\
    tmr_init_task_tcb_receipt_output critical sg (tmr_init_task_stack_region base) args task_return
      (tmr_init_task_after_lower entry base lower old_frame upper)
      (tmr_init_task_after_upper entry base lower old_frame upper) (LitMap "?")
      (fst stack_result) tcb_initial returned current receipt /\
    task_create_tcb_return_program environment critical sg args returned mask 0 current 0 final.

Lemma tmr_init_task_success_source_has_receipt :
  forall environment critical sg entry base task_return lower old_frame upper original mask LitMap initial final,
  tmr_init_task_create_program environment critical sg entry base task_return lower old_frame upper
    original mask LitMap initial 0 final ->
  exists receipt, tmr_init_task_success_source environment critical sg entry base task_return
    lower old_frame upper original mask LitMap initial final receipt.
Proof.
  intros environment critical sg entry base task_return lower old_frame upper original mask LitMap initial final Hcreate.
  unfold tmr_init_task_create_program, task_create_program in Hcreate.
  destruct (Z.ltb 63 (unsigned_last_nbits (createPriority (tmr_init_task_create_args entry base)) 32)) eqn:Hpriority.
  - destruct Hcreate as [Hcode Hfinal]; discriminate.
  - apply Z.ltb_ge in Hpriority.
    destruct Hcreate as [saved [acquired [Hsave Hacquired]]].
    destruct Hacquired as [observed [middle [[Hobserved Hmiddle] Hbody]]].
    subst observed middle.
    destruct (Z.ltb 0 (task_create_stack_nesting acquired)) eqn:Hnesting.
    + pose proof (tmr_init_task_restore_return_code _ _ _ _ _ _ _ _ Hbody); discriminate.
    + apply Z.ltb_ge in Hnesting.
      destruct (Z.eqb (task_create_stack_priority sg (tmr_init_task_create_args entry base) acquired) 0) eqn:Hfree.
      * apply Z.eqb_eq in Hfree.
        destruct Hbody as [value [reserved [Hupdate [stack_call [checkpoint [Hrestore Hinitialize]]]]]].
        change (reserved = task_create_stack_reserved (tmr_init_task_create_args entry base) original acquired) in Hupdate.
        subst reserved.
        destruct Hinitialize as [stack_result [tcb_initial [Hstack [tcb_result [current [Htcb Hreturn]]]]]].
        destruct tcb_result as [returned code].
        assert (Hcodes : code = 0 \/ code = 66).
        { destruct Htcb as [released [Hresult Hrest]]; cbn in Hresult; inversion Hresult; auto. }
        pose proof (tmr_init_task_tcb_return_code _ _ _ _ _ _ _ _ _ _ Hcodes Hreturn) as Hcode.
        cbn in Hcode; subst code.
        destruct (tmr_init_task_tcb_source_has_receipt _ _ _ _ _ _ _ _ _ _ _ _ Htcb) as [receipt Hreceipt].
        exists receipt; unfold tmr_init_task_success_source.
        exists saved, acquired, stack_call, checkpoint, stack_result, tcb_initial, returned, current.
        repeat first [assumption | split].
      * pose proof (tmr_init_task_restore_return_code _ _ _ _ _ _ _ _ Hbody); discriminate.
Qed.

Definition tmr_init_task_source_receipt environment critical sg entry base task_return
  lower old_frame upper original mask LitMap initial error final receipt : Prop :=
  tmr_init_task_create_program environment critical sg entry base task_return lower old_frame upper
    original mask LitMap initial error final /\
  if Z.eq_dec error 0 then
    tmr_init_task_success_source environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial final receipt
  else receipt = None.

Lemma tmr_init_task_create_source_has_receipt :
  forall environment critical sg entry base task_return lower old_frame upper original mask LitMap initial error final,
  tmr_init_task_create_program environment critical sg entry base task_return lower old_frame upper
    original mask LitMap initial error final ->
  exists receipt, tmr_init_task_source_receipt environment critical sg entry base task_return lower old_frame upper
    original mask LitMap initial error final receipt.
Proof.
  intros; destruct (Z.eq_dec error 0) as [->|Herror].
  - destruct (tmr_init_task_success_source_has_receipt _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as [receipt Hreceipt].
    exists receipt; split; [exact H|]; destruct (Z.eq_dec 0 0); [exact Hreceipt|contradiction].
  - exists None; split; [exact H|]; destruct (Z.eq_dec error 0); [contradiction|reflexivity].
Qed.

Lemma tmr_init_task_failed_receipt_none :
  forall environment critical sg entry base task_return lower old_frame upper original mask LitMap initial error final receipt,
  error <> 0 ->
  tmr_init_task_source_receipt environment critical sg entry base task_return lower old_frame upper
    original mask LitMap initial error final receipt -> receipt = None.
Proof. intros; destruct H0 as [_ Hreceipt]; destruct (Z.eq_dec error 0); [contradiction|exact Hreceipt]. Qed.

Lemma tmr_init_task_success_receipt_some :
  forall environment critical sg entry base task_return lower old_frame upper original mask LitMap initial final receipt,
  tmr_init_task_success_source environment critical sg entry base task_return lower old_frame upper
    original mask LitMap initial final receipt ->
  exists slot generation, receipt = Some (slot, generation).
Proof.
  intros environment critical sg entry base task_return lower old_frame upper original mask LitMap initial final receipt
    (saved & acquired & stack_call & checkpoint & stack_result & tcb_initial & returned & current &
      Hpriority & Hsave & Hnesting & Hfree & Hrestore & Hstack & Htcb & Hreturn).
  destruct Htcb as (released & Hresult & Hvalid & Hsource & Hsame & Hpreserved & Hready & Hhistory & Hnames & Hpublication).
  destruct Hpublication as (allocated & committed & slot & image & lease & Hreceipt & Hrest).
  exists slot, allocated.(TskState).(taskLifecycle).(taskNextGeneration); exact Hreceipt.
Qed.

Definition tmr_init_task_phase_created environment critical sg entry base task_return lower old_frame upper
  original mask LitMap initial X returned current error receipt : Prop :=
  tmr_init_task_created environment critical sg entry base task_return lower old_frame upper
    original mask LitMap initial X returned current error /\
  tmr_init_task_timer_phase_eq initial current /\
  tmr_init_task_source_receipt environment critical sg entry base task_return lower old_frame upper
    original mask LitMap initial error current receipt.

Lemma tmr_init_task_phase_create_post_open : forall environment critical saved_local sg entry base task_return
  lower old_frame upper original mask LitMap literals initial X error,
  tmr_init_task_stopped initial ->
  task_create_ext_boot_phase_post environment critical saved_local sg (tmr_init_task_stack_region base)
    (tmr_init_task_create_args entry base) task_return lower old_frame upper [] (lower ++ old_frame ++ upper) []
    original mask initial error
    (tmr_init_task_create_postcondition environment critical sg entry base task_return lower old_frame upper original mask LitMap initial X) **
    GlobalStrings_missing LitMap literals |--
  EX returned current receipt,
    coq_prop (tmr_init_task_phase_created environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial X returned current error receipt /\
      task_name_set_admission critical sg returned.(os_sched_call_invocation) 61 (LitMap "uC/OS-II Tmr") current /\
      task_name_set_safe critical sg returned.(os_sched_call_invocation) 61 (LitMap "uC/OS-II Tmr") current
        (tmr_init_task_name_continuation X)) &&
    (task_name_set_closed environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) mask current **
     tmr_init_task_create_residual environment saved_local sg entry base task_return lower old_frame upper
       returned current error ** GlobalStrings_missing LitMap literals).
Proof.
  intros environment critical saved_local sg entry base task_return lower old_frame upper
    original mask LitMap literals initial X error Hstopped; unfold task_create_ext_boot_phase_post; Intros returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  assert (Hsafe : task_create_safe current (StateRelMonad.ret error)
    (tmr_init_task_create_postcondition environment critical sg entry base task_return lower old_frame upper original mask LitMap initial X)) by tauto.
  destruct Hsafe as [start [Hstart Hsafe]]; subst start.
  specialize (Hsafe error current (conj eq_refl eq_refl)).
  assert (Hphase : tmr_init_task_timer_phase_eq initial current).
  { unfold tmr_init_task_timer_phase_eq, tmr_init_task_stopped in *; tauto. }
  destruct (tmr_init_task_create_source_has_receipt environment critical sg entry base task_return
    lower old_frame upper original mask LitMap initial error current (proj1 Hsafe)) as [receipt Hreceipt].
  assert (Hcodes : error = 0 \/ error = 40 \/ error = 60 \/ error = 66).
  { assert (Hex : error = 42 -> 63 < (tmr_init_task_create_args entry base).(createPriority)) by tauto.
    cbn in Hex; tauto || lia. }
  assert (Hinvocation : returned.(os_sched_call_invocation) = original.(os_sched_call_invocation))
    by (unfold task_tcb_init_stack_same_call in Hsame; tauto).
  assert (Hadmit : task_name_set_admission critical sg returned.(os_sched_call_invocation) 61
    (LitMap "uC/OS-II Tmr") current).
  { eapply tmr_init_task_name_admission; exact (proj1 (proj2 (proj2 Hsafe))). }
  assert (Hname : task_name_set_safe critical sg returned.(os_sched_call_invocation) 61
    (LitMap "uC/OS-II Tmr") current (tmr_init_task_name_continuation X)).
  { rewrite Hinvocation; exact (proj2 (proj2 (proj2 Hsafe))). }
  sep_apply_l_atomic (proj1 (tmr_init_task_name_call_resource_equiv environment critical saved_local sg returned mask current)); Intros.
  Exists returned current receipt; unfold tmr_init_task_phase_created, tmr_init_task_created, tmr_init_task_create_residual,
    tmr_init_task_after_lower, tmr_init_task_after_upper; entailer!; tauto.
Qed.

Definition tmr_init_task_phase_post environment critical saved_local sg entry base task_return
  lower old_frame upper original mask LitMap literals initial (X : unit -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned middle create_error receipt current name_error,
    coq_prop (safeExec (eq current) (StateRelMonad.ret tt) X /\
      tmr_init_task_timer_phase_eq initial current) &&
    (coq_prop (tmr_init_task_phase_created environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial X returned middle create_error receipt) **
     coq_prop (task_name_set_post critical sg returned.(os_sched_call_invocation) 61 (LitMap "uC/OS-II Tmr")
        middle name_error current (tmr_init_task_name_continuation X)) **
     task_name_set_closed environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) mask current **
     tmr_init_task_create_residual environment saved_local sg entry base task_return lower old_frame upper
       returned middle create_error ** GlobalStrings_missing LitMap literals).

Lemma tmr_init_task_phase_post_forget :
  forall environment critical saved_local sg entry base task_return lower old_frame upper
    original mask LitMap literals initial X,
  tmr_init_task_phase_post environment critical saved_local sg entry base task_return lower old_frame upper
    original mask LitMap literals initial X |--
  tmr_init_task_post environment critical saved_local sg entry base task_return lower old_frame upper
    original mask LitMap literals initial X.
Proof.
  intros; unfold tmr_init_task_phase_post; Intros returned middle create_error receipt current name_error.
  unfold tmr_init_task_post; Exists returned middle create_error current name_error.
  unfold tmr_init_task_phase_created in *; entailer!; tauto.
Qed.
