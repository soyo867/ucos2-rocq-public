Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The active assertion describes this call's resources separately from
    the saved-map interpretation. Only the actual protected Scheduler prefix
    must preserve it. Fresh/Waiting follow from unchanged Task/Flag state;
    global ready-list facts can also be retained because this prefix leaves
    that list unchanged. External Save/Switch/Restore events separately bind
    the actual input and returned active resources. *)
Definition os_sched_active_local_stable
  (active : OsSchedCallContext -> UCOS2_Verify_State -> Assertion) : Prop :=
  forall call state,
    active call state --||-- active call (os_sched_prefix_state state).

Lemma os_sched_active_prefix_transport : forall active call state,
  os_sched_active_local_stable active ->
  active call state --||-- active call (os_sched_prefix_state state).
Proof. intros active call state H; apply H. Qed.

Lemma os_sched_active_local_stable_of_fields : forall active,
  (forall call before after,
    before.(TskState) = after.(TskState) -> before.(FlagState) = after.(FlagState) ->
    active call before --||-- active call after) ->
  os_sched_active_local_stable active.
Proof. intros active H call state; apply H; reflexivity. Qed.

Definition os_sched_active_heap_cut (owned : Assertion) (captured : model) : Assertion :=
  fun actual => actual = captured /\ owned actual.

Lemma os_sched_active_heap_capture : forall (owned : Assertion),
  owned |-- EX captured, os_sched_active_heap_cut owned captured.
Proof. intros owned heap H; exists heap; split; [reflexivity|exact H]. Qed.

Definition os_sched_active_save_input environment critical local active sg call mask state : Assertion :=
  coq_prop (os_sched_call_cut sg call state /\ kernel_sched_ready_clients critical) &&
  (os_sched_fields_save_input environment critical local sg call mask state ** active call state).

Definition os_sched_active_restore_input environment critical local active sg call saved acquired state : Assertion :=
  os_sched_fields_restore_input environment critical local sg call saved acquired state ** active call state.

Definition os_sched_active_call_pre environment local active sg call mask state : Assertion :=
  coq_prop (os_sched_active_local_stable active /\ os_sched_call_cut sg call state) &&
  (kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg (task_stack_call_active_key call) call mask state ** active call state).

Lemma os_sched_active_call_pre_open : forall environment critical local active sg call mask state,
  kernel_sched_ready_clients critical ->
  os_sched_active_call_pre environment local active sg call mask state |--
  coq_prop (os_sched_active_local_stable active) &&
    (os_sched_active_save_input environment critical local active sg call mask state ** unmap_table_rep sg).
Proof.
  intros; unfold os_sched_active_call_pre, os_sched_active_save_input; Intros.
  sep_apply_l_atomic (proj2 (os_sched_fields_save_input_closed_world
    environment critical local sg call mask state)); entailer!; tauto.
Qed.

Definition os_sched_active_switch_pre environment critical local active sg call saved acquired entry : Assertion :=
  os_sched_fields_switch_pre environment critical local kernel_program_fields_inv sg call saved acquired entry **
  active call (os_sched_prefix_state entry).

Definition os_sched_active_body_post environment critical active sg call saved acquired entry : Assertion :=
  EX returned current next_local,
    coq_prop (os_sched_c_return environment.(task_stack_call_external) critical sg entry call returned current) &&
    (kernel_continuation_call_masked environment.(task_stack_call_continuations) kernel_program_fields_inv
      next_local critical sg (task_stack_call_active_key returned) returned saved acquired current **
     active returned current).

(** These are conditional linked-C ABI events, not a theorem that arbitrary
    external code preserves a requested active assertion. Each event binds
    the input and returned resources on the actual paired-call footprint.
    Saved-local families and call fragments may change at each endpoint. *)
Definition os_sched_active_save_event environment critical local active sg original mask saved before
  returned acquired next_local (before_heap after_heap : model) : Prop :=
  os_sched_continuation_save_effect environment critical sg original mask saved before returned acquired /\
  task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
  task_tcb_init_stack_source_preserved original before acquired /\ os_sched_call_cut sg returned acquired /\
  os_sched_active_save_input environment critical local active sg original mask before before_heap /\
  os_sched_active_restore_input environment critical next_local active sg returned saved acquired acquired after_heap.

Definition os_sched_active_save_output environment critical local active sg original mask saved before before_heap : Assertion :=
  fun after_heap => exists returned acquired next_local,
    os_sched_active_save_event environment critical local active sg original mask saved before
      returned acquired next_local before_heap after_heap.

Lemma os_sched_active_save_output_open : forall environment critical local active sg original mask saved before before_heap,
  os_sched_active_save_output environment critical local active sg original mask saved before before_heap |--
  EX returned acquired next_local,
    coq_prop (os_sched_continuation_save_effect environment critical sg original mask saved before returned acquired /\
      task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
      task_tcb_init_stack_source_preserved original before acquired /\ os_sched_call_cut sg returned acquired) &&
    os_sched_active_restore_input environment critical next_local active sg returned saved acquired acquired.
Proof.
  intros environment critical local active sg original mask saved before before_heap heap
    [returned [acquired [next_local [Heffect [Hsame [Hsaved [Hsource [Hcut [Hpre Hpost]]]]]]]]].
  exists returned, acquired, next_local; split.
  - exact (conj Heffect (conj Hsame (conj Hsaved (conj Hsource Hcut)))).
  - exact Hpost.
Qed.

Definition os_sched_active_switch_event environment critical local active sg call saved acquired entry
  (before_heap after_heap : model) : Prop :=
  os_sched_active_switch_pre environment critical local active sg call saved acquired entry before_heap /\
  os_sched_active_body_post environment critical active sg call saved acquired entry after_heap.

Definition os_sched_active_switch_output environment critical local active sg call saved acquired entry before_heap : Assertion :=
  fun after_heap => os_sched_active_switch_event environment critical local active sg call saved acquired entry before_heap after_heap.

Lemma os_sched_active_switch_output_open : forall environment critical local active sg call saved acquired entry before_heap,
  os_sched_active_switch_output environment critical local active sg call saved acquired entry before_heap |--
  os_sched_active_body_post environment critical active sg call saved acquired entry.
Proof. intros; intros heap [_ Hpost]; exact Hpost. Qed.

Lemma os_sched_active_body_restore_input : forall environment critical active sg call saved acquired entry,
  os_sched_active_body_post environment critical active sg call saved acquired entry |--
  EX returned current next_local,
    coq_prop (os_sched_c_return environment.(task_stack_call_external) critical sg entry call returned current /\
      UCOS2_state_inv sg current) &&
    (os_sched_active_restore_input environment critical next_local active sg returned saved acquired current ** unmap_table_rep sg).
Proof.
  intros; unfold os_sched_active_body_post; Intros returned current next_local.
  Exists returned current next_local.
  sep_apply_l_atomic (proj2 (os_sched_fields_restore_input_masked_world
    environment critical next_local sg returned saved acquired current)).
  unfold os_sched_active_restore_input, os_sched_fields_restore_input, UCOS2_fields_inv; entailer!.
Qed.

Definition os_sched_active_restore_event environment critical local active sg original saved acquired released
  returned current next_local (before_heap after_heap : model) : Prop :=
  os_sched_continuation_restore_effect environment critical sg original released returned current /\
  task_tcb_init_stack_same_call returned original /\
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
  (UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved original released current) /\
  os_sched_active_restore_input environment critical local active sg original saved acquired released before_heap /\
  (os_sched_fields_save_input environment critical next_local sg returned (armv7a_irq_fiq_mask saved) current **
   active returned current) after_heap.

Definition os_sched_active_restore_output environment critical local active sg original saved acquired released before_heap : Assertion :=
  fun after_heap => exists returned current next_local,
    os_sched_active_restore_event environment critical local active sg original saved acquired released
      returned current next_local before_heap after_heap.

Lemma os_sched_active_restore_output_open : forall environment critical local active sg original saved acquired released before_heap,
  os_sched_active_restore_output environment critical local active sg original saved acquired released before_heap |--
  EX returned current next_local,
    coq_prop (os_sched_continuation_restore_effect environment critical sg original released returned current /\
      task_tcb_init_stack_same_call returned original /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
      (UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved original released current)) &&
    (os_sched_fields_save_input environment critical next_local sg returned (armv7a_irq_fiq_mask saved) current **
     active returned current).
Proof.
  intros environment critical local active sg original saved acquired released before_heap heap
    [returned [current [next_local [Heffect [Hsame [Hpreserved [Hsource [Hpre Hpost]]]]]]]].
  exists returned, current, next_local; split.
  - exact (conj Heffect (conj Hsame (conj Hpreserved Hsource))).
  - exact Hpost.
Qed.

Definition os_sched_active_history_return_post environment critical active sg original mask before : Assertion :=
  EX returned current next_local,
    coq_prop (os_sched_continuation_call_history environment critical sg original mask before returned current /\
      task_tcb_init_stack_same_call returned original /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current)) &&
    (kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_fields_inv
      next_local sg (task_stack_call_active_key returned) returned mask current ** active returned current).

Lemma os_sched_active_restore_output_return : forall environment critical local active sg
  original scheduled resumed mask saved before entry released before_heap,
  os_sched_continuation_save_effect environment critical sg original mask saved before scheduled entry ->
  task_tcb_init_stack_same_call scheduled original ->
  (kernel_call_task_source original before -> kernel_call_task_source scheduled entry) ->
  (os_sched_requests_switch entry = true -> os_sched_current_storage_binding sg scheduled entry) ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry scheduled resumed released ->
  UCOS2_state_inv sg released -> interrupt_saved_value mask saved ->
  os_sched_active_restore_output environment critical local active sg resumed saved entry released before_heap **
    unmap_table_rep sg |-- os_sched_active_history_return_post environment critical active sg original mask before.
Proof.
  intros environment critical local active sg original scheduled resumed mask saved before entry released before_heap
    Hsave Hscheduled Hentry_source Hcut Hbody Hvalid Hsaved.
  sep_apply_l_atomic (os_sched_active_restore_output_open environment critical local active sg resumed saved entry released before_heap).
  Intros returned current next_local.
  assert (Hrestore : os_sched_continuation_restore_effect environment critical sg resumed released returned current) by tauto.
  assert (Hreturned : task_tcb_init_stack_same_call returned resumed) by tauto.
  assert (Hsource : task_tcb_init_stack_source_preserved resumed released current) by tauto.
  assert (Hhistory : os_sched_continuation_call_history environment critical sg original mask before returned current).
  { exists scheduled, entry, resumed, released, saved; repeat split; assumption. }
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { eapply os_sched_continuation_call_history_same_call; exact Hhistory. }
  assert (Hfinal_source : kernel_call_task_source original before -> kernel_call_task_source returned current).
  { intro Hinitial.
    pose proof (os_sched_continuation_c_return_source _ _ _ _ _ _ _ Hcut Hbody (Hentry_source Hinitial)) as Hreleased.
    apply (proj2 (task_tcb_init_stack_same_call_source_iff returned resumed current Hreturned)).
    apply Hsource; exact Hreleased. }
  sep_apply_l_atomic (proj1 (os_sched_fields_save_input_closed_world environment critical next_local sg returned
    (armv7a_irq_fiq_mask saved) current)).
  rewrite (proj2 Hsaved).
  unfold os_sched_active_history_return_post; Exists returned current next_local; entailer!.
Qed.
