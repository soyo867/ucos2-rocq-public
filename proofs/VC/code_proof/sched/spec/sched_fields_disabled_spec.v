Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.flag_fields_resources Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_disabled_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The executing handler keeps its real view. Normal paired-call returns
    retain invocation/origin/context/stack, but may change saved fragments.
    No task-allocation lease is manufactured for an exception stack. *)
Definition sched_fields_same_view (returned original : OsExecutionView) : Prop :=
  returned.(os_execution_invocation) = original.(os_execution_invocation) /\
  returned.(os_execution_origin) = original.(os_execution_origin) /\
  returned.(os_execution_context) = original.(os_execution_context) /\
  returned.(os_execution_stack) = original.(os_execution_stack).

Lemma sched_fields_same_view_refl : forall view, sched_fields_same_view view view.
Proof. intros; unfold sched_fields_same_view; repeat split. Qed.

Lemma sched_fields_same_view_trans : forall last middle first,
  sched_fields_same_view last middle -> sched_fields_same_view middle first ->
  sched_fields_same_view last first.
Proof. unfold sched_fields_same_view; intros; intuition congruence. Qed.

Lemma sched_fields_same_view_entry_source : forall returned original state,
  sched_fields_same_view returned original ->
  sched_disabled_entry_source original state -> sched_disabled_entry_source returned state.
Proof.
  intros returned original state [_ [_ [Hcontext _]]] Hsource.
  unfold sched_disabled_entry_source, sched_disabled_isr_source in *; rewrite Hcontext; exact Hsource.
Qed.

Lemma sched_fields_same_view_completed_clients : forall critical returned original,
  sched_fields_same_view returned original ->
  sched_disabled_completed_clients critical original -> sched_disabled_completed_clients critical returned.
Proof.
  intros critical returned original [_ [_ [Hcontext _]]] Hclients.
  unfold sched_disabled_completed_clients, sched_disabled_context_rely, sched_disabled_isr_source in *.
  rewrite Hcontext; exact Hclients.
Qed.

Definition sched_fields_disabled_closed (environment : TaskStackCallEnvironment)
  local sg view mask state : Assertion :=
  kernel_execution_view_owned environment.(task_stack_call_external)
    environment.(task_stack_call_platform) view mask **
  kernel_continuation_inv environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg None state.

Definition sched_fields_disabled_masked (environment : TaskStackCallEnvironment)
  critical local sg view saved acquired state : Assertion :=
  critical_region_masked environment.(task_stack_call_platform) critical sg
    view.(os_execution_invocation) view.(os_execution_origin) saved acquired **
  os_execution_view_resources environment.(task_stack_call_external) view **
  kernel_continuation_inv environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg None state.

Definition sched_fields_disabled_pre environment critical local sg view mask state
  (frame : Assertion) : Assertion :=
  coq_prop (sched_disabled_completed_clients critical view /\
    sched_disabled_entry_source view state /\ UCOS2_state_inv sg state) &&
  (sched_fields_disabled_closed environment local sg view mask state ** frame).

Definition sched_fields_disabled_restore_pre environment critical local sg view mask saved acquired released
  (frame : Assertion) : Assertion :=
  coq_prop (sched_disabled_completed_clients critical view /\
    sched_disabled_entry_source view released /\ UCOS2_state_inv sg released /\
    interrupt_saved_value mask saved) &&
  (sched_fields_disabled_masked environment critical local sg view saved acquired released ** frame).

Definition sched_fields_heap_cut (owned : Assertion) (captured : model) : Assertion :=
  fun actual => actual = captured /\ owned actual.

Lemma sched_fields_heap_capture : forall (owned : Assertion),
  owned |-- EX captured, sched_fields_heap_cut owned captured.
Proof. intros owned heap Howned; exists heap; split; [reflexivity|exact Howned]. Qed.

(** Explicit conditional linked-C ABI events. Their returned local family
    belongs to the SAME actual footprint and source interval. These are
    contracts to be realized by the linked paired calls, not theorems that
    arbitrary handlers preserve a world or produce a requested receipt. *)
Definition sched_fields_disabled_save_event environment critical sg original returned mask saved
  before acquired local next_local frame (before_heap after_heap : model) : Prop :=
  critical_region_interval critical sg original.(os_execution_invocation) before acquired /\
  sched_fields_same_view returned original /\ interrupt_saved_value mask saved /\
  sched_fields_disabled_pre environment critical local sg original mask before frame before_heap /\
  (sched_fields_disabled_masked environment critical next_local sg returned saved acquired acquired ** frame) after_heap.

Definition sched_fields_disabled_restore_event environment critical sg original returned mask saved
  acquired released current local next_local frame (before_heap after_heap : model) : Prop :=
  critical_region_interval critical sg original.(os_execution_invocation) released current /\
  sched_fields_same_view returned original /\
  sched_fields_disabled_restore_pre environment critical local sg original mask saved acquired released frame before_heap /\
  (sched_fields_disabled_closed environment next_local sg returned mask current ** frame) after_heap.

Definition sched_fields_disabled_save_output environment critical sg original mask before local frame before_heap saved : Assertion :=
  fun after_heap => exists returned acquired next_local,
    sched_fields_disabled_save_event environment critical sg original returned mask saved
      before acquired local next_local frame before_heap after_heap.

Definition sched_fields_disabled_restore_output environment critical sg original mask saved acquired released local frame before_heap : Assertion :=
  fun after_heap => exists returned current next_local,
    sched_fields_disabled_restore_event environment critical sg original returned mask saved
      acquired released current local next_local frame before_heap after_heap.

Definition sched_fields_disabled_post environment critical sg original mask before local frame : Assertion :=
  fun after_heap => exists saved entered acquired entered_local first_heap saved_heap restore_heap,
    sched_fields_disabled_save_event environment critical sg original entered mask saved
      before acquired local entered_local frame first_heap saved_heap /\
    sched_fields_disabled_restore_output environment critical sg entered mask saved acquired acquired
      entered_local frame restore_heap after_heap.

Lemma sched_fields_disabled_save_output_open : forall environment critical sg original mask before local frame before_heap saved,
  sched_fields_disabled_save_output environment critical sg original mask before local frame before_heap saved |--
  EX returned acquired next_local after_heap,
    coq_prop (sched_fields_disabled_save_event environment critical sg original returned mask saved
      before acquired local next_local frame before_heap after_heap /\
      sched_disabled_completed_clients critical returned /\ sched_disabled_entry_source returned acquired /\
      UCOS2_state_inv sg acquired /\ interrupt_saved_value mask saved) &&
    (sched_fields_disabled_masked environment critical next_local sg returned saved acquired acquired ** frame).
Proof.
  intros environment critical sg original mask before local frame before_heap saved heap
    [returned [acquired [next_local Hevent]]].
  pose proof Hevent as [Hinterval [Hsame [Hsaved [[[Hclients [Hsource Hvalid]] Hbefore] Hafter]]]].
  destruct (sched_disabled_interval_preserves_context critical sg original
    original.(os_execution_invocation) before acquired Hclients Hvalid Hinterval) as [Hacquired Hrely].
  pose proof (sched_disabled_context_rely_preserves_entry_source original sg before acquired Hrely Hsource) as Hentry.
  exists returned, acquired, next_local, heap; split; [|exact Hafter].
  split; [exact Hevent|]. split.
  - eapply sched_fields_same_view_completed_clients; eassumption.
  - split; [eapply sched_fields_same_view_entry_source; eassumption|auto].
Qed.

Definition sched_fields_disabled_counter_frame environment critical local sg view saved acquired state : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\ interrupt_in_range state.(IntrState) /\
    task_stack_live_coverage state.(TskState) None) &&
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     view.(os_execution_invocation) view.(os_execution_origin) saved acquired **
   os_execution_view_resources environment.(task_stack_call_external) view **
   UCOS2_fields_raw_rep_missing_module sg state InterruptModule ** unmap_table_rep sg **
   store_parked_continuations
     (kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState) local)
     state.(TskState).(parkedTaskStacks)).

Lemma sched_fields_disabled_masked_split_counters : forall environment critical local sg view saved acquired state,
  sched_fields_disabled_masked environment critical local sg view saved acquired state --||--
  (sg.(g_OSIntNesting) # UChar |-> os_sched_ints state **
   sg.(g_OSLockNesting) # UChar |-> os_sched_locks state **
   sched_fields_disabled_counter_frame environment critical local sg view saved acquired state).
Proof.
  intros; unfold sched_fields_disabled_masked, kernel_continuation_inv.
  rewrite kernel_program_fields_inv_split_unmap.
  rewrite (UCOS2_fields_inv_split_module sg state InterruptModule) by discriminate.
  cbn [UCOS2_module_rep].
  unfold sched_fields_disabled_counter_frame, interrupt_inv, store_int_state, os_sched_ints, os_sched_locks.
  split; entailer!.
Qed.

Lemma sched_fields_disabled_post_from_restore : forall environment critical sg original mask before local frame
  saved entered acquired entered_local first_heap saved_heap restore_heap,
  sched_fields_disabled_save_event environment critical sg original entered mask saved
    before acquired local entered_local frame first_heap saved_heap ->
  sched_fields_disabled_restore_output environment critical sg entered mask saved acquired acquired
    entered_local frame restore_heap |--
  sched_fields_disabled_post environment critical sg original mask before local frame.
Proof.
  intros environment critical sg original mask before local frame saved entered acquired entered_local
    first_heap saved_heap restore_heap Hsave heap Hrestore.
  exists saved, entered, acquired, entered_local, first_heap, saved_heap, restore_heap; auto.
Qed.

Lemma sched_fields_disabled_post_resources : forall environment critical sg original mask before local frame,
  sched_fields_disabled_post environment critical sg original mask before local frame |--
  EX returned current next_local,
    coq_prop (sched_fields_same_view returned original /\
      sched_disabled_entry_source returned current /\ UCOS2_state_inv sg current) &&
    (sched_fields_disabled_closed environment next_local sg returned mask current ** frame).
Proof.
  intros environment critical sg original mask before local frame heap
    [saved [entered [acquired [entered_local [first_heap [saved_heap [restore_heap [Hsave
      [returned [current [next_local Hrestore]]]]]]]]]]].
  destruct Hsave as [Hsave_interval [Hentered [Hsaved Hsave_rest]]].
  destruct Hrestore as [Hinterval [Hreturned [[[Hclients [Hsource [Hvalid Hword]]] Hpre] Hpost]]].
  destruct (sched_disabled_interval_preserves_context critical sg entered
    entered.(os_execution_invocation) acquired current Hclients Hvalid Hinterval) as [Hcurrent Hrely].
  pose proof (sched_disabled_context_rely_preserves_entry_source entered sg acquired current Hrely Hsource) as Hentry.
  exists returned, current, next_local; split; [|exact Hpost].
  split; [eapply sched_fields_same_view_trans; eassumption|].
  split; [eapply sched_fields_same_view_entry_source; eassumption|exact Hcurrent].
Qed.
