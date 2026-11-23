Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_program_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Import UCOS2_C_Rules KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A deliberately small SOURCE registry. These are the two checked
    counter bodies, not a claim that arbitrary BSP code only calls these
    functions. Extending the registry requires another actual heap proof.
    In particular a pure KernelClientCertificate is not sufficient.

    No validity, table, ready-task or continuation fact occurs in the
    source relation below. Actual guards are physical byte reads, not an
    assumed result of the BSP execution. *)
Inductive RestoreHandlerClientKind : Type :=
| RestoreHandlerIntEnter
| RestoreHandlerIntExitNoSchedule.

(** The source relation exposed to the BSP contract has NO abstract OS
    state argument. Its entry read chooses the actual guarded body. *)
Inductive restore_handler_int_enter_execution (sg : StableGlobVars) : model -> model -> Prop :=
| RestoreHandlerEnterInactive : forall heap,
    uchar_load sg.(g_OSRunning) 0 heap ->
    restore_handler_int_enter_execution sg heap heap
| RestoreHandlerEnterSaturated : forall heap nesting,
    uchar_load sg.(g_OSRunning) 1 heap ->
    uchar_load sg.(g_OSIntNesting) nesting heap -> 255 <= nesting ->
    restore_handler_int_enter_execution sg heap heap
| RestoreHandlerEnterIncrement : forall before nesting after,
    uchar_load sg.(g_OSRunning) 1 before ->
    uchar_load sg.(g_OSIntNesting) nesting before -> nesting < 255 ->
    kernel_heap_execution [(sg.(g_OSIntNesting), nesting + 1)] before after ->
    restore_handler_int_enter_execution sg before after.

Inductive restore_handler_client_execution (sg : StableGlobVars)
  : RestoreHandlerClientKind -> model -> model -> Prop :=
| RestoreHandlerEnterExecution : forall before after,
    restore_handler_int_enter_execution sg before after ->
    restore_handler_client_execution sg RestoreHandlerIntEnter before after
| RestoreHandlerExitExecution : forall before after,
    os_int_exit_masked_no_schedule_fragment sg before after ->
    restore_handler_client_execution sg RestoreHandlerIntExitNoSchedule before after.

(** The indexed state relation is INTERNAL to the checked registry. It is
    obtained from input ownership and physical reads, never from the BSP. *)
Inductive restore_handler_client_source (sg : StableGlobVars)
  : RestoreHandlerClientKind -> UCOS2_Verify_State -> model ->
      UCOS2_Verify_State -> model -> Prop :=
| RestoreHandlerIntEnterSource : forall state before after,
    kernel_heap_execution (os_int_enter_heap_writes sg state) before after ->
    restore_handler_client_source sg RestoreHandlerIntEnter state before
      (os_int_enter_state state) after
| RestoreHandlerIntExitNoScheduleSource : forall state before after,
    os_int_exit_masked_no_schedule_fragment sg before after ->
    restore_handler_client_source sg RestoreHandlerIntExitNoSchedule state before
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) after.

(** The table and focused capsule are an ordinary frame ONLY across the
    checked counter body. They are not a private frame across unknown BSP
    execution. Determinism connects the producer to the supplied heap. *)
Lemma restore_handler_int_enter_preserves_world : forall external platform port
  (continuations : Armv7aContinuationABI external platform port) focus sg state
  (frame : Assertion) before after,
  (armv7a_continuation_world continuations focus (kernel_program_inv sg) state ** frame) before ->
  kernel_heap_execution (os_int_enter_heap_writes sg state) before after ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg)
     (os_int_enter_state state) ** frame) after.
Proof.
  intros external platform port continuations focus sg state frame before after Hpre Hsource.
  assert (Hsplit : armv7a_continuation_world continuations focus (kernel_program_inv sg)
      state ** frame |-- UCOS2_inv sg state **
      (unmap_table_rep sg ** armv7a_parked_continuations continuations focus state ** frame)).
  { rewrite kernel_program_continuation_world_split_unmap.
    unfold armv7a_continuation_world; entailer!. }
  destruct (os_int_enter_source_heap_frames_private sg state _ before (Hsplit before Hpre))
    as [produced [Hrun Hpost]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced.
  assert (Hmerge : UCOS2_inv sg (os_int_enter_state state) **
      (unmap_table_rep sg ** armv7a_parked_continuations continuations focus state ** frame) |--
    armv7a_continuation_world continuations focus (kernel_program_inv sg)
      (os_int_enter_state state) ** frame).
  { rewrite kernel_program_continuation_world_split_unmap.
    unfold armv7a_continuation_world, armv7a_parked_continuations, os_int_enter_state.
    cbn [replace_IntrS TskState]; entailer!. }
  exact (Hmerge after Hpost).
Qed.

Lemma restore_handler_no_schedule_preserves_world : forall external platform port
  (continuations : Armv7aContinuationABI external platform port) focus sg state
  (frame : Assertion) before after,
  (armv7a_continuation_world continuations focus (kernel_program_inv sg) state ** frame) before ->
  os_int_exit_masked_no_schedule_fragment sg before after ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg)
     (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros external platform port continuations focus sg state frame before after Hpre Hsource.
  assert (Hsplit : armv7a_continuation_world continuations focus (kernel_program_inv sg) state ** frame |--
    UCOS2_inv sg state **
      (unmap_table_rep sg ** armv7a_parked_continuations continuations focus state ** frame)).
  { rewrite kernel_program_continuation_world_split_unmap.
    unfold armv7a_continuation_world; entailer!. }
  destruct (Hsplit before Hpre) as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
  destruct (os_int_exit_masked_counter_raw_post sg state owned Hraw) as [middle [Hcounter Hraw_after]].
  destruct (os_int_exit_masked_counter_fragment_frame sg owned _ middle rest before Hcounter Hjoin)
    as [produced [Hwhole Hjoined]].
  assert (produced = after).
  { destruct Hsource; eapply os_int_exit_masked_counter_final_eq; eassumption. }
  subst produced.
  assert (Hafter : (UCOS2_inv sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
    (unmap_table_rep sg ** armv7a_parked_continuations continuations focus state ** frame)) after).
  { exists middle, rest; split; [exact Hjoined|]. split; [split; assumption|exact Hrest]. }
  assert (Hmerge : UCOS2_inv sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
      (unmap_table_rep sg ** armv7a_parked_continuations continuations focus state ** frame) |--
    armv7a_continuation_world continuations focus (kernel_program_inv sg)
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame).
  { rewrite kernel_program_continuation_world_split_unmap.
    unfold armv7a_continuation_world, armv7a_parked_continuations, os_int_exit_counter_state.
    cbn [replace_IntrS TskState]; entailer!. }
  exact (Hmerge after Hafter).
Qed.

(** This registry certificate is proved from the concrete source producers;
    it is NOT a new BSP or CPU assumption. *)
Lemma restore_handler_client_preserves_world : forall external platform port
  (continuations : Armv7aContinuationABI external platform port) focus sg kind state before
  returned after (frame : Assertion),
  restore_handler_client_source sg kind state before returned after ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg) state ** frame) before ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg) returned ** frame) after.
Proof.
  intros external platform port continuations focus sg kind state before returned after frame
    Hsource Hpre; destruct Hsource.
  - eapply restore_handler_int_enter_preserves_world; eassumption.
  - eapply restore_handler_no_schedule_preserves_world; eassumption.
Qed.

Lemma restore_handler_client_task_sched_eq : forall sg kind state before returned after,
  restore_handler_client_source sg kind state before returned after ->
  returned.(TskState) = state.(TskState) /\ returned.(SchedState) = state.(SchedState).
Proof. intros; destruct H; split; reflexivity. Qed.

Lemma restore_handler_client_execution_source : forall external platform port
  (continuations : Armv7aContinuationABI external platform port) focus sg kind state before after
  (frame : Assertion),
  restore_handler_client_execution sg kind before after ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg) state ** frame) before ->
  exists returned, restore_handler_client_source sg kind state before returned after.
Proof.
  intros external platform port continuations focus sg kind state before after frame Hsource Hpre.
  destruct Hsource as [before after Henter|before after Hexit].
  - assert (Hsplit : armv7a_continuation_world continuations focus (kernel_program_inv sg) state ** frame |--
      UCOS2_inv sg state **
        (unmap_table_rep sg ** armv7a_parked_continuations continuations focus state ** frame)).
    { rewrite kernel_program_continuation_world_split_unmap.
      unfold armv7a_continuation_world; entailer!. }
    destruct (Hsplit before Hpre) as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
    pose proof (uchar_load_frame _ _ _ _ _ (os_int_exit_raw_running_load sg state owned Hraw) Hjoin) as Hr.
    pose proof (uchar_load_frame _ _ _ _ _ (os_int_exit_raw_nesting_load sg state owned Hraw) Hjoin) as Hn.
    exists (os_int_enter_state state); constructor; unfold os_int_enter_heap_writes.
    destruct Henter as [heap Hread|heap nesting Hread Hnest Hsat|heap nesting final Hread Hnest Hbelow Hwrite].
    + pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
      destruct state.(SchedState).(isRunning); [discriminate|].
      split; [constructor|split; reflexivity].
    + pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
      pose proof (uchar_load_deterministic _ _ _ _ Hnest Hn) as ->.
      destruct state.(SchedState).(isRunning); [|discriminate].
      assert ((state.(IntrState).(intNesting) <? 255) = false) as -> by (apply Z.ltb_ge; exact Hsat).
      split; [constructor|split; reflexivity].
    + pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
      pose proof (uchar_load_deterministic _ _ _ _ Hnest Hn) as ->.
      destruct state.(SchedState).(isRunning); [|discriminate].
      assert ((state.(IntrState).(intNesting) <? 255) = true) as -> by (apply Z.ltb_lt; exact Hbelow).
      exact Hwrite.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state); constructor; exact Hexit.
Qed.

(** The invocation/return word identify the actual BL OS_CPU_ExceptHndlr
    call, independently of the interrupted public Restore call. Neither is
    an ownership resource: physical handler resources must already be held.
    [local] is the implementation's private cursor/stack state. *)
Record RestoreHandlerCall : Type := restore_handler_call {
  restore_handler_invocation : nat;
  restore_handler_return_word : Z
}.

Record RestoreHandlerCursor (Local : Type) : Type := restore_handler_cursor {
  restore_handler_current_call : RestoreHandlerCall;
  restore_handler_pc : Z;
  restore_handler_local : Local
}.
Arguments restore_handler_cursor {Local}.
Arguments restore_handler_current_call {Local}.
Arguments restore_handler_pc {Local}.
Arguments restore_handler_local {Local}.

Definition restore_handler_return_cursor {Local} (cursor : RestoreHandlerCursor Local)
  (return_word : Z) : RestoreHandlerCursor Local :=
  restore_handler_cursor cursor.(restore_handler_current_call) return_word
    cursor.(restore_handler_local).

Record RestoreHandlerKernelCall : Type := restore_handler_kernel_call {
  restore_handler_kernel_kind : RestoreHandlerClientKind;
  restore_handler_kernel_call_pc : Z;
  restore_handler_kernel_return_pc : Z
}.

(** Each Kernel constructor is a completed, matched call/return boundary
    for one checked body. Arbitrary local work is retained as Local steps;
    it is not replaced with an empty heap update. No unmatched callback can
    disappear at the outer Return. Nested BSP work may be represented by
    its own private stack in Local; unsupported kernel bodies require a
    registry extension, not a fictitious Local no-op. *)
Inductive restore_handler_execution {Local}
  (local_step : RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop)
  (sg : StableGlobVars)
  : RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop :=
| RestoreHandlerReturn : forall cursor heap,
    restore_handler_execution local_step sg cursor heap cursor heap
| RestoreHandlerLocal : forall cursor before middle_cursor middle returned_cursor after,
    local_step cursor before middle_cursor middle ->
    restore_handler_execution local_step sg middle_cursor middle returned_cursor after ->
    restore_handler_execution local_step sg cursor before returned_cursor after
| RestoreHandlerKernel : forall cursor before call middle returned_cursor after,
    cursor.(restore_handler_pc) = call.(restore_handler_kernel_call_pc) ->
    restore_handler_client_execution sg call.(restore_handler_kernel_kind) before middle ->
    restore_handler_execution local_step sg
      (restore_handler_return_cursor cursor call.(restore_handler_kernel_return_pc)) middle
      returned_cursor after ->
    restore_handler_execution local_step sg cursor before returned_cursor after.

(** Exactly two external laws for the unavailable BSP implementation:
    (1) an ACTUAL normal return refines a finite matched interaction and
        returns through the same BL continuation;
    (2) a Local step acts on its owned private resource and frames every
        separating resource on that SAME step.

    The laws contain no OS validity/ready/table/selected-caller conclusion.
    They do not assert existence or eventual termination of a return, and
    no instance for a platform implementation is postulated here. *)
Record RestoreHandlerContract {Local}
  (private : RestoreHandlerCall -> Local -> Assertion)
  (local_step : RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop)
  (normal_return : StableGlobVars -> RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop)
  : Prop := {
  restore_handler_return_refinement : forall sg cursor before returned_cursor after,
    normal_return sg cursor before returned_cursor after ->
    returned_cursor.(restore_handler_current_call) = cursor.(restore_handler_current_call) /\
    returned_cursor.(restore_handler_pc) =
      cursor.(restore_handler_current_call).(restore_handler_return_word) /\
    restore_handler_execution local_step sg cursor before returned_cursor after;
  restore_handler_local_resources : forall cursor before returned_cursor after (frame : Assertion),
    local_step cursor before returned_cursor after ->
    (private cursor.(restore_handler_current_call) cursor.(restore_handler_local) ** frame) before ->
    (private returned_cursor.(restore_handler_current_call) returned_cursor.(restore_handler_local) ** frame) after
}.

Lemma restore_handler_execution_preserves_world : forall external platform port
  (continuations : Armv7aContinuationABI external platform port) focus Local
  (private : RestoreHandlerCall -> Local -> Assertion) local_step normal_return,
  RestoreHandlerContract private local_step normal_return ->
  forall sg cursor before returned_cursor after (frame : Assertion),
  restore_handler_execution local_step sg cursor before returned_cursor after ->
  forall state,
  (armv7a_continuation_world continuations focus (kernel_program_inv sg) state **
    (private cursor.(restore_handler_current_call) cursor.(restore_handler_local) ** frame)) before ->
  exists final,
    final.(TskState) = state.(TskState) /\ final.(SchedState) = state.(SchedState) /\
    (armv7a_continuation_world continuations focus (kernel_program_inv sg) final **
      (private returned_cursor.(restore_handler_current_call) returned_cursor.(restore_handler_local) ** frame)) after.
Proof.
  intros external platform port continuations focus Local private local_step normal_return Hcontract
    sg cursor before returned_cursor after frame Hrun; induction Hrun; intros state Hpre.
  - exists state; split; [reflexivity|]. split; [reflexivity|exact Hpre].
  - apply IHHrun.
    assert (Horder : armv7a_continuation_world continuations focus (kernel_program_inv sg) state **
        (private cursor.(restore_handler_current_call) cursor.(restore_handler_local) ** frame) |--
      private cursor.(restore_handler_current_call) cursor.(restore_handler_local) **
        (armv7a_continuation_world continuations focus (kernel_program_inv sg) state ** frame)) by entailer!.
    pose proof (restore_handler_local_resources _ _ _ Hcontract _ _ _ _ _ H
      (Horder before Hpre)) as Hmiddle.
    assert (Hback : private middle_cursor.(restore_handler_current_call) middle_cursor.(restore_handler_local) **
        (armv7a_continuation_world continuations focus (kernel_program_inv sg) state ** frame) |--
      armv7a_continuation_world continuations focus (kernel_program_inv sg) state **
        (private middle_cursor.(restore_handler_current_call) middle_cursor.(restore_handler_local) ** frame))
      by entailer!.
    exact (Hback middle Hmiddle).
  - destruct (restore_handler_client_execution_source external platform port continuations focus sg
      _ state before middle _ H0 Hpre) as [middle_state Hsource].
    pose proof (restore_handler_client_preserves_world external platform port continuations focus sg
      _ state before middle_state middle _ Hsource Hpre) as Hmiddle.
    destruct (IHHrun middle_state Hmiddle) as [final [Ht [Hs Hpost]]].
    destruct (restore_handler_client_task_sched_eq _ _ _ _ _ _ Hsource) as [Ht' Hs'].
    exists final; split; [congruence|]. split; [congruence|exact Hpost].
Qed.

(** The actual supplied normal-return heap, not an existential replacement.
    Every program byte is carried through each real callback producer. *)
Lemma restore_handler_normal_return_preserves_world : forall external platform port
  (continuations : Armv7aContinuationABI external platform port) focus Local
  (private : RestoreHandlerCall -> Local -> Assertion) local_step normal_return,
  RestoreHandlerContract private local_step normal_return ->
  forall sg state cursor before returned_cursor after (frame : Assertion),
  normal_return sg cursor before returned_cursor after ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg) state **
    (private cursor.(restore_handler_current_call) cursor.(restore_handler_local) ** frame)) before ->
  exists final,
    restore_handler_execution local_step sg cursor before returned_cursor after /\
    returned_cursor.(restore_handler_current_call) = cursor.(restore_handler_current_call) /\
    returned_cursor.(restore_handler_pc) =
      cursor.(restore_handler_current_call).(restore_handler_return_word) /\
    final.(TskState) = state.(TskState) /\ final.(SchedState) = state.(SchedState) /\
    (armv7a_continuation_world continuations focus (kernel_program_inv sg) final **
      (private returned_cursor.(restore_handler_current_call) returned_cursor.(restore_handler_local) ** frame)) after.
Proof.
  intros external platform port continuations focus Local private local_step normal_return Hcontract
    sg state cursor before returned_cursor after frame Hreturn Hpre.
  destruct (restore_handler_return_refinement _ _ _ Hcontract sg cursor before returned_cursor after Hreturn)
    as [Hcall [Hpc Hrun]].
  destruct (restore_handler_execution_preserves_world external platform port continuations focus Local
    private local_step normal_return Hcontract sg cursor before returned_cursor after frame Hrun state Hpre)
    as [final [Ht [Hs Hpost]]].
  exists final; split; [exact Hrun|]. split; [exact Hcall|]. split; [exact Hpc|].
  split; [exact Ht|]. split; [exact Hs|].
  exact Hpost.
Qed.
