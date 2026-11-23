Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_program_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Import UCOS2_C_Rules KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The registry carries the WHOLE existing continuation map. The table is
    one shared program owner, not a private loan across arbitrary clients. *)
Definition kernel_client_heap_world {external platform port}
  (abi : Armv7aContinuationABI external platform port) sg state : Assertion :=
  kernel_program_inv sg state ** armv7a_task_continuations abi state.(TskState).(parkedTaskStacks).

(** These cuts are resource stages, not public API input restrictions. A
    publication cut must be supplied by the actual TCBInit caller AFTER its
    earlier stores. It cannot be obtained merely from a closed world. Extra
    cuts let independent source owners register allocations, switched tasks,
    nested calls and other legitimate intermediate states. *)
Inductive KernelClientHeapCut (Extra : Type) : Type :=
| KernelClientHeapClosed
| KernelClientHeapTaskPublication (publication : TaskCreateStackPublication)
| KernelClientHeapExtra (cut : Extra).
Arguments KernelClientHeapClosed {Extra}.
Arguments KernelClientHeapTaskPublication {Extra}.
Arguments KernelClientHeapExtra {Extra}.

Definition kernel_client_heap_publication {external platform port}
  (abi : Armv7aContinuationABI external platform port) sg publication state : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\
    task_create_stack_publication_input sg publication state /\
    0 <= (task_create_stack_publication_args publication).(initPrio) < 64 /\
    0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296) &&
  (task_tcb_init_publication_tail_storage sg (task_create_stack_publication_args publication)
     state publication.(stack_publication_slot) publication.(stack_publication_image) **
   task_stack_storage publication.(stack_publication_region)
     (task_create_stack_publication_words publication) **
   armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg).

Definition kernel_client_heap_resources {external platform port Extra}
  (abi : Armv7aContinuationABI external platform port)
  (extra_resources : StableGlobVars -> Extra -> UCOS2_Verify_State -> Assertion)
  sg (cut : KernelClientHeapCut Extra) state : Assertion :=
  match cut with
  | KernelClientHeapClosed => kernel_client_heap_world abi sg state
  | KernelClientHeapTaskPublication publication => kernel_client_heap_publication abi sg publication state
  | KernelClientHeapExtra extra => extra_resources sg extra state
  end.

(** Ordered source guards for OSIntEnter; no abstract OS state or invariant
    occurs here. The selected disabled trace macro has no body. *)
Inductive kernel_client_int_enter_fragment (sg : StableGlobVars) : model -> model -> Prop :=
| KernelClientIntEnterInactive : forall heap,
    uchar_load sg.(g_OSRunning) 0 heap -> kernel_client_int_enter_fragment sg heap heap
| KernelClientIntEnterSaturated : forall heap nesting,
    uchar_load sg.(g_OSRunning) 1 heap -> uchar_load sg.(g_OSIntNesting) nesting heap ->
    255 <= nesting -> kernel_client_int_enter_fragment sg heap heap
| KernelClientIntEnterIncrement : forall before nesting after,
    uchar_load sg.(g_OSRunning) 1 before -> uchar_load sg.(g_OSIntNesting) nesting before ->
    nesting < 255 -> kernel_heap_execution [(sg.(g_OSIntNesting), nesting + 1)] before after ->
    kernel_client_int_enter_fragment sg before after.

Lemma kernel_client_int_enter_writes : forall sg state (frame : Assertion) before after,
  (UCOS2_inv sg state ** frame) before ->
  kernel_client_int_enter_fragment sg before after ->
  kernel_heap_execution (os_int_enter_heap_writes sg state) before after.
Proof.
  intros sg state frame before after [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]] Hsource.
  pose proof (uchar_load_frame _ _ _ _ _ (os_int_exit_raw_running_load sg state owned Hraw) Hjoin) as Hr.
  pose proof (uchar_load_frame _ _ _ _ _ (os_int_exit_raw_nesting_load sg state owned Hraw) Hjoin) as Hn.
  unfold os_int_enter_heap_writes.
  destruct Hsource as [heap Hread|heap nesting Hread Hnest Hsat|heap nesting final Hread Hnest Hlt Hwrite].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
    destruct state.(SchedState).(isRunning); [discriminate|]. split; [constructor|split; reflexivity].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
    pose proof (uchar_load_deterministic _ _ _ _ Hnest Hn) as ->.
    destruct state.(SchedState).(isRunning); [|discriminate].
    assert ((state.(IntrState).(intNesting) <? 255) = false) as -> by (apply Z.ltb_ge; exact Hsat).
    split; [constructor|split; reflexivity].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
    pose proof (uchar_load_deterministic _ _ _ _ Hnest Hn) as ->.
    destruct state.(SchedState).(isRunning); [|discriminate].
    assert ((state.(IntrState).(intNesting) <? 255) = true) as -> by (apply Z.ltb_lt; exact Hlt).
    exact Hwrite.
Qed.

Lemma kernel_client_int_enter_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state (frame : Assertion) before after,
  (kernel_client_heap_world abi sg state ** frame) before ->
  kernel_client_int_enter_fragment sg before after ->
  (kernel_client_heap_world abi sg (os_int_enter_state state) ** frame) after.
Proof.
  intros external platform port abi sg state frame before after Hpre Hsource.
  assert (Hsplit : kernel_client_heap_world abi sg state ** frame |-- UCOS2_inv sg state **
    (unmap_table_rep sg ** armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame)).
  { unfold kernel_client_heap_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  pose proof (kernel_client_int_enter_writes sg state _ before after (Hsplit before Hpre) Hsource) as Hwrites.
  destruct (os_int_enter_source_heap_frames_private sg state _ before (Hsplit before Hpre))
    as [produced [Hrun Hpost]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hmerge : UCOS2_inv sg (os_int_enter_state state) **
      (unmap_table_rep sg ** armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame) |--
    kernel_client_heap_world abi sg (os_int_enter_state state) ** frame).
  { unfold kernel_client_heap_world; rewrite kernel_program_inv_split_unmap.
    unfold os_int_enter_state; cbn [replace_IntrS TskState]; entailer!. }
  exact (Hmerge after Hpost).
Qed.

Lemma kernel_client_int_enter_produces_world : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state (frame : Assertion) before,
  (kernel_client_heap_world abi sg state ** frame) before ->
  exists after, kernel_client_int_enter_fragment sg before after /\
    (kernel_client_heap_world abi sg (os_int_enter_state state) ** frame) after.
Proof.
  intros external platform port abi sg state frame before Hpre.
  assert (Hsplit : kernel_client_heap_world abi sg state ** frame |-- UCOS2_inv sg state **
    (unmap_table_rep sg ** armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame)).
  { unfold kernel_client_heap_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  pose proof (Hsplit before Hpre) as Howned.
  destruct Howned as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
  pose proof (uchar_load_frame _ _ _ _ _ (os_int_exit_raw_running_load sg state owned Hraw) Hjoin) as Hr.
  pose proof (uchar_load_frame _ _ _ _ _ (os_int_exit_raw_nesting_load sg state owned Hraw) Hjoin) as Hn.
  destruct (os_int_enter_source_heap_frames_private sg state _ before (Hsplit before Hpre))
    as [after [Hrun Hafter]].
  assert (Hsource : kernel_client_int_enter_fragment sg before after).
  { unfold os_int_enter_heap_writes in Hrun.
    destruct state.(SchedState).(isRunning) eqn:Hrunning.
    - destruct (state.(IntrState).(intNesting) <? 255) eqn:Hbelow.
      + apply Z.ltb_lt in Hbelow; eapply KernelClientIntEnterIncrement; eassumption.
      + assert (Hid : kernel_heap_execution [] before before) by (split; [constructor|split; reflexivity]).
        assert (after = before) by (eapply kernel_heap_execution_deterministic; eassumption); subst after.
        apply Z.ltb_ge in Hbelow; eapply KernelClientIntEnterSaturated; eassumption.
    - assert (Hid : kernel_heap_execution [] before before) by (split; [constructor|split; reflexivity]).
      assert (after = before) by (eapply kernel_heap_execution_deterministic; eassumption); subst after.
      constructor; exact Hr. }
  exists after; split; [exact Hsource|]. eapply kernel_client_int_enter_resources; eassumption.
Qed.

Lemma kernel_client_int_exit_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state (frame : Assertion) before after,
  (kernel_client_heap_world abi sg state ** frame) before ->
  os_int_exit_masked_no_schedule_fragment sg before after ->
  (kernel_client_heap_world abi sg
    (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros external platform port abi sg state frame before after Hpre Hsource.
  assert (Hsplit : kernel_client_heap_world abi sg state ** frame |-- UCOS2_inv sg state **
    (unmap_table_rep sg ** armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame)).
  { unfold kernel_client_heap_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hsplit before Hpre) as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
  destruct (os_int_exit_masked_counter_raw_post sg state owned Hraw) as [middle [Hcounter Hraw_after]].
  destruct (os_int_exit_masked_counter_fragment_frame sg owned _ middle rest before Hcounter Hjoin)
    as [produced [Hwhole Hjoined]].
  assert (produced = after).
  { destruct Hsource; eapply os_int_exit_masked_counter_final_eq; eassumption. }
  subst produced.
  assert (Hafter : (UCOS2_inv sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
    (unmap_table_rep sg ** armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame)) after).
  { exists middle, rest; split; [exact Hjoined|]. split; [split; assumption|exact Hrest]. }
  assert (Hmerge : UCOS2_inv sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
      (unmap_table_rep sg ** armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame) |--
    kernel_client_heap_world abi sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame).
  { unfold kernel_client_heap_world; rewrite kernel_program_inv_split_unmap.
    unfold os_int_exit_counter_state; cbn [replace_IntrS TskState]; entailer!. }
  exact (Hmerge after Hafter).
Qed.

Lemma kernel_client_int_exit_produces_world : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state (frame : Assertion) before,
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  (kernel_client_heap_world abi sg state ** frame) before ->
  exists after, os_int_exit_masked_no_schedule_fragment sg before after /\
    (kernel_client_heap_world abi sg
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros external platform port abi sg state frame before Hbranch Hpre.
  assert (Hsplit : kernel_client_heap_world abi sg state ** frame |-- UCOS2_inv sg state **
    (unmap_table_rep sg ** armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame)).
  { unfold kernel_client_heap_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hsplit before Hpre) as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
  destruct (os_int_exit_masked_no_schedule_raw_post sg state owned Hraw Hbranch)
    as [middle [Hsource [Hrun Hmiddle]]].
  destruct (os_int_exit_masked_no_schedule_fragment_frame sg owned middle rest before Hsource Hjoin)
    as [after [Hwhole Hjoined]].
  exists after; split; [exact Hwhole|]. eapply kernel_client_int_exit_resources; eassumption.
Qed.

(** This identifies the supplied real endpoint with the existing producer;
    an existential heap from a proof cannot replace an actual return heap. *)
Lemma kernel_client_publication_final_eq : forall sg priority pointer before first second,
  task_tcb_init_publication_tail_fragment sg priority pointer before first ->
  task_tcb_init_publication_tail_fragment sg priority pointer before second -> first = second.
Proof.
  intros sg priority pointer before first second Hfirst Hsecond.
  destruct Hfirst as [l1 [g1 [r1 [c1 [group1 [row1 [count1 Hfirst]]]]]]].
  destruct Hsecond as [l2 [g2 [r2 [c2 [group2 [row2 [count2 Hsecond]]]]]]].
  destruct Hfirst as [Hl1 [Hg1 [Hby1 [Hwg1 [Hy1 [Hr1 [Hbx1 [Hwr1 [Hc1 [Hwc1 Hp1]]]]]]]]]].
  destruct Hsecond as [Hl2 [Hg2 [Hby2 [Hwg2 [Hy2 [Hr2 [Hbx2 [Hwr2 [Hc2 [Hwc2 Hp2]]]]]]]]]].
  assert (l1 = l2) by (eapply kernel_heap_execution_deterministic; eassumption); subst l2.
  assert (group1 = group2) by (eapply uchar_load_deterministic; eassumption); subst group2.
  assert (g1 = g2) by (eapply kernel_heap_execution_deterministic; eassumption); subst g2.
  assert (row1 = row2) by (eapply uchar_load_deterministic; eassumption); subst row2.
  assert (r1 = r2) by (eapply kernel_heap_execution_deterministic; eassumption); subst r2.
  assert (count1 = count2) by (eapply uchar_load_deterministic; eassumption); subst count2.
  assert (c1 = c2) by (eapply kernel_heap_execution_deterministic; eassumption); subst c2.
  eapply kernel_heap_execution_deterministic; eassumption.
Qed.

Lemma kernel_client_publication_produces_world : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg publication state (frame : Assertion) before,
  (kernel_client_heap_publication abi sg publication state ** frame) before ->
  exists after,
    task_tcb_init_publication_tail_fragment sg (task_create_stack_publication_args publication).(initPrio)
      (task_slot_addr sg publication.(stack_publication_slot)) before after /\
    kernel_client_step (task_create_stack_publication_client publication) sg state
      (task_create_stack_publication_state sg publication state) /\
    (kernel_client_heap_world abi sg (task_create_stack_publication_state sg publication state) ** frame) after.
Proof.
  intros external platform port abi sg publication state frame before Hpre.
  assert (Hsplit : kernel_client_heap_publication abi sg publication state ** frame |--
    coq_prop (UCOS2_state_inv sg state /\ task_create_stack_publication_input sg publication state /\
      0 <= (task_create_stack_publication_args publication).(initPrio) < 64 /\
      0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296) &&
    (task_tcb_init_publication_tail_storage sg (task_create_stack_publication_args publication)
       state publication.(stack_publication_slot) publication.(stack_publication_image) **
     (task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
      armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame))).
  { unfold kernel_client_heap_publication; entailer!. }
  destruct (Hsplit before Hpre) as [[Hvalid [Hinput [Hpriority Hpointer]]] Hheap].
  pose proof (proj1 (proj2 (proj2 Hinput))) as Hbinding.
  destruct (task_tcb_init_publication_tail_store_execution sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_origin)
    publication.(stack_publication_acquired) state publication.(stack_publication_slot)
    publication.(stack_publication_image) _ before Hvalid Hbinding Hpriority Hpointer Hheap)
    as [after [Hsource Hafter]].
  pose proof (task_create_stack_publication_source_post external platform port abi sg publication state Hvalid Hinput)
    as Hclose; cbv zeta in Hclose.
  assert (Hmerge : task_create_publication_storage sg (task_create_stack_publication_args publication)
      publication.(stack_publication_invocation) publication.(stack_publication_acquired)
      state publication.(stack_publication_slot) publication.(stack_publication_image) **
      (task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
       armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame) |--
    kernel_client_heap_world abi sg (task_create_stack_publication_state sg publication state) ** frame).
  { unfold task_create_stack_publication_resources in Hclose.
    unfold kernel_client_heap_world; rewrite kernel_program_inv_split_unmap.
    sepcon_assoc_change; sep_apply_l_atomic Hclose; Intros; entailer!. }
  exists after; split; [exact Hsource|]. split; [split; [exact Hinput|reflexivity]|exact (Hmerge after Hafter)].
Qed.

Lemma kernel_client_publication_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg publication state (frame : Assertion) before after,
  (kernel_client_heap_publication abi sg publication state ** frame) before ->
  task_tcb_init_publication_tail_fragment sg (task_create_stack_publication_args publication).(initPrio)
    (task_slot_addr sg publication.(stack_publication_slot)) before after ->
  kernel_client_step (task_create_stack_publication_client publication) sg state
    (task_create_stack_publication_state sg publication state) /\
  (kernel_client_heap_world abi sg (task_create_stack_publication_state sg publication state) ** frame) after.
Proof.
  intros external platform port abi sg publication state frame before after Hpre Hsource.
  destruct (kernel_client_publication_produces_world external platform port abi sg publication state frame before Hpre)
    as [produced [Hrun [Hstep Hpost]]].
  assert (produced = after) by (eapply kernel_client_publication_final_eq; eassumption); subst produced.
  split; assumption.
Qed.

(** An extensible SOURCE registry. Extra transitions may enter and leave
    any cut; the type does not ban other clients, task switches or nesting.
    Each extension needs its own proved same-heap resource transport below.
    In particular it cannot be registered by a pure KernelClientCertificate. *)
Inductive kernel_client_heap_step {Extra}
  (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model -> KernelClientHeapCut Extra -> model -> Prop)
  (sg : StableGlobVars) : KernelClientHeapCut Extra -> model -> KernelClientHeapCut Extra -> model -> Prop :=
| KernelClientHeapEnter : forall before after,
    kernel_client_int_enter_fragment sg before after ->
    kernel_client_heap_step extra_step sg KernelClientHeapClosed before KernelClientHeapClosed after
| KernelClientHeapExit : forall before after,
    os_int_exit_masked_no_schedule_fragment sg before after ->
    kernel_client_heap_step extra_step sg KernelClientHeapClosed before KernelClientHeapClosed after
| KernelClientHeapPublish : forall publication before after,
    task_tcb_init_publication_tail_fragment sg (task_create_stack_publication_args publication).(initPrio)
      (task_slot_addr sg publication.(stack_publication_slot)) before after ->
    kernel_client_heap_step extra_step sg (KernelClientHeapTaskPublication publication) before KernelClientHeapClosed after
| KernelClientHeapRegistered : forall cut before next after,
    extra_step sg cut before next after -> kernel_client_heap_step extra_step sg cut before next after.

(** This logical projection is produced by the heap proof, not supplied by
    the handler contract. It retains the real operation needed by protocol
    clients; validity alone does not characterize owner-use or lifecycle. *)
Inductive kernel_client_heap_state_step {Extra}
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) (sg : StableGlobVars) :
  KernelClientHeapCut Extra -> UCOS2_Verify_State -> KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop :=
| KernelClientHeapEnterState : forall state,
    kernel_client_heap_state_step extra_effect sg KernelClientHeapClosed state
      KernelClientHeapClosed (os_int_enter_state state)
| KernelClientHeapExitState : forall state,
    kernel_client_heap_state_step extra_effect sg KernelClientHeapClosed state
      KernelClientHeapClosed (os_int_exit_counter_state state.(SchedState).(isRunning) state)
| KernelClientHeapPublishState : forall publication state,
    task_create_stack_publication_input sg publication state ->
    kernel_client_heap_state_step extra_effect sg (KernelClientHeapTaskPublication publication) state
      KernelClientHeapClosed (task_create_stack_publication_state sg publication state)
| KernelClientHeapExtraState : forall cut state next returned,
    extra_effect sg cut state next returned ->
    kernel_client_heap_state_step extra_effect sg cut state next returned.

Definition kernel_client_heap_extension_valid {external platform port Extra}
  (abi : Armv7aContinuationABI external platform port) extra_resources
  (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model -> KernelClientHeapCut Extra -> model -> Prop)
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) : Prop :=
  forall sg (cut : KernelClientHeapCut Extra) before next after state (frame : Assertion),
    extra_step sg cut before next after ->
    (kernel_client_heap_resources abi extra_resources sg cut state ** frame) before ->
    exists returned, extra_effect sg cut state next returned /\
      (kernel_client_heap_resources abi extra_resources sg next returned ** frame) after.

Lemma kernel_client_heap_step_resources : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources extra_step extra_effect,
  @kernel_client_heap_extension_valid external platform port Extra abi extra_resources extra_step extra_effect ->
  forall sg cut before next after state (frame : Assertion),
  kernel_client_heap_step extra_step sg cut before next after ->
  (kernel_client_heap_resources abi extra_resources sg cut state ** frame) before ->
  exists returned, kernel_client_heap_state_step extra_effect sg cut state next returned /\
    (kernel_client_heap_resources abi extra_resources sg next returned ** frame) after.
Proof.
  intros external platform port Extra abi extra_resources extra_step extra_effect Hextra
    sg cut before next after state frame Hsource Hpre; destruct Hsource.
  - exists (os_int_enter_state state); split; [constructor|].
    eapply kernel_client_int_enter_resources; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state).
    split; [constructor|].
    eapply kernel_client_int_exit_resources; eassumption.
  - exists (task_create_stack_publication_state sg publication state).
    destruct (kernel_client_publication_resources external platform port abi sg publication state frame
      before after Hpre H) as [[Hinput Hstate] Hpost].
    split; [constructor; exact Hinput|exact Hpost].
  - destruct (Hextra sg cut before next after state frame H Hpre) as [returned [Heffect Hpost]].
    exists returned; split; [constructor; exact Heffect|exact Hpost].
Qed.

Inductive kernel_client_heap_trace {Extra} extra_step sg :
  KernelClientHeapCut Extra -> model -> KernelClientHeapCut Extra -> model -> Prop :=
| KernelClientHeapTraceNil : forall cut heap, kernel_client_heap_trace extra_step sg cut heap cut heap
| KernelClientHeapTraceCons : forall cut before middle_cut middle final_cut after,
    kernel_client_heap_step extra_step sg cut before middle_cut middle ->
    kernel_client_heap_trace extra_step sg middle_cut middle final_cut after ->
    kernel_client_heap_trace extra_step sg cut before final_cut after.

Inductive kernel_client_heap_state_trace {Extra} extra_effect sg :
  KernelClientHeapCut Extra -> UCOS2_Verify_State -> KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop :=
| KernelClientHeapStateTraceNil : forall cut state,
    kernel_client_heap_state_trace extra_effect sg cut state cut state
| KernelClientHeapStateTraceCons : forall cut state middle_cut middle final_cut returned,
    kernel_client_heap_state_step extra_effect sg cut state middle_cut middle ->
    kernel_client_heap_state_trace extra_effect sg middle_cut middle final_cut returned ->
    kernel_client_heap_state_trace extra_effect sg cut state final_cut returned.

Lemma kernel_client_heap_trace_resources : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources extra_step extra_effect,
  @kernel_client_heap_extension_valid external platform port Extra abi extra_resources extra_step extra_effect ->
  forall sg cut before next after (frame : Assertion),
  kernel_client_heap_trace extra_step sg cut before next after -> forall state,
  (kernel_client_heap_resources abi extra_resources sg cut state ** frame) before ->
  exists returned, kernel_client_heap_state_trace extra_effect sg cut state next returned /\
    (kernel_client_heap_resources abi extra_resources sg next returned ** frame) after.
Proof.
  intros external platform port Extra abi extra_resources extra_step extra_effect Hextra
    sg cut before next after frame Htrace; induction Htrace; intros state Hpre.
  - exists state; split; [constructor|exact Hpre].
  - destruct (kernel_client_heap_step_resources external platform port Extra abi extra_resources extra_step extra_effect
      Hextra sg cut before middle_cut middle state frame H Hpre) as [middle_state [Hstep Hmiddle]].
    destruct (IHHtrace middle_state Hmiddle) as [returned [Htail Hpost]].
    exists returned; split; [econstructor; eassumption|exact Hpost].
Qed.

(** The cursor belongs to the actual caller/handler source relation. A
    segment is a completed source FRAGMENT, not automatically a complete
    public kernel call. Matching BL/return, nesting and normal-return
    classification remain properties of the supplied cursor execution.
    Local steps keep their real private heap effects; they are not no-ops. *)
Inductive kernel_client_handler_trace {Cursor Extra}
  (local_step : Cursor -> model -> Cursor -> model -> Prop)
  (segment : StableGlobVars -> Cursor -> KernelClientHeapCut Extra -> model ->
    Cursor -> KernelClientHeapCut Extra -> model -> Prop) (sg : StableGlobVars) :
  Cursor -> KernelClientHeapCut Extra -> model -> Cursor -> KernelClientHeapCut Extra -> model -> Prop :=
| KernelClientHandlerReturn : forall cursor cut heap,
    kernel_client_handler_trace local_step segment sg cursor cut heap cursor cut heap
| KernelClientHandlerLocal : forall cursor cut before middle_cursor middle returned_cursor final_cut after,
    local_step cursor before middle_cursor middle ->
    kernel_client_handler_trace local_step segment sg middle_cursor cut middle returned_cursor final_cut after ->
    kernel_client_handler_trace local_step segment sg cursor cut before returned_cursor final_cut after
| KernelClientHandlerSegment : forall cursor cut before middle_cursor middle_cut middle returned_cursor final_cut after,
    segment sg cursor cut before middle_cursor middle_cut middle ->
    kernel_client_handler_trace local_step segment sg middle_cursor middle_cut middle returned_cursor final_cut after ->
    kernel_client_handler_trace local_step segment sg cursor cut before returned_cursor final_cut after.

(** Only source classification and the existing private-frame rule are
    external inputs. The OS/table/map post is derived from concrete client
    proofs. Changing CPU/stack owners must live in an appropriate registered
    cut; they cannot be smuggled through [frame] on a switching step. *)
Lemma kernel_client_handler_trace_resources : forall external platform port Cursor Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources extra_step extra_effect
  (private : Cursor -> Assertion) local_step segment,
  @kernel_client_heap_extension_valid external platform port Extra abi extra_resources extra_step extra_effect ->
  (forall sg cursor cut before returned_cursor next after,
    segment sg cursor cut before returned_cursor next after ->
    kernel_client_heap_step extra_step sg cut before next after) ->
  (forall sg cursor cut before returned_cursor next after,
    segment sg cursor cut before returned_cursor next after -> private cursor = private returned_cursor) ->
  (forall cursor before returned_cursor after (frame : Assertion),
    local_step cursor before returned_cursor after ->
    (private cursor ** frame) before -> (private returned_cursor ** frame) after) ->
  forall sg cursor cut before returned_cursor next after (frame : Assertion),
  kernel_client_handler_trace local_step segment sg cursor cut before returned_cursor next after ->
  forall state,
  (kernel_client_heap_resources abi extra_resources sg cut state ** private cursor ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace extra_effect sg cut state next returned /\
    (kernel_client_heap_resources abi extra_resources sg next returned ** private returned_cursor ** frame) after.
Proof.
  intros external platform port Cursor Extra abi extra_resources extra_step extra_effect private
    local_step segment Hextra Hsegment Hprivate Hlocal sg cursor cut before returned_cursor next after frame Hrun.
  induction Hrun; intros state Hpre.
  - exists state; split; [constructor|exact Hpre].
  - assert (Horder : kernel_client_heap_resources abi extra_resources sg cut state ** private cursor ** frame |--
      private cursor ** (kernel_client_heap_resources abi extra_resources sg cut state ** frame)) by entailer!.
    pose proof (Hlocal _ _ _ _ _ H (Horder before Hpre)) as Hmiddle.
    assert (Hback : private middle_cursor ** (kernel_client_heap_resources abi extra_resources sg cut state ** frame) |--
      kernel_client_heap_resources abi extra_resources sg cut state ** private middle_cursor ** frame) by entailer!.
    exact (IHHrun state (Hback middle Hmiddle)).
  - assert (Horder : kernel_client_heap_resources abi extra_resources sg cut state ** private cursor ** frame |--
      kernel_client_heap_resources abi extra_resources sg cut state ** (private cursor ** frame)) by entailer!.
    destruct (kernel_client_heap_step_resources external platform port Extra abi extra_resources extra_step extra_effect
      Hextra sg cut before middle_cut middle state (private cursor ** frame)
      (Hsegment sg cursor cut before middle_cursor middle_cut middle H) (Horder before Hpre))
      as [middle_state [Heffect Hmiddle]].
    rewrite (Hprivate sg cursor cut before middle_cursor middle_cut middle H) in Hmiddle.
    assert (Hback : kernel_client_heap_resources abi extra_resources sg middle_cut middle_state **
        (private middle_cursor ** frame) |--
      kernel_client_heap_resources abi extra_resources sg middle_cut middle_state ** private middle_cursor ** frame)
      by entailer!.
    destruct (IHHrun middle_state (Hback middle Hmiddle)) as [returned [Htail Hpost]].
    exists returned; split; [econstructor; eassumption|exact Hpost].
Qed.
