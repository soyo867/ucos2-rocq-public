Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Ucos2Verify.lib.ucos2_spatial Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.event_registration.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_continuation_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.lib.interrupt.
Import UCOS2_C_Rules KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source/os_core.c:708-710. OS_SchedNew has completed its real byte
    store before the caller re-reads OSPrioHighRdy, reads that exact priority
    table slot, and writes OSTCBHighRdy. Free/reserved table encodings are
    retained here; a live selected task is a separately proved consequence.
    Both enabled profiles share these operations, before profiling's guard. *)
Definition os_int_exit_selection_heap_fragment (sg : StableGlobVars)
  (before after : model) : Prop :=
  exists middle priority pointer,
    sched_new_heap_fragment sg before middle /\
    uchar_load sg.(g_OSPrioHighRdy) priority middle /\
    pointer_load (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) pointer middle /\
    kernel_heap_execution (pointer_store_writes sg.(g_OSTCBHighRdy) pointer) middle after.

(** A physical intermediate stage, NOT a full invariant indexed by a
    fictional already-updated state. The ready tables and every non-cache
    cell stay at their actual input bytes while the two cache stores occur. *)
Definition os_int_exit_selection_rep (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (high pointer : Z) : Assertion :=
  sched_new_rep sg (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) high **
  sg.(g_OSTCBHighRdy) # Ptr |-> pointer **
  sched_physical_without_high sg state.(SchedState) **
  UCOS2_raw_rep_missing_sched sg state.

Lemma os_int_exit_selection_rep_entry : forall sg state,
  UCOS2_raw_rep sg state ** unmap_table_rep sg --||--
  os_int_exit_selection_rep sg state
    (sched_priority_byte state.(SchedState).(highRdyPrio))
    (encode_task_link sg state.(SchedState).(highRdyTid)).
Proof.
  intros; rewrite (UCOS2_raw_rep_split_module sg state SchedModule).
  cbn [UCOS2_module_rep].
  unfold os_int_exit_selection_rep, sched_new_rep, sched_raw_rep,
    sched_physical_rep, sched_physical_without_high.
  rewrite sched_rows_array_equiv; split; entailer!.
Qed.

Lemma os_int_exit_selection_rep_high_load : forall sg state high pointer heap,
  os_int_exit_selection_rep sg state high pointer heap ->
  uchar_load sg.(g_OSPrioHighRdy) high heap.
Proof.
  intros sg state high pointer heap Hrep.
  assert (Hfocus : os_int_exit_selection_rep sg state high pointer |--
    sg.(g_OSPrioHighRdy) # UChar |-> high ** TT).
  { unfold os_int_exit_selection_rep, sched_new_rep; entailer!; intros ? ?; exact I. }
  eapply framed_uchar_store_load; exact (Hfocus heap Hrep).
Qed.

Lemma os_int_exit_selection_rep_current_load : forall sg state high pointer heap,
  os_int_exit_selection_rep sg state high pointer heap ->
  uchar_load sg.(g_OSPrioCur) (sched_priority_byte state.(SchedState).(curSchedPrio)) heap.
Proof.
  intros sg state high pointer heap Hrep.
  assert (Hfocus : os_int_exit_selection_rep sg state high pointer |--
    sg.(g_OSPrioCur) # UChar |-> sched_priority_byte state.(SchedState).(curSchedPrio) ** TT).
  { unfold os_int_exit_selection_rep, sched_physical_without_high; entailer!; intros ? ?; exact I. }
  eapply framed_uchar_store_load; exact (Hfocus heap Hrep).
Qed.

Lemma os_int_exit_selection_rep_table_load : forall sg state high pointer heap,
  os_int_exit_selection_rep sg state high pointer heap ->
  pointer_load
    (sg.(g_OSTCBPrioTbl) + sched_selected_priority state.(TskState) state.(SchedState) * sizeof(PTR))
    (sched_selected_pointer sg state.(TskState) state.(SchedState)) heap.
Proof.
  intros sg state high pointer heap Hrep.
  assert (Hfocus : os_int_exit_selection_rep sg state high pointer |--
    (sg.(g_OSTCBPrioTbl) + sched_selected_priority state.(TskState) state.(SchedState) * sizeof(PTR))
      # Ptr |-> sched_selected_pointer sg state.(TskState) state.(SchedState) ** TT).
  { unfold os_int_exit_selection_rep, UCOS2_raw_rep_missing_sched,
      UCOS2_raw_rep_missing_module, UCOS2_selected_rep;
      cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep].
    unfold task_shared_rep, task_public_storage.
    sep_apply_l_atomic (store_prio_tbl_split_selection sg state.(TskState) state.(SchedState)).
    entailer!; intros ? ?; exact I. }
  eapply framed_pointer_store_load; exact (Hfocus heap Hrep).
Qed.

Lemma os_int_exit_selection_heap_fragment_deterministic : forall sg before first second,
  os_int_exit_selection_heap_fragment sg before first ->
  os_int_exit_selection_heap_fragment sg before second -> first = second.
Proof.
  intros sg before first second [middle [priority [pointer [Hnew [Hp [Hptr Hrun]]]]]]
    [middle' [priority' [pointer' [Hnew' [Hp' [Hptr' Hrun']]]]]].
  assert (middle = middle') by (eapply sched_new_heap_fragment_deterministic; eassumption); subst middle'.
  assert (priority = priority') by (eapply uchar_load_deterministic; eassumption); subst priority'.
  assert (pointer = pointer') by (eapply pointer_load_deterministic; eassumption); subst pointer'.
  eapply kernel_heap_execution_deterministic; eassumption.
Qed.

Lemma os_int_exit_selection_heap_fragment_frame : forall sg before after frame whole,
  os_int_exit_selection_heap_fragment sg before after -> join before frame whole ->
  exists final, os_int_exit_selection_heap_fragment sg whole final /\ join after frame final.
Proof.
  intros sg before after frame whole [middle [priority [pointer [Hnew [Hp [Hptr Hrun]]]]]] Hjoin.
  destruct (sched_new_heap_fragment_frame sg before middle frame whole Hnew Hjoin)
    as [mid [Hmid Hjoinmid]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoinmid) as [final [Hfinal Hjoinfinal]].
  exists final; split; [|exact Hjoinfinal].
  exists mid, priority, pointer; split; [exact Hmid|].
  split; [eapply uchar_load_frame; eassumption|].
  split; [eapply pointer_load_frame; eassumption|exact Hfinal].
Qed.

Lemma os_int_exit_selection_heap_rep_post : forall sg state high pointer heap,
  os_int_exit_selection_rep sg state high pointer heap ->
  exists final, os_int_exit_selection_heap_fragment sg heap final /\
    os_int_exit_selection_rep sg state
      (sched_selected_priority state.(TskState) state.(SchedState))
      (sched_selected_pointer sg state.(TskState) state.(SchedState)) final.
Proof.
  intros sg state high pointer heap Hrep.
  assert (Hsplit : os_int_exit_selection_rep sg state high pointer |--
    sched_new_rep sg (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
      (sched_row_values state.(TskState) state.(SchedState).(readyList)) high **
    (sg.(g_OSTCBHighRdy) # Ptr |-> pointer **
     sched_physical_without_high sg state.(SchedState) ** UCOS2_raw_rep_missing_sched sg state)).
  { unfold os_int_exit_selection_rep; entailer!. }
  destruct (sched_new_heap_fragment_frame_post _ _ _ _ _ heap (Hsplit heap Hrep))
    as [middle [Hnew Hmiddle]].
  rewrite sched_new_priority_eq_selected in Hmiddle.
  assert (Hmid : os_int_exit_selection_rep sg state
    (sched_selected_priority state.(TskState) state.(SchedState)) pointer middle).
  { assert (Hmerge : sched_new_rep sg (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
      (sched_row_values state.(TskState) state.(SchedState).(readyList))
      (sched_selected_priority state.(TskState) state.(SchedState)) **
      (sg.(g_OSTCBHighRdy) # Ptr |-> pointer ** sched_physical_without_high sg state.(SchedState) **
        UCOS2_raw_rep_missing_sched sg state) |--
      os_int_exit_selection_rep sg state (sched_selected_priority state.(TskState) state.(SchedState)) pointer).
    { unfold os_int_exit_selection_rep; entailer!. }
    exact (Hmerge middle Hmiddle). }
  pose proof (os_int_exit_selection_rep_high_load _ _ _ _ _ Hmid) as Hp.
  pose proof (os_int_exit_selection_rep_table_load _ _ _ _ _ Hmid) as Hptr.
  assert (Hwrite : os_int_exit_selection_rep sg state
      (sched_selected_priority state.(TskState) state.(SchedState)) pointer |--
    sg.(g_OSTCBHighRdy) # Ptr |->_ **
    (sched_new_rep sg (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
      (sched_row_values state.(TskState) state.(SchedState).(readyList))
      (sched_selected_priority state.(TskState) state.(SchedState)) **
     sched_physical_without_high sg state.(SchedState) ** UCOS2_raw_rep_missing_sched sg state)).
  { unfold os_int_exit_selection_rep; sep_apply_l_atomic (store_ptr_undef_store_ptr sg.(g_OSTCBHighRdy) pointer).
    entailer!. }
  destruct (framed_pointer_store_execution _ _ _ middle (proj1 Hptr) (Hwrite middle Hmid))
    as [final [Hrun Hpost]].
  exists final; split.
  - exists middle, (sched_selected_priority state.(TskState) state.(SchedState)),
      (sched_selected_pointer sg state.(TskState) state.(SchedState)).
    split; [exact Hnew|]. split; [exact Hp|]. split; [exact Hptr|exact Hrun].
  - assert (Hmerge : sg.(g_OSTCBHighRdy) # Ptr |-> sched_selected_pointer sg state.(TskState) state.(SchedState) **
      (sched_new_rep sg (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
        (sched_row_values state.(TskState) state.(SchedState).(readyList))
        (sched_selected_priority state.(TskState) state.(SchedState)) **
       sched_physical_without_high sg state.(SchedState) ** UCOS2_raw_rep_missing_sched sg state) |--
      os_int_exit_selection_rep sg state
        (sched_selected_priority state.(TskState) state.(SchedState))
        (sched_selected_pointer sg state.(TskState) state.(SchedState))).
    { unfold os_int_exit_selection_rep; entailer!. }
    exact (Hmerge final Hpost).
Qed.

Lemma os_int_exit_selection_heap_rep_preservation : forall sg state high pointer before after,
  os_int_exit_selection_rep sg state high pointer before ->
  os_int_exit_selection_heap_fragment sg before after ->
  os_int_exit_selection_rep sg state
    (sched_selected_priority state.(TskState) state.(SchedState))
    (sched_selected_pointer sg state.(TskState) state.(SchedState)) after.
Proof.
  intros sg state high pointer before after Hrep Hsource.
  destruct (os_int_exit_selection_heap_rep_post _ _ _ _ _ Hrep) as [final [Hrun Hpost]].
  replace after with final by (eapply os_int_exit_selection_heap_fragment_deterministic; eassumption).
  exact Hpost.
Qed.

Definition os_int_exit_selection_state (state : UCOS2_Verify_State) :=
  replace_SchedS (sched_refresh_high state.(TskState) state.(SchedState)) state.

(** The selector depends on the owned bitmap and the live, priority-sorted
    ready list. A Multi-woken task may retain pending bits; neither selection
    nor these cache stores tests or clears them. *)
Lemma sched_selected_priority_eq_head_from_structure : forall sg tasks s head tail t,
  valid_stable_glob_vars sg ->
  sched_ready_structure sg tasks s ->
  s.(readyList) = head :: tail ->
  tasks.(inUsedTaskStates) head = Some t ->
  sched_selected_priority tasks s = t.(curPrio).
Proof.
  intros sg tasks s head tail t Hsg [Hmembers [Hsorted Hrest]] Hready Hhead.
  unfold sched_selected_priority; rewrite Hready.
  assert (Hlowest : sg.(osLowestPrio) = 63).
  { unfold valid_stable_glob_vars in Hsg; tauto. }
  assert (Hrange : forall tid other, In tid (head :: tail) ->
    tasks.(inUsedTaskStates) tid = Some other -> 0 <= other.(curPrio) < 64).
  { intros tid other Hin Hget.
    assert (Hin' : In tid s.(readyList)) by (rewrite Hready; exact Hin).
    destruct (Hmembers tid Hin') as [found [Hfound Hprio]].
    rewrite Hget in Hfound; inversion Hfound; subst found.
    unfold task_priority_in_range in Hprio; lia. }
  apply sched_unmap_minimum_priority; [exact Hhead| | |].
  - eapply Hrange; [left; reflexivity|exact Hhead].
  - intros; eapply (proj1 (Hrange _ _ H H0)).
  - intros tid other Hin Hget.
    rewrite Hready in Hsorted.
    pose proof (sched_sorted_head_le TaskID
      (fun id => match tasks.(inUsedTaskStates) id with
        | Some node => node.(curPrio) | None => sg.(osLowestPrio) + 1 end)
      head tail tid Hsorted Hin) as Hle.
    cbn beta in Hle. rewrite Hhead, Hget in Hle; exact Hle.
Qed.

Lemma sched_selected_pointer_eq_head_from_structure : forall sg tasks s head tail t,
  valid_stable_glob_vars sg ->
  sched_ready_structure sg tasks s ->
  task_current_prio_registered tasks ->
  s.(readyList) = head :: tail ->
  tasks.(inUsedTaskStates) head = Some t ->
  sched_selected_pointer sg tasks s = task_slot_addr sg head.
Proof.
  intros sg tasks s head tail t Hsg Hready Hregistered Hlist Hhead.
  unfold sched_selected_pointer.
  rewrite (sched_selected_priority_eq_head_from_structure sg tasks s head tail t Hsg Hready Hlist Hhead).
  rewrite (Hregistered head t Hhead); reflexivity.
Qed.

Lemma sched_selection_written_head_eq_from_structure : forall sg tasks s head tail t,
  valid_stable_glob_vars sg -> sched_ready_structure sg tasks s ->
  task_current_prio_registered tasks -> s.(readyList) = head :: tail ->
  tasks.(inUsedTaskStates) head = Some t ->
  sched_selection_written_rep sg tasks s --||--
    sched_physical_rep sg (sched_refresh_high tasks s).
Proof.
  intros sg tasks s head tail t Hsg Hrdy Hregistered Hlist Hhead.
  unfold sched_selection_written_rep, sched_cache_cells,
    sched_physical_without_high, sched_physical_rep,
    sched_refresh_high; simpl.
  rewrite (sched_selected_priority_eq_head_from_structure sg tasks s head tail t Hsg Hrdy Hlist Hhead).
  rewrite (sched_selected_pointer_eq_head_from_structure sg tasks s head tail t Hsg Hrdy Hregistered Hlist Hhead).
  rewrite Hlist; simpl; rewrite Hhead; simpl; split; entailer!.
Qed.

(** This consequence needs a nonempty, live, priority-sorted ready list;
    it is not inserted as a guard into either fragment above. Empty/raw
    cases still have the exact physical endpoint proved above. *)
Lemma os_int_exit_selection_rep_merge_with_ready_structure : forall sg state,
  valid_stable_glob_vars sg -> sched_ready_structure sg state.(TskState) state.(SchedState) ->
  task_current_prio_registered state.(TskState) -> state.(SchedState).(readyList) <> [] ->
  os_int_exit_selection_rep sg state
    (sched_selected_priority state.(TskState) state.(SchedState))
    (sched_selected_pointer sg state.(TskState) state.(SchedState)) |--
  UCOS2_raw_rep sg (os_int_exit_selection_state state) ** unmap_table_rep sg.
Proof.
  intros sg state Hsg Hready Hregistered Hnonempty.
  destruct state.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
  destruct (proj1 Hready head ltac:(rewrite Hlist; left; reflexivity)) as [node [Hnode Hrest]].
  pose proof (proj1 (sched_selection_written_head_eq_from_structure sg state.(TskState) state.(SchedState)
    head tail node Hsg Hready Hregistered Hlist Hnode)) as Hphysical.
  rewrite (UCOS2_raw_rep_split_module sg (os_int_exit_selection_state state) SchedModule).
  cbn [UCOS2_module_rep].
  change (os_int_exit_selection_rep sg state
    (sched_selected_priority state.(TskState) state.(SchedState))
    (sched_selected_pointer sg state.(TskState) state.(SchedState)) |--
    (sched_raw_rep sg state.(TskState) (sched_refresh_high state.(TskState) state.(SchedState)) **
      UCOS2_raw_rep_missing_sched sg state) ** unmap_table_rep sg).
  eapply derivable1_trans with (y :=
    sched_selection_written_rep sg state.(TskState) state.(SchedState) **
    (sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
     UCOS2_raw_rep_missing_sched sg state ** unmap_table_rep sg)).
  - unfold os_int_exit_selection_rep, sched_new_rep, sched_selection_written_rep, sched_cache_cells.
    rewrite sched_rows_array_equiv; entailer!.
  - sep_apply_l_atomic Hphysical.
    unfold sched_raw_rep.
    assert (Hreadyframe : (sched_refresh_high state.(TskState) state.(SchedState)).(readyList) =
      state.(SchedState).(readyList)) by reflexivity.
    rewrite Hreadyframe; entailer!.
Qed.

Lemma os_int_exit_selection_rep_merge : forall sg state,
  valid_stable_glob_vars sg -> sched_ready_in_range sg state.(TskState) state.(SchedState) ->
  task_current_prio_registered state.(TskState) -> state.(SchedState).(readyList) <> [] ->
  os_int_exit_selection_rep sg state
    (sched_selected_priority state.(TskState) state.(SchedState))
    (sched_selected_pointer sg state.(TskState) state.(SchedState)) |--
  UCOS2_raw_rep sg (os_int_exit_selection_state state) ** unmap_table_rep sg.
Proof.
  intros; eapply os_int_exit_selection_rep_merge_with_ready_structure;
    try eassumption; eapply sched_ready_in_range_implies_structure; eassumption.
Qed.

Lemma os_int_exit_selection_state_preserves_validity : forall sg state,
  UCOS2_state_inv sg state -> UCOS2_state_inv sg (os_int_exit_selection_state state).
Proof.
  intros sg state Hvalid; apply UCOS2_replace_sched_preserves_validity; [exact Hvalid| |reflexivity].
  apply sched_refresh_high_preserves_in_range;
    [exact (proj1 (proj1 (proj2 Hvalid)))|exact (proj1 (proj2 (proj2 Hvalid)))].
Qed.

Lemma os_int_exit_selection_state_preserves_full_validity : forall sg state,
  UCOS2_full_state_inv sg state -> UCOS2_full_state_inv sg (os_int_exit_selection_state state).
Proof.
  intros sg state [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle Hrest]]]]]].
  split; [exact Hprofile|]; split; [exact Htasks|]; split.
  - apply sched_refresh_high_preserves_registered_in_range; [exact (proj1 Htasks)|exact Hsched].
  - split; [exact Hevents|]; split.
    + apply cross_module_registration_sched_frame; [reflexivity|exact Hcross].
    + split; [exact Hidle|exact Hrest].
Qed.

Lemma os_int_exit_selection_raw_frame_post_with_ready_structure : forall sg state (frame : Assertion) heap,
  valid_stable_glob_vars sg -> sched_ready_structure sg state.(TskState) state.(SchedState) ->
  task_current_prio_registered state.(TskState) -> state.(SchedState).(readyList) <> [] ->
  (UCOS2_raw_rep sg state ** unmap_table_rep sg ** frame) heap ->
  exists final, os_int_exit_selection_heap_fragment sg heap final /\
    uchar_load sg.(g_OSPrioHighRdy) (sched_selected_priority state.(TskState) state.(SchedState)) final /\
    uchar_load sg.(g_OSPrioCur) (sched_priority_byte state.(SchedState).(curSchedPrio)) final /\
    (UCOS2_raw_rep sg (os_int_exit_selection_state state) ** unmap_table_rep sg ** frame) final.
Proof.
  intros sg state frame heap Hsg Hready Hregistered Hnonempty
    [owned [rest [Hjoin [Hrep Hframe]]]].
  destruct (os_int_exit_selection_heap_rep_post _ _ _ _ _
    (proj1 (os_int_exit_selection_rep_entry sg state) owned Hrep)) as [after [Hsource Hpost]].
  destruct (os_int_exit_selection_heap_fragment_frame sg owned after rest heap Hsource Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  split; [eapply uchar_load_frame; [eapply os_int_exit_selection_rep_high_load; exact Hpost|exact Hfinal]|].
  split; [eapply uchar_load_frame; [eapply os_int_exit_selection_rep_current_load; exact Hpost|exact Hfinal]|].
  exists after, rest; split; [exact Hfinal|]. split; [|exact Hframe].
  eapply os_int_exit_selection_rep_merge_with_ready_structure; eassumption.
Qed.

Lemma os_int_exit_selection_raw_frame_post : forall sg state (frame : Assertion) heap,
  valid_stable_glob_vars sg -> sched_ready_in_range sg state.(TskState) state.(SchedState) ->
  task_current_prio_registered state.(TskState) -> state.(SchedState).(readyList) <> [] ->
  (UCOS2_raw_rep sg state ** unmap_table_rep sg ** frame) heap ->
  exists final, os_int_exit_selection_heap_fragment sg heap final /\
    uchar_load sg.(g_OSPrioHighRdy) (sched_selected_priority state.(TskState) state.(SchedState)) final /\
    uchar_load sg.(g_OSPrioCur) (sched_priority_byte state.(SchedState).(curSchedPrio)) final /\
    (UCOS2_raw_rep sg (os_int_exit_selection_state state) ** unmap_table_rep sg ** frame) final.
Proof.
  intros; eapply os_int_exit_selection_raw_frame_post_with_ready_structure;
    try eassumption; eapply sched_ready_in_range_implies_structure; eassumption.
Qed.

(** The normal first-level branch DOES run the selector even when no
    context switch follows. Its final byte comparison is on the new heap,
    after BOTH cache stores, not on the old logical high-ready cache. *)
Inductive os_int_exit_masked_same_priority_fragment (sg : StableGlobVars)
  : model -> model -> Prop :=
| OsIntExitMaskedSamePriority : forall before counted after priority,
    os_int_exit_masked_counter_fragment sg before true counted ->
    uchar_load sg.(g_OSIntNesting) 0 counted ->
    uchar_load sg.(g_OSLockNesting) 0 counted ->
    os_int_exit_selection_heap_fragment sg counted after ->
    uchar_load sg.(g_OSPrioHighRdy) priority after ->
    uchar_load sg.(g_OSPrioCur) priority after ->
    os_int_exit_masked_same_priority_fragment sg before after.

Lemma os_int_exit_masked_active_counter_deterministic : forall sg before first second,
  os_int_exit_masked_counter_fragment sg before true first ->
  os_int_exit_masked_counter_fragment sg before true second -> first = second.
Proof.
  intros sg before first second Hfirst Hsecond.
  inversion Hfirst as [|initial nesting final Hrun Hnest Hwrites]; subst.
  inversion Hsecond as [|initial nesting' final Hrun' Hnest' Hwrites']; subst.
  assert (nesting = nesting') by (eapply uchar_load_deterministic; eassumption); subst nesting'.
  eapply kernel_heap_execution_deterministic; eassumption.
Qed.

Lemma os_int_exit_masked_same_priority_deterministic : forall sg before first second,
  os_int_exit_masked_same_priority_fragment sg before first ->
  os_int_exit_masked_same_priority_fragment sg before second -> first = second.
Proof.
  intros sg before first second Hfirst Hsecond.
  inversion Hfirst as [initial counted final priority Hcount Hnest Hlock Hselect Hhigh Hcur]; subst.
  inversion Hsecond as [initial counted' final priority' Hcount' Hnest' Hlock' Hselect' Hhigh' Hcur']; subst.
  assert (counted = counted') by (eapply os_int_exit_masked_active_counter_deterministic; eassumption).
  subst counted'; eapply os_int_exit_selection_heap_fragment_deterministic; eassumption.
Qed.

Definition os_int_exit_same_priority_state (state : UCOS2_Verify_State) :=
  os_int_exit_selection_state (os_int_exit_counter_state true state).

Lemma os_int_exit_masked_same_priority_raw_frame_post_with_ready_structure : forall sg state (frame : Assertion) heap,
  valid_stable_glob_vars sg -> sched_ready_structure sg state.(TskState) state.(SchedState) ->
  task_current_prio_registered state.(TskState) -> state.(SchedState).(readyList) <> [] ->
  state.(SchedState).(isRunning) = true ->
  interrupt_exit_requests_schedule true state.(IntrState) = true ->
  sched_selected_priority state.(TskState) state.(SchedState) =
    sched_priority_byte state.(SchedState).(curSchedPrio) ->
  (UCOS2_raw_rep sg state ** unmap_table_rep sg ** frame) heap ->
  exists final, os_int_exit_masked_same_priority_fragment sg heap final /\
    (UCOS2_raw_rep sg (os_int_exit_same_priority_state state) ** unmap_table_rep sg ** frame) final.
Proof.
  intros sg state frame heap Hsg Hready Hregistered Hnonempty Hrunning Hschedule Hequal Hbefore.
  assert (Hsplit : UCOS2_raw_rep sg state ** unmap_table_rep sg ** frame |--
    UCOS2_raw_rep sg state ** (unmap_table_rep sg ** frame)) by entailer!.
  destruct (Hsplit heap Hbefore) as [owned [rest [Hjoin [Hraw Hframe]]]].
  destruct (os_int_exit_masked_counter_raw_post sg state owned Hraw)
    as [after [Hcounter Hafter]].
  rewrite Hrunning in Hcounter, Hafter.
  destruct (os_int_exit_masked_counter_fragment_frame sg owned true after rest heap Hcounter Hjoin)
    as [counted [Hsource Hjoined]].
  assert (Hnest : uchar_load sg.(g_OSIntNesting) 0 counted).
  { apply interrupt_exit_requests_schedule_iff in Hschedule; destruct Hschedule as [_ [Hcountzero Hlockzero]].
    eapply uchar_load_frame; [|exact Hjoined].
    pose proof (os_int_exit_raw_nesting_load sg _ after Hafter) as Hload.
    change (uchar_load sg.(g_OSIntNesting) (interrupt_exit_state true state.(IntrState)).(intNesting) after) in Hload.
    rewrite Hcountzero in Hload; exact Hload. }
  assert (Hlock : uchar_load sg.(g_OSLockNesting) 0 counted).
  { apply interrupt_exit_requests_schedule_iff in Hschedule; destruct Hschedule as [_ [Hcountzero Hlockzero]].
    eapply uchar_load_frame; [|exact Hjoined].
    pose proof (os_int_exit_raw_lock_load sg _ after Hafter) as Hload.
    change (uchar_load sg.(g_OSLockNesting) (interrupt_exit_state true state.(IntrState)).(lockNesting) after) in Hload.
    assert (Hunchanged : (interrupt_exit_state true state.(IntrState)).(lockNesting) =
      state.(IntrState).(lockNesting)).
    { unfold interrupt_exit_state; destruct (0 <? state.(IntrState).(intNesting)); reflexivity. }
    rewrite Hunchanged, Hlockzero in Hload; exact Hload. }
  assert (Hcounted : (UCOS2_raw_rep sg (os_int_exit_counter_state true state) **
    unmap_table_rep sg ** frame) counted).
  { assert (Hmerge : UCOS2_raw_rep sg (os_int_exit_counter_state true state) **
      (unmap_table_rep sg ** frame) |-- UCOS2_raw_rep sg (os_int_exit_counter_state true state) **
      unmap_table_rep sg ** frame) by entailer!.
    apply Hmerge; exists after, rest; split; [exact Hjoined|]; split; assumption. }
  destruct (os_int_exit_selection_raw_frame_post_with_ready_structure sg (os_int_exit_counter_state true state) frame counted
    Hsg Hready Hregistered Hnonempty Hcounted) as [final [Hselection [Hhigh [Hcurrent Hpost]]]].
  exists final; split; [|exact Hpost].
  change (uchar_load sg.(g_OSPrioHighRdy) (sched_selected_priority state.(TskState) state.(SchedState)) final) in Hhigh.
  rewrite Hequal in Hhigh.
  eapply OsIntExitMaskedSamePriority; eassumption.
Qed.

Lemma os_int_exit_masked_same_priority_raw_frame_post : forall sg state (frame : Assertion) heap,
  valid_stable_glob_vars sg -> sched_ready_in_range sg state.(TskState) state.(SchedState) ->
  task_current_prio_registered state.(TskState) -> state.(SchedState).(readyList) <> [] ->
  state.(SchedState).(isRunning) = true ->
  interrupt_exit_requests_schedule true state.(IntrState) = true ->
  sched_selected_priority state.(TskState) state.(SchedState) =
    sched_priority_byte state.(SchedState).(curSchedPrio) ->
  (UCOS2_raw_rep sg state ** unmap_table_rep sg ** frame) heap ->
  exists final, os_int_exit_masked_same_priority_fragment sg heap final /\
    (UCOS2_raw_rep sg (os_int_exit_same_priority_state state) ** unmap_table_rep sg ** frame) final.
Proof.
  intros; eapply os_int_exit_masked_same_priority_raw_frame_post_with_ready_structure;
    try eassumption; eapply sched_ready_in_range_implies_structure; eassumption.
Qed.

Lemma os_int_exit_masked_same_priority_frame_post : forall sg state (frame : Assertion) heap,
  state.(SchedState).(isRunning) = true ->
  interrupt_exit_requests_schedule true state.(IntrState) = true ->
  state.(SchedState).(readyList) <> [] ->
  sched_selected_priority state.(TskState) state.(SchedState) =
    sched_priority_byte state.(SchedState).(curSchedPrio) ->
  (UCOS2_inv sg state ** unmap_table_rep sg ** frame) heap ->
  exists final, os_int_exit_masked_same_priority_fragment sg heap final /\
    (UCOS2_inv sg (os_int_exit_same_priority_state state) ** unmap_table_rep sg ** frame) final.
Proof.
  intros sg state frame heap Hrunning Hschedule Hnonempty Hequal Hbefore.
  assert (Hvalid : UCOS2_state_inv sg state).
  { destruct Hbefore as [owned [rest [Hj [[kernel [table [Hj2 [[Hvalid Hraw] Htable]]]] Hframe]]]]. exact Hvalid. }
  assert (Hsg : valid_stable_glob_vars sg) by (exact (proj1 (proj1 Hvalid))).
  assert (Hregistered : task_current_prio_registered state.(TskState)).
  { destruct Hvalid as [_ [Ht _]]; unfold task_in_range in Ht; tauto. }
  assert (Herase : UCOS2_inv sg state ** unmap_table_rep sg ** frame |--
    UCOS2_raw_rep sg state ** unmap_table_rep sg ** frame) by (unfold UCOS2_inv; entailer!).
  destruct (os_int_exit_masked_same_priority_raw_frame_post sg state frame heap Hsg
    (proj1 (proj1 (proj2 (proj2 Hvalid)))) Hregistered Hnonempty
    Hrunning Hschedule Hequal (Herase heap Hbefore)) as [final [Hsource Hpost]].
  exists final; split; [exact Hsource|].
  assert (Hvalid' : UCOS2_state_inv sg (os_int_exit_same_priority_state state)).
  { apply os_int_exit_selection_state_preserves_validity; exact Hvalid. }
  assert (Hmerge : UCOS2_raw_rep sg (os_int_exit_same_priority_state state) ** unmap_table_rep sg ** frame |--
    UCOS2_inv sg (os_int_exit_same_priority_state state) ** unmap_table_rep sg ** frame).
  { unfold UCOS2_inv; entailer!. }
  exact (Hmerge final Hpost).
Qed.

Lemma os_int_exit_masked_same_priority_full_frame_post : forall sg state (frame : Assertion) heap,
  state.(SchedState).(isRunning) = true ->
  interrupt_exit_requests_schedule true state.(IntrState) = true ->
  state.(SchedState).(readyList) <> [] ->
  sched_selected_priority state.(TskState) state.(SchedState) =
    sched_priority_byte state.(SchedState).(curSchedPrio) ->
  (UCOS2_full_inv sg state ** unmap_table_rep sg ** frame) heap ->
  exists final, os_int_exit_masked_same_priority_fragment sg heap final /\
    (UCOS2_full_inv sg (os_int_exit_same_priority_state state) ** unmap_table_rep sg ** frame) final.
Proof.
  intros sg state frame heap Hrunning Hschedule Hnonempty Hequal Hbefore.
  assert (Hvalid : UCOS2_full_state_inv sg state).
  { destruct Hbefore as [owned [rest [Hj [[kernel [table [Hj2 [[Hvalid Hraw] Htable]]]] Hframe]]]]. exact Hvalid. }
  assert (Hsg : valid_stable_glob_vars sg) by (exact (proj1 (proj1 Hvalid))).
  assert (Hregistered : task_current_prio_registered state.(TskState)).
  { destruct Hvalid as [_ [Ht _]]; unfold task_in_range in Ht; tauto. }
  assert (Herase : UCOS2_full_inv sg state ** unmap_table_rep sg ** frame |--
    UCOS2_raw_rep sg state ** unmap_table_rep sg ** frame) by (unfold UCOS2_full_inv; entailer!).
  destruct (os_int_exit_masked_same_priority_raw_frame_post_with_ready_structure sg state frame heap Hsg
    (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid))))) Hregistered Hnonempty
    Hrunning Hschedule Hequal (Herase heap Hbefore)) as [final [Hsource Hpost]].
  exists final; split; [exact Hsource|].
  assert (Hvalid' : UCOS2_full_state_inv sg (os_int_exit_same_priority_state state)).
  { apply os_int_exit_selection_state_preserves_full_validity; exact Hvalid. }
  assert (Hmerge : UCOS2_raw_rep sg (os_int_exit_same_priority_state state) ** unmap_table_rep sg ** frame |--
    UCOS2_full_inv sg (os_int_exit_same_priority_state state) ** unmap_table_rep sg ** frame).
  { unfold UCOS2_full_inv; entailer!. }
  exact (Hmerge final Hpost).
Qed.

(** Consume the actual normal-IRQ no-switch branch at the same saved
    continuation. The input is an internal masked cut after the handler,
    not a narrowed public API precondition. Its live-current/saved-frame
    facts still require the intervening handler's source proof. No claim
    is made that equal priority bytes alone imply a live current task.

    Neither profiling counter is written on this C branch. The full-profile
    version therefore retains all profiling fields rather than pretending
    the macro is disabled. The constant unmap table is returned as well. *)
Lemma armv7a_irq_same_priority_resumes_saved_call :
  forall external platform port sg context state heap restored_pc,
  task_current_at state context.(os_int_exit_interrupted_stack).(stackLeaseSlot)
    context.(os_int_exit_interrupted_stack).(stackLeaseGeneration) ->
  os_int_exit_saved_exception_binding context state ->
  state.(SchedState).(isRunning) = true ->
  interrupt_exit_requests_schedule true state.(IntrState) = true ->
  state.(SchedState).(readyList) <> [] ->
  sched_selected_priority state.(TskState) state.(SchedState) =
    sched_priority_byte state.(SchedState).(curSchedPrio) ->
  tcb_field_address (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot) ->
  port.(os_int_exit_frame_return_source) context restored_pc ->
  (UCOS2_inv sg state ** unmap_table_rep sg ** armv7a_irq_handler_frame external platform port context) heap ->
  exists final,
    os_int_exit_masked_same_priority_fragment sg heap final /\
    armv7a_irq_restore_pointer_reads sg final
      (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
      context.(os_int_exit_interrupted_sp) /\
    (coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
      (kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
         context.(os_int_exit_interrupted_mask) **
       UCOS2_inv sg (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state state)
         context.(os_int_exit_interrupted_stack)) **
       task_stack_fragments_rep context.(os_int_exit_handler_stack) context.(os_int_exit_handler_fragments) **
       unmap_table_rep sg)) final.
Proof.
  intros external platform port sg context state heap restored_pc
    Hcurrent Hsaved Hrunning Hschedule Hnonempty Hequal Haddress Hpc Hbefore.
  destruct (os_int_exit_masked_same_priority_frame_post sg state _ heap
    Hrunning Hschedule Hnonempty Hequal Hbefore) as [final [Hsource Hafter]].
  assert (Hsplit : UCOS2_inv sg (os_int_exit_same_priority_state state) ** unmap_table_rep sg **
      armv7a_irq_handler_frame external platform port context |--
    (UCOS2_inv sg (os_int_exit_same_priority_state state) **
      armv7a_irq_handler_frame external platform port context) ** unmap_table_rep sg) by entailer!.
  destruct (Hsplit final Hafter) as [owned [table [Hjoin [Howned Htable]]]].
  destruct (armv7a_irq_wrapper_resumes_saved_call external platform port sg context
    (os_int_exit_same_priority_state state) owned restored_pc Hcurrent Hsaved Haddress Hpc Howned)
    as [Hreads [Hpcvalue Hpost]].
  exists final; split; [exact Hsource|].
  split; [eapply armv7a_irq_restore_pointer_reads_frame; eassumption|].
  split; [exact Hpcvalue|].
  exists owned, table; split; [exact Hjoin|]; split; assumption.
Qed.

Lemma armv7a_irq_same_priority_resumes_saved_call_full :
  forall external platform port sg context state heap restored_pc,
  task_current_at state context.(os_int_exit_interrupted_stack).(stackLeaseSlot)
    context.(os_int_exit_interrupted_stack).(stackLeaseGeneration) ->
  os_int_exit_saved_exception_binding context state ->
  state.(SchedState).(isRunning) = true ->
  interrupt_exit_requests_schedule true state.(IntrState) = true ->
  state.(SchedState).(readyList) <> [] ->
  sched_selected_priority state.(TskState) state.(SchedState) =
    sched_priority_byte state.(SchedState).(curSchedPrio) ->
  tcb_field_address (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot) ->
  port.(os_int_exit_frame_return_source) context restored_pc ->
  (UCOS2_full_inv sg state ** unmap_table_rep sg ** armv7a_irq_handler_frame external platform port context) heap ->
  exists final,
    os_int_exit_masked_same_priority_fragment sg heap final /\
    armv7a_irq_restore_pointer_reads sg final
      (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
      context.(os_int_exit_interrupted_sp) /\
    (coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
      (kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
         context.(os_int_exit_interrupted_mask) **
       UCOS2_full_inv sg (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state state)
         context.(os_int_exit_interrupted_stack)) **
       task_stack_fragments_rep context.(os_int_exit_handler_stack) context.(os_int_exit_handler_fragments) **
       unmap_table_rep sg)) final.
Proof.
  intros external platform port sg context state heap restored_pc
    Hcurrent Hsaved Hrunning Hschedule Hnonempty Hequal Haddress Hpc Hbefore.
  destruct (os_int_exit_masked_same_priority_full_frame_post sg state _ heap
    Hrunning Hschedule Hnonempty Hequal Hbefore) as [final [Hsource Hafter]].
  assert (Hsplit : UCOS2_full_inv sg (os_int_exit_same_priority_state state) ** unmap_table_rep sg **
      armv7a_irq_handler_frame external platform port context |--
    (UCOS2_full_inv sg (os_int_exit_same_priority_state state) **
      armv7a_irq_handler_frame external platform port context) ** unmap_table_rep sg) by entailer!.
  destruct (Hsplit final Hafter) as [owned [table [Hjoin [Howned Htable]]]].
  destruct (armv7a_irq_wrapper_resumes_saved_call_full external platform port sg context
    (os_int_exit_same_priority_state state) owned restored_pc Hcurrent Hsaved Haddress Hpc Howned)
    as [Hreads [Hpcvalue Hpost]].
  exists final; split; [exact Hsource|].
  split; [eapply armv7a_irq_restore_pointer_reads_frame; eassumption|].
  split; [exact Hpcvalue|].
  exists owned, table; split; [exact Hjoin|]; split; assumption.
Qed.
