Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cleanup_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_wait_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** The same success/abort/timeout C suffix, retaining only its existing
    fields owner. Timeout first consumes the actual EventTaskRemove post;
    the common stores then consume their typed cells. Neither step changes
    the current continuation-local assertion family. *)

Definition sem_pend_fields_cleanup_frame sg entry tid old : Assertion :=
  sem_pend_tcb_residual (task_slot_addr sg tid) (task_tcb64_image sg old) TCBEventPtr **
  store_prio_tbl sg entry.(TskState).(prioTbl) ** sem_post_task_frame sg entry.(TskState) tid **
  sem_pend_sched_without_current sg entry ** sem_pend_fields_task_sched_frame sg entry.

Definition sem_pend_fields_cleanup_cells sg state tid old : Assertion :=
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
  sem_pend_fields_cleanup_frame sg state tid old.

Definition sem_pend_fields_remove_call_frame sg entry eid current tid old : Assertion :=
  event_task_remove_tcb_frame (task_slot_addr sg tid) (task_tcb64_image sg old) **
  event_task_remove_ecb_frame sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg entry.(TskState) current) (old.(curPrio) / 8) **
  store_prio_tbl sg entry.(TskState).(prioTbl) ** sem_post_task_frame sg entry.(TskState) tid **
  sem_pend_sched_without_current sg entry **
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
  sem_pend_fields_task_sched_event_frame sg entry.

Lemma sem_pend_fields_cleanup_split : forall sg state tid old,
  UCOS2_state_inv sg state -> state.(SchedState).(curTaskID) = Some tid ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_fields_inv sg state |--
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (encode_task_status old.(stat))) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some (encode_pend_status old.(statPend))) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some (encode_event_link sg old.(eventPtr))) **
  sem_pend_fields_cleanup_frame sg state tid old.
Proof.
  intros * Hvalid Hcur Hold.
  sep_apply_l_atomic (sem_pend_fields_full_task_split sg state tid old Hvalid Hold).
  sep_apply_l_atomic (sem_pend_tcb_three_fields_split (task_slot_addr sg tid)
    (task_tcb64_image sg old) TCBEventPtr ltac:(discriminate) ltac:(discriminate)).
  unfold sem_pend_fields_full_task_frame, sem_pend_fields_cleanup_frame, sem_pend_sched_without_current,
    sched_raw_rep, sched_physical_rep.
  cbn [task_tcb64_image]; rewrite Hcur; cbn [encode_task_link]; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_resume_split_remove_call : forall sg resumed eid tid old current,
  sem_pend_resume_entry sg resumed eid tid old -> mutex_query_lookup resumed eid current ->
  event_object_layout_prop sg eid ->
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (encode_task_status old.(stat))) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some (encode_pend_status old.(statPend))) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some (encode_event_link sg old.(eventPtr))) **
  sem_pend_fields_cleanup_frame sg resumed tid old |--
  event_task_remove_pre (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (old.(curPrio) / 8) (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) **
  sem_pend_fields_remove_call_frame sg resumed eid current tid old.
Proof.
  intros * [Hvalid [Hcur [Hold [Hregistration Hready]]]] He Hlayout.
  pose proof Hvalid as [Hprofile [Htasks _]].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hpriority _]]]]]]]].
  specialize (Hpriority tid old Hold); unfold task_priority_in_range in Hpriority.
  assert (Hrow : 0 <= old.(curPrio) / 8 < 8)
    by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  unfold sem_pend_fields_cleanup_frame.
  sepcon_assoc_change.
  pose proof (sem_pend_tcb_merge_cleanup_unchanged sg tid old) as Hmerge.
  lazymatch type of Hmerge with
  | ?prefix |-- _ =>
      lazymatch goal with
      | |- ?whole |-- _ =>
          lazymatch whole with
          | ?a ** (?b ** (?c ** (?d ** ?frame))) =>
              assert (Hpacked : whole |-- prefix ** frame) by entailer!;
              rewrite Hpacked, Hmerge
          end
      end
  end.
  sepcon_assoc_change.
  unfold sem_pend_fields_task_sched_frame, UCOS2_raw_rep_missing_task_storage_sched_flag.
  sep_apply_l_atomic (event_raw_rep_split_eid sg resumed.(TskState) resumed.(EventState) eid current He).
  unfold used_event_rep.
  sep_apply_l_atomic (event_task_remove_storage_layout_split sg eid (task_slot_addr sg tid)
    (task_tcb64_image sg old) (event_image sg resumed.(TskState) current) (old.(curPrio) / 8)
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) Hlayout Hrow eq_refl eq_refl eq_refl
    (event_table_image_eq sg resumed.(TskState) current (old.(curPrio) / 8) Hrow) eq_refl).
  unfold sem_pend_fields_remove_call_frame, sem_pend_fields_task_sched_event_frame; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_event_task_remove_preserves_residual : forall sg s eid e tid old,
  s.(EventState).(inUsedEventStates) eid = Some e ->
  sem_pend_fields_task_sched_event_frame sg s |--
    sem_pend_fields_task_sched_event_frame sg (event_task_remove_state s eid e tid old).
Proof.
  intros sg s eid e tid old He.
  unfold sem_pend_fields_task_sched_event_frame, event_task_remove_state; simpl.
  sep_apply_l_atomic (queue_set_event_wait_list_preserves_storage
    sg s.(EventState) eid e (remove_Z_eqb tid e.(waitList)) He); repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_event_task_remove_merge : forall sg s eid e tid old,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> In tid e.(waitList) ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  let post := event_task_remove_state s eid e tid old in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  event_raw_rep sg s.(TskState) post.(EventState) **
  sem_pend_fields_task_sched_event_frame sg s |-- UCOS2_fields_inv sg post.
Proof.
  intros sg s eid e tid old Hvalid He Hin Hold post.
  pose proof (UCOS2_event_task_remove_preserves_validity sg s eid e tid old Hvalid He Hin Hold)
    as Hpost; fold post in Hpost.
  assert (Hindex : event_raw_rep sg s.(TskState) post.(EventState) =
    event_raw_rep sg post.(TskState) post.(EventState)).
  { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
  rewrite Hindex.
  sep_apply_l_atomic (sem_pend_fields_event_task_remove_preserves_residual sg s eid e tid old He); fold post.
  rewrite sem_pend_fields_inv_split_task_sched_event; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_remove_call_merge : forall sg resumed eid current tid old,
  sem_pend_resume_entry sg resumed eid tid old -> old.(statPend) = PendTimeout ->
  mutex_query_lookup resumed eid current -> event_object_layout_prop sg eid ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  event_task_remove_post (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (old.(curPrio) / 8) (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) **
  sem_pend_fields_remove_call_frame sg resumed eid current tid old |--
  UCOS2_fields_inv sg (event_task_remove_state resumed eid current tid old).
Proof.
  intros * [Hvalid [Hcur [Hold [[Hmulti0 [Hflag Hregistration]] Hready]]]] Htimeout He Hlayout.
  rewrite Htimeout in Hregistration.
  destruct (sem_pend_resume_timeout_event sg resumed eid tid old Hvalid Hold Hregistration)
    as [found [Hfound Hin]].
  assert (found = current) by congruence; subst found.
  pose proof Hvalid as [Hprofile [Htasks [_ [Hevents _]]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof Htasks as [_ [_ [_ [_ [_ [_ [Hunique _]]]]]]].
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  pose proof (Hentries eid current He) as [Hcanonical _].
  destruct (proj2 (proj2 Hcanonical) tid Hin) as [found [HpriorityLookup Hprio]].
  assert (found = old) by congruence; subst found.
  unfold sem_pend_fields_remove_call_frame, tcb_bit_x_of_prio, tcb_bit_y_of_prio,
    tcb_x_of_prio, tcb_y_of_prio.
  sepcon_assoc_change.
  pose proof (event_task_remove_abstract_storage_consequence sg resumed.(TskState)
    eid current tid old (task_slot_addr sg tid) Hlayout Hsg Hunique Hcanonical Hprio Hold) as Hremove_merge.
  lazymatch type of Hremove_merge with
  | ?remove_fields |-- _ =>
      lazymatch goal with
      | |- ?whole |-- _ =>
          lazymatch whole with
          | ?current_cell ** (?helper_post ** (?tcb_frame ** (?event_frame ** ?frame))) =>
              assert (Hpacked_remove : whole |-- remove_fields ** (current_cell ** frame)) by entailer!;
              rewrite Hpacked_remove, Hremove_merge
          end
      end
  end.
  sepcon_assoc_change.
  sep_apply_l_atomic (sem_post_task_storage_merge sg resumed.(TskState) tid
    (task_set_event_ptr old None) Hmulti Hprofiling).
  fold (used_event_rep sg resumed.(TskState) eid
    (event_set_wait_list current (remove_Z_eqb tid current.(waitList)))).
  sep_apply_l_atomic (event_raw_rep_merge_updated_eid sg resumed.(TskState) resumed.(EventState)
    eid (event_set_wait_list current (remove_Z_eqb tid current.(waitList)))).
  assert (Hindex : sched_raw_rep sg resumed.(TskState) resumed.(SchedState) =
    sched_raw_rep sg (glob_task_set_usedtask resumed.(TskState) tid (task_set_event_ptr old None)) resumed.(SchedState)).
  { apply sched_raw_rep_priority_ext; intros slot HinSlot.
    change (option_map curPrio (resumed.(TskState).(inUsedTaskStates) slot) =
      option_map curPrio (if Z.eqb slot tid then Some (task_set_event_ptr old None)
        else resumed.(TskState).(inUsedTaskStates) slot)).
    destruct (Z.eqb slot tid) eqn:E;
      [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  pose proof (sem_pend_fields_event_task_remove_merge sg resumed eid current tid old Hvalid He Hin Hold)
    as Hmerge_storage.
  let merge_type := type of Hmerge_storage in
  let merge_type := eval cbv zeta in merge_type in
  lazymatch merge_type with
  | ?pre |-- _ =>
      lazymatch goal with
      | |- ?left |-- _ =>
          assert (Hresources : left |-- pre);
          [ | intros heap Hheap; exact (Hmerge_storage heap (Hresources heap Hheap)) ]
      end
  end.
  cbn [event_task_remove_state replace_TskS replace_EventS TskState SchedState EventState].
  rewrite <- Hindex; unfold sem_pend_sched_without_current, sched_raw_rep, sched_physical_rep.
  rewrite Hcur; cbn [encode_task_link]; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_event_pend_cleanup_merge : forall sg s tid old clear_message,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = nil ->
  old.(tcbFlagNode) = 0 -> In tid s.(SchedState).(readyList) ->
  let post := event_pend_cleanup_state sg clear_message s tid old in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  sem_pend_fields_task_sched_frame sg s |-- UCOS2_fields_inv sg post.
Proof.
  intros sg s tid old clear_message Hvalid Hold Hnull Hmulti Hflagnull Hready post.
  assert (Hprio : (task_event_pend_cleanup sg.(osKernelConfig).(cfgEventMultiEnabled) clear_message old).(curPrio)
    = old.(curPrio)) by (destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity).
  assert (Hevent : event_raw_rep sg s.(TskState) s.(EventState) =
    event_raw_rep sg post.(TskState) s.(EventState)).
  { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; eauto. }
  assert (Hsched : sched_raw_rep sg s.(TskState) s.(SchedState) =
    sched_raw_rep sg post.(TskState) s.(SchedState)).
  { apply sched_raw_rep_priority_ext; intros slot Hin.
    change (option_map curPrio (s.(TskState).(inUsedTaskStates) slot) =
      option_map curPrio (if Z.eqb slot tid then
        Some (task_event_pend_cleanup sg.(osKernelConfig).(cfgEventMultiEnabled) clear_message old)
        else s.(TskState).(inUsedTaskStates) slot)).
    destruct (Z.eqb slot tid) eqn:E; [|reflexivity].
    apply Z.eqb_eq in E; subst slot; rewrite Hold.
    destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity. }
  pose proof (UCOS2_event_pend_cleanup_preserves_validity
    sg s tid old clear_message Hvalid Hold Hnull Hmulti Hflagnull Hready) as Hpost; fold post in Hpost.
  rewrite Hsched.
  unfold sem_pend_fields_task_sched_frame, UCOS2_raw_rep_missing_task_storage_sched_flag.
  rewrite Hevent, UCOS2_fields_inv_split_task_storage_sched_flag.
  unfold UCOS2_raw_rep_missing_task_storage_sched_flag.
  unfold post, event_pend_cleanup_state in *.
  cbn [replace_TskS TskState SchedState EventState IntrState TickState FlagState MemoryState
    TimerState StatsState ControlState NameState glob_task_set_usedtask parkedTaskStacks].
  repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_cleanup_merge : forall sg state tid old,
  sem_pend_cleanup_entry sg state tid old ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
  sem_pend_fields_cleanup_frame sg state tid old |--
  UCOS2_fields_inv sg (event_pend_cleanup_state sg false state tid old).
Proof.
  intros * [Hvalid [Hcur [Hold [Hnone [Hmulti0 [Hflag Hready]]]]]].
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  unfold sem_pend_fields_cleanup_frame.
  sepcon_assoc_change.
  pose proof (sem_pend_tcb_merge_cleanup sg tid old) as Hmerge.
  lazymatch type of Hmerge with
  | ?prefix |-- _ =>
      lazymatch goal with
      | |- ?whole |-- _ =>
          lazymatch whole with
          | ?current ** (?a ** (?b ** (?c ** (?d ** ?frame)))) =>
              assert (Hpacked : whole |-- prefix ** (current ** frame)) by entailer!;
              rewrite Hpacked, Hmerge
          end
      end
  end.
  sepcon_assoc_change.
  sep_apply_l_atomic (sem_post_task_storage_merge sg state.(TskState) tid
    (task_event_pend_cleanup false false old) Hmulti Hprofiling).
  pose proof (sem_pend_fields_event_pend_cleanup_merge sg state tid old false
    Hvalid Hold Hnone Hmulti0 Hflag Hready) as Hmerge_storage.
  let merge_type := type of Hmerge_storage in
  let merge_type := eval cbv zeta in merge_type in
  lazymatch merge_type with
  | ?pre |-- _ =>
      lazymatch goal with
      | |- ?left |-- _ =>
          assert (Hresources : left |-- pre);
          [ | intros heap Hheap; exact (Hmerge_storage heap (Hresources heap Hheap)) ]
      end
  end.
  cbn [event_pend_cleanup_state replace_TskS TskState].
  rewrite Hmulti; unfold sem_pend_sched_without_current, sched_raw_rep, sched_physical_rep.
  rewrite Hcur; cbn [encode_task_link]; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_observed_timeout_remove_cleanup : forall environment critical sg context mask before observed eid
  timeout resumed tid old current,
  sem_pend_observed_resume_origin environment critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) = PendTimeout -> mutex_query_lookup resumed eid current -> event_object_layout_prop sg eid ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  event_task_remove_post (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (old.(curPrio) / 8) (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) **
  sem_pend_fields_remove_call_frame sg resumed eid current tid old |--
  coq_prop (sem_pend_observed_cleanup_origin environment critical sg context mask before observed eid timeout 10
    (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None)) &&
  UCOS2_fields_inv sg (event_task_remove_state resumed eid current tid old).
Proof.
  intros * Horigin Htimeout Hlookup Hlayout.
  pose proof (sem_pend_observed_resume_cleanup_timeout environment critical sg context mask before observed eid
    timeout resumed tid old current Horigin Htimeout Hlookup) as Hcleanup.
  sep_apply_l_atomic (sem_pend_fields_remove_call_merge sg resumed eid current tid old
    (proj1 Horigin) Htimeout Hlookup Hlayout); repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_observed_cleanup_return_merge : forall environment critical sg context mask before observed eid
  pevent timeout error cleaning tid node,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_observed_cleanup_origin environment critical sg context mask before observed eid timeout error cleaning tid node ->
  sem_pend_fields_cleanup_cells sg cleaning tid node |--
  coq_prop (sem_pend_checkpoint_result environment critical sg context pevent timeout before error
    (event_pend_cleanup_state sg false cleaning tid node)) &&
  UCOS2_fields_inv sg (event_pend_cleanup_state sg false cleaning tid node).
Proof.
  intros * Hnonnull Haddress Hid Hslot Hordered Horigin.
  pose proof (sem_pend_observed_cleanup_result environment critical sg context mask before observed eid
    pevent timeout error cleaning tid node Hnonnull Haddress Hid Hslot Hordered Horigin) as Hresult.
  unfold sem_pend_fields_cleanup_cells.
  sep_apply_l_atomic (sem_pend_fields_cleanup_merge sg cleaning tid node (proj1 Horigin)); repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_cleanup_stores_source : forall sg state tid old perr error
  (frame : Assertion) before,
  sem_pend_cleanup_entry sg state tid old -> 0 <= error < 256 ->
  (UCOS2_fields_inv sg state ** perr # UChar |->_ ** frame) before ->
  exists after,
    sem_pend_cleanup_fragment sg perr error before after /\
    (sem_pend_fields_cleanup_cells sg state tid old ** perr # UChar |-> error ** frame) after.
Proof.
  intros sg state tid old perr error frame before Hentry Hrange Hpre.
  pose proof Hentry as [Hvalid [Hcurrent [Hold [Hregistration [Hmulti [Hflag Hready]]]]]].
  set (base := task_slot_addr sg tid).
  set (tail := sg.(g_OSTCBCur) # Ptr |-> base **
    tcb_cell base TCBStat (Some (encode_task_status old.(stat))) **
    tcb_cell base TCBStatPend (Some (encode_pend_status old.(statPend))) ** tcb_cell base TCBEventPtr (Some 0) **
    sem_pend_fields_cleanup_frame sg state tid old ** frame).
  assert (Hsplit : UCOS2_fields_inv sg state ** perr # UChar |->_ ** frame |--
    perr # UChar |->_ ** tail).
  { sep_apply_l_atomic (sem_pend_fields_cleanup_split sg state tid old Hvalid Hcurrent Hold).
    rewrite Hregistration; cbn [encode_event_link].
    unfold tail, base; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end). }
  destruct (sem_pend_error_store perr error tail before Hrange (Hsplit before Hpre))
    as [error_written [Herror Herror_post]].
  set (stat_frame := sg.(g_OSTCBCur) # Ptr |-> base **
    tcb_cell base TCBStatPend (Some (encode_pend_status old.(statPend))) ** tcb_cell base TCBEventPtr (Some 0) **
    sem_pend_fields_cleanup_frame sg state tid old ** perr # UChar |-> error ** frame).
  assert (Hstat : perr # UChar |-> error ** tail |--
    tcb_field_address base TCBStat # UChar |-> encode_task_status old.(stat) ** stat_frame).
  { unfold tail, stat_frame; cbn [tcb_cell]; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end). }
  assert (Hread_error : pointer_load sg.(g_OSTCBCur) base error_written).
  { eapply framed_pointer_store_load.
    assert (Hr : perr # UChar |-> error ** tail |-- sg.(g_OSTCBCur) # Ptr |-> base ** TT).
    { unfold tail; entailer!; intros ? ?; exact I. }
    exact (Hr error_written Herror_post). }
  destruct (kernel_heap_framed_uchar_store (tcb_field_address base TCBStat)
    (encode_task_status old.(stat)) 0 stat_frame error_written ltac:(lia)
    (Hstat error_written Herror_post)) as [status_written [Hstatus Hstatus_post]].
  set (pend_frame := sg.(g_OSTCBCur) # Ptr |-> base **
    tcb_cell base TCBStat (Some 0) ** tcb_cell base TCBEventPtr (Some 0) **
    sem_pend_fields_cleanup_frame sg state tid old ** perr # UChar |-> error ** frame).
  assert (Hpend : tcb_field_address base TCBStat # UChar |-> 0 ** stat_frame |--
    tcb_field_address base TCBStatPend # UChar |-> encode_pend_status old.(statPend) ** pend_frame).
  { unfold stat_frame, pend_frame; cbn [tcb_cell]; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end). }
  assert (Hread_status : pointer_load sg.(g_OSTCBCur) base status_written).
  { eapply framed_pointer_store_load.
    assert (Hr : tcb_field_address base TCBStat # UChar |-> 0 ** stat_frame |--
      sg.(g_OSTCBCur) # Ptr |-> base ** TT).
    { unfold stat_frame; entailer!; intros ? ?; exact I. }
    exact (Hr status_written Hstatus_post). }
  destruct (kernel_heap_framed_uchar_store (tcb_field_address base TCBStatPend)
    (encode_pend_status old.(statPend)) 0 pend_frame status_written ltac:(lia) (Hpend status_written Hstatus_post))
    as [pending_written [Hpending Hpending_post]].
  set (event_frame := sg.(g_OSTCBCur) # Ptr |-> base **
    tcb_cell base TCBStat (Some 0) ** tcb_cell base TCBStatPend (Some 0) **
    sem_pend_fields_cleanup_frame sg state tid old ** perr # UChar |-> error ** frame).
  assert (Hevent : tcb_field_address base TCBStatPend # UChar |-> 0 ** pend_frame |--
    tcb_field_address base TCBEventPtr # Ptr |->_ ** event_frame).
  { unfold pend_frame, event_frame; cbn [tcb_cell].
    sep_apply_l_atomic (store_ptr_undef_store_ptr (tcb_field_address base TCBEventPtr) 0).
    repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end). }
  assert (Hread_pending : pointer_load sg.(g_OSTCBCur) base pending_written).
  { eapply framed_pointer_store_load.
    assert (Hr : tcb_field_address base TCBStatPend # UChar |-> 0 ** pend_frame |--
      sg.(g_OSTCBCur) # Ptr |-> base ** TT).
    { unfold pend_frame; entailer!; intros ? ?; exact I. }
    exact (Hr pending_written Hpending_post). }
  destruct (framed_pointer_store_execution (tcb_field_address base TCBEventPtr) 0
    event_frame pending_written ltac:(lia) (Hevent pending_written Hpending_post))
    as [after [Hclear Hafter]].
  exists after; split.
  - exists base, error_written, status_written, pending_written; tauto.
  - assert (Hclose : tcb_field_address base TCBEventPtr # Ptr |-> 0 ** event_frame |--
      sem_pend_fields_cleanup_cells sg state tid old ** perr # UChar |-> error ** frame).
    { unfold sem_pend_fields_cleanup_cells, event_frame, base; cbn [tcb_cell]; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end). }
    exact (Hclose after Hafter).
Qed.

(** This source producer executes the actual error and three TCB stores,
    then consumes the observed branch history. The exact checkpoint result
    is the original Pend program's result, shared by all three arms. *)
Lemma sem_pend_fields_observed_cleanup_stores_source : forall environment critical sg context mask
  initial observed eid pevent timeout error cleaning tid node perr (frame : Assertion) before,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  sem_pend_observed_cleanup_origin environment critical sg context mask initial observed eid
    timeout error cleaning tid node ->
  (UCOS2_fields_inv sg cleaning ** perr # UChar |->_ ** frame) before ->
  exists after,
    sem_pend_cleanup_fragment sg perr error before after /\
    sem_pend_checkpoint_result environment critical sg context pevent timeout initial error
      (event_pend_cleanup_state sg false cleaning tid node) /\
    (UCOS2_fields_inv sg (event_pend_cleanup_state sg false cleaning tid node) **
      perr # UChar |-> error ** frame) after.
Proof.
  intros environment critical sg context mask initial observed eid pevent timeout error cleaning
    tid node perr frame before Hnonnull Haddress Hid Hslot Hordered Horigin Hpre.
  assert (Hrange : 0 <= error < 256).
  { destruct Horigin as [_ [resumed [old [code [Hresume [Herror Hstep]]]]]].
    destruct Hstep as [slot [task [_ [_ [Hcode Hstep]]]]].
    rewrite Herror, Hcode; destruct task.(statPend); cbn; lia. }
  destruct (sem_pend_fields_cleanup_stores_source sg cleaning tid node perr error frame before
    (proj1 Horigin) Hrange Hpre) as [after [Hsource Hcells]].
  assert (Hmerge : sem_pend_fields_cleanup_cells sg cleaning tid node ** perr # UChar |-> error ** frame |--
    coq_prop (sem_pend_checkpoint_result environment critical sg context pevent timeout initial error
      (event_pend_cleanup_state sg false cleaning tid node)) &&
    (UCOS2_fields_inv sg (event_pend_cleanup_state sg false cleaning tid node) **
      perr # UChar |-> error ** frame)).
  { sep_apply_l_atomic (sem_pend_fields_observed_cleanup_return_merge environment critical sg context mask
      initial observed eid pevent timeout error cleaning tid node Hnonnull Haddress Hid Hslot Hordered Horigin).
    repeat rewrite logic_equiv_coq_prop_andp_sepcon.
    repeat rewrite logic_equiv_sepcon_coq_prop_andp.
    repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end). }
  destruct (Hmerge after Hcells) as [Hresult Hafter].
  exists after; tauto.
Qed.

Lemma sem_pend_fields_remove_preserves_call_source : forall context state eid current tid old,
  state.(TskState).(inUsedTaskStates) tid = Some old -> kernel_call_task_source context state ->
  kernel_call_task_source context (event_task_remove_state state eid current tid old).
Proof.
  intros context state eid current tid old Hnode [Hlease [Hactive Hcurrent]].
  split; [exact Hlease|]; split; [|exact Hcurrent].
  cbn [event_task_remove_state replace_TskS replace_EventS TskState].
  eapply glob_task_set_usedtask_preserves_invocation_active;
    [exact Hnode|reflexivity|exact Hactive].
Qed.

Lemma sem_pend_fields_cleanup_preserves_call_source : forall sg context state tid old,
  state.(TskState).(inUsedTaskStates) tid = Some old -> kernel_call_task_source context state ->
  kernel_call_task_source context (event_pend_cleanup_state sg false state tid old).
Proof.
  intros sg context state tid old Hnode [Hlease [Hactive Hcurrent]].
  split; [exact Hlease|]; split; [|exact Hcurrent].
  cbn [event_pend_cleanup_state replace_TskS TskState].
  eapply glob_task_set_usedtask_preserves_invocation_active;
    [exact Hnode|destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity|exact Hactive].
Qed.

(** Timeout's helper returns the existing typed post. The real Queue
    transport and updated Task generation/SP produce the fields world and
    the same arbitrary local map at that new cleaning checkpoint. *)
Lemma sem_pend_fields_timeout_remove_continuation_merge : forall environment local critical sg
  original mask initial observed eid timeout resumed tid old current call saved acquired,
  sem_pend_observed_resume_origin (Some environment) critical sg original mask initial observed eid
    timeout resumed tid old ->
  old.(statPend) = PendTimeout -> mutex_query_lookup resumed eid current -> event_object_layout_prop sg eid ->
  kernel_call_task_source call resumed ->
  task_stack_live_coverage resumed.(TskState) (task_stack_call_active_key call) ->
  critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired **
  os_sched_context_resources environment.(task_stack_call_external) call **
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  event_task_remove_post (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (old.(curPrio) / 8) (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) **
  sem_pend_fields_remove_call_frame sg resumed eid current tid old ** unmap_table_rep sg **
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) resumed.(TskState) local)
    resumed.(TskState).(parkedTaskStacks) |--
  coq_prop (sem_pend_observed_cleanup_origin (Some environment) critical sg original mask initial observed eid
      timeout 10 (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None) /\
    kernel_call_task_source call (event_task_remove_state resumed eid current tid old)) &&
  sem_pend_fields_masked environment local critical sg call saved acquired
    (event_task_remove_state resumed eid current tid old).
Proof.
  intros environment local critical sg original mask initial observed eid timeout resumed tid old current
    call saved acquired Horigin Htimeout Hlookup Hlayout Hsource Hcoverage.
  pose proof (proj1 Horigin) as [_ [_ [Hold _]]].
  pose proof (sem_pend_fields_remove_preserves_call_source call resumed eid current tid old Hold Hsource)
    as Hsource_after.
  assert (Hcovered : task_stack_live_coverage (event_task_remove_state resumed eid current tid old).(TskState)
    (task_stack_call_active_key call)).
  { apply (sem_pend_fields_task_update_preserves_coverage resumed.(TskState) (task_stack_call_active_key call)
      tid old (task_set_event_ptr old None) Hold eq_refl Hcoverage). }
  sep_apply_l_atomic (sem_pend_fields_observed_timeout_remove_cleanup (Some environment) critical sg original
    mask initial observed eid timeout resumed tid old current Horigin Htimeout Hlookup Hlayout).
  sep_apply_l_atomic (sem_pend_fields_task_update_continuations environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) local resumed.(TskState) tid old
    (task_set_event_ptr old None) Hold eq_refl eq_refl).
  repeat rewrite logic_equiv_coq_prop_andp_sepcon.
  repeat rewrite logic_equiv_sepcon_coq_prop_andp.
  unfold sem_pend_fields_masked, kernel_continuation_call_masked, kernel_continuation_inv.
  rewrite kernel_program_fields_inv_split_unmap; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_cleanup_continuation_merge : forall environment local critical sg
  call saved acquired cleaning tid old,
  sem_pend_cleanup_entry sg cleaning tid old -> kernel_call_task_source call cleaning ->
  task_stack_live_coverage cleaning.(TskState) (task_stack_call_active_key call) ->
  critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired **
  os_sched_context_resources environment.(task_stack_call_external) call **
  sem_pend_fields_cleanup_cells sg cleaning tid old ** unmap_table_rep sg **
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) cleaning.(TskState) local)
    cleaning.(TskState).(parkedTaskStacks) |--
  coq_prop (kernel_call_task_source call (event_pend_cleanup_state sg false cleaning tid old)) &&
  sem_pend_fields_masked environment local critical sg call saved acquired
    (event_pend_cleanup_state sg false cleaning tid old).
Proof.
  intros environment local critical sg call saved acquired cleaning tid old Hentry Hsource Hcoverage.
  pose proof Hentry as [Hvalid [_ [Hold _]]].
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof (sem_pend_fields_cleanup_preserves_call_source sg call cleaning tid old Hold Hsource) as Hsource_after.
  assert (Hcovered : task_stack_live_coverage (event_pend_cleanup_state sg false cleaning tid old).(TskState)
    (task_stack_call_active_key call)).
  { cbn [event_pend_cleanup_state replace_TskS TskState]; rewrite Hmulti.
    apply (sem_pend_fields_task_update_preserves_coverage cleaning.(TskState) (task_stack_call_active_key call)
      tid old (task_event_pend_cleanup false false old) Hold eq_refl Hcoverage). }
  cbn [event_pend_cleanup_state replace_TskS TskState] in Hcovered.
  rewrite Hmulti in Hcovered.
  unfold sem_pend_fields_cleanup_cells.
  sep_apply_l_atomic (sem_pend_fields_cleanup_merge sg cleaning tid old Hentry).
  sep_apply_l_atomic (sem_pend_fields_task_update_continuations environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) local cleaning.(TskState) tid old
    (task_event_pend_cleanup false false old) Hold eq_refl eq_refl).
  unfold sem_pend_fields_masked, kernel_continuation_call_masked, kernel_continuation_inv.
  rewrite kernel_program_fields_inv_split_unmap.
  cbn [event_pend_cleanup_state replace_TskS TskState glob_task_set_usedtask parkedTaskStacks]; rewrite Hmulti.
  repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

(** The actual final Restore consumer. Error-cell/App resources frame this
    implication; the original same-X return bridge consumes its unchanged
    checkpoint result after the generic current-map Restore completes. *)
Lemma sem_pend_fields_cleanup_restore_input : forall environment local critical sg original initial_mask
  initial observed eid pevent timeout error cleaning tid node call mask saved acquired,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  sem_pend_observed_cleanup_origin (Some environment) critical sg original initial_mask initial observed eid
    timeout error cleaning tid node ->
  interrupt_saved_value mask saved -> kernel_call_task_source call cleaning ->
  task_stack_live_coverage cleaning.(TskState) (task_stack_call_active_key call) ->
  critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired **
  os_sched_context_resources environment.(task_stack_call_external) call **
  sem_pend_fields_cleanup_cells sg cleaning tid node ** unmap_table_rep sg **
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) cleaning.(TskState) local)
    cleaning.(TskState).(parkedTaskStacks) |--
  coq_prop (sem_pend_checkpoint_result (Some environment) critical sg original pevent timeout initial error
      (event_pend_cleanup_state sg false cleaning tid node)) &&
  sem_pend_fields_phase_restore_input SemPendReturnPhase environment local critical sg call mask saved acquired
    (event_pend_cleanup_state sg false cleaning tid node).
Proof.
  intros environment local critical sg original initial_mask initial observed eid pevent timeout error cleaning
    tid node call mask saved acquired Hnonnull Haddress Hid Hslot Hordered Horigin Hsaved Hsource Hcoverage.
  pose proof (sem_pend_observed_cleanup_result (Some environment) critical sg original initial_mask initial observed
    eid pevent timeout error cleaning tid node Hnonnull Haddress Hid Hslot Hordered Horigin) as Hresult.
  sep_apply_l_atomic (sem_pend_fields_cleanup_continuation_merge environment local critical sg call saved acquired
    cleaning tid node (proj1 Horigin) Hsource Hcoverage).
  unfold sem_pend_fields_phase_restore_input; cbn [sem_pend_restore_phase_pre]; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.
