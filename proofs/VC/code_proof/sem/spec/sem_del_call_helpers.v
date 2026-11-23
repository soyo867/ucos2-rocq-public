Require Export Ucos2Verify.VC.code.sem.spec.sem_del_call_spec.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.field_storage.
Import ListNotations UCOS2_C_Rules Monad.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition sem_del_wake_result (sg : StableGlobVars) (eid : EventID)
  (entry after : UCOS2_Verify_State) (priority : Z) : Prop :=
  event_task_rdy sg entry eid PendSem 0 PendAbort = Some (priority, after).

Lemma sem_del_wake_loop_facts : forall sg eid entry state node priority next,
  sem_del_loop_facts sg eid entry state node -> sem_del_group state node <> 0 ->
  sem_del_wake_result sg eid state next priority ->
  exists next_node, sem_del_loop_facts sg eid entry next next_node.
Proof.
  intros sg eid entry state node priority next [Hprefix [Hlookup [Htype Hvalid]]] Hgroup Hstep.
  destruct node.(waitList) as [|head tail] eqn:Hlist.
  { exfalso; apply Hgroup; unfold sem_del_group, sem_post_group; rewrite Hlist; reflexivity. }
  assert (Hkind : event_type_to_pend_type node.(eventType) = Some PendSem)
    by (rewrite Htype; reflexivity).
  destruct (event_wake_head sg state eid node head tail PendSem 0 PendAbort
    Hvalid Hlookup Hkind Hlist) as [old [Hold [Hcall [Hafter Hnode]]]].
  unfold sem_del_wake_result in Hstep; rewrite Hcall in Hstep; injection Hstep as Hp Hnext; subst next.
  exists (event_set_wait_list node tail); unfold sem_del_loop_facts.
  split; [eapply sem_del_abort_prefix_step; eassumption|].
  split; [exact Hnode|]; split; [exact Htype|exact Hafter].
Qed.

Lemma sem_del_critical_no_pend_empty : forall sg entry eid node,
  sem_del_lookup entry eid node -> sem_del_group entry node = 0 ->
  sem_del_critical_result sg eid 0 entry 0 0 0 (event_delete_recycle_state sg entry eid node).
Proof.
  intros sg entry eid node Hlookup Hgroup; exists OS_ERR_NONE, false.
  split; [reflexivity|]; split; [reflexivity|].
  exists node; split; [exact Hlookup|]; simpl.
  unfold sem_del_group, sem_post_group in Hgroup; rewrite Hgroup; split; reflexivity.
Qed.

Lemma sem_del_critical_no_pend_waiting : forall sg entry eid node,
  sem_del_lookup entry eid node -> sem_del_group entry node <> 0 ->
  sem_del_critical_result sg eid 0 entry (event_addr sg eid) 73 0 entry.
Proof.
  intros sg entry eid node Hlookup Hgroup; exists OS_ERR_TASK_WAITING, false.
  split; [reflexivity|]; split; [reflexivity|].
  exists node; split; [exact Hlookup|]; simpl.
  unfold sem_del_group, sem_post_group in Hgroup; rewrite (proj2 (Z.eqb_neq _ _) Hgroup).
  split; reflexivity.
Qed.

Lemma sem_del_critical_invalid_option : forall sg entry eid node opt,
  sem_del_lookup entry eid node -> opt <> 0 -> opt <> 1 ->
  sem_del_critical_result sg eid opt entry (event_addr sg eid) 7 0 entry.
Proof.
  intros sg entry eid node opt Hlookup Hnone Halways; exists OS_ERR_INVALID_OPT, false.
  split; [reflexivity|]; split; [reflexivity|].
  exists node; split; [exact Hlookup|].
  rewrite (proj2 (Z.eqb_neq _ _) Hnone), (proj2 (Z.eqb_neq _ _) Halways); split; reflexivity.
Qed.

Lemma sem_del_critical_always_recycled : forall sg entry eid current state node waiting,
  sem_del_lookup entry eid current -> sem_del_waiting entry current waiting ->
  sem_del_loop_facts sg eid entry state node -> sem_del_group state node = 0 ->
  sem_del_critical_result sg eid 1 entry 0 0 waiting (event_delete_recycle_state sg state eid node).
Proof.
  intros sg entry eid current state node waiting Hlookup Hwaiting
    [Hprefix [Hnode [Htype Hvalid]]] Hzero.
  destruct (sem_del_abort_prefix_complete sg eid entry state Hprefix [] state
    (event_broadcast_done sg eid PendSem 0 PendAbort state node Hnode Hzero)) as [priorities Hloop].
  destruct Hwaiting as [[Hgroup ->]|[Hgroup ->]].
  - exists OS_ERR_NONE, false; split; [reflexivity|]; split; [reflexivity|].
    exists current; split; [exact Hlookup|]; simpl.
    exists priorities, state, node; split; [exact Hloop|]; split; [exact Hnode|].
    unfold sem_del_group, sem_post_group in Hgroup; rewrite Hgroup; split; reflexivity.
  - exists OS_ERR_NONE, true; split; [reflexivity|]; split; [reflexivity|].
    exists current; split; [exact Hlookup|]; simpl.
    exists priorities, state, node; split; [exact Hloop|]; split; [exact Hnode|].
    unfold sem_del_group, sem_post_group in Hgroup; rewrite (proj2 (Z.eqb_neq _ _) Hgroup).
    split; reflexivity.
Qed.

Lemma sem_del_call_null_return : forall external critical sg context opt before,
  sem_del_call_program external critical sg context 0 opt before (0, 4) before.
Proof. intros; left; repeat split; reflexivity. Qed.

Lemma sem_del_call_wrong_type_return : forall external critical sg context pe opt before eid observed,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_del_lookup before eid observed -> observed.(eventType) <> OS_EVENT_TYPE_SEM ->
  sem_del_call_program external critical sg context pe opt before (pe, 1) before.
Proof.
  intros; right; split; [assumption|]; exists eid, observed.
  split; [assumption|]; split; [assumption|]; split; [assumption|].
  left; repeat split; assumption || reflexivity.
Qed.

Lemma sem_del_call_isr_return : forall external critical sg context pe opt before eid observed,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_del_lookup before eid observed -> observed.(eventType) = OS_EVENT_TYPE_SEM ->
  0 < sem_del_int_nesting before ->
  sem_del_call_program external critical sg context pe opt before (pe, 15) before.
Proof.
  intros; right; split; [assumption|]; exists eid, observed.
  split; [assumption|]; split; [assumption|]; split; [assumption|].
  right; split; [assumption|]; left; repeat split; assumption || reflexivity.
Qed.

Lemma sem_del_nonscheduled_return :
  forall external platform critical sg context mask pe opt perr before eid observed saved entry current
    checkpoint ret err requests X,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid -> requests <> 1 ->
  sem_del_acquire_facts external critical sg context eid opt mask saved before entry observed current ->
  sem_del_critical_result sg eid opt entry ret err requests checkpoint ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_del_call_program external critical sg context pe opt)) observe_sem_del_call) X ->
  perr # UChar |-> err ** sem_del_closed platform critical sg context mask checkpoint **
    os_sched_context_resources external context ** unmap_table_rep sg |--
  sem_del_call_post external platform critical sg context mask pe opt perr before ret X.
Proof.
  intros external platform critical sg context mask pe opt perr before eid observed saved entry current
    checkpoint ret err requests X Hnonzero Haddr Hid Hnonsched Hfacts
    [code [requested [Herror [Hrequests Hstep]]]] Hexec.
  destruct requested; [contradiction Hnonsched; exact Hrequests|].
  apply sem_del_closed_return; [|exact Hexec].
  rewrite Herror; eapply sem_del_call_protected_return; eauto; reflexivity.
Qed.

Lemma sem_del_scheduled_return :
  forall external platform critical sg context mask pe opt perr before eid observed saved entry current
    checkpoint X,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_del_acquire_facts external critical sg context eid opt mask saved before entry observed current ->
  sem_del_critical_result sg eid opt entry 0 0 1 checkpoint ->
  UCOS2_state_inv sg checkpoint -> os_sched_acquire_safety external critical sg context checkpoint ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_del_call_program external critical sg context pe opt)) observe_sem_del_call) X ->
  perr # UChar |-> 0 ** os_sched_post external platform critical sg context mask checkpoint |--
    sem_del_call_post external platform critical sg context mask pe opt perr before 0 X.
Proof.
  intros external platform critical sg context mask pe opt perr before eid observed saved entry current
    checkpoint X Hnonzero Haddr Hid Hfacts [code [requests [Herror [Hrequests Hstep]]]]
    Hvalid Hsafe Hexec.
  destruct requests; [|discriminate].
  unfold os_sched_post; Intros selected final resumed.
  match goal with H : _ /\ os_sched_c_return _ _ _ _ _ _ _ |- _ =>
    destruct H as [Hinterval Hreturn] end.
  pose proof (sem_post_sched_return_preserves_validity external critical sg context
    checkpoint selected resumed final Hvalid Hsafe Hinterval Hreturn) as Hfinal.
  assert (Hcall : sem_del_call_program external critical sg context pe opt before (0, 0) final).
  { assert (Hpair : (0, 0) = (0, encode_os_err_code code)) by (f_equal; exact Herror).
    rewrite Hpair; eapply sem_del_call_protected_return with
      (mask := mask) (saved := saved) (entry := entry) (current := current)
      (observed := observed) (eid := eid) (requests := true) (checkpoint := checkpoint);
      try eassumption.
    exists selected, resumed; split; assumption. }
  pose proof (sem_del_call_safe_return _ _ _ _ _ _ Hcall Hexec) as HexecFinal.
  unfold sem_del_call_post; Exists final resumed 0.
  unfold sem_post_return_resources; entailer!.
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold;
    apply derivable1s_coq_prop_r; tauto].
Qed.

(** Structural normalization retains the arbitrary heap owned by a pure
    assertion as TT; it does not erase resources or unfold an OS owner. *)
Lemma sem_del_assertion_normalize_pure : forall (A : Prop),
  coq_prop A --||-- coq_prop A && TT.
Proof. intros; split; entailer!. Qed.

Lemma sem_del_assertion_normalize_leaf : forall P : Assertion,
  P --||-- coq_prop True && P.
Proof. intros; split; entailer!. Qed.

Lemma sem_del_assertion_normalize_sepcon : forall (P Q S T : Assertion) (A B : Prop),
  P --||-- coq_prop A && S -> Q --||-- coq_prop B && T ->
  P ** Q --||-- coq_prop (and A B) && (S ** T).
Proof. intros P Q S T A B HP HQ; rewrite HP, HQ; split; entailer!. Qed.

Lemma sem_del_assertion_normalize_andp : forall (P Q S T : Assertion) (A B : Prop),
  P --||-- coq_prop A && S -> Q --||-- coq_prop B && T ->
  P && Q --||-- coq_prop (and A B) && (S && T).
Proof. intros P Q S T A B HP HQ; rewrite HP, HQ; split; entailer!. Qed.

Ltac sem_del_split_explicit_pure_spatial :=
  let rec norm term k :=
    lazymatch term with
    | coq_prop ?A => k A constr:(TT) constr:(sem_del_assertion_normalize_pure A)
    | ?P ** ?Q =>
        norm P ltac:(fun A S HP =>
          norm Q ltac:(fun B T HQ =>
            k constr:(and A B) constr:(S ** T)
              constr:(sem_del_assertion_normalize_sepcon P Q S T A B HP HQ)))
    | ?P && ?Q =>
        norm P ltac:(fun A S HP =>
          norm Q ltac:(fun B T HQ =>
            k constr:(and A B) constr:(S && T)
              constr:(sem_del_assertion_normalize_andp P Q S T A B HP HQ)))
    | _ => k constr:(True) term constr:(sem_del_assertion_normalize_leaf term)
    end in
  lazymatch goal with |- ?P |-- ?Q =>
    norm P ltac:(fun A S HP =>
      norm Q ltac:(fun B T HQ =>
        eapply derivable1_trans; [exact (proj1 HP)|];
        eapply derivable1_trans; [|exact (proj2 HQ)];
        apply coq_prop_andp_left;
        let facts := fresh "Hfacts" in intro facts;
        let rec flatten h :=
          lazymatch type of h with
          | and _ _ =>
              let h1 := fresh "Hatom" in let h2 := fresh "Hatoms" in
              destruct h as [h1 h2]; flatten h1; flatten h2
          | True => clear h
          | _ => idtac
          end in flatten facts;
        repeat rewrite truep_andp_left_equiv;
        repeat rewrite truep_andp_right_equiv;
        apply split_pure_and_spatial_goals))
  end.

Lemma sem_del_wake_split_full : forall sg entry eid current,
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM -> sem_post_group entry current <> 0 ->
  event_object_layout_prop sg eid ->
  UCOS2_inv sg entry ** unmap_table_rep sg |-- EX tid, EX old,
    coq_prop (event_task_rdy_entry sg entry.(TskState) eid current tid old) &&
    (event_task_rdy_pre sg entry.(TskState) eid current tid old 1 2
      (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
      (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
     sem_post_wake_frame sg entry eid tid).
Proof.
  intros sg entry eid current Hvalid Hlookup Htype Hnonempty Hlayout.
  pose proof Hvalid as [Hprofile [Htasks [_ [Hevents _]]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hkind : event_type_to_pend_type current.(eventType) = Some PendSem)
    by (rewrite Htype; reflexivity).
  destruct current.(waitList) as [|tid tail] eqn:Hlist;
    [contradiction Hnonempty; unfold sem_post_group; rewrite Hlist; reflexivity|].
  destruct (event_wake_head sg entry eid current tid tail PendSem 0 PendAbort
    Hvalid Hlookup Hkind Hlist) as [old [Hold [Hstep [Hafter Hlast]]]].
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  assert (Hentry : event_task_rdy_entry sg entry.(TskState) eid current tid old).
  { unfold event_task_rdy_entry; split; [exact Hsg|]; split; [exact Hlayout|].
    split; [exact Hmulti|]; split; [exact Htasks|]; split; [exact (Hentries eid current Hlookup)|].
    split; [rewrite Hlist; reflexivity|exact Hold]. }
  rewrite UCOS2_inv_open_task_storage_sched_event; Intros.
  sep_apply_l_atomic (sem_post_task_storage_split sg entry.(TskState) tid old Hmulti Hprofiling Hold).
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState)
    eid current Hlookup).
  unfold sched_raw_rep; rewrite sched_rows_array_equiv.
  Exists tid old; unfold event_task_rdy_pre, sem_post_wake_frame, used_event_rep.
  entailer!; unfold sched_row_values; reflexivity.
Qed.

Lemma sem_del_wake_merge_full : forall sg entry eid current tid old priority,
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid current tid old ->
  event_task_rdy_post sg entry.(TskState) eid current tid old 0 1 2
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
  sem_post_wake_frame sg entry eid tid |-- EX after,
    coq_prop (sem_del_wake_result sg eid entry after priority) &&
    (UCOS2_inv sg after ** unmap_table_rep sg).
Proof.
  intros sg entry eid current tid old priority Hvalid Hlookup Htype Hentry.
  pose proof Hentry as [Hsg [Hlayout [Hmulti [Htasks [Hwait [Hhead Hold]]]]]].
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof (event_task_rdy_selection sg entry.(TskState) eid current tid old Hentry)
    as [_ [_ [_ [Hprio _]]]].
  assert (Hkind : event_type_to_pend_type current.(eventType) = Some PendSem)
    by (rewrite Htype; reflexivity).
  destruct current.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (event_wake_head sg entry eid current tid tail PendSem 0 PendAbort
    Hvalid Hlookup Hkind Hlist) as [found [Hfound [Hstep [Hafter Hlast]]]].
  assert (found = old) by congruence; subst found.
  unfold event_task_rdy_post, sem_post_wake_frame; Intros.
  assert (Hreturned : priority = old.(curPrio)) by tauto; subst priority.
  rewrite (event_task_rdy_typed_image_eq sg old 0 1 2 PendSem PendAbort eq_refl eq_refl).
  rewrite (event_task_rdy_scheduler_group_eq sg entry.(TskState) entry.(SchedState) tid old _ Hold).
  rewrite (event_task_rdy_scheduler_rows_eq sg entry.(TskState) entry.(SchedState) tid old _ Hold Hprio).
  sep_apply_l_atomic (sem_post_task_storage_merge sg entry.(TskState) tid
    (task_event_wake_single old PendSem 0 PendAbort) Hmulti Hprofiling).
  fold (used_event_rep sg entry.(TskState) eid
    (event_set_wait_list current (remove_Z_eqb tid current.(waitList)))).
  sep_apply_l_atomic (event_raw_rep_merge_updated_eid sg entry.(TskState) entry.(EventState) eid
    (event_set_wait_list current (remove_Z_eqb tid current.(waitList)))).
  rewrite <- sched_rows_array_equiv.
  rewrite <- (sched_wake_by_status_physical_rep_eq sg entry.(TskState) entry.(SchedState) tid
    (task_status_clear_wait (encode_task_status old.(stat)) 1)).
  assert (Hstatus : task_status_clear_wait (encode_task_status old.(stat)) 1 =
    encode_task_status (task_event_wake_single old PendSem 0 PendAbort).(stat)).
  { change (task_status_clear_wait (encode_task_status old.(stat)) 1 =
      encode_task_status (task_clear_pending_status old.(stat) PendSem)).
    rewrite task_clear_pending_status_encoding; reflexivity. }
  rewrite Hstatus.
  assert (Hindex : forall s, sched_raw_rep sg entry.(TskState) s =
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) tid
      (task_event_wake_single old PendSem 0 PendAbort)) s).
  { intro s; apply sched_raw_rep_priority_ext; intros slot Hin.
    simpl; destruct (Z.eqb slot tid) eqn:E; [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  set (woken_sched := sched_wake_by_status sg entry.(TskState) entry.(SchedState) tid
    (encode_task_status (task_event_wake_single old PendSem 0 PendAbort).(stat))).
  assert (Hsched :
    sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp woken_sched.(readyList) entry.(TskState) **
    sched_rows_rep sg entry.(TskState) woken_sched.(readyList) [0;1;2;3;4;5;6;7] **
    sched_physical_rep sg woken_sched |--
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) tid
      (task_event_wake_single old PendSem 0 PendAbort)) woken_sched).
  { rewrite <- Hindex; unfold sched_raw_rep; reflexivity. }
  sep_apply_l_atomic Hsched.
  pose proof (UCOS2_inv_merge_event_wake sg entry eid current tid old PendSem 0 PendAbort
    Hvalid Hlookup ltac:(rewrite Hlist; left; reflexivity) Hold Hkind) as Hmerge.
  cbn zeta in Hmerge.
  cbn [event_wake_state replace_SchedS replace_EventS replace_TskS
    TskState SchedState EventState] in Hmerge.
  fold woken_sched in Hmerge.
  sep_apply_l_atomic Hmerge.
  Exists (event_wake_state sg entry eid current tid old PendSem 0 PendAbort).
  unfold sem_del_wake_result; entailer!.
Qed.
