(** Ordinary Pend helpers: the 114 checked statements and proofs follow. *)
Require Export Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_c_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_task_return_c_case_lib.
Require Export Ucos2Verify.VC.code.flag.spec.flag_pend_sched_entry_spec.

Module PendManualHelpers.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import PrimitiveComponent PendPhaseCandidate SelectedCallerPhaseComponent
  SchedulerPhaseCandidate SchedulerCalleePhaseComponent.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma flag_pend_selected_caller_save_output_source_open :
  forall environment critical local active sg caller original mask before before_heap saved,
  SelectedCallerPhaseComponent.flag_pend_selected_caller_save_output
    environment critical local active sg caller original mask before before_heap saved |--
  EX returned_caller returned acquired next_local,
    coq_prop (PendPhaseCandidate.flag_pend_caller_save_observation environment critical sg
      caller original returned_caller returned mask saved before acquired /\ interrupt_saved_value mask saved /\
      flag_pend_call_source_observations environment sg caller original before returned acquired) &&
    flag_pend_caller_restore_input environment critical next_local active sg
      returned_caller returned saved acquired acquired.
Proof.
  intros environment critical local active sg caller original mask before before_heap saved heap Houtput.
  destruct (CompletedCallerOpen.flag_pend_selected_caller_save_output_open
    environment critical local active sg caller original mask before before_heap saved heap Houtput)
    as [returned_caller [returned [acquired [next_local [[Hobs [Hsaved Hendpoint]] Howned]]]]].
  exists returned_caller, returned, acquired, next_local; split; [|exact Howned].
  split; [exact Hobs|]. split; [exact Hsaved|].
  destruct caller; [|exact I].
  destruct Hendpoint as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  split; [exact Hready|]. split; [exact Hidle|]. split; [exact Hnonidle|].
  split; [exact Hnormal|]. intro Horigin.
  eapply flag_pend_normal_return_control; [exact Hnormal|exact (Hcontrol Horigin)].
Qed.

Lemma flag_pend_selected_caller_restore_output_source_open :
  forall environment critical local active sg caller original saved acquired released before_heap,
  SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output
    environment critical local active sg caller original saved acquired released before_heap |--
  EX returned_caller returned current next_local,
    coq_prop (PendPhaseCandidate.flag_pend_caller_restore_observation environment critical sg
      caller original returned_caller returned released current /\
      flag_pend_call_source_observations environment sg caller original released returned current) &&
    flag_pend_caller_save_input environment critical next_local active sg
      returned_caller returned (armv7a_irq_fiq_mask saved) current.
Proof.
  intros environment critical local active sg caller original saved acquired released before_heap heap Houtput.
  destruct (CompletedCallerOpen.flag_pend_selected_caller_restore_output_open
    environment critical local active sg caller original saved acquired released before_heap heap Houtput)
    as [returned_caller [returned [current [next_local [[Hobs Hendpoint] Howned]]]]].
  exists returned_caller, returned, current, next_local; split; [|exact Howned].
  split; [exact Hobs|].
  destruct caller; [|exact I].
  destruct Hendpoint as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  split; [exact Hready|]. split; [exact Hidle|]. split; [exact Hnonidle|].
  split; [exact Hnormal|]. intro Horigin.
  eapply flag_pend_normal_return_control; [exact Hnormal|exact (Hcontrol Horigin)].
Qed.

Lemma flag_pend_group_type_in_range__saved_mode_join : forall sg state i image,
  UCOS2_state_inv sg state -> flag_pend_group_lookup state i image ->
  0 <= flag_pend_group_type image < 256.
Proof.
  intros sg state i image Hstate Himage.
  assert (Hflag : valid_flag_configuration sg state.(FlagState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hstate; tauto. }
  unfold flag_pend_group_lookup in Himage.
  unfold valid_flag_configuration in Hflag.
  destruct (cfgFlagEnabled (osKernelConfig sg)).
  - destruct Hflag as [Hpartition [Hdomain [Hvalid [Hused [Hfree Hnodes]]]]].
    assert (Hi : 0 <= i < cfgMaxFlags (osKernelConfig sg)).
    { apply (proj1 (Hdomain i)); exists image; exact Himage. }
    destruct (in_dec Z.eq_dec i (flagFree (FlagState state))) as [Hin | Hnot].
    + apply in_split in Hin; destruct Hin as [pre [rest Heq]].
      destruct (Hfree pre i rest Heq) as [current [Hlookup [Htype Hhead]]].
      rewrite Himage in Hlookup; injection Hlookup as <-.
      unfold flag_pend_group_type; lia.
    + destruct Hpartition as [_ [_ Hpartition]].
      destruct (proj2 (Hpartition i) (conj Hi Hnot)) as [group Hget].
      destruct (Hused i group Hget) as [_ [_ [_ [current [Hlookup [Htype Hrest]]]]]].
      rewrite Himage in Hlookup; injection Hlookup as <-.
      unfold flag_pend_group_type; lia.
  - rewrite Hflag in Himage; discriminate.
Qed.

Lemma flag_pend_mode_parameters_from_c_tests__saved_mode_join : forall original normalized consumed,
  0 <= original < 256 ->
  ((Z.land original 128 = 0 /\ normalized = original /\ consumed = 0) \/
   (Z.land original 128 <> 0 /\ normalized = Z.land original 127 /\ consumed = 1)) ->
  flag_pend_mode_parameters original normalized consumed.
Proof.
  intros original normalized consumed Hrange Hbranch.
  assert (Hmask : Z.land original 255 = original).
  { change 255 with (Z.ones 8).
    rewrite Z.land_ones by lia; apply Z.mod_small; exact Hrange. }
  destruct Hbranch as [[Hbit [-> ->]] | [Hbit [-> ->]]].
  - assert (Hlow : Z.land original 127 = original).
    { change 255 with (Z.lor 127 128) in Hmask.
      rewrite Z.land_lor_distr_r, Hbit, Z.lor_0_r in Hmask; exact Hmask. }
    unfold flag_pend_mode_parameters; rewrite Hlow, Hbit; split; reflexivity.
  - unfold flag_pend_mode_parameters.
    rewrite (proj2 (Z.eqb_neq _ _) Hbit); split; reflexivity.
Qed.

Lemma flag_pend_mode_source_checkpoint__source_mode_set :
  forall environment critical sg caller call mask i pgrp requested original_mode
    delay before X entered_caller entered saved acquired normalized consumed,
  flag_pend_public_entry environment critical sg caller call mask i pgrp
    requested original_mode delay before X ->
  flag_pend_caller_saved_prefix environment critical sg caller call mask before
    i pgrp entered_caller entered saved acquired ->
  flag_pend_mode_parameters original_mode normalized consumed ->
  0 <= normalized <= 3 ->
  flag_pend_valid_mode original_mode /\
  task_tcb_init_stack_same_call entered call /\
  task_tcb_init_stack_source_preserved call before acquired.
Proof.
  intros environment critical sg caller call mask i pgrp requested original_mode
    delay before X entered_caller entered saved acquired normalized consumed
    Hentry Hprefix Hparameters Hrange.
  destruct Hparameters as [Hnormalized Hconsume].
  assert (Hmode : flag_pend_valid_mode original_mode).
  { unfold flag_pend_valid_mode; lia. }
  destruct Hentry as [_ [_ [_ [_ [_ [Hsource _]]]]]].
  destruct Hprefix as [Hpgrp [Hints [Hlocks
    [[observed [Hlookup Htype]] [Hsave Hsaved]]]]].
  split; [exact Hmode|].
  destruct caller as [actual | view key].
  - destruct entered_caller as [next | next_view next_key].
    + cbn [flag_pend_caller_save_observation] in Hsave.
      destruct Hsave as [_ [_ [_ [Hsame Hpreserved]]]].
      exact (conj Hsame Hpreserved).
    + cbn [flag_pend_caller_save_observation] in Hsave; contradiction.
  - cbn [flag_pend_caller_source] in Hsource.
    destruct Hsource as [_ Hinvalid].
    exfalso; exact (Hinvalid Hpgrp Hints Hlocks observed Hlookup Htype Hmode).
Qed.

Lemma flag_pend_update_ready_preserves_validity__immediate_set :
  forall sg s tid old ready,
  UCOS2_state_inv sg s ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_state_inv sg
    (flag_pend_update_task s tid (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros sg s tid old ready
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags Hmodules]]]]]]]] Hold.
  destruct Hmodules as [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]].
  assert (HreferencesAfter : Ucos2Verify.lib.kernel_names.kernel_names_valid sg
    (flag_pend_update_task s tid (flag_pend_task_set_ready_flags old ready))).
  { eapply Ucos2Verify.lib.kernel_names.kernel_names_valid_replace_task; [exact Hreferences|].
    eapply task_update_name_references; [exact Hold|reflexivity]. }
  assert (HstacksAfter : parked_stacks_consistent
    (glob_task_set_usedtask s.(TskState) tid
      (flag_pend_task_set_ready_flags old ready))
    s.(TskState).(parkedTaskStacks)).
  { eapply Ucos2Verify.lib.task_stack.parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  split; [exact Hprofile|]. split.
  - eapply task_update_preserves_in_range; try eassumption; reflexivity.
  - split.
    + eapply sched_update_task_preserves_in_range;
        [exact Hsched|exact Hold|reflexivity|reflexivity].
    + split.
      * eapply Ucos2Verify.lib.event.event_update_task_preserves_in_range;
          [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hevents].
        intros kind Hphase; exact Hphase.
      * split.
        -- destruct Hcross as [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Hinit]]]]]].
           split.
           ++ eapply Ucos2Verify.lib.cross_module_invariants.task_mutex_priotbl_consistency_update_task;
                [exact Hold|reflexivity|exact Htable].
           ++ split; [eapply Ucos2Verify.lib.mutex.mutex_owner_snapshot_update_task; eassumption|].
              split.
              ** eapply Ucos2Verify.lib.event_wait.event_wait_object_update_task;
                   [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hwait].
                 intros kind Hphase; exact Hphase.
              ** split; [exact Hprotocol|]. split; [exact Hunique|]. split; [|exact Hinit].
                 eapply Ucos2Verify.lib.cross_module_invariants.task_flag_waiter_consistency_update_task;
                   [exact Hold|reflexivity|reflexivity|reflexivity|reflexivity| | |exact Hflag];
                   intros H; exact H.
        -- split.
           ++ intro Hrunning; eapply task_update_preserves_idle_tail;
                [exact Hold|reflexivity|apply Hidle; exact Hrunning].
           ++ split.
              ** apply task_reserved_bits_clear_update_task;
                   [exact Hstatus|exact (Hstatus tid old Hold)].
              ** split; [exact Hflags|]. split; [exact Hmemory|]. split; [exact Htimer|].
                 split; [exact Hstats|]. split; [exact Hcontrol|]. split; [exact Hnames|].
                 split; [exact HreferencesAfter|]. split; [exact HstacksAfter|exact Hpending].
Qed.

Lemma flag_pend_ready_flags_layout__immediate_set : forall sg old ready,
  task_layout_image sg (flag_pend_task_set_ready_flags old ready) =
  tcb_layout_write (task_layout_image sg old) (TCBCommonField TCBFlagsRdy) (Some ready).
Proof.
  intros; apply functional_extensionality; intros [field| | | | | | | ]; try reflexivity.
  destruct field; reflexivity.
Qed.

Lemma flag_pend_live_image__immediate_set : forall sg state i image,
  valid_flag_state sg state ->
  state.(flagImages) i = Some image -> image.(flagImageType) = 5 ->
  exists group, state.(flagUsed) i = Some group.
Proof.
  intros sg state i image [Hpool [Hdomain [Himages [Hused [Hfree Hnodes]]]]] Himage Htype.
  destruct Hpool as [Hnodup [Hfreerange Hpartition]].
  apply (proj2 (Hpartition i)); split.
  - apply (proj1 (Hdomain i)); eauto.
  - intro Hin; apply in_split in Hin; destruct Hin as [pre [rest Hlist]].
    destruct (Hfree pre i rest Hlist) as [v [Hv [Hty Hhead]]].
    rewrite Himage in Hv; inversion Hv; subst v; congruence.
Qed.

Lemma flag_pend_pool_bits_preserves_validity__immediate_set :
  forall sg state i image bits,
  UCOS2_state_inv sg state -> sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  state.(FlagState).(flagImages) i = Some image -> image.(flagImageType) = 5 ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  UCOS2_state_inv sg (replace_FlagS (flag_pend_pool_set_bits state.(FlagState) i image bits) state).
Proof.
  intros sg state i image bits Hinv Hen Himage Htype Hbits.
  assert (Hflag : valid_flag_state sg state.(FlagState)).
  { destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [Hflag _]]]]]]]].
    unfold valid_flag_configuration in Hflag; rewrite Hen in Hflag; exact Hflag. }
  destruct (flag_pend_live_image__immediate_set sg state.(FlagState) i image
    Hflag Himage Htype) as [group Hgroup].
  assert (Epool : flag_pend_pool_set_bits state.(FlagState) i image bits =
    flag_replace_bits state.(FlagState) i group image bits).
  { unfold flag_pend_pool_set_bits, flag_replace_bits; rewrite Hgroup; reflexivity. }
  rewrite Epool.
  assert (Hnext : valid_flag_configuration sg
    (flag_replace_bits state.(FlagState) i group image bits)).
  { unfold valid_flag_configuration; rewrite Hen.
    eapply flag_replace_bits_preserves_validity; eauto. }
  assert (Hnames : Ucos2Verify.lib.kernel_names.kernel_names_valid sg
    (replace_FlagS (flag_replace_bits state.(FlagState) i group image bits) state)).
  { apply Ucos2Verify.lib.kernel_names.kernel_names_valid_replace_flag.
    - exact (UCOS2_state_inv_names_valid _ _ Hinv).
    - intros name [id [node [Hlookup Hname]]].
      unfold flag_replace_bits in Hlookup; cbn [flagUsed] in Hlookup.
      unfold kernel_map_set in Hlookup; destruct (Z.eq_dec id i) as [->|Hne].
      + inversion Hlookup; subst node; exists i, group; split; assumption.
      + exists id, node; split; assumption. }
  assert (Hcross : Ucos2Verify.lib.cross_module_invariants.cross_module_consistency sg
    (replace_FlagS (flag_replace_bits state.(FlagState) i group image bits) state)).
  { apply Ucos2Verify.lib.cross_module_invariants.cross_module_consistency_flag_nodes_frame.
    - reflexivity.
    - destruct Hinv as [_ [_ [_ [_ [Hcross _]]]]]; exact Hcross. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *.
  cbn [replace_FlagS TskState SchedState FlagState EventState IntrState MemoryState
    TimerState StatsState ControlState NameState] in *.
  tauto.
Qed.

Lemma flag_pend_ready_flags_event_rep_eq__immediate_set :
  forall sg tasks tid old ready events,
  tasks.(inUsedTaskStates) tid = Some old ->
  Ucos2Verify.lib.event.event_raw_rep sg tasks events =
  Ucos2Verify.lib.event.event_raw_rep sg
    (glob_task_set_usedtask tasks tid (flag_pend_task_set_ready_flags old ready)) events.
Proof.
  intros sg tasks tid old ready events Hold.
  apply Ucos2Verify.lib.event.event_raw_rep_change_task_index.
  intros eid event Hevent.
  assert (Henc : forall ids,
    Ucos2Verify.lib.event.encode_event_wait_grp ids tasks =
      Ucos2Verify.lib.event.encode_event_wait_grp ids
        (glob_task_set_usedtask tasks tid (flag_pend_task_set_ready_flags old ready)) /\
    forall row, Ucos2Verify.lib.event.encode_event_wait_tbl_at_or ids tasks row =
      Ucos2Verify.lib.event.encode_event_wait_tbl_at_or ids
        (glob_task_set_usedtask tasks tid (flag_pend_task_set_ready_flags old ready)) row).
  { intro ids; induction ids as [|head tail [Hgrp Htbl]].
    all: unfold Ucos2Verify.lib.event.encode_event_wait_tbl_at_or in *.
    - split; reflexivity.
    - cbn [Ucos2Verify.lib.event.encode_event_wait_grp
        Ucos2Verify.lib.event.encode_event_wait_tbl_at_or map fold_right].
      unfold glob_task_set_usedtask; cbn [inUsedTaskStates].
      destruct (Z.eqb head tid) eqn:E.
      + apply Z.eqb_eq in E; subst head; rewrite Hold; cbn [flag_pend_task_set_ready_flags curPrio].
        split; [rewrite Hgrp|intro row; rewrite Htbl]; reflexivity.
      + destruct (inUsedTaskStates tasks head); split;
          [rewrite Hgrp|intro row; rewrite Htbl|rewrite Hgrp|intro row; rewrite Htbl]; reflexivity. }
  apply Henc.
Qed.

Lemma flag_pend_ready_flags_live_sp_iff__immediate_set :
  forall tasks tid old ready key sp,
  tasks.(inUsedTaskStates) tid = Some old ->
  (task_stack_live_sp tasks key sp <->
   task_stack_live_sp
    (glob_task_set_usedtask tasks tid (flag_pend_task_set_ready_flags old ready)) key sp).
Proof.
  intros tasks tid old ready key sp Hold.
  unfold task_stack_live_sp, glob_task_set_usedtask; cbn [inUsedTaskStates].
  destruct (Z.eqb (fst key) tid) eqn:E.
  - apply Z.eqb_eq in E; rewrite E, Hold; split; intros H node Hnode Hgen; inversion Hnode; subst node.
    + apply (H old eq_refl Hgen).
    + apply (H (flag_pend_task_set_ready_flags old ready) eq_refl Hgen).
  - reflexivity.
Qed.

Lemma flag_pend_ready_flags_capsules__immediate_set :
  forall environment local state tid old ready,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  os_sched_fields_capsules environment local state |--
  os_sched_fields_capsules environment local
    (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros environment local state tid old ready Hold.
  unfold os_sched_fields_capsules, flag_pend_update_task.
  cbn [replace_TskS TskState glob_task_set_usedtask parkedTaskStacks].
  unfold store_parked_continuations, store_map.
  Intros keys; Exists keys; entailer!.
  clear H H0.
  induction keys as [|key keys IH].
  - cbn [map iter_sepcon]; entailer!.
  - cbn [map iter_sepcon].
    destruct (parkedTaskStacks (TskState state) key) as [payload|].
    all: match goal with
    | |- iter_sepcon (?a :: ?xs) |-- iter_sepcon (?b :: ?ys) =>
      change (iter_sepcon ([a] ++ xs) |-- iter_sepcon ([b] ++ ys));
      rewrite (derivable1_sepcon_iter_sepcon2 [a] xs);
      rewrite <- (derivable1_sepcon_iter_sepcon1 [b] ys)
    end.
    all: match goal with
    | |- iter_sepcon [?a] ** ?xs |-- iter_sepcon [?b] ** ?ys =>
      change ((emp ** a) ** xs |-- (emp ** b) ** ys)
    end.
    + assert (Hentry :
        kernel_saved_continuation_entry (task_stack_call_continuations environment)
          (TskState state) local key payload |--
        kernel_saved_continuation_entry (task_stack_call_continuations environment)
          (glob_task_set_usedtask (TskState state) tid
            (flag_pend_task_set_ready_flags old ready)) local key payload).
      { unfold kernel_saved_continuation_entry.
        Intros descriptor; Exists descriptor; entailer!.
        apply (proj1 (flag_pend_ready_flags_live_sp_iff__immediate_set
          _ _ _ _ _ _ Hold)); tauto. }
      sep_apply Hentry. sep_apply IH. entailer!.
    + sep_apply IH. entailer!.
Qed.

Lemma flag_pend_ready_flags_coverage__immediate_set :
  forall tasks tid old ready active,
  tasks.(inUsedTaskStates) tid = Some old ->
  task_stack_live_coverage tasks active ->
  task_stack_live_coverage
    (glob_task_set_usedtask tasks tid (flag_pend_task_set_ready_flags old ready)) active.
Proof.
  intros tasks tid old ready active Hold Hcoverage.
  eapply task_stack_live_coverage_used_map_frame with (before:=tasks); [|reflexivity|exact Hcoverage].
  intros slot node Hnode.
  unfold glob_task_set_usedtask in Hnode; cbn [inUsedTaskStates] in Hnode.
  destruct (Z.eqb slot tid) eqn:E.
  - apply Z.eqb_eq in E; subst slot; inversion Hnode; subst node; exists old; split; [exact Hold|reflexivity].
  - exists node; auto.
Qed.

Lemma flag_pend_word_land_eq__immediate_set : forall bits mask,
  0 <= bits < 65536 ->
  Z.land bits (mask mod 65536) = (Z.land bits mask) mod 65536.
Proof.
  intros bits mask Hbits.
  change 65536 with (2^16).
  rewrite <- (Z.land_ones mask 16) by lia.
  rewrite Z.land_assoc.
  rewrite Z.land_ones by lia; reflexivity.
Qed.

Lemma flag_pend_consume_testbit__immediate_set : forall word,
  Z.eqb (Z.land word 128) 0 = negb (Z.testbit word 7).
Proof.
  intros word.
  assert (E : Z.land word 128 = if Z.testbit word 7 then 128 else 0).
  { apply Z.bits_inj; intro bit.
    rewrite Z.land_spec.
    change 128 with (2^7).
    rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eq_dec bit 7) as [->|Hne].
    - rewrite Z.eqb_refl; destruct (Z.testbit word 7); reflexivity.
    - assert (Eb : (Z.eqb 7 bit) = false) by (apply Z.eqb_neq; lia).
      rewrite Eb, Bool.andb_false_r.
      destruct (Z.testbit word 7); [rewrite Z.pow2_bits_false by lia|rewrite Z.bits_0]; reflexivity. }
  rewrite E; destruct (Z.testbit word 7); reflexivity.
Qed.

Lemma flag_pend_mode_consume__immediate_set : forall word mode consume,
  flag_pend_mode_parameters word mode consume ->
  unsigned_last_nbits consume 32 = consume /\
  (consume = 1 <-> Z.testbit word 7 = true) /\
  (consume = 0 <-> Z.testbit word 7 = false).
Proof.
  intros word mode consume [_ ->].
  rewrite flag_pend_consume_testbit__immediate_set.
  destruct (Z.testbit word 7); cbn; repeat split; intros; try congruence; reflexivity.
Qed.

Lemma flag_pend_ready_flags_registration__immediate_set :
  forall original call state tid old ready flags,
  flag_active_fresh_registration original call state ->
  flag_pend_current_ready call state ->
  flag_pend_current_binding state tid old ->
  flag_active_fresh_registration original call
    (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros original call state tid old ready flags [task [Hfields Hnode]]
    [current [[Hlookup [Hcurrent Hrest]] Hgen]] [Htid Hold].
  destruct Hfields as [Hsame [Horigin [Htask [Htaskgen [Hactive Hclear]]]]].
  destruct Hsame as [Hcallinv [Hcallorigin Hcallstack]].
  assert (Eslot : tid = (os_sched_call_stack original).(stackLeaseSlot)).
  { rewrite Hcallstack in Hcurrent; congruence. }
  assert (Etask : task = old) by (rewrite <- Eslot in Htask; congruence).
  subst task tid.
  exists (flag_pend_task_set_ready_flags old ready); split; [|exact Hnode].
  apply flag_active_task_fields_update with (task:=old); [|reflexivity|exact Hclear].
  unfold flag_active_task_fields, flag_active_event_clear, task_tcb_init_stack_same_call in *;
    cbn [replace_FlagS TskState]; tauto.
Qed.

Lemma flag_pend_ready_flags_stage__immediate_set :
  forall call state tid old ready flags,
  flag_pend_task_stage call state ->
  flag_pend_current_binding state tid old ->
  flag_pend_task_stage call
    (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros call state tid old ready flags
    [Horigin [Hrunning [Hpark [task [[Hlookup [Hcur [Hprio [Hin Hready]]]] [Hgen Hclean]]]]]]
    [Htid Hold].
  assert (Eslot : tid = (os_sched_call_stack call).(stackLeaseSlot)) by congruence.
  assert (Eold : task = old) by (rewrite <- Eslot in Hlookup; congruence).
  subst task tid.
  split; [exact Horigin|]. split; [exact Hrunning|]. split; [exact Hpark|].
  exists (flag_pend_task_set_ready_flags old ready).
  split.
  - split.
    + unfold flag_pend_update_task; cbn [replace_TskS TskState replace_FlagS].
      unfold glob_task_set_usedtask; cbn [inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    + split; [exact Hcur|]. split; [exact Hprio|]. split; [exact Hin|exact Hready].
  - split; [exact Hgen|exact Hclean].
Qed.

Lemma flag_pend_current_fields_merge__immediate_set :
  forall sg state tid old i image ready flags bits,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  sg.(osKernelConfig).(cfgFlagBits) = 16 ->
  flag_pend_current_binding state tid old ->
  flags.(flagImages) i = Some (flag_image_set_bits image bits) ->
  (forall j, j <> i -> state.(FlagState).(flagImages) j = flags.(flagImages) j) ->
  state.(FlagState).(flagWaitNodes) = flags.(flagWaitNodes) ->
  state.(FlagState).(flagFree) = flags.(flagFree) ->
  UCOS2_state_inv sg
    (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)) ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBFlagsRdy # UShort |-> ready **
  flag_pend_group_current_frame sg state tid old i image **
  flag_pool_addr sg i # UChar |-> image.(flagImageType) **
  (flag_pool_addr sg i + 8) # UShort |-> bits |--
  UCOS2_fields_inv sg
    (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros sg state tid old i image ready flags bits Hen Hwidth [Hcur Hold]
    Himage Hother Hnodes Hfree Hinv.
  assert (Hresidual :
    UCOS2_raw_rep_missing_task_storage_sched_flag sg state =
    UCOS2_raw_rep_missing_task_storage_sched_flag sg
      (flag_pend_update_task (replace_FlagS flags state) tid
        (flag_pend_task_set_ready_flags old ready))).
  { unfold UCOS2_raw_rep_missing_task_storage_sched_flag.
    cbn [flag_pend_update_task replace_TskS replace_FlagS TskState IntrState EventState
      TickState MemoryState TimerState StatsState ControlState NameState
      glob_task_set_usedtask parkedTaskStacks].
    rewrite (flag_pend_ready_flags_event_rep_eq__immediate_set
      sg state.(TskState) tid old ready state.(EventState) Hold).
    reflexivity. }
  pose proof (UCOS2_fields_inv_merge_updated_task_storage_sched_flag sg state
    (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)) Hinv Hresidual) as Hmerge.
  sep_apply_r_atomic Hmerge.
  cbn [flag_pend_update_task replace_TskS replace_FlagS TskState SchedState FlagState].
  unfold flag_fields_configured_rep; rewrite Hen.
  pose proof (task_public_storage_merge_updated_field sg state.(TskState) tid old
    (flag_pend_task_set_ready_flags old ready) (TCBCommonField TCBFlagsRdy) (Some ready)
    (tcb_configured_common_field_in _ _ TCBFlagsRdy)
    (flag_pend_ready_flags_layout__immediate_set sg old ready)) as Htask.
  cbn [tcb_layout_cell tcb_cell] in Htask.
  unfold flag_pend_group_current_frame.
  sepcon_assoc_change.
  sep_apply_l_atomic Htask.
  assert (Hflag : flag_pool_addr sg i # UChar |-> image.(flagImageType) **
    (flag_pool_addr sg i + 8) # UShort |-> bits **
    flag_pend_group_without_type_bits sg.(osKernelConfig) (flag_pool_addr sg i) image **
    flag_fields_raw_rep_without_group sg state.(FlagState) i |--
    flag_fields_raw_rep sg flags).
  { sep_apply_r_atomic (flag_fields_raw_rep_merge_updated_group
      sg state.(FlagState) flags i (flag_image_set_bits image bits)
      Himage Hother Hnodes Hfree).
    unfold flag_group_rep, flag_pend_group_without_type_bits, flag_image_set_bits.
    cbn [flagImageType flagImageBits flagImagePadding flagImageHead flagImageName].
    unfold flag_word_rep; rewrite Hwidth; cbn [Z.eqb Pos.eqb]; entailer!. }
  sep_apply Hflag.
  assert (Hsched : sched_raw_rep sg state.(TskState) state.(SchedState) =
    sched_raw_rep sg
      (glob_task_set_usedtask state.(TskState) tid (flag_pend_task_set_ready_flags old ready))
      state.(SchedState)).
  { apply sched_raw_rep_priority_ext; intros slot Hin.
    symmetry; apply glob_task_set_usedtask_observation with (old:=old); [exact Hold|reflexivity]. }
  rewrite <- Hsched.
  unfold flag_pend_sched_without_current, sched_raw_rep, sched_physical_rep.
  rewrite Hcur; cbn [encode_task_link]; entailer!.
Qed.

Lemma flag_pend_acquired_task_stage__immediate_set :
  forall environment critical sg caller call mask i pgrp requested mode timeout before X
    entered_caller entered saved acquired,
  flag_pend_public_entry environment critical sg caller call mask i pgrp requested mode timeout before X ->
  flag_pend_caller_saved_prefix environment critical sg caller call mask before i pgrp
    entered_caller entered saved acquired ->
  flag_pend_call_source_observations environment sg caller call before entered acquired ->
  flag_pend_first_registration mode call before entered acquired ->
  flag_pend_valid_mode mode ->
  entered_caller = FlagPendTaskCaller entered /\
  flag_pend_saved_prefix environment critical sg call mask before i pgrp entered saved acquired /\
  flag_pend_task_stage entered acquired.
Proof.
  exact PendSchedulerSeedAdapter.flag_pend_acquired_task_stage_with_counters.
Qed.

Lemma flag_pend_ready_fields_restore__immediate_set :
  forall environment critical local sg call saved state tid old i image ready flags bits,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  sg.(osKernelConfig).(cfgFlagBits) = 16 ->
  flag_pend_current_binding state tid old ->
  flags.(flagImages) i = Some (flag_image_set_bits image bits) ->
  (forall j, j <> i -> state.(FlagState).(flagImages) j = flags.(flagImages) j) ->
  state.(FlagState).(flagWaitNodes) = flags.(flagWaitNodes) ->
  state.(FlagState).(flagFree) = flags.(flagFree) ->
  UCOS2_state_inv sg
    (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)) ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBFlagsRdy # UShort |-> ready **
  flag_pend_group_current_frame sg state tid old i image **
  flag_pend_caller_masked_control environment local critical sg (FlagPendTaskCaller call)
    call saved state state **
  flag_pool_addr sg i # UChar |-> image.(flagImageType) **
  (flag_pool_addr sg i + 8) # UShort |-> bits |--
  flag_pend_caller_fields_restore_input environment critical local sg (FlagPendTaskCaller call)
    call saved state
    (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros environment critical local sg call saved state tid old i image ready flags bits
    Hen Hwidth Hbinding Himage Hother Hnodes Hfree Hinv.
  sepcon_assoc_change.
  sep_apply_l_atomic (flag_pend_current_fields_merge__immediate_set sg state tid old i image
    ready flags bits Hen Hwidth Hbinding Himage Hother Hnodes Hfree Hinv).
  unfold flag_pend_caller_masked_control, flag_pend_masked_control.
  Intros.
  pose proof (flag_pend_ready_flags_coverage__immediate_set
    state.(TskState) tid old ready (task_stack_call_active_key call) (proj2 Hbinding) H0) as Hcoverage.
  sep_apply (flag_pend_ready_flags_capsules__immediate_set
    environment local state tid old ready (proj2 Hbinding)).
  unfold flag_pend_caller_fields_restore_input, flag_pend_caller_restore_input,
    flag_pend_active_restore_input, os_sched_fields_restore_input.
  entailer!.
Qed.

Lemma flag_pend_ready_flags_preserves_state_inv__immediate_clear_1 :
  forall sg state tid old ready,
  UCOS2_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_state_inv sg
    (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros sg state tid old ready
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags
      [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]]]]]]]]] Hold.
  unfold flag_pend_update_task.
  assert (Hreferences_after : Ucos2Verify.lib.kernel_names.kernel_names_valid sg
    (replace_TskS (glob_task_set_usedtask state.(TskState) tid
      (flag_pend_task_set_ready_flags old ready)) state)).
  { eapply Ucos2Verify.lib.kernel_names.kernel_names_valid_replace_task; [exact Hreferences|].
    eapply task_update_name_references; [exact Hold|reflexivity]. }
  assert (Hstacks_after : Ucos2Verify.lib.task_stack.parked_stacks_consistent
    (glob_task_set_usedtask state.(TskState) tid
      (flag_pend_task_set_ready_flags old ready)) state.(TskState).(parkedTaskStacks)).
  { eapply Ucos2Verify.lib.task_stack.parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready.
  split; [exact Hprofile|]. split.
  - eapply task_update_preserves_in_range; try exact Htasks; try exact Hold; reflexivity.
  - split.
    + eapply sched_update_task_preserves_in_range;
        [exact Hsched|exact Hold|reflexivity|reflexivity].
    + split.
      * eapply Ucos2Verify.lib.event.event_update_task_preserves_in_range;
          [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hevents].
        intros kind Hphase; exact Hphase.
      * split.
        -- destruct Hcross as [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Hinit]]]]]].
           split.
           ++ eapply Ucos2Verify.lib.cross_module_invariants.task_mutex_priotbl_consistency_update_task;
                [exact Hold|reflexivity|exact Htable].
           ++ split; [eapply Ucos2Verify.lib.mutex.mutex_owner_snapshot_update_task; eassumption|].
              split.
              ** eapply Ucos2Verify.lib.event_wait.event_wait_object_update_task;
                   [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hwait].
                 intros kind Hphase; exact Hphase.
              ** split; [exact Hprotocol|]. split; [exact Hunique|]. split; [|exact Hinit].
                 eapply Ucos2Verify.lib.cross_module_invariants.task_flag_waiter_consistency_update_task;
                   [exact Hold|reflexivity|reflexivity|reflexivity|reflexivity| | |exact Hflag];
                   intros H; exact H.
        -- split.
           ++ intro Hrunning; eapply task_update_preserves_idle_tail;
                [exact Hold|reflexivity|apply Hidle; exact Hrunning].
           ++ split.
              ** apply task_reserved_bits_clear_update_task;
                   [exact Hstatus|exact (Hstatus tid old Hold)].
              ** split; [exact Hflags|]. split; [exact Hmemory|]. split; [exact Htimer|].
                 split; [exact Hstats|]. split; [exact Hcontrol|]. split; [exact Hnames|].
                 split; [exact Hreferences_after|]. split; [exact Hstacks_after|exact Hpending].
Qed.

Lemma flag_pend_ready_flags_layout_eq__immediate_clear_1 : forall sg old ready,
  task_layout_image sg (flag_pend_task_set_ready_flags old ready) =
    tcb_layout_write (task_layout_image sg old) (TCBCommonField TCBFlagsRdy) (Some ready).
Proof.
  intros; apply Coq.Logic.FunctionalExtensionality.functional_extensionality.
  intros field; destruct field as [field| | | | | | | ]; [destruct field|..]; reflexivity.
Qed.

Lemma flag_pend_ready_flags_residual_eq__immediate_clear_1 : forall sg state tid old ready,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_raw_rep_missing_task_storage_sched_flag sg
    (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready)) =
  UCOS2_raw_rep_missing_task_storage_sched_flag sg state.
Proof.
  intros sg state tid old ready Hold.
  assert (Hevents : Ucos2Verify.lib.event.event_raw_rep sg state.(TskState) state.(EventState) =
    Ucos2Verify.lib.event.event_raw_rep sg
      (glob_task_set_usedtask state.(TskState) tid (flag_pend_task_set_ready_flags old ready)) state.(EventState)).
  { apply Ucos2Verify.lib.event.event_raw_rep_change_task_index.
    apply Ucos2Verify.lib.event.event_wait_priority_agreement_encodes.
    eapply Ucos2Verify.lib.event.glob_task_set_usedtask_preserves_event_priority_agreement;
      [exact Hold|reflexivity]. }
  unfold UCOS2_raw_rep_missing_task_storage_sched_flag, flag_pend_update_task; simpl.
  rewrite <- Hevents; reflexivity.
Qed.

Lemma flag_pend_ready_flags_merge_current__immediate_clear_1 : forall sg state tid old i image ready,
  flag_pend_current_binding state tid old ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBFlagsRdy # UShort |-> ready **
  flag_pend_group_current_frame sg state tid old i image |--
  flag_pend_group_frame sg
    (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready)) i image.
Proof.
  intros sg state tid old i image ready [Hcur Hold].
  pose proof (task_public_storage_merge_updated_field sg state.(TskState) tid old
    (flag_pend_task_set_ready_flags old ready) (TCBCommonField TCBFlagsRdy) (Some ready)
    (tcb_configured_common_field_in _ _ TCBFlagsRdy)
    (flag_pend_ready_flags_layout_eq__immediate_clear_1 sg old ready)) as Htask.
  cbn [tcb_layout_cell tcb_cell] in Htask.
  assert (Hsched : sched_raw_rep sg state.(TskState) state.(SchedState) =
    sched_raw_rep sg (glob_task_set_usedtask state.(TskState) tid
      (flag_pend_task_set_ready_flags old ready)) state.(SchedState)).
  { apply sched_raw_rep_priority_ext; intros slot Hin; symmetry.
    eapply glob_task_set_usedtask_observation; [exact Hold|reflexivity]. }
  unfold flag_pend_group_current_frame, flag_pend_group_frame.
  rewrite (flag_pend_flag_frame_split_task_sched sg
    (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready))).
  rewrite flag_pend_ready_flags_residual_eq__immediate_clear_1 by exact Hold.
  cbn [flag_pend_update_task replace_TskS TskState FlagState SchedState].
  rewrite <- Hsched.
  sepcon_assoc_change; sep_apply_l_atomic Htask.
  unfold sched_raw_rep, sched_physical_rep, flag_pend_sched_without_current.
  rewrite Hcur; cbn [encode_task_link]; entailer!.
Qed.

Lemma flag_pend_pool_set_bits_preserves_state_inv__immediate_clear_1 :
  forall sg state i image bits,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  UCOS2_state_inv sg state -> state.(FlagState).(flagImages) i = Some image ->
  image.(flagImageType) = 5 ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  UCOS2_state_inv sg (replace_FlagS (flag_pend_pool_set_bits state.(FlagState) i image bits) state).
Proof.
  intros sg state i image bits Hen Hvalid Himage Htype Hbits.
  pose proof Hvalid as [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags
    [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hroots [Hstacks Hpending]]]]]]]]]]]]]]].
  unfold valid_flag_configuration in Hflags; rewrite Hen in Hflags.
  assert (Hlive : exists group, state.(FlagState).(flagUsed) i = Some group).
  { destruct Hflags as [[Hfree_range [Hnd Hpartition]] [Hdomain [Himages [Hused [Hfree Hnodes]]]]].
    assert (Hrange : 0 <= i < sg.(osKernelConfig).(cfgMaxFlags))
      by (apply (proj1 (Hdomain i)); eauto).
    destruct (state.(FlagState).(flagUsed) i) as [group|] eqn:Hg; [eauto|].
    assert (Hin : In i state.(FlagState).(flagFree)).
    { destruct (in_dec Z.eq_dec i state.(FlagState).(flagFree)); [assumption|].
      destruct (proj2 (Hpartition i) (conj Hrange n)) as [g H]; congruence. }
    apply in_split in Hin; destruct Hin as [pre [rest Hlist]].
    destruct (Hfree pre i rest Hlist) as [found [Hfound [Hfree_type Hhead]]].
    rewrite Himage in Hfound; inversion Hfound; subst; congruence. }
  destruct Hlive as [group Hgroup].
  assert (Hflag_after : valid_flag_configuration sg (flag_pend_pool_set_bits state.(FlagState) i image bits)).
  { unfold valid_flag_configuration; rewrite Hen.
    unfold flag_pend_pool_set_bits; rewrite Hgroup.
    change (valid_flag_state sg (flag_replace_bits state.(FlagState) i group image bits)).
    eapply flag_replace_bits_preserves_validity; eassumption. }
  assert (Hcross_after : Ucos2Verify.lib.cross_module_invariants.cross_module_consistency sg
    (replace_FlagS (flag_pend_pool_set_bits state.(FlagState) i image bits) state)).
  { apply Ucos2Verify.lib.cross_module_invariants.cross_module_consistency_flag_nodes_frame;
      [reflexivity|exact Hcross]. }
  assert (Hroots_after : Ucos2Verify.lib.kernel_names.kernel_names_valid sg
    (replace_FlagS (flag_pend_pool_set_bits state.(FlagState) i image bits) state)).
  { eapply Ucos2Verify.lib.kernel_names.kernel_names_valid_frame;
      [exact Hroots|reflexivity|..]; try (intros; assumption).
    intros p [j [found [Hfound Hname]]].
    change ((match state.(FlagState).(flagUsed) i with
      | Some group => Ucos2Verify.lib.kernel_resources.kernel_map_set state.(FlagState).(flagUsed) i
        (Some (flag_group_set_bits group bits))
      | None => state.(FlagState).(flagUsed) end) j = Some found) in Hfound.
    rewrite Hgroup in Hfound.
    unfold Ucos2Verify.lib.kernel_resources.kernel_map_set in Hfound.
    destruct (Z.eq_dec j i) as [->|Hne].
    - inversion Hfound; subst found; exists i, group; auto.
    - exists j, found; auto. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *; cbn.
  repeat first [assumption | split].
Qed.

Lemma flag_pend_pool_set_bits_merge__immediate_clear_1 : forall sg state i image bits,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg state -> flag_pend_group_lookup state i image ->
  image.(flagImageType) = 5 -> flag_word_in_range sg.(osKernelConfig) bits ->
  flag_pool_addr sg i # UChar |-> image.(flagImageType) **
  (flag_pool_addr sg i + 8) # UShort |-> bits **
  flag_pend_group_frame sg state i image |--
  UCOS2_fields_inv sg (replace_FlagS (flag_pend_pool_set_bits state.(FlagState) i image bits) state).
Proof.
  intros sg state i image bits Hconfig Hvalid Himage Htype Hbits.
  assert (Hgroup :
    flag_pool_addr sg i # UChar |-> image.(flagImageType) **
    (flag_pool_addr sg i + 8) # UShort |-> bits **
    flag_pend_group_without_type_bits sg.(osKernelConfig) (flag_pool_addr sg i) image |--
    flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) (flag_image_set_bits image bits)).
  { unfold flag_group_rep, flag_pend_group_without_type_bits, flag_word_rep, flag_image_set_bits;
    rewrite Hconfig; cbn [selected_kernel_configuration cfgFlagBits flagImageType flagImagePadding flagImageHead flagImageBits flagImageName]; entailer!. }
  unfold flag_pend_group_frame; sep_apply_l_atomic Hgroup.
  sep_apply_l_atomic (flag_fields_raw_rep_merge_updated_group sg state.(FlagState)
    (flag_pend_pool_set_bits state.(FlagState) i image bits) i (flag_image_set_bits image bits)
    (flag_pend_pool_set_bits_image _ _ _ _)
    ltac:(intros j Hne; cbn [flag_pend_pool_set_bits flagImages];
      symmetry; apply Ucos2Verify.lib.kernel_resources.kernel_map_set_other; exact Hne)
    eq_refl eq_refl).
  assert (Hupdated : UCOS2_state_inv sg
    (replace_FlagS (flag_pend_pool_set_bits state.(FlagState) i image bits) state)).
  { eapply flag_pend_pool_set_bits_preserves_state_inv__immediate_clear_1;
      [rewrite Hconfig; reflexivity|exact Hvalid|exact Himage|exact Htype|exact Hbits]. }
  unfold UCOS2_fields_inv, UCOS2_fields_raw_rep, flag_fields_configured_rep.
  rewrite UCOS2_raw_rep_missing_flag_replace_eq.
  cbn [replace_FlagS FlagState].
  rewrite Hconfig; cbn [selected_kernel_configuration cfgFlagEnabled]; entailer!.
Qed.

Lemma flag_pend_ready_flags_preserves_task_stage__immediate_clear_1 : forall call state tid old ready,
  flag_pend_current_binding state tid old -> flag_pend_task_stage call state ->
  flag_pend_task_stage call (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros call state tid old ready [Hcur Hold]
    [Horigin [Hrunning [Havailable [node [[Hnode [Hcurrent [Hprio [Hin Hready]]]] [Hgen Hclean]]]]]].
  assert (Htid : tid = call.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
  subst tid; assert (node = old) by congruence; subst node.
  unfold flag_pend_task_stage, flag_pend_update_task; cbn [replace_TskS TskState SchedState].
  split; [exact Horigin|]. split; [exact Hrunning|]. split; [exact Havailable|].
  exists (flag_pend_task_set_ready_flags old ready).
  split.
  - unfold sched_current_ready_at; cbn [glob_task_set_usedtask inUsedTaskStates].
    rewrite Z.eqb_refl; split; [reflexivity|]. exact (conj Hcurrent (conj Hprio (conj Hin Hready))).
  - exact (conj Hgen Hclean).
Qed.

Lemma flag_pend_ready_flags_preserves_first_registration__immediate_clear_1 :
  forall mode original before call state tid old ready,
  flag_pend_current_binding state tid old -> flag_pend_task_stage call state ->
  flag_pend_first_registration mode original before call state ->
  flag_pend_first_registration mode original before call
    (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros mode original before call state tid old ready [Hcur Hold] Hstage Hregistration Hmode.
  destruct (Hregistration Hmode) as [task [Hfields Hnull]].
  pose proof Hfields as [Hsame [Horigin [Htask [Hgen [Hactive Hclear]]]]].
  destruct Hsame as [Hinv [Hcall_origin Hstack]].
  pose proof (flag_pend_task_stage_current call state Hstage) as [Hcurrent Hcurrent_task].
  rewrite Hstack in Hcurrent.
  assert (Htid : tid = original.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
  subst tid; assert (task = old) by congruence; subst task.
  exists (flag_pend_task_set_ready_flags old ready); split; [|exact Hnull].
  eapply flag_active_task_fields_update with (task := old); [exact Hfields|reflexivity|exact Hclear].
Qed.

Lemma flag_pend_ready_flags_preserves_live_sp__immediate_clear_1 : forall tasks tid old ready key sp,
  tasks.(inUsedTaskStates) tid = Some old ->
  Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.task_stack_live_sp tasks key sp ->
  Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.task_stack_live_sp
    (glob_task_set_usedtask tasks tid (flag_pend_task_set_ready_flags old ready)) key sp.
Proof.
  intros tasks tid old ready key sp Hold Hlive node Hnode Hgen.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
  destruct (Z.eqb (fst key) tid) eqn:Hkey.
  - apply Z.eqb_eq in Hkey; inversion Hnode; subst node.
    apply (Hlive old); [rewrite Hkey; exact Hold|exact Hgen].
  - eapply Hlive; eassumption.
Qed.

Lemma flag_pend_ready_flags_preserves_masked_control__immediate_clear_1 :
  forall environment local critical sg call saved acquired state tid old ready,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  flag_pend_masked_control environment local critical sg call saved acquired state |--
  flag_pend_masked_control environment local critical sg call saved acquired
    (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros environment local critical sg call saved acquired state tid old ready Hold.
  unfold flag_pend_masked_control; Intros.
  assert (Hcoverage : Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.task_stack_live_coverage
    (glob_task_set_usedtask state.(TskState) tid (flag_pend_task_set_ready_flags old ready))
    (task_stack_call_active_key call)).
  { eapply Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.task_stack_live_coverage_used_map_frame
      with (before := state.(TskState)); [|reflexivity|eassumption].
    intros slot node Hnode; cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
    destruct (Z.eqb slot tid) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot; inversion Hnode; subst node; exists old; auto.
    - exists node; auto. }
  assert (Hcapsules : os_sched_fields_capsules environment local state |--
    os_sched_fields_capsules environment local
      (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready))).
  { unfold os_sched_fields_capsules, Ucos2Verify.lib.task_stack.store_parked_continuations.
    cbn [flag_pend_update_task replace_TskS TskState glob_task_set_usedtask parkedTaskStacks].
    apply TaskFieldStorage.store_map_mono; intros key payload Hpayload.
    unfold Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.kernel_saved_continuation_entry.
    Intros descriptor; Exists descriptor.
    match goal with Hfacts : _ /\ _ /\ _ /\ _ /\ _ |- _ =>
      destruct Hfacts as [Hbinding [Hkey [Hpayload_eq [Hslice Hsp]]]] end.
    pose proof (flag_pend_ready_flags_preserves_live_sp__immediate_clear_1
      state.(TskState) tid old ready key _ Hold Hsp) as Hnewsp.
    entailer!. }
  sep_apply_l_atomic Hcapsules; entailer!.
Qed.

Lemma flag_pend_clear_all_mode_parameters_cases__immediate_clear_1 : forall mode consumed,
  0 <= mode < 256 -> flag_pend_mode_parameters mode 0 consumed ->
  (mode = 0 /\ consumed = 0) \/ (mode = 128 /\ consumed = 1).
Proof.
  intros mode consumed Hrange [Hnorm Hcons].
  assert (Hmod : mode mod 128 = 0).
  { symmetry in Hnorm; change (Z.land mode (Z.ones 7) = 0) in Hnorm.
    rewrite Z.land_ones in Hnorm by lia; exact Hnorm. }
  assert (Hdiv : 0 <= mode / 128 <= 1).
  { assert (Hnonnegative : 0 <= mode / 128) by (apply Z.div_pos; lia).
    assert (Hupper : mode / 128 < 2) by (apply Z.div_lt_upper_bound; lia).
    lia. }
  pose proof (Z.div_mod mode 128 ltac:(lia)) as Heq.
  assert (Hcases : mode = 0 \/ mode = 128) by lia.
  destruct Hcases as [Hcase|Hcase]; subst mode; cbn in Hcons; subst consumed; auto.
Qed.

Lemma flag_pend_ready_flags_layout_eq__immediate_clear_2 : forall sg old ready,
  task_layout_image sg (flag_pend_task_set_ready_flags old ready) =
    tcb_layout_write (task_layout_image sg old) (TCBCommonField TCBFlagsRdy) (Some ready).
Proof.
  intros; apply functional_extensionality; intro field; destruct field; try reflexivity.
  match goal with f : TCBField |- _ => destruct f; reflexivity end.
Qed.

Lemma flag_pend_update_ready_flags_preserves_validity__immediate_clear_2 :
  forall sg state tid old ready,
  UCOS2_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_state_inv sg (flag_pend_update_task state tid
    (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros sg state tid old ready
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags
      [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hrefs [Hstacks Hpending]]]]]]]]]]]]]]] Hold.
  unfold flag_pend_update_task.
  split; [exact Hprofile|]. split.
  - eapply task_update_preserves_in_range; try exact Htasks; try exact Hold; reflexivity.
  - split.
    + eapply sched_update_task_preserves_in_range; try exact Hsched; try exact Hold; reflexivity.
    + split.
      * eapply event.event_update_task_preserves_in_range; try exact Hold; try reflexivity.
        -- intros kind Hphase; exact Hphase.
        -- exact Hevents.
      * split.
        -- destruct Hcross as [Htable [Howners [Hwait [Hprotocol [Hunique [Hflag HtimerCross]]]]]].
           split.
           ++ eapply cross_module_invariants.task_mutex_priotbl_consistency_update_task;
                [exact Hold|reflexivity|exact Htable].
           ++ split.
              ** eapply mutex.mutex_owner_snapshot_update_task; eauto.
              ** split.
                 --- eapply event_wait.event_wait_object_update_task; try exact Hold;
                       try reflexivity; [intros kind Hphase; exact Hphase|exact Hwait].
                 --- split; [exact Hprotocol|]. split; [exact Hunique|].
                     split; [|exact HtimerCross].
                     eapply cross_module_invariants.task_flag_waiter_consistency_update_task;
                       try exact Hold; try reflexivity; try exact Hflag;
                       intros Hphase; exact Hphase.
        -- split.
           ++ intro Hrunning; eapply task_update_preserves_idle_tail;
                [exact Hold|reflexivity|exact (Hidle Hrunning)].
           ++ split.
              ** apply task_reserved_bits_clear_update_task; [exact Hstatus|exact (Hstatus _ old Hold)].
              ** split; [exact Hflags|]. split; [exact Hmemory|].
                 split; [exact Htimer|]. split; [exact Hstats|].
                 split; [exact Hcontrol|]. split; [exact Hnames|]. split.
                 --- eapply kernel_names.kernel_names_valid_replace_task;
                       [exact Hrefs|eapply task_update_name_references; [exact Hold|reflexivity]].
                 --- split; [|exact Hpending].
                     eapply task_stack.parked_stacks_consistent_update_task;
                       [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks].
Qed.

Lemma flag_pend_live_group_of_image_type__immediate_clear_2 :
  forall sg flags i image,
  valid_flag_state sg flags -> flags.(flagImages) i = Some image ->
  image.(flagImageType) = 5 -> exists group, flags.(flagUsed) i = Some group.
Proof.
  intros sg flags i image [[Hnd [Hrange Hpartition]]
    [Hdomain [Himages [Hused [Hfree Hnodes]]]]] Himage Htype.
  apply (proj2 (Hpartition i)); split.
  - apply (proj1 (Hdomain i)); eauto.
  - intro Hin; apply in_split in Hin; destruct Hin as [pre [rest Heq]].
    destruct (Hfree pre i rest Heq) as [other [Hother [Hzero Hhead]]].
    rewrite Himage in Hother; inversion Hother; subst other; congruence.
Qed.

Lemma flag_pend_pool_set_bits_preserves_validity__immediate_clear_2 :
  forall sg state i image bits,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg state -> flag_pend_group_lookup state i image ->
  image.(flagImageType) = 5 -> flag_word_in_range sg.(osKernelConfig) bits ->
  UCOS2_state_inv sg (replace_FlagS
    (flag_pend_pool_set_bits state.(FlagState) i image bits) state).
Proof.
  intros sg state i image bits Hconfig
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags
      [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hrefs [Hstacks Hpending]]]]]]]]]]]]]]]
    Himage Htype Hbits.
  assert (Hflagvalid : valid_flag_state sg state.(FlagState)).
  { unfold valid_flag_configuration in Hflags; rewrite Hconfig in Hflags; exact Hflags. }
  destruct (flag_pend_live_group_of_image_type__immediate_clear_2
    sg state.(FlagState) i image Hflagvalid Himage Htype) as [group Hgroup].
  assert (Heq : flag_pend_pool_set_bits state.(FlagState) i image bits =
    flag_replace_bits state.(FlagState) i group image bits).
  { unfold flag_pend_pool_set_bits; rewrite Hgroup; reflexivity. }
  split; [exact Hprofile|]. split; [exact Htasks|].
  split; [exact Hsched|]. split; [exact Hevents|]. split.
  - apply cross_module_invariants.cross_module_consistency_flag_nodes_frame;
      [reflexivity|exact Hcross].
  - split; [exact Hidle|]. split; [exact Hstatus|]. split.
    + unfold valid_flag_configuration; rewrite Hconfig.
      rewrite Heq; eapply flag_replace_bits_preserves_validity; eassumption.
    + split; [exact Hmemory|]. split; [exact Htimer|]. split; [exact Hstats|].
      split; [exact Hcontrol|]. split; [exact Hnames|]. split.
      * eapply kernel_names.kernel_names_valid_frame; try exact Hrefs; try reflexivity;
          try (intros; assumption).
        intros name [slot [new [Hnew Hname]]].
        cbn [replace_FlagS FlagState] in Hnew.
        rewrite Heq in Hnew; cbn [flag_replace_bits flagUsed] in Hnew.
        unfold kernel_map_set in Hnew; destruct (Z.eq_dec slot i).
        -- subst slot; inversion Hnew; subst new; exists i, group; auto.
        -- exists slot, new; auto.
      * split; assumption.
Qed.

Lemma flag_pend_ready_flags_resources__immediate_clear_2 :
  forall sg state tid old i image ready,
  flag_pend_current_binding state tid old ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBFlagsRdy # UShort |-> ready **
  flag_pend_group_current_frame sg state tid old i image |--
  task_public_storage sg
    (glob_task_set_usedtask state.(TskState) tid (flag_pend_task_set_ready_flags old ready)) **
  sched_raw_rep sg
    (glob_task_set_usedtask state.(TskState) tid (flag_pend_task_set_ready_flags old ready))
    state.(SchedState) **
  flag_pend_group_without_type_bits sg.(osKernelConfig) (flag_pool_addr sg i) image **
  flag_fields_raw_rep_without_group sg state.(FlagState) i **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg state.
Proof.
  intros sg state tid old i image ready [Hcurrent Hold].
  pose proof (task_public_storage_merge_updated_field sg state.(TskState) tid old
    (flag_pend_task_set_ready_flags old ready) (TCBCommonField TCBFlagsRdy) (Some ready)
    (tcb_configured_common_field_in _ _ TCBFlagsRdy)
    (flag_pend_ready_flags_layout_eq__immediate_clear_2 sg old ready)) as Htask.
  cbn [tcb_layout_cell tcb_cell] in Htask.
  assert (Hsched : sched_raw_rep sg state.(TskState) state.(SchedState) =
    sched_raw_rep sg (glob_task_set_usedtask state.(TskState) tid
      (flag_pend_task_set_ready_flags old ready)) state.(SchedState)).
  { apply sched_raw_rep_priority_ext; intros slot Hin; symmetry.
    apply glob_task_set_usedtask_observation with (old := old); [exact Hold|reflexivity]. }
  rewrite <- Hsched.
  unfold flag_pend_group_current_frame.
  sepcon_assoc_change; sep_apply_l_atomic Htask.
  unfold sched_raw_rep, sched_physical_rep, flag_pend_sched_without_current.
  rewrite Hcurrent; cbn [encode_task_link]; entailer!.
Qed.

Lemma flag_pend_ready_flags_residual_eq__immediate_clear_2 :
  forall sg state tid old ready flags,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_raw_rep_missing_task_storage_sched_flag sg state =
  UCOS2_raw_rep_missing_task_storage_sched_flag sg
    (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros sg state tid old ready flags Hold.
  assert (Hevents : event_raw_rep sg state.(TskState) state.(EventState) =
    event_raw_rep sg (glob_task_set_usedtask state.(TskState) tid
      (flag_pend_task_set_ready_flags old ready)) state.(EventState)).
  { apply event_raw_rep_change_task_index.
    apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement;
      [exact Hold|reflexivity]. }
  unfold UCOS2_raw_rep_missing_task_storage_sched_flag, flag_pend_update_task;
    cbn [replace_FlagS replace_TskS]; rewrite Hevents; reflexivity.
Qed.

Lemma flag_pend_pool_bits_resources__immediate_clear_2 :
  forall sg flags i image bits (consume : bool),
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flags.(flagImages) i = Some image ->
  (flag_pool_addr sg i) # UChar |-> image.(flagImageType) **
  (flag_pool_addr sg i + 8) # UShort |-> (if consume then bits else image.(flagImageBits)) **
  flag_pend_group_without_type_bits sg.(osKernelConfig) (flag_pool_addr sg i) image **
  flag_fields_raw_rep_without_group sg flags i |--
  flag_fields_configured_rep sg (if consume then flag_pend_pool_set_bits flags i image bits else flags).
Proof.
  intros sg flags i image bits consume Hconfig Himage.
  destruct consume.
  - assert (Hgroup :
      (flag_pool_addr sg i) # UChar |-> image.(flagImageType) **
      (flag_pool_addr sg i + 8) # UShort |-> bits **
      flag_pend_group_without_type_bits sg.(osKernelConfig) (flag_pool_addr sg i) image |--
      flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) (flag_image_set_bits image bits)).
    { unfold flag_group_rep, flag_pend_group_without_type_bits, flag_word_rep.
      rewrite Hconfig; cbn [flag_image_set_bits flagImageType flagImageHead flagImageBits flagImagePadding flagImageName selected_kernel_configuration cfgFlagBits Z.eqb Pos.eqb]; entailer!. }
    sep_apply_l_atomic Hgroup.
    unfold flag_fields_configured_rep; rewrite (f_equal cfgFlagEnabled Hconfig).
    cbn [selected_kernel_configuration cfgFlagEnabled].
    apply flag_fields_raw_rep_merge_updated_group.
    + apply flag_pend_pool_set_bits_image.
    + intros; symmetry; apply kernel_map_set_other; assumption.
    + reflexivity.
    + reflexivity.
  - assert (Hgroup :
      (flag_pool_addr sg i) # UChar |-> image.(flagImageType) **
      (flag_pool_addr sg i + 8) # UShort |-> image.(flagImageBits) **
      flag_pend_group_without_type_bits sg.(osKernelConfig) (flag_pool_addr sg i) image |--
      flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) image).
    { unfold flag_group_rep, flag_pend_group_without_type_bits, flag_word_rep.
      rewrite Hconfig; cbn [selected_kernel_configuration cfgFlagBits Z.eqb Pos.eqb]; entailer!. }
    sep_apply_l_atomic Hgroup.
    unfold flag_fields_configured_rep; rewrite (f_equal cfgFlagEnabled Hconfig).
    cbn [selected_kernel_configuration cfgFlagEnabled].
    apply (proj2 (flag_fields_raw_rep_split_group sg flags i image Himage)).
Qed.

Lemma flag_pend_ready_flags_control__immediate_clear_2 :
  forall environment local critical sg call saved acquired state tid old ready flags,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  flag_pend_masked_control environment local critical sg call saved acquired state |--
  flag_pend_masked_control environment local critical sg call saved acquired
    (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros environment local critical sg call saved acquired state tid old ready flags Hold.
  assert (Hcoverage : task_stack_live_coverage state.(TskState) (task_stack_call_active_key call) ->
    task_stack_live_coverage (glob_task_set_usedtask state.(TskState) tid
      (flag_pend_task_set_ready_flags old ready)) (task_stack_call_active_key call)).
  { apply task_stack_live_coverage_used_map_frame; [|reflexivity].
    intros slot node Hnode; cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
    destruct (Z.eqb slot tid) eqn:E.
    - apply Z.eqb_eq in E; subst slot; inversion Hnode; subst node; exists old; auto.
    - exists node; auto. }
  assert (Hcapsules : os_sched_fields_capsules environment local state |--
    os_sched_fields_capsules environment local
      (flag_pend_update_task (replace_FlagS flags state) tid
        (flag_pend_task_set_ready_flags old ready))).
  { unfold os_sched_fields_capsules, flag_pend_update_task;
      cbn [replace_TskS replace_FlagS TskState glob_task_set_usedtask parkedTaskStacks].
    apply kernel_saved_continuation_map_reindex.
    intros key payload node Hlookup Hnode Hgen.
    cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
    destruct (Z.eqb (fst key) tid) eqn:E.
    - apply Z.eqb_eq in E; rewrite E; inversion Hnode; subst node.
      exists old; auto.
    - exists node; auto. }
  unfold flag_pend_masked_control; Intros.
  assert (Hnewcoverage := Hcoverage H).
  sep_apply_l_atomic Hcapsules; entailer!.
Qed.

Lemma flag_pend_ready_flags_preserves_stage__immediate_clear_2 :
  forall call state tid old ready flags,
  flag_pend_current_binding state tid old ->
  flag_pend_task_stage call state ->
  flag_pend_task_stage call
    (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros call state tid old ready flags [Hcur Hold]
    [Horigin [Hrunning [Habsent [node [[Hlookup [Hcurrent Hrest]] [Hgen Hclean]]]]]].
  assert (Hslot : tid = call.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
  assert (Hnode : node = old) by congruence.
  subst tid node.
  split; [exact Horigin|]. split; [exact Hrunning|]. split; [exact Habsent|].
  exists (flag_pend_task_set_ready_flags old ready).
  split; [|split; [exact Hgen|exact Hclean]].
  split; [cbn [flag_pend_update_task replace_TskS replace_FlagS TskState
    glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity|].
  split; [exact Hcurrent|exact Hrest].
Qed.

Lemma flag_pend_ready_flags_preserves_registration__immediate_clear_2 :
  forall original call state tid old ready flags,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  flag_active_fresh_registration original call state ->
  flag_active_fresh_registration original call
    (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros original call state tid old ready flags Hold
    [node [[Hsame [Horigin [Hlookup [Hgen [Hactive Hclear]]]]] Hnode]].
  pose proof (glob_task_set_usedtask_preserves_invocation_active
    state.(TskState) tid old (flag_pend_task_set_ready_flags old ready)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    Hold eq_refl Hactive) as Hnewactive.
  destruct (Z.eq_dec original.(os_sched_call_stack).(stackLeaseSlot) tid) as [Heq|Hne].
  - assert (E : node = old) by (rewrite Heq in Hlookup; congruence); subst node.
    exists (flag_pend_task_set_ready_flags old ready).
    split; [|exact Hnode].
    split; [exact Hsame|]. split; [exact Horigin|]. split.
    + cbn [flag_pend_update_task replace_TskS replace_FlagS TskState glob_task_set_usedtask inUsedTaskStates].
      rewrite Heq, Z.eqb_refl; reflexivity.
    + split; [exact Hgen|]. split; [exact Hnewactive|exact Hclear].
  - exists node; split; [|exact Hnode].
    split; [exact Hsame|]. split; [exact Horigin|]. split.
    + cbn [flag_pend_update_task replace_TskS replace_FlagS TskState glob_task_set_usedtask inUsedTaskStates].
      apply Z.eqb_neq in Hne; rewrite Hne; exact Hlookup.
    + split; [exact Hgen|]. split; [exact Hnewactive|exact Hclear].
Qed.

Lemma flag_pend_land_word_in_range__immediate_clear_2 : forall value mask,
  0 <= mask < 65536 -> 0 <= Z.land value mask < 65536.
Proof.
  intros value mask Hrange.
  assert (Hmask : Z.land mask (Z.ones 16) = mask).
  { rewrite Z.land_ones by lia; apply Z.mod_small; exact Hrange. }
  assert (Hmod : Z.land value mask mod 65536 = Z.land value mask).
  { change (Z.land value mask mod (2 ^ 16) = Z.land value mask).
    rewrite <- Z.land_ones by lia; rewrite <- Z.land_assoc, Hmask; reflexivity. }
  pose proof (Z.mod_pos_bound (Z.land value mask) 65536 ltac:(lia)) as Hbounds.
  rewrite Hmod in Hbounds; exact Hbounds.
Qed.

Lemma flag_pend_consume_bit_eq__immediate_clear_2 : forall mode,
  Z.eqb (Z.land mode 128) 0 = negb (Z.testbit mode 7).
Proof.
  intro mode.
  assert (Hbits : Z.land mode 128 = if Z.testbit mode 7 then 128 else 0).
  { apply Z.bits_inj'; intros n Hn.
    rewrite Z.land_spec.
    change 128 with (2 ^ 7).
    rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eqb 7 n) eqn:E.
    - apply Z.eqb_eq in E; subst n.
      destruct (Z.testbit mode 7); cbn; reflexivity.
    - destruct (Z.testbit mode 7); rewrite ?Z.pow2_bits_eqb, ?Z.testbit_0_l by lia;
        rewrite ?E; apply Bool.andb_false_r. }
  rewrite Hbits; destruct (Z.testbit mode 7); reflexivity.
Qed.

Lemma flag_pend_replace_flags_self__immediate_clear_2 : forall state,
  replace_FlagS state.(FlagState) state = state.
Proof. intros []; reflexivity. Qed.

Lemma flag_pend_group_current_merge_ready_flags__immediate_clear_2 :
  forall sg state tid old i image ready bits (consume : bool),
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg state ->
  flag_pend_current_binding state tid old ->
  flag_pend_group_lookup state i image ->
  image.(flagImageType) = 5 ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  let flags := if consume then flag_pend_pool_set_bits state.(FlagState) i image bits
    else state.(FlagState) in
  let post := flag_pend_update_task (replace_FlagS flags state) tid
    (flag_pend_task_set_ready_flags old ready) in
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBFlagsRdy # UShort |-> ready **
  flag_pend_group_current_frame sg state tid old i image **
  (flag_pool_addr sg i) # UChar |-> image.(flagImageType) **
  (flag_pool_addr sg i + 8) # UShort |-> (if consume then bits else image.(flagImageBits)) |--
  UCOS2_fields_inv sg post.
Proof.
  intros sg state tid old i image ready bits consume Hconfig Hvalid Hbinding Himage Htype Hbits
    flags post.
  assert (Hpost : UCOS2_state_inv sg post).
  { apply flag_pend_update_ready_flags_preserves_validity__immediate_clear_2.
    - unfold flags; destruct consume.
      + eapply flag_pend_pool_set_bits_preserves_validity__immediate_clear_2; eauto.
      + rewrite flag_pend_replace_flags_self__immediate_clear_2; exact Hvalid.
    - exact (proj2 Hbinding). }
  pose proof (flag_pend_ready_flags_resources__immediate_clear_2
    sg state tid old i image ready Hbinding) as Htask.
  pose proof (flag_pend_pool_bits_resources__immediate_clear_2
    sg state.(FlagState) i image bits consume Hconfig Himage) as Hflag.
  pose proof (UCOS2_fields_inv_merge_updated_task_storage_sched_flag sg state post Hpost
    (flag_pend_ready_flags_residual_eq__immediate_clear_2
      sg state tid old ready flags (proj2 Hbinding))) as Hmerge.
  sep_apply_l_atomic Htask; sep_apply_l_atomic Hflag.
  cbn [post flag_pend_update_task replace_TskS replace_FlagS TskState SchedState FlagState] in Hmerge.
  unfold flags in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma flag_pend_ready_flags_preserves_validity__immediate_clear_3 :
  forall sg state tid old ready,
  UCOS2_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_state_inv sg
    (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros sg state tid old ready
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags Hmodules]]]]]]]] Hold.
  destruct Hmodules as [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]].
  unfold flag_pend_update_task.
  split; [exact Hprofile|]. split.
  - eapply task_update_preserves_in_range; try eassumption; reflexivity.
  - split.
    + apply sched_update_task_preserves_in_range with (old:=old); try assumption; reflexivity.
    + split.
      * eapply event_update_task_preserves_in_range;
          [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hevents].
        intros kind Hphase; exact Hphase.
      * split.
        -- destruct Hcross as [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Hinit]]]]]].
           split.
           ++ eapply task_mutex_priotbl_consistency_update_task;
                [exact Hold|reflexivity|exact Htable].
           ++ split; [eapply Ucos2Verify.lib.mutex.mutex_owner_snapshot_update_task; eassumption|].
              split.
              ** eapply event_wait_object_update_task;
                   [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hwait].
                 intros kind Hphase; exact Hphase.
              ** split; [exact Hprotocol|]. split; [exact Hunique|]. split; [|exact Hinit].
                 eapply task_flag_waiter_consistency_update_task;
                   [exact Hold|reflexivity|reflexivity|reflexivity|reflexivity| | |exact Hflag];
                   intros H; exact H.
        -- split.
           ++ intro Hrunning; eapply task_update_preserves_idle_tail;
                [exact Hold|reflexivity|apply Hidle; exact Hrunning].
           ++ split.
              ** apply task_reserved_bits_clear_update_task;
                   [exact Hstatus|exact (Hstatus tid old Hold)].
              ** split; [exact Hflags|]. split; [exact Hmemory|]. split; [exact Htimer|].
                 split; [exact Hstats|]. split; [exact Hcontrol|]. split; [exact Hnames|].
                 split.
                 --- eapply Ucos2Verify.lib.kernel_names.kernel_names_valid_replace_task; [exact Hreferences|].
                     eapply task_update_name_references; [exact Hold|reflexivity].
                 --- split; [|exact Hpending].
                     eapply parked_stacks_consistent_update_task;
                       [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks].
Qed.

Lemma flag_pend_live_image_has_group__immediate_clear_3 :
  forall sg flags i image,
  valid_flag_state sg flags -> flags.(flagImages) i = Some image ->
  image.(flagImageType) = 5 ->
  exists group, flags.(flagUsed) i = Some group.
Proof.
  intros sg flags i image [Hpool [Hdomain [Himages [Hused [Hfree Hnodes]]]]] Himage Htype.
  destruct Hpool as [Hnd [Hfree_range Hpartition]].
  apply (proj2 (Hpartition i)); split.
  - apply (proj1 (Hdomain i)); exists image; exact Himage.
  - intro Hin; apply in_split in Hin as [pre [rest Heq]].
    destruct (Hfree pre i rest Heq) as [free_image [Hfreeimage [Hfreetype Hhead]]].
    rewrite Himage in Hfreeimage; inversion Hfreeimage; subst free_image; lia.
Qed.

Lemma flag_pend_live_bits_preserves_validity__immediate_clear_3 :
  forall sg state i image bits,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  UCOS2_state_inv sg state ->
  state.(FlagState).(flagImages) i = Some image ->
  image.(flagImageType) = 5 ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  UCOS2_state_inv sg
    (replace_FlagS (flag_pend_pool_set_bits state.(FlagState) i image bits) state).
Proof.
  intros sg state i image bits Hen
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags Hmodules]]]]]]]]
    Himage Htype Hbits.
  unfold valid_flag_configuration in Hflags; rewrite Hen in Hflags.
  destruct (flag_pend_live_image_has_group__immediate_clear_3
    sg state.(FlagState) i image Hflags Himage Htype) as [group Hgroup].
  assert (Hreplace : flag_pend_pool_set_bits state.(FlagState) i image bits =
    flag_replace_bits state.(FlagState) i group image bits).
  { unfold flag_pend_pool_set_bits, flag_replace_bits; rewrite Hgroup; reflexivity. }
  rewrite Hreplace.
  split; [exact Hprofile|]. split; [exact Htasks|]. split; [exact Hsched|].
  split; [exact Hevents|]. split.
  - apply cross_module_consistency_flag_nodes_frame; [reflexivity|exact Hcross].
  - split; [exact Hidle|]. split; [exact Hstatus|]. split.
    + unfold valid_flag_configuration; rewrite Hen.
      eapply flag_replace_bits_preserves_validity; eassumption.
    + destruct Hmodules as [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences Hrest]]]]]].
      split; [exact Hmemory|]. split; [exact Htimer|]. split; [exact Hstats|].
      split; [exact Hcontrol|]. split; [exact Hnames|]. split; [|exact Hrest].
      eapply Ucos2Verify.lib.kernel_names.kernel_names_valid_replace_flag; [exact Hreferences|].
      intros name [j [found [Hlookup Hname]]].
      cbn [flag_replace_bits flagUsed] in Hlookup.
      unfold kernel_map_set in Hlookup; destruct (Z.eq_dec j i) as [->|Hne].
      * inversion Hlookup; subst found. exists i, group; split; [exact Hgroup|exact Hname].
      * exists j, found; split; assumption.
Qed.

Lemma flag_pend_ready_flags_layout_eq__immediate_clear_3 : forall sg old ready,
  task_layout_image sg (flag_pend_task_set_ready_flags old ready) =
  tcb_layout_write (task_layout_image sg old) (TCBCommonField TCBFlagsRdy) (Some ready).
Proof.
  intros; apply functional_extensionality; intros [field| | | | | | |]; try reflexivity;
  destruct field; reflexivity.
Qed.

Lemma flag_pend_ready_flags_stack_metadata__immediate_clear_3 : forall tasks tid old ready,
  tasks.(inUsedTaskStates) tid = Some old ->
  forall slot node,
  (glob_task_set_usedtask tasks tid (flag_pend_task_set_ready_flags old ready)).(inUsedTaskStates) slot = Some node ->
  exists prior, tasks.(inUsedTaskStates) slot = Some prior /\
    node.(taskGeneration) = prior.(taskGeneration) /\ node.(tcbStkPtr) = prior.(tcbStkPtr).
Proof.
  intros tasks tid old ready Hold slot node Hnode.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
  destruct (Z.eqb slot tid) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot; inversion Hnode; subst node.
    exists old; auto.
  - exists node; auto.
Qed.

Lemma flag_pend_ready_flags_control_transport__immediate_clear_3 :
  forall environment local critical sg caller call saved acquired state flags tid old ready,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  flag_pend_caller_masked_control environment local critical sg caller call saved acquired state |--
  flag_pend_caller_masked_control environment local critical sg caller call saved acquired
    (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros environment local critical sg caller call saved acquired state flags tid old ready Hold.
  assert (Hcoverage : forall active,
    task_stack_live_coverage state.(TskState) active ->
    task_stack_live_coverage
      (glob_task_set_usedtask state.(TskState) tid (flag_pend_task_set_ready_flags old ready)) active).
  { intros active Hcover; eapply task_stack_live_coverage_used_map_frame with (before := state.(TskState));
      [|reflexivity|exact Hcover].
    intros slot node Hnode.
    destruct (flag_pend_ready_flags_stack_metadata__immediate_clear_3 _ _ _ _ Hold _ _ Hnode)
      as [prior [Hprior [Hgen Hsp]]]; exists prior; auto. }
  assert (Hcapsules : os_sched_fields_capsules environment local state |--
    os_sched_fields_capsules environment local
      (flag_pend_update_task (replace_FlagS flags state) tid
        (flag_pend_task_set_ready_flags old ready))).
  { unfold os_sched_fields_capsules.
    apply kernel_saved_continuation_map_reindex.
    intros key payload node Hlookup Hnode Hgen.
    destruct (flag_pend_ready_flags_stack_metadata__immediate_clear_3 _ _ _ _ Hold _ _ Hnode)
      as [prior [Hprior [Hg Hsp]]]; exists prior; auto. }
  destruct caller; unfold flag_pend_caller_masked_control, flag_pend_masked_control;
    Intros; sep_apply_l_atomic Hcapsules; entailer!; apply Hcoverage; assumption.
Qed.

Lemma flag_pend_ready_flags_stage_preserved__immediate_clear_3 :
  forall call state flags tid old ready,
  flag_pend_current_binding state tid old ->
  flag_pend_task_stage call state ->
  flag_pend_task_stage call
    (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros call state flags tid old ready [Hcurrent Hold]
    [Horigin [Hrunning [Habsent [node [[Hnode [Hcur Hready]] [Hgen Hclean]]]]]].
  assert (Hslot : tid = call.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
  subst tid; rewrite Hold in Hnode; inversion Hnode; subst node.
  split; [exact Horigin|]. split; [exact Hrunning|]. split; [exact Habsent|].
  exists (flag_pend_task_set_ready_flags old ready).
  split.
  - split.
    + cbn [flag_pend_update_task replace_FlagS replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
      rewrite Z.eqb_refl; reflexivity.
    + split; [exact Hcur|exact Hready].
  - split; [exact Hgen|exact Hclean].
Qed.

Lemma flag_pend_ready_flags_registration_preserved__immediate_clear_3 :
  forall original call state flags tid old ready,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  flag_active_fresh_registration original call state ->
  flag_active_fresh_registration original call
    (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros original call state flags tid old ready Hold
    [node [[Hsame [Horigin [Hlookup [Hgen [Hactive Hclear]]]]] Hnode]].
  destruct (Z.eq_dec original.(os_sched_call_stack).(stackLeaseSlot) tid) as [Hslot|Hslot].
  - rewrite Hslot, Hold in Hlookup; inversion Hlookup; subst node.
    exists (flag_pend_task_set_ready_flags old ready); split; [|exact Hnode].
    split; [exact Hsame|]. split; [exact Horigin|]. split.
    + cbn [flag_pend_update_task replace_FlagS replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
      rewrite Hslot, Z.eqb_refl; reflexivity.
    + split; [exact Hgen|]. split; [|exact Hclear].
      eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hold|reflexivity|exact Hactive].
  - exists node; split; [|exact Hnode]. split; [exact Hsame|]. split; [exact Horigin|]. split.
    + cbn [flag_pend_update_task replace_FlagS replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
      rewrite (proj2 (Z.eqb_neq _ _) Hslot); exact Hlookup.
    + split; [exact Hgen|]. split; [|exact Hclear].
      eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hold|reflexivity|exact Hactive].
Qed.

Lemma flag_pend_ready_flags_merge_group__immediate_clear_3 :
  forall sg state tid old i image flags new_image ready,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_pend_current_binding state tid old ->
  flags.(flagImages) i = Some new_image ->
  (forall j, j <> i -> state.(FlagState).(flagImages) j = flags.(flagImages) j) ->
  state.(FlagState).(flagWaitNodes) = flags.(flagWaitNodes) ->
  state.(FlagState).(flagFree) = flags.(flagFree) ->
  flag_pend_group_without_type_bits sg.(osKernelConfig) (flag_pool_addr sg i) image =
    flag_pend_group_without_type_bits sg.(osKernelConfig) (flag_pool_addr sg i) new_image ->
  UCOS2_state_inv sg (flag_pend_update_task (replace_FlagS flags state) tid
      (flag_pend_task_set_ready_flags old ready)) ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBFlagsRdy # UShort |-> ready **
  flag_pend_group_current_frame sg state tid old i image **
  flag_pool_addr sg i # UChar |-> new_image.(flagImageType) **
  (flag_pool_addr sg i + 8) # UShort |-> new_image.(flagImageBits) |--
  UCOS2_fields_inv sg (flag_pend_update_task (replace_FlagS flags state) tid
    (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros sg state tid old i image flags new_image ready Hconfig [Hcurrent Hold]
    Hnew Himages Hnodes Hfree Himageframe Hvalid.
  set (tasks := glob_task_set_usedtask state.(TskState) tid (flag_pend_task_set_ready_flags old ready)).
  assert (Htask : tcb_field_address (task_slot_addr sg tid) TCBFlagsRdy # UShort |-> ready **
    task_public_storage_without_field sg state.(TskState) tid old (TCBCommonField TCBFlagsRdy) |--
    task_public_storage sg tasks).
  { apply (task_public_storage_merge_updated_field sg state.(TskState) tid old
      (flag_pend_task_set_ready_flags old ready) (TCBCommonField TCBFlagsRdy) (Some ready)).
    - apply tcb_configured_common_field_in.
    - apply flag_pend_ready_flags_layout_eq__immediate_clear_3. }
  assert (Hsched : sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
    flag_pend_sched_without_current sg state.(TskState) state.(SchedState) |--
    sched_raw_rep sg tasks state.(SchedState)).
  { assert (Hpriority : forall slot, In slot state.(SchedState).(readyList) ->
      option_map curPrio (state.(TskState).(inUsedTaskStates) slot) =
      option_map curPrio (tasks.(inUsedTaskStates) slot)).
    { intros; symmetry; apply (glob_task_set_usedtask_observation Z curPrio _ _ old);
        [exact Hold|reflexivity]. }
    rewrite <- (sched_raw_rep_priority_ext sg _ _ _ Hpriority).
    unfold sched_raw_rep, sched_physical_rep, flag_pend_sched_without_current.
    rewrite Hcurrent; cbn [encode_task_link]; entailer!. }
  assert (Hgroup : flag_pool_addr sg i # UChar |-> new_image.(flagImageType) **
    (flag_pool_addr sg i + 8) # UShort |-> new_image.(flagImageBits) **
    flag_pend_group_without_type_bits sg.(osKernelConfig) (flag_pool_addr sg i) image |--
    flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) new_image).
  { rewrite Himageframe; unfold flag_group_rep, flag_pend_group_without_type_bits, flag_word_rep.
    rewrite Hconfig; cbn [selected_kernel_configuration cfgFlagBits]; entailer!. }
  assert (Hflag : flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) new_image **
    flag_fields_raw_rep_without_group sg state.(FlagState) i |-- flag_fields_configured_rep sg flags).
  { assert (Hen : sg.(osKernelConfig).(cfgFlagEnabled) = true) by (rewrite Hconfig; reflexivity).
    unfold flag_fields_configured_rep; rewrite Hen.
    apply flag_fields_raw_rep_merge_updated_group; assumption. }
  assert (Hresidual : UCOS2_raw_rep_missing_task_storage_sched_flag sg state =
    UCOS2_raw_rep_missing_task_storage_sched_flag sg
      (flag_pend_update_task (replace_FlagS flags state) tid (flag_pend_task_set_ready_flags old ready))).
  { assert (Hevents : event_raw_rep sg state.(TskState) state.(EventState) =
      event_raw_rep sg tasks state.(EventState)).
    { apply event_raw_rep_change_task_index.
      apply event_wait_priority_agreement_encodes.
      eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
    unfold UCOS2_raw_rep_missing_task_storage_sched_flag.
    cbn [flag_pend_update_task replace_FlagS replace_TskS TskState EventState IntrState TickState MemoryState TimerState StatsState ControlState NameState].
    fold tasks; rewrite Hevents; reflexivity. }
  unfold flag_pend_group_current_frame; sepcon_assoc_change.
  sep_apply_l_atomic Htask.
  sep_apply_l_atomic Hsched.
  sep_apply_l_atomic Hgroup.
  sep_apply_l_atomic Hflag.
  pose proof (UCOS2_fields_inv_merge_updated_task_storage_sched_flag sg state
    (flag_pend_update_task (replace_FlagS flags state) tid (flag_pend_task_set_ready_flags old ready))
    Hvalid Hresidual) as Hmerge.
  cbn [flag_pend_update_task replace_TskS replace_FlagS TskState SchedState FlagState] in Hmerge.
  fold tasks in Hmerge.
  sep_apply_r_atomic Hmerge; entailer!.
Qed.

Lemma flag_pend_consume_mask_testbit_eq__immediate_clear_3 : forall original,
  Z.land original 128 = if Z.testbit original 7 then 128 else 0.
Proof.
  intros original.
  replace 128 with (2 ^ 7) by reflexivity.
  apply Z.bits_inj'; intros n Hn.
  rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.eq_dec 7 n) as [<-|Hne].
  - rewrite Z.eqb_refl; destruct (Z.testbit original 7); reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) Hne), Bool.andb_false_r.
    destruct (Z.testbit original 7).
    + rewrite Z.pow2_bits_eqb by lia; rewrite (proj2 (Z.eqb_neq _ _) Hne); reflexivity.
    + rewrite Z.testbit_0_l; reflexivity.
Qed.

Lemma flag_pend_mode_consume_testbit_eq__immediate_clear_3 : forall original normalized consumed,
  flag_pend_mode_parameters original normalized consumed ->
  consumed = if Z.testbit original 7 then 1 else 0.
Proof.
  intros original normalized consumed [_ ->].
  rewrite flag_pend_consume_mask_testbit_eq__immediate_clear_3.
  destruct (Z.testbit original 7); reflexivity.
Qed.

Lemma flag_pend_ready_flags_preserves_validity__immediate_clear_4 : forall sg state tid old ready,
  UCOS2_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_state_inv sg (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros sg state tid old ready
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags Hmodules]]]]]]]] Hold.
  destruct Hmodules as [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]].
  unfold flag_pend_update_task.
  assert (HreferencesAfter : kernel_names.kernel_names_valid sg
    (replace_TskS (glob_task_set_usedtask state.(TskState) tid
      (flag_pend_task_set_ready_flags old ready)) state)).
  { eapply kernel_names.kernel_names_valid_replace_task; [exact Hreferences|].
    eapply task_update_name_references; [exact Hold|reflexivity]. }
  assert (HstacksAfter : parked_stacks_consistent
    (glob_task_set_usedtask state.(TskState) tid (flag_pend_task_set_ready_flags old ready))
    state.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  split; [exact Hprofile|]. split.
  - eapply task_update_preserves_in_range; try eassumption; reflexivity.
  - split.
    + eapply sched_update_task_preserves_in_range; [exact Hsched|exact Hold|reflexivity|reflexivity].
    + split.
      * eapply event_update_task_preserves_in_range;
          [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hevents].
        intros kind Hphase; exact Hphase.
      * split.
        -- destruct Hcross as [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Hinit]]]]]].
           split.
           ++ eapply cross_module_invariants.task_mutex_priotbl_consistency_update_task;
                [exact Hold|reflexivity|exact Htable].
           ++ split; [eapply mutex.mutex_owner_snapshot_update_task; eassumption|].
              split.
              ** eapply event_wait_object_update_task;
                   [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hwait].
                 intros kind Hphase; exact Hphase.
              ** split; [exact Hprotocol|]. split; [exact Hunique|]. split; [|exact Hinit].
                 eapply cross_module_invariants.task_flag_waiter_consistency_update_task;
                   [exact Hold|reflexivity|reflexivity|reflexivity|reflexivity| | |exact Hflag];
                   intros H; exact H.
        -- split.
           ++ intro Hrunning; eapply task_update_preserves_idle_tail;
                [exact Hold|reflexivity|apply Hidle; exact Hrunning].
           ++ split.
              ** apply task_reserved_bits_clear_update_task;
                   [exact Hstatus|exact (Hstatus tid old Hold)].
              ** split; [exact Hflags|]. split; [exact Hmemory|]. split; [exact Htimer|].
                 split; [exact Hstats|]. split; [exact Hcontrol|]. split; [exact Hnames|].
                 split; [exact HreferencesAfter|]. split; [exact HstacksAfter|exact Hpending].
Qed.

Lemma flag_pend_ready_flags_layout_image__immediate_clear_4 : forall sg old ready,
  task_layout_image sg (flag_pend_task_set_ready_flags old ready) =
    tcb_layout_write (task_layout_image sg old) (TCBCommonField TCBFlagsRdy) (Some ready).
Proof.
  intros sg old ready.
  apply functional_extensionality; intro field.
  destruct field as [common | | | | | | |]; try reflexivity.
  destruct common; reflexivity.
Qed.

Lemma flag_pend_ready_flags_preserves_task_stage__immediate_clear_4 : forall call state tid old ready,
  flag_pend_current_binding state tid old ->
  flag_pend_task_stage call state ->
  flag_pend_task_stage call (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros call state tid old ready [Hcurrent Hold]
    [Horigin [Hrunning [Havailable [node [[Hnode [Hcur [Hprio [Hin Hready]]]] [Hgen Hclean]]]]]].
  assert (Hslot : call.(os_sched_call_stack).(stackLeaseSlot) = tid) by congruence.
  rewrite Hslot in Hnode; assert (node = old) by congruence; subst node.
  unfold flag_pend_task_stage; split; [exact Horigin|].
  split; [exact Hrunning|]. split; [exact Havailable|].
  exists (flag_pend_task_set_ready_flags old ready); split.
  - unfold sched_current_ready_at; cbn [flag_pend_update_task replace_TskS TskState SchedState].
    split; [cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Hslot,Z.eqb_refl; reflexivity|].
    split; [exact Hcur|]. split; [exact Hprio|]. split; [exact Hin|exact Hready].
  - split; [exact Hgen|exact Hclean].
Qed.

Lemma flag_pend_ready_flags_preserves_fresh_registration__immediate_clear_4 :
  forall original call state tid old ready,
  flag_pend_current_binding state tid old -> flag_pend_task_stage call state ->
  flag_active_fresh_registration original call state ->
  flag_active_fresh_registration original call
    (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros original call state tid old ready [Hcurrent Hold]
    [Horigin [Hrun [Havail [node [[Hnode [Hcur Hrest]] Hclean]]]]]
    [registered [Hfields Hflag]].
  pose proof Hfields as [Hsame [Horiginal [Hregistered HrestFields]]].
  destruct Hsame as [Hinv [Horig Hstack]].
  assert (Hslot : original.(os_sched_call_stack).(stackLeaseSlot) = tid).
  { rewrite Hstack in Hcur; congruence. }
  rewrite Hslot in Hregistered; assert (registered = old) by congruence; subst registered.
  exists (flag_pend_task_set_ready_flags old ready); split; [|exact Hflag].
  unfold flag_pend_update_task; rewrite <- Hslot.
  apply flag_active_task_fields_update with (task := old); [exact Hfields|reflexivity|].
  destruct Hfields as [_ [_ [_ [_ [_ Hclear]]]]]; exact Hclear.
Qed.

Lemma flag_pend_ready_flags_preserves_stack_coverage__immediate_clear_4 :
  forall tasks tid old ready active,
  tasks.(inUsedTaskStates) tid = Some old -> task_stack_live_coverage tasks active ->
  task_stack_live_coverage
    (glob_task_set_usedtask tasks tid (flag_pend_task_set_ready_flags old ready)) active.
Proof.
  intros tasks tid old ready active Hold Hcoverage.
  eapply (task_stack_live_coverage_used_map_frame tasks
    (glob_task_set_usedtask tasks tid (flag_pend_task_set_ready_flags old ready)) active);
    [|reflexivity|exact Hcoverage].
  intros slot node Hnode; cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
  destruct (Z.eqb slot tid) eqn:E.
  - apply Z.eqb_eq in E; subst slot; injection Hnode as Heq; subst node.
    exists old; split; [exact Hold|reflexivity].
  - exists node; auto.
Qed.

Lemma flag_pend_ready_flags_live_sp_eq__immediate_clear_4 :
  forall tasks tid old ready key sp,
  tasks.(inUsedTaskStates) tid = Some old ->
  task_stack_live_sp
    (glob_task_set_usedtask tasks tid (flag_pend_task_set_ready_flags old ready)) key sp =
  task_stack_live_sp tasks key sp.
Proof.
  intros tasks tid old ready key sp Hold.
  apply Axioms.propositional_extensionality; unfold task_stack_live_sp.
  cbn [glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb (fst key) tid) eqn:E.
  - apply Z.eqb_eq in E; rewrite E, Hold; split; intros H node Heq Hgen;
      injection Heq as Heq; subst node.
    + exact (H (flag_pend_task_set_ready_flags old ready) eq_refl Hgen).
    + exact (H old eq_refl Hgen).
  - tauto.
Qed.

Lemma flag_pend_ready_flags_capsules_eq__immediate_clear_4 :
  forall environment local state tid old ready,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  os_sched_fields_capsules environment local
    (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready)) =
  os_sched_fields_capsules environment local state.
Proof.
  intros environment local state tid old ready Hold.
  unfold os_sched_fields_capsules; cbn [flag_pend_update_task replace_TskS TskState].
  cbn [glob_task_set_usedtask parkedTaskStacks].
  assert (Hentry : kernel_saved_continuation_entry environment.(task_stack_call_continuations)
    (glob_task_set_usedtask state.(TskState) tid (flag_pend_task_set_ready_flags old ready)) local =
    kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState) local).
  { apply functional_extensionality; intro key.
    apply functional_extensionality; intro payload.
    unfold kernel_saved_continuation_entry.
    assert (Hsp : task_stack_live_sp
      (glob_task_set_usedtask state.(TskState) tid (flag_pend_task_set_ready_flags old ready)) key =
      task_stack_live_sp state.(TskState) key).
    { apply functional_extensionality; intro sp.
      apply flag_pend_ready_flags_live_sp_eq__immediate_clear_4; exact Hold. }
    rewrite Hsp; reflexivity. }
  rewrite Hentry; reflexivity.
Qed.

Lemma flag_pend_group_current_frame_merge_ready_flags__immediate_clear_4 :
  forall sg state tid old i image ready,
  flag_pend_current_binding state tid old ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBFlagsRdy # UShort |-> ready **
  flag_pend_group_current_frame sg state tid old i image |--
  flag_pend_group_frame sg
    (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready)) i image.
Proof.
  intros sg state tid old i image ready [Hcurrent Hold].
  pose proof (task_public_storage_merge_updated_field sg state.(TskState) tid old
    (flag_pend_task_set_ready_flags old ready) (TCBCommonField TCBFlagsRdy) (Some ready)
    (tcb_configured_common_field_in _ _ TCBFlagsRdy)
    (flag_pend_ready_flags_layout_image__immediate_clear_4 sg old ready)) as Htask.
  cbn [tcb_layout_cell tcb_cell] in Htask.
  assert (Hsched : sched_raw_rep sg state.(TskState) state.(SchedState) =
    sched_raw_rep sg
      (glob_task_set_usedtask state.(TskState) tid (flag_pend_task_set_ready_flags old ready))
      state.(SchedState)).
  { apply sched_raw_rep_priority_ext; intros slot Hin.
    symmetry; apply glob_task_set_usedtask_observation with (old := old); [exact Hold|reflexivity]. }
  assert (Hresidual : UCOS2_raw_rep_missing_task_storage_sched_flag sg state =
    UCOS2_raw_rep_missing_task_storage_sched_flag sg
      (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready))).
  { assert (Hevents : event_raw_rep sg state.(TskState) state.(EventState) =
      event_raw_rep sg
        (glob_task_set_usedtask state.(TskState) tid (flag_pend_task_set_ready_flags old ready))
        state.(EventState)).
    { apply event_raw_rep_change_task_index.
      apply event_wait_priority_agreement_encodes.
      eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
    unfold UCOS2_raw_rep_missing_task_storage_sched_flag, flag_pend_update_task.
    cbn [replace_TskS TskState IntrState EventState TickState MemoryState TimerState StatsState
      ControlState NameState glob_task_set_usedtask parkedTaskStacks].
    rewrite Hevents; reflexivity. }
  unfold flag_pend_group_current_frame, flag_pend_group_frame.
  sepcon_assoc_change; sep_apply_l_atomic Htask.
  sep_apply_r_atomic (proj2 (flag_pend_flag_frame_split_task_sched sg
    (flag_pend_update_task state tid (flag_pend_task_set_ready_flags old ready)))).
  rewrite <- Hresidual.
  cbn [flag_pend_update_task replace_TskS FlagState TskState SchedState].
  rewrite <- Hsched.
  unfold sched_raw_rep, sched_physical_rep, flag_pend_sched_without_current.
  rewrite Hcurrent; cbn [encode_task_link]; entailer!.
Qed.

Lemma flag_pend_group_type_five_implies_live__block_prepare_base : forall sg flags i image,
  valid_flag_state sg flags ->
  flags.(flagImages) i = Some image -> image.(flagImageType) = 5 ->
  exists group, flags.(flagUsed) i = Some group.
Proof.
  intros sg flags i image [Hpartition [Himages [_ [_ [Hfree _]]]]] Himage Htype.
  destruct Hpartition as [_ [_ Hpartition]].
  apply (proj2 (Hpartition i)); split.
  - apply (proj1 (Himages i)); eauto.
  - intro Hin.
    apply in_split in Hin; destruct Hin as [pre [post Hlist]].
    destruct (Hfree pre i post Hlist) as [free_image [Hfree_image [Hfree_type _]]].
    rewrite Himage in Hfree_image; inversion Hfree_image; subst free_image; congruence.
Qed.

Lemma flag_pend_local_node_not_registered__block_prepare_base : forall sg state node,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_fields_inv sg state ** flag_pend_node_fields node |--
  coq_prop (state.(FlagState).(flagWaitNodes) node = None).
Proof.
  intros sg state node Hconfig.
  unfold UCOS2_fields_inv, UCOS2_fields_raw_rep, flag_fields_configured_rep.
  rewrite Hconfig; cbn [selected_kernel_configuration cfgFlagEnabled].
  unfold flag_fields_raw_rep; Intros.
  sep_apply_l_atomic (flag_pend_node_fields_not_registered sg state.(FlagState).(flagWaitNodes) node).
  entailer!.
Qed.

Lemma flag_pend_word_land_requested_eq__block_prepare_base : forall sg bits requested,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  0 <= requested < 65536 ->
  flag_word sg.(osKernelConfig) (Z.land bits requested) = Z.land bits requested.
Proof.
  intros sg bits requested Hconfig Hrange.
  unfold flag_word; rewrite Hconfig.
  change ((Z.land bits requested) mod 2 ^ 16 = Z.land bits requested).
  rewrite <- (Z.land_ones (Z.land bits requested) 16) by lia.
  rewrite <- Z.land_assoc.
  rewrite (Z.land_ones requested 16) by lia.
  rewrite Z.mod_small by exact Hrange; reflexivity.
Qed.

Lemma flag_pend_first_waiting_current_waiter__block_waiting :
  forall sg i requested wait_type timeout acquired node blocked,
  flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked ->
  exists waiter,
    blocked.(SchedState).(curTaskID) = Some waiter.(flagTask) /\
    blocked.(FlagState).(flagWaitNodes) node = Some waiter.
Proof.
  intros sg i requested wait_type timeout acquired node blocked Hwaiting.
  unfold flag_pend_first_waiting, flag_pend_first_critical in Hwaiting.
  destruct (decode_flag_wait_mode sg.(osKernelConfig) (Z.land wait_type 127)) as [mode|];
    [|destruct Hwaiting as [Hfalse _]; discriminate].
  destruct Hwaiting as [image [Himage Hwaiting]].
  destruct (negb (Z.eqb image.(flagImageType) 5));
    [destruct Hwaiting as [Hfalse _]; discriminate|].
  destruct (flag_wait_satisfied mode (flag_ready_bits sg.(osKernelConfig) image.(flagImageBits) requested mode) requested);
    [destruct Hwaiting as [tid [old [_ [_ [Hfalse _]]]]]; discriminate|].
  destruct Hwaiting as [waiter [old [group [post [Hprotocol
    [Hgroup [Hmask [Hmode [Hblock [Hphase Hpost]]]]]]]]]].
  injection Hphase as Hnode; subst node; subst blocked.
  destruct (flag_block_spec.flag_block_result _ _ _ _ _ Hblock)
    as [tid [old2 [flags [Hcurrent [Hlookup [Hflags Hpost]]]]]].
  pose proof (proj1 Hprotocol) as Hcurrent_waiter.
  assert (Htid : tid = waiter.(flagTask)) by congruence; subst tid; subst post.
  unfold flag_block_node in Hflags.
  destruct (acquired.(FlagState).(flagUsed) waiter.(flagGroup)) as [g|]; [|discriminate].
  destruct (acquired.(FlagState).(flagImages) waiter.(flagGroup)) as [v|]; [|discriminate].
  injection Hflags as Hflags; subst flags.
  cbn [flag_block_spec.flag_block_state replace_FlagS replace_SchedS replace_TskS SchedState FlagState
    sched_remove_ready_task curTaskID flagWaitNodes].
  destruct (Z.eqb v.(flagImageHead) 0) eqn:Hhead.
  - rewrite kernel_resources.kernel_map_set_same.
    eexists; split; [|reflexivity]; exact Hcurrent_waiter.
  - unfold flag_nodes_set_prev.
    destruct (Z.eq_dec waiter.(flagNodeAddr) v.(flagImageHead)) as [Heq|Hneq].
    + rewrite <- Heq.
      rewrite !kernel_resources.kernel_map_set_same.
      cbn [option_map].
      eexists; split; [|reflexivity]; exact Hcurrent_waiter.
    + rewrite kernel_resources.kernel_map_set_other by exact Hneq.
      rewrite kernel_resources.kernel_map_set_same.
      eexists; split; [|reflexivity]; exact Hcurrent_waiter.
Qed.

Lemma flag_pend_waiting_active_task_source__block_waiting :
  forall sg i requested wait_type timeout acquired node blocked original call,
  flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked ->
  flag_pend_wait_active sg original node call blocked |--
    coq_prop (task_resume_spec.kernel_call_task_source call blocked).
Proof.
  intros sg i requested wait_type timeout acquired node blocked original call Hwaiting.
  destruct (flag_pend_first_waiting_current_waiter__block_waiting _ _ _ _ _ _ _ _ Hwaiting)
    as [waiter [Hcurrent Hnode]].
  unfold flag_pend_wait_active, flag_active_phase_source_spec.flag_active_waiting.
  Intros.
  entailer!.
  destruct H0 as [task [Hfields Hregistration]].
  rewrite Hnode in Hregistration.
  destruct Hregistration as [Hnode_addr [Hkey Hbacklink]].
  destruct Hfields as [[Hinv_eq [Horigin_eq Hstack_eq]]
    [Horigin [Hlookup [Hgen [Hinv Hclear]]]]].
  assert (Hslot : original.(os_sched_call_stack).(stackLeaseSlot) = waiter.(flagTask)).
  { exact (f_equal fst Hkey). }
  unfold task_resume_spec.kernel_call_task_source.
  split; [rewrite Horigin_eq, Hstack_eq; exact Horigin|].
  split; [rewrite Hinv_eq, Horigin_eq; exact Hinv|].
  unfold task_resume_spec.task_execution_current; rewrite Horigin_eq, Horigin, Hslot; exact Hcurrent.
Qed.

Lemma flag_pend_waiting_scheduler_input__block_waiting :
  forall environment critical local sg original node call mask state,
  task_resume_spec.kernel_call_task_source call state ->
  flag_pend_running_available call state ->
  (tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) ->
  flag_pend_caller_save_input environment critical local (flag_pend_wait_active sg original node)
    sg (FlagPendTaskCaller call) call mask state |--
  os_sched_active_call_pre environment local (flag_pend_wait_active sg original node) sg call mask state.
Proof.
  intros environment critical local sg original node call mask state Hsource Hrunning Hstack_address.
  unfold flag_pend_caller_save_input, flag_pend_active_save_input, os_sched_active_call_pre.
  rewrite <- (os_sched_fields_save_input_closed_world environment critical local sg call mask state).
  unfold os_sched_fields_save_input, flag_pend_wait_active, UCOS2_fields_inv.
  Intros.
  assert (Hready : state.(SchedState).(readyList) <> nil).
  { apply (task_idle_ready.sched_idle_ready_nonempty sg state.(TskState) state.(SchedState)).
    - exact (proj1 (proj1 (proj2 (proj2 H2)))).
    - exact (proj1 (proj2 H1)). }
  pose proof (os_sched_call_cut_from_source sg call state H2 Hsource Hready (proj2 Hrunning) Hstack_address) as Hcut.
  pose proof (flag_pend_wait_active_prefix sg original node) as Hstable.
  fold (flag_pend_wait_active sg original node) in Hstable.
  entailer!.
Qed.

Lemma flag_pend_waiting_restore_input_facts__block_waiting :
  forall environment critical local sg original node call saved acquired blocked
    i requested wait_type timeout,
  flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked ->
  flag_pend_caller_restore_input environment critical local
    (flag_pend_wait_active sg original node) sg (FlagPendTaskCaller call)
    call saved acquired blocked |--
  coq_prop (UCOS2_state_inv sg blocked /\
    task_resume_spec.kernel_call_task_source call blocked).
Proof.
  intros environment critical local sg original node call saved acquired blocked
    i requested wait_type timeout Hwaiting.
  unfold flag_pend_caller_restore_input, flag_pend_active_restore_input,
    os_sched_fields_restore_input.
  Intros.
  prop_apply_p (flag_pend_waiting_active_task_source__block_waiting
    sg i requested wait_type timeout acquired node blocked original call Hwaiting).
  Intros.
  unfold UCOS2_fields_inv; Intros; entailer!.
Qed.

Lemma flag_pend_waiting_restore_output_open__block_waiting :
  forall environment critical local sg original node call saved acquired blocked
    before_heap i requested wait_type timeout,
  flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked ->
  SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output environment critical local
    (flag_pend_wait_active sg original node) sg (FlagPendTaskCaller call)
    call saved acquired blocked before_heap |--
  EX returned current next_local,
    coq_prop (ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg
        call blocked returned current /\
      task_resume_spec.kernel_call_task_source returned current /\
      flag_pend_call_source_observations environment sg (FlagPendTaskCaller call)
        call blocked returned current) &&
    flag_pend_caller_save_input environment critical next_local
      (flag_pend_wait_active sg original node) sg (FlagPendTaskCaller returned)
      returned (armv7a_irq_fiq_mask saved) current.
Proof.
  intros environment critical local sg original node call saved acquired blocked
    before_heap i requested wait_type timeout Hwaiting heap
    [returned_caller [returned [current [next_local [Hobs [Hbefore [Hafter Hcompleted]]]]]]].
  pose proof (flag_pend_waiting_restore_input_facts__block_waiting
    environment critical local sg original node call saved acquired blocked
    i requested wait_type timeout Hwaiting before_heap Hbefore) as Hfacts.
  change (UCOS2_state_inv sg blocked /\
    task_resume_spec.kernel_call_task_source call blocked) in Hfacts.
  destruct Hfacts as [Hvalid Hsource].
  pose proof (proj1 (CompletedCallerSource.flag_pend_selected_completed_source_endpoints
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcompleted)) as Hendpoint.
  assert (Hend : flag_pend_call_source_observations environment sg
    (FlagPendTaskCaller call) call blocked returned current).
  { destruct Hendpoint as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
    split; [exact Hready|]. split; [exact Hidle|]. split; [exact Hnonidle|].
    split; [exact Hnormal|]. intro Horigin.
    eapply flag_pend_normal_return_control; [exact Hnormal|exact (Hcontrol Horigin)]. }
  destruct returned_caller as [next|view key]; [|contradiction].
  destruct Hobs as [Hactual [Hnext [Heffect [Hsame [Hpreserved Htransport]]]]].
  subst next.
  exists returned, current, next_local; split.
  - split; [exact Heffect|]. split; [|exact Hend].
    apply (proj2 (task_tcb_init_stack_same_call_source_iff returned call current Hsame)).
    apply (Htransport Hvalid); exact Hsource.
  - exact Hafter.
Qed.

Lemma flag_pend_waiting_current_task__resume_error :
  forall original call node state tid task,
  flag_pend_current_binding state tid task ->
  flag_pend_current_ready call state ->
  flag_active_waiting_registration original node call state ->
  tid = stackLeaseSlot (os_sched_call_stack original) /\
  flag_active_task_fields original call state task /\
  is_effectively_ready (stat task) (dly task) = true /\
  (match flagWaitNodes (FlagState state) node with
   | Some waiter => flagNodeAddr waiter = node /\
       task_stack_key (os_sched_call_stack original) =
         (flagTask waiter, flagTaskGeneration waiter) /\ tcbFlagNode task = node
   | None => tcbFlagNode task = 0
   end).
Proof.
  intros original call node state tid task [Hcurrent Htask]
    [ready [[Hreadytask [Hreadycurrent [Hpriority [Hin Heffective]]]] Hgen]]
    [registered [Hfields Hnode]].
  pose proof Hfields as [Hsame [Horigin [Hregistered Hrest]]].
  destruct Hsame as [Hinvocation [Hcallerorigin Hstack]].
  rewrite Hstack in Hreadycurrent, Hreadytask.
  assert (Htid : tid = stackLeaseSlot (os_sched_call_stack original)) by congruence.
  subst tid.
  assert (registered = task) by congruence; subst registered.
  assert (ready = task) by congruence; subst ready.
  split; [reflexivity|]. split; [exact Hfields|]. split; assumption.
Qed.

Lemma flag_pend_ready_detached_registration__resume_error :
  forall original call node state tid task,
  flag_pend_current_binding state tid task ->
  flag_pend_current_ready call state ->
  flag_active_waiting_registration original node call state ->
  flag_pend_wait_outcome original node state ->
  (encode_pend_status (statPend task) = 0 \/ encode_pend_status (statPend task) = 2) ->
  flagWaitNodes (FlagState state) node = None /\
  flag_active_fresh_registration original call state.
Proof.
  intros original call node state tid task Hbinding Hready Hregistration Houtcome Hstatus.
  destruct (flag_pend_waiting_current_task__resume_error original call node state tid task
    Hbinding Hready Hregistration) as [Htid [Hfields [Heffective Hnode]]].
  assert (Hpend : statPend task = PendOK \/ statPend task = PendAbort).
  { destruct (statPend task); simpl in Hstatus; intuition congruence. }
  pose proof (flag_pend_wait_ready_classification original node state task Houtcome
    (proj1 (proj2 (proj2 Hfields))) Heffective) as Hclassification.
  assert (Hnone : flagWaitNodes (FlagState state) node = None).
  { apply (proj2 (proj1 Hclassification)); exact Hpend. }
  split; [exact Hnone|]. exists task; split; [exact Hfields|].
  rewrite Hnone in Hnode; exact Hnode.
Qed.

Lemma task_active_lookup_identity__resume_error : forall sg tasks tid task,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some task ->
  task.(taskID) = tid.
Proof.
  intros sg tasks tid task [_ [[Hnd [Hhead [Hcount [Hdomain Hlinks]]]] Hrest]] Hlookup.
  assert (Hin : In tid (taskActiveOrder (taskLifecycle tasks))).
  { apply (proj2 (Hdomain tid)); eauto. }
  clear Hnd Hhead Hcount Hdomain Hrest.
  revert Hin Hlinks.
  generalize (@None TaskID).
  induction (taskActiveOrder (taskLifecycle tasks)) as [|head tail IH].
  - intros previous Hin; contradiction.
  - intros previous Hin [t [Ht [Hid [Hp [Hn Htail]]]]].
    destruct Hin as [Heq|Hin].
    + subst head; rewrite Hlookup in Ht; inversion Ht; exact Hid.
    + exact (IH (Some head) Hin Htail).

Qed.

Lemma flag_pend_sched_priority_frame__resume_error : forall sg tasks sched tid old new,
  inUsedTaskStates tasks tid = Some old -> curPrio new = curPrio old ->
  flag_pend_sched_without_current sg tasks sched =
  flag_pend_sched_without_current sg (glob_task_set_usedtask tasks tid new) sched.
Proof.
  intros sg tasks sched tid old new Hold Hprio.
  assert (Hobs : forall slot, In slot (readyList sched) ->
    option_map curPrio (inUsedTaskStates tasks slot) =
    option_map curPrio (inUsedTaskStates (glob_task_set_usedtask tasks tid new) slot)).
  { intros slot Hin; symmetry; eapply glob_task_set_usedtask_observation; eauto. }
  destruct (sched_encoding_priority_ext (readyList sched) tasks
    (glob_task_set_usedtask tasks tid new) Hobs) as [Hgrp Htbl].
  unfold flag_pend_sched_without_current.
  rewrite Hgrp; cbn [sched_rows_rep]; rewrite !Htbl; reflexivity.
Qed.

Lemma flag_pend_task_update_residual_eq__resume_error : forall sg state tid old new,
  inUsedTaskStates (TskState state) tid = Some old ->
  curPrio new = curPrio old ->
  UCOS2_raw_rep_missing_task_storage_sched_flag sg state =
  UCOS2_raw_rep_missing_task_storage_sched_flag sg (flag_pend_update_task state tid new).
Proof.
  intros sg state tid old new Hold Hprio.
  unfold UCOS2_raw_rep_missing_task_storage_sched_flag, flag_pend_update_task.
  cbn [replace_TskS TskState IntrState EventState TickState MemoryState TimerState StatsState ControlState NameState glob_task_set_usedtask parkedTaskStacks].
  rewrite (event.event_raw_rep_change_task_index sg (TskState state)
    (glob_task_set_usedtask (TskState state) tid new) (EventState state)).
  - reflexivity.
  - apply event.event_wait_priority_agreement_encodes.
    eapply event.glob_task_set_usedtask_preserves_event_priority_agreement; eauto.
Qed.

Lemma flag_pend_task_update_masked_control__resume_error :
  forall environment local critical sg call saved acquired state tid old new,
  inUsedTaskStates (TskState state) tid = Some old ->
  taskGeneration new = taskGeneration old ->
  tcbStkPtr new = tcbStkPtr old ->
  flag_pend_masked_control environment local critical sg call saved acquired state |--
  flag_pend_masked_control environment local critical sg call saved acquired
    (flag_pend_update_task state tid new).
Proof.
  intros environment local critical sg call saved acquired state tid old new Hold Hgen Hsp.
  assert (Hback : forall slot node,
    inUsedTaskStates (glob_task_set_usedtask (TskState state) tid new) slot = Some node ->
    exists previous, inUsedTaskStates (TskState state) slot = Some previous /\
      taskGeneration node = taskGeneration previous /\ tcbStkPtr node = tcbStkPtr previous).
  { intros slot node Hnode; cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
    destruct (Z.eqb slot tid) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot; inversion Hnode; subst node; eauto.
    - exists node; auto. }
  assert (Hcaps : os_sched_fields_capsules environment local state |--
    os_sched_fields_capsules environment local (flag_pend_update_task state tid new)).
  { unfold os_sched_fields_capsules, flag_pend_update_task.
    cbn [replace_TskS TskState glob_task_set_usedtask parkedTaskStacks].
    apply kernel_saved_continuation_publication_spec.kernel_saved_continuation_map_reindex.
    intros key payload node Hpayload Hnode Hkey.
    destruct (Hback (fst key) node Hnode) as [previous [Hprevious [Hg Hs]]].
    exists previous; split; [exact Hprevious|]; split; symmetry; assumption. }
  unfold flag_pend_masked_control; Intros.
  assert (Hcoverage : task_stack_coverage_spec.task_stack_live_coverage
    (TskState (flag_pend_update_task state tid new)) (task_stack_call_active_key call)).
  { eapply task_stack_coverage_spec.task_stack_live_coverage_used_map_frame
      with (before := TskState state).
    - intros slot node Hnode.
      destruct (Hback slot node Hnode) as [previous [Hprevious [Hg Hs]]].
      exists previous; auto.
    - reflexivity.
    - assumption. }
  sep_apply_l_atomic Hcaps; entailer!.
Qed.

Lemma flag_pend_resume_merge_written_pend__resume_error : forall sg tasks tid old,
    tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> 0 **
    tcb_field_address (task_slot_addr sg tid) TCBStat # UChar |-> encode_task_status (stat old) **
    task_public_storage_without_two_fields sg tasks tid old
      (TCBCommonField TCBStatPend) (TCBCommonField TCBStat) |--
    used_task_rep sg tid (flag_pend_write_pend_ok old) **
    task_public_storage_without_task sg tasks tid.
Proof.
  intros sg tasks tid old.
unfold task_public_storage_without_two_fields.
    pose proof (TaskFieldStorage.store_fields_merge_field
      TCBLayoutField (option Z) TCBLayoutField_eq_dec
      (tcb_layout_cell (cfgEventMultiEnabled (osKernelConfig sg)) (task_slot_addr sg tid))
      (remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend)
        (tcb_configured_fields (cfgEventMultiEnabled (osKernelConfig sg)) (cfgTaskProfile (osKernelConfig sg))))
      (task_layout_image sg old) (TCBCommonField TCBStat)
      (tcb_configured_fields_remove_nodup _ _ (tcb_configured_fields_nodup _ _))
      ltac:(apply in_in_remove; [discriminate|apply tcb_configured_common_field_in])) as Hsecond.
    cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell] in Hsecond.
    unfold task.encode_task_status in Hsecond.
    unfold used_task_rep, task_slot_storage_rep, tcb_configured_storage_rep.
    rewrite flag_pend_write_pend_ok_layout.
    pose proof (TaskFieldStorage.store_fields_merge_updated_field
      TCBLayoutField (option Z) TCBLayoutField_eq_dec
      (tcb_layout_cell (cfgEventMultiEnabled (osKernelConfig sg)) (task_slot_addr sg tid))
      (tcb_configured_fields (cfgEventMultiEnabled (osKernelConfig sg)) (cfgTaskProfile (osKernelConfig sg)))
      (task_layout_image sg old) (TCBCommonField TCBStatPend) (Some 0)
      (tcb_configured_fields_nodup _ _) (tcb_configured_common_field_in _ _ _)) as Hfirst.
    cbn [tcb_layout_cell tcb_cell] in Hfirst.
    sep_apply_r_atomic Hfirst.
    sepcon_assoc_change.
    sep_apply_r_atomic Hsecond.
    entailer!.
Qed.

Lemma flag_pend_update_task_twice_eq__resume_error : forall state tid first last,
  flag_pend_update_task (flag_pend_update_task state tid first) tid last =
  flag_pend_update_task state tid last.
Proof.
  intros; unfold flag_pend_update_task.
  cbn [replace_TskS TskState].
  assert (Htasks : glob_task_set_usedtask (glob_task_set_usedtask (TskState state) tid first) tid last =
    glob_task_set_usedtask (TskState state) tid last).
  { unfold glob_task_set_usedtask; cbn; f_equal.
    apply Coq.Logic.FunctionalExtensionality.functional_extensionality; intro slot.
    destruct (Z.eqb slot tid); reflexivity. }
  rewrite Htasks; apply replace_TskS_last_write.
Qed.

Lemma flag_pend_clear_status_event_cleanup_eq__resume_error : forall sg state tid old,
  osKernelConfig sg = selected_kernel_configuration ->
  eventPtr old = None ->
  cross_module_invariants.event_pend_cleanup_state sg false state tid old =
  flag_pend_update_task state tid (task_clear_pend_status false old).
Proof.
  intros sg state tid old Hconfig Hnull.
  unfold cross_module_invariants.event_pend_cleanup_state.
  rewrite Hconfig.
  cbn [selected_kernel_configuration cfgEventMultiEnabled task_event_pend_cleanup].
  assert (Htask : task_set_event_ptr (task_clear_pend_status false old) None =
      task_clear_pend_status false old).
  { destruct old; cbn in Hnull; subst; reflexivity. }
  change (replace_TskS (glob_task_set_usedtask (TskState state) tid
    (task_set_event_ptr (task_clear_pend_status false old) None)) state =
    replace_TskS (glob_task_set_usedtask (TskState state) tid (task_clear_pend_status false old)) state).
  rewrite Htask; reflexivity.
Qed.

Lemma flag_pend_clear_status_preserves_validity__resume_error : forall sg state tid old,
  osKernelConfig sg = selected_kernel_configuration ->
  UCOS2_state_inv sg state ->
  inUsedTaskStates (TskState state) tid = Some old ->
  flag_active_event_clear old -> tcbFlagNode old = 0 ->
  In tid (readyList (SchedState state)) ->
  UCOS2_state_inv sg (flag_pend_update_task state tid (task_clear_pend_status false old)).
Proof.
  intros sg state tid old Hconfig Hvalid Hold [Hevent [Hmulti HmultiPtr]] Hnode Hready.
  rewrite <- (flag_pend_clear_status_event_cleanup_eq__resume_error sg state tid old Hconfig Hevent).
  eapply UCOS2_event_pend_cleanup_preserves_validity; eassumption.
Qed.

Lemma flag_pend_update_current_ready__resume_error : forall call state tid old new,
  flag_pend_current_binding state tid old ->
  flag_pend_current_ready call state ->
  taskGeneration new = taskGeneration old -> curPrio new = curPrio old ->
  is_effectively_ready (stat new) (dly new) = true ->
  flag_pend_current_ready call (flag_pend_update_task state tid new).
Proof.
  intros call state tid old new [Hcurrent Hold]
    [ready [[Hlookup [Hcur [Hprio [Hin Heffective]]]] Hgen]] Hgeneration Hpriority Hready.
  assert (Htid : tid = stackLeaseSlot (os_sched_call_stack call)) by congruence.
  subst tid.
  assert (ready = old) by congruence; subst ready.
  exists new; split.
  - split.
    + cbn [flag_pend_update_task replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
      rewrite Z.eqb_refl; reflexivity.
    + split; [exact Hcur|]. split; [rewrite Hpriority; exact Hprio|].
      split; assumption.
  - congruence.
Qed.

Lemma flag_pend_clear_status_effectively_ready__resume_error : forall old,
  is_effectively_ready (stat old) (dly old) = true ->
  is_effectively_ready (stat (task_clear_pend_status false old))
    (dly (task_clear_pend_status false old)) = true.
Proof.
  intros old Hready.
  unfold is_effectively_ready in Hready.
  destruct (Z.eqb (task_non_suspension_bits (stat old)) 0); [|discriminate].
  apply Bool.andb_true_iff in Hready; destruct Hready as [_ Hdelay].
  exact Hdelay.
Qed.

Lemma flag_pend_cleanup_stat_merge_updated__resume_error : forall sg state tid old current_ptr,
  osKernelConfig sg = selected_kernel_configuration ->
  flag_pend_current_binding state tid old ->
  current_ptr = g_OSTCBCur sg ->
  UCOS2_state_inv sg (flag_pend_update_task state tid (task_set_status old Byte.zero)) ->
  current_ptr # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBStat # UChar |-> 0 **
  flag_pend_cleanup_stat_frame sg state tid old |--
  UCOS2_fields_inv sg (flag_pend_update_task state tid (task_set_status old Byte.zero)).
Proof.
  intros sg state tid old current_ptr Hconfig Hbinding Hcurrent Hvalid.
  pose proof (task_public_storage_merge_updated_field sg (TskState state) tid old
    (task_set_status old Byte.zero) (TCBCommonField TCBStat) (Some 0)
    (tcb_configured_common_field_in _ _ _) (task_set_status_layout_image_eq sg old Byte.zero)) as Hmerge.
  cbn [tcb_layout_cell tcb_cell] in Hmerge.
  unfold flag_pend_cleanup_stat_frame.
  sepcon_assoc_change; sep_apply_l_atomic Hmerge.
  rewrite (flag_pend_sched_priority_frame__resume_error sg (TskState state) (SchedState state)
    tid old (task_set_status old Byte.zero) (proj2 Hbinding) eq_refl).
  rewrite (flag_pend_task_update_residual_eq__resume_error sg state tid old
    (task_set_status old Byte.zero) (proj2 Hbinding) eq_refl).
  rewrite UCOS2_fields_inv_split_task_storage_sched_flag.
  unfold sched_raw_rep, sched_physical_rep, flag_pend_sched_without_current.
  cbn [flag_pend_update_task replace_TskS TskState SchedState FlagState].
  rewrite (proj1 Hbinding), Hcurrent.
  cbn [encode_task_link].
  unfold flag_fields_configured_rep; rewrite Hconfig; cbn [selected_kernel_configuration cfgFlagEnabled].
  entailer!.
Qed.

Lemma flag_pend_update_flag_commute_eq__resume_error : forall state tid task flags,
  flag_pend_update_task (replace_FlagS flags state) tid task =
  replace_FlagS flags (flag_pend_update_task state tid task).
Proof. reflexivity. Qed.

Lemma flag_pend_error_cleanup_preserves_call_state__resume_error :
  forall sg original call node state tid old intermediate middle,
  osKernelConfig sg = selected_kernel_configuration ->
  flag_pend_error_source_facts sg original call node state tid old ->
  flag_pend_error_intermediate state node (encode_pend_status (statPend old)) intermediate ->
  flag_pend_current_binding intermediate tid middle ->
  let cleaned := flag_pend_update_task intermediate tid (task_set_status middle Byte.zero) in
  UCOS2_state_inv sg cleaned /\
  flag_pend_current_ready call cleaned /\
  flag_active_fresh_registration original call cleaned /\
  flag_pend_running_available call cleaned /\
  (forall i mode, flag_pend_resume_result sg i node mode state 0
    (flag_pend_resume_error (encode_pend_status (statPend old))) cleaned).
Proof.
  intros sg original call node state tid old intermediate middle Hconfig
    [Hvalid [Hbinding [Hready [Hrunning [Houtcome [Hregistration Hnonzero]]]]]]
    Hintermediate Hmiddle.
  cbn zeta.
  pose proof (flag_pend_waiting_current_task__resume_error original call node state tid old
    Hbinding Hready Hregistration) as [Htid [Hfields [Heffective Hnode]]].
  pose proof Hfields as [Hsame [Horigin [Hregistered [Hgeneration [Hactive Hclear]]]]].
  assert (Hin : In tid (readyList (SchedState state))).
  { destruct Hready as [t [[Ht [Hcur [Hp [Hi He]]]] Hg]].
    destruct Hbinding as [Hcur' Hold]. assert (tid = stackLeaseSlot (os_sched_call_stack call)) by congruence.
    congruence. }
  pose proof Hbinding as [Hcurrent Hold].
  destruct Hintermediate as [tid' [old' [Hbinding' [Hstatus Hintermediate]]]].
  assert (tid' = tid) by (destruct Hbinding' as [Hcur' _]; congruence).
  subst tid'.
  assert (old' = old) by (destruct Hbinding' as [_ Hold']; congruence).
  subst old'.
  destruct (Z.eqb (encode_pend_status (statPend old)) 2) eqn:Hbranch.
  - apply Z.eqb_eq in Hbranch.
    subst intermediate.
    assert (Hmiddle_eq : middle = flag_pend_write_pend_ok old).
    { pose proof (proj2 Hmiddle) as Hlookup.
      cbn [flag_pend_update_task replace_TskS TskState glob_task_set_usedtask inUsedTaskStates] in Hlookup.
      rewrite Z.eqb_refl in Hlookup; congruence. }
    subst middle.
    rewrite (proj1 (flag_pend_error_write_stat_endpoint old)).
    rewrite flag_pend_update_task_twice_eq__resume_error.
    destruct (flag_pend_ready_detached_registration__resume_error original call node state tid old
      Hbinding Hready Hregistration Houtcome (or_intror Hbranch)) as [Hnone Hfresh].
    rewrite Hnone in Hnode.
    split.
    + eapply flag_pend_clear_status_preserves_validity__resume_error; eassumption.
    + split.
      * eapply flag_pend_update_current_ready__resume_error; try eassumption; try reflexivity.
        apply flag_pend_clear_status_effectively_ready__resume_error; exact Heffective.
      * split.
        -- exists (task_clear_pend_status false old); split; [|exact Hnode].
           unfold flag_pend_update_task; rewrite Htid.
           apply flag_active_task_fields_update with (task := old); try assumption; reflexivity.
        -- split; [exact Hrunning|].
           intros i mode; unfold flag_pend_resume_result; rewrite Hbranch.
           apply flag_pend_resume_abort; assumption.
  - apply Z.eqb_neq in Hbranch.
    destruct Hintermediate as [waiter [flags [Hunlink [Hwaiter Hintermediate]]]].
    subst intermediate.
    assert (Hmiddle_eq : middle = task_set_flag_node (flag_pend_write_pend_ok old) 0).
    { pose proof (proj2 Hmiddle) as Hlookup.
      cbn [flag_pend_update_task replace_TskS replace_FlagS TskState glob_task_set_usedtask inUsedTaskStates] in Hlookup.
      rewrite Z.eqb_refl in Hlookup; congruence. }
    subst middle.
    rewrite flag_pend_update_flag_commute_eq__resume_error.
    rewrite flag_pend_update_task_twice_eq__resume_error.
    rewrite (proj2 (flag_pend_error_write_stat_endpoint old)).
    set (unlinked := cross_module_invariants.flag_timeout_cleanup_state state waiter flags old).
    assert (Hunlinked_valid : UCOS2_state_inv sg unlinked).
    { apply UCOS2_flag_timeout_cleanup_preserves_validity with (p := node).
      - exact Hvalid.
      - exact Hunlink.
      - rewrite Hwaiter; exact Hold.
      - unfold is_effectively_ready in Heffective.
        destruct (Z.eqb (task_non_suspension_bits (stat old)) 0) eqn:Hbits; [apply Z.eqb_eq; exact Hbits|discriminate]. }
    assert (Hunlinked_binding : flag_pend_current_binding unlinked tid (task_set_flag_node old 0)).
    { split; [exact Hcurrent|].
      unfold unlinked; cbn [cross_module_invariants.flag_timeout_cleanup_state replace_FlagS replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
      rewrite Hwaiter, Z.eqb_refl; reflexivity. }
    assert (Hunlinked_ready : flag_pend_current_ready call unlinked).
    { unfold unlinked.
      change (flag_pend_current_ready call (flag_pend_update_task state (flagTask waiter) (task_set_flag_node old 0))).
      rewrite Hwaiter.
      eapply flag_pend_update_current_ready__resume_error; try eassumption; reflexivity. }
    assert (Hunlinked_fields : flag_active_task_fields original call unlinked (task_set_flag_node old 0)).
    { unfold unlinked.
      change (flag_active_task_fields original call
        (flag_pend_update_task state (flagTask waiter) (task_set_flag_node old 0)) (task_set_flag_node old 0)).
      rewrite Hwaiter, Htid.
      apply flag_active_task_fields_update with (task := old); try assumption; reflexivity. }
    assert (Hendpoint :
      replace_FlagS flags (flag_pend_update_task state tid (task_set_flag_node (task_clear_pend_status false old) 0)) =
      flag_pend_update_task unlinked tid (task_clear_pend_status false (task_set_flag_node old 0))).
    { unfold unlinked.
      change (replace_FlagS flags (flag_pend_update_task state tid (task_set_flag_node (task_clear_pend_status false old) 0)) = flag_pend_update_task
        (replace_FlagS flags (flag_pend_update_task state (flagTask waiter) (task_set_flag_node old 0)))
        tid (task_clear_pend_status false (task_set_flag_node old 0))).
      rewrite Hwaiter, flag_pend_update_flag_commute_eq__resume_error, flag_pend_update_task_twice_eq__resume_error.
      reflexivity. }
    assert (Hresult : forall i mode, flag_pend_resume_result sg i node mode state 0
      (flag_pend_resume_error (encode_pend_status (statPend old)))
      (replace_FlagS flags (flag_pend_update_task state tid (task_set_flag_node (task_clear_pend_status false old) 0)))).
    { intros i mode; unfold flag_pend_resume_result.
      rewrite (flag_pend_resume_default_error _ Hbranch).
      rewrite <- flag_pend_update_flag_commute_eq__resume_error.
      eapply flag_pend_resume_timeout; eassumption. }
    rewrite Hendpoint in Hresult |- *.
    split.
    + eapply flag_pend_clear_status_preserves_validity__resume_error.
      * exact Hconfig.
      * exact Hunlinked_valid.
      * exact (proj2 Hunlinked_binding).
      * exact Hclear.
      * reflexivity.
      * exact Hin.
    + split.
      * eapply flag_pend_update_current_ready__resume_error; try eassumption; try reflexivity.
        apply flag_pend_clear_status_effectively_ready__resume_error; exact Heffective.
      * split.
        -- exists (task_clear_pend_status false (task_set_flag_node old 0)); split; [|reflexivity].
           unfold flag_pend_update_task; rewrite Htid.
           apply flag_active_task_fields_update with (task := task_set_flag_node old 0); try assumption; reflexivity.
        -- split; [exact Hrunning|exact Hresult].
Qed.

Lemma flag_pend_resume_fields_merge_original__resume_success : forall sg state tid old,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg state ->
  flag_pend_current_binding state tid old ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> encode_pend_status old.(statPend) **
  tcb_field_address (task_slot_addr sg tid) TCBStat # UChar |-> encode_task_status old.(stat) **
  flag_pend_resume_frame sg state tid old |-- UCOS2_fields_inv sg state.
Proof.
  intros sg state tid old Hconfig Hinv [Hcurrent Hold].
  assert (Htasks :
    tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> encode_pend_status old.(statPend) **
    tcb_field_address (task_slot_addr sg tid) TCBStat # UChar |-> encode_task_status old.(stat) **
    task_public_storage_without_two_fields sg state.(TskState) tid old
      (TCBCommonField TCBStatPend) (TCBCommonField TCBStat) |--
    task_public_storage sg state.(TskState)).
  { pose proof (TaskFieldStorage.store_fields_merge_field
      TCBLayoutField (option Z) TCBLayoutField_eq_dec
      (tcb_layout_cell (cfgEventMultiEnabled (osKernelConfig sg)) (task_slot_addr sg tid))
      (remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend)
        (tcb_configured_fields (cfgEventMultiEnabled (osKernelConfig sg)) (cfgTaskProfile (osKernelConfig sg))))
      (task_layout_image sg old) (TCBCommonField TCBStat)
      (tcb_configured_fields_remove_nodup _ _ (tcb_configured_fields_nodup _ _))
      ltac:(apply in_in_remove; [discriminate|apply tcb_configured_common_field_in])) as Hsecond.
    cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell] in Hsecond.
    unfold task.encode_task_status in Hsecond.
    unfold task_public_storage_without_two_fields.
    pose proof (task_public_storage_merge_field sg state.(TskState) tid old
      (TCBCommonField TCBStatPend) Hold (tcb_configured_common_field_in _ _ _)) as Hfirst.
    cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell] in Hfirst.
    sep_apply_r_atomic Hfirst.
    unfold task_public_storage_without_field, tcb_configured_storage_without_field.
    sepcon_assoc_change; sep_apply_r_atomic Hsecond; entailer!. }
  unfold flag_pend_resume_frame.
  unfold UCOS2_fields_inv, UCOS2_fields_raw_rep, flag_fields_configured_rep.
  rewrite Hconfig; cbn [selected_kernel_configuration cfgFlagEnabled]; entailer!.
  sep_apply_r_atomic (proj2 (flag_pend_flag_frame_split_task_sched sg state)).
  sepcon_assoc_change; sep_apply_r_atomic Htasks.
  unfold sched_raw_rep, sched_physical_rep, flag_pend_sched_without_current.
  rewrite Hcurrent; cbn [encode_task_link]; entailer!.
Qed.

Lemma flag_pend_waiting_current_task__resume_success :
  forall original call node state tid task,
  flag_pend_current_binding state tid task ->
  flag_pend_current_ready call state ->
  flag_active_waiting_registration original node call state ->
  tid = stackLeaseSlot (os_sched_call_stack original) /\
  flag_active_task_fields original call state task /\
  is_effectively_ready (stat task) (dly task) = true /\
  (match flagWaitNodes (FlagState state) node with
   | Some waiter => flagNodeAddr waiter = node /\
       task_stack_key (os_sched_call_stack original) =
         (flagTask waiter, flagTaskGeneration waiter) /\ tcbFlagNode task = node
   | None => tcbFlagNode task = 0
   end).
Proof.
  intros original call node state tid task [Hcurrent Htask]
    [ready [[Hreadytask [Hreadycurrent [Hpriority [Hin Heffective]]]] Hgen]]
    [registered [Hfields Hnode]].
  pose proof Hfields as [Hsame [Horigin [Hregistered Hrest]]].
  destruct Hsame as [Hinvocation [Hcallerorigin Hstack]].
  rewrite Hstack in Hreadycurrent, Hreadytask.
  assert (Htid : tid = stackLeaseSlot (os_sched_call_stack original)) by congruence.
  subst tid.
  assert (registered = task) by congruence; subst registered.
  assert (ready = task) by congruence; subst ready.
  split; [reflexivity|]. split; [exact Hfields|]. split; assumption.
Qed.

Lemma flag_pend_ready_detached_registration__resume_success :
  forall original call node state tid task,
  flag_pend_current_binding state tid task ->
  flag_pend_current_ready call state ->
  flag_active_waiting_registration original node call state ->
  flag_pend_wait_outcome original node state ->
  encode_pend_status (statPend task) = 0 ->
  flagWaitNodes (FlagState state) node = None /\
  flag_active_fresh_registration original call state.
Proof.
  intros original call node state tid task Hbinding Hready Hregistration Houtcome Hstatus.
  destruct (flag_pend_waiting_current_task__resume_success original call node state tid task
    Hbinding Hready Hregistration) as [Htid [Hfields [Heffective Hnode]]].
  assert (Hpend : statPend task = PendOK).
  { destruct (statPend task); simpl in Hstatus; congruence. }
  pose proof (flag_pend_wait_ready_classification original node state task Houtcome
    (proj1 (proj2 (proj2 Hfields))) Heffective) as Hclassification.
  assert (Hnone : flagWaitNodes (FlagState state) node = None).
  { apply (proj2 (proj1 Hclassification)); left; exact Hpend. }
  split; [exact Hnone|]. exists task; split; [exact Hfields|].
  rewrite Hnone in Hnode; exact Hnode.
Qed.

Lemma flag_pend_consume_testbit__resume_success : forall word,
  Z.eqb (Z.land word 128) 0 = negb (Z.testbit word 7).
Proof.
  intros word.
  assert (E : Z.land word 128 = if Z.testbit word 7 then 128 else 0).
  { apply Z.bits_inj; intro bit.
    rewrite Z.land_spec.
    change 128 with (2^7).
    rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eq_dec bit 7) as [->|Hne].
    - rewrite Z.eqb_refl; destruct (Z.testbit word 7); reflexivity.
    - assert (Eb : (Z.eqb 7 bit) = false) by (apply Z.eqb_neq; lia).
      rewrite Eb, Bool.andb_false_r.
      destruct (Z.testbit word 7); [rewrite Z.pow2_bits_false by lia|rewrite Z.bits_0]; reflexivity. }
  rewrite E; destruct (Z.testbit word 7); reflexivity.
Qed.

Lemma flag_pend_mode_consume__resume_success : forall word mode consume,
  flag_pend_mode_parameters word mode consume ->
  unsigned_last_nbits consume 32 = consume /\
  (consume = 1 <-> Z.testbit word 7 = true) /\
  (consume = 0 <-> Z.testbit word 7 = false).
Proof.
  intros word mode consume [_ ->].
  rewrite flag_pend_consume_testbit__resume_success.
  destruct (Z.testbit word 7); cbn; repeat split; intros; try congruence; reflexivity.
Qed.

Lemma flag_pend_resumed_group_address__resume_success :
  forall environment critical sg caller original mask before i pgrp requested mode delay X
    node returned saved acquired,
  flag_pend_public_entry environment critical sg caller original mask i pgrp requested mode delay before X ->
  flag_pend_resumed_prefix environment critical sg original mask before i pgrp requested mode delay
    node returned saved acquired ->
  0 <= i < sg.(osKernelConfig).(cfgMaxFlags) /\ pgrp = flag_pool_addr sg i.
Proof.
  intros environment critical sg caller original mask before i pgrp requested mode delay X
    node returned saved acquired [_ [Haddress _]]
    [scheduled [entry [[restored [released [[entered [first_saved [first_acquired [blocked
      [[Hnonnull Hprefix] Hrest]]]]] Hscheduled]]] Hsave]]].
  destruct Haddress as [Hzero|Haddress]; [contradiction|exact Haddress].
Qed.

Lemma flag_pend_masked_fields_fresh_restore__resume_success :
  forall environment critical local sg original call saved acquired state,
  flag_active_fresh_registration original call state ->
  flag_pend_masked_control environment local critical sg call saved acquired state **
  UCOS2_fields_inv sg state |--
  flag_pend_caller_restore_input environment critical local (flag_pend_fresh_observation original)
    sg (FlagPendTaskCaller call) call saved acquired state.
Proof.
  intros.
  unfold flag_pend_caller_restore_input, flag_pend_active_restore_input,
    flag_pend_fresh_observation, os_sched_fields_restore_input,
    flag_pend_masked_control.
  entailer!.
Qed.

Lemma flag_pend_pool_set_bits_preserves_validity__resume_success : forall sg flags i image bits,
  valid_flag_state sg flags -> flags.(flagImages) i = Some image ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  valid_flag_state sg (flag_pend_pool_set_bits flags i image bits).
Proof.
  intros sg flags i image bits Hvalid Himage Hbits.
  destruct (flags.(flagUsed) i) as [group|] eqn:Hgroup.
  - assert (Heq : flag_pend_pool_set_bits flags i image bits =
      flag_replace_bits flags i group image bits).
    { unfold flag_pend_pool_set_bits, flag_replace_bits; rewrite Hgroup; reflexivity. }
    rewrite Heq; eapply flag_replace_bits_preserves_validity; eassumption.
  - destruct Hvalid as [Hpool [Hdomain [Himages [Hused [Hfree Hnodes]]]]].
    unfold flag_pend_pool_set_bits; rewrite Hgroup.
    unfold valid_flag_state; cbn.
    split; [exact Hpool|]. split.
    + intro j; destruct (Z.eq_dec j i) as [->|Hne].
      * rewrite kernel_map_set_same; split.
        -- intros _; apply (proj1 (Hdomain i)); exists image; exact Himage.
        -- intros _; eauto.
      * rewrite kernel_map_set_other by exact Hne; apply Hdomain.
    + split.
      * intros j v Hlookup; unfold kernel_map_set in Hlookup.
        destruct (Z.eq_dec j i) as [->|Hne].
        -- inversion Hlookup; subst v; split; [exact Hbits|exact (proj2 (Himages i image Himage))].
        -- eapply Himages; eassumption.
      * split.
        -- intros j g Hlookup.
           assert (Hne : j <> i) by (intro E; subst j; congruence).
           destruct (Hused j g Hlookup) as [Hg [Hgen [Hwait [v [Hv Hrest]]]]].
           split; [exact Hg|]. split; [exact Hgen|]. split.
           ++ exact Hwait.
           ++ exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Hv|exact Hrest].
        -- split.
           ++ intros pre j rest Hlist.
              destruct (Hfree pre j rest Hlist) as [v [Hv Hrest]].
              destruct (Z.eq_dec j i) as [->|Hne].
              ** assert (v = image) by congruence; subst v.
                 exists (flag_image_set_bits image bits); split;
                   [apply kernel_map_set_same|exact Hrest].
              ** exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Hv|exact Hrest].
           ++ exact Hnodes.
Qed.

Lemma flag_pend_pool_bits_preserves_state_inv__resume_success : forall sg state i image bits,
  UCOS2_state_inv sg state -> sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  state.(FlagState).(flagImages) i = Some image ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  UCOS2_state_inv sg (replace_FlagS (flag_pend_pool_set_bits state.(FlagState) i image bits) state).
Proof.
  intros sg state i image bits Hinv Hen Himage Hbits.
  assert (Hnext : valid_flag_configuration sg (flag_pend_pool_set_bits state.(FlagState) i image bits)).
  { unfold valid_flag_configuration; rewrite Hen.
    eapply flag_pend_pool_set_bits_preserves_validity__resume_success; [|exact Himage|exact Hbits].
    destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [Hflag _]]]]]]]].
    unfold valid_flag_configuration in Hflag; rewrite Hen in Hflag; exact Hflag. }
  assert (Hnames : Ucos2Verify.lib.kernel_names.kernel_names_valid sg
    (replace_FlagS (flag_pend_pool_set_bits state.(FlagState) i image bits) state)).
  { apply Ucos2Verify.lib.kernel_names.kernel_names_valid_replace_flag.
    - exact (UCOS2_state_inv_names_valid _ _ Hinv).
    - intros name [id [node [Hlookup Hname]]].
      unfold flag_pend_pool_set_bits in Hlookup; cbn [flagUsed] in Hlookup.
      destruct (state.(FlagState).(flagUsed) i) as [group|] eqn:Hgroup.
      + unfold kernel_map_set in Hlookup; destruct (Z.eq_dec id i) as [->|Hne].
        * inversion Hlookup; subst node; exists i, group; split; assumption.
        * exists id, node; split; assumption.
      + exists id, node; split; assumption. }
  assert (Hcross : Ucos2Verify.lib.cross_module_invariants.cross_module_consistency sg
    (replace_FlagS (flag_pend_pool_set_bits state.(FlagState) i image bits) state)).
  { apply Ucos2Verify.lib.cross_module_invariants.cross_module_consistency_flag_nodes_frame.
    - reflexivity.
    - destruct Hinv as [_ [_ [_ [_ [Hcross _]]]]]; exact Hcross. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *.
  cbn [replace_FlagS TskState SchedState FlagState EventState IntrState MemoryState
    TimerState StatsState ControlState NameState] in *.
  tauto.
Qed.

Lemma flag_pend_group_merge_updated_bits__resume_success : forall sg state i image bits,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg state -> flag_pend_group_lookup state i image ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  flag_pool_addr sg i # UChar |-> image.(flagImageType) **
  (flag_pool_addr sg i + 8) # UShort |-> bits **
  flag_pend_group_frame sg state i image |--
  UCOS2_fields_inv sg (replace_FlagS (flag_pend_pool_set_bits state.(FlagState) i image bits) state).
Proof.
  intros sg state i image bits Hconfig Hinv Himage Hbits.
  assert (Hen : sg.(osKernelConfig).(cfgFlagEnabled) = true)
    by (rewrite Hconfig; reflexivity).
  pose proof (flag_pend_pool_bits_preserves_state_inv__resume_success sg state i image bits
    Hinv Hen Himage Hbits) as Hupdated.
  sep_apply_r_atomic (UCOS2_fields_inv_merge_replace_flag sg state
    (flag_pend_pool_set_bits state.(FlagState) i image bits) Hupdated).
  unfold flag_pend_group_frame, flag_fields_configured_rep; rewrite Hen.
  sep_apply_r_atomic (flag_fields_raw_rep_merge_updated_group sg state.(FlagState)
    (flag_pend_pool_set_bits state.(FlagState) i image bits) i (flag_image_set_bits image bits)
    (flag_pend_pool_set_bits_image state.(FlagState) i image bits)
    ltac:(intros j Hne; unfold flag_pend_pool_set_bits; cbn [flagImages];
      rewrite kernel_map_set_other by exact Hne; reflexivity) eq_refl eq_refl).
  unfold flag_group_rep, flag_pend_group_without_type_bits, flag_image_set_bits.
  cbn [flagImageType flagImageBits flagImagePadding flagImageHead flagImageName].
  unfold flag_word_rep; rewrite Hconfig; cbn [selected_kernel_configuration cfgFlagBits];
    entailer!.
Qed.

Lemma flag_pend_consume_set_bits_eq__resume_success : forall bits ready,
  0 <= bits < 65536 ->
  Z.land bits (unsigned_last_nbits (Z.lnot ready) 16) =
  flag_consume_bits selected_kernel_configuration bits ready FlagSetAll.
Proof.
  intros bits ready Hbits.
  unfold flag_consume_bits, flag_word.
  change (Z.land bits (unsigned_last_nbits (Z.lnot ready) 16) =
    unsigned_last_nbits (Z.land bits (Z.lnot ready)) 16).
  rewrite unsigned_last_nbits_land_distr by lia.
  rewrite (unsigned_last_nbits_eq bits 16) by (cbn; lia).
  reflexivity.
Qed.

Lemma flag_pend_consume_clear_bits_eq__resume_success : forall bits ready,
  Z.lor (unsigned_last_nbits bits 16) (unsigned_last_nbits ready 16) =
  flag_consume_bits selected_kernel_configuration bits ready FlagClearAll.
Proof.
  intros; unfold flag_consume_bits, flag_word.
  change (Z.lor (unsigned_last_nbits bits 16) (unsigned_last_nbits ready 16) =
    unsigned_last_nbits (Z.lor bits ready) 16).
  symmetry; apply unsigned_last_nbits_lor_distr; lia.
Qed.

Lemma flag_pend_wait_active_detached_local__resume_success :
  forall sg original call node state tid task,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_pend_current_binding state tid task ->
  flag_pend_current_ready call state ->
  encode_pend_status task.(statPend) = 0 ->
  flag_pend_wait_active sg original node call state |--
  coq_prop (flag_active_fresh_registration original call state) &&
    flag_pend_node_fields node.
Proof.
  intros sg original call node state tid task Hconfig Hbinding Hready Hstatus.
  unfold flag_pend_wait_active, flag_active_waiting; Intros.
  assert (Hr : flag_active_waiting_registration original node call state) by tauto.
  assert (Ho : flag_pend_wait_outcome original node state) by tauto.
  destruct (flag_pend_ready_detached_registration__resume_success original call node state tid task
    Hbinding Hready Hr Ho Hstatus) as [Hnone Hfresh].
  sep_apply (flag_pend_detached_receipt_to_local_fields sg state node Hconfig Hnone).
  entailer!.
Qed.

Lemma flag_pend_resume_fields_split_group__resume_success : forall sg state tid old i image,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg state ->
  flag_pend_current_binding state tid old ->
  flag_pend_group_lookup state i image ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> encode_pend_status old.(statPend) **
  tcb_field_address (task_slot_addr sg tid) TCBStat # UChar |-> encode_task_status old.(stat) **
  flag_pend_resume_frame sg state tid old |--
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  (tcb_field_address (task_slot_addr sg tid) TCBFlagsRdy # UShort |-> old.(tcbFlagsRdy) **
  (flag_pool_addr sg i # UChar |-> image.(flagImageType) **
  ((flag_pool_addr sg i + 8) # UShort |-> image.(flagImageBits) **
  flag_pend_group_current_frame sg state tid old i image))).
Proof.
  intros sg state tid old i image Hconfig Hinv Hbinding Himage.
  rewrite (flag_pend_resume_fields_merge_original__resume_success sg state tid old Hconfig Hinv Hbinding).
  sep_apply_l_atomic (flag_pend_group_split sg state i image Hconfig Himage).
  Intros.
  sep_apply_l_atomic (flag_pend_group_frame_split_current sg state tid old i image Hbinding).
  entailer!.
Qed.

Lemma flag_pend_group_current_merge_bits__resume_success : forall sg state tid old i image bits,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg state ->
  flag_pend_current_binding state tid old ->
  flag_pend_group_lookup state i image ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  (tcb_field_address (task_slot_addr sg tid) TCBFlagsRdy # UShort |-> old.(tcbFlagsRdy) **
  (flag_pool_addr sg i # UChar |-> image.(flagImageType) **
  ((flag_pool_addr sg i + 8) # UShort |-> bits **
  flag_pend_group_current_frame sg state tid old i image))) |--
  UCOS2_fields_inv sg (replace_FlagS (flag_pend_pool_set_bits state.(FlagState) i image bits) state).
Proof.
  intros sg state tid old i image bits Hconfig Hinv Hbinding Himage Hbits.
  sep_apply_r_atomic (flag_pend_group_merge_updated_bits__resume_success sg state i image bits
    Hconfig Hinv Himage Hbits).
  sepcon_assoc_change.
  sep_apply_r_atomic (flag_pend_group_frame_merge_current sg state tid old i image Hbinding).
  entailer!.
Qed.

Lemma flag_pend_group_current_merge_original__resume_success : forall sg state tid old i image,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg state ->
  flag_pend_current_binding state tid old ->
  flag_pend_group_lookup state i image ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  (tcb_field_address (task_slot_addr sg tid) TCBFlagsRdy # UShort |-> old.(tcbFlagsRdy) **
  (flag_pool_addr sg i # UChar |-> image.(flagImageType) **
  ((flag_pool_addr sg i + 8) # UShort |-> image.(flagImageBits) **
  flag_pend_group_current_frame sg state tid old i image))) |--
  UCOS2_fields_inv sg state.
Proof.
  intros sg state tid old i image Hconfig Hinv Hbinding Himage.
  sep_apply_r_atomic (flag_pend_group_merge_original sg state i image Hconfig Hinv Himage).
  sepcon_assoc_change.
  sep_apply_r_atomic (flag_pend_group_frame_merge_current sg state tid old i image Hbinding).
  entailer!.
Qed.

Lemma flag_pend_first_result_has_valid_mode__immediate_return : forall sg i requested mode delay acquired phase released,
  flag_pend_first_critical sg i requested mode delay acquired phase released ->
  phase <> FlagPendReturn 0 111 -> flag_pend_valid_mode mode.
Proof.
  intros sg i requested mode delay acquired phase released Hstep Hnot.
  unfold flag_pend_first_critical in Hstep.
  destruct (decode_flag_wait_mode (osKernelConfig sg) (Z.land mode 127)) eqn:Hdecode.
  - unfold decode_flag_wait_mode in Hdecode.
    unfold flag_pend_valid_mode.
    repeat match type of Hdecode with
    | context [if ?b then _ else _] => destruct b eqn:?; try discriminate
    end; repeat match goal with
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    end; lia.
  - destruct Hstep as [Heq _]; contradiction.
Qed.

Lemma flag_pend_saved_prefix_has_task_caller__immediate_return :
  forall environment critical sg caller call mask before i pgrp requested mode delay entered saved acquired X,
  flag_pend_public_entry environment critical sg caller call mask i pgrp requested mode delay before X ->
  flag_pend_saved_prefix environment critical sg call mask before i pgrp entered saved acquired ->
  flag_pend_valid_mode mode -> caller = FlagPendTaskCaller call.
Proof.
  intros environment critical sg caller call mask before i pgrp requested mode delay entered saved acquired X
    Hpublic Hprefix Hmode.
  destruct Hpublic as [_ [_ [_ [_ [_ [Hsource _]]]]]].
  destruct Hprefix as [Hptr [Hnest [Hlock [[image [Himage Htype]] _]]]].
  destruct caller as [task_call|view key].
  - destruct Hsource as [-> _]; reflexivity.
  - destruct Hsource as [_ Hdomain]. exfalso.
    exact (Hdomain Hptr Hnest Hlock image Himage Htype Hmode).
Qed.

Lemma flag_pend_fresh_registration_task_entry__immediate_return : forall original call state,
  flag_active_fresh_registration original call state ->
  flag_pend_task_stage call state -> flag_pend_task_entry call state.
Proof.
  intros original call state [task [[Hsame [Horigin [Hlookup [Hgen [Hactive Hclear]]]]] Hnode]] Hstage.
  split; [exact Hstage|]. destruct Hsame as [Hi [Ho Hs]].
  rewrite Hi, Ho; exact Hactive.
Qed.

Lemma flag_pend_restore_preserves_task_stage_resources__immediate_return :
  forall environment critical local sg original call saved acquired released before_heap
    (registration : OsSchedCallContext -> UCOS2_Verify_State -> Prop),
  (forall next state, registration next state -> flag_active_fresh_registration original next state) ->
  flag_pend_task_stage call released ->
  SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output environment critical local
    (fun next state => coq_prop (registration next state) && emp)
    sg (FlagPendTaskCaller call) call saved acquired released before_heap |--
  EX returned current next_local,
    coq_prop (ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg call released returned current /\
      task_tcb_init_stack_same_call returned original /\ flag_pend_task_stage returned current) &&
    flag_pend_call_world environment next_local sg returned (armv7a_irq_fiq_mask saved) current.
Proof.
  intros environment critical local sg original call saved acquired released before_heap registration
    Hfresh Hstage heap [returned_caller [returned [current [next_local [Hobservation [Hbefore [Hafter Hcompleted]]]]]]].
  pose proof (proj1 (CompletedCallerSource.flag_pend_selected_completed_source_endpoints
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcompleted)) as Hendpoint.
  assert (Hsource : flag_pend_call_source_observations environment sg
    (FlagPendTaskCaller call) call released returned current).
  { destruct Hendpoint as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
    split; [exact Hready|]. split; [exact Hidle|]. split; [exact Hnonidle|].
    split; [exact Hnormal|]. intro Horigin.
    eapply flag_pend_normal_return_control; [exact Hnormal|exact (Hcontrol Horigin)]. }
  destruct returned_caller as [next|view key]; cbn [flag_pend_caller_restore_observation] in Hobservation; [|contradiction].
  destruct Hobservation as [_ [Heq [Hrestore [Hsame Hpreserved]]]]. subst next.
  assert (Hbefore_pure : flag_pend_caller_restore_input environment critical local
    (fun next state => coq_prop (registration next state) && emp)
    sg (FlagPendTaskCaller call) call saved acquired released |-- coq_prop (registration call released)).
  { unfold flag_pend_caller_restore_input, flag_pend_active_restore_input; entailer!. }
  pose proof (Hfresh call released (Hbefore_pure before_heap Hbefore)) as Hfresh_before.
  assert (Hafter_resources : flag_pend_caller_save_input environment critical next_local
    (fun next state => coq_prop (registration next state) && emp)
    sg (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current |--
    coq_prop (registration returned current) &&
      flag_pend_call_world environment next_local sg returned (armv7a_irq_fiq_mask saved) current).
  { unfold flag_pend_caller_save_input, flag_pend_active_save_input, flag_pend_call_world.
    Intros. sep_apply_l_atomic (proj1 (os_sched_fields_save_input_closed_world
      environment critical next_local sg returned (armv7a_irq_fiq_mask saved) current)). entailer!. }
  destruct (Hafter_resources heap Hafter) as [Hregistration Hworld].
  pose proof (Hfresh returned current Hregistration) as Hfresh_after.
  pose proof (flag_pend_fresh_registration_task_entry__immediate_return original call released Hfresh_before Hstage) as Hentry.
  destruct Hsource as [Hready [_ [_ Hcontrol_caller]]].
  pose proof (PendPhaseCandidate.flag_pend_caller_return_control_task_source
    call released returned current (flag_pend_task_entry_call_source call released Hentry) Hcontrol_caller) as Hcontrol.
  assert (Hready_before : flag_pend_current_ready call released).
  { destruct Hstage as [_ [_ [_ [task [Hr [Hg Hclean]]]]]]. exists task; auto. }
  pose proof (Hready (conj (flag_pend_task_entry_call_source call released Hentry) Hready_before)) as Hready_after.
  pose proof (flag_pend_return_control_running_available call released returned current Hcontrol
    (flag_pend_task_stage_running_available call released Hstage)) as Hrunning.
  pose proof (flag_pend_fresh_ready_task_stage original returned current Hfresh_after Hready_after Hrunning) as Hstage_after.
  assert (Hsame_original : task_tcb_init_stack_same_call returned original).
  { destruct Hfresh_after as [task [[Hsame_original _] _]]; exact Hsame_original. }
  exists returned, current, next_local; split; [exact (conj Hrestore (conj Hsame_original Hstage_after))|exact Hworld].
Qed.

Lemma flag_pend_first_waiting_valid_mode__resume_return :
  forall sg i requested wait_type timeout acquired node blocked,
  flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked ->
  flag_pend_valid_mode wait_type.
Proof.
  intros sg i requested wait_type timeout acquired node blocked Hwaiting.
  unfold flag_pend_first_waiting, flag_pend_first_critical in Hwaiting.
  destruct (decode_flag_wait_mode (osKernelConfig sg) (Z.land wait_type 127))
    as [mode|] eqn:Hmode; [|destruct Hwaiting as [Hbad _]; discriminate].
  unfold decode_flag_wait_mode in Hmode; unfold flag_pend_valid_mode.
  destruct (Z.eqb (Z.land wait_type 127) 2) eqn:Htwo.
  - apply Z.eqb_eq in Htwo; lia.
  - destruct (Z.eqb (Z.land wait_type 127) 3) eqn:Hthree.
    + apply Z.eqb_eq in Hthree; lia.
    + destruct (cfgFlagClearWait (osKernelConfig sg)); [|discriminate].
      destruct (Z.eqb (Z.land wait_type 127) 0) eqn:Hzero.
      * apply Z.eqb_eq in Hzero; lia.
      * destruct (Z.eqb (Z.land wait_type 127) 1) eqn:Hone; [|discriminate].
        apply Z.eqb_eq in Hone; lia.
Qed.

Lemma flag_pend_resumed_prefix_caller_and_mask__resume_return :
  forall environment critical sg caller original mask before i pgrp requested wait_type
    timeout node reentered saved reacquired,
  flag_pend_caller_source sg caller original i pgrp wait_type before ->
  flag_pend_resumed_prefix environment critical sg original mask before i pgrp
    requested wait_type timeout node reentered saved reacquired ->
  caller = FlagPendTaskCaller original /\ interrupt_saved_value mask saved.
Proof.
  intros environment critical sg caller original mask before i pgrp requested wait_type
    timeout node reentered saved reacquired Hsource Hresumed.
  destruct Hresumed as [scheduled [entry [Hscheduled [Hsave Hcurrent]]]].
  destruct Hscheduled as [restored [released [Hwaiting_prefix [Hsched Hready]]]].
  destruct Hwaiting_prefix as [entered [first_saved [acquired [blocked [Hprefix [Hwaiting Hrestore]]]]]].
  destruct Hprefix as [Hptr [Hnest [Hlock [[image [Himage Htype]] Hrest]]]].
  pose proof (flag_pend_first_waiting_valid_mode__resume_return
    sg i requested wait_type timeout acquired node blocked Hwaiting) as Hmode.
  split.
  - destruct caller as [actual|view key].
    + destruct Hsource as [-> _]; reflexivity.
    + destruct Hsource as [_ Hdomain].
      exfalso; exact (Hdomain Hptr Hnest Hlock image Himage Htype Hmode).
  - eapply ContinuationPhaseEffects.os_sched_continuation_phase_save_effect_saved_value;
      exact Hsave.
Qed.

Lemma flag_pend_restore_fresh_resources__resume_return :
  forall environment critical local sg original reentered saved acquired cleaned before_heap,
  flag_pend_current_ready reentered cleaned -> flag_pend_task_stage reentered cleaned ->
  SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output environment critical local
    (flag_pend_fresh_observation original) sg (FlagPendTaskCaller reentered)
    reentered saved acquired cleaned before_heap |--
  EX returned current next_local,
    coq_prop (ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg reentered cleaned returned current /\
      task_tcb_init_stack_same_call returned original /\ flag_pend_task_stage returned current) &&
    (os_sched_fields_save_input environment critical next_local sg returned
      (armv7a_irq_fiq_mask saved) current ** unmap_table_rep sg).
Proof.
  intros environment critical local sg original reentered saved acquired cleaned before_heap
    Hready Hstage heap [returned_caller [returned [current [next_local
      [Hobservation [Hbefore [Hafter Hcompleted]]]]]]].
  destruct returned_caller as [actual|view key]; [|contradiction].
  destruct Hobservation as [_ [Hactual [Hrestore [Hsame Hpreserved]]]]; subst actual.
  assert (Hbefore_extract : flag_pend_caller_restore_input environment critical local
    (flag_pend_fresh_observation original) sg (FlagPendTaskCaller reentered)
    reentered saved acquired cleaned |-- coq_prop (flag_active_fresh_registration original reentered cleaned)).
  { unfold flag_pend_caller_restore_input, flag_pend_active_restore_input,
      flag_pend_fresh_observation; entailer!. }
  pose proof (Hbefore_extract before_heap Hbefore) as Hfresh_before.
  assert (Hentry : flag_pend_task_entry reentered cleaned).
  { split; [exact Hstage|].
    destruct Hfresh_before as [task [[Hcall [_ [_ [_ [Hactive _]]]]] Hnode]].
    destruct Hcall as [Hinv [Horigin Hstack]].
    rewrite Hinv, Horigin; exact Hactive. }
  pose proof (proj1 (CompletedCallerSource.flag_pend_selected_completed_source_endpoints
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcompleted)) as Hendpoint.
  assert (Hsource : flag_pend_call_source_observations environment sg
    (FlagPendTaskCaller reentered) reentered cleaned returned current).
  { destruct Hendpoint as [Hready_endpoint [Hidle [Hnonidle [Hnormal Hcontrol_endpoint]]]].
    split; [exact Hready_endpoint|]. split; [exact Hidle|]. split; [exact Hnonidle|].
    split; [exact Hnormal|]. intro Horigin.
    eapply flag_pend_normal_return_control; [exact Hnormal|exact (Hcontrol_endpoint Horigin)]. }
  destruct Hsource as [Hready_return [_ [_ Hcontrol_caller]]].
  pose proof (PendPhaseCandidate.flag_pend_caller_return_control_task_source
    reentered cleaned returned current (flag_pend_task_entry_call_source reentered cleaned Hentry) Hcontrol_caller) as Hcontrol.
  pose proof (Hready_return (conj (flag_pend_task_entry_call_source reentered cleaned Hentry) Hready)) as Hcurrent.
  pose proof (flag_pend_return_control_running_available reentered cleaned returned current Hcontrol
    (flag_pend_task_stage_running_available reentered cleaned Hstage)) as Havailable.
  assert (Hafter_extract : flag_pend_caller_save_input environment critical next_local
    (flag_pend_fresh_observation original) sg (FlagPendTaskCaller returned) returned
    (armv7a_irq_fiq_mask saved) current |--
    coq_prop (flag_active_fresh_registration original returned current) &&
    (os_sched_fields_save_input environment critical next_local sg returned
      (armv7a_irq_fiq_mask saved) current ** unmap_table_rep sg)).
  { unfold flag_pend_caller_save_input, flag_pend_active_save_input,
      flag_pend_fresh_observation; entailer!. }
  destruct (Hafter_extract heap Hafter) as [Hfresh Howned].
  exists returned, current, next_local; split; [|exact Howned].
  split; [exact Hrestore|]. split.
  - destruct Hfresh as [task [[Hcall _] Hnode]]; exact Hcall.
  - eapply flag_pend_fresh_ready_task_stage; eassumption.
Qed.

Lemma flag_pend_resumed_restore_public_post__resume_return :
  forall environment critical sg caller original mask i pgrp requested wait_type timeout
    before X local resumed_local node reentered saved reacquired cleaned ready error before_heap perr,
  flag_pend_public_entry environment critical sg caller original mask i pgrp requested wait_type timeout before X ->
  flag_pend_resumed_prefix environment critical sg original mask before i pgrp requested wait_type timeout
    node reentered saved reacquired ->
  flag_pend_resume_result sg i node wait_type reacquired ready error cleaned ->
  flag_pend_current_ready reentered cleaned -> flag_pend_task_stage reentered cleaned ->
  SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output environment critical resumed_local
    (flag_pend_fresh_observation original) sg (FlagPendTaskCaller reentered)
    reentered saved reacquired cleaned before_heap ** perr # UChar |-> error |--
  flag_pend_public_post environment local sg caller original mask perr before ready X.
Proof.
  intros environment critical sg caller original mask i pgrp requested wait_type timeout
    before X local resumed_local node reentered saved reacquired cleaned ready error before_heap perr
    Hentry Hprefix Hresume Hready Hstage.
  destruct Hentry as [Hconfig [Hptr [Hrequested [Hmode [Htimeout [Hsource Hsafe]]]]]].
  destruct (flag_pend_resumed_prefix_caller_and_mask__resume_return environment critical sg caller original
    mask before i pgrp requested wait_type timeout node reentered saved reacquired Hsource Hprefix)
    as [Hcaller [Hsaved Hmask]].
  subst caller.
  sep_apply_l_atomic (flag_pend_restore_fresh_resources__resume_return environment critical resumed_local
    sg original reentered saved reacquired cleaned before_heap Hready Hstage).
  Intros returned current next_local.
  assert (Hrestore : ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg reentered cleaned returned current) by tauto.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  assert (Hreturned_stage : flag_pend_task_stage returned current) by tauto.
  assert (Hreturn : flag_pend_return_safe ready error current X).
  { eapply flag_pend_safe_resumed_return; [exact Hprefix|exact Hresume|exact Hrestore|exact Hsafe]. }
  unfold flag_pend_public_post.
  Exists (FlagPendTaskCaller returned) current error next_local.
  rewrite Hmask.
  cbn [flag_pend_caller_world flag_pend_same_caller].
  unfold flag_pend_call_world.
  rewrite <- (os_sched_fields_save_input_closed_world
    environment critical next_local sg returned mask current).
  entailer!; tauto.
Qed.

Lemma flag_group_image_type_cases__error_returns : forall sg flags i image,
  valid_flag_state sg flags -> flags.(flagImages) i = Some image ->
  image.(flagImageType) = 0 \/ image.(flagImageType) = 5.
Proof.
  intros sg flags i image [Hpartition [Hdomain [Himages [Hused [Hfree Hnodes]]]]] Himage.
  destruct Hpartition as [Hnodup [Hfree_range Hused_range]].
  assert (Hrange : 0 <= i < sg.(osKernelConfig).(cfgMaxFlags)).
  { apply (proj1 (Hdomain i)); exists image; exact Himage. }
  destruct (in_dec Z.eq_dec i flags.(flagFree)) as [Hin|Hnotin].
  - apply in_split in Hin; destruct Hin as [pre [rest Hlist]].
    destruct (Hfree pre i rest Hlist) as [found [Hfound [Htype Hhead]]].
    rewrite Himage in Hfound; inversion Hfound; subst found; auto.
  - destruct (proj2 (Hused_range i) (conj Hrange Hnotin)) as [group Hgroup].
    destruct (Hused i group Hgroup) as [_ [_ [_ [found [Hfound [Htype Hrest]]]]]].
    rewrite Himage in Hfound; inversion Hfound; subst found; auto.
Qed.

Lemma flag_pend_revalidated_type_return__error_returns :
  forall environment critical saved_local local sg caller call entered_caller entered
    mask saved before acquired release_heap i pgrp requested mode timeout perr X,
  flag_pend_public_entry environment critical sg caller call mask i pgrp requested mode timeout before X ->
  pgrp <> 0 -> os_sched_ints before <= 0 -> os_sched_locks before <= 0 ->
  (exists observed, before.(FlagState).(flagImages) i = Some observed /\ observed.(flagImageType) = 5) ->
  flag_pend_valid_mode mode ->
  flag_pend_caller_save_observation environment critical sg caller call entered_caller entered
    mask saved before acquired ->
  flag_pend_call_source_observations environment sg caller call before entered acquired ->
  interrupt_saved_value mask saved ->
  flag_pend_first_critical sg i requested mode timeout acquired (FlagPendReturn 0 1) acquired ->
  SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output environment critical saved_local
    (flag_pend_first_observation mode call before) sg entered_caller entered saved acquired acquired release_heap **
    perr # UChar |-> 1 |--
  flag_pend_public_post environment local sg caller call mask perr before 0 X.
Proof.
  intros environment critical saved_local local sg caller call entered_caller entered
    mask saved before acquired release_heap i pgrp requested mode timeout perr X
    Hentry Hptr Hints Hlocks [observed [Hobserved Htype]] Hmode Hsave Hsave_source Hsaved Hfirst.
  destruct Hentry as [Hconfig [Haddress [Hrequested [Hmode_range [Htimeout [Hsource Hsafe]]]]]].
  destruct caller as [actual|view key].
  2: { destruct Hsource as [Hinterrupt Hdomain].
       exfalso; exact (Hdomain Hptr Hints Hlocks observed Hobserved Htype Hmode). }
  destruct Hsource as [Heq Hdomain]; subst actual.
  destruct (Hdomain Hptr Hints Hlocks observed Hobserved Htype Hmode)
    as [Htask_entry [Hidle Hnonidle]].
  destruct entered_caller as [actual|view key]; cbn [flag_pend_caller_save_observation] in Hsave;
    [|contradiction].
  destruct Hsave as [_ [Heq [Hsave_effect [Hsame_save Hsource_save]]]]; subst actual.
  rewrite (flag_pend_selected_caller_restore_output_source_open environment critical saved_local
    (flag_pend_first_observation mode call before) sg (FlagPendTaskCaller entered) entered
    saved acquired acquired release_heap).
  Intros returned_caller returned current next_local.
  match goal with
  | H : PendPhaseCandidate.flag_pend_caller_restore_observation _ _ _ _ _ _ _ _ _ /\
        flag_pend_call_source_observations _ _ _ _ _ _ _ |- _ =>
    destruct H as [Hrestore Hrestore_source]
  end.
  destruct returned_caller as [actual|view key]; cbn [PendPhaseCandidate.flag_pend_caller_restore_observation] in Hrestore;
    [|contradiction].
  destruct Hrestore as [_ [Heq [Hrestore_effect [Hsame_restore [Hpreserve Hsource_restore]]]]].
  subst actual.
  unfold flag_pend_caller_save_input, flag_pend_active_save_input, flag_pend_first_observation.
  Intros.
  match goal with H : flag_pend_first_registration mode call before returned current |- _ =>
    rename H into Hregistration end.
  destruct Hsaved as [Hsaved_range Hmask]; rewrite Hmask.
  assert (Hreturn : flag_pend_return_safe 0 1 current X).
  { eapply (flag_pend_safe_immediate_return environment critical sg call mask i pgrp requested
      mode timeout before observed entered saved acquired 0 1 acquired returned current X);
      eassumption. }
  assert (Hsame : task_tcb_init_stack_same_call returned call).
  { unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  assert (Hsource_before : kernel_call_task_source call before).
  { apply flag_pend_task_entry_call_source; exact Htask_entry. }
  assert (Hready_before : flag_pend_current_ready call before).
  { destruct Htask_entry as [[Horigin [Hrunning [Havailable [task [Hready [Hgen Hclean]]]]]] Hactive].
    exists task; auto. }
  assert (Hsource_acquired : kernel_call_task_source entered acquired).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff entered call acquired Hsame_save)).
    apply Hsource_save; exact Hsource_before. }
  destruct Hsave_source as [Hready_save [Hidle_save [Hnonidle_save Hcontrol_save_caller]]].
  pose proof (PendPhaseCandidate.flag_pend_caller_return_control_task_source
    call before entered acquired Hsource_before Hcontrol_save_caller) as Hcontrol_save.
  destruct Hrestore_source as [Hready_restore [Hidle_restore [Hnonidle_restore Hcontrol_restore_caller]]].
  pose proof (PendPhaseCandidate.flag_pend_caller_return_control_task_source
    entered acquired returned current Hsource_acquired Hcontrol_restore_caller) as Hcontrol_restore.
  assert (Hstage : flag_pend_task_stage returned current).
  { eapply (flag_pend_fresh_ready_task_stage call returned current).
    - apply Hregistration; left; exact Hmode.
    - apply Hready_restore; split; [exact Hsource_acquired|].
      apply Hready_save; auto.
    - eapply flag_pend_return_control_running_available; [exact Hcontrol_restore|].
      eapply flag_pend_return_control_running_available; [exact Hcontrol_save|].
      apply flag_pend_task_stage_running_available; exact (proj1 Htask_entry). }
  unfold flag_pend_public_post.
  Exists (FlagPendTaskCaller returned) current 1 next_local.
  cbn [flag_pend_same_caller flag_pend_caller_world].
  unfold flag_pend_call_world.
  rewrite <- (os_sched_fields_save_input_closed_world environment critical next_local sg returned mask current).
  entailer!.
Qed.
End PendManualHelpers.

Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_pend_entry_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_local_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_caller_control_spec.

Module FlagPendProtectedControl.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import PendPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma flag_pend_group_source_entry_counters : forall environment critical sg
  caller original mask saved initial i pgrp mode observed returned_caller returned
  current protected_image,
  flag_pend_caller_source sg caller original i pgrp mode initial ->
  pgrp <> 0 -> os_sched_ints initial <= 0 -> os_sched_locks initial <= 0 ->
  flag_pend_group_lookup initial i observed -> flag_pend_group_type observed = 5 ->
  flag_pend_caller_save_observation environment critical sg caller original
    returned_caller returned mask saved initial current ->
  flag_pend_call_source_observations environment sg caller original initial returned current ->
  flag_pend_group_frame sg current i protected_image |--
  coq_prop (FlagPendEntryControl.flag_pend_active_entry sg
      (flag_pend_first_observation mode original initial) current /\
    FlagPendCallerControl.flag_pend_caller_counters_zero returned_caller current) &&
  flag_pend_group_frame sg current i protected_image.
Proof.
  intros environment critical sg caller original mask saved initial i pgrp mode
    observed returned_caller returned current protected_image Hsource Hp Hints Hlocks
    Hlookup Htype Hsave Hobservations.
  assert (Hentry : FlagPendEntryControl.flag_pend_active_entry sg
    (flag_pend_first_observation mode original initial) current).
  { eapply FlagPendLocalControl.flag_pend_first_source_observations_entry;
      eassumption. }
  assert (Hbounds : flag_pend_group_frame sg current i protected_image |--
    coq_prop (0 <= os_sched_ints current /\ 0 <= os_sched_locks current)).
  { unfold flag_pend_group_frame, UCOS2_raw_rep_missing_flag,
      UCOS2_raw_rep_missing_module, UCOS2_selected_rep.
    cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep].
    unfold interrupt_inv, interrupt_in_range, os_sched_ints, os_sched_locks.
    entailer!. }
  intros heap Howned.
  split; [split; [exact Hentry|] | exact Howned].
  destruct caller as [actual|view key], returned_caller as [next|next_view next_key];
    cbn [flag_pend_caller_save_observation] in Hsave; try contradiction.
  - destruct Hsave as [Hactual [Hnext [Heffect [Hsame Hpreserved]]]].
    subst actual next.
    cbn [FlagPendCallerControl.flag_pend_caller_counters_zero].
    intros Hreturned_nonboot.
    assert (Horiginal_nonboot : original.(os_sched_call_origin) <> BootInvocation).
    { destruct Hsame as [_ [Horigin _]]. rewrite <- Horigin; exact Hreturned_nonboot. }
    destruct Hobservations as [_ [_ [_ Hcaller_control]]].
    pose proof (PendPhaseCandidate.flag_pend_caller_return_control_running_origin
      original initial returned current Horiginal_nonboot Hcaller_control) as Hcontrol.
    destruct Hcontrol as [_ [_ Hintr]].
    destruct (Hbounds heap Howned) as [Hcurrent_ints Hcurrent_locks].
    unfold os_sched_ints, os_sched_locks in *.
    rewrite <- Hintr in Hcurrent_ints, Hcurrent_locks |- *.
    lia.
  - exact I.
Qed.

End FlagPendProtectedControl.


Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.

Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_entry_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_local_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_counter_entry_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_caller_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_caller_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_inactive_program_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_inactive_entry_spec.

Module PendActiveIRQHelpers.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import PrimitiveComponent PendPhaseCandidate SelectedCallerPhaseComponent.
Import SchedulerPhaseCandidate SchedulerCalleePhaseComponent ContinuationPhaseEffects.
Import PendManualHelpers FlagPendProtectedControl.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Ltac pend_active_restrict_entry :=
  match goal with
  | H : FlagPendInactiveFirstProgram.flag_pend_public_entry
      ?E ?critical ?sg ?caller ?call ?mask ?i ?pgrp ?requested ?mode ?timeout ?before ?X |- _ =>
    apply (FlagPendInactiveFirstProgram.flag_pend_public_entry_restrict
      E critical sg caller call mask i pgrp requested mode timeout before X) in H
  end.

Lemma flag_pend_endpoint_source_observations :
  forall environment sg caller original before returned current,
  flag_pend_call_protocol.flag_pend_call_endpoint_observations environment sg
    caller original before returned current ->
  PendPhaseCandidate.flag_pend_call_source_observations environment sg
    caller original before returned current.
Proof.
  intros environment sg caller original before returned current Hendpoint.
  destruct caller; [|exact I].
  destruct Hendpoint as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  split; [exact Hready|]. split; [exact Hidle|]. split; [exact Hnonidle|].
  split; [exact Hnormal|]. intro Horigin.
  eapply flag_pend_normal_return_control; [exact Hnormal|exact (Hcontrol Horigin)].
Qed.

Lemma flag_pend_first_caller_endpoint_entry :
  forall environment sg caller original i pgrp mode before image returned acquired,
  flag_pend_caller_source sg caller original i pgrp mode before ->
  pgrp <> 0 -> before.(IntrState).(intNesting) <= 0 ->
  before.(IntrState).(lockNesting) <= 0 ->
  flag_pend_group_lookup before i image -> flag_pend_group_type image = 5 ->
  FlagPendEntryControl.flag_pend_active_entry sg
    (flag_pend_first_observation mode original before) before ->
  FlagPendActiveCaller.flag_pend_caller_endpoint_observations environment
    (flag_pend_first_observation mode original before) sg
    caller original before returned acquired ->
  FlagPendEntryControl.flag_pend_active_entry sg
    (flag_pend_first_observation mode original before) acquired.
Proof.
  intros environment sg caller original i pgrp mode before image returned acquired
    Hsource Hgroup Hints Hlocks Hlookup Htype Hentry Hendpoint.
  apply FlagPendEntryControl.FlagPendEntryFirst; intro Hcondition.
  pose proof (FlagPendActiveControl.flag_pend_first_observation_not_emp
    mode original before Hcondition) as Hnonempty.
  pose proof (FlagPendActiveControl.flag_pend_active_entry_not_emp_running
    sg (flag_pend_first_observation mode original before) before Hentry Hnonempty)
    as Hrunning.
  destruct (FlagPendLocalControl.flag_pend_source_first_task_running
    sg caller original i pgrp mode before image
    Hsource Hgroup Hints Hlocks Hlookup Htype Hcondition) as [Hcaller _].
  subst caller.
  assert (Htask_entry : flag_pend_task_entry original before).
  { destruct Hcondition as [Hmode|Htask_entry]; [|exact Htask_entry].
    exact (proj1 ((proj2 Hsource) Hgroup Hints Hlocks image Hlookup Htype Hmode)). }
  assert (Hnonboot : original.(os_sched_call_origin) <> BootInvocation).
  { destruct Htask_entry as [[Horigin _] _].
    intro Hboot; rewrite Hboot in Horigin; discriminate. }
  specialize (Hendpoint Hnonempty).
  cbn [flag_pend_call_protocol.flag_pend_call_endpoint_observations] in Hendpoint.
  destruct Hendpoint as [_ [_ [_ [_ Hcontrol]]]].
  destruct (Hcontrol Hnonboot) as [Hrunning_eq Hintr_eq].
  rewrite Hrunning_eq; exact Hrunning.
Qed.

Lemma flag_pend_active_saved_prefix :
  forall environment critical sg caller original mode mask i pgrp before image
    returned_caller returned saved acquired,
  flag_pend_valid_mode mode ->
  pgrp <> 0 -> before.(IntrState).(intNesting) <= 0 ->
  before.(IntrState).(lockNesting) <= 0 ->
  flag_pend_group_lookup before i image -> flag_pend_group_type image = 5 ->
  interrupt_saved_value mask saved ->
  FlagPendActiveCaller.flag_pend_caller_save_observation environment critical
    (flag_pend_first_observation mode original before) sg
    caller original returned_caller returned mask saved before acquired ->
  FlagPendActiveCaller.flag_pend_caller_endpoint_observations environment
    (flag_pend_first_observation mode original before) sg caller original before returned acquired ->
  FlagPendActiveCallerControl.flag_pend_active_requires_control
    (flag_pend_first_observation mode original before) /\
  PendPhaseCandidate.flag_pend_caller_save_observation environment critical sg
    caller original returned_caller returned mask saved before acquired /\
  flag_pend_call_source_observations environment sg caller original before returned acquired /\
  flag_pend_caller_saved_prefix environment critical sg caller original mask before i pgrp
    returned_caller returned saved acquired.
Proof.
  intros environment critical sg caller original mode mask i pgrp before image
    returned_caller returned saved acquired Hmode Hptr Hints Hlocks Himage Htype Hsaved Hsave Hendpoint.
  pose proof (FlagPendActiveControl.flag_pend_first_observation_not_emp
    mode original before (or_introl Hmode)) as Hnonempty.
  pose proof (FlagPendActiveCaller.flag_pend_save_observation_nonempty
    environment critical (flag_pend_first_observation mode original before) sg caller original
    returned_caller returned mask saved before acquired Hnonempty Hsave) as Hold.
  split; [exact Hnonempty|]. split; [exact Hold|].
  split; [apply flag_pend_endpoint_source_observations; exact (Hendpoint Hnonempty)|].
  split; [exact Hptr|]. split; [exact Hints|]. split; [exact Hlocks|].
  split; [exists image; auto|]. split; assumption.
Qed.

(** This lemma consumes each real Save/Restore alternative separately.
    No decision on task_entry or future return condition is assumed. *)
Lemma flag_pend_first_task_return_safe :
  forall environment critical sg original mask i pgrp requested mode timeout
    before image entered saved acquired returned current X,
  pgrp <> 0 -> before.(IntrState).(intNesting) <= 0 ->
  before.(IntrState).(lockNesting) <= 0 ->
  flag_pend_group_lookup before i image -> flag_pend_group_type image = 5 ->
  FlagPendActiveCaller.flag_pend_caller_save_observation environment critical
    (flag_pend_first_observation mode original before) sg
    (FlagPendTaskCaller original) original (FlagPendTaskCaller entered) entered
    mask saved before acquired ->
  flag_pend_first_critical sg i requested mode timeout acquired (FlagPendReturn 0 111) acquired ->
  FlagPendActiveCaller.flag_pend_caller_restore_observation environment critical
    (flag_pend_first_observation mode original before) sg
    (FlagPendTaskCaller entered) entered (FlagPendTaskCaller returned) returned acquired current ->
  FlagPendInactiveFirstProgram.flag_pend_caller_safe environment critical sg
    (FlagPendTaskCaller original) original mask i pgrp requested mode timeout before X ->
  flag_pend_return_safe 0 111 current X.
Proof.
  intros environment critical sg original mask i pgrp requested mode timeout
    before image entered saved acquired returned current X
    Hptr Hints Hlocks Himage Htype Hsave Hfirst Hrestore Hsafe.
  pose proof (proj2 (proj2 (FlagPendActiveCaller.flag_pend_task_save_observation_effect
    environment critical (flag_pend_first_observation mode original before) sg original
    (FlagPendTaskCaller entered) entered mask saved before acquired Hsave))) as Hsave_effect.
  pose proof (proj2 (proj2 (FlagPendActiveCaller.flag_pend_task_restore_observation_effect
    environment critical (flag_pend_first_observation mode original before) sg entered
    (FlagPendTaskCaller returned) returned acquired current Hrestore))) as Hrestore_effect.
  assert (Hchoice :
    (PendPhaseCandidate.flag_pend_caller_save_observation environment critical sg
       (FlagPendTaskCaller original) original (FlagPendTaskCaller entered) entered mask saved before acquired /\
     PendPhaseCandidate.flag_pend_caller_restore_observation environment critical sg
       (FlagPendTaskCaller entered) entered (FlagPendTaskCaller returned) returned acquired current) \/
    ~ (flag_pend_valid_mode mode \/ flag_pend_task_entry original before)).
  { destruct Hsave as [Holdsave|[Hempty Hrest]].
    - destruct Hrestore as [Holdrestore|[Hempty Hrest]].
      + left; auto.
      + right; intro Hcondition.
        exact (FlagPendActiveControl.flag_pend_first_observation_not_emp
          mode original before Hcondition Hempty).
    - right; intro Hcondition.
      exact (FlagPendActiveControl.flag_pend_first_observation_not_emp
        mode original before Hcondition Hempty). }
  destruct Hchoice as [[Holdsave Holdrestore]|Hfalse].
  - destruct Holdsave as [_ [_ [Htasksave _]]].
    destruct Holdrestore as [_ [_ [Htaskrestore _]]].
    pose proof (FlagPendInactiveFirstProgram.flag_pend_caller_safe_restrict
      environment critical sg (FlagPendTaskCaller original) original mask i pgrp requested
      mode timeout before X Hsafe) as Hsafe_old.
    apply flag_pend_caller_safe_task in Hsafe_old.
    eapply (flag_pend_safe_immediate_return environment critical sg original mask i pgrp
      requested mode timeout before image entered saved acquired 0 111 acquired returned current X);
      eassumption.
  - eapply (FlagPendInactiveFirstProgram.flag_pend_caller_safe_inactive_return
      environment critical sg original mask i pgrp requested mode timeout before image
      entered saved acquired returned current X); eassumption.
Qed.

Lemma flag_pend_first_task_return_stage :
  forall environment critical sg original mode before entered mask saved acquired returned current,
  FlagPendActiveCaller.flag_pend_caller_save_observation environment critical
    (flag_pend_first_observation mode original before) sg
    (FlagPendTaskCaller original) original (FlagPendTaskCaller entered) entered mask saved before acquired ->
  FlagPendActiveCaller.flag_pend_caller_endpoint_observations environment
    (flag_pend_first_observation mode original before) sg
    (FlagPendTaskCaller original) original before entered acquired ->
  FlagPendActiveCaller.flag_pend_caller_restore_observation environment critical
    (flag_pend_first_observation mode original before) sg
    (FlagPendTaskCaller entered) entered (FlagPendTaskCaller returned) returned acquired current ->
  FlagPendActiveCaller.flag_pend_caller_endpoint_observations environment
    (flag_pend_first_observation mode original before) sg
    (FlagPendTaskCaller entered) entered acquired returned current ->
  flag_pend_first_registration mode original before returned current ->
  flag_pend_task_entry original before -> flag_pend_task_stage returned current.
Proof.
  intros environment critical sg original mode before entered mask saved acquired returned current
    Hsave Hbefore_endpoint Hrestore Hafter_endpoint Hregistration Hentry.
  pose proof (FlagPendActiveControl.flag_pend_first_observation_not_emp
    mode original before (or_intror Hentry)) as Hnonempty.
  pose proof (FlagPendActiveCaller.flag_pend_save_observation_nonempty
    environment critical (flag_pend_first_observation mode original before) sg
    (FlagPendTaskCaller original) original (FlagPendTaskCaller entered) entered
    mask saved before acquired Hnonempty Hsave) as Hsave_old.
  pose proof (FlagPendActiveCaller.flag_pend_restore_observation_nonempty
    environment critical (flag_pend_first_observation mode original before) sg
    (FlagPendTaskCaller entered) entered (FlagPendTaskCaller returned) returned
    acquired current Hnonempty Hrestore) as Hrestore_old.
  destruct Hsave_old as [_ [_ [Hsave_effect [Hsame_save Hsource_save]]]].
  destruct Hrestore_old as [_ [_ [Hrestore_effect [Hsame_restore Hrest]]]].
  pose proof (flag_pend_endpoint_source_observations _ _ _ _ _ _ _
    (Hbefore_endpoint Hnonempty)) as Hsource_observations_save.
  pose proof (flag_pend_endpoint_source_observations _ _ _ _ _ _ _
    (Hafter_endpoint Hnonempty)) as Hsource_observations_restore.
  destruct Hsource_observations_save as [Hready_save [_ [_ Hcontrol_save_weak]]].
  destruct Hsource_observations_restore as [Hready_restore [_ [_ Hcontrol_restore_weak]]].
  pose proof (flag_pend_task_entry_call_source original before Hentry) as Hsource_before.
  assert (Hready_before : flag_pend_current_ready original before).
  { destruct Hentry as [[Ho [Hr [Ha [node [Hready [Hgen Hclean]]]]]] Hactive].
    exists node; auto. }
  pose proof (Hready_save (conj Hsource_before Hready_before)) as Hready_acquired.
  pose proof (proj2 (task_tcb_init_stack_same_call_source_iff entered original acquired Hsame_save)
    (Hsource_save Hsource_before)) as Hsource_acquired.
  pose proof (Hready_restore (conj Hsource_acquired Hready_acquired)) as Hready_current.
  pose proof (flag_pend_caller_return_control_task_source
    original before entered acquired Hsource_before Hcontrol_save_weak) as Hcontrol_save.
  pose proof (flag_pend_caller_return_control_task_source
    entered acquired returned current Hsource_acquired Hcontrol_restore_weak) as Hcontrol_restore.
  pose proof (flag_pend_task_stage_running_available original before (proj1 Hentry)) as Hrunning_before.
  pose proof (flag_pend_return_control_running_available original before entered acquired
    Hcontrol_save Hrunning_before) as Hrunning_acquired.
  pose proof (flag_pend_return_control_running_available entered acquired returned current
    Hcontrol_restore Hrunning_acquired) as Hrunning_current.
  eapply flag_pend_fresh_ready_task_stage.
  - exact (Hregistration (or_intror Hentry)).
  - exact Hready_current.
  - exact Hrunning_current.
Qed.

Lemma flag_pend_first_return_public_post :
  forall environment critical local acquired_local sg caller original mode mask i pgrp requested timeout
    before image entered_caller entered saved acquired release_heap perr X,
  FlagPendInactiveFirstProgram.flag_pend_public_entry environment critical sg
    caller original mask i pgrp requested mode timeout before X ->
  pgrp <> 0 -> before.(IntrState).(intNesting) <= 0 ->
  before.(IntrState).(lockNesting) <= 0 ->
  flag_pend_group_lookup before i image -> flag_pend_group_type image = 5 ->
  FlagPendActiveCaller.flag_pend_caller_save_observation environment critical
    (flag_pend_first_observation mode original before) sg
    caller original entered_caller entered mask saved before acquired ->
  FlagPendActiveCaller.flag_pend_caller_endpoint_observations environment
    (flag_pend_first_observation mode original before) sg
    caller original before entered acquired ->
  interrupt_saved_value mask saved ->
  flag_pend_first_critical sg i requested mode timeout acquired (FlagPendReturn 0 111) acquired ->
  FlagPendActiveCaller.flag_pend_selected_caller_restore_output environment critical acquired_local
    (flag_pend_first_observation mode original before) sg entered_caller entered
    saved acquired acquired release_heap ** perr # UChar |-> 111 |--
  flag_pend_public_post environment local sg caller original mask perr before 0 X.
Proof.
  intros environment critical local acquired_local sg caller original mode mask i pgrp requested timeout
    before image entered_caller entered saved acquired release_heap perr X
    Hentry Hptr Hints Hlocks Himage Htype Hsave Hbefore_endpoint Hsaved Hfirst.
  sep_apply_l_atomic (FlagPendActiveCaller.flag_pend_selected_caller_restore_output_open
    environment critical acquired_local (flag_pend_first_observation mode original before)
    sg entered_caller entered saved acquired acquired release_heap).
  Intros returned_caller returned current next_local.
  match goal with
  | H : FlagPendActiveCaller.flag_pend_caller_restore_observation _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hrestore Hafter_endpoint]
  end.
  destruct Hentry as [Hconfig [Hpointer [Hrequested [Hmode_range [Htimeout [Hcaller Hsafe]]]]]].
  destruct Hsaved as [Hsaved Hmask]; rewrite Hmask.
  destruct caller as [task_call|view key].
  - destruct Hcaller as [Heq Hdomain]; subst task_call.
    destruct (FlagPendActiveCaller.flag_pend_task_save_observation_effect
      environment critical (flag_pend_first_observation mode original before) sg original
      entered_caller entered mask saved before acquired Hsave) as [Hentered [Hsame_save Hsave_effect]].
    subst entered_caller.
    destruct (FlagPendActiveCaller.flag_pend_task_restore_observation_effect
      environment critical (flag_pend_first_observation mode original before) sg entered
      returned_caller returned acquired current Hrestore) as [Hreturned [Hsame_restore Hrestore_effect]].
    subst returned_caller.
    cbn [flag_pend_caller_save_input].
    unfold flag_pend_active_save_input, flag_pend_first_observation.
    Intros.
    match goal with H : flag_pend_first_registration _ _ _ _ _ |- _ => rename H into Hregistration end.
    assert (Hsame : task_tcb_init_stack_same_call returned original).
    { unfold task_tcb_init_stack_same_call in *; intuition congruence. }
    assert (Hstage : flag_pend_task_entry original before -> flag_pend_task_stage returned current).
    { eapply flag_pend_first_task_return_stage; eassumption. }
    assert (Hsafe_return : flag_pend_return_safe 0 111 current X).
    { eapply flag_pend_first_task_return_safe; eassumption. }
    sep_apply_l_atomic (proj1 (os_sched_fields_save_input_closed_world
      environment critical next_local sg returned mask current)).
    unfold flag_pend_public_post.
    Exists (FlagPendTaskCaller returned) current 111 next_local.
    cbn [flag_pend_same_caller flag_pend_caller_world].
    unfold flag_pend_call_world; entailer!.
  - destruct Hsave as [Hsave|[Hempty [Hbad Hrest]]]; [|discriminate Hbad].
    destruct entered_caller as [entered_task|entered_view entered_key];
      cbn [CompletedCallerEvents.flag_pend_caller_save_observation] in Hsave; [contradiction|].
    destruct Hsave as [Hentered [Hentered_key [Hview_save Hsave_interval]]].
    subst entered entered_key.
    destruct Hrestore as [Hrestore|[Hempty [Hbad Hrest]]]; [|discriminate Hbad].
    destruct returned_caller as [returned_task|returned_view returned_key];
      cbn [CompletedCallerEvents.flag_pend_caller_restore_observation] in Hrestore; [contradiction|].
    destruct Hrestore as [Hreturned [Hreturned_key [Hview_restore Hrestore_interval]]].
    subst returned returned_key.
    cbn [flag_pend_caller_save_input].
    unfold flag_pend_first_observation; Intros.
    assert (Hsame_view : sched_fields_same_view returned_view view).
    { eapply sched_fields_same_view_trans; eassumption. }
    assert (Hsafe_return : flag_pend_return_safe 0 111 current X).
    { eapply (FlagPendInactiveFirstProgram.flag_pend_caller_safe_return environment critical sg
        (FlagPendInterruptCaller view key) original mask i pgrp requested mode timeout
        before 0 111 current X); [|exact Hsafe].
      cbn [FlagPendInactiveFirstProgram.flag_pend_caller_program]; unfold flag_pend_view_program.
      rewrite (proj2 (Z.eqb_neq pgrp 0) Hptr).
      rewrite (proj2 (Z.ltb_ge 0 (intNesting (IntrState before))) Hints).
      rewrite (proj2 (Z.ltb_ge 0 (lockNesting (IntrState before))) Hlocks).
      exists image; split; [exact Himage|].
      change (flagImageType image = 5) in Htype; rewrite Htype; cbn [Z.eqb negb].
      exists entered_view, acquired, 0, 111, acquired.
      split; [exact Hview_save|]. split; [exact Hsave_interval|].
      split; [exact Hfirst|]. split; [exact Hrestore_interval|reflexivity]. }
    unfold flag_pend_public_post.
    Exists (FlagPendInterruptCaller returned_view key) current 111 next_local.
    cbn [flag_pend_same_caller]; entailer!.
    sep_apply_r_atomic (proj2 (flag_pend_caller_world_split environment next_local sg
      (FlagPendInterruptCaller returned_view key) mask current)).
    unfold flag_pend_caller_control; entailer!.
Qed.

End PendActiveIRQHelpers.



(** Current assigned proof candidates. Fixed ordinary-context checking is pending. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
From Ucos2Verify.VC.code.flag Require Import OSFlagPend_def.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.task Ucos2Verify.lib.sched Ucos2Verify.lib.flag Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_protocol_spec.
Require Import SimpleC.SL.ConAssertion Ucos2Verify.lib.task_status Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec Ucos2Verify.VC.code.flag.spec.flag_unlink_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_call_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_caller_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_entry_control_spec Ucos2Verify.VC.code.flag.spec.flag_pend_local_control_spec Ucos2Verify.VC.code.flag.spec.flag_pend_counter_entry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.lib.task_idle_ready.
Import PrimitiveComponent.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_call_spec Ucos2Verify.VC.code.flag.spec.flag_pend_active_caller_control_spec Ucos2Verify.VC.code.flag.spec.flag_pend_inactive_program_spec Ucos2Verify.VC.code.flag.spec.flag_pend_inactive_entry_spec.
Local Open Scope sac.

(*----- Function OSFlagPend -----*)


Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_callee_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_sched_entry_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_sched_phase_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_c_source_spec.

Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_caller_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_inactive_program_spec.

Module PendActiveTickHelpers.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import PrimitiveComponent PendPhaseCandidate SelectedCallerPhaseComponent.
Import SchedulerPhaseCandidate SchedulerCalleePhaseComponent ContinuationPhaseEffects.
Import PendManualHelpers FlagPendProtectedControl.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Ltac retain_original_public_entry__active_tick :=
  match goal with
  | H : FlagPendInactiveFirstProgram.flag_pend_public_entry
      ?E ?critical ?sg ?caller ?call ?mask ?i ?pgrp ?requested ?mode ?delay ?before ?X |- _ =>
    pose proof (FlagPendInactiveFirstProgram.flag_pend_public_entry_restrict
      E critical sg caller call mask i pgrp requested mode delay before X H)
      as Hlegacy_entry__active_tick
  end.

Lemma flag_pend_mode_parameters_valid__active_tick : forall original normalized consumed,
  flag_pend_mode_parameters original normalized consumed ->
  0 <= normalized <= 3 -> flag_pend_valid_mode original.
Proof.
  intros original normalized consumed [Hnormalized Hconsume] Hrange.
  unfold flag_pend_valid_mode; lia.
Qed.

End PendActiveTickHelpers.

