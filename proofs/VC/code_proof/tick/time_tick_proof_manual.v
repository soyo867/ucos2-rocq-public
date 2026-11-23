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
From Ucos2Verify.VC.code.tick Require Import time_tick_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_hook_isr_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSTimeTick_entail_wit_1_1 : OSTimeTick_entail_wit_1_1.
Proof.
  right; intros.
  rewrite time_tick_process_byte_unsigned__traversal_and_return in PreH2.
  assert (Hprocess : time_tick_process_tasks hook_state_2 = true).
  { unfold time_tick_process_byte in PreH2.
    destruct (time_tick_process_tasks hook_state_2); [reflexivity|contradiction]. }
  assert (Hbyte : time_tick_process_byte hook_state_2 = 1).
  { unfold time_tick_process_byte; rewrite Hprocess; reflexivity. }
  destruct (time_tick_cursor_initialize__traversal_and_return sg hook_state_2 PreH1 Hprocess)
    as [remaining [tid [node [Hcursor Hhead]]]].
  pose proof (proj2 (proj2 Hcursor)) as Hlookup.
  Exists (@nil Z) remaining (time_tick_clock_step_state hook_state_2) tid node
    app_after_2 counter_after_2 hook_state_2.
  sep_apply_l_atomic (time_tick_cursor_split_priority__traversal_and_return sg
    (time_tick_clock_step_state hook_state_2) tid node Hlookup).
  cbn [tcb_field_address].
  unfold time_tick_lookup; entailer!.
Qed.

Lemma proof_of_OSTimeTick_entail_wit_1_2 : OSTimeTick_entail_wit_1_2.
Proof.
  right; intros.
  rewrite time_tick_process_byte_unsigned__traversal_and_return in PreH2.
  assert (Hprocess : time_tick_process_tasks hook_state_2 = true).
  { unfold time_tick_process_byte in PreH2.
    destruct (time_tick_process_tasks hook_state_2); [reflexivity|contradiction]. }
  assert (Hbyte : time_tick_process_byte hook_state_2 = 1).
  { unfold time_tick_process_byte; rewrite Hprocess; reflexivity. }
  destruct (time_tick_cursor_initialize__traversal_and_return sg hook_state_2 PreH1 Hprocess)
    as [remaining [tid [node [Hcursor Hhead]]]].
  pose proof (proj2 (proj2 Hcursor)) as Hlookup.
  Exists (@nil Z) remaining (time_tick_clock_step_state hook_state_2) tid node
    app_after_2 counter_after_2 hook_state_2.
  sep_apply_l_atomic (time_tick_cursor_split_priority__traversal_and_return sg
    (time_tick_clock_step_state hook_state_2) tid node Hlookup).
  cbn [tcb_field_address].
  unfold time_tick_lookup; entailer!.
Qed.

Lemma proof_of_OSTimeTick_entail_wit_1_3 : OSTimeTick_entail_wit_1_3.
Proof.
  right; intros.
  rewrite time_tick_process_byte_unsigned__traversal_and_return in PreH2.
  assert (Hprocess : time_tick_process_tasks hook_state_2 = true).
  { unfold time_tick_process_byte in PreH2.
    destruct (time_tick_process_tasks hook_state_2); [reflexivity|contradiction]. }
  assert (Hbyte : time_tick_process_byte hook_state_2 = 1).
  { unfold time_tick_process_byte; rewrite Hprocess; reflexivity. }
  destruct (time_tick_cursor_initialize__traversal_and_return sg hook_state_2 PreH1 Hprocess)
    as [remaining [tid [node [Hcursor Hhead]]]].
  pose proof (proj2 (proj2 Hcursor)) as Hlookup.
  Exists (@nil Z) remaining (time_tick_clock_step_state hook_state_2) tid node
    app_after_2 counter_after_2 hook_state_2.
  sep_apply_l_atomic (time_tick_cursor_split_priority__traversal_and_return sg
    (time_tick_clock_step_state hook_state_2) tid node Hlookup).
  cbn [tcb_field_address].
  unfold time_tick_lookup; entailer!.
Qed.

Lemma proof_of_OSTimeTick_entail_wit_1_4 : OSTimeTick_entail_wit_1_4.
Proof.
  right; intros.
  rewrite time_tick_process_byte_unsigned__traversal_and_return in PreH2.
  assert (Hprocess : time_tick_process_tasks hook_state_2 = true).
  { unfold time_tick_process_byte in PreH2.
    destruct (time_tick_process_tasks hook_state_2); [reflexivity|contradiction]. }
  assert (Hbyte : time_tick_process_byte hook_state_2 = 1).
  { unfold time_tick_process_byte; rewrite Hprocess; reflexivity. }
  destruct (time_tick_cursor_initialize__traversal_and_return sg hook_state_2 PreH1 Hprocess)
    as [remaining [tid [node [Hcursor Hhead]]]].
  pose proof (proj2 (proj2 Hcursor)) as Hlookup.
  Exists (@nil Z) remaining (time_tick_clock_step_state hook_state_2) tid node
    app_after_2 counter_after_2 hook_state_2.
  sep_apply_l_atomic (time_tick_cursor_split_priority__traversal_and_return sg
    (time_tick_clock_step_state hook_state_2) tid node Hlookup).
  cbn [tcb_field_address].
  unfold time_tick_lookup; entailer!.
Qed.

Lemma proof_of_OSTimeTick_entail_wit_2_1 : OSTimeTick_entail_wit_2_1.
Proof.
  left; intros.
  assert (Hz : Z.eqb node_2.(dly) 0 = false) by (apply Z.eqb_neq; exact PreH4).
  assert (Hsub : unsigned_last_nbits (time_tick_delay node_2 - 1) 32 =
    time_tick_delay node_2 - 1).
  { apply unsigned_last_nbits_eq; cbn; lia. }
  rewrite Hsub in PreH3.
  assert (He : Z.eqb (node_2.(dly) - 1) 0 = true) by (apply Z.eqb_eq; exact PreH3).
  assert (Hnewdelay : (tick_task_update node_2).(dly) = node_2.(dly) - 1).
  { unfold tick_task_update; rewrite Hz; reflexivity. }
  assert (Hpending_bool : Z.eqb (Z.land (task_status.encode_task_status node_2.(stat)) 55) 0 = false)
    by (apply Z.eqb_neq; exact PreH2).
  assert (Hnewstatus : task.encode_task_status (tick_task_update node_2).(stat) =
    Z.land (time_tick_status node_2) (unsigned_last_nbits (Z.lnot 55) 8)).
  { unfold tick_task_update; rewrite Hz; cbn [stat]; rewrite He, task_status_after_timeout_encoding.
    unfold task_status_timeout, task_status_has_pending, task_pend_any_mask, task.encode_task_status.
    rewrite Hpending_bool; cbn [negb fst].
    apply task_status_clear_wait_byte_complement; lia. }
  assert (Hsuspended_bool :
    task_status_is_suspended (task.encode_task_status (tick_task_update node_2).(stat)) = false).
  { rewrite Hnewstatus; unfold task_status_is_suspended.
    apply negb_false_iff; apply Z.eqb_eq; exact PreH1. }
  destruct (time_tick_task_step_ready_encoding__task_update_backedges sg current_2 tid_2 node_2
    PreH7 (conj PreH8 PreH9)) as [Hgroup Hrows].
  rewrite Hz, Hnewdelay, He, Hsuspended_bool in Hgroup, Hrows.
  destruct (time_tick_bitmap_values_in_range__task_update_backedges sg current_2 tid_2 node_2
    PreH6 PreH7) as [Hgroup_range [Hrow_range [Hbitx_range Hbity_range]]].
  pose proof (time_tick_configuration_no_multi__task_update_backedges sg current_2 PreH6) as Hmulti.
  destruct (time_tick_cursor_advance__task_update_backedges sg hook_state_2 visited_2 remaining_2
    current_2 tid_2 node_2 PreH18 PreH17 PreH6 PreH12)
    as [next [rest [next_node [Hremaining [Hnext [Hcursor_next Hlookup_next]]]]]].
  pose proof (time_tick_task_step_preserves_state_inv sg tid_2 node_2 current_2 Hmulti PreH6 PreH7)
    as Hvalid_next.
  Exists (visited_2 ++ (tid_2 :: nil)) rest (tick_task_step sg tid_2 node_2 current_2) next next_node
    app_after_2 counter_after_2 hook_state_2.
  unfold time_tick_priority; cbn [tcb_field_address]; rewrite Hnext; entailer!.
  pose proof (time_tick_inv_split_priority__task_update_backedges sg
    (tick_task_step sg tid_2 node_2 current_2) next next_node Hlookup_next) as Hfocus.
  cbn [tcb_field_address] in Hfocus.
  sep_apply_r_atomic Hfocus.
  sep_apply_r_atomic (time_tick_body_merge_task_step__task_update_backedges sg current_2 tid_2 node_2
    Hmulti PreH6 PreH7).
  rewrite Hgroup, Hrows, Hsub.
    rewrite (unsigned_last_nbits_eq (time_tick_ready_group current_2) 8 Hgroup_range),
      (unsigned_last_nbits_eq (Znth (time_tick_y node_2) (time_tick_ready_rows current_2) 0)
        8 Hrow_range),
      (unsigned_last_nbits_eq (time_tick_bit_x node_2) 8 Hbitx_range),
      (unsigned_last_nbits_eq (time_tick_bit_y node_2) 8 Hbity_range).
    destruct PreH13 as [_ [_ [_ [_ [Hg Hr]]]]].
    unfold time_tick_body_cells, time_tick_delay, time_tick_status, time_tick_pend_result,
      time_tick_priority, time_tick_next, time_tick_y, time_tick_bit_x, time_tick_bit_y.
    unfold tick_task_update; rewrite Hz; cbn [dly stat statPend curPrio nextTCB].
    rewrite He, task_status_after_timeout_encoding.
    unfold task_status_timeout, task_status_has_pending, task_pend_any_mask, task.encode_task_status; rewrite Hpending_bool.
    cbn [negb fst snd task.encode_pend_status tcb_field_address].
    rewrite task_status_clear_wait_byte_complement by lia.
    rewrite Hg, Hr; unfold time_tick_next in Hnext; rewrite Hnext; entailer!.
Qed.

Lemma proof_of_OSTimeTick_entail_wit_2_2 : OSTimeTick_entail_wit_2_2.
Proof.
  left; intros.
  assert (Hz : Z.eqb node_2.(dly) 0 = false) by (apply Z.eqb_neq; exact PreH4).
  assert (Hsub : unsigned_last_nbits (time_tick_delay node_2 - 1) 32 =
    time_tick_delay node_2 - 1).
  { apply unsigned_last_nbits_eq; cbn; lia. }
  rewrite Hsub in PreH3.
  assert (He : Z.eqb (node_2.(dly) - 1) 0 = true) by (apply Z.eqb_eq; exact PreH3).
  assert (Hnewdelay : (tick_task_update node_2).(dly) = node_2.(dly) - 1).
  { unfold tick_task_update; rewrite Hz; reflexivity. }
  assert (Hpending_bool : Z.eqb (Z.land (task_status.encode_task_status node_2.(stat)) 55) 0 = true)
    by (apply Z.eqb_eq; exact PreH2).
  assert (Hnewstatus : task.encode_task_status (tick_task_update node_2).(stat) = time_tick_status node_2).
  { unfold tick_task_update; rewrite Hz; cbn [stat]; rewrite He, task_status_after_timeout_encoding.
    unfold task_status_timeout, task_status_has_pending, task_pend_any_mask, task.encode_task_status.
    rewrite Hpending_bool; reflexivity. }
  assert (Hsuspended_bool :
    task_status_is_suspended (task.encode_task_status (tick_task_update node_2).(stat)) = false).
  { rewrite Hnewstatus; unfold task_status_is_suspended.
    apply negb_false_iff; apply Z.eqb_eq; exact PreH1. }
  destruct (time_tick_task_step_ready_encoding__task_update_backedges sg current_2 tid_2 node_2
    PreH7 (conj PreH8 PreH9)) as [Hgroup Hrows].
  rewrite Hz, Hnewdelay, He, Hsuspended_bool in Hgroup, Hrows.
  destruct (time_tick_bitmap_values_in_range__task_update_backedges sg current_2 tid_2 node_2
    PreH6 PreH7) as [Hgroup_range [Hrow_range [Hbitx_range Hbity_range]]].
  pose proof (time_tick_configuration_no_multi__task_update_backedges sg current_2 PreH6) as Hmulti.
  destruct (time_tick_cursor_advance__task_update_backedges sg hook_state_2 visited_2 remaining_2
    current_2 tid_2 node_2 PreH18 PreH17 PreH6 PreH12)
    as [next [rest [next_node [Hremaining [Hnext [Hcursor_next Hlookup_next]]]]]].
  pose proof (time_tick_task_step_preserves_state_inv sg tid_2 node_2 current_2 Hmulti PreH6 PreH7)
    as Hvalid_next.
  Exists (visited_2 ++ (tid_2 :: nil)) rest (tick_task_step sg tid_2 node_2 current_2) next next_node
    app_after_2 counter_after_2 hook_state_2.
  unfold time_tick_priority; cbn [tcb_field_address]; rewrite Hnext; entailer!.
  pose proof (time_tick_inv_split_priority__task_update_backedges sg
    (tick_task_step sg tid_2 node_2 current_2) next next_node Hlookup_next) as Hfocus.
  cbn [tcb_field_address] in Hfocus.
  sep_apply_r_atomic Hfocus.
  sep_apply_r_atomic (time_tick_body_merge_task_step__task_update_backedges sg current_2 tid_2 node_2
    Hmulti PreH6 PreH7).
  rewrite Hgroup, Hrows, Hsub.
    rewrite (unsigned_last_nbits_eq (time_tick_ready_group current_2) 8 Hgroup_range),
      (unsigned_last_nbits_eq (Znth (time_tick_y node_2) (time_tick_ready_rows current_2) 0)
        8 Hrow_range),
      (unsigned_last_nbits_eq (time_tick_bit_x node_2) 8 Hbitx_range),
      (unsigned_last_nbits_eq (time_tick_bit_y node_2) 8 Hbity_range).
    destruct PreH13 as [_ [_ [_ [_ [Hg Hr]]]]].
    unfold time_tick_body_cells, time_tick_delay, time_tick_status, time_tick_pend_result,
      time_tick_priority, time_tick_next, time_tick_y, time_tick_bit_x, time_tick_bit_y.
    unfold tick_task_update; rewrite Hz; cbn [dly stat statPend curPrio nextTCB].
    rewrite He, task_status_after_timeout_encoding.
    unfold task_status_timeout, task_status_has_pending, task_pend_any_mask, task.encode_task_status; rewrite Hpending_bool.
    cbn [negb fst snd task.encode_pend_status tcb_field_address]; rewrite Hg, Hr; unfold time_tick_next in Hnext; rewrite Hnext; entailer!.
Qed.

Lemma proof_of_OSTimeTick_entail_wit_2_3 : OSTimeTick_entail_wit_2_3.
Proof.
  left; intros.
  assert (Hz : Z.eqb node_2.(dly) 0 = false) by (apply Z.eqb_neq; exact PreH4).
  assert (Hsub : unsigned_last_nbits (time_tick_delay node_2 - 1) 32 =
    time_tick_delay node_2 - 1).
  { apply unsigned_last_nbits_eq; cbn; lia. }
  rewrite Hsub in PreH3.
  assert (He : Z.eqb (node_2.(dly) - 1) 0 = true) by (apply Z.eqb_eq; exact PreH3).
  assert (Hnewdelay : (tick_task_update node_2).(dly) = node_2.(dly) - 1).
  { unfold tick_task_update; rewrite Hz; reflexivity. }
  assert (Hpending_bool : Z.eqb (Z.land (task_status.encode_task_status node_2.(stat)) 55) 0 = true)
    by (apply Z.eqb_eq; exact PreH2).
  assert (Hnewstatus : task.encode_task_status (tick_task_update node_2).(stat) = time_tick_status node_2).
  { unfold tick_task_update; rewrite Hz; cbn [stat]; rewrite He, task_status_after_timeout_encoding.
    unfold task_status_timeout, task_status_has_pending, task_pend_any_mask, task.encode_task_status.
    rewrite Hpending_bool; reflexivity. }
  assert (Hsuspended_bool :
    task_status_is_suspended (task.encode_task_status (tick_task_update node_2).(stat)) = true).
  { rewrite Hnewstatus; unfold task_status_is_suspended.
    apply negb_true_iff; apply Z.eqb_neq; exact PreH1. }
  destruct (time_tick_task_step_ready_encoding__task_update_backedges sg current_2 tid_2 node_2
    PreH7 (conj PreH8 PreH9)) as [Hgroup Hrows].
  rewrite Hz, Hnewdelay, He, Hsuspended_bool in Hgroup, Hrows.
  pose proof (time_tick_configuration_no_multi__task_update_backedges sg current_2 PreH6) as Hmulti.
  destruct (time_tick_cursor_advance__task_update_backedges sg hook_state_2 visited_2 remaining_2
    current_2 tid_2 node_2 PreH18 PreH17 PreH6 PreH12)
    as [next [rest [next_node [Hremaining [Hnext [Hcursor_next Hlookup_next]]]]]].
  pose proof (time_tick_task_step_preserves_state_inv sg tid_2 node_2 current_2 Hmulti PreH6 PreH7)
    as Hvalid_next.
  Exists (visited_2 ++ (tid_2 :: nil)) rest (tick_task_step sg tid_2 node_2 current_2) next next_node
    app_after_2 counter_after_2 hook_state_2.
  unfold time_tick_priority; cbn [tcb_field_address]; rewrite Hnext; entailer!.
  pose proof (time_tick_inv_split_priority__task_update_backedges sg
    (tick_task_step sg tid_2 node_2 current_2) next next_node Hlookup_next) as Hfocus.
  cbn [tcb_field_address] in Hfocus.
  sep_apply_r_atomic Hfocus.
  sep_apply_r_atomic (time_tick_body_merge_task_step__task_update_backedges sg current_2 tid_2 node_2
    Hmulti PreH6 PreH7).
  rewrite Hgroup, Hrows, Hsub.
    destruct PreH13 as [_ [_ [_ [_ [Hg Hr]]]]].
    unfold time_tick_body_cells, time_tick_delay, time_tick_status, time_tick_pend_result,
      time_tick_priority, time_tick_next, time_tick_y, time_tick_bit_x, time_tick_bit_y.
    unfold tick_task_update; rewrite Hz; cbn [dly stat statPend curPrio nextTCB].
    rewrite He, task_status_after_timeout_encoding.
    unfold task_status_timeout, task_status_has_pending, task_pend_any_mask, task.encode_task_status; rewrite Hpending_bool.
    cbn [negb fst snd task.encode_pend_status tcb_field_address]; rewrite Hg, Hr; unfold time_tick_next in Hnext; rewrite Hnext; entailer!.
Qed.

Lemma proof_of_OSTimeTick_entail_wit_2_4 : OSTimeTick_entail_wit_2_4.
Proof.
  left; intros.
  assert (Hz : Z.eqb node_2.(dly) 0 = false) by (apply Z.eqb_neq; exact PreH4).
  assert (Hsub : unsigned_last_nbits (time_tick_delay node_2 - 1) 32 =
    time_tick_delay node_2 - 1).
  { apply unsigned_last_nbits_eq; cbn; lia. }
  rewrite Hsub in PreH3.
  assert (He : Z.eqb (node_2.(dly) - 1) 0 = true) by (apply Z.eqb_eq; exact PreH3).
  assert (Hnewdelay : (tick_task_update node_2).(dly) = node_2.(dly) - 1).
  { unfold tick_task_update; rewrite Hz; reflexivity. }
  assert (Hpending_bool : Z.eqb (Z.land (task_status.encode_task_status node_2.(stat)) 55) 0 = false)
    by (apply Z.eqb_neq; exact PreH2).
  assert (Hnewstatus : task.encode_task_status (tick_task_update node_2).(stat) =
    Z.land (time_tick_status node_2) (unsigned_last_nbits (Z.lnot 55) 8)).
  { unfold tick_task_update; rewrite Hz; cbn [stat]; rewrite He, task_status_after_timeout_encoding.
    unfold task_status_timeout, task_status_has_pending, task_pend_any_mask, task.encode_task_status.
    rewrite Hpending_bool; cbn [negb fst].
    apply task_status_clear_wait_byte_complement; lia. }
  assert (Hsuspended_bool :
    task_status_is_suspended (task.encode_task_status (tick_task_update node_2).(stat)) = true).
  { rewrite Hnewstatus; unfold task_status_is_suspended.
    apply negb_true_iff; apply Z.eqb_neq; exact PreH1. }
  destruct (time_tick_task_step_ready_encoding__task_update_backedges sg current_2 tid_2 node_2
    PreH7 (conj PreH8 PreH9)) as [Hgroup Hrows].
  rewrite Hz, Hnewdelay, He, Hsuspended_bool in Hgroup, Hrows.
  pose proof (time_tick_configuration_no_multi__task_update_backedges sg current_2 PreH6) as Hmulti.
  destruct (time_tick_cursor_advance__task_update_backedges sg hook_state_2 visited_2 remaining_2
    current_2 tid_2 node_2 PreH18 PreH17 PreH6 PreH12)
    as [next [rest [next_node [Hremaining [Hnext [Hcursor_next Hlookup_next]]]]]].
  pose proof (time_tick_task_step_preserves_state_inv sg tid_2 node_2 current_2 Hmulti PreH6 PreH7)
    as Hvalid_next.
  Exists (visited_2 ++ (tid_2 :: nil)) rest (tick_task_step sg tid_2 node_2 current_2) next next_node
    app_after_2 counter_after_2 hook_state_2.
  unfold time_tick_priority; cbn [tcb_field_address]; rewrite Hnext; entailer!.
  pose proof (time_tick_inv_split_priority__task_update_backedges sg
    (tick_task_step sg tid_2 node_2 current_2) next next_node Hlookup_next) as Hfocus.
  cbn [tcb_field_address] in Hfocus.
  sep_apply_r_atomic Hfocus.
  sep_apply_r_atomic (time_tick_body_merge_task_step__task_update_backedges sg current_2 tid_2 node_2
    Hmulti PreH6 PreH7).
  rewrite Hgroup, Hrows, Hsub.
    destruct PreH13 as [_ [_ [_ [_ [Hg Hr]]]]].
    unfold time_tick_body_cells, time_tick_delay, time_tick_status, time_tick_pend_result,
      time_tick_priority, time_tick_next, time_tick_y, time_tick_bit_x, time_tick_bit_y.
    unfold tick_task_update; rewrite Hz; cbn [dly stat statPend curPrio nextTCB].
    rewrite He, task_status_after_timeout_encoding.
    unfold task_status_timeout, task_status_has_pending, task_pend_any_mask, task.encode_task_status; rewrite Hpending_bool.
    cbn [negb fst snd task.encode_pend_status tcb_field_address].
    rewrite task_status_clear_wait_byte_complement by lia.
    rewrite Hg, Hr; unfold time_tick_next in Hnext; rewrite Hnext; entailer!.
Qed.

Lemma proof_of_OSTimeTick_entail_wit_2_5 : OSTimeTick_entail_wit_2_5.
Proof.
  left; intros.
  assert (Hz : Z.eqb node_2.(dly) 0 = false) by (apply Z.eqb_neq; exact PreH2).
  assert (Hsub : unsigned_last_nbits (time_tick_delay node_2 - 1) 32 =
    time_tick_delay node_2 - 1).
  { apply unsigned_last_nbits_eq; cbn; lia. }
  rewrite Hsub in PreH1.
  assert (He : Z.eqb (node_2.(dly) - 1) 0 = false) by (apply Z.eqb_neq; exact PreH1).
  assert (Hnewdelay : (tick_task_update node_2).(dly) = node_2.(dly) - 1).
  { unfold tick_task_update; rewrite Hz; reflexivity. }
  destruct (time_tick_task_step_ready_encoding__task_update_backedges sg current_2 tid_2 node_2
    PreH5 (conj PreH6 PreH7)) as [Hgroup Hrows].
  rewrite Hz, Hnewdelay, He in Hgroup, Hrows.
  pose proof (time_tick_configuration_no_multi__task_update_backedges sg current_2 PreH4) as Hmulti.
  destruct (time_tick_cursor_advance__task_update_backedges sg hook_state_2 visited_2 remaining_2
    current_2 tid_2 node_2 PreH16 PreH15 PreH4 PreH10)
    as [next [rest [next_node [Hremaining [Hnext [Hcursor_next Hlookup_next]]]]]].
  pose proof (time_tick_task_step_preserves_state_inv sg tid_2 node_2 current_2 Hmulti PreH4 PreH5)
    as Hvalid_next.
  Exists (visited_2 ++ (tid_2 :: nil)) rest (tick_task_step sg tid_2 node_2 current_2) next next_node
    app_after_2 counter_after_2 hook_state_2.
  unfold time_tick_priority; cbn [tcb_field_address]; rewrite Hnext; entailer!.
  pose proof (time_tick_inv_split_priority__task_update_backedges sg
    (tick_task_step sg tid_2 node_2 current_2) next next_node Hlookup_next) as Hfocus.
  cbn [tcb_field_address] in Hfocus.
  sep_apply_r_atomic Hfocus.
  sep_apply_r_atomic (time_tick_body_merge_task_step__task_update_backedges sg current_2 tid_2 node_2
    Hmulti PreH4 PreH5).
  rewrite Hgroup, Hrows, Hsub.
    destruct PreH11 as [_ [_ [_ [_ [Hg Hr]]]]].
    unfold time_tick_body_cells, time_tick_delay, time_tick_status, time_tick_pend_result,
      time_tick_priority, time_tick_next, time_tick_y, time_tick_bit_x, time_tick_bit_y.
    unfold tick_task_update; rewrite Hz; cbn [dly stat statPend curPrio nextTCB].
    rewrite He; cbn [tcb_field_address]; rewrite Hg, Hr; unfold time_tick_next in Hnext; rewrite Hnext; entailer!.
Qed.

Lemma proof_of_OSTimeTick_entail_wit_2_6 : OSTimeTick_entail_wit_2_6.
Proof.
  left; intros.
  pose proof (time_tick_configuration_no_multi__task_update_backedges sg current_2 PreH3) as Hmulti.
  destruct (time_tick_cursor_advance__task_update_backedges sg hook_state_2 visited_2 remaining_2
    current_2 tid_2 node_2 PreH15 PreH14 PreH3 PreH9)
    as [next [rest [next_node [Hremaining [Hnext [Hcursor_next Hlookup_next]]]]]].
  pose proof (time_tick_task_step_preserves_state_inv sg tid_2 node_2 current_2 Hmulti PreH3 PreH4)
    as Hvalid_next.
  Exists (visited_2 ++ (tid_2 :: nil)) rest (tick_task_step sg tid_2 node_2 current_2) next next_node
    app_after_2 counter_after_2 hook_state_2.
  unfold time_tick_priority; cbn [tcb_field_address]; rewrite Hnext; entailer!.
  pose proof (time_tick_inv_split_priority__task_update_backedges sg
    (tick_task_step sg tid_2 node_2 current_2) next next_node Hlookup_next) as Hfocus.
  cbn [tcb_field_address] in Hfocus.
  sep_apply_r_atomic Hfocus.
  sep_apply_r_atomic (time_tick_body_merge_task_step__task_update_backedges sg current_2 tid_2 node_2
    Hmulti PreH3 PreH4).
  rewrite tick_task_zero_delay_eq, tick_task_step_zero_delay_eq by exact PreH1.
    destruct PreH10 as [_ [_ [_ [_ [Hg Hr]]]]].
    unfold time_tick_body_cells, time_tick_delay, time_tick_status, time_tick_pend_result,
      time_tick_priority, time_tick_next, time_tick_y, time_tick_bit_x, time_tick_bit_y.
    cbn [tcb_field_address]; rewrite Hg, Hr; unfold time_tick_next in Hnext; rewrite Hnext; entailer!.
Qed.

Lemma proof_of_OSTimeTick_return_wit_1 : OSTimeTick_return_wit_1.
Proof.
  left; intros.
  rewrite time_tick_process_byte_unsigned__traversal_and_return in PreH1.
  assert (Hprocess : time_tick_process_tasks hook_state = false).
  { unfold time_tick_process_byte in PreH1.
    destruct (time_tick_process_tasks hook_state); [discriminate|reflexivity]. }
  assert (Hendpoint : time_tick_serialized_after_hook sg hook_state =
    time_tick_clock_step_state hook_state).
  { unfold time_tick_serialized_after_hook; rewrite Hprocess; reflexivity. }
  rewrite <- Hendpoint.
  eapply time_tick_owned_entails_post__traversal_and_return; eassumption.
Qed.

Lemma proof_of_OSTimeTick_return_wit_2 : OSTimeTick_return_wit_2.
Proof.
  left; intros.
  rewrite time_tick_process_byte_unsigned__traversal_and_return in PreH1.
  assert (Hprocess : time_tick_process_tasks hook_state = false).
  { unfold time_tick_process_byte in PreH1.
    destruct (time_tick_process_tasks hook_state); [discriminate|reflexivity]. }
  assert (Hendpoint : time_tick_serialized_after_hook sg hook_state =
    time_tick_clock_step_state hook_state).
  { unfold time_tick_serialized_after_hook; rewrite Hprocess; reflexivity. }
  rewrite <- Hendpoint.
  eapply time_tick_owned_entails_post__traversal_and_return; eassumption.
Qed.

Lemma proof_of_OSTimeTick_return_wit_3 : OSTimeTick_return_wit_3.
Proof.
  left; intros.
  rewrite time_tick_process_byte_unsigned__traversal_and_return in PreH1.
  assert (Hprocess : time_tick_process_tasks hook_state = false).
  { unfold time_tick_process_byte in PreH1.
    destruct (time_tick_process_tasks hook_state); [discriminate|reflexivity]. }
  assert (Hendpoint : time_tick_serialized_after_hook sg hook_state =
    time_tick_clock_step_state hook_state).
  { unfold time_tick_serialized_after_hook; rewrite Hprocess; reflexivity. }
  rewrite <- Hendpoint.
  eapply time_tick_owned_entails_post__traversal_and_return; eassumption.
Qed.

Lemma proof_of_OSTimeTick_return_wit_4 : OSTimeTick_return_wit_4.
Proof.
  left; intros.
  rewrite time_tick_process_byte_unsigned__traversal_and_return in PreH1.
  assert (Hprocess : time_tick_process_tasks hook_state = false).
  { unfold time_tick_process_byte in PreH1.
    destruct (time_tick_process_tasks hook_state); [discriminate|reflexivity]. }
  assert (Hendpoint : time_tick_serialized_after_hook sg hook_state =
    time_tick_clock_step_state hook_state).
  { unfold time_tick_serialized_after_hook; rewrite Hprocess; reflexivity. }
  rewrite <- Hendpoint.
  eapply time_tick_owned_entails_post__traversal_and_return; eassumption.
Qed.

Lemma proof_of_OSTimeTick_return_wit_5 : OSTimeTick_return_wit_5.
Proof.
  left; intros.
  assert (Hprocess : time_tick_process_tasks hook_state = true).
  { unfold time_tick_process_byte in PreH6.
    destruct (time_tick_process_tasks hook_state); [reflexivity|discriminate]. }
  assert (Hlowest : sg.(osLowestPrio) = 63).
  { destruct PreH3 as [_ [Hlowest _]]; exact Hlowest. }
  assert (Hpriority : time_tick_priority node = sg.(osLowestPrio)) by congruence.
  pose proof (time_tick_cursor_idle_endpoint__traversal_and_return sg hook_state
    visited remaining current tid node PreH7 Hprocess PreH8 Hpriority) as Hendpoint.
  pose proof (time_tick_cursor_merge_priority__traversal_and_return sg current tid node
    PreH8 PreH9) as Hmerge.
  cbn [tcb_field_address] in Hmerge.
  sep_apply_l_atomic Hmerge.
  rewrite Hendpoint.
  pose proof (time_tick_return_continuation (time_tick_fixed_application sg application) sg app_value counter initial X
    app_after counter_after hook_state PreH4 PreH5) as HX.
  unfold time_tick_post.
  Exists app_after counter_after hook_state.
  unfold time_tick_owned, time_tick_client_frame; entailer!.
Qed.

Lemma proof_of_OSTimeTick_return_wit_6 : OSTimeTick_return_wit_6.
Proof.
  left; intros.
  rewrite time_tick_running_unsigned__traversal_and_return in PreH1.
  assert (Hrunning : hook_state.(SchedState).(isRunning) = false).
  { unfold time_tick_running in PreH1.
    destruct hook_state.(SchedState).(isRunning); [contradiction|reflexivity]. }
  unfold time_tick_global_addresses in PreH16.
  destruct PreH16 as [_ [_ [Haddress _]]].
  rewrite Haddress.
  replace (time_tick_running hook_state) with
    (time_tick_running (time_tick_counted_state hook_state)) by reflexivity.
  sep_apply_l_atomic (time_tick_running_merge__traversal_and_return sg
    (time_tick_counted_state hook_state) PreH2).
  rewrite <- (time_tick_serialized_after_hook_not_running sg hook_state Hrunning).
  pose proof (time_tick_return_continuation (time_tick_fixed_application sg application) sg app_value counter initial X
    app_after counter_after hook_state PreH10 PreH8) as HX.
  unfold time_tick_post.
  Exists app_after counter_after hook_state.
  unfold time_tick_owned, time_tick_client_frame; entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_6_pure : OSTimeTick_partial_solve_wit_6_pure.
Proof.
  left; intros.
  assert (Hrem : unsigned_last_nbits (time_tick_time hook_state + 1) 32 =
    Z.rem (time_tick_time hook_state + 1) 4294967296).
  { unfold unsigned_last_nbits.
    change ((time_tick_time hook_state + 1) mod 4294967296 =
      Z.rem (time_tick_time hook_state + 1) 4294967296).
    rewrite Z.rem_mod_nonneg by lia; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_11_pure : OSTimeTick_partial_solve_wit_11_pure.
Proof.
  left; intros.
  assert (Hrunning_byte : unsigned_last_nbits (time_tick_running hook_state) 32 = 1)
    by assumption.
  rewrite time_tick_running_unsigned__traversal_and_return in Hrunning_byte.
  assert (Hrun : hook_state.(SchedState).(isRunning) = true).
  { unfold time_tick_running in Hrunning_byte.
    destruct hook_state.(SchedState).(isRunning); [reflexivity|discriminate]. }
  pose proof (time_tick_running_step_cases hook_state Hrun) as Hdecision.
  assert (Hstep : tick_step_decision hook_state.(TickState).(tickStepState) =
    (true, 0)).
  { apply time_tick_step_invalid; unfold time_tick_step in *; lia. }
  rewrite Hstep in Hdecision.
  injection Hdecision as Hprocess Hnext.
  change (time_tick_step (time_tick_clock_step_state hook_state) = 0) in Hnext.
  unfold time_tick_process_byte, time_tick_running.
  rewrite Hprocess, Hnext, Hrun; entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_12_pure : OSTimeTick_partial_solve_wit_12_pure.
Proof.
  left; intros.
  assert (Hrunning_byte : unsigned_last_nbits (time_tick_running hook_state) 32 = 1)
    by assumption.
  rewrite time_tick_running_unsigned__traversal_and_return in Hrunning_byte.
  assert (Hrun : hook_state.(SchedState).(isRunning) = true).
  { unfold time_tick_running in Hrunning_byte.
    destruct hook_state.(SchedState).(isRunning); [reflexivity|discriminate]. }
  pose proof (time_tick_running_step_cases hook_state Hrun) as Hdecision.
  assert (Hsource_step : time_tick_step hook_state = 2) by congruence.
  unfold time_tick_step in Hsource_step.
  rewrite Hsource_step in Hdecision; cbn [tick_step_decision] in Hdecision.
  injection Hdecision as Hprocess Hnext.
  change (time_tick_step (time_tick_clock_step_state hook_state) = 1) in Hnext.
  unfold time_tick_process_byte, time_tick_running.
  rewrite Hprocess, Hnext, Hrun; entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_13_pure : OSTimeTick_partial_solve_wit_13_pure.
Proof.
  left; intros.
  assert (Hrunning_byte : unsigned_last_nbits (time_tick_running hook_state) 32 = 1)
    by assumption.
  rewrite time_tick_running_unsigned__traversal_and_return in Hrunning_byte.
  assert (Hrun : hook_state.(SchedState).(isRunning) = true).
  { unfold time_tick_running in Hrunning_byte.
    destruct hook_state.(SchedState).(isRunning); [reflexivity|discriminate]. }
  pose proof (time_tick_running_step_cases hook_state Hrun) as Hdecision.
  assert (Hsource_step : time_tick_step hook_state = 1) by congruence.
  unfold time_tick_step in Hsource_step.
  rewrite Hsource_step in Hdecision; cbn [tick_step_decision] in Hdecision.
  injection Hdecision as Hprocess Hnext.
  change (time_tick_step (time_tick_clock_step_state hook_state) = 1) in Hnext.
  unfold time_tick_process_byte, time_tick_running.
  rewrite Hprocess, Hnext, Hrun; entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_14_pure : OSTimeTick_partial_solve_wit_14_pure.
Proof.
  left; intros.
  assert (Hrunning_byte : unsigned_last_nbits (time_tick_running hook_state) 32 = 1)
    by assumption.
  rewrite time_tick_running_unsigned__traversal_and_return in Hrunning_byte.
  assert (Hrun : hook_state.(SchedState).(isRunning) = true).
  { unfold time_tick_running in Hrunning_byte.
    destruct hook_state.(SchedState).(isRunning); [reflexivity|discriminate]. }
  pose proof (time_tick_running_step_cases hook_state Hrun) as Hdecision.
  assert (Hsource_step : time_tick_step hook_state = 0) by congruence.
  unfold time_tick_step in Hsource_step.
  rewrite Hsource_step in Hdecision; cbn [tick_step_decision] in Hdecision.
  injection Hdecision as Hprocess Hnext.
  change (time_tick_step (time_tick_clock_step_state hook_state) = 0) in Hnext.
  unfold time_tick_process_byte, time_tick_running.
  rewrite Hprocess, Hnext, Hrun; entailer!.
Qed.

Lemma proof_of_OSTimeTick_which_implies_wit_1 : OSTimeTick_which_implies_wit_1.
Proof.
  unfold OSTimeTick_which_implies_wit_1; left; intros.
  unfold time_tick_pre, time_tick_continuation, time_tick_owned, store_ushort.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_which_implies_wit_2 : OSTimeTick_which_implies_wit_2.
Proof.
  unfold OSTimeTick_which_implies_wit_2; left; intros.
  unfold time_tick_hook_isr_post; Intros counter_after hook_state.
  Exists app_value counter_after hook_state.
  unfold time_tick_owned, time_tick_client_frame; rewrite PreH1; entailer!.
Qed.

Lemma proof_of_OSTimeTick_which_implies_wit_3 : OSTimeTick_which_implies_wit_3.
Proof.
  left; intros.
  unfold time_tick_global_addresses in PreH1.
  destruct PreH1 as [Htime _]; rewrite Htime.
  rewrite UCOS2_inv_split_tick.
  unfold tick_inv, store_tick_state, time_tick_time,
    time_tick_step, time_tick_without_time; entailer!.
Qed.

Lemma proof_of_OSTimeTick_which_implies_wit_4 : OSTimeTick_which_implies_wit_4.
Proof.
  left; intros.
  unfold time_tick_global_addresses in PreH1.
  destruct PreH1 as [Htime _]; rewrite Htime.
  rewrite Z.rem_mod_nonneg by lia.
  apply time_tick_merge_counted; [exact PreH2|lia].
Qed.

Lemma proof_of_OSTimeTick_which_implies_wit_5 : OSTimeTick_which_implies_wit_5.
Proof.
  left; intros.
  unfold time_tick_global_addresses in PreH1.
  destruct PreH1 as [_ [_ [Hrunning _]]]; rewrite Hrunning.
  rewrite time_tick_running_resources.
  unfold time_tick_running, time_tick_counted_state.
  cbn [replace_TickS SchedState]; entailer!.
Qed.

Lemma proof_of_OSTimeTick_which_implies_wit_6 : OSTimeTick_which_implies_wit_6.
Proof.
  left; intros.
  unfold time_tick_global_addresses in PreH1.
  destruct PreH1 as [_ [_ [Hrunning _]]]; rewrite Hrunning.
  rewrite time_tick_running_resources.
  unfold time_tick_running, time_tick_counted_state.
  cbn [replace_TickS SchedState]; entailer!.
Qed.

Lemma proof_of_OSTimeTick_which_implies_wit_7 : OSTimeTick_which_implies_wit_7.
Proof.
  left; intros.
  unfold time_tick_global_addresses in PreH1.
  destruct PreH1 as [_ [Hstep _]]; rewrite Hstep.
  sep_apply (time_tick_split_step sg (time_tick_counted_state hook_state)).
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_which_implies_wit_8 : OSTimeTick_which_implies_wit_8.
Proof.
  right; intros.
  unfold time_tick_global_addresses in PreH1.
  destruct PreH1 as [_ [Hstep _]]; rewrite Hstep.
  assert (Hrun : hook_state.(SchedState).(isRunning) = true).
  { unfold time_tick_running in PreH2.
    destruct hook_state.(SchedState).(isRunning); [reflexivity|discriminate]. }
  assert (Hrange : 0 <= time_tick_step (time_tick_clock_step_state hook_state) < 256).
  { unfold time_tick_step, time_tick_clock_step_state, tick_step_advance.
    rewrite Hrun; unfold tick_step_decision.
    destruct (Z.eqb hook_state.(TickState).(tickStepState) 0);
      [|destruct (Z.eqb hook_state.(TickState).(tickStepState) 1);
        [|destruct (Z.eqb hook_state.(TickState).(tickStepState) 2)]];
      cbn; lia. }
  assert (Hstate :
    time_tick_step_write (time_tick_counted_state hook_state)
      (time_tick_step (time_tick_clock_step_state hook_state)) =
    time_tick_clock_step_state hook_state).
  { unfold time_tick_step_write, time_tick_counted_state, time_tick_step,
      time_tick_clock_step_state, tick_step_advance.
    rewrite Hrun; destruct (tick_step_decision _); reflexivity. }
  pose proof (time_tick_merge_step sg (time_tick_counted_state hook_state)
    (time_tick_step (time_tick_clock_step_state hook_state))
    PreH4 (conj PreH5 PreH6) Hrange) as Hmerge.
  rewrite Hstate in Hmerge; exact Hmerge.
Qed.

Lemma proof_of_OSTimeTick_which_implies_wit_9 : OSTimeTick_which_implies_wit_9.
Proof.
  left; intros.
  unfold time_tick_global_addresses in PreH1.
  destruct PreH1 as [_ [_ [_ [Hhead _]]]].
  rewrite Hhead.
  change (UCOS2_inv sg (time_tick_clock_step_state hook_state) |--
    coq_prop (UCOS2_state_inv sg (time_tick_clock_step_state hook_state)) &&
    (g_OSTCBList sg # Ptr |-> time_tick_list_head sg (time_tick_clock_step_state hook_state) **
      time_tick_task_without_head sg (time_tick_clock_step_state hook_state))).
  apply (proj1 (time_tick_head_resources sg (time_tick_clock_step_state hook_state))).
Qed.

Lemma proof_of_OSTimeTick_which_implies_wit_10 : OSTimeTick_which_implies_wit_10.
Proof.
  left; intros.
  unfold time_tick_global_addresses in PreH1.
  destruct PreH1 as [_ [_ [_ [Hhead _]]]].
  rewrite Hhead.
  change (g_OSTCBList sg # Ptr |-> time_tick_list_head sg (time_tick_clock_step_state hook_state) **
      time_tick_task_without_head sg (time_tick_clock_step_state hook_state) |--
      UCOS2_inv sg (time_tick_clock_step_state hook_state)).
  rewrite (time_tick_head_resources sg (time_tick_clock_step_state hook_state)).
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_which_implies_wit_11 : OSTimeTick_which_implies_wit_11.
Proof.
  left; intros.
  subst ptcb.
  pose proof (time_tick_configuration_no_multi__task_update_backedges sg current PreH4) as Hmulti.
  pose proof (time_tick_task_y_in_range__task_update_backedges sg current tid node PreH4 PreH3) as Hy.
  pose proof (time_tick_cursor_merge_inv__task_update_backedges sg current tid node PreH4 PreH3) as Hmerge.
  cbn [tcb_field_address] in Hmerge.
  unfold time_tick_priority.
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (time_tick_inv_split_body__task_update_backedges sg current tid node Hmulti PreH3).
  sep_apply_l_atomic (time_tick_body_delay_range__task_update_backedges sg tid node
    (time_tick_ready_group current) (time_tick_ready_rows current)).
  Intros.
  destruct PreH1 as [_ [_ [_ [_ [Hgroup Hrows]]]]].
  rewrite Hgroup, Hrows.
  unfold time_tick_body_cells, time_tick_delay, time_tick_status, time_tick_pend_result,
    time_tick_priority, time_tick_next, time_tick_y, time_tick_bit_x, time_tick_bit_y in *.
  cbn [tcb_field_address].
  entailer!.
Qed.
