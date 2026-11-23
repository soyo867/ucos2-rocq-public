Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.task.
Require Export Ucos2Verify.VC.code.task.spec.init_tcb_list_full_spec.
Require Export Ucos2Verify.VC.code.task.spec.init_tcb_list_full_prio_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma init_tcb_list_full_node_merge_next_name : forall sg ix next name,
  init_tcb_list_full_profile sg ->
  tcb_layout_cell true (task_slot_addr sg ix) (TCBCommonField TCBNext)
      (Some (encode_task_link sg next)) **
  tcb_layout_cell true (task_slot_addr sg ix) (TCBCommonField TCBTaskName)
      (Some name) **
  init_tcb_list_full_node_residual sg ix |--
  task_slot_storage_rep sg ix (tcb_init_free_image sg next name).
Proof.
  intros sg ix next name Hprofile.
  pose proof (init_tcb_list_full_profile_valid sg Hprofile) as Hconfig.
  unfold task_slot_storage_rep; rewrite Hconfig.
  cbn [cfgEventMultiEnabled cfgTaskProfile].
  unfold init_tcb_list_full_node_residual.
  set (fields := tcb_configured_fields true true).
  set (base := task_slot_addr sg ix).
  set (image_name := tcb_layout_write init_tcb_list_full_zero_image
    (TCBCommonField TCBTaskName) (Some name)).
  set (image_both := tcb_layout_write image_name
    (TCBCommonField TCBNext) (Some (encode_task_link sg next))).
  assert (Hnd : NoDup fields) by (subst fields; apply tcb_configured_fields_nodup).
  assert (Hnext : In (TCBCommonField TCBNext) fields) by
    (subst fields; apply tcb_configured_common_field_in).
  assert (Hname : In (TCBCommonField TCBTaskName)
      (remove TCBLayoutField_eq_dec (TCBCommonField TCBNext) fields)).
  { subst fields; apply in_in_remove; [discriminate|apply tcb_configured_common_field_in]. }
  assert (Hnd_next : NoDup (remove TCBLayoutField_eq_dec
      (TCBCommonField TCBNext) fields)) by
    (apply init_tcb_list_full_remove_preserves_nodup; exact Hnd).
  assert (Hname_merge :
    tcb_layout_cell true base (TCBCommonField TCBTaskName) (Some name) **
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec
      (tcb_layout_cell true base)
      (remove TCBLayoutField_eq_dec (TCBCommonField TCBTaskName)
        (remove TCBLayoutField_eq_dec (TCBCommonField TCBNext) fields))
      init_tcb_list_full_zero_image |--
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec
      (tcb_layout_cell true base)
      (remove TCBLayoutField_eq_dec (TCBCommonField TCBNext) fields)
      image_name).
  { unfold image_name.
    exact (TaskFieldStorage.store_fields_merge_updated_field
      TCBLayoutField (option Z) TCBLayoutField_eq_dec
      (tcb_layout_cell true base)
      (remove TCBLayoutField_eq_dec (TCBCommonField TCBNext) fields)
      init_tcb_list_full_zero_image (TCBCommonField TCBTaskName) (Some name)
      Hnd_next Hname). }
  assert (Hname_step :
    tcb_layout_cell true base (TCBCommonField TCBNext)
        (Some (encode_task_link sg next)) **
    tcb_layout_cell true base (TCBCommonField TCBTaskName) (Some name) **
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec
      (tcb_layout_cell true base)
      (remove TCBLayoutField_eq_dec (TCBCommonField TCBTaskName)
        (remove TCBLayoutField_eq_dec (TCBCommonField TCBNext) fields))
      init_tcb_list_full_zero_image |--
    tcb_layout_cell true base (TCBCommonField TCBNext)
        (Some (encode_task_link sg next)) **
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec
      (tcb_layout_cell true base)
      (remove TCBLayoutField_eq_dec (TCBCommonField TCBNext) fields)
      image_name).
  { sepcon_assoc_change.
    eapply derivable1_sepcon_mono; [derivable1_refl_tac | exact Hname_merge]. }
  assert (Hnext_step :
    tcb_layout_cell true base (TCBCommonField TCBNext)
        (Some (encode_task_link sg next)) **
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec
      (tcb_layout_cell true base)
      (remove TCBLayoutField_eq_dec (TCBCommonField TCBNext) fields)
      image_name |--
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec
      (tcb_layout_cell true base) fields image_both).
  { unfold image_both.
    exact (TaskFieldStorage.store_fields_merge_updated_field
      TCBLayoutField (option Z) TCBLayoutField_eq_dec
      (tcb_layout_cell true base) fields image_name
      (TCBCommonField TCBNext) (Some (encode_task_link sg next)) Hnd Hnext). }
  assert (Himage : image_both = tcb_init_free_image sg next name).
  { unfold image_both, image_name, init_tcb_list_full_zero_image,
      tcb_init_free_image, tcb_layout_write.
    apply functional_extensionality;
      intros [f| | | | | | |]; try destruct f; reflexivity. }
  unfold tcb_configured_storage_rep.
  change ((tcb_layout_cell true base (TCBCommonField TCBNext)
      (Some (encode_task_link sg next)) **
    tcb_layout_cell true base (TCBCommonField TCBTaskName) (Some name) **
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec
      (tcb_layout_cell true base)
      (remove TCBLayoutField_eq_dec (TCBCommonField TCBTaskName)
        (remove TCBLayoutField_eq_dec (TCBCommonField TCBNext) fields))
      init_tcb_list_full_zero_image) |--
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec
      (tcb_layout_cell true base) fields (tcb_init_free_image sg next name)).
  rewrite <- Himage.
  eapply derivable1_trans; [exact Hname_step | exact Hnext_step].
Qed.

Lemma init_tcb_list_full_loop_split_next_name : forall sg name ix,
  init_tcb_list_full_profile sg -> 0 <= ix < 22 ->
  init_tcb_list_full_loop_state sg name ix |--
    tcb_layout_cell true (task_slot_addr sg ix) (TCBCommonField TCBNext) (Some 0) **
    tcb_layout_cell true (task_slot_addr sg ix) (TCBCommonField TCBTaskName) (Some 0) **
    init_tcb_list_full_loop_residual sg name ix.
Proof.
  intros sg name ix Hprofile Hrange.
  unfold init_tcb_list_full_loop_state, init_tcb_list_full_loop_residual,
    init_tcb_list_full_zero_suffix.
  rewrite (init_tcb_list_full_zrange_head ix 22) by lia.
  cbn [task_free_storage_rep].
  Intros image.
  assert (image = init_tcb_list_full_zero_image) by congruence; subst image.
  rewrite (task_slot_storage_full sg ix init_tcb_list_full_zero_image Hprofile).
  sep_apply_l_atomic (init_tcb_list_full_storage_split_next_name
    (task_slot_addr sg ix) init_tcb_list_full_zero_image).
  entailer!.
Qed.
