Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem ConAssertion.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Export Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.sched Ucos2Verify.lib.kernel_program_storage.
Require Export Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_stk_clr_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_calls_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_modular_init_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_call_protocol_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_runtime_consumer_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_modular_call_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Export Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Actual Ext arguments, including the complete option word and all five
    extended TCB fields.  No pointee owner is inferred from [extension]. *)
Definition task_create_ext_arguments (args : TaskCreateArgs)
  (entry argument top priority public_id bottom count extension options : Z) : Prop :=
  args.(createEntry) = entry /\ args.(createArgument) = argument /\
  args.(createStackTop) = top /\ args.(createPriority) = priority /\
  args.(createExtension) = TaskCreateExtended public_id bottom count extension options /\
  0 <= public_id <= 65535 /\ 0 <= count <= 4294967295 /\ 0 <= options <= 65535.

Definition task_create_ext_bottom (args : TaskCreateArgs) : Z :=
  match args.(createExtension) with
  | TaskCreateBasic => 0
  | TaskCreateExtended _ bottom _ _ _ => bottom
  end.

Definition task_create_ext_size (args : TaskCreateArgs) : Z :=
  match args.(createExtension) with
  | TaskCreateBasic => 0
  | TaskCreateExtended _ _ count _ _ => count
  end.

Definition task_create_ext_clear_access (args : TaskCreateArgs) : bool :=
  task_stack_clear_enabled (task_create_options args) &&
  negb (Z.eqb (task_create_ext_size args) 0).

(** A clear may cover any nonempty subarray of the actual writable stack.
    Metadata has no geometric constraint on the source's no-access paths.
    [prefix]/[suffix] retain exact bytes outside the cleared subarray. *)
Definition task_create_ext_clear_binding region args
  (initial prefix middle suffix : list (option Z)) : Prop :=
  task_create_ext_clear_access args = true ->
  initial = prefix ++ middle ++ suffix /\
  task_create_ext_bottom args = region.(stackRegionBase) + Zlength prefix * sizeof(UINT) /\
  task_create_ext_size args = Zlength middle.

Definition task_create_ext_clear_image args
  (initial prefix middle suffix : list (option Z)) : list (option Z) :=
  if task_create_ext_clear_access args
  then prefix ++ repeat (Some 0) (List.length middle) ++ suffix else initial.

Definition task_create_ext_clear_frame region args
  (initial prefix middle suffix : list (option Z)) : Assertion :=
  if task_create_ext_clear_access args
  then task_stack_storage_without_region region prefix (Zlength middle) suffix
  else task_stack_storage region initial.

Definition task_create_ext_after_lower args lower old_frame upper prefix middle suffix :=
  sublist 0 (Zlength lower)
    (task_create_ext_clear_image args (lower ++ old_frame ++ upper) prefix middle suffix).
Definition task_create_ext_after_frame args lower old_frame upper prefix middle suffix :=
  sublist (Zlength lower) (Zlength lower + Zlength old_frame)
    (task_create_ext_clear_image args (lower ++ old_frame ++ upper) prefix middle suffix).
Definition task_create_ext_after_upper args lower old_frame upper prefix middle suffix :=
  sublist (Zlength lower + Zlength old_frame) (Zlength (lower ++ old_frame ++ upper))
    (task_create_ext_clear_image args (lower ++ old_frame ++ upper) prefix middle suffix).

Lemma task_create_ext_arguments_options : forall args entry argument top priority public_id bottom
  count extension options,
  task_create_ext_arguments args entry argument top priority public_id bottom count extension options ->
  task_create_options args = options /\ task_create_ext_bottom args = bottom /\
  task_create_ext_size args = count.
Proof.
  intros args entry argument top priority public_id bottom count extension options H.
  destruct H as [_ [_ [_ [_ [Hext _]]]]].
  unfold task_create_options, task_create_ext_bottom, task_create_ext_size;
    rewrite Hext; auto.
Qed.

Lemma task_create_ext_clear_image_length : forall region args initial prefix middle suffix,
  task_create_ext_clear_binding region args initial prefix middle suffix ->
  Zlength (task_create_ext_clear_image args initial prefix middle suffix) = Zlength initial.
Proof.
  intros region args initial prefix middle suffix Hbinding.
  unfold task_create_ext_clear_image.
  destruct (task_create_ext_clear_access args) eqn:Haccess; [|reflexivity].
  destruct (Hbinding Haccess) as [Himage _].
  rewrite Himage, !Zlength_app.
  rewrite !Zlength_correct, repeat_length; reflexivity.
Qed.

Lemma task_create_ext_clear_bounds : forall region (prefix middle suffix : list (option Z)),
  valid_task_stack_region region ->
  region.(stackRegionWords) = Zlength prefix + Zlength middle + Zlength suffix ->
  task_stk_clr_array_bounds
    (region.(stackRegionBase) + Zlength prefix * sizeof(UINT)) (Zlength middle).
Proof.
  intros region prefix middle suffix [Hwords [Hbase [Halign Hend]]] Hsize.
  pose proof (Zlength_nonneg prefix); pose proof (Zlength_nonneg middle);
    pose proof (Zlength_nonneg suffix).
  unfold task_stk_clr_array_bounds, task_stack_region_end in *.
  rewrite sizeof_uint in *.
  repeat split; try lia.
  rewrite Z.add_mod, Z.mod_mul by lia; rewrite Halign; reflexivity.
Qed.

(** Exact consequence of the checked OS_TaskStkClr C contract. No new
    clearing semantics and no overlapping array owner is introduced. *)
Lemma task_create_ext_clear_prepare : forall region args initial prefix middle suffix,
  valid_task_stack_region region ->
  Zlength initial = region.(stackRegionWords) ->
  task_create_ext_clear_binding region args initial prefix middle suffix ->
  task_stack_storage region initial |--
  task_stk_clr_pre (task_create_ext_bottom args) (task_create_ext_size args)
    (task_create_options args) middle **
  task_create_ext_clear_frame region args initial prefix middle suffix.
Proof.
  intros region args initial prefix middle suffix Hvalid Hlength Hbinding.
  unfold task_create_ext_clear_binding in Hbinding.
  unfold task_create_ext_clear_frame, task_create_ext_clear_access in *.
  unfold task_stk_clr_pre.
  destruct (task_stack_clear_enabled (task_create_options args)) eqn:Henabled;
    destruct (Z.eqb (task_create_ext_size args) 0) eqn:Hzero; cbn in *; try solve [entailer!].
  destruct (Hbinding eq_refl) as [Himage [Hbottom Hsize]].
  assert (Htotal : region.(stackRegionWords) = Zlength prefix + Zlength middle + Zlength suffix).
  { rewrite <- Hlength, Himage, !Zlength_app; lia. }
  pose proof (task_create_ext_clear_bounds region prefix middle suffix Hvalid Htotal) as Hbounds.
  rewrite Himage, Hbottom, Hsize.
  sep_apply_l_atomic (task_stack_storage_split_region region prefix middle suffix Htotal).
  entailer!.
Qed.

Lemma task_create_ext_clear_finish : forall region args initial prefix middle suffix,
  Zlength initial = region.(stackRegionWords) ->
  task_create_ext_clear_binding region args initial prefix middle suffix ->
  task_stk_clr_post (task_create_ext_bottom args) (task_create_ext_size args)
    (task_create_options args) middle **
  task_create_ext_clear_frame region args initial prefix middle suffix |--
  task_stack_storage region (task_create_ext_clear_image args initial prefix middle suffix).
Proof.
  intros region args initial prefix middle suffix Hlength Hbinding.
  unfold task_create_ext_clear_binding in Hbinding.
  unfold task_create_ext_clear_frame, task_create_ext_clear_image, task_create_ext_clear_access in *.
  unfold task_stk_clr_post.
  destruct (task_stack_clear_enabled (task_create_options args)) eqn:Henabled;
    destruct (Z.eqb (task_create_ext_size args) 0) eqn:Hzero; cbn in *; try solve [entailer!].
  destruct (Hbinding eq_refl) as [Himage [Hbottom Hsize]].
  assert (Htotal : region.(stackRegionWords) = Zlength prefix + Zlength middle + Zlength suffix).
  { rewrite <- Hlength, Himage, !Zlength_app; lia. }
  rewrite Hbottom, Hsize; Intros.
  pose proof (task_stack_storage_merge_region region prefix
    (repeat (Some 0) (List.length middle)) suffix (Zlength middle) Htotal
    ltac:(rewrite !Zlength_correct, repeat_length; reflexivity)) as Hmerge.
  rewrite sizeof_uint in Hmerge.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed.


Lemma task_create_ext_tcb_arguments : forall args entry argument top priority public_id bottom
  count extension options stack_pointer initial_name,
  task_create_ext_arguments args entry argument top priority public_id bottom count extension options ->
  stack_pointer = task_stack_init_sp TaskStackNoVFP top ->
  task_tcb_init_arguments (task_tcb_init_stack_call_args args initial_name)
    priority stack_pointer bottom public_id count extension options initial_name.
Proof.
  intros args entry argument top priority public_id bottom count extension options stack_pointer
    initial_name [Hentry [Hargument [Htop [Hpriority [Hextension Hranges]]]]] Hsp.
  unfold task_tcb_init_stack_call_args, task_create_tcb_args, task_tcb_init_arguments.
  rewrite Hextension; cbn.
  rewrite Hpriority, Htop, <- Hsp; repeat split; reflexivity.
Qed.

(** Partition the returned clear image at the original StackInit frame
    boundaries. These are values of one array, not duplicate heap owners. *)
Lemma task_create_ext_clear_partitions : forall region args lower old_frame upper prefix middle suffix,
  task_create_ext_clear_binding region args (lower ++ old_frame ++ upper) prefix middle suffix ->
  Zlength (task_create_ext_after_lower args lower old_frame upper prefix middle suffix) = Zlength lower /\
  Zlength (task_create_ext_after_frame args lower old_frame upper prefix middle suffix) = Zlength old_frame /\
  Zlength (task_create_ext_after_upper args lower old_frame upper prefix middle suffix) = Zlength upper /\
  task_create_ext_clear_image args (lower ++ old_frame ++ upper) prefix middle suffix =
    task_create_ext_after_lower args lower old_frame upper prefix middle suffix ++
    task_create_ext_after_frame args lower old_frame upper prefix middle suffix ++
    task_create_ext_after_upper args lower old_frame upper prefix middle suffix.
Proof.
  intros region args lower old_frame upper prefix middle suffix Hbinding.
  pose proof (task_create_ext_clear_image_length region args (lower ++ old_frame ++ upper)
    prefix middle suffix Hbinding) as Hlength.
  pose proof (Zlength_nonneg lower); pose proof (Zlength_nonneg old_frame);
    pose proof (Zlength_nonneg upper).
  unfold task_create_ext_after_lower, task_create_ext_after_frame, task_create_ext_after_upper.
  set (cleared := task_create_ext_clear_image args (lower ++ old_frame ++ upper) prefix middle suffix) in *.
  rewrite !Zlength_app in Hlength.
  repeat split.
  - rewrite Zlength_sublist by lia; lia.
  - rewrite Zlength_sublist by lia; lia.
  - rewrite Zlength_sublist by (rewrite !Zlength_app; lia).
    rewrite !Zlength_app; lia.
  - symmetry.
    rewrite <- (sublist_split (Zlength lower) (Zlength (lower ++ old_frame ++ upper))
      (Zlength lower + Zlength old_frame) cleared) by (rewrite ?Zlength_app; lia).
    rewrite <- (sublist_split 0 (Zlength (lower ++ old_frame ++ upper))
      (Zlength lower) cleared) by (rewrite ?Zlength_app; lia).
    apply sublist_self; rewrite !Zlength_app; lia.
Qed.

Lemma task_create_ext_clear_buffer_domain : forall region args task_return lower old_frame upper
  prefix middle suffix,
  task_create_stack_buffer_domain region args task_return lower old_frame upper ->
  task_create_ext_clear_binding region args (lower ++ old_frame ++ upper) prefix middle suffix ->
  task_create_stack_buffer_domain region args task_return
    (task_create_ext_after_lower args lower old_frame upper prefix middle suffix)
    (task_create_ext_after_frame args lower old_frame upper prefix middle suffix)
    (task_create_ext_after_upper args lower old_frame upper prefix middle suffix).
Proof.
  intros region args task_return lower old_frame upper prefix middle suffix Hdomain Hbinding.
  destruct (task_create_ext_clear_partitions region args lower old_frame upper prefix middle suffix Hbinding)
    as [Hlower [Hframe [Hupper Himage]]].
  destruct Hdomain as [Hlayout [Hcount [Hentry [Hargument Hreturn]]]].
  split.
  - unfold task_create_stack_layout in *; rewrite Hlower, Hupper; exact Hlayout.
  - rewrite Hframe; tauto.
Qed.

(** Consequence of the checked clear return followed by the existing
    StackInit precondition. The callable world is transported unchanged by
    the actual heap-only clear call; no interference equality is asserted. *)
Lemma task_create_ext_clear_init_input : forall environment critical saved_local sg region args
  task_return lower old_frame upper prefix middle suffix call mask checkpoint,
  task_create_stack_buffer_domain region args task_return lower old_frame upper ->
  task_create_ext_clear_binding region args (lower ++ old_frame ++ upper) prefix middle suffix ->
  task_stk_clr_post (task_create_ext_bottom args) (task_create_ext_size args)
      (task_create_options args) middle **
  task_create_ext_clear_frame region args (lower ++ old_frame ++ upper) prefix middle suffix **
  task_tcb_init_continuation_save_input environment critical saved_local sg call mask checkpoint |--
  coq_prop (task_create_stack_buffer_domain region args task_return
    (task_create_ext_after_lower args lower old_frame upper prefix middle suffix)
    (task_create_ext_after_frame args lower old_frame upper prefix middle suffix)
    (task_create_ext_after_upper args lower old_frame upper prefix middle suffix)) &&
  task_create_continuation_init_input environment critical saved_local sg region args task_return
    (task_create_ext_after_lower args lower old_frame upper prefix middle suffix)
    (task_create_ext_after_frame args lower old_frame upper prefix middle suffix)
    (task_create_ext_after_upper args lower old_frame upper prefix middle suffix) call mask checkpoint.
Proof.
  intros environment critical saved_local sg region args task_return lower old_frame upper
    prefix middle suffix call mask checkpoint Hdomain Hbinding.
  pose proof (task_create_ext_clear_buffer_domain region args task_return lower old_frame upper
    prefix middle suffix Hdomain Hbinding) as Hafter.
  pose proof (task_create_ext_clear_partitions region args lower old_frame upper prefix middle suffix Hbinding)
    as [_ [_ [_ Himage]]].
  destruct Hdomain as [Hlayout [Hcount [Hentry [Hargument Hreturn]]]].
  assert (Hlength : Zlength (lower ++ old_frame ++ upper) = region.(stackRegionWords)).
  { destruct Hlayout as [_ [_ Hsize]].
    rewrite !Zlength_app; cbn in Hsize; lia. }
  sep_apply_l_atomic (task_create_ext_clear_finish region args (lower ++ old_frame ++ upper)
    prefix middle suffix Hlength Hbinding).
  rewrite Himage.
  pose proof Hafter as Hafter_parts.
  destruct Hafter_parts as [Hafter_layout [Hafter_count Hafter_ranges]].
  unfold task_create_continuation_init_input.
  sep_apply_l_atomic (task_create_stack_storage_init_pre TaskStackNoVFP region args task_return
    (task_create_ext_after_lower args lower old_frame upper prefix middle suffix)
    (task_create_ext_after_frame args lower old_frame upper prefix middle suffix)
    (task_create_ext_after_upper args lower old_frame upper prefix middle suffix)
    Hafter_layout Hafter_count Hentry Hargument Hreturn).
  entailer!.
Qed.

(** Public error paths retain the entry image. On 66 the exact clear
    image is first partitioned at the original frame boundaries; only the
    sixteen initialized frame words then replace that middle partition.
    On 0 the entire child stack has transferred at protected publication. *)
Definition task_create_ext_post environment critical saved_local sg region args task_return
  lower old_frame upper prefix middle suffix original mask result : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\ UCOS2_state_inv sg current /\
      (result = 0 \/ result = 40 \/ result = 42 \/ result = 60 \/ result = 66) /\
      (result = 42 -> 63 < args.(createPriority)) /\
      (result <> 42 -> args.(createPriority) <= 63)) &&
    (task_create_continuation_input environment critical saved_local sg returned mask current **
     unmap_table_rep sg **
     (if Z.eq_dec result 0 then emp else
       task_stack_storage region
         (if Z.eq_dec result 66 then
           task_create_stack_image TaskStackNoVFP args task_return
             (task_create_ext_after_lower args lower old_frame upper prefix middle suffix)
             (task_create_ext_after_upper args lower old_frame upper prefix middle suffix)
          else lower ++ old_frame ++ upper))).
