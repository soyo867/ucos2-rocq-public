Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_clear_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_clear_heap_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_program_boot_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.sched.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source/ucos_ii.h declares Idle, Statistics and Timer arrays; the selected
    os_cfg.h gives each 128 OS_STK words.  The caller owns these actual static
    arrays before the corresponding Create calls.  An address interval in
    [selected_kernel_global_regions] does not produce this storage.
    Their zero initialization is a program-loading input, not an effect of
    OS_InitMisc and not a second copy retained after task publication. *)
Definition kernel_boot_stack_region (base : addr) : TaskStackRegion :=
  {| stackRegionBase := base; stackRegionWords := 128;
     stackRegionGrowsDown := true |}.

Definition kernel_boot_stack_storage (base : addr) : Assertion :=
  task_stack_storage (kernel_boot_stack_region base) (repeat (Some 0) 128).

Definition kernel_boot_stacks (sg : StableGlobVars) : Assertion :=
  kernel_boot_stack_storage sg.(g_OSTaskIdleStk) **
  (if sg.(osKernelConfig).(cfgStatisticsEnabled)
   then kernel_boot_stack_storage sg.(g_OSTaskStatStk) else emp) **
  (if sg.(osKernelConfig).(cfgTimerEnabled)
   then kernel_boot_stack_storage sg.(g_OSTmrTaskStk) else emp).

Lemma kernel_boot_stack_storage_from_zero_array : forall base,
  UIntArray.full base 128 (repeat 0 128) |-- kernel_boot_stack_storage base.
Proof.
  intros; unfold kernel_boot_stack_storage, task_stack_storage, kernel_boot_stack_region.
  cbn [stackRegionBase stackRegionWords].
  eapply derivable1_trans; [apply UIntArray.full_to_mixed_full|].
  rewrite map_repeat; reflexivity.
Qed.

Lemma kernel_boot_stacks_from_zero_arrays : forall sg,
  UIntArray.full sg.(g_OSTaskIdleStk) 128 (repeat 0 128) **
  (if sg.(osKernelConfig).(cfgStatisticsEnabled)
   then UIntArray.full sg.(g_OSTaskStatStk) 128 (repeat 0 128) else emp) **
  (if sg.(osKernelConfig).(cfgTimerEnabled)
   then UIntArray.full sg.(g_OSTmrTaskStk) 128 (repeat 0 128) else emp) |--
  kernel_boot_stacks sg.
Proof.
  intros; unfold kernel_boot_stacks.
  destruct sg.(osKernelConfig).(cfgStatisticsEnabled),
    sg.(osKernelConfig).(cfgTimerEnabled);
    apply derivable1_sepcon_mono;
      (apply kernel_boot_stack_storage_from_zero_array || reflexivity ||
       (apply derivable1_sepcon_mono;
          (apply kernel_boot_stack_storage_from_zero_array || reflexivity))).
Qed.

(** The existing initializer endpoint plus the loader's three real array
    resources. This implication retains the unclaimed arrays for future
    Create calls; it does not establish either initializer execution or
    startup masking. No arrays are inserted into the dynamic invariant. *)
Lemma kernel_boot_initializer_post_retains_system_stacks :
  forall sg task_name flag_name memory_name names,
  selected_kernel_profile sg -> init_tcb_list_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
   sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  kernel_boot_initializer_post sg task_name flag_name memory_name names **
    unmap_table_rep sg ** kernel_boot_stacks sg |--
  kernel_program_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names) **
    kernel_boot_stacks sg.
Proof.
  intros sg task_name flag_name memory_name names Hprofile Htcb Hnames Hname.
  sep_apply_l_atomic (kernel_boot_initializer_post_establishes_program_inv
    sg task_name flag_name memory_name names Hprofile Htcb Hnames Hname); entailer!.
Qed.

(** Source-order CreateExt arguments shared by OS_InitTaskIdle,
    OS_InitTaskStat and OS_TmrInitTask: ptos=&stack[127], pbos=&stack[0],
    size=128, p_arg=pext=NULL, opt=STK_CHK|STK_CLR. Function addresses are
    actual linker inputs; this descriptor does not establish executable
    code ownership. The basic-API/upward/VFP variants are not selected. *)
Definition kernel_boot_create_args (base entry priority public_id : Z) : TaskCreateArgs :=
  {| createEntry := entry; createArgument := 0; createStackTop := base + 508;
     createPriority := priority;
     createExtension := TaskCreateExtended public_id base 128 0 3 |}.

Definition kernel_boot_idle_args (sg : StableGlobVars) (entry : addr) : TaskCreateArgs :=
  kernel_boot_create_args sg.(g_OSTaskIdleStk) entry sg.(osLowestPrio) 65535.

Definition kernel_boot_stat_args (sg : StableGlobVars) (entry : addr) : TaskCreateArgs :=
  kernel_boot_create_args sg.(g_OSTaskStatStk) entry (sg.(osLowestPrio) - 1) 65534.

Definition kernel_boot_timer_args (sg : StableGlobVars) (entry : addr) : TaskCreateArgs :=
  kernel_boot_create_args sg.(g_OSTmrTaskStk) entry (sg.(osLowestPrio) - 2) 65533.

(** OS_STK requires four-byte alignment, not eight-byte alignment. The
    actual StackInit rounds (ptos+1) down to an eight-byte address: it may
    leave one upper word untouched. Both legal placements are retained. *)
Definition kernel_boot_stack_lower (base : addr) : list (option Z) :=
  repeat (Some 0) (if Z.eqb (base mod 8) 0 then 112 else 111).

Definition kernel_boot_stack_upper (base : addr) : list (option Z) :=
  if Z.eqb (base mod 8) 0 then [] else [Some 0].

Lemma kernel_boot_stack_alignment_cases : forall base,
  base mod 4 = 0 -> base mod 8 = 0 \/ base mod 8 = 4.
Proof.
  intros base Halign.
  destruct (proj1 (Z.mod_divide base 4 ltac:(lia)) Halign) as [k Hk].
  pose proof (Z.div_mod base 8 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound base 8 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma kernel_boot_stack_aligned_top : forall base,
  task_stack_init_aligned_top (base + 508) = base + 512 - base mod 8.
Proof.
  intros; unfold task_stack_init_aligned_top.
  replace (base + 508 + 4) with (base + 512) by ring.
  pose proof (Z.div_mod (base + 512) 8 ltac:(lia)) as Hdiv.
  assert (Hmod : (base + 512) mod 8 = base mod 8).
  { rewrite Z.add_mod by lia; change ((base mod 8 + 0) mod 8 = base mod 8).
    rewrite Z.add_0_r, Z.mod_mod by lia; reflexivity. }
  lia.
Qed.

Lemma kernel_boot_stack_create_layout : forall base entry priority public_id,
  valid_task_stack_region (kernel_boot_stack_region base) ->
  task_create_stack_layout TaskStackNoVFP (kernel_boot_stack_region base)
    (kernel_boot_create_args base entry priority public_id)
    (kernel_boot_stack_lower base) (kernel_boot_stack_upper base).
Proof.
  intros base entry priority public_id Hvalid.
  assert (Halign : base mod 4 = 0) by exact (proj1 (proj2 (proj2 Hvalid))).
  destruct (kernel_boot_stack_alignment_cases base Halign) as [Hmod|Hmod];
    unfold task_create_stack_layout; split.
  - split; [exact Hvalid|]; split; reflexivity.
  - unfold kernel_boot_stack_lower, kernel_boot_stack_upper; rewrite Hmod.
    change (task_stack_init_aligned_top (base + 508) - 64 = base + 112 * 4 /\
      128 = 112 + 16 + 0).
    rewrite kernel_boot_stack_aligned_top, Hmod; split; lia.
  - split; [exact Hvalid|]; split; reflexivity.
  - unfold kernel_boot_stack_lower, kernel_boot_stack_upper; rewrite Hmod.
    change (task_stack_init_aligned_top (base + 508) - 64 = base + 111 * 4 /\
      128 = 111 + 16 + 1).
    rewrite kernel_boot_stack_aligned_top, Hmod; split; lia.
Qed.

Lemma kernel_boot_stack_zero_image_split : forall base,
  repeat (Some 0) 128 = kernel_boot_stack_lower base ++
    repeat (Some 0) 16 ++ kernel_boot_stack_upper base.
Proof.
  intros; unfold kernel_boot_stack_lower, kernel_boot_stack_upper.
  destruct (Z.eqb (base mod 8) 0); reflexivity.
Qed.

Lemma kernel_boot_stacks_split_idle : forall sg,
  kernel_boot_stacks sg |-- kernel_boot_stack_storage sg.(g_OSTaskIdleStk) **
    ((if sg.(osKernelConfig).(cfgStatisticsEnabled)
      then kernel_boot_stack_storage sg.(g_OSTaskStatStk) else emp) **
     (if sg.(osKernelConfig).(cfgTimerEnabled)
      then kernel_boot_stack_storage sg.(g_OSTmrTaskStk) else emp)).
Proof. intros; unfold kernel_boot_stacks; entailer!. Qed.

(** The actual selected CreateExt call sequence consumes one of these
    static arrays: 128 zero stores, then the 16 StackInit stores on the
    SAME middle heap. Keeping the caller frame here is a local heap
    projection, not a theorem transporting it through arbitrary IRQs. *)
Lemma kernel_boot_stack_clear_init_store_execution :
  forall base entry priority public_id task_return (frame : Assertion) before,
  valid_task_stack_region (kernel_boot_stack_region base) ->
  0 <= entry < 4294967296 -> 0 <= task_return < 4294967296 ->
  (kernel_boot_stack_storage base ** frame) before ->
  exists middle after,
    task_stack_clear_heap_result 3
      (task_stack_clear_initial base 128 (repeat (Some 0) 128)) before
      (task_stack_clear_frontier base (repeat (Some 0) 128) 128) middle /\
    kernel_heap_execution (task_stack_clear_writes base 128) before middle /\
    kernel_heap_execution
      (task_stack_init_no_vfp_writes (base + 508) entry 0 task_return) middle after /\
    kernel_heap_execution (task_stack_clear_writes base 128 ++
      task_stack_init_no_vfp_writes (base + 508) entry 0 task_return) before after /\
    (task_stack_storage (kernel_boot_stack_region base)
      (task_create_stack_image TaskStackNoVFP
        (kernel_boot_create_args base entry priority public_id) task_return
        (kernel_boot_stack_lower base) (kernel_boot_stack_upper base)) ** frame) after.
Proof.
  intros base entry priority public_id task_return frame before Hvalid Hentry Hreturn Hbefore.
  exact (task_create_stack_clear_init_store_execution (kernel_boot_stack_region base)
    (kernel_boot_create_args base entry priority public_id) 3 task_return
    (repeat (Some 0) 128) (kernel_boot_stack_lower base) (kernel_boot_stack_upper base)
    frame before eq_refl eq_refl
    (kernel_boot_stack_create_layout base entry priority public_id Hvalid)
    eq_refl (kernel_boot_stack_zero_image_split base) Hentry ltac:(cbn; lia) Hreturn Hbefore).
Qed.

(** Idle's concrete call consumes its own static buffer and preserves
    the as-yet-unclaimed Stat/Timer buffers. Those are not duplicated into
    the task's parked-stack map when its publication happens later. *)
Lemma kernel_boot_idle_stack_clear_init_store_execution :
  forall sg entry task_return (frame : Assertion) before,
  valid_task_stack_region (kernel_boot_stack_region sg.(g_OSTaskIdleStk)) ->
  0 <= entry < 4294967296 -> 0 <= task_return < 4294967296 ->
  (kernel_boot_stacks sg ** frame) before ->
  exists after,
    kernel_heap_execution (task_stack_clear_writes sg.(g_OSTaskIdleStk) 128 ++
      task_stack_init_no_vfp_writes (sg.(g_OSTaskIdleStk) + 508) entry 0 task_return)
      before after /\
    (task_stack_storage (kernel_boot_stack_region sg.(g_OSTaskIdleStk))
      (task_create_stack_image TaskStackNoVFP (kernel_boot_idle_args sg entry) task_return
        (kernel_boot_stack_lower sg.(g_OSTaskIdleStk))
        (kernel_boot_stack_upper sg.(g_OSTaskIdleStk))) **
     ((if sg.(osKernelConfig).(cfgStatisticsEnabled)
       then kernel_boot_stack_storage sg.(g_OSTaskStatStk) else emp) **
      (if sg.(osKernelConfig).(cfgTimerEnabled)
       then kernel_boot_stack_storage sg.(g_OSTmrTaskStk) else emp) ** frame)) after.
Proof.
  intros sg entry task_return frame before Hvalid Hentry Hreturn Hbefore.
  assert (Hsplit : kernel_boot_stacks sg ** frame |--
    kernel_boot_stack_storage sg.(g_OSTaskIdleStk) **
     ((if sg.(osKernelConfig).(cfgStatisticsEnabled)
       then kernel_boot_stack_storage sg.(g_OSTaskStatStk) else emp) **
      (if sg.(osKernelConfig).(cfgTimerEnabled)
       then kernel_boot_stack_storage sg.(g_OSTmrTaskStk) else emp) ** frame)).
  { sep_apply_l_atomic (kernel_boot_stacks_split_idle sg); entailer!. }
  destruct (kernel_boot_stack_clear_init_store_execution sg.(g_OSTaskIdleStk) entry
    sg.(osLowestPrio) 65535 task_return _ before Hvalid Hentry Hreturn (Hsplit before Hbefore))
    as [middle [after [_ [_ [_ [Hrun Hafter]]]]]].
  exists after; split; assumption.
Qed.
