Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_full_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_full_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_program_boot_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_type_source_spec.
Import UCOS2_C_Rules EventStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Real initializer postconditions establish the empty private pool and
    strong stack world at the SAME selected/full boot state. No private
    bytes are manufactured: both private maps and parked maps are empty.
    The underlying explicit initializer/BSS/Memory/Timer boundaries are
    unchanged. This is not a proof of the BSP or complete OSInit source.
    Boot dependencies remain outside ordinary runtime pool consumers. *)
Lemma kernel_boot_initializer_post_establishes_private_pool : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg task_name flag_name memory_name names,
  selected_kernel_profile sg -> init_tcb_list_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true -> sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  kernel_boot_initializer_post sg task_name flag_name memory_name names ** unmap_table_rep sg |--
  coq_prop (event_private_types_defined
    (UCOS2_boot_state sg task_name flag_name memory_name names).(EventState)) &&
  kernel_stack_inv abi (fun sg state => kernel_program_inv sg state **
    event_private_pool_rep sg state.(EventState)) sg None
    (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof.
  intros external platform port abi sg task_name flag_name memory_name names Hprofile Htcb Hnames Hmemory.
  sep_apply_l_atomic (kernel_boot_initializer_post_establishes_program_inv sg task_name
    flag_name memory_name names Hprofile Htcb Hnames Hmemory).
  assert (Hempty : event_private_pool_rep sg
      (UCOS2_boot_state sg task_name flag_name memory_name names).(EventState) --||-- emp).
  { apply event_private_pool_empty; intros; reflexivity. }
  assert (Htypes : event_private_types_defined
      (UCOS2_boot_state sg task_name flag_name memory_name names).(EventState)).
  { apply event_pool_initial_private_types_defined. }
  assert (Hworld : kernel_program_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names) |--
    kernel_stack_inv abi (fun sg state => kernel_program_inv sg state **
      event_private_pool_rep sg state.(EventState)) sg None
      (UCOS2_boot_state sg task_name flag_name memory_name names)).
  { eapply derivable1_trans.
    2: { apply kernel_stack_inv_boot with (name := task_name); reflexivity. }
    rewrite Hempty; entailer!. }
  sep_apply_l_atomic Hworld; entailer!.
Qed.

Lemma kernel_full_boot_initializer_post_establishes_private_pool : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg task_name event_name flag_name memory_name names,
  full_features_kernel_profile sg -> init_tcb_list_full_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true -> sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  kernel_full_boot_initializer_post sg task_name event_name flag_name memory_name names ** unmap_table_rep sg |--
  coq_prop (event_private_types_defined
    (kernel_full_boot_state sg task_name event_name flag_name memory_name names).(EventState)) &&
  kernel_stack_inv abi (fun sg state => kernel_program_full_inv sg state **
    event_private_pool_rep sg state.(EventState)) sg None
    (kernel_full_boot_state sg task_name event_name flag_name memory_name names).
Proof.
  intros external platform port abi sg task_name event_name flag_name memory_name names Hprofile Htcb Hnames Hmemory.
  sep_apply_l_atomic (kernel_full_boot_initializer_post_establishes_program_inv sg task_name
    event_name flag_name memory_name names Hprofile Htcb Hnames Hmemory).
  assert (Hempty : event_private_pool_rep sg
      (kernel_full_boot_state sg task_name event_name flag_name memory_name names).(EventState) --||-- emp).
  { apply event_private_pool_empty; intros; reflexivity. }
  assert (Htypes : event_private_types_defined
      (kernel_full_boot_state sg task_name event_name flag_name memory_name names).(EventState)).
  { apply event_pool_initial_named_private_types_defined. }
  assert (Hworld : kernel_program_full_inv sg
      (kernel_full_boot_state sg task_name event_name flag_name memory_name names) |--
    kernel_stack_inv abi (fun sg state => kernel_program_full_inv sg state **
      event_private_pool_rep sg state.(EventState)) sg None
      (kernel_full_boot_state sg task_name event_name flag_name memory_name names)).
  { eapply derivable1_trans.
    2: { apply kernel_stack_inv_boot with (name := task_name); reflexivity. }
    rewrite Hempty; entailer!. }
  sep_apply_l_atomic Hworld; entailer!.
Qed.
