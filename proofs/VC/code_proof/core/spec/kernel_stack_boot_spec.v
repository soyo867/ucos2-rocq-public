Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_full_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_full_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_program_boot_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual selected/full initializer producers are separate from the
    reusable stack-world interface. Ordinary runtime consumers need not
    import or rebuild either complete initializer dependency closure.
    Their BSS/Memory/Timer/name boundaries remain the existing explicit
    initializer contracts; these are not whole OSInit C proofs. *)
Lemma kernel_boot_initializer_post_establishes_stack_inv : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg task_name flag_name memory_name names,
  selected_kernel_profile sg -> init_tcb_list_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
   sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  kernel_boot_initializer_post sg task_name flag_name memory_name names ** unmap_table_rep sg |--
  kernel_stack_inv abi kernel_program_inv sg None
    (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof.
  intros external platform port abi sg task_name flag_name memory_name names Hprofile Htcb Hnames Hmemory.
  sep_apply_l_atomic (kernel_boot_initializer_post_establishes_program_inv sg task_name
    flag_name memory_name names Hprofile Htcb Hnames Hmemory).
  apply kernel_stack_inv_boot with (name := task_name); reflexivity.
Qed.

Lemma kernel_full_boot_initializer_post_establishes_stack_inv : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg task_name event_name flag_name memory_name names,
  full_features_kernel_profile sg -> init_tcb_list_full_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
   sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  kernel_full_boot_initializer_post sg task_name event_name flag_name memory_name names ** unmap_table_rep sg |--
  kernel_stack_inv abi kernel_program_full_inv sg None
    (kernel_full_boot_state sg task_name event_name flag_name memory_name names).
Proof.
  intros external platform port abi sg task_name event_name flag_name memory_name names Hprofile Htcb Hnames Hmemory.
  sep_apply_l_atomic (kernel_full_boot_initializer_post_establishes_program_inv sg task_name
    event_name flag_name memory_name names Hprofile Htcb Hnames Hmemory).
  apply kernel_stack_inv_boot with (name := task_name); reflexivity.
Qed.
