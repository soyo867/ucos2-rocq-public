Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_full_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_full_spec.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

(** The constant array is initialized before OSInit. Its real resource is
    retained alongside the dynamic module initializer results; we do not
    execute a second initializer after OSInit or infer bytes from validity.
    The existing boot theorems' explicit Memory/BSS/Timer/hook boundaries
    are unchanged. These are compositions of initializer postconditions,
    not whole-source OSInit proofs. *)
Lemma kernel_boot_initializer_post_establishes_program_inv :
  forall sg task_name flag_name memory_name names,
  selected_kernel_profile sg -> init_tcb_list_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
   sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  kernel_boot_initializer_post sg task_name flag_name memory_name names **
    unmap_table_rep sg |--
  kernel_program_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof.
  intros sg task_name flag_name memory_name names Hprofile Htcb Hnames Hname.
  sep_apply_l_atomic (kernel_boot_initializer_post_establishes_global_inv
    sg task_name flag_name memory_name names Hprofile Htcb Hnames Hname).
  rewrite kernel_program_inv_split_unmap; entailer!.
Qed.

Lemma kernel_full_boot_initializer_post_establishes_program_inv :
  forall sg task_name event_name flag_name memory_name names,
  full_features_kernel_profile sg -> init_tcb_list_full_profile sg ->
  valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
   sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  kernel_full_boot_initializer_post sg task_name event_name flag_name memory_name names **
    unmap_table_rep sg |--
  kernel_program_full_inv sg
    (kernel_full_boot_state sg task_name event_name flag_name memory_name names).
Proof.
  intros sg task_name event_name flag_name memory_name names Hprofile Htcb Hnames Hname.
  sep_apply_l_atomic (kernel_full_boot_initializer_post_establishes_global_inv
    sg task_name event_name flag_name memory_name names Hprofile Htcb Hnames Hname).
  rewrite kernel_program_full_inv_split_unmap; entailer!.
Qed.
