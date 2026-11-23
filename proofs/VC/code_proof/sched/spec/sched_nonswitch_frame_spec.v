Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual uninterrupted Save / no-switch C prefix / Restore
    sequence needs no dormant-map shape. Any disjoint resource is carried
    through these local instructions. This frame rule does not cover an
    IRQ or a switch between the named source endpoints. *)
Lemma os_sched_uninterrupted_nonswitch_frame : forall external platform critical arch
  (save : Armv7aSaveSuffixABI external platform critical arch)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg call mask state registers before final_registers acquired saved_heap (frame : Assertion),
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (kernel_call_execution_owned external platform call mask ** kernel_program_inv sg state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired saved_heap /\ acquired = state /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      (kernel_call_execution_owned external platform call mask **
       kernel_program_inv sg (os_sched_prefix_state state) ** frame) after).
Proof.
  intros external platform critical arch save restore sg call mask state registers before
    final_registers acquired saved_heap frame Hreturn Hvalid Hmask Hnoswitch Hnonempty Hpre Hsave.
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hvalid|reflexivity]).
  match type of Hpre with ?P before => assert (Hsave_input : P |--
    kernel_call_execution_owned external platform call
      (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
    (kernel_program_inv sg state ** frame)) end.
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call
    (kernel_save_read_cpsr registers) state before final_registers acquired saved_heap _ Hsaved
    (Hsave_input before Hpre) Hsave) as [Hstate [Hmemory [Hlr [Hr0 Hmasked]]]].
  split.
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave). }
  split; [exact Hstate|].
  assert (Hsaved_mask : armv7a_irq_fiq_mask final_registers.(kernel_save_r0) = mask)
    by (rewrite Hr0; exact Hmask).
  match type of Hmasked with ?P saved_heap => assert (Hprefix_input : P |--
    UCOS2_inv sg state ** unmap_table_rep sg **
    (critical_region_masked platform critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
     os_sched_context_resources external call ** frame)) end.
  { rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (os_sched_source_nonswitch_prefix_resources sg state _ saved_heap Hnoswitch Hnonempty
    (Hprefix_input saved_heap Hmasked)) as [prefix_heap [Hprefix Hafter_prefix]].
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hcursor Hcursor_mask Hrestore_prefix Hrestore_suffix.
  match type of Hafter_prefix with ?P prefix_heap => assert (Hrestore_input : P |--
    critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
    os_sched_context_resources external call **
    (kernel_program_inv sg (os_sched_prefix_state state) ** frame)) end.
  { rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg call
    final_registers.(kernel_save_r0) state cursor prefix_heap written middle final_cursor after _
    Hcursor Hcursor_mask (Hrestore_input prefix_heap Hafter_prefix) Hrestore_prefix Hrestore_suffix)
    as [Hrun [Hreturn_word [Hmemory_return Hreturned]]].
  rewrite Hsaved_mask in Hreturned; split; [exact Hrun|].
  match type of Hreturned with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) by entailer! end end.
  exact (Hclose after Hreturned).
Qed.
