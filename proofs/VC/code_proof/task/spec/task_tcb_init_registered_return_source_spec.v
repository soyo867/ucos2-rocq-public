Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_foreign_return_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The existing post-hook resource stage, before install. Its selector
    may name any ready task. This view does not demand that the next task
    be the original caller. A registered source extension proves the view
    from its actual prefix, stack stores and continuation capture. *)
Definition task_tcb_init_switch_capture environment
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg original suspended context outgoing state : Assertion :=
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  coq_prop (os_sched_saved_stack_binding context outgoing state /\
    sched_high_ready_consistency state.(TskState) state.(SchedState) /\
    state.(SchedState).(readyList) <> [] /\
    task_stack_live_coverage state.(TskState) (Some (task_stack_key context.(os_sched_call_stack)))) &&
  (UCOS2_inv sg state **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_call_stack_entry abi state.(TskState) focus (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
   armv7a_task_switch_control task_abi context ** unmap_table_rep sg).

(** The finite source trace and spatial transport have the SAME concrete
    endpoints. Extra is the existing handler/client proof interface;
    [capture_view] is a proved view of its post-hook cut, not a callee
    Ensure or a future safety condition. The stop flag and observed
    destination remain explicit outcomes. A trace that retires this
    invocation or keeps selecting another task does not prove its return.

    The original saved word and inside handle, including any caller-owned
    private TCB or failed-create stack buffer in [frame], pass through that
    actual trace and the actual install/restore chain. *)
Lemma task_tcb_init_registered_foreign_return :
  forall environment critical arch Extra
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    extra_resources extra_step extra_effect sg original suspended context outgoing
    (return_cut : Extra) released first_state first_origin saved acquired
    first_cut before captured (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  UCOS2_state_inv sg released ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released first_state ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_saved_pointer_at first_state suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  @kernel_client_call_stack_extension_valid _ _ _ Extra abi
    extra_resources focus payload extra_step extra_effect ->
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state ->
    task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp)) ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients) (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None extra_effect ->
  (forall state, extra_resources sg return_cut state |--
    task_tcb_init_switch_capture environment task_abi sg original suspended context outgoing state) ->
  kernel_client_heap_observer_cut original.(os_sched_call_invocation) first_cut ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload first_cut first_state **
   (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** frame)) before ->
  kernel_client_heap_trace extra_step sg first_cut before (KernelClientHeapExtra return_cut) captured ->
  exists hooked stopped returned_origin,
    kernel_client_heap_state_trace extra_effect sg first_cut first_state (KernelClientHeapExtra return_cut) hooked /\
    kernel_resumption_task_source_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
      first_origin first_state stopped returned_origin hooked /\
    (stopped = false ->
     os_sched_destination_binding environment.(task_stack_call_external) context outgoing hooked
       original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments) ->
     exists installed selected,
       sched_install_heap_fragment sg captured installed
         (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
       armv7a_continuation_restore_reads selected installed /\
       selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
       selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
       selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
       (forall restored,
         armv7a_task_restore_transition task_abi context selected installed restored ->
         forall cursor written middle final_cursor after,
         cursor.(kernel_restore_r0) = saved ->
         cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
         armv7a_restore_prefix_transition restore cursor restored written middle ->
         armv7a_restore_suffix_transition restore written middle final_cursor after ->
         kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
         (task_tcb_init_stack_restore_output environment critical sg original saved released **
          unmap_table_rep sg ** frame) after /\
         (task_tcb_init_stack_call_return_post environment critical sg original
            (armv7a_irq_fiq_mask saved) released ** unmap_table_rep sg ** frame) after)).
Proof.
  intros environment critical arch Extra task_abi restore extra_resources extra_step extra_effect sg
    original suspended context outgoing return_cut released first_state first_origin saved acquired
    first_cut before captured frame abi focus payload Hreleased Hprefix Horigin Hbinding Hcall Hslice
    Hmask Hpointer Haddress Hextension Hextra Henter Hexit Hpublish Hsource Hcapture_view Hcut Hpre Htrace.
  destruct (kernel_client_call_stack_trace_source_resources _ _ _ Extra abi extra_resources focus payload
    extra_step extra_effect critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
    Hextension Henter Hexit Hpublish Hsource first_cut before (KernelClientHeapExtra return_cut)
    captured _ Htrace first_state first_origin Hcut Hpre)
    as [hooked [stopped [returned_origin [Hstates [Hsources [Hcompatible Howned]]]]]].
  exists hooked, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hnormal Hdestination.
  pose proof (proj1 (Hprefix Hreleased)) as Hfirst_valid.
  destruct (kernel_client_trace_preserves_saved_pointer Extra extra_effect sg
    suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) Hextra
    first_cut first_state (KernelClientHeapExtra return_cut) hooked Hstates Hfirst_valid Hpointer)
    as [Hhooked_valid Hhooked_pointer].
  assert (Hhistory : task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released hooked).
  { eapply task_tcb_init_call_preserved_trans; [exact Hprefix|].
    eapply task_tcb_init_interval_preserves_call.
    rewrite Hnormal in Hsources.
    exact (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hsources)). }
  assert (Hcapture : (task_tcb_init_switch_capture environment task_abi sg original suspended
    context outgoing hooked **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** frame)) captured).
  { eapply (derivable1_sepcon_mono _ _ _ _ (Hcapture_view hooked) (derivable1_refl _)); exact Howned. }
  unfold task_tcb_init_switch_capture in Hcapture; fold abi focus in Hcapture.
  match type of Hcapture with ?P captured => assert (Hopen : P |--
    coq_prop (os_sched_saved_stack_binding context outgoing hooked /\
      sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) /\
      hooked.(SchedState).(readyList) <> [] /\
      task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack)))) &&
    (UCOS2_inv sg hooked **
     task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
     armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key context.(os_sched_call_stack))
       (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
     armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
     (armv7a_task_switch_control task_abi context **
      (interrupt_platform_saved environment.(task_stack_call_platform)
         (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
       critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
       unmap_table_rep sg ** frame)))) by entailer! end.
  destruct (Hopen captured Hcapture) as [[Hsaved [Hhigh [Hnonempty Hcoverage]]] Hinput].
  exact (task_tcb_init_foreign_switch_return environment critical arch task_abi restore sg original released
    context outgoing hooked suspended saved acquired captured frame Hreleased Hhistory Horigin Hbinding Hcall Hslice
    Hmask Hsaved Hdestination Hhigh Hnonempty Hhooked_pointer Haddress Hcoverage Hinput).
Qed.

(** The returned execution is consumed by the original TCBInit result.
    The historical result still proves the actual no-free or publication
    branch, including its exact generation and initialized fields. In the
    error branch the initialized stack buffer remains owned for rollback. *)
Lemma task_tcb_init_foreign_return_call_post :
  forall environment critical sg region args task_return lower upper initial_name invocation origin
    mask initial original result released,
  task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
    invocation origin initial result released ->
  UCOS2_state_inv sg released ->
  task_tcb_init_stack_source_preserved original initial released ->
  task_tcb_init_stack_call_return_post environment critical sg original mask released **
  task_tcb_init_stack_buffer_result region args task_return lower upper result |--
  task_tcb_init_stack_call_post environment critical sg region args task_return lower upper initial_name
    invocation origin mask initial original result.
Proof.
  intros; unfold task_tcb_init_stack_call_post; Exists released; entailer!.
Qed.

