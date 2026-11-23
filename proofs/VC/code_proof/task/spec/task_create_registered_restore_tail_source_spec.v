Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_program_storage.
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
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_registered_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_pending_suffix_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_return_tail_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Consume the call stage proved by a real returning selector. Its ready
    node supplies nonemptiness only when scheduling is enabled. The
    actual next Save, nonswitch C prefix and Restore return the original
    TaskCreate result on the same resource heap. *)
Lemma task_create_current_nonswitch_return_source :
  forall environment critical arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg region args task_return lower old_frame upper original returned mask current
    registers before final_registers acquired saved_heap (frame : Assertion),
  task_tcb_init_stack_same_call returned original ->
  task_create_call_stage returned current -> current.(SchedState).(isRunning) = true ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch current = false ->
  (kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv sg
    (task_stack_call_active_key returned) returned mask current ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers current before final_registers acquired saved_heap /\
  acquired = current /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      (task_create_stack_post environment critical sg region args task_return lower old_frame upper
        original mask 0 ** frame) after).
Proof.
  intros environment critical arch save restore sg region args task_return lower old_frame upper original
    returned mask current registers before final_registers acquired saved_heap frame Hsame Hstage Hrunning
    Hreturn Hvalid Hmask Hnoswitch Hpre Hsave.
  assert (Hnonempty : os_sched_selection_enabled current = true -> current.(SchedState).(readyList) <> []).
  { intros Henabled Hnil.
    destruct (task_create_call_stage_selection_ready returned current Hstage Hrunning Henabled)
      as [_ [_ [node [Hready Hgen]]]].
    destruct Hready as [_ [_ [_ [Hin _]]]]; rewrite Hnil in Hin; contradiction. }
  destruct (os_sched_stack_uninterrupted_nonswitch_call environment critical arch save restore sg returned mask
    current registers before final_registers acquired saved_heap frame Hreturn Hvalid Hmask Hnoswitch Hnonempty
    Hpre Hsave) as [Hexecution [Hacquired [prefix_heap [Hprefix Htail]]]].
  split; [exact Hexecution|]. split; [exact Hacquired|]. exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hr0 Hmasked Hrestore_prefix Hrestore_suffix.
  destruct (Htail cursor written middle final_cursor after Hr0 Hmasked Hrestore_prefix Hrestore_suffix)
    as [Hrestore_run Hafter].
  split; [exact Hrestore_run|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (os_sched_stack_return_post_returns_create environment critical sg original returned mask
      current region args task_return lower old_frame upper Hsame); entailer!. }
  exact (Hclose after Hafter).
Qed.

(** A concrete registered foreign execution returns to the original
    Restore AFTER its MSR. The registry owns all participating CPU cut
    resources; only the private buffer and independent frame survive as
    separate resources. The original saved/inside token was consumed by
    that MSR and is deliberately not requested again here.

    At the actual original destination, install/frame loads restore the
    saved CPSR of any mask. The remaining BX then feeds the original
    TCBInit result into TaskCreate's OSRunning or rollback continuation.
    [capture_view] belongs to the existing proved source-extension
    interface; it gives the present post-hook heap, never a future return. *)
Lemma task_create_registered_pending_restore_tail_source :
  forall environment critical arch Extra
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    extra_resources extra_step extra_effect sg region args task_return lower old_frame upper initial_name
    initial result original suspended context outgoing (return_cut : Extra) released
    first_state first_origin saved first_cut before captured (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial ->
  task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial result released ->
  UCOS2_state_inv sg released ->
  task_tcb_init_stack_source_preserved original initial released ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released first_state ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  armv7a_irq_fiq_mask saved = armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) ->
  task_saved_pointer_at first_state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
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
   (task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame)) before ->
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
         forall written cursor final_cursor after,
         armv7a_irq_fiq_mask written = armv7a_irq_fiq_mask saved ->
         cursor.(kernel_restore_msr_word) = Some written ->
         cursor.(kernel_restore_lr) = selected.(armv7a_continuation_lr) ->
         armv7a_restore_suffix_transition restore cursor restored final_cursor after ->
         final_cursor.(kernel_restore_return_word) = Some suspended.(armv7a_continuation_lr) /\
         task_create_tcb_return_source_continuation environment critical arch save restore sg region args task_return
           lower old_frame upper original (armv7a_irq_fiq_mask saved) result after frame /\
         (let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
          forall registers final_registers acquired saved_heap,
          result = 0 -> current.(SchedState).(isRunning) = true ->
          registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
          armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
          os_sched_requests_switch current = false ->
          armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current after
            final_registers acquired saved_heap ->
          kernel_call_save_uninterrupted_execution arch registers current after final_registers acquired saved_heap /\
          acquired = current /\
          exists prefix_heap,
            os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
            (forall sched_cursor sched_written sched_middle sched_final final_heap,
              sched_cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
              armv7a_irq_fiq_mask sched_cursor.(kernel_restore_current_cpsr) = 192 ->
              armv7a_restore_prefix_transition restore sched_cursor prefix_heap sched_written sched_middle ->
              armv7a_restore_suffix_transition restore sched_written sched_middle sched_final final_heap ->
              kernel_call_restore_uninterrupted_execution arch sched_cursor prefix_heap sched_final final_heap /\
              (task_create_stack_post environment critical sg region args task_return lower old_frame upper
                original (armv7a_irq_fiq_mask saved) 0 ** frame) final_heap)))).
Proof.
  intros environment critical arch Extra task_abi save restore extra_resources extra_step extra_effect sg
    region args task_return lower old_frame upper initial_name initial result original suspended context outgoing
    return_cut released first_state first_origin saved first_cut before captured frame abi focus payload
    Hentry Hresult Hreleased Hordinary Hprefix Horigin Hbinding Hcall Hslice Hmask Hpointer Haddress
    Hextension Hextra Henter Hexit Hpublish Hsource Hcapture_view Hcut Hpre Htrace.
  destruct (kernel_client_call_stack_trace_source_resources _ _ _ Extra abi extra_resources focus payload
    extra_step extra_effect critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
    Hextension Henter Hexit Hpublish Hsource first_cut before (KernelClientHeapExtra return_cut)
    captured _ Htrace first_state first_origin Hcut Hpre)
    as [hooked [stopped [returned_origin [Hstates [Hsources [Hcompatible Howned]]]]]].
  exists hooked, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hnormal Hdestination.
  destruct (kernel_client_trace_preserves_saved_pointer Extra extra_effect sg
    suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) Hextra
    first_cut first_state (KernelClientHeapExtra return_cut) hooked Hstates
    (proj1 (Hprefix Hreleased)) Hpointer) as [Hhooked Hhooked_pointer].
  assert (Hhistory : task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released hooked).
  { eapply task_tcb_init_call_preserved_trans; [exact Hprefix|].
    eapply task_tcb_init_interval_preserves_call.
    rewrite Hnormal in Hsources.
    exact (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hsources)). }
  assert (Hcapture : (task_tcb_init_switch_capture environment task_abi sg original suspended context outgoing hooked **
    (task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame)) captured).
  { eapply (derivable1_sepcon_mono _ _ _ _ (Hcapture_view hooked) (derivable1_refl _)); exact Howned. }
  destruct (task_tcb_init_pending_call_suffix_source environment critical arch task_abi save restore sg
    original released context outgoing hooked suspended captured
    (task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame)
    Hhistory Horigin Hbinding Hcall Hslice Hhooked_pointer Haddress Hdestination Hcapture)
    as [installed [selected [Hinstall [Hreads [Hsp [Hcpsr [Hregisters Hreturn]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hsp|]. split; [exact Hcpsr|]. split; [exact Hregisters|].
  intros restored Hrestore written cursor final_cursor after Hwritten Hword Hlr Hsuffix.
  destruct (Hreturn restored Hrestore) as [Hsame [Hselected_stage [Hstage [Hpreserved [Hsource_current [Hcurrent [Hsave Hlast]]]]]]].
  destruct (Hlast saved written cursor final_cursor after ltac:(rewrite Hwritten; exact Hmask)
    ltac:(symmetry; exact Hwritten) Hword Hlr Hsuffix) as [Hreturn_word [Hclosed_after Hafter]].
  split; [exact Hreturn_word|].
  split.
  -
  eapply task_create_tcb_return_source; [exact Hentry|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold task_tcb_init_stack_restore_output; Intros returned current.
    assert (Hobserved : task_tcb_init_call_preserved sg original.(os_sched_call_invocation)
      released current) by tauto.
    destruct (Hobserved Hreleased) as [_ [Hcreation [Hactive Hname]]].
    unfold task_tcb_init_stack_call_post; Exists released.
    unfold task_tcb_init_stack_call_return_post; Exists returned current.
    unfold task_tcb_init_stack_return_preserved; entailer!; try tauto. }
  exact (Hclose after Hafter).
  - intros current registers final_registers acquired saved_heap Hsuccess Hrunning Hsave_return Hsave_valid
      Hsave_mask Hnoswitch Hsave_suffix.
    assert (Hclosed : (kernel_stack_call_closed abi kernel_program_inv sg
      (task_stack_call_active_key (armv7a_continuation_resumed_call selected original))
      (armv7a_continuation_resumed_call selected original) (armv7a_irq_fiq_mask saved) current ** frame) after).
    { match type of Hclosed_after with ?P after => match goal with |- ?Q after => assert (Horder : P |-- Q) end end.
      { rewrite Hsuccess; unfold task_tcb_init_stack_buffer_result.
        destruct (Z.eq_dec 0 66); [lia|entailer!]. }
      exact (Horder after Hclosed_after). }
    eapply task_create_current_nonswitch_return_source; try eassumption.
    apply Hstage; exact Hrunning.
Qed.
