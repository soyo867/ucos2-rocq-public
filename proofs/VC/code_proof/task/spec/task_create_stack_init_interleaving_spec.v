Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_source_spec.
Import UCOS2_C_Rules KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Physical child-buffer ownership after a prefix of the descending typed
    stores. The unwritten low region and written high region are disjoint.
    This child has not been published; the interrupted creator's OS resources
    are transported separately by the actual IRQ source. *)
Definition task_stack_init_partial_frame (base top : Z)
  (lower upper : list (option Z)) (prefix suffix : list Z) : Assertion :=
  UIntArray.mixed_full base (Zlength lower) lower **
  UIntArray.undef_full (task_stack_init_sp TaskStackNoVFP top) (Zlength suffix) **
  UIntArray.mixed_full (task_stack_init_aligned_top top - 4 * Zlength prefix)
    (Zlength prefix) (map (@Some Z) (rev prefix)) **
  UIntArray.mixed_full (task_stack_init_aligned_top top) (Zlength upper) upper.

Lemma task_stack_init_prefix_store_execution :
  forall base size top entry argument task_return lower old_frame upper prefix suffix
    (frame : Assertion) before,
  prefix ++ suffix = task_stack_init_core_push_words entry argument task_return ->
  (task_stack_init_pre TaskStackNoVFP base size top entry argument task_return
    lower old_frame upper ** frame) before ->
  exists cut,
    kernel_heap_execution (task_stack_push_writes (task_stack_init_aligned_top top) prefix)
      before cut /\
    Forall (fun value => 0 <= value < 4294967296) suffix /\
    (task_stack_init_partial_frame base top lower upper prefix suffix ** frame) cut.
Proof.
  intros base size top entry argument task_return lower old_frame upper prefix suffix frame before Hwords Hbefore.
  assert (Hextract : task_stack_init_pre TaskStackNoVFP base size top entry argument task_return
      lower old_frame upper ** frame |--
    coq_prop (0 <= entry < 4294967296 /\ 0 <= argument < 4294967296 /\
      0 <= task_return < 4294967296) &&
    (UIntArray.undef_full (task_stack_init_sp TaskStackNoVFP top) 16 **
     (UIntArray.mixed_full base (Zlength lower) lower **
      UIntArray.mixed_full (task_stack_init_aligned_top top) (Zlength upper) upper ** frame))).
  { unfold task_stack_init_pre; Intros.
    sep_apply_l_atomic (UIntArray.mixed_full_to_undef_full
      (task_stack_init_sp TaskStackNoVFP top) 16 old_frame); entailer!. }
  destruct (Hextract before Hbefore) as [[Hentry [Harg Hreturn]] Howned].
  pose proof (task_stack_init_core_words_in_range entry argument task_return Hentry Harg Hreturn) as Hranges.
  rewrite <- Hwords, Forall_app in Hranges; destruct Hranges as [Hprefix Hsuffix].
  assert (Hlength : Zlength prefix + Zlength suffix = 16).
  { rewrite <- Zlength_app, Hwords; reflexivity. }
  pose proof (Zlength_nonneg prefix) as Hp; pose proof (Zlength_nonneg suffix) as Hs.
  match type of Howned with ?P before => assert (Hsplit : P |--
    UIntArray.undef_full (task_stack_init_aligned_top top - 4 * Zlength prefix) (Zlength prefix) **
    (UIntArray.undef_full (task_stack_init_sp TaskStackNoVFP top) (Zlength suffix) **
     UIntArray.mixed_full base (Zlength lower) lower **
     UIntArray.mixed_full (task_stack_init_aligned_top top) (Zlength upper) upper ** frame)) end.
  { sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_full
      (task_stack_init_sp TaskStackNoVFP top) (Zlength suffix) 16 ltac:(lia)).
    rewrite sizeof_uint.
    replace (16 - Zlength suffix) with (Zlength prefix) by lia.
    replace (task_stack_init_sp TaskStackNoVFP top + Zlength suffix * 4)
      with (task_stack_init_aligned_top top - 4 * Zlength prefix)
      by (unfold task_stack_init_sp, task_stack_init_frame_bytes, task_stack_init_word_count; lia).
    entailer!. }
  destruct (task_stack_push_store_execution prefix (task_stack_init_aligned_top top) _ before
    Hprefix (Hsplit before Howned)) as [cut [Hrun Hcut]].
  exists cut; split; [exact Hrun|]. split; [exact Hsuffix|].
  match type of Hcut with ?P cut => match goal with |- ?Q cut => assert (Hclose : P |-- Q) end end.
  { unfold task_stack_init_partial_frame; entailer!. }
  exact (Hclose cut Hcut).
Qed.

Lemma task_stack_init_suffix_store_execution :
  forall base top entry argument task_return options lower upper prefix suffix
    (frame : Assertion) before,
  prefix ++ suffix = task_stack_init_core_push_words entry argument task_return ->
  Forall (fun value => 0 <= value < 4294967296) suffix ->
  (task_stack_init_partial_frame base top lower upper prefix suffix ** frame) before ->
  exists after,
    kernel_heap_execution (task_stack_push_writes
      (task_stack_init_aligned_top top - 4 * Zlength prefix) suffix) before after /\
    (task_stack_init_post TaskStackNoVFP base top entry argument task_return options
      lower upper (task_stack_init_sp TaskStackNoVFP top) ** frame) after.
Proof.
  intros base top entry argument task_return options lower upper prefix suffix frame before Hwords Hsuffix Hbefore.
  assert (Hlength : Zlength prefix + Zlength suffix = 16).
  { rewrite <- Zlength_app, Hwords; reflexivity. }
  pose proof (Zlength_nonneg prefix) as Hp; pose proof (Zlength_nonneg suffix) as Hs.
  assert (Hbase : task_stack_init_aligned_top top - 4 * Zlength prefix - 4 * Zlength suffix =
    task_stack_init_sp TaskStackNoVFP top).
  { unfold task_stack_init_sp, task_stack_init_frame_bytes, task_stack_init_word_count; lia. }
  match type of Hbefore with ?P before => assert (Horder : P |--
    UIntArray.undef_full
      (task_stack_init_aligned_top top - 4 * Zlength prefix - 4 * Zlength suffix) (Zlength suffix) **
    (UIntArray.mixed_full (task_stack_init_aligned_top top - 4 * Zlength prefix)
       (Zlength prefix) (map (@Some Z) (rev prefix)) **
     UIntArray.mixed_full base (Zlength lower) lower **
     UIntArray.mixed_full (task_stack_init_aligned_top top) (Zlength upper) upper ** frame)) end.
  { unfold task_stack_init_partial_frame; rewrite Hbase; entailer!. }
  destruct (task_stack_push_store_execution suffix
    (task_stack_init_aligned_top top - 4 * Zlength prefix) _ before
    Hsuffix (Horder before Hbefore)) as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  rewrite Hbase in Hafter.
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hmerge : P |-- Q) end end.
  { pose proof (UIntArray.mixed_full_merge_to_mixed_full
      (task_stack_init_sp TaskStackNoVFP top) (Zlength suffix) 16
      (map (@Some Z) (rev suffix)) (map (@Some Z) (rev prefix)) ltac:(lia)) as Hjoin.
    rewrite sizeof_uint in Hjoin.
    replace (16 - Zlength suffix) with (Zlength prefix) in Hjoin by lia.
    replace (task_stack_init_sp TaskStackNoVFP top + Zlength suffix * 4)
      with (task_stack_init_aligned_top top - 4 * Zlength prefix) in Hjoin by lia.
    sep_apply_l_atomic Hjoin.
    rewrite <- map_app, <- rev_app_distr, Hwords.
    unfold task_stack_init_post, task_stack_init_frame_rep, task_stack_init_frame_words,
      task_stack_init_push_words, task_stack_init_fpu_push_words.
    rewrite app_nil_r; entailer!. }
  exact (Hmerge after Hafter).
Qed.

Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_spatial Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import TaskStateDef.

(** Every decomposition of the actual sixteen typed stores gives a source
    cut, including an empty prefix or suffix. The same heap executes the
    prefix, actual returning IRQ, and suffix, then establishes the next
    TCBInit precondition. Return-selection and registry-extension conditions
    are the existing IRQ contract; this is one IRQ at an arbitrary typed
    store boundary, without an arbitrary-handler or termination claim. *)
Lemma task_create_stack_init_interleaved_irq_tcb_pre : forall environment critical Extra
  extra_resources extra_step extra_effect sg args state node handler suspended publication mask
  region task_return lower old_frame upper initial_name prefix suffix before (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state state call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  call.(os_sched_call_origin) = RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_task_frame_slice suspended ->
  state.(SchedState).(isRunning) = true -> state.(IntrState).(intNesting) = 0 ->
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened state.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_sp) ->
  handler.(os_int_exit_interrupted_mask) = mask ->
  @kernel_client_call_stack_extension_valid _ _ _ Extra abi
    extra_resources focus payload extra_step extra_effect ->
  (forall cut initial next returned, extra_effect sg cut initial next returned ->
    UCOS2_state_inv sg initial ->
    task_saved_pointer_at initial suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp)) ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None extra_effect ->
  prefix ++ suffix = task_stack_init_core_push_words args.(createEntry) args.(createArgument) task_return ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    call.(os_sched_call_invocation) call.(os_sched_call_origin) state ->
  (task_create_stack_init_input environment critical sg region args task_return lower old_frame upper
     call mask state ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) before ->
  exists cut,
    kernel_heap_execution (task_stack_push_writes (task_stack_init_aligned_top args.(createStackTop)) prefix) before cut /\
    (forall saved_heap, armv7a_save_transition abi handler suspended cut saved_heap ->
  exists registry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes suspended)
      cut.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg state
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (forall closed_heap, kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
      KernelClientHeapClosed closed_heap ->
      exists returned stopped returned_origin,
        kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg call.(os_sched_call_invocation)
          None call.(os_sched_call_origin) parked stopped returned_origin returned /\
        (stopped = false -> returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
         exists selected,
           armv7a_irq_restore_pointer_reads sg closed_heap (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
             selected.(armv7a_continuation_sp) /\
           (forall final, armv7a_restore_transition abi handler selected closed_heap final ->
             let resumed := armv7a_continuation_resumed_call selected call in
             let current := os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack) in
             exists initialized,
             kernel_heap_execution (task_stack_push_writes
               (task_stack_init_aligned_top args.(createStackTop) - 4 * Zlength prefix) suffix) final initialized /\
             (task_create_stack_init_output environment critical sg region args task_return lower upper
                call mask state (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) ** unmap_table_rep sg **
              task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) initialized /\
             ((EX context checkpoint,
               coq_prop (task_tcb_init_stack_same_call context call /\
                 task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
                   call.(os_sched_call_invocation) call.(os_sched_call_origin) checkpoint /\
                 task_tcb_init_stack_source_preserved call state checkpoint) &&
               task_tcb_init_stack_call_pre environment critical sg region args task_return lower upper initial_name
                 call.(os_sched_call_invocation) call.(os_sched_call_origin) mask checkpoint context) ** unmap_table_rep sg **
              task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) initialized)))).
Proof.
  intros environment critical Extra extra_resources extra_step extra_effect sg args state node handler suspended
    publication mask region task_return lower old_frame upper initial_name prefix suffix before frame call abi parked focus payload
    Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp
    Hmask Hextension Hextra Henter Hexit Hpublish Hsource Hwords Hlayout Hentry Hpre.
  match type of Hpre with ?P before => assert (Horder : P |--
    task_stack_init_pre TaskStackNoVFP region.(stackRegionBase) region.(stackRegionWords)
      args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower old_frame upper **
    (task_tcb_init_stack_save_input environment critical sg call mask state ** unmap_table_rep sg **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) end.
  { unfold task_create_stack_init_input; entailer!. }
  destruct (task_stack_init_prefix_store_execution region.(stackRegionBase) region.(stackRegionWords)
    args.(createStackTop) args.(createEntry) args.(createArgument) task_return
    lower old_frame upper prefix suffix _ before Hwords (Horder before Hpre))
    as [cut [Hprefix [Hsuffix Hcut]]].
  exists cut; split; [exact Hprefix|].
  intros saved_heap Hsave.
  set (buffer := task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop)
    lower upper prefix suffix).
  match type of Hcut with ?P cut => assert (Hirq_input : P |--
    task_tcb_init_stack_save_input environment critical sg call mask state ** unmap_table_rep sg **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    (buffer ** frame)) end.
  { unfold buffer; entailer!. }
  destruct (task_create_stack_init_irq_source environment critical Extra extra_resources extra_step extra_effect
    sg args state node handler suspended publication mask cut saved_heap (buffer ** frame)
    Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp
    Hmask Hextension Hextra Henter Hexit Hpublish Hsource (Hirq_input cut Hcut) Hsave)
    as [registry_heap [Hwrites [Hstores Htrace_return]]].
  exists registry_heap; split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (Htrace_return closed_heap Htrace)
    as [returned [stopped [returned_origin [Hstates [Hsources Hreturn]]]]].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hnormal Hreturned_current.
  destruct (Hreturn Hnormal Hreturned_current) as [selected [Hpointers Hresume]].
  exists selected; split; [exact Hpointers|].
  intros final Hrestore resumed current.
  destruct (Hresume final Hrestore) as [Hsame [Hpreserved [Hordinary Hfinal]]].
  match type of Hfinal with ?P final => assert (Hsuffix_input : P |--
    task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix suffix **
    (task_tcb_init_stack_save_input environment critical sg resumed mask current ** unmap_table_rep sg **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) end.
  { unfold buffer; entailer!. }
  destruct (task_stack_init_suffix_store_execution region.(stackRegionBase) args.(createStackTop)
    args.(createEntry) args.(createArgument) task_return (task_create_options args)
    lower upper prefix suffix _ final Hwords Hsuffix (Hsuffix_input final Hfinal))
    as [initialized [Htail Hinitialized]].
  exists initialized; split; [exact Htail|].
  assert (Houtput : (task_create_stack_init_output environment critical sg region args task_return lower upper
    call mask state (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) ** unmap_table_rep sg **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) initialized).
  { match type of Hinitialized with ?P initialized => match goal with |- ?Q initialized => assert (Hpack : P |-- Q) end end.
    { unfold task_create_stack_init_output; Exists resumed current; entailer!. }
    exact (Hpack initialized Hinitialized). }
  split; [exact Houtput|].
  match type of Houtput with ?P initialized => match goal with |- ?Q initialized => assert (Hconsume : P |-- Q) end end.
  { sep_apply_l_atomic (task_create_stack_init_output_tcb_pre environment critical sg region args task_return
      lower upper initial_name call mask state (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) Hlayout Hentry).
    Intros context checkpoint; Exists context checkpoint; entailer!; tauto. }
  exact (Hconsume initialized Houtput).
Qed.
