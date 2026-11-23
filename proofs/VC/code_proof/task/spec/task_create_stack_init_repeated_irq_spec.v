Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
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
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_interleaving_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Advance a partly written, unpublished child frame by any next chunk.
    The earlier words remain initialized and the unwritten remainder stays
    separately owned. This is the physical step between two IRQ returns. *)
Lemma task_stack_init_partial_store_execution : forall base top lower upper prefix chunk suffix
  (frame : Assertion) before,
  Zlength prefix + Zlength chunk + Zlength suffix = 16 ->
  Forall (fun value => 0 <= value < 4294967296) chunk ->
  (task_stack_init_partial_frame base top lower upper prefix (chunk ++ suffix) ** frame) before ->
  exists after,
    kernel_heap_execution (task_stack_push_writes
      (task_stack_init_aligned_top top - 4 * Zlength prefix) chunk) before after /\
    (task_stack_init_partial_frame base top lower upper (prefix ++ chunk) suffix ** frame) after.
Proof.
  intros base top lower upper prefix chunk suffix frame before Hlength Hranges Hbefore.
  pose proof (Zlength_nonneg prefix) as Hp.
  pose proof (Zlength_nonneg chunk) as Hc.
  pose proof (Zlength_nonneg suffix) as Hs.
  assert (Hsplit_address : task_stack_init_sp TaskStackNoVFP top + Zlength suffix * 4 =
    task_stack_init_aligned_top top - 4 * Zlength prefix - 4 * Zlength chunk).
  { unfold task_stack_init_sp, task_stack_init_frame_bytes, task_stack_init_word_count; lia. }
  match type of Hbefore with ?P before => assert (Hsplit : P |--
    UIntArray.undef_full
      (task_stack_init_aligned_top top - 4 * Zlength prefix - 4 * Zlength chunk) (Zlength chunk) **
    (UIntArray.mixed_full (task_stack_init_aligned_top top - 4 * Zlength prefix)
       (Zlength prefix) (map (@Some Z) (rev prefix)) **
     UIntArray.undef_full (task_stack_init_sp TaskStackNoVFP top) (Zlength suffix) **
     UIntArray.mixed_full base (Zlength lower) lower **
     UIntArray.mixed_full (task_stack_init_aligned_top top) (Zlength upper) upper ** frame)) end.
  { unfold task_stack_init_partial_frame; rewrite Zlength_app.
    sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_full
      (task_stack_init_sp TaskStackNoVFP top) (Zlength suffix)
      (Zlength chunk + Zlength suffix) ltac:(lia)).
    rewrite sizeof_uint, Hsplit_address.
    replace (Zlength chunk + Zlength suffix - Zlength suffix) with (Zlength chunk) by lia.
    entailer!. }
  destruct (task_stack_push_store_execution chunk
    (task_stack_init_aligned_top top - 4 * Zlength prefix) _ before Hranges (Hsplit before Hbefore))
    as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hmerge : P |-- Q) end end.
  { pose proof (UIntArray.mixed_full_merge_to_mixed_full
      (task_stack_init_aligned_top top - 4 * Zlength prefix - 4 * Zlength chunk)
      (Zlength chunk) (Zlength chunk + Zlength prefix)
      (map (@Some Z) (rev chunk)) (map (@Some Z) (rev prefix)) ltac:(lia)) as Hjoin.
    rewrite sizeof_uint in Hjoin.
    replace (task_stack_init_aligned_top top - 4 * Zlength prefix - 4 * Zlength chunk + Zlength chunk * 4)
      with (task_stack_init_aligned_top top - 4 * Zlength prefix) in Hjoin by ring.
    replace (Zlength chunk + Zlength prefix - Zlength chunk) with (Zlength prefix) in Hjoin by lia.
    sep_apply_l_atomic Hjoin.
    unfold task_stack_init_partial_frame; rewrite Zlength_app, rev_app_distr, map_app.
    replace (task_stack_init_aligned_top top - 4 * (Zlength prefix + Zlength chunk))
      with (task_stack_init_aligned_top top - 4 * Zlength prefix - 4 * Zlength chunk) by ring.
    replace (Zlength prefix + Zlength chunk) with (Zlength chunk + Zlength prefix) by lia.
    entailer!. }
  exact (Hmerge after Hafter).
Qed.

(** A finite SOURCE CONTINUATION, produced by the theorem below and never
    assumed by a public Require. Each natural records how many remaining
    typed stores precede the next IRQ (firstn clips at the final boundary).
    At every IRQ the same current heap executes Save, registry steps and
    the actually selected Restore. Only the existing normal same-call
    return branch recurses. The empty schedule writes the remaining words
    and directly supplies the existing minimum StackInit/TCBInit post.

    Current handler/stack facts and approved registry-extension laws remain
    local source parameters. This covers repeated first-level IRQs with the
    owned handler stack; a nested handler needs its own resource producer.
    No eventual return is asserted for a stopped/non-returning trace. *)
Fixpoint task_create_stack_init_irq_continuation (schedule : list nat)
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (args : TaskCreateArgs) (region handler_region : TaskStackRegion)
  (handler_fragments : TaskStackFragments) (task_return : Z)
  (lower upper : list (option Z)) (initial_name : Z)
  (original : OsSchedCallContext) (mask : Z) (initial_state : UCOS2_Verify_State)
  (call : OsSchedCallContext) (state : UCOS2_Verify_State) (prefix suffix : list Z)
  (before : model) (frame : Assertion) {struct schedule} : Prop :=
  match schedule with
  | [] =>
      exists initialized,
        kernel_heap_execution (task_stack_push_writes
          (task_stack_init_aligned_top args.(createStackTop) - 4 * Zlength prefix) suffix) before initialized /\
        (task_create_stack_init_output environment critical sg region args task_return lower upper
           original mask initial_state (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) **
         unmap_table_rep sg ** task_stack_fragments_rep handler_region handler_fragments ** frame) initialized /\
        ((EX context checkpoint,
          coq_prop (task_tcb_init_stack_same_call context original /\
            task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
              original.(os_sched_call_invocation) original.(os_sched_call_origin) checkpoint /\
            task_tcb_init_stack_source_preserved original initial_state checkpoint) &&
          task_tcb_init_stack_call_pre environment critical sg region args task_return lower upper initial_name
            original.(os_sched_call_invocation) original.(os_sched_call_origin) mask checkpoint context) **
         unmap_table_rep sg ** task_stack_fragments_rep handler_region handler_fragments ** frame) initialized
  | count :: remaining =>
      let chunk := firstn count suffix in
      let rest := skipn count suffix in
      let abi := environment.(task_stack_call_continuations) in
      exists cut,
        kernel_heap_execution (task_stack_push_writes
          (task_stack_init_aligned_top args.(createStackTop) - 4 * Zlength prefix) chunk) before cut /\
        (forall Extra extra_resources extra_step extra_effect node handler suspended publication saved_heap,
          let parked := armv7a_irq_live_parked_state state call suspended.(armv7a_continuation_sp)
            suspended.(armv7a_continuation_fragments) in
          let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc)
            suspended.(armv7a_continuation_lr) in
          let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
            suspended.(armv7a_continuation_fragments)) in
          handler.(os_int_exit_interrupted_call) = call ->
          handler.(os_int_exit_handler_stack) = handler_region ->
          handler.(os_int_exit_handler_fragments) = handler_fragments ->
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
          (forall client_cut initial next returned, extra_effect sg client_cut initial next returned ->
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
          armv7a_save_transition abi handler suspended cut saved_heap ->
          exists registry_heap,
            kernel_heap_writes (armv7a_continuation_save_writes suspended)
              cut.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
            kernel_heap_execution (armv7a_irq_live_entry_writes sg state
              call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
              saved_heap registry_heap /\
            (forall closed_heap,
              kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
                KernelClientHeapClosed closed_heap ->
              exists returned stopped returned_origin,
                kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked
                  KernelClientHeapClosed returned /\
                kernel_resumption_task_source_trace environment.(task_stack_call_external)
                  environment.(task_stack_call_port) critical.(critical_region_clients) sg
                  call.(os_sched_call_invocation) None call.(os_sched_call_origin)
                  parked stopped returned_origin returned /\
                (stopped = false ->
                 returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
                 exists selected,
                   armv7a_irq_restore_pointer_reads sg closed_heap
                     (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
                   (forall final, armv7a_restore_transition abi handler selected closed_heap final ->
                     task_create_stack_init_irq_continuation remaining environment critical sg args region
                       handler_region handler_fragments task_return lower upper initial_name original mask
                       initial_state (armv7a_continuation_resumed_call selected call)
                       (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))
                       (prefix ++ chunk) rest final frame))))
  end.

Lemma task_create_stack_init_irq_continuation_source : forall schedule environment critical sg args region
  handler_region handler_fragments task_return lower upper initial_name original mask initial_state,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial_state ->
  forall call state prefix suffix before (frame : Assertion),
  task_tcb_init_stack_same_call call original ->
  task_create_stack_init_entry_preserved sg args original initial_state state ->
  task_tcb_init_stack_source_preserved original initial_state state ->
  prefix ++ suffix = task_stack_init_core_push_words args.(createEntry) args.(createArgument) task_return ->
  Forall (fun value => 0 <= value < 4294967296) suffix ->
  (task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix suffix **
   task_tcb_init_stack_save_input environment critical sg call mask state **
   unmap_table_rep sg ** task_stack_fragments_rep handler_region handler_fragments ** frame) before ->
  task_create_stack_init_irq_continuation schedule environment critical sg args region handler_region
    handler_fragments task_return lower upper initial_name original mask initial_state
    call state prefix suffix before frame.
Proof.
  induction schedule as [|count remaining IH]; intros environment critical sg args region handler_region
    handler_fragments task_return lower upper initial_name original mask initial_state Hlayout Hentry
    call state prefix suffix before frame Hsame Hpreserved Hordinary Hwords Hranges Hpre.
  - cbn [task_create_stack_init_irq_continuation].
    match type of Hpre with ?P before => assert (Horder : P |--
      task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix suffix **
      (task_tcb_init_stack_save_input environment critical sg call mask state ** unmap_table_rep sg **
       task_stack_fragments_rep handler_region handler_fragments ** frame)) by entailer! end.
    destruct (task_stack_init_suffix_store_execution region.(stackRegionBase) args.(createStackTop)
      args.(createEntry) args.(createArgument) task_return (task_create_options args)
      lower upper prefix suffix _ before Hwords Hranges (Horder before Hpre))
      as [initialized [Hrun Hinitialized]].
    exists initialized; split; [exact Hrun|].
    assert (Houtput : (task_create_stack_init_output environment critical sg region args task_return lower upper
      original mask initial_state (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) **
      unmap_table_rep sg ** task_stack_fragments_rep handler_region handler_fragments ** frame) initialized).
    { match type of Hinitialized with ?P initialized => match goal with |- ?Q initialized =>
        assert (Hpack : P |-- Q) end end.
      { unfold task_create_stack_init_output; Exists call state; entailer!. }
      exact (Hpack initialized Hinitialized). }
    split; [exact Houtput|].
    match type of Houtput with ?P initialized => match goal with |- ?Q initialized =>
      assert (Hconsume : P |-- Q) end end.
    { sep_apply_l_atomic (task_create_stack_init_output_tcb_pre environment critical sg region args task_return
        lower upper initial_name original mask initial_state
        (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) Hlayout Hentry).
      Intros context checkpoint; Exists context checkpoint; entailer!; tauto. }
    exact (Hconsume initialized Houtput).
  - cbn [task_create_stack_init_irq_continuation].
    set (chunk := firstn count suffix).
    set (rest := skipn count suffix).
    assert (Hsplit : chunk ++ rest = suffix) by (unfold chunk, rest; apply firstn_skipn).
    assert (Hlength : Zlength prefix + Zlength chunk + Zlength rest = 16).
    { rewrite <- Z.add_assoc, <- Zlength_app, Hsplit, <- Zlength_app, Hwords; reflexivity. }
    assert (Hchunk : Forall (fun value => 0 <= value < 4294967296) chunk).
    { rewrite <- Hsplit, Forall_app in Hranges; tauto. }
    assert (Hrest : Forall (fun value => 0 <= value < 4294967296) rest).
    { rewrite <- Hsplit, Forall_app in Hranges; tauto. }
    match type of Hpre with ?P before => assert (Horder : P |--
      task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix
        (chunk ++ rest) **
      (task_tcb_init_stack_save_input environment critical sg call mask state ** unmap_table_rep sg **
       task_stack_fragments_rep handler_region handler_fragments ** frame)) end.
    { rewrite Hsplit; entailer!. }
    destruct (task_stack_init_partial_store_execution region.(stackRegionBase) args.(createStackTop)
      lower upper prefix chunk rest _ before Hlength Hchunk (Horder before Hpre))
      as [cut [Hstores Hcut]].
    exists cut; split; [exact Hstores|].
    intros Extra extra_resources extra_step extra_effect node handler suspended publication saved_heap
      Hhandler_call Hhandler_region Hhandler_fragments Horigin Hslice Hrunning
      Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hmask
      Hextension Hextra Henter Hexit Hpublish Hsource Hsave.
    set (buffer := task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop)
      lower upper (prefix ++ chunk) rest).
    match type of Hcut with ?P cut => assert (Hirq_input : P |--
      task_tcb_init_stack_save_input environment critical sg handler.(os_int_exit_interrupted_call) mask state **
      unmap_table_rep sg **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
      (buffer ** frame)) end.
    { rewrite Hhandler_call, Hhandler_region, Hhandler_fragments; unfold buffer; entailer!. }
    pose proof (task_create_stack_init_irq_source environment critical Extra extra_resources extra_step extra_effect
      sg args state node handler suspended publication mask cut saved_heap (buffer ** frame)) as Hirq.
    cbv zeta in Hirq.
    rewrite Hhandler_call in Hirq.
    destruct (Hirq Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
      Hpublication Hsp Hmask Hextension Hextra Henter Hexit Hpublish Hsource
      ltac:(rewrite Hhandler_call in Hirq_input; exact (Hirq_input cut Hcut)) Hsave)
      as [registry_heap [Hwrites [Hentry_stores Hreturned]]].
    exists registry_heap; split; [exact Hwrites|]. split; [exact Hentry_stores|].
    intros closed_heap Htrace.
    destruct (Hreturned closed_heap Htrace)
      as [returned [stopped [returned_origin [Hstates [Hsources Hreturn]]]]].
    exists returned, stopped, returned_origin.
    split; [exact Hstates|]. split; [exact Hsources|].
    intros Hnormal Hreturned_current.
    destruct (Hreturn Hnormal Hreturned_current) as [selected [Hpointers Hresume]].
    exists selected; split; [exact Hpointers|].
    intros final Hrestore.
    destruct (Hresume final Hrestore) as [Hresumed_same [Hstep_entry [Hstep_source Hfinal]]].
    set (resumed := armv7a_continuation_resumed_call selected call).
    set (current := os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).
    assert (Hsame_next : task_tcb_init_stack_same_call resumed original).
    { unfold resumed; unfold task_tcb_init_stack_same_call in *; destruct Hsame as [Hi [Ho Hs]];
        destruct Hresumed_same as [Hri [Hro Hrs]]; split; [congruence|]; split; congruence. }
    assert (Hentry_next : task_create_stack_init_entry_preserved sg args original initial_state current).
    { intros name Hinitial.
      specialize (Hpreserved name Hinitial).
      destruct Hsame as [Hi [Ho Hs]].
      specialize (Hstep_entry name).
      rewrite Hi, Ho in Hstep_entry.
      exact (Hstep_entry Hpreserved). }
    assert (Hsource_next : task_tcb_init_stack_source_preserved original initial_state current).
    { intros Hinitial.
      apply (proj1 (task_tcb_init_stack_same_call_source_iff call original current Hsame)).
      apply Hstep_source.
      apply (proj2 (task_tcb_init_stack_same_call_source_iff call original state Hsame)).
      exact (Hordinary Hinitial). }
    match type of Hfinal with ?P final => assert (Hnext : P |--
      task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop)
        lower upper (prefix ++ chunk) rest **
      task_tcb_init_stack_save_input environment critical sg resumed mask current **
      unmap_table_rep sg ** task_stack_fragments_rep handler_region handler_fragments ** frame) end.
    { rewrite Hhandler_region, Hhandler_fragments; unfold buffer; entailer!. }
    apply (IH environment critical sg args region handler_region handler_fragments task_return lower upper
      initial_name original mask initial_state Hlayout Hentry resumed current (prefix ++ chunk) rest final frame
      Hsame_next Hentry_next Hsource_next).
    + rewrite <- app_assoc, Hsplit; exact Hwords.
    + exact Hrest.
    + exact (Hnext final Hfinal).
Qed.

(** The real StackInit input is the producer of the initial induction
    invariant. No IRQ postcondition is supplied by the API caller. *)
Lemma task_create_stack_init_repeated_irq_tcb_pre : forall schedule environment critical sg args state
  call mask region handler_region handler_fragments task_return lower old_frame upper initial_name
  before (frame : Assertion),
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    call.(os_sched_call_invocation) call.(os_sched_call_origin) state ->
  (task_create_stack_init_input environment critical sg region args task_return lower old_frame upper
     call mask state ** unmap_table_rep sg **
   task_stack_fragments_rep handler_region handler_fragments ** frame) before ->
  exists prepared,
    kernel_heap_execution [] before prepared /\
    task_create_stack_init_irq_continuation schedule environment critical sg args region handler_region
      handler_fragments task_return lower upper initial_name call mask state call state []
      (task_stack_init_core_push_words args.(createEntry) args.(createArgument) task_return) prepared frame.
Proof.
  intros schedule environment critical sg args state call mask region handler_region handler_fragments
    task_return lower old_frame upper initial_name before frame Hlayout Hentry Hpre.
  match type of Hpre with ?P before => assert (Horder : P |--
    task_stack_init_pre TaskStackNoVFP region.(stackRegionBase) region.(stackRegionWords)
      args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower old_frame upper **
    (task_tcb_init_stack_save_input environment critical sg call mask state ** unmap_table_rep sg **
     task_stack_fragments_rep handler_region handler_fragments ** frame)) end.
  { unfold task_create_stack_init_input; entailer!. }
  destruct (task_stack_init_prefix_store_execution region.(stackRegionBase) region.(stackRegionWords)
    args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower old_frame upper []
    (task_stack_init_core_push_words args.(createEntry) args.(createArgument) task_return) _ before eq_refl
    (Horder before Hpre)) as [prepared [Hrun [Hranges Hprepared]]].
  exists prepared; split; [exact Hrun|].
  eapply task_create_stack_init_irq_continuation_source.
  - exact Hlayout.
  - exact Hentry.
  - repeat split; reflexivity.
  - intros name Hinitial; exact Hinitial.
  - apply task_tcb_init_stack_source_preserved_refl.
  - reflexivity.
  - exact Hranges.
  - match type of Hprepared with ?P prepared => match goal with |- ?Q prepared =>
      assert (Hclose : P |-- Q) by entailer! end end.
    exact (Hclose prepared Hprepared).
Qed.
