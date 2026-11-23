Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_preparation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Commands of the selected unmasked private-initialization interval.
    Hook constructors denote the TWO existing configured empty bodies,
    not arbitrary callbacks. Their separate positions permit an IRQ
    before, between, or after those actual calls. This is source syntax,
    not an OS-state/ownership record. *)
Inductive TaskTCBPrivateCommand : Type :=
| TaskTCBPrivateStore (field : TCBLayoutField) (value : Z)
| TaskTCBInitHookCall
| TaskTCBCreateHookCall.

Definition task_tcb_init_private_commands sg args : list TaskTCBPrivateCommand :=
  map (fun store => TaskTCBPrivateStore (fst store) (snd store))
    (task_tcb_init_source_layout_stores sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile) args) ++ [TaskTCBInitHookCall; TaskTCBCreateHookCall].

Definition task_tcb_init_private_command_writes sg slot command :=
  match command with
  | TaskTCBPrivateStore field word => task_tcb_init_field_writes
      sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg slot) field word
  | _ => []
  end.

Definition task_tcb_init_private_command_image image command :=
  match command with
  | TaskTCBPrivateStore field word => tcb_layout_write image field (Some word)
  | _ => image
  end.

Definition task_tcb_init_private_command_valid sg command : Prop :=
  match command with
  | TaskTCBPrivateStore field word =>
      In field (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile)) /\ 0 <= word < task_tcb_init_field_bound field
  | _ => True
  end.

Inductive task_tcb_init_private_execution sg slot : list TaskTCBPrivateCommand -> model -> model -> Prop :=
| task_tcb_init_private_execution_nil : forall heap,
    task_tcb_init_private_execution sg slot [] heap heap
| task_tcb_init_private_execution_cons : forall command commands before middle after,
    kernel_heap_execution (task_tcb_init_private_command_writes sg slot command) before middle ->
    task_tcb_init_private_execution sg slot commands middle after ->
    task_tcb_init_private_execution sg slot (command :: commands) before after.

Lemma task_tcb_init_private_commands_valid : forall sg args,
  task_tcb_init_parameters_in_range args ->
  Forall (task_tcb_init_private_command_valid sg) (task_tcb_init_private_commands sg args).
Proof.
  intros sg args Hranges; unfold task_tcb_init_private_commands; apply Forall_app; split.
  - apply Forall_map; apply task_tcb_init_source_field_ranges; exact Hranges.
  - repeat constructor.
Qed.

Lemma task_tcb_init_private_commands_image : forall sg args image,
  fold_left task_tcb_init_private_command_image (task_tcb_init_private_commands sg args) image =
  task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile) args image.
Proof.
  intros sg args image; unfold task_tcb_init_private_commands; rewrite fold_left_app.
  cbn [fold_left task_tcb_init_private_command_image].
  assert (Hmap : forall stores seed,
    fold_left task_tcb_init_private_command_image
      (map (fun store => TaskTCBPrivateStore (fst store) (snd store)) stores) seed =
    fold_left (fun current store => tcb_layout_write current (fst store) (Some (snd store))) stores seed).
  { induction stores as [|[field word] stores IH]; intro seed; cbn; auto. }
  rewrite Hmap; apply task_tcb_init_source_layout_stores_image_eq.
Qed.

(** Disjoint private stores and selected empty hooks preserve an arbitrary
    owned frame. Between chunks the actual IRQ producer below, not this
    lemma, advances the OS world. No unchanged-world frame crosses IRQ. *)
Lemma task_tcb_init_private_commands_execution : forall commands sg slot image
  (frame : Assertion) before,
  Forall (task_tcb_init_private_command_valid sg) commands ->
  (task_slot_storage_rep sg slot image ** frame) before ->
  exists after, task_tcb_init_private_execution sg slot commands before after /\
    (task_slot_storage_rep sg slot
      (fold_left task_tcb_init_private_command_image commands image) ** frame) after.
Proof.
  induction commands as [|command commands IH]; intros sg slot image frame before Hvalid Hpre.
  - exists before; split; [constructor|exact Hpre].
  - inversion Hvalid as [|? ? Hcommand Hcommands]; subst.
    assert (Hstep : exists middle,
      kernel_heap_execution (task_tcb_init_private_command_writes sg slot command) before middle /\
      (task_slot_storage_rep sg slot (task_tcb_init_private_command_image image command) ** frame) middle).
    { destruct command as [field value| |].
      - destruct (task_tcb_init_field_sequence_execution [(field, value)]
          sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
          (task_slot_addr sg slot) image frame before ltac:(constructor; [exact Hcommand|constructor]) Hpre)
          as [middle [Hrun Hmiddle]].
        exists middle; cbn [task_tcb_init_private_command_writes task_tcb_init_private_command_image].
        cbn [task_tcb_init_field_sequence_writes flat_map fst snd fold_left] in Hrun, Hmiddle.
        rewrite app_nil_r in Hrun; split; assumption.
      - exists before; split; [split; [constructor|split; reflexivity]|exact Hpre].
      - exists before; split; [split; [constructor|split; reflexivity]|exact Hpre]. }
    destruct Hstep as [middle [Hrun Hmiddle]].
    destruct (IH sg slot (task_tcb_init_private_command_image image command) frame middle Hcommands Hmiddle)
      as [after [Hrest Hafter]].
    exists after; split; [econstructor; eassumption|exact Hafter].
Qed.

(** Pure consequence of the same concrete IRQ entry's established
    saved-stack binding. It is used only with that source entry below;
    no validity/stack fact is requested from CPU authority. *)
Lemma task_tcb_init_private_irq_parked_valid : forall sg state node call sp fragments publication,
  UCOS2_state_inv sg state -> state.(SchedState).(isRunning) = true ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0 fragments ->
  task_publication_happened state.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) sp ->
  UCOS2_state_inv sg (armv7a_irq_live_parked_state state call sp fragments).
Proof.
  intros sg state node call sp fragments publication Hvalid Hrunning Hnode Hid Hgen Hnone
    Hregion Hgeometry Hpublication Hsp.
  pose proof (armv7a_irq_live_entry_preserves_validity sg state node sp call.(os_sched_call_stack)
    Hvalid Hnode Hid Hgen Hnone) as Hstored.
  pose proof (armv7a_irq_live_entry_saved_stack_binding state node sp call fragments publication
    Hrunning Hnode Hid Hgen Hnone Hregion Hgeometry Hpublication Hsp) as Hbinding.
  unfold armv7a_irq_live_parked_state; apply UCOS2_replace_parked_stacks_preserves_validity.
  - exact Hstored.
  - apply os_sched_park_saved_context_preserves_consistency; [|exact Hbinding].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hstored; tauto.
Qed.

(** Finite interleavings of this concrete private command sequence with
    the already registered first-level IRQ family. Each count chooses
    the next command boundary; zero permits repeated IRQs at one cut.
    The base case supplies the EXISTING second Save input and allocation
    history used by [task_tcb_init_stack_save_output_commit]. A stopped
    or non-returning registered trace has no claimed C continuation. *)
Fixpoint task_tcb_init_private_irq_continuation (schedule : list nat)
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (args : TaskCreateArgs) (initial_name : Z)
  (handler_region : TaskStackRegion) (handler_fragments : TaskStackFragments)
  (original : OsSchedCallContext) (mask : Z)
  (initial detached : UCOS2_Verify_State) (slot : Z) (free_image : TCBLayoutImage)
  (call : OsSchedCallContext) (state : UCOS2_Verify_State)
  (commands : list TaskTCBPrivateCommand) (image : TCBLayoutImage)
  (before : model) (frame : Assertion) {struct schedule} : Prop :=
  match schedule with
  | [] =>
      exists initialized,
        task_tcb_init_private_execution sg slot commands before initialized /\
        (coq_prop (task_tcb_init_stack_same_call call original /\
          task_tcb_init_call_preserved sg original.(os_sched_call_invocation) detached state /\
          task_tcb_init_stack_source_preserved original initial state) &&
         (task_slot_storage_rep sg slot
            (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
              sg.(osKernelConfig).(cfgTaskProfile)
              (task_tcb_init_stack_call_args args initial_name) free_image) **
          task_tcb_init_stack_save_input environment critical sg call mask state **
          unmap_table_rep sg ** task_stack_fragments_rep handler_region handler_fragments ** frame)) initialized
  | count :: remaining =>
      let chunk := firstn count commands in
      let rest := skipn count commands in
      let abi := environment.(task_stack_call_continuations) in
      exists cut,
        task_tcb_init_private_execution sg slot chunk before cut /\
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
          (forall client_cut current next returned, extra_effect sg client_cut current next returned ->
            UCOS2_state_inv sg current ->
            task_saved_pointer_at current suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
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
                     task_tcb_init_private_irq_continuation remaining environment critical sg args initial_name
                       handler_region handler_fragments original mask initial detached slot free_image
                       (armv7a_continuation_resumed_call selected call)
                       (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) rest
                       (fold_left task_tcb_init_private_command_image chunk image) final frame))))
  end.

Lemma task_tcb_init_private_irq_continuation_source : forall schedule environment critical sg args initial_name
  handler_region handler_fragments original mask initial detached slot free_image call state commands image
  before (frame : Assertion),
  task_tcb_init_stack_same_call call original ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) detached state ->
  task_tcb_init_stack_source_preserved original initial state ->
  Forall (task_tcb_init_private_command_valid sg) commands ->
  fold_left task_tcb_init_private_command_image commands image =
    task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile) (task_tcb_init_stack_call_args args initial_name) free_image ->
  (task_slot_storage_rep sg slot image ** task_tcb_init_stack_save_input environment critical sg call mask state **
   unmap_table_rep sg ** task_stack_fragments_rep handler_region handler_fragments ** frame) before ->
  task_tcb_init_private_irq_continuation schedule environment critical sg args initial_name
    handler_region handler_fragments original mask initial detached slot free_image call state commands image before frame.
Proof.
  induction schedule as [|count remaining IH]; intros environment critical sg args initial_name
    handler_region handler_fragments original mask initial detached slot free_image call state commands image
    before frame Hsame Hhistory Hordinary Hcommands Himage Hpre.
  - cbn [task_tcb_init_private_irq_continuation].
    match type of Hpre with ?P before => assert (Horder : P |--
      task_slot_storage_rep sg slot image **
      (task_tcb_init_stack_save_input environment critical sg call mask state ** unmap_table_rep sg **
       task_stack_fragments_rep handler_region handler_fragments ** frame)) by entailer! end.
    destruct (task_tcb_init_private_commands_execution commands sg slot image _ before Hcommands
      (Horder before Hpre)) as [initialized [Hrun Hinitialized]].
    exists initialized; split; [exact Hrun|].
    match type of Hinitialized with ?P initialized => match goal with |- ?Q initialized =>
      assert (Hpack : P |-- Q) end end.
    { rewrite Himage; entailer!. }
    exact (Hpack initialized Hinitialized).
  - cbn [task_tcb_init_private_irq_continuation].
    set (chunk := firstn count commands).
    set (rest := skipn count commands).
    assert (Hsplit : chunk ++ rest = commands) by (unfold chunk, rest; apply firstn_skipn).
    assert (Hchunk : Forall (task_tcb_init_private_command_valid sg) chunk).
    { rewrite <- Hsplit, Forall_app in Hcommands; tauto. }
    assert (Hrest : Forall (task_tcb_init_private_command_valid sg) rest).
    { rewrite <- Hsplit, Forall_app in Hcommands; tauto. }
    match type of Hpre with ?P before => assert (Horder : P |--
      task_slot_storage_rep sg slot image **
      (task_tcb_init_stack_save_input environment critical sg call mask state ** unmap_table_rep sg **
       task_stack_fragments_rep handler_region handler_fragments ** frame)) by entailer! end.
    destruct (task_tcb_init_private_commands_execution chunk sg slot image _ before Hchunk
      (Horder before Hpre)) as [cut [Hstores Hcut]].
    exists cut; split; [exact Hstores|].
    intros Extra extra_resources extra_step extra_effect node handler suspended publication saved_heap
      Hhandler_call Hhandler_region Hhandler_fragments Horigin Hslice Hrunning
      Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hmask
      Hextension Hextra Henter Hexit Hpublish Hsource Hsave.
    set (buffer := task_slot_storage_rep sg slot (fold_left task_tcb_init_private_command_image chunk image)).
    match type of Hcut with ?P cut => assert (Hirq_input : P |--
      task_tcb_init_stack_save_input environment critical sg handler.(os_int_exit_interrupted_call) mask state **
      unmap_table_rep sg **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
      (buffer ** frame)) end.
    { rewrite Hhandler_call, Hhandler_region, Hhandler_fragments; unfold buffer; entailer!. }
    assert (Hvalid : UCOS2_state_inv sg state).
    { match type of Hcut with ?P cut => assert (Hread : P |-- coq_prop (UCOS2_state_inv sg state)) end.
      { unfold task_tcb_init_stack_save_input; entailer!. }
      exact (Hread cut Hcut). }
    pose proof (task_tcb_init_private_irq_parked_valid sg state node call
      suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments) publication
      Hvalid Hrunning Hnode Hid Hgen Hnone Hregion Hgeometry Hpublication Hsp) as Hparked.
    pose proof (task_create_stack_init_irq_source environment critical Extra extra_resources extra_step extra_effect
      sg args state node handler suspended publication mask cut saved_heap (buffer ** frame)) as Hirq.
    cbv zeta in Hirq; rewrite Hhandler_call in Hirq.
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
    assert (Hcurrent_valid : UCOS2_state_inv sg current).
    { match type of Hfinal with ?P final => assert (Hread : P |-- coq_prop (UCOS2_state_inv sg current)) end.
      { unfold task_tcb_init_stack_save_input, current; entailer!. }
      exact (Hread final Hfinal). }
    assert (Hstep_history : task_tcb_init_call_preserved sg call.(os_sched_call_invocation) state current).
    { eapply (task_tcb_init_irq_preserves_call environment critical sg call state node
        suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments) returned returned_origin).
      - exact Hrunning.
      - exact Hnode.
      - exact Hparked.
      - rewrite Hnormal in Hsources; exact Hsources.
      - exact Hcurrent_valid. }
    assert (Hhistory_next : task_tcb_init_call_preserved sg original.(os_sched_call_invocation) detached current).
    { rewrite (proj1 Hsame) in Hstep_history.
      eapply task_tcb_init_call_preserved_trans; eassumption. }
    assert (Hsource_next : task_tcb_init_stack_source_preserved original initial current).
    { intros Hinitial.
      apply (proj1 (task_tcb_init_stack_same_call_source_iff call original current Hsame)).
      apply Hstep_source.
      apply (proj2 (task_tcb_init_stack_same_call_source_iff call original state Hsame)).
      exact (Hordinary Hinitial). }
    match type of Hfinal with ?P final => assert (Hnext : P |--
      task_slot_storage_rep sg slot (fold_left task_tcb_init_private_command_image chunk image) **
      task_tcb_init_stack_save_input environment critical sg resumed mask current **
      unmap_table_rep sg ** task_stack_fragments_rep handler_region handler_fragments ** frame) end.
    { rewrite Hhandler_region, Hhandler_fragments; unfold buffer; entailer!. }
    apply (IH environment critical sg args initial_name handler_region handler_fragments original mask
      initial detached slot free_image resumed current rest
      (fold_left task_tcb_init_private_command_image chunk image) final frame
      Hsame_next Hhistory_next Hsource_next Hrest).
    + rewrite <- fold_left_app, Hsplit; exact Himage.
    + exact (Hnext final Hfinal).
Qed.

(** The name pointer's range comes from the already owned Name bytes,
    not from an extra literal-pool owner or a new scalar premise. *)
Lemma task_tcb_init_private_name_pointer_range : forall sg state pointer chars,
  readable_name state.(NameState) pointer chars ->
  UCOS2_inv sg state |-- coq_prop (0 <= pointer < 4294967296).
Proof.
  intros sg state pointer chars [_ [Hchars Hnul]].
  assert (Hbyte : exists byte, state.(NameState).(nameBytes) pointer = Some byte).
  { destruct chars as [|byte chars].
    - exists 0; cbn in Hnul; rewrite Z.add_0_r in Hnul; exact Hnul.
    - exists byte; specialize (Hchars 0%nat byte eq_refl); cbn in Hchars.
      rewrite Z.add_0_r in Hchars; exact Hchars. }
  destruct Hbyte as [byte Hbyte].
  rewrite UCOS2_inv_split_names; Intros.
  sep_apply_l_atomic (store_name_bytes_split_byte state.(NameState) pointer byte Hbyte).
  unfold name_byte_rep, store_uchar, isvalidptr_char; entailer!.
  change addr_max_unsigned with 4294967295 in *; lia.
Qed.

(** Actual BASIC OSTaskCreate consumer at OS_TCBInit_Stack.c's detach Restore return.
    Its existing post is produced by the already checked uninterrupted,
    IRQ and foreign-call source branches. The owned detached TCB is then
    initialized by exactly the source list plus the two selected empty
    hooks. At the last cut the finite continuation provides second Save's
    current-world input, preserving precisely the history used by its
    existing commit consumer; no new public precondition is introduced. *)
Lemma task_tcb_init_private_repeated_irq_save_pre :
  forall schedule environment critical sg args region lower upper initial_name original first_call mask saved
    initial acquired slot rest free_image handler_region handler_fragments before (frame : Assertion),
  args.(createExtension) = TaskCreateBasic ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_stack_same_call first_call original ->
  task_tcb_init_stack_source_preserved original initial acquired ->
  interrupt_saved_value mask saved ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) acquired ->
  task_tcb_init_detach_observation (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) acquired slot rest free_image ->
  (task_tcb_init_stack_restore_output environment critical sg first_call saved
     (task_tcb_init_detached_state (task_tcb_init_stack_call_args args initial_name)
       original.(os_sched_call_invocation) original.(os_sched_call_origin) acquired slot rest free_image) **
   task_slot_storage_rep sg slot free_image ** unmap_table_rep sg **
   task_stack_fragments_rep handler_region handler_fragments ** frame) before ->
  exists call state,
    task_tcb_init_private_irq_continuation schedule environment critical sg args initial_name
      handler_region handler_fragments original mask initial
      (task_tcb_init_detached_state (task_tcb_init_stack_call_args args initial_name)
        original.(os_sched_call_invocation) original.(os_sched_call_origin) acquired slot rest free_image)
      slot free_image call state (task_tcb_init_private_commands sg (task_tcb_init_stack_call_args args initial_name))
      free_image before frame.
Proof.
  intros schedule environment critical sg args region lower upper initial_name original first_call mask saved
    initial acquired slot rest free_image handler_region handler_fragments before frame
    Hbasic Hlayout Hsame Hordinary Hsaved Hentry Hdetach Hpre.
  set (detached := task_tcb_init_detached_state (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) acquired slot rest free_image).
  assert (Hvalid : UCOS2_state_inv sg detached).
  { eapply task_tcb_init_detach_preserves_validity; eassumption. }
  assert (Hdetached_source : task_tcb_init_stack_source_preserved original initial detached).
  { intros Hinitial; eapply task_tcb_init_detach_preserves_call_source; exact (Hordinary Hinitial). }
  match type of Hpre with ?P before => assert (Hopen : P |-- EX call state,
    coq_prop (task_tcb_init_stack_same_call call original /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) detached state /\
      task_tcb_init_stack_source_preserved original initial state) &&
    (task_slot_storage_rep sg slot free_image **
     task_tcb_init_stack_save_input environment critical sg call mask state ** unmap_table_rep sg **
     task_stack_fragments_rep handler_region handler_fragments ** frame)) end.
  { fold detached.
    sep_apply_l_atomic (task_tcb_init_stack_restore_output_caller environment critical sg first_call original
      saved detached Hsame).
    sep_apply_l_atomic (task_tcb_init_stack_restore_output_reacquire environment critical sg original saved
      mask detached Hsaved).
    Intros call state.
    assert (Hstep : task_tcb_init_stack_source_preserved original detached state) by tauto.
    pose proof (task_tcb_init_stack_source_preserved_trans original initial detached state
      Hdetached_source Hstep) as Hsource.
    Exists call state; entailer!. }
  destruct (Hopen before Hpre) as [call [state [[Hreturned [Hhistory Hsource]] Howned]]].
  assert (Hnames_enabled : sg.(osKernelConfig).(cfgTaskNames) = true).
  { pose proof (proj1 Hentry) as Hprofile.
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
      tcb64_configuration in Hprofile; tauto. }
  destruct (proj2 (proj2 (proj2 (proj2 Hentry))) Hnames_enabled) as [chars Hname].
  destruct (Hhistory Hvalid) as [_ [_ [_ Hnames]]].
  change (acquired.(NameState) = state.(NameState)) in Hnames.
  assert (Hname_pointer : readable_name state.(NameState) initial_name chars).
  { unfold task_tcb_init_stack_call_args, task_create_tcb_args in Hname.
    rewrite Hbasic in Hname; cbn [initNamePointer] in Hname.
    rewrite <- Hnames; exact Hname. }
  assert (Hname_input : task_tcb_init_stack_save_input environment critical sg call mask state |--
    coq_prop (0 <= initial_name < 4294967296)).
  { eapply derivable1_trans with (y := UCOS2_inv sg state **
      (kernel_call_execution_owned environment.(task_stack_call_external)
        environment.(task_stack_call_platform) call mask ** task_tcb_init_stack_capsules environment state)).
    - unfold task_tcb_init_stack_save_input, critical_region_outside.
      rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
      unfold UCOS2_inv; entailer!.
    - sep_apply_l_atomic (task_tcb_init_private_name_pointer_range sg state initial_name chars Hname_pointer).
      entailer!. }
  assert (Hname_range : 0 <= initial_name < 4294967296).
  { match type of Howned with ?P before => assert (Hread : P |-- coq_prop (0 <= initial_name < 4294967296)) end.
    { sep_apply_l_atomic Hname_input; entailer!. }
    exact (Hread before Howned). }
  pose proof (task_create_stack_pointer_in_range TaskStackNoVFP region args lower upper Hlayout) as Hpointer.
  assert (Hstack_range : 0 <= task_stack_init_sp TaskStackNoVFP args.(createStackTop) < 4294967296).
  { pose proof (proj1 (proj1 Hlayout)) as Hregion.
    unfold valid_task_stack_region in Hregion; unfold task_stack_saved_pointer_in_range in Hpointer; lia. }
  pose proof (proj1 (task_tcb_init_entry_priority_in_range sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) acquired Hentry)) as Hpriority.
  assert (Hranges : task_tcb_init_parameters_in_range (task_tcb_init_stack_call_args args initial_name)).
  { unfold task_tcb_init_parameters_in_range, task_tcb_init_stack_call_args, task_create_tcb_args in *.
    rewrite Hbasic in *; cbn in Hpriority |- *; repeat split; lia. }
  exists call, state.
  eapply task_tcb_init_private_irq_continuation_source.
  - exact Hreturned.
  - exact Hhistory.
  - exact Hsource.
  - apply task_tcb_init_private_commands_valid; exact Hranges.
  - apply task_tcb_init_private_commands_image.
  - exact Howned.
Qed.

