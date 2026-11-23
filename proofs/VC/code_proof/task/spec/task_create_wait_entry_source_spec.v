Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From compcert.lib Require Import Integers.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_create_wait_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** At the zero-count branch the actual little-endian unsigned-short read
    observes two zero bytes. Its equality with the abstract count follows
    from the owned typed cell, including QCP's modulo-byte encoding. *)
Lemma task_create_wait_count_read_zero : forall address count (frame : Assertion) heap,
  (address # UShort |-> count ** frame) heap ->
  uchar_load address 0 heap -> uchar_load (address + 1) 0 heap -> count = 0.
Proof.
  intros address count frame heap Howned Hread_low Hread_high.
  assert (Hsplit : address # UShort |-> count ** frame |--
    coq_prop (0 <= count < 65536) &&
    EX low high, coq_prop (merge_short low high count) &&
      (store_byte address low ** (store_byte (address + 1) high ** frame))).
  { unfold store_ushort, store_2byte; Intros low high; Exists low high; entailer!; lia. }
  destruct (Hsplit heap Howned) as [Hrange [low [high [Hmerge Hcells]]]].
  destruct (framed_byte_store_observation _ _ _ _ Hcells) as [a [Ha Hlow]].
  assert (Horder : store_byte address low ** (store_byte (address + 1) high ** frame) |--
    store_byte (address + 1) high ** (store_byte address low ** frame)) by entailer!.
  destruct (framed_byte_store_observation _ _ _ _ (Horder heap Hcells)) as [b [Hb Hhigh]].
  destruct Hread_low as [_ [a' [Ha' Hzero_low]]].
  destruct Hread_high as [_ [b' [Hb' Hzero_high]]].
  assert (a' = a) by congruence; assert (b' = b) by congruence; subst a' b'.
  assert (Hlow_zero : Byte.eqm low 0)
    by (eapply Byte.eqm_trans; [exact Hlow|apply Byte.eqm_sym; exact Hzero_low]).
  assert (Hhigh_zero : Byte.eqm high 0)
    by (eapply Byte.eqm_trans; [exact Hhigh|apply Byte.eqm_sym; exact Hzero_high]).
  pose proof (merge_short_eqm low high 0 0 count Hlow_zero Hhigh_zero Hmerge) as Hzero.
  change (count mod 65536 = 0 mod 256 + 0 mod 256 * 256) in Hzero.
  rewrite (Z.mod_small count _ Hrange) in Hzero; exact Hzero.
Qed.

(** The existing ordinary API-entry boundary exchanges only the current
    execution label. The old TaskCreate focus, saved-SP relation and history
    handles survive the registration and the same uninterrupted first Save.
    Type, nesting and zero-count facts come from these actual byte reads.
    Interruptible entry intervals retain their separate source producers. *)
Lemma task_create_foreign_wait_entry_source : forall environment critical arch
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg previous original suspended mask state eid event before entered registers
  final_registers acquired after (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let entry := replace_TskS (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state in
  sem_pend_task_call_stage sg previous state ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key previous.(os_sched_call_stack))) ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  mutex_query_lookup state eid event -> event_addr sg eid <> 0 -> event_object_layout_prop sg eid ->
  (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      previous mask ** kernel_program_inv sg state **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) before ->
  kernel_sequential_call_source boundary previous state.(TskState).(taskLifecycle).(taskNextInvocation)
    before entered ->
  uchar_load (event_addr sg eid + OSEventType_off) 3 entered ->
  uchar_load sg.(g_OSIntNesting) 0 entered -> uchar_load sg.(g_OSLockNesting) 0 entered ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) entry entered
    final_registers acquired after ->
  uchar_load (event_addr sg eid + OSEventCnt_off) 0 after ->
  uchar_load (event_addr sg eid + OSEventCnt_off + 1) 0 after ->
  kernel_call_save_uninterrupted_execution arch registers entry entered final_registers acquired after /\
  acquired = entry /\
  sem_pend_precritical_error (event_addr sg eid) 3 0 0 = None /\
  os_sched_selection_enabled entry = true /\
  task_invocation_active entry.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
  task_saved_pointer_at entry suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) /\
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
  exists old,
    sem_pend_wait_entry sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old /\
    kernel_call_task_source call entry /\
    sched_current_consistency entry.(TskState) entry.(SchedState) /\
    (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
     os_sched_context_resources environment.(task_stack_call_external) call ** kernel_program_inv sg entry **
     armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros environment critical arch boundary save sg previous original suspended mask state eid event before
    entered registers final_registers acquired after frame abi focus call entry Hstage Hcoverage Hactive Hpointer
    Hlookup Hnonnull Hlayout Hpre Hboundary Htype_read Hint_read Hlock_read Hreturn Hcpsr Hmask Hsave Hlow Hhigh.
  pose proof Hstage as [[Horigin [_ Hcurrent]] [Hrunning [node [Hready [Hgen Hfields]]]]].
  assert (Hlive : task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin)).
  { rewrite Horigin; exists node; exact (conj (proj1 Hready) Hgen). }
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg state) && TT) end.
    { rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  destruct (kernel_sequential_call_register_focused_world _ _ _ abi boundary sg previous mask state focus
    before entered frame Hlive Hboundary Hpre) as [Hmemory Hentered].
  fold call entry in Hentered.
  assert (Hentry_valid : UCOS2_state_inv sg entry)
    by (apply UCOS2_begin_task_invocation_preserves_validity; assumption).
  assert (Hstage_entry : sem_pend_task_call_stage sg call entry).
  { unfold sem_pend_task_call_stage, kernel_call_task_source.
    split.
    - split; [exact Horigin|]. split.
      + apply task_begin_invocation_active; exact Hlive.
      + exact Hcurrent.
    - split; [exact Hrunning|]. exists node; split; [exact Hready|exact (conj Hgen Hfields)]. }
  assert (Hactive_entry : task_invocation_active entry.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { apply task_begin_invocation_preserves_invocation_active; [|exact Hactive].
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 (proj2 Hvalid))))))). }
  assert (Htype : event.(eventType) = OS_EVENT_TYPE_SEM).
  { match type of Hentered with ?P entered => assert (Hcell : P |--
      (event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type event.(eventType) ** TT) end.
    { rewrite kernel_program_inv_split_unmap.
      sep_apply_l_atomic (sem_post_field_split_full sg entry eid event EventTypeField Hlookup ltac:(simpl; tauto)).
      cbn [event_cell event_image event_field_offset]; unfold OSEventType_off; entailer!; intros ? ?; exact I. }
    pose proof (uchar_load_deterministic _ _ _ _
      (framed_uchar_store_load _ _ _ _ (Hcell entered Hentered)) Htype_read) as Hencoded.
    destruct event.(eventType); cbn [encode_event_type] in Hencoded; congruence. }
  assert (Hnesting : entry.(IntrState).(intNesting) = 0 /\ entry.(IntrState).(lockNesting) = 0).
  { assert (Hcells : kernel_program_inv sg entry |--
      sg.(g_OSIntNesting) # UChar |-> entry.(IntrState).(intNesting) **
      sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) ** TT).
    { rewrite kernel_program_inv_split_unmap, UCOS2_inv_split_interrupt.
      unfold interrupt_inv, store_int_state; entailer!; intros ? ?; exact I. }
    match type of Hentered with ?P entered => assert (Hint : P |--
      sg.(g_OSIntNesting) # UChar |-> entry.(IntrState).(intNesting) ** TT) end.
    { sep_apply_l_atomic Hcells; entailer!; intros ? ?; exact I. }
    match type of Hentered with ?P entered => assert (Hlock : P |--
      sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) ** TT) end.
    { sep_apply_l_atomic Hcells; entailer!; intros ? ?; exact I. }
    split; eapply uchar_load_deterministic; [|exact Hint_read| |exact Hlock_read];
      eapply framed_uchar_store_load; [exact (Hint entered Hentered)|exact (Hlock entered Hentered)]. }
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hcpsr|reflexivity]).
  match type of Hentered with ?P entered => assert (Horder : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      call mask ** (kernel_program_inv sg entry **
    armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame))
    by entailer! end.
  pose proof (Horder entered Hentered) as Howned; rewrite <- Hmask in Howned.
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call
    (kernel_save_read_cpsr registers) entry entered final_registers acquired after _ Hsaved Howned Hsave)
    as [Hstate [Hafter_memory [Hlr [Hr0 Hafter]]]].
  assert (Hzero : encode_event_cnt_value event = 0).
  { match type of Hafter with ?P after => assert (Hcell : P |--
      (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value event ** TT) end.
    { rewrite kernel_program_inv_split_unmap.
      sep_apply_l_atomic (sem_post_count_split_full sg entry eid event Hlookup Htype).
      entailer!; intros ? ?; exact I. }
    exact (task_create_wait_count_read_zero _ _ _ _ (Hcell after Hafter) Hlow Hhigh). }
  split.
  - unfold kernel_call_save_uninterrupted_execution; econstructor.
    + constructor; [exact Hreturn|reflexivity].
    + exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave).
  - split; [exact Hstate|]. split; [apply sem_pend_precritical_clear; exact Hnonnull|].
    split.
    + unfold os_sched_selection_enabled; rewrite (proj1 Hnesting), (proj2 Hnesting); reflexivity.
    + split; [exact Hactive_entry|]. split; [exact Hpointer|]. split; [exact Hcoverage|].
      destruct (sem_pend_task_stage_wait_entry sg call entry eid event Hstage_entry Hentry_valid Hlookup Htype
        Hzero Hlayout) as [old [Hwait [_ [Hsource Hcache]]]].
      exists old; split; [exact Hwait|]. split; [exact Hsource|]. split; [exact Hcache|].
      match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) by entailer! end end.
      exact (Hclose after Hafter).
Qed.

(** Concrete consumer of the entry producer and the adopted foreign-wait
    return theorem. Ordinary entry, actual zero-count observation, wait
    stores, scheduler Save/selection and the old pending owner's restore
    belong to one connected execution. The pre-existing ready-list prefix
    selects this returning branch; no future selection/result is assumed.
    The platform transitions and the reference no-write switch hook retain
    their existing explicit boundaries. *)
Lemma task_create_foreign_call_wait_return_source : forall environment critical arch
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg previous mask state eid event timeout tail original suspended saved original_entry
  call_before region args task_return lower old_frame upper
  old_sp cpsr values lr prefix suffix first old_words publication (frame : Assertion)
  before entered first_registers first_final acquired after,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let entry := replace_TskS (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state in
  sem_pend_task_call_stage sg previous state ->
  state.(SchedState).(readyList) = previous.(os_sched_call_stack).(stackLeaseSlot) ::
    original.(os_sched_call_stack).(stackLeaseSlot) :: tail ->
  state.(TskState).(parkedTaskStacks) (task_stack_key previous.(os_sched_call_stack)) = None ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key previous.(os_sched_call_stack))) ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  mutex_query_lookup state eid event -> event_addr sg eid <> 0 -> event_object_layout_prop sg eid ->
  0 <= timeout < 4294967296 ->
  previous.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region previous.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range previous.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    previous.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range previous.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened state.(TskState) publication previous.(os_sched_call_stack).(stackLeaseSlot)
    previous.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = previous.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      previous mask ** kernel_program_inv sg state **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
   (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** frame)) before ->
  kernel_sequential_call_source boundary previous state.(TskState).(taskLifecycle).(taskNextInvocation)
    before entered ->
  uchar_load (event_addr sg eid + OSEventType_off) 3 entered ->
  uchar_load sg.(g_OSIntNesting) 0 entered -> uchar_load sg.(g_OSLockNesting) 0 entered ->
  first_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr first_registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask first_registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr first_registers) entry entered
    first_final acquired after ->
  uchar_load (event_addr sg eid + OSEventCnt_off) 0 after ->
  uchar_load (event_addr sg eid + OSEventCnt_off + 1) 0 after ->
  kernel_call_save_uninterrupted_execution arch first_registers entry entered first_final acquired after /\
  acquired = entry /\
  exists old waited,
    let waiting := event_pend_state sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old PendSem timeout in
    let checkpoint := os_sched_prefix_state waiting in
    let fragments := prefix ++ [(first, first + 16,
      map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
    let foreign_saved := armv7a_task_save_image call old_sp cpsr values lr fragments in
    let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
      foreign_saved.(armv7a_continuation_sp) in
    sem_pend_wait_fragment sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old timeout after waited /\
    (forall cursor written middle final_cursor released,
      cursor.(kernel_restore_r0) = first_final.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor waited written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor released ->
      kernel_call_restore_uninterrupted_execution arch cursor waited final_cursor released /\
      (forall registers final_registers sched_acquired saved_heap,
        registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask first_final.(kernel_save_r0) ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) waiting released
          final_registers sched_acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers waiting released final_registers sched_acquired saved_heap /\
        sched_acquired = waiting /\
        exists prefix_heap stack_written stored,
          os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
          kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap stack_written /\
          pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) stack_written /\
          kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
            foreign_saved.(armv7a_continuation_sp)) stack_written stored /\
          (forall captured hooked,
            armv7a_task_capture_transition task_abi call foreign_saved stored captured ->
            kernel_heap_execution [] captured hooked ->
            kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
            exists installed selected,
              sched_install_heap_fragment sg hooked installed
                (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
              armv7a_continuation_restore_reads selected installed /\
              selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
              selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
              selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
              (forall restored,
                armv7a_task_restore_transition task_abi call selected installed restored ->
                forall return_cursor return_written return_middle return_final final_heap,
                return_cursor.(kernel_restore_r0) = saved ->
                return_cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
                armv7a_restore_prefix_transition restore return_cursor restored return_written return_middle ->
                armv7a_restore_suffix_transition restore return_written return_middle return_final final_heap ->
                let retained := interrupt_platform_saved environment.(task_stack_call_platform)
                  (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation)
                    call.(os_sched_call_origin)) **
                  critical_region_inside critical sg call.(os_sched_call_invocation) waiting ** frame in
                os_sched_source_switch_execution environment.(task_stack_call_external)
                  environment.(task_stack_call_platform) environment.(task_stack_call_port) abi task_abi
                  sg checkpoint call old_sp cpsr values lr foreign_saved original.(os_sched_call_stack)
                  selected prefix_heap restored /\
                kernel_call_restore_uninterrupted_execution arch return_cursor restored return_final final_heap /\
                (os_sched_stack_return_post environment kernel_program_inv sg original
                  (armv7a_irq_fiq_mask saved) call_before ** retained) final_heap /\
                (task_create_stack_post environment critical sg region args task_return lower old_frame upper
                  original (armv7a_irq_fiq_mask saved) 0 ** retained) final_heap)))).
Proof.
  intros environment critical arch boundary save restore task_abi sg previous mask state eid event timeout tail
    original suspended saved original_entry call_before region args task_return lower old_frame upper
    old_sp cpsr values lr prefix suffix first old_words publication frame before entered first_registers first_final
    acquired after abi focus call entry Hstage Hlist Habsent Hcoverage Horigin Hbinding Hcall Hslice Hsuspended_mask
    Hactive Hpointer Hparked Hlookup Hnonnull Hlayout Htimeout Hfragments Hregion Hgeometry Hsp_range Hpublication
    Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hpre Hboundary Htype_hint Hint_hint Hlock_hint
    Hfirst_return Hfirst_cpsr Hfirst_mask Hfirst_save Hcount_low Hcount_high.
  set (handles := interrupt_platform_saved environment.(task_stack_call_platform)
    (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** frame).
  destruct (task_create_foreign_wait_entry_source environment critical arch boundary save sg previous original
    suspended mask state eid event before entered first_registers first_final acquired after handles
    Hstage Hcoverage Hactive Hpointer Hlookup Hnonnull Hlayout Hpre Hboundary Htype_hint Hint_hint Hlock_hint
    Hfirst_return Hfirst_cpsr Hfirst_mask Hfirst_save Hcount_low Hcount_high)
    as [Hfirst [Hacquired [Hclear [Henabled [Hactive_entry [Hpointer_entry [Hcovered
      [old [Hwait [Hsource [Hcache Hafter]]]]]]]]]]].
  fold abi focus call entry in Hfirst, Hacquired, Henabled, Hactive_entry, Hpointer_entry, Hcovered,
    Hwait, Hsource, Hcache, Hafter.
  split; [exact Hfirst|]. split; [exact Hacquired|]. exists old.
  exact (task_create_foreign_wait_return_source environment critical arch save restore task_abi sg call
    first_final.(kernel_save_r0) entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old timeout tail
    original suspended saved original_entry call_before region args task_return lower old_frame upper
    old_sp cpsr values lr prefix suffix first old_words publication frame after
    Hwait Hsource Hcache Henabled Hlist Habsent Hcovered Horigin Hbinding Hcall Hslice Hsuspended_mask
    Hactive_entry Hpointer_entry Hparked Htimeout Hfragments Hregion Hgeometry Hsp_range Hpublication
    Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hafter).
Qed.
