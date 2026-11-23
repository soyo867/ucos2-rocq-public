Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_entry_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_proofs.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_repeated_irq_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Import UCOS2_C_Rules ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The two source branches that neither recycle the ECB nor schedule:
    NO_PEND with a nonempty group, and the default option.  These are C
    guards, not a restriction of Del's public input domain.  In this source
    revision the Count/PCP read is inside the mutating branches, so neither
    read-only error branch executes it. *)
Definition mutex_del_readonly_error_guard option group code : Prop :=
  (option = 0 /\ group <> 0 /\ code = OS_ERR_TASK_WAITING) \/
  (option <> 0 /\ option <> 1 /\ code = OS_ERR_INVALID_OPT).

(** A local source projection from the first C initializer to the final
    error store and pointer return.  The exact Save and Restore transitions
    below are the existing approved instruction/resource interfaces.  There
    is no intervening IRQ/client in THIS branch; that is an execution case,
    not a new platform law or a public no-interference precondition.

    All heap-changing operations are explicit: cpu_sr = 0, Save's returned
    word assignment, Restore's CPU/resource transitions and *perr = code.
    The protected Type/Grp reads and option branch are actual observations.
    The local tasks_waiting/pevent_return assignments are the guard/result
    values, not writes to kernel storage. *)
Definition mutex_del_readonly_error_execution environment critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  sg state mask registers pe option perr cpu_sr code saved_word before after : Prop :=
  exists initialized saved_heap body_heap middle returned_heap
    final_registers final_state cursor written final_cursor group,
    kernel_heap_execution (pointer_store_writes cpu_sr 0) before initialized /\
    mutex_del_call_prefix_execution sg pe perr initialized None initialized /\
    registers.(kernel_save_return_word) = None /\
    valid_os_cpu_sr registers.(kernel_save_cpsr) /\
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask /\
    armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state initialized
      final_registers final_state saved_heap /\
    saved_word = final_registers.(kernel_save_r0) /\
    kernel_heap_execution (pointer_store_writes cpu_sr saved_word) saved_heap body_heap /\
    uchar_load (pe + OSEventType_off) 4 body_heap /\
    uchar_load (pe + OSEventGrp_off) group body_heap /\
    mutex_del_readonly_error_guard option group code /\
    cursor.(kernel_restore_r0) = saved_word /\
    armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 /\
    armv7a_restore_prefix_transition restore cursor body_heap written middle /\
    armv7a_restore_suffix_transition restore written middle final_cursor returned_heap /\
    kernel_heap_execution [(perr, encode_os_err_code code)] returned_heap after.

Lemma mutex_del_call_program_group_load : forall sg state pe eid event heap (frame : Assertion),
  pe = event_addr sg eid -> mutex_query_lookup state eid event ->
  (kernel_program_inv sg state ** frame) heap ->
  uchar_load (pe + OSEventGrp_off)
    (encode_event_wait_grp event.(waitList) state.(TskState)) heap.
Proof.
  intros sg state pe eid event heap frame -> Hlookup Hpre.
  assert (Hsplit : kernel_program_inv sg state ** frame |--
    (event_pool_addr sg eid + 10) # UChar |->
      encode_event_wait_grp event.(waitList) state.(TskState) **
    (mutex_del_event_group_frame sg state eid event ** unmap_table_rep sg ** frame)).
  { unfold kernel_program_inv, kernel_program_rep; Intros_p Hvalid.
    sep_apply_l_atomic (mutex_del_raw_split_event sg state eid event Hlookup).
    pose proof (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) (event_image sg state.(TskState) event)
      EventGrpField ltac:(unfold event_fields; simpl; tauto)) as Hfield.
    cbn [event_cell event_image event_field_offset] in Hfield.
    sep_apply_l_atomic Hfield; unfold mutex_del_event_group_frame; entailer!. }
  change (uchar_load (event_pool_addr sg eid + 10)
    (encode_event_wait_grp event.(waitList) state.(TskState)) heap).
  eapply framed_uchar_store_load; exact (Hsplit heap Hpre).
Qed.

Section ReadonlyErrorRepeatedRestore.
Context (environment : MutexDelCallEnvironment) (critical : CriticalRegionResources)
  (arch : A32InterruptContext) (sg : StableGlobVars) (Local : Type).
Variable save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
  environment.(mutex_del_call_platform) critical arch.
Variable restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
  environment.(mutex_del_call_platform) critical arch.
Variable local_step : OsIntExitCallContext ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable normal_return : OsIntExitCallContext -> StableGlobVars ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable handler_contract : forall handler,
  RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) =>
      mutex_del_restore_handler_owner environment.(mutex_del_call_platform)
        environment.(mutex_del_call_port) handler)
    (local_step handler) (normal_return handler).
Variable handler_stack : TaskStackRegion.
Variable handler_fragments : TaskStackFragments.

(** The actual complete C error path now has one MSR, arbitrarily many
    supplied normally-returning counter IRQs, and one BX. Save is still
    the explicit uninterrupted branch. This is not a classification of
    all configured clients or an assertion that a call eventually returns.
    The pre/post OS states in each IRQ are retained by the old physical
    execution relation, including SP stores, park and final take.
    [restore_entry] is an explicit parameterized code address, not an
    existentially chosen PC or a linker binding supplied by the Restore
    ABI (which has no entry-address field). *)
Definition mutex_del_readonly_error_repeated_restore_execution
  restore_entry call state mask registers pe option perr cpu_sr code saved_word
  before returned final after : Prop :=
  exists initialized saved_heap body_heap middle resumed returned_heap
    final_registers final_state cursor written final_cursor group,
    kernel_heap_execution (pointer_store_writes cpu_sr 0) before initialized /\
    mutex_del_call_prefix_execution sg pe perr initialized None initialized /\
    registers.(kernel_save_return_word) = None /\
    valid_os_cpu_sr registers.(kernel_save_cpsr) /\
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask /\
    armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state initialized
      final_registers final_state saved_heap /\
    saved_word = final_registers.(kernel_save_r0) /\
    kernel_heap_execution (pointer_store_writes cpu_sr saved_word) saved_heap body_heap /\
    uchar_load (pe + OSEventType_off) 4 body_heap /\
    uchar_load (pe + OSEventGrp_off) group body_heap /\
    mutex_del_readonly_error_guard option group code /\
    cursor.(kernel_restore_r0) = saved_word /\
    armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 /\
    armv7a_restore_prefix_transition restore cursor body_heap written middle /\
    mutex_del_restore_irqs_execution environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
      environment.(mutex_del_call_continuations) sg Local local_step normal_return
      handler_stack handler_fragments (armv7a_irq_fiq_mask saved_word)
      (restore_entry + 8) cursor.(kernel_restore_lr) call state middle returned final resumed /\
    armv7a_restore_suffix_transition restore written resumed final_cursor returned_heap /\
    kernel_heap_execution [(perr, encode_os_err_code code)] returned_heap after.

(** Real consumer of the stronger repeated-IRQ producer. The public Type
    cell is borrowed and put back at the masked C cut; the private pool is
    the SAME pool split from the entry world. No extra pool or stack owner
    is added. The exact post keeps the final strong world and the original
    call identity, without claiming the old flat public history follows. *)
Lemma mutex_del_readonly_error_repeated_restore_post : forall restore_entry active call state mask registers
  pe eid observed option perr old_error cpu_sr code saved_word before returned final after
  (frame : Assertion),
  mutex_del_parent_input sg pe state eid observed ->
  (kernel_stack_call_closed environment.(mutex_del_call_continuations)
     mutex_del_stack_resources sg active call mask state **
    (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) before ->
  mutex_del_readonly_error_repeated_restore_execution restore_entry call state mask registers pe option perr
    cpu_sr code saved_word before returned final after ->
  kernel_stack_call_same_call returned call /\
  mutex_del_parent_critical_observation sg eid option pe (encode_os_err_code code) 0 state state /\
  mutex_del_readonly_error_repeated_restore_execution restore_entry call state mask registers pe option perr
    cpu_sr code saved_word before returned final after /\
  (kernel_stack_call_closed environment.(mutex_del_call_continuations)
     mutex_del_stack_resources sg active returned mask final **
    (perr # UChar |-> encode_os_err_code code) ** (cpu_sr # UInt |-> saved_word) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) after.
Proof.
  intros restore_entry active call state mask registers pe eid observed option perr old_error cpu_sr code saved_word
    before returned final after frame Hdomain Hpre Hsource.
  pose proof Hsource as Hexecution.
  destruct Hsource as (initialized & saved_heap & body_heap & middle & resumed & returned_heap &
    final_registers & final_state & cursor & written & final_cursor & group &
    Hinit & Hprefix & Hreturn & Hword & Hmask & Hsave & Hsaved & Hstore & Htype_read & Hgroup_read &
    Hguard & Hr0 & Hmasked & Hrestore_prefix & Hirqs & Hrestore_suffix & Herror).
  subst saved_word.
  set (abi := environment.(mutex_del_call_continuations)) in *.
  set (residual := mutex_del_stack_critical_frame abi sg active state **
    task_stack_fragments_rep handler_stack handler_fragments ** frame).
  assert (Hentry_open : kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame |--
    (cpu_sr # UInt |->_) **
      (mutex_del_call_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
        sg call mask state ** (perr # UChar |-> old_error) ** residual)).
  { unfold kernel_stack_call_closed, mutex_del_call_owned, residual.
    rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (task_stack_uint_store_execution cpu_sr 0 _ before ltac:(lia)
    (Hentry_open before Hpre)) as [produced [Hinitialize Hinitialized]].
  assert (produced = initialized) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced.
  assert (Hinitialized_order : (cpu_sr # UInt |-> 0) **
      (mutex_del_call_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
        sg call mask state ** (perr # UChar |-> old_error) ** residual) |--
    mutex_del_call_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      sg call mask state ** (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** residual).
  { sep_apply_l_atomic (store_uint_undef_store_uint cpu_sr 0); entailer!. }
  pose proof (Hinitialized_order initialized Hinitialized) as Hprefix_input.
  assert (Hprefix_order : mutex_del_call_owned environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** residual |--
    coq_prop (UCOS2_state_inv sg state) &&
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) **
        (kernel_call_execution_owned environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) call mask ** (cpu_sr # UInt |->_) ** residual))).
  { unfold mutex_del_call_owned, kernel_program_inv; entailer!. }
  destruct (Hprefix_order initialized Hprefix_input) as [Hvalid Hprefix_owned].
  destruct (mutex_del_call_prefix_resources sg state pe eid observed perr old_error
    initialized None initialized _ Hdomain Hprefix_owned Hprefix)
    as [[Hnonnull [Htype Hnest]] Hprefix_resources].
  destruct (mutex_del_call_prefix_save_body environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch save sg call state mask registers
    pe eid observed perr old_error cpu_sr initialized initialized saved_heap body_heap
    final_registers final_state _ Hdomain Hprefix_input Hprefix Hreturn Hword Hmask Hsave Hstore)
    as [Hstate [Hsave_return [Hread Hbody]]].
  destruct Hdomain as [Hzero|[_ [Haddress [Hid Hslot]]]]; [contradiction|].
  destruct (mutex_del_parent_recheck_live_fields sg state eid observed Hvalid Hslot Htype)
    as [mutex [Hlookup [Hkind Hfields]]].
  assert (Hbody_closed : (mutex_del_stack_restore_input abi critical sg active call
      final_registers.(kernel_save_r0) state state **
    (task_stack_fragments_rep handler_stack handler_fragments **
      ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame))) body_heap).
  { match type of Hbody with ?P body_heap => match goal with |- ?Q body_heap =>
      assert (Hclose : P |-- Q) end end.
    { rewrite Haddress, <- Htype.
      sep_apply_l_atomic (mutex_del_parent_program_type_merge sg state eid Hvalid).
      unfold mutex_del_stack_restore_input, mutex_del_call_masked, residual.
      assert (Hcheckpoint : mutex_del_stack_checkpoint sg state state) by (left; reflexivity).
      entailer!. }
    exact (Hclose body_heap Hbody). }
  assert (Hprogram_order : mutex_del_stack_restore_input abi critical sg active call
      final_registers.(kernel_save_r0) state state **
    (task_stack_fragments_rep handler_stack handler_fragments **
      ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame)) |--
    kernel_program_inv sg state **
      (critical_region_masked environment.(mutex_del_call_platform) critical sg
         call.(os_sched_call_invocation) call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
       os_sched_context_resources environment.(mutex_del_call_external) call **
       mutex_del_stack_critical_frame abi sg active state **
       task_stack_fragments_rep handler_stack handler_fragments **
       (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame)).
  { unfold mutex_del_stack_restore_input; entailer!. }
  pose proof (mutex_del_call_program_group_load sg state pe eid observed body_heap _ Haddress Hlookup
    (Hprogram_order body_heap Hbody_closed)) as Hgroup.
  assert (Hgroup_value : group = encode_event_wait_grp observed.(waitList) state.(TskState))
    by (eapply uchar_load_deterministic; eassumption).
  assert (Hobservation : mutex_del_parent_critical_observation sg eid option pe
      (encode_os_err_code code) 0 state state).
  { exists code, false; split; [|split; reflexivity].
    exists observed, mutex; split; [exact Hlookup|]. split; [exact Hkind|]. split; [exact Hfields|].
    destruct Hguard as [[Hoption [Hwaiting ->]]|[Hoption [Hother ->]]].
    - subst option; rewrite Hgroup_value in Hwaiting.
      destruct (Z.eq_dec 0 0); [|contradiction].
      destruct (Z.eq_dec (encode_event_wait_grp observed.(waitList) state.(TskState)) 0);
        [contradiction|rewrite Haddress; auto].
    - destruct (Z.eq_dec option 0); [contradiction|].
      destruct (Z.eq_dec option 1); [contradiction|rewrite Haddress; auto]. }
  assert (Hsave_source : kernel_call_save_uninterrupted_execution arch registers state initialized
      final_registers final_state saved_heap).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave). }
  destruct (kernel_call_save_uninterrupted_return_values _ _ _ _ _ _ _ Hsave_source) as [Hsaved_value _].
  destruct (mutex_del_stack_repeated_restore_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi sg Local local_step normal_return
    handler_contract handler_stack handler_fragments critical arch restore active call
    final_registers.(kernel_save_r0) state state restore_entry cursor body_heap written middle
    returned final resumed final_cursor returned_heap _ Hr0 Hmasked Hbody_closed
    Hrestore_prefix Hirqs Hrestore_suffix) as [Hi [Ho [Hs [Hrestore_return Hreturned]]]].
  rewrite Hsaved_value, Hmask in Hreturned.
  assert (Hreturned_order : kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
      (task_stack_fragments_rep handler_stack handler_fragments **
        ((cpu_sr # UInt |-> registers.(kernel_save_cpsr)) ** (perr # UChar |-> old_error) ** frame)) |--
    (perr # UChar |-> old_error) **
      (kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
       (cpu_sr # UInt |-> registers.(kernel_save_cpsr)) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)) by entailer!.
  assert (Hcode_range : 0 <= encode_os_err_code code < 256).
  { destruct Hguard as [[_ [_ ->]]|[_ [_ ->]]]; cbn [encode_os_err_code]; lia. }
  destruct (kernel_heap_framed_uchar_store perr old_error (encode_os_err_code code) _ returned_heap
    Hcode_range (Hreturned_order returned_heap Hreturned)) as [finished [Hwrite Hfinished]].
  assert (finished = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst finished.
  split; [unfold kernel_stack_call_same_call; auto|]. split; [exact Hobservation|].
  split; [exact Hexecution|].
  match type of Hfinished with ?P after => match goal with |- ?Q after =>
    assert (Hfinish : P |-- Q) end end.
  { rewrite Hsaved_value; entailer!. }
  exact (Hfinish after Hfinished).
Qed.
End ReadonlyErrorRepeatedRestore.

(** This is only a consequence of a SOURCE-ESTABLISHED Restore post.
    It is deliberately not a consequence of the legacy dynamic-only C
    Ensure appearing in the fourteen open canonical obligations. *)
Lemma mutex_del_interface_restore_unscheduled : forall environment critical sg call mask state,
  mutex_del_interface_restore_post environment critical sg call mask state |--
  mutex_del_callsite_unscheduled_post environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical sg call mask state.
Proof.
  intros; unfold mutex_del_interface_restore_post; Intros returned current.
  unfold mutex_del_callsite_unscheduled_post, mutex_del_callsite_restore_return.
  Exists returned current KernelClientHeapClosed environment.
  rewrite mutex_del_interface_closed_owned.
  unfold mutex_del_callsite_cut, mutex_del_interface_world,
    mutex_del_callsite_environment; cbn [kernel_client_heap_resources]; entailer!.
Qed.

(** Complete source consumer, not another detached call-interface helper:
    the same execution supplies the source guards, both CPU calls, the
    caller-local stores, and the existing exact public Del postcondition.
    The caller's whole continuation map and the one UnMapTbl owner are
    transported through both actual calls.  They are never recreated from
    a weak post or framed across an arbitrary interruptible Restore. *)
Lemma mutex_del_readonly_error_source_post : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  sg call state mask registers pe eid observed option perr old_error cpu_sr code saved_word
  before after (frame : Assertion),
  mutex_del_parent_input sg pe state eid observed ->
  (mutex_del_interface_closed environment critical sg call mask state **
    (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame) before ->
  mutex_del_readonly_error_execution environment critical arch save restore sg state mask
    registers pe option perr cpu_sr code saved_word before after ->
  (mutex_del_parent_post environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) critical sg call mask state pe option eid
      pe (encode_os_err_code code) **
    (perr # UChar |-> encode_os_err_code code) ** (cpu_sr # UInt |-> saved_word) ** frame) after.
Proof.
  intros environment critical arch save restore sg call state mask registers pe eid observed option
    perr old_error cpu_sr code saved_word before after frame Hdomain Hpre Hsource.
  destruct Hsource as [initialized [saved_heap [body_heap [middle [returned_heap
    [final_registers [final_state [cursor [written [final_cursor [group
    [Hinit [Hprefix [Hreturn [Hword [Hmask [Hsave [Hsaved [Hstore
    [Htype_read [Hgroup_read [Hguard [Hr0 [Hmasked [Hrestore_prefix [Hrestore_suffix Herror]]]]]]]]]]]]]]]]]]]]]]]]]].
  subst saved_word.
  assert (Hentry_open : mutex_del_interface_closed environment critical sg call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame |--
    (cpu_sr # UInt |->_) **
    (mutex_del_call_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      sg call mask state ** (perr # UChar |-> old_error) **
      (mutex_del_interface_capsules environment state ** frame))).
  { rewrite mutex_del_interface_closed_owned.
    unfold mutex_del_interface_world, kernel_client_heap_world, mutex_del_interface_capsules,
      mutex_del_call_owned; entailer!. }
  destruct (task_stack_uint_store_execution cpu_sr 0 _ before ltac:(lia)
    (Hentry_open before Hpre)) as [produced [Hinitialize Hinitialized]].
  assert (produced = initialized) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced.
  assert (Hinitialized_order : (cpu_sr # UInt |-> 0) **
      (mutex_del_call_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
        sg call mask state ** (perr # UChar |-> old_error) **
        (mutex_del_interface_capsules environment state ** frame)) |--
    mutex_del_call_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      sg call mask state ** (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      (mutex_del_interface_capsules environment state ** frame)).
  { sep_apply_l_atomic (store_uint_undef_store_uint cpu_sr 0); entailer!. }
  pose proof (Hinitialized_order initialized Hinitialized) as Hprefix_input.
  assert (Hprefix_order : mutex_del_call_owned environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      (mutex_del_interface_capsules environment state ** frame) |--
    coq_prop (UCOS2_state_inv sg state) &&
    (kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) call mask ** (cpu_sr # UInt |->_) **
        mutex_del_interface_capsules environment state ** frame))).
  { unfold mutex_del_call_owned, kernel_program_inv; entailer!. }
  destruct (Hprefix_order initialized Hprefix_input) as [Hvalid Hprefix_owned].
  destruct (mutex_del_call_prefix_resources sg state pe eid observed perr old_error
    initialized None initialized _ Hdomain Hprefix_owned Hprefix)
    as [[Hnonnull [Htype Hnest]] Hprefix_resources].
  destruct (mutex_del_call_prefix_save_body environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch save sg call state mask registers
    pe eid observed perr old_error cpu_sr initialized initialized saved_heap body_heap
    final_registers final_state _ Hdomain Hprefix_input Hprefix Hreturn Hword Hmask Hsave Hstore)
    as [Hstate [Hsave_return [Hread Hbody]]].
  destruct Hdomain as [Hzero|[_ [Haddress [Hid Hslot]]]]; [contradiction|].
  destruct (mutex_del_parent_recheck_live_fields sg state eid observed Hvalid Hslot Htype)
    as [mutex [Hlookup [Hkind Hfields]]].
  assert (Hbody_closed :
    (mutex_del_interface_restore_pre environment critical sg call final_registers.(kernel_save_r0)
      state state ** ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
        (perr # UChar |-> old_error) ** frame)) body_heap).
  { match type of Hbody with ?P body_heap => assert (Hclose : P |--
      mutex_del_interface_restore_pre environment critical sg call final_registers.(kernel_save_r0)
        state state ** ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
          (perr # UChar |-> old_error) ** frame)) end.
    { rewrite Haddress, <- Htype.
      sep_apply_l_atomic (mutex_del_parent_program_type_merge sg state eid Hvalid).
      unfold mutex_del_interface_restore_pre, mutex_del_interface_context,
        mutex_del_interface_world, kernel_client_heap_world, mutex_del_interface_capsules; entailer!. }
    exact (Hclose body_heap Hbody). }
  assert (Hprogram_order : mutex_del_interface_restore_pre environment critical sg call
      final_registers.(kernel_save_r0) state state **
      ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame) |--
    kernel_program_inv sg state **
      (critical_region_masked environment.(mutex_del_call_platform) critical sg
         call.(os_sched_call_invocation) call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
       mutex_del_interface_context environment call ** mutex_del_interface_capsules environment state **
       (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame)).
  { unfold mutex_del_interface_restore_pre, mutex_del_interface_world,
      kernel_client_heap_world, mutex_del_interface_capsules; entailer!. }
  pose proof (mutex_del_call_program_group_load sg state pe eid observed body_heap _ Haddress Hlookup
    (Hprogram_order body_heap Hbody_closed)) as Hgroup.
  assert (Hgroup_value : group = encode_event_wait_grp observed.(waitList) state.(TskState))
    by (eapply uchar_load_deterministic; eassumption).
  assert (Hobservation : mutex_del_parent_critical_observation sg eid option pe
      (encode_os_err_code code) 0 state state).
  { exists code, false; split; [|split; reflexivity].
    exists observed, mutex; split; [exact Hlookup|]. split; [exact Hkind|]. split; [exact Hfields|].
    destruct Hguard as [[Hoption [Hwaiting ->]]|[Hoption [Hother ->]]].
    - subst option; rewrite Hgroup_value in Hwaiting.
      destruct (Z.eq_dec 0 0); [|contradiction].
      destruct (Z.eq_dec (encode_event_wait_grp observed.(waitList) state.(TskState)) 0);
        [contradiction|rewrite Haddress; auto].
    - destruct (Z.eq_dec option 0); [contradiction|].
      destruct (Z.eq_dec option 1); [contradiction|rewrite Haddress; auto]. }
  assert (Hsave_source : kernel_call_save_uninterrupted_execution arch registers state initialized
      final_registers final_state saved_heap).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave). }
  destruct (kernel_call_save_uninterrupted_return_values _ _ _ _ _ _ _ Hsave_source) as [Hsaved_value _].
  destruct (mutex_del_interface_uninterrupted_restore environment critical arch restore sg call
    final_registers.(kernel_save_r0) state state cursor body_heap written middle final_cursor
    returned_heap _ Hr0 Hmasked Hbody_closed Hrestore_prefix Hrestore_suffix)
    as [Hrestore_source [Hrestore_return Hreturned]].
  rewrite Hsaved_value, Hmask in Hreturned.
  assert (Hreturned_order : mutex_del_interface_restore_post environment critical sg call mask state **
      ((cpu_sr # UInt |-> registers.(kernel_save_cpsr)) ** (perr # UChar |-> old_error) ** frame) |--
    (perr # UChar |-> old_error) **
      (mutex_del_interface_restore_post environment critical sg call mask state **
       (cpu_sr # UInt |-> registers.(kernel_save_cpsr)) ** frame)) by entailer!.
  assert (Hcode_range : 0 <= encode_os_err_code code < 256).
  { destruct Hguard as [[_ [_ ->]]|[_ [_ ->]]]; cbn [encode_os_err_code]; lia. }
  destruct (kernel_heap_framed_uchar_store perr old_error (encode_os_err_code code) _ returned_heap
    Hcode_range (Hreturned_order returned_heap Hreturned)) as [finished [Hwrite Hfinished]].
  assert (finished = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst finished.
  assert (Hprefix_ok : mutex_del_parent_prefix_ok pe state eid).
  { unfold mutex_del_parent_prefix_ok; apply mutex_del_before_save_continues_iff;
      [rewrite Hnest; lia|auto]. }
  assert (Hpost : mutex_del_interface_restore_post environment critical sg call mask state |--
    mutex_del_parent_post environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      critical sg call mask state pe option eid pe (encode_os_err_code code)).
  { eapply derivable1_trans; [apply mutex_del_interface_restore_unscheduled|].
    unfold mutex_del_parent_post, mutex_del_parent_original_post.
    Left; Right; Exists state state 0; Left.
    unfold mutex_del_parent_unscheduled_post; entailer!.
    unfold critical_region_interval; constructor. }
  match type of Hfinished with ?P after => match goal with |- ?Q after =>
    assert (Hfinish : P |-- Q) end end.
  { rewrite Hsaved_value; sep_apply_l_atomic Hpost; entailer!. }
  exact (Hfinish after Hfinished).
Qed.
