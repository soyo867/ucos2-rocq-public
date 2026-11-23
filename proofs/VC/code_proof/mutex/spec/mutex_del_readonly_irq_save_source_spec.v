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
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_entry_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_proofs.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_repeated_irq_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_save_irq_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_readonly_error_source_spec.
Import UCOS2_C_Rules ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Section ReadonlyIRQSaveSource.
Context (environment : MutexDelCallEnvironment) (critical : CriticalRegionResources)
  (arch : A32InterruptContext) (sg : StableGlobVars) (Local : Type).
Variable save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
  environment.(mutex_del_call_platform) critical arch.
Variable restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
  environment.(mutex_del_call_platform) critical arch.
Variable registers_source : Armv7aIRQRegisterSave environment.(mutex_del_call_external)
  environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
  environment.(mutex_del_call_continuations).
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

(** Actual prefix -> MRS -> register-indexed IRQs at Save+4 -> restored
    CPSID/DSB/BX -> local store -> protected reads/error guard -> Restore.
    Save's acquired state is a separate endpoint, not equated with entry.
    The existing counter families are explicit on both calls; this is not
    a classifier or total contract for arbitrary configured executions. *)
Definition mutex_del_readonly_error_irq_save_execution
  restore_entry call state mask registers pe option perr cpu_sr code saved_word
  before entered acquired returned final after : Prop :=
  exists initialized prefix_heap returned_registers resumed final_registers final_state saved_heap body_heap
    middle restored returned_heap cursor written final_cursor group,
    kernel_heap_execution (pointer_store_writes cpu_sr 0) before initialized /\
    mutex_del_call_prefix_execution sg pe perr initialized None prefix_heap /\
    registers.(kernel_save_return_word) = None /\
    valid_os_cpu_sr registers.(kernel_save_cpsr) /\
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask /\
    mutex_del_irq_registers_execution environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
      environment.(mutex_del_call_continuations) registers_source sg Local local_step normal_return
      handler_stack handler_fragments (armv7a_save_entry_address save + 4)
      (kernel_save_read_cpsr registers) call state prefix_heap returned_registers entered acquired resumed /\
    armv7a_save_suffix_transition save returned_registers acquired resumed
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
      (restore_entry + 8) cursor.(kernel_restore_lr) entered acquired middle returned final restored /\
    armv7a_restore_suffix_transition restore written restored final_cursor returned_heap /\
    kernel_heap_execution [(perr, encode_os_err_code code)] returned_heap after.

(** The original nullable/free/public entry domain is retained. Public
    Type ownership at the acquired cut is derived here from the SAME
    source's proved EventState equality and current strong world. No
    acquired slot, current/ready, pool, or full-CPSR premise is added. *)
Lemma mutex_del_readonly_error_irq_save_post : forall restore_entry active call state mask registers
  pe eid observed option perr old_error cpu_sr code saved_word before entered acquired returned final after
  (frame : Assertion),
  mutex_del_parent_input sg pe state eid observed ->
  (kernel_stack_call_closed environment.(mutex_del_call_continuations)
     mutex_del_stack_resources sg active call mask state **
    (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) before ->
  mutex_del_readonly_error_irq_save_execution restore_entry call state mask registers pe option perr cpu_sr
    code saved_word before entered acquired returned final after ->
  saved_word = registers.(kernel_save_cpsr) /\
  kernel_stack_call_same_call entered call /\ kernel_stack_call_same_call returned call /\
  mutex_del_parent_critical_observation sg eid option pe (encode_os_err_code code) 0 acquired acquired /\
  mutex_del_readonly_error_irq_save_execution restore_entry call state mask registers pe option perr cpu_sr
    code saved_word before entered acquired returned final after /\
  (kernel_stack_call_closed environment.(mutex_del_call_continuations)
     mutex_del_stack_resources sg active returned mask final **
    (perr # UChar |-> encode_os_err_code code) ** (cpu_sr # UInt |-> saved_word) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) after.
Proof.
  intros restore_entry active call state mask registers pe eid observed option perr old_error cpu_sr code saved_word
    before entered acquired returned final after frame Hdomain Hpre Hsource.
  pose proof Hsource as Hexecution.
  destruct Hsource as (initialized & prefix_heap & returned_registers & resumed & final_registers & final_state &
    saved_heap & body_heap & middle & restored & returned_heap & cursor & written & final_cursor & group &
    Hinit & Hprefix & Hnone & Hvalid & Hmask & Hsave_irqs & Hsave_suffix & Hsaved & Hstore &
    Htype_read & Hgroup_read & Hguard & Hr0 & Hmasked & Hrestore_prefix & Hrestore_irqs &
    Hrestore_suffix & Herror).
  subst saved_word.
  set (abi := environment.(mutex_del_call_continuations)) in *.
  set (entry_residual := mutex_del_stack_critical_frame abi sg active state **
    task_stack_fragments_rep handler_stack handler_fragments ** frame).
  assert (Hinitialize_order : kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame |--
    (cpu_sr # UInt |->_) **
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) **
       (kernel_call_execution_owned environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) call mask ** entry_residual))).
  { unfold kernel_stack_call_closed, entry_residual.
    rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (task_stack_uint_store_execution cpu_sr 0 _ before ltac:(lia)
    (Hinitialize_order before Hpre)) as [produced [Hinitialize Hinitialized]].
  assert (produced = initialized) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced.
  assert (Hprefix_order : (cpu_sr # UInt |-> 0) **
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) **
       (kernel_call_execution_owned environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) call mask ** entry_residual)) |--
    kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) call mask ** (cpu_sr # UInt |->_) ** entry_residual)).
  { sep_apply_l_atomic (store_uint_undef_store_uint cpu_sr 0); entailer!. }
  destruct (mutex_del_call_prefix_resources sg state pe eid observed perr old_error initialized None prefix_heap _
    Hdomain (Hprefix_order initialized Hinitialized) Hprefix)
    as [[Hnonnull [Hentry_type Hnest]] Hprefix_owned].
  assert (Hsave_order : kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) call mask ** (cpu_sr # UInt |->_) ** entry_residual) |--
    kernel_stack_call_closed abi mutex_del_stack_resources sg active call
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** (perr # UChar |-> old_error) ** frame))).
  { unfold kernel_stack_call_closed, entry_residual; rewrite Hmask.
    rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (mutex_del_stack_irq_save_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi registers_source sg Local
    local_step normal_return handler_contract handler_stack handler_fragments critical arch save active call state
    registers prefix_heap returned_registers entered acquired resumed final_registers final_state saved_heap _
    Hnone Hvalid (Hsave_order prefix_heap Hprefix_owned) Hsave_irqs Hsave_suffix)
    as [Hmrs [Hsuffix_source [Hstate [Hsaved_value [Hfinal_cpsr [Hreturn [Hsame_entered [Hevents Hsaved_heap]]]]]]]].
  assert (Hstore_order : kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
      final_registers.(kernel_save_r0) acquired acquired **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** (perr # UChar |-> old_error) ** frame)) |--
    (cpu_sr # UInt |->_) **
      (kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
         final_registers.(kernel_save_r0) acquired acquired ** (perr # UChar |-> old_error) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)) by entailer!.
  destruct (task_stack_uint_store_execution cpu_sr final_registers.(kernel_save_r0) _ saved_heap
    ltac:(rewrite Hsaved_value; exact Hvalid) (Hstore_order saved_heap Hsaved_heap))
    as [produced [Hwrite Hbody_owned]].
  assert (produced = body_heap) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced.
  set (residual := mutex_del_stack_critical_frame abi sg active acquired **
    task_stack_fragments_rep handler_stack handler_fragments ** frame).
  assert (Hbody_order : (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
      (kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
         final_registers.(kernel_save_r0) acquired acquired ** (perr # UChar |-> old_error) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    coq_prop (UCOS2_state_inv sg acquired) &&
      (mutex_del_call_masked environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
         critical sg entered final_registers.(kernel_save_r0) acquired acquired **
       ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** residual))).
  { unfold kernel_stack_call_masked, mutex_del_call_masked, residual.
    rewrite mutex_del_stack_world_split_critical_frame; unfold kernel_program_inv; entailer!. }
  destruct (Hbody_order body_heap Hbody_owned) as [Hacquired_valid Hbody].
  destruct Hdomain as [Hzero|[_ [Haddress [Hid Hslot]]]]; [contradiction|].
  assert (Hacquired_slot : sem_query_public_slot acquired eid observed).
  { unfold sem_query_public_slot, mutex_query_lookup in *; rewrite Hevents; exact Hslot. }
  destruct (mutex_del_call_masked_type_load environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical sg entered final_registers.(kernel_save_r0)
    acquired acquired pe eid observed body_heap _ Haddress Hacquired_slot Hbody) as [Hactual_type Hborrowed].
  assert (Htype : event_slot_type_value acquired.(EventState) eid = 4)
    by (eapply uchar_load_deterministic; eassumption).
  destruct (mutex_del_parent_recheck_live_fields sg acquired eid observed Hacquired_valid Hacquired_slot Htype)
    as [mutex [Hlookup [Hkind Hfields]]].
  assert (Hbody_closed : (mutex_del_stack_restore_input abi critical sg active entered
      final_registers.(kernel_save_r0) acquired acquired **
    (task_stack_fragments_rep handler_stack handler_fragments **
      ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame))) body_heap).
  { match type of Hborrowed with ?P body_heap => match goal with |- ?Q body_heap =>
      assert (Hclose : P |-- Q) end end.
    { rewrite Haddress.
      sep_apply_l_atomic (mutex_del_parent_program_type_merge sg acquired eid Hacquired_valid).
      unfold mutex_del_stack_restore_input, residual.
      assert (Hcheckpoint : mutex_del_stack_checkpoint sg acquired acquired) by (left; reflexivity).
      entailer!. }
    exact (Hclose body_heap Hborrowed). }
  assert (Hprogram_order : mutex_del_stack_restore_input abi critical sg active entered
      final_registers.(kernel_save_r0) acquired acquired **
    (task_stack_fragments_rep handler_stack handler_fragments **
      ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame)) |--
    kernel_program_inv sg acquired **
      (critical_region_masked environment.(mutex_del_call_platform) critical sg
         entered.(os_sched_call_invocation) entered.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
       os_sched_context_resources environment.(mutex_del_call_external) entered **
       mutex_del_stack_critical_frame abi sg active acquired **
       task_stack_fragments_rep handler_stack handler_fragments **
       (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame)).
  { unfold mutex_del_stack_restore_input; entailer!. }
  pose proof (mutex_del_call_program_group_load sg acquired pe eid observed body_heap _ Haddress Hlookup
    (Hprogram_order body_heap Hbody_closed)) as Hgroup.
  assert (Hgroup_value : group = encode_event_wait_grp observed.(waitList) acquired.(TskState))
    by (eapply uchar_load_deterministic; eassumption).
  assert (Hobservation : mutex_del_parent_critical_observation sg eid option pe
      (encode_os_err_code code) 0 acquired acquired).
  { exists code, false; split; [|split; reflexivity].
    exists observed, mutex; split; [exact Hlookup|]. split; [exact Hkind|]. split; [exact Hfields|].
    destruct Hguard as [[Hoption [Hwaiting ->]]|[Hoption [Hother ->]]].
    - subst option; rewrite Hgroup_value in Hwaiting.
      destruct (Z.eq_dec 0 0); [|contradiction].
      destruct (Z.eq_dec (encode_event_wait_grp observed.(waitList) acquired.(TskState)) 0);
        [contradiction|rewrite Haddress; auto].
    - destruct (Z.eq_dec option 0); [contradiction|].
      destruct (Z.eq_dec option 1); [contradiction|rewrite Haddress; auto]. }
  destruct (mutex_del_stack_repeated_restore_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi sg Local local_step normal_return
    handler_contract handler_stack handler_fragments critical arch restore active entered
    final_registers.(kernel_save_r0) acquired acquired restore_entry cursor body_heap written middle
    returned final restored final_cursor returned_heap _ Hr0 Hmasked Hbody_closed
    Hrestore_prefix Hrestore_irqs Hrestore_suffix) as [Hi [Ho [Hs [Hrestore_return Hreturned]]]].
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
    Hcode_range (Hreturned_order returned_heap Hreturned)) as [finished [Hwrite_error Hfinished]].
  assert (finished = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst finished.
  split; [exact Hsaved_value|]. split; [exact Hsame_entered|].
  split.
  { destruct Hsame_entered as [Hi' [Ho' Hs']]; unfold kernel_stack_call_same_call; repeat split; congruence. }
  split; [exact Hobservation|]. split; [exact Hexecution|].
  match type of Hfinished with ?P after => match goal with |- ?Q after =>
    assert (Hfinish : P |-- Q) end end.
  { rewrite Hsaved_value; entailer!. }
  exact (Hfinish after Hfinished).
Qed.
End ReadonlyIRQSaveSource.
