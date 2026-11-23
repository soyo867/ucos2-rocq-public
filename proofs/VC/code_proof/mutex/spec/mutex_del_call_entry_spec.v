Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_program_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Import UCOS2_C_Rules ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The owned entry cut is NOT the old public Require and is not supplied
    by a ghost [context]. Its CPU/context pair must come from a real entry
    or return producer; its program owner contains OSUnMapTbl exactly once.
    The physical prefix below is deliberately polymorphic in the private
    frame, so the NULL/type/ISR errors do not require a task-only caller. *)
Definition mutex_del_call_owned external platform sg call mask state : Assertion :=
  kernel_call_execution_owned external platform call mask ** kernel_program_inv sg state.

Definition mutex_del_call_masked external platform critical sg call saved entry checkpoint : Assertion :=
  critical_region_masked platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved entry **
  os_sched_context_resources external call ** kernel_program_inv sg checkpoint.

(** Source/parameter cut of the approved Del projection. This is exactly
    its existing nullable public ECB-slot domain, including recycled ECBs;
    it adds neither generation equality nor caller/current/ready facts. *)
Definition mutex_del_call_pointer_domain sg state pe eid observed : Prop :=
  pe = 0 \/ (pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
    sem_query_public_slot state eid observed).

(** The selected C guard prefix, after the local cpu_sr initializer and
    before OS_ENTER_CRITICAL. Each constructor
    keeps the source short-circuit order. The three error branches execute
    the actual byte store to perr; Continue executes no store. This is a
    local, uninterrupted C fragment, NOT a model of arbitrary IRQs between
    its reads or a restriction on Del's public environment. *)
Inductive mutex_del_call_prefix_execution (sg : StableGlobVars) (pe perr : Z)
  : model -> option OSErrCode -> model -> Prop :=
| MutexDelCallPrefixNull : forall before after,
    pe = 0 -> kernel_heap_execution [(perr, 4)] before after ->
    mutex_del_call_prefix_execution sg pe perr before (Some OS_ERR_PEVENT_NULL) after
| MutexDelCallPrefixType : forall before observed_type after,
    pe <> 0 -> uchar_load (pe + OSEventType_off) observed_type before -> observed_type <> 4 ->
    kernel_heap_execution [(perr, 1)] before after ->
    mutex_del_call_prefix_execution sg pe perr before (Some OS_ERR_EVENT_TYPE) after
| MutexDelCallPrefixISR : forall before nesting after,
    pe <> 0 -> uchar_load (pe + OSEventType_off) 4 before ->
    uchar_load sg.(g_OSIntNesting) nesting before -> 0 < nesting ->
    kernel_heap_execution [(perr, 15)] before after ->
    mutex_del_call_prefix_execution sg pe perr before (Some OS_ERR_DEL_ISR) after
| MutexDelCallPrefixContinue : forall heap,
    pe <> 0 -> uchar_load (pe + OSEventType_off) 4 heap ->
    uchar_load sg.(g_OSIntNesting) 0 heap ->
    mutex_del_call_prefix_execution sg pe perr heap None heap.

Definition mutex_del_call_prefix_post sg state pe eid perr old_error result (frame : Assertion) : Assertion :=
  match result with
  | Some code => kernel_program_inv sg state ** (perr # UChar |-> encode_os_err_code code) ** frame
  | None => coq_prop (pe <> 0 /\ event_slot_type_value state.(EventState) eid = 4 /\
      state.(IntrState).(intNesting) = 0) &&
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) ** frame)
  end.

Lemma mutex_del_call_program_type_load : forall sg state pe eid observed heap (frame : Assertion),
  pe = event_addr sg eid -> sem_query_public_slot state eid observed ->
  (kernel_program_inv sg state ** frame) heap ->
  uchar_load (pe + OSEventType_off) (event_slot_type_value state.(EventState) eid) heap.
Proof.
  intros sg state pe eid observed heap frame -> Hslot Hpre.
  assert (Hsplit : kernel_program_inv sg state ** frame |--
    (event_addr sg eid + OSEventType_off) # UChar |-> event_slot_type_value state.(EventState) eid **
    (sem_query_type_frame sg state eid ** unmap_table_rep sg ** frame)).
  { rewrite kernel_program_inv_split_unmap.
    sep_apply_l_atomic (sem_query_type_split_full sg state eid observed Hslot); entailer!. }
  eapply framed_uchar_store_load; exact (Hsplit heap Hpre).
Qed.

Lemma mutex_del_call_program_nesting_load : forall sg state heap (frame : Assertion),
  (kernel_program_inv sg state ** frame) heap ->
  uchar_load sg.(g_OSIntNesting) state.(IntrState).(intNesting) heap.
Proof.
  intros sg state heap frame Hpre.
  assert (Hsplit : kernel_program_inv sg state ** frame |--
    sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
    (interrupt_inv_no_int_nesting sg state.(IntrState) ** mutex_query_whole_frame sg state **
     unmap_table_rep sg ** frame)).
  { rewrite kernel_program_inv_split_unmap.
    sep_apply_l_atomic (mutex_query_interrupt_split_full sg state); entailer!. }
  eapply framed_uchar_store_load; exact (Hsplit heap Hpre).
Qed.

Lemma mutex_del_call_error_store_resources : forall sg state perr old_error code before after (frame : Assertion),
  0 <= code < 256 ->
  (kernel_program_inv sg state ** (perr # UChar |-> old_error) ** frame) before ->
  kernel_heap_execution [(perr, code)] before after ->
  (kernel_program_inv sg state ** (perr # UChar |-> code) ** frame) after.
Proof.
  intros sg state perr old_error code before after frame Hrange Hpre Hrun.
  assert (Hopen : kernel_program_inv sg state ** (perr # UChar |-> old_error) ** frame |--
    (perr # UChar |-> old_error) ** (kernel_program_inv sg state ** frame)) by entailer!.
  destruct (kernel_heap_framed_uchar_store perr old_error code _ before Hrange (Hopen before Hpre))
    as [produced [Hstore Hpost]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced.
  assert (Hclose : (perr # UChar |-> code) ** (kernel_program_inv sg state ** frame) |--
    kernel_program_inv sg state ** (perr # UChar |-> code) ** frame) by entailer!.
  exact (Hclose after Hpost).
Qed.

(** The supplied execution's actual reads determine the continuation
    facts. No pre-Save type observation is carried across an interrupt. *)
Lemma mutex_del_call_prefix_resources : forall sg state pe eid observed perr old_error
  before result after (frame : Assertion),
  mutex_del_call_pointer_domain sg state pe eid observed ->
  (kernel_program_inv sg state ** (perr # UChar |-> old_error) ** frame) before ->
  mutex_del_call_prefix_execution sg pe perr before result after ->
  mutex_del_call_prefix_post sg state pe eid perr old_error result frame after.
Proof.
  intros sg state pe eid observed perr old_error before result after frame Hdomain Hpre Hrun.
  destruct Hrun; cbn [mutex_del_call_prefix_post encode_os_err_code].
  - eapply mutex_del_call_error_store_resources; eauto; lia.
  - eapply mutex_del_call_error_store_resources; eauto; lia.
  - eapply mutex_del_call_error_store_resources; eauto; lia.
  - destruct Hdomain as [Hzero|[_ [Haddress [_ Hslot]]]]; [contradiction|].
    assert (Horder : kernel_program_inv sg state ** (perr # UChar |-> old_error) ** frame |--
      kernel_program_inv sg state ** ((perr # UChar |-> old_error) ** frame)) by entailer!.
    pose proof (mutex_del_call_program_type_load sg state pe eid observed heap _ Haddress Hslot
      (Horder heap Hpre)) as Htype.
    pose proof (mutex_del_call_program_nesting_load sg state heap _ (Horder heap Hpre)) as Hnesting.
    assert (event_slot_type_value state.(EventState) eid = 4)
      by (eapply uchar_load_deterministic; eassumption).
    assert (state.(IntrState).(intNesting) = 0)
      by (eapply uchar_load_deterministic; eassumption).
    split; [repeat split; assumption|exact Hpre].
Qed.

(** Existence uses actual owned bytes and the original guards, including
    all three errors. It supplies one local source branch, not termination
    of an interruptible public call. Caller/handler/stack resources can
    all be supplied in [frame] and are preserved by the real perr store. *)
Lemma mutex_del_call_prefix_source : forall sg state pe eid observed perr old_error before (frame : Assertion),
  mutex_del_call_pointer_domain sg state pe eid observed ->
  (kernel_program_inv sg state ** (perr # UChar |-> old_error) ** frame) before ->
  exists result after,
    mutex_del_call_prefix_execution sg pe perr before result after /\
    mutex_del_call_prefix_post sg state pe eid perr old_error result frame after.
Proof.
  intros sg state pe eid observed perr old_error before frame Hdomain Hpre.
  assert (Hstore : forall code, 0 <= code < 256 ->
    exists after, kernel_heap_execution [(perr, code)] before after).
  { intros code Hrange.
    assert (Horder : kernel_program_inv sg state ** (perr # UChar |-> old_error) ** frame |--
      (perr # UChar |-> old_error) ** (kernel_program_inv sg state ** frame)) by entailer!.
    destruct (kernel_heap_framed_uchar_store perr old_error code _ before Hrange (Horder before Hpre))
      as [after [Hrun Hpost]]; eauto. }
  assert (Hrun : exists result after, mutex_del_call_prefix_execution sg pe perr before result after).
  { destruct Hdomain as [Hzero|[Hnonzero [Haddress [_ Hslot]]]].
    - destruct (Hstore 4 ltac:(lia)) as [after Hwrite].
      exists (Some OS_ERR_PEVENT_NULL), after; econstructor; eassumption.
    - assert (Horder : kernel_program_inv sg state ** (perr # UChar |-> old_error) ** frame |--
        kernel_program_inv sg state ** ((perr # UChar |-> old_error) ** frame)) by entailer!.
      pose proof (mutex_del_call_program_type_load sg state pe eid observed before _ Haddress Hslot
        (Horder before Hpre)) as Htype.
      destruct (Z.eq_dec (event_slot_type_value state.(EventState) eid) 4) as [Hmutex|Hother].
      + rewrite Hmutex in Htype.
        pose proof (mutex_del_call_program_nesting_load sg state before _ (Horder before Hpre)) as Hnest.
        destruct (Z_lt_dec 0 state.(IntrState).(intNesting)) as [Hpositive|Hzero].
        * destruct (Hstore 15 ltac:(lia)) as [after Hwrite].
          exists (Some OS_ERR_DEL_ISR), after; econstructor; eassumption.
        * assert (state.(IntrState).(intNesting) = 0) as Hzero'.
          { destruct Hnest as [Hrange _]; lia. }
          rewrite Hzero' in Hnest; exists None, before; constructor; assumption.
      + destruct (Hstore 1 ltac:(lia)) as [after Hwrite].
        exists (Some OS_ERR_EVENT_TYPE), after; econstructor; eassumption. }
  destruct Hrun as [result [after Hrun]].
  exists result, after; split; [exact Hrun|].
  eapply mutex_del_call_prefix_resources; eassumption.
Qed.

(** Save's actual local MRS and supplied CPSID/DSB/BX suffix consume a
    real caller owner. Context and the single program world are returned
    together, not added to a header Ensure. No task/current/ready premise
    is needed by this local branch. Interrupted branches remain separate. *)
Lemma mutex_del_call_uninterrupted_save : forall external platform critical arch
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  sg call state mask registers before final_registers final_state after (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (mutex_del_call_owned external platform sg call mask state ** frame) before ->
  armv7a_save_suffix_transition suffix (kernel_save_read_cpsr registers) state before
    final_registers final_state after ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers final_state after /\
  final_state = state /\ final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  (mutex_del_call_masked external platform critical sg call final_registers.(kernel_save_r0)
    state state ** frame) after.
Proof.
  intros external platform critical arch suffix sg call state mask registers before final_registers final_state after
    frame Hreturn Hvalid Hmask Hpre Hsuffix.
  assert (Hsource : kernel_call_save_uninterrupted_execution arch registers state before
    final_registers final_state after).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hsuffix). }
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hvalid|reflexivity]).
  assert (Hopen : mutex_del_call_owned external platform sg call mask state ** frame |--
    kernel_call_execution_owned external platform call
      (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
    (kernel_program_inv sg state ** frame)).
  { change (mutex_del_call_owned external platform sg call mask state ** frame |--
      kernel_call_execution_owned external platform call (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
        (kernel_program_inv sg state ** frame)).
    rewrite Hmask; unfold mutex_del_call_owned; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix sg call
    (kernel_save_read_cpsr registers) state before final_registers final_state after _ Hsaved
    (Hopen before Hpre) Hsuffix) as [Hstate [Hmemory [Hlr [Hvalue Hpost]]]].
  split; [exact Hsource|]. split; [exact Hstate|]. split; [exact Hlr|].
  assert (Hclose : critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) final_registers.(kernel_save_r0) state ** os_sched_context_resources external call **
      (kernel_program_inv sg state ** frame) |--
    mutex_del_call_masked external platform critical sg call final_registers.(kernel_save_r0) state state ** frame).
  { unfold mutex_del_call_masked; entailer!. }
  exact (Hclose after Hpost).
Qed.

(** The C assignment cpu_sr = OS_CPU_SR_Save() writes one real borrowed
    UInt cell. That cell must be disjoint from the context's stack fragments
    and all other owners. Its address alone is not an allocation proof. *)
Lemma mutex_del_call_saved_return_store : forall external platform critical sg call saved entry checkpoint
  cpu_sr before after (frame : Assertion),
  valid_os_cpu_sr saved ->
  (mutex_del_call_masked external platform critical sg call saved entry checkpoint **
    (cpu_sr # UInt |->_) ** frame) before ->
  kernel_heap_execution (pointer_store_writes cpu_sr saved) before after ->
  (mutex_del_call_masked external platform critical sg call saved entry checkpoint **
    (cpu_sr # UInt |-> saved) ** frame) after.
Proof.
  intros external platform critical sg call saved entry checkpoint cpu_sr before after frame Hsaved Hpre Hrun.
  assert (Hopen : mutex_del_call_masked external platform critical sg call saved entry checkpoint **
      (cpu_sr # UInt |->_) ** frame |--
    (cpu_sr # UInt |->_) ** (mutex_del_call_masked external platform critical sg call saved entry checkpoint ** frame))
    by entailer!.
  destruct (task_stack_uint_store_execution cpu_sr saved _ before Hsaved (Hopen before Hpre))
    as [produced [Hstore Hpost]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hclose : (cpu_sr # UInt |-> saved) **
      (mutex_del_call_masked external platform critical sg call saved entry checkpoint ** frame) |--
    mutex_del_call_masked external platform critical sg call saved entry checkpoint **
      (cpu_sr # UInt |-> saved) ** frame) by entailer!.
  exact (Hclose after Hpost).
Qed.


(** This is the actual protected C read and residual used at Del's body
    entry. The public-slot premise is intentionally explicit: transporting
    context/table through Save does NOT establish the independent lifetime
    obligation _6. In particular [observed] may be a newly reused object. *)
Lemma mutex_del_call_masked_type_load : forall external platform critical sg call saved entry checkpoint
  pe eid observed heap (frame : Assertion),
  pe = event_addr sg eid -> sem_query_public_slot checkpoint eid observed ->
  (mutex_del_call_masked external platform critical sg call saved entry checkpoint ** frame) heap ->
  uchar_load (pe + OSEventType_off) (event_slot_type_value checkpoint.(EventState) eid) heap /\
  ((pe + OSEventType_off) # UChar |-> event_slot_type_value checkpoint.(EventState) eid **
    sem_query_type_frame sg checkpoint eid ** unmap_table_rep sg **
    critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved entry ** os_sched_context_resources external call ** frame) heap.
Proof.
  intros external platform critical sg call saved entry checkpoint pe eid observed heap frame -> Hslot Hpre.
  assert (Hsplit : mutex_del_call_masked external platform critical sg call saved entry checkpoint ** frame |--
    (event_addr sg eid + OSEventType_off) # UChar |-> event_slot_type_value checkpoint.(EventState) eid **
    sem_query_type_frame sg checkpoint eid ** unmap_table_rep sg **
    critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved entry ** os_sched_context_resources external call ** frame).
  { unfold mutex_del_call_masked; rewrite kernel_program_inv_split_unmap.
    sep_apply_l_atomic (sem_query_type_split_full sg checkpoint eid observed Hslot); entailer!. }
  pose proof (Hsplit heap Hpre) as Howned; split; [|exact Howned].
  eapply framed_uchar_store_load.
  assert (Horder : (event_addr sg eid + OSEventType_off) # UChar |->
      event_slot_type_value checkpoint.(EventState) eid ** sem_query_type_frame sg checkpoint eid **
      unmap_table_rep sg ** critical_region_masked platform critical sg call.(os_sched_call_invocation)
        call.(os_sched_call_origin) saved entry ** os_sched_context_resources external call ** frame |--
    (event_addr sg eid + OSEventType_off) # UChar |-> event_slot_type_value checkpoint.(EventState) eid **
      (sem_query_type_frame sg checkpoint eid ** unmap_table_rep sg **
       critical_region_masked platform critical sg call.(os_sched_call_invocation)
         call.(os_sched_call_origin) saved entry ** os_sched_context_resources external call ** frame)) by entailer!.
  exact (Horder heap Howned).
Qed.

(** Method-3's real local declaration initializes cpu_sr before even the
    NULL branch. Consume the supplied automatic-local cell, execute its
    four-byte store, then execute the actual short-circuit guard prefix.
    Allocating/borrowing this cell is a separate caller/stack partition
    operation; this theorem never obtains it from an address or a token. *)
Lemma mutex_del_call_entry_prefix_source : forall sg state pe eid observed perr old_error cpu_sr before
  (frame : Assertion),
  mutex_del_call_pointer_domain sg state pe eid observed ->
  (kernel_program_inv sg state ** (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame) before ->
  exists initialized result after,
    kernel_heap_execution (pointer_store_writes cpu_sr 0) before initialized /\
    mutex_del_call_prefix_execution sg pe perr initialized result after /\
    mutex_del_call_prefix_post sg state pe eid perr old_error result ((cpu_sr # UInt |-> 0) ** frame) after.
Proof.
  intros sg state pe eid observed perr old_error cpu_sr before frame Hdomain Hpre.
  assert (Hopen : kernel_program_inv sg state ** (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame |--
    (cpu_sr # UInt |->_) ** (kernel_program_inv sg state ** (perr # UChar |-> old_error) ** frame)) by entailer!.
  destruct (task_stack_uint_store_execution cpu_sr 0 _ before ltac:(unfold valid_os_cpu_sr; lia) (Hopen before Hpre))
    as [initialized [Hstore Hinitialized]].
  assert (Horder : (cpu_sr # UInt |-> 0) ** (kernel_program_inv sg state ** (perr # UChar |-> old_error) ** frame) |--
    kernel_program_inv sg state ** (perr # UChar |-> old_error) ** ((cpu_sr # UInt |-> 0) ** frame)) by entailer!.
  destruct (mutex_del_call_prefix_source sg state pe eid observed perr old_error initialized _ Hdomain
    (Horder initialized Hinitialized)) as [result [after [Hprefix Hpost]]].
  exists initialized, result, after; split; [exact Hstore|]. split; assumption.
Qed.

(** Complete local prefix -> MRS/CPSID/DSB/BX -> cpu_sr assignment ->
    protected type read, all on successive actual heaps. This is usable
    after ANY real owned caller return, not only initial task registration.
    Only this branch is uninterrupted; no old public input is removed. *)
Lemma mutex_del_call_prefix_save_body : forall external platform critical arch
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  sg call state mask registers pe eid observed perr old_error cpu_sr before prefix_heap saved_heap body_heap
  final_registers final_state (frame : Assertion),
  mutex_del_call_pointer_domain sg state pe eid observed ->
  (mutex_del_call_owned external platform sg call mask state **
    (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame) before ->
  mutex_del_call_prefix_execution sg pe perr before None prefix_heap ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition suffix (kernel_save_read_cpsr registers) state prefix_heap
    final_registers final_state saved_heap ->
  kernel_heap_execution (pointer_store_writes cpu_sr final_registers.(kernel_save_r0)) saved_heap body_heap ->
  final_state = state /\ final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  uchar_load (pe + OSEventType_off) 4 body_heap /\
  ((pe + OSEventType_off) # UChar |-> 4 ** sem_query_type_frame sg state eid ** unmap_table_rep sg **
    critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
    os_sched_context_resources external call **
    ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame)) body_heap.
Proof.
  intros external platform critical arch suffix sg call state mask registers pe eid observed perr old_error cpu_sr
    before prefix_heap saved_heap body_heap final_registers final_state frame Hdomain Hpre Hprefix
    Hreturn Hvalid Hmask Hsuffix Hstore.
  assert (Hopen : mutex_del_call_owned external platform sg call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame |--
    kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned external platform call mask ** (cpu_sr # UInt |->_) ** frame)).
  { unfold mutex_del_call_owned; entailer!. }
  destruct (mutex_del_call_prefix_resources sg state pe eid observed perr old_error before None prefix_heap _
    Hdomain (Hopen before Hpre) Hprefix) as [[Hnonnull [Htype Hnest]] Hprefix_owned].
  assert (Hsave_order : kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned external platform call mask ** (cpu_sr # UInt |->_) ** frame) |--
    mutex_del_call_owned external platform sg call mask state **
      ((cpu_sr # UInt |->_) ** (perr # UChar |-> old_error) ** frame)).
  { unfold mutex_del_call_owned; entailer!. }
  destruct (mutex_del_call_uninterrupted_save external platform critical arch suffix sg call state mask registers
    prefix_heap final_registers final_state saved_heap _ Hreturn Hvalid Hmask
    (Hsave_order prefix_heap Hprefix_owned) Hsuffix) as [Hrun [Hstate [Hlr Hsaved]]].
  destruct (kernel_call_save_uninterrupted_return_values _ _ _ _ _ _ _ Hrun) as [Hr0 _].
  assert (Hsaved_value : valid_os_cpu_sr final_registers.(kernel_save_r0)) by (rewrite Hr0; exact Hvalid).
  assert (Hstore_order : mutex_del_call_masked external platform critical sg call final_registers.(kernel_save_r0)
      state state ** ((cpu_sr # UInt |->_) ** (perr # UChar |-> old_error) ** frame) |--
    mutex_del_call_masked external platform critical sg call final_registers.(kernel_save_r0) state state **
      (cpu_sr # UInt |->_) ** ((perr # UChar |-> old_error) ** frame)) by entailer!.
  pose proof (mutex_del_call_saved_return_store external platform critical sg call final_registers.(kernel_save_r0)
    state state cpu_sr saved_heap body_heap _ Hsaved_value (Hstore_order saved_heap Hsaved) Hstore) as Hbody.
  destruct Hdomain as [Hzero|[_ [Haddress [_ Hslot]]]]; [contradiction|].
  assert (Hbody_order : mutex_del_call_masked external platform critical sg call final_registers.(kernel_save_r0)
      state state ** (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
      ((perr # UChar |-> old_error) ** frame) |--
    mutex_del_call_masked external platform critical sg call final_registers.(kernel_save_r0) state state **
      ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame)) by entailer!.
  destruct (mutex_del_call_masked_type_load external platform critical sg call final_registers.(kernel_save_r0)
    state state pe eid observed body_heap _ Haddress Hslot (Hbody_order body_heap Hbody)) as [Hread Hpost].
  rewrite Htype in Hread, Hpost.
  split; [exact Hstate|]. split; [exact Hlr|]. split; assumption.
Qed.

(** The interrupted/selected branch consumes the already checked actual
    install/take -> register restore -> Save suffix producer. It does not
    recreate that shared interface. The remaining capsule owner is kept
    explicitly through the C store/read. A complete Save prefix and handler
    middle still have to supply the hooked world; final-slot safety is _6. *)
Lemma mutex_del_call_selected_save_body : forall external platform port critical arch
  (continuations : Armv7aContinuationABI external platform port)
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  sg handler original transfer return_pc cpu_sr pe eid observed heap (frame : Assertion),
  let focus := armv7a_call_focus original (armv7a_save_entry_address suffix + 4) return_pc in
  os_int_exit_destination_binding external transfer ->
  task_stack_key transfer.(os_int_exit_incoming_stack) = task_stack_key original.(os_sched_call_stack) ->
  tcb_field_address (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg) transfer.(os_int_exit_hooked_state) **
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** ((cpu_sr # UInt |->_) ** frame))) heap ->
  exists installed saved,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)) transfer.(os_int_exit_incoming_sp) /\
    saved.(armv7a_continuation_call) = Some original /\
    saved.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 /\
    saved.(armv7a_continuation_lr) = return_pc /\
    (forall registers restored final_registers resumed saved_heap body_heap,
      saved.(armv7a_continuation_sp) = transfer.(os_int_exit_incoming_sp) ->
      registers.(kernel_save_cpsr) = saved.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_r0) = nth 0 saved.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_lr) = saved.(armv7a_continuation_lr) ->
      interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
      armv7a_continuation_restore_reads saved installed ->
      armv7a_restore_transition continuations handler saved installed restored ->
      armv7a_save_suffix_transition suffix registers (os_int_exit_installed_state transfer)
        restored final_registers resumed saved_heap ->
      kernel_heap_execution (pointer_store_writes cpu_sr final_registers.(kernel_save_r0)) saved_heap body_heap ->
      pe = event_addr sg eid -> sem_query_public_slot resumed eid observed ->
      resumed = os_int_exit_installed_state transfer /\
      final_registers.(kernel_save_return_word) = Some return_pc /\
      uchar_load (pe + OSEventType_off) (event_slot_type_value resumed.(EventState) eid) body_heap /\
      ((pe + OSEventType_off) # UChar |-> event_slot_type_value resumed.(EventState) eid **
       sem_query_type_frame sg resumed eid ** unmap_table_rep sg **
       critical_region_masked platform critical sg original.(os_sched_call_invocation)
         original.(os_sched_call_origin) final_registers.(kernel_save_r0) resumed **
       os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
       ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
        armv7a_parked_continuations continuations focus resumed **
        task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame))
      body_heap).
Proof.
  intros external platform port critical arch continuations suffix sg handler original transfer return_pc cpu_sr
    pe eid observed heap frame focus Hdestination Hkey Haddress Hpre.
  destruct (kernel_program_selected_save_continuation external platform port critical arch continuations suffix
    sg handler original transfer return_pc ((cpu_sr # UInt |->_) ** frame) heap Hdestination Hkey Haddress Hpre)
    as [installed [saved [Hinstall [Hcall [Hpc [Hlr Hconsume]]]]]].
  exists installed, saved; split; [exact Hinstall|]. split; [exact Hcall|].
  split; [exact Hpc|]. split; [exact Hlr|].
  intros registers restored final_registers resumed saved_heap body_heap Hsp Hcpsr Hr0 Hreglr Hsaved
    Hreads Hrestore Hsuffix Hstore Hpe Hslot.
  destruct (Hconsume registers restored final_registers resumed saved_heap Hsp Hcpsr Hr0 Hreglr Hsaved
    Hreads Hrestore Hsuffix) as [Hstate [Hreturn [Hvalue Howned]]].
  subst resumed.
  assert (Hvalid : valid_os_cpu_sr final_registers.(kernel_save_r0)) by (rewrite Hvalue; exact (proj1 Hsaved)).
  assert (Hopen : critical_region_masked platform critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) final_registers.(kernel_save_r0) (os_int_exit_installed_state transfer) **
      os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
      (armv7a_continuation_world continuations focus (kernel_program_inv sg) (os_int_exit_installed_state transfer) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       ((cpu_sr # UInt |->_) ** frame)) |--
    mutex_del_call_masked external platform critical sg (armv7a_continuation_resumed_call saved original)
      final_registers.(kernel_save_r0) (os_int_exit_installed_state transfer) (os_int_exit_installed_state transfer) **
      (cpu_sr # UInt |->_) ** (armv7a_parked_continuations continuations focus (os_int_exit_installed_state transfer) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)).
  { unfold mutex_del_call_masked, armv7a_continuation_world, armv7a_continuation_resumed_call; cbn; entailer!. }
  pose proof (mutex_del_call_saved_return_store external platform critical sg
    (armv7a_continuation_resumed_call saved original) final_registers.(kernel_save_r0)
    (os_int_exit_installed_state transfer) (os_int_exit_installed_state transfer) cpu_sr saved_heap body_heap _ Hvalid
    (Hopen saved_heap Howned) Hstore) as Hbody.
  assert (Horder : mutex_del_call_masked external platform critical sg (armv7a_continuation_resumed_call saved original)
      final_registers.(kernel_save_r0) (os_int_exit_installed_state transfer) (os_int_exit_installed_state transfer) **
      (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
      (armv7a_parked_continuations continuations focus (os_int_exit_installed_state transfer) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) |--
    mutex_del_call_masked external platform critical sg (armv7a_continuation_resumed_call saved original)
      final_registers.(kernel_save_r0) (os_int_exit_installed_state transfer) (os_int_exit_installed_state transfer) **
      ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
       armv7a_parked_continuations continuations focus (os_int_exit_installed_state transfer) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame))
    by entailer!.
  destruct (mutex_del_call_masked_type_load external platform critical sg
    (armv7a_continuation_resumed_call saved original) final_registers.(kernel_save_r0)
    (os_int_exit_installed_state transfer) (os_int_exit_installed_state transfer) pe eid observed body_heap _ Hpe Hslot
    (Horder body_heap Hbody)) as [Hload Hpost].
  split; [reflexivity|]. split; [exact Hreturn|]. split; [exact Hload|exact Hpost].
Qed.

(** A real preceding Restore return supplies the next local Del prefix's
    caller, context, program and inactive handler-stack owners. The same
    actual return heap is the prefix heap; invocation/origin come from the
    consumed return, not a new With argument. This is a C-source resource
    handoff, not an ISA proof of an arbitrary compiled application's call
    instruction/argument setup. The admitted C arguments retain the old
    nullable public-slot domain at THIS call's entry. *)
Section RestoreReturnPrefix.
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (port : OsIntExitPlatformResources) (abi : Armv7aContinuationABI external platform port)
  (sg : StableGlobVars) (Local : Type).
Variable local_step : OsIntExitCallContext ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable normal_return : OsIntExitCallContext -> StableGlobVars ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable handler_contract : forall handler,
  RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner platform port handler)
    (local_step handler) (normal_return handler).
Variable handler_stack : TaskStackRegion.
Variable handler_fragments : TaskStackFragments.

Lemma mutex_del_call_prefix_after_restore : forall critical arch
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  original saved entry checkpoint restore_entry cursor before written_cursor released
  returned final resumed final_cursor after pe eid observed perr old_error cpu_sr (frame : Assertion),
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked platform critical sg original.(os_sched_call_invocation)
     original.(os_sched_call_origin) saved entry ** os_sched_context_resources external original **
    (kernel_program_inv sg checkpoint ** task_stack_fragments_rep handler_stack handler_fragments **
      ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame))) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor released ->
  mutex_del_restore_irqs_execution external platform port abi sg Local local_step normal_return
    handler_stack handler_fragments (armv7a_irq_fiq_mask saved) (restore_entry + 8)
    cursor.(kernel_restore_lr) original checkpoint released returned final resumed ->
  armv7a_restore_suffix_transition restore written_cursor resumed final_cursor after ->
  mutex_del_call_pointer_domain sg final pe eid observed ->
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
  exists initialized result prefix_after,
    kernel_heap_execution (pointer_store_writes cpu_sr 0) after initialized /\
    mutex_del_call_prefix_execution sg pe perr initialized result prefix_after /\
    mutex_del_call_prefix_post sg final pe eid perr old_error result
      ((cpu_sr # UInt |-> 0) **
       (kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask saved) **
        task_stack_fragments_rep handler_stack handler_fragments ** frame)) prefix_after.
Proof.
  intros critical arch restore original saved entry checkpoint restore_entry cursor before written_cursor released
    returned final resumed final_cursor after pe eid observed perr old_error cpu_sr frame Hr0 Hmask Hpre
    Hprefix Hirqs Hsuffix Hdomain.
  destruct (mutex_del_restore_call_normal_return external platform port abi sg Local local_step normal_return
    handler_contract handler_stack handler_fragments critical arch restore original saved entry checkpoint
    restore_entry cursor before written_cursor released returned final resumed final_cursor after
    ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame) Hr0 Hmask Hpre Hprefix Hirqs Hsuffix)
    as [Hi [Ho [Hs [Hlr Hreturned]]]].
  assert (Hopen : kernel_program_closed platform critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) (armv7a_irq_fiq_mask saved) final **
      os_sched_context_resources external returned ** task_stack_fragments_rep handler_stack handler_fragments **
      ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame) |--
    kernel_program_inv sg final ** (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      (kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask saved) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)).
  { rewrite kernel_program_closed_equiv; unfold kernel_call_execution_owned; rewrite Hi, Ho; entailer!. }
  split; [exact Hlr|]. split; [exact Hi|]. split; [exact Ho|].
  eapply mutex_del_call_entry_prefix_source; [exact Hdomain|exact (Hopen after Hreturned)].
Qed.
End RestoreReturnPrefix.
