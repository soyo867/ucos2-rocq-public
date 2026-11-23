Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cleanup_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage ListNotations.
Import Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** The unowned optional environment has no task stack capsule. The local
    MRS/CPSID/DSB/BX path nevertheless owns its ordinary execution resource
    and returns the same state. This producer uses the existing ARM resource
    interface directly, without a running-task or ready-list premise. *)
Lemma sem_pend_unowned_save_phase : forall external platform critical arch
  (save : Armv7aSaveSuffixABI external platform critical arch)
  sg call mask state pevent eid observed registers before final_registers acquired after
  (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  sem_pend_runtime_nonblocking critical sg call None pevent state eid ->
  (sem_pend_phase_save_input (SemPendAcquirePhase pevent eid observed)
     external platform None critical sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired after ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after /\
  acquired = state /\
  sem_pend_optional_acquire_observation None critical sg call call mask
    final_registers.(kernel_save_r0) state state eid observed observed /\
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
   os_sched_context_resources external call ** (UCOS2_inv sg state ** frame)) after /\
  (sem_pend_phase_save_output (SemPendAcquirePhase pevent eid observed)
     external platform None critical sg call mask final_registers.(kernel_save_r0) state ** frame) after.
Proof.
  intros external platform critical arch save sg call mask state pevent eid observed registers before
    final_registers acquired after frame Hreturn Hcpsr Hmask Hnonblocking Hpre Hrun.
  assert (Hopen : sem_pend_phase_save_input (SemPendAcquirePhase pevent eid observed)
    external platform None critical sg call mask state ** frame |--
    coq_prop (sem_pend_save_phase_pre (SemPendAcquirePhase pevent eid observed)
      None critical sg call mask state /\ UCOS2_state_inv sg state) &&
    (kernel_call_execution_owned external platform call mask ** (UCOS2_inv sg state ** frame))).
  { unfold sem_pend_phase_save_input, sem_pend_stack_save_input, sem_pend_optional_stack_resources.
    rewrite mutex_query_closed_equiv; unfold kernel_call_execution_owned, UCOS2_inv; entailer!. }
  destruct (Hopen before Hpre) as [[Hphase Hvalid] Howned].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hcpsr|reflexivity]).
  assert (Howned' : (kernel_call_execution_owned external platform call
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
    (UCOS2_inv sg state ** frame)) before).
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask; exact Howned. }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch save sg call
    (kernel_save_read_cpsr registers) state before final_registers acquired after
    (UCOS2_inv sg state ** frame) Hsaved Howned' Hrun)
    as [Hstate [Hmemory [Hlr [Hr0 Hafter]]]].
  assert (Hexecution : kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired after).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hrun). }
  split; [exact Hexecution|]. split; [exact Hstate|]. subst acquired.
  assert (Hfinal_saved : interrupt_saved_value mask final_registers.(kernel_save_r0)).
  { rewrite Hr0; cbn [kernel_save_read_cpsr kernel_save_r0]; split; assumption. }
  assert (Hinterval : critical_region_interval critical sg call.(os_sched_call_invocation) state state)
    by constructor.
  destruct Hphase as [Hinput [Hnonnull [Hclear Hadmission]]].
  destruct (sem_pend_call_input_nonnull _ _ _ _ _ _ _ Hinput Hnonnull)
    as [Haddress [Hid [Hslot Hprotocol]]].
  assert (Htype : event_slot_type_value state.(EventState) eid = 3).
  { destruct (Z.eq_dec (event_slot_type_value state.(EventState) eid) 3) as [Heq|Hne];
      [exact Heq|].
    rewrite (sem_pend_context_error_type_first _ _ _ Hne) in Hclear; discriminate. }
  destruct (sem_query_public_slot_is_sem state eid observed Hslot Htype) as [Hlookup Hsem].
  assert (Hobservation : sem_pend_optional_acquire_observation None critical sg call call mask
    final_registers.(kernel_save_r0) state state eid observed observed).
  { unfold sem_pend_optional_acquire_observation, sem_query_acquire_facts,
      kernel_stack_call_same_call.
    repeat first [assumption | split | reflexivity]. }
  assert (Hordered : sem_pend_precritical_error pevent (event_slot_type_value state.(EventState) eid)
    state.(IntrState).(intNesting) state.(IntrState).(lockNesting) = None).
  { unfold sem_pend_precritical_error; rewrite (proj2 (Z.eqb_neq _ _) Hnonnull); exact Hclear. }
  assert (Hpositive : 0 < encode_event_cnt_value observed).
  { exact (Hnonblocking eq_refl Hordered state observed Hinterval Hlookup Hsem). }
  assert (Hphase_after : sem_pend_save_phase_observation (SemPendAcquirePhase pevent eid observed)
    None critical sg call call mask final_registers.(kernel_save_r0) state state).
  { exists observed; split; [exact Hobservation|intro; lia]. }
  assert (Hbase : sem_pend_stack_save_observation critical sg call call None mask
    final_registers.(kernel_save_r0) state state).
  { unfold sem_pend_stack_save_observation, kernel_stack_call_same_call, sem_pend_save_facts.
    repeat first [assumption | split | reflexivity | intro]. }
  split; [exact Hobservation|]. split; [exact Hafter|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold sem_pend_phase_save_output; Exists call state.
    unfold sem_pend_optional_stack_resources; entailer!. }
  exact (Hclose after Hafter).
Qed.

(** After the existing ordered null/type/ISR/lock guard, C only stores
    its selected error and returns. No Save, Scheduler or task resource
    is needed. The checked C caller supplies the guard/read correspondence;
    this source consumer executes its actual error store and public tail. *)
Lemma sem_pend_unowned_early_error_source : forall external platform critical sg call mask
  state pevent eid observed timeout perr code (frame : Assertion) before X,
  sem_pend_call_input critical sg call.(os_sched_call_invocation) pevent state eid observed ->
  sem_pend_precritical_error pevent (event_slot_type_value state.(EventState) eid)
    state.(IntrState).(intNesting) state.(IntrState).(lockNesting) = Some code ->
  safeExec (LastSeen state)
    (bind (atomic_cmd (sem_pend_runtime_program external platform None critical sg call pevent timeout))
      sem_query_observe_error) X ->
  (sem_pend_stack_save_input external platform None critical sg call mask state **
    unmap_table_rep sg ** perr # UChar |->_ ** frame) before ->
  exists after, kernel_heap_execution [(perr, encode_os_err_code code)] before after /\
    (sem_pend_stack_call_post external platform None critical sg call mask
      pevent timeout perr state X ** frame) after.
Proof.
  intros external platform critical sg call mask state pevent eid observed timeout perr code frame before X
    Hinput Herror Hexec Hpre.
  assert (Hruntime : sem_pend_runtime_program external platform None critical sg call pevent timeout
    state (encode_os_err_code code) state).
  { left; unfold sem_pend_precritical_error in Herror.
    destruct (Z.eqb pevent 0) eqn:Hzero.
    - apply Z.eqb_eq in Hzero; subst pevent; inversion Herror; subst code.
      split; [apply sem_pend_c_null_return|auto].
    - apply Z.eqb_neq in Hzero.
      destruct (sem_pend_call_input_nonnull _ _ _ _ _ _ _ Hinput Hzero)
        as [Haddress [Hid [Hslot Hprotocol]]].
      split; [eapply sem_pend_c_context_return; eassumption|].
      split; [right; exists eid; split; [exact Haddress|rewrite Herror; discriminate]|reflexivity]. }
  assert (Hrange : 0 <= encode_os_err_code code < 256).
  { unfold sem_pend_precritical_error, sem_pend_context_error in Herror.
    repeat match type of Herror with context [if ?test then _ else _] => destruct test end;
      inversion Herror; subst; cbn; lia. }
  set (tail := sem_pend_stack_save_input external platform None critical sg call mask state **
    unmap_table_rep sg ** frame).
  assert (Hstore : (perr # UChar |->_ ** tail) before).
  { match type of Hpre with ?P before => match goal with |- ?Q before => assert (Horder : P |-- Q)
      by (unfold tail; entailer!) end end; exact (Horder before Hpre). }
  destruct (sem_pend_error_store perr (encode_os_err_code code) tail before Hrange Hstore)
    as [after [Hwrite Hafter]].
  exists after; split; [exact Hwrite|].
  assert (Hsame : kernel_stack_call_same_call call call) by (repeat split; reflexivity).
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold tail, sem_pend_stack_save_input.
    match goal with |- ?P |-- _ => assert (Hpad : P |--
      (TT ** mutex_query_closed platform critical sg call.(os_sched_call_invocation)
        call.(os_sched_call_origin) mask state ** os_sched_context_resources external call **
       unmap_table_rep sg ** perr # UChar |-> encode_os_err_code code **
       sem_pend_optional_stack_resources external platform None call state) ** frame)
       by (entailer!; apply derivable1_truep_intros) end.
    eapply derivable1_trans; [exact Hpad|].
    sep_apply_l_atomic (sem_pend_stack_call_post_from_result external platform None critical sg call call mask
      pevent timeout perr state state (encode_os_err_code code) X Hruntime Hexec Hsame); entailer!. }
  exact (Hclose after Hafter).
Qed.

(** The actual final MSR and BX transitions share the same intermediate
    heap. Their concrete history supplies the uninterrupted None arm;
    this statement makes no claim about interrupted returns. *)
Lemma sem_pend_unowned_restore_phase : forall external platform critical arch
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg call mask saved acquired released cursor before written middle final_cursor after
  (frame : Assertion),
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (sem_pend_stack_restore_input external platform None critical sg call mask saved acquired released ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  (sem_pend_phase_restore_output SemPendReturnPhase external platform None critical sg call mask released ** frame) after.
Proof.
  intros external platform critical arch restore sg call mask saved acquired released cursor before written
    middle final_cursor after frame Hr0 Hmask Hpre Hprefix Hsuffix.
  assert (Hopen : sem_pend_stack_restore_input external platform None critical sg call mask saved acquired released ** frame |--
    coq_prop (interrupt_saved_value mask saved) &&
    (critical_region_masked platform critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) saved acquired ** os_sched_context_resources external call **
      (UCOS2_inv sg released ** frame))).
  { unfold sem_pend_stack_restore_input, sem_pend_optional_stack_resources; entailer!. }
  destruct (Hopen before Hpre) as [Hsaved Howned].
  destruct (armv7a_restore_uninterrupted_transports_owned_execution external platform critical arch restore
    sg call saved acquired cursor before written middle final_cursor after (UCOS2_inv sg released ** frame)
    Hr0 Hmask Howned Hprefix Hsuffix) as [Hrun [Hreturn [Hmemory Hafter]]].
  assert (Hhistory : sem_pend_unowned_restore_history external platform critical sg
    call released call released).
  { eapply SemPendUnownedRestoreUninterrupted; eassumption. }
  split; [exact Hrun|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold sem_pend_phase_restore_output; Exists call released.
    rewrite mutex_query_closed_equiv, (proj2 Hsaved).
    unfold sem_pend_optional_restore_history, sem_pend_stack_restore_observation,
      sem_pend_restore_phase_pre, sem_pend_optional_stack_resources,
      kernel_stack_call_same_call, kernel_call_execution_owned; entailer!. }
  exact (Hclose after Hafter).
Qed.

(** The count read is witnessed by the typed physical cell on this heap.
    The two-byte write is ONE unsigned-short C store in the masked region. *)
Lemma sem_pend_count_decrement_source : forall sg state eid event (frame : Assertion) before,
  UCOS2_state_inv sg state -> mutex_query_lookup state eid event ->
  event.(eventType) = OS_EVENT_TYPE_SEM -> 0 < encode_event_cnt_value event ->
  (UCOS2_inv sg state ** frame) before ->
  ((event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value event ** TT) before /\
  exists after,
    kernel_heap_execution (byte_list_writes (event_addr sg eid + OSEventCnt_off)
      [(encode_event_cnt_value event - 1) mod 256;
       ((encode_event_cnt_value event - 1) / 256) mod 256]) before after /\
    (UCOS2_inv sg (sem_count_update_state state eid event (encode_event_cnt_value event - 1)) ** frame) after.
Proof.
  intros sg state eid event frame before Hvalid Hlookup Htype Hpositive Hpre.
  assert (Hsplit : UCOS2_inv sg state ** frame |--
    coq_prop (0 <= encode_event_cnt_value event <= 65535) &&
    ((event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value event **
      (sem_post_count_frame sg state eid event ** frame))).
  { sep_apply_l_atomic (sem_post_count_split_full sg state eid event Hlookup Htype); entailer!. }
  destruct (Hsplit before Hpre) as [Hrange Hcells].
  change (0 <= encode_event_cnt_value event <= 65535) in Hrange.
  split.
  - match type of Hcells with ?P before => match goal with |- ?Q before => assert (Hread : P |-- Q)
      by (entailer!; intros ? ?; exact I) end end; exact (Hread before Hcells).
  - assert (Hforget : (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value event **
      (sem_post_count_frame sg state eid event ** frame) |--
      (event_addr sg eid + OSEventCnt_off) # UShort |->_ **
      (sem_post_count_frame sg state eid event ** frame)).
    { sep_apply_l_atomic (store_ushort_undef_store_ushort (event_addr sg eid + OSEventCnt_off)
        (encode_event_cnt_value event)); entailer!. }
    destruct (event_create_count_store_execution (event_addr sg eid + OSEventCnt_off)
      (encode_event_cnt_value event - 1) (sem_post_count_frame sg state eid event ** frame)
      before ltac:(lia) (Hforget before Hcells)) as [after [Hrun Hwritten]].
    exists after; split; [exact Hrun|].
    match type of Hwritten with ?P after => match goal with |- ?Q after => assert (Hmerge : P |-- Q) end end.
    { sep_apply_l_atomic (sem_pend_count_merge_decrement sg state eid event Hvalid Hlookup Htype Hpositive); entailer!. }
    exact (Hmerge after Hwritten).
Qed.

(** Immediate success follows the literal source order: first Save,
    count--, final Restore, then *perr = OS_ERR_NONE. The public result is
    the original optional-environment specification. This family allows
    OSInit-before-OSStart and introduces no task/readiness premise. *)
Lemma sem_pend_unowned_immediate_source : forall external platform critical arch
  (save : Armv7aSaveSuffixABI external platform critical arch)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg call mask state pevent eid observed timeout perr registers before final_registers acquired saved_heap
  (frame : Assertion) X,
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  sem_pend_runtime_nonblocking critical sg call None pevent state eid ->
  safeExec (LastSeen state)
    (bind (atomic_cmd (sem_pend_runtime_program external platform None critical sg call pevent timeout))
      sem_query_observe_error) X ->
  (sem_pend_phase_save_input (SemPendAcquirePhase pevent eid observed)
     external platform None critical sg call mask state ** unmap_table_rep sg **
    perr # UChar |->_ ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\
  ((event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value observed ** TT) saved_heap /\
  exists counted,
    kernel_heap_execution (byte_list_writes (event_addr sg eid + OSEventCnt_off)
      [(encode_event_cnt_value observed - 1) mod 256;
       ((encode_event_cnt_value observed - 1) / 256) mod 256]) saved_heap counted /\
    (forall cursor written middle final_cursor restored,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor counted written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor restored ->
      kernel_call_restore_uninterrupted_execution arch cursor counted final_cursor restored /\
      exists after, kernel_heap_execution [(perr, 0)] restored after /\
        (sem_pend_stack_call_post external platform None critical sg call mask
          pevent timeout perr state X ** frame) after).
Proof.
  intros external platform critical arch save restore sg call mask state pevent eid observed timeout perr registers
    before final_registers acquired saved_heap frame X Hreturn Hcpsr Hmask Hnonblocking Hexec Hpre Hsave.
  assert (Hphase : sem_pend_save_phase_pre (SemPendAcquirePhase pevent eid observed)
    None critical sg call mask state).
  { match type of Hpre with ?P before => assert (Hget : P |-- coq_prop
      (sem_pend_save_phase_pre (SemPendAcquirePhase pevent eid observed) None critical sg call mask state) && TT)
      by (unfold sem_pend_phase_save_input; entailer!) end; exact (proj1 (Hget before Hpre)). }
  assert (Hsave_pre : (sem_pend_phase_save_input (SemPendAcquirePhase pevent eid observed)
    external platform None critical sg call mask state **
    (unmap_table_rep sg ** perr # UChar |->_ ** frame)) before).
  { match type of Hpre with ?P before => match goal with |- ?Q before => assert (Horder : P |-- Q)
      by entailer! end end; exact (Horder before Hpre). }
  destruct (sem_pend_unowned_save_phase external platform critical arch save sg call mask state pevent eid observed
    registers before final_registers acquired saved_heap (unmap_table_rep sg ** perr # UChar |->_ ** frame)
    Hreturn Hcpsr Hmask Hnonblocking Hsave_pre Hsave) as [Hrun [Hstate [Hobservation [Hexact Hsaved]]]].
  split; [exact Hrun|]. split; [exact Hstate|]. subst acquired.
  destruct Hphase as [Hinput [Hnonnull [Hclear Hadmission]]].
  destruct (sem_pend_call_input_nonnull _ _ _ _ _ _ _ Hinput Hnonnull)
    as [Haddress [Hid [Hslot Hprotocol]]].
  pose proof (sem_pend_optional_acquire_fields _ _ _ _ _ _ _ _ _ _ _ _ Hobservation)
    as [Hsame [Hsavedword [Hvalid [_ [Hlookup [_ [Htype Hgeneration]]]]]]].
  assert (Hpositive : 0 < encode_event_cnt_value observed).
  { assert (Hordered : sem_pend_precritical_error pevent (event_slot_type_value state.(EventState) eid)
      state.(IntrState).(intNesting) state.(IntrState).(lockNesting) = None).
    { unfold sem_pend_precritical_error; rewrite (proj2 (Z.eqb_neq _ _) Hnonnull); exact Hclear. }
    exact (Hnonblocking eq_refl Hordered state observed ltac:(constructor) Hlookup Htype). }
  set (checkpoint := sem_count_update_state state eid observed (encode_event_cnt_value observed - 1)).
  assert (Hresult : sem_pend_checkpoint_result None critical sg call pevent timeout state 0 checkpoint).
  { eapply sem_pend_observed_immediate_result; eassumption. }
  set (tail := critical_region_masked platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
    os_sched_context_resources external call ** unmap_table_rep sg ** perr # UChar |->_ ** frame).
  assert (Howned : (UCOS2_inv sg state ** tail) saved_heap).
  { match type of Hexact with ?P saved_heap => assert (Hopen : P |-- UCOS2_inv sg state ** tail)
      by (unfold tail; entailer!) end; exact (Hopen saved_heap Hexact). }
  destruct (sem_pend_count_decrement_source sg state eid observed tail saved_heap
    Hvalid Hlookup Htype Hpositive Howned) as [Hread [counted [Hwrite Hcounted]]].
  split; [exact Hread|]. exists counted; split; [exact Hwrite|].
  intros cursor written middle final_cursor restored Hr0 Hmasked Hprefix Hsuffix.
  assert (Hrestore_pre : (sem_pend_stack_restore_input external platform None critical sg call mask
    final_registers.(kernel_save_r0) state checkpoint **
    (unmap_table_rep sg ** perr # UChar |->_ ** frame)) counted).
  { match type of Hcounted with ?P counted => match goal with |- ?Q counted => assert (Hclose : P |-- Q)
      by (unfold tail, checkpoint, sem_pend_stack_restore_input, sem_pend_optional_stack_resources; entailer!) end end.
    exact (Hclose counted Hcounted). }
  destruct (sem_pend_unowned_restore_phase external platform critical arch restore sg call mask
    final_registers.(kernel_save_r0) state checkpoint cursor counted written middle final_cursor restored
    (unmap_table_rep sg ** perr # UChar |->_ ** frame) Hr0 Hmasked Hrestore_pre Hprefix Hsuffix)
    as [Hrestore Hrestored].
  split; [exact Hrestore|].
  set (return_frame := sem_pend_phase_restore_output SemPendReturnPhase external platform None
    critical sg call mask checkpoint ** unmap_table_rep sg ** frame).
  assert (Herror_pre : (perr # UChar |->_ ** return_frame) restored).
  { match type of Hrestored with ?P restored => match goal with |- ?Q restored => assert (Horder : P |-- Q)
      by (unfold return_frame; entailer!) end end; exact (Horder restored Hrestored). }
  destruct (sem_pend_error_store perr 0 return_frame restored ltac:(lia) Herror_pre)
    as [after [Herror Hafter]].
  exists after; split; [exact Herror|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hfinish : P |-- Q) end end.
  { unfold return_frame; rewrite <- sem_pend_phase_restore_return_output.
    match goal with |- ?P |-- _ => assert (Hpad : P |--
      (TT ** sem_pend_stack_restore_source_output external platform None critical sg call mask checkpoint **
        unmap_table_rep sg ** perr # UChar |-> 0) ** frame)
      by (entailer!; apply derivable1_truep_intros) end.
    eapply derivable1_trans; [exact Hpad|].
    sep_apply_l_atomic (sem_pend_stack_call_post_from_restore external platform None critical sg call call mask
      pevent timeout perr state checkpoint 0 eid X Hresult Hnonnull Haddress Hclear Hsame Hexec); entailer!. }
  exact (Hfinish after Hafter).
Qed.
