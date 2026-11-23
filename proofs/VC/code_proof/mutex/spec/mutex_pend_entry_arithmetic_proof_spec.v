Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib Require Import Monad.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.lib.mutex_query_spec.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma mutex_pend_shifted_priority_range__entry_arithmetic : forall priority,
  0 <= priority < 64 ->
  Z.shiftr priority 3 = tcb_y_of_prio priority /\
  0 <= unsigned_last_nbits (Z.shiftr priority 3) 8 < 8.
Proof.
  intros priority Hp.
  assert (Hy : 0 <= priority / 8 < 8).
  { split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  rewrite Z.shiftr_div_pow2 by lia.
  change (priority / 8 = tcb_y_of_prio priority /\
    0 <= unsigned_last_nbits (priority / 8) 8 < 8).
  split; [reflexivity|].
  rewrite unsigned_last_nbits_eq; [exact Hy|].
  change (0 <= priority / 8 < 256); lia.
Qed.

Lemma mutex_pend_early_post__entry_arithmetic :
  forall external platform environment critical saved_local sg original mask
    pe eid timeout perr before X error,
  mutex_pend_precritical_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some error ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (mutex_pend_api_program environment critical sg original pe eid timeout))
      sem_query_observe_error) X ->
  perr # UChar |-> encode_os_err_code error **
  sem_pend_continuation_save_input external platform environment critical saved_local
    sg original mask before ** unmap_table_rep sg |--
  mutex_pend_api_post external platform environment critical saved_local
    sg original mask pe eid timeout perr before X.
Proof.
  intros * Herr Hexec.
  pose proof (mutex_pend_api_early_result environment critical sg original pe eid timeout
    before error Herr) as Hprogram.
  pose proof (mutex_pend_api_safe_return environment critical sg original pe eid timeout
    before (encode_os_err_code error) before X Hprogram Hexec) as Hsafe.
  assert (Hsame : kernel_stack_call_same_call original original).
  { unfold kernel_stack_call_same_call; repeat split; reflexivity. }
  unfold mutex_pend_api_post; Exists original before (encode_os_err_code error).
  entailer!.
Qed.

Lemma mutex_pend_priority_native_fields__entry_arithmetic : forall priority,
  0 <= priority < 64 ->
  unsigned_last_nbits
    (Z.shiftl 1 (unsigned_last_nbits (Z.shiftr priority 3) 8)) 8 =
      tcb_bit_y_of_prio priority /\
  unsigned_last_nbits (Z.shiftl 1 (Z.land priority 7)) 8 =
      tcb_bit_x_of_prio priority /\
  unsigned_last_nbits (Z.shiftr priority 3) 8 = tcb_y_of_prio priority /\
  Z.land priority 7 = tcb_x_of_prio priority.
Proof.
  intros priority Hp.
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding
    priority Hp) as [Hx [Hy [Hland _]]].
  destruct (mutex_pend_shifted_priority_range__entry_arithmetic priority Hp)
    as [Hshift _].
  assert (Hbyte : unsigned_last_nbits (Z.shiftr priority 3) 8 = tcb_y_of_prio priority).
  { rewrite Hshift; apply unsigned_last_nbits_eq.
    change (0 <= tcb_y_of_prio priority < 256); lia. }
  rewrite Hbyte, Hland.
  repeat split; try reflexivity;
    apply shift_one_unsigned_byte_eq__priority_encoding; assumption.
Qed.
