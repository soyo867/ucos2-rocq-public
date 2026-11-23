Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_call_spec.
Import ListNotations UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These are reversible field bundles, not abstract state updates. Their
    addresses are the same CNotation arrows as the generated source cells;
    no offset, lifetime, no-alias or platform premise is introduced. *)
Definition event_pend_multi_queue_deferred_cells (qcb : addr) (q : QueueFields)
  : Assertion :=
  &(qcb # "os_q" ->ₛ "OSQPtr") # Ptr |->_ **
  &(qcb # "os_q" ->ₛ "OSQIn") # Ptr |-> queue_in_addr q **
  &(qcb # "os_q" ->ₛ "OSQSize") # UShort |-> q.(qSize).

Lemma event_pend_multi_queue_cells_split_deferred : forall qcb q out entries,
  (&(qcb # "os_q" ->ₛ "OSQPtr") # Ptr |->_ **
   &(qcb # "os_q" ->ₛ "OSQStart") # Ptr |-> q.(qStart) **
   &(qcb # "os_q" ->ₛ "OSQEnd") # Ptr |-> queue_end_addr q **
   &(qcb # "os_q" ->ₛ "OSQIn") # Ptr |-> queue_in_addr q **
   &(qcb # "os_q" ->ₛ "OSQOut") # Ptr |-> out **
   &(qcb # "os_q" ->ₛ "OSQSize") # UShort |-> q.(qSize) **
   &(qcb # "os_q" ->ₛ "OSQEntries") # UShort |-> entries)
  --||--
  (&(qcb # "os_q" ->ₛ "OSQStart") # Ptr |-> q.(qStart) **
   &(qcb # "os_q" ->ₛ "OSQEnd") # Ptr |-> queue_end_addr q **
   &(qcb # "os_q" ->ₛ "OSQOut") # Ptr |-> out **
   &(qcb # "os_q" ->ₛ "OSQEntries") # UShort |-> entries **
   event_pend_multi_queue_deferred_cells qcb q).
Proof. intros; split; unfold event_pend_multi_queue_deferred_cells; entailer!. Qed.

(** After the first StatPend switch no Y/BitX/BitY reads remain. Only the
    pending byte is needed by the second switch, and Msg by its Mbox/Q arm.
    Invalid-type return keeps these old fields; cleanup is a separate split. *)
Definition event_pend_multi_resume_deferred_without_message (sg : StableGlobVars)
  (tid : TaskID) (task : TaskAbstractState) : Assertion :=
  let tcb := task_slot_addr sg tid in
  &(tcb # "os_tcb" ->ₛ "OSTCBStat") # UChar |-> event_pend_multi_task_status task **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventMultiPtr") # Ptr |-> event_pend_multi_task_multi_pointer task **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventMultiRdy") # Ptr |-> event_pend_multi_task_ready_pointer sg task **
  event_task_remove_multi_tcb_reads tcb task.

Definition event_pend_multi_resume_deferred_cells (sg : StableGlobVars)
  (tid : TaskID) (task : TaskAbstractState) : Assertion :=
  let tcb := task_slot_addr sg tid in
  event_pend_multi_resume_deferred_without_message sg tid task **
  &(tcb # "os_tcb" ->ₛ "OSTCBMsg") # Ptr |-> event_pend_multi_task_message task.

Lemma event_pend_multi_resume_cells_split_pending : forall sg tid task pending,
  let tcb := task_slot_addr sg tid in
  event_pend_multi_resume_cells sg tid task pending --||--
  sg.(g_OSTCBCur) # Ptr |-> tcb **
  &(tcb # "os_tcb" ->ₛ "OSTCBStatPend") # UChar |-> pending **
  event_pend_multi_resume_deferred_cells sg tid task.
Proof.
  intros; split; unfold event_pend_multi_resume_cells,
    event_pend_multi_resume_deferred_cells, event_pend_multi_resume_deferred_without_message;
    entailer!.
Qed.

Lemma event_pend_multi_resume_deferred_cells_split_message : forall sg tid task,
  let tcb := task_slot_addr sg tid in
  event_pend_multi_resume_deferred_cells sg tid task --||--
  &(tcb # "os_tcb" ->ₛ "OSTCBMsg") # Ptr |-> event_pend_multi_task_message task **
  event_pend_multi_resume_deferred_without_message sg tid task.
Proof. intros; split; unfold event_pend_multi_resume_deferred_cells; entailer!. Qed.

Lemma event_pend_multi_resume_deferred_cells_split_cleanup : forall sg tid task,
  let tcb := task_slot_addr sg tid in
  event_pend_multi_resume_deferred_cells sg tid task --||--
  &(tcb # "os_tcb" ->ₛ "OSTCBStat") # UChar |-> event_pend_multi_task_status task **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventMultiPtr") # Ptr |-> event_pend_multi_task_multi_pointer task **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventMultiRdy") # Ptr |-> event_pend_multi_task_ready_pointer sg task **
  &(tcb # "os_tcb" ->ₛ "OSTCBMsg") # Ptr |-> event_pend_multi_task_message task **
  event_task_remove_multi_tcb_reads tcb task.
Proof.
  intros sg tid task; cbn zeta; split; unfold event_pend_multi_resume_deferred_cells,
    event_pend_multi_resume_deferred_without_message; entailer!.
Qed.

Lemma event_pend_multi_saved_value_duplicate_equiv : forall mask saved frame,
  coq_prop (interrupt_saved_value mask saved) &&
    (coq_prop (interrupt_saved_value mask saved) && frame) --||--
  coq_prop (interrupt_saved_value mask saved) && frame.
Proof.
  intros mask saved frame.
  change (“ interrupt_saved_value mask saved ” &&
    (“ interrupt_saved_value mask saved ” && frame) --||--
    “ interrupt_saved_value mask saved ” && frame).
  split; entailer!.
Qed.
