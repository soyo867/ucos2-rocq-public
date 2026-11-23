Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_annotation_spec.
Require Import Ucos2Verify.lib.event.
Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

(** The legacy SemPend post owns a genuine coq_prop carrier disjoint from
    its returned resources.  It may contain a nonempty residual heap.  The
    Task keeps that heap in this explicit ordinary frame across all later
    stages; it is never discarded by an implication to emp. *)
Definition tmr_task_call_residual : TmrTaskRules.expr := fun _ => True.

Lemma tmr_task_call_residual_join :
  TmrTaskRules.derivable1
    (TmrTaskRules.sepcon tmr_task_call_residual tmr_task_call_residual)
    tmr_task_call_residual.
Proof. intros heap Hjoined; exact I. Qed.

Lemma tmr_task_call_residual_start : forall resources,
  TmrTaskRules.derivable1 resources
    (TmrTaskRules.sepcon resources tmr_task_call_residual).
Proof.
  intros resources heap Hresources.
  destruct (TmrTaskRules.unit_join heap) as [unit [Hunit Hjoin]].
  exists heap, unit; split; [exact Hjoin|]. split; [exact Hresources|exact I].
Qed.

(** Exact ordered address side condition from the checked OSSemPend C
    contract.  The predicate only folds its existing disjunction for QCP;
    NULL, wrong type, ISR, locked and actual blocking paths remain present.
    Field addresses are arguments carrying the original C alias-arrow terms.
    This proposition never grants ownership of those fields. *)
Definition tmr_task_pend_address_guard sg (before : UCOS2_Verify_State)
  environment critical context pe eid type_address count_address
  ints locks current group rows : Prop :=
  pe = 0 \/
  (pe <> 0 /\ type_address = event_addr sg eid + OSEventType_off /\
    (event_slot_type_value before.(EventState) eid <> 3 \/
      (event_slot_type_value before.(EventState) eid = 3 /\ ints = sg.(g_OSIntNesting) /\
        (before.(IntrState).(intNesting) > 0 \/
          (before.(IntrState).(intNesting) <= 0 /\ locks = sg.(g_OSLockNesting) /\
            (before.(IntrState).(lockNesting) > 0 \/
              (before.(IntrState).(lockNesting) <= 0 /\
                count_address = event_addr sg eid + OSEventCnt_off /\
                sem_pend_observed_blocking_layout environment critical sg context before eid
                  current group rows))))))).

Lemma tmr_task_pend_address_guard_unfold : forall sg before environment critical context
  pe eid type_address count_address ints locks current group rows,
  tmr_task_pend_address_guard sg before environment critical context pe eid
    type_address count_address ints locks current group rows <->
  pe = 0 \/
  (pe <> 0 /\ type_address = event_addr sg eid + OSEventType_off /\
    (event_slot_type_value before.(EventState) eid <> 3 \/
      (event_slot_type_value before.(EventState) eid = 3 /\ ints = sg.(g_OSIntNesting) /\
        (before.(IntrState).(intNesting) > 0 \/
          (before.(IntrState).(intNesting) <= 0 /\ locks = sg.(g_OSLockNesting) /\
            (before.(IntrState).(lockNesting) > 0 \/
              (before.(IntrState).(lockNesting) <= 0 /\
                count_address = event_addr sg eid + OSEventCnt_off /\
                sem_pend_observed_blocking_layout environment critical sg context before eid
                  current group rows))))))).
Proof. intros; reflexivity. Qed.

(** The argument expression OSTmrSemSignal must still be readable BEFORE
    the callee consumes its full kernel precondition.  The same typed cell
    and this wand restore precisely that original product-lifted pre.
    AppRep/capabilities/C locals stay in the ordinary disjoint caller frame;
    the view neither consumes them nor changes the callee's postcondition. *)
Definition tmr_task_pend_argument_rest external platform environment critical saved_local sg
  context mask signal_address signal ticks perr before eid observed X : TmrTaskRules.expr :=
  TmrTaskRules.wand (TmrTaskRules.store_ptr signal_address signal)
    (tmr_task_pend_call_pre external platform environment critical saved_local sg context
      mask signal ticks perr before eid observed X).

Definition tmr_task_pend_argument_pre external platform environment critical saved_local sg
  context mask signal_address signal ticks perr before eid observed X : TmrTaskRules.expr :=
  TmrTaskRules.sepcon (TmrTaskRules.store_ptr signal_address signal)
    (tmr_task_pend_argument_rest external platform environment critical saved_local sg context
      mask signal_address signal ticks perr before eid observed X).

Lemma tmr_task_pend_argument_pre_closed : forall external platform environment critical saved_local
  sg context mask signal_address signal ticks perr before eid observed X,
  TmrTaskRules.derivable1
    (tmr_task_pend_argument_pre external platform environment critical saved_local sg context
      mask signal_address signal ticks perr before eid observed X)
    (tmr_task_pend_call_pre external platform environment critical saved_local sg context
      mask signal ticks perr before eid observed X).
Proof.
  intros external platform environment critical saved_local sg context mask signal_address
    signal ticks perr before eid observed X heap
    [cell [rest [Hjoin [Hcell Hrest]]]].
  apply (Hrest cell heap).
  - exact (TmrTaskRules.join_comm cell rest heap Hjoin).
  - exact Hcell.
Qed.

Lemma tmr_task_pend_argument_pre_frame : forall external platform environment critical saved_local
  sg context mask signal_address signal ticks perr before eid observed X frame,
  TmrTaskRules.derivable1
    (TmrTaskRules.sepcon
      (tmr_task_pend_argument_pre external platform environment critical saved_local sg context
        mask signal_address signal ticks perr before eid observed X) frame)
    (TmrTaskRules.sepcon
      (tmr_task_pend_call_pre external platform environment critical saved_local sg context
        mask signal ticks perr before eid observed X) frame).
Proof.
  intros external platform environment critical saved_local sg context mask signal_address
    signal ticks perr before eid observed X frame heap
    [callee [rest [Hjoin [Hcallee Hframe]]]].
  exists callee, rest; split; [exact Hjoin|]. split; [|exact Hframe].
  exact (tmr_task_pend_argument_pre_closed external platform environment critical saved_local
    sg context mask signal_address signal ticks perr before eid observed X callee Hcallee).
Qed.
