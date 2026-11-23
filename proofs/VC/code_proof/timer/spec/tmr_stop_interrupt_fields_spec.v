Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_stop_spec.

Local Open Scope Z_scope.

(** The same interrupt-module decomposition used by OSTmrStart, applied
    to Stop's closed context.  The existing closed-region equivalence
    supplies the raw kernel representation.  No new layout or resource
    transition is assumed.  The residual owns the OTHER interrupt byte. *)
Module TmrStopOldInterruptFields.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

Definition context_rest (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (mask : Z) (kernel : UCOS2_Verify_State)
  : Assertion :=
  coq_prop (UCOS2_state_inv sg kernel) &&
  (interrupt_platform_running platform context.(os_sched_call_invocation)
     context.(os_sched_call_origin) mask **
   sg.(g_OSLockNesting) # UChar |-> kernel.(IntrState).(lockNesting) **
   UCOS2_raw_rep_missing_interrupt sg kernel **
   os_sched_context_resources external context ** unmap_table_rep sg).

Lemma context_rep_split_interrupt : forall external platform critical sg
  context mask kernel,
  mutex_query_closed platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask kernel **
    (os_sched_context_resources external context ** unmap_table_rep sg) |--
  sg.(g_OSIntNesting) # UChar |-> os_sched_lock_ints kernel **
    context_rest external platform sg context mask kernel.
Proof.
  intros; unfold context_rest.
  rewrite mutex_query_closed_equiv, UCOS2_inv_split_interrupt.
  unfold interrupt_inv, store_int_state, os_sched_lock_ints. entailer!.
Qed.

Lemma context_rep_merge_interrupt : forall external platform critical sg
  context mask kernel,
  sg.(g_OSIntNesting) # UChar |-> os_sched_lock_ints kernel **
    context_rest external platform sg context mask kernel |--
  mutex_query_closed platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask kernel **
    (os_sched_context_resources external context ** unmap_table_rep sg).
Proof.
  intros; unfold context_rest.
  rewrite mutex_query_closed_equiv, UCOS2_inv_split_interrupt.
  unfold interrupt_inv, store_int_state, interrupt_in_range, os_sched_lock_ints.
  Intros.
  prop_apply_p (store_uchar_range sg.(g_OSIntNesting) kernel.(IntrState).(intNesting)).
  prop_apply_p (store_uchar_range sg.(g_OSLockNesting) kernel.(IntrState).(lockNesting)).
  entailer!.
Qed.
End TmrStopOldInterruptFields.

Definition tmr_stop_interrupt_rest (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars) (mask : Z)
  (context : OsSchedCallContext) (kernel : UCOS2_Verify_State) : TmrStopRules.expr :=
  TmrStopRules.lift
    (TmrStopOldInterruptFields.context_rest external platform sg context mask kernel).

Lemma tmr_stop_context_rep_split_interrupt : forall external platform critical sg
  mask context kernel,
  TmrStopRules.derivable1
    (tmr_stop_context_rep external platform critical sg mask context kernel)
    (TmrStopRules.sepcon
      (TmrStopRules.store_uchar sg.(g_OSIntNesting) (os_sched_lock_ints kernel))
      (tmr_stop_interrupt_rest external platform sg mask context kernel)).
Proof.
  intros external platform critical sg mask context kernel heap Hcontext.
  pose proof (proj1 (TimerCalleeLift.os_sched_closed_resources_lift
    external platform critical sg context mask kernel) heap Hcontext) as Hold.
  pose proof (TmrStopRules.lift_entailment _ _
    (TmrStopOldInterruptFields.context_rep_split_interrupt
      external platform critical sg context mask kernel) heap Hold) as Hsplit.
  destruct (proj1 (TmrStopRules.lift_sepcon _ _ heap) Hsplit)
    as [cell [rest [Hjoin [Hcell Hrest]]]].
  exists cell, rest. split; [exact Hjoin|]. split; [|exact Hrest].
  exact (proj2 (TmrStopRules.store_uchar_lift sg.(g_OSIntNesting)
    (os_sched_lock_ints kernel)) cell Hcell).
Qed.

Lemma tmr_stop_context_rep_merge_interrupt : forall external platform critical sg
  mask context kernel,
  TmrStopRules.derivable1
    (TmrStopRules.sepcon
      (TmrStopRules.store_uchar sg.(g_OSIntNesting) (os_sched_lock_ints kernel))
      (tmr_stop_interrupt_rest external platform sg mask context kernel))
    (tmr_stop_context_rep external platform critical sg mask context kernel).
Proof.
  intros external platform critical sg mask context kernel heap
    [cell [rest [Hjoin [Hcell Hrest]]]].
  apply (proj2 (TimerCalleeLift.os_sched_closed_resources_lift
    external platform critical sg context mask kernel) heap).
  apply (TmrStopRules.lift_entailment _ _
    (TmrStopOldInterruptFields.context_rep_merge_interrupt
      external platform critical sg context mask kernel) heap).
  apply (proj2 (TmrStopRules.lift_sepcon _ _ heap)).
  exists cell, rest. split; [exact Hjoin|]. split; [|exact Hrest].
  exact (proj1 (TmrStopRules.store_uchar_lift sg.(g_OSIntNesting)
    (os_sched_lock_ints kernel)) cell Hcell).
Qed.

(** The upper bound comes from the real UChar cell, rather than the old
    interrupt_in_range predicate (which supplies only nonnegativity). *)
Lemma tmr_stop_interrupt_fields_facts : forall external platform sg mask context kernel,
  TmrStopRules.derivable1
    (TmrStopRules.sepcon
      (TmrStopRules.store_uchar sg.(g_OSIntNesting) (os_sched_lock_ints kernel))
      (tmr_stop_interrupt_rest external platform sg mask context kernel))
    (TmrStopRules.coq_prop
      (UCOS2_state_inv sg kernel /\ 0 <= os_sched_lock_ints kernel <= 255)).
Proof.
  intros external platform sg mask context kernel heap
    [cell [rest [Hjoin [Hcell Hrest]]]].
  destruct Hcell as [[Haddress [Hnonnegative Hupper]] Hbytes].
  destruct Hrest as [Hvalid Hresources].
  split; [exact Hvalid|]. split; [lia|].
  change (os_sched_lock_ints kernel <= 255) in Hupper. exact Hupper.
Qed.

(** The arbitrary product assertion [client] may depend on Gamma and may
    own an undefined output byte, a written byte, or other client resources.
    These lemmas neither inspect it nor allocate a second output cell. *)
Lemma tmr_stop_context_rep_split_interrupt_with_frame :
  forall external platform critical sg mask context kernel client,
  TmrStopRules.derivable1
    (TmrStopRules.sepcon
      (tmr_stop_context_rep external platform critical sg mask context kernel) client)
    (TmrStopRules.andp
      (TmrStopRules.coq_prop
        (UCOS2_state_inv sg kernel /\ 0 <= os_sched_lock_ints kernel <= 255))
      (TmrStopRules.sepcon
        (TmrStopRules.sepcon
          (TmrStopRules.store_uchar sg.(g_OSIntNesting) (os_sched_lock_ints kernel))
          (tmr_stop_interrupt_rest external platform sg mask context kernel)) client)).
Proof.
  intros external platform critical sg mask context kernel client heap
    [owned [framed [Hjoin [Hcontext Hclient]]]].
  pose proof (tmr_stop_context_rep_split_interrupt external platform critical sg
    mask context kernel owned Hcontext) as Hsplit.
  split.
  - exact (tmr_stop_interrupt_fields_facts external platform sg mask context
      kernel owned Hsplit).
  - exists owned, framed. split; [exact Hjoin|]. split; assumption.
Qed.

Lemma tmr_stop_context_rep_merge_interrupt_with_frame :
  forall external platform critical sg mask context kernel client,
  TmrStopRules.derivable1
    (TmrStopRules.sepcon
      (TmrStopRules.sepcon
        (TmrStopRules.store_uchar sg.(g_OSIntNesting) (os_sched_lock_ints kernel))
        (tmr_stop_interrupt_rest external platform sg mask context kernel)) client)
    (TmrStopRules.sepcon
      (tmr_stop_context_rep external platform critical sg mask context kernel) client).
Proof.
  intros external platform critical sg mask context kernel client heap
    [owned [framed [Hjoin [Hfields Hclient]]]].
  exists owned, framed. split; [exact Hjoin|]. split; [|exact Hclient].
  exact (tmr_stop_context_rep_merge_interrupt external platform critical sg
    mask context kernel owned Hfields).
Qed.
