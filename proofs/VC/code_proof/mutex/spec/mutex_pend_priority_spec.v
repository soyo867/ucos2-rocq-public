Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Local Open Scope Z_scope.

(** OSMutexPend in the selected nested-priority implementation.  The
    disabled ceiling is checked before either the scan or a table access.
    This is a source branch selector, with no validity assumption hidden
    in an execution guard. *)
Definition mutex_pend_inherit_action (disabled base current waiter ceiling : Z)
  : MutexDemandAction :=
  if Z.eqb ceiling disabled then NoMutexDemand
  else mutex_pend_demand_action base current waiter ceiling.

Lemma mutex_pend_demand_action_source : forall base current waiter ceiling,
  mutex_pend_demand_action base current waiter ceiling =
    if Z.ltb ceiling current then
      if Z.ltb waiter base then PromoteMutexOwner else NoMutexDemand
    else if (Z.ltb waiter base && Z.ltb ceiling base)%bool
         then RecordMutexDemand else NoMutexDemand.
Proof.
  intros; unfold mutex_pend_demand_action.
  destruct (Z.ltb ceiling current), (Z.ltb waiter base); reflexivity.
Qed.

Lemma mutex_pend_inherit_disabled : forall disabled base current waiter,
  mutex_pend_inherit_action disabled base current waiter disabled = NoMutexDemand.
Proof. intros; unfold mutex_pend_inherit_action; rewrite Z.eqb_refl; reflexivity. Qed.

Lemma mutex_pend_inherit_promote_iff : forall disabled base current waiter ceiling,
  mutex_pend_inherit_action disabled base current waiter ceiling = PromoteMutexOwner <->
  ceiling <> disabled /\ ceiling < current /\ waiter < base.
Proof.
  intros; unfold mutex_pend_inherit_action; rewrite mutex_pend_demand_action_source.
  destruct (Z.eqb ceiling disabled) eqn:Edisabled;
    destruct (Z.ltb ceiling current) eqn:Ecurrent;
    destruct (Z.ltb waiter base) eqn:Ewaiter;
    destruct (Z.ltb ceiling base) eqn:Ebase;
    cbn; apply Z.eqb_eq in Edisabled || apply Z.eqb_neq in Edisabled;
    apply Z.ltb_lt in Ecurrent || apply Z.ltb_ge in Ecurrent;
    apply Z.ltb_lt in Ewaiter || apply Z.ltb_ge in Ewaiter;
    apply Z.ltb_lt in Ebase || apply Z.ltb_ge in Ebase;
    split; intros; try discriminate; intuition lia.
Qed.

Lemma mutex_pend_inherit_record_iff : forall disabled base current waiter ceiling,
  mutex_pend_inherit_action disabled base current waiter ceiling = RecordMutexDemand <->
  ceiling <> disabled /\ current <= ceiling /\ waiter < base /\ ceiling < base.
Proof.
  intros; unfold mutex_pend_inherit_action; rewrite mutex_pend_demand_action_source.
  destruct (Z.eqb ceiling disabled) eqn:Edisabled;
    destruct (Z.ltb ceiling current) eqn:Ecurrent;
    destruct (Z.ltb waiter base) eqn:Ewaiter;
    destruct (Z.ltb ceiling base) eqn:Ebase;
    cbn; apply Z.eqb_eq in Edisabled || apply Z.eqb_neq in Edisabled;
    apply Z.ltb_lt in Ecurrent || apply Z.ltb_ge in Ecurrent;
    apply Z.ltb_lt in Ewaiter || apply Z.ltb_ge in Ewaiter;
    apply Z.ltb_lt in Ebase || apply Z.ltb_ge in Ebase;
    split; intros; try discriminate; intuition lia.
Qed.

Lemma mutex_pend_inherit_none_iff : forall disabled base current waiter ceiling,
  mutex_pend_inherit_action disabled base current waiter ceiling = NoMutexDemand <->
  ceiling = disabled \/
    (current <= ceiling /\ (base <= waiter \/ base <= ceiling)) \/
    (ceiling < current /\ base <= waiter).
Proof.
  intros; unfold mutex_pend_inherit_action; rewrite mutex_pend_demand_action_source.
  destruct (Z.eqb ceiling disabled) eqn:Edisabled;
    destruct (Z.ltb ceiling current) eqn:Ecurrent;
    destruct (Z.ltb waiter base) eqn:Ewaiter;
    destruct (Z.ltb ceiling base) eqn:Ebase;
    cbn; apply Z.eqb_eq in Edisabled || apply Z.eqb_neq in Edisabled;
    apply Z.ltb_lt in Ecurrent || apply Z.ltb_ge in Ecurrent;
    apply Z.ltb_lt in Ewaiter || apply Z.ltb_ge in Ewaiter;
    apply Z.ltb_lt in Ebase || apply Z.ltb_ge in Ebase;
    split; intros; try discriminate; intuition lia.
Qed.

(** Consume the actual BasePrio helper postcondition.  Its no-match
    fallback remains in the helper's raw contract; a real alias from the
    current kernel representation excludes that fallback here.  Neither
    a synthetic base-priority field nor the acquisition snapshot is used. *)
Lemma mutex_pend_base_scan_identifies_base :
  forall sg entries table owner pointer fallback result base,
  sg.(osLowestPrio) = 63 ->
  (forall p, 0 <= p < 64 ->
    (Znth p entries 0 = pointer <-> table p = PTTask owner)) ->
  task_base_priority sg table owner base ->
  mutex_base_priority_result entries pointer fallback result -> result = base.
Proof.
  intros sg entries table owner pointer fallback result base Hlowest Htable Hbase Hscan.
  apply (task_base_priority_unique sg table owner result base); [|exact Hbase].
  eapply mutex_base_priority_result_implies_task_base_priority;
    [exact Hlowest|exact Htable|exact (proj1 Hbase)|exact Hscan].
Qed.

Lemma mutex_pend_inherit_preserves_priority_extrema :
  forall sg table owner base current waiter ceiling,
  task_base_priority sg table owner base ->
  task_effective_priority sg table owner current ->
  (ceiling <> sg.(osPrioMutexCeilDis) -> task_priority_in_range sg ceiling) ->
  let action := mutex_pend_inherit_action sg.(osPrioMutexCeilDis)
    base current waiter ceiling in
  task_base_priority sg (mutex_demand_table action table owner ceiling) owner base /\
  task_effective_priority sg (mutex_demand_table action table owner ceiling) owner
    (mutex_demand_priority action current ceiling).
Proof.
  intros sg table owner base current waiter ceiling Hbase Hcurrent Hrange.
  unfold mutex_pend_inherit_action.
  destruct (Z.eqb ceiling sg.(osPrioMutexCeilDis)) eqn:E.
  - exact (conj Hbase Hcurrent).
  - apply mutex_pend_demand_preserves_priority_extrema; try assumption.
    apply Hrange; apply Z.eqb_neq; exact E.
Qed.

(** This is the native call-site consumer: the scan observation and the
    two actual C guards determine the new physical table/effective
    priority.  Validity is not a premise on the resulting state. *)
Lemma mutex_pend_base_scan_closes_demand :
  forall sg entries table owner pointer current result waiter ceiling base,
  sg.(osLowestPrio) = 63 ->
  (forall p, 0 <= p < 64 ->
    (Znth p entries 0 = pointer <-> table p = PTTask owner)) ->
  task_base_priority sg table owner base ->
  task_effective_priority sg table owner current ->
  task_priority_in_range sg ceiling ->
  mutex_base_priority_result entries pointer current result ->
  let action := mutex_pend_demand_action result current waiter ceiling in
  result = base /\
  task_base_priority sg (mutex_demand_table action table owner ceiling) owner base /\
  task_effective_priority sg (mutex_demand_table action table owner ceiling) owner
    (mutex_demand_priority action current ceiling).
Proof.
  intros sg entries table owner pointer current result waiter ceiling base
    Hlowest Htable Hbase Hcurrent Hceiling Hscan.
  assert (Hresult : result = base).
  { eapply mutex_pend_base_scan_identifies_base; eassumption. }
  subst result; split; [reflexivity|].
  apply mutex_pend_demand_preserves_priority_extrema; assumption.
Qed.

Lemma mutex_pend_demand_table_other : forall action table owner ceiling p,
  p <> ceiling -> mutex_demand_table action table owner ceiling p = table p.
Proof.
  intros action table owner ceiling p Hne; destruct action; cbn [mutex_demand_table];
    [reflexivity|apply update_prio_tbl_other; exact Hne|apply update_prio_tbl_other; exact Hne].
Qed.

Lemma mutex_pend_demand_preserves_foreign_aliases :
  forall sg action table owner ceiling tid p,
  tid <> owner -> table ceiling <> PTTask tid ->
  (task_priority_alias sg (mutex_demand_table action table owner ceiling) tid p <->
   task_priority_alias sg table tid p).
Proof.
  intros sg action table owner ceiling tid p Hne Hslot.
  destruct action; cbn [mutex_demand_table]; [reflexivity| |];
    apply task_priority_alias_foreign_write_iff; [exact Hslot|congruence|exact Hslot|congruence].
Qed.

Lemma mutex_pend_masked_demand_records_alias : forall table owner ceiling,
  mutex_demand_table RecordMutexDemand table owner ceiling ceiling = PTTask owner.
Proof. intros; apply update_prio_tbl_same. Qed.

Lemma mutex_pend_masked_demand_keeps_effective_priority : forall current ceiling,
  mutex_demand_priority RecordMutexDemand current ceiling = current.
Proof. reflexivity. Qed.
