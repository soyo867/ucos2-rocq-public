Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_slot_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Provenance of the actual private image, not a public input restriction.
    The source tags are Mbox=1, Queue=2, Sem=3. Queue's separate QCB producer
    is still required by its source registration; this only describes the
    common ECB initializer prefix. The prefix may be empty at first Restore.
    Neither a raw address nor the public-map default supplies these facts. *)
Definition mutex_del_initializer_image sg eid allocation : Prop :=
  exists before allocated initialized image kind count pointer name prefix suffix,
    UCOS2_state_inv sg before /\
    event_create_allocate_critical before (Some (eid, image)) allocated /\
    (kind = 1 \/ kind = 2 \/ kind = 3) /\
    event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames)
      kind count pointer name = prefix ++ suffix /\
    event_create_private_stores eid prefix allocated tt initialized /\
    initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation.

Lemma mutex_del_initializer_image_type_non_mutex : forall sg eid allocation,
  mutex_del_initializer_image sg eid allocation ->
  exists observed, allocation.(eventPrivateStorage) EventTypeField = Some observed /\ observed <> 4.
Proof.
  intros sg eid allocation Hsource.
  destruct Hsource as [before [allocated [initialized [image [kind [count [pointer
    [name [prefix [suffix Hsource]]]]]]]]]].
  destruct Hsource as [Hvalid [Hallocate [Hkind [Hprefix [Hstores Hfinal]]]]].
  destruct (event_create_allocate_private_type_unused sg before eid image allocated Hvalid Hallocate)
    as [initial [Hinitial Htype]].
  destruct (event_create_initialization_prefix_type_non_mutex eid
    sg.(osKernelConfig).(cfgEventNames) kind count pointer name prefix suffix allocated tt initialized
    initial 0 ltac:(lia) Hprefix Hinitial Htype ltac:(lia) Hstores)
    as [final [observed [Hget [Hvalue Hnot]]]].
  assert (final = allocation) by congruence; subst final; exists observed; split; assumption.
Qed.

(** This logical observation names the actual byte source. The private
    alternative does not use the public map's default Type. *)
Definition mutex_del_recheck_observation sg eid state observed : Prop :=
  (exists event, sem_query_public_slot state eid event /\
    observed = event_slot_type_value state.(EventState) eid) \/
  (exists allocation,
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    allocation.(eventPrivateStorage) EventTypeField = Some observed /\
    mutex_del_initializer_image sg eid allocation).

(** The residual distinguishes a public slot from an actually borrowed
    creator image. It owns no Type byte. Both alternatives retain the ONE
    program table. A currently owned context and whole continuation map
    remain an ordinary frame through this MASKED byte read only. No
    frame-through-Restore law is asserted here. *)
Definition mutex_del_recheck_residual sg pointer eid state observed : Assertion :=
  (EX event,
    coq_prop (UCOS2_state_inv sg state /\ pointer = event_addr sg eid /\
      sem_query_public_slot state eid event /\ observed = event_slot_type_value state.(EventState) eid) &&
    (sem_query_type_frame sg state eid ** unmap_table_rep sg)) ||
  (EX allocation,
    coq_prop (pointer = event_pool_addr sg eid /\
      state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      allocation.(eventPrivateStorage) EventTypeField = Some observed /\
      mutex_del_initializer_image sg eid allocation) &&
    (kernel_program_inv sg state **
      event_private_storage_without_type sg eid allocation)).

Definition mutex_del_recheck_type_rep sg pointer eid state : Assertion :=
  EX observed, pointer # UChar |-> observed **
    mutex_del_recheck_residual sg pointer eid state observed.

(** This stage is handed back to the actual Restore/client composition.
    A private ECB is not dropped or converted to a public slot on the error
    edge. The later source execution may publish it and must return its real
    current cut, not an assertion indexed by this release snapshot. *)
Definition mutex_del_recheck_whole sg pointer eid state : Assertion :=
  (EX event,
    coq_prop (pointer = event_addr sg eid /\ sem_query_public_slot state eid event) &&
    kernel_program_inv sg state) ||
  (EX allocation,
    coq_prop (pointer = event_pool_addr sg eid /\
      state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      mutex_del_initializer_image sg eid allocation) &&
    (kernel_program_inv sg state ** event_private_storage_rep sg eid allocation)).

Lemma mutex_del_recheck_public_split : forall sg pointer eid state event,
  pointer = event_addr sg eid -> sem_query_public_slot state eid event ->
  kernel_program_inv sg state |--
    pointer # UChar |-> event_slot_type_value state.(EventState) eid **
    mutex_del_recheck_residual sg pointer eid state
      (event_slot_type_value state.(EventState) eid).
Proof.
  intros sg pointer eid state event Hpointer Hslot.
  assert (Hopen : kernel_program_inv sg state |--
      coq_prop (UCOS2_state_inv sg state) &&
      (pointer # UChar |-> event_slot_type_value state.(EventState) eid **
       (sem_query_type_frame sg state eid ** unmap_table_rep sg))).
  { rewrite kernel_program_inv_split_unmap.
    sep_apply_l_atomic (sem_query_type_split_full sg state eid event Hslot).
    unfold OSEventType_off; rewrite Z.add_0_r, <- Hpointer; entailer!. }
  intros heap Hpre; destruct (Hopen heap Hpre) as [Hvalid [owned [rest [Hjoin [Htype Hrest]]]]].
  exists owned, rest; split; [exact Hjoin|]. split; [exact Htype|].
  left; exists event; split; [exact (conj Hvalid (conj Hpointer (conj Hslot eq_refl)))|exact Hrest].
Qed.

Lemma mutex_del_recheck_private_split : forall sg pointer eid state allocation,
  pointer = event_pool_addr sg eid ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  mutex_del_initializer_image sg eid allocation ->
  kernel_program_inv sg state ** event_private_storage_rep sg eid allocation |--
    mutex_del_recheck_type_rep sg pointer eid state.
Proof.
  intros sg pointer eid state allocation Hpointer Hget Hsource.
  destruct (mutex_del_initializer_image_type_non_mutex sg eid allocation Hsource) as [observed [Htype Hnot]].
  assert (Hopen : kernel_program_inv sg state ** event_private_storage_rep sg eid allocation |--
      pointer # UChar |-> observed **
        (kernel_program_inv sg state ** event_private_storage_without_type sg eid allocation)).
  { sep_apply_l_atomic (event_private_storage_rep_split_type sg eid allocation observed Htype).
    rewrite Hpointer; entailer!. }
  intros heap Hpre; exists observed.
  destruct (Hopen heap Hpre) as [owned [rest [Hjoin [Hcell Hrest]]]].
  exists owned, rest; split; [exact Hjoin|]. split; [exact Hcell|].
  right; exists allocation; split; [exact (conj Hpointer (conj Hget (conj Htype Hsource)))|exact Hrest].
Qed.

Lemma mutex_del_recheck_split_type : forall sg pointer eid state,
  mutex_del_recheck_whole sg pointer eid state |-- mutex_del_recheck_type_rep sg pointer eid state.
Proof.
  intros sg pointer eid state heap [Hpublic|Hprivate].
  - destruct Hpublic as [event [[Hpointer Hslot] Hworld]].
    exists (event_slot_type_value state.(EventState) eid).
    exact (mutex_del_recheck_public_split sg pointer eid state event Hpointer Hslot heap Hworld).
  - destruct Hprivate as [allocation [[Hpointer [Hget Hsource]] Hworld]].
    exact (mutex_del_recheck_private_split sg pointer eid state allocation Hpointer Hget Hsource heap Hworld).
Qed.

Lemma mutex_del_recheck_merge_type : forall sg pointer eid state observed,
  pointer # UChar |-> observed ** mutex_del_recheck_residual sg pointer eid state observed |--
    coq_prop (mutex_del_recheck_observation sg eid state observed) &&
    mutex_del_recheck_whole sg pointer eid state.
Proof.
  intros sg pointer eid state observed heap
    [owned [rest [Hjoin [Hcell [Hpublic|Hprivate]]]]].
  - destruct Hpublic as [event [[Hvalid [Hpointer [Hslot Hvalue]]] Hrest]].
    split; [left; exists event; split; assumption|].
    left; exists event; split; [split; assumption|].
    assert (Hmerge : pointer # UChar |-> observed **
        (sem_query_type_frame sg state eid ** unmap_table_rep sg) |--
        kernel_program_inv sg state).
    { rewrite Hpointer, Hvalue.
      replace (event_addr sg eid) with (event_addr sg eid + OSEventType_off) at 1 by
        (unfold OSEventType_off; lia).
      sep_apply_l_atomic (sem_query_type_merge_full sg state eid Hvalid).
      rewrite kernel_program_inv_split_unmap; entailer!. }
    apply Hmerge; exists owned, rest; split; [exact Hjoin|split; assumption].
  - destruct Hprivate as [allocation [[Hpointer [Hget [Htype Hsource]]] Hrest]].
    split; [right; exists allocation; exact (conj Hget (conj Htype Hsource))|].
    right; exists allocation; split; [exact (conj Hpointer (conj Hget Hsource))|].
    assert (Hmerge : pointer # UChar |-> observed **
        (kernel_program_inv sg state ** event_private_storage_without_type sg eid allocation) |--
        kernel_program_inv sg state ** event_private_storage_rep sg eid allocation).
    { rewrite Hpointer; sep_apply_l_atomic (event_private_storage_rep_merge_type sg eid allocation observed Htype).
      entailer!. }
    apply Hmerge; exists owned, rest; split; [exact Hjoin|split; assumption].
Qed.

(** Type=4 itself rules out precisely the three actual creator-prefix
    cases, not arbitrary private storage. The independent owner-use protocol
    is intentionally not manufactured by this success-side observation. *)
Lemma mutex_del_recheck_mutex_public : forall sg pointer eid state,
  pointer # UChar |-> 4 ** mutex_del_recheck_residual sg pointer eid state 4 |--
    EX event, coq_prop (pointer = event_addr sg eid /\ sem_query_public_slot state eid event /\
      event_slot_type_value state.(EventState) eid = 4) &&
      kernel_program_inv sg state.
Proof.
  intros sg pointer eid state heap [owned [rest [Hjoin [Hcell [Hpublic|Hprivate]]]]].
  - destruct Hpublic as [event [[Hvalid [Hpointer [Hslot Htype]]] Hrest]].
    exists event; split; [exact (conj Hpointer (conj Hslot (eq_sym Htype)))|].
    assert (Hmerge : pointer # UChar |-> 4 **
        (sem_query_type_frame sg state eid ** unmap_table_rep sg) |--
        kernel_program_inv sg state).
    { rewrite Hpointer, Htype.
      replace (event_addr sg eid) with (event_addr sg eid + OSEventType_off) at 1 by
        (unfold OSEventType_off; lia).
      sep_apply_l_atomic (sem_query_type_merge_full sg state eid Hvalid).
      rewrite kernel_program_inv_split_unmap; entailer!. }
    apply Hmerge; exists owned, rest; split; [exact Hjoin|split; assumption].
  - destruct Hprivate as [allocation [[Hpointer [Hget [Htype Hsource]]] Hrest]].
    destruct (mutex_del_initializer_image_type_non_mutex sg eid allocation Hsource) as [value [Hvalue Hnot]].
    assert (value = 4) by congruence; contradiction.
Qed.
