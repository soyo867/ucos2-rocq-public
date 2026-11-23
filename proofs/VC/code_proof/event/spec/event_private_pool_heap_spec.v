Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_borrow_spec.
Import UCOS2_C_Rules EventStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These are actual selected-profile source fragments, not arbitrary
    environment frames. All other private ECBs remain in the same pool.
    A new ECB enters it only after the real free-root write has detached
    its bytes; one field store borrows and returns exactly its current
    image. The parametric pool algebra also serves the separate full92
    producers, but these selected-profile rules do not claim that case. *)
Lemma event_private_pool_detach_heap : forall sg state eid rest before (frame : Assertion),
  sem_create_source_binding sg ->
  state.(EventState).(unUsedEventStates) = eid :: rest ->
  (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists image after,
    state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image /\
    event_pool_addr sg eid <> 0 /\
    pointer_load sg.(g_OSEventFreeList) (event_pool_addr sg eid) before /\
    pointer_load (event_pool_addr sg eid + 4) (event_encode_pool_link sg (hd_error rest)) before /\
    kernel_heap_execution
      (pointer_store_writes sg.(g_OSEventFreeList) (event_encode_pool_link sg (hd_error rest)))
      before after /\
    event_create_allocate_critical state (Some (eid, image))
      (replace_EventS (event_detach_head state.(EventState) eid rest image) state) /\
    (kernel_program_inv sg (replace_EventS (event_detach_head state.(EventState) eid rest image) state) **
     event_private_pool_rep sg (event_detach_head state.(EventState) eid rest image) ** frame) after.
Proof.
  intros sg state eid rest before frame Hbinding Hhead Hpre.
  assert (Hvalid : UCOS2_state_inv sg state).
  { assert (Hget : kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame |--
      coq_prop (UCOS2_state_inv sg state)) by (unfold kernel_program_inv; entailer!).
    exact (Hget before Hpre). }
  assert (Hnone : state.(EventState).(eventLifecycle).(eventPrivate) eid = None).
  { pose proof Hvalid as [_ [_ [_ [[Hpartition _] _]]]].
    exact (proj2 (event_pool_free_unallocated sg state.(EventState) eid Hpartition
      ltac:(rewrite Hhead; simpl; auto))). }
  assert (Hopen : kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame |--
    kernel_program_inv sg state ** (event_private_pool_rep sg state.(EventState) ** frame)) by entailer!.
  destruct (event_create_detach_heap_resources sg state eid rest before
    (event_private_pool_rep sg state.(EventState) ** frame) Hbinding Hhead (Hopen before Hpre))
    as [image [after [Himage [Hnonzero [Hread [Hnext [Hwrite [Hstep Hafter]]]]]]]].
  assert (Hlookup : (event_detach_head state.(EventState) eid rest image).(eventLifecycle).(eventPrivate) eid =
    Some (sem_create_allocation_identity state image)) by apply kernel_map_set_same.
  assert (Hclose : event_private_storage_rep sg eid (sem_create_allocation_identity state image) **
      kernel_program_inv sg (replace_EventS (event_detach_head state.(EventState) eid rest image) state) **
      (event_private_pool_rep sg state.(EventState) ** frame) |--
    kernel_program_inv sg (replace_EventS (event_detach_head state.(EventState) eid rest image) state) **
      event_private_pool_rep sg (event_detach_head state.(EventState) eid rest image) ** frame).
  { sepcon_assoc_change.
    sep_apply_l_atomic (event_private_pool_merge_detached sg state.(EventState) eid rest image
      (sem_create_allocation_identity state image) Hnone Hlookup); entailer!. }
  exists image, after; split; [exact Himage|]. split; [exact Hnonzero|].
  split; [exact Hread|]. split; [exact Hnext|]. split; [exact Hwrite|].
  split; [exact Hstep|exact (Hclose after Hafter)].
Qed.

Lemma event_private_pool_allocate_heap : forall sg state before (frame : Assertion),
  sem_create_source_binding sg ->
  (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists result allocated after,
    pointer_load sg.(g_OSEventFreeList) (event_create_return_ptr sg result) before /\
    event_create_allocate_critical state result allocated /\
    (match result with
     | None => after = before
     | Some (eid, _) => event_pool_addr sg eid <> 0 /\ exists next,
         pointer_load (event_pool_addr sg eid + 4) next before /\
         kernel_heap_execution (pointer_store_writes sg.(g_OSEventFreeList) next) before after
     end) /\
    (kernel_program_inv sg allocated ** event_private_pool_rep sg allocated.(EventState) ** frame) after.
Proof.
  intros sg state before frame Hbinding Hpre.
  assert (Hopen : kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame |--
    kernel_program_inv sg state ** (event_private_pool_rep sg state.(EventState) ** frame)) by entailer!.
  destruct state.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
  - destruct (event_create_allocate_heap_source sg state before
      (event_private_pool_rep sg state.(EventState) ** frame) Hbinding (Hopen before Hpre))
      as [result [allocated [after [Hread [Hstep [Hrun Hafter]]]]]].
    unfold event_create_allocate_critical in Hstep; rewrite Hhead in Hstep.
    destruct Hstep as [-> ->]; cbn in Hrun; subst after.
    exists None, state, before; split; [exact Hread|].
    split; [unfold event_create_allocate_critical; rewrite Hhead; auto|].
    split; [reflexivity|exact Hpre].
  - destruct (event_private_pool_detach_heap sg state eid rest before frame Hbinding Hhead Hpre)
      as [image [after [Himage [Hnonzero [Hread [Hnext [Hwrite [Hstep Hafter]]]]]]]].
    exists (Some (eid, image)), (replace_EventS (event_detach_head state.(EventState) eid rest image) state), after.
    split; [exact Hread|]. split; [exact Hstep|]. split.
    + split; [exact Hnonzero|]. exists (event_encode_pool_link sg (hd_error rest)); split; assumption.
    + exact Hafter.
Qed.

Lemma event_private_pool_field_heap : forall sg state eid allocation field stored before (frame : Assertion),
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  event_create_field_value_in_range field stored ->
  (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists final after,
    (event_private_write state.(EventState) eid allocation field (Some stored)).(eventLifecycle).(eventPrivate)
      eid = Some final /\
    kernel_heap_execution (event_create_field_writes (event_pool_addr sg eid) field stored) before after /\
    (kernel_program_inv sg (replace_EventS
       (event_private_write state.(EventState) eid allocation field (Some stored)) state) **
     event_private_pool_rep sg (event_private_write state.(EventState) eid allocation field (Some stored)) **
     frame) after.
Proof.
  intros sg state eid allocation field stored before frame Hget Hfield Hrange Hpre.
  assert (Hopen : kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame |--
    event_private_storage_rep sg eid allocation ** kernel_program_inv sg state **
      (event_private_pool_missing_eid sg state.(EventState) eid ** frame)).
  { sepcon_assoc_change.
    sep_apply_l_atomic (event_private_pool_split_eid sg state.(EventState) eid allocation Hget); entailer!. }
  destruct (event_create_private_field_heap sg state eid allocation field stored before _
    Hget Hfield Hrange (Hopen before Hpre)) as [final [after [Hfinal [Hrun Hafter]]]].
  assert (Hclose : event_private_storage_rep sg eid final **
    kernel_program_inv sg (replace_EventS
      (event_private_write state.(EventState) eid allocation field (Some stored)) state) **
    (event_private_pool_missing_eid sg state.(EventState) eid ** frame) |--
    kernel_program_inv sg (replace_EventS
      (event_private_write state.(EventState) eid allocation field (Some stored)) state) **
    event_private_pool_rep sg (event_private_write state.(EventState) eid allocation field (Some stored)) ** frame).
  { sepcon_assoc_change.
    sep_apply_l_atomic (event_private_pool_merge_written sg state.(EventState) eid allocation field
      (Some stored) final Hfinal); entailer!. }
  exists final, after; split; [exact Hfinal|]. split; [exact Hrun|exact (Hclose after Hafter)].
Qed.

(** The entire uninterrupted source prefix is a composition of the actual
    per-field loans above. Interruptible prefixes are composed with their
    explicit interrupt/client edges instead of framing this pool across
    arbitrary Restore. *)
Lemma event_private_pool_prefix_heap : forall sg eid writes state allocation before (frame : Assertion),
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  Forall (fun write => In (fst write) (event_fields sg.(osKernelConfig).(cfgEventNames)) /\
    event_create_field_value_in_range (fst write) (snd write)) writes ->
  (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists final next after,
    event_create_private_stores eid writes state tt next /\
    next.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes (event_pool_addr sg eid) (fst write) (snd write)) writes)
      before after /\
    (kernel_program_inv sg next ** event_private_pool_rep sg next.(EventState) ** frame) after.
Proof.
  intros sg eid writes; induction writes as [|[field stored] rest IH];
    intros state allocation before frame Hget Hfields Hpre.
  - exists allocation, state, before; split; [split; reflexivity|].
    split; [exact Hget|]. split; [split; [constructor|split; reflexivity]|exact Hpre].
  - inversion Hfields as [|head tail [Hfield Hrange] Hrest]; subst.
    destruct (event_private_pool_field_heap sg state eid allocation field stored before frame
      Hget Hfield Hrange Hpre) as [middle_allocation [middle [Hlookup [Hwrite Hmiddle]]]].
    destruct (IH (replace_EventS
      (event_private_write state.(EventState) eid allocation field (Some stored)) state)
      middle_allocation middle frame Hlookup Hrest Hmiddle)
      as [final [next [after [Htail [Hfinal [Hrun Hafter]]]]]].
    exists final, next, after; split.
    + cbn [event_create_private_stores]; exists allocation; split; assumption.
    + split; [exact Hfinal|]. split; [|exact Hafter].
      cbn [flat_map fst snd]; eapply heap_execution_append; eassumption.
Qed.
