Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_slot_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Import UCOS2_C_Rules EventStateDef ListNotations KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The numerical pointer and actual private lookup select one existing
    allocation. This equivalence does not obtain private memory from the
    program invariant, a lifecycle tag, or a default Type projection. *)
Lemma mutex_del_creator_heap_resources_equiv_private_storage :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg pointer state eid allocation,
  pointer = event_pool_addr sg eid ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  mutex_del_creator_heap_resources abi sg pointer state --||--
    kernel_client_heap_world abi sg state ** event_private_storage_rep sg eid allocation.
Proof.
  intros external platform port abi sg pointer state eid allocation Hpointer Hget.
  split.
  - unfold mutex_del_creator_heap_resources; Intros found current.
    assert (Hbindings : pointer = event_pool_addr sg found /\
      state.(EventState).(eventLifecycle).(eventPrivate) found = Some current) by tauto.
    destruct Hbindings as [Haddress Hcurrent].
    assert (found = eid) by (apply event_pool_addr_injective with (sg := sg); congruence).
    subst found; assert (current = allocation) by congruence; subst current; entailer!.
  - unfold mutex_del_creator_heap_resources; Exists eid allocation; entailer!.
Qed.

(** One source field is the singleton prefix. Longer prefixes are
    uninterrupted source stores, never a frame rule across Restore. The
    whole successor capsule map is reindexed by the proved Task frame. *)
Lemma mutex_del_creator_prefix_heap_resources :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg pointer state eid allocation writes before (frame : Assertion),
  pointer = event_pool_addr sg eid ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  Forall (fun write => In (fst write) (event_fields sg.(osKernelConfig).(cfgEventNames)) /\
    event_create_field_value_in_range (fst write) (snd write)) writes ->
  (mutex_del_creator_heap_resources abi sg pointer state ** frame) before ->
  exists next after,
    event_create_private_stores eid writes state tt next /\
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes pointer (fst write) (snd write)) writes)
      before after /\
    (mutex_del_creator_heap_resources abi sg pointer next ** frame) after.
Proof.
  intros external platform port abi sg pointer state eid allocation writes before frame
    Hpointer Hget Hfields Hpre.
  assert (Hopen : mutex_del_creator_heap_resources abi sg pointer state ** frame |--
    event_private_storage_rep sg eid allocation ** kernel_program_inv sg state **
      (armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame)).
  { sep_apply_l_atomic (proj1 (mutex_del_creator_heap_resources_equiv_private_storage
      external platform port abi sg pointer state eid allocation Hpointer Hget)).
    unfold kernel_client_heap_world; entailer!. }
  destruct (event_create_private_prefix_heap sg eid writes state allocation before
    (armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame)
    Hget Hfields (Hopen before Hpre)) as [final [next [after [Hrun [Hlookup [Hexecution Hafter]]]]]].
  assert (Htasks : next.(TskState) = state.(TskState)).
  { pose proof (event_create_private_stores_published_frame eid writes state tt next Hrun); tauto. }
  exists next, after; split; [exact Hrun|]. split.
  - rewrite Hpointer; exact Hexecution.
  - assert (Hclose : event_private_storage_rep sg eid final ** kernel_program_inv sg next **
      (armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame) |--
      mutex_del_creator_heap_resources abi sg pointer next ** frame).
    { unfold mutex_del_creator_heap_resources; Exists eid final.
      unfold kernel_client_heap_world; rewrite Htasks; entailer!. }
    exact (Hclose after Hafter).
Qed.

(** Same-cut borrow: the Type byte is absent from this residual. All other
    private bytes, the actual allocation lookup, the one program/table
    owner and the WHOLE current capsule map are retained. The remembered
    value permits original-value return only, not a Type update. *)
Definition mutex_del_creator_type_residual {external platform port}
  (abi : Armv7aContinuationABI external platform port) sg pointer state observed : Assertion :=
  EX eid allocation,
    coq_prop (pointer = event_pool_addr sg eid /\
      state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      allocation.(eventPrivateStorage) EventTypeField = Some observed) &&
    (kernel_client_heap_world abi sg state ** event_private_storage_without_type sg eid allocation).

Lemma mutex_del_creator_heap_resources_split_type :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg pointer state eid allocation observed,
  pointer = event_pool_addr sg eid ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateStorage) EventTypeField = Some observed ->
  mutex_del_creator_heap_resources abi sg pointer state |--
    pointer # UChar |-> observed ** mutex_del_creator_type_residual abi sg pointer state observed.
Proof.
  intros external platform port abi sg pointer state eid allocation observed Hpointer Hget Htype.
  sep_apply_l_atomic (proj1 (mutex_del_creator_heap_resources_equiv_private_storage
    external platform port abi sg pointer state eid allocation Hpointer Hget)).
  sep_apply_l_atomic (event_private_storage_rep_split_type sg eid allocation observed Htype).
  unfold mutex_del_creator_type_residual; Exists eid allocation.
  rewrite Hpointer; entailer!.
Qed.

Lemma mutex_del_creator_heap_resources_merge_type :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg pointer state observed,
  pointer # UChar |-> observed ** mutex_del_creator_type_residual abi sg pointer state observed |--
    mutex_del_creator_heap_resources abi sg pointer state.
Proof.
  intros external platform port abi sg pointer state observed.
  unfold mutex_del_creator_type_residual; Intros eid allocation.
  assert (Hbindings : pointer = event_pool_addr sg eid /\
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    allocation.(eventPrivateStorage) EventTypeField = Some observed) by tauto.
  destruct Hbindings as [Hpointer [Hget Htype]].
  rewrite Hpointer.
  sep_apply_l_atomic (event_private_storage_rep_merge_type sg eid allocation observed Htype).
  unfold mutex_del_creator_heap_resources; Exists eid allocation; entailer!.
Qed.

(** An actual protected uchar load followed by original-value return.
    The heap is the supplied acquired heap on both sides. No later Restore,
    perr store, caller resumption or lifetime across an open call is claimed. *)
Lemma mutex_del_creator_type_load_return :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg pointer state observed heap (frame : Assertion),
  (pointer # UChar |-> observed **
   mutex_del_creator_type_residual abi sg pointer state observed ** frame) heap ->
  uchar_load pointer observed heap /\
    (mutex_del_creator_heap_resources abi sg pointer state ** frame) heap.
Proof.
  intros external platform port abi sg pointer state observed heap frame Hpre.
  assert (Hload : pointer # UChar |-> observed **
      mutex_del_creator_type_residual abi sg pointer state observed ** frame |--
    pointer # UChar |-> observed **
      (mutex_del_creator_type_residual abi sg pointer state observed ** frame)) by entailer!.
  split.
  - exact (framed_uchar_store_load pointer observed _ heap (Hload heap Hpre)).
  - assert (Hclose : pointer # UChar |-> observed **
        mutex_del_creator_type_residual abi sg pointer state observed ** frame |--
      mutex_del_creator_heap_resources abi sg pointer state ** frame).
    { sep_apply_l_atomic (mutex_del_creator_heap_resources_merge_type
        external platform port abi sg pointer state observed); entailer!. }
    exact (Hclose heap Hpre).
Qed.

(** Real Sem/Mbox/Queue initializer prefixes, starting from the actual
    detached UNUSED byte. The source list establishes non-Mutex, and the
    heap producer supplies the readable byte; neither is substituted for
    the other. Repaired Mutex Type-last order is deliberately not this list. *)
Lemma mutex_del_creator_initialization_prefix_type_loan :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg pointer state eid allocation kind count payload name prefix remaining before (frame : Assertion),
  pointer = event_pool_addr sg eid ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateStorage) EventTypeField = Some 0 ->
  (kind = 1 \/ kind = 2 \/ kind = 3) ->
  0 <= count < 65536 -> 0 <= payload < 4294967296 -> 0 <= name < 4294967296 ->
  event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames) kind count payload name =
    prefix ++ remaining ->
  (mutex_del_creator_heap_resources abi sg pointer state ** frame) before ->
  exists next after observed,
    event_create_private_stores eid prefix state tt next /\
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes pointer (fst write) (snd write)) prefix)
      before after /\
    observed <> 4 /\
    (pointer # UChar |-> observed **
      mutex_del_creator_type_residual abi sg pointer next observed ** frame) after.
Proof.
  intros external platform port abi sg pointer state eid allocation kind count payload name
    prefix remaining before frame Hpointer Hget Htype Hkind Hcount Hpayload Hname Hprefix Hpre.
  assert (Hkind_range : 0 <= kind < 256) by lia.
  assert (Hnot_mutex : kind <> 4) by lia.
  pose proof (event_create_initialization_fields_in_range sg.(osKernelConfig).(cfgEventNames)
    kind count payload name Hkind_range Hcount Hpayload Hname) as Hall.
  rewrite Hprefix in Hall; apply Forall_app in Hall; destruct Hall as [Hfields _].
  destruct (mutex_del_creator_prefix_heap_resources external platform port abi sg pointer state
    eid allocation prefix before frame Hpointer Hget Hfields Hpre)
    as [next [after [Hrun [Hexecution Hafter]]]].
  destruct (event_create_initialization_prefix_type_non_mutex eid sg.(osKernelConfig).(cfgEventNames)
    kind count payload name prefix remaining state tt next allocation 0 Hnot_mutex Hprefix
    Hget Htype ltac:(lia) Hrun) as [final [observed [Hlookup [Hobserved Hnonmutex]]]].
  exists next, after, observed; split; [exact Hrun|]. split; [exact Hexecution|].
  split; [exact Hnonmutex|].
  assert (Hloan : mutex_del_creator_heap_resources abi sg pointer next ** frame |--
    pointer # UChar |-> observed **
      mutex_del_creator_type_residual abi sg pointer next observed ** frame).
  { sep_apply_l_atomic (mutex_del_creator_heap_resources_split_type
      external platform port abi sg pointer next eid final observed Hpointer Hlookup Hobserved); entailer!. }
  exact (Hloan after Hafter).
Qed.
