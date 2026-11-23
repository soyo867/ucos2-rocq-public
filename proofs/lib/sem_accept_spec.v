Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import AUXLib.ListLib.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.memory.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.statistics.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.ucos2_verify_inv.

Import ListNotations.
Import UCOS2_C_Rules.
Import EventStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Full frame retained by OSSemAccept after focusing one Event.  This is
    the complement of the focused Event storage and queue-independent module
    owners; it is deliberately concrete so the public annotation cannot
    replace the full invariant by a verification slice. *)
Definition sem_accept_raw_frame
  (sg : StableGlobVars) (s : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  event_raw_rep_no_eid sg s.(TskState) s.(EventState) eid **
  queue_storage_rep sg s.(EventState) **
  store_parked_stacks s.(TskState).(parkedTaskStacks) **
  flag_configured_rep sg s.(FlagState) **
  memory_configured_rep sg s.(MemoryState) **
  timer_configured_rep sg s.(TimerState) **
  statistics_rep sg s.(StatsState) **
  kernel_control_rep sg s.(ControlState) **
  store_name_bytes s.(NameState).

Definition sem_accept_event_rest_fields_full (named : bool) : list EventField :=
  remove EventField_eq_dec EventCntField
    (remove EventField_eq_dec EventPtrField
      (remove EventField_eq_dec EventTypeField (event_fields named))).

Definition sem_accept_event_rest_storage_full
  (named : bool) (base : addr) (image : EventStorage) : Assertion :=
  EventFieldStorage.store_fields EventField_eq_dec (event_cell base)
    (sem_accept_event_rest_fields_full named) image.

Definition sem_accept_event_rest_full
  (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (eid : EventID) (e : OSEventAbstractState) : Assertion :=
  sem_accept_event_rest_storage_full sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg tasks e).

Lemma sem_accept_event_fields_reorder_full : forall named base image,
  event_storage_rep named base image =
  EventFieldStorage.store_fields EventField_eq_dec (event_cell base)
    (EventTypeField :: EventPtrField :: EventCntField ::
      sem_accept_event_rest_fields_full named) image.
Proof.
  intros named base image; unfold event_storage_rep,
    EventFieldStorage.store_fields.
  f_equal; apply functional_extensionality; intro field.
  destruct named, field; reflexivity.
Qed.

Lemma sem_accept_event_fields_nodup_full : forall named,
  NoDup (EventTypeField :: EventPtrField :: EventCntField ::
    remove EventField_eq_dec EventCntField
      (remove EventField_eq_dec EventPtrField
        (remove EventField_eq_dec EventTypeField (event_fields named)))).
Proof.
  intros []; unfold event_fields; simpl.
  all: repeat (apply NoDup_cons; [simpl; intuition discriminate|]).
  all: apply NoDup_nil.
Qed.

Lemma sem_accept_event_storage_merge_updated_count_full :
  forall named base image count,
  event_cell base EventTypeField (image EventTypeField) **
  event_cell base EventPtrField (image EventPtrField) **
  event_cell base EventCntField (Some count) **
  sem_accept_event_rest_storage_full named base image |--
  event_storage_rep named base (event_write image EventCntField (Some count)).
Proof.
  intros named base image count.
  rewrite sem_accept_event_fields_reorder_full.
  pose proof (sem_accept_event_fields_nodup_full named) as Htype.
  pose proof Htype as Hptr; apply NoDup_cons_iff in Hptr; destruct Hptr as [_ Hptr].
  pose proof Hptr as Hcnt; apply NoDup_cons_iff in Hcnt; destruct Hcnt as [_ Hcnt].
  rewrite (EventFieldStorage.store_fields_cons _ _ EventField_eq_dec
    (event_cell base) _ (event_write image EventCntField (Some count)) EventTypeField Htype).
  rewrite (EventFieldStorage.store_fields_cons _ _ EventField_eq_dec
    (event_cell base) _ (event_write image EventCntField (Some count)) EventPtrField Hptr).
  rewrite (EventFieldStorage.store_fields_cons _ _ EventField_eq_dec
    (event_cell base) _ (event_write image EventCntField (Some count)) EventCntField Hcnt).
  unfold sem_accept_event_rest_storage_full.
  unfold event_write.
  rewrite EventFieldStorage.store_fields_update_unlisted by
    (unfold sem_accept_event_rest_fields_full; apply remove_In).
  cbn [field_storage.field_update EventField_eq_dec].
  entailer!.
Qed.

Lemma sem_accept_event_storage_merge_full :
  forall named base image,
  event_cell base EventTypeField (image EventTypeField) **
  event_cell base EventPtrField (image EventPtrField) **
  event_cell base EventCntField (image EventCntField) **
  sem_accept_event_rest_storage_full named base image |--
  event_storage_rep named base image.
Proof.
  intros named base image.
  rewrite sem_accept_event_fields_reorder_full.
  pose proof (sem_accept_event_fields_nodup_full named) as Htype.
  pose proof Htype as Hptr; apply NoDup_cons_iff in Hptr; destruct Hptr as [_ Hptr].
  pose proof Hptr as Hcnt; apply NoDup_cons_iff in Hcnt; destruct Hcnt as [_ Hcnt].
  rewrite (EventFieldStorage.store_fields_cons _ _ EventField_eq_dec
    (event_cell base) _ image EventTypeField Htype).
  rewrite (EventFieldStorage.store_fields_cons _ _ EventField_eq_dec
    (event_cell base) _ image EventPtrField Hptr).
  rewrite (EventFieldStorage.store_fields_cons _ _ EventField_eq_dec
    (event_cell base) _ image EventCntField Hcnt).
  unfold sem_accept_event_rest_storage_full.
  entailer!.
Qed.

Lemma sem_accept_event_rep_merge_updated_count_full :
  forall sg tasks eid e count,
    e.(eventType) = OS_EVENT_TYPE_SEM ->
    (event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type e.(eventType) **
    (event_addr sg eid + OSEventPtr_off) # Ptr |-> encode_event_ptr_value sg e **
    (event_addr sg eid + OSEventCnt_off) # UShort |-> count **
    sem_accept_event_rest_full sg tasks eid e |--
    used_event_rep sg tasks eid (sem_set_count e count).
Proof.
  intros sg tasks eid e count Hsem.
  unfold used_event_rep, sem_accept_event_rest_full.
  rewrite sem_set_count_image_eq by exact Hsem.
  change
    (event_cell (event_addr sg eid) EventTypeField
       ((event_image sg tasks e) EventTypeField) **
     event_cell (event_addr sg eid) EventPtrField
       ((event_image sg tasks e) EventPtrField) **
     event_cell (event_addr sg eid) EventCntField (Some count) **
     sem_accept_event_rest_storage_full (cfgEventNames (osKernelConfig sg))
       (event_addr sg eid) (event_image sg tasks e) |--
     event_storage_rep (cfgEventNames (osKernelConfig sg))
       (event_addr sg eid)
       (event_write (event_image sg tasks e) EventCntField (Some count))).
  apply sem_accept_event_storage_merge_updated_count_full.
Qed.

Lemma sem_accept_event_rep_merge_full :
  forall sg tasks eid e,
    (event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type e.(eventType) **
    (event_addr sg eid + OSEventPtr_off) # Ptr |-> encode_event_ptr_value sg e **
    (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value e **
    sem_accept_event_rest_full sg tasks eid e |--
    used_event_rep sg tasks eid e.
Proof.
  intros sg tasks eid e.
  unfold used_event_rep, sem_accept_event_rest_full.
  change
    (event_cell (event_addr sg eid) EventTypeField
       ((event_image sg tasks e) EventTypeField) **
     event_cell (event_addr sg eid) EventPtrField
       ((event_image sg tasks e) EventPtrField) **
     event_cell (event_addr sg eid) EventCntField
       ((event_image sg tasks e) EventCntField) **
     sem_accept_event_rest_storage_full sg.(osKernelConfig).(cfgEventNames)
       (event_addr sg eid) (event_image sg tasks e) |--
     event_storage_rep sg.(osKernelConfig).(cfgEventNames)
       (event_addr sg eid) (event_image sg tasks e)).
  apply sem_accept_event_storage_merge_full.
Qed.

(* Current-profile snapshot used only by OSSemAccept.  It follows the same
   pointer and wait-table encoders as [event_image], so Mutex owners use the
   configured Task slot address instead of the legacy 68-byte slice address. *)
Definition sem_accept_current_snapshot_of_prop
  (sg : StableGlobVars) (tskSt : Glob_TaskAbstractState)
  (evSt : Glob_EventAbstractState) (eid : EventID)
  (e : OSEventAbstractState) (etype ecnt eptr egrp : Z) (etbl : list Z) : Prop :=
  evSt.(inUsedEventStates) eid = Some e /\
  etype = encode_event_type e.(eventType) /\
  ecnt = encode_event_cnt_value e /\
  eptr = encode_event_ptr_value sg e /\
  egrp = encode_event_wait_grp e.(waitList) tskSt /\
  etbl = encode_event_wait_tbl_values_or e tskSt.

(* Exact L5 transformer for the single concrete OSEventCnt write performed
   by OSSemAccept.  The event identity, type, payload alternatives and wait
   state are copied verbatim; only the semaphore payload count changes. *)
Definition sem_accept_event_with_count
  (e : OSEventAbstractState) (cnt : Z) : OSEventAbstractState :=
  {| eventGeneration := e.(eventGeneration);
     eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
     eventType   := e.(eventType);
     mutexFields := e.(mutexFields);
     semFields   := Some {| semCount := cnt |};
     mboxFields  := e.(mboxFields);
     queueFields := e.(queueFields);
     waitList    := e.(waitList) |}.

Definition sem_accept_event_state_update
  (evSt : Glob_EventAbstractState) (eid : EventID)
  (e : OSEventAbstractState) (cnt : Z) : Glob_EventAbstractState :=
  update_event_field_raw evSt eid (sem_accept_event_with_count e cnt).

Lemma sem_accept_update_event_field_raw_same : forall evSt eid e,
  evSt.(inUsedEventStates) eid = Some e ->
  update_event_field_raw evSt eid e = evSt.
Proof.
  intros [used unused published lifecycle] eid e Hlookup; simpl in Hlookup |- *.
  unfold update_event_field_raw. f_equal.
  apply functional_extensionality; intro eid'.
  destruct (Z.eqb eid' eid) eqn:Heq;
    [apply Z.eqb_eq in Heq; subst; symmetry; exact Hlookup|reflexivity].
Qed.

Lemma sem_accept_event_with_count_eq_sem_set_count : forall e count,
  sem_accept_event_with_count e count = sem_set_count e count.
Proof. intros; destruct e; reflexivity. Qed.

Definition sem_accept_post_state
  (ls0 : UCOS2_Verify_State) (eid : EventID)
  (e : OSEventAbstractState) (cnt : Z) : UCOS2_Verify_State :=
  replace_EventS
    (sem_accept_event_state_update ls0.(EventState) eid e cnt) ls0.

Lemma sem_accept_post_state_eq_sem_count_update_state : forall s eid e count,
  sem_accept_post_state s eid e count = sem_count_update_state s eid e count.
Proof.
  intros; unfold sem_accept_post_state, sem_count_update_state,
    sem_accept_event_state_update.
  rewrite sem_accept_event_with_count_eq_sem_set_count; reflexivity.
Qed.

(* Source-faithful, ordered public semantics.  The nullable arm precedes
   every dereference.  A non-semaphore event returns zero unchanged.  A
   semaphore returns its entry count and decrements exactly when positive. *)
Definition OSSemAccept_sem
  (sg : StableGlobVars) (pevent : addr)
  : program UCOS2_Verify_State Z :=
  fun ls0 ret ls1 =>
    (pevent = 0 /\ ret = 0 /\ ls1 = ls0) \/
    (pevent <> 0 /\
     exists eid e,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) <> OS_EVENT_TYPE_SEM /\
       ret = 0 /\ ls1 = ls0) \/
    (pevent <> 0 /\
     exists eid e sf,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       sf.(semCount) = 0 /\
       ret = 0 /\ ls1 = ls0) \/
    (pevent <> 0 /\
     exists eid e sf,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       0 < sf.(semCount) /\
       ret = sf.(semCount) /\
       ls1 = sem_accept_post_state ls0 eid e (sf.(semCount) - 1)).

(* Annotation-facing relational view.  QCP treats [program] abstractly in
   Extern Coq types, so the public post is exposed as an ordinary Prop. *)
Definition sem_accept_public_post_prop
  (sg : StableGlobVars) (pevent : addr)
  (ls0 : UCOS2_Verify_State) (ret : Z) (ls1 : UCOS2_Verify_State) : Prop :=
  OSSemAccept_sem sg pevent ls0 ret ls1.

(* The public return observation is exact INT16U data, not a boolean
   availability observer. *)
Definition observe_sem_accept_count
  (cnt : Z) : program (UCOS2_Verify_State -> Prop) Z :=
  StateRelMonad.ret cnt.

(* Critical-section endpoint used by the annotated Restore contract.  Entry
   to the critical section itself does not change the kernel state.  Exit
   commits exactly the count update selected by the source branch. *)
Definition sem_accept_restore_transition_prop
  (ls0 ls_inside ls_restored : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) (entry_count : Z) : Prop :=
  crit_rel_event_only ls_inside ls_restored /\
  ls_restored =
    if Z.ltb 0 entry_count
    then sem_accept_post_state ls0 eid e (entry_count - 1)
    else ls0.

Lemma atomic_count_observer_safe_return__sem_accept_returns_and_focus :
  forall (c : program UCOS2_Verify_State Z) ls0 ls2 count X,
    c ls0 count ls2 ->
    safeExec (LastSeen ls0)
      (bind (atomic_cmd c) observe_sem_accept_count) X ->
    safeExec (LastSeen ls2) (StateRelMonad.ret count) X.
Proof.
  intros c ls0 ls2 count X Hsem Hexec.
  assert (Hatomic : hs_eval (atomic_cmd c)
    (LastSeen ls0) (LastSeen ls2) count).
  {
    unfold hs_eval, LastSeen, atomic_cmd.
    intros P0 HP0.
    exists (RTrans_Abs ls2).
    split.
    - exists ls0, ls2.
      split; [apply HP0; exact I |].
      split; [exact Hsem | intro state; split; trivial].
    - intro state; split; trivial.
  }
  exact (highstepbind_derive _ _ _ count (LastSeen ls2)
    Hatomic X Hexec).
Qed.
Lemma used_complete_event_merge_core_fields__sem_accept_returns_and_focus :
  forall sg tasks base eid e,
  ((base + OSEventType_off) # UChar |-> encode_event_type e.(eventType) **
   (base + OSEventPtr_off) # Ptr |-> verification_slice_encode_event_ptr_value sg e **
   (base + OSEventCnt_off) # UShort |-> encode_event_cnt_value e **
   used_event_rest_no_type_cnt_ptr sg tasks base eid e |--
   used_complete_event sg tasks base eid e)%sac.
Proof.
  intros. unfold used_complete_event, used_event_rest_no_type_cnt_ptr.
  entailer!.
Qed.
Lemma event_inv_merge_complete_event__sem_accept_returns_and_focus :
  forall sg tasks events eid e,
  events.(inUsedEventStates) eid = Some e ->
  (used_complete_event sg tasks (event_addr sg eid) eid e **
   verification_slice_event_inv_no_eid sg tasks events eid |--
   verification_slice_event_inv sg tasks events)%sac.
Proof.
  intros sg tasks events eid e Hlookup.
  unfold verification_slice_event_inv_no_eid, store_used_event_map_missing_i.
  Intros.
  sep_apply_l_atomic (store_map_merge
    (fun i value => used_complete_event sg tasks (event_addr sg i) i value)
    eid e events.(inUsedEventStates) Hlookup).
  unfold verification_slice_event_inv, store_used_event_map. entailer!.
Qed.
Lemma sem_count_update_preserves_event_wait_consistency__sem_accept_returns_and_focus :
  forall sg state eid e count,
  state.(EventState).(inUsedEventStates) eid = Some e ->
  event_wait.verification_slice_event_wait_object_consistency sg state ->
  event_wait.verification_slice_event_wait_object_consistency sg
    (sem_accept_post_state state eid e count).
Proof.
  intros sg state eid e count Hlookup [Hentry [Hback Hclosed]].
  unfold event_wait.verification_slice_event_wait_object_consistency,
    event_wait.task_event_reference_backlink_consistency,
    event_wait.task_event_reference_closure.
  cbn [sem_accept_post_state replace_EventS].
  unfold sem_accept_event_state_update, update_event_field_raw. cbn.
  split.
  - intros i value Hvalue.
    destruct (Z.eqb i eid) eqn:Hi.
    + apply Z.eqb_eq in Hi. subst i. injection Hvalue as Hvalue. subst value.
      exact (Hentry eid e Hlookup).
    + exact (Hentry i value Hvalue).
  - split.
    + intros tid t i value Htask Hvalue Href.
      destruct (Z.eqb i eid) eqn:Hi.
      * apply Z.eqb_eq in Hi. subst i. injection Hvalue as Hvalue. subst value.
         exact (Hback tid t eid e Htask Hlookup Href).
      * exact (Hback tid t i value Htask Hvalue Href).
    + intros tid t Htask.
      destruct (Hclosed tid t Htask) as [Hptr Hmulti]. split.
      * intros i Href. destruct (Z.eqb i eid).
         -- eexists; reflexivity.
         -- exact (Hptr i Href).
      * intros i Href. destruct (Z.eqb i eid).
         -- eexists; reflexivity.
         -- exact (Hmulti i Href).
Qed.
Lemma sem_count_update_mutex_lookup_iff__sem_accept_returns_and_focus :
  forall state eid e count,
  state.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM ->
  forall i value,
  value.(eventType) = OS_EVENT_TYPE_MUTEX ->
  ((sem_accept_post_state state eid e count).(EventState).(inUsedEventStates) i = Some value <->
   state.(EventState).(inUsedEventStates) i = Some value).
Proof.
  intros state eid e count Hlookup Hsem i value Hmutex.
  cbn [sem_accept_post_state replace_EventS].
  unfold sem_accept_event_state_update, update_event_field_raw. cbn.
  destruct (Z.eqb i eid) eqn:Hi; [|reflexivity].
  apply Z.eqb_eq in Hi. subst i. rewrite Hlookup.
  split; intro Heq; injection Heq as Heq; subst value; cbn in Hmutex; congruence.
Qed.

Lemma sem_accept_inv_merge_updated_event : forall sg s eid old new,
  UCOS2_state_inv sg
    (replace_EventS (update_event_field_raw s.(EventState) eid new) s) ->
  s.(EventState).(inUsedEventStates) eid = Some old ->
  new.(queueFields) = old.(queueFields) ->
  new.(eventType) = old.(eventType) ->
  used_event_rep sg s.(TskState) eid new **
  task_inv sg s.(TskState) **
  sched_inv sg s.(TskState) s.(SchedState) **
  interrupt_inv sg s.(IntrState) **
  tick_inv sg s.(TickState) **
  sem_accept_raw_frame sg s eid |--
  UCOS2_inv sg (replace_EventS (update_event_field_raw s.(EventState) eid new) s).
Proof.
  intros sg s eid old new Hvalid Hlookup Hqueue Htype.
  unfold sem_accept_raw_frame, task_inv, sched_inv.
  eapply derivable1_trans with
    (used_event_rep sg s.(TskState) eid new **
     event_raw_rep_no_eid sg s.(TskState) s.(EventState) eid **
     queue_storage_rep sg s.(EventState) **
     UCOS2_raw_rep_missing_event_queue sg s).
  - unfold UCOS2_raw_rep_missing_event_queue, UCOS2_raw_rep_missing_two,
      UCOS2_selected_rep, UCOS2_module_rep, task_stack.task_shared_rep.
    cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect].
    entailer!.
  - apply (UCOS2_inv_merge_updated_event sg s eid old new Hvalid Hlookup Hqueue Htype).
Qed.
