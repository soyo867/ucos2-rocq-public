Require Import Coq.ZArith.ZArith Coq.Strings.String Coq.micromega.Lia.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_annotation_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** The actual Task-specific Sem C declaration checks these physical
    bindings only on the ordered arm reaching the first critical section.
    No observation of the old optional-acquire program is used here. *)
Definition tmr_task_client_pend_address_guard sg (before : UCOS2_Verify_State)
  pe eid type_address count_address ints locks current group rows : Prop :=
  pe = 0 \/
  (pe <> 0 /\ type_address = event_addr sg eid + OSEventType_off /\
    (event_slot_type_value before.(EventState) eid <> 3 \/
      (event_slot_type_value before.(EventState) eid = 3 /\ ints = sg.(g_OSIntNesting) /\
        (before.(IntrState).(intNesting) > 0 \/
          (before.(IntrState).(intNesting) <= 0 /\ locks = sg.(g_OSLockNesting) /\
            (before.(IntrState).(lockNesting) > 0 \/
              (before.(IntrState).(lockNesting) <= 0 /\
                count_address = event_addr sg eid + OSEventCnt_off /\
                current = sg.(g_OSTCBCur) /\ group = sg.(g_OSRdyGrp) /\
                rows = sg.(g_OSRdyTbl) /\ event_object_layout_prop sg eid))))))).

Lemma tmr_task_client_pend_address_guard_from_input : forall critical sg invocation
  before eid observed pe ints locks current group rows,
  sem_pend_call_input critical sg invocation pe before eid observed ->
  event_table_layout_prop sg ->
  ints = sg.(g_OSIntNesting) -> locks = sg.(g_OSLockNesting) ->
  current = sg.(g_OSTCBCur) -> group = sg.(g_OSRdyGrp) -> rows = sg.(g_OSRdyTbl) ->
  tmr_task_client_pend_address_guard sg before pe eid
    (&((pe) # "os_event" ->ₛ "OSEventType"))
    (&((pe) # "os_event" ->ₛ "OSEventCnt")) ints locks current group rows.
Proof.
  intros critical sg invocation before eid observed pe ints locks current group rows
    Hinput Hlayout Hints Hlocks Hcurrent Hgroup Hrows.
  destruct Hinput as [Hzero|[Hnonzero [Haddress [Hid [Hslot Hprotocol]]]]].
  - left; exact Hzero.
  - pose proof (Hlayout eid Hid) as Hobject.
    pose proof (event_object_layout_core_proj sg eid Hobject)
      as [Htype_address [_ Hcount_address]].
    right; split; [exact Hnonzero|]. split.
    + rewrite Haddress; exact Htype_address.
    + destruct (Z.eq_dec (event_slot_type_value before.(EventState) eid) 3) as [Htype|Htype].
      2: { left; exact Htype. }
      right; split; [exact Htype|]. split; [exact Hints|].
      destruct (Z_lt_ge_dec 0 before.(IntrState).(intNesting)) as [Hinside|Houtside].
      * left; lia.
      * right; split; [lia|]. split; [exact Hlocks|].
        destruct (Z_lt_ge_dec 0 before.(IntrState).(lockNesting)) as [Hlocked|Hunlocked].
        -- left; lia.
        -- right; split; [lia|]. split.
           ++ rewrite Haddress; exact Hcount_address.
           ++ exact (conj Hcurrent (conj Hgroup (conj Hrows Hobject))).
Qed.

Lemma tmr_task_client_pend_address_guard_from_domain : forall environment critical sg call
  before eid observed pe ints locks current group rows,
  sem_pend_fields_call_domain environment critical sg call pe before eid observed ->
  event_table_layout_prop sg ->
  ints = sg.(g_OSIntNesting) -> locks = sg.(g_OSLockNesting) ->
  current = sg.(g_OSTCBCur) -> group = sg.(g_OSRdyGrp) -> rows = sg.(g_OSRdyTbl) ->
  tmr_task_client_pend_address_guard sg before pe eid
    (&((pe) # "os_event" ->ₛ "OSEventType"))
    (&((pe) # "os_event" ->ₛ "OSEventCnt")) ints locks current group rows.
Proof.
  intros environment critical sg call before eid observed pe ints locks current group rows
    [_ [_ [Hinput Hrest]]] Hlayout Hints Hlocks Hcurrent Hgroup Hrows.
  eapply tmr_task_client_pend_address_guard_from_input; eassumption.
Qed.

Lemma tmr_task_client_pend_address_guard_from_global_addresses :
  forall environment critical sg call before eid observed pe
    signal wheel time current running ints locks high priority high_tcb table counter unmap group rows,
  sem_pend_fields_call_domain environment critical sg call pe before eid observed ->
  event_table_layout_prop sg ->
  tmr_task_global_addresses sg signal wheel time current running ints locks high priority
    high_tcb table counter unmap group rows ->
  tmr_task_client_pend_address_guard sg before pe eid
    (&((pe) # "os_event" ->ₛ "OSEventType"))
    (&((pe) # "os_event" ->ₛ "OSEventCnt")) ints locks current group rows /\
  os_sched_global_addresses sg ints locks high priority high_tcb table counter unmap group rows.
Proof.
  intros environment critical sg call before eid observed pe signal wheel time current
    running ints locks high priority high_tcb table counter unmap group rows
    Hdomain Hlayout Haddresses.
  assert (Hsched : os_sched_global_addresses sg ints locks high priority high_tcb table
    counter unmap group rows).
  { unfold tmr_task_global_addresses, os_sched_unlock_global_addresses in Haddresses; tauto. }
  split; [|exact Hsched].
  eapply tmr_task_client_pend_address_guard_from_domain; [exact Hdomain|exact Hlayout|..].
  all: unfold tmr_task_global_addresses, os_sched_lock_global_addresses,
    os_sched_unlock_global_addresses, os_sched_global_addresses,
    sched_new_global_addresses in Haddresses; tauto.
Qed.

Lemma tmr_task_client_pend_address_guard_from_pre : forall environment local critical sg call
  mask pe ticks perr before eid observed X ints locks current group rows heap,
  tmr_task_client_pend_pre environment local critical sg call mask pe ticks perr
    before eid observed X heap ->
  event_table_layout_prop sg ->
  ints = sg.(g_OSIntNesting) -> locks = sg.(g_OSLockNesting) ->
  current = sg.(g_OSTCBCur) -> group = sg.(g_OSRdyGrp) -> rows = sg.(g_OSRdyTbl) ->
  tmr_task_client_pend_address_guard sg before pe eid
    (&((pe) # "os_event" ->ₛ "OSEventType"))
    (&((pe) # "os_event" ->ₛ "OSEventCnt")) ints locks current group rows.
Proof.
  intros environment local critical sg call mask pe ticks perr before eid observed X
    ints locks current group rows heap [[Hdomain Hfacts] Hresources]
    Hlayout Hints Hlocks Hcurrent Hgroup Hrows.
  eapply tmr_task_client_pend_address_guard_from_domain; eassumption.
Qed.
