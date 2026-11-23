Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.kernel_resources.
Import ListNotations.
Local Open Scope Z_scope.

Definition task_name_reference (tasks : Glob_TaskAbstractState) (p : addr) : Prop :=
  exists tid node, tasks.(inUsedTaskStates) tid = Some node /\ p = node.(tcbTaskName).
Definition event_name_reference (events : Glob_EventAbstractState) (p : addr) : Prop :=
  exists eid node, events.(inUsedEventStates) eid = Some node /\ p = node.(eventName).

(** A publication transfers an initialized name pointer, not the string
    bytes themselves.  When the field is enabled those bytes must already
    be represented by the separate Name owner.  The spatial global frame
    supplies that owner's storage; this pure condition creates no memory. *)
Definition event_name_valid (sg : StableGlobVars) (names : NameResourceState)
  (node : OSEventAbstractState) : Prop :=
  sg.(osKernelConfig).(cfgEventNames) = true ->
  exists chars, readable_name names node.(eventName) chars.

Lemma event_name_valid_disabled : forall sg names node,
  sg.(osKernelConfig).(cfgEventNames) = false -> event_name_valid sg names node.
Proof. intros sg names node Hdisabled Henabled; congruence. Qed.
Definition flag_name_reference (flags : GlobFlagState) (p : addr) : Prop :=
  exists id group, flags.(flagUsed) id = Some group /\ p = group.(flagName).
Definition memory_name_reference (memory : GlobMemoryState) (p : addr) : Prop :=
  (exists id image, memory.(memControlImages) id = Some image /\ p = image.(memImageName)) \/
  (exists id allocation, memory.(memPrivateControls) id = Some allocation /\
    p = allocation.(memPrivateImage).(memImageName)).
Definition timer_name_reference (timers : GlobTimerState) (p : addr) : Prop :=
  exists id timer, timers.(timerUsed) id = Some timer /\ p = timer.(timerName).

(** References derive from existing source fields, not from another ghost
    object map. Task/Flag getters select live objects; Timer NameGet rejects
    UNUSED before reading its name. Memory NameGet has no allocated-state
    check, so all globally represented control images are included. A
    private Memory allocation retains its old name through Create and must
    keep that string alive until publication/rollback. Arbitrary unfinished
    Task/Timer images are not interpreted as initialized name pointers.
    Event names are conditional and disabled in the current global profile. *)
Definition kernel_name_root (sg : StableGlobVars) (s : UCOS2_Verify_State) (p : addr) : Prop :=
  (sg.(osKernelConfig).(cfgTaskNames) = true /\ task_name_reference s.(TskState) p) \/
  (sg.(osKernelConfig).(cfgEventNames) = true /\ event_name_reference s.(EventState) p) \/
  (sg.(osKernelConfig).(cfgFlagEnabled) = true /\ sg.(osKernelConfig).(cfgFlagNames) = true /\
    flag_name_reference s.(FlagState) p) \/
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true /\ sg.(osKernelConfig).(cfgMemoryNames) = true /\
    memory_name_reference s.(MemoryState) p) \/
  (sg.(osKernelConfig).(cfgTimerEnabled) = true /\ sg.(osKernelConfig).(cfgTimerNames) = true /\
    timer_name_reference s.(TimerState) p).

Definition kernel_names_valid (sg : StableGlobVars) (s : UCOS2_Verify_State) : Prop :=
  forall p, kernel_name_root sg s p -> exists chars, readable_name s.(NameState) p chars.

(** Includes the terminator and overlapping suffix aliases. These are
    references to the single shared byte owner, not extra copies of it. *)
Definition kernel_name_byte_protected (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (q : addr) : Prop :=
  exists p chars i, kernel_name_root sg s p /\ readable_name s.(NameState) p chars /\
    (i <= List.length chars)%nat /\ q = p + Z.of_nat i.

Lemma kernel_name_root_replace_names_eq : forall sg s names p,
  kernel_name_root sg (replace_NameS names s) p = kernel_name_root sg s p.
Proof. reflexivity. Qed.

Lemma readable_name_same_bytes : forall before after p chars,
  before.(nameBytes) = after.(nameBytes) ->
  readable_name before p chars -> readable_name after p chars.
Proof.
  intros before after p chars Hbytes [Hchars [Hread Hnul]].
  split; [exact Hchars|]. split; rewrite <- Hbytes; assumption.
Qed.

Lemma kernel_names_valid_root_subset : forall sg before after,
  kernel_names_valid sg before -> before.(NameState).(nameBytes) = after.(NameState).(nameBytes) ->
  (forall p, kernel_name_root sg after p -> kernel_name_root sg before p) ->
  kernel_names_valid sg after.
Proof.
  intros sg before after Hvalid Hbytes Hroots p Hp.
  destruct (Hvalid p (Hroots p Hp)) as [chars Hread].
  exists chars; eapply readable_name_same_bytes; eassumption.
Qed.

Lemma kernel_names_valid_frame : forall sg before after,
  kernel_names_valid sg before -> before.(NameState).(nameBytes) = after.(NameState).(nameBytes) ->
  (forall p, task_name_reference after.(TskState) p -> task_name_reference before.(TskState) p) ->
  (forall p, event_name_reference after.(EventState) p -> event_name_reference before.(EventState) p) ->
  (forall p, flag_name_reference after.(FlagState) p -> flag_name_reference before.(FlagState) p) ->
  (forall p, memory_name_reference after.(MemoryState) p -> memory_name_reference before.(MemoryState) p) ->
  (forall p, timer_name_reference after.(TimerState) p -> timer_name_reference before.(TimerState) p) ->
  kernel_names_valid sg after.
Proof.
  intros sg before after Hvalid Hbytes Htask Hevent Hflag Hmemory Htimer.
  eapply kernel_names_valid_root_subset; [exact Hvalid|exact Hbytes|].
  intros p [[Henabled Hr] | [[Henabled Hr] |
    [[Henabled [Hnamed Hr]] | [[Henabled [Hnamed Hr]] | [Henabled [Hnamed Hr]]]]]].
  - left; split; [exact Henabled|apply Htask; exact Hr].
  - right; left; split; [exact Henabled|apply Hevent; exact Hr].
  - right; right; left; split; [exact Henabled|]. split; [exact Hnamed|apply Hflag; exact Hr].
  - right; right; right; left; split; [exact Henabled|]. split; [exact Hnamed|apply Hmemory; exact Hr].
  - right; right; right; right; split; [exact Henabled|]. split; [exact Hnamed|apply Htimer; exact Hr].
Qed.

Lemma kernel_names_valid_replace_task : forall sg s tasks,
  kernel_names_valid sg s ->
  (forall p, task_name_reference tasks p -> task_name_reference s.(TskState) p) ->
  kernel_names_valid sg (replace_TskS tasks s).
Proof.
  intros; eapply kernel_names_valid_frame; [eassumption|reflexivity|eassumption|..];
    intros; assumption.
Qed.

Lemma kernel_names_valid_replace_event : forall sg s events,
  kernel_names_valid sg s ->
  (forall p, event_name_reference events p -> event_name_reference s.(EventState) p) ->
  kernel_names_valid sg (replace_EventS events s).
Proof.
  intros; eapply kernel_names_valid_frame; [eassumption|reflexivity| |eassumption|..];
    intros; assumption.
Qed.

Lemma kernel_names_valid_replace_flag : forall sg s flags,
  kernel_names_valid sg s ->
  (forall p, flag_name_reference flags p -> flag_name_reference s.(FlagState) p) ->
  kernel_names_valid sg (replace_FlagS flags s).
Proof.
  intros; eapply kernel_names_valid_frame; [eassumption|reflexivity| | |eassumption|..];
    intros; assumption.
Qed.

Lemma kernel_names_valid_replace_memory : forall sg s memory,
  kernel_names_valid sg s ->
  (forall p, memory_name_reference memory p -> memory_name_reference s.(MemoryState) p) ->
  kernel_names_valid sg (replace_MemoryS memory s).
Proof.
  intros; eapply kernel_names_valid_frame; [eassumption|reflexivity| | | |eassumption|];
    intros; assumption.
Qed.

Lemma kernel_names_valid_replace_timer : forall sg s timers,
  kernel_names_valid sg s ->
  (forall p, timer_name_reference timers p -> timer_name_reference s.(TimerState) p) ->
  kernel_names_valid sg (replace_TimerS timers s).
Proof.
  intros; eapply kernel_names_valid_frame; [eassumption|reflexivity| | | | |eassumption];
    intros; assumption.
Qed.

(** A source operation may introduce the one actual new pointer it stores.
    Its caller supplies that string, not validity of the entire post-state. *)
Lemma kernel_names_valid_add_root : forall sg before after name chars,
  kernel_names_valid sg before -> readable_name before.(NameState) name chars ->
  before.(NameState).(nameBytes) = after.(NameState).(nameBytes) ->
  (forall p, kernel_name_root sg after p -> kernel_name_root sg before p \/ p = name) ->
  kernel_names_valid sg after.
Proof.
  intros sg before after name chars Hvalid Hname Hbytes Hroots p Hp.
  destruct (Hroots p Hp) as [Hold | Heq].
  - destruct (Hvalid p Hold) as [old Hread]; exists old.
    eapply readable_name_same_bytes; eassumption.
  - subst p; exists chars; eapply readable_name_same_bytes; eassumption.
Qed.

(** An Event publication or NameSet may introduce one name pointer. The
    readable bytes are a separate premise, never obtained from the pointer
    value itself. This rule is independent of the names-disabled profile. *)
Lemma kernel_names_valid_replace_event_add_name : forall sg s events name,
  kernel_names_valid sg s ->
  (sg.(osKernelConfig).(cfgEventNames) = true ->
    exists chars, readable_name s.(NameState) name chars) ->
  (forall p, event_name_reference events p ->
    event_name_reference s.(EventState) p \/ p = name) ->
  kernel_names_valid sg (replace_EventS events s).
Proof.
  intros sg s events name Hvalid Hread Hreferences.
  unfold kernel_names_valid.
  intros p [[Henabled Hr] | [[Henabled Hr] |
    [[Henabled [Hnamed Hr]] | [[Henabled [Hnamed Hr]] | [Henabled [Hnamed Hr]]]]]].
  - apply Hvalid; left; split; assumption.
  - destruct (Hreferences p Hr) as [Hold|Heq].
    + apply Hvalid; right; left; split; assumption.
    + subst p; apply Hread; exact Henabled.
  - apply Hvalid; right; right; left; split; [exact Henabled|]; split; assumption.
  - apply Hvalid; right; right; right; left; split; [exact Henabled|]; split; assumption.
  - apply Hvalid; right; right; right; right; split; [exact Henabled|]; split; assumption.
Qed.

Lemma kernel_name_referenced_byte_protected : forall sg s p chars i,
  kernel_name_root sg s p -> readable_name s.(NameState) p chars ->
  (i <= List.length chars)%nat -> kernel_name_byte_protected sg s (p + Z.of_nat i).
Proof.
  intros sg s p chars i Hroot Hread Hi; exists p, chars, i.
  split; [exact Hroot|]. split; [exact Hread|]. split; [exact Hi|reflexivity].
Qed.

(** Instantiate the formerly caller-chosen protected set with real object
    references. The raw write still changes exactly one byte; protection
    is a caller/resource protocol, not an invented C runtime branch. *)
Lemma kernel_name_write_preserves_validity : forall sg s q b,
  kernel_names_valid sg s ->
  name_byte_writable s.(NameState) (kernel_name_byte_protected sg s) q ->
  kernel_names_valid sg (replace_NameS (name_write_byte s.(NameState) q b) s).
Proof.
  intros sg s q b Hvalid [Hunreferenced Hreaders] p Hp.
  rewrite kernel_name_root_replace_names_eq in Hp.
  destruct (Hvalid p Hp) as [chars Hname].
  exists chars; pose proof Hname as [Hchars [Hbytes Hnul]].
  split; [exact Hchars|]. split.
  - intros i c Hi; change ((name_write_byte s.(NameState) q b).(nameBytes) (p + Z.of_nat i) = Some c).
    unfold name_write_byte; simpl.
    rewrite kernel_map_set_other; [apply Hbytes; exact Hi|].
    intro Heq; apply Hunreferenced; rewrite <- Heq.
    apply kernel_name_referenced_byte_protected with (chars := chars); try assumption.
    apply Nat.lt_le_incl; apply nth_error_Some; congruence.
  - change ((name_write_byte s.(NameState) q b).(nameBytes)
      (p + Z.of_nat (List.length chars)) = Some 0).
    unfold name_write_byte; simpl.
    rewrite kernel_map_set_other; [exact Hnul|].
    intro Heq; apply Hunreferenced; rewrite <- Heq.
    apply kernel_name_referenced_byte_protected with (chars := chars); auto.
Qed.

Lemma kernel_name_source_release_preserves_validity : forall sg s source src,
  kernel_names_valid sg s ->
  name_source_releasable s.(NameState) source src (kernel_name_byte_protected sg s) ->
  kernel_names_valid sg (replace_NameS (name_unregister_source s.(NameState) source src) s).
Proof.
  intros sg s source src Hvalid [_ [_ [Hprotected Hreaders]]] p Hp.
  rewrite kernel_name_root_replace_names_eq in Hp.
  destruct (Hvalid p Hp) as [chars Hname].
  exists chars; pose proof Hname as [Hchars [Hbytes Hnul]].
  assert (Houtside : forall i, (i <= List.length chars)%nat ->
    ~ In (p + Z.of_nat i) src.(nameStorageDomain)).
  { intros i Hi; apply Hprotected.
    apply kernel_name_referenced_byte_protected with (chars := chars); assumption. }
  split; [exact Hchars|]. split.
  - intros i c Hi; change ((name_unregister_source s.(NameState) source src).(nameBytes)
      (p + Z.of_nat i) = Some c).
    unfold name_unregister_source; simpl.
    destruct (in_dec Z.eq_dec (p + Z.of_nat i) src.(nameStorageDomain)) as [Hin|Hnot].
    + exfalso; eapply Houtside; [|exact Hin].
      apply Nat.lt_le_incl; apply nth_error_Some; congruence.
    + apply Hbytes; exact Hi.
  - change ((name_unregister_source s.(NameState) source src).(nameBytes)
      (p + Z.of_nat (List.length chars)) = Some 0).
    unfold name_unregister_source; simpl.
    destruct (in_dec Z.eq_dec (p + Z.of_nat (List.length chars)) src.(nameStorageDomain)) as [Hin|Hnot].
    + exfalso; exact (Houtside _ (Nat.le_refl _) Hin).
    + exact Hnul.
Qed.
