Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.flag.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** OS_FlagBlock, pinned V2.93.01 Source/os_flag.c:1090--1127.
    The TCB status/pend/delay stores precede the conditional TCB backlink;
    that backlink precedes the six local-node stores.  Old-head Prev,
    group head and ready-bit writes follow.  All occur inside the caller's
    critical interval.  These operations describe its endpoint, not an
    instruction sequence or a proof that the caller owns the local node.

    [task_prepare_event_wait] is reused for its exact OR/OK/delay stores;
    it does not itself register an OS_EVENT.  TaskDelete-disabled source
    retains the old backlink instead of silently performing the enabled
    profile's additional write. *)
Definition flag_block_task (c : KernelConfiguration) (old : TaskAbstractState)
  (node : addr) (timeout : Z) : TaskAbstractState :=
  let waiting := task_prepare_event_wait old PendFlag timeout in
  if c.(cfgTaskDelete) then task_set_flag_node waiting node else waiting.

Definition flag_block_state (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (tid : TaskID) (old : TaskAbstractState) (node : addr) (timeout : Z)
  (flags : GlobFlagState) : UCOS2_Verify_State :=
  replace_FlagS flags
    (replace_SchedS (sched_remove_ready_task s.(SchedState) tid)
      (replace_TskS (glob_task_set_usedtask s.(TskState) tid
        (flag_block_task sg.(osKernelConfig) old node timeout)) s)).

(** The selected TCB comes from the current-task observation, not from an
    arbitrary ghost waiter ID.  The caller separately binds the waiter's
    task/generation and actual group, mask, decoded mode and node address.
    None marks missing modeled dereference data; it is NOT a new C branch,
    error return, validity guard, or permission to skip the source writes. *)
Definition flag_block (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (timeout : Z) : option UCOS2_Verify_State :=
  match s.(SchedState).(curTaskID) with
  | None => None
  | Some tid => match s.(TskState).(inUsedTaskStates) tid with
    | None => None
    | Some old => match flag_block_node sg s.(FlagState) w (task_slot_addr sg tid) with
      | None => None
      | Some flags => Some (flag_block_state sg s tid old w.(flagNodeAddr) timeout flags)
      end
    end
  end.

Lemma flag_block_task_fields : forall c old node timeout,
  let updated := flag_block_task c old node timeout in
  encode_task_status updated.(stat) = Z.lor (encode_task_status old.(stat)) 32 /\
  updated.(statPend) = PendOK /\ updated.(dly) = timeout /\
  updated.(tcbFlagNode) = (if c.(cfgTaskDelete) then node else old.(tcbFlagNode)).
Proof.
  intros c old node timeout updated; unfold updated, flag_block_task.
  destruct c.(cfgTaskDelete);
    (split; [apply task_prepare_event_wait_status_encoding|repeat split; reflexivity]).
Qed.

Lemma flag_block_task_identity_frame : forall c old node timeout,
  let updated := flag_block_task c old node timeout in
  updated.(taskID) = old.(taskID) /\
  updated.(taskGeneration) = old.(taskGeneration) /\
  updated.(curPrio) = old.(curPrio) /\ updated.(tcbStkPtr) = old.(tcbStkPtr) /\
  updated.(eventPtr) = old.(eventPtr) /\
  updated.(eventMultiWaitEvents) = old.(eventMultiWaitEvents).
Proof.
  intros c old node timeout updated; unfold updated, flag_block_task.
  destruct c.(cfgTaskDelete); repeat split; reflexivity.
Qed.

(** This is the existing common-field image, not a theorem that a concrete
    C/ARM layout or a complete 72-byte multi-wait TCB has been established. *)
Lemma flag_block_task_common_image_eq : forall sg old node timeout,
  task_tcb64_image sg (flag_block_task sg.(osKernelConfig) old node timeout) =
  let prepared := tcb_prepare_wait_image (task_tcb64_image sg old)
    (task_status_set_wait (encode_task_status old.(stat)) PendFlag) timeout in
  if sg.(osKernelConfig).(cfgTaskDelete)
  then tcb_write prepared TCBFlagNode (Some node) else prepared.
Proof.
  intros; unfold flag_block_task.
  destruct sg.(osKernelConfig).(cfgTaskDelete);
    rewrite ?task_set_flag_node_image_eq, task_prepare_event_wait_image_eq; reflexivity.
Qed.

Lemma flag_block_task_not_ready : forall c old node timeout,
  is_effectively_ready (flag_block_task c old node timeout).(stat)
    (flag_block_task c old node timeout).(dly) = false.
Proof.
  intros; unfold flag_block_task; destruct c.(cfgTaskDelete);
    apply task_prepare_event_wait_not_ready.
Qed.

Lemma flag_block_task_linked_phase : forall c old node timeout,
  task_non_suspension_bits old.(stat) = 0 ->
  task_linked_wait_phase (flag_block_task c old node timeout) PendFlag.
Proof.
  intros; left; unfold flag_block_task; destruct c.(cfgTaskDelete);
    apply task_prepare_event_wait_pending_bits; assumption.
Qed.

Lemma flag_block_result : forall sg s w timeout post,
  flag_block sg s w timeout = Some post ->
  exists tid old flags,
    s.(SchedState).(curTaskID) = Some tid /\
    s.(TskState).(inUsedTaskStates) tid = Some old /\
    flag_block_node sg s.(FlagState) w (task_slot_addr sg tid) = Some flags /\
    post = flag_block_state sg s tid old w.(flagNodeAddr) timeout flags.
Proof.
  intros sg s w timeout post Hstep; unfold flag_block in Hstep.
  destruct s.(SchedState).(curTaskID) as [tid|] eqn:Hcurrent; [|discriminate].
  destruct (s.(TskState).(inUsedTaskStates) tid) as [old|] eqn:Hold; [|discriminate].
  destruct (flag_block_node sg s.(FlagState) w (task_slot_addr sg tid)) as [flags|]
    eqn:Hflags; [|discriminate].
  injection Hstep as Hpost; subst post.
  exists tid, old, flags; repeat split; assumption || reflexivity.
Qed.

Lemma flag_block_current_lookup_exists : forall sg s w timeout tid old group image,
  s.(SchedState).(curTaskID) = Some tid ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  s.(FlagState).(flagUsed) w.(flagGroup) = Some group ->
  s.(FlagState).(flagImages) w.(flagGroup) = Some image ->
  exists post, flag_block sg s w timeout = Some post.
Proof.
  intros sg s w timeout tid old group image Hcurrent Hold Hgroup Himage.
  unfold flag_block; rewrite Hcurrent, Hold.
  unfold flag_block_node; rewrite Hgroup, Himage; eexists; reflexivity.
Qed.

Lemma flag_block_state_task_lookup : forall sg s tid old node timeout flags,
  (flag_block_state sg s tid old node timeout flags).(TskState).(inUsedTaskStates) tid =
    Some (flag_block_task sg.(osKernelConfig) old node timeout).
Proof. intros; simpl; rewrite Z.eqb_refl; reflexivity. Qed.

Lemma flag_block_state_other_task : forall sg s tid old node timeout flags other,
  other <> tid ->
  (flag_block_state sg s tid old node timeout flags).(TskState).(inUsedTaskStates) other =
    s.(TskState).(inUsedTaskStates) other.
Proof. intros; simpl; rewrite (proj2 (Z.eqb_neq _ _) H); reflexivity. Qed.

Lemma flag_block_state_task_lifecycle_frame : forall sg s tid old node timeout flags,
  let post := flag_block_state sg s tid old node timeout flags in
  post.(TskState).(taskLifecycle) = s.(TskState).(taskLifecycle) /\
  post.(TskState).(unUsedTaskStates) = s.(TskState).(unUsedTaskStates) /\
  post.(TskState).(prioTbl) = s.(TskState).(prioTbl) /\
  post.(TskState).(tcbListHead) = s.(TskState).(tcbListHead) /\
  post.(TskState).(taskCount) = s.(TskState).(taskCount) /\
  post.(TskState).(taskRegNextID) = s.(TskState).(taskRegNextID).
Proof. intros; repeat split; reflexivity. Qed.

Lemma flag_block_state_scheduler_fields : forall sg s tid old node timeout flags,
  let post := flag_block_state sg s tid old node timeout flags in
  post.(SchedState).(readyList) = remove_Z_eqb tid s.(SchedState).(readyList) /\
  post.(SchedState).(curTaskID) = s.(SchedState).(curTaskID) /\
  post.(SchedState).(curSchedPrio) = s.(SchedState).(curSchedPrio) /\
  post.(SchedState).(highRdyTid) = s.(SchedState).(highRdyTid) /\
  post.(SchedState).(highRdyPrio) = s.(SchedState).(highRdyPrio) /\
  post.(SchedState).(ctxSwCtr) = s.(SchedState).(ctxSwCtr) /\
  post.(SchedState).(isRunning) = s.(SchedState).(isRunning).
Proof. intros; repeat split; reflexivity. Qed.

Lemma flag_block_state_module_frame : forall sg s tid old node timeout flags,
  let post := flag_block_state sg s tid old node timeout flags in
  post.(IntrState) = s.(IntrState) /\ post.(EventState) = s.(EventState) /\
  post.(TickState) = s.(TickState) /\ post.(MemoryState) = s.(MemoryState) /\
  post.(TimerState) = s.(TimerState) /\ post.(StatsState) = s.(StatsState) /\
  post.(ControlState) = s.(ControlState) /\ post.(NameState) = s.(NameState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma flag_block_state_preserves_task_scheduler_in_range :
  forall sg s tid old node timeout flags,
  task_in_range sg s.(TskState) -> sched_in_range sg s.(TskState) s.(SchedState) ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  let post := flag_block_state sg s tid old node timeout flags in
  task_in_range sg post.(TskState) /\ sched_in_range sg post.(TskState) post.(SchedState).
Proof.
  intros sg s tid old node timeout flags Htasks Hsched Hold post; split.
  - eapply task_update_preserves_in_range; [exact Htasks|exact Hold| | | | |];
      unfold flag_block_task; destruct sg.(osKernelConfig).(cfgTaskDelete); reflexivity.
  - eapply sched_remove_ready_task_preserves_in_range; [exact Hsched|exact Hold| |].
    + unfold flag_block_task; destruct sg.(osKernelConfig).(cfgTaskDelete); reflexivity.
    + apply flag_block_task_not_ready.
Qed.

(** Only the three stated MODULE predicates are established here.  The
    Task-Flag/Event/Mutex cross-relations, full UCOS2 invariant and actual
    bitmap/TCB/node ownership need their own joint call-site reconstruction.
    All premises concern the source state, source argument image, or the
    actual endpoint equation; no post-validity premise is introduced. *)
Lemma flag_block_preserves_module_validity : forall sg s w timeout tid old flags group,
  task_in_range sg s.(TskState) -> sched_in_range sg s.(TskState) s.(SchedState) ->
  valid_flag_state sg s.(FlagState) ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  s.(FlagState).(flagUsed) w.(flagGroup) = Some group ->
  w.(flagGroupGeneration) = group.(flagGeneration) -> w.(flagNodeAddr) <> 0 ->
  s.(FlagState).(flagWaitNodes) w.(flagNodeAddr) = None ->
  flag_word_in_range sg.(osKernelConfig) w.(flagMask) ->
  Z.of_nat (List.length w.(flagWaitImage).(flagNodePadding)) =
    flag_node_size sg.(osKernelConfig) - flag_node_mode_offset sg.(osKernelConfig) - 1 ->
  flag_block_node sg s.(FlagState) w (task_slot_addr sg tid) = Some flags ->
  let post := flag_block_state sg s tid old w.(flagNodeAddr) timeout flags in
  task_in_range sg post.(TskState) /\
  sched_in_range sg post.(TskState) post.(SchedState) /\ valid_flag_state sg post.(FlagState).
Proof.
  intros sg s w timeout tid old flags group Htasks Hsched Hflags Hold Hgroup
    Hgeneration Haddress Hfresh Hmask Hpadding Hstep post.
  destruct (flag_block_state_preserves_task_scheduler_in_range
    sg s tid old w.(flagNodeAddr) timeout flags Htasks Hsched Hold) as [Ht Hs].
  split; [exact Ht|]; split; [exact Hs|].
  eapply flag_block_preserves_state_validity; eassumption.
Qed.

Lemma flag_block_state_installs_node : forall sg s w timeout tid old flags group image,
  valid_flag_state sg s.(FlagState) ->
  s.(FlagState).(flagUsed) w.(flagGroup) = Some group ->
  s.(FlagState).(flagImages) w.(flagGroup) = Some image ->
  s.(FlagState).(flagWaitNodes) w.(flagNodeAddr) = None ->
  flag_block_node sg s.(FlagState) w (task_slot_addr sg tid) = Some flags ->
  let post := flag_block_state sg s tid old w.(flagNodeAddr) timeout flags in
  post.(FlagState).(flagWaitNodes) w.(flagNodeAddr) =
    Some (flag_waiter_set_image w
      (flag_block_node_image sg w (task_slot_addr sg tid) image.(flagImageHead))) /\
  post.(TskState).(inUsedTaskStates) tid =
    Some (flag_block_task sg.(osKernelConfig) old w.(flagNodeAddr) timeout).
Proof.
  intros sg s w timeout tid old flags group image Hvalid Hgroup Himage Hfresh Hstep post.
  split; [eapply flag_block_installs_node; eassumption|apply flag_block_state_task_lookup].
Qed.

(** Remaining call connections: bind &node and the original Pend invocation
    to the actual borrowed stack interval; prove the six stores from uninit
    cells; transfer the initialized node before critical release; connect
    joint cross-relations and physical ready writes; retain direct-caller
    ownership through Del/Post's post-unlink Next read before returning the
    node to its original stack.  No continuation, hook, scheduler or ARM
    execution theorem is claimed by these endpoint lemmas. *)
