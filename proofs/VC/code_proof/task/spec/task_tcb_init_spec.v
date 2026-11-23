Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Operators.
Require Import AUXLib.ListLib.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Export Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_resources.

Import ListNotations.
Import TaskStateDef.
Import SchedStateDef.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.

Record TaskTCBInitArgs : Type := {
  initPrio : Priority;
  initStkPtr : addr;
  initStkBottom : addr;
  initPublicId : Z;
  initStkSize : Z;
  initExtPtr : addr;
  initOpt : Z;
  initNamePointer : addr;
}.

(** Exact source write footprint before OSTCBInitHook.  In particular, link
    fields, FlagsRdy and padding are not reset, even on a reused pool slot. *)
Definition task_tcb_init_written_field (f : TCBField) : bool :=
  match f with
  | TCBNext | TCBPrev | TCBFlagsRdy | TCBPadding42 | TCBPadding43 => false
  | _ => true
  end.

Definition task_tcb_init_raw_image (args : TaskTCBInitArgs)
  (old : TCBCommonImage) : TCBCommonImage :=
  fun f => match f with
  | TCBStkPtr => Some args.(initStkPtr)
  | TCBExtPtr => Some args.(initExtPtr)
  | TCBStkBottom => Some args.(initStkBottom)
  | TCBStkSize => Some args.(initStkSize)
  | TCBOpt => Some args.(initOpt)
  | TCBId => Some args.(initPublicId)
  | TCBPrio => Some args.(initPrio)
  | TCBX => Some (args.(initPrio) mod 8)
  | TCBY => Some (args.(initPrio) / 8)
  | TCBBitX => Some (Z.shiftl 1 (args.(initPrio) mod 8))
  | TCBBitY => Some (Z.shiftl 1 (args.(initPrio) / 8))
  | TCBTaskName => Some args.(initNamePointer)
  | TCBStat | TCBStatPend | TCBDly | TCBEventPtr | TCBFlagNode
  | TCBMsg | TCBDelReq | TCBReg0 => Some 0
  | TCBNext | TCBPrev | TCBFlagsRdy | TCBPadding42 | TCBPadding43 => old f
  end.

Lemma task_tcb_init_raw_untouched : forall args old f,
  task_tcb_init_written_field f = false ->
  task_tcb_init_raw_image args old f = old f.
Proof. intros args old f; destruct f; simpl; congruence. Qed.

Lemma task_tcb_init_raw_all_written_defined : forall args old f,
  task_tcb_init_written_field f = true ->
  exists value, task_tcb_init_raw_image args old f = Some value.
Proof. intros args old f; destruct f; simpl; intros; try discriminate; eauto. Qed.

(** Optional fields follow the source configuration. Multi adds two NULL
    stores; profiling zeros its five real fields, including StkBase (not pbos).
    Disabled fields have no owned cells and their image entries are framed. *)
Definition task_tcb_init_layout_written_field (multi profile : bool)
  (field : TCBLayoutField) : bool :=
  match field with
  | TCBCommonField f => task_tcb_init_written_field f
  | TCBEventMultiPtr | TCBEventMultiRdy => multi
  | _ => profile
  end.

Definition task_tcb_init_layout_image (multi profile : bool) (args : TaskTCBInitArgs)
  (old : TCBLayoutImage) : TCBLayoutImage :=
  let initialized := tcb_layout_update_common (task_tcb_init_raw_image args) old in
  let with_multi := if multi then tcb_layout_set_multi initialized 0 0 else initialized in
  fun field => match field with
  | TCBCtxSwCtr | TCBCyclesTot | TCBCyclesStart | TCBStkBase | TCBStkUsed =>
      if profile then Some 0 else with_multi field
  | _ => with_multi field
  end.

Lemma task_tcb_init_layout_common_image_eq : forall multi profile args old,
  tcb_layout_common_image (task_tcb_init_layout_image multi profile args old) =
    task_tcb_init_raw_image args (tcb_layout_common_image old).
Proof. intros [] [] args old; apply functional_extensionality; intros []; reflexivity. Qed.

Lemma task_tcb_init_layout_untouched : forall multi profile args old field,
  task_tcb_init_layout_written_field multi profile field = false ->
  task_tcb_init_layout_image multi profile args old field = old field.
Proof.
  intros [] [] args old [f| | | | | | |]; try (intros; discriminate); try reflexivity;
    destruct f; simpl; intros; try discriminate; reflexivity.
Qed.

Lemma task_tcb_init_layout_multi_fields_zero : forall profile args old,
  task_tcb_init_layout_image true profile args old TCBEventMultiPtr = Some 0 /\
  task_tcb_init_layout_image true profile args old TCBEventMultiRdy = Some 0.
Proof. intros; split; reflexivity. Qed.

Lemma task_tcb_init_layout_profile_fields_zero : forall multi args old field,
  In field tcb_profile_fields ->
  task_tcb_init_layout_image multi true args old field = Some 0.
Proof. intros multi args old [] Hin; simpl in Hin; try reflexivity; intuition discriminate. Qed.

Definition task_tcb_init_before_hooks (args : TaskTCBInitArgs)
  (old : TaskAbstractState) : TaskAbstractState :=
  {| taskID := old.(taskID);
     taskGeneration := old.(taskGeneration);
     tcbStkPtr := args.(initStkPtr);
     tcbExtPtr := args.(initExtPtr);
     tcbStkBottom := args.(initStkBottom);
     tcbStkSize := args.(initStkSize);
     tcbOpt := args.(initOpt);
     tcbPublicId := args.(initPublicId);
     tcbFlagNode := 0;
     tcbFlagsRdy := old.(tcbFlagsRdy);
     tcbTaskName := args.(initNamePointer);
     tcbReg0 := 0;
     tcbCtxSwCtr := old.(tcbCtxSwCtr);
     tcbCyclesTot := old.(tcbCyclesTot);
     tcbCyclesStart := old.(tcbCyclesStart);
     tcbStkBase := old.(tcbStkBase);
     tcbStkUsed := old.(tcbStkUsed);
     tcbPadding42 := old.(tcbPadding42);
     tcbPadding43 := old.(tcbPadding43);
     tcbEventMultiPtr := old.(tcbEventMultiPtr);
     curPrio := args.(initPrio);
     stat := task_status_single None false;
     statPend := PendOK;
     dly := 0;
     eventPtr := None;
     eventMultiWaitEvents := old.(eventMultiWaitEvents);
     eventMultiRdy := old.(eventMultiRdy);
     msg := None;
     nextTCB := old.(nextTCB);
     prevTCB := old.(prevTCB);
     delReq := false |}.

Lemma task_tcb_init_raw_binding : forall sg args old f,
  task_tcb64_image sg (task_tcb_init_before_hooks args old) f =
  task_tcb_init_raw_image args (task_tcb64_image sg old) f.
Proof. intros; destruct f; reflexivity. Qed.

(** This interface specifies allowable private-node effects separately from
    global effects.  A future hook implementation must prove its own effect
    relation and frame; no arbitrary hook receives the empty-instance theorem. *)
Definition TaskTCBInitHookEffect : Type :=
  TCBCommonImage -> UCOS2_Verify_State ->
  TCBCommonImage -> UCOS2_Verify_State -> Prop.

Definition task_tcb_init_precommit_field (f : TCBField) : bool :=
  match f with TCBNext | TCBPrev => false | _ => true end.

Definition task_tcb_init_commit_safe_image
  (sg : StableGlobVars) (args : TaskTCBInitArgs) (image : TCBCommonImage)
  : Prop :=
  exists t,
    t.(curPrio) = args.(initPrio) /\
    task_priority_in_range sg t.(curPrio) /\
    is_effectively_ready t.(stat) t.(dly) = true /\
    t.(eventPtr) = None /\
    t.(eventMultiWaitEvents) = [] /\
    (forall f, task_tcb_init_precommit_field f = true ->
       image f = task_tcb64_image sg t f).

(** A reused free node need not already decode as a live task.  Its links
    are still stale and are deliberately excluded from the precommit view.
    Only FlagsRdy definedness comes from the initializer/recycle protocol;
    every other selected non-padding field below is written by OS_TCBInit
    itself. Optional Multi and profiling values are zero after their enabled
    source stores. When disabled they are unobserved abstract choices, not
    stores to missing fields. The configured binding below is restricted to
    the actual field inventory. *)
Definition task_tcb_init_node_from_free_image (args : TaskTCBInitArgs)
  (slot : TaskID) (generation : nat) (flags : Z) (old : TCBCommonImage)
  : TaskAbstractState :=
  {| taskID := slot; taskGeneration := generation;
     tcbStkPtr := args.(initStkPtr); tcbExtPtr := args.(initExtPtr);
     tcbStkBottom := args.(initStkBottom); tcbStkSize := args.(initStkSize);
     tcbOpt := args.(initOpt); tcbPublicId := args.(initPublicId);
     tcbFlagNode := 0; tcbFlagsRdy := flags;
     tcbTaskName := args.(initNamePointer); tcbReg0 := 0;
     tcbCtxSwCtr := 0; tcbCyclesTot := 0; tcbCyclesStart := 0;
     tcbStkBase := 0; tcbStkUsed := 0;
     tcbPadding42 := old TCBPadding42; tcbPadding43 := old TCBPadding43;
     tcbEventMultiPtr := 0;
     curPrio := args.(initPrio);
     stat := task_status_single None false;
     statPend := PendOK; dly := 0; eventPtr := None;
     eventMultiWaitEvents := []; eventMultiRdy := None; msg := None;
     nextTCB := None; prevTCB := None; delReq := false |}.

Lemma task_tcb_init_arbitrary_free_image_safe : forall sg args old flags
    (slot : TaskID) (generation : nat),
  task_priority_in_range sg args.(initPrio) ->
  old TCBFlagsRdy = Some flags ->
  task_tcb_init_commit_safe_image sg args (task_tcb_init_raw_image args old).
Proof.
  intros sg args old flags slot generation Hprio Hflags.
  exists (task_tcb_init_node_from_free_image args slot generation flags old).
  split; [reflexivity|]. split; [exact Hprio|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  intros f Hf; destruct f; simpl in Hf |- *; try discriminate;
    try reflexivity; exact Hflags.
Qed.

Definition task_tcb_init_initialize_private (sg : StableGlobVars) (args : TaskTCBInitArgs)
  (tasks : Glob_TaskAbstractState) (entry : TaskCreationEntry)
  (allocation : TaskPrivateAllocation) : Glob_TaskAbstractState :=
  task_update_private_image tasks args.(initPrio) entry allocation
    (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
      args allocation.(privateStorage)).

Lemma task_tcb_init_private_initialization_preserves_in_range :
  forall sg args tasks entry allocation,
    task_in_range sg tasks ->
    tasks.(taskLifecycle).(taskReservations) args.(initPrio) = Some entry ->
    entry.(creationAllocation) = Some allocation ->
    task_in_range sg (task_tcb_init_initialize_private sg args tasks entry allocation).
Proof. intros; apply task_update_private_image_preserves_in_range; assumption. Qed.

(** After the individual C stores, rebuild the same invocation's ownership
    with the actual new image.  The old private image is not silently reused
    in a pure frame, and no other reservation's storage is consumed. *)
Lemma task_tcb_init_private_storage_merge_initialized_image :
  forall sg args tasks entry allocation invocation,
    tasks.(taskLifecycle).(taskReservations) args.(initPrio) = Some entry ->
    entry.(creationInvocation) = invocation ->
    entry.(creationAllocation) = Some allocation ->
    task_slot_storage_rep sg allocation.(privateSlot)
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
        args allocation.(privateStorage)) **
    task_private_storage_without_priority sg tasks invocation args.(initPrio) |--
    task_private_storage sg
      (task_tcb_init_initialize_private sg args tasks entry allocation) invocation.
Proof. intros; apply task_private_storage_merge_updated_image; assumption. Qed.

Lemma task_tcb_init_private_initialization_frames_global_inv :
  forall sg args s entry allocation,
    s.(TskState).(taskLifecycle).(taskReservations) args.(initPrio) = Some entry ->
    entry.(creationAllocation) = Some allocation ->
    UCOS2_inv sg s |-- UCOS2_inv sg (replace_TskS
      (task_tcb_init_initialize_private sg args s.(TskState) entry allocation) s).
Proof. intros; apply UCOS2_inv_update_private_image; assumption. Qed.

Definition task_tcb_init_linked_image (sg : StableGlobVars) (head : option TaskID)
  (image : TCBCommonImage) : TCBCommonImage :=
  fun f => match f with
  | TCBNext => Some (encode_tcb64_link sg head)
  | TCBPrev => Some 0
  | _ => image f end.

Definition task_tcb_init_linked_layout_image (sg : StableGlobVars) (head : option TaskID)
  (image : TCBLayoutImage) : TCBLayoutImage :=
  tcb_layout_write
    (tcb_layout_write image (TCBCommonField TCBNext)
      (Some (encode_task_link sg head)))
    (TCBCommonField TCBPrev) (Some 0).

(** Ghost slot/generation come from the same detached reservation, never
    from the hook's existential byte decoder or the application OSTCBId. *)
Lemma task_tcb_init_hook_image_binds_reserved_lifetime :
  forall sg args image tasks invocation entry allocation,
    tasks.(taskLifecycle).(taskReservations) args.(initPrio) = Some entry ->
    entry.(creationInvocation) = invocation ->
    entry.(creationAllocation) = Some allocation ->
    task_tcb_init_commit_safe_image sg args image ->
    exists node,
      task_commit_identity tasks args.(initPrio) invocation node /\
      is_effectively_ready node.(stat) node.(dly) = true /\
      node.(eventPtr) = None /\ node.(eventMultiWaitEvents) = [] /\
      task_tcb_init_linked_image sg tasks.(tcbListHead) image =
        task_tcb64_image sg (task_set_links node tasks.(tcbListHead) None).
Proof.
  intros sg args image tasks invocation entry allocation Hentry Hinv Ha
    [decoded [Hp [Hprio [Hready [Hevent [Hmulti Himage]]]]]].
  exists (task_bind_identity decoded allocation.(privateSlot) allocation.(privateGeneration)).
  split.
  - exists entry, allocation; split; [exact Hentry|]. split; [exact Hinv|].
    split; [exact Ha|]. split; [reflexivity|]. split; [reflexivity|exact Hp].
  - split; [exact Hready|]. split; [exact Hevent|]. split; [exact Hmulti|].
    apply functional_extensionality; intro f; destruct f;
      try reflexivity; apply Himage; reflexivity.
Qed.

Definition task_tcb_init_commit_state (sg : StableGlobVars) (args : TaskTCBInitArgs)
  (invocation : nat) (node : TaskAbstractState) (s : UCOS2_Verify_State)
  : UCOS2_Verify_State :=
  task_sched_commit_state sg s args.(initPrio) invocation node.

Lemma task_tcb_init_commit_preserves_task_sched_invariants :
  forall sg args invocation node s,
    task_in_range sg s.(TskState) ->
    sched_in_range sg s.(TskState) s.(SchedState) ->
    task_commit_identity s.(TskState) args.(initPrio) invocation node ->
    is_effectively_ready node.(stat) node.(dly) = true ->
    let post := task_tcb_init_commit_state sg args invocation node s in
    task_in_range sg post.(TskState) /\
    sched_in_range sg post.(TskState) post.(SchedState).
Proof.
  intros sg args invocation node s Htasks Hsched Hidentity Hready; simpl; split.
  - apply task_commit_preserves_in_range; assumption.
  - apply sched_commit_preserves_in_range; assumption.
Qed.

Lemma task_tcb_init_commit_records_publication : forall sg args invocation node s,
  task_publication_happened
    (task_tcb_init_commit_state sg args invocation node s).(TskState)
    invocation node.(taskID) node.(taskGeneration).
Proof. intros; apply task_commit_records_history. Qed.

Lemma task_tcb_init_commit_preserves_physical_cache : forall sg args invocation node s,
  let post := task_tcb_init_commit_state sg args invocation node s in
  post.(SchedState).(highRdyTid) = s.(SchedState).(highRdyTid) /\
  post.(SchedState).(highRdyPrio) = s.(SchedState).(highRdyPrio) /\
  post.(SchedState).(curTaskID) = s.(SchedState).(curTaskID) /\
  post.(SchedState).(curSchedPrio) = s.(SchedState).(curSchedPrio) /\
  post.(SchedState).(ctxSwCtr) = s.(SchedState).(ctxSwCtr).
Proof. intros; repeat split; reflexivity. Qed.

Record TaskTCBInitHookContract : Type := {
  initHookEffect : TaskTCBInitHookEffect;
  initHookFrame : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop;
  initHookPreservesFrame : forall before s after s',
    initHookEffect before s after s' -> initHookFrame s s';
  initHookPreservesCommitSafety : forall sg args before s after s',
    task_tcb_init_commit_safe_image sg args before ->
    initHookEffect before s after s' ->
    task_tcb_init_commit_safe_image sg args after;
}.

Definition task_tcb_init_empty_hook_effect : TaskTCBInitHookEffect :=
  fun before s after s' => after = before /\ s' = s.

Definition task_tcb_init_empty_hook_contract : TaskTCBInitHookContract.
Proof.
  refine {| initHookEffect := task_tcb_init_empty_hook_effect;
            initHookFrame := eq |}.
  - intros before s after s' [_ H]; symmetry; exact H.
  - intros sg args before s after s' Hsafe [H _]; subst; exact Hsafe.
Defined.

(** The empty effect is only the direct body effect, not the whole open-IRQ
    call interval.  Consuming it
    as the App hooks' C contract requires the controller's selected source
    binding and a proof for those concrete implementations. *)

Inductive task_tcb_init_hook_call
  (environment : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop)
  (body : TaskTCBInitHookEffect)
  : TCBCommonImage -> UCOS2_Verify_State ->
    TCBCommonImage -> UCOS2_Verify_State -> Prop :=
| InitHookCallBody : forall image s image' s',
    body image s image' s' -> task_tcb_init_hook_call environment body image s image' s'
| InitHookCallEnvironmentBefore : forall image s middle image' s',
    environment s middle ->
    task_tcb_init_hook_call environment body image middle image' s' ->
    task_tcb_init_hook_call environment body image s image' s'
| InitHookCallEnvironmentAfter : forall image s image' middle s',
    task_tcb_init_hook_call environment body image s image' middle ->
    environment middle s' ->
    task_tcb_init_hook_call environment body image s image' s'.

Lemma task_tcb_init_empty_hook_call_preserves_private_image :
  forall environment image s image' s',
    task_tcb_init_hook_call environment task_tcb_init_empty_hook_effect
      image s image' s' -> image' = image.
Proof.
  intros environment image s image' s' Hcall; induction Hcall.
  - exact (proj1 H).
  - exact IHHcall.
  - exact IHHcall.
Qed.

(** The preceding call relation is usable only with an environment proved
    unable to access the detached private image.  It makes no equality claim
    about the initial and final global states. *)

(** C-store refinement of the independent, pointwise [task_tcb_init_raw_image].
    This list records only the target's direct writes, in source order.  It
    does not model the surrounding Restore interval or assert that it returns.
    The selected register loop has one iteration; the lemma below retains its
    actual replace_Znth effect instead of assuming an arbitrary output list. *)
Definition task_tcb_init_source_stores (args : TaskTCBInitArgs)
  : list (TCBField * Z) :=
  [(TCBStkPtr, args.(initStkPtr)); (TCBPrio, args.(initPrio));
   (TCBStat, 0); (TCBStatPend, 0); (TCBDly, 0);
   (TCBExtPtr, args.(initExtPtr)); (TCBStkSize, args.(initStkSize));
   (TCBStkBottom, args.(initStkBottom)); (TCBOpt, args.(initOpt));
   (TCBId, args.(initPublicId)); (TCBDelReq, 0);
   (TCBY, args.(initPrio) / 8); (TCBX, args.(initPrio) mod 8);
   (TCBBitY, Z.shiftl 1 (args.(initPrio) / 8));
   (TCBBitX, Z.shiftl 1 (args.(initPrio) mod 8));
   (TCBEventPtr, 0); (TCBFlagNode, 0); (TCBMsg, 0);
   (TCBTaskName, args.(initNamePointer)); (TCBReg0, 0)].

Definition task_tcb_init_apply_stores (args : TaskTCBInitArgs)
  (old : TCBCommonImage) : TCBCommonImage :=
  fold_left (fun image write =>
    tcb_write image (fst write) (Some (snd write)))
    (task_tcb_init_source_stores args) old.

Lemma task_tcb_init_source_stores_image_eq : forall args old,
  task_tcb_init_apply_stores args old = task_tcb_init_raw_image args old.
Proof.
  intros; apply functional_extensionality; intros [];
    unfold task_tcb_init_apply_stores, task_tcb_init_source_stores;
    reflexivity.
Qed.

(** Source order: Multi follows EventPtr; profiling follows FlagNode/Msg,
    before name/register initialization. CyclesStart precedes CyclesTot. *)
Definition task_tcb_init_source_layout_stores (multi profile : bool) (args : TaskTCBInitArgs)
  : list (TCBLayoutField * Z) :=
  map (fun write => (TCBCommonField (fst write), snd write))
    (firstn 16 (task_tcb_init_source_stores args)) ++
  (if multi then [(TCBEventMultiPtr, 0); (TCBEventMultiRdy, 0)] else []) ++
  map (fun write => (TCBCommonField (fst write), snd write))
    (firstn 2 (skipn 16 (task_tcb_init_source_stores args))) ++
  (if profile then [(TCBCtxSwCtr, 0); (TCBCyclesStart, 0); (TCBCyclesTot, 0);
                    (TCBStkBase, 0); (TCBStkUsed, 0)] else []) ++
  map (fun write => (TCBCommonField (fst write), snd write))
    (skipn 18 (task_tcb_init_source_stores args)).

Lemma task_tcb_init_source_layout_stores_image_eq : forall multi profile args old,
  fold_left (fun image write =>
    tcb_layout_write image (fst write) (Some (snd write)))
    (task_tcb_init_source_layout_stores multi profile args) old =
  task_tcb_init_layout_image multi profile args old.
Proof.
  intros [] [] args old; apply functional_extensionality; intros [f| | | | | | |];
    try reflexivity; destruct f; reflexivity.
Qed.

Lemma task_tcb_init_priority_shift_eq : forall prio,
  Z.shiftr prio 3 = prio / 8.
Proof. intros; rewrite Z.shiftr_div_pow2 by lia; reflexivity. Qed.

Lemma task_tcb_init_priority_mask_eq : forall prio,
  Z.land prio 7 = prio mod 8.
Proof.
  intros; change 7 with (Z.ones 3).
  rewrite Z.land_ones by lia; reflexivity.
Qed.

Lemma task_tcb_init_register_replace_eq : forall values,
  Zlength values = 1 -> replace_Znth 0 0 values = [0].
Proof.
  intros [|value [|other rest]] Hlen; try reflexivity;
    rewrite Zlength_correct in Hlen; simpl in Hlen; lia.
Qed.

Lemma task_tcb_init_register_storage_to_undef : forall base image,
  tcb_cell base TCBReg0 (image TCBReg0) |--
  UIntArray.undef_full (&(base # "os_tcb" ->ₛ "OSTCBRegTbl")) 1.
Proof.
  intros base image; unfold tcb_cell, tcb_field_address.
  destruct (image TCBReg0); [apply UIntArray.full_to_undef_full|reflexivity].
Qed.

Lemma task_tcb_init_register_storage_merge_zero : forall base image values,
  Zlength values = 1 ->
  UIntArray.full (&(base # "os_tcb" ->ₛ "OSTCBRegTbl")) 1
    (replace_Znth 0 0 values) ** tcb64_storage_without base TCBReg0 image |--
  tcb64_storage_rep base (tcb_write image TCBReg0 (Some 0)).
Proof.
  intros base image values Hlen.
  rewrite task_tcb_init_register_replace_eq by exact Hlen.
  apply (tcb64_storage_merge_updated base image TCBReg0 (Some 0)).
Qed.

(** The protected source writes the detached node's Next/Prev before updating
    the old head.  These are field-cell updates, not an assumption that the
    already-published invariant holds between the writes. *)
Lemma task_tcb_init_commit_link_writes_image_eq : forall sg head image,
  tcb_write
    (tcb_write image TCBNext (Some (encode_tcb64_link sg head)))
    TCBPrev (Some 0) = task_tcb_init_linked_image sg head image.
Proof. intros; apply functional_extensionality; intros []; reflexivity. Qed.

Lemma task_tcb_init_commit_links_merge : forall sg base head image,
  tcb_cell base TCBPrev (Some 0) **
  tcb64_storage_without base TCBPrev
    (tcb_write image TCBNext (Some (encode_tcb64_link sg head))) |--
  tcb64_storage_rep base (task_tcb_init_linked_image sg head image).
Proof.
  intros; rewrite <- task_tcb_init_commit_link_writes_image_eq.
  apply tcb64_storage_merge_updated.
Qed.

(** Concrete empty bodies selected by r3 have the direct identity instance.
    Framing this assertion preserves the SAME private allocation, including its
    retained bytes. This is not a claim that ambient global states are equal
    across a call interval with interrupts enabled. *)
Lemma task_tcb_init_empty_hook_private_frame : forall base image (frame : Assertion),
  tcb64_storage_rep base image ** frame |--
  tcb64_storage_rep base image ** frame.
Proof. reflexivity. Qed.

Lemma task_tcb_init_selected_hook_effect : forall image s,
  initHookEffect task_tcb_init_empty_hook_contract image s image s.
Proof. intros; split; reflexivity. Qed.

Definition task_tcb_init_arguments (args : TaskTCBInitArgs)
  (p top bottom public_id size extension options name : Z) : Prop :=
  args.(initPrio) = p /\ args.(initStkPtr) = top /\
  args.(initStkBottom) = bottom /\ args.(initPublicId) = public_id /\
  args.(initStkSize) = size /\ args.(initExtPtr) = extension /\
  args.(initOpt) = options /\ args.(initNamePointer) = name.

Definition task_tcb_init_global_addresses (sg : StableGlobVars)
  (free_head active_head priorities group rows count : addr) : Prop :=
  sg.(g_OSTCBFreeList) = free_head /\ sg.(g_OSTCBList) = active_head /\
  sg.(g_OSTCBPrioTbl) = priorities /\ sg.(g_OSRdyGrp) = group /\
  sg.(g_OSRdyTbl) = rows /\ sg.(g_OSTaskCtr) = count.

Definition task_tcb_init_pending (args : TaskTCBInitArgs)
  (invocation : nat) (origin : TaskInvocationOrigin)
  (s : UCOS2_Verify_State) : Prop :=
  s.(TskState).(taskLifecycle).(taskReservations) args.(initPrio) =
    Some {| creationInvocation := invocation; creationOrigin := origin;
            creationAllocation := None |}.

(** The name pointer is written into a newly published TCB.  It is not yet a
    global name root at entry, so its byte lifetime is an explicit caller
    contract.  The predicate is conditional on the selected source option;
    it does not require bytes for configurations where Task names are off. *)
Definition task_tcb_init_name_valid (sg : StableGlobVars)
  (args : TaskTCBInitArgs) (s : UCOS2_Verify_State) : Prop :=
  sg.(osKernelConfig).(cfgTaskNames) = true ->
  exists chars, readable_name s.(NameState) args.(initNamePointer) chars.

Definition task_tcb_init_entry (sg : StableGlobVars) (args : TaskTCBInitArgs)
  (invocation : nat) (origin : TaskInvocationOrigin)
  (s : UCOS2_Verify_State) : Prop :=
  UCOS2_state_inv sg s /\
  task_priority_in_range sg args.(initPrio) /\
  task_invocation_active s.(TskState) invocation origin /\
  (task_tcb_init_pending args invocation origin s /\
   task_tcb_init_name_valid sg args s).

Definition task_tcb_init_initial_entry (invocation : nat)
  (origin : TaskInvocationOrigin) : TaskCreationEntry :=
  {| creationInvocation := invocation; creationOrigin := origin;
     creationAllocation := None |}.

Definition task_tcb_init_detached_state (args : TaskTCBInitArgs)
  (invocation : nat) (origin : TaskInvocationOrigin)
  (s : UCOS2_Verify_State) (slot : TaskID) (rest : list TaskID)
  (image : TCBLayoutImage) : UCOS2_Verify_State :=
  replace_TskS (task_detach_head s.(TskState) args.(initPrio)
    (task_tcb_init_initial_entry invocation origin) slot rest image) s.

Definition task_tcb_init_free_root (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : addr :=
  encode_task_link sg (hd_error s.(TskState).(unUsedTaskStates)).

Definition task_tcb_init_free_next (sg : StableGlobVars) (rest : list TaskID) : addr :=
  encode_task_link sg (hd_error rest).

Definition task_tcb_init_free_next_image (image : TCBLayoutImage) (next : addr) : Prop :=
  image (TCBCommonField TCBNext) = Some next.

Definition task_tcb_init_no_free (s : UCOS2_Verify_State) : Prop :=
  s.(TskState).(unUsedTaskStates) = [].

Definition task_tcb_init_active_head (sg : StableGlobVars) (s : UCOS2_Verify_State) : addr :=
  encode_task_link sg s.(TskState).(tcbListHead).

Definition task_tcb_init_count (s : UCOS2_Verify_State) : Z := s.(TskState).(taskCount).

Definition task_tcb_init_ready_group (s : UCOS2_Verify_State) : Z :=
  encode_ready_grp s.(SchedState).(readyList) s.(TskState).

Definition task_tcb_init_ready_rows (s : UCOS2_Verify_State) : list Z :=
  map (encode_ready_tbl_at_or s.(SchedState).(readyList) s.(TskState)) [0;1;2;3;4;5;6;7].

Definition task_tcb_init_priority_table (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : list Z :=
  map (fun p => prio_tbl_entry_to_addr sg (s.(TskState).(prioTbl) p)) (Zrange 0 64).

Definition task_tcb_init_used_storage (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  store_used_task_map sg s.(TskState).(inUsedTaskStates).

Definition task_tcb_init_used_without_head_prev (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  EX head t, coq_prop (s.(TskState).(tcbListHead) = Some head /\
    s.(TskState).(inUsedTaskStates) head = Some t) &&
  (tcb_configured_storage_without_field sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
     (task_slot_addr sg head) (task_layout_image sg t) (TCBCommonField TCBPrev) **
   store_map_missing_i (used_task_rep sg)
     s.(TskState).(inUsedTaskStates) head).

Definition task_tcb_init_head_updated_map (s : UCOS2_Verify_State) (slot : TaskID) :=
  fun tid => match s.(TskState).(tcbListHead), s.(TskState).(inUsedTaskStates) tid with
  | Some head, Some t => if Z.eq_dec tid head
      then Some (task_set_links t t.(nextTCB) (Some slot)) else Some t
  | _, previous => previous
  end.

Definition task_tcb_init_used_with_head_prev (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (slot : TaskID) : Assertion :=
  store_used_task_map sg (task_tcb_init_head_updated_map s slot).

Definition task_tcb_init_publication_other (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  task_free_storage_rep sg s.(TskState).(taskLifecycle).(taskFreeStorage)
    s.(TskState).(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> task_tcb_init_free_root sg s **
  sched_physical_rep sg s.(SchedState) **
  task_reg_allocator_rep sg s.(TskState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s.

Definition task_tcb_init_commit_node (args : TaskTCBInitArgs)
  (acquired : UCOS2_Verify_State) (slot : TaskID) (image : TCBLayoutImage)
  : TaskAbstractState :=
  task_tcb_init_node_from_free_image args slot
    acquired.(TskState).(taskLifecycle).(taskNextGeneration)
    (match image (TCBCommonField TCBFlagsRdy) with Some flags => flags | None => 0 end)
    (tcb_layout_common_image image).

Lemma task_tcb_init_commit_node_name : forall args acquired slot image,
  (task_tcb_init_commit_node args acquired slot image).(tcbTaskName) =
    args.(initNamePointer).
Proof. intros; reflexivity. Qed.

Definition task_tcb_init_published_state (sg : StableGlobVars)
  (args : TaskTCBInitArgs) (invocation : nat)
  (acquired current : UCOS2_Verify_State) (slot : TaskID) (image : TCBLayoutImage)
  : UCOS2_Verify_State :=
  task_tcb_init_commit_state sg args invocation
    (task_tcb_init_commit_node args acquired slot image) current.

Definition task_tcb_init_commit_binding (args : TaskTCBInitArgs)
  (invocation : nat) (origin : TaskInvocationOrigin)
  (acquired current : UCOS2_Verify_State) (slot : TaskID) : Prop :=
  exists entry allocation,
    current.(TskState).(taskLifecycle).(taskReservations) args.(initPrio) = Some entry /\
    entry.(creationInvocation) = invocation /\ entry.(creationOrigin) = origin /\
    entry.(creationAllocation) = Some allocation /\ allocation.(privateSlot) = slot /\
    allocation.(privateGeneration) = acquired.(TskState).(taskLifecycle).(taskNextGeneration).

Definition task_tcb_init_public_without_free_root (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  store_used_task_map sg s.(TskState).(inUsedTaskStates) **
  task_free_storage_rep sg s.(TskState).(taskLifecycle).(taskFreeStorage)
    s.(TskState).(unUsedTaskStates) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg s.(TskState).(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> s.(TskState).(taskCount) **
  store_prio_tbl sg s.(TskState).(prioTbl) **
  task_reg_allocator_rep sg s.(TskState) **
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s.

Definition task_tcb_init_public_without_free_head (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (rest : list TaskID) : Assertion :=
  task_public_storage_without_free_head sg s.(TskState) rest **
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s.

Definition task_tcb_init_retained_storage (base : addr)
  (image : TCBCommonImage) : Assertion :=
  tcb_cell base TCBNext (image TCBNext) **
  tcb_cell base TCBPrev (image TCBPrev) **
  tcb_cell base TCBFlagsRdy (image TCBFlagsRdy) **
  tcb_cell base TCBPadding42 (image TCBPadding42) **
  tcb_cell base TCBPadding43 (image TCBPadding43).

Definition task_tcb_init_retained_without_links (base : addr)
  (image : TCBCommonImage) : Assertion :=
  tcb_cell base TCBFlagsRdy (image TCBFlagsRdy) **
  tcb_cell base TCBPadding42 (image TCBPadding42) **
  tcb_cell base TCBPadding43 (image TCBPadding43).

(** The loop invariant is a mathematical initialized-prefix property; it is
    not the C loop redefined as its own postcondition.  The unprocessed suffix
    may contain genuinely undefined reused bytes. *)
Definition task_tcb_init_register_prefix (base : addr) (done : Z) : Assertion :=
  coq_prop (0 <= done <= 1) &&
  (UIntArray.seg base 0 done (repeat 0 (Z.to_nat done)) **
   UIntArray.undef_seg base done 1).

Definition task_tcb_init_detach_observation (args : TaskTCBInitArgs)
  (invocation : nat) (origin : TaskInvocationOrigin)
  (before : UCOS2_Verify_State) (slot : TaskID) (rest : list TaskID)
  (image : TCBLayoutImage) : Prop :=
  task_detach_guard before.(TskState) args.(initPrio)
    (task_tcb_init_initial_entry invocation origin) slot rest image.

(** A normal-return observation has the actual return-code partition and the
    exact two protected mutations.  Between them the PUBLIC state follows the
    resource protocol's interference relation; it is not held equal.  The
    pending allocation and invocation identities are explicit obligations,
    not replaced by an existential node decoded after the hooks.  At return
    [published] is the last released snapshot, not a claim that the task has
    not subsequently been scheduled, deleted or reused by the environment. *)
Inductive task_tcb_init_result (critical : CriticalRegionResources)
  (sg : StableGlobVars) (args : TaskTCBInitArgs)
  (invocation : nat) (origin : TaskInvocationOrigin)
  (initial : UCOS2_Verify_State) : Z -> UCOS2_Verify_State -> Prop :=
| TaskTCBInitNoFree : forall acquired,
    critical_region_interval critical sg invocation initial acquired ->
    acquired.(TskState).(unUsedTaskStates) = [] ->
    task_tcb_init_pending args invocation origin acquired ->
    UCOS2_state_inv sg acquired ->
    task_tcb_init_result critical sg args invocation origin initial 66 acquired
| TaskTCBInitPublished : forall acquired slot rest old current entry allocation node,
    critical_region_interval critical sg invocation initial acquired ->
    task_tcb_init_detach_observation args invocation origin acquired slot rest old ->
    critical_region_interval critical sg invocation
      (task_tcb_init_detached_state args invocation origin acquired slot rest old) current ->
    current.(TskState).(taskLifecycle).(taskReservations) args.(initPrio) = Some entry ->
    entry.(creationInvocation) = invocation -> entry.(creationOrigin) = origin ->
    entry.(creationAllocation) = Some allocation ->
    allocation.(privateSlot) = slot ->
    allocation.(privateGeneration) = acquired.(TskState).(taskLifecycle).(taskNextGeneration) ->
    task_commit_identity current.(TskState) args.(initPrio) invocation node ->
    (forall field, In field (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)) ->
      task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead)
        (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) args old) field =
      task_layout_image sg
        (task_set_links node current.(TskState).(tcbListHead) None) field) ->
    UCOS2_state_inv sg current ->
    UCOS2_state_inv sg (task_tcb_init_commit_state sg args invocation node current) ->
    task_tcb_init_result critical sg args invocation origin initial 0
      (task_tcb_init_commit_state sg args invocation node current).

Lemma task_tcb_init_result_return_codes : forall critical sg args invocation origin
    initial result released,
  task_tcb_init_result critical sg args invocation origin initial result released ->
  result = 0 \/ result = 66.
Proof. intros; inversion H; auto. Qed.

Lemma task_tcb_init_result_success_has_publication :
  forall critical sg args invocation origin initial released,
  task_tcb_init_result critical sg args invocation origin initial 0 released ->
  exists slot generation, task_publication_happened released.(TskState)
    invocation slot generation.
Proof.
  intros; inversion H; subst.
  eexists; eexists; apply task_tcb_init_commit_records_publication.
Qed.

Definition task_tcb_init_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (args : TaskTCBInitArgs) (invocation : nat) (origin : TaskInvocationOrigin)
  (mask : Z) (s : UCOS2_Verify_State) : Assertion :=
  coq_prop (task_tcb_init_entry sg args invocation origin s) &&
  (interrupt_platform_running platform invocation origin mask **
   critical_region_outside critical sg invocation s).

Definition task_tcb_init_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (args : TaskTCBInitArgs) (invocation : nat) (origin : TaskInvocationOrigin)
  (mask : Z) (initial : UCOS2_Verify_State) (result : Z) : Assertion :=
  EX released, coq_prop
    (task_tcb_init_result critical sg args invocation origin initial result released) &&
    (interrupt_platform_running platform invocation origin mask **
     critical_region_outside critical sg invocation released).

Lemma interrupt_saved_value_resave : forall mask before after,
  interrupt_saved_value mask before ->
  interrupt_saved_value (armv7a_irq_fiq_mask before) after ->
  interrupt_saved_value mask after.
Proof. unfold interrupt_saved_value; intros; intuition congruence. Qed.

Lemma task_tcb_init_entry_priority_in_range : forall sg args invocation origin s,
  task_tcb_init_entry sg args invocation origin s ->
  0 <= args.(initPrio) < 64 /\
  0 <= args.(initPrio) / 8 < 8 /\ 0 <= args.(initPrio) mod 8 < 8.
Proof.
  intros sg args invocation origin s [Hvalid [Hprio _]].
  destruct Hvalid as [[Hsg _] _].
  assert (Hlowest : sg.(osLowestPrio) = 63) by
    (unfold valid_stable_glob_vars in Hsg; tauto).
  unfold task_priority_in_range in Hprio; rewrite Hlowest in Hprio.
  split; [lia|]. split.
  - split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
  - apply Z.mod_pos_bound; lia.
Qed.

Lemma task_tcb_init_raw_split_free_root : forall sg s,
  UCOS2_raw_rep sg s --||--
  sg.(g_OSTCBFreeList) # Ptr |-> task_tcb_init_free_root sg s **
    task_tcb_init_public_without_free_root sg s.
Proof.
  intros; unfold UCOS2_raw_rep, task_shared_rep, task_public_storage,
    task_tcb_init_free_root, task_tcb_init_public_without_free_root, UCOS2_raw_rep_missing_task_storage_sched;
    split; entailer!.
Qed.

Lemma task_tcb_init_raw_split_publication : forall sg s,
  UCOS2_raw_rep sg s --||--
  sg.(g_OSTCBList) # Ptr |-> task_tcb_init_active_head sg s **
  task_tcb_init_used_storage sg s **
  sg.(g_OSTaskCtr) # UChar |-> task_tcb_init_count s **
  sg.(g_OSRdyGrp) # UChar |-> task_tcb_init_ready_group s **
  UCharArray.full sg.(g_OSRdyTbl) 8 (task_tcb_init_ready_rows s) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 (task_tcb_init_priority_table sg s) **
  task_tcb_init_publication_other sg s.
Proof.
  intros; unfold UCOS2_raw_rep, task_shared_rep, task_public_storage,
    task_tcb_init_active_head, task_tcb_init_used_storage, task_tcb_init_count,
    task_tcb_init_ready_group, task_tcb_init_ready_rows,
    task_tcb_init_priority_table, task_tcb_init_publication_other,
    task_tcb_init_free_root, store_prio_tbl, sched_raw_rep, UCOS2_raw_rep_missing_task_storage_sched.
  rewrite sched_rows_array_equiv.
  unfold sched_row_values; split; entailer!.
Qed.

Lemma task_tcb_init_detached_flags_defined : forall sg args invocation origin
    acquired slot rest image,
  task_tcb_init_entry sg args invocation origin acquired ->
  task_tcb_init_detach_observation args invocation origin acquired slot rest image ->
  exists flags, image (TCBCommonField TCBFlagsRdy) = Some flags.
Proof.
  intros sg args invocation origin acquired slot rest image [Hvalid _] Hdetach.
  destruct Hvalid as [_ [Htasks _]].
  assert (Hreuse : task_free_reuse_closure acquired.(TskState)) by
    (unfold task_in_range in Htasks; tauto).
  destruct Hdetach as [_ [_ [_ Himage]]].
  eapply Hreuse; exact Himage.
Qed.

Lemma task_tcb_init_commit_binding_identity : forall args invocation origin
    acquired current slot image,
  task_tcb_init_commit_binding args invocation origin acquired current slot ->
  task_commit_identity current.(TskState) args.(initPrio) invocation
    (task_tcb_init_commit_node args acquired slot image).
Proof.
  intros args invocation origin acquired current slot image
    [entry [allocation [He [Hi [Ho [Ha [Hs Hg]]]]]]].
  exists entry, allocation; unfold task_tcb_init_commit_node,
    task_tcb_init_node_from_free_image; simpl; repeat split; congruence.
Qed.

Lemma task_tcb_init_commit_node_layout_field_eq : forall sg args acquired current slot image flags,
  image (TCBCommonField TCBFlagsRdy) = Some flags ->
  forall field, In field (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)) ->
  task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead)
    (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) args image) field =
  task_layout_image sg (task_set_links
    (task_tcb_init_commit_node args acquired slot image)
    current.(TskState).(tcbListHead) None) field.
Proof.
  intros sg args acquired current slot image flags Hflags field Hin.
  unfold task_tcb_init_commit_node; rewrite Hflags.
  destruct sg.(osKernelConfig).(cfgEventMultiEnabled), sg.(osKernelConfig).(cfgTaskProfile);
    destruct field as [f| | | | | | |]; try destruct f;
    try reflexivity; try exact Hflags; simpl in Hin; intuition discriminate.
Qed.

(** Equality is required only on fields present in the chosen C layout.
    QCP's field-map monotonicity transports the actual owned bytes; no absent
    Multi cell is manufactured when using the 64-byte configuration. *)
Lemma task_tcb_init_linked_storage_rep : forall sg args acquired current slot image flags,
  image (TCBCommonField TCBFlagsRdy) = Some flags ->
  task_slot_storage_rep sg slot
    (task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead)
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) args image)) |--
  used_task_rep sg slot (task_set_links
    (task_tcb_init_commit_node args acquired slot image) current.(TskState).(tcbListHead) None).
Proof.
  intros sg args acquired current slot image flags Hflags.
  unfold used_task_rep, task_slot_storage_rep, tcb_configured_storage_rep.
  apply TaskFieldStorage.store_fields_mono; intros field Hin.
  rewrite (task_tcb_init_commit_node_layout_field_eq sg args acquired current slot
    image flags Hflags field Hin); reflexivity.
Qed.

Lemma task_tcb_init_published_result : forall critical sg args invocation origin initial
    acquired slot rest image current,
  task_tcb_init_entry sg args invocation origin acquired ->
  critical_region_interval critical sg invocation initial acquired ->
  task_tcb_init_detach_observation args invocation origin acquired slot rest image ->
  critical_region_interval critical sg invocation
    (task_tcb_init_detached_state args invocation origin acquired slot rest image) current ->
  task_tcb_init_commit_binding args invocation origin acquired current slot ->
  UCOS2_state_inv sg current ->
  task_tcb_init_result critical sg args invocation origin initial 0
    (task_tcb_init_published_state sg args invocation acquired current slot image).
Proof.
  intros critical sg args invocation origin initial acquired slot rest image current
    Hentry Hinter Hdetach Hopen Hbinding Hvalid.
  pose proof (proj2 (proj2 (proj2 Hentry))) as [Hpending Hname].
  pose proof (critical_region_interval_preserves_name_state critical sg invocation
    (task_tcb_init_detached_state args invocation origin acquired slot rest image) current
    Hopen) as Hname_frame.
  assert (Hname_current : sg.(osKernelConfig).(cfgTaskNames) = true ->
      exists chars, readable_name current.(NameState)
        (task_tcb_init_commit_node args acquired slot image).(tcbTaskName) chars).
  { intros Htasknames.
    destruct (Hname Htasknames) as [chars Hread].
    exists chars; rewrite (task_tcb_init_commit_node_name args acquired slot image).
    rewrite <- Hname_frame; exact Hread. }
  pose proof (task_tcb_init_commit_binding_identity args invocation origin
    acquired current slot image Hbinding) as Hidentity.
  destruct (task_tcb_init_detached_flags_defined sg args invocation origin
    acquired slot rest image Hentry Hdetach) as [flags Hflags].
  destruct Hbinding as [entry [allocation [He [Hi [Ho [Ha [Hs Hg]]]]]]].
  unfold task_tcb_init_published_state.
  eapply TaskTCBInitPublished with (acquired := acquired) (slot := slot)
    (rest := rest) (old := image) (entry := entry) (allocation := allocation);
    try eassumption.
  - eapply task_tcb_init_commit_node_layout_field_eq; eassumption.
  - unfold task_tcb_init_commit_state.
    eapply UCOS2_task_commit_preserves_validity.
    + exact Hvalid.
    + exact Hidentity.
    + unfold task_tcb_init_commit_node, task_tcb_init_node_from_free_image,
        is_effectively_ready, task_non_suspension_bits, task_is_suspended.
      cbn; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact Hname_current.
Qed.

Lemma task_tcb_init_post_from_released_result : forall platform critical sg args
    invocation origin mask initial result released saved,
  interrupt_saved_value mask saved ->
  task_tcb_init_result critical sg args invocation origin initial result released ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
  critical_region_outside critical sg invocation released |--
  task_tcb_init_post platform critical sg args invocation origin mask initial result.
Proof.
  intros platform critical sg args invocation origin mask initial result released saved
    [_ Hmask] Hresult; rewrite Hmask; unfold task_tcb_init_post.
  Exists released; entailer!.
Qed.

(** Local initialization may forget the previous values of precisely the
    fields it overwrites.  Retained links, FlagsRdy and padding stay owned. *)
Definition task_tcb_init_written_storage (base : addr) (image : TCBCommonImage)
  : Assertion :=
  tcb64_fields_rep base
    (filter task_tcb_init_written_field tcb_fields) image.

Lemma task_tcb_init_storage_split_written : forall base image,
  tcb64_storage_rep base image --||--
    task_tcb_init_retained_storage base image **
    task_tcb_init_written_storage base image.
Proof.
  intros; unfold tcb64_storage_rep, task_tcb_init_retained_storage,
    task_tcb_init_written_storage, tcb64_fields_rep, tcb_fields.
  cbn [filter task_tcb_init_written_field].
  repeat rewrite TaskFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite !TaskFieldStorage.store_fields_nil.
  split; entailer!.
Qed.

Lemma task_tcb_init_cell_to_undef : forall base field value,
  tcb_cell base field value |-- tcb_cell base field None.
Proof.
  intros base field [value | ]; [|reflexivity].
  destruct field; cbn [tcb_cell];
    first [apply store_ptr_undef_store_ptr | apply store_uint_undef_store_uint |
      apply store_ushort_undef_store_ushort | apply store_uchar_undef_store_uchar |
      apply tcb_padding_cell_forget |
      apply UIntArray.full_to_undef_full].
Qed.

Lemma task_tcb_init_fields_to_undef : forall fields base image,
  tcb64_fields_rep base fields image |--
    tcb64_fields_rep base fields (fun _ => None).
Proof.
  intros; apply TaskFieldStorage.store_fields_mono.
  intros; apply task_tcb_init_cell_to_undef.
Qed.

Lemma task_tcb_init_storage_open_initialization : forall base image,
  tcb64_storage_rep base image |--
    task_tcb_init_retained_storage base image **
    task_tcb_init_written_storage base (fun _ => None).
Proof.
  intros; rewrite task_tcb_init_storage_split_written.
  unfold task_tcb_init_written_storage.
  sep_apply_l_atomic (task_tcb_init_fields_to_undef
    (filter task_tcb_init_written_field tcb_fields) base image).
  entailer!.
Qed.

(** These are the two acquired-state transports used by the annotated C
    client.  They are derived from certified source traces, not fields added
    to the interrupt primitive, and do not equate acquired states. *)
Lemma task_tcb_init_acquire_entry : forall critical sg args invocation origin before after,
  task_tcb_init_entry sg args invocation origin before ->
  critical_region_interval critical sg invocation before after ->
  task_tcb_init_entry sg args invocation origin after.
Proof.
  intros critical sg args invocation origin before after
    [Hvalid [Hpriority [Hactive [Hpending Hname]]]] Hinterval.
  destruct (critical_region_interval_transports_resources
    critical sg invocation before after Hinterval Hvalid) as [Hpost [Hframe Hresume]].
  pose proof (critical_region_interval_preserves_name_state critical sg invocation
    before after Hinterval) as Hname_frame.
  split; [exact Hpost|].
  split; [exact Hpriority|].
  split; [apply Hresume; exact Hactive|].
  split.
  - unfold task_tcb_init_pending in *.
    eapply task_creation_frame_lookup; [exact Hframe|exact Hpending|reflexivity].
  - unfold task_tcb_init_name_valid in *; intros Htasknames.
    destruct (Hname Htasknames) as [chars Hread].
    exists chars; rewrite <- Hname_frame; exact Hread.
Qed.

Lemma task_tcb_init_detach_preserves_validity : forall sg args invocation origin acquired slot rest image,
  task_tcb_init_entry sg args invocation origin acquired ->
  task_tcb_init_detach_observation args invocation origin acquired slot rest image ->
  UCOS2_state_inv sg
    (task_tcb_init_detached_state args invocation origin acquired slot rest image).
Proof.
  intros sg args invocation origin acquired slot rest image Hentry Hdetach.
  apply UCOS2_task_detach_preserves_validity; [exact (proj1 Hentry)|exact Hdetach].
Qed.

Lemma task_tcb_init_acquire_commit :
  forall critical sg args invocation origin acquired slot rest image current,
  task_tcb_init_entry sg args invocation origin acquired ->
  task_tcb_init_detach_observation args invocation origin acquired slot rest image ->
  critical_region_interval critical sg invocation
    (task_tcb_init_detached_state args invocation origin acquired slot rest image) current ->
  UCOS2_state_inv sg current /\
  task_tcb_init_commit_binding args invocation origin acquired current slot /\
  task_invocation_active current.(TskState) invocation origin.
Proof.
  intros critical sg args invocation origin acquired slot rest image current Hentry Hdetach Hinterval.
  pose proof (task_tcb_init_detach_preserves_validity sg args invocation origin acquired
    slot rest image Hentry Hdetach) as Hvalid.
  destruct (critical_region_interval_transports_resources _ _ _ _ _ Hinterval Hvalid)
    as [Hpost [Hframe Hresume]].
  split; [exact Hpost|]. split.
  - unfold task_tcb_init_commit_binding.
    exists {| creationInvocation := invocation; creationOrigin := origin;
      creationAllocation := Some {| privateSlot := slot;
        privateGeneration := acquired.(TskState).(taskLifecycle).(taskNextGeneration);
        privateStorage := image |} |}.
    exists {| privateSlot := slot;
      privateGeneration := acquired.(TskState).(taskLifecycle).(taskNextGeneration);
      privateStorage := image |}; split.
    + eapply task_creation_frame_lookup; [exact Hframe| |reflexivity].
      simpl; destruct (Z.eq_dec args.(initPrio) args.(initPrio)); [reflexivity|contradiction].
    + repeat split; reflexivity.
  - apply Hresume; exact (proj1 (proj2 (proj2 Hentry))).
Qed.

Lemma task_tcb_init_acquire_entry_open : forall critical sg args invocation origin before after,
  task_tcb_init_entry sg args invocation origin before ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_raw_rep sg after |--
    coq_prop (task_tcb_init_entry sg args invocation origin after) && UCOS2_inv sg after.
Proof.
  intros; pose proof (task_tcb_init_acquire_entry _ _ _ _ _ _ _ H H0) as Hentry.
  unfold UCOS2_inv; entailer!; exact (proj1 Hentry).
Qed.

Lemma task_tcb_init_acquire_commit_open :
  forall critical sg args invocation origin acquired slot rest image current,
  task_tcb_init_entry sg args invocation origin acquired ->
  task_tcb_init_detach_observation args invocation origin acquired slot rest image ->
  critical_region_interval critical sg invocation
    (task_tcb_init_detached_state args invocation origin acquired slot rest image) current ->
  UCOS2_raw_rep sg current |--
    coq_prop (task_tcb_init_commit_binding args invocation origin acquired current slot) &&
    UCOS2_inv sg current.
Proof.
  intros; destruct (task_tcb_init_acquire_commit _ _ _ _ _ _ _ _ _ _ H H0 H1)
    as [Hvalid [Hbinding Hactive]].
  unfold UCOS2_inv; entailer!.
Qed.

(** Return 66 leaves the caller's Pending fragment available for the real
    Create caller's rollback; OS_TCBInit itself performs no rollback store. *)
Lemma task_tcb_init_no_free_pending_agreement :
  forall critical sg args invocation origin initial released,
  task_tcb_init_result critical sg args invocation origin initial 66 released ->
  task_creation_fragment_agrees released.(TskState)
    (task_creation_singleton args.(initPrio) (task_tcb_init_initial_entry invocation origin)) /\
  task_rollback_guard released.(TskState) args.(initPrio) invocation.
Proof.
  intros critical sg args invocation origin initial released Hresult.
  inversion Hresult; subst.
  split.
  - apply task_creation_singleton_agreement; assumption.
  - eexists; split; [eassumption|]; split; reflexivity.
Qed.

Lemma task_tcb_init_detach_merge_invariant : forall sg args invocation origin acquired slot rest image,
  task_tcb_init_entry sg args invocation origin acquired ->
  task_tcb_init_detach_observation args invocation origin acquired slot rest image ->
  sg.(g_OSTCBFreeList) # Ptr |-> task_tcb_init_free_next sg rest **
    task_tcb_init_public_without_free_head sg acquired rest |--
  UCOS2_inv sg
    (task_tcb_init_detached_state args invocation origin acquired slot rest image).
Proof.
  intros sg args invocation origin acquired slot rest image Hentry Hdetach.
  pose proof (task_tcb_init_detach_preserves_validity _ _ _ _ _ _ _ _ Hentry Hdetach) as Hvalid.
  pose proof (proj1 (proj2 (proj1 Hentry))) as Htasks.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj1 Htasks))))) as Hnd.
  unfold task_tcb_init_public_without_free_head, task_tcb_init_free_next.
  sep_apply_l_atomic (task_public_storage_merge_detached_free_head sg acquired.(TskState)
    args.(initPrio) (task_tcb_init_initial_entry invocation origin) slot rest image Hnd (proj1 Hdetach)).
  pose proof (sched_raw_rep_change_task_index sg acquired.(TskState)
    (task_detach_head acquired.(TskState) args.(initPrio)
      (task_tcb_init_initial_entry invocation origin) slot rest image) acquired.(SchedState) eq_refl)
    as Hsched.
  pose proof (UCOS2_raw_rep_missing_task_storage_sched_task_map_frame sg acquired
    (task_detach_head acquired.(TskState) args.(initPrio)
      (task_tcb_init_initial_entry invocation origin) slot rest image) eq_refl eq_refl) as Hresidual.
  rewrite Hsched, Hresidual.
  unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep, task_tcb_init_detached_state, UCOS2_raw_rep_missing_task_storage_sched.
  entailer!.
Qed.

(** At the second acquire the local image is synchronized with the reopened
    authority, while the initialized private bytes remain separately owned.
    The subsequent exact commit consumes this entry, so synchronization does
    not change the C-facing published state. *)
Lemma task_tcb_init_acquire_private_image :
  forall critical sg args invocation origin acquired slot rest old current,
  task_tcb_init_entry sg args invocation origin acquired ->
  task_tcb_init_detach_observation args invocation origin acquired slot rest old ->
  critical_region_interval critical sg invocation
    (task_tcb_init_detached_state args invocation origin acquired slot rest old) current ->
  UCOS2_raw_rep sg current **
    task_slot_storage_rep sg slot (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) args old) |--
  EX entry allocation,
    coq_prop (current.(TskState).(taskLifecycle).(taskReservations) args.(initPrio) = Some entry /\
      entry.(creationInvocation) = invocation /\ entry.(creationOrigin) = origin /\
      entry.(creationAllocation) = Some allocation /\ allocation.(privateSlot) = slot /\
      allocation.(privateGeneration) = acquired.(TskState).(taskLifecycle).(taskNextGeneration) /\
      task_tcb_init_published_state sg args invocation acquired
        (replace_TskS (task_update_private_image current.(TskState) args.(initPrio)
          entry allocation (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) args old)) current) slot old =
      task_tcb_init_published_state sg args invocation acquired current slot old) &&
    (UCOS2_inv sg
      (replace_TskS (task_update_private_image current.(TskState) args.(initPrio)
        entry allocation (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) args old)) current) **
     task_slot_storage_rep sg slot (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) args old)).
Proof.
  intros critical sg args invocation origin acquired slot rest old current Hentry Hdetach Hinterval.
  destruct (task_tcb_init_acquire_commit _ _ _ _ _ _ _ _ _ _ Hentry Hdetach Hinterval)
    as [Hvalid [Hbinding Hactive]].
  destruct Hbinding as [entry [allocation [Hget [Hinv [Horigin [Halloc [Hslot Hgeneration]]]]]]].
  assert (Hpublish : task_tcb_init_published_state sg args invocation acquired
      (replace_TskS (task_update_private_image current.(TskState) args.(initPrio)
        entry allocation (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) args old)) current) slot old =
      task_tcb_init_published_state sg args invocation acquired current slot old).
  { apply task_sched_commit_after_private_image_eq. }
  Exists entry allocation.
  sep_apply_l_atomic (critical_region_interval_open_invariant critical sg invocation
    (task_tcb_init_detached_state args invocation origin acquired slot rest old) current Hinterval
    (task_tcb_init_detach_preserves_validity _ _ _ _ _ _ _ _ Hentry Hdetach)).
  sep_apply_l_atomic (UCOS2_inv_update_private_image sg current args.(initPrio)
    entry allocation (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) args old) Hget Halloc).
  entailer!.
Qed.

Lemma task_tcb_init_storage_merge_initialized : forall base args image,
  task_tcb_init_retained_storage base image **
    task_tcb_init_written_storage base (task_tcb_init_raw_image args image) |--
  tcb64_storage_rep base (task_tcb_init_raw_image args image).
Proof.
  intros; rewrite task_tcb_init_storage_split_written.
  unfold task_tcb_init_retained_storage; cbn [task_tcb_init_raw_image]; reflexivity.
Qed.

(** Full-layout initialization ownership.  The field inventories are a
    partition of the existing QCP-backed representation, not another TCB
    map.  In particular, retained padding moves with the selected layout. *)
Definition task_tcb_init_layout_retained_storage (multi profile : bool) (base : addr)
  (image : TCBLayoutImage) : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
    (filter (fun field => negb (task_tcb_init_layout_written_field multi profile field))
      (tcb_configured_fields multi profile)) image.

Definition task_tcb_init_layout_written_storage (multi profile : bool) (base : addr)
  (image : TCBLayoutImage) : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
    (filter (task_tcb_init_layout_written_field multi profile) (tcb_configured_fields multi profile)) image.

Lemma task_tcb_init_layout_storage_split_written : forall multi profile base image,
  tcb_configured_storage_rep multi profile base image --||--
    task_tcb_init_layout_retained_storage multi profile base image **
    task_tcb_init_layout_written_storage multi profile base image.
Proof.
  intros [] [] base image; unfold tcb_configured_storage_rep,
    task_tcb_init_layout_retained_storage, task_tcb_init_layout_written_storage,
    tcb_configured_fields, tcb_profile_fields, tcb_fields;
  cbn [map firstn skipn app filter task_tcb_init_layout_written_field task_tcb_init_written_field negb];
  repeat rewrite TaskFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate);
  rewrite !TaskFieldStorage.store_fields_nil; split; entailer!.
Qed.

Lemma task_tcb_init_layout_storage_open_initialization : forall multi profile base image,
  tcb_configured_storage_rep multi profile base image |--
    task_tcb_init_layout_retained_storage multi profile base image **
    task_tcb_init_layout_written_storage multi profile base (fun _ => None).
Proof.
  intros; rewrite task_tcb_init_layout_storage_split_written.
  apply derivable1_sepcon_mono; [reflexivity|].
  unfold task_tcb_init_layout_written_storage; apply TaskFieldStorage.store_fields_mono.
  intros [field| | | | | | |] Hin; destruct (image _) as [value|]; try reflexivity.
  - destruct field; cbn [tcb_layout_cell tcb_cell];
      first [apply store_ptr_undef_store_ptr | apply store_uint_undef_store_uint |
        apply store_ushort_undef_store_ushort | apply store_uchar_undef_store_uchar |
        apply tcb_padding_cell_forget |
        apply UIntArray.full_to_undef_full].
  - apply store_ptr_undef_store_ptr.
  - apply store_ptr_undef_store_ptr.
  - apply store_uint_undef_store_uint.
  - apply store_uint_undef_store_uint.
  - apply store_uint_undef_store_uint.
  - apply store_ptr_undef_store_ptr.
  - apply store_uint_undef_store_uint.
Qed.

Lemma task_tcb_init_layout_retained_storage_initialized_eq : forall multi profile base args image,
  task_tcb_init_layout_retained_storage multi profile base (task_tcb_init_layout_image multi profile args image) =
  task_tcb_init_layout_retained_storage multi profile base image.
Proof.
  intros; unfold task_tcb_init_layout_retained_storage, TaskFieldStorage.store_fields.
  f_equal; apply functional_extensionality; intro field;
    unfold Ucos2Verify.lib.field_storage.fields_map.
  destruct in_dec as [Hin|Hnot]; [|reflexivity].
  apply filter_In in Hin; destruct Hin as [_ Hwritten].
  apply Bool.negb_true_iff in Hwritten.
  rewrite task_tcb_init_layout_untouched by exact Hwritten; reflexivity.
Qed.

Lemma task_tcb_init_layout_storage_merge_initialized : forall multi profile base args image,
  task_tcb_init_layout_retained_storage multi profile base image **
    task_tcb_init_layout_written_storage multi profile base (task_tcb_init_layout_image multi profile args image) |--
  tcb_configured_storage_rep multi profile base (task_tcb_init_layout_image multi profile args image).
Proof.
  intros; rewrite task_tcb_init_layout_storage_split_written.
  rewrite task_tcb_init_layout_retained_storage_initialized_eq; reflexivity.
Qed.

Require Import Coq.Sorting.Permutation.
Lemma shiftl_one_byte_in_range__private_initialization : forall n,
  0 <= n < 8 -> 0 <= Z.shiftl 1 n < 256.
Proof.
  intros n Hrange.
  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/
          n = 4 \/ n = 5 \/ n = 6 \/ n = 7) as Hcases by lia.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    cbn; lia.
Qed.
Lemma task_slot_addr_positive__publication_and_returns : forall sg tid,
  valid_stable_glob_vars sg -> task_slot_in_range sg tid ->
  0 < task_slot_addr sg tid.
Proof.
  intros sg tid Hsg Hslot.
  pose proof (valid_stable_address_pos sg sg.(g_OSTCBTbl) Hsg
    ltac:(unfold stable_global_addresses; simpl; auto)) as Hbase.
  unfold task_slot_addr, task_slot_in_range, tcb_configured_size, tcb_layout_size in *.
  destruct sg.(osKernelConfig).(cfgEventMultiEnabled), sg.(osKernelConfig).(cfgTaskProfile); lia.
Qed.
Lemma task_active_head_lookup__publication_and_returns : forall sg tasks head,
  task_in_range sg tasks -> tasks.(tcbListHead) = Some head ->
  exists t, tasks.(inUsedTaskStates) head = Some t.
Proof.
  intros sg tasks head Htasks Hsome.
  destruct Htasks as [_ [Hclosure _]].
  destruct Hclosure as [Hnd [Hhead [Hcount [Hlookup Hlinks]]]].
  rewrite Hhead in Hsome.
  destruct tasks.(taskLifecycle).(taskActiveOrder) as [|first tail];
    simpl in Hsome; [discriminate|].
  inversion Hsome; subst first.
  apply (proj1 (Hlookup head)); left; reflexivity.
Qed.
Lemma task_tcb_init_free_root_zero__publication_and_returns : forall sg s,
  UCOS2_state_inv sg s -> task_tcb_init_free_root sg s = 0 ->
  s.(TskState).(unUsedTaskStates) = [].
Proof.
  intros sg s [[Hsg _] [Htasks _]] Hzero.
  destruct Htasks as [[Hpool _] _].
  unfold task_tcb_init_free_root in Hzero.
  destruct s.(TskState).(unUsedTaskStates) as [|tid rest] eqn:Hfree; [reflexivity|].
  assert (Hslot : task_slot_in_range sg tid).
  { apply (proj2 (Hpool tid)); right; left; left; reflexivity. }
  pose proof (task_slot_addr_positive__publication_and_returns sg tid Hsg Hslot).
  simpl in Hzero; lia.
Qed.
Lemma task_tcb_init_active_head_zero__publication_and_returns : forall sg s,
  UCOS2_state_inv sg s -> task_tcb_init_active_head sg s = 0 ->
  s.(TskState).(tcbListHead) = None.
Proof.
  intros sg s [[Hsg _] [Htasks _]] Hzero.
  unfold task_tcb_init_active_head in Hzero.
  destruct s.(TskState).(tcbListHead) as [head|] eqn:Hhead; [|reflexivity].
  destruct (task_active_head_lookup__publication_and_returns sg s.(TskState)
    head Htasks Hhead) as [t Hget].
  assert (Hslot : task_slot_in_range sg head).
  { apply (proj2 (proj1 (proj1 Htasks) head)); left; eauto. }
  pose proof (task_slot_addr_positive__publication_and_returns sg head Hsg Hslot).
  simpl in Hzero; lia.
Qed.
Lemma task_tcb_init_used_split_head_prev__publication_and_returns : forall sg s,
  UCOS2_state_inv sg s -> task_tcb_init_active_head sg s <> 0 ->
  task_tcb_init_used_storage sg s |--
  EX previous, tcb_cell (task_tcb_init_active_head sg s) TCBPrev (Some previous) **
    task_tcb_init_used_without_head_prev sg s.
Proof.
  intros sg s Hvalid Hnonzero.
  destruct s.(TskState).(tcbListHead) as [head|] eqn:Hhead.
  2: { unfold task_tcb_init_active_head in Hnonzero; rewrite Hhead in Hnonzero;
       contradiction. }
  destruct (task_active_head_lookup__publication_and_returns sg s.(TskState)
    head (proj1 (proj2 Hvalid)) Hhead) as [t Hget].
  unfold task_tcb_init_used_storage, store_used_task_map.
  sep_apply_l_atomic (store_map_split (used_task_rep sg) head t _ Hget).
  unfold used_task_rep, task_slot_storage_rep at 1.
  sep_apply_l_atomic (tcb_configured_storage_split_field sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg head) (task_layout_image sg t) (TCBCommonField TCBPrev)
    (tcb_configured_common_field_in _ _ TCBPrev)).
  unfold task_tcb_init_used_without_head_prev, task_tcb_init_active_head.
  rewrite Hhead.
  Exists (encode_task_link sg t.(prevTCB)) head t.
  entailer!.
Qed.
Lemma task_prev_write_image_eq__publication_and_returns : forall sg t slot,
  tcb_layout_write (task_layout_image sg t) (TCBCommonField TCBPrev)
    (Some (task_slot_addr sg slot)) =
  task_layout_image sg (task_set_links t t.(nextTCB) (Some slot)).
Proof.
  intros; apply functional_extensionality; intros [f| | | | | | |]; try reflexivity; destruct f; reflexivity.
Qed.
Lemma task_tcb_init_used_merge_head_prev__publication_and_returns : forall sg s slot,
  tcb_cell (task_tcb_init_active_head sg s) TCBPrev
    (Some (task_slot_addr sg slot)) **
  task_tcb_init_used_without_head_prev sg s |--
  task_tcb_init_used_with_head_prev sg s slot.
Proof.
  intros; unfold task_tcb_init_used_without_head_prev.
  Intros head t.
  destruct H as [Hhead Hget].
  unfold task_tcb_init_active_head; rewrite Hhead; cbn [encode_task_link].
  pose proof (tcb_configured_storage_merge_updated_field sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg head) (task_layout_image sg t) (TCBCommonField TCBPrev)
    (Some (task_slot_addr sg slot)) (tcb_configured_common_field_in _ _ TCBPrev)) as Hmerge.
  cbn [tcb_layout_cell] in Hmerge.
  sep_apply_l_atomic Hmerge.
  rewrite task_prev_write_image_eq__publication_and_returns.
  assert (Hoff : forall tid, tid <> head -> s.(TskState).(inUsedTaskStates) tid =
      task_tcb_init_head_updated_map s slot tid).
  { intros tid Hne; unfold task_tcb_init_head_updated_map; rewrite Hhead.
    destruct (s.(TskState).(inUsedTaskStates) tid); [|reflexivity].
    destruct (Z.eq_dec tid head); congruence. }
  rewrite (store_map_missing_i_equiv _ _ _ head Hoff).
  unfold task_tcb_init_used_with_head_prev, store_used_task_map.
  assert (Hupdated : task_tcb_init_head_updated_map s slot head =
    Some (task_set_links t t.(nextTCB) (Some slot))).
  { unfold task_tcb_init_head_updated_map; rewrite Hhead, Hget.
    destruct (Z.eq_dec head head); [reflexivity|contradiction]. }
  intros heap [node_heap [map_heap [Hjoin [Hnode Hmap]]]].
  apply (store_map_merge (used_task_rep sg) head
    (task_set_links t t.(nextTCB) (Some slot)) _ Hupdated heap).
  exists map_heap, node_heap.
  split; [apply UCOS2_C_Rules.join_comm; exact Hjoin|split; assumption].
Qed.
Lemma task_tcb_init_storage_open_links__publication_and_returns : forall base args image,
  tcb64_storage_rep base (task_tcb_init_raw_image args image) |--
  task_tcb_init_retained_without_links base image **
  task_tcb_init_written_storage base (task_tcb_init_raw_image args image) **
  tcb_cell base TCBNext None ** tcb_cell base TCBPrev None.
Proof.
  intros; rewrite task_tcb_init_storage_split_written.
  unfold task_tcb_init_retained_storage, task_tcb_init_retained_without_links.
  cbn [task_tcb_init_raw_image].
  sep_apply_l_atomic (task_tcb_init_cell_to_undef base TCBNext (image TCBNext)).
  sep_apply_l_atomic (task_tcb_init_cell_to_undef base TCBPrev (image TCBPrev)).
  entailer!.
Qed.
Lemma ready_group_permutation_eq__publication_and_returns : forall xs ys tasks,
  Permutation xs ys -> encode_ready_grp xs tasks = encode_ready_grp ys tasks.
Proof.
  intros xs ys tasks Hperm; induction Hperm; cbn [encode_ready_grp].
  - reflexivity.
  - destruct (tasks.(inUsedTaskStates) x); rewrite IHHperm; reflexivity.
  - destruct (tasks.(inUsedTaskStates) x); destruct (tasks.(inUsedTaskStates) y);
      try reflexivity.
    rewrite !Z.lor_assoc; f_equal; apply Z.lor_comm.
  - etransitivity; eassumption.
Qed.
Lemma ready_row_permutation_eq__publication_and_returns : forall xs ys tasks y,
  Permutation xs ys -> encode_ready_tbl_at_or xs tasks y = encode_ready_tbl_at_or ys tasks y.
Proof.
  intros xs ys tasks y Hperm; unfold encode_ready_tbl_at_or; induction Hperm; simpl.
  - reflexivity.
  - destruct (tasks.(inUsedTaskStates) x); [destruct Z.eqb|]; rewrite IHHperm; reflexivity.
  - destruct (tasks.(inUsedTaskStates) x); destruct (tasks.(inUsedTaskStates) y0);
      try reflexivity; repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      try reflexivity.
    rewrite !Z.lor_assoc; f_equal; apply Z.lor_comm.
  - etransitivity; eassumption.
Qed.
Lemma ready_group_priority_observation_eq__publication_and_returns : forall ready before after,
  (forall tid, In tid ready ->
    option_map curPrio (before.(inUsedTaskStates) tid) =
    option_map curPrio (after.(inUsedTaskStates) tid)) ->
  encode_ready_grp ready before = encode_ready_grp ready after.
Proof.
  induction ready as [|tid rest IH]; intros before after Hobs; [reflexivity|].
  specialize (IH before after ltac:(intros; apply Hobs; right; assumption)).
  pose proof (Hobs tid (or_introl eq_refl)) as Hhead.
  cbn [encode_ready_grp]; rewrite IH.
  destruct (before.(inUsedTaskStates) tid); destruct (after.(inUsedTaskStates) tid);
    simpl in Hhead; try discriminate; try reflexivity.
  injection Hhead as Heq; rewrite Heq; reflexivity.
Qed.
Lemma ready_row_priority_observation_eq__publication_and_returns : forall ready before after y,
  (forall tid, In tid ready ->
    option_map curPrio (before.(inUsedTaskStates) tid) =
    option_map curPrio (after.(inUsedTaskStates) tid)) ->
  encode_ready_tbl_at_or ready before y = encode_ready_tbl_at_or ready after y.
Proof.
  induction ready as [|tid rest IH]; intros before after y Hobs; [reflexivity|].
  specialize (IH before after y ltac:(intros; apply Hobs; right; assumption)).
  pose proof (Hobs tid (or_introl eq_refl)) as Hhead.
  unfold encode_ready_tbl_at_or in *; cbn; rewrite IH.
  destruct (before.(inUsedTaskStates) tid); destruct (after.(inUsedTaskStates) tid);
    simpl in Hhead; try discriminate; try reflexivity.
  injection Hhead as Heq; rewrite Heq; reflexivity.
Qed.
Lemma sched_commit_ready_encodings__publication_and_returns : forall sg tasks sched p invocation node,
  ~ In node.(taskID) sched.(readyList) ->
  let post_tasks := task_commit tasks p invocation node in
  let post_sched := sched_commit_ready sg tasks sched p invocation node in
  encode_ready_grp post_sched.(readyList) post_tasks =
    Z.lor (encode_ready_grp sched.(readyList) tasks) (Z.shiftl 1 (node.(curPrio) / 8)) /\
  (forall y, encode_ready_tbl_at_or post_sched.(readyList) post_tasks y =
    if Z.eq_dec y (node.(curPrio) / 8)
    then Z.lor (encode_ready_tbl_at_or sched.(readyList) tasks y)
      (Z.shiftl 1 (node.(curPrio) mod 8))
    else encode_ready_tbl_at_or sched.(readyList) tasks y).
Proof.
  intros sg tasks sched p invocation node Hnot; cbv zeta.
  assert (Hobs : forall tid, In tid sched.(readyList) ->
    option_map curPrio ((task_commit tasks p invocation node).(inUsedTaskStates) tid) =
    option_map curPrio (tasks.(inUsedTaskStates) tid)).
  { intros tid Hin; rewrite task_commit_observation by reflexivity.
    destruct (Z.eq_dec tid node.(taskID)); [subst; contradiction|reflexivity]. }
  pose proof (proj1 (task_commit_publication_fields_eq tasks p invocation node)) as Hget.
  unfold sched_commit_ready; cbn [sched_set_ready readyList].
  split.
  - rewrite <- (ready_group_permutation_eq__publication_and_returns _ _ _ (Ucos2Verify.lib.helpers.insert_sorted_by_perm _ _ _ _)).
    cbn [encode_ready_grp]; rewrite Hget; cbn [task_set_links curPrio].
    rewrite (ready_group_priority_observation_eq__publication_and_returns _ _ _ Hobs).
    apply Z.lor_comm.
  - intro y.
    rewrite <- (ready_row_permutation_eq__publication_and_returns _ _ _ y (Ucos2Verify.lib.helpers.insert_sorted_by_perm _ _ _ _)).
    change ((match (task_commit tasks p invocation node).(inUsedTaskStates) node.(taskID) with
      | Some t => if Z.eqb (t.(curPrio) / 8) y then
          Z.lor (Z.shiftl 1 (t.(curPrio) mod 8))
            (encode_ready_tbl_at_or sched.(readyList) (task_commit tasks p invocation node) y)
          else encode_ready_tbl_at_or sched.(readyList) (task_commit tasks p invocation node) y
      | None => encode_ready_tbl_at_or sched.(readyList) (task_commit tasks p invocation node) y
      end) = (if Z.eq_dec y (node.(curPrio) / 8) then
        Z.lor (encode_ready_tbl_at_or sched.(readyList) tasks y)
          (Z.shiftl 1 (node.(curPrio) mod 8))
        else encode_ready_tbl_at_or sched.(readyList) tasks y)).
    rewrite Hget; cbn [task_set_links curPrio].
    rewrite (ready_row_priority_observation_eq__publication_and_returns _ _ _ y Hobs).
    destruct (Z.eq_dec y (node.(curPrio) / 8)) as [Heq|Hne].
    + subst y; rewrite Z.eqb_refl; apply Z.lor_comm.
    + assert (Z.eqb (node.(curPrio) / 8) y = false) by (apply Z.eqb_neq; lia).
      rewrite H; reflexivity.
Qed.
Lemma uchar_shift_mask_id__publication_and_returns : forall bit,
  0 <= bit < 8 -> unsigned_last_nbits (Z.shiftl 1 bit) 8 = Z.shiftl 1 bit.
Proof.
  intros bit Hbit.
  assert (bit = 0 \/ bit = 1 \/ bit = 2 \/ bit = 3 \/ bit = 4 \/ bit = 5 \/ bit = 6 \/ bit = 7) by lia.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst bit; reflexivity.
Qed.
Lemma ready_group_uchar_id__publication_and_returns : forall ready tasks,
  (forall tid t, In tid ready -> tasks.(inUsedTaskStates) tid = Some t -> 0 <= t.(curPrio) < 64) ->
  unsigned_last_nbits (encode_ready_grp ready tasks) 8 = encode_ready_grp ready tasks.
Proof.
  induction ready as [|tid rest IH]; intros tasks Hrange; [reflexivity|].
  cbn [encode_ready_grp].
  specialize (IH tasks ltac:(intros; eapply Hrange; [right; eassumption|eassumption])).
  destruct (tasks.(inUsedTaskStates) tid) as [t|] eqn:Hget; [|exact IH].
  rewrite unsigned_last_nbits_lor_distr by lia; rewrite IH.
  rewrite uchar_shift_mask_id__publication_and_returns; [reflexivity|].
  specialize (Hrange tid t (or_introl eq_refl) Hget).
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.
Lemma ready_row_uchar_id__publication_and_returns : forall ready tasks y,
  unsigned_last_nbits (encode_ready_tbl_at_or ready tasks y) 8 = encode_ready_tbl_at_or ready tasks y.
Proof.
  induction ready as [|tid rest IH]; intros tasks y; [reflexivity|].
  unfold encode_ready_tbl_at_or in *; cbn.
  destruct (tasks.(inUsedTaskStates) tid) as [t|]; [|apply IH].
  destruct Z.eqb; [|apply IH].
  rewrite unsigned_last_nbits_lor_distr by lia; rewrite IH.
  rewrite uchar_shift_mask_id__publication_and_returns; [reflexivity|].
  apply Z.mod_pos_bound; lia.
Qed.
Lemma sched_commit_rows_replace_eq__publication_and_returns : forall sg tasks sched p invocation node,
  ~ In node.(taskID) sched.(readyList) -> 0 <= node.(curPrio) / 8 < 8 ->
  let post_tasks := task_commit tasks p invocation node in
  let post_sched := sched_commit_ready sg tasks sched p invocation node in
  sched_row_values post_tasks post_sched.(readyList) =
  replace_Znth (node.(curPrio) / 8)
    (Z.lor (Znth (node.(curPrio) / 8) (sched_row_values tasks sched.(readyList)) 0)
      (Z.shiftl 1 (node.(curPrio) mod 8))) (sched_row_values tasks sched.(readyList)).
Proof.
  intros sg tasks sched p invocation node Hnot Hrow; cbv zeta.
  pose proof (proj2 (sched_commit_ready_encodings__publication_and_returns
    sg tasks sched p invocation node Hnot)) as Hencoding.
  rewrite sched_row_values_Znth by exact Hrow.
  unfold sched_row_values.
  change [0;1;2;3;4;5;6;7] with (Zrange 0 8).
  rewrite <- map_Zrange_update by exact Hrow.
  apply map_ext; intro y; rewrite Hencoding.
  destruct (Z.eq_dec y (node.(curPrio) / 8)); [subst|]; reflexivity.
Qed.
Lemma task_commit_priority_table_replace_eq__publication_and_returns :
  forall sg tasks p invocation node,
  0 <= p < 64 ->
  map (fun q => prio_tbl_entry_to_addr sg
    ((task_commit tasks p invocation node).(prioTbl) q)) (Zrange 0 64) =
  replace_Znth p (task_slot_addr sg node.(taskID))
    (map (fun q => prio_tbl_entry_to_addr sg (tasks.(prioTbl) q)) (Zrange 0 64)).
Proof.
  intros; rewrite <- map_Zrange_update by assumption.
  apply map_ext; intro q; cbn [task_commit prioTbl].
  destruct (Z.eq_dec q p); reflexivity.
Qed.
Lemma store_used_task_map_insert__publication_and_returns : forall sg used slot node,
  used slot = None ->
  used_task_rep sg slot node **
  store_used_task_map sg used |--
  store_used_task_map sg (fun tid => if Z.eq_dec tid slot then Some node else used tid).
Proof.
  intros sg used slot node Hnone; unfold store_used_task_map.
  sep_apply_l_atomic (store_map_equiv_store_map_missing
    (used_task_rep sg)
    used slot Hnone).
  assert (Hoff : forall tid, tid <> slot -> used tid =
    (if Z.eq_dec tid slot then Some node else used tid)).
  { intros; destruct (Z.eq_dec tid slot); congruence. }
  rewrite (store_map_missing_i_equiv _ _ _ slot Hoff).
  entailer!.
  apply (store_map_merge (used_task_rep sg) slot node
    (fun tid => if Z.eq_dec tid slot then Some node else used tid)).
  destruct (Z.eq_dec slot slot); [reflexivity|contradiction].
Qed.
Lemma task_tcb_init_used_merge_published_node__publication_and_returns : forall sg args invocation origin acquired current slot image,
  UCOS2_state_inv sg current ->
  task_tcb_init_commit_binding args invocation origin acquired current slot ->
  used_task_rep sg slot
    (task_set_links (task_tcb_init_commit_node args acquired slot image)
      current.(TskState).(tcbListHead) None) **
  task_tcb_init_used_with_head_prev sg current slot |--
  store_used_task_map sg
    (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState).(inUsedTaskStates).
Proof.
  intros sg args invocation origin acquired current slot image Hvalid Hbinding.
  pose proof (task_tcb_init_commit_binding_identity args invocation origin acquired current slot image Hbinding)
    as Hidentity.
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  destruct (task_private_excludes_public sg current.(TskState) slot
    (proj1 (proj1 (proj2 Hvalid))) Hprivate) as [Hnone Hnotfree].
  change (used_task_rep sg slot
    (task_set_links (task_tcb_init_commit_node args acquired slot image)
      current.(TskState).(tcbListHead) None) **
    store_used_task_map sg (task_tcb_init_head_updated_map current slot) |--
    store_used_task_map sg (fun tid => if Z.eq_dec tid slot then
      Some (task_set_links (task_tcb_init_commit_node args acquired slot image)
        current.(TskState).(tcbListHead) None) else task_tcb_init_head_updated_map current slot tid)).
  apply store_used_task_map_insert__publication_and_returns.
  unfold task_tcb_init_head_updated_map; rewrite Hnone.
  destruct current.(TskState).(tcbListHead); reflexivity.
Qed.
Lemma task_tcb_init_publication_storage_merge__publication_and_returns :
  forall sg args invocation origin acquired current slot image flags,
  UCOS2_state_inv sg current ->
  task_tcb_init_commit_binding args invocation origin acquired current slot ->
  image (TCBCommonField TCBFlagsRdy) = Some flags ->
  (sg.(osKernelConfig).(cfgTaskNames) = true ->
    exists chars, readable_name current.(NameState)
      (task_tcb_init_commit_node args acquired slot image).(tcbTaskName) chars) ->
  let post := task_tcb_init_published_state sg args invocation acquired current slot image in
  task_slot_storage_rep sg slot
    (task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead)
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) args image)) **
  task_tcb_init_used_with_head_prev sg current slot **
  sg.(g_OSTCBList) # Ptr |-> task_slot_addr sg slot **
  sg.(g_OSTaskCtr) # UChar |-> (task_tcb_init_count current + 1) **
  sg.(g_OSRdyGrp) # UChar |-> task_tcb_init_ready_group post **
  UCharArray.full sg.(g_OSRdyTbl) 8 (task_tcb_init_ready_rows post) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 (task_tcb_init_priority_table sg post) **
  task_tcb_init_publication_other sg current |-- UCOS2_inv sg post.
Proof.
  intros sg args invocation origin acquired current slot image flags Hvalid Hbinding Hflags Hnewname; cbv zeta.
  sep_apply_l_atomic (task_tcb_init_linked_storage_rep sg args acquired current slot image flags Hflags).
  sep_apply_l_atomic (task_tcb_init_used_merge_published_node__publication_and_returns
    sg args invocation origin acquired current slot image Hvalid Hbinding).
  pose proof (task_tcb_init_commit_binding_identity args invocation origin acquired current slot image Hbinding)
    as Hidentity.
  match goal with
  | |- ?resources |-- _ =>
    assert (Hassembled : resources |--
      task_public_storage sg
        (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState) **
      sched_raw_rep sg
        (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState)
        (task_tcb_init_published_state sg args invocation acquired current slot image).(SchedState) **
      UCOS2_raw_rep_missing_task_storage_sched sg current)
  end.
  {
  unfold task_public_storage, sched_raw_rep, store_prio_tbl,
    task_tcb_init_publication_other, task_tcb_init_priority_table, task_tcb_init_ready_group,
    task_tcb_init_ready_rows, task_tcb_init_free_root, task_tcb_init_count.
  rewrite sched_rows_array_equiv.
  unfold sched_row_values.
  unfold task_tcb_init_published_state, task_tcb_init_commit_state.
  cbn [task_sched_commit_state replace_TskS replace_SchedS TskState SchedState].
  entailer!.
  cbn [task_commit taskFreeStorage taskLifecycle unUsedTaskStates tcbListHead taskCount
    encode_task_link task_tcb_init_commit_node task_tcb_init_node_from_free_image taskID].
  unfold sched_physical_rep.
  cbn [sched_commit_ready sched_set_ready curSchedPrio highRdyPrio
    curTaskID highRdyTid ctxSwCtr isRunning].
  entailer!.
  }
  intros heap Hresources.
  apply (UCOS2_task_commit_merge_task_sched sg current args.(initPrio)
    invocation (task_tcb_init_commit_node args acquired slot image)
    Hvalid Hidentity eq_refl eq_refl eq_refl eq_refl Hnewname heap).
  exact (Hassembled heap Hresources).
Qed.
