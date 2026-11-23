Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.SL Require Import CriticalSTS.
From MonadLib.StateRelMonad Require Export safeexec_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.task_status.

(* ================================================================== *)
(* Phase 2 Task 2.5.5:子状态类型 — 已实现(interrupt/tick)+ 占位(other) *)
(* ================================================================== *)

(* 已实现:中断抽象状态 *)
Module InterruptStateDef.
  Record InterruptAbstractState : Type := {
    intNesting  : Z;
    lockNesting : Z;
  }.
End InterruptStateDef.
Export InterruptStateDef.

Definition Glob_InterruptAbstractState := InterruptAbstractState.

(* 已实现:tick 抽象状态 *)
Module TickStateDef.
  Record TickAbstractState : Type := {
    ostime  : Z;
    tickStepState : Z;
  }.
End TickStateDef.
Export TickStateDef.

(* 已实现:task 抽象状态(Phase 3)*)
Module TaskStateDef.
  Definition TaskID : Type := Z.

  (** Actual caller-provided stack extent, in increasing address order.
      Basic Create passes zero bottom/size to TCBInit, so this descriptor
      cannot be reconstructed from those TCB fields. *)
  Record TaskStackRegion : Type := {
    stackRegionBase : addr;
    stackRegionWords : Z;
    stackRegionGrowsDown : bool
  }.

  (** Each triple is [lo, hi, current words], with word offsets relative
      to the region base.  Missing intervals are genuinely not owned by
      this entry; None within a word list still owns undefined storage. *)
  Definition TaskStackFragment : Type := Z * Z * list (option Z).
  Definition TaskStackFragments : Type := list TaskStackFragment.
  Definition TaskStackMap : Type :=
    (TaskID * nat) -> option (TaskStackRegion * TaskStackFragments).

  Inductive PrioTblEntry : Type :=
  | PTFree
  | PTReserved
  | PTTask (tid : TaskID).

  (* EventID 前向声明;实际定义在 event.v(Phase 5)*)
  Definition EventID : Type := Z.

  (** Source-selected native fields, including both bytes of padding.  A
      raw image permits stale values on a free/reused node; it is not a
      complete-task or task-validity assertion. *)
  Inductive TCBField : Type :=
  | TCBStkPtr | TCBExtPtr | TCBStkBottom | TCBStkSize
  | TCBOpt | TCBId | TCBNext | TCBPrev | TCBEventPtr | TCBMsg
  | TCBFlagNode | TCBFlagsRdy | TCBPadding42 | TCBPadding43
  | TCBDly | TCBStat | TCBStatPend | TCBPrio | TCBX | TCBY
  | TCBBitX | TCBBitY | TCBDelReq | TCBTaskName | TCBReg0.

  Definition TCBCommonImage := TCBField -> option Z.

  Definition TCBField_eq_dec :
    forall x y : TCBField, {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  (** One raw image vocabulary for free, private and configured live TCBs.
      A layout selects the physically present fields; absent configuration
      fields are not additional cells.  TCBCommonImage remains the common
      field projection used by existing status/priority transformers. *)
  Inductive TCBLayoutField : Type :=
  | TCBCommonField (field : TCBField)
  | TCBEventMultiPtr
  | TCBEventMultiRdy
  | TCBCtxSwCtr
  | TCBCyclesTot
  | TCBCyclesStart
  | TCBStkBase
  | TCBStkUsed.

  Definition TCBLayoutField_eq_dec :
    forall x y : TCBLayoutField, {x = y} + {x <> y}.
  Proof. decide equality; apply TCBField_eq_dec. Defined.

  Definition TCBLayoutImage := TCBLayoutField -> option Z.

  Inductive TaskInvocationOrigin : Type :=
  | BootInvocation
  | RunningInvocation (slot : TaskID) (generation : nat).

  Record TaskPrivateAllocation : Type := {
    privateSlot : TaskID;
    privateGeneration : nat;
    privateStorage : TCBLayoutImage;
  }.

  Record TaskCreationEntry : Type := {
    creationInvocation : nat;
    creationOrigin : TaskInvocationOrigin;
    creationAllocation : option TaskPrivateAllocation;
  }.

  (** One canonical task lifecycle state.  Pending entries are indexed by
      the actually reserved priority, not by a single global initializing
      bit.  Invocation and allocation generations are distinct from pool
      indices and from the application's 16-bit OSTCBId. *)
  Record TaskLifecycleState : Type := {
    taskFreeStorage : TaskID -> option TCBLayoutImage;
    taskReservations : Priority -> option TaskCreationEntry;
    taskActiveOrder : list TaskID;
    taskNextGeneration : nat;
    taskInvocations : nat -> option TaskInvocationOrigin;
    taskRetiredInvocations : nat -> bool;
    taskNextInvocation : nat;
    taskPublications : list (nat * TaskID * nat);
  }.

  Definition empty_task_lifecycle : TaskLifecycleState :=
    {| taskFreeStorage := fun _ => None;
       taskReservations := fun _ => None;
       taskActiveOrder := nil;
       taskNextGeneration := 0;
       taskInvocations := fun _ => None;
       taskRetiredInvocations := fun _ => false;
       taskNextInvocation := 0;
       taskPublications := nil |}.

  Record TaskAbstractState : Type := {
    taskID          : TaskID;
    taskGeneration  : nat;
    (** OS_TCB field values.  Pointer values do not own the pointed-to
        stack, extension, flag node, name or event array.  Conditional
        fields are interpreted only by the selected layout. *)
    tcbStkPtr       : addr;
    tcbExtPtr       : addr;
    tcbStkBottom    : addr;
    tcbStkSize      : Z;
    tcbOpt          : Z;
    tcbPublicId     : Z;
    tcbFlagNode     : addr;
    tcbFlagsRdy     : Z;
    tcbTaskName     : addr;
    tcbReg0         : Z;
    (** Real OS_TASK_PROFILE_EN fields. These values do not introduce ghost
        cells when profiling is disabled; the configured representation selects
        whether the corresponding C fields are present. OSTCBStkUsed counts
        OS_STK entries (OS_TaskStatStkChk assigns OS_STK_DATA.OSUsed). *)
    tcbCtxSwCtr     : Z;
    tcbCyclesTot    : Z;
    tcbCyclesStart  : Z;
    tcbStkBase      : addr;
    tcbStkUsed      : Z;
    (** Padding observations: None makes no promise about the byte value. *)
    tcbPadding42    : option Z;
    tcbPadding43    : option Z;
    (** Actual OS_EVENT ** address, distinct from the logical sequence. *)
    tcbEventMultiPtr : addr;
    curPrio         : Priority;
    stat            : TaskStatus;
    statPend        : PendStatus;
    dly             : Z;
    eventPtr        : option EventID;
    (** Logical input order, including duplicates, not a pointer encoding.
        Binding and lifetime of the actual array are separate obligations. *)
    eventMultiWaitEvents : list EventID;
    eventMultiRdy   : option EventID;
    msg             : option addr;
    nextTCB         : option TaskID;
    prevTCB         : option TaskID;
    delReq          : bool;
  }.

  Record Glob_TaskAbstractState : Type := {
    inUsedTaskStates : TaskID -> option TaskAbstractState;
    unUsedTaskStates : list TaskID;
    tcbListHead      : option TaskID;
    prioTbl          : Priority -> PrioTblEntry;
    taskCount        : Z;
    taskLifecycle    : TaskLifecycleState;
    (** OSTaskRegNextAvailID; a real conditional global, not a task ID. *)
    taskRegNextID    : Z;
    (** Bytes transferred to the shared context protocol.  The executing
        stack and private creation buffers remain outside this map.
        Keys reuse the existing task allocation generation. *)
    parkedTaskStacks : TaskStackMap;
  }.
End TaskStateDef.
Export TaskStateDef.

(* 已实现:event 抽象状态(Phase 5)*)
Module EventStateDef.
  Inductive OSEventType : Type :=
  | OS_EVENT_TYPE_UNUSED
  | OS_EVENT_TYPE_SEM
  | OS_EVENT_TYPE_MUTEX
  | OS_EVENT_TYPE_MBOX
  | OS_EVENT_TYPE_Q
  | OS_EVENT_TYPE_FLAG.

  Record MutexFields : Type := {
    mfPCP           : Priority;
    mfOwner         : option TaskID;
    mfOwnerOrigPrio : option Priority;
  }.

  Record SemFields : Type := {
    semCount : Z;
  }.

  Record MboxFields : Type := {
    mboxMsg : option addr;
  }.

  Definition QueueID : Type := Z.

  (* OS_Q is a separate control block referenced by OS_EVENT.OSEventPtr.
     The concrete ring pointers are derived from qStart/qSize and the two
     indices; qMessages is the FIFO sequence visible to queue clients. *)
  Record QueueFields : Type := {
    qID       : QueueID;
    qStart    : addr;
    qSize     : Z;
    qInIndex  : Z;
    qOutIndex : Z;
    qMessages : list addr;
  }.

  (** Fields of the narrow-priority OS_EVENT layout.  EventName is present
      only in the named profile; the four padding bytes remain owned in
      either profile.  A free or private image need not decode as a live
      synchronization object. *)
  Inductive EventField : Type :=
  | EventTypeField | EventPtrField | EventCntField | EventGrpField
  | EventTbl0 | EventTbl1 | EventTbl2 | EventTbl3
  | EventTbl4 | EventTbl5 | EventTbl6 | EventTbl7
  | EventPadding1 | EventPadding2 | EventPadding3 | EventPadding19
  | EventNameField.

  Definition EventStorage := EventField -> option Z.

  Definition EventField_eq_dec :
    forall x y : EventField, {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Record OSEventAbstractState : Type := {
    eventType   : OSEventType;
    mutexFields : option MutexFields;
    semFields   : option SemFields;
    mboxFields  : option MboxFields;
    queueFields : option QueueFields;
    waitList    : list TaskID;
    eventGeneration : nat;
    (** OSEventName is conditional; padding retains the actual byte
        observations.  These values alone do not grant memory ownership. *)
    eventName : addr;
    eventPadding1 : option Z;
    eventPadding2 : option Z;
    eventPadding3 : option Z;
    eventPadding19 : option Z;
  }.

  Record EventPrivateAllocation : Type := {
    eventPrivateInvocation : nat;
    eventPrivateGeneration : nat;
    (** OSQCreate can detach a QCB before initializing either object.
        This ghost association reuses the ECB invocation identity; the
        QCB bytes remain owned by that invocation, not by the public pool. *)
    eventPrivateQueue : option QueueID;
    (** Logical lease for an enabled PCP that OSMutexCreate has actually
        reserved while this ECB is still private.  It has no C address
        and owns no second priority-table cell.  Ordinary Event/Queue
        allocations carry None; private stores retain the lease until
        publication transfers it to the live mutex or rollback cancels it. *)
    eventPrivateMutexPCP : option Priority;
    eventPrivateStorage : EventStorage;
  }.

  (** ECB slots, creation invocations and allocation generations are
      different identities.  Private storage is owned by its invocation,
      not by the public Event heap.  The Task caller belongs to the call protocol, rather than an
      additional unused field in this allocation. *)
  Record EventLifecycleState : Type := {
    eventFreeStorage : EventID -> option EventStorage;
    eventPrivate : EventID -> option EventPrivateAllocation;
    eventNextGeneration : nat;
    eventNextInvocation : nat;
  }.

  Definition empty_event_lifecycle : EventLifecycleState :=
    {| eventFreeStorage := fun _ => None;
       eventPrivate := fun _ => None;
       eventNextGeneration := 0;
       eventNextInvocation := 0 |}.

  Record Glob_EventAbstractState : Type := {
    inUsedEventStates : EventID -> option OSEventAbstractState;
    unUsedEventStates : list EventID;
    (** Physical contents of published queue buffers.  Unoccupied ring
        slots retain their bytes; logical qMessages is a separate projection. *)
    publishedQueueBytes : QueueID -> option (list (option addr));
    eventLifecycle : EventLifecycleState;
  }.
End EventStateDef.
Export EventStateDef.

(* 已实现:sched 抽象状态(Phase 4)*)
Module SchedStateDef.
  Record SchedAbstractState : Type := {
    readyList    : list TaskID;
    curTaskID    : option TaskID;
    curSchedPrio : option Priority;
    highRdyTid   : option TaskID;
    highRdyPrio  : option Priority;
    ctxSwCtr     : Z;
    isRunning    : bool;
  }.

  Definition Glob_SchedAbstractState := SchedAbstractState.
End SchedStateDef.
Export SchedStateDef.

(** Independent resources from Source/ucos_ii.h.  All records below are
    observations or explicit lifecycle ghosts; only their module [*_rep]
    predicates own memory.  In particular, block-loan and invocation IDs
    do not constitute duplicable substitutes for spatial permissions. *)
Module KernelResourceStateDef.
  Record KernelControlState := {
    safetyCriticalStarted : option bool
  }.
  Inductive NameStorageOrigin := StaticNameStorage | ApplicationNameStorage.
  Record NameStorageSource := {
    nameStorageOrigin : NameStorageOrigin;
    nameStorageDomain : list addr
  }.
  (** Reader identity is the key of nameReaders; the lease records only
      the root and bytes protected until that reader is released. *)
  Record NameReadLease := {
    nameReadRoot : addr;
    nameReadDomain : list addr
  }.
  Record NameResourceState := {
    nameBytes : addr -> option Z;
    nameSources : nat -> option NameStorageSource;
    nameReaders : nat -> option NameReadLease
  }.
End KernelResourceStateDef.
Export KernelResourceStateDef.

Module FlagStateDef.
  Definition FlagID := Z.
  Inductive FlagWaitMode := FlagClearAll | FlagClearAny | FlagSetAll | FlagSetAny.
  Record FlagGroupImage := {
    flagImageType : Z; flagImageHead : addr; flagImageBits : Z;
    flagImageName : addr; flagImagePadding : list (option Z)
  }.
  Record FlagNodeImage := {
    flagNodeNext : addr; flagNodePrev : addr; flagNodeTCB : addr;
    flagNodeGroup : addr; flagNodeMask : Z; flagNodeMode : Z;
    flagNodePadding : list (option Z)
  }.
  Record FlagGroupState := {
    flagGeneration : nat; flagBits : Z; flagName : addr;
    flagWaitOrder : list addr
  }.
  Record FlagWaiterState := {
    flagNodeAddr : addr; flagTask : TaskID; flagTaskGeneration : nat;
    flagGroup : FlagID; flagGroupGeneration : nat;
    flagMask : Z; flagWaitMode : FlagWaitMode; flagWaitImage : FlagNodeImage
  }.
  Record GlobFlagState := {
    flagUsed : FlagID -> option FlagGroupState;
    flagFree : list FlagID;
    flagImages : FlagID -> option FlagGroupImage;
    flagWaitNodes : addr -> option FlagWaiterState;
    flagNextGeneration : nat
  }.
End FlagStateDef.
Export FlagStateDef.

Module MemoryStateDef.
  Definition MemID := Z.
  Record MemoryControlImage := {
    memImageBase : addr; memImageFree : addr; memImageSize : Z;
    memImageCount : Z; memImageNFree : Z; memImageName : addr
  }.
  Record MemoryBlockLoan := {
    loanPartition : MemID; loanPartitionGeneration : nat;
    loanBlock : Z; loanGeneration : nat
  }.
  Record MemoryPartitionState := {
    memGeneration : nat; memBase : addr; memBlockSize : Z; memBlockCount : Z;
    memFreeBlocks : list Z; memAllocatedBlocks : Z -> option MemoryBlockLoan;
    memName : addr; memNextLoan : nat
  }.
  Record MemoryPrivatePartition := {
    memPrivateSlot : MemID;
    memPrivateImage : MemoryControlImage; memPrivateBase : addr;
    memPrivateExtent : Z; memPrivateBlockSize : Z; memPrivateBlockCount : Z;
    memPrivateLinkedPrefix : Z
  }.
  Record GlobMemoryState := {
    memPartitions : MemID -> option MemoryPartitionState;
    memFreeControls : list MemID;
    memControlImages : MemID -> option MemoryControlImage;
    memPrivateControls : MemID -> option MemoryPrivatePartition;
    memNextGeneration : nat
  }.
End MemoryStateDef.
Export MemoryStateDef.

Module TimerStateDef.
  Definition TimerID := Z.
  (** Source-progress ghost, not an additional C global.  Finished means
      that initialization returned, not that all service creations succeeded. *)
  Inductive TimerInitializationPhase :=
  | TimerUninitialized | TimerPoolInitialized | TimerLockAttempted
  | TimerSignalAttempted | TimerInitializationFinished.
  Inductive TimerMode := TimerOneShot | TimerPeriodic.
  Inductive TimerStatus := TimerUnused | TimerStopped | TimerCompleted | TimerRunning.
  Record TimerImage := {
    timerImageType : Z; timerImageCallback : addr; timerImageArg : addr;
    timerImageNext : addr; timerImagePrev : addr; timerImageMatch : Z;
    timerImageDelay : Z; timerImagePeriod : Z; timerImageName : addr;
    timerImageOption : Z; timerImageState : Z;
    timerImagePadding : list (option Z)
  }.
  Record TimerObjectState := {
    timerGeneration : nat; timerDelay : Z; timerPeriod : Z; timerMatch : Z;
    timerMode : TimerMode; timerState : TimerStatus;
    timerCallback : addr; timerCallbackArg : addr; timerName : addr
  }.
  (** Generation names the allocated instance until publication, which
      transfers it to TimerObjectState for scan/callback identity checks.
      Image records the real object bytes; generation has no C cell.
      Invocation ownership belongs to the call/lock protocol, not this value. *)
  Record TimerPrivateAllocation := {
    timerPrivateGeneration : nat;
    timerPrivateImage : TimerImage
  }.
  (** Per-visit local ghost cursor, not additional C storage.  The spoke
      follows from Time/configuration; Current is the dispatch argument.
      Past callback observations and the invocation boundary belong to
      the execution trace.  Remaining length is the traversal measure. *)
  Record TimerScanState := {
    timerScanTime : Z;
    timerScanNext : option (TimerID * nat);
    timerScanRemaining : list TimerID
  }.
  Record GlobTimerState := {
    timerUsed : TimerID -> option TimerObjectState;
    timerFree : list TimerID;
    timerImages : TimerID -> option TimerImage;
    timerPrivate : TimerID -> option TimerPrivateAllocation;
    timerWheel : list (list TimerID); timerTime : Z;
    timerFreeCount : Z; timerUsedCount : Z;
    timerSem : addr; timerSignalSem : addr;
    timerTask : option (TaskID * nat); timerNextGeneration : nat;
    timerInitPhase : TimerInitializationPhase
  }.
End TimerStateDef.
Export TimerStateDef.

Module StatisticsStateDef.
  Record StatisticsSample := {
    sampleRun : Z; sampleDivisor : Z
  }.
  (** The source's five cells.  Calibration and sampling order is part of
      the task's control flow, not an extra global phase variable. *)
  Record StatisticsState := {
    idleCtr : Z; idleCtrMax : Z; idleCtrRun : Z;
    cpuUsage : Z; statReady : bool
  }.
End StatisticsStateDef.
Export StatisticsStateDef.

(* ================================================================== *)
(* 顶层 UCOS2_Verify_State                                              *)
(* ================================================================== *)

Record UCOS2_Verify_State : Type := {
  IntrState  : Glob_InterruptAbstractState;
  TskState   : Glob_TaskAbstractState;
  SchedState : SchedAbstractState;
  EventState : Glob_EventAbstractState;
  TickState  : TickAbstractState;
  FlagState  : GlobFlagState;
  MemoryState : GlobMemoryState;
  TimerState : GlobTimerState;
  StatsState : StatisticsState;
  ControlState : KernelControlState;
  NameState : NameResourceState;
}.

(* ================================================================== *)
(* 各模块子状态更新；保留其他字段，不引入额外公理。                   *)
(* ================================================================== *)

Definition replace_IntrS  (ms : Glob_InterruptAbstractState) (os : UCOS2_Verify_State) : UCOS2_Verify_State :=
  {| IntrState  := ms;
     TskState   := os.(TskState);
     SchedState := os.(SchedState);
     EventState := os.(EventState);
     TickState  := os.(TickState);
     FlagState := os.(FlagState);
     MemoryState := os.(MemoryState);
     TimerState := os.(TimerState);
     StatsState := os.(StatsState);
     ControlState := os.(ControlState);
     NameState := os.(NameState);
  |}.

Definition replace_TickS  (ms : TickAbstractState) (os : UCOS2_Verify_State) : UCOS2_Verify_State :=
  {| IntrState  := os.(IntrState);
     TskState   := os.(TskState);
     SchedState := os.(SchedState);
     EventState := os.(EventState);
     TickState  := ms;
     FlagState := os.(FlagState);
     MemoryState := os.(MemoryState);
     TimerState := os.(TimerState);
     StatsState := os.(StatsState);
     ControlState := os.(ControlState);
     NameState := os.(NameState);
  |}.

Definition replace_TskS   (ms : Glob_TaskAbstractState) (os : UCOS2_Verify_State) : UCOS2_Verify_State :=
  {| IntrState  := os.(IntrState);
     TskState   := ms;
     SchedState := os.(SchedState);
     EventState := os.(EventState);
     TickState  := os.(TickState);
     FlagState := os.(FlagState);
     MemoryState := os.(MemoryState);
     TimerState := os.(TimerState);
     StatsState := os.(StatsState);
     ControlState := os.(ControlState);
     NameState := os.(NameState);
  |}.

Definition replace_SchedS (ms : SchedAbstractState) (os : UCOS2_Verify_State) : UCOS2_Verify_State :=
  {| IntrState  := os.(IntrState);
     TskState   := os.(TskState);
     SchedState := ms;
     EventState := os.(EventState);
     TickState  := os.(TickState);
     FlagState := os.(FlagState);
     MemoryState := os.(MemoryState);
     TimerState := os.(TimerState);
     StatsState := os.(StatsState);
     ControlState := os.(ControlState);
     NameState := os.(NameState);
  |}.

Definition replace_EventS (ms : Glob_EventAbstractState) (os : UCOS2_Verify_State) : UCOS2_Verify_State :=
  {| IntrState  := os.(IntrState);
     TskState   := os.(TskState);
     SchedState := os.(SchedState);
     EventState := ms;
     TickState  := os.(TickState);
     FlagState := os.(FlagState);
     MemoryState := os.(MemoryState);
     TimerState := os.(TimerState);
     StatsState := os.(StatsState);
     ControlState := os.(ControlState);
     NameState := os.(NameState);
  |}.

(* Projection facts retained below all have concrete verification consumers. *)

Lemma replace_TskS_TskState   : forall ms os, (replace_TskS ms os).(TskState) = ms.
Proof. intros; reflexivity. Qed.

Lemma replace_TskS_other_Intr : forall ms os, (replace_TskS ms os).(IntrState) = os.(IntrState).
Proof. intros; reflexivity. Qed.

Lemma replace_TskS_other_Sched : forall ms os, (replace_TskS ms os).(SchedState) = os.(SchedState).
Proof. intros; reflexivity. Qed.

Lemma replace_TskS_other_Event : forall ms os, (replace_TskS ms os).(EventState) = os.(EventState).
Proof. intros; reflexivity. Qed.

Lemma replace_TskS_other_Tick : forall ms os, (replace_TskS ms os).(TickState) = os.(TickState).
Proof. intros; reflexivity. Qed.

Lemma replace_SchedS_SchedState : forall ms os, (replace_SchedS ms os).(SchedState) = ms.
Proof. intros; reflexivity. Qed.

Lemma replace_SchedS_other_Intr : forall ms os, (replace_SchedS ms os).(IntrState) = os.(IntrState).
Proof. intros; reflexivity. Qed.

Lemma replace_SchedS_other_Tsk : forall ms os, (replace_SchedS ms os).(TskState) = os.(TskState).
Proof. intros; reflexivity. Qed.

Lemma replace_SchedS_other_Event : forall ms os, (replace_SchedS ms os).(EventState) = os.(EventState).
Proof. intros; reflexivity. Qed.

Lemma replace_SchedS_other_Tick : forall ms os, (replace_SchedS ms os).(TickState) = os.(TickState).
Proof. intros; reflexivity. Qed.

Lemma replace_EventS_EventState : forall ms os, (replace_EventS ms os).(EventState) = ms.
Proof. intros; reflexivity. Qed.

Lemma replace_EventS_other_Intr : forall ms os, (replace_EventS ms os).(IntrState) = os.(IntrState).
Proof. intros; reflexivity. Qed.

Lemma replace_EventS_other_Tsk : forall ms os, (replace_EventS ms os).(TskState) = os.(TskState).
Proof. intros; reflexivity. Qed.

Lemma replace_EventS_other_Sched : forall ms os, (replace_EventS ms os).(SchedState) = os.(SchedState).
Proof. intros; reflexivity. Qed.

Lemma replace_EventS_other_Tick : forall ms os, (replace_EventS ms os).(TickState) = os.(TickState).
Proof. intros; reflexivity. Qed.

Definition replace_FlagS (ms : GlobFlagState) (os : UCOS2_Verify_State) : UCOS2_Verify_State :=
  {| IntrState := os.(IntrState);
     TickState := os.(TickState);
     TskState := os.(TskState);
     SchedState := os.(SchedState);
     EventState := os.(EventState);
     FlagState := ms;
     MemoryState := os.(MemoryState);
     TimerState := os.(TimerState);
     StatsState := os.(StatsState);
     ControlState := os.(ControlState);
     NameState := os.(NameState) |}.

Definition replace_MemoryS (ms : GlobMemoryState) (os : UCOS2_Verify_State) : UCOS2_Verify_State :=
  {| IntrState := os.(IntrState);
     TickState := os.(TickState);
     TskState := os.(TskState);
     SchedState := os.(SchedState);
     EventState := os.(EventState);
     FlagState := os.(FlagState);
     MemoryState := ms;
     TimerState := os.(TimerState);
     StatsState := os.(StatsState);
     ControlState := os.(ControlState);
     NameState := os.(NameState) |}.

Definition replace_TimerS (ms : GlobTimerState) (os : UCOS2_Verify_State) : UCOS2_Verify_State :=
  {| IntrState := os.(IntrState);
     TickState := os.(TickState);
     TskState := os.(TskState);
     SchedState := os.(SchedState);
     EventState := os.(EventState);
     FlagState := os.(FlagState);
     MemoryState := os.(MemoryState);
     TimerState := ms;
     StatsState := os.(StatsState);
     ControlState := os.(ControlState);
     NameState := os.(NameState) |}.

Definition replace_StatsS (ms : StatisticsState) (os : UCOS2_Verify_State) : UCOS2_Verify_State :=
  {| IntrState := os.(IntrState);
     TickState := os.(TickState);
     TskState := os.(TskState);
     SchedState := os.(SchedState);
     EventState := os.(EventState);
     FlagState := os.(FlagState);
     MemoryState := os.(MemoryState);
     TimerState := os.(TimerState);
     StatsState := ms;
     ControlState := os.(ControlState);
     NameState := os.(NameState) |}.

Definition replace_ControlS (ms : KernelControlState) (os : UCOS2_Verify_State) : UCOS2_Verify_State :=
  {| IntrState := os.(IntrState);
     TickState := os.(TickState);
     TskState := os.(TskState);
     SchedState := os.(SchedState);
     EventState := os.(EventState);
     FlagState := os.(FlagState);
     MemoryState := os.(MemoryState);
     TimerState := os.(TimerState);
     StatsState := os.(StatsState);
     ControlState := ms;
     NameState := os.(NameState) |}.

Definition replace_NameS (ms : NameResourceState) (os : UCOS2_Verify_State) : UCOS2_Verify_State :=
  {| IntrState := os.(IntrState);
     TickState := os.(TickState);
     TskState := os.(TskState);
     SchedState := os.(SchedState);
     EventState := os.(EventState);
     FlagState := os.(FlagState);
     MemoryState := os.(MemoryState);
     TimerState := os.(TimerState);
     StatsState := os.(StatsState);
     ControlState := os.(ControlState);
     NameState := ms |}.

Lemma replace_IntrS_put_back : forall s,
  replace_IntrS s.(IntrState) s = s.
Proof. intros []; reflexivity. Qed.

Lemma replace_IntrS_last_write : forall (a b : Glob_InterruptAbstractState) s,
  replace_IntrS b (replace_IntrS a s) = replace_IntrS b s.
Proof. intros; reflexivity. Qed.

Lemma replace_IntrS_frame : forall ms s,
  (replace_IntrS ms s).(TickState) = s.(TickState) /\
  (replace_IntrS ms s).(TskState) = s.(TskState) /\
  (replace_IntrS ms s).(SchedState) = s.(SchedState) /\
  (replace_IntrS ms s).(EventState) = s.(EventState) /\
  (replace_IntrS ms s).(FlagState) = s.(FlagState) /\
  (replace_IntrS ms s).(MemoryState) = s.(MemoryState) /\
  (replace_IntrS ms s).(TimerState) = s.(TimerState) /\
  (replace_IntrS ms s).(StatsState) = s.(StatsState) /\
  (replace_IntrS ms s).(ControlState) = s.(ControlState) /\
  (replace_IntrS ms s).(NameState) = s.(NameState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma replace_TickS_put_back : forall s,
  replace_TickS s.(TickState) s = s.
Proof. intros []; reflexivity. Qed.

Lemma replace_TickS_last_write : forall (a b : TickAbstractState) s,
  replace_TickS b (replace_TickS a s) = replace_TickS b s.
Proof. intros; reflexivity. Qed.

Lemma replace_TickS_frame : forall ms s,
  (replace_TickS ms s).(IntrState) = s.(IntrState) /\
  (replace_TickS ms s).(TskState) = s.(TskState) /\
  (replace_TickS ms s).(SchedState) = s.(SchedState) /\
  (replace_TickS ms s).(EventState) = s.(EventState) /\
  (replace_TickS ms s).(FlagState) = s.(FlagState) /\
  (replace_TickS ms s).(MemoryState) = s.(MemoryState) /\
  (replace_TickS ms s).(TimerState) = s.(TimerState) /\
  (replace_TickS ms s).(StatsState) = s.(StatsState) /\
  (replace_TickS ms s).(ControlState) = s.(ControlState) /\
  (replace_TickS ms s).(NameState) = s.(NameState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma replace_TskS_put_back : forall s,
  replace_TskS s.(TskState) s = s.
Proof. intros []; reflexivity. Qed.

Lemma replace_TskS_last_write : forall (a b : Glob_TaskAbstractState) s,
  replace_TskS b (replace_TskS a s) = replace_TskS b s.
Proof. intros; reflexivity. Qed.

Lemma replace_TskS_frame : forall ms s,
  (replace_TskS ms s).(IntrState) = s.(IntrState) /\
  (replace_TskS ms s).(TickState) = s.(TickState) /\
  (replace_TskS ms s).(SchedState) = s.(SchedState) /\
  (replace_TskS ms s).(EventState) = s.(EventState) /\
  (replace_TskS ms s).(FlagState) = s.(FlagState) /\
  (replace_TskS ms s).(MemoryState) = s.(MemoryState) /\
  (replace_TskS ms s).(TimerState) = s.(TimerState) /\
  (replace_TskS ms s).(StatsState) = s.(StatsState) /\
  (replace_TskS ms s).(ControlState) = s.(ControlState) /\
  (replace_TskS ms s).(NameState) = s.(NameState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma replace_SchedS_put_back : forall s,
  replace_SchedS s.(SchedState) s = s.
Proof. intros []; reflexivity. Qed.

Lemma replace_SchedS_last_write : forall (a b : SchedAbstractState) s,
  replace_SchedS b (replace_SchedS a s) = replace_SchedS b s.
Proof. intros; reflexivity. Qed.

Lemma replace_SchedS_frame : forall ms s,
  (replace_SchedS ms s).(IntrState) = s.(IntrState) /\
  (replace_SchedS ms s).(TickState) = s.(TickState) /\
  (replace_SchedS ms s).(TskState) = s.(TskState) /\
  (replace_SchedS ms s).(EventState) = s.(EventState) /\
  (replace_SchedS ms s).(FlagState) = s.(FlagState) /\
  (replace_SchedS ms s).(MemoryState) = s.(MemoryState) /\
  (replace_SchedS ms s).(TimerState) = s.(TimerState) /\
  (replace_SchedS ms s).(StatsState) = s.(StatsState) /\
  (replace_SchedS ms s).(ControlState) = s.(ControlState) /\
  (replace_SchedS ms s).(NameState) = s.(NameState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma replace_EventS_put_back : forall s,
  replace_EventS s.(EventState) s = s.
Proof. intros []; reflexivity. Qed.

Lemma replace_EventS_last_write : forall (a b : Glob_EventAbstractState) s,
  replace_EventS b (replace_EventS a s) = replace_EventS b s.
Proof. intros; reflexivity. Qed.

Lemma replace_EventS_frame : forall ms s,
  (replace_EventS ms s).(IntrState) = s.(IntrState) /\
  (replace_EventS ms s).(TickState) = s.(TickState) /\
  (replace_EventS ms s).(TskState) = s.(TskState) /\
  (replace_EventS ms s).(SchedState) = s.(SchedState) /\
  (replace_EventS ms s).(FlagState) = s.(FlagState) /\
  (replace_EventS ms s).(MemoryState) = s.(MemoryState) /\
  (replace_EventS ms s).(TimerState) = s.(TimerState) /\
  (replace_EventS ms s).(StatsState) = s.(StatsState) /\
  (replace_EventS ms s).(ControlState) = s.(ControlState) /\
  (replace_EventS ms s).(NameState) = s.(NameState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma replace_FlagS_put_back : forall s,
  replace_FlagS s.(FlagState) s = s.
Proof. intros []; reflexivity. Qed.

Lemma replace_FlagS_last_write : forall (a b : GlobFlagState) s,
  replace_FlagS b (replace_FlagS a s) = replace_FlagS b s.
Proof. intros; reflexivity. Qed.

Lemma replace_FlagS_FlagState : forall ms s,
  (replace_FlagS ms s).(FlagState) = ms.
Proof. reflexivity. Qed.

Lemma replace_FlagS_frame : forall ms s,
  (replace_FlagS ms s).(IntrState) = s.(IntrState) /\
  (replace_FlagS ms s).(TickState) = s.(TickState) /\
  (replace_FlagS ms s).(TskState) = s.(TskState) /\
  (replace_FlagS ms s).(SchedState) = s.(SchedState) /\
  (replace_FlagS ms s).(EventState) = s.(EventState) /\
  (replace_FlagS ms s).(MemoryState) = s.(MemoryState) /\
  (replace_FlagS ms s).(TimerState) = s.(TimerState) /\
  (replace_FlagS ms s).(StatsState) = s.(StatsState) /\
  (replace_FlagS ms s).(ControlState) = s.(ControlState) /\
  (replace_FlagS ms s).(NameState) = s.(NameState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma replace_MemoryS_put_back : forall s,
  replace_MemoryS s.(MemoryState) s = s.
Proof. intros []; reflexivity. Qed.

Lemma replace_MemoryS_last_write : forall (a b : GlobMemoryState) s,
  replace_MemoryS b (replace_MemoryS a s) = replace_MemoryS b s.
Proof. intros; reflexivity. Qed.

Lemma replace_MemoryS_MemoryState : forall ms s,
  (replace_MemoryS ms s).(MemoryState) = ms.
Proof. reflexivity. Qed.

Lemma replace_MemoryS_frame : forall ms s,
  (replace_MemoryS ms s).(IntrState) = s.(IntrState) /\
  (replace_MemoryS ms s).(TickState) = s.(TickState) /\
  (replace_MemoryS ms s).(TskState) = s.(TskState) /\
  (replace_MemoryS ms s).(SchedState) = s.(SchedState) /\
  (replace_MemoryS ms s).(EventState) = s.(EventState) /\
  (replace_MemoryS ms s).(FlagState) = s.(FlagState) /\
  (replace_MemoryS ms s).(TimerState) = s.(TimerState) /\
  (replace_MemoryS ms s).(StatsState) = s.(StatsState) /\
  (replace_MemoryS ms s).(ControlState) = s.(ControlState) /\
  (replace_MemoryS ms s).(NameState) = s.(NameState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma replace_TimerS_put_back : forall s,
  replace_TimerS s.(TimerState) s = s.
Proof. intros []; reflexivity. Qed.

Lemma replace_TimerS_last_write : forall (a b : GlobTimerState) s,
  replace_TimerS b (replace_TimerS a s) = replace_TimerS b s.
Proof. intros; reflexivity. Qed.

Lemma replace_TimerS_TimerState : forall ms s,
  (replace_TimerS ms s).(TimerState) = ms.
Proof. reflexivity. Qed.

Lemma replace_TimerS_frame : forall ms s,
  (replace_TimerS ms s).(IntrState) = s.(IntrState) /\
  (replace_TimerS ms s).(TickState) = s.(TickState) /\
  (replace_TimerS ms s).(TskState) = s.(TskState) /\
  (replace_TimerS ms s).(SchedState) = s.(SchedState) /\
  (replace_TimerS ms s).(EventState) = s.(EventState) /\
  (replace_TimerS ms s).(FlagState) = s.(FlagState) /\
  (replace_TimerS ms s).(MemoryState) = s.(MemoryState) /\
  (replace_TimerS ms s).(StatsState) = s.(StatsState) /\
  (replace_TimerS ms s).(ControlState) = s.(ControlState) /\
  (replace_TimerS ms s).(NameState) = s.(NameState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma replace_StatsS_put_back : forall s,
  replace_StatsS s.(StatsState) s = s.
Proof. intros []; reflexivity. Qed.

Lemma replace_StatsS_last_write : forall (a b : StatisticsState) s,
  replace_StatsS b (replace_StatsS a s) = replace_StatsS b s.
Proof. intros; reflexivity. Qed.

Lemma replace_StatsS_StatsState : forall ms s,
  (replace_StatsS ms s).(StatsState) = ms.
Proof. reflexivity. Qed.

Lemma replace_StatsS_frame : forall ms s,
  (replace_StatsS ms s).(IntrState) = s.(IntrState) /\
  (replace_StatsS ms s).(TickState) = s.(TickState) /\
  (replace_StatsS ms s).(TskState) = s.(TskState) /\
  (replace_StatsS ms s).(SchedState) = s.(SchedState) /\
  (replace_StatsS ms s).(EventState) = s.(EventState) /\
  (replace_StatsS ms s).(FlagState) = s.(FlagState) /\
  (replace_StatsS ms s).(MemoryState) = s.(MemoryState) /\
  (replace_StatsS ms s).(TimerState) = s.(TimerState) /\
  (replace_StatsS ms s).(ControlState) = s.(ControlState) /\
  (replace_StatsS ms s).(NameState) = s.(NameState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma replace_ControlS_put_back : forall s,
  replace_ControlS s.(ControlState) s = s.
Proof. intros []; reflexivity. Qed.

Lemma replace_ControlS_last_write : forall (a b : KernelControlState) s,
  replace_ControlS b (replace_ControlS a s) = replace_ControlS b s.
Proof. intros; reflexivity. Qed.

Lemma replace_ControlS_ControlState : forall ms s,
  (replace_ControlS ms s).(ControlState) = ms.
Proof. reflexivity. Qed.

Lemma replace_ControlS_frame : forall ms s,
  (replace_ControlS ms s).(IntrState) = s.(IntrState) /\
  (replace_ControlS ms s).(TickState) = s.(TickState) /\
  (replace_ControlS ms s).(TskState) = s.(TskState) /\
  (replace_ControlS ms s).(SchedState) = s.(SchedState) /\
  (replace_ControlS ms s).(EventState) = s.(EventState) /\
  (replace_ControlS ms s).(FlagState) = s.(FlagState) /\
  (replace_ControlS ms s).(MemoryState) = s.(MemoryState) /\
  (replace_ControlS ms s).(TimerState) = s.(TimerState) /\
  (replace_ControlS ms s).(StatsState) = s.(StatsState) /\
  (replace_ControlS ms s).(NameState) = s.(NameState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma replace_NameS_put_back : forall s,
  replace_NameS s.(NameState) s = s.
Proof. intros []; reflexivity. Qed.

Lemma replace_NameS_last_write : forall (a b : NameResourceState) s,
  replace_NameS b (replace_NameS a s) = replace_NameS b s.
Proof. intros; reflexivity. Qed.

Lemma replace_NameS_NameState : forall ms s,
  (replace_NameS ms s).(NameState) = ms.
Proof. reflexivity. Qed.

Lemma replace_NameS_frame : forall ms s,
  (replace_NameS ms s).(IntrState) = s.(IntrState) /\
  (replace_NameS ms s).(TickState) = s.(TickState) /\
  (replace_NameS ms s).(TskState) = s.(TskState) /\
  (replace_NameS ms s).(SchedState) = s.(SchedState) /\
  (replace_NameS ms s).(EventState) = s.(EventState) /\
  (replace_NameS ms s).(FlagState) = s.(FlagState) /\
  (replace_NameS ms s).(MemoryState) = s.(MemoryState) /\
  (replace_NameS ms s).(TimerState) = s.(TimerState) /\
  (replace_NameS ms s).(StatsState) = s.(StatsState) /\
  (replace_NameS ms s).(ControlState) = s.(ControlState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma replace_IntrS_TickS_commute : forall a b s,
  replace_IntrS a (replace_TickS b s) = replace_TickS b (replace_IntrS a s).
Proof. reflexivity. Qed.

Lemma replace_IntrS_TskS_commute : forall a b s,
  replace_IntrS a (replace_TskS b s) = replace_TskS b (replace_IntrS a s).
Proof. reflexivity. Qed.

Lemma replace_IntrS_SchedS_commute : forall a b s,
  replace_IntrS a (replace_SchedS b s) = replace_SchedS b (replace_IntrS a s).
Proof. reflexivity. Qed.

Lemma replace_IntrS_EventS_commute : forall a b s,
  replace_IntrS a (replace_EventS b s) = replace_EventS b (replace_IntrS a s).
Proof. reflexivity. Qed.

Lemma replace_IntrS_FlagS_commute : forall a b s,
  replace_IntrS a (replace_FlagS b s) = replace_FlagS b (replace_IntrS a s).
Proof. reflexivity. Qed.

Lemma replace_IntrS_MemoryS_commute : forall a b s,
  replace_IntrS a (replace_MemoryS b s) = replace_MemoryS b (replace_IntrS a s).
Proof. reflexivity. Qed.

Lemma replace_IntrS_TimerS_commute : forall a b s,
  replace_IntrS a (replace_TimerS b s) = replace_TimerS b (replace_IntrS a s).
Proof. reflexivity. Qed.

Lemma replace_IntrS_StatsS_commute : forall a b s,
  replace_IntrS a (replace_StatsS b s) = replace_StatsS b (replace_IntrS a s).
Proof. reflexivity. Qed.

Lemma replace_IntrS_ControlS_commute : forall a b s,
  replace_IntrS a (replace_ControlS b s) = replace_ControlS b (replace_IntrS a s).
Proof. reflexivity. Qed.

Lemma replace_IntrS_NameS_commute : forall a b s,
  replace_IntrS a (replace_NameS b s) = replace_NameS b (replace_IntrS a s).
Proof. reflexivity. Qed.

Lemma replace_TickS_TskS_commute : forall a b s,
  replace_TickS a (replace_TskS b s) = replace_TskS b (replace_TickS a s).
Proof. reflexivity. Qed.

Lemma replace_TickS_SchedS_commute : forall a b s,
  replace_TickS a (replace_SchedS b s) = replace_SchedS b (replace_TickS a s).
Proof. reflexivity. Qed.

Lemma replace_TickS_EventS_commute : forall a b s,
  replace_TickS a (replace_EventS b s) = replace_EventS b (replace_TickS a s).
Proof. reflexivity. Qed.

Lemma replace_TickS_FlagS_commute : forall a b s,
  replace_TickS a (replace_FlagS b s) = replace_FlagS b (replace_TickS a s).
Proof. reflexivity. Qed.

Lemma replace_TickS_MemoryS_commute : forall a b s,
  replace_TickS a (replace_MemoryS b s) = replace_MemoryS b (replace_TickS a s).
Proof. reflexivity. Qed.

Lemma replace_TickS_TimerS_commute : forall a b s,
  replace_TickS a (replace_TimerS b s) = replace_TimerS b (replace_TickS a s).
Proof. reflexivity. Qed.

Lemma replace_TickS_StatsS_commute : forall a b s,
  replace_TickS a (replace_StatsS b s) = replace_StatsS b (replace_TickS a s).
Proof. reflexivity. Qed.

Lemma replace_TickS_ControlS_commute : forall a b s,
  replace_TickS a (replace_ControlS b s) = replace_ControlS b (replace_TickS a s).
Proof. reflexivity. Qed.

Lemma replace_TickS_NameS_commute : forall a b s,
  replace_TickS a (replace_NameS b s) = replace_NameS b (replace_TickS a s).
Proof. reflexivity. Qed.

Lemma replace_TskS_SchedS_commute : forall a b s,
  replace_TskS a (replace_SchedS b s) = replace_SchedS b (replace_TskS a s).
Proof. reflexivity. Qed.

Lemma replace_TskS_EventS_commute : forall a b s,
  replace_TskS a (replace_EventS b s) = replace_EventS b (replace_TskS a s).
Proof. reflexivity. Qed.

Lemma replace_TskS_FlagS_commute : forall a b s,
  replace_TskS a (replace_FlagS b s) = replace_FlagS b (replace_TskS a s).
Proof. reflexivity. Qed.

Lemma replace_TskS_MemoryS_commute : forall a b s,
  replace_TskS a (replace_MemoryS b s) = replace_MemoryS b (replace_TskS a s).
Proof. reflexivity. Qed.

Lemma replace_TskS_TimerS_commute : forall a b s,
  replace_TskS a (replace_TimerS b s) = replace_TimerS b (replace_TskS a s).
Proof. reflexivity. Qed.

Lemma replace_TskS_StatsS_commute : forall a b s,
  replace_TskS a (replace_StatsS b s) = replace_StatsS b (replace_TskS a s).
Proof. reflexivity. Qed.

Lemma replace_TskS_ControlS_commute : forall a b s,
  replace_TskS a (replace_ControlS b s) = replace_ControlS b (replace_TskS a s).
Proof. reflexivity. Qed.

Lemma replace_TskS_NameS_commute : forall a b s,
  replace_TskS a (replace_NameS b s) = replace_NameS b (replace_TskS a s).
Proof. reflexivity. Qed.

Lemma replace_SchedS_EventS_commute : forall a b s,
  replace_SchedS a (replace_EventS b s) = replace_EventS b (replace_SchedS a s).
Proof. reflexivity. Qed.

Lemma replace_SchedS_FlagS_commute : forall a b s,
  replace_SchedS a (replace_FlagS b s) = replace_FlagS b (replace_SchedS a s).
Proof. reflexivity. Qed.

Lemma replace_SchedS_MemoryS_commute : forall a b s,
  replace_SchedS a (replace_MemoryS b s) = replace_MemoryS b (replace_SchedS a s).
Proof. reflexivity. Qed.

Lemma replace_SchedS_TimerS_commute : forall a b s,
  replace_SchedS a (replace_TimerS b s) = replace_TimerS b (replace_SchedS a s).
Proof. reflexivity. Qed.

Lemma replace_SchedS_StatsS_commute : forall a b s,
  replace_SchedS a (replace_StatsS b s) = replace_StatsS b (replace_SchedS a s).
Proof. reflexivity. Qed.

Lemma replace_SchedS_ControlS_commute : forall a b s,
  replace_SchedS a (replace_ControlS b s) = replace_ControlS b (replace_SchedS a s).
Proof. reflexivity. Qed.

Lemma replace_SchedS_NameS_commute : forall a b s,
  replace_SchedS a (replace_NameS b s) = replace_NameS b (replace_SchedS a s).
Proof. reflexivity. Qed.

Lemma replace_EventS_FlagS_commute : forall a b s,
  replace_EventS a (replace_FlagS b s) = replace_FlagS b (replace_EventS a s).
Proof. reflexivity. Qed.

Lemma replace_EventS_MemoryS_commute : forall a b s,
  replace_EventS a (replace_MemoryS b s) = replace_MemoryS b (replace_EventS a s).
Proof. reflexivity. Qed.

Lemma replace_EventS_TimerS_commute : forall a b s,
  replace_EventS a (replace_TimerS b s) = replace_TimerS b (replace_EventS a s).
Proof. reflexivity. Qed.

Lemma replace_EventS_StatsS_commute : forall a b s,
  replace_EventS a (replace_StatsS b s) = replace_StatsS b (replace_EventS a s).
Proof. reflexivity. Qed.

Lemma replace_EventS_ControlS_commute : forall a b s,
  replace_EventS a (replace_ControlS b s) = replace_ControlS b (replace_EventS a s).
Proof. reflexivity. Qed.

Lemma replace_EventS_NameS_commute : forall a b s,
  replace_EventS a (replace_NameS b s) = replace_NameS b (replace_EventS a s).
Proof. reflexivity. Qed.

Lemma replace_FlagS_MemoryS_commute : forall a b s,
  replace_FlagS a (replace_MemoryS b s) = replace_MemoryS b (replace_FlagS a s).
Proof. reflexivity. Qed.

Lemma replace_FlagS_TimerS_commute : forall a b s,
  replace_FlagS a (replace_TimerS b s) = replace_TimerS b (replace_FlagS a s).
Proof. reflexivity. Qed.

Lemma replace_FlagS_StatsS_commute : forall a b s,
  replace_FlagS a (replace_StatsS b s) = replace_StatsS b (replace_FlagS a s).
Proof. reflexivity. Qed.

Lemma replace_FlagS_ControlS_commute : forall a b s,
  replace_FlagS a (replace_ControlS b s) = replace_ControlS b (replace_FlagS a s).
Proof. reflexivity. Qed.

Lemma replace_FlagS_NameS_commute : forall a b s,
  replace_FlagS a (replace_NameS b s) = replace_NameS b (replace_FlagS a s).
Proof. reflexivity. Qed.

Lemma replace_MemoryS_TimerS_commute : forall a b s,
  replace_MemoryS a (replace_TimerS b s) = replace_TimerS b (replace_MemoryS a s).
Proof. reflexivity. Qed.

Lemma replace_MemoryS_StatsS_commute : forall a b s,
  replace_MemoryS a (replace_StatsS b s) = replace_StatsS b (replace_MemoryS a s).
Proof. reflexivity. Qed.

Lemma replace_MemoryS_ControlS_commute : forall a b s,
  replace_MemoryS a (replace_ControlS b s) = replace_ControlS b (replace_MemoryS a s).
Proof. reflexivity. Qed.

Lemma replace_MemoryS_NameS_commute : forall a b s,
  replace_MemoryS a (replace_NameS b s) = replace_NameS b (replace_MemoryS a s).
Proof. reflexivity. Qed.

Lemma replace_TimerS_StatsS_commute : forall a b s,
  replace_TimerS a (replace_StatsS b s) = replace_StatsS b (replace_TimerS a s).
Proof. reflexivity. Qed.

Lemma replace_TimerS_ControlS_commute : forall a b s,
  replace_TimerS a (replace_ControlS b s) = replace_ControlS b (replace_TimerS a s).
Proof. reflexivity. Qed.

Lemma replace_TimerS_NameS_commute : forall a b s,
  replace_TimerS a (replace_NameS b s) = replace_NameS b (replace_TimerS a s).
Proof. reflexivity. Qed.

Lemma replace_StatsS_ControlS_commute : forall a b s,
  replace_StatsS a (replace_ControlS b s) = replace_ControlS b (replace_StatsS a s).
Proof. reflexivity. Qed.

Lemma replace_StatsS_NameS_commute : forall a b s,
  replace_StatsS a (replace_NameS b s) = replace_NameS b (replace_StatsS a s).
Proof. reflexivity. Qed.

Lemma replace_ControlS_NameS_commute : forall a b s,
  replace_ControlS a (replace_NameS b s) = replace_NameS b (replace_ControlS a s).
Proof. reflexivity. Qed.
