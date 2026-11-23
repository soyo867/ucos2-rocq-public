Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem.
Import ListNotations.
Local Open Scope Z_scope.

(** Configuration is immutable; optional global cells are described here,
    while their values belong to the corresponding module state. Physical
    layout claims below state their required configuration explicitly. *)
Record KernelConfiguration : Type := {
  cfgFlagBits : Z;
  cfgMaxFlags : Z;
  cfgMaxMemPartitions : Z;
  cfgMaxTimers : Z;
  cfgTimerWheelSize : Z;
  cfgTicksPerSecond : Z;
  cfgTimerTicksPerSecond : Z;
  cfgTaskRegisters : Z;
  cfgTLSSize : Z;
  cfgFlagEnabled : bool;
  cfgMemoryEnabled : bool;
  cfgTimerEnabled : bool;
  cfgStatisticsEnabled : bool;
  cfgEventMultiEnabled : bool;
  cfgEventNames : bool;
  cfgTaskNames : bool;
  cfgFlagNames : bool;
  cfgMemoryNames : bool;
  cfgTimerNames : bool;
  cfgTaskProfile : bool;
  cfgTaskDelete : bool;
  cfgTaskCreateExt : bool;
  cfgFlagClearWait : bool;
  cfgTimeGetSet : bool;
  cfgTickStep : bool;
  cfgSafetyCritical : bool;
  cfgSafetyCriticalIEC : bool;
  cfgDebug : bool;
  cfgArgumentChecks : bool
}.

Definition selected_kernel_configuration : KernelConfiguration :=
  {| cfgFlagBits := 16; cfgMaxFlags := 5; cfgMaxMemPartitions := 5;
     cfgMaxTimers := 16; cfgTimerWheelSize := 7; cfgTicksPerSecond := 100;
     cfgTimerTicksPerSecond := 10; cfgTaskRegisters := 1; cfgTLSSize := 0;
     cfgFlagEnabled := true; cfgMemoryEnabled := true; cfgTimerEnabled := true;
     cfgStatisticsEnabled := true; cfgEventMultiEnabled := false;
     cfgEventNames := false; cfgTaskNames := true; cfgFlagNames := true;
     cfgMemoryNames := true; cfgTimerNames := true; cfgTaskProfile := false;
     cfgTaskDelete := true; cfgTaskCreateExt := true; cfgFlagClearWait := true;
     cfgTimeGetSet := true; cfgTickStep := true; cfgSafetyCritical := false;
     cfgSafetyCriticalIEC := false; cfgDebug := true; cfgArgumentChecks := true |}.

(** The upstream template with Multi, Event names and Task profiling enabled
    together. Keep the historical profile above unchanged. Configuration validity
    below does not establish that a representation supports this profile: its
    92-byte TCB must not be interpreted using the 64/72-byte non-profile layouts. *)
Definition full_features_kernel_configuration : KernelConfiguration :=
  {| cfgFlagBits := 16; cfgMaxFlags := 5; cfgMaxMemPartitions := 5;
     cfgMaxTimers := 16; cfgTimerWheelSize := 7; cfgTicksPerSecond := 100;
     cfgTimerTicksPerSecond := 10; cfgTaskRegisters := 1; cfgTLSSize := 0;
     cfgFlagEnabled := true; cfgMemoryEnabled := true; cfgTimerEnabled := true;
     cfgStatisticsEnabled := true; cfgEventMultiEnabled := true;
     cfgEventNames := true; cfgTaskNames := true; cfgFlagNames := true;
     cfgMemoryNames := true; cfgTimerNames := true; cfgTaskProfile := true;
     cfgTaskDelete := true; cfgTaskCreateExt := true; cfgFlagClearWait := true;
     cfgTimeGetSet := true; cfgTickStep := true; cfgSafetyCritical := false;
     cfgSafetyCriticalIEC := false; cfgDebug := true; cfgArgumentChecks := true |}.

Record StableGlobVars : Type := {
  (* 容量 *)
  osMaxEvents        : Z;
  osMaxQs            : Z;
  osMaxTasks         : Z;
  osNSysTasks        : Z;
  osLowestPrio       : Z;

  (* 静态池基址 *)
  g_OSEventTbl       : addr;
  g_OSQTbl           : addr;
  g_OSTCBTbl         : addr;
  g_OSTCBPrioTbl     : addr;
  g_OSUnMapTbl       : addr;

  (* 优先级特殊值 *)
  osTaskIdlePrio     : Z;
  osTaskStatPrio     : Z;
  osPrioMutexCeilDis : Z;
  osPrioSelf         : Z;

  (* 派生配置 *)
  osRdyTblSize       : Z;
  osEventTblSize     : Z;

  (* 各全局变量的地址 *)
  g_OSRdyGrp         : addr;
  g_OSRdyTbl         : addr;
  g_OSPrioCur        : addr;
  g_OSPrioHighRdy    : addr;
  g_OSTCBCur         : addr;
  g_OSTCBHighRdy     : addr;
  g_OSCtxSwCtr       : addr;
  g_OSRunning        : addr;
  g_OSIntNesting     : addr;
  g_OSLockNesting    : addr;
  g_OSTime           : addr;
  g_OSTaskCtr        : addr;
  g_OSEventFreeList  : addr;
  g_OSQFreeList      : addr;
  g_OSTCBFreeList    : addr;
  g_OSTCBList        : addr;
  g_OSTickStepState  : addr;
  g_OSFlagTbl        : addr;
  g_OSFlagFreeList   : addr;
  g_OSMemTbl         : addr;
  g_OSMemFreeList    : addr;
  g_OSTmrTbl         : addr;
  g_OSTmrFreeList    : addr;
  g_OSTmrWheelTbl    : addr;
  g_OSTmrFree        : addr;
  g_OSTmrUsed        : addr;
  g_OSTmrTime        : addr;
  g_OSTmrSem         : addr;
  g_OSTmrSemSignal   : addr;
  g_OSIdleCtr        : addr;
  g_OSIdleCtrMax     : addr;
  g_OSIdleCtrRun     : addr;
  g_OSCPUUsage       : addr;
  g_OSStatRdy        : addr;
  g_OSTaskRegNextAvailID : addr;
  g_OSTaskIdleStk    : addr;
  g_OSTaskStatStk    : addr;
  g_OSTmrTaskStk     : addr;
  g_OSSafetyCriticalStartFlag : addr;
  osKernelConfig    : KernelConfiguration;
}.

(** Core address facts retained for the existing local encoders.  The complete
    selected-layout interval constraint is part of [selected_kernel_profile]
    below; this list alone does not describe all enabled global storage. *)
Definition stable_global_addresses (sg : StableGlobVars) : list addr :=
  [ sg.(g_OSEventTbl); sg.(g_OSQTbl); sg.(g_OSTCBTbl); sg.(g_OSTCBPrioTbl);
    sg.(g_OSUnMapTbl); sg.(g_OSRdyGrp); sg.(g_OSRdyTbl);
    sg.(g_OSPrioCur); sg.(g_OSPrioHighRdy); sg.(g_OSTCBCur);
    sg.(g_OSTCBHighRdy); sg.(g_OSCtxSwCtr); sg.(g_OSRunning);
    sg.(g_OSIntNesting); sg.(g_OSLockNesting); sg.(g_OSTime);
    sg.(g_OSTaskCtr); sg.(g_OSEventFreeList); sg.(g_OSQFreeList);
    sg.(g_OSTCBFreeList);
    sg.(g_OSTCBList); sg.(g_OSTickStepState) ].

Definition valid_stable_global_addresses (sg : StableGlobVars) : Prop :=
  Forall (fun a => 0 < a) (stable_global_addresses sg) /\
  NoDup (stable_global_addresses sg).

Definition Priority : Type := Z.

(* 容量合法性 + 内存基址非零(物理布局约束:event/tcb 表基址 > 0) *)
(* g_OSEventTbl > 0 是 event_addr_nonzero 的建模根据 *)
Definition valid_stable_glob_vars (sg : StableGlobVars) : Prop :=
  sg.(osMaxEvents) > 0 /\
  sg.(osMaxQs) > 0 /\
  sg.(osMaxTasks) > 0 /\
  sg.(osNSysTasks) >= 0 /\
  0 < sg.(osLowestPrio) < 256 /\
  sg.(osLowestPrio) = 63 /\
  sg.(osTaskIdlePrio) = sg.(osLowestPrio) /\
  sg.(osTaskStatPrio) = sg.(osLowestPrio) - 1 /\
  sg.(osPrioMutexCeilDis) = 0xFF /\
  sg.(osPrioSelf) = 0xFF /\
  sg.(osRdyTblSize) = (sg.(osLowestPrio) / 8) + 1 /\
  sg.(osEventTblSize) = (sg.(osLowestPrio) / 8) + 1 /\
  valid_stable_global_addresses sg.

Definition valid_event_id (sg : StableGlobVars) (eid : Z) : Prop :=
  0 <= eid /\ eid < sg.(osMaxEvents).

Definition valid_queue_id (sg : StableGlobVars) (qid : Z) : Prop :=
  0 <= qid /\ qid < sg.(osMaxQs).

Definition verification_slice_priority_index (sg : StableGlobVars) (p : Z) : Prop :=
  0 <= p /\ p < sg.(osLowestPrio).

(** The native table contains OS_LOWEST_PRIO + 1 entries.  Keep the
    historical slice/API guard above separate: idle is a native task/table
    priority, while a mutex PCP must remain strictly below idle. *)
Definition task_priority_in_range (sg : StableGlobVars) (p : Z) : Prop :=
  0 <= p <= sg.(osLowestPrio).

Definition task_slot_in_range (sg : StableGlobVars) (tid : Z) : Prop :=
  0 <= tid < sg.(osMaxTasks) + sg.(osNSysTasks).

(** In the selected 32-bit, eight-row ABI, OSEventName adds a pointer after
    the common 20-byte ECB. WaitMulti does not change this layout. Keep the
    address owner here so Task pointers and Event predicates share one
    encoder without an import cycle. *)
Definition event_object_size (c : KernelConfiguration) : Z :=
  if c.(cfgEventNames) then 24 else 20.
Definition event_pool_addr (sg : StableGlobVars) (eid : Z) : addr :=
  sg.(g_OSEventTbl) + eid * event_object_size sg.(osKernelConfig).

Lemma event_object_size_positive : forall config, 0 < event_object_size config.
Proof. intros; unfold event_object_size; destruct config.(cfgEventNames); lia. Qed.

Lemma event_pool_addr_injective : forall sg first second,
  event_pool_addr sg first = event_pool_addr sg second -> first = second.
Proof.
  intros sg first second Heq; unfold event_pool_addr, event_object_size in Heq.
  destruct sg.(osKernelConfig).(cfgEventNames); lia.
Qed.

Lemma event_pool_addr_no_names : forall sg eid,
  sg.(osKernelConfig).(cfgEventNames) = false ->
  event_pool_addr sg eid = sg.(g_OSEventTbl) + eid * 20.
Proof. intros; unfold event_pool_addr, event_object_size; rewrite H; reflexivity. Qed.

Definition valid_mutex_pcp (sg : StableGlobVars) (pcp : Z) : Prop :=
  pcp = sg.(osPrioMutexCeilDis) \/
  (0 <= pcp /\ pcp < sg.(osLowestPrio)).

Definition os_int_nesting_addr (sg : StableGlobVars) (p : addr) : Prop :=
  p = sg.(g_OSIntNesting).

Definition os_lock_nesting_addr (sg : StableGlobVars) (p : addr) : Prop :=
  p = sg.(g_OSLockNesting).

Definition os_rdy_grp_addr (sg : StableGlobVars) (p : addr) : Prop :=
  p = sg.(g_OSRdyGrp).

Definition os_rdy_tbl_addr (sg : StableGlobVars) (p : addr) : Prop :=
  p = sg.(g_OSRdyTbl).

Definition os_prio_cur_addr (sg : StableGlobVars) (p : addr) : Prop :=
  p = sg.(g_OSPrioCur).

Definition os_tcb_cur_addr (sg : StableGlobVars) (p : addr) : Prop :=
  p = sg.(g_OSTCBCur).

Definition os_tcb_prio_tbl_addr (sg : StableGlobVars) (p : addr) : Prop :=
  p = sg.(g_OSTCBPrioTbl).

Definition os_event_free_list_addr (sg : StableGlobVars) (p : addr) : Prop :=
  p = sg.(g_OSEventFreeList).

Definition os_q_free_list_addr (sg : StableGlobVars) (p : addr) : Prop :=
  p = sg.(g_OSQFreeList).

Definition valid_kernel_configuration (c : KernelConfiguration) : Prop :=
  (c.(cfgFlagBits) = 8 \/ c.(cfgFlagBits) = 16 \/ c.(cfgFlagBits) = 32) /\
  0 <= c.(cfgMaxFlags) <= 65500 /\
  0 <= c.(cfgMaxMemPartitions) <= 65500 /\
  (c.(cfgTimerEnabled) = true ->
     2 <= c.(cfgMaxTimers) <= 65500 /\ 2 <= c.(cfgTimerWheelSize) <= 1024) /\
  0 < c.(cfgTicksPerSecond) /\ 0 < c.(cfgTimerTicksPerSecond) /\
  0 <= c.(cfgTaskRegisters) <= 255 /\ 0 <= c.(cfgTLSSize).

Lemma selected_kernel_configuration_valid :
  valid_kernel_configuration selected_kernel_configuration.
Proof. unfold valid_kernel_configuration, selected_kernel_configuration; simpl; lia. Qed.

Lemma full_features_kernel_configuration_valid :
  valid_kernel_configuration full_features_kernel_configuration.
Proof.
  unfold valid_kernel_configuration, full_features_kernel_configuration; simpl; lia.
Qed.

(** Exactly the enabled fields of the selected 64-byte OS_TCB, not a claim
    about every legal macro combination. In ucos_ii.h, FlagNode and FlagsRdy
    require both OS_FLAG_EN > 0 and OS_MAX_FLAGS > 0; enabling Flag alone is
    not sufficient. Unrelated Memory/Timer switches do not change this layout. *)
Definition tcb64_configuration (c : KernelConfiguration) : Prop :=
  c.(cfgFlagEnabled) = true /\ c.(cfgFlagBits) = 16 /\
  c.(cfgTaskCreateExt) = true /\ c.(cfgTaskDelete) = true /\
  c.(cfgTaskNames) = true /\ c.(cfgTaskRegisters) = 1 /\
  c.(cfgTLSSize) = 0 /\ c.(cfgTaskProfile) = false /\
  c.(cfgEventMultiEnabled) = false /\ 0 < c.(cfgMaxFlags).

(** Common source layout constraints. Multi adds two pointers and profiling
    adds five 32-bit cells; neither switch changes the remaining field set.
    Event names affect the ECB, not this TCB configuration. *)
Definition task_layout_configuration (c : KernelConfiguration) : Prop :=
  c.(cfgFlagEnabled) = true /\ c.(cfgFlagBits) = 16 /\
  c.(cfgTaskCreateExt) = true /\ c.(cfgTaskDelete) = true /\
  c.(cfgTaskNames) = true /\ c.(cfgTaskRegisters) = 1 /\
  c.(cfgTLSSize) = 0 /\ 0 < c.(cfgMaxFlags).

Definition tcb_layout_size (multi : bool) : Z := if multi then 72 else 64.
Definition tcb_configured_size (multi profile : bool) : Z :=
  tcb_layout_size multi + if profile then 20 else 0.
Definition task_object_size (c : KernelConfiguration) : Z :=
  tcb_configured_size c.(cfgEventMultiEnabled) c.(cfgTaskProfile).

Lemma tcb64_configuration_implies_task_layout : forall c,
  tcb64_configuration c -> task_layout_configuration c.
Proof. unfold tcb64_configuration, task_layout_configuration; tauto. Qed.

Lemma full_features_kernel_configuration_task_layout :
  task_layout_configuration full_features_kernel_configuration.
Proof. unfold task_layout_configuration, full_features_kernel_configuration; simpl; lia. Qed.

Lemma task_object_size_tcb64 : forall c,
  tcb64_configuration c -> task_object_size c = 64.
Proof.
  intros c H; unfold tcb64_configuration in H.
  assert (Hmulti : c.(cfgEventMultiEnabled) = false) by tauto.
  assert (Hprofile : c.(cfgTaskProfile) = false) by tauto.
  unfold task_object_size; rewrite Hmulti, Hprofile; reflexivity.
Qed.

Lemma full_features_task_object_size :
  task_object_size full_features_kernel_configuration = 92.
Proof. reflexivity. Qed.

Lemma selected_kernel_configuration_tcb64 :
  tcb64_configuration selected_kernel_configuration.
Proof.
  unfold tcb64_configuration, selected_kernel_configuration; simpl; lia.
Qed.

Lemma full_features_kernel_configuration_not_tcb64 :
  ~ tcb64_configuration full_features_kernel_configuration.
Proof.
  unfold tcb64_configuration, full_features_kernel_configuration; simpl; intuition discriminate.
Qed.

Definition kernel_align4 (n : Z) : Z := ((n + 3) / 4) * 4.
Definition flag_word_bytes (c : KernelConfiguration) := c.(cfgFlagBits) / 8.
Definition flag_group_name_offset (c : KernelConfiguration) :=
  kernel_align4 (8 + flag_word_bytes c).
Definition flag_group_size (c : KernelConfiguration) :=
  flag_group_name_offset c + if c.(cfgFlagNames) then 4 else 0.
Definition flag_node_mode_offset (c : KernelConfiguration) := 16 + flag_word_bytes c.
Definition flag_node_size (c : KernelConfiguration) :=
  kernel_align4 (flag_node_mode_offset c + 1).
Definition memory_control_size (c : KernelConfiguration) :=
  if c.(cfgMemoryNames) then 24 else 20.
Definition timer_option_offset (c : KernelConfiguration) :=
  if c.(cfgTimerNames) then 36 else 32.
Definition timer_object_size (c : KernelConfiguration) :=
  timer_option_offset c + 4.
Definition timer_wheel_spoke_size : Z := 8.

Definition flag_pool_addr (sg : StableGlobVars) (i : Z) : addr :=
  sg.(g_OSFlagTbl) + i * flag_group_size sg.(osKernelConfig).
Definition memory_control_addr (sg : StableGlobVars) (i : Z) : addr :=
  sg.(g_OSMemTbl) + i * memory_control_size sg.(osKernelConfig).
Definition timer_pool_addr (sg : StableGlobVars) (i : Z) : addr :=
  sg.(g_OSTmrTbl) + i * timer_object_size sg.(osKernelConfig).

(** Regions are half-open byte intervals.  Base-address inequality is not
    a substitute for the pairwise interval separation below. *)
Definition kernel_region_valid (r : addr * Z) : Prop :=
  0 < fst r /\ 0 <= snd r /\ fst r + snd r <= 4294967296.
Definition kernel_regions_disjoint (a b : addr * Z) : Prop :=
  fst a + snd a <= fst b \/ fst b + snd b <= fst a.
Definition kernel_region_layout_valid (rs : list (addr * Z)) : Prop :=
  Forall kernel_region_valid rs /\
  forall i j a b, nth_error rs i = Some a -> nth_error rs j = Some b ->
    i <> j -> kernel_regions_disjoint a b.

Lemma selected_independent_layout_sizes :
  flag_group_size selected_kernel_configuration = 16 /\
  flag_node_size selected_kernel_configuration = 20 /\
  memory_control_size selected_kernel_configuration = 24 /\
  timer_object_size selected_kernel_configuration = 40.
Proof. repeat split; reflexivity. Qed.

(** OS_MemClr takes INT16U, even when sizeof is wider.  These are source
    initialization preconditions, not hidden guards in the initializer. *)
Definition valid_kernel_initialization_layout (c : KernelConfiguration) : Prop :=
  (c.(cfgFlagEnabled) = true -> 1 <= c.(cfgMaxFlags) /\
    flag_group_size c * c.(cfgMaxFlags) <= 65535) /\
  (c.(cfgMemoryEnabled) = true -> 1 <= c.(cfgMaxMemPartitions) /\
    memory_control_size c * c.(cfgMaxMemPartitions) <= 65535) /\
  (c.(cfgTimerEnabled) = true -> 2 <= c.(cfgMaxTimers) /\
    timer_object_size c * c.(cfgMaxTimers) <= 65535 /\
    2 <= c.(cfgTimerWheelSize) /\ timer_wheel_spoke_size * c.(cfgTimerWheelSize) <= 65535).
Lemma selected_kernel_initialization_layout_valid :
  valid_kernel_initialization_layout selected_kernel_configuration.
Proof. unfold valid_kernel_initialization_layout, selected_kernel_configuration; simpl; lia. Qed.

Definition kernel_independent_regions (sg : StableGlobVars) : list (addr * Z) :=
  (if andb sg.(osKernelConfig).(cfgFlagEnabled)
           (Z.ltb 0 sg.(osKernelConfig).(cfgMaxFlags)) then
    [(sg.(g_OSFlagTbl), flag_group_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxFlags));
     (sg.(g_OSFlagFreeList), 4)] else []) ++
  (if andb sg.(osKernelConfig).(cfgMemoryEnabled)
           (Z.ltb 0 sg.(osKernelConfig).(cfgMaxMemPartitions)) then
    [(sg.(g_OSMemTbl), memory_control_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxMemPartitions));
     (sg.(g_OSMemFreeList), 4)] else []) ++
  (if sg.(osKernelConfig).(cfgTimerEnabled) then
    [(sg.(g_OSTmrTbl), timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers));
     (sg.(g_OSTmrWheelTbl), timer_wheel_spoke_size * sg.(osKernelConfig).(cfgTimerWheelSize));
     (sg.(g_OSTmrFreeList), 4); (sg.(g_OSTmrFree), 2);
     (sg.(g_OSTmrUsed), 2); (sg.(g_OSTmrTime), 4);
     (sg.(g_OSTmrSem), 4); (sg.(g_OSTmrSemSignal), 4)] else []) ++
  [(sg.(g_OSIdleCtr), 4)] ++
  (if sg.(osKernelConfig).(cfgStatisticsEnabled) then
    [(sg.(g_OSIdleCtrMax), 4); (sg.(g_OSIdleCtrRun), 4);
     (sg.(g_OSCPUUsage), 1); (sg.(g_OSStatRdy), 1)] else []) ++
  (if sg.(osKernelConfig).(cfgSafetyCriticalIEC) then
    [(sg.(g_OSSafetyCriticalStartFlag), 1)] else []) ++
  (if Z.ltb 0 sg.(osKernelConfig).(cfgTaskRegisters) then
    [(sg.(g_OSTaskRegNextAvailID), 1)] else []).

(** Static global objects in the selected ARMv7-A/GNU layout family, not a
    layout for arbitrary macro combinations. Source/ucos_ii.h declares the
    pools/cells; OS_LOWEST_PRIO is 63, pointers and OS_STK are four bytes,
    OS_Q is 24 bytes, and TCB/ECB sizes follow their actual feature switches.
    config/queue-v2.93.01-first-round/os_cfg.h fixes each system stack at
    128 OS_STK words.  Optional globals follow their declaration guards.

    These intervals constrain addresses only.  In particular, mentioning a
    system stack here does not own a second copy of its array: its heap
    ownership still belongs to the caller/task stack lease and context
    resources.  Stack alignment and source-operation pointer bounds remain
    separate ABI obligations. *)
Definition selected_kernel_global_regions (sg : StableGlobVars) : list (addr * Z) :=
  [(sg.(g_OSEventTbl), event_object_size sg.(osKernelConfig) * sg.(osMaxEvents));
   (sg.(g_OSQTbl), 24 * sg.(osMaxQs));
   (sg.(g_OSTCBTbl), task_object_size sg.(osKernelConfig) * (sg.(osMaxTasks) + sg.(osNSysTasks)));
   (sg.(g_OSTCBPrioTbl), 4 * (sg.(osLowestPrio) + 1));
   (sg.(g_OSUnMapTbl), 256);
   (sg.(g_OSRdyGrp), 1); (sg.(g_OSRdyTbl), sg.(osRdyTblSize));
   (sg.(g_OSPrioCur), 1); (sg.(g_OSPrioHighRdy), 1);
   (sg.(g_OSTCBCur), 4); (sg.(g_OSTCBHighRdy), 4);
   (sg.(g_OSCtxSwCtr), 4); (sg.(g_OSRunning), 1);
   (sg.(g_OSIntNesting), 1); (sg.(g_OSLockNesting), 1);
   (sg.(g_OSTaskCtr), 1); (sg.(g_OSEventFreeList), 4);
   (sg.(g_OSQFreeList), 4); (sg.(g_OSTCBFreeList), 4);
   (sg.(g_OSTCBList), 4)] ++
  (if sg.(osKernelConfig).(cfgTimeGetSet) then
    [(sg.(g_OSTime), 4)] else []) ++
  (if sg.(osKernelConfig).(cfgTickStep) then
    [(sg.(g_OSTickStepState), 1)] else []) ++
  kernel_independent_regions sg ++
  [(sg.(g_OSTaskIdleStk), 128 * 4)] ++
  (if sg.(osKernelConfig).(cfgStatisticsEnabled) then
    [(sg.(g_OSTaskStatStk), 128 * 4)] else []) ++
  (if sg.(osKernelConfig).(cfgTimerEnabled) then
    [(sg.(g_OSTmrTaskStk), 128 * 4)] else []).

Definition valid_selected_kernel_global_layout (sg : StableGlobVars) : Prop :=
  kernel_region_layout_valid (selected_kernel_global_regions sg).

(** The basic TCB initializer clears the complete pool and retains its final
    one-past pointer.  Its safe-init contract therefore already requires this
    endpoint to fit UINT_MAX.  This is an additional static source-operation
    constraint; generic half-open region validity above remains unchanged. *)
Definition valid_tcb_pool_initialization_endpoint (sg : StableGlobVars) : Prop :=
  sg.(g_OSTCBTbl) + task_object_size sg.(osKernelConfig) *
    (sg.(osMaxTasks) + sg.(osNSysTasks)) <= 4294967295.

(** Immutable configuration and global layout are checked once at the kernel
    invariant boundary.  This is broader than the Task-only TCB layout above.
    The selected tick representation owns both optional tick cells, so their
    switches must be enabled.  An enabled Memory module must have its source
    globals present, which also requires a nonzero partition count. *)
Definition selected_kernel_profile (sg : StableGlobVars) : Prop :=
  valid_stable_glob_vars sg /\
  sg.(osMaxTasks) = 20 /\ sg.(osNSysTasks) = 2 /\
  valid_kernel_configuration sg.(osKernelConfig) /\
  tcb64_configuration sg.(osKernelConfig) /\
  sg.(osKernelConfig).(cfgEventNames) = false /\
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true /\
  sg.(osKernelConfig).(cfgTimeGetSet) = true /\
  sg.(osKernelConfig).(cfgTickStep) = true /\
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
    0 < sg.(osKernelConfig).(cfgMaxMemPartitions)) /\
  valid_selected_kernel_global_layout sg /\
  valid_tcb_pool_initialization_endpoint sg.

(** The source-faithful full-features entry point keeps the historical
    [selected_kernel_profile] closed over the 64-byte, names-disabled ABI.
    This predicate is deliberately additive: callers proving the full
    profile must establish the 92-byte TCB, the named 24-byte ECB and the
    enabled Multi/Profile fields explicitly.  It is not a weakening or an
    alias of the selected profile. *)
Definition full_features_kernel_global_regions (sg : StableGlobVars) :
  list (addr * Z) := selected_kernel_global_regions sg.

Definition valid_full_features_kernel_global_layout (sg : StableGlobVars) : Prop :=
  kernel_region_layout_valid (full_features_kernel_global_regions sg).

Definition full_features_kernel_profile (sg : StableGlobVars) : Prop :=
  valid_stable_glob_vars sg /\
  sg.(osMaxTasks) = 20 /\ sg.(osNSysTasks) = 2 /\
  sg.(osKernelConfig) = full_features_kernel_configuration /\
  valid_kernel_configuration sg.(osKernelConfig) /\
  task_layout_configuration sg.(osKernelConfig) /\
  sg.(osKernelConfig).(cfgEventMultiEnabled) = true /\
  sg.(osKernelConfig).(cfgEventNames) = true /\
  sg.(osKernelConfig).(cfgTaskNames) = true /\
  sg.(osKernelConfig).(cfgTaskProfile) = true /\
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true /\
  sg.(osKernelConfig).(cfgTimeGetSet) = true /\
  sg.(osKernelConfig).(cfgTickStep) = true /\
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
    0 < sg.(osKernelConfig).(cfgMaxMemPartitions)) /\
  valid_full_features_kernel_global_layout sg.

Lemma full_features_kernel_profile_event_layout : forall sg,
  full_features_kernel_profile sg ->
  event_object_size sg.(osKernelConfig) = 24 /\
  task_object_size sg.(osKernelConfig) = 92.
Proof.
  intros sg Hprofile.
  destruct Hprofile as [_ [_ [_ [_ [_ [_ [Hmulti [Hnames [_ [Hprofile
    [_ [_ [_ [_ _]]]]]]]]]]]]]].
  split.
  - unfold event_object_size; rewrite Hnames; reflexivity.
  - unfold task_object_size, tcb_configured_size, tcb_layout_size;
      rewrite Hmulti, Hprofile; reflexivity.
Qed.


Lemma valid_selected_kernel_global_layout_region :
  forall sg r,
    valid_selected_kernel_global_layout sg ->
    In r (selected_kernel_global_regions sg) ->
    kernel_region_valid r.
Proof.
  intros sg r Hlayout Hin.
  unfold valid_selected_kernel_global_layout, kernel_region_layout_valid in Hlayout.
  destruct Hlayout as [Hvalid _].
  rewrite Forall_forall in Hvalid.
  apply Hvalid; exact Hin.
Qed.

Lemma selected_kernel_profile_timer_pool_region_valid :
  forall sg,
    selected_kernel_profile sg ->
    sg.(osKernelConfig).(cfgTimerEnabled) = true ->
    kernel_region_valid
      (sg.(g_OSTmrTbl),
       timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)).
Proof.
  intros sg Hprofile Htimer.
  eapply (valid_selected_kernel_global_layout_region sg).
  - unfold selected_kernel_profile in Hprofile; tauto.
  - unfold selected_kernel_global_regions.
    apply in_or_app; right.
    apply in_or_app; right.
    apply in_or_app; right.
    apply in_or_app; left.
    unfold kernel_independent_regions.
    apply in_or_app; right.
    apply in_or_app; right.
    apply in_or_app; left.
    rewrite Htimer; simpl; auto.
Qed.

Lemma valid_stable_address_pos :
  forall sg a,
    valid_stable_glob_vars sg ->
    In a (stable_global_addresses sg) ->
    0 < a.
Proof.
  intros sg a Hvalid Hin.
  unfold valid_stable_glob_vars in Hvalid.
  do 12 (destruct Hvalid as [_ Hvalid]).
  unfold valid_stable_global_addresses in Hvalid.
  destruct Hvalid as [Hpos _].
  rewrite Forall_forall in Hpos.
  apply Hpos. exact Hin.
Qed.

Lemma selected_kernel_profile_tcb_pool_initialization_endpoint : forall sg,
  selected_kernel_profile sg -> valid_tcb_pool_initialization_endpoint sg.
Proof. intros sg Hprofile; unfold selected_kernel_profile in Hprofile; tauto. Qed.

Lemma selected_kernel_profile_tcb_slot_bounds : forall sg tid,
  selected_kernel_profile sg -> task_slot_in_range sg tid ->
  0 <= sg.(g_OSTCBTbl) + tid * task_object_size sg.(osKernelConfig) /\
  sg.(g_OSTCBTbl) + tid * task_object_size sg.(osKernelConfig) +
    task_object_size sg.(osKernelConfig) <= 4294967295.
Proof.
  intros sg tid Hprofile Hslot.
  pose proof Hprofile as [Hstable [Happ [Hsystem [_ [Hconfig _]]]]].
  pose proof (selected_kernel_profile_tcb_pool_initialization_endpoint sg Hprofile)
    as Hendpoint.
  pose proof (task_object_size_tcb64 _ Hconfig) as Hsize.
  pose proof (valid_stable_address_pos sg sg.(g_OSTCBTbl) Hstable
    ltac:(unfold stable_global_addresses; simpl; auto)) as Hbase.
  unfold valid_tcb_pool_initialization_endpoint in Hendpoint.
  unfold task_slot_in_range in Hslot.
  rewrite Hsize, Happ, Hsystem in Hendpoint.
  rewrite Happ, Hsystem in Hslot.
  rewrite Hsize; split; lia.
Qed.
