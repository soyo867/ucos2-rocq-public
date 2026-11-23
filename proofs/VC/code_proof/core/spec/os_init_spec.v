(** Public OSInit composition for the selected timer-v2.93.01 A32 NoVFP
    source. Startup owns raw objects; no initialized kernel invariant is an
    entry premise. The kernel-state observation omits private caller bytes,
    which are retained separately in the spatial postcondition. *)
Require Export Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.String Coq.micromega.Lia.
Require Export AUXLib.ListLib.
From SimpleC.SL Require Export Mem SeparationLogic.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.kernel_literal_resources.
Require Export Ucos2Verify.VC.code.interrupt.spec.os_init_hook_begin_spec.
Require Export Ucos2Verify.VC.code.core.spec.init_misc_spec.
Require Export Ucos2Verify.VC.code.sched.spec.init_rdy_list_spec.
Require Export Ucos2Verify.VC.code.core.spec.init_tcb_list_selected_spec.
Require Export Ucos2Verify.VC.code.event.spec.init_event_list_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_init_spec.
Require Export Ucos2Verify.VC.code.memory.spec.mem_init_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_init_generic_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_init_spec.
Require Export Ucos2Verify.VC.code.core.spec.kernel_stack_boot_spec.
Require Export Ucos2Verify.VC.code.core.spec.init_task_idle_continuation_spec.
Require Export Ucos2Verify.VC.code.core.spec.init_task_stat_continuation_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_init_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.os_init_hook_end_spec.
Require Export Ucos2Verify.VC.code.core.spec.os_debug_init_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_init_task_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_init_task_timer_phase_spec.
Require Export Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Require Export Ucos2Verify.VC.code.core.spec.kernel_program_boot_spec.
Require Export Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_name_resources_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Export Ucos2Verify.lib.event_pool Ucos2Verify.lib.queue_core Ucos2Verify.lib.event.
Require Export Ucos2Verify.lib.flag.
Require Export Ucos2Verify.lib.memory.
Require Export Ucos2Verify.lib.sched.
Require Export Ucos2Verify.lib.task.
Require Export Ucos2Verify.lib.timer.
Require Export Ucos2Verify.lib.kernel_execution.
Require Export Ucos2Verify.lib.kernel_names.
Require Export Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.kernel_program_storage.
Import ListNotations UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** OSTmrCtr is the original translation-unit-private UShort object. These
    are definitional consequences of the delivered Begin contract; there is
    no new extern declaration, allocation or trusted interface. *)
Definition os_init_hook_port_pre base base_cell dreg_cell initial frame : Assertion :=
  os_init_hook_begin_pre base base_cell dreg_cell &("OSTmrCtr") initial frame.
Definition os_init_hook_port_post base base_cell dreg_cell frame : Assertion :=
  os_init_hook_begin_post base base_cell dreg_cell &("OSTmrCtr") frame.
Lemma os_init_hook_port_pre_begin : forall base base_cell dreg_cell initial frame,
  os_init_hook_port_pre base base_cell dreg_cell initial frame |--
  os_init_hook_begin_pre base base_cell dreg_cell &("OSTmrCtr") initial frame.
Proof. intros; reflexivity. Qed.
Lemma os_init_hook_begin_post_port : forall base base_cell dreg_cell frame,
  os_init_hook_begin_post base base_cell dreg_cell &("OSTmrCtr") frame |--
  os_init_hook_port_post base base_cell dreg_cell frame.
Proof. intros; reflexivity. Qed.

Record OsInitContext := {
  os_init_timer : TmrInitContext;
  os_init_call : OsSchedCallContext;
  os_init_exception_initial : list (option Z);
  os_init_idle_lower : list (option Z);
  os_init_idle_frame : list (option Z);
  os_init_idle_upper : list (option Z);
  os_init_stat_lower : list (option Z);
  os_init_stat_frame : list (option Z);
  os_init_stat_upper : list (option Z)
}.
Definition os_init_sg p := p.(os_init_timer).(tmr_init_sg).
Definition os_init_environment p := p.(os_init_timer).(tmr_init_environment).
Definition os_init_critical p := p.(os_init_timer).(tmr_init_critical).
Definition os_init_mask p := p.(os_init_timer).(tmr_init_mask).
Definition os_init_literals p := p.(os_init_timer).(tmr_init_literals).
Definition os_init_literal_keys : list string := ["?"; "uC/OS-II Tmr"; "uC/OS-II Stat"; "uC/OS-II Idle"].
Definition os_init_names_idle p :=
  init_task_idle_register_name empty_name_resources 0 (os_init_literals p "uC/OS-II Idle").
Definition os_init_names_stat p :=
  init_task_stat_register_name (os_init_names_idle p) 1 (os_init_literals p "uC/OS-II Stat").
Definition os_init_names_timer p :=
  tmr_init_task_register_name (os_init_names_stat p) 2 (os_init_literals p "uC/OS-II Tmr").
Definition os_init_names p :=
  task_create_register_default_name (os_init_names_timer p) 3 (os_init_literals p "?").

(** One pointer per literal spelling is used throughout all thirteen calls.
    In particular every occurrence of "?" uses the same registered source.
    These three byte-domain conditions are static loader layout facts for
    the four different, non-suffix strings; they are not a requirement that
    different occurrences of the same spelling have different pointers. *)
Definition os_init_literal_layout p : Prop :=
  name_source_disjoint (os_init_names_idle p)
    (init_task_stat_name_source (os_init_literals p "uC/OS-II Stat")) /\
  name_source_disjoint (os_init_names_stat p)
    (tmr_init_task_name_source (os_init_literals p "uC/OS-II Tmr")) /\
  name_source_disjoint (os_init_names_timer p)
    (name_question_mark_source (os_init_literals p "?")).

Definition os_init_boot_state p := UCOS2_boot_state (os_init_sg p)
  (os_init_literals p "?") (os_init_literals p "?") (os_init_literals p "?") (os_init_names p).
Definition os_init_registered_state p :=
  replace_TskS (task_begin_invocation BootInvocation (os_init_boot_state p).(TskState))
    (os_init_boot_state p).

(** The raw observations record the exact results of the eight initializer
    calls. They are consumed by the startup-to-kernel view change, rather
    than pretending that an uninitialized allocation already has a kernel
    state. Queue's exact linked/zeroed bytes remain in its spatial spec. *)
Inductive OsInitInitialized : Type :=
| OsInitPort (aligned_top dreg timer_counter : Z)
| OsInitMisc (scalars : list Z)
| OsInitReady (scheduler : SchedAbstractState)
| OsInitTasks (tasks : Glob_TaskAbstractState)
| OsInitEvents (events : Glob_EventAbstractState)
| OsInitFlags (flags : GlobFlagState)
| OsInitMemory (memory : GlobMemoryState)
| OsInitQueues (free_ids : list Z).
Inductive OsInitState : Type :=
| OsInitRaw (initialized : list OsInitInitialized)
| OsInitKernel (state : UCOS2_Verify_State).
Definition os_init_raw_effects p : list OsInitInitialized :=
  [OsInitPort (((&("OS_CPU_ExceptStk") + 4096) / 8) * 8) 0 0;
   OsInitMisc (repeat 0 11); OsInitReady sched_boot;
   OsInitTasks (task_boot (os_init_sg p) (os_init_literals p "?"));
   OsInitEvents (event_pool_initial (os_init_sg p));
   OsInitFlags (flag_initial (os_init_sg p) (os_init_literals p "?"));
   OsInitMemory (memory_initial (os_init_sg p) (os_init_literals p "?"));
   OsInitQueues (queue_all_ids (os_init_sg p))].
Definition os_init_raw_state p (n : nat) := OsInitRaw (firstn n (os_init_raw_effects p)).
Definition os_init_raw_call p (n : nat) : program OsInitState unit :=
  fun before result after => before = os_init_raw_state p n /\ result = tt /\
    after = os_init_raw_state p (S n).
Definition os_init_kernel_view p : program OsInitState unit :=
  fun before result after => before = os_init_raw_state p 8 /\ result = tt /\
    after = OsInitKernel (os_init_registered_state p).
Definition os_init_lift {A} (c : program UCOS2_Verify_State A) : program OsInitState A :=
  fun before result after => exists first last,
    before = OsInitKernel first /\ after = OsInitKernel last /\ c first result last.
Definition os_init_idle_program p call :=
  init_task_idle_continuation_sequence (os_init_environment p) (os_init_critical p) (os_init_sg p)
    &("OS_TaskIdle") &("OSTaskIdleStk") &("OS_TaskReturn")
    p.(os_init_idle_lower) p.(os_init_idle_frame) p.(os_init_idle_upper)
    call (os_init_mask p) (os_init_literals p).
Definition os_init_stat_program p call :=
  init_task_stat_continuation_sequence (os_init_environment p) (os_init_critical p) (os_init_sg p)
    &("OS_TaskStat") &("OSTaskStatStk") &("OS_TaskReturn")
    p.(os_init_stat_lower) p.(os_init_stat_frame) p.(os_init_stat_upper)
    call (os_init_mask p) (os_init_literals p).
Definition os_init_after_timer : program OsInitState unit :=
  StateRelMonad.bind (StateRelMonad.ret tt) (fun _ =>
  StateRelMonad.bind (StateRelMonad.ret tt) (fun _ => StateRelMonad.ret tt)).
Definition os_init_timer_program p call : program OsInitState unit :=
  StateRelMonad.bind (os_init_lift (tmr_init_program p.(os_init_timer) call))
    (fun _ => os_init_after_timer).
Definition os_init_after_idle p call : program OsInitState unit :=
  StateRelMonad.bind (os_init_lift (os_init_stat_program p call))
    (fun returned => os_init_timer_program p returned).
Definition os_init_kernel_program p call : program OsInitState unit :=
  StateRelMonad.bind (os_init_lift (os_init_idle_program p call))
    (fun returned => os_init_after_idle p returned).
Definition os_init_after_raw p : program OsInitState unit :=
  StateRelMonad.bind (os_init_kernel_view p)
    (fun _ => os_init_kernel_program p p.(os_init_call)).
Fixpoint os_init_raw_tail p (n remaining : nat) : program OsInitState unit :=
  match remaining with
  | O => os_init_after_raw p
  | S count => StateRelMonad.bind (os_init_raw_call p n)
      (fun _ => os_init_raw_tail p (S n) count)
  end.
Definition os_init_program p := os_init_raw_tail p 0 8.
Definition os_init_raw_safe p n (X : unit -> OsInitState -> Prop) : Prop :=
  safeExec (eq (os_init_raw_state p n)) (os_init_raw_tail p n (8-n)) X.
Definition os_init_idle_continuation p (X : unit -> OsInitState -> Prop)
  : OsSchedCallContext -> UCOS2_Verify_State -> Prop := fun returned state =>
    safeExec (eq (OsInitKernel state)) (os_init_after_idle p returned) X.
Definition os_init_stat_continuation p (X : unit -> OsInitState -> Prop)
  : OsSchedCallContext -> UCOS2_Verify_State -> Prop := fun returned state =>
    safeExec (eq (OsInitKernel state)) (os_init_timer_program p returned) X.
Definition os_init_timer_continuation (X : unit -> OsInitState -> Prop)
  : unit -> UCOS2_Verify_State -> Prop := fun _ state =>
    safeExec (eq (OsInitKernel state)) os_init_after_timer X.

Lemma os_init_raw_safe_step : forall p n X,
  (n < 8)%nat -> os_init_raw_safe p n X -> os_init_raw_safe p (S n) X.
Proof.
  intros p n X Hn [first [Hfirst Hsafe]]; subst first.
  unfold os_init_raw_safe; exists (os_init_raw_state p (S n)); split; [reflexivity|].
  assert (Hsub : (8-n = S (8-S n))%nat) by lia.
  rewrite Hsub in Hsafe; cbn [os_init_raw_tail] in Hsafe.
  intros result last Htail; apply (Hsafe result last).
  exists tt, (os_init_raw_state p (S n)); split; [repeat split; reflexivity|exact Htail].
Qed.

Lemma os_init_lift_bind_safe : forall A B (c : program UCOS2_Verify_State A)
  (tail : A -> program OsInitState B) before X,
  safeExec (eq (OsInitKernel before)) (StateRelMonad.bind (os_init_lift c) tail) X ->
  safeExec (eq before) c (fun result state =>
    safeExec (eq (OsInitKernel state)) (tail result) X).
Proof.
  intros A B c tail before X [first [Hfirst Hsafe]]; subst first.
  exists before; split; [reflexivity|]. intros result state Hcall.
  exists (OsInitKernel state); split; [reflexivity|].
  intros output last Htail; apply (Hsafe output last).
  exists result, (OsInitKernel state); split; [|exact Htail].
  exists before, state; repeat split; auto.
Qed.

(** All source address terms use this one C interpretation. The strict
    one-past MemClr bounds are preserved independently of layout facts. *)
Definition os_init_source_binding p : Prop :=
  let sg := os_init_sg p in
  selected_kernel_profile sg /\ init_tcb_list_profile sg /\
  init_tcb_list_global_addresses sg &("OSTCBTbl") &("OSTCBPrioTbl") &("OSTCBList") &("OSTCBFreeList") /\
  init_tcb_list_layout sg /\ init_event_list_profile sg /\ event_table_layout_prop sg /\
  sg.(osMaxEvents) = 10 /\ sg.(g_OSEventTbl) = &("OSEventTbl") /\
  sg.(g_OSEventFreeList) = &("OSEventFreeList") /\
  sizeof_alias_type "os_event" = 20 /\
  0 <= sg.(g_OSEventTbl) /\ sg.(g_OSEventTbl) + 200 <= 4294967295 /\ sg.(g_OSEventTbl) mod 4 = 0 /\
  flag_init_profile sg /\ flag_init_global_addresses sg &("OSFlagTbl") &("OSFlagFreeList") /\
  flag_init_layout sg /\ mem_init_profile sg /\
  mem_init_global_addresses sg &("OSMemTbl") &("OSMemFreeList") /\ mem_init_layout sg /\
  queue_first_round_profile sg /\ os_q_table_addr sg &("OSQTbl") /\
  os_q_free_list_addr sg &("OSQFreeList") /\ queue_table_layout_prop sg &("OSQTbl") /\
  q_init_table_endpoint_in_range sg /\
  sg.(g_OSTime) = &("OSTime") /\ sg.(g_OSIntNesting) = &("OSIntNesting") /\
  sg.(g_OSLockNesting) = &("OSLockNesting") /\ sg.(g_OSTaskCtr) = &("OSTaskCtr") /\
  sg.(g_OSRunning) = &("OSRunning") /\ sg.(g_OSCtxSwCtr) = &("OSCtxSwCtr") /\
  sg.(g_OSIdleCtr) = &("OSIdleCtr") /\ sg.(g_OSIdleCtrRun) = &("OSIdleCtrRun") /\
  sg.(g_OSIdleCtrMax) = &("OSIdleCtrMax") /\ sg.(g_OSStatRdy) = &("OSStatRdy") /\
  sg.(g_OSTaskRegNextAvailID) = &("OSTaskRegNextAvailID") /\
  sg.(g_OSRdyGrp) = &("OSRdyGrp") /\ sg.(g_OSRdyTbl) = &("OSRdyTbl") /\
  sg.(g_OSPrioCur) = &("OSPrioCur") /\ sg.(g_OSPrioHighRdy) = &("OSPrioHighRdy") /\
  sg.(g_OSTCBHighRdy) = &("OSTCBHighRdy") /\ sg.(g_OSTCBCur) = &("OSTCBCur") /\
  tmr_init_source_binding p.(os_init_timer) /\ os_init_literal_layout p /\
  p.(os_init_timer).(tmr_init_missing_literals) = os_init_literal_keys /\
  p.(os_init_call).(os_sched_call_origin) = BootInvocation /\
  p.(os_init_call).(os_sched_call_invocation) = 0%nat /\
  valid_task_stack_region (init_task_idle_stack_region &("OSTaskIdleStk")) /\
  Zlength p.(os_init_idle_lower) = init_task_idle_frame_first &("OSTaskIdleStk") /\
  Zlength p.(os_init_idle_frame) = 16 /\
  Zlength p.(os_init_idle_upper) = 112 - init_task_idle_frame_first &("OSTaskIdleStk") /\
  valid_task_stack_region (init_task_stat_stack_region &("OSTaskStatStk")) /\
  Zlength p.(os_init_stat_lower) = init_task_stat_frame_first &("OSTaskStatStk") /\
  Zlength p.(os_init_stat_frame) = 16 /\
  Zlength p.(os_init_stat_upper) = 112 - init_task_stat_frame_first &("OSTaskStatStk") /\
  valid_task_stack_region (tmr_init_task_stack_region p.(os_init_timer).(tmr_init_stack_base)) /\
  Zlength p.(os_init_timer).(tmr_init_lower) = tmr_init_task_frame_first p.(os_init_timer).(tmr_init_stack_base) /\
  Zlength p.(os_init_timer).(tmr_init_old_frame) = 16 /\
  Zlength p.(os_init_timer).(tmr_init_upper) = 112 - tmr_init_task_frame_first p.(os_init_timer).(tmr_init_stack_base) /\
  0 <= &("OS_TaskIdle") < 4294967296 /\ 0 <= &("OS_TaskStat") < 4294967296 /\
  0 <= &("OS_TaskReturn") < 4294967296 /\
  0 <= p.(os_init_timer).(tmr_init_entry_address) < 4294967296.

Definition os_init_misc_raw sg : Assertion :=
  sg.(g_OSTime) # UInt |->_ ** sg.(g_OSIntNesting) # UChar |->_ **
  sg.(g_OSLockNesting) # UChar |->_ ** sg.(g_OSTaskCtr) # UChar |->_ **
  sg.(g_OSRunning) # UChar |->_ ** sg.(g_OSCtxSwCtr) # UInt |->_ **
  sg.(g_OSIdleCtr) # UInt |->_ ** sg.(g_OSIdleCtrRun) # UInt |->_ **
  sg.(g_OSIdleCtrMax) # UInt |->_ ** sg.(g_OSStatRdy) # UChar |->_ **
  sg.(g_OSTaskRegNextAvailID) # UChar |->_ .
Definition os_init_idle_stack p : Assertion :=
  task_stack_storage (init_task_idle_stack_region &("OSTaskIdleStk"))
    (p.(os_init_idle_lower) ++ p.(os_init_idle_frame) ++ p.(os_init_idle_upper)).
Definition os_init_stat_stack p : Assertion :=
  task_stack_storage (init_task_stat_stack_region &("OSTaskStatStk"))
    (p.(os_init_stat_lower) ++ p.(os_init_stat_frame) ++ p.(os_init_stat_upper)).
Definition os_init_timer_stack p : Assertion :=
  task_stack_storage (tmr_init_task_stack_region p.(os_init_timer).(tmr_init_stack_base))
    (p.(os_init_timer).(tmr_init_lower) ++ p.(os_init_timer).(tmr_init_old_frame) ++ p.(os_init_timer).(tmr_init_upper)).
Definition os_init_loader_frame p : Assertion :=
  (os_init_sg p).(g_OSCPUUsage) # UChar |-> 0 **
  (os_init_sg p).(g_OSTickStepState) # UChar |-> 0 **
  timer_uninitialized_rep (os_init_sg p) ** unmap_table_rep (os_init_sg p) **
  kernel_call_execution_owned (os_init_environment p).(task_stack_call_external)
    (os_init_environment p).(task_stack_call_platform) p.(os_init_call) (os_init_mask p) **
  os_init_idle_stack p ** os_init_stat_stack p ** os_init_timer_stack p.
Definition os_init_component p (index : nat) (initialized : bool) : Assertion :=
  let sg := os_init_sg p in let name := os_init_literals p "?" in
  match index with
  | O => if initialized then os_init_hook_port_post &("OS_CPU_ExceptStk")
      &("OS_CPU_ExceptStkBase") &("OS_CPU_ARM_DRegCnt") emp
    else os_init_hook_port_pre &("OS_CPU_ExceptStk") &("OS_CPU_ExceptStkBase")
      &("OS_CPU_ARM_DRegCnt") p.(os_init_exception_initial) emp
  | S O => if initialized then init_misc_zero sg else os_init_misc_raw sg
  | S (S O) => if initialized then init_rdy_list_post sg.(g_OSRdyGrp) sg.(g_OSRdyTbl)
      sg.(g_OSPrioCur) sg.(g_OSPrioHighRdy) sg.(g_OSTCBHighRdy) sg.(g_OSTCBCur)
    else init_rdy_list_pre sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) sg.(g_OSPrioCur)
      sg.(g_OSPrioHighRdy) sg.(g_OSTCBHighRdy) sg.(g_OSTCBCur)
  | S (S (S O)) => if initialized then init_tcb_list_post sg name else init_tcb_list_pre sg
  | S (S (S (S O))) => if initialized then init_event_list_post sg else init_event_list_pre sg
  | S (S (S (S (S O)))) => if initialized then flag_init_post sg name else flag_init_pre sg
  | S (S (S (S (S (S O))))) => if initialized then mem_init_post sg name else mem_init_pre sg
  | _ => if initialized then OS_QInit_spec sg else queue_init_pre sg
  end.
Definition os_init_components p (completed : nat) : Assertion :=
  fold_right sepcon emp (map (fun i => os_init_component p i (Nat.ltb i completed)) (seq 0 8)).
Definition os_init_component_frame p (completed : nat) : Assertion :=
  fold_right sepcon emp (map (fun i => os_init_component p i (Nat.ltb i completed))
    (filter (fun i => negb (Nat.eqb i completed)) (seq 0 8))).
Definition os_init_raw_stage p n X : Assertion :=
  coq_prop (os_init_source_binding p /\ os_init_raw_safe p n X) &&
  (os_init_components p n ** os_init_loader_frame p ** GlobalStrings (os_init_literals p)).
Definition os_init_raw_call_frame p n X : Assertion :=
  coq_prop (os_init_source_binding p /\ os_init_raw_safe p n X) &&
  (os_init_component_frame p n ** os_init_loader_frame p).
Definition os_init_pre p X : Assertion := os_init_raw_stage p 0 X.


Lemma os_init_names_valid : forall p,
  os_init_literal_layout p -> valid_name_resources (os_init_names p).
Proof.
  intros p [Hstat [Htimer Hquestion]].
  unfold os_init_names; apply task_create_register_default_name_valid.
  - unfold os_init_names_timer, tmr_init_task_register_name.
    apply name_register_source_preserves_resources.
    + unfold os_init_names_stat, init_task_stat_register_name.
      apply name_register_source_preserves_resources.
      * unfold os_init_names_idle, init_task_idle_register_name.
        apply name_register_source_preserves_resources.
        -- apply empty_name_resources_valid.
        -- reflexivity.
        -- apply init_task_idle_name_source_valid.
        -- intros q Hin; reflexivity.
      * reflexivity.
      * apply init_task_stat_name_source_valid.
      * exact Hstat.
    + reflexivity.
    + apply tmr_init_task_name_source_valid.
    + exact Htimer.
  - reflexivity.
  - exact Hquestion.
Qed.

Lemma os_init_names_readable : forall p,
  os_init_literal_layout p ->
  readable_name (os_init_names p) (os_init_literals p "?") [63] /\
  readable_name (os_init_names p) (os_init_literals p "uC/OS-II Idle") init_task_idle_name_chars /\
  readable_name (os_init_names p) (os_init_literals p "uC/OS-II Stat") init_task_stat_name_chars /\
  readable_name (os_init_names p) (os_init_literals p "uC/OS-II Tmr") tmr_init_task_name_chars.
Proof.
  intros p [Hstat [Htimer Hquestion]].
  split.
  - destruct (task_create_register_default_name_lookup (os_init_names_timer p) 3
      (os_init_literals p "?")) as [Hchar Hnul].
    unfold readable_name; split; [repeat constructor; lia|]. split.
    + intros i c Hnth; destruct i as [|i]; cbn in Hnth.
      * inversion Hnth; subst c; rewrite Z.add_0_r; exact Hchar.
      * destruct i; discriminate.
    + exact Hnul.
  - split.
    + unfold os_init_names; apply task_create_register_default_name_preserves_readable; [exact Hquestion|].
      unfold os_init_names_timer; apply tmr_init_task_register_name_preserves_readable; [exact Htimer|].
      unfold os_init_names_stat; apply init_task_stat_register_name_preserves_readable; [exact Hstat|].
      apply init_task_idle_register_name_readable.
    + split.
      * unfold os_init_names; apply task_create_register_default_name_preserves_readable; [exact Hquestion|].
        unfold os_init_names_timer; apply tmr_init_task_register_name_preserves_readable; [exact Htimer|].
        apply init_task_stat_register_name_readable.
      * unfold os_init_names; apply task_create_register_default_name_preserves_readable; [exact Hquestion|].
        apply tmr_init_task_register_name_readable.
Qed.

Lemma os_init_empty_name_storage :
  store_name_bytes empty_name_resources --||-- emp.
Proof.
  unfold store_name_bytes; apply store_map_empty.
  - exists []; split; [intros; split; [contradiction|intros [v H]; discriminate]|constructor].
  - intros q; left; reflexivity.
Qed.

Lemma os_init_register_literals : forall p,
  os_init_literal_layout p ->
  GlobalStrings (os_init_literals p) |--
  store_name_bytes (os_init_names p) ** GlobalStrings_missing (os_init_literals p) os_init_literal_keys.
Proof.
  intros p [Hstat [Htimer Hquestion]].
  sep_apply_l_atomic (GlobalStrings_split (os_init_literals p) "uC/OS-II Idle").
  assert (Hidle : store_stringLit (os_init_literals p "uC/OS-II Idle") "uC/OS-II Idle" |--
    store_name_bytes (os_init_names_idle p)).
  { unfold os_init_names_idle.
    sep_apply_r_atomic (init_task_idle_register_name_storage empty_name_resources 0
      (os_init_literals p "uC/OS-II Idle") ltac:(intros q Hin; reflexivity)).
    rewrite os_init_empty_name_storage; entailer!. }
  sep_apply_l_atomic Hidle.
  sep_apply_l_atomic (GlobalStrings_missing_split (os_init_literals p) ["uC/OS-II Idle"]
    "uC/OS-II Stat" ltac:(cbn; intuition discriminate)).
  sep_apply_l_atomic (init_task_stat_register_name_storage (os_init_names_idle p) 1
    (os_init_literals p "uC/OS-II Stat") Hstat).
  fold (os_init_names_stat p).
  sep_apply_l_atomic (GlobalStrings_missing_split (os_init_literals p) ["uC/OS-II Stat"; "uC/OS-II Idle"]
    "uC/OS-II Tmr" ltac:(cbn; intuition discriminate)).
  sep_apply_l_atomic (tmr_init_task_register_name_storage (os_init_names_stat p) 2
    (os_init_literals p "uC/OS-II Tmr") Htimer).
  fold (os_init_names_timer p).
  sep_apply_l_atomic (GlobalStrings_missing_split (os_init_literals p)
    ["uC/OS-II Tmr"; "uC/OS-II Stat"; "uC/OS-II Idle"] "?" ltac:(cbn; intuition discriminate)).
  sep_apply_l_atomic (task_create_register_default_name_storage (os_init_names_timer p) 3
    (os_init_literals p "?") Hquestion).
  unfold os_init_names, os_init_literal_keys; entailer!.
Qed.

Definition os_init_boot_residual p : Assertion :=
  os_init_component p 0 true ** os_init_stat_stack p ** os_init_timer_stack p.
Definition os_init_idle_entry p call state : Assertion :=
  init_task_idle_entry (os_init_environment p) (os_init_critical p) tmr_init_empty_local (os_init_sg p)
    &("OS_TaskIdle") &("OSTaskIdleStk") &("OS_TaskReturn")
    p.(os_init_idle_lower) p.(os_init_idle_frame) p.(os_init_idle_upper)
    call (os_init_mask p) (os_init_literals p) os_init_literal_keys state.
Definition os_init_stat_entry p call state : Assertion :=
  init_task_stat_entry (os_init_environment p) (os_init_critical p) tmr_init_empty_local (os_init_sg p)
    &("OS_TaskStat") &("OSTaskStatStk") &("OS_TaskReturn")
    p.(os_init_stat_lower) p.(os_init_stat_frame) p.(os_init_stat_upper)
    call (os_init_mask p) (os_init_literals p) os_init_literal_keys state.
Definition os_init_idle_post p call state X : Assertion :=
  init_task_idle_continuation_post (os_init_environment p) (os_init_critical p) tmr_init_empty_local (os_init_sg p)
    &("OS_TaskIdle") &("OSTaskIdleStk") &("OS_TaskReturn")
    p.(os_init_idle_lower) p.(os_init_idle_frame) p.(os_init_idle_upper)
    call (os_init_mask p) (os_init_literals p) os_init_literal_keys state (os_init_idle_continuation p X).
Definition os_init_stat_post p call state X : Assertion :=
  init_task_stat_continuation_post (os_init_environment p) (os_init_critical p) tmr_init_empty_local (os_init_sg p)
    &("OS_TaskStat") &("OSTaskStatStk") &("OS_TaskReturn")
    p.(os_init_stat_lower) p.(os_init_stat_frame) p.(os_init_stat_upper)
    call (os_init_mask p) (os_init_literals p) os_init_literal_keys state (os_init_stat_continuation p X).

(** The current same-call/world facts are consumed at each next call.
    Only the private failed-creation buffer and returned logical evidence
    remain framed; a previous kernel world is never framed beside a new one. *)
Definition os_init_idle_receipt p original initial X returned middle error named current name_error : Assertion :=
  coq_prop (init_task_idle_continuation_created (os_init_environment p) (os_init_critical p) (os_init_sg p)
    &("OS_TaskIdle") &("OSTaskIdleStk") &("OS_TaskReturn")
    p.(os_init_idle_lower) p.(os_init_idle_frame) p.(os_init_idle_upper)
    original (os_init_mask p) (os_init_literals p) initial (os_init_idle_continuation p X) returned middle error) **
  coq_prop (task_name_set_continuation_call_post (os_init_environment p) (os_init_critical p) (os_init_sg p)
    returned (os_init_mask p) 63 (os_init_literals p "uC/OS-II Idle") middle named name_error current
    (init_task_idle_continuation_name_postcondition (os_init_idle_continuation p X))) **
  coq_prop (init_task_idle_continuation_phase_frame initial middle) **
  init_task_idle_continuation_failure_buffer &("OS_TaskIdle") &("OSTaskIdleStk") &("OS_TaskReturn")
    p.(os_init_idle_lower) p.(os_init_idle_frame) p.(os_init_idle_upper) error.
Definition os_init_stat_receipt p original initial X returned middle error named current name_error : Assertion :=
  coq_prop (init_task_stat_continuation_created (os_init_environment p) (os_init_critical p) (os_init_sg p)
    &("OS_TaskStat") &("OSTaskStatStk") &("OS_TaskReturn")
    p.(os_init_stat_lower) p.(os_init_stat_frame) p.(os_init_stat_upper)
    original (os_init_mask p) (os_init_literals p) initial (os_init_stat_continuation p X) returned middle error) **
  coq_prop (task_name_set_continuation_call_post (os_init_environment p) (os_init_critical p) (os_init_sg p)
    returned (os_init_mask p) 62 (os_init_literals p "uC/OS-II Stat") middle named name_error current
    (init_task_stat_continuation_name_postcondition (os_init_stat_continuation p X))) **
  coq_prop (init_task_stat_continuation_phase_frame initial middle) **
  init_task_stat_continuation_failure_buffer &("OS_TaskStat") &("OSTaskStatStk") &("OS_TaskReturn")
    p.(os_init_stat_lower) p.(os_init_stat_frame) p.(os_init_stat_upper) error.


Lemma os_init_raw_safe_idle : forall p X,
  os_init_raw_safe p 8 X ->
  init_task_idle_continuation_safe (os_init_environment p) (os_init_critical p) (os_init_sg p)
    &("OS_TaskIdle") &("OSTaskIdleStk") &("OS_TaskReturn")
    p.(os_init_idle_lower) p.(os_init_idle_frame) p.(os_init_idle_upper)
    p.(os_init_call) (os_init_mask p) (os_init_literals p) (os_init_registered_state p)
    (os_init_idle_continuation p X).
Proof.
  intros p X Hsafe.
  assert (Hkernel : safeExec (eq (OsInitKernel (os_init_registered_state p)))
    (os_init_kernel_program p p.(os_init_call)) X).
  { destruct Hsafe as [first [Hfirst Hsafe]]; subst first.
    exists (OsInitKernel (os_init_registered_state p)); split; [reflexivity|].
    intros result last Htail; apply (Hsafe result last).
    exists tt, (OsInitKernel (os_init_registered_state p)); split; [repeat split; reflexivity|exact Htail]. }
  apply os_init_lift_bind_safe in Hkernel; exact Hkernel.
Qed.

Lemma os_init_initializers_stack_world : forall p,
  os_init_source_binding p ->
  os_init_components p 8 ** os_init_loader_frame p ** GlobalStrings (os_init_literals p) |--
  kernel_stack_call_closed (os_init_environment p).(task_stack_call_continuations)
    kernel_program_inv (os_init_sg p) None p.(os_init_call) (os_init_mask p) (os_init_boot_state p) **
  os_init_component p 0 true ** os_init_idle_stack p ** os_init_stat_stack p ** os_init_timer_stack p **
  GlobalStrings_missing (os_init_literals p) os_init_literal_keys.
Proof.
  intros p Hbinding.
  assert (Hprofile : selected_kernel_profile (os_init_sg p))
    by (unfold os_init_source_binding in Hbinding; tauto).
  assert (Htcb : init_tcb_list_profile (os_init_sg p))
    by (unfold os_init_source_binding in Hbinding; tauto).
  assert (Hliterals : os_init_literal_layout p)
    by (unfold os_init_source_binding in Hbinding; tauto).
  pose proof (os_init_names_valid p Hliterals) as Hnames.
  pose proof (proj1 (os_init_names_readable p Hliterals)) as Hquestion.
  assert (Hmemory : (os_init_sg p).(osKernelConfig).(cfgMemoryEnabled) = true ->
    (os_init_sg p).(osKernelConfig).(cfgMemoryNames) = true ->
    exists chars, readable_name (os_init_names p) (os_init_literals p "?") chars)
    by (intros; exists [63]; exact Hquestion).
  pose proof (kernel_boot_initializer_post_establishes_stack_inv _ _ _
    (os_init_environment p).(task_stack_call_continuations) (os_init_sg p)
    (os_init_literals p "?") (os_init_literals p "?") (os_init_literals p "?")
    (os_init_names p) Hprofile Htcb Hnames Hmemory) as Hassemble.
  unfold kernel_boot_initializer_post in Hassemble.
  sep_apply_l_atomic (os_init_register_literals p Hliterals).
  unfold os_init_components, os_init_loader_frame.
  cbn [seq map Nat.ltb Nat.leb os_init_component iter_sepcon fold_right].
  unfold mem_init_post; Intros.
  sep_apply_l_atomic Hassemble.
  unfold kernel_stack_call_closed, os_init_boot_state, os_init_component; entailer!.
Qed.

Lemma os_init_register_boot_world : forall p,
  os_init_source_binding p ->
  kernel_stack_call_closed (os_init_environment p).(task_stack_call_continuations)
    kernel_program_inv (os_init_sg p) None p.(os_init_call) (os_init_mask p) (os_init_boot_state p) |--
  coq_prop (task_create_source_entry (os_init_sg p)
    (init_task_idle_create_args &("OS_TaskIdle") &("OSTaskIdleStk"))
    (os_init_literals p "?") p.(os_init_call) (os_init_registered_state p)) &&
  kernel_stack_call_closed (os_init_environment p).(task_stack_call_continuations)
    kernel_program_inv (os_init_sg p) None p.(os_init_call) (os_init_mask p) (os_init_registered_state p).
Proof.
  intros p Hbinding.
  assert (Horigin : p.(os_init_call).(os_sched_call_origin) = BootInvocation)
    by (unfold os_init_source_binding in Hbinding; tauto).
  assert (Hinv : p.(os_init_call).(os_sched_call_invocation) = 0%nat)
    by (unfold os_init_source_binding in Hbinding; tauto).
  assert (Hliterals : os_init_literal_layout p)
    by (unfold os_init_source_binding in Hbinding; tauto).
  pose proof (proj1 (os_init_names_readable p Hliterals)) as Hquestion.
  apply task_create_boot_entry_world.
  - exact Horigin.
  - reflexivity.
  - exact Hinv.
  - intros Henabled; exists [63]; exact Hquestion.
Qed.

Lemma os_init_boot_world_continuation : forall p,
  p.(os_init_call).(os_sched_call_origin) = BootInvocation ->
  kernel_stack_call_closed (os_init_environment p).(task_stack_call_continuations)
    kernel_program_inv (os_init_sg p) None p.(os_init_call) (os_init_mask p) (os_init_registered_state p) |--
  task_create_continuation_input (os_init_environment p) (os_init_critical p) tmr_init_empty_local
    (os_init_sg p) p.(os_init_call) (os_init_mask p) (os_init_registered_state p) ** unmap_table_rep (os_init_sg p).
Proof.
  intros p Horigin.
  assert (Hactive : task_stack_call_active_key p.(os_init_call) = None)
    by (unfold task_stack_call_active_key; rewrite Horigin; reflexivity).
  assert (Hstack : armv7a_task_stack_continuations (os_init_environment p).(task_stack_call_continuations)
    (os_init_registered_state p).(TskState) (os_init_registered_state p).(TskState).(parkedTaskStacks) --||-- emp).
  { unfold armv7a_task_stack_continuations, store_parked_continuations.
    apply store_map_empty.
    - exists []; split; [intros; split; [contradiction|intros [v H]; discriminate]|constructor].
    - intros q; left; reflexivity. }
  assert (Hsaved : store_parked_continuations
    (kernel_saved_continuation_entry (os_init_environment p).(task_stack_call_continuations)
      (os_init_registered_state p).(TskState) (task_create_continuation_local tmr_init_empty_local))
    (os_init_registered_state p).(TskState).(parkedTaskStacks) --||-- emp).
  { unfold store_parked_continuations; apply store_map_empty.
    - exists []; split; [intros; split; [contradiction|intros [v H]; discriminate]|constructor].
    - intros q; left; reflexivity. }
  unfold kernel_stack_call_closed, kernel_stack_inv, task_create_continuation_input.
  rewrite Hstack, Hsaved, Hactive, kernel_program_inv_split_unmap.
  unfold UCOS2_inv, critical_region_outside.
  rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
  entailer!.
Qed.

Definition os_init_idle_call_frame p : Assertion :=
  coq_prop (os_init_source_binding p) && os_init_boot_residual p.
Definition os_init_before_idle p X : Assertion :=
  coq_prop (os_init_source_binding p /\
    init_task_idle_continuation_safe (os_init_environment p) (os_init_critical p) (os_init_sg p)
      &("OS_TaskIdle") &("OSTaskIdleStk") &("OS_TaskReturn")
      p.(os_init_idle_lower) p.(os_init_idle_frame) p.(os_init_idle_upper)
      p.(os_init_call) (os_init_mask p) (os_init_literals p) (os_init_registered_state p)
      (os_init_idle_continuation p X) /\
    task_create_runtime_call_input (init_task_idle_create_args &("OS_TaskIdle") &("OSTaskIdleStk"))
      p.(os_init_call) (os_init_registered_state p) /\ init_task_idle_stopped (os_init_registered_state p)) &&
  (os_init_idle_entry p p.(os_init_call) (os_init_registered_state p) ** os_init_idle_call_frame p).

Lemma os_init_raw_stage_to_idle : forall p X,
  os_init_raw_stage p 8 X |-- os_init_before_idle p X.
Proof.
  intros p X; unfold os_init_raw_stage; Intros.
  assert (Hbinding : os_init_source_binding p) by tauto.
  assert (Hsafe : os_init_raw_safe p 8 X) by tauto.
  assert (Horigin : p.(os_init_call).(os_sched_call_origin) = BootInvocation)
    by (unfold os_init_source_binding in Hbinding; tauto).
  assert (Hliterals : os_init_literal_layout p)
    by (unfold os_init_source_binding in Hbinding; tauto).
  pose proof (os_init_names_readable p Hliterals) as Hread.
  pose proof (os_init_raw_safe_idle p X Hsafe) as Hidle_safe.
  assert (Hruntime : task_create_runtime_call_input
    (init_task_idle_create_args &("OS_TaskIdle") &("OSTaskIdleStk"))
    p.(os_init_call) (os_init_registered_state p)).
  { apply task_create_runtime_call_input_boot; reflexivity. }
  sep_apply_l_atomic (os_init_initializers_stack_world p Hbinding).
  sep_apply_l_atomic (os_init_register_boot_world p Hbinding); Intros.
  assert (Hentry : task_create_stack_entry (os_init_sg p)
    (init_task_idle_create_args &("OS_TaskIdle") &("OSTaskIdleStk"))
    (os_init_literals p "?") p.(os_init_call) (os_init_registered_state p))
    by (unfold task_create_source_entry in *; tauto).
  sep_apply_l_atomic (os_init_boot_world_continuation p Horigin).
  unfold os_init_before_idle, os_init_idle_entry, init_task_idle_entry,
    os_init_idle_call_frame, os_init_boot_residual, os_init_idle_stack.
  assert (Hnames : task_create_name_registered (os_init_literals p "?") (os_init_registered_state p)).
  { exists (os_init_names_timer p), 3%nat; reflexivity. }
  assert (Hname_input : task_create_continuation_input (os_init_environment p) (os_init_critical p)
    tmr_init_empty_local (os_init_sg p) p.(os_init_call) (os_init_mask p) (os_init_registered_state p) **
    GlobalStrings_missing (os_init_literals p) os_init_literal_keys |--
    init_task_idle_name_input (os_init_environment p) (os_init_critical p) tmr_init_empty_local (os_init_sg p)
      p.(os_init_call) (os_init_mask p) (os_init_literals p) os_init_literal_keys (os_init_registered_state p)).
  { unfold init_task_idle_name_input; Right; entailer!; tauto. }
  fold (init_task_idle_name_input (os_init_environment p) (os_init_critical p) tmr_init_empty_local (os_init_sg p)
    p.(os_init_call) (os_init_mask p) (os_init_literals p) os_init_literal_keys (os_init_registered_state p)).
  sep_apply_l_atomic Hname_input.
  unfold os_init_source_binding in Hbinding.
  unfold task_create_stack_entry in Hentry.
  unfold init_task_idle_stopped; entailer!; tauto || reflexivity.
Qed.


Record OsInitTaskResult := {
  os_init_created_call : OsSchedCallContext;
  os_init_created_state : UCOS2_Verify_State;
  os_init_create_error : Z;
  os_init_named_call : OsSchedCallContext;
  os_init_named_state : UCOS2_Verify_State;
  os_init_name_error : Z
}.
Definition os_init_continuing p call state : Prop :=
  task_invocation_active state.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
  task_create_stack_no_reservation state call.(os_sched_call_invocation) /\
  state.(TimerState).(timerInitPhase) = TimerUninitialized /\
  state.(NameState) = os_init_names p /\ state.(SchedState).(isRunning) = false.

Definition os_init_idle_result_facts p X r : Prop :=
  safeExec (eq r.(os_init_named_state)) (StateRelMonad.ret r.(os_init_named_call)) (os_init_idle_continuation p X) /\
  task_create_stack_entry (os_init_sg p) (init_task_idle_create_args &("OS_TaskIdle") &("OSTaskIdleStk"))
    (os_init_literals p "?") r.(os_init_named_call) r.(os_init_named_state) /\
  task_tcb_init_stack_same_call r.(os_init_named_call) p.(os_init_call) /\
  (os_init_registered_state p).(TimerState).(timerInitPhase) = r.(os_init_created_state).(TimerState).(timerInitPhase) /\
  r.(os_init_created_state).(TimerState).(timerInitPhase) = r.(os_init_named_state).(TimerState).(timerInitPhase) /\
  (os_init_registered_state p).(NameState) = r.(os_init_named_state).(NameState) /\
  ((os_init_sg p).(osKernelConfig).(cfgTimerEnabled) = true ->
    (os_init_registered_state p).(TimerState).(timerInitPhase) = TimerUninitialized ->
    r.(os_init_named_state).(SchedState).(isRunning) = false) /\
  init_task_idle_continuation_created (os_init_environment p) (os_init_critical p) (os_init_sg p)
    &("OS_TaskIdle") &("OSTaskIdleStk") &("OS_TaskReturn")
    p.(os_init_idle_lower) p.(os_init_idle_frame) p.(os_init_idle_upper)
    p.(os_init_call) (os_init_mask p) (os_init_literals p) (os_init_registered_state p)
    (os_init_idle_continuation p X) r.(os_init_created_call) r.(os_init_created_state) r.(os_init_create_error) /\
  task_name_set_continuation_call_post (os_init_environment p) (os_init_critical p) (os_init_sg p)
    r.(os_init_created_call) (os_init_mask p) 63 (os_init_literals p "uC/OS-II Idle")
    r.(os_init_created_state) r.(os_init_named_call) r.(os_init_name_error) r.(os_init_named_state)
    (init_task_idle_continuation_name_postcondition (os_init_idle_continuation p X)).
Definition os_init_idle_result_receipt p X r : Assertion :=
  os_init_idle_receipt p p.(os_init_call) (os_init_registered_state p) X
    r.(os_init_created_call) r.(os_init_created_state) r.(os_init_create_error)
    r.(os_init_named_call) r.(os_init_named_state) r.(os_init_name_error).
Definition os_init_stat_result_receipt p idle X r : Assertion :=
  os_init_stat_receipt p idle.(os_init_named_call) idle.(os_init_named_state) X
    r.(os_init_created_call) r.(os_init_created_state) r.(os_init_create_error)
    r.(os_init_named_call) r.(os_init_named_state) r.(os_init_name_error).
Definition os_init_closed_result p r : Assertion :=
  task_name_set_continuation_closed (os_init_environment p) (os_init_critical p) tmr_init_empty_local
    (os_init_sg p) r.(os_init_named_call) (os_init_mask p) r.(os_init_named_state) **
  GlobalStrings_missing (os_init_literals p) os_init_literal_keys.
Definition os_init_idle_result p X r : Assertion :=
  coq_prop (os_init_idle_result_facts p X r) &&
  (os_init_closed_result p r ** os_init_idle_result_receipt p X r).
Lemma os_init_idle_post_result : forall p X,
  os_init_idle_post p p.(os_init_call) (os_init_registered_state p) X |--
  EX r, os_init_idle_result p X r.
Proof.
  intros p X; unfold os_init_idle_post, init_task_idle_continuation_post.
  Intros returned middle error named current name_error.
  Exists {| os_init_created_call := returned; os_init_created_state := middle; os_init_create_error := error;
    os_init_named_call := named; os_init_named_state := current; os_init_name_error := name_error |}.
  unfold os_init_idle_result, os_init_idle_result_facts, os_init_closed_result,
    os_init_idle_result_receipt, os_init_idle_receipt; cbn; entailer!; tauto.
Qed.

Lemma os_init_safe_return_value : forall S A (state : S) (value : A) X,
  safeExec (eq state) (StateRelMonad.ret value) X -> X value state.
Proof.
  intros S A state value X [first [Hfirst Hsafe]]; subst first.
  apply Hsafe; split; reflexivity.
Qed.

Lemma os_init_idle_result_continuing : forall p X r,
  os_init_source_binding p -> os_init_idle_result_facts p X r ->
  os_init_continuing p r.(os_init_named_call) r.(os_init_named_state).
Proof.
  intros p X r Hsource Hresult.
  assert (Hconfig : (os_init_sg p).(osKernelConfig) = selected_kernel_configuration)
    by (unfold os_init_source_binding, init_tcb_list_profile in Hsource; tauto).
  assert (Htimer : (os_init_sg p).(osKernelConfig).(cfgTimerEnabled) = true)
    by (rewrite Hconfig; reflexivity).
  unfold os_init_continuing, os_init_idle_result_facts, task_create_stack_entry in *.
  cbn [os_init_registered_state os_init_boot_state UCOS2_boot_state replace_TskS TimerState NameState
    timer_uninitialized timerInitPhase] in Hresult.
  intuition congruence.
Qed.

Definition os_init_stat_call_frame p idle X : Assertion :=
  coq_prop (os_init_source_binding p /\ os_init_idle_result_facts p X idle /\
    os_init_continuing p idle.(os_init_named_call) idle.(os_init_named_state)) &&
  (os_init_component p 0 true ** os_init_timer_stack p ** os_init_idle_result_receipt p X idle).
Definition os_init_before_stat p idle X : Assertion :=
  coq_prop (init_task_stat_continuation_safe (os_init_environment p) (os_init_critical p) (os_init_sg p)
      &("OS_TaskStat") &("OSTaskStatStk") &("OS_TaskReturn")
      p.(os_init_stat_lower) p.(os_init_stat_frame) p.(os_init_stat_upper)
      idle.(os_init_named_call) (os_init_mask p) (os_init_literals p) idle.(os_init_named_state)
      (os_init_stat_continuation p X) /\
    task_create_runtime_call_input (init_task_stat_create_args &("OS_TaskStat") &("OSTaskStatStk"))
      idle.(os_init_named_call) idle.(os_init_named_state) /\ init_task_stat_stopped idle.(os_init_named_state)) &&
  (os_init_stat_entry p idle.(os_init_named_call) idle.(os_init_named_state) ** os_init_stat_call_frame p idle X).

Lemma os_init_idle_result_to_stat : forall p X idle,
  os_init_source_binding p ->
  os_init_idle_result p X idle ** os_init_boot_residual p |-- os_init_before_stat p idle X.
Proof.
  intros p X idle Hsource; unfold os_init_idle_result; Intros.
  assert (Hresult : os_init_idle_result_facts p X idle) by assumption.
  pose proof (os_init_idle_result_continuing p X idle Hsource Hresult) as Hcontinue.
  assert (Hsafe : safeExec (eq (OsInitKernel idle.(os_init_named_state)))
    (os_init_after_idle p idle.(os_init_named_call)) X).
  { exact (os_init_safe_return_value UCOS2_Verify_State OsSchedCallContext
      idle.(os_init_named_state) idle.(os_init_named_call) (os_init_idle_continuation p X) (proj1 Hresult)). }
  apply os_init_lift_bind_safe in Hsafe.
  assert (Hruntime : task_create_runtime_call_input
    (init_task_stat_create_args &("OS_TaskStat") &("OSTaskStatStk"))
    idle.(os_init_named_call) idle.(os_init_named_state)).
  { apply task_create_runtime_call_input_boot; exact (proj2 (proj2 (proj2 (proj2 Hcontinue)))). }
  assert (Hnames : task_create_name_registered (os_init_literals p "?") idle.(os_init_named_state)).
  { exists (os_init_names_timer p), 3%nat; exact (proj1 (proj2 (proj2 (proj2 Hcontinue)))). }
  assert (Hread : readable_name idle.(os_init_named_state).(NameState)
    (os_init_literals p "uC/OS-II Stat") init_task_stat_name_chars).
  { rewrite (proj1 (proj2 (proj2 (proj2 Hcontinue))));
    apply (proj1 (proj2 (proj2 (os_init_names_readable p ltac:(unfold os_init_source_binding in Hsource; tauto))))). }
  unfold os_init_closed_result, task_name_set_continuation_closed, os_init_boot_residual,
    os_init_before_stat, os_init_stat_entry, init_task_stat_entry, os_init_stat_call_frame, os_init_stat_stack.
  assert (Hname_input : task_create_continuation_input (os_init_environment p) (os_init_critical p)
    tmr_init_empty_local (os_init_sg p) idle.(os_init_named_call) (os_init_mask p) idle.(os_init_named_state) **
    GlobalStrings_missing (os_init_literals p) os_init_literal_keys |--
    init_task_stat_name_input (os_init_environment p) (os_init_critical p) tmr_init_empty_local (os_init_sg p)
      idle.(os_init_named_call) (os_init_mask p) (os_init_literals p) os_init_literal_keys idle.(os_init_named_state)).
  { unfold init_task_stat_name_input; Right; entailer!. }
  sep_apply_l_atomic Hname_input.
  unfold os_init_source_binding in Hsource; unfold os_init_continuing in Hcontinue.
  unfold init_task_stat_stopped; entailer!; tauto.
Qed.

Definition os_init_stat_result_facts p idle X r : Prop :=
  safeExec (eq r.(os_init_named_state)) (StateRelMonad.ret r.(os_init_named_call)) (os_init_stat_continuation p X) /\
  task_create_stack_entry (os_init_sg p) (init_task_stat_create_args &("OS_TaskStat") &("OSTaskStatStk"))
    (os_init_literals p "?") r.(os_init_named_call) r.(os_init_named_state) /\
  task_tcb_init_stack_same_call r.(os_init_named_call) idle.(os_init_named_call) /\
  idle.(os_init_named_state).(TimerState).(timerInitPhase) = r.(os_init_created_state).(TimerState).(timerInitPhase) /\
  r.(os_init_created_state).(TimerState).(timerInitPhase) = r.(os_init_named_state).(TimerState).(timerInitPhase) /\
  idle.(os_init_named_state).(NameState) = r.(os_init_named_state).(NameState) /\
  ((os_init_sg p).(osKernelConfig).(cfgTimerEnabled) = true ->
    idle.(os_init_named_state).(TimerState).(timerInitPhase) = TimerUninitialized ->
    r.(os_init_named_state).(SchedState).(isRunning) = false) /\
  init_task_stat_continuation_created (os_init_environment p) (os_init_critical p) (os_init_sg p)
    &("OS_TaskStat") &("OSTaskStatStk") &("OS_TaskReturn")
    p.(os_init_stat_lower) p.(os_init_stat_frame) p.(os_init_stat_upper)
    idle.(os_init_named_call) (os_init_mask p) (os_init_literals p) idle.(os_init_named_state)
    (os_init_stat_continuation p X) r.(os_init_created_call) r.(os_init_created_state) r.(os_init_create_error) /\
  task_name_set_continuation_call_post (os_init_environment p) (os_init_critical p) (os_init_sg p)
    r.(os_init_created_call) (os_init_mask p) 62 (os_init_literals p "uC/OS-II Stat")
    r.(os_init_created_state) r.(os_init_named_call) r.(os_init_name_error) r.(os_init_named_state)
    (init_task_stat_continuation_name_postcondition (os_init_stat_continuation p X)).

Definition os_init_stat_result p idle X r : Assertion :=
  coq_prop (os_init_stat_result_facts p idle X r) &&
  (os_init_closed_result p r ** os_init_stat_result_receipt p idle X r).
Lemma os_init_stat_post_result : forall p idle X,
  os_init_stat_post p idle.(os_init_named_call) idle.(os_init_named_state) X |--
  EX r, os_init_stat_result p idle X r.
Proof.
  intros p idle X; unfold os_init_stat_post, init_task_stat_continuation_post.
  Intros returned middle error named current name_error.
  Exists {| os_init_created_call := returned; os_init_created_state := middle; os_init_create_error := error;
    os_init_named_call := named; os_init_named_state := current; os_init_name_error := name_error |}.
  unfold os_init_stat_result, os_init_stat_result_facts, os_init_closed_result,
    os_init_stat_result_receipt, os_init_stat_receipt; cbn; entailer!; tauto.
Qed.
Definition os_init_timer_call_frame p idle stat X : Assertion :=
  coq_prop (os_init_source_binding p /\ os_init_idle_result_facts p X idle /\
    os_init_stat_result_facts p idle X stat) &&
  (os_init_component p 0 true ** os_init_idle_result_receipt p X idle ** os_init_stat_result_receipt p idle X stat).
Definition os_init_before_timer p idle stat X : Assertion :=
  tmr_init_pre p.(os_init_timer) stat.(os_init_named_call) stat.(os_init_named_state)
    (os_init_timer_continuation X) ** os_init_timer_call_frame p idle stat X.

Lemma os_init_stat_result_continuing : forall p idle X r,
  os_init_source_binding p -> os_init_continuing p idle.(os_init_named_call) idle.(os_init_named_state) ->
  os_init_stat_result_facts p idle X r ->
  os_init_continuing p r.(os_init_named_call) r.(os_init_named_state).
Proof.
  intros p idle X r Hsource Hbefore Hresult.
  assert (Hconfig : (os_init_sg p).(osKernelConfig) = selected_kernel_configuration)
    by (unfold os_init_source_binding, init_tcb_list_profile in Hsource; tauto).
  assert (Htimer : (os_init_sg p).(osKernelConfig).(cfgTimerEnabled) = true)
    by (rewrite Hconfig; reflexivity).
  unfold os_init_continuing, os_init_stat_result_facts, task_create_stack_entry in *.
  intuition congruence.
Qed.

Lemma os_init_stat_result_to_timer : forall p idle X stat,
  os_init_stat_result p idle X stat ** os_init_stat_call_frame p idle X |--
  os_init_before_timer p idle stat X.
Proof.
  intros p idle X stat; unfold os_init_stat_result, os_init_stat_call_frame; Intros.
  assert (Hsource : os_init_source_binding p) by tauto.
  assert (Hidle : os_init_idle_result_facts p X idle) by tauto.
  assert (Hstat : os_init_stat_result_facts p idle X stat) by tauto.
  assert (Hbefore : os_init_continuing p idle.(os_init_named_call) idle.(os_init_named_state)) by tauto.
  pose proof (os_init_stat_result_continuing p idle X stat Hsource Hbefore Hstat) as Hcontinue.
  assert (Hsafe : safeExec (eq (OsInitKernel stat.(os_init_named_state)))
    (os_init_timer_program p stat.(os_init_named_call)) X).
  { exact (os_init_safe_return_value UCOS2_Verify_State OsSchedCallContext
      stat.(os_init_named_state) stat.(os_init_named_call) (os_init_stat_continuation p X) (proj1 Hstat)). }
  apply os_init_lift_bind_safe in Hsafe.
  assert (Hnames : task_create_name_registered (os_init_literals p "?") stat.(os_init_named_state)).
  { exists (os_init_names_timer p), 3%nat; exact (proj1 (proj2 (proj2 (proj2 Hcontinue)))). }
  assert (Hread : readable_name stat.(os_init_named_state).(NameState)
    (os_init_literals p "uC/OS-II Tmr") tmr_init_task_name_chars).
  { rewrite (proj1 (proj2 (proj2 (proj2 Hcontinue))));
    apply (proj2 (proj2 (proj2 (os_init_names_readable p ltac:(unfold os_init_source_binding in Hsource; tauto))))). }
  assert (Hlits : p.(os_init_timer).(tmr_init_missing_literals) = os_init_literal_keys)
    by (unfold os_init_source_binding in Hsource; tauto).
  assert (Hreturn : 0 <= p.(os_init_timer).(tmr_init_return_address) < 4294967296).
  { assert (Hbinding : tmr_init_source_binding p.(os_init_timer))
      by (unfold os_init_source_binding in Hsource; tauto).
    assert (Heq : p.(os_init_timer).(tmr_init_return_address) = &("OS_TaskReturn"))
      by (unfold tmr_init_source_binding in Hbinding; tauto).
    rewrite Heq; unfold os_init_source_binding in Hsource; tauto. }
  unfold os_init_closed_result, task_name_set_continuation_closed,
    os_init_before_timer, tmr_init_pre, tmr_init_entry_resources, tmr_init_task_entry,
    os_init_timer_call_frame, os_init_timer_stack.
  rewrite Hlits.
  assert (Hname_input : task_create_continuation_input (os_init_environment p) (os_init_critical p)
    tmr_init_empty_local (os_init_sg p) stat.(os_init_named_call) (os_init_mask p) stat.(os_init_named_state) **
    GlobalStrings_missing (os_init_literals p) os_init_literal_keys |--
    tmr_init_task_name_input (os_init_environment p) (os_init_critical p) tmr_init_empty_local (os_init_sg p)
      stat.(os_init_named_call) (os_init_mask p) (os_init_literals p) os_init_literal_keys stat.(os_init_named_state)).
  { unfold tmr_init_task_name_input; Right; entailer!. }
  sep_apply_l_atomic Hname_input.
  unfold os_init_source_binding in Hsource; unfold os_init_continuing in Hcontinue.
  unfold tmr_init_task_stopped; entailer!; tauto.
Qed.


Record OsInitTimerResult := {
  os_init_timer_call : OsSchedCallContext;
  os_init_timer_before : UCOS2_Verify_State;
  os_init_timer_returned : OsSchedCallContext;
  os_init_timer_middle : UCOS2_Verify_State;
  os_init_timer_create_error : Z;
  os_init_timer_receipt : option (TaskID * nat);
  os_init_timer_current : UCOS2_Verify_State;
  os_init_timer_name_error : Z;
  os_init_timer_state : GlobTimerState
}.
Definition os_init_final_state t := replace_TimerS t.(os_init_timer_state) t.(os_init_timer_current).
Definition os_init_after_end : program OsInitState unit :=
  StateRelMonad.bind (StateRelMonad.ret tt) (fun _ => StateRelMonad.ret tt).
Definition os_init_timer_result_facts p original t X : Prop :=
  let ctx := p.(os_init_timer) in
  task_tcb_init_stack_same_call t.(os_init_timer_call) original /\
  task_tcb_init_stack_same_call t.(os_init_timer_returned) t.(os_init_timer_call) /\
  tmr_init_task_source_receipt ctx.(tmr_init_environment) ctx.(tmr_init_critical) ctx.(tmr_init_sg)
    ctx.(tmr_init_entry_address) ctx.(tmr_init_stack_base) ctx.(tmr_init_return_address)
    ctx.(tmr_init_lower) ctx.(tmr_init_old_frame) ctx.(tmr_init_upper) t.(os_init_timer_call)
    ctx.(tmr_init_mask) ctx.(tmr_init_literals) t.(os_init_timer_before) t.(os_init_timer_create_error)
    t.(os_init_timer_middle) t.(os_init_timer_receipt) /\
  task_name_set_program ctx.(tmr_init_critical) ctx.(tmr_init_sg)
    t.(os_init_timer_call).(os_sched_call_invocation) 61 (ctx.(tmr_init_literals) "uC/OS-II Tmr")
    t.(os_init_timer_middle) t.(os_init_timer_name_error) t.(os_init_timer_current) /\
  timer_finish_initialization t.(os_init_timer_current).(TimerState) t.(os_init_timer_receipt)
    = Some t.(os_init_timer_state) /\
  t.(os_init_timer_state).(timerInitPhase) = TimerInitializationFinished /\
  UCOS2_state_inv ctx.(tmr_init_sg) (os_init_final_state t) /\
  safeExec (eq (os_init_final_state t)) (StateRelMonad.ret tt) (os_init_timer_continuation X).
Definition os_init_timer_result_resources p t X : Assertion :=
  let ctx := p.(os_init_timer) in
  coq_prop (tmr_init_task_phase_created ctx.(tmr_init_environment) ctx.(tmr_init_critical) ctx.(tmr_init_sg)
    ctx.(tmr_init_entry_address) ctx.(tmr_init_stack_base) ctx.(tmr_init_return_address)
    ctx.(tmr_init_lower) ctx.(tmr_init_old_frame) ctx.(tmr_init_upper) t.(os_init_timer_call)
    ctx.(tmr_init_mask) ctx.(tmr_init_literals) t.(os_init_timer_before)
    (tmr_init_task_continuation ctx t.(os_init_timer_call) t.(os_init_timer_before) (os_init_timer_continuation X))
    t.(os_init_timer_returned) t.(os_init_timer_middle) t.(os_init_timer_create_error) t.(os_init_timer_receipt)) **
  coq_prop (task_name_set_post ctx.(tmr_init_critical) ctx.(tmr_init_sg)
    t.(os_init_timer_returned).(os_sched_call_invocation) 61 (ctx.(tmr_init_literals) "uC/OS-II Tmr")
    t.(os_init_timer_middle) t.(os_init_timer_name_error) t.(os_init_timer_current)
    (tmr_init_task_name_continuation (tmr_init_task_continuation ctx t.(os_init_timer_call)
      t.(os_init_timer_before) (os_init_timer_continuation X)))) **
  task_name_set_closed ctx.(tmr_init_environment).(task_stack_call_platform) ctx.(tmr_init_critical) ctx.(tmr_init_sg)
    t.(os_init_timer_returned).(os_sched_call_invocation) t.(os_init_timer_returned).(os_sched_call_origin)
    ctx.(tmr_init_mask) (os_init_final_state t) **
  tmr_init_task_create_residual ctx.(tmr_init_environment) tmr_init_empty_local ctx.(tmr_init_sg)
    ctx.(tmr_init_entry_address) ctx.(tmr_init_stack_base) ctx.(tmr_init_return_address)
    ctx.(tmr_init_lower) ctx.(tmr_init_old_frame) ctx.(tmr_init_upper)
    t.(os_init_timer_returned) t.(os_init_timer_middle) t.(os_init_timer_create_error) **
  GlobalStrings_missing ctx.(tmr_init_literals) ctx.(tmr_init_missing_literals).
Definition os_init_timer_result p original t X : Assertion :=
  coq_prop (os_init_timer_result_facts p original t X) && os_init_timer_result_resources p t X.
Lemma os_init_timer_post_result : forall p original X,
  tmr_init_post p.(os_init_timer) original (os_init_timer_continuation X) |--
  EX t, os_init_timer_result p original t X.
Proof.
  intros p original X; unfold tmr_init_post.
  Intros call before returned middle error receipt current name_error timers.
  Exists {| os_init_timer_call := call; os_init_timer_before := before; os_init_timer_returned := returned;
    os_init_timer_middle := middle; os_init_timer_create_error := error; os_init_timer_receipt := receipt;
    os_init_timer_current := current; os_init_timer_name_error := name_error; os_init_timer_state := timers |}.
  unfold os_init_timer_result, os_init_timer_result_facts, os_init_timer_result_resources,
    os_init_final_state; cbn; entailer!; tauto.
Qed.

Definition os_init_tail_stage p idle stat t X (tail : program OsInitState unit) : Assertion :=
  coq_prop (os_init_timer_result_facts p stat.(os_init_named_call) t X /\
    safeExec (eq (OsInitKernel (os_init_final_state t))) tail X) &&
  (os_init_timer_result_resources p t X ** os_init_timer_call_frame p idle stat X).
Definition os_init_after_timer_stage p idle stat t X : Assertion :=
  os_init_tail_stage p idle stat t X os_init_after_timer.
Definition os_init_after_end_stage p idle stat t X : Assertion :=
  os_init_tail_stage p idle stat t X os_init_after_end.
Definition os_init_return_stage p idle stat t X : Assertion :=
  os_init_tail_stage p idle stat t X (StateRelMonad.ret tt).
Definition os_init_post p (X : unit -> OsInitState -> Prop) : Assertion :=
  EX idle stat timer, os_init_return_stage p idle stat timer X.

Lemma os_init_timer_result_tail : forall p idle stat t X,
  os_init_timer_result p stat.(os_init_named_call) t X ** os_init_timer_call_frame p idle stat X |--
  os_init_after_timer_stage p idle stat t X.
Proof.
  intros p idle stat t X; unfold os_init_timer_result; Intros.
  assert (Hfacts : os_init_timer_result_facts p stat.(os_init_named_call) t X) by assumption.
  assert (Hsafe : safeExec (eq (os_init_final_state t)) (StateRelMonad.ret tt) (os_init_timer_continuation X))
    by (unfold os_init_timer_result_facts in Hfacts; tauto).
  apply os_init_safe_return_value in Hsafe.
  unfold os_init_after_timer_stage, os_init_tail_stage; entailer!.
Qed.
Lemma os_init_ret_safe_step : forall S A B (value : A) (state : S)
  (tail : A -> program S B) X,
  safeExec (eq state) (StateRelMonad.bind (StateRelMonad.ret value) tail) X ->
  safeExec (eq state) (tail value) X.
Proof.
  intros S A B value state tail X [first [Hfirst Hsafe]]; subst first.
  exists state; split; [reflexivity|]. intros result last Htail.
  apply (Hsafe result last); exists value, state; split; [split; reflexivity|exact Htail].
Qed.
Lemma os_init_end_safe_step : forall p idle stat t X,
  os_init_after_timer_stage p idle stat t X |-- os_init_after_end_stage p idle stat t X.
Proof.
  intros p idle stat t X; unfold os_init_after_timer_stage, os_init_after_end_stage, os_init_tail_stage; Intros.
  assert (Hsafe : safeExec (eq (OsInitKernel (os_init_final_state t))) os_init_after_timer X) by tauto.
  apply os_init_ret_safe_step in Hsafe; entailer!.
Qed.
Lemma os_init_debug_safe_step : forall p idle stat t X,
  os_init_after_end_stage p idle stat t X |-- os_init_return_stage p idle stat t X.
Proof.
  intros p idle stat t X; unfold os_init_after_end_stage, os_init_return_stage, os_init_tail_stage; Intros.
  assert (Hsafe : safeExec (eq (OsInitKernel (os_init_final_state t))) os_init_after_end X) by tauto.
  apply os_init_ret_safe_step in Hsafe; entailer!.
Qed.

Lemma os_init_idle_post_next : forall p X,
  os_init_idle_post p p.(os_init_call) (os_init_registered_state p) X ** os_init_idle_call_frame p |--
  EX idle, os_init_before_stat p idle X.
Proof.
  intros p X; unfold os_init_idle_call_frame; Intros.
  assert (Hsource : os_init_source_binding p) by assumption.
  sep_apply_l_atomic (os_init_idle_post_result p X); Intros idle.
  Exists idle; apply os_init_idle_result_to_stat; exact Hsource.
Qed.
Lemma os_init_stat_post_next : forall p idle X,
  os_init_stat_post p idle.(os_init_named_call) idle.(os_init_named_state) X ** os_init_stat_call_frame p idle X |--
  EX stat, os_init_before_timer p idle stat X.
Proof.
  intros p idle X; sep_apply_l_atomic (os_init_stat_post_result p idle X); Intros stat.
  Exists stat; apply os_init_stat_result_to_timer.
Qed.
Lemma os_init_timer_post_next : forall p idle stat X,
  tmr_init_post p.(os_init_timer) stat.(os_init_named_call) (os_init_timer_continuation X) **
    os_init_timer_call_frame p idle stat X |-- EX timer, os_init_after_timer_stage p idle stat timer X.
Proof.
  intros p idle stat X; sep_apply_l_atomic (os_init_timer_post_result p stat.(os_init_named_call) X); Intros timer.
  Exists timer; apply os_init_timer_result_tail.
Qed.
