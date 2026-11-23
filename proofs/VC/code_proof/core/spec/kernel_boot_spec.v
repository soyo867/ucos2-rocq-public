Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.flag Ucos2Verify.lib.memory Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.statistics Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.core.spec.init_misc_spec.
Require Import Ucos2Verify.VC.code.sched.spec.init_rdy_list_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Require Import Ucos2Verify.VC.code.event.spec.init_event_list_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_init_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_init_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The ECB initializer owns no published objects. Its exact free images
    and root suffice for any Task index; no existing global invariant or
    Queue heap is an initializer premise. *)
Lemma init_event_list_post_to_event_raw_rep : forall sg tasks,
  init_event_list_post sg |-- event_raw_rep sg tasks (event_pool_initial sg).
Proof.
  intros sg tasks.
  assert (Hempty : store_map (used_event_rep sg tasks) (fun _ => None) --||-- emp).
  { apply store_map_empty.
    - exists []; split; [intros; split; [contradiction|intros [e He]; discriminate]|constructor].
    - intro eid; left; reflexivity. }
  unfold init_event_list_post, event_raw_rep.
  change (coq_prop (event_pool_partition sg (event_pool_initial sg) /\
    event_free_storage_valid sg (event_pool_initial sg) /\
    event_identity_valid (event_pool_initial sg)) &&
    (event_free_storage_rep sg (event_pool_initial sg) ** event_free_root_rep sg (event_pool_initial sg)) |--
    store_map (used_event_rep sg tasks) (fun _ => None) **
    event_free_storage_rep sg (event_pool_initial sg) ** event_free_root_rep sg (event_pool_initial sg)).
  rewrite Hempty; entailer!.
Qed.

Lemma task_boot_shared_rep_equiv : forall sg name,
  task_shared_rep sg (task_boot sg name) --||-- task_public_storage sg (task_boot sg name).
Proof.
  intros sg name; unfold task_shared_rep.
  change (task_public_storage sg (task_boot sg name) ** store_parked_stacks (fun _ => None)
    --||-- task_public_storage sg (task_boot sg name)).
  unfold store_parked_stacks.
  rewrite store_map_empty.
  - split; entailer!.
  - exists []; split; [intros; split; [contradiction|intros [e He]; discriminate]|constructor].
  - intro key; left; reflexivity.
Qed.

(** OSInit checkpoint after Misc/Rdy/TCB/Event/Flag/Memory/Queue and before
    Idle/Stat/Timer task creation. The first six posts are the actual
    existing initializer interfaces. Memory's selected cleared-and-linked
    image is supplied separately; no C proof of OS_MemInit is claimed.

    OSCPUUsage and OSTickStepState are not written by OS_InitMisc: their
    zero cells, the as-yet-uninitialized Timer storage and actual name
    bytes must come from startup/BSS or an explicit earlier resource
    contract. The hook cannot be silently assumed to preserve them.
    Distinct name pointers do not assume compiler string-literal pooling. *)
Definition kernel_boot_initializer_post (sg : StableGlobVars)
  (task_name flag_name memory_name : addr) (names : NameResourceState) : Assertion :=
  init_misc_zero sg **
  init_rdy_list_post sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) sg.(g_OSPrioCur)
    sg.(g_OSPrioHighRdy) sg.(g_OSTCBHighRdy) sg.(g_OSTCBCur) **
  init_tcb_list_post sg task_name ** init_event_list_post sg **
  flag_init_post sg flag_name ** OS_QInit_spec sg **
  memory_raw_rep sg (memory_initial sg memory_name) **
  sg.(g_OSCPUUsage) # UChar |-> 0 ** sg.(g_OSTickStepState) # UChar |-> 0 **
  timer_uninitialized_rep sg ** store_name_bytes names.

(** Assemble real, disjoint initializer results. Boot pure validity is
    derived from the existing initializer construction, not required as an
    input; Task/ready scalar cells are consumed once, and empty parked
    stacks add no heap. This is not a proof of OSInit's calls or of the
    later ignored system-task/Timer creation return values. *)
Lemma kernel_boot_initializer_post_establishes_global_inv :
  forall sg task_name flag_name memory_name names,
  selected_kernel_profile sg -> init_tcb_list_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
   sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  kernel_boot_initializer_post sg task_name flag_name memory_name names |--
  UCOS2_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof.
  intros sg task_name flag_name memory_name names Hprofile Htcb Hnames Hmemoryname.
  pose proof (proj2 (proj2 (proj2 Htcb))) as Hconfig.
  pose proof (flag_init_profile_of_supported_configuration sg
    (or_introl Hconfig)) as Hflagprofile.
  pose proof (UCOS2_boot_validity sg task_name flag_name memory_name names
    Hprofile Hnames Hmemoryname) as Hboot.
  unfold kernel_boot_initializer_post, init_misc_zero.
  sepcon_right_assoc.
  sep_apply_l_atomic (init_tcb_list_post_to_task_boot sg task_name Htcb).
  sep_apply_l_atomic (init_rdy_list_post_implies_sched_boot_rep sg (task_boot sg task_name)).
  sep_apply_l_atomic (init_event_list_post_to_event_raw_rep sg (task_boot sg task_name)).
  sep_apply_l_atomic (q_init_spec_establishes_queue_storage sg).
  sep_apply_l_atomic (flag_init_post_to_flag_raw_rep sg flag_name Hflagprofile).
  unfold UCOS2_inv.
  eapply derivable1_trans with (y := UCOS2_raw_rep sg
    (UCOS2_boot_state sg task_name flag_name memory_name names)); [|entailer!].
  unfold UCOS2_raw_rep, UCOS2_boot_state.
  cbn [TskState SchedState IntrState EventState TickState FlagState MemoryState TimerState
    StatsState ControlState NameState].
  rewrite task_boot_shared_rep_equiv.
  unfold initial_event_abstract_state, interrupt_inv, interrupt_in_range, store_int_state,
    tick_inv, store_tick_state, flag_configured_rep, memory_configured_rep, timer_configured_rep,
    statistics_rep, kernel_control_rep, kernel_control_initial.
  rewrite Hconfig.
  cbn [cfgFlagEnabled cfgMemoryEnabled cfgTimerEnabled cfgStatisticsEnabled cfgSafetyCriticalIEC
    selected_kernel_configuration timerInitPhase timer_uninitialized statistics_initial
    idleCtr idleCtrMax idleCtrRun cpuUsage statReady safetyCriticalStarted
    intNesting lockNesting ostime tickStepState].
  entailer!.
Qed.
