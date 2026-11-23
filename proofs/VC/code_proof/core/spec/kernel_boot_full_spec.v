Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event_registration.
Require Import Ucos2Verify.lib.flag Ucos2Verify.lib.memory Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.statistics Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.core.spec.init_misc_spec.
Require Import Ucos2Verify.VC.code.sched.spec.init_rdy_list_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_full_spec.
Require Import Ucos2Verify.VC.code.event.spec.init_event_list_names_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_init_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_init_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The same pre-system-task checkpoint as the selected-profile boot, with
    the actual named ECB image and configured 92-byte TCB pool. This is an
    initial state value, not a new state record or a C OSInit theorem. *)
Definition kernel_full_boot_state (sg : StableGlobVars)
  (task_name event_name flag_name memory_name : addr)
  (names : NameResourceState) : UCOS2_Verify_State :=
  {| IntrState := {| intNesting := 0; lockNesting := 0 |};
     TskState := task_boot sg task_name; SchedState := sched_boot;
     EventState := event_pool_initial_named sg event_name;
     TickState := {| ostime := 0; tickStepState := 0 |};
     FlagState := if sg.(osKernelConfig).(cfgFlagEnabled)
       then flag_initial sg flag_name else flag_disabled;
     MemoryState := if sg.(osKernelConfig).(cfgMemoryEnabled)
       then memory_initial sg memory_name else memory_disabled;
     TimerState := timer_uninitialized; StatsState := statistics_initial;
     ControlState := kernel_control_initial sg.(osKernelConfig); NameState := names |}.

(** InitMisc, not InitTCBList, supplies TaskCtr and TaskRegNextAvailID. *)
Lemma init_tcb_list_full_post_to_task_boot : forall sg name,
  init_tcb_list_full_profile sg ->
  init_tcb_list_full_post sg name **
    sg.(g_OSTaskCtr) # UChar |-> 0 **
    sg.(g_OSTaskRegNextAvailID) # UChar |-> 0 |--
  task_public_storage sg (task_boot sg name).
Proof.
  intros sg name [Happ [Hsys [_ Hconfig]]].
  unfold init_tcb_list_full_post, task_public_storage, task_reg_allocator_rep, task_boot.
  cbn [inUsedTaskStates unUsedTaskStates tcbListHead taskCount prioTbl
    taskLifecycle taskFreeStorage taskRegNextID].
  rewrite Happ, Hsys, Hconfig.
  change (20 + 2) with 22.
  change (Z.ltb 0 (cfgTaskRegisters full_features_kernel_configuration)) with true.
  change (hd_error (Zrange 0 22)) with (Some 0).
  unfold encode_task_link, task_slot_addr, tcb_configured_size, tcb_layout_size.
  rewrite Hconfig; cbn [cfgEventMultiEnabled cfgTaskProfile].
  replace (g_OSTCBTbl sg + 0 * 92) with (g_OSTCBTbl sg) by lia.
  unfold store_used_task_map.
  rewrite store_map_empty.
  - entailer!; rewrite Z.mul_0_l, Z.add_0_r; reflexivity.
  - exists []; split; [intro tid; split; [contradiction|intros [t H]; discriminate]|constructor].
  - intro tid; left; reflexivity.
Qed.

Lemma init_event_list_named_post_to_event_raw_rep : forall sg tasks name,
  init_event_list_named_post sg name |--
  event_raw_rep sg tasks (event_pool_initial_named sg name).
Proof.
  intros sg tasks name.
  assert (Hempty : store_map (used_event_rep sg tasks) (fun _ => None) --||-- emp).
  { apply store_map_empty.
    - exists []; split; [intros; split; [contradiction|intros [e He]; discriminate]|constructor].
    - intro eid; left; reflexivity. }
  unfold init_event_list_named_post, event_raw_rep.
  cbn [event_pool_initial_named inUsedEventStates].
  rewrite Hempty; entailer!.
Qed.

Lemma kernel_full_boot_cross_module_consistency :
  forall sg task_name event_name flag_name memory_name names,
  cross_module_registration_consistency sg
    (kernel_full_boot_state sg task_name event_name flag_name memory_name names).
Proof.
  intros sg task_name event_name flag_name memory_name names; split.
  - split; [intros p entry H; discriminate|]. split.
    + intros p Hrange [mid [e [m [H _]]]]; discriminate.
    + intros tid t H; discriminate.
  - split; [intros mid e m owner H; discriminate|]. split.
    + unfold event_registration_consistency,
        event_registered_backlinks, event_registered_reference_closure.
      repeat split; intros; discriminate.
    + split; [intros mid e m H; discriminate|]. split.
      * intros mid1 mid2 e1 e2 m1 m2 H; discriminate.
      * split.
        -- apply task_flag_waiter_consistency_empty.
           ++ intro p; simpl; destruct (cfgFlagEnabled (osKernelConfig sg)); reflexivity.
           ++ intros tid t H; discriminate.
        -- intros Henabled Hrunning; discriminate.
Qed.

Lemma kernel_full_boot_state_valid :
  forall sg task_name event_name flag_name memory_name names,
  full_features_kernel_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
   sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  UCOS2_full_state_inv sg
    (kernel_full_boot_state sg task_name event_name flag_name memory_name names).
Proof.
  intros sg task_name event_name flag_name memory_name names Hprofile Hnames Hmemoryname.
  pose proof Hprofile as [_ [_ [_ [Hconfig _]]]].
  assert (HflagEnabled : cfgFlagEnabled (osKernelConfig sg) = true)
    by (rewrite Hconfig; reflexivity).
  assert (HflagBits : cfgFlagBits (osKernelConfig sg) = 16)
    by (rewrite Hconfig; reflexivity).
  assert (Hregs : cfgTaskRegisters (osKernelConfig sg) = 1)
    by (rewrite Hconfig; reflexivity).
  split; [exact Hprofile|]. split; [apply task_boot_in_range; lia|].
  assert (Hmetadata : sched_metadata_in_range sg sched_boot).
  { exact (proj2 (sched_boot_in_range sg (task_boot sg task_name) (fun _ => eq_refl))). }
  split; [split; [apply sched_registered_ready_boot|exact Hmetadata]|]. split.
  - split; [apply event_pool_initial_named_partition|].
    split; [apply event_pool_initial_named_free_storage|].
    split; [apply event_pool_initial_named_identity_valid|].
    split; [intros; discriminate|]. split; [intros; discriminate|].
    split; intros; discriminate.
  - split; [apply kernel_full_boot_cross_module_consistency|].
    split; [discriminate|]. split; [apply task_boot_reserved_bits_clear|]. split.
    + unfold valid_flag_configuration; simpl; rewrite HflagEnabled.
      apply flag_initial_valid.
      * lia.
      * unfold flag_group_name_offset, flag_word_bytes, kernel_align4.
        rewrite HflagBits; simpl; lia.
    + split.
      * unfold valid_memory_configuration; simpl; destruct (cfgMemoryEnabled (osKernelConfig sg));
          [apply memory_initial_valid|reflexivity].
      * split; [apply timer_uninitialized_configuration_valid|].
        split; [apply statistics_initial_configuration_valid|].
        split; [apply kernel_control_initial_valid|]. split; [exact Hnames|].
        split; [|split; [apply parked_stacks_empty_consistent|intros eid pcp queue Hlease; discriminate]].
        intros name [[Henabled [i [t [Hlookup Hname]]]] |
          [[Henabled [i [e [Hlookup Hname]]]] |
          [[Henabled [Hnamed [i [g [Hlookup Hname]]]]] |
          [[Henabled [Hnamed Hreference]] | [Henabled [Hnamed [i [t [Hlookup Hname]]]]]]]]].
        -- discriminate.
        -- discriminate.
        -- cbn [kernel_full_boot_state FlagState] in Hlookup; rewrite Henabled in Hlookup; discriminate.
        -- destruct Hreference as [[i [v [Hlookup Hname]]] | [i [v [Hlookup Hname]]]];
            cbn [kernel_full_boot_state MemoryState] in Hlookup; rewrite Henabled in Hlookup.
           ++ cbv beta iota zeta delta [memory_initial memControlImages] in Hlookup.
              destruct (andb (0 <=? i) (i <? cfgMaxMemPartitions (osKernelConfig sg))); [|discriminate].
              injection Hlookup as Himage; subst v.
              cbv beta iota zeta delta [memory_initial_image memImageName] in Hname.
              subst name; apply Hmemoryname; assumption.
           ++ discriminate.
        -- discriminate.
Qed.

(** These are actual initializer postconditions, not assumed global validity.
    The Memory initializer result, BSS CPUUsage/TickStep and Timer bytes and
    live name bytes remain explicit inputs. QInit's outstanding C cursor
    bound is not discharged by this conditional resource composition. *)
Definition kernel_full_boot_initializer_post (sg : StableGlobVars)
  (task_name event_name flag_name memory_name : addr)
  (names : NameResourceState) : Assertion :=
  init_misc_zero sg **
  init_rdy_list_post sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) sg.(g_OSPrioCur)
    sg.(g_OSPrioHighRdy) sg.(g_OSTCBHighRdy) sg.(g_OSTCBCur) **
  init_tcb_list_full_post sg task_name ** init_event_list_named_post sg event_name **
  flag_init_post sg flag_name ** OS_QInit_spec sg **
  memory_raw_rep sg (memory_initial sg memory_name) **
  sg.(g_OSCPUUsage) # UChar |-> 0 ** sg.(g_OSTickStepState) # UChar |-> 0 **
  timer_uninitialized_rep sg ** store_name_bytes names.

Lemma kernel_full_boot_initializer_post_establishes_global_inv :
  forall sg task_name event_name flag_name memory_name names,
  full_features_kernel_profile sg -> init_tcb_list_full_profile sg ->
  valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
   sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  kernel_full_boot_initializer_post sg task_name event_name flag_name memory_name names |--
  UCOS2_full_inv sg
    (kernel_full_boot_state sg task_name event_name flag_name memory_name names).
Proof.
  intros sg task_name event_name flag_name memory_name names Hprofile Htcb Hnames Hmemoryname.
  pose proof (proj2 (proj2 (proj2 Htcb))) as Hconfig.
  pose proof (flag_init_profile_of_supported_configuration sg
    (or_intror Hconfig)) as Hflagprofile.
  pose proof (kernel_full_boot_state_valid sg task_name event_name flag_name
    memory_name names Hprofile Hnames Hmemoryname) as Hboot.
  unfold kernel_full_boot_initializer_post, init_misc_zero.
  sepcon_right_assoc.
  sep_apply_l_atomic (init_tcb_list_full_post_to_task_boot sg task_name Htcb).
  sep_apply_l_atomic (init_rdy_list_post_implies_sched_boot_rep sg (task_boot sg task_name)).
  sep_apply_l_atomic (init_event_list_named_post_to_event_raw_rep sg (task_boot sg task_name) event_name).
  sep_apply_l_atomic (q_init_spec_establishes_queue_storage sg).
  sep_apply_l_atomic (flag_init_post_to_flag_raw_rep sg flag_name Hflagprofile).
  unfold UCOS2_full_inv.
  eapply derivable1_trans with (y := UCOS2_raw_rep sg
    (kernel_full_boot_state sg task_name event_name flag_name memory_name names)); [|entailer!].
  unfold UCOS2_raw_rep, kernel_full_boot_state.
  cbn [TskState SchedState IntrState EventState TickState FlagState MemoryState TimerState
    StatsState ControlState NameState].
  rewrite task_boot_shared_rep_equiv.
  unfold interrupt_inv, interrupt_in_range, store_int_state,
    tick_inv, store_tick_state, flag_configured_rep, memory_configured_rep, timer_configured_rep,
    statistics_rep, kernel_control_rep, kernel_control_initial.
  rewrite Hconfig.
  cbn [cfgFlagEnabled cfgMemoryEnabled cfgTimerEnabled cfgStatisticsEnabled cfgSafetyCriticalIEC
    full_features_kernel_configuration timerInitPhase timer_uninitialized statistics_initial
    idleCtr idleCtrMax idleCtrRun cpuUsage statReady safetyCriticalStarted
    intNesting lockNesting ostime tickStepState].
  entailer!.
Qed.
