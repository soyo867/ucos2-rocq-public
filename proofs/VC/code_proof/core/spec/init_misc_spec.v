Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.

Import ListNotations.
Import UCOS2_C_Rules.
Import TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The selected OS_InitMisc body owns ordinary RAM during serialized
    startup.  This exact post does not include OSCPUUsage, ready/priority
    storage, task pools, timer state, or a running-kernel invariant. *)
Definition init_misc_zero (sg : StableGlobVars) : Assertion :=
  sg.(g_OSTime) # UInt |-> 0 **
  sg.(g_OSIntNesting) # UChar |-> 0 **
  sg.(g_OSLockNesting) # UChar |-> 0 **
  sg.(g_OSTaskCtr) # UChar |-> 0 **
  sg.(g_OSRunning) # UChar |-> 0 **
  sg.(g_OSCtxSwCtr) # UInt |-> 0 **
  sg.(g_OSIdleCtr) # UInt |-> 0 **
  sg.(g_OSIdleCtrRun) # UInt |-> 0 **
  sg.(g_OSIdleCtrMax) # UInt |-> 0 **
  sg.(g_OSStatRdy) # UChar |-> 0 **
  sg.(g_OSTaskRegNextAvailID) # UChar |-> 0.

(** Cells supplied by this helper, not by OS_InitTCBList. *)
Definition init_misc_task_cells (sg : StableGlobVars) : Assertion :=
  sg.(g_OSTaskCtr) # UChar |-> 0 **
  sg.(g_OSTaskRegNextAvailID) # UChar |-> 0.

(** Cells supplied by this helper, not by OS_InitRdyList. *)
Definition init_misc_sched_cells (sg : StableGlobVars) : Assertion :=
  sg.(g_OSCtxSwCtr) # UInt |-> 0 **
  sg.(g_OSRunning) # UChar |-> 0.

Definition init_misc_other_cells (sg : StableGlobVars) : Assertion :=
  sg.(g_OSTime) # UInt |-> 0 **
  sg.(g_OSIntNesting) # UChar |-> 0 **
  sg.(g_OSLockNesting) # UChar |-> 0 **
  sg.(g_OSIdleCtr) # UInt |-> 0 **
  sg.(g_OSIdleCtrRun) # UInt |-> 0 **
  sg.(g_OSIdleCtrMax) # UInt |-> 0 **
  sg.(g_OSStatRdy) # UChar |-> 0.

Lemma init_misc_zero_split_frames : forall sg (R : Assertion),
  init_misc_zero sg ** R |--
  init_misc_task_cells sg ** init_misc_sched_cells sg **
    init_misc_other_cells sg ** R.
Proof.
  intros; unfold init_misc_zero, init_misc_task_cells,
    init_misc_sched_cells, init_misc_other_cells; entailer!.
Qed.

Lemma init_misc_zero_merge_frames : forall sg (R : Assertion),
  init_misc_task_cells sg ** init_misc_sched_cells sg **
    init_misc_other_cells sg ** R |-- init_misc_zero sg ** R.
Proof.
  intros; unfold init_misc_zero, init_misc_task_cells,
    init_misc_sched_cells, init_misc_other_cells; entailer!.
Qed.

(** This is an equality of the two scalar resources consumed by the
    existing task boot representation, not a claim about TCB storage. *)
Lemma init_misc_task_cells_boot_eq : forall sg name,
  0 < sg.(osKernelConfig).(cfgTaskRegisters) ->
  init_misc_task_cells sg =
    (sg.(g_OSTaskCtr) # UChar |-> (task_boot sg name).(taskCount) **
      task_reg_allocator_rep sg (task_boot sg name)).
Proof.
  intros sg name Hregs.
  unfold init_misc_task_cells, task_reg_allocator_rep.
  rewrite (proj2 (Z.ltb_lt 0 _) Hregs).
  reflexivity.
Qed.

Lemma init_misc_sched_cells_boot_eq : forall sg,
  init_misc_sched_cells sg =
    (sg.(g_OSCtxSwCtr) # UInt |-> sched_boot.(ctxSwCtr) **
      sg.(g_OSRunning) # UChar |->
        (if sched_boot.(isRunning) then 1 else 0)).
Proof. reflexivity. Qed.
