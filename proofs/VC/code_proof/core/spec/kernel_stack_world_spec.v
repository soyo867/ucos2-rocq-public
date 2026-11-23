Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The executing invocation, not the current raw pool address, fixes the
    coverage exception. Boot has no active task generation. *)
Definition task_stack_call_active_key (call : OsSchedCallContext) : option (TaskID * nat) :=
  match call.(os_sched_call_origin) with
  | BootInvocation => None
  | RunningInvocation slot generation => Some (slot, generation)
  end.

(** The source-established stack view at one execution cut. The active
    key is the coverage exemption for the executing stack, not another
    kernel field. Absence from the parked map is supplied by its actual
    take/entry source where needed; coverage alone does not imply it.
    The supplied resource predicate owns the actual shared bytes,
    including store_parked_stacks; the continuation map below owns only
    the matching dormant execution resources and their frame/SP facts.

    [resources] stays a parameter: selected64 and full-profile worlds use
    their own representation. A private-object loan may be part of this
    owner, but must be transferred by the actual source step that resumes
    its creator. This definition provides no frame rule across Restore.
    In particular a weak armv7a_task_continuations assertion cannot be
    upgraded to this invariant without its missing source producer. *)
Definition kernel_stack_inv {external platform port}
  (abi : Armv7aContinuationABI external platform port)
  (resources : StableGlobVars -> UCOS2_Verify_State -> Assertion)
  sg active state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState) active) &&
  (resources sg state ** armv7a_task_stack_continuations abi state.(TskState)
    state.(TskState).(parkedTaskStacks)).

(** A projection for an old consumer, never an equivalence. A caller that
    will switch again must retain the stronger world at its next cut. *)
Lemma kernel_stack_inv_forget : forall external platform port
  (abi : Armv7aContinuationABI external platform port) resources sg active state,
  kernel_stack_inv abi resources sg active state |--
  coq_prop (task_stack_live_coverage state.(TskState) active) &&
  (resources sg state ** armv7a_task_continuations abi state.(TskState).(parkedTaskStacks)).
Proof.
  intros; unfold kernel_stack_inv; Intros.
  sep_apply_l_atomic (armv7a_task_stack_continuations_forget external platform port abi
    state.(TskState) state.(TskState).(parkedTaskStacks)); entailer!.
Qed.

(** Split a real extra owner at this SAME state and heap. This is not a
    claim that the owner, the state, or a borrowed byte survives a call. *)
Lemma kernel_stack_inv_split_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) resources extra sg active state,
  kernel_stack_inv abi (fun sg state => resources sg state ** extra sg state) sg active state --||--
  kernel_stack_inv abi resources sg active state ** extra sg state.
Proof. intros; unfold kernel_stack_inv; split; entailer!. Qed.

(** Beginning a new call focuses only an absent key. Existing parked
    descriptors cannot be relabelled as this invocation or its PC/LR. *)
Lemma kernel_stack_inv_focus_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port) resources sg active state focus,
  state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = None ->
  kernel_stack_inv abi resources sg active state |--
  coq_prop (task_stack_live_coverage state.(TskState) active) &&
  (resources sg state ** armv7a_task_call_stacks abi state.(TskState) focus
    state.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi resources sg active state focus Habsent.
  unfold kernel_stack_inv; Intros.
  sep_apply_l_atomic (armv7a_task_call_stacks_absent external platform port abi
    state.(TskState) focus state.(TskState).(parkedTaskStacks) Habsent); entailer!.
Qed.

Lemma kernel_stack_inv_after_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port) resources sg active state focus,
  coq_prop (task_stack_live_coverage state.(TskState) active) &&
  (resources sg state ** armv7a_task_call_stacks abi state.(TskState) focus
    state.(TskState).(parkedTaskStacks)) |--
  kernel_stack_inv abi resources sg active state.
Proof.
  intros; Intros; unfold kernel_stack_inv.
  sep_apply_l_atomic (armv7a_task_call_stacks_forget external platform port abi
    state.(TskState) focus state.(TskState).(parkedTaskStacks)); entailer!.
Qed.

(** Initialization supplies the first world, before any TaskCreate. Only
    the empty dormant map is introduced from emp; all real kernel bytes
    remain those of the supplied initializer postcondition. *)
Lemma kernel_stack_inv_boot : forall external platform port
  (abi : Armv7aContinuationABI external platform port) resources sg state name,
  state.(TskState) = task_boot sg name ->
  resources sg state |-- kernel_stack_inv abi resources sg None state.
Proof.
  intros external platform port abi resources sg state name Htasks.
  assert (Hcoverage : task_stack_live_coverage state.(TskState) None).
  { rewrite Htasks; apply task_boot_stack_coverage. }
  assert (Hempty : armv7a_task_stack_continuations abi state.(TskState)
    state.(TskState).(parkedTaskStacks) --||-- emp).
  { rewrite Htasks; unfold armv7a_task_stack_continuations, store_parked_continuations.
    apply store_map_empty.
    - exists []; split.
      + intros key; split; [intros Hin; contradiction|intros [payload Hentry]; discriminate].
      + constructor.
    - intros key; left; reflexivity. }
  unfold kernel_stack_inv; rewrite Hempty; entailer!.
Qed.
