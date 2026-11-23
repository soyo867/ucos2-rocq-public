Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Fresh logical registration preserves the exact pending Scheduler
    entry. The invocation ledger changes; the physical stack map, TCBs
    and saved SPs do not. Freshness follows from the owned state's valid
    ledger, so an older active invocation is not overwritten. *)
Lemma kernel_saved_sched_call_map_begin_invocation : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg original saved acquired descriptor
  state origin focus,
  UCOS2_state_inv sg state ->
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus)
    state.(TskState).(parkedTaskStacks) |--
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor
      (task_begin_invocation origin state.(TskState)) focus)
    (task_begin_invocation origin state.(TskState)).(parkedTaskStacks).
Proof.
  intros external platform port abi critical sg original saved acquired descriptor state origin focus Hvalid.
  apply kernel_saved_sched_call_map_reindex.
  - intros key payload node Hlookup Hnode Hg; exists node; repeat split; assumption || reflexivity.
  - intros Hactive; apply task_begin_invocation_preserves_invocation_active; [|exact Hactive].
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 (proj2 Hvalid))))))).
Qed.

(** First C entry of a physically restored initial task. The already
    approved entry ABI consumes initial execution once; the current/live
    binding comes from the actual selector/install source. Fragments are
    the real remaining stack after any caller-owned local-cell partition.
    No byte, saved token, inside handle or completed API event is created.

    The pending Scheduler invocation remains in the same exact map. Its
    own saved/inside pair can subsequently be recovered by the shared
    focus consumer after the newly entered task reaches a real wait cut. *)
Lemma kernel_saved_sched_call_initial_entry_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (entry : Armv7aInitialCallABI external platform port abi)
  critical sg state selected fragments original saved acquired descriptor focus,
  armv7a_initial_frame_binding selected ->
  task_stack_fragments_in_range
    selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0 fragments ->
  task_current_at state selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  UCOS2_inv sg state ** armv7a_initial_execution abi selected **
    task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion) fragments **
    store_parked_continuations
      (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus)
      state.(TskState).(parkedTaskStacks) |--
  let current := armv7a_initial_call_registered selected state in
  let call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
  coq_prop (kernel_call_task_source call current) &&
    (kernel_call_execution_owned external platform call
       (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
     UCOS2_inv sg current ** store_parked_continuations
       (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor current.(TskState) focus)
       current.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi entry critical sg state selected fragments original saved acquired descriptor
    focus Hbinding Hgeometry Hcurrent.
  cbv zeta.
  assert (Hobserve : UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) && UCOS2_inv sg state)
    by (unfold UCOS2_inv; entailer!).
  sep_apply_l_atomic Hobserve; Intros.
  assert (Hvalid : UCOS2_state_inv sg state) by assumption.
  pose proof (armv7a_initial_call_register_resources external platform port abi entry sg state selected fragments
    Hbinding Hgeometry Hcurrent) as Hregister.
  cbv zeta in Hregister; sep_apply_l_atomic Hregister; Intros.
  sep_apply_l_atomic (kernel_saved_sched_call_map_begin_invocation external platform port abi critical sg
    original saved acquired descriptor state
    (RunningInvocation selected.(armv7a_continuation_stack).(stackLeaseSlot)
      selected.(armv7a_continuation_stack).(stackLeaseGeneration)) focus Hvalid).
  unfold armv7a_initial_call_registered; entailer!.
Qed.
