Require Import Coq.ZArith.ZArith Coq.Lists.List.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source/os_task.c's two creation wrappers call TCBInit with the actual
    StackInit return value.  This is the resource implication at that same
    normal-return/call boundary, not a claim that the outside kernel state
    stayed unchanged while StackInit was executing.  The basic and extended
    argument constructors retain their original zero/explicit fields. *)
Lemma task_create_stack_init_post_tcb_call_input :
  forall platform critical sg region args task_return lower upper initial_name
    invocation origin mask current returned_sp,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_stack_init_post TaskStackNoVFP region.(stackRegionBase) args.(createStackTop)
    args.(createEntry) args.(createArgument) task_return (task_create_options args)
    lower upper returned_sp **
  task_tcb_init_pre platform critical sg (task_create_tcb_args args returned_sp initial_name)
    invocation origin mask current |--
  task_tcb_init_stack_pre platform critical sg region args task_return lower upper
    initial_name invocation origin mask current.
Proof.
  intros platform critical sg region args task_return lower upper initial_name
    invocation origin mask current returned_sp Hlayout.
  sep_apply_l_atomic (task_create_stack_init_post_storage TaskStackNoVFP region args task_return
    lower upper returned_sp Hlayout).
  Intros; destruct H as [Hsp Hrange]; subst returned_sp.
  unfold task_tcb_init_stack_pre; entailer!.
Qed.

(** The source-facing callee is reached with actual call-boundary owners:
    StackInit supplies this buffer, and the caller supplies its execution
    context and the current whole capsule map.  No map from an earlier
    release cut is transported across an open interval here. *)
Lemma task_create_stack_init_post_stack_call_input :
  forall environment critical sg region args task_return lower upper initial_name
    invocation origin mask current call returned_sp,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  call.(os_sched_call_invocation) = invocation -> call.(os_sched_call_origin) = origin ->
  task_stack_live_coverage current.(TskState) (task_stack_call_active_key call) ->
  task_stack_init_post TaskStackNoVFP region.(stackRegionBase) args.(createStackTop)
    args.(createEntry) args.(createArgument) task_return (task_create_options args)
    lower upper returned_sp **
  task_tcb_init_pre environment.(task_stack_call_platform) critical sg
    (task_create_tcb_args args returned_sp initial_name) invocation origin mask current **
  task_tcb_init_stack_context environment call ** task_tcb_init_stack_capsules environment current |--
  task_tcb_init_stack_call_pre environment critical sg region args task_return lower upper initial_name
    invocation origin mask current call.
Proof.
  intros environment critical sg region args task_return lower upper initial_name invocation origin mask
    current call returned_sp Hlayout Hinvocation Horigin Hcoverage.
  sepcon_assoc_change.
  sep_apply_l_atomic (task_create_stack_init_post_tcb_call_input environment.(task_stack_call_platform)
    critical sg region args task_return lower upper initial_name invocation origin mask current returned_sp Hlayout).
  unfold task_tcb_init_stack_call_pre, task_tcb_init_stack_context, task_tcb_init_stack_capsules; entailer!.
Qed.

(** The actual sixteen StackInit writes produce the buffer used at the
    immediately following TCBInit call.  The supplied call-boundary owner
    is framed through these local stores; this does not freeze a kernel
    snapshot over an intervening interrupt or scheduler execution. *)
Lemma task_create_stack_init_source_tcb_call_input :
  forall platform critical sg region args task_return lower old_frame upper initial_name
    invocation origin mask current (frame : Assertion) before,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  Zlength old_frame = 16 ->
  0 <= args.(createEntry) < 4294967296 ->
  0 <= args.(createArgument) < 4294967296 -> 0 <= task_return < 4294967296 ->
  (task_stack_storage region (lower ++ old_frame ++ upper) **
   task_tcb_init_pre platform critical sg
     (task_create_tcb_args args (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name)
     invocation origin mask current ** frame) before ->
  exists after,
    kernel_heap_execution
      (task_stack_init_no_vfp_writes args.(createStackTop) args.(createEntry)
        args.(createArgument) task_return) before after /\
    (task_tcb_init_stack_pre platform critical sg region args task_return lower upper
       initial_name invocation origin mask current ** frame) after.
Proof.
  intros platform critical sg region args task_return lower old_frame upper initial_name
    invocation origin mask current frame before Hlayout Hlength Hentry Hargument Hreturn Hbefore.
  assert (Horder : task_stack_storage region (lower ++ old_frame ++ upper) **
      task_tcb_init_pre platform critical sg
        (task_create_tcb_args args (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name)
        invocation origin mask current ** frame |--
    task_stack_storage region (lower ++ old_frame ++ upper) **
      (task_tcb_init_pre platform critical sg
        (task_create_tcb_args args (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name)
        invocation origin mask current ** frame)) by entailer!.
  destruct (task_create_stack_init_store_execution region args task_return lower old_frame upper
    _ before Hlayout Hlength Hentry Hargument Hreturn (Horder before Hbefore)) as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  match type of Hafter with ?P after =>
    assert (Hpack : P |-- task_tcb_init_stack_pre platform critical sg region args task_return
      lower upper initial_name invocation origin mask current ** frame)
  end.
  { unfold task_tcb_init_stack_pre; entailer!. }
  exact (Hpack after Hafter).
Qed.
