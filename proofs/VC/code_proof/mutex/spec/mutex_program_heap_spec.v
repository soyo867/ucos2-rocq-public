Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The history and resources are indexed by the state produced by the
    SAME concrete execution. The logical source history does not conjure
    heap bytes or a continuation. These are the current physical registry's
    IntEnter/IntExit, TCB-publication and Sem/Mbox allocation/store/publish
    cuts; other source registries need their corresponding physical proof. *)
Lemma mutex_program_creator_state_trace : forall initial creator sg cut state next returned,
  mutex_program_reachable initial sg state ->
  kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut state next returned ->
  mutex_program_reachable initial sg returned.
Proof.
  intros initial creator sg cut state next returned Hreachable Htrace.
  revert Hreachable; induction Htrace; intro Hreachable; [exact Hreachable|].
  apply IHHtrace; eapply mutex_program_source_step_reachable; [exact Hreachable|].
  eapply MutexOwnerSourceCreator; eassumption.
Qed.

Lemma mutex_program_creator_heap_trace : forall external platform port
  (abi : Armv7aContinuationABI external platform port) initial creator sg cut state before next after
  (frame : Assertion),
  mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before next after ->
  (coq_prop (mutex_program_reachable initial sg state) &&
    (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state ** frame)) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    (coq_prop (mutex_program_reachable initial sg returned) &&
      (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg next returned ** frame)) after.
Proof.
  intros external platform port abi initial creator sg cut state before next after frame Hargs Hsource
    [Hreachable Hpre].
  destruct (kernel_client_heap_trace_resources external platform port Z abi
    (mutex_del_creator_pending abi) (mutex_del_creator_publication_step creator)
    (mutex_del_creator_publication_effect creator)
    (mutex_del_creator_publication_extension_valid external platform port abi creator Hargs)
    sg cut before next after frame Hsource state Hpre) as [returned [Hlogical Hpost]].
  exists returned; split; [exact Hlogical|]. split; [|exact Hpost].
  eapply mutex_program_creator_state_trace; eassumption.
Qed.
