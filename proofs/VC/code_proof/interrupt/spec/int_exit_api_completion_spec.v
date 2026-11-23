Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_api_program_spec.
From SimpleC.SL Require Import Mem SeparationLogic.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Both exits of the C API retain the original continuation. The transferred
    arm uses the already approved nonlocal platform output; it is not the
    impossible ordinary Ensure of OSIntCtxSw. *)
Definition os_int_exit_completed_program_post external platform port critical sg
  context mask saved before X (outcome : OsIntExitOutcome) : Assertion :=
  coq_prop (os_int_exit_full_call external port critical sg context before outcome /\
    X outcome (os_int_exit_outcome_state before outcome)) &&
  match outcome with
  | OsIntExitReturned entry =>
      let final := os_int_exit_ready_checkpoint before.(SchedState).(isRunning) entry in
      coq_prop (UCOS2_state_inv sg final) &&
      (sg.(g_OSRunning) # UChar |-> os_int_exit_running final **
        os_int_exit_outside_frame platform port critical sg context mask final)
  | OsIntExitExceptionTransferred entry transfer =>
      os_int_exit_transfer_post external port sg context saved entry transfer
  end.

Lemma os_int_exit_returned_program_completion : forall external platform port critical
  sg context mask saved before X,
  os_int_exit_program_post platform port critical sg context mask before X |--
  EX outcome, os_int_exit_completed_program_post external platform port critical sg
    context mask saved before X outcome.
Proof.
  intros external platform port critical sg context mask saved before X heap
    [entry [[Hreturn [Hvalid HX]] Hresources]].
  exists (OsIntExitReturned entry).
  split; [exact (conj Hreturn HX)|exact (conj Hvalid Hresources)].
Qed.

(** call_heap is the heap at the actual OSIntCtxSw call, after the C selector
    and counter writes. completion_heap is that invocation's nonlocal platform
    output. All call indices, including saved/before/entry/context/X, are shared.
    The original transfer output is consumed, not asserted as a new platform law. *)
Lemma os_int_exit_transfer_call_completion : forall external platform port critical
  sg context mask saved before entry transfer X call_heap completion_heap,
  os_int_exit_transfer_program_pre external platform port critical sg context saved
    before entry X call_heap ->
  os_int_exit_transfer_post external port sg context saved entry transfer completion_heap ->
  os_int_exit_completed_program_post external platform port critical sg context
    mask saved before X (OsIntExitExceptionTransferred entry transfer) completion_heap.
Proof.
  intros external platform port critical sg context mask saved before entry transfer
    X call_heap completion_heap [[Hrunning [Hinterval Hsafe]] Hcall] Hcompleted.
  pose proof (os_int_exit_transfer_post_program_post external port critical sg context
    saved before entry transfer X Hrunning Hinterval Hsafe completion_heap Hcompleted)
    as [HX Hpost].
  split.
  - split; [exact (conj Hrunning (conj Hinterval (proj1 Hpost)))|exact HX].
  - exact Hpost.
Qed.

Lemma os_int_exit_completed_program_continuation : forall external platform port critical
  sg context mask saved before X outcome heap,
  os_int_exit_completed_program_post external platform port critical sg context
    mask saved before X outcome heap ->
  X outcome (os_int_exit_outcome_state before outcome).
Proof.
  intros external platform port critical sg context mask saved before X outcome heap
    [[Hsource HX] Hresources]; exact HX.
Qed.
