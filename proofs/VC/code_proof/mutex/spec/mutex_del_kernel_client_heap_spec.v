Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_borrow_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Import UCOS2_C_Rules KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A creator's returned POINTER selects this resource cut. The allocation
    identity is existentially produced by the actual free-pop, not chosen
    by a source descriptor. All private bytes and the WHOLE capsule map are
    still owned; the cut is BEFORE Restore, not a private frame across it. *)
Definition mutex_del_creator_heap_resources {external platform port}
  (abi : Armv7aContinuationABI external platform port) sg pointer state : Assertion :=
  EX eid allocation,
    coq_prop (pointer = event_pool_addr sg eid /\
      state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation) &&
    (kernel_client_heap_world abi sg state ** event_private_storage_rep sg eid allocation).

(** This is the selected source's layout/address binding, followed by its
    real root/next reads and root store. It has no state, invariant, owner
    protocol or desired output premise. Both empty and nonempty branches
    are retained. Later creator fields are a different extension. *)
Inductive mutex_del_creator_heap_step (sg : StableGlobVars) :
  KernelClientHeapCut Z -> model -> KernelClientHeapCut Z -> model -> Prop :=
| MutexDelCreatorHeapEmpty : forall heap,
    sem_create_source_binding sg -> pointer_load sg.(g_OSEventFreeList) 0 heap ->
    mutex_del_creator_heap_step sg KernelClientHeapClosed heap KernelClientHeapClosed heap
| MutexDelCreatorHeapDetach : forall before pointer next after,
    sem_create_source_binding sg -> pointer <> 0 ->
    pointer_load sg.(g_OSEventFreeList) pointer before ->
    pointer_load (pointer + 4) next before ->
    kernel_heap_execution (pointer_store_writes sg.(g_OSEventFreeList) next) before after ->
    mutex_del_creator_heap_step sg KernelClientHeapClosed before (KernelClientHeapExtra pointer) after.

Inductive mutex_del_creator_heap_effect (sg : StableGlobVars) :
  KernelClientHeapCut Z -> UCOS2_Verify_State -> KernelClientHeapCut Z -> UCOS2_Verify_State -> Prop :=
| MutexDelCreatorHeapEmptyState : forall state returned,
    event_create_allocate_critical state None returned ->
    mutex_del_creator_heap_effect sg KernelClientHeapClosed state KernelClientHeapClosed returned
| MutexDelCreatorHeapDetachState : forall state returned eid image,
    event_create_allocate_critical state (Some (eid, image)) returned ->
    mutex_del_creator_heap_effect sg KernelClientHeapClosed state
      (KernelClientHeapExtra (event_pool_addr sg eid)) returned.

(** Internal registry certificate, PROVED from the adopted producer. The
    actual supplied endpoint is joined by deterministic physical reads and
    writes; no platform law is granted a post-world or a fresh allocation. *)
Lemma mutex_del_creator_heap_extension_valid : forall external platform port
  (abi : Armv7aContinuationABI external platform port),
  kernel_client_heap_extension_valid abi (mutex_del_creator_heap_resources abi)
    mutex_del_creator_heap_step mutex_del_creator_heap_effect.
Proof.
  intros external platform port abi sg cut before next after state frame Hsource Hpre.
  assert (Hpre_closed : (kernel_client_heap_world abi sg state ** frame) before).
  { destruct Hsource; exact Hpre. }
  assert (Hsplit : kernel_client_heap_world abi sg state ** frame |-- kernel_program_inv sg state **
    (armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame)).
  { unfold kernel_client_heap_world; entailer!. }
  destruct Hsource as [heap Hbinding Hread|before pointer next after Hbinding Hnonzero Hread Hnext Hwrites].
  - destruct (event_create_allocate_heap_source sg state heap _ Hbinding (Hsplit heap Hpre_closed))
      as [result [allocated [produced [Hhead [Hstep [Hrun Hpost]]]]]].
    pose proof (pointer_load_deterministic _ _ _ _ Hread Hhead) as Hpointer.
    destruct result as [[eid image]|].
    + destruct Hrun as [Hnonzero _]; cbn [event_create_return_ptr] in Hpointer.
      exfalso; apply Hnonzero; symmetry; exact Hpointer.
    + destruct (event_create_allocate_critical_empty_frame _ _ Hstep) as [_ ->].
      exists state; split; [constructor; exact Hstep|exact Hpre_closed].
  - destruct (event_create_allocate_heap_source sg state before _ Hbinding (Hsplit before Hpre_closed))
      as [result [allocated [produced [Hhead [Hstep [Hrun Hpost]]]]]].
    pose proof (pointer_load_deterministic _ _ _ _ Hread Hhead) as Hpointer.
    destruct result as [[eid image]|].
    + cbn [event_create_return_ptr] in Hpointer.
      destruct Hrun as [Hpositive [actual_next [Hnext_read Hwrite]]].
      assert (next = actual_next).
      { rewrite Hpointer in Hnext; eapply pointer_load_deterministic; eassumption. }
      subst actual_next.
      assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
      pose proof (event_create_allocate_critical_task_frame _ _ _ Hstep) as Htasks.
      pose proof (proj2 (event_create_allocate_critical_private_result state eid image allocated Hstep)) as Hlookup.
      exists allocated; split.
      * rewrite Hpointer; econstructor; exact Hstep.
      * assert (Hmerge : kernel_program_inv sg allocated **
          event_private_storage_rep sg eid (sem_create_allocation_identity state image) **
          (armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame) |--
          kernel_client_heap_resources abi (mutex_del_creator_heap_resources abi) sg
            (KernelClientHeapExtra pointer) allocated ** frame).
        { cbn [kernel_client_heap_resources]; unfold mutex_del_creator_heap_resources.
          Exists eid (sem_create_allocation_identity state image).
          unfold kernel_client_heap_world; rewrite Htasks; entailer!. }
        exact (Hmerge after Hpost).
    + cbn [event_create_return_ptr] in Hpointer; exfalso; apply Hnonzero; exact Hpointer.
Qed.

(** This constructor is supplyable from the actual shared owner, including
    ordinary exhaustion. It returns both a source step for the registry and
    the precise resulting cut, with the same frame and unchanged map. *)
Lemma mutex_del_creator_heap_produces_cut : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state before (frame : Assertion),
  sem_create_source_binding sg ->
  (kernel_client_heap_world abi sg state ** frame) before ->
  exists cut after returned,
    mutex_del_creator_heap_step sg KernelClientHeapClosed before cut after /\
    mutex_del_creator_heap_effect sg KernelClientHeapClosed state cut returned /\
    (kernel_client_heap_resources abi (mutex_del_creator_heap_resources abi) sg cut returned ** frame) after.
Proof.
  intros external platform port abi sg state before frame Hbinding Hpre.
  assert (Hsplit : kernel_client_heap_world abi sg state ** frame |-- kernel_program_inv sg state **
    (armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame)).
  { unfold kernel_client_heap_world; entailer!. }
  destruct (event_create_allocate_heap_source sg state before _ Hbinding (Hsplit before Hpre))
    as [result [allocated [after [Hread [Hstep [Hrun Hpost]]]]]].
  assert (Hsource : exists cut, mutex_del_creator_heap_step sg KernelClientHeapClosed before cut after).
  { destruct result as [[eid image]|].
    - destruct Hrun as [Hnonzero [next [Hnext Hwrite]]].
      exists (KernelClientHeapExtra (event_pool_addr sg eid)); econstructor; eassumption.
    - subst after; exists KernelClientHeapClosed; constructor; assumption. }
  destruct Hsource as [cut Hsource].
  destruct (mutex_del_creator_heap_extension_valid external platform port abi sg KernelClientHeapClosed before
    cut after state frame Hsource Hpre) as [returned [Heffect Hafter]].
  exists cut, after, returned; split; [exact Hsource|]. split; assumption.
Qed.

(** Annotation-facing close: all actual source steps are consumed on their
    real heaps. A closed endpoint returns the NEW raw state, single table,
    and whole map, along with the actual logical-operation projection.
    It does not establish caller execution/stack permission, private-slot
    access, owner-use or return to the interrupted invocation. *)
Lemma mutex_del_registered_heap_closed : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg cut state before after (frame : Assertion),
  kernel_client_heap_trace mutex_del_creator_heap_step sg cut before KernelClientHeapClosed after ->
  (kernel_client_heap_resources abi (mutex_del_creator_heap_resources abi) sg cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace mutex_del_creator_heap_effect sg cut state KernelClientHeapClosed returned /\
    UCOS2_state_inv sg returned /\
    (UCOS2_raw_rep sg returned ** unmap_table_rep sg **
     armv7a_task_continuations abi returned.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg cut state before after frame Htrace Hpre.
  destruct (kernel_client_heap_trace_resources external platform port Z abi
    (mutex_del_creator_heap_resources abi) mutex_del_creator_heap_step mutex_del_creator_heap_effect
    (mutex_del_creator_heap_extension_valid external platform port abi)
    sg cut before KernelClientHeapClosed after frame Htrace state Hpre) as [returned [Hlogical Hpost]].
  assert (Hsplit : kernel_client_heap_resources abi (mutex_del_creator_heap_resources abi)
      sg KernelClientHeapClosed returned ** frame |-- coq_prop (UCOS2_state_inv sg returned) &&
    (UCOS2_raw_rep sg returned ** unmap_table_rep sg **
     armv7a_task_continuations abi returned.(TskState).(parkedTaskStacks) ** frame)).
  { cbn [kernel_client_heap_resources]; unfold kernel_client_heap_world, kernel_program_inv.
    entailer!. }
  destruct (Hsplit after Hpost) as [Hvalid Hraw].
  exists returned; split; [exact Hlogical|]. split; assumption.
Qed.

(** Compatibility consumer for the ALREADY modeled two counter calls.
    Their matched call/return cursors come from the existing actual handler
    source relation. This is not a statement that every BSP uses only them,
    nor that TCB publication can execute directly in ISR context. *)
Inductive mutex_del_counter_handler_segment {Local} (sg : StableGlobVars) :
  RestoreHandlerCursor Local -> KernelClientHeapCut Z -> model ->
  RestoreHandlerCursor Local -> KernelClientHeapCut Z -> model -> Prop :=
| MutexDelCounterHandlerSegment : forall cursor before call after,
    cursor.(restore_handler_pc) = call.(restore_handler_kernel_call_pc) ->
    restore_handler_client_execution sg call.(restore_handler_kernel_kind) before after ->
    mutex_del_counter_handler_segment sg cursor KernelClientHeapClosed before
      (restore_handler_return_cursor cursor call.(restore_handler_kernel_return_pc)) KernelClientHeapClosed after.

Lemma mutex_del_counter_handler_segment_source : forall Local sg cursor cut before returned_cursor next after,
  @mutex_del_counter_handler_segment Local sg cursor cut before returned_cursor next after ->
  kernel_client_heap_step mutex_del_creator_heap_step sg cut before next after.
Proof.
  intros Local sg cursor cut before returned_cursor next after Hsource; destruct Hsource.
  destruct H0 as [before after Henter|before after Hexit].
  - apply KernelClientHeapEnter; destruct Henter; econstructor; eassumption.
  - apply KernelClientHeapExit; exact Hexit.
Qed.

Lemma mutex_del_counter_handler_trace : forall Local local_step sg cursor before returned_cursor after,
  @restore_handler_execution Local local_step sg cursor before returned_cursor after ->
  kernel_client_handler_trace local_step mutex_del_counter_handler_segment sg
    cursor KernelClientHeapClosed before returned_cursor KernelClientHeapClosed after.
Proof.
  intros Local local_step sg cursor before returned_cursor after Hrun; induction Hrun.
  - constructor.
  - eapply KernelClientHandlerLocal; eassumption.
  - eapply KernelClientHandlerSegment; [econstructor; eassumption|exact IHHrun].
Qed.

(** The old BSP normal-return classification can now consume the new
    full-map registry, on the SAME actual invocation and final heap. No new
    BSP field or OS-level law is postulated. General handler coverage still
    needs a source classification into registered segments and physical
    cursor/cut ownership for switches/nesting; these two calls are not that
    complete classification. *)
Lemma mutex_del_counter_handler_return_world : forall external platform port Local
  (abi : Armv7aContinuationABI external platform port)
  (private : RestoreHandlerCall -> Local -> Assertion) local_step normal_return,
  RestoreHandlerContract private local_step normal_return ->
  forall sg state cursor before returned_cursor after (frame : Assertion),
  normal_return sg cursor before returned_cursor after ->
  (kernel_client_heap_world abi sg state **
   private cursor.(restore_handler_current_call) cursor.(restore_handler_local) ** frame) before ->
  exists returned,
    returned_cursor.(restore_handler_current_call) = cursor.(restore_handler_current_call) /\
    returned_cursor.(restore_handler_pc) = cursor.(restore_handler_current_call).(restore_handler_return_word) /\
    kernel_client_heap_state_trace mutex_del_creator_heap_effect sg
      KernelClientHeapClosed state KernelClientHeapClosed returned /\
    (kernel_client_heap_world abi sg returned **
     private returned_cursor.(restore_handler_current_call) returned_cursor.(restore_handler_local) ** frame) after.
Proof.
  intros external platform port Local abi private local_step normal_return Hcontract
    sg state cursor before returned_cursor after frame Hreturn Hpre.
  destruct (restore_handler_return_refinement _ _ _ Hcontract sg cursor before returned_cursor after Hreturn)
    as [Hcall [Hpc Hrun]].
  pose proof (mutex_del_counter_handler_trace Local local_step sg cursor before returned_cursor after Hrun) as Htrace.
  assert (Hprivate : forall sg cursor cut before returned_cursor next after,
    mutex_del_counter_handler_segment sg cursor cut before returned_cursor next after ->
    private cursor.(restore_handler_current_call) cursor.(restore_handler_local) =
      private returned_cursor.(restore_handler_current_call) returned_cursor.(restore_handler_local)).
  { intros sg' cursor' cut before' returned_cursor' next after' Hsegment; destruct Hsegment; reflexivity. }
  destruct (kernel_client_handler_trace_resources external platform port (RestoreHandlerCursor Local) Z abi
    (mutex_del_creator_heap_resources abi) mutex_del_creator_heap_step mutex_del_creator_heap_effect
    (fun cursor => private cursor.(restore_handler_current_call) cursor.(restore_handler_local))
    local_step mutex_del_counter_handler_segment (mutex_del_creator_heap_extension_valid external platform port abi)
    (mutex_del_counter_handler_segment_source Local) Hprivate
    (restore_handler_local_resources _ _ _ Hcontract)
    sg cursor KernelClientHeapClosed before returned_cursor KernelClientHeapClosed after frame Htrace state Hpre)
    as [returned [Hlogical Hpost]].
  exists returned; split; [exact Hcall|]. split; [exact Hpc|]. split; assumption.
Qed.
