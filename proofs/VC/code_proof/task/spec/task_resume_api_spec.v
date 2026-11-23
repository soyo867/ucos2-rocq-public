Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_disabled_spec.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

(** Fresh whole-API intake imports. The annotation owner must establish the
    actual OSTaskResume call/resource contract. The critical-effect spec and
    contextual disabled Scheduler remain separate, read-only dependencies;
    neither these imports nor a historical candidate establish API correctness. *)

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The reserved pointer comparison needs the pool's actual object-base
    alignment, independently of the opaque addresses of its named fields.
    This is only the immutable projection of the existing initialization
    layout; it neither requires a live target nor constrains caller state. *)
Definition task_resume_tcb_pool_aligned (sg : StableGlobVars) : Prop :=
  sg.(g_OSTCBTbl) mod 4 = 0.

Lemma init_tcb_list_layout_implies_task_resume_tcb_pool_aligned : forall sg,
  init_tcb_list_layout sg -> task_resume_tcb_pool_aligned sg.
Proof. intros sg [_ [_ [_ [Haligned _]]]]; exact Haligned. Qed.

Lemma task_resume_slot_addr_ne_reserved : forall sg tid,
  selected_kernel_profile sg -> task_resume_tcb_pool_aligned sg ->
  task_slot_addr sg tid <> 1.
Proof.
  intros sg tid Hprofile Haligned Heq.
  destruct Hprofile as [_ [_ [_ [_ [Hconfig _]]]]].
  rewrite task_slot_addr_object_size, (task_object_size_tcb64 _ Hconfig) in Heq.
  unfold task_resume_tcb_pool_aligned in Haligned.
  pose proof (Z.div_mod sg.(g_OSTCBTbl) 4 ltac:(lia)) as Hdivision.
  rewrite Haligned in Hdivision; lia.
Qed.

Lemma task_resume_entry_addr_eq_reserved : forall sg entry,
  selected_kernel_profile sg -> task_resume_tcb_pool_aligned sg ->
  prio_tbl_entry_to_addr sg entry = 1 -> entry = PTReserved.
Proof.
  intros sg [| |tid] Hprofile Haligned Haddr.
  - discriminate.
  - reflexivity.
  - exfalso; exact (task_resume_slot_addr_ne_reserved sg tid Hprofile Haligned Haddr).
Qed.

(** These alternatives keep the actual execution resource.  In particular a
    generic caller is never converted to a Task stack lease. *)
Inductive TaskResumeCaller : Type :=
| ResumeTaskCaller (call : OsSchedCallContext)
| ResumeGenericCaller (view : OsExecutionView).

Definition task_resume_view caller : OsExecutionView :=
  match caller with
  | ResumeTaskCaller call => os_sched_execution_view call
  | ResumeGenericCaller view => view
  end.

Definition task_resume_same_caller first second : Prop :=
  match first, second with
  | ResumeTaskCaller first, ResumeTaskCaller second =>
      task_tcb_init_stack_same_call first second
  | ResumeGenericCaller first, ResumeGenericCaller second => first = second
  | _, _ => False
  end.

Definition task_resume_closed environment critical saved_local sg caller mask state : Assertion :=
  match caller with
  | ResumeTaskCaller call =>
      task_tcb_init_continuation_save_input environment critical saved_local sg call mask state **
      unmap_table_rep sg
  | ResumeGenericCaller view =>
      sched_disabled_closed environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical sg view mask state
  end.

Definition task_resume_masked environment critical saved_local sg caller saved acquired released : Assertion :=
  match caller with
  | ResumeTaskCaller call =>
      task_tcb_init_continuation_restore_input environment critical saved_local sg call
        saved acquired released ** unmap_table_rep sg
  | ResumeGenericCaller view =>
      sched_disabled_masked environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical sg view saved acquired released
  end.

(** The two raw primitive summaries are precisely the existing Task source
    contract and generic CPU/CSL contract, respectively.  They do not install
    contextual C preservation as a CPU/BSP postcondition. *)
Definition task_resume_save_output environment critical saved_local sg caller mask saved before : Assertion :=
  match caller with
  | ResumeTaskCaller call =>
      task_tcb_init_continuation_save_post environment critical saved_local sg call mask saved before **
      unmap_table_rep sg
  | ResumeGenericCaller view => EX acquired,
      coq_prop (critical_region_interval critical sg view.(os_execution_invocation) before acquired /\
        interrupt_saved_value mask saved) &&
      (critical_region_masked environment.(task_stack_call_platform) critical sg
         view.(os_execution_invocation) view.(os_execution_origin) saved acquired **
       UCOS2_raw_rep sg acquired **
       os_execution_view_resources environment.(task_stack_call_external) view)
  end.

Definition task_resume_restore_output environment critical saved_local sg caller saved released : Assertion :=
  match caller with
  | ResumeTaskCaller call =>
      task_tcb_init_continuation_restore_post environment critical saved_local sg call
        (armv7a_irq_fiq_mask saved) released ** unmap_table_rep sg
  | ResumeGenericCaller view => EX current,
      coq_prop (critical_region_interval critical sg view.(os_execution_invocation) released current) &&
      sched_disabled_closed environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical sg view
        (armv7a_irq_fiq_mask saved) current
  end.

(** A completed-return C protocol.  Its antecedent is the SAME source trace
    emitted by Save/Restore.  Availability is deliberately required only at
    the completed return, never at intermediate parked IRQ cuts. *)
Definition task_resume_completed_task_returns environment critical : Prop :=
  forall sg original returned before after,
    UCOS2_state_inv sg before -> kernel_call_task_source original before ->
    kernel_call_stack_available original before ->
    task_tcb_init_stack_same_call returned original ->
    kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      before false returned.(os_sched_call_origin) after ->
    kernel_call_stack_available returned after.

(** Non-running callers need neither a current Task lease nor positive
    interrupt/lock counters.  If the actual later OSRunning load is true,
    this same source predicate supplies the disabled Scheduler entry. *)
Definition task_resume_generic_source view state : Prop :=
  state.(SchedState).(isRunning) = false \/
  sched_disabled_entry_source view state.

(** Explicit completed-call C rely for a non-running entry.  It concerns
    the SAME interval and actual endpoints produced by Save/Restore; it
    neither rewrites their heap contracts nor freezes OSRunning.  A return
    with OSRunning=true is allowed when its actual context disables Task
    scheduling.  Running ISR/locked entries use the existing separate
    sched_disabled_completed_clients protocol. *)
Definition task_resume_completed_generic_returns critical view : Prop :=
  forall sg before after,
    UCOS2_state_inv sg before ->
    critical_region_interval critical sg view.(os_execution_invocation) before after ->
    before.(SchedState).(isRunning) = false ->
    task_resume_generic_source view after.

Definition task_resume_clients environment critical caller : Prop :=
  match caller with
  | ResumeTaskCaller _ => kernel_sched_ready_clients critical /\
      task_resume_completed_task_returns environment critical
  | ResumeGenericCaller view => sched_disabled_completed_clients critical view /\
      task_resume_completed_generic_returns critical view
  end.

Definition task_resume_caller_source sg caller state : Prop :=
  match caller with
  | ResumeTaskCaller call => kernel_call_task_source call state /\
      kernel_call_stack_available call state /\
      tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
        task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)
  | ResumeGenericCaller view => task_resume_generic_source view state
  end.

(** These two operations retain the full context returned by the existing
    source-facing calls. Same invocation/origin/stack does not identify
    context fragments, so the returned caller is a result, not a rewritten
    copy of the entry caller. Generic calls keep their exact execution view. *)
Definition task_resume_save_program environment critical sg original mask
  : program UCOS2_Verify_State (TaskResumeCaller * Z) :=
  fun before result acquired =>
    match original, fst result with
    | ResumeTaskCaller call, ResumeTaskCaller active =>
        kernel_call_save_source environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical sg call active mask
          (snd result) before acquired
    | ResumeGenericCaller view, ResumeGenericCaller active =>
        active = view /\
        critical_region_interval critical sg view.(os_execution_invocation) before acquired /\
        interrupt_saved_value mask (snd result)
    | _, _ => False
    end.

Definition task_resume_restore_program environment critical sg active
  : program UCOS2_Verify_State TaskResumeCaller :=
  fun released returned current =>
    match active, returned with
    | ResumeTaskCaller call, ResumeTaskCaller resumed =>
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients)
          sg call.(os_sched_call_invocation) None call.(os_sched_call_origin)
          released false resumed.(os_sched_call_origin) current /\
        task_tcb_init_stack_same_call resumed call
    | ResumeGenericCaller view, ResumeGenericCaller resumed =>
        resumed = view /\
        critical_region_interval critical sg view.(os_execution_invocation) released current
    | _, _ => False
    end.

Definition task_resume_acquire_facts environment critical sg original active mask initial acquired saved : Prop :=
  task_resume_same_caller active original /\
  UCOS2_state_inv sg acquired /\
  critical_region_interval critical sg
    (task_resume_view original).(os_execution_invocation) initial acquired /\
  interrupt_saved_value mask saved /\
  task_resume_clients environment critical active /\
  task_resume_caller_source sg active acquired /\
  task_resume_save_program environment critical sg original mask initial (active, saved) acquired.

(** The invariant is extracted once.  This residual retains the actual
    masked token, caller owner and (for Task callers) every parked local.
    Reindexing it after Resume requires live-SP/coverage preservation. *)
Definition task_resume_mask_frame environment critical saved_local sg caller saved acquired released : Assertion :=
  match caller with
  | ResumeTaskCaller call =>
      coq_prop (task_stack_live_coverage released.(TskState) (task_stack_call_active_key call)) &&
      (critical_region_masked environment.(task_stack_call_platform) critical sg
         call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
       os_sched_context_resources environment.(task_stack_call_external) call **
       task_tcb_init_continuation_capsules environment saved_local released ** unmap_table_rep sg)
  | ResumeGenericCaller view =>
      critical_region_masked environment.(task_stack_call_platform) critical sg
        view.(os_execution_invocation) view.(os_execution_origin) saved acquired **
      os_execution_view_resources environment.(task_stack_call_external) view
  end.

Definition task_resume_sched_pre environment critical saved_local sg caller mask state : Assertion :=
  match caller with
  | ResumeTaskCaller call => coq_prop (kernel_sched_ready_clients critical) &&
      os_sched_continuation_call_pre environment saved_local kernel_program_inv sg call mask state
  | ResumeGenericCaller view =>
      coq_prop (sched_disabled_completed_clients critical view /\
        UCOS2_state_inv sg state /\ sched_disabled_entry_source view state) &&
      sched_disabled_closed environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical sg view mask state
  end.

Definition task_resume_sched_post environment critical saved_local sg caller mask state : Assertion :=
  match caller with
  | ResumeTaskCaller call =>
      os_sched_continuation_history_return_post environment critical saved_local
        kernel_program_inv sg call mask state
  | ResumeGenericCaller view =>
      sched_disabled_contextual_post environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical sg view mask state
  end.

(** Exact critical checkpoint; the two surrounding intervals are allowed
    interference.  The local ready_path is retained rather than recomputed. *)
Definition task_resume_critical_code sg prio before (result : Z * bool) after : Prop :=
  exists error, fst result = encode_os_err_code error /\
    task_resume_critical sg prio before (error, snd result) after.

Definition task_resume_critical_history critical sg invocation prio initial result ready_path restored : Prop :=
  exists acquired released,
    critical_region_interval critical sg invocation initial acquired /\
    task_resume_critical_code sg prio acquired (result, ready_path) released /\
    critical_region_interval critical sg invocation released restored.

(** The active caller stays fixed during the protected C statements. Only
    the actual Save/Restore source relations can supply a new full context. *)
Definition task_resume_source_history environment critical sg original mask
  priority initial error ready_path returned restored : Prop :=
  exists active saved acquired released,
    task_resume_save_program environment critical sg original mask initial (active, saved) acquired /\
    task_resume_critical_code sg priority acquired (error, ready_path) released /\
    task_resume_restore_program environment critical sg active released returned restored.

Definition task_resume_source_prefix_program environment critical sg original mask priority
  : program UCOS2_Verify_State ((Z * bool) * TaskResumeCaller) :=
  if Z.leb 63 priority then StateRelMonad.ret ((42, false), original)
  else StateRelMonad.bind (task_resume_save_program environment critical sg original mask)
    (fun acquired => StateRelMonad.bind (task_resume_critical_code sg priority)
      (fun result => StateRelMonad.bind
        (task_resume_restore_program environment critical sg (fst acquired))
        (fun returned => StateRelMonad.ret (result, returned)))).

Definition task_resume_return_facts environment critical sg original returned mask initial prio result ready_path restored : Prop :=
  task_resume_same_caller returned original /\
  task_resume_critical_history critical sg
    (task_resume_view original).(os_execution_invocation) prio initial result ready_path restored /\
  UCOS2_state_inv sg restored /\ task_resume_clients environment critical returned /\
  task_resume_caller_source sg returned restored /\
  (match returned with
  | ResumeTaskCaller _ => ready_path = true -> restored.(SchedState).(readyList) <> []
  | ResumeGenericCaller _ => True
  end) /\
  task_resume_source_history environment critical sg original mask prio initial result ready_path returned restored.

Lemma task_resume_source_prefix_program_iff :
  forall environment critical sg original mask priority before error ready_path returned restored,
  task_resume_source_prefix_program environment critical sg original mask priority
    before ((error, ready_path), returned) restored <->
  if Z.leb 63 priority then
    error = 42 /\ ready_path = false /\ returned = original /\ restored = before
  else task_resume_source_history environment critical sg original mask priority
    before error ready_path returned restored.
Proof.
  intros environment critical sg original mask priority before error ready_path returned restored.
  unfold task_resume_source_prefix_program.
  destruct (Z.leb 63 priority).
  - change ((((error, ready_path), returned) = ((42, false), original) /\ before = restored) <->
      error = 42 /\ ready_path = false /\ returned = original /\ restored = before).
    split.
    + intros [Heq Hstate]; inversion Heq; auto.
    + intros [-> [-> [-> ->]]]; split; reflexivity.
  - split.
    + intros [[active saved] [acquired [Hsave [result [released [Hcritical
        [resumed [current [Hrestore [Hresult Hcurrent]]]]]]]]]].
      inversion Hresult; subst result resumed current.
      exists active, saved, acquired, released; auto.
    + intros [active [saved [acquired [released [Hsave [Hcritical Hrestore]]]]]].
      exists (active, saved), acquired; split; [exact Hsave|].
      exists (error, ready_path), released; split; [exact Hcritical|].
      exists returned, restored; split; [exact Hrestore|split; reflexivity].
Qed.

Lemma task_resume_source_history_prefix_program :
  forall environment critical sg original mask priority before error ready_path returned restored,
  priority < 63 ->
  task_resume_source_history environment critical sg original mask priority
    before error ready_path returned restored ->
  task_resume_source_prefix_program environment critical sg original mask priority
    before ((error, ready_path), returned) restored.
Proof.
  intros environment critical sg original mask priority before error ready_path returned restored Hrange Hhistory.
  apply task_resume_source_prefix_program_iff.
  rewrite (proj2 (Z.leb_gt _ _) Hrange); exact Hhistory.
Qed.

Lemma task_resume_source_prefix_safe_continuation :
  forall environment critical sg original mask priority
    (continuation : ((Z * bool) * TaskResumeCaller) -> program UCOS2_Verify_State Z)
    before error ready_path returned restored X,
  task_resume_source_prefix_program environment critical sg original mask priority
    before ((error, ready_path), returned) restored ->
  safeExec (fun state => state = before)
    (StateRelMonad.bind
      (task_resume_source_prefix_program environment critical sg original mask priority) continuation) X ->
  safeExec (fun state => state = restored) (continuation ((error, ready_path), returned)) X.
Proof.
  intros environment critical sg original mask priority continuation before error ready_path
    returned restored X Hprefix Hsafe.
  eapply (highstepbind_derive
    (task_resume_source_prefix_program environment critical sg original mask priority)
    continuation (fun state => state = before) ((error, ready_path), returned)
    (fun state => state = restored)).
  - intros state ->; exists restored; split; [exact Hprefix|reflexivity].
  - exact Hsafe.
Qed.

(** The only post-Restore state observation made by this C tail is the
    actual OSRunning read on the ready path. The schedule argument is the
    remaining actual call, not an arbitrary state transformer. *)
Definition task_resume_schedule_tail (schedule : program UCOS2_Verify_State unit)
  (result : Z * bool) : program UCOS2_Verify_State Z :=
  if snd result then
    StateRelMonad.bind (get' (fun state => state.(SchedState).(isRunning)))
      (fun running => if running
        then StateRelMonad.bind schedule (fun _ => StateRelMonad.ret (fst result))
        else StateRelMonad.ret (fst result))
  else StateRelMonad.ret (fst result).

Lemma task_resume_tail_nonschedule_result : forall schedule error ready_path restored,
  task_resume_requests_schedule ready_path restored = false ->
  task_resume_schedule_tail schedule (error, ready_path) restored error restored.
Proof.
  intros schedule error ready_path restored Hguard.
  unfold task_resume_schedule_tail, task_resume_requests_schedule in *; simpl in *.
  destruct ready_path; simpl in *.
  - exists false, restored; split.
    + split; [symmetry; exact Hguard|reflexivity].
    + split; reflexivity.
  - split; reflexivity.
Qed.

(** This high-step is conditional on the actual Scheduler endpoint.
    The source-aware callee post supplies it only after a real return. *)
Lemma task_resume_schedule_endpoint_safe_return :
  forall (schedule : program UCOS2_Verify_State unit) restored current (error : Z)
    (X : Z -> UCOS2_Verify_State -> Prop),
  schedule restored tt current ->
  safeExec (fun state => state = restored)
    (StateRelMonad.bind schedule (fun _ => StateRelMonad.ret error)) X ->
  safeExec (fun state => state = current) (StateRelMonad.ret error) X.
Proof.
  intros schedule restored current error X Hschedule Hsafe.
  eapply (highstepbind_derive schedule (fun _ => StateRelMonad.ret error)
    (fun state => state = restored) tt (fun state => state = current)).
  - intros state ->; exists current; split; [exact Hschedule|reflexivity].
  - exact Hsafe.
Qed.


(** Generic Scheduler entries are the already admitted ISR/locked calls.
    The protected source branch is an identity, between two distinct CPU
    intervals. Task entries instead consume the checked Scheduler history
    program and keep its actual returned context. *)
Definition task_resume_schedule_program environment critical sg caller mask
  : program UCOS2_Verify_State TaskResumeCaller :=
  match caller with
  | ResumeTaskCaller call =>
      StateRelMonad.bind (os_sched_continuation_program environment critical sg call mask)
        (fun returned => StateRelMonad.ret (ResumeTaskCaller returned))
  | ResumeGenericCaller view =>
      StateRelMonad.bind
        (task_resume_save_program environment critical sg (ResumeGenericCaller view) mask)
        (fun entered => StateRelMonad.bind
          (update (fun before after => sched_disabled_protected_identity before /\ after = before))
          (fun _ => task_resume_restore_program environment critical sg (fst entered)))
  end.

Definition task_resume_schedule_call_program environment critical sg caller mask
  : program UCOS2_Verify_State unit :=
  StateRelMonad.bind (task_resume_schedule_program environment critical sg caller mask)
    (fun _ => StateRelMonad.ret tt).

Definition task_resume_source_tail environment critical sg mask
  (result : (Z * bool) * TaskResumeCaller) : program UCOS2_Verify_State Z :=
  task_resume_schedule_tail
    (task_resume_schedule_call_program environment critical sg (snd result) mask) (fst result).

Definition task_resume_program environment critical sg caller mask priority
  : program UCOS2_Verify_State Z :=
  StateRelMonad.bind
    (task_resume_source_prefix_program environment critical sg caller mask priority)
    (task_resume_source_tail environment critical sg mask).

Definition task_resume_safe environment critical sg caller mask priority initial
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = initial)
    (task_resume_program environment critical sg caller mask priority) X.

Definition task_resume_sched_safe environment critical sg caller mask before error
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (StateRelMonad.bind (task_resume_schedule_call_program environment critical sg caller mask)
      (fun _ => StateRelMonad.ret error)) X.

Lemma task_resume_source_nonschedule_safe_return :
  forall environment critical sg original mask priority initial error ready_path returned restored X,
  task_resume_source_prefix_program environment critical sg original mask priority
    initial ((error, ready_path), returned) restored ->
  task_resume_requests_schedule ready_path restored = false ->
  task_resume_safe environment critical sg original mask priority initial X ->
  safeExec (fun state => state = restored) (StateRelMonad.ret error) X.
Proof.
  intros environment critical sg original mask priority initial error ready_path returned restored
    X Hprefix Hguard Hsafe.
  unfold task_resume_safe, task_resume_program in Hsafe.
  pose proof (task_resume_source_prefix_safe_continuation environment critical sg original mask
    priority (task_resume_source_tail environment critical sg mask) initial error ready_path
    returned restored X Hprefix Hsafe) as Htail.
  cbn [task_resume_source_tail fst snd] in Htail.
  eapply (highstependret_derive
    (task_resume_schedule_tail
      (task_resume_schedule_call_program environment critical sg returned mask) (error, ready_path))
    (fun state => state = restored) error (fun _ state => state = restored)).
  - intros state ->; exists restored; split; [|reflexivity].
    apply task_resume_tail_nonschedule_result; exact Hguard.
  - exact Htail.
Qed.

Lemma task_resume_source_schedule_safe_continuation :
  forall environment critical sg original mask priority initial error ready_path returned restored X,
  task_resume_source_prefix_program environment critical sg original mask priority
    initial ((error, ready_path), returned) restored ->
  task_resume_requests_schedule ready_path restored = true ->
  task_resume_safe environment critical sg original mask priority initial X ->
  safeExec (fun state => state = restored)
    (StateRelMonad.bind (task_resume_schedule_call_program environment critical sg returned mask)
      (fun _ => StateRelMonad.ret error)) X.
Proof.
  intros environment critical sg original mask priority initial error ready_path returned restored
    X Hprefix Hguard Hsafe.
  unfold task_resume_safe, task_resume_program in Hsafe.
  apply task_resume_requests_schedule_iff in Hguard; destruct Hguard as [-> Hrunning].
  pose proof (task_resume_source_prefix_safe_continuation environment critical sg original mask
    priority (task_resume_source_tail environment critical sg mask) initial error true
    returned restored X Hprefix Hsafe) as Htail.
  cbn [task_resume_source_tail fst snd task_resume_schedule_tail] in Htail.
  eapply (highstepbind_derive
    (get' (fun state : UCOS2_Verify_State => state.(SchedState).(isRunning)))
    (fun running => if running then
      StateRelMonad.bind (task_resume_schedule_call_program environment critical sg returned mask)
        (fun _ => StateRelMonad.ret error) else StateRelMonad.ret error)
    (fun state => state = restored) true (fun state => state = restored)).
  - intros state ->; exists restored; split;
      [split; [symmetry; exact Hrunning|reflexivity]|reflexivity].
  - exact Htail.
Qed.

Lemma task_resume_early_safe_return :
  forall environment critical sg original mask priority initial X,
  63 <= priority -> task_resume_safe environment critical sg original mask priority initial X ->
  safeExec (fun state => state = initial) (StateRelMonad.ret 42) X.
Proof.
  intros environment critical sg original mask priority initial X Hrange Hsafe.
  eapply (task_resume_source_nonschedule_safe_return environment critical sg original mask priority
    initial 42 false original initial X); [|reflexivity|exact Hsafe].
  apply task_resume_source_prefix_program_iff.
  rewrite (proj2 (Z.leb_le _ _) Hrange); auto.
Qed.

(** Both conjuncts use the same physical heap. The first retains the
    exact endpoint associated with X; the second preserves every fact of
    the existing Scheduler resource post, not merely a fresh closed world. *)
Definition task_resume_sched_refined_post environment critical saved_local sg caller mask before error
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current,
    coq_prop (task_resume_schedule_program environment critical sg caller mask before returned current /\
      safeExec (fun state => state = current) (StateRelMonad.ret error) X) &&
    (task_resume_closed environment critical saved_local sg returned mask current &&
     task_resume_sched_post environment critical saved_local sg caller mask before).

Lemma task_resume_schedule_result_safe_return :
  forall environment critical sg caller mask before returned current (error : Z)
    (X : Z -> UCOS2_Verify_State -> Prop),
  task_resume_schedule_program environment critical sg caller mask before returned current ->
  safeExec (fun state => state = before)
    (StateRelMonad.bind (task_resume_schedule_call_program environment critical sg caller mask)
      (fun _ => StateRelMonad.ret error)) X ->
  safeExec (fun state => state = current) (StateRelMonad.ret error) X.
Proof.
  intros environment critical sg caller mask before returned current error X Hprogram Hsafe.
  eapply (task_resume_schedule_endpoint_safe_return
    (task_resume_schedule_call_program environment critical sg caller mask) before current error X).
  - exists returned, current; split; [exact Hprogram|split; reflexivity].
  - exact Hsafe.
Qed.

Lemma task_resume_sched_post_safe_return :
  forall environment critical saved_local sg caller mask before error X,
  safeExec (fun state => state = before)
    (StateRelMonad.bind (task_resume_schedule_call_program environment critical sg caller mask)
      (fun _ => StateRelMonad.ret error)) X ->
  task_resume_sched_post environment critical saved_local sg caller mask before |--
  task_resume_sched_refined_post environment critical saved_local sg caller mask before error X.
Proof.
  intros environment critical saved_local sg [call|view] mask before error X Hsafe;
    unfold task_resume_sched_refined_post; cbn [task_resume_sched_post].
  - unfold os_sched_continuation_history_return_post at 1; Intros returned current.
    assert (Hprogram : task_resume_schedule_program environment critical sg
      (ResumeTaskCaller call) mask before (ResumeTaskCaller returned) current).
    { cbn [task_resume_schedule_program]; exists returned, current; split.
      - apply os_sched_continuation_program_iff; tauto.
      - split; reflexivity. }
    pose proof (task_resume_schedule_result_safe_return environment critical sg
      (ResumeTaskCaller call) mask before (ResumeTaskCaller returned) current error X
      Hprogram Hsafe) as Hreturn.
    Exists (ResumeTaskCaller returned) current.
    apply _derivable1_andp_intros; [entailer!|].
    apply _derivable1_andp_intros.
    + cbn [task_resume_closed].
      rewrite task_tcb_init_continuation_save_input_closed_world; entailer!.
    + unfold os_sched_continuation_history_return_post; Exists returned current; entailer!.
  - unfold sched_disabled_contextual_post at 1; Intros saved acquired current.
    assert (Hprogram : task_resume_schedule_program environment critical sg
      (ResumeGenericCaller view) mask before (ResumeGenericCaller view) current).
    { cbn [task_resume_schedule_program].
      exists (ResumeGenericCaller view, saved), acquired; split.
      - cbn [task_resume_save_program fst snd]; split; [reflexivity|tauto].
      - exists tt, acquired; split.
        + split; [tauto|reflexivity].
        + cbn [task_resume_restore_program fst]; split; [reflexivity|tauto]. }
    pose proof (task_resume_schedule_result_safe_return environment critical sg
      (ResumeGenericCaller view) mask before (ResumeGenericCaller view) current error X
      Hprogram Hsafe) as Hreturn.
    Exists (ResumeGenericCaller view) current.
    apply _derivable1_andp_intros; [entailer!|].
    apply _derivable1_andp_intros.
    + cbn [task_resume_closed]; entailer!.
    + unfold sched_disabled_contextual_post; Exists saved acquired current; entailer!.
Qed.

Definition task_resume_post environment critical saved_local sg original mask initial prio result
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  (coq_prop (63 <= prio /\ result = 42 /\
      safeExec (fun state => state = initial) (StateRelMonad.ret result) X) &&
    task_resume_closed environment critical saved_local sg original mask initial) ||
  (EX returned restored ready_path,
    coq_prop (0 <= prio < 63 /\ task_resume_same_caller returned original /\
      task_resume_critical_history critical sg
        (task_resume_view original).(os_execution_invocation) prio initial result ready_path restored) &&
    (if task_resume_requests_schedule ready_path restored then
       task_resume_sched_refined_post environment critical saved_local sg returned mask restored result X
     else coq_prop (safeExec (fun state => state = restored) (StateRelMonad.ret result) X) &&
       task_resume_closed environment critical saved_local sg returned mask restored)).

Lemma task_resume_return_facts_prefix_program :
  forall environment critical sg original returned mask initial priority error ready_path restored,
  priority < 63 ->
  task_resume_return_facts environment critical sg original returned mask initial
    priority error ready_path restored ->
  task_resume_source_prefix_program environment critical sg original mask priority
    initial ((error, ready_path), returned) restored.
Proof.
  intros; apply task_resume_source_history_prefix_program; [assumption|].
  unfold task_resume_return_facts in *; tauto.
Qed.

Lemma task_resume_return_facts_sched_safe :
  forall environment critical sg original returned mask initial priority error ready_path restored X,
  priority < 63 ->
  task_resume_return_facts environment critical sg original returned mask initial
    priority error ready_path restored ->
  task_resume_requests_schedule ready_path restored = true ->
  task_resume_safe environment critical sg original mask priority initial X ->
  task_resume_sched_safe environment critical sg returned mask restored error X.
Proof.
  intros environment critical sg original returned mask initial priority error ready_path restored
    X Hrange Hfacts Hguard Hsafe.
  unfold task_resume_sched_safe.
  eapply task_resume_source_schedule_safe_continuation;
    [eapply task_resume_return_facts_prefix_program; eassumption|eassumption|eassumption].
Qed.

Lemma task_resume_closed_return_post :
  forall environment critical saved_local sg original returned mask initial priority error ready_path restored X,
  0 <= priority < 63 ->
  task_resume_return_facts environment critical sg original returned mask initial
    priority error ready_path restored ->
  task_resume_requests_schedule ready_path restored = false ->
  task_resume_safe environment critical sg original mask priority initial X ->
  task_resume_closed environment critical saved_local sg returned mask restored |--
  task_resume_post environment critical saved_local sg original mask initial priority error X.
Proof.
  intros environment critical saved_local sg original returned mask initial priority error ready_path
    restored X Hrange Hfacts Hguard Hsafe.
  pose proof (task_resume_return_facts_prefix_program environment critical sg original returned mask
    initial priority error ready_path restored (proj2 Hrange) Hfacts) as Hprefix.
  pose proof (task_resume_source_nonschedule_safe_return environment critical sg original mask
    priority initial error ready_path returned restored X Hprefix Hguard Hsafe) as Hreturn.
  destruct Hfacts as [Hsame [Hhistory Hrest]].
  unfold task_resume_post; Right; Exists returned restored ready_path; rewrite Hguard; entailer!.
Qed.

Lemma task_resume_sched_return_post :
  forall environment critical saved_local sg original returned mask initial priority error ready_path restored X,
  0 <= priority < 63 ->
  task_resume_return_facts environment critical sg original returned mask initial
    priority error ready_path restored ->
  task_resume_requests_schedule ready_path restored = true ->
  task_resume_sched_safe environment critical sg returned mask restored error X ->
  task_resume_sched_post environment critical saved_local sg returned mask restored |--
  task_resume_post environment critical saved_local sg original mask initial priority error X.
Proof.
  intros environment critical saved_local sg original returned mask initial priority error ready_path
    restored X Hrange Hfacts Hguard Hsafe.
  unfold task_resume_sched_safe in Hsafe.
  sep_apply_l_atomic (task_resume_sched_post_safe_return environment critical saved_local sg
    returned mask restored error X Hsafe).
  destruct Hfacts as [Hsame [Hhistory Hrest]].
  unfold task_resume_post; Right; Exists returned restored ready_path; rewrite Hguard; entailer!.
Qed.

Definition task_resume_priority_frame sg state prio : Assertion :=
  store_prio_tbl_missing_i sg state.(TskState).(prioTbl) prio **
  UCOS2_raw_rep_missing_priority_table sg state.

Definition task_resume_node_fields : list TCBLayoutField :=
  map TCBCommonField [TCBStat; TCBDly; TCBY; TCBBitX; TCBBitY].

(** Exactly the five source-read TCB cells are open together.  The finite
    inventory below retains all other configured fields, while the task
    residual retains every other slot, list link and priority-table cell.
    The row residual omits only the row actually read/written by C. *)
Definition task_resume_node_frame sg state tid node : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec
    (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid))
    (filter (fun field =>
      if in_dec TCBLayoutField_eq_dec field task_resume_node_fields then false else true)
      (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile)))
    (task_layout_image sg node) **
  task_public_storage_without_task sg state.(TskState) tid **
  UCharArray.missing_i sg.(g_OSRdyTbl) (node.(curPrio) / 8) 0 8
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) **
  sched_physical_rep sg state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg state.

Definition task_resume_field_frame sg state tid node field : Assertion :=
  task_public_storage_without_field sg state.(TskState) tid node field **
  sched_raw_rep sg state.(TskState) state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg state.

Definition task_resume_byte sg state tid node field value : Assertion :=
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) (TCBCommonField field) (Some value) **
  task_resume_field_frame sg state tid node (TCBCommonField field).

(** Stat has been written while the ready bitmap still denotes the entry
    state.  The other fields of this same TCB remain in the real residual. *)
Definition task_resume_status_stage sg state tid node : Assertion :=
  task_resume_byte sg state tid node TCBStat (Z.land (encode_task_status node.(stat)) 247).

Definition task_resume_ready_frame sg state tid node : Assertion :=
  task_public_storage sg (glob_task_set_usedtask state.(TskState) tid (task_resume node)) **
  UCharArray.missing_i sg.(g_OSRdyTbl) (node.(curPrio) / 8) 0 8
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) **
  sched_physical_rep sg state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg state.

Definition task_resume_group (sg : StableGlobVars) state : Z :=
  encode_ready_grp state.(SchedState).(readyList) state.(TskState).
Definition task_resume_row state node : Z :=
  encode_ready_tbl_at_or state.(SchedState).(readyList) state.(TskState) (node.(curPrio) / 8).
Definition task_resume_y node : Z := node.(curPrio) / 8.
Definition task_resume_bit_x node : Z := Z.shiftl 1 (node.(curPrio) mod 8).
Definition task_resume_bit_y node : Z := Z.shiftl 1 (node.(curPrio) / 8).

Definition task_resume_running_frame environment critical saved_local sg caller mask state : Assertion :=
  match caller with
  | ResumeTaskCaller call =>
      coq_prop (UCOS2_state_inv sg state /\
        task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
      (kernel_call_execution_owned environment.(task_stack_call_external)
         environment.(task_stack_call_platform) call mask **
       critical_region_outside_without_running critical sg call.(os_sched_call_invocation) state **
       task_tcb_init_continuation_capsules environment saved_local state ** unmap_table_rep sg)
  | ResumeGenericCaller view =>
      interrupt_platform_running environment.(task_stack_call_platform)
        view.(os_execution_invocation) view.(os_execution_origin) mask **
      critical_region_outside_without_running critical sg view.(os_execution_invocation) state **
      os_execution_view_resources environment.(task_stack_call_external) view
  end.

Definition task_resume_running state : Z :=
  if state.(SchedState).(isRunning) then 1 else 0.

Lemma task_resume_generic_interval_preserves_source :
  forall critical sg view before after,
  sched_disabled_completed_clients critical view ->
  task_resume_completed_generic_returns critical view ->
  UCOS2_state_inv sg before -> task_resume_generic_source view before ->
  critical_region_interval critical sg view.(os_execution_invocation) before after ->
  UCOS2_state_inv sg after /\ task_resume_generic_source view after.
Proof.
  intros critical sg view before after Hclients Hreturns Hvalid Hsource Hinterval.
  destruct (sched_disabled_interval_preserves_context critical sg view
    view.(os_execution_invocation) before after Hclients Hvalid Hinterval)
    as [Hafter Hcontext].
  split; [exact Hafter|].
  destruct Hsource as [Hnonrunning|Hdisabled].
  - exact (Hreturns sg before after Hvalid Hinterval Hnonrunning).
  - right; eapply sched_disabled_context_rely_preserves_entry_source; eassumption.
Qed.

Lemma task_resume_generic_running_entry : forall view state,
  task_resume_generic_source view state -> state.(SchedState).(isRunning) = true ->
  sched_disabled_entry_source view state.
Proof. intros view state [Hfalse|Hdisabled] Htrue; [congruence|exact Hdisabled]. Qed.

Lemma task_resume_critical_preserves_ready_members : forall sg prio before result after slot,
  task_resume_critical sg prio before result after ->
  In slot before.(SchedState).(readyList) -> In slot after.(SchedState).(readyList).
Proof.
  intros sg prio before result after slot [_ Hstep] Hmember.
  destruct (before.(TskState).(prioTbl) prio) as [| |tid].
  - destruct Hstep as [_ ->]; exact Hmember.
  - destruct Hstep as [_ ->]; exact Hmember.
  - destruct Hstep as [node [Hnode Hstep]].
    destruct (task_is_suspended node.(stat)).
    + destruct Hstep as [_ ->].
      change (In slot (sched_resume_task sg before.(TskState) before.(SchedState) tid node).(readyList)).
      apply (proj2 (sched_resume_task_ready_membership sg before.(TskState)
        before.(SchedState) tid node slot)); left; exact Hmember.
    + destruct Hstep as [_ ->]; exact Hmember.
Qed.

Lemma task_resume_critical_ready_path_nonempty : forall sg prio before result after,
  task_resume_critical sg prio before result after -> snd result = true ->
  after.(SchedState).(readyList) <> [].
Proof.
  intros sg prio before result after [_ Hstep] Hready.
  destruct (before.(TskState).(prioTbl) prio) as [| |tid].
  - destruct Hstep as [-> _]; discriminate.
  - destruct Hstep as [-> _]; discriminate.
  - destruct Hstep as [node [Hnode Hstep]].
    destruct (task_is_suspended node.(stat)).
    + destruct Hstep as [-> ->]; simpl in Hready.
      apply task_resume_ready_test_iff in Hready.
      assert (Hmember : In tid
        (sched_resume_task sg before.(TskState) before.(SchedState) tid node).(readyList)).
      { apply (proj2 (sched_resume_task_ready_membership sg before.(TskState)
          before.(SchedState) tid node tid)); right; split; [reflexivity|exact Hready]. }
      change ((sched_resume_task sg before.(TskState) before.(SchedState) tid node).(readyList) <> []).
      intros Hempty; rewrite Hempty in Hmember; contradiction.
    + destruct Hstep as [-> _]; discriminate.
Qed.

Lemma task_resume_critical_preserves_control : forall sg prio before result after,
  task_resume_critical sg prio before result after ->
  after.(IntrState) = before.(IntrState) /\
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg prio before result after [_ Hstep].
  destruct (before.(TskState).(prioTbl) prio).
  - destruct Hstep as [_ ->]; split; reflexivity.
  - destruct Hstep as [_ ->]; split; reflexivity.
  - destruct Hstep as [node [_ Hstep]].
    destruct (task_is_suspended node.(stat)).
    + destruct Hstep as [_ ->]; split; [reflexivity|apply sched_resume_task_running_eq].
    + destruct Hstep as [_ ->]; split; reflexivity.
Qed.

Lemma task_resume_critical_preserves_generic_source : forall sg prio before result after view,
  task_resume_critical sg prio before result after ->
  task_resume_generic_source view before -> task_resume_generic_source view after.
Proof.
  intros sg prio before result after view Hstep Hsource.
  destruct (task_resume_critical_preserves_control sg prio before result after Hstep)
    as [Hintr Hrunning].
  unfold task_resume_generic_source, sched_disabled_entry_source,
    sched_disabled_isr_source in *.
  rewrite Hintr, Hrunning; exact Hsource.
Qed.

Lemma task_resume_restore_ready_nonempty : forall critical sg invocation prio before result released restored,
  kernel_sched_ready_clients critical -> UCOS2_state_inv sg before ->
  task_resume_critical sg prio before result released -> snd result = true ->
  critical_region_interval critical sg invocation released restored ->
  restored.(SchedState).(readyList) <> [].
Proof.
  intros critical sg invocation prio before result released restored Hclients Hvalid Heffect Hready Hinterval.
  eapply critical_region_interval_preserves_sched_ready.
  - exact Hclients.
  - exact Hinterval.
  - eapply task_resume_critical_preserves_validity; eassumption.
  - eapply task_resume_critical_ready_path_nonempty; eassumption.
Qed.

Lemma task_resume_running_split : forall environment critical saved_local sg caller mask state,
  task_resume_closed environment critical saved_local sg caller mask state --||--
  (sg.(g_OSRunning) # UChar |-> task_resume_running state **
   task_resume_running_frame environment critical saved_local sg caller mask state).
Proof.
  intros; destruct caller; unfold task_resume_closed, task_resume_running_frame,
    task_tcb_init_continuation_save_input, task_create_continuation_input,
    task_tcb_init_continuation_capsules, sched_disabled_closed, critical_region_outside,
    task_resume_running; split; entailer!.
Qed.

Lemma task_resume_masked_split_inv__resume_storage :
  forall environment critical saved_local sg caller saved acquired released,
  task_resume_masked environment critical saved_local sg caller saved acquired released --||--
  (UCOS2_inv sg released **
   task_resume_mask_frame environment critical saved_local sg caller saved acquired released).
Proof.
  intros; destruct caller;
    unfold task_resume_masked, task_resume_mask_frame,
      task_tcb_init_continuation_restore_input, sched_disabled_masked;
    split; entailer!.
Qed.
Lemma task_resume_priority_cell_merge__resume_storage : forall sg state priority,
  0 <= priority < 64 -> UCOS2_state_inv sg state ->
  (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->
    prio_tbl_entry_to_addr sg (state.(TskState).(prioTbl) priority) **
  task_resume_priority_frame sg state priority |-- UCOS2_inv sg state.
Proof.
  intros sg state priority Hrange Hvalid.
  unfold task_resume_priority_frame, UCOS2_inv.
  sep_apply_l_atomic (store_prio_tbl_merge_cell sg state.(TskState).(prioTbl) priority Hrange).
  rewrite UCOS2_raw_rep_priority_table_equiv; entailer!.
Qed.
Lemma task_resume_priority_in_range__resume_storage : forall sg priority,
  selected_kernel_profile sg -> 0 <= priority < 64 -> task_priority_in_range sg priority.
Proof.
  intros sg priority [Hstable _] Hrange.
  destruct Hstable as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
  unfold task_priority_in_range; lia.
Qed.
Lemma task_resume_priority_task_live__resume_storage : forall sg state priority tid,
  UCOS2_state_inv sg state -> 0 <= priority < 64 ->
  state.(TskState).(prioTbl) priority = PTTask tid ->
  exists node, state.(TskState).(inUsedTaskStates) tid = Some node.
Proof.
  intros sg state priority tid [Hprofile [_ [_ [_ [Hcross _]]]]] Hrange Hentry.
  destruct Hcross as [[_ [Htable _]] _].
  specialize (Htable priority (task_resume_priority_in_range__resume_storage sg priority Hprofile Hrange)).
  rewrite Hentry in Htable; exact Htable.
Qed.
Lemma task_resume_live_slot_positive__resume_storage : forall sg state tid node,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some node ->
  0 < task_slot_addr sg tid.
Proof.
  intros sg state tid node [Hprofile [Htasks _]] Hnode.
  destruct Htasks as [[Hpool _] _].
  assert (Hslot : task_slot_in_range sg tid).
  { apply Hpool; left; exists node; exact Hnode. }
  destruct Hprofile as [Hstable [_ [_ [_ [Hconfig _]]]]].
  assert (Hbase : 0 < sg.(g_OSTCBTbl)).
  { apply (valid_stable_address_pos sg sg.(g_OSTCBTbl)); [exact Hstable|].
    unfold stable_global_addresses; simpl; auto. }
  rewrite task_slot_addr_object_size, (task_object_size_tcb64 _ Hconfig).
  unfold task_slot_in_range in Hslot; lia.
Qed.
Lemma task_resume_entry_addr_eq_null__resume_storage : forall sg state priority,
  UCOS2_state_inv sg state -> 0 <= priority < 64 ->
  prio_tbl_entry_to_addr sg (state.(TskState).(prioTbl) priority) = 0 ->
  state.(TskState).(prioTbl) priority = PTFree.
Proof.
  intros sg state priority Hvalid Hrange Haddr.
  destruct (state.(TskState).(prioTbl) priority) as [| |tid] eqn:Hentry;
    [reflexivity|discriminate|].
  destruct (task_resume_priority_task_live__resume_storage sg state priority tid Hvalid Hrange Hentry)
    as [node Hnode].
  pose proof (task_resume_live_slot_positive__resume_storage sg state tid node Hvalid Hnode).
  change (task_slot_addr sg tid = 0) in Haddr; lia.
Qed.
Lemma task_resume_live_priority_range__resume_storage : forall sg state tid node,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some node ->
  0 <= node.(curPrio) < 64 /\ 0 <= task_resume_y node < 8.
Proof.
  intros sg state tid node [Hprofile [Htasks _]] Hnode.
  destruct Hprofile as [Hstable _].
  destruct Hstable as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
  destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hprios _]]]]]]]].
  specialize (Hprios tid node Hnode); unfold task_priority_in_range in Hprios.
  unfold task_resume_y; split; [lia|].
  split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia.
Qed.
Lemma tcb_configured_storage_split_resume_fields__resume_storage :
  forall multi profile base image,
  tcb_configured_storage_rep multi profile base image --||--
  (tcb_layout_cell multi base (TCBCommonField TCBStat) (image (TCBCommonField TCBStat)) **
   tcb_layout_cell multi base (TCBCommonField TCBDly) (image (TCBCommonField TCBDly)) **
   tcb_layout_cell multi base (TCBCommonField TCBY) (image (TCBCommonField TCBY)) **
   tcb_layout_cell multi base (TCBCommonField TCBBitX) (image (TCBCommonField TCBBitX)) **
   tcb_layout_cell multi base (TCBCommonField TCBBitY) (image (TCBCommonField TCBBitY)) **
   TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
     (filter (fun field => if in_dec TCBLayoutField_eq_dec field task_resume_node_fields
       then false else true) (tcb_configured_fields multi profile)) image).
Proof.
  intros multi profile base image.
  assert (Hreorder :
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
      (tcb_configured_fields multi profile) image =
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
      (task_resume_node_fields ++ filter
        (fun field => if in_dec TCBLayoutField_eq_dec field task_resume_node_fields
          then false else true) (tcb_configured_fields multi profile)) image).
  { unfold TaskFieldStorage.store_fields; f_equal.
    apply FunctionalExtensionality.functional_extensionality.
    intros [common| | | | | | |]; try destruct common;
      destruct multi, profile; reflexivity. }
  assert (Hnodup : NoDup (task_resume_node_fields ++ filter
    (fun field => if in_dec TCBLayoutField_eq_dec field task_resume_node_fields
      then false else true) (tcb_configured_fields multi profile))).
  { apply NoDup_app.
    - unfold task_resume_node_fields; repeat constructor; simpl; intuition discriminate.
    - apply NoDup_filter; apply tcb_configured_fields_nodup.
    - intros field Hselected Hin; apply filter_In in Hin; destruct Hin as [_ Hin].
      destruct (in_dec TCBLayoutField_eq_dec field task_resume_node_fields);
        [discriminate|contradiction]. }
  unfold tcb_configured_storage_rep; rewrite Hreorder.
  unfold task_resume_node_fields at 1; cbn [map app].
  cbn [task_resume_node_fields map app] in Hnodup.
  do 5 (rewrite (TaskFieldStorage.store_fields_cons _ _ _ _ _ _ _ Hnodup);
    apply NoDup_cons_iff in Hnodup; destruct Hnodup as [_ Hnodup]).
  split; entailer!.
Qed.
Lemma task_resume_node_split__resume_storage : forall sg state tid node,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some node ->
  UCOS2_inv sg state |--
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBStat) (Some (encode_task_status node.(stat))) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBDly) (Some node.(dly)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBY) (Some (task_resume_y node)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBBitX) (Some (task_resume_bit_x node)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBBitY) (Some (task_resume_bit_y node)) **
  sg.(g_OSRdyGrp) # UChar |-> task_resume_group sg state **
  (sg.(g_OSRdyTbl) + task_resume_y node * sizeof(UCHAR)) # UChar |-> task_resume_row state node **
  task_resume_node_frame sg state tid node.
Proof.
  intros sg state tid node Hvalid Hnode.
  pose proof (proj2 (task_resume_live_priority_range__resume_storage sg state tid node Hvalid Hnode)) as Hy.
  sep_apply_l_atomic (UCOS2_inv_open_task_storage_sched sg state); Intros.
  sep_apply_l_atomic (task_public_storage_split_task sg state.(TskState) tid node Hnode).
  unfold used_task_rep, task_slot_storage_rep.
  rewrite tcb_configured_storage_split_resume_fields__resume_storage.
  unfold sched_raw_rep.
  sep_apply_l_atomic (sched_rows_split_cell sg state.(TskState) state.(SchedState).(readyList)
    (task_resume_y node) Hy).
  unfold task_resume_node_frame, task_resume_group, task_resume_row,
    task_resume_y, task_resume_bit_x, task_resume_bit_y.
  entailer!.
Qed.
Lemma task_resume_node_merge__resume_storage : forall sg state tid node,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some node ->
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBStat) (Some (encode_task_status node.(stat))) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBDly) (Some node.(dly)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBY) (Some (task_resume_y node)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBBitX) (Some (task_resume_bit_x node)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBBitY) (Some (task_resume_bit_y node)) **
  sg.(g_OSRdyGrp) # UChar |-> task_resume_group sg state **
  (sg.(g_OSRdyTbl) + task_resume_y node * sizeof(UCHAR)) # UChar |-> task_resume_row state node **
  task_resume_node_frame sg state tid node |-- UCOS2_inv sg state.
Proof.
  intros sg state tid node Hvalid Hnode.
  pose proof (proj2 (task_resume_live_priority_range__resume_storage sg state tid node Hvalid Hnode)) as Hy.
  sep_apply_r_atomic (UCOS2_inv_merge_updated_task_storage_sched sg state state Hvalid eq_refl).
  sepcon_assoc_change.
  sep_apply_r_atomic (task_public_storage_merge_task sg state.(TskState) tid node Hnode).
  unfold used_task_rep, task_slot_storage_rep.
  rewrite tcb_configured_storage_split_resume_fields__resume_storage.
  unfold task_resume_node_frame, sched_raw_rep, task_resume_row, task_resume_y,
    task_resume_group in *.
  sepcon_assoc_change.
  sep_apply_r_atomic (sched_rows_merge_cell sg state.(TskState) state.(SchedState).(readyList)
    (node.(curPrio) / 8) Hy).
  entailer!.
Qed.
Lemma task_status_update_preserves_live_stack_observations__resume_storage :
  forall tasks tid node status,
  tasks.(inUsedTaskStates) tid = Some node ->
  forall slot updated,
  (glob_task_set_usedtask tasks tid (task_set_status node status)).(inUsedTaskStates) slot = Some updated ->
  exists old, tasks.(inUsedTaskStates) slot = Some old /\
    updated.(taskGeneration) = old.(taskGeneration) /\ updated.(tcbStkPtr) = old.(tcbStkPtr).
Proof.
  intros tasks tid node status Hnode slot updated Hupdated.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Hupdated.
  destruct (Z.eqb slot tid) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot.
    injection Hupdated as Hupdated; subst updated; exists node; auto.
  - exists updated; auto.
Qed.
Lemma task_resume_mask_frame_update__resume_storage :
  forall environment critical saved_local sg caller saved acquired state tid node,
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  task_resume_mask_frame environment critical saved_local sg caller saved acquired state |--
  task_resume_mask_frame environment critical saved_local sg caller saved acquired
    (task_resume_state sg state tid node).
Proof.
  intros environment critical saved_local sg caller saved acquired state tid node Hnode.
  destruct caller as [call|view]; [|reflexivity].
  unfold task_resume_mask_frame; Intros.
  assert (Hcoverage : task_stack_live_coverage state.(TskState) (task_stack_call_active_key call))
    by assumption.
  assert (Hafter : task_stack_live_coverage
    (task_resume_state sg state tid node).(TskState) (task_stack_call_active_key call)).
  { eapply task_stack_live_coverage_used_map_frame with (before := state.(TskState)).
    - intros slot updated Hupdated.
      destruct (task_status_update_preserves_live_stack_observations__resume_storage
        state.(TskState) tid node (task_status_resume node.(stat)) Hnode slot updated Hupdated)
        as [old [Hold [Hg Hsp]]].
      exists old; auto.
    - reflexivity.
    - exact Hcoverage. }
  assert (Hcapsules : task_tcb_init_continuation_capsules environment saved_local state |--
    task_tcb_init_continuation_capsules environment saved_local (task_resume_state sg state tid node)).
  { unfold task_tcb_init_continuation_capsules.
    apply kernel_saved_continuation_publication_spec.kernel_saved_continuation_map_reindex.
    intros key payload updated Hstack Hupdated Hg.
    destruct (task_status_update_preserves_live_stack_observations__resume_storage
      state.(TskState) tid node (task_status_resume node.(stat)) Hnode (fst key) updated Hupdated)
      as [old [Hold [Hgen Hsp]]].
    exists old; repeat split; auto. }
  sep_apply_l_atomic Hcapsules; entailer!.
Qed.
Lemma task_resume_caller_source_update__resume_storage : forall sg state tid node caller,
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  task_resume_caller_source sg caller state ->
  task_resume_caller_source sg caller (task_resume_state sg state tid node).
Proof.
  intros sg state tid node caller Hnode Hsource.
  assert (Hcurrent : (task_resume_state sg state tid node).(SchedState).(curTaskID) =
    state.(SchedState).(curTaskID)).
  { change ((sched_resume_task sg state.(TskState) state.(SchedState) tid node).(curTaskID) =
      state.(SchedState).(curTaskID)).
    unfold sched_resume_task, sched_wake_by_status.
    destruct task_resume_ready_test; [destruct task_status_is_suspended|]; reflexivity. }
  assert (Hrunning : (task_resume_state sg state tid node).(SchedState).(isRunning) =
    state.(SchedState).(isRunning)) by apply sched_resume_task_running_eq.
  destruct caller as [call|view].
  - destruct Hsource as [[Horigin [Hactive Hsource]] [Havailable Haddress]].
    unfold task_resume_caller_source, kernel_call_task_source.
    split; [|split; [exact Havailable|exact Haddress]].
    split; [exact Horigin|]; split.
    + eapply glob_task_set_usedtask_preserves_invocation_active;
        [exact Hnode|reflexivity|exact Hactive].
    + unfold task_execution_current in *.
      destruct call.(os_sched_call_origin); [exact I|rewrite Hcurrent; exact Hsource].
  - unfold task_resume_caller_source, task_resume_generic_source,
      sched_disabled_entry_source, sched_disabled_isr_source in *.
    rewrite Hrunning; exact Hsource.
Qed.
Lemma task_resume_fields_merge_updated__resume_storage : forall sg tasks tid node,
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBStat) (Some (Z.land (encode_task_status node.(stat)) 247)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBDly) (Some node.(dly)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBY) (Some (task_resume_y node)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBBitX) (Some (task_resume_bit_x node)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBBitY) (Some (task_resume_bit_y node)) **
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec
    (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid))
    (filter (fun field => if in_dec TCBLayoutField_eq_dec field task_resume_node_fields
      then false else true) (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile))) (task_layout_image sg node) **
  task_public_storage_without_task sg tasks tid |--
  task_public_storage sg (glob_task_set_usedtask tasks tid (task_resume node)).
Proof.
  intros sg tasks tid node.
  sep_apply_r_atomic (task_public_storage_merge_updated_task sg tasks tid (task_resume node)).
  unfold used_task_rep, task_slot_storage_rep.
  rewrite tcb_configured_storage_split_resume_fields__resume_storage.
  rewrite task_resume_layout_image_eq.
  unfold tcb_layout_write.
  rewrite TaskFieldStorage.store_fields_update_unlisted.
  2: { intro Hin; apply filter_In in Hin; destruct Hin as [_ Hin]; discriminate. }
  rewrite field_storage.field_update_same.
  repeat rewrite field_storage.field_update_other by discriminate.
  entailer!.
Qed.
Lemma task_resume_reserved_bits_clear__resume_storage : forall sg state tid node,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some node ->
  task_status_reserved_bits_clear false node.(stat).
Proof.
  intros sg state tid node [Hprofile [_ [_ [_ [_ [_ [Hbits _]]]]]]] Hnode.
  destruct Hprofile as [_ [_ [_ [_ [Hconfig _]]]]].
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold tcb64_configuration in Hconfig; tauto).
  specialize (Hbits tid node Hnode); rewrite Hmulti in Hbits; exact Hbits.
Qed.
Lemma task_resume_sched_storage_merge__resume_storage : forall sg state tid node,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some node ->
  sg.(g_OSRdyGrp) # UChar |->
    (if task_resume_ready_test node then Z.lor (task_resume_group sg state) (task_resume_bit_y node)
     else task_resume_group sg state) **
  (sg.(g_OSRdyTbl) + task_resume_y node * sizeof(UCHAR)) # UChar |->
    (if task_resume_ready_test node then Z.lor (task_resume_row state node) (task_resume_bit_x node)
     else task_resume_row state node) **
  UCharArray.missing_i sg.(g_OSRdyTbl) (task_resume_y node) 0 8
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) **
  sched_physical_rep sg state.(SchedState) |--
  sched_raw_rep sg (glob_task_set_usedtask state.(TskState) tid (task_resume node))
    (sched_resume_task sg state.(TskState) state.(SchedState) tid node).
Proof.
  intros sg state tid node Hvalid Hnode.
  pose proof (task_resume_reserved_bits_clear__resume_storage sg state tid node Hvalid Hnode) as Hbits.
  pose proof (proj2 (task_resume_live_priority_range__resume_storage sg state tid node Hvalid Hnode)) as Hy.
  unfold task_resume_group, task_resume_row, task_resume_y, task_resume_bit_x, task_resume_bit_y in *.
  destruct (task_resume_ready_test node) eqn:Hready.
  - assert (Hr : is_effectively_ready (task_resume node).(stat) (task_resume node).(dly) = true).
    { rewrite task_resume_effectively_ready_eq_test by exact Hbits; exact Hready. }
    unfold sched_raw_rep; rewrite sched_resume_task_physical_rep_eq.
    rewrite sched_resume_task_eq_wake_task by exact Hbits.
    destruct (sched_wake_ready_encoding sg state.(TskState) state.(SchedState) tid node
      (task_resume node) Hnode eq_refl Hr) as [Hgroup Hrows].
    rewrite Hgroup.
    sep_apply_l_atomic (sched_rows_merge_wake sg state.(TskState) state.(SchedState) tid node
      (task_resume node) Hnode eq_refl Hr Hy).
    entailer!.
  - unfold sched_resume_task; rewrite Hready.
    assert (Hrep : sched_raw_rep sg (glob_task_set_usedtask state.(TskState) tid (task_resume node))
      state.(SchedState) = sched_raw_rep sg state.(TskState) state.(SchedState)).
    { apply sched_raw_rep_priority_ext; intros slot Hin.
      eapply glob_task_set_usedtask_observation; [exact Hnode|reflexivity]. }
    rewrite Hrep; unfold sched_raw_rep.
    sep_apply_l_atomic (sched_rows_merge_cell sg state.(TskState) state.(SchedState).(readyList)
      (node.(curPrio) / 8) Hy); entailer!.
Qed.
Lemma task_resume_node_merge_updated__resume_storage : forall sg state tid node,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some node ->
  task_is_suspended node.(stat) = true ->
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBStat) (Some (Z.land (encode_task_status node.(stat)) 247)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBDly) (Some node.(dly)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBY) (Some (task_resume_y node)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBBitX) (Some (task_resume_bit_x node)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBBitY) (Some (task_resume_bit_y node)) **
  sg.(g_OSRdyGrp) # UChar |->
    (if task_resume_ready_test node then Z.lor (task_resume_group sg state) (task_resume_bit_y node)
     else task_resume_group sg state) **
  (sg.(g_OSRdyTbl) + task_resume_y node * sizeof(UCHAR)) # UChar |->
    (if task_resume_ready_test node then Z.lor (task_resume_row state node) (task_resume_bit_x node)
     else task_resume_row state node) **
  task_resume_node_frame sg state tid node |-- UCOS2_inv sg (task_resume_state sg state tid node).
Proof.
  intros sg state tid node Hvalid Hnode Hsuspended.
  pose proof (UCOS2_inv_merge_task_resume sg state tid node Hvalid Hnode Hsuspended) as Hmerge.
  cbv zeta in Hmerge.
  sep_apply_r_atomic Hmerge.
  sepcon_assoc_change.
  sep_apply_r_atomic (task_resume_fields_merge_updated__resume_storage sg state.(TskState) tid node).
  sepcon_assoc_change.
  cbn [task_resume_state replace_SchedS replace_TskS TskState SchedState].
  sep_apply_r_atomic (task_resume_sched_storage_merge__resume_storage sg state tid node Hvalid Hnode).
  unfold task_resume_node_frame.
  entailer!.
Qed.
Lemma task_resume_bitmap_bytes__resume_storage : forall sg state tid node,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some node ->
  unsigned_last_nbits (task_resume_group sg state) 8 = task_resume_group sg state /\
  unsigned_last_nbits (task_resume_row state node) 8 = task_resume_row state node /\
  unsigned_last_nbits (task_resume_bit_x node) 8 = task_resume_bit_x node /\
  unsigned_last_nbits (task_resume_bit_y node) 8 = task_resume_bit_y node.
Proof.
  intros sg state tid node Hvalid Hnode.
  pose proof (proj2 (task_resume_live_priority_range__resume_storage sg state tid node Hvalid Hnode)) as Hy.
  repeat split; apply unsigned_last_nbits_eq.
  - apply encode_ready_grp_in_range; intros slot other Hin Hother.
    exact (proj2 (task_resume_live_priority_range__resume_storage sg state slot other Hvalid Hother)).
  - apply encode_ready_tbl_or_in_range.
  - apply bitmap_single_bit_in_range; unfold task_resume_bit_x; apply Z.mod_pos_bound; lia.
  - apply bitmap_single_bit_in_range; exact Hy.
Qed.
Lemma task_resume_same_caller_trans__resume_calls_returns : forall first middle last,
  task_resume_same_caller first middle -> task_resume_same_caller middle last ->
  task_resume_same_caller first last.
Proof.
  intros [first|first] [middle|middle] [last|last];
    unfold task_resume_same_caller, task_tcb_init_stack_same_call; simpl;
    intros; try contradiction; intuition congruence.
Qed.
Lemma task_resume_same_caller_invocation_eq__resume_calls_returns : forall first second,
  task_resume_same_caller first second ->
  (task_resume_view first).(os_execution_invocation) =
    (task_resume_view second).(os_execution_invocation).
Proof.
  intros [first|first] [second|second];
    unfold task_resume_same_caller, task_tcb_init_stack_same_call, task_resume_view;
    simpl; intros; try contradiction; intuition congruence.
Qed.
Lemma task_resume_save_output_acquire__resume_calls_returns :
  forall environment critical saved_local sg original mask saved initial,
  UCOS2_state_inv sg initial -> task_resume_clients environment critical original ->
  task_resume_caller_source sg original initial ->
  task_resume_save_output environment critical saved_local sg original mask saved initial |--
  EX active acquired,
    coq_prop (task_resume_acquire_facts environment critical sg original active mask initial acquired saved) &&
    task_resume_masked environment critical saved_local sg active saved acquired acquired.
Proof.
  intros environment critical saved_local sg [original|view] mask saved initial Hvalid Hclients Hcaller.
  - cbn [task_resume_save_output].
    unfold task_tcb_init_continuation_save_post; Intros returned acquired.
    destruct H as [Hsave Hcoverage].
    pose proof Hsave as Hsource_save.
    pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
    destruct Hsave as [Htrace [Hi [Ho [Hs Hsaved]]]].
    assert (Hsame : task_tcb_init_stack_same_call returned original)
      by (unfold task_tcb_init_stack_same_call; tauto).
    destruct Hclients as [Hready Hreturns].
    destruct Hcaller as [Hsource [Havailable Haddress]].
    pose proof (proj1 (critical_region_interval_transports_resources critical sg
      original.(os_sched_call_invocation) initial acquired Hinterval Hvalid)) as Hafter.
    assert (Hreturned_source : kernel_call_task_source returned acquired).
    { apply (kernel_call_save_source_preserves_task_source environment.(task_stack_call_external)
        environment.(task_stack_call_port) critical sg original returned mask saved initial acquired
        Hvalid Hsource).
      unfold kernel_call_save_source; tauto. }
    pose proof (Hreturns sg original returned initial acquired Hvalid Hsource Havailable Hsame Htrace)
      as Hreturned_available.
    assert (Hreturned_address :
      tcb_field_address (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
        task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot)) by (rewrite Hs; exact Haddress).
    assert (Hfacts : task_resume_acquire_facts environment critical sg
      (ResumeTaskCaller original) (ResumeTaskCaller returned) mask initial acquired saved).
    { unfold task_resume_acquire_facts; cbn [task_resume_same_caller task_resume_view
        task_resume_clients task_resume_caller_source os_sched_execution_view
        task_resume_save_program fst snd]; tauto. }
    Exists (ResumeTaskCaller returned) acquired.
    cbn [task_resume_masked]; unfold task_tcb_init_continuation_restore_input; entailer!.
  - cbn [task_resume_save_output]; Intros acquired.
    destruct H as [Hinterval Hsaved].
    destruct Hclients as [Hclients Hreturns].
    destruct (task_resume_generic_interval_preserves_source critical sg view initial acquired
      Hclients Hreturns Hvalid Hcaller Hinterval) as [Hafter Hsource].
    assert (Hfacts : task_resume_acquire_facts environment critical sg
      (ResumeGenericCaller view) (ResumeGenericCaller view) mask initial acquired saved).
    { unfold task_resume_acquire_facts; cbn [task_resume_same_caller task_resume_view
        task_resume_clients task_resume_caller_source task_resume_save_program fst snd]; tauto. }
    Exists (ResumeGenericCaller view) acquired.
    cbn [task_resume_masked]; unfold sched_disabled_masked, UCOS2_inv; entailer!.
Qed.
Lemma task_resume_restore_output_return__resume_calls_returns :
  forall environment critical saved_local sg original active mask initial acquired saved
    prio result ready_path released,
  task_resume_acquire_facts environment critical sg original active mask initial acquired saved ->
  task_resume_critical_code sg prio acquired (result, ready_path) released ->
  task_resume_caller_source sg active released ->
  task_resume_restore_output environment critical saved_local sg active saved released |--
  EX returned restored,
    coq_prop (task_resume_return_facts environment critical sg original returned mask initial
      prio result ready_path restored) &&
    task_resume_closed environment critical saved_local sg returned mask restored.
Proof.
  intros environment critical saved_local sg original active mask initial acquired saved
    prio result ready_path released Hacquire Hcode Hcaller.
  destruct Hacquire as [Hsame [Hvalid [Hinitial [Hsaved [Hclients [Hacquired_source Hsave]]]]]].
  pose proof (task_resume_same_caller_invocation_eq__resume_calls_returns active original Hsame) as Hinvocation.
  destruct Hcode as [error [Hresult Heffect]].
  assert (Hreleased : UCOS2_state_inv sg released)
    by (eapply task_resume_critical_preserves_validity; eassumption).
  destruct Hsaved as [Hsaved Hmask].
  destruct active as [active|view].
  - cbn [task_resume_restore_output].
    unfold task_tcb_init_continuation_restore_post; Intros returned restored.
    destruct H as [Htrace [Hi [Ho [Hs [Hrestored Hcoverage]]]]].
    assert (Hsame_return : task_tcb_init_stack_same_call returned active)
      by (unfold task_tcb_init_stack_same_call; tauto).
    pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)) as Hinterval.
    destruct Hclients as [Hready Hreturns].
    destruct Hcaller as [Hsource [Havailable Haddress]].
    assert (Hreturned_source : kernel_call_task_source returned restored).
    { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned active restored Hsame_return)).
      exact (task_tcb_init_stack_registered_source_preserved environment.(task_stack_call_external)
        environment.(task_stack_call_port) critical sg active returned released restored
        Hreleased Hsame_return Htrace Hsource). }
    pose proof (Hreturns sg active returned released restored Hreleased Hsource Havailable
      Hsame_return Htrace) as Hreturned_available.
    assert (Hreturned_address :
      tcb_field_address (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
        task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot)) by (rewrite Hs; exact Haddress).
    assert (Hsame_final : task_resume_same_caller (ResumeTaskCaller returned) original).
    { exact (task_resume_same_caller_trans__resume_calls_returns (ResumeTaskCaller returned)
        (ResumeTaskCaller active) original Hsame_return Hsame). }
    assert (Hhistory : task_resume_critical_history critical sg
      (task_resume_view original).(os_execution_invocation) prio initial result ready_path restored).
    { exists acquired, released; split; [exact Hinitial|]. split.
      - exists error; split; assumption.
      - rewrite <- Hinvocation; exact Hinterval. }
    assert (Hnonempty : ready_path = true -> restored.(SchedState).(readyList) <> []).
    { intros Hpath; exact (task_resume_restore_ready_nonempty critical sg
        active.(os_sched_call_invocation) prio acquired (error, ready_path) released restored
        Hready Hvalid Heffect Hpath Hinterval). }
    assert (Hsource_history : task_resume_source_history environment critical sg original mask
      prio initial result ready_path (ResumeTaskCaller returned) restored).
    { exists (ResumeTaskCaller active), saved, acquired, released; split; [exact Hsave|].
      split; [exists error; split; assumption|].
      cbn [task_resume_restore_program]; split; assumption. }
    assert (Hfacts : task_resume_return_facts environment critical sg original
      (ResumeTaskCaller returned) mask initial prio result ready_path restored).
    { unfold task_resume_return_facts; cbn [task_resume_clients task_resume_caller_source]; tauto. }
    Exists (ResumeTaskCaller returned) restored.
    rewrite Hmask.
    cbn [task_resume_closed]; unfold task_tcb_init_continuation_save_input,
      task_create_continuation_input, task_tcb_init_continuation_capsules; entailer!.
  - cbn [task_resume_restore_output]; Intros restored.
    rename H into Hinterval.
    destruct Hclients as [Hclients Hreturns].
    destruct (task_resume_generic_interval_preserves_source critical sg view released restored
      Hclients Hreturns Hreleased Hcaller Hinterval) as [Hrestored Hsource].
    assert (Hhistory : task_resume_critical_history critical sg
      (task_resume_view original).(os_execution_invocation) prio initial result ready_path restored).
    { exists acquired, released; split; [exact Hinitial|]. split.
      - exists error; split; assumption.
      - rewrite <- Hinvocation; exact Hinterval. }
    assert (Hsource_history : task_resume_source_history environment critical sg original mask
      prio initial result ready_path (ResumeGenericCaller view) restored).
    { exists (ResumeGenericCaller view), saved, acquired, released; split; [exact Hsave|].
      split; [exists error; split; assumption|].
      cbn [task_resume_restore_program]; split; [reflexivity|exact Hinterval]. }
    assert (Hfacts : task_resume_return_facts environment critical sg original
      (ResumeGenericCaller view) mask initial prio result ready_path restored).
    { unfold task_resume_return_facts; cbn [task_resume_clients task_resume_caller_source]; tauto. }
    Exists (ResumeGenericCaller view) restored; rewrite Hmask; entailer!.
Qed.
Lemma task_resume_closed_sched_pre__resume_calls_returns :
  forall environment critical saved_local sg original returned mask initial prio restored,
  task_resume_return_facts environment critical sg original returned mask initial prio 0 true restored ->
  restored.(SchedState).(isRunning) = true ->
  task_resume_closed environment critical saved_local sg returned mask restored |--
  task_resume_sched_pre environment critical saved_local sg returned mask restored.
Proof.
  intros environment critical saved_local sg original [returned|view] mask initial prio restored Hfacts Hrunning.
  - destruct Hfacts as [_ [_ [Hvalid [[Hready Hreturns] [Hsource [Hnonempty Hhistory]]]]]].
    destruct Hsource as [Hsource [Havailable Haddress]].
    assert (Hcut : os_sched_call_cut sg returned restored).
    { eapply os_sched_call_cut_from_source; eauto. }
    cbn [task_resume_closed task_resume_sched_pre].
    unfold os_sched_continuation_call_pre, os_sched_continuation_pre.
    rewrite <- task_tcb_init_continuation_save_input_closed_world; entailer!.
  - destruct Hfacts as [_ [_ [Hvalid [[Hclients Hreturns] [Hsource Hrest]]]]].
    pose proof (task_resume_generic_running_entry view restored Hsource Hrunning) as Hentry.
    cbn [task_resume_closed task_resume_sched_pre]; entailer!.
Qed.
