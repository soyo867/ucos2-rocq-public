Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Require Export Ucos2Verify.lib.kernel_program_storage.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_wait_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_unowned_history_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Import UCOS2_C_Rules.
Import Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** None adds neither a platform-environment witness nor a stack owner to
    the existing early-error/nonblocking domain. Some carries the existing
    Task world, not a new representation or a future-safety promise. *)
Definition sem_pend_without_stack : option TaskStackCallEnvironment := None.

Definition sem_pend_owned_stack (environment : TaskStackCallEnvironment) := Some environment.

Definition sem_pend_optional_stack_resources external platform
  (environment : option TaskStackCallEnvironment) call state : Assertion :=
  match environment with
  | Some owned =>
      coq_prop (owned.(task_stack_call_external) = external /\
        owned.(task_stack_call_platform) = platform /\
        task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
      task_tcb_init_stack_capsules owned state
  | None => emp
  end.

Definition sem_pend_runtime_nonblocking critical sg call
  (environment : option TaskStackCallEnvironment) pevent before eid : Prop :=
  environment = None ->
  sem_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_nonblocking_acquire critical sg call before eid.

Definition sem_pend_stack_save_input external platform environment critical sg call mask state : Assertion :=
  mutex_query_closed platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) mask state **
  os_sched_context_resources external call **
  sem_pend_optional_stack_resources external platform environment call state.

(** The owned arm deliberately does NOT turn a segmented IRQ deposit,
    registry, take and return into the old flat critical-region interval.
    It retains exactly the source-independent observations shared by the
    actual returning Save branches. The None projection keeps the ordinary
    nonblocking acquisition facts, while allowing an actually saved stack
    image. Its source producer must construct that image from the same
    save/restore path; same_call alone is not an execution certificate. *)
Definition sem_pend_stack_save_observation critical sg original returned
  (environment : option TaskStackCallEnvironment) mask saved before acquired : Prop :=
  kernel_stack_call_same_call returned original /\ interrupt_saved_value mask saved /\
  (environment = None ->
    sem_pend_save_facts critical sg original.(os_sched_call_invocation) mask saved before acquired).

Definition sem_pend_stack_save_output external platform environment critical sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (sem_pend_stack_save_observation critical sg original returned environment mask saved before acquired) &&
    (critical_region_masked platform critical sg original.(os_sched_call_invocation)
       original.(os_sched_call_origin) saved acquired **
     os_sched_context_resources external returned ** UCOS2_inv sg acquired **
     sem_pend_optional_stack_resources external platform environment returned acquired).

Lemma sem_pend_stack_save_input_owned : forall environment critical sg call mask state,
  sem_pend_stack_save_input environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical sg call mask state --||--
  task_tcb_init_stack_save_input environment critical sg call mask state.
Proof.
  intros; unfold sem_pend_stack_save_input, sem_pend_optional_stack_resources,
    task_tcb_init_stack_save_input, mutex_query_closed, kernel_call_execution_owned.
  split; entailer!.
Qed.

Lemma sem_pend_stack_save_input_unowned : forall external platform critical sg call mask state,
  sem_pend_stack_save_input external platform None critical sg call mask state --||--
  mutex_query_closed platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) mask state ** os_sched_context_resources external call.
Proof. intros; unfold sem_pend_stack_save_input, sem_pend_optional_stack_resources; split; entailer!. Qed.

(** This consumes a real current world and its actual history together.
    No property of that history is assumed, erased into a flat interval or
    installed as an additional platform law. The generic history owner is
    shared with Task/Scheduler; this lemma only projects its resources. *)
Lemma sem_pend_stack_save_output_history : forall environment critical sg history original mask saved before,
  kernel_stack_call_history_save_post environment.(task_stack_call_continuations)
    UCOS2_inv critical sg (task_stack_call_active_key original) history original mask saved before |--
  sem_pend_stack_save_output environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical sg original mask saved before.
Proof.
  intros; unfold kernel_stack_call_history_save_post; Intros returned acquired.
  assert (Hsame : kernel_stack_call_same_call returned original) by tauto.
  destruct Hsame as [Hinv [Horigin Hstack]].
  unfold kernel_stack_call_masked, kernel_stack_inv; Intros.
  unfold sem_pend_stack_save_output; Exists returned acquired.
  unfold sem_pend_stack_save_observation, kernel_stack_call_same_call,
    sem_pend_optional_stack_resources, task_tcb_init_stack_capsules,
    task_stack_call_active_key.
  rewrite Hinv, Horigin, Hstack; entailer!; discriminate.
Qed.

(** The Task modular post provides this resource projection through its
    same-call and saved-value observations. Its call-preservation fact
    is not converted into a flat execution history. *)
Lemma sem_pend_stack_save_output_owned : forall environment critical sg original mask saved before,
  task_tcb_init_stack_save_output environment critical sg original mask saved before |--
  sem_pend_stack_save_output environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical sg original mask saved before.
Proof.
  intros; unfold task_tcb_init_stack_save_output; Intros returned acquired.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  destruct Hsame as [Hinv [Horigin Hstack]].
  unfold sem_pend_stack_save_output; Exists returned acquired.
  unfold sem_pend_stack_save_observation, kernel_stack_call_same_call,
    sem_pend_optional_stack_resources, task_tcb_init_stack_capsules.
  rewrite Hinv, Horigin; entailer!; discriminate.
Qed.

Lemma sem_pend_stack_save_output_unowned : forall external platform critical sg original mask saved before acquired,
  sem_pend_save_facts critical sg original.(os_sched_call_invocation) mask saved before acquired ->
  critical_region_masked platform critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) saved acquired **
  UCOS2_inv sg acquired ** os_sched_context_resources external original |--
  sem_pend_stack_save_output external platform None critical sg original mask saved before.
Proof.
  intros * Hfacts; pose proof Hfacts as [_ [_ [Hsaved _]]].
  unfold sem_pend_stack_save_output; Exists original acquired.
  unfold sem_pend_optional_stack_resources, sem_pend_stack_save_observation,
    kernel_stack_call_same_call; entailer!.
Qed.

Lemma sem_pend_zero_count_runtime_owned : forall critical sg call environment pevent before eid acquired current,
  sem_pend_runtime_nonblocking critical sg call environment pevent before eid ->
  sem_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  critical_region_interval critical sg call.(os_sched_call_invocation) before acquired ->
  mutex_query_lookup acquired eid current -> current.(eventType) = OS_EVENT_TYPE_SEM ->
  encode_event_cnt_value current = 0 -> exists owned, environment = Some owned.
Proof.
  intros * Hprotocol Hclear Hinterval Hlookup Htype Hzero.
  destruct environment as [owned|]; [exists owned; reflexivity|].
  specialize (Hprotocol eq_refl Hclear acquired current Hinterval Hlookup Htype); lia.
Qed.

Lemma sem_pend_runtime_nonblocking_early_error : forall critical sg call pevent before eid error,
  sem_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some error ->
  sem_pend_runtime_nonblocking critical sg call None pevent before eid.
Proof. intros * Herror _ Hclear; congruence. Qed.

Lemma sem_pend_runtime_nonblocking_acquire : forall critical sg call pevent before eid,
  sem_pend_nonblocking_acquire critical sg call before eid ->
  sem_pend_runtime_nonblocking critical sg call None pevent before eid.
Proof. intros * Hprotocol _ _; exact Hprotocol. Qed.

(** These views retain the current owner through Restore. The owned branch
    is a projection of the adopted Task interface, not a new ready/wake law.
    The None branch remains the legacy resource domain. Total interrupted
    CPU coverage is still an implementation obligation of the callee. *)
Definition sem_pend_stack_restore_input external platform environment critical sg
  call mask saved acquired released : Assertion :=
  coq_prop (interrupt_saved_value mask saved) &&
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved acquired **
   os_sched_context_resources external call ** UCOS2_inv sg released **
   sem_pend_optional_stack_resources external platform environment call released).

Definition sem_pend_stack_restore_observation sg original returned
  (environment : option TaskStackCallEnvironment) released current : Prop :=
  kernel_stack_call_same_call returned original /\
  (UCOS2_state_inv sg released -> kernel_call_task_source original released ->
    kernel_call_task_source returned current).

Definition sem_pend_stack_restore_output external platform environment critical sg
  original mask released : Assertion :=
  EX returned current,
    coq_prop (sem_pend_stack_restore_observation sg original returned environment released current) &&
    (mutex_query_closed platform critical sg original.(os_sched_call_invocation)
       original.(os_sched_call_origin) mask current **
     os_sched_context_resources external returned **
     sem_pend_optional_stack_resources external platform environment returned current).

(** Both branches record returning source execution. None uses the same
    external/platform parameters as its real resource owner and retains
    the actual saved descriptor and the selected physical client history.
    It introduces no Task environment or stronger public input domain. *)
Definition sem_pend_optional_restore_history external platform environment critical sg original checkpoint returned current : Prop :=
  match environment with
  | Some owned => sem_pend_restore_call_history owned critical sg original checkpoint returned current
  | None => sem_pend_unowned_return_history external platform critical sg
      original checkpoint returned current
  end.

Definition sem_pend_stack_restore_source_output external platform environment critical sg
  original mask released : Assertion :=
  EX returned current,
    coq_prop (sem_pend_optional_restore_history external platform environment critical sg original released returned current /\
      sem_pend_stack_restore_observation sg original returned environment released current) &&
    (mutex_query_closed platform critical sg original.(os_sched_call_invocation)
       original.(os_sched_call_origin) mask current **
     os_sched_context_resources external returned **
     sem_pend_optional_stack_resources external platform environment returned current).

Lemma sem_pend_stack_restore_source_output_forget : forall external platform environment critical sg
  original mask released,
  sem_pend_stack_restore_source_output external platform environment critical sg original mask released |--
  sem_pend_stack_restore_output external platform environment critical sg original mask released.
Proof.
  intros; unfold sem_pend_stack_restore_source_output; Intros returned current.
  unfold sem_pend_stack_restore_output; Exists returned current; entailer!.
Qed.

(** This constructor requires the actual history and current strong
    world together. Task's weaker modular post alone is not a producer. *)
Lemma sem_pend_stack_restore_source_output_current : forall environment critical sg
  original returned mask released current,
  kernel_call_restore_history environment critical sg original released returned current ->
  (UCOS2_state_inv sg released -> kernel_call_task_source original released ->
    kernel_call_task_source returned current) ->
  kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv sg
    (task_stack_call_active_key original) returned mask current |--
  sem_pend_stack_restore_source_output environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical sg original mask released **
    unmap_table_rep sg.
Proof.
  intros * Hhistory Hsource.
  pose proof (kernel_call_restore_history_same_call environment critical sg original released returned current
    Hhistory) as Hsame.
  assert (Hcall_history : sem_pend_restore_call_history environment critical sg original released returned current)
    by (left; exact Hhistory).
  pose proof Hsame as [Hi [Ho Hs]].
  unfold kernel_stack_call_closed, kernel_stack_inv; rewrite kernel_program_inv_split_unmap; Intros.
  unfold sem_pend_stack_restore_source_output; Exists returned current.
  rewrite mutex_query_closed_equiv.
  unfold sem_pend_optional_restore_history, sem_pend_stack_restore_observation,
    sem_pend_optional_stack_resources, task_tcb_init_stack_capsules,
    kernel_call_execution_owned, task_stack_call_active_key.
  rewrite Hi, Ho; entailer!; try discriminate; try tauto.
Qed.

(** Concrete MSR/BX producer for the uninterrupted returning branch.
    Interrupted branches must establish their own actual history and
    returned world; the generic weak Task post cannot replace them. *)
Lemma sem_pend_stack_restore_uninterrupted_source_output : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg call saved acquired released cursor before written middle final_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (task_tcb_init_stack_restore_input environment critical sg call saved acquired released **
    unmap_table_rep sg ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  (sem_pend_stack_restore_source_output environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical sg call
      (armv7a_irq_fiq_mask saved) released ** unmap_table_rep sg ** frame) after.
Proof.
  intros environment critical arch restore sg call saved acquired released cursor before written middle
    final_cursor after frame Hr0 Hmask Hpre Hprefix Hsuffix.
  destruct (sem_pend_wait_first_restore_source environment critical arch restore sg call saved acquired released
    cursor before written middle final_cursor after frame Hr0 Hmask Hpre Hprefix Hsuffix)
    as [Hrun [Hreturn [Hhistory Hafter]]].
  split; [exact Hrun|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (sem_pend_stack_restore_source_output_current environment critical sg call call
      (armv7a_irq_fiq_mask saved) released released Hhistory ltac:(auto)); entailer!. }
  exact (Hclose after Hafter).
Qed.

Lemma sem_pend_stack_restore_source_output_unowned : forall external platform critical sg
  call returned mask released current,
  sem_pend_unowned_restore_history external platform critical sg call released returned current ->
  mutex_query_closed platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) mask current ** os_sched_context_resources external returned |--
  sem_pend_stack_restore_source_output external platform None critical sg call mask released.
Proof.
  intros * Hhistory.
  pose proof (sem_pend_unowned_restore_history_same_call _ _ _ _ _ _ _ _ Hhistory) as Hsame.
  pose proof (sem_pend_unowned_restore_history_preserves_task_source _ _ _ _ _ _ _ _ Hhistory)
    as Hsource.
  unfold sem_pend_stack_restore_source_output; Exists returned current.
  unfold sem_pend_optional_restore_history, sem_pend_stack_restore_observation,
    sem_pend_optional_stack_resources, sem_pend_unowned_return_history; entailer!.
Qed.

Lemma sem_pend_stack_restore_input_owned : forall environment critical sg call mask saved acquired released,
  interrupt_saved_value mask saved ->
  sem_pend_stack_restore_input environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical sg call mask saved acquired released --||--
  task_tcb_init_stack_restore_input environment critical sg call saved acquired released.
Proof.
  intros * Hsaved; unfold sem_pend_stack_restore_input, sem_pend_optional_stack_resources,
    task_tcb_init_stack_restore_input; split; entailer!.
Qed.

Lemma sem_pend_stack_restore_output_owned : forall environment critical sg original mask saved released,
  interrupt_saved_value mask saved ->
  task_tcb_init_stack_restore_output environment critical sg original saved released |--
  sem_pend_stack_restore_output environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical sg original mask released.
Proof.
  intros * Hsaved.
  sep_apply_l_atomic (task_tcb_init_stack_restore_output_reacquire environment critical sg
    original saved mask released Hsaved); Intros returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  assert (Hsource : UCOS2_state_inv sg released -> kernel_call_task_source original released ->
    kernel_call_task_source returned current).
  { intros Hvalid Horiginal.
    rewrite (task_tcb_init_stack_same_call_source_iff returned original current Hsame).
    assert (Hpreserved : task_tcb_init_stack_source_preserved original released current) by tauto.
    exact (Hpreserved Horiginal). }
  destruct Hsame as [Hi [Ho Hs]].
  unfold sem_pend_stack_restore_output; Exists returned current.
  unfold sem_pend_stack_restore_observation, kernel_stack_call_same_call,
    task_tcb_init_stack_save_input, kernel_call_execution_owned, mutex_query_closed,
    sem_pend_optional_stack_resources.
  rewrite Hi, Ho; entailer!.
Qed.

Lemma sem_pend_stack_restore_output_unowned : forall external platform critical sg call mask state,
  mutex_query_closed platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) mask state ** os_sched_context_resources external call |--
  sem_pend_stack_restore_output external platform None critical sg call mask state.
Proof.
  intros; unfold sem_pend_stack_restore_output; Exists call state.
  unfold sem_pend_stack_restore_observation, kernel_stack_call_same_call,
    sem_pend_optional_stack_resources; entailer!.
Qed.

Lemma sem_pend_optional_stack_same_call : forall external platform environment first second state,
  kernel_stack_call_same_call first second ->
  sem_pend_optional_stack_resources external platform environment first state =
    sem_pend_optional_stack_resources external platform environment second state.
Proof.
  intros external platform [environment|] first second state [Hi [Ho Hs]]; [|reflexivity].
  unfold sem_pend_optional_stack_resources, task_stack_call_active_key; rewrite Ho; reflexivity.
Qed.

Lemma sem_pend_optional_stack_count_update : forall external platform environment call state eid event count,
  sem_pend_optional_stack_resources external platform environment call
    (sem_count_update_state state eid event count) =
  sem_pend_optional_stack_resources external platform environment call state.
Proof. intros external platform [environment|]; reflexivity. Qed.

Lemma sem_pend_stack_restore_sched_input : forall external platform environment critical sg
  original mask released,
  sem_pend_stack_restore_output external platform (Some environment) critical sg original mask released **
    unmap_table_rep sg |--
  EX returned current,
    coq_prop (sem_pend_stack_restore_observation sg original returned (Some environment) released current) &&
    os_sched_stack_pre environment kernel_program_inv sg returned mask current.
Proof.
  intros; unfold sem_pend_stack_restore_output; Intros returned current.
  assert (Hsame : kernel_stack_call_same_call returned original) by
    (unfold sem_pend_stack_restore_observation in *; tauto).
  destruct Hsame as [Hi [Ho Hs]].
  unfold sem_pend_optional_stack_resources; Intros.
  assert (Hexternal : environment.(task_stack_call_external) = external) by tauto.
  assert (Hplatform : environment.(task_stack_call_platform) = platform) by tauto.
  Exists returned current; unfold os_sched_stack_pre.
  rewrite <- task_tcb_init_stack_save_input_closed_world.
  unfold task_tcb_init_stack_save_input, kernel_call_execution_owned, mutex_query_closed.
  rewrite Hexternal, Hplatform, Hi, Ho; entailer!.
Qed.

(** The former relation ends at the count/cleanup checkpoint. The runtime
    relation below retains that exact effect and adds the actual final
    Restore history. Its continuation observes the returned current world.
    Initial acquisition and waiting histories remain explicit obligations
    of the checkpoint relation until their separate source migration. *)
Definition sem_pend_runtime_program external platform environment critical sg context pevent timeout
  : program UCOS2_Verify_State Z :=
  fun before error current =>
    (sem_pend_c_program external critical sg context pevent timeout before error before /\
      (pevent = 0 \/ exists eid, pevent = event_addr sg eid /\
        sem_pend_context_error (event_slot_type_value before.(EventState) eid)
          before.(IntrState).(intNesting) before.(IntrState).(lockNesting) <> None) /\
      current = before) \/
    (exists checkpoint call returned eid,
      sem_pend_checkpoint_result environment critical sg context pevent timeout before error checkpoint /\
      pevent <> 0 /\ pevent = event_addr sg eid /\
      sem_pend_context_error (event_slot_type_value before.(EventState) eid)
        before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None /\
      kernel_stack_call_same_call call context /\
      sem_pend_optional_restore_history external platform environment critical sg call checkpoint returned current).

Definition sem_pend_stack_call_post external platform environment critical sg context mask
  pevent timeout perr before X : Assertion :=
  EX after returned error,
    coq_prop (sem_pend_runtime_program external platform environment critical sg context pevent timeout before error after /\
      safeExec (LastSeen after) (StateRelMonad.ret error) X /\ kernel_stack_call_same_call returned context) **
    (perr # UChar |-> error **
     sem_post_return_resources external platform critical sg context returned mask after **
     sem_pend_optional_stack_resources external platform environment returned after).

Lemma sem_pend_stack_call_post_from_result : forall external platform environment critical sg context returned mask
  pevent timeout perr before after error X,
  sem_pend_runtime_program external platform environment critical sg context pevent timeout before error after ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_pend_runtime_program external platform environment critical sg context pevent timeout)) sem_query_observe_error) X ->
  kernel_stack_call_same_call returned context ->
  TT ** mutex_query_closed platform critical sg context.(os_sched_call_invocation) context.(os_sched_call_origin) mask after **
  os_sched_context_resources external returned ** unmap_table_rep sg ** perr # UChar |-> error **
  sem_pend_optional_stack_resources external platform environment returned after |--
  sem_pend_stack_call_post external platform environment critical sg context mask pevent timeout perr before X.
Proof.
  intros * Hresult Hexec Hsame.
  pose proof (sem_query_safe_return _ _ _ _ _ Hresult Hexec) as Hsafe.
  unfold sem_pend_stack_call_post; Exists after returned error.
  unfold mutex_query_closed, sem_post_return_resources; entailer!.
Qed.

Lemma sem_pend_stack_call_post_from_restore : forall external platform environment critical sg
  context call mask pevent timeout perr before checkpoint error eid X,
  sem_pend_checkpoint_result environment critical sg context pevent timeout before error checkpoint ->
  pevent <> 0 -> pevent = event_addr sg eid ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  kernel_stack_call_same_call call context ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_pend_runtime_program external platform environment critical sg context pevent timeout))
      sem_query_observe_error) X ->
  TT ** sem_pend_stack_restore_source_output external platform environment critical sg call mask checkpoint **
    unmap_table_rep sg ** perr # UChar |-> error |--
  sem_pend_stack_call_post external platform environment critical sg context mask pevent timeout perr before X.
Proof.
  intros * Hresult Hnonzero Haddress Hclear Hcall Hexec.
  unfold sem_pend_stack_restore_source_output; Intros returned current.
  assert (Hhistory : sem_pend_optional_restore_history external platform environment critical sg call checkpoint returned current)
    by tauto.
  assert (Hreturned : kernel_stack_call_same_call returned call) by
    (unfold sem_pend_stack_restore_observation in *; tauto).
  assert (Hruntime : sem_pend_runtime_program external platform environment critical sg context pevent timeout
    before error current).
  { right; exists checkpoint, call, returned, eid; tauto. }
  pose proof (sem_query_safe_return _ _ _ _ _ Hruntime Hexec) as Hsafe.
  assert (Hsame : kernel_stack_call_same_call returned context).
  { unfold kernel_stack_call_same_call in *; intuition congruence. }
  pose proof Hcall as [Hi [Ho Hs]].
  unfold sem_pend_stack_call_post; Exists current returned error.
  unfold sem_post_return_resources, mutex_query_closed; rewrite Hi, Ho; entailer!.
Qed.

Lemma sem_pend_stack_wait_restore_input : forall external platform environment critical sg context returned
  mask saved before observed entry eid current tid old timeout,
  sem_pend_observed_wait_origin environment critical sg context returned mask saved before observed entry eid current tid old ->
  sem_pend_stack_save_observation critical sg context returned environment mask saved before entry ->
  critical_region_masked platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) saved entry ** os_sched_context_resources external returned **
  sem_pend_wait_call_post sg entry eid current tid old timeout **
  sem_pend_optional_stack_resources external platform environment returned entry |--
  coq_prop (let waiting := event_pend_state sg entry eid current tid old PendSem timeout in
    sem_pend_observed_wait_history environment critical sg context mask before observed eid timeout waiting /\
    UCOS2_state_inv sg waiting /\ kernel_stack_call_same_call returned context /\
    kernel_call_task_source returned waiting) &&
  sem_pend_stack_restore_input external platform environment critical sg returned mask saved entry
    (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros external platform environment critical sg context returned mask saved before observed
    entry eid current tid old timeout Horigin [Hsame [Hsaved Hnone]].
  pose proof Horigin as [_ [Hentry [_ [Hsource Hcache]]]].
  pose proof (sem_pend_observed_wait_origin_history environment critical sg context returned mask saved before observed entry
    eid current tid old timeout Horigin) as Hhistory.
  assert (Hreturned : kernel_call_task_source returned entry).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned context entry Hsame)); exact Hsource. }
  pose proof (sem_pend_wait_preserves_call_source sg returned entry eid current tid old timeout
    Hentry Hreturned Hcache) as [Hvalid [Hwaiting Hwaiting_cache]].
  destruct environment as [owned|].
  - unfold sem_pend_optional_stack_resources; Intros.
    assert (He : owned.(task_stack_call_external) = external) by tauto.
    assert (Hp : owned.(task_stack_call_platform) = platform) by tauto.
    assert (Hcoverage : task_stack_live_coverage entry.(TskState) (task_stack_call_active_key returned)) by tauto.
    pose proof Hsame as [Hi [Ho Hs]].
    rewrite <- Hi, <- Ho, <- He, <- Hp.
    unfold task_tcb_init_stack_capsules.
    sep_apply_l_atomic (sem_pend_wait_call_stack_merge_source _ _ _ owned.(task_stack_call_continuations)
      critical sg (task_stack_call_active_key returned) returned saved entry eid current tid old timeout
      Hentry Hreturned Hcache Hcoverage).
    unfold sem_pend_stack_restore_input, sem_pend_optional_stack_resources,
      task_tcb_init_stack_capsules, kernel_stack_call_masked, kernel_stack_inv; entailer!.
  - unfold sem_pend_optional_stack_resources.
    sep_apply_l_atomic (sem_pend_wait_call_merge sg entry eid current tid old timeout Hentry).
    pose proof Hsame as [Hi [Ho Hs]].
    unfold sem_pend_stack_restore_input, sem_pend_optional_stack_resources; rewrite Hi, Ho; entailer!.
Qed.

(** Optional dispatch only: Some is exactly the adopted Scheduler world;
    None has no Scheduler call. Early errors and positive-count calls do
    not consume this assertion. No stage or future-acquisition property
    has been added to either branch. *)
Definition sem_pend_stack_sched_input external platform environment sg call mask state : Assertion :=
  match environment with
  | Some owned =>
      coq_prop (owned.(task_stack_call_external) = external /\
        owned.(task_stack_call_platform) = platform) &&
      os_sched_stack_pre owned kernel_program_inv sg call mask state
  | None => coq_prop False && emp
  end.

Definition sem_pend_stack_sched_output external platform environment sg call mask state : Assertion :=
  match environment with
  | Some owned =>
      coq_prop (owned.(task_stack_call_external) = external /\
        owned.(task_stack_call_platform) = platform) &&
      os_sched_stack_return_post owned kernel_program_inv sg call mask state
  | None => coq_prop False && emp
  end.

Lemma sem_pend_stack_sched_return_save_input : forall external platform environment critical sg
  original mask waiting,
  kernel_call_task_source original waiting ->
  sem_pend_stack_sched_output external platform environment sg original mask waiting |--
  EX returned current,
    coq_prop (kernel_stack_call_same_call returned original /\
      kernel_call_task_source returned current /\ UCOS2_state_inv sg current) &&
    (sem_pend_stack_save_input external platform environment critical sg returned mask current **
      unmap_table_rep sg).
Proof.
  intros external platform [owned|] critical sg original mask waiting Hsource;
    unfold sem_pend_stack_sched_output; Intros; [|contradiction].
  assert (He : owned.(task_stack_call_external) = external) by tauto.
  assert (Hp : owned.(task_stack_call_platform) = platform) by tauto.
  sep_apply_l_atomic (sem_pend_sched_return_save_input owned critical sg original mask waiting Hsource).
  Intros returned current; Exists returned current; rewrite <- He, <- Hp.
  rewrite sem_pend_stack_save_input_owned; entailer!.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_stack_equiv_spec.
Require Import Ucos2Verify.lib.task_storage.
Import TaskStateDef.

(** Current canonical interfaces retain the caller-supplied saved locals.
    The stack interfaces above remain historical empty-local compatibility
    views. The pure admission, wait and returning histories are shared;
    there is no second state model or invariant. In particular None keeps
    its original early-error/nonblocking domain and has no parked owner. *)
Definition sem_pend_optional_continuation_resources external platform
  (environment : option TaskStackCallEnvironment) saved_local call state : Assertion :=
  match environment with
  | Some owned =>
      coq_prop (owned.(task_stack_call_external) = external /\
        owned.(task_stack_call_platform) = platform /\
        task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
      task_tcb_init_continuation_capsules owned saved_local state
  | None => emp
  end.

Definition sem_pend_continuation_save_input external platform environment critical saved_local
  sg call mask state : Assertion :=
  mutex_query_closed platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) mask state **
  os_sched_context_resources external call **
  sem_pend_optional_continuation_resources external platform environment saved_local call state.

Definition sem_pend_continuation_save_output external platform environment critical saved_local
  sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (sem_pend_stack_save_observation critical sg original returned environment mask saved before acquired) &&
    (critical_region_masked platform critical sg original.(os_sched_call_invocation)
       original.(os_sched_call_origin) saved acquired **
     os_sched_context_resources external returned ** UCOS2_inv sg acquired **
     sem_pend_optional_continuation_resources external platform environment saved_local returned acquired).

Definition sem_pend_continuation_restore_input external platform environment critical saved_local
  sg call mask saved acquired released : Assertion :=
  coq_prop (interrupt_saved_value mask saved) &&
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved acquired **
   os_sched_context_resources external call ** UCOS2_inv sg released **
   sem_pend_optional_continuation_resources external platform environment saved_local call released).

Definition sem_pend_continuation_restore_output external platform environment critical saved_local
  sg original mask released : Assertion :=
  EX returned current,
    coq_prop (sem_pend_stack_restore_observation sg original returned environment released current) &&
    (mutex_query_closed platform critical sg original.(os_sched_call_invocation)
       original.(os_sched_call_origin) mask current **
     os_sched_context_resources external returned **
     sem_pend_optional_continuation_resources external platform environment saved_local returned current).

Definition sem_pend_continuation_restore_source_output external platform environment critical saved_local
  sg original mask released : Assertion :=
  EX returned current,
    coq_prop (sem_pend_optional_restore_history external platform environment critical sg original released returned current /\
      sem_pend_stack_restore_observation sg original returned environment released current) &&
    (mutex_query_closed platform critical sg original.(os_sched_call_invocation)
       original.(os_sched_call_origin) mask current **
     os_sched_context_resources external returned **
     sem_pend_optional_continuation_resources external platform environment saved_local returned current).

Definition sem_pend_continuation_call_post external platform environment critical saved_local
  sg context mask pevent timeout perr before X : Assertion :=
  EX after returned error,
    coq_prop (sem_pend_runtime_program external platform environment critical sg context pevent timeout before error after /\
      safeExec (LastSeen after) (StateRelMonad.ret error) X /\ kernel_stack_call_same_call returned context) **
    (perr # UChar |-> error **
     sem_post_return_resources external platform critical sg context returned mask after **
     sem_pend_optional_continuation_resources external platform environment saved_local returned after).

Definition sem_pend_continuation_sched_input external platform environment saved_local sg call mask state : Assertion :=
  match environment with
  | Some owned =>
      coq_prop (owned.(task_stack_call_external) = external /\
        owned.(task_stack_call_platform) = platform) &&
      os_sched_continuation_pre owned saved_local kernel_program_inv sg call mask state
  | None => coq_prop False && emp
  end.

Definition sem_pend_continuation_sched_output external platform environment saved_local sg call mask state : Assertion :=
  match environment with
  | Some owned =>
      coq_prop (owned.(task_stack_call_external) = external /\
        owned.(task_stack_call_platform) = platform) &&
      os_sched_continuation_return_post owned saved_local kernel_program_inv sg call mask state
  | None => coq_prop False && emp
  end.

(** At emp this is exactly the earlier optional owner, in both directions.
    Destructing the existing descriptor's call only simplifies Task's
    None=emp wrapper; it introduces neither a saved owner nor a new field. *)
Lemma sem_pend_optional_continuation_resources_emp_equiv :
  forall external platform environment call state,
  sem_pend_optional_continuation_resources external platform environment (fun _ => emp) call state --||--
  sem_pend_optional_stack_resources external platform environment call state.
Proof.
  intros external platform [owned|] call state;
    unfold sem_pend_optional_continuation_resources, sem_pend_optional_stack_resources;
    [|split; reflexivity].
  assert (Hmap : task_tcb_init_continuation_capsules owned (fun _ => emp) state --||--
    task_tcb_init_stack_capsules owned state).
  { assert (Hlocal : task_create_continuation_local (fun _ => emp) = (fun _ => emp)).
    { apply functional_extensionality; intros descriptor.
      unfold task_create_continuation_local.
      destruct descriptor.(armv7a_continuation_call); reflexivity. }
    unfold task_tcb_init_continuation_capsules, task_tcb_init_stack_capsules.
    rewrite Hlocal; apply kernel_saved_continuation_map_emp_equiv. }
  split; Intros; [sep_apply_l_atomic (proj1 Hmap)|sep_apply_l_atomic (proj2 Hmap)]; entailer!.
Qed.

Lemma sem_pend_continuation_save_input_owned : forall environment critical saved_local sg call mask state,
  sem_pend_continuation_save_input environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask state --||--
  task_tcb_init_continuation_save_input environment critical saved_local sg call mask state.
Proof.
  intros; unfold sem_pend_continuation_save_input, sem_pend_optional_continuation_resources,
    task_tcb_init_continuation_save_input, task_create_continuation_input,
    task_tcb_init_continuation_capsules, mutex_query_closed, kernel_call_execution_owned.
  split; entailer!.
Qed.

Lemma sem_pend_continuation_call_post_emp_equiv :
  forall external platform environment critical sg context mask pevent timeout perr before X,
  sem_pend_continuation_call_post external platform environment critical (fun _ => emp)
    sg context mask pevent timeout perr before X --||--
  sem_pend_stack_call_post external platform environment critical sg context mask
    pevent timeout perr before X.
Proof.
  intros; unfold sem_pend_continuation_call_post, sem_pend_stack_call_post.
  split; Intros after returned error; Exists after returned error.
  - sep_apply_l_atomic (proj1 (sem_pend_optional_continuation_resources_emp_equiv
      external platform environment returned after)); entailer!.
  - sep_apply_l_atomic (proj2 (sem_pend_optional_continuation_resources_emp_equiv
      external platform environment returned after)); entailer!.
Qed.

Lemma sem_pend_continuation_restore_input_owned : forall environment critical saved_local
  sg call mask saved acquired released,
  interrupt_saved_value mask saved ->
  sem_pend_continuation_restore_input environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical saved_local
    sg call mask saved acquired released --||--
  task_tcb_init_continuation_restore_input environment critical saved_local sg call saved acquired released.
Proof.
  intros * Hsaved; unfold sem_pend_continuation_restore_input, sem_pend_optional_continuation_resources,
    task_tcb_init_continuation_restore_input; split; entailer!.
Qed.

Lemma sem_pend_optional_continuation_same_call : forall external platform environment saved_local first second state,
  kernel_stack_call_same_call first second ->
  sem_pend_optional_continuation_resources external platform environment saved_local first state =
    sem_pend_optional_continuation_resources external platform environment saved_local second state.
Proof.
  intros external platform [environment|] saved_local first second state [Hi [Ho Hs]]; [|reflexivity].
  unfold sem_pend_optional_continuation_resources, task_stack_call_active_key; rewrite Ho; reflexivity.
Qed.

Lemma sem_pend_optional_continuation_count_update :
  forall external platform environment saved_local call state eid event count,
  sem_pend_optional_continuation_resources external platform environment saved_local call
    (sem_count_update_state state eid event count) =
  sem_pend_optional_continuation_resources external platform environment saved_local call state.
Proof. intros external platform [environment|]; reflexivity. Qed.


Lemma sem_pend_continuation_save_output_owned : forall environment critical saved_local sg original mask saved before,
  task_tcb_init_continuation_save_output environment critical saved_local sg original mask saved before |--
  sem_pend_continuation_save_output environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg original mask saved before.
Proof.
  intros; unfold task_tcb_init_continuation_save_output; Intros returned acquired.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  destruct Hsame as [Hinv [Horigin Hstack]].
  unfold sem_pend_continuation_save_output; Exists returned acquired.
  unfold sem_pend_stack_save_observation, kernel_stack_call_same_call,
    sem_pend_optional_continuation_resources, task_tcb_init_continuation_capsules.
  rewrite Hinv, Horigin; entailer!; discriminate.
Qed.

Lemma sem_pend_continuation_restore_output_owned : forall environment critical saved_local sg original mask saved released,
  interrupt_saved_value mask saved ->
  task_tcb_init_continuation_restore_output environment critical saved_local sg original saved released |--
  sem_pend_continuation_restore_output environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical saved_local sg original mask released.
Proof.
  intros * Hsaved.
  sep_apply_l_atomic (task_tcb_init_continuation_restore_output_reacquire environment critical saved_local sg
    original saved mask released Hsaved); Intros returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  assert (Hsource : UCOS2_state_inv sg released -> kernel_call_task_source original released ->
    kernel_call_task_source returned current).
  { intros Hvalid Horiginal.
    rewrite (task_tcb_init_stack_same_call_source_iff returned original current Hsame).
    assert (Hpreserved : task_tcb_init_stack_source_preserved original released current) by tauto.
    exact (Hpreserved Horiginal). }
  destruct Hsame as [Hi [Ho Hs]].
  unfold sem_pend_continuation_restore_output; Exists returned current.
  unfold sem_pend_stack_restore_observation, kernel_stack_call_same_call,
    task_tcb_init_continuation_save_input, task_create_continuation_input, kernel_call_execution_owned, mutex_query_closed,
    sem_pend_optional_continuation_resources.
  rewrite Hi, Ho; entailer!.
Qed.

Lemma sem_pend_continuation_restore_source_output_forget : forall external platform environment critical saved_local sg
  original mask released,
  sem_pend_continuation_restore_source_output external platform environment critical saved_local sg original mask released |--
  sem_pend_continuation_restore_output external platform environment critical saved_local sg original mask released.
Proof.
  intros; unfold sem_pend_continuation_restore_source_output; Intros returned current.
  unfold sem_pend_continuation_restore_output; Exists returned current; entailer!.
Qed.

Lemma sem_pend_continuation_call_post_from_result : forall external platform environment critical saved_local sg context returned mask
  pevent timeout perr before after error X,
  sem_pend_runtime_program external platform environment critical sg context pevent timeout before error after ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_pend_runtime_program external platform environment critical sg context pevent timeout)) sem_query_observe_error) X ->
  kernel_stack_call_same_call returned context ->
  TT ** mutex_query_closed platform critical sg context.(os_sched_call_invocation) context.(os_sched_call_origin) mask after **
  os_sched_context_resources external returned ** unmap_table_rep sg ** perr # UChar |-> error **
  sem_pend_optional_continuation_resources external platform environment saved_local returned after |--
  sem_pend_continuation_call_post external platform environment critical saved_local sg context mask pevent timeout perr before X.
Proof.
  intros * Hresult Hexec Hsame.
  pose proof (sem_query_safe_return _ _ _ _ _ Hresult Hexec) as Hsafe.
  unfold sem_pend_continuation_call_post; Exists after returned error.
  unfold mutex_query_closed, sem_post_return_resources; entailer!.
Qed.

Lemma sem_pend_continuation_call_post_from_restore : forall external platform environment critical saved_local sg
  context call mask pevent timeout perr before checkpoint error eid X,
  sem_pend_checkpoint_result environment critical sg context pevent timeout before error checkpoint ->
  pevent <> 0 -> pevent = event_addr sg eid ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  kernel_stack_call_same_call call context ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_pend_runtime_program external platform environment critical sg context pevent timeout))
      sem_query_observe_error) X ->
  TT ** sem_pend_continuation_restore_source_output external platform environment critical saved_local sg call mask checkpoint **
    unmap_table_rep sg ** perr # UChar |-> error |--
  sem_pend_continuation_call_post external platform environment critical saved_local sg context mask pevent timeout perr before X.
Proof.
  intros * Hresult Hnonzero Haddress Hclear Hcall Hexec.
  unfold sem_pend_continuation_restore_source_output; Intros returned current.
  assert (Hhistory : sem_pend_optional_restore_history external platform environment critical sg call checkpoint returned current)
    by tauto.
  assert (Hreturned : kernel_stack_call_same_call returned call) by
    (unfold sem_pend_stack_restore_observation in *; tauto).
  assert (Hruntime : sem_pend_runtime_program external platform environment critical sg context pevent timeout
    before error current).
  { right; exists checkpoint, call, returned, eid; tauto. }
  pose proof (sem_query_safe_return _ _ _ _ _ Hruntime Hexec) as Hsafe.
  assert (Hsame : kernel_stack_call_same_call returned context).
  { unfold kernel_stack_call_same_call in *; intuition congruence. }
  pose proof Hcall as [Hi [Ho Hs]].
  unfold sem_pend_continuation_call_post; Exists current returned error.
  unfold sem_post_return_resources, mutex_query_closed; rewrite Hi, Ho; entailer!.
Qed.

Lemma sem_pend_continuation_wait_restore_input : forall external platform environment critical saved_local sg context returned
  mask saved before observed entry eid current tid old timeout,
  sem_pend_observed_wait_origin environment critical sg context returned mask saved before observed entry eid current tid old ->
  sem_pend_stack_save_observation critical sg context returned environment mask saved before entry ->
  critical_region_masked platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) saved entry ** os_sched_context_resources external returned **
  sem_pend_wait_call_post sg entry eid current tid old timeout **
  sem_pend_optional_continuation_resources external platform environment saved_local returned entry |--
  coq_prop (let waiting := event_pend_state sg entry eid current tid old PendSem timeout in
    sem_pend_observed_wait_history environment critical sg context mask before observed eid timeout waiting /\
    UCOS2_state_inv sg waiting /\ kernel_stack_call_same_call returned context /\
    kernel_call_task_source returned waiting) &&
  sem_pend_continuation_restore_input external platform environment critical saved_local sg returned mask saved entry
    (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros external platform environment critical saved_local sg context returned mask saved before observed
    entry eid current tid old timeout Horigin [Hsame [Hsaved Hnone]].
  pose proof Horigin as [_ [Hentry [_ [Hsource Hcache]]]].
  pose proof (sem_pend_observed_wait_origin_history environment critical sg context returned mask saved before observed entry
    eid current tid old timeout Horigin) as Hhistory.
  assert (Hreturned : kernel_call_task_source returned entry).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned context entry Hsame)); exact Hsource. }
  pose proof (sem_pend_wait_preserves_call_source sg returned entry eid current tid old timeout
    Hentry Hreturned Hcache) as [Hvalid [Hwaiting Hwaiting_cache]].
  destruct environment as [owned|].
  - unfold sem_pend_optional_continuation_resources; Intros.
    assert (He : owned.(task_stack_call_external) = external) by tauto.
    assert (Hp : owned.(task_stack_call_platform) = platform) by tauto.
    assert (Hcoverage : task_stack_live_coverage entry.(TskState) (task_stack_call_active_key returned)) by tauto.
    pose proof Hsame as [Hi [Ho Hs]].
    rewrite <- Hi, <- Ho, <- He, <- Hp.
    unfold task_tcb_init_continuation_capsules.
    sep_apply_l_atomic (sem_pend_wait_call_continuation_merge_source _ _ _ owned.(task_stack_call_continuations) (task_create_continuation_local saved_local)
      critical sg (task_stack_call_active_key returned) returned saved entry eid current tid old timeout
      Hentry Hreturned Hcache Hcoverage).
    unfold sem_pend_continuation_restore_input, sem_pend_optional_continuation_resources,
      task_tcb_init_continuation_capsules, kernel_continuation_call_masked, kernel_continuation_inv; entailer!.
  - unfold sem_pend_optional_continuation_resources.
    sep_apply_l_atomic (sem_pend_wait_call_merge sg entry eid current tid old timeout Hentry).
    pose proof Hsame as [Hi [Ho Hs]].
    unfold sem_pend_continuation_restore_input, sem_pend_optional_continuation_resources; rewrite Hi, Ho; entailer!.
Qed.

Lemma sem_pend_continuation_restore_source_output_current : forall environment critical saved_local sg
  original returned mask released current,
  sem_pend_restore_call_history environment critical sg original released returned current ->
  (UCOS2_state_inv sg released -> kernel_call_task_source original released ->
    kernel_call_task_source returned current) ->
  kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv (task_create_continuation_local saved_local) sg
    (task_stack_call_active_key original) returned mask current |--
  sem_pend_continuation_restore_source_output environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical saved_local sg original mask released **
    unmap_table_rep sg.
Proof.
  intros * Hhistory Hsource.
  pose proof (sem_pend_restore_call_history_same_call environment critical sg original released returned current
    Hhistory) as Hsame.
  pose proof Hsame as [Hi [Ho Hs]].
  unfold kernel_continuation_call_closed, kernel_continuation_inv; rewrite kernel_program_inv_split_unmap; Intros.
  unfold sem_pend_continuation_restore_source_output; Exists returned current.
  rewrite mutex_query_closed_equiv.
  unfold sem_pend_optional_restore_history, sem_pend_stack_restore_observation,
    sem_pend_optional_continuation_resources, task_tcb_init_continuation_capsules,
    kernel_call_execution_owned, task_stack_call_active_key.
  rewrite Hi, Ho; entailer!; try discriminate; try tauto.
Qed.

Lemma sem_pend_optional_continuation_task_update :
  forall external platform environment saved_local call state tid old current,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  current.(taskGeneration) = old.(taskGeneration) -> current.(tcbStkPtr) = old.(tcbStkPtr) ->
  sem_pend_optional_continuation_resources external platform environment saved_local call state |--
  sem_pend_optional_continuation_resources external platform environment saved_local call
    (replace_TskS (glob_task_set_usedtask state.(TskState) tid current) state).
Proof.
  intros external platform [owned|] saved_local call state tid old current Hold Hgen Hsp;
    [|apply derivable1_refl].
  unfold sem_pend_optional_continuation_resources; Intros.
  assert (Hcoverage : task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) by tauto.
  unfold task_tcb_init_continuation_capsules.
  sep_apply_l_atomic (sem_pend_task_field_update_continuations _ _ _ owned.(task_stack_call_continuations)
    (task_create_continuation_local saved_local) state.(TskState)
    (task_stack_call_active_key call) tid old current Hold Hgen Hsp Hcoverage).
  cbn [replace_TskS TskState glob_task_set_usedtask parkedTaskStacks]; entailer!.
Qed.

Lemma sem_pend_continuation_save_input_unowned : forall external platform critical saved_local sg call mask state,
  sem_pend_continuation_save_input external platform None critical saved_local sg call mask state --||--
  sem_pend_stack_save_input external platform None critical sg call mask state.
Proof.
  intros; unfold sem_pend_continuation_save_input, sem_pend_stack_save_input,
    sem_pend_optional_continuation_resources, sem_pend_optional_stack_resources; split; reflexivity.
Qed.

Lemma sem_pend_continuation_save_output_unowned : forall external platform critical saved_local sg call mask saved state,
  sem_pend_continuation_save_output external platform None critical saved_local sg call mask saved state --||--
  sem_pend_stack_save_output external platform None critical sg call mask saved state.
Proof.
  intros; unfold sem_pend_continuation_save_output, sem_pend_stack_save_output,
    sem_pend_optional_continuation_resources, sem_pend_optional_stack_resources; split; reflexivity.
Qed.

Lemma sem_pend_continuation_restore_source_output_unowned :
  forall external platform critical saved_local sg call mask state,
  sem_pend_continuation_restore_source_output external platform None critical saved_local sg call mask state --||--
  sem_pend_stack_restore_source_output external platform None critical sg call mask state.
Proof.
  intros; unfold sem_pend_continuation_restore_source_output, sem_pend_stack_restore_source_output,
    sem_pend_optional_continuation_resources, sem_pend_optional_stack_resources; split; reflexivity.
Qed.
