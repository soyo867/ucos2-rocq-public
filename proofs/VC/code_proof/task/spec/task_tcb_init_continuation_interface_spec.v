Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_storage Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_world_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Continuation-parametric counterparts of the existing TCBInit C-call
    interfaces. Pure call identity, history, publication and result facts
    retain their existing definitions. Only the owned map is changed;
    no field or law is added to the caller environment. *)

Definition task_tcb_init_continuation_call_pre environment critical saved_local sg region args task_return
  lower upper initial_name invocation origin mask initial call : Assertion :=
  coq_prop (call.(os_sched_call_invocation) = invocation /\ call.(os_sched_call_origin) = origin /\
    task_stack_live_coverage initial.(TskState) (task_stack_call_active_key call)) &&
  (task_tcb_init_stack_pre environment.(task_stack_call_platform) critical sg region args task_return
     lower upper initial_name invocation origin mask initial **
   os_sched_context_resources environment.(task_stack_call_external) call **
   task_tcb_init_continuation_capsules environment saved_local initial).

(** The public Save input is definitionally the TaskCreate caller's current
    continuation world; it does not add a second resource owner. *)
Definition task_tcb_init_continuation_save_input environment critical saved_local sg call mask state : Assertion :=
  task_create_continuation_input environment critical saved_local sg call mask state.

Definition task_tcb_init_continuation_save_output environment critical saved_local sg call mask saved state : Assertion :=
  EX returned acquired,
    coq_prop (task_tcb_init_stack_same_call returned call /\
      task_tcb_init_call_preserved sg call.(os_sched_call_invocation) state acquired /\
      (UCOS2_state_inv sg state -> task_tcb_init_stack_source_preserved call state acquired) /\
      interrupt_saved_value mask saved /\
      task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key returned)) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved acquired **
     task_tcb_init_stack_context environment returned ** UCOS2_inv sg acquired **
     task_tcb_init_continuation_capsules environment saved_local acquired).

Definition task_tcb_init_continuation_restore_input environment critical saved_local sg call saved acquired released : Assertion :=
  coq_prop (task_stack_live_coverage released.(TskState) (task_stack_call_active_key call)) &&
  (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired **
  os_sched_context_resources environment.(task_stack_call_external) call ** UCOS2_inv sg released **
  task_tcb_init_continuation_capsules environment saved_local released).

Definition task_tcb_init_continuation_restore_output environment critical saved_local sg call saved released : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned call /\
      task_tcb_init_call_preserved sg call.(os_sched_call_invocation) released current /\
      (UCOS2_state_inv sg released ->
       task_tcb_init_stack_source_preserved call released current)) &&
    task_tcb_init_continuation_save_input environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current.

Lemma task_tcb_init_continuation_registered_save_output :
  forall environment critical saved_local sg original mask saved before,
  task_tcb_init_continuation_save_post environment critical saved_local sg original mask saved before |--
  task_tcb_init_continuation_save_output environment critical saved_local sg original mask saved before.
Proof.
  intros environment critical saved_local sg original mask saved before.
  unfold task_tcb_init_continuation_save_post; Intros returned acquired.
  assert (Hsource : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask saved before acquired) by tauto.
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsource) as Hinterval.
  pose proof (task_tcb_init_interval_preserves_call _ _ _ _ _ Hinterval) as Hpreserved.
  destruct Hsource as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hsame : task_tcb_init_stack_same_call returned original) by (repeat split; assumption).
  assert (Hordinary : UCOS2_state_inv sg before ->
    task_tcb_init_stack_source_preserved original before acquired).
  { intro Hvalid; eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  unfold task_tcb_init_continuation_save_output; Exists returned acquired.
  unfold task_tcb_init_stack_context, task_tcb_init_continuation_capsules; entailer!.
Qed.

Lemma task_tcb_init_continuation_registered_restore_output :
  forall environment critical saved_local sg original saved released,
  task_tcb_init_continuation_restore_post environment critical saved_local sg original (armv7a_irq_fiq_mask saved) released |--
  task_tcb_init_continuation_restore_output environment critical saved_local sg original saved released.
Proof.
  intros environment critical saved_local sg original saved released.
  unfold task_tcb_init_continuation_restore_post; Intros returned current.
  assert (Htrace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    released false returned.(os_sched_call_origin) current) by tauto.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by (repeat split; tauto).
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)) as Hinterval.
  pose proof (task_tcb_init_interval_preserves_call _ _ _ _ _ Hinterval) as Hpreserved.
  assert (Hordinary : UCOS2_state_inv sg released ->
    task_tcb_init_stack_source_preserved original released current).
  { intro Hvalid; eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  unfold task_tcb_init_continuation_restore_output; Exists returned current.
  unfold task_tcb_init_continuation_save_input, task_tcb_init_continuation_capsules, task_create_continuation_input; entailer!.
Qed.

(** The public callable resource is exactly the existing source-owned
    runtime world, not an additional record or platform promise. *)

Lemma task_tcb_init_continuation_save_input_closed_world :
  forall environment critical saved_local sg call mask state,
  task_tcb_init_continuation_save_input environment critical saved_local sg call mask state **
    unmap_table_rep sg --||--
  kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv
    (task_create_continuation_local saved_local) sg (task_stack_call_active_key call) call mask state.
Proof.
  intros; apply task_create_continuation_input_closed_world.
Qed.

Lemma task_tcb_init_continuation_restore_input_masked_world : forall environment critical saved_local sg call saved acquired state,
  task_tcb_init_continuation_restore_input environment critical saved_local sg call saved acquired state **
    unmap_table_rep sg --||--
  kernel_continuation_call_masked environment.(task_stack_call_continuations) kernel_program_inv
    (task_create_continuation_local saved_local) critical sg
    (task_stack_call_active_key call) call saved acquired state.
Proof.
  intros; unfold task_tcb_init_continuation_restore_input, task_tcb_init_continuation_capsules,
    kernel_continuation_call_masked, kernel_continuation_inv.
  rewrite kernel_program_inv_split_unmap; split; entailer!.
Qed.

Definition task_tcb_init_continuation_call_return_post environment critical saved_local sg original mask released : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_stack_return_preserved original released current) &&
    task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current.

Lemma task_tcb_init_continuation_restore_post_returns_call :
  forall environment critical saved_local sg original mask released,
  UCOS2_state_inv sg released ->
  task_tcb_init_continuation_restore_post environment critical saved_local sg original mask released |--
  task_tcb_init_continuation_call_return_post environment critical saved_local sg original mask released.
Proof.
  intros environment critical saved_local sg original mask released Hvalid.
  unfold task_tcb_init_continuation_restore_post; Intros returned current.
  assert (Htrace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    released false returned.(os_sched_call_origin) current) by tauto.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by (repeat split; tauto).
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)) as Hinterval.
  destruct (critical_region_interval_transports_resources critical sg original.(os_sched_call_invocation)
    released current Hinterval Hvalid) as [_ [Hframe Hactive]].
  pose proof (task_tcb_init_stack_registered_source_preserved _ _ _ _ _ _ _ _
    Hvalid Hsame Htrace) as Hsource.
  unfold task_tcb_init_continuation_call_return_post; Exists returned current.
  unfold task_tcb_init_continuation_save_input, task_tcb_init_continuation_capsules, task_tcb_init_stack_return_preserved, task_create_continuation_input; entailer!.
Qed.

Definition task_tcb_init_continuation_call_post environment critical saved_local sg region args task_return
  lower upper initial_name invocation origin mask initial original result : Assertion :=
  EX released,
    coq_prop (task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
      invocation origin initial result released) &&
    coq_prop (UCOS2_state_inv sg released /\
      task_tcb_init_stack_source_preserved original initial released) &&
    (task_tcb_init_continuation_call_return_post environment critical saved_local sg original mask released **
     task_tcb_init_stack_buffer_result region args task_return lower upper result).

Lemma task_tcb_init_continuation_restore_output_returns_call :
  forall environment critical saved_local sg original saved mask released,
  interrupt_saved_value mask saved ->
  UCOS2_state_inv sg released ->
  task_tcb_init_continuation_restore_output environment critical saved_local sg original saved released |--
  task_tcb_init_continuation_call_return_post environment critical saved_local sg original mask released.
Proof.
  intros environment critical saved_local sg original saved mask released Hsaved Hvalid.
  unfold task_tcb_init_continuation_restore_output; Intros returned current.
  assert (Hpreserved : task_tcb_init_call_preserved sg original.(os_sched_call_invocation)
    released current) by tauto.
  destruct (Hpreserved Hvalid) as [_ [Hframe [Hactive Hname]]].
  assert (Hsource : task_tcb_init_stack_source_preserved original released current) by tauto.
  unfold task_tcb_init_continuation_call_return_post; Exists returned current.
  rewrite (proj2 Hsaved); entailer!.
  unfold task_tcb_init_stack_return_preserved; split; [exact Hframe|].
  split; [apply Hactive|exact Hsource].
Qed.

Lemma task_tcb_init_continuation_call_pre_first_save :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial call,
  task_tcb_init_continuation_call_pre environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial call |--
  coq_prop (task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    invocation origin initial) &&
  (task_tcb_init_continuation_save_input environment critical saved_local sg call mask initial **
   task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper)).
Proof.
  intros; unfold task_tcb_init_continuation_call_pre, task_tcb_init_stack_pre, task_tcb_init_pre.
  Intros.
  assert (Hcall : call.(os_sched_call_invocation) = invocation /\ call.(os_sched_call_origin) = origin)
    by tauto.
  assert (Hentry : task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    invocation origin initial) by assumption.
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input,
    kernel_call_execution_owned, task_tcb_init_continuation_capsules.
  destruct Hcall as [-> ->]; entailer!; exact (proj1 Hentry).
Qed.

Lemma task_tcb_init_continuation_save_output_entry :
  forall environment critical saved_local sg args original mask saved before,
  task_tcb_init_entry sg args original.(os_sched_call_invocation) original.(os_sched_call_origin) before ->
  task_tcb_init_continuation_save_output environment critical saved_local sg original mask saved before |--
  EX returned acquired,
    coq_prop (task_tcb_init_entry sg args original.(os_sched_call_invocation)
      original.(os_sched_call_origin) acquired /\
      task_tcb_init_stack_same_call returned original /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before acquired /\
      task_tcb_init_stack_source_preserved original before acquired /\
      interrupt_saved_value mask saved /\
      task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key returned)) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       original.(os_sched_call_invocation) original.(os_sched_call_origin) saved acquired **
     task_tcb_init_stack_context environment returned ** UCOS2_raw_rep sg acquired **
     task_tcb_init_continuation_capsules environment saved_local acquired).
Proof.
intros environment critical saved_local sg args original mask saved before Hentry.
  unfold task_tcb_init_continuation_save_output; Intros returned acquired.
  assert (Hhistory : task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before acquired)
    by tauto.
  pose proof (task_tcb_init_call_preserves_entry sg args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) before acquired Hentry Hhistory) as Hacquired.
  pose proof (proj1 Hentry) as Hbefore.
  assert (Hpreserved : task_tcb_init_stack_source_preserved original before acquired) by
    tauto.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  destruct Hsame as [Hinvocation [Horigin Hstack]].
  Exists returned acquired.
  unfold task_tcb_init_stack_same_call, task_tcb_init_stack_context, task_tcb_init_continuation_capsules, UCOS2_inv.
  rewrite Hinvocation, Horigin; entailer!.
Qed.

Lemma task_tcb_init_continuation_restore_output_reacquire :
  forall environment critical saved_local sg original saved mask released,
  interrupt_saved_value mask saved ->
  task_tcb_init_continuation_restore_output environment critical saved_local sg original saved released |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
      (UCOS2_state_inv sg released ->
       task_tcb_init_stack_source_preserved original released current)) &&
    task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current.
Proof.
intros environment critical saved_local sg original saved mask released Hsaved.
  unfold task_tcb_init_continuation_restore_output; Intros returned current.
  Exists returned current; rewrite (proj2 Hsaved); entailer!.
Qed.

Lemma task_tcb_init_continuation_restore_output_caller :
  forall environment critical saved_local sg returned original saved released,
  task_tcb_init_stack_same_call returned original ->
  task_tcb_init_continuation_restore_output environment critical saved_local sg returned saved released |--
  task_tcb_init_continuation_restore_output environment critical saved_local sg original saved released.
Proof.
intros environment critical saved_local sg returned original saved released [Hinvocation [Horigin Hstack]].
  unfold task_tcb_init_continuation_restore_output; Intros last current.
  Exists last current.
  unfold task_tcb_init_stack_same_call, task_tcb_init_stack_source_preserved,
    kernel_call_task_source in *.
  rewrite Hinvocation, Horigin, Hstack in *; entailer!; intuition congruence.
Qed.

(** The second Save starts at the actual previous Restore return, not at
    the released detach snapshot.  Join the two real intervals only after
    Save has returned on the same invocation. *)

Lemma task_tcb_init_continuation_save_output_commit :
  forall environment critical saved_local sg args original checkpoint_call mask saved
    first slot rest image checkpoint,
  task_tcb_init_stack_same_call checkpoint_call original ->
  task_tcb_init_entry sg args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) first ->
  task_tcb_init_detach_observation args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) first slot rest image ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation)
    (task_tcb_init_detached_state args original.(os_sched_call_invocation)
      original.(os_sched_call_origin) first slot rest image) checkpoint ->
  task_tcb_init_continuation_save_output environment critical saved_local sg checkpoint_call mask saved checkpoint |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_commit_binding args original.(os_sched_call_invocation)
        original.(os_sched_call_origin) first current slot /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation)
        (task_tcb_init_detached_state args original.(os_sched_call_invocation)
          original.(os_sched_call_origin) first slot rest image) current /\
      task_tcb_init_stack_source_preserved checkpoint_call checkpoint current /\
      interrupt_saved_value mask saved /\ UCOS2_state_inv sg current /\
      task_stack_live_coverage current.(TskState) (task_stack_call_active_key returned)) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       original.(os_sched_call_invocation) original.(os_sched_call_origin) saved current **
     task_tcb_init_stack_context environment returned ** UCOS2_raw_rep sg current **
     task_tcb_init_continuation_capsules environment saved_local current).
Proof.
intros environment critical saved_local sg args original checkpoint_call mask saved first slot rest image checkpoint
    [Hinvocation [Horigin Hstack]] Hentry Hdetach Hprevious.
  unfold task_tcb_init_continuation_save_output; Intros returned current.
  assert (Hlast : task_tcb_init_call_preserved sg checkpoint_call.(os_sched_call_invocation)
    checkpoint current) by tauto.
  assert (Hcheckpoint : UCOS2_state_inv sg checkpoint).
  { apply (proj1 (Hprevious (task_tcb_init_detach_preserves_validity sg args
      original.(os_sched_call_invocation) original.(os_sched_call_origin)
      first slot rest image Hentry Hdetach))). }
  assert (Hpreserved : task_tcb_init_stack_source_preserved checkpoint_call checkpoint current)
    by tauto.
  rewrite Hinvocation in Hlast.
  pose proof (task_tcb_init_call_preserved_trans sg original.(os_sched_call_invocation)
    _ checkpoint current Hprevious Hlast) as Hinterval.
  destruct (task_tcb_init_call_preserves_allocation sg args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) first slot rest image current Hentry Hdetach Hinterval)
    as [Hvalid [Hcommit Hactive]].
  assert (Hsame : task_tcb_init_stack_same_call returned checkpoint_call) by tauto.
  destruct Hsame as [Hreturned_invocation [Hreturned_origin Hreturned_stack]].
  Exists returned current.
  unfold task_tcb_init_stack_same_call, task_tcb_init_stack_context, task_tcb_init_continuation_capsules, UCOS2_inv.
  rewrite Hreturned_invocation, Hreturned_origin, Hinvocation, Horigin; entailer!; congruence.
Qed.

(** At the real free-list store, detach the free head and reindex the SAME
    continuation map.  The selected task's caller stage is unaffected by
    this private allocation; no claim is made about the following Restore
    or about intervening incomplete client operations.  This is the
    combined resource consumer for OS_TCBInit_entail_wit_3. *)
Lemma task_tcb_init_continuation_detach_resources :
  forall environment saved_local sg args invocation origin acquired slot rest image,
  task_tcb_init_entry sg args invocation origin acquired ->
  task_tcb_init_detach_observation args invocation origin acquired slot rest image ->
  sg.(g_OSTCBFreeList) # Ptr |-> task_tcb_init_free_next sg rest **
    task_tcb_init_public_without_free_head sg acquired rest **
    task_tcb_init_continuation_capsules environment saved_local acquired |--
  let detached := task_tcb_init_detached_state args invocation origin acquired slot rest image in
  coq_prop (forall observer, task_create_call_stage observer acquired ->
    task_create_call_stage observer detached) &&
  (UCOS2_inv sg detached ** task_tcb_init_continuation_capsules environment saved_local detached).
Proof.
  intros environment saved_local sg args invocation origin acquired slot rest image Hentry Hdetach.
  cbv zeta.
  sep_apply_l_atomic (task_tcb_init_detach_merge_invariant sg args invocation origin
    acquired slot rest image Hentry Hdetach).
  sep_apply_l_atomic (task_tcb_init_continuation_capsules_used_map_eq environment saved_local
    acquired (task_tcb_init_detached_state args invocation origin acquired slot rest image)
    eq_refl eq_refl).
  entailer!.
Qed.

(** At the post-store cut, consume the concrete publication cells, the
    caller's initialized buffer and the CURRENT capsule map.  The lease
    comes from the actual allocation binding preserved by both intervals;
    this theorem performs no new C store and assumes no ready-to-frame law. *)

Lemma task_tcb_init_continuation_publication_output :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin initial acquired current slot rest image active,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    invocation origin acquired ->
  task_tcb_init_call_preserved sg invocation initial acquired ->
  task_tcb_init_detach_observation (task_tcb_init_stack_call_args args initial_name)
    invocation origin acquired slot rest image ->
  task_tcb_init_call_preserved sg invocation
    (task_tcb_init_detached_state (task_tcb_init_stack_call_args args initial_name)
      invocation origin acquired slot rest image) current ->
  task_tcb_init_commit_binding (task_tcb_init_stack_call_args args initial_name)
    invocation origin acquired current slot ->
  UCOS2_state_inv sg current ->
  task_stack_live_coverage current.(TskState) active ->
  task_create_publication_storage sg (task_tcb_init_stack_call_args args initial_name)
    invocation acquired current slot image **
  task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
  task_tcb_init_continuation_capsules environment saved_local current |--
  EX lease,
    let publication := task_tcb_init_stack_publication region args task_return lower upper initial_name
      invocation origin acquired slot image lease in
    coq_prop (task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
      invocation origin initial 0 (task_create_stack_publication_state sg publication current) /\
      task_stack_live_coverage (task_create_stack_publication_state sg publication current).(TskState) active /\
      (forall call, task_tcb_init_stack_source_preserved call current
        (task_create_stack_publication_state sg publication current)) /\
      task_create_stack_publication_input sg publication current /\
      (forall call, task_create_call_stage call current ->
        task_create_call_stage call (task_create_stack_publication_state sg publication current))) &&
    (UCOS2_inv sg (task_create_stack_publication_state sg publication current) **
     task_tcb_init_continuation_capsules environment saved_local (task_create_stack_publication_state sg publication current)).
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name invocation origin
    initial acquired current slot rest image active Hlayout Hentry Hfirst Hdetach Hinterval Hcommit Hvalid Hcoverage.
  destruct (task_create_stack_commit_allocation_binding region (task_tcb_init_stack_call_args args initial_name)
    invocation origin acquired current slot Hcommit) as [allocation [Hslot [Hgeneration Hcreation]]].
  destruct (task_tcb_init_detached_flags_defined sg (task_tcb_init_stack_call_args args initial_name)
    invocation origin acquired slot rest image Hentry Hdetach) as [flags Hflags].
  set (publication := task_tcb_init_stack_publication region args task_return lower upper initial_name
    invocation origin acquired slot image (task_stack_lease_of_allocation region allocation)).
  assert (Hinput : task_create_stack_publication_input sg publication current).
  { split; [exact Hlayout|]. split; [reflexivity|]. split; [exact Hcommit|].
    split; [exact Hcreation|]. split; [exists flags; exact Hflags|].
    intros Hnames; destruct (proj2 (proj2 (proj2 (proj2 Hentry))) Hnames) as [chars Hread].
    destruct (Hinterval (task_tcb_init_detach_preserves_validity sg
      (task_tcb_init_stack_call_args args initial_name) invocation origin acquired slot rest image
      Hentry Hdetach)) as [_ [_ [_ Hname]]].
    exists chars; rewrite task_tcb_init_commit_node_name, <- Hname; exact Hread. }
  pose proof (task_tcb_init_call_published_result sg (task_tcb_init_stack_call_args args initial_name)
    invocation origin initial acquired slot rest image current Hentry Hfirst Hdetach Hinterval Hcommit Hvalid)
    as Hraw.
  pose proof (kernel_task_publication_continuation_merge environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) sg publication current
    (task_create_continuation_local saved_local) active Hvalid Hinput Hcoverage) as Hpost.
  assert (Hinitial_local : task_create_continuation_local saved_local
    (task_create_stack_publication_continuation publication) = emp) by reflexivity.
  rewrite Hinitial_local in Hpost.
  cbv zeta in Hpost.
  cbn [publication task_tcb_init_stack_publication task_create_stack_publication_args
    task_create_stack_publication_words stack_publication_region stack_publication_args
    stack_publication_return stack_publication_lower stack_publication_upper stack_publication_name
    stack_publication_invocation stack_publication_origin stack_publication_acquired
    stack_publication_slot stack_publication_image stack_publication_lease] in Hpost.
  fold (task_tcb_init_stack_call_args args initial_name) in Hpost.
  unfold task_tcb_init_continuation_capsules.
  match type of Hpost with ?P |-- ?Q =>
    match goal with |- ?R |-- ?S =>
      assert (Hready : R |-- P) by entailer!;
      eapply derivable1_trans; [exact Hready|]
    end
  end.
  eapply derivable1_trans; [exact Hpost|]. Intros.
  Exists (task_stack_lease_of_allocation region allocation); fold publication.
  entailer!.
  - econstructor; eassumption.
  - intros call Hsource; eapply task_create_stack_publication_preserves_call_source; eassumption.
  - intros call Hstage; eapply task_create_publication_preserves_call_stage; eassumption.
Qed.

Lemma task_tcb_init_continuation_call_post_no_free :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original released,
  task_tcb_init_call_result sg (task_tcb_init_stack_call_args args initial_name)
    invocation origin initial 66 released ->
  task_tcb_init_stack_source_preserved original initial released ->
  task_tcb_init_continuation_call_return_post environment critical saved_local sg original mask released **
  task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) |--
  task_tcb_init_continuation_call_post environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original 66.
Proof.
intros environment critical saved_local sg region args task_return lower upper initial_name invocation origin mask
    initial original released Hresult Hsource.
  assert (Hvalid : UCOS2_state_inv sg released) by (inversion Hresult; assumption).
  unfold task_tcb_init_continuation_call_post, task_tcb_init_stack_buffer_result.
  destruct (Z.eq_dec 66 66); [|contradiction]. Exists released; entailer!.
  constructor; assumption.
Qed.

Lemma task_tcb_init_continuation_call_post_published :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original acquired current slot image lease,
  task_tcb_init_result critical sg (task_tcb_init_stack_call_args args initial_name)
    invocation origin initial 0
    (task_tcb_init_published_state sg (task_tcb_init_stack_call_args args initial_name)
      invocation acquired current slot image) ->
  task_create_stack_publication_input sg
    (task_tcb_init_stack_publication region args task_return lower upper initial_name
      invocation origin acquired slot image lease) current ->
  UCOS2_state_inv sg current ->
  task_tcb_init_stack_source_preserved original initial current ->
  task_tcb_init_continuation_restore_post environment critical saved_local sg original mask
    (task_create_stack_publication_state sg
      (task_tcb_init_stack_publication region args task_return lower upper initial_name
        invocation origin acquired slot image lease) current) |--
  task_tcb_init_continuation_call_post environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original 0.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name invocation origin mask
    initial original acquired current slot image lease Hresult Hinput Hvalid Hsource.
  set (publication := task_tcb_init_stack_publication region args task_return lower upper initial_name
    invocation origin acquired slot image lease).
  assert (Hpublished : UCOS2_state_inv sg (task_create_stack_publication_state sg publication current)).
  { eapply task_create_stack_publication_preserves_validity; [exact Hvalid|].
    split; [exact Hinput|reflexivity]. }
  assert (Hpreserved : task_tcb_init_stack_source_preserved original initial
    (task_create_stack_publication_state sg publication current)).
  { intros Hbefore; eapply task_create_stack_publication_preserves_call_source;
      [exact Hvalid|exact Hinput|apply Hsource; exact Hbefore]. }
  sep_apply_l_atomic (task_tcb_init_continuation_restore_post_returns_call environment critical saved_local sg original mask
    (task_create_stack_publication_state sg publication current) Hpublished).
  unfold task_tcb_init_continuation_call_post, task_tcb_init_stack_buffer_result.
  destruct (Z.eq_dec 0 66); [discriminate|].
  Exists (task_create_stack_publication_state sg
    (task_tcb_init_stack_publication region args task_return lower upper initial_name
      invocation origin acquired slot image lease) current); fold publication; entailer!.
  econstructor; [eapply task_tcb_init_result_implies_call_result; exact Hresult|exact Hinput].
Qed.
