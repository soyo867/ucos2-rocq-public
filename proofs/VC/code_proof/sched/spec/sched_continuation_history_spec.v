Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_irq_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_irq_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_return_source_spec.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_context Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_save_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Additive observations of completed calls.  The left alternatives are
    the existing modular source contracts; the right alternatives retain
    the existing deposit/registry/take histories.  No flat trace is inferred
    from a segmented execution.  In either case the spatial producer must
    return the SAME context and state as this observation. *)
Definition os_sched_continuation_save_effect environment critical sg
  original mask saved before returned acquired : Prop :=
  kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask saved before acquired \/
  (kernel_call_save_history environment critical sg original before returned acquired /\
   interrupt_saved_value mask saved).

Definition os_sched_continuation_restore_effect environment critical sg
  original released returned current : Prop :=
  (kernel_resumption_task_source_trace environment.(task_stack_call_external)
     environment.(task_stack_call_port) critical.(critical_region_clients) sg
     original.(os_sched_call_invocation) None original.(os_sched_call_origin)
     released false returned.(os_sched_call_origin) current /\
   task_tcb_init_stack_same_call returned original) \/
  kernel_call_restore_history environment critical sg original released returned current.

Definition os_sched_continuation_save_history_output environment critical saved_local
  sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (os_sched_continuation_save_effect environment critical sg
        original mask saved before returned acquired /\
      task_tcb_init_stack_same_call returned original /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before acquired /\
      (UCOS2_state_inv sg before -> task_tcb_init_stack_source_preserved original before acquired) /\
      interrupt_saved_value mask saved /\
      task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key returned)) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved acquired **
     task_tcb_init_stack_context environment returned ** UCOS2_inv sg acquired **
     task_tcb_init_continuation_capsules environment saved_local acquired).

(** The selector cut is an observation of the actual acquired state, not
    a new universally quantified future-entry assumption on callers. *)
Definition os_sched_continuation_call_save_history_output environment critical saved_local
  sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (os_sched_continuation_save_effect environment critical sg
        original mask saved before returned acquired /\
      task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
      task_tcb_init_stack_source_preserved original before acquired /\
      os_sched_call_cut sg returned acquired) &&
    task_tcb_init_continuation_restore_input environment critical saved_local
      sg returned saved acquired acquired.

Definition os_sched_continuation_restore_history_output environment critical saved_local
  sg original saved released : Assertion :=
  EX returned current,
    coq_prop (os_sched_continuation_restore_effect environment critical sg original released returned current /\
      task_tcb_init_stack_same_call returned original /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
      (UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved original released current)) &&
    task_tcb_init_continuation_save_input environment critical saved_local sg
      returned (armv7a_irq_fiq_mask saved) current.

(** Three different cuts are intentional.  The C body is exactly the old
    [os_sched_c_return], and [current] is not identified with [released].
    Returned fragments are observed through the actual context, never by
    treating same invocation/origin/stack as equality of whole contexts. *)
Definition os_sched_continuation_call_history environment critical sg
  original mask before returned current : Prop :=
  exists scheduled entry resumed released saved,
    os_sched_continuation_save_effect environment critical sg
      original mask saved before scheduled entry /\
    os_sched_c_return environment.(task_stack_call_external) critical sg
      entry scheduled resumed released /\
    os_sched_continuation_restore_effect environment critical sg resumed released returned current.

Definition os_sched_continuation_history_return_post environment critical saved_local resources
  sg original mask before : Assertion :=
  EX returned current,
    coq_prop (os_sched_continuation_call_history environment critical sg original mask before returned current /\
      task_tcb_init_stack_same_call returned original /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current)) &&
    kernel_continuation_call_closed environment.(task_stack_call_continuations)
      resources (task_create_continuation_local saved_local) sg
      (task_stack_call_active_key returned) returned mask current.

Definition os_sched_continuation_save_program environment critical sg original mask :
  program UCOS2_Verify_State (OsSchedCallContext * Z) :=
  fun before result acquired => os_sched_continuation_save_effect environment critical sg
    original mask (snd result) before (fst result) acquired.

Definition os_sched_continuation_body_program environment critical sg scheduled :
  program UCOS2_Verify_State OsSchedCallContext :=
  fun entry resumed released =>
    os_sched_c_return environment.(task_stack_call_external) critical sg entry scheduled resumed released.

Definition os_sched_continuation_restore_program environment critical sg resumed :
  program UCOS2_Verify_State OsSchedCallContext :=
  fun released returned current =>
    os_sched_continuation_restore_effect environment critical sg resumed released returned current.

Definition os_sched_continuation_program environment critical sg original mask :
  program UCOS2_Verify_State OsSchedCallContext :=
  StateRelMonad.bind (os_sched_continuation_save_program environment critical sg original mask)
    (fun entered => StateRelMonad.bind (os_sched_continuation_body_program environment critical sg (fst entered))
      (fun resumed => os_sched_continuation_restore_program environment critical sg resumed)).

Lemma os_sched_continuation_program_iff : forall environment critical sg original mask before returned current,
  os_sched_continuation_program environment critical sg original mask before returned current <->
  os_sched_continuation_call_history environment critical sg original mask before returned current.
Proof.
  intros; unfold os_sched_continuation_program, os_sched_continuation_save_program,
    os_sched_continuation_body_program, os_sched_continuation_restore_program,
    os_sched_continuation_call_history, StateRelMonad.bind.
  split.
  - intros [[scheduled saved] [entry [Hsave [resumed [released [Hbody Hrestore]]]]]].
    exists scheduled, entry, resumed, released, saved; exact (conj Hsave (conj Hbody Hrestore)).
  - intros [scheduled [entry [resumed [released [saved [Hsave [Hbody Hrestore]]]]]]].
    exists (scheduled, saved), entry; split; [exact Hsave|].
    exists resumed, released; split; assumption.
Qed.

Lemma os_sched_continuation_save_history_output_weaken : forall environment critical saved_local
  sg original mask saved before,
  os_sched_continuation_save_history_output environment critical saved_local sg original mask saved before |--
  task_tcb_init_continuation_save_output environment critical saved_local sg original mask saved before.
Proof.
  intros; unfold os_sched_continuation_save_history_output; Intros returned acquired.
  unfold task_tcb_init_continuation_save_output; Exists returned acquired; entailer!; tauto.
Qed.

Lemma os_sched_continuation_call_save_history_output_weaken : forall environment critical saved_local
  sg original mask saved before,
  os_sched_continuation_call_save_history_output environment critical saved_local sg original mask saved before |--
  os_sched_continuation_call_save_output environment critical saved_local sg original mask saved before.
Proof.
  intros; unfold os_sched_continuation_call_save_history_output; Intros returned acquired.
  unfold os_sched_continuation_call_save_output; Exists returned acquired; entailer!; tauto.
Qed.

Lemma os_sched_continuation_restore_history_output_weaken : forall environment critical saved_local
  sg original saved released,
  os_sched_continuation_restore_history_output environment critical saved_local sg original saved released |--
  task_tcb_init_continuation_restore_output environment critical saved_local sg original saved released.
Proof.
  intros; unfold os_sched_continuation_restore_history_output; Intros returned current.
  unfold task_tcb_init_continuation_restore_output; Exists returned current; entailer!; tauto.
Qed.

Lemma os_sched_continuation_history_return_post_weaken : forall environment critical saved_local resources
  sg original mask before,
  os_sched_continuation_history_return_post environment critical saved_local resources sg original mask before |--
  os_sched_continuation_return_post environment saved_local resources sg original mask before.
Proof.
  intros; unfold os_sched_continuation_history_return_post; Intros returned current.
  unfold os_sched_continuation_return_post; Exists returned current; entailer!; tauto.
Qed.

Lemma os_sched_continuation_save_effect_same_call : forall environment critical sg
  original mask saved before returned acquired,
  os_sched_continuation_save_effect environment critical sg original mask saved before returned acquired ->
  task_tcb_init_stack_same_call returned original.
Proof.
  intros * [Hsave|[Hhistory Hsaved]].
  - destruct Hsave as [Htrace [Hi [Ho [Hs Hsaved]]]].
    repeat split; assumption.
  - eapply kernel_call_save_history_same_call; exact Hhistory.
Qed.

Lemma os_sched_continuation_restore_effect_same_call : forall environment critical sg
  original released returned current,
  os_sched_continuation_restore_effect environment critical sg original released returned current ->
  task_tcb_init_stack_same_call returned original.
Proof.
  intros * [[_ Hsame]|Hhistory]; [exact Hsame|].
  eapply kernel_call_restore_history_same_call; exact Hhistory.
Qed.

Lemma os_sched_continuation_call_history_same_call : forall environment critical sg
  original mask before returned current,
  os_sched_continuation_call_history environment critical sg original mask before returned current ->
  task_tcb_init_stack_same_call returned original.
Proof.
  intros * [scheduled [entry [resumed [released [saved [Hsave [Hbody Hrestore]]]]]]].
  pose proof (os_sched_continuation_save_effect_same_call _ _ _ _ _ _ _ _ _ Hsave) as Hfirst.
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hmiddle.
  pose proof (os_sched_continuation_restore_effect_same_call _ _ _ _ _ _ _ Hrestore) as Hlast.
  unfold task_tcb_init_stack_same_call in *; intuition congruence.
Qed.

Lemma os_sched_continuation_history_safeexec : forall environment critical sg
  original mask before returned current (X : OsSchedCallContext -> UCOS2_Verify_State -> Prop),
  os_sched_continuation_call_history environment critical sg original mask before returned current ->
  safeExec (fun state => state = before)
    (os_sched_continuation_program environment critical sg original mask) X ->
  safeExec (fun state => state = current) (StateRelMonad.ret returned) X.
Proof.
  intros environment critical sg original mask before returned current X Hhistory Hsafe.
  eapply (highstependret_derive
    (os_sched_continuation_program environment critical sg original mask)
    (fun state => state = before) returned (fun _ state => state = current)).
  - intros state Hstate; subst state; exists current; split; [|reflexivity].
    apply os_sched_continuation_program_iff; exact Hhistory.
  - exact Hsafe.
Qed.

Lemma os_sched_continuation_restore_history_output_return : forall environment critical saved_local sg
  original scheduled resumed mask saved before entry released,
  os_sched_continuation_save_effect environment critical sg original mask saved before scheduled entry ->
  task_tcb_init_stack_same_call scheduled original ->
  (kernel_call_task_source original before -> kernel_call_task_source scheduled entry) ->
  (os_sched_requests_switch entry = true -> os_sched_current_storage_binding sg scheduled entry) ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry scheduled resumed released ->
  UCOS2_state_inv sg released -> interrupt_saved_value mask saved ->
  os_sched_continuation_restore_history_output environment critical saved_local sg resumed saved released **
    unmap_table_rep sg |--
  os_sched_continuation_history_return_post environment critical saved_local kernel_program_inv
    sg original mask before.
Proof.
  intros environment critical saved_local sg original scheduled resumed mask saved before entry released
    Hsave Hscheduled Hentry_source Hcut Hbody Hvalid Hsaved.
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hresumed.
  unfold os_sched_continuation_restore_history_output; Intros returned current.
  assert (Hrestore : os_sched_continuation_restore_effect environment critical sg resumed released returned current)
    by tauto.
  assert (Hreturned : task_tcb_init_stack_same_call returned resumed) by tauto.
  assert (Hsource : task_tcb_init_stack_source_preserved resumed released current) by tauto.
  assert (Hhistory : os_sched_continuation_call_history environment critical sg original mask before returned current).
  { exists scheduled, entry, resumed, released, saved; repeat split; assumption. }
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { eapply os_sched_continuation_call_history_same_call; exact Hhistory. }
  assert (Hfinal_source : kernel_call_task_source original before -> kernel_call_task_source returned current).
  { intro Hinitial.
    pose proof (os_sched_continuation_c_return_source _ _ _ _ _ _ _ Hcut Hbody
      (Hentry_source Hinitial)) as Hreleased.
    apply (proj2 (task_tcb_init_stack_same_call_source_iff returned resumed current Hreturned)).
    apply Hsource; exact Hreleased. }
  sep_apply_l_atomic (proj1 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current)).
  rewrite (proj2 Hsaved).
  unfold os_sched_continuation_history_return_post; Exists returned current; entailer!.
Qed.

(** These producers retain facts before the older interface projections
    discard them.  They consume an existing source-owned post, not the
    weaker same-call assertion. *)
Lemma os_sched_continuation_registered_save_history_output :
  forall environment critical saved_local sg original mask saved before,
  task_tcb_init_continuation_save_post environment critical saved_local sg original mask saved before |--
  os_sched_continuation_save_history_output environment critical saved_local sg original mask saved before.
Proof.
  intros; unfold task_tcb_init_continuation_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask saved before acquired) by tauto.
  assert (Heffect : os_sched_continuation_save_effect environment critical sg
    original mask saved before returned acquired) by (left; exact Hsave).
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  pose proof (task_tcb_init_interval_preserves_call _ _ _ _ _ Hinterval) as Hpreserved.
  destruct Hsave as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hsame : task_tcb_init_stack_same_call returned original) by (repeat split; assumption).
  assert (Hordinary : UCOS2_state_inv sg before -> task_tcb_init_stack_source_preserved original before acquired).
  { intro Hvalid; eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  unfold os_sched_continuation_save_history_output; Exists returned acquired.
  unfold task_tcb_init_stack_context; entailer!.
Qed.

Lemma os_sched_continuation_registered_restore_history_output :
  forall environment critical saved_local sg original saved released,
  task_tcb_init_continuation_restore_post environment critical saved_local sg original
    (armv7a_irq_fiq_mask saved) released |--
  os_sched_continuation_restore_history_output environment critical saved_local sg original saved released.
Proof.
  intros; unfold task_tcb_init_continuation_restore_post; Intros returned current.
  assert (Htrace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    released false returned.(os_sched_call_origin) current) by tauto.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by (repeat split; tauto).
  assert (Heffect : os_sched_continuation_restore_effect environment critical sg original released returned current)
    by (left; split; assumption).
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)) as Hinterval.
  pose proof (task_tcb_init_interval_preserves_call _ _ _ _ _ Hinterval) as Hpreserved.
  assert (Hordinary : UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved original released current).
  { intro Hvalid; eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  unfold os_sched_continuation_restore_history_output; Exists returned current.
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input; entailer!.
Qed.

Lemma os_sched_continuation_modular_restore_history_output :
  forall environment critical saved_local rely sg original saved released,
  kernel_call_modular_restore_post environment.(task_stack_call_continuations) kernel_program_inv
    (task_create_continuation_local saved_local) critical rely sg original
    (armv7a_irq_fiq_mask saved) released |--
  os_sched_continuation_restore_history_output environment critical saved_local sg original saved released **
    unmap_table_rep sg.
Proof.
  intros; unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Htrace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    released false returned.(os_sched_call_origin) current) by tauto.
  assert (Hnormal : kernel_call_normal_return original released returned current) by tauto.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by exact (proj1 Hnormal).
  assert (Heffect : os_sched_continuation_restore_effect environment critical sg original released returned current)
    by (left; split; assumption).
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)) as Hinterval.
  pose proof (task_tcb_init_interval_preserves_call _ _ _ _ _ Hinterval) as Hpreserved.
  assert (Hordinary : UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved original released current).
  { intro Hvalid; eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current)).
  unfold os_sched_continuation_restore_history_output; Exists returned current; entailer!.
Qed.

Lemma os_sched_continuation_modular_save_history_output_guarded :
  forall environment critical saved_local rely sg original mask saved before,
  UCOS2_state_inv sg before -> kernel_tcb_stack_field_layout sg ->
  (forall after, rely sg before after -> os_sched_selection_enabled after = true ->
    after.(SchedState).(readyList) <> []) ->
  (forall after, rely sg before after -> os_sched_requests_switch after = true ->
    kernel_call_task_source original before /\ kernel_call_stack_available original before) ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations) kernel_program_inv
    (task_create_continuation_local saved_local) critical rely sg original mask saved before |--
  os_sched_continuation_call_save_history_output environment critical saved_local sg original mask saved before **
    unmap_table_rep sg.
Proof.
  intros environment critical saved_local rely sg original mask saved before Hvalid Hlayout Hready Hsource.
  sep_apply_l_atomic (kernel_call_modular_save_post_guarded_cut
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    environment.(task_stack_call_port) environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical rely sg original mask saved before
    Hvalid Hlayout Hready Hsource).
  Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask saved before acquired) by tauto.
  assert (Heffect : os_sched_continuation_save_effect environment critical sg
    original mask saved before returned acquired) by (left; exact Hsave).
  destruct Hsave as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hsame : task_tcb_init_stack_same_call returned original) by (repeat split; assumption).
  assert (Hordinary : task_tcb_init_stack_source_preserved original before acquired).
  { eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_restore_input_masked_world
    environment critical saved_local sg returned saved acquired acquired)).
  unfold os_sched_continuation_call_save_history_output; Exists returned acquired; entailer!.
Qed.

Lemma os_sched_registered_save_call_history_output :
  forall environment critical saved_local sg original returned mask saved before acquired,
  kernel_sched_ready_clients critical ->
  UCOS2_state_inv sg before -> before.(SchedState).(readyList) <> [] ->
  kernel_call_task_source original before ->
  kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask saved before acquired ->
  kernel_call_stack_available returned acquired ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_tcb_init_continuation_restore_input environment critical saved_local
    sg returned saved acquired acquired |--
  os_sched_continuation_call_save_history_output environment critical saved_local sg original mask saved before.
Proof.
  intros environment critical saved_local sg original returned mask saved before acquired
    Hmodules Hvalid Hready Hsource Hsave Havailable Haddress.
  assert (Heffect : os_sched_continuation_save_effect environment critical sg
    original mask saved before returned acquired) by (left; exact Hsave).
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  pose proof (critical_region_interval_preserves_sched_ready critical sg
    original.(os_sched_call_invocation) before acquired Hmodules Hinterval Hvalid Hready) as Hready_after.
  pose proof Hsave as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hsame : task_tcb_init_stack_same_call returned original) by (repeat split; assumption).
  assert (Hpreserved : task_tcb_init_stack_source_preserved original before acquired).
  { eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  assert (Hcurrent : kernel_call_task_source returned acquired).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original acquired Hsame)).
    apply Hpreserved; exact Hsource. }
  pose proof (critical_region_interval_transports_resources critical sg
    original.(os_sched_call_invocation) before acquired Hinterval Hvalid) as [Hvalid_after Hrest].
  assert (Hcut : os_sched_call_cut sg returned acquired).
  { eapply os_sched_call_cut_from_source; try eassumption.
    rewrite Hs; exact Haddress. }
  unfold os_sched_continuation_call_save_history_output; Exists returned acquired; entailer!.
Qed.

Lemma os_sched_disabled_save_call_history_output : forall environment critical saved_local sg
  original returned mask saved before acquired,
  os_sched_continuation_save_effect environment critical sg original mask saved before returned acquired ->
  task_tcb_init_stack_same_call returned original -> interrupt_saved_value mask saved ->
  task_tcb_init_stack_source_preserved original before acquired ->
  os_sched_selection_enabled acquired = false ->
  task_tcb_init_continuation_restore_input environment critical saved_local
    sg returned saved acquired acquired |--
  os_sched_continuation_call_save_history_output environment critical saved_local sg original mask saved before.
Proof.
  intros; assert (Hcut : os_sched_call_cut sg returned acquired)
    by (apply os_sched_call_cut_disabled; assumption).
  unfold os_sched_continuation_call_save_history_output; Exists returned acquired; entailer!.
Qed.

Lemma os_sched_uninterrupted_save_call_history_output : forall environment critical saved_local sg
  call mask saved state,
  os_sched_call_cut sg call state -> interrupt_saved_value mask saved ->
  task_tcb_init_continuation_restore_input environment critical saved_local
    sg call saved state state |--
  os_sched_continuation_call_save_history_output environment critical saved_local sg call mask saved state.
Proof.
  intros environment critical saved_local sg call mask saved state Hcut Hsaved.
  assert (Heffect : os_sched_continuation_save_effect environment critical sg call mask saved state call state).
  { left; split; [constructor|]. repeat (split; [reflexivity|]); exact Hsaved. }
  unfold os_sched_continuation_call_save_history_output; Exists call state.
  unfold task_tcb_init_stack_same_call, task_tcb_init_stack_source_preserved; entailer!.
Qed.

(** Conversion after observing the actual raw Save endpoint.  The cut is
    indexed by that very returned descriptor/state; this does not quantify
    over future Save behavior or strengthen a caller's public precondition.
    A disabled endpoint uses [os_sched_call_cut_disabled], with no ready
    or Task-source requirement. *)
Lemma os_sched_continuation_save_history_endpoint_call_output : forall environment critical saved_local sg
  original returned mask saved before acquired,
  UCOS2_state_inv sg before ->
  os_sched_continuation_save_effect environment critical sg original mask saved before returned acquired ->
  task_tcb_init_stack_same_call returned original -> interrupt_saved_value mask saved ->
  (UCOS2_state_inv sg before -> task_tcb_init_stack_source_preserved original before acquired) ->
  os_sched_call_cut sg returned acquired ->
  task_tcb_init_continuation_restore_input environment critical saved_local
    sg returned saved acquired acquired |--
  os_sched_continuation_call_save_history_output environment critical saved_local sg original mask saved before.
Proof.
  intros; unfold os_sched_continuation_call_save_history_output; Exists returned acquired; entailer!.
Qed.

(** The following two additive exports reuse the already checked generic
    continuation deposit/registry/take/suffix composition.  Only its final
    packaging changes: the actual descriptor and state are retained before
    the legacy existential output forgets them.  Their hypotheses and source
    branch scope are unchanged (first-level, Closed/counter-only registry).
    They neither cover arbitrary IRQ families nor assert eventual return. *)
Lemma os_sched_continuation_mrs_irq_save_history_output :
  forall environment critical saved_local arch Extra
    (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (registers_source : Armv7aIRQRegisterSave environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    sg entry node handler suspended publication registers after_mrs before irq_input saved_heap
    (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let local := task_tcb_init_irq_local saved_local suspended in
  let parked := armv7a_irq_live_parked_state entry call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_task_frame_slice suspended ->
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_sp) ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  kernel_call_save_instruction_step arch SaveReadCPSR registers entry before after_mrs entry irq_input ->
  handler.(os_int_exit_interrupted_pc) = armv7a_save_entry_address suffix + 4 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask registers.(kernel_save_cpsr) ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  (task_tcb_init_continuation_save_input environment critical saved_local sg call
     (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) entry ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
   frame) irq_input ->
  armv7a_irq_register_save registers_source after_mrs.(kernel_save_r0) after_mrs.(kernel_save_lr)
    handler suspended irq_input saved_heap ->
  exists registry_heap,
    nth 0 suspended.(armv7a_continuation_registers) 0 = registers.(kernel_save_cpsr) /\
    kernel_heap_writes (armv7a_continuation_save_writes suspended)
      irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (forall closed_heap,
      @kernel_client_heap_trace Extra (fun _ _ _ _ _ => False) sg
        KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap ->
      exists returned,
        @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg
          KernelClientHeapClosed parked KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg
          call.(os_sched_call_invocation) None call.(os_sched_call_origin)
          parked false call.(os_sched_call_origin) returned /\
        armv7a_irq_restore_pointer_reads sg closed_heap
          (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) suspended.(armv7a_continuation_sp) /\
        (forall restored cursor final_registers acquired after,
          armv7a_restore_transition abi handler suspended closed_heap restored ->
          cursor.(kernel_save_cpsr) = suspended.(armv7a_continuation_cpsr) ->
          cursor.(kernel_save_r0) = nth 0 suspended.(armv7a_continuation_registers) 0 ->
          cursor.(kernel_save_lr) = suspended.(armv7a_continuation_lr) ->
          armv7a_save_suffix_transition suffix cursor
            (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) restored
            final_registers acquired after ->
          kernel_save_after_mrs_execution arch cursor
            (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) restored
            final_registers acquired after /\
          final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
          final_registers.(kernel_save_return_word) = Some suspended.(armv7a_continuation_lr) /\
          (os_sched_continuation_save_history_output environment critical saved_local sg call
             (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0) entry **
           unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
             handler.(os_int_exit_handler_fragments) ** frame) after /\
          (os_sched_call_cut sg (armv7a_continuation_resumed_call suspended call)
             (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) ->
           (os_sched_continuation_call_save_history_output environment critical saved_local sg call
              (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0) entry **
            unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
              handler.(os_int_exit_handler_fragments) ** frame) after))).
Proof.
  intros environment critical saved_local arch Extra suffix registers_source sg entry node handler suspended
    publication registers after_mrs before irq_input saved_heap frame call abi local parked
    Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hregister_valid Hmrs Hpc Hhandler Henter Hexit Hpublish Hpre Hcapture.
  assert (Hmrs_registers : after_mrs = kernel_save_read_cpsr registers)
    by (inversion Hmrs; reflexivity).
  subst after_mrs.
  destruct (armv7a_irq_register_save_refinement _ _ _ _ registers_source _ _ _ _ _ _ Hcapture)
    as [Hsave [Hr0 Hlr]].
  change (nth 0 suspended.(armv7a_continuation_registers) 0 = registers.(kernel_save_cpsr)) in Hr0.
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended irq_input saved_heap Hsave)
    as [Hsave_source [Hcall [Hbinding [Hsaved_mask [Hsaved_pc Hsave_rest]]]]].
  assert (Hlease : suspended.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hbound; rewrite Hcall in Hbound; symmetry; exact Hbound. }
  assert (Habsent : entry.(TskState).(parkedTaskStacks)
    (task_stack_key suspended.(armv7a_continuation_stack)) = None) by (rewrite Hlease; exact Hnone).
  assert (Hcoverage : task_stack_live_coverage entry.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { match type of Hpre with ?P irq_input => assert (Hobserve : P |-- coq_prop
      (task_stack_live_coverage entry.(TskState) (task_stack_call_active_key call)) && TT) end.
    { unfold task_tcb_init_continuation_save_input, task_create_continuation_input;
        entailer!; intros ? ?; exact I. }
    pose proof (proj1 (Hobserve irq_input Hpre)) as Hcovered.
    unfold task_stack_call_active_key in Hcovered; rewrite Horigin in Hcovered; exact Hcovered. }
  match type of Hpre with ?P irq_input => assert (Hirq_input : P |--
    os_int_exit_frame_save_pre environment.(task_stack_call_external) environment.(task_stack_call_platform) handler **
    (UCOS2_inv sg entry **
     store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
       entry.(TskState).(parkedTaskStacks) ** local suspended ** (unmap_table_rep sg ** frame))) end.
  { unfold task_tcb_init_continuation_save_input, task_create_continuation_input.
    fold abi; Intros.
    sep_apply_l_atomic (proj1 (task_tcb_init_irq_map_absent _ _ _ abi entry.(TskState)
      entry.(TskState).(parkedTaskStacks) saved_local suspended Habsent)).
    unfold os_int_exit_frame_save_pre, local; rewrite task_tcb_init_irq_local_saved_eq.
    rewrite Hhandler; unfold critical_region_outside.
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
    unfold UCOS2_inv; entailer!. }
  destruct (kernel_irq_save_continuation_resources _ _ _ abi sg entry node handler suspended publication
    local (unmap_table_rep sg ** frame) irq_input saved_heap Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen
    Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage (Hirq_input irq_input Hpre) Hsave)
    as [registry_heap [Hsave_call [Hsave_pc [Hsave_mask [Hwrites [Hstores [Hcovered Hparked]]]]]]].
  fold parked in Hcovered, Hparked.
  assert (Hparked_valid : UCOS2_state_inv sg parked).
  { match type of Hparked with ?P registry_heap => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg parked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve registry_heap Hparked)). }
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node suspended.(armv7a_continuation_sp)))
    (task_stack_park_fragments entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      suspended.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hparked_sched : parked.(SchedState) = entry.(SchedState)).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  match type of Hparked with ?P registry_heap => assert (Hregistry : P |--
    kernel_client_continuation_world abi local sg parked **
    (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
     frame)) end.
  { unfold kernel_client_continuation_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  exists registry_heap; split; [exact Hr0|]. split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (kernel_client_continuation_trace_resources _ _ _ Extra abi local critical.(critical_region_clients)
    sg call.(os_sched_call_invocation) None Henter Hexit Hpublish
    KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap _ Htrace parked
    call.(os_sched_call_origin) I (Hregistry registry_heap Hparked))
    as [returned [Hstates [Hsources [Hobserver Hworld]]]].
  destruct (kernel_client_builtin_closed_trace_task_fields Extra sg _ _ _ _ Hstates eq_refl)
    as [Hclosed [Hreturned_tasks Hreturned_sched]].
  assert (Hreturned_current : returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot)).
  { rewrite Hreturned_sched, Hparked_sched; exact Hcurrent. }
  assert (Hreturned_node : returned.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node suspended.(armv7a_continuation_sp))).
  { rewrite Hreturned_tasks, Htasks; cbn [glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask].
    rewrite Z.eqb_refl; reflexivity. }
  assert (Hreturned_lookup : returned.(TskState).(parkedTaskStacks)
    (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
  { rewrite Hreturned_tasks, Htasks, Hlease; apply task_stack_park_fragments_lookup. }
  match type of Hworld with ?P closed_heap => assert (Htake_input : P |--
    coq_prop (task_stack_live_coverage returned.(TskState) None) &&
    (UCOS2_inv sg returned ** store_parked_continuations
       (kernel_saved_continuation_entry abi returned.(TskState) (task_tcb_init_irq_local saved_local suspended))
       returned.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
      unmap_table_rep sg ** frame))) end.
  { unfold kernel_client_continuation_resources, kernel_client_continuation_world, local;
      rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Htake_input closed_heap Hworld) as [Hreturned_coverage Htake_owned].
  assert (Htake_current : returned.(SchedState).(curTaskID) =
    Some suspended.(armv7a_continuation_stack).(stackLeaseSlot)) by (rewrite Hlease; exact Hreturned_current).
  assert (Htake_node : returned.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node suspended.(armv7a_continuation_sp))) by (rewrite Hlease; exact Hreturned_node).
  assert (Htake_gen : (task_set_saved_sp node suspended.(armv7a_continuation_sp)).(taskGeneration) =
    suspended.(armv7a_continuation_stack).(stackLeaseGeneration)) by (rewrite Hlease; exact Hgen).
  assert (Htake_address : tcb_field_address
    (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) by (rewrite Hlease; exact Haddress).
  destruct (task_tcb_init_irq_take_resources _ _ _ abi sg returned saved_local suspended call
    (task_set_saved_sp node suspended.(armv7a_continuation_sp)) _ closed_heap Hcall Htake_current Htake_node
    Htake_gen Hreturned_lookup Htake_address Hreturned_coverage Htake_owned)
    as [Hpointers [Hreads [Hfinal_coverage Htake_resources]]].
  exists returned; split; [exact Hstates|]. split; [exact Hsources|]. split.
  - rewrite Hlease in Hpointers; exact Hpointers.
  - intros restored cursor final_registers acquired after Hrestore Hcursor_cpsr Hcursor_r0 Hcursor_lr Hsuffix.
    match type of Htake_resources with ?P closed_heap => assert (Hrestore_input : P |--
      interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
      task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
        suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
      (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack)) **
       task_tcb_init_continuation_capsules environment saved_local
         (os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack)) **
       unmap_table_rep sg ** frame)) end.
    { unfold task_tcb_init_continuation_capsules; fold abi; entailer!. }
    destruct (armv7a_restore_call_resources _ _ _ abi handler suspended call _ closed_heap restored
      Hcall Hreads (Hrestore_input closed_heap Htake_resources) Hrestore) as [Hirq_memory Hrestored].
    assert (Hsaved : interrupt_saved_value (armv7a_irq_fiq_mask cursor.(kernel_save_cpsr)) cursor.(kernel_save_r0)).
    { rewrite Hcursor_cpsr, Hcursor_r0, Hr0.
      split; [exact Hregister_valid|rewrite Hsaved_mask, Hhandler; reflexivity]. }
    match type of Hrestored with ?P restored => assert (Hsuffix_input : P |--
      kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
        (armv7a_continuation_resumed_call suspended call) (armv7a_irq_fiq_mask cursor.(kernel_save_cpsr)) **
      (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
       task_tcb_init_continuation_capsules environment saved_local
         (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
       unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) ** frame)) end.
    { rewrite Hcursor_cpsr, Hlease; entailer!. }
    destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ suffix sg
      (armv7a_continuation_resumed_call suspended call) cursor
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) restored
      final_registers acquired after _ Hsaved (Hsuffix_input restored Hrestored) Hsuffix)
      as [Hacquired [Hafter_memory [Hreturn_word [Hreturn_r0 Hafter]]]].
    split; [exact (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hsuffix)|].
    split; [rewrite Hreturn_r0, Hcursor_r0; exact Hr0|].
    split; [rewrite Hreturn_word, Hcursor_lr; reflexivity|].
    assert (Hcurrent_valid : UCOS2_state_inv sg
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { match type of Hafter with ?P after => assert (Hobserve : P |-- coq_prop
        (UCOS2_state_inv sg (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))) && TT) end.
      { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
      exact (proj1 (Hobserve after Hafter)). }
    assert (Hpreserved : task_tcb_init_call_preserved sg call.(os_sched_call_invocation) entry
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { eapply task_tcb_init_irq_preserves_call; eassumption. }
    assert (Hsource_preserved : UCOS2_state_inv sg entry -> task_tcb_init_stack_source_preserved call entry
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { intro Hentry_valid.
      pose proof (task_tcb_init_stack_irq_return_preserved environment critical sg call entry node
        suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments)
        returned call.(os_sched_call_origin) Horigin Hrunning Hnode Hparked_valid
        Hsources Hreturned_current) as Hfacts.
      exact (proj2 (proj2 Hfacts)). }
    assert (Hsaved_result : interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
      final_registers.(kernel_save_r0)).
    { rewrite Hreturn_r0, Hcursor_r0, Hr0; split; [exact Hregister_valid|reflexivity]. }
    assert (Hsame : task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) call).
    { unfold task_tcb_init_stack_same_call, armv7a_continuation_resumed_call;
        cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack]; auto. }
    assert (Hhistory : kernel_call_save_history environment critical sg call entry
      (armv7a_continuation_resumed_call suspended call)
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { eapply (KernelCallSaveIRQ environment critical sg arch Extra suffix
        (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False)
        call entry handler suspended suspended registers before irq_input saved_heap
        registry_heap closed_heap returned false call.(os_sched_call_origin)
        restored cursor final_registers after).
      - reflexivity.
      - exact Hmrs.
      - rewrite Hsaved_pc; exact Hpc.
      - exact Hsave.
      - exact Hstores.
      - exact Htrace.
      - exact Hstates.
      - exact Hsources.
      - rewrite Hlease in Hpointers; exact Hpointers.
      - unfold armv7a_continuation_focus_binding, armv7a_call_focus; simpl.
        repeat split; assumption || reflexivity.
      - exact Hlease.
      - reflexivity.
      - reflexivity.
      - exact Hrestore.
      - exact Hcursor_cpsr.
      - exact Hcursor_r0.
      - exact Hcursor_lr.
      - rewrite Hacquired in Hsuffix; exact Hsuffix. }
    assert (Heffect : os_sched_continuation_save_effect environment critical sg call
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0) entry
      (armv7a_continuation_resumed_call suspended call)
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { right; split; assumption. }
    assert (Hcoverage_after : task_stack_live_coverage
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).(TskState)
      (task_stack_call_active_key (armv7a_continuation_resumed_call suspended call))).
    { unfold task_stack_call_active_key, armv7a_continuation_resumed_call;
        cbn [os_sched_call_origin]; rewrite Horigin.
      rewrite Hlease in Hfinal_coverage; exact Hfinal_coverage. }
    split.
    + match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hpost : P |-- Q) end end.
      { unfold os_sched_continuation_save_history_output.
        Exists (armv7a_continuation_resumed_call suspended call)
          (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).
        unfold task_tcb_init_stack_context; entailer!. }
      exact (Hpost after Hafter).
    + intro Hcut.
      assert (Hentry_valid : UCOS2_state_inv sg entry).
      { match type of Hpre with ?P irq_input => assert (Hobserve : P |--
          coq_prop (UCOS2_state_inv sg entry) && TT) end.
        { unfold task_tcb_init_continuation_save_input, task_create_continuation_input;
            entailer!; intros ? ?; exact I. }
        exact (proj1 (Hobserve irq_input Hpre)). }
      assert (Hordinary : task_tcb_init_stack_source_preserved call entry
        (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)))
        by (apply Hsource_preserved; exact Hentry_valid).
      match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hpost : P |-- Q) end end.
      { unfold os_sched_continuation_call_save_history_output.
        Exists (armv7a_continuation_resumed_call suspended call)
          (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).
        unfold task_tcb_init_continuation_restore_input; entailer!. }
      exact (Hpost after Hafter).
Qed.

Lemma os_sched_continuation_restore_irq_history_output :
  forall environment critical saved_local arch Extra
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg entry released node handler suspended publication saved cursor before (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let local := task_tcb_init_irq_local saved_local suspended in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_task_frame_slice suspended ->
  released.(SchedState).(isRunning) = true -> released.(IntrState).(intNesting) = 0 ->
  released.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  released.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  released.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened released.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_sp) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  (task_tcb_init_continuation_restore_input environment critical saved_local sg call saved entry released **
   unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
   frame) before ->
  forall written irq_input saved_heap,
  armv7a_restore_prefix_transition restore cursor before written irq_input ->
  armv7a_save_transition abi handler suspended irq_input saved_heap ->
  exists registry_heap,
    written = kernel_restore_write_cpsr cursor /\
    kernel_heap_writes (armv7a_continuation_save_writes suspended)
      irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg released
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (forall closed_heap,
      @kernel_client_heap_trace Extra (fun _ _ _ _ _ => False) sg
        KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap ->
      exists returned,
        @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg
          KernelClientHeapClosed parked KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg
          call.(os_sched_call_invocation) None call.(os_sched_call_origin)
          parked false call.(os_sched_call_origin) returned /\
        armv7a_irq_restore_pointer_reads sg closed_heap
          (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) suspended.(armv7a_continuation_sp) /\
        (forall irq_return resume_cursor final_cursor after,
          armv7a_restore_transition abi handler suspended closed_heap irq_return ->
          resume_cursor.(kernel_restore_msr_word) = Some
            (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)) ->
          resume_cursor.(kernel_restore_lr) = suspended.(armv7a_continuation_lr) ->
          armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor after ->
          final_cursor.(kernel_restore_return_word) = Some suspended.(armv7a_continuation_lr) /\
          (os_sched_continuation_restore_history_output environment critical saved_local sg call saved released **
           unmap_table_rep sg **
           task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
           frame) after /\
          task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) call /\
          task_tcb_init_stack_return_preserved call released
            (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) /\
          (task_tcb_init_continuation_save_input environment critical saved_local sg
             (armv7a_continuation_resumed_call suspended call) (armv7a_irq_fiq_mask saved)
             (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
           unmap_table_rep sg **
           task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
           frame) after)).
Proof.
  intros environment critical saved_local arch Extra restore sg entry released node handler suspended
    publication saved cursor before frame call abi local parked Horigin Hslice Hrunning Hnesting Hcurrent
    Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hr0 Hmask Hhandler
    Henter Hexit Hpublish Hpre written irq_input saved_heap Hprefix Hsave.
  assert (Hreleased_valid : UCOS2_state_inv sg released).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg released) && TT) end.
    { unfold task_tcb_init_continuation_restore_input, UCOS2_inv;
        entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  assert (Hcoverage : task_stack_live_coverage released.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { match type of Hpre with ?P before => assert (Hobserve : P |--
      coq_prop (task_stack_live_coverage released.(TskState) (task_stack_call_active_key call)) && TT) end.
    { unfold task_tcb_init_continuation_restore_input; entailer!; intros ? ?; exact I. }
    pose proof (proj1 (Hobserve before Hpre)) as Hcovered.
    unfold task_stack_call_active_key in Hcovered; rewrite Horigin in Hcovered; exact Hcovered. }
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended irq_input saved_heap Hsave)
    as [Hsave_source [Hcall [Hbinding [Hsaved_mask [Hpc [Hsaved_sp Hsaved_fragments]]]]]].
  assert (Hlease : suspended.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hbound; rewrite Hcall in Hbound; symmetry; exact Hbound. }
  assert (Habsent : released.(TskState).(parkedTaskStacks)
    (task_stack_key suspended.(armv7a_continuation_stack)) = None) by (rewrite Hlease; exact Hnone).
  match type of Hpre with ?P before => assert (Hrelease_input : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved entry **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (UCOS2_inv sg released ** task_tcb_init_continuation_capsules environment saved_local released **
     unmap_table_rep sg **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) end.
  { unfold task_tcb_init_continuation_restore_input; entailer!. }
  destruct (armv7a_restore_prefix_releases_critical_region _ _ _ _ restore sg call saved entry cursor before
    written irq_input _ Hr0 Hmask (Hrelease_input before Hpre) Hprefix) as [Hwritten [Hmemory Hreleased]].
  match type of Hreleased with ?P irq_input => assert (Hirq_input : P |--
    os_int_exit_frame_save_pre environment.(task_stack_call_external) environment.(task_stack_call_platform) handler **
    (UCOS2_inv sg released **
     store_parked_continuations (kernel_saved_continuation_entry abi released.(TskState) local)
       released.(TskState).(parkedTaskStacks) ** local suspended ** (unmap_table_rep sg ** frame))) end.
  { unfold task_tcb_init_continuation_capsules; fold abi.
    sep_apply_l_atomic (proj1 (task_tcb_init_irq_map_absent _ _ _ abi released.(TskState)
      released.(TskState).(parkedTaskStacks) saved_local suspended Habsent)).
    unfold os_int_exit_frame_save_pre, local.
    rewrite task_tcb_init_irq_local_saved_eq.
    rewrite Hhandler; entailer!. }
  destruct (kernel_irq_save_continuation_resources _ _ _ abi sg released node handler suspended publication
    local (unmap_table_rep sg ** frame) irq_input saved_heap Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen
    Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage (Hirq_input irq_input Hreleased) Hsave)
    as [registry_heap [Hsave_call [Hsave_pc [Hsave_mask [Hwrites [Hstores [Hcovered Hparked]]]]]]].
  fold parked in Hcovered, Hparked.
  assert (Hparked_valid : UCOS2_state_inv sg parked).
  { match type of Hparked with ?P registry_heap => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg parked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve registry_heap Hparked)). }
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask released.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node suspended.(armv7a_continuation_sp)))
    (task_stack_park_fragments released.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      suspended.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hparked_sched : parked.(SchedState) = released.(SchedState)).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  match type of Hparked with ?P registry_heap => assert (Hregistry : P |--
    kernel_client_continuation_world abi local sg parked **
    (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
     frame)) end.
  { unfold kernel_client_continuation_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  exists registry_heap; split; [exact Hwritten|]. split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (kernel_client_continuation_trace_resources _ _ _ Extra abi local critical.(critical_region_clients)
    sg call.(os_sched_call_invocation) None Henter Hexit Hpublish
    KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap _ Htrace parked
    call.(os_sched_call_origin) I (Hregistry registry_heap Hparked))
    as [returned [Hstates [Hsources [Hobserver Hworld]]]].
  destruct (kernel_client_builtin_closed_trace_task_fields Extra sg _ _ _ _ Hstates eq_refl)
    as [Hclosed [Hreturned_tasks Hreturned_sched]].
  assert (Hreturned_current : returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot)).
  { rewrite Hreturned_sched, Hparked_sched; exact Hcurrent. }
  assert (Hreturned_node : returned.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node suspended.(armv7a_continuation_sp))).
  { rewrite Hreturned_tasks, Htasks; cbn [glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask].
    rewrite Z.eqb_refl; reflexivity. }
  assert (Hreturned_lookup : returned.(TskState).(parkedTaskStacks)
    (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
  { rewrite Hreturned_tasks, Htasks, Hlease.
    apply task_stack_park_fragments_lookup. }
  match type of Hworld with ?P closed_heap => assert (Htake_input : P |--
    coq_prop (task_stack_live_coverage returned.(TskState) None) &&
    (UCOS2_inv sg returned **
     store_parked_continuations (kernel_saved_continuation_entry abi returned.(TskState)
       (task_tcb_init_irq_local saved_local suspended)) returned.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
      unmap_table_rep sg ** frame))) end.
  { unfold kernel_client_continuation_resources, kernel_client_continuation_world, local;
      rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Htake_input closed_heap Hworld) as [Hreturned_coverage Htake_owned].
  assert (Htake_current : returned.(SchedState).(curTaskID) =
    Some suspended.(armv7a_continuation_stack).(stackLeaseSlot)) by (rewrite Hlease; exact Hreturned_current).
  assert (Htake_node : returned.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node suspended.(armv7a_continuation_sp))) by (rewrite Hlease; exact Hreturned_node).
  assert (Htake_gen : (task_set_saved_sp node suspended.(armv7a_continuation_sp)).(taskGeneration) =
    suspended.(armv7a_continuation_stack).(stackLeaseGeneration)) by (rewrite Hlease; exact Hgen).
  assert (Htake_address : tcb_field_address
    (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) by (rewrite Hlease; exact Haddress).
  destruct (task_tcb_init_irq_take_resources _ _ _ abi sg returned saved_local suspended call
    (task_set_saved_sp node suspended.(armv7a_continuation_sp)) _ closed_heap Hcall Htake_current Htake_node
    Htake_gen Hreturned_lookup Htake_address Hreturned_coverage Htake_owned)
    as [Hpointers [Hreads [Hfinal_coverage Htake_resources]]].
  exists returned; split; [exact Hstates|]. split; [exact Hsources|]. split.
  - rewrite Hlease in Hpointers; exact Hpointers.
  - intros irq_return resume_cursor final_cursor after Hrestore Hword Hlr Hsuffix.
    match type of Htake_resources with ?P closed_heap => assert (Hrestore_input : P |--
      interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
      task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
        suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
      (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack)) **
       task_tcb_init_continuation_capsules environment saved_local
         (os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack)) **
       unmap_table_rep sg ** frame)) end.
    { unfold task_tcb_init_continuation_capsules; entailer!. }
    destruct (armv7a_restore_call_resources _ _ _ abi handler suspended call _ closed_heap irq_return
      Hcall Hreads (Hrestore_input closed_heap Htake_resources) Hrestore) as [Hirq_memory Hirq_owned].
    assert (Hcomputed_mask : armv7a_irq_fiq_mask
      (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)) =
      armv7a_irq_fiq_mask saved) by (rewrite armv7a_cpsr_restore_mask_eq, Hr0; reflexivity).
    rewrite Hsaved_mask, Hhandler in Hirq_owned.
    rewrite <- Hcomputed_mask in Hirq_owned.
    match type of Hirq_owned with ?P irq_return => assert (Hsuffix_input : P |--
      kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
        (armv7a_continuation_resumed_call suspended call)
        (armv7a_irq_fiq_mask
          (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0))) **
      (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack)) **
       task_tcb_init_continuation_capsules environment saved_local
         (os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack)) **
       unmap_table_rep sg **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame))
      by entailer! end.
    destruct (armv7a_restore_suffix_transports_owned_execution _ _ _ _ restore
      (armv7a_continuation_resumed_call suspended call) _ resume_cursor irq_return final_cursor after _
      Hword (Hsuffix_input irq_return Hirq_owned) Hsuffix) as [Hcursor [Hafter_memory Hafter]].
    rewrite Hcomputed_mask, Hlease in Hafter.
    assert (Hcurrent_valid : UCOS2_state_inv sg
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { match type of Hafter with ?P after => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg
        (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))) && TT) end.
      { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
      exact (proj1 (Hobserve after Hafter)). }
    assert (Hpreserved : task_tcb_init_stack_return_preserved call released
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { eapply task_tcb_init_stack_irq_return_preserved; eassumption. }
    assert (Hcall_preserved : task_tcb_init_call_preserved sg call.(os_sched_call_invocation) released
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { eapply task_tcb_init_irq_preserves_call; eassumption. }
    assert (Hordinary : UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved call released
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { intro Hvalid; exact (proj2 (proj2 Hpreserved)). }
    split.
    + rewrite Hcursor; cbn [kernel_restore_branch_lr kernel_restore_return_word]; rewrite Hlr; reflexivity.
    + assert (Hsame : task_tcb_init_stack_same_call
        (armv7a_continuation_resumed_call suspended call) call).
      { unfold task_tcb_init_stack_same_call, armv7a_continuation_resumed_call;
          cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack];
          repeat split; try reflexivity; exact Hlease. }
      match type of Hafter with ?P after => assert (Hsource_pack : P |--
        task_tcb_init_continuation_save_input environment critical saved_local sg
          (armv7a_continuation_resumed_call suspended call) (armv7a_irq_fiq_mask saved)
          (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
        unmap_table_rep sg **
        task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
        frame) end.
      { unfold task_tcb_init_continuation_save_input, task_create_continuation_input,
          task_stack_call_active_key, armv7a_continuation_resumed_call, critical_region_outside.
        cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
        rewrite Hlease, Horigin, critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
        rewrite Hlease in Hfinal_coverage.
        unfold task_tcb_init_continuation_capsules, UCOS2_inv; entailer!. }
      pose proof (Hsource_pack after Hafter) as Hcurrent_owned.
      assert (Hhistory : kernel_call_restore_history environment critical sg call released
        (armv7a_continuation_resumed_call suspended call)
        (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
      { eapply (KernelCallRestoreIRQ environment critical sg arch Extra restore
          (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False)
          call released handler suspended suspended cursor before written irq_input saved_heap
          registry_heap closed_heap returned false call.(os_sched_call_origin)
          irq_return resume_cursor final_cursor after).
        - reflexivity.
        - exact Hprefix.
        - exact Hsave.
        - exact Hstores.
        - exact Htrace.
        - exact Hstates.
        - exact Hsources.
        - rewrite Hlease in Hpointers; exact Hpointers.
        - unfold armv7a_continuation_focus_binding, armv7a_call_focus; simpl.
          repeat split; assumption || reflexivity.
        - exact Hlease.
        - reflexivity.
        - reflexivity.
        - exact Hrestore.
        - exact Hword.
        - exact Hlr.
        - exact Hsuffix. }
      assert (Heffect : os_sched_continuation_restore_effect environment critical sg call released
        (armv7a_continuation_resumed_call suspended call)
        (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)))
        by (right; exact Hhistory).

      split.
      * match type of Hcurrent_owned with ?P after => match goal with |- ?Q after =>
          assert (Hlegacy : P |-- Q) end end.
        { unfold os_sched_continuation_restore_history_output.
          Exists (armv7a_continuation_resumed_call suspended call)
            (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)); entailer!. }
        exact (Hlegacy after Hcurrent_owned).
      * split; [exact Hsame|]. split; [exact Hpreserved|exact Hcurrent_owned].
Qed.


