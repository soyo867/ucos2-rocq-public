Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual registered C clients and hook preserve this invocation's
    wait projection. This is an explicit module R/G interpretation, not a
    fact supplied by ARM or by bare registration. *)
Definition sem_pend_sched_clients environment critical : Prop :=
  (forall action, critical.(critical_region_clients) action ->
    sem_pend_projected_source_client action) /\
  sem_pend_projected_source_client environment.(task_stack_call_external).(os_sched_hook_action).

(** The existing pure ready/current consumer is reproduced from
    sem_pend_wait_selected_from_ready_current without importing its legacy
    physical-ISA source families. Its statement and proof obligations are
    unchanged; this C instance consumes it directly below. *)
Lemma sem_pend_sched_selected_from_ready_current : forall environment critical sg original mask initial
  observed eid timeout waiting call current,
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call current ->
  UCOS2_state_inv sg current ->
  current.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  In original.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList) ->
  sem_pend_wait_selected_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call current.
Proof.
  intros * Hwait Hvalid Hcurrent Hmember; split; [exact Hwait|].
  destruct Hwait as [owned [Howned [Hsame [Hinitial Hpath]]]].
  destruct (sem_pend_observed_wait_history_waiter _ _ _ _ _ _ _ _ _ _ Hinitial)
    as [first [Hfirst Hcontinuation]].
  destruct (sem_pend_wait_source_history_preserves_waiter _ _ _ _ _ _ _ _ Hpath
    first Hfirst Hcontinuation) as [last [Hlast Hlast_wait]].
  pose proof Hvalid as [_ [_ [[Hready _] _]]].
  destruct (proj1 Hready _ Hmember) as [node [Hnode [Hpriority Heffective]]].
  assert (node = last) by congruence; subst node.
  destruct (sem_pend_wait_ready_resume_registration _ _ _ Hlast_wait Heffective)
    as [Hregistration Hgeneration].
  exists last; unfold sem_pend_resume_entry; auto.
Qed.

(** Keep the actual C Scheduler relation in the existing wait history.
    No source/ISA execution family is reconstructed at this C boundary. *)
Lemma sem_pend_wait_at_c_scheduler : forall environment critical sg original mask initial
  observed eid timeout waiting entered entry returned released,
  sem_pend_sched_clients environment critical ->
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting entered entry ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry entered returned released ->
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting returned released.
Proof.
  intros * [Hclients Hhook] [owned [Howned [Hsame [Hinitial Hpath]]]] Hbody.
  inversion Howned; subst owned.
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hreturned.
  exists environment; split; [reflexivity|]. split.
  - unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence.
  - split; [exact Hinitial|]. eapply SemPendWaitSourceTrans; [exact Hpath|].
    eapply SemPendWaitSourceCScheduler; eassumption.
Qed.

(** Selection and same-call current identity are independent facts. The
    nonswitch case is proved from the actual cache and C selection guard.
    On a switch, the explicit C/RG endpoint certificate concerns the very
    returned state. It is not inferred from the architecture resume token. *)
Lemma sem_pend_sched_body_selected : forall environment critical sg original mask initial
  observed eid timeout waiting entered entry returned released,
  sem_pend_sched_clients environment critical ->
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting entered entry ->
  sem_pend_wait_sched_entry sg entered entry ->
  UCOS2_state_inv sg entry -> UCOS2_state_inv sg released ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry entered returned released ->
  (os_sched_requests_switch entry = true ->
    In entered.(os_sched_call_stack).(stackLeaseSlot) released.(SchedState).(readyList)) ->
  sem_pend_wait_selected_at (Some environment) critical sg original mask initial observed eid timeout
    waiting returned released.
Proof.
  intros * Hclients Hwait [Hcut [Henabled [Hsource [Hblocking Hcache]]]] Hvalid Hvalid'
    Hbody Hswitch_ready.
  pose proof (sem_pend_wait_at_c_scheduler _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hclients Hwait Hbody) as Hwait'.
  assert (Hreturned_source : kernel_call_task_source returned released).
  { eapply os_sched_continuation_c_return_source; [|exact Hbody|exact Hsource].
    intro Hswitch; exact (proj1 (proj2 Hcut Hswitch)). }
  pose proof (kernel_call_task_source_current_at returned released Hreturned_source)
    as [Hcurrent Hnode].
  pose proof Hwait as [owned [Howned [Hsame Hrest]]].
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hreturned.
  assert (Hready : In entered.(os_sched_call_stack).(stackLeaseSlot) released.(SchedState).(readyList)).
  { destruct (os_sched_requests_switch entry) eqn:Hswitch; [apply Hswitch_ready; reflexivity|].
    pose proof Hbody as Hnonswitch; unfold os_sched_c_return in Hnonswitch; rewrite Hswitch in Hnonswitch.
    destruct Hnonswitch as [-> ->].
    destruct (os_sched_nonswitch_current_ready_at sg entered entry Hvalid Hsource Hcache Henabled
      Hswitch (proj1 Hcut Henabled)) as [node [[Hlookup [Hcur [Hprio [Hin Hnode_ready]]]] Hgen]].
    exact Hin. }
  eapply sem_pend_sched_selected_from_ready_current; [exact Hwait'|exact Hvalid'| |].
  - rewrite (proj2 (proj2 Hreturned)), (proj2 (proj2 Hsame)) in Hcurrent; exact Hcurrent.
  - rewrite (proj2 (proj2 Hsame)) in Hready; exact Hready.
Qed.

(** The specialized summaries are direct consumers of the common modular
    Save/Restore resource contracts. Extra pure clauses belong to the C
    module environment; no platform definition is changed. *)
Definition sem_pend_sched_save_input phase environment critical saved_local sg call mask state : Assertion :=
  coq_prop (sem_pend_restore_phase_pre phase (Some environment) critical sg call mask state) &&
  (task_tcb_init_continuation_save_input environment critical saved_local sg call mask state **
    unmap_table_rep sg).

Definition sem_pend_sched_save_output phase environment critical saved_local sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
      task_tcb_init_stack_source_preserved original before acquired /\
      sem_pend_sched_clients environment critical /\
      sem_pend_restore_phase_pre phase (Some environment) critical sg returned mask acquired) &&
    (task_tcb_init_continuation_restore_input environment critical saved_local sg returned saved acquired acquired **
      unmap_table_rep sg).

Definition sem_pend_sched_restore_input phase environment critical saved_local sg call saved acquired released : Assertion :=
  match phase with
  | SemPendWaitPhase original mask initial observed eid timeout waiting =>
      coq_prop (sem_pend_wait_selected_at (Some environment) critical sg original mask initial
        observed eid timeout waiting call released) &&
      (task_tcb_init_continuation_restore_input environment critical saved_local sg call saved acquired released **
        unmap_table_rep sg)
  | _ => coq_prop False && emp
  end.

Definition sem_pend_sched_restore_output phase environment critical saved_local sg call saved
  (released : UCOS2_Verify_State) : Assertion :=
  match phase with
  | SemPendWaitPhase original mask initial observed eid timeout waiting =>
      EX returned current,
        coq_prop (kernel_stack_call_same_call returned call /\
          sem_pend_wait_selected_at (Some environment) critical sg original mask initial
            observed eid timeout waiting returned current) &&
        (task_tcb_init_continuation_save_input environment critical saved_local sg returned
          (armv7a_irq_fiq_mask saved) current ** unmap_table_rep sg)
  | _ => coq_prop False && emp
  end.

Definition sem_pend_sched_switch_output phase environment critical saved_local sg call saved acquired entry : Assertion :=
  EX returned current,
    coq_prop (os_sched_c_return environment.(task_stack_call_external) critical sg entry call returned current /\
      UCOS2_state_inv sg current) &&
    sem_pend_sched_restore_input phase environment critical saved_local sg returned saved acquired current.

Definition sem_pend_sched_switch_input phase environment critical saved_local sg call mask saved acquired entry : Assertion :=
  coq_prop (sem_pend_sched_clients environment critical /\ interrupt_saved_value mask saved /\
    UCOS2_state_inv sg entry /\
    sem_pend_restore_phase_pre phase (Some environment) critical sg call mask entry) &&
  os_sched_continuation_switch_pre environment critical saved_local kernel_program_inv
    sg call saved acquired entry.

Lemma sem_pend_sched_call_save_input : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting call mask before,
  sem_pend_continuation_phase_sched_input (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
    critical saved_local sg call mask before |--
  coq_prop (os_sched_call_cut sg call before) &&
  sem_pend_sched_save_input (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical saved_local sg call mask before.
Proof.
  intros; cbn [sem_pend_continuation_phase_sched_input sem_pend_continuation_sched_input].
  unfold os_sched_continuation_pre; Intros.
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg call mask before)).
  unfold sem_pend_sched_save_input, sem_pend_restore_phase_pre.
  unfold sem_pend_wait_sched_entry in *; entailer!.
Qed.

Lemma sem_pend_sched_modular_save_output : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting call mask saved before,
  sem_pend_sched_clients environment critical -> kernel_tcb_stack_field_layout sg ->
  UCOS2_state_inv sg before ->
  sem_pend_restore_phase_pre (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask before ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_blocking_rely
    sg call mask saved before |--
  sem_pend_sched_save_output (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical saved_local sg call mask saved before.
Proof.
  intros * Hclients Hlayout Hvalid [Hmask [Hwait Hentry]].
  unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return call before returned acquired) by tauto.
  pose proof (proj1 Hnormal) as Hsame.
  assert (Hrely : sem_pend_blocking_rely sg before acquired) by tauto.
  pose proof Hsave as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call before returned acquired)
    by (split; assumption).
  pose proof (sem_pend_wait_at_modular_return _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (proj1 Hclients) Hwait Hhistory) as Hwait'.
  pose proof (sem_pend_wait_sched_entry_modular_return environment critical sg call before returned acquired
    Hlayout Hvalid (proj1 (proj2 (proj2 Hentry))) Hentry Hhistory Hrely) as Hentry'.
  assert (Hpreserved : task_tcb_init_stack_source_preserved call before acquired).
  { eapply task_tcb_init_stack_registered_source_preserved; [exact Hvalid|exact (proj1 Hnormal)|exact Htrace]. }
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_restore_input_masked_world
    environment critical saved_local sg returned saved acquired acquired)).
  unfold sem_pend_sched_save_output; Exists returned acquired.
  unfold sem_pend_restore_phase_pre; entailer!.
Qed.

(** The switch's C/RG endpoint is explicit. The common body relation
    already contains the actual C selector/hook and later registered
    interval. Readiness of the normally resumed original caller must be
    justified by the selected C scheduling/environment protocol; it is
    neither an ARM fact nor a consequence of a mere current pointer. *)
Lemma sem_pend_sched_modular_switch_output : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting call mask saved acquired entry,
  sem_pend_sched_clients environment critical -> UCOS2_state_inv sg entry ->
  sem_pend_restore_phase_pre (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask entry ->
  (forall returned current,
    os_sched_c_return environment.(task_stack_call_external) critical sg entry call returned current ->
    os_sched_requests_switch entry = true ->
    In call.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList)) ->
  os_sched_continuation_body_post environment critical saved_local kernel_program_inv
    sg call saved acquired entry |--
  sem_pend_sched_switch_output (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical saved_local sg call saved acquired entry.
Proof.
  intros * Hclients Hvalid [Hmask [Hwait Hentry]] Hready.
  sep_apply_l_atomic (os_sched_continuation_body_restore_input
    environment critical saved_local sg call saved acquired entry).
  Intros returned current.
  assert (Hbody : os_sched_c_return environment.(task_stack_call_external) critical sg entry call returned current)
    by tauto.
  assert (Hvalid' : UCOS2_state_inv sg current) by tauto.
  pose proof (sem_pend_sched_body_selected _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hclients Hwait Hentry Hvalid Hvalid' Hbody (Hready returned current Hbody)) as Hselected.
  unfold sem_pend_sched_switch_output; Exists returned current.
  cbn [sem_pend_sched_restore_input]; entailer!.
Qed.

Lemma sem_pend_sched_nonswitch_selected : forall environment critical sg original initial_mask initial
  observed eid timeout waiting call mask entry,
  sem_pend_sched_clients environment critical -> UCOS2_state_inv sg entry ->
  sem_pend_restore_phase_pre (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask entry ->
  os_sched_requests_switch entry = false ->
  sem_pend_wait_selected_at (Some environment) critical sg original initial_mask initial observed eid timeout
    waiting call (os_sched_prefix_state entry).
Proof.
  intros * Hclients Hvalid [Hmask [Hwait Hentry]] Hswitch.
  eapply sem_pend_sched_body_selected; try eassumption.
  - apply os_sched_ready_checkpoint_preserves_validity; exact Hvalid.
  - unfold os_sched_c_return; rewrite Hswitch; auto.
  - congruence.
Qed.

Lemma sem_pend_sched_modular_restore_output : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting call saved released,
  sem_pend_sched_clients environment critical ->
  sem_pend_wait_selected_at (Some environment) critical sg original initial_mask initial observed eid timeout
    waiting call released ->
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_save_rely
    sg call (armv7a_irq_fiq_mask saved) released |--
  sem_pend_sched_restore_output (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical saved_local sg call saved released.
Proof.
  intros * Hclients Hselected.
  unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call released returned current)
    by (unfold sem_pend_modular_call_history; tauto).
  pose proof (proj1 (proj2 Hhistory)) as Hsame.
  assert (Hrely : sem_pend_save_rely sg released current) by tauto.
  pose proof (sem_pend_wait_selected_modular_return _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (proj1 Hclients) Hselected Hhistory Hrely) as Hselected'.
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current)).
  cbn [sem_pend_sched_restore_output]; Exists returned current; entailer!.
Qed.

Lemma sem_pend_sched_restore_output_return : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting context scheduled returned mask saved before entry released,
  task_tcb_init_stack_same_call scheduled context ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry scheduled returned released ->
  interrupt_saved_value mask saved ->
  sem_pend_sched_restore_output (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical saved_local sg returned saved released |--
  sem_pend_continuation_phase_sched_output (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
    critical saved_local sg context mask before.
Proof.
  intros * Hscheduled Hbody Hsaved.
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hreturned.
  cbn [sem_pend_sched_restore_output]; Intros final current.
  assert (Hsame : kernel_stack_call_same_call final context).
  { assert (Hfinal : kernel_stack_call_same_call final returned) by tauto.
    unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  rewrite (proj2 Hsaved).
  sep_apply_l_atomic (proj2 (sem_pend_continuation_save_input_owned
    environment critical saved_local sg final mask current)).
  cbn [sem_pend_continuation_phase_sched_output]; Exists final current; entailer!.
Qed.

(** The optional public descriptor is opened once at the real blocking
    call. Its external/platform equalities select the SAME resource
    interpretation used by this Scheduler instance. Static C symbol
    bindings remain the selected program's separate layout parameter. *)
Lemma sem_pend_sched_input_environment : forall external platform environment critical saved_local
  sg original initial_mask initial observed eid timeout waiting call mask before,
  sem_pend_continuation_phase_sched_input (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    external platform environment critical saved_local sg call mask before |--
  EX owned,
    coq_prop (environment = Some owned /\ owned.(task_stack_call_external) = external /\
      owned.(task_stack_call_platform) = platform) &&
    sem_pend_continuation_phase_sched_input (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
      owned.(task_stack_call_external) owned.(task_stack_call_platform) (Some owned)
      critical saved_local sg call mask before.
Proof.
  intros external platform [owned|]; intros;
    cbn [sem_pend_continuation_phase_sched_input sem_pend_continuation_sched_input].
  - Exists owned; entailer!.
  - entailer!.
Qed.
