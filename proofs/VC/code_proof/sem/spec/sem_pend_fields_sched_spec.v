Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.flag_fields_resources.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This is the actual SemPend waiting protocol from OS_Sched_Sem.c.
    A semaphore waiter is neither a Flag Waiting node nor a Fresh caller.
    Only its existing Wait phase can call this instance. *)
Definition sem_pend_fields_phase_sched_input phase environment local critical sg call mask before : Assertion :=
  match phase with
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      coq_prop (sem_pend_restore_phase_pre phase (Some environment) critical sg call mask before) &&
      sem_pend_fields_closed environment local sg call mask before
  | _ => coq_prop False && emp
  end.

Definition sem_pend_fields_phase_sched_output phase environment critical sg call mask before : Assertion :=
  match phase with
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      EX returned current next_local,
        coq_prop (os_sched_continuation_call_history environment critical sg call mask before returned current /\
          kernel_stack_call_same_call returned call /\
          sem_pend_wait_selected_at (Some environment) critical sg original initial_mask initial observed
            eid timeout waiting returned current) &&
        sem_pend_fields_closed environment next_local sg returned mask current
  | _ => coq_prop False && emp
  end.

Definition sem_pend_fields_sched_save_output phase environment local critical sg call mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (kernel_call_save_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical sg call returned mask saved before acquired /\
      kernel_call_normal_return call before returned acquired /\
      sem_pend_blocking_rely sg before acquired /\
      sem_pend_restore_phase_pre phase (Some environment) critical sg returned mask acquired) &&
    sem_pend_fields_masked environment local critical sg returned saved acquired acquired.

Lemma sem_pend_fields_sched_input_cut : forall environment local critical sg original initial_mask initial
  observed eid timeout waiting call mask before,
  sem_pend_fields_phase_sched_input
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment local critical sg call mask before |--
  coq_prop (os_sched_call_cut sg call before /\
    sem_pend_restore_phase_pre
      (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
      (Some environment) critical sg call mask before) &&
  sem_pend_fields_closed environment local sg call mask before.
Proof.
  intros; cbn [sem_pend_fields_phase_sched_input].
  unfold sem_pend_restore_phase_pre, sem_pend_wait_sched_entry; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_sched_modular_save_output : forall environment local critical sg original
  initial_mask initial observed eid timeout waiting call mask saved before,
  sem_pend_sched_clients environment critical -> kernel_tcb_stack_field_layout sg ->
  UCOS2_state_inv sg before ->
  sem_pend_restore_phase_pre
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask before ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    kernel_program_fields_inv local critical sem_pend_blocking_rely sg call mask saved before |--
  sem_pend_fields_sched_save_output
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment local critical sg call mask saved before.
Proof.
  intros * Hclients Hlayout Hvalid [Hmask [Hwait Hentry]].
  unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return call before returned acquired) by tauto.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call before returned acquired)
    by (split; [exact (proj1 Hsave)|exact Hnormal]).
  assert (Hrely : sem_pend_blocking_rely sg before acquired) by tauto.
  pose proof (sem_pend_wait_at_modular_return environment critical sg original initial_mask initial
    observed eid timeout waiting call before returned acquired (proj1 Hclients) Hwait Hhistory) as Hwait'.
  pose proof (sem_pend_wait_sched_entry_modular_return environment critical sg call before returned acquired
    Hlayout Hvalid (proj1 (proj2 (proj2 Hentry))) Hentry Hhistory Hrely) as Hentry'.
  unfold sem_pend_fields_sched_save_output; Exists returned acquired.
  cbn [sem_pend_restore_phase_pre]; unfold sem_pend_fields_masked; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

(** This consumes one ACTUAL source endpoint. The switch branch's ready
    receipt must come from that endpoint's source producer. There is no
    quantified assertion that all future Scheduler returns are ready. *)
Lemma sem_pend_fields_sched_body_selected : forall environment local critical sg original
  initial_mask initial observed eid timeout waiting entered entry returned released saved acquired,
  sem_pend_sched_clients environment critical ->
  UCOS2_state_inv sg entry ->
  sem_pend_wait_at (Some environment) critical sg original initial_mask initial observed eid timeout
    waiting entered entry ->
  sem_pend_wait_sched_entry sg entered entry ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry entered returned released ->
  (os_sched_requests_switch entry = true ->
    In entered.(os_sched_call_stack).(stackLeaseSlot) released.(SchedState).(readyList)) ->
  sem_pend_fields_masked environment local critical sg returned saved acquired released |--
  coq_prop (sem_pend_wait_selected_at (Some environment) critical sg original initial_mask initial observed
    eid timeout waiting returned released) &&
  sem_pend_fields_masked environment local critical sg returned saved acquired released.
Proof.
  intros * Hclients Hvalid Hwait Hentry Hbody Hready.
  prop_apply_p (sem_pend_fields_masked_observations environment local critical sg
    returned saved acquired released); Intros.
  assert (Hvalid' : UCOS2_state_inv sg released) by tauto.
  pose proof (sem_pend_sched_body_selected environment critical sg original initial_mask initial
    observed eid timeout waiting entered entry returned released
    Hclients Hwait Hentry Hvalid Hvalid' Hbody Hready) as Hselected.
  repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

(** Compose the real initial Save, Scheduler C body, and final generic
    Restore. The local supplied here is the actual body-return family;
    it is existential in the complete Scheduler post. *)
Lemma sem_pend_fields_sched_restore_return : forall environment local critical sg original initial_mask
  initial observed eid timeout waiting call scheduled resumed mask saved before entry released,
  sem_pend_sched_clients environment critical ->
  kernel_call_save_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical sg call scheduled mask saved before entry ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry scheduled resumed released ->
  sem_pend_wait_selected_at (Some environment) critical sg original initial_mask initial observed
    eid timeout waiting resumed released ->
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    kernel_program_fields_inv local critical sem_pend_save_rely sg resumed mask released |--
  sem_pend_fields_phase_sched_output
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical sg call mask before.
Proof.
  intros * Hclients Hsave Hbody Hselected.
  unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hrestore : sem_pend_modular_call_history environment critical sg resumed released returned current)
    by (unfold sem_pend_modular_call_history; tauto).
  assert (Hrely : sem_pend_save_rely sg released current) by tauto.
  pose proof (sem_pend_wait_selected_modular_return environment critical sg original initial_mask
    initial observed eid timeout waiting resumed released returned current
    (proj1 Hclients) Hselected Hrestore Hrely) as Hselected'.
  assert (Hhistory : os_sched_continuation_call_history environment critical sg call mask before returned current).
  { exists scheduled, entry, resumed, released, saved.
    split; [left; exact Hsave|]. split; [exact Hbody|].
    left; split; [exact (proj1 Hrestore)|exact (proj1 (proj2 Hrestore))]. }
  pose proof (os_sched_continuation_call_history_same_call environment critical sg
    call mask before returned current Hhistory) as Hsame.
  cbn [sem_pend_fields_phase_sched_output]; Exists returned current local.
  unfold sem_pend_fields_closed; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_sched_return_save_input : forall environment critical sg original initial_mask initial
  observed eid timeout waiting call mask before,
  mask = initial_mask ->
  sem_pend_fields_phase_sched_output
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical sg call mask before |--
  EX returned current next_local,
    coq_prop (os_sched_continuation_call_history environment critical sg call mask before returned current /\
      kernel_stack_call_same_call returned call) &&
    sem_pend_fields_phase_save_input
      (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
      environment next_local critical sg returned mask current.
Proof.
  intros * Hmask; cbn [sem_pend_fields_phase_sched_output]; Intros returned current next_local.
  Exists returned current next_local.
  unfold sem_pend_fields_phase_save_input; cbn [sem_pend_save_phase_pre]; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.
