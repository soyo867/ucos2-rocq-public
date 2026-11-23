Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A published initial task has no suspended C call and needs no saved
    local owner. Each Some entry keeps the resource supplied at its real
    save cut. The parameter may distinguish Scheduler and IRQ cuts; no
    Scheduler mask, return PC or inside token is imposed on an IRQ. *)
Definition task_create_continuation_local
  (saved_local : Armv7aContinuation -> Assertion) (descriptor : Armv7aContinuation) : Assertion :=
  match descriptor.(armv7a_continuation_call) with
  | None => emp
  | Some _ => saved_local descriptor
  end.

(** The current callable world has exactly one parked continuation map.
    Its entries retain their local resources; the old weak map is never
    an intermediate representation of this contract. *)
Definition task_create_continuation_input environment critical saved_local sg call mask state : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\
    task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) call mask **
   critical_region_outside critical sg call.(os_sched_call_invocation) state **
   store_parked_continuations
     (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
       state.(TskState) (task_create_continuation_local saved_local))
     state.(TskState).(parkedTaskStacks)).

Definition task_create_continuation_pre environment critical saved_local sg region args task_return
  lower old_frame upper initial_name call mask initial : Assertion :=
  coq_prop (task_create_stack_entry sg args initial_name call initial /\
    task_create_stack_buffer_domain region args task_return lower old_frame upper) &&
  (task_create_continuation_input environment critical saved_local sg call mask initial **
   task_stack_storage region (lower ++ old_frame ++ upper) ** unmap_table_rep sg).

(** The original result domain and failure-buffer alternatives are kept.
    A successful publication transfers the buffer to the kernel. No
    survival/readiness of the new child at eventual return is promised. *)
Definition task_create_continuation_post environment critical saved_local sg region args task_return
  lower old_frame upper original mask result : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\ UCOS2_state_inv sg current /\
      (result = 0 \/ result = 40 \/ result = 42 \/ result = 60 \/ result = 66)) &&
    (task_create_continuation_input environment critical saved_local sg returned mask current **
     unmap_table_rep sg **
     (if Z.eq_dec result 0 then emp else
       EX initialized, task_create_stack_failure_buffer region args task_return
         lower old_frame upper initialized)).

Lemma task_create_continuation_input_closed_world :
  forall environment critical saved_local sg call mask state,
  task_create_continuation_input environment critical saved_local sg call mask state **
    unmap_table_rep sg --||--
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) sg
    (task_stack_call_active_key call) call mask state.
Proof.
  intros; unfold task_create_continuation_input, kernel_continuation_call_closed,
    kernel_continuation_inv, critical_region_outside.
  rewrite kernel_program_inv_split_unmap, critical_region_outside_without_running_rep,
    <- UCOS2_raw_rep_split_running.
  unfold UCOS2_inv; split; entailer!.
Qed.

(** Both no-switch and actual restored-Some source consumers finish at
    this same public post. Its world is obtained from the source endpoint,
    not by strengthening an earlier weak callee post. *)
Lemma task_create_continuation_closed_returns_success :
  forall environment critical saved_local sg original returned mask state
    region args task_return lower old_frame upper,
  task_tcb_init_stack_same_call returned original ->
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) sg
    (task_stack_call_active_key returned) returned mask state |--
  task_create_continuation_post environment critical saved_local sg region args task_return
    lower old_frame upper original mask 0.
Proof.
  intros environment critical saved_local sg original returned mask state
    region args task_return lower old_frame upper Hsame.
  rewrite <- task_create_continuation_input_closed_world.
  unfold task_create_continuation_input; Intros.
  unfold task_create_continuation_post; Exists returned state.
  destruct (Z.eq_dec 0 0); [|contradiction].
  unfold task_create_continuation_input; entailer!.
Qed.

(** One actual source path: the five TCB publication stores deposit the
    initialized None frame, final TCB Restore returns the new whole map,
    and Scheduler Save/the real no-switch C prefix/Restore consume it.
    The new child supplies the nonempty-ready fact. All other saved local
    owners stay in the same map throughout these instructions.

    This is the uninterrupted no-switch source branch. The conditional
    source transitions below describe actual endpoints; they do not assume
    future termination, an arbitrary interrupt return or a new ABI law. *)
Lemma task_create_continuation_publication_nonswitch_source :
  forall environment critical saved_local arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg publication state call saved acquired before old_frame (frame : Assertion),
  let local := task_create_continuation_local saved_local in
  let args := task_create_stack_publication_args publication in
  let published := task_create_stack_publication_state sg publication state in
  UCOS2_state_inv sg state ->
  task_create_stack_publication_input sg publication state ->
  task_create_call_stage call state ->
  task_stack_live_coverage state.(TskState) (task_stack_call_active_key call) ->
  0 <= args.(initPrio) < 64 ->
  0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296 ->
  (task_tcb_init_publication_tail_storage sg args state
     publication.(stack_publication_slot) publication.(stack_publication_image) **
   task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
   store_parked_continuations
     (kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState) local)
     state.(TskState).(parkedTaskStacks) **
   (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved acquired **
    task_tcb_init_stack_context environment call ** unmap_table_rep sg ** frame)) before ->
  exists publication_heap,
    task_tcb_init_publication_tail_fragment sg args.(initPrio)
      (task_slot_addr sg publication.(stack_publication_slot)) before publication_heap /\
    kernel_client_step (task_create_stack_publication_client publication) sg state published /\
    task_create_call_stage call published /\
    (forall tcb_cursor tcb_written tcb_middle tcb_final returned_heap,
      tcb_cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask tcb_cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore tcb_cursor publication_heap tcb_written tcb_middle ->
      armv7a_restore_suffix_transition restore tcb_written tcb_middle tcb_final returned_heap ->
      kernel_call_restore_uninterrupted_execution arch tcb_cursor publication_heap tcb_final returned_heap /\
      (task_create_continuation_input environment critical saved_local sg call
         (armv7a_irq_fiq_mask saved) published ** unmap_table_rep sg ** frame) returned_heap /\
      (forall registers final_registers sched_acquired saved_heap,
        published.(SchedState).(isRunning) = true ->
        registers.(kernel_save_return_word) = None ->
        valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
        os_sched_requests_switch published = false ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) published returned_heap
          final_registers sched_acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers published returned_heap
          final_registers sched_acquired saved_heap /\
        sched_acquired = published /\
        exists prefix_heap,
          os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
          (forall cursor written middle final_cursor after,
            cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
            armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
            armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
            armv7a_restore_suffix_transition restore written middle final_cursor after ->
            kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
            (task_create_continuation_post environment critical saved_local sg
              publication.(stack_publication_region) publication.(stack_publication_args)
              publication.(stack_publication_return) publication.(stack_publication_lower)
              old_frame publication.(stack_publication_upper) call (armv7a_irq_fiq_mask saved) 0 ** frame) after))).
Proof.
  intros environment critical saved_local arch save restore sg publication state call saved acquired
    before old_frame frame local args published Hvalid Hinput Hstage Hcoverage Hpriority Hpointer Hpre.
  set (retained := critical_region_masked environment.(task_stack_call_platform) critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    task_tcb_init_stack_context environment call ** frame).
  assert (Hinitial : local (task_create_stack_publication_continuation publication) = emp)
    by reflexivity.
  match type of Hpre with ?P before => assert (Hopen : P |--
    task_tcb_init_publication_tail_storage sg args state publication.(stack_publication_slot)
      publication.(stack_publication_image) **
    (task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
     local (task_create_stack_publication_continuation publication) **
     store_parked_continuations
       (kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState) local)
       state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** retained)) end.
  { rewrite Hinitial; unfold retained; entailer!. }
  destruct (kernel_task_publication_continuation_produces _ _ _
    environment.(task_stack_call_continuations) sg publication state local (task_stack_call_active_key call)
    retained before Hvalid Hinput Hcoverage Hpriority Hpointer (Hopen before Hpre))
    as [publication_heap [Hstores [Hstep [Hcovered Hpublished]]]].
  fold published in Hstep, Hcovered, Hpublished.
  pose proof (task_create_publication_preserves_call_stage sg publication state call Hvalid Hinput Hstage)
    as Hstage_published.
  fold published in Hstage_published.
  assert (Hmasked : (kernel_continuation_call_masked environment.(task_stack_call_continuations)
    kernel_program_inv local critical sg (task_stack_call_active_key call) call saved acquired published **
    frame) publication_heap).
  { match type of Hpublished with ?P publication_heap => match goal with |- ?Q publication_heap =>
      assert (Hclose : P |-- Q) end end.
    { unfold kernel_continuation_call_masked, kernel_continuation_inv,
        retained, task_tcb_init_stack_context; entailer!. }
    exact (Hclose publication_heap Hpublished). }
  exists publication_heap; split; [exact Hstores|]. split; [exact Hstep|].
  split; [exact Hstage_published|].
  intros tcb_cursor tcb_written tcb_middle tcb_final returned_heap Hr0 Hmask Hprefix Hsuffix.
  destruct (kernel_continuation_call_uninterrupted_restore _ _ _ critical arch
    environment.(task_stack_call_continuations) restore kernel_program_inv local sg
    (task_stack_call_active_key call) call saved acquired published tcb_cursor publication_heap
    tcb_written tcb_middle tcb_final returned_heap frame Hr0 Hmask Hmasked Hprefix Hsuffix)
    as [Htcb_run [Htcb_return Hclosed]].
  assert (Hpublic : (task_create_continuation_input environment critical saved_local sg call
    (armv7a_irq_fiq_mask saved) published ** unmap_table_rep sg ** frame) returned_heap).
  { match type of Hclosed with ?P returned_heap => match goal with |- ?Q returned_heap =>
      assert (Hpublic_rule : P |-- Q) end end.
    { rewrite task_create_continuation_input_closed_world; reflexivity. }
    exact (Hpublic_rule returned_heap Hclosed). }
  split; [exact Htcb_run|]. split; [exact Hpublic|].
  intros registers final_registers sched_acquired saved_heap Hrunning Hreturn Hcpsr Hsaved_mask
    Hnoswitch Hsave.
  assert (Hnonempty : os_sched_selection_enabled published = true ->
    published.(SchedState).(readyList) <> []).
  { intros _ Hempty.
    assert (Hin : In publication.(stack_publication_slot) published.(SchedState).(readyList)).
    { change (In publication.(stack_publication_slot)
        (Ucos2Verify.lib.helpers.insert_sorted_by
          (sched_task_key sg (task_commit state.(TskState) args.(initPrio)
            publication.(stack_publication_invocation)
            (task_tcb_init_commit_node args publication.(stack_publication_acquired)
              publication.(stack_publication_slot) publication.(stack_publication_image))))
          publication.(stack_publication_slot) state.(SchedState).(readyList))).
      apply Ucos2Verify.lib.helpers.insert_sorted_by_in; left; reflexivity. }
    rewrite Hempty in Hin; contradiction. }
  destruct (kernel_continuation_call_uninterrupted_save _ _ _ critical arch
    environment.(task_stack_call_continuations) save kernel_program_inv local sg
    (task_stack_call_active_key call) call published (armv7a_irq_fiq_mask saved) registers
    returned_heap final_registers sched_acquired saved_heap frame Hreturn Hcpsr Hsaved_mask Hclosed Hsave)
    as [Hstate [Hsaved_word [Hsave_run Hsched_masked]]].
  split; [exact Hsave_run|]. split; [exact Hstate|].
  match type of Hsched_masked with ?P saved_heap => assert (Hprefix_input : P |--
    coq_prop (task_stack_live_coverage published.(TskState) (task_stack_call_active_key call)) &&
    (UCOS2_inv sg published ** unmap_table_rep sg **
      (critical_region_masked environment.(task_stack_call_platform) critical sg
         call.(os_sched_call_invocation) call.(os_sched_call_origin)
         final_registers.(kernel_save_r0) published **
       task_tcb_init_stack_context environment call **
       store_parked_continuations
         (kernel_saved_continuation_entry environment.(task_stack_call_continuations) published.(TskState) local)
         published.(TskState).(parkedTaskStacks) ** frame))) end.
  { unfold kernel_continuation_call_masked, kernel_continuation_inv, task_tcb_init_stack_context.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hprefix_input saved_heap Hsched_masked) as [Hprefix_coverage Hprefix_owned].
  destruct (os_sched_source_nonswitch_prefix_resources sg published _ saved_heap
    Hnoswitch Hnonempty Hprefix_owned) as [prefix_heap [Hprefix_run Hafter_prefix]].
  assert (Htasks : (os_sched_prefix_state published).(TskState) = published.(TskState)) by reflexivity.
  assert (Hprefix_masked : (kernel_continuation_call_masked environment.(task_stack_call_continuations)
    kernel_program_inv local critical sg (task_stack_call_active_key call) call
    final_registers.(kernel_save_r0) published (os_sched_prefix_state published) ** frame) prefix_heap).
  { match type of Hafter_prefix with ?P prefix_heap => match goal with |- ?Q prefix_heap =>
      assert (Hclose : P |-- Q) end end.
    { unfold kernel_continuation_call_masked, kernel_continuation_inv, task_tcb_init_stack_context.
      rewrite kernel_program_inv_split_unmap, Htasks; entailer!. }
    exact (Hclose prefix_heap Hafter_prefix). }
  exists prefix_heap; split; [exact Hprefix_run|].
  intros cursor written middle final_cursor after Hrestore_r0 Hrestore_mask Hrestore_prefix Hrestore_suffix.
  destruct (kernel_continuation_call_uninterrupted_restore _ _ _ critical arch
    environment.(task_stack_call_continuations) restore kernel_program_inv local sg
    (task_stack_call_active_key call) call final_registers.(kernel_save_r0) published
    (os_sched_prefix_state published) cursor prefix_heap written middle final_cursor after frame
    Hrestore_r0 Hrestore_mask Hprefix_masked Hrestore_prefix Hrestore_suffix)
    as [Hrestore_run [Hrestore_return Hfinal]].
  split; [exact Hrestore_run|].
  rewrite Hsaved_word, Hsaved_mask in Hfinal.
  match type of Hfinal with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { unfold local; sepcon_assoc_change.
    sep_apply_l_atomic (task_create_continuation_closed_returns_success environment critical saved_local
      sg call call (armv7a_irq_fiq_mask saved) (os_sched_prefix_state published)
      publication.(stack_publication_region) publication.(stack_publication_args)
      publication.(stack_publication_return) publication.(stack_publication_lower)
      old_frame publication.(stack_publication_upper)
      ltac:(unfold task_tcb_init_stack_same_call; auto)); entailer!. }
  exact (Hclose after Hfinal).
Qed.
