Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.array_abstraction Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The real failed-create store consumes the current acquired cell.
    Its guard is transported from the same TCBInit no-free observation;
    the initialized caller buffer remains separately owned. The produced
    Restore input is shared by uninterrupted and interrupted producers. *)
Lemma task_create_no_free_rollback_store_source :
  forall environment critical sg region args task_return lower upper initial_name
    original checkpoint_call mask saved initial released checkpoint before (frame : Assertion),
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial ->
  task_tcb_init_stack_same_call checkpoint_call original ->
  task_tcb_init_call_result sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 66 released ->
  UCOS2_state_inv sg checkpoint ->
  task_tcb_init_stack_return_preserved original released checkpoint ->
  (task_tcb_init_stack_save_output environment critical sg checkpoint_call mask saved checkpoint **
   task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
   unmap_table_rep sg ** frame) before ->
  exists returned acquired after,
    task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
    kernel_heap_execution (pointer_store_writes
      (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) 0) before after /\
    (task_tcb_init_stack_restore_input environment critical sg returned saved acquired
       (task_create_stack_rolled_back args acquired) **
     task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
     unmap_table_rep sg ** frame) after.
Proof.
  intros environment critical sg region args task_return lower upper initial_name original checkpoint_call
    mask saved initial released checkpoint before frame Hentry Hsame Hresult Hcheckpoint Hprevious Hpre.
  pose proof (proj1 (task_tcb_init_entry_priority_in_range sg
    (task_tcb_init_stack_call_args args initial_name) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) initial Hentry)) as Hpriority.
  assert (Hprio : (task_tcb_init_stack_call_args args initial_name).(initPrio) = args.(createPriority)).
  { unfold task_tcb_init_stack_call_args, task_create_tcb_args; destruct args.(createExtension); reflexivity. }
  rewrite Hprio in Hpriority.
  match type of Hpre with ?P before => assert (Hopen : P |--
    EX returned acquired,
      coq_prop (task_tcb_init_stack_same_call returned original /\
        task_tcb_init_stack_return_preserved original released acquired /\
        task_rollback_guard acquired.(TskState) args.(createPriority) original.(os_sched_call_invocation) /\
        interrupt_saved_value mask saved /\ UCOS2_state_inv sg acquired /\
        task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key returned)) &&
      ((sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) # Ptr |->_ **
       (store_prio_tbl_missing_i sg acquired.(TskState).(prioTbl) args.(createPriority) **
        UCOS2_raw_rep_missing_priority_table sg acquired **
        task_tcb_init_stack_capsules environment acquired **
        critical_region_masked environment.(task_stack_call_platform) critical sg
          original.(os_sched_call_invocation) original.(os_sched_call_origin) saved acquired **
        task_tcb_init_stack_context environment returned **
        task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
        unmap_table_rep sg ** frame))) end.
  { sep_apply_l_atomic (task_create_stack_save_output_no_free environment critical sg
      (task_tcb_init_stack_call_args args initial_name) original checkpoint_call mask saved initial released
      checkpoint Hsame Hresult Hcheckpoint Hprevious).
    Intros returned acquired.
    rewrite Hprio in *.
    assert (Hvalid : UCOS2_state_inv sg acquired) by tauto.
    assert (Hinv : UCOS2_raw_rep sg acquired |-- UCOS2_inv sg acquired)
      by (unfold UCOS2_inv; entailer!).
    sep_apply_l_atomic Hinv.
    sep_apply_l_atomic (UCOS2_inv_split_priority_cell sg acquired args.(createPriority) Hpriority).
    Intros.
    Exists returned acquired.
    sep_apply_l_atomic (store_ptr_undef_store_ptr
      (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR))
      (prio_tbl_entry_to_addr sg (acquired.(TskState).(prioTbl) args.(createPriority)))).
    entailer!. }
  destruct (Hopen before Hpre) as [returned [acquired [Hpure Howned]]].
  destruct Hpure as [Hreturned [Hpreserved [Hguard [Hsaved [Hvalid Hcovered]]]]].
  destruct (framed_pointer_store_execution
    (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) 0 _ before ltac:(lia) Howned)
    as [after [Hstore Hafter]].
  exists returned, acquired, after; split; [exact Hreturned|]. split; [exact Hsaved|].
  split; [exact Hstore|].
  assert (Hcovered_after : task_stack_live_coverage
    (task_create_stack_rolled_back args acquired).(TskState) (task_stack_call_active_key returned))
    by exact Hcovered.
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sepcon_assoc_change.
    pose proof (task_create_stack_no_free_rollback_resources environment critical sg
      (task_tcb_init_stack_call_args args initial_name) original.(os_sched_call_invocation)
      original.(os_sched_call_origin) initial released acquired Hentry Hresult Hvalid
      (proj1 Hpreserved) (proj1 (proj2 Hpreserved))) as Hmerge.
    rewrite Hprio in Hmerge; sep_apply_l_atomic Hmerge.
    destruct Hreturned as [Hi [Ho Hs]].
    unfold task_tcb_init_stack_restore_input, task_create_stack_rolled_back.
    rewrite Hi, Ho; entailer!. }
  exact (Hclose after Hafter).
Qed.

(** The two concrete continuations at the C statement after OS_TCBInit.
    This is a produced source conclusion, never an API precondition or
    an external ABI guarantee. It retains the observed result and heap. *)
Definition task_create_tcb_return_source_continuation environment critical arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg region args task_return lower old_frame upper original mask result before (frame : Assertion) : Prop :=
  (result = 0 /\ exists returned current,
    task_tcb_init_stack_same_call returned original /\
    uchar_load sg.(g_OSRunning) (task_create_stack_running current) before /\
    match current.(SchedState).(isRunning) with
    | false =>
        (task_create_stack_post environment critical sg region args task_return lower old_frame upper
          original mask 0 ** frame) before
    | true =>
        (os_sched_stack_pre environment kernel_program_inv sg returned mask current ** frame) before /\
        (forall after,
          (os_sched_stack_return_post environment kernel_program_inv sg returned mask current ** frame) after ->
          (task_create_stack_post environment critical sg region args task_return lower old_frame upper
            original mask 0 ** frame) after)
    end) \/
  (result = 66 /\ exists checkpoint_call checkpoint,
    task_tcb_init_stack_same_call checkpoint_call original /\
    (forall registers final_registers acquired saved_heap,
      registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
      armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
      armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) checkpoint before
        final_registers acquired saved_heap ->
      kernel_call_save_uninterrupted_execution arch registers checkpoint before final_registers acquired saved_heap /\
      exists returned rollback_heap,
        task_tcb_init_stack_same_call returned original /\
        kernel_heap_execution (pointer_store_writes
          (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) 0) saved_heap rollback_heap /\
        (forall cursor written middle final_cursor after,
          cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
          armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
          armv7a_restore_prefix_transition restore cursor rollback_heap written middle ->
          armv7a_restore_suffix_transition restore written middle final_cursor after ->
          kernel_call_restore_uninterrupted_execution arch cursor rollback_heap final_cursor after /\
          (task_create_stack_post environment critical sg region args task_return lower old_frame upper
             original mask 66 ** frame) after))).

(** Consume success from ANY checked TCBInit return producer. The C test
    reads the actual OSRunning byte on this heap. A stopped kernel returns
    immediately; a running kernel transfers this same world to Scheduler.
    The continuation consumes Scheduler's actual return post and therefore
    works with its no-switch, switching, and IRQ return producers alike. *)
Lemma task_create_success_return_source :
  forall environment critical sg region args task_return lower old_frame upper initial_name
    invocation origin original mask initial before (frame : Assertion),
  (task_tcb_init_stack_call_post environment critical sg region args task_return lower upper initial_name
     invocation origin mask initial original 0 ** unmap_table_rep sg ** frame) before ->
  exists returned current,
    task_tcb_init_stack_same_call returned original /\
    uchar_load sg.(g_OSRunning) (task_create_stack_running current) before /\
    match current.(SchedState).(isRunning) with
    | false =>
        (task_create_stack_post environment critical sg region args task_return lower old_frame upper
          original mask 0 ** frame) before
    | true =>
        (os_sched_stack_pre environment kernel_program_inv sg returned mask current ** frame) before /\
        (forall after,
          (os_sched_stack_return_post environment kernel_program_inv sg returned mask current ** frame) after ->
          (task_create_stack_post environment critical sg region args task_return lower old_frame upper
            original mask 0 ** frame) after)
    end.
Proof.
  intros environment critical sg region args task_return lower old_frame upper initial_name
    invocation origin original mask initial before frame Hpre.
  match type of Hpre with ?P before => assert (Hopen : P |--
    EX returned current,
      coq_prop (task_tcb_init_stack_same_call returned original /\
        task_tcb_init_stack_source_preserved original initial current /\ UCOS2_state_inv sg current) &&
      (sg.(g_OSRunning) # UChar |-> task_create_stack_running current **
       (task_create_stack_without_running environment critical sg returned mask current **
        unmap_table_rep sg ** frame))) end.
  { sep_apply_l_atomic (task_create_stack_tcb_success_source environment critical sg region args task_return
      lower upper initial_name invocation origin original mask initial).
    Intros returned current; unfold task_tcb_init_stack_save_input; Intros.
    Exists returned current.
    unfold task_create_stack_without_running, task_create_stack_running, critical_region_outside.
    entailer!. }
  destruct (Hopen before Hpre) as [returned [current [[Hsame [Hsource Hvalid]] Howned]]].
  exists returned, current; split; [exact Hsame|].
  split; [eapply framed_uchar_store_load; exact Howned|].
  destruct current.(SchedState).(isRunning) eqn:Hrunning.
  - split.
    + match type of Howned with ?P before => match goal with |- ?Q before => assert (Hcall : P |-- Q) end end.
      { sepcon_assoc_change.
        sep_apply_l_atomic (task_create_stack_running_sched_pre environment critical sg returned mask current Hvalid).
        entailer!. }
      exact (Hcall before Howned).
    + intros after Hafter.
      match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hreturn : P |-- Q) end end.
      { sep_apply_l_atomic (os_sched_stack_return_post_returns_create environment critical sg original returned
          mask current region args task_return lower old_frame upper Hsame); reflexivity. }
      exact (Hreturn after Hafter).
  - match type of Howned with ?P before => match goal with |- ?Q before => assert (Hreturn : P |-- Q) end end.
    { unfold task_create_stack_post; Exists returned current.
      destruct (Z.eq_dec 0 0); [|contradiction].
      unfold task_create_stack_without_running, task_tcb_init_stack_save_input,
        critical_region_outside, task_create_stack_running.
      entailer!. }
    exact (Hreturn before Howned).
Qed.

(** A single consumer covers both failure sources: no-free may have
    returned directly or after foreign execution. It starts from the
    CURRENT TCBInit post, runs Save, writes NULL, and runs Restore on the
    exact resulting heap. The local Save/Restore branch uses only the
    already selected ABI; IRQ producers use the same store theorem above. *)
Lemma task_create_no_free_return_source :
  forall environment critical arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg region args task_return lower old_frame upper initial_name original mask initial before (frame : Assertion),
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial ->
  (task_tcb_init_stack_call_post environment critical sg region args task_return lower upper initial_name
     original.(os_sched_call_invocation) original.(os_sched_call_origin) mask initial original 66 **
   unmap_table_rep sg ** frame) before ->
  exists checkpoint_call checkpoint,
    task_tcb_init_stack_same_call checkpoint_call original /\
    (forall registers final_registers acquired saved_heap,
      registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
      armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
      armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) checkpoint before
        final_registers acquired saved_heap ->
      kernel_call_save_uninterrupted_execution arch registers checkpoint before final_registers acquired saved_heap /\
      exists returned rollback_heap,
        task_tcb_init_stack_same_call returned original /\
        kernel_heap_execution (pointer_store_writes
          (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) 0) saved_heap rollback_heap /\
        (forall cursor written middle final_cursor after,
          cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
          armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
          armv7a_restore_prefix_transition restore cursor rollback_heap written middle ->
          armv7a_restore_suffix_transition restore written middle final_cursor after ->
          kernel_call_restore_uninterrupted_execution arch cursor rollback_heap final_cursor after /\
          (task_create_stack_post environment critical sg region args task_return lower old_frame upper
             original mask 66 ** frame) after)).
Proof.
  intros environment critical arch save restore sg region args task_return lower old_frame upper
    initial_name original mask initial before frame Hentry Hpre.
  match type of Hpre with ?P before => assert (Hopen : P |--
    (EX released returned current,
      coq_prop (task_tcb_init_call_result sg (task_tcb_init_stack_call_args args initial_name)
        original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 66 released /\
        task_tcb_init_stack_same_call returned original /\ UCOS2_state_inv sg current /\
        task_tcb_init_stack_return_preserved original released current) &&
      (task_tcb_init_stack_save_input environment critical sg returned mask current **
       task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper))) **
    unmap_table_rep sg ** frame) end.
  { sep_apply_l_atomic (task_create_stack_no_free_reacquire environment critical sg region args
      task_return lower upper initial_name original mask initial).
    Intros released returned current; Exists released returned current; entailer!. }
  match type of Hopen with _ |-- ?P => assert (Horder : P |-- EX released returned current,
      coq_prop (task_tcb_init_call_result sg (task_tcb_init_stack_call_args args initial_name)
        original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 66 released /\
        task_tcb_init_stack_same_call returned original /\ UCOS2_state_inv sg current /\
        task_tcb_init_stack_return_preserved original released current) &&
      (task_tcb_init_stack_save_input environment critical sg returned mask current **
       (task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
        unmap_table_rep sg ** frame))) end.
  { Intros released returned current; Exists released returned current; entailer!. }
  destruct (Horder before (Hopen before Hpre)) as [released [checkpoint_call [checkpoint [Hpure Howned]]]].
  destruct Hpure as [Hresult [Hsame [Hvalid Hprevious]]].
  assert (Hcoverage : task_stack_live_coverage checkpoint.(TskState)
    (task_stack_call_active_key checkpoint_call)).
  { match type of Howned with ?P before => assert (Hobserve : P |--
      coq_prop (task_stack_live_coverage checkpoint.(TskState)
        (task_stack_call_active_key checkpoint_call)) && TT) end.
    { unfold task_tcb_init_stack_save_input; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Howned)). }
  exists checkpoint_call, checkpoint; split; [exact Hsame|].
  intros registers final_registers acquired saved_heap Hreturn Hcpsr Hmask Hsave.
  match type of Howned with ?P before => assert (Hsave_pre : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      checkpoint_call mask ** critical_region_outside critical sg checkpoint_call.(os_sched_call_invocation) checkpoint **
    armv7a_task_stack_continuations environment.(task_stack_call_continuations)
      checkpoint.(TskState) checkpoint.(TskState).(parkedTaskStacks) **
    (task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
     unmap_table_rep sg ** frame)) end.
  { unfold task_tcb_init_stack_save_input, task_tcb_init_stack_capsules; entailer!. }
  destruct (task_tcb_init_stack_uninterrupted_save_post _ _ _ critical arch
    environment.(task_stack_call_continuations) save sg checkpoint_call mask checkpoint registers before
    final_registers acquired saved_heap _ Hvalid Hcoverage Hreturn Hcpsr Hmask
    (Hsave_pre before Howned) Hsave) as [Hsave_run Hsaved].
  match type of Hsaved with ?P saved_heap => assert (Hsaved_output : P |--
    task_tcb_init_stack_save_output environment critical sg checkpoint_call mask
      final_registers.(kernel_save_r0) checkpoint **
    task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
    unmap_table_rep sg ** frame) end.
  { sep_apply_l_atomic (task_tcb_init_stack_registered_save_output environment critical sg checkpoint_call
      mask final_registers.(kernel_save_r0) checkpoint); entailer!. }
  destruct (task_create_no_free_rollback_store_source environment critical sg region args task_return lower upper
    initial_name original checkpoint_call mask final_registers.(kernel_save_r0) initial released checkpoint
    saved_heap frame Hentry Hsame Hresult Hvalid Hprevious (Hsaved_output saved_heap Hsaved))
    as [returned [current [rollback_heap [Hreturned [Hsaved_mask [Hstore Hrollback]]]]]].
  split; [exact Hsave_run|]. exists returned, rollback_heap.
  split; [exact Hreturned|]. split; [exact Hstore|].
  intros cursor written middle final_cursor after Hr0 Hcursor Hprefix Hsuffix.
  assert (Hrollback_coverage : task_stack_live_coverage
    (task_create_stack_rolled_back args current).(TskState) (task_stack_call_active_key returned)).
  { match type of Hrollback with ?P rollback_heap => assert (Hobserve : P |--
      coq_prop (task_stack_live_coverage (task_create_stack_rolled_back args current).(TskState)
        (task_stack_call_active_key returned)) && TT) end.
    { unfold task_tcb_init_stack_restore_input; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve rollback_heap Hrollback)). }
  match type of Hrollback with ?P rollback_heap => assert (Hrestore_pre : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      returned.(os_sched_call_invocation) returned.(os_sched_call_origin) final_registers.(kernel_save_r0) current **
    task_tcb_init_stack_context environment returned ** UCOS2_inv sg (task_create_stack_rolled_back args current) **
    task_tcb_init_stack_covered_capsules environment (task_create_stack_rolled_back args current) **
    (task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
     unmap_table_rep sg ** frame)) end.
  { unfold task_tcb_init_stack_restore_input, task_tcb_init_stack_context,
      task_tcb_init_stack_capsules, task_tcb_init_stack_covered_capsules; entailer!. }
  destruct (task_tcb_init_stack_covered_uninterrupted_restore environment critical arch restore sg returned
    final_registers.(kernel_save_r0) current (task_create_stack_rolled_back args current) cursor rollback_heap
    written middle final_cursor after _ Hrollback_coverage Hr0 Hcursor
    (Hrestore_pre rollback_heap Hrollback) Hprefix Hsuffix) as [Hrun [Hlr Hafter]].
  split; [exact Hrun|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold task_tcb_init_stack_covered_save_input; Intros.
    unfold task_create_stack_post; Exists returned (task_create_stack_rolled_back args current).
    destruct (Z.eq_dec 66 0); [lia|]; Exists true.
    unfold task_create_stack_failure_buffer, task_tcb_init_stack_save_input,
      task_tcb_init_stack_capsules, task_tcb_init_stack_covered_capsules.
    rewrite (proj2 Hsaved_mask); entailer!; tauto. }
  exact (Hclose after Hafter).
Qed.

Lemma task_create_tcb_return_source :
  forall environment critical arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg region args task_return lower old_frame upper initial_name original mask initial result before (frame : Assertion),
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial ->
  (task_tcb_init_stack_call_post environment critical sg region args task_return lower upper initial_name
     original.(os_sched_call_invocation) original.(os_sched_call_origin) mask initial original result **
   unmap_table_rep sg ** frame) before ->
  task_create_tcb_return_source_continuation environment critical arch save restore sg region args task_return
    lower old_frame upper original mask result before frame.
Proof.
  intros environment critical arch save restore sg region args task_return lower old_frame upper initial_name
    original mask initial result before frame Hentry Hpre.
  assert (Hcodes : result = 0 \/ result = 66).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop (result = 0 \/ result = 66) && TT) end.
    { sep_apply_l_atomic (task_create_stack_tcb_result_codes environment critical sg region args task_return
        lower upper initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin)
        mask initial original result); Intros; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  unfold task_create_tcb_return_source_continuation.
  destruct Hcodes as [Hzero|Hnofree].
  - subst result; left; split; [reflexivity|]. eapply task_create_success_return_source; exact Hpre.
  - subst result; right; split; [reflexivity|]. eapply task_create_no_free_return_source; eassumption.
Qed.
