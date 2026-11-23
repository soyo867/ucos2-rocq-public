Require Import Coq.ZArith.ZArith Coq.Strings.String Coq.Lists.List Coq.micromega.Lia.
Require Import SetsClass.SetsClass.
From SimpleC.SL Require Import Mem SeparationLogic ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_literal_resources.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.lib.interrupt.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** A static-program binding, not a new application argument or a second
    owner. The producers below move the actual QCP literal bytes into the
    existing NameState. Neither string pooling across translation units nor
    a fresh source key is inferred from an arbitrary valid name state. *)
Definition task_create_default_name_binding (p : addr)
  (state : UCOS2_Verify_State) : Prop :=
  state.(NameState).(nameBytes) p = Some 63 /\
  state.(NameState).(nameBytes) (p + 1) = Some 0.

Definition task_create_register_default_name (names : NameResourceState)
  (key : nat) (p : addr) : NameResourceState :=
  name_register_source names key (name_question_mark_source p) (name_question_mark_bytes p).

Lemma task_create_register_default_name_lookup : forall names key p,
  (task_create_register_default_name names key p).(nameBytes) p = Some 63 /\
  (task_create_register_default_name names key p).(nameBytes) (p + 1) = Some 0.
Proof.
  intros; unfold task_create_register_default_name, name_register_source.
  cbn [nameBytes name_question_mark_source nameStorageDomain].
  destruct (in_dec Z.eq_dec p [p; p + 1]); [|simpl in n; tauto].
  destruct (in_dec Z.eq_dec (p + 1) [p; p + 1]); [|simpl in n; tauto].
  unfold name_question_mark_bytes.
  destruct (Z.eq_dec p p); [|congruence].
  destruct (Z.eq_dec (p + 1) p); [lia|].
  destruct (Z.eq_dec (p + 1) (p + 1)); [split; reflexivity|congruence].
Qed.

Lemma task_create_register_default_name_source : forall names key p,
  (task_create_register_default_name names key p).(nameSources) key =
    Some (name_question_mark_source p).
Proof.
  intros; unfold task_create_register_default_name, name_register_source; cbn.
  destruct (Nat.eq_dec key key); congruence.
Qed.

Lemma task_create_register_default_name_valid : forall names key p,
  valid_name_resources names -> names.(nameSources) key = None ->
  name_source_disjoint names (name_question_mark_source p) ->
  valid_name_resources (task_create_register_default_name names key p).
Proof.
  intros; apply name_register_source_preserves_resources; try assumption.
  apply name_question_mark_source_valid.
Qed.

(** The residual of the new registered source is exactly the OLD byte
    owner. Reclassification does not allocate or overwrite a C byte. *)
Lemma task_create_registered_default_name_residual : forall names key p,
  name_source_disjoint names (name_question_mark_source p) ->
  store_name_bytes_without_question_mark (task_create_register_default_name names key p) p
    --||-- store_name_bytes names.
Proof.
  intros names key p Hdis.
  unfold store_name_bytes_without_question_mark.
  rewrite store_name_bytes_missing_byte_equiv.
  unfold store_name_bytes; apply store_map_equiv; intro q.
  unfold kernel_map_set.
  destruct (Z.eq_dec q (p + 1)) as [->|Hnext].
  - symmetry; apply Hdis; simpl; auto.
  - destruct (Z.eq_dec q p) as [->|Hfirst].
    + symmetry; apply Hdis; simpl; auto.
    + unfold task_create_register_default_name, name_register_source.
      cbn [nameBytes name_question_mark_source nameStorageDomain].
      destruct (in_dec Z.eq_dec q [p; p + 1]); [simpl in i; intuition congruence|reflexivity].
Qed.

Lemma task_create_register_default_name_storage : forall names key p,
  name_source_disjoint names (name_question_mark_source p) ->
  store_name_bytes names ** store_stringLit p "?" |--
    store_name_bytes (task_create_register_default_name names key p).
Proof.
  intros names key p Hdis.
  destruct (task_create_register_default_name_lookup names key p) as [Hchar Hnul].
  rewrite <- (task_create_registered_default_name_residual names key p Hdis).
  sep_apply_l_atomic (store_name_bytes_merge_question_mark
    (task_create_register_default_name names key p) p Hchar Hnul); entailer!.
Qed.

Lemma task_create_default_name_pool_producer : forall names key LitMap,
  valid_name_resources names -> names.(nameSources) key = None ->
  name_source_disjoint names (name_question_mark_source (LitMap "?")) ->
  store_name_bytes names ** GlobalStrings LitMap |--
    name_resources_inv (task_create_register_default_name names key (LitMap "?")) **
    GlobalStrings_missing LitMap ["?"].
Proof.
  intros names key LitMap Hvalid Hfresh Hdis.
  sep_apply_l_atomic (GlobalStrings_split LitMap "?").
  sep_apply_l_atomic (task_create_register_default_name_storage names key (LitMap "?") Hdis).
  unfold name_resources_inv; entailer!.
  apply task_create_register_default_name_valid; assumption.
Qed.

(** This producer is applied to an actual heap, so its conclusion is not
    merely pure inhabitation. It retains every caller-supplied frame and
    the exact residual pool. The caller of the producer supplies the real
    disjoint loader/static heap; no literal-pool inhabitation axiom is added. *)
Lemma task_create_default_name_pool_producer_on_heap :
  forall names key LitMap (frame : Assertion) heap,
  valid_name_resources names -> names.(nameSources) key = None ->
  name_source_disjoint names (name_question_mark_source (LitMap "?")) ->
  (store_name_bytes names ** GlobalStrings LitMap ** frame) heap ->
  (name_resources_inv (task_create_register_default_name names key (LitMap "?")) **
    GlobalStrings_missing LitMap ["?"] ** frame) heap.
Proof.
  intros names key LitMap frame heap Hvalid Hfresh Hdis Hheap.
  assert (Hmove : store_name_bytes names ** GlobalStrings LitMap ** frame |--
    name_resources_inv (task_create_register_default_name names key (LitMap "?")) **
      GlobalStrings_missing LitMap ["?"] ** frame).
  { sep_apply_l_atomic (task_create_default_name_pool_producer names key LitMap
      Hvalid Hfresh Hdis); entailer!. }
  exact (Hmove heap Hheap).
Qed.

Lemma task_create_registered_default_name_binding : forall state key p,
  task_create_default_name_binding p
    (replace_NameS (task_create_register_default_name state.(NameState) key p) state).
Proof. intros; apply task_create_register_default_name_lookup. Qed.

Lemma task_create_register_default_name_preserves_readable : forall names key p name chars,
  name_source_disjoint names (name_question_mark_source p) ->
  readable_name names name chars ->
  readable_name (task_create_register_default_name names key p) name chars.
Proof.
  intros names key p name chars Hdis [Hchars [Hbytes Hnul]].
  unfold readable_name; split; [exact Hchars|]; split.
  - intros i c Hi; specialize (Hbytes i c Hi).
    unfold task_create_register_default_name, name_register_source; cbn [nameBytes].
    destruct (in_dec Z.eq_dec (name + Z.of_nat i) (nameStorageDomain (name_question_mark_source p)));
      [rewrite Hdis in Hbytes by assumption; discriminate|exact Hbytes].
  - unfold task_create_register_default_name, name_register_source; cbn [nameBytes].
    destruct (in_dec Z.eq_dec (name + Z.of_nat (List.length chars))
      (nameStorageDomain (name_question_mark_source p)));
      [rewrite Hdis in Hnul by assumption; discriminate|exact Hnul].
Qed.

Lemma task_create_register_default_name_preserves_state_inv : forall sg before key p,
  UCOS2_state_inv sg before -> before.(NameState).(nameSources) key = None ->
  name_source_disjoint before.(NameState) (name_question_mark_source p) ->
  UCOS2_state_inv sg
    (replace_NameS (task_create_register_default_name before.(NameState) key p) before).
Proof.
  intros sg before key p Hvalid Hfresh Hdis.
  assert (Hnames : valid_name_resources
    (task_create_register_default_name before.(NameState) key p)).
  { apply task_create_register_default_name_valid; try assumption.
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Hroots : kernel_names_valid sg
    (replace_NameS (task_create_register_default_name before.(NameState) key p) before)).
  { intros name Hroot; change (kernel_name_root sg before name) in Hroot.
    destruct (UCOS2_state_inv_names_valid sg before Hvalid name Hroot) as [chars Hread].
    exists chars; eapply task_create_register_default_name_preserves_readable; eassumption. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *; cbn; intuition.
Qed.

Lemma task_create_register_default_name_raw_rep : forall sg before key p,
  name_source_disjoint before.(NameState) (name_question_mark_source p) ->
  UCOS2_raw_rep sg before ** store_stringLit p "?" |--
  UCOS2_raw_rep sg
    (replace_NameS (task_create_register_default_name before.(NameState) key p) before).
Proof.
  intros sg before key p Hdis.
  rewrite (UCOS2_raw_rep_split_module sg before NamesModule).
  rewrite (UCOS2_raw_rep_split_module sg
    (replace_NameS (task_create_register_default_name before.(NameState) key p) before) NamesModule).
  change (store_name_bytes before.(NameState) ** UCOS2_raw_rep_missing_names sg before **
    store_stringLit p "?" |--
    store_name_bytes (task_create_register_default_name before.(NameState) key p) **
    UCOS2_raw_rep_missing_names sg before).
  sep_apply_l_atomic (task_create_register_default_name_storage before.(NameState) key p Hdis); entailer!.
Qed.

(** Compose the real static producer with the existing continuation owner.
    Its output state is reindexed ONCE, at registration, rather than silently
    changing a state after a caller has chosen its safeExec continuation. *)
Lemma task_create_default_name_continuation_producer :
  forall environment critical saved_local sg call mask before key LitMap,
  before.(NameState).(nameSources) key = None ->
  name_source_disjoint before.(NameState) (name_question_mark_source (LitMap "?")) ->
  task_tcb_init_continuation_save_input environment critical saved_local sg call mask before **
    GlobalStrings LitMap |--
  coq_prop (task_create_default_name_binding (LitMap "?")
    (replace_NameS (task_create_register_default_name before.(NameState) key (LitMap "?")) before)) &&
  (task_tcb_init_continuation_save_input environment critical saved_local sg call mask
    (replace_NameS (task_create_register_default_name before.(NameState) key (LitMap "?")) before) **
    GlobalStrings_missing LitMap ["?"]).
Proof.
  intros environment critical saved_local sg call mask before key LitMap Hfresh Hdis.
  rewrite !task_tcb_init_modular_save_input_world.
  unfold kernel_continuation_call_closed, kernel_continuation_inv, UCOS2_inv; Intros.
  assert (Hvalid : UCOS2_state_inv sg before) by tauto.
  pose proof (task_create_register_default_name_preserves_state_inv sg before key
    (LitMap "?") Hvalid Hfresh Hdis) as Hafter.
  pose proof (task_create_registered_default_name_binding before key (LitMap "?")) as Hbinding.
  sep_apply_l_atomic (GlobalStrings_split LitMap "?").
  sep_apply_l_atomic (task_create_register_default_name_raw_rep sg before key (LitMap "?") Hdis).
  entailer!.
Qed.

(** Reuse after registration needs no pool split and no second source key.
    The caller keeps its exact list of already removed literals as a frame. *)
Lemma task_create_default_name_registered_call_pre :
  forall environment critical saved_local sg region args task_return lower upper
    initial_name invocation origin mask initial call,
  call.(os_sched_call_invocation) = invocation -> call.(os_sched_call_origin) = origin ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name) invocation origin initial ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_continuation_save_input environment critical saved_local sg call mask initial **
    task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) |--
  task_tcb_init_continuation_call_pre environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial call.
Proof.
  intros environment critical saved_local sg region args task_return lower upper
    initial_name invocation origin mask initial call Hi Ho Hentry Hlayout.
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input; Intros.
  unfold task_tcb_init_continuation_call_pre, task_tcb_init_stack_pre, task_tcb_init_pre,
    task_tcb_init_continuation_capsules, kernel_call_execution_owned.
  rewrite Hi, Ho; entailer!.
Qed.

Lemma task_create_default_name_binding_readable : forall p state,
  task_create_default_name_binding p state -> readable_name state.(NameState) p [63].
Proof.
  intros p state [Hchar Hnul]; unfold readable_name; split.
  - repeat constructor; lia.
  - split.
    + intros [|i] c Hnth; cbn in Hnth.
      * injection Hnth as <-; rewrite Z.add_0_r; exact Hchar.
      * destruct i; discriminate.
    + exact Hnul.
Qed.

(** Actual callee-input producer. The priority/reservation/caller/initialized
    child-stack conditions are the pre-existing TCBInit input conditions.
    The only extra inputs belong to static-source registration: a genuinely
    unused source key and disjoint real bytes from this callee's LitMap.
    No readable-question-mark premise is requested from an application. *)
Lemma task_tcb_init_default_name_call_producer :
  forall environment critical saved_local sg region args task_return lower upper
    invocation origin mask before call key LitMap (frame : Assertion) heap,
  call.(os_sched_call_invocation) = invocation -> call.(os_sched_call_origin) = origin ->
  before.(NameState).(nameSources) key = None ->
  name_source_disjoint before.(NameState) (name_question_mark_source (LitMap "?")) ->
  task_priority_in_range sg (task_tcb_init_stack_call_args args (LitMap "?")).(initPrio) ->
  task_invocation_active before.(TskState) invocation origin ->
  task_tcb_init_pending (task_tcb_init_stack_call_args args (LitMap "?")) invocation origin before ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  (task_tcb_init_continuation_save_input environment critical saved_local sg call mask before **
    task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
    GlobalStrings LitMap ** frame) heap ->
  let initial := replace_NameS
    (task_create_register_default_name before.(NameState) key (LitMap "?")) before in
  (coq_prop (task_create_default_name_binding (LitMap "?") initial /\ UCOS2_state_inv sg initial) &&
    (task_tcb_init_continuation_call_pre environment critical saved_local sg region args task_return
      lower upper (LitMap "?") invocation origin mask initial call **
      GlobalStrings_missing LitMap ["?"] ** frame)) heap.
Proof.
  intros environment critical saved_local sg region args task_return lower upper
    invocation origin mask before call key LitMap frame heap Hi Ho Hfresh Hdis Hprio Hactive
    Hpending Hlayout Hheap initial.
  assert (Hcompose :
    task_tcb_init_continuation_save_input environment critical saved_local sg call mask before **
      task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
      GlobalStrings LitMap ** frame |--
    coq_prop (task_create_default_name_binding (LitMap "?") initial /\ UCOS2_state_inv sg initial) &&
      (task_tcb_init_continuation_call_pre environment critical saved_local sg region args task_return
        lower upper (LitMap "?") invocation origin mask initial call **
        GlobalStrings_missing LitMap ["?"] ** frame)).
  { sep_apply_l_atomic (task_create_default_name_continuation_producer environment critical
      saved_local sg call mask before key LitMap Hfresh Hdis); Intros.
    fold initial.
    assert (Hbinding : task_create_default_name_binding (LitMap "?") initial) by assumption.
    assert (Hvalid : task_tcb_init_continuation_save_input environment critical saved_local
      sg call mask initial |-- coq_prop (UCOS2_state_inv sg initial) &&
      task_tcb_init_continuation_save_input environment critical saved_local sg call mask initial).
    { unfold task_tcb_init_continuation_save_input, task_create_continuation_input; Intros; entailer!. }
    sep_apply_l_atomic Hvalid; Intros.
    assert (Hentry : task_tcb_init_entry sg (task_tcb_init_stack_call_args args (LitMap "?"))
      invocation origin initial).
    { unfold task_tcb_init_entry; split; [assumption|].
      split; [exact Hprio|]. split; [exact Hactive|]. split; [exact Hpending|].
      intros _; exists [63]; apply task_create_default_name_binding_readable.
      unfold task_tcb_init_stack_call_args, task_create_tcb_args;
        destruct args.(createExtension); exact Hbinding. }
    sep_apply_l_atomic (task_create_default_name_registered_call_pre environment critical saved_local
      sg region args task_return lower upper (LitMap "?") invocation origin mask initial call
      Hi Ho Hentry Hlayout); entailer!. }
  exact (Hcompose heap Hheap).
Qed.

(** A concrete two-byte heap for the unique static name owner. This is a
    genuine heap-level witness, separate from the conditional platform/world
    composition above; it does not assert that the opaque pool or arbitrary
    platform resources are inhabited without their existing producers. *)
Definition task_create_literal_heap (memory : Mem.mem) : UCOS2_C_Rules.model :=
  {| ConAssertion.s_mem := memory;
     ConAssertion.s_STS := Sets.full; ConAssertion.s_token := Sets.empty |}.

Lemma task_create_literal_byte_heap : forall p b,
  isvalidptr_char p -> 0 <= b <= 255 ->
  (p # UChar |-> b) (task_create_literal_heap (single_byte_mem p b)).
Proof.
  intros p b Hptr Hb; unfold store_uchar; split.
  - change (isvalidptr_char p /\ b >= 0 /\ b <= 255).
    split; [exact Hptr|lia].
  - exists b; split; [apply Byte.eqm_refl|].
    unfold task_create_literal_heap; cbn; repeat split; try reflexivity;
      sets_unfold; tauto.
Qed.

Lemma task_create_default_name_owner_inhabited : forall p,
  isvalidptr_char p -> isvalidptr_char (p + 1) ->
  exists heap, name_resources_inv (name_question_mark_resources p) heap.
Proof.
  intros p Hp Hnext.
  set (memory := fun q => if addr_eqb q p then value 63
    else if addr_eqb q (p + 1) then value 0 else Noperm).
  exists (task_create_literal_heap memory).
  apply (store_string_lit_question_mark_register p).
  apply (proj2 (store_string_lit_question_mark_equiv p)).
  exists (task_create_literal_heap (single_byte_mem p 63)),
    (task_create_literal_heap (single_byte_mem (p + 1) 0)).
  split.
  - unfold ConAssertion.state_join, task_create_literal_heap; cbn; split.
    + change (mem_join (single_byte_mem p 63) (single_byte_mem (p + 1) 0) memory).
      intro q; unfold memory, single_byte_mem.
      destruct (addr_eqb q p) eqn:Hfirst, (addr_eqb q (p + 1)) eqn:Hsecond.
      * apply addr_eqb_eq in Hfirst; apply addr_eqb_eq in Hsecond; lia.
      * right; right; right; right; exists 63; auto.
      * right; right; right; left; exists 0; auto.
      * left; auto.
    + unfold ConAssertion.TokenSet_join, ConAssertion.STS_state_join;
        repeat split; sets_unfold; tauto.
  - split; apply task_create_literal_byte_heap; auto; lia.
Qed.

Lemma task_create_default_name_binding_transport : forall p before after,
  before.(NameState) = after.(NameState) ->
  task_create_default_name_binding p before -> task_create_default_name_binding p after.
Proof. unfold task_create_default_name_binding; intros; rewrite <- H; assumption. Qed.

Lemma task_create_default_name_binding_detached :
  forall sg args invocation origin initial acquired slot rest image p,
  UCOS2_state_inv sg initial -> task_create_default_name_binding p initial ->
  task_tcb_init_call_preserved sg invocation initial acquired ->
  task_create_default_name_binding p
    (task_tcb_init_detached_state args invocation origin acquired slot rest image).
Proof.
  intros sg args invocation origin initial acquired slot rest image p Hvalid Hbinding Hsource.
  eapply task_create_default_name_binding_transport; [|exact Hbinding].
  exact (proj2 (proj2 (proj2 (Hsource Hvalid)))).
Qed.

(** Only the two literal bytes are absent. The state validity and all
    continuation metadata remain tied to the same actual current world. *)
Definition task_tcb_init_literal_world (p : addr) (sg : StableGlobVars)
  (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (task_create_default_name_binding p state /\ UCOS2_state_inv sg state) &&
  UCOS2_raw_rep_without_question_mark sg state p.

Definition task_tcb_init_literal_restore_output environment critical saved_local
  sg original saved released p : Assertion :=
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    (task_tcb_init_literal_world p) (task_create_continuation_local saved_local) critical
    kernel_call_control_rely sg original (armv7a_irq_fiq_mask saved) released.

Lemma task_tcb_init_literal_restore_split :
  forall environment critical saved_local sg original saved released p,
  task_create_default_name_binding p released ->
  task_tcb_init_modular_restore_output environment critical saved_local sg original saved released |--
    store_stringLit p "?" **
    task_tcb_init_literal_restore_output environment critical saved_local sg original saved released p.
Proof.
  intros environment critical saved_local sg original saved released p Hbinding.
  unfold task_tcb_init_modular_restore_output, kernel_call_modular_restore_post.
  Intros returned current.
  assert (Htrace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    released false returned.(os_sched_call_origin) current) by tauto.
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)) as Hinterval.
  pose proof (critical_region_interval_preserves_name_state critical sg
    original.(os_sched_call_invocation) released current Hinterval) as Hnames.
  pose proof (task_create_default_name_binding_transport p released current Hnames Hbinding) as Hcurrent.
  destruct Hcurrent as [Hchar Hnul].
  unfold kernel_continuation_call_closed, kernel_continuation_inv, UCOS2_inv; Intros.
  rewrite (UCOS2_raw_rep_split_question_mark sg current p Hchar Hnul).
  unfold task_tcb_init_literal_restore_output, kernel_call_modular_restore_post.
  Exists returned current.
  unfold kernel_continuation_call_closed, kernel_continuation_inv,
    task_tcb_init_literal_world, task_create_default_name_binding; entailer!.
Qed.

Lemma task_tcb_init_literal_restore_merge :
  forall environment critical saved_local sg original saved released p,
  store_stringLit p "?" **
    task_tcb_init_literal_restore_output environment critical saved_local sg original saved released p |--
  task_tcb_init_modular_restore_output environment critical saved_local sg original saved released.
Proof.
  intros environment critical saved_local sg original saved released p.
  unfold task_tcb_init_literal_restore_output, kernel_call_modular_restore_post;
    Intros returned current.
  unfold kernel_continuation_call_closed, kernel_continuation_inv,
    task_tcb_init_literal_world, task_create_default_name_binding; Intros.
  assert (Hchar : current.(NameState).(nameBytes) p = Some 63) by tauto.
  assert (Hnul : current.(NameState).(nameBytes) (p + 1) = Some 0) by tauto.
  sep_apply_l_atomic (proj2 (UCOS2_raw_rep_split_question_mark sg current p Hchar Hnul)).
  unfold task_tcb_init_modular_restore_output, kernel_call_modular_restore_post.
  Exists returned current.
  unfold kernel_continuation_call_closed, kernel_continuation_inv, UCOS2_inv; entailer!.
Qed.
