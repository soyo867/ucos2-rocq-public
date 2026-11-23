Require Import Coq.ZArith.ZArith Coq.Strings.String Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic ConAssertion.
Require Export Ucos2Verify.VC.code.task.spec.task_create_api_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_ext_api_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_name_resources_spec.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.kernel_literal_resources.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** Registration is a change of the logical owner of the existing static
    bytes, not a C write. The public safeExec initial state is selected
    AFTER this registration. A reused source has exactly the same registered
    NameState shape; it needs neither another literal owner nor a fresh key. *)
Definition task_create_name_initial before key p : UCOS2_Verify_State :=
  replace_NameS (task_create_register_default_name before.(NameState) key p) before.

Definition task_create_name_registered p (state : UCOS2_Verify_State) : Prop :=
  exists names key, state.(NameState) = task_create_register_default_name names key p.

Lemma task_create_name_initial_registered : forall before key p,
  task_create_name_registered p (task_create_name_initial before key p).
Proof. intros; exists before.(NameState), key; reflexivity. Qed.

Lemma task_create_name_registered_binding : forall p state,
  task_create_name_registered p state -> task_create_default_name_binding p state.
Proof.
  intros p state [names [key Hnames]].
  unfold task_create_default_name_binding; rewrite Hnames.
  apply task_create_register_default_name_lookup.
Qed.

Lemma task_create_name_registered_transport : forall p before current,
  before.(NameState) = current.(NameState) ->
  task_create_name_registered p before -> task_create_name_registered p current.
Proof. intros p before current Hnames [names [key Hsource]]; exists names, key; congruence. Qed.

(** This is the actual public entry resource, not a pure readable-name
    requirement attached to an application. The fresh alternative owns the
    old callable world and the full real literal pool; the checked producer
    consumes those bytes. The registered alternative owns the registered
    callable world and its exact residual pool. [initial] is the same state
    used by the public arbitrary-X program in BOTH alternatives. *)
Definition task_create_name_world_input environment critical saved_local sg call mask
  (LitMap : string -> Z) (literals : list string) initial : Assertion :=
  (EX before key,
    coq_prop (initial = task_create_name_initial before key (LitMap "?") /\
      before.(NameState).(nameSources) key = None /\
      name_source_disjoint before.(NameState) (name_question_mark_source (LitMap "?")) /\
      literals = ["?"]) &&
    (task_create_continuation_input environment critical saved_local sg call mask before **
      GlobalStrings LitMap)) ||
  (coq_prop (task_create_name_registered (LitMap "?") initial) &&
    (task_create_continuation_input environment critical saved_local sg call mask initial **
      GlobalStrings_missing LitMap literals)).

Lemma task_create_name_world_input_open :
  forall environment critical saved_local sg call mask LitMap literals initial,
  task_create_name_world_input environment critical saved_local sg call mask LitMap literals initial |--
  coq_prop (task_create_name_registered (LitMap "?") initial /\
    task_create_default_name_binding (LitMap "?") initial) &&
  (task_create_continuation_input environment critical saved_local sg call mask initial **
    GlobalStrings_missing LitMap literals).
Proof.
  intros environment critical saved_local sg call mask LitMap literals initial.
  unfold task_create_name_world_input; apply derivable1_orp_elim.
  - Intros before key.
    assert (Hinitial : initial = task_create_name_initial before key (LitMap "?")) by tauto.
    assert (Hliterals : literals = ["?"]) by tauto.
    assert (Hfresh : before.(NameState).(nameSources) key = None) by tauto.
    assert (Hdis : name_source_disjoint before.(NameState)
      (name_question_mark_source (LitMap "?"))) by tauto.
    subst initial literals.
    pose proof (task_create_default_name_continuation_producer environment critical
      saved_local sg call mask before key LitMap Hfresh Hdis) as Hproducer.
    unfold task_tcb_init_continuation_save_input in Hproducer.
    sep_apply_l_atomic Hproducer; Intros.
    pose proof (task_create_name_initial_registered before key (LitMap "?")) as Hregistered.
    unfold task_create_name_initial in *.
    unfold task_tcb_init_continuation_save_input; entailer!.
  - Intros.
    assert (Hregistered : task_create_name_registered (LitMap "?") initial) by assumption.
    pose proof (task_create_name_registered_binding _ _ Hregistered) as Hbinding.
    entailer!.
Qed.

Lemma task_create_name_tcb_result_codes :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original result,
  task_tcb_init_modular_name_call_post environment critical saved_local sg region args task_return lower upper
    initial_name invocation origin mask initial original result |--
  coq_prop (result = 0 \/ result = 66) &&
  task_tcb_init_modular_name_call_post environment critical saved_local sg region args task_return lower upper
    initial_name invocation origin mask initial original result.
Proof.
  intros; unfold task_tcb_init_modular_name_call_post; Intros released returned current.
  assert (Hresult : task_tcb_init_stack_call_result critical sg region args task_return lower upper
    initial_name invocation origin initial result released) by tauto.
  assert (Hcodes : result = 0 \/ result = 66) by (inversion Hresult; auto).
  Exists released returned current; entailer!.
Qed.

Definition task_create_name_api_pre environment critical saved_local sg region args task_return
  lower old_frame upper call mask initial LitMap literals : Assertion :=
  coq_prop (task_invocation_active initial.(TskState)
      call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
    task_create_stack_no_reservation initial call.(os_sched_call_invocation) /\
    task_create_stack_buffer_domain region args task_return lower old_frame upper) &&
  (task_create_name_world_input environment critical saved_local sg call mask LitMap literals initial **
    task_stack_storage region (lower ++ old_frame ++ upper) ** unmap_table_rep sg).

Lemma task_create_name_api_pre_open :
  forall environment critical saved_local sg region args task_return lower old_frame upper
    call mask initial LitMap literals,
  task_create_name_api_pre environment critical saved_local sg region args task_return
    lower old_frame upper call mask initial LitMap literals |--
  coq_prop (task_create_name_registered (LitMap "?") initial /\
    task_create_default_name_binding (LitMap "?") initial) &&
  (task_create_continuation_pre environment critical saved_local sg region args task_return
    lower old_frame upper (LitMap "?") call mask initial ** GlobalStrings_missing LitMap literals).
Proof.
  intros environment critical saved_local sg region args task_return lower old_frame upper
    call mask initial LitMap literals.
  unfold task_create_name_api_pre; Intros.
  sep_apply_l_atomic (task_create_name_world_input_open environment critical saved_local
    sg call mask LitMap literals initial); Intros.
  assert (Hbinding : task_create_default_name_binding (LitMap "?") initial) by tauto.
  assert (Hname : task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args (LitMap "?")) initial).
  { intros _; exists [63].
    unfold task_tcb_init_stack_call_args, task_create_tcb_args.
    destruct args.(createExtension); apply task_create_default_name_binding_readable; exact Hbinding. }
  unfold task_create_continuation_input; Intros.
  unfold task_create_continuation_pre, task_create_stack_entry, task_create_continuation_input.
  entailer!; tauto.
Qed.

(** Loader/static-owner entry construction. The priority, context, buffer
    and arbitrary-X conditions remain the existing public API obligations.
    No premise asks an application to invent readable [63]. *)
Lemma task_create_name_api_fresh_pre :
  forall environment critical saved_local sg region args task_return lower old_frame upper
    call mask before key LitMap,
  before.(NameState).(nameSources) key = None ->
  name_source_disjoint before.(NameState) (name_question_mark_source (LitMap "?")) ->
  task_invocation_active before.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin) ->
  task_create_stack_no_reservation before call.(os_sched_call_invocation) ->
  task_create_stack_buffer_domain region args task_return lower old_frame upper ->
  task_create_continuation_input environment critical saved_local sg call mask before **
    task_stack_storage region (lower ++ old_frame ++ upper) ** unmap_table_rep sg ** GlobalStrings LitMap |--
  task_create_name_api_pre environment critical saved_local sg region args task_return
    lower old_frame upper call mask (task_create_name_initial before key (LitMap "?")) LitMap ["?"].
Proof.
  intros environment critical saved_local sg region args task_return lower old_frame upper
    call mask before key LitMap Hfresh Hdis Hactive Hreservation Hbuffer.
  unfold task_create_name_api_pre.
  assert (Hdomain : task_invocation_active
      (task_create_name_initial before key (LitMap "?")).(TskState)
      call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
    task_create_stack_no_reservation (task_create_name_initial before key (LitMap "?"))
      call.(os_sched_call_invocation) /\
    task_create_stack_buffer_domain region args task_return lower old_frame upper)
    by (unfold task_create_name_initial, task_create_stack_no_reservation in *; cbn; tauto).
  assert (Hsource : task_create_continuation_input environment critical saved_local sg call mask before **
    GlobalStrings LitMap |-- task_create_name_world_input environment critical saved_local sg call mask
      LitMap ["?"] (task_create_name_initial before key (LitMap "?"))).
  { unfold task_create_name_world_input; Left; Exists before key; entailer!. }
  entailer!; sep_apply_r_atomic Hsource; entailer!.
Qed.

Lemma task_create_name_api_registered_pre :
  forall environment critical saved_local sg region args task_return lower old_frame upper
    call mask initial LitMap literals,
  task_create_name_registered (LitMap "?") initial ->
  task_create_continuation_pre environment critical saved_local sg region args task_return
    lower old_frame upper (LitMap "?") call mask initial ** GlobalStrings_missing LitMap literals |--
  task_create_name_api_pre environment critical saved_local sg region args task_return
    lower old_frame upper call mask initial LitMap literals.
Proof.
  intros environment critical saved_local sg region args task_return lower old_frame upper
    call mask initial LitMap literals Hregistered.
  unfold task_create_continuation_pre, task_create_stack_entry; Intros.
  assert (Hsource : task_create_continuation_input environment critical saved_local sg call mask initial **
    GlobalStrings_missing LitMap literals |--
    task_create_name_world_input environment critical saved_local sg call mask LitMap literals initial).
  { unfold task_create_name_world_input; Right; entailer!. }
  unfold task_create_name_api_pre.
  entailer!; sep_apply_r_atomic Hsource; entailer!; tauto.
Qed.

(** A concrete static-registration choice for the existing empty NameState
    initializer. Neither a fresh key nor disjointness is demanded from an
    application: key 0 and the empty byte domain establish them here. The
    surrounding real callable heap remains an explicit source obligation. *)
Lemma task_create_name_api_empty_pre :
  forall environment critical saved_local sg region args task_return lower old_frame upper
    call mask before LitMap,
  before.(NameState) = empty_name_resources ->
  task_invocation_active before.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin) ->
  task_create_stack_no_reservation before call.(os_sched_call_invocation) ->
  task_create_stack_buffer_domain region args task_return lower old_frame upper ->
  task_create_continuation_input environment critical saved_local sg call mask before **
    task_stack_storage region (lower ++ old_frame ++ upper) ** unmap_table_rep sg ** GlobalStrings LitMap |--
  task_create_name_api_pre environment critical saved_local sg region args task_return
    lower old_frame upper call mask (task_create_name_initial before 0 (LitMap "?")) LitMap ["?"].
Proof.
  intros environment critical saved_local sg region args task_return lower old_frame upper
    call mask before LitMap Hempty Hactive Hreservation Hbuffer.
  apply task_create_name_api_fresh_pre; try assumption.
  - rewrite Hempty; reflexivity.
  - rewrite Hempty; intros q Hq; reflexivity.
Qed.
