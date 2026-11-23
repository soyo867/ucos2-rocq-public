Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare safeexec_lib.
Require Export Ucos2Verify.VC.code.task.spec.task_create_name_api_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_name_set_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_ext_timer_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.lib.kernel_literal_resources.

Import ListNotations UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac_scope.

(** Selected V2.93.01 statistics-task profile: this descriptor is the actual static
    OSTaskStatStk array, not an allocation or an additional byte owner. Its
    [base] must be bound to that C symbol by the eventual function contract. *)
Definition init_task_stat_stack_region (base : Z) : TaskStackRegion :=
  {| stackRegionBase := base; stackRegionWords := 128;
     stackRegionGrowsDown := true |}.

Definition init_task_stat_create_args (entry base : Z) : TaskCreateArgs :=
  {| createEntry := entry; createArgument := 0;
     createStackTop := base + 508; createPriority := 62;
     createExtension := TaskCreateExtended 65534 base 128 0 3 |}.

Lemma init_task_stat_create_arguments : forall entry base,
  task_create_ext_arguments (init_task_stat_create_args entry base)
    entry 0 (base + 508) 62 65534 base 128 0 3.
Proof. intros; unfold task_create_ext_arguments, init_task_stat_create_args; cbn; repeat split; lia. Qed.

Lemma init_task_stat_stack_geometry : forall base,
  task_stack_region_end (init_task_stat_stack_region base) = base + 512 /\
  task_stack_region_top (init_task_stat_stack_region base) = base + 508 /\
  task_stack_region_bottom (init_task_stat_stack_region base) = base.
Proof.
  intros; unfold task_stack_region_end, task_stack_region_top,
    task_stack_region_bottom, init_task_stat_stack_region; cbn;
    repeat split; ring.
Qed.

Lemma init_task_stat_stack_storage_eq : forall base words,
  task_stack_storage (init_task_stat_stack_region base) words =
  UIntArray.mixed_full base 128 words.
Proof. reflexivity. Qed.

Lemma init_task_stat_stack_bounds : forall base,
  valid_task_stack_region (init_task_stat_stack_region base) ->
  0 < base /\ base mod 4 = 0 /\ base + 512 <= 4294967295 /\
  base <= base + 508 < base + 512.
Proof.
  intros base H; unfold valid_task_stack_region, task_stack_region_end,
    init_task_stat_stack_region in H; cbn in H; lia.
Qed.

(** The ABI only guarantees four-byte alignment for this OS_STK array.
    The port aligns top+4 down to eight bytes before placing its frame. *)
Definition init_task_stat_frame_first (base : Z) : Z :=
  (task_stack_init_sp TaskStackNoVFP (base + 508) - base) / 4.

Lemma init_task_stat_frame_geometry : forall base,
  valid_task_stack_region (init_task_stat_stack_region base) ->
  111 <= init_task_stat_frame_first base <= 112 /\
  task_stack_init_sp TaskStackNoVFP (base + 508) =
    base + init_task_stat_frame_first base * 4.
Proof.
  intros base Hregion.
  destruct (init_task_stat_stack_bounds base Hregion) as [Hbase [Hmod [Hend Htop]]].
  pose proof (Z.div_mod base 4 ltac:(lia)) as Hdiv.
  pose proof (task_stack_init_aligned_top_bounds (base + 508) ltac:(lia)) as Halign.
  unfold task_stack_init_aligned_top in Halign.
  replace (base + 508 + 4) with (base + 512) in Halign by lia.
  assert (Hmultiple : task_stack_init_sp TaskStackNoVFP (base + 508) - base =
    (2 * ((base + 512) / 8) - 16 - base / 4) * 4).
  { change ((base + 508 + 4) / 8 * 8 - 64 - base =
      (2 * ((base + 512) / 8) - 16 - base / 4) * 4).
    replace (base + 508 + 4) with (base + 512) by lia; lia. }
  assert (Hfirst : init_task_stat_frame_first base =
    2 * ((base + 512) / 8) - 16 - base / 4).
  { unfold init_task_stat_frame_first; rewrite Hmultiple, Z.div_mul by lia; reflexivity. }
  rewrite Hfirst; split; lia.
Qed.

(** The stack-domain premise retains actual static-array ownership/ABI bounds.
    The lemma only derives this function's sublayout; arithmetic never
    manufactures storage. *)
Lemma init_task_stat_stack_buffer_domain : forall entry base task_return lower old_frame upper,
  valid_task_stack_region (init_task_stat_stack_region base) ->
  Zlength lower = init_task_stat_frame_first base -> Zlength old_frame = 16 ->
  Zlength upper = 112 - init_task_stat_frame_first base ->
  0 <= entry < 4294967296 -> 0 <= task_return < 4294967296 ->
  task_create_stack_buffer_domain (init_task_stat_stack_region base)
    (init_task_stat_create_args entry base) task_return lower old_frame upper.
Proof.
  intros entry base task_return lower old_frame upper Hregion Hlower Hframe Hupper Hentry Hreturn.
  unfold task_create_stack_buffer_domain; split.
  - unfold task_create_stack_layout; split.
    + unfold task_create_stack_region_binding; split; [exact Hregion|].
      split; [reflexivity|].
      symmetry; apply (proj1 (proj2 (init_task_stat_stack_geometry base))).
    + split.
      * change (task_stack_init_sp TaskStackNoVFP (base + 508) = base + Zlength lower * 4).
        rewrite Hlower; exact (proj2 (init_task_stat_frame_geometry base Hregion)).
      * change (128 = Zlength lower + 16 + Zlength upper).
        rewrite Hlower, Hupper; lia.
  - split; [exact Hframe|].
    change (0 <= entry < 4294967296 /\ 0 <= 0 < 4294967296 /\
      0 <= task_return < 4294967296).
    split; [exact Hentry|]; split; [lia|exact Hreturn].
Qed.

Lemma init_task_stat_clear_binding : forall entry base lower old_frame upper,
  Zlength (lower ++ old_frame ++ upper) = 128 ->
  task_create_ext_clear_binding (init_task_stat_stack_region base)
    (init_task_stat_create_args entry base)
    (lower ++ old_frame ++ upper) [] (lower ++ old_frame ++ upper) [].
Proof.
  intros entry base lower old_frame upper Hlength _.
  change ((lower ++ old_frame ++ upper) = (lower ++ old_frame ++ upper) ++ [] /\
    base = base + 0 /\ 128 = Zlength (lower ++ old_frame ++ upper)).
  rewrite app_nil_r, Z.add_0_r.
  repeat split; lia.
Qed.

(** Exact ordered composition of the two existing public callee programs.
    Both error bytes are ignored by this void helper. No task identity,
    successful creation/naming or eventual return is manufactured here. *)
Definition init_task_stat_program environment critical sg entry base task_return
  after_lower after_upper initial_name call mask name : program UCOS2_Verify_State unit :=
  StateRelMonad.bind
    (task_create_program environment critical sg (init_task_stat_stack_region base)
      (init_task_stat_create_args entry base) task_return
      after_lower after_upper initial_name call mask)
    (fun _ => StateRelMonad.bind
      (task_name_set_program critical sg call.(os_sched_call_invocation) 62 name)
      (fun _ => StateRelMonad.ret tt)).

Definition init_task_stat_create_continuation critical sg invocation name
  (X : unit -> UCOS2_Verify_State -> Prop) : Z -> UCOS2_Verify_State -> Prop :=
  fun _ current => task_name_set_safe critical sg invocation 62 name current
    (fun _ final => X tt final).

Lemma init_task_stat_safe_composition : forall environment critical sg entry base task_return
  after_lower after_upper initial_name call mask name before X,
  safeExec (eq before)
    (init_task_stat_program environment critical sg entry base task_return
      after_lower after_upper initial_name call mask name) X <->
  task_create_safe before
    (task_create_program environment critical sg (init_task_stat_stack_region base)
      (init_task_stat_create_args entry base) task_return
      after_lower after_upper initial_name call mask)
    (init_task_stat_create_continuation critical sg call.(os_sched_call_invocation) name X).
Proof.
  intros; unfold init_task_stat_program, task_create_safe,
    init_task_stat_create_continuation, task_name_set_safe, safeExec, safe, weakestpre.
  split.
  - intros [start [Hstart Hsafe]]; subst start.
    exists before; split; [reflexivity|].
    intros create_error middle Hcreate; exists middle; split; [reflexivity|].
    intros name_error final Hname.
    apply (Hsafe tt final).
    exists create_error, middle; split; [exact Hcreate|].
    exists name_error, final; split; [exact Hname|split; reflexivity].
  - intros [start [Hstart Hsafe]]; subst start.
    exists before; split; [reflexivity|].
    intros result final [create_error [middle [Hcreate
      [name_error [named [Hname [Hresult Hend]]]]]]].
    subst result final.
    destruct (Hsafe create_error middle Hcreate) as [same [Hsame Hname_safe]].
    subst same; exact (Hname_safe name_error named Hname).
Qed.

Lemma init_task_stat_name_admission : forall critical sg invocation name before chars,
  readable_name before.(NameState) name chars ->
  task_name_set_admission critical sg invocation 62 name before.
Proof.
  intros critical sg invocation name before chars Hread _ _ _ acquired Hinterval.
  split; [intros Hself; discriminate|].
  intros prio tid t Hresolved Htarget; exists chars.
  rewrite <- (critical_region_interval_preserves_name_state _ _ _ _ _ Hinterval).
  exact Hread.
Qed.

Lemma init_task_stat_create_return_continuation : forall critical sg invocation name
  create_error current X,
  task_create_safe current (StateRelMonad.ret create_error)
    (init_task_stat_create_continuation critical sg invocation name X) ->
  task_name_set_safe critical sg invocation 62 name current (fun _ final => X tt final).
Proof.
  intros critical sg invocation name create_error current X [start [Hstart Hsafe]].
  subst start; apply (Hsafe create_error current); split; reflexivity.
Qed.

(** Reversible resource view for the second call. The residual remains
    indexed by the actual CreateExt return, not silently by NameSet's later
    endpoint. In particular this view does not assert OSRunning = true. *)
Definition init_task_stat_continuation_residual environment saved_local call state : Assertion :=
  os_sched_context_resources environment.(task_stack_call_external) call **
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
      state.(TskState) (task_create_continuation_local saved_local))
    state.(TskState).(parkedTaskStacks).

Lemma init_task_stat_name_call_resource_equiv : forall environment critical saved_local sg call mask state,
  task_create_continuation_input environment critical saved_local sg call mask state --||--
  coq_prop (UCOS2_state_inv sg state /\
    task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
  (task_name_set_closed environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) mask state **
   init_task_stat_continuation_residual environment saved_local call state).
Proof.
  intros; unfold task_create_continuation_input, kernel_call_execution_owned,
    task_name_set_closed, init_task_stat_continuation_residual; split; entailer!.
Qed.

(** The internal boot helper is called before OSStart.  This observation
    is proved from the actual public creation program and its existing
    completed-call control rely; it does not strengthen either public API. *)
Definition init_task_stat_boot_frame before after : Prop :=
  after.(SchedState).(isRunning) = false /\ before.(NameState) = after.(NameState).
Definition init_task_stat_stopped (state : UCOS2_Verify_State) : Prop :=
  state.(SchedState).(isRunning) = false.

Definition init_task_stat_preserves_boot {A : Type}
  (code : program UCOS2_Verify_State A) : Prop :=
  forall before result after,
    before.(SchedState).(isRunning) = false -> code before result after ->
    init_task_stat_boot_frame before after.

Lemma init_task_stat_bind_preserves_boot : forall A B
  (first : program UCOS2_Verify_State A) (next : A -> program UCOS2_Verify_State B),
  init_task_stat_preserves_boot first ->
  (forall result, init_task_stat_preserves_boot (next result)) ->
  init_task_stat_preserves_boot (StateRelMonad.bind first next).
Proof.
  intros A B first next Hfirst Hnext before result after Hstop
    [value [middle [Hone Htwo]]].
  destruct (Hfirst _ _ _ Hstop Hone) as [Hmiddle Hnames].
  destruct (Hnext value _ _ _ Hmiddle Htwo) as [Hafter Hnames']; split; congruence.
Qed.

Lemma init_task_stat_ret_preserves_boot : forall A (value : A),
  init_task_stat_preserves_boot (StateRelMonad.ret value).
Proof. intros A value before result after Hstop [-> ->]; split; auto. Qed.

Lemma init_task_stat_save_preserves_boot : forall environment critical sg call mask,
  init_task_stat_preserves_boot (task_create_save_program environment critical sg call mask).
Proof.
  intros environment critical sg call mask before result after Hstop [Hsource [_ [Hrun _]]].
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsource) as Hi.
  split; [congruence|].
  eapply critical_region_interval_preserves_name_state; exact Hi.
Qed.

Lemma init_task_stat_restore_preserves_boot : forall environment critical sg call,
  init_task_stat_preserves_boot (task_create_restore_program environment critical sg call).
Proof.
  intros environment critical sg call before result after Hstop [Hsource [_ [Hrun _]]].
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hsource)
    as [Hi _].
  split; [congruence|].
  eapply critical_region_interval_preserves_name_state; exact Hi.
Qed.

Lemma init_task_stat_restore_return_preserves_boot : forall environment critical sg call error,
  init_task_stat_preserves_boot
    (task_create_restore_return_program environment critical sg call error).
Proof.
  intros; apply init_task_stat_bind_preserves_boot.
  - apply init_task_stat_restore_preserves_boot.
  - intros; apply init_task_stat_ret_preserves_boot.
Qed.

Lemma init_task_stat_rollback_preserves_boot : forall environment critical sg args call mask,
  init_task_stat_preserves_boot
    (task_create_rollback_program environment critical sg args call mask).
Proof.
  intros; apply init_task_stat_bind_preserves_boot.
  - apply init_task_stat_save_preserves_boot.
  - intros result; apply init_task_stat_bind_preserves_boot.
    + intros before value after Hstop Hupdate; unfold update', update in Hupdate;
        subst after; split; [exact Hstop|reflexivity].
    + intros; apply init_task_stat_restore_return_preserves_boot.
Qed.

Lemma init_task_stat_tcb_return_preserves_boot : forall environment critical sg args call mask error,
  init_task_stat_preserves_boot
    (task_create_tcb_return_program environment critical sg args call mask error).
Proof.
  intros; unfold task_create_tcb_return_program; destruct (Z.eqb error 0).
  - intros before result after Hstop [running [middle [[Hrunning Hmiddle] Hnext]]].
    subst middle running; rewrite Hstop in Hnext.
    destruct Hnext as [Hresult Hafter]; subst after; split; [exact Hstop|reflexivity].
  - apply init_task_stat_rollback_preserves_boot.
Qed.

Lemma init_task_stat_initialized_preserves_boot :
  forall environment critical sg region args task_return lower upper initial_name call mask,
  init_task_stat_preserves_boot
    (task_create_initialized_program environment critical sg region args task_return
      lower upper initial_name call mask).
Proof.
  intros; apply init_task_stat_bind_preserves_boot.
  - intros before result after Hstop
      [released [Hresult [Hinv [Hsource [Hsame [Hreturned [Hready [[Hnormal [Hrun Hintr]] Hnames]]]]]]]].
    split; [congruence|exact Hnames].
  - intros; apply init_task_stat_tcb_return_preserves_boot.
Qed.

Lemma init_task_stat_initialize_preserves_boot :
  forall environment critical sg region args task_return lower upper initial_name call mask,
  init_task_stat_preserves_boot
    (task_create_initialize_program environment critical sg region args task_return
      lower upper initial_name call mask).
Proof.
  intros; apply init_task_stat_bind_preserves_boot.
  - intros before result after Hstop [Hsp [Hentry [Hsource [[Hnormal [Hrun Hintr]] Hnames]]]].
    split; [congruence|exact Hnames].
  - intros; apply init_task_stat_initialized_preserves_boot.
Qed.

Lemma init_task_stat_acquired_preserves_boot :
  forall environment critical sg region args task_return lower upper initial_name original call mask,
  init_task_stat_preserves_boot
    (task_create_acquired_program environment critical sg region args task_return
      lower upper initial_name original call mask).
Proof.
  intros environment critical sg region args task_return lower upper initial_name original call mask
    before result after Hstop [acquired [middle [[Hacquired Hmiddle] Hnext]]].
  subst middle acquired.
  destruct (Z.ltb 0 (task_create_stack_nesting before)).
  - exact (init_task_stat_restore_return_preserves_boot environment critical sg call 60 before result after Hstop Hnext).
  - destruct (Z.eqb (task_create_stack_priority sg args before) 0).
    + destruct Hnext as [value [reserved [Hreserve Hreserved]]].
      unfold update', update in Hreserve.
      change (reserved = task_create_stack_reserved args original before) in Hreserve.
      subst reserved.
      destruct Hreserved as [returned [restored [Hrestore Hinit]]].
      destruct (init_task_stat_restore_preserves_boot environment critical sg call
        (task_create_stack_reserved args original before) returned restored Hstop Hrestore) as [Hrestored Hnames].
      destruct (init_task_stat_initialize_preserves_boot environment critical sg region args task_return
        lower upper initial_name returned mask _ _ _ Hrestored Hinit) as [Hafter Hnames'];
        split; [exact Hafter|cbn in Hnames; congruence].
    + exact (init_task_stat_restore_return_preserves_boot environment critical sg call 40 before result after Hstop Hnext).
Qed.

Lemma init_task_stat_create_preserves_boot :
  forall environment critical sg region args task_return lower upper initial_name call mask,
  init_task_stat_preserves_boot
    (task_create_program environment critical sg region args task_return
      lower upper initial_name call mask).
Proof.
  intros; unfold task_create_program; destruct (Z.ltb 63 (unsigned_last_nbits (createPriority args) 32)).
  - apply init_task_stat_ret_preserves_boot.
  - apply init_task_stat_bind_preserves_boot.
    + apply init_task_stat_save_preserves_boot.
    + intros; apply init_task_stat_acquired_preserves_boot.
Qed.

Definition init_task_stat_name_chars : list Z := [117; 67; 47; 79; 83; 45; 73; 73; 32; 83; 116; 97; 116].
Definition init_task_stat_name_domain (p : Z) : list Z :=
  [p; p+1; p+2; p+3; p+4; p+5; p+6; p+7; p+8; p+9; p+10; p+11; p+12; p+13].
Definition init_task_stat_name_source (p : Z) : NameStorageSource :=
  {| nameStorageOrigin := StaticNameStorage; nameStorageDomain := init_task_stat_name_domain p |}.
Definition init_task_stat_name_bytes (p q : Z) : option Z :=
  Some (Znth (q-p) (init_task_stat_name_chars ++ [0]) 0).
Definition init_task_stat_register_name names key p : NameResourceState :=
  name_register_source names key (init_task_stat_name_source p) (init_task_stat_name_bytes p).

Lemma init_task_stat_name_domain_in_range : forall p q,
  In q (init_task_stat_name_domain p) <-> p <= q <= p+13.
Proof. intros; unfold init_task_stat_name_domain; cbn; lia. Qed.

Lemma init_task_stat_name_domain_nodup : forall p,
  NoDup (init_task_stat_name_domain p).
Proof. intro p; unfold init_task_stat_name_domain; repeat constructor; cbn; lia. Qed.

Lemma init_task_stat_name_source_valid : forall p,
  name_source_bytes_valid (init_task_stat_name_source p) (init_task_stat_name_bytes p).
Proof.
  intro p; split; [apply init_task_stat_name_domain_nodup|].
  intros q Hin; apply init_task_stat_name_domain_in_range in Hin.
  exists (Znth (q-p) (init_task_stat_name_chars ++ [0]) 0); split; [reflexivity|].
  assert (Hcases : In (q-p) [0;1;2;3;4;5;6;7;8;9;10;11;12;13]) by (cbn; lia).
  cbn in Hcases; repeat destruct Hcases as [Hcase|Hcases];
    try contradiction; rewrite <- Hcase; vm_compute; intuition discriminate.
Qed.

Lemma init_task_stat_register_name_lookup : forall names key p i,
  0 <= i <= 13 ->
  (init_task_stat_register_name names key p).(nameBytes) (p+i) =
    Some (Znth i (init_task_stat_name_chars ++ [0]) 0).
Proof.
  intros names key p i Hi; unfold init_task_stat_register_name, name_register_source.
  cbn [nameBytes nameStorageDomain init_task_stat_name_source].
  destruct (in_dec Z.eq_dec (p+i) (init_task_stat_name_domain p)).
  - unfold init_task_stat_name_bytes; f_equal; f_equal; lia.
  - exfalso; apply n, init_task_stat_name_domain_in_range; lia.
Qed.

Lemma init_task_stat_register_name_readable : forall names key p,
  readable_name (init_task_stat_register_name names key p) p init_task_stat_name_chars.
Proof.
  intros; split.
  - unfold init_task_stat_name_chars; repeat constructor; lia.
  - split.
    + intros i c Hnth.
      assert (Hi : (i < 13)%nat).
      { assert (Hbound : (i < List.length init_task_stat_name_chars)%nat).
        { apply nth_error_Some; rewrite Hnth; discriminate. }
        exact Hbound. }
      rewrite init_task_stat_register_name_lookup by lia.
      f_equal; unfold Znth; rewrite Nat2Z.id.
      rewrite app_nth1 by exact Hi.
      eapply nth_error_nth; exact Hnth.
    + change ((init_task_stat_register_name names key p).(nameBytes) (p+13) = Some 0).
      rewrite init_task_stat_register_name_lookup by lia; reflexivity.
Qed.

Lemma init_task_stat_register_name_preserves_readable : forall names key p name chars,
  name_source_disjoint names (init_task_stat_name_source p) ->
  readable_name names name chars ->
  readable_name (init_task_stat_register_name names key p) name chars.
Proof.
  intros names key p name chars Hdis [Hchars [Hbytes Hnul]].
  split; [exact Hchars|]; split.
  - intros i c Hi; specialize (Hbytes i c Hi).
    unfold init_task_stat_register_name, name_register_source; cbn [nameBytes].
    destruct (in_dec Z.eq_dec (name + Z.of_nat i) (nameStorageDomain (init_task_stat_name_source p)));
      [rewrite Hdis in Hbytes by assumption; discriminate|exact Hbytes].
  - unfold init_task_stat_register_name, name_register_source; cbn [nameBytes].
    destruct (in_dec Z.eq_dec (name + Z.of_nat (List.length chars))
      (nameStorageDomain (init_task_stat_name_source p)));
      [rewrite Hdis in Hnul by assumption; discriminate|exact Hnul].
Qed.

Lemma init_task_stat_register_name_preserves_state_inv : forall sg before key p,
  UCOS2_state_inv sg before -> before.(NameState).(nameSources) key = None ->
  name_source_disjoint before.(NameState) (init_task_stat_name_source p) ->
  UCOS2_state_inv sg (replace_NameS (init_task_stat_register_name before.(NameState) key p) before).
Proof.
  intros sg before key p Hvalid Hfresh Hdis.
  assert (Hnames : valid_name_resources (init_task_stat_register_name before.(NameState) key p)).
  { apply name_register_source_preserves_resources; try assumption.
    - unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto.
    - apply init_task_stat_name_source_valid. }
  assert (Hroots : kernel_names_valid sg
    (replace_NameS (init_task_stat_register_name before.(NameState) key p) before)).
  { intros name Hroot; change (kernel_name_root sg before name) in Hroot.
    destruct (UCOS2_state_inv_names_valid sg before Hvalid name Hroot) as [chars Hread].
    exists chars; eapply init_task_stat_register_name_preserves_readable; eassumption. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *; cbn; intuition.
Qed.

Definition init_task_stat_name_cells p : Assertion :=
  iter_sepcon (map (fun q => name_byte_rep q
    (Znth (q-p) (init_task_stat_name_chars ++ [0]) 0)) (init_task_stat_name_domain p)).

Lemma init_task_stat_name_byte_char_equiv : forall p c,
  0 <= c <= 127 -> p # Char |-> c --||-- p # UChar |-> c.
Proof.
  intros; unfold store_char, store_uchar.
  replace Byte.min_signed with (-128) by reflexivity.
  replace Byte.max_signed with 127 by reflexivity.
  replace Byte.max_unsigned with 255 by reflexivity.
  split; entailer!; lia.
Qed.

Lemma init_task_stat_name_literal_cells : forall p,
  store_stringLit p "uC/OS-II Stat" --||-- init_task_stat_name_cells p.
Proof.
  intro p; unfold store_stringLit, init_task_stat_name_cells.
  change (coq_prop (valid_stringLit "uC/OS-II Stat") &&
    CharArray.full p 14 (init_task_stat_name_chars ++ [0]) --||--
    iter_sepcon (map (fun q => name_byte_rep q
      (Znth (q-p) (init_task_stat_name_chars ++ [0]) 0)) (init_task_stat_name_domain p))).
  unfold init_task_stat_name_domain, init_task_stat_name_chars, name_byte_rep.
  cbn [map app].
  unfold CharArray.full, store_array, store_array_rec, StoreCharAsElement.storeA.
  rewrite sizeof_char.
  repeat match goal with |- context [(p + ?n - p)%Z] => replace (p+n-p) with n by lia end.
  replace (p-p) with 0 by lia.
  cbn [Znth Z.to_nat Pos.to_nat Pos.iter_op Nat.add].
  rewrite ?Z.add_0_r, ?Z.mul_1_r.
  repeat match goal with |- context [store_char ?a ?c] =>
    rewrite (init_task_stat_name_byte_char_equiv a c ltac:(lia)) end.
  assert (Hvalid : valid_stringLit "uC/OS-II Stat").
  { unfold valid_stringLit, valid_string; cbn; repeat constructor; lia. }
  split; rewrite ?derivable1_iter_sepcon_l, <- ?derivable1_iter_sepcon_r;
    cbn [fold_left]; entailer!; try lia.
Qed.

Fixpoint init_task_stat_name_remainder (bytes : Z -> option Z) (points : list Z) : Assertion :=
  match points with
  | [] => store_map name_byte_rep bytes
  | q :: rest => init_task_stat_name_remainder (kernel_map_set bytes q None) rest
  end.

Lemma init_task_stat_name_map_split_list : forall points bytes contents,
  NoDup points ->
  (forall q, In q points -> bytes q = Some (contents q)) ->
  store_map name_byte_rep bytes --||--
    iter_sepcon (map (fun q => name_byte_rep q (contents q)) points) **
    init_task_stat_name_remainder bytes points.
Proof.
  induction points as [|q points IH]; intros bytes contents Hnodup Hbytes.
  - cbn [map init_task_stat_name_remainder]; split;
      rewrite ?derivable1_iter_sepcon_l, <- ?derivable1_iter_sepcon_r;
      cbn [fold_left]; entailer!.
  - inversion Hnodup as [|q' points' Hnotin Htail]; subst q' points'.
    assert (Hq : bytes q = Some (contents q)) by (apply Hbytes; left; reflexivity).
    assert (Hsingle : iter_sepcon [name_byte_rep q (contents q)] --||-- name_byte_rep q (contents q)).
    { split; [rewrite derivable1_iter_sepcon_l|rewrite <- derivable1_iter_sepcon_r]; cbn; entailer!. }
    assert (Hrest : forall p, In p points -> kernel_map_set bytes q None p = Some (contents p)).
    { intros p Hp; rewrite kernel_map_set_other; [apply Hbytes; right; exact Hp|].
      intro Heq; subst p; contradiction. }
    specialize (IH (kernel_map_set bytes q None) contents Htail Hrest).
    change (store_map name_byte_rep bytes --||--
      iter_sepcon ([name_byte_rep q (contents q)] ++ map (fun p => name_byte_rep p (contents p)) points) **
      init_task_stat_name_remainder (kernel_map_set bytes q None) points).
    split.
    + sep_apply_l_atomic (store_map_split name_byte_rep q (contents q) bytes Hq).
      sep_apply_l_atomic (proj1 (store_name_bytes_missing_byte_equiv bytes q)).
      sep_apply_l_atomic (proj1 IH).
      rewrite <- derivable1_sepcon_iter_sepcon1, Hsingle; entailer!.
    + rewrite derivable1_sepcon_iter_sepcon2, Hsingle.
      sep_apply_l_atomic (proj2 IH).
      sep_apply_l_atomic (proj2 (store_name_bytes_missing_byte_equiv bytes q)).
      sep_apply_l_atomic (store_map_merge name_byte_rep q (contents q) bytes Hq); entailer!.
Qed.

Lemma init_task_stat_readable_name_bytes : forall names p q,
  readable_name names p init_task_stat_name_chars ->
  In q (init_task_stat_name_domain p) ->
  names.(nameBytes) q = Some (Znth (q-p) (init_task_stat_name_chars ++ [0]) 0).
Proof.
  intros names p q [_ [Hchars Hnul]] Hq.
  apply init_task_stat_name_domain_in_range in Hq.
  assert (Hcases : In (q-p) [0;1;2;3;4;5;6;7;8;9;10;11;12;13]) by (cbn; lia).
  cbn in Hcases; repeat destruct Hcases as [Hcase|Hcases]; try contradiction;
    let i := match type of Hcase with ?i = _ => i end in
    replace q with (p+i) by lia;
    repeat match goal with |- context [(p + ?n - p)%Z] => replace (p+n-p) with n by lia end;
    first [exact (Hchars (Z.to_nat i) _ eq_refl) | exact Hnul].
Qed.

Lemma init_task_stat_name_bytes_split_literal : forall names p,
  readable_name names p init_task_stat_name_chars ->
  store_name_bytes names --||--
    store_stringLit p "uC/OS-II Stat" **
    init_task_stat_name_remainder names.(nameBytes) (init_task_stat_name_domain p).
Proof.
  intros names p Hread; rewrite init_task_stat_name_literal_cells.
  unfold store_name_bytes, init_task_stat_name_cells.
  apply init_task_stat_name_map_split_list.
  - apply init_task_stat_name_domain_nodup.
  - intros; eapply init_task_stat_readable_name_bytes; eassumption.
Qed.

Lemma init_task_stat_register_name_storage : forall names key p,
  name_source_disjoint names (init_task_stat_name_source p) ->
  store_name_bytes names ** store_stringLit p "uC/OS-II Stat" |--
  store_name_bytes (init_task_stat_register_name names key p).
Proof.
  intros names key p Hdis.
  unfold store_name_bytes, store_map; Intros domain.
  assert (Hdomain : forall q, In q domain <-> exists b, names.(nameBytes) q = Some b) by assumption.
  assert (Hnodup : NoDup domain) by assumption.
  assert (Hold : forall q, In q domain ->
    (init_task_stat_register_name names key p).(nameBytes) q = names.(nameBytes) q).
  { intros q Hq; destruct (proj1 (Hdomain q) Hq) as [b Hb].
    unfold init_task_stat_register_name, name_register_source; cbn [nameBytes].
    destruct (in_dec Z.eq_dec q (nameStorageDomain (init_task_stat_name_source p)));
      [rewrite Hdis in Hb by assumption; discriminate|reflexivity]. }
  assert (Hmap : map (fun q => match (init_task_stat_register_name names key p).(nameBytes) q
      with Some b => name_byte_rep q b | None => emp end) domain =
    map (fun q => match names.(nameBytes) q with Some b => name_byte_rep q b | None => emp end) domain).
  { apply map_ext_in; intros q Hq; rewrite Hold by exact Hq; reflexivity. }
  assert (Hnew : forall q, In q (init_task_stat_name_domain p) ->
    (init_task_stat_register_name names key p).(nameBytes) q = init_task_stat_name_bytes p q).
  { intros q Hq; unfold init_task_stat_register_name, name_register_source.
    cbn [nameBytes nameStorageDomain init_task_stat_name_source].
    destruct (in_dec Z.eq_dec q (init_task_stat_name_domain p)); tauto. }
  assert (Hnewmap : map (fun q => match (init_task_stat_register_name names key p).(nameBytes) q
      with Some b => name_byte_rep q b | None => emp end) (init_task_stat_name_domain p) =
    map (fun q => name_byte_rep q (Znth (q-p) (init_task_stat_name_chars ++ [0]) 0))
      (init_task_stat_name_domain p)).
  { apply map_ext_in; intros q Hq; rewrite Hnew by exact Hq; reflexivity. }
  Exists (domain ++ init_task_stat_name_domain p); entailer!.
  - rewrite map_app, Hmap, Hnewmap.
    rewrite <- derivable1_sepcon_iter_sepcon1; entailer!.
    apply (proj1 (init_task_stat_name_literal_cells p)).
  - apply NoDup_app; repeat split; try assumption.
    + apply init_task_stat_name_domain_nodup.
    + intros q Hq Hnewq; destruct (proj1 (Hdomain q) Hq) as [b Hb].
      rewrite Hdis in Hb by exact Hnewq; discriminate.
  - intro q; rewrite in_app_iff; split.
    + intros [Hq|Hq].
      * rewrite Hold by exact Hq; apply Hdomain; exact Hq.
      * rewrite Hnew by exact Hq; eexists; reflexivity.
    + intros [b Hb]; destruct (in_dec Z.eq_dec q (init_task_stat_name_domain p)) as [Hin|Hout];
        [right; exact Hin|left].
      apply Hdomain; exists b.
      unfold init_task_stat_register_name, name_register_source in Hb.
      cbn [nameBytes nameStorageDomain init_task_stat_name_source] in Hb.
      destruct (in_dec Z.eq_dec q (init_task_stat_name_domain p)); [contradiction|exact Hb].
Qed.

Lemma init_task_stat_register_name_raw_rep : forall sg before key p,
  name_source_disjoint before.(NameState) (init_task_stat_name_source p) ->
  UCOS2_raw_rep sg before ** store_stringLit p "uC/OS-II Stat" |--
  UCOS2_raw_rep sg (replace_NameS (init_task_stat_register_name before.(NameState) key p) before).
Proof.
  intros sg before key p Hdis.
  rewrite (UCOS2_raw_rep_split_module sg before NamesModule).
  rewrite (UCOS2_raw_rep_split_module sg
    (replace_NameS (init_task_stat_register_name before.(NameState) key p) before) NamesModule).
  change (store_name_bytes before.(NameState) ** UCOS2_raw_rep_missing_names sg before **
    store_stringLit p "uC/OS-II Stat" |--
    store_name_bytes (init_task_stat_register_name before.(NameState) key p) **
    UCOS2_raw_rep_missing_names sg before).
  sep_apply_l_atomic (init_task_stat_register_name_storage before.(NameState) key p Hdis); entailer!.
Qed.

Definition init_task_stat_name_initial before key name : UCOS2_Verify_State :=
  replace_NameS (init_task_stat_register_name before.(NameState) key name) before.

Lemma init_task_stat_name_continuation_producer :
  forall environment critical saved_local sg call mask before key LitMap,
  before.(NameState).(nameSources) key = None ->
  name_source_disjoint before.(NameState) (init_task_stat_name_source (LitMap "uC/OS-II Stat")) ->
  task_create_continuation_input environment critical saved_local sg call mask before ** GlobalStrings LitMap |--
  task_create_continuation_input environment critical saved_local sg call mask
    (init_task_stat_name_initial before key (LitMap "uC/OS-II Stat")) **
  GlobalStrings_missing LitMap ["uC/OS-II Stat"].
Proof.
  intros environment critical saved_local sg call mask before key LitMap Hfresh Hdis.
  change (task_tcb_init_continuation_save_input environment critical saved_local sg call mask before **
    GlobalStrings LitMap |-- task_tcb_init_continuation_save_input environment critical saved_local sg call mask
      (init_task_stat_name_initial before key (LitMap "uC/OS-II Stat")) **
      GlobalStrings_missing LitMap ["uC/OS-II Stat"]).
  rewrite !task_tcb_init_modular_save_input_world.
  unfold kernel_continuation_call_closed, kernel_continuation_inv, UCOS2_inv; Intros.
  assert (Hvalid : UCOS2_state_inv sg before) by tauto.
  pose proof (init_task_stat_register_name_preserves_state_inv sg before key
    (LitMap "uC/OS-II Stat") Hvalid Hfresh Hdis) as Hafter.
  sep_apply_l_atomic (GlobalStrings_split LitMap "uC/OS-II Stat").
  sep_apply_l_atomic (init_task_stat_register_name_raw_rep sg before key (LitMap "uC/OS-II Stat") Hdis).
  unfold init_task_stat_name_initial; entailer!.
Qed.

Lemma init_task_stat_default_name_continuation_producer :
  forall environment critical saved_local sg call mask before key LitMap,
  before.(NameState).(nameSources) key = None ->
  name_source_disjoint before.(NameState) (name_question_mark_source (LitMap "?")) ->
  task_create_continuation_input environment critical saved_local sg call mask before **
    GlobalStrings_missing LitMap ["uC/OS-II Stat"] |--
  task_create_continuation_input environment critical saved_local sg call mask
    (task_create_name_initial before key (LitMap "?")) **
    GlobalStrings_missing LitMap ["?"; "uC/OS-II Stat"].
Proof.
  intros environment critical saved_local sg call mask before key LitMap Hfresh Hdis.
  change (task_tcb_init_continuation_save_input environment critical saved_local sg call mask before **
    GlobalStrings_missing LitMap ["uC/OS-II Stat"] |--
    task_tcb_init_continuation_save_input environment critical saved_local sg call mask
      (task_create_name_initial before key (LitMap "?")) **
      GlobalStrings_missing LitMap ["?"; "uC/OS-II Stat"]).
  rewrite !task_tcb_init_modular_save_input_world.
  unfold kernel_continuation_call_closed, kernel_continuation_inv, UCOS2_inv; Intros.
  assert (Hvalid : UCOS2_state_inv sg before) by tauto.
  pose proof (task_create_register_default_name_preserves_state_inv sg before key
    (LitMap "?") Hvalid Hfresh Hdis) as Hafter.
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap ["uC/OS-II Stat"] "?" ltac:(cbn; intuition discriminate)).
  sep_apply_l_atomic (task_create_register_default_name_raw_rep sg before key (LitMap "?") Hdis).
  unfold task_create_name_initial; entailer!.
Qed.

Definition init_task_stat_registered_initial before stat_key default_key LitMap :=
  task_create_name_initial
    (init_task_stat_name_initial before stat_key (LitMap "uC/OS-II Stat")) default_key (LitMap "?").

(** Both static sources are transferred once.  The alternative reuses a
    previously registered world and its exact remaining pool.  Source keys
    describe the loader ownership, not an additional C/API argument. *)
Definition init_task_stat_name_input environment critical saved_local sg call mask
  (LitMap : string -> Z) (literals : list string) initial : Assertion :=
  (EX before stat_key default_key,
    coq_prop (initial = init_task_stat_registered_initial before stat_key default_key LitMap /\
      before.(NameState).(nameSources) stat_key = None /\
      name_source_disjoint before.(NameState) (init_task_stat_name_source (LitMap "uC/OS-II Stat")) /\
      (init_task_stat_name_initial before stat_key (LitMap "uC/OS-II Stat")).(NameState).(nameSources) default_key = None /\
      name_source_disjoint (init_task_stat_name_initial before stat_key (LitMap "uC/OS-II Stat")).(NameState)
        (name_question_mark_source (LitMap "?")) /\ literals = ["?"; "uC/OS-II Stat"]) &&
    (task_create_continuation_input environment critical saved_local sg call mask before ** GlobalStrings LitMap)) ||
  (coq_prop (task_create_name_registered (LitMap "?") initial /\
     readable_name initial.(NameState) (LitMap "uC/OS-II Stat") init_task_stat_name_chars) &&
    (task_create_continuation_input environment critical saved_local sg call mask initial **
      GlobalStrings_missing LitMap literals)).

Lemma init_task_stat_name_input_open :
  forall environment critical saved_local sg call mask LitMap literals initial,
  init_task_stat_name_input environment critical saved_local sg call mask LitMap literals initial |--
  coq_prop (task_create_name_registered (LitMap "?") initial /\
    readable_name initial.(NameState) (LitMap "uC/OS-II Stat") init_task_stat_name_chars) &&
  (task_create_continuation_input environment critical saved_local sg call mask initial **
    GlobalStrings_missing LitMap literals).
Proof.
  intros; unfold init_task_stat_name_input; apply derivable1_orp_elim.
  - Intros before stat_key default_key.
    assert (Hinitial : initial = init_task_stat_registered_initial before stat_key default_key LitMap) by tauto.
    assert (Htfresh : before.(NameState).(nameSources) stat_key = None) by tauto.
    assert (Htdis : name_source_disjoint before.(NameState)
      (init_task_stat_name_source (LitMap "uC/OS-II Stat"))) by tauto.
    assert (Hdfresh : (init_task_stat_name_initial before stat_key (LitMap "uC/OS-II Stat")).(NameState).(nameSources) default_key = None) by tauto.
    assert (Hddis : name_source_disjoint
      (init_task_stat_name_initial before stat_key (LitMap "uC/OS-II Stat")).(NameState)
      (name_question_mark_source (LitMap "?"))) by tauto.
    assert (Hlits : literals = ["?"; "uC/OS-II Stat"]) by tauto.
    subst initial literals.
    sep_apply_l_atomic (init_task_stat_name_continuation_producer environment critical saved_local sg call mask
      before stat_key LitMap Htfresh Htdis).
    sep_apply_l_atomic (init_task_stat_default_name_continuation_producer environment critical saved_local sg call mask
      (init_task_stat_name_initial before stat_key (LitMap "uC/OS-II Stat")) default_key LitMap Hdfresh Hddis).
    assert (Hregistered : task_create_name_registered (LitMap "?")
      (init_task_stat_registered_initial before stat_key default_key LitMap))
      by apply task_create_name_initial_registered.
    assert (Hread : readable_name
      (init_task_stat_registered_initial before stat_key default_key LitMap).(NameState)
      (LitMap "uC/OS-II Stat") init_task_stat_name_chars).
    { apply task_create_register_default_name_preserves_readable; [exact Hddis|].
      apply init_task_stat_register_name_readable. }
    unfold init_task_stat_registered_initial; entailer!.
  - Intros; entailer!.
Qed.

Definition init_task_stat_after_lower entry base lower old_frame upper :=
  task_create_ext_after_lower (init_task_stat_create_args entry base) lower old_frame upper
    [] (lower ++ old_frame ++ upper) [].
Definition init_task_stat_empty_stack : list (option Z) := [].
Definition init_task_stat_name_call_residual platform critical sg invocation origin mask state name : Assertion :=
  store_stringLit name "uC/OS-II Stat" -*
    task_name_set_closed platform critical sg invocation origin mask state.

Lemma init_task_stat_name_closed_rep : forall platform critical sg invocation origin mask state,
  task_name_set_closed platform critical sg invocation origin mask state --||--
    interrupt_platform_running platform invocation origin mask **
    store_name_bytes state.(NameState) ** UCOS2_raw_rep_missing_names sg state.
Proof.
  intros; unfold task_name_set_closed, critical_region_outside.
  rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
  rewrite (UCOS2_raw_rep_split_module sg state NamesModule).
  change (interrupt_platform_running platform invocation origin mask **
    (UCOS2_module_rep sg state NamesModule ** UCOS2_raw_rep_missing_module sg state NamesModule) --||--
    interrupt_platform_running platform invocation origin mask **
    UCOS2_module_rep sg state NamesModule ** UCOS2_raw_rep_missing_module sg state NamesModule).
  split; entailer!.
Qed.

Lemma init_task_stat_name_call_split_literal : forall platform critical sg invocation origin mask state name,
  readable_name state.(NameState) name init_task_stat_name_chars ->
  task_name_set_closed platform critical sg invocation origin mask state |--
    store_stringLit name "uC/OS-II Stat" **
    init_task_stat_name_call_residual platform critical sg invocation origin mask state name.
Proof.
  intros platform critical sg invocation origin mask state name Hread.
  pose proof (init_task_stat_name_bytes_split_literal state.(NameState) name Hread) as Hslice.
  assert (Hresidual : interrupt_platform_running platform invocation origin mask **
    init_task_stat_name_remainder state.(NameState).(nameBytes) (init_task_stat_name_domain name) **
    UCOS2_raw_rep_missing_names sg state |--
    init_task_stat_name_call_residual platform critical sg invocation origin mask state name).
  { unfold init_task_stat_name_call_residual.
    apply (proj1 (derivable1s_wand_sepcon_adjoint _ _ _)).
    rewrite init_task_stat_name_closed_rep, Hslice; entailer!. }
  rewrite init_task_stat_name_closed_rep.
  sep_apply_l_atomic (proj1 Hslice).
  sep_apply_l_atomic Hresidual; entailer!.
Qed.

Lemma init_task_stat_name_call_merge_literal : forall platform critical sg invocation origin mask state name,
  store_stringLit name "uC/OS-II Stat" **
    init_task_stat_name_call_residual platform critical sg invocation origin mask state name |--
  task_name_set_closed platform critical sg invocation origin mask state.
Proof. intros; apply derivable1_wand_elim2. Qed.
Definition init_task_stat_after_upper entry base lower old_frame upper :=
  task_create_ext_after_upper (init_task_stat_create_args entry base) lower old_frame upper
    [] (lower ++ old_frame ++ upper) [].
Definition init_task_stat_create_program environment critical sg entry base task_return
  lower old_frame upper call mask LitMap :=
  task_create_program environment critical sg (init_task_stat_stack_region base)
    (init_task_stat_create_args entry base) task_return
    (init_task_stat_after_lower entry base lower old_frame upper)
    (init_task_stat_after_upper entry base lower old_frame upper) (LitMap "?") call mask.
Definition init_task_stat_sequence environment critical sg entry base task_return
  lower old_frame upper call mask LitMap :=
  init_task_stat_program environment critical sg entry base task_return
    (init_task_stat_after_lower entry base lower old_frame upper)
    (init_task_stat_after_upper entry base lower old_frame upper) (LitMap "?") call mask (LitMap "uC/OS-II Stat").
Definition init_task_stat_safe environment critical sg entry base task_return
  lower old_frame upper call mask LitMap before (X : unit -> UCOS2_Verify_State -> Prop) :=
  safeExec (eq before)
    (init_task_stat_sequence environment critical sg entry base task_return
      lower old_frame upper call mask LitMap) X.
Definition init_task_stat_name_continuation (X : unit -> UCOS2_Verify_State -> Prop)
  : Z -> UCOS2_Verify_State -> Prop := fun _ current => X tt current.
Definition init_task_stat_create_postcondition environment critical sg entry base task_return
  lower old_frame upper call mask LitMap before (X : unit -> UCOS2_Verify_State -> Prop)
  : Z -> UCOS2_Verify_State -> Prop := fun error current =>
  init_task_stat_create_program environment critical sg entry base task_return lower old_frame upper call mask LitMap
    before error current /\
  init_task_stat_boot_frame before current /\
  readable_name current.(NameState) (LitMap "uC/OS-II Stat") init_task_stat_name_chars /\
  task_name_set_safe critical sg call.(os_sched_call_invocation) 62 (LitMap "uC/OS-II Stat") current
    (init_task_stat_name_continuation X).

Lemma init_task_stat_safe_create : forall environment critical sg entry base task_return
  lower old_frame upper call mask LitMap before X,
  before.(SchedState).(isRunning) = false ->
  readable_name before.(NameState) (LitMap "uC/OS-II Stat") init_task_stat_name_chars ->
  init_task_stat_safe environment critical sg entry base task_return lower old_frame upper call mask LitMap before X ->
  task_create_safe before
    (init_task_stat_create_program environment critical sg entry base task_return lower old_frame upper call mask LitMap)
    (init_task_stat_create_postcondition environment critical sg entry base task_return lower old_frame upper call mask LitMap before X).
Proof.
  intros environment critical sg entry base task_return lower old_frame upper call mask LitMap before X Hstop Hread Hsafe.
  apply init_task_stat_safe_composition in Hsafe.
  destruct Hsafe as [start [Hstart Hsafe]]; subst start.
  exists before; split; [reflexivity|].
  intros error current Hcreate.
  pose proof (init_task_stat_create_preserves_boot environment critical sg (init_task_stat_stack_region base)
    (init_task_stat_create_args entry base) task_return
    (init_task_stat_after_lower entry base lower old_frame upper)
    (init_task_stat_after_upper entry base lower old_frame upper) (LitMap "?") call mask
    before error current Hstop Hcreate) as Hframe.
  split; [exact Hcreate|]; split; [exact Hframe|]; split.
  - rewrite <- (proj2 Hframe); exact Hread.
  - exact (Hsafe error current Hcreate).
Qed.

Definition init_task_stat_entry environment critical saved_local sg entry base task_return
  lower old_frame upper call mask LitMap literals initial : Assertion :=
  coq_prop (task_invocation_active initial.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
    task_create_stack_no_reservation initial call.(os_sched_call_invocation) /\
    valid_task_stack_region (init_task_stat_stack_region base) /\
    Zlength lower = init_task_stat_frame_first base /\ Zlength old_frame = 16 /\
    Zlength upper = 112 - init_task_stat_frame_first base /\
    0 <= entry < 4294967296 /\ 0 <= task_return < 4294967296) &&
  (init_task_stat_name_input environment critical saved_local sg call mask LitMap literals initial **
    task_stack_storage (init_task_stat_stack_region base) (lower ++ old_frame ++ upper) ** unmap_table_rep sg).

Lemma init_task_stat_entry_open : forall environment critical saved_local sg entry base task_return
  lower old_frame upper call mask LitMap literals initial,
  init_task_stat_entry environment critical saved_local sg entry base task_return lower old_frame upper call mask LitMap literals initial |--
  coq_prop (readable_name initial.(NameState) (LitMap "uC/OS-II Stat") init_task_stat_name_chars /\
    0 < base /\ base + 512 <= 4294967295 /\
    task_create_ext_clear_binding (init_task_stat_stack_region base) (init_task_stat_create_args entry base)
      (lower ++ old_frame ++ upper) [] (lower ++ old_frame ++ upper) []) &&
  task_create_name_api_pre environment critical saved_local sg (init_task_stat_stack_region base)
    (init_task_stat_create_args entry base) task_return lower old_frame upper call mask initial LitMap literals.
Proof.
  intros; unfold init_task_stat_entry; Intros.
  assert (Hregion : valid_task_stack_region (init_task_stat_stack_region base)) by tauto.
  assert (Hbuffer : task_create_stack_buffer_domain (init_task_stat_stack_region base)
    (init_task_stat_create_args entry base) task_return lower old_frame upper).
  { apply init_task_stat_stack_buffer_domain; tauto. }
  assert (Hlength : Zlength (lower ++ old_frame ++ upper) = 128).
  { rewrite !Zlength_app; lia. }
  pose proof (init_task_stat_clear_binding entry base lower old_frame upper Hlength) as Hclear.
  pose proof (init_task_stat_stack_bounds base Hregion) as Hbounds.
  sep_apply_l_atomic (init_task_stat_name_input_open environment critical saved_local sg call mask LitMap literals initial); Intros.
  unfold task_create_name_api_pre.
  assert (Hworld : task_create_continuation_input environment critical saved_local sg call mask initial **
    GlobalStrings_missing LitMap literals |--
    task_create_name_world_input environment critical saved_local sg call mask LitMap literals initial).
  { unfold task_create_name_world_input; Right; entailer!; tauto. }
  entailer!; sep_apply_r_atomic Hworld; entailer!; tauto.
Qed.

Definition init_task_stat_create_residual environment saved_local sg entry base task_return
  lower old_frame upper call state error : Assertion :=
  init_task_stat_continuation_residual environment saved_local call state ** unmap_table_rep sg **
  (if Z.eq_dec error 0 then emp else
    task_stack_storage (init_task_stat_stack_region base)
      (if Z.eq_dec error 66 then task_create_stack_image TaskStackNoVFP
        (init_task_stat_create_args entry base) task_return
        (init_task_stat_after_lower entry base lower old_frame upper)
        (init_task_stat_after_upper entry base lower old_frame upper)
       else lower ++ old_frame ++ upper)).

Definition init_task_stat_created environment critical sg entry base task_return lower old_frame upper
  original mask LitMap initial X returned current error : Prop :=
  task_tcb_init_stack_same_call returned original /\ UCOS2_state_inv sg current /\
  (error = 0 \/ error = 40 \/ error = 60 \/ error = 66) /\
  init_task_stat_create_postcondition environment critical sg entry base task_return lower old_frame upper
    original mask LitMap initial X error current.

Lemma init_task_stat_create_post_open : forall environment critical saved_local sg entry base task_return
  lower old_frame upper original mask LitMap literals initial X error,
  task_create_ext_api_post environment critical saved_local sg (init_task_stat_stack_region base)
    (init_task_stat_create_args entry base) task_return lower old_frame upper [] (lower ++ old_frame ++ upper) []
    original mask error
    (init_task_stat_create_postcondition environment critical sg entry base task_return lower old_frame upper original mask LitMap initial X) **
    GlobalStrings_missing LitMap literals |--
  EX returned current,
    coq_prop (init_task_stat_created environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial X returned current error /\
      task_name_set_admission critical sg returned.(os_sched_call_invocation) 62 (LitMap "uC/OS-II Stat") current /\
      task_name_set_safe critical sg returned.(os_sched_call_invocation) 62 (LitMap "uC/OS-II Stat") current
        (init_task_stat_name_continuation X)) &&
    (task_name_set_closed environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) mask current **
     init_task_stat_create_residual environment saved_local sg entry base task_return lower old_frame upper
       returned current error ** GlobalStrings_missing LitMap literals).
Proof.
  intros; unfold task_create_ext_api_post; Intros returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  assert (Hsafe : task_create_safe current (StateRelMonad.ret error)
    (init_task_stat_create_postcondition environment critical sg entry base task_return lower old_frame upper original mask LitMap initial X)) by tauto.
  destruct Hsafe as [start [Hstart Hsafe]]; subst start.
  specialize (Hsafe error current (conj eq_refl eq_refl)).
  assert (Hcodes : error = 0 \/ error = 40 \/ error = 60 \/ error = 66).
  { assert (Hex : error = 42 -> 63 < (init_task_stat_create_args entry base).(createPriority)) by tauto.
    cbn in Hex; tauto || lia. }
  assert (Hinvocation : returned.(os_sched_call_invocation) = original.(os_sched_call_invocation))
    by (unfold task_tcb_init_stack_same_call in Hsame; tauto).
  assert (Hadmit : task_name_set_admission critical sg returned.(os_sched_call_invocation) 62
    (LitMap "uC/OS-II Stat") current).
  { eapply init_task_stat_name_admission; exact (proj1 (proj2 (proj2 Hsafe))). }
  assert (Hname : task_name_set_safe critical sg returned.(os_sched_call_invocation) 62
    (LitMap "uC/OS-II Stat") current (init_task_stat_name_continuation X)).
  { rewrite Hinvocation; exact (proj2 (proj2 (proj2 Hsafe))). }
  sep_apply_l_atomic (proj1 (init_task_stat_name_call_resource_equiv environment critical saved_local sg returned mask current)); Intros.
  Exists returned current; unfold init_task_stat_created, init_task_stat_create_residual,
    init_task_stat_after_lower, init_task_stat_after_upper; entailer!; tauto.
Qed.

Definition init_task_stat_post environment critical saved_local sg entry base task_return
  lower old_frame upper original mask LitMap literals initial (X : unit -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned middle create_error current name_error,
    coq_prop (safeExec (eq current) (StateRelMonad.ret tt) X) &&
    (coq_prop (init_task_stat_created environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial X returned middle create_error) **
     coq_prop (task_name_set_post critical sg returned.(os_sched_call_invocation) 62 (LitMap "uC/OS-II Stat")
        middle name_error current (init_task_stat_name_continuation X)) **
     task_name_set_closed environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) mask current **
     init_task_stat_create_residual environment saved_local sg entry base task_return lower old_frame upper
       returned middle create_error ** GlobalStrings_missing LitMap literals).

Lemma init_task_stat_name_post_safe_return : forall critical sg invocation name before error current X,
  task_name_set_post critical sg invocation 62 name before error current (init_task_stat_name_continuation X) ->
  safeExec (eq current) (StateRelMonad.ret tt) X.
Proof.
  intros critical sg invocation name before error current X [_ [start [Hstart Hsafe]]].
  subst start; exists current; split; [reflexivity|].
  intros result final [Hresult Hfinal]; subst result final.
  exact (Hsafe error current (conj eq_refl eq_refl)).
Qed.

(** Internal OSInit composition obligation: the caller must establish the actual
    boot call/continuation world, the OSTaskStatStk ownership and symbol/ABI
    bindings, and either the fresh static-literal pool or its registered view.
    The fresh branch above proves the literal transfer, not whole OSInit/loader
    initialization. No timer initialization, task execution or calibration
    receipt is asserted. The post keeps CreateExt's residual at [middle] and
    the NameSet closed world at its actual [current]. *)
