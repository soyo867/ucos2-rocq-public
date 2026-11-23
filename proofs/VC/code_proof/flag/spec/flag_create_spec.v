(** OSFlagCreate source-order safeExec semantics and resource transformations.
    Generated witness statements and proofs are deliberately not imported. *)
Require Export Ucos2Verify.VC.code.flag.spec.flag_query_spec.
Require Export Ucos2Verify.VC.code.mbox.spec.mbox_accept_spec.
Require Export Ucos2Verify.lib.kernel_literal_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.cross_module_invariants.

Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic MapLib StoreAux.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import ListNotations UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Static address/layout interpretation for the selected original headers.
    These conditions describe the linked objects, not restrictions on flags. *)
Definition flag_create_layout (sg : StableGlobVars) (interrupt_addr free_addr : addr) : Prop :=
  interrupt_addr = sg.(g_OSIntNesting) /\ free_addr = sg.(g_OSFlagFreeList) /\
  0 < sg.(g_OSFlagTbl) /\ sg.(osKernelConfig).(cfgFlagBits) = 16 /\
  sg.(osKernelConfig).(cfgFlagNames) = true /\
  (forall p, (&(p # "os_flag_grp" ->ₛ "OSFlagType")) = p) /\
  (forall p, (&(p # "os_flag_grp" ->ₛ "OSFlagWaitList")) = p + 4) /\
  (forall p, (&(p # "os_flag_grp" ->ₛ "OSFlagFlags")) = p + 8) /\
  (forall p, (&(p # "os_flag_grp" ->ₛ "OSFlagName")) = p + 12).

Definition flag_create_depth (s : UCOS2_Verify_State) : Z := s.(IntrState).(intNesting).
Definition flag_create_free_head (sg : StableGlobVars) (s : UCOS2_Verify_State) : addr :=
  match s.(FlagState).(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.
Definition flag_create_error (s : UCOS2_Verify_State) : Z :=
  match s.(FlagState).(flagFree) with [] => 114 | _ :: _ => 0 end.
Definition flag_create_checkpoint (s : UCOS2_Verify_State) (bits name : Z) : UCOS2_Verify_State :=
  match flag_allocate s.(FlagState) bits name with
  | None => s
  | Some (_, flags) => replace_FlagS flags s
  end.

(** The registered static source and the same two bytes are required only
    for an actual nonempty acquisition. ISR and exhausted acquisitions do
    not need a new object or a name source. No post-invariant is a guard. *)
Definition flag_create_default_name (s : UCOS2_Verify_State) (name : addr) : Prop :=
  s.(NameState).(nameBytes) name = Some 63 /\
  s.(NameState).(nameBytes) (name + 1) = Some 0.
Definition flag_create_name_admission (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before : UCOS2_Verify_State) (name : addr) : Prop :=
  forall entry, flag_create_depth before <= 0 ->
    critical_region_interval critical sg invocation before entry ->
    entry.(FlagState).(flagFree) <> [] -> flag_create_default_name entry name.

(** The conditional API premise is supplied by the existing registered
    static source and the selected client-family NameState frame.  It does
    not attribute byte stability to the CPU Save/Restore implementation. *)
Lemma flag_create_name_admission_registered : forall critical sg invocation before name,
  flag_create_default_name before name ->
  flag_create_name_admission critical sg invocation before name.
Proof.
  intros critical sg invocation before name Hname entry Hdepth Hinterval Hnonempty.
  unfold flag_create_default_name in *.
  rewrite <- (critical_region_interval_preserves_name_state
    critical sg invocation before entry Hinterval); exact Hname.
Qed.

Lemma flag_create_name_admission_isr : forall critical sg invocation before name,
  0 < flag_create_depth before ->
  flag_create_name_admission critical sg invocation before name.
Proof. intros critical sg invocation before name Hdepth entry Hnot; lia. Qed.

Lemma flag_create_default_name_registered_source : forall before name,
  before.(NameState) = name_question_mark_resources name ->
  flag_create_default_name before name.
Proof.
  intros before name Hsource; unfold flag_create_default_name; rewrite Hsource.
  repeat rewrite name_question_mark_resources_lookup; unfold name_question_mark_bytes.
  destruct (Z.eq_dec name name), (Z.eq_dec (name + 1) name),
    (Z.eq_dec (name + 1) (name + 1)); split; congruence || lia.
Qed.

Lemma flag_create_default_name_readable : forall s name,
  flag_create_default_name s name -> readable_name s.(NameState) name [63].
Proof.
  intros s name [Hchar Hnul]; unfold readable_name; split.
  - repeat constructor; lia.
  - split; [|exact Hnul]. intros [|i] c H; cbn in H.
    + injection H as <-; rewrite Z.add_0_r; exact Hchar.
    + destruct i; discriminate.
Qed.

Definition flag_create_protected (sg : StableGlobVars) (bits name : Z)
  : program UCOS2_Verify_State (Z * Z) :=
  fun entry result checkpoint =>
    result = (flag_create_free_head sg entry, flag_create_error entry) /\
    checkpoint = flag_create_checkpoint entry bits name.

(** Ordered source semantics: OSIntNesting is observed before Save; the
    free head is observed at acquisition. Restore advances the written
    checkpoint, and the result retains the allocated address, not a claim
    that the same generation survives subsequent environment steps. *)
Definition flag_create_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (bits name : Z)
  : program UCOS2_Verify_State (Z * Z) :=
  StateRelMonad.bind (get' flag_create_depth) (fun nesting =>
    if Z.ltb 0 nesting then StateRelMonad.ret (0, 16) else
    StateRelMonad.bind (update (critical_region_interval critical sg invocation)) (fun _ =>
      StateRelMonad.bind (flag_create_protected sg bits name) (fun result =>
        StateRelMonad.bind (update (critical_region_interval critical sg invocation)) (fun _ =>
          StateRelMonad.ret result)))).

Definition flag_create_safe critical sg invocation bits name before
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (flag_create_program critical sg invocation bits name)
    (fun result current => X (fst result) (snd result) current).

Lemma flag_create_program_isr : forall critical sg invocation bits name before,
  0 < flag_create_depth before ->
  flag_create_program critical sg invocation bits name before (0, 16) before.
Proof.
  intros critical sg invocation bits name before Hdepth; unfold flag_create_program.
  exists (flag_create_depth before), before; split; [split; reflexivity|].
  rewrite (proj2 (Z.ltb_lt _ _) Hdepth); split; reflexivity.
Qed.

Lemma flag_create_program_restored : forall critical sg invocation bits name before entry current,
  flag_create_depth before <= 0 ->
  critical_region_interval critical sg invocation before entry ->
  critical_region_interval critical sg invocation (flag_create_checkpoint entry bits name) current ->
  flag_create_program critical sg invocation bits name before
    (flag_create_free_head sg entry, flag_create_error entry) current.
Proof.
  intros critical sg invocation bits name before entry current Hdepth Hentry Hcurrent.
  unfold flag_create_program.
  exists (flag_create_depth before), before; split; [split; reflexivity|].
  rewrite (proj2 (Z.ltb_ge _ _) Hdepth).
  exists tt, entry; split; [exact Hentry|].
  exists (flag_create_free_head sg entry, flag_create_error entry),
    (flag_create_checkpoint entry bits name); split; [split; reflexivity|].
  exists tt, current; split; [exact Hcurrent|]; split; reflexivity.
Qed.

Lemma flag_create_program_has_result : forall critical sg invocation bits name before,
  exists result current, flag_create_program critical sg invocation bits name before result current.
Proof.
  intros; destruct (Z_lt_ge_dec 0 (flag_create_depth before)).
  - exists (0, 16), before; apply flag_create_program_isr; assumption.
  - exists (flag_create_free_head sg before, flag_create_error before),
      (flag_create_checkpoint before bits name).
    apply flag_create_program_restored with (entry := before); try lia; constructor.
Qed.

Lemma flag_create_safe_return : forall critical sg invocation bits name before current pointer error X,
  flag_create_program critical sg invocation bits name before (pointer, error) current ->
  flag_create_safe critical sg invocation bits name before X ->
  safeExec (eq current) (StateRelMonad.ret (pointer, error))
    (fun result state => X (fst result) (snd result) state).
Proof.
  intros critical sg invocation bits name before current pointer error X Hprogram Hsafe.
  unfold flag_create_safe in Hsafe.
  eapply (highstependret_derive (flag_create_program critical sg invocation bits name)
    (eq before) (pointer, error) (fun _ => eq current)); [|exact Hsafe].
  intros state ->; exists current; split; assumption || reflexivity.
Qed.

Definition flag_create_api_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask bits name perr : Z)
  (before : UCOS2_Verify_State) (pointer : Z)
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX error current,
    coq_prop (flag_create_program critical sg invocation bits name before (pointer, error) current /\
      safeExec (eq current) (StateRelMonad.ret (pointer, error))
        (fun result state => X (fst result) (snd result) state)) &&
    (perr # UChar |-> error ** mutex_query_closed platform critical sg invocation origin mask current).

Definition flag_create_interrupt_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (s : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg s) &&
  (interrupt_platform_running platform invocation origin mask **
   interrupt_inv_no_int_nesting sg s.(IntrState) ** UCOS2_raw_rep_missing_interrupt sg s).

Lemma flag_create_interrupt_split : forall platform critical sg invocation origin mask s,
  mutex_query_closed platform critical sg invocation origin mask s |--
    sg.(g_OSIntNesting) # UChar |-> flag_create_depth s **
    flag_create_interrupt_frame platform critical sg invocation origin mask s.
Proof.
  intros; rewrite mutex_query_closed_equiv, UCOS2_inv_split_interrupt.
  unfold flag_create_interrupt_frame, flag_create_depth, interrupt_inv,
    interrupt_inv_no_int_nesting, store_int_state; entailer!.
Qed.

Lemma flag_create_interrupt_merge : forall platform critical sg invocation origin mask s,
  sg.(g_OSIntNesting) # UChar |-> flag_create_depth s **
    flag_create_interrupt_frame platform critical sg invocation origin mask s |--
  mutex_query_closed platform critical sg invocation origin mask s.
Proof.
  intros; rewrite mutex_query_closed_equiv, UCOS2_inv_split_interrupt.
  unfold flag_create_interrupt_frame, flag_create_depth, interrupt_inv,
    interrupt_inv_no_int_nesting, store_int_state; entailer!.
Qed.

Definition flag_create_pool_frame (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg s) &&
    (flag_groups_rep sg s.(FlagState) ** flag_nodes_rep sg s.(FlagState) **
     UCOS2_raw_rep_missing_flag sg s).

Lemma flag_create_pool_split : forall sg s,
  UCOS2_inv sg s |-- sg.(g_OSFlagFreeList) # Ptr |-> flag_create_free_head sg s **
    flag_create_pool_frame sg s.
Proof.
  intros; rewrite UCOS2_inv_split_flag; Intros.
  match goal with H : UCOS2_state_inv sg s |- _ =>
    destruct (flag_query_state_configuration sg s H) as [Henabled _] end.
  unfold flag_configured_rep; rewrite Henabled.
  unfold flag_raw_rep, flag_create_free_head, flag_create_pool_frame; entailer!.
Qed.

Lemma flag_create_pool_merge : forall sg s,
  sg.(g_OSFlagFreeList) # Ptr |-> flag_create_free_head sg s **
    flag_create_pool_frame sg s |-- UCOS2_inv sg s.
Proof.
  intros; unfold flag_create_pool_frame; Intros.
  match goal with H : UCOS2_state_inv sg s |- _ =>
    destruct (flag_query_state_configuration sg s H) as [Henabled _] end.
  rewrite UCOS2_inv_split_flag; unfold flag_configured_rep; rewrite Henabled.
  unfold flag_raw_rep, flag_create_free_head; entailer!.
Qed.

Definition flag_create_slot (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (id : Z) (rest : list Z) (old : FlagGroupImage) : Prop :=
  s.(FlagState).(flagFree) = id :: rest /\
  s.(FlagState).(flagImages) id = Some old /\
  s.(FlagState).(flagUsed) id = None /\
  old.(flagImageType) = 0 /\
  old.(flagImageHead) = match rest with [] => 0 | j :: _ => flag_pool_addr sg j end /\
  0 <= id < sg.(osKernelConfig).(cfgMaxFlags).

Lemma flag_create_nonempty_slot : forall sg s,
  UCOS2_state_inv sg s -> s.(FlagState).(flagFree) <> [] ->
  exists id rest old, flag_create_slot sg s id rest old.
Proof.
  intros sg s Hvalid Hnonempty.
  destruct (flag_query_state_configuration sg s Hvalid) as [_ [_ Hflag]].
  destruct Hflag as [Hpool [_ [_ [_ [Hfree _]]]]].
  destruct (flagFree (FlagState s)) as [|id rest] eqn:Hlist; [contradiction|].
  destruct (Hfree [] id rest eq_refl) as [old [Himage [Htype Hnext]]].
  destruct Hpool as [Hnd [Hrange Hpartition]].
  assert (Hid : 0 <= id < cfgMaxFlags (osKernelConfig sg)) by (apply Hrange; simpl; auto).
  assert (Hunused : flagUsed (FlagState s) id = None).
  { destruct (flagUsed (FlagState s) id) as [g|] eqn:Hg; [|reflexivity].
    destruct (proj1 (Hpartition id) (ex_intro _ g Hg)) as [_ Hnot].
    exfalso; apply Hnot; simpl; auto. }
  exists id, rest, old; unfold flag_create_slot; repeat split; try assumption; lia.
Qed.

Lemma flag_create_allocate_nodes : forall s bits name id flags,
  flag_allocate s bits name = Some (id, flags) -> flags.(flagWaitNodes) = s.(flagWaitNodes).
Proof.
  intros s bits name id flags H; unfold flag_allocate in H.
  destruct (flagFree s) as [|head tail]; [discriminate|].
  destruct (flagImages s head); [|discriminate].
  inversion H; reflexivity.
Qed.

Lemma flag_create_allocate_names : forall sg s bits name id flags,
  flag_allocate s.(FlagState) bits name = Some (id, flags) ->
  forall p, kernel_name_root sg (replace_FlagS flags s) p ->
    kernel_name_root sg s p \/ p = name.
Proof.
  intros sg s bits name id flags Hstep p Hroot.
  unfold flag_allocate in Hstep; destruct (flagFree (FlagState s)) as [|head tail]; [discriminate|].
  destruct (flagImages (FlagState s) head); [|discriminate].
  inversion Hstep; subst flags id; clear Hstep.
  unfold kernel_name_root in *; cbn [replace_FlagS] in Hroot.
  destruct Hroot as [Ht|[He|[Hf|[Hm|Htimer]]]];
    try (left; tauto).
  destruct Hf as [Hen [Hnamed [other [group [Hget Hp]]]]].
  cbn in Hget; unfold kernel_map_set in Hget.
  destruct (Z.eq_dec other head).
  - inversion Hget; subst group; right; exact Hp.
  - left; right; right; left; split; [exact Hen|]. split; [exact Hnamed|].
    exists other, group; auto.
Qed.

Lemma flag_create_allocate_preserves_validity : forall sg s bits name id flags,
  UCOS2_state_inv sg s -> flag_word_in_range sg.(osKernelConfig) bits ->
  flag_create_default_name s name -> flag_allocate s.(FlagState) bits name = Some (id, flags) ->
  UCOS2_state_inv sg (replace_FlagS flags s).
Proof.
  intros sg s bits name id flags Hvalid Hbits Hname Hstep.
  destruct (flag_query_state_configuration sg s Hvalid) as [Henabled [_ Hflags]].
  pose proof (flag_allocate_preserves_state_validity sg s.(FlagState) bits name id flags
    Hflags Hbits Hstep) as Hflags_after.
  assert (Hnames_after : kernel_names_valid sg (replace_FlagS flags s)).
  { eapply kernel_names_valid_add_root with (before := s) (name := name) (chars := [63]).
    - apply UCOS2_state_inv_names_valid; exact Hvalid.
    - apply flag_create_default_name_readable; exact Hname.
    - reflexivity.
    - eapply flag_create_allocate_names; exact Hstep. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *.
  destruct Hvalid as [Hprofile [Htask [Hsched [Hevent [Hcross Hrest]]]]].
  cbn [replace_FlagS].
  split; [exact Hprofile|]. split; [exact Htask|]. split; [exact Hsched|].
  split; [exact Hevent|]. split.
  - apply cross_module_consistency_flag_nodes_frame; [eapply flag_create_allocate_nodes; exact Hstep|exact Hcross].
  - unfold valid_flag_configuration in *; rewrite Henabled in *.
    tauto.
Qed.

Definition flag_create_fields_frame (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (id : Z) (old : FlagGroupImage) : Assertion :=
  coq_prop (UCOS2_state_inv sg s) &&
   (store_optional_bytes (flag_pool_addr sg id + 1) (firstn 3 old.(flagImagePadding)) **
    store_optional_bytes (flag_pool_addr sg id + 10) (skipn 3 old.(flagImagePadding)) **
    flag_groups_without sg s.(FlagState) id ** flag_nodes_rep sg s.(FlagState) **
    UCOS2_raw_rep_missing_flag sg s).

Definition flag_create_literal_frame (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (id : Z) (old : FlagGroupImage) (name : addr) : Assertion :=
  coq_prop (UCOS2_state_inv sg s) &&
   (store_optional_bytes (flag_pool_addr sg id + 1) (firstn 3 old.(flagImagePadding)) **
    store_optional_bytes (flag_pool_addr sg id + 10) (skipn 3 old.(flagImagePadding)) **
    flag_groups_without sg s.(FlagState) id ** flag_nodes_rep sg s.(FlagState) **
    store_name_bytes_without_question_mark s.(NameState) name **
    UCOS2_raw_rep_missing_two sg s FlagModule NamesModule).

Lemma flag_create_literal_split : forall sg s id old name,
  flag_create_default_name s name -> flag_create_fields_frame sg s id old |--
    store_stringLit name "?" ** flag_create_literal_frame sg s id old name.
Proof.
  intros sg s id old name [Hchar Hnul].
  unfold flag_create_fields_frame, flag_create_literal_frame, UCOS2_raw_rep_missing_flag.
  rewrite (UCOS2_raw_rep_missing_module_split_module sg s FlagModule NamesModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  Intros.
  sep_apply_l_atomic (store_name_bytes_split_question_mark s.(NameState) name Hchar Hnul); entailer!.
Qed.

Lemma flag_create_literal_merge : forall sg s id old name,
  flag_create_default_name s name ->
  store_stringLit name "?" ** flag_create_literal_frame sg s id old name |--
    flag_create_fields_frame sg s id old.
Proof.
  intros sg s id old name [Hchar Hnul].
  unfold flag_create_fields_frame, flag_create_literal_frame, UCOS2_raw_rep_missing_flag.
  rewrite (UCOS2_raw_rep_missing_module_split_module sg s FlagModule NamesModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  Intros.
  sep_apply_l_atomic (store_name_bytes_merge_question_mark s.(NameState) name Hchar Hnul); entailer!.
Qed.

Definition flag_create_effect (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (bits name pointer error : Z) (checkpoint : UCOS2_Verify_State) : Prop :=
  pointer = flag_create_free_head sg entry /\ error = flag_create_error entry /\
  checkpoint = flag_create_checkpoint entry bits name.

Lemma flag_create_effect_program : forall critical sg invocation bits name before entry
  checkpoint current pointer error,
  flag_create_depth before <= 0 ->
  critical_region_interval critical sg invocation before entry ->
  flag_create_effect sg entry bits name pointer error checkpoint ->
  critical_region_interval critical sg invocation checkpoint current ->
  flag_create_program critical sg invocation bits name before (pointer, error) current.
Proof.
  intros critical sg invocation bits name before entry checkpoint current pointer error
    Hdepth Hentry [-> [-> ->]] Hcurrent.
  eapply flag_create_program_restored; eassumption.
Qed.

Lemma flag_create_pool_address_nonzero : forall sg interrupt_addr free_addr id,
  flag_create_layout sg interrupt_addr free_addr -> 0 <= id -> flag_pool_addr sg id <> 0.
Proof.
  intros sg interrupt_addr free_addr id [_ [_ [Hbase [Hbits [Hnames _]]]]] Hid.
  unfold flag_pool_addr, flag_group_size, flag_group_name_offset, flag_word_bytes, kernel_align4.
  rewrite Hbits, Hnames; cbn; lia.
Qed.

Lemma flag_create_head_zero : forall sg s interrupt_addr free_addr,
  flag_create_layout sg interrupt_addr free_addr -> UCOS2_state_inv sg s ->
  flag_create_free_head sg s = 0 -> s.(FlagState).(flagFree) = [].
Proof.
  intros sg s interrupt_addr free_addr Hlayout Hvalid Hhead.
  destruct (flag_query_state_configuration sg s Hvalid) as [_ [_ [[_ [Hrange _]] _]]].
  unfold flag_create_free_head in Hhead.
  destruct (flagFree (FlagState s)) as [|id rest] eqn:Hfree; [reflexivity|].
  exfalso; eapply flag_create_pool_address_nonzero; [exact Hlayout| |exact Hhead].
  specialize (Hrange id ltac:(simpl; auto)); lia.
Qed.

Lemma flag_create_slot_head : forall sg s id rest old,
  flag_create_slot sg s id rest old -> flag_create_free_head sg s = flag_pool_addr sg id.
Proof. intros sg s id rest old [Hfree _]; unfold flag_create_free_head; rewrite Hfree; reflexivity. Qed.

Lemma flag_create_slot_allocation : forall sg s id rest old bits name,
  flag_create_slot sg s id rest old ->
  exists flags,
    flag_allocate s.(FlagState) bits name = Some (id, flags) /\
    flags.(flagFree) = rest /\
    flags.(flagImages) id = Some (flag_create_image old bits name) /\
    (forall other, other <> id -> s.(FlagState).(flagImages) other = flags.(flagImages) other) /\
    flags.(flagWaitNodes) = s.(FlagState).(flagWaitNodes).
Proof.
  intros sg s id rest old bits name [Hfree [Himage _]].
  unfold flag_allocate; rewrite Hfree, Himage.
  eexists; split; [reflexivity|]. cbn; split; [reflexivity|].
  split; [apply kernel_map_set_same|]. split; [|reflexivity].
  intros other Hother; symmetry; apply kernel_map_set_other; assumption.
Qed.

Lemma flag_create_fields_split : forall sg s id rest old interrupt_addr free_addr,
  flag_create_layout sg interrupt_addr free_addr -> flag_create_slot sg s id rest old ->
  flag_create_pool_frame sg s |--
    (flag_pool_addr sg id) # UChar |-> 0 **
    (flag_pool_addr sg id + 4) # Ptr |-> old.(flagImageHead) **
    (flag_pool_addr sg id + 8) # UShort |-> old.(flagImageBits) **
    (flag_pool_addr sg id + 12) # Ptr |-> old.(flagImageName) **
    flag_create_fields_frame sg s id old.
Proof.
  intros sg s id rest old interrupt_addr free_addr [_ [_ [_ [Hbits [Hnames _]]]]]
    [_ [Himage [_ [Htype _]]]].
  unfold flag_create_pool_frame; Intros.
  sep_apply_l_atomic (flag_groups_split_group sg s.(FlagState) id old Himage).
  unfold flag_group_rep, flag_create_fields_frame, flag_word_rep, flag_group_name_offset,
    flag_word_bytes, kernel_align4.
  rewrite Hbits, Hnames, Htype; cbn.
  replace (flag_pool_addr sg id + 8 + 2) with (flag_pool_addr sg id + 10) by lia.
  entailer!.
Qed.

Lemma flag_create_fields_fold : forall sg id old bits name,
  sg.(osKernelConfig).(cfgFlagBits) = 16 -> sg.(osKernelConfig).(cfgFlagNames) = true ->
  (flag_pool_addr sg id) # UChar |-> 5 **
  (flag_pool_addr sg id + 4) # Ptr |-> 0 **
  (flag_pool_addr sg id + 8) # UShort |-> bits **
  (flag_pool_addr sg id + 12) # Ptr |-> name **
  store_optional_bytes (flag_pool_addr sg id + 1) (firstn 3 old.(flagImagePadding)) **
  store_optional_bytes (flag_pool_addr sg id + 10) (skipn 3 old.(flagImagePadding)) |--
  flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg id) (flag_create_image old bits name).
Proof.
  intros sg id old bits name Hbits Hnames.
  unfold flag_group_rep, flag_create_image, flag_word_rep, flag_group_name_offset,
    flag_word_bytes, kernel_align4; cbn.
  rewrite Hbits, Hnames; cbn.
  replace (flag_pool_addr sg id + 8 + 2) with (flag_pool_addr sg id + 10) by lia.
  entailer!.
Qed.

Lemma flag_create_fields_merge_updated : forall sg s id rest old bits name interrupt_addr free_addr,
  flag_create_layout sg interrupt_addr free_addr -> flag_create_slot sg s id rest old ->
  0 <= bits <= 65535 -> flag_create_default_name s name ->
  sg.(g_OSFlagFreeList) # Ptr |-> old.(flagImageHead) **
  (flag_pool_addr sg id) # UChar |-> 5 **
  (flag_pool_addr sg id + 4) # Ptr |-> 0 **
  (flag_pool_addr sg id + 8) # UShort |-> bits **
  (flag_pool_addr sg id + 12) # Ptr |-> name ** flag_create_fields_frame sg s id old |--
  coq_prop (UCOS2_state_inv sg (flag_create_checkpoint s bits name) /\
    flag_create_effect sg s bits name (flag_create_free_head sg s) 0 (flag_create_checkpoint s bits name)) &&
  UCOS2_inv sg (flag_create_checkpoint s bits name).
Proof.
  intros sg s id rest old bits name interrupt_addr free_addr Hlayout Hslot Hbits Hname.
  pose proof Hlayout as [_ [_ [_ [Hwidth [Hnames _]]]]].
  destruct (flag_create_slot_allocation sg s id rest old bits name Hslot)
    as [flags [Hallocate [Hfree [Himage [Hother Hnodes]]]]].
  pose proof Hslot as [Hfree_before [_ [_ [_ [Hnext _]]]]].
  assert (Hcheckpoint : flag_create_checkpoint s bits name = replace_FlagS flags s).
  { unfold flag_create_checkpoint; rewrite Hallocate; reflexivity. }
  assert (Hword : flag_word_in_range sg.(osKernelConfig) bits).
  { unfold flag_word_in_range; rewrite Hwidth; cbn; lia. }
  unfold flag_create_fields_frame; Intros.
  match goal with Hvalid : UCOS2_state_inv sg s |- _ =>
    pose proof (flag_create_allocate_preserves_validity sg s bits name id flags Hvalid Hword Hname Hallocate) as Hafter;
    destruct (flag_query_state_configuration sg s Hvalid) as [Henabled _] end.
  sep_apply_l_atomic (flag_create_fields_fold sg id old bits name Hwidth Hnames).
  sep_apply_l_atomic (flag_groups_merge_updated_group sg s.(FlagState) flags id
    (flag_create_image old bits name) Himage Hother).
  assert (Hmodule : sg.(g_OSFlagFreeList) # Ptr |-> old.(flagImageHead) **
    flag_groups_rep sg flags ** flag_nodes_rep sg s.(FlagState) |-- flag_configured_rep sg flags).
  { unfold flag_configured_rep; rewrite Henabled; unfold flag_raw_rep, flag_nodes_rep.
    rewrite Hfree, Hnodes, Hnext; entailer!. }
  sep_apply_l_atomic Hmodule.
  pose proof (UCOS2_inv_merge_updated_flag sg s (replace_FlagS flags s) Hafter eq_refl) as Hmerge.
  change (flag_configured_rep sg flags ** UCOS2_raw_rep_missing_flag sg s |--
    UCOS2_inv sg (replace_FlagS flags s)) in Hmerge.
  sep_apply_l_atomic Hmerge.
  rewrite Hcheckpoint.
  assert (Heffect : flag_create_effect sg s bits name (flag_create_free_head sg s) 0 (replace_FlagS flags s)).
  { unfold flag_create_effect; split; [reflexivity|]. split.
    - unfold flag_create_error; rewrite Hfree_before; reflexivity.
    - symmetry; exact Hcheckpoint. }
  entailer!.
Qed.

Lemma flag_create_empty_effect : forall sg s bits name,
  s.(FlagState).(flagFree) = [] -> flag_create_effect sg s bits name 0 114 s.
Proof.
  intros sg s bits name Hfree; unfold flag_create_effect, flag_create_free_head,
    flag_create_error, flag_create_checkpoint, flag_allocate.
  rewrite Hfree; repeat split; reflexivity.
Qed.
