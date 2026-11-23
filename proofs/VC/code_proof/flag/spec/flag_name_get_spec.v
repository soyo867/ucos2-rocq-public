(** OSFlagNameGet, V2.93.01, selected ARM32 profile.  A raw handle owns
    only the fields actually reached; a pool handle is re-read in the
    acquired state. Names are borrowed from the one existing NameState. *)
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Export Ucos2Verify.VC.code.time.spec.time_get_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_name_get_spec.
Require Export Ucos2Verify.VC.code.core.spec.os_strlen_spec.
Require Export Ucos2Verify.lib.flag.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

Definition flag_name_get_early_error (p pname nesting : Z) : option Z :=
  if Z.eqb p 0 then Some 110 else
  if Z.eqb pname 0 then Some 12 else
  if Z.ltb 0 nesting then Some 17 else None.

Definition flag_name_get_type (v : FlagGroupImage) : Z := v.(flagImageType).
Definition flag_name_get_name (v : FlagGroupImage) : Z := v.(flagImageName).

(** [None] is a separately owned raw object; [Some i] is the actual fixed
    pool slot, including a free slot. The raw image is ignored in pool mode. *)
Definition flag_name_get_selected (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (p : Z) (slot : option Z) (raw image : FlagGroupImage) : Prop :=
  match slot with
  | None => image = raw
  | Some i => p = flag_pool_addr sg i /\ s.(FlagState).(flagImages) i = Some image
  end.

Definition flag_name_get_name_cell (p : Z) (image : FlagGroupImage) : Assertion :=
  if Z.eqb image.(flagImageType) 5 then
    (p + 12) # Ptr |-> image.(flagImageName) else emp.

Definition flag_name_get_fields (p : Z) (image : FlagGroupImage) : Assertion :=
  p # UChar |-> image.(flagImageType) ** flag_name_get_name_cell p image.

Definition flag_name_get_private (p : Z) (slot : option Z)
  (raw : FlagGroupImage) : Assertion :=
  match slot with None => flag_name_get_fields p raw | Some _ => emp end.

Definition flag_name_get_guarded_private (before : UCOS2_Verify_State)
  (p pname : Z) (slot : option Z) (raw : FlagGroupImage) : Assertion :=
  match flag_name_get_early_error p pname (task_name_get_nesting before) with
  | Some _ => emp | None => flag_name_get_private p slot raw
  end.

(** Static C/ABI interpretation, not a runtime success or liveness premise. *)
Definition flag_name_get_addresses (sg : StableGlobVars)
  (p nesting type_addr name_addr : Z) : Prop :=
  sg.(g_OSIntNesting) = nesting /\ type_addr = p /\ name_addr = p + 12 /\
  sg.(osKernelConfig).(cfgFlagEnabled) = true /\
  sg.(osKernelConfig).(cfgFlagNames) = true /\
  flag_group_name_offset sg.(osKernelConfig) = 12.

(** This is the guarded memory-safety protocol, not a future-return claim.
    It supplies an output cell only if the acquired type allows the write.
    The NULL name is legal and needs no string bytes. *)
Definition flag_name_get_access (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before : UCOS2_Verify_State)
  (p pname : Z) (slot : option Z) (raw : FlagGroupImage) (old : option Z) : Prop :=
  flag_name_get_early_error p pname (task_name_get_nesting before) = None ->
  forall acquired,
    critical_region_interval critical sg invocation before acquired ->
    UCOS2_state_inv sg acquired ->
    (exists image, flag_name_get_selected sg acquired p slot raw image) /\
    (forall image, flag_name_get_selected sg acquired p slot raw image ->
      image.(flagImageType) = 5 -> exists previous chars,
        old = Some previous /\
        task_name_get_readable acquired.(NameState) image.(flagImageName) chars).

Definition flag_name_get_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (before : UCOS2_Verify_State)
  (p pname perr : Z) (slot : option Z) (raw : FlagGroupImage) (old : option Z) : Assertion :=
  coq_prop (UCOS2_state_inv sg before /\
    flag_name_get_access critical sg invocation before p pname slot raw old) &&
  (task_name_get_closed platform critical sg invocation origin mask before **
   perr # UChar |->_ ** task_name_get_output_cell pname old **
   flag_name_get_guarded_private before p pname slot raw).

Record FlagNameGetObservation : Type := flag_name_get_observation {
  flag_name_get_observed_length : Z;
  flag_name_get_observed_error : Z;
  flag_name_get_observed_output : option Z
}.

Definition flag_name_get_protected_program (sg : StableGlobVars) (p : Z)
  (slot : option Z) (raw : FlagGroupImage)
  : program UCOS2_Verify_State FlagNameGetObservation :=
  StateRelMonad.bind (get (fun s image => flag_name_get_selected sg s p slot raw image))
    (fun image => if Z.eqb image.(flagImageType) 5 then
      StateRelMonad.bind (task_name_get_strlen_program image.(flagImageName))
        (fun len => StateRelMonad.ret
          (flag_name_get_observation len 0 (Some image.(flagImageName))))
      else StateRelMonad.ret (flag_name_get_observation 0 1 None)).

Definition flag_name_get_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (p pname : Z)
  (slot : option Z) (raw : FlagGroupImage)
  : program UCOS2_Verify_State FlagNameGetObservation :=
  if Z.eqb p 0 then StateRelMonad.ret (flag_name_get_observation 0 110 None) else
  if Z.eqb pname 0 then StateRelMonad.ret (flag_name_get_observation 0 12 None) else
  StateRelMonad.bind (get' task_name_get_nesting) (fun nesting =>
    if Z.ltb 0 nesting then StateRelMonad.ret (flag_name_get_observation 0 17 None) else
    StateRelMonad.bind (update (critical_region_interval critical sg invocation))
      (fun _ => StateRelMonad.bind (flag_name_get_protected_program sg p slot raw)
        (fun observed => StateRelMonad.bind
          (update (critical_region_interval critical sg invocation))
          (fun _ => StateRelMonad.ret observed)))).

Definition flag_name_get_safe critical sg invocation p pname slot raw before
  (X : FlagNameGetObservation -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (flag_name_get_program critical sg invocation p pname slot raw) X.

Definition flag_name_get_return_safe current result error output
  (X : FlagNameGetObservation -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq current) (StateRelMonad.ret
    (flag_name_get_observation result error output)) X.

Definition flag_name_get_effect (sg : StableGlobVars)
  (before acquired : UCOS2_Verify_State) (p pname : Z) (slot : option Z)
  (raw : FlagGroupImage) (result error : Z) (output : option Z) : Prop :=
  match flag_name_get_early_error p pname (task_name_get_nesting before) with
  | Some code => acquired = before /\ result = 0 /\ error = code /\ output = None
  | None => exists image, flag_name_get_selected sg acquired p slot raw image /\
      ((image.(flagImageType) <> 5 /\ result = 0 /\ error = 1 /\ output = None) \/
       (image.(flagImageType) = 5 /\ exists chars,
         task_name_get_readable acquired.(NameState) image.(flagImageName) chars /\
         result = task_name_get_length image.(flagImageName) chars /\
         error = 0 /\ output = Some image.(flagImageName)))
  end.

Lemma flag_name_get_effect_program : forall critical sg invocation p pname slot raw
  before acquired current result error output,
  flag_name_get_effect sg before acquired p pname slot raw result error output ->
  critical_region_interval critical sg invocation before acquired ->
  critical_region_interval critical sg invocation acquired current ->
  (flag_name_get_early_error p pname (task_name_get_nesting before) <> None ->
    current = before) ->
  flag_name_get_program critical sg invocation p pname slot raw before
    (flag_name_get_observation result error output) current.
Proof.
  intros critical sg invocation p pname slot raw before acquired current result error output
    Heffect Hacquire Hrelease Hearly.
  unfold flag_name_get_effect, flag_name_get_early_error in Heffect.
  unfold flag_name_get_program.
  destruct (Z.eqb p 0) eqn:Hp.
  - destruct Heffect as [-> [-> [-> ->]]].
    assert (current = before) by
      (apply Hearly; unfold flag_name_get_early_error; rewrite Hp; discriminate).
    subst; split; reflexivity.
  - destruct (Z.eqb pname 0) eqn:Hname.
    + destruct Heffect as [-> [-> [-> ->]]].
      assert (current = before) by
        (apply Hearly; unfold flag_name_get_early_error; rewrite Hp, Hname; discriminate).
      subst; split; reflexivity.
    + exists (task_name_get_nesting before), before; split; [split; reflexivity|].
      destruct (Z.ltb 0 (task_name_get_nesting before)) eqn:Hnest.
      * destruct Heffect as [-> [-> [-> ->]]].
        assert (current = before) by
          (apply Hearly; unfold flag_name_get_early_error; rewrite Hp, Hname, Hnest; discriminate).
        subst; split; reflexivity.
      * exists tt, acquired; split; [exact Hacquire|].
        exists (flag_name_get_observation result error output), acquired; split.
        -- unfold flag_name_get_protected_program.
           destruct Heffect as [image [Himage Hresult]].
           exists image, acquired; split; [split; [exact Himage|reflexivity]|].
           destruct Hresult as [[Htype [-> [-> ->]]]|[Htype [chars [Hread [-> [-> ->]]]]]].
           ++ rewrite (proj2 (Z.eqb_neq _ _) Htype); split; reflexivity.
           ++ rewrite Htype, Z.eqb_refl.
              exists (task_name_get_length image.(flagImageName) chars), acquired; split.
              ** unfold task_name_get_strlen_program; exists chars, acquired.
                 split; [split; [exact Hread|reflexivity]|split; reflexivity].
              ** split; reflexivity.
        -- exists tt, current; split; [exact Hrelease|split; reflexivity].
Qed.

Lemma flag_name_get_safe_return : forall critical sg invocation p pname slot raw
  before acquired current result error output X,
  flag_name_get_effect sg before acquired p pname slot raw result error output ->
  critical_region_interval critical sg invocation before acquired ->
  critical_region_interval critical sg invocation acquired current ->
  (flag_name_get_early_error p pname (task_name_get_nesting before) <> None -> current = before) ->
  flag_name_get_safe critical sg invocation p pname slot raw before X ->
  flag_name_get_return_safe current result error output X.
Proof.
  intros critical sg invocation p pname slot raw before acquired current result error output X
    Heffect Hacquire Hrelease Hearly Hsafe.
  eapply (highstependret_derive
    (flag_name_get_program critical sg invocation p pname slot raw)
    (eq before) (flag_name_get_observation result error output) (fun _ => eq current)).
  - intros s <-; exists current; split; [|reflexivity].
    eapply flag_name_get_effect_program; eassumption.
  - exact Hsafe.
Qed.

Definition flag_name_get_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (before : UCOS2_Verify_State)
  (p pname perr : Z) (slot : option Z) (raw : FlagGroupImage) (old : option Z) (result : Z)
  (X : FlagNameGetObservation -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX acquired current error output,
    coq_prop (flag_name_get_effect sg before acquired p pname slot raw result error output /\
      critical_region_interval critical sg invocation before acquired /\
      critical_region_interval critical sg invocation acquired current /\
      UCOS2_state_inv sg current /\ flag_name_get_return_safe current result error output X) &&
    (task_name_get_closed platform critical sg invocation origin mask current **
     perr # UChar |-> error **
     task_name_get_output_cell pname (match output with None => old | Some n => Some n end) **
     flag_name_get_guarded_private before p pname slot raw).

Definition flag_name_get_group_frame (c : KernelConfiguration) (p : Z)
  (image : FlagGroupImage) : Assertion :=
  store_optional_bytes (p + 1) (firstn 3 image.(flagImagePadding)) **
  (p + 4) # Ptr |-> image.(flagImageHead) **
  flag_word_rep c (p + 8) image.(flagImageBits) **
  store_optional_bytes (p + 8 + flag_word_bytes c) (skipn 3 image.(flagImagePadding)) **
  (if Z.eqb image.(flagImageType) 5 then emp else (p + 12) # Ptr |-> image.(flagImageName)).

Definition flag_name_get_read_frame (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (p : Z) (slot : option Z) (image : FlagGroupImage) : Assertion :=
  match slot with
  | None => UCOS2_raw_rep sg s
  | Some i => flag_name_get_group_frame sg.(osKernelConfig) p image **
      flag_groups_without sg s.(FlagState) i ** flag_nodes_rep sg s.(FlagState) **
      sg.(g_OSFlagFreeList) # Ptr |->
        (match s.(FlagState).(flagFree) with [] => 0 | j :: _ => flag_pool_addr sg j end) **
      UCOS2_raw_rep_missing_module sg s FlagModule
  end.

Lemma flag_name_get_group_fields_equiv : forall c p image,
  c.(cfgFlagNames) = true -> flag_group_name_offset c = 12 ->
  flag_group_rep c p image --||--
    flag_name_get_fields p image ** flag_name_get_group_frame c p image.
Proof.
  intros c p image Hnames Hoffset.
  unfold flag_group_rep, flag_name_get_fields, flag_name_get_name_cell,
    flag_name_get_group_frame; rewrite Hnames, Hoffset.
  destruct (Z.eqb image.(flagImageType) 5); split; entailer!.
Qed.

Lemma flag_name_get_read_equiv : forall sg s p slot raw image,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  sg.(osKernelConfig).(cfgFlagNames) = true ->
  flag_group_name_offset sg.(osKernelConfig) = 12 ->
  flag_name_get_selected sg s p slot raw image ->
  UCOS2_raw_rep sg s ** flag_name_get_private p slot raw --||--
    flag_name_get_fields p image ** flag_name_get_read_frame sg s p slot image.
Proof.
  intros sg s p slot raw image Henabled Hnames Hoffset Hselected.
  destruct slot as [i|].
  - destruct Hselected as [-> Hlookup].
    unfold flag_name_get_private, flag_name_get_read_frame.
    rewrite (UCOS2_raw_rep_split_module sg s FlagModule).
    cbn [UCOS2_module_rep]; unfold flag_configured_rep; rewrite Henabled.
    unfold flag_raw_rep.
    pose proof (flag_groups_split_group sg s.(FlagState) i image Hlookup) as Hsplit.
    pose proof (flag_groups_merge_group sg s.(FlagState) i image Hlookup) as Hmerge.
    split.
    + sep_apply Hsplit; rewrite (flag_name_get_group_fields_equiv _ _ _ Hnames Hoffset); entailer!.
    + sep_apply (proj2 (flag_name_get_group_fields_equiv
        (osKernelConfig sg) (flag_pool_addr sg i) image Hnames Hoffset)).
      sep_apply Hmerge; entailer!.
  - unfold flag_name_get_selected in Hselected; subst image.
    unfold flag_name_get_private, flag_name_get_read_frame; split; entailer!.
Qed.

Lemma flag_name_get_names_equiv : forall sg s name chars,
  task_name_get_readable s.(NameState) name chars ->
  UCOS2_raw_rep sg s --||--
    task_name_get_name_bytes name chars ** task_name_get_name_frame sg s name chars.
Proof.
  intros sg s name chars Hread.
  rewrite (UCOS2_raw_rep_split_module sg s NamesModule).
  cbn [UCOS2_module_rep].
  unfold task_name_get_name_bytes, task_name_get_name_frame.
  destruct (Z.eqb name 0) eqn:Hname; [split; entailer!|].
  apply Z.eqb_neq in Hname; specialize (Hread Hname).
  rewrite (task_name_get_name_split__resource_stages_strlen _ _ _ Hread).
  split; entailer!.
Qed.

Definition flag_name_get_call_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (saved : Z) (acquired : UCOS2_Verify_State)
  (p perr : Z) (slot : option Z) (raw image : FlagGroupImage) (chars : list Z) : Assertion :=
  task_name_get_name_frame sg acquired image.(flagImageName) chars **
  flag_name_get_private p slot raw **
  critical_region_masked platform critical sg invocation origin saved acquired **
  perr # UChar |->_ .

(** A fixed initialized pool slot remains readable even after delete/reuse;
    no preservation of the previous object identity is asserted. *)
Lemma flag_name_get_pool_image : forall sg s i,
  sg.(osKernelConfig).(cfgFlagEnabled) = true -> UCOS2_state_inv sg s ->
  0 <= i < sg.(osKernelConfig).(cfgMaxFlags) ->
  exists image, s.(FlagState).(flagImages) i = Some image.
Proof.
  intros sg s i Henabled Hvalid Hi.
  assert (Hflags : valid_flag_configuration sg s.(FlagState)) by
    (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags.
  destruct Hflags as [_ [Himages _]]; apply Himages; exact Hi.
Qed.

Lemma flag_name_get_pool_type_is_live : forall sg s i image,
  valid_flag_state sg s -> s.(flagImages) i = Some image ->
  image.(flagImageType) = 5 ->
  exists group, s.(flagUsed) i = Some group /\ image.(flagImageName) = group.(flagName).
Proof.
  intros sg s i image [Hpartition [Himages [_ [Hused [Hfree _]]]]] Himage Htype.
  assert (Hi : 0 <= i < sg.(osKernelConfig).(cfgMaxFlags)) by
    (apply Himages; eauto).
  assert (Hnotfree : ~ In i s.(flagFree)).
  { intro Hin; apply in_split in Hin; destruct Hin as [pre [rest Hlist]].
    destruct (Hfree pre i rest Hlist) as [other [Hother [Hzero _]]].
    rewrite Himage in Hother; inversion Hother; subst; lia. }
  destruct Hpartition as [_ [_ Hpartition]].
  destruct (proj2 (Hpartition i) (conj Hi Hnotfree)) as [group Hgroup].
  destruct (Hused i group Hgroup) as (_ & _ & _ & other & Hother & _ & _ & _ & Hname).
  rewrite Himage in Hother; inversion Hother; subst; eauto.
Qed.

Lemma flag_name_get_pool_name_readable : forall sg s i image,
  sg.(osKernelConfig).(cfgFlagEnabled) = true -> sg.(osKernelConfig).(cfgFlagNames) = true ->
  UCOS2_state_inv sg s -> s.(FlagState).(flagImages) i = Some image ->
  image.(flagImageType) = 5 -> exists chars, readable_name s.(NameState) image.(flagImageName) chars.
Proof.
  intros sg s i image Henabled Hnames Hvalid Himage Htype.
  assert (Hflags : valid_flag_configuration sg s.(FlagState)) by
    (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  assert (Hroots : kernel_names_valid sg s) by
    (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags.
  destruct (flag_name_get_pool_type_is_live sg s.(FlagState) i image Hflags Himage Htype)
    as [group [Hgroup Hname]].
  apply Hroots; right; right; left; repeat split; try assumption.
  exists i, group; auto.
Qed.

(** The pool domain includes free slots and slots whose identity changes
    before Save. No live-object or entry-name preservation premise is used. *)
Lemma flag_name_get_pool_access : forall critical sg invocation before p pname i raw previous,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  sg.(osKernelConfig).(cfgFlagNames) = true ->
  p = flag_pool_addr sg i -> 0 <= i < sg.(osKernelConfig).(cfgMaxFlags) ->
  flag_name_get_access critical sg invocation before p pname (Some i) raw (Some previous).
Proof.
  intros critical sg invocation before p pname i raw previous Henabled Hnames Hp Hi.
  intros _ acquired Hinterval Hvalid; split.
  - destruct (flag_name_get_pool_image sg acquired i Henabled Hvalid Hi) as [image Himage].
    exists image; split; assumption.
  - intros image [_ Himage] Htype.
    destruct (flag_name_get_pool_name_readable sg acquired i image
      Henabled Hnames Hvalid Himage Htype) as [chars Hread].
    exists previous, chars; split; [reflexivity|].
    intros _; exact Hread.
Qed.

(** Raw handles use the current client interface's proved NameState frame;
    they never own another copy of globally represented string bytes. *)
Lemma flag_name_get_raw_access : forall critical sg invocation before p pname raw old,
  (raw.(flagImageType) = 5 -> exists previous chars,
    old = Some previous /\
    task_name_get_readable before.(NameState) raw.(flagImageName) chars) ->
  flag_name_get_access critical sg invocation before p pname None raw old.
Proof.
  intros critical sg invocation before p pname raw old Hread _ acquired Hinterval Hvalid.
  split; [exists raw; reflexivity|].
  intros image Himage Htype; unfold flag_name_get_selected in Himage; subst image.
  destruct (Hread Htype) as [previous [chars [Hold Hchars]]].
  exists previous, chars; split; [exact Hold|].
  rewrite <- (critical_region_interval_preserves_name_state
    critical sg invocation before acquired Hinterval); exact Hchars.
Qed.

(** An admissible state has at least the empty-interference execution.
    This is non-vacuity, not a claim that an arbitrary scheduler returns. *)
Lemma flag_name_get_program_has_result : forall critical sg invocation before p pname slot raw old,
  UCOS2_state_inv sg before ->
  flag_name_get_access critical sg invocation before p pname slot raw old ->
  exists observation,
    flag_name_get_program critical sg invocation p pname slot raw before observation before.
Proof.
  intros critical sg invocation before p pname slot raw old Hvalid Haccess.
  assert (Hinterval : critical_region_interval critical sg invocation before before) by constructor.
  destruct (flag_name_get_early_error p pname (task_name_get_nesting before)) as [code|] eqn:Hearly.
  - exists (flag_name_get_observation 0 code None).
    eapply flag_name_get_effect_program with (acquired := before); try eassumption; [|auto].
    unfold flag_name_get_effect; rewrite Hearly; auto.
  - destruct (Haccess Hearly before Hinterval Hvalid) as [[image Himage] Hread].
    destruct (Z.eq_dec image.(flagImageType) 5) as [Htype|Htype].
    + destruct (Hread image Himage Htype) as [previous [chars [Hold Hchars]]].
      exists (flag_name_get_observation (task_name_get_length image.(flagImageName) chars)
        0 (Some image.(flagImageName))).
      eapply flag_name_get_effect_program with (acquired := before); try eassumption; [|auto].
      unfold flag_name_get_effect; rewrite Hearly; exists image; split; [exact Himage|].
      right; split; [exact Htype|]; exists chars; auto.
    + exists (flag_name_get_observation 0 1 None).
      eapply flag_name_get_effect_program with (acquired := before); try eassumption; [|auto].
      unfold flag_name_get_effect; rewrite Hearly; exists image; split; [exact Himage|].
      left; auto.
Qed.

(** The reused Restore postcondition follows from the registered interval
    and the released invariant, rather than an additional platform axiom. *)
Lemma flag_name_get_restore_consequence : forall platform critical sg invocation origin saved released current,
  UCOS2_state_inv sg released ->
  critical_region_interval critical sg invocation released current ->
  task_name_get_closed platform critical sg invocation origin (armv7a_irq_fiq_mask saved) current |--
    task_name_get_restore_post platform critical sg invocation origin saved released.
Proof.
  intros platform critical sg invocation origin saved released current Hvalid Hinterval.
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation released current Hinterval Hvalid)) as Hcurrent.
  unfold task_name_get_restore_post; Exists current; entailer!.
Qed.
