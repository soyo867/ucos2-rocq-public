Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Export Ucos2Verify.VC.code.memory.spec.mem_query_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_name_get_spec.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source order: NULL control, NULL output, ISR, Save/read/StrLen/Restore.
    Control images may be caller-owned, shared free, or shared allocated.
    The output and error cells have their actual, disjoint ownership. No
    lifetime of a shared returned string is promised after Restore. *)
Definition mem_name_get_early_error (pe pn nesting : Z) : option Z :=
  if Z.eqb pe 0 then Some 96
  else if Z.eqb pn 0 then Some 12
  else if Z.ltb 0 nesting then Some 17 else None.

Definition mem_name_get_addresses (sg : StableGlobVars) (nesting : Z) : Prop :=
  sg.(g_OSIntNesting) = nesting.

Definition mem_name_get_names (view : MemQueryView) (raw : NameResourceState)
  (state : UCOS2_Verify_State) : NameResourceState :=
  match view with MemQueryRaw _ => raw | MemQueryPool _ => state.(NameState) end.

Definition mem_name_get_selected (view : MemQueryView) (raw : NameResourceState)
  (raw_chars : list Z) (state : UCOS2_Verify_State)
  (image : MemoryControlImage) (chars : list Z) : Prop :=
  mem_query_selected view state image /\
  (match view with MemQueryRaw _ => chars = raw_chars | MemQueryPool _ => True end) /\
  task_name_get_readable (mem_name_get_names view raw state) image.(memImageName) chars.

Definition mem_name_get_admission (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe : Z) (view : MemQueryView)
  (raw : NameResourceState) (raw_chars : list Z) (before : UCOS2_Verify_State) : Prop :=
  mem_query_admission critical sg invocation pe view before /\
  match view with
  | MemQueryRaw image => task_name_get_readable raw image.(memImageName) raw_chars
  | MemQueryPool _ => True
  end.

Definition mem_name_get_raw_bytes (view : MemQueryView) (raw_chars : list Z) : Assertion :=
  match view with
  | MemQueryRaw image => task_name_get_name_bytes image.(memImageName) raw_chars
  | MemQueryPool _ => emp
  end.

Definition mem_name_get_source (sg : StableGlobVars) (pe : Z)
  (view : MemQueryView) (raw_chars : list Z) : Assertion :=
  mem_query_source_rep sg pe view ** mem_name_get_raw_bytes view raw_chars.

Definition mem_name_get_guarded_source (sg : StableGlobVars) (pe pn : Z)
  (view : MemQueryView) (raw_chars : list Z) (before : UCOS2_Verify_State) : Assertion :=
  match mem_name_get_early_error pe pn (task_name_get_nesting before) with
  | Some _ => emp
  | None => mem_name_get_source sg pe view raw_chars
  end.

Definition mem_name_get_access critical sg invocation pe pn view raw raw_chars before
  (old : option Z) : Prop :=
  mem_name_get_early_error pe pn (task_name_get_nesting before) = None ->
  mem_name_get_admission critical sg invocation pe view raw raw_chars before /\
  exists previous, old = Some previous.

Definition mem_name_get_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (before : UCOS2_Verify_State)
  (pe pn err : Z) (view : MemQueryView) (raw : NameResourceState)
  (raw_chars : list Z) (old : option Z) : Assertion :=
  coq_prop (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old) &&
  (mutex_query_closed platform critical sg invocation origin mask before **
   err # UChar |->_ ** task_name_get_output_cell pn old **
   mem_name_get_guarded_source sg pe pn view raw_chars before).

Record MemNameGetObservation : Type := mem_name_get_observation {
  mem_name_get_observed_length : Z;
  mem_name_get_observed_error : Z;
  mem_name_get_observed_output : option Z
}.

Definition mem_name_get_observe (view : MemQueryView) (raw : NameResourceState)
  (raw_chars : list Z) : program UCOS2_Verify_State MemNameGetObservation :=
  StateRelMonad.bind (get (fun state image => mem_query_selected view state image))
    (fun image => StateRelMonad.bind
      (get (fun state chars =>
        (match view with MemQueryRaw _ => chars = raw_chars | MemQueryPool _ => True end) /\
        task_name_get_readable (mem_name_get_names view raw state) image.(memImageName) chars))
      (fun chars => StateRelMonad.ret
        (mem_name_get_observation (task_name_get_length image.(memImageName) chars)
          0 (Some image.(memImageName))))).

Definition mem_name_get_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe pn : Z)
  (view : MemQueryView) (raw : NameResourceState) (raw_chars : list Z)
  : program UCOS2_Verify_State MemNameGetObservation :=
  if Z.eqb pe 0 then StateRelMonad.ret (mem_name_get_observation 0 96 None)
  else if Z.eqb pn 0 then StateRelMonad.ret (mem_name_get_observation 0 12 None)
  else StateRelMonad.bind (get' task_name_get_nesting) (fun nesting =>
    if Z.ltb 0 nesting then StateRelMonad.ret (mem_name_get_observation 0 17 None)
    else StateRelMonad.bind (update (critical_region_interval critical sg invocation))
      (fun _ => StateRelMonad.bind (mem_name_get_observe view raw raw_chars)
        (fun observed => StateRelMonad.bind
          (update (critical_region_interval critical sg invocation))
          (fun _ => StateRelMonad.ret observed)))).

Definition mem_name_get_safe critical sg invocation pe pn view raw raw_chars before
  (X : MemNameGetObservation -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (mem_name_get_program critical sg invocation pe pn view raw raw_chars) X.

Definition mem_name_get_return_safe current result error output
  (X : MemNameGetObservation -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq current) (StateRelMonad.ret (mem_name_get_observation result error output)) X.

(** The delivered StrLen source contract returns its non-NULL result fact as
    a spatial [coq_prop], not as a pure conjunction.  Retain that carrier:
    extracting its mathematical fact does not license discarding its heap.
    This is in addition to, never a replacement for, the complete borrowed
    byte array, control, kernel, error and output resources. *)
Definition mem_name_get_strlen_carrier (name : Z) : Assertion :=
  if Z.eqb name 0 then emp else TT.

Definition mem_name_get_effect critical sg invocation pe pn view raw raw_chars
  before acquired current result error output : Prop :=
  match mem_name_get_early_error pe pn (task_name_get_nesting before) with
  | Some code => acquired = before /\ current = before /\
      result = 0 /\ error = code /\ output = None
  | None => critical_region_interval critical sg invocation before acquired /\
      critical_region_interval critical sg invocation acquired current /\
      exists image chars, mem_name_get_selected view raw raw_chars acquired image chars /\
        result = task_name_get_length image.(memImageName) chars /\
        error = 0 /\ output = Some image.(memImageName)
  end.

Definition mem_name_get_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (before : UCOS2_Verify_State)
  (pe pn err : Z) (view : MemQueryView) (raw : NameResourceState)
  (raw_chars : list Z) (old : option Z) (result : Z)
  (X : MemNameGetObservation -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX acquired current error output,
    coq_prop (mem_name_get_effect critical sg invocation pe pn view raw raw_chars
      before acquired current result error output /\
      mem_name_get_return_safe current result error output X) &&
    (mutex_query_closed platform critical sg invocation origin mask current **
     err # UChar |-> error **
     task_name_get_output_cell pn (match output with None => old | Some name => Some name end) **
     mem_name_get_guarded_source sg pe pn view raw_chars before **
     match output with None => emp | Some name => mem_name_get_strlen_carrier name end).

Lemma mem_name_get_pool_readable : forall sg state id image,
  UCOS2_state_inv sg state ->
  sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  sg.(osKernelConfig).(cfgMemoryNames) = true ->
  state.(MemoryState).(memControlImages) id = Some image ->
  exists chars, readable_name state.(NameState) image.(memImageName) chars.
Proof.
  intros sg state id image Hvalid Henabled Hnames Himage.
  assert (Hroots : kernel_names_valid sg state).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  apply Hroots; right; right; right; left.
  split; [exact Henabled|]. split; [exact Hnames|].
  left; exists id, image; auto.
Qed.

Lemma mem_name_get_acquired_selection : forall critical sg invocation pe view raw raw_chars before acquired,
  mem_name_get_admission critical sg invocation pe view raw raw_chars before ->
  UCOS2_state_inv sg before -> UCOS2_state_inv sg acquired ->
  critical_region_interval critical sg invocation before acquired ->
  exists image chars, mem_name_get_selected view raw raw_chars acquired image chars.
Proof.
  intros critical sg invocation pe view raw raw_chars before acquired [Hadmission Hraw]
    Hbefore Hacquired Hinterval.
  destruct (mem_query_acquired_image critical sg invocation pe view before acquired
    Hadmission Hbefore Hinterval) as [image Himage].
  destruct view as [original|id].
  - cbn [mem_query_selected] in Himage; subst image.
    exists original, raw_chars; unfold mem_name_get_selected, mem_name_get_names.
    split; [reflexivity|]. split; [reflexivity|exact Hraw].
  - destruct (mem_name_get_pool_readable sg acquired id image Hacquired
      (proj1 Hadmission) (proj1 (proj2 Hadmission)) Himage) as [chars Hread].
    exists image, chars; unfold mem_name_get_selected, mem_name_get_names.
    split; [exact Himage|]. split; [exact I|]. intros _; exact Hread.
Qed.

Lemma mem_name_get_effect_program : forall critical sg invocation pe pn view raw raw_chars
  before acquired current result error output,
  mem_name_get_effect critical sg invocation pe pn view raw raw_chars
    before acquired current result error output ->
  mem_name_get_program critical sg invocation pe pn view raw raw_chars before
    (mem_name_get_observation result error output) current.
Proof.
  intros critical sg invocation pe pn view raw raw_chars before acquired current result error output Heffect.
  unfold mem_name_get_effect, mem_name_get_early_error in Heffect.
  unfold mem_name_get_program.
  destruct (pe =? 0); [destruct Heffect as [-> [-> [-> [-> ->]]]]; split; reflexivity|].
  destruct (pn =? 0); [destruct Heffect as [-> [-> [-> [-> ->]]]]; split; reflexivity|].
  exists (task_name_get_nesting before), before; split; [split; reflexivity|].
  destruct (0 <? task_name_get_nesting before).
  - destruct Heffect as [-> [-> [-> [-> ->]]]]; split; reflexivity.
  - destruct Heffect as [Hacquire [Hrestore [image [chars [[Himage [Hchars Hread]] [-> [-> ->]]]]]]].
    exists tt, acquired; split; [exact Hacquire|].
    exists (mem_name_get_observation (task_name_get_length image.(memImageName) chars)
      0 (Some image.(memImageName))), acquired; split.
    + unfold mem_name_get_observe.
      exists image, acquired; split; [split; [exact Himage|reflexivity]|].
      exists chars, acquired; split; [split; [split; assumption|reflexivity]|split; reflexivity].
    + exists tt, current; split; [exact Hrestore|split; reflexivity].
Qed.

Lemma mem_name_get_safe_return : forall critical sg invocation pe pn view raw raw_chars
  before acquired current result error output X,
  mem_name_get_effect critical sg invocation pe pn view raw raw_chars
    before acquired current result error output ->
  mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ->
  mem_name_get_return_safe current result error output X.
Proof.
  intros critical sg invocation pe pn view raw raw_chars before acquired current result error output X
    Heffect Hsafe.
  eapply (highstependret_derive
    (mem_name_get_program critical sg invocation pe pn view raw raw_chars)
    (eq before) (mem_name_get_observation result error output) (fun _ => eq current)).
  - intros state <-; exists current; split; [|reflexivity].
    eapply mem_name_get_effect_program; eassumption.
  - exact Hsafe.
Qed.

Lemma mem_name_get_program_effect : forall critical sg invocation pe pn view raw raw_chars
  before current result error output,
  mem_name_get_program critical sg invocation pe pn view raw raw_chars before
    (mem_name_get_observation result error output) current ->
  exists acquired, mem_name_get_effect critical sg invocation pe pn view raw raw_chars
    before acquired current result error output.
Proof.
  intros critical sg invocation pe pn view raw raw_chars before current result error output Hprogram.
  unfold mem_name_get_program in Hprogram.
  unfold mem_name_get_effect, mem_name_get_early_error.
  destruct (pe =? 0).
  - destruct Hprogram as [Hresult <-]; inversion Hresult; subst; exists before; auto.
  - destruct (pn =? 0).
    + destruct Hprogram as [Hresult <-]; inversion Hresult; subst; exists before; auto.
    + destruct Hprogram as [nesting [entry [[-> <-] Hprogram]]].
      destruct (0 <? task_name_get_nesting before).
      * destruct Hprogram as [Hresult <-]; inversion Hresult; subst; exists before; auto.
      * destruct Hprogram as [u [acquired [Hacquire [observed [released [Hobserve
          [v [returned [Hrestore [Hresult Hcurrent]]]]]]]]]].
        unfold mem_name_get_observe in Hobserve.
        destruct Hobserve as [image [read_image [[Himage <-] Hobserve]]].
        destruct Hobserve as [chars [read_chars [[[Hchars Hread] <-] [Hobserved Hreleased]]]].
        subst released returned observed; inversion Hresult; subst.
        exists acquired; split; [exact Hacquire|]. split; [exact Hrestore|].
        exists image, chars; unfold mem_name_get_selected; auto.
Qed.

Lemma mem_name_get_program_has_result : forall critical sg invocation pe pn view raw raw_chars before old,
  UCOS2_state_inv sg before ->
  mem_name_get_access critical sg invocation pe pn view raw raw_chars before old ->
  exists observed, mem_name_get_program critical sg invocation pe pn view raw raw_chars before observed before.
Proof.
  intros critical sg invocation pe pn view raw raw_chars before old Hvalid Haccess.
  destruct (mem_name_get_early_error pe pn (task_name_get_nesting before)) as [code|] eqn:Herror.
  - exists (mem_name_get_observation 0 code None).
    eapply mem_name_get_effect_program with (acquired := before).
    unfold mem_name_get_effect; rewrite Herror; auto.
  - destruct (Haccess Herror) as [Hadmission Houtput].
    assert (Hrefl : critical_region_interval critical sg invocation before before) by constructor.
    destruct (mem_name_get_acquired_selection critical sg invocation pe view raw raw_chars
      before before Hadmission Hvalid Hvalid Hrefl) as [image [chars Hselected]].
    exists (mem_name_get_observation (task_name_get_length image.(memImageName) chars)
      0 (Some image.(memImageName))).
    eapply mem_name_get_effect_program with (acquired := before).
    unfold mem_name_get_effect; rewrite Herror; split; [exact Hrefl|].
    split; [exact Hrefl|]. exists image, chars; auto.
Qed.

Definition mem_name_get_control_residual (sg : StableGlobVars) (pe : Z)
  (view : MemQueryView) (acquired : UCOS2_Verify_State) (image : MemoryControlImage) : Assertion :=
  memory_control_without_field sg pe image MCBName ** mem_query_source_frame sg view acquired.

Lemma mem_name_get_control_split : forall sg pe view acquired image,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  sg.(osKernelConfig).(cfgMemoryNames) = true ->
  mem_query_address sg pe view -> mem_query_selected view acquired image ->
  UCOS2_inv sg acquired ** mem_query_source_rep sg pe view |--
    memory_control_cell pe MCBName image.(memImageName) **
    mem_name_get_control_residual sg pe view acquired image.
Proof.
  intros sg pe view acquired image Henabled Hnames Haddress Himage.
  sep_apply_l_atomic (mem_query_source_split sg pe view acquired image Henabled Haddress Himage).
  assert (Hfield : In MCBName (memory_control_fields sg.(osKernelConfig))).
  { unfold memory_control_fields; rewrite Hnames.
    apply in_or_app; right; left; reflexivity. }
  sep_apply_l_atomic (store_memory_control_split_field sg pe image MCBName Hfield).
  unfold mem_name_get_control_residual; entailer!.
Qed.

Lemma mem_name_get_control_merge : forall sg pe view acquired image,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  sg.(osKernelConfig).(cfgMemoryNames) = true ->
  mem_query_address sg pe view -> mem_query_selected view acquired image ->
  memory_control_cell pe MCBName image.(memImageName) **
    mem_name_get_control_residual sg pe view acquired image |--
  UCOS2_inv sg acquired ** mem_query_source_rep sg pe view.
Proof.
  intros sg pe view acquired image Henabled Hnames Haddress Himage.
  unfold mem_name_get_control_residual.
  assert (Hfield : In MCBName (memory_control_fields sg.(osKernelConfig))).
  { unfold memory_control_fields; rewrite Hnames.
    apply in_or_app; right; left; reflexivity. }
  pose proof (store_memory_control_merge_field sg pe image MCBName Hfield) as Hmerge.
  cbn [memory_control_value] in Hmerge.
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (mem_query_source_merge sg pe view acquired image Henabled Haddress Himage).
  entailer!.
Qed.

Definition mem_name_get_string_residual (sg : StableGlobVars) (pe : Z)
  (view : MemQueryView) (acquired : UCOS2_Verify_State) (name : Z) (chars : list Z) : Assertion :=
  match view with
  | MemQueryRaw image => UCOS2_inv sg acquired ** store_memory_control sg pe image
  | MemQueryPool _ => task_name_get_name_frame sg acquired name chars
  end.

Lemma mem_name_get_string_split : forall sg pe view raw raw_chars acquired image chars,
  UCOS2_state_inv sg acquired -> mem_name_get_selected view raw raw_chars acquired image chars ->
  UCOS2_inv sg acquired ** mem_name_get_source sg pe view raw_chars |--
    task_name_get_name_bytes image.(memImageName) chars **
    mem_name_get_string_residual sg pe view acquired image.(memImageName) chars.
Proof.
  intros sg pe [original|id] raw raw_chars acquired image chars Hvalid [Himage [Hchars Hread]].
  - cbn [mem_query_selected] in Himage; subst image chars.
    unfold mem_name_get_source, mem_query_source_rep, mem_name_get_raw_bytes,
      mem_name_get_string_residual; entailer!.
  - unfold mem_name_get_source, mem_query_source_rep, mem_name_get_raw_bytes,
      mem_name_get_string_residual.
    rewrite UCOS2_inv_split_names.
    unfold task_name_get_name_bytes, task_name_get_name_frame.
    destruct (Z.eqb image.(memImageName) 0) eqn:Hnull; [entailer!|].
    rewrite (task_name_get_name_split__resource_stages_strlen acquired.(NameState)
      image.(memImageName) chars).
    + entailer!.
    + apply Hread; apply Z.eqb_neq; exact Hnull.
Qed.

Lemma mem_name_get_string_merge : forall sg pe view raw raw_chars acquired image chars,
  UCOS2_state_inv sg acquired -> mem_name_get_selected view raw raw_chars acquired image chars ->
  task_name_get_name_bytes image.(memImageName) chars **
    mem_name_get_string_residual sg pe view acquired image.(memImageName) chars |--
  UCOS2_inv sg acquired ** mem_name_get_source sg pe view raw_chars.
Proof.
  intros sg pe [original|id] raw raw_chars acquired image chars Hvalid [Himage [Hchars Hread]].
  - cbn [mem_query_selected] in Himage; subst image chars.
    unfold mem_name_get_source, mem_query_source_rep, mem_name_get_raw_bytes,
      mem_name_get_string_residual; entailer!.
  - unfold mem_name_get_source, mem_query_source_rep, mem_name_get_raw_bytes,
      mem_name_get_string_residual.
    rewrite UCOS2_inv_split_names.
    unfold task_name_get_name_bytes, task_name_get_name_frame.
    destruct (Z.eqb image.(memImageName) 0) eqn:Hnull; [entailer!|].
    rewrite (task_name_get_name_split__resource_stages_strlen acquired.(NameState)
      image.(memImageName) chars).
    + entailer!.
    + apply Hread; apply Z.eqb_neq; exact Hnull.
Qed.

Definition mem_name_get_call_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (saved : Z) (pe err : Z) (view : MemQueryView)
  (acquired : UCOS2_Verify_State) (name : Z) (chars : list Z) : Assertion :=
  mem_name_get_string_residual sg pe view acquired name chars **
  critical_region_masked platform critical sg invocation origin saved acquired ** err # UChar |->_ .

(** Exact consequence obligation of the actual delivered source_spec.  In
    particular its [coq_prop] atoms are spatial on both sides; the returned
    non-NULL carrier is conserved by [mem_name_get_strlen_carrier]. *)
Lemma mem_name_get_strlen_source_consequence : forall
  (psrc : Z) (frame : Assertion) (chars : list Z)
  (names : NameResourceState) (entry : Z),
  coq_prop (psrc = entry) && coq_prop (task_name_get_readable names entry chars) &&
    task_name_get_name_bytes entry chars ** frame |--
  EX (source_entry base : Z) (source_names : NameResourceState)
    (source_chars : list Z) (source_frame : Assertion),
    ((coq_prop (psrc = source_entry) && coq_prop (psrc <> 0) &&
      coq_prop (psrc = base) &&
      coq_prop (readable_name source_names psrc source_chars) **
      os_strlen_bytes psrc source_chars ** source_frame) ||
     (coq_prop (psrc = source_entry) && coq_prop (psrc = 0) && source_frame)) **
    (((EX retval,
        coq_prop (source_entry = 0) && coq_prop (retval = 0) && source_frame) ||
      (EX retval,
        coq_prop (source_entry <> 0) && coq_prop (source_entry = base) &&
        coq_prop (os_strlen_result source_chars retval) **
        os_strlen_bytes source_entry source_chars ** source_frame)) -*
     (EX retval, coq_prop (retval = task_name_get_length entry chars) &&
        task_name_get_name_bytes entry chars ** frame ** mem_name_get_strlen_carrier entry)).
Proof.
  intros psrc frame chars names entry; Intros; subst psrc.
  destruct (Z.eqb entry 0) eqn:Hnull.
  all: Exists entry entry names chars frame.
  all: match goal with |- _ |-- ?P ** (?Q -* ?R) =>
    assert (Hwand : emp |-- Q -* R)
  end.
  1,3: (apply_sepcon_adjoint; pre_process;
    apply derivable1_orp_elim; Intros retval; Exists retval;
    unfold task_name_get_length, task_name_get_name_bytes,
      mem_name_get_strlen_carrier, os_strlen_result in *;
    rewrite Hnull; entailer!;
    first [apply Z.eqb_eq in Hnull; congruence | apply Z.eqb_neq in Hnull; congruence]).
  all: sep_apply_r_atomic Hwand.
  - Right; unfold task_name_get_name_bytes; rewrite Hnull.
    apply Z.eqb_eq in Hnull; entailer!.
  - Left; unfold task_name_get_name_bytes; rewrite Hnull.
    assert (entry <> 0) by (apply Z.eqb_neq; exact Hnull).
    unfold task_name_get_readable in *; entailer!.
    apply derivable1_truep_intros.
Qed.
