Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Equalities.
Require Import SimpleC.Common.CTypes.
Require Import SimpleC.CoreLang.CTypes.
From SimpleC.SL Require Import Mem ConAssertion.
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.timer.spec.timer_callback_rules.

(** The declarations below implement a typed callback-contract interface.
    The source function table and the caller's resource protocol are fixed
    parts of the shared environment.  They are not inferred from a C type.

    A protocol relation alone gives no callable capability.  The only
    introduction lemma requires [callback_source_evidence]: a proof of
    all-frame Hoare safety AND positive coverage of every source normal
    result.  Its caller must construct these fields from the actual callback
    body and the existing CSL/critical/CPU source contracts that authorize
    its resource steps.  This file supplies no such concrete instance and
    no rule creating arbitrary STS observations or tokens.

    Source linking still has to identify [source_functions] with the actual
    C addresses and bodies.  This is the existing QCP source/linking trust
    boundary, not a theorem asserted by this adapter. *)

Module TimerCallback_C_Rules.

Module Old := UCOS2_C_Rules.

Definition ParamSig : Type := list SimpleCtype.
Definition FuncSig : Type := (ParamSig * SimpleCtype)%type.

Definition RetType (result_type : SimpleCtype) : Type :=
  match result_type with
  | CT_basic CT_void => unit
  | _ => Z
  end.

Fixpoint ParamTuple (parameters : ParamSig) : Type :=
  match parameters with
  | nil => unit
  | cons _ nil => Z
  | cons _ remaining => (Z * ParamTuple remaining)%type
  end.

(** This is the official FunAssertion signature shape, using the existing
    MonadErr implementation and the unique CoreLang C-type definitions.
    The source semantics starts after callee parameter initialization and
    ends after callee-owned parameter storage has been discharged. *)
Definition FunSem (signature : FuncSig) : Type :=
  ParamTuple (fst signature) -> MonadErr.M Mem.mem (RetType (snd signature)).

Definition FunEnv : Type := forall signature : FuncSig,
  Z -> option (FunSem signature).

Definition ResourceProtocol : Type := forall signature : FuncSig,
  FunSem signature -> ParamTuple (fst signature) ->
  Old.model -> RetType (snd signature) -> Old.model -> Prop.

Record callback_environment : Type := {
  source_functions : FunEnv;
  caller_resource_step : ResourceProtocol
}.

Module EnvironmentType <: Typ.
  Definition t : Type := callback_environment.
End EnvironmentType.

Module Rules := TimerCallbackRules EnvironmentType.
Export Rules SimpleCtypeNotations.

Definition timer_callback_signature : FuncSig :=
  (cons (CT_pointer (CT_basic CT_void))
    (cons (CT_pointer (CT_basic CT_void)) nil), CT_basic CT_void).

Definition resource_execution {signature : FuncSig}
  (environment : callback_environment) (body : FunSem signature)
  (arguments : ParamTuple (fst signature))
  : MonadErr.M Old.model (RetType (snd signature)) :=
  {| MonadErr.nrm := fun initial result final =>
       MonadErr.nrm (body arguments) initial.(ConAssertion.s_mem) result
         final.(ConAssertion.s_mem) /\
       caller_resource_step environment signature body arguments initial result final;
     MonadErr.err := fun initial =>
       MonadErr.err (body arguments) initial.(ConAssertion.s_mem) |}.

(** Coverage is a positive proposition.  It rules out taking only a safe
    subset of source outcomes without using double-negation elimination.
    The resulting state must satisfy the fixed caller protocol, not merely
    a postcondition chosen by this theorem. *)
Definition source_outcomes_covered {signature : FuncSig}
  (environment : callback_environment) (body : FunSem signature)
  (arguments : ParamTuple (fst signature)) (P : Rules.expr) : Prop :=
  forall initial result final_memory,
    P (initial, environment) ->
    MonadErr.nrm (body arguments) initial.(ConAssertion.s_mem) result final_memory ->
    exists final,
      final.(ConAssertion.s_mem) = final_memory /\
      caller_resource_step environment signature body arguments initial result final.

Record callback_source_evidence (environment : callback_environment)
  (signature : FuncSig) (body : FunSem signature)
  (P : ParamTuple (fst signature) -> Rules.expr)
  (Q : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr)
  : Prop := {
  source_evidence_hoare : forall arguments (frame : Rules.expr),
    MonadErrHoare.Hoare
      (fun initial => Rules.sepcon (P arguments) frame (initial, environment))
      (resource_execution environment body arguments)
      (fun result final => Rules.sepcon (Q arguments result) frame (final, environment));
  source_evidence_coverage : forall arguments (frame : Rules.expr),
    source_outcomes_covered environment body arguments
      (Rules.sepcon (P arguments) frame)
}.

Definition Spec (signature : FuncSig) : Type := FunSem signature -> Rules.expr.

Definition HoareFun (signature : FuncSig)
  (P : ParamTuple (fst signature) -> Rules.expr)
  (Q : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr)
  : Spec signature :=
  fun body state => callback_source_evidence (snd state) signature body P Q.

Definition func_ptr_spec {signature : FuncSig}
  (pointer : Z) (specification : Spec signature) : Rules.expr :=
  fun state => pointer <> 0%Z /\ exists body,
    source_functions (snd state) signature pointer = Some body /\
    specification body state.

Lemma func_ptr_spec_nonzero {signature : FuncSig}
  (pointer : Z) (specification : Spec signature) :
  Rules.derivable1 (func_ptr_spec pointer specification)
    (Rules.coq_prop (pointer <> 0%Z)).
Proof. intros state [Hnonzero Hbody]. exact Hnonzero. Qed.

Lemma func_ptr_spec_mono {signature : FuncSig} (pointer : Z)
  (first second : Spec signature) :
  (forall body, Rules.derivable1 (first body) (second body)) ->
  Rules.derivable1 (func_ptr_spec pointer first) (func_ptr_spec pointer second).
Proof.
  intros H state [Hnonzero [body [Hlookup Hspec]]].
  split; [exact Hnonzero |].
  exists body. split; [exact Hlookup | exact (H body state Hspec)].
Qed.

Lemma HoareFun_environment_eq (signature : FuncSig)
  (P : ParamTuple (fst signature) -> Rules.expr)
  (Q : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr)
  (body : FunSem signature) (first second : Rules.model) :
  snd first = snd second -> HoareFun signature P Q body first ->
  HoareFun signature P Q body second.
Proof. unfold HoareFun. intros Henv H. rewrite <- Henv. exact H. Qed.

(** Only assertions proved to depend on the shared environment can be
    retained independently of heap/resource changes.  This premise is not
    available for an arbitrary [Spec].  In particular, the quantifiers
    emitted around a callback's ghost parameters preserve this property. *)
Definition assertion_environment_only (P : Rules.expr) : Prop :=
  forall first second : Rules.model,
    snd first = snd second -> P first -> P second.

Definition specification_environment_only {signature : FuncSig}
  (specification : Spec signature) : Prop :=
  forall body, assertion_environment_only (specification body).

Lemma HoareFun_specification_environment_only (signature : FuncSig)
  (P : ParamTuple (fst signature) -> Rules.expr)
  (Q : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr) :
  specification_environment_only (HoareFun signature P Q).
Proof.
  intros body first second Henv Hspec.
  exact (HoareFun_environment_eq signature P Q body first second Henv Hspec).
Qed.

Lemma allp_assertion_environment_only (Witness : Type) (P : Witness -> Rules.expr) :
  (forall witness, assertion_environment_only (P witness)) ->
  assertion_environment_only (@Rules.allp Witness P).
Proof.
  intros H first second Henv HP witness.
  exact (H witness first second Henv (HP witness)).
Qed.

Lemma allp_specification_environment_only {signature : FuncSig}
  (Witness : Type) (specifications : Witness -> Spec signature) :
  (forall witness, specification_environment_only (specifications witness)) ->
  specification_environment_only
    (fun body => @Rules.allp Witness (fun witness => specifications witness body)).
Proof.
  intros H body. apply allp_assertion_environment_only.
  intro witness. exact (H witness body).
Qed.

Lemma func_ptr_spec_environment_eq {signature : FuncSig} (pointer : Z)
  (specification : Spec signature) :
  specification_environment_only specification ->
  forall first second : Rules.model,
    snd first = snd second ->
    func_ptr_spec pointer specification first ->
    func_ptr_spec pointer specification second.
Proof.
  intros Honly first second Henv [Hnonzero [body [Hlookup Hspec]]].
  split; [exact Hnonzero|]. exists body. split.
  - rewrite <- Henv. exact Hlookup.
  - exact (Honly body first second Henv Hspec).
Qed.

Lemma func_ptr_spec_join_iff {signature : FuncSig} (pointer : Z)
  (specification : Spec signature) :
  specification_environment_only specification ->
  forall first frame combined : Rules.model,
    Rules.join first frame combined ->
    (func_ptr_spec pointer specification first <->
     func_ptr_spec pointer specification combined).
Proof.
  intros Honly first frame combined Hjoin.
  change (Old.join (fst first) (fst frame) (fst combined) /\
    snd first = snd combined /\ snd frame = snd combined) in Hjoin.
  destruct Hjoin as [Hresource [Henv Hframe]]. split.
  - exact (func_ptr_spec_environment_eq pointer specification Honly first combined Henv).
  - apply (func_ptr_spec_environment_eq pointer specification Honly combined first).
    symmetry. exact Henv.
Qed.

Lemma func_ptr_spec_allp_specialize {signature : FuncSig} (pointer : Z)
  (Witness : Type) (specifications : Witness -> Spec signature) (witness : Witness) :
  Rules.derivable1
    (func_ptr_spec pointer
      (fun body => @Rules.allp Witness (fun selected => specifications selected body)))
    (func_ptr_spec pointer (specifications witness)).
Proof.
  apply func_ptr_spec_mono. intros body state Hall. exact (Hall witness).
Qed.

Lemma func_ptr_hoare_environment_eq (signature : FuncSig) (pointer : Z)
  (P : ParamTuple (fst signature) -> Rules.expr)
  (Q : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr)
  (first second : Rules.model) :
  snd first = snd second ->
  func_ptr_spec pointer (HoareFun signature P Q) first ->
  func_ptr_spec pointer (HoareFun signature P Q) second.
Proof.
  intros Henv [Hnonzero [body [Hlookup Hspec]]].
  split; [exact Hnonzero |]. exists body. split.
  - rewrite <- Henv. exact Hlookup.
  - apply (HoareFun_environment_eq signature P Q body first second Henv).
    exact Hspec.
Qed.

Lemma func_ptr_hoare_join_iff (signature : FuncSig) (pointer : Z)
  (P : ParamTuple (fst signature) -> Rules.expr)
  (Q : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr)
  (first frame combined : Rules.model) :
  Rules.join first frame combined ->
  (func_ptr_spec pointer (HoareFun signature P Q) first <->
   func_ptr_spec pointer (HoareFun signature P Q) combined).
Proof.
  intros Hjoin.
  change (Old.join (fst first) (fst frame) (fst combined) /\
    snd first = snd combined /\ snd frame = snd combined) in Hjoin.
  destruct Hjoin as [Hresource [Henv Hframe]]. split.
  - apply func_ptr_hoare_environment_eq. exact Henv.
  - apply func_ptr_hoare_environment_eq. symmetry. exact Henv.
Qed.

Lemma HoareFun_conseq (signature : FuncSig)
  (P P' : ParamTuple (fst signature) -> Rules.expr)
  (Q Q' : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr) :
  (forall arguments, Rules.derivable1 (P' arguments) (P arguments)) ->
  (forall arguments result, Rules.derivable1 (Q arguments result) (Q' arguments result)) ->
  forall body, Rules.derivable1 (HoareFun signature P Q body)
    (HoareFun signature P' Q' body).
Proof.
  intros Hpre Hpost body state [Hhoare Hcoverage].
  constructor.
  - intros arguments frame.
    destruct (Hhoare arguments frame) as [Hnormal Herror].
    split.
    + intros result initial final HP Hrun.
      assert (Hinitial : Rules.sepcon (P arguments) frame (initial, snd state)).
      { destruct HP as [owned [rest [Hjoin [Howned Hframe]]]].
        exists owned, rest. split; [exact Hjoin|].
        split; [exact (Hpre arguments owned Howned)|exact Hframe]. }
      destruct (Hnormal result initial final Hinitial Hrun)
        as [owned [rest [Hjoin [Howned Hframe]]]].
      exists owned, rest. split; [exact Hjoin|].
      split; [exact (Hpost arguments result owned Howned)|exact Hframe].
    + intros initial HP Herr.
      apply (Herror initial).
      * destruct HP as [owned [rest [Hjoin [Howned Hframe]]]].
        exists owned, rest. split; [exact Hjoin|].
        split; [exact (Hpre arguments owned Howned)|exact Hframe].
      * exact Herr.
  - intros arguments frame initial result final_memory HP Hrun.
    apply (Hcoverage arguments frame initial result final_memory).
    + destruct HP as [owned [rest [Hjoin [Howned Hframe]]]].
      exists owned, rest. split; [exact Hjoin|].
      split; [exact (Hpre arguments owned Howned)|exact Hframe].
    + exact Hrun.
Qed.

(** The explicit construction entrance.  [evidence] must come from the
    caller's proved source/CSL/critical contract.  Neither a pointer type,
    a lookup alone nor a relation named "authorized" satisfies it. *)
Lemma func_ptr_hoare_from_source_evidence (signature : FuncSig)
  (environment : callback_environment) (pointer : Z) (body : FunSem signature)
  (P : ParamTuple (fst signature) -> Rules.expr)
  (Q : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr) :
  pointer <> 0%Z ->
  source_functions environment signature pointer = Some body ->
  callback_source_evidence environment signature body P Q ->
  forall state : Old.model,
    func_ptr_spec pointer (HoareFun signature P Q) (state, environment).
Proof.
  intros Hnonzero Hlookup evidence state.
  split; [exact Hnonzero |]. exists body. split; assumption.
Qed.

Definition source_call_normal {signature : FuncSig}
  (environment : callback_environment) (pointer : Z)
  (arguments : ParamTuple (fst signature))
  (initial : Mem.mem) (result : RetType (snd signature)) (final : Mem.mem) : Prop :=
  pointer <> 0%Z /\ exists body,
    source_functions environment signature pointer = Some body /\
    MonadErr.nrm (body arguments) initial result final.

Definition source_call_error {signature : FuncSig}
  (environment : callback_environment) (pointer : Z)
  (arguments : ParamTuple (fst signature)) (initial : Mem.mem) : Prop :=
  pointer = 0%Z \/ source_functions environment signature pointer = None \/
  exists body, source_functions environment signature pointer = Some body /\
    MonadErr.err (body arguments) initial.

Definition indirect_call {signature : FuncSig} (pointer : Z)
  (arguments : ParamTuple (fst signature))
  : MonadErr.M Rules.model (RetType (snd signature)) :=
  {| MonadErr.nrm := fun initial result final =>
       snd final = snd initial /\ pointer <> 0%Z /\ exists body,
         source_functions (snd initial) signature pointer = Some body /\
         MonadErr.nrm (resource_execution (snd initial) body arguments)
           (fst initial) result (fst final);
     MonadErr.err := fun initial =>
       source_call_error (snd initial) pointer arguments
         (fst initial).(ConAssertion.s_mem) |}.

Lemma indirect_call_preserves_environment {signature : FuncSig} (pointer : Z)
  (arguments : ParamTuple (fst signature)) (initial final : Rules.model)
  (result : RetType (snd signature)) :
  MonadErr.nrm (indirect_call pointer arguments) initial result final ->
  snd final = snd initial.
Proof. intros [Henv Hrest]. exact Henv. Qed.

Lemma indirect_call_normal_source {signature : FuncSig} (pointer : Z)
  (arguments : ParamTuple (fst signature)) (initial final : Rules.model)
  (result : RetType (snd signature)) :
  MonadErr.nrm (indirect_call pointer arguments) initial result final ->
  source_call_normal (snd initial) pointer arguments
    (fst initial).(ConAssertion.s_mem) result (fst final).(ConAssertion.s_mem).
Proof.
  intros [Henv [Hnonzero [body [Hlookup [Hnormal Hresource]]]]].
  split; [exact Hnonzero |]. exists body. split; assumption.
Qed.

Lemma indirect_call_error_source_iff {signature : FuncSig} (pointer : Z)
  (arguments : ParamTuple (fst signature)) (initial : Rules.model) :
  MonadErr.err (indirect_call pointer arguments) initial <->
  source_call_error (snd initial) pointer arguments
    (fst initial).(ConAssertion.s_mem).
Proof. split; intro H; exact H. Qed.

Definition call_pre {signature : FuncSig} (pointer : Z)
  (arguments : ParamTuple (fst signature))
  (P : ParamTuple (fst signature) -> Rules.expr)
  (Q : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr)
  (frame : Rules.expr) : Rules.expr :=
  Rules.andp (Rules.sepcon (P arguments) frame)
    (func_ptr_spec pointer (HoareFun signature P Q)).

Definition call_post {signature : FuncSig} (pointer : Z)
  (arguments : ParamTuple (fst signature))
  (P : ParamTuple (fst signature) -> Rules.expr)
  (Q : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr)
  (frame : Rules.expr) (result : RetType (snd signature)) : Rules.expr :=
  Rules.andp (Rules.sepcon (Q arguments result) frame)
    (func_ptr_spec pointer (HoareFun signature P Q)).

Lemma indirect_call_hoare {signature : FuncSig} (pointer : Z)
  (arguments : ParamTuple (fst signature))
  (P : ParamTuple (fst signature) -> Rules.expr)
  (Q : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr)
  (frame : Rules.expr) :
  MonadErrHoare.Hoare (call_pre pointer arguments P Q frame)
    (indirect_call pointer arguments) (call_post pointer arguments P Q frame).
Proof.
  split.
  - intros result [initial environment] [final final_environment]
      [HP Hcap] Hrun.
    destruct Hcap as [Hnonzero [body [Hlookup evidence]]].
    change (source_functions environment signature pointer = Some body) in Hlookup.
    destruct Hrun as [Henv [Hnonnull [called [Hcalled Hresource]]]].
    change (final_environment = environment) in Henv.
    subst final_environment.
    change (source_functions environment signature pointer = Some called) in Hcalled.
    rewrite Hlookup in Hcalled. injection Hcalled as Hbody. subst called.
    destruct evidence as [Hhoare Hcoverage].
    split.
    + exact (proj1 (Hhoare arguments frame) result initial final HP Hresource).
    + split; [exact Hnonzero |]. exists body. split; [exact Hlookup |].
      constructor; assumption.
  - intros [initial environment] [HP Hcap] Herr.
    destruct Hcap as [Hnonzero [body [Hlookup evidence]]].
    change (source_functions environment signature pointer = Some body) in Hlookup.
    destruct evidence as [Hhoare Hcoverage].
    destruct Herr as [Hzero | [Hmissing | [called [Hcalled Herror]]]].
    + exact (Hnonzero Hzero).
    + change (source_functions environment signature pointer = None) in Hmissing.
      rewrite Hlookup in Hmissing. discriminate.
    + change (source_functions environment signature pointer = Some called) in Hcalled.
      rewrite Hlookup in Hcalled. injection Hcalled as Hbody. subst called.
      exact (proj2 (Hhoare arguments frame) initial HP Herror).
Qed.

(** This theorem consumes the positive coverage field.  It starts with an
    arbitrary actual source outcome, not a preselected resource execution.
    The same environment, source result, final bytes, caller protocol and
    disjoint frame are all retained in the conclusion. *)
Lemma indirect_call_covers_source_outcomes {signature : FuncSig} (pointer : Z)
  (arguments : ParamTuple (fst signature))
  (P : ParamTuple (fst signature) -> Rules.expr)
  (Q : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr)
  (frame : Rules.expr) (initial : Rules.model)
  (result : RetType (snd signature)) (final_memory : Mem.mem) :
  call_pre pointer arguments P Q frame initial ->
  source_call_normal (snd initial) pointer arguments
    (fst initial).(ConAssertion.s_mem) result final_memory ->
  exists final : Rules.model,
    MonadErr.nrm (indirect_call pointer arguments) initial result final /\
    (fst final).(ConAssertion.s_mem) = final_memory /\
    call_post pointer arguments P Q frame result final.
Proof.
  destruct initial as [initial environment].
  intros [HP Hcap] [Hnonnull [called [Hcalled Hsource]]].
  destruct Hcap as [Hnonzero [body [Hlookup evidence]]].
  change (source_functions environment signature pointer = Some body) in Hlookup.
  change (source_functions environment signature pointer = Some called) in Hcalled.
  rewrite Hlookup in Hcalled. injection Hcalled as Hbody. subst called.
  destruct evidence as [Hhoare Hcoverage].
  destruct (Hcoverage arguments frame initial result final_memory HP Hsource)
    as [final [Hmemory Hprotocol]].
  assert (Hresource : MonadErr.nrm
    (resource_execution environment body arguments) initial result final).
  { split.
    - rewrite Hmemory. exact Hsource.
    - exact Hprotocol. }
  exists (final, environment). split.
  - split; [reflexivity |]. split; [exact Hnonzero |].
    exists body. split; assumption.
  - split; [exact Hmemory |]. split.
    + exact (proj1 (Hhoare arguments frame) result initial final HP Hresource).
    + split; [exact Hnonzero |]. exists body. split; [exact Hlookup |].
      constructor; assumption.
Qed.

(** The public call rule intentionally packages BOTH directions needed at
    the C call boundary: resource Hoare safety and complete source coverage.
    Consumers must not use the forward projection lemma as a replacement. *)
Theorem indirect_call_rule {signature : FuncSig} (pointer : Z)
  (arguments : ParamTuple (fst signature))
  (P : ParamTuple (fst signature) -> Rules.expr)
  (Q : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr)
  (frame : Rules.expr) :
  MonadErrHoare.Hoare (call_pre pointer arguments P Q frame)
    (indirect_call pointer arguments) (call_post pointer arguments P Q frame) /\
  (forall initial result final_memory,
    call_pre pointer arguments P Q frame initial ->
    source_call_normal (snd initial) pointer arguments
      (fst initial).(ConAssertion.s_mem) result final_memory ->
    exists final : Rules.model,
      MonadErr.nrm (indirect_call pointer arguments) initial result final /\
      (fst final).(ConAssertion.s_mem) = final_memory /\
      call_post pointer arguments P Q frame result final).
Proof.
  split.
  - apply indirect_call_hoare.
  - intros initial result final_memory.
    apply indirect_call_covers_source_outcomes.
Qed.

(** The generated contract can quantify over several ghost values before
    reaching HoareFun.  Its complete capability is retained across the call;
    [instantiate] selects the actual proved pre/post instance.  Both the
    normal/error rule and positive coverage are inherited from the rule
    above, so quantifier instantiation cannot hide a source outcome. *)
Definition specified_call_pre {signature : FuncSig} (pointer : Z)
  (arguments : ParamTuple (fst signature)) (specification : Spec signature)
  (P : ParamTuple (fst signature) -> Rules.expr) (frame : Rules.expr) : Rules.expr :=
  Rules.andp (Rules.sepcon (P arguments) frame) (func_ptr_spec pointer specification).

Definition specified_call_post {signature : FuncSig} (pointer : Z)
  (arguments : ParamTuple (fst signature)) (specification : Spec signature)
  (Q : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr)
  (frame : Rules.expr) (result : RetType (snd signature)) : Rules.expr :=
  Rules.andp (Rules.sepcon (Q arguments result) frame) (func_ptr_spec pointer specification).

Theorem indirect_call_specification_rule {signature : FuncSig} (pointer : Z)
  (arguments : ParamTuple (fst signature)) (specification : Spec signature)
  (P : ParamTuple (fst signature) -> Rules.expr)
  (Q : ParamTuple (fst signature) -> RetType (snd signature) -> Rules.expr)
  (frame : Rules.expr) :
  specification_environment_only specification ->
  (forall body, Rules.derivable1 (specification body) (HoareFun signature P Q body)) ->
  MonadErrHoare.Hoare (specified_call_pre pointer arguments specification P frame)
    (indirect_call pointer arguments)
    (specified_call_post pointer arguments specification Q frame) /\
  (forall initial result final_memory,
    specified_call_pre pointer arguments specification P frame initial ->
    source_call_normal (snd initial) pointer arguments
      (fst initial).(ConAssertion.s_mem) result final_memory ->
    exists final : Rules.model,
      MonadErr.nrm (indirect_call pointer arguments) initial result final /\
      (fst final).(ConAssertion.s_mem) = final_memory /\
      specified_call_post pointer arguments specification Q frame result final).
Proof.
  intros Honly Hinstantiate.
  pose proof (func_ptr_spec_mono pointer specification (HoareFun signature P Q)
    Hinstantiate) as Hselect.
  destruct (indirect_call_rule pointer arguments P Q frame) as [Hhoare Hcoverage].
  split.
  - split.
    + intros result initial final [HP Hcap] Hrun.
      destruct (proj1 Hhoare result initial final
        (conj HP (Hselect initial Hcap)) Hrun) as [HQ Hselected].
      split; [exact HQ|].
      apply (func_ptr_spec_environment_eq pointer specification Honly initial final).
      * symmetry. exact (indirect_call_preserves_environment pointer arguments
          initial final result Hrun).
      * exact Hcap.
    + intros initial [HP Hcap] Herr.
      exact (proj2 Hhoare initial (conj HP (Hselect initial Hcap)) Herr).
  - intros initial result final_memory [HP Hcap] Hsource.
    destruct (Hcoverage initial result final_memory
      (conj HP (Hselect initial Hcap)) Hsource)
      as [final [Hrun [Hmemory [HQ Hselected]]]].
    exists final. split; [exact Hrun|]. split; [exact Hmemory|].
    split; [exact HQ|].
    apply (func_ptr_spec_environment_eq pointer specification Honly initial final).
    + symmetry. exact (indirect_call_preserves_environment pointer arguments
        initial final result Hrun).
    + exact Hcap.
Qed.

End TimerCallback_C_Rules.
