Require Import Coq.ZArith.ZArith.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_call_api_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_call_api_program_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_unlink_spec.
Require Import Ucos2Verify.VC.code.timer.spec.timer_callback_semantics.

(** Assertion interfaces for the unchanged Lock, Unlock and Unlink callees.
    The wrappers retain the existing old Lstate and its actual storage,
    region, stack and scheduler predicates.  In particular they introduce no
    replacement address or layout constants.

    These are assertion consequences, not whole-C Hoare theorems.  Reusing
    an old witness requires the corresponding freshly generated obligation
    to reduce, for every environment slice, to that old witness.  The source,
    selected 32-bit little-endian configuration, full target set and external
    CPU/CSL contracts must still be checked at that integration boundary. *)

Module TimerCalleeLift.

Module Old := UCOS2_C_Rules.
Module New := TimerCallback_C_Rules.Rules.

Module OldConsequences.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma os_sched_lock_program_post_closed_return : forall platform critical sg
  invocation origin mask before X,
  os_sched_lock_program_post platform critical sg invocation origin mask before X |--
  EX entry, EX final,
    coq_prop (os_sched_lock_call_relation critical sg invocation before entry final /\ X final) &&
    mutex_query_closed platform critical sg invocation origin mask final.
Proof.
  intros platform critical sg invocation origin mask before X heap
    [entry [final [[Hcall [Hvalid HX]] Hresources]]].
  exists entry, final. split; [exact (conj Hcall HX)|].
  exact (proj1 (os_sched_lock_pre_closed_equiv platform critical sg invocation
    origin mask final) heap (conj Hvalid Hresources)).
Qed.

Definition os_sched_unlock_return_resources
  (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (calling_context returned_context : OsSchedCallContext) (mask : Z)
  (final : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform calling_context.(os_sched_call_invocation)
    calling_context.(os_sched_call_origin) mask **
  critical_region_outside critical sg calling_context.(os_sched_call_invocation) final **
  os_sched_context_resources external returned_context ** unmap_table_rep sg.

Lemma os_sched_c_return_context_fields : forall external critical sg entry
  context returned final,
  os_sched_c_return external critical sg entry context returned final ->
  returned.(os_sched_call_invocation) = context.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = context.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = context.(os_sched_call_stack).
Proof.
  intros external critical sg entry context returned final Hreturn.
  unfold os_sched_c_return in Hreturn.
  destruct (os_sched_requests_switch entry).
  - destruct Hreturn as [installed [Hsource Hreturn]].
    cbn in Hreturn. tauto.
  - destruct Hreturn as [-> Hfinal]. repeat split; reflexivity.
Qed.

Lemma os_sched_unlock_call_relation_context_fields : forall external critical
  sg context before returned final,
  os_sched_unlock_call_relation external critical sg context before returned final ->
  returned.(os_sched_call_invocation) = context.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = context.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = context.(os_sched_call_stack).
Proof.
  intros external critical sg context before returned final Hreturn.
  destruct Hreturn as [[Hrunning [-> Hfinal]]|
    [entry [Hrunning [Hinterval Hreturn]]]].
  - repeat split; reflexivity.
  - destruct (os_sched_unlock_requests entry).
    + destruct Hreturn as [acquired [Hacquired Hreturn]].
      eapply os_sched_c_return_context_fields; exact Hreturn.
    + destruct Hreturn as [-> Hfinal]. repeat split; reflexivity.
Qed.

Lemma os_sched_c_return_preserves_validity : forall external critical sg entry
  context returned final,
  UCOS2_state_inv sg entry ->
  (os_sched_requests_switch entry = true ->
    os_sched_switch_input external sg context entry) ->
  os_sched_c_return external critical sg entry context returned final ->
  UCOS2_state_inv sg final.
Proof.
  intros external critical sg entry context returned final Hvalid Hinput Hreturn.
  pose proof (os_sched_ready_checkpoint_preserves_validity sg entry Hvalid)
    as Hprefix.
  unfold os_sched_c_return in Hreturn.
  destruct (os_sched_requests_switch entry) eqn:Hswitch.
  - exact (os_sched_switch_outcome_preserves_validity external critical sg
      entry context (OsSchedOriginalResumed returned final)
      Hprefix (Hinput eq_refl) Hreturn).
  - destruct Hreturn as [Hcontext ->]. exact Hprefix.
Qed.

Lemma os_sched_unlock_program_post_return : forall external platform critical
  sg context mask before X,
  os_sched_unlock_program_post external platform critical sg context mask before X |--
  EX returned, EX final,
    coq_prop (os_sched_unlock_call_relation external critical sg context before
      returned final /\ X final) &&
    os_sched_unlock_return_resources external platform critical sg context returned mask final.
Proof.
  intros external platform critical sg context mask before X heap Hpost.
  destruct Hpost as [[[Hrunning [Hvalid HX]] Hresources]|
    [entry [[Hrunning [Hinterval Hvalid]] Hresources]]].
  - exists context, before. split.
    + split; [left; repeat split; assumption || reflexivity|exact HX].
    + exact (proj2 (os_sched_unlock_outside_frame_split_running external
        platform critical sg context mask before) heap Hresources).
  - destruct (os_sched_unlock_requests entry) eqn:Hrequest.
    + destruct Hresources as [acquired [final [returned
        [[Hacquired [Hreturn HX]] Hresources]]]].
      exists returned, final. split; [|exact Hresources].
      split; [|exact HX]. right; exists entry.
      split; [exact Hrunning|]. split; [exact Hinterval|]. rewrite Hrequest.
      exists acquired; exact (conj Hacquired Hreturn).
    + destruct Hresources as [HX Hresources].
      exists context, (os_sched_unlock_checkpoint true entry).
      split; [|exact Hresources]. split; [|exact HX].
      right; exists entry. split; [exact Hrunning|].
      split; [exact Hinterval|]. rewrite Hrequest. split; reflexivity.
Qed.

(** The original precondition supplies this safety fact.  The scheduled
    branch uses its own acquired state; it is never identified with the
    decrement checkpoint.  These are consequences of the existing source
    relations, not additional requirements on all Timer callbacks. *)
Lemma os_sched_unlock_program_post_return_valid : forall external platform
  critical sg context mask before X,
  os_sched_unlock_acquire_safety external critical sg context before ->
  os_sched_unlock_program_post external platform critical sg context mask before X |--
  EX returned, EX final,
    coq_prop (os_sched_unlock_call_relation external critical sg context before
      returned final /\ UCOS2_state_inv sg final /\ X final) &&
    os_sched_unlock_return_resources external platform critical sg context returned mask final.
Proof.
  intros external platform critical sg context mask before X Hsafe heap Hpost.
  destruct Hpost as [[[Hrunning [Hvalid HX]] Hresources]|
    [entry [[Hrunning [Hinterval Hvalid]] Hresources]]].
  - exists context, before. split.
    + split; [left; repeat split; assumption || reflexivity|].
      exact (conj Hvalid HX).
    + exact (proj2 (os_sched_unlock_outside_frame_split_running external
        platform critical sg context mask before) heap Hresources).
  - destruct (os_sched_unlock_requests entry) eqn:Hrequest.
    + destruct Hresources as [acquired [final [returned
        [[Hacquired [Hreturn HX]] Hresources]]]].
      pose proof (Hsafe Hrunning entry Hinterval Hrequest) as Hacquire_safety.
      pose proof (proj1 (critical_region_interval_transports_resources
        critical sg context.(os_sched_call_invocation)
        (os_sched_unlock_checkpoint true entry) acquired Hacquired Hvalid))
        as Hacquired_valid.
      pose proof (os_sched_c_return_preserves_validity external critical sg
        acquired context returned final Hacquired_valid
        (proj2 (Hacquire_safety acquired Hacquired)) Hreturn) as Hfinal_valid.
      exists returned, final. split; [|exact Hresources].
      split; [|exact (conj Hfinal_valid HX)]. right; exists entry.
      split; [exact Hrunning|]. split; [exact Hinterval|]. rewrite Hrequest.
      exists acquired; exact (conj Hacquired Hreturn).
    + destruct Hresources as [HX Hresources].
      exists context, (os_sched_unlock_checkpoint true entry).
      split; [|exact Hresources]. split; [|exact (conj Hvalid HX)].
      right; exists entry. split; [exact Hrunning|].
      split; [exact Hinterval|]. rewrite Hrequest. split; reflexivity.
Qed.

Lemma os_sched_unlock_program_post_closed_return : forall external platform
  critical sg context mask before X,
  os_sched_unlock_acquire_safety external critical sg context before ->
  os_sched_unlock_program_post external platform critical sg context mask before X |--
  EX returned, EX final,
    coq_prop (os_sched_unlock_call_relation external critical sg context before
      returned final /\ X final) &&
    (mutex_query_closed platform critical sg returned.(os_sched_call_invocation)
       returned.(os_sched_call_origin) mask final **
     (os_sched_context_resources external returned ** unmap_table_rep sg)).
Proof.
  intros external platform critical sg context mask before X Hsafe heap Hpost.
  destruct (os_sched_unlock_program_post_return_valid external platform
    critical sg context mask before X Hsafe heap Hpost)
    as [returned [final [[Hreturn [Hvalid HX]] Hresources]]].
  exists returned, final. split; [exact (conj Hreturn HX)|].
  destruct (os_sched_unlock_call_relation_context_fields external critical sg
    context before returned final Hreturn) as [Hinvocation [Horigin Hstack]].
  destruct Hresources as [prefix [unmap [Hwhole [Hprefix Hunmap]]]].
  destruct Hprefix as [closed [caller [Hprefix [Hclosed Hcaller]]]].
  destruct (Old.join_assoc closed caller unmap prefix heap Hprefix Hwhole)
    as [tail [Htail Hjoined]].
  exists closed, tail. split; [exact Hjoined|]. split.
  - unfold mutex_query_closed. rewrite Hinvocation, Horigin.
    exact (conj Hvalid Hclosed).
  - exists caller, unmap. split; [exact Htail|]. split; assumption.
Qed.

End OldConsequences.

(** These names can be imported by the C annotation's product-rule module.
    Each right-hand side is an explicit lift of the current old predicate. *)
Definition mutex_query_closed platform critical sg invocation origin mask state :=
  New.lift (mutex_query_spec.mutex_query_closed platform critical sg invocation origin mask state).
Definition os_sched_context_resources external context :=
  New.lift (sched_spec.os_sched_context_resources external context).
Definition unmap_table_rep sg := New.lift (sched.unmap_table_rep sg).
Definition timer_inv sg state := New.lift (timer.timer_inv sg state).
Definition UCOS2_inv sg state := New.lift (ucos2_verify_inv.UCOS2_inv sg state).
Definition UCOS2_raw_rep_missing_interrupt sg state :=
  New.lift (ucos2_spatial.UCOS2_raw_rep_missing_interrupt sg state).

Definition os_sched_lock_outside_frame platform critical sg invocation origin mask state :=
  New.lift (sched_lock_call_spec.os_sched_lock_outside_frame platform critical sg invocation origin mask state).
Definition os_sched_lock_inside_frame platform critical sg invocation origin saved entry :=
  New.lift (sched_lock_call_spec.os_sched_lock_inside_frame platform critical sg invocation origin saved entry).
Definition os_sched_lock_pre platform critical sg invocation origin mask before :=
  New.lift (sched_lock_call_spec.os_sched_lock_pre platform critical sg invocation origin mask before).
Definition os_sched_lock_post platform critical sg invocation origin mask before :=
  New.lift (sched_lock_call_spec.os_sched_lock_post platform critical sg invocation origin mask before).
Definition os_sched_lock_program_pre platform critical sg invocation origin mask before X :=
  New.lift (sched_lock_call_api_program_spec.os_sched_lock_program_pre
    platform critical sg invocation origin mask before X).
Definition os_sched_lock_program_post platform critical sg invocation origin mask before X :=
  New.lift (sched_lock_call_api_program_spec.os_sched_lock_program_post
    platform critical sg invocation origin mask before X).

Definition os_sched_unlock_outside_frame external platform critical sg context mask state :=
  New.lift (sched_unlock_call_spec.os_sched_unlock_outside_frame external platform critical sg context mask state).
Definition os_sched_unlock_inside_frame external platform critical sg context saved entry :=
  New.lift (sched_unlock_call_spec.os_sched_unlock_inside_frame external platform critical sg context saved entry).
Definition os_sched_unlock_observation_frame external platform critical sg context mask state :=
  New.lift (sched_unlock_call_spec.os_sched_unlock_observation_frame external platform critical sg context mask state).
Definition os_sched_unlock_pre external platform critical sg context mask before :=
  New.lift (sched_unlock_call_spec.os_sched_unlock_pre external platform critical sg context mask before).
Definition os_sched_unlock_post external platform critical sg context mask before :=
  New.lift (sched_unlock_call_spec.os_sched_unlock_post external platform critical sg context mask before).
Definition os_sched_unlock_program_pre external platform critical sg context mask before X :=
  New.lift (sched_unlock_call_api_program_spec.os_sched_unlock_program_pre
    external platform critical sg context mask before X).
Definition os_sched_unlock_program_post external platform critical sg context mask before X :=
  New.lift (sched_unlock_call_api_program_spec.os_sched_unlock_program_post
    external platform critical sg context mask before X).
Definition os_sched_unlock_return_resources external platform critical sg
  calling_context returned_context mask final :=
  New.lift (OldConsequences.os_sched_unlock_return_resources external platform
    critical sg calling_context returned_context mask final).

Definition tmr_unlink_configured_post sg state index :=
  New.lift (tmr_unlink_spec.tmr_unlink_configured_post sg state index).
Definition tmr_unlink_neighbor_pre pointer next previous first :=
  New.lift (tmr_unlink_spec.tmr_unlink_neighbor_pre pointer next previous first).
Definition tmr_unlink_neighbor_post pointer next previous first :=
  New.lift (tmr_unlink_spec.tmr_unlink_neighbor_post pointer next previous first).

(** An assertion-valued callee parameter, such as Unlink's residual R,
    may depend on the shared environment.  Slicing that parameter preserves
    it rather than restricting it to a lift of an old heap-only assertion. *)
Definition lift_frame_contract (contract : Old.expr -> Old.expr)
  (frame : New.expr) : New.expr :=
  fun state => contract (New.slice (snd state) frame) (fst state).

Definition tmr_unlink_raw_pre pointer base match_time next previous first entries frame :=
  lift_frame_contract
    (tmr_unlink_spec.tmr_unlink_raw_pre pointer base match_time next previous first entries) frame.
Definition tmr_unlink_raw_post pointer base match_time next previous first entries frame :=
  lift_frame_contract
    (tmr_unlink_spec.tmr_unlink_raw_post pointer base match_time next previous first entries) frame.

Lemma lift_slice : forall environment assertion state,
  New.slice environment (New.lift assertion) state <-> assertion state.
Proof. intros; reflexivity. Qed.

Lemma entailment_from_slices : forall P Q,
  (forall environment, Old.derivable1 (New.slice environment P) (New.slice environment Q)) ->
  New.derivable1 P Q.
Proof. intros P Q Hslices [state environment] HP; exact (Hslices environment state HP). Qed.

Lemma framed_lift_entailment : forall P Q frame,
  Old.derivable1 P Q ->
  New.derivable1 (New.sepcon (New.lift P) frame) (New.sepcon (New.lift Q) frame).
Proof.
  intros P Q frame Hentails state [first [second [Hjoin [HP Hframe]]]].
  exists first, second. split; [exact Hjoin|].
  split; [exact (New.lift_entailment P Q Hentails first HP)|exact Hframe].
Qed.

Lemma slice_lift_frame_contract : forall contract frame environment state,
  New.slice environment (lift_frame_contract contract frame) state <->
  contract (New.slice environment frame) state.
Proof. intros; reflexivity. Qed.

Lemma lift_frame_contract_lift : forall contract frame,
  New.logic_equiv (lift_frame_contract contract (New.lift frame)) (New.lift (contract frame)).
Proof. intros; split; intros [state environment] H; exact H. Qed.

Lemma lift_frame_contract_entailment : forall first second frame,
  (forall old_frame, Old.derivable1 (first old_frame) (second old_frame)) ->
  New.derivable1 (lift_frame_contract first frame) (lift_frame_contract second frame).
Proof.
  intros first second frame Hentails [state environment] Hpre.
  exact (Hentails (New.slice environment frame) state Hpre).
Qed.

Lemma tmr_unlink_raw_pre_slice : forall pointer base match_time next previous
  first entries frame environment state,
  New.slice environment
    (tmr_unlink_raw_pre pointer base match_time next previous first entries frame) state <->
  tmr_unlink_spec.tmr_unlink_raw_pre pointer base match_time next previous first
    entries (New.slice environment frame) state.
Proof. intros; reflexivity. Qed.

Lemma tmr_unlink_raw_post_slice : forall pointer base match_time next previous
  first entries frame environment state,
  New.slice environment
    (tmr_unlink_raw_post pointer base match_time next previous first entries frame) state <->
  tmr_unlink_spec.tmr_unlink_raw_post pointer base match_time next previous first
    entries (New.slice environment frame) state.
Proof. intros; reflexivity. Qed.

Lemma tmr_unlink_configured_post_slice : forall sg timers index environment state,
  New.slice environment (tmr_unlink_configured_post sg timers index) state <->
  tmr_unlink_spec.tmr_unlink_configured_post sg timers index state.
Proof. intros; reflexivity. Qed.

Lemma os_sched_lock_program_pre_open : forall platform critical sg invocation
  origin mask before X frame,
  New.derivable1
    (New.sepcon (os_sched_lock_program_pre platform critical sg invocation origin mask before X) frame)
    (New.sepcon (New.andp (New.coq_prop
      (os_sched_lock_continuation critical sg invocation before X))
      (os_sched_lock_pre platform critical sg invocation origin mask before)) frame).
Proof.
  intros platform critical sg invocation origin mask before X frame state
    [first [second [Hjoin [Hpre Hframe]]]].
  exists first, second. split; [exact Hjoin|]. split; [|exact Hframe].
  exact (sched_lock_call_api_program_spec.os_sched_lock_program_pre_open
    platform critical sg invocation origin mask before X (fst first) Hpre).
Qed.

Lemma os_sched_lock_post_program_post : forall platform critical sg invocation
  origin mask before X frame,
  os_sched_lock_continuation critical sg invocation before X ->
  New.derivable1
    (New.sepcon (os_sched_lock_post platform critical sg invocation origin mask before) frame)
    (New.sepcon (os_sched_lock_program_post platform critical sg invocation origin mask before X) frame).
Proof.
  intros platform critical sg invocation origin mask before X frame Hcontinuation
    state [first [second [Hjoin [Hpost Hframe]]]].
  exists first, second. split; [exact Hjoin|]. split; [|exact Hframe].
  exact (sched_lock_call_api_program_spec.os_sched_lock_post_program_post
    platform critical sg invocation origin mask before X Hcontinuation
    (fst first) Hpost).
Qed.

Lemma os_sched_unlock_program_pre_open : forall external platform critical sg
  context mask before X frame,
  New.derivable1
    (New.sepcon (os_sched_unlock_program_pre external platform critical sg context mask before X) frame)
    (New.sepcon (New.andp (New.coq_prop
      (os_sched_unlock_continuation external critical sg context before X))
      (os_sched_unlock_pre external platform critical sg context mask before)) frame).
Proof.
  intros external platform critical sg context mask before X frame state
    [first [second [Hjoin [Hpre Hframe]]]].
  exists first, second. split; [exact Hjoin|]. split; [|exact Hframe].
  exact (sched_unlock_call_api_program_spec.os_sched_unlock_program_pre_open
    external platform critical sg context mask before X (fst first) Hpre).
Qed.

Lemma os_sched_unlock_post_program_post : forall external platform critical sg
  context mask before X frame,
  os_sched_unlock_continuation external critical sg context before X ->
  New.derivable1
    (New.sepcon (os_sched_unlock_post external platform critical sg context mask before) frame)
    (New.sepcon (os_sched_unlock_program_post external platform critical sg context mask before X) frame).
Proof.
  intros external platform critical sg context mask before X frame Hcontinuation
    state [first [second [Hjoin [Hpost Hframe]]]].
  exists first, second. split; [exact Hjoin|]. split; [|exact Hframe].
  exact (sched_unlock_call_api_program_spec.os_sched_unlock_post_program_post
    external platform critical sg context mask before X Hcontinuation
    (fst first) Hpost).
Qed.

Lemma os_sched_unlock_program_post_base : forall external platform critical sg
  context mask before X frame,
  New.derivable1
    (New.sepcon (os_sched_unlock_program_post external platform critical sg context mask before X) frame)
    (New.sepcon (os_sched_unlock_post external platform critical sg context mask before) frame).
Proof.
  intros external platform critical sg context mask before X frame state
    [first [second [Hjoin [Hpost Hframe]]]].
  exists first, second. split; [exact Hjoin|]. split; [|exact Hframe].
  exact (sched_unlock_call_api_program_spec.os_sched_unlock_program_post_base
    external platform critical sg context mask before X (fst first) Hpost).
Qed.

Lemma os_sched_unlock_call_relation_context_fields : forall external critical
  sg context before returned final,
  os_sched_unlock_call_relation external critical sg context before returned final ->
  returned.(os_sched_call_invocation) = context.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = context.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = context.(os_sched_call_stack).
Proof. exact OldConsequences.os_sched_unlock_call_relation_context_fields. Qed.

Lemma os_sched_lock_program_post_closed_return : forall platform critical sg
  invocation origin mask before X,
  New.derivable1
    (os_sched_lock_program_post platform critical sg invocation origin mask before X)
    (New.exp (fun entry => New.exp (fun final =>
      New.andp (New.coq_prop
        (os_sched_lock_call_relation critical sg invocation before entry final /\ X final))
      (mutex_query_closed platform critical sg invocation origin mask final)))).
Proof.
  intros platform critical sg invocation origin mask before X [state environment] Hpost.
  exact (OldConsequences.os_sched_lock_program_post_closed_return platform
    critical sg invocation origin mask before X state Hpost).
Qed.

Lemma os_sched_unlock_program_post_return : forall external platform critical
  sg context mask before X,
  New.derivable1
    (os_sched_unlock_program_post external platform critical sg context mask before X)
    (New.exp (fun returned => New.exp (fun final =>
      New.andp (New.coq_prop
        (os_sched_unlock_call_relation external critical sg context before returned final /\ X final))
      (os_sched_unlock_return_resources external platform critical sg context returned mask final)))).
Proof.
  intros external platform critical sg context mask before X [state environment] Hpost.
  exact (OldConsequences.os_sched_unlock_program_post_return external platform
    critical sg context mask before X state Hpost).
Qed.

Lemma os_sched_closed_resources_lift : forall external platform critical sg
  context mask state,
  New.logic_equiv
    (New.sepcon
      (mutex_query_closed platform critical sg context.(os_sched_call_invocation)
        context.(os_sched_call_origin) mask state)
      (New.sepcon (os_sched_context_resources external context) (unmap_table_rep sg)))
    (New.lift (Old.sepcon
      (mutex_query_spec.mutex_query_closed platform critical sg context.(os_sched_call_invocation)
        context.(os_sched_call_origin) mask state)
      (Old.sepcon (sched_spec.os_sched_context_resources external context) (sched.unmap_table_rep sg)))).
Proof.
  intros; apply New.slices_imply_lift_equiv; intros environment heap.
  apply New.slice_sepcon_preserves.
  - intro; reflexivity.
  - apply New.slice_sepcon_preserves; intro; reflexivity.
Qed.

Lemma os_sched_unlock_program_post_closed_return : forall external platform
  critical sg context mask before X,
  os_sched_unlock_acquire_safety external critical sg context before ->
  New.derivable1
    (os_sched_unlock_program_post external platform critical sg context mask before X)
    (New.exp (fun returned => New.exp (fun final =>
      New.andp (New.coq_prop
        (os_sched_unlock_call_relation external critical sg context before returned final /\ X final))
      (New.sepcon
        (mutex_query_closed platform critical sg returned.(os_sched_call_invocation)
          returned.(os_sched_call_origin) mask final)
        (New.sepcon (os_sched_context_resources external returned) (unmap_table_rep sg)))))).
Proof.
  intros external platform critical sg context mask before X Hsafe [state environment] Hpost.
  destruct (OldConsequences.os_sched_unlock_program_post_closed_return external
    platform critical sg context mask before X Hsafe state Hpost)
    as [returned [final [Hreturn Hresources]]].
  exists returned, final; split; [exact Hreturn|].
  exact (proj2 (os_sched_closed_resources_lift external platform critical sg
    returned mask final) (state, environment) Hresources).
Qed.

End TimerCalleeLift.
