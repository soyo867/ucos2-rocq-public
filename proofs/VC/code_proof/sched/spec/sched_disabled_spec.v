Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Psatz.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition sched_disabled_addresses (sg : StableGlobVars)
  (ints locks : Z) : Prop :=
  ints = sg.(g_OSIntNesting) /\ locks = sg.(g_OSLockNesting).

Definition sched_disabled_isr_source (view : OsExecutionView)
  (state : UCOS2_Verify_State) : Prop :=
  exists handler interrupted,
    view.(os_execution_context) = KernelInterrupt handler interrupted /\
    state.(SchedState).(isRunning) = true /\
    kernel_interrupt_nesting_agrees true view.(os_execution_context) state.(IntrState).

Definition sched_disabled_entry_source (view : OsExecutionView)
  (state : UCOS2_Verify_State) : Prop :=
  sched_disabled_isr_source view state \/ 0 < state.(IntrState).(lockNesting).

(** An explicit C completed-segment rely. Each existing reason is preserved
    separately, including when both reasons hold. This is neither a CPU law
    nor an admission theorem for the elementary Enter/Exit registry. *)
Definition sched_disabled_context_rely (view : OsExecutionView)
  (_ : StableGlobVars) (before after : UCOS2_Verify_State) : Prop :=
  (sched_disabled_isr_source view before -> sched_disabled_isr_source view after) /\
  (0 < before.(IntrState).(lockNesting) -> 0 < after.(IntrState).(lockNesting)).

Definition sched_disabled_completed_clients
  (critical : CriticalRegionResources) (view : OsExecutionView) : Prop :=
  forall action, critical_region_clients critical action ->
  forall sg before after,
    UCOS2_state_inv sg before -> kernel_client_step action sg before after ->
    sched_disabled_context_rely view sg before after.

Lemma sched_disabled_context_rely_refl : forall view sg state,
  sched_disabled_context_rely view sg state state.
Proof. unfold sched_disabled_context_rely; auto. Qed.

Lemma sched_disabled_context_rely_trans : forall view sg before middle after,
  sched_disabled_context_rely view sg before middle ->
  sched_disabled_context_rely view sg middle after ->
  sched_disabled_context_rely view sg before after.
Proof.
  intros view sg before middle after [Hisr_first Hlock_first]
    [Hisr_second Hlock_second].
  split; intro Hsource.
  - exact (Hisr_second (Hisr_first Hsource)).
  - exact (Hlock_second (Hlock_first Hsource)).
Qed.

Lemma sched_disabled_context_rely_preserves_entry_source : forall view sg before after,
  sched_disabled_context_rely view sg before after ->
  sched_disabled_entry_source view before -> sched_disabled_entry_source view after.
Proof.
  intros view sg before after [Hisr Hlock] [Hsource|Hsource].
  - left; exact (Hisr Hsource).
  - right; exact (Hlock Hsource).
Qed.

(** The reference-indexed invariant is transported along the SAME interval
    returned by the generic CPU contract. The certificates supply validity
    and resource frames; the separate public premise supplies contextual R. *)
Lemma sched_disabled_interval_preserves_context :
  forall critical sg view invocation before after,
  sched_disabled_completed_clients critical view ->
  UCOS2_state_inv sg before ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg after /\ sched_disabled_context_rely view sg before after.
Proof.
  intros critical sg view invocation before after Hclients Hvalid Hinterval.
  pose (I := fun sg state => UCOS2_state_inv sg state /\
    sched_disabled_context_rely view sg before state).
  assert (Hpreserves : forall action, critical_region_clients critical action ->
    kernel_client_preserves_resources I action).
  { intros action Hin sg' state next [Hstate Hreference] Hstep.
    destruct (kernel_client_certificate_preserves_selected_resources action
      (critical_region_client_certificates critical action Hin)
      sg' state next Hstate Hstep) as [Hnext Hframes].
    split; [split; [exact Hnext|]|exact Hframes].
    eapply sched_disabled_context_rely_trans; [exact Hreference|].
    exact (Hclients action Hin sg' state next Hstate Hstep). }
  exact (proj1 (critical_region_interval_transports_invariant I critical sg
    invocation before after Hpreserves Hinterval
    (conj Hvalid (sched_disabled_context_rely_refl view sg before)))).
Qed.

Lemma sched_disabled_entry_source_disables_counters : forall view state,
  sched_disabled_entry_source view state ->
  os_sched_ints state <> 0 \/ os_sched_locks state <> 0.
Proof.
  intros view state [[handler [interrupted [Hcontext [Hrunning Hagrees]]]]|Hlock].
  - left; unfold os_sched_ints; rewrite Hcontext in Hagrees.
    pose proof (kernel_running_interrupt_nesting_positive handler interrupted
      state.(IntrState) Hagrees); lia.
  - right; unfold os_sched_locks; lia.
Qed.

Lemma sched_disabled_counters_positive_guard : forall view state,
  sched_disabled_entry_source view state -> interrupt_in_range state.(IntrState) ->
  0 < os_sched_ints state + os_sched_locks state.
Proof.
  intros view state Hsource Hrange.
  destruct (sched_disabled_entry_source_disables_counters view state Hsource);
    unfold interrupt_in_range, os_sched_ints, os_sched_locks in *; lia.
Qed.

Definition sched_disabled_protected_identity (state : UCOS2_Verify_State) : Prop :=
  os_sched_selection_enabled state = false /\ os_sched_prefix_state state = state.

Lemma sched_disabled_entry_source_protected_identity : forall view state,
  sched_disabled_entry_source view state -> sched_disabled_protected_identity state.
Proof.
  intros view state Hsource.
  assert (Hdisabled : os_sched_selection_enabled state = false).
  { destruct (os_sched_selection_enabled state) eqn:Hen; [|reflexivity].
    apply os_sched_selection_enabled_iff in Hen.
    destruct (sched_disabled_entry_source_disables_counters view state Hsource);
      unfold os_sched_ints, os_sched_locks in *; tauto. }
  split; [exact Hdisabled|].
  unfold os_sched_prefix_state.
  rewrite (proj2 (os_sched_disabled_checkpoint_eq state Hdisabled)).
  apply replace_SchedS_put_back.
Qed.

(** Generic CPU, outside and SAME-view resources. No Task allocation lease,
    current TCB, ready-list premise or handler-to-Task conversion is used. *)
Definition sched_disabled_closed (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (view : OsExecutionView) (mask : Z)
  (state : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform view.(os_execution_invocation)
    view.(os_execution_origin) mask **
  critical_region_outside critical sg view.(os_execution_invocation) state **
  os_execution_view_resources external view.

Definition sched_disabled_masked (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (view : OsExecutionView) (saved : Z)
  (acquired released : UCOS2_Verify_State) : Assertion :=
  critical_region_masked platform critical sg view.(os_execution_invocation)
    view.(os_execution_origin) saved acquired **
  UCOS2_inv sg released ** os_execution_view_resources external view.

Definition sched_disabled_save_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (view : OsExecutionView) (mask saved : Z)
  (before : UCOS2_Verify_State) : Assertion :=
  EX acquired,
    coq_prop (sched_disabled_completed_clients critical view /\
      critical_region_interval critical sg view.(os_execution_invocation) before acquired /\
      interrupt_saved_value mask saved /\ UCOS2_state_inv sg acquired /\
      sched_disabled_context_rely view sg before acquired /\
      sched_disabled_entry_source view acquired /\
      sched_disabled_protected_identity acquired) &&
    sched_disabled_masked external platform critical sg view saved acquired acquired.

Definition sched_disabled_restore_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (view : OsExecutionView) (saved : Z)
  (released : UCOS2_Verify_State) : Assertion :=
  EX current,
    coq_prop (sched_disabled_completed_clients critical view /\
      critical_region_interval critical sg view.(os_execution_invocation) released current /\
      UCOS2_state_inv sg current /\ sched_disabled_context_rely view sg released current /\
      sched_disabled_entry_source view current) &&
    sched_disabled_closed external platform critical sg view
      (armv7a_irq_fiq_mask saved) current.

Definition sched_disabled_contextual_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (view : OsExecutionView) (mask : Z)
  (before : UCOS2_Verify_State) : Assertion :=
  EX saved acquired current,
    coq_prop (sched_disabled_completed_clients critical view /\
      critical_region_interval critical sg view.(os_execution_invocation) before acquired /\
      interrupt_saved_value mask saved /\ UCOS2_state_inv sg acquired /\
      sched_disabled_context_rely view sg before acquired /\
      sched_disabled_entry_source view acquired /\
      sched_disabled_protected_identity acquired /\
      critical_region_interval critical sg view.(os_execution_invocation) acquired current /\
      sched_disabled_context_rely view sg acquired current /\
      sched_disabled_context_rely view sg before current /\
      UCOS2_state_inv sg current /\ sched_disabled_entry_source view current) &&
    sched_disabled_closed external platform critical sg view mask current.

Lemma sched_disabled_save_post_from_interval :
  forall external platform critical sg view mask saved before,
  sched_disabled_completed_clients critical view -> UCOS2_state_inv sg before ->
  sched_disabled_entry_source view before ->
  (EX acquired,
    coq_prop (critical_region_interval critical sg view.(os_execution_invocation)
      before acquired /\ interrupt_saved_value mask saved) &&
    (critical_region_masked platform critical sg view.(os_execution_invocation)
       view.(os_execution_origin) saved acquired ** UCOS2_raw_rep sg acquired **
     os_execution_view_resources external view)) |--
  sched_disabled_save_post external platform critical sg view mask saved before.
Proof.
  intros external platform critical sg view mask saved before Hclients Hvalid Hsource.
  unfold sched_disabled_save_post, sched_disabled_masked.
  Intros acquired; Intros.
  destruct H as [Hinterval Hsaved].
  destruct (sched_disabled_interval_preserves_context critical sg view
    view.(os_execution_invocation) before acquired Hclients Hvalid Hinterval)
    as [Hacquired Hrely].
  pose proof (sched_disabled_context_rely_preserves_entry_source
    view sg before acquired Hrely Hsource) as Hacquired_source.
  sep_apply_l_atomic (critical_region_interval_open_invariant critical sg
    view.(os_execution_invocation) before acquired Hinterval Hvalid).
  Exists acquired; entailer!.
  apply sched_disabled_entry_source_protected_identity with (view := view); assumption.
Qed.

Lemma sched_disabled_restore_post_from_interval :
  forall external platform critical sg view saved released,
  sched_disabled_completed_clients critical view -> UCOS2_state_inv sg released ->
  sched_disabled_entry_source view released ->
  (EX current,
    coq_prop (critical_region_interval critical sg view.(os_execution_invocation)
      released current) &&
    (interrupt_platform_running platform view.(os_execution_invocation)
       view.(os_execution_origin) (armv7a_irq_fiq_mask saved) **
     critical_region_outside critical sg view.(os_execution_invocation) current **
     os_execution_view_resources external view)) |--
  sched_disabled_restore_post external platform critical sg view saved released.
Proof.
  intros external platform critical sg view saved released Hclients Hvalid Hsource.
  unfold sched_disabled_restore_post, sched_disabled_closed.
  Intros current; Intros.
  destruct (sched_disabled_interval_preserves_context critical sg view
    view.(os_execution_invocation) released current Hclients Hvalid H)
    as [Hcurrent Hrely].
  Exists current; entailer!.
  eapply sched_disabled_context_rely_preserves_entry_source; eassumption.
Qed.

(** Original-value split/merge only: both guards are read-only and the
    double-zero branch is ruled out from its actual acquired counter cells. *)
Definition sched_disabled_counter_frame (sg : StableGlobVars)
  (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\ interrupt_in_range state.(IntrState)) &&
  UCOS2_raw_rep_missing_interrupt sg state.

Lemma sched_disabled_inv_split_counters : forall sg state,
  UCOS2_inv sg state --||--
  (sg.(g_OSIntNesting) # UChar |-> os_sched_ints state **
   sg.(g_OSLockNesting) # UChar |-> os_sched_locks state **
   sched_disabled_counter_frame sg state).
Proof.
  intros; rewrite UCOS2_inv_split_interrupt.
  unfold interrupt_inv, store_int_state, sched_disabled_counter_frame,
    os_sched_ints, os_sched_locks; split; entailer!.
Qed.

Lemma sched_disabled_contextual_post_from_restore :
  forall external platform critical sg view mask saved before acquired,
  sched_disabled_completed_clients critical view ->
  critical_region_interval critical sg view.(os_execution_invocation) before acquired ->
  interrupt_saved_value mask saved -> UCOS2_state_inv sg acquired ->
  sched_disabled_context_rely view sg before acquired ->
  sched_disabled_entry_source view acquired -> sched_disabled_protected_identity acquired ->
  sched_disabled_restore_post external platform critical sg view saved acquired |--
  sched_disabled_contextual_post external platform critical sg view mask before.
Proof.
  intros external platform critical sg view mask saved before acquired
    Hclients Hinterval Hsaved Hvalid Hrely Hsource Hidentity.
  unfold sched_disabled_restore_post, sched_disabled_contextual_post.
  Intros current; Intros.
  destruct H as [_ [Hrestore [Hcurrent [Hafter Hcurrent_source]]]].
  destruct Hsaved as [Hword Hmask]; rewrite Hmask.
  Exists saved acquired current; entailer!.
  - split; assumption.
  - eapply sched_disabled_context_rely_trans; eassumption.
Qed.
