Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Bool.Bool Coq.micromega.Lia.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.kernel_execution.
Import ListNotations.
Local Open Scope Z_scope.

(** Public storage means that the pool image is in the shared Timer
    representation. It says nothing about object identity, generation,
    status or contents. Allocation temporarily removes this storage;
    complete creation publishes it again before OSSchedUnlock. *)
Definition timer_image_present (images : TimerID -> option TimerImage)
  (i : TimerID) : bool :=
  match images i with Some _ => true | None => false end.

Definition timer_public_storage_frame (before after : GlobTimerState) : Prop :=
  after.(timerInitPhase) = before.(timerInitPhase) /\
  forall i, timer_image_present after.(timerImages) i =
    timer_image_present before.(timerImages) i.

Lemma timer_public_storage_frame_refl : forall s,
  timer_public_storage_frame s s.
Proof. intro s; split; reflexivity. Qed.

Lemma timer_public_storage_frame_trans : forall before middle after,
  timer_public_storage_frame before middle ->
  timer_public_storage_frame middle after ->
  timer_public_storage_frame before after.
Proof.
  intros before middle after [Hphase1 Himages1] [Hphase2 Himages2].
  split; [congruence|intro i; rewrite Himages2, Himages1; reflexivity].
Qed.

Lemma timer_public_storage_frame_has_image : forall before after i old,
  timer_public_storage_frame before after ->
  before.(timerImages) i = Some old ->
  exists current, after.(timerImages) i = Some current.
Proof.
  intros before after i old [_ Himages] Hold.
  specialize (Himages i); unfold timer_image_present in Himages; rewrite Hold in Himages.
  destruct (timerImages after i) as [current|] eqn:Hcurrent; [eauto|discriminate].
Qed.

Lemma timer_public_storage_frame_initialized : forall before after,
  timer_public_storage_frame before after ->
  timer_api_initialized before -> timer_api_initialized after.
Proof.
  intros before after [Hphase _] Hinit; unfold timer_api_initialized in *.
  rewrite Hphase; exact Hinit.
Qed.

Lemma timer_images_replace_present : forall images i old current j,
  images i = Some old ->
  timer_image_present (kernel_map_set images i (Some current)) j =
    timer_image_present images j.
Proof.
  intros images i old current j Hold.
  unfold timer_image_present, kernel_map_set.
  destruct (Z.eq_dec j i) as [->|Hother].
  - rewrite Hold; reflexivity.
  - reflexivity.
Qed.

Lemma timer_images_set_next_present : forall images i next j,
  timer_image_present (timer_images_set_next images i next) j =
    timer_image_present images j.
Proof.
  intros images i next j; unfold timer_images_set_next, kernel_map_set, timer_image_present.
  destruct (Z.eq_dec j i) as [->|Hother].
  - destruct (images i); reflexivity.
  - reflexivity.
Qed.

Lemma timer_images_set_prev_present : forall images i prev j,
  timer_image_present (timer_images_set_prev images i prev) j =
    timer_image_present images j.
Proof.
  intros images i prev j; unfold timer_images_set_prev, kernel_map_set, timer_image_present.
  destruct (Z.eq_dec j i) as [->|Hother].
  - destruct (images i); reflexivity.
  - reflexivity.
Qed.

Lemma timer_wheel_prepend_images_present : forall sg images i old current row j,
  images i = Some old ->
  timer_image_present (timer_wheel_prepend_images sg images i current row) j =
    timer_image_present images j.
Proof.
  intros sg images i old current row j Hold.
  unfold timer_wheel_prepend_images.
  destruct (Z.eq_dec j i) as [->|Hother].
  - unfold timer_image_present; rewrite kernel_map_set_same, Hold; reflexivity.
  - unfold timer_image_present at 1; rewrite kernel_map_set_other by exact Hother.
    change (timer_image_present
      (match row with [] => images | head :: _ =>
        timer_images_set_prev images head (timer_pool_addr sg i) end) j =
      timer_image_present images j).
    destruct row; [reflexivity|apply timer_images_set_prev_present].
Qed.

Lemma timer_wheel_unlink_images_present : forall sg images i old row j,
  images i = Some old ->
  timer_image_present (timer_wheel_unlink_images sg images i old row) j =
    timer_image_present images j.
Proof.
  intros sg images i old row j Hold.
  unfold timer_wheel_unlink_images.
  destruct (Z.eq_dec j i) as [->|Hother].
  - unfold timer_image_present; rewrite kernel_map_set_same, Hold; reflexivity.
  - unfold timer_image_present at 1; rewrite kernel_map_set_other by exact Hother.
    change (timer_image_present
      (if timerImageNext old =? 0
       then (if timer_id_pointer sg row =? timer_pool_addr sg i then images
             else timer_images_set_next images (timer_pointer_index sg (timerImagePrev old))
               (timerImageNext old))
       else timer_images_set_prev
         (if timer_id_pointer sg row =? timer_pool_addr sg i then images
          else timer_images_set_next images (timer_pointer_index sg (timerImagePrev old))
            (timerImageNext old))
         (timer_pointer_index sg (timerImageNext old))
         (if timer_id_pointer sg row =? timer_pool_addr sg i then 0 else timerImagePrev old)) j =
      timer_image_present images j).
    destruct (timerImageNext old =? 0);
      destruct (timer_id_pointer sg row =? timer_pool_addr sg i);
      rewrite ?timer_images_set_next_present, ?timer_images_set_prev_present;
      try rewrite timer_images_set_next_present; reflexivity.
Qed.

(** The interval from successful Alloc through the private stores to
    publication is represented as a composition. The Alloc endpoint remains
    available to helper proofs; it is not itself a completed Create call. *)
Lemma timer_allocate_publish_public_storage_frame : forall before i private allocated
  delay period mode callback arg name,
  timer_allocate before = Some (i, private, allocated) ->
  timer_public_storage_frame before
    (timer_publish allocated i private delay period mode callback arg name).
Proof.
  intros before i private allocated delay period mode callback arg name Halloc.
  unfold timer_allocate in Halloc.
  destruct (timerFree before) as [|slot rest]; [discriminate|].
  destruct (timerImages before slot) as [old|] eqn:Hold; [|discriminate].
  inversion Halloc; subst i private allocated; clear Halloc.
  split; [reflexivity|].
  intro j; unfold timer_publish; cbn [timerImages].
  destruct (Z.eq_dec j slot) as [->|Hother].
  - unfold timer_image_present; rewrite kernel_map_set_same, Hold; reflexivity.
  - unfold timer_image_present; rewrite !kernel_map_set_other by exact Hother; reflexivity.
Qed.

Lemma timer_release_public_storage_frame : forall sg before i old name,
  before.(timerImages) i = Some old ->
  timer_public_storage_frame before (timer_release sg before i old name).
Proof.
  intros; split; [reflexivity|].
  intro j; apply timer_images_replace_present with (old := old); exact H.
Qed.

Lemma timer_link_public_storage_frame : forall sg before i periodic after,
  timer_link sg before i periodic = Some after ->
  timer_public_storage_frame before after.
Proof.
  intros sg before i periodic after Hstep; unfold timer_link in Hstep.
  destruct (timerUsed before i) as [node|]; [|discriminate].
  destruct (timerImages before i) as [old|] eqn:Hold; [|discriminate].
  inversion Hstep; subst after; clear Hstep.
  split; [reflexivity|].
  intro j; apply timer_wheel_prepend_images_present with (old := old); exact Hold.
Qed.

Lemma timer_unlink_public_storage_frame : forall sg before i after,
  timer_unlink sg before i = Some after ->
  timer_public_storage_frame before after.
Proof.
  intros sg before i after Hstep; unfold timer_unlink in Hstep.
  destruct (timerUsed before i) as [node|]; [|discriminate].
  destruct (timerImages before i) as [old|] eqn:Hold; [|discriminate].
  inversion Hstep; subst after; clear Hstep.
  split; [reflexivity|].
  intro j; apply timer_wheel_unlink_images_present; exact Hold.
Qed.

Lemma timer_complete_public_storage_frame : forall before i after,
  timer_complete before i = Some after ->
  timer_public_storage_frame before after.
Proof.
  intros before i after Hstep; unfold timer_complete in Hstep.
  destruct (timerUsed before i) as [node|]; [|discriminate].
  destruct (timerImages before i) as [old|] eqn:Hold; [|discriminate].
  inversion Hstep; subst after; clear Hstep.
  split; [reflexivity|].
  intro j; apply timer_images_replace_present with (old := old); exact Hold.
Qed.

(** Concrete Timer transformations whose complete endpoints can be used
    between public callers. This is a projection of those source segments,
    not an assertion that all kernel/interrupt/callback code is linked here.
    Internal allocation is intentionally retained in timer_allocate and in
    its helper specification, outside this public-step relation. *)
Inductive timer_public_step (sg : StableGlobVars)
  : GlobTimerState -> GlobTimerState -> Prop :=
| TimerPublicUnchanged : forall s, timer_public_step sg s s
| TimerPublicCreate : forall before i private allocated delay period mode callback arg name,
    timer_allocate before = Some (i, private, allocated) ->
    timer_public_step sg before (timer_publish allocated i private delay period mode callback arg name)
| TimerPublicRelease : forall before i old name,
    before.(timerImages) i = Some old ->
    timer_public_step sg before (timer_release sg before i old name)
| TimerPublicLink : forall before i periodic after,
    timer_link sg before i periodic = Some after -> timer_public_step sg before after
| TimerPublicUnlink : forall before i after,
    timer_unlink sg before i = Some after -> timer_public_step sg before after
| TimerPublicComplete : forall before i after,
    timer_complete before i = Some after -> timer_public_step sg before after
| TimerPublicAdvance : forall before, timer_public_step sg before (timer_service_advance before).

Lemma timer_public_step_public_storage_frame : forall sg before after,
  timer_public_step sg before after -> timer_public_storage_frame before after.
Proof.
  intros sg before after Hstep; destruct Hstep.
  - apply timer_public_storage_frame_refl.
  - eapply timer_allocate_publish_public_storage_frame; eassumption.
  - apply timer_release_public_storage_frame; assumption.
  - eapply timer_link_public_storage_frame; eassumption.
  - eapply timer_unlink_public_storage_frame; eassumption.
  - eapply timer_complete_public_storage_frame; eassumption.
  - split; reflexivity.
Qed.

Inductive timer_public_trace (sg : StableGlobVars)
  : GlobTimerState -> GlobTimerState -> Prop :=
| TimerPublicTraceNil : forall s, timer_public_trace sg s s
| TimerPublicTraceCons : forall before middle after,
    timer_public_step sg before middle -> timer_public_trace sg middle after ->
    timer_public_trace sg before after.

Lemma timer_public_trace_public_storage_frame : forall sg before after,
  timer_public_trace sg before after -> timer_public_storage_frame before after.
Proof.
  intros sg before after Htrace; induction Htrace.
  - apply timer_public_storage_frame_refl.
  - eapply timer_public_storage_frame_trans;
      [eapply timer_public_step_public_storage_frame; eassumption|exact IHHtrace].
Qed.

(** This counter theorem uses the exact saturating OSSchedLock transform.
    It applies to the source interval before the matching Unlock; a body
    theorem must still establish that interval's counter frame. In particular
    this does not add publication as an assumed platform/region field. *)
Lemma timer_create_locked_interrupt_exit_no_schedule : forall invocation origin counters observed,
  kernel_interrupt_nesting_agrees true (KernelCaller invocation origin) counters ->
  0 <= counters.(lockNesting) ->
  interrupt_exit_requests_schedule observed (sched_lock_state true counters) = false.
Proof.
  intros invocation origin counters observed Hcontext Hlocks.
  apply kernel_locked_interrupt_exit_no_schedule.
  pose proof (kernel_caller_lock_positive invocation origin counters Hcontext Hlocks); lia.
Qed.

Lemma timer_public_trace_one : forall sg before after,
  timer_public_step sg before after -> timer_public_trace sg before after.
Proof. intros; econstructor; [exact H|constructor]. Qed.

Lemma timer_public_trace_trans : forall sg before middle after,
  timer_public_trace sg before middle -> timer_public_trace sg middle after ->
  timer_public_trace sg before after.
Proof.
  intros sg before middle after Hleft Hright; induction Hleft.
  - exact Hright.
  - econstructor; [exact H|apply IHHleft; exact Hright].
Qed.

(** These source-composition lemmas cover the concrete Timer state writes
    in Start, Stop, Del and each service-loop visit. Error and observation
    paths are identity. Callbacks remain separate executions; the callback
    linking theorem must give its own public source trace. *)
Lemma timer_start_locked_public_trace : forall sg before i ret err after,
  timer_start_locked sg before i = Some (ret, err, after) ->
  timer_public_trace sg before after.
Proof.
  intros sg before i ret err after Hstep; unfold timer_start_locked in Hstep.
  destruct (timerImages before i) as [old|]; [|discriminate].
  destruct (timerImageState old =? 3).
  - destruct (timer_unlink sg before i) as [stopped|] eqn:Hunlink; [|discriminate].
    destruct (timer_link sg stopped i false) as [started|] eqn:Hlink; [|discriminate].
    inversion Hstep; subst after.
    econstructor; [eapply TimerPublicUnlink; exact Hunlink|].
    apply timer_public_trace_one; eapply TimerPublicLink; exact Hlink.
  - destruct (orb (timerImageState old =? 1) (timerImageState old =? 2)).
    + destruct (timer_link sg before i false) as [started|] eqn:Hlink; [|discriminate].
      inversion Hstep; subst after.
      apply timer_public_trace_one; eapply TimerPublicLink; exact Hlink.
    + destruct (timerImageState old =? 0); inversion Hstep; subst; constructor.
Qed.

Lemma timer_stop_dispatch_public_trace : forall sg before i opt arg ret err request after,
  timer_stop_dispatch sg before i opt arg = Some (ret, err, request, after) ->
  timer_public_trace sg before after.
Proof.
  intros sg before i opt arg ret err request after Hstep; unfold timer_stop_dispatch in Hstep.
  destruct (timerImages before i) as [old|]; [|discriminate].
  destruct (timerImageState old =? 3).
  - destruct (timer_unlink sg before i) as [stopped|] eqn:Hunlink; [|discriminate].
    destruct (timerImages stopped i) as [current|]; [|discriminate].
    destruct (timer_stop_request sg i current opt arg).
    inversion Hstep; subst after.
    apply timer_public_trace_one; eapply TimerPublicUnlink; exact Hunlink.
  - destruct (orb (timerImageState old =? 1) (timerImageState old =? 2)).
    + inversion Hstep; subst; constructor.
    + destruct (timerImageState old =? 0); inversion Hstep; subst; constructor.
Qed.

Lemma timer_delete_locked_public_trace : forall sg before i name ret err after,
  timer_delete_locked sg before i name = Some (ret, err, after) ->
  timer_public_trace sg before after.
Proof.
  intros sg before i name ret err after Hstep; unfold timer_delete_locked in Hstep.
  destruct (timerImages before i) as [old|] eqn:Hold; [|discriminate].
  destruct (timerImageState old =? 3).
  - destruct (timer_unlink sg before i) as [stopped|] eqn:Hunlink; [|discriminate].
    destruct (timerImages stopped i) as [current|] eqn:Hcurrent; [|discriminate].
    inversion Hstep; subst after.
    econstructor; [eapply TimerPublicUnlink; exact Hunlink|].
    apply timer_public_trace_one; apply TimerPublicRelease; exact Hcurrent.
  - destruct (orb (timerImageState old =? 1) (timerImageState old =? 2)).
    + inversion Hstep; subst after.
      apply timer_public_trace_one; apply TimerPublicRelease; exact Hold.
    + destruct (timerImageState old =? 0); inversion Hstep; subst; constructor.
Qed.

Lemma timer_expire_dispatch_public_trace : forall sg before i next request after,
  timer_expire_dispatch sg before i = Some (next, request, after) ->
  timer_public_trace sg before after.
Proof.
  intros sg before i next request after Hstep; unfold timer_expire_dispatch in Hstep.
  destruct (timerImages before i) as [old|]; [|discriminate].
  destruct (timerTime before =? timerImageMatch old).
  - destruct (timer_unlink sg before i) as [unlinked|] eqn:Hunlink; [|discriminate].
    destruct (timerImages unlinked i) as [current|]; [|discriminate].
    destruct (timerImageOption current =? 2).
    + destruct (timer_link sg unlinked i true) as [linked|] eqn:Hlink; [|discriminate].
      destruct (timerImages linked i); [|discriminate].
      inversion Hstep; subst after.
      econstructor; [eapply TimerPublicUnlink; exact Hunlink|].
      apply timer_public_trace_one; eapply TimerPublicLink; exact Hlink.
    + destruct (timer_complete unlinked i) as [completed|] eqn:Hcomplete; [|discriminate].
      destruct (timerImages completed i); [|discriminate].
      inversion Hstep; subst after.
      econstructor; [eapply TimerPublicUnlink; exact Hunlink|].
      apply timer_public_trace_one; eapply TimerPublicComplete; exact Hcomplete.
  - inversion Hstep; subst; constructor.
Qed.

Lemma timer_scan_execution_public_trace : forall sg callback before scan events after finish,
  (forall cursor call initial final,
    callback cursor call initial final -> timer_public_trace sg initial final) ->
  timer_scan_execution sg callback before scan events after finish ->
  timer_public_trace sg before after.
Proof.
  intros sg callback before scan events after finish Hcallback Hexec.
  induction Hexec.
  - constructor.
  - eapply timer_public_trace_trans.
    + eapply timer_expire_dispatch_public_trace; exact H1.
    + eapply timer_public_trace_trans; [|exact IHHexec].
      destruct request; [eapply Hcallback; exact H2|subst; constructor].
Qed.
