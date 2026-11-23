Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_program_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** C counter producers for the six-field Flag owner.  OSIntEnter is
    saturated at 255; OSIntExit stores only after a positive observed
    nesting value.  These are distinct from the ARM byte-wrap producer. *)

Lemma os_int_enter_source_heap_fields_raw_post : forall sg entry heap,
  UCOS2_fields_raw_rep sg entry heap ->
  exists final,
    kernel_heap_execution (os_int_enter_heap_writes sg entry) heap final /\
    UCOS2_fields_raw_rep sg (os_int_enter_state entry) final.
Proof.
  intros sg entry heap Hraw. unfold os_int_enter_heap_writes.
  destruct entry.(SchedState).(isRunning) eqn:Hrunning.
  - destruct (entry.(IntrState).(intNesting) <? 255) eqn:Hbelow.
    + apply Z.ltb_lt in Hbelow.
      assert (Hsplit : UCOS2_fields_raw_rep sg entry |--
        coq_prop (interrupt_in_range entry.(IntrState)) &&
        (sg.(g_OSIntNesting) # UChar |-> entry.(IntrState).(intNesting) **
         (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
          UCOS2_fields_raw_rep_missing_module sg entry InterruptModule))).
      { rewrite (UCOS2_fields_raw_rep_split_module sg entry InterruptModule
          ltac:(discriminate)); cbn [UCOS2_module_rep].
        unfold interrupt_inv, store_int_state; entailer!. }
      destruct (Hsplit heap Hraw) as [Hrange Hcells].
      change (interrupt_in_range entry.(IntrState)) in Hrange.
      assert (Hstored : 0 <= entry.(IntrState).(intNesting) + 1 < 256)
        by (unfold interrupt_in_range in Hrange; lia).
      destruct (kernel_heap_framed_uchar_store _ _ _ _ _ Hstored Hcells)
        as [final [Hrun Hfinal]].
      exists final; split; [exact Hrun|].
      assert (Hmerge :
        sg.(g_OSIntNesting) # UChar |-> (entry.(IntrState).(intNesting) + 1) **
        (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
         UCOS2_fields_raw_rep_missing_module sg entry InterruptModule) |--
        UCOS2_fields_raw_rep sg (os_int_enter_state entry)).
      { unfold os_int_enter_state;
        rewrite (UCOS2_fields_raw_rep_split_module sg _ InterruptModule
          ltac:(discriminate)).
        change (sg.(g_OSIntNesting) # UChar |-> (entry.(IntrState).(intNesting) + 1) **
          (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
           UCOS2_fields_raw_rep_missing_module sg entry InterruptModule) |--
          interrupt_inv sg
            (interrupt_enter_state entry.(SchedState).(isRunning) entry.(IntrState)) **
          UCOS2_fields_raw_rep_missing_module sg entry InterruptModule).
        unfold interrupt_enter_state; rewrite Hrunning.
        assert (Hlt : (entry.(IntrState).(intNesting) <? 255) = true)
          by (apply Z.ltb_lt; exact Hbelow); rewrite Hlt.
        assert (Hpack :
          sg.(g_OSIntNesting) # UChar |-> (entry.(IntrState).(intNesting) + 1) **
          (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
           UCOS2_fields_raw_rep_missing_module sg entry InterruptModule) |--
          store_int_state sg
            {| intNesting := entry.(IntrState).(intNesting) + 1;
               lockNesting := entry.(IntrState).(lockNesting) |} **
          UCOS2_fields_raw_rep_missing_module sg entry InterruptModule).
        { unfold store_int_state; cbn; entailer!. }
        intros h Hcells0; destruct (Hpack h Hcells0) as [c [r [Hjoin [Hc Hr]]]].
        exists c, r; split; [exact Hjoin|]. split.
        - apply interrupt_inv_merge_counters; exact Hc.
        - exact Hr. }
      exact (Hmerge final Hfinal).
    + exists heap; split; [split; [constructor|split; reflexivity]|].
      unfold os_int_enter_state, interrupt_enter_state; rewrite Hrunning, Hbelow.
      rewrite replace_IntrS_put_back; exact Hraw.
  - exists heap; split; [split; [constructor|split; reflexivity]|].
    rewrite (os_int_enter_not_running_no_effect entry Hrunning); exact Hraw.
Qed.

Lemma os_int_enter_source_heap_fields_raw_preservation : forall sg entry heap final,
  UCOS2_fields_raw_rep sg entry heap ->
  kernel_heap_execution (os_int_enter_heap_writes sg entry) heap final ->
  UCOS2_fields_raw_rep sg (os_int_enter_state entry) final.
Proof.
  intros sg entry heap final Hraw Hrun.
  destruct (os_int_enter_source_heap_fields_raw_post sg entry heap Hraw)
    as [produced [Hproduced Hpost]].
  assert (produced = final) by
    (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced; exact Hpost.
Qed.

Lemma os_int_enter_source_heap_fields_post : forall sg entry heap,
  UCOS2_fields_inv sg entry heap ->
  exists final,
    kernel_heap_execution (os_int_enter_heap_writes sg entry) heap final /\
    UCOS2_fields_inv sg (os_int_enter_state entry) final.
Proof.
  intros sg entry heap [Hvalid Hraw].
  destruct (os_int_enter_source_heap_fields_raw_post sg entry heap Hraw)
    as [final [Hrun Hpost]].
  exists final; split; [exact Hrun|].
  split; [apply os_int_enter_preserves_validity; exact Hvalid|exact Hpost].
Qed.

Lemma os_int_enter_source_heap_fields_frames_private : forall sg entry
  (private : Assertion) heap,
  (UCOS2_fields_inv sg entry ** private) heap ->
  exists final,
    kernel_heap_execution (os_int_enter_heap_writes sg entry) heap final /\
    (UCOS2_fields_inv sg (os_int_enter_state entry) ** private) final.
Proof.
  intros sg entry private heap [owned [local [Hjoin [Hinv Hprivate]]]].
  destruct (os_int_enter_source_heap_fields_post sg entry owned Hinv)
    as [after [Hrun Hpost]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  exists after, local; split; [exact Hfinal|]; split; assumption.
Qed.

Lemma os_int_exit_counter_heap_fields_raw_post : forall sg observed entry heap,
  UCOS2_fields_raw_rep sg entry heap ->
  exists final,
    kernel_heap_execution (os_int_exit_counter_heap_writes sg observed entry) heap final /\
    UCOS2_fields_raw_rep sg (os_int_exit_counter_state observed entry) final.
Proof.
  intros sg [] entry heap Hraw; unfold os_int_exit_counter_heap_writes.
  - destruct (0 <? entry.(IntrState).(intNesting)) eqn:Hpositive.
    + assert (Hsplit : UCOS2_fields_raw_rep sg entry |--
        sg.(g_OSIntNesting) # UChar |-> entry.(IntrState).(intNesting) **
        (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
         UCOS2_fields_raw_rep_missing_module sg entry InterruptModule)).
      { rewrite (UCOS2_fields_raw_rep_split_module sg entry InterruptModule
          ltac:(discriminate)); cbn [UCOS2_module_rep].
        unfold interrupt_inv, store_int_state; entailer!. }
      pose proof (Hsplit heap Hraw) as Hcells.
      destruct Hcells as [cell [rest [Hjoin [Hcell Hrest]]]].
      pose proof (store_uchar_range _ _ cell Hcell) as Hrange.
      change (0 <= entry.(IntrState).(intNesting) <= 255) in Hrange.
      assert (Hstored : 0 <= entry.(IntrState).(intNesting) - 1 < 256)
        by (apply Z.ltb_lt in Hpositive; lia).
      destruct (kernel_heap_framed_uchar_store _ _ _ _ _ Hstored (Hsplit heap Hraw))
        as [final [Hrun Hfinal]].
      exists final; split; [exact Hrun|].
      assert (Hmerge :
        sg.(g_OSIntNesting) # UChar |-> (entry.(IntrState).(intNesting) - 1) **
        (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
         UCOS2_fields_raw_rep_missing_module sg entry InterruptModule) |--
        UCOS2_fields_raw_rep sg (os_int_exit_counter_state true entry)).
      { unfold os_int_exit_counter_state;
        rewrite (UCOS2_fields_raw_rep_split_module sg _ InterruptModule
          ltac:(discriminate)).
        change (sg.(g_OSIntNesting) # UChar |-> (entry.(IntrState).(intNesting) - 1) **
          (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
           UCOS2_fields_raw_rep_missing_module sg entry InterruptModule) |--
          interrupt_inv sg (interrupt_exit_state true entry.(IntrState)) **
          UCOS2_fields_raw_rep_missing_module sg entry InterruptModule).
        unfold interrupt_exit_state; rewrite Hpositive.
        assert (Hpack :
          sg.(g_OSIntNesting) # UChar |-> (entry.(IntrState).(intNesting) - 1) **
          (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
           UCOS2_fields_raw_rep_missing_module sg entry InterruptModule) |--
          store_int_state sg
            {| intNesting := entry.(IntrState).(intNesting) - 1;
               lockNesting := entry.(IntrState).(lockNesting) |} **
          UCOS2_fields_raw_rep_missing_module sg entry InterruptModule).
        { unfold store_int_state; cbn; entailer!. }
        intros h Hcells0; destruct (Hpack h Hcells0) as [c [r [Hjoin0 [Hc0 Hr0]]]].
        exists c, r; split; [exact Hjoin0|]. split.
        - apply interrupt_inv_merge_counters; exact Hc0.
        - exact Hr0. }
      exact (Hmerge final Hfinal).
    + exists heap; split; [split; [constructor|split; reflexivity]|].
      unfold os_int_exit_counter_state, interrupt_exit_state; rewrite Hpositive.
      rewrite replace_IntrS_put_back; exact Hraw.
  - exists heap; split; [split; [constructor|split; reflexivity]|].
    unfold os_int_exit_counter_state, interrupt_exit_state.
    rewrite replace_IntrS_put_back; exact Hraw.
Qed.

Lemma os_int_exit_counter_heap_fields_raw_preservation : forall sg observed entry heap final,
  UCOS2_fields_raw_rep sg entry heap ->
  kernel_heap_execution (os_int_exit_counter_heap_writes sg observed entry) heap final ->
  UCOS2_fields_raw_rep sg (os_int_exit_counter_state observed entry) final.
Proof.
  intros sg observed entry heap final Hraw Hrun.
  destruct (os_int_exit_counter_heap_fields_raw_post sg observed entry heap Hraw)
    as [produced [Hproduced Hpost]].
  assert (produced = final) by
    (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced; exact Hpost.
Qed.

Lemma os_int_exit_counter_heap_fields_post : forall sg observed entry heap,
  UCOS2_fields_inv sg entry heap ->
  exists final,
    kernel_heap_execution (os_int_exit_counter_heap_writes sg observed entry) heap final /\
    UCOS2_fields_inv sg (os_int_exit_counter_state observed entry) final.
Proof.
  intros sg observed entry heap [Hvalid Hraw].
  destruct (os_int_exit_counter_heap_fields_raw_post sg observed entry heap Hraw)
    as [final [Hrun Hpost]].
  exists final; split; [exact Hrun|]. split; [exact Hvalid|exact Hpost].
Qed.

Lemma os_int_enter_fields_raw_running_load : forall sg state heap,
  UCOS2_fields_raw_rep sg state heap ->
  uchar_load sg.(g_OSRunning)
    (if state.(SchedState).(isRunning) then 1 else 0) heap.
Proof.
  intros sg state heap Hraw.
  assert (Hsplit : UCOS2_fields_raw_rep sg state |--
    sg.(g_OSRunning) # UChar |->
      (if state.(SchedState).(isRunning) then 1 else 0) **
    (sched_raw_rep_without_running sg state.(TskState) state.(SchedState) **
     UCOS2_fields_raw_rep_missing_module sg state SchedModule)).
  { rewrite (UCOS2_fields_raw_rep_split_module sg state SchedModule
      ltac:(discriminate)); cbn [UCOS2_module_rep].
    rewrite sched_raw_rep_split_running.
    unfold UCOS2_fields_raw_rep_missing_module; entailer!. }
  eapply framed_uchar_store_load; exact (Hsplit heap Hraw).
Qed.

Lemma os_int_enter_fields_raw_nesting_load : forall sg state heap,
  UCOS2_fields_raw_rep sg state heap ->
  uchar_load sg.(g_OSIntNesting) state.(IntrState).(intNesting) heap.
Proof.
  intros sg state heap Hraw.
  assert (Hsplit : UCOS2_fields_raw_rep sg state |--
    sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
    (sg.(g_OSLockNesting) # UChar |-> state.(IntrState).(lockNesting) **
     UCOS2_fields_raw_rep_missing_module sg state InterruptModule)).
  { rewrite (UCOS2_fields_raw_rep_split_module sg state InterruptModule
      ltac:(discriminate)); cbn [UCOS2_module_rep].
    unfold interrupt_inv, store_int_state; entailer!. }
  eapply framed_uchar_store_load; exact (Hsplit heap Hraw).
Qed.

Lemma os_int_exit_fields_raw_running_load : forall sg state heap,
  UCOS2_fields_raw_rep sg state heap ->
  uchar_load sg.(g_OSRunning)
    (if state.(SchedState).(isRunning) then 1 else 0) heap.
Proof. exact os_int_enter_fields_raw_running_load. Qed.

Lemma os_int_exit_fields_raw_nesting_load : forall sg state heap,
  UCOS2_fields_raw_rep sg state heap ->
  uchar_load sg.(g_OSIntNesting) state.(IntrState).(intNesting) heap.
Proof. exact os_int_enter_fields_raw_nesting_load. Qed.

Lemma os_int_exit_fields_raw_lock_load : forall sg state heap,
  UCOS2_fields_raw_rep sg state heap ->
  uchar_load sg.(g_OSLockNesting) state.(IntrState).(lockNesting) heap.
Proof.
  intros sg state heap Hraw.
  assert (Hsplit : UCOS2_fields_raw_rep sg state |--
    sg.(g_OSLockNesting) # UChar |-> state.(IntrState).(lockNesting) **
    (sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
     UCOS2_fields_raw_rep_missing_module sg state InterruptModule)).
  { rewrite (UCOS2_fields_raw_rep_split_module sg state InterruptModule
      ltac:(discriminate)); cbn [UCOS2_module_rep].
    unfold interrupt_inv, store_int_state; entailer!. }
  eapply framed_uchar_store_load; exact (Hsplit heap Hraw).
Qed.

Lemma kernel_client_int_enter_fields_writes : forall sg state (frame : Assertion)
  before after,
  (UCOS2_fields_inv sg state ** frame) before ->
  kernel_client_int_enter_fragment sg before after ->
  kernel_heap_execution (os_int_enter_heap_writes sg state) before after.
Proof.
  intros sg state frame before after [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]] Hsource.
  pose proof (uchar_load_frame _ _ _ _ _
    (os_int_exit_fields_raw_running_load sg state owned Hraw) Hjoin) as Hr.
  pose proof (uchar_load_frame _ _ _ _ _
    (os_int_enter_fields_raw_nesting_load sg state owned Hraw) Hjoin) as Hn.
  unfold os_int_enter_heap_writes.
  destruct Hsource as [heap Hread|heap nesting Hread Hnest Hsat|heap nesting final Hread Hnest Hlt Hwrite].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
    destruct state.(SchedState).(isRunning); [discriminate|].
    split; [constructor|split; reflexivity].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
    pose proof (uchar_load_deterministic _ _ _ _ Hnest Hn) as ->.
    destruct state.(SchedState).(isRunning); [|discriminate].
    assert ((state.(IntrState).(intNesting) <? 255) = false) as ->
      by (apply Z.ltb_ge; exact Hsat).
    split; [constructor|split; reflexivity].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
    pose proof (uchar_load_deterministic _ _ _ _ Hnest Hn) as ->.
    destruct state.(SchedState).(isRunning); [|discriminate].
    assert ((state.(IntrState).(intNesting) <? 255) = true) as ->
      by (apply Z.ltb_lt; exact Hlt).
    exact Hwrite.
Qed.

Lemma os_int_exit_masked_counter_fields_observation : forall sg state before observed after,
  UCOS2_fields_raw_rep sg state before ->
  os_int_exit_masked_counter_fragment sg before observed after ->
  observed = state.(SchedState).(isRunning) /\
  kernel_heap_execution (os_int_exit_counter_heap_writes sg observed state) before after.
Proof.
  intros sg state before observed after Hraw Hsource.
  pose proof (os_int_exit_fields_raw_running_load sg state before Hraw) as Hrunning.
  destruct Hsource as [heap Hread|heap nesting final Hread Hnest Hrun].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hrunning) as Hvalue.
    destruct state.(SchedState).(isRunning); [discriminate|].
    split; [reflexivity|]. split; [constructor|split; reflexivity].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hrunning) as Hvalue.
    pose proof (uchar_load_deterministic _ _ _ _ Hnest
      (os_int_exit_fields_raw_nesting_load sg state heap Hraw)) as Hcount.
    destruct state.(SchedState).(isRunning); [|discriminate].
    split; [reflexivity|]. subst nesting; exact Hrun.
Qed.

Lemma os_int_exit_masked_counter_fields_raw_preservation : forall sg state before observed after,
  UCOS2_fields_raw_rep sg state before ->
  os_int_exit_masked_counter_fragment sg before observed after ->
  UCOS2_fields_raw_rep sg (os_int_exit_counter_state observed state) after.
Proof.
  intros sg state before observed after Hraw Hsource.
  destruct (os_int_exit_masked_counter_fields_observation sg state before observed after
    Hraw Hsource) as [_ Hrun].
  eapply os_int_exit_counter_heap_fields_raw_preservation; eassumption.
Qed.

Lemma os_int_exit_masked_no_schedule_fields_raw_post : forall sg state heap,
  UCOS2_fields_raw_rep sg state heap ->
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  exists final,
    os_int_exit_masked_no_schedule_fragment sg heap final /\
    kernel_heap_execution
      (os_int_exit_counter_heap_writes sg state.(SchedState).(isRunning) state)
      heap final /\
    UCOS2_fields_raw_rep sg
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) final.
Proof.
  intros sg state heap Hraw Hnoschedule.
  destruct (os_int_exit_counter_heap_fields_raw_post sg state.(SchedState).(isRunning)
    state heap Hraw) as [final [Hrun Hpost]].
  assert (Hsource : os_int_exit_masked_counter_fragment sg heap
    state.(SchedState).(isRunning) final).
  { pose proof (os_int_exit_fields_raw_running_load sg state heap Hraw) as Hread.
    destruct state.(SchedState).(isRunning) eqn:Hrunning.
    - pose proof (os_int_exit_fields_raw_nesting_load sg state heap Hraw) as Hnest.
      unfold os_int_exit_counter_heap_writes in Hrun.
      eapply OsIntExitMaskedActive; [exact Hread|exact Hnest|exact Hrun].
    - assert (Hid : kernel_heap_execution [] heap heap)
        by (split; [constructor|split; reflexivity]).
      assert (Hsame : final = heap)
        by (eapply kernel_heap_execution_deterministic; eassumption).
      subst final; apply OsIntExitMaskedInactive; exact Hread. }
  exists final; split; [|split; assumption].
  destruct state.(SchedState).(isRunning) eqn:Hrunning.
  - pose proof (os_int_exit_fields_raw_nesting_load sg _ final Hpost) as Hnest.
    pose proof (os_int_exit_fields_raw_lock_load sg _ final Hpost) as Hlock.
    set (nesting := (interrupt_exit_state true state.(IntrState)).(intNesting)) in *.
    change (uchar_load sg.(g_OSIntNesting) nesting final) in Hnest.
    destruct (Z.eq_dec nesting 0) as [Hzero|Hnonzero].
    + eapply OsIntExitMaskedLocked; [exact Hsource|rewrite <- Hzero; exact Hnest|
        exact Hlock|].
      intro HzeroLock; unfold interrupt_exit_requests_schedule in Hnoschedule.
      change ((Z.eqb nesting 0 && Z.eqb state.(IntrState).(lockNesting) 0)%bool = false)
        in Hnoschedule.
      assert (Hlocks : (interrupt_exit_state true state.(IntrState)).(lockNesting) =
        state.(IntrState).(lockNesting)).
      { unfold interrupt_exit_state; destruct (0 <? state.(IntrState).(intNesting)); reflexivity. }
      change ((interrupt_exit_state true state.(IntrState)).(lockNesting) = 0) in HzeroLock.
      rewrite Hlocks in HzeroLock; rewrite Hzero, HzeroLock in Hnoschedule; discriminate.
    + eapply OsIntExitMaskedStillNested; eassumption.
  - apply OsIntExitMaskedNoRunning; exact Hsource.
Qed.

Lemma os_int_exit_masked_no_schedule_fields_frame_post : forall sg state
  (frame : Assertion) heap,
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  (UCOS2_fields_inv sg state ** frame) heap ->
  exists final,
    os_int_exit_masked_no_schedule_fragment sg heap final /\
    (UCOS2_fields_inv sg
       (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) final.
Proof.
  intros sg state frame heap Hnoschedule
    [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]].
  destruct (os_int_exit_masked_no_schedule_fields_raw_post sg state owned Hraw Hnoschedule)
    as [after [Hsource [Hrun Hpost]]].
  destruct (os_int_exit_masked_no_schedule_fragment_frame sg owned after rest heap Hsource Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  exists after, rest; split; [exact Hfinal|].
  split; [split; assumption|exact Hframe].
Qed.



Lemma os_int_exit_masked_no_schedule_fields_frame_transport : forall sg state
  (frame : Assertion) before after,
  os_int_exit_masked_no_schedule_fragment sg before after ->
  (UCOS2_fields_inv sg state ** frame) before ->
  (UCOS2_fields_inv sg
     (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros sg state frame before after Hsource
    [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]].
  destruct (os_int_exit_counter_heap_fields_raw_post sg state.(SchedState).(isRunning)
    state owned Hraw) as [owned_after [Hrun Hpost]].
  assert (Hcounter : os_int_exit_masked_counter_fragment sg owned
    state.(SchedState).(isRunning) owned_after).
  { pose proof (os_int_exit_fields_raw_running_load sg state owned Hraw) as Hread.
    destruct state.(SchedState).(isRunning) eqn:Hrunning.
    - pose proof (os_int_exit_fields_raw_nesting_load sg state owned Hraw) as Hnest.
      unfold os_int_exit_counter_heap_writes in Hrun.
      eapply OsIntExitMaskedActive; [exact Hread|exact Hnest|exact Hrun].
    - assert (Hid : kernel_heap_execution [] owned owned)
        by (split; [constructor|split; reflexivity]).
      assert (Hsame : owned_after = owned)
        by (eapply kernel_heap_execution_deterministic; eassumption).
      subst owned_after; apply OsIntExitMaskedInactive; exact Hread. }
  destruct (os_int_exit_masked_counter_fragment_frame sg owned
    state.(SchedState).(isRunning) owned_after rest before Hcounter Hjoin)
    as [produced [Hcounter_whole Hframe_join]].
  assert (Hsame : produced = after).
  { destruct Hsource; eapply os_int_exit_masked_counter_final_eq; eassumption. }
  subst produced.
  exists owned_after, rest; split; [exact Hframe_join|].
  split; [split; assumption|exact Hframe].
Qed.
(** Actual continuation consumer for the C counter producers.  The map and
    local predicate stay in the frame; only the fields global owner changes. *)
Definition kernel_client_continuation_fields_world {external platform port}
  (abi : Armv7aContinuationABI external platform port)
  (local : Armv7aContinuation -> Assertion) sg state : Assertion :=
  kernel_continuation_inv abi kernel_program_fields_inv local sg None state.

Lemma kernel_client_int_enter_continuation_fields_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  local sg state (frame : Assertion) before after,
  (kernel_client_continuation_fields_world abi local sg state ** frame) before ->
  kernel_client_int_enter_fragment sg before after ->
  (kernel_client_continuation_fields_world abi local sg (os_int_enter_state state) ** frame) after.
Proof.
  intros external platform port abi local sg state frame before after Hpre Hsource.
  assert (Hsplit :
    kernel_client_continuation_fields_world abi local sg state ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) None) &&
    (UCOS2_fields_inv sg state **
      (unmap_table_rep sg **
       store_parked_continuations
         (kernel_saved_continuation_entry abi state.(TskState) local)
         state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv.
    rewrite kernel_program_fields_inv_split_unmap; entailer!. }
  destruct (Hsplit before Hpre) as [Hcoverage Hheap].
  pose proof (kernel_client_int_enter_fields_writes sg state _ before after Hheap Hsource)
    as Hwrites.
  destruct (os_int_enter_source_heap_fields_frames_private sg state
    (unmap_table_rep sg **
     store_parked_continuations
       (kernel_saved_continuation_entry abi state.(TskState) local)
       state.(TskState).(parkedTaskStacks) ** frame) before Hheap)
    as [produced [Hrun Hpost]].
  assert (produced = after) by
    (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced.
  assert (Hmerge :
    UCOS2_fields_inv sg (os_int_enter_state state) **
      (unmap_table_rep sg **
       store_parked_continuations
         (kernel_saved_continuation_entry abi state.(TskState) local)
         state.(TskState).(parkedTaskStacks) ** frame) |--
    kernel_client_continuation_fields_world abi local sg (os_int_enter_state state) ** frame).
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv.
    rewrite kernel_program_fields_inv_split_unmap.
    unfold os_int_enter_state; cbn [replace_IntrS TskState]; entailer!. }
  exact (Hmerge after Hpost).
Qed.

Lemma kernel_client_int_exit_continuation_fields_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  local sg state (frame : Assertion) before after,
  (kernel_client_continuation_fields_world abi local sg state ** frame) before ->
  os_int_exit_masked_no_schedule_fragment sg before after ->
  (kernel_client_continuation_fields_world abi local sg
    (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros external platform port abi local sg state frame before after Hpre Hsource.
  assert (Hsplit :
    kernel_client_continuation_fields_world abi local sg state ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) None) &&
    (UCOS2_fields_inv sg state **
      (unmap_table_rep sg **
       store_parked_continuations
         (kernel_saved_continuation_entry abi state.(TskState) local)
         state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv.
    rewrite kernel_program_fields_inv_split_unmap; entailer!. }
  destruct (Hsplit before Hpre) as [Hcoverage Hheap].
  pose proof (os_int_exit_masked_no_schedule_fields_frame_transport sg state
    (unmap_table_rep sg **
     store_parked_continuations
       (kernel_saved_continuation_entry abi state.(TskState) local)
       state.(TskState).(parkedTaskStacks) ** frame) before after Hsource Hheap)
    as Hpost.
  destruct Hpost as [owned_after [rest_after [Hjoin_after [Hfields_after Hframe_after]]]].
  assert (Hmerge :
    UCOS2_fields_inv sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
      (unmap_table_rep sg **
       store_parked_continuations
         (kernel_saved_continuation_entry abi state.(TskState) local)
         state.(TskState).(parkedTaskStacks) ** frame) |--
    kernel_client_continuation_fields_world abi local sg
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame).
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv.
    rewrite kernel_program_fields_inv_split_unmap.
    unfold os_int_exit_counter_state; cbn [replace_IntrS TskState]; entailer!. }
  exact (Hmerge after (ex_intro _ owned_after (ex_intro _ rest_after
    (conj Hjoin_after (conj Hfields_after Hframe_after))))).
Qed.
