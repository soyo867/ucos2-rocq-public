Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Import UCOS2_C_Rules KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source/os_core.c:1751-1760, OS_LOWEST_PRIO <= 63. The two enabled
    profiles use this branch. These are four actual reads followed by the
    single OSPrioHighRdy byte store. This fragment runs with IRQ/FIQ masked;
    it neither assumes nor supplies an unmasked shared-memory rule.
    The second lookup is dependent on the byte actually read from RdyTbl.
    It does not infer a nonempty ready set from a source-total lookup. *)
Definition sched_new_heap_reads (sg : StableGlobVars) (heap : model)
  (priority : Z) : Prop :=
  exists group y row x,
    uchar_load sg.(g_OSRdyGrp) group heap /\
    uchar_load (sg.(g_OSUnMapTbl) + group * sizeof(UCHAR)) y heap /\
    uchar_load (sg.(g_OSRdyTbl) + y * sizeof(UCHAR)) row heap /\
    uchar_load (sg.(g_OSUnMapTbl) + row * sizeof(UCHAR)) x heap /\
    priority = (y * 8 + x) mod 256.

Definition sched_new_heap_fragment (sg : StableGlobVars)
  (before after : model) : Prop :=
  exists priority, sched_new_heap_reads sg before priority /\
    kernel_heap_execution [(sg.(g_OSPrioHighRdy), priority)] before after.

Lemma sched_new_heap_reads_deterministic : forall sg heap first second,
  sched_new_heap_reads sg heap first -> sched_new_heap_reads sg heap second ->
  first = second.
Proof.
  intros sg heap first second
    [group [y [row [x [Hg [Hy [Hr [Hx Hfirst]]]]]]]]
    [group' [y' [row' [x' [Hg' [Hy' [Hr' [Hx' Hsecond]]]]]]]].
  assert (group = group') by (eapply uchar_load_deterministic; eassumption); subst group'.
  assert (y = y') by (eapply uchar_load_deterministic; eassumption); subst y'.
  assert (row = row') by (eapply uchar_load_deterministic; eassumption); subst row'.
  assert (x = x') by (eapply uchar_load_deterministic; eassumption); subst x'; congruence.
Qed.

Lemma sched_new_heap_reads_frame : forall sg heap priority frame whole,
  sched_new_heap_reads sg heap priority -> join heap frame whole ->
  sched_new_heap_reads sg whole priority.
Proof.
  intros sg heap priority frame whole [group [y [row [x [Hg [Hy [Hr [Hx Hp]]]]]]]] Hjoin.
  exists group, y, row, x; repeat split; try exact Hp;
    eapply uchar_load_frame; eassumption.
Qed.

Lemma sched_new_heap_fragment_deterministic : forall sg before first second,
  sched_new_heap_fragment sg before first -> sched_new_heap_fragment sg before second ->
  first = second.
Proof.
  intros sg before first second [p [Hp Hfirst]] [q [Hq Hsecond]].
  assert (p = q) by (eapply sched_new_heap_reads_deterministic; eassumption); subst q.
  eapply kernel_heap_execution_deterministic; eassumption.
Qed.

Lemma sched_new_heap_fragment_frame : forall sg before after frame whole,
  sched_new_heap_fragment sg before after -> join before frame whole ->
  exists final, sched_new_heap_fragment sg whole final /\ join after frame final.
Proof.
  intros sg before after frame whole [priority [Hreads Hrun]] Hjoin.
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [final [Hwhole Hfinal]].
  exists final; split; [exists priority; split; [|exact Hwhole]|exact Hfinal].
  eapply sched_new_heap_reads_frame; eassumption.
Qed.

Lemma sched_new_heap_reads_from_rep : forall sg group rows high heap,
  sched_new_rep sg group rows high heap ->
  sched_new_heap_reads sg heap (sched_new_priority group rows).
Proof.
  intros sg group rows high heap Hrep.
  assert (Hgroup : uchar_load sg.(g_OSRdyGrp) group heap).
  { assert (Hfocus : sched_new_rep sg group rows high |--
      sg.(g_OSRdyGrp) # UChar |-> group ** TT).
    { unfold sched_new_rep; entailer!; intros ? ?; exact I. }
    eapply framed_uchar_store_load; exact (Hfocus heap Hrep). }
  assert (Htable : forall bits, 0 <= bits < 256 ->
    uchar_load (sg.(g_OSUnMapTbl) + bits * sizeof(UCHAR)) (unmap_value bits) heap).
  { intros bits Hbits.
    assert (Hfocus : sched_new_rep sg group rows high |--
      (sg.(g_OSUnMapTbl) + bits * sizeof(UCHAR)) # UChar |-> unmap_value bits ** TT).
    { unfold sched_new_rep; sep_apply_l_atomic (unmap_table_split_cell sg bits Hbits).
      entailer!; intros ? ?; exact I. }
    eapply framed_uchar_store_load; exact (Hfocus heap Hrep). }
  assert (Hrow : uchar_load (sg.(g_OSRdyTbl) + unmap_value group * sizeof(UCHAR))
    (Znth (unmap_value group) rows 0) heap).
  { assert (Hfocus : sched_new_rep sg group rows high |--
      (sg.(g_OSRdyTbl) + unmap_value group * sizeof(UCHAR)) # UChar |->
        Znth (unmap_value group) rows 0 ** TT).
    { unfold sched_new_rep.
      assert (Hsplit : UCharArray.full sg.(g_OSRdyTbl) 8 rows |--
        (sg.(g_OSRdyTbl) + unmap_value group * sizeof(UCHAR)) # UChar |->
          Znth (unmap_value group) rows 0 **
        UCharArray.missing_i sg.(g_OSRdyTbl) (unmap_value group) 0 8 rows).
      { apply UCharArray.full_split_to_missing_i; apply unmap_in_range. }
      sep_apply_l_atomic Hsplit.
      entailer!; intros ? ?; exact I. }
    eapply framed_uchar_store_load; exact (Hfocus heap Hrep). }
  exists group, (unmap_value group), (Znth (unmap_value group) rows 0),
    (unmap_value (Znth (unmap_value group) rows 0)).
  split; [exact Hgroup|]. split; [apply Htable; exact (proj1 Hgroup)|].
  split; [exact Hrow|]. split; [apply Htable; exact (proj1 Hrow)|].
  change (sched_new_priority group rows = sched_new_priority group rows mod 256).
  symmetry; apply Z.mod_small; pose proof (sched_new_priority_in_range group rows); lia.
Qed.

Lemma sched_new_heap_fragment_rep_post : forall sg group rows high heap,
  sched_new_rep sg group rows high heap ->
  exists final, sched_new_heap_fragment sg heap final /\
    sched_new_rep sg group rows (sched_new_priority group rows) final.
Proof.
  intros sg group rows high heap Hrep.
  pose proof (sched_new_heap_reads_from_rep sg group rows high heap Hrep) as Hreads.
  assert (Hsplit : sched_new_rep sg group rows high |--
    sg.(g_OSPrioHighRdy) # UChar |-> high **
      (sg.(g_OSRdyGrp) # UChar |-> group **
       UCharArray.full sg.(g_OSRdyTbl) 8 rows ** unmap_table_rep sg)).
  { unfold sched_new_rep; entailer!. }
  destruct (kernel_heap_framed_uchar_store _ _ (sched_new_priority group rows) _ heap
    ltac:(pose proof (sched_new_priority_in_range group rows); lia)
    (Hsplit heap Hrep)) as [final [Hrun Hpost]].
  exists final; split; [exists (sched_new_priority group rows); split; assumption|].
  assert (Hmerge : sg.(g_OSPrioHighRdy) # UChar |-> sched_new_priority group rows **
      (sg.(g_OSRdyGrp) # UChar |-> group **
       UCharArray.full sg.(g_OSRdyTbl) 8 rows ** unmap_table_rep sg) |--
    sched_new_rep sg group rows (sched_new_priority group rows)).
  { unfold sched_new_rep; entailer!. }
  exact (Hmerge final Hpost).
Qed.

Lemma sched_new_heap_fragment_rep_preservation : forall sg group rows high before after,
  sched_new_rep sg group rows high before -> sched_new_heap_fragment sg before after ->
  sched_new_rep sg group rows (sched_new_priority group rows) after.
Proof.
  intros sg group rows high before after Hrep Hrun.
  destruct (sched_new_heap_fragment_rep_post sg group rows high before Hrep)
    as [final [Hsource Hpost]].
  replace after with final by (eapply sched_new_heap_fragment_deterministic; eassumption).
  exact Hpost.
Qed.

Lemma sched_new_heap_fragment_frame_post : forall sg group rows high (frame : Assertion) heap,
  (sched_new_rep sg group rows high ** frame) heap ->
  exists final, sched_new_heap_fragment sg heap final /\
    (sched_new_rep sg group rows (sched_new_priority group rows) ** frame) final.
Proof.
  intros sg group rows high frame heap [owned [rest [Hjoin [Hrep Hframe]]]].
  destruct (sched_new_heap_fragment_rep_post sg group rows high owned Hrep)
    as [after [Hsource Hpost]].
  destruct (sched_new_heap_fragment_frame sg owned after rest heap Hsource Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  exists after, rest; split; [exact Hfinal|]; split; assumption.
Qed.
