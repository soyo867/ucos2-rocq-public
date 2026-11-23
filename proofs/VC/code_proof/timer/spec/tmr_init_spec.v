(** OSTmr_Init local components over the existing Timer and QCP owners.
    This library is not a contract or proof of the complete C function.
    Task/Create/InitTask source projection gaps are not caller premises here. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.timer Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Static layout source obligation, not an additional heap owner.  In particular
    the UINT_MAX endpoints are needed by MemClr's final post-increment.  The
    existing generic half-open region bound alone is insufficient. *)
Definition tmr_init_pool_layout (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig) = selected_kernel_configuration /\
  0 < sg.(g_OSTmrTbl) /\ sg.(g_OSTmrTbl) mod 4 = 0 /\
  sg.(g_OSTmrTbl) + 640 <= 4294967295 /\
  0 < sg.(g_OSTmrWheelTbl) /\ sg.(g_OSTmrWheelTbl) mod 4 = 0 /\
  sg.(g_OSTmrWheelTbl) + 56 <= 4294967295.

(** This is just the actual four-store intermediate image, not a new Timer
    lifecycle.  Its zero-valued fields and five defined padding bytes come from
    the first real MemClr, never from pure valid_timer_configuration. *)
Definition tmr_init_slot_image (kind state next name : Z) : TimerImage :=
  {| timerImageType := kind; timerImageCallback := 0; timerImageArg := 0;
     timerImageNext := next; timerImagePrev := 0; timerImageMatch := 0;
     timerImageDelay := 0; timerImagePeriod := 0; timerImageName := name;
     timerImageOption := 0; timerImageState := state;
     timerImagePadding := repeat (Some 0) 5 |}.

Definition tmr_init_slot_residual (p : Z) : Assertion :=
  store_optional_bytes (p + 1) [Some 0; Some 0; Some 0] **
  (p + 4) # Ptr |-> 0 ** (p + 8) # Ptr |-> 0 **
  (p + 16) # Ptr |-> 0 ** (p + 20) # UInt |-> 0 **
  (p + 24) # UInt |-> 0 ** (p + 28) # UInt |-> 0 **
  (p + 36) # UChar |-> 0 **
  store_optional_bytes (p + 38) [Some 0; Some 0].

Definition tmr_init_slot_cells p kind state next name : Assertion :=
  p # UChar |-> kind ** (p + 37) # UChar |-> state **
  (p + 12) # Ptr |-> next ** (p + 32) # Ptr |-> name **
  tmr_init_slot_residual p.

(* Component: reversible view, including all unchanged fields/padding. *)
Lemma tmr_init_slot_cells_rep_equiv : forall cfg p kind state next name,
  cfg.(cfgTimerNames) = true ->
  tmr_init_slot_cells p kind state next name --||--
  timer_object_rep cfg p (tmr_init_slot_image kind state next name).
Proof.
  intros cfg p kind state next name Hnames.
  unfold tmr_init_slot_cells, tmr_init_slot_residual, timer_object_rep,
    timer_option_offset, tmr_init_slot_image; rewrite Hnames; cbn.
  replace (p + 36 + 1) with (p + 37) by lia.
  replace (p + 36 + 2) with (p + 38) by lia.
  split; entailer!.
Qed.

(* Components; no duplicate byte owner is introduced by these views. *)
Lemma tmr_init_zero_padding_three : forall p,
  UCharArray.full p 3 [0; 0; 0] |--
  store_optional_bytes p [Some 0; Some 0; Some 0].
Proof. intros; unfold store_optional_bytes; apply UCharArray.full_to_mixed_full. Qed.

Lemma tmr_init_zero_padding_two : forall p,
  UCharArray.full p 2 [0; 0] |-- store_optional_bytes p [Some 0; Some 0].
Proof. intros; unfold store_optional_bytes; apply UCharArray.full_to_mixed_full. Qed.

Lemma tmr_init_zero_bytes_to_slot_cells : forall p,
  p mod 4 = 0 ->
  UCharArray.full p 40 (repeat_Z 0 40) |-- tmr_init_slot_cells p 0 0 0 0.
Proof.
  intros p Hmod.
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction p 1 40); [|lia].
  sep_apply (zero_bytes_to_store_uchar__tcb_zero_byte_reconstruction p).
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 1) 3 39); [|lia].
  sep_apply (tmr_init_zero_padding_three (p + 1)).
  replace (p + 1 + 3) with (p + 4) by lia.
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 4) 4 36); [|lia].
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction (p + 4));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  replace (p + 4 + 4) with (p + 8) by lia.
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 8) 4 32); [|lia].
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction (p + 8));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  replace (p + 8 + 4) with (p + 12) by lia.
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 12) 4 28); [|lia].
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction (p + 12));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  replace (p + 12 + 4) with (p + 16) by lia.
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 16) 4 24); [|lia].
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction (p + 16));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  replace (p + 16 + 4) with (p + 20) by lia.
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 20) 4 20); [|lia].
  sep_apply (zero_bytes_to_store_uint__tcb_zero_byte_reconstruction (p + 20));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  replace (p + 20 + 4) with (p + 24) by lia.
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 24) 4 16); [|lia].
  sep_apply (zero_bytes_to_store_uint__tcb_zero_byte_reconstruction (p + 24));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  replace (p + 24 + 4) with (p + 28) by lia.
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 28) 4 12); [|lia].
  sep_apply (zero_bytes_to_store_uint__tcb_zero_byte_reconstruction (p + 28));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  replace (p + 28 + 4) with (p + 32) by lia.
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 32) 4 8); [|lia].
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction (p + 32));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  replace (p + 32 + 4) with (p + 36) by lia.
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 36) 1 4); [|lia].
  sep_apply (zero_bytes_to_store_uchar__tcb_zero_byte_reconstruction (p + 36)).
  replace (p + 36 + 1) with (p + 37) by lia.
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 37) 1 3); [|lia].
  sep_apply (zero_bytes_to_store_uchar__tcb_zero_byte_reconstruction (p + 37)).
  replace (p + 37 + 1) with (p + 38) by lia.
  sep_apply (tmr_init_zero_padding_two (p + 38)).
  unfold tmr_init_slot_cells, tmr_init_slot_residual; entailer!.
Qed.

Definition tmr_init_wheel_zero_cell p : Assertion :=
  p # Ptr |-> 0 ** (p + 4) # UShort |-> 0 ** UCharArray.full (p + 6) 2 [0; 0].
Fixpoint tmr_init_wheel_zero (p : Z) (n : nat) : Assertion :=
  match n with
  | O => emp
  | S rest => tmr_init_wheel_zero_cell p ** tmr_init_wheel_zero (p + 8) rest
  end.

Lemma tmr_init_zero_bytes_to_wheel_cell : forall p,
  p mod 4 = 0 -> UCharArray.full p 8 (repeat_Z 0 8) |-- tmr_init_wheel_zero_cell p.
Proof.
  intros p Hmod.
  assert (Hmod2 : p mod 2 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hmod; [|lia].
    destruct Hmod as [k Hk]; exists (2 * k); lia. }
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction p 4 8); [|lia].
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction p Hmod).
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 4) 2 4); [|lia].
  sep_apply (zero_bytes_to_store_ushort__tcb_zero_byte_reconstruction (p + 4));
    [|rewrite Z.add_mod, Hmod2 by lia; reflexivity].
  replace (p + 4 + 2) with (p + 6) by lia.
  unfold tmr_init_wheel_zero_cell; entailer!.
Qed.

Lemma tmr_init_wheel_zero_to_rep : forall sg p n,
  tmr_init_wheel_zero p n |-- timer_wheel_rep_from sg p (repeat [] n).
Proof.
  intros sg p n; revert p; induction n; intro p; cbn [tmr_init_wheel_zero repeat timer_wheel_rep_from].
  - entailer!.
  - unfold tmr_init_wheel_zero_cell; cbn [timer_id_pointer List.length].
    sep_apply UCharArray.full_to_undef_full; sep_apply (IHn (p + 8)); entailer!.
Qed.

Lemma tmr_init_zero_bytes_to_wheel : forall p n,
  p mod 4 = 0 ->
  UCharArray.full p (8 * Z.of_nat n) (repeat_Z 0 (8 * Z.of_nat n)) |--
  tmr_init_wheel_zero p n.
Proof.
  intros p n; revert p; induction n; intros p Hmod.
  - cbn [tmr_init_wheel_zero]; change (8 * Z.of_nat O) with 0.
    change (repeat_Z 0 0) with (@nil Z); rewrite UCharArray.full_empty; entailer!.
  - rewrite Nat2Z.inj_succ.
    sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction p 8 (8 * Z.succ (Z.of_nat n)));
      [|lia].
    sep_apply (tmr_init_zero_bytes_to_wheel_cell p Hmod).
    replace (8 * Z.succ (Z.of_nat n) - 8) with (8 * Z.of_nat n) by lia.
    sep_apply (IHn (p + 8)); [|rewrite Z.add_mod, Hmod by lia; reflexivity].
    cbn [tmr_init_wheel_zero]; entailer!.
Qed.

(** Prefix contains precisely the initialized slots. The rightmost form makes
    the ix++ reassembly an append of one completed object. The tail remains
    zero bytes until focused; no whole valid Timer pool is claimed mid-loop. *)
Fixpoint tmr_init_prefix (sg : StableGlobVars) (name : Z) (count : nat) : Assertion :=
  match count with
  | O => emp
  | S previous => tmr_init_prefix sg name previous **
      timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg (Z.of_nat previous))
        (timer_initial_image sg name (Z.of_nat previous))
  end.
Definition tmr_init_zero_tail sg (ix : Z) : Assertion :=
  UCharArray.full (sg.(g_OSTmrTbl) + 40 * ix) (40 * (16 - ix))
    (repeat_Z 0 (40 * (16 - ix))).
Definition tmr_init_globals sg time used free root sem signal : Assertion :=
  sg.(g_OSTmrTime) # UInt |-> time ** sg.(g_OSTmrUsed) # UShort |-> used **
  sg.(g_OSTmrFree) # UShort |-> free ** sg.(g_OSTmrFreeList) # Ptr |-> root **
  sg.(g_OSTmrSem) # Ptr |-> sem ** sg.(g_OSTmrSemSignal) # Ptr |-> signal.
Definition tmr_init_loop sg name ix : Assertion :=
  coq_prop (0 <= ix <= 15) &&
  (tmr_init_prefix sg name (Z.to_nat ix) ** tmr_init_zero_tail sg ix **
   tmr_init_wheel_zero sg.(g_OSTmrWheelTbl) 7 ** tmr_init_globals sg 0 0 0 0 0 0).

Definition tmr_init_loop_focus sg name ix : Assertion :=
  tmr_init_prefix sg name (Z.to_nat ix) **
  tmr_init_slot_cells (timer_pool_addr sg ix) 0 0 0 0 **
  tmr_init_zero_tail sg (ix + 1) **
  tmr_init_wheel_zero sg.(g_OSTmrWheelTbl) 7 ** tmr_init_globals sg 0 0 0 0 0 0.

(* Each PC is retained even when writing zero over zero. stage 0 is before
   Time, stage 1 before Used, stage 2 before Free, stage 3 before FreeList,
   and stage 4 is the first point at which the pure pool state may be closed. *)
Definition tmr_init_four_globals sg (stage : nat) : Assertion :=
  tmr_init_globals sg 0 0 (if Nat.leb 3 stage then 16 else 0)
    (if Nat.leb 4 stage then sg.(g_OSTmrTbl) else 0) 0 0.
Definition tmr_init_before_globals sg name : Assertion :=
  tmr_init_prefix sg name 16 ** tmr_init_wheel_zero sg.(g_OSTmrWheelTbl) 7 **
  tmr_init_four_globals sg 0.
Definition tmr_init_after_globals sg name : Assertion :=
  tmr_init_prefix sg name 16 ** tmr_init_wheel_zero sg.(g_OSTmrWheelTbl) 7 **
  tmr_init_four_globals sg 4.

Lemma tmr_init_loop_focus_zero_slot : forall sg name ix,
  tmr_init_pool_layout sg -> 0 <= ix <= 15 ->
  tmr_init_loop sg name ix |-- tmr_init_loop_focus sg name ix.
Proof.
  intros sg name ix [Hcfg [Hbase [Hmod Hrest]]] Hix.
  assert (Haddr : timer_pool_addr sg ix = sg.(g_OSTmrTbl) + 40 * ix).
  { unfold timer_pool_addr, timer_object_size, timer_option_offset; rewrite Hcfg.
    change (g_OSTmrTbl sg + ix * 40 = g_OSTmrTbl sg + 40 * ix); lia. }
  assert (Hslotmod : (sg.(g_OSTmrTbl) + 40 * ix) mod 4 = 0).
  { rewrite Z.add_mod, Z.mul_mod, Hmod by lia; reflexivity. }
  unfold tmr_init_loop, tmr_init_loop_focus, tmr_init_zero_tail; Intros.
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction
    (sg.(g_OSTmrTbl) + 40 * ix) 40 (40 * (16 - ix))); [|lia].
  sep_apply (tmr_init_zero_bytes_to_slot_cells _ Hslotmod).
  rewrite Haddr.
  replace (sg.(g_OSTmrTbl) + 40 * ix + 40) with
    (sg.(g_OSTmrTbl) + 40 * (ix + 1)) by lia.
  replace (40 * (16 - ix) - 40) with (40 * (16 - (ix + 1))) by lia.
  entailer!.
Qed.

(* The finite cases are the selected 16-slot C array, not a bound on callbacks
   or interference. A generic Zrange proof can replace this small normalization. *)
Lemma tmr_init_loop_image_eq : forall sg name ix,
  sg.(osKernelConfig).(cfgMaxTimers) = 16 -> 0 <= ix < 15 ->
  timer_initial_image sg name ix =
  tmr_init_slot_image 100 0 (timer_pool_addr sg (ix + 1)) name.
Proof.
  intros sg name ix Hcapacity Hix.
  assert (Hcases : ix=0 \/ ix=1 \/ ix=2 \/ ix=3 \/ ix=4 \/ ix=5 \/
    ix=6 \/ ix=7 \/ ix=8 \/ ix=9 \/ ix=10 \/ ix=11 \/ ix=12 \/ ix=13 \/ ix=14) by lia.
  unfold timer_initial_image, tmr_init_slot_image; rewrite Hcapacity.
  repeat match type of Hcases with _ \/ _ => destruct Hcases as [Hcase|Hcases];
    [subst ix; reflexivity|] end.
  subst ix; reflexivity.
Qed.

Lemma tmr_init_tail_image_eq : forall sg name,
  sg.(osKernelConfig).(cfgMaxTimers) = 16 ->
  timer_initial_image sg name 15 = tmr_init_slot_image 100 0 0 name.
Proof. intros; unfold timer_initial_image, tmr_init_slot_image; rewrite H; reflexivity. Qed.

Lemma tmr_init_loop_merge_completed_slot : forall sg name ix,
  sg.(osKernelConfig).(cfgTimerNames) = true ->
  sg.(osKernelConfig).(cfgMaxTimers) = 16 -> 0 <= ix < 15 ->
  tmr_init_prefix sg name (Z.to_nat ix) **
  tmr_init_slot_cells (timer_pool_addr sg ix) 100 0 (timer_pool_addr sg (ix+1)) name **
  tmr_init_zero_tail sg (ix+1) ** tmr_init_wheel_zero sg.(g_OSTmrWheelTbl) 7 **
  tmr_init_globals sg 0 0 0 0 0 0 |-- tmr_init_loop sg name (ix+1).
Proof.
  intros sg name ix Hnames Hcapacity Hix.
  sep_apply_l_atomic (proj1 (tmr_init_slot_cells_rep_equiv (osKernelConfig sg)
    (timer_pool_addr sg ix) 100 0 (timer_pool_addr sg (ix + 1)) name Hnames)).
  rewrite <- (tmr_init_loop_image_eq sg name ix Hcapacity Hix).
  unfold tmr_init_loop.
  replace (Z.to_nat (ix+1)) with (S (Z.to_nat ix)) by lia.
  cbn [tmr_init_prefix].
  rewrite Z2Nat.id by lia; entailer!.
Qed.

Lemma tmr_init_tail_merge_completed_slot : forall sg name,
  sg.(osKernelConfig).(cfgTimerNames) = true ->
  sg.(osKernelConfig).(cfgMaxTimers) = 16 ->
  tmr_init_prefix sg name 15 **
  tmr_init_slot_cells (timer_pool_addr sg 15) 100 0 0 name **
  tmr_init_zero_tail sg 16 ** tmr_init_wheel_zero sg.(g_OSTmrWheelTbl) 7 **
  tmr_init_globals sg 0 0 0 0 0 0 |-- tmr_init_before_globals sg name.
Proof.
  intros sg name Hnames Hcapacity.
  sep_apply_l_atomic (proj1 (tmr_init_slot_cells_rep_equiv (osKernelConfig sg)
    (timer_pool_addr sg 15) 100 0 0 name Hnames)).
  rewrite <- (tmr_init_tail_image_eq sg name Hcapacity).
  unfold tmr_init_zero_tail; change (40*(16-16)) with 0.
  change (repeat_Z 0 0) with (@nil Z); rewrite UCharArray.full_empty.
  unfold tmr_init_before_globals, tmr_init_four_globals.
  change (tmr_init_prefix sg name 16) with
    (tmr_init_prefix sg name 15 **
      timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg 15) (timer_initial_image sg name 15)).
  cbn [Nat.leb]; entailer!.
Qed.

Lemma tmr_init_mem_clr_bounds : forall sg,
  tmr_init_pool_layout sg ->
  (0 <= 640 <= 65535 /\ 0 <= sg.(g_OSTmrTbl) /\
    sg.(g_OSTmrTbl) + 640 <= 4294967295) /\
  (0 <= 56 <= 65535 /\ 0 <= sg.(g_OSTmrWheelTbl) /\
    sg.(g_OSTmrWheelTbl) + 56 <= 4294967295).
Proof. intros sg [Hcfg [Ht [Hta [Hte [Hw [Hwa Hwe]]]]]]; lia. Qed.

Lemma tmr_init_uninitialized_arrays_equiv : forall sg,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  timer_uninitialized_rep sg --||--
  mem_clr_pre sg.(g_OSTmrTbl) 640 ** mem_clr_pre sg.(g_OSTmrWheelTbl) 56 **
  tmr_init_globals sg 0 0 0 0 0 0.
Proof.
  intros sg Hcfg; unfold timer_uninitialized_rep, timer_globals_rep,
    mem_clr_pre, tmr_init_globals, timer_object_size, timer_option_offset.
  rewrite Hcfg; cbn [cfgTimerNames cfgMaxTimers cfgTimerWheelSize
    selected_kernel_configuration timer_uninitialized timerFree timerFreeCount
    timerUsedCount timerTime timerSem timerSignalSem timer_id_pointer].
  split; entailer!.
Qed.

Lemma tmr_init_mem_clr_posts_to_loop : forall sg name,
  tmr_init_pool_layout sg ->
  mem_clr_post sg.(g_OSTmrTbl) 640 ** mem_clr_post sg.(g_OSTmrWheelTbl) 56 **
  tmr_init_globals sg 0 0 0 0 0 0 |-- tmr_init_loop sg name 0.
Proof.
  intros sg name [Hcfg [Ht [Hta [Hte [Hw [Hwa Hwe]]]]]].
  unfold mem_clr_post, tmr_init_loop, tmr_init_zero_tail.
  change (Z.to_nat 0) with O; cbn [tmr_init_prefix].
  replace (g_OSTmrTbl sg + 40 * 0) with (g_OSTmrTbl sg) by lia.
  change (40 * (16 - 0)) with 640.
  sep_apply (tmr_init_zero_bytes_to_wheel (g_OSTmrWheelTbl sg) 7 Hwa).
  entailer!.
Qed.

(** The finite support is the existing timerImages map.  The prefix does not
    become a second pool owner: the proof supplies exactly its 16 map cells. *)
Lemma tmr_init_prefix_to_images : forall sg name,
  sg.(osKernelConfig).(cfgMaxTimers) = 16 ->
  tmr_init_prefix sg name 16 |-- timer_images_rep sg (timer_pool_initialize sg name).
Proof.
  intros sg name Hcapacity.
  assert (Hdomain : forall i, In i (Zrange 0 16) <-> exists v,
    (if andb (0 <=? i) (i <? 16) then Some (timer_initial_image sg name i) else None) = Some v).
  { intro i; rewrite <- In_Zrange.
    destruct (andb (0 <=? i) (i <? 16)) eqn:Hi.
    - apply Bool.andb_true_iff in Hi; rewrite Z.leb_le, Z.ltb_lt in Hi.
      split; [intros; eexists; reflexivity|intros; tauto].
    - split; [|intros [v Hv]; discriminate].
      intros [Hlo Hhi].
      assert (andb (0 <=? i) (i <? 16) = true).
      { apply Bool.andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
      congruence. }
  pose proof (NoDup_Zrange 0 16) as Hnodup.
  unfold timer_images_rep, store_map.
  cbn [timer_pool_initialize timer_set_initialization timer_initial timerImages].
  rewrite Hcapacity.
  Exists (Zrange 0 16); entailer!.
  all: rewrite <- derivable1_iter_sepcon_r;
    cbn [Zrange Zrange_aux map fold_left tmr_init_prefix]; entailer!.
Qed.

Lemma tmr_init_after_globals_to_configured : forall sg name,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  tmr_init_after_globals sg name |-- timer_configured_rep sg (timer_pool_initialize sg name).
Proof.
  intros sg name Hcfg.
  assert (He : cfgTimerEnabled (osKernelConfig sg) = true) by (rewrite Hcfg; reflexivity).
  assert (Hcap : cfgMaxTimers (osKernelConfig sg) = 16) by (rewrite Hcfg; reflexivity).
  rewrite (timer_pool_initialized_configured_rep_eq sg (timer_pool_initialize sg name)
    He ltac:(discriminate)).
  unfold tmr_init_after_globals, timer_raw_rep.
  sep_apply (tmr_init_prefix_to_images sg name Hcap).
  sep_apply (tmr_init_wheel_zero_to_rep sg (g_OSTmrWheelTbl sg) 7).
  unfold tmr_init_four_globals, tmr_init_globals, timer_globals_rep.
  cbn [timer_pool_initialize timer_set_initialization timer_initial timerWheel timerFree
    timerFreeCount timerUsedCount timerTime timerSem timerSignalSem Nat.leb].
  rewrite Hcfg.
  change (timer_id_pointer sg (Zrange 0 (cfgMaxTimers selected_kernel_configuration)))
    with (timer_pool_addr sg 0).
  unfold timer_pool_addr; rewrite Z.mul_0_l, Z.add_0_r.
  cbn [cfgMaxTimers cfgTimerWheelSize selected_kernel_configuration]; entailer!.
Qed.

(** This is the first point where the actual spatial pool may be closed into
    the old kernel world. The non-Timer owner is reused, never regenerated. *)
Lemma tmr_init_after_globals_merge_world : forall sg before name,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg before -> before.(SchedState).(isRunning) = false ->
  before.(TimerState).(timerInitPhase) = TimerUninitialized ->
  tmr_init_after_globals sg name ** UCOS2_raw_rep_missing_timer sg before |--
  UCOS2_inv sg (replace_TimerS (timer_pool_initialize sg name) before).
Proof.
  intros sg before name Hcfg Hvalid Hstopped Hphase.
  sep_apply (tmr_init_after_globals_to_configured sg name Hcfg).
  apply (UCOS2_inv_merge_updated_timer sg before
    (replace_TimerS (timer_pool_initialize sg name) before)).
  - apply UCOS2_timer_pool_initialize_preserves_validity; try assumption.
    rewrite Hcfg; reflexivity.
  - reflexivity.
Qed.

(** Field-address/sizeof bindings still belong to the future canonical C
    annotation. Numeric byte offsets do not equate FET_alias with struct fields. *)


Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.timer_execution Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_api_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_init_task_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition tmr_init_record_lock_program (result : Z) : program UCOS2_Verify_State unit :=
  fun before observed after => observed = tt /\ exists timers,
    timer_record_lock_result before.(TimerState) result = Some timers /\
    after = replace_TimerS timers before.
Definition tmr_init_record_signal_program (result : Z) : program UCOS2_Verify_State unit :=
  fun before observed after => observed = tt /\ exists timers,
    timer_record_signal_result before.(TimerState) result = Some timers /\
    after = replace_TimerS timers before.

Definition tmr_init_after_lock_program critical sg invocation
  (tail : program UCOS2_Verify_State unit) : program UCOS2_Verify_State unit :=
  StateRelMonad.bind (sem_create_api_program critical sg invocation 0)
    (fun result => StateRelMonad.bind (tmr_init_record_signal_program result) (fun _ => tail)).
Definition tmr_init_semaphore_program critical sg invocation
  (tail : program UCOS2_Verify_State unit) : program UCOS2_Verify_State unit :=
  StateRelMonad.bind (sem_create_api_program critical sg invocation 1)
    (fun result => StateRelMonad.bind (tmr_init_record_lock_program result)
      (fun _ => tmr_init_after_lock_program critical sg invocation tail)).

Definition tmr_init_first_sem_continuation critical sg invocation tail
  (X : unit -> UCOS2_Verify_State -> Prop) : Z -> UCOS2_Verify_State -> Prop :=
  fun result current => safeExec (eq current)
    (StateRelMonad.bind (tmr_init_record_lock_program result)
      (fun _ => tmr_init_after_lock_program critical sg invocation tail)) X.
Definition tmr_init_second_sem_continuation tail
  (X : unit -> UCOS2_Verify_State -> Prop) : Z -> UCOS2_Verify_State -> Prop :=
  fun result current => safeExec (eq current)
    (StateRelMonad.bind (tmr_init_record_signal_program result) (fun _ => tail)) X.

(* Same arbitrary X. This lemma does not assert that either call returns. *)
Lemma tmr_init_bind_safe_continuation : forall A B
  (first : program UCOS2_Verify_State A) (next : A -> program UCOS2_Verify_State B)
  before (X : B -> UCOS2_Verify_State -> Prop),
  safeExec (eq before) (StateRelMonad.bind first next) X ->
  safeExec (eq before) first
    (fun result current => safeExec (eq current) (next result) X).
Proof.
  intros A B first next before X [start [Hstart Hsafe]]; subst start.
  exists before; split; [reflexivity|].
  intros result current Hfirst; exists current; split; [reflexivity|].
  intros final_value final Hnext; apply (Hsafe final_value final).
  exists result, current; auto.
Qed.

Lemma tmr_init_first_sem_safe : forall critical sg invocation tail before X,
  safeExec (eq before) (tmr_init_semaphore_program critical sg invocation tail) X ->
  sem_create_api_safe critical sg invocation 1 before
    (tmr_init_first_sem_continuation critical sg invocation tail X).
Proof.
  intros; unfold sem_create_api_safe, tmr_init_first_sem_continuation.
  eapply tmr_init_bind_safe_continuation; exact H.
Qed.

Lemma tmr_init_second_sem_safe : forall critical sg invocation tail before X,
  safeExec (eq before) (tmr_init_after_lock_program critical sg invocation tail) X ->
  sem_create_api_safe critical sg invocation 0 before
    (tmr_init_second_sem_continuation tail X).
Proof.
  intros; unfold sem_create_api_safe, tmr_init_second_sem_continuation.
  eapply tmr_init_bind_safe_continuation; exact H.
Qed.

(** Instantiate the actual callee's X with source AND continuation. The source
    conjunct is proved from the same run; it is not assumed as a second hidden
    specification. This lets the caller project Timer phase at actual current. *)
Definition tmr_init_sem_source_continuation critical sg invocation count before K :=
  fun result current =>
    sem_create_api_program critical sg invocation count before result current /\ K result current.

Lemma tmr_init_sem_safe_retain_source : forall critical sg invocation count before K,
  sem_create_api_safe critical sg invocation count before K ->
  sem_create_api_safe critical sg invocation count before
    (tmr_init_sem_source_continuation critical sg invocation count before K).
Proof.
  intros critical sg invocation count before K [start [Hstart Hsafe]]; subst start.
  exists before; split; [reflexivity|].
  intros result current Hrun; split; [exact Hrun|apply Hsafe; exact Hrun].
Qed.

(** The returned call/current are the existential results in main's TRUE post.
    In particular never rebuild returned from original's stack fragments and
    never replace current by before. No heap or continuation map is copied. *)
Lemma tmr_init_sem_post_open : forall environment critical sg original mask result K,
  sem_create_api_call_post environment critical sg original mask result K |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\ K result current) &&
    q_create_save_input environment critical QCreateNoPrivate emp sg returned mask current.
Proof.
  intros; unfold sem_create_api_call_post, mbox_create_call_post; Intros returned current.
  assert (Hret : q_create_return_safe current result K) by tauto.
  destruct Hret as [start [Hstart Hsafe]]; subst start.
  assert (HK : K result current) by (apply (Hsafe result current); split; reflexivity).
  Exists returned current; entailer!.
Qed.

(** Exactly the Sem world's existing empty local family, not a conversion of
    arbitrary owned locals to emp. Both None and Some descriptors are retained. *)
Lemma tmr_init_empty_continuation_local_eq :
  task_create_continuation_local (fun _ => emp) = (fun _ => emp).
Proof.
  apply functional_extensionality; intro descriptor.
  unfold task_create_continuation_local.
  destruct descriptor.(armv7a_continuation_call); reflexivity.
Qed.

Lemma tmr_init_sem_world_task_world_equiv : forall environment critical sg call mask current,
  q_create_save_input environment critical QCreateNoPrivate emp sg call mask current --||--
  task_create_continuation_input environment critical (fun _ => emp) sg call mask current.
Proof.
  intros; unfold q_create_save_input, q_create_resources, q_create_owned,
    kernel_continuation_call_closed, kernel_continuation_inv,
    task_create_continuation_input.
  rewrite tmr_init_empty_continuation_local_eq.
  unfold critical_region_outside.
  rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
  unfold UCOS2_inv; split; entailer!.
Qed.

Lemma tmr_init_private_stores_timer_trace : forall critical sg invocation eid writes before result after,
  q_create_private_stores_interleaved critical sg invocation eid writes before result after ->
  timer_public_trace sg before.(TimerState) after.(TimerState).
Proof.
  intros critical sg invocation eid writes; induction writes as [|[field value] rest IH];
    intros before result after Hrun.
  - destruct Hrun as [_ [Hinterval _]].
    eapply critical_region_interval_timer_public_trace; exact Hinterval.
  - destruct Hrun as [entry [allocation [[Hinterval _] [Hlookup Hrest]]]].
    eapply timer_public_trace_trans.
    + eapply critical_region_interval_timer_public_trace; exact Hinterval.
    + exact (IH _ _ _ Hrest).
Qed.

Lemma tmr_init_event_allocation_timer_eq : forall before result after,
  event_create_allocate_critical before result after -> after.(TimerState) = before.(TimerState).
Proof.
  intros before result after Hrun; unfold event_create_allocate_critical in Hrun.
  destruct before.(EventState).(unUsedEventStates).
  - destruct Hrun as [_ ->]; reflexivity.
  - destruct Hrun as [image [_ [_ ->]]]; reflexivity.
Qed.

Lemma tmr_init_sem_timer_trace : forall critical sg invocation count before result after,
  sem_create_api_program critical sg invocation count before result after ->
  timer_public_trace sg before.(TimerState) after.(TimerState).
Proof.
  intros critical sg invocation count before result after Hrun.
  unfold sem_create_api_program in Hrun.
  destruct (Z.ltb 0 before.(IntrState).(intNesting)).
  - destruct Hrun as [_ ->]; constructor.
  - destruct Hrun as [entry [allocated [detached [Hfirst [Halloc Htail]]]]].
    pose proof (tmr_init_event_allocation_timer_eq _ _ _ Halloc) as Hdetached.
    eapply timer_public_trace_trans.
    + eapply critical_region_interval_timer_public_trace; exact Hfirst.
    + destruct allocated as [[eid image]|].
      * destruct Htail as [resumed [initialized [allocation [[Hresume _]
          [Hstores [Hlookup [Hresult ->]]]]]]].
        cbn [replace_EventS TimerState].
        rewrite <- Hdetached.
        eapply timer_public_trace_trans.
        -- eapply critical_region_interval_timer_public_trace; exact Hresume.
        -- eapply tmr_init_private_stores_timer_trace; exact Hstores.
      * destruct Htail as [_ Hreturn]; rewrite <- Hdetached.
        eapply critical_region_interval_timer_public_trace; exact Hreturn.
Qed.

Lemma tmr_init_sem_preserves_phase : forall critical sg invocation count before result after,
  sem_create_api_program critical sg invocation count before result after ->
  after.(TimerState).(timerInitPhase) = before.(TimerState).(timerInitPhase).
Proof.
  intros; apply (proj1 (timer_public_trace_public_storage_frame sg _ _
    (tmr_init_sem_timer_trace _ _ _ _ _ _ _ H))).
Qed.

(** The existing cross invariant rules out OSRunning=true while an enabled
    Timer has an unfinished phase. No new boot/control promise is put in CPU. *)
Lemma tmr_init_unfinished_is_stopped : forall sg current,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> UCOS2_state_inv sg current ->
  current.(TimerState).(timerInitPhase) <> TimerInitializationFinished ->
  current.(SchedState).(isRunning) = false.
Proof.
  intros sg current He Hvalid Hphase.
  assert (Hcross : timer_running_initialization_consistency sg current).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, cross_module_consistency,
      cross_module_consistency_with_wait in Hvalid; tauto. }
  destruct current.(SchedState).(isRunning) eqn:Hrun; [|reflexivity].
  exfalso; apply Hphase; apply Hcross; assumption.
Qed.

Lemma tmr_init_sem_program_same_call_eq : forall critical sg original returned count,
  task_tcb_init_stack_same_call returned original ->
  sem_create_api_program critical sg returned.(os_sched_call_invocation) count =
  sem_create_api_program critical sg original.(os_sched_call_invocation) count.
Proof. intros critical sg original returned count [Hi _]; rewrite Hi; reflexivity. Qed.

(** The stronger observation is installed through the real SemCreate X,
    not through an alternative callee declaration. *)
Lemma tmr_init_sem_pre_retain_source : forall environment critical sg call mask before count K,
  sem_create_api_input_facts critical sg call before count K ->
  q_create_save_input environment critical QCreateNoPrivate emp sg call mask before |--
  sem_create_api_call_pre environment critical sg call mask before count
    (tmr_init_sem_source_continuation critical sg call.(os_sched_call_invocation) count before K).
Proof.
  intros environment critical sg call mask before count K [Hbinding [Hcount Hsafe]].
  pose proof (tmr_init_sem_safe_retain_source _ _ _ _ _ _ Hsafe) as Hsafe_source.
  unfold sem_create_api_call_pre, sem_create_api_input_facts; entailer!.
Qed.

Lemma tmr_init_sem_post_phase : forall environment critical sg original mask count before result K,
  sem_create_api_call_post environment critical sg original mask result
    (tmr_init_sem_source_continuation critical sg original.(os_sched_call_invocation) count before K) |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\ K result current /\
      current.(TimerState).(timerInitPhase) = before.(TimerState).(timerInitPhase)) &&
    q_create_save_input environment critical QCreateNoPrivate emp sg returned mask current.
Proof.
  intros; sep_apply (tmr_init_sem_post_open environment critical sg original mask result
    (tmr_init_sem_source_continuation critical sg original.(os_sched_call_invocation) count before K)).
  Intros returned current.
  assert (Hrun : sem_create_api_program critical sg original.(os_sched_call_invocation)
    count before result current) by (unfold tmr_init_sem_source_continuation in *; tauto).
  pose proof (tmr_init_sem_preserves_phase _ _ _ _ _ _ _ Hrun) as Hphase.
  Exists returned current; unfold tmr_init_sem_source_continuation in *; entailer!.
Qed.

Lemma tmr_init_record_lock_safe_step : forall critical sg invocation tail before result timers X,
  tmr_init_first_sem_continuation critical sg invocation tail X result before ->
  timer_record_lock_result before.(TimerState) result = Some timers ->
  safeExec (eq (replace_TimerS timers before))
    (tmr_init_after_lock_program critical sg invocation tail) X.
Proof.
  intros critical sg invocation tail before result timers X [start [Hstart Hsafe]] Hstep; subst start.
  exists (replace_TimerS timers before); split; [reflexivity|].
  intros value after Htail; apply (Hsafe value after).
  exists tt, (replace_TimerS timers before); split; [|exact Htail].
  split; [reflexivity|exists timers; auto].
Qed.

Lemma tmr_init_record_signal_safe_step : forall tail before result timers X,
  tmr_init_second_sem_continuation tail X result before ->
  timer_record_signal_result before.(TimerState) result = Some timers ->
  safeExec (eq (replace_TimerS timers before)) tail X.
Proof.
  intros tail before result timers X [start [Hstart Hsafe]] Hstep; subst start.
  exists (replace_TimerS timers before); split; [reflexivity|].
  intros value after Htail; apply (Hsafe value after).
  exists tt, (replace_TimerS timers before); split; [|exact Htail].
  split; [reflexivity|exists timers; auto].
Qed.

Definition tmr_init_timer_without_lock sg timers : Assertion :=
  timer_pool_rep sg timers ** sg.(g_OSTmrTime) # UInt |-> timers.(timerTime) **
  sg.(g_OSTmrSemSignal) # Ptr |-> timers.(timerSignalSem).
Definition tmr_init_timer_without_signal sg timers : Assertion :=
  timer_pool_rep sg timers ** sg.(g_OSTmrTime) # UInt |-> timers.(timerTime) **
  sg.(g_OSTmrSem) # Ptr |-> timers.(timerSem).

Lemma tmr_init_timer_split_lock : forall sg timers,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timers.(timerInitPhase) = TimerPoolInitialized ->
  timer_configured_rep sg timers --||--
  sg.(g_OSTmrSem) # Ptr |-> timers.(timerSem) ** tmr_init_timer_without_lock sg timers.
Proof.
  intros sg timers He Hphase; unfold timer_configured_rep; rewrite He, Hphase.
  unfold tmr_init_timer_without_lock, timer_raw_rep, timer_globals_rep, timer_pool_rep;
    split; entailer!.
Qed.

Lemma tmr_init_timer_split_signal : forall sg timers,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timers.(timerInitPhase) = TimerLockAttempted ->
  timer_configured_rep sg timers --||--
  sg.(g_OSTmrSemSignal) # Ptr |-> timers.(timerSignalSem) ** tmr_init_timer_without_signal sg timers.
Proof.
  intros sg timers He Hphase; unfold timer_configured_rep; rewrite He, Hphase.
  unfold tmr_init_timer_without_signal, timer_raw_rep, timer_globals_rep, timer_pool_rep;
    split; entailer!.
Qed.

Lemma tmr_init_timer_merge_lock : forall sg before result after,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_record_lock_result before result = Some after ->
  sg.(g_OSTmrSem) # Ptr |-> result ** tmr_init_timer_without_lock sg before |--
  timer_configured_rep sg after.
Proof.
  intros sg before result after He Hstep; unfold timer_record_lock_result in Hstep.
  destruct (timerInitPhase before); try discriminate; inversion Hstep; subst after.
  unfold timer_configured_rep; rewrite He.
  unfold tmr_init_timer_without_lock, timer_raw_rep, timer_globals_rep, timer_pool_rep,
    timer_images_rep; cbn [timer_set_initialization timerInitPhase timerImages timerWheel
      timerFree timerFreeCount timerUsedCount timerTime timerSem timerSignalSem]; entailer!.
Qed.

Lemma tmr_init_timer_merge_signal : forall sg before result after,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_record_signal_result before result = Some after ->
  sg.(g_OSTmrSemSignal) # Ptr |-> result ** tmr_init_timer_without_signal sg before |--
  timer_configured_rep sg after.
Proof.
  intros sg before result after He Hstep; unfold timer_record_signal_result in Hstep.
  destruct (timerInitPhase before); try discriminate; inversion Hstep; subst after.
  unfold timer_configured_rep; rewrite He.
  unfold tmr_init_timer_without_signal, timer_raw_rep, timer_globals_rep, timer_pool_rep,
    timer_images_rep; cbn [timer_set_initialization timerInitPhase timerImages timerWheel
      timerFree timerFreeCount timerUsedCount timerTime timerSem timerSignalSem]; entailer!.
Qed.

(** Residual of ONE actual returned world at either handle store. It owns
    the same current non-Timer state and parked map, not an entry snapshot. *)
Definition tmr_init_sem_store_frame environment sg call mask current timer_rest : Assertion :=
  coq_prop (UCOS2_state_inv sg current /\
    task_stack_live_coverage current.(TskState) (task_stack_call_active_key call)) &&
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) call mask ** timer_rest **
   UCOS2_raw_rep_missing_timer sg current **
   armv7a_task_stack_continuations environment.(task_stack_call_continuations)
     current.(TskState) current.(TskState).(parkedTaskStacks)).

Lemma tmr_init_sem_world_split_lock : forall environment critical sg call mask current,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  current.(TimerState).(timerInitPhase) = TimerPoolInitialized ->
  q_create_save_input environment critical QCreateNoPrivate emp sg call mask current |--
  sg.(g_OSTmrSem) # Ptr |-> current.(TimerState).(timerSem) **
  tmr_init_sem_store_frame environment sg call mask current
    (tmr_init_timer_without_lock sg current.(TimerState)).
Proof.
  intros environment critical sg call mask current He Hphase.
  rewrite q_create_save_input_open, UCOS2_inv_split_timer.
  rewrite (tmr_init_timer_split_lock sg current.(TimerState) He Hphase).
  unfold tmr_init_sem_store_frame, q_create_owned; entailer!.
Qed.

Lemma tmr_init_sem_world_split_signal : forall environment critical sg call mask current,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  current.(TimerState).(timerInitPhase) = TimerLockAttempted ->
  q_create_save_input environment critical QCreateNoPrivate emp sg call mask current |--
  sg.(g_OSTmrSemSignal) # Ptr |-> current.(TimerState).(timerSignalSem) **
  tmr_init_sem_store_frame environment sg call mask current
    (tmr_init_timer_without_signal sg current.(TimerState)).
Proof.
  intros environment critical sg call mask current He Hphase.
  rewrite q_create_save_input_open, UCOS2_inv_split_timer.
  rewrite (tmr_init_timer_split_signal sg current.(TimerState) He Hphase).
  unfold tmr_init_sem_store_frame, q_create_owned; entailer!.
Qed.

Lemma tmr_init_sem_world_merge_lock : forall environment critical sg call mask current result timers,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_record_lock_result current.(TimerState) result = Some timers ->
  sg.(g_OSTmrSem) # Ptr |-> result **
  tmr_init_sem_store_frame environment sg call mask current
    (tmr_init_timer_without_lock sg current.(TimerState)) |--
  q_create_save_input environment critical QCreateNoPrivate emp sg call mask
    (replace_TimerS timers current).
Proof.
  intros environment critical sg call mask current result timers He Hstep.
  unfold tmr_init_sem_store_frame; Intros.
  assert (Hvalid : UCOS2_state_inv sg current) by tauto.
  assert (Hphase : timerInitPhase (TimerState current) <> TimerInitializationFinished).
  { unfold timer_record_lock_result in Hstep; destruct (timerInitPhase (TimerState current)); discriminate. }
  pose proof (tmr_init_unfinished_is_stopped sg current He Hvalid Hphase) as Hstopped.
  pose proof (UCOS2_timer_record_lock_preserves_validity sg current result timers
    He Hvalid Hstopped Hstep) as Hafter.
  sep_apply (tmr_init_timer_merge_lock sg current.(TimerState) result timers He Hstep).
  pose proof (UCOS2_inv_merge_updated_timer sg current (replace_TimerS timers current)
    Hafter eq_refl) as Hmerge.
  change (timer_configured_rep sg timers ** UCOS2_raw_rep_missing_timer sg current |--
    UCOS2_inv sg (replace_TimerS timers current)) in Hmerge.
  sep_apply Hmerge.
  rewrite q_create_save_input_open; unfold q_create_owned;
    cbn [replace_TimerS TskState]; entailer!.
Qed.

Lemma tmr_init_sem_world_merge_signal : forall environment critical sg call mask current result timers,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_record_signal_result current.(TimerState) result = Some timers ->
  sg.(g_OSTmrSemSignal) # Ptr |-> result **
  tmr_init_sem_store_frame environment sg call mask current
    (tmr_init_timer_without_signal sg current.(TimerState)) |--
  q_create_save_input environment critical QCreateNoPrivate emp sg call mask
    (replace_TimerS timers current).
Proof.
  intros environment critical sg call mask current result timers He Hstep.
  unfold tmr_init_sem_store_frame; Intros.
  assert (Hvalid : UCOS2_state_inv sg current) by tauto.
  assert (Hphase : timerInitPhase (TimerState current) <> TimerInitializationFinished).
  { unfold timer_record_signal_result in Hstep; destruct (timerInitPhase (TimerState current)); discriminate. }
  pose proof (tmr_init_unfinished_is_stopped sg current He Hvalid Hphase) as Hstopped.
  pose proof (UCOS2_timer_record_signal_preserves_validity sg current result timers
    He Hvalid Hstopped Hstep) as Hafter.
  sep_apply (tmr_init_timer_merge_signal sg current.(TimerState) result timers He Hstep).
  pose proof (UCOS2_inv_merge_updated_timer sg current (replace_TimerS timers current)
    Hafter eq_refl) as Hmerge.
  change (timer_configured_rep sg timers ** UCOS2_raw_rep_missing_timer sg current |--
    UCOS2_inv sg (replace_TimerS timers current)) in Hmerge.
  sep_apply Hmerge.
  rewrite q_create_save_input_open; unfold q_create_owned;
    cbn [replace_TimerS TskState]; entailer!.
Qed.

(** Remaining tail composition, NOT an installed assumption:
    [tail] must be instantiated at the second returned call, not an old
    physical context. Same-call only preserves invocation/origin/stack,
    not arbitrary stack fragments. The empty-local equivalence above uses
    the actual Sem world and covers both None and Some descriptors.
    Static stack, unmap and the one literal resource remain outside these
    calls. P4 phase and the historical creation receipt must come from real
    Task producers before timer_finish_initialization can be constructed. *)


Require Import Ucos2Verify.lib.timer_execution Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_name_set_spec.

Definition tmr_init_phase_frame (before after : UCOS2_Verify_State) : Prop :=
  after.(TimerState).(timerInitPhase) = before.(TimerState).(timerInitPhase).

Lemma tmr_init_phase_frame_refl : forall state, tmr_init_phase_frame state state.
Proof. intros; reflexivity. Qed.

Lemma tmr_init_phase_frame_trans : forall before middle after,
  tmr_init_phase_frame before middle -> tmr_init_phase_frame middle after ->
  tmr_init_phase_frame before after.
Proof. unfold tmr_init_phase_frame; intros; congruence. Qed.

Lemma tmr_init_interval_phase_frame : forall critical sg invocation before after,
  critical_region_interval critical sg invocation before after ->
  tmr_init_phase_frame before after.
Proof.
  intros critical sg invocation before after Hsource.
  exact (proj1 (timer_public_trace_public_storage_frame sg _ _
    (critical_region_interval_timer_public_trace _ _ _ _ _ Hsource))).
Qed.

(** Additive candidate observation at the existing producer, preserving the
    entire old consequence. No new CPU field, stronger caller Require or
    definition change of task_tcb_init_call_preserved is made here. *)
Definition tmr_init_tcb_call_observation sg invocation before after : Prop :=
  task_tcb_init_call_preserved sg invocation before after /\
  tmr_init_phase_frame before after.

Lemma tmr_init_interval_tcb_call_observation : forall critical sg invocation before after,
  critical_region_interval critical sg invocation before after ->
  tmr_init_tcb_call_observation sg invocation before after.
Proof.
  intros; split.
  - eapply task_tcb_init_interval_preserves_call; exact H.
  - eapply tmr_init_interval_phase_frame; exact H.
Qed.

Lemma tmr_init_tcb_call_observation_forget : forall sg invocation before after,
  tmr_init_tcb_call_observation sg invocation before after ->
  task_tcb_init_call_preserved sg invocation before after.
Proof. intros sg invocation before after [H _]; exact H. Qed.

(* The final NameSet edge ALREADY retains the real source intervals. Its
   ordinary 67/0 outcomes and earlier errors need no stronger Task/CPU post. *)
Lemma tmr_init_name_set_step_phase_frame : forall prio name before error after,
  task_name_set_step prio name before error after -> tmr_init_phase_frame before after.
Proof. intros; destruct H; reflexivity. Qed.

Lemma tmr_init_name_set_result_phase_frame : forall critical sg invocation request name before error after,
  task_name_set_result critical sg invocation request name before error after ->
  tmr_init_phase_frame before after.
Proof.
  intros critical sg invocation request name before error after Hresult.
  destruct Hresult as [[_ [_ ->]]|[[_ [_ [_ ->]]]|[[_ [_ [_ [_ ->]]]]|Hprotected]]];
    try apply tmr_init_phase_frame_refl.
  destruct Hprotected as [_ [_ [_ [acquired [prio [released [Hacquire [_ [Hstep Hreturn]]]]]]]]].
  eapply tmr_init_phase_frame_trans.
  - eapply tmr_init_interval_phase_frame; exact Hacquire.
  - eapply tmr_init_phase_frame_trans.
    + eapply tmr_init_name_set_step_phase_frame; exact Hstep.
    + eapply tmr_init_interval_phase_frame; exact Hreturn.
Qed.

Lemma tmr_init_name_set_post_phase_frame : forall critical sg invocation request name before error after X,
  task_name_set_post critical sg invocation request name before error after X ->
  tmr_init_phase_frame before after.
Proof. intros; eapply tmr_init_name_set_result_phase_frame; exact (proj1 H). Qed.

(* REQUIRED BUT NOT CLAIMED HERE:
   - transport this observation through actual StackInit repeated-store source
     induction and its modular output, not from runtime_history alone;
   - preserve it through the two actual TCBInit protected mutations and the
     source intervals erased by task_tcb_init_call_result;
   - at final TCB Restore derive released->current from the actual Htrace;
   - propagate same-current consequence through Create[Ext] and InitTask's
     actual QCP declarations and source high-level programs;
   - NameSet's own selected source transformer/intervals give the final phase
     equality. Its registered NameState is framed, but the targeted TCB name
     field changes, so the old complete TCB image is not a frame;
   - retain the actual success publication slot/generation at its real released
     snapshot. No priority-61/name lookup is a creation receipt.
 *)

Require Import Coq.Strings.String.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_init_task_timer_phase_spec.
Local Open Scope string_scope.

(** The pool prefix is established by the actual clear/link/scalar C cuts.
    These programs supply no spatial resource and no successful-call premise. *)
Definition tmr_init_pool_program sg name : program UCOS2_Verify_State unit :=
  fun before result after => result = tt /\
    after = replace_TimerS (timer_pool_initialize sg name) before.

Definition tmr_init_task_receipt_program environment critical sg entry base task_return
  lower old_frame upper call mask LitMap
  : program UCOS2_Verify_State (option (TaskID * nat)) :=
  fun before receipt after => exists create_error middle name_error,
    tmr_init_task_source_receipt environment critical sg entry base task_return
      lower old_frame upper call mask LitMap before create_error middle receipt /\
    task_name_set_program critical sg call.(os_sched_call_invocation)
      61 (LitMap "uC/OS-II Tmr") middle name_error after.

Definition tmr_init_finish_program receipt : program UCOS2_Verify_State unit :=
  fun before result after => result = tt /\ exists timers,
    timer_finish_initialization before.(TimerState) receipt = Some timers /\
    after = replace_TimerS timers before.

Definition tmr_init_task_finish_program environment critical sg entry base task_return
  lower old_frame upper call mask LitMap : program UCOS2_Verify_State unit :=
  StateRelMonad.bind
    (tmr_init_task_receipt_program environment critical sg entry base task_return
      lower old_frame upper call mask LitMap)
    (fun receipt => tmr_init_finish_program receipt).

Definition tmr_init_source_program environment critical sg entry base task_return
  lower old_frame upper call mask LitMap : program UCOS2_Verify_State unit :=
  StateRelMonad.bind (tmr_init_pool_program sg (LitMap "?"))
    (fun _ => tmr_init_semaphore_program critical sg call.(os_sched_call_invocation)
      (tmr_init_task_finish_program environment critical sg entry base task_return
        lower old_frame upper call mask LitMap)).

(** InitTask really returns unit. The same-source receipt is obtained from
    its phase post, not inferred from its final priority/name. *)
Definition tmr_init_task_finish_continuation environment critical sg entry base task_return
  lower old_frame upper call mask LitMap before
  (X : unit -> UCOS2_Verify_State -> Prop) : unit -> UCOS2_Verify_State -> Prop :=
  fun _ current => forall receipt,
    tmr_init_task_receipt_program environment critical sg entry base task_return
      lower old_frame upper call mask LitMap before receipt current ->
    safeExec (eq current) (tmr_init_finish_program receipt) X.

Lemma tmr_init_pool_safe_step : forall environment critical sg entry base task_return
  lower old_frame upper call mask LitMap before X,
  safeExec (eq before) (tmr_init_source_program environment critical sg entry base task_return
    lower old_frame upper call mask LitMap) X ->
  safeExec (eq (replace_TimerS (timer_pool_initialize sg (LitMap "?")) before))
    (tmr_init_semaphore_program critical sg call.(os_sched_call_invocation)
      (tmr_init_task_finish_program environment critical sg entry base task_return
        lower old_frame upper call mask LitMap)) X.
Proof.
  intros environment critical sg entry base task_return lower old_frame upper call mask LitMap before X
    [start [Hstart Hsafe]]; subst start.
  eexists; split; [reflexivity|]. intros result after Htail.
  apply (Hsafe result after); exists tt, (replace_TimerS (timer_pool_initialize sg (LitMap "?")) before).
  split; [split; reflexivity|exact Htail].
Qed.

Lemma tmr_init_task_receipt_program_erasure : forall environment critical sg entry base task_return
  lower old_frame upper call mask LitMap before after,
  (exists receipt, tmr_init_task_receipt_program environment critical sg entry base task_return
    lower old_frame upper call mask LitMap before receipt after) <->
  tmr_init_task_sequence environment critical sg entry base task_return
    lower old_frame upper call mask LitMap before tt after.
Proof.
  intros; split.
  - intros [receipt [create_error [middle [name_error [[Hcreate _] Hname]]]]].
    exists create_error, middle; split; [exact Hcreate|].
    exists name_error, after; split; [exact Hname|split; reflexivity].
  - intros [create_error [middle [Hcreate [name_error [named [Hname [Hunit Hend]]]]]]].
    subst after.
    destruct (tmr_init_task_create_source_has_receipt environment critical sg entry base task_return
      lower old_frame upper call mask LitMap before create_error middle Hcreate) as [receipt Hreceipt].
    exists receipt, create_error, middle, name_error; auto.
Qed.

Lemma tmr_init_task_finish_safe_call : forall environment critical sg entry base task_return
  lower old_frame upper call mask LitMap before X,
  safeExec (eq before) (tmr_init_task_finish_program environment critical sg entry base task_return
    lower old_frame upper call mask LitMap) X ->
  tmr_init_task_safe environment critical sg entry base task_return lower old_frame upper call mask LitMap before
    (tmr_init_task_finish_continuation environment critical sg entry base task_return
      lower old_frame upper call mask LitMap before X).
Proof.
  intros environment critical sg entry base task_return lower old_frame upper call mask LitMap before X
    [start [Hstart Hsafe]]; subst start.
  exists before; split; [reflexivity|].
  intros result current Hrun receipt Hreceipt.
  exists current; split; [reflexivity|]. intros final_value final Hfinish.
  apply (Hsafe final_value final); exists receipt, current; auto.
Qed.

(** These equalities concern pure programs only. The actual returned call
    retains its own stack fragments in every spatial interface. *)
Lemma tmr_init_save_program_same_call_eq : forall environment critical sg first second mask,
  task_tcb_init_stack_same_call first second ->
  task_create_save_program environment critical sg first mask =
  task_create_save_program environment critical sg second mask.
Proof.
  intros environment critical sg first second mask [Hi [Ho Hs]].
  unfold task_create_save_program, kernel_call_save_source,
    task_tcb_init_runtime_history, kernel_call_normal_return,
    task_tcb_init_stack_same_call, kernel_call_stack_available.
  rewrite Hi, Ho, Hs; reflexivity.
Qed.

Lemma tmr_init_reserved_same_call_eq : forall args first second,
  task_tcb_init_stack_same_call first second ->
  task_create_stack_reserved args first = task_create_stack_reserved args second.
Proof.
  intros args first second [Hi [Ho Hs]]. unfold task_create_stack_reserved;
    rewrite Hi, Ho; reflexivity.
Qed.

Lemma tmr_init_create_program_same_call_eq : forall environment critical sg region args task_return
  lower upper name first second mask,
  task_tcb_init_stack_same_call first second ->
  task_create_program environment critical sg region args task_return lower upper name first mask =
  task_create_program environment critical sg region args task_return lower upper name second mask.
Proof.
  intros environment critical sg region args task_return lower upper name first second mask Hsame.
  unfold task_create_program.
  rewrite (tmr_init_save_program_same_call_eq _ _ _ _ _ _ Hsame).
  unfold task_create_acquired_program.
  rewrite (tmr_init_reserved_same_call_eq args first second Hsame); reflexivity.
Qed.

Lemma tmr_init_success_source_same_call_eq : forall environment critical sg entry base task_return
  lower old_frame upper first second mask LitMap before after receipt,
  task_tcb_init_stack_same_call first second ->
  (tmr_init_task_success_source environment critical sg entry base task_return lower old_frame upper
    first mask LitMap before after receipt =
   tmr_init_task_success_source environment critical sg entry base task_return lower old_frame upper
    second mask LitMap before after receipt).
Proof.
  intros environment critical sg entry base task_return lower old_frame upper first second mask LitMap before after receipt Hsame.
  unfold tmr_init_task_success_source.
  rewrite (tmr_init_save_program_same_call_eq _ _ _ _ _ _ Hsame),
    (tmr_init_reserved_same_call_eq _ _ _ Hsame); reflexivity.
Qed.

Lemma tmr_init_task_receipt_program_same_call_eq : forall environment critical sg entry base task_return
  lower old_frame upper first second mask LitMap,
  task_tcb_init_stack_same_call first second ->
  tmr_init_task_receipt_program environment critical sg entry base task_return lower old_frame upper first mask LitMap =
  tmr_init_task_receipt_program environment critical sg entry base task_return lower old_frame upper second mask LitMap.
Proof.
  intros environment critical sg entry base task_return lower old_frame upper first second mask LitMap Hsame.
  apply functional_extensionality; intro source_state.
  apply functional_extensionality; intro receipt.
  apply functional_extensionality; intro final_state.
  unfold tmr_init_task_receipt_program, tmr_init_task_source_receipt,
    tmr_init_task_create_program, tmr_init_task_success_source.
  rewrite (tmr_init_create_program_same_call_eq _ _ _ _ _ _ _ _ _ _ _ _ Hsame).
  rewrite (tmr_init_save_program_same_call_eq _ _ _ _ _ _ Hsame).
  rewrite (tmr_init_reserved_same_call_eq _ _ _ Hsame), (proj1 Hsame).
  reflexivity.
Qed.

Lemma tmr_init_task_finish_program_same_call_eq : forall environment critical sg entry base task_return
  lower old_frame upper first second mask LitMap,
  task_tcb_init_stack_same_call first second ->
  tmr_init_task_finish_program environment critical sg entry base task_return lower old_frame upper first mask LitMap =
  tmr_init_task_finish_program environment critical sg entry base task_return lower old_frame upper second mask LitMap.
Proof.
  intros; unfold tmr_init_task_finish_program.
  rewrite (tmr_init_task_receipt_program_same_call_eq _ _ _ _ _ _ _ _ _ _ _ _ _ H); reflexivity.
Qed.

(** Fixed source arguments, packaged only to keep the caller's cut interfaces
    readable. This record adds neither a resource nor a platform guarantee. *)
Record TmrInitContext := {
  tmr_init_environment : TaskStackCallEnvironment;
  tmr_init_critical : CriticalRegionResources;
  tmr_init_sg : StableGlobVars;
  tmr_init_entry_address : Z;
  tmr_init_stack_base : Z;
  tmr_init_return_address : Z;
  tmr_init_mask : Z;
  tmr_init_lower : list (option Z);
  tmr_init_old_frame : list (option Z);
  tmr_init_upper : list (option Z);
  tmr_init_literals : string -> Z;
  tmr_init_missing_literals : list string
}.
Definition tmr_init_empty_local (_ : Armv7aContinuation) : Assertion := emp.
Definition tmr_init_question p := p.(tmr_init_literals) "?".
Definition tmr_init_tail p call :=
  tmr_init_task_finish_program p.(tmr_init_environment) p.(tmr_init_critical) p.(tmr_init_sg)
    p.(tmr_init_entry_address) p.(tmr_init_stack_base) p.(tmr_init_return_address)
    p.(tmr_init_lower) p.(tmr_init_old_frame) p.(tmr_init_upper) call
    p.(tmr_init_mask) p.(tmr_init_literals).
Definition tmr_init_program p call :=
  tmr_init_source_program p.(tmr_init_environment) p.(tmr_init_critical) p.(tmr_init_sg)
    p.(tmr_init_entry_address) p.(tmr_init_stack_base) p.(tmr_init_return_address)
    p.(tmr_init_lower) p.(tmr_init_old_frame) p.(tmr_init_upper) call
    p.(tmr_init_mask) p.(tmr_init_literals).
Definition tmr_init_task_continuation p call before X :=
  tmr_init_task_finish_continuation p.(tmr_init_environment) p.(tmr_init_critical) p.(tmr_init_sg)
    p.(tmr_init_entry_address) p.(tmr_init_stack_base) p.(tmr_init_return_address)
    p.(tmr_init_lower) p.(tmr_init_old_frame) p.(tmr_init_upper) call
    p.(tmr_init_mask) p.(tmr_init_literals) before X.

(** Exact selected C address interpretation. Like the existing Alloc binding,
    these are caller/loader obligations, not equalities postulated as axioms.
    The MemClr endpoints are included independently of the half-open layout. *)
Definition tmr_init_source_binding (p : TmrInitContext) : Prop :=
  let sg := p.(tmr_init_sg) in
  tmr_init_pool_layout sg /\ sizeof_alias_type "os_tmr" = 40 /\
  sizeof_alias_type "os_tmr_wheel" = 8 /\
  &("OSTmrTbl") = sg.(g_OSTmrTbl) /\ &("OSTmrWheelTbl") = sg.(g_OSTmrWheelTbl) /\
  &("OSTmrTime") = sg.(g_OSTmrTime) /\ &("OSTmrUsed") = sg.(g_OSTmrUsed) /\
  &("OSTmrFree") = sg.(g_OSTmrFree) /\ &("OSTmrFreeList") = sg.(g_OSTmrFreeList) /\
  &("OSTmrSem") = sg.(g_OSTmrSem) /\ &("OSTmrSemSignal") = sg.(g_OSTmrSemSignal) /\
  p.(tmr_init_entry_address) = &("OSTmr_Task") /\
  p.(tmr_init_stack_base) = &("OSTmrTaskStk") /\
  p.(tmr_init_return_address) = &("OS_TaskReturn") /\
  (forall i, 0 <= i < 16 ->
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (timer_pool_addr sg i) (FET_alias "os_tmr")) "OSTmrType")) = timer_pool_addr sg i /\
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (timer_pool_addr sg i) (FET_alias "os_tmr")) "OSTmrState")) = timer_pool_addr sg i + 37 /\
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (timer_pool_addr sg i) (FET_alias "os_tmr")) "OSTmrNext")) = timer_pool_addr sg i + 12 /\
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (timer_pool_addr sg i) (FET_alias "os_tmr")) "OSTmrName")) = timer_pool_addr sg i + 32) /\
  mbox_create_source_binding sg /\
  task_create_stack_global_addresses sg &("OSIntNesting") &("OSTCBPrioTbl") &("OSRunning") /\
  task_tcb_init_global_addresses sg &("OSTCBFreeList") &("OSTCBList") &("OSTCBPrioTbl")
    &("OSRdyGrp") &("OSRdyTbl") &("OSTaskCtr") /\
  os_sched_global_addresses sg &("OSIntNesting") &("OSLockNesting") &("OSPrioHighRdy") &("OSPrioCur")
    &("OSTCBHighRdy") &("OSTCBPrioTbl") &("OSCtxSwCtr") &("OSUnMapTbl") &("OSRdyGrp") &("OSRdyTbl") /\
  task_name_set_addresses sg &("OSTCBPrioTbl") &("OSTCBCur") &("OSIntNesting") /\
  task_name_set_layout sg /\ kernel_sched_ready_clients p.(tmr_init_critical) /\
  kernel_tcb_stack_field_layout sg.

Definition tmr_init_entry_facts p call state : Prop :=
  task_invocation_active state.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
  task_create_stack_no_reservation state call.(os_sched_call_invocation) /\
  valid_task_stack_region (tmr_init_task_stack_region p.(tmr_init_stack_base)) /\
  Zlength p.(tmr_init_lower) = tmr_init_task_frame_first p.(tmr_init_stack_base) /\
  Zlength p.(tmr_init_old_frame) = 16 /\
  Zlength p.(tmr_init_upper) = 112 - tmr_init_task_frame_first p.(tmr_init_stack_base) /\
  0 <= p.(tmr_init_entry_address) < 4294967296 /\
  0 <= p.(tmr_init_return_address) < 4294967296 /\
  task_create_name_registered (tmr_init_question p) state /\
  readable_name state.(NameState) (p.(tmr_init_literals) "uC/OS-II Tmr") tmr_init_task_name_chars.
Definition tmr_init_static_resources p : Assertion :=
  task_stack_storage (tmr_init_task_stack_region p.(tmr_init_stack_base))
    (p.(tmr_init_lower) ++ p.(tmr_init_old_frame) ++ p.(tmr_init_upper)) **
  unmap_table_rep p.(tmr_init_sg) **
  GlobalStrings_missing p.(tmr_init_literals) p.(tmr_init_missing_literals).
Definition tmr_init_world p call state : Assertion :=
  q_create_save_input p.(tmr_init_environment) p.(tmr_init_critical) QCreateNoPrivate emp
    p.(tmr_init_sg) call p.(tmr_init_mask) state.
Definition tmr_init_entry_resources p call state : Assertion :=
  tmr_init_task_entry p.(tmr_init_environment) p.(tmr_init_critical) tmr_init_empty_local p.(tmr_init_sg)
    p.(tmr_init_entry_address) p.(tmr_init_stack_base) p.(tmr_init_return_address)
    p.(tmr_init_lower) p.(tmr_init_old_frame) p.(tmr_init_upper) call p.(tmr_init_mask)
    p.(tmr_init_literals) p.(tmr_init_missing_literals) state.
Definition tmr_init_pre p call initial (X : unit -> UCOS2_Verify_State -> Prop) : Assertion :=
  coq_prop (tmr_init_source_binding p /\ initial.(TimerState).(timerInitPhase) = TimerUninitialized /\
    tmr_init_task_stopped initial /\ safeExec (eq initial) (tmr_init_program p call) X) &&
  tmr_init_entry_resources p call initial.

Definition tmr_init_pool_residual p call initial : Assertion :=
  tmr_init_sem_store_frame p.(tmr_init_environment) p.(tmr_init_sg) call p.(tmr_init_mask) initial emp **
  tmr_init_static_resources p.
Definition tmr_init_pool_context p call initial X : Assertion :=
  coq_prop (tmr_init_source_binding p /\ tmr_init_entry_facts p call initial /\
    initial.(TimerState).(timerInitPhase) = TimerUninitialized /\ tmr_init_task_stopped initial /\
    safeExec (eq initial) (tmr_init_program p call) X) && tmr_init_pool_residual p call initial.
Definition tmr_init_pool_literal_residual p call initial X : Assertion :=
  coq_prop (tmr_init_source_binding p) &&
  ((store_stringLit (tmr_init_question p) "?" **
   GlobalStrings_missing p.(tmr_init_literals) p.(tmr_init_missing_literals)) -*
  tmr_init_pool_context p call initial X).
Definition tmr_init_slot_context sg name ix : Assertion :=
  tmr_init_prefix sg name (Z.to_nat ix) **
  tmr_init_slot_residual (timer_pool_addr sg ix) ** tmr_init_zero_tail sg (ix + 1) **
  tmr_init_wheel_zero sg.(g_OSTmrWheelTbl) 7 ** tmr_init_globals sg 0 0 0 0 0 0.
Definition tmr_init_globals_context sg name : Assertion :=
  tmr_init_prefix sg name 16 ** tmr_init_wheel_zero sg.(g_OSTmrWheelTbl) 7.

Definition tmr_init_sem_continuation p original (stage : bool) X : Z -> UCOS2_Verify_State -> Prop :=
  if stage then
    tmr_init_first_sem_continuation p.(tmr_init_critical) p.(tmr_init_sg)
      original.(os_sched_call_invocation) (tmr_init_tail p original) X
  else tmr_init_second_sem_continuation (tmr_init_tail p original) X.
Definition tmr_init_sem_stage_phase (stage : bool) := if stage then TimerPoolInitialized else TimerLockAttempted.
Definition tmr_init_sem_count (stage : bool) : Z := if stage then 1 else 0.
Definition tmr_init_sem_call_continuation p call before stage K :=
  tmr_init_sem_source_continuation p.(tmr_init_critical) p.(tmr_init_sg)
    call.(os_sched_call_invocation) (tmr_init_sem_count stage) before K.

(** The derived views below preserve the complete actual SemCreate source
    continuation. The caller's assignment is deliberately NOT part of it. *)
Definition tmr_init_sem_pre p call before stage K : Assertion :=
  coq_prop (tmr_init_source_binding p /\ tmr_init_entry_facts p call before /\
    before.(TimerState).(timerInitPhase) = tmr_init_sem_stage_phase stage) &&
  sem_create_api_call_pre p.(tmr_init_environment) p.(tmr_init_critical) p.(tmr_init_sg)
    call p.(tmr_init_mask) before (tmr_init_sem_count stage)
    (tmr_init_sem_call_continuation p call before stage K).
Definition tmr_init_sem_return_facts p original before stage K result returned current : Prop :=
  tmr_init_source_binding p /\ task_tcb_init_stack_same_call returned original /\
  sem_create_api_program p.(tmr_init_critical) p.(tmr_init_sg) original.(os_sched_call_invocation)
    (tmr_init_sem_count stage) before result current /\ K result current /\
  current.(TimerState).(timerInitPhase) = tmr_init_sem_stage_phase stage /\
  tmr_init_entry_facts p returned current.
Definition tmr_init_sem_current_value (stage : bool) current :=
  if stage then current.(TimerState).(timerSem) else current.(TimerState).(timerSignalSem).
Definition tmr_init_sem_return_frame p returned current (stage : bool) : Assertion :=
  tmr_init_sem_store_frame p.(tmr_init_environment) p.(tmr_init_sg) returned p.(tmr_init_mask) current
    (if stage then tmr_init_timer_without_lock p.(tmr_init_sg) current.(TimerState)
     else tmr_init_timer_without_signal p.(tmr_init_sg) current.(TimerState)).
Definition tmr_init_sem_next_state (stage : bool) current result :=
  replace_TimerS
    (if stage then timer_set_initialization current.(TimerState) TimerLockAttempted result
        current.(TimerState).(timerSignalSem) current.(TimerState).(timerTask)
     else timer_set_initialization current.(TimerState) TimerSignalAttempted
        current.(TimerState).(timerSem) result current.(TimerState).(timerTask)) current.
Definition tmr_init_after_pool p initial :=
  replace_TimerS (timer_pool_initialize p.(tmr_init_sg) (tmr_init_question p)) initial.

Definition tmr_init_task_pre p call before X : Assertion :=
  coq_prop (tmr_init_source_binding p /\ before.(TimerState).(timerInitPhase) = TimerSignalAttempted /\
    tmr_init_task_stopped before /\
    tmr_init_task_safe p.(tmr_init_environment) p.(tmr_init_critical) p.(tmr_init_sg)
      p.(tmr_init_entry_address) p.(tmr_init_stack_base) p.(tmr_init_return_address)
      p.(tmr_init_lower) p.(tmr_init_old_frame) p.(tmr_init_upper) call p.(tmr_init_mask)
      p.(tmr_init_literals) before (tmr_init_task_continuation p call before X)) &&
  tmr_init_entry_resources p call before.
Definition tmr_init_task_return p call before X : Assertion :=
  coq_prop (tmr_init_source_binding p /\ before.(TimerState).(timerInitPhase) = TimerSignalAttempted) &&
  tmr_init_task_phase_post p.(tmr_init_environment) p.(tmr_init_critical) tmr_init_empty_local p.(tmr_init_sg)
    p.(tmr_init_entry_address) p.(tmr_init_stack_base) p.(tmr_init_return_address)
    p.(tmr_init_lower) p.(tmr_init_old_frame) p.(tmr_init_upper) call p.(tmr_init_mask)
    p.(tmr_init_literals) p.(tmr_init_missing_literals) before (tmr_init_task_continuation p call before X).
Definition tmr_init_post p original (X : unit -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX call before returned middle create_error receipt current name_error timers,
    coq_prop (task_tcb_init_stack_same_call call original /\
      task_tcb_init_stack_same_call returned call /\
      tmr_init_task_source_receipt p.(tmr_init_environment) p.(tmr_init_critical) p.(tmr_init_sg)
        p.(tmr_init_entry_address) p.(tmr_init_stack_base) p.(tmr_init_return_address)
        p.(tmr_init_lower) p.(tmr_init_old_frame) p.(tmr_init_upper) call p.(tmr_init_mask)
        p.(tmr_init_literals) before create_error middle receipt /\
      task_name_set_program p.(tmr_init_critical) p.(tmr_init_sg) call.(os_sched_call_invocation)
        61 (p.(tmr_init_literals) "uC/OS-II Tmr") middle name_error current /\
      timer_finish_initialization current.(TimerState) receipt = Some timers /\
      timers.(timerInitPhase) = TimerInitializationFinished /\
      UCOS2_state_inv p.(tmr_init_sg) (replace_TimerS timers current) /\
      safeExec (eq (replace_TimerS timers current)) (StateRelMonad.ret tt) X) &&
    (coq_prop (tmr_init_task_phase_created p.(tmr_init_environment) p.(tmr_init_critical) p.(tmr_init_sg)
       p.(tmr_init_entry_address) p.(tmr_init_stack_base) p.(tmr_init_return_address)
       p.(tmr_init_lower) p.(tmr_init_old_frame) p.(tmr_init_upper) call p.(tmr_init_mask)
       p.(tmr_init_literals) before (tmr_init_task_continuation p call before X)
       returned middle create_error receipt) **
     coq_prop (task_name_set_post p.(tmr_init_critical) p.(tmr_init_sg) returned.(os_sched_call_invocation)
       61 (p.(tmr_init_literals) "uC/OS-II Tmr") middle name_error current
       (tmr_init_task_name_continuation (tmr_init_task_continuation p call before X))) **
     task_name_set_closed p.(tmr_init_environment).(task_stack_call_platform) p.(tmr_init_critical) p.(tmr_init_sg)
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) p.(tmr_init_mask)
       (replace_TimerS timers current) **
     tmr_init_task_create_residual p.(tmr_init_environment) tmr_init_empty_local p.(tmr_init_sg)
       p.(tmr_init_entry_address) p.(tmr_init_stack_base) p.(tmr_init_return_address)
       p.(tmr_init_lower) p.(tmr_init_old_frame) p.(tmr_init_upper) returned middle create_error **
     GlobalStrings_missing p.(tmr_init_literals) p.(tmr_init_missing_literals)).

Definition tmr_init_call_facts invocation before after : Prop :=
  before.(NameState) = after.(NameState) /\
  (forall origin, task_invocation_active before.(TskState) invocation origin ->
     task_invocation_active after.(TskState) invocation origin) /\
  (task_create_stack_no_reservation before invocation ->
     task_create_stack_no_reservation after invocation).
Lemma tmr_init_call_facts_refl : forall invocation state,
  tmr_init_call_facts invocation state state.
Proof. intros; split; [reflexivity|]; split; auto. Qed.
Lemma tmr_init_call_facts_trans : forall invocation before middle after,
  tmr_init_call_facts invocation before middle -> tmr_init_call_facts invocation middle after ->
  tmr_init_call_facts invocation before after.
Proof.
  intros invocation before middle after [Hnames1 [Hactive1 Hnone1]] [Hnames2 [Hactive2 Hnone2]].
  split; [congruence|]; split.
  - intros origin Hactive; apply Hactive2, Hactive1; exact Hactive.
  - intros Hnone; apply Hnone2, Hnone1; exact Hnone.
Qed.
Lemma tmr_init_event_update_call_facts : forall invocation state events,
  tmr_init_call_facts invocation state (replace_EventS events state).
Proof. intros; split; [reflexivity|]; split; auto. Qed.
Lemma tmr_init_interval_call_facts : forall critical sg invocation before after,
  UCOS2_state_inv sg before -> critical_region_interval critical sg invocation before after ->
  tmr_init_call_facts invocation before after.
Proof.
  intros critical sg invocation before after Hvalid Htrace.
  destruct (critical_region_interval_transports_resources _ _ _ _ _ Htrace Hvalid)
    as [_ [Hframe Hactive]].
  split; [eapply critical_region_interval_preserves_name_state; exact Htrace|].
  split; [exact Hactive|].
  intros Hnone priority entry Hget Hinv.
  assert (Hreverse : task_creation_frame invocation after.(TskState) before.(TskState)).
  { unfold task_creation_frame in *; symmetry; exact Hframe. }
  pose proof (task_creation_frame_lookup _ _ _ _ _ Hreverse Hget Hinv) as Hbefore.
  exact (Hnone priority entry Hbefore Hinv).
Qed.
Lemma tmr_init_allocate_call_facts : forall invocation before result after,
  event_create_allocate_critical before result after -> tmr_init_call_facts invocation before after.
Proof.
  intros invocation before result after Hrun; unfold event_create_allocate_critical in Hrun.
  destruct before.(EventState).(unUsedEventStates).
  - destruct Hrun as [_ ->]; apply tmr_init_call_facts_refl.
  - destruct Hrun as [image [_ [_ ->]]]; apply tmr_init_event_update_call_facts.
Qed.
Lemma tmr_init_private_stores_call_facts : forall critical sg invocation eid writes before result after,
  UCOS2_state_inv sg before ->
  q_create_private_stores_interleaved critical sg invocation eid writes before result after ->
  tmr_init_call_facts invocation before after.
Proof.
  intros critical sg invocation eid writes; induction writes as [|[field value] rest IH];
    intros before result after Hvalid Hrun.
  - destruct Hrun as [_ [Htrace _]]; eapply tmr_init_interval_call_facts; eassumption.
  - destruct Hrun as [entry [allocation [[Htrace Howned] [Hget Htail]]]].
    pose proof (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Htrace Hvalid)) as Hentry.
    pose proof (UCOS2_event_private_write_preserves_validity sg entry eid allocation field
      (Some value) Hentry Hget) as Hwritten.
    eapply tmr_init_call_facts_trans; [eapply tmr_init_interval_call_facts; eassumption|].
    eapply tmr_init_call_facts_trans; [apply tmr_init_event_update_call_facts|].
    eapply IH; eassumption.
Qed.
Lemma tmr_init_sem_call_facts : forall critical sg invocation count before result after,
  UCOS2_state_inv sg before -> sem_create_api_program critical sg invocation count before result after ->
  tmr_init_call_facts invocation before after.
Proof.
  intros critical sg invocation count before result after Hvalid Hrun.
  unfold sem_create_api_program in Hrun; destruct (Z.ltb 0 before.(IntrState).(intNesting)).
  - destruct Hrun as [_ ->]; apply tmr_init_call_facts_refl.
  - destruct Hrun as [entry [allocated [detached [Htrace [Hallocate Hreturn]]]]].
    pose proof (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Htrace Hvalid)) as Hentry.
    pose proof (event_create_allocate_critical_preserves_validity sg entry allocated detached Hentry Hallocate) as Hdetached.
    eapply tmr_init_call_facts_trans; [eapply tmr_init_interval_call_facts; eassumption|].
    eapply tmr_init_call_facts_trans; [eapply tmr_init_allocate_call_facts; exact Hallocate|].
    destruct allocated as [[eid image]|].
    + destruct Hreturn as [resumed [initialized [allocation [[Hresume Hprivate] [Hstores [_ [_ ->]]]]]]].
      pose proof (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Hresume Hdetached)) as Hresumed.
      eapply tmr_init_call_facts_trans; [eapply tmr_init_interval_call_facts; eassumption|].
      eapply tmr_init_call_facts_trans; [eapply tmr_init_private_stores_call_facts; eassumption|].
      apply tmr_init_event_update_call_facts.
    + destruct Hreturn as [_ Hreturn]; eapply tmr_init_interval_call_facts; eassumption.
Qed.

Lemma tmr_init_entry_facts_transport : forall p original returned before after count result,
  UCOS2_state_inv p.(tmr_init_sg) before ->
  task_tcb_init_stack_same_call returned original ->
  sem_create_api_program p.(tmr_init_critical) p.(tmr_init_sg) original.(os_sched_call_invocation)
    count before result after ->
  tmr_init_entry_facts p original before -> tmr_init_entry_facts p returned after.
Proof.
  intros p original returned before after count result Hvalid [Hi [Ho Hstack]] Hrun Hfacts.
  destruct (tmr_init_sem_call_facts _ _ _ _ _ _ _ Hvalid Hrun) as [Hnames [Hactive Hnone]].
  unfold tmr_init_entry_facts in *; rewrite Hi, Ho.
  destruct Hfacts as [Ha [Hn [Hr [Hl [Hf [Hu [He [Ht [Hregistered Hread]]]]]]]]].
  pose proof (Hactive _ Ha) as Ha_after.
  pose proof (Hnone Hn) as Hn_after.
  pose proof (task_create_name_registered_transport _ _ _ Hnames Hregistered) as Hregistered_after.
  assert (Hread_after : readable_name after.(NameState) (p.(tmr_init_literals) "uC/OS-II Tmr")
    tmr_init_task_name_chars) by (rewrite <- Hnames; exact Hread).
  tauto.
Qed.

Lemma tmr_init_source_binding_config : forall p,
  tmr_init_source_binding p -> p.(tmr_init_sg).(osKernelConfig) = selected_kernel_configuration.
Proof. intros p H; exact (proj1 (proj1 H)). Qed.

Lemma tmr_init_entry_open : forall p call state,
  tmr_init_entry_resources p call state |--
  coq_prop (tmr_init_entry_facts p call state) &&
  (tmr_init_world p call state ** tmr_init_static_resources p).
Proof.
  intros p call state; unfold tmr_init_entry_resources, tmr_init_task_entry; Intros.
  sep_apply_l_atomic (tmr_init_task_name_input_open p.(tmr_init_environment) p.(tmr_init_critical)
    tmr_init_empty_local p.(tmr_init_sg) call p.(tmr_init_mask) p.(tmr_init_literals)
    p.(tmr_init_missing_literals) state); Intros.
  unfold tmr_init_world, tmr_init_static_resources, tmr_init_empty_local.
  rewrite (tmr_init_sem_world_task_world_equiv p.(tmr_init_environment) p.(tmr_init_critical)
    p.(tmr_init_sg) call p.(tmr_init_mask) state).
  unfold tmr_init_entry_facts, tmr_init_question; entailer!; tauto.
Qed.

Lemma tmr_init_entry_close : forall p call state,
  tmr_init_entry_facts p call state ->
  tmr_init_world p call state ** tmr_init_static_resources p |--
  tmr_init_entry_resources p call state.
Proof.
  intros p call state Hfacts.
  unfold tmr_init_world, tmr_init_static_resources, tmr_init_entry_resources, tmr_init_task_entry.
  rewrite (tmr_init_sem_world_task_world_equiv p.(tmr_init_environment) p.(tmr_init_critical)
    p.(tmr_init_sg) call p.(tmr_init_mask) state).
  assert (Hname : task_create_continuation_input p.(tmr_init_environment) p.(tmr_init_critical)
      tmr_init_empty_local p.(tmr_init_sg) call p.(tmr_init_mask) state **
      GlobalStrings_missing p.(tmr_init_literals) p.(tmr_init_missing_literals) |--
    tmr_init_task_name_input p.(tmr_init_environment) p.(tmr_init_critical) tmr_init_empty_local
      p.(tmr_init_sg) call p.(tmr_init_mask) p.(tmr_init_literals) p.(tmr_init_missing_literals) state).
  { unfold tmr_init_task_name_input; Right; unfold tmr_init_entry_facts, tmr_init_question in Hfacts;
      entailer!; tauto. }
  unfold tmr_init_empty_local in Hname.
  sep_apply Hname; unfold tmr_init_entry_facts in Hfacts; entailer!; tauto.
Qed.

Lemma tmr_init_pre_split_pool : forall p call initial X,
  tmr_init_pre p call initial X |--
  timer_uninitialized_rep p.(tmr_init_sg) ** tmr_init_pool_context p call initial X.
Proof.
  intros p call initial X; unfold tmr_init_pre; Intros.
  assert (Hbinding : tmr_init_source_binding p) by tauto.
  assert (Hphase : initial.(TimerState).(timerInitPhase) = TimerUninitialized) by tauto.
  pose proof (tmr_init_source_binding_config p Hbinding) as Hconfig.
  assert (Henabled : p.(tmr_init_sg).(osKernelConfig).(cfgTimerEnabled) = true).
  { rewrite Hconfig; reflexivity. }
  sep_apply (tmr_init_entry_open p call initial); Intros.
  unfold tmr_init_world; rewrite q_create_save_input_open, UCOS2_inv_split_timer.
  unfold timer_configured_rep; rewrite Henabled, Hphase.
  unfold tmr_init_pool_context, tmr_init_pool_residual, tmr_init_sem_store_frame,
    q_create_owned; entailer!; tauto.
Qed.

Lemma tmr_init_sem_post_view : forall p original before stage K result,
  tmr_init_source_binding p -> UCOS2_state_inv p.(tmr_init_sg) before ->
  tmr_init_entry_facts p original before ->
  before.(TimerState).(timerInitPhase) = tmr_init_sem_stage_phase stage ->
  sem_create_api_call_post p.(tmr_init_environment) p.(tmr_init_critical) p.(tmr_init_sg)
    original p.(tmr_init_mask) result (tmr_init_sem_call_continuation p original before stage K) |--
  EX returned current,
    coq_prop (tmr_init_sem_return_facts p original before stage K result returned current) &&
    ((if stage then p.(tmr_init_sg).(g_OSTmrSem) else p.(tmr_init_sg).(g_OSTmrSemSignal)) # Ptr |->
       tmr_init_sem_current_value stage current **
     tmr_init_sem_return_frame p returned current stage).
Proof.
  intros p original before stage K result Hbinding Hvalid Hentry Hphase.
  unfold tmr_init_sem_call_continuation.
  sep_apply (tmr_init_sem_post_open p.(tmr_init_environment) p.(tmr_init_critical) p.(tmr_init_sg)
    original p.(tmr_init_mask) result
    (tmr_init_sem_source_continuation p.(tmr_init_critical) p.(tmr_init_sg)
      original.(os_sched_call_invocation) (tmr_init_sem_count stage) before K)).
  Intros returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  assert (Hrun : sem_create_api_program p.(tmr_init_critical) p.(tmr_init_sg)
    original.(os_sched_call_invocation) (tmr_init_sem_count stage) before result current)
    by (unfold tmr_init_sem_source_continuation in *; tauto).
  assert (Hcurrent_entry : tmr_init_entry_facts p returned current).
  { eapply tmr_init_entry_facts_transport; eassumption. }
  pose proof (tmr_init_sem_preserves_phase _ _ _ _ _ _ _ Hrun) as Hcurrent_phase.
  assert (Hstage : current.(TimerState).(timerInitPhase) = tmr_init_sem_stage_phase stage)
    by congruence.
  assert (Henabled : p.(tmr_init_sg).(osKernelConfig).(cfgTimerEnabled) = true).
  { rewrite (tmr_init_source_binding_config p Hbinding); reflexivity. }
  Exists returned current.
  unfold tmr_init_sem_return_facts, tmr_init_sem_source_continuation in *.
  destruct stage; cbn [tmr_init_sem_current_value tmr_init_sem_return_frame tmr_init_sem_stage_phase] in *.
  - sep_apply (tmr_init_sem_world_split_lock p.(tmr_init_environment) p.(tmr_init_critical)
      p.(tmr_init_sg) returned p.(tmr_init_mask) current Henabled ltac:(congruence)); entailer!; tauto.
  - sep_apply (tmr_init_sem_world_split_signal p.(tmr_init_environment) p.(tmr_init_critical)
      p.(tmr_init_sg) returned p.(tmr_init_mask) current Henabled ltac:(congruence)); entailer!; tauto.
Qed.

Lemma tmr_init_name_result_preserves_validity : forall critical sg invocation name before error current chars,
  UCOS2_state_inv sg before -> readable_name before.(NameState) name chars ->
  task_name_set_result critical sg invocation 61 name before error current ->
  UCOS2_state_inv sg current.
Proof.
  intros critical sg invocation name before error current chars Hvalid Hread Hresult.
  unfold task_name_set_result in Hresult.
  destruct Hresult as [[Hbad _]|[[_ [_ [_ ->]]]|[[_ [_ [_ [_ ->]]]]|Hresult]]];
    try lia; try exact Hvalid.
  destruct Hresult as [_ [_ [_ [acquired [prio [released [Hacquire [_ [Hstep Hrelease]]]]]]]]].
  pose proof (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Hacquire Hvalid)) as Hacquired.
  assert (Hread_acquired : readable_name acquired.(NameState) name chars).
  { rewrite <- (critical_region_interval_preserves_name_state _ _ _ _ _ Hacquire); exact Hread. }
  assert (Hreleased : UCOS2_state_inv sg released).
  { inversion Hstep; subst; try exact Hacquired.
    eapply task_name_set_preserves_invariant; [exact Hacquired| |exact Hread_acquired].
    unfold task_name_set_target in *; tauto. }
  exact (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Hrelease Hreleased)).
Qed.

Lemma tmr_init_timer_finish_rep_eq : forall sg current receipt timers,
  timer_finish_initialization current receipt = Some timers ->
  timer_configured_rep sg current = timer_configured_rep sg timers.
Proof.
  intros sg current receipt timers Hfinish.
  unfold timer_finish_initialization in Hfinish.
  destruct current.(timerInitPhase) eqn:Hphase; try discriminate.
  inversion Hfinish; subst timers; unfold timer_configured_rep; rewrite Hphase.
  destruct sg.(osKernelConfig).(cfgTimerEnabled); reflexivity.
Qed.

Lemma tmr_init_finish_name_closed_equiv : forall environment critical sg call mask current receipt timers,
  timer_finish_initialization current.(TimerState) receipt = Some timers ->
  task_name_set_closed environment.(task_stack_call_platform) critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) mask current --||--
  task_name_set_closed environment.(task_stack_call_platform) critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) mask (replace_TimerS timers current).
Proof.
  intros environment critical sg call mask current receipt timers Hfinish.
  unfold task_name_set_closed, critical_region_outside.
  rewrite !critical_region_outside_without_running_rep, <- !UCOS2_raw_rep_split_running.
  unfold UCOS2_raw_rep; cbn [replace_TimerS TskState SchedState IntrState EventState TickState
    FlagState MemoryState TimerState StatsState ControlState NameState].
  rewrite (tmr_init_timer_finish_rep_eq sg current.(TimerState) receipt timers Hfinish).
  split; entailer!.
Qed.

Lemma tmr_init_finish_safe_return : forall current receipt timers X,
  timer_finish_initialization current.(TimerState) receipt = Some timers ->
  safeExec (eq current) (tmr_init_finish_program receipt) X ->
  safeExec (eq (replace_TimerS timers current)) (StateRelMonad.ret tt) X.
Proof.
  intros current receipt timers X Hfinish [start [Hstart Hsafe]]; subst start.
  exists (replace_TimerS timers current); split; [reflexivity|].
  intros result after [Hresult Hafter]; subst result after.
  apply Hsafe; split; [reflexivity|exists timers; auto].
Qed.

Lemma tmr_init_task_return_finish : forall p original call before X,
  task_tcb_init_stack_same_call call original ->
  tmr_init_task_return p call before X |-- tmr_init_post p original X.
Proof.
  intros p original call before X Hcall; unfold tmr_init_task_return; Intros.
  assert (Hbinding : tmr_init_source_binding p) by tauto.
  assert (Hphase : before.(TimerState).(timerInitPhase) = TimerSignalAttempted) by tauto.
  unfold tmr_init_task_phase_post; Intros returned middle create_error receipt current name_error.
  assert (Hcreated : tmr_init_task_phase_created p.(tmr_init_environment) p.(tmr_init_critical) p.(tmr_init_sg)
    p.(tmr_init_entry_address) p.(tmr_init_stack_base) p.(tmr_init_return_address)
    p.(tmr_init_lower) p.(tmr_init_old_frame) p.(tmr_init_upper) call p.(tmr_init_mask)
    p.(tmr_init_literals) before (tmr_init_task_continuation p call before X)
    returned middle create_error receipt) by tauto.
  destruct Hcreated as [Hcreated [Hmiddle_phase Hreceipt]].
  destruct Hcreated as [Hsame [Hmiddle_valid [Hcodes [Hcreate [Hboot [Hread Hnamesafe]]]]]].
  assert (Hname : task_name_set_post p.(tmr_init_critical) p.(tmr_init_sg) returned.(os_sched_call_invocation)
    61 (p.(tmr_init_literals) "uC/OS-II Tmr") middle name_error current
    (tmr_init_task_name_continuation (tmr_init_task_continuation p call before X))) by tauto.
  pose proof (tmr_init_name_result_preserves_validity _ _ _ _ _ _ _ _ Hmiddle_valid Hread (proj1 Hname)) as Hcurrent_valid.
  pose proof (task_name_set_result_program _ _ _ _ _ _ _ _ (proj1 Hname)) as Hname_run.
  assert (Hname_run_original : task_name_set_program p.(tmr_init_critical) p.(tmr_init_sg)
    call.(os_sched_call_invocation) 61 (p.(tmr_init_literals) "uC/OS-II Tmr") middle name_error current).
  { rewrite <- (proj1 Hsame); exact Hname_run. }
  assert (Hreceived : tmr_init_task_receipt_program p.(tmr_init_environment) p.(tmr_init_critical) p.(tmr_init_sg)
    p.(tmr_init_entry_address) p.(tmr_init_stack_base) p.(tmr_init_return_address)
    p.(tmr_init_lower) p.(tmr_init_old_frame) p.(tmr_init_upper) call p.(tmr_init_mask)
    p.(tmr_init_literals) before receipt current).
  { exists create_error, middle, name_error; auto. }
  assert (Hreturned_safe : safeExec (eq current) (StateRelMonad.ret tt)
      (tmr_init_task_continuation p call before X)) by tauto.
  destruct Hreturned_safe as [start [Hstart Hreturned_safe]]; subst start.
  specialize (Hreturned_safe tt current (conj eq_refl eq_refl)).
  assert (Hfinish_safe : safeExec (eq current) (tmr_init_finish_program receipt) X).
  { apply Hreturned_safe; exact Hreceived. }
  assert (Hphase_eq : tmr_init_task_timer_phase_eq before current) by tauto.
  assert (Hcurrent_phase : current.(TimerState).(timerInitPhase) = TimerSignalAttempted).
  { unfold tmr_init_task_timer_phase_eq in Hphase_eq; congruence. }
  set (timers := timer_set_initialization current.(TimerState) TimerInitializationFinished
    current.(TimerState).(timerSem) current.(TimerState).(timerSignalSem) receipt).
  assert (Hfinish : timer_finish_initialization current.(TimerState) receipt = Some timers).
  { unfold timer_finish_initialization; rewrite Hcurrent_phase; reflexivity. }
  assert (Henabled : p.(tmr_init_sg).(osKernelConfig).(cfgTimerEnabled) = true).
  { rewrite (tmr_init_source_binding_config p Hbinding); reflexivity. }
  pose proof (UCOS2_timer_finish_initialization_preserves_validity p.(tmr_init_sg) current receipt timers
    Henabled Hcurrent_valid Hfinish) as Hfinished_valid.
  pose proof (tmr_init_finish_safe_return current receipt timers X Hfinish Hfinish_safe) as Hsafe.
  sep_apply_l_atomic (proj1 (tmr_init_finish_name_closed_equiv p.(tmr_init_environment) p.(tmr_init_critical)
    p.(tmr_init_sg) returned p.(tmr_init_mask) current receipt timers Hfinish)).
  assert (Hfinished_phase : timers.(timerInitPhase) = TimerInitializationFinished) by reflexivity.
  unfold tmr_init_post; Exists call before returned middle create_error receipt current name_error timers.
  unfold tmr_init_task_phase_created, tmr_init_task_created; entailer!; tauto.
Qed.

Lemma tmr_init_sem_pre_ready : forall p call before stage K,
  tmr_init_source_binding p -> tmr_init_entry_facts p call before ->
  before.(TimerState).(timerInitPhase) = tmr_init_sem_stage_phase stage ->
  sem_create_api_safe p.(tmr_init_critical) p.(tmr_init_sg) call.(os_sched_call_invocation)
    (tmr_init_sem_count stage) before K ->
  tmr_init_world p call before |-- tmr_init_sem_pre p call before stage K.
Proof.
  intros p call before stage K Hbinding Hentry Hphase Hsafe.
  assert (Hsource : mbox_create_source_binding p.(tmr_init_sg))
    by (unfold tmr_init_source_binding in Hbinding; tauto).
  assert (Hcount : 0 <= tmr_init_sem_count stage <= 65535)
    by (destruct stage; cbn [tmr_init_sem_count]; lia).
  assert (Hinput : sem_create_api_input_facts p.(tmr_init_critical) p.(tmr_init_sg) call before
    (tmr_init_sem_count stage) K).
  { unfold sem_create_api_input_facts; tauto. }
  unfold tmr_init_world, tmr_init_sem_pre, tmr_init_sem_call_continuation.
  sep_apply (tmr_init_sem_pre_retain_source p.(tmr_init_environment) p.(tmr_init_critical)
    p.(tmr_init_sg) call p.(tmr_init_mask) before (tmr_init_sem_count stage) K Hinput).
  entailer!; tauto.
Qed.

Lemma tmr_init_entry_facts_timer_replace : forall p call before timers,
  tmr_init_entry_facts p call (replace_TimerS timers before) = tmr_init_entry_facts p call before.
Proof. reflexivity. Qed.

Lemma tmr_init_lock_store_next_call : forall p original initial result returned current X,
  tmr_init_sem_return_facts p original (tmr_init_after_pool p initial) true
    (tmr_init_sem_continuation p original true X) result returned current ->
  p.(tmr_init_sg).(g_OSTmrSem) # Ptr |-> result ** tmr_init_sem_return_frame p returned current true |--
  EX next,
    coq_prop (task_tcb_init_stack_same_call returned original) &&
    tmr_init_sem_pre p returned next false (tmr_init_sem_continuation p original false X).
Proof.
  intros p original initial result returned current X [Hbinding [Hsame [Hrun [HK [Hphase Hentry]]]]].
  cbn [tmr_init_sem_stage_phase tmr_init_sem_continuation] in Hphase, HK.
  set (timers := timer_set_initialization current.(TimerState) TimerLockAttempted result
    current.(TimerState).(timerSignalSem) current.(TimerState).(timerTask)).
  assert (Hstep : timer_record_lock_result current.(TimerState) result = Some timers).
  { unfold timer_record_lock_result; rewrite Hphase; reflexivity. }
  pose proof (tmr_init_record_lock_safe_step p.(tmr_init_critical) p.(tmr_init_sg)
    original.(os_sched_call_invocation) (tmr_init_tail p original) current result timers X HK Hstep) as Hnext.
  pose proof (tmr_init_second_sem_safe _ _ _ _ _ _ Hnext) as Hsafe.
  rewrite <- (proj1 Hsame) in Hsafe.
  assert (Henabled : p.(tmr_init_sg).(osKernelConfig).(cfgTimerEnabled) = true).
  { rewrite (tmr_init_source_binding_config p Hbinding); reflexivity. }
  cbn [tmr_init_sem_return_frame].
  sep_apply (tmr_init_sem_world_merge_lock p.(tmr_init_environment) p.(tmr_init_critical)
    p.(tmr_init_sg) returned p.(tmr_init_mask) current result timers Henabled Hstep).
  assert (Hready : tmr_init_world p returned (replace_TimerS timers current) |--
    tmr_init_sem_pre p returned (replace_TimerS timers current) false
      (tmr_init_sem_continuation p original false X)).
  { apply tmr_init_sem_pre_ready.
    - exact Hbinding.
    - rewrite tmr_init_entry_facts_timer_replace; exact Hentry.
    - reflexivity.
    - exact Hsafe. }
  unfold tmr_init_world in Hready.
  sep_apply Hready; Exists (replace_TimerS timers current); entailer!.
Qed.

Lemma tmr_init_world_valid : forall p call state,
  tmr_init_world p call state |-- coq_prop (UCOS2_state_inv p.(tmr_init_sg) state) &&
    tmr_init_world p call state.
Proof. intros; unfold tmr_init_world; rewrite q_create_save_input_open; unfold UCOS2_inv; entailer!. Qed.

Lemma tmr_init_task_pre_ready : forall p call before X,
  tmr_init_source_binding p -> tmr_init_entry_facts p call before ->
  before.(TimerState).(timerInitPhase) = TimerSignalAttempted ->
  safeExec (eq before) (tmr_init_tail p call) X ->
  tmr_init_world p call before ** tmr_init_static_resources p |-- tmr_init_task_pre p call before X.
Proof.
  intros p call before X Hbinding Hentry Hphase Hsafe.
  sep_apply (tmr_init_world_valid p call before); Intros.
  assert (Hvalid : UCOS2_state_inv p.(tmr_init_sg) before) by tauto.
  assert (Henabled : p.(tmr_init_sg).(osKernelConfig).(cfgTimerEnabled) = true).
  { rewrite (tmr_init_source_binding_config p Hbinding); reflexivity. }
  assert (Hstopped : tmr_init_task_stopped before).
  { eapply tmr_init_unfinished_is_stopped; [exact Henabled|exact Hvalid|congruence]. }
  pose proof (tmr_init_task_finish_safe_call p.(tmr_init_environment) p.(tmr_init_critical) p.(tmr_init_sg)
    p.(tmr_init_entry_address) p.(tmr_init_stack_base) p.(tmr_init_return_address)
    p.(tmr_init_lower) p.(tmr_init_old_frame) p.(tmr_init_upper) call p.(tmr_init_mask)
    p.(tmr_init_literals) before X Hsafe) as Hcall.
  sep_apply (tmr_init_entry_close p call before Hentry).
  unfold tmr_init_task_pre, tmr_init_task_continuation; entailer!; tauto.
Qed.

Lemma tmr_init_signal_store_next_call : forall p original previous before result returned current X,
  task_tcb_init_stack_same_call previous original ->
  tmr_init_sem_return_facts p previous before false
    (tmr_init_sem_continuation p original false X) result returned current ->
  p.(tmr_init_sg).(g_OSTmrSemSignal) # Ptr |-> result **
    tmr_init_sem_return_frame p returned current false ** tmr_init_static_resources p |--
  EX next,
    coq_prop (task_tcb_init_stack_same_call returned original) && tmr_init_task_pre p returned next X.
Proof.
  intros p original previous before result returned current X Hprevious
    [Hbinding [Hsame [Hrun [HK [Hphase Hentry]]]]].
  assert (Hsame_original : task_tcb_init_stack_same_call returned original).
  { unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  cbn [tmr_init_sem_stage_phase tmr_init_sem_continuation] in Hphase, HK.
  set (timers := timer_set_initialization current.(TimerState) TimerSignalAttempted
    current.(TimerState).(timerSem) result current.(TimerState).(timerTask)).
  assert (Hstep : timer_record_signal_result current.(TimerState) result = Some timers).
  { unfold timer_record_signal_result; rewrite Hphase; reflexivity. }
  pose proof (tmr_init_record_signal_safe_step (tmr_init_tail p original) current result timers X HK Hstep) as Hsafe.
  assert (Htail_eq : tmr_init_tail p returned = tmr_init_tail p original).
  { unfold tmr_init_tail; apply tmr_init_task_finish_program_same_call_eq; exact Hsame_original. }
  rewrite <- Htail_eq in Hsafe.
  assert (Henabled : p.(tmr_init_sg).(osKernelConfig).(cfgTimerEnabled) = true).
  { rewrite (tmr_init_source_binding_config p Hbinding); reflexivity. }
  cbn [tmr_init_sem_return_frame].
  sep_apply (tmr_init_sem_world_merge_signal p.(tmr_init_environment) p.(tmr_init_critical)
    p.(tmr_init_sg) returned p.(tmr_init_mask) current result timers Henabled Hstep).
  assert (Hready : tmr_init_world p returned (replace_TimerS timers current) ** tmr_init_static_resources p |--
    tmr_init_task_pre p returned (replace_TimerS timers current) X).
  { apply tmr_init_task_pre_ready.
    - exact Hbinding.
    - rewrite tmr_init_entry_facts_timer_replace; exact Hentry.
    - reflexivity.
    - exact Hsafe. }
  unfold tmr_init_world in Hready.
  sep_apply Hready; Exists (replace_TimerS timers current); entailer!.
Qed.

Lemma tmr_init_source_pool_addr_eq__pool_resources : forall p i,
  tmr_init_source_binding p ->
  &("OSTmrTbl") + i * sizeof("os_tmr") = timer_pool_addr p.(tmr_init_sg) i.
Proof.
  intros p i Hbinding.
  pose proof (tmr_init_source_binding_config p Hbinding) as Hcfg.
  destruct Hbinding as [Hlayout [Hsize [Hwheel [Hbase Hrest]]]].
  change (&("OSTmrTbl") + i * sizeof_alias_type "os_tmr" =
    timer_pool_addr p.(tmr_init_sg) i).
  rewrite Hsize, Hbase.
  unfold timer_pool_addr, timer_object_size, timer_option_offset.
  rewrite Hcfg; reflexivity.
Qed.
Lemma tmr_init_source_slot_fields_eq__pool_resources : forall p i,
  tmr_init_source_binding p -> 0 <= i < 16 ->
  eval_addr_expr (RE_addr_of (LE_arrow_field
    (RE_const (timer_pool_addr p.(tmr_init_sg) i) (FET_alias "os_tmr")) "OSTmrType")) =
    timer_pool_addr p.(tmr_init_sg) i /\
  eval_addr_expr (RE_addr_of (LE_arrow_field
    (RE_const (timer_pool_addr p.(tmr_init_sg) i) (FET_alias "os_tmr")) "OSTmrState")) =
    timer_pool_addr p.(tmr_init_sg) i + 37 /\
  eval_addr_expr (RE_addr_of (LE_arrow_field
    (RE_const (timer_pool_addr p.(tmr_init_sg) i) (FET_alias "os_tmr")) "OSTmrNext")) =
    timer_pool_addr p.(tmr_init_sg) i + 12 /\
  eval_addr_expr (RE_addr_of (LE_arrow_field
    (RE_const (timer_pool_addr p.(tmr_init_sg) i) (FET_alias "os_tmr")) "OSTmrName")) =
    timer_pool_addr p.(tmr_init_sg) i + 32.
Proof.
  intros p i Hbinding Hi; unfold tmr_init_source_binding in Hbinding.
  repeat match type of Hbinding with _ /\ _ => destruct Hbinding as [? Hbinding] end.
  eauto.
Qed.
Lemma tmr_init_pool_context_split_question_mark__pool_resources : forall p call initial X,
  tmr_init_pool_context p call initial X |--
  store_stringLit (tmr_init_question p) "?" **
  GlobalStrings_missing p.(tmr_init_literals) p.(tmr_init_missing_literals) **
  tmr_init_pool_literal_residual p call initial X.
Proof.
  intros p call initial X.
  unfold tmr_init_pool_context at 1; Intros.
  assert (Hbinding : tmr_init_source_binding p) by tauto.
  assert (Hentry : tmr_init_entry_facts p call initial) by tauto.
  assert (Hregistered : task_create_name_registered (tmr_init_question p) initial)
    by (unfold tmr_init_entry_facts in Hentry; tauto).
  pose proof (task_create_name_registered_binding _ _ Hregistered) as [Hchar Hnul].
  unfold tmr_init_pool_residual, tmr_init_sem_store_frame, tmr_init_static_resources.
  Intros.
  unfold UCOS2_raw_rep_missing_timer.
  rewrite (UCOS2_raw_rep_missing_module_split_module p.(tmr_init_sg) initial
    TimerModule NamesModule ltac:(discriminate)).
  change (UCOS2_module_rep p.(tmr_init_sg) initial NamesModule)
    with (store_name_bytes initial.(NameState)).
  sep_apply (kernel_literal_resources.store_name_bytes_split_question_mark initial.(NameState)
    (tmr_init_question p) Hchar Hnul).
  unfold tmr_init_pool_literal_residual.
  entailer!.
  apply_sepcon_adjoint.
  unfold tmr_init_pool_context, tmr_init_pool_residual, tmr_init_sem_store_frame,
    tmr_init_static_resources, UCOS2_raw_rep_missing_timer.
  rewrite (UCOS2_raw_rep_missing_module_split_module p.(tmr_init_sg) initial
    TimerModule NamesModule ltac:(discriminate)).
  change (UCOS2_module_rep p.(tmr_init_sg) initial NamesModule)
    with (store_name_bytes initial.(NameState)).
  sep_apply (kernel_literal_resources.store_name_bytes_merge_question_mark initial.(NameState)
    (tmr_init_question p) Hchar Hnul).
  entailer!; tauto.
Qed.
Lemma tmr_init_after_globals_merge_call_world__pool_resources : forall p call initial,
  tmr_init_source_binding p ->
  initial.(SchedState).(isRunning) = false ->
  initial.(TimerState).(timerInitPhase) = TimerUninitialized ->
  tmr_init_after_globals p.(tmr_init_sg) (tmr_init_question p) **
  tmr_init_sem_store_frame p.(tmr_init_environment) p.(tmr_init_sg) call
    p.(tmr_init_mask) initial emp |--
  tmr_init_world p call (tmr_init_after_pool p initial).
Proof.
  intros p call initial Hbinding Hstopped Hphase.
  pose proof (tmr_init_source_binding_config p Hbinding) as Hcfg.
  unfold tmr_init_sem_store_frame; Intros.
  assert (Hvalid : UCOS2_state_inv p.(tmr_init_sg) initial) by tauto.
  sep_apply (tmr_init_after_globals_merge_world p.(tmr_init_sg) initial
    (tmr_init_question p) Hcfg Hvalid Hstopped Hphase).
  unfold tmr_init_world, tmr_init_after_pool.
  rewrite q_create_save_input_open; unfold q_create_owned.
  cbn [replace_TimerS TskState]; entailer!.
Qed.
Lemma tmr_init_pool_safe_first_call__pool_resources : forall p call initial X,
  safeExec (eq initial) (tmr_init_program p call) X ->
  sem_create_api_safe p.(tmr_init_critical) p.(tmr_init_sg)
    call.(os_sched_call_invocation) 1 (tmr_init_after_pool p initial)
    (tmr_init_sem_continuation p call true X).
Proof.
  intros p call initial X Hsafe.
  apply tmr_init_first_sem_safe.
  apply (tmr_init_pool_safe_step p.(tmr_init_environment) p.(tmr_init_critical)
    p.(tmr_init_sg) p.(tmr_init_entry_address) p.(tmr_init_stack_base)
    p.(tmr_init_return_address) p.(tmr_init_lower) p.(tmr_init_old_frame)
    p.(tmr_init_upper) call p.(tmr_init_mask) p.(tmr_init_literals) initial X).
  exact Hsafe.
Qed.
Lemma tmr_init_post_absorb_coq_prop__call_refinement : forall p original X (P : Prop),
  tmr_init_post p original X ** coq_prop P |-- tmr_init_post p original X.
Proof.
  intros p original X P; unfold tmr_init_post.
  Intros call before returned middle create_error receipt current name_error timers.
  assert (Htrue : (TT ** TT) |-- TT) by entailer!.
  sep_apply_l_atomic Htrue.
  Exists call before returned middle create_error receipt current name_error timers.
  entailer!.
Qed.
Lemma tmr_init_sem_pre_implies_state_inv__call_refinement : forall p call before stage K,
  tmr_init_sem_pre p call before stage K |--
  coq_prop (UCOS2_state_inv p.(tmr_init_sg) before) &&
  tmr_init_sem_pre p call before stage K.
Proof.
  intros; unfold tmr_init_sem_pre, sem_create_api_call_pre.
  rewrite q_create_save_input_open; unfold UCOS2_inv; entailer!.
Qed.
