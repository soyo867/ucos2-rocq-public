Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import SumLib.ZRange.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.memory.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_init_spec.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Internal, startup-serialized helper. The caller owns the uninitialized
    table, root and one literal pool. No running-state invariant, allocated
    partition or additional copy of the literal bytes is an entry resource. *)
Definition mem_init_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgMemoryEnabled) = true /\
  sg.(osKernelConfig).(cfgMaxMemPartitions) = 5 /\
  sg.(osKernelConfig).(cfgMemoryNames) = true.

Definition mem_init_global_addresses (sg : StableGlobVars) (pool root : Z) : Prop :=
  sg.(g_OSMemTbl) = pool /\ sg.(g_OSMemFreeList) = root.

(** Actual QCP arrow interpretation for the selected six-field OS_MEM.
    Alignment and the strict MemClr cursor endpoint are explicit startup
    caller obligations, not consequences of raw byte ownership. *)
Definition mem_init_layout (sg : StableGlobVars) : Prop :=
  0 <= sg.(g_OSMemTbl) /\ sg.(g_OSMemTbl) + 120 <= 4294967295 /\
  sg.(g_OSMemTbl) mod 4 = 0 /\ sizeof ("os_mem") = 24 /\
  (forall i, 0 <= i < 5 ->
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (sg.(g_OSMemTbl) + i * 24) (FET_alias "os_mem")) "OSMemAddr")) =
      sg.(g_OSMemTbl) + i * 24 /\
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (sg.(g_OSMemTbl) + i * 24) (FET_alias "os_mem")) "OSMemFreeList")) =
      sg.(g_OSMemTbl) + i * 24 + 4 /\
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (sg.(g_OSMemTbl) + i * 24) (FET_alias "os_mem")) "OSMemBlkSize")) =
      sg.(g_OSMemTbl) + i * 24 + 8 /\
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (sg.(g_OSMemTbl) + i * 24) (FET_alias "os_mem")) "OSMemNBlks")) =
      sg.(g_OSMemTbl) + i * 24 + 12 /\
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (sg.(g_OSMemTbl) + i * 24) (FET_alias "os_mem")) "OSMemNFree")) =
      sg.(g_OSMemTbl) + i * 24 + 16 /\
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (sg.(g_OSMemTbl) + i * 24) (FET_alias "os_mem")) "OSMemName")) =
      sg.(g_OSMemTbl) + i * 24 + 20).

Definition mem_init_pre (sg : StableGlobVars) : Assertion :=
  mem_clr_pre sg.(g_OSMemTbl) 120 ** sg.(g_OSMemFreeList) # Ptr |->_ .

(** The mathematical endpoint is the existing finite-map initial state.
    This prefix merely records which exact endpoint images have been stored. *)
Definition mem_init_prefix (sg : StableGlobVars) (name i : Z) : Assertion :=
  iter_sepcon (map (fun j =>
    store_memory_control sg (memory_control_addr sg j)
      (memory_initial_image sg name j)) (Zrange 0 i)).

Definition mem_init_loop_state (sg : StableGlobVars) (name i : Z) : Assertion :=
  mem_init_prefix sg name i **
  mem_clr_post (sg.(g_OSMemTbl) + i * 24) (120 - i * 24) **
  sg.(g_OSMemFreeList) # Ptr |->_ .

Definition mem_init_control_residual (p : Z) : Assertion :=
  p # Ptr |-> 0 ** (p + 8) # UInt |-> 0 **
  (p + 12) # UInt |-> 0 ** (p + 16) # UInt |-> 0.

Definition mem_init_loop_residual (sg : StableGlobVars) (name i : Z) : Assertion :=
  mem_init_prefix sg name i **
  mem_init_control_residual (sg.(g_OSMemTbl) + i * 24) **
  mem_clr_post (sg.(g_OSMemTbl) + (i + 1) * 24) (120 - (i + 1) * 24) **
  sg.(g_OSMemFreeList) # Ptr |->_ .

Definition mem_init_linked_pool (sg : StableGlobVars) (name : Z) : Assertion :=
  mem_init_prefix sg name 5 ** sg.(g_OSMemFreeList) # Ptr |-> sg.(g_OSMemTbl).

Definition mem_init_post (sg : StableGlobVars) (name : Z) : Assertion :=
  coq_prop (valid_memory_state sg (memory_initial sg name)) &&
  memory_raw_rep sg (memory_initial sg name).

Lemma mem_init_profile_of_selected_configuration : forall sg,
  sg.(osKernelConfig) = selected_kernel_configuration -> mem_init_profile sg.
Proof. intros sg H; unfold mem_init_profile; rewrite H; repeat split; reflexivity. Qed.

Lemma mem_init_control_addr_eq : forall sg i,
  mem_init_profile sg -> memory_control_addr sg i = sg.(g_OSMemTbl) + i * 24.
Proof.
  intros sg i [_ [_ Hnames]]; unfold memory_control_addr, memory_control_size.
  rewrite Hnames; reflexivity.
Qed.

Lemma mem_init_empty_prefix : forall sg name,
  mem_init_prefix sg name 0 --||-- emp.
Proof. intros; unfold mem_init_prefix; cbn; split; entailer!. Qed.

Lemma mem_init_mem_clr_to_loop_state : forall sg name,
  mem_clr_post sg.(g_OSMemTbl) 120 ** sg.(g_OSMemFreeList) # Ptr |->_ |--
  mem_init_loop_state sg name 0.
Proof.
  intros; unfold mem_init_loop_state; rewrite mem_init_empty_prefix.
  replace (g_OSMemTbl sg + 0 * 24) with (g_OSMemTbl sg) by lia.
  replace (120 - 0 * 24) with 120 by lia; entailer!.
Qed.

Lemma mem_init_zero_control_bytes_to_typed : forall p,
  p mod 4 = 0 ->
  mem_clr_post p 24 |--
  (p + 4) # Ptr |-> 0 ** (p + 20) # Ptr |-> 0 ** mem_init_control_residual p.
Proof.
  intros p Halign.
  assert (Hptrs : mem_clr_post p 24 |--
    p # Ptr |-> 0 ** (p + 4) # Ptr |-> 0 ** (p + 8) # Ptr |-> 0 **
    (p + 12) # Ptr |-> 0 ** (p + 16) # Ptr |-> 0 ** (p + 20) # Ptr |-> 0).
  { repeat rewrite flag_init_zero_link_uchar_equiv by
      (try exact Halign; rewrite Z.add_mod by lia; rewrite Halign; reflexivity).
    unfold mem_clr_post, UCharArray.full, UCharArray.mixed_full,
      UCharArray.seg, UCharArray.mixed_seg, store_array, store_array_rec,
      UCharArray.mixedstoreA, StoreUCharAsElement.storeA, repeat_Z; cbn.
    change (Pos.to_nat 24) with 24%nat; cbn.
    repeat rewrite Z.mul_1_r; repeat rewrite <- Z.add_assoc; cbn.
    repeat rewrite Z.add_0_r; entailer!. }
  sep_apply_l_atomic Hptrs.
  sep_apply_l_atomic (store_ptr_store_uint (p + 8) 0 eq_refl eq_refl).
  sep_apply_l_atomic (store_ptr_store_uint (p + 12) 0 eq_refl eq_refl).
  sep_apply_l_atomic (store_ptr_store_uint (p + 16) 0 eq_refl eq_refl).
  unfold mem_init_control_residual; entailer!.
Qed.

Lemma mem_init_loop_state_split_control : forall sg name i,
  mem_init_layout sg -> 0 <= i < 5 ->
  mem_init_loop_state sg name i |--
  (g_OSMemTbl sg + i * 24 + 4) # Ptr |-> 0 **
  (g_OSMemTbl sg + i * 24 + 20) # Ptr |-> 0 **
  mem_init_loop_residual sg name i.
Proof.
  intros sg name i [_ [_ [Halign _]]] Hi.
  unfold mem_init_loop_state, mem_init_loop_residual.
  sep_apply_l_atomic (mem_clr_post_split__flag_pool_initialization
    (g_OSMemTbl sg + i * 24) 24 (120 - i * 24) ltac:(lia)).
  replace (g_OSMemTbl sg + i * 24 + 24) with
    (g_OSMemTbl sg + (i + 1) * 24) by lia.
  replace (120 - i * 24 - 24) with (120 - (i + 1) * 24) by lia.
  sep_apply_l_atomic (mem_init_zero_control_bytes_to_typed
    (g_OSMemTbl sg + i * 24)
    ltac:(rewrite Z.add_mod, Z.mul_mod by lia; rewrite Halign;
          change ((0 + (i mod 4 * 0) mod 4) mod 4 = 0);
          rewrite Z.mul_0_r; reflexivity)).
  entailer!.
Qed.

Lemma mem_init_prefix_snoc_eq : forall sg name i,
  0 <= i ->
  mem_init_prefix sg name (i + 1) = mem_init_prefix sg name i **
  store_memory_control sg (memory_control_addr sg i) (memory_initial_image sg name i).
Proof.
  intros sg name i Hi.
  assert (Hrange : Zrange 0 (i + 1) = Zrange 0 i ++ [i]).
  { unfold Zrange.
    replace (Z.to_nat (i + 1 - 0)) with (Z.to_nat (i - 0) + 1)%nat by lia.
    rewrite Zrange_aux_app.
    replace (0 + Z.of_nat (Z.to_nat (i - 0))) with i by lia; reflexivity. }
  unfold mem_init_prefix; rewrite Hrange, map_app.
  unfold iter_sepcon; rewrite fold_left_app; reflexivity.
Qed.

Lemma mem_init_initial_image_rep_equiv : forall sg name i,
  mem_init_profile sg -> mem_init_layout sg -> 0 <= i < 5 ->
  store_memory_control sg (memory_control_addr sg i) (memory_initial_image sg name i) --||--
  (g_OSMemTbl sg + i * 24 + 4) # Ptr |->
    (if i <? 4 then g_OSMemTbl sg + (i + 1) * 24 else 0) **
  (g_OSMemTbl sg + i * 24 + 20) # Ptr |-> name **
  mem_init_control_residual (g_OSMemTbl sg + i * 24).
Proof.
  intros sg name i Hprofile [_ [_ [_ [_ Hfields]]]] Hi.
  rewrite store_memory_control_layout_equiv.
  rewrite (mem_init_control_addr_eq sg i Hprofile).
  destruct (Hfields i Hi) as [Haddr [Hfree [Hsize [Hcount [Hnfree Hname]]]]].
  destruct Hprofile as [_ [Hparts Hnames]].
  rewrite Hnames; rewrite Haddr, Hfree, Hsize, Hcount, Hnfree, Hname.
  unfold memory_initial_image, mem_init_control_residual.
  rewrite Hparts.
  assert (Hcases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  unfold memory_control_addr, memory_control_size; rewrite Hnames.
  destruct Hcases as [-> | [-> | [-> | [-> | ->]]]]; cbn;
    change (Pos.to_nat 5) with 5%nat; cbn;
    repeat rewrite Z.add_0_r; repeat rewrite <- Z.add_assoc;
    split; entailer!.
Qed.

Lemma mem_init_loop_residual_merge_control : forall sg name i,
  mem_init_profile sg -> mem_init_layout sg -> 0 <= i < 5 ->
  (g_OSMemTbl sg + i * 24 + 4) # Ptr |->
    (if i <? 4 then g_OSMemTbl sg + (i + 1) * 24 else 0) **
  (g_OSMemTbl sg + i * 24 + 20) # Ptr |-> name **
  mem_init_loop_residual sg name i |-- mem_init_loop_state sg name (i + 1).
Proof.
  intros sg name i Hprofile Hlayout Hi.
  unfold mem_init_loop_residual, mem_init_loop_state.
  rewrite mem_init_prefix_snoc_eq by lia.
  rewrite (mem_init_initial_image_rep_equiv sg name i Hprofile Hlayout Hi).
  entailer!.
Qed.

Lemma mem_init_loop_state_complete : forall sg name,
  mem_init_loop_state sg name 5 |--
  mem_init_prefix sg name 5 ** sg.(g_OSMemFreeList) # Ptr |->_ .
Proof.
  intros; unfold mem_init_loop_state, mem_clr_post.
  replace (120 - 5 * 24) with 0 by lia.
  change (repeat_Z 0 0) with (@nil Z).
  rewrite UCharArray.full_empty; entailer!.
Qed.

Lemma mem_init_linked_pool_to_raw_rep : forall sg name,
  mem_init_profile sg ->
  mem_init_linked_pool sg name |-- memory_raw_rep sg (memory_initial sg name).
Proof.
  intros sg name Hprofile.
  assert (Hparts : store_map
    (fun _ p => store_memory_free_blocks p (memFreeBlocks p))
    (memPartitions (memory_initial sg name)) --||-- emp).
  { unfold memory_initial; cbn; apply store_map_empty.
    - exists []; split; [intros; split; [contradiction|intros [w Hw]; discriminate]|constructor].
    - intros; left; reflexivity. }
  unfold memory_raw_rep; rewrite Hparts.
  unfold mem_init_linked_pool, mem_init_prefix, memory_controls_rep, store_map.
  Exists ([0; 1; 2; 3; 4]).
  destruct Hprofile as [_ [Hcount Hnames]].
  unfold memory_initial; rewrite Hcount; cbn.
  entailer!.
  - simpl; replace (memory_control_addr sg 0) with (g_OSMemTbl sg)
      by (unfold memory_control_addr; lia); entailer!.
  - repeat constructor; simpl; lia.
  - intros i; split.
    + intros Hi; simpl in Hi; destruct Hi as [Hi|[Hi|[Hi|[Hi|[Hi|Hbad]]]]];
        try contradiction; subst i; eexists; reflexivity.
    + intros [v Hv]. destruct ((0 <=? i) && (i <? 5))%bool eqn:Hi; [|discriminate].
      apply Bool.andb_true_iff in Hi; destruct Hi as [Hl Hh].
      apply Z.leb_le in Hl; apply Z.ltb_lt in Hh; simpl; lia.
Qed.

Lemma mem_init_linked_pool_to_post : forall sg name,
  mem_init_profile sg -> mem_init_linked_pool sg name |-- mem_init_post sg name.
Proof.
  intros sg name Hprofile; unfold mem_init_post.
  pose proof (memory_initial_valid sg name) as Hvalid.
  sep_apply_l_atomic (mem_init_linked_pool_to_raw_rep sg name Hprofile); entailer!.
Qed.
