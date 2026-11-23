Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.error_codes.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OS_FLAG_GRP is an independent pool, never an OS_EVENT payload.  All
    bit operations use the configured OS_FLAGS width. *)
Definition flag_word (c : KernelConfiguration) (x : Z) := x mod (2 ^ c.(cfgFlagBits)).
Definition flag_word_in_range (c : KernelConfiguration) (x : Z) : Prop :=
  0 <= x < 2 ^ c.(cfgFlagBits).
Lemma flag_word_bounds : forall c x, 0 <= c.(cfgFlagBits) ->
  flag_word_in_range c (flag_word c x).
Proof.
  intros; unfold flag_word_in_range, flag_word; apply Z.mod_pos_bound.
  apply Z.pow_pos_nonneg; lia.
Qed.
Definition encode_flag_wait_mode (m : FlagWaitMode) : Z :=
  match m with FlagClearAll => 0 | FlagClearAny => 1 | FlagSetAll => 2 | FlagSetAny => 3 end.
Definition decode_flag_wait_mode (c : KernelConfiguration) (w : Z) : option FlagWaitMode :=
  if Z.eqb w 2 then Some FlagSetAll else if Z.eqb w 3 then Some FlagSetAny else
  if c.(cfgFlagClearWait) then
    if Z.eqb w 0 then Some FlagClearAll else if Z.eqb w 1 then Some FlagClearAny else None
  else None.
Lemma decode_encode_flag_wait_mode : forall c m,
  c.(cfgFlagClearWait) = true -> decode_flag_wait_mode c (encode_flag_wait_mode m) = Some m.
Proof. intros c m H; destruct m; unfold decode_flag_wait_mode; simpl; rewrite ?H; reflexivity. Qed.
Definition flag_ready_bits (c : KernelConfiguration) (bits mask : Z) (m : FlagWaitMode) : Z :=
  match m with
  | FlagSetAll | FlagSetAny => flag_word c (Z.land bits mask)
  | FlagClearAll | FlagClearAny => flag_word c (Z.land (Z.lnot bits) mask)
  end.
Definition flag_wait_satisfied (m : FlagWaitMode) (ready mask : Z) : bool :=
  match m with
  | FlagClearAll | FlagSetAll => Z.eqb ready mask
  | FlagClearAny | FlagSetAny => negb (Z.eqb ready 0)
  end.
Definition flag_consume_bits (c : KernelConfiguration) (bits ready : Z) (m : FlagWaitMode) :=
  match m with
  | FlagSetAll | FlagSetAny => flag_word c (Z.land bits (Z.lnot ready))
  | FlagClearAll | FlagClearAny => flag_word c (Z.lor bits ready)
  end.
Definition flag_post_bits (c : KernelConfiguration) (bits mask opt : Z) : option Z :=
  if Z.eqb opt 0 then Some (flag_word c (Z.land bits (Z.lnot mask))) else
  if Z.eqb opt 1 then Some (flag_word c (Z.lor bits mask)) else None.

Definition flag_accept_bits (c : KernelConfiguration) (bits mask wait_type : Z)
  : Z * Z * OSErrCode :=
  match decode_flag_wait_mode c (Z.land wait_type 127) with
  | None => (bits, 0, OS_ERR_FLAG_WAIT_TYPE)
  | Some mode =>
    let ready := flag_ready_bits c bits mask mode in
    if flag_wait_satisfied mode ready mask then
      (if Z.testbit wait_type 7 then flag_consume_bits c bits ready mode else bits,
       ready, OS_ERR_NONE)
    else (bits, ready, OS_ERR_FLAG_NOT_RDY)
  end.

Lemma flag_accept_failure_keeps_partial_ready :
  flag_accept_bits selected_kernel_configuration 1 3 2 = (1, 1, OS_ERR_FLAG_NOT_RDY).
Proof. reflexivity. Qed.
Lemma flag_accept_zero_all_succeeds :
  flag_accept_bits selected_kernel_configuration 7 0 2 = (7, 0, OS_ERR_NONE).
Proof. reflexivity. Qed.
Lemma flag_accept_zero_any_fails :
  flag_accept_bits selected_kernel_configuration 7 0 3 = (7, 0, OS_ERR_FLAG_NOT_RDY).
Proof. reflexivity. Qed.
Lemma flag_consume_bits_in_range : forall c bits ready mode,
  0 <= c.(cfgFlagBits) -> flag_word_in_range c (flag_consume_bits c bits ready mode).
Proof. intros; destruct mode; apply flag_word_bounds; assumption. Qed.
Lemma flag_post_bits_in_range : forall c bits mask opt post,
  0 <= c.(cfgFlagBits) -> flag_post_bits c bits mask opt = Some post ->
  flag_word_in_range c post.
Proof.
  intros c bits mask opt post Hc H; unfold flag_post_bits in H.
  destruct (Z.eqb opt 0), (Z.eqb opt 1); inversion H; subst;
    apply flag_word_bounds; assumption.
Qed.

Definition flag_group_set_bits (g : FlagGroupState) (bits : Z) : FlagGroupState :=
  {| flagGeneration := g.(flagGeneration); flagBits := bits; flagName := g.(flagName);
     flagWaitOrder := g.(flagWaitOrder) |}.
Definition valid_flag_group (c : KernelConfiguration) (g : FlagGroupState) : Prop :=
  flag_word_in_range c g.(flagBits) /\ NoDup g.(flagWaitOrder).
Lemma flag_consume_preserves_group_validity : forall c g ready mode,
  0 <= c.(cfgFlagBits) -> valid_flag_group c g ->
  valid_flag_group c (flag_group_set_bits g (flag_consume_bits c g.(flagBits) ready mode)).
Proof. intros c g ready mode Hc [_ Hnd]; split; [apply flag_consume_bits_in_range; exact Hc|exact Hnd]. Qed.
Lemma flag_post_preserves_group_validity : forall c g mask opt bits,
  0 <= c.(cfgFlagBits) -> valid_flag_group c g ->
  flag_post_bits c g.(flagBits) mask opt = Some bits ->
  valid_flag_group c (flag_group_set_bits g bits).
Proof. intros c g mask opt bits Hc [_ Hnd] H; split; [eapply flag_post_bits_in_range; eauto|exact Hnd]. Qed.

(** Post snapshots every satisfiable waiter from the same posted word.
    It does not consume that word.  Consumption occurs in the resumed Pend
    invocation and uses the saved ready bits, not a fresh condition test. *)
Definition flag_post_waiter_result (c : KernelConfiguration) (bits : Z) (w : FlagWaiterState)
  : option Z :=
  let ready := flag_ready_bits c bits w.(flagMask) w.(flagWaitMode) in
  if flag_wait_satisfied w.(flagWaitMode) ready w.(flagMask) then Some ready else None.
Fixpoint flag_post_ready_waiters (c : KernelConfiguration) (bits : Z)
  (nodes : addr -> option FlagWaiterState) (order : list addr) : list (addr * Z) :=
  match order with
  | [] => []
  | n :: rest => match nodes n with
    | None => flag_post_ready_waiters c bits nodes rest
    | Some w => match flag_post_waiter_result c bits w with
      | None => flag_post_ready_waiters c bits nodes rest
      | Some ready => (n, ready) :: flag_post_ready_waiters c bits nodes rest
      end
    end
  end.
Definition flag_resume_bits (c : KernelConfiguration) (bits ready : Z)
  (mode : FlagWaitMode) (consume : bool) : Z :=
  if consume then flag_consume_bits c bits ready mode else bits.
Lemma flag_resume_without_consume_eq : forall c bits ready mode,
  flag_resume_bits c bits ready mode false = bits.
Proof. reflexivity. Qed.

Definition flag_word_rep (c : KernelConfiguration) (p : addr) (v : Z) : Assertion :=
  if Z.eqb c.(cfgFlagBits) 8 then p # UChar |-> v else
  if Z.eqb c.(cfgFlagBits) 16 then p # UShort |-> v else p # UInt |-> v.
Definition flag_group_rep (c : KernelConfiguration) (p : addr) (v : FlagGroupImage) : Assertion :=
  p # UChar |-> v.(flagImageType) **
  store_optional_bytes (p + 1) (firstn 3 v.(flagImagePadding)) **
  (p + 4) # Ptr |-> v.(flagImageHead) **
  flag_word_rep c (p + 8) v.(flagImageBits) **
  store_optional_bytes (p + 8 + flag_word_bytes c) (skipn 3 v.(flagImagePadding)) **
  (if c.(cfgFlagNames) then (p + flag_group_name_offset c) # Ptr |-> v.(flagImageName) else emp).
Definition flag_node_rep (c : KernelConfiguration) (p : addr) (v : FlagNodeImage) : Assertion :=
  p # Ptr |-> v.(flagNodeNext) ** (p + 4) # Ptr |-> v.(flagNodePrev) **
  (p + 8) # Ptr |-> v.(flagNodeTCB) ** (p + 12) # Ptr |-> v.(flagNodeGroup) **
  flag_word_rep c (p + 16) v.(flagNodeMask) **
  (p + flag_node_mode_offset c) # UChar |-> v.(flagNodeMode) **
  store_optional_bytes (p + flag_node_mode_offset c + 1) v.(flagNodePadding).

Definition flag_group_image_valid (c : KernelConfiguration) (v : FlagGroupImage) : Prop :=
  flag_word_in_range c v.(flagImageBits) /\
  Z.of_nat (List.length v.(flagImagePadding)) = 3 + flag_group_name_offset c - (8 + flag_word_bytes c).
Definition flag_node_image_valid (c : KernelConfiguration) (v : FlagNodeImage) : Prop :=
  flag_word_in_range c v.(flagNodeMask) /\
  Z.of_nat (List.length v.(flagNodePadding)) = flag_node_size c - flag_node_mode_offset c - 1.

Definition flag_groups_rep (sg : StableGlobVars) (s : GlobFlagState) : Assertion :=
  store_map (fun i v => flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) v) s.(flagImages).
Definition flag_groups_without (sg : StableGlobVars) (s : GlobFlagState) (i : FlagID) : Assertion :=
  store_map_missing_i (fun i v => flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) v) s.(flagImages) i.
Definition flag_wait_nodes_rep (sg : StableGlobVars) (nodes : addr -> option FlagWaiterState) : Assertion :=
  store_map (fun p w => flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)) nodes.
Definition flag_wait_nodes_without_node (sg : StableGlobVars) (nodes : addr -> option FlagWaiterState)
  (p : addr) : Assertion :=
  store_map_missing_i (fun p w => flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)) nodes p.

Definition flag_nodes_rep (sg : StableGlobVars) (s : GlobFlagState) : Assertion :=
  flag_wait_nodes_rep sg s.(flagWaitNodes).
Definition flag_nodes_without (sg : StableGlobVars) (s : GlobFlagState) (p : addr) : Assertion :=
  flag_wait_nodes_without_node sg s.(flagWaitNodes) p.
Definition flag_raw_rep (sg : StableGlobVars) (s : GlobFlagState) : Assertion :=
  flag_groups_rep sg s ** flag_nodes_rep sg s **
  sg.(g_OSFlagFreeList) # Ptr |->
    match s.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.

Definition flag_wait_list_valid (sg : StableGlobVars) (s : GlobFlagState)
  (i : FlagID) (g : FlagGroupState) : Prop :=
  forall pre p rest, g.(flagWaitOrder) = pre ++ p :: rest ->
    exists w, s.(flagWaitNodes) p = Some w /\
      w.(flagNodeAddr) = p /\ w.(flagGroup) = i /\
      w.(flagGroupGeneration) = g.(flagGeneration) /\
      w.(flagWaitImage).(flagNodeGroup) = flag_pool_addr sg i /\
      w.(flagWaitImage).(flagNodePrev) = last pre 0 /\
      w.(flagWaitImage).(flagNodeNext) = hd 0 rest /\
      w.(flagWaitImage).(flagNodeMask) = w.(flagMask) /\
      w.(flagWaitImage).(flagNodeMode) = encode_flag_wait_mode w.(flagWaitMode).
Definition valid_flag_state (sg : StableGlobVars) (s : GlobFlagState) : Prop :=
  kernel_pool_partition sg.(osKernelConfig).(cfgMaxFlags) s.(flagFree) s.(flagUsed) /\
  (forall i, (exists v, s.(flagImages) i = Some v) <-> 0 <= i < sg.(osKernelConfig).(cfgMaxFlags)) /\
  (forall i v, s.(flagImages) i = Some v -> flag_group_image_valid sg.(osKernelConfig) v) /\
  (forall i g, s.(flagUsed) i = Some g ->
    valid_flag_group sg.(osKernelConfig) g /\ (g.(flagGeneration) < s.(flagNextGeneration))%nat /\
    flag_wait_list_valid sg s i g /\
    exists v, s.(flagImages) i = Some v /\ v.(flagImageType) = 5 /\
      v.(flagImageHead) = hd 0 g.(flagWaitOrder) /\
      v.(flagImageBits) = g.(flagBits) /\ v.(flagImageName) = g.(flagName)) /\
  (forall pre i rest, s.(flagFree) = pre ++ i :: rest ->
    exists v, s.(flagImages) i = Some v /\ v.(flagImageType) = 0 /\
      v.(flagImageHead) = match rest with [] => 0 | j :: _ => flag_pool_addr sg j end) /\
  (forall p w, s.(flagWaitNodes) p = Some w ->
    p <> 0 /\ flag_node_image_valid sg.(osKernelConfig) w.(flagWaitImage) /\
    exists g, s.(flagUsed) w.(flagGroup) = Some g /\ In p g.(flagWaitOrder)).
Definition flag_disabled : GlobFlagState :=
  {| flagUsed := fun _ => None; flagFree := []; flagImages := fun _ => None;
     flagWaitNodes := fun _ => None; flagNextGeneration := 0 |}.
Definition valid_flag_configuration (sg : StableGlobVars) (s : GlobFlagState) : Prop :=
  if sg.(osKernelConfig).(cfgFlagEnabled) then valid_flag_state sg s else s = flag_disabled.
Definition flag_configured_rep (sg : StableGlobVars) (s : GlobFlagState) : Assertion :=
  if sg.(osKernelConfig).(cfgFlagEnabled) then flag_raw_rep sg s else emp.
Definition flag_inv (sg : StableGlobVars) (s : GlobFlagState) : Assertion :=
  coq_prop (valid_flag_configuration sg s) && flag_configured_rep sg s.
Lemma valid_flag_state_node_nonzero : forall sg s p w,
  valid_flag_state sg s -> s.(flagWaitNodes) p = Some w -> p <> 0.
Proof. intros sg s p w [_ [_ [_ [_ [_ Hnodes]]]]] H; exact (proj1 (Hnodes p w H)). Qed.
Lemma valid_flag_state_node_position : forall sg s p w,
  valid_flag_state sg s -> s.(flagWaitNodes) p = Some w ->
  exists g pre rest, s.(flagUsed) w.(flagGroup) = Some g /\
    g.(flagWaitOrder) = pre ++ p :: rest /\
    w.(flagNodeAddr) = p /\ w.(flagGroupGeneration) = g.(flagGeneration) /\
    w.(flagWaitImage).(flagNodeGroup) = flag_pool_addr sg w.(flagGroup) /\
    w.(flagWaitImage).(flagNodePrev) = last pre 0 /\
    w.(flagWaitImage).(flagNodeNext) = hd 0 rest /\
    w.(flagWaitImage).(flagNodeMask) = w.(flagMask) /\
    w.(flagWaitImage).(flagNodeMode) = encode_flag_wait_mode w.(flagWaitMode).
Proof.
  intros sg s p w [_ [_ [_ [Hused [_ Hnodes]]]]] Hw.
  destruct (Hnodes p w Hw) as [_ [_ [g [Hg Hin]]]].
  destruct (Hused _ g Hg) as [_ [_ [Hwait _]]].
  apply in_split in Hin; destruct Hin as [pre [rest Hlist]].
  destruct (Hwait pre p rest Hlist) as [old [Hold [Haddr [_ Hfields]]]].
  rewrite Hw in Hold; inversion Hold; subst old.
  exists g, pre, rest; auto.
Qed.
Lemma flag_disabled_configuration_valid : forall sg,
  sg.(osKernelConfig).(cfgFlagEnabled) = false -> valid_flag_configuration sg flag_disabled.
Proof. intros; unfold valid_flag_configuration; rewrite H; reflexivity. Qed.

Lemma flag_groups_split_group : forall sg s i v,
  s.(flagImages) i = Some v -> flag_groups_rep sg s |--
  flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) v ** flag_groups_without sg s i.
Proof.
  intros; unfold flag_groups_rep, flag_groups_without.
  sep_apply_l_atomic (store_map_split
    (fun i v => flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) v) i v _ H); entailer!.
Qed.
Lemma flag_groups_merge_group : forall sg s i v,
  s.(flagImages) i = Some v ->
  flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) v ** flag_groups_without sg s i |-- flag_groups_rep sg s.
Proof.
  intros; unfold flag_groups_rep, flag_groups_without.
  sep_apply_l_atomic (store_map_merge
    (fun i v => flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) v) i v _ H); entailer!.
Qed.
Lemma flag_groups_merge_updated_group : forall sg s post i v,
  post.(flagImages) i = Some v ->
  (forall j, j <> i -> s.(flagImages) j = post.(flagImages) j) ->
  flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) v ** flag_groups_without sg s i |-- flag_groups_rep sg post.
Proof.
  intros sg s post i v H Hframe; unfold flag_groups_rep, flag_groups_without.
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun i v => flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) v) _ _ i Hframe)).
  sep_apply_l_atomic (store_map_merge
    (fun i v => flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) v) i v _ H); entailer!.
Qed.
Lemma flag_nodes_split_node : forall sg s p w,
  s.(flagWaitNodes) p = Some w -> flag_nodes_rep sg s |--
  flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage) ** flag_nodes_without sg s p.
Proof.
  intros; unfold flag_nodes_rep, flag_nodes_without, flag_wait_nodes_rep, flag_wait_nodes_without_node.
  sep_apply_l_atomic (store_map_split
    (fun p w => flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)) p w _ H); entailer!.
Qed.
Lemma flag_nodes_merge_node : forall sg s p w,
  s.(flagWaitNodes) p = Some w ->
  flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage) ** flag_nodes_without sg s p |-- flag_nodes_rep sg s.
Proof.
  intros; unfold flag_nodes_rep, flag_nodes_without, flag_wait_nodes_rep, flag_wait_nodes_without_node.
  sep_apply_l_atomic (store_map_merge
    (fun p w => flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)) p w _ H); entailer!.
Qed.

Definition flag_create_group (generation : nat) (bits name : Z) : FlagGroupState :=
  {| flagGeneration := generation; flagBits := bits; flagName := name; flagWaitOrder := [] |}.
Definition flag_create_image (old : FlagGroupImage) (bits name : Z) : FlagGroupImage :=
  {| flagImageType := 5; flagImageHead := 0; flagImageBits := bits;
     flagImageName := name; flagImagePadding := old.(flagImagePadding) |}.
Definition flag_delete_image (old : FlagGroupImage) (next name : Z) : FlagGroupImage :=
  {| flagImageType := 0; flagImageHead := next; flagImageBits := 0;
     flagImageName := name; flagImagePadding := old.(flagImagePadding) |}.
Definition flag_allocate (s : GlobFlagState) (bits name : Z) : option (FlagID * GlobFlagState) :=
  match s.(flagFree) with
  | [] => None
  | i :: rest => match s.(flagImages) i with
    | None => None
    | Some old => Some (i,
      {| flagUsed := kernel_map_set s.(flagUsed) i (Some (flag_create_group s.(flagNextGeneration) bits name));
         flagFree := rest;
         flagImages := kernel_map_set s.(flagImages) i (Some (flag_create_image old bits name));
         flagWaitNodes := s.(flagWaitNodes); flagNextGeneration := S s.(flagNextGeneration) |})
    end
  end.
Lemma flag_allocate_preserves_pool_partition : forall sg s bits name i post,
  kernel_pool_partition sg.(osKernelConfig).(cfgMaxFlags) s.(flagFree) s.(flagUsed) ->
  flag_allocate s bits name = Some (i, post) ->
  kernel_pool_partition sg.(osKernelConfig).(cfgMaxFlags) post.(flagFree) post.(flagUsed).
Proof.
  intros sg s bits name i post Hp H; unfold flag_allocate in H.
  destruct (flagFree s) as [|j rest]; [discriminate|].
  destruct (flagImages s j); [|discriminate].
  inversion H; subst; apply kernel_pool_allocate_preserves_partition; exact Hp.
Qed.
Lemma flag_allocate_preserves_state_validity : forall sg s bits name i post,
  valid_flag_state sg s -> flag_word_in_range sg.(osKernelConfig) bits ->
  flag_allocate s bits name = Some (i, post) -> valid_flag_state sg post.
Proof.
  intros sg s bits name i post [Hpool [Hdomain [Himages [Hused [Hfree Hnodes]]]]] Hb Hstep.
  unfold flag_allocate in Hstep.
  destruct (flagFree s) as [|j rest] eqn:HF; [discriminate|].
  destruct (flagImages s j) as [old|] eqn:HO; [|discriminate].
  inversion Hstep; subst i post; clear Hstep.
  pose proof Hpool as [Hnd [Hrange Hslots]].
  inversion Hnd as [|? ? Hnot Hrest]; subst.
  assert (Hid : 0 <= j < cfgMaxFlags (osKernelConfig sg)) by (apply Hrange; left; reflexivity).
  assert (Hunused : flagUsed s j = None).
  { destruct (flagUsed s j) as [g|] eqn:E; [|reflexivity].
    destruct (proj1 (Hslots j) (ex_intro _ g E)) as [_ Hnotfree].
    exfalso; apply Hnotfree; left; reflexivity. }
  unfold valid_flag_state; simpl.
  split; [apply kernel_pool_allocate_preserves_partition; exact Hpool|]. split.
  - intros k; destruct (Z.eq_dec k j) as [->|Hne].
    + rewrite kernel_map_set_same; split; [intros; exact Hid|eauto].
    + rewrite kernel_map_set_other by exact Hne; apply Hdomain.
  - split.
    + intros k image H; unfold kernel_map_set in H; destruct (Z.eq_dec k j) as [->|Hne].
      * inversion H; subst image; split; [exact Hb|exact (proj2 (Himages j old HO))].
      * eapply Himages; eauto.
    + split.
      * intros k group H; unfold kernel_map_set in H; destruct (Z.eq_dec k j) as [->|Hne].
        -- inversion H; subst group; split; [split; [exact Hb|constructor]|].
           split; [simpl; lia|]. split.
           ++ intros pre p suffix Hlist; destruct pre; discriminate.
           ++ exists (flag_create_image old bits name); split; [apply kernel_map_set_same|].
              repeat split; reflexivity.
        -- destruct (Hused k group H) as [Hvg [Hgen [Hwait [image [Him Hfields]]]]].
           split; [exact Hvg|]. split; [lia|]. split; [exact Hwait|].
           exists image; split; [rewrite kernel_map_set_other by exact Hne; exact Him|exact Hfields].
      * split.
        -- intros pre k suffix Hlist.
           assert (Hne : k <> j).
           { intro E; subst k; apply Hnot; rewrite Hlist; apply in_or_app; right; left; reflexivity. }
           assert (Hlist' : j :: rest = (j :: pre) ++ k :: suffix) by (rewrite Hlist; reflexivity).
           destruct (Hfree (j :: pre) k suffix Hlist') as [image [Him Hfields]].
           exists image; split; [rewrite kernel_map_set_other by exact Hne; exact Him|exact Hfields].
        -- intros p w Hw; destruct (Hnodes p w Hw) as [Hp0 [Hiv [g [Hg Hin]]]].
           assert (Hne : flagGroup w <> j) by (intro E; rewrite E, Hunused in Hg; discriminate).
           split; [exact Hp0|]. split; [exact Hiv|]. exists g; split; [|exact Hin].
           rewrite kernel_map_set_other by exact Hne; exact Hg.
Qed.

Definition flag_release (sg : StableGlobVars) (s : GlobFlagState) (i : FlagID)
  (old : FlagGroupImage) (name : Z) : GlobFlagState :=
  {| flagUsed := kernel_map_set s.(flagUsed) i None; flagFree := i :: s.(flagFree);
     flagImages := kernel_map_set s.(flagImages) i
       (Some (flag_delete_image old
         (match s.(flagFree) with [] => 0 | j :: _ => flag_pool_addr sg j end) name));
     flagWaitNodes := s.(flagWaitNodes); flagNextGeneration := s.(flagNextGeneration) |}.
Lemma flag_release_preserves_pool_partition : forall sg s i g old name,
  kernel_pool_partition sg.(osKernelConfig).(cfgMaxFlags) s.(flagFree) s.(flagUsed) ->
  s.(flagUsed) i = Some g ->
  kernel_pool_partition sg.(osKernelConfig).(cfgMaxFlags)
    (flag_release sg s i old name).(flagFree) (flag_release sg s i old name).(flagUsed).
Proof. intros; apply kernel_pool_release_preserves_partition with g; assumption. Qed.

Lemma flag_release_preserves_state_validity : forall sg s i g old name,
  valid_flag_state sg s -> s.(flagUsed) i = Some g -> s.(flagImages) i = Some old ->
  g.(flagWaitOrder) = [] -> valid_flag_state sg (flag_release sg s i old name).
Proof.
  intros sg s i g old name [Hpool [Hdomain [Himages [Hused [Hfree Hnodes]]]]] Hg HO Hempty.
  pose proof Hpool as [_ [_ Hslots]].
  destruct (proj1 (Hslots i) (ex_intro _ g Hg)) as [Hid Hnot].
  assert (Hvalidimage : flag_group_image_valid (osKernelConfig sg)
    (flag_delete_image old (match flagFree s with [] => 0 | j :: _ => flag_pool_addr sg j end) name)).
  { destruct (Himages i old HO) as [Hbits Hpad]; split; [|exact Hpad].
    unfold flag_word_in_range in Hbits |- *; simpl; lia. }
  unfold valid_flag_state, flag_release; simpl.
  split; [eapply kernel_pool_release_preserves_partition; eauto|]. split.
  - intros j; destruct (Z.eq_dec j i) as [->|Hne].
    + rewrite kernel_map_set_same; split; [intros; exact Hid|eauto].
    + rewrite kernel_map_set_other by exact Hne; apply Hdomain.
  - split.
    + intros j image H; unfold kernel_map_set in H; destruct (Z.eq_dec j i) as [->|Hne].
      * inversion H; subst image; exact Hvalidimage.
      * eapply Himages; eauto.
    + split.
      * intros j group H; unfold kernel_map_set in H; destruct (Z.eq_dec j i) as [->|Hne]; [discriminate|].
        destruct (Hused j group H) as [Hvg [Hgen [Hwait [image [Him Hfields]]]]].
        split; [exact Hvg|]. split; [exact Hgen|]. split; [exact Hwait|].
        exists image; split; [rewrite kernel_map_set_other by exact Hne; exact Him|exact Hfields].
      * split.
        -- intros pre j rest Hlist; destruct pre as [|a pre].
           ++ simpl in Hlist; inversion Hlist; subst j rest.
              eexists; split; [apply kernel_map_set_same|]; split; reflexivity.
           ++ simpl in Hlist; inversion Hlist as [[Ha Htail]]; subst a.
              assert (Hne : j <> i).
              { intro E; subst j; apply Hnot; rewrite Htail; apply in_or_app; right; left; reflexivity. }
              destruct (Hfree pre j rest Htail) as [image [Him Hfields]].
              exists image; split; [rewrite kernel_map_set_other by exact Hne; exact Him|exact Hfields].
        -- intros p w Hw; destruct (Hnodes p w Hw) as [Hp0 [Hiv [group [Hgr Hin]]]].
           assert (Hne : flagGroup w <> i).
           { intro E; rewrite E, Hg in Hgr; inversion Hgr; subst group; rewrite Hempty in Hin; contradiction. }
           split; [exact Hp0|]. split; [exact Hiv|]. exists group; split; [|exact Hin].
           rewrite kernel_map_set_other by exact Hne; exact Hgr.
Qed.

(** The detached node's own Next/Prev bytes are unchanged by OS_FlagUnlink.
    A second unlink therefore needs an actual linked-node precondition; a
    saved stack address alone cannot justify it after Delete's abort pass. *)
Definition flag_unlink_neighbors (v : FlagNodeImage) : addr * addr :=
  (v.(flagNodePrev), v.(flagNodeNext)).
Definition flag_node_return_loan (c : KernelConfiguration) (w : FlagWaiterState) : Assertion :=
  flag_node_rep c w.(flagNodeAddr) w.(flagWaitImage).
Definition flag_nodes_remove (s : GlobFlagState) (p : addr) : GlobFlagState :=
  {| flagUsed := s.(flagUsed); flagFree := s.(flagFree); flagImages := s.(flagImages);
     flagWaitNodes := kernel_map_set s.(flagWaitNodes) p None;
     flagNextGeneration := s.(flagNextGeneration) |}.
Lemma flag_nodes_remove_lookup : forall s p,
  (flag_nodes_remove s p).(flagWaitNodes) p = None.
Proof. intros; apply kernel_map_set_same. Qed.

Lemma flag_nodes_remove_transfers_node : forall sg s p w,
  s.(flagWaitNodes) p = Some w ->
  flag_nodes_rep sg s |-- flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage) **
    flag_nodes_rep sg (flag_nodes_remove s p).
Proof.
  intros sg s p w H; unfold flag_nodes_rep, flag_wait_nodes_rep, flag_nodes_remove; simpl.
  sep_apply_l_atomic (store_map_split
    (fun p w => flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)) p w _ H).
  assert (Hframe : forall j, j <> p -> flagWaitNodes s j = kernel_map_set (flagWaitNodes s) p None j).
  { intros; symmetry; apply kernel_map_set_other; assumption. }
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun p w => flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)) _ _ p Hframe)).
  sep_apply_l_atomic (store_map_missing_equiv_store_map
    (fun p w => flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)) _ p
      (kernel_map_set_same _ (flagWaitNodes s) p None)); entailer!.
Qed.

Definition flag_image_set_head (v : FlagGroupImage) (head : addr) : FlagGroupImage :=
  {| flagImageType := v.(flagImageType); flagImageHead := head; flagImageBits := v.(flagImageBits);
     flagImageName := v.(flagImageName); flagImagePadding := v.(flagImagePadding) |}.
Definition flag_image_set_bits (v : FlagGroupImage) (bits : Z) : FlagGroupImage :=
  {| flagImageType := v.(flagImageType); flagImageHead := v.(flagImageHead); flagImageBits := bits;
     flagImageName := v.(flagImageName); flagImagePadding := v.(flagImagePadding) |}.
Definition flag_group_set_wait_order (g : FlagGroupState) (order : list addr) : FlagGroupState :=
  {| flagGeneration := g.(flagGeneration); flagBits := g.(flagBits);
     flagName := g.(flagName); flagWaitOrder := order |}.
Definition flag_waiter_set_image (w : FlagWaiterState) (v : FlagNodeImage) : FlagWaiterState :=
  {| flagNodeAddr := w.(flagNodeAddr); flagTask := w.(flagTask);
     flagTaskGeneration := w.(flagTaskGeneration);
     flagGroup := w.(flagGroup); flagGroupGeneration := w.(flagGroupGeneration);
     flagMask := w.(flagMask); flagWaitMode := w.(flagWaitMode); flagWaitImage := v |}.
Definition flag_node_set_links (v : FlagNodeImage) (next prev : addr) : FlagNodeImage :=
  {| flagNodeNext := next; flagNodePrev := prev; flagNodeTCB := v.(flagNodeTCB);
     flagNodeGroup := v.(flagNodeGroup); flagNodeMask := v.(flagNodeMask);
     flagNodeMode := v.(flagNodeMode); flagNodePadding := v.(flagNodePadding) |}.
Definition flag_nodes_set_prev (nodes : addr -> option FlagWaiterState) (p prev : addr) :=
  kernel_map_set nodes p (option_map
    (fun w => flag_waiter_set_image w (flag_node_set_links w.(flagWaitImage) w.(flagWaitImage).(flagNodeNext) prev))
    (nodes p)).
Definition flag_nodes_set_next (nodes : addr -> option FlagWaiterState) (p next : addr) :=
  kernel_map_set nodes p (option_map
    (fun w => flag_waiter_set_image w (flag_node_set_links w.(flagWaitImage) next w.(flagWaitImage).(flagNodePrev)))
    (nodes p)).

(** Link writes must not change the Task/Group instance or the TCB,
    group and wait arguments stored in its stack node. This projection
    is shared with cross-module continuation proofs; it owns no bytes. *)
Definition flag_waiter_link_identity (w : FlagWaiterState) :=
  (w.(flagNodeAddr), w.(flagTask), w.(flagTaskGeneration),
   w.(flagGroup), w.(flagGroupGeneration), w.(flagMask), w.(flagWaitMode),
   w.(flagWaitImage).(flagNodeTCB), w.(flagWaitImage).(flagNodeGroup),
   w.(flagWaitImage).(flagNodeMask), w.(flagWaitImage).(flagNodeMode),
   w.(flagWaitImage).(flagNodePadding)).
Lemma flag_waiter_set_links_identity_eq : forall w next prev,
  flag_waiter_link_identity
    (flag_waiter_set_image w (flag_node_set_links w.(flagWaitImage) next prev)) =
  flag_waiter_link_identity w.
Proof. reflexivity. Qed.
Lemma flag_nodes_set_prev_identity_frame : forall nodes p prev q,
  option_map flag_waiter_link_identity (flag_nodes_set_prev nodes p prev q) =
  option_map flag_waiter_link_identity (nodes q).
Proof.
  intros; unfold flag_nodes_set_prev, kernel_map_set.
  destruct (Z.eq_dec q p) as [->|Hne]; [destruct (nodes p); reflexivity|reflexivity].
Qed.
Lemma flag_nodes_set_next_identity_frame : forall nodes p next q,
  option_map flag_waiter_link_identity (flag_nodes_set_next nodes p next q) =
  option_map flag_waiter_link_identity (nodes q).
Proof.
  intros; unfold flag_nodes_set_next, kernel_map_set.
  destruct (Z.eq_dec q p) as [->|Hne]; [destruct (nodes p); reflexivity|reflexivity].
Qed.

(** These pure functions follow the physical write order.  Pointer
    dereferences still require the corresponding focused node/group rep.
    The logical order update is justified only for a linked, unique node. *)
Definition flag_unlink_neighbor_nodes (nodes : addr -> option FlagWaiterState) (w : FlagWaiterState) :=
  let prev := w.(flagWaitImage).(flagNodePrev) in
  let next := w.(flagWaitImage).(flagNodeNext) in
  let nodes1 := if Z.eqb prev 0 then nodes else flag_nodes_set_next nodes prev next in
  if Z.eqb next 0 then nodes1 else flag_nodes_set_prev nodes1 next prev.

Definition flag_unlink_node (s : GlobFlagState) (p : addr) : option (FlagWaiterState * GlobFlagState) :=
  match s.(flagWaitNodes) p with
  | None => None
  | Some w => match s.(flagUsed) w.(flagGroup), s.(flagImages) w.(flagGroup) with
    | Some g, Some v =>
      let prev := w.(flagWaitImage).(flagNodePrev) in
      let next := w.(flagWaitImage).(flagNodeNext) in
      let nodes2 := flag_unlink_neighbor_nodes s.(flagWaitNodes) w in
      Some (w, {| flagUsed := kernel_map_set s.(flagUsed) w.(flagGroup)
                    (Some (flag_group_set_wait_order g (remove Z.eq_dec p g.(flagWaitOrder))));
        flagFree := s.(flagFree);
        flagImages := if Z.eqb prev 0 then kernel_map_set s.(flagImages) w.(flagGroup)
                        (Some (flag_image_set_head v next)) else s.(flagImages);
        flagWaitNodes := kernel_map_set nodes2 p None; flagNextGeneration := s.(flagNextGeneration) |})
    | _, _ => None end
  end.
Lemma flag_linked_node_unlink_exists : forall sg s p w,
  valid_flag_state sg s -> s.(flagWaitNodes) p = Some w ->
  exists post, flag_unlink_node s p = Some (w, post).
Proof.
  intros sg s p w [_ [_ [_ [Hgroups [_ Hnodes]]]]] Hw.
  destruct (Hnodes p w Hw) as [_ [_ [g [Hg _]]]].
  destruct (Hgroups w.(flagGroup) g Hg) as [_ [_ [_ [v [Hv _]]]]].
  unfold flag_unlink_node; rewrite Hw, Hg, Hv; eexists; reflexivity.
Qed.

Lemma flag_unlink_removes_node_and_keeps_its_image : forall s p w post,
  flag_unlink_node s p = Some (w, post) ->
  s.(flagWaitNodes) p = Some w /\ post.(flagWaitNodes) p = None.
Proof.
  intros s p w post H; unfold flag_unlink_node, flag_unlink_neighbor_nodes in H.
  destruct (flagWaitNodes s p) as [old|] eqn:E; [|discriminate].
  destruct (flagUsed s (flagGroup old)), (flagImages s (flagGroup old)); try discriminate.
  inversion H; subst; split; [reflexivity|apply kernel_map_set_same].
Qed.
Lemma flag_unlink_twice_is_not_a_linked_transition : forall s p w post,
  flag_unlink_node s p = Some (w, post) -> flag_unlink_node post p = None.
Proof.
  intros s p w post H; apply flag_unlink_removes_node_and_keeps_its_image in H.
  unfold flag_unlink_node, flag_unlink_neighbor_nodes; rewrite (proj2 H); reflexivity.
Qed.
Lemma flag_unlink_frames_waiter_identity : forall s p w post q,
  flag_unlink_node s p = Some (w, post) -> q <> p ->
  option_map flag_waiter_link_identity (post.(flagWaitNodes) q) =
  option_map flag_waiter_link_identity (s.(flagWaitNodes) q).
Proof.
  intros s p w post q Hstep Hne; unfold flag_unlink_node, flag_unlink_neighbor_nodes in Hstep.
  destruct (flagWaitNodes s p) as [old|]; [|discriminate].
  destruct (flagUsed s (flagGroup old)), (flagImages s (flagGroup old)); try discriminate.
  inversion Hstep; subst w post; simpl; rewrite kernel_map_set_other by exact Hne.
  destruct (Z.eqb (flagNodeNext (flagWaitImage old)) 0);
    destruct (Z.eqb (flagNodePrev (flagWaitImage old)) 0);
    rewrite ?flag_nodes_set_prev_identity_frame, ?flag_nodes_set_next_identity_frame; reflexivity.
Qed.
Lemma flag_unlink_frames_unrelated_node : forall s p w post q,
  flag_unlink_node s p = Some (w, post) ->
  q <> p -> q <> w.(flagWaitImage).(flagNodePrev) -> q <> w.(flagWaitImage).(flagNodeNext) ->
  post.(flagWaitNodes) q = s.(flagWaitNodes) q.
Proof.
  intros s p w post q Hstep Hp Hprev Hnext; unfold flag_unlink_node, flag_unlink_neighbor_nodes in Hstep.
  destruct (flagWaitNodes s p) as [old|]; [|discriminate].
  destruct (flagUsed s (flagGroup old)), (flagImages s (flagGroup old)); try discriminate.
  inversion Hstep; subst w post; simpl; rewrite kernel_map_set_other by exact Hp.
  destruct (Z.eqb (flagNodeNext (flagWaitImage old)) 0);
    destruct (Z.eqb (flagNodePrev (flagWaitImage old)) 0);
    unfold flag_nodes_set_prev, flag_nodes_set_next;
    rewrite ?kernel_map_set_other by assumption; reflexivity.
Qed.
Lemma flag_unlink_preserves_group_order_validity : forall c g p,
  valid_flag_group c g -> valid_flag_group c (flag_group_set_wait_order g (remove Z.eq_dec p g.(flagWaitOrder))).
Proof.
  intros c g p [Hb Hnd]; split; [exact Hb|]. simpl.
  apply kernel_list_remove_preserves_nodup; exact Hnd.
Qed.

Definition flag_block_node_image (sg : StableGlobVars) (w : FlagWaiterState)
  (tcb head : addr) : FlagNodeImage :=
  {| flagNodeNext := head; flagNodePrev := 0; flagNodeTCB := tcb;
     flagNodeGroup := flag_pool_addr sg w.(flagGroup); flagNodeMask := w.(flagMask);
     flagNodeMode := encode_flag_wait_mode w.(flagWaitMode);
     flagNodePadding := w.(flagWaitImage).(flagNodePadding) |}.

Definition flag_block_node (sg : StableGlobVars) (s : GlobFlagState) (w : FlagWaiterState)
  (tcb : addr) : option GlobFlagState :=
  match s.(flagUsed) w.(flagGroup), s.(flagImages) w.(flagGroup) with
  | Some g, Some v =>
    let image := flag_block_node_image sg w tcb v.(flagImageHead) in
    let nodes1 := kernel_map_set s.(flagWaitNodes) w.(flagNodeAddr) (Some (flag_waiter_set_image w image)) in
    let nodes2 := if Z.eqb v.(flagImageHead) 0 then nodes1 else
      flag_nodes_set_prev nodes1 v.(flagImageHead) w.(flagNodeAddr) in
    Some {| flagUsed := kernel_map_set s.(flagUsed) w.(flagGroup)
                  (Some (flag_group_set_wait_order g (w.(flagNodeAddr) :: g.(flagWaitOrder))));
      flagFree := s.(flagFree); flagImages := kernel_map_set s.(flagImages) w.(flagGroup)
                  (Some (flag_image_set_head v w.(flagNodeAddr)));
      flagWaitNodes := nodes2; flagNextGeneration := s.(flagNextGeneration) |}
  | _, _ => None
  end.
Lemma flag_block_preserves_group_order_validity : forall c g p,
  valid_flag_group c g -> ~ In p g.(flagWaitOrder) ->
  valid_flag_group c (flag_group_set_wait_order g (p :: g.(flagWaitOrder))).
Proof. intros c g p [Hb Hnd] Hnot; split; [exact Hb|constructor; assumption]. Qed.

Definition flag_initial_padding (c : KernelConfiguration) : list (option Z) :=
  repeat (if c.(cfgMaxFlags) <? 2 then None else Some 0)
    (Z.to_nat (3 + flag_group_name_offset c - (8 + flag_word_bytes c))).
Definition flag_initial_image (sg : StableGlobVars) (name : addr) (i : FlagID) : FlagGroupImage :=
  {| flagImageType := 0;
     flagImageHead := match kernel_list_next (Zrange 0 sg.(osKernelConfig).(cfgMaxFlags)) i with
       | None => 0 | Some j => flag_pool_addr sg j end;
     flagImageBits := 0; flagImageName := name;
     flagImagePadding := flag_initial_padding sg.(osKernelConfig) |}.
Definition flag_initial (sg : StableGlobVars) (name : addr) : GlobFlagState :=
  {| flagUsed := fun _ => None; flagFree := Zrange 0 sg.(osKernelConfig).(cfgMaxFlags);
     flagImages := fun i => if andb (0 <=? i) (i <? sg.(osKernelConfig).(cfgMaxFlags))
       then Some (flag_initial_image sg name i) else None;
     flagWaitNodes := fun _ => None; flagNextGeneration := 0 |}.
Lemma flag_initial_valid : forall sg name,
  0 <= sg.(osKernelConfig).(cfgFlagBits) ->
  0 <= 3 + flag_group_name_offset sg.(osKernelConfig) - (8 + flag_word_bytes sg.(osKernelConfig)) ->
  valid_flag_state sg (flag_initial sg name).
Proof.
  intros sg name Hbits Hpad; unfold valid_flag_state, flag_initial; simpl.
  split; [apply kernel_pool_initial_partition|]. split.
  - intro i; destruct (andb (0 <=? i) (i <? cfgMaxFlags (osKernelConfig sg))) eqn:E.
    + apply Bool.andb_true_iff in E; destruct E as [Hl Hh].
      apply Z.leb_le in Hl; apply Z.ltb_lt in Hh; split; [intros; lia|eauto].
    + split; [intros [v H]; discriminate|]. intros [Hl Hh].
      assert (andb (0 <=? i) (i <? cfgMaxFlags (osKernelConfig sg)) = true)
        by (apply Bool.andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia); congruence.
  - split.
    + intros i v H; destruct (andb (0 <=? i) (i <? cfgMaxFlags (osKernelConfig sg))); [|discriminate].
      inversion H; subst; unfold flag_group_image_valid, flag_initial_image, flag_initial_padding; simpl.
      split.
      * unfold flag_word_in_range; split; [lia|apply Z.pow_pos_nonneg; lia].
      * rewrite repeat_length; apply Z2Nat.id; exact Hpad.
    + split; [intros; discriminate|]. split.
      * intros pre i rest Hlist.
        assert (Hi : 0 <= i < cfgMaxFlags (osKernelConfig sg)).
        { apply In_Zrange; rewrite Hlist; apply in_or_app; right; left; reflexivity. }
        assert (Hb : andb (0 <=? i) (i <? cfgMaxFlags (osKernelConfig sg)) = true)
          by (apply Bool.andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        rewrite Hb; exists (flag_initial_image sg name i); split; [reflexivity|].
        split; [reflexivity|]. unfold flag_initial_image; simpl; rewrite Hlist, kernel_list_next_at.
        -- destruct rest; reflexivity.
        -- pose proof (NoDup_Zrange 0 (cfgMaxFlags (osKernelConfig sg))) as Hnd.
           rewrite Hlist in Hnd; exact Hnd.
      * intros; discriminate.
Qed.
Lemma flag_initial_has_group : forall sg name,
  0 < sg.(osKernelConfig).(cfgMaxFlags) -> exists v, (flag_initial sg name).(flagImages) 0 = Some v.
Proof.
  intros sg name H; unfold flag_initial; simpl.
  assert (Hlt : (0 <? cfgMaxFlags (osKernelConfig sg)) = true) by (apply Z.ltb_lt; lia).
  rewrite Hlt; eauto.
Qed.

Definition flag_replace_bits (s : GlobFlagState) (i : FlagID)
  (g : FlagGroupState) (v : FlagGroupImage) (bits : Z) : GlobFlagState :=
  {| flagUsed := kernel_map_set s.(flagUsed) i (Some (flag_group_set_bits g bits));
     flagFree := s.(flagFree); flagImages := kernel_map_set s.(flagImages) i (Some (flag_image_set_bits v bits));
     flagWaitNodes := s.(flagWaitNodes); flagNextGeneration := s.(flagNextGeneration) |}.
Lemma flag_replace_bits_preserves_validity : forall sg s i g v bits,
  valid_flag_state sg s -> s.(flagUsed) i = Some g -> s.(flagImages) i = Some v ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  valid_flag_state sg (flag_replace_bits s i g v bits).
Proof.
  intros sg s i g v bits [Hpool [Hdomain [Himages [Hused [Hfree Hnodes]]]]] Hg Hv Hb.
  assert (Hnot : ~ In i (flagFree s)).
  { destruct Hpool as [_ [_ Hdom]].
    exact (proj2 (proj1 (Hdom i) (ex_intro _ g Hg))). }
  destruct (Hused i g Hg) as [[Hbits Hnd] [Hgen [Hwait [v0 [Hv0 [Htype [Hhead [Hbits0 Hname]]]]]]]].
  rewrite Hv in Hv0; inversion Hv0; subst v0.
  unfold valid_flag_state, flag_replace_bits; simpl.
  split; [eapply kernel_pool_replace_preserves_partition; eauto|]. split.
  - intro j; destruct (Z.eq_dec j i) as [->|Hne].
    + rewrite kernel_map_set_same; split.
      * intros _; apply (proj1 (Hdomain i)); exists v; exact Hv.
      * intros _; eauto.
    + rewrite kernel_map_set_other by exact Hne; apply Hdomain.
  - split.
    + intros j image H; unfold kernel_map_set in H; destruct (Z.eq_dec j i) as [->|Hne].
      * inversion H; subst; unfold flag_group_image_valid, flag_image_set_bits; simpl.
        split; [exact Hb|exact (proj2 (Himages i v Hv))].
      * eapply Himages; eauto.
    + split.
      * intros j group H; unfold kernel_map_set in H; destruct (Z.eq_dec j i) as [->|Hne].
        -- inversion H; subst group; split; [split; [exact Hb|exact Hnd]|].
           split; [exact Hgen|]. split; [exact Hwait|].
           exists (flag_image_set_bits v bits); split; [apply kernel_map_set_same|].
           unfold flag_image_set_bits, flag_group_set_bits; simpl; auto.
        -- destruct (Hused j group H) as [Hvg [Hgg [Hwg [image [Him Hprops]]]]].
           split; [exact Hvg|]. split; [exact Hgg|]. split; [exact Hwg|].
           exists image; split; [rewrite kernel_map_set_other by exact Hne; exact Him|exact Hprops].
      * split.
        -- intros pre j rest Hlist.
           assert (Hne : j <> i).
           { intro E; subst j; apply Hnot; rewrite Hlist; apply in_or_app; right; left; reflexivity. }
           destruct (Hfree pre j rest Hlist) as [image [Him Hprops]].
           exists image; split; [rewrite kernel_map_set_other by exact Hne; exact Him|exact Hprops].
        -- intros p w H; destruct (Hnodes p w H) as [Hnonzero [Hiv [group [Hgr Hin]]]].
           split; [exact Hnonzero|]. split; [exact Hiv|]. destruct (Z.eq_dec (flagGroup w) i) as [Heq|Hne].
           ++ rewrite Heq in Hgr; rewrite Hg in Hgr; inversion Hgr; subst group.
              exists (flag_group_set_bits g bits); split; [rewrite Heq; apply kernel_map_set_same|exact Hin].
           ++ exists group; split; [rewrite kernel_map_set_other by exact Hne; exact Hgr|exact Hin].
Qed.

Definition flag_accept (sg : StableGlobVars) (s : GlobFlagState) (i : FlagID) (mask wait_type : Z)
  : option (Z * OSErrCode * GlobFlagState) :=
  match s.(flagUsed) i, s.(flagImages) i with
  | Some g, Some v =>
    let '(bits, ready, err) := flag_accept_bits sg.(osKernelConfig) g.(flagBits) mask wait_type in
    Some (ready, err, flag_replace_bits s i g v bits)
  | _, _ => None
  end.
Definition flag_post_word (sg : StableGlobVars) (s : GlobFlagState) (i : FlagID) (mask opt : Z)
  : option GlobFlagState :=
  match s.(flagUsed) i, s.(flagImages) i with
  | Some g, Some v => match flag_post_bits sg.(osKernelConfig) g.(flagBits) mask opt with
    | None => None | Some bits => Some (flag_replace_bits s i g v bits) end
  | _, _ => None
  end.
Definition flag_resume_consume (sg : StableGlobVars) (s : GlobFlagState) (i : FlagID)
  (ready : Z) (mode : FlagWaitMode) (consume : bool) : option GlobFlagState :=
  match s.(flagUsed) i, s.(flagImages) i with
  | Some g, Some v => Some (flag_replace_bits s i g v
      (flag_resume_bits sg.(osKernelConfig) g.(flagBits) ready mode consume))
  | _, _ => None
  end.
Lemma flag_accept_bits_preserves_word_range : forall c bits mask wait_type post ready err,
  0 <= c.(cfgFlagBits) -> flag_word_in_range c bits ->
  flag_accept_bits c bits mask wait_type = (post, ready, err) -> flag_word_in_range c post.
Proof.
  intros c bits mask wait_type post ready err Hc Hb H; unfold flag_accept_bits in H.
  destruct (decode_flag_wait_mode c (Z.land wait_type 127)) as [mode|]; [|inversion H; subst; exact Hb].
  destruct (flag_wait_satisfied mode (flag_ready_bits c bits mask mode) mask);
    [destruct (Z.testbit wait_type 7)|]; inversion H; subst; auto.
  apply flag_consume_bits_in_range; exact Hc.
Qed.
Lemma flag_accept_preserves_state_validity : forall sg s i mask wait_type ready err post,
  0 <= sg.(osKernelConfig).(cfgFlagBits) -> valid_flag_state sg s ->
  flag_accept sg s i mask wait_type = Some (ready, err, post) -> valid_flag_state sg post.
Proof.
  intros sg s i mask wait_type ready err post Hc Hv H; unfold flag_accept in H.
  destruct (flagUsed s i) as [g|] eqn:Eg, (flagImages s i) as [v|] eqn:Ev; try discriminate.
  destruct (flag_accept_bits (osKernelConfig sg) (flagBits g) mask wait_type) as [[bits r] e] eqn:E.
  inversion H; subst; eapply flag_replace_bits_preserves_validity; eauto.
  eapply flag_accept_bits_preserves_word_range; eauto.
  destruct Hv as [_ [_ [_ [Hused _]]]]; exact (proj1 (proj1 (Hused i g Eg))).
Qed.
Lemma flag_post_word_preserves_state_validity : forall sg s i mask opt post,
  0 <= sg.(osKernelConfig).(cfgFlagBits) -> valid_flag_state sg s ->
  flag_post_word sg s i mask opt = Some post -> valid_flag_state sg post.
Proof.
  intros sg s i mask opt post Hc Hv H; unfold flag_post_word in H.
  destruct (flagUsed s i) as [g|] eqn:Eg, (flagImages s i) as [v|] eqn:Ev; try discriminate.
  destruct (flag_post_bits (osKernelConfig sg) (flagBits g) mask opt) eqn:E; [|discriminate].
  inversion H; subst; eapply flag_replace_bits_preserves_validity; eauto.
  eapply flag_post_bits_in_range; eauto.
Qed.
Lemma flag_resume_consume_preserves_state_validity : forall sg s i ready mode consume post,
  0 <= sg.(osKernelConfig).(cfgFlagBits) -> valid_flag_state sg s ->
  flag_resume_consume sg s i ready mode consume = Some post -> valid_flag_state sg post.
Proof.
  intros sg s i ready mode consume post Hc Hv H; unfold flag_resume_consume in H.
  destruct (flagUsed s i) as [g|] eqn:Eg, (flagImages s i) as [v|] eqn:Ev; try discriminate.
  inversion H; subst; eapply flag_replace_bits_preserves_validity; eauto.
  unfold flag_resume_bits; destruct consume; [apply flag_consume_bits_in_range; exact Hc|].
  destruct Hv as [_ [_ [_ [Hused _]]]]; exact (proj1 (proj1 (Hused i g Eg))).
Qed.

Lemma flag_nodes_set_next_lookup : forall nodes target next p,
  flag_nodes_set_next nodes target next p =
  option_map (fun w => if Z.eq_dec p target then flag_waiter_set_image w
    (flag_node_set_links w.(flagWaitImage) next w.(flagWaitImage).(flagNodePrev)) else w) (nodes p).
Proof.
  intros; unfold flag_nodes_set_next, kernel_map_set.
  destruct (Z.eq_dec p target) as [->|Hne]; [destruct (nodes target)|destruct (nodes p)]; reflexivity.
Qed.

Lemma flag_nodes_set_prev_lookup : forall nodes target prev p,
  flag_nodes_set_prev nodes target prev p =
  option_map (fun w => if Z.eq_dec p target then flag_waiter_set_image w
    (flag_node_set_links w.(flagWaitImage) w.(flagWaitImage).(flagNodeNext) prev) else w) (nodes p).
Proof.
  intros; unfold flag_nodes_set_prev, kernel_map_set.
  destruct (Z.eq_dec p target) as [->|Hne]; [destruct (nodes target)|destruct (nodes p)]; reflexivity.
Qed.

Lemma flag_unlink_updates_neighbor_links : forall s p w post q before,
  flag_unlink_node s p = Some (w, post) -> q <> p -> q <> 0 -> s.(flagWaitNodes) q = Some before ->
  exists after, post.(flagWaitNodes) q = Some after /\
    flag_waiter_link_identity after = flag_waiter_link_identity before /\
    after.(flagWaitImage).(flagNodeNext) =
      (if Z.eq_dec q w.(flagWaitImage).(flagNodePrev) then w.(flagWaitImage).(flagNodeNext)
        else before.(flagWaitImage).(flagNodeNext)) /\
    after.(flagWaitImage).(flagNodePrev) =
      (if Z.eq_dec q w.(flagWaitImage).(flagNodeNext) then w.(flagWaitImage).(flagNodePrev)
        else before.(flagWaitImage).(flagNodePrev)).
Proof.
  intros s p w post q before Hstep Hqp Hq0 Hbefore.
  unfold flag_unlink_node, flag_unlink_neighbor_nodes in Hstep; destruct (flagWaitNodes s p) as [old|]; [|discriminate].
  destruct (flagUsed s (flagGroup old)), (flagImages s (flagGroup old)); try discriminate.
  inversion Hstep; subst w post; simpl; rewrite kernel_map_set_other by exact Hqp.
  destruct (Z.eqb (flagNodePrev (flagWaitImage old)) 0) eqn:Ep;
    destruct (Z.eqb (flagNodeNext (flagWaitImage old)) 0) eqn:En;
    rewrite ?flag_nodes_set_prev_lookup, ?flag_nodes_set_next_lookup, Hbefore;
    simpl; destruct (Z.eq_dec q (flagNodePrev (flagWaitImage old))) as [Eprev|Nprev];
    destruct (Z.eq_dec q (flagNodeNext (flagWaitImage old))) as [Enext|Nnext];
    try (apply Z.eqb_eq in Ep; exfalso; apply Hq0; congruence);
    try (apply Z.eqb_eq in En; exfalso; apply Hq0; congruence);
    eexists; repeat split; reflexivity.
Qed.

Lemma flag_wait_list_member_group : forall sg s i g p w,
  flag_wait_list_valid sg s i g -> In p g.(flagWaitOrder) ->
  s.(flagWaitNodes) p = Some w -> w.(flagGroup) = i.
Proof.
  intros sg s i g p w Hwait Hin Hw; apply in_split in Hin; destruct Hin as [pre [rest Heq]].
  destruct (Hwait pre p rest Heq) as [old [Hold [_ [Hg _]]]].
  rewrite Hw in Hold; inversion Hold; subst old; exact Hg.
Qed.

Lemma flag_unlink_frames_other_group_nodes : forall sg s p w post q before,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  s.(flagWaitNodes) q = Some before -> before.(flagGroup) <> w.(flagGroup) ->
  post.(flagWaitNodes) q = Some before.
Proof.
  intros sg s p w post q before Hvalid Hstep Hq Hgroup.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hp.
  assert (Hqp : q <> p) by (intro Heq; subst q; rewrite Hp in Hq; congruence).
  pose proof (valid_flag_state_node_nonzero _ _ _ _ Hvalid Hq) as Hq0.
  destruct (valid_flag_state_node_position _ _ _ _ Hvalid Hp) as
    [g [pre [rest [Hg [Hlist [_ [_ [_ [Hprev [Hnext _]]]]]]]]]].
  destruct Hvalid as [_ [_ [_ [Hused _]]]].
  destruct (Hused _ g Hg) as [[Hbits Hnd] [_ [Hwait _]]].
  assert (Hndlist : NoDup (pre ++ p :: rest)) by (rewrite <- Hlist; exact Hnd).
  assert (Hprevq : q <> flagNodePrev (flagWaitImage w)).
  { intro Heq; apply Hgroup; eapply flag_wait_list_member_group; [exact Hwait| |exact Hq].
    assert (Heq' : kernel_list_previous_addr (flagWaitOrder g) p = q).
    { rewrite Hlist. transitivity (last pre 0); [exact (kernel_list_previous_addr_at pre p rest Hndlist)|congruence]. }
    apply kernel_list_previous_addr_eq in Heq'; [|exact Hq0].
    eapply kernel_list_previous_some_in; eauto. }
  assert (Hnextq : q <> flagNodeNext (flagWaitImage w)).
  { intro Heq; apply Hgroup; eapply flag_wait_list_member_group; [exact Hwait| |exact Hq].
    assert (Heq' : kernel_list_next_addr (flagWaitOrder g) p = q).
    { rewrite Hlist. transitivity (hd 0 rest); [exact (kernel_list_next_addr_at pre p rest Hndlist)|congruence]. }
    apply kernel_list_next_addr_eq in Heq'; [|exact Hq0].
    eapply kernel_list_next_some_in; eauto. }
  rewrite (flag_unlink_frames_unrelated_node _ _ _ _ _ Hstep Hqp Hprevq Hnextq); exact Hq.
Qed.

Lemma flag_unlink_preserves_own_wait_list : forall sg s p w post g,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) -> s.(flagUsed) w.(flagGroup) = Some g ->
  flag_wait_list_valid sg post w.(flagGroup)
    (flag_group_set_wait_order g (remove Z.eq_dec p g.(flagWaitOrder))).
Proof.
  intros sg s p w post g Hvalid Hstep Hg.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hp.
  pose proof (valid_flag_state_node_nonzero _ _ _ _ Hvalid Hp) as Hp0.
  destruct (valid_flag_state_node_position _ _ _ _ Hvalid Hp) as
    [g0 [ppre [prest [Hg0 [Hplist [_ [_ [_ [Hpprev [Hpnext _]]]]]]]]]].
  rewrite Hg in Hg0; inversion Hg0; subst g0; clear Hg0.
  destruct Hvalid as [Hpool [Hdomain [Himages [Hused [Hfree Hnodes]]]]].
  destruct (Hused _ g Hg) as [[Hbits Hnd] [Hgen [Hwait Himage]]].
  assert (Hndpost : NoDup (remove Z.eq_dec p (flagWaitOrder g)))
    by (exact (proj2 (flag_unlink_preserves_group_order_validity _ _ p (conj Hbits Hnd)))).
  assert (Hndp : NoDup (ppre ++ p :: prest)) by (rewrite <- Hplist; exact Hnd).
  assert (Hpprev' : flagNodePrev (flagWaitImage w) = kernel_list_previous_addr (flagWaitOrder g) p).
  { rewrite Hplist; transitivity (last ppre 0); [exact Hpprev|symmetry; exact (kernel_list_previous_addr_at ppre p prest Hndp)]. }
  assert (Hpnext' : flagNodeNext (flagWaitImage w) = kernel_list_next_addr (flagWaitOrder g) p).
  { rewrite Hplist; transitivity (hd 0 prest); [exact Hpnext|symmetry; exact (kernel_list_next_addr_at ppre p prest Hndp)]. }
  intros pre q rest Hlist; simpl in Hlist.
  assert (Hin : In q (remove Z.eq_dec p (flagWaitOrder g)))
    by (rewrite Hlist; apply in_or_app; right; left; reflexivity).
  apply in_remove in Hin; destruct Hin as [Hin Hqp].
  apply in_split in Hin; destruct Hin as [qpre [qrest Hqorder]].
  destruct (Hwait qpre q qrest Hqorder) as [before [Hbefore
    [Haddr [Hgroup [Hgg [Hig [Hprev [Hnext [Hmask Hmode]]]]]]]]].
  pose proof (proj1 (Hnodes q before Hbefore)) as Hq0.
  destruct (flag_unlink_updates_neighbor_links _ _ _ _ _ _ Hstep Hqp Hq0 Hbefore) as
    [after [Hafter [Hidentity [Hnewnext Hnewprev]]]].
  pose proof Hnd as Hndq; rewrite Hqorder in Hndq.
  pose proof Hndpost as Hndafter; rewrite Hlist in Hndafter.
  assert (Hprev' : flagNodePrev (flagWaitImage before) = kernel_list_previous_addr (flagWaitOrder g) q).
  { rewrite Hqorder; transitivity (last qpre 0); [exact Hprev|symmetry; exact (kernel_list_previous_addr_at qpre q qrest Hndq)]. }
  assert (Hnext' : flagNodeNext (flagWaitImage before) = kernel_list_next_addr (flagWaitOrder g) q).
  { rewrite Hqorder; transitivity (hd 0 qrest); [exact Hnext|symmetry; exact (kernel_list_next_addr_at qpre q qrest Hndq)]. }
  assert (Hafterprev : flagNodePrev (flagWaitImage after) = last pre 0).
  { transitivity (kernel_list_previous_addr (remove Z.eq_dec p (flagWaitOrder g)) q).
    - rewrite Hnewprev, Hpnext', Hpprev', Hprev'; symmetry; apply kernel_list_previous_addr_remove; assumption.
    - rewrite Hlist; exact (kernel_list_previous_addr_at pre q rest Hndafter). }
  assert (Hafternext : flagNodeNext (flagWaitImage after) = hd 0 rest).
  { transitivity (kernel_list_next_addr (remove Z.eq_dec p (flagWaitOrder g)) q).
    - rewrite Hnewnext, Hpprev', Hpnext', Hnext'; symmetry; apply kernel_list_next_addr_remove; assumption.
    - rewrite Hlist; exact (kernel_list_next_addr_at pre q rest Hndafter). }
  unfold flag_waiter_link_identity in Hidentity; inversion Hidentity.
  exists after; split; [exact Hafter|]. simpl; repeat split; congruence.
Qed.

Lemma valid_flag_wait_order_nonzero : forall sg s i g,
  valid_flag_state sg s -> s.(flagUsed) i = Some g -> forall p, In p g.(flagWaitOrder) -> p <> 0.
Proof.
  intros sg s i g Hvalid Hg p Hin; pose proof Hvalid as [_ [_ [_ [Hused _]]]].
  destruct (Hused i g Hg) as [_ [_ [Hwait _]]].
  apply in_split in Hin; destruct Hin as [pre [rest Hlist]].
  destruct (Hwait pre p rest Hlist) as [w [Hw _]].
  eapply valid_flag_state_node_nonzero; eauto.
Qed.

Lemma flag_unlink_preserves_other_wait_list : forall sg s p w post i g,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  s.(flagUsed) i = Some g -> i <> w.(flagGroup) -> flag_wait_list_valid sg post i g.
Proof.
  intros sg s p w post i g Hv Hstep Hg Hne.
  pose proof Hv as [_ [_ [_ [Hused _]]]].
  destruct (Hused i g Hg) as [_ [_ [Hwait _]]].
  intros pre q rest Hlist; destruct (Hwait pre q rest Hlist) as [before [Hbefore Hfields]].
  exists before; split; [|exact Hfields].
  eapply flag_unlink_frames_other_group_nodes; eauto; intuition congruence.
Qed.

Lemma flag_unlink_group_fields : forall s p w post g v,
  flag_unlink_node s p = Some (w, post) -> s.(flagUsed) w.(flagGroup) = Some g ->
  s.(flagImages) w.(flagGroup) = Some v ->
  post.(flagUsed) = kernel_map_set s.(flagUsed) w.(flagGroup)
    (Some (flag_group_set_wait_order g (remove Z.eq_dec p g.(flagWaitOrder)))) /\
  post.(flagImages) = (if Z.eqb w.(flagWaitImage).(flagNodePrev) 0 then
    kernel_map_set s.(flagImages) w.(flagGroup) (Some (flag_image_set_head v w.(flagWaitImage).(flagNodeNext)))
    else s.(flagImages)) /\
  post.(flagFree) = s.(flagFree) /\ post.(flagNextGeneration) = s.(flagNextGeneration).
Proof.
  intros s p w post g v Hstep Hg Hv.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hp.
  unfold flag_unlink_node, flag_unlink_neighbor_nodes in Hstep; rewrite Hp, Hg, Hv in Hstep; inversion Hstep; repeat split; reflexivity.
Qed.

Lemma flag_unlink_surviving_node_origin : forall s p w post q after,
  flag_unlink_node s p = Some (w, post) -> post.(flagWaitNodes) q = Some after ->
  q <> p /\ exists before, s.(flagWaitNodes) q = Some before /\
    flag_waiter_link_identity after = flag_waiter_link_identity before.
Proof.
  intros s p w post q after Hstep Hafter.
  assert (Hne : q <> p).
  { intro Heq; subst q; pose proof (proj2 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)); congruence. }
  split; [exact Hne|].
  pose proof (flag_unlink_frames_waiter_identity _ _ _ _ _ Hstep Hne) as Hidentity.
  rewrite Hafter in Hidentity; destruct (flagWaitNodes s q) as [before|] eqn:E; [|discriminate].
  exists before; split; [reflexivity|].
  exact (f_equal (fun o => match o with Some identity => identity | None => flag_waiter_link_identity before end) Hidentity).
Qed.

Lemma flag_unlink_preserves_group_image : forall sg s p w post g,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  s.(flagUsed) w.(flagGroup) = Some g ->
  exists v, post.(flagImages) w.(flagGroup) = Some v /\
    flag_group_image_valid sg.(osKernelConfig) v /\ v.(flagImageType) = 5 /\
    v.(flagImageHead) = hd 0 (remove Z.eq_dec p g.(flagWaitOrder)) /\
    v.(flagImageBits) = g.(flagBits) /\ v.(flagImageName) = g.(flagName).
Proof.
  intros sg s p w post g Hvalid Hstep Hg.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hp.
  pose proof (valid_flag_wait_order_nonzero _ _ _ _ Hvalid Hg) as Hnonzero.
  destruct (valid_flag_state_node_position _ _ _ _ Hvalid Hp) as
    [g0 [pre [rest [Hg0 [Hlist [_ [_ [_ [Hprev [Hnext _]]]]]]]]]].
  rewrite Hg in Hg0; inversion Hg0; subst g0; clear Hg0.
  pose proof Hvalid as [_ [_ [Himages [Hused _]]]].
  destruct (Hused _ g Hg) as [[Hbits Hnd] [_ [_ [v [Hv [Ht [Hhead [Hb Hname]]]]]]]].
  pose proof (Himages _ v Hv) as Hiv.
  destruct (flag_unlink_group_fields _ _ _ _ _ _ Hstep Hg Hv) as [_ [HI _]].
  assert (Hin : In p (flagWaitOrder g)) by (rewrite Hlist; apply in_or_app; right; left; reflexivity).
  pose proof (kernel_list_head_remove _ _ Hnd Hin Hnonzero) as Hheadremove.
  pose proof Hnd as Hndlist; rewrite Hlist in Hndlist.
  assert (Hprev' : flagNodePrev (flagWaitImage w) = kernel_list_previous_addr (flagWaitOrder g) p).
  { rewrite Hlist; transitivity (last pre 0); [exact Hprev|symmetry; exact (kernel_list_previous_addr_at pre p rest Hndlist)]. }
  assert (Hnext' : flagNodeNext (flagWaitImage w) = kernel_list_next_addr (flagWaitOrder g) p).
  { rewrite Hlist; transitivity (hd 0 rest); [exact Hnext|symmetry; exact (kernel_list_next_addr_at pre p rest Hndlist)]. }
  assert (Hheadupdate : hd 0 (remove Z.eq_dec p (flagWaitOrder g)) =
    if Z.eqb (flagNodePrev (flagWaitImage w)) 0 then flagNodeNext (flagWaitImage w) else flagImageHead v).
  { rewrite Hprev', Hnext', Hhead; exact Hheadremove. }
  rewrite HI; destruct (Z.eqb (flagNodePrev (flagWaitImage w)) 0) eqn:E.
  - exists (flag_image_set_head v (flagNodeNext (flagWaitImage w))).
    split; [apply kernel_map_set_same|]. split; [exact Hiv|].
    split; [exact Ht|]. split; [simpl; symmetry; exact Hheadupdate|]. simpl; auto.
  - exists v; split; [exact Hv|]. split; [exact Hiv|]. split; [exact Ht|].
    split; [symmetry; exact Hheadupdate|auto].
Qed.

Lemma flag_unlink_preserves_state_validity : forall sg s p w post,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) -> valid_flag_state sg post.
Proof.
  intros sg s p w post Hv Hstep.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hp.
  destruct (valid_flag_state_node_position _ _ _ _ Hv Hp) as [g [pre [rest [Hg Hposition]]]].
  pose proof Hv as [Hpool [Hdomain [Himages [Hused [Hfree Hnodes]]]]].
  destruct (Hused _ g Hg) as [Hvg [Hgen [Hwait [old [Hold Hprops]]]]].
  destruct (flag_unlink_group_fields _ _ _ _ _ _ Hstep Hg Hold) as [HU [HI [HF HN]]].
  destruct (flag_unlink_preserves_group_image _ _ _ _ _ _ Hv Hstep Hg) as
    [v [Himage [Hiv [Htype [Hhead [Hbits Hname]]]]]].
  assert (Himage_other : forall j, j <> flagGroup w -> flagImages post j = flagImages s j).
  { intros j Hne; rewrite HI; destruct (Z.eqb (flagNodePrev (flagWaitImage w)) 0);
      [apply kernel_map_set_other; exact Hne|reflexivity]. }
  destruct Hpool as [Hnd [Hrange Hslots]].
  destruct (proj1 (Hslots (flagGroup w)) (ex_intro _ g Hg)) as [Hid Hnot].
  unfold valid_flag_state; split.
  - rewrite HF, HU; eapply kernel_pool_replace_preserves_partition; [split; [exact Hnd|]; split; assumption|exact Hg].
  - split.
    + intros j; destruct (Z.eq_dec j (flagGroup w)) as [->|Hne].
      * split; [intros; exact Hid|intros; eauto].
      * rewrite Himage_other by exact Hne; apply Hdomain.
    + split.
      * intros j image Him; destruct (Z.eq_dec j (flagGroup w)) as [->|Hne].
        -- rewrite Himage in Him; inversion Him; subst image; exact Hiv.
        -- rewrite Himage_other in Him by exact Hne; eapply Himages; eauto.
      * split.
        -- intros j group Hj; rewrite HU in Hj; unfold kernel_map_set in Hj.
           destruct (Z.eq_dec j (flagGroup w)) as [->|Hne].
           ++ inversion Hj; subst group; split; [apply flag_unlink_preserves_group_order_validity; exact Hvg|].
              split; [rewrite HN; exact Hgen|]. split.
              ** eapply flag_unlink_preserves_own_wait_list; eauto.
              ** exists v; split; [exact Himage|]. simpl; auto.
           ++ destruct (Hused j group Hj) as [Hvalid [Hgeneration [Hwaiting [image [Him Hfields]]]]].
              split; [exact Hvalid|]. split; [rewrite HN; exact Hgeneration|]. split.
              ** eapply flag_unlink_preserves_other_wait_list; eauto.
              ** exists image; split; [rewrite Himage_other by exact Hne; exact Him|exact Hfields].
        -- split.
           ++ intros prefix j suffix Hlist; rewrite HF in Hlist.
              assert (Hne : j <> flagGroup w).
              { intro Heq; subst j; apply Hnot; rewrite Hlist; apply in_or_app; right; left; reflexivity. }
              destruct (Hfree prefix j suffix Hlist) as [image [Him Hfields]].
              exists image; split; [rewrite Himage_other by exact Hne; exact Him|exact Hfields].
           ++ intros q after Hafter.
              destruct (flag_unlink_surviving_node_origin _ _ _ _ _ _ Hstep Hafter) as
                [Hqp [before [Hbefore Hidentity]]].
              destruct (Hnodes q before Hbefore) as [Hq0 [Hnodevalid [group [Hgr Hin]]]].
              assert (Hgroup : flagGroup after = flagGroup before)
                by (unfold flag_waiter_link_identity in Hidentity; congruence).
              assert (Hnodeafter : flag_node_image_valid (osKernelConfig sg) (flagWaitImage after)).
              { unfold flag_node_image_valid in Hnodevalid |- *.
                destruct Hnodevalid as [Hmask Hpad].
                unfold flag_waiter_link_identity in Hidentity; inversion Hidentity; split; congruence. }
              split; [exact Hq0|]. split; [exact Hnodeafter|]. rewrite Hgroup, HU.
              destruct (Z.eq_dec (flagGroup before) (flagGroup w)) as [Heq|Hne].
              ** rewrite Heq, kernel_map_set_same.
                 rewrite Heq in Hgr; rewrite Hg in Hgr; inversion Hgr; subst group.
                 eexists; split; [reflexivity|]. simpl; apply in_in_remove; assumption.
              ** rewrite kernel_map_set_other by exact Hne; exists group; auto.
Qed.

Lemma flag_fresh_node_absent_from_wait_order : forall sg s i g p,
  valid_flag_state sg s -> s.(flagUsed) i = Some g -> s.(flagWaitNodes) p = None ->
  ~ In p g.(flagWaitOrder).
Proof.
  intros sg s i g p [_ [_ [_ [Hused _]]]] Hg Hp Hin.
  destruct (Hused i g Hg) as [_ [_ [Hwait _]]].
  apply in_split in Hin; destruct Hin as [pre [rest Hlist]].
  destruct (Hwait pre p rest Hlist) as [w [Hw _]]; congruence.
Qed.

Lemma flag_block_installs_node : forall sg s w tcb post g v,
  valid_flag_state sg s -> s.(flagUsed) w.(flagGroup) = Some g ->
  s.(flagImages) w.(flagGroup) = Some v -> s.(flagWaitNodes) w.(flagNodeAddr) = None ->
  flag_block_node sg s w tcb = Some post ->
  post.(flagWaitNodes) w.(flagNodeAddr) =
    Some (flag_waiter_set_image w (flag_block_node_image sg w tcb v.(flagImageHead))).
Proof.
  intros sg s w tcb post g v Hvalid Hg Hv Hfresh Hstep.
  pose proof (flag_fresh_node_absent_from_wait_order _ _ _ _ _ Hvalid Hg Hfresh) as Hnot.
  pose proof Hvalid as [_ [_ [_ [Hused _]]]].
  destruct (Hused _ g Hg) as [_ [_ [_ [v0 [Hv0 [_ [Hhead _]]]]]]].
  rewrite Hv in Hv0; inversion Hv0; subst v0.
  unfold flag_block_node in Hstep; rewrite Hg, Hv in Hstep; inversion Hstep; subst post; simpl.
  destruct (Z.eqb (flagImageHead v) 0) eqn:E; [apply kernel_map_set_same|].
  unfold flag_nodes_set_prev; rewrite kernel_map_set_other; [apply kernel_map_set_same|].
  intro Heq; apply Hnot; rewrite Hhead in Heq.
  destruct (flagWaitOrder g) as [|a rest] eqn:Hl; simpl in Heq.
  - apply Z.eqb_neq in E; rewrite Hhead in E; simpl in E; contradiction.
  - left; symmetry; exact Heq.
Qed.

Lemma flag_block_updates_old_node : forall sg s w tcb post q before v,
  flag_block_node sg s w tcb = Some post -> s.(flagImages) w.(flagGroup) = Some v ->
  q <> w.(flagNodeAddr) -> q <> 0 -> s.(flagWaitNodes) q = Some before ->
  post.(flagWaitNodes) q = Some (if Z.eq_dec q v.(flagImageHead) then
    flag_waiter_set_image before (flag_node_set_links before.(flagWaitImage)
      before.(flagWaitImage).(flagNodeNext) w.(flagNodeAddr)) else before).
Proof.
  intros sg s w tcb post q before v Hstep Hv Hqp Hq0 Hbefore.
  unfold flag_block_node in Hstep; rewrite Hv in Hstep.
  destruct (flagUsed s (flagGroup w)); [|discriminate].
  inversion Hstep; subst post; simpl.
  destruct (Z.eqb (flagImageHead v) 0) eqn:E.
  - rewrite kernel_map_set_other by exact Hqp; rewrite Hbefore.
    destruct (Z.eq_dec q (flagImageHead v)); [apply Z.eqb_eq in E; exfalso; apply Hq0; congruence|reflexivity].
  - rewrite flag_nodes_set_prev_lookup, kernel_map_set_other by exact Hqp.
    rewrite Hbefore; reflexivity.
Qed.

Lemma flag_block_preserves_own_wait_list : forall sg s w tcb post g v,
  valid_flag_state sg s -> s.(flagUsed) w.(flagGroup) = Some g ->
  s.(flagImages) w.(flagGroup) = Some v -> s.(flagWaitNodes) w.(flagNodeAddr) = None ->
  w.(flagGroupGeneration) = g.(flagGeneration) ->
  flag_block_node sg s w tcb = Some post ->
  flag_wait_list_valid sg post w.(flagGroup)
    (flag_group_set_wait_order g (w.(flagNodeAddr) :: g.(flagWaitOrder))).
Proof.
  intros sg s w tcb post g v Hvalid Hg Hv Hfresh Hgeneration Hstep.
  pose proof Hvalid as [_ [_ [_ [Hused _]]]].
  destruct (Hused _ g Hg) as [[Hbits Hnd] [_ [Hwait [v0 [Hv0 [_ [Hhead _]]]]]]].
  rewrite Hv in Hv0; inversion Hv0; subst v0.
  pose proof (flag_fresh_node_absent_from_wait_order _ _ _ _ _ Hvalid Hg Hfresh) as Hnot.
  intros pre q rest Hlist; simpl in Hlist; destruct pre as [|a pre].
  - simpl in Hlist; inversion Hlist; subst q rest.
    exists (flag_waiter_set_image w (flag_block_node_image sg w tcb (flagImageHead v))).
    split; [eapply flag_block_installs_node; eauto|].
    simpl; repeat split; assumption.
  - simpl in Hlist; inversion Hlist as [[Ha Htail]]; subst a.
    destruct (Hwait pre q rest Htail) as [before [Hbefore Hfields]].
    assert (Hq0 : q <> 0) by (eapply valid_flag_state_node_nonzero; eauto).
    assert (Hqp : q <> flagNodeAddr w).
    { intro E; subst q; rewrite Hfresh in Hbefore; discriminate. }
    pose proof (flag_block_updates_old_node _ _ _ _ _ _ _ _ Hstep Hv Hqp Hq0 Hbefore) as Hafter.
    destruct pre as [|a pre].
    + simpl in Htail; rewrite Htail in Hhead; simpl in Hhead.
      destruct (Z.eq_dec q (flagImageHead v)) as [Heq|Hne]; [|congruence].
      eexists; split; [exact Hafter|].
      simpl; destruct Hfields as [Haddr [Hgroup [Hgen [Hgrp [Hprev [Hnext [Hmask Hmode]]]]]]].
      repeat split; assumption.
    + assert (Hqhead : q <> flagImageHead v).
      { rewrite Hhead, Htail; simpl; intro E; subst q.
        rewrite Htail in Hnd; inversion Hnd as [|? ? Hnothead Hndtail]; subst.
        apply Hnothead; apply in_or_app; right; left; reflexivity. }
      destruct (Z.eq_dec q (flagImageHead v)) as [Heq|Hne]; [contradiction|].
      exists before; split; [exact Hafter|].
      simpl in Hfields |- *; exact Hfields.
Qed.

Lemma flag_block_frames_waiter_identity : forall sg s w tcb post q,
  flag_block_node sg s w tcb = Some post -> q <> w.(flagNodeAddr) ->
  option_map flag_waiter_link_identity (post.(flagWaitNodes) q) =
    option_map flag_waiter_link_identity (s.(flagWaitNodes) q).
Proof.
  intros sg s w tcb post q Hstep Hne; unfold flag_block_node in Hstep.
  destruct (flagUsed s (flagGroup w)), (flagImages s (flagGroup w)); try discriminate.
  inversion Hstep; subst post; simpl.
  destruct (Z.eqb (flagImageHead f0) 0);
    rewrite ?flag_nodes_set_prev_identity_frame, kernel_map_set_other by exact Hne; reflexivity.
Qed.

Lemma flag_block_frames_other_group_nodes : forall sg s w tcb post q before,
  valid_flag_state sg s -> s.(flagWaitNodes) w.(flagNodeAddr) = None ->
  flag_block_node sg s w tcb = Some post -> s.(flagWaitNodes) q = Some before ->
  before.(flagGroup) <> w.(flagGroup) -> post.(flagWaitNodes) q = Some before.
Proof.
  intros sg s w tcb post q before Hvalid Hfresh Hstep Hbefore Hgroup.
  assert (Hqp : q <> flagNodeAddr w) by (intro E; subst q; congruence).
  assert (Hq0 : q <> 0) by (eapply valid_flag_state_node_nonzero; eauto).
  pose proof Hstep as Hstep'; unfold flag_block_node in Hstep'.
  destruct (flagUsed s (flagGroup w)) as [g|] eqn:Hg; [|discriminate].
  destruct (flagImages s (flagGroup w)) as [v|] eqn:Hv; [|discriminate].
  pose proof (flag_block_updates_old_node _ _ _ _ _ _ _ _ Hstep Hv Hqp Hq0 Hbefore) as Hafter.
  destruct (Z.eq_dec q (flagImageHead v)) as [Heq|Hne]; [|exact Hafter].
  exfalso; apply Hgroup.
  destruct Hvalid as [_ [_ [_ [Hused _]]]].
  destruct (Hused _ g Hg) as [_ [_ [Hwait [v0 [Hv0 [_ [Hhead _]]]]]]].
  rewrite Hv in Hv0; inversion Hv0; subst v0.
  eapply flag_wait_list_member_group; [exact Hwait| |exact Hbefore].
  rewrite Hhead in Heq; destruct (flagWaitOrder g); simpl in Heq; [contradiction|left; symmetry; exact Heq].
Qed.

Lemma flag_block_preserves_other_wait_list : forall sg s w tcb post i g,
  valid_flag_state sg s -> s.(flagWaitNodes) w.(flagNodeAddr) = None ->
  flag_block_node sg s w tcb = Some post -> s.(flagUsed) i = Some g ->
  i <> w.(flagGroup) -> flag_wait_list_valid sg post i g.
Proof.
  intros sg s w tcb post i g Hvalid Hfresh Hstep Hg Hne.
  pose proof Hvalid as [_ [_ [_ [Hused _]]]].
  destruct (Hused i g Hg) as [_ [_ [Hwait _]]].
  intros pre q rest Hlist; destruct (Hwait pre q rest Hlist) as [before [Hbefore Hfields]].
  exists before; split; [|exact Hfields].
  eapply flag_block_frames_other_group_nodes; eauto; intuition congruence.
Qed.

Lemma flag_block_group_fields : forall sg s w tcb post g v,
  flag_block_node sg s w tcb = Some post -> s.(flagUsed) w.(flagGroup) = Some g ->
  s.(flagImages) w.(flagGroup) = Some v ->
  post.(flagUsed) = kernel_map_set s.(flagUsed) w.(flagGroup)
    (Some (flag_group_set_wait_order g (w.(flagNodeAddr) :: g.(flagWaitOrder)))) /\
  post.(flagImages) = kernel_map_set s.(flagImages) w.(flagGroup)
    (Some (flag_image_set_head v w.(flagNodeAddr))) /\
  post.(flagFree) = s.(flagFree) /\ post.(flagNextGeneration) = s.(flagNextGeneration).
Proof.
  intros sg s w tcb post g v Hstep Hg Hv; unfold flag_block_node in Hstep.
  rewrite Hg, Hv in Hstep; inversion Hstep; repeat split; reflexivity.
Qed.

Lemma flag_block_preserves_state_validity : forall sg s w tcb post g,
  valid_flag_state sg s -> s.(flagUsed) w.(flagGroup) = Some g ->
  w.(flagGroupGeneration) = g.(flagGeneration) -> w.(flagNodeAddr) <> 0 ->
  s.(flagWaitNodes) w.(flagNodeAddr) = None ->
  flag_word_in_range sg.(osKernelConfig) w.(flagMask) ->
  Z.of_nat (List.length w.(flagWaitImage).(flagNodePadding)) =
    flag_node_size sg.(osKernelConfig) - flag_node_mode_offset sg.(osKernelConfig) - 1 ->
  flag_block_node sg s w tcb = Some post -> valid_flag_state sg post.
Proof.
  intros sg s w tcb post g Hvalid Hg Hgeneration Hp0 Hfresh Hmask Hpadding Hstep.
  pose proof Hvalid as [Hpool [Hdomain [Himages [Hused [Hfree Hnodes]]]]].
  destruct (Hused _ g Hg) as [Hvg [Hgen [Hwait [v [Hv [Htype [Hhead [Hbits Hname]]]]]]]].
  pose proof (flag_fresh_node_absent_from_wait_order _ _ _ _ _ Hvalid Hg Hfresh) as Hnotorder.
  pose proof (flag_block_installs_node _ _ _ _ _ _ _ Hvalid Hg Hv Hfresh Hstep) as Hnew.
  destruct (flag_block_group_fields _ _ _ _ _ _ _ Hstep Hg Hv) as [HU [HI [HF HN]]].
  pose proof Hpool as [_ [_ Hslots]].
  destruct (proj1 (Hslots (flagGroup w)) (ex_intro _ g Hg)) as [Hid Hnotfree].
  unfold valid_flag_state; split.
  - rewrite HU, HF; eapply kernel_pool_replace_preserves_partition; eauto.
  - split.
    + intros i; rewrite HI; destruct (Z.eq_dec i (flagGroup w)) as [->|Hne].
      * rewrite kernel_map_set_same; split; [intros; exact Hid|eauto].
      * rewrite kernel_map_set_other by exact Hne; apply Hdomain.
    + split.
      * intros i image Him; rewrite HI in Him; unfold kernel_map_set in Him.
        destruct (Z.eq_dec i (flagGroup w)) as [->|Hne].
        -- inversion Him; subst image; exact (Himages _ v Hv).
        -- eapply Himages; eauto.
      * split.
        -- intros i group Hgr; rewrite HU in Hgr; unfold kernel_map_set in Hgr.
           destruct (Z.eq_dec i (flagGroup w)) as [->|Hne].
           ++ inversion Hgr; subst group; split.
              ** apply flag_block_preserves_group_order_validity; assumption.
              ** split; [rewrite HN; exact Hgen|]. split.
                 --- eapply flag_block_preserves_own_wait_list; eauto.
                 --- exists (flag_image_set_head v (flagNodeAddr w)); split; [rewrite HI; apply kernel_map_set_same|].
                     simpl; repeat split; assumption.
           ++ destruct (Hused i group Hgr) as [Hgroupvalid [Hothergen [Hwaiting [image [Him Hfields]]]]].
              split; [exact Hgroupvalid|]. split; [rewrite HN; exact Hothergen|]. split.
              ** eapply flag_block_preserves_other_wait_list; eauto.
              ** exists image; split; [rewrite HI, kernel_map_set_other by exact Hne; exact Him|exact Hfields].
        -- split.
           ++ intros pre i rest Hlist; rewrite HF in Hlist.
              assert (Hne : i <> flagGroup w).
              { intro E; subst i; apply Hnotfree; rewrite Hlist; apply in_or_app; right; left; reflexivity. }
              destruct (Hfree pre i rest Hlist) as [image [Him Hfields]].
              exists image; split; [rewrite HI, kernel_map_set_other by exact Hne; exact Him|exact Hfields].
           ++ intros q after Hafter; destruct (Z.eq_dec q (flagNodeAddr w)) as [->|Hqp].
              ** rewrite Hnew in Hafter; inversion Hafter; subst after.
                 split; [exact Hp0|]. split; [split; assumption|].
                 exists (flag_group_set_wait_order g (flagNodeAddr w :: flagWaitOrder g)); split.
                 --- simpl; rewrite HU; apply kernel_map_set_same.
                 --- left; reflexivity.
              ** pose proof (flag_block_frames_waiter_identity _ _ _ _ _ _ Hstep Hqp) as Hidentity.
                 rewrite Hafter in Hidentity; destruct (flagWaitNodes s q) as [before|] eqn:Hbefore; [|discriminate].
                 apply (f_equal (fun o => match o with Some identity => identity | None => flag_waiter_link_identity before end)) in Hidentity.
                 change (flag_waiter_link_identity after = flag_waiter_link_identity before) in Hidentity.
                 destruct (Hnodes q before Hbefore) as [Hq0 [Hiv [group [Hgr Hin]]]].
                 assert (Hgroup : flagGroup after = flagGroup before)
                   by (unfold flag_waiter_link_identity in Hidentity; congruence).
                 split; [exact Hq0|]. split.
                 --- unfold flag_node_image_valid in Hiv |- *; destruct Hiv as [Hm Hp].
                     unfold flag_waiter_link_identity in Hidentity; inversion Hidentity; split; congruence.
                 --- rewrite Hgroup, HU; destruct (Z.eq_dec (flagGroup before) (flagGroup w)) as [Heq|Hne].
                     +++ rewrite Heq, kernel_map_set_same; rewrite Heq, Hg in Hgr; inversion Hgr; subst group.
                         eexists; split; [reflexivity|right; exact Hin].
                     +++ rewrite kernel_map_set_other by exact Hne; exists group; auto.
Qed.

Definition flag_node_rep_without_next (c : KernelConfiguration) (p : addr) (v : FlagNodeImage) : Assertion :=
  (p + 4) # Ptr |-> v.(flagNodePrev) **
  (p + 8) # Ptr |-> v.(flagNodeTCB) ** (p + 12) # Ptr |-> v.(flagNodeGroup) **
  flag_word_rep c (p + 16) v.(flagNodeMask) **
  (p + flag_node_mode_offset c) # UChar |-> v.(flagNodeMode) **
  store_optional_bytes (p + flag_node_mode_offset c + 1) v.(flagNodePadding).

Definition flag_node_rep_without_prev (c : KernelConfiguration) (p : addr) (v : FlagNodeImage) : Assertion :=
  p # Ptr |-> v.(flagNodeNext) **
  (p + 8) # Ptr |-> v.(flagNodeTCB) ** (p + 12) # Ptr |-> v.(flagNodeGroup) **
  flag_word_rep c (p + 16) v.(flagNodeMask) **
  (p + flag_node_mode_offset c) # UChar |-> v.(flagNodeMode) **
  store_optional_bytes (p + flag_node_mode_offset c + 1) v.(flagNodePadding).

Lemma flag_node_rep_split_next : forall c p v,
  flag_node_rep c p v |-- p # Ptr |-> v.(flagNodeNext) ** flag_node_rep_without_next c p v.
Proof. intros; unfold flag_node_rep, flag_node_rep_without_next; entailer!. Qed.

Lemma flag_node_rep_merge_updated_next : forall c p v next,
  p # Ptr |-> next ** flag_node_rep_without_next c p v |--
    flag_node_rep c p (flag_node_set_links v next v.(flagNodePrev)).
Proof. intros; unfold flag_node_rep, flag_node_rep_without_next, flag_node_set_links; simpl; entailer!. Qed.

Lemma flag_node_rep_split_prev : forall c p v,
  flag_node_rep c p v |-- (p + 4) # Ptr |-> v.(flagNodePrev) ** flag_node_rep_without_prev c p v.
Proof. intros; unfold flag_node_rep, flag_node_rep_without_prev; entailer!. Qed.

Lemma flag_node_rep_merge_updated_prev : forall c p v prev,
  (p + 4) # Ptr |-> prev ** flag_node_rep_without_prev c p v |--
    flag_node_rep c p (flag_node_set_links v v.(flagNodeNext) prev).
Proof. intros; unfold flag_node_rep, flag_node_rep_without_prev, flag_node_set_links; simpl; entailer!. Qed.

Definition flag_group_rep_without_head (c : KernelConfiguration) (p : addr) (v : FlagGroupImage) : Assertion :=
  p # UChar |-> v.(flagImageType) **
  store_optional_bytes (p + 1) (firstn 3 v.(flagImagePadding)) **
  flag_word_rep c (p + 8) v.(flagImageBits) **
  store_optional_bytes (p + 8 + flag_word_bytes c) (skipn 3 v.(flagImagePadding)) **
  (if c.(cfgFlagNames) then (p + flag_group_name_offset c) # Ptr |-> v.(flagImageName) else emp).

Lemma flag_group_rep_split_head : forall c p v,
  flag_group_rep c p v |-- (p + 4) # Ptr |-> v.(flagImageHead) ** flag_group_rep_without_head c p v.
Proof. intros; unfold flag_group_rep, flag_group_rep_without_head; entailer!. Qed.

Lemma flag_group_rep_merge_updated_head : forall c p v head,
  (p + 4) # Ptr |-> head ** flag_group_rep_without_head c p v |--
    flag_group_rep c p (flag_image_set_head v head).
Proof. intros; unfold flag_group_rep, flag_group_rep_without_head, flag_image_set_head; simpl; entailer!. Qed.

Lemma flag_wait_nodes_rep_split_node : forall sg nodes p w,
  nodes p = Some w -> flag_wait_nodes_rep sg nodes |--
    flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage) ** flag_wait_nodes_without_node sg nodes p.
Proof.
  intros sg nodes p w H; unfold flag_wait_nodes_rep, flag_wait_nodes_without_node.
  sep_apply_l_atomic (store_map_split
    (fun p w => flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)) p w nodes H); entailer!.
Qed.

Lemma flag_wait_nodes_rep_merge_updated_node : forall sg nodes p w,
  flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage) ** flag_wait_nodes_without_node sg nodes p |--
    flag_wait_nodes_rep sg (kernel_map_set nodes p (Some w)).
Proof.
  intros sg nodes p w; unfold flag_wait_nodes_rep, flag_wait_nodes_without_node.
  assert (Hframe : forall q, q <> p -> nodes q = kernel_map_set nodes p (Some w) q)
    by (intros; symmetry; apply kernel_map_set_other; assumption).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun p w => flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)) _ _ p Hframe)).
  sep_apply_l_atomic (store_map_merge
    (fun p w => flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)) p w _
      (kernel_map_set_same _ nodes p (Some w))); entailer!.
Qed.

Lemma flag_wait_nodes_rep_split_next : forall sg nodes p w,
  nodes p = Some w -> flag_wait_nodes_rep sg nodes |--
    p # Ptr |-> w.(flagWaitImage).(flagNodeNext) **
    flag_node_rep_without_next sg.(osKernelConfig) p w.(flagWaitImage) ** flag_wait_nodes_without_node sg nodes p.
Proof.
  intros; sep_apply_l_atomic (flag_wait_nodes_rep_split_node sg nodes p w H).
  sep_apply_l_atomic (flag_node_rep_split_next sg.(osKernelConfig) p w.(flagWaitImage)); entailer!.
Qed.

Lemma flag_wait_nodes_rep_merge_updated_next : forall sg nodes p w next,
  nodes p = Some w ->
  p # Ptr |-> next ** flag_node_rep_without_next sg.(osKernelConfig) p w.(flagWaitImage) **
    flag_wait_nodes_without_node sg nodes p |-- flag_wait_nodes_rep sg (flag_nodes_set_next nodes p next).
Proof.
  intros sg nodes p w next H.
  sep_apply_l_atomic (flag_node_rep_merge_updated_next sg.(osKernelConfig) p w.(flagWaitImage) next).
  unfold flag_nodes_set_next; rewrite H.
  pose proof (flag_wait_nodes_rep_merge_updated_node sg nodes p
    (flag_waiter_set_image w (flag_node_set_links w.(flagWaitImage) next w.(flagWaitImage).(flagNodePrev)))) as Hmerge.
  cbv beta iota delta [flag_waiter_set_image flagWaitImage] in Hmerge.
  fold (flagWaitImage w) in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma flag_wait_nodes_rep_split_prev : forall sg nodes p w,
  nodes p = Some w -> flag_wait_nodes_rep sg nodes |--
    (p + 4) # Ptr |-> w.(flagWaitImage).(flagNodePrev) **
    flag_node_rep_without_prev sg.(osKernelConfig) p w.(flagWaitImage) ** flag_wait_nodes_without_node sg nodes p.
Proof.
  intros; sep_apply_l_atomic (flag_wait_nodes_rep_split_node sg nodes p w H).
  sep_apply_l_atomic (flag_node_rep_split_prev sg.(osKernelConfig) p w.(flagWaitImage)); entailer!.
Qed.

Lemma flag_wait_nodes_rep_merge_updated_prev : forall sg nodes p w prev,
  nodes p = Some w ->
  (p + 4) # Ptr |-> prev ** flag_node_rep_without_prev sg.(osKernelConfig) p w.(flagWaitImage) **
    flag_wait_nodes_without_node sg nodes p |-- flag_wait_nodes_rep sg (flag_nodes_set_prev nodes p prev).
Proof.
  intros sg nodes p w prev H.
  sep_apply_l_atomic (flag_node_rep_merge_updated_prev sg.(osKernelConfig) p w.(flagWaitImage) prev).
  unfold flag_nodes_set_prev; rewrite H.
  pose proof (flag_wait_nodes_rep_merge_updated_node sg nodes p
    (flag_waiter_set_image w (flag_node_set_links w.(flagWaitImage) w.(flagWaitImage).(flagNodeNext) prev))) as Hmerge.
  cbv beta iota delta [flag_waiter_set_image flagWaitImage] in Hmerge.
  fold (flagWaitImage w) in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma flag_groups_rep_split_head : forall sg s i v,
  s.(flagImages) i = Some v -> flag_groups_rep sg s |--
    (flag_pool_addr sg i + 4) # Ptr |-> v.(flagImageHead) **
    flag_group_rep_without_head sg.(osKernelConfig) (flag_pool_addr sg i) v ** flag_groups_without sg s i.
Proof.
  intros; sep_apply_l_atomic (flag_groups_split_group sg s i v H).
  sep_apply_l_atomic (flag_group_rep_split_head sg.(osKernelConfig) (flag_pool_addr sg i) v); entailer!.
Qed.

Lemma flag_groups_rep_merge_updated_head : forall sg s post i v head,
  post.(flagImages) = kernel_map_set s.(flagImages) i (Some (flag_image_set_head v head)) ->
  (flag_pool_addr sg i + 4) # Ptr |-> head **
    flag_group_rep_without_head sg.(osKernelConfig) (flag_pool_addr sg i) v ** flag_groups_without sg s i |--
    flag_groups_rep sg post.
Proof.
  intros sg s post i v head Himages.
  sep_apply_l_atomic (flag_group_rep_merge_updated_head sg.(osKernelConfig) (flag_pool_addr sg i) v head).
  sep_apply_l_atomic (flag_groups_merge_updated_group sg s post i (flag_image_set_head v head)
    ltac:(rewrite Himages; apply kernel_map_set_same)
    ltac:(intros; rewrite Himages; symmetry; apply kernel_map_set_other; assumption)); entailer!.
Qed.

Lemma flag_linked_node_differs_from_neighbors : forall sg s p w,
  valid_flag_state sg s -> s.(flagWaitNodes) p = Some w ->
  p <> w.(flagWaitImage).(flagNodeNext) /\ p <> w.(flagWaitImage).(flagNodePrev).
Proof.
  intros sg s p w Hvalid Hw.
  pose proof (valid_flag_state_node_nonzero _ _ _ _ Hvalid Hw) as Hp0.
  destruct (valid_flag_state_node_position _ _ _ _ Hvalid Hw) as
    [g [pre [rest [Hg [Hlist [_ [_ [_ [Hprev [Hnext _]]]]]]]]]].
  pose proof Hvalid as [_ [_ [_ [Hused _]]]].
  destruct (Hused _ g Hg) as [[Hbits Hnd] _].
  pose proof Hnd as Hndlist; rewrite Hlist in Hndlist.
  assert (Hnextptr : kernel_list_next_addr (flagWaitOrder g) p = flagNodeNext (flagWaitImage w)).
  { rewrite Hlist, kernel_list_next_addr_at by exact Hndlist; symmetry; exact Hnext. }
  assert (Hprevptr : kernel_list_previous_addr (flagWaitOrder g) p = flagNodePrev (flagWaitImage w)).
  { rewrite Hlist, kernel_list_previous_addr_at by exact Hndlist; symmetry; exact Hprev. }
  split; intro E.
  - assert (Hself : kernel_list_next_addr (flagWaitOrder g) p = p) by congruence.
    apply (proj1 (kernel_list_next_addr_eq _ _ _ Hp0)) in Hself.
    exact (kernel_list_next_not_self _ _ Hnd Hself).
  - assert (Hself : kernel_list_previous_addr (flagWaitOrder g) p = p) by congruence.
    apply (proj1 (kernel_list_previous_addr_eq _ _ _ Hp0)) in Hself.
    exact (kernel_list_previous_not_self _ _ Hnd Hself).
Qed.

(** After OS_FlagUnlink's two conditional neighbor stores, the removed
    stack node is still owned and its own bytes have not been modified. *)

Definition flag_unlink_neighbors_rep (sg : StableGlobVars) (s : GlobFlagState) (w : FlagWaiterState) : Assertion :=
  flag_wait_nodes_rep sg (flag_unlink_neighbor_nodes s.(flagWaitNodes) w).

Lemma flag_unlink_neighbor_nodes_keep_removed_node : forall sg s p w,
  valid_flag_state sg s -> s.(flagWaitNodes) p = Some w ->
  flag_unlink_neighbor_nodes s.(flagWaitNodes) w p = Some w.
Proof.
  intros sg s p w Hvalid Hw; destruct (flag_linked_node_differs_from_neighbors _ _ _ _ Hvalid Hw) as [Hnext Hprev].
  unfold flag_unlink_neighbor_nodes.
  destruct (Z.eqb (flagNodeNext (flagWaitImage w)) 0), (Z.eqb (flagNodePrev (flagWaitImage w)) 0);
    unfold flag_nodes_set_next, flag_nodes_set_prev;
    rewrite ?kernel_map_set_other by assumption; exact Hw.
Qed.

Lemma flag_wait_nodes_rep_remove_transfers_node : forall sg nodes p w,
  nodes p = Some w -> flag_wait_nodes_rep sg nodes |--
    flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage) ** flag_wait_nodes_rep sg (kernel_map_set nodes p None).
Proof.
  intros sg nodes p w H; unfold flag_wait_nodes_rep.
  sep_apply_l_atomic (store_map_split
    (fun p w => flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)) p w _ H).
  assert (Hframe : forall q, q <> p -> nodes q = kernel_map_set nodes p None q)
    by (intros; symmetry; apply kernel_map_set_other; assumption).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun p w => flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)) _ _ p Hframe)).
  sep_apply_l_atomic (store_map_missing_equiv_store_map
    (fun p w => flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)) _ p (kernel_map_set_same _ nodes p None)); entailer!.
Qed.

Lemma flag_unlink_node_map_eq : forall s p w post,
  flag_unlink_node s p = Some (w, post) ->
  post.(flagWaitNodes) = kernel_map_set (flag_unlink_neighbor_nodes s.(flagWaitNodes) w) p None /\
  post.(flagFree) = s.(flagFree).
Proof.
  intros s p w post Hstep; unfold flag_unlink_node, flag_unlink_neighbor_nodes in Hstep.
  destruct (flagWaitNodes s p) as [before|]; [|discriminate].
  destruct (flagUsed s (flagGroup before)), (flagImages s (flagGroup before)); try discriminate.
  inversion Hstep; subst w post; split; reflexivity.
Qed.

(** The field-level merge lemmas above consume the new pointer cells
    produced by the C stores.  This final cutpoint reassembles their map
    and transfers the unchanged stack-node image back to the caller. *)

Lemma flag_unlink_reconstructs_raw_rep : forall sg s p w post,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  flag_groups_rep sg post ** flag_unlink_neighbors_rep sg s w **
    sg.(g_OSFlagFreeList) # Ptr |->
      (match s.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end) |--
    flag_node_return_loan sg.(osKernelConfig) w ** flag_raw_rep sg post.
Proof.
  intros sg s p w post Hvalid Hstep.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  destruct (valid_flag_state_node_position _ _ _ _ Hvalid Hw) as [g [pre [rest [_ [_ [Haddr _]]]]]].
  pose proof (flag_unlink_neighbor_nodes_keep_removed_node _ _ _ _ Hvalid Hw) as Hlookup.
  destruct (flag_unlink_node_map_eq _ _ _ _ Hstep) as [Hnodes Hfree].
  unfold flag_unlink_neighbors_rep, flag_node_return_loan, flag_raw_rep, flag_nodes_rep.
  rewrite Hnodes, Hfree, Haddr.
  sep_apply_l_atomic (flag_wait_nodes_rep_remove_transfers_node sg (flag_unlink_neighbor_nodes (flagWaitNodes s) w) p w Hlookup).
  unfold flag_wait_nodes_rep; entailer!.
Qed.

Lemma flag_linked_node_next_lookup : forall sg s p w,
  valid_flag_state sg s -> s.(flagWaitNodes) p = Some w ->
  w.(flagWaitImage).(flagNodeNext) <> 0 ->
  exists nextw, s.(flagWaitNodes) w.(flagWaitImage).(flagNodeNext) = Some nextw /\
    nextw.(flagWaitImage).(flagNodePrev) = p.
Proof.
  intros sg s p w Hvalid Hw Hnext0.
  destruct (valid_flag_state_node_position _ _ _ _ Hvalid Hw) as
    [g [pre [rest [Hg [Hlist [_ [_ [_ [Hprev [Hnext _]]]]]]]]]].
  destruct rest as [|q rest]; [simpl in Hnext; contradiction|].
  simpl in Hnext.
  destruct Hvalid as [_ [_ [_ [Hused _]]]].
  destruct (Hused _ g Hg) as [_ [_ [Hwait _]]].
  assert (Hposition : flagWaitOrder g = (pre ++ [p]) ++ q :: rest).
  { rewrite <- app_assoc; exact Hlist. }
  destruct (Hwait _ _ _ Hposition) as
    [nextw [Hlookup [_ [_ [_ [_ [Hback _]]]]]]].
  exists nextw; rewrite Hnext; split; [exact Hlookup|].
  rewrite last_last in Hback; exact Hback.
Qed.

Lemma flag_linked_node_prev_lookup : forall sg s p w,
  valid_flag_state sg s -> s.(flagWaitNodes) p = Some w ->
  w.(flagWaitImage).(flagNodePrev) <> 0 ->
  exists prevw, s.(flagWaitNodes) w.(flagWaitImage).(flagNodePrev) = Some prevw /\
    prevw.(flagWaitImage).(flagNodeNext) = p.
Proof.
  intros sg s p w Hvalid Hw Hprev0.
  destruct (valid_flag_state_node_position _ _ _ _ Hvalid Hw) as
    [g [pre [rest [Hg [Hlist [_ [_ [_ [Hprev [Hnext _]]]]]]]]]].
  assert (Hnonempty : pre <> []) by (intros E; rewrite E in Hprev; simpl in Hprev; contradiction).
  destruct (exists_last Hnonempty) as [prefix [q Hpre]].
  rewrite Hpre, last_last in Hprev.
  destruct Hvalid as [_ [_ [_ [Hused _]]]].
  destruct (Hused _ g Hg) as [_ [_ [Hwait _]]].
  assert (Hposition : flagWaitOrder g = prefix ++ q :: p :: rest).
  { rewrite Hlist, Hpre, <- app_assoc; reflexivity. }
  destruct (Hwait _ _ _ Hposition) as
    [prevw [Hlookup [_ [_ [_ [_ [_ [Hforward _]]]]]]]].
  exists prevw; rewrite Hprev; split; [exact Hlookup|exact Hforward].
Qed.

Definition flag_unlink_first_neighbor_nodes
  (nodes : addr -> option FlagWaiterState) (w : FlagWaiterState) :=
  if Z.eqb w.(flagWaitImage).(flagNodePrev) 0 then nodes else
    flag_nodes_set_next nodes w.(flagWaitImage).(flagNodePrev) w.(flagWaitImage).(flagNodeNext).

Lemma flag_unlink_first_neighbor_next_lookup : forall sg s p w,
  valid_flag_state sg s -> s.(flagWaitNodes) p = Some w ->
  w.(flagWaitImage).(flagNodeNext) <> 0 ->
  exists nextw,
    flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w w.(flagWaitImage).(flagNodeNext) = Some nextw /\
    nextw.(flagWaitImage).(flagNodePrev) = p.
Proof.
  intros sg s p w Hvalid Hw Hnext0.
  destruct (flag_linked_node_next_lookup _ _ _ _ Hvalid Hw Hnext0) as [before [Hbefore Hprev]].
  unfold flag_unlink_first_neighbor_nodes.
  destruct (Z.eqb (flagNodePrev (flagWaitImage w)) 0); [exists before; auto|].
  rewrite flag_nodes_set_next_lookup, Hbefore.
  destruct (Z.eq_dec (flagNodeNext (flagWaitImage w)) (flagNodePrev (flagWaitImage w)));
    (eexists; split; [reflexivity|exact Hprev]).
Qed.

Lemma flag_linked_node_head_lookup : forall sg s p w,
  valid_flag_state sg s -> s.(flagWaitNodes) p = Some w ->
  w.(flagWaitImage).(flagNodePrev) = 0 ->
  exists v, s.(flagImages) w.(flagGroup) = Some v /\ v.(flagImageHead) = p /\
    w.(flagWaitImage).(flagNodeGroup) = flag_pool_addr sg w.(flagGroup).
Proof.
  intros sg s p w Hvalid Hw Hprev0.
  destruct (valid_flag_state_node_position _ _ _ _ Hvalid Hw) as
    [g [pre [rest [Hg [Hlist [_ [_ [Hgroup [Hprev [Hnext _]]]]]]]]]].
  pose proof (valid_flag_wait_order_nonzero _ _ _ _ Hvalid Hg) as Hnonzero.
  destruct Hvalid as [_ [_ [_ [Hused _]]]].
  destruct (Hused _ g Hg) as [_ [_ [_ [v [Hv [_ [Hhead _]]]]]]].
  exists v; split; [exact Hv|]; split; [|exact Hgroup].
  destruct pre as [|a pre]; [rewrite Hlist in Hhead; exact Hhead|].
  exfalso; assert (Hlast : last (a :: pre) 0 <> 0).
  { apply kernel_list_last_nonzero; [discriminate|].
    intros q Hq; apply Hnonzero; rewrite Hlist; apply in_or_app; left; exact Hq. }
  apply Hlast; congruence.
Qed.

(** The first store is either Group.WaitList := Next or Prev.Next := Next.
    These assertions are instruction cutpoints, not additional kernel states.
    TCB.OSTCBFlagNode is task-owned and is framed by this local protocol. *)
Definition flag_unlink_head_store_frame (sg : StableGlobVars) (s : GlobFlagState)
  (w : FlagWaiterState) (v : FlagGroupImage) : Assertion :=
  flag_group_rep_without_head sg.(osKernelConfig) (flag_pool_addr sg w.(flagGroup)) v **
  flag_groups_without sg s w.(flagGroup) ** flag_nodes_rep sg s **
  sg.(g_OSFlagFreeList) # Ptr |->
    match s.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.

Definition flag_unlink_prev_store_frame (sg : StableGlobVars) (s : GlobFlagState)
  (w prevw : FlagWaiterState) : Assertion :=
  flag_node_rep_without_next sg.(osKernelConfig) w.(flagWaitImage).(flagNodePrev) prevw.(flagWaitImage) **
  flag_wait_nodes_without_node sg s.(flagWaitNodes) w.(flagWaitImage).(flagNodePrev) **
  flag_groups_rep sg s **
  sg.(g_OSFlagFreeList) # Ptr |->
    match s.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.

Definition flag_unlink_after_first_store_rep (sg : StableGlobVars)
  (s post : GlobFlagState) (w : FlagWaiterState) : Assertion :=
  flag_groups_rep sg post **
  flag_wait_nodes_rep sg (flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w) **
  sg.(g_OSFlagFreeList) # Ptr |->
    match s.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.

Lemma flag_unlink_split_head_store : forall sg s p w,
  valid_flag_state sg s -> s.(flagWaitNodes) p = Some w ->
  w.(flagWaitImage).(flagNodePrev) = 0 ->
  exists v, s.(flagImages) w.(flagGroup) = Some v /\
    flag_raw_rep sg s |--
      (w.(flagWaitImage).(flagNodeGroup) + 4) # Ptr |-> p ** flag_unlink_head_store_frame sg s w v.
Proof.
  intros sg s p w Hvalid Hw Hprev0.
  destruct (flag_linked_node_head_lookup _ _ _ _ Hvalid Hw Hprev0) as [v [Hv [Hhead Hgroup]]].
  exists v; split; [exact Hv|].
  unfold flag_raw_rep, flag_unlink_head_store_frame.
  sep_apply_l_atomic (flag_groups_rep_split_head sg s w.(flagGroup) v Hv).
  rewrite Hhead, Hgroup; entailer!.
Qed.

Lemma flag_unlink_merge_head_store : forall sg s p w post v,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  w.(flagWaitImage).(flagNodePrev) = 0 -> s.(flagImages) w.(flagGroup) = Some v ->
  (w.(flagWaitImage).(flagNodeGroup) + 4) # Ptr |-> w.(flagWaitImage).(flagNodeNext) **
    flag_unlink_head_store_frame sg s w v |-- flag_unlink_after_first_store_rep sg s post w.
Proof.
  intros sg s p w post v Hvalid Hstep Hprev0 Hv.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  destruct (valid_flag_state_node_position _ _ _ _ Hvalid Hw) as
    [g [pre [rest [Hg [_ [_ [_ [Hgroup _]]]]]]]].
  destruct (flag_unlink_group_fields _ _ _ _ _ _ Hstep Hg Hv) as [_ [Himages _]].
  rewrite Hprev0, Z.eqb_refl in Himages.
  unfold flag_unlink_head_store_frame, flag_unlink_after_first_store_rep,
    flag_unlink_first_neighbor_nodes, flag_nodes_rep.
  rewrite Hprev0, Z.eqb_refl, Hgroup.
  sep_apply_l_atomic (flag_groups_rep_merge_updated_head sg s post w.(flagGroup) v
    w.(flagWaitImage).(flagNodeNext) Himages); entailer!.
Qed.

Lemma flag_unlink_split_prev_store : forall sg s p w,
  valid_flag_state sg s -> s.(flagWaitNodes) p = Some w ->
  w.(flagWaitImage).(flagNodePrev) <> 0 ->
  exists prevw, s.(flagWaitNodes) w.(flagWaitImage).(flagNodePrev) = Some prevw /\
    flag_raw_rep sg s |--
      w.(flagWaitImage).(flagNodePrev) # Ptr |-> p ** flag_unlink_prev_store_frame sg s w prevw.
Proof.
  intros sg s p w Hvalid Hw Hprev0.
  destruct (flag_linked_node_prev_lookup _ _ _ _ Hvalid Hw Hprev0) as [prevw [Hprevw Hnext]].
  exists prevw; split; [exact Hprevw|].
  unfold flag_raw_rep, flag_nodes_rep, flag_unlink_prev_store_frame.
  sep_apply_l_atomic (flag_wait_nodes_rep_split_next sg s.(flagWaitNodes)
    w.(flagWaitImage).(flagNodePrev) prevw Hprevw).
  rewrite Hnext; entailer!.
Qed.

Lemma flag_unlink_merge_prev_store : forall sg s p w post prevw,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  w.(flagWaitImage).(flagNodePrev) <> 0 ->
  s.(flagWaitNodes) w.(flagWaitImage).(flagNodePrev) = Some prevw ->
  w.(flagWaitImage).(flagNodePrev) # Ptr |-> w.(flagWaitImage).(flagNodeNext) **
    flag_unlink_prev_store_frame sg s w prevw |-- flag_unlink_after_first_store_rep sg s post w.
Proof.
  intros sg s p w post prevw Hvalid Hstep Hprev0 Hprevw.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  destruct (valid_flag_state_node_position _ _ _ _ Hvalid Hw) as [g [pre [rest [Hg _]]]].
  destruct Hvalid as [_ [_ [_ [Hused _]]]].
  destruct (Hused _ g Hg) as [_ [_ [_ [v [Hv _]]]]].
  destruct (flag_unlink_group_fields _ _ _ _ _ _ Hstep Hg Hv) as [_ [Himages _]].
  apply Z.eqb_neq in Hprev0; rewrite Hprev0 in Himages.
  unfold flag_unlink_prev_store_frame, flag_unlink_after_first_store_rep, flag_unlink_first_neighbor_nodes.
  rewrite Hprev0.
  sep_apply_l_atomic (flag_wait_nodes_rep_merge_updated_next sg s.(flagWaitNodes)
    w.(flagWaitImage).(flagNodePrev) prevw w.(flagWaitImage).(flagNodeNext) Hprevw).
  unfold flag_groups_rep; rewrite Himages; entailer!.
Qed.

Definition flag_unlink_next_store_frame (sg : StableGlobVars) (s post : GlobFlagState)
  (w nextw : FlagWaiterState) : Assertion :=
  flag_node_rep_without_prev sg.(osKernelConfig) w.(flagWaitImage).(flagNodeNext) nextw.(flagWaitImage) **
  flag_wait_nodes_without_node sg (flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w)
    w.(flagWaitImage).(flagNodeNext) ** flag_groups_rep sg post **
  sg.(g_OSFlagFreeList) # Ptr |->
    match s.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.

Lemma flag_unlink_split_next_store : forall sg s p w post,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  w.(flagWaitImage).(flagNodeNext) <> 0 ->
  exists nextw,
    flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w w.(flagWaitImage).(flagNodeNext) = Some nextw /\
    flag_unlink_after_first_store_rep sg s post w |--
      (w.(flagWaitImage).(flagNodeNext) + 4) # Ptr |-> p ** flag_unlink_next_store_frame sg s post w nextw.
Proof.
  intros sg s p w post Hvalid Hstep Hnext0.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  destruct (flag_unlink_first_neighbor_next_lookup _ _ _ _ Hvalid Hw Hnext0) as [nextw [Hnextw Hprev]].
  exists nextw; split; [exact Hnextw|].
  unfold flag_unlink_after_first_store_rep, flag_unlink_next_store_frame.
  sep_apply_l_atomic (flag_wait_nodes_rep_split_prev sg (flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w)
    w.(flagWaitImage).(flagNodeNext) nextw Hnextw).
  rewrite Hprev; entailer!.
Qed.

Lemma flag_unlink_merge_next_store : forall sg s p w post nextw,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  w.(flagWaitImage).(flagNodeNext) <> 0 ->
  flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w w.(flagWaitImage).(flagNodeNext) = Some nextw ->
  (w.(flagWaitImage).(flagNodeNext) + 4) # Ptr |-> w.(flagWaitImage).(flagNodePrev) **
    flag_unlink_next_store_frame sg s post w nextw |--
    flag_node_return_loan sg.(osKernelConfig) w ** flag_raw_rep sg post.
Proof.
  intros sg s p w post nextw Hvalid Hstep Hnext0 Hnextw.
  unfold flag_unlink_next_store_frame.
  sep_apply_l_atomic (flag_wait_nodes_rep_merge_updated_prev sg
    (flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w)
    w.(flagWaitImage).(flagNodeNext) nextw w.(flagWaitImage).(flagNodePrev) Hnextw).
  pose proof (flag_unlink_reconstructs_raw_rep sg s p w post Hvalid Hstep) as Hclose.
  unfold flag_unlink_neighbors_rep, flag_unlink_neighbor_nodes in Hclose.
  apply Z.eqb_neq in Hnext0; rewrite Hnext0 in Hclose.
  fold (flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w) in Hclose.
  sep_apply_l_atomic Hclose; entailer!.
Qed.

Lemma flag_unlink_without_next_store_reconstructs_raw_rep : forall sg s p w post,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  w.(flagWaitImage).(flagNodeNext) = 0 ->
  flag_unlink_after_first_store_rep sg s post w |--
    flag_node_return_loan sg.(osKernelConfig) w ** flag_raw_rep sg post.
Proof.
  intros sg s p w post Hvalid Hstep Hnext0.
  unfold flag_unlink_after_first_store_rep.
  pose proof (flag_unlink_reconstructs_raw_rep sg s p w post Hvalid Hstep) as Hclose.
  unfold flag_unlink_neighbors_rep, flag_unlink_neighbor_nodes in Hclose.
  rewrite Hnext0, Z.eqb_refl in Hclose.
  unfold flag_unlink_first_neighbor_nodes; rewrite Hnext0.
  sep_apply_l_atomic Hclose; entailer!.
Qed.
