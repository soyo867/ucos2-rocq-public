Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_program_storage.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A companion resource family for nodes whose actual owner supplies the
    six C fields. The existing full-byte Flag and kernel worlds are unchanged.
    These definitions retain the SAME pure state invariant: a padding image
    still describes the abstract image, but does not allocate its bytes. *)
Definition flag_fields_raw_rep (sg : StableGlobVars)
  (flags : GlobFlagState) : Assertion :=
  flag_groups_rep sg flags **
  flag_wait_nodes_fields_rep sg flags.(flagWaitNodes) **
  sg.(g_OSFlagFreeList) # Ptr |->
    match flags.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.

Definition flag_fields_configured_rep (sg : StableGlobVars)
  (flags : GlobFlagState) : Assertion :=
  if sg.(osKernelConfig).(cfgFlagEnabled)
  then flag_fields_raw_rep sg flags else emp.

Definition flag_configured_padding_rep (sg : StableGlobVars)
  (flags : GlobFlagState) : Assertion :=
  if sg.(osKernelConfig).(cfgFlagEnabled)
  then flag_wait_nodes_padding_rep sg flags.(flagWaitNodes) else emp.

(** [owns] selects actual supplemental padding owners, not allocation rights.
    It may omit ANY number of nodes. No single-current-node restriction is
    imposed, and false leaves the six field resources in their own map. *)
Definition flag_configured_padding_policy_rep (sg : StableGlobVars)
  (owns : addr -> bool) (flags : GlobFlagState) : Assertion :=
  if sg.(osKernelConfig).(cfgFlagEnabled)
  then flag_wait_nodes_padding_policy_rep sg owns flags.(flagWaitNodes) else emp.

Definition UCOS2_fields_raw_rep (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  flag_fields_configured_rep sg s.(FlagState) **
  UCOS2_raw_rep_missing_flag sg s.

Definition UCOS2_fields_inv (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg s) && UCOS2_fields_raw_rep sg s.

Definition UCOS2_fields_policy_inv (sg : StableGlobVars)
  (owns : addr -> bool) (s : UCOS2_Verify_State) : Assertion :=
  UCOS2_fields_inv sg s **
  flag_configured_padding_policy_rep sg owns s.(FlagState).

Definition kernel_program_fields_rep (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  UCOS2_fields_raw_rep sg s ** unmap_table_rep sg.

Definition kernel_program_fields_inv (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg s) && kernel_program_fields_rep sg s.

Definition kernel_program_fields_policy_inv (sg : StableGlobVars)
  (owns : addr -> bool) (s : UCOS2_Verify_State) : Assertion :=
  kernel_program_fields_inv sg s **
  flag_configured_padding_policy_rep sg owns s.(FlagState).

(** Exact bridges retain all padding separately. Neither direction drops
    owned bytes; the reverse direction requires the padding map on its left. *)
Lemma flag_raw_rep_fields_padding : forall sg flags,
  flag_raw_rep sg flags --||--
    flag_fields_raw_rep sg flags **
    flag_wait_nodes_padding_rep sg flags.(flagWaitNodes).
Proof.
  intros; unfold flag_raw_rep, flag_nodes_rep, flag_fields_raw_rep.
  rewrite flag_wait_nodes_rep_fields_padding; split; entailer!.
Qed.

Lemma flag_configured_rep_fields_padding : forall sg flags,
  flag_configured_rep sg flags --||--
    flag_fields_configured_rep sg flags ** flag_configured_padding_rep sg flags.
Proof.
  intros; unfold flag_configured_rep, flag_fields_configured_rep,
    flag_configured_padding_rep.
  destruct sg.(osKernelConfig).(cfgFlagEnabled).
  - apply flag_raw_rep_fields_padding.
  - split; entailer!.
Qed.

Lemma UCOS2_raw_rep_fields_padding : forall sg s,
  UCOS2_raw_rep sg s --||--
    UCOS2_fields_raw_rep sg s ** flag_configured_padding_rep sg s.(FlagState).
Proof.
  intros; rewrite (UCOS2_raw_rep_split_module sg s FlagModule).
  cbn [UCOS2_module_rep].
  rewrite flag_configured_rep_fields_padding.
  unfold UCOS2_fields_raw_rep, UCOS2_raw_rep_missing_flag; split; entailer!.
Qed.

Lemma UCOS2_inv_fields_padding : forall sg s,
  UCOS2_inv sg s --||--
    UCOS2_fields_inv sg s ** flag_configured_padding_rep sg s.(FlagState).
Proof.
  intros; rewrite UCOS2_inv_split_flag, flag_configured_rep_fields_padding.
  unfold UCOS2_fields_inv, UCOS2_fields_raw_rep; split; entailer!.
Qed.

Lemma kernel_program_fields_inv_split_unmap : forall sg s,
  kernel_program_fields_inv sg s --||--
    UCOS2_fields_inv sg s ** unmap_table_rep sg.
Proof.
  intros; unfold kernel_program_fields_inv, kernel_program_fields_rep,
    UCOS2_fields_inv; split; entailer!.
Qed.

Lemma kernel_program_inv_fields_padding : forall sg s,
  kernel_program_inv sg s --||--
    kernel_program_fields_inv sg s ** flag_configured_padding_rep sg s.(FlagState).
Proof.
  intros; rewrite kernel_program_inv_split_unmap, UCOS2_inv_fields_padding,
    kernel_program_fields_inv_split_unmap; split; entailer!.
Qed.

Lemma flag_configured_padding_policy_all : forall sg flags,
  flag_configured_padding_policy_rep sg (fun _ => true) flags =
    flag_configured_padding_rep sg flags.
Proof.
  intros; unfold flag_configured_padding_policy_rep, flag_configured_padding_rep.
  destruct sg.(osKernelConfig).(cfgFlagEnabled); [apply flag_wait_nodes_padding_policy_all|reflexivity].
Qed.

(** Full recovery quantifies over EVERY live node. Removal of one
    invocation's node does not prove this premise for another one. *)
Lemma flag_configured_padding_policy_live : forall sg owns flags,
  (forall p w, flags.(flagWaitNodes) p = Some w -> owns p = true) ->
  flag_configured_padding_policy_rep sg owns flags --||--
    flag_configured_padding_rep sg flags.
Proof.
  intros sg owns flags Hlive.
  unfold flag_configured_padding_policy_rep, flag_configured_padding_rep.
  destruct sg.(osKernelConfig).(cfgFlagEnabled).
  - apply flag_wait_nodes_padding_policy_live; exact Hlive.
  - split; reflexivity.
Qed.

Lemma UCOS2_fields_policy_inv_all : forall sg s,
  UCOS2_fields_policy_inv sg (fun _ => true) s --||-- UCOS2_inv sg s.
Proof.
  intros; unfold UCOS2_fields_policy_inv.
  rewrite flag_configured_padding_policy_all, <- UCOS2_inv_fields_padding.
  split; reflexivity.
Qed.

Lemma UCOS2_fields_policy_inv_live : forall sg owns s,
  (forall p w, s.(FlagState).(flagWaitNodes) p = Some w -> owns p = true) ->
  UCOS2_fields_policy_inv sg owns s --||-- UCOS2_inv sg s.
Proof.
  intros sg owns s Hlive; unfold UCOS2_fields_policy_inv.
  rewrite (flag_configured_padding_policy_live sg owns s.(FlagState) Hlive),
    <- UCOS2_inv_fields_padding; split; reflexivity.
Qed.

Lemma kernel_program_fields_policy_inv_live : forall sg owns s,
  (forall p w, s.(FlagState).(flagWaitNodes) p = Some w -> owns p = true) ->
  kernel_program_fields_policy_inv sg owns s --||-- kernel_program_inv sg s.
Proof.
  intros sg owns s Hlive; unfold kernel_program_fields_policy_inv.
  rewrite (flag_configured_padding_policy_live sg owns s.(FlagState) Hlive),
    <- kernel_program_inv_fields_padding; split; reflexivity.
Qed.

(** Local Flag resources preserve all group images, the free-list cell,
    and all other nodes. Updated merge requires actual off-node agreement. *)
Definition flag_fields_raw_rep_without_node (sg : StableGlobVars)
  (flags : GlobFlagState) (p : addr) : Assertion :=
  flag_groups_rep sg flags **
  flag_wait_nodes_fields_without_node sg flags.(flagWaitNodes) p **
  sg.(g_OSFlagFreeList) # Ptr |->
    match flags.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.

Lemma flag_fields_raw_rep_split_node : forall sg flags p w,
  flags.(flagWaitNodes) p = Some w ->
  flag_fields_raw_rep sg flags --||--
    flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage) **
    flag_fields_raw_rep_without_node sg flags p.
Proof.
  intros sg flags p w Hnode.
  assert (Hmap : flag_wait_nodes_fields_rep sg flags.(flagWaitNodes) --||--
    flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage) **
    flag_wait_nodes_fields_without_node sg flags.(flagWaitNodes) p).
  { split.
    - apply flag_wait_nodes_fields_rep_split_node; exact Hnode.
    - apply flag_wait_nodes_fields_rep_merge_node; exact Hnode. }
  unfold flag_fields_raw_rep, flag_fields_raw_rep_without_node.
  rewrite Hmap; split; entailer!.
Qed.

Lemma flag_fields_raw_rep_without_node_frame : forall sg before after p,
  before.(flagImages) = after.(flagImages) ->
  before.(flagFree) = after.(flagFree) ->
  (forall q, q <> p -> before.(flagWaitNodes) q = after.(flagWaitNodes) q) ->
  flag_fields_raw_rep_without_node sg before p --||--
    flag_fields_raw_rep_without_node sg after p.
Proof.
  intros sg before after p Himages Hfree Hnodes.
  unfold flag_fields_raw_rep_without_node, flag_groups_rep,
    flag_wait_nodes_fields_without_node.
  rewrite Himages, Hfree.
  rewrite (store_map_missing_i_equiv
    (fun q v => flag_node_fields_rep sg.(osKernelConfig) q v.(flagWaitImage))
    _ _ p Hnodes); split; reflexivity.
Qed.

Lemma flag_fields_raw_rep_merge_updated_node : forall sg before after p w,
  after.(flagWaitNodes) p = Some w ->
  before.(flagImages) = after.(flagImages) ->
  before.(flagFree) = after.(flagFree) ->
  (forall q, q <> p -> before.(flagWaitNodes) q = after.(flagWaitNodes) q) ->
  flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage) **
    flag_fields_raw_rep_without_node sg before p |-- flag_fields_raw_rep sg after.
Proof.
  intros sg before after p w Hnode Himages Hfree Hnodes.
  rewrite (flag_fields_raw_rep_without_node_frame sg before after p Himages Hfree Hnodes).
  exact (proj2 (flag_fields_raw_rep_split_node sg after p w Hnode)).
Qed.

Lemma flag_fields_raw_rep_frame_eq : forall sg before after,
  before.(flagImages) = after.(flagImages) ->
  before.(flagWaitNodes) = after.(flagWaitNodes) ->
  before.(flagFree) = after.(flagFree) ->
  flag_fields_raw_rep sg before = flag_fields_raw_rep sg after.
Proof.
  intros sg before after Himages Hnodes Hfree.
  unfold flag_fields_raw_rep, flag_groups_rep; rewrite Himages, Hnodes, Hfree; reflexivity.
Qed.

Lemma flag_fields_configured_rep_frame_eq : forall sg before after,
  before.(flagImages) = after.(flagImages) ->
  before.(flagWaitNodes) = after.(flagWaitNodes) ->
  before.(flagFree) = after.(flagFree) ->
  flag_fields_configured_rep sg before = flag_fields_configured_rep sg after.
Proof.
  intros sg before after Himages Hnodes Hfree; unfold flag_fields_configured_rep.
  destruct sg.(osKernelConfig).(cfgFlagEnabled); [apply flag_fields_raw_rep_frame_eq; assumption|reflexivity].
Qed.

Lemma UCOS2_fields_inv_split_flag : forall sg s,
  UCOS2_fields_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (flag_fields_configured_rep sg s.(FlagState) ** UCOS2_raw_rep_missing_flag sg s).
Proof. intros; split; reflexivity. Qed.

Lemma UCOS2_fields_inv_merge_updated_flag : forall sg before after,
  UCOS2_state_inv sg after ->
  UCOS2_raw_rep_missing_flag sg before = UCOS2_raw_rep_missing_flag sg after ->
  flag_fields_configured_rep sg after.(FlagState) ** UCOS2_raw_rep_missing_flag sg before |--
    UCOS2_fields_inv sg after.
Proof.
  intros sg before after Hvalid Hframe; rewrite Hframe.
  unfold UCOS2_fields_inv, UCOS2_fields_raw_rep; entailer!.
Qed.

Lemma UCOS2_fields_inv_merge_replace_flag : forall sg s flags,
  UCOS2_state_inv sg (replace_FlagS flags s) ->
  flag_fields_configured_rep sg flags ** UCOS2_raw_rep_missing_flag sg s |--
    UCOS2_fields_inv sg (replace_FlagS flags s).
Proof.
  intros sg s flags Hvalid.
  apply (UCOS2_fields_inv_merge_updated_flag sg s (replace_FlagS flags s));
    [exact Hvalid|symmetry; apply UCOS2_raw_rep_missing_flag_replace_eq].
Qed.

(** Non-Flag operations get a structural residual. Task-indexed Event and
    Scheduler stores require their real representation transport proofs. *)
Definition UCOS2_fields_raw_rep_missing_module (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (m : UCOS2Module) : Assertion :=
  flag_fields_configured_rep sg s.(FlagState) **
  UCOS2_raw_rep_missing_two sg s FlagModule m.

Lemma UCOS2_fields_raw_rep_split_module : forall sg s m,
  m <> FlagModule ->
  UCOS2_fields_raw_rep sg s --||--
    UCOS2_module_rep sg s m ** UCOS2_fields_raw_rep_missing_module sg s m.
Proof.
  intros sg s m Hdistinct.
  unfold UCOS2_fields_raw_rep, UCOS2_fields_raw_rep_missing_module,
    UCOS2_raw_rep_missing_flag.
  rewrite (UCOS2_raw_rep_missing_module_split_module sg s FlagModule m)
    by congruence.
  split; entailer!.
Qed.

Lemma UCOS2_fields_inv_split_module : forall sg s m,
  m <> FlagModule ->
  UCOS2_fields_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (UCOS2_module_rep sg s m ** UCOS2_fields_raw_rep_missing_module sg s m).
Proof.
  intros sg s m Hdistinct; unfold UCOS2_fields_inv.
  rewrite (UCOS2_fields_raw_rep_split_module sg s m Hdistinct); split; reflexivity.
Qed.

Lemma UCOS2_fields_raw_rep_missing_module_frame_eq : forall sg before after m,
  flag_fields_configured_rep sg before.(FlagState) =
    flag_fields_configured_rep sg after.(FlagState) ->
  (forall n, n <> FlagModule -> n <> m ->
    UCOS2_module_rep sg before n = UCOS2_module_rep sg after n) ->
  UCOS2_fields_raw_rep_missing_module sg before m =
    UCOS2_fields_raw_rep_missing_module sg after m.
Proof.
  intros sg before after m Hflag Hparts.
  unfold UCOS2_fields_raw_rep_missing_module; rewrite Hflag.
  rewrite (UCOS2_raw_rep_missing_two_frame sg before after FlagModule m Hparts); reflexivity.
Qed.

Lemma UCOS2_fields_inv_merge_updated_module : forall sg before after m,
  m <> FlagModule -> UCOS2_state_inv sg after ->
  UCOS2_fields_raw_rep_missing_module sg before m =
    UCOS2_fields_raw_rep_missing_module sg after m ->
  UCOS2_module_rep sg after m ** UCOS2_fields_raw_rep_missing_module sg before m |--
    UCOS2_fields_inv sg after.
Proof.
  intros sg before after m Hdistinct Hvalid Hframe.
  rewrite Hframe, (UCOS2_fields_inv_split_module sg after m Hdistinct); entailer!.
Qed.

(** The common Block/Unlink/TaskRdy footprint leaves parked Task stacks
    in the existing residual; it never recreates their local provenance. *)
Lemma UCOS2_fields_raw_rep_split_task_storage_sched_flag : forall sg s,
  UCOS2_fields_raw_rep sg s --||--
    task_public_storage sg s.(TskState) **
    sched_raw_rep sg s.(TskState) s.(SchedState) **
    flag_fields_configured_rep sg s.(FlagState) **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg s.
Proof.
  intros; unfold UCOS2_fields_raw_rep, UCOS2_raw_rep_missing_flag,
    UCOS2_raw_rep_missing_module, UCOS2_selected_rep,
    UCOS2_raw_rep_missing_task_storage_sched_flag.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep].
  unfold task_shared_rep; split; entailer!.
Qed.

Lemma UCOS2_fields_inv_split_task_storage_sched_flag : forall sg s,
  UCOS2_fields_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (task_public_storage sg s.(TskState) **
     sched_raw_rep sg s.(TskState) s.(SchedState) **
     flag_fields_configured_rep sg s.(FlagState) **
     UCOS2_raw_rep_missing_task_storage_sched_flag sg s).
Proof.
  intros; unfold UCOS2_fields_inv.
  rewrite UCOS2_fields_raw_rep_split_task_storage_sched_flag; split; reflexivity.
Qed.

Lemma UCOS2_fields_inv_merge_updated_task_storage_sched_flag : forall sg before after,
  UCOS2_state_inv sg after ->
  UCOS2_raw_rep_missing_task_storage_sched_flag sg before =
    UCOS2_raw_rep_missing_task_storage_sched_flag sg after ->
  task_public_storage sg after.(TskState) **
    sched_raw_rep sg after.(TskState) after.(SchedState) **
    flag_fields_configured_rep sg after.(FlagState) **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg before |--
    UCOS2_fields_inv sg after.
Proof.
  intros sg before after Hvalid Hframe.
  rewrite Hframe, UCOS2_fields_inv_split_task_storage_sched_flag; entailer!.
Qed.

Lemma UCOS2_fields_inv_merge_flag_wake : forall sg s p w after old bits result,
  UCOS2_state_inv sg s ->
  flag_unlink_node s.(FlagState) p = Some (w, after) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  let post := flag_wake_state sg s w after old bits result in
  task_public_storage sg post.(TskState) **
    sched_raw_rep sg post.(TskState) post.(SchedState) **
    flag_fields_configured_rep sg post.(FlagState) **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg s |--
    UCOS2_fields_inv sg post.
Proof.
  intros sg s p w after old bits result Hvalid Hstep Hold post.
  apply UCOS2_fields_inv_merge_updated_task_storage_sched_flag.
  - apply (UCOS2_flag_wake_preserves_validity sg s p w after old bits result);
      assumption.
  - symmetry; apply UCOS2_flag_wake_residual_eq; exact Hold.
Qed.

(** Padding transports along an actual equality of node domains and
    padding images. Node insertion/removal instead uses the lower module's
    explicit padding split/merge laws and the removed node's real owner. *)
Lemma flag_configured_padding_policy_rep_equiv : forall sg owns before after,
  (forall p,
    option_map (fun w => w.(flagWaitImage).(flagNodePadding)) (before.(flagWaitNodes) p) =
    option_map (fun w => w.(flagWaitImage).(flagNodePadding)) (after.(flagWaitNodes) p)) ->
  flag_configured_padding_policy_rep sg owns before --||--
    flag_configured_padding_policy_rep sg owns after.
Proof.
  intros sg owns before after Hpadding; unfold flag_configured_padding_policy_rep.
  destruct sg.(osKernelConfig).(cfgFlagEnabled).
  - apply flag_wait_nodes_padding_policy_rep_equiv; exact Hpadding.
  - split; reflexivity.
Qed.

Lemma kernel_program_fields_policy_inv_split_unmap : forall sg owns s,
  kernel_program_fields_policy_inv sg owns s --||--
    UCOS2_fields_policy_inv sg owns s ** unmap_table_rep sg.
Proof.
  intros; unfold kernel_program_fields_policy_inv, UCOS2_fields_policy_inv.
  rewrite kernel_program_fields_inv_split_unmap; split; entailer!.
Qed.

(** Group-head writes in Block and Unlink retain the complete node map.
    The caller separately proves the node-map update before group merge. *)
Definition flag_fields_raw_rep_without_group (sg : StableGlobVars)
  (flags : GlobFlagState) (i : FlagID) : Assertion :=
  flag_groups_without sg flags i **
  flag_wait_nodes_fields_rep sg flags.(flagWaitNodes) **
  sg.(g_OSFlagFreeList) # Ptr |->
    match flags.(flagFree) with [] => 0 | j :: _ => flag_pool_addr sg j end.

Lemma flag_fields_raw_rep_split_group : forall sg flags i v,
  flags.(flagImages) i = Some v ->
  flag_fields_raw_rep sg flags --||--
    flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) v **
    flag_fields_raw_rep_without_group sg flags i.
Proof.
  intros sg flags i v Hgroup.
  assert (Hgroups : flag_groups_rep sg flags --||--
    flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) v **
    flag_groups_without sg flags i).
  { split.
    - apply flag_groups_split_group; exact Hgroup.
    - apply flag_groups_merge_group; exact Hgroup. }
  unfold flag_fields_raw_rep, flag_fields_raw_rep_without_group.
  rewrite Hgroups; split; entailer!.
Qed.

Lemma flag_fields_raw_rep_without_group_frame : forall sg before after i,
  (forall j, j <> i -> before.(flagImages) j = after.(flagImages) j) ->
  before.(flagWaitNodes) = after.(flagWaitNodes) ->
  before.(flagFree) = after.(flagFree) ->
  flag_fields_raw_rep_without_group sg before i --||--
    flag_fields_raw_rep_without_group sg after i.
Proof.
  intros sg before after i Himages Hnodes Hfree.
  unfold flag_fields_raw_rep_without_group, flag_groups_without.
  rewrite Hnodes, Hfree.
  rewrite (store_map_missing_i_equiv
    (fun j v => flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg j) v)
    _ _ i Himages); split; reflexivity.
Qed.

Lemma flag_fields_raw_rep_merge_updated_group : forall sg before after i v,
  after.(flagImages) i = Some v ->
  (forall j, j <> i -> before.(flagImages) j = after.(flagImages) j) ->
  before.(flagWaitNodes) = after.(flagWaitNodes) ->
  before.(flagFree) = after.(flagFree) ->
  flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) v **
    flag_fields_raw_rep_without_group sg before i |-- flag_fields_raw_rep sg after.
Proof.
  intros sg before after i v Hgroup Himages Hnodes Hfree.
  rewrite (flag_fields_raw_rep_without_group_frame sg before after i Himages Hnodes Hfree).
  exact (proj2 (flag_fields_raw_rep_split_group sg after i v Hgroup)).
Qed.

Lemma UCOS2_fields_inv_merge_flag_timeout_cleanup : forall sg s p w after old,
  UCOS2_state_inv sg s ->
  flag_unlink_node s.(FlagState) p = Some (w, after) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  task_non_suspension_bits old.(stat) = 0 ->
  let post := flag_timeout_cleanup_state s w after old in
  task_public_storage sg post.(TskState) **
    sched_raw_rep sg post.(TskState) post.(SchedState) **
    flag_fields_configured_rep sg post.(FlagState) **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg s |--
    UCOS2_fields_inv sg post.
Proof.
  intros sg s p w after old Hvalid Hstep Hold Hstatus post.
  apply UCOS2_fields_inv_merge_updated_task_storage_sched_flag.
  - eapply UCOS2_flag_timeout_cleanup_preserves_validity; eauto.
  - symmetry; apply UCOS2_flag_timeout_cleanup_residual_eq; exact Hold.
Qed.

(** These are heap entailments and state-index transports only. Generic
    resources-parameterized continuation lemmas may consume this family,
    but Closed-world, scheduler-prefix, Tick, TaskDel and allowed IRQ/event
    source clients require their actual new resource proofs. No arbitrary
    scheduling frame rule, registered-client closure, checked C callee
    contract or public Pend same-X refinement is asserted here. *)
