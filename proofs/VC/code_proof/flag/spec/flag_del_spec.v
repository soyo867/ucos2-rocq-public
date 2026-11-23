(** Current OSFlagDel candidate: ordered source semantics and fields resources.
    The protected type recheck, acquired wait order, ignored TaskRdy Boolean,
    exact outputs and same arbitrary X are retained.  The call-effect programs
    are existing C-level interfaces. Actual public C cuts consume these
    definitions and the fields Scheduler interface. Paired Save/Restore are
    explicit conditional external contracts; their source-entry and scheduling
    preconditions remain subject to the candidate's semantic review. *)
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia Coq.Strings.String.
Require Import AUXLib.ListLib.
Require Export Ucos2Verify.VC.code.time.spec.time_dly_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_query_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_name_set_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_api_entry_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_source_fields_resources_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.lib.flag_fields_resources Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.kernel_names Ucos2Verify.lib.error_codes.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare safeexec_lib.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Definition flag_del_release_state sg state id image name : UCOS2_Verify_State :=
  replace_FlagS (flag_release sg state.(FlagState) id image name) state.

Lemma flag_del_release_name_references : forall sg flags id image name pointer,
  flag_name_reference (flag_release sg flags id image name) pointer ->
  flag_name_reference flags pointer.
Proof.
  intros sg flags id image name pointer [other [group [Hgroup Hname]]].
  change (kernel_map_set flags.(flagUsed) id None other = Some group) in Hgroup.
  unfold kernel_map_set in Hgroup; destruct (Z.eq_dec other id); [discriminate|].
  exists other, group; auto.
Qed.

Lemma flag_del_release_preserves_state_inv : forall sg state id group image name,
  UCOS2_state_inv sg state -> state.(FlagState).(flagUsed) id = Some group ->
  state.(FlagState).(flagImages) id = Some image -> group.(flagWaitOrder) = [] ->
  UCOS2_state_inv sg (flag_del_release_state sg state id image name).
Proof.
  intros sg state id group image name Hinv Hgroup Himage Hempty.
  destruct (flag_query_state_configuration sg state Hinv) as [Henabled [Hbits Hflags]].
  assert (Hnewflag : valid_flag_configuration sg (flag_release sg state.(FlagState) id image name)).
  { unfold valid_flag_configuration; rewrite Henabled.
    eapply flag_release_preserves_state_validity; eassumption. }
  assert (Hcross : cross_module_consistency sg (flag_del_release_state sg state id image name)).
  { apply cross_module_consistency_flag_nodes_frame; [reflexivity|].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hinv; tauto. }
  assert (Hnames : kernel_names_valid sg (flag_del_release_state sg state id image name)).
  { eapply kernel_names_valid_frame; [exact (UCOS2_state_inv_names_valid sg state Hinv)|reflexivity|..];
      try (intros; assumption).
    intros pointer Hp; eapply flag_del_release_name_references; exact Hp. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, flag_del_release_state in *.
  cbn [replace_FlagS] in *; tauto.
Qed.


Definition flag_del_pool_fields_frame sg state id : Assertion :=
  flag_groups_without sg state.(FlagState) id ** flag_wait_nodes_fields_rep sg state.(FlagState).(flagWaitNodes) **
  UCOS2_raw_rep_missing_flag sg state.

Definition flag_del_free_head sg flags : addr :=
  match flags.(flagFree) with [] => 0 | id :: _ => flag_pool_addr sg id end.

Lemma flag_del_pool_fields_split : forall sg state id image,
  sg.(osKernelConfig).(cfgFlagEnabled) = true -> state.(FlagState).(flagImages) id = Some image ->
  UCOS2_fields_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    (flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg id) image **
     sg.(g_OSFlagFreeList) # Ptr |-> flag_del_free_head sg state.(FlagState) **
     flag_del_pool_fields_frame sg state id).
Proof.
  intros sg state id image Henabled Himage; rewrite UCOS2_fields_inv_split_flag.
  unfold flag_fields_configured_rep; rewrite Henabled.
  unfold flag_fields_raw_rep, flag_del_pool_fields_frame, flag_del_free_head; Intros.
  sep_apply_l_atomic (flag_groups_split_group sg state.(FlagState) id image Himage); entailer!.
Qed.

Lemma flag_del_pool_fields_merge_original : forall sg state id image,
  sg.(osKernelConfig).(cfgFlagEnabled) = true -> UCOS2_state_inv sg state ->
  state.(FlagState).(flagImages) id = Some image ->
  flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg id) image **
    sg.(g_OSFlagFreeList) # Ptr |-> flag_del_free_head sg state.(FlagState) **
    flag_del_pool_fields_frame sg state id |-- UCOS2_fields_inv sg state.
Proof.
  intros sg state id image Henabled Hinv Himage; unfold flag_del_pool_fields_frame, flag_del_free_head.
  rewrite UCOS2_fields_inv_split_flag; unfold flag_fields_configured_rep; rewrite Henabled.
  unfold flag_fields_raw_rep; entailer!.
  sep_apply_r_atomic (flag_groups_merge_group sg state.(FlagState) id image Himage); entailer!.
Qed.

Lemma flag_del_pool_fields_merge_released : forall sg state id group image name,
  UCOS2_state_inv sg state -> state.(FlagState).(flagUsed) id = Some group ->
  state.(FlagState).(flagImages) id = Some image -> group.(flagWaitOrder) = [] ->
  flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg id)
    (flag_delete_image image (flag_del_free_head sg state.(FlagState)) name) **
    sg.(g_OSFlagFreeList) # Ptr |-> flag_pool_addr sg id ** flag_del_pool_fields_frame sg state id |--
  UCOS2_fields_inv sg (flag_del_release_state sg state id image name).
Proof.
  intros sg state id group image name Hinv Hgroup Himage Hempty.
  destruct (flag_query_state_configuration sg state Hinv) as [Henabled [Hbits Hflags]].
  pose proof (flag_del_release_preserves_state_inv sg state id group image name
    Hinv Hgroup Himage Hempty) as Hreleased.
  unfold flag_del_pool_fields_frame, flag_del_free_head.
  rewrite UCOS2_fields_inv_split_flag; unfold flag_del_release_state in *.
  cbn [replace_FlagS FlagState].
  unfold flag_fields_configured_rep; rewrite Henabled.
  unfold flag_fields_raw_rep; cbn [flag_release flagWaitNodes flagFree].
  rewrite UCOS2_raw_rep_missing_flag_replace_eq.
  entailer!.
  sep_apply_r_atomic (flag_groups_merge_updated_group sg state.(FlagState)
    (flag_release sg state.(FlagState) id image name) id
    (flag_delete_image image (match state.(FlagState).(flagFree) with
       [] => 0 | other :: _ => flag_pool_addr sg other end) name)
    ltac:(apply kernel_map_set_same)
    ltac:(intros other Hne; symmetry; apply kernel_map_set_other; exact Hne)); entailer!.
Qed.

(** The layout lemma exposes exactly the fields written by the source,
    including preserved padding.  The free-list root has a separate owner. *)
Definition flag_del_group_padding p image : Assertion :=
  store_optional_bytes (p + 1) (firstn 3 image.(flagImagePadding)) **
  store_optional_bytes (p + 10) (skipn 3 image.(flagImagePadding)).

Lemma flag_del_group_fields : forall config p image,
  config.(cfgFlagBits) = 16 -> config.(cfgFlagNames) = true ->
  flag_group_rep config p image --||--
  (p # UChar |-> image.(flagImageType) **
   (p + 4) # Ptr |-> image.(flagImageHead) **
   (p + 8) # UShort |-> image.(flagImageBits) **
   (p + 12) # Ptr |-> image.(flagImageName) ** flag_del_group_padding p image).
Proof.
  intros config p image Hbits Hnames.
  unfold flag_group_rep, flag_word_rep, flag_group_name_offset, flag_word_bytes, kernel_align4,
    flag_del_group_padding; rewrite Hbits, Hnames; cbn.
  replace (p + 8 + 2) with (p + 10) by lia; split; entailer!.
Qed.

Lemma flag_del_group_merge_deleted : forall config p image next name,
  config.(cfgFlagBits) = 16 -> config.(cfgFlagNames) = true ->
  p # UChar |-> 0 ** (p + 4) # Ptr |-> next **
    (p + 8) # UShort |-> 0 ** (p + 12) # Ptr |-> name ** flag_del_group_padding p image |--
  flag_group_rep config p (flag_delete_image image next name).
Proof.
  intros; rewrite (flag_del_group_fields config p (flag_delete_image image next name) H H0).
  unfold flag_del_group_padding; cbn [flag_delete_image]; entailer!.
Qed.


(** The abort fold traverses the acquired group's existing wait order.
    Each element uses the actual helper transformer;
    its ignored Boolean does not determine Del's scheduling decision. *)
Fixpoint flag_del_abort_waiters sg (nodes : list addr) (state : UCOS2_Verify_State)
  : option UCOS2_Verify_State :=
  match nodes with
  | [] => Some state
  | node :: rest =>
      match flag_task_rdy sg state node 0 PendAbort with
      | Some (_, next) => flag_del_abort_waiters sg rest next
      | None => None
      end
  end.

Lemma flag_del_abort_waiters_append : forall sg first rest before middle,
  flag_del_abort_waiters sg first before = Some middle ->
  flag_del_abort_waiters sg (first ++ rest) before = flag_del_abort_waiters sg rest middle.
Proof.
  intros sg first; induction first as [|node first IH]; intros rest before middle Hfirst.
  - cbn in Hfirst; inversion Hfirst; reflexivity.
  - cbn in Hfirst |- *; destruct (flag_task_rdy sg before node 0 PendAbort)
      as [[ready next]|] eqn:Hstep; [eapply IH; exact Hfirst|discriminate].
Qed.

Definition flag_del_valid_option (opt : Z) : bool := (Z.eqb opt 0 || Z.eqb opt 1)%bool.
Definition flag_del_observation (pointer : addr) (error : OSErrCode) : Z * Z :=
  (pointer, encode_os_err_code error).

(** Reads use the image at this particular cut.  Invalid options still
    reach the acquired wait-list read and never release a pool slot. *)
Definition flag_del_protected sg view pointer opt name
  : program UCOS2_Verify_State ((Z * Z) * bool) :=
  fun acquired result released => exists image,
    flag_query_selected view acquired image /\
    if (flag_del_valid_option opt && negb (Z.eqb image.(flagImageType) 5))%bool then
      result = (flag_del_observation pointer OS_ERR_EVENT_TYPE, false) /\ released = acquired
    else if Z.eqb opt 0 then
      if Z.eqb image.(flagImageHead) 0 then
        exists id, view = FlagQueryPool id /\
          result = (flag_del_observation 0 OS_ERR_NONE, false) /\
          released = flag_del_release_state sg acquired id image name
      else result = (flag_del_observation pointer OS_ERR_TASK_WAITING, false) /\ released = acquired
    else if Z.eqb opt 1 then
      exists id group drained drained_image,
        view = FlagQueryPool id /\ acquired.(FlagState).(flagUsed) id = Some group /\
        flag_del_abort_waiters sg group.(flagWaitOrder) acquired = Some drained /\
        drained.(FlagState).(flagImages) id = Some drained_image /\
        result = (flag_del_observation 0 OS_ERR_NONE, negb (Z.eqb image.(flagImageHead) 0)) /\
        released = flag_del_release_state sg drained id drained_image name
    else result = (flag_del_observation pointer OS_ERR_INVALID_OPT, false) /\ released = acquired.

Definition flag_del_prefix_program environment critical sg caller mask view pointer opt name
  : program UCOS2_Verify_State (((Z * Z) * bool) * TaskSuspendCaller) :=
  if Z.eqb pointer 0 then StateRelMonad.ret ((flag_del_observation pointer OS_ERR_FLAG_INVALID_PGRP, false), caller)
  else StateRelMonad.bind (StateRelBasic.get' (fun state => os_sched_ints state)) (fun nesting =>
    if 0 <? nesting then StateRelMonad.ret ((flag_del_observation pointer OS_ERR_DEL_ISR, false), caller)
    else StateRelMonad.bind (flag_query_observe view) (fun observed =>
      if Z.eqb observed.(flagImageType) 5 then
        StateRelMonad.bind (task_suspend_save_program environment critical sg caller mask) (fun entered =>
          StateRelMonad.bind (flag_del_protected sg view pointer opt name) (fun result =>
            StateRelMonad.bind (task_suspend_restore_program environment critical sg (fst entered))
              (fun returned => StateRelMonad.ret (result, returned))))
      else StateRelMonad.ret ((flag_del_observation pointer OS_ERR_EVENT_TYPE, false), caller))).

Definition flag_del_tail_program environment critical sg mask
  (result : ((Z * Z) * bool) * TaskSuspendCaller) : program UCOS2_Verify_State (Z * Z) :=
  if snd (fst result) then
    StateRelMonad.bind (task_suspend_schedule_program environment critical sg (snd result) mask)
      (fun _ => StateRelMonad.ret (fst (fst result)))
  else StateRelMonad.ret (fst (fst result)).

Definition flag_del_program environment critical sg caller mask view pointer opt name
  : program UCOS2_Verify_State (Z * Z) :=
  StateRelMonad.bind (flag_del_prefix_program environment critical sg caller mask view pointer opt name)
    (flag_del_tail_program environment critical sg mask).

Definition flag_del_safe environment critical sg caller mask view pointer opt name before
  (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (flag_del_program environment critical sg caller mask view pointer opt name) X.

Definition flag_del_return_safe current result
  (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = current) (StateRelMonad.ret result) X.

Lemma flag_del_prefix_null : forall environment critical sg caller mask view opt name before,
  flag_del_prefix_program environment critical sg caller mask view 0 opt name before
    ((flag_del_observation 0 OS_ERR_FLAG_INVALID_PGRP, false), caller) before.
Proof. intros; unfold flag_del_prefix_program; cbn; split; reflexivity. Qed.

Lemma flag_del_prefix_isr : forall environment critical sg caller mask view pointer opt name before,
  pointer <> 0 -> 0 < os_sched_ints before ->
  flag_del_prefix_program environment critical sg caller mask view pointer opt name before
    ((flag_del_observation pointer OS_ERR_DEL_ISR, false), caller) before.
Proof.
  intros environment critical sg caller mask view pointer opt name before Hp Hnest.
  unfold flag_del_prefix_program; rewrite (proj2 (Z.eqb_neq _ _) Hp).
  exists (os_sched_ints before), before; split; [split; reflexivity|].
  rewrite (proj2 (Z.ltb_lt _ _) Hnest); split; reflexivity.
Qed.

Lemma flag_del_prefix_wrong_type : forall environment critical sg caller mask view pointer opt name before image,
  pointer <> 0 -> os_sched_ints before = 0 -> flag_query_selected view before image ->
  image.(flagImageType) <> 5 ->
  flag_del_prefix_program environment critical sg caller mask view pointer opt name before
    ((flag_del_observation pointer OS_ERR_EVENT_TYPE, false), caller) before.
Proof.
  intros environment critical sg caller mask view pointer opt name before image Hp Hnest Himage Htype.
  unfold flag_del_prefix_program; rewrite (proj2 (Z.eqb_neq _ _) Hp).
  exists (os_sched_ints before), before; split; [split; reflexivity|].
  rewrite Hnest; cbn; exists image, before; split; [split; assumption || reflexivity|].
  rewrite (proj2 (Z.eqb_neq _ _) Htype); split; reflexivity.
Qed.

Lemma flag_del_prefix_protected : forall environment critical sg caller mask view pointer opt name before observed
  saved active acquired result released returned current,
  pointer <> 0 -> os_sched_ints before = 0 -> flag_query_selected view before observed ->
  observed.(flagImageType) = 5 ->
  task_suspend_save_effect environment critical sg caller active mask saved before acquired ->
  flag_del_protected sg view pointer opt name acquired result released ->
  task_suspend_restore_effect environment critical sg active returned released current ->
  flag_del_prefix_program environment critical sg caller mask view pointer opt name before (result, returned) current.
Proof.
  intros environment critical sg caller mask view pointer opt name before observed saved active acquired
    result released returned current Hp Hnest Himage Htype Hsave Hprotected Hrestore.
  unfold flag_del_prefix_program; rewrite (proj2 (Z.eqb_neq _ _) Hp).
  exists (os_sched_ints before), before; split; [split; reflexivity|].
  rewrite Hnest; cbn; exists observed, before; split; [split; assumption || reflexivity|].
  rewrite Htype, Z.eqb_refl; exists (active, saved), acquired; split; [exact Hsave|].
  exists result, released; split; [exact Hprotected|].
  exists returned, current; split; [exact Hrestore|split; reflexivity].
Qed.

Lemma flag_del_protected_recheck_error : forall sg view pointer opt name acquired image,
  flag_query_selected view acquired image -> flag_del_valid_option opt = true ->
  image.(flagImageType) <> 5 ->
  flag_del_protected sg view pointer opt name acquired
    (flag_del_observation pointer OS_ERR_EVENT_TYPE, false) acquired.
Proof.
  intros sg view pointer opt name acquired image Himage Hopt Htype.
  exists image; split; [exact Himage|].
  rewrite Hopt, (proj2 (Z.eqb_neq _ _) Htype); cbn; auto.
Qed.

Lemma flag_del_protected_invalid_option : forall sg view pointer opt name acquired image,
  flag_query_selected view acquired image -> opt <> 0 -> opt <> 1 ->
  flag_del_protected sg view pointer opt name acquired
    (flag_del_observation pointer OS_ERR_INVALID_OPT, false) acquired.
Proof.
  intros sg view pointer opt name acquired image Himage Hzero Hone.
  exists image; split; [exact Himage|]; unfold flag_del_valid_option.
  rewrite (proj2 (Z.eqb_neq _ _) Hzero), (proj2 (Z.eqb_neq _ _) Hone); cbn; auto.
Qed.

Lemma flag_del_protected_waiting : forall sg view pointer name acquired image,
  flag_query_selected view acquired image -> image.(flagImageType) = 5 -> image.(flagImageHead) <> 0 ->
  flag_del_protected sg view pointer 0 name acquired
    (flag_del_observation pointer OS_ERR_TASK_WAITING, false) acquired.
Proof.
  intros sg view pointer name acquired image Himage Htype Hhead.
  exists image; split; [exact Himage|].
  unfold flag_del_valid_option; rewrite Htype, (proj2 (Z.eqb_neq _ _) Hhead); cbn; auto.
Qed.

Lemma flag_del_protected_no_pend_empty : forall sg pointer name acquired id image,
  acquired.(FlagState).(flagImages) id = Some image -> image.(flagImageType) = 5 -> image.(flagImageHead) = 0 ->
  flag_del_protected sg (FlagQueryPool id) pointer 0 name acquired
    (flag_del_observation 0 OS_ERR_NONE, false) (flag_del_release_state sg acquired id image name).
Proof.
  intros sg pointer name acquired id image Himage Htype Hhead.
  exists image; split; [exact Himage|].
  unfold flag_del_valid_option; rewrite Htype, Hhead; cbn; exists id; auto.
Qed.

Lemma flag_del_protected_always : forall sg pointer name acquired id group image drained drained_image,
  acquired.(FlagState).(flagImages) id = Some image -> image.(flagImageType) = 5 ->
  acquired.(FlagState).(flagUsed) id = Some group ->
  flag_del_abort_waiters sg group.(flagWaitOrder) acquired = Some drained ->
  drained.(FlagState).(flagImages) id = Some drained_image ->
  flag_del_protected sg (FlagQueryPool id) pointer 1 name acquired
    (flag_del_observation 0 OS_ERR_NONE, negb (Z.eqb image.(flagImageHead) 0))
    (flag_del_release_state sg drained id drained_image name).
Proof.
  intros sg pointer name acquired id group image drained drained_image Himage Htype Hgroup Habort Hdrained.
  exists image; split; [exact Himage|].
  unfold flag_del_valid_option; rewrite Htype; cbn.
  exists id, group, drained, drained_image; repeat split; assumption || reflexivity.
Qed.

Lemma flag_del_prefix_safe_continuation : forall environment critical sg caller mask view pointer opt name
  before result scheduled returned current X,
  flag_del_prefix_program environment critical sg caller mask view pointer opt name
    before ((result, scheduled), returned) current ->
  flag_del_safe environment critical sg caller mask view pointer opt name before X ->
  safeExec (fun state => state = current)
    (flag_del_tail_program environment critical sg mask ((result, scheduled), returned)) X.
Proof.
  intros environment critical sg caller mask view pointer opt name before result scheduled returned current X Hprefix Hsafe.
  eapply (highstepbind_derive
    (flag_del_prefix_program environment critical sg caller mask view pointer opt name)
    (flag_del_tail_program environment critical sg mask)
    (fun state => state = before) ((result, scheduled), returned) (fun state => state = current)).
  - intros state ->; exists current; split; [exact Hprefix|reflexivity].
  - exact Hsafe.
Qed.

Lemma flag_del_no_schedule_safe_return : forall environment critical sg caller mask view pointer opt name
  before result returned current X,
  flag_del_prefix_program environment critical sg caller mask view pointer opt name
    before ((result, false), returned) current ->
  flag_del_safe environment critical sg caller mask view pointer opt name before X ->
  flag_del_return_safe current result X.
Proof.
  intros; exact (flag_del_prefix_safe_continuation environment critical sg caller mask view pointer opt name
    before result false returned current X H H0).
Qed.

Lemma flag_del_schedule_safe_return : forall environment critical sg caller mask before returned current result X,
  task_suspend_schedule_program environment critical sg caller mask before returned current ->
  safeExec (fun state => state = before)
    (StateRelMonad.bind (task_suspend_schedule_program environment critical sg caller mask)
      (fun _ => StateRelMonad.ret result)) X ->
  flag_del_return_safe current result X.
Proof.
  intros environment critical sg caller mask before returned current result X Hstep Hsafe.
  eapply (highstepbind_derive (task_suspend_schedule_program environment critical sg caller mask)
    (fun _ => StateRelMonad.ret result) (fun state => state = before) returned
    (fun state => state = current)).
  - intros state ->; exists current; split; [exact Hstep|reflexivity].
  - exact Hsafe.
Qed.

(** A returned error or pointer is tied to the actual Restore endpoint.
    Restoring resources does not preserve the acquired live generation. *)

Lemma flag_del_waiter_coverage : forall sg tasks flags active node waiter,
  task_flag_waiter_consistency sg tasks flags -> flags.(flagWaitNodes) node = Some waiter ->
  task_stack_live_coverage tasks active ->
  active = Some (waiter.(flagTask), waiter.(flagTaskGeneration)) \/
  exists region fragments, tasks.(parkedTaskStacks) (waiter.(flagTask), waiter.(flagTaskGeneration)) =
    Some (region, fragments).
Proof.
  intros sg tasks flags active node waiter Hconsistent Hnode Hcoverage.
  destruct (task_flag_waiter_has_live_generation sg tasks flags node waiter Hconsistent Hnode)
    as [task [Htask Hgeneration]].
  specialize (Hcoverage _ _ Htask); rewrite Hgeneration in Hcoverage; exact Hcoverage.
Qed.

Lemma flag_del_other_waiter_parked : forall sg tasks flags active node waiter,
  task_flag_waiter_consistency sg tasks flags -> flags.(flagWaitNodes) node = Some waiter ->
  task_stack_live_coverage tasks active ->
  active <> Some (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  exists region fragments, tasks.(parkedTaskStacks) (waiter.(flagTask), waiter.(flagTaskGeneration)) =
    Some (region, fragments).
Proof.
  intros; destruct (flag_del_waiter_coverage sg tasks flags active node waiter H H0 H1); [contradiction|assumption].
Qed.

(** Exact interfaces at the local-predicate conversion.  Some-call identity
    makes the ordinary callable map compatible; a None entry discards the
    new receipt.  These equalities do not assert that a real waiter has a
    None descriptor, nor infer Some from the initial-frame comment. *)
Lemma flag_del_continuation_local_some : forall original receipt local descriptor call,
  descriptor.(armv7a_continuation_call) = Some call ->
  flag_continuation_local_node original receipt (task_create_continuation_local local) descriptor =
  task_create_continuation_local (flag_continuation_local_node original receipt local) descriptor.
Proof.
  intros; unfold flag_continuation_local_node, task_create_continuation_local.
  rewrite H; destruct task_stack_key_eq_dec; reflexivity.
Qed.

Lemma flag_del_continuation_local_none : forall original receipt local descriptor,
  task_stack_key descriptor.(armv7a_continuation_stack) = task_stack_key original ->
  descriptor.(armv7a_continuation_call) = None ->
  flag_continuation_local_node original receipt (task_create_continuation_local local) descriptor = emp ** receipt /\
  task_create_continuation_local (flag_continuation_local_node original receipt local) descriptor = emp.
Proof.
  intros; unfold flag_continuation_local_node, task_create_continuation_local.
  rewrite H0; destruct task_stack_key_eq_dec; [split; reflexivity|contradiction].
Qed.

(** This is the real post-Next publication cut: first reassemble the borrowed
    Next field, then use the already existing originating task/generation
    entry.  No statement manufactures the receipt from global node absence. *)
Lemma flag_del_fields_next_read_publish : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg post node waiter original local fragments,
  waiter.(flagNodeAddr) = node -> post.(FlagState).(flagWaitNodes) node = None ->
  task_stack_key original = (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  post.(TskState).(parkedTaskStacks) (task_stack_key original) = Some (original.(stackLeaseRegion), fragments) ->
  waiter.(flagNodeAddr) # Ptr |-> waiter.(flagWaitImage).(flagNodeNext) **
    flag_node_fields_rep_without_next sg.(osKernelConfig) waiter.(flagNodeAddr) waiter.(flagWaitImage) **
    store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
      post.(TskState).(parkedTaskStacks) |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi post.(TskState)
      (flag_continuation_local_node original (flag_pend_sched_node_fields_rep sg node post) local))
    post.(TskState).(parkedTaskStacks).
Proof.
  intros; sep_apply_l_atomic (flag_node_fields_return_loan_merge_next sg waiter).
  sep_apply_l_atomic (flag_wake_fields_publish_returned_node external platform port abi sg post node waiter original local
    fragments H H0 H1 H2); entailer!.
Qed.


(** Adapt only the frozen Scheduler's unit result.  The user's SAME X
    observes Del's already determined pointer/error pair at the actual
    Scheduler endpoint, including every intervening state change. *)

Lemma flag_del_live_head_empty : forall sg flags id group image,
  valid_flag_state sg flags -> flags.(flagUsed) id = Some group ->
  flags.(flagImages) id = Some image ->
  (image.(flagImageHead) = 0 <-> group.(flagWaitOrder) = []).
Proof.
  intros sg flags id group image [_ [_ [_ [Hused [_ Hnodes]]]]] Hgroup Himage.
  destruct (Hused id group Hgroup) as [_ [_ [Hwait [stored [Hstored [_ [Hhead _]]]]]]].
  rewrite Himage in Hstored; inversion Hstored; subst stored.
  split.
  - intro Hzero; destruct group.(flagWaitOrder) as [|node rest] eqn:Horder; [reflexivity|].
    destruct (Hwait [] node rest Horder) as [waiter [Hnode Hfields]].
    pose proof (proj1 (Hnodes node waiter Hnode)) as Hnonzero.
    cbn in Hhead; congruence.
  - intro Hempty; rewrite Hempty in Hhead; exact Hhead.
Qed.

Lemma flag_del_acquired_live_empty : forall sg acquired id image,
  UCOS2_state_inv sg acquired -> acquired.(FlagState).(flagImages) id = Some image ->
  image.(flagImageType) = 5 -> image.(flagImageHead) = 0 ->
  exists group, acquired.(FlagState).(flagUsed) id = Some group /\ group.(flagWaitOrder) = [].
Proof.
  intros sg acquired id image Hinv Himage Htype Hhead.
  destruct (flag_query_state_configuration sg acquired Hinv) as [_ [_ Hflags]].
  destruct (flag_name_set_pool_type_is_live sg acquired.(FlagState) id image Hflags Himage Htype)
    as [group Hgroup]; exists group; split; [exact Hgroup|].
  apply (proj1 (flag_del_live_head_empty sg acquired.(FlagState) id group image Hflags Hgroup Himage)); exact Hhead.
Qed.

Lemma flag_del_protected_always_empty : forall sg pointer name acquired id group image,
  acquired.(FlagState).(flagImages) id = Some image -> image.(flagImageType) = 5 -> image.(flagImageHead) = 0 ->
  acquired.(FlagState).(flagUsed) id = Some group -> group.(flagWaitOrder) = [] ->
  flag_del_protected sg (FlagQueryPool id) pointer 1 name acquired
    (flag_del_observation 0 OS_ERR_NONE, false) (flag_del_release_state sg acquired id image name).
Proof.
  intros sg pointer name acquired id group image Himage Htype Hhead Hgroup Hempty.
  pose proof (flag_del_protected_always sg pointer name acquired id group image acquired image
    Himage Htype Hgroup ltac:(rewrite Hempty; reflexivity) Himage) as Hstep.
  rewrite Hhead in Hstep; exact Hstep.
Qed.

Lemma flag_del_fields_task_rdy_split_next : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg before node waiter old returned local,
  UCOS2_state_inv sg before -> flag_task_rdy_domain sg before node waiter old 0 ->
  flag_task_rdy_fields_post sg before node waiter 0 PendAbort returned **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg before **
    store_parked_continuations (kernel_saved_continuation_entry abi before.(TskState) local)
      before.(TskState).(parkedTaskStacks) |--
  EX post, EX schedule,
    coq_prop (flag_task_rdy sg before node 0 PendAbort = Some (schedule, post) /\
      returned = (if schedule then 1 else 0)) &&
    (UCOS2_fields_inv sg post **
     waiter.(flagNodeAddr) # Ptr |-> waiter.(flagWaitImage).(flagNodeNext) **
     flag_node_fields_rep_without_next sg.(osKernelConfig) waiter.(flagNodeAddr) waiter.(flagWaitImage) **
     store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
       post.(TskState).(parkedTaskStacks)).
Proof.
  intros; sep_apply_l_atomic (flag_wake_fields_returns_node_with_continuation_map external platform port
    abi sg before node waiter old 0 PendAbort returned local H H0).
  Intros post schedule; sep_apply_l_atomic (flag_node_fields_return_loan_split_next sg waiter).
  Exists post schedule; entailer!.
Qed.


Lemma flag_del_abort_head : forall sg before id group node rest,
  UCOS2_state_inv sg before -> before.(FlagState).(flagUsed) id = Some group ->
  group.(flagWaitOrder) = node :: rest ->
  exists waiter schedule after,
    before.(FlagState).(flagWaitNodes) node = Some waiter /\
    waiter.(flagWaitImage).(flagNodeNext) = hd 0 rest /\
    flag_task_rdy sg before node 0 PendAbort = Some (schedule, after) /\
    UCOS2_state_inv sg after /\
    after.(FlagState).(flagUsed) id = Some (flag_group_set_wait_order group rest).
Proof.
  intros sg before id group node rest Hinv Hgroup Horder.
  destruct (flag_query_state_configuration sg before Hinv) as [Henabled [Hbits Hflags]].
  pose proof Hflags as [_ [_ [_ [Hgroups [_ Hnodes]]]]].
  destruct (Hgroups id group Hgroup) as [Hgroupvalid [_ [Hwait [image [Himage Hfields]]]]].
  destruct (Hwait [] node rest Horder) as [waiter [Hwaiter [Haddr [Hid [Hgeneration [Hnodegroup
    [Hprev [Hnext Hother]]]]]]]].
  assert (Hconsistent : task_flag_waiter_consistency sg before.(TskState) before.(FlagState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, cross_module_consistency in Hinv; tauto. }
  assert (Hconfigured : valid_flag_configuration sg before.(FlagState)).
  { unfold valid_flag_configuration; rewrite Henabled; exact Hflags. }
  destruct (flag_task_rdy_selects_waiter sg before node waiter 0 PendAbort Hconfigured Hconsistent Hwaiter)
    as [old [flags [Hold [Htcb [Hunlink Hstep]]]]].
  pose proof (flag_unlink_group_fields before.(FlagState) node waiter flags group image Hunlink
    ltac:(rewrite Hid; exact Hgroup) ltac:(rewrite Hid; exact Himage)) as [Hused Hrest].
  assert (Hnot : ~ In node rest).
  { destruct Hgroupvalid as [_ Hnodup]; rewrite Horder in Hnodup; inversion Hnodup; assumption. }
  assert (Hremove : remove Z.eq_dec node rest = rest).
  { apply notin_remove; exact Hnot. }
  assert (Hremoved : remove Z.eq_dec node group.(flagWaitOrder) = rest).
  { rewrite Horder; cbn; destruct (Z.eq_dec node node); [exact Hremove|contradiction]. }
  exists waiter, (Z.eqb (encode_task_status (task_flag_wake old 0 PendAbort).(stat)) 0),
    (flag_wake_state sg before waiter flags old 0 PendAbort).
  split; [exact Hwaiter|]. split; [exact Hnext|]. split; [exact Hstep|]. split.
  - eapply UCOS2_flag_task_rdy_preserves_validity; eassumption.
  - change (flags.(flagUsed) id = Some (flag_group_set_wait_order group rest)).
    rewrite Hused, Hid, Hremoved, kernel_map_set_same; reflexivity.
Qed.

Lemma flag_del_abort_waiters_total : forall sg nodes before id group,
  UCOS2_state_inv sg before -> before.(FlagState).(flagUsed) id = Some group ->
  group.(flagWaitOrder) = nodes ->
  exists after remaining,
    flag_del_abort_waiters sg nodes before = Some after /\ UCOS2_state_inv sg after /\
    after.(FlagState).(flagUsed) id = Some remaining /\ remaining.(flagWaitOrder) = [].
Proof.
  intros sg nodes; induction nodes as [|node rest IH]; intros before id group Hinv Hgroup Horder.
  - exists before, group; split; [reflexivity|].
    split; [exact Hinv|]. split; assumption.
  - destruct (flag_del_abort_head sg before id group node rest Hinv Hgroup Horder)
      as [waiter [schedule [next [Hwaiter [Hnext [Hstep [Hvalid Hgroupnext]]]]]]].
    destruct (IH next id (flag_group_set_wait_order group rest) Hvalid Hgroupnext eq_refl)
      as [after [remaining [Habort [Hafter [Hremaining Hempty]]]]].
    exists after, remaining; split.
    + cbn; rewrite Hstep; exact Habort.
    + auto.
Qed.

Lemma flag_del_protected_always_has_result : forall sg pointer name acquired id image,
  UCOS2_state_inv sg acquired -> acquired.(FlagState).(flagImages) id = Some image ->
  image.(flagImageType) = 5 ->
  exists released,
    flag_del_protected sg (FlagQueryPool id) pointer 1 name acquired
      (flag_del_observation 0 OS_ERR_NONE, negb (Z.eqb image.(flagImageHead) 0)) released /\
    UCOS2_state_inv sg released.
Proof.
  intros sg pointer name acquired id image Hinv Himage Htype.
  destruct (flag_query_state_configuration sg acquired Hinv) as [_ [_ Hflags]].
  destruct (flag_name_set_pool_type_is_live sg acquired.(FlagState) id image Hflags Himage Htype)
    as [group Hgroup].
  destruct (flag_del_abort_waiters_total sg group.(flagWaitOrder) acquired id group Hinv Hgroup eq_refl)
    as [drained [remaining [Habort [Hvalid [Hremaining Hempty]]]]].
  destruct (flag_query_state_configuration sg drained Hvalid) as [_ [_ Hdrainedflags]].
  destruct Hdrainedflags as [_ [_ [_ [Hused _]]]].
  destruct (Hused id remaining Hremaining) as [_ [_ [_ [drained_image [Hdrainedimage Hfields]]]]].
  exists (flag_del_release_state sg drained id drained_image name); split.
  - eapply flag_del_protected_always; eassumption.
  - eapply flag_del_release_preserves_state_inv; eassumption.
Qed.


(** This is the result-cell boundary after the source's actual *perr store.
    A caller frame, including any separately owned raw type-error input,
    stays on this endpoint.  It is not an ownership producer for that store. *)

Lemma flag_del_fields_task_rdy_call_next : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg before node waiter old returned local
  (frame : Assertion) heap_before heap_after,
  UCOS2_state_inv sg before -> flag_task_rdy_domain sg before node waiter old 0 ->
  flag_pend_sched_fields_task_rdy_call sg node 0 PendAbort returned heap_before heap_after ->
  (flag_task_rdy_fields_pre sg before node waiter old 0 **
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg before **
     store_parked_continuations (kernel_saved_continuation_entry abi before.(TskState) local)
       before.(TskState).(parkedTaskStacks) ** frame)) heap_before ->
  (EX post, EX schedule,
    coq_prop (flag_task_rdy sg before node 0 PendAbort = Some (schedule, post) /\
      returned = (if schedule then 1 else 0)) &&
    (UCOS2_fields_inv sg post **
     waiter.(flagNodeAddr) # Ptr |-> waiter.(flagWaitImage).(flagNodeNext) **
     flag_node_fields_rep_without_next sg.(osKernelConfig) waiter.(flagNodeAddr) waiter.(flagWaitImage) **
     store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
       post.(TskState).(parkedTaskStacks) ** frame)) heap_after.
Proof.
  intros external platform port abi sg before node waiter old returned local frame heap_before heap_after
    Hvalid Hdomain Hcall Hheap.
  specialize (Hcall before waiter old
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg before **
     store_parked_continuations (kernel_saved_continuation_entry abi before.(TskState) local)
       before.(TskState).(parkedTaskStacks) ** frame) Hheap).
  match type of Hcall with ?P heap_after => match goal with |- ?Q heap_after =>
    assert (Hresource : P |-- Q) end end.
  { sep_apply_l_atomic (flag_del_fields_task_rdy_split_next external platform port abi sg before node waiter old
      returned local Hvalid Hdomain).
    Intros post schedule; Exists post schedule; entailer!. }
  exact (Hresource heap_after Hcall).
Qed.


(** Actual TCB initialization clears this flag-node field.  Del only
    needs that field to exclude an active waiter at the caller's own key;
    event-pointer cleanliness is not required.  This does not claim that
    the field survives an arbitrary subsequent API. *)
Definition flag_del_application_task_clean (node : TaskAbstractState) : Prop :=
  node.(tcbFlagNode) = 0.

Lemma flag_del_initial_node_clean : forall args acquired slot image,
  flag_del_application_task_clean (task_tcb_init_commit_node args acquired slot image).
Proof. intros; repeat split; reflexivity. Qed.

(** This candidate task-entry slice is intentionally stronger than the old
    arbitrary current-task premise.  The initial/previous-return source
    producers must furnish it; merely being ready is insufficient.  ISR and
    boot/disabled views are separate actual caller variants and are not
    ruled out by this task-only definition. *)
Definition flag_del_task_application_entry (call : OsSchedCallContext)
  (state : UCOS2_Verify_State) : Prop :=
  kernel_call_task_source call state /\
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None /\
  exists node,
    state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) /\
    flag_del_application_task_clean node.

Lemma flag_del_task_entry_waiter_other_key : forall sg call state p waiter,
  flag_del_task_application_entry call state ->
  task_flag_waiter_consistency sg state.(TskState) state.(FlagState) ->
  state.(FlagState).(flagWaitNodes) p = Some waiter ->
  task_stack_key call.(os_sched_call_stack) <>
    (waiter.(flagTask), waiter.(flagTaskGeneration)).
Proof.
  intros sg call state p waiter [_ [_ [node [Hnode [_ Hclean]]]]] Hconsistent Hwaiter Hkey.
  assert (Hslot : waiter.(flagTask) = call.(os_sched_call_stack).(stackLeaseSlot)).
  { unfold task_stack_key in Hkey; inversion Hkey; reflexivity. }
  eapply (task_flag_null_pointer_has_no_waiter sg state.(TskState) state.(FlagState)
    call.(os_sched_call_stack).(stackLeaseSlot) node Hconsistent Hnode Hclean).
  exists p, waiter; auto.
Qed.

Lemma flag_del_task_entry_waiter_parked : forall sg call state p waiter,
  flag_del_task_application_entry call state ->
  task_flag_waiter_consistency sg state.(TskState) state.(FlagState) ->
  state.(FlagState).(flagWaitNodes) p = Some waiter ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  exists region fragments,
    state.(TskState).(parkedTaskStacks) (waiter.(flagTask), waiter.(flagTaskGeneration)) =
      Some (region, fragments).
Proof.
  intros sg call state p waiter Hentry Hconsistent Hwaiter Hcoverage.
  eapply flag_del_other_waiter_parked; [exact Hconsistent|exact Hwaiter|exact Hcoverage|].
  intro Heq.
  apply (flag_del_task_entry_waiter_other_key sg call state p waiter Hentry Hconsistent Hwaiter).
  congruence.
Qed.

(** The complete source segment consumes the checked fields helper, then
    the actual pointer read/assignment, then deposits the SAME node loan.
    It retains the returned Boolean even though Del ignores it. *)
Lemma flag_del_fields_abort_next_publish : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state node waiter old returned
  original local fragments pnode (frame : Assertion) before middle after observed,
  UCOS2_state_inv sg state -> flag_task_rdy_domain sg state node waiter old 0 ->
  waiter.(flagNodeAddr) = node ->
  task_stack_key original = (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original) =
    Some (original.(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg node 0 PendAbort returned before middle ->
  flag_source_next_assignment pnode node observed middle after ->
  (flag_task_rdy_fields_pre sg state node waiter old 0 **
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
     store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
       state.(TskState).(parkedTaskStacks) ** (pnode # Ptr |-> node ** frame))) before ->
  exists post schedule,
    flag_task_rdy sg state node 0 PendAbort = Some (schedule, post) /\
    returned = (if schedule then 1 else 0) /\
    observed = waiter.(flagWaitImage).(flagNodeNext) /\
    (pnode # Ptr |-> observed ** UCOS2_fields_inv sg post **
     store_parked_continuations
       (kernel_saved_continuation_entry abi post.(TskState)
         (flag_continuation_local_node original (flag_pend_sched_node_fields_rep sg node post) local))
       post.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros; eapply flag_source_fields_task_rdy_next_publish; eassumption.
Qed.

(** Actual public C resource cuts. The local family is arbitrary, including
    receipts at descriptors without a saved C call. *)
Definition flag_del_active_key (caller : TaskSuspendCaller) : option (TaskID * nat) :=
  match caller with
  | TaskSuspendTask call => task_stack_call_active_key call
  | TaskSuspendDisabled _ => None
  end.

Definition flag_del_context environment (caller : TaskSuspendCaller) : Assertion :=
  match caller with
  | TaskSuspendTask call => os_sched_context_resources environment.(task_stack_call_external) call
  | TaskSuspendDisabled view => os_execution_view_resources environment.(task_stack_call_external) view
  end.

Definition flag_del_closed environment local sg caller mask state : Assertion :=
  interrupt_platform_running environment.(task_stack_call_platform)
    (task_suspend_view caller).(os_execution_invocation)
    (task_suspend_view caller).(os_execution_origin) mask **
  flag_del_context environment caller **
  kernel_continuation_inv environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg (flag_del_active_key caller) state.

Definition flag_del_masked environment critical local sg caller saved acquired state : Assertion :=
  critical_region_masked environment.(task_stack_call_platform) critical sg
    (task_suspend_view caller).(os_execution_invocation)
    (task_suspend_view caller).(os_execution_origin) saved acquired **
  flag_del_context environment caller **
  kernel_continuation_inv environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg (flag_del_active_key caller) state.

(** The fixed port executes boot handlers without incrementing
    OSIntNesting.  Their execution view is still an interrupt, and the
    initialized boot source keeps the no-waiter property. *)
Definition flag_del_boot_handler_source (view : OsExecutionView) (state : UCOS2_Verify_State) : Prop :=
  exists handler interrupted,
    view.(os_execution_context) = KernelInterrupt handler interrupted /\
    view.(os_execution_origin) = BootInvocation /\
    state.(SchedState).(isRunning) = false /\
    state.(IntrState).(intNesting) = 0 /\
    flag_state_has_no_waiters state.(FlagState).

Definition flag_del_handler_source view state : Prop :=
  sched_disabled_isr_source view state \/ flag_del_boot_handler_source view state.

Definition flag_del_call_cut (sg : StableGlobVars) caller state : Prop :=
  match caller with
  | TaskSuspendTask call =>
      match call.(os_sched_call_origin) with
      | BootInvocation => state.(SchedState).(isRunning) = false
      | RunningInvocation _ _ => state.(SchedState).(isRunning) = true /\ flag_del_task_application_entry call state
      end
  | TaskSuspendDisabled view => flag_del_handler_source view state
  end.

(** Static interpretation of the selected timer-v2.93.01 ARM32 build.
    This binds the actual configuration record and the existing Unlink alias
    field interpretation; it places no condition on a runtime state or option. *)
Definition flag_del_build_context (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig) = selected_kernel_configuration /\ flag_unlink_layout.

Lemma flag_del_build_configuration : forall sg,
  flag_del_build_context sg -> sg.(osKernelConfig) = selected_kernel_configuration.
Proof. intros sg [Hconfig _]; exact Hconfig. Qed.

Lemma flag_del_build_flag_names : forall sg,
  flag_del_build_context sg -> sg.(osKernelConfig).(cfgFlagNames) = true.
Proof. intros sg [Hconfig _]; rewrite Hconfig; reflexivity. Qed.

Lemma flag_del_build_unlink_layout : forall sg,
  flag_del_build_context sg -> flag_unlink_layout.
Proof. intros sg [_ Hlayout]; exact Hlayout. Qed.

Lemma flag_del_build_node_next_address : forall sg node,
  flag_del_build_context sg -> &(node # "os_flag_node" ->ₛ "OSFlagNodeNext") = node.
Proof. intros sg node [_ [Hnext _]]; apply Hnext. Qed.

Definition flag_del_layout (p : addr) : Prop :=
  (&(p # "os_flag_grp" ->ₛ "OSFlagType")) = p /\
  (&(p # "os_flag_grp" ->ₛ "OSFlagWaitList")) = p + 4 /\
  (&(p # "os_flag_grp" ->ₛ "OSFlagFlags")) = p + 8 /\
  (&(p # "os_flag_grp" ->ₛ "OSFlagName")) = p + 12.

Definition flag_del_raw_type (p : addr) (view : FlagQueryView) : Assertion :=
  if Z.eqb p 0 then emp else
  match view with
  | FlagQueryRaw image => p # UChar |-> image.(flagImageType)
  | FlagQueryPool _ => emp
  end.

(** Invalid raw types keep their original caller-owned byte. A live flag
    object is always a real fixed pool slot, without a generation lock. *)
Definition flag_del_argument sg p view before observed : Prop :=
  p = 0 \/ (p <> 0 /\ flag_del_layout p /\
  flag_query_address sg p view /\ flag_query_selected view before observed /\
  match view with
    | FlagQueryRaw image => image.(flagImageType) <> 5
    | FlagQueryPool _ => True
    end).

Definition flag_del_type_frame sg p view state (image : FlagGroupImage) : Assertion :=
  match view with
  | FlagQueryRaw _ => kernel_program_fields_inv sg state
  | FlagQueryPool id =>
      flag_query_group_without_type sg p image **
      sg.(g_OSFlagFreeList) # Ptr |-> flag_del_free_head sg state.(FlagState) **
      flag_del_pool_fields_frame sg state id ** unmap_table_rep sg
  end.

Definition flag_del_type_cut environment local sg caller mask p view state image : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\
  task_stack_live_coverage state.(TskState) (flag_del_active_key caller)) &&
  (interrupt_platform_running environment.(task_stack_call_platform)
     (task_suspend_view caller).(os_execution_invocation)
     (task_suspend_view caller).(os_execution_origin) mask **
   flag_del_context environment caller **
   p # UChar |-> image.(flagImageType) ** flag_del_type_frame sg p view state image **
   os_sched_fields_capsules environment local state).

Definition flag_del_masked_type_cut environment critical local sg caller saved acquired
    p id state image : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\
  task_stack_live_coverage state.(TskState) (flag_del_active_key caller)) &&
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     (task_suspend_view caller).(os_execution_invocation)
     (task_suspend_view caller).(os_execution_origin) saved acquired **
   flag_del_context environment caller **
   p # UChar |-> image.(flagImageType) **
   flag_del_type_frame sg p (FlagQueryPool id) state image **
   os_sched_fields_capsules environment local state).

Definition flag_del_group_cut environment critical local sg caller saved acquired
    p id state image : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\
  task_stack_live_coverage state.(TskState) (flag_del_active_key caller)) &&
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     (task_suspend_view caller).(os_execution_invocation)
     (task_suspend_view caller).(os_execution_origin) saved acquired **
   flag_del_context environment caller **
   p # UChar |-> image.(flagImageType) **
   (p + 4) # Ptr |-> image.(flagImageHead) **
   (p + 8) # UShort |-> image.(flagImageBits) **
   (p + 12) # Ptr |-> image.(flagImageName) ** flag_del_group_padding p image **
   sg.(g_OSFlagFreeList) # Ptr |-> flag_del_free_head sg state.(FlagState) **
   flag_del_pool_fields_frame sg state id ** unmap_table_rep sg **
   os_sched_fields_capsules environment local state).

Definition flag_del_save_post environment critical local sg original mask before saved : Assertion :=
  EX active acquired,
    coq_prop (task_suspend_save_effect environment critical sg original active mask saved before acquired /\
  task_suspend_same_call active original /\ interrupt_saved_value mask saved /\
  flag_del_call_cut sg active acquired) &&
    flag_del_masked environment critical local sg active saved acquired acquired.

(** These paired external contracts are used only by the actual Save and
    Restore calls. The C environment must supply their source observations
    and the SAME normal-return heap endpoints. Retirement/nonreturn is not
    excluded. The body establishes its protected state separately. *)
Definition flag_del_restore_cut sg active state (schedule : bool) : Prop :=
  flag_del_call_cut sg active state /\
  (schedule = true ->
    match active with
    | TaskSuspendTask call => os_sched_call_cut sg call state
    | TaskSuspendDisabled view => sched_disabled_entry_source view state
    end).

Definition flag_del_restore_post environment critical local sg active saved released (schedule : bool) : Assertion :=
  EX returned current,
    coq_prop (task_suspend_restore_effect environment critical sg active returned released current /\
  task_suspend_same_call returned active /\
  flag_del_call_cut sg returned current /\
  (schedule = true -> match returned with
      | TaskSuspendTask call => os_sched_call_cut sg call current
      | TaskSuspendDisabled view => sched_disabled_entry_source view current
      end)) &&
    flag_del_closed environment local sg returned (armv7a_irq_fiq_mask saved) current.

Definition flag_del_return_cut environment local sg original returned mask p view
    current (result : Z * Z) (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Assertion :=
  coq_prop (task_suspend_same_call returned original /\ flag_del_return_safe current result X) &&
  (flag_del_closed environment local sg returned mask current ** flag_del_raw_type p view).

Lemma flag_del_fields_scheduler_pre : forall environment local sg call mask state,
  os_sched_call_cut sg call state ->
  flag_del_closed environment local sg (TaskSuspendTask call) mask state |--
  os_sched_fields_call_pre environment local kernel_program_fields_inv sg call mask state.
Proof.
  intros; unfold flag_del_closed, flag_del_context, flag_del_active_key, task_suspend_view,
    os_sched_execution_view, os_sched_fields_call_pre, os_sched_fields_pre,
    kernel_continuation_call_closed, kernel_call_execution_owned; entailer!.
Qed.

Lemma flag_del_fields_scheduler_return : forall environment critical local sg call mask before
    result X,
  safeExec (fun state => state = before)
    (StateRelMonad.bind (task_suspend_schedule_program environment critical sg
      (TaskSuspendTask call) mask) (fun _ => StateRelMonad.ret result)) X ->
  os_sched_fields_history_return_post environment critical local kernel_program_fields_inv sg call mask before |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned call /\ flag_del_return_safe current result X) &&
    flag_del_closed environment local sg (TaskSuspendTask returned) mask current.
Proof.
  intros environment critical local sg call mask before result X Hsafe.
  unfold os_sched_fields_history_return_post; Intros returned current.
  assert (Hhistory : os_sched_continuation_call_history environment critical sg
      call mask before returned current) by tauto.
  assert (Hstep : task_suspend_schedule_program environment critical sg
      (TaskSuspendTask call) mask before (TaskSuspendTask returned) current).
  { cbn [task_suspend_schedule_program].
    exists returned, current; split.
    - apply os_sched_continuation_program_iff; exact Hhistory.
    - split; reflexivity. }
  pose proof (flag_del_schedule_safe_return environment critical sg
    (TaskSuspendTask call) mask before (TaskSuspendTask returned) current result X Hstep Hsafe) as Hreturn.
  Exists returned current.
  unfold flag_del_closed, flag_del_context, flag_del_active_key, task_suspend_view,
    os_sched_execution_view, kernel_continuation_call_closed, kernel_call_execution_owned; entailer!.
Qed.

Definition flag_del_nesting_frame environment local sg caller mask state : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\
    task_stack_live_coverage state.(TskState) (flag_del_active_key caller)) &&
  (interrupt_platform_running environment.(task_stack_call_platform)
     (task_suspend_view caller).(os_execution_invocation)
     (task_suspend_view caller).(os_execution_origin) mask **
   flag_del_context environment caller **
   sg.(g_OSLockNesting) # UChar |-> state.(IntrState).(lockNesting) **
   flag_fields_configured_rep sg state.(FlagState) **
   UCOS2_raw_rep_missing_two sg state FlagModule InterruptModule **
   unmap_table_rep sg ** os_sched_fields_capsules environment local state).

Definition flag_del_prefix_facts environment critical sg caller mask view pointer opt name before
    observed active saved acquired (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Prop :=
  pointer <> 0 /\ os_sched_ints before = 0 /\
  flag_query_selected view before observed /\ observed.(flagImageType) = 5 /\
  task_suspend_save_effect environment critical sg caller active mask saved before acquired /\
  task_suspend_same_call active caller /\ interrupt_saved_value mask saved /\
  flag_del_safe environment critical sg caller mask view pointer opt name before X.

Definition flag_del_waiting (image : FlagGroupImage) : Z :=
  if Z.eqb image.(flagImageHead) 0 then 0 else 1.

Definition flag_del_loop_facts sg caller acquired id original
    (visited remaining : list addr) current (pnode : addr) : Prop :=
  original = visited ++ remaining /\
  flag_del_abort_waiters sg visited acquired = Some current /\
  (exists group, current.(FlagState).(flagUsed) id = Some group /\
     group.(flagWaitOrder) = remaining) /\
  pnode = (match remaining with [] => 0 | node :: _ => node end) /\
  flag_del_call_cut sg caller current.

(** Preserve the coverage already owned by the masked continuation world.
    TaskRdy changes the selected task but retains its generation and the parked
    map; the next cut transports this fact through that actual step. *)
Definition flag_del_iteration_frame environment critical local sg caller saved acquired state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState) (flag_del_active_key caller)) &&
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     (task_suspend_view caller).(os_execution_invocation)
     (task_suspend_view caller).(os_execution_origin) saved acquired **
   flag_del_context environment caller **
   UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
   os_sched_fields_capsules environment local state ** unmap_table_rep sg).

Definition flag_del_iteration_next environment critical local sg caller saved acquired
    post node waiter : Assertion :=
  coq_prop (UCOS2_state_inv sg post /\
    task_stack_live_coverage post.(TskState) (flag_del_active_key caller)) &&
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     (task_suspend_view caller).(os_execution_invocation)
     (task_suspend_view caller).(os_execution_origin) saved acquired **
   flag_del_context environment caller **
   UCOS2_fields_inv sg post **
   node # Ptr |-> waiter.(flagWaitImage).(flagNodeNext) **
   flag_node_fields_rep_without_next sg.(osKernelConfig) node waiter.(flagWaitImage) **
   os_sched_fields_capsules environment local post ** unmap_table_rep sg).

Definition flag_del_published_local sg post node (waiter : FlagWaiterState) original local :=
  flag_continuation_local_node original (flag_pend_sched_node_fields_rep sg node post) local.

Lemma flag_del_fields_begin_invocation : forall sg state origin,
  task_invocation_origin_live state.(TskState) origin ->
  UCOS2_fields_inv sg state |--
  UCOS2_fields_inv sg (replace_TskS (task_begin_invocation origin state.(TskState)) state).
Proof.
  intros sg state origin Horigin; unfold UCOS2_fields_inv; Intros.
  pose proof (UCOS2_begin_task_invocation_preserves_validity sg state origin H Horigin) as Hvalid.
  assert (Hraw : UCOS2_fields_raw_rep sg
    (replace_TskS (task_begin_invocation origin state.(TskState)) state) =
    UCOS2_fields_raw_rep sg state).
  { unfold UCOS2_fields_raw_rep; f_equal.
    unfold UCOS2_raw_rep_missing_flag.
    apply UCOS2_raw_rep_missing_module_frame; intros module Hmodule.
    destruct module; try reflexivity.
    - symmetry; apply sched_raw_rep_change_task_index; reflexivity.
    - symmetry; apply event_raw_rep_change_task_index.
      apply event_wait_priority_agreement_encodes.
      unfold event_wait_priority_agreement; intros; reflexivity. }
  rewrite Hraw; entailer!.
Qed.

(** The initial endpoint owns the real restored initial descriptor and the
    partition used by the first C invocation. Its current/live, taken-key and
    clean facts are supplied by initialization/publication and selection,
    not inferred from readiness or an arbitrary world. *)
Lemma flag_del_initial_fields_owner : forall environment
  (entry : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations)) sg state saved fragments local,
  armv7a_initial_frame_binding saved ->
  task_stack_fragments_in_range
    saved.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0 fragments ->
  task_current_at state saved.(armv7a_continuation_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  UCOS2_fields_inv sg state ** armv7a_initial_execution environment.(task_stack_call_continuations) saved **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion) fragments **
    os_sched_fields_capsules environment local state |--
  let call := armv7a_initial_call saved state.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
  let registered := armv7a_initial_call_registered saved state in
  coq_prop (kernel_call_task_source call registered) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) call (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
     UCOS2_fields_inv sg registered ** os_sched_fields_capsules environment local registered).
Proof.
  intros environment entry sg state saved fragments local Hbinding Hfragments Hcurrent.
  cbv zeta.
  destruct (task_current_at_begin_invocation state
    saved.(armv7a_continuation_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_stack).(stackLeaseGeneration) Hcurrent) as [Hcurrent' Hactive].
  sep_apply_l_atomic (flag_del_fields_begin_invocation sg state
    (RunningInvocation saved.(armv7a_continuation_stack).(stackLeaseSlot)
      saved.(armv7a_continuation_stack).(stackLeaseGeneration)) (proj2 Hcurrent)).
  sep_apply_l_atomic (armv7a_initial_call_resources _ _ _
    environment.(task_stack_call_continuations) entry saved
    state.(TskState).(taskLifecycle).(taskNextInvocation) fragments Hbinding Hfragments).
  unfold kernel_call_task_source, armv7a_initial_call_registered, armv7a_initial_call,
    kernel_call_execution_owned, os_sched_context_resources, os_sched_fields_capsules.
  entailer!.
  exact (proj1 Hcurrent').
Qed.

Definition flag_del_schedule_bit (waiting : Z) : bool := Z.eqb waiting 1.
Definition flag_del_rechecked (option : Z) (image : FlagGroupImage) : Prop :=
  (option = 0 \/ option = 1) -> image.(flagImageType) = 5.
Definition flag_del_acquired_group state id image (order : list addr) : Prop :=
  state.(FlagState).(flagImages) id = Some image /\ image.(flagImageType) = 5 /\
  exists group, state.(FlagState).(flagUsed) id = Some group /\ group.(flagWaitOrder) = order.
Definition flag_del_step sg before node after : Prop :=
  exists ready, flag_task_rdy sg before node 0 PendAbort = Some (ready, after).

Lemma flag_del_step_preserves_stack_live_coverage : forall sg before node after active,
  flag_del_step sg before node after ->
  task_stack_live_coverage before.(TskState) active ->
  task_stack_live_coverage after.(TskState) active.
Proof.
  intros sg before node after active [ready Hstep] Hcoverage.
  destruct (FlagPendSchedulerResources.flag_task_rdy_preserves_stack_metadata
    sg before node 0 PendAbort ready after Hstep) as [Hparked Htasks].
  eapply task_stack_live_coverage_used_map_frame; [|exact Hparked|exact Hcoverage].
  intros slot current Hcurrent.
  destruct (Htasks slot current Hcurrent) as [old [Hold [Hgeneration Hsp]]].
  exists old; split; [exact Hold|symmetry; exact Hgeneration].
Qed.

Lemma flag_del_masked_split_iteration : forall environment critical local sg caller
    saved acquired state node waiter,
  flag_del_build_context sg -> state.(FlagState).(flagWaitNodes) node = Some waiter ->
  flag_del_masked environment critical local sg caller saved acquired state |--
  EX old, coq_prop (UCOS2_state_inv sg state) &&
    (flag_task_rdy_fields_pre sg state node waiter old 0 **
     flag_del_iteration_frame environment critical local sg caller saved acquired state).
Proof.
  intros environment critical local sg caller saved acquired state node waiter [Hconfig Hlayout] Hwaiter.
  unfold flag_del_masked, kernel_continuation_inv.
  rewrite kernel_program_fields_inv_split_unmap; Intros.
  sep_apply_l_atomic (flag_task_rdy_fields_stable_split sg state node waiter 0
    Hconfig Hlayout ltac:(lia) Hwaiter).
  Intros old; Exists old.
  unfold flag_del_iteration_frame, os_sched_fields_capsules; entailer!.
Qed.

Lemma flag_del_iteration_task_rdy_next : forall environment critical local sg caller
    saved acquired state node waiter old returned,
  UCOS2_state_inv sg state -> flag_task_rdy_domain sg state node waiter old 0 ->
  waiter.(flagNodeAddr) = node ->
  flag_task_rdy_fields_post sg state node waiter 0 PendAbort returned **
    flag_del_iteration_frame environment critical local sg caller saved acquired state |--
  EX post, coq_prop (flag_del_step sg state node post) &&
    flag_del_iteration_next environment critical local sg caller saved acquired post node waiter.
Proof.
  intros environment critical local sg caller saved acquired state node waiter old returned
    Hvalid Hdomain Haddress.
  unfold flag_del_iteration_frame, os_sched_fields_capsules; Intros.
  sep_apply_l_atomic (flag_del_fields_task_rdy_split_next
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    environment.(task_stack_call_port) environment.(task_stack_call_continuations)
    sg state node waiter old returned local Hvalid Hdomain).
  Intros post ready.
  assert (Hstep : flag_del_step sg state node post).
  { exists ready; tauto. }
  pose proof (flag_del_step_preserves_stack_live_coverage sg state node post
    (flag_del_active_key caller) Hstep H) as Hcoverage.
  pose proof (UCOS2_flag_task_rdy_preserves_validity sg state node 0 PendAbort
    ready post Hvalid ltac:(tauto)) as Hpost.
  Exists post; unfold flag_del_iteration_next, os_sched_fields_capsules.
  rewrite Haddress; entailer!.
Qed.

Definition flag_del_waiter_at state node waiter old : Prop :=
  state.(FlagState).(flagWaitNodes) node = Some waiter /\
  state.(TskState).(inUsedTaskStates) waiter.(flagTask) = Some old /\
  waiter.(flagNodeAddr) = node.
Definition flag_del_node_next (waiter : FlagWaiterState) : addr :=
  waiter.(flagWaitImage).(flagNodeNext).
Definition flag_del_loan_origin state waiter original fragments : Prop :=
  task_stack_key original = (waiter.(flagTask), waiter.(flagTaskGeneration)) /\
  state.(TskState).(parkedTaskStacks) (task_stack_key original) =
    Some (original.(stackLeaseRegion), fragments).
Definition flag_del_free_head_state sg state : addr := flag_del_free_head sg state.(FlagState).
Definition flag_del_protected_result sg view pointer opt name acquired result error schedule released : Prop :=
  flag_del_protected sg view pointer opt name acquired ((result, error), schedule) released.
Definition flag_del_same_task_call returned original : Prop :=
  task_suspend_same_call (TaskSuspendTask returned) original.
Definition flag_del_scheduler_safe environment critical sg context mask current (result error : Z) X : Prop :=
  safeExec (fun state => state = current)
    (StateRelMonad.bind (task_suspend_schedule_program environment critical sg
      (TaskSuspendTask context) mask) (fun _ => StateRelMonad.ret (result, error))) X.


Fixpoint flag_del_local_prefix sg (nodes : list addr) before
    (original_local : Armv7aContinuation -> Assertion) after
    (returned_local : Armv7aContinuation -> Assertion) : Prop :=
  match nodes with
  | [] => after = before /\ returned_local = original_local
  | node :: rest =>
      exists waiter lease fragments next,
        before.(FlagState).(flagWaitNodes) node = Some waiter /\
        flag_del_loan_origin before waiter lease fragments /\
        flag_del_step sg before node next /\
        flag_del_local_prefix sg rest next
          (flag_del_published_local sg next node waiter lease original_local) after returned_local
  end.

Definition flag_del_local_change environment critical sg caller mask view pointer option before
    (original_local returned_local : Armv7aContinuation -> Assertion) : Prop :=
  returned_local = original_local \/
  exists observed active saved acquired id image order drained,
    pointer <> 0 /\ os_sched_ints before = 0 /\
    flag_query_selected view before observed /\ observed.(flagImageType) = 5 /\
    task_suspend_save_effect environment critical sg caller active mask saved before acquired /\
    option = 1 /\ view = FlagQueryPool id /\
    flag_del_acquired_group acquired id image order /\
    flag_del_abort_waiters sg order acquired = Some drained /\
    flag_del_local_prefix sg order acquired original_local drained returned_local.

Definition flag_del_after_restore environment critical original_local local sg original mask view pointer option name
    before (X : (Z * Z) -> UCOS2_Verify_State -> Prop) result error schedule : Assertion :=
  EX returned current,
    coq_prop (flag_del_local_change environment critical sg original mask view pointer option before original_local local /\
      task_suspend_same_call returned original /\
      flag_del_prefix_program environment critical sg original mask view pointer option name before
        (((result, error), schedule), returned) current /\
      safeExec (fun state => state = current)
        (flag_del_tail_program environment critical sg mask (((result, error), schedule), returned)) X /\
      flag_del_call_cut sg returned current /\
      (schedule = true ->
        match returned with
        | TaskSuspendTask call => os_sched_call_cut sg call current
        | TaskSuspendDisabled view => sched_disabled_entry_source view current
        end)) &&
    (flag_del_closed environment local sg returned mask current ** flag_del_raw_type pointer view).

Definition flag_del_type_read_frame environment local sg caller mask p view state image : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\
    task_stack_live_coverage state.(TskState) (flag_del_active_key caller)) &&
  (interrupt_platform_running environment.(task_stack_call_platform)
     (task_suspend_view caller).(os_execution_invocation)
     (task_suspend_view caller).(os_execution_origin) mask **
   flag_del_context environment caller ** flag_del_type_frame sg p view state image **
   os_sched_fields_capsules environment local state).

Definition flag_del_masked_type_frame environment critical local sg caller saved acquired
    p id state image : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\
    task_stack_live_coverage state.(TskState) (flag_del_active_key caller)) &&
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     (task_suspend_view caller).(os_execution_invocation)
     (task_suspend_view caller).(os_execution_origin) saved acquired **
   flag_del_context environment caller **
   flag_del_type_frame sg p (FlagQueryPool id) state image **
   os_sched_fields_capsules environment local state).

Definition flag_del_group_frame environment critical local sg caller saved acquired
    p id state image : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\
    task_stack_live_coverage state.(TskState) (flag_del_active_key caller)) &&
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     (task_suspend_view caller).(os_execution_invocation)
     (task_suspend_view caller).(os_execution_origin) saved acquired **
   flag_del_context environment caller ** flag_del_group_padding p image **
   flag_del_pool_fields_frame sg state id ** unmap_table_rep sg **
   os_sched_fields_capsules environment local state).

Definition flag_del_iteration_next_frame environment critical local sg caller saved acquired
    post node waiter : Assertion :=
  coq_prop (UCOS2_state_inv sg post /\
    task_stack_live_coverage post.(TskState) (flag_del_active_key caller)) &&
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     (task_suspend_view caller).(os_execution_invocation)
     (task_suspend_view caller).(os_execution_origin) saved acquired **
   flag_del_context environment caller ** UCOS2_fields_inv sg post **
   flag_node_fields_rep_without_next sg.(osKernelConfig) node waiter.(flagWaitImage) **
   os_sched_fields_capsules environment local post ** unmap_table_rep sg).

Definition flag_del_registered_state call state : UCOS2_Verify_State :=
  replace_TskS (task_begin_invocation call.(os_sched_call_origin) state.(TskState)) state.

Definition flag_del_entry_frame pointer view error (frame : Assertion) : Assertion :=
  flag_del_raw_type pointer view ** (error # UChar |->_) ** frame.

(** This endpoint is produced by initial publication, selector/install/take
    and the actual initial-frame restore. The pure clean projection belongs
    to that source endpoint; [flag_del_initial_node_clean] proves the
    initializer's contribution. The CPU resource cannot create it. *)
Definition flag_del_initial_entry environment local sg caller mask state (frame : Assertion) : Assertion :=
  EX initial saved fragments,
  EX entry : Armv7aInitialCallABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations),
    let call := armv7a_initial_call saved initial.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
    coq_prop (caller = TaskSuspendTask call /\
      state = armv7a_initial_call_registered saved initial /\
      mask = armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) /\
      armv7a_initial_frame_binding saved /\ saved.(armv7a_continuation_call) = None /\
      task_stack_fragments_in_range saved.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
        0 fragments /\
      task_current_at initial saved.(armv7a_continuation_stack).(stackLeaseSlot)
        saved.(armv7a_continuation_stack).(stackLeaseGeneration) /\
      initial.(SchedState).(isRunning) = true /\
      initial.(TskState).(parkedTaskStacks) (task_stack_key saved.(armv7a_continuation_stack)) = None /\
      task_stack_live_coverage initial.(TskState) (Some (task_stack_key saved.(armv7a_continuation_stack))) /\
      (exists node, initial.(TskState).(inUsedTaskStates) saved.(armv7a_continuation_stack).(stackLeaseSlot) = Some node /\
        node.(taskGeneration) = saved.(armv7a_continuation_stack).(stackLeaseGeneration) /\
        flag_del_application_task_clean node)) &&
    (UCOS2_fields_inv sg initial ** armv7a_initial_execution environment.(task_stack_call_continuations) saved **
     task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion) fragments **
     os_sched_fields_capsules environment local initial ** unmap_table_rep sg ** frame).

(** A source event from the completed preceding C return is mandatory.
    Neither its existence nor its execution ownership follows from a fresh
    invocation label. The predecessor's clean result is consumed once. *)
Definition flag_del_sequential_entry environment local sg caller mask state (frame : Assertion) : Assertion :=
  fun heap =>
    exists (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform)) previous previous_state previous_heap,
      let invocation := previous_state.(TskState).(taskLifecycle).(taskNextInvocation) in
      caller = TaskSuspendTask (kernel_sequential_call previous invocation) /\
      state = flag_del_registered_state previous previous_state /\
      previous_state.(SchedState).(isRunning) = true /\
      flag_del_task_application_entry previous previous_state /\
      kernel_sequential_call_source boundary previous invocation previous_heap heap /\
      (flag_del_closed environment local sg (TaskSuspendTask previous) mask previous_state ** frame) previous_heap.

(** The ISR view owns the real handler execution resource. All dormant
    task continuations remain in the same map, including the interrupted
    task when the suspended origin is a task. *)
Definition flag_del_isr_entry environment local sg caller mask state (frame : Assertion) : Assertion :=
  EX view,
    coq_prop (caller = TaskSuspendDisabled view /\ sched_disabled_isr_source view state) &&
    (flag_del_closed environment local sg (TaskSuspendDisabled view) mask state ** frame).

Definition flag_del_boot_entry environment local sg caller mask state (frame : Assertion) : Assertion :=
  EX call,
    coq_prop (caller = TaskSuspendTask call /\ call.(os_sched_call_origin) = BootInvocation /\
      state.(SchedState).(isRunning) = false /\
      task_invocation_active state.(TskState) call.(os_sched_call_invocation) BootInvocation) &&
    (flag_del_closed environment local sg (TaskSuspendTask call) mask state ** frame).

Definition flag_del_public_entry environment local sg caller mask state pointer view error frame : Assertion :=
  let retained := flag_del_entry_frame pointer view error frame in
  flag_del_initial_entry environment local sg caller mask state retained ||
  flag_del_sequential_entry environment local sg caller mask state retained ||
  flag_del_isr_entry environment local sg caller mask state retained ||
  flag_del_boot_entry environment local sg caller mask state retained.

Lemma flag_del_sequential_task_entry : forall previous state,
  flag_del_task_application_entry previous state ->
  flag_del_task_application_entry
    (kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation))
    (flag_del_registered_state previous state).
Proof.
  intros previous state Hentry.
  destruct Hentry as [Hsource [Hnone [node [Hnode [Hgen Hclean]]]]].
  pose proof (kernel_call_task_source_current_at previous state Hsource) as Hcurrent.
  destruct Hsource as [Horigin [Hactive Hexecuting]].
  assert (Hat : task_current_at state previous.(os_sched_call_stack).(stackLeaseSlot)
    previous.(os_sched_call_stack).(stackLeaseGeneration)).
  { exact Hcurrent. }
  destruct (task_current_at_begin_invocation state previous.(os_sched_call_stack).(stackLeaseSlot)
    previous.(os_sched_call_stack).(stackLeaseGeneration) Hat) as [Hregistered Hfresh].
  unfold flag_del_task_application_entry, flag_del_registered_state, kernel_sequential_call.
  cbn [os_sched_call_origin os_sched_call_invocation os_sched_call_stack].
  rewrite Horigin.
  split.
  - unfold kernel_call_task_source; cbn.
    split; [reflexivity|]. split; [exact Hfresh|exact (proj1 Hregistered)].
  - split; [exact Hnone|]. exists node; repeat split; assumption.
Qed.

Lemma flag_del_continuations_begin_invocation : forall environment local sg active state origin,
  task_invocation_origin_live state.(TskState) origin ->
  kernel_continuation_inv environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg active state |--
  kernel_continuation_inv environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg active
    (replace_TskS (task_begin_invocation origin state.(TskState)) state).
Proof.
  intros; unfold kernel_continuation_inv; rewrite !kernel_program_fields_inv_split_unmap; Intros.
  sep_apply_l_atomic (flag_del_fields_begin_invocation sg state origin H).
  entailer!.
Qed.


Lemma flag_del_initial_entry_open : forall environment local sg caller mask state frame,
  flag_del_initial_entry environment local sg caller mask state frame |--
  coq_prop (flag_del_call_cut sg caller state) &&
    (flag_del_closed environment local sg caller mask state ** frame).
Proof.
  intros; unfold flag_del_initial_entry.
  Intros initial saved fragments entry.
  match goal with H : caller = _ /\ _ |- _ =>
    destruct H as [Hcaller [Hstate [Hmask [Hbinding [Hsaved [Hfragments
      [Hcurrent [Hrunning [Hnone [Hcoverage Hclean]]]]]]]]]]
  end.
  subst caller state mask.
  sep_apply_l_atomic (flag_del_initial_fields_owner environment entry sg initial saved fragments local
    Hbinding Hfragments Hcurrent).
  Intros.
  unfold flag_del_closed, flag_del_context, flag_del_active_key, kernel_continuation_inv.
  rewrite kernel_program_fields_inv_split_unmap.
  unfold flag_del_call_cut; cbn [armv7a_initial_call os_sched_call_origin].
  unfold kernel_call_execution_owned.
  entailer!.
  - split; [exact H|]. split; [exact Hnone|exact Hclean].
Qed.

Lemma flag_del_sequential_entry_open : forall environment local sg caller mask state frame,
  flag_del_sequential_entry environment local sg caller mask state frame |--
  coq_prop (flag_del_call_cut sg caller state) &&
    (flag_del_closed environment local sg caller mask state ** frame).
Proof.
  intros environment local sg caller mask state frame heap Hentry.
  destruct Hentry as [boundary [previous [previous_state [previous_heap
    [Hcaller [Hstate [Hrunning [Hclean [Hsource Hbefore]]]]]]]]].
  subst caller state.
  pose proof (flag_del_sequential_task_entry previous previous_state Hclean) as Hfresh.
  assert (Horigin : task_invocation_origin_live previous_state.(TskState)
    previous.(os_sched_call_origin)).
  { destruct Hclean as [[Heq [_ Hcurrent]] [_ [node [Hnode [Hgen Hflag]]]]].
    rewrite Heq; exists node; auto. }
  assert (Hopen : flag_del_closed environment local sg (TaskSuspendTask previous) mask previous_state ** frame |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) previous mask **
    (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv
       local sg (task_stack_call_active_key previous) previous_state ** frame)).
  { unfold flag_del_closed, flag_del_context, flag_del_active_key,
      task_suspend_view, kernel_call_execution_owned; entailer!. }
  destruct (kernel_sequential_call_owned_entry _ _ boundary previous
    previous_state.(TskState).(taskLifecycle).(taskNextInvocation) mask previous_heap heap _
    Hsource (Hopen previous_heap Hbefore)) as [Hmemory Hafter].
  match type of Hafter with ?P heap => match goal with |- ?Q heap =>
    assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (flag_del_continuations_begin_invocation environment local sg
      (task_stack_call_active_key previous) previous_state previous.(os_sched_call_origin) Horigin).
    unfold flag_del_closed, flag_del_context, flag_del_active_key, kernel_call_execution_owned,
      flag_del_registered_state, kernel_sequential_call, task_suspend_view; cbn.
    entailer!.
    unfold flag_del_call_cut; cbn.
    pose proof (proj1 (proj1 Hfresh)) as Heq; cbn in Heq.
    rewrite Heq.
    split; [exact Hrunning|].
    unfold flag_del_registered_state, kernel_sequential_call in Hfresh.
    cbn in Hfresh; rewrite Heq in Hfresh.
    exact Hfresh. }
  exact (Hclose heap Hafter).
Qed.

Lemma flag_del_public_entry_open : forall environment local sg caller mask state pointer view error frame,
  flag_del_public_entry environment local sg caller mask state pointer view error frame |--
  coq_prop (flag_del_call_cut sg caller state) &&
    (flag_del_closed environment local sg caller mask state **
      flag_del_raw_type pointer view ** (error # UChar |->_) ** frame).
Proof.
  intros; unfold flag_del_public_entry, flag_del_entry_frame.
  repeat apply derivable1_orp_elim.
  - sep_apply_l_atomic (flag_del_initial_entry_open environment local sg caller mask state
      (flag_del_raw_type pointer view ** (error # UChar |->_) ** frame)); entailer!.
  - sep_apply_l_atomic (flag_del_sequential_entry_open environment local sg caller mask state
      (flag_del_raw_type pointer view ** (error # UChar |->_) ** frame)); entailer!.
  - unfold flag_del_isr_entry; Intros disabled.
    match goal with H : caller = _ /\ _ |- _ => destruct H as [-> Hsource] end.
    unfold flag_del_call_cut, flag_del_handler_source; entailer!.
  - unfold flag_del_boot_entry; Intros call.
    match goal with H : caller = _ /\ _ |- _ =>
      destruct H as [-> [Horigin [Hrunning Hactive]]] end.
    unfold flag_del_call_cut; rewrite Horigin; entailer!.
Qed.


(** Source-bound successor interface.  The earlier mathematical and resource
    lemmas remain available; only this interface is consumed by the C API. *)
Require Export Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Require Export Ucos2Verify.VC.code.core.spec.os_init_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_irq_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.helpers.

Definition flag_del_source_cut (sg : StableGlobVars) caller state : Prop :=
  match caller with
  | TaskSuspendTask call =>
      match call.(os_sched_call_origin) with
      | BootInvocation =>
          state.(SchedState).(isRunning) = false /\
          task_invocation_active state.(TskState) call.(os_sched_call_invocation) BootInvocation /\
          flag_state_has_no_waiters state.(FlagState)
      | RunningInvocation _ _ =>
          state.(SchedState).(isRunning) = true /\ flag_api_task_entry_observation call state
      end
  | TaskSuspendDisabled view => flag_del_handler_source view state
  end.

Definition flag_del_stack_layout (sg : StableGlobVars) : Prop :=
  forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot.

Lemma flag_del_source_cut_call_cut : forall sg caller state,
  flag_del_source_cut sg caller state -> flag_del_call_cut sg caller state.
Proof.
  intros sg [call|view] state H; [|exact H].
  unfold flag_del_source_cut, flag_del_call_cut in *.
  destruct (os_sched_call_origin call); [tauto|].
  destruct H as [Hrun [Hsource [[node [Hnode [Hgen Hclean]]] [Hnone Hready]]]].
  split; [exact Hrun|].
  unfold flag_del_task_application_entry, flag_del_application_task_clean.
  split; [exact Hsource|]. split; [exact Hnone|].
  exists node; auto.
Qed.

Definition flag_del_source_active sg call state : Assertion :=
  coq_prop (flag_del_source_cut sg (TaskSuspendTask call) state) && emp.

Lemma flag_del_source_active_stable : forall sg,
  os_sched_active_local_stable (flag_del_source_active sg).
Proof.
  intros sg call state.
  unfold flag_del_source_active, flag_del_source_cut.
  destruct (os_sched_call_origin call);
    unfold os_sched_prefix_state, os_sched_ready_checkpoint;
    destruct (os_sched_selection_enabled state);
    try destruct (os_sched_requests_switch state); split; reflexivity.
Qed.

(** These are paired linked-C source events.  Each event relates the actual
    owned footprint on the two adjacent heaps, the same invocation and saved
    mask, and the actual dynamic continuation family.  The conditional source
    contract applies only on this API source domain; it is not an assertion
    that every interrupt/client preserves an arbitrary world. *)
Definition flag_del_source_save_input environment critical local sg caller mask state : Assertion :=
  coq_prop (kernel_sched_ready_clients critical /\ flag_del_source_cut sg caller state) &&
  flag_del_closed environment local sg caller mask state.

(** A normal return of the same boot handler stays in the boot phase.
    This is a law of the paired actual linked-C segment below; it is not
    required of every generic critical-region client or arbitrary world. *)
Definition flag_del_boot_handler_preserved original returned before after : Prop :=
  match original, returned with
  | TaskSuspendDisabled view, TaskSuspendDisabled next =>
      flag_del_boot_handler_source view before -> flag_del_boot_handler_source next after
  | TaskSuspendDisabled _, TaskSuspendTask _ => False
  | TaskSuspendTask _, _ => True
  end.

Definition flag_del_source_save_event environment critical local sg original mask before
    saved returned acquired next_local (before_heap after_heap : model) : Prop :=
  task_suspend_save_effect environment critical sg original returned mask saved before acquired /\
  task_suspend_same_call returned original /\ interrupt_saved_value mask saved /\
  flag_del_boot_handler_preserved original returned before acquired /\
  (flag_del_source_save_input environment critical local sg original mask before) before_heap /\
  (coq_prop (flag_del_source_cut sg returned acquired) &&
    flag_del_masked environment critical next_local sg returned saved acquired acquired) after_heap.

Definition flag_del_source_save_output environment critical local sg original mask before
    before_heap saved : Assertion :=
  fun after_heap => exists returned acquired next_local,
    flag_del_source_save_event environment critical local sg original mask before
      saved returned acquired next_local before_heap after_heap.

Lemma flag_del_source_save_output_open : forall environment critical local sg original mask before before_heap saved,
  flag_del_source_save_output environment critical local sg original mask before before_heap saved |--
  EX returned acquired next_local,
    coq_prop (task_suspend_save_effect environment critical sg original returned mask saved before acquired /\
      task_suspend_same_call returned original /\ interrupt_saved_value mask saved /\
      flag_del_source_cut sg original before /\
      flag_del_boot_handler_preserved original returned before acquired /\
      flag_del_source_cut sg returned acquired) &&
    flag_del_masked environment critical next_local sg returned saved acquired acquired.
Proof.
  intros environment critical local sg original mask before before_heap saved heap H.
  destruct H as [returned [acquired [next_local [Heffect [Hsame [Hmask [Hphase [Hpre Hpost]]]]]]]].
  assert (Horiginal : flag_del_source_cut sg original before) by exact (proj2 (proj1 Hpre)).
  match goal with |- ?Q heap =>
    assert (Hclose : coq_prop (flag_del_source_cut sg returned acquired) &&
      flag_del_masked environment critical next_local sg returned saved acquired acquired |-- Q)
  end.
  { Exists returned acquired next_local; entailer!. }
  exact (Hclose heap Hpost).
Qed.

Definition flag_del_source_restore_cut sg caller state (schedule : bool) : Prop :=
  flag_del_source_cut sg caller state /\
  (schedule = true -> exists call, caller = TaskSuspendTask call /\
    call.(os_sched_call_origin) <> BootInvocation /\ os_sched_call_cut sg call state).

Definition flag_del_source_restore_input environment critical local sg active saved acquired released schedule : Assertion :=
  coq_prop (kernel_sched_ready_clients critical /\ flag_del_source_restore_cut sg active released schedule) &&
  flag_del_masked environment critical local sg active saved acquired released.

Definition flag_del_source_restore_event environment critical local sg active saved acquired released schedule
    returned current next_local (before_heap after_heap : model) : Prop :=
  task_suspend_restore_effect environment critical sg active returned released current /\
  task_suspend_same_call returned active /\
  flag_del_boot_handler_preserved active returned released current /\
  (flag_del_source_restore_input environment critical local sg active saved acquired released schedule) before_heap /\
  (coq_prop (flag_del_source_restore_cut sg returned current schedule) &&
    flag_del_closed environment next_local sg returned (armv7a_irq_fiq_mask saved) current) after_heap.

Definition flag_del_source_restore_output environment critical local sg active saved acquired released schedule
    before_heap : Assertion :=
  fun after_heap => exists returned current next_local,
    flag_del_source_restore_event environment critical local sg active saved acquired released schedule
      returned current next_local before_heap after_heap.

Lemma flag_del_source_restore_output_open : forall environment critical local sg active saved acquired released schedule before_heap,
  flag_del_source_restore_output environment critical local sg active saved acquired released schedule before_heap |--
  EX returned current next_local,
    coq_prop (task_suspend_restore_effect environment critical sg active returned released current /\
      task_suspend_same_call returned active /\
      flag_del_boot_handler_preserved active returned released current /\
      flag_del_source_restore_cut sg returned current schedule) &&
    flag_del_closed environment next_local sg returned (armv7a_irq_fiq_mask saved) current.
Proof.
  intros environment critical local sg active saved acquired released schedule before_heap heap H.
  destruct H as [returned [current [next_local [Heffect [Hsame [Hphase [Hpre Hpost]]]]]]].
  match goal with |- ?Q heap =>
    assert (Hclose : coq_prop (flag_del_source_restore_cut sg returned current schedule) &&
      flag_del_closed environment next_local sg returned (armv7a_irq_fiq_mask saved) current |-- Q)
  end.
  { Exists returned current next_local; entailer!. }
  exact (Hclose heap Hpost).
Qed.

Definition flag_del_source_return_cut environment critical local sg original returned mask p view option name before current result X : Assertion :=
  coq_prop (flag_del_source_cut sg returned current /\
    flag_del_program environment critical sg original mask view p option name before result current) &&
  flag_del_return_cut environment local sg original returned mask p view current result X.

Definition flag_del_prefix_to_scheduler environment critical sg original mask view pointer option name
    before context current : Prop :=
  flag_del_prefix_program environment critical sg original mask view pointer option name before
    ((flag_del_observation 0 OS_ERR_NONE, true), TaskSuspendTask context) current.

Definition flag_del_source_after_restore environment critical sg original mask view pointer option name
    before (X : (Z * Z) -> UCOS2_Verify_State -> Prop) result error schedule : Assertion :=
  EX returned current next_local,
    coq_prop (task_suspend_same_call returned original /\
      flag_del_prefix_program environment critical sg original mask view pointer option name before
        (((result, error), schedule), returned) current /\
      safeExec (fun state => state = current)
        (flag_del_tail_program environment critical sg mask (((result, error), schedule), returned)) X /\
      flag_del_source_restore_cut sg returned current schedule) &&
    (flag_del_closed environment next_local sg returned mask current ** flag_del_raw_type pointer view).

Lemma flag_del_source_scheduler_pre : forall environment local sg call mask state,
  os_sched_call_cut sg call state -> flag_del_source_cut sg (TaskSuspendTask call) state ->
  flag_del_closed environment local sg (TaskSuspendTask call) mask state |--
  os_sched_active_call_pre environment local (flag_del_source_active sg) sg call mask state.
Proof.
  intros; unfold os_sched_active_call_pre, flag_del_source_active.
  pose proof (flag_del_source_active_stable sg).
  unfold flag_del_closed, flag_del_context, flag_del_active_key, task_suspend_view,
    os_sched_execution_view, kernel_continuation_call_closed, kernel_call_execution_owned; entailer!.
Qed.

Lemma flag_del_source_scheduler_return : forall environment critical sg call mask before result X,
  flag_del_scheduler_safe environment critical sg call mask before (fst result) (snd result) X ->
  os_sched_active_history_return_post environment critical (flag_del_source_active sg) sg call mask before |--
  EX returned current next_local,
    coq_prop (task_tcb_init_stack_same_call returned call /\
      flag_del_return_safe current result X /\ flag_del_source_cut sg (TaskSuspendTask returned) current) &&
    flag_del_closed environment next_local sg (TaskSuspendTask returned) mask current.
Proof.
  intros environment critical sg call mask before [result error] X Hsafe.
  unfold os_sched_active_history_return_post, flag_del_source_active; Intros returned current next_local.
  assert (Hhistory : os_sched_continuation_call_history environment critical sg call mask before returned current) by tauto.
  assert (Hstep : task_suspend_schedule_program environment critical sg
    (TaskSuspendTask call) mask before (TaskSuspendTask returned) current).
  { cbn [task_suspend_schedule_program]. exists returned, current; split.
    - apply os_sched_continuation_program_iff; exact Hhistory.
    - split; reflexivity. }
  pose proof (flag_del_schedule_safe_return environment critical sg (TaskSuspendTask call) mask
    before (TaskSuspendTask returned) current (result,error) X Hstep Hsafe) as Hreturn.
  Exists returned current next_local.
  unfold flag_del_closed, flag_del_context, flag_del_active_key, task_suspend_view,
    os_sched_execution_view, kernel_continuation_call_closed, kernel_call_execution_owned; entailer!.
Qed.


Definition flag_del_source_loop_facts sg caller acquired id original visited remaining current pnode : Prop :=
  flag_del_loop_facts sg caller acquired id original visited remaining current pnode /\
  flag_del_source_cut sg caller current.

(** The boot domain is a finite chain of completed linked C calls.  The
    conditional module boundary below binds each *actual* source relation to
    adjacent owned heaps.  In particular Timer's old return-only receipt is
    not treated as a theorem about the omitted Stat-to-Timer prefix. *)
Inductive FlagDelBootModule : Type :=
| FlagDelBootIdle
| FlagDelBootStat
| FlagDelBootTimer
| FlagDelBootCreate (publication : TaskCreateStackPublication)
| FlagDelBootClient (action : KernelClientAction).

Definition flag_del_boot_module_program (p : OsInitContext) (module : FlagDelBootModule)
    call returned before after : Prop :=
  match module with
  | FlagDelBootIdle => os_init_idle_program p call before returned after
  | FlagDelBootStat => os_init_stat_program p call before returned after
  | FlagDelBootTimer =>
      tmr_init_program p.(os_init_timer) call before tt after /\
      task_tcb_init_stack_same_call returned call
  | FlagDelBootCreate publication =>
      kernel_client_step (task_create_stack_publication_client publication)
        (os_init_sg p) before after /\ task_tcb_init_stack_same_call returned call
  | FlagDelBootClient action =>
      critical_region_clients (os_init_critical p) action /\
      kernel_client_step action (os_init_sg p) before after /\
      task_tcb_init_stack_same_call returned call
  end.

(** A registered Boot allocation client has this exact Flag update.
    A linked-C event must identify this client; an unconstrained initializer
    post is never used as evidence that a flag was allocated. *)
Definition flag_del_boot_allocate_client bits name id : KernelClientAction :=
  {| kernel_client_actor := None;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun _ before after =>
       exists flags, flag_allocate before.(FlagState) bits name = Some (id, flags) /\
         after = replace_FlagS flags before |}.

Lemma flag_del_boot_allocate_preserves_no_waiters : forall sg bits name id before after,
  flag_state_has_no_waiters before.(FlagState) ->
  kernel_client_step (flag_del_boot_allocate_client bits name id) sg before after ->
  flag_state_has_no_waiters after.(FlagState).
Proof.
  intros sg bits name id before after Hnone [flags [Hallocate ->]].
  cbn; eapply flag_allocate_preserves_no_waiters; eassumption.
Qed.

Record FlagDelBootModuleABI (p : OsInitContext) : Type := {
  flag_del_boot_module_event :
    FlagDelBootModule -> OsSchedCallContext -> UCOS2_Verify_State ->
    (Armv7aContinuation -> Assertion) -> OsSchedCallContext -> UCOS2_Verify_State ->
    (Armv7aContinuation -> Assertion) -> model -> model -> Prop;
  flag_del_boot_module_source : forall module call before local returned after next_local first last,
    flag_del_boot_module_event module call before local returned after next_local first last ->
    flag_del_boot_module_program p module call returned before after;
  flag_del_boot_module_resources : forall module call before local returned after next_local first last,
    flag_del_boot_module_event module call before local returned after next_local first last ->
    flag_del_closed (os_init_environment p) local (os_init_sg p)
      (TaskSuspendTask call) (os_init_mask p) before first ->
    flag_del_closed (os_init_environment p) next_local (os_init_sg p)
      (TaskSuspendTask returned) (os_init_mask p) after last;
  flag_del_boot_module_no_waiters : forall module call before local returned after next_local first last,
    flag_del_boot_module_event module call before local returned after next_local first last ->
    flag_del_boot_module_program p module call returned before after ->
    flag_del_closed (os_init_environment p) local (os_init_sg p)
      (TaskSuspendTask call) (os_init_mask p) before first ->
    call.(os_sched_call_origin) = BootInvocation ->
    before.(SchedState).(isRunning) = false ->
    flag_state_has_no_waiters before.(FlagState) ->
    returned.(os_sched_call_origin) = BootInvocation /\
    after.(SchedState).(isRunning) = false /\
    task_invocation_active after.(TskState) returned.(os_sched_call_invocation) BootInvocation /\
    flag_state_has_no_waiters after.(FlagState)
}.

(** Initialization uses the checked eight initializer posts, with the actual
    loader footprint.  The fields conversion below is proved from empty
    parked-continuation and flag-wait-node maps, retaining the actual
    initializer residual; it assumes no pre-existing invariant. *)
Definition flag_del_boot_initializer_owned p : Assertion :=
  os_init_components p 8 ** os_init_loader_frame p ** GlobalStrings (os_init_literals p).

Definition flag_del_boot_registered_owned p : Assertion :=
  kernel_stack_call_closed (os_init_environment p).(task_stack_call_continuations)
    kernel_program_inv (os_init_sg p) None p.(os_init_call)
      (os_init_mask p) (os_init_registered_state p) **
  os_init_component p 0 true ** os_init_idle_stack p ** os_init_stat_stack p **
  os_init_timer_stack p ** GlobalStrings_missing (os_init_literals p) os_init_literal_keys.

Lemma flag_del_boot_initializers_registered : forall p,
  os_init_source_binding p ->
  flag_del_boot_initializer_owned p |-- flag_del_boot_registered_owned p.
Proof.
  intros p Hbinding; unfold flag_del_boot_initializer_owned, flag_del_boot_registered_owned.
  sep_apply_l_atomic (os_init_initializers_stack_world p Hbinding).
  sep_apply_l_atomic (os_init_register_boot_world p Hbinding); entailer!.
Qed.

Lemma flag_del_boot_registered_no_waiters : forall p,
  flag_state_has_no_waiters (os_init_registered_state p).(FlagState).
Proof.
  intros p; unfold os_init_registered_state, os_init_boot_state.
  cbn [replace_TskS FlagState UCOS2_boot_state].
  destruct (cfgFlagEnabled (osKernelConfig (os_init_sg p))).
  - apply flag_initial_has_no_waiters.
  - split; [intros id group H; discriminate|intros; reflexivity].
Qed.

Lemma flag_del_boot_sequential_resources : forall environment local sg
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform)) previous state mask before after,
  previous.(os_sched_call_origin) = BootInvocation ->
  flag_del_source_cut sg (TaskSuspendTask previous) state ->
  kernel_sequential_call_source boundary previous state.(TskState).(taskLifecycle).(taskNextInvocation)
    before after ->
  flag_del_closed environment local sg (TaskSuspendTask previous) mask state before ->
  flag_del_source_cut sg (TaskSuspendTask (kernel_sequential_call previous
      state.(TskState).(taskLifecycle).(taskNextInvocation))) (flag_del_registered_state previous state) /\
  flag_del_closed environment local sg (TaskSuspendTask (kernel_sequential_call previous
      state.(TskState).(taskLifecycle).(taskNextInvocation))) mask (flag_del_registered_state previous state) after.
Proof.
  intros environment local sg boundary previous state mask before after Horigin Hcut Hevent Howned.
  unfold flag_del_source_cut in Hcut; rewrite Horigin in Hcut.
  destruct Hcut as [Hrun [Hactive Hnone]].
  assert (Hlive : task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin)).
  { rewrite Horigin; exact I. }
  assert (Hopen : flag_del_closed environment local sg (TaskSuspendTask previous) mask state |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) previous mask **
    kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv
      local sg (task_stack_call_active_key previous) state).
  { unfold flag_del_closed, flag_del_context, flag_del_active_key,
      task_suspend_view, kernel_call_execution_owned; entailer!. }
  destruct (kernel_sequential_call_owned_entry _ _ boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) mask before after _
    Hevent (Hopen before Howned)) as [Hmemory Hafter].
  split.
  - unfold flag_del_source_cut, kernel_sequential_call; cbn [os_sched_call_origin].
    rewrite Horigin; split; [exact Hrun|]. split.
    + unfold flag_del_registered_state; rewrite Horigin.
      apply task_begin_invocation_active; exact I.
    + exact Hnone.
  - match type of Hafter with ?P after => match goal with |- ?Q after =>
      assert (Hclose : P |-- Q) end end.
    { sep_apply_l_atomic (flag_del_continuations_begin_invocation environment local sg
        (task_stack_call_active_key previous) state previous.(os_sched_call_origin) Hlive).
      unfold flag_del_closed, flag_del_context, flag_del_active_key, kernel_call_execution_owned,
        flag_del_registered_state, kernel_sequential_call, task_suspend_view; cbn; entailer!. }
    exact (Hclose after Hafter).
Qed.

Inductive flag_del_boot_completed_chain p (abi : FlagDelBootModuleABI p) :
  OsSchedCallContext -> UCOS2_Verify_State -> (Armv7aContinuation -> Assertion) -> model ->
  OsSchedCallContext -> UCOS2_Verify_State -> (Armv7aContinuation -> Assertion) -> model -> Prop :=
| flag_del_boot_chain_refl : forall call state local heap,
    flag_del_boot_completed_chain p abi call state local heap call state local heap
| flag_del_boot_chain_step : forall call state local heap middle middle_state middle_local middle_heap
    module returned current next_local after_heap,
    flag_del_boot_completed_chain p abi call state local heap middle middle_state middle_local middle_heap ->
    flag_del_boot_module_event p abi module middle middle_state middle_local
      returned current next_local middle_heap after_heap ->
    flag_del_boot_completed_chain p abi call state local heap returned current next_local after_heap
| flag_del_boot_chain_sequential : forall call state local heap previous previous_state previous_local previous_heap
    (boundary : KernelSequentialCallABI (os_init_environment p).(task_stack_call_external)
      (os_init_environment p).(task_stack_call_platform)) after_heap,
    flag_del_boot_completed_chain p abi call state local heap previous previous_state previous_local previous_heap ->
    kernel_sequential_call_source boundary previous previous_state.(TskState).(taskLifecycle).(taskNextInvocation)
      previous_heap after_heap ->
    flag_del_boot_completed_chain p abi call state local heap
      (kernel_sequential_call previous previous_state.(TskState).(taskLifecycle).(taskNextInvocation))
      (flag_del_registered_state previous previous_state) previous_local after_heap.

Lemma flag_del_boot_chain_append : forall p abi first first_state first_local first_heap
    middle middle_state middle_local middle_heap returned current next_local after_heap,
  flag_del_boot_completed_chain p abi first first_state first_local first_heap
    middle middle_state middle_local middle_heap ->
  flag_del_boot_completed_chain p abi middle middle_state middle_local middle_heap
    returned current next_local after_heap ->
  flag_del_boot_completed_chain p abi first first_state first_local first_heap
    returned current next_local after_heap.
Proof.
  intros p abi first first_state first_local first_heap middle middle_state middle_local middle_heap
    returned current next_local after_heap Hfirst Hsecond.
  revert first first_state first_local first_heap Hfirst.
  induction Hsecond; intros; eauto using flag_del_boot_chain_step, flag_del_boot_chain_sequential.
Qed.

Lemma flag_del_boot_chain_no_waiters : forall p abi call state local heap returned current next_local after_heap,
  flag_del_boot_completed_chain p abi call state local heap returned current next_local after_heap ->
  flag_del_closed (os_init_environment p) local (os_init_sg p) (TaskSuspendTask call)
    (os_init_mask p) state heap ->
  call.(os_sched_call_origin) = BootInvocation ->
  state.(SchedState).(isRunning) = false ->
  task_invocation_active state.(TskState) call.(os_sched_call_invocation) BootInvocation ->
  flag_state_has_no_waiters state.(FlagState) ->
  returned.(os_sched_call_origin) = BootInvocation /\
  flag_del_source_cut (os_init_sg p) (TaskSuspendTask returned) current /\
  flag_del_closed (os_init_environment p) next_local (os_init_sg p) (TaskSuspendTask returned)
    (os_init_mask p) current after_heap.
Proof.
  intros p abi call state local heap returned current next_local after_heap Hchain.
  induction Hchain; intros Howned Horigin Hrun Hactive Hnone.
  - split; [exact Horigin|].
    split; [unfold flag_del_source_cut; rewrite Horigin; auto|exact Howned].
  - destruct (IHHchain Howned Horigin Hrun Hactive Hnone)
      as [Hmiddle_origin [Hmiddle Hmiddle_owned]].
    unfold flag_del_source_cut in Hmiddle; rewrite Hmiddle_origin in Hmiddle.
    destruct Hmiddle as [Hmrun [Hmactive Hmnone]].
    pose proof (flag_del_boot_module_source p abi _ _ _ _ _ _ _ _ _ H) as Hprogram.
    destruct (flag_del_boot_module_no_waiters p abi _ _ _ _ _ _ _ _ _ H Hprogram
      Hmiddle_owned Hmiddle_origin Hmrun Hmnone) as [Hreturned [Hcrun [Hcactive Hcnone]]].
    split; [exact Hreturned|]. split.
    + unfold flag_del_source_cut; rewrite Hreturned; auto.
    + eapply flag_del_boot_module_resources; eassumption.
  - destruct (IHHchain Howned Horigin Hrun Hactive Hnone) as [Hprevious [Hcut Hprevious_owned]].
    split; [exact Hprevious|].
    eapply flag_del_boot_sequential_resources; eassumption.
Qed.


Lemma flag_del_no_waiter_padding_empty : forall sg flags,
  flag_state_has_no_waiters flags ->
  flag_configured_padding_rep sg flags --||-- emp.
Proof.
  intros sg flags [_ Hnodes].
  unfold flag_configured_padding_rep.
  destruct (cfgFlagEnabled (osKernelConfig sg)); [|split; reflexivity].
  unfold flag_wait_nodes_padding_rep; apply store_map_empty.
  - exists []; split.
    + intros q; split; [contradiction|intros [v Hv]; rewrite Hnodes in Hv; discriminate].
    + constructor.
  - intros q; left; apply Hnodes.
Qed.

Lemma flag_del_boot_registered_fields : forall p local,
  p.(os_init_call).(os_sched_call_origin) = BootInvocation ->
  kernel_stack_call_closed (os_init_environment p).(task_stack_call_continuations)
    kernel_program_inv (os_init_sg p) None p.(os_init_call)
      (os_init_mask p) (os_init_registered_state p) |--
  flag_del_closed (os_init_environment p) local (os_init_sg p)
    (TaskSuspendTask p.(os_init_call)) (os_init_mask p) (os_init_registered_state p).
Proof.
  intros p local Horigin.
  assert (Hactive : task_stack_call_active_key p.(os_init_call) = None)
    by (unfold task_stack_call_active_key; rewrite Horigin; reflexivity).
  assert (Hstack : armv7a_task_stack_continuations (os_init_environment p).(task_stack_call_continuations)
    (os_init_registered_state p).(TskState) (os_init_registered_state p).(TskState).(parkedTaskStacks) --||-- emp).
  { unfold armv7a_task_stack_continuations, store_parked_continuations.
    apply store_map_empty.
    - exists []; split; [intros; split; [contradiction|intros [v H]; discriminate]|constructor].
    - intros q; left; reflexivity. }
  assert (Hsaved : store_parked_continuations
    (kernel_saved_continuation_entry (os_init_environment p).(task_stack_call_continuations)
      (os_init_registered_state p).(TskState) local)
    (os_init_registered_state p).(TskState).(parkedTaskStacks) --||-- emp).
  { unfold store_parked_continuations; apply store_map_empty.
    - exists []; split; [intros; split; [contradiction|intros [v H]; discriminate]|constructor].
    - intros q; left; reflexivity. }
  unfold kernel_stack_call_closed, kernel_stack_inv, flag_del_closed, flag_del_context,
    flag_del_active_key, task_suspend_view, kernel_continuation_inv.
  rewrite Hstack, Hsaved, Hactive, kernel_program_inv_fields_padding.
  rewrite (flag_del_no_waiter_padding_empty _ _ (flag_del_boot_registered_no_waiters p)).
  unfold kernel_call_execution_owned; entailer!.
Qed.

Definition flag_del_boot_initial_residual p : Assertion :=
  os_init_component p 0 true ** os_init_idle_stack p ** os_init_stat_stack p **
  os_init_timer_stack p ** GlobalStrings_missing (os_init_literals p) os_init_literal_keys.

Lemma flag_del_boot_initializers_fields : forall p local,
  os_init_source_binding p ->
  flag_del_boot_initializer_owned p |--
  flag_del_closed (os_init_environment p) local (os_init_sg p)
    (TaskSuspendTask p.(os_init_call)) (os_init_mask p) (os_init_registered_state p) **
  flag_del_boot_initial_residual p.
Proof.
  intros p local Hbinding.
  assert (Horigin : p.(os_init_call).(os_sched_call_origin) = BootInvocation)
    by (unfold os_init_source_binding in Hbinding; tauto).
  sep_apply_l_atomic (flag_del_boot_initializers_registered p Hbinding).
  unfold flag_del_boot_registered_owned, flag_del_boot_initial_residual.
  sep_apply_l_atomic (flag_del_boot_registered_fields p local Horigin); entailer!.
Qed.

(** The selector and machine-return events below have the SAME actual
    restored footprint as the first-call owner.  The source relations supply
    no heap by themselves; the adjoining initial-execution assertion owns it. *)
Definition flag_del_initial_selection_source environment sg published outgoing sp outgoing_fragments selected
    (restored : model) : Prop :=
  let hooked := os_sched_save_current_sp (os_sched_prefix_state published)
    outgoing.(os_sched_call_stack).(stackLeaseSlot) sp in
  exists (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations)) before installed,
    os_sched_saved_stack_binding outgoing outgoing_fragments hooked /\
    sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) /\
    os_sched_destination_binding environment.(task_stack_call_external) outgoing outgoing_fragments
      hooked selected.(armv7a_continuation_stack) selected.(armv7a_continuation_fragments) /\
    sched_install_heap_fragment sg before installed
      (task_slot_addr sg selected.(armv7a_continuation_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    armv7a_task_restore_transition task_abi outgoing selected installed restored.

Lemma flag_del_captured_heap_forget : forall (owned : Assertion) captured,
  os_sched_active_heap_cut owned captured |-- owned.
Proof. intros owned captured actual [_ Howned]; exact Howned. Qed.

Definition flag_del_source_initial_root environment local sg caller mask state (frame : Assertion) : Assertion :=
  EX publication published_from published outgoing sp outgoing_fragments selected restored_heap,
  EX entry : Armv7aInitialCallABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations),
  let initial := os_sched_install_context outgoing outgoing_fragments selected.(armv7a_continuation_stack)
    (os_sched_save_current_sp (os_sched_prefix_state published)
      outgoing.(os_sched_call_stack).(stackLeaseSlot) sp) in
  let first := armv7a_initial_call selected initial.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) in
  coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg published_from published /\
    selected.(armv7a_continuation_stack).(stackLeaseSlot) = publication.(stack_publication_slot) /\
    selected.(armv7a_continuation_stack).(stackLeaseGeneration) =
      publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration) /\
    caller = TaskSuspendTask first /\ state = armv7a_initial_call_registered selected initial /\
    mask = armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) /\
    selected.(armv7a_continuation_call) = None /\ armv7a_initial_frame_binding selected /\
    task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
      0 selected.(armv7a_continuation_fragments) /\
    task_current_at initial selected.(armv7a_continuation_stack).(stackLeaseSlot)
      selected.(armv7a_continuation_stack).(stackLeaseGeneration) /\
    initial.(SchedState).(isRunning) = true /\
    task_stack_live_coverage initial.(TskState) (Some (task_stack_key selected.(armv7a_continuation_stack))) /\
    flag_del_initial_selection_source environment sg published outgoing sp outgoing_fragments selected restored_heap) &&
  os_sched_active_heap_cut (UCOS2_fields_inv sg initial ** armv7a_initial_execution environment.(task_stack_call_continuations) selected **
   task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
     selected.(armv7a_continuation_fragments) ** os_sched_fields_capsules environment local initial **
   unmap_table_rep sg ** frame) restored_heap.

Lemma flag_del_source_initial_root_open : forall environment local sg caller mask state frame,
  flag_del_source_initial_root environment local sg caller mask state frame |--
  coq_prop (flag_del_source_cut sg caller state) &&
    (flag_del_closed environment local sg caller mask state ** frame).
Proof.
  intros; unfold flag_del_source_initial_root.
  Intros publication published_from published outgoing sp outgoing_fragments selected restored_heap entry.
  cbv zeta in *.
  match goal with H : kernel_client_step _ _ _ _ /\ _ |- _ =>
    destruct H as [Hpublication [Hslot [Hgen [Hcaller [Hstate [Hmask [Hnone
      [Hbinding [Hfragments [Hcurrent [Hrunning [Hcoverage Hselection]]]]]]]]]]]]
  end.
  subst caller state mask.
  match goal with |- os_sched_active_heap_cut ?owned restored_heap |-- _ =>
    sep_apply_l_atomic (flag_del_captured_heap_forget owned restored_heap) end.
  pose proof (flag_initial_published_entry_observation sg publication published_from published
    outgoing sp outgoing_fragments selected Hpublication Hslot Hgen Hcurrent) as Hentry.
  sep_apply_l_atomic (flag_del_initial_fields_owner environment entry sg _ selected
    selected.(armv7a_continuation_fragments) local Hbinding Hfragments Hcurrent); Intros.
  unfold flag_del_source_cut; cbn [armv7a_initial_call os_sched_call_origin].
  unfold flag_del_closed, flag_del_context, flag_del_active_key, kernel_continuation_inv,
    kernel_call_execution_owned.
  rewrite kernel_program_fields_inv_split_unmap; entailer!.
Qed.

(** Mathematical Del return observation only.  This consequence retains
    the checked return proof; it is NOT an actual completed-source event
    and is never accepted as the predecessor of the public source chain. *)
Definition flag_del_task_return_observation environment local sg previous mask state : Assertion :=
  EX critical original initial view pointer option name result,
  coq_prop (task_suspend_same_call (TaskSuspendTask previous) original /\
    flag_del_program environment critical sg original mask view pointer option name initial result state /\
    flag_del_source_cut sg (TaskSuspendTask previous) state) &&
  flag_del_closed environment local sg (TaskSuspendTask previous) mask state.

Lemma flag_del_source_return_task_observation : forall environment critical local sg original previous mask
    pointer view option name before current result X,
  flag_del_source_return_cut environment critical local sg original (TaskSuspendTask previous) mask
    pointer view option name before current result X |--
  flag_del_task_return_observation environment local sg previous mask current ** flag_del_raw_type pointer view.
Proof.
  intros; unfold flag_del_source_return_cut, flag_del_return_cut; Intros.
  unfold flag_del_task_return_observation.
  Exists critical original before view pointer option name result; entailer!.
Qed.

Definition flag_del_source_sequential_owner environment local sg caller mask state (frame : Assertion) : Assertion :=
  fun heap => exists (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform)) previous previous_state previous_heap,
    caller = TaskSuspendTask (kernel_sequential_call previous
      previous_state.(TskState).(taskLifecycle).(taskNextInvocation)) /\
    state = flag_del_registered_state previous previous_state /\
    kernel_sequential_call_source boundary previous
      previous_state.(TskState).(taskLifecycle).(taskNextInvocation) previous_heap heap /\
    (coq_prop (flag_del_source_cut sg (TaskSuspendTask previous) previous_state) &&
      (flag_del_closed environment local sg (TaskSuspendTask previous) mask previous_state ** frame)) previous_heap.

Lemma flag_del_source_sequential_owner_open : forall environment local sg caller mask state frame,
  flag_del_source_sequential_owner environment local sg caller mask state frame |--
  coq_prop (flag_del_source_cut sg caller state) &&
    (flag_del_closed environment local sg caller mask state ** frame).
Proof.
  intros environment local sg caller mask state frame heap H.
  destruct H as [boundary [previous [previous_state [previous_heap [Hcaller [Hstate [Hevent Howned]]]]]]].
  subst caller state.
  destruct Howned as [Hcut Hclosed].
  destruct (os_sched_call_origin previous) eqn:Horigin_eq.
  { unfold flag_del_source_cut in Hcut; rewrite Horigin_eq in Hcut.
    destruct Hcut as [Hrun [Hactive Hnone]].
    assert (Hlive : task_invocation_origin_live previous_state.(TskState) previous.(os_sched_call_origin))
      by (rewrite Horigin_eq; exact I).
    assert (Howned_cut : flag_del_closed environment local sg (TaskSuspendTask previous) mask previous_state ** frame |--
      kernel_call_execution_owned environment.(task_stack_call_external)
        environment.(task_stack_call_platform) previous mask **
      (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv
        local sg (task_stack_call_active_key previous) previous_state ** frame)).
    { unfold flag_del_closed, flag_del_context, flag_del_active_key, task_suspend_view,
        kernel_call_execution_owned; entailer!. }
    destruct (kernel_sequential_call_owned_entry _ _ boundary previous
      previous_state.(TskState).(taskLifecycle).(taskNextInvocation) mask previous_heap heap _
      Hevent (Howned_cut previous_heap Hclosed)) as [Hmemory Hafter].
    split.
    - unfold flag_del_source_cut, kernel_sequential_call; cbn [os_sched_call_origin].
      rewrite Horigin_eq; split; [exact Hrun|]. split.
      + unfold flag_del_registered_state; rewrite Horigin_eq.
        apply task_begin_invocation_active; exact I.
      + exact Hnone.
    - match type of Hafter with ?P heap => match goal with |- ?Q heap =>
        assert (Hclose : P |-- Q) end end.
      { sep_apply_l_atomic (flag_del_continuations_begin_invocation environment local sg
          (task_stack_call_active_key previous) previous_state previous.(os_sched_call_origin) Hlive).
        unfold flag_del_closed, flag_del_context, flag_del_active_key, kernel_call_execution_owned,
          flag_del_registered_state, kernel_sequential_call, task_suspend_view; cbn; entailer!. }
      exact (Hclose heap Hafter). }
  unfold flag_del_source_cut in Hcut; rewrite Horigin_eq in Hcut.
  destruct Hcut as [Hrun Hentry].
  pose proof (flag_sequential_entry_observation previous previous_state Hentry) as Hnext.
  pose proof (flag_del_source_cut_call_cut sg (TaskSuspendTask previous) previous_state) as Hold.
  assert (Happlication : flag_del_task_application_entry previous previous_state).
  { unfold flag_del_task_application_entry.
    destruct Hentry as [Hs [[node [Hnode [Hgen Hclean]]] [Hnone Hr]]].
    split; [exact Hs|]. split; [exact Hnone|]. exists node; auto. }
  assert (Hlegacy : flag_del_sequential_entry environment local sg
    (TaskSuspendTask (kernel_sequential_call previous
      previous_state.(TskState).(taskLifecycle).(taskNextInvocation))) mask
    (flag_del_registered_state previous previous_state) frame heap).
  { exists boundary, previous, previous_state, previous_heap.
    split; [reflexivity|]. split; [reflexivity|].
    exact (conj Hrun (conj Happlication (conj Hevent Hclosed))). }
  destruct (flag_del_sequential_entry_open environment local sg _ mask _ frame heap Hlegacy) as [_ Hafter].
  split; [|exact Hafter].
  unfold flag_del_source_cut; cbn [kernel_sequential_call os_sched_call_origin].
  rewrite Horigin_eq; split; [exact Hrun|exact Hnext].
Qed.

(** The ISR domain additionally carries the actual frame-save and park
    source, retaining the interrupted descriptor and its lease.  The handler
    footprint is the current resource; a ready task never creates it. *)
Definition flag_del_source_isr_root environment local sg caller mask state (frame : Assertion) : Assertion :=
  fun heap => exists view handler descriptor before saved_heap entry,
    caller = TaskSuspendDisabled view /\
    view = os_int_exit_execution_view handler /\
    mask = 192 /\
    armv7a_save_transition environment.(task_stack_call_continuations) handler descriptor before saved_heap /\
    descriptor.(armv7a_continuation_call) = Some handler.(os_int_exit_interrupted_call) /\
    state = armv7a_irq_live_parked_state entry handler.(os_int_exit_interrupted_call)
      descriptor.(armv7a_continuation_sp) descriptor.(armv7a_continuation_fragments) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)
      descriptor.(armv7a_continuation_sp)) saved_heap heap /\
    (os_int_exit_frame_save_pre environment.(task_stack_call_external)
       environment.(task_stack_call_platform) handler **
     (UCOS2_fields_inv sg entry ** os_sched_fields_capsules environment local entry **
       local descriptor ** unmap_table_rep sg ** frame)) before /\
    (flag_del_isr_entry environment local sg caller mask state frame) heap.

Definition flag_del_source_boot_origin environment critical local sg caller mask state : Assertion :=
  fun heap => exists p (modules : FlagDelBootModuleABI p)
    (sequential : KernelSequentialCallABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform))
    initial_heap registered_heap idle idle_state idle_local idle_heap
    stat stat_state stat_local stat_heap timer timer_state timer_local timer_heap
    previous previous_state previous_local previous_heap,
    environment = os_init_environment p /\ critical = os_init_critical p /\
    sg = os_init_sg p /\ mask = os_init_mask p /\ os_init_source_binding p /\
    flag_del_boot_initializer_owned p initial_heap /\
    (os_sched_active_heap_cut
      (flag_del_closed environment tmr_init_empty_local sg
        (TaskSuspendTask p.(os_init_call)) mask (os_init_registered_state p)) registered_heap **
      flag_del_boot_initial_residual p) initial_heap /\
    flag_del_boot_module_event p modules FlagDelBootIdle p.(os_init_call) (os_init_registered_state p)
      tmr_init_empty_local idle idle_state idle_local registered_heap idle_heap /\
    flag_del_boot_module_event p modules FlagDelBootStat idle idle_state idle_local
      stat stat_state stat_local idle_heap stat_heap /\
    flag_del_boot_module_event p modules FlagDelBootTimer stat stat_state stat_local
      timer timer_state timer_local stat_heap timer_heap /\
    flag_del_boot_completed_chain p modules timer timer_state timer_local timer_heap
      previous previous_state previous_local previous_heap /\
    caller = TaskSuspendTask (kernel_sequential_call previous
      previous_state.(TskState).(taskLifecycle).(taskNextInvocation)) /\
    state = flag_del_registered_state previous previous_state /\
    local = previous_local /\
    kernel_sequential_call_source sequential previous
      previous_state.(TskState).(taskLifecycle).(taskNextInvocation) previous_heap heap.

Definition flag_del_source_boot_entry environment critical local sg caller mask state (frame : Assertion) : Assertion :=
  flag_del_source_boot_origin environment critical local sg caller mask state ** frame.

Lemma flag_del_captured_heap_owned : forall (owned extra : Assertion) captured,
  os_sched_active_heap_cut owned captured ** extra |-- coq_prop (owned captured).
Proof.
  intros owned extra captured.
  assert (Hcut : os_sched_active_heap_cut owned captured |-- coq_prop (owned captured) && owned).
  { intros actual [Heq Howned]; subst actual; split; exact Howned. }
  sep_apply_l_atomic Hcut; entailer!.
Qed.

Lemma flag_del_source_boot_origin_open : forall environment critical local sg caller mask state,
  flag_del_source_boot_origin environment critical local sg caller mask state |--
  coq_prop (flag_del_source_cut sg caller state) &&
    flag_del_closed environment local sg caller mask state.
Proof.
  intros environment critical local sg caller mask state heap H.
  destruct H as (p & modules & sequential & initial_heap & registered_heap &
    idle & idle_state & idle_local & idle_heap & stat & stat_state & stat_local & stat_heap &
    timer & timer_state & timer_local & timer_heap & previous & previous_state & previous_local & previous_heap &
    Henv & Hcritical & Hsg & Hmask & Hbinding & Hinitial & Hregistered & Hidle & Hstat & Htimer &
    Hchain & Hcaller & Hstate & Hlocal & Hsequential).
  subst environment critical sg mask caller state local.
  assert (Hstart : flag_del_closed (os_init_environment p) tmr_init_empty_local (os_init_sg p)
    (TaskSuspendTask p.(os_init_call)) (os_init_mask p) (os_init_registered_state p) registered_heap).
  { exact (flag_del_captured_heap_owned _ _ registered_heap initial_heap Hregistered). }
  assert (Horigin : p.(os_init_call).(os_sched_call_origin) = BootInvocation)
    by (unfold os_init_source_binding in Hbinding; tauto).
  assert (Hinvocation : p.(os_init_call).(os_sched_call_invocation) = 0%nat)
    by (unfold os_init_source_binding in Hbinding; tauto).
  assert (Hactive : task_invocation_active (os_init_registered_state p).(TskState)
      p.(os_init_call).(os_sched_call_invocation) BootInvocation).
  { rewrite Hinvocation; unfold os_init_registered_state. apply task_begin_invocation_active; exact I. }
  assert (Hall : flag_del_boot_completed_chain p modules p.(os_init_call)
    (os_init_registered_state p) tmr_init_empty_local registered_heap
    previous previous_state previous_local previous_heap).
  { (* Append the fixed, completed initializer calls before the later chain. *)
    assert (Hprefix : flag_del_boot_completed_chain p modules p.(os_init_call)
      (os_init_registered_state p) tmr_init_empty_local registered_heap
      timer timer_state timer_local timer_heap).
    { eapply flag_del_boot_chain_step; [|exact Htimer].
      eapply flag_del_boot_chain_step; [|exact Hstat].
      eapply flag_del_boot_chain_step; [constructor|exact Hidle]. }
    eapply flag_del_boot_chain_append; eassumption. }
  destruct (flag_del_boot_chain_no_waiters _ _ _ _ _ _ _ _ _ _ Hall Hstart
    Horigin eq_refl Hactive (flag_del_boot_registered_no_waiters p))
    as [Hprevious_origin [Hprevious_cut Hprevious_owned]].
  exact (flag_del_boot_sequential_resources (os_init_environment p) previous_local (os_init_sg p)
    sequential previous previous_state (os_init_mask p) previous_heap heap
    Hprevious_origin Hprevious_cut Hsequential Hprevious_owned).
Qed.

Lemma flag_del_source_boot_entry_open : forall environment critical local sg caller mask state frame,
  flag_del_source_boot_entry environment critical local sg caller mask state frame |--
  coq_prop (flag_del_source_cut sg caller state) &&
    (flag_del_closed environment local sg caller mask state ** frame).
Proof.
  intros; unfold flag_del_source_boot_entry.
  sep_apply_l_atomic (flag_del_source_boot_origin_open environment critical local sg caller mask state); entailer!.
Qed.

(** The selected linked-C interpretation is a single public parameter.  A
    source operation fixes its actual callee/arguments, result type and
    complete program before an event is used.  The completion relation is
    the linked implementation's event, not an existential program receipt.
    These conditional C module laws are separate from the CPU/port ABI.
    They apply to adjacent owned heaps of an actual finite source segment;
    they neither promise eventual return nor create resources from an
    unowned world.  A linked implementation must establish these laws for
    the operations/ordinary intervals that it exports. *)
Record FlagDelSourceABI : Type := {
  flag_del_source_operation : Type;
  flag_del_source_result : flag_del_source_operation -> Type;
  flag_del_source_operation_program : forall operation,
    TaskStackCallEnvironment -> StableGlobVars -> TaskSuspendCaller -> Z ->
    program UCOS2_Verify_State (TaskSuspendCaller * flag_del_source_result operation);
  flag_del_source_completed : forall operation,
    TaskStackCallEnvironment -> StableGlobVars -> TaskSuspendCaller -> Z ->
    UCOS2_Verify_State -> (Armv7aContinuation -> Assertion) -> Assertion ->
    flag_del_source_result operation -> TaskSuspendCaller -> UCOS2_Verify_State ->
    (Armv7aContinuation -> Assertion) -> Assertion -> model -> model -> Prop;
  flag_del_source_completed_program : forall operation environment sg call mask before local frame
      result returned current next_local next_frame first last,
    flag_del_source_completed operation environment sg call mask before local frame
      result returned current next_local next_frame first last ->
    flag_del_source_operation_program operation environment sg call mask before (returned,result) current;
  flag_del_source_completed_same_call : forall operation environment sg call mask before local frame
      result returned current next_local next_frame first last,
    flag_del_source_completed operation environment sg call mask before local frame
      result returned current next_local next_frame first last ->
    task_suspend_same_call returned call;
  flag_del_source_completed_owned : forall operation environment sg call mask before local frame
      result returned current next_local next_frame first last,
    flag_del_source_completed operation environment sg call mask before local frame
      result returned current next_local next_frame first last ->
    flag_del_source_operation_program operation environment sg call mask before (returned,result) current ->
    task_suspend_same_call returned call ->
    flag_del_source_cut sg call before ->
    (flag_del_closed environment local sg call mask before ** frame) first ->
    flag_del_source_cut sg returned current /\
    (flag_del_closed environment next_local sg returned mask current ** next_frame) last;
  (** This is the actual finite ordinary C interval, including its local
      reads/stores and permitted interference.  Completed public APIs are
      composed by [flag_del_source_completed], not hidden in this relation.
      Its endpoints retain the current invocation, actual mask, dynamic
      local family, continuation map and the caller's before/after frame. *)
  flag_del_source_interval : TaskStackCallEnvironment -> StableGlobVars ->
    TaskSuspendCaller -> Z -> UCOS2_Verify_State -> (Armv7aContinuation -> Assertion) -> Assertion ->
    TaskSuspendCaller -> Z -> UCOS2_Verify_State -> (Armv7aContinuation -> Assertion) -> Assertion ->
    model -> model -> Prop;
  flag_del_source_interval_same_call : forall environment sg call mask before local frame
      returned next_mask current next_local next_frame first last,
    flag_del_source_interval environment sg call mask before local frame
      returned next_mask current next_local next_frame first last ->
    task_suspend_same_call returned call;
  flag_del_source_interval_owned : forall environment sg call mask before local frame
      returned next_mask current next_local next_frame first last,
    flag_del_source_interval environment sg call mask before local frame
      returned next_mask current next_local next_frame first last ->
    flag_del_source_cut sg call before ->
    (flag_del_closed environment local sg call mask before ** frame) first ->
    flag_del_source_cut sg returned current /\
    (flag_del_closed environment next_local sg returned next_mask current ** next_frame) last;
  (** A nested interrupt saves the currently executing HANDLER on its
      exception stack.  It leaves the already parked task descriptor/map
      intact.  These predicates interpret the real stack-save boundary;
      their ownership law consumes the parent handler and actual storage.
      The saved handler resource is returned in the frame of the nested
      API, retaining its view and pre-exception mask until exception return. *)
  flag_del_saved_execution : TaskStackCallEnvironment -> OsExecutionView -> Z ->
    OsExecutionView -> Assertion;
  flag_del_exception_stack_save : TaskStackCallEnvironment -> OsExecutionView -> Z ->
    OsExecutionView -> model -> model -> Prop;
  flag_del_nested_entry : TaskStackCallEnvironment -> StableGlobVars -> OsExecutionView -> Z ->
    UCOS2_Verify_State -> (Armv7aContinuation -> Assertion) -> Assertion -> OsExecutionView ->
    Assertion -> model -> model -> model -> Prop;
  flag_del_nested_entry_source : forall environment sg outer mask state local frame nested next_frame first saved last,
    flag_del_nested_entry environment sg outer mask state local frame nested next_frame first saved last ->
    nested.(os_execution_context) = KernelInterrupt nested.(os_execution_invocation) outer.(os_execution_context) /\
    nested.(os_execution_origin) = outer.(os_execution_origin) /\
    (state.(SchedState).(isRunning) = true ->
      (kernel_interrupt_depth outer.(os_execution_context) < 255)%nat) /\
    flag_del_exception_stack_save environment outer mask nested first saved /\
    kernel_heap_execution (armv7a_irq_entry_counter_heap_writes sg state) saved last;
  flag_del_nested_entry_owned : forall environment sg outer mask state local frame nested next_frame first saved last,
    flag_del_nested_entry environment sg outer mask state local frame nested next_frame first saved last ->
    flag_del_exception_stack_save environment outer mask nested first saved ->
    kernel_heap_execution (armv7a_irq_entry_counter_heap_writes sg state) saved last ->
    (flag_del_closed environment local sg (TaskSuspendDisabled outer) mask state ** frame) first ->
    (flag_del_closed environment local sg (TaskSuspendDisabled nested) 192
       (armv7a_irq_entry_counter_state state) **
      (flag_del_saved_execution environment outer mask nested ** next_frame)) last;
  (** Boot exceptions branch directly to the handler: no TCB park,
      invocation registration or counter increment occurs.  The source
      event starts at the owned initializer/client-chain endpoint. *)
  flag_del_boot_irq_entry : TaskStackCallEnvironment -> StableGlobVars -> OsSchedCallContext -> Z ->
    UCOS2_Verify_State -> (Armv7aContinuation -> Assertion) -> Assertion -> OsExecutionView ->
    Assertion -> model -> model -> model -> Prop;
  flag_del_boot_irq_entry_source : forall environment sg call mask state local frame handler next_frame first saved last,
    flag_del_boot_irq_entry environment sg call mask state local frame handler next_frame first saved last ->
    call.(os_sched_call_origin) = BootInvocation /\
    handler.(os_execution_context) = KernelInterrupt handler.(os_execution_invocation)
      (KernelCaller call.(os_sched_call_invocation) BootInvocation) /\
    handler.(os_execution_origin) = BootInvocation /\
    state.(IntrState).(intNesting) = 0 /\
    flag_del_exception_stack_save environment (os_sched_execution_view call) mask handler first saved /\
    kernel_heap_execution (armv7a_irq_entry_counter_heap_writes sg state) saved last;
  flag_del_boot_irq_entry_owned : forall environment sg call mask state local frame handler next_frame first saved last,
    flag_del_boot_irq_entry environment sg call mask state local frame handler next_frame first saved last ->
    state.(SchedState).(isRunning) = false ->
    flag_del_exception_stack_save environment (os_sched_execution_view call) mask handler first saved ->
    kernel_heap_execution (armv7a_irq_entry_counter_heap_writes sg state) saved last ->
    (flag_del_closed environment local sg (TaskSuspendTask call) mask state ** frame) first ->
    (flag_del_closed environment local sg (TaskSuspendDisabled handler) 192 state **
      (flag_del_saved_execution environment (os_sched_execution_view call) mask handler ** next_frame)) last;
  (** The SAME interpretation supplies the actual completed-return to next
      entry ABI.  Its source event below starts at the precise completion /
      ordinary-interval endpoint; it cannot choose another predecessor. *)
  flag_del_source_sequential_abi : forall environment : TaskStackCallEnvironment,
    KernelSequentialCallABI environment.(task_stack_call_external) environment.(task_stack_call_platform)
}.

(** Finite composition of ordinary source steps.  The empty interval is
    genuine identity on the SAME call, state, mask, local, frame and heap. *)
Inductive flag_del_source_interval_path (source : FlagDelSourceABI)
    (environment : TaskStackCallEnvironment) (sg : StableGlobVars) :
    TaskSuspendCaller -> Z -> UCOS2_Verify_State -> (Armv7aContinuation -> Assertion) -> Assertion -> model ->
    TaskSuspendCaller -> Z -> UCOS2_Verify_State -> (Armv7aContinuation -> Assertion) -> Assertion -> model -> Prop :=
| flag_del_source_interval_refl : forall caller mask state local frame heap,
    flag_del_source_interval_path source environment sg caller mask state local frame heap
      caller mask state local frame heap
| flag_del_source_interval_step : forall caller mask state local frame heap
      middle middle_mask middle_state middle_local middle_frame middle_heap
      returned next_mask current next_local next_frame last,
    flag_del_source_interval_path source environment sg caller mask state local frame heap
      middle middle_mask middle_state middle_local middle_frame middle_heap ->
    flag_del_source_interval source environment sg middle middle_mask middle_state middle_local middle_frame
      returned next_mask current next_local next_frame middle_heap last ->
    flag_del_source_interval_path source environment sg caller mask state local frame heap
      returned next_mask current next_local next_frame last.

Lemma flag_del_source_interval_path_owned : forall source environment sg caller mask state local frame heap
    returned next_mask current next_local next_frame last,
  flag_del_source_interval_path source environment sg caller mask state local frame heap
    returned next_mask current next_local next_frame last ->
  flag_del_source_cut sg caller state ->
  (flag_del_closed environment local sg caller mask state ** frame) heap ->
  flag_del_source_cut sg returned current /\
    (flag_del_closed environment next_local sg returned next_mask current ** next_frame) last.
Proof.
  intros source environment sg caller mask state local frame heap returned next_mask current next_local next_frame last Hpath.
  induction Hpath; intros Hcut Howned; [auto|].
  destruct (IHHpath Hcut Howned) as [Hmiddle Hmiddle_owned].
  eapply flag_del_source_interval_owned; eassumption.
Qed.

Lemma flag_del_source_isr_root_open : forall environment local sg caller mask state frame,
  flag_del_source_isr_root environment local sg caller mask state frame |--
  coq_prop (flag_del_source_cut sg caller state) &&
    (flag_del_closed environment local sg caller mask state ** frame).
Proof.
  intros environment local sg caller mask state frame heap Hentry.
  destruct Hentry as (view & handler & descriptor & first & saved & initial &
    Hcaller & Hview & Hmask & Hsave & Hcall & Hstate & Hwrites & Hpre & Hpost).
  assert (Hopen : flag_del_isr_entry environment local sg caller mask state frame |--
    coq_prop (flag_del_source_cut sg caller state) &&
    (flag_del_closed environment local sg caller mask state ** frame)).
  { unfold flag_del_isr_entry; Intros v.
    match goal with H : caller = _ /\ _ |- _ => destruct H as [-> Hsource] end.
    unfold flag_del_source_cut, flag_del_handler_source; entailer!. }
  exact (Hopen heap Hpost).
Qed.

Lemma flag_del_nested_entry_source_cut : forall sg outer nested state,
  flag_del_source_cut sg (TaskSuspendDisabled outer) state ->
  nested.(os_execution_context) = KernelInterrupt nested.(os_execution_invocation) outer.(os_execution_context) ->
  nested.(os_execution_origin) = outer.(os_execution_origin) ->
  (state.(SchedState).(isRunning) = true -> (kernel_interrupt_depth outer.(os_execution_context) < 255)%nat) ->
  flag_del_source_cut sg (TaskSuspendDisabled nested) (armv7a_irq_entry_counter_state state).
Proof.
  intros sg outer nested state Hsource Hnested Horigin Hbound.
  destruct Hsource as [[handler [interrupted [Hcontext [Hrunning Hagrees]]]]|
    [handler [interrupted [Hcontext [Hboot [Hrunning [Hzero Hnone]]]]]]].
  - left. unfold sched_disabled_isr_source.
    exists nested.(os_execution_invocation), outer.(os_execution_context).
    split; [exact Hnested|].
    unfold armv7a_irq_entry_counter_state; rewrite Hrunning; cbn [replace_IntrS SchedState IntrState].
    split; [exact Hrunning|].
    unfold kernel_interrupt_nesting_agrees in *.
    specialize (Hagrees eq_refl); specialize (Hbound Hrunning).
    rewrite Hnested; intro Htrue.
    change ((state.(IntrState).(intNesting) + 1) mod 256 =
      Z.of_nat (S (kernel_interrupt_depth outer.(os_execution_context)))).
    rewrite Hagrees, Nat2Z.inj_succ.
    pose proof (Nat2Z.is_nonneg (kernel_interrupt_depth outer.(os_execution_context))).
    apply Nat2Z.inj_lt in Hbound.
    rewrite Z.mod_small by lia; lia.
  - right. unfold armv7a_irq_entry_counter_state; rewrite Hrunning.
    exists nested.(os_execution_invocation), outer.(os_execution_context).
    split; [exact Hnested|]. split; [congruence|].
    exact (conj Hrunning (conj Hzero Hnone)).
Qed.

Lemma flag_del_boot_irq_entry_source_cut : forall sg call handler state,
  flag_del_source_cut sg (TaskSuspendTask call) state ->
  call.(os_sched_call_origin) = BootInvocation ->
  handler.(os_execution_context) = KernelInterrupt handler.(os_execution_invocation)
    (KernelCaller call.(os_sched_call_invocation) BootInvocation) ->
  handler.(os_execution_origin) = BootInvocation ->
  state.(IntrState).(intNesting) = 0 ->
  flag_del_source_cut sg (TaskSuspendDisabled handler) state.
Proof.
  intros sg call handler state Hsource Hboot Hcontext Horigin Hzero.
  unfold flag_del_source_cut in Hsource; rewrite Hboot in Hsource.
  destruct Hsource as [Hrunning [Hactive Hnone]].
  right. exists handler.(os_execution_invocation),
    (KernelCaller call.(os_sched_call_invocation) BootInvocation).
  exact (conj Hcontext (conj Horigin (conj Hrunning (conj Hzero Hnone)))).
Qed.

(** Each chain starts with the actual publication/restore, initializer, or
    IRQ save/park root.  There is no constructor from a merely closed world.
    A task's completed API and its next-entry event are one composition step;
    their shared returned heap/state is not existentially detached from the
    preceding root.  An ISR stays in its actual handler execution view and
    never passes through Task invocation registration. *)
Inductive flag_del_source_chain (source : FlagDelSourceABI)
    (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources) (sg : StableGlobVars) :
    TaskSuspendCaller -> Z -> UCOS2_Verify_State -> (Armv7aContinuation -> Assertion) -> Assertion -> model -> Prop :=
| flag_del_source_chain_initial : forall caller mask state local frame heap,
    flag_del_source_initial_root environment local sg caller mask state frame heap ->
    flag_del_source_chain source environment critical sg caller mask state local frame heap
| flag_del_source_chain_boot : forall caller mask state local frame heap,
    flag_del_source_boot_entry environment critical local sg caller mask state frame heap ->
    flag_del_source_chain source environment critical sg caller mask state local frame heap
| flag_del_source_chain_isr : forall caller mask state local frame heap,
    flag_del_source_isr_root environment local sg caller mask state frame heap ->
    flag_del_source_chain source environment critical sg caller mask state local frame heap
| flag_del_source_chain_interval : forall caller mask state local frame heap
      returned next_mask current next_local next_frame last,
    flag_del_source_chain source environment critical sg caller mask state local frame heap ->
    flag_del_source_interval_path source environment sg caller mask state local frame heap
      returned next_mask current next_local next_frame last ->
    flag_del_source_chain source environment critical sg returned next_mask current next_local next_frame last
| flag_del_source_chain_task_return : forall call mask state local frame heap operation result
      returned current next_local next_frame return_heap previous next_mask previous_state
      previous_local previous_frame previous_heap last,
    flag_del_source_chain source environment critical sg (TaskSuspendTask call) mask state local frame heap ->
    flag_del_source_completed source operation environment sg (TaskSuspendTask call) mask state local frame
      result (TaskSuspendTask returned) current next_local next_frame heap return_heap ->
    flag_del_source_interval_path source environment sg (TaskSuspendTask returned) mask current next_local next_frame return_heap
      (TaskSuspendTask previous) next_mask previous_state previous_local previous_frame previous_heap ->
    kernel_sequential_call_source (flag_del_source_sequential_abi source environment) previous
      previous_state.(TskState).(taskLifecycle).(taskNextInvocation) previous_heap last ->
    flag_del_source_chain source environment critical sg
      (TaskSuspendTask (kernel_sequential_call previous previous_state.(TskState).(taskLifecycle).(taskNextInvocation)))
      next_mask (flag_del_registered_state previous previous_state) previous_local previous_frame last
| flag_del_source_chain_handler_return : forall view mask state local frame heap operation result
      returned current next_local next_frame last,
    flag_del_source_chain source environment critical sg (TaskSuspendDisabled view) mask state local frame heap ->
    flag_del_source_completed source operation environment sg (TaskSuspendDisabled view) mask state local frame
      result (TaskSuspendDisabled returned) current next_local next_frame heap last ->
    flag_del_source_chain source environment critical sg (TaskSuspendDisabled returned) mask current next_local next_frame last
| flag_del_source_chain_nested_irq : forall outer mask state local frame heap nested next_frame saved last,
    flag_del_source_chain source environment critical sg (TaskSuspendDisabled outer) mask state local frame heap ->
    flag_del_nested_entry source environment sg outer mask state local frame nested next_frame heap saved last ->
    flag_del_source_chain source environment critical sg (TaskSuspendDisabled nested) 192
      (armv7a_irq_entry_counter_state state) local
      (flag_del_saved_execution source environment outer mask nested ** next_frame) last
| flag_del_source_chain_boot_irq : forall call mask state local frame heap handler next_frame saved last,
    flag_del_source_chain source environment critical sg (TaskSuspendTask call) mask state local frame heap ->
    flag_del_boot_irq_entry source environment sg call mask state local frame handler next_frame heap saved last ->
    flag_del_source_chain source environment critical sg (TaskSuspendDisabled handler) 192 state local
      (flag_del_saved_execution source environment (os_sched_execution_view call) mask handler ** next_frame) last.

Lemma flag_del_source_chain_owned : forall source environment critical sg caller mask state local frame heap,
  flag_del_source_chain source environment critical sg caller mask state local frame heap ->
  flag_del_source_cut sg caller state /\
    (flag_del_closed environment local sg caller mask state ** frame) heap.
Proof.
  intros source environment critical sg caller mask state local frame heap Hchain.
  induction Hchain.
  - exact (flag_del_source_initial_root_open environment local sg caller mask state frame heap H).
  - exact (flag_del_source_boot_entry_open environment critical local sg caller mask state frame heap H).
  - exact (flag_del_source_isr_root_open environment local sg caller mask state frame heap H).
  - destruct IHHchain as [Hcut Howned].
    eapply flag_del_source_interval_path_owned; eassumption.
  - destruct IHHchain as [Hcut Howned].
    pose proof (flag_del_source_completed_program source operation environment sg (TaskSuspendTask call)
      mask state local frame result (TaskSuspendTask returned) current next_local next_frame heap return_heap H) as Hprogram.
    pose proof (flag_del_source_completed_same_call source operation environment sg (TaskSuspendTask call)
      mask state local frame result (TaskSuspendTask returned) current next_local next_frame heap return_heap H) as Hsame.
    destruct (flag_del_source_completed_owned source operation environment sg (TaskSuspendTask call)
      mask state local frame result (TaskSuspendTask returned) current next_local next_frame
      heap return_heap H Hprogram Hsame Hcut Howned) as [Hreturned Hreturned_owned].
    destruct (flag_del_source_interval_path_owned source environment sg (TaskSuspendTask returned) mask current
      next_local next_frame return_heap (TaskSuspendTask previous) next_mask previous_state previous_local previous_frame
      previous_heap H0 Hreturned Hreturned_owned) as [Hprevious Hprevious_owned].
    assert (Hnext : flag_del_source_sequential_owner environment previous_local sg
      (TaskSuspendTask (kernel_sequential_call previous previous_state.(TskState).(taskLifecycle).(taskNextInvocation)))
      next_mask (flag_del_registered_state previous previous_state) previous_frame last).
    { exists (flag_del_source_sequential_abi source environment), previous, previous_state, previous_heap.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact H1|].
      exact (conj Hprevious Hprevious_owned). }
    exact (flag_del_source_sequential_owner_open environment previous_local sg _ next_mask _ previous_frame last Hnext).
  - destruct IHHchain as [Hcut Howned].
    pose proof (flag_del_source_completed_program source operation environment sg (TaskSuspendDisabled view)
      mask state local frame result (TaskSuspendDisabled returned) current next_local next_frame heap last H) as Hprogram.
    pose proof (flag_del_source_completed_same_call source operation environment sg (TaskSuspendDisabled view)
      mask state local frame result (TaskSuspendDisabled returned) current next_local next_frame heap last H) as Hsame.
    eapply flag_del_source_completed_owned; eassumption.
  - destruct IHHchain as [Hcut Howned].
    destruct (flag_del_nested_entry_source source environment sg outer mask state local frame
      nested next_frame heap saved last H) as [Hcontext [Horigin [Hdepth [Hsave Hcounter]]]].
    split.
    + eapply flag_del_nested_entry_source_cut; eassumption.
    + eapply flag_del_nested_entry_owned; eassumption.
  - destruct IHHchain as [Hcut Howned].
    destruct (flag_del_boot_irq_entry_source source environment sg call mask state local frame
      handler next_frame heap saved last H) as [Hboot [Hcontext [Horigin [Hzero [Hsave Hcounter]]]]].
    assert (Hrunning : state.(SchedState).(isRunning) = false).
    { unfold flag_del_source_cut in Hcut; rewrite Hboot in Hcut; tauto. }
    split.
    + eapply flag_del_boot_irq_entry_source_cut; eassumption.
    + eapply flag_del_boot_irq_entry_owned; eassumption.
Qed.

Definition flag_del_source_public_entry source environment critical local sg caller mask state pointer view error frame : Assertion :=
  flag_del_source_chain source environment critical sg caller mask state local
    (flag_del_entry_frame pointer view error frame).

Lemma flag_del_source_public_entry_open : forall source environment critical local sg caller mask state pointer view error frame,
  flag_del_source_public_entry source environment critical local sg caller mask state pointer view error frame |--
  coq_prop (flag_del_source_cut sg caller state) &&
    (flag_del_closed environment local sg caller mask state **
      flag_del_raw_type pointer view ** (error # UChar |->_) ** frame).
Proof.
  intros source environment critical local sg caller mask state pointer view error frame heap Hsource.
  destruct (flag_del_source_chain_owned source environment critical sg caller mask state local
    (flag_del_entry_frame pointer view error frame) heap Hsource) as [Hcut Howned].
  assert (Hreorder : flag_del_closed environment local sg caller mask state **
    flag_del_entry_frame pointer view error frame |--
    coq_prop (flag_del_source_cut sg caller state) &&
    (flag_del_closed environment local sg caller mask state ** flag_del_raw_type pointer view **
      (error # UChar |->_) ** frame)).
  { unfold flag_del_entry_frame; entailer!. }
  exact (Hreorder heap Howned).
Qed.


Definition flag_del_source_prefix_facts environment critical sg caller mask view pointer opt name before
    observed active saved acquired (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Prop :=
  flag_del_prefix_facts environment critical sg caller mask view pointer opt name before
    observed active saved acquired X /\
  UCOS2_state_inv sg acquired /\ flag_del_source_cut sg active acquired /\
  flag_del_source_cut sg caller before /\
  flag_del_boot_handler_preserved caller active before acquired.

Lemma flag_del_source_prefix_disabled_boot : forall environment critical sg view mask group pointer opt name before
    observed active saved acquired X,
  flag_del_source_prefix_facts environment critical sg (TaskSuspendDisabled view) mask group pointer opt name
    before observed active saved acquired X ->
  active = TaskSuspendDisabled view /\ flag_del_boot_handler_source view acquired.
Proof.
  intros environment critical sg view mask group pointer opt name before observed active saved acquired X
    [Hprefix [Hvalid [Hacquired [Hbefore Hphase]]]].
  destruct Hprefix as [Hpointer [Hzero [Hselected [Htype [Heffect [Hsame [Hmask Hsafe]]]]]]].
  destruct active as [call|next]; [contradiction|].
  cbn [task_suspend_same_call] in Hsame; subst next.
  split; [reflexivity|]. apply Hphase.
  destruct Hbefore as [Hisr|Hboot]; [|exact Hboot].
  destruct Hisr as [handler [interrupted [Hcontext [Hrunning Hagrees]]]].
  rewrite Hcontext in Hagrees.
  pose proof (kernel_running_interrupt_nesting_positive handler interrupted before.(IntrState) Hagrees).
  unfold os_sched_ints in Hzero; lia.
Qed.

Lemma flag_del_acquired_no_waiter_head : forall sg acquired id image,
  UCOS2_state_inv sg acquired -> flag_state_has_no_waiters acquired.(FlagState) ->
  acquired.(FlagState).(flagImages) id = Some image -> image.(flagImageType) = 5 ->
  image.(flagImageHead) = 0.
Proof.
  intros sg acquired id image Hvalid [Hgroups Hnodes] Himage Htype.
  destruct (flag_query_state_configuration sg acquired Hvalid) as [_ [_ Hflags]].
  destruct (flag_name_set_pool_type_is_live sg acquired.(FlagState) id image Hflags Himage Htype)
    as [group Hgroup].
  apply (proj2 (flag_del_live_head_empty sg acquired.(FlagState) id group image Hflags Hgroup Himage)).
  exact (Hgroups id group Hgroup).
Qed.

Lemma flag_del_boot_acquired_waiting_zero : forall sg call acquired id image,
  call.(os_sched_call_origin) = BootInvocation ->
  flag_del_source_cut sg (TaskSuspendTask call) acquired ->
  UCOS2_state_inv sg acquired ->
  acquired.(FlagState).(flagImages) id = Some image -> image.(flagImageType) = 5 ->
  flag_del_waiting image = 0.
Proof.
  intros sg call acquired id image Horigin Hcut Hvalid Himage Htype.
  unfold flag_del_source_cut in Hcut; rewrite Horigin in Hcut.
  destruct Hcut as [_ [_ Hnone]].
  unfold flag_del_waiting.
  rewrite (flag_del_acquired_no_waiter_head sg acquired id image Hvalid Hnone Himage Htype); reflexivity.
Qed.

Lemma flag_del_boot_handler_acquired_waiting_zero : forall sg view acquired id image,
  flag_del_boot_handler_source view acquired ->
  UCOS2_state_inv sg acquired ->
  acquired.(FlagState).(flagImages) id = Some image -> image.(flagImageType) = 5 ->
  flag_del_waiting image = 0.
Proof.
  intros sg view acquired id image [handler [interrupted [_ [_ [_ [_ Hnone]]]]]] Hvalid Himage Htype.
  unfold flag_del_waiting.
  rewrite (flag_del_acquired_no_waiter_head sg acquired id image Hvalid Hnone Himage Htype); reflexivity.
Qed.

Lemma flag_del_release_preserves_no_waiters : forall sg flags id image name,
  flag_state_has_no_waiters flags ->
  flag_state_has_no_waiters (flag_release sg flags id image name).
Proof.
  intros sg flags id image name [Hgroups Hnodes]; split; [|exact Hnodes].
  intros other group Hgroup; cbn in Hgroup; unfold kernel_map_set in Hgroup.
  destruct (Z.eq_dec other id); [discriminate|].
  exact (Hgroups other group Hgroup).
Qed.

Lemma flag_del_task_rdy_preserves_ready_nonempty : forall sg before node ready after,
  before.(SchedState).(readyList) <> [] ->
  flag_task_rdy sg before node 0 PendAbort = Some (ready, after) ->
  after.(SchedState).(readyList) <> [].
Proof.
  intros sg before node ready after Hready Hstep.
  destruct (flag_task_rdy_result sg before node 0 PendAbort ready after Hstep)
    as [waiter [flags [old [Hunlink [Hlookup [Hafter Hresult]]]]]].
  subst after; unfold flag_wake_state, sched_wake_task; cbn.
  destruct (is_effectively_ready (task_clear_flag_status (stat old)) 0); [|exact Hready].
  intro Hempty.
  assert (Hin : In waiter.(flagTask)
    (insert_sorted_by (sched_task_key sg before.(TskState)) waiter.(flagTask)
      (remove_Z_eqb waiter.(flagTask) before.(SchedState).(readyList)))).
  { apply insert_sorted_by_in; left; reflexivity. }
  rewrite Hempty in Hin; contradiction.
Qed.

Lemma flag_del_closed_nesting_equiv__entry_and_early_returns : forall environment local sg caller mask state,
  flag_del_closed environment local sg caller mask state --||--
  (sg.(g_OSIntNesting) # UChar |-> os_sched_ints state **
   flag_del_nesting_frame environment local sg caller mask state).
Proof.
  intros.
  unfold flag_del_closed, kernel_continuation_inv, kernel_program_fields_inv,
    kernel_program_fields_rep, UCOS2_fields_raw_rep, UCOS2_raw_rep_missing_flag,
    flag_del_nesting_frame, os_sched_fields_capsules, os_sched_ints.
  rewrite (UCOS2_raw_rep_missing_module_split_module sg state FlagModule InterruptModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  unfold interrupt_inv, store_int_state.
  split.
  - entailer!.
  - Intros.
    prop_apply_p (UCOS2_C_Rules.store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState state))).
    Intros.
    prop_apply_p (UCOS2_C_Rules.store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState state))).
    Intros.
    unfold interrupt_in_range; entailer!.
Qed.
Lemma flag_del_closed_type_cut_equiv__entry_and_early_returns : forall environment local sg caller mask p view state image,
  p <> 0 -> flag_query_address sg p view -> flag_query_selected view state image ->
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  (flag_del_closed environment local sg caller mask state ** flag_del_raw_type p view) --||--
  flag_del_type_cut environment local sg caller mask p view state image.
Proof.
  intros environment local sg caller mask p [original|id] state image Hp Haddr Hselected Henabled.
  - cbn [flag_query_selected] in Hselected; subst image.
    unfold flag_del_raw_type; rewrite (proj2 (Z.eqb_neq _ _) Hp).
    unfold flag_del_closed, flag_del_type_cut, flag_del_type_frame,
      kernel_continuation_inv, os_sched_fields_capsules, kernel_program_fields_inv.
    split; entailer!.
  - destruct Haddr as [-> Hid]; cbn [flag_query_selected] in Hselected.
    unfold flag_del_raw_type; rewrite (proj2 (Z.eqb_neq _ _) Hp).
    split.
    + unfold flag_del_closed, kernel_continuation_inv.
      rewrite kernel_program_fields_inv_split_unmap; Intros.
      sep_apply_l_atomic (flag_del_pool_fields_split sg state id image Henabled Hselected).
      unfold flag_del_type_cut, flag_del_type_frame, flag_group_rep,
        flag_query_group_without_type, os_sched_fields_capsules; entailer!.
    + unfold flag_del_type_cut, flag_del_type_frame; Intros.
      unfold flag_del_closed, kernel_continuation_inv.
      rewrite kernel_program_fields_inv_split_unmap.
      match goal with H : UCOS2_state_inv sg state /\ _ |- _ =>
        destruct H as [Hinv Hcover]
      end.
      entailer!.
      sep_apply_r_atomic (flag_del_pool_fields_merge_original sg state id image Henabled Hinv Hselected).
      unfold flag_group_rep, flag_query_group_without_type, os_sched_fields_capsules; entailer!.
Qed.
Lemma flag_del_prefix_no_schedule_implies_program__entry_and_early_returns : forall environment critical sg caller mask view p option name
    before result returned current,
  flag_del_prefix_program environment critical sg caller mask view p option name
    before ((result, false), returned) current ->
  flag_del_program environment critical sg caller mask view p option name before result current.
Proof.
  intros environment critical sg caller mask view p option name before result returned current Hprefix.
  unfold flag_del_program.
  exists ((result, false), returned), current; split; [exact Hprefix|].
  split; reflexivity.
Qed.
Lemma flag_del_masked_state_inv__acquired_type_and_group_fields :
  forall environment critical local sg caller saved acquired state,
  flag_del_masked environment critical local sg caller saved acquired state |--
    coq_prop (UCOS2_state_inv sg state).
Proof.
  intros; unfold flag_del_masked, kernel_continuation_inv, kernel_program_fields_inv.
  Intros; entailer!.
Qed.
Lemma flag_del_masked_type_cut_split__acquired_type_and_group_fields :
  forall environment critical local sg caller saved acquired state p id image,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  p = flag_pool_addr sg id ->
  state.(FlagState).(flagImages) id = Some image ->
  flag_del_masked environment critical local sg caller saved acquired state |--
    flag_del_masked_type_cut environment critical local sg caller saved acquired p id state image.
Proof.
  intros environment critical local sg caller saved acquired state p id image Henabled Haddress Himage.
  subst p.
  unfold flag_del_masked, kernel_continuation_inv, flag_del_masked_type_cut.
  rewrite kernel_program_fields_inv_split_unmap.
  Intros.
  sep_apply (flag_del_pool_fields_split sg state id image Henabled Himage).
  unfold flag_del_type_frame, flag_group_rep, flag_query_group_without_type, os_sched_fields_capsules.
  Intros; entailer!.
Qed.
Lemma flag_del_masked_type_cut_merge__acquired_type_and_group_fields :
  forall environment critical local sg caller saved acquired state p id image,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  p = flag_pool_addr sg id ->
  state.(FlagState).(flagImages) id = Some image ->
  flag_del_masked_type_cut environment critical local sg caller saved acquired p id state image |--
    flag_del_masked environment critical local sg caller saved acquired state.
Proof.
  intros environment critical local sg caller saved acquired state p id image Henabled Haddress Himage.
  subst p.
  unfold flag_del_masked, kernel_continuation_inv, flag_del_masked_type_cut,
    flag_del_type_frame, os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap.
  Intros.
  entailer!.
  sep_apply_r_atomic (flag_del_pool_fields_merge_original sg state id image Henabled ltac:(tauto) Himage).
  unfold flag_group_rep, flag_query_group_without_type; entailer!.
Qed.
Lemma flag_del_masked_type_cut_group_cut_equiv__acquired_type_and_group_fields :
  forall environment critical local sg caller saved acquired state p id image,
  flag_del_build_context sg ->
  flag_del_masked_type_cut environment critical local sg caller saved acquired p id state image --||--
    flag_del_group_cut environment critical local sg caller saved acquired p id state image.
Proof.
  intros environment critical local sg caller saved acquired state p id image Hbuild.
  pose proof (flag_del_build_configuration sg Hbuild) as Hconfig.
  unfold flag_del_masked_type_cut, flag_del_group_cut, flag_del_type_frame,
    flag_query_group_without_type, flag_del_group_padding,
    flag_word_rep, flag_word_bytes, flag_group_name_offset, kernel_align4.
  rewrite Hconfig.
  cbn [selected_kernel_configuration cfgFlagBits cfgFlagNames].
  change (16 / 8) with 2.
  change ((8 + flag_word_bytes selected_kernel_configuration + 3) / 4 * 4) with 12.
  cbn [Z.eqb Pos.eqb].
  replace (p + 8 + 2) with (p + 10) by lia.
  split; entailer!.
Qed.
Lemma flag_del_release_preserves_source_cut__drain_and_release_results : forall sg caller state id image name,
  flag_del_source_cut sg caller state ->
  flag_del_source_cut sg caller (flag_del_release_state sg state id image name).
Proof.
  intros sg [call|view] state id image name Hcut.
  - unfold flag_del_source_cut in *.
    destruct (os_sched_call_origin call).
    + destruct Hcut as [Hrun [Hactive Hnone]].
      split; [exact Hrun|]. split; [exact Hactive|].
      apply flag_del_release_preserves_no_waiters; exact Hnone.
    + exact Hcut.
  - unfold flag_del_source_cut, flag_del_handler_source in *.
    destruct Hcut as [Hisr|Hboot].
    + left; exact Hisr.
    + right. destruct Hboot as [handler [interrupted [Hcontext [Horigin [Hrun [Hnest Hnone]]]]]].
      exists handler, interrupted.
      split; [exact Hcontext|]. split; [exact Horigin|].
      split; [exact Hrun|]. split; [exact Hnest|].
      apply flag_del_release_preserves_no_waiters; exact Hnone.
Qed.
Lemma flag_del_group_merge_original__drain_and_release_results :
  forall environment critical local sg caller saved acquired p id state image,
  p = flag_pool_addr sg id ->
  state.(FlagState).(flagImages) id = Some image ->
  sg.(osKernelConfig).(cfgFlagNames) = true ->
  flag_del_group_cut environment critical local sg caller saved acquired p id state image |--
  flag_del_masked environment critical local sg caller saved acquired state.
Proof.
  intros environment critical local sg caller saved acquired p id state image Hpointer Himage Hnames.
  subst p.
  unfold flag_del_group_cut, flag_del_masked, kernel_continuation_inv, os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap. Intros.
  assert (Hinv : UCOS2_state_inv sg state) by tauto.
  destruct (flag_query_state_configuration sg state Hinv) as [Henabled [Hbits Hvalid]].
  pose proof (flag_del_pool_fields_merge_original sg state id image Henabled Hinv Himage) as Hmerge.
  rewrite (flag_del_group_fields _ _ image Hbits Hnames) in Hmerge.
  sep_apply_l_atomic Hmerge. entailer!.
Qed.
Lemma flag_del_group_merge_released__drain_and_release_results :
  forall environment critical local sg caller saved acquired p id state group image name,
  p = flag_pool_addr sg id ->
  state.(FlagState).(flagImages) id = Some image ->
  state.(FlagState).(flagUsed) id = Some group -> group.(flagWaitOrder) = nil ->
  sg.(osKernelConfig).(cfgFlagNames) = true ->
  p # UChar |-> 0 ** (p + 4) # Ptr |-> flag_del_free_head_state sg state **
  (p + 8) # UShort |-> 0 ** (p + 12) # Ptr |-> name **
  sg.(g_OSFlagFreeList) # Ptr |-> p **
  flag_del_group_frame environment critical local sg caller saved acquired p id state image |--
  flag_del_masked environment critical local sg caller saved acquired
    (flag_del_release_state sg state id image name).
Proof.
  intros environment critical local sg caller saved acquired p id state group image name
    Hpointer Himage Hgroup Hempty Hnames. subst p.
  unfold flag_del_group_frame, flag_del_masked, kernel_continuation_inv, os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap. Intros.
  assert (Hinv : UCOS2_state_inv sg state) by tauto.
  destruct (flag_query_state_configuration sg state Hinv) as [Henabled [Hbits Hvalid]].
  unfold flag_del_free_head_state.
  sep_apply_l_atomic (flag_del_group_merge_deleted (osKernelConfig sg) (flag_pool_addr sg id) image
    (flag_del_free_head sg (FlagState state)) name Hbits Hnames).
  sep_apply_l_atomic (flag_del_pool_fields_merge_released sg state id group image name Hinv Hgroup Himage Hempty).
  cbn [flag_del_release_state replace_FlagS TskState]. entailer!.
Qed.
Lemma flag_del_masked_split_group__drain_and_release_results :
  forall environment critical local sg caller saved acquired p id state image,
  p = flag_pool_addr sg id ->
  state.(FlagState).(flagImages) id = Some image ->
  sg.(osKernelConfig).(cfgFlagNames) = true ->
  flag_del_masked environment critical local sg caller saved acquired state |--
  flag_del_group_cut environment critical local sg caller saved acquired p id state image.
Proof.
  intros environment critical local sg caller saved acquired p id state image Hpointer Himage Hnames.
  subst p.
  unfold flag_del_masked, kernel_continuation_inv, flag_del_group_cut, os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap.
  assert (Hvalidp : UCOS2_fields_inv sg state |-- coq_prop (UCOS2_state_inv sg state) && UCOS2_fields_inv sg state).
  { unfold UCOS2_fields_inv; entailer!. }
  Intros. sep_apply_l_atomic Hvalidp. Intros.
  assert (Hinv : UCOS2_state_inv sg state) by tauto.
  destruct (flag_query_state_configuration sg state Hinv) as [Henabled [Hbits Hvalid]].
  sep_apply_l_atomic (flag_del_pool_fields_split sg state id image Henabled Himage).
  rewrite (flag_del_group_fields _ _ image Hbits Hnames). entailer!.
Qed.
Lemma flag_del_masked_implies_state_inv__drain_and_release_results :
  forall environment critical local sg caller saved acquired state,
  flag_del_masked environment critical local sg caller saved acquired state |--
  coq_prop (UCOS2_state_inv sg state) &&
  flag_del_masked environment critical local sg caller saved acquired state.
Proof.
  intros; unfold flag_del_masked, kernel_continuation_inv, kernel_program_fields_inv; entailer!.
Qed.
Lemma flag_del_pool_argument_implies_layout_address__drain_and_release_results : forall sg pointer view before observed id,
  flag_del_argument sg pointer view before observed -> pointer <> 0 -> view = FlagQueryPool id ->
  flag_del_layout pointer /\ pointer = flag_pool_addr sg id.
Proof.
  intros sg pointer view before observed id [Hzero|[_ [Hlayout [Haddress _]]]] Hnonzero Hview;
    [contradiction|]. subst view. exact (conj Hlayout (proj1 Haddress)).
Qed.
Lemma flag_del_loop_zero_head_remaining_empty__drain_and_release_results : forall sg caller acquired id order visited remaining current,
  UCOS2_state_inv sg current ->
  flag_del_source_loop_facts sg caller acquired id order visited remaining current 0 ->
  remaining = nil /\ order = visited /\ exists image,
    current.(FlagState).(flagImages) id = Some image.
Proof.
  intros sg caller acquired id order visited remaining current Hinv
    [[Horder [Hfold [[group [Hgroup Hremaining]] [Hhead Hcall]]]] Hsource].
  destruct (flag_query_state_configuration sg current Hinv) as [_ [_ Hflags]].
  destruct Hflags as [_ [_ [_ [Hused [_ Hnodes]]]]].
  destruct (Hused id group Hgroup) as [_ [_ [Hwait [image [Himage Hfields]]]]].
  assert (Hnil : remaining = nil).
  { destruct remaining as [|node rest]; [reflexivity|].
    subst node.
    destruct (Hwait nil 0 rest Hremaining) as [waiter [Hnode Hrest]].
    exfalso. exact (proj1 (Hnodes 0 waiter Hnode) eq_refl). }
  split; [exact Hnil|]. split.
  - rewrite Hnil, app_nil_r in Horder; exact Horder.
  - exists image; exact Himage.
Qed.
Lemma flag_del_abort_waiters_preserves_validity__waiter_loop_and_publication : forall sg nodes before after,
  UCOS2_state_inv sg before -> flag_del_abort_waiters sg nodes before = Some after ->
  UCOS2_state_inv sg after.
Proof.
  intros sg nodes; induction nodes as [|node rest IH]; intros before after Hvalid Hfold.
  - cbn [flag_del_abort_waiters] in Hfold; injection Hfold as <-; exact Hvalid.
  - cbn [flag_del_abort_waiters] in Hfold.
    destruct (flag_task_rdy sg before node 0 PendAbort) as [[ready next]|] eqn:Hstep; [|discriminate].
    eapply IH; [eapply UCOS2_flag_task_rdy_preserves_validity; eassumption|exact Hfold].
Qed.
Lemma flag_del_step_preserves_source_cut__waiter_loop_and_publication : forall sg before node after caller,
  flag_del_step sg before node after ->
  flag_del_source_cut sg caller before -> flag_del_source_cut sg caller after.
Proof.
  intros sg before node after caller [ready Hstep] Hsource.
  destruct (flag_task_rdy_result sg before node 0 PendAbort ready after Hstep)
    as [waiter [flags [old [Hunlink [Hold [Hafter Hready]]]]]].
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink)) as Hwaiter.
  assert (Hrun : after.(SchedState).(isRunning) = before.(SchedState).(isRunning)) by (subst after; reflexivity).
  assert (Hcurrent : after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID)) by (subst after; reflexivity).
  assert (Hinterrupts : after.(IntrState) = before.(IntrState)) by (subst after; reflexivity).
  assert (Hstacks : after.(TskState).(parkedTaskStacks) = before.(TskState).(parkedTaskStacks)) by (subst after; reflexivity).
  destruct caller as [call|view].
  - unfold flag_del_source_cut in *; destruct (os_sched_call_origin call) eqn:Horigin.
    + destruct Hsource as [_ [_ [_ Hnone]]]; specialize (Hnone node); congruence.
    + destruct Hsource as [Hrunning [Hcall [Hclean [Hnone Hnonempty]]]].
      split; [rewrite Hrun; exact Hrunning|].
      unfold flag_api_task_entry_observation; split.
      * destruct Hcall as [Hidentity [Hactive Hcur]].
        unfold kernel_call_task_source; split; [exact Hidentity|]; split.
        -- eapply FlagPendSchedulerResources.flag_task_rdy_preserves_invocation_active; eassumption.
        -- unfold task_execution_current in *; rewrite Horigin in *; rewrite Hcurrent; exact Hcur.
      * split.
        -- destruct Hclean as [task [Htask [Hg Hclean]]].
           subst after; unfold flag_task_clean_at.
           destruct (Z.eqb (stackLeaseSlot (os_sched_call_stack call)) (flagTask waiter)) eqn:Heq.
           ++ apply Z.eqb_eq in Heq.
              assert (task = old) by (rewrite Heq in Htask; congruence); subst task.
              exists (task_flag_wake old 0 PendAbort).
              split; [change ((if Z.eqb (stackLeaseSlot (os_sched_call_stack call)) (flagTask waiter) then Some (task_flag_wake old 0 PendAbort) else before.(TskState).(inUsedTaskStates) (stackLeaseSlot (os_sched_call_stack call))) = Some (task_flag_wake old 0 PendAbort)); rewrite Heq, Z.eqb_refl; reflexivity|].
              split; [exact Hg|reflexivity].
           ++ exists task; split; [change ((if Z.eqb (stackLeaseSlot (os_sched_call_stack call)) (flagTask waiter) then Some (task_flag_wake old 0 PendAbort) else before.(TskState).(inUsedTaskStates) (stackLeaseSlot (os_sched_call_stack call))) = Some task); rewrite Heq; exact Htask|auto].
        -- split; [rewrite Hstacks; exact Hnone|].
           eapply flag_del_task_rdy_preserves_ready_nonempty; eassumption.
  - unfold flag_del_source_cut, flag_del_handler_source in *.
    destruct Hsource as [Hisr|Hboot].
    + left; destruct Hisr as [handler [interrupted [Hcontext [Hrunning Hnesting]]]].
      exists handler, interrupted; rewrite Hrun, Hinterrupts; auto.
    + destruct Hboot as [handler [interrupted [_ [_ [_ [_ [_ Hnone]]]]]]].
      specialize (Hnone node); congruence.
Qed.
Lemma flag_del_local_prefix_append__waiter_loop_and_publication : forall sg first rest before original middle local after returned,
  flag_del_local_prefix sg first before original middle local ->
  flag_del_local_prefix sg rest middle local after returned ->
  flag_del_local_prefix sg (first ++ rest) before original after returned.
Proof.
  intros sg first; induction first as [|node first IH]; intros rest before original middle local after returned Hfirst Hrest.
  - destruct Hfirst as [-> ->]; exact Hrest.
  - cbn [flag_del_local_prefix] in Hfirst |- *.
    destruct Hfirst as [waiter [lease [fragments [next [Hnode [Hloan [Hstep Hfirst]]]]]]].
    exists waiter, lease, fragments, next; split; [exact Hnode|].
    split; [exact Hloan|]. split; [exact Hstep|].
    eapply IH; eassumption.
Qed.
Lemma flag_del_running_source_sched_cut__save_restore_call_cuts : forall sg call state,
  os_sched_call_origin call <> BootInvocation ->
  flag_del_source_cut sg (TaskSuspendTask call) state ->
  UCOS2_state_inv sg state -> flag_del_stack_layout sg ->
  os_sched_call_cut sg call state.
Proof.
  intros sg call state Hrunning Hcut Hvalid Hlayout.
  unfold flag_del_source_cut in Hcut.
  destruct (os_sched_call_origin call) eqn:Horigin; [contradiction|].
  destruct Hcut as [_ [Hsource [_ [Havailable Hready]]]].
  split; [intros _; exact Hready|].
  intros _; split; [|exact Havailable].
  apply sched_call_protocol_spec.kernel_call_task_source_current_storage;
    [exact Hvalid|exact Hsource|apply Hlayout].
Qed.
Lemma flag_del_protected_always_no_waiters_unscheduled__save_restore_call_cuts :
  forall sg view pointer name acquired scheduled released,
  UCOS2_state_inv sg acquired -> flag_state_has_no_waiters (FlagState acquired) ->
  flag_del_protected_result sg view pointer 1 name acquired 0 0 scheduled released ->
  scheduled = false.
Proof.
  intros sg view pointer name acquired scheduled released Hvalid Hnone Hresult.
  unfold flag_del_protected_result, flag_del_protected in Hresult.
  destruct Hresult as [image [Hselected Hresult]].
  cbn [flag_del_valid_option Z.eqb Pos.eqb orb andb] in Hresult.
  destruct (Z.eqb (flagImageType image) 5) eqn:Htype;
    cbn [negb] in Hresult.
  - apply Z.eqb_eq in Htype.
    destruct Hresult as [id [group [drained [drained_image
      [Hview [_ [_ [_ [Hvalue Hreleased]]]]]]]]].
    subst view; cbn [flag_query_selected] in Hselected.
    pose proof (flag_del_acquired_no_waiter_head sg acquired id image
      Hvalid Hnone Hselected Htype) as Hhead.
    rewrite Hhead in Hvalue; inversion Hvalue; reflexivity.
  - destruct Hresult as [Hvalue _]; inversion Hvalue; reflexivity.
Qed.
Lemma flag_del_live_prefix_pool_view__restore_and_scheduler_returns : forall sg pointer view before observed,
  flag_del_argument sg pointer view before observed ->
  pointer <> 0 -> observed.(flagImageType) = 5 ->
  exists id, view = FlagQueryPool id.
Proof.
  intros sg pointer view before observed Harg Hp Htype.
  destruct Harg as [Hnull | [_ [_ [_ [Hselected Hraw]]]]]; [contradiction|].
  destruct view as [image | id]; [|eauto].
  cbn [flag_query_selected] in Hselected; subst observed; contradiction.
Qed.
Lemma flag_del_restore_output_after_restore__restore_and_scheduler_returns :
  forall environment critical local sg caller mask view pointer opt name before observed
    active saved acquired result error schedule released before_heap X,
  flag_del_argument sg pointer view before observed ->
  flag_del_prefix_facts environment critical sg caller mask view pointer opt name before
    observed active saved acquired X ->
  flag_del_protected_result sg view pointer opt name acquired result error schedule released ->
  flag_del_source_restore_output environment critical local sg active saved acquired released schedule before_heap |--
  flag_del_source_after_restore environment critical sg caller mask view pointer opt name before X result error schedule.
Proof.
  intros environment critical local sg caller mask view pointer opt name before observed
    active saved acquired result error schedule released before_heap X Harg Hfacts Hprotected.
  destruct Hfacts as [Hp [Hnest [Hselected [Htype [Hsave [Hsame [Hmask Hsafe]]]]]]].
  destruct (flag_del_live_prefix_pool_view__restore_and_scheduler_returns
    sg pointer view before observed Harg Hp Htype) as [id Hview].
  assert (Hraw : flag_del_raw_type pointer view = emp).
  { rewrite Hview; unfold flag_del_raw_type; destruct (Z.eqb pointer 0); reflexivity. }
  sep_apply (flag_del_source_restore_output_open environment critical local sg active saved acquired released schedule before_heap).
  Intros returned current next_local.
  assert (Hrestore : task_suspend_restore_effect environment critical sg active returned released current) by tauto.
  assert (Hreturned : task_suspend_same_call returned caller).
  { eapply task_suspend_same_call_trans; [|exact Hsame]; tauto. }
  pose proof (flag_del_prefix_protected environment critical sg caller mask view pointer opt name
    before observed saved active acquired ((result,error),schedule) released returned current
    Hp Hnest Hselected Htype Hsave Hprotected Hrestore) as Hprefix.
  pose proof (flag_del_prefix_safe_continuation environment critical sg caller mask view pointer opt name
    before (result,error) schedule returned current X Hprefix Hsafe) as Htail.
  unfold flag_del_source_after_restore.
  Exists returned current next_local.
  rewrite Hraw, (proj2 Hmask); entailer!.
Qed.
Lemma flag_del_scheduled_prefix_pool_view__restore_and_scheduler_returns : forall environment critical sg caller mask view pointer opt name
  before result returned current,
  flag_del_prefix_program environment critical sg caller mask view pointer opt name
    before ((result,true), returned) current ->
  exists id, view = FlagQueryPool id.
Proof.
  intros environment critical sg caller mask view pointer opt name before result returned current Hprefix.
  unfold flag_del_prefix_program in Hprefix.
  destruct (Z.eqb pointer 0).
  - destruct Hprefix as [Heq _]; discriminate Heq.
  - destruct Hprefix as [nesting [s1 [Hget Hrest]]].
    destruct (0 <? nesting)%Z.
    + destruct Hrest as [Heq _]; discriminate Heq.
    + destruct Hrest as [observed [s2 [Hobserve Hrest]]].
      destruct (Z.eqb (flagImageType observed) 5).
      * destruct Hrest as [entered [s3 [Hsave Hrest]]].
        destruct Hrest as [protected [s4 [Hprotected Hrest]]].
        destruct Hrest as [r [s5 [Hrestore [Heq _]]]].
        inversion Heq; subst protected; clear Heq.
        unfold flag_del_protected in Hprotected.
        destruct Hprotected as [image [Hselected Hprotected]].
        destruct (flag_del_valid_option opt && negb (Z.eqb (flagImageType image) 5))%bool.
        -- destruct Hprotected as [Heq _]; discriminate Heq.
        -- destruct (Z.eqb opt 0).
           ++ destruct (Z.eqb (flagImageHead image) 0).
              ** destruct Hprotected as [id [Hview _]]; eauto.
              ** destruct Hprotected as [Heq _]; discriminate Heq.
           ++ destruct (Z.eqb opt 1).
              ** destruct Hprotected as [id [group [drained [image' [Hview _]]]]]; eauto.
              ** destruct Hprotected as [Heq _]; discriminate Heq.
      * destruct Hrest as [Heq _]; discriminate Heq.
Qed.
