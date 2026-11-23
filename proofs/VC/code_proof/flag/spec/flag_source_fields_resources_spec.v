Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.flag Ucos2Verify.lib.flag_stack Ucos2Verify.lib.flag_execution.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.lib.flag_node_fields Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source consequences for the checked fields C helper contracts.
    The exact C implementations and contracts are bound by the scope's
    delivered_c_evidence (Block check-5dx_n40b; TaskRdy check-jbqh1fcp,
    whose actual Unlink callee passed check-l9ph7o4l).
    A call relation below remains a conditional modular premise; defining
    it does not certify arbitrary heaps or replace the actual C proof.

    Pure protocols, key identity, parked metadata and the concrete Next
    heap relation are reused from the original source module. The actual
    loan remains outside the map until Next has been read and assigned.
    No public entry, ABI, source-registry or scheduler closure is added. *)

Definition flag_source_fields_block_call sg state waiter old group image timeout
  (before after : model) : Prop :=
  forall frame : Assertion,
    (flag_block_call_fields_pre sg state waiter old group image timeout ** frame) before ->
    (flag_block_call_fields_post sg state waiter old timeout ** frame) after.

Lemma flag_source_fields_block_post_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state call waiter old group image timeout local,
  valid_flag_state sg state.(FlagState) ->
  flag_block_call_protocol sg state waiter old group image timeout ->
  task_current_at state call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  flag_block_call_fields_post sg state waiter old timeout **
    store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) |--
  EX flags, coq_prop
    (flag_block_spec.flag_block sg state waiter timeout = Some (flag_block_state state waiter flags old timeout) /\
     flag_pend_sched_waiter_binding call waiter.(flagNodeAddr) (flag_block_state state waiter flags old timeout)) &&
    (UCOS2_fields_inv sg (flag_block_state state waiter flags old timeout) **
     store_parked_continuations
       (kernel_saved_continuation_entry abi (flag_block_state state waiter flags old timeout).(TskState) local)
       (flag_block_state state waiter flags old timeout).(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg state call waiter old group image timeout local Hvalid Hprotocol Hcurrent.
  unfold flag_block_call_fields_post; Intros flags.
  assert (Hblock : flag_block_node sg state.(FlagState) waiter (flag_block_call_tcb sg waiter) = Some flags) by tauto.
  pose proof (flag_source_block_waiter_binding sg state call waiter old group image timeout flags
    Hvalid Hprotocol Hcurrent Hblock) as Hbinding.
  destruct (flag_source_block_stack_metadata state waiter flags old timeout) as [Hstacks Hfields].
  assert (Hold : state.(TskState).(inUsedTaskStates) waiter.(flagTask) = Some old)
    by (unfold flag_block_call_protocol in Hprotocol; tauto).
  assert (Hmetadata : forall key payload updated,
    state.(TskState).(parkedTaskStacks) key = Some payload ->
    (flag_block_state state waiter flags old timeout).(TskState).(inUsedTaskStates) (fst key) = Some updated ->
    updated.(taskGeneration) = snd key ->
    exists previous, state.(TskState).(inUsedTaskStates) (fst key) = Some previous /\
      previous.(taskGeneration) = updated.(taskGeneration) /\ previous.(tcbStkPtr) = updated.(tcbStkPtr)).
  { intros; eapply Hfields; eassumption. }
  sep_apply_l_atomic (kernel_saved_continuation_map_reindex external platform port abi state.(TskState)
    (flag_block_state state waiter flags old timeout).(TskState) local
    state.(TskState).(parkedTaskStacks) Hmetadata).
  Exists flags; rewrite Hstacks; entailer!.
Qed.

Lemma flag_source_fields_block_call_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state call waiter old group image timeout local
  (frame : Assertion) before after,
  valid_flag_state sg state.(FlagState) ->
  flag_block_call_protocol sg state waiter old group image timeout ->
  task_current_at state call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  flag_source_fields_block_call sg state waiter old group image timeout before after ->
  (flag_block_call_fields_pre sg state waiter old group image timeout **
    (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) ** frame)) before ->
  (EX flags, coq_prop
    (flag_block_spec.flag_block sg state waiter timeout = Some (flag_block_state state waiter flags old timeout) /\
     flag_pend_sched_waiter_binding call waiter.(flagNodeAddr) (flag_block_state state waiter flags old timeout)) &&
    (UCOS2_fields_inv sg (flag_block_state state waiter flags old timeout) **
     store_parked_continuations
       (kernel_saved_continuation_entry abi (flag_block_state state waiter flags old timeout).(TskState) local)
       (flag_block_state state waiter flags old timeout).(TskState).(parkedTaskStacks) ** frame)) after.
Proof.
  intros external platform port abi sg state call waiter old group image timeout local frame before after
    Hvalid Hprotocol Hcurrent Hcall Hpre.
  specialize (Hcall _ Hpre).
  match type of Hcall with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (flag_source_fields_block_post_resources external platform port abi sg state call waiter old
      group image timeout local Hvalid Hprotocol Hcurrent); Intros flags; Exists flags; entailer!. }
  exact (Hclose after Hcall).
Qed.

Lemma flag_source_fields_task_rdy_call_loan : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state node waiter old bits result returned local
  (frame : Assertion) before after,
  UCOS2_state_inv sg state -> flag_task_rdy_domain sg state node waiter old bits ->
  flag_pend_sched_fields_task_rdy_call sg node bits result returned before after ->
  (flag_task_rdy_fields_pre sg state node waiter old bits **
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
     store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
       state.(TskState).(parkedTaskStacks) ** frame)) before ->
  (EX post, EX schedule, coq_prop
    (flag_task_rdy sg state node bits result = Some (schedule, post) /\
     returned = (if schedule then 1 else 0)) &&
    (UCOS2_fields_inv sg post ** flag_node_fields_return_loan sg.(osKernelConfig) waiter **
     store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
       post.(TskState).(parkedTaskStacks) ** frame)) after.
Proof.
  intros external platform port abi sg state node waiter old bits result returned local frame before after
    Hvalid Hdomain Hcall Hpre.
  specialize (Hcall state waiter old _ Hpre).
  match type of Hcall with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (flag_wake_fields_returns_node_with_continuation_map external platform port abi sg state node
      waiter old bits result returned local Hvalid Hdomain); Intros post schedule; Exists post schedule; entailer!. }
  exact (Hclose after Hcall).
Qed.

Lemma flag_source_fields_next_assignment_resources : forall sg waiter pnode (frame : Assertion) before after observed,
  (pnode # Ptr |-> waiter.(flagNodeAddr) ** flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame) before ->
  flag_source_next_assignment pnode waiter.(flagNodeAddr) observed before after ->
  observed = waiter.(flagWaitImage).(flagNodeNext) /\
  (pnode # Ptr |-> observed ** flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame) after.
Proof.
  intros sg waiter pnode frame before after observed Hpre [Hnode [Hnext Hwrite]].
  assert (Hread : pnode # Ptr |-> waiter.(flagNodeAddr) ** flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame |--
    waiter.(flagNodeAddr) # Ptr |-> waiter.(flagWaitImage).(flagNodeNext) **
      (flag_node_fields_rep_without_next sg.(osKernelConfig) waiter.(flagNodeAddr) waiter.(flagWaitImage) **
       pnode # Ptr |-> waiter.(flagNodeAddr) ** frame)).
  { sep_apply_l_atomic (flag_node_fields_return_loan_split_next sg waiter); entailer!. }
  pose proof (framed_pointer_store_load _ _ _ before (Hread before Hpre)) as Hstored.
  assert (Heq : observed = waiter.(flagWaitImage).(flagNodeNext))
    by (eapply pointer_load_deterministic; eassumption).
  assert (Hforget : pnode # Ptr |-> waiter.(flagNodeAddr) ** flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame |--
    pnode # Ptr |->_ ** (flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame)).
  { sep_apply_l_atomic (store_ptr_undef_store_ptr pnode waiter.(flagNodeAddr)); entailer!. }
  destruct (framed_pointer_store_execution pnode observed _ before (proj1 Hnext)
    (Hforget before Hpre)) as [produced [Hproduced Hafter]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced; split; [exact Heq|].
  assert (Hclose : pnode # Ptr |-> observed ** (flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame) |--
    pnode # Ptr |-> observed ** flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame) by entailer!.
  exact (Hclose after Hafter).
Qed.

Lemma flag_source_fields_next_assignment_exists : forall sg waiter pnode (frame : Assertion) before,
  (pnode # Ptr |-> waiter.(flagNodeAddr) ** flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame) before ->
  exists after,
    flag_source_next_assignment pnode waiter.(flagNodeAddr) waiter.(flagWaitImage).(flagNodeNext) before after /\
    (pnode # Ptr |-> waiter.(flagWaitImage).(flagNodeNext) **
     flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame) after.
Proof.
  intros sg waiter pnode frame before Hpre.
  assert (Hpnode : pnode # Ptr |-> waiter.(flagNodeAddr) ** flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame |--
    pnode # Ptr |-> waiter.(flagNodeAddr) ** (flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame)) by entailer!.
  pose proof (framed_pointer_store_load _ _ _ before (Hpnode before Hpre)) as Hnode.
  assert (Hnext : pnode # Ptr |-> waiter.(flagNodeAddr) ** flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame |--
    waiter.(flagNodeAddr) # Ptr |-> waiter.(flagWaitImage).(flagNodeNext) **
      (flag_node_fields_rep_without_next sg.(osKernelConfig) waiter.(flagNodeAddr) waiter.(flagWaitImage) **
       pnode # Ptr |-> waiter.(flagNodeAddr) ** frame)).
  { sep_apply_l_atomic (flag_node_fields_return_loan_split_next sg waiter); entailer!. }
  pose proof (framed_pointer_store_load _ _ _ before (Hnext before Hpre)) as Hread.
  assert (Hforget : pnode # Ptr |-> waiter.(flagNodeAddr) ** flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame |--
    pnode # Ptr |->_ ** (flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame)).
  { sep_apply_l_atomic (store_ptr_undef_store_ptr pnode waiter.(flagNodeAddr)); entailer!. }
  destruct (framed_pointer_store_execution pnode waiter.(flagWaitImage).(flagNodeNext) _ before
    (proj1 Hread) (Hforget before Hpre)) as [after [Hwrite Hafter]].
  exists after; split.
  - unfold flag_source_next_assignment; auto.
  - assert (Hclose : pnode # Ptr |-> waiter.(flagWaitImage).(flagNodeNext) **
       (flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame) |--
       pnode # Ptr |-> waiter.(flagWaitImage).(flagNodeNext) **
       flag_node_fields_return_loan sg.(osKernelConfig) waiter ** frame) by entailer!.
    exact (Hclose after Hafter).
Qed.

Lemma flag_source_fields_next_assignment_publish : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg post node waiter original local fragments pnode
  (frame : Assertion) before after observed,
  waiter.(flagNodeAddr) = node -> post.(FlagState).(flagWaitNodes) node = None ->
  task_stack_key original = (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  post.(TskState).(parkedTaskStacks) (task_stack_key original) = Some (original.(stackLeaseRegion), fragments) ->
  (pnode # Ptr |-> node ** flag_node_fields_return_loan sg.(osKernelConfig) waiter **
    (UCOS2_fields_inv sg post **
     store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
       post.(TskState).(parkedTaskStacks) ** frame)) before ->
  flag_source_next_assignment pnode node observed before after ->
  observed = waiter.(flagWaitImage).(flagNodeNext) /\
  (pnode # Ptr |-> observed ** UCOS2_fields_inv sg post **
   store_parked_continuations
     (kernel_saved_continuation_entry abi post.(TskState)
       (flag_continuation_local_node original (flag_pend_sched_node_fields_rep sg node post) local))
     post.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg post node waiter original local fragments pnode frame before after observed
    Hnode Hnone Hkey Hentry Hpre Hrun.
  rewrite <- Hnode in Hpre, Hrun.
  destruct (flag_source_fields_next_assignment_resources sg waiter pnode _ before after observed Hpre Hrun)
    as [Hobserved Hafter].
  split; [exact Hobserved|].
  assert (Hopen : pnode # Ptr |-> observed ** flag_node_fields_return_loan sg.(osKernelConfig) waiter **
    (UCOS2_fields_inv sg post **
     store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
       post.(TskState).(parkedTaskStacks) ** frame) |--
    (flag_node_fields_return_loan sg.(osKernelConfig) waiter **
     store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
       post.(TskState).(parkedTaskStacks)) ** (pnode # Ptr |-> observed ** UCOS2_fields_inv sg post ** frame)) by entailer!.
  pose proof (Hopen after Hafter) as Hopened.
  match type of Hopened with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (flag_wake_fields_publish_returned_node external platform port abi sg post node waiter
      original local fragments Hnode Hnone Hkey Hentry); entailer!. }
  exact (Hclose after Hopened).
Qed.

Lemma flag_source_fields_task_rdy_next_publish : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state node waiter old bits result returned
  original local fragments pnode (frame : Assertion) before middle after observed,
  UCOS2_state_inv sg state -> flag_task_rdy_domain sg state node waiter old bits ->
  waiter.(flagNodeAddr) = node ->
  task_stack_key original = (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original) =
    Some (original.(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg node bits result returned before middle ->
  flag_source_next_assignment pnode node observed middle after ->
  (flag_task_rdy_fields_pre sg state node waiter old bits **
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
     store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
       state.(TskState).(parkedTaskStacks) ** (pnode # Ptr |-> node ** frame))) before ->
  exists post schedule,
    flag_task_rdy sg state node bits result = Some (schedule, post) /\
    returned = (if schedule then 1 else 0) /\
    observed = waiter.(flagWaitImage).(flagNodeNext) /\
    (pnode # Ptr |-> observed ** UCOS2_fields_inv sg post **
     store_parked_continuations
       (kernel_saved_continuation_entry abi post.(TskState)
         (flag_continuation_local_node original (flag_pend_sched_node_fields_rep sg node post) local))
       post.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg state node waiter old bits result returned original local fragments
    pnode frame before middle after observed Hvalid Hdomain Hnode Hkey Hentry Hcall Hnext Hpre.
  destruct (flag_source_fields_task_rdy_call_loan external platform port abi sg state node waiter old bits result
    returned local (pnode # Ptr |-> node ** frame) before middle Hvalid Hdomain Hcall Hpre)
    as [post [schedule [[Hstep Hreturned] Hmiddle]]].
  pose proof (flag_pend_sched_wake_unlinks_node sg state node bits result schedule post Hstep) as Hnone.
  pose proof (proj1 (FlagPendSchedulerResources.flag_task_rdy_preserves_stack_metadata
    sg state node bits result schedule post Hstep)) as Hstacks.
  assert (Hparked : post.(TskState).(parkedTaskStacks) (task_stack_key original) =
    Some (original.(stackLeaseRegion), fragments)) by (rewrite Hstacks; exact Hentry).
  match type of Hmiddle with ?P middle => assert (Horder : P |--
    pnode # Ptr |-> node ** flag_node_fields_return_loan sg.(osKernelConfig) waiter **
      (UCOS2_fields_inv sg post **
       store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
         post.(TskState).(parkedTaskStacks) ** frame)) by entailer! end.
  destruct (flag_source_fields_next_assignment_publish external platform port abi sg post node waiter original
    local fragments pnode frame middle after observed Hnode Hnone Hkey Hparked
    (Horder middle Hmiddle) Hnext) as [Hobserved Hafter].
  exists post, schedule; auto.
Qed.
