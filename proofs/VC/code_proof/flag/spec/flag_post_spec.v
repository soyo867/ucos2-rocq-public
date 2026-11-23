Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_fields_resources_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_fields_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.lib.flag_fields_resources Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.kernel_resources.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules TaskStateDef Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
Local Open Scope sac_scope.

(** Source components of OSFlagPost. The protected fold below is connected
    to the checked fields TaskRdy contract, the actual Next assignment, and
    same-invocation continuation publication. These conditional component
    proofs do not certify the enclosing public C call. That call still needs
    its actual paired Save/Restore and Scheduler contracts on the fields world.
    In particular [posted_word] below is not the value of the final C read. *)

Definition flag_post_valid_option (option_word : Z) : bool :=
  Z.eqb option_word 0 || Z.eqb option_word 1.

(** Decode the byte the C switch actually reads.  Using only flagWaitMode
    would erase the default/error branch before the source proof establishes
    image/mode consistency.  The selected configuration enables all four. *)
Definition flag_post_node_test (configuration : KernelConfiguration)
  (word mask mode_word : Z) : option (Z * bool) :=
  match decode_flag_wait_mode configuration mode_word with
  | None => None
  | Some mode =>
      let ready := flag_ready_bits configuration word mask mode in
      Some (ready, flag_wait_satisfied mode ready mask)
  end.

Lemma flag_post_valid_option_iff : forall option_word,
  flag_post_valid_option option_word = true <-> option_word = 0 \/ option_word = 1.
Proof.
  intros; unfold flag_post_valid_option.
  rewrite Bool.orb_true_iff, !Z.eqb_eq; tauto.
Qed.

Lemma flag_post_bits_invalid_option : forall configuration word mask option_word,
  flag_post_valid_option option_word = false ->
  flag_post_bits configuration word mask option_word = None.
Proof.
  intros configuration word mask option_word Hoption.
  unfold flag_post_valid_option in Hoption.
  apply Bool.orb_false_iff in Hoption; destruct Hoption as [Hclear Hset].
  unfold flag_post_bits; rewrite Hclear, Hset; reflexivity.
Qed.

Lemma flag_post_node_test_set_all : forall word mask,
  flag_post_node_test selected_kernel_configuration word mask 2 =
  Some (flag_word selected_kernel_configuration (Z.land word mask),
    Z.eqb (flag_word selected_kernel_configuration (Z.land word mask)) mask).
Proof. reflexivity. Qed.

Lemma flag_post_node_test_set_any : forall word mask,
  flag_post_node_test selected_kernel_configuration word mask 3 =
  Some (flag_word selected_kernel_configuration (Z.land word mask),
    negb (Z.eqb (flag_word selected_kernel_configuration (Z.land word mask)) 0)).
Proof. reflexivity. Qed.

Lemma flag_post_node_test_clear_all : forall word mask,
  flag_post_node_test selected_kernel_configuration word mask 0 =
  Some (flag_word selected_kernel_configuration (Z.land (Z.lnot word) mask),
    Z.eqb (flag_word selected_kernel_configuration (Z.land (Z.lnot word) mask)) mask).
Proof. reflexivity. Qed.

Lemma flag_post_node_test_clear_any : forall word mask,
  flag_post_node_test selected_kernel_configuration word mask 1 =
  Some (flag_word selected_kernel_configuration (Z.land (Z.lnot word) mask),
    negb (Z.eqb (flag_word selected_kernel_configuration (Z.land (Z.lnot word) mask)) 0)).
Proof. reflexivity. Qed.

Lemma flag_post_node_test_invalid : forall configuration word mask mode_word,
  decode_flag_wait_mode configuration mode_word = None ->
  flag_post_node_test configuration word mask mode_word = None.
Proof. intros; unfold flag_post_node_test; rewrite H; reflexivity. Qed.

(** A receipt records one observed node and the real helper result.  A false
    helper result still records a wake/unlink; [None] means no helper call.
    The Next value is absent on the invalid-mode early return, which does not
    execute the C Next read.  The waiter retains node, task, group generations
    and its concrete image; the source proof must supply its actual lookup. *)
Record FlagPostVisit := {
  flag_post_visit_node : addr;
  flag_post_visit_waiter : FlagWaiterState;
  flag_post_visit_ready : option Z;
  flag_post_visit_returned : option bool;
  flag_post_visit_next : option addr
}.

Definition flag_post_visit (node : addr) (waiter : FlagWaiterState)
  (ready : option Z) (returned : option bool) (next : option addr) : FlagPostVisit :=
  {| flag_post_visit_node := node;
     flag_post_visit_waiter := waiter;
     flag_post_visit_ready := ready;
     flag_post_visit_returned := returned;
     flag_post_visit_next := next |}.

Definition flag_post_visit_requests_schedule (visit : FlagPostVisit) : bool :=
  match visit.(flag_post_visit_returned) with Some returned => returned | None => false end.

Definition flag_post_schedule (visits : list FlagPostVisit) : bool :=
  existsb flag_post_visit_requests_schedule visits.

Lemma flag_post_schedule_append : forall visited current,
  flag_post_schedule (visited ++ [current]) =
  (flag_post_schedule visited || flag_post_visit_requests_schedule current)%bool.
Proof.
  intros; unfold flag_post_schedule; rewrite existsb_app; simpl.
  rewrite Bool.orb_false_r; reflexivity.
Qed.

Lemma flag_post_schedule_false_result : forall visited node waiter ready next,
  flag_post_schedule (visited ++ [flag_post_visit node waiter (Some ready) (Some false) (Some next)]) =
  flag_post_schedule visited.
Proof. intros; rewrite flag_post_schedule_append; simpl; apply Bool.orb_false_r. Qed.

Lemma flag_post_schedule_true_result : forall visited node waiter ready next,
  flag_post_schedule (visited ++ [flag_post_visit node waiter (Some ready) (Some true) (Some next)]) = true.
Proof. intros; rewrite flag_post_schedule_append; simpl; apply Bool.orb_true_r. Qed.

Lemma flag_post_schedule_no_call : forall visited node waiter ready next,
  flag_post_schedule (visited ++ [flag_post_visit node waiter ready None next]) =
  flag_post_schedule visited.
Proof. intros; rewrite flag_post_schedule_append; simpl; apply Bool.orb_false_r. Qed.

Record FlagPostScan := {
  flag_post_scan_state : UCOS2_Verify_State;
  flag_post_scan_visits : list FlagPostVisit;
  flag_post_scan_error : option Z
}.

Definition flag_post_scan_initial (state : UCOS2_Verify_State) : FlagPostScan :=
  {| flag_post_scan_state := state;
     flag_post_scan_visits := [];
     flag_post_scan_error := None |}.

Definition flag_post_scan_append (scan : FlagPostScan) (state : UCOS2_Verify_State)
  (visit : FlagPostVisit) (error : option Z) : FlagPostScan :=
  {| flag_post_scan_state := state;
     flag_post_scan_visits := scan.(flag_post_scan_visits) ++ [visit];
     flag_post_scan_error := error |}.

(** The fold uses the current node/TCB lookup and the checked pure helper
    transformer.  None is a missing represented lookup/callee domain, NOT a
    fabricated C error return.  Annotation must prove those lookups from real
    ownership and retain the returned node loan until Next has been read.
    The fold's ordered input comes from the acquired group; a source invariant
    must connect its remaining suffix to pnode, including after unlink. *)
Definition flag_post_scan_step (sg : StableGlobVars) (posted_word : Z)
  (accumulator : option FlagPostScan) (node : addr) : option FlagPostScan :=
  match accumulator with
  | None => None
  | Some scan =>
      match scan.(flag_post_scan_error) with
      | Some _ => Some scan
      | None =>
          let state := scan.(flag_post_scan_state) in
          match state.(FlagState).(flagWaitNodes) node with
          | None => None
          | Some waiter =>
              match flag_post_node_test sg.(osKernelConfig) posted_word
                waiter.(flagWaitImage).(flagNodeMask)
                waiter.(flagWaitImage).(flagNodeMode) with
              | None => Some (flag_post_scan_append scan state
                  (flag_post_visit node waiter None None None) (Some 111))
              | Some (ready, satisfied) =>
                  let next := waiter.(flagWaitImage).(flagNodeNext) in
                  if satisfied then
                    match flag_task_rdy sg state node ready PendOK with
                    | None => None
                    | Some (returned, after) => Some (flag_post_scan_append scan after
                        (flag_post_visit node waiter (Some ready) (Some returned) (Some next)) None)
                    end
                  else Some (flag_post_scan_append scan state
                    (flag_post_visit node waiter (Some ready) None (Some next)) None)
              end
          end
      end
  end.

Definition flag_post_scan (sg : StableGlobVars) (posted_word : Z)
  (initial : UCOS2_Verify_State) (visited : list addr) : option FlagPostScan :=
  fold_left (flag_post_scan_step sg posted_word) visited (Some (flag_post_scan_initial initial)).

Lemma flag_post_scan_visited_extension : forall sg posted_word initial visited remaining,
  flag_post_scan sg posted_word initial (visited ++ remaining) =
  fold_left (flag_post_scan_step sg posted_word) remaining
    (flag_post_scan sg posted_word initial visited).
Proof. intros; unfold flag_post_scan; apply fold_left_app. Qed.

Lemma flag_post_scan_error_retains_effects : forall sg posted_word scan node error,
  scan.(flag_post_scan_error) = Some error ->
  flag_post_scan_step sg posted_word (Some scan) node = Some scan.
Proof. intros; unfold flag_post_scan_step; rewrite H; reflexivity. Qed.

Lemma flag_post_scan_invalid_mode : forall sg posted_word scan node waiter,
  scan.(flag_post_scan_error) = None ->
  scan.(flag_post_scan_state).(FlagState).(flagWaitNodes) node = Some waiter ->
  decode_flag_wait_mode sg.(osKernelConfig) waiter.(flagWaitImage).(flagNodeMode) = None ->
  flag_post_scan_step sg posted_word (Some scan) node =
    Some (flag_post_scan_append scan scan.(flag_post_scan_state)
      (flag_post_visit node waiter None None None) (Some 111)).
Proof.
  intros sg posted_word scan node waiter Herror Hnode Hmode.
  unfold flag_post_scan_step; rewrite Herror, Hnode.
  unfold flag_post_node_test; rewrite Hmode; reflexivity.
Qed.

Inductive FlagPostProtectedResult :=
| FlagPostProtectedRejected (error : Z)
| FlagPostProtectedScanned (posted_word : Z) (visits : list FlagPostVisit) (error : option Z).

(** Only the first protected phase.  The source tests type again for SET/CLR
    before modifying the word.  Invalid opt has its own error even if the slot
    changed type after the pre-critical read.  All prior effects survive an
    invalid waiter mode.  No invariant-closure condition is inserted as a guard. *)
Definition flag_post_protected_program (sg : StableGlobVars) (id : FlagID)
  (requested option_word : Z) : program UCOS2_Verify_State FlagPostProtectedResult :=
  fun before result after => exists image,
    before.(FlagState).(flagImages) id = Some image /\
    if (flag_post_valid_option option_word && negb (Z.eqb image.(flagImageType) 5))%bool then
      result = FlagPostProtectedRejected 1 /\ after = before
    else match flag_post_bits sg.(osKernelConfig) image.(flagImageBits) requested option_word with
      | None => result = FlagPostProtectedRejected 113 /\ after = before
      | Some posted_word => exists group scan,
          before.(FlagState).(flagUsed) id = Some group /\
          flag_post_scan sg posted_word
            (replace_FlagS (flag_replace_bits before.(FlagState) id group image posted_word) before)
            group.(flagWaitOrder) = Some scan /\
          result = FlagPostProtectedScanned posted_word scan.(flag_post_scan_visits)
            scan.(flag_post_scan_error) /\
          after = scan.(flag_post_scan_state)
      end.

Definition flag_post_protected_safe sg id requested option_word before
  (X : FlagPostProtectedResult -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (flag_post_protected_program sg id requested option_word) X.

Lemma flag_post_protected_safe_return : forall sg id requested option_word before current result X,
  flag_post_protected_program sg id requested option_word before result current ->
  flag_post_protected_safe sg id requested option_word before X ->
  safeExec (eq current) (StateRelMonad.ret result) X.
Proof.
  intros sg id requested option_word before current result X Hprogram Hsafe.
  unfold flag_post_protected_safe in Hsafe.
  eapply (highstependret_derive (flag_post_protected_program sg id requested option_word)
    (eq before) result (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

(** These two equations connect the source guard to a single fold step.
    A satisfied call records its returned state even when its Boolean is false. *)
Lemma flag_post_scan_unsatisfied : forall sg posted_word scan node waiter ready,
  scan.(flag_post_scan_error) = None ->
  scan.(flag_post_scan_state).(FlagState).(flagWaitNodes) node = Some waiter ->
  flag_post_node_test sg.(osKernelConfig) posted_word
    waiter.(flagWaitImage).(flagNodeMask) waiter.(flagWaitImage).(flagNodeMode) =
    Some (ready, false) ->
  flag_post_scan_step sg posted_word (Some scan) node =
    Some (flag_post_scan_append scan scan.(flag_post_scan_state)
      (flag_post_visit node waiter (Some ready) None
        (Some waiter.(flagWaitImage).(flagNodeNext))) None).
Proof.
  intros sg posted_word scan node waiter ready Herror Hnode Htest.
  unfold flag_post_scan_step; rewrite Herror, Hnode, Htest; reflexivity.
Qed.

Lemma flag_post_scan_satisfied_call : forall sg posted_word scan node waiter ready returned post,
  scan.(flag_post_scan_error) = None ->
  scan.(flag_post_scan_state).(FlagState).(flagWaitNodes) node = Some waiter ->
  flag_post_node_test sg.(osKernelConfig) posted_word
    waiter.(flagWaitImage).(flagNodeMask) waiter.(flagWaitImage).(flagNodeMode) =
    Some (ready, true) ->
  flag_task_rdy sg scan.(flag_post_scan_state) node ready PendOK = Some (returned, post) ->
  flag_post_scan_step sg posted_word (Some scan) node =
    Some (flag_post_scan_append scan post
      (flag_post_visit node waiter (Some ready) (Some returned)
        (Some waiter.(flagWaitImage).(flagNodeNext))) None).
Proof.
  intros sg posted_word scan node waiter ready returned post Herror Hnode Htest Hcall.
  unfold flag_post_scan_step; rewrite Herror, Hnode, Htest, Hcall; reflexivity.
Qed.

(** A node whose wait test is false stays registered. Its six fields are
    borrowed for the actual Next assignment and then returned to the same map. *)
Definition flag_post_registered_node_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (node : addr) : Assertion :=
  flag_groups_rep sg state.(FlagState) **
  flag_wait_nodes_fields_without_node sg state.(FlagState).(flagWaitNodes) node **
  sg.(g_OSFlagFreeList) # Ptr |->
    (match state.(FlagState).(flagFree) with [] => 0 | id :: _ => flag_pool_addr sg id end) **
  UCOS2_raw_rep_missing_flag sg state ** unmap_table_rep sg.

Lemma flag_post_registered_node_resources : forall sg state node waiter,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  state.(FlagState).(flagWaitNodes) node = Some waiter ->
  kernel_program_fields_inv sg state --||--
    coq_prop (UCOS2_state_inv sg state) &&
      (flag_node_fields_rep sg.(osKernelConfig) node waiter.(flagWaitImage) **
       flag_post_registered_node_frame sg state node).
Proof.
  intros sg state node waiter Hcfg Hlookup.
  unfold kernel_program_fields_inv, kernel_program_fields_rep, UCOS2_fields_raw_rep,
    flag_fields_configured_rep.
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true) by (rewrite Hcfg; reflexivity).
  rewrite Henabled.
  unfold flag_fields_raw_rep, flag_post_registered_node_frame; split.
  - Intros; sep_apply_l_atomic (flag_wait_nodes_fields_rep_split_node sg state.(FlagState).(flagWaitNodes)
      node waiter Hlookup); entailer!.
  - Intros; sep_apply_l_atomic (flag_wait_nodes_fields_rep_merge_node sg state.(FlagState).(flagWaitNodes)
      node waiter Hlookup); entailer!.
Qed.

Lemma flag_post_scan_fields_unsatisfied_next : forall sg posted_word scan node waiter ready
  pnode (frame : Assertion) before after observed,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  scan.(flag_post_scan_error) = None ->
  scan.(flag_post_scan_state).(FlagState).(flagWaitNodes) node = Some waiter ->
  waiter.(flagNodeAddr) = node ->
  flag_post_node_test sg.(osKernelConfig) posted_word
    waiter.(flagWaitImage).(flagNodeMask) waiter.(flagWaitImage).(flagNodeMode) = Some (ready, false) ->
  (pnode # Ptr |-> node ** kernel_program_fields_inv sg scan.(flag_post_scan_state) ** frame) before ->
  flag_source_next_assignment pnode node observed before after ->
  flag_post_scan_step sg posted_word (Some scan) node =
    Some (flag_post_scan_append scan scan.(flag_post_scan_state)
      (flag_post_visit node waiter (Some ready) None (Some observed)) None) /\
  observed = waiter.(flagWaitImage).(flagNodeNext) /\
  (pnode # Ptr |-> observed ** kernel_program_fields_inv sg scan.(flag_post_scan_state) ** frame) after.
Proof.
  intros sg posted_word scan node waiter ready pnode frame before after observed Hcfg Herror Hlookup Hnode
    Htest Hpre Hnext.
  assert (Hopen : pnode # Ptr |-> node ** kernel_program_fields_inv sg scan.(flag_post_scan_state) ** frame |--
    pnode # Ptr |-> waiter.(flagNodeAddr) ** flag_node_fields_return_loan sg.(osKernelConfig) waiter **
      (coq_prop (UCOS2_state_inv sg scan.(flag_post_scan_state)) &&
        (flag_post_registered_node_frame sg scan.(flag_post_scan_state) node ** frame))).
  { rewrite (flag_post_registered_node_resources sg scan.(flag_post_scan_state) node waiter Hcfg Hlookup).
    unfold flag_node_fields_return_loan; rewrite Hnode; entailer!. }
  assert (Hrun : flag_source_next_assignment pnode waiter.(flagNodeAddr) observed before after)
    by (rewrite Hnode; exact Hnext).
  destruct (flag_source_fields_next_assignment_resources sg waiter pnode _ before after observed
    (Hopen before Hpre) Hrun) as [Hobserved Hafter].
  split.
  - rewrite Hobserved; apply flag_post_scan_unsatisfied; assumption.
  - split; [exact Hobserved|].
    match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { rewrite (flag_post_registered_node_resources sg scan.(flag_post_scan_state) node waiter Hcfg Hlookup).
      unfold flag_node_fields_return_loan; rewrite Hnode; entailer!. }
    exact (Hclose after Hafter).
Qed.

(** [Hcall] must come from the actual OS_FlagTaskRdy fields contract, with
    the same framed heap endpoints; [Hnext] is the concrete read/read/store
    sequence. A parked-entry lookup is consumed explicitly. Node absence,
    task readiness, or the existence of an invocation number cannot supply it. *)
Lemma flag_post_scan_fields_wake_next : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg posted_word scan node waiter old ready returned
  original local fragments pnode (frame : Assertion) before middle after observed,
  scan.(flag_post_scan_error) = None ->
  scan.(flag_post_scan_state).(FlagState).(flagWaitNodes) node = Some waiter ->
  flag_post_node_test sg.(osKernelConfig) posted_word
    waiter.(flagWaitImage).(flagNodeMask) waiter.(flagWaitImage).(flagNodeMode) = Some (ready, true) ->
  UCOS2_state_inv sg scan.(flag_post_scan_state) ->
  flag_task_rdy_domain sg scan.(flag_post_scan_state) node waiter old ready ->
  waiter.(flagNodeAddr) = node ->
  task_stack_key original = (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  scan.(flag_post_scan_state).(TskState).(parkedTaskStacks) (task_stack_key original) =
    Some (original.(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg node ready PendOK returned before middle ->
  flag_source_next_assignment pnode node observed middle after ->
  (flag_task_rdy_fields_pre sg scan.(flag_post_scan_state) node waiter old ready **
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg scan.(flag_post_scan_state) **
     store_parked_continuations
       (kernel_saved_continuation_entry abi scan.(flag_post_scan_state).(TskState) local)
       scan.(flag_post_scan_state).(TskState).(parkedTaskStacks) **
     (pnode # Ptr |-> node ** frame))) before ->
  exists post schedule,
    flag_post_scan_step sg posted_word (Some scan) node =
      Some (flag_post_scan_append scan post
        (flag_post_visit node waiter (Some ready) (Some schedule) (Some observed)) None) /\
    returned = (if schedule then 1 else 0) /\
    observed = waiter.(flagWaitImage).(flagNodeNext) /\
    (pnode # Ptr |-> observed ** UCOS2_fields_inv sg post **
     store_parked_continuations
       (kernel_saved_continuation_entry abi post.(TskState)
         (flag_continuation_local_node original (flag_pend_sched_node_fields_rep sg node post) local))
       post.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg posted_word scan node waiter old ready returned original local fragments
    pnode frame before middle after observed Herror Hlookup Htest Hvalid Hdomain Hnode Hkey Hentry Hcall Hnext Hpre.
  destruct (flag_source_fields_task_rdy_next_publish external platform port abi sg scan.(flag_post_scan_state)
    node waiter old ready PendOK returned original local fragments pnode frame before middle after observed
    Hvalid Hdomain Hnode Hkey Hentry Hcall Hnext Hpre)
    as [post [schedule [Hstep [Hreturned [Hobserved Hafter]]]]].
  exists post, schedule; split.
  - rewrite Hobserved; eapply flag_post_scan_satisfied_call; eassumption.
  - auto.
Qed.

(** The ISR may wake the Pend it interrupted. The fields receipt joins that
    exact suspended local only after Next. It does not require node padding or
    a different task to wake, and does not infer that the task was already ready. *)
Lemma flag_post_scan_fields_irq_wake_next : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg posted_word scan node waiter old ready returned
  saved_local suspended fragments pnode (interrupted_local frame : Assertion) before middle after observed,
  scan.(flag_post_scan_error) = None ->
  scan.(flag_post_scan_state).(FlagState).(flagWaitNodes) node = Some waiter ->
  flag_post_node_test sg.(osKernelConfig) posted_word
    waiter.(flagWaitImage).(flagNodeMask) waiter.(flagWaitImage).(flagNodeMode) = Some (ready, true) ->
  UCOS2_state_inv sg scan.(flag_post_scan_state) ->
  flag_task_rdy_domain sg scan.(flag_post_scan_state) node waiter old ready ->
  waiter.(flagNodeAddr) = node ->
  task_stack_key suspended.(armv7a_continuation_stack) = (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  scan.(flag_post_scan_state).(TskState).(parkedTaskStacks)
    (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg node ready PendOK returned before middle ->
  flag_source_next_assignment pnode node observed middle after ->
  (flag_task_rdy_fields_pre sg scan.(flag_post_scan_state) node waiter old ready **
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg scan.(flag_post_scan_state) **
     store_parked_continuations
       (kernel_saved_continuation_entry abi scan.(flag_post_scan_state).(TskState)
         (flag_source_irq_local saved_local suspended interrupted_local))
       scan.(flag_post_scan_state).(TskState).(parkedTaskStacks) **
     (pnode # Ptr |-> node ** frame))) before ->
  exists post schedule,
    flag_post_scan_step sg posted_word (Some scan) node =
      Some (flag_post_scan_append scan post
        (flag_post_visit node waiter (Some ready) (Some schedule) (Some observed)) None) /\
    returned = (if schedule then 1 else 0) /\
    observed = waiter.(flagWaitImage).(flagNodeNext) /\
    (pnode # Ptr |-> observed ** UCOS2_fields_inv sg post **
     store_parked_continuations
       (kernel_saved_continuation_entry abi post.(TskState)
         (flag_source_irq_local saved_local suspended
           (interrupted_local ** flag_pend_sched_node_fields_rep sg node post)))
       post.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg posted_word scan node waiter old ready returned saved_local suspended fragments
    pnode interrupted_local frame before middle after observed Herror Hlookup Htest Hvalid Hdomain Hnode
    Hkey Hentry Hcall Hnext Hpre.
  destruct (flag_post_scan_fields_wake_next external platform port abi sg posted_word scan node waiter old ready
    returned suspended.(armv7a_continuation_stack)
    (flag_source_irq_local saved_local suspended interrupted_local) fragments pnode frame before middle after observed
    Herror Hlookup Htest Hvalid Hdomain Hnode Hkey Hentry Hcall Hnext Hpre)
    as [post [schedule [Hstep [Hreturned [Hobserved Hafter]]]]].
  exists post, schedule; split; [exact Hstep|]. split; [exact Hreturned|]. split; [exact Hobserved|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (flag_source_irq_map_add_receipt external platform port abi post.(TskState)
      post.(TskState).(parkedTaskStacks) saved_local suspended interrupted_local
      (flag_pend_sched_node_fields_rep sg node post)); entailer!. }
  exact (Hclose after Hafter).
Qed.

(** The final C load observes the current slot image after the second Save.
    Its frame keeps all other group bytes and every other kernel resource.
    There is no relation to the earlier group's generation or posted bits. *)
Definition flag_post_current_word_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (id : FlagID) (image : FlagGroupImage) : Assertion :=
  flag_pool_addr sg id # UChar |-> image.(flagImageType) **
  store_optional_bytes (flag_pool_addr sg id + 1) (firstn 3 image.(flagImagePadding)) **
  (flag_pool_addr sg id + 4) # Ptr |-> image.(flagImageHead) **
  store_optional_bytes (flag_pool_addr sg id + 8 + flag_word_bytes sg.(osKernelConfig))
    (skipn 3 image.(flagImagePadding)) **
  (if sg.(osKernelConfig).(cfgFlagNames)
   then (flag_pool_addr sg id + flag_group_name_offset sg.(osKernelConfig)) # Ptr |-> image.(flagImageName)
   else emp) **
  flag_fields_raw_rep_without_group sg state.(FlagState) id **
  UCOS2_raw_rep_missing_flag sg state ** unmap_table_rep sg.

Lemma flag_post_current_word_resources : forall sg state id image,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  state.(FlagState).(flagImages) id = Some image ->
  kernel_program_fields_inv sg state --||--
    coq_prop (UCOS2_state_inv sg state) &&
      ((flag_pool_addr sg id + 8) # UShort |-> image.(flagImageBits) **
       flag_post_current_word_frame sg state id image).
Proof.
  intros sg state id image Hcfg Himage.
  unfold kernel_program_fields_inv, kernel_program_fields_rep, UCOS2_fields_raw_rep,
    flag_fields_configured_rep.
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true) by (rewrite Hcfg; reflexivity).
  rewrite Henabled.
  rewrite (flag_fields_raw_rep_split_group sg state.(FlagState) id image Himage).
  unfold flag_post_current_word_frame, flag_group_rep.
  assert (Hword : flag_word_rep sg.(osKernelConfig) (flag_pool_addr sg id + 8) image.(flagImageBits) =
    ((flag_pool_addr sg id + 8) # UShort |-> image.(flagImageBits))) by (rewrite Hcfg; reflexivity).
  rewrite Hword; split; entailer!.
Qed.

Definition flag_post_current_word_program (id : FlagID) : program UCOS2_Verify_State Z :=
  fun before value after => exists image,
    before.(FlagState).(flagImages) id = Some image /\
    value = image.(flagImageBits) /\ after = before.

Lemma flag_post_current_word_safe_step : forall id current image X,
  current.(FlagState).(flagImages) id = Some image ->
  safeExec (eq current) (flag_post_current_word_program id) X ->
  safeExec (eq current) (StateRelMonad.ret image.(flagImageBits)) X.
Proof.
  intros id current image X Himage Hsafe.
  eapply (highstependret_derive (flag_post_current_word_program id)
    (eq current) image.(flagImageBits) (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; [|reflexivity].
  exists image; auto.
Qed.

(** Actual execution identity: the handler branch is deliberately not a
    fabricated task lease.  Its suspended-task receipt remains in [local]. *)
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_disabled_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_irq_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.flag_fields_publication_spec.

Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_api_entry_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.core.spec.os_init_spec.

Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution.

Inductive FlagPostExecution : Type :=
| FlagPostTask (call : OsSchedCallContext)
| FlagPostHandler (handler : OsExecutionView).

Definition flag_post_execution_view (execution : FlagPostExecution) : OsExecutionView :=
  match execution with
  | FlagPostTask call => os_sched_execution_view call
  | FlagPostHandler handler => handler
  end.

Definition flag_post_execution_active (execution : FlagPostExecution) : option (TaskID * nat) :=
  match execution with
  | FlagPostTask call => task_stack_call_active_key call
  | FlagPostHandler _ => None
  end.

(** Endpoint observations are supplied by the source-entry constructors
    below and by the same-heap paired boundary. Boot is not a task source:
    its no-wait fact is obtained from initializer/module history. *)
Definition flag_post_source_observation (execution : FlagPostExecution) state : Prop :=
  match execution with
  | FlagPostTask call =>
      match call.(os_sched_call_origin) with
      | BootInvocation => flag_state_has_no_waiters state.(FlagState)
      | RunningInvocation _ _ => flag_api_task_entry_observation call state
      end
  | FlagPostHandler handler =>
      if state.(SchedState).(isRunning)
      then sched_disabled_isr_source handler state
      else flag_state_has_no_waiters state.(FlagState)
  end.

Definition flag_post_current_valid (sg : StableGlobVars) execution state : Prop :=
  UCOS2_state_inv sg state /\
  task_stack_live_coverage state.(TskState) (flag_post_execution_active execution) /\
  flag_post_source_observation execution state.

Definition flag_post_same_execution (before after : FlagPostExecution) : Prop :=
  match before, after with
  | FlagPostTask original, FlagPostTask returned =>
      task_tcb_init_stack_same_call returned original
  | FlagPostHandler original, FlagPostHandler returned =>
      (returned).(os_execution_invocation) =
        (original).(os_execution_invocation) /\
      (returned).(os_execution_origin) =
        (original).(os_execution_origin) /\
      (returned).(os_execution_context) =
        (original).(os_execution_context) /\
      (returned).(os_execution_stack) =
        (original).(os_execution_stack)
  | _, _ => False
  end.

(** Boot phase registry condition, restricted to actual registered source
    actions. It is not a theorem for an arbitrary Block/update relation. *)
Definition flag_post_boot_clients (critical : CriticalRegionResources) : Prop :=
  forall action, critical.(critical_region_clients) action ->
    forall sg before after,
      UCOS2_state_inv sg before -> kernel_client_step action sg before after ->
      flag_state_has_no_waiters before.(FlagState) -> flag_state_has_no_waiters after.(FlagState).

Lemma flag_post_boot_interval_no_waiters : forall critical sg invocation before after,
  flag_post_boot_clients critical ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg before -> flag_state_has_no_waiters before.(FlagState) ->
  flag_state_has_no_waiters after.(FlagState).
Proof.
  intros critical sg invocation before after Hclients Hinterval.
  pose proof (critical_region_interval_raw_trace critical sg invocation before after Hinterval) as Htrace.
  clear Hinterval; induction Htrace as
    [state|action first middle last stopped Hin Hforeign Hevent Hstep Htail IH];
    intros Hvalid Hnone; [exact Hnone|].
  apply IH.
  - exact (kernel_client_preserves_validity action
      (critical_region_client_certificates critical action Hin) sg first middle Hvalid Hstep).
  - exact (Hclients action Hin sg first middle Hvalid Hstep Hnone).
Qed.

Definition flag_post_execution_clients (critical : CriticalRegionResources) execution : Prop :=
  match execution with
  | FlagPostTask call =>
      match call.(os_sched_call_origin) with
      | BootInvocation => flag_post_boot_clients critical
      | RunningInvocation _ _ => True
      end
  | FlagPostHandler handler =>
      sched_disabled_completed_clients critical handler /\
      (handler.(os_execution_origin) = BootInvocation -> flag_post_boot_clients critical)
  end.

Definition flag_post_closed (environment : TaskStackCallEnvironment)
  (local : Armv7aContinuation -> Assertion) sg execution mask state : Assertion :=
  kernel_execution_view_owned environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (flag_post_execution_view execution) mask **
  kernel_continuation_inv environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg (flag_post_execution_active execution) state.

Definition flag_post_masked (environment : TaskStackCallEnvironment)
  (critical : CriticalRegionResources) (local : Armv7aContinuation -> Assertion)
  sg execution saved acquired state : Assertion :=
  critical_region_masked environment.(task_stack_call_platform) critical sg
    (flag_post_execution_view execution).(os_execution_invocation)
    (flag_post_execution_view execution).(os_execution_origin) saved acquired **
  os_execution_view_resources environment.(task_stack_call_external)
    (flag_post_execution_view execution) **
  kernel_continuation_inv environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg (flag_post_execution_active execution) state.

Definition flag_post_source_closed environment local sg execution mask state : Assertion :=
  coq_prop (flag_post_source_observation execution state) &&
  flag_post_closed environment local sg execution mask state.
Definition flag_post_source_masked environment critical local sg execution saved acquired state : Assertion :=
  coq_prop (flag_post_source_observation execution state) &&
  flag_post_masked environment critical local sg execution saved acquired state.

Lemma flag_post_task_closed_eq : forall environment local sg call mask state,
  flag_post_closed environment local sg (FlagPostTask call) mask state =
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg (task_stack_call_active_key call) call mask state.
Proof. reflexivity. Qed.

Lemma flag_post_task_masked_eq : forall environment critical local sg call saved acquired state,
  flag_post_masked environment critical local sg (FlagPostTask call) saved acquired state =
  kernel_continuation_call_masked environment.(task_stack_call_continuations)
    kernel_program_fields_inv local critical sg (task_stack_call_active_key call) call saved acquired state.
Proof. reflexivity. Qed.

Lemma flag_post_handler_context_distinct : forall handler call invocation interrupted,
  handler.(os_execution_context) = KernelInterrupt invocation interrupted ->
  (flag_post_execution_view (FlagPostHandler handler)).(os_execution_context) <>
  (flag_post_execution_view (FlagPostTask call)).(os_execution_context).
Proof. intros handler call invocation interrupted Hcontext; cbn; rewrite Hcontext; discriminate. Qed.

(** The C paired-call R/G boundary records completed normal intervals only.
    Every relation below refers to this invocation's actual before/after
    states.  It contains no promised future return and no stable group slot.
    The resource contract must additionally bind these to the same call heaps.
    The task branch retains the registered Save/resumption source; the handler
    branch retains its actual interrupt context and matching nesting. *)
Definition flag_post_save_relation (environment : TaskStackCallEnvironment)
  (critical : CriticalRegionResources) sg original mask saved before returned acquired : Prop :=
  interrupt_saved_value mask saved /\ flag_post_same_execution original returned /\
  kernel_call_control_rely sg before acquired /\
  match original, returned with
  | FlagPostTask call, FlagPostTask after =>
      os_sched_continuation_save_effect environment critical sg call mask saved before after acquired /\
      (match call.(os_sched_call_origin) with
       | BootInvocation => critical_region_interval critical sg call.(os_sched_call_invocation) before acquired
       | RunningInvocation _ _ => True
       end) /\
      task_tcb_init_call_preserved sg call.(os_sched_call_invocation) before acquired /\
      (UCOS2_state_inv sg before -> task_tcb_init_stack_source_preserved call before acquired)
  | FlagPostHandler handler, FlagPostHandler after =>
      critical_region_interval critical sg handler.(os_execution_invocation) before acquired /\
      kernel_interrupt_nesting_agrees before.(SchedState).(isRunning)
        (handler).(os_execution_context) before.(IntrState) /\
      kernel_interrupt_nesting_agrees acquired.(SchedState).(isRunning)
        (after).(os_execution_context) acquired.(IntrState)
  | _, _ => False
  end.

Definition flag_post_restore_relation (environment : TaskStackCallEnvironment)
  (critical : CriticalRegionResources) sg original released returned current : Prop :=
  flag_post_same_execution original returned /\ kernel_call_control_rely sg released current /\
  match original, returned with
  | FlagPostTask call, FlagPostTask after =>
      os_sched_continuation_restore_effect environment critical sg call released after current /\
      (match call.(os_sched_call_origin) with
       | BootInvocation => critical_region_interval critical sg call.(os_sched_call_invocation) released current
       | RunningInvocation _ _ => True
       end) /\
      task_tcb_init_call_preserved sg call.(os_sched_call_invocation) released current /\
      (UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved call released current)
  | FlagPostHandler handler, FlagPostHandler after =>
      critical_region_interval critical sg handler.(os_execution_invocation) released current /\
      kernel_interrupt_nesting_agrees released.(SchedState).(isRunning)
        (handler).(os_execution_context) released.(IntrState) /\
      kernel_interrupt_nesting_agrees current.(SchedState).(isRunning)
        (after).(os_execution_context) current.(IntrState)
  | _, _ => False
  end.

(** Both cases are the actual checked C Scheduler interfaces. The handler
    history retains the precise paired heap events, including the dynamic
    continuation families. No task-context coercion or balanced-lock fact is
    inferred from the weaker disabled context rely. *)
Definition flag_post_scheduler_relation (environment : TaskStackCallEnvironment)
  (critical : CriticalRegionResources) sg original mask before returned current : Prop :=
  match original, returned with
  | FlagPostTask call, FlagPostTask after =>
      os_sched_continuation_call_history environment critical sg call mask before after current
  | FlagPostHandler handler, FlagPostHandler after =>
      exists saved entered acquired local entered_local next_local
        first_heap saved_heap restore_heap final_heap,
        sched_fields_disabled_save_event environment critical sg
          (handler) entered mask saved before acquired
          local entered_local emp first_heap saved_heap /\
        sched_fields_disabled_restore_event environment critical sg entered
          (after) mask saved acquired acquired current
          entered_local next_local emp restore_heap final_heap
  | _, _ => False
  end.

Lemma flag_post_task_scheduler_pre : forall environment local sg call mask state,
  os_sched_call_cut sg call state ->
  flag_post_closed environment local sg (FlagPostTask call) mask state |--
  os_sched_fields_call_pre environment local kernel_program_fields_inv sg call mask state.
Proof. intros; unfold os_sched_fields_call_pre, os_sched_fields_pre; rewrite flag_post_task_closed_eq; entailer!. Qed.

Lemma flag_post_task_scheduler_post : forall environment critical local sg call mask before,
  os_sched_fields_history_return_post environment critical local kernel_program_fields_inv
    sg call mask before |--
  EX returned current,
    coq_prop (flag_post_scheduler_relation environment critical sg (FlagPostTask call)
      mask before (FlagPostTask returned) current /\
      task_tcb_init_stack_same_call returned call /\
      (kernel_call_task_source call before -> kernel_call_task_source returned current)) &&
    flag_post_closed environment local sg (FlagPostTask returned) mask current.
Proof.
  intros; unfold os_sched_fields_history_return_post; Intros returned current.
  Exists returned current; rewrite flag_post_task_closed_eq.
  unfold flag_post_scheduler_relation; entailer!.
Qed.

Record FlagPostObservation := {
  flag_post_error : Z;
  flag_post_value : Z
}.
Definition flag_post_observation error value : FlagPostObservation :=
  {| flag_post_error := error; flag_post_value := value |}.

Definition flag_post_protected_error (result : FlagPostProtectedResult) : option Z :=
  match result with
  | FlagPostProtectedRejected error => Some error
  | FlagPostProtectedScanned _ _ error => error
  end.
Definition flag_post_protected_schedule (result : FlagPostProtectedResult) : bool :=
  match result with
  | FlagPostProtectedRejected _ => false
  | FlagPostProtectedScanned _ visits _ => flag_post_schedule visits
  end.

(** This relation covers all ordered public observations. It deliberately
    separates the protected broadcast word from the final current-slot read.
    A successful read is followed by the LAST Restore before observing X. *)
Definition flag_post_success_tail (environment : TaskStackCallEnvironment)
  (critical : CriticalRegionResources) sg id mask (schedule : bool) original
  : program UCOS2_Verify_State FlagPostObservation :=
  fun before output final => exists after_schedule scheduled saved acquired reader image returned,
    (if schedule then flag_post_scheduler_relation environment critical sg original mask before
       scheduled after_schedule else scheduled = original /\ after_schedule = before) /\
    flag_post_save_relation environment critical sg scheduled mask saved after_schedule reader acquired /\
    acquired.(FlagState).(flagImages) id = Some image /\
    flag_post_restore_relation environment critical sg reader acquired returned final /\
    output = flag_post_observation 0 image.(flagImageBits).

Definition flag_post_after_protected (environment : TaskStackCallEnvironment)
  (critical : CriticalRegionResources) sg id mask original (result : FlagPostProtectedResult)
  : program UCOS2_Verify_State FlagPostObservation :=
  fun released output final => exists returned current,
    flag_post_restore_relation environment critical sg original released returned current /\
    match flag_post_protected_error result with
    | Some error => output = flag_post_observation error 0 /\ final = current
    | None => flag_post_success_tail environment critical sg id mask
        (flag_post_protected_schedule result) returned current output final
    end.

Definition flag_post_api_program (environment : TaskStackCallEnvironment)
  (critical : CriticalRegionResources) sg (pointer : addr) (id : FlagID)
  requested option_word mask original : program UCOS2_Verify_State FlagPostObservation :=
  fun before output final =>
    if Z.eqb pointer 0 then output = flag_post_observation 110 0 /\ final = before
    else exists initial_image,
      before.(FlagState).(flagImages) id = Some initial_image /\
      if Z.eqb initial_image.(flagImageType) 5 then
        exists saved acquired entered result released,
          flag_post_save_relation environment critical sg original mask saved before entered acquired /\
          flag_post_protected_program sg id requested option_word acquired result released /\
          flag_post_after_protected environment critical sg id mask entered result released output final
      else output = flag_post_observation 1 0 /\ final = before.

Definition flag_post_api_safe environment critical sg pointer id requested option_word mask original before
  (X : FlagPostObservation -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before)
    (flag_post_api_program environment critical sg pointer id requested option_word mask original) X.

Lemma flag_post_api_safe_return : forall environment critical sg pointer id requested option_word
  mask original before current output X,
  flag_post_api_program environment critical sg pointer id requested option_word mask original
    before output current ->
  flag_post_api_safe environment critical sg pointer id requested option_word mask original before X ->
  safeExec (eq current) (StateRelMonad.ret output) X.
Proof.
  intros environment critical sg pointer id requested option_word mask original before current output X Hrun Hsafe.
  unfold flag_post_api_safe in Hsafe.
  eapply (highstependret_derive
    (flag_post_api_program environment critical sg pointer id requested option_word mask original)
    (eq before) output (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

Lemma flag_post_api_null_return : forall environment critical sg id requested option_word mask original before X,
  flag_post_api_safe environment critical sg 0 id requested option_word mask original before X ->
  safeExec (eq before) (StateRelMonad.ret (flag_post_observation 110 0)) X.
Proof.
  intros; eapply flag_post_api_safe_return; [|eassumption].
  unfold flag_post_api_program; simpl; auto.
Qed.

Lemma flag_post_api_type_return : forall environment critical sg pointer id requested option_word
  mask original before image X,
  pointer <> 0 -> before.(FlagState).(flagImages) id = Some image -> image.(flagImageType) <> 5 ->
  flag_post_api_safe environment critical sg pointer id requested option_word mask original before X ->
  safeExec (eq before) (StateRelMonad.ret (flag_post_observation 1 0)) X.
Proof.
  intros environment critical sg pointer id requested option_word mask original before image X Hpointer Himage Htype Hsafe.
  eapply flag_post_api_safe_return; [|exact Hsafe].
  unfold flag_post_api_program; assert (Hp : (pointer =? 0) = false) by (apply Z.eqb_neq; exact Hpointer); rewrite Hp.
  exists image; split; [exact Himage|]. assert (Ht : (flagImageType image =? 5) = false) by (apply Z.eqb_neq; exact Htype); rewrite Ht; auto.
Qed.

Lemma flag_post_api_protected_return : forall environment critical sg pointer id requested option_word
  mask original before initial_image saved entered acquired result released returned current error X,
  pointer <> 0 -> before.(FlagState).(flagImages) id = Some initial_image -> initial_image.(flagImageType) = 5 ->
  flag_post_save_relation environment critical sg original mask saved before entered acquired ->
  flag_post_protected_program sg id requested option_word acquired result released ->
  flag_post_protected_error result = Some error ->
  flag_post_restore_relation environment critical sg entered released returned current ->
  flag_post_api_safe environment critical sg pointer id requested option_word mask original before X ->
  safeExec (eq current) (StateRelMonad.ret (flag_post_observation error 0)) X.
Proof.
  intros environment critical sg pointer id requested option_word mask original before initial_image saved entered
    acquired result released returned current error X Hpointer Himage Htype Hsave Hprotected Herror Hrestore Hsafe.
  eapply flag_post_api_safe_return; [|exact Hsafe].
  unfold flag_post_api_program; assert (Hp : (pointer =? 0) = false) by (apply Z.eqb_neq; exact Hpointer); rewrite Hp.
  exists initial_image; split; [exact Himage|]. rewrite Htype, Z.eqb_refl.
  exists saved, acquired, entered, result, released; split; [exact Hsave|]. split; [exact Hprotected|].
  exists returned, current; split; [exact Hrestore|]. rewrite Herror; auto.
Qed.

Lemma flag_post_api_success_return : forall environment critical sg pointer id requested option_word
  mask original before initial_image saved entered acquired result released returned current
  after_schedule scheduled final_saved reader read_state image final_returned final X,
  pointer <> 0 -> before.(FlagState).(flagImages) id = Some initial_image -> initial_image.(flagImageType) = 5 ->
  flag_post_save_relation environment critical sg original mask saved before entered acquired ->
  flag_post_protected_program sg id requested option_word acquired result released ->
  flag_post_protected_error result = None ->
  flag_post_restore_relation environment critical sg entered released returned current ->
  (if flag_post_protected_schedule result then
     flag_post_scheduler_relation environment critical sg returned mask current scheduled after_schedule
   else scheduled = returned /\ after_schedule = current) ->
  flag_post_save_relation environment critical sg scheduled mask final_saved after_schedule reader read_state ->
  read_state.(FlagState).(flagImages) id = Some image ->
  flag_post_restore_relation environment critical sg reader read_state final_returned final ->
  flag_post_api_safe environment critical sg pointer id requested option_word mask original before X ->
  safeExec (eq final) (StateRelMonad.ret (flag_post_observation 0 image.(flagImageBits))) X.
Proof.
  intros environment critical sg pointer id requested option_word mask original before initial_image saved entered acquired
    result released returned current after_schedule scheduled final_saved reader read_state image final_returned final X
    Hpointer Himage Htype Hsave Hprotected Herror Hrestore Hschedule Hreadsave Hread Hlast Hsafe.
  eapply flag_post_api_safe_return; [|exact Hsafe].
  unfold flag_post_api_program; assert (Hp : (pointer =? 0) = false) by (apply Z.eqb_neq; exact Hpointer); rewrite Hp.
  exists initial_image; split; [exact Himage|]. rewrite Htype, Z.eqb_refl.
  exists saved, acquired, entered, result, released; split; [exact Hsave|]. split; [exact Hprotected|].
  exists returned, current; split; [exact Hrestore|]. rewrite Herror.
  exists after_schedule, scheduled, final_saved, read_state, reader, image, final_returned.
  split; [exact Hschedule|]. split; [exact Hreadsave|].
  split; [exact Hread|]. split; [exact Hlast|reflexivity].
Qed.


(** The following events are the explicit, conditional linked-C paired-call
    boundary. They bind ONE actual call footprint, its original saved value,
    the registered source trace and the resources on the actual returned heap.
    They are relations, not resource-creation axioms or ABI-realization proofs.
    In particular [next_local] need not equal [local]: nested wakes may append
    receipts and the returned endpoint must own precisely that resulting map. *)
Definition flag_post_heap_cut (owned : Assertion) (captured : model) : Assertion :=
  fun actual => actual = captured /\ owned actual.

Definition flag_post_paired_closed environment critical local sg execution mask state : Assertion :=
  match execution with
  | FlagPostTask call => coq_prop (flag_post_source_observation execution state) &&
      (os_sched_fields_save_input environment critical local sg call mask state ** unmap_table_rep sg)
  | FlagPostHandler _ => flag_post_source_closed environment local sg execution mask state
  end.
Definition flag_post_paired_masked environment critical local sg execution saved acquired state : Assertion :=
  match execution with
  | FlagPostTask call => coq_prop (flag_post_source_observation execution state) &&
      (os_sched_fields_restore_input environment critical local sg call saved acquired state ** unmap_table_rep sg)
  | FlagPostHandler _ => flag_post_source_masked environment critical local sg execution saved acquired state
  end.

Lemma flag_post_paired_closed_resources : forall environment critical local sg execution mask state,
  flag_post_paired_closed environment critical local sg execution mask state --||--
  flag_post_source_closed environment local sg execution mask state.
Proof.
  intros environment critical local sg [call|handler] mask state; [|split; reflexivity].
  unfold flag_post_paired_closed, flag_post_source_closed.
  rewrite os_sched_fields_save_input_closed_world, flag_post_task_closed_eq; split; reflexivity.
Qed.
Lemma flag_post_paired_masked_resources : forall environment critical local sg execution saved acquired state,
  flag_post_paired_masked environment critical local sg execution saved acquired state --||--
  flag_post_source_masked environment critical local sg execution saved acquired state.
Proof.
  intros environment critical local sg [call|handler] saved acquired state; [|split; reflexivity].
  unfold flag_post_paired_masked, flag_post_source_masked.
  rewrite os_sched_fields_restore_input_masked_world, flag_post_task_masked_eq; split; reflexivity.
Qed.

Definition flag_post_save_event environment critical sg original returned mask saved
  before acquired local next_local (frame : Assertion) (before_heap after_heap : model) : Prop :=
  flag_post_save_relation environment critical sg original mask saved before returned acquired /\
  (flag_post_paired_closed environment critical local sg original mask before ** frame) before_heap /\
  (flag_post_paired_masked environment critical next_local sg returned saved acquired acquired ** frame) after_heap.

Definition flag_post_restore_event environment critical sg original returned mask saved
  acquired released current local next_local (frame : Assertion)
  (before_heap after_heap : model) : Prop :=
  interrupt_saved_value mask saved /\
  flag_post_restore_relation environment critical sg original released returned current /\
  (flag_post_paired_masked environment critical local sg original saved acquired released ** frame) before_heap /\
  (flag_post_paired_closed environment critical next_local sg returned mask current ** frame) after_heap.

Definition flag_post_save_output environment critical sg original mask before local
  (frame : Assertion) (before_heap : model) saved : Assertion :=
  fun after_heap => exists returned acquired next_local,
    flag_post_save_event environment critical sg original returned mask saved
      before acquired local next_local frame before_heap after_heap.

Definition flag_post_restore_output environment critical sg original mask saved acquired released local
  (frame : Assertion) (before_heap : model) : Assertion :=
  fun after_heap => exists returned current next_local,
    flag_post_restore_event environment critical sg original returned mask saved
      acquired released current local next_local frame before_heap after_heap.

Lemma flag_post_heap_capture : forall (owned : Assertion),
  owned |-- EX captured, flag_post_heap_cut owned captured.
Proof. intros owned heap Howned; exists heap; split; [reflexivity|exact Howned]. Qed.

Lemma flag_post_heap_cut_owned : forall owned captured,
  flag_post_heap_cut owned captured |-- owned.
Proof. intros owned captured heap [_ Howned]; exact Howned. Qed.

Lemma flag_post_save_output_resources : forall environment critical sg original mask before local frame before_heap saved,
  flag_post_save_output environment critical sg original mask before local frame before_heap saved |--
  EX returned acquired next_local,
    coq_prop (flag_post_save_relation environment critical sg original mask saved before returned acquired) &&
    (flag_post_source_masked environment critical next_local sg returned saved acquired acquired ** frame).
Proof.
  intros environment critical sg original mask before local frame before_heap saved heap
    [returned [acquired [next_local [Hsource [Hbefore Hafter]]]]].
  exists returned, acquired, next_local; split; [exact Hsource|].
  assert (Hconvert : flag_post_paired_masked environment critical next_local sg returned saved acquired acquired ** frame |--
    flag_post_source_masked environment critical next_local sg returned saved acquired acquired ** frame).
  { rewrite flag_post_paired_masked_resources; reflexivity. }
  exact (Hconvert heap Hafter).
Qed.

Lemma flag_post_restore_output_resources : forall environment critical sg original mask saved acquired released local frame before_heap,
  flag_post_restore_output environment critical sg original mask saved acquired released local frame before_heap |--
  EX returned current next_local,
    coq_prop (interrupt_saved_value mask saved /\
      flag_post_restore_relation environment critical sg original released returned current) &&
    (flag_post_source_closed environment next_local sg returned mask current ** frame).
Proof.
  intros environment critical sg original mask saved acquired released local frame before_heap heap
    [returned [current [next_local [Hsaved [Hsource [Hbefore Hafter]]]]]].
  exists returned, current, next_local; split; [split; assumption|].
  assert (Hconvert : flag_post_paired_closed environment critical next_local sg returned mask current ** frame |--
    flag_post_source_closed environment next_local sg returned mask current ** frame).
  { rewrite flag_post_paired_closed_resources; reflexivity. }
  exact (Hconvert heap Hafter).
Qed.

(** Registration changes only ghost lifecycle data. These fields resources
    contain no invented node padding and the parked family is transported once. *)
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Lemma flag_post_fields_begin_invocation : forall sg state origin,
  task_invocation_origin_live state.(TskState) origin ->
  kernel_program_fields_inv sg state |--
  kernel_program_fields_inv sg (replace_TskS (task_begin_invocation origin state.(TskState)) state).
Proof.
  intros sg state origin Hlive; unfold kernel_program_fields_inv; Intros.
  pose proof (UCOS2_begin_task_invocation_preserves_validity sg state origin H Hlive) as Hvalid.
  assert (Hraw : kernel_program_fields_rep sg
    (replace_TskS (task_begin_invocation origin state.(TskState)) state) =
    kernel_program_fields_rep sg state).
  { assert (Hframe : UCOS2_raw_rep_missing_flag sg
      (replace_TskS (task_begin_invocation origin state.(TskState)) state) =
      UCOS2_raw_rep_missing_flag sg state).
    { apply UCOS2_raw_rep_missing_module_frame; intros m Hdistinct; destruct m;
        cbn [UCOS2_module_rep replace_TskS TskState SchedState IntrState EventState TickState
          FlagState MemoryState TimerState StatsState ControlState NameState]; try reflexivity.
      - apply sched_raw_rep_change_task_index; reflexivity.
      - apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes;
          unfold event_wait_priority_agreement; intros; reflexivity. }
    unfold kernel_program_fields_rep, UCOS2_fields_raw_rep; rewrite Hframe; reflexivity. }
  rewrite Hraw; entailer!.
Qed.

Lemma flag_post_initial_entry_resources : forall environment
  (entry : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations)) sg state saved fragments local,
  armv7a_initial_frame_binding saved ->
  task_stack_fragments_in_range saved.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0 fragments ->
  task_current_at state saved.(armv7a_continuation_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key saved.(armv7a_continuation_stack))) ->
  let call := armv7a_initial_call saved state.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
  kernel_program_fields_inv sg state ** armv7a_initial_execution environment.(task_stack_call_continuations) saved **
  task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion) fragments **
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState) local)
    state.(TskState).(parkedTaskStacks) |--
  coq_prop (kernel_call_task_source call (armv7a_initial_call_registered saved state)) &&
  flag_post_closed environment local sg (FlagPostTask call)
    (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) (armv7a_initial_call_registered saved state).
Proof.
  intros environment entry sg state saved fragments local Hbinding Hfragments Hcurrent Hcoverage call.
  destruct (task_current_at_begin_invocation state
    saved.(armv7a_continuation_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_stack).(stackLeaseGeneration) Hcurrent) as [Hregistered Hactive].
  assert (Hsource : kernel_call_task_source call (armv7a_initial_call_registered saved state)).
  { unfold kernel_call_task_source, call, armv7a_initial_call.
    split; [reflexivity|]. split; [exact Hactive|exact (proj1 Hregistered)]. }
  sep_apply_l_atomic (flag_post_fields_begin_invocation sg state
    (RunningInvocation saved.(armv7a_continuation_stack).(stackLeaseSlot)
      saved.(armv7a_continuation_stack).(stackLeaseGeneration)) (proj2 Hcurrent)).
  sep_apply_l_atomic (armv7a_initial_call_resources _ _ _ _ entry saved
    state.(TskState).(taskLifecycle).(taskNextInvocation) fragments Hbinding Hfragments).
  sep_apply_l_atomic (kernel_saved_continuation_map_used_map_eq _ _ _
    environment.(task_stack_call_continuations) state.(TskState)
    (armv7a_initial_call_registered saved state).(TskState) local state.(TskState).(parkedTaskStacks) eq_refl).
  unfold flag_post_closed, kernel_execution_view_owned, os_execution_view_resources,
    kernel_continuation_inv; cbn [flag_post_execution_view flag_post_execution_active os_sched_execution_view].
  unfold armv7a_initial_call_registered, call, armv7a_initial_call in *; cbn in *; entailer!.
Qed.


Definition flag_post_sequential_state (previous : OsSchedCallContext) state :=
  replace_TskS (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state.

Lemma flag_post_sequential_entry_resources : forall environment
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform)) local sg previous mask state frame before_heap after_heap,
  task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin) ->
  kernel_sequential_call_source boundary previous state.(TskState).(taskLifecycle).(taskNextInvocation)
    before_heap after_heap ->
  (flag_post_closed environment local sg (FlagPostTask previous) mask state ** frame) before_heap ->
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  (kernel_call_task_source previous state ->
    kernel_call_task_source call (flag_post_sequential_state previous state)) /\
  (flag_post_closed environment local sg (FlagPostTask call) mask
    (flag_post_sequential_state previous state) ** frame) after_heap.
Proof.
  intros environment boundary local sg previous mask state frame before_heap after_heap Hlive Hevent Howned call.
  unfold flag_post_closed in Howned; cbn [flag_post_execution_view flag_post_execution_active] in Howned.
  change ((kernel_call_execution_owned environment.(task_stack_call_external)
    environment.(task_stack_call_platform) previous mask **
    kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv local sg
      (task_stack_call_active_key previous) state ** frame) before_heap) in Howned.
  assert (Hassoc : forall P Q R : Assertion, P ** Q ** R |-- P ** (Q ** R)) by (intros; entailer!).
  pose proof (Hassoc _ _ _ before_heap Howned) as Howned_associated.
  destruct (kernel_sequential_call_owned_entry _ _ boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) mask before_heap after_heap
    (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv local sg
      (task_stack_call_active_key previous) state ** frame) Hevent Howned_associated) as [Hmemory Hafter].
  assert (Hnewsource : kernel_call_task_source previous state ->
    kernel_call_task_source call (flag_post_sequential_state previous state)).
  { intro Hsource.
    pose proof (kernel_call_task_source_current_at previous state Hsource) as Hcurrent.
    destruct (task_current_at_begin_invocation state previous.(os_sched_call_stack).(stackLeaseSlot)
      previous.(os_sched_call_stack).(stackLeaseGeneration) Hcurrent) as [Hregistered Hactive].
    destruct Hsource as [Horigin Hsource].
    unfold kernel_call_task_source, call, kernel_sequential_call, flag_post_sequential_state; cbn.
    rewrite Horigin; split; [reflexivity|]. split; [exact Hactive|exact (proj1 Hregistered)]. }
  split; [exact Hnewsource|].
  match type of Hafter with ?P after_heap => match goal with |- ?Q after_heap =>
    assert (Hclose : P |-- Q) end end.
  { unfold kernel_continuation_inv; Intros.
    sep_apply_l_atomic (flag_post_fields_begin_invocation sg state previous.(os_sched_call_origin)
      Hlive).
    sep_apply_l_atomic (kernel_saved_continuation_map_used_map_eq _ _ _
      environment.(task_stack_call_continuations) state.(TskState)
      (flag_post_sequential_state previous state).(TskState) local state.(TskState).(parkedTaskStacks) eq_refl).
    unfold flag_post_closed, kernel_continuation_inv, kernel_execution_view_owned,
      kernel_call_execution_owned, os_execution_view_resources, os_sched_context_resources;
      cbn [flag_post_execution_view flag_post_execution_active os_sched_execution_view].
    unfold flag_post_sequential_state, call, kernel_sequential_call in *; cbn in *; entailer!. }
  exact (Hclose after_heap Hafter).
Qed.

(** Source provenance is attached to the actual entry heap. Initial entries
    own the restored execution resource before the interpretation above;
    sequential entries carry the real predecessor-return/next-entry event;
    handlers carry the port's wrapper source and matching saved exception.
    These constructors never turn an arbitrary world or fresh id into a source. *)
Inductive flag_post_entry_source (environment : TaskStackCallEnvironment)
  (sg : StableGlobVars) : FlagPostExecution -> Z -> UCOS2_Verify_State ->
    (Armv7aContinuation -> Assertion) -> model -> Prop :=
| FlagPostInitialSource : forall
    (entry : Armv7aInitialCallABI environment.(task_stack_call_external) environment.(task_stack_call_platform)
      environment.(task_stack_call_port) environment.(task_stack_call_continuations)) state saved fragments local heap,
    armv7a_initial_frame_binding saved ->
    task_stack_fragments_in_range saved.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0 fragments ->
    task_current_at state saved.(armv7a_continuation_stack).(stackLeaseSlot)
      saved.(armv7a_continuation_stack).(stackLeaseGeneration) ->
    task_stack_live_coverage state.(TskState) (Some (task_stack_key saved.(armv7a_continuation_stack))) ->
    (kernel_program_fields_inv sg state ** armv7a_initial_execution environment.(task_stack_call_continuations) saved **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion) fragments **
      store_parked_continuations
        (kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState) local)
        state.(TskState).(parkedTaskStacks)) heap ->
    flag_post_entry_source environment sg
      (FlagPostTask (armv7a_initial_call saved state.(TskState).(taskLifecycle).(taskNextInvocation) fragments))
      (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr))
      (armv7a_initial_call_registered saved state) local heap
| FlagPostSequentialSource : forall
    (boundary : KernelSequentialCallABI environment.(task_stack_call_external) environment.(task_stack_call_platform)) previous mask state local before_heap after_heap,
    task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin) ->
    kernel_sequential_call_source boundary previous state.(TskState).(taskLifecycle).(taskNextInvocation)
      before_heap after_heap ->
    flag_post_closed environment local sg (FlagPostTask previous) mask state before_heap ->
    flag_post_entry_source environment sg
      (FlagPostTask (kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation)))
      mask (flag_post_sequential_state previous state) local after_heap
| FlagPostHandlerSource : forall handler mask state local heap,
    environment.(task_stack_call_port).(os_int_exit_entry_source) handler ->
    os_int_exit_saved_exception_binding handler state ->
    kernel_interrupt_nesting_agrees state.(SchedState).(isRunning)
      (os_int_exit_execution_view handler).(os_execution_context) state.(IntrState) ->
    flag_post_closed environment local sg (FlagPostHandler (os_int_exit_execution_view handler)) mask state heap ->
    flag_post_entry_source environment sg (FlagPostHandler (os_int_exit_execution_view handler)) mask state local heap.


Definition flag_post_entry_resources environment sg original mask before local : Assertion :=
  flag_post_entry_source environment sg original mask before local.

Lemma flag_post_entry_resources_closed : forall environment sg original mask before local,
  flag_post_entry_resources environment sg original mask before local |--
  flag_post_closed environment local sg original mask before.
Proof.
  intros environment sg original mask before local heap Hentry.
  destruct Hentry as [initialABI state saved fragments local0 heap0 Hb Hf Hc Hcover Ho |
    boundary previous mask0 state local0 pre post Hs He Ho |
    handler mask0 state local0 heap0 Hs Hsaved Hnest Ho].
  - exact (proj2 (flag_post_initial_entry_resources environment initialABI sg state saved fragments local0
      Hb Hf Hc Hcover heap0 Ho)).
  - assert (Hframed : (flag_post_closed environment local0 sg (FlagPostTask previous) mask0 state ** emp) pre).
    { assert (Hframe : flag_post_closed environment local0 sg (FlagPostTask previous) mask0 state |--
        flag_post_closed environment local0 sg (FlagPostTask previous) mask0 state ** emp) by entailer!.
      exact (Hframe pre Ho). }
    destruct (flag_post_sequential_entry_resources environment boundary local0 sg previous mask0 state emp
      pre post Hs He Hframed) as [_ Hafter].
    assert (Hclose : flag_post_closed environment local0 sg
      (FlagPostTask (kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation))) mask0
      (flag_post_sequential_state previous state) ** emp |--
      flag_post_closed environment local0 sg
      (FlagPostTask (kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation))) mask0
      (flag_post_sequential_state previous state)) by entailer!.
    exact (Hclose post Hafter).
  - exact Ho.
Qed.

(** Fixed ARM32 alias-arrow interpretation for the four fields read or
    written by Post beyond the existing Unlink layout. These equalities
    interpret the selected C structs; they impose no dynamic object condition. *)
Local Open Scope string_scope.
Definition flag_post_field_layout : Prop :=
  (forall p, &(p # "os_flag_grp" ->ₛ "OSFlagType") = p) /\
  (forall p, &(p # "os_flag_grp" ->ₛ "OSFlagFlags") = p + 8) /\
  (forall p, &(p # "os_flag_node" ->ₛ "OSFlagNodeFlags") = p + 16) /\
  (forall p, &(p # "os_flag_node" ->ₛ "OSFlagNodeWaitType") = p + 18).
Local Close Scope string_scope.

Definition flag_post_parameters sg pointer id requested option_word : Prop :=
  sg.(osKernelConfig) = selected_kernel_configuration /\
  (pointer = 0 \/ pointer = flag_pool_addr sg id) /\
  0 <= requested < 65536 /\ 0 <= option_word < 256 /\ flag_unlink_layout /\
  kernel_tcb_stack_field_layout sg /\ flag_post_field_layout.

(** Transparent Boot module boundary. Every event below is a completed
    call of a fixed source program on its real state endpoints and the two
    actual owned heaps. Its preservation law is an explicit linked-C module
    obligation; the old weak TaskCreate/Timer post does not prove this law. *)
Inductive FlagPostBootModule := FlagPostBootIdle | FlagPostBootStat | FlagPostBootTimer.
Definition flag_post_boot_module_program p module call before returned after : Prop :=
  match module with
  | FlagPostBootIdle => os_init_idle_program p call before returned after
  | FlagPostBootStat => os_init_stat_program p call before returned after
  | FlagPostBootTimer => os_init_timer_program p call (OsInitKernel before) tt (OsInitKernel after)
  end.
Record FlagPostBootModuleBoundary (p : OsInitContext) := {
  flag_post_boot_module_event : FlagPostBootModule -> OsSchedCallContext -> UCOS2_Verify_State ->
    OsSchedCallContext -> UCOS2_Verify_State -> model -> model -> Prop;
  flag_post_boot_module_source : forall module call before returned after first last,
    flag_post_boot_module_event module call before returned after first last ->
    flag_post_boot_module_program p module call before returned after;
  flag_post_boot_module_same_call : forall module call before returned after first last,
    flag_post_boot_module_event module call before returned after first last ->
    task_tcb_init_stack_same_call returned call;
  flag_post_boot_module_owned : forall module call before returned after first last,
    flag_post_boot_module_event module call before returned after first last ->
    exists local next_local,
      flag_post_closed (os_init_environment p) local (os_init_sg p) (FlagPostTask call)
        (os_init_mask p) before first /\
      flag_post_closed (os_init_environment p) next_local (os_init_sg p) (FlagPostTask returned)
        (os_init_mask p) after last;
  flag_post_boot_module_no_waiters : forall module call before returned after first last,
    flag_post_boot_module_event module call before returned after first last ->
    flag_state_has_no_waiters before.(FlagState) -> flag_state_has_no_waiters after.(FlagState);
  flag_post_boot_client_event : KernelClientAction -> OsSchedCallContext -> UCOS2_Verify_State ->
    OsSchedCallContext -> UCOS2_Verify_State -> model -> model -> Prop;
  flag_post_boot_client_registered : forall action call before returned after first last,
    flag_post_boot_client_event action call before returned after first last ->
    (os_init_critical p).(critical_region_clients) action;
  flag_post_boot_client_source : forall action call before returned after first last,
    flag_post_boot_client_event action call before returned after first last ->
    kernel_client_step action (os_init_sg p) before after;
  flag_post_boot_client_owned : forall action call before returned after first last,
    flag_post_boot_client_event action call before returned after first last ->
    task_tcb_init_stack_same_call returned call /\
    exists local next_local,
      flag_post_closed (os_init_environment p) local (os_init_sg p) (FlagPostTask call)
        (os_init_mask p) before first /\
      flag_post_closed (os_init_environment p) next_local (os_init_sg p) (FlagPostTask returned)
        (os_init_mask p) after last;
  flag_post_boot_client_no_waiters : forall action call before returned after first last,
    flag_post_boot_client_event action call before returned after first last ->
    flag_state_has_no_waiters before.(FlagState) -> flag_state_has_no_waiters after.(FlagState)
}.

Lemma flag_post_boot_registered_no_waiters : forall p,
  flag_state_has_no_waiters (os_init_registered_state p).(FlagState).
Proof.
  intros p; unfold os_init_registered_state, os_init_boot_state, UCOS2_boot_state; cbn.
  destruct (cfgFlagEnabled (osKernelConfig (os_init_sg p)));
    [apply flag_initial_has_no_waiters|split; [intros; discriminate|intros; reflexivity]].
Qed.

Lemma flag_post_no_waiters_padding_empty : forall sg state,
  flag_state_has_no_waiters state.(FlagState) ->
  flag_configured_padding_rep sg state.(FlagState) --||-- emp.
Proof.
  intros sg state [_ Hnodes].
  unfold flag_configured_padding_rep; destruct sg.(osKernelConfig).(cfgFlagEnabled);
    [|split; reflexivity].
  unfold flag_wait_nodes_padding_rep; apply store_map_empty.
  - exists []; split.
    + intros p; split; [contradiction|intros [v Hv]; rewrite Hnodes in Hv; discriminate].
    + constructor.
  - intros q; left; apply Hnodes.
Qed.

Lemma flag_post_boot_registered_fields : forall p local,
  os_init_source_binding p ->
  kernel_stack_call_closed (os_init_environment p).(task_stack_call_continuations)
    kernel_program_inv (os_init_sg p) None p.(os_init_call) (os_init_mask p)
    (os_init_registered_state p) |--
  flag_post_closed (os_init_environment p) local (os_init_sg p)
    (FlagPostTask p.(os_init_call)) (os_init_mask p) (os_init_registered_state p).
Proof.
  intros p local Hbinding.
  assert (Horigin : p.(os_init_call).(os_sched_call_origin) = BootInvocation)
    by (unfold os_init_source_binding in Hbinding; tauto).
  assert (Hactive : task_stack_call_active_key p.(os_init_call) = None)
    by (unfold task_stack_call_active_key; rewrite Horigin; reflexivity).
  assert (Hstack : armv7a_task_stack_continuations (os_init_environment p).(task_stack_call_continuations)
    (os_init_registered_state p).(TskState) (os_init_registered_state p).(TskState).(parkedTaskStacks) --||-- emp).
  { unfold armv7a_task_stack_continuations, store_parked_continuations; apply store_map_empty.
    - exists []; split; [intros; split; [contradiction|intros [v H]; discriminate]|constructor].
    - intros q; left; reflexivity. }
  assert (Hsaved : store_parked_continuations
    (kernel_saved_continuation_entry (os_init_environment p).(task_stack_call_continuations)
      (os_init_registered_state p).(TskState) local)
    (os_init_registered_state p).(TskState).(parkedTaskStacks) --||-- emp).
  { unfold store_parked_continuations; apply store_map_empty.
    - exists []; split; [intros; split; [contradiction|intros [v H]; discriminate]|constructor].
    - intros q; left; reflexivity. }
  rewrite flag_post_task_closed_eq.
  unfold kernel_stack_call_closed, kernel_stack_inv, kernel_continuation_call_closed,
    kernel_continuation_inv.
  rewrite Hactive, Hstack, Hsaved, kernel_program_inv_fields_padding,
    (flag_post_no_waiters_padding_empty (os_init_sg p) (os_init_registered_state p)
      (flag_post_boot_registered_no_waiters p)); entailer!.
Qed.

Definition flag_post_boot_initializer_remainder p : Assertion :=
  os_init_component p 0 true ** os_init_idle_stack p ** os_init_stat_stack p ** os_init_timer_stack p **
  GlobalStrings_missing (os_init_literals p) os_init_literal_keys.

(** The footprint comes from the very same heap that owns all eight
    initializer posts, the loader owner and the source string literals.
    The preserved startup objects are retained in the displayed remainder. *)
Definition flag_post_boot_initializer_event p local owned : Prop :=
  exists whole,
    (os_init_components p 8 ** os_init_loader_frame p ** GlobalStrings (os_init_literals p)) whole /\
    (flag_post_heap_cut
      (flag_post_closed (os_init_environment p) local (os_init_sg p)
        (FlagPostTask p.(os_init_call)) (os_init_mask p) (os_init_registered_state p)) owned **
      flag_post_boot_initializer_remainder p) whole.

Lemma flag_post_boot_initializer_resources : forall p local,
  os_init_source_binding p ->
  os_init_components p 8 ** os_init_loader_frame p ** GlobalStrings (os_init_literals p) |--
  EX owned, coq_prop (flag_post_boot_initializer_event p local owned) &&
    (flag_post_heap_cut
      (flag_post_closed (os_init_environment p) local (os_init_sg p)
        (FlagPostTask p.(os_init_call)) (os_init_mask p) (os_init_registered_state p)) owned **
      flag_post_boot_initializer_remainder p).
Proof.
  intros p local Hbinding.
  assert (Hassemble : os_init_components p 8 ** os_init_loader_frame p ** GlobalStrings (os_init_literals p) |--
    EX owned, flag_post_heap_cut
      (flag_post_closed (os_init_environment p) local (os_init_sg p)
        (FlagPostTask p.(os_init_call)) (os_init_mask p) (os_init_registered_state p)) owned **
      flag_post_boot_initializer_remainder p).
  { sep_apply_l_atomic (os_init_initializers_stack_world p Hbinding).
    sep_apply_l_atomic (os_init_register_boot_world p Hbinding).
    Intros.
    sep_apply_l_atomic (flag_post_boot_registered_fields p local Hbinding).
    sep_apply_l_atomic (flag_post_heap_capture
      (flag_post_closed (os_init_environment p) local (os_init_sg p)
        (FlagPostTask p.(os_init_call)) (os_init_mask p) (os_init_registered_state p))).
    Intros owned; Exists owned; unfold flag_post_boot_initializer_remainder; entailer!. }
  intros whole Hposts; destruct (Hassemble whole Hposts) as [owned Howned].
  exists owned; split; [exists whole; split; assumption|exact Howned].
Qed.

Inductive flag_post_boot_source (p : OsInitContext) (boundary : FlagPostBootModuleBoundary p)
  : nat -> OsSchedCallContext -> UCOS2_Verify_State -> model -> Prop :=
| FlagPostBootInitializers : forall local heap,
    os_init_source_binding p ->
    flag_post_boot_initializer_event p local heap ->
    flag_post_boot_source p boundary 0 p.(os_init_call) (os_init_registered_state p) heap
| FlagPostBootIdleReturned : forall call before first returned after last,
    flag_post_boot_source p boundary 0 call before first ->
    flag_post_boot_module_event p boundary FlagPostBootIdle call before returned after first last ->
    flag_post_boot_source p boundary 1 returned after last
| FlagPostBootStatReturned : forall call before first returned after last,
    flag_post_boot_source p boundary 1 call before first ->
    flag_post_boot_module_event p boundary FlagPostBootStat call before returned after first last ->
    flag_post_boot_source p boundary 2 returned after last
| FlagPostBootTimerReturned : forall call before first returned after last,
    flag_post_boot_source p boundary 2 call before first ->
    flag_post_boot_module_event p boundary FlagPostBootTimer call before returned after first last ->
    flag_post_boot_source p boundary 3 returned after last
| FlagPostBootClientReturned : forall action call before first returned after last,
    flag_post_boot_source p boundary 3 call before first ->
    flag_post_boot_client_event p boundary action call before returned after first last ->
    flag_post_boot_source p boundary 3 returned after last
| FlagPostBootSequential : forall
    (entry : KernelSequentialCallABI (os_init_environment p).(task_stack_call_external)
      (os_init_environment p).(task_stack_call_platform))
    call before local first last,
    flag_post_boot_source p boundary 3 call before first ->
    call.(os_sched_call_origin) = BootInvocation ->
    flag_post_closed (os_init_environment p) local (os_init_sg p) (FlagPostTask call)
      (os_init_mask p) before first ->
    kernel_sequential_call_source entry call before.(TskState).(taskLifecycle).(taskNextInvocation) first last ->
    flag_post_boot_source p boundary 3
      (kernel_sequential_call call before.(TskState).(taskLifecycle).(taskNextInvocation))
      (flag_post_sequential_state call before) last.

Lemma flag_post_boot_source_no_waiters : forall p boundary stage call state heap,
  flag_post_boot_source p boundary stage call state heap ->
  flag_state_has_no_waiters state.(FlagState).
Proof.
  intros p boundary stage call state heap Hsource; induction Hsource.
  - apply flag_post_boot_registered_no_waiters.
  - eapply flag_post_boot_module_no_waiters; eassumption.
  - eapply flag_post_boot_module_no_waiters; eassumption.
  - eapply flag_post_boot_module_no_waiters; eassumption.
  - eapply flag_post_boot_client_no_waiters; eassumption.
  - exact IHHsource.
Qed.

(** Concrete successful allocation action. The source relation is the
    fixed allocator transformer, independently of its preservation theorem.
    A completed-C event must still supply registry membership and the actual
    before/after heap owners through the public Boot module boundary. *)
Definition flag_post_boot_allocate_client (invocation : nat) (bits name : Z) (id : FlagID)
  : KernelClientAction :=
  {| kernel_client_actor := Some invocation;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       sg.(osKernelConfig).(cfgFlagEnabled) = true /\
       flag_word_in_range sg.(osKernelConfig) bits /\
       (sg.(osKernelConfig).(cfgFlagNames) = true ->
         exists chars, readable_name before.(NameState) name chars) /\
       exists flags, flag_allocate before.(FlagState) bits name = Some (id, flags) /\
         after = replace_FlagS flags before |}.

Lemma flag_post_boot_allocate_preserves_no_waiters : forall invocation bits name id sg before after,
  flag_state_has_no_waiters before.(FlagState) ->
  kernel_client_step (flag_post_boot_allocate_client invocation bits name id) sg before after ->
  flag_state_has_no_waiters after.(FlagState).
Proof.
  intros invocation bits name id sg before after Hnone [_ [_ [_ [flags [Hallocate ->]]]]].
  cbn; eapply flag_allocate_preserves_no_waiters; eassumption.
Qed.

Lemma flag_post_boot_allocate_used_group : forall invocation bits name id sg before after,
  kernel_client_step (flag_post_boot_allocate_client invocation bits name id) sg before after ->
  after.(FlagState).(flagUsed) id =
    Some (flag_create_group before.(FlagState).(flagNextGeneration) bits name).
Proof.
  intros invocation bits name id sg before after [_ [_ [_ [flags [Hallocate ->]]]]].
  unfold flag_allocate in Hallocate.
  destruct before.(FlagState).(flagFree) as [|chosen rest]; [discriminate|].
  destruct (before.(FlagState).(flagImages) chosen) as [image|]; [|discriminate].
  injection Hallocate as Hid Hflags; subst id flags; cbn.
  unfold kernel_map_set; destruct (Z.eq_dec chosen chosen); congruence.
Qed.

Lemma flag_post_boot_allocation_source : forall p boundary call before first returned after last bits name id,
  flag_post_boot_source p boundary 3 call before first ->
  flag_post_boot_client_event p boundary
    (flag_post_boot_allocate_client call.(os_sched_call_invocation) bits name id)
    call before returned after first last ->
  flag_post_boot_source p boundary 3 returned after last /\
  flag_state_has_no_waiters after.(FlagState) /\
  after.(FlagState).(flagUsed) id =
    Some (flag_create_group before.(FlagState).(flagNextGeneration) bits name).
Proof.
  intros p boundary call before first returned after last bits name id Hbefore Hevent.
  pose proof (flag_post_boot_client_source p boundary _ _ _ _ _ _ _ Hevent) as Hallocate.
  split; [eapply FlagPostBootClientReturned; eassumption|].
  split.
  - eapply flag_post_boot_allocate_preserves_no_waiters; [|exact Hallocate].
    eapply flag_post_boot_source_no_waiters; exact Hbefore.
  - eapply flag_post_boot_allocate_used_group; exact Hallocate.
Qed.

(** Conditional linked-C boundary for a fixed completed predecessor API.
    The source program, result, returned call/state and both owned heaps
    belong to the same observed C event. Its next-entry ABI is supplied by
    this same interpretation; the public constructor below joins the exact
    returned heap to that actual next entry. The program parameter alone
    cannot create an event or an endpoint observation. *)
Record FlagPostPredecessorBoundary (environment : TaskStackCallEnvironment)
  (sg : StableGlobVars) (A : Type)
  (source : OsSchedCallContext -> program UCOS2_Verify_State A) (mask : Z) : Type := {
  flag_post_predecessor_next_entry :
    KernelSequentialCallABI environment.(task_stack_call_external) environment.(task_stack_call_platform);
  flag_post_predecessor_event : OsSchedCallContext -> UCOS2_Verify_State ->
    (Armv7aContinuation -> Assertion) -> A -> OsSchedCallContext -> UCOS2_Verify_State ->
    (Armv7aContinuation -> Assertion) -> Assertion -> Assertion -> model -> model -> Prop;
  flag_post_predecessor_program : forall original before first_local output returned after local first_frame last_frame first last,
    flag_post_predecessor_event original before first_local output returned after local first_frame last_frame first last ->
    source original before output after;
  flag_post_predecessor_input : forall original before first_local output returned after local first_frame last_frame first last,
    flag_post_predecessor_event original before first_local output returned after local first_frame last_frame first last ->
    (flag_post_closed environment first_local sg (FlagPostTask original) mask before ** first_frame) first;
  flag_post_predecessor_same_call : forall original before first_local output returned after local first_frame last_frame first last,
    flag_post_predecessor_event original before first_local output returned after local first_frame last_frame first last ->
    task_tcb_init_stack_same_call returned original;
  flag_post_predecessor_entry_observation : forall original before first_local output returned after local first_frame last_frame first last,
    flag_post_predecessor_event original before first_local output returned after local first_frame last_frame first last ->
    flag_api_task_entry_observation returned after;
  flag_post_predecessor_endpoint : forall original before first_local output returned after local first_frame last_frame first last,
    flag_post_predecessor_event original before first_local output returned after local first_frame last_frame first last ->
    (flag_post_closed environment local sg (FlagPostTask returned) mask after ** last_frame) last
}.

(** The saved ordinary-memory frame belongs to an interrupted execution view,
    including an outer handler or Boot. It is not a fabricated task lease. *)
Record FlagPostExceptionFrame : Type := {
  flag_post_exception_sp : Z;
  flag_post_exception_cpsr : Z;
  flag_post_exception_registers : list Z;
  flag_post_exception_lr : Z;
  flag_post_exception_pc : Z
}.
Definition flag_post_exception_frame_rep (snapshot : FlagPostExceptionFrame) : Assertion :=
  coq_prop (List.length snapshot.(flag_post_exception_registers) = 13%nat) &&
  UIntArray.mixed_full snapshot.(flag_post_exception_sp) 16
    (map (@Some Z) (snapshot.(flag_post_exception_cpsr) ::
      snapshot.(flag_post_exception_registers) ++
        [snapshot.(flag_post_exception_lr); snapshot.(flag_post_exception_pc)])).

(** One interpretation is fixed by the public C With parameter. Instructions
    and completed-call events are actual finite intervals in that linked
    program. Their resource law uses the same whole heaps as their source
    event; ordinary writes and stack splitting may change the caller frame.
    The current output cell is needed at the actual Post cut only.
    These are explicit conditional module/port interpretations, not proofs
    of all clients, the compiler, exception assembly or eventual return. *)
Record FlagPostLinkedCSource : Type := {
  flag_post_linked_environment : TaskStackCallEnvironment;
  flag_post_linked_globals : StableGlobVars;
  flag_post_linked_initial_abi :
    Armv7aInitialCallABI flag_post_linked_environment.(task_stack_call_external)
      flag_post_linked_environment.(task_stack_call_platform)
      flag_post_linked_environment.(task_stack_call_port)
      flag_post_linked_environment.(task_stack_call_continuations);
  flag_post_linked_task_abi :
    Armv7aTaskContextABI flag_post_linked_environment.(task_stack_call_external)
      flag_post_linked_environment.(task_stack_call_platform)
      flag_post_linked_environment.(task_stack_call_port)
      flag_post_linked_environment.(task_stack_call_continuations);
  flag_post_linked_sequential_abi :
    KernelSequentialCallABI flag_post_linked_environment.(task_stack_call_external)
      flag_post_linked_environment.(task_stack_call_platform);
  flag_post_linked_boot_context : OsInitContext;
  flag_post_linked_boot_boundary : FlagPostBootModuleBoundary flag_post_linked_boot_context;
  flag_post_linked_predecessor_code : Type;
  flag_post_linked_predecessor_result : flag_post_linked_predecessor_code -> Type;
  flag_post_linked_predecessor_program : forall code,
    OsSchedCallContext -> program UCOS2_Verify_State (flag_post_linked_predecessor_result code);
  flag_post_linked_predecessor_boundary : forall code mask,
    FlagPostPredecessorBoundary flag_post_linked_environment flag_post_linked_globals
      (flag_post_linked_predecessor_result code) (flag_post_linked_predecessor_program code) mask;
  flag_post_linked_instruction : Type;
  flag_post_linked_instruction_program : flag_post_linked_instruction ->
    FlagPostExecution -> Z -> program UCOS2_Verify_State (FlagPostExecution * Z);
  flag_post_linked_instruction_event : flag_post_linked_instruction ->
    FlagPostExecution -> Z -> UCOS2_Verify_State -> (Armv7aContinuation -> Assertion) ->
    FlagPostExecution -> Z -> UCOS2_Verify_State -> (Armv7aContinuation -> Assertion) ->
    Assertion -> Assertion -> model -> model -> model -> model -> model -> model -> Prop;
  flag_post_linked_instruction_source : forall instruction original mask before local
    returned next_mask after next_local first_frame last_frame first_remainder last_remainder whole_first whole_last first last,
    flag_post_linked_instruction_event instruction original mask before local
      returned next_mask after next_local first_frame last_frame first_remainder last_remainder whole_first whole_last first last ->
    flag_post_linked_instruction_program instruction original mask before (returned, next_mask) after;
  flag_post_linked_instruction_same_execution : forall instruction original mask before local
    returned next_mask after next_local first_frame last_frame first_remainder last_remainder whole_first whole_last first last,
    flag_post_linked_instruction_event instruction original mask before local
      returned next_mask after next_local first_frame last_frame first_remainder last_remainder whole_first whole_last first last ->
    flag_post_same_execution original returned;
  flag_post_linked_instruction_resources : forall instruction original mask before local
    returned next_mask after next_local first_frame last_frame first_remainder last_remainder whole_first whole_last first last,
    flag_post_linked_instruction_event instruction original mask before local
      returned next_mask after next_local first_frame last_frame first_remainder last_remainder whole_first whole_last first last ->
    (flag_post_source_closed flag_post_linked_environment local flag_post_linked_globals
      original mask before ** first_frame) whole_first ->
    (flag_post_heap_cut
       (flag_post_source_closed flag_post_linked_environment local flag_post_linked_globals
         original mask before) first ** flag_post_heap_cut first_frame first_remainder) whole_first /\
    (flag_post_heap_cut
       (flag_post_source_closed flag_post_linked_environment next_local flag_post_linked_globals
         returned next_mask after) last ** flag_post_heap_cut last_frame last_remainder) whole_last;
  (** Selected non-VFP wrapper's nested and Boot exception interval. The
      event includes actual banked-register reads, frame stores and CPU
      exchange on these heaps. Running first-level task parking remains
      the separate checked source root below. Neither this event nor its
      law registers a task invocation or parks the interrupted task again. *)
  flag_post_linked_exception_event : FlagPostExecution -> Z -> UCOS2_Verify_State ->
    OsExecutionView -> Z -> UCOS2_Verify_State -> FlagPostExceptionFrame ->
    (Armv7aContinuation -> Assertion) -> Assertion -> Assertion -> model -> model -> Prop;
  flag_post_linked_exception_source : forall original mask before handler next_mask after snapshot local
    first_frame retained first last,
    flag_post_linked_exception_event original mask before handler next_mask after snapshot local
      first_frame retained first last ->
    handler.(os_execution_context) =
      KernelInterrupt handler.(os_execution_invocation) (flag_post_execution_view original).(os_execution_context) /\
    handler.(os_execution_origin) = (flag_post_execution_view original).(os_execution_origin) /\
    mask = armv7a_irq_fiq_mask snapshot.(flag_post_exception_cpsr) /\
    after = replace_IntrS (interrupt_enter_state before.(SchedState).(isRunning) before.(IntrState)) before /\
    (before.(SchedState).(isRunning) = true ->
      (exists outer, original = FlagPostHandler outer) /\
      (kernel_interrupt_depth (flag_post_execution_view original).(os_execution_context) < 255)%nat) /\
    (before.(SchedState).(isRunning) = false ->
      forall call, original = FlagPostTask call -> call.(os_sched_call_origin) = BootInvocation);
  flag_post_linked_exception_resources : forall original mask before handler next_mask after snapshot local
    first_frame retained first last,
    flag_post_linked_exception_event original mask before handler next_mask after snapshot local
      first_frame retained first last ->
    (flag_post_source_closed flag_post_linked_environment local flag_post_linked_globals
      original mask before ** first_frame) first ->
    (flag_post_closed flag_post_linked_environment local flag_post_linked_globals
      (FlagPostHandler handler) next_mask after ** (flag_post_exception_frame_rep snapshot ** retained)) last;
  (** Actual OSFlagPost invocation and arguments on the same whole heap
      and resource cut. This relation is not an extra execution step. *)
  flag_post_linked_post_entry : FlagPostExecution -> Z -> UCOS2_Verify_State ->
    (Armv7aContinuation -> Assertion) -> Z -> Z -> Z -> Z ->
    model -> model -> model -> Prop
}.

Lemma flag_post_exception_source_observation : forall linked original mask before handler next_mask after snapshot local
  first_frame retained first last,
  linked.(flag_post_linked_exception_event) original mask before handler next_mask after snapshot local
    first_frame retained first last ->
  flag_post_source_observation original before ->
  flag_post_source_observation (FlagPostHandler handler) after.
Proof.
  intros linked original mask before handler next_mask after snapshot local first_frame retained first last
    Hevent Hsource.
  destruct (flag_post_linked_exception_source linked _ _ _ _ _ _ _ _ _ _ _ _ Hevent)
    as [Hcontext [Horigin [Hmask [Hafter [Hnested Hboot]]]]].
  subst after; cbn [flag_post_source_observation replace_IntrS SchedState FlagState].
  destruct before.(SchedState).(isRunning) eqn:Hrunning.
  - destruct (Hnested eq_refl) as [[outer Houter] Hbound]; subst original.
    cbn [flag_post_source_observation] in Hsource; rewrite Hrunning in Hsource.
    destruct Hsource as [invocation [interrupted [Houter_context [Htrue Hnesting]]]].
    exists handler.(os_execution_invocation), outer.(os_execution_context).
    split; [exact Hcontext|]. split; [exact Hrunning|].
    rewrite Hcontext; cbn [replace_IntrS IntrState].
    apply kernel_interrupt_entry_preserves_nesting_agreement.
    + exact Hnesting.
    + intros _; exact Hbound.
  - destruct original as [call|outer].
    + cbn [flag_post_source_observation] in Hsource.
      rewrite (Hboot eq_refl call eq_refl) in Hsource; exact Hsource.
    + cbn [flag_post_source_observation] in Hsource; rewrite Hrunning in Hsource; exact Hsource.
Qed.

(** Source-produced initial, sequential and IRQ endpoints. The initial
    constructor records the exact publication, prefix/SP/install path and
    actual initial execution owner. Sequential entry consumes a completed
    predecessor C event and the actual next-entry ABI event on that same heap.
    The linked-C completion interpretation remains explicit. *)
Inductive flag_post_source_entry (linked : FlagPostLinkedCSource) : Assertion -> FlagPostExecution -> Z -> UCOS2_Verify_State ->
  (Armv7aContinuation -> Assertion) -> model -> Prop :=
| FlagPostPublishedInitial : forall frame
    publication published_before published selector sp outgoing selected
    current local first installed heap whole,
    kernel_client_step (task_create_stack_publication_client publication) linked.(flag_post_linked_globals) published_before published ->
    selected.(armv7a_continuation_stack).(stackLeaseSlot) = publication.(stack_publication_slot) ->
    selected.(armv7a_continuation_stack).(stackLeaseGeneration) =
      publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration) ->
    current = os_sched_install_context selector outgoing selected.(armv7a_continuation_stack)
      (os_sched_save_current_sp (os_sched_prefix_state published)
        selector.(os_sched_call_stack).(stackLeaseSlot) sp) ->
    os_sched_destination_binding linked.(flag_post_linked_environment).(task_stack_call_external) selector outgoing
      (os_sched_save_current_sp (os_sched_prefix_state published)
        selector.(os_sched_call_stack).(stackLeaseSlot) sp)
      selected.(armv7a_continuation_stack) selected.(armv7a_continuation_fragments) ->
    sched_install_heap_fragment linked.(flag_post_linked_globals) first installed
      (task_slot_addr linked.(flag_post_linked_globals) selected.(armv7a_continuation_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) ->
    armv7a_task_restore_transition linked.(flag_post_linked_task_abi) selector selected installed heap ->
    task_current_at current selected.(armv7a_continuation_stack).(stackLeaseSlot)
      selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
    armv7a_initial_frame_binding selected ->
    task_stack_fragments_in_range
      selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0
      selected.(armv7a_continuation_fragments) ->
    task_stack_live_coverage current.(TskState) (Some (task_stack_key selected.(armv7a_continuation_stack))) ->
    (kernel_program_fields_inv linked.(flag_post_linked_globals) current **
      armv7a_initial_execution linked.(flag_post_linked_environment).(task_stack_call_continuations) selected **
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) **
      store_parked_continuations
        (kernel_saved_continuation_entry linked.(flag_post_linked_environment).(task_stack_call_continuations) current.(TskState) local)
        current.(TskState).(parkedTaskStacks)) heap ->
    (flag_post_heap_cut
      (kernel_program_fields_inv linked.(flag_post_linked_globals) current **
       armv7a_initial_execution linked.(flag_post_linked_environment).(task_stack_call_continuations) selected **
       task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
         selected.(armv7a_continuation_fragments) **
       store_parked_continuations
         (kernel_saved_continuation_entry linked.(flag_post_linked_environment).(task_stack_call_continuations)
           current.(TskState) local) current.(TskState).(parkedTaskStacks)) heap ** frame) whole ->
    flag_post_source_entry linked frame
      (FlagPostTask (armv7a_initial_call selected current.(TskState).(taskLifecycle).(taskNextInvocation)
        selected.(armv7a_continuation_fragments)))
      (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr))
      (armv7a_initial_call_registered selected current) local whole
| FlagPostCompletedSequential : forall code first_frame frame
    previous original start first_local output mask state local start_heap first last,
    flag_post_source_entry linked first_frame (FlagPostTask original) mask start first_local start_heap ->
    flag_post_predecessor_event
      linked.(flag_post_linked_environment) linked.(flag_post_linked_globals)
      (linked.(flag_post_linked_predecessor_result) code)
      (linked.(flag_post_linked_predecessor_program) code) mask
      (linked.(flag_post_linked_predecessor_boundary) code mask)
      original start first_local output previous state local first_frame frame start_heap first ->
    kernel_sequential_call_source
      (flag_post_predecessor_next_entry _ _ _ _ _
        (linked.(flag_post_linked_predecessor_boundary) code mask))
      previous state.(TskState).(taskLifecycle).(taskNextInvocation) first last ->
    flag_post_source_entry linked frame
      (FlagPostTask (kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation)))
      mask (flag_post_sequential_state previous state) local last
| FlagPostActualHandler : forall frame handler mask entry descriptor state local first saved_heap heap whole,
    flag_post_entry_source linked.(flag_post_linked_environment) linked.(flag_post_linked_globals) (FlagPostHandler (os_int_exit_execution_view handler)) mask state local heap ->
    state = armv7a_irq_live_parked_state entry handler.(os_int_exit_interrupted_call)
      descriptor.(armv7a_continuation_sp) descriptor.(armv7a_continuation_fragments) ->
    (os_int_exit_frame_save_pre linked.(flag_post_linked_environment).(task_stack_call_external)
       linked.(flag_post_linked_environment).(task_stack_call_platform) handler **
      (UCOS2_fields_inv linked.(flag_post_linked_globals) entry **
       store_parked_continuations
         (kernel_saved_continuation_entry linked.(flag_post_linked_environment).(task_stack_call_continuations) entry.(TskState) local)
         entry.(TskState).(parkedTaskStacks) ** local descriptor ** unmap_table_rep linked.(flag_post_linked_globals))) first ->
    armv7a_save_transition linked.(flag_post_linked_environment).(task_stack_call_continuations) handler descriptor first saved_heap ->
    kernel_heap_execution (armv7a_irq_live_entry_writes linked.(flag_post_linked_globals) entry
      handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)
      descriptor.(armv7a_continuation_sp)) saved_heap heap ->
    descriptor.(armv7a_continuation_call) = Some handler.(os_int_exit_interrupted_call) ->
    state.(TskState).(parkedTaskStacks)
      (task_stack_key handler.(os_int_exit_interrupted_call).(os_sched_call_stack)) =
      Some (handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseRegion),
        descriptor.(armv7a_continuation_fragments)) ->
    state.(SchedState).(isRunning) = true ->
    kernel_interrupt_nesting_agrees true (os_int_exit_execution_view handler).(os_execution_context) state.(IntrState) ->
    (flag_post_heap_cut
      (flag_post_entry_source linked.(flag_post_linked_environment) linked.(flag_post_linked_globals)
        (FlagPostHandler (os_int_exit_execution_view handler)) mask state local) heap ** frame) whole ->
    flag_post_source_entry linked frame (FlagPostHandler (os_int_exit_execution_view handler)) mask state local whole
| FlagPostInitializedBoot : forall frame call state local first whole_first heap,
    linked.(flag_post_linked_environment) = os_init_environment linked.(flag_post_linked_boot_context) ->
    linked.(flag_post_linked_globals) = os_init_sg linked.(flag_post_linked_boot_context) ->
    flag_post_boot_source linked.(flag_post_linked_boot_context)
      linked.(flag_post_linked_boot_boundary) 3 call state first ->
    call.(os_sched_call_origin) = BootInvocation ->
    flag_post_closed linked.(flag_post_linked_environment) local linked.(flag_post_linked_globals)
      (FlagPostTask call) (os_init_mask linked.(flag_post_linked_boot_context)) state first ->
    (flag_post_heap_cut
      (flag_post_closed linked.(flag_post_linked_environment) local linked.(flag_post_linked_globals)
        (FlagPostTask call) (os_init_mask linked.(flag_post_linked_boot_context)) state) first ** frame) whole_first ->
    kernel_sequential_call_source linked.(flag_post_linked_sequential_abi) call
      state.(TskState).(taskLifecycle).(taskNextInvocation) whole_first heap ->
    flag_post_source_entry linked frame
      (FlagPostTask (kernel_sequential_call call state.(TskState).(taskLifecycle).(taskNextInvocation)))
      (os_init_mask linked.(flag_post_linked_boot_context)) (flag_post_sequential_state call state) local heap
| FlagPostLinkedInstruction : forall instruction original mask before local
    returned next_mask after next_local first_frame last_frame first_remainder last_remainder
    whole_first whole_last first last,
    flag_post_source_entry linked first_frame original mask before local whole_first ->
    linked.(flag_post_linked_instruction_event) instruction original mask before local
      returned next_mask after next_local first_frame last_frame first_remainder last_remainder whole_first whole_last first last ->
    flag_post_source_entry linked last_frame returned next_mask after next_local whole_last
| FlagPostLinkedException : forall original mask before handler next_mask after snapshot local
    first_frame retained first last,
    flag_post_source_entry linked first_frame original mask before local first ->
    linked.(flag_post_linked_exception_event) original mask before handler next_mask after snapshot local
      first_frame retained first last ->
    flag_post_source_entry linked (flag_post_exception_frame_rep snapshot ** retained)
      (FlagPostHandler handler) next_mask after local last.

Lemma flag_post_source_entry_closed : forall linked frame original mask before local,
  flag_post_source_entry linked frame original mask before local |--
  flag_post_source_closed linked.(flag_post_linked_environment) local linked.(flag_post_linked_globals)
    original mask before ** frame.
Proof.
  intros linked frame original mask before local heap Hentry.
  induction Hentry as
    [frame publication published_before published selector sp outgoing selected current local first installed heap whole
      Hpublication Hslot Hgeneration Hcurrent_eq Hdestination Hinstall Hrestore Hcurrent Hbinding Hfragments Hcoverage Howned Hwhole
    |code first_frame frame previous original start first_local output mask state local start_heap first last
      Hstart IHstart Hcompleted Hnext
    |frame handler mask irq_entry descriptor state local first saved_heap heap whole Howned Hparked Hpre Hsave Hwrites
      Hdescriptor Hmap Hrunning Hnesting Hwhole
    |frame call state local first whole_first heap Henvironment Hsg Hsource Hboot Howned Hwhole Hnext
    |instruction original mask before local returned next_mask after next_local first_frame last_frame
      first_remainder last_remainder whole_first whole_last first last Hstart IHstart Hevent
    |original mask before handler next_mask after snapshot local first_frame retained first last
      Hstart IHstart Hevent].
  - set (environment := linked.(flag_post_linked_environment)) in *.
    set (sg := linked.(flag_post_linked_globals)) in *.
    assert (Hobservation : flag_api_task_entry_observation
      (armv7a_initial_call selected current.(TskState).(taskLifecycle).(taskNextInvocation)
        selected.(armv7a_continuation_fragments)) (armv7a_initial_call_registered selected current)).
    { subst current; eapply flag_initial_published_entry_observation; eassumption. }
    match type of Hwhole with ?P whole => match goal with |- ?Q whole =>
      assert (Hconvert : P |-- Q) end end.
    { match goal with |- context [flag_post_heap_cut ?P heap] => sep_apply_l_atomic (flag_post_heap_cut_owned P heap) end.
      pose proof (flag_post_initial_entry_resources environment linked.(flag_post_linked_initial_abi)
        sg current selected selected.(armv7a_continuation_fragments) local Hbinding Hfragments Hcurrent Hcoverage) as Hinitial.
      cbv zeta in Hinitial; sep_apply_l_atomic Hinitial.
      unfold flag_post_source_closed; cbn [flag_post_source_observation].
      entailer!. }
    exact (Hconvert whole Hwhole).
  - set (environment := linked.(flag_post_linked_environment)) in *.
    set (sg := linked.(flag_post_linked_globals)) in *.
    set (A := linked.(flag_post_linked_predecessor_result) code).
    set (source := linked.(flag_post_linked_predecessor_program) code).
    set (completed := linked.(flag_post_linked_predecessor_boundary) code mask).
    pose proof (flag_post_predecessor_entry_observation environment sg A source mask
      completed original start first_local output previous state local first_frame frame start_heap first Hcompleted) as Hentry.
    pose proof (flag_post_predecessor_endpoint environment sg A source mask
      completed original start first_local output previous state local first_frame frame start_heap first Hcompleted) as Howned.
    assert (Hlive : task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin)).
    { pose proof (kernel_call_task_source_current_at previous state (proj1 Hentry)) as [_ Hl].
      rewrite (proj1 (proj1 Hentry)); exact Hl. }
    destruct (flag_post_sequential_entry_resources environment
      (flag_post_predecessor_next_entry environment sg A source mask completed)
      local sg previous mask state frame first last Hlive Hnext Howned) as [_ Hafter].
    assert (Hobservation : flag_post_source_observation
      (FlagPostTask (kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation)))
      (flag_post_sequential_state previous state)).
    { unfold flag_post_source_observation, kernel_sequential_call; cbn [os_sched_call_origin].
      rewrite (proj1 (proj1 Hentry)).
      pose proof (flag_sequential_entry_observation previous state Hentry) as Hnew.
      unfold kernel_sequential_call in Hnew; rewrite (proj1 (proj1 Hentry)) in Hnew.
      exact Hnew. }
    match type of Hafter with ?P last => match goal with |- ?Q last =>
      assert (Hconvert : P |-- Q) end end.
    { unfold flag_post_source_closed; entailer!. }
    exact (Hconvert last Hafter).
  - assert (Hobservation : flag_post_source_observation (FlagPostHandler (os_int_exit_execution_view handler)) state).
    { cbn [flag_post_source_observation]; rewrite Hrunning.
      exists handler.(os_int_exit_invocation),
        (KernelCaller handler.(os_int_exit_interrupted_call).(os_sched_call_invocation)
          handler.(os_int_exit_interrupted_call).(os_sched_call_origin)); repeat split; assumption || reflexivity. }
    match type of Hwhole with ?P whole => match goal with |- ?Q whole =>
      assert (Hconvert : P |-- Q) end end.
    { match goal with |- context [flag_post_heap_cut ?P heap] => sep_apply_l_atomic (flag_post_heap_cut_owned P heap) end.
      sep_apply_l_atomic (flag_post_entry_resources_closed linked.(flag_post_linked_environment)
        linked.(flag_post_linked_globals) (FlagPostHandler (os_int_exit_execution_view handler)) mask state local).
      unfold flag_post_source_closed; entailer!. }
    exact (Hconvert whole Hwhole).
  - assert (Hlive : task_invocation_origin_live state.(TskState) call.(os_sched_call_origin)).
    { unfold task_invocation_origin_live; rewrite Hboot; exact I. }
    assert (Hinput :
      (flag_post_closed linked.(flag_post_linked_environment) local linked.(flag_post_linked_globals)
        (FlagPostTask call) (os_init_mask linked.(flag_post_linked_boot_context)) state ** frame) whole_first).
    { match type of Hwhole with ?P whole_first => match goal with |- ?Q whole_first =>
        assert (Hconvert : P |-- Q) end end.
      { match goal with |- context [flag_post_heap_cut ?P first] => sep_apply_l_atomic (flag_post_heap_cut_owned P first) end; entailer!. }
      exact (Hconvert whole_first Hwhole). }
    destruct (flag_post_sequential_entry_resources linked.(flag_post_linked_environment)
      linked.(flag_post_linked_sequential_abi) local linked.(flag_post_linked_globals) call
      (os_init_mask linked.(flag_post_linked_boot_context)) state frame whole_first heap Hlive Hnext Hinput)
      as [_ Hafter].
    assert (Hobservation : flag_post_source_observation
      (FlagPostTask (kernel_sequential_call call state.(TskState).(taskLifecycle).(taskNextInvocation)))
      (flag_post_sequential_state call state)).
    { unfold flag_post_source_observation, kernel_sequential_call; cbn [os_sched_call_origin].
      rewrite Hboot; change (flag_state_has_no_waiters state.(FlagState)).
      eapply flag_post_boot_source_no_waiters; exact Hsource. }
    match type of Hafter with ?P heap => match goal with |- ?Q heap =>
      assert (Hconvert : P |-- Q) end end.
    { unfold flag_post_source_closed; entailer!. }
    exact (Hconvert heap Hafter).
  - pose proof (proj2 (flag_post_linked_instruction_resources linked instruction original mask before local
      returned next_mask after next_local first_frame last_frame first_remainder last_remainder
      whole_first whole_last first last Hevent IHstart)) as Hafter.
    match type of Hafter with ?P whole_last => match goal with |- ?Q whole_last =>
      assert (Hconvert : P |-- Q) end end.
    { match goal with |- context [flag_post_heap_cut ?P last] => sep_apply_l_atomic (flag_post_heap_cut_owned P last) end.
      match goal with |- context [flag_post_heap_cut ?P last_remainder] => sep_apply_l_atomic (flag_post_heap_cut_owned P last_remainder) end.
      entailer!. }
    exact (Hconvert whole_last Hafter).
  - assert (Hbefore : flag_post_source_observation original before).
    { destruct IHstart as [owned [remainder [Hjoin [[Hsource Howned] Hframe]]]]; exact Hsource. }
    pose proof (flag_post_exception_source_observation linked _ _ _ _ _ _ _ _ _ _ _ _ Hevent Hbefore) as Hobservation.
    pose proof (flag_post_linked_exception_resources linked original mask before handler next_mask after snapshot local
      first_frame retained first last Hevent IHstart) as Hafter.
    match type of Hafter with ?P last => match goal with |- ?Q last =>
      assert (Hconvert : P |-- Q) end end.
    { unfold flag_post_source_closed; entailer!. }
    exact (Hconvert last Hafter).
Qed.

(** The checked Boot allocation component is retained. Its source-to-entry
    instance now uses the fixed interpretation and the actual framed heaps. *)
Lemma flag_post_boot_allocation_next_entry : forall linked frame
  call before first returned after last whole_last next bits name id,
  linked.(flag_post_linked_environment) = os_init_environment linked.(flag_post_linked_boot_context) ->
  linked.(flag_post_linked_globals) = os_init_sg linked.(flag_post_linked_boot_context) ->
  flag_post_boot_source linked.(flag_post_linked_boot_context) linked.(flag_post_linked_boot_boundary)
    3 call before first ->
  call.(os_sched_call_origin) = BootInvocation ->
  flag_post_boot_client_event linked.(flag_post_linked_boot_context) linked.(flag_post_linked_boot_boundary)
    (flag_post_boot_allocate_client call.(os_sched_call_invocation) bits name id)
    call before returned after first last ->
  (forall local, flag_post_closed linked.(flag_post_linked_environment) local linked.(flag_post_linked_globals)
      (FlagPostTask returned) (os_init_mask linked.(flag_post_linked_boot_context)) after last ->
    (flag_post_heap_cut
      (flag_post_closed linked.(flag_post_linked_environment) local linked.(flag_post_linked_globals)
        (FlagPostTask returned) (os_init_mask linked.(flag_post_linked_boot_context)) after) last ** frame) whole_last) ->
  kernel_sequential_call_source linked.(flag_post_linked_sequential_abi) returned
    after.(TskState).(taskLifecycle).(taskNextInvocation) whole_last next ->
  exists local,
    flag_post_source_entry linked frame
      (FlagPostTask (kernel_sequential_call returned after.(TskState).(taskLifecycle).(taskNextInvocation)))
      (os_init_mask linked.(flag_post_linked_boot_context)) (flag_post_sequential_state returned after) local next /\
    (flag_post_sequential_state returned after).(FlagState).(flagUsed) id =
      Some (flag_create_group before.(FlagState).(flagNextGeneration) bits name).
Proof.
  intros linked frame call before first returned after last whole_last next bits name id
    Henvironment Hsg Hsource Hboot Hallocate Hframe Hnext.
  destruct (flag_post_boot_allocation_source linked.(flag_post_linked_boot_context)
    linked.(flag_post_linked_boot_boundary) call before first returned after last bits name id Hsource Hallocate)
    as [Hafter [Hnone Hgroup]].
  destruct (flag_post_boot_client_owned linked.(flag_post_linked_boot_context)
    linked.(flag_post_linked_boot_boundary) _ _ _ _ _ _ _ Hallocate)
    as [Hsame [previous_local [local [Hfirst Hlast]]]].
  assert (Howned : flag_post_closed linked.(flag_post_linked_environment) local linked.(flag_post_linked_globals)
    (FlagPostTask returned) (os_init_mask linked.(flag_post_linked_boot_context)) after last).
  { rewrite Henvironment, Hsg; exact Hlast. }
  exists local; split; [|exact Hgroup].
  eapply FlagPostInitializedBoot with (first := last) (whole_first := whole_last); try eassumption.
  - rewrite (proj1 (proj2 Hsame)); exact Hboot.
  - apply Hframe; exact Howned.
Qed.

(** A source cut is accepted only at the actual Post invocation in the fixed
    linked interpretation. The call cut observes the same whole heap split,
    source owner, caller output cell and frame; it does not allocate resources. *)
Definition flag_post_actual_call_entry (linked : FlagPostLinkedCSource)
  original mask before local pointer requested option_word error_cell old_error (frame : Assertion) : Assertion :=
  fun whole =>
    flag_post_source_entry linked (error_cell # UChar |-> old_error ** frame)
      original mask before local whole /\
    exists owned remainder,
      linked.(flag_post_linked_post_entry) original mask before local pointer requested option_word error_cell
        whole owned remainder /\
      (flag_post_heap_cut
        (flag_post_source_closed linked.(flag_post_linked_environment) local linked.(flag_post_linked_globals)
          original mask before) owned **
        flag_post_heap_cut (error_cell # UChar |-> old_error ** frame) remainder) whole.

Definition flag_post_public_pre (linked : FlagPostLinkedCSource) environment critical sg original mask before local
  pointer id requested option_word error_cell old_error (frame : Assertion)
  (X : FlagPostObservation -> UCOS2_Verify_State -> Prop) : Assertion :=
  coq_prop (linked.(flag_post_linked_environment) = environment /\ linked.(flag_post_linked_globals) = sg /\
    flag_post_parameters sg pointer id requested option_word /\
    (pointer <> 0 -> exists image, before.(FlagState).(flagImages) id = Some image) /\
    flag_post_api_safe environment critical sg pointer id requested option_word mask original before X) &&
  flag_post_actual_call_entry linked original mask before local pointer requested option_word error_cell old_error frame.

Lemma flag_post_actual_call_entry_resources : forall linked original mask before local pointer requested option_word
  error_cell old_error frame,
  flag_post_actual_call_entry linked original mask before local pointer requested option_word error_cell old_error frame |--
  flag_post_source_closed linked.(flag_post_linked_environment) local linked.(flag_post_linked_globals)
    original mask before ** error_cell # UChar |-> old_error ** frame.
Proof.
  intros linked original mask before local pointer requested option_word error_cell old_error frame whole [Hsource Hentry].
  pose proof (flag_post_source_entry_closed linked (error_cell # UChar |-> old_error ** frame)
    original mask before local whole Hsource) as Howned.
  assert (Hassoc : forall P Q R : Assertion, P ** (Q ** R) |-- P ** Q ** R) by (intros; entailer!).
  exact (Hassoc _ _ _ whole Howned).
Qed.

Definition flag_post_public_post environment sg original mask error_cell returned_value frame
  (X : FlagPostObservation -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current local error,
    coq_prop (flag_post_same_execution original returned /\
      safeExec (eq current) (StateRelMonad.ret (flag_post_observation error returned_value)) X) &&
    (flag_post_source_closed environment local sg returned mask current **
      error_cell # UChar |-> error ** frame).

(** Opened group/node resources used at the actual C loads and stores. *)
Definition flag_post_group_frame sg state id : Assertion :=
  flag_fields_raw_rep_without_group sg state.(FlagState) id **
  UCOS2_raw_rep_missing_flag sg state ** unmap_table_rep sg.
Definition flag_post_type_frame sg state id image : Assertion :=
  store_optional_bytes (flag_pool_addr sg id + 1) (firstn 3 image.(flagImagePadding)) **
  (flag_pool_addr sg id + 4) # Ptr |-> image.(flagImageHead) **
  flag_word_rep sg.(osKernelConfig) (flag_pool_addr sg id + 8) image.(flagImageBits) **
  store_optional_bytes (flag_pool_addr sg id + 8 + flag_word_bytes sg.(osKernelConfig))
    (skipn 3 image.(flagImagePadding)) **
  (if sg.(osKernelConfig).(cfgFlagNames)
   then (flag_pool_addr sg id + flag_group_name_offset sg.(osKernelConfig)) # Ptr |-> image.(flagImageName)
   else emp) ** flag_post_group_frame sg state id.

Definition flag_post_execution_frame environment local (sg : StableGlobVars) original mask state : Assertion :=
  coq_prop (flag_post_source_observation original state) && (kernel_execution_view_owned environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (flag_post_execution_view original) mask **
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState) local)
    state.(TskState).(parkedTaskStacks)).
Definition flag_post_critical_frame environment critical local sg execution saved acquired state : Assertion :=
  coq_prop (flag_post_source_observation execution state) && (critical_region_masked environment.(task_stack_call_platform) critical sg
    (flag_post_execution_view execution).(os_execution_invocation)
    (flag_post_execution_view execution).(os_execution_origin) saved acquired **
  os_execution_view_resources environment.(task_stack_call_external) (flag_post_execution_view execution) **
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState) local)
    state.(TskState).(parkedTaskStacks)).

Definition flag_post_prefix environment critical sg pointer id (requested option_word : Z) mask original before
  initial_image saved entered acquired : Prop :=
  pointer <> 0 /\ before.(FlagState).(flagImages) id = Some initial_image /\ initial_image.(flagImageType) = 5 /\
  flag_post_save_relation environment critical sg original mask saved before entered acquired.

Definition flag_post_loop_state sg id requested option_word acquired posted initial_order
  visited remaining scan : Prop :=
  exists group image,
    acquired.(FlagState).(flagUsed) id = Some group /\ acquired.(FlagState).(flagImages) id = Some image /\
    image.(flagImageType) = 5 /\ flag_post_bits sg.(osKernelConfig) image.(flagImageBits) requested option_word = Some posted /\
    initial_order = group.(flagWaitOrder) /\ initial_order = visited ++ remaining /\
    flag_post_scan sg posted
      (replace_FlagS (flag_replace_bits acquired.(FlagState) id group image posted) acquired) visited = Some scan /\
    scan.(flag_post_scan_error) = None /\
    (exists current_group current_image kept,
      scan.(flag_post_scan_state).(FlagState).(flagUsed) id = Some current_group /\
      scan.(flag_post_scan_state).(FlagState).(flagImages) id = Some current_image /\
      current_image.(flagImageBits) = posted /\ current_group.(flagWaitOrder) = kept ++ remaining).

Definition flag_post_remaining_node (remaining : list addr) : addr :=
  match remaining with [] => 0 | node :: _ => node end.
Definition flag_post_schedule_word visits : Z := if flag_post_schedule visits then 1 else 0.

Definition flag_post_loop_resources environment critical sg execution saved acquired local
  id requested option_word posted initial_order visited remaining scan : Assertion :=
  coq_prop (flag_post_loop_state sg id requested option_word acquired posted initial_order visited remaining scan) &&
  flag_post_source_masked environment critical local sg execution saved acquired scan.(flag_post_scan_state).


Record FlagPostProtectedContext := {
  flag_post_initial_image : FlagGroupImage;
  flag_post_entered : FlagPostExecution;
  flag_post_acquired : UCOS2_Verify_State;
  flag_post_local : Armv7aContinuation -> Assertion
}.
(** The protected recheck only requires a live image for SET/CLR.
    An invalid option still follows its ordered error branch for any type. *)
Definition flag_post_checked_type (option_word : Z) (image : FlagGroupImage) : Prop :=
  flag_post_valid_option option_word = true -> image.(flagImageType) = 5.

Definition flag_post_protected_facts environment critical sg pointer id requested option_word mask original before
  saved (context : FlagPostProtectedContext) : Prop :=
  flag_post_prefix environment critical sg pointer id requested option_word mask original before
    context.(flag_post_initial_image) saved context.(flag_post_entered) context.(flag_post_acquired) /\
  flag_post_current_valid sg context.(flag_post_entered) context.(flag_post_acquired).
(** Retain the initial fixed-pool index only until the acquired slot is
    localized. Its range comes from the actual before heap of the Save event;
    the acquired image is still selected from the returned current world. *)
Definition flag_post_protected_cut environment critical sg pointer id requested option_word mask original before
  saved context : Assertion :=
  coq_prop (0 <= id < sg.(osKernelConfig).(cfgMaxFlags) /\
    flag_post_protected_facts environment critical sg pointer id requested option_word mask original before saved context) &&
  flag_post_source_masked environment critical context.(flag_post_local) sg context.(flag_post_entered) saved
    context.(flag_post_acquired) context.(flag_post_acquired).

Record FlagPostLoopContext := {
  flag_post_loop_entry : FlagPostProtectedContext;
  flag_post_posted_word : Z;
  flag_post_initial_order : list addr;
  flag_post_visited : list addr;
  flag_post_remaining : list addr;
  flag_post_accumulator : FlagPostScan;
  flag_post_loop_local : Armv7aContinuation -> Assertion
}.
(** Used only before the one-time group-head load, never on the loop back edge. *)
Definition flag_post_initial_scan (context : FlagPostLoopContext) : Prop :=
  context.(flag_post_visited) = [].

Definition flag_post_waiter_satisfied (sg : StableGlobVars) (context : FlagPostLoopContext)
  (waiter : FlagWaiterState) (ready : Z) : Prop :=
  flag_post_node_test sg.(osKernelConfig) context.(flag_post_posted_word)
    waiter.(flagWaitImage).(flagNodeMask) waiter.(flagWaitImage).(flagNodeMode) = Some (ready, true).

Definition flag_post_loop_facts environment critical sg pointer id requested option_word mask original before
  saved (context : FlagPostLoopContext) node schedule : Prop :=
  flag_post_protected_facts environment critical sg pointer id requested option_word mask original before saved
    context.(flag_post_loop_entry) /\
  flag_post_loop_state sg id requested option_word context.(flag_post_loop_entry).(flag_post_acquired)
    context.(flag_post_posted_word) context.(flag_post_initial_order) context.(flag_post_visited)
    context.(flag_post_remaining) context.(flag_post_accumulator) /\
  node = flag_post_remaining_node context.(flag_post_remaining) /\
  schedule = flag_post_schedule_word context.(flag_post_accumulator).(flag_post_scan_visits) /\
  flag_post_current_valid sg context.(flag_post_loop_entry).(flag_post_entered)
    context.(flag_post_accumulator).(flag_post_scan_state).
Definition flag_post_loop_cut environment critical sg pointer id requested option_word mask original before
  saved context node schedule : Assertion :=
  coq_prop (flag_post_loop_facts environment critical sg pointer id requested option_word mask original before saved context node schedule) &&
  flag_post_source_masked environment critical context.(flag_post_loop_local) sg
    context.(flag_post_loop_entry).(flag_post_entered) saved context.(flag_post_loop_entry).(flag_post_acquired)
    context.(flag_post_accumulator).(flag_post_scan_state).

Definition flag_post_node_word_frame sg state id node image : Assertion :=
  flag_pool_addr sg id # UChar |-> image.(flagImageType) **
  store_optional_bytes (flag_pool_addr sg id + 1) (firstn 3 image.(flagImagePadding)) **
  (flag_pool_addr sg id + 4) # Ptr |-> image.(flagImageHead) **
  store_optional_bytes (flag_pool_addr sg id + 8 + flag_word_bytes sg.(osKernelConfig))
    (skipn 3 image.(flagImagePadding)) **
  (if sg.(osKernelConfig).(cfgFlagNames)
   then (flag_pool_addr sg id + flag_group_name_offset sg.(osKernelConfig)) # Ptr |-> image.(flagImageName)
   else emp) ** flag_groups_without sg state.(FlagState) id **
  flag_wait_nodes_fields_without_node sg state.(FlagState).(flagWaitNodes) node **
  sg.(g_OSFlagFreeList) # Ptr |->
    (match state.(FlagState).(flagFree) with [] => 0 | first :: _ => flag_pool_addr sg first end) **
  UCOS2_raw_rep_missing_flag sg state ** unmap_table_rep sg.

Record FlagPostPendingVisit := {
  flag_post_pending_loop : FlagPostLoopContext;
  flag_post_pending_waiter : FlagWaiterState;
  flag_post_pending_ready : Z;
  flag_post_pending_returned : option bool;
  flag_post_pending_state : UCOS2_Verify_State;
  flag_post_pending_lease : TaskStackLease
}.
Definition flag_post_pending_facts sg pending node schedule : Prop :=
  let context := pending.(flag_post_pending_loop) in
  let scan := context.(flag_post_accumulator) in
  let waiter := pending.(flag_post_pending_waiter) in
  node = flag_post_remaining_node context.(flag_post_remaining) /\
  scan.(flag_post_scan_state).(FlagState).(flagWaitNodes) node = Some waiter /\ waiter.(flagNodeAddr) = node /\
  (match pending.(flag_post_pending_returned) with
   | None => flag_post_node_test sg.(osKernelConfig) context.(flag_post_posted_word)
       waiter.(flagWaitImage).(flagNodeMask) waiter.(flagWaitImage).(flagNodeMode) =
       Some (pending.(flag_post_pending_ready), false) /\ pending.(flag_post_pending_state) = scan.(flag_post_scan_state)
   | Some returned => flag_post_node_test sg.(osKernelConfig) context.(flag_post_posted_word)
       waiter.(flagWaitImage).(flagNodeMask) waiter.(flagWaitImage).(flagNodeMode) =
       Some (pending.(flag_post_pending_ready), true) /\
       flag_task_rdy sg scan.(flag_post_scan_state) node pending.(flag_post_pending_ready) PendOK =
         Some (returned, pending.(flag_post_pending_state)) /\
       task_stack_key pending.(flag_post_pending_lease) = (waiter.(flagTask), waiter.(flagTaskGeneration)) /\
       exists fragments, scan.(flag_post_scan_state).(TskState).(parkedTaskStacks)
         (task_stack_key pending.(flag_post_pending_lease)) = Some (pending.(flag_post_pending_lease).(stackLeaseRegion), fragments)
   end) /\
  schedule = (if (flag_post_schedule scan.(flag_post_scan_visits) ||
    match pending.(flag_post_pending_returned) with None => false | Some returned => returned end)%bool then 1 else 0).

Definition flag_post_pending_world sg pending node : Assertion :=
  match pending.(flag_post_pending_returned) with
  | None => coq_prop (UCOS2_state_inv sg pending.(flag_post_pending_state)) &&
      flag_post_registered_node_frame sg pending.(flag_post_pending_state) node
  | Some _ => kernel_program_fields_inv sg pending.(flag_post_pending_state)
  end.
Definition flag_post_next_cut environment critical sg pointer id requested option_word mask original before
  saved pending node schedule : Assertion :=
  coq_prop (flag_post_loop_facts environment critical sg pointer id requested option_word mask original before saved
      pending.(flag_post_pending_loop) node
      (flag_post_schedule_word pending.(flag_post_pending_loop).(flag_post_accumulator).(flag_post_scan_visits)) /\
    flag_post_pending_facts sg pending node schedule /\
    flag_post_current_valid sg pending.(flag_post_pending_loop).(flag_post_loop_entry).(flag_post_entered)
      pending.(flag_post_pending_state)) &&
  (flag_node_fields_return_loan sg.(osKernelConfig) pending.(flag_post_pending_waiter) **
   flag_post_pending_world sg pending node **
   flag_post_critical_frame environment critical pending.(flag_post_pending_loop).(flag_post_loop_local) sg
     pending.(flag_post_pending_loop).(flag_post_loop_entry).(flag_post_entered) saved
     pending.(flag_post_pending_loop).(flag_post_loop_entry).(flag_post_acquired) pending.(flag_post_pending_state)).

Definition flag_post_exit_cut environment critical sg pointer id requested option_word mask original before
  saved entry result released local : Assertion :=
  coq_prop (flag_post_protected_facts environment critical sg pointer id requested option_word mask original before saved entry /\
    flag_post_protected_program sg id requested option_word entry.(flag_post_acquired) result released) &&
  flag_post_source_masked environment critical local sg entry.(flag_post_entered) saved entry.(flag_post_acquired) released.

Record FlagPostReleasedContext := {
  flag_post_released_entry : FlagPostProtectedContext;
  flag_post_released_result : FlagPostProtectedResult;
  flag_post_released_state : UCOS2_Verify_State;
  flag_post_released_execution : FlagPostExecution;
  flag_post_restored_state : UCOS2_Verify_State;
  flag_post_restored_local : Armv7aContinuation -> Assertion
}.
Definition flag_post_restored_facts environment critical sg pointer id requested option_word mask original before saved context : Prop :=
  flag_post_protected_facts environment critical sg pointer id requested option_word mask original before saved
    context.(flag_post_released_entry) /\
  flag_post_protected_program sg id requested option_word context.(flag_post_released_entry).(flag_post_acquired)
    context.(flag_post_released_result) context.(flag_post_released_state) /\
  flag_post_restore_relation environment critical sg context.(flag_post_released_entry).(flag_post_entered)
    context.(flag_post_released_state) context.(flag_post_released_execution) context.(flag_post_restored_state).
Definition flag_post_restored_cut environment critical sg pointer id requested option_word mask original before saved context : Assertion :=
  coq_prop (flag_post_restored_facts environment critical sg pointer id requested option_word mask original before saved context) &&
  flag_post_source_closed environment context.(flag_post_restored_local) sg context.(flag_post_released_execution)
    mask context.(flag_post_restored_state).

Record FlagPostReadContext := {
  flag_post_read_prefix : FlagPostReleasedContext;
  flag_post_scheduled_execution : FlagPostExecution;
  flag_post_scheduled_state : UCOS2_Verify_State;
  flag_post_reader : FlagPostExecution;
  flag_post_read_state : UCOS2_Verify_State;
  flag_post_read_image : FlagGroupImage;
  flag_post_read_local : Armv7aContinuation -> Assertion
}.
Definition flag_post_read_facts environment critical sg pointer id requested option_word mask original before first_saved read_saved context : Prop :=
  let prefix := context.(flag_post_read_prefix) in
  flag_post_restored_facts environment critical sg pointer id requested option_word mask original before first_saved prefix /\
  flag_post_protected_error prefix.(flag_post_released_result) = None /\
  (if flag_post_protected_schedule prefix.(flag_post_released_result) then
    flag_post_scheduler_relation environment critical sg prefix.(flag_post_released_execution) mask
      prefix.(flag_post_restored_state) context.(flag_post_scheduled_execution) context.(flag_post_scheduled_state)
   else context.(flag_post_scheduled_execution) = prefix.(flag_post_released_execution) /\
      context.(flag_post_scheduled_state) = prefix.(flag_post_restored_state)) /\
  flag_post_save_relation environment critical sg context.(flag_post_scheduled_execution) mask read_saved
    context.(flag_post_scheduled_state) context.(flag_post_reader) context.(flag_post_read_state) /\
  context.(flag_post_read_state).(FlagState).(flagImages) id = Some context.(flag_post_read_image) /\
  flag_post_current_valid sg context.(flag_post_reader) context.(flag_post_read_state).
Definition flag_post_read_cut environment critical sg pointer id requested option_word mask original before first_saved read_saved context : Assertion :=
  coq_prop (flag_post_read_facts environment critical sg pointer id requested option_word mask original before first_saved read_saved context) &&
  flag_post_source_masked environment critical context.(flag_post_read_local) sg context.(flag_post_reader) read_saved
    context.(flag_post_read_state) context.(flag_post_read_state).


Definition flag_post_helper_cut environment critical sg pointer id requested option_word mask original before
  saved context node ready waiter old : Assertion :=
  coq_prop (flag_post_loop_facts environment critical sg pointer id requested option_word mask original before saved context node
      (flag_post_schedule_word context.(flag_post_accumulator).(flag_post_scan_visits)) /\
    context.(flag_post_accumulator).(flag_post_scan_state).(FlagState).(flagWaitNodes) node = Some waiter /\
    flag_post_waiter_satisfied sg context waiter ready) &&
  (flag_task_rdy_fields_pre sg context.(flag_post_accumulator).(flag_post_scan_state) node waiter old ready **
   UCOS2_raw_rep_missing_task_storage_sched_flag sg context.(flag_post_accumulator).(flag_post_scan_state) **
   unmap_table_rep sg ** flag_post_critical_frame environment critical context.(flag_post_loop_local) sg
     context.(flag_post_loop_entry).(flag_post_entered) saved context.(flag_post_loop_entry).(flag_post_acquired)
     context.(flag_post_accumulator).(flag_post_scan_state)).

Definition flag_post_final_cut environment critical sg pointer id requested option_word mask original before
  first_saved read_saved context returned current local : Assertion :=
  coq_prop (flag_post_read_facts environment critical sg pointer id requested option_word mask original before first_saved read_saved context /\
    flag_post_restore_relation environment critical sg context.(flag_post_reader) context.(flag_post_read_state) returned current) &&
  flag_post_source_closed environment local sg returned mask current.

Definition flag_post_image_at state id image : Prop := state.(FlagState).(flagImages) id = Some image.
Definition flag_post_waiter_at state node waiter : Prop := state.(FlagState).(flagWaitNodes) node = Some waiter.
Definition flag_post_next_is pending next : Prop :=
  next = pending.(flag_post_pending_waiter).(flagWaitImage).(flagNodeNext).
Definition flag_post_result_error result error : Prop := flag_post_protected_error result = Some error.
Definition flag_post_result_success result schedule : Prop :=
  flag_post_protected_error result = None /\ schedule = if flag_post_protected_schedule result then 1 else 0.
Definition flag_post_success_result context schedule : Prop :=
  flag_post_result_success context.(flag_post_released_result) schedule.
Definition flag_post_group_head_frame sg state id image : Assertion :=
  flag_group_rep_without_head sg.(osKernelConfig) (flag_pool_addr sg id) image ** flag_post_group_frame sg state id.
Definition flag_post_scheduled_facts environment critical sg pointer id requested option_word mask original before
  saved prefix scheduled current : Prop :=
  flag_post_restored_facts environment critical sg pointer id requested option_word mask original before saved prefix /\
  flag_post_protected_error prefix.(flag_post_released_result) = None /\
  (if flag_post_protected_schedule prefix.(flag_post_released_result) then
    flag_post_scheduler_relation environment critical sg prefix.(flag_post_released_execution) mask
      prefix.(flag_post_restored_state) scheduled current
   else scheduled = prefix.(flag_post_released_execution) /\ current = prefix.(flag_post_restored_state)).
Definition flag_post_next_frame environment critical sg pointer id requested option_word mask original before
  saved pending node schedule : Assertion :=
  coq_prop (flag_post_loop_facts environment critical sg pointer id requested option_word mask original before saved
      pending.(flag_post_pending_loop) node
      (flag_post_schedule_word pending.(flag_post_pending_loop).(flag_post_accumulator).(flag_post_scan_visits)) /\
    flag_post_pending_facts sg pending node schedule /\
    flag_post_current_valid sg pending.(flag_post_pending_loop).(flag_post_loop_entry).(flag_post_entered)
      pending.(flag_post_pending_state)) &&
  (flag_node_fields_rep_without_next sg.(osKernelConfig) node pending.(flag_post_pending_waiter).(flagWaitImage) **
   flag_post_pending_world sg pending node **
   flag_post_critical_frame environment critical pending.(flag_post_pending_loop).(flag_post_loop_local) sg
     pending.(flag_post_pending_loop).(flag_post_loop_entry).(flag_post_entered) saved
     pending.(flag_post_pending_loop).(flag_post_loop_entry).(flag_post_acquired) pending.(flag_post_pending_state)).

Definition flag_post_protected_run sg id requested option_word acquired result released : Prop :=
  flag_post_protected_program sg id requested option_word acquired result released.

Definition flag_post_pointer_image state id pointer : Prop :=
  pointer <> 0 -> exists image, state.(FlagState).(flagImages) id = Some image.
Definition flag_post_initial_type_ok state id : Prop :=
  exists image, state.(FlagState).(flagImages) id = Some image /\ image.(flagImageType) = 5.

Definition flag_post_caller_frame error_cell old_error (frame : Assertion) : Assertion :=
  error_cell # UChar |-> old_error ** frame.
Definition flag_post_save_input environment (critical : CriticalRegionResources) local sg original mask before frame captured : Assertion :=
  flag_post_heap_cut (flag_post_paired_closed environment critical local sg original mask before ** frame) captured.
Definition flag_post_restore_input environment critical (mask : Z) local sg original saved acquired released frame captured : Assertion :=
  flag_post_heap_cut (flag_post_paired_masked environment critical local sg original saved acquired released ** frame) captured.


(** This is a source obligation, not an added public admission: the active
    caller's TCB must be clean at an actual API entry/return cut. ISR coverage
    has active=None, so the interrupted task remains eligible for self-wake. *)
Definition flag_post_active_node_clear execution state : Prop :=
  forall slot generation task,
    flag_post_execution_active execution = Some (slot, generation) ->
    state.(TskState).(inUsedTaskStates) slot = Some task ->
    task.(taskGeneration) = generation -> task.(tcbFlagNode) = 0.

Lemma flag_post_waiter_parked_from_coverage : forall sg execution state node waiter,
  task_flag_waiter_consistency sg state.(TskState) state.(FlagState) ->
  task_stack_live_coverage state.(TskState) (flag_post_execution_active execution) ->
  flag_post_active_node_clear execution state ->
  state.(FlagState).(flagWaitNodes) node = Some waiter ->
  exists region fragments,
    state.(TskState).(parkedTaskStacks) (waiter.(flagTask), waiter.(flagTaskGeneration)) =
      Some (region, fragments).
Proof.
  intros sg execution state node waiter [Hnodes _] Hcoverage Hclear Hnode.
  destruct (Hnodes node waiter Hnode) as [Hnonzero [task [Htask [Hg [Hptr Hrest]]]]].
  destruct (Hcoverage waiter.(flagTask) task Htask) as [Hactive|Hparked].
  - pose proof (Hclear waiter.(flagTask) task.(taskGeneration) task Hactive Htask eq_refl); congruence.
  - rewrite Hg in Hparked; exact Hparked.
Qed.

Lemma flag_post_handler_active_node_clear : forall handler state,
  flag_post_active_node_clear (FlagPostHandler handler) state.
Proof. intros handler state slot generation task Hactive; discriminate. Qed.


Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Lemma flag_post_same_execution_refl : forall execution,
  flag_post_same_execution execution execution.
Proof.
  intros [call|handler]; unfold flag_post_same_execution, task_tcb_init_stack_same_call;
    repeat split; reflexivity.
Qed.

Lemma flag_post_same_execution_trans : forall first middle last,
  flag_post_same_execution first middle -> flag_post_same_execution middle last ->
  flag_post_same_execution first last.
Proof.
  intros [first|first] [middle|middle] [last|last];
    unfold flag_post_same_execution, task_tcb_init_stack_same_call; intuition congruence.
Qed.

Lemma flag_post_scheduler_same_execution : forall environment critical sg original mask before returned current,
  flag_post_scheduler_relation environment critical sg original mask before returned current ->
  flag_post_same_execution original returned.
Proof.
  intros environment critical sg [call|handler] mask before [after|after] current Hhistory;
    cbn [flag_post_scheduler_relation flag_post_same_execution] in *; try contradiction.
  - eapply os_sched_continuation_call_history_same_call; exact Hhistory.
  - destruct Hhistory as [saved [entered [acquired [local [entered_local [next_local
      [first_heap [saved_heap [restore_heap [final_heap [Hsave Hrestore]]]]]]]]]]].
    destruct Hsave as [_ [Hfirst _]].
    destruct Hrestore as [_ [Hlast _]].
    exact (sched_fields_same_view_trans _ _ _ Hlast Hfirst).
Qed.

(** The precise public post is reached only after the last actual Restore.
    Its value is the image read under the second Save, while its state and
    dynamic local family are the Restore's actual returned endpoints. *)
Lemma flag_post_read_restore_public_post : forall environment critical sg pointer id requested option_word
  mask original before first_saved read_saved context returned current local error_cell (frame : Assertion) X,
  flag_post_read_facts environment critical sg pointer id requested option_word mask original before
    first_saved read_saved context ->
  flag_post_restore_relation environment critical sg context.(flag_post_reader)
    context.(flag_post_read_state) returned current ->
  flag_post_api_safe environment critical sg pointer id requested option_word mask original before X ->
  flag_post_source_closed environment local sg returned mask current ** error_cell # UChar |-> 0 ** frame |--
  flag_post_public_post environment sg original mask error_cell context.(flag_post_read_image).(flagImageBits) frame X.
Proof.
  intros environment critical sg pointer id requested option_word mask original before first_saved read_saved
    context returned current local error_cell frame X Hread Hlast Hsafe.
  destruct Hread as [Hrest [Herror [Hsched [Hsave2 [Himage Hreadvalid]]]]].
  destruct Hrest as [Hentry [Hprotected Hrestore1]].
  destruct Hentry as [[Hpointer [Hinitial [Htype Hsave1]]] Hentryvalid].
  assert (Hscheduled : flag_post_same_execution
    context.(flag_post_read_prefix).(flag_post_released_execution) context.(flag_post_scheduled_execution)).
  { destruct (flag_post_protected_schedule context.(flag_post_read_prefix).(flag_post_released_result)).
    - eapply flag_post_scheduler_same_execution; exact Hsched.
    - destruct Hsched as [Heq _]; rewrite Heq; apply flag_post_same_execution_refl. }
  assert (Hsame : flag_post_same_execution original returned).
  { eapply flag_post_same_execution_trans; [exact (proj1 (proj2 Hsave1))|].
    eapply flag_post_same_execution_trans; [exact (proj1 Hrestore1)|].
    eapply flag_post_same_execution_trans; [exact Hscheduled|].
    eapply flag_post_same_execution_trans; [exact (proj1 (proj2 Hsave2))|exact (proj1 Hlast)]. }
  assert (Hreturn : safeExec (eq current)
    (StateRelMonad.ret (flag_post_observation 0 context.(flag_post_read_image).(flagImageBits))) X).
  { eapply (flag_post_api_success_return environment critical sg pointer id requested option_word mask original before
      context.(flag_post_read_prefix).(flag_post_released_entry).(flag_post_initial_image) first_saved
      context.(flag_post_read_prefix).(flag_post_released_entry).(flag_post_entered)
      context.(flag_post_read_prefix).(flag_post_released_entry).(flag_post_acquired)
      context.(flag_post_read_prefix).(flag_post_released_result) context.(flag_post_read_prefix).(flag_post_released_state)
      context.(flag_post_read_prefix).(flag_post_released_execution) context.(flag_post_read_prefix).(flag_post_restored_state)
      context.(flag_post_scheduled_state) context.(flag_post_scheduled_execution) read_saved
      context.(flag_post_reader) context.(flag_post_read_state) context.(flag_post_read_image) returned current X);
      eassumption. }
  unfold flag_post_public_post; Exists returned current local 0; entailer!.
Qed.

Lemma flag_post_error_restore_public_post : forall environment critical sg pointer id requested option_word
  mask original before saved entry result released returned current local error error_cell (frame : Assertion) X,
  flag_post_protected_facts environment critical sg pointer id requested option_word mask original before saved entry ->
  flag_post_protected_program sg id requested option_word entry.(flag_post_acquired) result released ->
  flag_post_protected_error result = Some error ->
  flag_post_restore_relation environment critical sg entry.(flag_post_entered) released returned current ->
  flag_post_api_safe environment critical sg pointer id requested option_word mask original before X ->
  flag_post_source_closed environment local sg returned mask current ** error_cell # UChar |-> error ** frame |--
  flag_post_public_post environment sg original mask error_cell 0 frame X.
Proof.
  intros environment critical sg pointer id requested option_word mask original before saved entry result released
    returned current local error error_cell frame X [[Hp [Hi [Ht Hsave]]] Hvalid] Hrun Herror Hrestore Hsafe.
  assert (Hsame : flag_post_same_execution original returned).
  { eapply flag_post_same_execution_trans; [exact (proj1 (proj2 Hsave))|exact (proj1 Hrestore)]. }
  assert (Hreturn : safeExec (eq current) (StateRelMonad.ret (flag_post_observation error 0)) X).
  { eapply flag_post_api_protected_return; eassumption. }
  unfold flag_post_public_post; Exists returned current local error; entailer!.
Qed.


(** The active assertion owns no C bytes. Its pure observation is produced
    at a real entry/return cut; only the Scheduler's actual prefix stability
    is required. It is not an assumption about arbitrary Task/Flag updates. *)
Definition flag_post_scheduler_active (call : OsSchedCallContext) state : Assertion :=
  coq_prop (flag_api_task_entry_observation call state) && emp.

Lemma flag_post_scheduler_active_stable : os_sched_active_local_stable flag_post_scheduler_active.
Proof.
  intros call state; unfold flag_post_scheduler_active, flag_api_task_entry_observation,
    kernel_call_task_source, task_execution_current, os_sched_prefix_state.
  cbn [replace_SchedS TskState SchedState].
  rewrite (proj1 (os_sched_ready_checkpoint_frame state)),
    (proj1 (proj2 (os_sched_ready_checkpoint_frame state))).
  split; entailer!.
Qed.

Definition flag_post_scheduler_call_pre environment critical local sg execution mask state : Assertion :=
  match execution with
  | FlagPostTask call => os_sched_active_call_pre environment local
      flag_post_scheduler_active sg call mask state
  | FlagPostHandler handler => coq_prop (sched_disabled_isr_source handler state) &&
      sched_fields_disabled_pre environment critical local sg handler mask state emp
  end.
Definition flag_post_scheduler_call_post environment critical local sg execution mask state : Assertion :=
  match execution with
  | FlagPostTask call => os_sched_active_history_return_post environment critical
      flag_post_scheduler_active sg call mask state
  | FlagPostHandler handler => coq_prop (sched_disabled_isr_source handler state) &&
      sched_fields_disabled_post environment critical sg handler mask state local emp
  end.

Lemma flag_post_scheduler_task_pre_eq : forall environment critical local sg call mask state,
  flag_post_scheduler_call_pre environment critical local sg (FlagPostTask call) mask state =
  os_sched_active_call_pre environment local flag_post_scheduler_active sg call mask state.
Proof. reflexivity. Qed.
Lemma flag_post_scheduler_task_post_eq : forall environment critical local sg call mask state,
  flag_post_scheduler_call_post environment critical local sg (FlagPostTask call) mask state =
  os_sched_active_history_return_post environment critical flag_post_scheduler_active sg call mask state.
Proof. reflexivity. Qed.
Lemma flag_post_scheduler_handler_pre_eq : forall environment critical local sg handler mask state,
  flag_post_scheduler_call_pre environment critical local sg (FlagPostHandler handler) mask state =
  coq_prop (sched_disabled_isr_source handler state) &&
  sched_fields_disabled_pre environment critical local sg handler mask state emp.
Proof. reflexivity. Qed.
Lemma flag_post_scheduler_handler_post_eq : forall environment critical local sg handler mask state,
  flag_post_scheduler_call_post environment critical local sg (FlagPostHandler handler) mask state =
  coq_prop (sched_disabled_isr_source handler state) &&
  sched_fields_disabled_post environment critical sg handler mask state local emp.
Proof. reflexivity. Qed.

Definition flag_post_handler_with_fragments (handler : OsIntExitCallContext)
  (fragments : TaskStackFragments) : OsIntExitCallContext :=
  {| os_int_exit_invocation := handler.(os_int_exit_invocation);
     os_int_exit_origin := handler.(os_int_exit_origin);
     os_int_exit_handler_stack := handler.(os_int_exit_handler_stack);
     os_int_exit_handler_fragments := fragments;
     os_int_exit_interrupted_stack := handler.(os_int_exit_interrupted_stack);
     os_int_exit_interrupted_sp := handler.(os_int_exit_interrupted_sp);
     os_int_exit_interrupted_fragments := handler.(os_int_exit_interrupted_fragments);
     os_int_exit_interrupted_call := handler.(os_int_exit_interrupted_call);
     os_int_exit_interrupted_pc := handler.(os_int_exit_interrupted_pc);
     os_int_exit_interrupted_mask := handler.(os_int_exit_interrupted_mask) |}.

Lemma flag_post_handler_returned_view : forall handler returned,
  sched_fields_same_view returned (os_int_exit_execution_view handler) ->
  os_int_exit_execution_view (flag_post_handler_with_fragments handler returned.(os_execution_fragments)) = returned.
Proof.
  intros handler [invocation origin context stack fragments] [Hi [Ho [Hc Hs]]].
  cbn in Hi, Ho, Hc, Hs; subst invocation origin context stack; reflexivity.
Qed.

Lemma flag_post_task_active_closed : forall environment local sg call mask state,
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg (task_stack_call_active_key call) call mask state **
    flag_post_scheduler_active call state |--
  flag_post_source_closed environment local sg (FlagPostTask call) mask state.
Proof.
  intros environment local sg call mask state; unfold flag_post_scheduler_active; Intros.
  assert (Horigin : call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration))
    by exact (proj1 (proj1 H)).
  unfold flag_post_source_closed, flag_post_source_observation; rewrite Horigin.
  rewrite flag_post_task_closed_eq; entailer!.
Qed.

Lemma flag_post_scheduler_call_post_resources : forall environment critical local sg execution mask state,
  flag_post_scheduler_call_post environment critical local sg execution mask state |--
  EX returned current next_local,
    coq_prop (flag_post_scheduler_relation environment critical sg execution mask state returned current) &&
    flag_post_source_closed environment next_local sg returned mask current.
Proof.
  intros environment critical local sg [call|handler] mask state.
  - unfold flag_post_scheduler_call_post, os_sched_active_history_return_post.
    Intros returned current next_local.
    sep_apply_l_atomic (flag_post_task_active_closed environment next_local sg returned mask current).
    Exists (FlagPostTask returned) current next_local.
    unfold flag_post_scheduler_relation; entailer!.
  - intros heap [Hinitial_isr Hpost].
    pose proof Hpost as (saved & entered & acquired & entered_local & first_heap & saved_heap &
      restore_heap & Hsave & returned_view & current & next_local & Hrestore).
    pose proof Hsave as [_ [Hfirst _]].
    pose proof Hrestore as [_ [Hlast [_ Howned]]].
    pose proof (sched_fields_same_view_trans _ _ _ Hlast Hfirst) as Hsame.
    exists (FlagPostHandler returned_view), current, next_local; split.
    + unfold flag_post_scheduler_relation.
      exists saved, entered, acquired, local, entered_local, next_local,
        first_heap, saved_heap, restore_heap, heap.
      split; [exact Hsave|exact Hrestore].
    + unfold flag_post_source_closed; split.
      * cbn [flag_post_source_observation].
        pose proof Hsave as [Hsave_interval [_ [_ [[[Hclients [Hfirst_source Hfirst_valid]] Hpre] Hafter]]]].
        pose proof Hrestore as [Hrestore_interval [_ [[[Hlast_clients [Hlast_source [Hlast_valid Hsaved]]] Hrestore_pre] Hrestore_after]]].
        destruct (sched_disabled_interval_preserves_context critical sg handler
          handler.(os_execution_invocation) state acquired Hclients Hfirst_valid Hsave_interval)
          as [_ [Hacquired_isr _]].
        assert (Hentered_isr : sched_disabled_isr_source entered acquired).
        { unfold sched_disabled_isr_source in *.
          destruct Hfirst as [Hi [Ho [Hcontext Hstack]]].
          rewrite Hcontext; exact (Hacquired_isr Hinitial_isr). }
        destruct (sched_disabled_interval_preserves_context critical sg entered
          entered.(os_execution_invocation) acquired current Hlast_clients Hlast_valid Hrestore_interval)
          as [_ [Hcurrent_isr _]].
        assert (Hreturned_isr : sched_disabled_isr_source returned_view current).
        { unfold sched_disabled_isr_source in *.
          destruct Hlast as [Hi [Ho [Hcontext Hstack]]].
          rewrite Hcontext; exact (Hcurrent_isr Hentered_isr). }
        destruct Hreturned_isr as [invocation [interrupted [Hcontext [Hrunning Hnesting]]]].
        rewrite Hrunning; exists invocation, interrupted; auto.
      * unfold flag_post_closed; cbn [flag_post_execution_view flag_post_execution_active].

      unfold sched_fields_disabled_closed in Howned.
      assert (Hclose : kernel_execution_view_owned environment.(task_stack_call_external)
        environment.(task_stack_call_platform) returned_view mask **
        kernel_continuation_inv environment.(task_stack_call_continuations)
          kernel_program_fields_inv next_local sg None current ** emp |--
        kernel_execution_view_owned environment.(task_stack_call_external)
          environment.(task_stack_call_platform) returned_view mask **
        kernel_continuation_inv environment.(task_stack_call_continuations)
          kernel_program_fields_inv next_local sg None current) by entailer!.
      exact (Hclose heap Howned).
Qed.


Lemma flag_post_source_active_node_clear : forall execution state,
  flag_post_source_observation execution state ->
  flag_post_active_node_clear execution state.
Proof.
  intros [call|handler] state Hsource.
  - unfold flag_post_source_observation in Hsource.
    unfold flag_post_active_node_clear, flag_post_execution_active, task_stack_call_active_key.
    destruct call.(os_sched_call_origin) as [|slot generation] eqn:Horigin.
    + intros; discriminate.
    + destruct Hsource as [Hcall [[clean [Hclean [Hg Hzero]]] Hrest]].
      intros other version node Hkey Hnode Hversion.
      inversion Hkey; subst other version.
      unfold kernel_call_task_source in Hcall; destruct Hcall as [Hsame _].
      rewrite Horigin in Hsame; injection Hsame as Hslot Hgeneration.
      rewrite <- Hslot, Hnode in Hclean; inversion Hclean; subst clean; exact Hzero.
  - apply flag_post_handler_active_node_clear.
Qed.

Lemma flag_post_no_waiters_used_head_zero : forall sg state id group image,
  valid_flag_state sg state.(FlagState) ->
  flag_state_has_no_waiters state.(FlagState) ->
  state.(FlagState).(flagUsed) id = Some group ->
  state.(FlagState).(flagImages) id = Some image ->
  image.(flagImageHead) = 0.
Proof.
  intros sg state id group image [_ [_ [_ [Hused _]]]] [Hempty _] Hgroup Himage.
  destruct (Hused id group Hgroup) as [_ [_ [_ [other [Hother [_ [Hhead _]]]]]]].
  rewrite Himage in Hother; inversion Hother; subst other.
  rewrite (Hempty id group Hgroup) in Hhead; exact Hhead.
Qed.

Lemma flag_post_task_rdy_running_eq : forall sg before node bits result scheduled after,
  flag_task_rdy sg before node bits result = Some (scheduled, after) ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg before node bits result scheduled after Hrun.
  destruct (flag_task_rdy_result _ _ _ _ _ _ _ Hrun)
    as [waiter [flags [old [_ [_ [-> _]]]]]].
  unfold flag_wake_state; cbn [replace_FlagS replace_SchedS replace_TskS SchedState].
  unfold sched_wake_task.
  destruct (is_effectively_ready (task_flag_wake old bits result).(stat)
    (task_flag_wake old bits result).(dly)); reflexivity.
Qed.

Lemma flag_post_scan_step_running_eq : forall sg word scan node next,
  flag_post_scan_step sg word (Some scan) node = Some next ->
  next.(flag_post_scan_state).(SchedState).(isRunning) =
    scan.(flag_post_scan_state).(SchedState).(isRunning).
Proof.
  intros sg word scan node next Hstep.
  unfold flag_post_scan_step in Hstep.
  destruct scan.(flag_post_scan_error); [inversion Hstep; reflexivity|].
  destruct (flagWaitNodes (FlagState (flag_post_scan_state scan)) node) as [waiter|]; [|discriminate].
  destruct (flag_post_node_test (osKernelConfig sg) word
    (flagNodeMask (flagWaitImage waiter)) (flagNodeMode (flagWaitImage waiter))) as [[ready test]|];
    [destruct test|]; try (inversion Hstep; reflexivity).
  destruct (flag_task_rdy sg (flag_post_scan_state scan) node ready PendOK) as [[returned after]|] eqn:Hcall;
    [|discriminate].
  inversion Hstep; subst next; cbn.
  eapply flag_post_task_rdy_running_eq; exact Hcall.
Qed.

Lemma flag_post_scan_fold_running_eq : forall sg word nodes scan next,
  fold_left (flag_post_scan_step sg word) nodes (Some scan) = Some next ->
  next.(flag_post_scan_state).(SchedState).(isRunning) =
    scan.(flag_post_scan_state).(SchedState).(isRunning).
Proof.
  intros sg word nodes; induction nodes as [|node rest IH]; intros scan next Hrun.
  - inversion Hrun; reflexivity.
  - change (fold_left (flag_post_scan_step sg word) rest
      (flag_post_scan_step sg word (Some scan) node) = Some next) in Hrun.
    destruct (flag_post_scan_step sg word (Some scan) node) as [middle|] eqn:Hstep.
    + rewrite (IH middle next Hrun); eapply flag_post_scan_step_running_eq; exact Hstep.
    + assert (Hnone : forall tail, fold_left (flag_post_scan_step sg word) tail None = None).
      { intro tail; induction tail; cbn; auto. }
      rewrite Hnone in Hrun; discriminate.
Qed.

Lemma flag_post_protected_running_eq : forall sg id requested option_word before result after,
  flag_post_protected_program sg id requested option_word before result after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg id requested option_word before result after [image [Himage Hrun]].
  destruct (flag_post_valid_option option_word && negb (Z.eqb image.(flagImageType) 5))%bool.
  - destruct Hrun as [_ ->]; reflexivity.
  - destruct (flag_post_bits sg.(osKernelConfig) image.(flagImageBits) requested option_word).
    + destruct Hrun as [group [scan [Hgroup [Hscan [_ ->]]]]].
      apply flag_post_scan_fold_running_eq in Hscan; exact Hscan.
    + destruct Hrun as [_ ->]; reflexivity.
Qed.

Lemma flag_post_protected_no_waiters_schedule : forall sg id requested option_word before result after,
  flag_state_has_no_waiters before.(FlagState) ->
  flag_post_protected_program sg id requested option_word before result after ->
  flag_post_protected_schedule result = false.
Proof.
  intros sg id requested option_word before result after [Hempty Hnodes] [image [Himage Hrun]].
  destruct (flag_post_valid_option option_word && negb (Z.eqb image.(flagImageType) 5))%bool.
  - destruct Hrun as [-> _]; reflexivity.
  - destruct (flag_post_bits sg.(osKernelConfig) image.(flagImageBits) requested option_word).
    + destruct Hrun as [group [scan [Hgroup [Hscan [Hresult Hafter]]]]].
      rewrite (Hempty id group Hgroup) in Hscan.
      unfold flag_post_scan in Hscan; cbn in Hscan; injection Hscan as Hscan; subst scan.
      subst result; reflexivity.
    + destruct Hrun as [-> _]; reflexivity.
Qed.

Lemma flag_post_execution_clients_same : forall critical first last,
  flag_post_same_execution first last ->
  flag_post_execution_clients critical first -> flag_post_execution_clients critical last.
Proof.
  intros critical [first|first] [last|last] Hsame Hclients;
    cbn [flag_post_same_execution flag_post_execution_clients] in *; try contradiction.
  - unfold task_tcb_init_stack_same_call in Hsame; destruct Hsame as [Hi [Ho Hstack]].
    rewrite Ho; exact Hclients.
  - destruct Hsame as [Hi [Ho [Hcontext Hstack]]].
    destruct Hclients as [Hdisabled Hboot]; split.
    + unfold sched_disabled_completed_clients, sched_disabled_context_rely, sched_disabled_isr_source in *.
      rewrite Hcontext; exact Hdisabled.
    + rewrite Ho; exact Hboot.
Qed.

Lemma flag_post_task_observation_call_cut : forall sg call state,
  kernel_tcb_stack_field_layout sg ->
  UCOS2_state_inv sg state -> flag_api_task_entry_observation call state ->
  os_sched_call_cut sg call state.
Proof.
  intros sg call state Hlayout Hvalid [Hsource [Hclean [Hnone Hready]]].
  eapply os_sched_call_cut_from_source; [exact Hvalid|exact Hsource|exact Hready| |].
  - unfold kernel_call_stack_available; rewrite (proj1 Hsource); exact Hnone.
  - eapply kernel_call_task_source_stack_field_address; eassumption.
Qed.


Lemma flag_post_save_input_capture : forall environment critical local sg execution mask state frame,
  flag_post_source_closed environment local sg execution mask state ** frame |--
  EX captured, flag_post_save_input environment critical local sg execution mask state frame captured.
Proof.
  intros; unfold flag_post_save_input.
  rewrite <- (flag_post_paired_closed_resources environment critical local sg execution mask state).
  apply flag_post_heap_capture.
Qed.

(** The historical owned heap yields only a pure validity/range fact.
    Every resource in the resulting cut is obtained from the actual after heap. *)
Lemma flag_post_save_output_protected_cut : forall environment critical local sg original mask before
  frame captured saved pointer id requested option_word,
  flag_post_parameters sg pointer id requested option_word ->
  pointer <> 0 -> flag_post_initial_type_ok before id ->
  flag_post_save_output environment critical sg original mask before local frame captured saved |--
  EX context, flag_post_protected_cut environment critical sg pointer id requested option_word
    mask original before saved context ** frame.
Proof.
  intros environment critical local sg original mask before frame captured saved pointer id requested option_word
    Hparameters Hpointer [image [Himage Htype]] heap
    [returned [acquired [next_local [Hsave [Hbefore Hafter]]]]].
  assert (Hbefore_valid : UCOS2_state_inv sg before).
  { assert (Hextract :
      flag_post_paired_closed environment critical local sg original mask before ** frame |--
      coq_prop (UCOS2_state_inv sg before)).
    { rewrite flag_post_paired_closed_resources.
      unfold flag_post_source_closed, flag_post_closed, kernel_continuation_inv,
        kernel_program_fields_inv; Intros; entailer!. }
    exact (Hextract captured Hbefore). }
  pose proof Hparameters as [Hconfiguration _].
  destruct Hbefore_valid as [_ [_ [_ [_ [_ [_ [_ [Hflags _]]]]]]]].
  unfold valid_flag_configuration in Hflags.
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true)
    by (rewrite Hconfiguration; reflexivity).
  rewrite Henabled in Hflags.
  destruct Hflags as [_ [Hdomain _]].
  pose proof (proj1 (Hdomain id) (ex_intro _ image Himage)) as Hrange.
  set (context := {| flag_post_initial_image := image;
    flag_post_entered := returned; flag_post_acquired := acquired;
    flag_post_local := next_local |}).
  exists context.
  assert (Hbuild :
    flag_post_paired_masked environment critical next_local sg returned saved acquired acquired ** frame |--
    flag_post_protected_cut environment critical sg pointer id requested option_word
      mask original before saved context ** frame).
  { rewrite flag_post_paired_masked_resources.
    unfold flag_post_protected_cut, flag_post_protected_facts, flag_post_prefix,
      flag_post_current_valid, context; cbn [flag_post_initial_image flag_post_entered
        flag_post_acquired flag_post_local].
    unfold flag_post_source_masked, flag_post_masked, kernel_continuation_inv,
      kernel_program_fields_inv; Intros; entailer!. }
  exact (Hbuild heap Hafter).
Qed.

Lemma flag_post_restore_input_capture : forall environment critical local sg execution mask saved acquired state frame,
  flag_post_source_masked environment critical local sg execution saved acquired state ** frame |--
  EX captured, flag_post_restore_input environment critical mask local sg execution saved acquired state frame captured.
Proof.
  intros; unfold flag_post_restore_input.
  rewrite <- (flag_post_paired_masked_resources environment critical local sg execution saved acquired state).
  apply flag_post_heap_capture.
Qed.

(** The Boot endpoint observation is derived on the actual acquired state.
    No Scheduler task-source cut is part of this Save interface. *)
Lemma flag_post_boot_save_event : forall environment critical sg call returned mask saved
  before acquired local next_local frame first last,
  call.(os_sched_call_origin) = BootInvocation ->
  flag_post_boot_clients critical ->
  UCOS2_state_inv sg before -> flag_state_has_no_waiters before.(FlagState) ->
  flag_post_save_relation environment critical sg (FlagPostTask call) mask saved before
    (FlagPostTask returned) acquired ->
  (flag_post_paired_closed environment critical local sg (FlagPostTask call) mask before ** frame) first ->
  (flag_post_masked environment critical next_local sg (FlagPostTask returned) saved acquired acquired ** frame) last ->
  flag_post_save_event environment critical sg (FlagPostTask call) (FlagPostTask returned)
    mask saved before acquired local next_local frame first last.
Proof.
  intros environment critical sg call returned mask saved before acquired local next_local frame first last
    Hboot Hclients Hvalid Hnone Hrelation Hpre Hpost.
  pose proof Hrelation as [Hsaved [Hsame [Hcontrol [Heffect [Hinterval Hrest]]]]].
  cbn [flag_post_same_execution] in Hsame.
  assert (Hreturned : returned.(os_sched_call_origin) = BootInvocation)
    by (rewrite (proj1 (proj2 Hsame)); exact Hboot).
  rewrite Hboot in Hinterval.
  pose proof (flag_post_boot_interval_no_waiters critical sg call.(os_sched_call_invocation)
    before acquired Hclients Hinterval Hvalid Hnone) as Hacquired.
  split; [exact Hrelation|]. split; [exact Hpre|].
  assert (Hclose : flag_post_masked environment critical next_local sg (FlagPostTask returned) saved acquired acquired ** frame |--
    flag_post_paired_masked environment critical next_local sg (FlagPostTask returned) saved acquired acquired ** frame).
  { rewrite flag_post_paired_masked_resources.
    unfold flag_post_source_masked, flag_post_source_observation; rewrite Hreturned; entailer!. }
  exact (Hclose last Hpost).
Qed.

Lemma flag_post_boot_restore_event : forall environment critical sg call returned mask saved
  acquired released current local next_local frame first last,
  call.(os_sched_call_origin) = BootInvocation ->
  flag_post_boot_clients critical ->
  UCOS2_state_inv sg released -> flag_state_has_no_waiters released.(FlagState) ->
  interrupt_saved_value mask saved ->
  flag_post_restore_relation environment critical sg (FlagPostTask call) released (FlagPostTask returned) current ->
  (flag_post_paired_masked environment critical local sg (FlagPostTask call) saved acquired released ** frame) first ->
  (flag_post_closed environment next_local sg (FlagPostTask returned) mask current ** frame) last ->
  flag_post_restore_event environment critical sg (FlagPostTask call) (FlagPostTask returned)
    mask saved acquired released current local next_local frame first last.
Proof.
  intros environment critical sg call returned mask saved acquired released current local next_local frame first last
    Hboot Hclients Hvalid Hnone Hsaved Hrelation Hpre Hpost.
  pose proof Hrelation as [Hsame [Hcontrol [Heffect [Hinterval Hrest]]]].
  cbn [flag_post_same_execution] in Hsame.
  assert (Hreturned : returned.(os_sched_call_origin) = BootInvocation)
    by (rewrite (proj1 (proj2 Hsame)); exact Hboot).
  rewrite Hboot in Hinterval.
  pose proof (flag_post_boot_interval_no_waiters critical sg call.(os_sched_call_invocation)
    released current Hclients Hinterval Hvalid Hnone) as Hcurrent.
  split; [exact Hsaved|]. split; [exact Hrelation|]. split; [exact Hpre|].
  assert (Hclose : flag_post_closed environment next_local sg (FlagPostTask returned) mask current ** frame |--
    flag_post_paired_closed environment critical next_local sg (FlagPostTask returned) mask current ** frame).
  { rewrite flag_post_paired_closed_resources.
    unfold flag_post_source_closed, flag_post_source_observation; rewrite Hreturned; entailer!. }
  exact (Hclose last Hpost).
Qed.

Lemma flag_post_restored_task_schedule_running : forall environment critical sg pointer id requested option_word
  mask original before saved context call,
  flag_post_restored_facts environment critical sg pointer id requested option_word mask original before saved context ->
  flag_post_success_result context 1 ->
  context.(flag_post_released_execution) = FlagPostTask call ->
  call.(os_sched_call_origin) <> BootInvocation.
Proof.
  intros environment critical sg pointer id requested option_word mask original before saved context call
    [Hentry [Hrun Hrestore]] Hsuccess Hexecution Hboot.
  destruct Hentry as [Hprefix [Hvalid [Hcoverage Hsource]]].
  destruct Hrestore as [Hsame Hrest].
  rewrite Hexecution in Hsame.
  destruct context.(flag_post_released_entry).(flag_post_entered) as [entered|handler] eqn:Hentered;
    cbn [flag_post_same_execution] in Hsame; [|contradiction].
  unfold flag_post_source_observation in Hsource.
  rewrite <- (proj1 (proj2 Hsame)), Hboot in Hsource.
  pose proof (flag_post_protected_no_waiters_schedule sg id requested option_word
    context.(flag_post_released_entry).(flag_post_acquired) context.(flag_post_released_result)
    context.(flag_post_released_state) Hsource Hrun) as Hschedule.
  destruct Hsuccess as [_ Hword]; rewrite Hschedule in Hword; discriminate.
Qed.

Lemma flag_post_restored_handler_schedule_running : forall environment critical sg pointer id requested option_word
  mask original before saved context handler,
  flag_post_restored_facts environment critical sg pointer id requested option_word mask original before saved context ->
  flag_post_success_result context 1 ->
  context.(flag_post_released_execution) = FlagPostHandler handler ->
  context.(flag_post_restored_state).(SchedState).(isRunning) = true.
Proof.
  intros environment critical sg pointer id requested option_word mask original before saved context handler
    [Hentry [Hrun Hrestore]] Hsuccess Hexecution.
  destruct Hentry as [Hprefix [Hvalid [Hcoverage Hsource]]].
  destruct Hrestore as [Hsame [Hcontrol Hrest]].
  rewrite Hexecution in Hsame.
  destruct context.(flag_post_released_entry).(flag_post_entered) as [call|entered] eqn:Hentered;
    cbn [flag_post_same_execution] in Hsame; [contradiction|].
  unfold kernel_call_control_rely in Hcontrol.
  rewrite (proj1 Hcontrol), (flag_post_protected_running_eq _ _ _ _ _ _ _ Hrun).
  destruct context.(flag_post_released_entry).(flag_post_acquired).(SchedState).(isRunning) eqn:Hrunning;
    [reflexivity|].
  cbn [flag_post_source_observation] in Hsource; rewrite Hrunning in Hsource.
  pose proof (flag_post_protected_no_waiters_schedule _ _ _ _ _ _ _ Hsource Hrun) as Hschedule.
  destruct Hsuccess as [_ Hword]; rewrite Hschedule in Hword; discriminate.
Qed.

Lemma flag_post_task_scheduler_source_pre : forall environment critical local sg call mask state,
  kernel_tcb_stack_field_layout sg -> call.(os_sched_call_origin) <> BootInvocation ->
  flag_post_source_closed environment local sg (FlagPostTask call) mask state |--
  flag_post_scheduler_call_pre environment critical local sg (FlagPostTask call) mask state.
Proof.
  intros environment critical local sg call mask state Hlayout Hrunning.
  unfold flag_post_source_closed, flag_post_source_observation.
  destruct call.(os_sched_call_origin) as [|slot generation] eqn:Horigin; [contradiction|].
  Intros.
  assert (Hvalid_resources : flag_post_closed environment local sg (FlagPostTask call) mask state |--
    coq_prop (UCOS2_state_inv sg state) && flag_post_closed environment local sg (FlagPostTask call) mask state).
  { unfold flag_post_closed, kernel_continuation_inv, kernel_program_fields_inv; entailer!. }
  sep_apply_l_atomic Hvalid_resources; Intros.
  assert (Hcut : os_sched_call_cut sg call state)
    by (eapply flag_post_task_observation_call_cut; eassumption).
  unfold flag_post_scheduler_call_pre, os_sched_active_call_pre, flag_post_scheduler_active.
  rewrite flag_post_task_closed_eq; entailer!.
  apply flag_post_scheduler_active_stable.
Qed.

Lemma flag_post_handler_scheduler_source_pre : forall environment critical local sg handler mask state,
  state.(SchedState).(isRunning) = true ->
  flag_post_execution_clients critical (FlagPostHandler handler) ->
  flag_post_source_closed environment local sg (FlagPostHandler handler) mask state |--
  flag_post_scheduler_call_pre environment critical local sg (FlagPostHandler handler) mask state.
Proof.
  intros environment critical local sg handler mask state Hrunning [Hclients Hboot_clients].
  unfold flag_post_scheduler_call_pre, sched_fields_disabled_pre, flag_post_source_closed,
    flag_post_source_observation, sched_fields_disabled_closed, flag_post_closed,
    kernel_continuation_inv, kernel_program_fields_inv; cbn; rewrite Hrunning; Intros.
  entailer!; unfold sched_disabled_entry_source; auto.
Qed.

Lemma flag_post_restored_scheduler_pre : forall environment critical sg pointer id requested option_word
  mask original before saved context,
  flag_post_parameters sg pointer id requested option_word ->
  flag_post_execution_clients critical original ->
  flag_post_success_result context 1 ->
  flag_post_restored_cut environment critical sg pointer id requested option_word mask original before saved context |--
  coq_prop (flag_post_restored_facts environment critical sg pointer id requested option_word mask original before saved context) &&
  flag_post_scheduler_call_pre environment critical context.(flag_post_restored_local) sg
    context.(flag_post_released_execution) mask context.(flag_post_restored_state).
Proof.
  intros environment critical sg pointer id requested option_word mask original before saved context
    Hparameters Hclients Hsuccess.
  unfold flag_post_restored_cut; Intros.
  assert (Hsame : flag_post_same_execution original context.(flag_post_released_execution)).
  { destruct H as [[[_ [_ [_ Hsave]]] Hvalid] [Hrun Hrestore]].
    eapply flag_post_same_execution_trans; [exact (proj1 (proj2 Hsave))|exact (proj1 Hrestore)]. }
  pose proof (flag_post_execution_clients_same critical original context.(flag_post_released_execution)
    Hsame Hclients) as Hreturned_clients.
  destruct context.(flag_post_released_execution) as [call|handler] eqn:Hexecution.
  - assert (Hrunning : call.(os_sched_call_origin) <> BootInvocation).
    { eapply flag_post_restored_task_schedule_running; eassumption. }
    assert (Hlayout : kernel_tcb_stack_field_layout sg) by (unfold flag_post_parameters in Hparameters; tauto).
    sep_apply_l_atomic (flag_post_task_scheduler_source_pre environment critical
      context.(flag_post_restored_local) sg call mask context.(flag_post_restored_state) Hlayout Hrunning).
    entailer!.
  - assert (Hrunning : context.(flag_post_restored_state).(SchedState).(isRunning) = true).
    { eapply flag_post_restored_handler_schedule_running; eassumption. }
    sep_apply_l_atomic (flag_post_handler_scheduler_source_pre environment critical
      context.(flag_post_restored_local) sg handler mask context.(flag_post_restored_state) Hrunning Hreturned_clients).
    entailer!.
Qed.

Lemma flag_replace_bits_preserves_no_waiters__word_update_first :
  forall flags id group image bits,
  flagUsed flags id = Some group ->
  flag_api_entry_source_spec.flag_state_has_no_waiters flags ->
  flag_api_entry_source_spec.flag_state_has_no_waiters
    (flag_replace_bits flags id group image bits).
Proof.
  intros flags id group image bits Hgroup [Hgroups Hnodes].
  split; [|exact Hnodes].
  intros other current Hcurrent.
  cbn [flag_replace_bits flagUsed] in Hcurrent.
  unfold kernel_resources.kernel_map_set in Hcurrent.
  destruct (Z.eq_dec other id) as [->|Hother].
  - inversion Hcurrent; subst current; cbn [flag_group_set_bits flagWaitOrder].
    exact (Hgroups id group Hgroup).
  - exact (Hgroups other current Hcurrent).
Qed.
Lemma flag_replace_bits_preserves_kernel_inv__word_update_first :
  forall sg state id group image bits,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg state ->
  state.(FlagState).(flagUsed) id = Some group ->
  state.(FlagState).(flagImages) id = Some image ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  UCOS2_state_inv sg
    (replace_FlagS (flag_replace_bits state.(FlagState) id group image bits) state).
Proof.
  intros sg state id group image bits Hcfg Hvalid Hgroup Himage Hbits.
  destruct Hvalid as [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle
    [Hreserved [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames
    [Hreferences [Hparked Hmutex]]]]]]]]]]]]]]].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true)
    by (rewrite Hcfg; reflexivity).
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready.
  split; [exact Hprofile|]. split; [exact Htasks|].
  split; [exact Hsched|]. split; [exact Hevents|].
  split; [apply cross_module_invariants.cross_module_consistency_flag_nodes_frame;
    [reflexivity|exact Hcross]|].
  split; [exact Hidle|]. split; [exact Hreserved|].
  split.
  - unfold valid_flag_configuration in Hflags |- *; rewrite Henabled in Hflags |- *.
    apply flag_replace_bits_preserves_validity; assumption.
  - split; [exact Hmemory|]. split; [exact Htimer|].
    split; [exact Hstats|]. split; [exact Hcontrol|].
    split; [exact Hnames|]. split.
    + apply kernel_names.kernel_names_valid_replace_flag; [exact Hreferences|].
      intros name [other [current [Hcurrent Hname]]].
      cbn [flag_replace_bits flagUsed] in Hcurrent.
      unfold kernel_resources.kernel_map_set in Hcurrent.
      destruct (Z.eq_dec other id) as [->|Hother].
      * inversion Hcurrent; subst current.
        exists id, group; split; [exact Hgroup|exact Hname].
      * exists other, current; auto.
    + split; [exact Hparked|exact Hmutex].
Qed.
Lemma flag_replace_bits_preserves_current_valid__word_update_first :
  forall sg execution state id group image bits,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_post_current_valid sg execution state ->
  state.(FlagState).(flagUsed) id = Some group ->
  state.(FlagState).(flagImages) id = Some image ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  flag_post_current_valid sg execution
    (replace_FlagS (flag_replace_bits state.(FlagState) id group image bits) state).
Proof.
  intros sg execution state id group image bits Hcfg [Hvalid [Hcoverage Hsource]]
    Hgroup Himage Hbits.
  split.
  - apply flag_replace_bits_preserves_kernel_inv__word_update_first; assumption.
  - split; [exact Hcoverage|].
    destruct execution as [call|handler]; cbn [flag_post_source_observation] in Hsource |- *.
    + destruct (sched_spec.os_sched_call_origin call).
      * apply flag_replace_bits_preserves_no_waiters__word_update_first; assumption.
      * exact Hsource.
    + cbn [replace_FlagS SchedState].
      destruct (SchedStateDef.isRunning (SchedState state)).
      * exact Hsource.
      * apply flag_replace_bits_preserves_no_waiters__word_update_first; assumption.
Qed.
Lemma flag_post_clear_word_16__word_update_first : forall bits requested,
  flag_post_bits selected_kernel_configuration bits requested 0 =
  Some (Z.land bits (unsigned_last_nbits (Z.lnot requested) 16)).
Proof.
  intros; unfold flag_post_bits, flag_word, unsigned_last_nbits.
  cbn [Z.eqb selected_kernel_configuration cfgFlagBits].
  rewrite <- (Z.land_ones (Z.lnot requested) 16) by lia.
  rewrite Z.land_assoc, Z.land_ones by lia; reflexivity.
Qed.
Lemma flag_post_set_word_16__word_update_first : forall bits requested,
  flag_post_bits selected_kernel_configuration bits requested 1 =
  Some (Z.lor (unsigned_last_nbits bits 16) (unsigned_last_nbits requested 16)).
Proof.
  intros; unfold flag_post_bits, flag_word, unsigned_last_nbits.
  cbn [Z.eqb Pos.eqb selected_kernel_configuration cfgFlagBits].
  rewrite <- (Z.land_ones bits 16) by lia.
  rewrite <- (Z.land_ones requested 16) by lia.
  rewrite <- Z.land_lor_distr_l, Z.land_ones by lia; reflexivity.
Qed.
Lemma flag_image_type_used_group__word_update_first : forall sg flags id image,
  valid_flag_state sg flags -> flagImages flags id = Some image ->
  flagImageType image = 5 -> exists group, flagUsed flags id = Some group.
Proof.
  intros sg flags id image [Hpool [Hdomain [Himages [Hused [Hfree Hnodes]]]]] Himage Htype.
  destruct Hpool as [Hnodup [Hrange Hpartition]].
  apply (proj2 (Hpartition id)); split.
  - apply (proj1 (Hdomain id)); exists image; exact Himage.
  - intro Hin; apply in_split in Hin; destruct Hin as [pre [rest Hlist]].
    destruct (Hfree pre id rest Hlist) as [old [Hold [Hfree_type Hnext]]].
    rewrite Himage in Hold; injection Hold as Heq; subst old; congruence.
Qed.
Lemma flag_post_scan_initial_loop_state__word_update_first :
  forall sg acquired id group image requested option_word posted,
  acquired.(FlagState).(flagUsed) id = Some group ->
  acquired.(FlagState).(flagImages) id = Some image ->
  image.(flagImageType) = 5 ->
  flag_post_bits sg.(osKernelConfig) image.(flagImageBits) requested option_word = Some posted ->
  flag_post_loop_state sg id requested option_word acquired posted group.(flagWaitOrder)
    nil group.(flagWaitOrder)
    (flag_post_scan_initial
      (replace_FlagS (flag_replace_bits acquired.(FlagState) id group image posted) acquired)).
Proof.
  intros sg acquired id group image requested option_word posted Hgroup Himage Htype Hposted.
  exists group, image.
  split; [exact Hgroup|]. split; [exact Himage|]. split; [exact Htype|].
  split; [exact Hposted|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  exists (flag_group_set_bits group posted), (flag_image_set_bits image posted), nil.
  cbn [flag_post_scan_initial flag_post_scan_state replace_FlagS FlagState
    flag_replace_bits flagUsed flagImages flag_image_set_bits flag_group_set_bits
    flagImageBits flagWaitOrder].
  repeat split; try apply kernel_resources.kernel_map_set_same; reflexivity.
Qed.
Lemma flag_post_current_word_merge_updated__word_update_first :
  forall sg state id group image bits,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg (replace_FlagS (flag_replace_bits state.(FlagState) id group image bits) state) ->
  (flag_pool_addr sg id + 8) # UShort |-> bits **
    flag_post_current_word_frame sg state id image |--
  kernel_program_fields_inv sg
    (replace_FlagS (flag_replace_bits state.(FlagState) id group image bits) state).
Proof.
  intros sg state id group image bits Hcfg Hvalid.
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true)
    by (rewrite Hcfg; reflexivity).
  pose proof (flag_fields_raw_rep_merge_updated_group sg state.(FlagState)
    (flag_replace_bits state.(FlagState) id group image bits) id (flag_image_set_bits image bits)
    (kernel_resources.kernel_map_set_same _ _ _ _) 
    ltac:(intros j Hne; cbn [flag_replace_bits flagImages];
      symmetry; apply kernel_resources.kernel_map_set_other; exact Hne)
    eq_refl eq_refl) as Hmerge.
  unfold kernel_program_fields_inv, kernel_program_fields_rep, UCOS2_fields_raw_rep,
    flag_fields_configured_rep.
  rewrite Henabled, UCOS2_raw_rep_missing_flag_replace_eq.
  entailer!.
  sep_apply_r_atomic Hmerge.
  unfold flag_post_current_word_frame, flag_group_rep.
  cbn [flag_image_set_bits flagImageType flagImageHead flagImageBits flagImageName flagImagePadding].
  assert (Hword : flag_word_rep sg.(osKernelConfig) (flag_pool_addr sg id + 8) bits =
    ((flag_pool_addr sg id + 8) # UShort |-> bits)) by (rewrite Hcfg; reflexivity).
  rewrite Hword; entailer!.
Qed.
Lemma flag_replace_bits_preserves_kernel_validity__word_update_remaining :
  forall sg state id group image posted,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg state ->
  state.(FlagState).(flagUsed) id = Some group ->
  state.(FlagState).(flagImages) id = Some image ->
  flag_word_in_range sg.(osKernelConfig) posted ->
  UCOS2_state_inv sg
    (replace_FlagS (flag_replace_bits state.(FlagState) id group image posted) state).
Proof.
  intros sg state id group image posted Hcfg Hvalid Hgroup Himage Hbits.
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *.
  destruct Hvalid as [Hprofile [Htask [Hsched [Hevent [Hcross [Hidle [Hreserved
    [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hroots [Hpark Hmutex]]]]]]]]]]]]]]].
  assert (Hflags_new : valid_flag_configuration sg
    (flag_replace_bits state.(FlagState) id group image posted)).
  { unfold valid_flag_configuration in Hflags |- *; rewrite Hcfg in Hflags |- *.
    cbn [selected_kernel_configuration cfgFlagEnabled] in Hflags |- *.
    eapply flag_replace_bits_preserves_validity; eauto. }
  assert (Hcross_new : cross_module_invariants.cross_module_consistency sg
    (replace_FlagS (flag_replace_bits state.(FlagState) id group image posted) state)).
  { apply cross_module_invariants.cross_module_consistency_flag_nodes_frame;
      [reflexivity | exact Hcross]. }
  assert (Hroots_new : kernel_names.kernel_names_valid sg
    (replace_FlagS (flag_replace_bits state.(FlagState) id group image posted) state)).
  { eapply kernel_names.kernel_names_valid_frame; try exact Hroots; try reflexivity;
      try (intros p Hp; exact Hp).
    intros p [j [other [Hother Hp]]].
    change (kernel_resources.kernel_map_set (flagUsed (FlagState state)) id
      (Some (flag_group_set_bits group posted)) j = Some other) in Hother.
    unfold kernel_resources.kernel_map_set in Hother.
    destruct (Z.eq_dec j id) as [-> | Hneq].
    - inversion Hother; subst. exists id, group; split; [exact Hgroup | reflexivity].
    - exists j, other; auto. }
  repeat first [assumption | split].
Qed.
Lemma flag_live_image_has_group__word_update_remaining : forall sg flags id image,
  valid_flag_state sg flags ->
  flags.(flagImages) id = Some image ->
  image.(flagImageType) = 5 ->
  exists group, flags.(flagUsed) id = Some group.
Proof.
  intros sg flags id image [[Hnd [Hfree_range Hpartition]]
    [Hdomain [Himages [Hused [Hfree Hnodes]]]]] Himage Htype.
  apply (proj2 (Hpartition id)).
  split.
  - apply (proj1 (Hdomain id)); eauto.
  - intros Hin; apply in_split in Hin; destruct Hin as [pre [rest Hlist]].
    destruct (Hfree pre id rest Hlist) as [other [Hother [Hzero Hhead]]].
    rewrite Himage in Hother; inversion Hother; subst other; lia.
Qed.
Lemma flag_replace_bits_preserves_no_waiters__word_update_remaining :
  forall flags id group image posted,
  flags.(flagUsed) id = Some group ->
  flag_api_entry_source_spec.flag_state_has_no_waiters flags ->
  flag_api_entry_source_spec.flag_state_has_no_waiters
    (flag_replace_bits flags id group image posted).
Proof.
  intros flags id group image posted Hgroup [Horders Hnodes].
  split; [|exact Hnodes].
  intros j current Hcurrent.
  change (kernel_resources.kernel_map_set (flagUsed flags) id
    (Some (flag_group_set_bits group posted)) j = Some current) in Hcurrent.
  unfold kernel_resources.kernel_map_set in Hcurrent.
  destruct (Z.eq_dec j id) as [-> | Hneq].
  - inversion Hcurrent; subst; exact (Horders id group Hgroup).
  - exact (Horders j current Hcurrent).
Qed.
Lemma flag_replace_bits_preserves_source_observation__word_update_remaining :
  forall execution state id group image posted,
  state.(FlagState).(flagUsed) id = Some group ->
  flag_post_source_observation execution state ->
  flag_post_source_observation execution
    (replace_FlagS (flag_replace_bits state.(FlagState) id group image posted) state).
Proof.
  intros [call | handler] state id group image posted Hgroup Hsource.
  - unfold flag_post_source_observation in *.
    destruct (os_sched_call_origin call).
    + apply flag_replace_bits_preserves_no_waiters__word_update_remaining; assumption.
    + exact Hsource.
  - unfold flag_post_source_observation in *.
    change (if SchedStateDef.isRunning (SchedState state)
      then sched_disabled_isr_source handler state
      else flag_api_entry_source_spec.flag_state_has_no_waiters
        (flag_replace_bits state.(FlagState) id group image posted)).
    destruct (SchedStateDef.isRunning (SchedState state)).
    + exact Hsource.
    + apply flag_replace_bits_preserves_no_waiters__word_update_remaining; assumption.
Qed.
Lemma flag_post_current_word_merge_updated__word_update_remaining :
  forall sg state id group image posted,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg
    (replace_FlagS (flag_replace_bits state.(FlagState) id group image posted) state) ->
  ((flag_pool_addr sg id + 8) # UShort |-> posted) **
    flag_post_current_word_frame sg state id image |--
  kernel_program_fields_inv sg
    (replace_FlagS (flag_replace_bits state.(FlagState) id group image posted) state).
Proof.
  intros sg state id group image posted Hcfg Hvalid.
  pose (after := replace_FlagS (flag_replace_bits state.(FlagState) id group image posted) state).
  assert (Himage : after.(FlagState).(flagImages) id = Some (flag_image_set_bits image posted)).
  { unfold after; cbn [replace_FlagS flag_replace_bits]; apply kernel_resources.kernel_map_set_same. }
  change (((flag_pool_addr sg id + 8) # UShort |-> posted) **
    flag_post_current_word_frame sg state id image |-- kernel_program_fields_inv sg after).
  rewrite (flag_post_current_word_resources sg after id (flag_image_set_bits image posted) Hcfg Himage).
  assert (Hframe : flag_post_current_word_frame sg state id image --||--
    flag_post_current_word_frame sg after id (flag_image_set_bits image posted)).
  { unfold flag_post_current_word_frame, after.
    rewrite UCOS2_raw_rep_missing_flag_replace_eq.
    cbn [replace_FlagS flag_image_set_bits].
    rewrite (flag_fields_raw_rep_without_group_frame sg state.(FlagState)
      (flag_replace_bits state.(FlagState) id group image posted) id).
    - split; reflexivity.
    - intros j Hneq.
      change (flagImages (FlagState state) j = kernel_resources.kernel_map_set
        (flagImages (FlagState state)) id (Some (flag_image_set_bits image posted)) j).
      rewrite kernel_resources.kernel_map_set_other by exact Hneq; reflexivity.
    - reflexivity.
    - reflexivity. }
  rewrite <- Hframe; cbn [flag_image_set_bits]; entailer!.
Qed.
Lemma flag_post_word_update_starts_scan__word_update_remaining :
  forall environment critical sg pointer id requested option_word mask original before saved entry image posted,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_post_protected_facts environment critical sg pointer id requested option_word
    mask original before saved entry ->
  flag_post_image_at entry.(flag_post_acquired) id image ->
  image.(flagImageType) = 5 ->
  flag_post_bits sg.(osKernelConfig) image.(flagImageBits) requested option_word = Some posted ->
  ((flag_pool_addr sg id + 8) # UShort |-> posted) **
    flag_post_current_word_frame sg entry.(flag_post_acquired) id image **
    flag_post_critical_frame environment critical entry.(flag_post_local) sg
      entry.(flag_post_entered) saved entry.(flag_post_acquired) entry.(flag_post_acquired) |--
  EX context,
    coq_prop (flag_post_initial_scan context) &&
    flag_post_loop_cut environment critical sg pointer id requested option_word mask original
      before saved context (flag_post_remaining_node context.(flag_post_remaining)) 0.
Proof.
  intros environment critical sg pointer id requested option_word mask original before
    saved entry image posted Hcfg Hfacts Himage Htype Hposted.
  destruct Hfacts as [Hprefix [Hvalid [Hcoverage Hsource]]].
  assert (Hflags : valid_flag_state sg entry.(flag_post_acquired).(FlagState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid.
    destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hflags _]]]]]]]].
    unfold valid_flag_configuration in Hflags; rewrite Hcfg in Hflags; exact Hflags. }
  destruct (flag_live_image_has_group__word_update_remaining sg
    entry.(flag_post_acquired).(FlagState) id image Hflags Himage Htype) as [group Hgroup].
  pose (after := replace_FlagS
    (flag_replace_bits entry.(flag_post_acquired).(FlagState) id group image posted)
    entry.(flag_post_acquired)).
  assert (Hbounds : flag_word_in_range sg.(osKernelConfig) posted).
  { eapply flag_post_bits_in_range; [rewrite Hcfg; simpl; lia | exact Hposted]. }
  assert (Hvalid_after : UCOS2_state_inv sg after).
  { unfold after; eapply flag_replace_bits_preserves_kernel_validity__word_update_remaining; eauto. }
  assert (Hsource_after : flag_post_source_observation entry.(flag_post_entered) after).
  { unfold after; apply flag_replace_bits_preserves_source_observation__word_update_remaining; assumption. }
  assert (Hloop : flag_post_loop_state sg id requested option_word entry.(flag_post_acquired)
    posted group.(flagWaitOrder) nil group.(flagWaitOrder) (flag_post_scan_initial after)).
  { unfold flag_post_loop_state.
    exists group, image.
    split; [exact Hgroup |]. split; [exact Himage |]. split; [exact Htype |].
    split; [exact Hposted |]. split; [reflexivity |]. split; [reflexivity |].
    split; [reflexivity |]. split; [reflexivity |].
    exists (flag_group_set_bits group posted), (flag_image_set_bits image posted), nil.
    split; [apply kernel_resources.kernel_map_set_same |].
    split; [apply kernel_resources.kernel_map_set_same |].
    split; reflexivity. }
  pose (context := {| flag_post_loop_entry := entry;
    flag_post_posted_word := posted;
    flag_post_initial_order := group.(flagWaitOrder);
    flag_post_visited := nil;
    flag_post_remaining := group.(flagWaitOrder);
    flag_post_accumulator := flag_post_scan_initial after;
    flag_post_loop_local := entry.(flag_post_local) |}).
  Exists context.
  assert (Hloopfacts : flag_post_loop_facts environment critical sg pointer id requested option_word
    mask original before saved context (flag_post_remaining_node context.(flag_post_remaining)) 0).
  { unfold flag_post_loop_facts, context.
    split; [unfold flag_post_protected_facts, flag_post_current_valid; auto |].
    split; [exact Hloop |].
    split; [reflexivity |].
    split; [reflexivity |].
    split; [exact Hvalid_after |]. split; assumption. }
  sep_apply_l_atomic (flag_post_current_word_merge_updated__word_update_remaining sg
    entry.(flag_post_acquired) id group image posted Hcfg Hvalid_after).
  unfold flag_post_loop_cut, flag_post_source_masked, flag_post_masked,
    flag_post_critical_frame, kernel_continuation_world_spec.kernel_continuation_inv.
  entailer!.
  unfold context, after.
  cbn [flag_post_loop_entry flag_post_loop_local flag_post_accumulator
    flag_post_scan_state flag_post_scan_initial replace_FlagS TskState].
  entailer!.
Qed.
Lemma flag_post_current_flag_valid__satisfied_helper_inputs : forall sg execution state,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_post_current_valid sg execution state -> valid_flag_state sg state.(FlagState).
Proof.
  intros sg execution state Hcfg [Hinv _].
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hinv.
  assert (Hflags : valid_flag_configuration sg state.(FlagState)) by tauto.
  unfold valid_flag_configuration in Hflags; rewrite Hcfg in Hflags; exact Hflags.
Qed.
Lemma flag_post_loop_image_and_mask__satisfied_helper_inputs :
  forall environment critical sg pointer id requested option_word mask original before
    saved context node schedule image waiter,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_post_loop_facts environment critical sg pointer id requested option_word mask
    original before saved context node schedule ->
  flag_post_image_at context.(flag_post_accumulator).(flag_post_scan_state) id image ->
  flag_post_waiter_at context.(flag_post_accumulator).(flag_post_scan_state) node waiter ->
  image.(flagImageBits) = context.(flag_post_posted_word) /\
    0 <= waiter.(flagWaitImage).(flagNodeMask) < 65536.
Proof.
  intros environment critical sg pointer id requested option_word mask original before
    saved context node schedule image waiter Hcfg Hfacts Himage Hwaiter.
  destruct Hfacts as [_ [Hloop [_ [_ Hvalid]]]].
  pose proof (flag_post_current_flag_valid__satisfied_helper_inputs _ _ _ Hcfg Hvalid) as Hflags.
  destruct Hloop as [initial_group [initial_image Hloop]].
  destruct Hloop as [_ [_ [_ [_ [_ [_ [_ [_ Hcurrent]]]]]]]].
  destruct Hcurrent as [current [current_image [kept [_ [Hcurrent [Hbits _]]]]]].
  unfold flag_post_image_at in Himage.
  assert (image = current_image) by congruence; subst image.
  split; [exact Hbits|].
  destruct Hflags as [_ [_ [_ [_ [_ Hnodes]]]]].
  destruct (Hnodes node waiter Hwaiter) as [_ [[Hrange _] _]].
  unfold flag_word_in_range in Hrange; rewrite Hcfg in Hrange; exact Hrange.
Qed.
Lemma flag_post_land_word_in_range__satisfied_helper_inputs : forall word mask,
  0 <= mask < 65536 ->
  0 <= Z.land word mask < 65536 /\
    flag_word selected_kernel_configuration (Z.land word mask) = Z.land word mask.
Proof.
  intros word mask Hmask.
  assert (Htrunc : unsigned_last_nbits (Z.land word mask) 16 = Z.land word mask).
  { apply unsigned_last_nbits_land_missing_r; [lia|exact Hmask]. }
  split.
  - pose proof (unsigned_Lastnbits_range (Z.land word mask) 16 ltac:(lia)) as Hrange.
    rewrite Htrunc in Hrange; exact Hrange.
  - exact Htrunc.
Qed.
Lemma flag_post_node_word_resources_equiv__satisfied_helper_inputs :
  forall sg state id node image waiter,
  flag_post_image_at state id image -> flag_post_waiter_at state node waiter ->
  flag_fields_raw_rep sg state.(FlagState) **
    UCOS2_raw_rep_missing_flag sg state ** unmap_table_rep sg --||--
  flag_node_fields_rep sg.(osKernelConfig) node waiter.(flagWaitImage) **
    flag_word_rep sg.(osKernelConfig) (flag_pool_addr sg id + 8) image.(flagImageBits) **
    flag_post_node_word_frame sg state id node image.
Proof.
  intros sg state id node image waiter Himage Hwaiter.
  rewrite (flag_fields_raw_rep_split_group sg state.(FlagState) id image Himage).
  unfold flag_fields_raw_rep_without_group.
  assert (Hnode : flag_wait_nodes_fields_rep sg state.(FlagState).(flagWaitNodes) --||--
    flag_node_fields_rep sg.(osKernelConfig) node waiter.(flagWaitImage) **
    flag_wait_nodes_fields_without_node sg state.(FlagState).(flagWaitNodes) node).
  { split; [apply flag_wait_nodes_fields_rep_split_node |
      apply flag_wait_nodes_fields_rep_merge_node]; exact Hwaiter. }
  rewrite Hnode; unfold flag_post_node_word_frame, flag_group_rep; split; entailer!.
Qed.
Lemma flag_post_current_flag_valid__loop_views_and_progress : forall sg execution state,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_post_current_valid sg execution state -> valid_flag_state sg state.(FlagState).
Proof.
  intros sg execution state Hcfg [Hinv _].
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hinv.
  assert (Hflags : valid_flag_configuration sg state.(FlagState)) by tauto.
  unfold valid_flag_configuration in Hflags; rewrite Hcfg in Hflags; exact Hflags.
Qed.
Lemma flag_post_masked_split_fields__loop_views_and_progress : forall environment critical local sg execution saved acquired state,
  flag_post_current_valid sg execution state ->
  flag_post_source_masked environment critical local sg execution saved acquired state --||--
    kernel_program_fields_inv sg state **
    flag_post_critical_frame environment critical local sg execution saved acquired state.
Proof.
  intros environment critical local sg execution saved acquired state [Hinv [Hcoverage Hsource]].
  unfold flag_post_source_masked, flag_post_masked, flag_post_critical_frame,
    kernel_continuation_inv; split; entailer!.
Qed.
Lemma flag_post_initial_scan_head__loop_views_and_progress : forall environment critical sg pointer id requested option_word mask original before saved context node schedule,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_post_initial_scan context ->
  flag_post_loop_facts environment critical sg pointer id requested option_word mask original before saved context node schedule ->
  exists image, flag_post_image_at context.(flag_post_accumulator).(flag_post_scan_state) id image /\
    image.(flagImageHead) = node.
Proof.
  intros environment critical sg pointer id requested option_word mask original before saved context node schedule Hcfg Hinitial Hfacts.
  destruct Hfacts as [Hprotected [Hloop [Hnode [Hschedule Hvalid]]]].
  pose proof (flag_post_current_flag_valid__loop_views_and_progress _ _ _ Hcfg Hvalid) as Hflags.
  destruct Hloop as [group [image [Hgroup [Himage [Htype [Hposted [Horder [Hremaining [Hscan Hrest]]]]]]]]].
  unfold flag_post_initial_scan in Hinitial.
  rewrite Hinitial in Hremaining, Hscan; cbn [List.app] in Hremaining.
  cbn [flag_post_scan fold_left] in Hscan; injection Hscan as Hscan.
  rewrite <- Hscan; cbn [flag_post_scan_initial flag_post_scan_state].
  exists (flag_image_set_bits image context.(flag_post_posted_word)).
  unfold flag_post_image_at; cbn [replace_FlagS FlagState flag_replace_bits flagImages].
  rewrite kernel_map_set_same; split; [reflexivity|].
  rewrite <- Hscan in Hflags; cbn [flag_post_scan_initial flag_post_scan_state] in Hflags.
  destruct Hflags as [_ [_ [_ [Hused _]]]].
  specialize (Hused id (flag_group_set_bits group context.(flag_post_posted_word))).
  assert (Hlookup : (replace_FlagS (flag_replace_bits (flag_post_acquired (flag_post_loop_entry context)).(FlagState) id group image context.(flag_post_posted_word)) (flag_post_acquired (flag_post_loop_entry context))).(FlagState).(flagUsed) id = Some (flag_group_set_bits group context.(flag_post_posted_word))).
  { cbn [replace_FlagS FlagState flag_replace_bits flagUsed]; apply kernel_map_set_same. }
  specialize (Hused Hlookup).
  destruct Hused as [_ [_ [_ [current [Hcurrent [_ [Hhead _]]]]]]].
  cbn [replace_FlagS FlagState flag_replace_bits flagImages] in Hcurrent.
  rewrite kernel_map_set_same in Hcurrent; injection Hcurrent as Hcurrent; subst current.
  cbn [flag_image_set_bits flagImageHead flag_group_set_bits flagWaitOrder] in Hhead |- *.
  rewrite Hhead, <- Horder, Hremaining, Hnode.
  destruct context.(flag_post_remaining); reflexivity.
Qed.
Lemma flag_post_remaining_waiter__loop_views_and_progress : forall environment critical sg pointer id requested option_word mask original before saved context node schedule,
  sg.(osKernelConfig) = selected_kernel_configuration -> node <> 0 ->
  flag_post_loop_facts environment critical sg pointer id requested option_word mask original before saved context node schedule ->
  exists image waiter,
    flag_post_image_at context.(flag_post_accumulator).(flag_post_scan_state) id image /\
    flag_post_waiter_at context.(flag_post_accumulator).(flag_post_scan_state) node waiter.
Proof.
  intros environment critical sg pointer id requested option_word mask original before saved context node schedule Hcfg Hnonzero Hfacts.
  destruct Hfacts as [Hprotected [Hloop [Hnode [Hschedule Hvalid]]]].
  pose proof (flag_post_current_flag_valid__loop_views_and_progress _ _ _ Hcfg Hvalid) as Hflags.
  destruct Hloop as [group [image Hloop]].
  destruct Hloop as [_ [_ [_ [_ [_ [_ [_ [_ Hcurrent]]]]]]]].
  destruct Hcurrent as [current [current_image [kept [Hgroup [Himage [_ Horder]]]]]].
  destruct context.(flag_post_remaining) as [|head rest] eqn:Hremaining;
    cbn [flag_post_remaining_node] in Hnode; [contradiction|subst node].
  destruct Hflags as [_ [_ [_ [Hused _]]]].
  destruct (Hused id current Hgroup) as [_ [_ [Hlist _]]].
  destruct (Hlist kept head rest Horder) as [waiter [Hwaiter _]].
  exists current_image, waiter; exact (conj Himage Hwaiter).
Qed.
Lemma flag_post_node_word_resources_equiv__loop_views_and_progress : forall sg state id node image waiter,
  flag_post_image_at state id image -> flag_post_waiter_at state node waiter ->
  flag_fields_raw_rep sg state.(FlagState) ** UCOS2_raw_rep_missing_flag sg state ** unmap_table_rep sg --||--
    flag_node_fields_rep sg.(osKernelConfig) node waiter.(flagWaitImage) **
    flag_word_rep sg.(osKernelConfig) (flag_pool_addr sg id + 8) image.(flagImageBits) **
    flag_post_node_word_frame sg state id node image.
Proof.
  intros sg state id node image waiter Himage Hwaiter.
  rewrite (flag_fields_raw_rep_split_group sg state.(FlagState) id image Himage).
  unfold flag_fields_raw_rep_without_group.
  assert (Hnode : flag_wait_nodes_fields_rep sg state.(FlagState).(flagWaitNodes) --||--
    flag_node_fields_rep sg.(osKernelConfig) node waiter.(flagWaitImage) **
    flag_wait_nodes_fields_without_node sg state.(FlagState).(flagWaitNodes) node).
  { split; [apply flag_wait_nodes_fields_rep_split_node | apply flag_wait_nodes_fields_rep_merge_node]; exact Hwaiter. }
  rewrite Hnode; unfold flag_post_node_word_frame, flag_group_rep; split; entailer!.
Qed.
Lemma flag_post_task_rdy_preserves_current_valid__helper_outcomes :
  forall sg execution state node bits result scheduled post,
  flag_post_current_valid sg execution state ->
  flag_task_rdy sg state node bits result = Some (scheduled, post) ->
  flag_post_current_valid sg execution post.
Proof.
  intros sg execution state node bits result scheduled post [Hinv [Hcoverage Hsource]] Hstep.
  split; [eapply UCOS2_flag_task_rdy_preserves_validity; eassumption|].
  destruct (FlagPendSchedulerResources.flag_task_rdy_preserves_stack_metadata
    sg state node bits result scheduled post Hstep) as [Hstacks Hmetadata].
  split.
  - intros slot task Htask.
    destruct (Hmetadata slot task Htask) as [old [Hold [Hgen Hsp]]].
    specialize (Hcoverage slot old Hold).
    rewrite Hgen in Hcoverage; rewrite Hstacks; exact Hcoverage.
  - pose proof (FlagPendSchedulerResources.flag_task_rdy_preserves_invocation_active
      sg state node bits result scheduled post) as Hactive.
    destruct (flag_task_rdy_result sg state node bits result scheduled post Hstep)
      as [waiter [flags [old [Hunlink [Hold [Hpost Hscheduled]]]]]].
    pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink)) as Hnode.
    subst post.
    destruct execution as [call|handler].
    + unfold flag_post_source_observation in *.
      destruct (os_sched_call_origin call) eqn:Horigin.
      * destruct Hsource as [_ Hnone]; specialize (Hnone node); congruence.
      * destruct Hsource as [[Horigin_key [Hinvocation Hcurrent]]
          [[clean [Hclean [Hg Hzero]]] [Hpark Hready]]].
        unfold flag_api_task_entry_observation, kernel_call_task_source.
        split.
        { split; [exact Horigin_key|]. split.
          - apply Hactive; assumption.
          - unfold task_execution_current in *; rewrite Horigin in *; exact Hcurrent. }
        split.
        { unfold flag_task_clean_at.
          change (exists clean,
            (if Z.eqb (stackLeaseSlot (os_sched_call_stack call)) (flagTask waiter)
             then Some (task_flag_wake old bits result)
             else inUsedTaskStates (TskState state) (stackLeaseSlot (os_sched_call_stack call))) = Some clean /\
            taskGeneration clean = stackLeaseGeneration (os_sched_call_stack call) /\ tcbFlagNode clean = 0).
          destruct (Z.eqb (stackLeaseSlot (os_sched_call_stack call)) (flagTask waiter)) eqn:E.
          - apply Z.eqb_eq in E; rewrite E, Hold in Hclean; inversion Hclean; subst clean.
            exists (task_flag_wake old bits result); repeat split; assumption || reflexivity.
          - exists clean; auto. }
        split; [exact Hpark|].
        change ((if is_effectively_ready (stat (task_flag_wake old bits result))
                    (dly (task_flag_wake old bits result))
                 then helpers.insert_sorted_by (sched_task_key sg (TskState state)) (flagTask waiter)
                   (helpers.remove_Z_eqb (flagTask waiter) (readyList (SchedState state)))
                 else readyList (SchedState state)) <> nil).
        destruct (is_effectively_ready (stat (task_flag_wake old bits result))
          (dly (task_flag_wake old bits result))); [|exact Hready].
        destruct (helpers.remove_Z_eqb (flagTask waiter) (readyList (SchedState state))) as [|head tail];
          cbn [helpers.insert_sorted_by]; try discriminate.
        destruct (Z.ltb _ _); discriminate.
    + unfold flag_post_source_observation in *.
      change (if isRunning (SchedState state) then
        sched_disabled_isr_source handler (flag_wake_state sg state waiter flags old bits result)
        else flag_state_has_no_waiters flags).
      destruct (isRunning (SchedState state)) eqn:Hrunning.
      * exact Hsource.
      * destruct Hsource as [_ Hnone]; specialize (Hnone node); congruence.
Qed.
Lemma flag_post_task_rdy_next_resources__helper_outcomes :
  forall environment critical sg pointer id requested option_word mask original before saved
    context node schedule waiter bits returned,
  flag_post_parameters sg pointer id requested option_word ->
  flag_post_loop_facts environment critical sg pointer id requested option_word mask original before
    saved context node schedule ->
  flag_post_waiter_at context.(flag_post_accumulator).(flag_post_scan_state) node waiter ->
  flag_post_waiter_satisfied sg context waiter bits ->
  0 <= bits < 65536 ->
  flag_task_rdy_fields_post sg context.(flag_post_accumulator).(flag_post_scan_state)
    node waiter bits PendOK returned **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg context.(flag_post_accumulator).(flag_post_scan_state) **
  unmap_table_rep sg **
  flag_post_critical_frame environment critical context.(flag_post_loop_local) sg
    context.(flag_post_loop_entry).(flag_post_entered) saved
    context.(flag_post_loop_entry).(flag_post_acquired) context.(flag_post_accumulator).(flag_post_scan_state)
  |-- EX (scheduled : bool), EX pending,
    coq_prop (returned = if scheduled then 1 else 0) &&
    flag_post_next_cut environment critical sg pointer id requested option_word mask original before saved
      pending node (if scheduled then 1 else schedule).
Proof.
  intros environment critical sg pointer id requested option_word mask original before saved
    context node schedule waiter bits returned Hparams Hloop Hlookup Hsatisfied Hbits.
  pose proof Hloop as [Hprotected [Hstate [Hnode [Hschedule Hvalid]]]].
  pose proof Hvalid as [Hinv [Hcoverage Hsource]].
  pose proof Hparams as [Hcfg [_ [_ [_ [Hlayout _]]]]].
  destruct (flag_task_rdy_stable_domain sg _ node waiter bits Hcfg Hlayout Hbits Hinv Hlookup)
    as [old Hdomain].
  pose proof Hdomain as [_ [[_ [_ [_ [Hnodeaddr _]]]] _]].
  pose proof Hinv as [_ [_ [_ [_ [Hcross _]]]]].
  assert (Hconsistent : task_flag_waiter_consistency sg
    context.(flag_post_accumulator).(flag_post_scan_state).(TskState)
    context.(flag_post_accumulator).(flag_post_scan_state).(FlagState)).
  { unfold cross_module_consistency in Hcross; tauto. }
  destruct (flag_post_waiter_parked_from_coverage sg
    context.(flag_post_loop_entry).(flag_post_entered) _ node waiter
    Hconsistent Hcoverage (flag_post_source_active_node_clear _ _ Hsource) Hlookup)
    as [region [fragments Hparked]].
  unfold flag_post_critical_frame; Intros.
  sep_apply_l_atomic (flag_wake_fields_returns_node_with_continuation_map
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    environment.(task_stack_call_port) environment.(task_stack_call_continuations)
    sg _ node waiter old bits PendOK returned context.(flag_post_loop_local) Hinv Hdomain).
  Intros post scheduled.
  assert (Hstep : flag_task_rdy sg context.(flag_post_accumulator).(flag_post_scan_state)
      node bits PendOK = Some (scheduled, post)) by tauto.
  pose proof (flag_post_task_rdy_preserves_current_valid__helper_outcomes sg
    context.(flag_post_loop_entry).(flag_post_entered) _ node bits PendOK scheduled post
    Hvalid Hstep) as Hpostvalid.
  set (lease := {| stackLeaseRegion := region; stackLeaseSlot := waiter.(flagTask);
    stackLeaseGeneration := waiter.(flagTaskGeneration) |}).
  set (pending := {| flag_post_pending_loop := context; flag_post_pending_waiter := waiter;
    flag_post_pending_ready := bits; flag_post_pending_returned := Some scheduled;
    flag_post_pending_state := post; flag_post_pending_lease := lease |}).
  assert (Hnormalized : flag_post_loop_facts environment critical sg pointer id requested option_word
    mask original before saved context node
    (flag_post_schedule_word context.(flag_post_accumulator).(flag_post_scan_visits))).
  { rewrite Hschedule in Hloop; exact Hloop. }
  assert (Hpending : flag_post_pending_facts sg pending node (if scheduled then 1 else schedule)).
  { unfold flag_post_pending_facts, pending; cbn.
    split; [exact Hnode|]. split; [exact Hlookup|]. split; [exact Hnodeaddr|].
    split.
    - split; [exact Hsatisfied|]. split; [exact Hstep|].
      split; [reflexivity|]. exists fragments; exact Hparked.
    - rewrite Hschedule; unfold flag_post_schedule_word.
      destruct scheduled, (flag_post_schedule (flag_post_scan_visits (flag_post_accumulator context)));
        reflexivity. }
  Exists scheduled pending.
  unfold flag_post_next_cut, flag_post_pending_world.
  cbn [pending flag_post_pending_loop flag_post_pending_waiter flag_post_pending_returned
    flag_post_pending_state flag_post_pending_ready flag_post_pending_lease].
  unfold kernel_program_fields_inv, kernel_program_fields_rep, UCOS2_fields_inv.
  unfold flag_post_critical_frame.
  entailer!; exact (proj2 (proj2 Hpostvalid)).
Qed.
Lemma flag_post_loop_node_image__helper_outcomes :
  forall environment critical sg pointer id requested option_word mask original before saved
    context node schedule waiter image,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_post_loop_facts environment critical sg pointer id requested option_word mask original before
    saved context node schedule ->
  flag_post_waiter_at context.(flag_post_accumulator).(flag_post_scan_state) node waiter ->
  flag_post_image_at context.(flag_post_accumulator).(flag_post_scan_state) id image ->
  waiter.(flagNodeAddr) = node /\ 0 <= waiter.(flagWaitImage).(flagNodeMask) < 65536 /\
    context.(flag_post_posted_word) = image.(flagImageBits).
Proof.
  intros environment critical sg pointer id requested option_word mask original before saved
    context node schedule waiter image Hcfg Hloop Hwaiter Himage.
  destruct Hloop as [_ [Hloop [_ [_ [Hinv _]]]]].
  pose proof Hinv as [_ [_ [_ [_ [_ [_ [_ [Hflags _]]]]]]]].
  unfold valid_flag_configuration in Hflags; rewrite Hcfg in Hflags.
  cbn [selected_kernel_configuration cfgFlagEnabled] in Hflags.
  destruct (valid_flag_state_node_position sg _ node waiter Hflags Hwaiter)
    as [group [visited [rest [_ [_ [Hnode _]]]]]].
  pose proof Hflags as [_ [_ [_ [_ [_ Hnodes]]]]].
  destruct (Hnodes node waiter Hwaiter) as [_ [[Hrange _] _]].
  unfold flag_word_in_range in Hrange; rewrite Hcfg in Hrange.
  change (0 <= flagNodeMask (flagWaitImage waiter) < 65536) in Hrange.
  split; [exact Hnode|]. split; [exact Hrange|].
  unfold flag_post_loop_state in Hloop; decompose [ex and] Hloop.
  unfold flag_post_image_at in Himage.
  match goal with
  | Hcurrent : flagImages _ id = Some ?current,
    Hposted : flagImageBits ?current = flag_post_posted_word context |- _ =>
    assert (current = image) by congruence; congruence
  end.
Qed.
Lemma flag_post_word_land_eq__helper_outcomes : forall word mask,
  0 <= mask < 65536 ->
  flag_word selected_kernel_configuration (Z.land word mask) = Z.land word mask.
Proof.
  intros word mask Hmask.
  change (Z.land word mask mod 2^16 = Z.land word mask).
  rewrite <- Z.land_ones by lia.
  rewrite <- Z.land_assoc.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by exact Hmask.
  reflexivity.
Qed.
Lemma flag_post_node_word_frame_merge__helper_outcomes : forall sg state id image,
  state.(FlagState).(flagImages) id = Some image ->
  forall node,
  flag_word_rep sg.(osKernelConfig) (flag_pool_addr sg id + 8) image.(flagImageBits) **
    flag_post_node_word_frame sg state id node image
  |-- flag_post_registered_node_frame sg state node.
Proof.
  intros sg state id image Himage node.
  unfold flag_post_node_word_frame, flag_post_registered_node_frame.
  rewrite <- (flag_groups_merge_group sg state.(FlagState) id image Himage).
  unfold flag_group_rep; entailer!.
Qed.
Lemma flag_post_unsatisfied_next_resources__helper_outcomes :
  forall environment critical sg pointer id requested option_word mask original before saved
    context node schedule waiter bits (lease : TaskStackLease),
  flag_post_loop_facts environment critical sg pointer id requested option_word mask original before
    saved context node schedule ->
  flag_post_waiter_at context.(flag_post_accumulator).(flag_post_scan_state) node waiter ->
  waiter.(flagNodeAddr) = node ->
  flag_post_node_test sg.(osKernelConfig) context.(flag_post_posted_word)
    waiter.(flagWaitImage).(flagNodeMask) waiter.(flagWaitImage).(flagNodeMode) = Some (bits, false) ->
  flag_node_fields_return_loan sg.(osKernelConfig) waiter **
  flag_post_registered_node_frame sg context.(flag_post_accumulator).(flag_post_scan_state) node **
  flag_post_critical_frame environment critical context.(flag_post_loop_local) sg
    context.(flag_post_loop_entry).(flag_post_entered) saved
    context.(flag_post_loop_entry).(flag_post_acquired) context.(flag_post_accumulator).(flag_post_scan_state)
  |-- EX pending,
    flag_post_next_cut environment critical sg pointer id requested option_word mask original before saved
      pending node schedule.
Proof.
  intros environment critical sg pointer id requested option_word mask original before saved
    context node schedule waiter bits lease Hloop Hlookup Hnodeaddr Htest.
  pose proof Hloop as [Hprotected [Hstate [Hnode [Hschedule Hvalid]]]].
  set (pending := {| flag_post_pending_loop := context; flag_post_pending_waiter := waiter;
    flag_post_pending_ready := bits; flag_post_pending_returned := None;
    flag_post_pending_state := context.(flag_post_accumulator).(flag_post_scan_state);
    flag_post_pending_lease := lease |}).
  assert (Hnormalized : flag_post_loop_facts environment critical sg pointer id requested option_word
    mask original before saved context node
    (flag_post_schedule_word context.(flag_post_accumulator).(flag_post_scan_visits))).
  { rewrite Hschedule in Hloop; exact Hloop. }
  assert (Hpending : flag_post_pending_facts sg pending node schedule).
  { unfold flag_post_pending_facts, pending; cbn.
    split; [exact Hnode|]. split; [exact Hlookup|]. split; [exact Hnodeaddr|].
    split; [auto|].
    rewrite Bool.orb_false_r; exact Hschedule. }
  Exists pending.
  unfold flag_post_next_cut, flag_post_pending_world.
  cbn [pending flag_post_pending_loop flag_post_pending_waiter flag_post_pending_returned
    flag_post_pending_state flag_post_pending_ready flag_post_pending_lease].
  entailer!; exact (proj1 Hvalid).
Qed.
