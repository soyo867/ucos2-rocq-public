Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Import UCOS2_C_Rules ListNotations.
Import KernelHeapStorage KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source: ARMv7-A/GNU non-VFP OS_CPU_SR_Save. This local memory/register
    projection follows MRS; CPSID IF; DSB; BX LR in that order. It is NOT
    the entire possibly interrupted call. In particular it neither changes
    a CPU/CSL assertion by entailment nor manufactures an inside handle.

    CPSID uses the existing explicit maskable-A32 specialization. DSB is
    retained as a distinct source instruction; its ordering/visibility and
    BX interworking are the approved architecture boundary, not assertions
    that arbitrary pending device writes have no effect. The kernel-memory
    projection here is the QCP ordinary-memory view of this local fragment.
    Return records the actual LR word; it does not assume an ARM-only caller. *)
Inductive KernelSaveInstruction : Type :=
| SaveReadCPSR | SaveMaskIRQFIQ | SaveDataBarrier | SaveBranchLR.

Record KernelSaveRegisters : Type := {
  kernel_save_cpsr : Z;
  kernel_save_r0 : Z;
  kernel_save_lr : Z;
  kernel_save_return_word : option Z;
}.

Definition kernel_save_read_cpsr (registers : KernelSaveRegisters) : KernelSaveRegisters :=
  {| kernel_save_cpsr := registers.(kernel_save_cpsr);
     kernel_save_r0 := registers.(kernel_save_cpsr);
     kernel_save_lr := registers.(kernel_save_lr);
     kernel_save_return_word := None |}.

Definition kernel_save_mask_irq_fiq (registers : KernelSaveRegisters) : KernelSaveRegisters :=
  {| kernel_save_cpsr := snd (armv7a_cpsr_save_direct registers.(kernel_save_cpsr));
     kernel_save_r0 := registers.(kernel_save_r0);
     kernel_save_lr := registers.(kernel_save_lr);
     kernel_save_return_word := None |}.

Definition kernel_save_branch_lr (registers : KernelSaveRegisters) : KernelSaveRegisters :=
  {| kernel_save_cpsr := registers.(kernel_save_cpsr);
     kernel_save_r0 := registers.(kernel_save_r0);
     kernel_save_lr := registers.(kernel_save_lr);
     kernel_save_return_word := Some registers.(kernel_save_lr) |}.

(** Each index is the SAME instruction cut's OS state and physical local
    model. CPU/STS/token projections are deliberately not made equal: their
    real resource exchange is still the existing external Save contract.
    The equality of OS state and memory in these constructors applies to
    these four local instructions only, not to an IRQ or a complete Save. *)
Inductive kernel_call_save_instruction_step (arch : A32InterruptContext)
  : KernelSaveInstruction -> KernelSaveRegisters -> UCOS2_Verify_State -> model ->
    KernelSaveRegisters -> UCOS2_Verify_State -> model -> Prop :=
| KernelSaveReadCPSR : forall registers state before after,
    registers.(kernel_save_return_word) = None ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) ->
    kernel_call_save_instruction_step arch SaveReadCPSR registers state before
      (kernel_save_read_cpsr registers) state after
| KernelSaveMaskIRQFIQ : forall registers state before after,
    registers.(kernel_save_return_word) = None ->
    a32_maskable_context arch registers.(kernel_save_cpsr) ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) ->
    kernel_call_save_instruction_step arch SaveMaskIRQFIQ registers state before
      (kernel_save_mask_irq_fiq registers) state after
| KernelSaveDataBarrier : forall registers state before after,
    registers.(kernel_save_return_word) = None ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) ->
    kernel_call_save_instruction_step arch SaveDataBarrier registers state before
      registers state after
| KernelSaveBranchLR : forall registers state before after,
    registers.(kernel_save_return_word) = None ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) ->
    kernel_call_save_instruction_step arch SaveBranchLR registers state before
      (kernel_save_branch_lr registers) state after.

Inductive kernel_call_save_instruction_execution (arch : A32InterruptContext)
  : list KernelSaveInstruction -> KernelSaveRegisters -> UCOS2_Verify_State -> model ->
    KernelSaveRegisters -> UCOS2_Verify_State -> model -> Prop :=
| KernelSaveExecutionNil : forall registers state heap,
    kernel_call_save_instruction_execution arch [] registers state heap registers state heap
| KernelSaveExecutionCons : forall instruction instructions registers state before
    middle_registers middle_state middle final_registers final_state after,
    kernel_call_save_instruction_step arch instruction registers state before
      middle_registers middle_state middle ->
    kernel_call_save_instruction_execution arch instructions middle_registers middle_state middle
      final_registers final_state after ->
    kernel_call_save_instruction_execution arch (instruction :: instructions) registers state before
      final_registers final_state after.

Definition kernel_call_save_uninterrupted_execution arch registers state before
  final_registers final_state after : Prop :=
  kernel_call_save_instruction_execution arch
    [SaveReadCPSR; SaveMaskIRQFIQ; SaveDataBarrier; SaveBranchLR]
    registers state before final_registers final_state after.

Lemma kernel_call_save_instruction_preserves_kernel :
  forall arch instruction registers state before final_registers final_state after,
  kernel_call_save_instruction_step arch instruction registers state before
    final_registers final_state after ->
  final_state = state /\ after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem).
Proof. intros; destruct H; split; auto. Qed.

Lemma kernel_call_save_instructions_preserve_kernel :
  forall arch instructions registers state before final_registers final_state after,
  kernel_call_save_instruction_execution arch instructions registers state before
    final_registers final_state after ->
  final_state = state /\ after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem).
Proof.
  intros arch instructions registers state before final_registers final_state after Hrun.
  induction Hrun as [registers state heap|instruction instructions registers state before
    middle_registers middle_state middle final_registers final_state after Hstep Htail [Hstate Hmemory]].
  - split; reflexivity.
  - destruct (kernel_call_save_instruction_preserves_kernel _ _ _ _ _ _ _ _ Hstep)
      as [Hfirst Hheap]. split; congruence.
Qed.

(** A genuine producer of the local instruction branch, not a claim that
    interrupts cannot occur. CPU/CSL post ownership is intentionally absent
    here; it cannot be constructed from the bare platform assertion fields. *)
Lemma kernel_call_save_uninterrupted_source : forall arch registers state heap,
  registers.(kernel_save_return_word) = None ->
  a32_maskable_context arch registers.(kernel_save_cpsr) ->
  kernel_call_save_uninterrupted_execution arch registers state heap
    (kernel_save_branch_lr (kernel_save_mask_irq_fiq (kernel_save_read_cpsr registers)))
    state heap.
Proof.
  intros arch registers state heap Hrunning Harch.
  unfold kernel_call_save_uninterrupted_execution.
  econstructor; [constructor; [exact Hrunning|reflexivity]|].
  econstructor; [constructor; [reflexivity|exact Harch|reflexivity]|].
  econstructor; [constructor; reflexivity|].
  econstructor; [constructor; reflexivity|constructor].
Qed.

Lemma kernel_call_save_uninterrupted_return_values :
  forall arch registers state before final_registers final_state after,
  kernel_call_save_uninterrupted_execution arch registers state before
    final_registers final_state after ->
  final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  final_registers.(kernel_save_cpsr) = Z.lor registers.(kernel_save_cpsr) 192 /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr).
Proof.
  intros arch registers state before final_registers final_state after Hrun.
  unfold kernel_call_save_uninterrupted_execution in Hrun.
  inversion Hrun; subst.
  match goal with H : kernel_call_save_instruction_step _ SaveReadCPSR _ _ _ _ _ _ |- _ =>
    inversion H; subst; clear H
  end.
  repeat match goal with
  | H : kernel_call_save_instruction_execution _ (_ :: _) _ _ _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H : kernel_call_save_instruction_step _ _ _ _ _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H : kernel_call_save_instruction_execution _ [] _ _ _ _ _ _ |- _ =>
      inversion H; subst; clear H
  end.
  repeat split; reflexivity.
Qed.

(** The selected non-VFP port stores sixteen words, in address order:
    CPSR, R0..R12, LR, PC. IRQ entry pushes PC/LR, R4..R12, the banked
    R0..R3 and CPSR; the task-level switch pushes its return LR as PC and
    LR. Both restorers pop CPSR, write SPSR, then LDM {R0-R12,LR,PC}^.
    A first-entry image is NOT a suspended C invocation. *)
Record Armv7aContinuation : Type := {
  armv7a_continuation_call : option OsSchedCallContext;
  armv7a_continuation_stack : TaskStackLease;
  armv7a_continuation_sp : Z;
  armv7a_continuation_fragments : TaskStackFragments;
  armv7a_continuation_cpsr : Z;
  armv7a_continuation_registers : list Z;
  armv7a_continuation_lr : Z;
  armv7a_continuation_pc : Z
}.

Definition armv7a_continuation_words (saved : Armv7aContinuation) : list Z :=
  saved.(armv7a_continuation_cpsr) ::
    saved.(armv7a_continuation_registers) ++
    [saved.(armv7a_continuation_lr); saved.(armv7a_continuation_pc)].

Definition armv7a_continuation_binding (saved : Armv7aContinuation) : Prop :=
  List.length saved.(armv7a_continuation_registers) = 13%nat /\
  match saved.(armv7a_continuation_call) with
  | Some call => call.(os_sched_call_stack) = saved.(armv7a_continuation_stack)
  | None => True
  end.

Definition armv7a_continuation_resumed_call (saved : Armv7aContinuation)
  (call : OsSchedCallContext) : OsSchedCallContext :=
  {| os_sched_call_invocation := call.(os_sched_call_invocation);
     os_sched_call_origin := call.(os_sched_call_origin);
     os_sched_call_stack := saved.(armv7a_continuation_stack);
     os_sched_call_fragments := saved.(armv7a_continuation_fragments) |}.

Fixpoint armv7a_frame_word_reads (sp : Z) (words : list Z) (heap : model) : Prop :=
  match words with
  | [] => True
  | word :: rest => pointer_load sp word heap /\ armv7a_frame_word_reads (sp + 4) rest heap
  end.

Definition armv7a_continuation_restore_reads (saved : Armv7aContinuation)
  (heap : model) : Prop :=
  armv7a_continuation_binding saved /\
  armv7a_frame_word_reads saved.(armv7a_continuation_sp)
    (armv7a_continuation_words saved) heap.

Fixpoint armv7a_frame_store_words (address : Z) (words : list Z)
  : list (Mem.addr * Mem.byte) :=
  match words with
  | [] => []
  | word :: rest => pointer_store_writes address word ++
      armv7a_frame_store_words (address + 4) rest
  end.

(** Each STMFD is one instruction. Within its ordinary-memory projection
    the lower-numbered register is stored at the lower address. In
    particular IRQ's R4..R12 group precedes its copied R0..R3 group; this
    is not a fictional sequence of sixteen single-register pushes. *)
Definition armv7a_continuation_save_writes (saved : Armv7aContinuation) :=
  pointer_store_writes (saved.(armv7a_continuation_sp) + 60) saved.(armv7a_continuation_pc) ++
  pointer_store_writes (saved.(armv7a_continuation_sp) + 56) saved.(armv7a_continuation_lr) ++
  armv7a_frame_store_words (saved.(armv7a_continuation_sp) + 20)
    (skipn 4 saved.(armv7a_continuation_registers)) ++
  armv7a_frame_store_words (saved.(armv7a_continuation_sp) + 4)
    (firstn 4 saved.(armv7a_continuation_registers)) ++
  pointer_store_writes saved.(armv7a_continuation_sp) saved.(armv7a_continuation_cpsr).

Lemma armv7a_continuation_words_length : forall saved,
  armv7a_continuation_binding saved -> List.length (armv7a_continuation_words saved) = 16%nat.
Proof.
  intros saved [Hlength Hcall]; unfold armv7a_continuation_words.
  cbn; rewrite List.app_length, Hlength; reflexivity.
Qed.

Lemma armv7a_frame_word_reads_deterministic : forall words other sp heap,
  List.length words = List.length other ->
  armv7a_frame_word_reads sp words heap -> armv7a_frame_word_reads sp other heap -> words = other.
Proof.
  induction words as [|word rest IH]; intros [|value tail] sp heap Hlength Hfirst Hsecond;
    cbn in *; try discriminate; auto.
  destruct Hfirst as [Hword Hrest], Hsecond as [Hvalue Htail].
  assert (word = value) by (eapply pointer_load_deterministic; eassumption).
  f_equal; [assumption|eapply IH; eauto].
Qed.

(** APPROVED EXTERNAL ABI REFINEMENT, not a consequence of the old opaque
    InterruptPlatformResources/OsIntExitPlatformResources records.

    Each law consumes the actual input resources and is indexed by one
    source transition on the SAME model. Save's byte-write projection and
    restore's sixteen loads are mandatory; no pure trace supplies a heap.
    A restoring handler may differ from the depositing handler. Its CPU
    resource is exchanged, never relabelled as the target's CPU token.
    Inactive handler bytes and arbitrary disjoint caller frames survive.
    No law asserts ready/current, eventual return, or an unchanged kernel.

    [None] is reserved for initial entry. Its resource is distinct from a
    suspended call and cannot establish a normal return to an old call. *)
Record Armv7aContinuationABI (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (port : OsIntExitPlatformResources) : Type := {
  armv7a_dormant_continuation : Armv7aContinuation -> Assertion;
  armv7a_initial_execution : Armv7aContinuation -> Assertion;
  armv7a_save_transition : OsIntExitCallContext -> Armv7aContinuation -> model -> model -> Prop;
  armv7a_restore_transition : OsIntExitCallContext -> Armv7aContinuation -> model -> model -> Prop;
  armv7a_save_transition_observations : forall context saved before after,
    armv7a_save_transition context saved before after ->
    port.(os_int_exit_entry_source) context /\
    saved.(armv7a_continuation_call) = Some context.(os_int_exit_interrupted_call) /\
    armv7a_continuation_binding saved /\
    armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) = context.(os_int_exit_interrupted_mask) /\
    saved.(armv7a_continuation_pc) = context.(os_int_exit_interrupted_pc) /\
    saved.(armv7a_continuation_sp) = context.(os_int_exit_interrupted_sp) /\
    saved.(armv7a_continuation_fragments) = context.(os_int_exit_interrupted_fragments);
  armv7a_save_transition_resources : forall context saved call (frame : Assertion) before after,
    saved.(armv7a_continuation_call) = Some call ->
    call = context.(os_int_exit_interrupted_call) ->
    armv7a_continuation_binding saved ->
    armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) = context.(os_int_exit_interrupted_mask) ->
    saved.(armv7a_continuation_pc) = context.(os_int_exit_interrupted_pc) ->
    saved.(armv7a_continuation_sp) = context.(os_int_exit_interrupted_sp) ->
    saved.(armv7a_continuation_fragments) = context.(os_int_exit_interrupted_fragments) ->
    (os_int_exit_frame_save_pre external platform context ** frame) before ->
    armv7a_save_transition context saved before after ->
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) after.(ConAssertion.s_mem) /\
    (interrupt_platform_running platform context.(os_int_exit_invocation)
       context.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port context **
     task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) **
     armv7a_dormant_continuation saved ** frame) after;
  armv7a_restore_transition_resources : forall context saved (frame : Assertion) before after,
    armv7a_continuation_restore_reads saved before ->
    (interrupt_platform_running platform context.(os_int_exit_invocation)
       context.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port context **
     task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) **
     armv7a_dormant_continuation saved ** frame) before ->
    armv7a_restore_transition context saved before after ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
    ((match saved.(armv7a_continuation_call) with
      | Some call => kernel_call_execution_owned external platform
          (armv7a_continuation_resumed_call saved call)
          (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr))
      | None => armv7a_initial_execution saved **
          task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
            saved.(armv7a_continuation_fragments)
      end) **
     task_stack_fragments_rep context.(os_int_exit_handler_stack)
       context.(os_int_exit_handler_fragments) ** frame) after
}.

Arguments armv7a_dormant_continuation {external platform port} _ _.
Arguments armv7a_initial_execution {external platform port} _ _.
Arguments armv7a_save_transition {external platform port} _ _ _ _ _.
Arguments armv7a_restore_transition {external platform port} _ _ _ _ _.

(** A pending source call is identified by more than its task slot. The
    invocation/origin and exact saved PC/LR remain part of the parked
    resource, so taking another descriptor with the same task key cannot
    establish a return to this call. *)
Record Armv7aCallFocus : Type := {
  armv7a_focus_call : OsSchedCallContext;
  armv7a_focus_pc : Z;
  armv7a_focus_lr : Z
}.

Definition armv7a_call_focus (call : OsSchedCallContext) (pc lr : Z) : Armv7aCallFocus :=
  {| armv7a_focus_call := call; armv7a_focus_pc := pc; armv7a_focus_lr := lr |}.

Definition armv7a_call_focus_key (focus : Armv7aCallFocus) : TaskID * nat :=
  task_stack_key focus.(armv7a_focus_call).(os_sched_call_stack).

Definition armv7a_continuation_focus_binding (focus : Armv7aCallFocus)
  (saved : Armv7aContinuation) : Prop :=
  saved.(armv7a_continuation_call) = Some focus.(armv7a_focus_call) /\
  saved.(armv7a_continuation_pc) = focus.(armv7a_focus_pc) /\
  saved.(armv7a_continuation_lr) = focus.(armv7a_focus_lr).

Definition armv7a_continuation_entry {external platform port}
  (abi : Armv7aContinuationABI external platform port) (focus : Armv7aCallFocus)
  (key : TaskID * nat) (payload : TaskStackRegion * TaskStackFragments) : Assertion :=
  EX saved,
    coq_prop (armv7a_continuation_binding saved /\
      armv7a_continuation_focus_binding focus saved /\
      task_stack_key saved.(armv7a_continuation_stack) = key /\
      (saved.(armv7a_continuation_stack).(stackLeaseRegion),
        saved.(armv7a_continuation_fragments)) = payload) &&
    armv7a_dormant_continuation abi saved.

(** Focus one suspended invocation. Foreign keys carry [emp], NOT an
    invented initial/foreign execution capability. This is still the same
    existing stack map, not an independently mutable side ledger. *)
Definition armv7a_parked_continuation_entry {external platform port}
  (abi : Armv7aContinuationABI external platform port) (focus : Armv7aCallFocus)
  (key : TaskID * nat)
  (payload : TaskStackRegion * TaskStackFragments) : Assertion :=
  if task_stack_key_eq_dec key (armv7a_call_focus_key focus)
  then armv7a_continuation_entry abi focus key payload else emp.

Definition armv7a_parked_continuations {external platform port}
  (abi : Armv7aContinuationABI external platform port) (focus : Armv7aCallFocus)
  (state : UCOS2_Verify_State) : Assertion :=
  store_parked_continuations (armv7a_parked_continuation_entry abi focus)
    state.(TskState).(parkedTaskStacks).

(** Parameterized by the actual shared assertion: selected/full validity
    and source-client certificates are separate obligations. The extension
    owns no duplicate stack bytes, and is never inferred from the old raw
    invariant or from a CPU token. *)
Definition armv7a_continuation_world {external platform port}
  (abi : Armv7aContinuationABI external platform port)
  (focus : Armv7aCallFocus)
  (shared : UCOS2_Verify_State -> Assertion) (state : UCOS2_Verify_State) : Assertion :=
  shared state ** armv7a_parked_continuations abi focus state.

Lemma armv7a_dormant_continuation_entry : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus saved,
  task_stack_key saved.(armv7a_continuation_stack) = armv7a_call_focus_key focus ->
  armv7a_continuation_focus_binding focus saved ->
  armv7a_continuation_binding saved ->
  armv7a_dormant_continuation abi saved |--
  armv7a_parked_continuation_entry abi focus
    (task_stack_key saved.(armv7a_continuation_stack))
    (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments)).
Proof.
  intros external platform port abi focus saved Hfocus Hfocused Hbinding.
  unfold armv7a_parked_continuation_entry.
  destruct task_stack_key_eq_dec; [|contradiction].
  unfold armv7a_continuation_entry; Exists saved; entailer!.
Qed.

(** A spatial deposit at the actual post-counter/post-TCB-SP cut. The
    already produced dormant resource goes INTO the map, not into an
    unrelated wrapper frame. The same saved bytes are owned exactly once. *)
Lemma armv7a_park_saved_continuation : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus sg state saved call,
  task_stack_key saved.(armv7a_continuation_stack) = armv7a_call_focus_key focus ->
  armv7a_continuation_focus_binding focus saved ->
  armv7a_continuation_call saved = Some call ->
  armv7a_continuation_binding saved ->
  os_sched_saved_stack_binding call saved.(armv7a_continuation_fragments) state ->
  task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
    saved.(armv7a_continuation_fragments) **
  armv7a_dormant_continuation abi saved **
  armv7a_continuation_world abi focus (UCOS2_inv sg) state |--
  armv7a_continuation_world abi focus (UCOS2_inv sg)
    (replace_TskS (glob_task_set_parked_stacks state.(TskState)
      (task_stack_park_fragments state.(TskState).(parkedTaskStacks)
        saved.(armv7a_continuation_stack) saved.(armv7a_continuation_fragments))) state).
Proof.
  intros external platform port abi focus sg state saved call Hfocus Hfocused Hcall Hbinding Hsaved.
  pose proof Hbinding as [_ Hstack]; rewrite Hcall in Hstack.
  assert (Hnone : state.(TskState).(parkedTaskStacks)
    (task_stack_key saved.(armv7a_continuation_stack)) = None).
  { rewrite <- Hstack; unfold os_sched_saved_stack_binding in Hsaved; tauto. }
  unfold armv7a_continuation_world, armv7a_parked_continuations.
  rewrite UCOS2_inv_split_parked_stacks; Intros.
  assert (Hvalid : UCOS2_state_inv sg state) by assumption.
  assert (Hconsistent : parked_stacks_consistent state.(TskState)
    (task_stack_park_fragments state.(TskState).(parkedTaskStacks)
      saved.(armv7a_continuation_stack) saved.(armv7a_continuation_fragments))).
  { rewrite <- Hstack; eapply os_sched_park_saved_context_preserves_consistency;
      [|exact Hsaved].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  sep_apply_l_atomic (armv7a_dormant_continuation_entry _ _ _ abi focus saved Hfocus Hfocused Hbinding).
  sep_apply_l_atomic (store_parked_continuations_park
    (armv7a_parked_continuation_entry abi focus) state.(TskState).(parkedTaskStacks)
    saved.(armv7a_continuation_stack) saved.(armv7a_continuation_fragments) Hnone).
  sep_apply_l_atomic (store_parked_stacks_park_fragments state.(TskState).(parkedTaskStacks)
    saved.(armv7a_continuation_stack) saved.(armv7a_continuation_fragments) Hnone).
  sep_apply_l_atomic (UCOS2_inv_merge_updated_parked_stacks sg state _ Hvalid Hconsistent).
  cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks]; entailer!.
Qed.

(** Unlike the old opaque [os_int_exit_transferred], this consumer obtains
    the capsule from the actual selected entry. The post-hook SP load and
    cache stores are the previously checked memory fragment; the disjoint
    resource map is carried on that SAME changing model. *)
Lemma armv7a_install_take_continuation : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus sg transfer (frame : Assertion) heap,
  os_int_exit_destination_binding external transfer ->
  task_stack_key transfer.(os_int_exit_incoming_stack) = armv7a_call_focus_key focus ->
  tcb_field_address (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  (armv7a_continuation_world abi focus (UCOS2_inv sg) transfer.(os_int_exit_hooked_state) ** frame) heap ->
  exists final saved,
    sched_install_heap_fragment sg heap final
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      transfer.(os_int_exit_incoming_sp) /\
    armv7a_continuation_binding saved /\
    armv7a_continuation_focus_binding focus saved /\
    saved.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) /\
    saved.(armv7a_continuation_fragments) = transfer.(os_int_exit_incoming_fragments) /\
    task_current_at (os_int_exit_installed_state transfer)
      saved.(armv7a_continuation_stack).(stackLeaseSlot)
      saved.(armv7a_continuation_stack).(stackLeaseGeneration) /\
    (armv7a_continuation_world abi focus (UCOS2_inv sg) (os_int_exit_installed_state transfer) **
     task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved ** frame) final.
Proof.
  intros external platform port abi focus sg transfer frame heap Hdestination Hfocus Haddress Hbefore.
  pose proof Hdestination as [_ [_ [_ [Hparked Harch]]]].
  assert (Hsplit : armv7a_continuation_world abi focus (UCOS2_inv sg)
      transfer.(os_int_exit_hooked_state) ** frame |--
    UCOS2_inv sg transfer.(os_int_exit_hooked_state) **
      (armv7a_parked_continuations abi focus transfer.(os_int_exit_hooked_state) ** frame)).
  { unfold armv7a_continuation_world; entailer!. }
  destruct (os_int_exit_install_heap_take_destination_frame external sg transfer _ heap
    Hdestination Haddress (Hsplit heap Hbefore)) as [final [Hrun [[Hcurrent Hrestore] Hafter]]].
  assert (Htake : UCOS2_inv sg (os_int_exit_installed_state transfer) **
      task_stack_fragments_rep transfer.(os_int_exit_incoming_stack).(stackLeaseRegion)
        transfer.(os_int_exit_incoming_fragments) **
      (armv7a_parked_continuations abi focus transfer.(os_int_exit_hooked_state) ** frame) |--
    EX saved,
      coq_prop (armv7a_continuation_binding saved /\
        armv7a_continuation_focus_binding focus saved /\
        saved.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) /\
        saved.(armv7a_continuation_fragments) = transfer.(os_int_exit_incoming_fragments)) &&
      (armv7a_continuation_world abi focus (UCOS2_inv sg) (os_int_exit_installed_state transfer) **
       task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
         saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved ** frame)).
  { unfold armv7a_parked_continuations.
    sep_apply_l_atomic (store_parked_continuations_take
      (armv7a_parked_continuation_entry abi focus) _ _ _ Hparked).
    unfold armv7a_parked_continuation_entry.
    destruct task_stack_key_eq_dec; [|contradiction].
    unfold armv7a_continuation_entry; Intros saved.
    assert (Hkey : task_stack_key saved.(armv7a_continuation_stack) =
      task_stack_key transfer.(os_int_exit_incoming_stack)) by tauto.
    assert (Hpayload : (saved.(armv7a_continuation_stack).(stackLeaseRegion),
      saved.(armv7a_continuation_fragments)) =
      (transfer.(os_int_exit_incoming_stack).(stackLeaseRegion),
       transfer.(os_int_exit_incoming_fragments))) by tauto.
    assert (Hstack : saved.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack)).
    { unfold task_stack_key in Hkey.
      destruct saved.(armv7a_continuation_stack), transfer.(os_int_exit_incoming_stack);
        cbn in *; congruence. }
    assert (Hfragments : saved.(armv7a_continuation_fragments) =
      transfer.(os_int_exit_incoming_fragments)) by congruence.
    Exists saved; unfold armv7a_continuation_world, armv7a_parked_continuations,
      os_int_exit_installed_state.
    cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
    rewrite Hstack, Hfragments; entailer!. }
  destruct (Htake final Hafter) as [saved [[Hbinding [Hfocused [Hstack Hfragments]]] Hresources]].
  exists final, saved; split; [exact Hrun|]. split; [exact Hbinding|].
  split; [exact Hfocused|]. split; [exact Hstack|]. split; [exact Hfragments|].
  split; [rewrite Hstack; exact Hcurrent|exact Hresources].
Qed.

(** This is the consumer of a selected take, after the real frame loads.
    The dormant call can have been deposited by any earlier handler. An
    initial-entry capsule cannot satisfy [Hcall]. This theorem grants no
    running resource unless the ABI actually consumes the selected capsule
    and the currently executing handler on its restore transition. *)
Lemma armv7a_restore_call_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) handler saved call
  (shared : Assertion) before after,
  saved.(armv7a_continuation_call) = Some call ->
  armv7a_continuation_restore_reads saved before ->
  (interrupt_platform_running platform handler.(os_int_exit_invocation)
     handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
   task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
     saved.(armv7a_continuation_fragments) **
   armv7a_dormant_continuation abi saved ** shared) before ->
  armv7a_restore_transition abi handler saved before after ->
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (kernel_call_execution_owned external platform
     (armv7a_continuation_resumed_call saved call)
     (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack)
     handler.(os_int_exit_handler_fragments) ** shared) after.
Proof.
  intros external platform port abi handler saved call shared before after Hcall Hreads Hpre Hrun.
  pose proof (armv7a_restore_transition_resources _ _ _ abi handler saved shared
    before after Hreads Hpre Hrun) as Hpost.
  rewrite Hcall in Hpost; exact Hpost.
Qed.

Definition kernel_save_after_mrs_execution arch registers state before final_registers final_state after :=
  kernel_call_save_instruction_execution arch
    [SaveMaskIRQFIQ; SaveDataBarrier; SaveBranchLR]
    registers state before final_registers final_state after.

Lemma kernel_save_after_mrs_return_values : forall arch registers state before final_registers final_state after,
  kernel_save_after_mrs_execution arch registers state before final_registers final_state after ->
  final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
  final_registers.(kernel_save_cpsr) = Z.lor registers.(kernel_save_cpsr) 192 /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr).
Proof.
  intros arch registers state before final_registers final_state after Hrun.
  unfold kernel_save_after_mrs_execution in Hrun.
  repeat match goal with
  | H : kernel_call_save_instruction_execution _ (_ :: _) _ _ _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H : kernel_call_save_instruction_step _ _ _ _ _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H : kernel_call_save_instruction_execution _ [] _ _ _ _ _ _ |- _ =>
      inversion H; subst; clear H
  end.
  repeat split; reflexivity.
Qed.

(** The CPU/CSL exchange of the actual, locally masked suffix. This is
    another explicit part of the approved external ABI, not a proof of the
    ARM implementation. The source relation has CPSID -> DSB -> BX LR and
    the resource law consumes running ownership. It does NOT assert that a
    whole Save has no interrupts; all interruptions before CPSID must have
    returned the original saved cursor before this suffix can execute.

    The arbitrary [frame] is the same caller-owned resource on this one
    execution; a full-profile heap or borrowed PendMulti arrays need no
    selected-profile conversion. No invariant, liveness or current-pointer
    fact is produced by this CPU resource exchange. *)
Record Armv7aSaveSuffixABI (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (arch : A32InterruptContext) : Type := {
  armv7a_save_entry_address : Z;
  armv7a_save_suffix_transition : KernelSaveRegisters -> UCOS2_Verify_State -> model ->
    KernelSaveRegisters -> UCOS2_Verify_State -> model -> Prop;
  armv7a_save_suffix_source : forall registers state before final_registers final_state after,
    armv7a_save_suffix_transition registers state before final_registers final_state after ->
    kernel_save_after_mrs_execution arch registers state before final_registers final_state after;
  armv7a_save_suffix_resources : forall sg call registers state before final_registers final_state after
      (frame : Assertion),
    interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
    (kernel_call_execution_owned external platform call
       (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) ** frame) before ->
    armv7a_save_suffix_transition registers state before final_registers final_state after ->
    (critical_region_masked platform critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) final_registers.(kernel_save_r0) final_state **
     os_sched_context_resources external call ** frame) after
}.

Arguments armv7a_save_suffix_transition {external platform critical arch} _ _ _ _ _ _ _.
Arguments armv7a_save_entry_address {external platform critical arch} _.

Lemma armv7a_save_suffix_preserves_source_heap : forall external platform critical arch
  (abi : Armv7aSaveSuffixABI external platform critical arch)
  sg call registers state before final_registers final_state after (frame : Assertion),
  interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
  (kernel_call_execution_owned external platform call
     (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) ** frame) before ->
  armv7a_save_suffix_transition abi registers state before final_registers final_state after ->
  final_state = state /\ after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
   os_sched_context_resources external call ** frame) after.
Proof.
  intros external platform critical arch abi sg call registers state before
    final_registers final_state after frame Hsaved Hpre Hrun.
  pose proof (armv7a_save_suffix_source _ _ _ _ abi _ _ _ _ _ _ Hrun) as Hsource.
  destruct (kernel_call_save_instructions_preserve_kernel _ _ _ _ _ _ _ _ Hsource)
    as [Hstate Hmemory].
  destruct (kernel_save_after_mrs_return_values _ _ _ _ _ _ _ Hsource) as [Hr0 [Hcpsr Hlr]].
  pose proof (armv7a_save_suffix_resources _ _ _ _ abi sg call registers state before
    final_registers final_state after frame Hsaved Hpre Hrun) as Hpost.
  subst final_state; repeat split; assumption || reflexivity.
Qed.

(** Last restored CPSID cursor of a normally returning Save.  The
    registered source edge and the owned continuation are consumed at the
    same acquired state.  Earlier tasks/IRQs may have run; before is not
    equated with acquired.  This theorem does not supply the prefix heap,
    a destination frame, ready membership, or a new OS fact from the ABI. *)
Lemma armv7a_restored_save_returns_owned_source :
  forall external platform port critical arch
    (continuations : Armv7aContinuationABI external platform port)
    (suffix : Armv7aSaveSuffixABI external platform critical arch)
    sg handler saved original mask before acquired registers heap restored
    final_registers final_state after (frame : Assertion),
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  saved.(armv7a_continuation_call) = Some original ->
  saved.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 ->
  registers.(kernel_save_cpsr) = saved.(armv7a_continuation_cpsr) ->
  registers.(kernel_save_r0) = nth 0 saved.(armv7a_continuation_registers) 0 ->
  registers.(kernel_save_lr) = saved.(armv7a_continuation_lr) ->
  interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
  kernel_call_save_source external port critical sg original
    (armv7a_continuation_resumed_call saved original) mask registers.(kernel_save_r0)
    before acquired ->
  armv7a_continuation_restore_reads saved heap ->
  (interrupt_platform_running platform handler.(os_int_exit_invocation)
     handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
   task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
     saved.(armv7a_continuation_fragments) **
   armv7a_dormant_continuation continuations saved ** (UCOS2_inv sg acquired ** frame)) heap ->
  armv7a_restore_transition continuations handler saved heap restored ->
  armv7a_save_suffix_transition suffix registers acquired restored
    final_registers final_state after ->
  final_state = acquired /\
  final_registers.(kernel_save_return_word) = Some saved.(armv7a_continuation_lr) /\
  kernel_call_save_source external port critical sg original
    (armv7a_continuation_resumed_call saved original) mask final_registers.(kernel_save_r0)
    before final_state /\
  kernel_call_task_source (armv7a_continuation_resumed_call saved original) final_state /\
  (critical_region_masked platform critical sg original.(os_sched_call_invocation)
     original.(os_sched_call_origin) final_registers.(kernel_save_r0) final_state **
   os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
   UCOS2_inv sg final_state **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack)
     handler.(os_int_exit_handler_fragments) ** frame) after.
Proof.
  intros external platform port critical arch continuations suffix sg handler saved original
    mask before acquired registers heap restored final_registers final_state after frame
    Hvalid Hcaller Hcall Hcursor Hcpsr Hr0 Hlr Hsaved Hsource Hreads Hpre Hrestore Hsuffix.
  destruct (armv7a_restore_call_resources external platform port continuations
    handler saved original (UCOS2_inv sg acquired ** frame) heap restored
    Hcall Hreads Hpre Hrestore) as [Hmemory Hrestored].
  assert (Hinput : (kernel_call_execution_owned external platform
    (armv7a_continuation_resumed_call saved original)
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** (UCOS2_inv sg acquired ** frame))) restored).
  { rewrite Hcpsr.
    assert (Hassoc : forall p q r : Assertion, p ** q ** r |-- p ** (q ** r))
      by (intros; entailer!).
    exact (Hassoc _ _ _ restored Hrestored). }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix
    sg (armv7a_continuation_resumed_call saved original) registers acquired restored
    final_registers final_state after _ Hsaved Hinput Hsuffix)
    as [Hstate [Hheap [Hreturn [Hvalue Hpost]]]].
  subst final_state; split; [reflexivity|]. split; [rewrite <- Hlr; exact Hreturn|].
  split; [rewrite Hvalue; exact Hsource|]. split.
  - eapply kernel_call_save_source_preserves_task_source; eassumption.
  - assert (Horder : critical_region_masked platform critical sg
      (armv7a_continuation_resumed_call saved original).(os_sched_call_invocation)
      (armv7a_continuation_resumed_call saved original).(os_sched_call_origin)
      final_registers.(kernel_save_r0) acquired **
      os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** (UCOS2_inv sg acquired ** frame)) |--
      critical_region_masked platform critical sg original.(os_sched_call_invocation)
        original.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
      os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
      UCOS2_inv sg acquired ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** frame).
    { cbn [armv7a_continuation_resumed_call os_sched_call_invocation os_sched_call_origin]; entailer!. }
    exact (Horder after Hpost).
Qed.

(** The ordinary wrapper reads current/SP and takes that exact parked key;
    unlike OSIntCtxSw it performs no current-cache stores. The current
    binding is a source-cut premise, not inferred from stale priority bytes. *)
Lemma armv7a_wrapper_take_continuation : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus sg state incoming fragments
  node (frame : Assertion) heap,
  state.(SchedState).(curTaskID) = Some incoming.(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node ->
  state.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), fragments) ->
  task_stack_key incoming = armv7a_call_focus_key focus ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (armv7a_continuation_world abi focus (UCOS2_inv sg) state ** frame) heap ->
  armv7a_irq_restore_pointer_reads sg heap (task_slot_addr sg incoming.(stackLeaseSlot)) node.(tcbStkPtr) /\
  exists saved,
    armv7a_continuation_binding saved /\ armv7a_continuation_focus_binding focus saved /\
    saved.(armv7a_continuation_stack) = incoming /\
    saved.(armv7a_continuation_fragments) = fragments /\
    (armv7a_continuation_world abi focus (UCOS2_inv sg)
       (os_int_exit_wrapper_restored_state state incoming) **
     task_stack_fragments_rep incoming.(stackLeaseRegion) fragments **
     armv7a_dormant_continuation abi saved ** frame) heap.
Proof.
  intros external platform port abi focus sg state incoming fragments node frame heap
    Hcurrent Hnode Hparked Hfocus Haddress Hpre.
  assert (Hsplit : armv7a_continuation_world abi focus (UCOS2_inv sg) state ** frame |--
    UCOS2_inv sg state ** (armv7a_parked_continuations abi focus state ** frame)).
  { unfold armv7a_continuation_world; entailer!. }
  pose proof (Hsplit heap Hpre) as Hworld.
  split.
  - destruct Hworld as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
    eapply armv7a_irq_restore_pointer_reads_frame; [|exact Hjoin].
    eapply armv7a_irq_restore_pointer_reads_live; eassumption.
  - assert (Htake : UCOS2_inv sg state ** (armv7a_parked_continuations abi focus state ** frame) |--
      EX saved,
      coq_prop (armv7a_continuation_binding saved /\ armv7a_continuation_focus_binding focus saved /\
        saved.(armv7a_continuation_stack) = incoming /\
        saved.(armv7a_continuation_fragments) = fragments) &&
      (armv7a_continuation_world abi focus (UCOS2_inv sg)
         (os_int_exit_wrapper_restored_state state incoming) **
       task_stack_fragments_rep incoming.(stackLeaseRegion) fragments **
       armv7a_dormant_continuation abi saved ** frame)).
    { sep_apply_l_atomic (os_int_exit_wrapper_take_destination_resources sg state incoming fragments Hparked).
      unfold armv7a_parked_continuations.
      sep_apply_l_atomic (store_parked_continuations_take
        (armv7a_parked_continuation_entry abi focus) _ _ _ Hparked).
      unfold armv7a_parked_continuation_entry.
      destruct task_stack_key_eq_dec; [|contradiction].
      unfold armv7a_continuation_entry; Intros saved.
      assert (Hkey : task_stack_key saved.(armv7a_continuation_stack) = task_stack_key incoming) by tauto.
      assert (Hpayload : (saved.(armv7a_continuation_stack).(stackLeaseRegion),
        saved.(armv7a_continuation_fragments)) = (incoming.(stackLeaseRegion), fragments)) by tauto.
      assert (Hstack : saved.(armv7a_continuation_stack) = incoming).
      { unfold task_stack_key in Hkey; destruct saved.(armv7a_continuation_stack), incoming;
          cbn in *; congruence. }
      assert (Hfragments : saved.(armv7a_continuation_fragments) = fragments) by congruence.
      Exists saved; unfold armv7a_continuation_world, armv7a_parked_continuations,
        os_int_exit_wrapper_restored_state.
      cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks]; entailer!. }
    destruct (Htake heap Hworld) as [saved [[Hbinding [Hfocused [Hstack Hfragments]]] Howned]].
    exists saved; split; [exact Hbinding|]. split; [exact Hfocused|].
    split; [exact Hstack|]. split; assumption.
Qed.

(** The real same-priority branch preserves the focused saved capability
    across its counter/high-cache writes. The unmap table is owned once and
    transported on this execution, not appended as an unrelated endpoint. *)
Lemma armv7a_irq_same_priority_keeps_parked_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus sg state
  (frame : Assertion) heap,
  state.(SchedState).(isRunning) = true ->
  interrupt_exit_requests_schedule true state.(IntrState) = true ->
  state.(SchedState).(readyList) <> nil ->
  sched_selected_priority state.(TskState) state.(SchedState) =
    sched_priority_byte state.(SchedState).(curSchedPrio) ->
  (armv7a_continuation_world abi focus (UCOS2_inv sg) state ** unmap_table_rep sg ** frame) heap ->
  exists final, os_int_exit_masked_same_priority_fragment sg heap final /\
    (armv7a_continuation_world abi focus (UCOS2_inv sg)
       (os_int_exit_same_priority_state state) ** unmap_table_rep sg ** frame) final.
Proof.
  intros external platform port abi focus sg state frame heap Hrunning Hschedule Hnonempty Hequal Hpre.
  assert (Hsplit : armv7a_continuation_world abi focus (UCOS2_inv sg) state **
      unmap_table_rep sg ** frame |--
    UCOS2_inv sg state ** unmap_table_rep sg **
      (armv7a_parked_continuations abi focus state ** frame)).
  { unfold armv7a_continuation_world; entailer!. }
  destruct (os_int_exit_masked_same_priority_frame_post sg state _ heap
    Hrunning Hschedule Hnonempty Hequal (Hsplit heap Hpre)) as [final [Hsource Hafter]].
  exists final; split; [exact Hsource|].
  assert (Hmerge : UCOS2_inv sg (os_int_exit_same_priority_state state) ** unmap_table_rep sg **
      (armv7a_parked_continuations abi focus state ** frame) |--
    armv7a_continuation_world abi focus (UCOS2_inv sg)
      (os_int_exit_same_priority_state state) ** unmap_table_rep sg ** frame).
  { unfold armv7a_continuation_world, armv7a_parked_continuations,
      os_int_exit_same_priority_state, os_int_exit_selection_state,
      os_int_exit_counter_state; cbn [replace_SchedS replace_IntrS TskState]; entailer!. }
  exact (Hmerge final Hafter).
Qed.

(** Counter and selection writes, then the wrapper's actual current/SP
    reads and one linear take. The descriptor is extracted from the saved
    owner, not supplied as an independent acquired-frame assertion. *)
Lemma armv7a_irq_same_priority_takes_continuation : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus sg state incoming fragments
  node (frame : Assertion) heap,
  state.(SchedState).(isRunning) = true ->
  interrupt_exit_requests_schedule true state.(IntrState) = true ->
  state.(SchedState).(readyList) <> nil ->
  sched_selected_priority state.(TskState) state.(SchedState) =
    sched_priority_byte state.(SchedState).(curSchedPrio) ->
  state.(SchedState).(curTaskID) = Some incoming.(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node ->
  state.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), fragments) ->
  task_stack_key incoming = armv7a_call_focus_key focus ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (armv7a_continuation_world abi focus (UCOS2_inv sg) state ** unmap_table_rep sg ** frame) heap ->
  exists final saved,
    os_int_exit_masked_same_priority_fragment sg heap final /\
    armv7a_irq_restore_pointer_reads sg final (task_slot_addr sg incoming.(stackLeaseSlot)) node.(tcbStkPtr) /\
    armv7a_continuation_binding saved /\ armv7a_continuation_focus_binding focus saved /\
    saved.(armv7a_continuation_stack) = incoming /\
    saved.(armv7a_continuation_fragments) = fragments /\
    (armv7a_continuation_world abi focus (UCOS2_inv sg)
       (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state state) incoming) **
     task_stack_fragments_rep incoming.(stackLeaseRegion) fragments **
     armv7a_dormant_continuation abi saved ** (unmap_table_rep sg ** frame)) final.
Proof.
  intros external platform port abi focus sg state incoming fragments node frame heap
    Hrunning Hschedule Hnonempty Hequal Hcurrent Hnode Hparked Hfocus Haddress Hpre.
  destruct (armv7a_irq_same_priority_keeps_parked_call external platform port abi focus
    sg state frame heap Hrunning Hschedule Hnonempty Hequal Hpre) as [final [Hrun Hafter]].
  assert (Horder : armv7a_continuation_world abi focus (UCOS2_inv sg)
      (os_int_exit_same_priority_state state) ** unmap_table_rep sg ** frame |--
    armv7a_continuation_world abi focus (UCOS2_inv sg)
      (os_int_exit_same_priority_state state) ** (unmap_table_rep sg ** frame)) by entailer!.
  destruct (armv7a_wrapper_take_continuation external platform port abi focus sg
    (os_int_exit_same_priority_state state) incoming fragments node _ final
    Hcurrent Hnode Hparked Hfocus Haddress (Horder final Hafter))
    as [Hreads [saved [Hbinding [Hfocused [Hstack [Hfragments Howned]]]]]].
  exists final, saved; split; [exact Hrun|]. split; [exact Hreads|].
  split; [exact Hbinding|]. split; [exact Hfocused|]. split; [exact Hstack|].
  split; assumption.
Qed.

(** The empty parked owner is constructed at boot; there is no rule
    upgrading an arbitrary pre-existing byte map into continuation rights. *)
Lemma armv7a_parked_continuations_empty : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus,
  emp |-- store_parked_continuations (armv7a_parked_continuation_entry abi focus)
    (fun _ => None).
Proof.
  intros; unfold store_parked_continuations, store_map.
  Exists (@nil (TaskID * nat)); simpl; entailer!.
  - apply List.NoDup_nil.
  - intros key; split; [contradiction|intros [entry Hentry]; discriminate].
Qed.

(** An absent focused key needs no capsule. The proof only adds [emp] at
    the existing foreign entries and preserves every physical byte. This
    is the usable closed-entry producer for an already running invocation;
    it does NOT turn [key=None] into a dormant or running resource. *)
Lemma armv7a_parked_focus_absent_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus stacks,
  stacks (armv7a_call_focus_key focus) = None ->
  store_parked_stacks stacks |--
    store_parked_stacks stacks **
    store_parked_continuations (armv7a_parked_continuation_entry abi focus) stacks.
Proof.
  intros external platform port abi focus stacks Hnone.
  unfold store_parked_stacks, store_parked_continuations.
  rewrite <- (TaskFieldStorage.store_map_sepcon _ _ task_stack_map_entry
    (armv7a_parked_continuation_entry abi focus) stacks).
  apply TaskFieldStorage.store_map_mono; intros key payload Hentry.
  unfold armv7a_parked_continuation_entry.
  destruct task_stack_key_eq_dec as [Hequal|Hother].
  - subst key; congruence.
  - entailer!.
Qed.

Lemma armv7a_continuation_world_open_absent : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus sg state,
  state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = None ->
  UCOS2_inv sg state |-- armv7a_continuation_world abi focus (UCOS2_inv sg) state.
Proof.
  intros external platform port abi focus sg state Hnone.
  unfold armv7a_continuation_world, armv7a_parked_continuations.
  rewrite UCOS2_inv_split_parked_stacks; Intros.
  intros heap [owned [rest [Hjoin [Howned Hrest]]]].
  pose proof (armv7a_parked_focus_absent_resources external platform port
    abi focus state.(TskState).(parkedTaskStacks) Hnone owned Howned) as Hextended.
  assert (Hresources : ((store_parked_stacks state.(TskState).(parkedTaskStacks) **
    store_parked_continuations (armv7a_parked_continuation_entry abi focus)
      state.(TskState).(parkedTaskStacks)) **
    UCOS2_raw_rep_missing_parked_stacks sg state) heap).
  { exists owned, rest; split; [exact Hjoin|]; split; assumption. }
  clear Hjoin Howned Hrest Hextended owned rest.
  revert heap Hresources.
  match goal with |- forall m : model, ?P m -> ?Q m => change (P |-- Q) end.
  entailer!.
Qed.

Lemma armv7a_parked_focus_absent_emp : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus stacks,
  stacks (armv7a_call_focus_key focus) = None ->
  store_parked_continuations (armv7a_parked_continuation_entry abi focus) stacks |-- emp.
Proof.
  intros external platform port abi focus stacks Hnone.
  unfold store_parked_continuations, store_map; Intros keys.
  assert (Hempty : store_map (armv7a_parked_continuation_entry abi focus) stacks --||-- emp).
  { apply store_map_empty.
    - exists keys; tauto.
    - intros key; destruct (stacks key) as [payload|] eqn:Hentry.
      + right; intros other Hother; unfold armv7a_parked_continuation_entry.
        destruct task_stack_key_eq_dec as [Hequal|Hdifferent].
        * subst key; congruence.
        * split; reflexivity.
      + left; reflexivity. }
  intros heap Hheap; apply (proj1 Hempty heap); revert heap Hheap.
  match goal with |- forall m : model, ?P m -> ?Q m => change (P |-- Q) end.
  unfold store_map; Exists keys; entailer!.
Qed.

(** This normal-return fact is already part of the real OS_Sched source
    contract: the original stack has been taken out of the parked map.
    It is not claimed for bootstrap or an arbitrary valid-state caller. *)
Lemma os_sched_switched_return_opens_continuation_focus :
  forall external platform port critical (abi : Armv7aContinuationABI external platform port)
    sg selected original returned final pc lr,
  os_sched_requests_switch selected = true ->
  os_sched_c_return external critical sg selected original returned final ->
  UCOS2_inv sg final |-- armv7a_continuation_world abi
    (armv7a_call_focus returned pc lr) (UCOS2_inv sg) final.
Proof.
  intros external platform port critical abi sg selected original returned final pc lr Hswitch Hreturn.
  unfold os_sched_c_return in Hreturn; rewrite Hswitch in Hreturn.
  destruct Hreturn as [installed [Hsource [Htrace [Harch [Hi [Ho [Hs
    [Hactive [Hcurrent Hparked]]]]]]]]].
  apply armv7a_continuation_world_open_absent.
  change (final.(TskState).(parkedTaskStacks)
    (task_stack_key returned.(os_sched_call_stack)) = None).
  rewrite Hs; exact Hparked.
Qed.

(** Existing real counter/SP memory producer, now depositing the issued
    continuation beside the exact bytes. The carried map and arbitrary
    caller frame are framed across actual writes, not regenerated from the
    pure after-state. The return resource need not remain with this ISR. *)
Lemma armv7a_irq_entry_deposits_continuation : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  focus sg entry node saved call publication (frame : Assertion) heap,
  task_stack_key saved.(armv7a_continuation_stack) = armv7a_call_focus_key focus ->
  armv7a_continuation_focus_binding focus saved ->
  saved.(armv7a_continuation_call) = Some call ->
  armv7a_continuation_binding saved ->
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    saved.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    saved.(armv7a_continuation_sp) ->
  (armv7a_continuation_world abi focus (UCOS2_inv sg) entry **
   task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
     saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved ** frame) heap ->
  exists final,
    kernel_heap_execution
      (armv7a_irq_live_entry_writes sg entry call.(os_sched_call_stack).(stackLeaseSlot)
        saved.(armv7a_continuation_sp)) heap final /\
    (armv7a_continuation_world abi focus (UCOS2_inv sg)
      (armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
        saved.(armv7a_continuation_fragments)) ** frame) final.
Proof.
  intros external platform port abi focus sg entry node saved call publication frame heap
    Hfocus Hfocused Hcall Hbinding Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion
    Hgeometry Hpublication Hsp Hpre.
  pose proof Hbinding as [_ Hstack]; rewrite Hcall in Hstack.
  assert (Hsplit : armv7a_continuation_world abi focus (UCOS2_inv sg) entry **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved ** frame |--
    (UCOS2_inv sg entry **
      task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments)) **
    (armv7a_dormant_continuation abi saved ** armv7a_parked_continuations abi focus entry ** frame)).
  { unfold armv7a_continuation_world; rewrite Hstack; entailer!. }
  destruct (Hsplit heap Hpre) as [owned [rest [Hjoin [Howned Hrest]]]].
  destruct (armv7a_irq_live_entry_parks_stack sg entry node saved.(armv7a_continuation_sp)
    call saved.(armv7a_continuation_fragments) publication owned Hrunning Hnesting Hcurrent
    Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Howned)
    as [updated [Hrun Hupdated]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [final [Hwhole Hfinal]].
  assert (Hpark : UCOS2_inv sg
      (armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
        saved.(armv7a_continuation_fragments)) **
      (armv7a_dormant_continuation abi saved ** armv7a_parked_continuations abi focus entry ** frame) |--
    armv7a_continuation_world abi focus (UCOS2_inv sg)
      (armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
        saved.(armv7a_continuation_fragments)) ** frame).
  { sep_apply_l_atomic (armv7a_dormant_continuation_entry _ _ _ abi focus saved Hfocus Hfocused Hbinding).
    unfold armv7a_parked_continuations; rewrite <- Hstack.
    sep_apply_l_atomic (store_parked_continuations_park (armv7a_parked_continuation_entry abi focus)
      entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      saved.(armv7a_continuation_fragments) Hnone).
    unfold armv7a_continuation_world, armv7a_parked_continuations,
      armv7a_irq_live_parked_state, armv7a_irq_live_entry_state, os_sched_save_current_sp.
    unfold armv7a_irq_entry_counter_state; rewrite Hrunning.
    cbn [replace_TskS replace_IntrS TskState glob_task_set_parked_stacks parkedTaskStacks].
    rewrite Hnode; cbn [glob_task_set_usedtask parkedTaskStacks]; entailer!. }
  exists final; split; [exact Hwhole|]. apply (Hpark final).
  exists updated, rest; split; [exact Hfinal|]; split; assumption.
Qed.

(** Full source deposit: running owner -> actual register/frame save ->
    actual counter/SP stores -> focused parked owner. No capsule is an
    input, and both physical effects share [saved_heap] as their boundary.
    The old handler is only a disjoint frame after this deposit. *)
Lemma armv7a_irq_source_save_deposit : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler saved publication (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let focus := armv7a_call_focus call handler.(os_int_exit_interrupted_pc)
    saved.(armv7a_continuation_lr) in
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    saved.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    saved.(armv7a_continuation_sp) ->
  (os_int_exit_frame_save_pre external platform handler **
    (armv7a_continuation_world abi focus
       (UCOS2_inv sg) entry ** frame)) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  exists final,
    saved.(armv7a_continuation_call) = Some call /\
    saved.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc) /\
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution
      (armv7a_irq_live_entry_writes sg entry call.(os_sched_call_stack).(stackLeaseSlot)
        saved.(armv7a_continuation_sp)) saved_heap final /\
    (armv7a_continuation_world abi focus (UCOS2_inv sg)
       (armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
         saved.(armv7a_continuation_fragments)) **
     (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources port handler ** frame)) final.
Proof.
  intros external platform port abi sg entry node handler saved publication frame before saved_heap
    call focus Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication
    Hsp Hpre Hsave.
  destruct (armv7a_save_transition_observations _ _ _ abi handler saved before saved_heap Hsave)
    as [Hentry [Hcall [Hbinding [Hmask [Hpc [Hsavedsp Hfragments]]]]]].
  destruct (armv7a_save_transition_resources _ _ _ abi handler saved call _ before saved_heap
    Hcall eq_refl Hbinding Hmask Hpc Hsavedsp Hfragments Hpre Hsave) as [Hwrites Hsaved].
  pose proof Hbinding as [_ Hstack]; rewrite Hcall in Hstack.
  assert (Hfocus : task_stack_key saved.(armv7a_continuation_stack) =
    armv7a_call_focus_key focus).
  { unfold focus, armv7a_call_focus_key, armv7a_call_focus; cbn. unfold call; rewrite Hstack; reflexivity. }
  assert (Hfocused : armv7a_continuation_focus_binding focus saved).
  { unfold armv7a_continuation_focus_binding, focus, armv7a_call_focus; cbn.
    split; [exact Hcall|]. split; [exact Hpc|reflexivity]. }
  assert (Hreorder :
    interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved **
    (armv7a_continuation_world abi focus
       (UCOS2_inv sg) entry ** frame) |--
    armv7a_continuation_world abi focus (UCOS2_inv sg) entry **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved **
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame)).
  { entailer!. }
  destruct (armv7a_irq_entry_deposits_continuation external platform port abi
    focus sg entry node saved call publication _ saved_heap
    Hfocus Hfocused Hcall Hbinding Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp (Hreorder saved_heap Hsaved)) as [final [Hrun Hpost]].
  exists final; split; [exact Hcall|].
  split; [exact Hpc|]. split; [exact Hwrites|]. split; assumption.
Qed.

(** A real intervening C fragment, not a pure trace endpoint. OSIntExit's
    observed no-schedule branch reads OSRunning/nesting/lock and performs
    its guarded counter store. The same focused capsule is a disjoint
    frame of those actual writes, so this branch cannot replace it by a
    different invocation at the same key. This says nothing about an
    arbitrary BSP handler or OSTaskSwHook between source cuts. *)
Lemma armv7a_irq_no_schedule_keeps_parked_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus sg state
  (frame : Assertion) before,
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  (armv7a_continuation_world abi focus (UCOS2_inv sg) state ** frame) before ->
  exists after,
    os_int_exit_masked_no_schedule_fragment sg before after /\
    (armv7a_continuation_world abi focus (UCOS2_inv sg)
       (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros external platform port abi focus sg state frame before Hbranch Hpre.
  assert (Hsplit : armv7a_continuation_world abi focus (UCOS2_inv sg) state ** frame |--
    UCOS2_inv sg state ** (armv7a_parked_continuations abi focus state ** frame)).
  { unfold armv7a_continuation_world; entailer!. }
  destruct (os_int_exit_masked_no_schedule_frame_post sg state _ before Hbranch
    (Hsplit before Hpre)) as [after [Hsource Hpost]].
  exists after; split; [exact Hsource|].
  assert (Hmerge : UCOS2_inv sg
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
      (armv7a_parked_continuations abi focus state ** frame) |--
    armv7a_continuation_world abi focus (UCOS2_inv sg)
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame).
  { unfold armv7a_continuation_world, armv7a_parked_continuations,
      os_int_exit_counter_state; cbn [replace_IntrS TskState]; entailer!. }
  exact (Hmerge after Hpost).
Qed.

(** Initial task entry is backed by the concrete StackInit image, not by
    a suspended-call receipt. The allocation lease is supplied only at the
    protected creation commit, after the actual TCB allocation chose its
    slot and generation. The descriptor alone owns no memory or CPU. *)
Definition armv7a_initial_continuation (lease : TaskStackLease)
  (top entry argument task_return : Z) (lower upper : list (option Z)) : Armv7aContinuation :=
  {| armv7a_continuation_call := None;
     armv7a_continuation_stack := lease;
     armv7a_continuation_sp := task_stack_init_sp TaskStackNoVFP top;
     armv7a_continuation_fragments := task_stack_complete_fragments lease.(stackLeaseRegion)
       (lower ++ map (@Some Z)
         (task_stack_init_frame_words TaskStackNoVFP entry argument task_return 0) ++ upper);
     armv7a_continuation_cpsr := task_stack_init_cpsr entry;
     armv7a_continuation_registers :=
       [argument; 16843009; 33686018; 50529027; 67372036; 84215045;
        101058054; 117901063; 134744072; 151587081; 269488144; 286331153; 303174162];
     armv7a_continuation_lr := task_return;
     armv7a_continuation_pc := task_stack_init_entry_pc entry |}.

Definition armv7a_initial_frame_binding (saved : Armv7aContinuation) : Prop :=
  exists top entry argument task_return lower upper,
    saved = armv7a_initial_continuation saved.(armv7a_continuation_stack)
      top entry argument task_return lower upper /\
    valid_task_stack_region saved.(armv7a_continuation_stack).(stackLeaseRegion) /\
    saved.(armv7a_continuation_sp) =
      saved.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionBase) + Zlength lower * sizeof(UINT) /\
    saved.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) =
      Zlength lower + 16 + Zlength upper.

Lemma armv7a_initial_continuation_binding : forall lease top entry argument task_return lower upper,
  armv7a_continuation_binding
    (armv7a_initial_continuation lease top entry argument task_return lower upper).
Proof. intros; split; reflexivity || exact I. Qed.

Lemma armv7a_initial_continuation_frame_words : forall lease top entry argument task_return lower upper,
  armv7a_continuation_words
    (armv7a_initial_continuation lease top entry argument task_return lower upper) =
  task_stack_init_frame_words TaskStackNoVFP entry argument task_return 0.
Proof. reflexivity. Qed.

Lemma armv7a_initial_frame_no_call : forall saved,
  armv7a_initial_frame_binding saved -> saved.(armv7a_continuation_call) = None.
Proof.
  intros saved [top [entry [argument [task_return [lower [upper [Heq Hrest]]]]]]].
  rewrite Heq; reflexivity.
Qed.

(** Only the resumed branch contains an opaque saved-call capability.
    The first-entry branch records a checked initial frame shape, paired
    with the separate, exclusive physical buffer in the SAME parked map.
    It cannot be used to derive [Some original] or normal C return. *)
Definition armv7a_task_continuation_resource {external platform port}
  (abi : Armv7aContinuationABI external platform port) (saved : Armv7aContinuation) : Assertion :=
  match saved.(armv7a_continuation_call) with
  | None => coq_prop (armv7a_initial_frame_binding saved) && emp
  | Some _ => armv7a_dormant_continuation abi saved
  end.

Definition armv7a_task_continuation_entry {external platform port}
  (abi : Armv7aContinuationABI external platform port)
  (key : TaskID * nat) (payload : TaskStackRegion * TaskStackFragments) : Assertion :=
  EX saved,
    coq_prop (armv7a_continuation_binding saved /\
      task_stack_key saved.(armv7a_continuation_stack) = key /\
      (saved.(armv7a_continuation_stack).(stackLeaseRegion),
        saved.(armv7a_continuation_fragments)) = payload) &&
    armv7a_task_continuation_resource abi saved.

Definition armv7a_task_continuations {external platform port}
  (abi : Armv7aContinuationABI external platform port) (stacks : TaskStackMap) : Assertion :=
  store_parked_continuations (armv7a_task_continuation_entry abi) stacks.

Lemma armv7a_task_continuation_entry_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved,
  armv7a_continuation_binding saved ->
  armv7a_task_continuation_resource abi saved |--
  armv7a_task_continuation_entry abi (task_stack_key saved.(armv7a_continuation_stack))
    (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments)).
Proof. intros; unfold armv7a_task_continuation_entry; Exists saved; entailer!. Qed.

Lemma armv7a_task_continuations_park : forall external platform port
  (abi : Armv7aContinuationABI external platform port) stacks saved,
  armv7a_continuation_binding saved ->
  stacks (task_stack_key saved.(armv7a_continuation_stack)) = None ->
  task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
    saved.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi saved **
    store_parked_stacks stacks ** armv7a_task_continuations abi stacks |--
  store_parked_stacks (task_stack_park_fragments stacks saved.(armv7a_continuation_stack)
    saved.(armv7a_continuation_fragments)) **
  armv7a_task_continuations abi (task_stack_park_fragments stacks saved.(armv7a_continuation_stack)
    saved.(armv7a_continuation_fragments)).
Proof.
  intros external platform port abi stacks saved Hbinding Hnone.
  sep_apply_l_atomic (store_parked_stacks_park_fragments stacks
    saved.(armv7a_continuation_stack) saved.(armv7a_continuation_fragments) Hnone).
  sep_apply_l_atomic (armv7a_task_continuation_entry_resources external platform port abi saved Hbinding).
  unfold armv7a_task_continuations.
  sep_apply_l_atomic (store_parked_continuations_park (armv7a_task_continuation_entry abi)
    stacks saved.(armv7a_continuation_stack) saved.(armv7a_continuation_fragments) Hnone); entailer!.
Qed.

Lemma armv7a_task_continuations_take : forall external platform port
  (abi : Armv7aContinuationABI external platform port) stacks lease fragments,
  stacks (task_stack_key lease) = Some (lease.(stackLeaseRegion), fragments) ->
  store_parked_stacks stacks ** armv7a_task_continuations abi stacks |--
  EX saved,
    coq_prop (armv7a_continuation_binding saved /\
      saved.(armv7a_continuation_stack) = lease /\
      saved.(armv7a_continuation_fragments) = fragments) &&
    (task_stack_fragments_rep lease.(stackLeaseRegion) fragments **
     armv7a_task_continuation_resource abi saved **
     store_parked_stacks (task_stack_take stacks lease) **
     armv7a_task_continuations abi (task_stack_take stacks lease)).
Proof.
  intros external platform port abi stacks lease fragments Hentry.
  sep_apply_l_atomic (store_parked_stacks_take_fragments stacks lease fragments Hentry).
  unfold armv7a_task_continuations.
  sep_apply_l_atomic (store_parked_continuations_take (armv7a_task_continuation_entry abi)
    stacks lease fragments Hentry).
  unfold armv7a_task_continuation_entry; Intros saved.
  assert (Hkey : task_stack_key saved.(armv7a_continuation_stack) = task_stack_key lease) by tauto.
  assert (Hpayload : (saved.(armv7a_continuation_stack).(stackLeaseRegion),
    saved.(armv7a_continuation_fragments)) = (lease.(stackLeaseRegion), fragments)) by tauto.
  assert (Hlease : saved.(armv7a_continuation_stack) = lease).
  { unfold task_stack_key in Hkey.
    destruct saved.(armv7a_continuation_stack), lease; cbn in *; congruence. }
  Exists saved; entailer!; congruence.
Qed.

Lemma armv7a_uint_single_cell : forall address value,
  UIntArray.mixed_full address 1 [Some value] |-- address # UInt |-> value.
Proof.
  intros; unfold UIntArray.mixed_full, store_array; cbn [store_array_rec]; Intros.
  unfold UIntArray.mixedstoreA, StoreUIntAsElement.storeA.
  replace (address + 0 * sizeof(UINT)) with address by lia; entailer!.
Qed.

Lemma armv7a_frame_array_reads : forall words address (frame : Assertion) heap,
  (UIntArray.mixed_full address (Zlength words) (map (@Some Z) words) ** frame) heap ->
  armv7a_frame_word_reads address words heap.
Proof.
  induction words as [|word rest IH]; intros address frame heap Howned; [exact I|].
  assert (Hlength : Zlength (map (@Some Z) rest) = Zlength rest).
  { rewrite !Zlength_correct, map_length; reflexivity. }
  assert (Hsingle : Zlength [Some word] = 1) by reflexivity.
  assert (Hsplit : UIntArray.mixed_full address (Zlength (word :: rest))
      (map (@Some Z) (word :: rest)) ** frame |--
    address # Ptr |-> word **
      (UIntArray.mixed_full (address + 4) (Zlength rest) (map (@Some Z) rest) ** frame)).
  { rewrite Zlength_cons.
    change (UIntArray.mixed_full address (Zlength rest + 1)
      ([Some word] ++ map (@Some Z) rest) ** frame |--
      address # Ptr |-> word **
        (UIntArray.mixed_full (address + 4) (Zlength rest) (map (@Some Z) rest) ** frame)).
    replace (Zlength rest + 1) with (Zlength [Some word] + Zlength (map (@Some Z) rest))
      by (rewrite Hlength, Hsingle; lia).
    sep_apply_l_atomic (task_stack_array_split_app address [Some word] (map (@Some Z) rest)).
    rewrite Hlength, Hsingle, sizeof_uint.
    replace (address + 1 * 4) with (address + 4) by lia.
    sep_apply_l_atomic (armv7a_uint_single_cell address word).
    sep_apply_l_atomic (kernel_store_uint_store_ptr address word); entailer!. }
  specialize (Hsplit heap Howned); split.
  - exact (framed_pointer_store_load address word _ heap Hsplit).
  - apply (IH (address + 4) (address # Ptr |-> word ** frame) heap).
    assert (Hreorder : address # Ptr |-> word **
        (UIntArray.mixed_full (address + 4) (Zlength rest) (map (@Some Z) rest) ** frame) |--
      UIntArray.mixed_full (address + 4) (Zlength rest) (map (@Some Z) rest) **
        (address # Ptr |-> word ** frame)) by entailer!.
    exact (Hreorder heap Hsplit).
Qed.

Lemma armv7a_initial_frame_restore_reads : forall saved (frame : Assertion) heap,
  armv7a_initial_frame_binding saved ->
  (task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
    saved.(armv7a_continuation_fragments) ** frame) heap ->
  armv7a_continuation_restore_reads saved heap.
Proof.
  intros saved frame heap [top [entry [argument [task_return [lower [upper [Heq [Hregion [Hsp Hsize]]]]]]]]]
    Howned.
  remember saved.(armv7a_continuation_stack) as lease eqn:Hlease.
  subst saved; cbn [armv7a_initial_continuation armv7a_continuation_stack
    armv7a_continuation_fragments armv7a_continuation_sp] in Howned, Hsp.
  split; [apply armv7a_initial_continuation_binding|].
  rewrite armv7a_initial_continuation_frame_words.
  cbn [armv7a_initial_continuation armv7a_continuation_sp].
  set (words := task_stack_init_frame_words TaskStackNoVFP entry argument task_return 0).
  assert (Hlength : Zlength words = 16) by reflexivity.
  assert (Hmap : Zlength (map (@Some Z) words) = 16).
  { rewrite Zlength_correct, map_length, <- Zlength_correct; exact Hlength. }
  assert (Hsplit : task_stack_fragments_rep lease.(stackLeaseRegion)
      (task_stack_complete_fragments lease.(stackLeaseRegion)
        (lower ++ map (@Some Z) words ++ upper)) ** frame |--
    UIntArray.mixed_full (task_stack_init_sp TaskStackNoVFP top) (Zlength words)
      (map (@Some Z) words) **
    (task_stack_storage_without_region lease.(stackLeaseRegion) lower 16 upper ** frame)).
  { rewrite task_stack_fragments_rep_complete.
    sep_apply_l_atomic (task_stack_storage_split_region lease.(stackLeaseRegion)
      lower (map (@Some Z) words) upper ltac:(rewrite Hmap; exact Hsize)).
    rewrite Hmap, Hlength, <- Hsp; entailer!. }
  exact (armv7a_frame_array_reads words (task_stack_init_sp TaskStackNoVFP top) _ heap
    (Hsplit heap Howned)).
Qed.

(** APPROVED first-entry extension of the external ARM exchange ABI.
    Unlike the suspended-call branch, initialization has no old running
    receipt to deposit. The actual initial frame plus the restoring
    handler's CPU/context resources are consumed on the SAME restore
    transition. This does not prove entry code, BSP/hook behavior, return
    to a caller, or any current/ready fact. The old ABI is unchanged. *)
Record Armv7aInitialEntryABI external platform port
  (abi : Armv7aContinuationABI external platform port) : Type := {
  armv7a_initial_restore_source : forall saved,
    armv7a_initial_frame_binding saved ->
    external.(os_sched_arch_restore_source) saved.(armv7a_continuation_stack)
      saved.(armv7a_continuation_sp) saved.(armv7a_continuation_fragments);
  armv7a_initial_restore_resources : forall handler saved (frame : Assertion) before after,
    armv7a_initial_frame_binding saved ->
    armv7a_continuation_restore_reads saved before ->
    (interrupt_platform_running platform handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
     task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) ** frame) before ->
    armv7a_restore_transition abi handler saved before after ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
    (armv7a_initial_execution abi saved **
     task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame) after
}.

Lemma armv7a_restore_initial_frame : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (initial : Armv7aInitialEntryABI external platform port abi)
  handler saved (frame : Assertion) before after,
  saved.(armv7a_continuation_call) = None ->
  (interrupt_platform_running platform handler.(os_int_exit_invocation)
     handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
   task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
     saved.(armv7a_continuation_fragments) **
   armv7a_task_continuation_resource abi saved ** frame) before ->
  armv7a_restore_transition abi handler saved before after ->
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (armv7a_initial_execution abi saved **
   task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
     saved.(armv7a_continuation_fragments) **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack)
     handler.(os_int_exit_handler_fragments) ** frame) after.
Proof.
  intros external platform port abi initial handler saved frame before after Hnone Hpre Hrun.
  assert (Hextract : interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) **
      armv7a_task_continuation_resource abi saved ** frame |--
    coq_prop (armv7a_initial_frame_binding saved) &&
    (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** frame)).
  { unfold armv7a_task_continuation_resource; rewrite Hnone; entailer!. }
  destruct (Hextract before Hpre) as [Hbinding Hresources].
  assert (Hreorder : interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** frame |--
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) **
    (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame))
    by entailer!.
  exact (armv7a_initial_restore_resources _ _ _ abi initial handler saved frame before after
    Hbinding (armv7a_initial_frame_restore_reads saved _ before Hbinding
      (Hreorder before Hresources)) Hresources Hrun).
Qed.

(** Actual post-hook cache stores/SP read and selected take, now retaining
    all existing parked entries, not just one focused pending invocation.
    The destination binding is still the concrete scheduler/IRQ input;
    this lemma does NOT assume that every ready task has an entry. *)
Lemma armv7a_install_take_task_continuation : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg transfer (frame : Assertion) heap,
  os_int_exit_destination_binding external transfer ->
  tcb_field_address (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  (UCOS2_inv sg transfer.(os_int_exit_hooked_state) **
   armv7a_task_continuations abi transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks) **
   frame) heap ->
  exists final saved,
    sched_install_heap_fragment sg heap final
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      transfer.(os_int_exit_incoming_sp) /\
    armv7a_continuation_binding saved /\
    saved.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) /\
    saved.(armv7a_continuation_fragments) = transfer.(os_int_exit_incoming_fragments) /\
    task_current_at (os_int_exit_installed_state transfer)
      saved.(armv7a_continuation_stack).(stackLeaseSlot)
      saved.(armv7a_continuation_stack).(stackLeaseGeneration) /\
    (UCOS2_inv sg (os_int_exit_installed_state transfer) **
     armv7a_task_continuations abi (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) **
     armv7a_task_continuation_resource abi saved ** frame) final.
Proof.
  intros external platform port abi sg transfer frame heap Hdestination Haddress Hpre.
  pose proof Hdestination as [_ [_ [_ [Hparked Harch]]]].
  assert (Hsplit : UCOS2_inv sg transfer.(os_int_exit_hooked_state) **
      armv7a_task_continuations abi transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks) **
      frame |--
    UCOS2_inv sg transfer.(os_int_exit_hooked_state) **
      (armv7a_task_continuations abi transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks) **
       frame)) by entailer!.
  destruct (os_int_exit_install_heap_take_destination_frame external sg transfer _ heap
    Hdestination Haddress (Hsplit heap Hpre)) as [final [Hrun [[Hcurrent Hrestore] Hafter]]].
  assert (Htake : UCOS2_inv sg (os_int_exit_installed_state transfer) **
      task_stack_fragments_rep transfer.(os_int_exit_incoming_stack).(stackLeaseRegion)
        transfer.(os_int_exit_incoming_fragments) **
      (armv7a_task_continuations abi transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks) **
       frame) |--
    EX saved,
      coq_prop (armv7a_continuation_binding saved /\
        saved.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) /\
        saved.(armv7a_continuation_fragments) = transfer.(os_int_exit_incoming_fragments)) &&
      (UCOS2_inv sg (os_int_exit_installed_state transfer) **
       armv7a_task_continuations abi (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks) **
       task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
         saved.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi saved ** frame)).
  { unfold armv7a_task_continuations.
    sep_apply_l_atomic (store_parked_continuations_take
      (armv7a_task_continuation_entry abi) _ _ _ Hparked).
    unfold armv7a_task_continuation_entry; Intros saved.
    assert (Hkey : task_stack_key saved.(armv7a_continuation_stack) =
      task_stack_key transfer.(os_int_exit_incoming_stack)) by tauto.
    assert (Hpayload : (saved.(armv7a_continuation_stack).(stackLeaseRegion),
      saved.(armv7a_continuation_fragments)) =
      (transfer.(os_int_exit_incoming_stack).(stackLeaseRegion),
       transfer.(os_int_exit_incoming_fragments))) by tauto.
    assert (Hstack : saved.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack)).
    { unfold task_stack_key in Hkey.
      destruct saved.(armv7a_continuation_stack), transfer.(os_int_exit_incoming_stack);
        cbn in *; congruence. }
    assert (Hfragments : saved.(armv7a_continuation_fragments) =
      transfer.(os_int_exit_incoming_fragments)) by congruence.
    Exists saved; unfold os_int_exit_installed_state.
    cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
    rewrite Hstack, Hfragments; entailer!. }
  destruct (Htake final Hafter) as [saved [[Hbinding [Hstack Hfragments]] Hresources]].
  exists final, saved; split; [exact Hrun|]. split; [exact Hbinding|].
  split; [exact Hstack|]. split; [exact Hfragments|].
  split; [rewrite Hstack; exact Hcurrent|exact Hresources].
Qed.

(** Ordinary C entry after the actual initial-frame restore. The invocation
    number is a fresh logical registration chosen by the OS producer, not
    a stored ARM register. Fragment selection is the caller's real stack
    partition, with borrowed local bytes owned separately. *)
Definition armv7a_initial_call (saved : Armv7aContinuation) (invocation : nat)
  (fragments : TaskStackFragments) : OsSchedCallContext :=
  {| os_sched_call_invocation := invocation;
     os_sched_call_origin := RunningInvocation
       saved.(armv7a_continuation_stack).(stackLeaseSlot)
       saved.(armv7a_continuation_stack).(stackLeaseGeneration);
     os_sched_call_stack := saved.(armv7a_continuation_stack);
     os_sched_call_fragments := fragments |}.

(** APPROVED first-C-entry interpretation of the already restored ARM
    execution resource. This is an additional external CPU/stack ABI field,
    not a theorem derived from opaque [armv7a_initial_execution]. It consumes
    that resource once and creates NO bytes or OS current/ready/lifetime
    fact. The physically owned fragments/borrowed local cells are supplied
    by the caller's actual partition of the restored buffer. The resource
    interpretation is on the SAME heap and is not an interrupted Save,
    scheduler return, or claim that arbitrary callbacks preserve state. *)
Record Armv7aInitialCallABI external platform port
  (abi : Armv7aContinuationABI external platform port) : Type := {
  armv7a_initial_call_resources : forall saved invocation fragments,
    armv7a_initial_frame_binding saved ->
    task_stack_fragments_in_range
      saved.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0 fragments ->
    armv7a_initial_execution abi saved |--
      interrupt_platform_running platform invocation
        (RunningInvocation saved.(armv7a_continuation_stack).(stackLeaseSlot)
          saved.(armv7a_continuation_stack).(stackLeaseGeneration))
        (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
      external.(os_sched_arch_running) (armv7a_initial_call saved invocation fragments)
}.

Definition armv7a_initial_call_registered (saved : Armv7aContinuation)
  (state : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_TskS
    (task_begin_invocation
      (RunningInvocation saved.(armv7a_continuation_stack).(stackLeaseSlot)
        saved.(armv7a_continuation_stack).(stackLeaseGeneration)) state.(TskState)) state.

(** The OS side must establish current/live at an actual install cut.
    Ghost registration then preserves the physical invariant. No CPU token
    is used to infer these facts. The Timer first-call consumer supplies
    the installed state and its concrete borrowed stack byte. *)
Lemma armv7a_initial_call_register_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (entry : Armv7aInitialCallABI external platform port abi) sg state saved fragments,
  armv7a_initial_frame_binding saved ->
  task_stack_fragments_in_range
    saved.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0 fragments ->
  task_current_at state saved.(armv7a_continuation_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  let call := armv7a_initial_call saved state.(TskState).(taskLifecycle).(taskNextInvocation)
    fragments in
  UCOS2_inv sg state ** armv7a_initial_execution abi saved **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion) fragments |--
  coq_prop (kernel_call_task_source call (armv7a_initial_call_registered saved state)) &&
    (kernel_call_execution_owned external platform call
       (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
     UCOS2_inv sg (armv7a_initial_call_registered saved state)).
Proof.
  intros external platform port abi entry sg state saved fragments
    Hbinding Hfragments Hcurrent call.
  destruct (task_current_at_begin_invocation state
    saved.(armv7a_continuation_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_stack).(stackLeaseGeneration) Hcurrent)
    as [Hregistered Hactive].
  assert (Hsource : kernel_call_task_source call (armv7a_initial_call_registered saved state)).
  { unfold kernel_call_task_source, call, armv7a_initial_call.
    split; [reflexivity|]. split; [exact Hactive|exact (proj1 Hregistered)]. }
  sep_apply_l_atomic (UCOS2_inv_begin_task_invocation sg state
    (RunningInvocation saved.(armv7a_continuation_stack).(stackLeaseSlot)
      saved.(armv7a_continuation_stack).(stackLeaseGeneration)) (proj2 Hcurrent)).
  sep_apply_l_atomic (armv7a_initial_call_resources _ _ _ abi entry saved
    state.(TskState).(taskLifecycle).(taskNextInvocation) fragments Hbinding Hfragments).
  unfold kernel_call_execution_owned, os_sched_context_resources, call,
    armv7a_initial_call, armv7a_initial_call_registered in *; entailer!.
Qed.

(** Non-VFP OSStartHighRdy, AFTER its hook and OSRunning byte store.
    These cursors retain the actual order LDR high; LDR SP; LDM CPSR;
    MSR SPSR; LDM R0-R12,LR,PC^. They are a register/read projection,
    not a proof of the external CPU exchange or of the earlier C writes. *)
Inductive Armv7aStartCursor : Type :=
| StartLoadHigh
| StartLoadStack (destination : Z)
| StartLoadStatus (sp : Z)
| StartInstallStatus (sp cpsr : Z)
| StartLoadContext (sp cpsr : Z)
| StartEnterTask (sp cpsr : Z) (registers : list Z) (lr pc : Z).

Inductive armv7a_start_restore_step (high_address : Z)
  : Armv7aStartCursor -> model -> Armv7aStartCursor -> model -> Prop :=
| Armv7aStartLoadHigh : forall destination before after,
    pointer_load high_address destination before ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) ->
    armv7a_start_restore_step high_address StartLoadHigh before
      (StartLoadStack destination) after
| Armv7aStartLoadStack : forall destination sp before after,
    pointer_load destination sp before ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) ->
    armv7a_start_restore_step high_address (StartLoadStack destination) before
      (StartLoadStatus sp) after
| Armv7aStartLoadStatus : forall sp cpsr before after,
    pointer_load sp cpsr before ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) ->
    armv7a_start_restore_step high_address (StartLoadStatus sp) before
      (StartInstallStatus (sp + 4) cpsr) after
| Armv7aStartInstallStatus : forall sp cpsr before after,
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) ->
    armv7a_start_restore_step high_address (StartInstallStatus sp cpsr) before
      (StartLoadContext sp cpsr) after
| Armv7aStartLoadContext : forall sp cpsr registers lr pc before after,
    List.length registers = 13%nat ->
    armv7a_frame_word_reads sp (registers ++ [lr; pc]) before ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) ->
    armv7a_start_restore_step high_address (StartLoadContext sp cpsr) before
      (StartEnterTask (sp + 60) cpsr registers lr pc) after.

Definition armv7a_start_restore_execution (high_address : Z)
  (saved : Armv7aContinuation) (before after : model) : Prop :=
  exists destination first second third fourth,
    armv7a_start_restore_step high_address StartLoadHigh before
      (StartLoadStack destination) first /\
    armv7a_start_restore_step high_address (StartLoadStack destination) first
      (StartLoadStatus saved.(armv7a_continuation_sp)) second /\
    armv7a_start_restore_step high_address (StartLoadStatus saved.(armv7a_continuation_sp)) second
      (StartInstallStatus (saved.(armv7a_continuation_sp) + 4) saved.(armv7a_continuation_cpsr)) third /\
    armv7a_start_restore_step high_address
      (StartInstallStatus (saved.(armv7a_continuation_sp) + 4) saved.(armv7a_continuation_cpsr)) third
      (StartLoadContext (saved.(armv7a_continuation_sp) + 4) saved.(armv7a_continuation_cpsr)) fourth /\
    armv7a_start_restore_step high_address
      (StartLoadContext (saved.(armv7a_continuation_sp) + 4) saved.(armv7a_continuation_cpsr)) fourth
      (StartEnterTask (saved.(armv7a_continuation_sp) + 4 + 60)
        saved.(armv7a_continuation_cpsr) saved.(armv7a_continuation_registers)
        saved.(armv7a_continuation_lr) saved.(armv7a_continuation_pc)) after.

(** APPROVED external first-start CPU/stack exchange, distinct from IRQ.
    The actual masked bootstrap execution owner is consumed; no handler
    token is fabricated. OSRunning, selected/current TCB and ready facts
    are NOT ABI outputs. The case producer must execute the OS byte write,
    read the selected live TCB/SP and take its already initialized buffer.
    The arbitrary frame is the same resource on this single transition.
    MSR SVC/CLREX/hook are earlier cuts, not assumed no-ops by this rule. *)
Record Armv7aStartRestoreABI external platform port
  (abi : Armv7aContinuationABI external platform port) : Type := {
  armv7a_start_restore_transition : OsSchedCallContext -> Z ->
    Armv7aContinuation -> model -> model -> Prop;
  armv7a_start_restore_source : forall boot high saved before after,
    armv7a_start_restore_transition boot high saved before after ->
    armv7a_start_restore_execution high saved before after;
  armv7a_start_restore_resources : forall boot high saved (frame : Assertion) before after,
    boot.(os_sched_call_origin) = BootInvocation ->
    armv7a_initial_frame_binding saved ->
    armv7a_continuation_restore_reads saved before ->
    (kernel_call_execution_owned external platform boot 192 **
     task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) ** frame) before ->
    armv7a_start_restore_transition boot high saved before after ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
    (armv7a_initial_execution abi saved **
     task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) **
     task_stack_fragments_rep boot.(os_sched_call_stack).(stackLeaseRegion)
       boot.(os_sched_call_fragments) ** frame) after
}.

Arguments armv7a_start_restore_transition {external platform port abi} _ _ _ _ _ _.
