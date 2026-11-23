Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From compcert.lib Require Import Integers.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Import UCOS2_C_Rules KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source/os_core.c declares the 256-byte OSUnMapTbl initializer outside
    OSInit. The existing dynamic representation does not own these bytes.
    This program-level owner contains them ONCE, separately from mutable
    Task/Scheduler/Event storage. It is not a new runtime field or ghost
    array, and pure valid_stable_glob_vars is not its producer.

    The selected and full profiles share the same C initializer. Opening
    a masked operation lends the actual array to its existing checked
    callee; closing returns it to this owner. An unmasked interruption
    hands this shared owner to the handler, not a second array copy. *)
Definition kernel_program_rep (sg : StableGlobVars)
  (state : UCOS2_Verify_State) : Assertion :=
  UCOS2_raw_rep sg state ** unmap_table_rep sg.

Definition kernel_program_inv (sg : StableGlobVars)
  (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg state) && kernel_program_rep sg state.

Definition kernel_program_full_inv (sg : StableGlobVars)
  (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_full_state_inv sg state) && kernel_program_rep sg state.

Lemma kernel_program_inv_split_unmap : forall sg state,
  kernel_program_inv sg state --||-- UCOS2_inv sg state ** unmap_table_rep sg.
Proof. intros; unfold kernel_program_inv, kernel_program_rep, UCOS2_inv; split; entailer!. Qed.

Lemma kernel_program_full_inv_split_unmap : forall sg state,
  kernel_program_full_inv sg state --||-- UCOS2_full_inv sg state ** unmap_table_rep sg.
Proof. intros; unfold kernel_program_full_inv, kernel_program_rep, UCOS2_full_inv; split; entailer!. Qed.

Lemma kernel_program_inv_merge_updated_unmap : forall sg after,
  UCOS2_state_inv sg after ->
  UCOS2_raw_rep sg after ** unmap_table_rep sg |-- kernel_program_inv sg after.
Proof. intros; unfold kernel_program_inv, kernel_program_rep; entailer!. Qed.

(** Global C initialization consumes the declared storage. This is its
    ordinary byte-memory projection, not a new executable OS routine and
    not a proof of the loader/BSP. The exact literal-to-unmap equation is
    already proved in sched.v and checked against the pinned source. *)
Lemma uchar_noninit_store_execution : forall address stored before,
  0 <= stored < 256 -> (address # UChar |->_) before ->
  exists after, kernel_heap_execution [(address, stored)] before after /\
    (address # UChar |-> stored) after.
Proof.
  intros address stored before Hrange [Haddress Hbefore].
  destruct (byte_noninit_store_execution address stored before Hrange Hbefore)
    as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  split; [split; [exact Haddress|]; change (stored >= 0 /\ stored <= 255); lia|exact Hafter].
Qed.

Lemma framed_uchar_noninit_store_execution : forall address stored (frame : Assertion) before,
  0 <= stored < 256 -> (address # UChar |->_ ** frame) before ->
  exists after, kernel_heap_execution [(address, stored)] before after /\
    (address # UChar |-> stored ** frame) after.
Proof.
  intros address stored frame before Hrange [cell [rest [Hjoin [Hcell Hrest]]]].
  destruct (uchar_noninit_store_execution address stored cell Hrange Hcell)
    as [updated [Hrun Hupdated]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [after [Hwhole Hafter]].
  exists after; split; [exact Hwhole|].
  exists updated, rest; split; [exact Hafter|]; split; assumption.
Qed.

Lemma uchar_array_rec_initialize : forall values base lo hi (frame : Assertion) before,
  Forall (fun value => 0 <= value < 256) values ->
  (store_undef_array_rec StoreUCharAsElement.undefstoreA base lo hi
      (List.length values) ** frame) before ->
  exists after,
    kernel_heap_execution (byte_list_writes (base + lo) values) before after /\
    (store_array_rec StoreUCharAsElement.storeA base lo hi values ** frame) after.
Proof.
  induction values as [|value rest IH]; intros base lo hi frame before Hranges Hbefore.
  - exists before; split; [split; [constructor|split; reflexivity]|].
    assert (Hfinish : store_undef_array_rec StoreUCharAsElement.undefstoreA base lo hi 0 ** frame |--
      store_array_rec StoreUCharAsElement.storeA base lo hi [] ** frame).
    { cbn [store_undef_array_rec store_array_rec]; entailer!. }
    exact (Hfinish before Hbefore).
  - inversion Hranges as [|value0 rest0 Hvalue Hrest]; subst.
    assert (Hsplit : store_undef_array_rec StoreUCharAsElement.undefstoreA base lo hi
        (List.length (value :: rest)) ** frame |--
      (base + lo) # UChar |->_ **
      (store_undef_array_rec StoreUCharAsElement.undefstoreA base (lo + 1) hi
        (List.length rest) ** frame)).
    { cbn [List.length store_undef_array_rec]; unfold StoreUCharAsElement.undefstoreA.
      rewrite sizeof_uchar, Z.mul_1_r; entailer!. }
    destruct (framed_uchar_noninit_store_execution (base + lo) value _ before Hvalue
      (Hsplit before Hbefore)) as [middle [Hhead Hmiddle]].
    assert (Hreorder : (base + lo) # UChar |-> value **
      (store_undef_array_rec StoreUCharAsElement.undefstoreA base (lo + 1) hi
        (List.length rest) ** frame) |--
      store_undef_array_rec StoreUCharAsElement.undefstoreA base (lo + 1) hi
        (List.length rest) ** ((base + lo) # UChar |-> value ** frame)) by entailer!.
    destruct (IH base (lo + 1) hi ((base + lo) # UChar |-> value ** frame) middle
      Hrest (Hreorder middle Hmiddle)) as [after [Htail Hafter]].
    exists after; split.
    + change (kernel_heap_execution
        ([(base + lo, value)] ++ byte_list_writes (base + lo + 1) rest) before after).
      replace (base + lo + 1) with (base + (lo + 1)) by lia.
      eapply heap_execution_append; eassumption.
    + assert (Hmerge : store_array_rec StoreUCharAsElement.storeA base (lo + 1) hi rest **
        ((base + lo) # UChar |-> value ** frame) |--
        store_array_rec StoreUCharAsElement.storeA base lo hi (value :: rest) ** frame).
      { cbn [store_array_rec]; unfold StoreUCharAsElement.storeA.
        rewrite sizeof_uchar, Z.mul_1_r; entailer!. }
      exact (Hmerge after Hafter).
Qed.

Lemma uchar_array_initialize : forall values base (frame : Assertion) before,
  Forall (fun value => 0 <= value < 256) values ->
  (UCharArray.undef_full base (Zlength values) ** frame) before ->
  exists after,
    kernel_heap_execution (byte_list_writes base values) before after /\
    (UCharArray.full base (Zlength values) values ** frame) after.
Proof.
  intros values base frame before Hranges Hbefore.
  unfold UCharArray.undef_full, store_undef_array in Hbefore.
  rewrite Zlength_correct, Nat2Z.id in Hbefore.
  rewrite Zlength_correct.
  destruct (uchar_array_rec_initialize values base 0 (Z.of_nat (List.length values)) frame before
    Hranges Hbefore) as [after [Hrun Hafter]].
  exists after; split; [rewrite Z.add_0_r in Hrun; exact Hrun|exact Hafter].
Qed.

Lemma unmap_table_values_in_range : Forall (fun value => 0 <= value < 256) unmap_table.
Proof.
  unfold unmap_table; apply Forall_forall; intros value Hin.
  apply in_map_iff in Hin; destruct Hin as [index [<- Hin]].
  pose proof (unmap_in_range (Z.of_nat index)); lia.
Qed.

Lemma unmap_table_initialize : forall sg (frame : Assertion) before,
  (UCharArray.undef_full sg.(g_OSUnMapTbl) 256 ** frame) before ->
  exists after,
    kernel_heap_execution (byte_list_writes sg.(g_OSUnMapTbl) unmap_table) before after /\
    (unmap_table_rep sg ** frame) after.
Proof.
  intros sg frame before Hbefore.
  rewrite <- unmap_table_length in Hbefore.
  destruct (uchar_array_initialize unmap_table sg.(g_OSUnMapTbl) frame before
    unmap_table_values_in_range Hbefore) as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  rewrite unmap_table_length in Hafter; exact Hafter.
Qed.

Lemma kernel_program_initialize_unmap : forall sg state before,
  (UCharArray.undef_full sg.(g_OSUnMapTbl) 256 ** UCOS2_inv sg state) before ->
  exists after,
    kernel_heap_execution (byte_list_writes sg.(g_OSUnMapTbl) unmap_table) before after /\
    kernel_program_inv sg state after.
Proof.
  intros sg state before Hbefore.
  destruct (unmap_table_initialize sg (UCOS2_inv sg state) before Hbefore)
    as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  assert (Hmerge : unmap_table_rep sg ** UCOS2_inv sg state |-- kernel_program_inv sg state).
  { rewrite kernel_program_inv_split_unmap; entailer!. }
  exact (Hmerge after Hafter).
Qed.

Definition kernel_program_closed (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
  (interrupt_platform_running platform invocation origin mask **
   critical_region_outside critical sg invocation state ** unmap_table_rep sg).

Lemma kernel_program_closed_equiv : forall platform critical sg invocation origin mask state,
  kernel_program_closed platform critical sg invocation origin mask state --||--
    interrupt_platform_running platform invocation origin mask ** kernel_program_inv sg state.
Proof.
  intros; unfold kernel_program_closed, critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite <- UCOS2_raw_rep_split_running.
  unfold kernel_program_inv, kernel_program_rep; split; entailer!.
Qed.

(** The caller transports the actual shared heap, including this table,
    through the source execution. It is not a private frame that remains
    separately available while an IRQ callee borrows another copy. *)
Lemma kernel_program_rep_excludes_duplicate_unmap : forall sg state,
  kernel_program_rep sg state ** unmap_table_rep sg |-- coq_prop False.
Proof.
  intros sg state; unfold kernel_program_rep.
  sep_apply_l_atomic (unmap_table_split_cell sg 0 ltac:(lia)).
  unfold store_uchar; pureIntros.
  sep_apply_l_atomic (dup_store_byte (sg.(g_OSUnMapTbl) + 0 * sizeof(UCHAR))
    (unmap_value 0) (unmap_value 0)); entailer!.
Qed.
