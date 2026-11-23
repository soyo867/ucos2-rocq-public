Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_wait_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** The three literal OSSemPend assignments immediately before
    OS_EventTaskWait. Dly is one typed 32-bit C store. *)
Definition sem_pend_wait_prefix_fragment sg timeout (before after : model) : Prop :=
  exists current status status_written pending_written,
    pointer_load sg.(g_OSTCBCur) current before /\
    uchar_load (tcb_field_address current TCBStat) status before /\
    kernel_heap_execution [(tcb_field_address current TCBStat, Z.lor status 1)] before status_written /\
    pointer_load sg.(g_OSTCBCur) current status_written /\
    kernel_heap_execution [(tcb_field_address current TCBStatPend, 0)] status_written pending_written /\
    pointer_load sg.(g_OSTCBCur) current pending_written /\
    kernel_heap_execution (pointer_store_writes (tcb_field_address current TCBDly) timeout)
      pending_written after.

Definition sem_pend_wait_prefix_cells sg entry tid old status pending delay : Assertion :=
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some status) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some pending) **
  tcb_cell (task_slot_addr sg tid) TCBDly (Some delay) **
  sem_pend_prefix_frame sg entry tid old.

Lemma sem_pend_byte_or_in_range : forall a b,
  0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
  intros a b Ha Hb.
  pose proof (unsigned_Lastnbits_range (Z.lor a b) 8 ltac:(lia)) as Hrange.
  rewrite unsigned_last_nbits_lor_distr_missing in Hrange by (cbn; lia).
  exact Hrange.
Qed.

Lemma sem_pend_byte_and_in_range : forall a b,
  0 <= a < 256 -> 0 <= Z.land a b < 256.
Proof.
  intros a b Ha.
  pose proof (unsigned_Lastnbits_range (Z.land a b) 8 ltac:(lia)) as Hrange.
  rewrite unsigned_last_nbits_land_missing_l in Hrange by (cbn; lia).
  exact Hrange.
Qed.

Lemma sem_pend_wait_prefix_stores_source : forall sg entry tid old timeout (frame : Assertion) before,
  0 <= timeout < 4294967296 ->
  (sem_pend_wait_prefix_cells sg entry tid old (encode_task_status old.(stat))
    (encode_pend_status old.(statPend)) old.(dly) ** frame) before ->
  exists after,
    sem_pend_wait_prefix_fragment sg timeout before after /\
    (sem_pend_wait_prefix_cells sg entry tid old (Z.lor (encode_task_status old.(stat)) 1) 0 timeout ** frame) after.
Proof.
  intros sg entry tid old timeout frame before Htimeout Hpre.
  set (base := task_slot_addr sg tid).
  set (stat_frame := sg.(g_OSTCBCur) # Ptr |-> base **
    tcb_cell base TCBStatPend (Some (encode_pend_status old.(statPend))) **
    tcb_cell base TCBDly (Some old.(dly)) ** sem_pend_prefix_frame sg entry tid old ** frame).
  assert (Hstat : sem_pend_wait_prefix_cells sg entry tid old (encode_task_status old.(stat))
      (encode_pend_status old.(statPend)) old.(dly) ** frame |--
    tcb_field_address base TCBStat # UChar |-> encode_task_status old.(stat) ** stat_frame).
  { unfold sem_pend_wait_prefix_cells, stat_frame, base; cbn [tcb_cell]; entailer!. }
  assert (Hread_before : pointer_load sg.(g_OSTCBCur) base before).
  { apply framed_pointer_store_load with (frame := TT).
    match type of Hpre with ?P before => assert (Hr : P |-- sg.(g_OSTCBCur) # Ptr |-> base ** TT)
      by (unfold sem_pend_wait_prefix_cells, base; entailer!; intros ? ?; exact I) end.
    exact (Hr before Hpre). }
  pose proof (framed_uchar_store_load _ _ _ _ (Hstat before Hpre)) as Hread_stat.
  pose proof (sem_pend_byte_or_in_range (encode_task_status old.(stat)) 1
    (encode_task_status_in_range old.(stat)) ltac:(lia)) as Hrange.
  destruct (kernel_heap_framed_uchar_store (tcb_field_address base TCBStat)
    (encode_task_status old.(stat)) (Z.lor (encode_task_status old.(stat)) 1)
    stat_frame before Hrange (Hstat before Hpre)) as [status_written [Hstatus Hstatus_post]].
  set (pend_frame := sg.(g_OSTCBCur) # Ptr |-> base **
    tcb_cell base TCBStat (Some (Z.lor (encode_task_status old.(stat)) 1)) **
    tcb_cell base TCBDly (Some old.(dly)) ** sem_pend_prefix_frame sg entry tid old ** frame).
  assert (Hpend : tcb_field_address base TCBStat # UChar |-> Z.lor (encode_task_status old.(stat)) 1 ** stat_frame |--
    tcb_field_address base TCBStatPend # UChar |-> encode_pend_status old.(statPend) ** pend_frame).
  { unfold stat_frame, pend_frame; cbn [tcb_cell]; entailer!. }
  assert (Hread_status : pointer_load sg.(g_OSTCBCur) base status_written).
  { apply framed_pointer_store_load with (frame := TT).
    match type of Hstatus_post with ?P status_written => assert (Hr : P |-- sg.(g_OSTCBCur) # Ptr |-> base ** TT)
      by (unfold stat_frame; entailer!; intros ? ?; exact I) end.
    exact (Hr status_written Hstatus_post). }
  destruct (kernel_heap_framed_uchar_store (tcb_field_address base TCBStatPend)
    (encode_pend_status old.(statPend)) 0 pend_frame status_written ltac:(lia)
    (Hpend status_written Hstatus_post)) as [pending_written [Hpending Hpending_post]].
  set (delay_frame := sg.(g_OSTCBCur) # Ptr |-> base **
    tcb_cell base TCBStat (Some (Z.lor (encode_task_status old.(stat)) 1)) **
    tcb_cell base TCBStatPend (Some 0) ** sem_pend_prefix_frame sg entry tid old ** frame).
  assert (Hdelay : tcb_field_address base TCBStatPend # UChar |-> 0 ** pend_frame |--
    tcb_field_address base TCBDly # UInt |->_ ** delay_frame).
  { unfold pend_frame, delay_frame; cbn [tcb_cell].
    sep_apply_l_atomic (store_uint_undef_store_uint (tcb_field_address base TCBDly) old.(dly)); entailer!. }
  assert (Hread_pending : pointer_load sg.(g_OSTCBCur) base pending_written).
  { apply framed_pointer_store_load with (frame := TT).
    match type of Hpending_post with ?P pending_written => assert (Hr : P |-- sg.(g_OSTCBCur) # Ptr |-> base ** TT)
      by (unfold pend_frame; entailer!; intros ? ?; exact I) end.
    exact (Hr pending_written Hpending_post). }
  destruct (task_stack_uint_store_execution (tcb_field_address base TCBDly) timeout delay_frame
    pending_written Htimeout (Hdelay pending_written Hpending_post)) as [after [Hdelay_run Hafter]].
  exists after; split.
  - exists base, (encode_task_status old.(stat)), status_written, pending_written; tauto.
  - match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q)
      by (unfold sem_pend_wait_prefix_cells, delay_frame, base; cbn [tcb_cell]; entailer!) end end.
    exact (Hclose after Hafter).
Qed.

(** Raw cells of the selected OS_EventTaskWait body. The explicit values
    describe its transient states; no global invariant is asserted until
    the caller reassembles the final state. *)
Definition sem_pend_event_wait_cells current tcb pevent ready_group ready_table
  row bit_x bit_y pointer event_row event_group ready_row ready_grp : Assertion :=
  current # Ptr |-> tcb **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventPtr") # Ptr |-> pointer **
  &(tcb # "os_tcb" ->ₛ "OSTCBY") # UChar |-> row **
  &(tcb # "os_tcb" ->ₛ "OSTCBBitX") # UChar |-> bit_x **
  &(tcb # "os_tcb" ->ₛ "OSTCBBitY") # UChar |-> bit_y **
  (&(pevent # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR)) # UChar |-> event_row **
  &(pevent # "os_event" ->ₛ "OSEventGrp") # UChar |-> event_group **
  (ready_table + row * sizeof(UCHAR)) # UChar |-> ready_row **
  ready_group # UChar |-> ready_grp.

(** Source reads are listed only where the C body performs them. The
    trace macro is disabled by the selected configuration. [row] is the
    local y value read before the ready-table assignment. *)
Definition sem_pend_event_wait_fragment current tcb pevent ready_group ready_table
  row bit_x bit_y event_row event_group ready_row ready_grp (before after : model) : Prop :=
  exists pointer_written table_written group_written ready_written,
    pointer_load current tcb before /\
    kernel_heap_execution (pointer_store_writes &(tcb # "os_tcb" ->ₛ "OSTCBEventPtr") pevent)
      before pointer_written /\
    pointer_load current tcb pointer_written /\
    uchar_load &(tcb # "os_tcb" ->ₛ "OSTCBY") row pointer_written /\
    uchar_load &(tcb # "os_tcb" ->ₛ "OSTCBBitX") bit_x pointer_written /\
    uchar_load (&(pevent # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR)) event_row pointer_written /\
    kernel_heap_execution [(&(pevent # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR), Z.lor event_row bit_x)]
      pointer_written table_written /\
    pointer_load current tcb table_written /\
    uchar_load &(tcb # "os_tcb" ->ₛ "OSTCBBitY") bit_y table_written /\
    uchar_load &(pevent # "os_event" ->ₛ "OSEventGrp") event_group table_written /\
    kernel_heap_execution [(&(pevent # "os_event" ->ₛ "OSEventGrp"), Z.lor event_group bit_y)]
      table_written group_written /\
    pointer_load current tcb group_written /\
    uchar_load &(tcb # "os_tcb" ->ₛ "OSTCBY") row group_written /\
    uchar_load &(tcb # "os_tcb" ->ₛ "OSTCBBitX") bit_x group_written /\
    uchar_load (ready_table + row * sizeof(UCHAR)) ready_row group_written /\
    kernel_heap_execution [(ready_table + row * sizeof(UCHAR), event_task_wait_ready_row ready_row bit_x)]
      group_written ready_written /\
    uchar_load (ready_table + row * sizeof(UCHAR)) (event_task_wait_ready_row ready_row bit_x) ready_written /\
    (if Z.eqb (event_task_wait_ready_row ready_row bit_x) 0 then
       pointer_load current tcb ready_written /\
       uchar_load &(tcb # "os_tcb" ->ₛ "OSTCBBitY") bit_y ready_written /\
       uchar_load ready_group ready_grp ready_written /\
       kernel_heap_execution [(ready_group, Z.land ready_grp (unsigned_last_nbits (Z.lnot bit_y) 8))]
         ready_written after
     else after = ready_written).

Local Ltac sem_pend_wait_read Hpre :=
  match goal with
  | |- pointer_load ?address ?observed ?heap =>
      apply framed_pointer_store_load with (frame := TT);
      match type of Hpre with ?P heap =>
        let Hfocus := fresh "Hfocus" in
        assert (Hfocus : P |-- address # Ptr |-> observed ** TT)
          by (unfold sem_pend_event_wait_cells; entailer!; intros ? ?; exact I);
        exact (Hfocus heap Hpre)
      end
  | |- uchar_load ?address ?observed ?heap =>
      apply framed_uchar_store_load with (frame := TT);
      match type of Hpre with ?P heap =>
        let Hfocus := fresh "Hfocus" in
        assert (Hfocus : P |-- address # UChar |-> observed ** TT)
          by (unfold sem_pend_event_wait_cells; entailer!; intros ? ?; exact I);
        exact (Hfocus heap Hpre)
      end
  end.

Lemma sem_pend_event_wait_stores_source : forall current tcb pevent ready_group ready_table
  row bit_x bit_y pointer event_row event_group ready_row ready_grp (frame : Assertion) before,
  0 <= row < 8 -> 0 <= pevent < 4294967296 ->
  (sem_pend_event_wait_cells current tcb pevent ready_group ready_table
    row bit_x bit_y pointer event_row event_group ready_row ready_grp ** frame) before ->
  exists after,
    sem_pend_event_wait_fragment current tcb pevent ready_group ready_table
      row bit_x bit_y event_row event_group ready_row ready_grp before after /\
    (event_task_wait_post current tcb pevent ready_group ready_table
      row bit_x bit_y event_row event_group ready_row ready_grp ** frame) after.
Proof.
  intros current tcb pevent ready_group ready_table row bit_x bit_y pointer event_row event_group
    ready_row ready_grp frame before Hrow Hpevent Hpre.
  assert (Hranges : 0 <= bit_x < 256 /\ 0 <= bit_y < 256 /\
    0 <= event_row < 256 /\ 0 <= event_group < 256 /\ 0 <= ready_row < 256 /\ 0 <= ready_grp < 256).
  { assert (Hx : uchar_load &(tcb # "os_tcb" ->ₛ "OSTCBBitX") bit_x before) by (sem_pend_wait_read Hpre).
    assert (Hy : uchar_load &(tcb # "os_tcb" ->ₛ "OSTCBBitY") bit_y before) by (sem_pend_wait_read Hpre).
    assert (He : uchar_load (&(pevent # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR)) event_row before)
      by (sem_pend_wait_read Hpre).
    assert (Hg : uchar_load &(pevent # "os_event" ->ₛ "OSEventGrp") event_group before) by (sem_pend_wait_read Hpre).
    assert (Hr : uchar_load (ready_table + row * sizeof(UCHAR)) ready_row before) by (sem_pend_wait_read Hpre).
    assert (Hrg : uchar_load ready_group ready_grp before) by (sem_pend_wait_read Hpre).
    unfold uchar_load in *; tauto. }
  set (pointer_frame := current # Ptr |-> tcb **
    &(tcb # "os_tcb" ->ₛ "OSTCBY") # UChar |-> row **
    &(tcb # "os_tcb" ->ₛ "OSTCBBitX") # UChar |-> bit_x **
    &(tcb # "os_tcb" ->ₛ "OSTCBBitY") # UChar |-> bit_y **
    (&(pevent # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR)) # UChar |-> event_row **
    &(pevent # "os_event" ->ₛ "OSEventGrp") # UChar |-> event_group **
    (ready_table + row * sizeof(UCHAR)) # UChar |-> ready_row ** ready_group # UChar |-> ready_grp ** frame).
  assert (Hpointer : sem_pend_event_wait_cells current tcb pevent ready_group ready_table
      row bit_x bit_y pointer event_row event_group ready_row ready_grp ** frame |--
    &(tcb # "os_tcb" ->ₛ "OSTCBEventPtr") # Ptr |->_ ** pointer_frame).
  { unfold sem_pend_event_wait_cells, pointer_frame.
    sep_apply_l_atomic (store_ptr_undef_store_ptr &(tcb # "os_tcb" ->ₛ "OSTCBEventPtr") pointer); entailer!. }
  destruct (framed_pointer_store_execution &(tcb # "os_tcb" ->ₛ "OSTCBEventPtr") pevent pointer_frame
    before Hpevent (Hpointer before Hpre)) as [pointer_written [Hpointer_run Hpointer_post]].
  assert (Hp : (sem_pend_event_wait_cells current tcb pevent ready_group ready_table
    row bit_x bit_y pevent event_row event_group ready_row ready_grp ** frame) pointer_written).
  { match type of Hpointer_post with ?P pointer_written => match goal with |- ?Q pointer_written =>
      assert (Hclose : P |-- Q) by (unfold sem_pend_event_wait_cells, pointer_frame; entailer!) end end.
    exact (Hclose pointer_written Hpointer_post). }
  set (table_frame := current # Ptr |-> tcb ** &(tcb # "os_tcb" ->ₛ "OSTCBEventPtr") # Ptr |-> pevent **
    &(tcb # "os_tcb" ->ₛ "OSTCBY") # UChar |-> row **
    &(tcb # "os_tcb" ->ₛ "OSTCBBitX") # UChar |-> bit_x **
    &(tcb # "os_tcb" ->ₛ "OSTCBBitY") # UChar |-> bit_y **
    &(pevent # "os_event" ->ₛ "OSEventGrp") # UChar |-> event_group **
    (ready_table + row * sizeof(UCHAR)) # UChar |-> ready_row ** ready_group # UChar |-> ready_grp ** frame).
  assert (Htable : sem_pend_event_wait_cells current tcb pevent ready_group ready_table
      row bit_x bit_y pevent event_row event_group ready_row ready_grp ** frame |--
    (&(pevent # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR)) # UChar |-> event_row ** table_frame).
  { unfold sem_pend_event_wait_cells, table_frame; entailer!. }
  destruct (kernel_heap_framed_uchar_store _ event_row (Z.lor event_row bit_x) table_frame pointer_written
    ltac:(apply sem_pend_byte_or_in_range; tauto) (Htable pointer_written Hp)) as [table_written [Htable_run Htable_post]].
  assert (Ht : (sem_pend_event_wait_cells current tcb pevent ready_group ready_table
    row bit_x bit_y pevent (Z.lor event_row bit_x) event_group ready_row ready_grp ** frame) table_written).
  { match type of Htable_post with ?P table_written => match goal with |- ?Q table_written =>
      assert (Hclose : P |-- Q) by (unfold sem_pend_event_wait_cells, table_frame; entailer!) end end.
    exact (Hclose table_written Htable_post). }
  set (group_frame := current # Ptr |-> tcb ** &(tcb # "os_tcb" ->ₛ "OSTCBEventPtr") # Ptr |-> pevent **
    &(tcb # "os_tcb" ->ₛ "OSTCBY") # UChar |-> row **
    &(tcb # "os_tcb" ->ₛ "OSTCBBitX") # UChar |-> bit_x **
    &(tcb # "os_tcb" ->ₛ "OSTCBBitY") # UChar |-> bit_y **
    (&(pevent # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR)) # UChar |-> Z.lor event_row bit_x **
    (ready_table + row * sizeof(UCHAR)) # UChar |-> ready_row ** ready_group # UChar |-> ready_grp ** frame).
  assert (Hgroup : sem_pend_event_wait_cells current tcb pevent ready_group ready_table
      row bit_x bit_y pevent (Z.lor event_row bit_x) event_group ready_row ready_grp ** frame |--
    &(pevent # "os_event" ->ₛ "OSEventGrp") # UChar |-> event_group ** group_frame).
  { unfold sem_pend_event_wait_cells, group_frame; entailer!. }
  destruct (kernel_heap_framed_uchar_store _ event_group (Z.lor event_group bit_y) group_frame table_written
    ltac:(apply sem_pend_byte_or_in_range; tauto) (Hgroup table_written Ht)) as [group_written [Hgroup_run Hgroup_post]].
  assert (Hg : (sem_pend_event_wait_cells current tcb pevent ready_group ready_table
    row bit_x bit_y pevent (Z.lor event_row bit_x) (Z.lor event_group bit_y) ready_row ready_grp ** frame) group_written).
  { match type of Hgroup_post with ?P group_written => match goal with |- ?Q group_written =>
      assert (Hclose : P |-- Q) by (unfold sem_pend_event_wait_cells, group_frame; entailer!) end end.
    exact (Hclose group_written Hgroup_post). }
  set (ready_frame := current # Ptr |-> tcb ** &(tcb # "os_tcb" ->ₛ "OSTCBEventPtr") # Ptr |-> pevent **
    &(tcb # "os_tcb" ->ₛ "OSTCBY") # UChar |-> row **
    &(tcb # "os_tcb" ->ₛ "OSTCBBitX") # UChar |-> bit_x **
    &(tcb # "os_tcb" ->ₛ "OSTCBBitY") # UChar |-> bit_y **
    (&(pevent # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR)) # UChar |-> Z.lor event_row bit_x **
    &(pevent # "os_event" ->ₛ "OSEventGrp") # UChar |-> Z.lor event_group bit_y **
    ready_group # UChar |-> ready_grp ** frame).
  assert (Hready : sem_pend_event_wait_cells current tcb pevent ready_group ready_table
      row bit_x bit_y pevent (Z.lor event_row bit_x) (Z.lor event_group bit_y) ready_row ready_grp ** frame |--
    (ready_table + row * sizeof(UCHAR)) # UChar |-> ready_row ** ready_frame).
  { unfold sem_pend_event_wait_cells, ready_frame; entailer!. }
  destruct (kernel_heap_framed_uchar_store _ ready_row (event_task_wait_ready_row ready_row bit_x)
    ready_frame group_written ltac:(apply sem_pend_byte_and_in_range; tauto) (Hready group_written Hg))
    as [ready_written [Hready_run Hready_post]].
  assert (Hr : (sem_pend_event_wait_cells current tcb pevent ready_group ready_table
    row bit_x bit_y pevent (Z.lor event_row bit_x) (Z.lor event_group bit_y)
    (event_task_wait_ready_row ready_row bit_x) ready_grp ** frame) ready_written).
  { match type of Hready_post with ?P ready_written => match goal with |- ?Q ready_written =>
      assert (Hclose : P |-- Q) by (unfold sem_pend_event_wait_cells, ready_frame; entailer!) end end.
    exact (Hclose ready_written Hready_post). }
  assert (Hfragment : forall after,
    (if Z.eqb (event_task_wait_ready_row ready_row bit_x) 0 then
      kernel_heap_execution [(ready_group, Z.land ready_grp (unsigned_last_nbits (Z.lnot bit_y) 8))] ready_written after
     else after = ready_written) ->
    sem_pend_event_wait_fragment current tcb pevent ready_group ready_table
      row bit_x bit_y event_row event_group ready_row ready_grp before after).
  { intros after Hlast; exists pointer_written, table_written, group_written, ready_written.
    repeat first [assumption | sem_pend_wait_read Hpre | sem_pend_wait_read Hp |
      sem_pend_wait_read Ht | sem_pend_wait_read Hg | sem_pend_wait_read Hr | split].
    destruct (Z.eqb (event_task_wait_ready_row ready_row bit_x) 0); [|exact Hlast].
    repeat first [exact Hlast | sem_pend_wait_read Hr | split]. }
  destruct (Z.eqb (event_task_wait_ready_row ready_row bit_x) 0) eqn:Hzero.
  - set (last_frame := current # Ptr |-> tcb ** &(tcb # "os_tcb" ->ₛ "OSTCBEventPtr") # Ptr |-> pevent **
      &(tcb # "os_tcb" ->ₛ "OSTCBY") # UChar |-> row **
      &(tcb # "os_tcb" ->ₛ "OSTCBBitX") # UChar |-> bit_x **
      &(tcb # "os_tcb" ->ₛ "OSTCBBitY") # UChar |-> bit_y **
      (&(pevent # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR)) # UChar |-> Z.lor event_row bit_x **
      &(pevent # "os_event" ->ₛ "OSEventGrp") # UChar |-> Z.lor event_group bit_y **
      (ready_table + row * sizeof(UCHAR)) # UChar |-> event_task_wait_ready_row ready_row bit_x ** frame).
    assert (Hlast : sem_pend_event_wait_cells current tcb pevent ready_group ready_table
        row bit_x bit_y pevent (Z.lor event_row bit_x) (Z.lor event_group bit_y)
        (event_task_wait_ready_row ready_row bit_x) ready_grp ** frame |-- ready_group # UChar |-> ready_grp ** last_frame).
    { unfold sem_pend_event_wait_cells, last_frame; entailer!. }
    destruct (kernel_heap_framed_uchar_store _ ready_grp
      (Z.land ready_grp (unsigned_last_nbits (Z.lnot bit_y) 8)) last_frame ready_written
      ltac:(apply sem_pend_byte_and_in_range; tauto) (Hlast ready_written Hr)) as [after [Hlast_run Hafter]].
    exists after; split; [apply Hfragment; exact Hlast_run|].
    match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { unfold event_task_wait_post, event_task_wait_ready_group, last_frame; rewrite Hzero; entailer!. }
    exact (Hclose after Hafter).
  - exists ready_written; split; [apply Hfragment; reflexivity|].
    match type of Hr with ?P ready_written => match goal with |- ?Q ready_written => assert (Hclose : P |-- Q) end end.
    { unfold event_task_wait_post, event_task_wait_ready_group, sem_pend_event_wait_cells; rewrite Hzero; entailer!. }
    exact (Hclose ready_written Hr).
Qed.

Lemma sem_pend_wait_event_address_in_range : forall sg entry eid current tid old,
  sem_pend_wait_entry sg entry eid current tid old ->
  0 <= event_addr sg eid < 4294967296.
Proof.
  intros sg entry eid current tid old [Hvalid [_ [_ [_ [Hlookup _]]]]].
  pose proof Hvalid as [Hprofile [_ [_ [[Hpartition _] _]]]].
  pose proof (proj1 (event_pool_used_not_free sg entry.(EventState) eid current Hpartition Hlookup)) as Hid.
  assert (Hregion : kernel_region_valid
    (sg.(g_OSEventTbl), event_object_size sg.(osKernelConfig) * sg.(osMaxEvents))).
  { apply valid_selected_kernel_global_layout_region with (sg := sg).
    - unfold selected_kernel_profile in Hprofile; tauto.
    - unfold selected_kernel_global_regions; cbn; tauto. }
  pose proof (event_object_size_positive sg.(osKernelConfig)) as Hsize.
  unfold kernel_region_valid in Hregion; cbn in Hregion.
  unfold valid_event_id in Hid; unfold event_addr, event_pool_addr; nia.
Qed.

Definition sem_pend_wait_fragment sg entry eid current tid old timeout (before after : model) : Prop :=
  exists prefix_written,
    sem_pend_wait_prefix_fragment sg timeout before prefix_written /\
    sem_pend_event_wait_fragment sg.(g_OSTCBCur) (task_slot_addr sg tid) (event_addr sg eid)
      sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) (old.(curPrio) / 8)
      (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
      (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
      (encode_event_wait_grp current.(waitList) entry.(TskState))
      (encode_ready_tbl_at_or entry.(SchedState).(readyList) entry.(TskState) (old.(curPrio) / 8))
      (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState)) prefix_written after.

(** Consume the pre-write cells, perform all actual C writes and take
    the EventWait zero-row branch only when its newly written byte is 0. *)
Lemma sem_pend_wait_stores_source : forall sg entry eid current tid old timeout (frame : Assertion) before,
  sem_pend_wait_entry sg entry eid current tid old -> 0 <= timeout < 4294967296 ->
  (sem_pend_wait_prefix_cells sg entry tid old (encode_task_status old.(stat))
    (encode_pend_status old.(statPend)) old.(dly) ** frame) before ->
  exists after,
    sem_pend_wait_fragment sg entry eid current tid old timeout before after /\
    (sem_pend_wait_call_post sg entry eid current tid old timeout ** frame) after.
Proof.
  intros sg entry eid current tid old timeout frame before Hentry Htimeout Hpre.
  destruct (sem_pend_wait_prefix_stores_source sg entry tid old timeout frame before Htimeout Hpre)
    as [prefix_written [Hprefix Hprefix_post]].
  set (call_frame := sem_pend_wait_call_frame sg entry eid current tid old timeout ** frame).
  assert (Hcall : sem_pend_wait_prefix_cells sg entry tid old (Z.lor (encode_task_status old.(stat)) 1) 0 timeout ** frame |--
    sem_pend_event_wait_cells sg.(g_OSTCBCur) (task_slot_addr sg tid) (event_addr sg eid)
      sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) (old.(curPrio) / 8)
      (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio)) 0
      (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
      (encode_event_wait_grp current.(waitList) entry.(TskState))
      (encode_ready_tbl_at_or entry.(SchedState).(readyList) entry.(TskState) (old.(curPrio) / 8))
      (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState)) ** call_frame).
  { unfold sem_pend_wait_prefix_cells.
    sep_apply_l_atomic (sem_pend_wait_prefix_split_call sg entry eid current tid old timeout Hentry).
    unfold sem_pend_event_wait_cells, call_frame; cbn [tcb_cell tcb_field_address]; entailer!. }
  destruct (sem_pend_event_wait_stores_source sg.(g_OSTCBCur) (task_slot_addr sg tid) (event_addr sg eid)
    sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) (old.(curPrio) / 8)
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio)) 0
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState))
    (encode_ready_tbl_at_or entry.(SchedState).(readyList) entry.(TskState) (old.(curPrio) / 8))
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState)) call_frame prefix_written
    (sem_pend_wait_entry_row_in_range sg entry eid current tid old Hentry)
    (sem_pend_wait_event_address_in_range sg entry eid current tid old Hentry)
    (Hcall prefix_written Hprefix_post)) as [after [Hwait Hafter]].
  exists after; split; [exists prefix_written; auto|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q)
    by (unfold sem_pend_wait_call_post, call_frame; entailer!) end end.
  exact (Hclose after Hafter).
Qed.

(** The first Restore consumes this exact returned call and the current
    blocked-state strong world, including parked ownership and coverage.
    The acquisition history remains segmented. In particular the caller
    is no longer ready here, and no future scheduler safety is required. *)
Lemma sem_pend_wait_first_restore_input : forall environment critical sg original before context saved
  entry eid current tid old timeout (frame : Assertion) heap,
  kernel_call_save_history environment critical sg original before context entry ->
  sem_pend_wait_entry sg entry eid current tid old ->
  kernel_call_task_source context entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  task_stack_live_coverage entry.(TskState) (task_stack_call_active_key context) ->
  0 <= timeout < 4294967296 ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
     context.(os_sched_call_origin) saved entry **
   os_sched_context_resources environment.(task_stack_call_external) context **
   sem_pend_wait_prefix_cells sg entry tid old (encode_task_status old.(stat))
     (encode_pend_status old.(statPend)) old.(dly) **
   armv7a_task_stack_continuations environment.(task_stack_call_continuations)
     entry.(TskState) entry.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame) heap ->
  exists waited,
    sem_pend_wait_fragment sg entry eid current tid old timeout heap waited /\
    kernel_call_save_history environment critical sg original before context entry /\
    sem_pend_first_critical sg eid timeout entry (SemPendWaiting tid old.(taskGeneration))
      (event_pend_state sg entry eid current tid old PendSem timeout) /\
    kernel_call_task_source context (event_pend_state sg entry eid current tid old PendSem timeout) /\
    sched_current_consistency (event_pend_state sg entry eid current tid old PendSem timeout).(TskState)
      (event_pend_state sg entry eid current tid old PendSem timeout).(SchedState) /\
    (task_tcb_init_stack_restore_input environment critical sg context saved entry
       (event_pend_state sg entry eid current tid old PendSem timeout) ** unmap_table_rep sg ** frame) waited.
Proof.
  intros environment critical sg original before context saved entry eid current tid old timeout frame heap
    Hhistory Hentry Hsource Hcache Hcoverage Htimeout Hpre.
  set (rest := critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) saved entry ** os_sched_context_resources environment.(task_stack_call_external) context **
    armv7a_task_stack_continuations environment.(task_stack_call_continuations)
      entry.(TskState) entry.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame).
  match type of Hpre with ?P heap => assert (Horder : P |--
    sem_pend_wait_prefix_cells sg entry tid old (encode_task_status old.(stat))
      (encode_pend_status old.(statPend)) old.(dly) ** rest) by (unfold rest; entailer!) end.
  destruct (sem_pend_wait_stores_source sg entry eid current tid old timeout rest heap
    Hentry Htimeout (Horder heap Hpre)) as [waited [Hrun Hafter]].
  pose proof (sem_pend_wait_preserves_call_source sg context entry eid current tid old timeout
    Hentry Hsource Hcache) as [Hvalid [Hwaiting Hwaiting_cache]].
  exists waited; split; [exact Hrun|]. split; [exact Hhistory|].
  split; [apply sem_pend_wait_entry_first_critical; exact Hentry|].
  split; [exact Hwaiting|]. split; [exact Hwaiting_cache|].
  match type of Hafter with ?P waited => match goal with |- ?Q waited => assert (Hclose : P |-- Q) end end.
  { eapply derivable1_trans with (y :=
      (critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
         context.(os_sched_call_origin) saved entry **
       os_sched_context_resources environment.(task_stack_call_external) context **
       sem_pend_wait_call_post sg entry eid current tid old timeout **
       armv7a_task_stack_continuations environment.(task_stack_call_continuations)
         entry.(TskState) entry.(TskState).(parkedTaskStacks)) ** (unmap_table_rep sg ** frame)).
    { unfold rest; entailer!. }
    sep_apply_l_atomic (sem_pend_wait_call_stack_merge_source _ _ _ environment.(task_stack_call_continuations)
      critical sg (task_stack_call_active_key context) context saved entry eid current tid old timeout
      Hentry Hsource Hcache Hcoverage).
    unfold task_tcb_init_stack_restore_input, task_tcb_init_stack_capsules,
      kernel_stack_call_masked, kernel_stack_inv; entailer!. }
  exact (Hclose waited Hafter).
Qed.

(** Actual uninterrupted first Restore suffix, for the exact input above.
    The resulting closed owner retains its current world and context;
    no projection into the legacy public post's TT is performed. *)
Lemma sem_pend_wait_first_restore_source : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg context saved acquired waiting cursor before written middle final_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (task_tcb_init_stack_restore_input environment critical sg context saved acquired waiting **
    unmap_table_rep sg ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  kernel_call_restore_history environment critical sg context waiting context waiting /\
  (kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv sg
    (task_stack_call_active_key context) context (armv7a_irq_fiq_mask saved) waiting ** frame) after.
Proof.
  intros environment critical arch restore sg context saved acquired waiting cursor before written middle
    final_cursor after frame Hr0 Hmask Hpre Hprefix Hsuffix.
  match type of Hpre with ?P before => assert (Hopen : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
      context.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) context **
    (kernel_stack_inv environment.(task_stack_call_continuations) kernel_program_inv sg
      (task_stack_call_active_key context) waiting ** frame)) end.
  { unfold task_tcb_init_stack_restore_input, task_tcb_init_stack_capsules, kernel_stack_inv.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg context saved
    acquired cursor before written middle final_cursor after _ Hr0 Hmask (Hopen before Hpre) Hprefix Hsuffix)
    as [Hexecution [Hreturn [Hmemory Hafter]]].
  split; [exact Hexecution|]. split; [exact Hreturn|]. split.
  - eapply KernelCallRestoreUninterrupted; eassumption.
  - match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q)
      by (unfold kernel_stack_call_closed; entailer!) end end.
    exact (Hclose after Hafter).
Qed.
