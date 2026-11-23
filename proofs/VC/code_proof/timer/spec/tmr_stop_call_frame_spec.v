Require Export Ucos2Verify.VC.code.timer.spec.tmr_stop_entry_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_stop_interrupt_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_unlink_spec.
Require Import Coq.ZArith.ZArith Coq.Strings.String.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Module TmrStopCallOldFrame.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

Lemma context_unlock_pre : forall external platform critical sg context mask before,
  os_sched_unlock_acquire_safety external critical sg context before ->
  mutex_query_spec.mutex_query_closed platform critical sg
    context.(os_sched_call_invocation) context.(os_sched_call_origin) mask before **
    (sched_spec.os_sched_context_resources external context ** sched.unmap_table_rep sg) |--
  sched_unlock_call_api_program_spec.os_sched_unlock_program_pre
    external platform critical sg context mask before (fun _ => True).
Proof.
  intros external platform critical sg context mask before Hready.
  assert (Hbase :
    mutex_query_spec.mutex_query_closed platform critical sg
      context.(os_sched_call_invocation) context.(os_sched_call_origin) mask before **
      (sched_spec.os_sched_context_resources external context ** sched.unmap_table_rep sg) |--
    coq_prop (UCOS2_state_inv sg before /\
      os_sched_unlock_acquire_safety external critical sg context before) &&
    os_sched_unlock_outside_frame external platform critical sg context mask before).
  { unfold mutex_query_spec.mutex_query_closed, os_sched_unlock_outside_frame. entailer!. }
  intros heap Hcontext. split.
  - exists before. split; [reflexivity|].
    unfold safe, StateRelHoare.weakestpre. hnf; intros; exact I.
  - apply (proj2 (os_sched_unlock_pre_closed_equiv external platform critical sg
      context mask before) heap). exact (Hbase heap Hcontext).
Qed.
End TmrStopCallOldFrame.

Lemma tmr_stop_call_context_unlock_pre : forall external platform critical sg mask context before,
  os_sched_unlock_acquire_safety external critical sg context before ->
  TmrStopRules.derivable1
    (tmr_stop_context_rep external platform critical sg mask context before)
    (TimerCalleeLift.os_sched_unlock_program_pre external platform critical sg
      context mask before (fun _ => True)).
Proof.
  intros external platform critical sg mask context before Hready heap Hcontext.
  pose proof (proj1 (TimerCalleeLift.os_sched_closed_resources_lift external platform
    critical sg context mask before) heap Hcontext) as Hold.
  exact (TmrStopRules.lift_entailment _ _
    (TmrStopCallOldFrame.context_unlock_pre external platform critical sg context mask
      before Hready) heap Hold).
Qed.

(** Concrete application protocol for clients whose resources are the
    disjoint frame of the EXISTING Lock/Unlock contracts.  The callback is
    still an arbitrary supplied program; it may change kernel, application,
    context and the one output byte.  These equalities describe the frame
    of Lock/Unlock only, and assert nothing about callback behaviour. *)
Definition tmr_stop_call_effects {Application : Type}
  (callback : Z -> Z -> Z -> OsSchedCallContext ->
    StateRelMonad.M (TmrStopState Application) OsSchedCallContext)
  : TmrStopEffects Application :=
  {| tmr_stop_lock_application := fun _ before after =>
       after.(tmr_stop_error) = before.(tmr_stop_error) /\
       after.(tmr_stop_application) = before.(tmr_stop_application);
     tmr_stop_unlock_application := fun _ before _ after =>
       after.(tmr_stop_error) = before.(tmr_stop_error) /\
       after.(tmr_stop_application) = before.(tmr_stop_application);
     tmr_stop_callback := callback |}.

Lemma tmr_stop_call_lock_application : forall (Application : Type) callback
  context (before : TmrStopState Application) kernel,
  tmr_stop_lock_application (tmr_stop_call_effects callback) context before
    (tmr_stop_set_kernel kernel before).
Proof. intros; split; reflexivity. Qed.

Lemma tmr_stop_call_unlock_application : forall (Application : Type) callback
  context returned (before : TmrStopState Application) kernel,
  tmr_stop_unlock_application (tmr_stop_call_effects callback) context before returned
    (tmr_stop_set_kernel kernel before).
Proof. intros; split; reflexivity. Qed.

(** Raw observations have their own represented application fields, rather
    than being arbitrary functions of the error ghost.  Client remains
    arbitrary and its representation may contain further application cells.
    The output cell is deliberately absent from this record/representation.
    A callback argument equal to perr still denotes the existing one cell. *)
Record TmrStopCallApplication (Client : Type) : Type := {
  tmr_stop_call_type_byte : Z;
  tmr_stop_call_state_byte : Z;
  tmr_stop_call_client : Client
}.
Arguments tmr_stop_call_type_byte {Client} _.
Arguments tmr_stop_call_state_byte {Client} _.
Arguments tmr_stop_call_client {Client} _.

Definition tmr_stop_call_application_rep {Client : Type}
  (ClientRep : Client -> TmrStopRules.expr) (pooled : bool)
  (pointer nesting : Z) (current : TmrStopCallApplication Client)
  : TmrStopRules.expr :=
  if pooled then ClientRep current.(tmr_stop_call_client)
  else TmrStopRules.sepcon
    (tmr_stop_raw_rep pointer current.(tmr_stop_call_type_byte) nesting
      current.(tmr_stop_call_state_byte))
    (ClientRep current.(tmr_stop_call_client)).

Definition tmr_stop_call_raw_type {Client : Type}
  (current : TmrStopState (TmrStopCallApplication Client)) : Z :=
  current.(tmr_stop_application).(tmr_stop_call_type_byte).

Definition tmr_stop_call_raw_state {Client : Type}
  (current : TmrStopState (TmrStopCallApplication Client)) : Z :=
  current.(tmr_stop_application).(tmr_stop_call_state_byte).

Lemma tmr_stop_call_raw_type_set_error : forall (Client : Type) error
  (current : TmrStopState (TmrStopCallApplication Client)),
  tmr_stop_call_raw_type (tmr_stop_set_error error current) =
    tmr_stop_call_raw_type current.
Proof. reflexivity. Qed.

Lemma tmr_stop_call_raw_state_set_error : forall (Client : Type) error
  (current : TmrStopState (TmrStopCallApplication Client)),
  tmr_stop_call_raw_state (tmr_stop_set_error error current) =
    tmr_stop_call_raw_state current.
Proof. reflexivity. Qed.

Lemma tmr_stop_call_raw_type_set_kernel : forall (Client : Type) kernel
  (current : TmrStopState (TmrStopCallApplication Client)),
  tmr_stop_call_raw_type (tmr_stop_set_kernel kernel current) =
    tmr_stop_call_raw_type current.
Proof. reflexivity. Qed.

Lemma tmr_stop_call_raw_state_set_kernel : forall (Client : Type) kernel
  (current : TmrStopState (TmrStopCallApplication Client)),
  tmr_stop_call_raw_state (tmr_stop_set_kernel kernel current) =
    tmr_stop_call_raw_state current.
Proof. reflexivity. Qed.

Lemma tmr_stop_call_application_raw_type : forall (Client : Type)
  (ClientRep : Client -> TmrStopRules.expr) pointer nesting
  (current : TmrStopCallApplication Client),
  pointer <> 0 ->
  tmr_stop_call_application_rep ClientRep false pointer nesting current =
    TmrStopRules.sepcon
      (TmrStopRules.sepcon
        (TmrStopRules.store_uchar (tmr_unlink_timer_field pointer "OSTmrType")
          current.(tmr_stop_call_type_byte))
        (tmr_stop_raw_state_rep pointer current.(tmr_stop_call_type_byte)
          nesting current.(tmr_stop_call_state_byte)))
      (ClientRep current.(tmr_stop_call_client)).
Proof.
  intros Client ClientRep pointer nesting current Hpointer.
  unfold tmr_stop_call_application_rep.
  rewrite tmr_stop_raw_rep_nonnull by exact Hpointer. reflexivity.
Qed.

Lemma tmr_stop_call_application_raw_state : forall (Client : Type)
  (ClientRep : Client -> TmrStopRules.expr) pointer nesting
  (current : TmrStopCallApplication Client),
  pointer <> 0 -> current.(tmr_stop_call_type_byte) = 100 -> nesting <= 0 ->
  tmr_stop_call_application_rep ClientRep false pointer nesting current =
    TmrStopRules.sepcon
      (TmrStopRules.sepcon
        (TmrStopRules.store_uchar (tmr_unlink_timer_field pointer "OSTmrType") 100)
        (TmrStopRules.store_uchar (tmr_unlink_timer_field pointer "OSTmrState")
          current.(tmr_stop_call_state_byte)))
      (ClientRep current.(tmr_stop_call_client)).
Proof.
  intros Client ClientRep pointer nesting current Hpointer Htype Hnesting.
  rewrite tmr_stop_call_application_raw_type by exact Hpointer.
  rewrite Htype, tmr_stop_raw_state_rep_enabled by exact Hnesting. reflexivity.
Qed.

(** Prefixes up to the first output store use entry_client_rep.  These
    cutpoints are the actual callee pre/post with that frame; they do not
    assert an additional C execution relation.  Kernel Xk=True is internal
    to the reused callee.  The public, arbitrary X is retained by the
    *_continue lemma and is never specialized to True. *)
Section StopCallFrame.
Context {Application : Type} (AppRep : Application -> TmrStopRules.expr).
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (mask perr : Z).

Definition tmr_stop_call_lock_pre (context : OsSchedCallContext)
  (before : TmrStopState Application) : TmrStopRules.expr :=
  TmrStopRules.sepcon
    (TmrStopRules.sepcon
      (TimerCalleeLift.os_sched_lock_program_pre platform critical sg
        context.(os_sched_call_invocation) context.(os_sched_call_origin) mask
        before.(tmr_stop_kernel) (fun _ => True))
      (TmrStopRules.sepcon (TimerCalleeLift.os_sched_context_resources external context)
        (TimerCalleeLift.unmap_table_rep sg)))
    (tmr_stop_entry_client_rep AppRep perr before).

Definition tmr_stop_call_lock_post (context : OsSchedCallContext)
  (before : TmrStopState Application) : TmrStopRules.expr :=
  TmrStopRules.sepcon
    (TmrStopRules.sepcon
      (TimerCalleeLift.os_sched_lock_program_post platform critical sg
        context.(os_sched_call_invocation) context.(os_sched_call_origin) mask
        before.(tmr_stop_kernel) (fun _ => True))
      (TmrStopRules.sepcon (TimerCalleeLift.os_sched_context_resources external context)
        (TimerCalleeLift.unmap_table_rep sg)))
    (tmr_stop_entry_client_rep AppRep perr before).

Lemma tmr_stop_call_lock_pre_open : forall context (before : TmrStopState Application),
  TmrStopRules.derivable1
    (tmr_stop_entry_owned AppRep external platform critical sg mask perr context before)
    (tmr_stop_call_lock_pre context before).
Proof.
  intros context before heap
    [context_heap [client_heap [Hwhole
      [[kernel_heap [stack_heap [Hcontext [Hkernel Hstack]]]] Hclient]]]].
  exists context_heap, client_heap. split; [exact Hwhole|]. split; [|exact Hclient].
  exists kernel_heap, stack_heap. split; [exact Hcontext|]. split; [|exact Hstack].
  split.
  - exists before.(tmr_stop_kernel). split; [reflexivity|].
    unfold safe, StateRelHoare.weakestpre. hnf; intros; exact I.
  - exact (proj2 (os_sched_lock_pre_closed_equiv platform critical sg
      context.(os_sched_call_invocation) context.(os_sched_call_origin) mask
      before.(tmr_stop_kernel)) (fst kernel_heap) Hkernel).
Qed.

Lemma tmr_stop_call_lock_post_continue : forall (Result : Type) callback context
  (before : TmrStopState Application)
  (next : unit -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop),
  safeExec (eq before)
    (StateRelMonad.bind
      (tmr_stop_lock_program critical sg (tmr_stop_call_effects callback) context) next) X ->
  TmrStopRules.derivable1 (tmr_stop_call_lock_post context before)
    (fun heap => exists after,
      tmr_stop_lock_program critical sg (tmr_stop_call_effects callback) context before tt after /\
      safeExec (eq after) (next tt) X /\
      tmr_stop_entry_owned AppRep external platform critical sg mask perr context after heap).
Proof.
  intros Result callback context before next X Hsafe.
  apply (tmr_stop_entry_lock_frame AppRep external platform critical sg
    (tmr_stop_call_effects callback) mask perr Result context before next X).
  - intros entry kernel Hcall. apply tmr_stop_call_lock_application.
  - exact Hsafe.
Qed.

Definition tmr_stop_call_unlock_pre (context : OsSchedCallContext)
  (before : TmrStopState Application) : TmrStopRules.expr :=
  TmrStopRules.sepcon
    (TimerCalleeLift.os_sched_unlock_program_pre external platform critical sg
      context mask before.(tmr_stop_kernel) (fun _ => True))
    (tmr_stop_entry_client_rep AppRep perr before).

Definition tmr_stop_call_unlock_post (context : OsSchedCallContext)
  (before : TmrStopState Application) : TmrStopRules.expr :=
  TmrStopRules.sepcon
    (TimerCalleeLift.os_sched_unlock_program_post external platform critical sg
      context mask before.(tmr_stop_kernel) (fun _ => True))
    (tmr_stop_entry_client_rep AppRep perr before).

Lemma tmr_stop_call_unlock_pre_open : forall context (before : TmrStopState Application),
  os_sched_unlock_acquire_safety external critical sg context before.(tmr_stop_kernel) ->
  TmrStopRules.derivable1
    (tmr_stop_entry_owned AppRep external platform critical sg mask perr context before)
    (tmr_stop_call_unlock_pre context before).
Proof.
  intros context before Hready heap [context_heap [client_heap [Hjoin [Hcontext Hclient]]]].
  exists context_heap, client_heap. split; [exact Hjoin|]. split; [|exact Hclient].
  exact (tmr_stop_call_context_unlock_pre external platform critical sg mask context
    before.(tmr_stop_kernel) Hready context_heap Hcontext).
Qed.

Lemma tmr_stop_call_unlock_post_continue : forall (Result : Type) callback context
  (before : TmrStopState Application)
  (next : OsSchedCallContext -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop),
  os_sched_unlock_acquire_safety external critical sg context before.(tmr_stop_kernel) ->
  safeExec (eq before)
    (StateRelMonad.bind
      (tmr_stop_unlock_program external critical sg (tmr_stop_call_effects callback) context)
      next) X ->
  TmrStopRules.derivable1 (tmr_stop_call_unlock_post context before)
    (fun heap => exists returned after,
      tmr_stop_unlock_program external critical sg (tmr_stop_call_effects callback)
        context before returned after /\
      safeExec (eq after) (next returned) X /\
      tmr_stop_entry_owned AppRep external platform critical sg mask perr returned after heap).
Proof.
  intros Result callback context before next X Hready Hsafe.
  apply (tmr_stop_entry_unlock_frame AppRep external platform critical sg
    (tmr_stop_call_effects callback) mask perr Result context before next X).
  - exact Hready.
  - intros returned kernel Hcall. apply tmr_stop_call_unlock_application.
  - exact Hsafe.
Qed.

(** The same real field split/merge is needed before the first store.
    Existing owned_field_view is for an initialized output byte. *)
Definition tmr_stop_call_entry_field_view (context : OsSchedCallContext)
  (before : TmrStopState Application) (index : Z) (image : TimerImage) (field : TmrStopField)
  : TmrStopRules.expr :=
  TmrStopRules.sepcon
    (TmrStopRules.sepcon (tmr_stop_field_cell (timer_pool_addr sg index) image field)
      (TmrStopRules.lift (TmrStopOldFields.context_without_field external platform sg
        context mask before.(tmr_stop_kernel) index image field)))
    (tmr_stop_entry_client_rep AppRep perr before).

Lemma tmr_stop_call_entry_split_field : forall context
  (before : TmrStopState Application) index image field,
  tmr_stop_fields_layout -> sg.(osKernelConfig).(cfgTimerNames) = true ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_api_initialized before.(tmr_stop_kernel).(TimerState) ->
  before.(tmr_stop_kernel).(TimerState).(timerImages) index = Some image ->
  TmrStopRules.derivable1
    (tmr_stop_entry_owned AppRep external platform critical sg mask perr context before)
    (tmr_stop_call_entry_field_view context before index image field).
Proof.
  intros context before index image field Hlayout Hnames Henabled Hinit Himage heap
    [context_heap [client_heap [Hjoin [Hcontext Hclient]]]].
  exists context_heap, client_heap. split; [exact Hjoin|]. split; [|exact Hclient].
  apply (tmr_stop_field_split_lift _ _ _ _ _
    (TmrStopOldFields.context_rep_split_field external platform critical sg context mask
      before.(tmr_stop_kernel) index image field Hlayout Hnames Henabled Hinit Himage) context_heap).
  exact (proj1 (TimerCalleeLift.os_sched_closed_resources_lift external platform critical sg
    context mask before.(tmr_stop_kernel)) context_heap Hcontext).
Qed.

Lemma tmr_stop_call_entry_merge_field : forall context
  (before : TmrStopState Application) index image field,
  tmr_stop_fields_layout -> sg.(osKernelConfig).(cfgTimerNames) = true ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_api_initialized before.(tmr_stop_kernel).(TimerState) ->
  before.(tmr_stop_kernel).(TimerState).(timerImages) index = Some image ->
  TmrStopRules.derivable1 (tmr_stop_call_entry_field_view context before index image field)
    (tmr_stop_entry_owned AppRep external platform critical sg mask perr context before).
Proof.
  intros context before index image field Hlayout Hnames Henabled Hinit Himage heap
    [context_heap [client_heap [Hjoin [Hfields Hclient]]]].
  exists context_heap, client_heap. split; [exact Hjoin|]. split; [|exact Hclient].
  apply (proj2 (TimerCalleeLift.os_sched_closed_resources_lift external platform critical sg
    context mask before.(tmr_stop_kernel)) context_heap).
  exact (tmr_stop_field_merge_lift _ _ _ _ _
    (TmrStopOldFields.context_rep_merge_field external platform critical sg context mask
      before.(tmr_stop_kernel) index image field Hlayout Hnames Henabled Hinit Himage)
    context_heap Hfields).
Qed.

Lemma tmr_stop_call_entry_split_timer : forall context (before : TmrStopState Application),
  TmrStopRules.derivable1
    (tmr_stop_entry_owned AppRep external platform critical sg mask perr context before)
    (TmrStopRules.sepcon
      (TmrStopRules.sepcon (TimerCalleeLift.timer_inv sg before.(tmr_stop_kernel).(TimerState))
        (tmr_stop_unlink_frame external platform sg mask context before))
      (tmr_stop_entry_client_rep AppRep perr before)).
Proof.
  intros context before heap [context_heap [client_heap [Hjoin [Hcontext Hclient]]]].
  exists context_heap, client_heap. split; [exact Hjoin|]. split; [|exact Hclient].
  apply (proj1 (TmrStopRules.lift_sepcon _ _ context_heap)).
  apply (TmrStopRules.lift_entailment _ _
    (TmrStopOldFields.context_rep_split_timer external platform critical sg context mask
      before.(tmr_stop_kernel)) context_heap).
  exact (proj1 (TimerCalleeLift.os_sched_closed_resources_lift external platform critical sg
    context mask before.(tmr_stop_kernel)) context_heap Hcontext).
Qed.
End StopCallFrame.
