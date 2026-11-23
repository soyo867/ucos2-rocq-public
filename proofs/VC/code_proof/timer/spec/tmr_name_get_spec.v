Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_call_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_name_get_spec.
Require Export Ucos2Verify.lib.timer.
Require Export Ucos2Verify.lib.timer_execution.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Raw fields belong to the caller; a configured view refers to the single
    shared pool owner. The raw view admits invalid Type/State bytes and NULL
    names. Its name storage is required only on the actual StrLen branch. *)
Inductive TmrNameGetView : Type :=
| TmrNameGetRaw (kind status name : Z) (names : NameResourceState) (chars : list Z)
| TmrNameGetPool (slot : TimerID).

Definition tmr_name_get_type view (s : UCOS2_Verify_State) : Z :=
  match view with
  | TmrNameGetRaw kind _ _ _ _ => kind
  | TmrNameGetPool i => match s.(TimerState).(timerImages) i with
    | Some v => v.(timerImageType) | None => 0 end
  end.
Definition tmr_name_get_state view (s : UCOS2_Verify_State) : Z :=
  match view with
  | TmrNameGetRaw _ status _ _ _ => status
  | TmrNameGetPool i => match s.(TimerState).(timerImages) i with
    | Some v => v.(timerImageState) | None => 0 end
  end.
Definition tmr_name_get_name view (s : UCOS2_Verify_State) : Z :=
  match view with
  | TmrNameGetRaw _ _ name _ _ => name
  | TmrNameGetPool i => match s.(TimerState).(timerImages) i with
    | Some v => v.(timerImageName) | None => 0 end
  end.
Definition tmr_name_get_names view (s : UCOS2_Verify_State) : NameResourceState :=
  match view with TmrNameGetRaw _ _ _ names _ => names | TmrNameGetPool _ => s.(NameState) end.
Definition tmr_name_get_successful (status : Z) : bool :=
  ((status =? 1) || (status =? 2) || (status =? 3))%bool.
Definition tmr_name_get_early_error view (p dest : Z) (s : UCOS2_Verify_State) : option Z :=
  if dest =? 0 then Some 136 else if p =? 0 then Some 138
  else if negb (tmr_name_get_type view s =? 100) then Some 137
  else if 0 <? s.(IntrState).(intNesting) then Some 17 else None.
Definition tmr_name_get_layout (sg : StableGlobVars) (p type_addr name_addr state_addr ints : Z) : Prop :=
  type_addr = p /\ name_addr = p + 32 /\ state_addr = p + 37 /\
  ints = sg.(g_OSIntNesting) /\ sg.(osKernelConfig).(cfgTimerEnabled) = true /\
  sg.(osKernelConfig).(cfgTimerNames) = true.
Definition tmr_name_get_view_present sg view p (s : UCOS2_Verify_State) : Prop :=
  match view with
  | TmrNameGetRaw _ _ _ _ _ => True
  | TmrNameGetPool i => p = timer_pool_addr sg i /\ timer_api_initialized s.(TimerState) /\
      exists v, s.(TimerState).(timerImages) i = Some v
  end.
Definition tmr_name_get_name_readable view (s : UCOS2_Verify_State) (chars : list Z) : Prop :=
  match view with
  | TmrNameGetRaw _ _ name names raw_chars =>
      chars = raw_chars /\ (name <> 0 -> readable_name names name chars)
  | TmrNameGetPool _ =>
      tmr_name_get_name view s <> 0 -> readable_name s.(NameState) (tmr_name_get_name view s) chars
  end.

Definition tmr_name_get_closed platform critical sg (context : OsSchedCallContext) mask s :=
  task_name_get_closed platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask s.
Definition tmr_name_get_continuation external sg (context : OsSchedCallContext) : Assertion :=
  os_sched_context_resources external context ** unmap_table_rep sg.
Definition tmr_name_get_raw_tail view p (before : UCOS2_Verify_State) : Assertion :=
  match view with
  | TmrNameGetRaw kind status name names chars =>
    if ((kind =? 100) && (before.(IntrState).(intNesting) =? 0))%bool then
      (p + 37) # UChar |-> status **
      (if tmr_name_get_successful status then
        coq_prop (name <> 0 -> readable_name names name chars) &&
        ((p + 32) # Ptr |-> name ** task_name_get_name_bytes name chars)
       else emp)
    else emp
  | TmrNameGetPool _ => emp
  end.
Definition tmr_name_get_private view p dest before : Assertion :=
  if ((dest =? 0) || (p =? 0))%bool then emp else
  match view with
  | TmrNameGetRaw kind _ _ _ _ => p # UChar |-> kind ** tmr_name_get_raw_tail view p before
  | TmrNameGetPool _ => emp
  end.
Definition tmr_name_get_extra external sg context view p dest before : Assertion :=
  match tmr_name_get_early_error view p dest before with
  | Some _ => emp | None => tmr_name_get_continuation external sg context end.
Definition tmr_name_get_resources external platform critical sg context mask view p dest before : Assertion :=
  tmr_name_get_closed platform critical sg context mask before **
  tmr_name_get_private view p dest before **
  tmr_name_get_extra external sg context view p dest before.

(** Caller/source protocol at precisely the Lock endpoint. It is not a
    Timer validity theorem, an IRQ guarantee, or a termination hypothesis. *)
Definition tmr_name_get_access external critical sg (context : OsSchedCallContext)
  view p dest before (old : option Z) : Prop :=
  tmr_name_get_early_error view p dest before = None ->
  forall entry locked,
    os_sched_lock_call_relation critical sg context.(os_sched_call_invocation) before entry locked ->
    os_sched_unlock_acquire_safety external critical sg context locked /\
    (tmr_name_get_successful (tmr_name_get_state view locked) = true ->
      exists previous, old = Some previous).

Record TmrNameGetObservation : Type := tmr_name_get_observation {
  tmr_name_get_length_observed : Z;
  tmr_name_get_error_observed : Z;
  tmr_name_get_output_observed : option Z
}.
Definition TmrNameGetPost := TmrNameGetObservation -> UCOS2_Verify_State -> Prop.

(** A parser-facing folding of the delivered StrLen source_spec. Both
    branches and all ghost parameters are retained verbatim semantically. *)
Definition tmr_name_get_strlen_pre entry base psrc names chars (frame : Assertion) : Assertion :=
  coq_prop (psrc = entry) &&
  ((coq_prop (psrc = 0) && frame) ||
   (coq_prop (psrc <> 0 /\ psrc = base /\ readable_name names psrc chars) &&
    (os_strlen_bytes psrc chars ** frame))).
Definition tmr_name_get_strlen_post entry base chars result (frame : Assertion) : Assertion :=
  (coq_prop (entry = 0 /\ result = 0) && frame) ||
  (coq_prop (entry <> 0 /\ entry = base /\ os_strlen_result chars result) &&
   (os_strlen_bytes entry chars ** frame)).
Lemma tmr_name_get_strlen_pre_source : forall entry base psrc names chars frame,
  tmr_name_get_strlen_pre entry base psrc names chars frame --||--
  (coq_prop (psrc = entry) &&
   ((coq_prop (psrc = 0) && frame) ||
    (coq_prop (psrc <> 0 /\ psrc = base) && coq_prop (readable_name names psrc chars) &&
     (os_strlen_bytes psrc chars ** frame)))).
Proof.
  intros; unfold tmr_name_get_strlen_pre.
  split; apply derivable1s_andp_mono; try reflexivity;
    apply derivable1_orp_elim; Intros.
  - Left; entailer!.
  - Right; entailer!.
  - Left; entailer!.
  - Right; entailer!.
Qed.
Lemma tmr_name_get_strlen_post_source : forall entry base chars result frame,
  tmr_name_get_strlen_post entry base chars result frame --||--
  ((coq_prop (entry = 0 /\ result = 0) && frame) ||
   (coq_prop (entry <> 0 /\ entry = base) && coq_prop (os_strlen_result chars result) &&
    (os_strlen_bytes entry chars ** frame))).
Proof.
  intros; unfold tmr_name_get_strlen_post.
  split; apply derivable1_orp_elim; Intros.
  - Left; entailer!.
  - Right; entailer!.
  - Left; entailer!.
  - Right; entailer!.
Qed.

(** Exactly the normal-return cases of the real Unlock post, including
    Scheduler's separate acquisition and returned original continuation. *)
Definition tmr_name_get_unlock_relation external critical sg (context : OsSchedCallContext)
  before returned current : Prop :=
  (before.(SchedState).(isRunning) = false /\ returned = context /\ current = before) \/
  (exists entry, before.(SchedState).(isRunning) = true /\
    critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
    if os_sched_unlock_requests entry then
      exists acquired,
        critical_region_interval critical sg context.(os_sched_call_invocation)
          (os_sched_unlock_checkpoint true entry) acquired /\
        os_sched_c_return external critical sg acquired context returned current
    else returned = context /\ current = os_sched_unlock_checkpoint true entry).
Definition tmr_name_get_unlock_program external critical sg context
  : program UCOS2_Verify_State OsSchedCallContext :=
  fun before returned current => tmr_name_get_unlock_relation external critical sg context before returned current.
Definition tmr_name_get_observe_program view : program UCOS2_Verify_State TmrNameGetObservation :=
  StateRelMonad.bind (get' (tmr_name_get_state view)) (fun status =>
    if tmr_name_get_successful status then
      StateRelMonad.bind (get (tmr_name_get_name_readable view)) (fun chars =>
        StateRelMonad.bind (get' (tmr_name_get_name view)) (fun name =>
          StateRelMonad.ret (tmr_name_get_observation (task_name_get_length name chars) 0 (Some name))))
    else StateRelMonad.ret (tmr_name_get_observation 0 (if status =? 0 then 135 else 141) None)).
Definition tmr_name_get_program external critical sg (context : OsSchedCallContext) view p dest
  : program UCOS2_Verify_State TmrNameGetObservation :=
  StateRelMonad.bind (get' (tmr_name_get_early_error view p dest)) (fun early =>
    match early with
    | Some error => StateRelMonad.ret (tmr_name_get_observation 0 error None)
    | None => StateRelMonad.bind
        (update (fun before locked => exists entry,
          os_sched_lock_call_relation critical sg context.(os_sched_call_invocation) before entry locked))
        (fun _ => StateRelMonad.bind (tmr_name_get_observe_program view) (fun observed =>
          StateRelMonad.bind (tmr_name_get_unlock_program external critical sg context)
            (fun _ => StateRelMonad.ret observed)))
    end).
Definition tmr_name_get_safe external critical sg context view p dest before (X : TmrNameGetPost) :=
  safeExec (fun state => state = before) (tmr_name_get_program external critical sg context view p dest) X.
Definition tmr_name_get_return_safe current len error output (X : TmrNameGetPost) :=
  safeExec (fun state => state = current)
    (StateRelMonad.ret (tmr_name_get_observation len error output)) X.

Definition tmr_name_get_entry_facts external critical sg context view p dest before old X : Prop :=
  UCOS2_state_inv sg before /\
    (p <> 0 -> dest <> 0 -> tmr_name_get_view_present sg view p before) /\
    tmr_name_get_access external critical sg context view p dest before old /\
    tmr_name_get_safe external critical sg context view p dest before X.
Definition tmr_name_get_lock_facts external critical sg context view p dest before old X locked : Prop :=
  tmr_name_get_entry_facts external critical sg context view p dest before old X /\
  tmr_name_get_early_error view p dest before = None /\
  before.(IntrState).(intNesting) = 0 /\
  (exists entry, os_sched_lock_call_relation critical sg context.(os_sched_call_invocation) before entry locked) /\
  UCOS2_state_inv sg locked /\ tmr_name_get_view_present sg view p locked /\
  os_sched_unlock_acquire_safety external critical sg context locked.
Definition tmr_name_get_pre external platform critical sg context mask view p dest before old X : Assertion :=
  coq_prop (tmr_name_get_entry_facts external critical sg context view p dest before old X) &&
  tmr_name_get_resources external platform critical sg context mask view p dest before.

Definition tmr_name_get_output dest old output : Assertion :=
  task_name_get_output_cell dest (match output with None => old | Some name => Some name end).
Definition tmr_name_get_post external platform critical sg context mask view p dest perr before old len X : Assertion :=
  (EX error,
    coq_prop (tmr_name_get_early_error view p dest before = Some error /\ len = 0 /\
      tmr_name_get_return_safe before len error None X) &&
    (tmr_name_get_resources external platform critical sg context mask view p dest before **
     task_name_get_output_cell dest old ** perr # UChar |-> error)) ||
  (EX locked, EX returned, EX current, EX error, EX output,
    coq_prop (tmr_name_get_early_error view p dest before = None /\
      (exists entry, os_sched_lock_call_relation critical sg context.(os_sched_call_invocation) before entry locked) /\
      tmr_name_get_observe_program view locked (tmr_name_get_observation len error output) locked /\
      tmr_name_get_unlock_relation external critical sg context locked returned current /\
      tmr_name_get_return_safe current len error output X) &&
    (tmr_name_get_closed platform critical sg context mask current **
     tmr_name_get_continuation external sg returned **
     tmr_name_get_private view p dest before **
     tmr_name_get_output dest old output ** perr # UChar |-> error)).

(** Exact source-backed residuals for reads. In particular the real padding,
    non-target pool objects and all other kernel modules remain owned. *)
Definition tmr_name_get_pool_rest sg (s : UCOS2_Verify_State) i : Assertion :=
  timer_images_without sg s.(TimerState) i **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) s.(TimerState).(timerWheel) **
  timer_globals_rep sg s.(TimerState) ** UCOS2_raw_rep_missing_timer sg s.
Definition tmr_name_get_type_rest external platform critical sg context mask view p dest before : Assertion :=
  (match view with
   | TmrNameGetRaw _ _ _ _ _ =>
       tmr_name_get_closed platform critical sg context mask before ** tmr_name_get_raw_tail view p before
   | TmrNameGetPool i => EX v,
       coq_prop (p = timer_pool_addr sg i /\ before.(TimerState).(timerImages) i = Some v) &&
       (interrupt_platform_running platform context.(os_sched_call_invocation) context.(os_sched_call_origin) mask **
        timer_object_rep_without_type sg.(osKernelConfig) p v ** tmr_name_get_pool_rest sg before i)
   end) ** tmr_name_get_extra external sg context view p dest before.
Definition tmr_name_get_int_rest external platform sg context mask view p dest before : Assertion :=
  interrupt_platform_running platform context.(os_sched_call_invocation) context.(os_sched_call_origin) mask **
  sg.(g_OSLockNesting) # UChar |-> before.(IntrState).(lockNesting) **
  UCOS2_raw_rep_missing_interrupt sg before **
  tmr_name_get_private view p dest before ** tmr_name_get_extra external sg context view p dest before.
Definition tmr_name_get_locked external platform critical sg context mask view p dest before locked : Assertion :=
  coq_prop (UCOS2_state_inv sg locked /\ tmr_name_get_view_present sg view p locked) &&
  (tmr_name_get_closed platform critical sg context mask locked **
   tmr_name_get_continuation external sg context ** tmr_name_get_private view p dest before).
Definition tmr_name_get_state_rest external platform critical sg context mask view p (dest : Z) (before : UCOS2_Verify_State) locked : Assertion :=
  (match view with
   | TmrNameGetRaw kind status name names chars =>
       tmr_name_get_closed platform critical sg context mask locked ** p # UChar |-> kind **
       (if tmr_name_get_successful status then
          coq_prop (name <> 0 -> readable_name names name chars) &&
          ((p + 32) # Ptr |-> name ** task_name_get_name_bytes name chars) else emp)
   | TmrNameGetPool i => EX v,
       coq_prop (p = timer_pool_addr sg i /\ locked.(TimerState).(timerImages) i = Some v) &&
       (interrupt_platform_running platform context.(os_sched_call_invocation) context.(os_sched_call_origin) mask **
        timer_object_rep_without_state sg.(osKernelConfig) p v ** tmr_name_get_pool_rest sg locked i)
   end) ** tmr_name_get_continuation external sg context.
Definition tmr_name_get_object_without_name (c : KernelConfiguration) p (v : TimerImage) : Assertion :=
  p # UChar |-> v.(timerImageType) **
  store_optional_bytes (p + 1) (firstn 3 v.(timerImagePadding)) **
  (p + 4) # Ptr |-> v.(timerImageCallback) ** (p + 8) # Ptr |-> v.(timerImageArg) **
  (p + 12) # Ptr |-> v.(timerImageNext) ** (p + 16) # Ptr |-> v.(timerImagePrev) **
  (p + 20) # UInt |-> v.(timerImageMatch) ** (p + 24) # UInt |-> v.(timerImageDelay) **
  (p + 28) # UInt |-> v.(timerImagePeriod) **
  (p + timer_option_offset c) # UChar |-> v.(timerImageOption) **
  (p + timer_option_offset c + 1) # UChar |-> v.(timerImageState) **
  store_optional_bytes (p + timer_option_offset c + 2) (skipn 3 v.(timerImagePadding)).
Definition tmr_name_get_name_rest external platform critical sg context mask view p (dest : Z) (before : UCOS2_Verify_State) locked : Assertion :=
  (match view with
   | TmrNameGetRaw kind status name names chars =>
       tmr_name_get_closed platform critical sg context mask locked ** p # UChar |-> kind **
       (p + 37) # UChar |-> status ** task_name_get_name_bytes name chars
   | TmrNameGetPool i => EX v,
       coq_prop (p = timer_pool_addr sg i /\ locked.(TimerState).(timerImages) i = Some v) &&
       (interrupt_platform_running platform context.(os_sched_call_invocation) context.(os_sched_call_origin) mask **
        tmr_name_get_object_without_name sg.(osKernelConfig) p v ** tmr_name_get_pool_rest sg locked i)
   end) ** tmr_name_get_continuation external sg context.
Definition tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars : Assertion :=
  (match view with
   | TmrNameGetRaw kind status name names raw_chars =>
       tmr_name_get_closed platform critical sg context mask locked **
       p # UChar |-> kind ** (p + 37) # UChar |-> status ** (p + 32) # Ptr |-> name
   | TmrNameGetPool _ =>
       interrupt_platform_running platform context.(os_sched_call_invocation) context.(os_sched_call_origin) mask **
       task_name_get_name_frame sg locked (tmr_name_get_name view locked) chars
   end) ** tmr_name_get_continuation external sg context.

Lemma tmr_name_get_safe_return : forall external critical sg context view p dest before current len error output X,
  tmr_name_get_safe external critical sg context view p dest before X ->
  tmr_name_get_program external critical sg context view p dest before
    (tmr_name_get_observation len error output) current ->
  tmr_name_get_return_safe current len error output X.
Proof.
  intros external critical sg context view p dest before current len error output X
    [initial [Heq Hsafe]] Hprogram; subst initial.
  exists current; split; [reflexivity|].
  intros observed after [-> <-]; exact (Hsafe _ _ Hprogram).
Qed.

Lemma tmr_name_get_early_program : forall external critical sg context view p dest before error,
  tmr_name_get_early_error view p dest before = Some error ->
  tmr_name_get_program external critical sg context view p dest before
    (tmr_name_get_observation 0 error None) before.
Proof.
  intros external critical sg context view p dest before error Hearly.
  unfold tmr_name_get_program.
  exists (Some error), before; split; [split; [symmetry; exact Hearly|reflexivity]|].
  split; reflexivity.
Qed.

Lemma tmr_name_get_observe_success : forall view locked chars,
  tmr_name_get_successful (tmr_name_get_state view locked) = true ->
  tmr_name_get_name_readable view locked chars ->
  tmr_name_get_observe_program view locked
    (tmr_name_get_observation (task_name_get_length (tmr_name_get_name view locked) chars)
      0 (Some (tmr_name_get_name view locked))) locked.
Proof.
  intros view locked chars Hstate Hread; unfold tmr_name_get_observe_program.
  exists (tmr_name_get_state view locked), locked; split; [split; reflexivity|].
  rewrite Hstate.
  exists chars, locked; split; [split; [exact Hread|reflexivity]|].
  exists (tmr_name_get_name view locked), locked; split; [split; reflexivity|].
  split; reflexivity.
Qed.

Lemma tmr_name_get_observe_error : forall view locked,
  tmr_name_get_successful (tmr_name_get_state view locked) = false ->
  tmr_name_get_observe_program view locked
    (tmr_name_get_observation 0 (if tmr_name_get_state view locked =? 0 then 135 else 141) None) locked.
Proof.
  intros view locked Hstate; unfold tmr_name_get_observe_program.
  exists (tmr_name_get_state view locked), locked; split; [split; reflexivity|].
  rewrite Hstate; split; reflexivity.
Qed.

Lemma tmr_name_get_normal_program : forall external critical sg context view p dest
  before entry locked returned current observed,
  tmr_name_get_early_error view p dest before = None ->
  os_sched_lock_call_relation critical sg context.(os_sched_call_invocation) before entry locked ->
  tmr_name_get_observe_program view locked observed locked ->
  tmr_name_get_unlock_relation external critical sg context locked returned current ->
  tmr_name_get_program external critical sg context view p dest before observed current.
Proof.
  intros external critical sg context view p dest before entry locked returned current observed
    Hearly Hlock Hobserve Hunlock.
  unfold tmr_name_get_program.
  exists (@None Z), before; split; [split; [symmetry; exact Hearly|reflexivity]|].
  exists tt, locked; split; [exists entry; exact Hlock|].
  exists observed, locked; split; [exact Hobserve|].
  exists returned, current; split; [exact Hunlock|split; reflexivity].
Qed.

Lemma tmr_name_get_locked_view_present : forall critical sg context view p before entry locked,
  tmr_name_get_view_present sg view p before ->
  os_sched_lock_call_relation critical sg context.(os_sched_call_invocation) before entry locked ->
  tmr_name_get_view_present sg view p locked.
Proof.
  intros critical sg context [kind status name names chars|i] p before entry locked Hview Hlock;
    [exact I|].
  destruct Hview as [Hp [Hinit [v Hv]]].
  pose proof (timer_public_trace_public_storage_frame _ _ _
    (os_sched_lock_call_timer_public_trace _ _ _ _ _ _ Hlock)) as Hframe.
  split; [exact Hp|]. split.
  - eapply timer_public_storage_frame_initialized; eassumption.
  - eapply timer_public_storage_frame_has_image; eassumption.
Qed.

Lemma tmr_name_get_pool_name_readable : forall sg s i v,
  UCOS2_state_inv sg s -> sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  sg.(osKernelConfig).(cfgTimerNames) = true -> timer_api_initialized s.(TimerState) ->
  s.(TimerState).(timerImages) i = Some v -> v.(timerImageState) <> 0 ->
  exists chars, readable_name s.(NameState) v.(timerImageName) chars.
Proof.
  intros sg s i v Hinv Henabled Hnames Hinit Himage Hnonzero.
  assert (Htimer : valid_timer_configuration sg s.(TimerState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hinv; tauto. }
  apply (proj1 (timer_initialized_configuration_iff sg s.(TimerState) Henabled Hinit)) in Htimer.
  destruct (valid_timer_state_image_live_or_free _ _ _ _ Htimer Himage)
    as [[_ [_ Hzero]]|[node [Hnode Hobject]]]; [contradiction|].
  apply (UCOS2_state_inv_names_valid _ _ Hinv).
  unfold kernel_name_root; right; right; right; right.
  split; [exact Henabled|]. split; [exact Hnames|].
  exists i, node; split; [exact Hnode|]. rewrite Hobject; reflexivity.
Qed.

Lemma tmr_name_get_resources_split_type__entry_guards :
  forall external platform critical sg context mask view p dest before,
  p <> 0 -> dest <> 0 -> sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  tmr_name_get_view_present sg view p before ->
  tmr_name_get_resources external platform critical sg context mask view p dest before |--
  p # UChar |-> tmr_name_get_type view before **
  tmr_name_get_type_rest external platform critical sg context mask view p dest before.
Proof.
  intros external platform critical sg context mask view p dest before Hp Hd Henabled Hview.
  apply Z.eqb_neq in Hp; apply Z.eqb_neq in Hd.
  destruct view as [kind status name names chars|i].
  - unfold tmr_name_get_resources, tmr_name_get_private, tmr_name_get_type_rest.
    rewrite Hp, Hd; cbn [orb tmr_name_get_type]; entailer!.
  - destruct Hview as [Haddr [Hinit [v Himage]]].
    unfold tmr_name_get_resources, tmr_name_get_private, tmr_name_get_type_rest.
    rewrite Hp, Hd; cbn [orb tmr_name_get_type]; rewrite Himage.
    unfold tmr_name_get_closed.
    rewrite task_name_get_closed_raw_rep__resource_stages_strlen.
    rewrite (UCOS2_raw_rep_split_module sg before TimerModule).
    cbn [UCOS2_module_rep].
    sep_apply_l_atomic (timer_configured_rep_split_type sg before.(TimerState) i v
      Henabled Hinit Himage).
    unfold timer_raw_rep_without_type, tmr_name_get_pool_rest.
    Exists v; rewrite Haddr; entailer!.
Qed.
Lemma tmr_name_get_resources_merge_type__entry_guards :
  forall external platform critical sg context mask view p dest before,
  p <> 0 -> dest <> 0 -> sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  tmr_name_get_view_present sg view p before ->
  p # UChar |-> tmr_name_get_type view before **
  tmr_name_get_type_rest external platform critical sg context mask view p dest before |--
  tmr_name_get_resources external platform critical sg context mask view p dest before.
Proof.
  intros external platform critical sg context mask view p dest before Hp Hd Henabled Hview.
  apply Z.eqb_neq in Hp; apply Z.eqb_neq in Hd.
  destruct view as [kind status name names chars|i].
  - unfold tmr_name_get_resources, tmr_name_get_private, tmr_name_get_type_rest.
    rewrite Hp, Hd; cbn [orb tmr_name_get_type]; entailer!.
  - destruct Hview as [Haddr [Hinit Hpresent]].
    unfold tmr_name_get_type_rest; Intros v.
    destruct H as [_ Himage].
    unfold tmr_name_get_resources, tmr_name_get_private.
    rewrite Hp, Hd; cbn [orb tmr_name_get_type]; rewrite Himage.
    unfold tmr_name_get_closed.
    rewrite task_name_get_closed_raw_rep__resource_stages_strlen.
    rewrite (UCOS2_raw_rep_split_module sg before TimerModule).
    cbn [UCOS2_module_rep].
    pose proof (timer_configured_rep_merge_type sg before.(TimerState) i v
      Henabled Hinit Himage) as Hmerge.
    unfold timer_raw_rep_without_type in Hmerge.
    unfold tmr_name_get_pool_rest; rewrite Haddr.
    sepcon_assoc_change; sep_apply_r_atomic Hmerge; entailer!.
Qed.
Lemma tmr_name_get_resources_split_nesting__entry_guards :
  forall external platform critical sg context mask view p dest before,
  tmr_name_get_resources external platform critical sg context mask view p dest before --||--
  sg.(g_OSIntNesting) # UChar |-> task_name_get_nesting before **
  tmr_name_get_int_rest external platform sg context mask view p dest before.
Proof.
  intros; unfold tmr_name_get_resources, tmr_name_get_closed, tmr_name_get_int_rest.
  rewrite task_name_get_closed_raw_rep__resource_stages_strlen.
  rewrite task_name_get_raw_rep_split_nesting__resource_stages_strlen.
  unfold task_name_get_nesting_frame, interrupt_inv_no_int_nesting.
  split; [entailer!|].
  prop_apply_p (store_uchar_range sg.(g_OSIntNesting) (task_name_get_nesting before)).
  prop_apply_p (store_uchar_range sg.(g_OSLockNesting) before.(IntrState).(lockNesting)).
  entailer!.
  unfold interrupt_in_range, task_name_get_nesting in *; lia.
Qed.
Lemma tmr_name_get_early_none_facts__name_resources : forall view p dest before,
  tmr_name_get_early_error view p dest before = None ->
  p <> 0 /\ dest <> 0 /\ tmr_name_get_type view before = 100.
Proof.
  intros view p dest before H.
  unfold tmr_name_get_early_error in H.
  destruct (dest =? 0) eqn:Hd; [discriminate|].
  destruct (p =? 0) eqn:Hp; [discriminate|].
  destruct (tmr_name_get_type view before =? 100) eqn:Ht;
    cbn in H; [|discriminate].
  apply Z.eqb_neq in Hp, Hd; apply Z.eqb_eq in Ht; auto.
Qed.
Lemma tmr_name_get_private_locked_eq__name_resources : forall view p dest before,
  tmr_name_get_early_error view p dest before = None ->
  before.(IntrState).(intNesting) = 0 ->
  tmr_name_get_private view p dest before =
  match view with
  | TmrNameGetRaw kind status name names chars =>
      p # UChar |-> kind ** ((p + 37) # UChar |-> status **
      (if tmr_name_get_successful status then
         coq_prop (name <> 0 -> readable_name names name chars) &&
         ((p + 32) # Ptr |-> name ** task_name_get_name_bytes name chars)
       else emp))
  | TmrNameGetPool _ => emp
  end.
Proof.
  intros view p dest before Hearly Hnest.
  destruct (tmr_name_get_early_none_facts__name_resources _ _ _ _ Hearly)
    as [Hp [Hd Htype]].
  apply Z.eqb_neq in Hp, Hd.
  unfold tmr_name_get_private; rewrite Hp, Hd; cbn.
  destruct view; [|reflexivity].
  cbn [tmr_name_get_type] in Htype; subst kind.
  unfold tmr_name_get_raw_tail; rewrite Hnest; reflexivity.
Qed.
Lemma tmr_name_get_pool_object_equiv__name_resources : forall platform critical sg context mask s i v,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_api_initialized s.(TimerState) ->
  s.(TimerState).(timerImages) i = Some v ->
  tmr_name_get_closed platform critical sg context mask s --||--
  interrupt_platform_running platform context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask **
  timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) v **
  tmr_name_get_pool_rest sg s i.
Proof.
  intros platform critical sg context mask s i v Henabled Hinit Himage.
  unfold tmr_name_get_closed.
  rewrite task_name_get_closed_raw_rep__resource_stages_strlen.
  rewrite (UCOS2_raw_rep_split_module sg s TimerModule).
  cbn [UCOS2_module_rep].
  rewrite (timer_initialized_configured_rep_eq sg s.(TimerState) Henabled Hinit).
  unfold timer_raw_rep, tmr_name_get_pool_rest, UCOS2_raw_rep_missing_timer.
  assert (Hobjects : timer_images_rep sg s.(TimerState) --||--
    timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) v **
    timer_images_without sg s.(TimerState) i).
  { split; [apply timer_images_split_object|apply timer_images_merge_object]; exact Himage. }
  rewrite Hobjects; split; entailer!.
Qed.
Lemma tmr_name_get_object_state_equiv__name_resources : forall c p v,
  c.(cfgTimerNames) = true ->
  timer_object_rep c p v --||--
    (p + 37) # UChar |-> v.(timerImageState) ** timer_object_rep_without_state c p v.
Proof.
  intros c p v Hnames.
  unfold timer_object_rep, timer_object_rep_without_state, timer_option_offset.
  rewrite Hnames; replace (p + 36 + 1) with (p + 37) by lia.
  split; entailer!.
Qed.
Lemma tmr_name_get_object_name_equiv__name_resources : forall c p v,
  c.(cfgTimerNames) = true ->
  timer_object_rep c p v --||--
    (p + 32) # Ptr |-> v.(timerImageName) ** tmr_name_get_object_without_name c p v.
Proof.
  intros c p v Hnames.
  unfold timer_object_rep, tmr_name_get_object_without_name.
  rewrite Hnames; split; entailer!.
Qed.
Lemma tmr_name_get_raw_rep_name_equiv__name_resources : forall sg s p chars,
  (p <> 0 -> readable_name s.(NameState) p chars) ->
  UCOS2_raw_rep sg s --||--
    task_name_get_name_bytes p chars ** task_name_get_name_frame sg s p chars.
Proof.
  intros sg s p chars Hread.
  rewrite (UCOS2_raw_rep_split_module sg s NamesModule).
  cbn [UCOS2_module_rep].
  unfold task_name_get_name_bytes, task_name_get_name_frame.
  destruct (p =? 0) eqn:Hp.
  - split; entailer!.
  - apply Z.eqb_neq in Hp.
    rewrite (task_name_get_name_split__resource_stages_strlen s.(NameState) p chars (Hread Hp)).
    split; entailer!.
Qed.
Lemma tmr_name_get_strlen_post_bytes__name_resources : forall name chars result frame,
  tmr_name_get_strlen_post name name chars result frame |--
    coq_prop (result = task_name_get_length name chars) &&
    (task_name_get_name_bytes name chars ** frame).
Proof.
  intros name chars result frame.
  unfold tmr_name_get_strlen_post; apply derivable1_orp_elim.
  - apply coq_prop_andp_left; intros [Hname Hresult].
    unfold task_name_get_length, task_name_get_name_bytes.
    subst name result; cbn; entailer!.
  - apply coq_prop_andp_left; intros [Hname [Heq Hresult]].
    unfold task_name_get_length, task_name_get_name_bytes.
    assert (Hnonzero : (name =? 0) = false) by (apply Z.eqb_neq; tauto).
    rewrite Hnonzero; unfold os_strlen_result in *; entailer!.
Qed.
Lemma tmr_name_get_unlock_post_relation__return_refinement :
  forall external platform critical sg context mask before,
  os_sched_unlock_post external platform critical sg context mask before |--
    EX returned, EX current,
      coq_prop (tmr_name_get_unlock_relation external critical sg context
        before returned current) &&
      (tmr_name_get_closed platform critical sg context mask current **
       tmr_name_get_continuation external sg returned).
Proof.
  intros; unfold os_sched_unlock_post.
  apply derivable1_orp_elim.
  - rewrite <- os_sched_unlock_outside_frame_split_running.
    Intros; Exists context before.
    assert (Hrelation : tmr_name_get_unlock_relation external critical sg context
      before context before).
    { left; tauto. }
    unfold os_sched_unlock_outside_frame, tmr_name_get_closed,
      task_name_get_closed, tmr_name_get_continuation; entailer!.
  - Intros entry.
    destruct (os_sched_unlock_requests entry) eqn:Hrequests.
    + unfold os_sched_post; Intros acquired current returned.
      Exists returned current.
      assert (Hrelation : tmr_name_get_unlock_relation external critical sg context
        before returned current).
      { right; exists entry; split; [tauto|]. split; [tauto|].
        rewrite Hrequests; exists acquired; tauto. }
      unfold tmr_name_get_closed, task_name_get_closed,
        tmr_name_get_continuation; entailer!.
    + Exists context (os_sched_unlock_checkpoint true entry).
      assert (Hrelation : tmr_name_get_unlock_relation external critical sg context
        before context (os_sched_unlock_checkpoint true entry)).
      { right; exists entry; split; [tauto|]. split; [tauto|].
        rewrite Hrequests; split; reflexivity. }
      unfold os_sched_unlock_outside_frame, tmr_name_get_closed,
        task_name_get_closed, tmr_name_get_continuation; entailer!.
Qed.
Lemma tmr_name_get_early_post__return_refinement :
  forall external platform critical sg context mask view p dest perr before old error X,
  tmr_name_get_early_error view p dest before = Some error ->
  tmr_name_get_pre external platform critical sg context mask view p dest before old X **
  task_name_get_output_cell dest old ** perr # UChar |-> error |--
  tmr_name_get_post external platform critical sg context mask view p dest perr before old 0 X.
Proof.
  intros external platform critical sg context mask view p dest perr before old error X Hearly.
  unfold tmr_name_get_pre; Intros.
  assert (Hreturn : tmr_name_get_return_safe before 0 error None X).
  { eapply (tmr_name_get_safe_return external critical sg context view p dest before).
    - unfold tmr_name_get_entry_facts in *; tauto.
    - apply tmr_name_get_early_program; exact Hearly. }
  unfold tmr_name_get_post; Left; Exists error; entailer!.
Qed.
Lemma tmr_name_get_normal_post__return_refinement :
  forall external platform critical sg context mask view p dest perr before old locked len error output X,
  tmr_name_get_lock_facts external critical sg context view p dest before old X locked ->
  tmr_name_get_observe_program view locked (tmr_name_get_observation len error output) locked ->
  os_sched_unlock_post external platform critical sg context mask locked **
  tmr_name_get_private view p dest before ** tmr_name_get_output dest old output **
  perr # UChar |-> error |--
  tmr_name_get_post external platform critical sg context mask view p dest perr before old len X.
Proof.
  intros external platform critical sg context mask view p dest perr before old locked len error output X
    Hfacts Hobserve.
  destruct Hfacts as [Hentry [Hearly [Hnest [[entry Hlock] Hrest]]]].
  sep_apply_l_atomic (tmr_name_get_unlock_post_relation__return_refinement
    external platform critical sg context mask locked).
  Intros returned current.
  assert (Hreturn : tmr_name_get_return_safe current len error output X).
  { eapply (tmr_name_get_safe_return external critical sg context view p dest before).
    - unfold tmr_name_get_entry_facts in Hentry; tauto.
    - eapply tmr_name_get_normal_program; eassumption. }
  unfold tmr_name_get_post; Right.
  Exists locked returned current error output; entailer!.
  exists entry; exact Hlock.
Qed.
