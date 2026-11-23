Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
From AUXLib Require Import int_auto Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.mutex_accept_spec.
Require Export Ucos2Verify.lib.mutex_annotation_slices.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Ucos2Verify.lib.mutex_rdyatprio_spec.
Require Import Ucos2Verify.lib.error_codes.
Import UCOS2_C_Rules.
Import TaskStateDef.
Import EventStateDef.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope list.
Local Open Scope sac_scope.

Definition observe_os_err_code (err : OSErrCode)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun X1 n X2 => n = encode_os_err_code err /\ X2 = X1.

Definition observe_mutex_accept_bool (ret : OSErrCode * bool)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun X1 n X2 =>
    n = (if snd ret then OS_TRUE else OS_FALSE) /\ X2 = X1.

Definition observe_mutex_create_ptr (sg : StableGlobVars)
           (ret : OSErrCode * option EventID)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun X1 p X2 =>
    p = match snd ret with
        | Some eid => event_addr sg eid
        | None => 0
        end /\ X2 = X1.

Definition observe_mutex_del_ptr (pevent : addr)
           (ret : OSErrCode * option addr)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun X1 p X2 =>
    p = match snd ret with
        | Some a => a
        | None => 0
        end /\ X2 = X1.

Definition observe_unit_void (_ : unit)
  : program (UCOS2_Verify_State -> Prop) unit :=
  fun X1 _ X2 => X2 = X1.

Definition OSMutex_RdyAtPrio_sem (sg : StableGlobVars)
           (ptcb : addr) (prio : Priority)
  : program UCOS2_Verify_State unit :=
  Ucos2Verify.lib.mutex_rdyatprio_spec.OSMutex_RdyAtPrio_sem
    sg ptcb prio.

(* ================================================================== *)
(* Phase 8: OSMutexQuery 函数语义 + preserves_inv                      *)
(* ================================================================== *)
(* fallback 路线:不经 symexec,直接定义函数语义为状态转换关系,        *)
(* 然后证明每个分支 preserves UCOS2_verification_slice_inv。                        *)
(*                                                                    *)
(* OSMutexQuery 是只读函数(C 代码 os_mutex.c:727-770):               *)
(*   1. OSIntNesting > 0         -> OS_ERR_QUERY_ISR                   *)
(*   2. pevent == 0               -> OS_ERR_PEVENT_NULL                *)
(*   3. p_mutex_data == 0         -> OS_ERR_PDATA_NULL                 *)
(*   4. OSEventType != MUTEX      -> OS_ERR_EVENT_TYPE                 *)
(*   5. else(进入临界区拷贝)     -> OS_ERR_NONE                       *)
(* 所有分支 lvs2 = lvs1(纯读,无副作用)。                              *)

Definition OSMutexQuery_sem (sg : StableGlobVars)
                            (pevent p_mutex_data : addr)
  : program UCOS2_Verify_State OSErrCode :=
  fun lvs1 ret lvs2 =>
    (lvs1.(IntrState).(intNesting) > 0 /\ ret = OS_ERR_QUERY_ISR /\ lvs2 = lvs1) \/
    (lvs1.(IntrState).(intNesting) <= 0 /\
     pevent = 0 /\ ret = OS_ERR_PEVENT_NULL /\ lvs2 = lvs1) \/
    (lvs1.(IntrState).(intNesting) <= 0 /\
     pevent <> 0 /\ p_mutex_data = 0 /\ ret = OS_ERR_PDATA_NULL /\ lvs2 = lvs1) \/
    (lvs1.(IntrState).(intNesting) <= 0 /\
     pevent <> 0 /\ p_mutex_data <> 0 /\
     exists eid, pevent = event_addr sg eid /\
                  (lvs1.(EventState).(inUsedEventStates)) eid = None /\
                  ret = OS_ERR_EVENT_TYPE /\ lvs2 = lvs1) \/
    (lvs1.(IntrState).(intNesting) <= 0 /\
     pevent <> 0 /\ p_mutex_data <> 0 /\
     exists eid e, pevent = event_addr sg eid /\
                   (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
                   e.(eventType) <> OS_EVENT_TYPE_MUTEX /\
                   ret = OS_ERR_EVENT_TYPE /\ lvs2 = lvs1) \/
    (lvs1.(IntrState).(intNesting) <= 0 /\
     pevent <> 0 /\ p_mutex_data <> 0 /\
     exists eid e, pevent = event_addr sg eid /\
                   (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
                   e.(eventType) = OS_EVENT_TYPE_MUTEX /\
                   ret = OS_ERR_NONE /\ lvs2 = lvs1).

(* The imported atomic relations below remain the source-level transition
   model.  This file exports only independently kernel-checked facts about
   them.  Operations whose representation or cross-module closure is not yet
   established deliberately have no whole-invariant preservation wrapper.

   In particular, priority-slot reservation, mutex initialization, and event
   publication/freeing can pass through transient states that do not satisfy
   the stable whole invariant.  Their future proofs must use explicit stage
   predicates or a single source-faithful full-pre/full-post linearization. *)

(* A live mutex either carries the disabled-PCP tag, whose total-map
   observation stays PTFree, or has an enabled PCP whose concrete priority
   slot cannot be PTFree.  The old model incorrectly concluded that every
   live mutex had enabled PCP and made OSMutexCreate(0xFF) inconsistent. *)
Lemma mutex_pcp_slot_consistency :
  forall sg lvs mid e m,
    (EventState lvs).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    verification_slice_cross_module_consistency sg lvs ->
    (m.(mfPCP) = sg.(osPrioMutexCeilDis) /\
     (TskState lvs).(prioTbl) sg.(osPrioMutexCeilDis) = PTFree) \/
    (m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\
     (TskState lvs).(prioTbl) m.(mfPCP) <> PTFree).
Proof.
  intros sg lvs mid e m Hget Htype Hmf Hcm.
  destruct Hcm as [H_osprio [H_pt [H_mo [H_mw [H_rlc [H_rlo [H_ceil _]]]]]]].
  destruct (Z.eq_dec m.(mfPCP) sg.(osPrioMutexCeilDis)) as [Hdisabled | Henabled].
  - left. split; assumption.
  - right. split; [exact Henabled|].
    intro Hfree.
    specialize (H_pt m.(mfPCP)).
    rewrite Hfree in H_pt.
    destruct H_pt as [_ Hno_enabled_mutex].
    apply Hno_enabled_mutex.
    exists mid, e, m.
    repeat split; try assumption.
Qed.

(* atomic_task_set_curPrio 总是更新 task/prioTbl。ready 分支还重定位
   readyList；waiting 分支重定位单个 event waitList；dormant 分支不改
   SchedState/EventState。IntrState 和 TickState 在三个分支中均保持。 *)
Lemma atomic_task_set_curPrio_preserves_neutral_fields :
  forall sg tid newPrio lvs1 lvs2,
    atomic_task_set_curPrio sg tid newPrio lvs1 tt lvs2 ->
    IntrState lvs1 = IntrState lvs2 /\
    TickState lvs1 = TickState lvs2.
Proof.
  intros sg tid newPrio lvs1 lvs2 Hatomic.
  unfold atomic_task_set_curPrio in Hatomic.
  destruct Hatomic as [Hready | [Hwaiting | Hdormant]].
  - unfold atomic_task_set_curPrio_ready in Hready.
    destruct Hready as [t [oldPrio [t'
      [_ [_ [_ [_ [_ [_ [_ [_ Hlvs2]]]]]]]]]]].
    cbv zeta in Hlvs2.
    rewrite Hlvs2.
    simpl.
    split; reflexivity.
  - unfold atomic_task_set_curPrio_waiting in Hwaiting.
    destruct Hwaiting as
      (t & oldPrio & t' & wait_eid & wait_e & wait_e' & tskSt2 & evSt2 & pty &
       Hnot_ready & Htask & Hold & Hne & Hlo & Hhi & Hpt & Hpend & Hevent &
       Hmulti & Hget & Htype & Hin & Ht' & Htsk & Hwait' & Hev & Hlvs2).
    rewrite Hlvs2.
    simpl.
    split; reflexivity.
  - unfold atomic_task_set_curPrio_dormant in Hdormant.
    destruct Hdormant as
      (t & oldPrio & t' & tskSt2 & Hnot_ready & Htask & Hold & Hne &
       Hlo & Hhi & Hpt & Hevent & Hmulti & Hnot_effective & Ht' & Htsk &
       Hlvs2).
    rewrite Hlvs2.
    simpl.
    split; reflexivity.
Qed.

Lemma atomic_mutex_del_owner_restore_preserves_neutral_fields :
  forall sg m lvs1 lvs2,
    atomic_mutex_del_owner_restore sg m lvs1 tt lvs2 ->
    IntrState lvs1 = IntrState lvs2 /\
    EventState lvs1 = EventState lvs2 /\
    TickState lvs1 = TickState lvs2.
Proof.
  intros sg m lvs1 lvs2 Hatomic.
  unfold atomic_mutex_del_owner_restore in Hatomic.
  destruct Hatomic as [Hshape Hrestore].
  destruct (mfOwner m) as [owner_tid |] eqn:Howner;
  destruct (mfOwnerOrigPrio m) as [orig_prio |] eqn:Horig;
  simpl in Hshape, Hrestore; try contradiction.
  - destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) eqn:Hpcp_disabled.
    + subst lvs2. repeat split; reflexivity.
    + destruct Hrestore as [owner_t [Howner_get Hrestore]].
      destruct (Z.eqb owner_t.(curPrio) m.(mfPCP)) eqn:Howner_at_pcp.
      * unfold atomic_task_set_curPrio_ready_owner_literal_exec in Hrestore.
        destruct Hrestore as
          (t' & Hready & Howner_get' & Hprio_lo & Hprio_hi & Ht' & Hlvs2).
        cbv zeta in Hlvs2.
        subst lvs2. repeat split; reflexivity.
      * subst lvs2. repeat split; reflexivity.
  - destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis));
      subst lvs2; repeat split; reflexivity.
Qed.

Lemma atomic_mutex_release_sched_inv_preserved :
  forall sg mid lvs1 lvs2,
    atomic_mutex_release sg mid lvs1 tt lvs2 ->
    verification_slice_sched_inv sg (TskState lvs1) (SchedState lvs1) |--
    verification_slice_sched_inv sg (TskState lvs2) (SchedState lvs2).
Proof.
  intros sg mid lvs1 lvs2 Hatomic.
  destruct Hatomic as
    [e1 [e2 [m1 [m2 [owner_tid [evSt2 [tskSt2 Hconj]]]]]]].
  destruct Hconj as
    (Hget_e1 & Htype & Hmf1 & Hwl & Howner & Hm2_def & He2_def &
     HevSt2_def & HtskSt2_def & Hlvs2).
  assert (HinU_func : (TskState lvs2).(inUsedTaskStates) = (TskState lvs1).(inUsedTaskStates)).
  { apply functional_extensionality.
    intros tid. rewrite Hlvs2. rewrite HtskSt2_def. reflexivity. }
  assert (Hsched : SchedState lvs2 = SchedState lvs1).
  { rewrite Hlvs2. reflexivity. }
  rewrite Hsched.
  rewrite (verification_slice_sched_inv_ext sg (TskState lvs2) (TskState lvs1) (SchedState lvs1) HinU_func).
  apply derivable1_refl.
Qed.

Lemma atomic_sched_preserves_neutral_fields :
  forall lvs1 res lvs2,
    atomic_sched lvs1 res lvs2 ->
    TskState lvs1 = TskState lvs2 /\
    EventState lvs1 = EventState lvs2 /\
    IntrState lvs1 = IntrState lvs2 /\
    TickState lvs1 = TickState lvs2.
Proof.
  intros lvs1 res lvs2 Hatomic.
  unfold atomic_sched in Hatomic.
  cbv zeta in Hatomic.
  remember (Z.eqb lvs1.(IntrState).(intNesting) 0 &&
             Z.eqb lvs1.(IntrState).(lockNesting) 0)%bool as b_outer in *.
  destruct b_outer.
  - cbv beta iota in Hatomic.
    remember (lvs1.(SchedState).(readyList)) as rl in *.
    destruct rl as [|h tl].
    + cbv beta iota in Hatomic.
      destruct Hatomic as [Hlvs2 Hres]. subst lvs2.
      repeat split; reflexivity.
    + cbv beta iota in Hatomic.
      remember (lvs1.(SchedState).(curTaskID)) as ctid in *.
      destruct ctid as [c|].
      * cbv beta iota in Hatomic.
        remember (lvs1.(TskState).(inUsedTaskStates) h) as geth in *.
        destruct geth as [headT|].
        -- cbv beta iota in Hatomic.
           remember (lvs1.(TskState).(inUsedTaskStates) c) as getc in *.
           destruct getc as [curT|].
           ++ cbv beta iota in Hatomic.
              remember (negb (is_effectively_ready curT.(stat) curT.(dly) &&
                              existsb (Z.eqb c) (h :: tl)) ||
                         negb (Z.eqb h c))%bool as b_inner in *.
              destruct b_inner.
              ** cbv beta iota in Hatomic.
                 destruct Hatomic as [schedSt2 [HschedSt2_def [Hlvs2 Hres]]].
                 rewrite Hlvs2.
                 split; [symmetry; apply replace_SchedS_other_Tsk |].
                 split; [symmetry; apply replace_SchedS_other_Event |].
                 split; [symmetry; apply replace_SchedS_other_Intr |].
                 symmetry. apply replace_SchedS_other_Tick.
              ** cbv beta iota in Hatomic.
                 destruct Hatomic as [Hlvs2 Hres]. subst lvs2.
                 repeat split; reflexivity.
           ++ cbv beta iota in Hatomic.
              destruct Hatomic as [Hlvs2 Hres]. subst lvs2.
              repeat split; reflexivity.
        -- cbv beta iota in Hatomic.
           destruct Hatomic as [Hlvs2 Hres]. subst lvs2.
           repeat split; reflexivity.
      * cbv beta iota in Hatomic.
        destruct Hatomic as [Hlvs2 Hres]. subst lvs2.
        repeat split; reflexivity.
  - cbv beta iota in Hatomic.
    destruct Hatomic as [Hlvs2 Hres]. subst lvs2.
    repeat split; reflexivity.
Qed.

(* Helper:atomic_sched switch 分支下 verification_slice_sched_in_range 保持。
   readyList 不变;curTaskID/curSchedPrio/highRdy*/ctxSwCtr 变。
   7 个合取分别处理。 *)
Lemma verification_slice_sched_in_range_preserved_by_sched_switch :
  forall sg tskSt schedSt1 h tl headT schedSt2,
    schedSt1.(readyList) = h :: tl ->
    tskSt.(inUsedTaskStates) h = Some headT ->
    schedSt2 = {|
      readyList    := schedSt1.(readyList);
      curTaskID    := Some h;
      curSchedPrio := Some headT.(curPrio);
      highRdyTid   := Some h;
      highRdyPrio  := Some headT.(curPrio);
      ctxSwCtr     := (schedSt1.(ctxSwCtr) + 1) mod 4294967296;
      isRunning    := schedSt1.(isRunning);
    |} ->
    verification_slice_sched_in_range sg tskSt schedSt1 ->
    verification_slice_sched_in_range sg tskSt schedSt2.
Proof.
  intros sg tskSt schedSt1 h tl headT schedSt2 Hrl Hget_h HschedSt2_def [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
  subst schedSt2.
  unfold verification_slice_sched_in_range.
  split.
  - (* conjunct 1: In readyList -> effectively_ready *)
    intros tid Hin. apply (H1 tid Hin).
  - split.
    + (* conjunct 2: strictly_sorted_by *)
      simpl in *. exact H2.
    + split.
      * (* conjunct 3: effectively_ready -> In readyList *)
        intros tid t Hget Hready. apply (H3 tid t Hget Hready).
      * split.
        -- (* conjunct 4: NoDup *)
           simpl in *. exact H4.
        -- split.
           ++ (* conjunct 5: 0 <= ctxSwCtr *)
              simpl. pose proof (Z.mod_pos_bound (ctxSwCtr schedSt1 + 1) 4294967296 ltac:(lia)); lia.
           ++ split.
              ** (* conjunct 6: sched_high_ready_consistency *)
                 unfold sched_high_ready_consistency in *.
                 cbv beta iota in *.
                 rewrite Hrl in *.
                 cbv beta iota in *.
                 split.
                 --- reflexivity.
                 --- exists headT. split.
                    +++ exact Hget_h.
                    +++ reflexivity.
              ** (* conjunct 7: sched_current_consistency *)
                 unfold sched_current_consistency in *.
                 cbv beta iota in *.
                 exists headT. split.
                    +++ exact Hget_h.
                    +++ reflexivity.
Qed.

(* Helper:atomic_sched 保持 verification_slice_sched_in_range(考虑所有分支)。 *)
Lemma atomic_sched_preserves_sched_in_range :
  forall sg lvs1 res lvs2,
    atomic_sched lvs1 res lvs2 ->
    verification_slice_sched_in_range sg (TskState lvs1) (SchedState lvs1) ->
    verification_slice_sched_in_range sg (TskState lvs1) (SchedState lvs2).
Proof.
  intros sg lvs1 res lvs2 Hatomic.
  unfold atomic_sched in Hatomic.
  cbv zeta in Hatomic.
  remember (Z.eqb lvs1.(IntrState).(intNesting) 0 &&
             Z.eqb lvs1.(IntrState).(lockNesting) 0)%bool as b_outer in *.
  destruct b_outer.
  - cbv beta iota in Hatomic.
    remember (lvs1.(SchedState).(readyList)) as rl in *.
    destruct rl as [|h tl].
    + cbv beta iota in Hatomic.
      destruct Hatomic as [Hlvs2 Hres]. subst lvs2.
      simpl. intro Hvs. exact Hvs.
    + cbv beta iota in Hatomic.
      remember (lvs1.(SchedState).(curTaskID)) as ctid in *.
      destruct ctid as [c|].
      * cbv beta iota in Hatomic.
        remember (lvs1.(TskState).(inUsedTaskStates) h) as geth in *.
        destruct geth as [headT|].
        -- cbv beta iota in Hatomic.
           remember (lvs1.(TskState).(inUsedTaskStates) c) as getc in *.
           destruct getc as [curT|].
           ++ cbv beta iota in Hatomic.
              remember (negb (is_effectively_ready curT.(stat) curT.(dly) &&
                              existsb (Z.eqb c) (h :: tl)) ||
                         negb (Z.eqb h c))%bool as b_inner in *.
              destruct b_inner.
              ** (* switch 分支 *)
                 cbv beta iota in Hatomic.
                 destruct Hatomic as [schedSt2 [HschedSt2_def [Hlvs2 Hres]]].
                 rewrite Heqrl in HschedSt2_def.
                 intro Hvs.
                 rewrite Hlvs2.
                 rewrite replace_SchedS_SchedState.
                 apply (verification_slice_sched_in_range_preserved_by_sched_switch
                         sg (TskState lvs1) (SchedState lvs1) h tl headT schedSt2).
                 +++ symmetry. exact Heqrl.
                 +++ symmetry. exact Heqgeth.
                 +++ exact HschedSt2_def.
                 +++ exact Hvs.
              ** (* no-switch 分支 *)
                 cbv beta iota in Hatomic.
                 destruct Hatomic as [Hlvs2 Hres]. subst lvs2.
                 intro Hvs.
                 pose proof Hvs as Hclosed.
                 destruct Hclosed as [_ [_ [_ [_ [_ [Hhigh _]]]]]].
                 unfold sched_high_ready_consistency in Hhigh.
                 rewrite <- Heqrl in Hhigh; simpl in Hhigh.
                 destruct Hhigh as [Htid [t [Ht Hprio]]].
                 rewrite <- Heqgeth in Ht; inversion Ht; subst t.
                 rewrite replace_SchedS_SchedState.
                 rewrite <- Htid, <- Hprio, sched_write_high_pair_eq.
                 exact Hvs.
           ++ cbv beta iota in Hatomic.
              destruct Hatomic as [Hlvs2 Hres]. subst lvs2.
              intro Hvs. exact Hvs.
        -- cbv beta iota in Hatomic.
           destruct Hatomic as [Hlvs2 Hres]. subst lvs2.
           intro Hvs. exact Hvs.
      * cbv beta iota in Hatomic.
        destruct Hatomic as [Hlvs2 Hres]. subst lvs2.
        intro Hvs. exact Hvs.
  - cbv beta iota in Hatomic.
    destruct Hatomic as [Hlvs2 Hres]. subst lvs2.
    intro Hvs. exact Hvs.
Qed.

(* verification_slice_cross_module_consistency 在 atomic_sched 下保持。
   Case 1 (switch):curTaskID/curSchedPrio/highRdy*/ctxSwCtr 变,readyList 不变。
                    仅 osprio_cur_consistency 需重证(其他 7 个合取依赖的字段不变)。
   Case 2 (no-switch):lvs2 = lvs1,trivial。 *)
Lemma verification_slice_cross_module_consistency_preserved_by_sched :
  forall sg lvs1 res lvs2,
    atomic_sched lvs1 res lvs2 ->
    verification_slice_cross_module_consistency sg lvs1 -> verification_slice_cross_module_consistency sg lvs2.
Proof.
  intros sg lvs1 res lvs2 Hatomic Hcm.
  unfold atomic_sched in Hatomic.
  cbv zeta in Hatomic.
  remember (Z.eqb lvs1.(IntrState).(intNesting) 0 &&
             Z.eqb lvs1.(IntrState).(lockNesting) 0)%bool as b_outer in *.
  destruct b_outer.
  - cbv beta iota in Hatomic.
    remember (lvs1.(SchedState).(readyList)) as rl in *.
    destruct rl as [|h tl].
    + cbv beta iota in Hatomic.
      destruct Hatomic as [Hlvs2 Hres]. subst lvs2. exact Hcm.
    + cbv beta iota in Hatomic.
      remember (lvs1.(SchedState).(curTaskID)) as ctid in *.
      destruct ctid as [c|].
      * cbv beta iota in Hatomic.
        remember (lvs1.(TskState).(inUsedTaskStates) h) as geth in *.
        destruct geth as [headT|].
        -- cbv beta iota in Hatomic.
           remember (lvs1.(TskState).(inUsedTaskStates) c) as getc in *.
           destruct getc as [curT|].
           ++ cbv beta iota in Hatomic.
              remember (negb (is_effectively_ready curT.(stat) curT.(dly) &&
                              existsb (Z.eqb c) (h :: tl)) ||
                         negb (Z.eqb h c))%bool as b_inner in *.
              destruct b_inner.
              ** (* switch 分支 *)
                 cbv beta iota in Hatomic.
                 destruct Hatomic as [schedSt2 [HschedSt2_def [Hlvs2 Hres]]].
                 unfold verification_slice_cross_module_consistency in *.
                 destruct Hcm as
                   [H_osprio [H_pt [H_mo [H_mw [H_rlc [H_rlo
                     [H_ceil [H_tpu [H_protocol H_pcp_unique]]]]]]]]].
                 assert (HTsk_lvs2 : TskState lvs2 = TskState lvs1).
                 { rewrite Hlvs2. apply replace_SchedS_other_Tsk. }
                 assert (HEvt_lvs2 : EventState lvs2 = EventState lvs1).
                 { rewrite Hlvs2. apply replace_SchedS_other_Event. }
                 assert (HSched_lvs2 : SchedState lvs2 = schedSt2).
                 { rewrite Hlvs2. apply replace_SchedS_SchedState. }
                 assert (Hrl_eq : readyList (SchedState lvs2) = readyList (SchedState lvs1)).
                 { rewrite HSched_lvs2. rewrite HschedSt2_def. exact Heqrl. }
                 split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
                 --- (* 1. osprio_cur_consistency *)
                     unfold osprio_cur_consistency in *.
                     rewrite HSched_lvs2. rewrite HschedSt2_def.
                     exists headT. split.
                     +++ rewrite HTsk_lvs2. symmetry. exact Heqgeth.
                     +++ reflexivity.
                 --- (* 2. priotbl_consistency *)
                     unfold priotbl_consistency in *.
                     intros p. rewrite HTsk_lvs2.
                     destruct (prioTbl (TskState lvs1) p) eqn:Hpt_case.
                     +++ (* PTFree *)
                         simpl. split.
                         *** intros [tid [Hin Hget]].
                             assert (Hpt_at_p := H_pt p). rewrite Hpt_case in Hpt_at_p.
                             apply (proj1 Hpt_at_p).
                             destruct Hget as [t Hget_t].
                             exists tid. split.
                             ---- rewrite Hrl_eq in Hin. exact Hin.
                             ---- exists t. split.
                                  ------ exact (proj1 Hget_t).
                                  ------ exact (proj2 Hget_t).
                         *** intros [mid [e [m [Hget [Htype [Hmf Hpcp]]]]]].
                             assert (Hpt_at_p := H_pt p). rewrite Hpt_case in Hpt_at_p.
                             apply (proj2 Hpt_at_p).
                             rewrite HEvt_lvs2 in Hget.
                             exists mid, e, m.
                             split; [exact Hget|].
                             split; [exact Htype|].
                             split; [exact Hmf|exact Hpcp].
                     +++ (* PTReserved *)
                         simpl.
                         assert (Hpt_at_p := H_pt p). rewrite Hpt_case in Hpt_at_p.
                         destruct Hpt_at_p as [mid [e [m [Hget [Htype [Hmf [Hpcp Howner]]]]]]].
                         exists mid, e, m. rewrite HEvt_lvs2. repeat split; try assumption; exact Hget.
                     +++ (* PTTask tid0 *)
                         simpl.
                         assert (Hpt_at_p := H_pt p). rewrite Hpt_case in Hpt_at_p.
                         destruct Hpt_at_p as [t0 [Hget Hor]].
                         exists t0. split.
                         *** exact Hget.
                         *** destruct Hor as [Hcp | [mid [e [m [Hget2 [Htype2 [Hmf2 [Hpcp2 Howner2]]]]]]]].
                             ---- left. exact Hcp.
                             ---- right. exists mid, e, m. rewrite HEvt_lvs2. repeat split; try assumption; exact Hget2.
                 --- (* 3. mutex_owner_consistency *)
                     unfold mutex_owner_consistency in *.
                     intros mid e m Hget.
                     rewrite HEvt_lvs2 in Hget. rewrite HTsk_lvs2.
                     apply (H_mo mid e m). exact Hget.
                 --- (* 4. verification_slice_event_wait_object_consistency *)
                     unfold verification_slice_event_wait_object_consistency in *.
                     rewrite HEvt_lvs2, HTsk_lvs2. exact H_mw.
                 --- (* 5. ready_list_completeness *)
                     unfold ready_list_completeness in *.
                     intros tid t Hget Hready.
                     rewrite Hrl_eq.
                     rewrite HTsk_lvs2 in Hget.
                     apply (H_rlc tid t).
                     +++ exact Hget.
                     +++ exact Hready.
                 --- (* 6. ready_list_order *)
                     unfold ready_list_order in *.
                     rewrite HSched_lvs2.
                     assert (Hrl_in_lvs2 : (schedSt2.(readyList)) = (lvs1.(SchedState)).(readyList))
                       by (rewrite HschedSt2_def; exact Heqrl).
                     rewrite Hrl_in_lvs2.
                     rewrite HTsk_lvs2.
                     exact H_rlo.
                 --- (* 7. ceiling_priotbl_free *)
                     unfold ceiling_priotbl_free in *.
                     rewrite HTsk_lvs2. exact H_ceil.
                 --- (* 8. task_priority_unique_prop *)
                     unfold task_priority_unique_prop in *.
                     rewrite HTsk_lvs2. exact H_tpu.
                 --- (* 9. mutex_protocol_consistency:SchedState-only update *)
                     unfold mutex_protocol_consistency in *.
                     rewrite HEvt_lvs2, HTsk_lvs2. exact H_protocol.
                 --- (* 10. mutex_enabled_pcp_unique:SchedState-only update *)
                     unfold mutex_enabled_pcp_unique in *.
                     rewrite HEvt_lvs2. exact H_pcp_unique.
              ** (* no-switch 分支 *)
                 cbv beta iota in Hatomic.
                 destruct Hatomic as [Hlvs2 Hres]. subst lvs2. exact Hcm.
           ++ cbv beta iota in Hatomic.
              destruct Hatomic as [Hlvs2 Hres]. subst lvs2. exact Hcm.
        -- cbv beta iota in Hatomic.
           destruct Hatomic as [Hlvs2 Hres]. subst lvs2. exact Hcm.
      * cbv beta iota in Hatomic.
        destruct Hatomic as [Hlvs2 Hres]. subst lvs2. exact Hcm.
  - cbv beta iota in Hatomic.
    destruct Hatomic as [Hlvs2 Hres]. subst lvs2. exact Hcm.
Qed.

(* ================================================================== *)
(* 2026-07-10:verification_slice_cross_module_consistency 在 atomic_event_task_rdy 下保持    *)
(* TskState:ready_tid 的 t→t'(curPrio 不变,task_non_suspension_bits→None,eventPtr→None) *)
(* EventState:e2.waitList = remove_Z_eqb ready_tid e1.waitList           *)
(* SchedState:readyList 可能通过 insert_sorted_by 加入 ready_tid         *)
(* ================================================================== *)
Lemma verification_slice_cross_module_consistency_preserved_by_event_task_remove :
  forall sg tid mid lvs1 lvs2,
    atomic_event_task_remove tid mid lvs1 tt lvs2 ->
    verification_slice_sched_in_range sg (TskState lvs1) (SchedState lvs1) ->
    verification_slice_cross_module_consistency sg lvs1 -> verification_slice_cross_module_consistency sg lvs2.
Proof.
  intros sg tid mid lvs1 lvs2 Hatomic Hvs Hcm.
  unfold atomic_event_task_remove in Hatomic.
  destruct Hatomic as [e1 [e2 [t [t'
    [Hget_e1 [Hin_wl [Hget_t [He2 [Ht' Hlvs2]]]]]]]]].
  assert (Hcp_t' : t'.(curPrio) = t.(curPrio)) by (rewrite Ht'; reflexivity).
  assert (Heptr_t' : t'.(eventPtr) = None) by (rewrite Ht'; reflexivity).
  assert (Hstat_t' : t'.(stat) = t.(stat)) by (rewrite Ht'; reflexivity).
  assert (Hdly_t' : t'.(dly) = t.(dly)) by (rewrite Ht'; reflexivity).
  assert (HinU_lvs2 : forall tidv, (TskState lvs2).(inUsedTaskStates) tidv =
    if Z.eqb tidv tid then Some t' else (TskState lvs1).(inUsedTaskStates) tidv).
  { intros tidv. rewrite Hlvs2. reflexivity. }
  assert (HprioTbl_lvs2 : (TskState lvs2).(prioTbl) = (TskState lvs1).(prioTbl))
    by (rewrite Hlvs2; reflexivity).
  assert (Hrl_lvs2 : (SchedState lvs2).(readyList) = (SchedState lvs1).(readyList))
    by (rewrite Hlvs2; reflexivity).
  assert (Hctid_lvs2 : (SchedState lvs2).(curTaskID) = (SchedState lvs1).(curTaskID))
    by (rewrite Hlvs2; reflexivity).
  assert (Hcsp_lvs2 : (SchedState lvs2).(curSchedPrio) = (SchedState lvs1).(curSchedPrio))
    by (rewrite Hlvs2; reflexivity).
  assert (HevSt_lvs2_at : forall eid, (EventState lvs2).(inUsedEventStates) eid =
    if Z.eqb eid mid then Some e2 else (EventState lvs1).(inUsedEventStates) eid).
  { intros eid. rewrite Hlvs2. unfold update_event_field_raw. simpl. reflexivity. }
  assert (He2_wl : e2.(waitList) = remove_Z_eqb tid e1.(waitList))
    by (rewrite He2; reflexivity).
  assert (He2_mf : e2.(mutexFields) = e1.(mutexFields))
    by (rewrite He2; reflexivity).
  assert (He2_ety : e2.(eventType) = e1.(eventType))
    by (rewrite He2; reflexivity).
  pose proof Hcm as Hcm_copy.
  destruct Hcm_copy as [_ [_ [_ [H_mw_cm _]]]].
  assert (Hrefs_t : t.(eventPtr) = Some mid /\ t.(eventMultiWaitEvents) = []).
  { unfold verification_slice_event_wait_object_consistency in H_mw_cm.
    destruct H_mw_cm as [Hmw_entry _].
    specialize (Hmw_entry mid e1 Hget_e1) as [_ Hmatch].
    destruct (event_type_to_pend_type e1.(eventType)) eqn:Hety_e1.
    - simpl in Hmatch.
      specialize (Hmatch tid Hin_wl) as [t0 [Hget0 [Heptr0 [Hmulti0 _]]]].
      rewrite Hget_t in Hget0. injection Hget0 as Heq. subst t0.
      split; assumption.
    - simpl in Hmatch. rewrite Hmatch in Hin_wl. inversion Hin_wl. }
  destruct Hrefs_t as [Heptr_t Hmulti_t].
  unfold verification_slice_cross_module_consistency in *.
  destruct Hcm as [H_osprio [H_pt [H_mo [H_mw [H_rlc [H_rlo [H_ceil [H_tpu [H_protocol H_pcp_unique]]]]]]]]].
  split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
  - (* 1. osprio_cur_consistency *)
    unfold osprio_cur_consistency in *.
    rewrite Hctid_lvs2, Hcsp_lvs2.
    destruct ((SchedState lvs1).(curTaskID)) as [curtid |] eqn:Hcurtid.
    + simpl. destruct H_osprio as [t0 [HinU Hcp]].
      destruct (Z.eqb curtid tid) eqn:Heq.
      * apply Z.eqb_eq in Heq. subst curtid.
        rewrite Hget_t in HinU. injection HinU as Heq_t. subst t0.
        exists t'. split.
        -- rewrite HinU_lvs2, Z.eqb_refl. reflexivity.
        -- rewrite Hcp_t'. exact Hcp.
      * exists t0. split.
        -- rewrite HinU_lvs2, Heq. exact HinU.
        -- exact Hcp.
    + simpl. exact H_osprio.
  - (* 2. priotbl_consistency *)
    unfold priotbl_consistency in *.
    intros p.
    rewrite HprioTbl_lvs2.
    specialize (H_pt p) as Hpt_p.
    destruct ((TskState lvs1).(prioTbl) p) as [ptv | | tidv] eqn:Hprio.
    + (* PTFree *)
      cbv beta iota in Hpt_p.
      destruct Hpt_p as [Hnf_task Hnf_mutex].
      split.
      * intros [tidv_r [Hin_rdy [t0 [Hgetv Hcp0]]]].
        apply Hnf_task.
        exists tidv_r.
        split.
        -- rewrite Hrl_lvs2 in Hin_rdy. exact Hin_rdy.
        -- rewrite HinU_lvs2 in Hgetv.
           destruct (Z.eqb tidv_r tid) eqn:Heq_tv.
           ++ apply Z.eqb_eq in Heq_tv. subst tidv_r.
              cbv beta iota in Hgetv. injection Hgetv as Heq_t. subst t0.
              exists t. split. exact Hget_t.
              rewrite Hcp_t' in Hcp0. exact Hcp0.
           ++ cbv beta iota in Hgetv.
              exists t0. split. exact Hgetv. exact Hcp0.
      * intros [midv [ev [m [Hgetv [Hty [Hmf HmfPCP]]]]]].
        apply Hnf_mutex.
        rewrite HevSt_lvs2_at in Hgetv.
        destruct (Z.eqb midv mid) eqn:Heq_midv.
        -- apply Z.eqb_eq in Heq_midv. subst midv.
           cbv beta iota in Hgetv. injection Hgetv as Heq_ev. subst ev.
           exists mid, e1, m. split; [| split; [| split]].
           ++ exact Hget_e1.
           ++ rewrite <- He2_ety. exact Hty.
           ++ rewrite <- He2_mf. exact Hmf.
           ++ exact HmfPCP.
        -- cbv beta iota in Hgetv.
           exists midv, ev, m. split; [| split; [| split]].
           ++ exact Hgetv.
           ++ exact Hty.
           ++ exact Hmf.
           ++ exact HmfPCP.
    + (* PTReserved *)
      cbv beta iota in Hpt_p.
      destruct Hpt_p as [midv [ev [m [Hgetv_lvs1 [Hty [Hmf [HmfPCP Howner_case]]]]]]].
      destruct (Z.eqb midv mid) eqn:Heq_midv.
      * apply Z.eqb_eq in Heq_midv. subst midv.
        rewrite Hget_e1 in Hgetv_lvs1. injection Hgetv_lvs1 as Heq_ev. subst ev.
        exists mid, e2, m. split; [| split; [| split; [| split]]].
        -- (* lvs2 lookup at mid *)
           rewrite HevSt_lvs2_at, Z.eqb_refl. reflexivity.
        -- rewrite He2_ety. exact Hty.
        -- rewrite He2_mf. exact Hmf.
        -- exact HmfPCP.
        -- (* owner case *)
           destruct m.(mfOwner) as [tidv|] eqn:Howner.
           ++ cbv beta iota in Howner_case.
              destruct Howner_case as [t0 [op [Hget_t0 [Hop Hcp_t0]]]].
              destruct (Z.eqb tidv tid) eqn:Heq_tv.
              ** apply Z.eqb_eq in Heq_tv. subst tidv.
                 rewrite Hget_t in Hget_t0. injection Hget_t0 as Heq_t00. subst t0.
                 exists t', op. split; [| split].
                 +++ rewrite HinU_lvs2, Z.eqb_refl. reflexivity.
                 +++ exact Hop.
                 +++ rewrite Hcp_t'. exact Hcp_t0.
              ** exists t0, op. split; [| split].
                 +++ rewrite HinU_lvs2, Heq_tv. cbv beta iota. exact Hget_t0.
                 +++ exact Hop.
                 +++ exact Hcp_t0.
           ++ exact I.
      * exists midv, ev, m. split; [| split; [| split; [| split]]].
        -- rewrite HevSt_lvs2_at, Heq_midv. cbv beta iota. exact Hgetv_lvs1.
        -- exact Hty.
        -- exact Hmf.
        -- exact HmfPCP.
        -- destruct m.(mfOwner) as [tidv|] eqn:Howner.
           ++ cbv beta iota in Howner_case.
              destruct Howner_case as [t0 [op [Hget_t0 [Hop Hcp_t0]]]].
              destruct (Z.eqb tidv tid) eqn:Heq_tv.
              ** apply Z.eqb_eq in Heq_tv. subst tidv.
                 rewrite Hget_t in Hget_t0. injection Hget_t0 as Heq_t00. subst t0.
                 exists t', op. split; [| split].
                 +++ rewrite HinU_lvs2, Z.eqb_refl. reflexivity.
                 +++ exact Hop.
                 +++ rewrite Hcp_t'. exact Hcp_t0.
              ** exists t0, op. split; [| split].
                 +++ rewrite HinU_lvs2, Heq_tv. cbv beta iota. exact Hget_t0.
                 +++ exact Hop.
                 +++ exact Hcp_t0.
           ++ exact I.
    + (* PTTask tidv *)
      cbv beta iota in Hpt_p.
      destruct Hpt_p as [t0 [Hgetv_lvs1 Hor]].
      destruct (Z.eqb tidv tid) eqn:Heq_tv.
      * apply Z.eqb_eq in Heq_tv. subst tidv.
        rewrite Hget_t in Hgetv_lvs1. injection Hgetv_lvs1 as Heq_t0. subst t0.
        exists t'. split.
        -- rewrite HinU_lvs2, Z.eqb_refl. reflexivity.
        -- destruct Hor as [Hcpp | [midv [ev [m [Hgetv_lvs1_m [Hty [Hmf [HmfPCP Howner]]]]]]]].
           ++ left. rewrite Hcp_t'. exact Hcpp.
           ++ right.
              destruct (Z.eqb midv mid) eqn:Heq_midv.
              ** apply Z.eqb_eq in Heq_midv. subst midv.
                 rewrite Hget_e1 in Hgetv_lvs1_m. injection Hgetv_lvs1_m as Heq_ev. subst ev.
                 exists mid, e2, m. split; [| split; [| split; [| split]]].
                 --- rewrite HevSt_lvs2_at, Z.eqb_refl. reflexivity.
                 --- rewrite He2_ety. exact Hty.
                 --- rewrite He2_mf. exact Hmf.
                 --- exact HmfPCP.
                 --- exact Howner.
              ** exists midv, ev, m. split; [| split; [| split; [| split]]].
                 --- rewrite HevSt_lvs2_at, Heq_midv. cbv beta iota. exact Hgetv_lvs1_m.
                 --- exact Hty.
                 --- exact Hmf.
                 --- exact HmfPCP.
                 --- exact Howner.
      * (* tidv ≠ tid *)
        exists t0. split.
        -- rewrite HinU_lvs2, Heq_tv. cbv beta iota. exact Hgetv_lvs1.
        -- destruct Hor as [Hcpp | [midv [ev [m [Hgetv_lvs1_m [Hty [Hmf [HmfPCP Howner]]]]]]]].
           ++ left. exact Hcpp.
           ++ right.
              destruct (Z.eqb midv mid) eqn:Heq_midv.
              ** apply Z.eqb_eq in Heq_midv. subst midv.
                 rewrite Hget_e1 in Hgetv_lvs1_m. injection Hgetv_lvs1_m as Heq_ev. subst ev.
                 exists mid, e2, m. split; [| split; [| split; [| split]]].
                 --- rewrite HevSt_lvs2_at, Z.eqb_refl. reflexivity.
                 --- rewrite He2_ety. exact Hty.
                 --- rewrite He2_mf. exact Hmf.
                 --- exact HmfPCP.
                 --- exact Howner.
              ** exists midv, ev, m. split; [| split; [| split; [| split]]].
                 --- rewrite HevSt_lvs2_at, Heq_midv. cbv beta iota. exact Hgetv_lvs1_m.
                 --- exact Hty.
                 --- exact Hmf.
                 --- exact HmfPCP.
                 --- exact Howner.
  - (* 3. mutex_owner_consistency *)
    unfold mutex_owner_consistency in *.
    intros midv ev mv [Hgetv [Htypev Hmfv]].
    rewrite HevSt_lvs2_at in Hgetv.
    destruct (Z.eqb midv mid) eqn:Heq_midv.
    + apply Z.eqb_eq in Heq_midv. subst midv.
      cbv beta iota in Hgetv. injection Hgetv as Heq_ev. subst ev.
      assert (Htype_lvs1 : e1.(eventType) = OS_EVENT_TYPE_MUTEX).
      { rewrite <- Htypev. rewrite He2_ety. reflexivity. }
      assert (Hmf_lvs1 : e1.(mutexFields) = Some mv).
      { rewrite <- Hmfv. rewrite He2_mf. reflexivity. }
      destruct (mv.(mfOwner)) as [tidv |] eqn:Howner.
      * pose proof (H_mo mid e1 mv (conj Hget_e1 (conj Htype_lvs1 Hmf_lvs1))) as Hmo_res.
        rewrite Howner in Hmo_res.
        cbv beta iota in Hmo_res.
        destruct Hmo_res as [t0 [op [Ht_lvs1 [Horig [Hcp_or Hnotin]]]]].
        destruct (Z.eqb tidv tid) eqn:Heq_tid.
        -- apply Z.eqb_eq in Heq_tid. subst tidv.
           rewrite Hget_t in Ht_lvs1. injection Ht_lvs1 as Heq_t. subst t0.
           exists t', op. split; [| split; [| split]].
           ++ rewrite HinU_lvs2, Z.eqb_refl. reflexivity.
           ++ exact Horig.
           ++ rewrite Hcp_t'. destruct Hcp_or as [Hcp | [Hne Hcp]].
              ** left. exact Hcp.
              ** right. split. exact Hne. exact Hcp.
           ++ rewrite He2_wl. intro Hin.
              apply Hnotin. apply remove_Z_eqb_in in Hin. exact Hin.
        -- exists t0, op. split; [| split; [| split]].
           ++ rewrite HinU_lvs2, Heq_tid. cbv beta iota. exact Ht_lvs1.
           ++ exact Horig.
           ++ exact Hcp_or.
           ++ rewrite He2_wl. intro Hin.
              apply Hnotin. apply remove_Z_eqb_in in Hin. exact Hin.
      * exact I.
    + cbv beta iota in Hgetv.
      destruct (mv.(mfOwner)) as [tidv |] eqn:Howner.
      * pose proof (H_mo midv ev mv (conj Hgetv (conj Htypev Hmfv))) as Hmo_res.
        rewrite Howner in Hmo_res.
        cbv beta iota in Hmo_res.
        destruct Hmo_res as [t0 [op [Ht_lvs1 [Horig [Hcp_or Hnotin]]]]].
        destruct (Z.eqb tidv tid) eqn:Heq_tid.
        -- apply Z.eqb_eq in Heq_tid. subst tidv.
           rewrite Hget_t in Ht_lvs1. injection Ht_lvs1 as Heq_t. subst t0.
           exists t', op. split; [| split; [| split]].
           ++ rewrite HinU_lvs2, Z.eqb_refl. reflexivity.
           ++ exact Horig.
           ++ rewrite Hcp_t'. destruct Hcp_or as [Hcp | [Hne Hcp]].
              ** left. exact Hcp.
              ** right. split. exact Hne. exact Hcp.
           ++ exact Hnotin.
        -- exists t0, op. split; [| split; [| split]].
           ++ rewrite HinU_lvs2, Heq_tid. cbv beta iota. exact Ht_lvs1.
           ++ exact Horig.
           ++ exact Hcp_or.
           ++ exact Hnotin.
      * exact I.
  - (* 4. verification_slice_event_wait_object_consistency *)
    unfold verification_slice_event_wait_object_consistency in *.
    destruct H_mw as [Hmw_entry [Hmw_total Hmw_closed]].
    split; [|split].
    + (* entry *)
      intros eidv ev Hgetv.
      rewrite HevSt_lvs2_at in Hgetv.
      destruct (Z.eqb eidv mid) eqn:Heq_eidv.
      * (* eidv = mid: e2.waitList = remove tid e1.waitList *)
        apply Z.eqb_eq in Heq_eidv. subst eidv.
        cbv beta iota in Hgetv. injection Hgetv as Heq_ev. subst ev.
        pose proof Hmw_entry as Hmw_entry_copy.
        specialize (Hmw_entry mid e1 Hget_e1) as [Hcanon Hmatch].
        unfold verification_slice_event_wait_entry_consistency.
        split.
        -- (* event_waitList_canonical *)
           unfold event_waitList_canonical in *.
           destruct Hcanon as [Hnd [Hssb Hforall]].
           split.
           ++ rewrite He2_wl. apply remove_Z_eqb_NoDup. exact Hnd.
           ++ split.
              ** rewrite He2_wl.
                 apply remove_Z_eqb_strictly_sorted_by.
                 apply strictly_sorted_by_key_ext with
                   (key := wait_prio_key sg (TskState lvs1)).
                 --- intros x. unfold wait_prio_key. rewrite HinU_lvs2.
                     destruct (Z.eqb x tid) eqn:Heq_x.
                     +++ apply Z.eqb_eq in Heq_x. subst x.
                         cbv beta iota. rewrite Hcp_t'. rewrite Hget_t.
                         cbv beta iota. reflexivity.
                     +++ cbv beta iota. reflexivity.
                 --- exact Hssb.
              ** intros tid_in Hin.
                 rewrite He2_wl in Hin.
                 assert (Hneq : tid_in <> tid).
                 { intro Heq. subst tid_in.
                   pose proof Hin as Hcopy.
                   apply remove_Z_eqb_notin in Hcopy. exact Hcopy. }
                 apply remove_Z_eqb_in in Hin.
                 destruct (Hforall tid_in Hin) as [t0 [Hget0 Hvp]].
                 exists t0. split.
                 +++ rewrite HinU_lvs2.
                     destruct (Z.eqb tid_in tid) eqn:Heq_tv.
                     ---- apply Z.eqb_eq in Heq_tv. subst tid_in. exfalso. apply Hneq. reflexivity.
                     ---- cbv beta iota. exact Hget0.
                 +++ exact Hvp.
        -- (* match event_type_to_pend_type e2.eventType *)
           assert (Hety2 : e2.(eventType) = e1.(eventType)) by exact He2_ety.
           rewrite Hety2.
           destruct (event_type_to_pend_type e1.(eventType)) eqn:Hety_e1.
           ++ (* Some pty *)
              cbv beta iota.
              cbv beta iota in Hmatch.
              intros tid_in Hin.
              rewrite He2_wl in Hin.
              assert (Hneq : tid_in <> tid).
              { intro Heq. subst tid_in.
                pose proof Hin as Hcopy.
                apply remove_Z_eqb_notin in Hcopy. exact Hcopy. }
              apply remove_Z_eqb_in in Hin.
              destruct (Hmatch tid_in Hin) as [t0 [Hget0 [Heptr0 [Hemptr0 Hpt0]]]].
              exists t0. repeat split.
              ** rewrite HinU_lvs2.
                 destruct (Z.eqb tid_in tid) eqn:Heq_tv.
                 --- apply Z.eqb_eq in Heq_tv. subst tid_in. exfalso. apply Hneq. reflexivity.
                 --- cbv beta iota. exact Hget0.
              ** exact Heptr0.
              ** exact Hemptr0.
              ** exact Hpt0.
           ++ (* None *)
              cbv beta iota.
              cbv beta iota in Hmatch.
              rewrite He2_wl. rewrite Hmatch. reflexivity.
      * (* eidv ≠ mid:lookup 不变,但需证明 tid 不在 ev.waitList *)
        assert (Hgetv_lvs1 : (EventState lvs1).(inUsedEventStates) eidv = Some ev).
        { destruct (Z.eqb eidv mid) eqn:Heq_midv.
          - exfalso. discriminate Heq_eidv.
          - cbv beta iota in Hgetv. exact Hgetv. }
        assert (Hne_mid : eidv <> mid) by (apply Z.eqb_neq; exact Heq_eidv).
        pose proof Hmw_entry as Hmw_entry_copy.
        specialize (Hmw_entry eidv ev Hgetv_lvs1) as [Hcanon_lvs1 Hmatch_lvs1].
        assert (Hnrid : ~ In tid ev.(waitList)).
        { intro Hin.
          destruct (event_type_to_pend_type ev.(eventType)) eqn:Hety_ev.
          - simpl in Hmatch_lvs1.
            specialize (Hmatch_lvs1 tid Hin) as [t0 [Hget0 [Heptr0 [_ _]]]].
            rewrite Hget_t in Hget0. inversion Hget0. subst t0.
            pose proof Hin_wl as Hin_e1.
            specialize (Hmw_entry_copy mid e1 Hget_e1) as [_ Hmatch_e1].
            destruct (event_type_to_pend_type e1.(eventType)) eqn:Hety_e1.
            + simpl in Hmatch_e1.
              specialize (Hmatch_e1 tid Hin_e1) as [t1 [Hget1 [Heptr1 [_ _]]]].
              rewrite Hget_t in Hget1. inversion Hget1. subst t1.
              rewrite Heptr0 in Heptr1.
              injection Heptr1 as Heidv_eq.
              exfalso. apply Hne_mid. exact Heidv_eq.
            + simpl in Hmatch_e1. rewrite Hmatch_e1 in Hin_e1. inversion Hin_e1.
          - simpl in Hmatch_lvs1. rewrite Hmatch_lvs1 in Hin. inversion Hin. }
        unfold verification_slice_event_wait_entry_consistency.
        split.
        -- (* event_waitList_canonical *)
           unfold event_waitList_canonical in *.
           destruct Hcanon_lvs1 as [Hnd [Hssb Hforall]].
           split.
           ** exact Hnd.
           ** split.
              +++ apply strictly_sorted_by_key_ext with
                    (key := wait_prio_key sg (TskState lvs1)).
                  --- intros x. unfold wait_prio_key. rewrite HinU_lvs2.
                      destruct (Z.eqb x tid) eqn:Heq_x.
                      ++++ apply Z.eqb_eq in Heq_x. subst x.
                           cbv beta iota. rewrite Hcp_t'. rewrite Hget_t.
                           cbv beta iota. reflexivity.
                      ++++ cbv beta iota. reflexivity.
                  --- exact Hssb.
              +++ intros tid_in Hin.
                  destruct (Z.eqb tid_in tid) eqn:Heq_tin.
                  **** apply Z.eqb_eq in Heq_tin. subst tid_in.
                       exfalso. apply Hnrid. exact Hin.
                  **** destruct (Hforall tid_in Hin) as [t0 [Hget0 Hvp]].
                       exists t0. split.
                       ***** rewrite HinU_lvs2. rewrite Heq_tin. cbv beta iota. exact Hget0.
                       ***** exact Hvp.
        -- (* match event_type_to_pend_type ev.eventType *)
           destruct (event_type_to_pend_type ev.(eventType)) eqn:Hety_ev.
           ** simpl.
              intros tid_in Hin.
              destruct (Z.eqb tid_in tid) eqn:Heq_tin.
              +++ apply Z.eqb_eq in Heq_tin. subst tid_in.
                  exfalso. apply Hnrid. exact Hin.
              +++ simpl in Hmatch_lvs1.
                  specialize (Hmatch_lvs1 tid_in Hin) as [t0 [Hget0 [Heptr0 [Hemptr0 Hpt0]]]].
                  exists t0. repeat split.
                  ++++ rewrite HinU_lvs2. rewrite Heq_tin. cbv beta iota. exact Hget0.
                  ++++ exact Heptr0.
                  ++++ exact Hemptr0.
                  ++++ exact Hpt0.
           ** simpl. exact Hmatch_lvs1.
    + (* total reference backlink *)
      intros tidv t0 midv ev Ht Hgetv Href.
      rewrite HinU_lvs2 in Ht.
      destruct (Z.eqb tidv tid) eqn:Heq_tidv.
      * apply Z.eqb_eq in Heq_tidv. subst tidv.
        cbv beta iota in Ht. injection Ht as Heq_t. subst t0.
        rewrite Ht' in Href. cbn in Href. rewrite Hmulti_t in Href.
        destruct Href as [Hnone | Hin_nil]; [discriminate|contradiction].
      * cbv beta iota in Ht.
        rewrite HevSt_lvs2_at in Hgetv.
        destruct (Z.eqb midv mid) eqn:Heq_midv.
        -- apply Z.eqb_eq in Heq_midv. subst midv.
           cbv beta iota in Hgetv. injection Hgetv as Heq_ev. subst ev.
           rewrite He2_wl. apply remove_Z_eqb_in_neq.
           ++ intro Heq. subst tidv. rewrite Z.eqb_refl in Heq_tidv. discriminate.
           ++ eapply Hmw_total; eauto.
        -- cbv beta iota in Hgetv. eapply Hmw_total; eauto.
    + (* live-reference closure *)
      unfold task_event_reference_closure in Hmw_closed |- *.
      intros tidv t0 Ht.
      rewrite HinU_lvs2 in Ht.
      destruct (Z.eqb tidv tid) eqn:Heq_tidv.
      * apply Z.eqb_eq in Heq_tidv. subst tidv.
        cbv beta iota in Ht. injection Ht as Heq_t. subst t0.
        rewrite Ht'. cbn. rewrite Hmulti_t. split.
        -- intros eid Hnone. discriminate.
        -- intros eid Hin_nil. contradiction.
      * cbv beta iota in Ht.
        specialize (Hmw_closed tidv t0 Ht) as [Hsingle Hmulti].
        split.
        -- intros eid Hptr. destruct (Hsingle eid Hptr) as [e0 He0].
           rewrite HevSt_lvs2_at. destruct (Z.eqb eid mid); eauto.
        -- intros eid Hin. destruct (Hmulti eid Hin) as [e0 He0].
           rewrite HevSt_lvs2_at. destruct (Z.eqb eid mid); eauto.
  - (* 5. ready_list_completeness *)
    unfold ready_list_completeness in *.
    intros tidv t0 Hget0 Heff.
    rewrite HinU_lvs2 in Hget0.
    destruct (Z.eqb tidv tid) eqn:Heq_tidv.
    + apply Z.eqb_eq in Heq_tidv. subst tidv.
      cbv beta iota in Hget0. injection Hget0 as Heq_t. subst t0.
      rewrite Hrl_lvs2. apply (H_rlc tid t).
      * exact Hget_t.
      * unfold is_effectively_ready in *.
        rewrite <- Hstat_t', <- Hdly_t'. exact Heff.
    + cbv beta iota in Hget0.
      rewrite Hrl_lvs2. apply (H_rlc tidv t0).
      * exact Hget0.
      * exact Heff.
  - (* 6. ready_list_order *)
    unfold ready_list_order in *.
    destruct H_rlo as [Hsorted Hnd].
    split.
    + rewrite Hrl_lvs2.
      apply strictly_sorted_by_key_ext with
        (key := fun tidv => match (TskState lvs1).(inUsedTaskStates) tidv with
                           | Some task => task.(curPrio)
                           | None => sg.(osLowestPrio) + 1
                           end).
      * intros x. rewrite HinU_lvs2.
        destruct (Z.eqb x tid) eqn:Heq_x.
        -- apply Z.eqb_eq in Heq_x. subst x.
           cbv beta iota. rewrite Hcp_t'. rewrite Hget_t. cbv beta iota. reflexivity.
        -- cbv beta iota. reflexivity.
      * exact Hsorted.
    + rewrite Hrl_lvs2. exact Hnd.
  - (* 7. ceiling_priotbl_free *)
    unfold ceiling_priotbl_free in *. rewrite HprioTbl_lvs2. exact H_ceil.
  - (* 8. task_priority_unique_prop *)
    unfold task_priority_unique_prop in *.
    unfold task_priority_unique in *.
    intros tid1 tid2 t1 t2 Hget1 Hget2 Hcp_eq.
    assert (Hget1' : (if Z.eqb tid1 tid then Some t'
                      else (TskState lvs1).(inUsedTaskStates) tid1) = Some t1).
    { rewrite <- HinU_lvs2. exact Hget1. }
    assert (Hget2' : (if Z.eqb tid2 tid then Some t'
                      else (TskState lvs1).(inUsedTaskStates) tid2) = Some t2).
    { rewrite <- HinU_lvs2. exact Hget2. }
    destruct (Z.eqb tid1 tid) eqn:Heq1.
    + apply Z.eqb_eq in Heq1. subst tid1.
      cbv beta iota in Hget1'. injection Hget1' as Heq_t1. subst t1.
      destruct (Z.eqb tid2 tid) eqn:Heq2.
      * apply Z.eqb_eq in Heq2. subst tid2. reflexivity.
      * cbv beta iota in Hget2'.
        apply (H_tpu tid tid2 t t2).
        -- exact Hget_t.
        -- exact Hget2'.
        -- rewrite <- Hcp_t'. exact Hcp_eq.
    + cbv beta iota in Hget1'.
      destruct (Z.eqb tid2 tid) eqn:Heq2.
      * apply Z.eqb_eq in Heq2. subst tid2.
        cbv beta iota in Hget2'. injection Hget2' as Heq_t2. subst t2.
        apply (H_tpu tid1 tid t1 t).
        -- exact Hget1'.
        -- exact Hget_t.
        -- rewrite Hcp_t' in Hcp_eq. exact Hcp_eq.
      * cbv beta iota in Hget2'.
        apply (H_tpu tid1 tid2 t1 t2).
        -- exact Hget1'.
        -- exact Hget2'.
        -- exact Hcp_eq.
  - (* 9. mutex_protocol_consistency:event waitList-only update *)
    unfold mutex_protocol_consistency in *.
    intros midv ev mv Hgetv Htypev Hmfv.
    rewrite HevSt_lvs2_at in Hgetv.
    destruct (Z.eqb midv mid) eqn:Heq_midv.
    + apply Z.eqb_eq in Heq_midv. subst midv.
      cbv beta iota in Hgetv. inversion Hgetv; subst ev.
      rewrite He2 in Htypev, Hmfv. cbv beta iota in Htypev, Hmfv.
      specialize (H_protocol mid e1 mv Hget_e1 Htypev Hmfv).
      rewrite HprioTbl_lvs2. exact H_protocol.
    + cbv beta iota in Hgetv.
      specialize (H_protocol midv ev mv Hgetv Htypev Hmfv).
      rewrite HprioTbl_lvs2. exact H_protocol.
  - (* 10. mutex_enabled_pcp_unique:event removal from waitList keeps PCP *)
    eapply mutex_enabled_pcp_unique_transport with (lvs1 := lvs1).
    + intros midv ev mv Hgetv Htypev Hmfv.
      rewrite HevSt_lvs2_at in Hgetv.
      destruct (Z.eqb midv mid) eqn:Heq_midv.
      * apply Z.eqb_eq in Heq_midv. subst midv.
        cbv beta iota in Hgetv. inversion Hgetv; subst ev.
        rewrite He2 in Htypev, Hmfv. cbv beta iota in Htypev, Hmfv.
        exists e1, mv. repeat split; try assumption; reflexivity.
      * cbv beta iota in Hgetv.
        exists ev, mv. repeat split; try assumption; reflexivity.
    + exact H_pcp_unique.
Qed.

Definition atomic_event_task_remove_happens
           (tid : TaskID) (mid : EventID) (lvs1 : UCOS2_Verify_State) : Prop :=
  exists lvs2, atomic_event_task_remove tid mid lvs1 tt lvs2.

Definition atomic_task_pend_cleanup (tid : TaskID)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists t t',
      (lvs1.(TskState).(inUsedTaskStates)) tid = Some t /\
      t' = {| taskID        := t.(taskID);
     taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
              curPrio        := t.(curPrio);
              stat           := (task_status_single None ((task_is_suspended t.(stat))));
              statPend       := PendOK;
              dly            := t.(dly);
              eventPtr       := None;
              eventMultiWaitEvents  := t.(eventMultiWaitEvents);
              eventMultiRdy  := t.(eventMultiRdy);
              msg            := t.(msg);
              nextTCB        := t.(nextTCB);
              prevTCB        := t.(prevTCB);
              delReq         := t.(delReq);
           |} /\
      lvs2 = replace_TskS
        {| inUsedTaskStates := fun tid' =>
             if Z.eqb tid' tid then Some t'
             else (lvs1.(TskState).(inUsedTaskStates)) tid';
           unUsedTaskStates := (lvs1.(TskState).(unUsedTaskStates));
           tcbListHead      := (lvs1.(TskState).(tcbListHead));
           prioTbl          := (lvs1.(TskState).(prioTbl));
           taskRegNextID := (lvs1.(TskState).(taskRegNextID));
           parkedTaskStacks := (lvs1.(TskState).(parkedTaskStacks));
           taskLifecycle := (lvs1.(TskState).(taskLifecycle));
     taskCount        := (lvs1.(TskState).(taskCount)); |}
        lvs1.

Lemma atomic_mutex_release_with_handover_preserves_neutral_fields :
  forall sg mid lvs1 new_owner lvs2,
    atomic_mutex_release_with_handover sg mid lvs1 new_owner lvs2 ->
    IntrState lvs1 = IntrState lvs2 /\
    TickState lvs1 = TickState lvs2.
Proof.
  intros sg mid lvs1 new_owner lvs2 Hatomic.
  destruct Hatomic as [e1 [e2 [m1 [m2 [old_owner [new_owner_t
    [new_owner_t' [evSt2 [tskSt2 [schedSt1 [schedSt2 [newReadyList
    [rest_waitlist Hconj]]]]]]]]]]]]].
  destruct Hconj as
    (Hget_e1 & Htype & Hmf1 & Howner_old & Hwl_def &
     Hget_new_owner & Hnew_owner_t'_def &
     Hm2_def & He2_def & HevSt2_def & HschedSt1_def &
     HnewReadyList_def & HschedSt2_def & HtskSt2_def & Hlvs2).
  rewrite Hlvs2. split; reflexivity.
Qed.

(* ---- atomic_mutex_del_prepare:owner restore + ready-all waiters + evSt clear ---- *)
Lemma atomic_mutex_del_prepare_preserves_neutral_fields :
  forall sg mid lvs1 lvs2,
    atomic_mutex_del_prepare sg mid lvs1 tt lvs2 ->
    IntrState lvs1 = IntrState lvs2 /\
    TickState lvs1 = TickState lvs2.
Proof.
  intros sg mid lvs1 lvs2 Hatomic.
  destruct Hatomic as [e1 [m1 [lvs_owner [tskSt2 [ready_after [schedSt2 [evSt2 Hconj]]]]]]].
  destruct Hconj as [Hget_e1 [Htype [Hmf1 [Howner_restore
    [HtskSt2_def [Hready_after_def [HschedSt2_def [HevSt2_def Hlvs2]]]]]]]].
  pose proof
    (atomic_mutex_del_owner_restore_preserves_neutral_fields
       sg m1 lvs1 lvs_owner Howner_restore)
    as [Hintr_eq [Hevent_eq Htick_eq]].
  rewrite Hlvs2. simpl. split; assumption.
Qed.

Definition atomic_mutex_del_no_pend_prepare (mid : EventID)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists e1 m1 evSt2,
      (lvs1.(EventState).(inUsedEventStates)) mid = Some e1 /\
      e1.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e1.(mutexFields) = Some m1 /\
      e1.(waitList) = [] /\
      evSt2 =
        update_event_field_raw
          lvs1.(EventState)
          mid
          {| eventGeneration := e1.(eventGeneration);
             eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
             eventType   := e1.(eventType);
             mutexFields := Some {| mfPCP := m1.(mfPCP);
                                    mfOwner := None;
                                    mfOwnerOrigPrio := None; |};
             semFields   := e1.(semFields);
             mboxFields  := e1.(mboxFields);
             queueFields := e1.(queueFields);
             waitList    := [];
          |} /\
      lvs2 = replace_EventS evSt2 lvs1.

(* ---- atomic_event_free_with_priotbl_free:tskSt 改 prioTbl(free),evSt 改 event removed ---- *)
Lemma atomic_event_free_with_priotbl_free_sched_inv_preserved :
  forall sg mid lvs1 lvs2,
    atomic_event_free_with_priotbl_free sg mid lvs1 tt lvs2 ->
    verification_slice_sched_inv sg (TskState lvs1) (SchedState lvs1) |--
    verification_slice_sched_inv sg (TskState lvs2) (SchedState lvs2).
Proof.
  intros sg mid lvs1 lvs2 Hatomic.
  destruct Hatomic as [e1 [m1 [evSt2 [tskSt2 Hconj]]]].
  destruct Hconj as [Hget_e1 [Htype [Hmf1 [Howner_n [Hwl
    [HevSt2_def [HtskSt2_def Hlvs2]]]]]]].
  assert (HinU_func : (TskState lvs2).(inUsedTaskStates) = (TskState lvs1).(inUsedTaskStates)).
  { apply functional_extensionality.
    intros tid. rewrite Hlvs2. rewrite HtskSt2_def. reflexivity. }
  assert (Hsched : SchedState lvs2 = SchedState lvs1).
  { rewrite Hlvs2. reflexivity. }
  rewrite Hsched.
  rewrite (verification_slice_sched_inv_ext sg (TskState lvs2) (TskState lvs1) (SchedState lvs1) HinU_func).
  apply derivable1_refl.
Qed.

Lemma atomic_event_free_with_priotbl_free_preserves_neutral_fields :
  forall sg mid lvs1 lvs2,
    atomic_event_free_with_priotbl_free sg mid lvs1 tt lvs2 ->
    IntrState lvs1 = IntrState lvs2 /\
    SchedState lvs1 = SchedState lvs2 /\
    TickState lvs1 = TickState lvs2.
Proof.
  intros sg mid lvs1 lvs2 Hatomic.
  destruct Hatomic as [e1 [m1 [evSt2 [tskSt2 Hconj]]]].
  destruct Hconj as [Hget_e1 [Htype [Hmf1 [Howner_n [Hwl
    [HevSt2_def [HtskSt2_def Hlvs2]]]]]]].
  rewrite Hlvs2. split; [reflexivity | split; reflexivity].
Qed.

(* ---- atomic_mutex_create:tskSt 改 prioTbl(reserve),evSt 改 event alloc ---- *)
Lemma atomic_mutex_create_sched_inv_preserved :
  forall sg pcp lvs1 oid lvs2,
    atomic_mutex_create sg pcp lvs1 oid lvs2 ->
    verification_slice_sched_inv sg (TskState lvs1) (SchedState lvs1) |--
    verification_slice_sched_inv sg (TskState lvs2) (SchedState lvs2).
Proof.
  intros sg pcp lvs1 oid lvs2 Hatomic.
  destruct Hatomic as [eid [rest [_ [_ [_ ->]]]]].
  unfold mutex_create_state; cbn [replace_EventS replace_TskS].
  rewrite (verification_slice_sched_inv_ext sg lvs1.(TskState)
    (mutex_create_priority_state sg pcp lvs1.(TskState))
    lvs1.(SchedState) eq_refl).
  apply derivable1_refl.
Qed.

Lemma atomic_mutex_create_preserves_neutral_fields :
  forall sg pcp lvs1 oid lvs2,
    atomic_mutex_create sg pcp lvs1 oid lvs2 ->
    IntrState lvs1 = IntrState lvs2 /\
    SchedState lvs1 = SchedState lvs2 /\
    TickState lvs1 = TickState lvs2.
Proof.
  intros sg pcp lvs1 oid lvs2 Hcreate.
  destruct Hcreate as [eid [rest [_ [_ [_ ->]]]]].
  split; [reflexivity|split; reflexivity].
Qed.

(* The cross-module protocol is preserved by the exact acquire transformer.
   The complete invariant theorem below additionally discharges the concrete
   task/scheduler/event representation slices. *)
Lemma atomic_mutex_acquire_preserves_cross_module :
  forall sg mid tid origPrio lvs1 lvs2,
    atomic_mutex_acquire mid tid origPrio lvs1 tt lvs2 ->
    valid_task_prio sg origPrio ->
    task_current_prio_registered (TskState lvs1) ->
    verification_slice_cross_module_consistency sg lvs1 ->
    verification_slice_cross_module_consistency sg lvs2.
Proof.
  intros sg mid tid origPrio lvs1 lvs2 Hatomic Hvalid_orig Hregistered Hcm.
  destruct Hatomic as [e1 [e2 [m1 [m2 [t_acquire
    [Hget_e1 [Htype [Hmf1 [Howner_n [Hcur [Htask [Hprio [Hpend
      [Hm2 [He2 Hlvs2]]]]]]]]]]]]]]].
  subst m2. subst e2.
  assert (Hlvs2_eq : lvs2 =
    replace_EventS (owner_acquire_update (EventState lvs1) mid e1 m1 tid origPrio) lvs1).
  { rewrite Hlvs2. unfold update_event_field.
    unfold owner_acquire_update, update_event_field_raw. reflexivity. }
  rewrite Hlvs2_eq.
  apply (verification_slice_cross_module_consistency_preserved_by_acquire sg lvs1 mid e1 m1 tid origPrio t_acquire).
  - exact Hget_e1.
  - exact Htype.
  - exact Hmf1.
  - exact Howner_n.
  - exact Htask.
  - exact Hprio.
  - exact Hpend.
  - exact Hvalid_orig.
  - exact Hregistered.
  - exact Hcm.
Qed.

(* valid_task_prio sg p implies p ≠ osPrioMutexCeilDis.
   依据:osPrioMutexCeilDis = 0xFF = 255,osLowestPrio <= 63,
   valid_task_prio 给出 p < osLowestPrio,故 p < 63 < 255 = ceil。 *)
Lemma valid_task_prio_ne_ceil :
  forall sg p,
    valid_stable_glob_vars sg ->
    valid_task_prio sg p ->
    p <> sg.(osPrioMutexCeilDis).
Proof.
  intros sg p Hvsg Hvp.
  unfold valid_stable_glob_vars in Hvsg.
  unfold valid_task_prio in Hvp.
  destruct Hvp as [Hp_lo Hp_hi].
  destruct Hvsg as [_ [_ [_ [_ [Hlo_63 [_ [_ [_ [Hceil _]]]]]]]]].
  lia.
Qed.

(* verification_slice_event_in_range 在 owner_acquire_update(mfOwner None→Some tid)下保持。
   仅 mid 处 event 的 mutexFields 变化,其余 event 结构不变。
   新 m2 需满足 mutex_fields_consistency(0 <= origPrio <= osLowestPrio /\ ≠ ceil),
   由 valid_task_prio + valid_stable_glob_vars 保证。 *)
Lemma verification_slice_event_in_range_preserved_by_owner_acquire :
  forall sg tskSt evSt mid e1 m1 tid origPrio,
    valid_stable_glob_vars sg ->
    evSt.(inUsedEventStates) mid = Some e1 ->
    e1.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e1.(mutexFields) = Some m1 ->
    m1.(mfOwner) = None ->
    valid_task_prio sg origPrio ->
    verification_slice_event_in_range sg tskSt evSt ->
    verification_slice_event_in_range sg tskSt (owner_acquire_update evSt mid e1 m1 tid origPrio).
Proof.
  intros sg tskSt evSt mid e1 m1 tid origPrio Hvsg Hget Htype Hmf Howner_n Hprio Hin.
  unfold verification_slice_event_in_range in *.
  destruct Hin as [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]].
  unfold owner_acquire_update, update_event_field_raw.
  simpl.
  split.
  - (* 1: eid range *)
    intros eid e Hget'.
    destruct (Z.eqb eid mid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst eid.
      inversion Hget'; subst.
      apply (H1 mid e1 Hget).
    + exact (H1 eid e Hget').
  - split; [exact H2 |].
    split; [exact H3 |].
    split.
    + (* 4: unUsed vs inUsed disjoint *)
      eapply event_slot_partition_preserved_some_to_some; eauto.
    + split.
      { (* 5: event_fields_consistency *)
        intros eid e Hget'.
        destruct (Z.eqb eid mid) eqn:Heq.
        - apply Z.eqb_eq in Heq. subst eid.
          inversion Hget'; subst.
          unfold event_fields_consistency.
          rewrite Htype.
          assert (Hefc : event_fields_consistency e1) by (exact (H5 mid e1 Hget)).
          unfold event_fields_consistency in Hefc.
          rewrite Htype in Hefc.
          destruct Hefc as [_ [Hsem [Hmbox Hqueue]]].
          repeat split; [discriminate | exact Hsem | exact Hmbox | exact Hqueue].
        - exact (H5 eid e Hget'). }
      { split.
        - (* 6: event payload consistency *)
          intros eid e Hget'.
          destruct (Z.eqb eid mid) eqn:Heq.
          + apply Z.eqb_eq in Heq. subst eid.
            inversion Hget'; subst.
            unfold event_payload_consistency. rewrite Htype. simpl.
            split.
            * unfold mutex_fields_consistency. simpl.
              unfold valid_task_prio in Hprio.
              destruct Hprio as [Hp_lo Hp_hi].
              split. exact Hp_lo.
              split. lia.
              apply (valid_task_prio_ne_ceil sg origPrio Hvsg).
              unfold valid_task_prio. split; [exact Hp_lo | exact Hp_hi].
            * intros Hnone. discriminate Hnone.
          + exact (H6 eid e Hget').
        - split;
          [ eapply queue_binding_unique_update_same_binding;
            [ exact Hget
            | unfold event_queue_id; rewrite Htype; reflexivity
            | exact H7 ]
          |].
          (* 8: verification_slice_event_wait_entry_consistency *)
          intros eid e Hget'.
          destruct (Z.eqb eid mid) eqn:Heq.
          + apply Z.eqb_eq in Heq. subst eid.
            inversion Hget'; subst.
            eapply (verification_slice_event_wait_entry_consistency_irrelevant_fields sg tskSt mid e1).
            * simpl. reflexivity.
            * simpl. reflexivity.
            * exact (H8 mid e1 Hget).
          + exact (H8 eid e Hget'). }
Qed.

(* Empty-wait-list release and waiter handover retain their literal raw
   relations.  No unconditional cross-module release wrapper is exported:
   after the source removed the old-owner lookup and priority-equality guards,
   nested/out-of-order release needs an operation-family protocol theorem to
   re-establish the stable invariant. *)
Definition OSMutexCreate_sem (sg : StableGlobVars) (pcp : Priority)
  : program UCOS2_Verify_State (OSErrCode * option EventID) :=
  fun lvs1 ret lvs2 =>
    let perr := fst ret in
    let oid := snd ret in
    (pcp <> sg.(osPrioMutexCeilDis) /\ pcp >= sg.(osLowestPrio) /\
     perr = OS_ERR_PRIO_INVALID /\ oid = None /\ lvs2 = lvs1) \/
    (pcp < sg.(osLowestPrio) /\
     lvs1.(IntrState).(intNesting) > 0 /\
     perr = OS_ERR_CREATE_ISR /\ oid = None /\ lvs2 = lvs1) \/
    (pcp <> sg.(osPrioMutexCeilDis) /\ pcp < sg.(osLowestPrio) /\
     lvs1.(IntrState).(intNesting) <= 0 /\
     (lvs1.(TskState).(prioTbl)) pcp <> PTFree /\
     perr = OS_ERR_PRIO_EXIST /\ oid = None /\ lvs2 = lvs1) \/
    (* PEVENT_NULL 路径(简化:不在 sem 中建模 rollback,留给 spec 描述) *)
    (pcp <> sg.(osPrioMutexCeilDis) /\ pcp < sg.(osLowestPrio) /\
     lvs1.(IntrState).(intNesting) <= 0 /\
     (lvs1.(TskState).(prioTbl)) pcp = PTFree /\
     lvs1.(EventState).(unUsedEventStates) = [] /\
     perr = OS_ERR_PEVENT_NULL /\ oid = None /\ lvs2 = lvs1) \/
    (pcp = sg.(osPrioMutexCeilDis) /\
     lvs1.(IntrState).(intNesting) > 0 /\
     perr = OS_ERR_CREATE_ISR /\ oid = None /\ lvs2 = lvs1) \/
    (pcp = sg.(osPrioMutexCeilDis) /\
     lvs1.(IntrState).(intNesting) <= 0 /\
     lvs1.(EventState).(unUsedEventStates) = [] /\
     perr = OS_ERR_PEVENT_NULL /\ oid = None /\ lvs2 = lvs1) \/
    (* 成功路径:用单一复合 atomic_mutex_create 替代 4 步链,
       避免 atomic_priotbl_reserve 等中间步独立保持不变式的问题
       (详见 README "已知建模问题" 节)。 *)
    (exists eid,
       lvs1.(IntrState).(intNesting) <= 0 /\
       (pcp = sg.(osPrioMutexCeilDis) \/
        (pcp <> sg.(osPrioMutexCeilDis) /\
         pcp < sg.(osLowestPrio) /\
         (lvs1.(TskState).(prioTbl)) pcp = PTFree)) /\
       atomic_mutex_create sg pcp lvs1 (Some eid) lvs2 /\
       perr = OS_ERR_NONE /\ oid = Some eid).

Definition OSMutexAccept_sem (sg : StableGlobVars) (pevent : addr)
  : program UCOS2_Verify_State (OSErrCode * bool) :=
  fun lvs1 ret lvs2 =>
    let perr := fst ret in
    let ok := snd ret in
    (pevent = 0 /\ perr = OS_ERR_PEVENT_NULL /\ ok = false /\ lvs2 = lvs1) \/
    (pevent <> 0 /\
     (exists eid, pevent = event_addr sg eid /\
                 (lvs1.(EventState).(inUsedEventStates)) eid = None /\
                 perr = OS_ERR_EVENT_TYPE /\ ok = false /\ lvs2 = lvs1)) \/
    (pevent <> 0 /\
     (exists eid e, pevent = event_addr sg eid /\
                  (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
                  e.(eventType) <> OS_EVENT_TYPE_MUTEX /\
                  perr = OS_ERR_EVENT_TYPE /\ ok = false /\ lvs2 = lvs1)) \/
    (pevent <> 0 /\
     lvs1.(IntrState).(intNesting) > 0 /\
     (exists eid e,
        pevent = event_addr sg eid /\
        (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
        e.(eventType) = OS_EVENT_TYPE_MUTEX /\
        perr = OS_ERR_PEND_ISR /\ ok = false /\ lvs2 = lvs1)) \/
    (* mutex available: acquire *)
    (pevent <> 0 /\
     lvs1.(IntrState).(intNesting) <= 0 /\
     (exists eid e m tid op lvs_a,
        pevent = event_addr sg eid /\
        (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
        e.(eventType) = OS_EVENT_TYPE_MUTEX /\
        e.(mutexFields) = Some m /\ m.(mfOwner) = None /\
        (lvs1.(SchedState).(curTaskID)) = Some tid /\
        (exists t, (lvs1.(TskState).(inUsedTaskStates)) tid = Some t /\
                   op = t.(curPrio) /\ (task_non_suspension_bits (t.(stat))) = 0) /\
        atomic_mutex_acquire eid tid op lvs1 tt lvs_a /\
        ((m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\ op <= m.(mfPCP) /\
          perr = OS_ERR_PCP_LOWER) \/
         ((m.(mfPCP) = sg.(osPrioMutexCeilDis) \/
           op > m.(mfPCP)) /\ perr = OS_ERR_NONE)) /\
        ok = true /\ lvs2 = lvs_a)) \/
    (* mutex unavailable: non-blocking false return *)
    (pevent <> 0 /\
     lvs1.(IntrState).(intNesting) <= 0 /\
     (exists eid e m,
        pevent = event_addr sg eid /\
        (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
        e.(eventType) = OS_EVENT_TYPE_MUTEX /\
        e.(mutexFields) = Some m /\ m.(mfOwner) <> None /\
        perr = OS_ERR_NONE /\ ok = false /\ lvs2 = lvs1)).

(* ================================================================== *)
(* Phase 11: OSMutexDel raw function semantics                        *)
(* ================================================================== *)
(* OSMutexDel C 代码 os_mutex.c:301-423:                              *)
(*   1. pevent == 0                  -> OS_ERR_PEVENT_NULL / pevent   *)
(*   2. eventType != MUTEX           -> OS_ERR_EVENT_TYPE / pevent    *)
(*   3. OSIntNesting > 0             -> OS_ERR_DEL_ISR / pevent       *)
(*   4. opt = OS_DEL_NO_PEND + 有 waiter -> OS_ERR_TASK_WAITING       *)
(*   5. opt = OS_DEL_NO_PEND + 无 waiter -> 释放(event_free_with_X)  *)
(*   6. opt = OS_DEL_ALWAYS          -> disinherit + rdy all + 释放  *)
(*   7. opt invalid                   -> OS_ERR_INVALID_OPT           *)
(* 返回 (OSErrCode * option addr):NULL=已删,非 NULL=未删             *)

Inductive DelOpt : Type :=
| OS_DEL_NO_PEND
| OS_DEL_ALWAYS
| OS_DEL_INVALID.

Definition OSMutexDel_sem (sg : StableGlobVars) (pevent : addr) (opt : DelOpt)
  : program UCOS2_Verify_State (OSErrCode * option addr) :=
  fun lvs1 ret lvs2 =>
    let perr := fst ret in
    let oret := snd ret in
    (pevent = 0 /\ perr = OS_ERR_PEVENT_NULL /\ oret = Some pevent /\ lvs2 = lvs1) \/
    (pevent <> 0 /\
     exists eid, pevent = event_addr sg eid /\
                  (lvs1.(EventState).(inUsedEventStates)) eid = None /\
                  perr = OS_ERR_EVENT_TYPE /\ oret = Some pevent /\ lvs2 = lvs1) \/
    (pevent <> 0 /\
     exists eid e, pevent = event_addr sg eid /\
                   (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
                   e.(eventType) <> OS_EVENT_TYPE_MUTEX /\
                   perr = OS_ERR_EVENT_TYPE /\ oret = Some pevent /\ lvs2 = lvs1) \/
    (pevent <> 0 /\
     exists eid e m, pevent = event_addr sg eid /\
                     (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
                     e.(eventType) = OS_EVENT_TYPE_MUTEX /\
                     e.(mutexFields) = Some m /\
                     lvs1.(IntrState).(intNesting) > 0 /\
                     perr = OS_ERR_DEL_ISR /\ oret = Some pevent /\ lvs2 = lvs1) \/
    (pevent <> 0 /\
     lvs1.(IntrState).(intNesting) <= 0 /\
     opt = OS_DEL_NO_PEND /\
     exists eid e m, pevent = event_addr sg eid /\
                      (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
                      e.(eventType) = OS_EVENT_TYPE_MUTEX /\
                      e.(mutexFields) = Some m /\
                      e.(waitList) <> [] /\
                      perr = OS_ERR_TASK_WAITING /\ oret = Some pevent /\ lvs2 = lvs1) \/
    (pevent <> 0 /\
     lvs1.(IntrState).(intNesting) <= 0 /\
     opt = OS_DEL_INVALID /\
     exists eid e m, pevent = event_addr sg eid /\
                      (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
                      e.(eventType) = OS_EVENT_TYPE_MUTEX /\
                      e.(mutexFields) = Some m /\
     perr = OS_ERR_INVALID_OPT /\ oret = Some pevent /\ lvs2 = lvs1) \/
    (* NO_PEND 成功:源码只检查 waitList 为空,随后清理并释放 event/PCP。 *)
    (pevent <> 0 /\
     lvs1.(IntrState).(intNesting) <= 0 /\
     opt = OS_DEL_NO_PEND /\
     exists eid e m lvs_p lvs_f,
       pevent = event_addr sg eid /\
       (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\
       e.(mutexFields) = Some m /\ e.(waitList) = [] /\
       atomic_mutex_del_no_pend_prepare eid lvs1 tt lvs_p /\
       atomic_event_free_with_priotbl_free sg eid lvs_p tt lvs_f /\
       perr = OS_ERR_NONE /\ oret = None /\ lvs2 = lvs_f) \/
    (* ALWAYS 成功:owner restore + focused ready-all + final free.
       The source snapshots tasks_waiting before the loop and calls OS_Sched
       after leaving the critical section iff that snapshot was true. *)
    (pevent <> 0 /\
     lvs1.(IntrState).(intNesting) <= 0 /\
     opt = OS_DEL_ALWAYS /\
     exists eid e m lvs_owner lvs_ready lvs_p lvs_f,
       pevent = event_addr sg eid /\
       (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\
       e.(mutexFields) = Some m /\
       atomic_mutex_del_owner_restore sg m lvs1 tt lvs_owner /\
       atomic_event_task_rdy_all_mutex_abort sg eid lvs_owner tt lvs_ready /\
       atomic_mutex_del_no_pend_prepare eid lvs_ready tt lvs_p /\
       atomic_event_free_with_priotbl_free sg eid lvs_p tt lvs_f /\
       perr = OS_ERR_NONE /\ oret = None /\
       ((e.(waitList) = [] /\ lvs2 = lvs_f) \/
        (e.(waitList) <> [] /\
         exists sched_res lvs_s,
           atomic_sched lvs_f sched_res lvs_s /\
           lvs2 = lvs_s))).

(* No [OSMutexDel_preserves_inv] theorem is stated here.  Its raw semantics is
   retained above, but the successful branches cross a source-real transient
   owner-clear/PCP-free state.  A sound proof must use a Delete staging
   invariant or one atomic full-pre/full-post linearization. *)

(* ================================================================== *)
(* Phase 12: OSMutexPost raw function semantics                       *)
(* ================================================================== *)
(* OSMutexPost C 代码 os_mutex.c:642-705:                             *)
(*   1. OSIntNesting > 0             -> OS_ERR_POST_ISR                *)
(*   2. pevent == 0                   -> OS_ERR_PEVENT_NULL            *)
(*   3. eventType != MUTEX            -> OS_ERR_EVENT_TYPE             *)
(*   4. OSTCBCur != mfOwner           -> OS_ERR_NOT_MUTEX_OWNER        *)
(*   5. waitList 空(可选 disinherit owner)+ atomic_mutex_release    *)
(*   6. waitList 非空(可选 disinherit)+ atomic_mutex_release_with_handover *)

Definition OSMutexPost_disinherit_sem (sg : StableGlobVars) (m : MutexFields)
           (cur_tid : TaskID) (lvs1 lvs_d : UCOS2_Verify_State) : Prop :=
  exists cur_t,
    lvs1.(TskState).(inUsedTaskStates) cur_tid = Some cur_t /\
    ((m.(mfPCP) = sg.(osPrioMutexCeilDis) /\
      lvs_d = lvs1) \/
     (m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\
      cur_t.(curPrio) <> m.(mfPCP) /\
      lvs_d = lvs1) \/
     (m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\
      cur_t.(curPrio) = m.(mfPCP) /\
      exists orig,
        m.(mfOwnerOrigPrio) = Some orig /\
        (* OSMutexPost passes OSTCBCur to the literal helper.  The helper
           removes that ready task, rewrites its priority fields and
           OSPrioCur, reinserts it, and overwrites OSTCBPrioTbl[orig].
           Waiting/dormant alternatives of the aggregate relocation relation
           are therefore not executions of this source branch. *)
        atomic_task_set_curPrio_current_literal_exec
          sg cur_tid cur_t orig lvs1 tt lvs_d)).

(* Preservation-side contract for the one source branch that actually calls
   OSMutex_RdyAtPrio.  It does not restrict [OSMutexPost_disinherit_sem]:the
   raw C transition remains executable exactly as written. *)
Definition OSMutexPost_disinherit_relocation_legal
  (sg : StableGlobVars) (m : MutexFields) (cur_tid : TaskID)
  (lvs1 lvs_d : UCOS2_Verify_State) : Prop :=
  forall cur_t orig,
    lvs1.(TskState).(inUsedTaskStates) cur_tid = Some cur_t ->
    m.(mfPCP) <> sg.(osPrioMutexCeilDis) ->
    cur_t.(curPrio) = m.(mfPCP) ->
    m.(mfOwnerOrigPrio) = Some orig ->
    atomic_task_set_curPrio_current_literal_exec
      sg cur_tid cur_t orig lvs1 tt lvs_d ->
    task_priority_relocation_legal sg lvs1 cur_tid orig.

(* Call-site proof obligation for the only internal priority relocation in
   Post.  This is deliberately separate from [OSMutexPost_sem], so it cannot
   erase a literal source execution merely to make preservation provable.
   It is defined before the closure lemmas below so fresh Rocq compilation
   never relies on a stale .vo or an impossible forward reference. *)
Definition OSMutexPost_relocations_legal
  (sg : StableGlobVars) (pevent : addr)
  (lvs1 : UCOS2_Verify_State) : Prop :=
  forall eid e m cur_tid lvs_d,
    pevent = event_addr sg eid ->
    lvs1.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    m.(mfOwner) = Some cur_tid ->
    lvs1.(SchedState).(curTaskID) = Some cur_tid ->
    OSMutexPost_disinherit_sem sg m cur_tid lvs1 lvs_d ->
    OSMutexPost_disinherit_relocation_legal
      sg m cur_tid lvs1 lvs_d.

(* Literal priority-ceiling reservation executed after the optional owner
   disinherit and before OS_EventTaskRdy.  Keeping this as its own state
   transition makes the second OSTCBPrioTbl read auditable against the exact
   intermediate state rather than a reconstructed final snapshot. *)
Definition OSMutexPost_reservation_sem
  (sg : StableGlobVars) (eid : EventID)
  (lvs_d lvs_reserved : UCOS2_Verify_State) : Prop :=
  exists e m owner tskSt_reserved,
    lvs_d.(EventState).(inUsedEventStates) eid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e.(mutexFields) = Some m /\
    m.(mfOwner) = Some owner /\
    tskSt_reserved =
      {| inUsedTaskStates := lvs_d.(TskState).(inUsedTaskStates);
         unUsedTaskStates := lvs_d.(TskState).(unUsedTaskStates);
         tcbListHead      := lvs_d.(TskState).(tcbListHead);
         prioTbl          := fun p =>
           if (negb (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis))
               && Z.eqb p m.(mfPCP))%bool
           then PTReserved
           else lvs_d.(TskState).(prioTbl) p;
         taskRegNextID := lvs_d.(TskState).(taskRegNextID);
         parkedTaskStacks := lvs_d.(TskState).(parkedTaskStacks);
         taskLifecycle := lvs_d.(TskState).(taskLifecycle);
     taskCount        := lvs_d.(TskState).(taskCount); |} /\
    lvs_reserved = replace_TskS tskSt_reserved lvs_d.

(* The helper itself stops at this stage: reservation has happened, but only
   OS_EventTaskRdy's TCB/ready/event-wait effects have executed.  In
   particular, the mutex count and owner pointer still denote their entry
   values. *)
Definition OSMutexPost_wake_sem
  (sg : StableGlobVars) (eid : EventID)
  (lvs_reserved : UCOS2_Verify_State) (returned_prio : Priority)
  (canonical_waiter table_owner : TaskID)
  (lvs_wake : UCOS2_Verify_State) : Prop :=
  atomic_event_task_rdy
    sg eid PendOK lvs_reserved returned_prio
    canonical_waiter table_owner lvs_wake.

Lemma OSMutexPost_literal_disinherit_preserves_task_priority_unique :
  forall sg entry cur_tid cur_t new_prio lvs_d,
    verification_slice_task_validity sg entry.(TskState) ->
    task_priority_relocation_legal sg entry cur_tid new_prio ->
    atomic_task_set_curPrio_current_literal_exec
      sg cur_tid cur_t new_prio entry tt lvs_d ->
    task_priority_unique lvs_d.(TskState).
Proof.
  intros sg entry cur_tid cur_t new_prio lvs_d
    Htask Hlegal Hexec.
  pose proof
    (Ucos2Verify.lib.mutex_rdyatprio_spec.ready_task_relocation_destination_unique_from_closure
       sg entry cur_tid new_prio Htask Hlegal)
    as Hdestination_unique.
  unfold atomic_task_set_curPrio_current_literal_exec in Hexec.
  destruct Hexec as
    (new_t & Hcur & Hcur_prio & Hget & Hlo & Hhi &
     Hnew_t & Hlvs_d).
  cbv zeta in Hlvs_d.
  subst lvs_d.
  destruct Htask as [Hrange Hderived].
  unfold verification_slice_task_in_range in Hrange.
  destruct Hrange as
    [Hids [Hfree_nodup [Hfree_range
      [Hfree_unused [Hprio [Hregistered Hentry_unique]]]]]].
  unfold task_priority_unique.
  cbn.
  intros tid1 tid2 t1 t2 Hget1 Hget2 Hprio_eq.
  destruct (Z.eqb tid1 cur_tid) eqn:Heq1;
    destruct (Z.eqb tid2 cur_tid) eqn:Heq2.
  - apply Z.eqb_eq in Heq1, Heq2. congruence.
  - apply Z.eqb_eq in Heq1. subst tid1.
    inversion Hget1; subst t1.
    rewrite Hnew_t in Hprio_eq. cbn in Hprio_eq.
    assert (tid2 = cur_tid).
    {
      eapply Hdestination_unique.
      - exact Hget2.
      - symmetry. exact Hprio_eq.
    }
    subst tid2. rewrite Z.eqb_refl in Heq2. discriminate.
  - apply Z.eqb_eq in Heq2. subst tid2.
    inversion Hget2; subst t2.
    rewrite Hnew_t in Hprio_eq. cbn in Hprio_eq.
    assert (tid1 = cur_tid).
    {
      eapply Hdestination_unique.
      - exact Hget1.
      - exact Hprio_eq.
    }
    subst tid1. rewrite Z.eqb_refl in Heq1. discriminate.
  - eapply Hentry_unique; eassumption.
Qed.

(* The equality needed to rebuild stable mutex/event/task consistency is a
   theorem of the complete Post protocol, not a premise of the shared raw
   wake relation.  In the no-relocation branches, entry task-priority
   uniqueness is unchanged.  In the literal disinherit branch, the original
   relocation classifier excludes overwriting another task's registered
   priority.  Reservation changes no task identity/priority, so the two live
   tasks observed by the wake relation at the same priority must coincide. *)
Lemma OSMutexPost_handover_identity_closure :
  forall sg pevent entry eid e m cur_tid
         lvs_d lvs_reserved lvs_wake
         returned_prio canonical_waiter table_owner,
    UCOS2_verification_slice_state_inv sg entry ->
    pevent = event_addr sg eid ->
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    m.(mfOwner) = Some cur_tid ->
    entry.(SchedState).(curTaskID) = Some cur_tid ->
    OSMutexPost_relocations_legal sg pevent entry ->
    OSMutexPost_disinherit_sem sg m cur_tid entry lvs_d ->
    OSMutexPost_reservation_sem sg eid lvs_d lvs_reserved ->
    OSMutexPost_wake_sem
      sg eid lvs_reserved returned_prio
      canonical_waiter table_owner lvs_wake ->
    table_owner = canonical_waiter.
Proof.
  intros sg pevent entry eid e m cur_tid
    lvs_d lvs_reserved lvs_wake
    returned_prio canonical_waiter table_owner
    Hvalid Hpevent Hevent Htype Hfields Howner Hcurrent
    Hrelocations Hdisinherit Hreservation Hwake.
  destruct Hvalid as [Htask [Hsched [Hevent_valid Hcross]]].
  assert (Hunique_entry : task_priority_unique entry.(TskState)).
  {
    destruct Htask as [Hrange Hderived].
    unfold verification_slice_task_in_range in Hrange.
    destruct Hrange as
      [Hids [Hfree_nodup [Hfree_range
        [Hfree_unused [Hprio [Hregistered Hunique]]]]]].
    exact Hunique.
  }
  assert (Hunique_d : task_priority_unique lvs_d.(TskState)).
  {
    unfold OSMutexPost_disinherit_sem in Hdisinherit.
    destruct Hdisinherit as [cur_t [Hcur_get Hbranch]].
    destruct Hbranch as
      [[Hdisabled Hlvs_d] |
       [[Henabled [Hnot_at_pcp Hlvs_d]] |
        [Henabled [Hat_pcp [orig [Horig Hexec]]]]]].
    - subst lvs_d. exact Hunique_entry.
    - subst lvs_d. exact Hunique_entry.
    - unfold OSMutexPost_relocations_legal in Hrelocations.
      specialize
        (Hrelocations eid e m cur_tid lvs_d
          Hpevent Hevent Htype Hfields Howner Hcurrent).
      assert (Hlocal :
        OSMutexPost_disinherit_relocation_legal
          sg m cur_tid entry lvs_d).
      {
        apply Hrelocations.
        unfold OSMutexPost_disinherit_sem.
        exists cur_t.
        split; [exact Hcur_get |].
        right. right.
        repeat split; try assumption.
        exists orig. split; assumption.
      }
      unfold OSMutexPost_disinherit_relocation_legal in Hlocal.
      specialize
        (Hlocal cur_t orig Hcur_get Henabled Hat_pcp Horig Hexec).
      eapply OSMutexPost_literal_disinherit_preserves_task_priority_unique;
        eassumption.
  }
  assert (Hunique_reserved :
    task_priority_unique lvs_reserved.(TskState)).
  {
    unfold OSMutexPost_reservation_sem in Hreservation.
    destruct Hreservation as
      (e_r & m_r & owner_r & tsk_reserved &
       Hevent_r & Htype_r & Hfields_r & Howner_r &
       Htsk_reserved & Hlvs_reserved).
    rewrite Hlvs_reserved, Htsk_reserved.
    cbn. exact Hunique_d.
  }
  unfold OSMutexPost_wake_sem, atomic_event_task_rdy,
    atomic_event_task_rdy_one in Hwake.
  destruct Hwake as
    (e1 & e2 & canonical_t & table_t & table_t' &
     He1 & Hpend & Hwait_nonempty & Hcanonical &
     Hcanonical_get & Hreturned & Htable_slot &
     Htable_get & Htable_prio & Htable_t' & He2 & Hpost).
  symmetry.
  eapply Hunique_reserved.
  - exact Hcanonical_get.
  - exact Htable_get.
  - etransitivity.
    + symmetry. exact Hreturned.
    + symmetry. exact Htable_prio.
Qed.

(* Exact checkpoint after

     OSEventCnt &= OS_MUTEX_KEEP_UPPER_8;
     OSEventCnt |= returned_prio.

   Only the saved/original-priority component changes here.  The owner pointer
   remains the old value until the following source statement. *)
Definition OSMutexPost_count_commit_sem
  (eid : EventID) (returned_prio : Priority)
  (lvs_wake lvs_cnt : UCOS2_Verify_State) : Prop :=
  exists e1 e2 m1 m2,
    lvs_wake.(EventState).(inUsedEventStates) eid = Some e1 /\
    e1.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e1.(mutexFields) = Some m1 /\
    m2 = {| mfPCP := m1.(mfPCP);
            mfOwner := m1.(mfOwner);
            mfOwnerOrigPrio := Some returned_prio; |} /\
    e2 = {| eventGeneration := e1.(eventGeneration);
            eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
            eventType   := e1.(eventType);
            mutexFields := Some m2;
            semFields   := e1.(semFields);
            mboxFields  := e1.(mboxFields);
            queueFields := e1.(queueFields);
            waitList    := e1.(waitList); |} /\
    lvs_cnt =
      replace_EventS
        (update_event_field_raw lvs_wake.(EventState) eid e2)
        lvs_wake.

(* Exact checkpoint after the second priority-table read and

     OSEventPtr = OSTCBPrioTbl[returned_prio].

   The lookup is stated in [lvs_cnt], exactly where the C read occurs.  The
   count stage and this owner commit do not modify the priority table, so the
   same [table_owner] observation is retained in [lvs_h]. *)
Definition OSMutexPost_owner_commit_sem
  (eid : EventID) (returned_prio : Priority) (table_owner : TaskID)
  (lvs_cnt lvs_h : UCOS2_Verify_State) : Prop :=
  lvs_cnt.(TskState).(prioTbl) returned_prio = PTTask table_owner /\
  exists e1 e2 m1 m2,
    lvs_cnt.(EventState).(inUsedEventStates) eid = Some e1 /\
    e1.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e1.(mutexFields) = Some m1 /\
    m2 = {| mfPCP := m1.(mfPCP);
            mfOwner := Some table_owner;
            mfOwnerOrigPrio := m1.(mfOwnerOrigPrio); |} /\
    e2 = {| eventGeneration := e1.(eventGeneration);
            eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
            eventType   := e1.(eventType);
            mutexFields := Some m2;
            semFields   := e1.(semFields);
            mboxFields  := e1.(mboxFields);
            queueFields := e1.(queueFields);
            waitList    := e1.(waitList); |} /\
    lvs_h =
      replace_EventS
        (update_event_field_raw lvs_cnt.(EventState) eid e2)
        lvs_cnt /\
    lvs_h.(TskState).(prioTbl) returned_prio = PTTask table_owner.

(* Empty-waiter source path, first write:

     OSEventCnt |= OS_MUTEX_AVAILABLE.

   Reservation has already happened before the wait-group test.  This stage
   therefore changes only the saved-owner-priority component; it must not
   reserve the PCP slot a second time or clear the owner pointer early. *)
Definition OSMutexPost_empty_count_commit_sem
  (eid : EventID) (lvs_reserved lvs_available : UCOS2_Verify_State) : Prop :=
  exists e1 e2 m1 m2 owner,
    lvs_reserved.(EventState).(inUsedEventStates) eid = Some e1 /\
    e1.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e1.(mutexFields) = Some m1 /\
    e1.(waitList) = [] /\
    m1.(mfOwner) = Some owner /\
    m2 = {| mfPCP := m1.(mfPCP);
            mfOwner := m1.(mfOwner);
            mfOwnerOrigPrio := Some 0xFF; |} /\
    e2 = {| eventGeneration := e1.(eventGeneration);
            eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
            eventType   := e1.(eventType);
            mutexFields := Some m2;
            semFields   := e1.(semFields);
            mboxFields  := e1.(mboxFields);
            queueFields := e1.(queueFields);
            waitList    := e1.(waitList); |} /\
    lvs_available =
      replace_EventS
        (update_event_field_raw lvs_reserved.(EventState) eid e2)
        lvs_reserved.

(* Empty-waiter source path, second write:

     OSEventPtr = NULL.

   The count's available marker is retained and only ownership is cleared. *)
Definition OSMutexPost_empty_owner_commit_sem
  (eid : EventID) (lvs_available lvs_r : UCOS2_Verify_State) : Prop :=
  exists e1 e2 m1 m2,
    lvs_available.(EventState).(inUsedEventStates) eid = Some e1 /\
    e1.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e1.(mutexFields) = Some m1 /\
    e1.(waitList) = [] /\
    m1.(mfOwnerOrigPrio) = Some 0xFF /\
    m2 = {| mfPCP := m1.(mfPCP);
            mfOwner := None;
            mfOwnerOrigPrio := None; |} /\
    e2 = {| eventGeneration := e1.(eventGeneration);
            eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
            eventType   := e1.(eventType);
            mutexFields := Some m2;
            semFields   := e1.(semFields);
            mboxFields  := e1.(mboxFields);
            queueFields := e1.(queueFields);
            waitList    := e1.(waitList); |} /\
    lvs_r =
      replace_EventS
        (update_event_field_raw lvs_available.(EventState) eid e2)
        lvs_available.

Definition OSMutexPost_empty_release_sem
  (sg : StableGlobVars) (eid : EventID)
  (lvs_d lvs_r : UCOS2_Verify_State) : Prop :=
  exists lvs_reserved lvs_available,
    OSMutexPost_reservation_sem sg eid lvs_d lvs_reserved /\
    OSMutexPost_empty_count_commit_sem
      eid lvs_reserved lvs_available /\
    OSMutexPost_empty_owner_commit_sem
      eid lvs_available lvs_r.

(* Source-order non-empty-waiter path.  The three identities are deliberately
   separate:

   [returned_prio]     -- event bitmap selection and function return;
   [canonical_waiter]  -- waiter removed from the event bitmap/list;
   [table_owner]       -- TCB selected by OSTCBPrioTbl[returned_prio], whose
                          task/scheduler fields are updated and which becomes
                          the mutex owner.

   The shared wake relation neither assumes nor concludes identity equality.
   Equality is a stable-entry closure fact obtained only when the caller also
   supplies Post's relocation legality.  Each source write has a distinct
   intermediate state, and the second table lookup is recorded only at its
   actual execution point. *)
Definition OSMutexPost_handover_sem
  (sg : StableGlobVars) (eid : EventID)
  (lvs_d : UCOS2_Verify_State) (returned_prio : Priority)
  (canonical_waiter table_owner : TaskID)
  (lvs_h : UCOS2_Verify_State) : Prop :=
  exists lvs_reserved lvs_wake lvs_cnt,
    OSMutexPost_reservation_sem sg eid lvs_d lvs_reserved /\
    OSMutexPost_wake_sem
      sg eid lvs_reserved returned_prio
      canonical_waiter table_owner lvs_wake /\
    OSMutexPost_count_commit_sem
      eid returned_prio lvs_wake lvs_cnt /\
    OSMutexPost_owner_commit_sem
      eid returned_prio table_owner lvs_cnt lvs_h.

Definition OSMutexPost_sem (sg : StableGlobVars) (pevent : addr)
  : program UCOS2_Verify_State OSErrCode :=
  fun lvs1 perr lvs2 =>
    (lvs1.(IntrState).(intNesting) > 0 /\ perr = OS_ERR_POST_ISR /\ lvs2 = lvs1) \/
    (lvs1.(IntrState).(intNesting) <= 0 /\ pevent = 0 /\
     perr = OS_ERR_PEVENT_NULL /\ lvs2 = lvs1) \/
    (lvs1.(IntrState).(intNesting) <= 0 /\ pevent <> 0 /\
     exists eid, pevent = event_addr sg eid /\
                  (lvs1.(EventState).(inUsedEventStates)) eid = None /\
                  perr = OS_ERR_EVENT_TYPE /\ lvs2 = lvs1) \/
    (lvs1.(IntrState).(intNesting) <= 0 /\ pevent <> 0 /\
     exists eid e, pevent = event_addr sg eid /\
                   (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
                   e.(eventType) <> OS_EVENT_TYPE_MUTEX /\
                   perr = OS_ERR_EVENT_TYPE /\ lvs2 = lvs1) \/
    (* NOT_MUTEX_OWNER:owner 不是 current *)
    (lvs1.(IntrState).(intNesting) <= 0 /\ pevent <> 0 /\
     exists eid e m cur_tid owner_tid,
       pevent = event_addr sg eid /\
       (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\
       e.(mutexFields) = Some m /\ m.(mfOwner) = Some owner_tid /\
       (lvs1.(SchedState).(curTaskID)) = Some cur_tid /\
       cur_tid <> owner_tid /\
       perr = OS_ERR_NOT_MUTEX_OWNER /\ lvs2 = lvs1) \/
    (* NOT_MUTEX_OWNER: source reaches this when the mutex is available. *)
    (lvs1.(IntrState).(intNesting) <= 0 /\ pevent <> 0 /\
     exists eid e m cur_tid cur_t,
       pevent = event_addr sg eid /\
       (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\
       e.(mutexFields) = Some m /\ m.(mfOwner) = None /\
       (lvs1.(SchedState).(curTaskID)) = Some cur_tid /\
       (lvs1.(TskState).(inUsedTaskStates)) cur_tid = Some cur_t /\
       perr = OS_ERR_NOT_MUTEX_OWNER /\ lvs2 = lvs1) \/
    (* waitList 空:atomic_mutex_release(前置 disinherit 由 sem 描述)*)
    (lvs1.(IntrState).(intNesting) <= 0 /\ pevent <> 0 /\
     exists eid e m cur_tid lvs_d lvs_r,
       pevent = event_addr sg eid /\
       (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\
       e.(mutexFields) = Some m /\ m.(mfOwner) = Some cur_tid /\
       (lvs1.(SchedState).(curTaskID)) = Some cur_tid /\
       e.(waitList) = [] /\
       OSMutexPost_disinherit_sem sg m cur_tid lvs1 lvs_d /\
       OSMutexPost_empty_release_sem sg eid lvs_d lvs_r /\
       perr = OS_ERR_NONE /\ lvs2 = lvs_r) \/
    (* waitList 非空:handover 后两个返回分支都字面调用
       OS_Sched.  The source returns PCP_LOWER when the handed-over task
       priority is not lower than the mutex ceiling priority. *)
    (lvs1.(IntrState).(intNesting) <= 0 /\ pevent <> 0 /\
      exists eid e m cur_tid lvs_d lvs_h lvs_s sched_res
             returned_prio canonical_waiter table_owner,
        pevent = event_addr sg eid /\
        (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
        e.(eventType) = OS_EVENT_TYPE_MUTEX /\
        e.(mutexFields) = Some m /\ m.(mfOwner) = Some cur_tid /\
        (lvs1.(SchedState).(curTaskID)) = Some cur_tid /\
        e.(waitList) <> [] /\
        OSMutexPost_disinherit_sem sg m cur_tid lvs1 lvs_d /\
        OSMutexPost_handover_sem
          sg eid lvs_d returned_prio
          canonical_waiter table_owner lvs_h /\
        atomic_sched lvs_h sched_res lvs_s /\
        ((m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\
          returned_prio <= m.(mfPCP) /\
          perr = OS_ERR_PCP_LOWER) \/
         ((m.(mfPCP) = sg.(osPrioMutexCeilDis) \/
           returned_prio > m.(mfPCP)) /\ perr = OS_ERR_NONE)) /\
        lvs2 = lvs_s).

Definition OSMutexPend_sem (sg : StableGlobVars) (pevent : addr) (timeout : Z)
  : program UCOS2_Verify_State OSErrCode :=
  fun lvs1 perr lvs2 =>
    (pevent = 0 /\ perr = OS_ERR_PEVENT_NULL /\ lvs2 = lvs1) \/
    (exists eid, pevent = event_addr sg eid /\
                 (lvs1.(EventState).(inUsedEventStates)) eid = None /\
                 perr = OS_ERR_EVENT_TYPE /\ lvs2 = lvs1) \/
    (exists eid e, pevent = event_addr sg eid /\
                  (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
                  e.(eventType) <> OS_EVENT_TYPE_MUTEX /\
                  perr = OS_ERR_EVENT_TYPE /\ lvs2 = lvs1) \/
    (exists eid e,
       pevent = event_addr sg eid /\
       (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\
       lvs1.(IntrState).(intNesting) > 0 /\
       perr = OS_ERR_PEND_ISR /\
       lvs2 = lvs1) \/
    (exists eid e,
       pevent = event_addr sg eid /\
       (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\
       lvs1.(IntrState).(intNesting) <= 0 /\
       lvs1.(IntrState).(lockNesting) > 0 /\
       perr = OS_ERR_PEND_LOCKED /\
       lvs2 = lvs1) \/
    (* mutex 可用:acquire *)
    (exists eid e m cur_tid op lvs_a,
       pevent = event_addr sg eid /\
       (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\
       lvs1.(IntrState).(intNesting) <= 0 /\
       lvs1.(IntrState).(lockNesting) <= 0 /\
       e.(mutexFields) = Some m /\ m.(mfOwner) = None /\
       (lvs1.(SchedState).(curTaskID)) = Some cur_tid /\
       (exists t, (lvs1.(TskState).(inUsedTaskStates)) cur_tid = Some t /\
                  op = t.(curPrio) /\
                  (task_non_suspension_bits (t.(stat))) = 0 /\
                  t.(eventPtr) = None /\
                  t.(eventMultiWaitEvents) = [] /\
                  t.(eventMultiRdy) = None) /\
       atomic_mutex_acquire eid cur_tid op lvs1 tt lvs_a /\
       ((m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\ op <= m.(mfPCP) /\ perr = OS_ERR_PCP_LOWER) \/
        ((m.(mfPCP) = sg.(osPrioMutexCeilDis) \/ op > m.(mfPCP)) /\ perr = OS_ERR_NONE)) /\
       lvs2 = lvs_a) \/
    (* mutex 不可用:inherit + wait + sched + stat switch *)
    (exists eid e m cur_tid owner_tid owner_t cur_t mprio
            lvs_i lvs_w lvs_s resume,
       pevent = event_addr sg eid /\
       (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\
       lvs1.(IntrState).(intNesting) <= 0 /\
       lvs1.(IntrState).(lockNesting) <= 0 /\
       e.(mutexFields) = Some m /\ m.(mfOwner) = Some owner_tid /\
       (lvs1.(SchedState).(curTaskID)) = Some cur_tid /\
       mutex_pend_nonrecursive_prop e cur_tid /\
       (lvs1.(TskState).(inUsedTaskStates)) owner_tid = Some owner_t /\
       (lvs1.(TskState).(inUsedTaskStates)) cur_tid = Some cur_t /\
       (task_non_suspension_bits (cur_t.(stat))) = 0 /\
       cur_t.(eventPtr) = None /\
       cur_t.(eventMultiWaitEvents) = [] /\
       cur_t.(eventMultiRdy) = None /\
       m.(mfOwnerOrigPrio) = Some mprio /\
       owner_t.(eventMultiWaitEvents) = [] /\
       owner_t.(eventMultiRdy) = None /\
       (((task_non_suspension_bits (owner_t.(stat))) = 0 /\
         owner_t.(eventPtr) = None /\
         is_effectively_ready owner_t.(stat) owner_t.(dly) = true /\
         In owner_tid lvs1.(SchedState).(readyList)) \/
        (exists owner_wait_eid owner_wait_e pty,
          (task_non_suspension_bits (owner_t.(stat))) = task_pend_mask pty /\
          owner_t.(eventPtr) = Some owner_wait_eid /\
          owner_wait_eid <> eid /\
          lvs1.(EventState).(inUsedEventStates) owner_wait_eid = Some owner_wait_e /\
          event_type_to_pend_type owner_wait_e.(eventType) = Some pty /\
          In owner_tid owner_wait_e.(waitList) /\
          ~ In owner_tid lvs1.(SchedState).(readyList) /\
          is_effectively_ready owner_t.(stat) owner_t.(dly) = false) \/
        (owner_t.(eventPtr) = None /\
         ~ In owner_tid lvs1.(SchedState).(readyList) /\
         is_effectively_ready owner_t.(stat) owner_t.(dly) = false)) /\
       (* Inheritance relocates either the ready list or the single event
          wait list selected by the owner-location disjunction above. *)
       (((m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\
          owner_t.(curPrio) > m.(mfPCP) /\
          mprio > cur_t.(curPrio)) /\
         atomic_mutex_inherit sg eid lvs1 tt lvs_i) \/
        ((m.(mfPCP) = sg.(osPrioMutexCeilDis) \/
          owner_t.(curPrio) <= m.(mfPCP) \/
          mprio <= cur_t.(curPrio)) /\
         lvs_i = lvs1)) /\
       atomic_event_task_wait_mutex sg eid timeout lvs_i tt lvs_w /\
       atomic_mutex_pend_sched_resume sg eid cur_tid lvs_w resume lvs_s /\
       match resume with
       | MutexPendResumeOK =>
           exists lvs_c,
             atomic_task_pend_cleanup cur_tid lvs_s tt lvs_c /\
             lvs2 = lvs_c /\
             perr = OS_ERR_NONE
       | MutexPendResumeAbort =>
           exists lvs_c,
             atomic_task_pend_cleanup cur_tid lvs_s tt lvs_c /\
             lvs2 = lvs_c /\
             perr = OS_ERR_PEND_ABORT
       | MutexPendResumeTimeout =>
           exists lvs_rm lvs_c,
             atomic_event_task_remove cur_tid eid lvs_s tt lvs_rm /\
             atomic_task_pend_cleanup cur_tid lvs_rm tt lvs_c /\
             lvs2 = lvs_c /\
             perr = OS_ERR_TIMEOUT
       end).

(* Pend's raw semantics is retained, but its whole-function preservation
   theorem is deferred until the inherit and resume-restore call sites carry
   their source-backed relocation protocol.  In particular, no unconditional
   full-invariant theorem is exported from the generic priority transformer. *)
