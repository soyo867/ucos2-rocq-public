Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_full_spec.
Import ListNotations.
Local Open Scope Z_scope.

(** A mathematical non-vacuity witness, NOT the addresses of a linked
    firmware image. The actual linker/ABI and physical initial heap remain
    separate obligations. Each enabled object fits in its own 4 KiB slot. *)
Definition kernel_boot_full_example_globals : StableGlobVars :=
  {| osMaxEvents := 10; osMaxQs := 4; osMaxTasks := 20; osNSysTasks := 2;
     osLowestPrio := 63; osTaskIdlePrio := 63; osTaskStatPrio := 62;
     osPrioMutexCeilDis := 255; osPrioSelf := 255;
     osRdyTblSize := 8; osEventTblSize := 8;
     g_OSEventTbl := 4096; g_OSQTbl := 8192; g_OSTCBTbl := 12288;
     g_OSTCBPrioTbl := 16384; g_OSUnMapTbl := 20480;
     g_OSRdyGrp := 24576; g_OSRdyTbl := 28672;
     g_OSPrioCur := 32768; g_OSPrioHighRdy := 36864;
     g_OSTCBCur := 40960; g_OSTCBHighRdy := 45056;
     g_OSCtxSwCtr := 49152; g_OSRunning := 53248;
     g_OSIntNesting := 57344; g_OSLockNesting := 61440;
     g_OSTaskCtr := 65536; g_OSEventFreeList := 69632;
     g_OSQFreeList := 73728; g_OSTCBFreeList := 77824; g_OSTCBList := 81920;
     g_OSTime := 86016; g_OSTickStepState := 90112;
     g_OSFlagTbl := 94208; g_OSFlagFreeList := 98304;
     g_OSMemTbl := 102400; g_OSMemFreeList := 106496;
     g_OSTmrTbl := 110592; g_OSTmrWheelTbl := 114688;
     g_OSTmrFreeList := 118784; g_OSTmrFree := 122880; g_OSTmrUsed := 126976;
     g_OSTmrTime := 131072; g_OSTmrSem := 135168; g_OSTmrSemSignal := 139264;
     g_OSIdleCtr := 143360; g_OSIdleCtrMax := 147456; g_OSIdleCtrRun := 151552;
     g_OSCPUUsage := 155648; g_OSStatRdy := 159744;
     g_OSTaskRegNextAvailID := 163840;
     g_OSTaskIdleStk := 167936; g_OSTaskStatStk := 172032;
     g_OSTmrTaskStk := 176128; g_OSSafetyCriticalStartFlag := 180224;
     osKernelConfig := full_features_kernel_configuration |}.

Local Fixpoint kernel_boot_regions_ordered (regions : list (Z * Z)) : Prop :=
  match regions with
  | [] => True
  | first :: rest =>
      Forall (fun next => fst first + snd first <= fst next) rest /\
      kernel_boot_regions_ordered rest
  end.

Local Definition kernel_boot_regions_validb (regions : list (Z * Z)) : bool :=
  forallb (fun region =>
    (0 <? fst region) && (0 <=? snd region) &&
    (fst region + snd region <=? 4294967296)) regions.

Local Fixpoint kernel_boot_regions_orderedb (regions : list (Z * Z)) : bool :=
  match regions with
  | [] => true
  | first :: rest =>
      forallb (fun next => fst first + snd first <=? fst next) rest &&
      kernel_boot_regions_orderedb rest
  end.

Local Lemma kernel_boot_regions_validb_sound : forall regions,
  kernel_boot_regions_validb regions = true -> Forall kernel_region_valid regions.
Proof.
  intros regions Hvalid; apply Forall_forall; intros region Hin.
  unfold kernel_boot_regions_validb in Hvalid; rewrite forallb_forall in Hvalid.
  specialize (Hvalid region Hin).
  apply andb_true_iff in Hvalid as [Hfirst Hlast].
  apply andb_true_iff in Hfirst as [Hbase Hsize].
  apply Z.ltb_lt in Hbase; apply Z.leb_le in Hsize; apply Z.leb_le in Hlast.
  unfold kernel_region_valid; tauto.
Qed.


Local Lemma kernel_boot_regions_orderedb_sound : forall regions,
  kernel_boot_regions_orderedb regions = true -> kernel_boot_regions_ordered regions.
Proof.
  induction regions as [|head rest IH]; cbn; intro Hordered; [exact I|].
  apply andb_true_iff in Hordered as [Hhead Hrest]; split; [|apply IH; exact Hrest].
  apply Forall_forall; intros next Hin.
  rewrite forallb_forall in Hhead; apply Z.leb_le; apply Hhead; exact Hin.
Qed.

Local Lemma kernel_boot_ordered_regions_disjoint : forall regions,
  kernel_boot_regions_ordered regions ->
  forall i j first second,
    nth_error regions i = Some first -> nth_error regions j = Some second ->
    i <> j -> kernel_regions_disjoint first second.
Proof.
  induction regions as [|head rest IH]; intros Hordered i j first second Hi Hj Hneq.
  - destruct i; discriminate.
  - destruct Hordered as [Hhead Hrest].
    destruct i as [|i], j as [|j]; cbn in Hi, Hj.
    + contradiction.
    + inversion Hi; subst first. left.
      rewrite Forall_forall in Hhead; apply Hhead.
      eapply nth_error_In; exact Hj.
    + inversion Hj; subst second. right.
      rewrite Forall_forall in Hhead; apply Hhead.
      eapply nth_error_In; exact Hi.
    + eapply IH; [exact Hrest|exact Hi|exact Hj|congruence].
Qed.

Lemma kernel_boot_full_example_profile :
  full_features_kernel_profile kernel_boot_full_example_globals.
Proof.
  unfold full_features_kernel_profile.
  split.
  - unfold valid_stable_glob_vars, valid_stable_global_addresses,
      stable_global_addresses, kernel_boot_full_example_globals.
    cbn; repeat split; try lia.
    + repeat constructor; lia.
    + repeat constructor; simpl; intuition congruence.
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply full_features_kernel_configuration_valid|].
    split; [apply full_features_kernel_configuration_task_layout|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [intros; cbn; lia|].
    unfold valid_full_features_kernel_global_layout, kernel_region_layout_valid.
    split.
    + apply kernel_boot_regions_validb_sound; vm_compute; reflexivity.
    + apply kernel_boot_ordered_regions_disjoint.
      apply kernel_boot_regions_orderedb_sound; vm_compute; reflexivity.
Qed.

Lemma kernel_boot_full_state_inhabited :
  exists sg state, full_features_kernel_profile sg /\ UCOS2_full_state_inv sg state.
Proof.
  exists kernel_boot_full_example_globals,
    (kernel_full_boot_state kernel_boot_full_example_globals 184320 184320 184320
      184320 (name_question_mark_resources 184320)).
  split; [apply kernel_boot_full_example_profile|].
  apply kernel_full_boot_state_valid.
  - apply kernel_boot_full_example_profile.
  - apply name_question_mark_resources_valid.
  - intros _ _; exists [63].
    unfold readable_name; split; [repeat constructor; lia|]. split.
    + intros [|i] c Hlookup; cbn in Hlookup.
      * inversion Hlookup; subst c; reflexivity.
      * destruct i; discriminate.
    + reflexivity.
Qed.
