Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From Ucos2Verify.VC.code.mutex Require Import pend_full_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_func_sem.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Local Open Scope sac.

Lemma proof_of_OSMutexPend_full_safety_wit_22 : OSMutexPend_full_safety_wit_22.
Proof.
  pre_process.
  prop_apply_p (store_ushort_range
    (&((pe) # "os_event" ->ₛ "OSEventCnt")) ecnt_in).
  Intros.
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_23 : OSMutexPend_full_safety_wit_23.
Proof.
  pre_process.
  prop_apply_p (store_ushort_range
    (&((pe) # "os_event" ->ₛ "OSEventCnt")) ecnt_in).
  Intros.
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_24 : OSMutexPend_full_safety_wit_24.
Proof.
  pre_process.
  prop_apply_p (store_ushort_range
    (&((pe) # "os_event" ->ₛ "OSEventCnt")) ecnt_in).
  Intros.
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_25 : OSMutexPend_full_safety_wit_25.
Proof.
  pre_process.
  prop_apply_p (store_ushort_range
    (&((pe) # "os_event" ->ₛ "OSEventCnt")) ecnt_in).
  Intros.
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_26 : OSMutexPend_full_safety_wit_26.
Proof.
  pre_process.
  prop_apply_p (store_ushort_range
    (&((pe) # "os_event" ->ₛ "OSEventCnt")) ecnt_in).
  Intros.
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_27 : OSMutexPend_full_safety_wit_27.
Proof.
  pre_process.
  prop_apply_p (store_ushort_range
    (&((pe) # "os_event" ->ₛ "OSEventCnt")) ecnt_in).
  Intros.
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_37 : OSMutexPend_full_safety_wit_37.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_38 : OSMutexPend_full_safety_wit_38.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_39 : OSMutexPend_full_safety_wit_39.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_40 : OSMutexPend_full_safety_wit_40.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_41 : OSMutexPend_full_safety_wit_41.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_42 : OSMutexPend_full_safety_wit_42.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_43 : OSMutexPend_full_safety_wit_43.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_44 : OSMutexPend_full_safety_wit_44.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_45 : OSMutexPend_full_safety_wit_45.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_46 : OSMutexPend_full_safety_wit_46.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_47 : OSMutexPend_full_safety_wit_47.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_48 : OSMutexPend_full_safety_wit_48.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_49 : OSMutexPend_full_safety_wit_49.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_50 : OSMutexPend_full_safety_wit_50.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_51 : OSMutexPend_full_safety_wit_51.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_52 : OSMutexPend_full_safety_wit_52.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_53 : OSMutexPend_full_safety_wit_53.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_54 : OSMutexPend_full_safety_wit_54.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_55 : OSMutexPend_full_safety_wit_55.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_56 : OSMutexPend_full_safety_wit_56.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_57 : OSMutexPend_full_safety_wit_57.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_58 : OSMutexPend_full_safety_wit_58.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_59 : OSMutexPend_full_safety_wit_59.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_60 : OSMutexPend_full_safety_wit_60.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_61 : OSMutexPend_full_safety_wit_61.
Proof.
  pre_process;
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hrange;
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_62 : OSMutexPend_full_safety_wit_62.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_63 : OSMutexPend_full_safety_wit_63.
Proof.
  pre_process.
  split_pures.
  - dump_pre_spatial.
    pose proof
      (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
      as Hinner.
    assert
      (Hshift :
         0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32).
    {
      split.
      - apply Z.shiftr_nonneg; lia.
      - rewrite Z.shiftr_div_pow2 by lia.
        apply Z.div_lt_upper_bound; lia.
    }
    rewrite unsigned_last_nbits_eq by lia.
    lia.
  - dump_pre_spatial.
    pose proof
      (unsigned_Lastnbits_range
         (Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
         8 ltac:(lia))
      as Houter.
    lia.
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_64 : OSMutexPend_full_safety_wit_64.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_65 : OSMutexPend_full_safety_wit_65.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_66 : OSMutexPend_full_safety_wit_66.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_67 : OSMutexPend_full_safety_wit_67.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_68 : OSMutexPend_full_safety_wit_68.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_69 : OSMutexPend_full_safety_wit_69.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_70 : OSMutexPend_full_safety_wit_70.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_71 : OSMutexPend_full_safety_wit_71.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_72 : OSMutexPend_full_safety_wit_72.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_73 : OSMutexPend_full_safety_wit_73.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_74 : OSMutexPend_full_safety_wit_74.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_75 : OSMutexPend_full_safety_wit_75.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_76 : OSMutexPend_full_safety_wit_76.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_77 : OSMutexPend_full_safety_wit_77.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_78 : OSMutexPend_full_safety_wit_78.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_79 : OSMutexPend_full_safety_wit_79.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_80 : OSMutexPend_full_safety_wit_80.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_81 : OSMutexPend_full_safety_wit_81.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_82 : OSMutexPend_full_safety_wit_82.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_83 : OSMutexPend_full_safety_wit_83.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_84 : OSMutexPend_full_safety_wit_84.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_85 : OSMutexPend_full_safety_wit_85.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_86 : OSMutexPend_full_safety_wit_86.
Proof.
  pre_process;
  try (
    split_pures;
    [ dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia))
        as Hinner;
      assert
        (Hshift :
           0 <=
           Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 32)
        by
          (split;
           [ apply Z.shiftr_nonneg; lia
           | rewrite Z.shiftr_div_pow2 by lia;
             apply Z.div_lt_upper_bound; lia ]);
      rewrite unsigned_last_nbits_eq by lia;
      lia
    | dump_pre_spatial;
      pose proof
        (unsigned_Lastnbits_range
           (Z.shiftr
              (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3)
           8 ltac:(lia))
        as Houter;
      lia ]).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_87 : OSMutexPend_full_safety_wit_87.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_88 : OSMutexPend_full_safety_wit_88.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_89 : OSMutexPend_full_safety_wit_89.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_90 : OSMutexPend_full_safety_wit_90.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_91 : OSMutexPend_full_safety_wit_91.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_92 : OSMutexPend_full_safety_wit_92.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_93 : OSMutexPend_full_safety_wit_93.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_94 : OSMutexPend_full_safety_wit_94.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_95 : OSMutexPend_full_safety_wit_95.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_96 : OSMutexPend_full_safety_wit_96.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_97 : OSMutexPend_full_safety_wit_97.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_98 : OSMutexPend_full_safety_wit_98.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_99 : OSMutexPend_full_safety_wit_99.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_100 : OSMutexPend_full_safety_wit_100.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_101 : OSMutexPend_full_safety_wit_101.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_102 : OSMutexPend_full_safety_wit_102.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_103 : OSMutexPend_full_safety_wit_103.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_104 : OSMutexPend_full_safety_wit_104.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_105 : OSMutexPend_full_safety_wit_105.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_106 : OSMutexPend_full_safety_wit_106.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_107 : OSMutexPend_full_safety_wit_107.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_108 : OSMutexPend_full_safety_wit_108.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_109 : OSMutexPend_full_safety_wit_109.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_110 : OSMutexPend_full_safety_wit_110.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_safety_wit_111 : OSMutexPend_full_safety_wit_111.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg;
      right;
      lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr ecnt_in 8) 8 ltac:(lia));
      change (Z.shiftr ecnt_in 8 mod 8 <= 63);
      lia
    ]
  ).
Qed.

Lemma proof_of_OSMutexPend_full_entail_wit_1_1 : OSMutexPend_full_entail_wit_1_1.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_2 : OSMutexPend_full_entail_wit_1_2.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_3 : OSMutexPend_full_entail_wit_1_3.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_4 : OSMutexPend_full_entail_wit_1_4.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_5 : OSMutexPend_full_entail_wit_1_5.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_6 : OSMutexPend_full_entail_wit_1_6.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_7 : OSMutexPend_full_entail_wit_1_7.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_8 : OSMutexPend_full_entail_wit_1_8.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_9 : OSMutexPend_full_entail_wit_1_9.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_10 : OSMutexPend_full_entail_wit_1_10.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_11 : OSMutexPend_full_entail_wit_1_11.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_12 : OSMutexPend_full_entail_wit_1_12.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_13 : OSMutexPend_full_entail_wit_1_13.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_14 : OSMutexPend_full_entail_wit_1_14.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_15 : OSMutexPend_full_entail_wit_1_15.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_16 : OSMutexPend_full_entail_wit_1_16.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_17 : OSMutexPend_full_entail_wit_1_17.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_18 : OSMutexPend_full_entail_wit_1_18.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_19 : OSMutexPend_full_entail_wit_1_19.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_20 : OSMutexPend_full_entail_wit_1_20.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_21 : OSMutexPend_full_entail_wit_1_21.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_22 : OSMutexPend_full_entail_wit_1_22.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_23 : OSMutexPend_full_entail_wit_1_23.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_24 : OSMutexPend_full_entail_wit_1_24.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_25 : OSMutexPend_full_entail_wit_1_25.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_26 : OSMutexPend_full_entail_wit_1_26.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_27 : OSMutexPend_full_entail_wit_1_27.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_28 : OSMutexPend_full_entail_wit_1_28.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_29 : OSMutexPend_full_entail_wit_1_29.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_30 : OSMutexPend_full_entail_wit_1_30.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_31 : OSMutexPend_full_entail_wit_1_31.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_32 : OSMutexPend_full_entail_wit_1_32.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_33 : OSMutexPend_full_entail_wit_1_33.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_34 : OSMutexPend_full_entail_wit_1_34.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_35 : OSMutexPend_full_entail_wit_1_35.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_36 : OSMutexPend_full_entail_wit_1_36.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_37 : OSMutexPend_full_entail_wit_1_37.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_38 : OSMutexPend_full_entail_wit_1_38.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_39 : OSMutexPend_full_entail_wit_1_39.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_40 : OSMutexPend_full_entail_wit_1_40.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_41 : OSMutexPend_full_entail_wit_1_41.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_42 : OSMutexPend_full_entail_wit_1_42.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_1_43 : OSMutexPend_full_entail_wit_1_43.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_2 : OSMutexPend_full_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_1 : OSMutexPend_full_entail_wit_7_1.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_2 : OSMutexPend_full_entail_wit_7_2.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_3 : OSMutexPend_full_entail_wit_7_3.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_4 : OSMutexPend_full_entail_wit_7_4.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_5 : OSMutexPend_full_entail_wit_7_5.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_6 : OSMutexPend_full_entail_wit_7_6.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_7 : OSMutexPend_full_entail_wit_7_7.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_8 : OSMutexPend_full_entail_wit_7_8.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_9 : OSMutexPend_full_entail_wit_7_9.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_10 : OSMutexPend_full_entail_wit_7_10.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_11 : OSMutexPend_full_entail_wit_7_11.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_12 : OSMutexPend_full_entail_wit_7_12.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_13 : OSMutexPend_full_entail_wit_7_13.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_14 : OSMutexPend_full_entail_wit_7_14.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_15 : OSMutexPend_full_entail_wit_7_15.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_16 : OSMutexPend_full_entail_wit_7_16.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_17 : OSMutexPend_full_entail_wit_7_17.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_18 : OSMutexPend_full_entail_wit_7_18.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_19 : OSMutexPend_full_entail_wit_7_19.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_20 : OSMutexPend_full_entail_wit_7_20.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_21 : OSMutexPend_full_entail_wit_7_21.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_22 : OSMutexPend_full_entail_wit_7_22.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_23 : OSMutexPend_full_entail_wit_7_23.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_24 : OSMutexPend_full_entail_wit_7_24.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_25 : OSMutexPend_full_entail_wit_7_25.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_26 : OSMutexPend_full_entail_wit_7_26.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_27 : OSMutexPend_full_entail_wit_7_27.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_28 : OSMutexPend_full_entail_wit_7_28.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_29 : OSMutexPend_full_entail_wit_7_29.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_30 : OSMutexPend_full_entail_wit_7_30.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_31 : OSMutexPend_full_entail_wit_7_31.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_32 : OSMutexPend_full_entail_wit_7_32.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_33 : OSMutexPend_full_entail_wit_7_33.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_34 : OSMutexPend_full_entail_wit_7_34.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_35 : OSMutexPend_full_entail_wit_7_35.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_36 : OSMutexPend_full_entail_wit_7_36.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_37 : OSMutexPend_full_entail_wit_7_37.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_38 : OSMutexPend_full_entail_wit_7_38.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_entail_wit_7_39 : OSMutexPend_full_entail_wit_7_39.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_return_wit_1 : OSMutexPend_full_return_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_return_wit_2 : OSMutexPend_full_return_wit_2.
Proof. pre_process. Qed.

Lemma proof_of_OSMutexPend_full_return_wit_3 : OSMutexPend_full_return_wit_3.
Proof. pre_process. Qed.

Lemma proof_of_OSMutexPend_full_return_wit_4 : OSMutexPend_full_return_wit_4.
Proof. pre_process. Qed.

Lemma proof_of_OSMutexPend_full_return_wit_5 : OSMutexPend_full_return_wit_5.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state, store_uchar.
  pre_process.
  unfold crit_rel_no_os_state_change, crit_rel_task_event_sched in *.
  simpl in *.
  match goal with
  | Hsame : ls1 = ls0,
    Hstep : ls2 = _,
    Hvalue : lock = lockNesting (IntrState ls0),
    Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [lockNesting (IntrState ls2)] =>
          pose proof (f_equal IntrState Hstep) as Hintr;
          simpl in Hintr;
          rewrite Hsame in Hintr;
          destruct Hrange as [_ [Hlock_nonneg Hlock_upper]];
          assert (Hlock_cast : unsigned_last_nbits lock 32 = lock);
          [ apply unsigned_last_nbits_eq;
            rewrite Hvalue, <- Hintr;
            split;
            [ apply Z.ge_le; exact Hlock_nonneg
            | change (lockNesting (IntrState ls2) <= 255) in Hlock_upper;
              change (lockNesting (IntrState ls2) < 4294967296);
              lia ]
          | lia ]
      end
  end.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_6 : OSMutexPend_full_return_wit_6.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state, store_uchar.
  pre_process.
  unfold crit_rel_no_os_state_change, crit_rel_task_event_sched in *.
  simpl in *.
  match goal with
  | Hsame : ls1 = ls0,
    Hstep : ls2 = _,
    Hvalue : isr = intNesting (IntrState ls0),
    Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [intNesting (IntrState ls2)] =>
          pose proof (f_equal IntrState Hstep) as Hintr;
          simpl in Hintr;
          rewrite Hsame in Hintr;
          destruct Hrange as [_ [Hisr_nonneg Hisr_upper]];
          assert (Hisr_cast : unsigned_last_nbits isr 32 = isr);
          [ apply unsigned_last_nbits_eq;
            rewrite Hvalue, <- Hintr;
            split;
            [ apply Z.ge_le; exact Hisr_nonneg
            | change (intNesting (IntrState ls2) <= 255) in Hisr_upper;
              change (intNesting (IntrState ls2) < 4294967296);
              lia ]
          | lia ]
      end
  end.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_7 : OSMutexPend_full_return_wit_7.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_return_wit_8 : OSMutexPend_full_return_wit_8.
Proof. pre_process. Qed.

Lemma proof_of_OSMutexPend_full_return_wit_9 : OSMutexPend_full_return_wit_9.
Proof. pre_process. Qed.

Lemma proof_of_OSMutexPend_full_return_wit_10 : OSMutexPend_full_return_wit_10.
Proof. pre_process. Qed.

Lemma proof_of_OSMutexPend_full_return_wit_11 : OSMutexPend_full_return_wit_11.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state, store_uchar.
  pre_process.
  unfold crit_rel_no_os_state_change, crit_rel_task_event_sched in *.
  simpl in *.
  match goal with
  | Hsame : ls1 = ls0,
    Hstep : ls2 = _,
    Hvalue : lock = lockNesting (IntrState ls0),
    Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [lockNesting (IntrState ls2)] =>
          pose proof (f_equal IntrState Hstep) as Hintr;
          simpl in Hintr;
          rewrite Hsame in Hintr;
          destruct Hrange as [_ [Hlock_nonneg Hlock_upper]];
          assert (Hlock_cast : unsigned_last_nbits lock 32 = lock);
          [ apply unsigned_last_nbits_eq;
            rewrite Hvalue, <- Hintr;
            split;
            [ apply Z.ge_le; exact Hlock_nonneg
            | change (lockNesting (IntrState ls2) <= 255) in Hlock_upper;
              change (lockNesting (IntrState ls2) < 4294967296);
              lia ]
          | lia ]
      end
  end.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_12 : OSMutexPend_full_return_wit_12.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state, store_uchar.
  pre_process.
  unfold crit_rel_no_os_state_change, crit_rel_task_event_sched in *.
  simpl in *.
  match goal with
  | Hsame : ls1 = ls0,
    Hstep : ls2 = _,
    Hvalue : isr = intNesting (IntrState ls0),
    Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [intNesting (IntrState ls2)] =>
          pose proof (f_equal IntrState Hstep) as Hintr;
          simpl in Hintr;
          rewrite Hsame in Hintr;
          destruct Hrange as [_ [Hisr_nonneg Hisr_upper]];
          assert (Hisr_cast : unsigned_last_nbits isr 32 = isr);
          [ apply unsigned_last_nbits_eq;
            rewrite Hvalue, <- Hintr;
            split;
            [ apply Z.ge_le; exact Hisr_nonneg
            | change (intNesting (IntrState ls2) <= 255) in Hisr_upper;
              change (intNesting (IntrState ls2) < 4294967296);
              lia ]
          | lia ]
      end
  end.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_13 : OSMutexPend_full_return_wit_13.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_return_wit_14 : OSMutexPend_full_return_wit_14.
Proof. pre_process. Qed.

Lemma proof_of_OSMutexPend_full_return_wit_15 : OSMutexPend_full_return_wit_15.
Proof. pre_process. Qed.

Lemma proof_of_OSMutexPend_full_return_wit_16 : OSMutexPend_full_return_wit_16.
Proof. pre_process. Qed.

Lemma proof_of_OSMutexPend_full_return_wit_17 : OSMutexPend_full_return_wit_17.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state, store_uchar.
  pre_process.
  unfold crit_rel_no_os_state_change, crit_rel_task_event_sched in *.
  simpl in *.
  match goal with
  | Hsame : ls1 = ls0,
    Hstep : ls2 = _,
    Hvalue : lock = lockNesting (IntrState ls0),
    Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [lockNesting (IntrState ls2)] =>
          pose proof (f_equal IntrState Hstep) as Hintr;
          simpl in Hintr;
          rewrite Hsame in Hintr;
          destruct Hrange as [_ [Hlock_nonneg Hlock_upper]];
          assert (Hlock_cast : unsigned_last_nbits lock 32 = lock);
          [ apply unsigned_last_nbits_eq;
            rewrite Hvalue, <- Hintr;
            split;
            [ apply Z.ge_le; exact Hlock_nonneg
            | change (lockNesting (IntrState ls2) <= 255) in Hlock_upper;
              change (lockNesting (IntrState ls2) < 4294967296);
              lia ]
          | lia ]
      end
  end.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_18 : OSMutexPend_full_return_wit_18.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state, store_uchar.
  pre_process.
  unfold crit_rel_no_os_state_change, crit_rel_task_event_sched in *.
  simpl in *.
  match goal with
  | Hsame : ls1 = ls0,
    Hstep : ls2 = _,
    Hvalue : isr = intNesting (IntrState ls0),
    Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [intNesting (IntrState ls2)] =>
          pose proof (f_equal IntrState Hstep) as Hintr;
          simpl in Hintr;
          rewrite Hsame in Hintr;
          destruct Hrange as [_ [Hisr_nonneg Hisr_upper]];
          assert (Hisr_cast : unsigned_last_nbits isr 32 = isr);
          [ apply unsigned_last_nbits_eq;
            rewrite Hvalue, <- Hintr;
            split;
            [ apply Z.ge_le; exact Hisr_nonneg
            | change (intNesting (IntrState ls2) <= 255) in Hisr_upper;
              change (intNesting (IntrState ls2) < 4294967296);
              lia ]
          | lia ]
      end
  end.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_19 : OSMutexPend_full_return_wit_19.
Proof.
  pre_process.
  unfold store_uchar.
  pre_process.
  match goal with
  | Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [lock] => destruct Hrange as [_ [Hlock_nonneg Hlock_upper]]
      end
  end.
  assert (Hlock_cast : unsigned_last_nbits lock 32 = lock).
  {
    apply unsigned_last_nbits_eq.
    split.
    - apply Z.ge_le. exact Hlock_nonneg.
    - change (lock <= 255) in Hlock_upper.
      change (lock < 4294967296).
      lia.
  }
  lia.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_20 : OSMutexPend_full_return_wit_20.
Proof.
  pre_process.
  unfold store_uchar.
  pre_process.
  match goal with
  | Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [lock] => destruct Hrange as [_ [Hlock_nonneg Hlock_upper]]
      end
  end.
  assert (Hlock_cast : unsigned_last_nbits lock 32 = lock).
  {
    apply unsigned_last_nbits_eq.
    split.
    - apply Z.ge_le. exact Hlock_nonneg.
    - change (lock <= 255) in Hlock_upper.
      change (lock < 4294967296).
      lia.
  }
  lia.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_21 : OSMutexPend_full_return_wit_21.
Proof.
  pre_process.
  unfold store_uchar.
  pre_process.
  match goal with
  | Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [lock] => destruct Hrange as [_ [Hlock_nonneg Hlock_upper]]
      end
  end.
  assert (Hlock_cast : unsigned_last_nbits lock 32 = lock).
  {
    apply unsigned_last_nbits_eq.
    split.
    - apply Z.ge_le. exact Hlock_nonneg.
    - change (lock <= 255) in Hlock_upper.
      change (lock < 4294967296).
      lia.
  }
  lia.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_22 : OSMutexPend_full_return_wit_22.
Proof.
  pre_process.
  unfold store_uchar.
  pre_process.
  match goal with
  | Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [lock] => destruct Hrange as [_ [Hlock_nonneg Hlock_upper]]
      end
  end.
  assert (Hlock_cast : unsigned_last_nbits lock 32 = lock).
  {
    apply unsigned_last_nbits_eq.
    split.
    - apply Z.ge_le. exact Hlock_nonneg.
    - change (lock <= 255) in Hlock_upper.
      change (lock < 4294967296).
      lia.
  }
  lia.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_23 : OSMutexPend_full_return_wit_23.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_return_wit_24 : OSMutexPend_full_return_wit_24.
Proof.
  pre_process.
  unfold store_uchar.
  pre_process.
  match goal with
  | Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [isr] => destruct Hrange as [_ [Hisr_nonneg Hisr_upper]]
      end
  end.
  assert (Hisr_cast : unsigned_last_nbits isr 32 = isr).
  {
    apply unsigned_last_nbits_eq.
    split.
    - apply Z.ge_le. exact Hisr_nonneg.
    - change (isr <= 255) in Hisr_upper.
      change (isr < 4294967296).
      lia.
  }
  lia.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_25 : OSMutexPend_full_return_wit_25.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_return_wit_26 : OSMutexPend_full_return_wit_26.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_return_wit_27 : OSMutexPend_full_return_wit_27.
Proof.
  pre_process.
  unfold store_uchar.
  pre_process.
  match goal with
  | Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [isr] => destruct Hrange as [_ [Hisr_nonneg Hisr_upper]]
      end
  end.
  assert (Hisr_cast : unsigned_last_nbits isr 32 = isr).
  {
    apply unsigned_last_nbits_eq.
    split.
    - apply Z.ge_le. exact Hisr_nonneg.
    - change (isr <= 255) in Hisr_upper.
      change (isr < 4294967296).
      lia.
  }
  lia.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_28 : OSMutexPend_full_return_wit_28.
Proof.
  pre_process.
  unfold store_uchar.
  pre_process.
  match goal with
  | Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [isr] => destruct Hrange as [_ [Hisr_nonneg Hisr_upper]]
      end
  end.
  assert (Hisr_cast : unsigned_last_nbits isr 32 = isr).
  {
    apply unsigned_last_nbits_eq.
    split.
    - apply Z.ge_le. exact Hisr_nonneg.
    - change (isr <= 255) in Hisr_upper.
      change (isr < 4294967296).
      lia.
  }
  lia.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_29 : OSMutexPend_full_return_wit_29.
Proof.
  pre_process.
  unfold store_uchar.
  pre_process.
  match goal with
  | Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [isr] => destruct Hrange as [_ [Hisr_nonneg Hisr_upper]]
      end
  end.
  assert (Hisr_cast : unsigned_last_nbits isr 32 = isr).
  {
    apply unsigned_last_nbits_eq.
    split.
    - apply Z.ge_le. exact Hisr_nonneg.
    - change (isr <= 255) in Hisr_upper.
      change (isr < 4294967296).
      lia.
  }
  lia.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_30 : OSMutexPend_full_return_wit_30.
Proof.
  pre_process.
  unfold store_uchar.
  pre_process.
  match goal with
  | Hrange : isvalidptr_char _ /\ ?P /\ ?Q |- _ =>
      lazymatch P with
      | context [isr] => destruct Hrange as [_ [Hisr_nonneg Hisr_upper]]
      end
  end.
  assert (Hisr_cast : unsigned_last_nbits isr 32 = isr).
  {
    apply unsigned_last_nbits_eq.
    split.
    - apply Z.ge_le. exact Hisr_nonneg.
    - change (isr <= 255) in Hisr_upper.
      change (isr < 4294967296).
      lia.
  }
  lia.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_31 : OSMutexPend_full_return_wit_31.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_return_wit_32 : OSMutexPend_full_return_wit_32.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_return_wit_33 : OSMutexPend_full_return_wit_33.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_return_wit_34 : OSMutexPend_full_return_wit_34.
Proof.
  pre_process.
  Right.
  Exists ls0 4.
  split_pure_spatial.
  - unfold UCOS2_Verify_inv.
    sepcon_assoc_change.
    coq_prop_lift.
    split_pure_spatial.
    + Intros_p Hcross.
      cancel (OutsideCritical sg ls0).
      cancel (interrupt_inv sg (IntrState ls0)).
      cancel (task_inv sg (TskState ls0)).
      cancel (sched_inv sg (TskState ls0) (SchedState ls0)).
      cancel (event_inv sg (TskState ls0) (EventState ls0)).
      cancel (tick_inv sg (TickState ls0)).
      cancel (perr_pre # UChar |-> 4).
      apply derivable1_truep_intros.
    + Intros_p Hcross.
      dump_pre_spatial.
      exact Hcross.
  - split_pures.
    + dump_pre_spatial.
      subst pevent_pre.
      eapply (highstependret_derive
        (bind (atomic_cmd (OSMutexPend_sem sg 0 timeout_pre))
          observe_os_err_code)
        (LastSeen ls0) 4 (fun _ => LastSeen ls0)).
      * unfold hs_eval, LastSeen.
        intros sigma Hsigma.
        exists (RTrans_Abs ls0).
        split.
        -- unfold_monad.
           exists OS_ERR_PEVENT_NULL, (RTrans_Abs ls0).
           split.
           ++ unfold atomic_cmd.
              exists ls0, ls0.
              split.
              ** apply (proj1 (Hsigma ls0)).
                 unfold RTrans_Abs, STS_UCOS2_Abs.RTrans,
                   C_STS_UCOS2_Abs.c_sts, UCOS2_CS_Abs.
                 exact I.
              ** split.
                 --- unfold OSMutexPend_sem.
                     left.
                     repeat split; reflexivity.
                 --- reflexivity.
           ++ unfold observe_os_err_code, encode_os_err_code.
              split; reflexivity.
        -- reflexivity.
      * exact H4.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      exact H.
Qed.

Lemma proof_of_OSMutexPend_full_return_wit_35 : OSMutexPend_full_return_wit_35.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_return_wit_36 : OSMutexPend_full_return_wit_36.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_return_wit_37 : OSMutexPend_full_return_wit_37.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_56_pure : OSMutexPend_full_partial_solve_wit_56_pure.
Proof. pre_process; entailer!. Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_57_pure : OSMutexPend_full_partial_solve_wit_57_pure.
Proof.
  pre_process; unfold task_inv_no_two_tids_priotbl; entailer!.
  all: unfold task_inherit_snapshot_of_prop, task_rdy_snapshot_of_prop in H34.
  all: destruct H34 as [[Howner_state [Htcb [Hprio [Hx [Hy [Hbitx Hbity]]]]]] Heventptr].
  all: match goal with
       | Htask : task_vaild_cond_prop _ _ |- _ =>
           unfold task_vaild_cond_prop in Htask;
           destruct Htask as [_ Hused_valid]
       end.
  all: specialize (Hused_valid owner_tid owner_t Howner_state).
  all: destruct Hused_valid as [_ Hderived].
  all: unfold valid_derived_fields in Hderived.
  all: destruct Hderived as [Hmod_lo [Hmod_hi [Hdiv_lo Hdiv_hi]]].
  all: unfold tcb_y_of_prio in Hy.
  all: subst owner_y.
  all: subst owner_new_y.
  all: try (apply Z.land_nonneg; right; lia).
  all: try (
    replace 7 with (Z.ones 3) by reflexivity;
    rewrite Z.land_ones by lia;
    apply Z.mod_pos_bound;
    lia).
  all: assumption.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_58_pure : OSMutexPend_full_partial_solve_wit_58_pure.
Proof.
  pre_process; unfold task_inv_no_two_tids_priotbl; entailer!.
  all: unfold task_inherit_snapshot_of_prop, task_rdy_snapshot_of_prop in H31.
  all: destruct H31 as [[Howner_state [Htcb [Hprio [Hx [Hy [Hbitx Hbity]]]]]] Heventptr].
  all: match goal with
       | Htask : task_vaild_cond_prop _ _ |- _ =>
           unfold task_vaild_cond_prop in Htask;
           destruct Htask as [_ Hused_valid]
       end.
  all: specialize (Hused_valid owner_tid owner_t Howner_state).
  all: destruct Hused_valid as [_ Hderived].
  all: unfold valid_derived_fields in Hderived.
  all: destruct Hderived as [Hmod_lo [Hmod_hi [Hdiv_lo Hdiv_hi]]].
  all: unfold tcb_y_of_prio in Hy.
  all: subst owner_y.
  all: subst owner_new_y.
  all: try (apply Z.land_nonneg; right; lia).
  all: try (
    replace 7 with (Z.ones 3) by reflexivity;
    rewrite Z.land_ones by lia;
    apply Z.mod_pos_bound;
    lia).
  all: assumption.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_59_pure : OSMutexPend_full_partial_solve_wit_59_pure.
Proof.
  pre_process; unfold task_inv_no_two_tids_priotbl; entailer!.
  all: unfold task_inherit_snapshot_of_prop, task_rdy_snapshot_of_prop in H31.
  all: destruct H31 as [[Howner_state [Htcb [Hprio [Hx [Hy [Hbitx Hbity]]]]]] Heventptr].
  all: match goal with
       | Htask : task_vaild_cond_prop _ _ |- _ =>
           unfold task_vaild_cond_prop in Htask;
           destruct Htask as [_ Hused_valid]
       end.
  all: specialize (Hused_valid owner_tid owner_t Howner_state).
  all: destruct Hused_valid as [_ Hderived].
  all: unfold valid_derived_fields in Hderived.
  all: destruct Hderived as [Hmod_lo [Hmod_hi [Hdiv_lo Hdiv_hi]]].
  all: unfold tcb_y_of_prio in Hy.
  all: subst owner_y.
  all: subst owner_new_y.
  all: try (apply Z.land_nonneg; right; lia).
  all: try (
    replace 7 with (Z.ones 3) by reflexivity;
    rewrite Z.land_ones by lia;
    apply Z.mod_pos_bound;
    lia).
  all: assumption.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_60_pure : OSMutexPend_full_partial_solve_wit_60_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSLockNesting)) (lockNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst lock.
  change (0 <= lockNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= lockNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_61_pure : OSMutexPend_full_partial_solve_wit_61_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSIntNesting)) (intNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst isr.
  change (0 <= intNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= intNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_66_pure : OSMutexPend_full_partial_solve_wit_66_pure.
Proof. pre_process; unfold decode_OwnerPrio_from_cnt in *; entailer!. Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_67_pure : OSMutexPend_full_partial_solve_wit_67_pure.
Proof.
  pre_process; unfold task_inv_no_two_tids_priotbl; entailer!.
  all: match goal with
       | Hsnap : task_inherit_snapshot_of_prop _ _ _ _ _ _ _ _ _ _ _ |- _ =>
           unfold task_inherit_snapshot_of_prop, task_rdy_snapshot_of_prop in Hsnap;
           destruct Hsnap as [[Howner_state [Htcb [Hprio [Hx [Hy [Hbitx Hbity]]]]]] Heventptr]
       end.
  all: match goal with
       | Htask : task_vaild_cond_prop _ _ |- _ =>
           unfold task_vaild_cond_prop in Htask;
           destruct Htask as [_ Hused_valid]
       end.
  all: specialize (Hused_valid owner_tid owner_t Howner_state).
  all: destruct Hused_valid as [_ Hderived].
  all: unfold valid_derived_fields in Hderived.
  all: destruct Hderived as [Hmod_lo [Hmod_hi [Hdiv_lo Hdiv_hi]]].
  all: unfold tcb_y_of_prio in Hy.
  all: subst owner_y.
  all: assumption.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_68_pure : OSMutexPend_full_partial_solve_wit_68_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSLockNesting)) (lockNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst lock.
  change (0 <= lockNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= lockNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_69_pure : OSMutexPend_full_partial_solve_wit_69_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSIntNesting)) (intNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst isr.
  change (0 <= intNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= intNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_70_pure : OSMutexPend_full_partial_solve_wit_70_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSIntNesting)) (intNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst isr.
  change (0 <= intNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= intNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_71_pure : OSMutexPend_full_partial_solve_wit_71_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSLockNesting)) (lockNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst lock.
  change (0 <= lockNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= lockNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_72_pure : OSMutexPend_full_partial_solve_wit_72_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl.
  Intros_p Htask.
  dump_pre_spatial.
  match goal with
  | Hsnap : task_inherit_snapshot_of_prop _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold task_inherit_snapshot_of_prop, task_rdy_snapshot_of_prop in Hsnap;
      destruct Hsnap as [[Howner_state [Htcb [Hprio [Hx [Hy [Hbitx Hbity]]]]]] Heventptr]
  end.
  unfold task_vaild_cond_prop in Htask.
  destruct Htask as [_ Hused_valid].
  specialize (Hused_valid owner_tid owner_t Howner_state).
  destruct Hused_valid as [Hvalid _].
  unfold valid_task_prio in Hvalid.
  destruct Hvalid as [Howner_nonneg Howner_hi].
  match goal with
  | Hsg : valid_stable_glob_vars sg |- _ =>
      unfold valid_stable_glob_vars in Hsg;
      destruct Hsg as [_ [_ [_ [_ [_ [Hlowest_eq _]]]]]]
  end.
  subst owner_prio.
  rewrite Hlowest_eq in Howner_hi.
  unfold decode_PCP_from_cnt.
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hpcp_byte.
  assert (Hpcp_hi : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 63).
  { match goal with
    | Hgt : Z.gt (curPrio owner_t)
        (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) |- _ =>
        exact (Z.lt_trans
          (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
          (curPrio owner_t) 63 (Z.gt_lt _ _ Hgt) Howner_hi)
    end. }
  assert (Hpcp64 : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 8 * 8).
  { lia. }
  assert (Hq : 0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8).
  { split.
    - apply (proj2 (Z.shiftr_nonneg _ _)); exact (proj1 Hpcp_byte).
    - rewrite Z.shiftr_div_pow2 by lia.
      change (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 / 8 < 8).
      exact (Z.div_lt_upper_bound _ 8 8 ltac:(lia) Hpcp64). }
  rewrite unsigned_last_nbits_eq by
    (split; [exact (proj1 Hq) | eapply Z.lt_trans; [exact (proj2 Hq) | lia]]).
  replace 7 with (Z.ones 3) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by (change (0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8); exact Hq).
  reflexivity.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_73_pure : OSMutexPend_full_partial_solve_wit_73_pure.
Proof. pre_process; unfold decode_OwnerPrio_from_cnt in *; entailer!. Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_74_pure : OSMutexPend_full_partial_solve_wit_74_pure.
Proof. pre_process; unfold decode_OwnerPrio_from_cnt in *; entailer!. Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_75_pure : OSMutexPend_full_partial_solve_wit_75_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl.
  Intros_p Htask.
  dump_pre_spatial.
  match goal with
  | Hsnap : task_inherit_snapshot_of_prop _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold task_inherit_snapshot_of_prop, task_rdy_snapshot_of_prop in Hsnap;
      destruct Hsnap as [[Howner_state [Htcb [Hprio [Hx [Hy [Hbitx Hbity]]]]]] Heventptr]
  end.
  unfold task_vaild_cond_prop in Htask.
  destruct Htask as [_ Hused_valid].
  specialize (Hused_valid owner_tid owner_t Howner_state).
  destruct Hused_valid as [Hvalid _].
  unfold valid_task_prio in Hvalid.
  destruct Hvalid as [Howner_nonneg Howner_hi].
  match goal with
  | Hsg : valid_stable_glob_vars sg |- _ =>
      unfold valid_stable_glob_vars in Hsg;
      destruct Hsg as [_ [_ [_ [_ [_ [Hlowest_eq _]]]]]]
  end.
  subst owner_prio.
  rewrite Hlowest_eq in Howner_hi.
  unfold decode_PCP_from_cnt.
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hpcp_byte.
  assert (Hpcp_hi : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 63).
  { match goal with
    | Hgt : Z.gt (curPrio owner_t)
        (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) |- _ =>
        exact (Z.lt_trans
          (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
          (curPrio owner_t) 63 (Z.gt_lt _ _ Hgt) Howner_hi)
    end. }
  assert (Hpcp64 : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 8 * 8).
  { lia. }
  assert (Hq : 0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8).
  { split.
    - apply (proj2 (Z.shiftr_nonneg _ _)); exact (proj1 Hpcp_byte).
    - rewrite Z.shiftr_div_pow2 by lia.
      change (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 / 8 < 8).
      exact (Z.div_lt_upper_bound _ 8 8 ltac:(lia) Hpcp64). }
  rewrite unsigned_last_nbits_eq by
    (split; [exact (proj1 Hq) | eapply Z.lt_trans; [exact (proj2 Hq) | lia]]).
  replace 7 with (Z.ones 3) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by (change (0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8); exact Hq).
  reflexivity.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_76_pure : OSMutexPend_full_partial_solve_wit_76_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSLockNesting)) (lockNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst lock.
  change (0 <= lockNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= lockNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_77_pure : OSMutexPend_full_partial_solve_wit_77_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSIntNesting)) (intNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst isr.
  change (0 <= intNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= intNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_78_pure : OSMutexPend_full_partial_solve_wit_78_pure.
Proof. pre_process; unfold decode_OwnerPrio_from_cnt in *; entailer!. Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_79_pure : OSMutexPend_full_partial_solve_wit_79_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl.
  Intros_p Htask.
  dump_pre_spatial.
  match goal with
  | Hsnap : task_inherit_snapshot_of_prop _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold task_inherit_snapshot_of_prop, task_rdy_snapshot_of_prop in Hsnap;
      destruct Hsnap as [[Howner_state [Htcb [Hprio [Hx [Hy [Hbitx Hbity]]]]]] Heventptr]
  end.
  unfold task_vaild_cond_prop in Htask.
  destruct Htask as [_ Hused_valid].
  specialize (Hused_valid owner_tid owner_t Howner_state).
  destruct Hused_valid as [Hvalid _].
  unfold valid_task_prio in Hvalid.
  destruct Hvalid as [Howner_nonneg Howner_hi].
  match goal with
  | Hsg : valid_stable_glob_vars sg |- _ =>
      unfold valid_stable_glob_vars in Hsg;
      destruct Hsg as [_ [_ [_ [_ [_ [Hlowest_eq _]]]]]]
  end.
  subst owner_prio.
  rewrite Hlowest_eq in Howner_hi.
  unfold decode_PCP_from_cnt.
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hpcp_byte.
  assert (Hpcp_hi : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 63).
  { match goal with
    | Hgt : Z.gt (curPrio owner_t)
        (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) |- _ =>
        exact (Z.lt_trans
          (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
          (curPrio owner_t) 63 (Z.gt_lt _ _ Hgt) Howner_hi)
    end. }
  assert (Hpcp64 : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 8 * 8).
  { lia. }
  assert (Hq : 0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8).
  { split.
    - apply (proj2 (Z.shiftr_nonneg _ _)); exact (proj1 Hpcp_byte).
    - rewrite Z.shiftr_div_pow2 by lia.
      change (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 / 8 < 8).
      exact (Z.div_lt_upper_bound _ 8 8 ltac:(lia) Hpcp64). }
  rewrite unsigned_last_nbits_eq by
    (split; [exact (proj1 Hq) | eapply Z.lt_trans; [exact (proj2 Hq) | lia]]).
  replace 7 with (Z.ones 3) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by (change (0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8); exact Hq).
  reflexivity.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_80_pure : OSMutexPend_full_partial_solve_wit_80_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl.
  Intros_p Htask.
  dump_pre_spatial.
  match goal with
  | Hsnap : task_inherit_snapshot_of_prop _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold task_inherit_snapshot_of_prop, task_rdy_snapshot_of_prop in Hsnap;
      destruct Hsnap as [[Howner_state [Htcb [Hprio [Hx [Hy [Hbitx Hbity]]]]]] Heventptr]
  end.
  unfold task_vaild_cond_prop in Htask.
  destruct Htask as [_ Hused_valid].
  specialize (Hused_valid owner_tid owner_t Howner_state).
  destruct Hused_valid as [Hvalid _].
  unfold valid_task_prio in Hvalid.
  destruct Hvalid as [Howner_nonneg Howner_hi].
  match goal with
  | Hsg : valid_stable_glob_vars sg |- _ =>
      unfold valid_stable_glob_vars in Hsg;
      destruct Hsg as [_ [_ [_ [_ [_ [Hlowest_eq _]]]]]]
  end.
  subst owner_prio.
  rewrite Hlowest_eq in Howner_hi.
  unfold decode_PCP_from_cnt.
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hpcp_byte.
  assert (Hpcp_hi : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 63).
  { match goal with
    | Hgt : Z.gt (curPrio owner_t)
        (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) |- _ =>
        exact (Z.lt_trans
          (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
          (curPrio owner_t) 63 (Z.gt_lt _ _ Hgt) Howner_hi)
    end. }
  assert (Hpcp64 : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 8 * 8).
  { lia. }
  assert (Hq : 0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8).
  { split.
    - apply (proj2 (Z.shiftr_nonneg _ _)); exact (proj1 Hpcp_byte).
    - rewrite Z.shiftr_div_pow2 by lia.
      change (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 / 8 < 8).
      exact (Z.div_lt_upper_bound _ 8 8 ltac:(lia) Hpcp64). }
  rewrite unsigned_last_nbits_eq by
    (split; [exact (proj1 Hq) | eapply Z.lt_trans; [exact (proj2 Hq) | lia]]).
  replace 7 with (Z.ones 3) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by (change (0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8); exact Hq).
  reflexivity.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_81_pure : OSMutexPend_full_partial_solve_wit_81_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSLockNesting)) (lockNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst lock.
  change (0 <= lockNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= lockNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_82_pure : OSMutexPend_full_partial_solve_wit_82_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSIntNesting)) (intNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst isr.
  change (0 <= intNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= intNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_83_pure : OSMutexPend_full_partial_solve_wit_83_pure.
Proof. pre_process; unfold decode_OwnerPrio_from_cnt in *; entailer!. Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_84_pure : OSMutexPend_full_partial_solve_wit_84_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl.
  Intros_p Htask.
  dump_pre_spatial.
  match goal with
  | Hsnap : task_inherit_snapshot_of_prop _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold task_inherit_snapshot_of_prop, task_rdy_snapshot_of_prop in Hsnap;
      destruct Hsnap as [[Howner_state [Htcb [Hprio [Hx [Hy [Hbitx Hbity]]]]]] Heventptr]
  end.
  unfold task_vaild_cond_prop in Htask.
  destruct Htask as [_ Hused_valid].
  specialize (Hused_valid owner_tid owner_t Howner_state).
  destruct Hused_valid as [Hvalid _].
  unfold valid_task_prio in Hvalid.
  destruct Hvalid as [Howner_nonneg Howner_hi].
  match goal with
  | Hsg : valid_stable_glob_vars sg |- _ =>
      unfold valid_stable_glob_vars in Hsg;
      destruct Hsg as [_ [_ [_ [_ [_ [Hlowest_eq _]]]]]]
  end.
  subst owner_prio.
  rewrite Hlowest_eq in Howner_hi.
  unfold decode_PCP_from_cnt.
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hpcp_byte.
  assert (Hpcp_hi : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 63).
  { match goal with
    | Hgt : Z.gt (curPrio owner_t)
        (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) |- _ =>
        exact (Z.lt_trans
          (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
          (curPrio owner_t) 63 (Z.gt_lt _ _ Hgt) Howner_hi)
    end. }
  assert (Hpcp64 : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 8 * 8).
  { lia. }
  assert (Hq : 0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8).
  { split.
    - apply (proj2 (Z.shiftr_nonneg _ _)); exact (proj1 Hpcp_byte).
    - rewrite Z.shiftr_div_pow2 by lia.
      change (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 / 8 < 8).
      exact (Z.div_lt_upper_bound _ 8 8 ltac:(lia) Hpcp64). }
  rewrite unsigned_last_nbits_eq by
    (split; [exact (proj1 Hq) | eapply Z.lt_trans; [exact (proj2 Hq) | lia]]).
  replace 7 with (Z.ones 3) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by (change (0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8); exact Hq).
  reflexivity.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_85_pure : OSMutexPend_full_partial_solve_wit_85_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl.
  Intros_p Htask.
  dump_pre_spatial.
  match goal with
  | Hsnap : task_inherit_snapshot_of_prop _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold task_inherit_snapshot_of_prop, task_rdy_snapshot_of_prop in Hsnap;
      destruct Hsnap as [[Howner_state [Htcb [Hprio [Hx [Hy [Hbitx Hbity]]]]]] Heventptr]
  end.
  unfold task_vaild_cond_prop in Htask.
  destruct Htask as [_ Hused_valid].
  specialize (Hused_valid owner_tid owner_t Howner_state).
  destruct Hused_valid as [Hvalid _].
  unfold valid_task_prio in Hvalid.
  destruct Hvalid as [Howner_nonneg Howner_hi].
  match goal with
  | Hsg : valid_stable_glob_vars sg |- _ =>
      unfold valid_stable_glob_vars in Hsg;
      destruct Hsg as [_ [_ [_ [_ [_ [Hlowest_eq _]]]]]]
  end.
  subst owner_prio.
  rewrite Hlowest_eq in Howner_hi.
  unfold decode_PCP_from_cnt.
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hpcp_byte.
  assert (Hpcp_hi : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 63).
  { match goal with
    | Hgt : Z.gt (curPrio owner_t)
        (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) |- _ =>
        exact (Z.lt_trans
          (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
          (curPrio owner_t) 63 (Z.gt_lt _ _ Hgt) Howner_hi)
    end. }
  assert (Hpcp64 : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 8 * 8).
  { lia. }
  assert (Hq : 0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8).
  { split.
    - apply (proj2 (Z.shiftr_nonneg _ _)); exact (proj1 Hpcp_byte).
    - rewrite Z.shiftr_div_pow2 by lia.
      change (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 / 8 < 8).
      exact (Z.div_lt_upper_bound _ 8 8 ltac:(lia) Hpcp64). }
  rewrite unsigned_last_nbits_eq by
    (split; [exact (proj1 Hq) | eapply Z.lt_trans; [exact (proj2 Hq) | lia]]).
  replace 7 with (Z.ones 3) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by (change (0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8); exact Hq).
  reflexivity.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_86_pure : OSMutexPend_full_partial_solve_wit_86_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl.
  Intros_p Htask.
  dump_pre_spatial.
  match goal with
  | Hsnap : task_inherit_snapshot_of_prop _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold task_inherit_snapshot_of_prop, task_rdy_snapshot_of_prop in Hsnap;
      destruct Hsnap as [[Howner_state [Htcb [Hprio [Hx [Hy [Hbitx Hbity]]]]]] Heventptr]
  end.
  unfold task_vaild_cond_prop in Htask.
  destruct Htask as [_ Hused_valid].
  specialize (Hused_valid owner_tid owner_t Howner_state).
  destruct Hused_valid as [Hvalid _].
  unfold valid_task_prio in Hvalid.
  destruct Hvalid as [Howner_nonneg Howner_hi].
  match goal with
  | Hsg : valid_stable_glob_vars sg |- _ =>
      unfold valid_stable_glob_vars in Hsg;
      destruct Hsg as [_ [_ [_ [_ [_ [Hlowest_eq _]]]]]]
  end.
  subst owner_prio.
  rewrite Hlowest_eq in Howner_hi.
  unfold decode_PCP_from_cnt.
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hpcp_byte.
  assert (Hpcp_hi : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 63).
  { match goal with
    | Hgt : Z.gt (curPrio owner_t)
        (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) |- _ =>
        exact (Z.lt_trans
          (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
          (curPrio owner_t) 63 (Z.gt_lt _ _ Hgt) Howner_hi)
    end. }
  assert (Hpcp64 : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 8 * 8).
  { lia. }
  assert (Hq : 0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8).
  { split.
    - apply (proj2 (Z.shiftr_nonneg _ _)); exact (proj1 Hpcp_byte).
    - rewrite Z.shiftr_div_pow2 by lia.
      change (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 / 8 < 8).
      exact (Z.div_lt_upper_bound _ 8 8 ltac:(lia) Hpcp64). }
  rewrite unsigned_last_nbits_eq by
    (split; [exact (proj1 Hq) | eapply Z.lt_trans; [exact (proj2 Hq) | lia]]).
  replace 7 with (Z.ones 3) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by (change (0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8); exact Hq).
  reflexivity.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_87_pure : OSMutexPend_full_partial_solve_wit_87_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSLockNesting)) (lockNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst lock.
  change (0 <= lockNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= lockNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_88_pure : OSMutexPend_full_partial_solve_wit_88_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSIntNesting)) (intNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst isr.
  change (0 <= intNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= intNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_89_pure : OSMutexPend_full_partial_solve_wit_89_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSIntNesting)) (intNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst isr.
  change (0 <= intNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= intNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_90_pure : OSMutexPend_full_partial_solve_wit_90_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSLockNesting)) (lockNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst lock.
  change (0 <= lockNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= lockNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_91_pure : OSMutexPend_full_partial_solve_wit_91_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl.
  Intros_p Htask.
  dump_pre_spatial.
  match goal with
  | Hsnap : task_inherit_snapshot_of_prop _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold task_inherit_snapshot_of_prop, task_rdy_snapshot_of_prop in Hsnap;
      destruct Hsnap as [[Howner_state [Htcb [Hprio [Hx [Hy [Hbitx Hbity]]]]]] Heventptr]
  end.
  unfold task_vaild_cond_prop in Htask.
  destruct Htask as [_ Hused_valid].
  specialize (Hused_valid owner_tid owner_t Howner_state).
  destruct Hused_valid as [Hvalid _].
  unfold valid_task_prio in Hvalid.
  destruct Hvalid as [Howner_nonneg Howner_hi].
  match goal with
  | Hsg : valid_stable_glob_vars sg |- _ =>
      unfold valid_stable_glob_vars in Hsg;
      destruct Hsg as [_ [_ [_ [_ [_ [Hlowest_eq _]]]]]]
  end.
  subst owner_prio.
  rewrite Hlowest_eq in Howner_hi.
  unfold decode_PCP_from_cnt.
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hpcp_byte.
  assert (Hpcp_hi : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 63).
  { match goal with
    | Hgt : Z.gt (curPrio owner_t)
        (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) |- _ =>
        exact (Z.lt_trans
          (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
          (curPrio owner_t) 63 (Z.gt_lt _ _ Hgt) Howner_hi)
    end. }
  assert (Hpcp64 : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 8 * 8).
  { lia. }
  assert (Hq : 0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8).
  { split.
    - apply (proj2 (Z.shiftr_nonneg _ _)); exact (proj1 Hpcp_byte).
    - rewrite Z.shiftr_div_pow2 by lia.
      change (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 / 8 < 8).
      exact (Z.div_lt_upper_bound _ 8 8 ltac:(lia) Hpcp64). }
  rewrite unsigned_last_nbits_eq by
    (split; [exact (proj1 Hq) | eapply Z.lt_trans; [exact (proj2 Hq) | lia]]).
  replace 7 with (Z.ones 3) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by (change (0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8); exact Hq).
  reflexivity.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_92_pure : OSMutexPend_full_partial_solve_wit_92_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl.
  Intros_p Htask.
  dump_pre_spatial.
  match goal with
  | Hsnap : task_inherit_snapshot_of_prop _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold task_inherit_snapshot_of_prop, task_rdy_snapshot_of_prop in Hsnap;
      destruct Hsnap as [[Howner_state [Htcb [Hprio [Hx [Hy [Hbitx Hbity]]]]]] Heventptr]
  end.
  unfold task_vaild_cond_prop in Htask.
  destruct Htask as [_ Hused_valid].
  specialize (Hused_valid owner_tid owner_t Howner_state).
  destruct Hused_valid as [Hvalid _].
  unfold valid_task_prio in Hvalid.
  destruct Hvalid as [Howner_nonneg Howner_hi].
  match goal with
  | Hsg : valid_stable_glob_vars sg |- _ =>
      unfold valid_stable_glob_vars in Hsg;
      destruct Hsg as [_ [_ [_ [_ [_ [Hlowest_eq _]]]]]]
  end.
  subst owner_prio.
  rewrite Hlowest_eq in Howner_hi.
  unfold decode_PCP_from_cnt.
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hpcp_byte.
  assert (Hpcp_hi : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 63).
  { match goal with
    | Hgt : Z.gt (curPrio owner_t)
        (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) |- _ =>
        exact (Z.lt_trans
          (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
          (curPrio owner_t) 63 (Z.gt_lt _ _ Hgt) Howner_hi)
    end. }
  assert (Hpcp64 : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 8 * 8).
  { lia. }
  assert (Hq : 0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8).
  { split.
    - apply (proj2 (Z.shiftr_nonneg _ _)); exact (proj1 Hpcp_byte).
    - rewrite Z.shiftr_div_pow2 by lia.
      change (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 / 8 < 8).
      exact (Z.div_lt_upper_bound _ 8 8 ltac:(lia) Hpcp64). }
  rewrite unsigned_last_nbits_eq by
    (split; [exact (proj1 Hq) | eapply Z.lt_trans; [exact (proj2 Hq) | lia]]).
  replace 7 with (Z.ones 3) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by (change (0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8); exact Hq).
  reflexivity.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_93_pure : OSMutexPend_full_partial_solve_wit_93_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl.
  Intros_p Htask.
  dump_pre_spatial.
  match goal with
  | Hsnap : task_inherit_snapshot_of_prop _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold task_inherit_snapshot_of_prop, task_rdy_snapshot_of_prop in Hsnap;
      destruct Hsnap as [[Howner_state [Htcb [Hprio [Hx [Hy [Hbitx Hbity]]]]]] Heventptr]
  end.
  unfold task_vaild_cond_prop in Htask.
  destruct Htask as [_ Hused_valid].
  specialize (Hused_valid owner_tid owner_t Howner_state).
  destruct Hused_valid as [Hvalid _].
  unfold valid_task_prio in Hvalid.
  destruct Hvalid as [Howner_nonneg Howner_hi].
  match goal with
  | Hsg : valid_stable_glob_vars sg |- _ =>
      unfold valid_stable_glob_vars in Hsg;
      destruct Hsg as [_ [_ [_ [_ [_ [Hlowest_eq _]]]]]]
  end.
  subst owner_prio.
  rewrite Hlowest_eq in Howner_hi.
  unfold decode_PCP_from_cnt.
  pose proof (unsigned_Lastnbits_range (Z.shiftr ecnt_in 8) 8 ltac:(lia)) as Hpcp_byte.
  assert (Hpcp_hi : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 63).
  { match goal with
    | Hgt : Z.gt (curPrio owner_t)
        (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) |- _ =>
        exact (Z.lt_trans
          (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
          (curPrio owner_t) 63 (Z.gt_lt _ _ Hgt) Howner_hi)
    end. }
  assert (Hpcp64 : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 < 8 * 8).
  { lia. }
  assert (Hq : 0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8).
  { split.
    - apply (proj2 (Z.shiftr_nonneg _ _)); exact (proj1 Hpcp_byte).
    - rewrite Z.shiftr_div_pow2 by lia.
      change (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 / 8 < 8).
      exact (Z.div_lt_upper_bound _ 8 8 ltac:(lia) Hpcp64). }
  rewrite unsigned_last_nbits_eq by
    (split; [exact (proj1 Hq) | eapply Z.lt_trans; [exact (proj2 Hq) | lia]]).
  replace 7 with (Z.ones 3) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by (change (0 <= Z.shiftr (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 3 < 8); exact Hq).
  reflexivity.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_94_pure : OSMutexPend_full_partial_solve_wit_94_pure.
Proof. pre_process; unfold decode_OwnerPrio_from_cnt in *; entailer!. Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_95_pure : OSMutexPend_full_partial_solve_wit_95_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSIntNesting)) (intNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst isr.
  change (0 <= intNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= intNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_96_pure : OSMutexPend_full_partial_solve_wit_96_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSLockNesting)) (lockNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst lock.
  change (0 <= lockNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= lockNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_97_pure : OSMutexPend_full_partial_solve_wit_97_pure.
Proof.
  pre_process.
  split_pures.
  all: dump_pre_spatial.
  all: subst owner_new_y.
  all: first
    [ apply Z.land_nonneg; right; lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      apply Z.mod_pos_bound; lia ].
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_98_pure : OSMutexPend_full_partial_solve_wit_98_pure.
Proof. pre_process; unfold decode_OwnerPrio_from_cnt in *; entailer!. Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_99_pure : OSMutexPend_full_partial_solve_wit_99_pure.
Proof. pre_process; unfold decode_OwnerPrio_from_cnt in *; entailer!. Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_100_pure : OSMutexPend_full_partial_solve_wit_100_pure.
Proof.
  pre_process.
  split_pures.
  all: dump_pre_spatial.
  all: subst owner_new_y.
  all: first
    [ apply Z.land_nonneg; right; lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      apply Z.mod_pos_bound; lia ].
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_101_pure : OSMutexPend_full_partial_solve_wit_101_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSLockNesting)) (lockNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst lock.
  change (0 <= lockNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= lockNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_102_pure : OSMutexPend_full_partial_solve_wit_102_pure.
Proof.
  pre_process.
  unfold interrupt_inv, store_int_state.
  Intros_p Hintr.
  prop_apply_p (store_uchar_range
    (sg.(g_OSIntNesting)) (intNesting (ls1.(IntrState)))).
  Intros_p Hrange.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  subst isr.
  change (0 <= intNesting (IntrState ls0) <= 255) in Hrange.
  assert (Hbyte_lt_word : (255 < 4294967296)%Z) by lia.
  assert (Hsmall : 0 <= intNesting (IntrState ls0) < 4294967296).
  { split.
    - exact (proj1 Hrange).
    - exact (Z.le_lt_trans _ _ _ (proj2 Hrange) Hbyte_lt_word). }
  match goal with
  | Htrunc : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      unfold unsigned_last_nbits in Htrunc;
      rewrite Z.mod_small in Htrunc by exact Hsmall
  end.
  exfalso; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_128_pure : OSMutexPend_full_partial_solve_wit_128_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_129_pure : OSMutexPend_full_partial_solve_wit_129_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl at 1.
  Intros_p Htask_valid.
  split_pures.
  all: dump_pre_spatial.
  all: unfold task_vaild_cond_prop in Htask_valid.
  all: destruct Htask_valid as [_ Htasks_valid].
  all: match goal with
       | Hsnap : task_inherit_snapshot_of_prop ?sg ?st ?tid ?t
                   ?tcb ?prio ?x ?y ?bitx ?bity ?eventptr |- _ =>
           unfold task_inherit_snapshot_of_prop,
             task_rdy_snapshot_of_prop in Hsnap;
           destruct Hsnap as
             [[Howner_map [_ [Howner_prio [_ [_ [_ _]]]]]] _];
           pose proof (Htasks_valid tid t Howner_map) as [Howner_valid _];
           unfold valid_task_prio in Howner_valid
       end.
  all: match goal with
       | Hsg : valid_stable_glob_vars ?sg |- _ =>
           unfold valid_stable_glob_vars in Hsg;
           destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]]
       end.
  all: match goal with
       | Howner_prio : ?prio = ?tprio,
         Hgt : ?prio > unsigned_last_nbits (Z.shiftr ?ecnt 8) 8 |- _ =>
           rewrite Howner_prio in Hgt
       end.
  all: match goal with
       | Hidx : ?pcp_idx = decode_PCP_from_cnt ?ecnt |- _ =>
           subst pcp_idx; unfold decode_PCP_from_cnt
       end.
  all: match goal with
       | |- context [unsigned_last_nbits (Z.shiftr ?ecnt 8) 8] =>
           pose proof
             (unsigned_Lastnbits_range (Z.shiftr ecnt 8) 8 ltac:(lia))
             as Hpcp
       end.
  all: try reflexivity; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_130_pure : OSMutexPend_full_partial_solve_wit_130_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl at 1.
  Intros_p Htask_valid.
  split_pures.
  all: dump_pre_spatial.
  all: unfold task_vaild_cond_prop in Htask_valid.
  all: destruct Htask_valid as [_ Htasks_valid].
  all: match goal with
       | Hsnap : task_inherit_snapshot_of_prop ?sg ?st ?tid ?t
                   ?tcb ?prio ?x ?y ?bitx ?bity ?eventptr |- _ =>
           unfold task_inherit_snapshot_of_prop,
             task_rdy_snapshot_of_prop in Hsnap;
           destruct Hsnap as
             [[Howner_map [_ [Howner_prio [_ [_ [_ _]]]]]] _];
           pose proof (Htasks_valid tid t Howner_map) as [Howner_valid _];
           unfold valid_task_prio in Howner_valid
       end.
  all: match goal with
       | Hsg : valid_stable_glob_vars ?sg |- _ =>
           unfold valid_stable_glob_vars in Hsg;
           destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]]
       end.
  all: match goal with
       | Howner_prio : ?prio = ?tprio,
         Hgt : ?prio > unsigned_last_nbits (Z.shiftr ?ecnt 8) 8 |- _ =>
           rewrite Howner_prio in Hgt
       end.
  all: match goal with
       | Hidx : ?pcp_idx = decode_PCP_from_cnt ?ecnt |- _ =>
           subst pcp_idx; unfold decode_PCP_from_cnt
       end.
  all: match goal with
       | |- context [unsigned_last_nbits (Z.shiftr ?ecnt 8) 8] =>
           pose proof
             (unsigned_Lastnbits_range (Z.shiftr ecnt 8) 8 ltac:(lia))
             as Hpcp
       end.
  all: try reflexivity; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_131_pure : OSMutexPend_full_partial_solve_wit_131_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl at 1.
  Intros_p Htask_valid.
  split_pures.
  all: dump_pre_spatial.
  all: unfold task_vaild_cond_prop in Htask_valid.
  all: destruct Htask_valid as [_ Htasks_valid].
  all: match goal with
       | Hsnap : task_inherit_snapshot_of_prop ?sg ?st ?tid ?t
                   ?tcb ?prio ?x ?y ?bitx ?bity ?eventptr |- _ =>
           unfold task_inherit_snapshot_of_prop,
             task_rdy_snapshot_of_prop in Hsnap;
           destruct Hsnap as
             [[Howner_map [_ [Howner_prio [_ [_ [_ _]]]]]] _];
           pose proof (Htasks_valid tid t Howner_map) as [Howner_valid _];
           unfold valid_task_prio in Howner_valid
       end.
  all: match goal with
       | Hsg : valid_stable_glob_vars ?sg |- _ =>
           unfold valid_stable_glob_vars in Hsg;
           destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]]
       end.
  all: match goal with
       | Howner_prio : ?prio = ?tprio,
         Hgt : ?prio > unsigned_last_nbits (Z.shiftr ?ecnt 8) 8 |- _ =>
           rewrite Howner_prio in Hgt
       end.
  all: match goal with
       | Hidx : ?pcp_idx = decode_PCP_from_cnt ?ecnt |- _ =>
           subst pcp_idx; unfold decode_PCP_from_cnt
       end.
  all: match goal with
       | |- context [unsigned_last_nbits (Z.shiftr ?ecnt 8) 8] =>
           pose proof
             (unsigned_Lastnbits_range (Z.shiftr ecnt 8) 8 ltac:(lia))
             as Hpcp
       end.
  all: try reflexivity; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_132_pure : OSMutexPend_full_partial_solve_wit_132_pure.
Proof.
  pre_process.
  match goal with
  | Hrel : crit_rel_no_os_state_change ?ls0 ?ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  unfold interrupt_inv, store_int_state at 1.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  split_pures.
  all: dump_pre_spatial.
  all: match goal with
       | Hiseq : ?isr = intNesting (IntrState ?ls) |- _ =>
           rewrite <- Hiseq in Hisr_range
       end.
  all: match goal with
       | Hlockeq : ?lock = lockNesting (IntrState ?ls) |- _ =>
           rewrite <- Hlockeq in Hlock_range
       end.
  all: change (0 <= isr <= 255) in Hisr_range.
  all: change (0 <= lock <= 255) in Hlock_range.
  all: repeat match goal with
       | Hcast : unsigned_last_nbits ?x 32 <= 0 |- _ =>
           rewrite (unsigned_last_nbits_eq x 32) in Hcast by lia
       end.
  all: lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_133_pure : OSMutexPend_full_partial_solve_wit_133_pure.
Proof.
  pre_process.
  match goal with
  | Hrel : crit_rel_no_os_state_change ?ls0 ?ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  unfold interrupt_inv, store_int_state at 1.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  split_pures.
  all: dump_pre_spatial.
  all: match goal with
       | Hiseq : ?isr = intNesting (IntrState ?ls) |- _ =>
           rewrite <- Hiseq in Hisr_range
       end.
  all: match goal with
       | Hlockeq : ?lock = lockNesting (IntrState ?ls) |- _ =>
           rewrite <- Hlockeq in Hlock_range
       end.
  all: change (0 <= isr <= 255) in Hisr_range.
  all: change (0 <= lock <= 255) in Hlock_range.
  all: repeat match goal with
       | Hcast : unsigned_last_nbits ?x 32 <= 0 |- _ =>
           rewrite (unsigned_last_nbits_eq x 32) in Hcast by lia
       end.
  all: lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_134_pure : OSMutexPend_full_partial_solve_wit_134_pure.
Proof.
  pre_process.
  match goal with
  | Hrel : crit_rel_no_os_state_change ?ls0 ?ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  unfold interrupt_inv, store_int_state at 1.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  split_pures.
  all: dump_pre_spatial.
  all: match goal with
       | Hiseq : ?isr = intNesting (IntrState ?ls) |- _ =>
           rewrite <- Hiseq in Hisr_range
       end.
  all: match goal with
       | Hlockeq : ?lock = lockNesting (IntrState ?ls) |- _ =>
           rewrite <- Hlockeq in Hlock_range
       end.
  all: change (0 <= isr <= 255) in Hisr_range.
  all: change (0 <= lock <= 255) in Hlock_range.
  all: repeat match goal with
       | Hcast : unsigned_last_nbits ?x 32 <= 0 |- _ =>
           rewrite (unsigned_last_nbits_eq x 32) in Hcast by lia
       end.
  all: lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_135_pure : OSMutexPend_full_partial_solve_wit_135_pure.
Proof.
  pre_process.
  match goal with
  | Hrel : crit_rel_no_os_state_change ?ls0 ?ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  unfold interrupt_inv, store_int_state at 1.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  split_pures.
  all: dump_pre_spatial.
  all: match goal with
       | Hiseq : ?isr = intNesting (IntrState ?ls) |- _ =>
           rewrite <- Hiseq in Hisr_range
       end.
  all: match goal with
       | Hlockeq : ?lock = lockNesting (IntrState ?ls) |- _ =>
           rewrite <- Hlockeq in Hlock_range
       end.
  all: change (0 <= isr <= 255) in Hisr_range.
  all: change (0 <= lock <= 255) in Hlock_range.
  all: repeat match goal with
       | Hcast : unsigned_last_nbits ?x 32 <= 0 |- _ =>
           rewrite (unsigned_last_nbits_eq x 32) in Hcast by lia
       end.
  all: lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_136_pure : OSMutexPend_full_partial_solve_wit_136_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl at 1.
  Intros_p Htask_valid.
  split_pures.
  all: dump_pre_spatial.
  all: unfold task_vaild_cond_prop in Htask_valid.
  all: destruct Htask_valid as [_ Htasks_valid].
  all: match goal with
       | Hsnap : task_inherit_snapshot_of_prop ?sg ?st ?tid ?t
                   ?tcb ?prio ?x ?y ?bitx ?bity ?eventptr |- _ =>
           unfold task_inherit_snapshot_of_prop,
             task_rdy_snapshot_of_prop in Hsnap;
           destruct Hsnap as
             [[Howner_map [_ [Howner_prio [_ [_ [_ _]]]]]] _];
           pose proof (Htasks_valid tid t Howner_map) as [Howner_valid _];
           unfold valid_task_prio in Howner_valid
       end.
  all: match goal with
       | Hsg : valid_stable_glob_vars ?sg |- _ =>
           unfold valid_stable_glob_vars in Hsg;
           destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]]
       end.
  all: match goal with
       | Howner_prio : ?prio = ?tprio,
         Hgt : ?prio > unsigned_last_nbits (Z.shiftr ?ecnt 8) 8 |- _ =>
           rewrite Howner_prio in Hgt
       end.
  all: match goal with
       | Hidx : ?pcp_idx = decode_PCP_from_cnt ?ecnt |- _ =>
           subst pcp_idx; unfold decode_PCP_from_cnt
       end.
  all: match goal with
       | |- context [unsigned_last_nbits (Z.shiftr ?ecnt 8) 8] =>
           pose proof
             (unsigned_Lastnbits_range (Z.shiftr ecnt 8) 8 ltac:(lia))
             as Hpcp
       end.
  all: try reflexivity; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_137_pure : OSMutexPend_full_partial_solve_wit_137_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl at 1.
  Intros_p Htask_valid.
  split_pures.
  all: dump_pre_spatial.
  all: unfold task_vaild_cond_prop in Htask_valid.
  all: destruct Htask_valid as [_ Htasks_valid].
  all: match goal with
       | Hsnap : task_inherit_snapshot_of_prop ?sg ?st ?tid ?t
                   ?tcb ?prio ?x ?y ?bitx ?bity ?eventptr |- _ =>
           unfold task_inherit_snapshot_of_prop,
             task_rdy_snapshot_of_prop in Hsnap;
           destruct Hsnap as
             [[Howner_map [_ [Howner_prio [_ [_ [_ _]]]]]] _];
           pose proof (Htasks_valid tid t Howner_map) as [Howner_valid _];
           unfold valid_task_prio in Howner_valid
       end.
  all: match goal with
       | Hsg : valid_stable_glob_vars ?sg |- _ =>
           unfold valid_stable_glob_vars in Hsg;
           destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]]
       end.
  all: match goal with
       | Howner_prio : ?prio = ?tprio,
         Hgt : ?prio > unsigned_last_nbits (Z.shiftr ?ecnt 8) 8 |- _ =>
           rewrite Howner_prio in Hgt
       end.
  all: match goal with
       | Hidx : ?pcp_idx = decode_PCP_from_cnt ?ecnt |- _ =>
           subst pcp_idx; unfold decode_PCP_from_cnt
       end.
  all: match goal with
       | |- context [unsigned_last_nbits (Z.shiftr ?ecnt 8) 8] =>
           pose proof
             (unsigned_Lastnbits_range (Z.shiftr ecnt 8) 8 ltac:(lia))
             as Hpcp
       end.
  all: try reflexivity; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_138_pure : OSMutexPend_full_partial_solve_wit_138_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl at 1.
  Intros_p Htask_valid.
  split_pures.
  all: dump_pre_spatial.
  all: unfold task_vaild_cond_prop in Htask_valid.
  all: destruct Htask_valid as [_ Htasks_valid].
  all: match goal with
       | Hsnap : task_inherit_snapshot_of_prop ?sg ?st ?tid ?t
                   ?tcb ?prio ?x ?y ?bitx ?bity ?eventptr |- _ =>
           unfold task_inherit_snapshot_of_prop,
             task_rdy_snapshot_of_prop in Hsnap;
           destruct Hsnap as
             [[Howner_map [_ [Howner_prio [_ [_ [_ _]]]]]] _];
           pose proof (Htasks_valid tid t Howner_map) as [Howner_valid _];
           unfold valid_task_prio in Howner_valid
       end.
  all: match goal with
       | Hsg : valid_stable_glob_vars ?sg |- _ =>
           unfold valid_stable_glob_vars in Hsg;
           destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]]
       end.
  all: match goal with
       | Howner_prio : ?prio = ?tprio,
         Hgt : ?prio > unsigned_last_nbits (Z.shiftr ?ecnt 8) 8 |- _ =>
           rewrite Howner_prio in Hgt
       end.
  all: match goal with
       | Hidx : ?pcp_idx = decode_PCP_from_cnt ?ecnt |- _ =>
           subst pcp_idx; unfold decode_PCP_from_cnt
       end.
  all: match goal with
       | |- context [unsigned_last_nbits (Z.shiftr ?ecnt 8) 8] =>
           pose proof
             (unsigned_Lastnbits_range (Z.shiftr ecnt 8) 8 ltac:(lia))
             as Hpcp
       end.
  all: try reflexivity; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_139_pure : OSMutexPend_full_partial_solve_wit_139_pure.
Proof. pre_process. Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_140_pure : OSMutexPend_full_partial_solve_wit_140_pure.
Proof.
  pre_process.
  match goal with
  | Hrel : crit_rel_no_os_state_change ?ls0 ?ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  unfold interrupt_inv, store_int_state at 1.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  split_pures.
  all: dump_pre_spatial.
  all: match goal with
       | Hiseq : ?isr = intNesting (IntrState ?ls) |- _ =>
           rewrite <- Hiseq in Hisr_range
       end.
  all: match goal with
       | Hlockeq : ?lock = lockNesting (IntrState ?ls) |- _ =>
           rewrite <- Hlockeq in Hlock_range
       end.
  all: change (0 <= isr <= 255) in Hisr_range.
  all: change (0 <= lock <= 255) in Hlock_range.
  all: repeat match goal with
       | Hcast : unsigned_last_nbits ?x 32 <= 0 |- _ =>
           rewrite (unsigned_last_nbits_eq x 32) in Hcast by lia
       end.
  all: lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_141_pure : OSMutexPend_full_partial_solve_wit_141_pure.
Proof.
  pre_process.
  match goal with
  | Hrel : crit_rel_no_os_state_change ?ls0 ?ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  unfold interrupt_inv, store_int_state at 1.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  split_pures.
  all: dump_pre_spatial.
  all: match goal with
       | Hiseq : ?isr = intNesting (IntrState ?ls) |- _ =>
           rewrite <- Hiseq in Hisr_range
       end.
  all: match goal with
       | Hlockeq : ?lock = lockNesting (IntrState ?ls) |- _ =>
           rewrite <- Hlockeq in Hlock_range
       end.
  all: change (0 <= isr <= 255) in Hisr_range.
  all: change (0 <= lock <= 255) in Hlock_range.
  all: repeat match goal with
       | Hcast : unsigned_last_nbits ?x 32 <= 0 |- _ =>
           rewrite (unsigned_last_nbits_eq x 32) in Hcast by lia
       end.
  all: lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_142_pure : OSMutexPend_full_partial_solve_wit_142_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl at 1.
  Intros_p Htask_valid.
  split_pures.
  all: dump_pre_spatial.
  all: unfold task_vaild_cond_prop in Htask_valid.
  all: destruct Htask_valid as [_ Htasks_valid].
  all: match goal with
       | Hsnap : task_inherit_snapshot_of_prop ?sg ?st ?tid ?t
                   ?tcb ?prio ?x ?y ?bitx ?bity ?eventptr |- _ =>
           unfold task_inherit_snapshot_of_prop,
             task_rdy_snapshot_of_prop in Hsnap;
           destruct Hsnap as
             [[Howner_map [_ [Howner_prio [_ [_ [_ _]]]]]] _];
           pose proof (Htasks_valid tid t Howner_map) as [Howner_valid _];
           unfold valid_task_prio in Howner_valid
       end.
  all: match goal with
       | Hsg : valid_stable_glob_vars ?sg |- _ =>
           unfold valid_stable_glob_vars in Hsg;
           destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]]
       end.
  all: match goal with
       | Howner_prio : ?prio = ?tprio,
         Hgt : ?prio > unsigned_last_nbits (Z.shiftr ?ecnt 8) 8 |- _ =>
           rewrite Howner_prio in Hgt
       end.
  all: match goal with
       | Hidx : ?pcp_idx = decode_PCP_from_cnt ?ecnt |- _ =>
           subst pcp_idx; unfold decode_PCP_from_cnt
       end.
  all: match goal with
       | |- context [unsigned_last_nbits (Z.shiftr ?ecnt 8) 8] =>
           pose proof
             (unsigned_Lastnbits_range (Z.shiftr ecnt 8) 8 ltac:(lia))
             as Hpcp
       end.
  all: try reflexivity; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_143_pure : OSMutexPend_full_partial_solve_wit_143_pure.
Proof. pre_process. Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_144_pure : OSMutexPend_full_partial_solve_wit_144_pure.
Proof. pre_process. Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_145_pure : OSMutexPend_full_partial_solve_wit_145_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl at 1.
  Intros_p Htask_valid.
  split_pures.
  all: dump_pre_spatial.
  all: unfold task_vaild_cond_prop in Htask_valid.
  all: destruct Htask_valid as [_ Htasks_valid].
  all: match goal with
       | Hsnap : task_inherit_snapshot_of_prop ?sg ?st ?tid ?t
                   ?tcb ?prio ?x ?y ?bitx ?bity ?eventptr |- _ =>
           unfold task_inherit_snapshot_of_prop,
             task_rdy_snapshot_of_prop in Hsnap;
           destruct Hsnap as
             [[Howner_map [_ [Howner_prio [_ [_ [_ _]]]]]] _];
           pose proof (Htasks_valid tid t Howner_map) as [Howner_valid _];
           unfold valid_task_prio in Howner_valid
       end.
  all: match goal with
       | Hsg : valid_stable_glob_vars ?sg |- _ =>
           unfold valid_stable_glob_vars in Hsg;
           destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]]
       end.
  all: match goal with
       | Howner_prio : ?prio = ?tprio,
         Hgt : ?prio > unsigned_last_nbits (Z.shiftr ?ecnt 8) 8 |- _ =>
           rewrite Howner_prio in Hgt
       end.
  all: match goal with
       | Hidx : ?pcp_idx = decode_PCP_from_cnt ?ecnt |- _ =>
           subst pcp_idx; unfold decode_PCP_from_cnt
       end.
  all: match goal with
       | |- context [unsigned_last_nbits (Z.shiftr ?ecnt 8) 8] =>
           pose proof
             (unsigned_Lastnbits_range (Z.shiftr ecnt 8) 8 ltac:(lia))
             as Hpcp
       end.
  all: try reflexivity; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_146_pure : OSMutexPend_full_partial_solve_wit_146_pure.
Proof.
  pre_process.
  match goal with
  | Hrel : crit_rel_no_os_state_change ?ls0 ?ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  unfold interrupt_inv, store_int_state at 1.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  split_pures.
  all: dump_pre_spatial.
  all: match goal with
       | Hiseq : ?isr = intNesting (IntrState ?ls) |- _ =>
           rewrite <- Hiseq in Hisr_range
       end.
  all: match goal with
       | Hlockeq : ?lock = lockNesting (IntrState ?ls) |- _ =>
           rewrite <- Hlockeq in Hlock_range
       end.
  all: change (0 <= isr <= 255) in Hisr_range.
  all: change (0 <= lock <= 255) in Hlock_range.
  all: repeat match goal with
       | Hcast : unsigned_last_nbits ?x 32 <= 0 |- _ =>
           rewrite (unsigned_last_nbits_eq x 32) in Hcast by lia
       end.
  all: lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_147_pure : OSMutexPend_full_partial_solve_wit_147_pure.
Proof.
  pre_process.
  match goal with
  | Hrel : crit_rel_no_os_state_change ?ls0 ?ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  unfold interrupt_inv, store_int_state at 1.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  split_pures.
  all: dump_pre_spatial.
  all: match goal with
       | Hiseq : ?isr = intNesting (IntrState ?ls) |- _ =>
           rewrite <- Hiseq in Hisr_range
       end.
  all: match goal with
       | Hlockeq : ?lock = lockNesting (IntrState ?ls) |- _ =>
           rewrite <- Hlockeq in Hlock_range
       end.
  all: change (0 <= isr <= 255) in Hisr_range.
  all: change (0 <= lock <= 255) in Hlock_range.
  all: repeat match goal with
       | Hcast : unsigned_last_nbits ?x 32 <= 0 |- _ =>
           rewrite (unsigned_last_nbits_eq x 32) in Hcast by lia
       end.
  all: lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_148_pure : OSMutexPend_full_partial_solve_wit_148_pure.
Proof.
  pre_process.
  match goal with
  | Hrel : crit_rel_no_os_state_change ?ls0 ?ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  unfold interrupt_inv, store_int_state at 1.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  split_pures.
  all: dump_pre_spatial.
  all: match goal with
       | Hiseq : ?isr = intNesting (IntrState ?ls) |- _ =>
           rewrite <- Hiseq in Hisr_range
       end.
  all: match goal with
       | Hlockeq : ?lock = lockNesting (IntrState ?ls) |- _ =>
           rewrite <- Hlockeq in Hlock_range
       end.
  all: change (0 <= isr <= 255) in Hisr_range.
  all: change (0 <= lock <= 255) in Hlock_range.
  all: repeat match goal with
       | Hcast : unsigned_last_nbits ?x 32 <= 0 |- _ =>
           rewrite (unsigned_last_nbits_eq x 32) in Hcast by lia
       end.
  all: lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_149_pure : OSMutexPend_full_partial_solve_wit_149_pure.
Proof.
  pre_process.
  match goal with
  | Hrel : crit_rel_no_os_state_change ?ls0 ?ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel; subst ls1
  end.
  unfold interrupt_inv, store_int_state at 1.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  split_pures.
  all: dump_pre_spatial.
  all: match goal with
       | Hiseq : ?isr = intNesting (IntrState ?ls) |- _ =>
           rewrite <- Hiseq in Hisr_range
       end.
  all: match goal with
       | Hlockeq : ?lock = lockNesting (IntrState ?ls) |- _ =>
           rewrite <- Hlockeq in Hlock_range
       end.
  all: change (0 <= isr <= 255) in Hisr_range.
  all: change (0 <= lock <= 255) in Hlock_range.
  all: repeat match goal with
       | Hcast : unsigned_last_nbits ?x 32 <= 0 |- _ =>
           rewrite (unsigned_last_nbits_eq x 32) in Hcast by lia
       end.
  all: lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_150_pure : OSMutexPend_full_partial_solve_wit_150_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl at 1.
  Intros_p Htask_valid.
  split_pures.
  all: dump_pre_spatial.
  all: unfold task_vaild_cond_prop in Htask_valid.
  all: destruct Htask_valid as [_ Htasks_valid].
  all: match goal with
       | Hsnap : task_inherit_snapshot_of_prop ?sg ?st ?tid ?t
                   ?tcb ?prio ?x ?y ?bitx ?bity ?eventptr |- _ =>
           unfold task_inherit_snapshot_of_prop,
             task_rdy_snapshot_of_prop in Hsnap;
           destruct Hsnap as
             [[Howner_map [_ [Howner_prio [_ [_ [_ _]]]]]] _];
           pose proof (Htasks_valid tid t Howner_map) as [Howner_valid _];
           unfold valid_task_prio in Howner_valid
       end.
  all: match goal with
       | Hsg : valid_stable_glob_vars ?sg |- _ =>
           unfold valid_stable_glob_vars in Hsg;
           destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]]
       end.
  all: match goal with
       | Howner_prio : ?prio = ?tprio,
         Hgt : ?prio > unsigned_last_nbits (Z.shiftr ?ecnt 8) 8 |- _ =>
           rewrite Howner_prio in Hgt
       end.
  all: match goal with
       | Hidx : ?pcp_idx = decode_PCP_from_cnt ?ecnt |- _ =>
           subst pcp_idx; unfold decode_PCP_from_cnt
       end.
  all: match goal with
       | |- context [unsigned_last_nbits (Z.shiftr ?ecnt 8) 8] =>
           pose proof
             (unsigned_Lastnbits_range (Z.shiftr ecnt 8) 8 ltac:(lia))
             as Hpcp
       end.
  all: try reflexivity; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_151_pure : OSMutexPend_full_partial_solve_wit_151_pure.
Proof.
  pre_process.
  unfold task_inv_no_two_tids_priotbl at 1.
  Intros_p Htask_valid.
  split_pures.
  all: dump_pre_spatial.
  all: unfold task_vaild_cond_prop in Htask_valid.
  all: destruct Htask_valid as [_ Htasks_valid].
  all: match goal with
       | Hsnap : task_inherit_snapshot_of_prop ?sg ?st ?tid ?t
                   ?tcb ?prio ?x ?y ?bitx ?bity ?eventptr |- _ =>
           unfold task_inherit_snapshot_of_prop,
             task_rdy_snapshot_of_prop in Hsnap;
           destruct Hsnap as
             [[Howner_map [_ [Howner_prio [_ [_ [_ _]]]]]] _];
           pose proof (Htasks_valid tid t Howner_map) as [Howner_valid _];
           unfold valid_task_prio in Howner_valid
       end.
  all: match goal with
       | Hsg : valid_stable_glob_vars ?sg |- _ =>
           unfold valid_stable_glob_vars in Hsg;
           destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]]
       end.
  all: match goal with
       | Howner_prio : ?prio = ?tprio,
         Hgt : ?prio > unsigned_last_nbits (Z.shiftr ?ecnt 8) 8 |- _ =>
           rewrite Howner_prio in Hgt
       end.
  all: match goal with
       | Hidx : ?pcp_idx = decode_PCP_from_cnt ?ecnt |- _ =>
           subst pcp_idx; unfold decode_PCP_from_cnt
       end.
  all: match goal with
       | |- context [unsigned_last_nbits (Z.shiftr ?ecnt 8) 8] =>
           pose proof
             (unsigned_Lastnbits_range (Z.shiftr ecnt 8) 8 ltac:(lia))
             as Hpcp
       end.
  all: try reflexivity; lia.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_152_pure : OSMutexPend_full_partial_solve_wit_152_pure.
Proof. pre_process. Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_153_pure : OSMutexPend_full_partial_solve_wit_153_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_154_pure : OSMutexPend_full_partial_solve_wit_154_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_155_pure : OSMutexPend_full_partial_solve_wit_155_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_156_pure : OSMutexPend_full_partial_solve_wit_156_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_157_pure : OSMutexPend_full_partial_solve_wit_157_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_158_pure : OSMutexPend_full_partial_solve_wit_158_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_159_pure : OSMutexPend_full_partial_solve_wit_159_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_160_pure : OSMutexPend_full_partial_solve_wit_160_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_161_pure : OSMutexPend_full_partial_solve_wit_161_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_162_pure : OSMutexPend_full_partial_solve_wit_162_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_163_pure : OSMutexPend_full_partial_solve_wit_163_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_164_pure : OSMutexPend_full_partial_solve_wit_164_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_165_pure : OSMutexPend_full_partial_solve_wit_165_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_166_pure : OSMutexPend_full_partial_solve_wit_166_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_167_pure : OSMutexPend_full_partial_solve_wit_167_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_168_pure : OSMutexPend_full_partial_solve_wit_168_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_169_pure : OSMutexPend_full_partial_solve_wit_169_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_170_pure : OSMutexPend_full_partial_solve_wit_170_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_171_pure : OSMutexPend_full_partial_solve_wit_171_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_172_pure : OSMutexPend_full_partial_solve_wit_172_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_173_pure : OSMutexPend_full_partial_solve_wit_173_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_174_pure : OSMutexPend_full_partial_solve_wit_174_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_175_pure : OSMutexPend_full_partial_solve_wit_175_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_176_pure : OSMutexPend_full_partial_solve_wit_176_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_177_pure : OSMutexPend_full_partial_solve_wit_177_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_178_pure : OSMutexPend_full_partial_solve_wit_178_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_179_pure : OSMutexPend_full_partial_solve_wit_179_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_180_pure : OSMutexPend_full_partial_solve_wit_180_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_181_pure : OSMutexPend_full_partial_solve_wit_181_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_182_pure : OSMutexPend_full_partial_solve_wit_182_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_183_pure : OSMutexPend_full_partial_solve_wit_183_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_184_pure : OSMutexPend_full_partial_solve_wit_184_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_185_pure : OSMutexPend_full_partial_solve_wit_185_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_186_pure : OSMutexPend_full_partial_solve_wit_186_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_187_pure : OSMutexPend_full_partial_solve_wit_187_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_188_pure : OSMutexPend_full_partial_solve_wit_188_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_189_pure : OSMutexPend_full_partial_solve_wit_189_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_190_pure : OSMutexPend_full_partial_solve_wit_190_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_191_pure : OSMutexPend_full_partial_solve_wit_191_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_192_pure : OSMutexPend_full_partial_solve_wit_192_pure.
Proof.
  pre_process;
  try (
    unfold interrupt_inv, store_int_state;
    Intros_p Hint_range;
    prop_apply_p (store_uchar_range sg.(g_OSIntNesting)
      (ls1.(IntrState).(intNesting)));
    Intros_p Hint_int_byte_range;
    prop_apply_p (store_uchar_range sg.(g_OSLockNesting)
      (ls1.(IntrState).(lockNesting)));
    Intros_p Hint_lock_byte_range;
    entailer!;
    unfold crit_rel_no_os_state_change in *;
    subst ls1;
    change (0 <= ls0.(IntrState).(intNesting) <= 255)
      in Hint_int_byte_range;
    change (0 <= ls0.(IntrState).(lockNesting) <= 255)
      in Hint_lock_byte_range;
    repeat match goal with
    | Hbits : unsigned_last_nbits ?x 32 <= 0 |- _ =>
        rewrite (unsigned_last_nbits_eq x 32) in Hbits by lia
    end;
    lia
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_193_pure : OSMutexPend_full_partial_solve_wit_193_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_194_pure : OSMutexPend_full_partial_solve_wit_194_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_195_pure : OSMutexPend_full_partial_solve_wit_195_pure.
Proof.
  pre_process;
  try (
    unfold task_mutex_full_snapshot_of_prop,
      task_mutex_pend_entry_prop,
      encode_task_status, encode_pend_type in *;
    entailer!;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    subst;
    repeat match goal with
    | Hnone : pendType (stat ?t) = None |- _ => rewrite Hnone
    | Hsusp : isSuspended (stat ?t) = false |- _ => rewrite Hsusp
    end;
    reflexivity
  ).
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_196_pure : OSMutexPend_full_partial_solve_wit_196_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_197_pure : OSMutexPend_full_partial_solve_wit_197_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_198_pure : OSMutexPend_full_partial_solve_wit_198_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_199_pure : OSMutexPend_full_partial_solve_wit_199_pure.
Proof.
  pre_process.
  subst lock.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hlock_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_200_pure : OSMutexPend_full_partial_solve_wit_200_pure.
Proof.
  pre_process.
  subst isr.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hisr_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_201_pure : OSMutexPend_full_partial_solve_wit_201_pure.
Proof.
  pre_process.
  subst isr.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hisr_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_202_pure : OSMutexPend_full_partial_solve_wit_202_pure.
Proof.
  pre_process.
  subst lock.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hlock_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_203_pure : OSMutexPend_full_partial_solve_wit_203_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_204_pure : OSMutexPend_full_partial_solve_wit_204_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_205_pure : OSMutexPend_full_partial_solve_wit_205_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_206_pure : OSMutexPend_full_partial_solve_wit_206_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_207_pure : OSMutexPend_full_partial_solve_wit_207_pure.
Proof.
  pre_process.
  subst lock.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hlock_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_208_pure : OSMutexPend_full_partial_solve_wit_208_pure.
Proof.
  pre_process.
  subst isr.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hisr_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_209_pure : OSMutexPend_full_partial_solve_wit_209_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_210_pure : OSMutexPend_full_partial_solve_wit_210_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_211_pure : OSMutexPend_full_partial_solve_wit_211_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_212_pure : OSMutexPend_full_partial_solve_wit_212_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_213_pure : OSMutexPend_full_partial_solve_wit_213_pure.
Proof.
  pre_process.
  subst lock.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hlock_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_214_pure : OSMutexPend_full_partial_solve_wit_214_pure.
Proof.
  pre_process.
  subst isr.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hisr_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_215_pure : OSMutexPend_full_partial_solve_wit_215_pure.
Proof.
  pre_process.
  subst isr.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hisr_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_216_pure : OSMutexPend_full_partial_solve_wit_216_pure.
Proof.
  pre_process.
  subst lock.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hlock_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_217_pure : OSMutexPend_full_partial_solve_wit_217_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_218_pure : OSMutexPend_full_partial_solve_wit_218_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_219_pure : OSMutexPend_full_partial_solve_wit_219_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_220_pure : OSMutexPend_full_partial_solve_wit_220_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_221_pure : OSMutexPend_full_partial_solve_wit_221_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_222_pure : OSMutexPend_full_partial_solve_wit_222_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_223_pure : OSMutexPend_full_partial_solve_wit_223_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_224_pure : OSMutexPend_full_partial_solve_wit_224_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_225_pure : OSMutexPend_full_partial_solve_wit_225_pure.
Proof.
  pre_process.
  subst lock.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hlock_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_226_pure : OSMutexPend_full_partial_solve_wit_226_pure.
Proof.
  pre_process.
  subst isr.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hisr_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_227_pure : OSMutexPend_full_partial_solve_wit_227_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_228_pure : OSMutexPend_full_partial_solve_wit_228_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_229_pure : OSMutexPend_full_partial_solve_wit_229_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_230_pure : OSMutexPend_full_partial_solve_wit_230_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_231_pure : OSMutexPend_full_partial_solve_wit_231_pure.
Proof.
  pre_process.
  subst lock.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hlock_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_232_pure : OSMutexPend_full_partial_solve_wit_232_pure.
Proof.
  pre_process.
  subst isr.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hisr_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_233_pure : OSMutexPend_full_partial_solve_wit_233_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_234_pure : OSMutexPend_full_partial_solve_wit_234_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_235_pure : OSMutexPend_full_partial_solve_wit_235_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_236_pure : OSMutexPend_full_partial_solve_wit_236_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_partial_solve_wit_237_pure : OSMutexPend_full_partial_solve_wit_237_pure.
Proof.
  pre_process.
  subst lock.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState ls0))).
  Intros_p Hlock_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hlock_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (lockNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_partial_solve_wit_238_pure : OSMutexPend_full_partial_solve_wit_238_pure.
Proof.
  pre_process.
  subst isr.
  match goal with
  | Hsame : crit_rel_no_os_state_change ?ls_in ?ls_out |- _ =>
      unfold crit_rel_no_os_state_change in Hsame;
      subst ls_out
  end.
  unfold interrupt_inv, interrupt_in_range, store_int_state.
  Intros_p Hintr_range.
  prop_apply_p
    (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState ls0))).
  Intros_p Hisr_range.
  exfalso.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hisr_range by reflexivity.
  match goal with
  | Hmod : unsigned_last_nbits (intNesting (IntrState ls0)) 32 <= 0 |- _ =>
      rewrite unsigned_last_nbits_eq in Hmod by lia;
      lia
  end.
Qed.

Lemma proof_of_OSMutexPend_full_which_implies_wit_1 : OSMutexPend_full_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_which_implies_wit_2 : OSMutexPend_full_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_which_implies_wit_3 : OSMutexPend_full_which_implies_wit_3.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_which_implies_wit_4 : OSMutexPend_full_which_implies_wit_4.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_which_implies_wit_5 : OSMutexPend_full_which_implies_wit_5.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_which_implies_wit_6 : OSMutexPend_full_which_implies_wit_6.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_which_implies_wit_7 : OSMutexPend_full_which_implies_wit_7.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_which_implies_wit_8 : OSMutexPend_full_which_implies_wit_8.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_which_implies_wit_9 : OSMutexPend_full_which_implies_wit_9.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_which_implies_wit_10 : OSMutexPend_full_which_implies_wit_10.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_which_implies_wit_11 : OSMutexPend_full_which_implies_wit_11.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_full_which_implies_wit_12 : OSMutexPend_full_which_implies_wit_12.
Proof. Admitted. 
