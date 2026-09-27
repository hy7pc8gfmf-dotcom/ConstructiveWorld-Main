(* ==========================================================================)
   UpReqLogRDF —— lrdf_req_minus_unfold / lrdf_inv_le_of_one_le_mul / lrdf_mult_opp_r 语句面；同域语句面
   使命：本件形式化lrdf_req_minus_unfold / lrdf_inv_le_of_one_le_mul / lrdf_mult_opp_r 语句面。
   本件并载：严格恒等式 2 的复合重建件；QltT / QltT / Qlt_to_QltT 语句面；C1 LogZWall 第四面墙定理化；件位 CZB12（组 E-STAGING-CZB12）。
   依赖：S01_BaseRing, S02_CauchyComplete, S03_QExp, S04_RealExpLogConv, S05_AlignmentGRPO, S06_DiffSamplingGibbs, S07_RealSetoidExpLog, S08_RealMainlineDPO
     S09_EntropyReal, S10_KVQuantTrig, S11_TP3B5, S12_B5RecycleSF, S13_NLiveAudit, S14_B5BatchBlock, S15_TailFEPUp, UpRealLeB,
     G05_LogSmall, UpReqLogCompD, UpReqAlgebra, List, UpReqSLM, UpReqRDF, Setoid, Morphisms,
     Lia, QArith.Qminmax, QArith.QArith, QArith.Qabs, Lqa, UpReqGeomD, UpReqLpoEquiv, UpReqEnvelopeDual,
     UpReqConstEnvelope, UpReqDyadicLog, Arith.PeanoNat。
   构造性：零公理、零承认式语句；语句面 Set 层承载，Print Assumptions 全 Closed。
   编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

(* ============================ §1 严格恒等式 2 的复合重建件 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpRealLeB.
Require Import G05_LogSmall.
Require Import G05_LogSmall.
Require Import UpReqLogCompD.
Require Import UpReqAlgebra.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Part 0：置换助件（泛型 RIS；纯 req 代数，零供给前提）                         *)
(* ============================================================ *)

Section LogcAlg2.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* P1：中项换位 (a+b)+c ≡ (a+c)+b *)
Lemma logc2_plus_swap_mid : forall a b c : R,
  req (plus (plus a b) c) (plus (plus a c) b).
Proof.
  intros a b c.
  apply (req_trans (plus (plus a b) c) (plus a (plus b c)) (plus (plus a c) b)).
  - exact (req_sym (plus a (plus b c)) (plus (plus a b) c) (plus_assoc a b c)).
  - apply (req_trans (plus a (plus b c)) (plus a (plus c b)) (plus (plus a c) b)).
    + apply (req_plus_compat a a (plus b c) (plus c b)).
      * apply req_refl.
      * exact (plus_comm b c).
    + exact (plus_assoc a c b).
Qed.

(* P2：四项交叉置换 ((a+b)+(c+d)) ≡ ((a+c)+(b+d)) *)
Lemma logc2_plus_exchange : forall a b c d : R,
  req (plus (plus a b) (plus c d)) (plus (plus a c) (plus b d)).
Proof.
  intros a b c d.
  apply (req_trans (plus (plus a b) (plus c d))
                   (plus a (plus b (plus c d)))
                   (plus (plus a c) (plus b d))).
  - exact (req_sym (plus a (plus b (plus c d))) (plus (plus a b) (plus c d))
             (plus_assoc a b (plus c d))).
  - apply (req_trans (plus a (plus b (plus c d)))
                     (plus a (plus (plus b c) d))
                     (plus (plus a c) (plus b d))).
    + apply (req_plus_compat a a (plus b (plus c d)) (plus (plus b c) d)).
      * apply req_refl.
      * exact (plus_assoc b c d).
    + apply (req_trans (plus a (plus (plus b c) d))
                       (plus a (plus (plus c b) d))
                       (plus (plus a c) (plus b d))).
      * apply (req_plus_compat a a (plus (plus b c) d) (plus (plus c b) d)).
        -- apply req_refl.
        -- apply (req_plus_compat (plus b c) (plus c b) d d
                     (plus_comm b c) (req_refl d)).
      * apply (req_trans (plus a (plus (plus c b) d))
                         (plus a (plus c (plus b d)))
                         (plus (plus a c) (plus b d))).
        -- apply (req_plus_compat a a (plus (plus c b) d) (plus c (plus b d))).
           ++ apply req_refl.
           ++ exact (req_sym (plus c (plus b d)) (plus (plus c b) d)
                       (plus_assoc c b d)).
        -- exact (plus_assoc a c (plus b d)).
Qed.

(* P3：对消零件 (x-y)+(y-x) ≡ 0（logZ 双抵消核） *)
Lemma logc2_logpair_zero : forall x y : R,
  req (plus (plus x (opp y)) (plus y (opp x))) zero.
Proof.
  intros x y.
  apply (req_trans (plus (plus x (opp y)) (plus y (opp x)))
                   (plus x (plus (opp y) (plus y (opp x)))) zero).
  - exact (req_sym (plus x (plus (opp y) (plus y (opp x))))
             (plus (plus x (opp y)) (plus y (opp x)))
             (plus_assoc x (opp y) (plus y (opp x)))).
  - apply (req_trans (plus x (plus (opp y) (plus y (opp x))))
                     (plus x (opp x)) zero).
    + apply (req_plus_compat x x (plus (opp y) (plus y (opp x))) (opp x)).
      * apply req_refl.
      * apply (req_trans (plus (opp y) (plus y (opp x)))
                         (plus (plus (opp y) y) (opp x)) (opp x)).
        -- exact (plus_assoc (opp y) y (opp x)).
        -- apply (req_trans (plus (plus (opp y) y) (opp x))
                            (plus zero (opp x)) (opp x)).
           ++ apply (req_plus_compat (plus (opp y) y) zero (opp x) (opp x)).
              ** exact (req_trans (plus (opp y) y) (plus y (opp y)) zero
                                    (plus_comm (opp y) y) (plus_opp y)).
              ** apply req_refl.
           ++ exact (logd_req_plus_zero_l R RIS (opp x)).
    + exact (plus_opp x).
Qed.

End LogcAlg2.

(* ============================================================ *)
(* Part 1：温度节（供给前提与 UpReqLogCompD LogcTemp 节同位，零新增）            *)
(* ============================================================ *)

Section LogcTemp2.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

Variable sumf : (S -> R) -> R.
Hypothesis tsum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis tsum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis tsum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).

Variable energy : S -> R.
Variable Z_temp : R -> R.
(* req_Z_temp_spec 前提（UpFirewallReq 同位） *)
Hypothesis zt_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (energy s)))).
(* zt_pos 前提 = UpReqTempEntropy req_Z_temp_pos 产物位 *)
Hypothesis zt_pos : forall (t : R) (Ht : lt zero t), lt zero (Z_temp t).
(* B1/B2 供给前提（同 UpReqLogCompD LogcTemp） *)
Hypothesis tsup_compat : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Hypothesis tsup_log_exp_neg : forall u : R,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).


Lemma logc2_opp_h_temp : forall (t : R) (Ht : lt zero t),
  req (opp (logc_t_h S sumf energy Z_temp zt_pos t Ht))
      (plus (opp (mult (inv_pos t Ht) (logc_t_et S sumf energy Z_temp zt_pos t Ht)))
            (opp (log (Z_temp t) (zt_pos t Ht)))).
Proof.
  intros t Ht.
  apply (req_trans (opp (logc_t_h S sumf energy Z_temp zt_pos t Ht))
                   (opp (plus (mult (inv_pos t Ht)
                                       (logc_t_et S sumf energy Z_temp zt_pos t Ht))
                              (log (Z_temp t) (zt_pos t Ht))))
                   (plus (opp (mult (inv_pos t Ht)
                                        (logc_t_et S sumf energy Z_temp zt_pos t Ht)))
                         (opp (log (Z_temp t) (zt_pos t Ht))))).
  - apply req_opp_compat.
    exact (logc_entropy_temp_explicit S sumf tsum_ext tsum_add tsum_linear
             energy Z_temp zt_spec zt_pos tsup_compat tsup_log_exp_neg t Ht).
  - exact (logc_opp_plus (mult (inv_pos t Ht)
                                 (logc_t_et S sumf energy Z_temp zt_pos t Ht))
            (log (Z_temp t) (zt_pos t Ht))).
Qed.

(* Q2【T6 例一 + T5 换形 + 置换】：                                           *)

Lemma logc2_kl21_temp_swap :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (logc_t_kl S sumf energy Z_temp zt_pos t2 t1 Ht2 Ht1)
      (plus (plus (mult (inv_pos t1 Ht1)
                        (logc_t_et S sumf energy Z_temp zt_pos t2 Ht2))
                  (opp (mult (inv_pos t2 Ht2)
                             (logc_t_et S sumf energy Z_temp zt_pos t2 Ht2))))
            (plus (log (Z_temp t1) (zt_pos t1 Ht1))
                  (opp (log (Z_temp t2) (zt_pos t2 Ht2))))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (A := inv_pos t1 Ht1).
  set (B := inv_pos t2 Ht2).
  set (E2 := logc_t_et S sumf energy Z_temp zt_pos t2 Ht2).
  set (L1 := log (Z_temp t1) (zt_pos t1 Ht1)).
  set (L2 := log (Z_temp t2) (zt_pos t2 Ht2)).
  set (Hh2 := logc_t_h S sumf energy Z_temp zt_pos t2 Ht2).
  apply (req_trans (logc_t_kl S sumf energy Z_temp zt_pos t2 t1 Ht2 Ht1)
                   (plus (plus (opp Hh2) (mult A E2)) L1)
                   (plus (plus (mult A E2) (opp (mult B E2)))
                         (plus L1 (opp L2)))).
  - 
    exact (logc_relative_entropy_temp_decomp S sumf tsum_ext tsum_add tsum_linear
              energy Z_temp zt_spec zt_pos tsup_compat tsup_log_exp_neg
              t1 Ht1 t2 Ht2).
  - 
    apply (req_trans (plus (plus (opp Hh2) (mult A E2)) L1)
                     (plus (plus (plus (opp (mult B E2)) (opp L2)) (mult A E2)) L1)
                     (plus (plus (mult A E2) (opp (mult B E2)))
                           (plus L1 (opp L2)))).
    + apply (req_plus_compat (plus (opp Hh2) (mult A E2))
                (plus (plus (opp (mult B E2)) (opp L2)) (mult A E2)) L1 L1).
      * apply (req_plus_compat (opp Hh2) (plus (opp (mult B E2)) (opp L2))
                  (mult A E2) (mult A E2)).
        -- exact (logc2_opp_h_temp t2 Ht2).
        -- apply req_refl.
      * apply req_refl.
    + apply (req_trans (plus (plus (plus (opp (mult B E2)) (opp L2)) (mult A E2)) L1)
                       (plus (plus (plus (opp (mult B E2)) (mult A E2)) (opp L2)) L1)
                       (plus (plus (mult A E2) (opp (mult B E2)))
                             (plus L1 (opp L2)))).
      * apply (req_plus_compat (plus (plus (opp (mult B E2)) (opp L2)) (mult A E2))
                  (plus (plus (opp (mult B E2)) (mult A E2)) (opp L2)) L1 L1).
        -- exact (logc2_plus_swap_mid (opp (mult B E2)) (opp L2) (mult A E2)).
        -- apply req_refl.
      * apply (req_trans (plus (plus (plus (opp (mult B E2)) (mult A E2)) (opp L2)) L1)
                         (plus (plus (opp (mult B E2)) (mult A E2)) (plus (opp L2) L1))
                         (plus (plus (mult A E2) (opp (mult B E2)))
                               (plus L1 (opp L2)))).
        -- exact (req_sym (plus (plus (opp (mult B E2)) (mult A E2))
                                   (plus (opp L2) L1))
                             (plus (plus (plus (opp (mult B E2)) (mult A E2))
                                        (opp L2)) L1)
                             (plus_assoc (plus (opp (mult B E2)) (mult A E2))
                               (opp L2) L1)).
        -- apply (req_trans (plus (plus (opp (mult B E2)) (mult A E2))
                                   (plus (opp L2) L1))
                            (plus (plus (mult A E2) (opp (mult B E2)))
                                  (plus (opp L2) L1))
                            (plus (plus (mult A E2) (opp (mult B E2)))
                                  (plus L1 (opp L2)))).
           ++ apply (req_plus_compat (plus (opp (mult B E2)) (mult A E2))
                        (plus (mult A E2) (opp (mult B E2)))
                        (plus (opp L2) L1) (plus (opp L2) L1)).
              ** exact (plus_comm (opp (mult B E2)) (mult A E2)).
              ** apply req_refl.
           ++ apply (req_plus_compat (plus (mult A E2) (opp (mult B E2)))
                        (plus (mult A E2) (opp (mult B E2)))
                        (plus (opp L2) L1) (plus L1 (opp L2))).
              ** apply req_refl.
              ** exact (plus_comm (opp L2) L1).
Qed.

(* Q3【T6 例二 + T5 换形 + 置换】：                                           *)

Lemma logc2_kl12_temp_swap :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (logc_t_kl S sumf energy Z_temp zt_pos t1 t2 Ht1 Ht2)
      (plus (plus (mult (inv_pos t2 Ht2)
                        (logc_t_et S sumf energy Z_temp zt_pos t1 Ht1))
                  (opp (mult (inv_pos t1 Ht1)
                             (logc_t_et S sumf energy Z_temp zt_pos t1 Ht1))))
            (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                  (opp (log (Z_temp t1) (zt_pos t1 Ht1))))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (A := inv_pos t1 Ht1).
  set (B := inv_pos t2 Ht2).
  set (E1 := logc_t_et S sumf energy Z_temp zt_pos t1 Ht1).
  set (L1 := log (Z_temp t1) (zt_pos t1 Ht1)).
  set (L2 := log (Z_temp t2) (zt_pos t2 Ht2)).
  set (Hh1 := logc_t_h S sumf energy Z_temp zt_pos t1 Ht1).
  apply (req_trans (logc_t_kl S sumf energy Z_temp zt_pos t1 t2 Ht1 Ht2)
                   (plus (plus (opp Hh1) (mult B E1)) L2)
                   (plus (plus (mult B E1) (opp (mult A E1)))
                         (plus L2 (opp L1)))).
  - 
    exact (logc_relative_entropy_temp_decomp S sumf tsum_ext tsum_add tsum_linear
              energy Z_temp zt_spec zt_pos tsup_compat tsup_log_exp_neg
              t2 Ht2 t1 Ht1).
  - 
    apply (req_trans (plus (plus (opp Hh1) (mult B E1)) L2)
                     (plus (plus (plus (opp (mult A E1)) (opp L1)) (mult B E1)) L2)
                     (plus (plus (mult B E1) (opp (mult A E1)))
                           (plus L2 (opp L1)))).
    + apply (req_plus_compat (plus (opp Hh1) (mult B E1))
                (plus (plus (opp (mult A E1)) (opp L1)) (mult B E1)) L2 L2).
      * apply (req_plus_compat (opp Hh1) (plus (opp (mult A E1)) (opp L1))
                  (mult B E1) (mult B E1)).
        -- exact (logc2_opp_h_temp t1 Ht1).
        -- apply req_refl.
      * apply req_refl.
    + apply (req_trans (plus (plus (plus (opp (mult A E1)) (opp L1)) (mult B E1)) L2)
                       (plus (plus (plus (opp (mult A E1)) (mult B E1)) (opp L1)) L2)
                       (plus (plus (mult B E1) (opp (mult A E1)))
                             (plus L2 (opp L1)))).
      * apply (req_plus_compat (plus (plus (opp (mult A E1)) (opp L1)) (mult B E1))
                  (plus (plus (opp (mult A E1)) (mult B E1)) (opp L1)) L2 L2).
        -- exact (logc2_plus_swap_mid (opp (mult A E1)) (opp L1) (mult B E1)).
        -- apply req_refl.
      * apply (req_trans (plus (plus (plus (opp (mult A E1)) (mult B E1)) (opp L1)) L2)
                         (plus (plus (opp (mult A E1)) (mult B E1)) (plus (opp L1) L2))
                         (plus (plus (mult B E1) (opp (mult A E1)))
                               (plus L2 (opp L1)))).
        -- exact (req_sym (plus (plus (opp (mult A E1)) (mult B E1))
                                   (plus (opp L1) L2))
                             (plus (plus (plus (opp (mult A E1)) (mult B E1))
                                        (opp L1)) L2)
                             (plus_assoc (plus (opp (mult A E1)) (mult B E1))
                               (opp L1) L2)).
        -- apply (req_trans (plus (plus (opp (mult A E1)) (mult B E1))
                                   (plus (opp L1) L2))
                            (plus (plus (mult B E1) (opp (mult A E1)))
                                  (plus (opp L1) L2))
                            (plus (plus (mult B E1) (opp (mult A E1)))
                                  (plus L2 (opp L1)))).
           ++ apply (req_plus_compat (plus (opp (mult A E1)) (mult B E1))
                        (plus (mult B E1) (opp (mult A E1)))
                        (plus (opp L1) L2) (plus (opp L1) L2)).
              ** exact (plus_comm (opp (mult A E1)) (mult B E1)).
              ** apply req_refl.
           ++ apply (req_plus_compat (plus (mult B E1) (opp (mult A E1)))
                        (plus (mult B E1) (opp (mult A E1)))
                        (plus (opp L1) L2) (plus L2 (opp L1))).
              ** apply req_refl.
              ** exact (plus_comm (opp L1) L2).
Qed.

(* Q4【参数位 7 消解件】：KL(t2‖t1)+KL(t1‖t2) ≡ (1/t1-1/t2)·(E2-E1)              *)
(*   （req_temp_strict_ident2@UpFirewallReq:144 复合重建；req_minus δ 透明，   *)
(*   证内 unfold 换 plus/opp 形后 8 项置换坍缩 + distrib 完成）                *)
Lemma logc_temp_strict_ident2 :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (plus (logc_t_kl S sumf energy Z_temp zt_pos t2 t1 Ht2 Ht1)
            (logc_t_kl S sumf energy Z_temp zt_pos t1 t2 Ht1 Ht2))
      (mult (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))
            (req_minus (logc_t_et S sumf energy Z_temp zt_pos t2 Ht2)
                       (logc_t_et S sumf energy Z_temp zt_pos t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  unfold req_minus.
  set (A := inv_pos t1 Ht1).
  set (B := inv_pos t2 Ht2).
  set (E1 := logc_t_et S sumf energy Z_temp zt_pos t1 Ht1).
  set (E2 := logc_t_et S sumf energy Z_temp zt_pos t2 Ht2).
  set (L1 := log (Z_temp t1) (zt_pos t1 Ht1)).
  set (L2 := log (Z_temp t2) (zt_pos t2 Ht2)).
  (* 主链：KL 和 → 4 项数缩形 → X·(E2-E1)，X = 1/t1 - 1/t2 *)
  apply (req_trans (plus (logc_t_kl S sumf energy Z_temp zt_pos t2 t1 Ht2 Ht1)
                         (logc_t_kl S sumf energy Z_temp zt_pos t1 t2 Ht1 Ht2))
                   (plus (plus (mult A E2) (opp (mult B E2)))
                         (plus (mult B E1) (opp (mult A E1))))
                   (mult (plus A (opp B)) (plus E2 (opp E1)))).
  - (* 8 项置换坍缩：两翼并置 → logZ 双抵消 → 4 项数缩形 *)
    apply (req_trans (plus (logc_t_kl S sumf energy Z_temp zt_pos t2 t1 Ht2 Ht1)
                           (logc_t_kl S sumf energy Z_temp zt_pos t1 t2 Ht1 Ht2))
                     (plus (plus (plus (mult A E2) (opp (mult B E2)))
                                 (plus L1 (opp L2)))
                           (plus (plus (mult B E1) (opp (mult A E1)))
                                 (plus L2 (opp L1))))
                     (plus (plus (mult A E2) (opp (mult B E2)))
                           (plus (mult B E1) (opp (mult A E1))))).
    + apply (req_plus_compat (logc_t_kl S sumf energy Z_temp zt_pos t2 t1 Ht2 Ht1)
               (plus (plus (mult A E2) (opp (mult B E2))) (plus L1 (opp L2)))
               (logc_t_kl S sumf energy Z_temp zt_pos t1 t2 Ht1 Ht2)
               (plus (plus (mult B E1) (opp (mult A E1))) (plus L2 (opp L1)))).
      * exact (logc2_kl21_temp_swap t1 t2 Ht1 Ht2).
      * exact (logc2_kl12_temp_swap t1 t2 Ht1 Ht2).
    + apply (req_trans (plus (plus (plus (mult A E2) (opp (mult B E2)))
                                   (plus L1 (opp L2)))
                             (plus (plus (mult B E1) (opp (mult A E1)))
                                   (plus L2 (opp L1))))
                       (plus (plus (plus (mult A E2) (opp (mult B E2)))
                                   (plus (mult B E1) (opp (mult A E1))))
                             (plus (plus L1 (opp L2)) (plus L2 (opp L1))))
                       (plus (plus (mult A E2) (opp (mult B E2)))
                             (plus (mult B E1) (opp (mult A E1))))).
      * exact (logc2_plus_exchange (plus (mult A E2) (opp (mult B E2)))
                     (plus L1 (opp L2))
                     (plus (mult B E1) (opp (mult A E1)))
                     (plus L2 (opp L1))).
      * apply (req_trans (plus (plus (plus (mult A E2) (opp (mult B E2)))
                                       (plus (mult B E1) (opp (mult A E1))))
                                 (plus (plus L1 (opp L2)) (plus L2 (opp L1))))
                         (plus (plus (plus (mult A E2) (opp (mult B E2)))
                                     (plus (mult B E1) (opp (mult A E1))))
                               zero)
                         (plus (plus (mult A E2) (opp (mult B E2)))
                               (plus (mult B E1) (opp (mult A E1))))).
        -- apply (req_plus_compat
                     (plus (plus (mult A E2) (opp (mult B E2)))
                           (plus (mult B E1) (opp (mult A E1))))
                     (plus (plus (mult A E2) (opp (mult B E2)))
                           (plus (mult B E1) (opp (mult A E1))))
                     (plus (plus L1 (opp L2)) (plus L2 (opp L1))) zero).
           ++ apply req_refl.
           ++ exact (logc2_logpair_zero L1 L2).
        -- exact (plus_zero (plus (plus (mult A E2) (opp (mult B E2)))
                    (plus (mult B E1) (opp (mult A E1))))).
  - (* distrib 完成：X·(E2-E1) ≡ X·E2 + X·(-E1) ≡ 4 项数缩形（反向链） *)
    apply req_sym.
    assert (HXE : forall E : R,
              req (mult (plus A (opp B)) E) (plus (mult A E) (opp (mult B E)))).
    { intro E.
      apply (req_trans (mult (plus A (opp B)) E)
                       (mult E (plus A (opp B)))
                       (plus (mult A E) (opp (mult B E)))).
      - exact (mult_comm (plus A (opp B)) E).
      - apply (req_trans (mult E (plus A (opp B)))
                         (plus (mult E A) (mult E (opp B)))
                         (plus (mult A E) (opp (mult B E)))).
        + exact (distrib E A (opp B)).
        + apply (req_plus_compat (mult E A) (mult A E)
                    (mult E (opp B)) (opp (mult B E))).
          * exact (mult_comm E A).
          * apply (req_trans (mult E (opp B)) (opp (mult E B))
                     (opp (mult B E))).
            -- exact (logc_mult_opp_l E B).
            -- apply req_opp_compat. exact (mult_comm E B). }
    apply (req_trans (mult (plus A (opp B)) (plus E2 (opp E1)))
                     (plus (mult (plus A (opp B)) E2)
                           (mult (plus A (opp B)) (opp E1)))
                     (plus (plus (mult A E2) (opp (mult B E2)))
                           (plus (mult B E1) (opp (mult A E1))))).
    + exact (distrib (plus A (opp B)) E2 (opp E1)).
    + apply (req_plus_compat (mult (plus A (opp B)) E2)
               (plus (mult A E2) (opp (mult B E2)))
               (mult (plus A (opp B)) (opp E1))
               (plus (mult B E1) (opp (mult A E1)))).
      * exact (HXE E2).
      * apply (req_trans (mult (plus A (opp B)) (opp E1))
                         (opp (mult (plus A (opp B)) E1))
                         (plus (mult B E1) (opp (mult A E1)))).
        -- exact (logc_mult_opp_l (plus A (opp B)) E1).
        -- apply (req_trans (opp (mult (plus A (opp B)) E1))
                            (opp (plus (mult A E1) (opp (mult B E1))))
                            (plus (mult B E1) (opp (mult A E1)))).
           ++ apply req_opp_compat. exact (HXE E1).
           ++ apply (req_trans (opp (plus (mult A E1) (opp (mult B E1))))
                               (plus (opp (mult A E1)) (opp (opp (mult B E1))))
                               (plus (mult B E1) (opp (mult A E1)))).
              ** exact (logc_opp_plus (mult A E1) (opp (mult B E1))).
              ** apply (req_trans (plus (opp (mult A E1)) (opp (opp (mult B E1))))
                                  (plus (mult B E1) (opp (mult A E1)))
                                  (plus (mult B E1) (opp (mult A E1)))).
                 --- apply (req_trans (plus (opp (mult A E1)) (opp (opp (mult B E1))))
                                      (plus (opp (mult A E1)) (mult B E1))
                                      (plus (mult B E1) (opp (mult A E1)))).
                     +++ apply (req_plus_compat (opp (mult A E1)) (opp (mult A E1))
                                   (opp (opp (mult B E1))) (mult B E1)).
                         *** apply req_refl.
                         *** exact (logd_req_opp_opp R RIS (mult B E1)).
                     +++ exact (plus_comm (opp (mult A E1)) (mult B E1)).
                 --- apply req_refl.
Qed.

End LogcTemp2.

(* ============================================================ *)
(* 闭合性审计（G2 关：Print Assumptions 全 Closed）                           *)
(* ============================================================ *)
Print Assumptions logc_temp_strict_ident2.
Print Assumptions logc2_kl21_temp_swap.
Print Assumptions logc2_kl12_temp_swap.
Print Assumptions logc2_opp_h_temp.
Print Assumptions logc2_plus_swap_mid.
Print Assumptions logc2_plus_exchange.
Print Assumptions logc2_logpair_zero.

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqSLM.
Require Import UpReqRDF.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Part 0：节假设位组（三申报参数 S1-S3 + 三类参数位给出）                              *)
(* ============================================================ *)

Section LRDF.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {RNN : ReqNonnegPlain R}.
Context {RDP : ReqDiffPlain R}.
Context {RLL : ReqLogPlain R}.

(* S1：|a| < c ⟹ 0 < c + a（real_abs_lt_lower req 参数形，正和形） *)
Hypothesis lrdf_abs_lower_pos :
  forall (a c : R), lt (abs a) c -> lt zero (plus c a).

(* S2：u ≤ w ∧ −u ≤ w ⟹ |u| ≤ w（real_abs_le_quad_eps 核 req 参数形） *)
Hypothesis lrdf_abs_le_intro :
  forall (u w : R), le u w -> le (opp u) w -> le (abs u) w.

(* S3a：0 ≤ t²（Qsquare_nonneg 逐点事实 req 参数形） *)
Hypothesis lrdf_sq_nonneg : forall t : R, le zero (mult t t).

(* S3b：t² ≤ |t|²（q_sq_abs@46130 req 参数形） *)
Hypothesis lrdf_sq_le_abs_sq : forall t : R,
  le (mult t t) (mult (abs t) (abs t)).

(* ============================================================ *)
(* Part 0.5：纯接口小件（零参数位；环/序/inv 机）                                   *)
(* ============================================================ *)

(* 0.0：req_minus 展开机（req_minus δ 透明；unification 位显式换形用） *)
Lemma lrdf_req_minus_unfold : forall a b : R,
  req (req_minus a b) (plus a (opp b)).
Proof.
  intros a b.
  exact (req_refl (plus a (opp b))).
Qed.

(* 0.1：1 ≤ c·w ⟹ inv c ≤ w（inv 放缩机） *)
Lemma lrdf_inv_le_of_one_le_mul : forall (c w : R) (Hc : lt zero c),
  le one (mult c w) -> le (inv_pos c Hc) w.
Proof.
  intros c w Hc Hle.
  apply (le_id_l (inv_pos c Hc) (mult one (inv_pos c Hc)) w
           (req_trans (inv_pos c Hc) (mult (inv_pos c Hc) one)
                      (mult one (inv_pos c Hc))
                      (req_sym (mult (inv_pos c Hc) one) (inv_pos c Hc)
                         (mult_one (inv_pos c Hc)))
                      (mult_comm (inv_pos c Hc) one))).
  apply (le_id_r (mult one (inv_pos c Hc)) (mult (mult c w) (inv_pos c Hc)) w).
  - exact (req_trans (mult (mult c w) (inv_pos c Hc))
                     (mult c (mult w (inv_pos c Hc)))
                     w
                     (req_sym (mult c (mult w (inv_pos c Hc)))
                              (mult (mult c w) (inv_pos c Hc))
                              (mult_assoc c w (inv_pos c Hc)))
                     (req_trans (mult c (mult w (inv_pos c Hc)))
                                (mult c (mult (inv_pos c Hc) w))
                                w
                                (req_mult_compat c c (mult w (inv_pos c Hc))
                                                   (mult (inv_pos c Hc) w)
                                                   (req_refl c) (mult_comm w (inv_pos c Hc)))
                                (req_trans (mult c (mult (inv_pos c Hc) w))
                                           (mult (mult c (inv_pos c Hc)) w)
                                           w
                                           (mult_assoc c (inv_pos c Hc) w)
                                           (req_trans (mult (mult c (inv_pos c Hc)) w)
                                                      (mult one w)
                                                      w
                                                      (req_mult_compat (mult c (inv_pos c Hc)) one w w
                                                         (inv_pos_correct c Hc) (req_refl w))
                                                      (req_trans (mult one w) (mult w one) w
                                                                 (mult_comm one w) (mult_one w)))))).
  - exact (le_mult_compat one (mult c w) (inv_pos c Hc) (inv_pos_pos c Hc) Hle).
Qed.

(* 0.2：a·(opp b) ≡ opp (a·b)（opp 出分配；UpReqLogCompD A2 同形独立重建） *)
Lemma lrdf_mult_opp_r : forall a b : R, req (mult a (opp b)) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (mult a (opp b)) (mult a b) (opp (mult a b))).
  apply (req_trans (plus (mult a (opp b)) (mult a b))
                   zero
                   (plus (opp (mult a b)) (mult a b))).
  - apply (req_trans (plus (mult a (opp b)) (mult a b))
                     (mult a (plus (opp b) b))
                     zero).
    + exact (req_sym (mult a (plus (opp b) b))
                     (plus (mult a (opp b)) (mult a b))
                     (distrib a (opp b) b)).
    + apply (req_trans (mult a (plus (opp b) b)) (mult a zero) zero).
      * exact (req_mult_compat a a (plus (opp b) b) zero (req_refl a)
                 (req_trans (plus (opp b) b) (plus b (opp b)) zero
                            (plus_comm (opp b) b) (plus_opp b))).
      * exact (mult_zero a).
  - exact (req_sym (plus (opp (mult a b)) (mult a b)) zero
             (req_trans (plus (opp (mult a b)) (mult a b))
                        (plus (mult a b) (opp (mult a b))) zero
                        (plus_comm (opp (mult a b)) (mult a b)) (plus_opp (mult a b)))).
Qed.

(* 0.3：(u + w) − u ≡ w（右消去） *)
Lemma lrdf_cancel_r : forall u w : R, req (plus (plus u w) (opp u)) w.
Proof.
  intros u w.
  apply (req_trans (plus (plus u w) (opp u)) (plus (plus w u) (opp u)) w).
  - exact (req_plus_compat (plus u w) (plus w u) (opp u) (opp u)
              (plus_comm u w) (req_refl (opp u))).
  - apply (req_trans (plus (plus w u) (opp u)) (plus w (plus u (opp u))) w).
    + exact (req_sym (plus w (plus u (opp u))) (plus (plus w u) (opp u))
               (plus_assoc w u (opp u))).
    + apply (req_trans (plus w (plus u (opp u))) (plus w zero) w).
      * exact (req_plus_compat w w (plus u (opp u)) zero (req_refl w) (plus_opp u)).
      * exact (plus_zero w).
Qed.

(* 0.4：(opp u) + (u + w) ≡ w（左 opp 消去） *)
Lemma lrdf_cancel_l_opp : forall u w : R, req (plus (opp u) (plus u w)) w.
Proof.
  intros u w.
  apply (req_trans (plus (opp u) (plus u w)) (plus (plus (opp u) u) w) w).
  - exact (plus_assoc (opp u) u w).
  - apply (req_trans (plus (plus (opp u) u) w) (plus zero w) w).
    + exact (req_plus_compat (plus (opp u) u) zero w w
               (req_trans (plus (opp u) u) (plus u (opp u)) zero
                          (plus_comm (opp u) u) (plus_opp u))
               (req_refl w)).
    + exact (req_trans (plus zero w) (plus w zero) w (plus_comm zero w) (plus_zero w)).
Qed.

(* 0.5：|a·inv x| ≡ |a|·inv x（x>0；abs_mult + abs_pos） *)
Lemma lrdf_t_abs_eq : forall (x a : R) (Hx : lt zero x),
  req (abs (mult a (inv_pos x Hx))) (mult (abs a) (inv_pos x Hx)).
Proof.
  intros x a Hx.
  apply (req_trans (abs (mult a (inv_pos x Hx)))
                   (mult (abs a) (abs (inv_pos x Hx)))
                   (mult (abs a) (inv_pos x Hx))).
  - exact (abs_mult a (inv_pos x Hx)).
  - exact (req_mult_compat (abs a) (abs a) (abs (inv_pos x Hx)) (inv_pos x Hx)
             (req_refl (abs a)) (abs_pos (inv_pos x Hx) (inv_pos_pos x Hx))).
Qed.

(* 0.6：|a| < b·x ⟹ |a·inv x| < b（x>0；t 小化机，一式两用） *)
Lemma lrdf_t_lt_of : forall (x a b : R) (Hx : lt zero x),
  lt (abs a) (mult b x) -> lt (abs (mult a (inv_pos x Hx))) b.
Proof.
  intros x a b Hx Hlt.
  apply (lt_id_l (abs (mult a (inv_pos x Hx))) (mult (abs a) (inv_pos x Hx)) b
            (lrdf_t_abs_eq x a Hx)).
  apply (lt_id_r (mult (abs a) (inv_pos x Hx)) (mult (mult b x) (inv_pos x Hx)) b).
  - exact (req_trans (mult (mult b x) (inv_pos x Hx))
                     (mult b (mult x (inv_pos x Hx)))
                     b
                     (req_sym (mult b (mult x (inv_pos x Hx)))
                              (mult (mult b x) (inv_pos x Hx))
                              (mult_assoc b x (inv_pos x Hx)))
                     (req_trans (mult b (mult x (inv_pos x Hx)))
                                (mult b one)
                                b
                                (req_mult_compat b b (mult x (inv_pos x Hx)) one
                                   (req_refl b) (inv_pos_correct x Hx))
                                (mult_one b))).
  - exact (lt_mult_compat (abs a) (mult b x) (inv_pos x Hx) (inv_pos_pos x Hx) Hlt).
Qed.

(* 0.7：A ≡ tt + B 形换形：tt ≡ A + B ⟹ opp A ≡ (opp tt) + B（误差分裂机） *)
Lemma lrdf_opp_split_eq : forall (A B tt : R),
  req tt (plus A B) -> req (opp A) (plus (opp tt) B).
Proof.
  intros A B tt H.
  apply (req_trans (opp A) (plus (opp A) (plus (opp B) B)) (plus (opp tt) B)).
  - apply (req_sym (plus (opp A) (plus (opp B) B)) (opp A)).
    apply (req_trans (plus (opp A) (plus (opp B) B)) (plus (opp A) zero) (opp A)).
    + exact (req_plus_compat (opp A) (opp A) (plus (opp B) B) zero
               (req_refl (opp A))
               (req_trans (plus (opp B) B) (plus B (opp B)) zero
                          (plus_comm (opp B) B) (plus_opp B))).
    + exact (plus_zero (opp A)).
  - apply (req_trans (plus (opp A) (plus (opp B) B))
                     (plus (plus (opp A) (opp B)) B)
                     (plus (opp tt) B)).
    + exact (plus_assoc (opp A) (opp B) B).
    + apply (req_plus_compat (plus (opp A) (opp B)) (opp tt) B B
               (req_sym (opp tt) (plus (opp A) (opp B))
                  (req_trans (opp tt) (opp (plus A B))
                             (plus (opp A) (opp B))
                             (req_opp_compat tt (plus A B) H)
                             (req_opp_plus A B)))
               (req_refl B)).
Qed.

(* 0.8：x + h ≡ x·(1 + h·inv x)（x>0；复合换元母恒等） *)
Lemma lrdf_xh_eq : forall (x h : R) (Hx : lt zero x),
  req (plus x h) (mult x (plus one (mult h (inv_pos x Hx)))).
Proof.
  intros x h Hx.
  apply (req_sym (mult x (plus one (mult h (inv_pos x Hx)))) (plus x h)).
  apply (req_trans (mult x (plus one (mult h (inv_pos x Hx))))
                   (plus (mult x one) (mult x (mult h (inv_pos x Hx))))
                   (plus x h)).
  - exact (distrib x one (mult h (inv_pos x Hx))).
  - apply (req_trans (plus (mult x one) (mult x (mult h (inv_pos x Hx))))
                     (plus x (mult h (mult x (inv_pos x Hx))))
                     (plus x h)).
    + exact (req_plus_compat (mult x one) x (mult x (mult h (inv_pos x Hx)))
               (mult h (mult x (inv_pos x Hx)))
               (mult_one x)
               (req_trans (mult x (mult h (inv_pos x Hx)))
                          (mult (mult h x) (inv_pos x Hx))
                          (mult h (mult x (inv_pos x Hx)))
                          (req_trans (mult x (mult h (inv_pos x Hx)))
                                     (mult (mult x h) (inv_pos x Hx))
                                     (mult (mult h x) (inv_pos x Hx))
                                     (mult_assoc x h (inv_pos x Hx))
                                     (req_mult_compat (mult x h) (mult h x)
                                        (inv_pos x Hx) (inv_pos x Hx)
                                        (mult_comm x h) (req_refl (inv_pos x Hx))))
                          (req_sym (mult h (mult x (inv_pos x Hx)))
                                   (mult (mult h x) (inv_pos x Hx))
                                   (mult_assoc h x (inv_pos x Hx))))).
    + apply (req_plus_compat x x (mult h (mult x (inv_pos x Hx))) h
               (req_refl x)
               (req_trans (mult h (mult x (inv_pos x Hx))) (mult h one) h
                          (req_mult_compat h h (mult x (inv_pos x Hx)) one
                             (req_refl h) (inv_pos_correct x Hx))
                          (mult_one h))).
Qed.

(* 0.9：A ≡ s + (A − s)（minus 对拆） *)
Lemma lrdf_plus_minus : forall (A s : R),
  req A (plus s (req_minus A s)).
Proof.
  intros A s.
  apply (req_trans A (plus (req_minus A s) s) (plus s (req_minus A s))).
  - exact (req_rdf_minus_pair A s).
  - exact (plus_comm (req_minus A s) s).
Qed.

(* 0.10：s + u ≡ s·(1 + u·inv s)（s·inv ≡ 1 一般化换元母恒等） *)
Lemma lrdf_s_plus_eq : forall (s uu inv : R) (Hc : req (mult s inv) one),
  req (plus s uu) (mult s (plus one (mult uu inv))).
Proof.
  intros s uu inv Hc.
  apply (req_sym (mult s (plus one (mult uu inv))) (plus s uu)).
  apply (req_trans (mult s (plus one (mult uu inv)))
                   (plus (mult s one) (mult s (mult uu inv)))
                   (plus s uu)).
  - exact (distrib s one (mult uu inv)).
  - apply (req_trans (plus (mult s one) (mult s (mult uu inv)))
                     (plus s (mult uu (mult s inv)))
                     (plus s uu)).
    + exact (req_plus_compat (mult s one) s (mult s (mult uu inv))
               (mult uu (mult s inv))
               (mult_one s)
               (req_trans (mult s (mult uu inv))
                          (mult (mult s uu) inv)
                          (mult uu (mult s inv))
                          (mult_assoc s uu inv)
                          (req_trans (mult (mult s uu) inv)
                                     (mult (mult uu s) inv)
                                     (mult uu (mult s inv))
                                     (req_mult_compat (mult s uu) (mult uu s)
                                        inv inv (mult_comm s uu) (req_refl inv))
                                     (req_sym (mult uu (mult s inv))
                                              (mult (mult uu s) inv)
                                              (mult_assoc uu s inv))))).
    + exact (req_plus_compat s s (mult uu (mult s inv)) uu
               (req_refl s)
               (req_trans (mult uu (mult s inv)) (mult uu one) uu
                          (req_mult_compat uu uu (mult s inv) one
                             (req_refl uu) Hc)
                          (mult_one uu))).
Qed.

(* 0.11：(a·b)·inv ≡ a（b·inv ≡ 1 消去） *)
Lemma lrdf_mul_inv_one : forall (a b inv : R) (Hb : req (mult b inv) one),
  req (mult (mult a b) inv) a.
Proof.
  intros a b inv Hb.
  apply (req_trans (mult (mult a b) inv) (mult a (mult b inv)) a).
  - exact (req_sym (mult a (mult b inv)) (mult (mult a b) inv) (mult_assoc a b inv)).
  - apply (req_trans (mult a (mult b inv)) (mult a one) a).
    + exact (req_mult_compat a a (mult b inv) one (req_refl a) Hb).
    + exact (mult_one a).
Qed.

(* 0.11b：(a·b)·inv ≡ (a·inv)·b（同因子双换位；HB 尾链换元用） *)
Lemma lrdf_mul_h_inv : forall a b inv : R,
  req (mult (mult a b) inv) (mult (mult a inv) b).
Proof.
  intros a b inv.
  exact (req_trans (mult (mult a b) inv) (mult a (mult b inv))                   (mult (mult a inv) b)           (req_sym (mult a (mult b inv)) (mult (mult a b) inv)              (mult_assoc a b inv))           (req_trans (mult a (mult b inv)) (mult a (mult inv b))                      (mult (mult a inv) b)              (req_mult_compat a a (mult b inv) (mult inv b)                 (req_refl a) (mult_comm b inv))              (mult_assoc a inv b))).
Qed.

(* ============================================================ *)

(* ============================================================ *)

(* 1.1：环恒等 1 − inv(1+t) ≡ (t)·inv(1+t)（对标 real_succ_minus_one +       *)
(*      real_inv_minus_one_opp_noHt 组合内件） *)
Lemma lrdf_inner_one_opp_inv : forall (t : R) (Hs : lt zero (plus one t)),
  req (plus one (opp (inv_pos (plus one t) Hs)))
      (mult (plus (plus one t) (opp one)) (inv_pos (plus one t) Hs)).
Proof.
  intros t Hs.
  apply (req_trans (plus one (opp (inv_pos (plus one t) Hs)))
                   (plus (mult (plus one t) (inv_pos (plus one t) Hs))
                         (opp (mult (inv_pos (plus one t) Hs) one)))
                   (mult (plus (plus one t) (opp one)) (inv_pos (plus one t) Hs))).
  - exact (req_plus_compat one (mult (plus one t) (inv_pos (plus one t) Hs))
              (opp (inv_pos (plus one t) Hs))
              (opp (mult (inv_pos (plus one t) Hs) one))
              (req_sym (mult (plus one t) (inv_pos (plus one t) Hs)) one
                 (inv_pos_correct (plus one t) Hs))
              (req_opp_compat (inv_pos (plus one t) Hs)
                 (mult (inv_pos (plus one t) Hs) one)
                 (req_sym (mult (inv_pos (plus one t) Hs) one)
                          (inv_pos (plus one t) Hs)
                          (mult_one (inv_pos (plus one t) Hs))))).
  - apply (req_trans (plus (mult (plus one t) (inv_pos (plus one t) Hs))
                           (opp (mult (inv_pos (plus one t) Hs) one)))
                     (plus (mult (inv_pos (plus one t) Hs) (plus one t))
                           (mult (inv_pos (plus one t) Hs) (opp one)))
                     (mult (plus (plus one t) (opp one)) (inv_pos (plus one t) Hs))).
    + exact (req_plus_compat (mult (plus one t) (inv_pos (plus one t) Hs))
               (mult (inv_pos (plus one t) Hs) (plus one t))
               (opp (mult (inv_pos (plus one t) Hs) one))
               (mult (inv_pos (plus one t) Hs) (opp one))
               (mult_comm (plus one t) (inv_pos (plus one t) Hs))
               (req_sym (mult (inv_pos (plus one t) Hs) (opp one))
                        (opp (mult (inv_pos (plus one t) Hs) one))
                        (lrdf_mult_opp_r (inv_pos (plus one t) Hs) one))).
    + apply (req_trans (plus (mult (inv_pos (plus one t) Hs) (plus one t))
                             (mult (inv_pos (plus one t) Hs) (opp one)))
                       (mult (inv_pos (plus one t) Hs) (plus (plus one t) (opp one)))
                       (mult (plus (plus one t) (opp one)) (inv_pos (plus one t) Hs))).
      * exact (req_sym (mult (inv_pos (plus one t) Hs) (plus (plus one t) (opp one)))
                       (plus (mult (inv_pos (plus one t) Hs) (plus one t))
                             (mult (inv_pos (plus one t) Hs) (opp one)))
                       (distrib (inv_pos (plus one t) Hs) (plus one t) (opp one))).
      * exact (mult_comm (inv_pos (plus one t) Hs) (plus (plus one t) (opp one))).
Qed.

(* 1.2：环恒等 t + (inv(1+t) − 1) ≡ t²·inv(1+t)（对标 real_t_plus_inv_      *)
(*      minus_one@:44952；链 = req_set_inv_minus_one_opp@UpReqSLM 反向   *)
(*      + distrib + req_ld3_minus_one_plus_t） *)
Lemma lrdf_t_plus_inv_minus_one : forall (t : R) (Hs : lt zero (plus one t)),
  req (plus t (req_minus (inv_pos (plus one t) Hs) one))
      (mult (mult t t) (inv_pos (plus one t) Hs)).
Proof.
  intros t Hs.
  unfold req_minus.
  apply (req_trans (plus t (plus (inv_pos (plus one t) Hs) (opp one)))
                   (plus t (opp (mult t (inv_pos (plus one t) Hs))))
                   (mult (mult t t) (inv_pos (plus one t) Hs))).
  - apply (req_plus_compat t t (plus (inv_pos (plus one t) Hs) (opp one))
              (opp (mult t (inv_pos (plus one t) Hs)))
              (req_refl t)
              (req_trans (plus (inv_pos (plus one t) Hs) (opp one))
                         (opp (opp (plus (inv_pos (plus one t) Hs) (opp one))))
                         (opp (mult t (inv_pos (plus one t) Hs)))
                         (req_sym (opp (opp (plus (inv_pos (plus one t) Hs) (opp one))))
                                  (plus (inv_pos (plus one t) Hs) (opp one))
                                  (req_double_neg
                                     (plus (inv_pos (plus one t) Hs) (opp one))))
                         (req_sym (opp (mult t (inv_pos (plus one t) Hs)))
                                  (opp (opp (plus (inv_pos (plus one t) Hs) (opp one))))
                                  (req_opp_compat (mult t (inv_pos (plus one t) Hs))
                                     (opp (plus (inv_pos (plus one t) Hs) (opp one)))
                                     (req_trans (mult t (inv_pos (plus one t) Hs))
                                        (opp (req_minus (inv_pos (plus one t) Hs) one))
                                        (opp (plus (inv_pos (plus one t) Hs) (opp one)))
                                        (req_set_inv_minus_one_opp t Hs)
                                        (req_opp_compat (req_minus (inv_pos (plus one t) Hs) one)
                                           (plus (inv_pos (plus one t) Hs) (opp one))
                                           (lrdf_req_minus_unfold
                                              (inv_pos (plus one t) Hs) one))))))).
  - apply (req_trans (plus t (opp (mult t (inv_pos (plus one t) Hs))))
                     (plus (mult t one) (mult t (opp (inv_pos (plus one t) Hs))))
                     (mult (mult t t) (inv_pos (plus one t) Hs))).
    + exact (req_plus_compat t (mult t one)
               (opp (mult t (inv_pos (plus one t) Hs)))
               (mult t (opp (inv_pos (plus one t) Hs)))
               (req_sym (mult t one) t (mult_one t))
               (req_sym (mult t (opp (inv_pos (plus one t) Hs)))
                        (opp (mult t (inv_pos (plus one t) Hs)))
                        (lrdf_mult_opp_r t (inv_pos (plus one t) Hs)))).
    + apply (req_trans (plus (mult t one) (mult t (opp (inv_pos (plus one t) Hs))))
                       (mult t (plus one (opp (inv_pos (plus one t) Hs))))
                       (mult (mult t t) (inv_pos (plus one t) Hs))).
      * exact (req_sym (mult t (plus one (opp (inv_pos (plus one t) Hs))))
                       (plus (mult t one) (mult t (opp (inv_pos (plus one t) Hs))))
                       (distrib t one (opp (inv_pos (plus one t) Hs)))).
      * apply (req_trans (mult t (plus one (opp (inv_pos (plus one t) Hs))))
                         (mult t (mult (plus (plus one t) (opp one))
                                       (inv_pos (plus one t) Hs)))
                         (mult (mult t t) (inv_pos (plus one t) Hs))).
        -- apply (req_mult_compat t t
                     (plus one (opp (inv_pos (plus one t) Hs)))
                     (mult (plus (plus one t) (opp one)) (inv_pos (plus one t) Hs))
                     (req_refl t) (lrdf_inner_one_opp_inv t Hs)).
        -- apply (req_trans (mult t (mult (plus (plus one t) (opp one))
                                            (inv_pos (plus one t) Hs)))
                            (mult t (mult t (inv_pos (plus one t) Hs)))
                            (mult (mult t t) (inv_pos (plus one t) Hs))).
           ++ apply (req_mult_compat t t
                        (mult (plus (plus one t) (opp one)) (inv_pos (plus one t) Hs))
                        (mult t (inv_pos (plus one t) Hs))
                        (req_refl t)
                        (req_mult_compat (plus (plus one t) (opp one)) t
                           (inv_pos (plus one t) Hs) (inv_pos (plus one t) Hs)
                           (req_trans (plus (plus one t) (opp one))
                              (req_minus (plus one t) one)
                              t
                              (req_sym (plus (plus one t) (opp one))
                                 (req_minus (plus one t) one)
                                 (lrdf_req_minus_unfold (plus one t) one))
                              (req_ld3_minus_one_plus_t t))
                           (req_refl (inv_pos (plus one t) Hs)))).
           ++ exact (mult_assoc t t (inv_pos (plus one t) Hs)).
Qed.

(* 1.3：|t| < 1/2 ⟹ 1/2 ≤ 1+t（S1 参数位 + 左 opp 消去 + one ≡ 1 − 1/2 链） *)
Lemma lrdf_half_le_one_t : forall t : R,
  lt (abs t) (inv_pos (plus one one) req_two_pos) ->
  le (inv_pos (plus one one) req_two_pos) (plus one t).
Proof.
  intros t Hlt.
  assert (Hle0 : le zero
    (plus (inv_pos (plus one one) req_two_pos) t)).
  { exact (lt_le_iff zero (plus (inv_pos (plus one one) req_two_pos) t)
             (inl (lrdf_abs_lower_pos t (inv_pos (plus one one) req_two_pos) Hlt))). }
  assert (Hcancel : req (plus (opp (inv_pos (plus one one) req_two_pos))
                              (plus (inv_pos (plus one one) req_two_pos) t))
                        t).
  { exact (lrdf_cancel_l_opp (inv_pos (plus one one) req_two_pos) t). }
  assert (Hoeq : le (opp (inv_pos (plus one one) req_two_pos)) t).
  { apply (le_id_l (opp (inv_pos (plus one one) req_two_pos))
                   (plus (opp (inv_pos (plus one one) req_two_pos)) zero) t
             (req_sym (plus (opp (inv_pos (plus one one) req_two_pos)) zero)
                      (opp (inv_pos (plus one one) req_two_pos))
                      (plus_zero (opp (inv_pos (plus one one) req_two_pos))))).
    apply (le_id_r (plus (opp (inv_pos (plus one one) req_two_pos)) zero)
                   (plus (opp (inv_pos (plus one one) req_two_pos))
                         (plus (inv_pos (plus one one) req_two_pos) t))
                   t
                   Hcancel).
    exact (le_plus_compat (opp (inv_pos (plus one one) req_two_pos))
                          (opp (inv_pos (plus one one) req_two_pos))
                          zero
                          (plus (inv_pos (plus one one) req_two_pos) t)
                          (le_refl (opp (inv_pos (plus one one) req_two_pos)))
                          Hle0). }
  assert (Hone : req (plus (inv_pos (plus one one) req_two_pos)
                           (inv_pos (plus one one) req_two_pos))
                     one).
  { exact (req_trans (plus (inv_pos (plus one one) req_two_pos)
                           (inv_pos (plus one one) req_two_pos))
                     (plus (mult (inv_pos (plus one one) req_two_pos) one)
                           (mult (inv_pos (plus one one) req_two_pos) one))
                     one
                     (req_plus_compat (inv_pos (plus one one) req_two_pos)
                        (mult (inv_pos (plus one one) req_two_pos) one)
                        (inv_pos (plus one one) req_two_pos)
                        (mult (inv_pos (plus one one) req_two_pos) one)
                        (req_sym (mult (inv_pos (plus one one) req_two_pos) one)
                                 (inv_pos (plus one one) req_two_pos)
                                 (mult_one (inv_pos (plus one one) req_two_pos)))
                        (req_sym (mult (inv_pos (plus one one) req_two_pos) one)
                                 (inv_pos (plus one one) req_two_pos)
                                 (mult_one (inv_pos (plus one one) req_two_pos))))
                     (req_half_twice one req_two_pos)). }
  assert (Hone' : req (plus one (opp (inv_pos (plus one one) req_two_pos)))
                      (inv_pos (plus one one) req_two_pos)).
  { apply (req_trans (plus one (opp (inv_pos (plus one one) req_two_pos)))
                     (plus (plus (inv_pos (plus one one) req_two_pos)
                                 (inv_pos (plus one one) req_two_pos))
                           (opp (inv_pos (plus one one) req_two_pos)))
                     (inv_pos (plus one one) req_two_pos)).
    - exact (req_plus_compat one
                (plus (inv_pos (plus one one) req_two_pos)
                      (inv_pos (plus one one) req_two_pos))
                (opp (inv_pos (plus one one) req_two_pos))
                (opp (inv_pos (plus one one) req_two_pos))
                (req_sym (plus (inv_pos (plus one one) req_two_pos)
                               (inv_pos (plus one one) req_two_pos))
                         one Hone)
                (req_refl (opp (inv_pos (plus one one) req_two_pos)))).
    - apply (req_trans (plus (plus (inv_pos (plus one one) req_two_pos)
                                   (inv_pos (plus one one) req_two_pos))
                             (opp (inv_pos (plus one one) req_two_pos)))
                       (plus (inv_pos (plus one one) req_two_pos)
                             (plus (inv_pos (plus one one) req_two_pos)
                                   (opp (inv_pos (plus one one) req_two_pos))))
                       (inv_pos (plus one one) req_two_pos)).
      + exact (req_sym (plus (inv_pos (plus one one) req_two_pos)
                             (plus (inv_pos (plus one one) req_two_pos)
                                   (opp (inv_pos (plus one one) req_two_pos))))
                       (plus (plus (inv_pos (plus one one) req_two_pos)
                                   (inv_pos (plus one one) req_two_pos))
                             (opp (inv_pos (plus one one) req_two_pos)))
                       (plus_assoc (inv_pos (plus one one) req_two_pos)
                                   (inv_pos (plus one one) req_two_pos)
                                   (opp (inv_pos (plus one one) req_two_pos)))).
      + apply (req_trans (plus (inv_pos (plus one one) req_two_pos)
                               (plus (inv_pos (plus one one) req_two_pos)
                                     (opp (inv_pos (plus one one) req_two_pos))))
                         (plus (inv_pos (plus one one) req_two_pos) zero)
                         (inv_pos (plus one one) req_two_pos)).
        * exact (req_plus_compat (inv_pos (plus one one) req_two_pos)
                    (inv_pos (plus one one) req_two_pos)
                    (plus (inv_pos (plus one one) req_two_pos)
                          (opp (inv_pos (plus one one) req_two_pos)))
                    zero
                    (req_refl (inv_pos (plus one one) req_two_pos))
                    (plus_opp (inv_pos (plus one one) req_two_pos))).
        * exact (plus_zero (inv_pos (plus one one) req_two_pos)). }
  exact (le_id_l (inv_pos (plus one one) req_two_pos)
                 (plus one (opp (inv_pos (plus one one) req_two_pos)))
                 (plus one t)
                 (req_sym (plus one (opp (inv_pos (plus one one) req_two_pos)))
                          (inv_pos (plus one one) req_two_pos)
                          Hone')
                 (le_plus_compat one one
                    (opp (inv_pos (plus one one) req_two_pos)) t
                    (le_refl one) Hoeq)).
Qed.

(* 1.4：核定理（缺件 A/B 共享）：0 < 1+t ∧ 1/2 ≤ 1+t ∧ |t| ≤ eps/2 ⟹          *)
(*      |log(1+t) − t| ≤ eps·|t|（主定理 X 双臂的无 eps 化）             *)
Lemma lrdf_core_abs_bound :
  forall (t eps : R)
    (H1t : lt zero (plus one t))
    (Hhalf : le (inv_pos (plus one one) req_two_pos) (plus one t))
    (Htb : le (abs t) (mult (inv_pos (plus one one) req_two_pos) eps))
    (Heps : lt zero eps),
    le (abs (plus (log (plus one t) H1t) (opp t))) (mult eps (abs t)).
Proof.
  intros t eps H1t Hhalf Htb Heps.
  assert (HA : le (plus (log (plus one t) H1t) (opp t)) zero).
  { apply (le_id_r (plus (log (plus one t) H1t) (opp t))
                   (plus t (opp t)) zero (plus_opp t)).
    apply (le_id_l (plus (log (plus one t) H1t) (opp t))
                   (plus (log (plus one t) H1t) (opp t))
                   (plus t (opp t))
                   (req_refl (plus (log (plus one t) H1t) (opp t)))).
    exact (le_plus_compat (log (plus one t) H1t) t (opp t) (opp t)
             (req_log_one_plus_le t H1t) (le_refl (opp t))). }
  assert (HA2 : le (plus (log (plus one t) H1t) (opp t)) (mult eps (abs t))).
  { exact (le_trans (plus (log (plus one t) H1t) (opp t)) zero (mult eps (abs t))
              HA (req_rdf_zero_le_mult_abs eps t Heps)). }
  assert (HreqX : req (opp (plus (log (plus one t) H1t) (opp t)))
                      (plus t (opp (log (plus one t) H1t)))).
  { exact (req_trans (opp (plus (log (plus one t) H1t) (opp t)))
                     (plus (opp (log (plus one t) H1t)) (opp (opp t)))
                     (plus t (opp (log (plus one t) H1t)))
                     (req_opp_plus (log (plus one t) H1t) (opp t))
                     (req_trans (plus (opp (log (plus one t) H1t)) (opp (opp t)))
                                (plus (opp (log (plus one t) H1t)) t)
                                (plus t (opp (log (plus one t) H1t)))
                                (req_plus_compat (opp (log (plus one t) H1t))
                                   (opp (log (plus one t) H1t))
                                   (opp (opp t)) t
                                   (req_refl (opp (log (plus one t) H1t)))
                                   (req_double_neg t))
                                (plus_comm (opp (log (plus one t) H1t)) t))). }
  assert (HC : le (plus t (opp (log (plus one t) H1t)))
                  (mult (mult t t) (inv_pos (plus one t) H1t))).
  { apply (le_trans (plus t (opp (log (plus one t) H1t)))
                    (plus t (log (inv_pos (plus one t) H1t)
                                 (inv_pos_pos (plus one t) H1t)))
                    (mult (mult t t) (inv_pos (plus one t) H1t))).
    - apply (le_plus_compat t t
               (opp (log (plus one t) H1t))
               (log (inv_pos (plus one t) H1t)
                    (inv_pos_pos (plus one t) H1t))
               (le_refl t)).
      exact (req_set_eq_le (opp (log (plus one t) H1t))
                           (log (inv_pos (plus one t) H1t)
                                (inv_pos_pos (plus one t) H1t))
                           (req_sym (log (inv_pos (plus one t) H1t)
                                      (inv_pos_pos (plus one t) H1t))
                                    (opp (log (plus one t) H1t))
                                    (req_log_inv_one_inv log_req_compat_plain
                                       (plus one t) H1t))).
    - apply (le_trans (plus t (log (inv_pos (plus one t) H1t)
                                   (inv_pos_pos (plus one t) H1t)))
                      (plus t (req_minus (inv_pos (plus one t) H1t) one))
                      (mult (mult t t) (inv_pos (plus one t) H1t))).
      + exact (le_plus_compat t t
                 (log (inv_pos (plus one t) H1t) (inv_pos_pos (plus one t) H1t))
                 (req_minus (inv_pos (plus one t) H1t) one)
                 (le_refl t)
                 (log_le_linear_plain (inv_pos (plus one t) H1t)
                    (inv_pos_pos (plus one t) H1t))).
      + apply (req_set_eq_le (plus t (req_minus (inv_pos (plus one t) H1t) one))
                             (mult (mult t t) (inv_pos (plus one t) H1t))).
        exact (lrdf_t_plus_inv_minus_one t H1t). }
  assert (HB1 : le (opp (plus (log (plus one t) H1t) (opp t)))
                   (mult (mult t t) (inv_pos (plus one t) H1t))).
  { exact (le_id_l (opp (plus (log (plus one t) H1t) (opp t)))
                   (plus t (opp (log (plus one t) H1t)))
                   (mult (mult t t) (inv_pos (plus one t) H1t))
                   HreqX HC). }
  assert (Hprem : le one (mult (plus one t) (plus one one))).
  { apply (le_id_l one
             (mult (inv_pos (plus one one) req_two_pos) (plus one one))
             (mult (plus one t) (plus one one))).
    - exact (req_sym (mult (inv_pos (plus one one) req_two_pos) (plus one one)) one
                       (req_trans (mult (inv_pos (plus one one) req_two_pos) (plus one one))
                       (mult (plus one one) (inv_pos (plus one one) req_two_pos))
                       one
                       (mult_comm (inv_pos (plus one one) req_two_pos) (plus one one))
                       (inv_pos_correct (plus one one) req_two_pos))).
    - exact (le_mult_compat (inv_pos (plus one one) req_two_pos) (plus one t)
               (plus one one) (req_two_pos) Hhalf). }
  assert (Hinvs2 : le (inv_pos (plus one t) H1t) (plus one one)).
  { exact (lrdf_inv_le_of_one_le_mul (plus one t) (plus one one) H1t Hprem). }
  assert (HD2 : le (mult (mult t t) (inv_pos (plus one t) H1t))
                   (mult (mult t t) (plus one one))).
  { apply (le_id_l (mult (mult t t) (inv_pos (plus one t) H1t))
                   (mult (inv_pos (plus one t) H1t) (mult t t))
                   (mult (mult t t) (plus one one))
                   (mult_comm (mult t t) (inv_pos (plus one t) H1t))).
    apply (le_id_r (mult (inv_pos (plus one t) H1t) (mult t t))
                   (mult (plus one one) (mult t t))
                   (mult (mult t t) (plus one one))
                   (mult_comm (plus one one) (mult t t))).
    exact (le_mult_compat_weak (inv_pos (plus one t) H1t) (plus one one) (mult t t)
             (lrdf_sq_nonneg t) Hinvs2). }
  assert (HH : le (mult t t)
                  (mult (abs t)
                    (mult (inv_pos (plus one one) req_two_pos) eps))).
  { exact (le_trans (mult t t) (mult (abs t) (abs t))
              (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps))
              (lrdf_sq_le_abs_sq t)
              (req_le_mult_compat_r (abs t) (abs t)
                 (mult (inv_pos (plus one one) req_two_pos) eps)
                 (abs_nonneg_plain t) Htb)). }
  assert (RING2 : req (mult (plus one one)
                            (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                     (mult eps (abs t))).
  { exact (req_trans (mult (plus one one) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps))) (mult (mult (plus one one) (abs t)) (mult (inv_pos (plus one one) req_two_pos) eps)) (mult eps (abs t)) (mult_assoc (plus one one) (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)) (req_trans (mult (mult (plus one one) (abs t)) (mult (inv_pos (plus one one) req_two_pos) eps)) (mult (mult (abs t) (plus one one)) (mult (inv_pos (plus one one) req_two_pos) eps)) (mult eps (abs t)) (req_mult_compat (mult (plus one one) (abs t))
                    (mult (abs t) (plus one one))
                    (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (plus one one) req_two_pos) eps)
                    (mult_comm (plus one one) (abs t))
                    (req_refl (mult (inv_pos (plus one one) req_two_pos) eps))) (req_trans (mult (mult (abs t) (plus one one)) (mult (inv_pos (plus one one) req_two_pos) eps)) (mult (abs t) (mult (plus one one) (mult (inv_pos (plus one one) req_two_pos) eps))) (mult eps (abs t)) (req_sym (mult (abs t) (mult (plus one one) (mult (inv_pos (plus one one) req_two_pos) eps)))
             (mult (mult (abs t) (plus one one)) (mult (inv_pos (plus one one) req_two_pos) eps))
             (mult_assoc (abs t) (plus one one) (mult (inv_pos (plus one one) req_two_pos) eps))) (req_trans (mult (abs t) (mult (plus one one) (mult (inv_pos (plus one one) req_two_pos) eps))) (mult (abs t) (mult (mult (plus one one) (inv_pos (plus one one) req_two_pos)) eps)) (mult eps (abs t)) (req_mult_compat (abs t) (abs t)
   (mult (plus one one) (mult (inv_pos (plus one one) req_two_pos) eps))
   (mult (mult (plus one one) (inv_pos (plus one one) req_two_pos)) eps)
   (req_refl (abs t))
   (mult_assoc (plus one one) (inv_pos (plus one one) req_two_pos) eps)) (req_trans (mult (abs t) (mult (mult (plus one one) (inv_pos (plus one one) req_two_pos)) eps)) (mult (abs t) (mult one eps)) (mult eps (abs t)) (req_mult_compat (abs t) (abs t)
   (mult (mult (plus one one) (inv_pos (plus one one) req_two_pos)) eps)
   (mult one eps)
   (req_refl (abs t))
   (req_mult_compat (mult (plus one one) (inv_pos (plus one one) req_two_pos)) one eps eps
      (inv_pos_correct (plus one one) req_two_pos)
      (req_refl eps))) (req_trans (mult (abs t) (mult one eps)) (mult (abs t) eps) (mult eps (abs t)) (req_mult_compat (abs t) (abs t)
   (mult one eps) eps
   (req_refl (abs t))
   (req_trans (mult one eps) (mult eps one) eps
      (mult_comm one eps) (mult_one eps))) (mult_comm (abs t) eps))))))). }
  assert (HD3 : le (mult (mult t t) (plus one one)) (mult eps (abs t))).
  { apply (le_id_l (mult (mult t t) (plus one one))
                   (plus (mult t t) (mult t t))
                   (mult eps (abs t))).
    apply (req_trans (mult (mult t t) (plus one one))
                     (mult (plus one one) (mult t t))
                     (plus (mult t t) (mult t t))
                     (mult_comm (mult t t) (plus one one))
                     (req_two_mult (mult t t))).
    apply (le_trans (plus (mult t t) (mult t t))
                    (plus (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps))
                          (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                    (mult eps (abs t))).
    - exact (le_plus_compat (mult t t) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps))
                            (mult t t) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps))
                            HH HH).
    - apply (le_id_r (plus (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                     (mult (plus one one) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                     (mult eps (abs t))).
      + exact RING2.
      + apply (le_id_l (plus (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                       (mult (plus one one) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                       (mult (plus one one) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))).
        * exact (req_sym (mult (plus one one) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                         (plus (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                         (req_two_mult (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))).
        * exact (le_refl (mult (plus one one) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))).
  }
  assert (HB2 : le (opp (plus (log (plus one t) H1t) (opp t)))
                   (mult eps (abs t))).
  { exact (le_trans (opp (plus (log (plus one t) H1t) (opp t)))
                    (mult (mult t t) (inv_pos (plus one t) H1t))
                    (mult eps (abs t)) HB1
                    (le_trans (mult (mult t t) (inv_pos (plus one t) H1t))
                              (mult (mult t t) (plus one one))
                              (mult eps (abs t)) HD2 HD3)). }
  exact (lrdf_abs_le_intro (plus (log (plus one t) H1t) (opp t))
           (mult eps (abs t)) HA2 HB2).
Qed.

(* ============================================================ *)

(*   df y := inv y；delta := min(x/2, (eps·x/2)·x)；                            *)
(*   上界 D ≤ 0（req_log_one_plus_le 精确切线）+ 下界 |D| ≤ 2t² ≤ eps·|h|。      *)
(* ============================================================ *)

Theorem lrdf_log_root : forall (Hpos : forall y : R, lt zero y),
  reqRDF (fun y : R => log y (Hpos y)).
Proof.
  intros Hpos.
  exists (fun y : R => inv_pos y (Hpos y)).
  intros x eps Heps.
  assert (Hx : lt zero x) by exact (Hpos x).
  assert (Hdl : lt zero (mult (inv_pos (plus one one) req_two_pos) x)).
  { exact (mult_positive (inv_pos (plus one one) req_two_pos) x (inv_pos_pos (plus one one) req_two_pos) Hx). }
  assert (Hepsx : lt zero (mult eps x)) by exact (mult_positive eps x Heps Hx).
  assert (Hdr : lt zero (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x)).
  { exact (mult_positive (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x
             (mult_positive (inv_pos (plus one one) req_two_pos) (mult eps x)
                (inv_pos_pos (plus one one) req_two_pos) Hepsx)
             Hx). }
  exists (min (mult (inv_pos (plus one one) req_two_pos) x)
              (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x)).
  split.
  - exact (min_pos (mult (inv_pos (plus one one) req_two_pos) x)
                   (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x) Hdl Hdr).
  - intros h Hh.
    assert (Hhl : lt (abs h) (mult (inv_pos (plus one one) req_two_pos) x)).
    { exact (lt_le_trans (abs h)
               (min (mult (inv_pos (plus one one) req_two_pos) x)
                    (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x))
               (mult (inv_pos (plus one one) req_two_pos) x)
               Hh (min_le_l_plain (mult (inv_pos (plus one one) req_two_pos) x)
                     (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x))). }
    assert (Hhr : lt (abs h) (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x)).
    { exact (lt_le_trans (abs h)
               (min (mult (inv_pos (plus one one) req_two_pos) x)
                    (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x))
               (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x)
               Hh (min_le_r_plain (mult (inv_pos (plus one one) req_two_pos) x)
                     (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x))). }
    assert (Ht2 : lt (abs (mult h (inv_pos x Hx))) (inv_pos (plus one one) req_two_pos)).
    { exact (lrdf_t_lt_of x h (inv_pos (plus one one) req_two_pos) Hx Hhl). }
    assert (Hte :
      lt (abs (mult h (inv_pos x Hx))) (mult (inv_pos (plus one one) req_two_pos) (mult eps x))).
    { exact (lrdf_t_lt_of x h (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) Hx Hhr). }
    assert (H1t : lt zero (plus one (mult h (inv_pos x Hx)))).
    { exact (lrdf_abs_lower_pos (mult h (inv_pos x Hx)) one
               (lt_le_trans (abs (mult h (inv_pos x Hx))) (inv_pos (plus one one) req_two_pos) one
                  Ht2 req_rdf_half_le_one)). }
    assert (Hhalf : le (inv_pos (plus one one) req_two_pos) (plus one (mult h (inv_pos x Hx)))).
    { exact (lrdf_half_le_one_t (mult h (inv_pos x Hx)) Ht2). }
    assert (Hm : lt zero (mult x (plus one (mult h (inv_pos x Hx))))).
    { exact (mult_positive x (plus one (mult h (inv_pos x Hx))) Hx H1t). }
    assert (Hxh : lt zero (plus x h)).
    { exact (req_lt_compat zero zero
               (mult x (plus one (mult h (inv_pos x Hx)))) (plus x h)
               (req_refl zero)
               (req_sym (plus x h)
                  (mult x (plus one (mult h (inv_pos x Hx))))
                  (lrdf_xh_eq x h Hx))
               Hm). }
    assert (HEq : req (plus (log (plus x h) Hxh)
                            (opp (plus (log x Hx) (mult (inv_pos x Hx) h))))
                      (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                            (opp (mult h (inv_pos x Hx))))).
    { apply (req_trans (plus (log (plus x h) Hxh)
                             (opp (plus (log x Hx) (mult (inv_pos x Hx) h))))
                       (plus (log (plus x h) Hxh)
                             (plus (opp (log x Hx))
                                   (opp (mult (inv_pos x Hx) h))))
                       (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                             (opp (mult h (inv_pos x Hx))))).
      - exact (req_plus_compat (log (plus x h) Hxh) (log (plus x h) Hxh)
                 (opp (plus (log x Hx) (mult (inv_pos x Hx) h)))
                 (plus (opp (log x Hx)) (opp (mult (inv_pos x Hx) h)))
                 (req_refl (log (plus x h) Hxh))
                 (req_opp_plus (log x Hx) (mult (inv_pos x Hx) h))).
      - apply (req_trans (plus (log (plus x h) Hxh)
                               (plus (opp (log x Hx))
                                     (opp (mult (inv_pos x Hx) h))))
                         (plus (plus (log (plus x h) Hxh) (opp (log x Hx)))
                               (opp (mult (inv_pos x Hx) h)))
                         (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                               (opp (mult h (inv_pos x Hx))))).
        + exact (plus_assoc (log (plus x h) Hxh) (opp (log x Hx))
                            (opp (mult (inv_pos x Hx) h))).
        + apply (req_trans
                   (plus (plus (log (plus x h) Hxh) (opp (log x Hx)))
                         (opp (mult (inv_pos x Hx) h)))
                   (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                         (opp (mult (inv_pos x Hx) h)))
                   (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                         (opp (mult h (inv_pos x Hx))))).
          * apply (req_plus_compat
                     (plus (log (plus x h) Hxh) (opp (log x Hx)))
                     (log (plus one (mult h (inv_pos x Hx))) H1t)
                     (opp (mult (inv_pos x Hx) h))
                     (opp (mult (inv_pos x Hx) h))
                     (req_trans
                        (plus (log (plus x h) Hxh) (opp (log x Hx)))
                        (plus (log (mult x (plus one (mult h (inv_pos x Hx)))) Hm)
                              (opp (log x Hx)))
                        (log (plus one (mult h (inv_pos x Hx))) H1t)
                        (req_plus_compat (log (plus x h) Hxh)
                           (log (mult x (plus one (mult h (inv_pos x Hx)))) Hm)
                           (opp (log x Hx)) (opp (log x Hx))
                           (log_req_compat_plain (plus x h)
                              (mult x (plus one (mult h (inv_pos x Hx))))
                              Hxh Hm (lrdf_xh_eq x h Hx))
                           (req_refl (opp (log x Hx))))
                        (req_trans
                           (plus (log (mult x (plus one (mult h (inv_pos x Hx)))) Hm)
                                 (opp (log x Hx)))
                           (plus (plus (log x Hx)
                                       (log (plus one (mult h (inv_pos x Hx))) H1t))
                                 (opp (log x Hx)))
                           (log (plus one (mult h (inv_pos x Hx))) H1t)
                           (req_plus_compat
                              (log (mult x (plus one (mult h (inv_pos x Hx)))) Hm)
                              (plus (log x Hx)
                                    (log (plus one (mult h (inv_pos x Hx))) H1t))
                              (opp (log x Hx)) (opp (log x Hx))
                              (req_trans
                                 (log (mult x (plus one (mult h (inv_pos x Hx)))) Hm)
                                 (log (mult x (plus one (mult h (inv_pos x Hx))))
                                    (mult_positive x (plus one (mult h (inv_pos x Hx)))
                                       Hx H1t))
                                 (plus (log x Hx)
                                       (log (plus one (mult h (inv_pos x Hx))) H1t))
                                 (log_req_compat_plain
                                    (mult x (plus one (mult h (inv_pos x Hx))))
                                    (mult x (plus one (mult h (inv_pos x Hx)))) Hm
                                    (mult_positive x (plus one (mult h (inv_pos x Hx)))
                                       Hx H1t)
                                    (req_refl
                                       (mult x (plus one (mult h (inv_pos x Hx))))))
                                 (log_mult x (plus one (mult h (inv_pos x Hx))) Hx H1t))
                              (req_refl (opp (log x Hx))))
                           (lrdf_cancel_r (log x Hx)
                              (log (plus one (mult h (inv_pos x Hx))) H1t))))
                     (req_refl (opp (mult (inv_pos x Hx) h)))).
          * exact (req_plus_compat
                     (log (plus one (mult h (inv_pos x Hx))) H1t)
                     (log (plus one (mult h (inv_pos x Hx))) H1t)
                     (opp (mult (inv_pos x Hx) h))
                     (opp (mult h (inv_pos x Hx)))
                     (req_refl (log (plus one (mult h (inv_pos x Hx))) H1t))
                     (req_opp_compat (mult (inv_pos x Hx) h)
                        (mult h (inv_pos x Hx)) (mult_comm (inv_pos x Hx) h))). }
    assert (Hcore :
      le (abs (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                    (opp (mult h (inv_pos x Hx)))))
         (mult (mult eps x) (abs (mult h (inv_pos x Hx))))).
    { exact (lrdf_core_abs_bound (mult h (inv_pos x Hx)) (mult eps x)
               H1t Hhalf
               (lt_le_iff (abs (mult h (inv_pos x Hx)))
                  (mult (inv_pos (plus one one) req_two_pos) (mult eps x))
                  (inl Hte))
               Hepsx). }
    assert (Hscale :
      req (mult (mult eps x) (abs (mult h (inv_pos x Hx))))
          (mult eps (abs h))).
    { apply (req_trans (mult (mult eps x) (abs (mult h (inv_pos x Hx))))
                       (mult (mult eps x) (mult (abs h) (inv_pos x Hx)))
                       (mult eps (abs h))).
      - exact (req_mult_compat (mult eps x) (mult eps x)
                 (abs (mult h (inv_pos x Hx))) (mult (abs h) (inv_pos x Hx))
                 (req_refl (mult eps x))
                 (lrdf_t_abs_eq x h Hx)).
      - apply (req_trans (mult (mult eps x) (mult (abs h) (inv_pos x Hx)))
                         (mult eps (mult (abs h) (mult x (inv_pos x Hx))))
                         (mult eps (abs h))).
        + exact (req_trans (mult (mult eps x) (mult (abs h) (inv_pos x Hx)))
                           (mult eps (mult x (mult (abs h) (inv_pos x Hx))))
                           (mult eps (mult (abs h) (mult x (inv_pos x Hx))))
                           (req_sym (mult eps (mult x (mult (abs h) (inv_pos x Hx))))
                                    (mult (mult eps x) (mult (abs h) (inv_pos x Hx)))
                                    (mult_assoc eps x (mult (abs h) (inv_pos x Hx))))
                           (req_mult_compat eps eps
                              (mult x (mult (abs h) (inv_pos x Hx)))
                              (mult (abs h) (mult x (inv_pos x Hx)))
                              (req_refl eps)
                              (req_trans (mult x (mult (abs h) (inv_pos x Hx)))
                                 (mult (mult (abs h) (inv_pos x Hx)) x)
                                 (mult (abs h) (mult x (inv_pos x Hx)))
                                 (mult_comm x (mult (abs h) (inv_pos x Hx)))
                                 (req_trans (mult (mult (abs h) (inv_pos x Hx)) x)
                                    (mult (abs h) (mult (inv_pos x Hx) x))
                                    (mult (abs h) (mult x (inv_pos x Hx)))
                                    (req_sym (mult (abs h) (mult (inv_pos x Hx) x))
                                             (mult (mult (abs h) (inv_pos x Hx)) x)
                                             (mult_assoc (abs h) (inv_pos x Hx) x))
                                    (req_mult_compat (abs h) (abs h)
                                       (mult (inv_pos x Hx) x)
                                       (mult x (inv_pos x Hx))
                                       (req_refl (abs h))
                                       (mult_comm (inv_pos x Hx) x)))))).
        + apply (req_trans (mult eps (mult (abs h) (mult x (inv_pos x Hx))))
                           (mult eps (mult (abs h) one))
                           (mult eps (abs h))).
          * exact (req_mult_compat eps eps
                     (mult (abs h) (mult x (inv_pos x Hx)))
                     (mult (abs h) one)
                     (req_refl eps)
                     (req_mult_compat (abs h) (abs h)
                        (mult x (inv_pos x Hx)) one
                        (req_refl (abs h)) (inv_pos_correct x Hx))).
          * exact (req_mult_compat eps eps (mult (abs h) one) (abs h)
                     (req_refl eps) (mult_one (abs h))). }
    exact (le_id_l
             (abs (req_minus (log (plus x h) (Hpos (plus x h)))
                     (plus (log x (Hpos x)) (mult (inv_pos x (Hpos x)) h))))
             (abs (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                        (opp (mult h (inv_pos x Hx)))))
             (mult eps (abs h))
             (req_abs_compat
                (req_minus (log (plus x h) (Hpos (plus x h)))
                   (plus (log x (Hpos x)) (mult (inv_pos x (Hpos x)) h)))
                (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                      (opp (mult h (inv_pos x Hx))))
                (req_trans
                   (req_minus (log (plus x h) (Hpos (plus x h)))
                      (plus (log x (Hpos x)) (mult (inv_pos x (Hpos x)) h)))
                   (plus (log (plus x h) Hxh)
                         (opp (plus (log x Hx) (mult (inv_pos x Hx) h))))
                   (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                         (opp (mult h (inv_pos x Hx))))
                   (req_plus_compat
                      (log (plus x h) (Hpos (plus x h)))
                      (log (plus x h) Hxh)
                      (opp (plus (log x (Hpos x)) (mult (inv_pos x (Hpos x)) h)))
                      (opp (plus (log x Hx) (mult (inv_pos x Hx) h)))
                      (log_req_compat_plain (plus x h) (plus x h)
                         (Hpos (plus x h)) Hxh (req_refl (plus x h)))
                      (req_opp_compat
                         (plus (log x (Hpos x)) (mult (inv_pos x (Hpos x)) h))
                         (plus (log x Hx) (mult (inv_pos x Hx) h))
                         (req_plus_compat
                            (log x (Hpos x)) (log x Hx)
                            (mult (inv_pos x (Hpos x)) h) (mult (inv_pos x Hx) h)
                            (log_req_compat_plain x x (Hpos x) Hx (req_refl x))
                            (req_mult_compat (inv_pos x (Hpos x)) (inv_pos x Hx)
                               h h
                               (inv_pos_ext x x (Hpos x) Hx (req_refl x))
                               (req_refl h)))))
                   HEq))
             (le_id_r
                (abs (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                           (opp (mult h (inv_pos x Hx)))))
                (mult (mult eps x) (abs (mult h (inv_pos x Hx))))
                (mult eps (abs h)) Hscale Hcore)).
Qed.
(* ============================================================ *)


(*   df z := inv(g z)·dg z；tt := (g(z+h)−g z)·inv(g z)；                      *)
(*   误差 ≡ X + err·inv（lrdf_opp_split_eq 分裂）；budget 双 (eps/2)|h|。      *)
(* ============================================================ *)

Theorem lrdf_rdf_log_diff :
  forall (g : R -> R) (Hg : forall y : R, lt zero (g y)) (dg : reqRDF g),
    reqRDF (fun z : R => log (g z) (Hg z)).
Proof.
  intros g Hg dg.
  exists (fun z : R => mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)).
  intros z eps Heps.
  assert (Hs : lt zero (g z)) by exact (Hg z).
  assert (Hef : lt zero (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))).
  { exact (mult_positive (mult (inv_pos (plus one one) req_two_pos) eps) (g z)
             (req_rdf_half_pos eps Heps) Hs). }
  destruct (rdf_correct g dg z
              (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)) Hef)
    as [d1 [Hd1 Hd2]].
  assert (HK : lt zero
    (mult (plus (abs (rdf_df g dg z))
                (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)))
          (inv_pos (g z) (Hg z)))).
  { exact (mult_positive
             (plus (abs (rdf_df g dg z))
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)))
             (inv_pos (g z) (Hg z))
             (req_plus_le_lt_pos (abs (rdf_df g dg z))
                (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))
                (abs_nonneg_plain (rdf_df g dg z)) Hef)
             (inv_pos_pos (g z) (Hg z))). }
  assert (HKinv : lt zero
    (inv_pos (mult (plus (abs (rdf_df g dg z))
                       (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)))
                 (inv_pos (g z) (Hg z))) HK)).
  { exact (inv_pos_pos (mult (plus (abs (rdf_df g dg z))
                                 (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                       (g z)))
                            (inv_pos (g z) (Hg z))) HK). }
  assert (HepsX : lt zero
    (mult (mult (inv_pos (plus one one) req_two_pos) eps)
          (inv_pos (mult (plus (abs (rdf_df g dg z))
                             (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)))
                       (inv_pos (g z) (Hg z))) HK))).
  { exact (mult_positive (mult (inv_pos (plus one one) req_two_pos) eps)
             (inv_pos (mult (plus (abs (rdf_df g dg z))
                                (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                      (g z)))
                          (inv_pos (g z) (Hg z))) HK)
             (req_rdf_half_pos eps Heps) HKinv). }
  assert (Hda : lt zero
    (mult (mult (inv_pos (plus one one) req_two_pos)
                (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                      (inv_pos (mult (plus (abs (rdf_df g dg z))
                                         (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                               (g z)))
                                    (inv_pos (g z) (Hg z))) HK)))
                (inv_pos (mult (plus (abs (rdf_df g dg z))
                                   (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                         (g z)))
                              (inv_pos (g z) (Hg z))) HK))).
  { exact (mult_positive
             (mult (inv_pos (plus one one) req_two_pos)
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                         (inv_pos (mult (plus (abs (rdf_df g dg z))
                                            (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                  (g z)))
                                       (inv_pos (g z) (Hg z))) HK)))
             (inv_pos (mult (plus (abs (rdf_df g dg z))
                                (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                      (g z)))
                          (inv_pos (g z) (Hg z))) HK)
             (mult_positive (inv_pos (plus one one) req_two_pos)
                (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                      (inv_pos (mult (plus (abs (rdf_df g dg z))
                                         (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                               (g z)))
                                    (inv_pos (g z) (Hg z))) HK))
                (inv_pos_pos (plus one one) req_two_pos) HepsX)
             HKinv). }
  assert (Hdpos : lt zero
    (mult (inv_pos (plus one one) req_two_pos)
          (inv_pos (mult (plus (abs (rdf_df g dg z))
                             (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)))
                       (inv_pos (g z) (Hg z))) HK))).
  { exact (mult_positive (inv_pos (plus one one) req_two_pos)
             (inv_pos (mult (plus (abs (rdf_df g dg z))
                                (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                      (g z)))
                          (inv_pos (g z) (Hg z))) HK)
             (inv_pos_pos (plus one one) req_two_pos) HKinv). }
  exists (min (min d1
                  (mult (mult (inv_pos (plus one one) req_two_pos)
                              (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                    (inv_pos (mult (plus (abs (rdf_df g dg z))
                                                       (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                             (g z)))
                                                  (inv_pos (g z) (Hg z))) HK)))
                        (inv_pos (mult (plus (abs (rdf_df g dg z))
                                           (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                 (g z)))
                                      (inv_pos (g z) (Hg z))) HK)))
                  (mult (inv_pos (plus one one) req_two_pos)
                        (inv_pos (mult (plus (abs (rdf_df g dg z))
                                           (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                 (g z)))
                                      (inv_pos (g z) (Hg z))) HK))).
  split.
  - exact (min_pos (min d1
                       (mult (mult (inv_pos (plus one one) req_two_pos)
                                   (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                         (inv_pos (mult (plus (abs (rdf_df g dg z))
                                                            (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                                  (g z)))
                                                       (inv_pos (g z) (Hg z))) HK)))
                         (inv_pos (mult (plus (abs (rdf_df g dg z))
                                            (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                  (g z)))
                                       (inv_pos (g z) (Hg z))) HK)))
                   (mult (inv_pos (plus one one) req_two_pos)
                         (inv_pos (mult (plus (abs (rdf_df g dg z))
                                            (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                  (g z)))
                                       (inv_pos (g z) (Hg z))) HK))
                   (min_pos d1
                      (mult (mult (inv_pos (plus one one) req_two_pos)
                                  (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                        (inv_pos (mult (plus (abs (rdf_df g dg z))
                                                           (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                                 (g z)))
                                                      (inv_pos (g z) (Hg z))) HK)))
                        (inv_pos (mult (plus (abs (rdf_df g dg z))
                                           (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                 (g z)))
                                      (inv_pos (g z) (Hg z))) HK))
                      Hd1 Hda)
                   Hdpos).
  - intros h Hh.
    assert (Hh_d1 : lt (abs h) d1).
    { exact (lt_le_trans (abs h) (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) d1
               (lt_le_trans (abs h) (min (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                  Hh (min_le_l_plain (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))))
               (min_le_l_plain d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))). }
    assert (Hh_da : lt (abs h) (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))).
    { exact (lt_le_trans (abs h) (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
               (lt_le_trans (abs h) (min (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                  Hh (min_le_l_plain (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))))
               (min_le_r_plain d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))). }
    assert (Hh_dp : lt (abs h) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))).
    { exact (lt_le_trans (abs h) (min (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
               Hh (min_le_r_plain (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))). }
    assert (He : le (abs (req_minus (g (plus z h)) (g z))) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (abs h))).
    { exact (req_rdf_delta_bound (g (plus z h)) (g z) (rdf_df g dg z)
               (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)) h (Hd2 h Hh_d1)). }

    assert (RINGKa : req (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))).
    { exact (req_trans (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                 (mult (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                 (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                 (mult_assoc (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                 (req_trans (mult (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                    (mult (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                    (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                    (req_mult_compat (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))) (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)
                       (mult_comm (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))) (req_refl (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                    (req_trans (mult (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                       (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                       (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                       (req_sym (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                          (mult (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                          (mult_assoc (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                       (req_trans (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                          (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) one)
                          (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                          (req_mult_compat (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) one
                             (req_refl (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))) (inv_pos_correct (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                          (mult_one (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))))))). }

    assert (RINGKd : req (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (plus one one) req_two_pos)).
    { exact (req_trans (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                 (mult (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (plus one one) req_two_pos)) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                 (inv_pos (plus one one) req_two_pos)
                 (mult_assoc (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                 (req_trans (mult (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (plus one one) req_two_pos)) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                    (mult (mult (inv_pos (plus one one) req_two_pos) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                    (inv_pos (plus one one) req_two_pos)
                    (req_mult_compat (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (plus one one) req_two_pos)) (mult (inv_pos (plus one one) req_two_pos) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)
                       (mult_comm (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (plus one one) req_two_pos)) (req_refl (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                    (req_trans (mult (mult (inv_pos (plus one one) req_two_pos) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                       (mult (inv_pos (plus one one) req_two_pos) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                       (inv_pos (plus one one) req_two_pos)
                       (req_sym (mult (inv_pos (plus one one) req_two_pos) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                          (mult (mult (inv_pos (plus one one) req_two_pos) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                          (mult_assoc (inv_pos (plus one one) req_two_pos) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                       (req_trans (mult (inv_pos (plus one one) req_two_pos) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                          (mult (inv_pos (plus one one) req_two_pos) one)
                          (inv_pos (plus one one) req_two_pos)
                          (req_mult_compat (inv_pos (plus one one) req_two_pos) (inv_pos (plus one one) req_two_pos) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) one
                             (req_refl (inv_pos (plus one one) req_two_pos)) (inv_pos_correct (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                          (mult_one (inv_pos (plus one one) req_two_pos)))))). }

    assert (HtK : le (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))).
    { exact (le_id_l (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                (mult (abs (req_minus (g (plus z h)) (g z))) (inv_pos (g z) (Hg z)))
                (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                (lrdf_t_abs_eq (g z) (req_minus (g (plus z h)) (g z)) (Hg z))
                (le_id_r (mult (abs (req_minus (g (plus z h)) (g z))) (inv_pos (g z) (Hg z)))
                   (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (abs h)) (inv_pos (g z) (Hg z)))
                   (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                   (req_trans (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (abs h)) (inv_pos (g z) (Hg z)))
                      (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (mult (abs h) (inv_pos (g z) (Hg z))))
                      (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                      (req_sym (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (mult (abs h) (inv_pos (g z) (Hg z))))
                         (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (abs h)) (inv_pos (g z) (Hg z)))
                         (mult_assoc (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (abs h) (inv_pos (g z) (Hg z))))
                      (req_trans (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (mult (abs h) (inv_pos (g z) (Hg z))))
                         (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (mult (inv_pos (g z) (Hg z)) (abs h)))
                         (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                         (req_mult_compat (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (mult (abs h) (inv_pos (g z) (Hg z))) (mult (inv_pos (g z) (Hg z)) (abs h))
                            (req_refl (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)))) (mult_comm (abs h) (inv_pos (g z) (Hg z))))
                         (mult_assoc (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)) (abs h))))
                   (le_mult_compat (abs (req_minus (g (plus z h)) (g z)))
                      (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (abs h)) (inv_pos (g z) (Hg z)) (inv_pos_pos (g z) (Hg z)) He))). }
    assert (Hb_core : le (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                        (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))).
    { exact (lt_le_iff (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
               (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
               (inl (lt_id_r (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                       (mult (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                       (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                       (req_trans (mult (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                          (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                          (mult_comm (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) RINGKa)
                       (le_lt_trans (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                          (mult (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                          (mult (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                          (le_id_r (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                             (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                             (mult (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                             (req_sym (mult (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                                (mult_comm (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))))
                             HtK)
                          (lt_mult_compat (abs h) (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK Hh_da))))). }
    assert (Hlt_i2 : lt (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) (inv_pos (plus one one) req_two_pos)).
    { exact (lt_id_r (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
               (mult (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
               (inv_pos (plus one one) req_two_pos)
               (req_trans (mult (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (plus one one) req_two_pos)
                  (mult_comm (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) RINGKd)
               (le_lt_trans (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                  (mult (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                  (mult (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                  (le_id_r (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                     (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                     (mult (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                     (req_sym (mult (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                        (mult_comm (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))))
                     HtK)
                  (lt_mult_compat (abs h) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK Hh_dp))). }

    assert (Htt_split : req (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))) (plus (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h) (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))).
    { exact (req_trans (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))
                (mult (plus (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (mult (rdf_df g dg z) h)) (inv_pos (g z) (Hg z)))
                (plus (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h) (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                (req_mult_compat (req_minus (g (plus z h)) (g z)) (plus (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (mult (rdf_df g dg z) h)) (inv_pos (g z) (Hg z)) (inv_pos (g z) (Hg z))
                   (req_minus_split (g (plus z h)) (g z) (mult (rdf_df g dg z) h)) (req_refl (inv_pos (g z) (Hg z))))
                (req_trans (mult (plus (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (mult (rdf_df g dg z) h)) (inv_pos (g z) (Hg z)))
                   (mult (inv_pos (g z) (Hg z)) (plus (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (mult (rdf_df g dg z) h)))
                   (plus (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h) (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                   (mult_comm (plus (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (mult (rdf_df g dg z) h)) (inv_pos (g z) (Hg z)))
                   (req_trans (mult (inv_pos (g z) (Hg z)) (plus (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (mult (rdf_df g dg z) h)))
                      (plus (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (mult (inv_pos (g z) (Hg z)) (mult (rdf_df g dg z) h)))
                      (plus (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h) (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                      (distrib (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (mult (rdf_df g dg z) h))
                      (req_trans (plus (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (mult (inv_pos (g z) (Hg z)) (mult (rdf_df g dg z) h)))
                         (plus (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))
                         (plus (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h) (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                         (req_plus_compat (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (mult (inv_pos (g z) (Hg z)) (mult (rdf_df g dg z) h)) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)
                            (req_refl (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))) (mult_assoc (inv_pos (g z) (Hg z)) (rdf_df g dg z) h))
                         (plus_comm (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))))). }
    assert (H1t : lt zero (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))).
    { exact (lrdf_abs_lower_pos (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))) one
               (lt_le_trans (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                  (inv_pos (plus one one) req_two_pos) one Hlt_i2 req_rdf_half_le_one)). }
    assert (Hhalf : le (inv_pos (plus one one) req_two_pos)
                        (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))).
    { exact (lrdf_half_le_one_t (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))) Hlt_i2). }
    assert (Hprod : req (g (plus z h))
                        (mult (g z) (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))).
    { exact (req_trans (g (plus z h))
               (plus (g z) (req_minus (g (plus z h)) (g z)))
               (mult (g z) (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
               (lrdf_plus_minus (g (plus z h)) (g z))
               (lrdf_s_plus_eq (g z) (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))
                  (inv_pos_correct (g z) (Hg z)))). }
    assert (Hlogchain : req (plus (log (g (plus z h)) (Hg (plus z h))) (opp (log (g z) (Hg z))))
                            (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)).
    { exact (req_trans
               (plus (log (g (plus z h)) (Hg (plus z h))) (opp (log (g z) (Hg z))))
               (plus (log (mult (g z) (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                        (mult_positive (g z)
                           (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                           (Hg z) H1t))
                     (opp (log (g z) (Hg z))))
               (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
               (req_plus_compat (log (g (plus z h)) (Hg (plus z h)))
                  (log (mult (g z) (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                     (mult_positive (g z)
                        (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                        (Hg z) H1t))
                  (opp (log (g z) (Hg z))) (opp (log (g z) (Hg z)))
                  (log_req_compat_plain (g (plus z h))
                     (mult (g z) (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                     (Hg (plus z h))
                     (mult_positive (g z)
                        (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                        (Hg z) H1t)
                     Hprod)
                  (req_refl (opp (log (g z) (Hg z)))))
               (req_trans
                  (plus (log (mult (g z) (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                           (mult_positive (g z)
                              (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                              (Hg z) H1t))
                        (opp (log (g z) (Hg z))))
                  (plus (plus (log (g z) (Hg z))
                              (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t))
                        (opp (log (g z) (Hg z))))
                  (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                  (req_plus_compat
                     (log (mult (g z) (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                        (mult_positive (g z)
                           (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                           (Hg z) H1t))
                     (plus (log (g z) (Hg z))
                           (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t))
                     (opp (log (g z) (Hg z))) (opp (log (g z) (Hg z)))
                     (log_mult (g z)
                        (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                        (Hg z) H1t)
                     (req_refl (opp (log (g z) (Hg z)))))
                  (lrdf_cancel_r (log (g z) (Hg z))
                     (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)))). }
    assert (HEq : req (plus (log (g (plus z h)) (Hg (plus z h)))
                            (opp (plus (log (g z) (Hg z)) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))))
                      (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                                  (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                            (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))).
    { exact (req_trans
               (plus (log (g (plus z h)) (Hg (plus z h)))
                     (opp (plus (log (g z) (Hg z)) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))))
               (plus (log (g (plus z h)) (Hg (plus z h)))
                     (plus (opp (log (g z) (Hg z))) (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))))
               (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                           (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                     (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
               (req_plus_compat (log (g (plus z h)) (Hg (plus z h))) (log (g (plus z h)) (Hg (plus z h)))
                  (opp (plus (log (g z) (Hg z)) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
                  (plus (opp (log (g z) (Hg z))) (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
                  (req_refl (log (g (plus z h)) (Hg (plus z h))))
                  (req_opp_plus (log (g z) (Hg z)) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
               (req_trans
                  (plus (log (g (plus z h)) (Hg (plus z h)))
                        (plus (opp (log (g z) (Hg z))) (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))))
                  (plus (plus (log (g (plus z h)) (Hg (plus z h))) (opp (log (g z) (Hg z))))
                        (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
                  (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                              (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                        (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                  (plus_assoc (log (g (plus z h)) (Hg (plus z h))) (opp (log (g z) (Hg z)))
                     (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
                  (req_trans
                     (plus (plus (log (g (plus z h)) (Hg (plus z h))) (opp (log (g z) (Hg z))))
                           (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
                     (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                           (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
                     (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                                 (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                           (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                     (req_plus_compat
                        (plus (log (g (plus z h)) (Hg (plus z h))) (opp (log (g z) (Hg z))))
                        (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                        (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))
                        (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))
                        Hlogchain
                        (req_refl (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))))
                     (req_trans
                        (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                              (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
                        (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                              (plus (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                                    (mult (inv_pos (g z) (Hg z))
                                          (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))))
                        (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                                    (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                              (mult (inv_pos (g z) (Hg z))
                                    (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                        (req_plus_compat
                           (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                           (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                           (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))
                           (plus (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                                 (mult (inv_pos (g z) (Hg z))
                                       (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                           (req_refl (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t))
                           (lrdf_opp_split_eq (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)
                              (mult (inv_pos (g z) (Hg z))
                                    (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))
                              (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))
                              Htt_split))
                        (plus_assoc
                           (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                           (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                           (mult (inv_pos (g z) (Hg z))
                                 (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))))))). }
    assert (HX : le (abs (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                               (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))))
                    (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                (inv_pos (mult (plus (abs (rdf_df g dg z))
                                                   (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                         (g z)))
                                              (inv_pos (g z) (Hg z))) HK))
                          (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))).
    { exact (lrdf_core_abs_bound (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))
               (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                     (inv_pos (mult (plus (abs (rdf_df g dg z))
                                        (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                              (g z)))
                                 (inv_pos (g z) (Hg z))) HK))
               H1t Hhalf Hb_core HepsX). }
    assert (HX2 : le (abs (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t) (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))))
                     (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))).
    { exact (le_trans
                (abs (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t) (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))))
                (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                HX
                (le_trans
                   (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                   (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h)))
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                   (req_le_mult_compat_r (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                      (lt_le_iff zero (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (inl HepsX)) HtK)
                   (le_id_l
                      (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h)))
                      (mult (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (abs h))
                      (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                      (mult_assoc (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                      (le_id_l
                         (mult (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (abs h))
                         (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))) (abs h))
                         (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                         (req_mult_compat (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                            (mult (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))))
                            (abs h) (abs h)
                            (req_sym (mult (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))))
                               (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                               (mult_assoc (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))))
                            (req_refl (abs h)))
                         (le_id_l
                            (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))) (abs h))
                            (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) one) (abs h))
                            (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                            (req_mult_compat
                               (mult (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))))
                               (mult (mult (inv_pos (plus one one) req_two_pos) eps) one)
                               (abs h) (abs h)
                               (req_mult_compat (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) one
                                  (req_refl (mult (inv_pos (plus one one) req_two_pos) eps))
                                  (req_trans (mult (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) one
                                     (mult_comm (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                                     (inv_pos_correct (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                               (req_refl (abs h)))
                            (le_id_l
                               (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) one) (abs h))
                               (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                               (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                               (req_mult_compat (mult (mult (inv_pos (plus one one) req_two_pos) eps) one)
                                  (mult (inv_pos (plus one one) req_two_pos) eps)
                                  (abs h) (abs h)
                                  (mult_one (mult (inv_pos (plus one one) req_two_pos) eps))
                                  (req_refl (abs h)))
                               (le_refl (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))))))))). }
    assert (HB : le (abs (mult (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (inv_pos (g z) (Hg z))))
                    (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))).
    { exact (le_id_l
                (abs (mult (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (inv_pos (g z) (Hg z))))
                (mult (abs (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (inv_pos (g z) (Hg z)))
                (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                (lrdf_t_abs_eq (g z) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (Hg z))
                (le_trans
                   (mult (abs (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (inv_pos (g z) (Hg z)))
                   (mult (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)) (abs h))
                         (inv_pos (g z) (Hg z)))
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                   (le_mult_compat (abs (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))
                      (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)) (abs h))
                      (inv_pos (g z) (Hg z)) (inv_pos_pos (g z) (Hg z)) (Hd2 h Hh_d1))
                   (le_id_l
                      (mult (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)) (abs h))
                            (inv_pos (g z) (Hg z)))
                      (mult (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))
                                  (inv_pos (g z) (Hg z)))
                            (abs h))
                      (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                      (lrdf_mul_h_inv (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))
                         (abs h) (inv_pos (g z) (Hg z)))
                      (le_id_l
                         (mult (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))
                                     (inv_pos (g z) (Hg z)))
                               (abs h))
                         (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                         (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                         (req_mult_compat
                            (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))
                                  (inv_pos (g z) (Hg z)))
                            (mult (inv_pos (plus one one) req_two_pos) eps)
                            (abs h) (abs h)
                            (lrdf_mul_inv_one (mult (inv_pos (plus one one) req_two_pos) eps) (g z)
                               (inv_pos (g z) (Hg z)) (inv_pos_correct (g z) (Hg z)))
                            (req_refl (abs h)))
                         (le_refl (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))))))). }
    exact (le_id_l
              (abs (plus (log (g (plus z h)) (Hg (plus z h)))
                         (opp (plus (log (g z) (Hg z)) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))))
              (abs (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                               (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                         (mult (inv_pos (g z) (Hg z))
                               (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))))
              (mult eps (abs h))
              (req_abs_compat
                 (plus (log (g (plus z h)) (Hg (plus z h)))
                       (opp (plus (log (g z) (Hg z)) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))))
                 (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                             (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                       (mult (inv_pos (g z) (Hg z))
                             (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                 HEq)
              (le_trans
                 (abs (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                                  (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                            (mult (inv_pos (g z) (Hg z))
                                  (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))))
                 (plus (abs (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                                  (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))))
                       (abs (mult (inv_pos (g z) (Hg z))
                                  (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))))
                 (mult eps (abs h))
                 (req_rdf_abs_triangle
                    (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                          (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                    (mult (inv_pos (g z) (Hg z))
                          (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                 (le_trans
                    (plus (abs (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                                     (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))))
                          (abs (mult (inv_pos (g z) (Hg z))
                                     (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))))
                    (plus (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                          (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h)))
                    (mult eps (abs h))
                    (le_plus_compat (abs (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t) (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))))
                       (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                       (abs (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                       (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h)) HX2 (le_id_l (abs (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))) (abs (mult (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (inv_pos (g z) (Hg z)))) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                       (req_abs_compat (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (mult (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (inv_pos (g z) (Hg z)))
                          (mult_comm (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                       HB))
                    (le_id_l (plus (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                                   (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h)))
                       (mult eps (abs h)) (mult eps (abs h))
                       (req_trans (plus (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                                        (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h)))
                                  (plus (mult (inv_pos (plus one one) req_two_pos) (mult eps (abs h)))
                                        (mult (inv_pos (plus one one) req_two_pos) (mult eps (abs h))))
                                  (mult eps (abs h))
                                  (req_plus_compat (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                                     (mult (inv_pos (plus one one) req_two_pos) (mult eps (abs h)))
                                     (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                                     (mult (inv_pos (plus one one) req_two_pos) (mult eps (abs h)))
                                     (req_sym (mult (inv_pos (plus one one) req_two_pos) (mult eps (abs h)))
                                        (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                                        (mult_assoc (inv_pos (plus one one) req_two_pos) eps (abs h)))
                                     (req_sym (mult (inv_pos (plus one one) req_two_pos) (mult eps (abs h)))
                                        (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                                        (mult_assoc (inv_pos (plus one one) req_two_pos) eps (abs h))))
                                  (req_half_twice (mult eps (abs h)) req_two_pos))
                       (le_refl (mult eps (abs h))))))).
Qed.

End LRDF.

(* ============================ §2 QltT / QltT / Qlt_to_QltT 语句面 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               ZArith.ZArith Arith.Arith Bool.Bool Lists.List.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ============================================================ *)
(* §0 Set 层出口件：QltT'（Qlt_bool 反映形，Id-of-bool，同 QltT） *)
(* ============================================================ *)
(* 库内已有 QltT/QleT'（S02）；本件按同形语句面命名补 QltT'。      *)

Definition QltT' (x y : Q) : Set := Id (Qlt_bool x y) true.

Lemma QltT'_to_Qlt : forall x y : Q, QltT' x y -> Qlt x y.
Proof. intros x y H. apply (QltT_to_Qlt x y). exact H. Qed.

Lemma Qlt_to_QltT' : forall x y : Q, Qlt x y -> QltT' x y.
Proof. intros x y H. exact (Qlt_to_QltT x y H). Qed.

Lemma qleT'_weaken : forall a b c : Q, Qle a b -> b == c -> QleT' a c.
Proof.
  intros a b c H Hbc.
  apply Qle_to_QleT'.
  apply (Qle_trans a b c H).
  apply qeq_le.
  exact Hbc.
Qed.

(* ============================================================ *)
(* §1 定义（四段式之一：定义）                                    *)
(* ============================================================ *)

(* ---- 项 t_k := (−1)^k/(k+1) ---- *)
Definition l2e_term (k : nat) : Q :=
  q_pow (-1) k / (Z.of_nat (Datatypes.S k) # 1).

(* ---- 部分和 S_n := Σ_{k=0}^{n−1} t_k（n 项） ---- *)
Fixpoint l2e_alt_partial (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S m => l2e_alt_partial m + l2e_term m
  end.

(* ---- 项模量 m_k := 1/(k+1)（|t_k| 的闭式；对照 atan_mag） ---- *)
Definition l2e_mag (k : nat) : Q := 1 / (Z.of_nat (Datatypes.S k) # 1).

(* ---- 一步差：S_{n+1} − S_n == t_n；两步差 S_{n+2} − S_n == t_n + t_{n+1} ---- *)
Lemma l2e_gap1 : forall n : nat,
  l2e_alt_partial (Datatypes.S n) - l2e_alt_partial n == l2e_term n.
Proof. intro n. simpl. ring. Qed.

Lemma l2e_gap2 : forall n : nat,
  l2e_alt_partial (Datatypes.S (Datatypes.S n)) - l2e_alt_partial n ==
  l2e_term n + l2e_term (Datatypes.S n).
Proof. intro n. simpl. ring. Qed.

(* ============================================================ *)
(* §2 模量序结构（四段式之二/之三：恒等 + 单调）                   *)
(* ============================================================ *)

Lemma l2e_den_pos : forall k : nat, Qlt 0 (Z.of_nat (Datatypes.S k) # 1).
Proof.
  intro k. unfold Qlt. cbn [Qnum Qden].
  (* Z 层化：乘积归约后 Z.of_nat (S k) 依定义化为 Z.pos (Pos.of_succ_nat *)
  (* k)，取正性见证 Pos2Z.pos_is_pos                                    *)
  rewrite Z.mul_0_l, Z.mul_1_r.
  change (Z.of_nat (Datatypes.S k)) with (Z.pos (Pos.of_succ_nat k)).
  apply Pos2Z.pos_is_pos.
Qed.

Lemma l2e_den_neq : forall k : nat, ~ ((Z.of_nat (Datatypes.S k) # 1) == 0).
Proof. intro k. apply q_neq_of_lt. apply l2e_den_pos. Qed.

(* ---- 1/d == /d 桥（Qdiv 展平） ---- *)
Lemma l2e_mag_inv : forall k : nat, l2e_mag k == / (Z.of_nat (Datatypes.S k) # 1).
Proof. intro k. unfold l2e_mag, Qdiv. apply Qmult_1_l. Qed.

Lemma l2e_mag_pos : forall k : nat, Qlt 0 (l2e_mag k).
Proof.
  intro k.
  setoid_replace (l2e_mag k) with (/ (Z.of_nat (Datatypes.S k) # 1))
    by (apply (l2e_mag_inv k)).
  apply Qinv_lt_0_compat.
  apply l2e_den_pos.
Qed.

Lemma l2e_mag_nonneg : forall k : nat, Qle 0 (l2e_mag k).
Proof.
  intro k.
  apply (Qlt_le_weak 0 (l2e_mag k)).
  apply l2e_mag_pos.
Qed.

(* ---- 严格递减：m_{k+1} < m_k（倒数反序；对照 atan_mag_decr 证明芯） ---- *)
Lemma l2e_mag_lt : forall k : nat, Qlt (l2e_mag (Datatypes.S k)) (l2e_mag k).
Proof.
  intro k.
  setoid_replace (l2e_mag (Datatypes.S k)) with (/ (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1))
    by (apply (l2e_mag_inv (Datatypes.S k))).
  setoid_replace (l2e_mag k) with (/ (Z.of_nat (Datatypes.S k) # 1))
    by (apply (l2e_mag_inv k)).
  apply (proj1 (Qinv_lt_contravar (Z.of_nat (Datatypes.S k) # 1)
                                  (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)
                                  (l2e_den_pos k) (l2e_den_pos (Datatypes.S k)))).
  (* 收束：倒数反序的核=S k < S (S k)，Z 层由 inj_succ 化为后继一步严格序 *)
  unfold Qlt. cbn [Qnum Qden].
  rewrite (Znat.Nat2Z.inj_succ (Datatypes.S k)), !Z.mul_1_r.
  exact (Z.lt_succ_diag_r (Z.of_nat (Datatypes.S k))).
Qed.

(* ---- 模量差为正：m_k − m_{k+1} > 0 ---- *)
Lemma l2e_pair_diff_pos : forall k : nat,
  Qlt 0 (l2e_mag k - l2e_mag (Datatypes.S k)).
Proof.
  intro k.
  apply (proj1 (Qlt_minus_iff (l2e_mag (Datatypes.S k)) (l2e_mag k))).
  apply l2e_mag_lt.
Qed.

(* ---- 模量反序（N ≤ M ⟹ m_M ≤ m_N；对照 atan_inv_chain） ---- *)
Lemma l2e_mag_antitone : forall a b : nat, (a <= b)%nat -> Qle (l2e_mag b) (l2e_mag a).
Proof.
  intros a b Hab.
  destruct (Nat.eq_dec a b) as [Heq | Hne].
  - subst b. apply Qle_refl.
  - assert (Hlt : (a < b)%nat) by lia.
    apply (Qle_trans _ (/ (Z.of_nat (Datatypes.S b) # 1)) _).
    + apply qeq_le. apply (l2e_mag_inv b).
    + apply Qlt_le_weak.
      setoid_replace (l2e_mag a) with (/ (Z.of_nat (Datatypes.S a) # 1))
        by (apply (l2e_mag_inv a)).
      apply (proj1 (Qinv_lt_contravar (Z.of_nat (Datatypes.S a) # 1)
                                      (Z.of_nat (Datatypes.S b) # 1)
                                      (l2e_den_pos a) (l2e_den_pos b))).
      (* 收束：a < b 经后继单调（Z.succ_lt_mono）平移到 Z 层分母序 *)
      unfold Qlt. cbn [Qnum Qden]. rewrite !Znat.Nat2Z.inj_succ, !Z.mul_1_r.
      exact (proj1 (Z.succ_lt_mono (Z.of_nat a) (Z.of_nat b))
                   (proj1 (Znat.Nat2Z.inj_lt a b) Hlt)).
Qed.

(* ---- 单调：m_{k+1} ≤ m_k（对照 atan_mag_decr） ---- *)
Lemma l2e_mag_decr : forall k : nat, Qle (l2e_mag (Datatypes.S k)) (l2e_mag k).
Proof. intro k. apply l2e_mag_antitone. lia. Qed.

Lemma l2e_mag_decr_pos_step : forall n : nat, Qle 0 (l2e_mag n - l2e_mag (Datatypes.S n)).
Proof.
  intro n.
  apply (proj1 (Qle_minus_iff (l2e_mag (Datatypes.S n)) (l2e_mag n))).
  apply l2e_mag_decr.
Qed.

(* ============================================================ *)
(* §3 项恒等（|t_k|==m_k；成对项 |t_k+t_{k+1}|==m_k−m_{k+1}）      *)
(* ============================================================ *)

(* ---- |t_k| == m_k（对照 arctan_term_abs） ---- *)
Lemma l2e_term_abs : forall k : nat, Qabs (l2e_term k) == l2e_mag k.
Proof.
  intro k.
  unfold l2e_term, Qdiv.
  setoid_rewrite Qabs_Qmult.
  setoid_rewrite sc_abs_sign.
  setoid_rewrite Qabs_Qinv.
  assert (Hd : Qabs (Z.of_nat (Datatypes.S k) # 1) ==
               (Z.of_nat (Datatypes.S k) # 1)).
  { apply Qabs_pos. apply Qlt_le_weak. apply l2e_den_pos. }
  setoid_rewrite Hd.
  unfold l2e_mag, Qdiv.
  ring.
Qed.

(* ---- 成对项代数分解（对照 atan_pair_factor） ---- *)
Lemma l2e_pair_factor : forall k : nat,
  l2e_term k + l2e_term (Datatypes.S k) ==
  q_pow (-1) k * (l2e_mag k - l2e_mag (Datatypes.S k)).
Proof.
  intro k.
  unfold l2e_term, l2e_mag, Qdiv.
  rewrite (q_pow_succ (-1) k).
  ring.
Qed.

(* ---- 成对项界：|t_k + t_{k+1}| == m_k − m_{k+1}（对照 atan_pair_abs） ---- *)
Lemma l2e_pair_abs : forall k : nat,
  Qabs (l2e_term k + l2e_term (Datatypes.S k)) ==
  l2e_mag k - l2e_mag (Datatypes.S k).
Proof.
  intro k.
  apply (Qeq_trans _ (Qabs (q_pow (-1) k * (l2e_mag k - l2e_mag (Datatypes.S k)))) _).
  - apply (Qabs_wd (l2e_term k + l2e_term (Datatypes.S k))
                   (q_pow (-1) k * (l2e_mag k - l2e_mag (Datatypes.S k)))).
    apply l2e_pair_factor.
  - setoid_rewrite Qabs_Qmult.
    setoid_rewrite sc_abs_sign.
    assert (Hd : Qabs (l2e_mag k - l2e_mag (Datatypes.S k)) ==
                 l2e_mag k - l2e_mag (Datatypes.S k)).
    { apply Qabs_pos.
      apply (Qlt_le_weak 0 (l2e_mag k - l2e_mag (Datatypes.S k))).
      apply l2e_pair_diff_pos. }
    setoid_rewrite Hd.
    ring.
Qed.

(* ============================================================ *)
(* §4 奇偶双边夹逼（对照 atan_sign_even/odd）                     *)
(*   两翼：偶列不减（l2e_even_mono）、奇列不增（l2e_odd_mono）；   *)
(*   夹口：任一偶部分和 ≤ 任一奇部分和（l2e_even_le_odd），        *)
(*   隙宽显式：S_{2m+1} − S_{2m} == 1/(2m+1)（l2e_parity_gap）。   *)
(* ============================================================ *)

(* ---- 界步：S_{2j} ≤ S_{2j+1}（差 == t_{2j} == m_{2j} > 0） ---- *)
Lemma l2e_boundary : forall j : nat, Qle (l2e_alt_partial (2 * j)) (l2e_alt_partial (2 * j + 1)).
Proof.
  intro j.
  assert (H1 : (2 * j + 1)%nat = Datatypes.S (2 * j)) by (exact (Nat.add_1_r (2 * j))).
  rewrite H1.
  assert (Hpos : Qle 0 (l2e_alt_partial (Datatypes.S (2 * j)) - l2e_alt_partial (2 * j))).
  { rewrite (l2e_gap1 (2 * j)).
    apply (Qle_trans _ (l2e_mag (2 * j)) _).
    - apply (Qlt_le_weak 0 (l2e_mag (2 * j))). apply l2e_mag_pos.
    - apply qeq_le.
      unfold l2e_term.
      rewrite (atan_sign_even j).
      unfold l2e_mag, Qdiv.
      ring. }
  apply (proj2 (Qle_minus_iff (l2e_alt_partial (2 * j))
                              (l2e_alt_partial (Datatypes.S (2 * j))))).
  exact Hpos.
Qed.

(* ---- 反向界步：S_{2j} ≤ S_{2j−1}（j=0 时 nat 截断为平凡） ---- *)
Lemma l2e_boundary_rev : forall j : nat,
  Qle (l2e_alt_partial (2 * j)) (l2e_alt_partial (2 * j - 1)).
Proof.
  intro j. destruct j as [| j'].
  - apply Qle_refl.
  - replace (2 * Datatypes.S j')%nat with (2 * j' + 2)%nat by (exact (eq_sym (Nat.mul_succ_r 2 j'))).
    replace (2 * j' + 2 - 1)%nat with (2 * j' + 1)%nat by lia.
    replace (2 * j' + 2)%nat with (Datatypes.S (2 * j' + 1)) by (exact (eq_sym (Nat.add_succ_r (2 * j') 1))).
    assert (Hpos : Qle 0 (l2e_alt_partial (2 * j' + 1) -
                          l2e_alt_partial (Datatypes.S (2 * j' + 1)))).
    { assert (Hd : l2e_alt_partial (2 * j' + 1) -
                   l2e_alt_partial (Datatypes.S (2 * j' + 1)) ==
                   l2e_mag (2 * j' + 1)).
      { apply (Qeq_trans _ (- (l2e_term (2 * j' + 1))) _).
        - pose proof (l2e_gap1 (2 * j' + 1)) as Hg.
          rewrite <- Hg. ring.
        - unfold l2e_term.
          rewrite (atan_sign_odd j').
          unfold l2e_mag, Qdiv.
          ring. }
      rewrite Hd. apply l2e_mag_nonneg. }
    apply (proj2 (Qle_minus_iff (l2e_alt_partial (Datatypes.S (2 * j' + 1)))
                                (l2e_alt_partial (2 * j' + 1)))).
    exact Hpos.
Qed.

(* ---- 偶步：S_{2j} ≤ S_{2j+2}（差 == 成对项 == m_{2j}−m_{2j+1} ≥ 0） ---- *)
(* ---- 偶对恒等（纯代数）：t_{2j}+t_{2j+1} == m_{2j}−m_{2j+1} ---- *)
Lemma l2e_even_pair_factor : forall j : nat,
  l2e_mag (2 * j) - l2e_mag (Datatypes.S (2 * j)) ==
  l2e_term (2 * j) + l2e_term (Datatypes.S (2 * j)).
Proof.
  intro j.
  unfold l2e_term, l2e_mag, Qdiv.
  rewrite (q_pow_succ (-1) (2 * j)).
  rewrite (atan_sign_even j).
  ring.
Qed.

Lemma l2e_even_step : forall j : nat, Qle (l2e_alt_partial (2 * j)) (l2e_alt_partial (2 * j + 2)).
Proof.
  intro j.
  assert (H2 : (2 * j + 2)%nat = Datatypes.S (Datatypes.S (2 * j))) by lia.
  rewrite H2.
  assert (Hpos : Qle 0 (l2e_alt_partial (Datatypes.S (Datatypes.S (2 * j))) -
                        l2e_alt_partial (2 * j))).
  { rewrite (l2e_gap2 (2 * j)).
    apply (Qle_trans _ (l2e_mag (2 * j) - l2e_mag (Datatypes.S (2 * j))) _).
    - apply l2e_mag_decr_pos_step.
    - apply qeq_le. apply l2e_even_pair_factor. }
  apply (proj2 (Qle_minus_iff (l2e_alt_partial (2 * j))
                              (l2e_alt_partial (Datatypes.S (Datatypes.S (2 * j)))))).
  exact Hpos.
Qed.

(* ---- 奇步：S_{2j+3} ≤ S_{2j+1}（差反向：−成对项 == m_{2j+1}−m_{2j+2} ≥ 0） ---- *)
Lemma l2e_odd_step : forall j : nat, Qle (l2e_alt_partial (2 * j + 3)) (l2e_alt_partial (2 * j + 1)).
Proof.
  intro j.
  assert (H3 : (2 * j + 3)%nat = Datatypes.S (Datatypes.S (2 * j + 1))) by lia.
  rewrite H3.
  assert (Hpos : Qle 0 (l2e_alt_partial (2 * j + 1) -
                        l2e_alt_partial (Datatypes.S (Datatypes.S (2 * j + 1))))).
  { assert (Hg : l2e_alt_partial (2 * j + 1) -
                 l2e_alt_partial (Datatypes.S (Datatypes.S (2 * j + 1))) ==
                 l2e_mag (2 * j + 1) - l2e_mag (Datatypes.S (2 * j + 1))).
    { pose proof (l2e_gap2 (2 * j + 1)) as Hfwd.
      assert (Hpf : l2e_term (2 * j + 1) + l2e_term (Datatypes.S (2 * j + 1)) ==
                    - (l2e_mag (2 * j + 1) - l2e_mag (Datatypes.S (2 * j + 1)))).
      { unfold l2e_term, l2e_mag, Qdiv.
        rewrite (q_pow_succ (-1) (2 * j + 1)).
        rewrite (atan_sign_odd j).
        ring. }
      apply (Qeq_trans _ (- (l2e_term (2 * j + 1) + l2e_term (Datatypes.S (2 * j + 1)))) _).
      - rewrite <- (l2e_gap2 (2 * j + 1)). ring.
      - rewrite Hpf. ring. }
    rewrite Hg.
    apply (l2e_mag_decr_pos_step (2 * j + 1)). }
  apply (proj2 (Qle_minus_iff (l2e_alt_partial (Datatypes.S (Datatypes.S (2 * j + 1))))
                              (l2e_alt_partial (2 * j + 1)))).
  exact Hpos.
Qed.

(* ---- 偶列单调（沿 d 不减） ---- *)
Lemma l2e_even_mono : forall d j : nat,
  Qle (l2e_alt_partial (2 * j)) (l2e_alt_partial (2 * (j + d))).
Proof.
  intros d j. induction d as [| d IH].
  - replace (2 * (j + 0))%nat with (2 * j)%nat by ring. apply Qle_refl.
  - replace (2 * (j + Datatypes.S d))%nat with (2 * (j + d) + 2)%nat by (rewrite (Nat.add_succ_r j d); symmetry; apply Nat.mul_succ_r).
    apply (Qle_trans _ (l2e_alt_partial (2 * (j + d))) _).
    + exact IH.
    + exact (l2e_even_step (j + d)).
Qed.

(* ---- 奇列单调（沿 d 不增） ---- *)
Lemma l2e_odd_mono : forall d k : nat,
  Qle (l2e_alt_partial (2 * (k + d) + 1)) (l2e_alt_partial (2 * k + 1)).
Proof.
  intros d k. induction d as [| d IH].
  - replace (2 * (k + 0) + 1)%nat with (2 * k + 1)%nat by ring. apply Qle_refl.
  - replace (2 * (k + Datatypes.S d) + 1)%nat with (2 * (k + d) + 3)%nat by lia.
    apply (Qle_trans _ (l2e_alt_partial (2 * (k + d) + 1)) _).
    + exact (l2e_odd_step (k + d)).
    + exact IH.
Qed.

(* ---- 夹逼核心：任一偶部分和 ≤ 任一奇部分和 ---- *)
Lemma l2e_even_le_odd : forall j k : nat,
  Qle (l2e_alt_partial (2 * j)) (l2e_alt_partial (2 * k + 1)).
Proof.
  intros j k.
  destruct (le_lt_dec j k) as [Hjk | Hkj].
  - (* j ≤ k：S_{2j} ≤_{偶列} S_{2k} ≤_{界步} S_{2k+1} *)
    replace (2 * k + 1)%nat with (2 * (j + (k - j)) + 1)%nat by lia.
    apply (Qle_trans _ (l2e_alt_partial (2 * (j + (k - j)))) _).
    + exact (l2e_even_mono (k - j) j).
    + exact (l2e_boundary (j + (k - j))).
  - (* k < j：S_{2j} ≤_{反向界步} S_{2j−1} ≤_{奇列} S_{2k+1} *)
    apply (Qle_trans _ (l2e_alt_partial (2 * j - 1)) _).
    + exact (l2e_boundary_rev j).
    + replace (2 * j - 1)%nat with (2 * (k + (j - k - 1)) + 1)%nat by lia.
      exact (l2e_odd_mono (j - k - 1) k).
Qed.

(* ---- 隙宽显式：S_{2m+1} − S_{2m} == 1/(2m+1) ---- *)
Lemma l2e_parity_gap : forall m : nat,
  l2e_alt_partial (2 * m + 1) - l2e_alt_partial (2 * m) == l2e_mag (2 * m).
Proof.
  intro m.
  assert (H1 : (2 * m + 1)%nat = Datatypes.S (2 * m)) by (exact (Nat.add_1_r (2 * m))).
  rewrite H1.
  rewrite (l2e_gap1 (2 * m)).
  unfold l2e_term.
  rewrite (atan_sign_even m).
  unfold l2e_mag, Qdiv.
  ring.
Qed.

(* ============================================================ *)
(* §5 尾界（四段式之四：Leibniz 余项；对照 atan_tail_bound）       *)
(*   m ≤ n ⟹ |S_n − S_m| ≤ m_m == 1/(m+1)（显式公式）            *)
(* ============================================================ *)

Lemma l2e_tail_bound : forall m n : nat, (m <= n)%nat ->
  Qle (Qabs (l2e_alt_partial n - l2e_alt_partial m)) (l2e_mag m).
Proof.
  assert (Hgen : forall (d m n : nat), (m <= n)%nat -> (n - m)%nat = d ->
    Qle (Qabs (l2e_alt_partial n - l2e_alt_partial m)) (l2e_mag m)).
  { induction d as [d IH] using lt_wf_ind.
    intros m n Hmn Hd.
    destruct (Nat.leb (Datatypes.S (Datatypes.S m)) n) eqn:E2.
    - (* m + 2 ≤ n：三角拆分 + 成对项 + 归纳（下界 m+2） *)
      apply Nat.leb_le in E2.
      apply (Qle_trans _ (Qabs ((l2e_alt_partial n - l2e_alt_partial (Datatypes.S (Datatypes.S m))) +
                                (l2e_alt_partial (Datatypes.S (Datatypes.S m)) - l2e_alt_partial m))) _).
      + apply qeq_le.
        apply (Qabs_wd (l2e_alt_partial n - l2e_alt_partial m)
                       ((l2e_alt_partial n - l2e_alt_partial (Datatypes.S (Datatypes.S m))) +
                        (l2e_alt_partial (Datatypes.S (Datatypes.S m)) - l2e_alt_partial m))).
        ring.
      + apply (Qle_trans _ (Qabs (l2e_alt_partial n - l2e_alt_partial (Datatypes.S (Datatypes.S m))) +
                            Qabs (l2e_alt_partial (Datatypes.S (Datatypes.S m)) - l2e_alt_partial m)) _).
        * apply Qabs_triangle.
        * apply (Qle_trans _ (l2e_mag (Datatypes.S (Datatypes.S m)) +
                              (l2e_mag m - l2e_mag (Datatypes.S m))) _).
          -- apply Qplus_le_compat.
             ++ (* |S_n − S_{m+2}| ≤ m_{m+2}（IH，下界 m+2） *)
                apply (IH (n - Datatypes.S (Datatypes.S m))%nat).
                ** lia.
                ** lia.
                ** reflexivity.
             ++ (* |S_{m+2} − S_m| == |t_m + t_{m+1}| == m_m − m_{m+1} *)
                apply qeq_le.
                apply (Qeq_trans _ (Qabs (l2e_term m + l2e_term (Datatypes.S m))) _).
                ** apply (Qabs_wd (l2e_alt_partial (Datatypes.S (Datatypes.S m)) -
                                   l2e_alt_partial m)
                                  (l2e_term m + l2e_term (Datatypes.S m))).
                   exact (l2e_gap2 m).
                ** apply l2e_pair_abs.
          -- (* m_{m+2} ≤ m_{m+1} ⟹ 和 ≤ m_{m+1} + (m_m − m_{m+1}) == m_m *)
             apply (Qle_trans _ (l2e_mag (Datatypes.S m) +
                                 (l2e_mag m - l2e_mag (Datatypes.S m))) _).
             ++ apply Qplus_le_compat.
                ** apply l2e_mag_decr.
                ** apply Qle_refl.
             ++ apply qeq_le. ring.
    - (* n ≤ S m：n = m 或 n = S m *)
      apply Nat.leb_gt in E2.
      destruct (Nat.eq_dec m n) as [Heq | Hne].
      + (* n = m：差 0 ≤ m_m *)
        subst n.
        apply (Qle_trans _ 0 _).
        * apply qeq_le.
          apply (Qabs_wd (l2e_alt_partial m - l2e_alt_partial m) 0).
          ring.
        * apply l2e_mag_nonneg.
      + (* n = S m：差 == |t_m| == m_m *)
        assert (Hn : n = Datatypes.S m) by lia.
        subst n.
        apply qeq_le.
        apply (Qeq_trans _ (Qabs (l2e_term m)) _).
        * apply (Qabs_wd (l2e_alt_partial (Datatypes.S m) - l2e_alt_partial m) (l2e_term m)).
          exact (l2e_gap1 m).
        * apply l2e_term_abs.
  }
  intros m n Hmn.
  apply (Hgen (n - m)%nat m n Hmn). reflexivity.
Qed.

(* ============================================================ *)
(* §6 出口二（QleT' 化）：l2e_alt_two_sided                       *)
(* ============================================================ *)

Theorem l2e_alt_two_sided : forall m n : nat, (m <= n)%nat ->
  QleT' (Qabs (l2e_alt_partial n - l2e_alt_partial m)) (1 / ((Z.of_nat m + 1) # 1)).
Proof.
  intros m n Hmn.
  apply (qleT'_weaken _ (l2e_mag m) _).
  - apply l2e_tail_bound. exact Hmn.
  - assert (Hb : (Z.of_nat m + 1)%Z = Z.of_nat (Datatypes.S m)) by (exact (eq_trans (Z.add_1_r (Z.of_nat m)) (eq_sym (Znat.Nat2Z.inj_succ m)))).
    unfold l2e_mag. rewrite Hb. reflexivity.
Qed.

(* ============================================================ *)
(* §7 出口三：显式模量 N := S(ceil(1/eps))（Qceiling）+ sigT 柯西件 *)
(*   （对照 arctan_partial_cauchy；见证 N 由 Qround 的            *)
(*   Qceiling 显式给出，可抽取）                                  *)
(* ============================================================ *)

Definition l2e_modulus (eps : Q) : nat :=
  Datatypes.S (Z.to_nat (Qceiling (Qinv eps))).

Lemma l2e_modulus_bound : forall eps : Q, Qlt 0 eps ->
  Qlt (l2e_mag (l2e_modulus eps)) eps.
Proof.
  intros eps Heps.
  assert (Hx0 : Qlt 0 (Qinv eps)) by (apply Qinv_lt_0_compat; exact Heps).
  assert (Hcq : Qle 0 (Qceiling (Qinv eps) # 1)).
  { apply (Qle_trans 0 (Qinv eps) (Qceiling (Qinv eps) # 1)).
    - apply (Qlt_le_weak 0 (Qinv eps)). exact Hx0.
    - apply Qle_ceiling. }
  assert (Hcpos : (0 <= Qceiling (Qinv eps))%Z).
  { unfold Qle in Hcq. cbn [Qnum Qden] in Hcq.
    rewrite Z.mul_0_l, Z.mul_1_r in Hcq. exact Hcq. }
  assert (Hstep : Qlt (Qinv eps) ((Z.succ (Qceiling (Qinv eps))) # 1)).
  { apply (Qle_lt_trans (Qinv eps) (Qceiling (Qinv eps) # 1)
                        ((Z.succ (Qceiling (Qinv eps))) # 1)).
    - apply Qle_ceiling.
    - unfold Qlt, Qle. cbn [Qnum Qden]. rewrite !Z.mul_1_r.
      exact (Z.lt_succ_diag_r (Qceiling (Qinv eps))). }
  assert (Hz : (Z.succ (Qceiling (Qinv eps)) = Z.of_nat (l2e_modulus eps))%Z)
    by (unfold l2e_modulus; lia).
  assert (Hmul : Qlt (Qinv eps * eps) ((Z.of_nat (l2e_modulus eps) # 1) * eps)).
  { apply (Qmult_lt_compat_r (Qinv eps) (Z.of_nat (l2e_modulus eps) # 1) eps Heps).
    rewrite <- Hz. exact Hstep. }
  setoid_replace (Qinv eps * eps) with 1%Q in Hmul.
  2: { field. intro Hzz. apply (Qlt_not_eq 0 eps Heps). exact (Qeq_sym _ _ Hzz). }
  setoid_replace ((Z.of_nat (l2e_modulus eps) # 1) * eps)
    with (eps * (Z.of_nat (l2e_modulus eps) # 1)) in Hmul by ring.
  assert (Hd1 : Qlt 0 (Z.of_nat (l2e_modulus eps) # 1)).
  { unfold Qlt. cbn [Qnum Qden]. rewrite Z.mul_0_l, Z.mul_1_r.
    assert (Hge : (1 <= Z.of_nat (l2e_modulus eps))%Z).
    { (* 模量=S(Z.to_nat _)：非负性（Nat2Z.is_nonneg）经后继单调前向给出 1<=_ *)
      unfold l2e_modulus. rewrite Znat.Nat2Z.inj_succ.
      exact (proj1 (Z.succ_le_mono 0 (Z.of_nat (Z.to_nat (Qceiling (Qinv eps)))))
                   (Znat.Nat2Z.is_nonneg (Z.to_nat (Qceiling (Qinv eps))))). }
    apply (Z.lt_le_trans 0 1 (Z.of_nat (l2e_modulus eps)) (Pos2Z.pos_is_pos 1) Hge). }
  assert (Hd2 : Qlt 0 (Z.of_nat (Datatypes.S (l2e_modulus eps)) # 1))
    by (apply (l2e_den_pos (l2e_modulus eps))).
  assert (Hlt2 : Qlt (Z.of_nat (l2e_modulus eps) # 1)
                     (Z.of_nat (Datatypes.S (l2e_modulus eps)) # 1))
    by (unfold Qlt; cbn [Qnum Qden];
        rewrite Znat.Nat2Z.inj_succ, !Z.mul_1_r;
        exact (Z.lt_succ_diag_r (Z.of_nat (l2e_modulus eps)))).
  setoid_replace (l2e_mag (l2e_modulus eps))
    with (/ (Z.of_nat (Datatypes.S (l2e_modulus eps)) # 1))
    by (apply (l2e_mag_inv (l2e_modulus eps))).
  apply (Qle_lt_trans _ (/ (Z.of_nat (l2e_modulus eps) # 1)) _).
  - apply Qlt_le_weak.
    apply (proj1 (Qinv_lt_contravar (Z.of_nat (l2e_modulus eps) # 1)
                                    (Z.of_nat (Datatypes.S (l2e_modulus eps)) # 1)
                                    Hd1 Hd2)).
    exact Hlt2.
  - apply Qlt_shift_inv_r.
    + exact Hd1.
    + exact Hmul.
Qed.

(* ---- 出口三：sigT 柯西模量（N 显式：ceil(1/eps)+1，可抽取） ---- *)
Theorem l2e_cauchy_modulus : forall eps : Q, QltT' 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    QltT' (Qabs (l2e_alt_partial n - l2e_alt_partial m)) eps).
Proof.
  intros eps Heps.
  assert (Hlt : Qlt 0 eps) by (apply (QltT'_to_Qlt 0 eps Heps)).
  exists (l2e_modulus eps).
  intros m n HNm HNn.
  apply Qlt_to_QltT'.
  destruct (Nat.leb m n) eqn:E.
  - (* m ≤ n：|S_n − S_m| ≤ m_m ≤ m_N < eps *)
    apply Nat.leb_le in E.
    apply (Qle_lt_trans _ (l2e_mag (l2e_modulus eps)) _).
    + apply (Qle_trans _ (l2e_mag m) _).
      * apply l2e_tail_bound. exact E.
      * apply l2e_mag_antitone.
        apply NatLe_drop in HNm. exact HNm.
    + exact (l2e_modulus_bound eps Hlt).
  - (* n < m：Qabs_Qminus 对折后同链（用 n） *)
    apply Nat.leb_gt in E.
    apply (Qle_lt_trans _ (l2e_mag (l2e_modulus eps)) _).
    + apply (Qle_trans _ (l2e_mag n) _).
      * rewrite Qabs_Qminus. apply (l2e_tail_bound n m). lia.
      * apply l2e_mag_antitone.
        apply NatLe_drop in HNn. lia.
    + exact (l2e_modulus_bound eps Hlt).
Qed.

(* ============================================================ *)
(* §8 审计注记（文末 Print Assumptions 追印）                     *)
(* ============================================================ *)

Print Assumptions l2e_alt_two_sided.
Print Assumptions l2e_cauchy_modulus.
Print Assumptions l2e_parity_gap.
Print Assumptions l2e_even_le_odd.

(* ============================ §3 C1 LogZWall 第四面墙定理化 ============================ *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpRealLeB.
Require Import UpReqGeomD.
Require Import UpReqLpoEquiv.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 1：Q 层小桥（Qlt_alt 破形 + 位移 helper + Qabs 界）          *)
(* ============================================================ *)

Lemma lgz_q_pos_half : Qlt 0 (1#2).
Proof.
  apply (proj2 (Qlt_alt 0 (1#2))).
  exact (@eq_refl comparison Lt).
Qed.

Lemma lgz_q_pos_quarter : Qlt 0 (1#4).
Proof.
  apply (proj2 (Qlt_alt 0 (1#4))).
  exact (@eq_refl comparison Lt).
Qed.

Lemma lgz_q_pos_quarterT : QltT 0 (1#4).
Proof.
  exact (Qlt_to_QltT 0 (1#4) lgz_q_pos_quarter).
Qed.


(* 位移三件与 Qabs 界拆分（lra 闭合；非线性单项式按原子抽象） *)
Lemma lgz_q_lt_add_l : forall a b c : Q, a + b < c -> a < c - b.
Proof.
  intros a b c H.
  lra.
Qed.

Lemma lgz_q_lt_add_r : forall a b c : Q, a + b < c -> b < c - a.
Proof.
  intros a b c H.
  lra.
Qed.

Lemma lgz_q_plus_lt_r : forall u v w : Q, u < v -> u + w < v + w.
Proof.
  intros u v w H.
  lra.
Qed.

Lemma lgz_q_plus_lt_l : forall u v w : Q, u < v -> w + u < w + v.
Proof.
  intros u v w H.
  lra.
Qed.

(* Qabs 界拆分：0 < b ∧ |a| < b ⟹ a < b（上界）/ −b < a（下界） *)
Lemma lgz_q_abs_lt_bounds_ub : forall a b : Q,
  0 < b -> Qabs a < b -> a < b.
Proof.
  intros a b Hb0 H.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)) in H.
    exact H.
  - rewrite (Qabs_neg a Hneg) in H.
    lra.
Qed.

Lemma lgz_q_abs_lt_bounds_lb : forall a b : Q,
  0 < b -> Qabs a < b -> - b < a.
Proof.
  intros a b Hb0 H.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)) in H.
    lra.
  - rewrite (Qabs_neg a Hneg) in H.
    lra.
Qed.

(* Qeq 位移四件：Qlt/Qabs 位换形（q_eq_le/q_abs_congr 桥）——
   Qeq 集合重写只在 Qeq-目标内可用（AA22 先例），Qlt/Id 位经此四件迁移 *)
Lemma lgz_qlt_shift : forall u u' w : Q, u == u' -> Qlt u w -> Qlt u' w.
Proof.
  intros u u' w Huu H.
  apply (Qle_lt_trans u' u w).
  - apply q_eq_le.
    apply Qeq_sym.
    exact Huu.
  - exact H.
Qed.

Lemma lgz_qlt_shift2_r : forall w u u' : Q, u == u' -> Qlt w u -> Qlt w u'.
Proof.
  intros w u u' Huu H.
  apply (Qlt_le_trans w u u').
  - exact H.
  - apply q_eq_le.
    exact Huu.
Qed.

Lemma lgz_qlt_abs_shift : forall a a' w : Q,
  a == a' -> Qlt (Qabs a) w -> Qlt (Qabs a') w.
Proof.
  intros a a' w Haa H.
  apply (Qle_lt_trans (Qabs a') (Qabs a) w).
  - apply q_eq_le.
    apply q_abs_congr.
    apply Qeq_sym.
    exact Haa.
  - exact H.
Qed.

Lemma lgz_qlt_shift_r : forall w u u' : Q,
  u == u' -> Qlt w (Qabs u) -> Qlt w (Qabs u').
Proof.
  intros w u u' Huu H.
  apply (Qlt_le_trans w (Qabs u) (Qabs u')).
  - exact H.
  - apply q_eq_le.
    apply q_abs_congr.
    exact Huu.
Qed.

(* 解码闭合（lt 支）：ε>0 ∧ ε < 1−a ∧ |a−(1−b)| < ε/2 ⟹ ε/2 < b *)
Lemma lgz_q_decode_lt : forall eps a b : Q,
  0 < eps -> Qlt eps (1 - a) ->
  Qlt (Qabs (a - (1 - b))) (eps * (1#2)) ->
  Qlt (eps * (1#2)) b.
Proof.
  intros eps a b Heps H1 H2.
  destruct (Qlt_le_dec 0 (a - (1 - b))) as [Hp | Hn].
  - rewrite (Qabs_pos _ (Qlt_le_weak _ _ Hp)) in H2.
    lra.
  - rewrite (Qabs_neg _ Hn) in H2.
    lra.
Qed.

(* 解码闭合（eq 支）：|a−(1−b)| < δ/2 ∧ |a−1| < δ/2 ⟹ |0−b| < δ *)
Lemma lgz_q_decode_eq : forall del a b : Q,
  Qlt (Qabs (a - (1 - b))) (del * (1#2)) ->
  Qlt (Qabs (a - 1)) (del * (1#2)) ->
  Qlt (Qabs (0 - b)) del.
Proof.
  intros del a b H1 H2.
  apply (lgz_qlt_abs_shift (((1 - b) + (- a)) + (a - 1)) (0 - b) del).
  - ring.
  - apply (Qle_lt_trans (Qabs (((1 - b) + (- a)) + (a - 1)))
             (Qabs ((1 - b) + (- a)) + Qabs (a - 1)) del).
    + apply Qabs_triangle.
    + assert (H1' : Qlt (Qabs ((1 - b) + (- a))) (del * (1#2))).
      { apply (Qle_lt_trans (Qabs ((1 - b) + (- a)))
                 (Qabs (a - (1 - b))) (del * (1#2))).
        - apply q_eq_le.
          rewrite <- (Qabs_opp (a - (1 - b))).
          apply q_abs_congr.
          ring.
        - exact H1. }
      lra.
Qed.

(* ============================================================ *)
(* Part 2：Real 层小桥 + 半量机 lgz_half                             *)
(* ============================================================ *)

(* le + lt 拼接（geod_b_le_lt_trans 同体） *)
Lemma lgz_le_lt_trans : forall x y z : Real,
  real_le x y -> real_lt y z -> real_lt x z.
Proof.
  intros x y z Hle Hlt.
  destruct Hle as [Hlt' | Heq].
  - exact (real_lt_trans x y z Hlt' Hlt).
  - exact (real_eq_lt_lt x y z Heq Hlt).
Qed.

(* 半量：inv2 := 1/(1+1)（正性证书内嵌） *)
Definition lgz_half : Real :=
  real_inv_pos (real_plus real_one real_one)
    (real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one).

Lemma lgz_half_eq :
  real_eq (real_mult (real_plus real_one real_one) lgz_half) real_one.
Proof.
  exact (real_inv_pos_correct (real_plus real_one real_one)           (real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one)).
Qed.

(* half < 1：隙 3/8 *)
Lemma lgz_half_lt_one : real_lt lgz_half real_one.
Proof.
  exists (3#8). split.
  - apply Qlt_to_QltT.
    apply (proj2 (Qlt_alt 0 (3#8))).
    reflexivity.
  - destruct (lgz_half_eq (1#4) lgz_q_pos_quarterT) as [N HN].
    exists N. intros m Hm.
    pose proof (HN m Hm) as HNb.
    apply QltT_to_Qlt in HNb.
    assert (Hpj : projT1 (real_mult (real_plus real_one real_one) lgz_half) m
                  == (1 + 1) * projT1 lgz_half m).
    { rewrite (real_mult_proj (real_plus real_one real_one) lgz_half m).
      reflexivity. }
    rewrite Hpj in HNb.
    assert (Hone : projT1 real_one m == 1) by reflexivity.
    rewrite Hone in HNb.
    pose proof (lgz_q_abs_lt_bounds_ub ((1 + 1) * projT1 lgz_half m - 1)
                  (1#4) lgz_q_pos_quarter HNb) as Hub.
    assert (Hb2 : (1 + 1) * projT1 lgz_half m < (5#4)) by lra.
    assert (Hb3 : projT1 lgz_half m < (5#8)).
    { assert (Hm1 : ((1 + 1) * projT1 lgz_half m) * (1#2) < (5#4) * (1#2))
        by (apply (Qmult_lt_compat_r _ _ (1#2));
            [apply (proj2 (Qlt_alt 0 (1#2))); reflexivity | exact Hb2]).
      assert (Hm2 : ((1 + 1) * projT1 lgz_half m) * (1#2)
                    == projT1 lgz_half m) by ring.
      rewrite Hm2 in Hm1.
      assert (Hm3 : (5#4) * (1#2) == (5#8)) by ring.
      rewrite Hm3 in Hm1.
      exact Hm1. }
    apply Qlt_to_QltT.
    apply (lgz_qlt_shift2_r (3#8) (1 - projT1 lgz_half m)
             (projT1 real_one m - projT1 lgz_half m)).
    + rewrite Hone.
      ring.
    + apply (lgz_q_lt_add_l (3#8) (projT1 lgz_half m) 1).
      assert (Hg : (3#8) + projT1 lgz_half m < (3#8) + (5#8))
        by (apply (lgz_q_plus_lt_l _ _ (3#8)); exact Hb3).
      assert (Hg2 : (3#8) + (5#8) == 1) by ring.
      rewrite Hg2 in Hg.
      exact Hg.
Qed.

(* half 投影的一致 5/8 上界（事件形，供反向解码） *)
Lemma lgz_half_eventual_ub :
  sigT (fun N : nat => forall m : nat, NatLe N m ->
    Qlt (projT1 lgz_half m) (5#8)).
Proof.
  destruct (lgz_half_eq (1#4) lgz_q_pos_quarterT) as [Nv HNv].
  exists Nv. intros m Hm.
  pose proof (HNv m Hm) as Hb.
  apply QltT_to_Qlt in Hb.
  assert (Hpj : projT1 (real_mult (real_plus real_one real_one) lgz_half) m
                == (1 + 1) * projT1 lgz_half m).
  { rewrite (real_mult_proj (real_plus real_one real_one) lgz_half m).
    reflexivity. }
  rewrite Hpj in Hb.
  assert (Hone : projT1 real_one m == 1) by reflexivity.
  rewrite Hone in Hb.
  pose proof (lgz_q_abs_lt_bounds_ub ((1 + 1) * projT1 lgz_half m - 1)
                (1#4) lgz_q_pos_quarter Hb) as Hub.
  assert (H1 : (1 + 1) * projT1 lgz_half m < (5#4)) by lra.
  assert (H1b : ((1 + 1) * projT1 lgz_half m) * (1#2) < (5#4) * (1#2)).
  { apply (Qmult_lt_compat_r ((1 + 1) * projT1 lgz_half m) (5#4) (1#2)).
    - apply (proj2 (Qlt_alt 0 (1#2))).
      reflexivity.
    - exact H1. }
  assert (H2 : ((1 + 1) * projT1 lgz_half m) * (1#2)
               == projT1 lgz_half m) by ring.
  rewrite H2 in H1b.
  assert (H3 : (5#4) * (1#2) == (5#8)) by ring.
  rewrite H3 in H1b.
  exact H1b.
Qed.

(* ε/2 < ε（严格，ε>0） *)
Lemma lgz_half_lt_eps : forall eps : Real,
  real_lt real_zero eps -> real_lt (real_mult eps lgz_half) eps.
Proof.
  intros eps Heps.
  apply (real_lt_eq_lt (real_mult eps lgz_half) (real_mult eps real_one) eps).
  - exact (real_mult_lt_compat_l lgz_half real_one eps lgz_half_lt_one Heps).
  - exact (real_mult_one eps).
Qed.

(* (1 + ε/2) < (1 + ε) *)
Lemma lgz_one_half_lt_one : forall eps : Real,
  real_lt real_zero eps ->
  real_lt (real_plus real_one (real_mult eps lgz_half)) (real_plus real_one eps).
Proof.
  intros eps Heps.
  apply (real_eq_lt_lt _ (real_plus (real_mult eps lgz_half) real_one)
           (real_plus real_one eps)).
  - exact (real_eq_sym _ _ (real_plus_comm (real_mult eps lgz_half) real_one)).
  - apply (real_lt_eq_lt _ (real_plus eps real_one) _).
    + exact (real_lt_plus_compat_lt_le (real_mult eps lgz_half) eps real_one
               real_one (lgz_half_lt_eps eps Heps) (real_le_refl real_one)).
    + exact (real_plus_comm eps real_one).
Qed.

(* ============================================================ *)
(* Part 3：具体墙语句面（Z ≤ 1 精确判定形）                          *)
(* ============================================================ *)

Definition lgz_LogZWall : Set :=
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnp : real_eq (real_list_sum nat p (List.seq 0 n)) real_one)
    (Hnr : real_eq (real_list_sum nat r (List.seq 0 n)) real_one)
    (Heta : real_lt real_zero eta) (Hetale : real_le eta real_one),
  real_le (real_interp_Z n p r eta Hp Hr) real_one.

(* ============================================================ *)
(* Part 4：泛型槽段（AA22 GibbMechanism 范式）——主件                 *)
(* ============================================================ *)

Section LogZMechanism.

Variable ZWf : Real -> Real.

(* 槽：载体编码——任意 x 的 1−x² 形可编码进 ZWf 值域。
   注：族内逐点正（配分语义位）在 Z-形正向中不被使用（log 形接口才需要），
   故不入段（段封闭会丢弃未使用槽），如实移除。 *)
Hypothesis lgmech_carr : forall x : Real,
  sigT (fun xi : Real =>
    real_eq (ZWf xi) (real_plus real_one (real_opp (real_mult x x)))).

(* 泛型墙 plain-le 形 ⟹ SqWall（解码双侧透明） *)
Theorem lgmech_wall_zle :
  (forall x : Real, real_le (ZWf x) real_one) -> SqWall.
Proof.
  intros Hwall x.
  destruct (lgmech_carr x) as [xi Heq].
  destruct (Hwall xi) as [Hlt | Heq1].
  - (* 左支：ZWf ξ < 1 带隙 ε ⟹ x·x 有隙（δ := ε/2） *)
    apply inl.
    destruct Hlt as [eps [Heps [N HN]]].
    assert (Hq2 : QltT 0 (eps * (1#2))).
    { apply Qlt_to_QltT.
      assert (H0 : 0 * (1#2) < eps * (1#2))
        by (apply Qmult_lt_compat_r;
            [exact lgz_q_pos_half | apply QltT_to_Qlt; exact Heps]).
      rewrite Qmult_0_l in H0.
      exact H0. }
    destruct (Heq (eps * (1#2)) Hq2) as [N2 HN2].
    exists (eps * (1#2)). split.
    + exact Hq2.
    + exists (Nat.max N N2). intros n Hn.
      assert (Hmn : NatLe N n).
      { apply NatLe_lift.
        pose proof (NatLe_drop _ _ Hn) as Hdn.
        lia. }
      assert (Hmn2 : NatLe N2 n).
      { apply NatLe_lift.
        pose proof (NatLe_drop _ _ Hn) as Hdn.
        lia. }
      assert (Hone : projT1 real_one n == 1) by reflexivity.
      (* H1 换形：eps < 1 − a（Qeq 位移桥） *)
      assert (H1 : Qlt eps (1 - projT1 (ZWf xi) n)).
      { pose proof (HN n Hmn) as HNn.
        pose proof (QltT_to_Qlt eps
                      (projT1 real_one n - projT1 (ZWf xi) n) HNn) as HNn'.
        apply (lgz_qlt_shift2_r eps (projT1 real_one n - projT1 (ZWf xi) n)
                 (1 - projT1 (ZWf xi) n)).
        - rewrite Hone.
          ring.
        - exact HNn'. }
      (* H2 换形：|a − (1−b)| < ε/2（Qeq 位移桥） *)
      assert (H2 : Qlt (Qabs (projT1 (ZWf xi) n
                                - (1 - projT1 x n * projT1 x n)))
                       (eps * (1#2))).
      { pose proof (HN2 n Hmn2) as HN2n.
        pose proof (QltT_to_Qlt
                      (Qabs
                         (projT1 (ZWf xi) n
                            - (projT1 (real_plus real_one
                                         (real_opp (real_mult x x))) n)))
                      (eps * (1#2)) HN2n) as HN2n'.
        apply (lgz_qlt_abs_shift
                 (projT1 (ZWf xi) n
                    - (projT1 (real_plus real_one
                                 (real_opp (real_mult x x))) n))
                 (projT1 (ZWf xi) n
                    - (1 - projT1 x n * projT1 x n))
                 (eps * (1#2))).
        - rewrite (real_plus_proj real_one (real_opp (real_mult x x)) n).
          rewrite (real_opp_proj (real_mult x x) n).
          rewrite (real_mult_proj x x n).
          rewrite Hone.
          ring.
        - exact HN2n'. }
      assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
      assert (Hfin : Qlt (eps * (1#2)) (projT1 x n * projT1 x n))
        by (apply (lgz_q_decode_lt eps (projT1 (ZWf xi) n)
                     (projT1 x n * projT1 x n) HepsQ H1 H2)).
      (* 终局迁移：目标位 projT1 (real_mult x x) n − projT1 real_zero n *)
      apply Qlt_to_QltT.
      apply (lgz_qlt_shift2_r (eps * (1#2))
               (projT1 x n * projT1 x n)
               (projT1 (real_mult x x) n - projT1 real_zero n)).
      * rewrite (real_mult_proj x x n).
        assert (Hz0 : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz0.
        ring.
      * exact Hfin.
  - (* 右支：ZWf ξ == 1 ⟹ x·x 逐点归零（容差半分 + 三角不等式） *)
    apply inr.
    intros del Hdel.
    assert (Hq2 : QltT 0 (del * (1#2))).
    { apply Qlt_to_QltT.
      assert (H0 : 0 * (1#2) < del * (1#2))
        by (apply Qmult_lt_compat_r;
            [exact lgz_q_pos_half | apply QltT_to_Qlt; exact Hdel]).
      rewrite Qmult_0_l in H0.
      exact H0. }
    destruct (Heq (del * (1#2)) Hq2) as [N1 HN1].
    destruct (Heq1 (del * (1#2)) Hq2) as [N2 HN2].
    exists (Nat.max N1 N2). intros n Hn.
    assert (Hmn1 : NatLe N1 n).
    { apply NatLe_lift.
      pose proof (NatLe_drop _ _ Hn) as Hdn.
      lia. }
    assert (Hmn2 : NatLe N2 n).
    { apply NatLe_lift.
      pose proof (NatLe_drop _ _ Hn) as Hdn.
      lia. }
    assert (Hone : projT1 real_one n == 1) by reflexivity.
    (* H1r 换形：|a − (1−b)| < δ/2 *)
    assert (H1r : Qlt (Qabs (projT1 (ZWf xi) n
                                - (1 - projT1 x n * projT1 x n)))
                       (del * (1#2))).
    { pose proof (HN1 n Hmn1) as HN1n.
      pose proof (QltT_to_Qlt
                    (Qabs
                       (projT1 (ZWf xi) n
                          - (projT1 (real_plus real_one
                                       (real_opp (real_mult x x))) n)))
                    (del * (1#2)) HN1n) as HN1n'.
      apply (lgz_qlt_abs_shift
               (projT1 (ZWf xi) n
                  - (projT1 (real_plus real_one
                               (real_opp (real_mult x x))) n))
               (projT1 (ZWf xi) n
                  - (1 - projT1 x n * projT1 x n))
               (del * (1#2))).
      - rewrite (real_plus_proj real_one (real_opp (real_mult x x)) n).
        rewrite (real_opp_proj (real_mult x x) n).
        rewrite (real_mult_proj x x n).
        rewrite Hone.
        ring.
      - exact HN1n'. }
    (* H2r 换形：|a − 1| < δ/2 *)
    assert (H2r : Qlt (Qabs (projT1 (ZWf xi) n - 1)) (del * (1#2))).
    { pose proof (HN2 n Hmn2) as HN2n.
      pose proof (QltT_to_Qlt
                    (Qabs (projT1 (ZWf xi) n - projT1 real_one n))
                    (del * (1#2)) HN2n) as HN2n'.
      apply (lgz_qlt_abs_shift
               (projT1 (ZWf xi) n - projT1 real_one n)
               (projT1 (ZWf xi) n - 1)
               (del * (1#2))).
      - rewrite Hone.
        ring.
      - exact HN2n'. }
    (* 终局迁移 *)
    apply Qlt_to_QltT.
    apply (lgz_qlt_abs_shift (0 - projT1 x n * projT1 x n)
             (projT1 real_zero n - projT1 (real_mult x x) n) del).
    * rewrite (real_mult_proj x x n).
      assert (Hz0 : projT1 real_zero n == 0) by reflexivity.
      rewrite Hz0.
      ring.
    * exact (lgz_q_decode_eq del (projT1 (ZWf xi) n)
               (projT1 x n * projT1 x n) H1r H2r).
Qed.

(* 主件：泛型墙 plain-le 形 ⟹ 受限 LPO（lpn_forward 升维） *)
Theorem lgz_log_z_wall_lpo :
  (forall x : Real, real_le (ZWf x) real_one) -> rLPO.
Proof.
  intros Hwall.
  exact (lpn_forward (lgmech_wall_zle Hwall)).
Qed.

End LogZMechanism.

(* ============================================================ *)
(* Part 5：对角双参数位（具体内容位）——r := p ⟹ Z == 1 与左支灭绝         *)
(* ============================================================ *)

(* 逐点幂拆：p^{1−η}·p^η == p（exp 加法性 + exp-wd + 分布律环链） *)
Lemma lgz_pow_split : forall (y : Real) (Hy : real_lt real_zero y) (eta : Real),
  real_eq (real_mult (real_pow_pos y (real_plus real_one (real_opp eta)) Hy)
                     (real_pow_pos y eta Hy))
            y.
Proof.
  intros y Hy eta.
  unfold real_pow_pos.
  apply (real_eq_trans
           (real_mult (cauchy_real_exp
                          (real_mult (real_plus real_one (real_opp eta)) (cw_log y Hy)))
                      (cauchy_real_exp (real_mult eta (cw_log y Hy))))
           (cauchy_real_exp
              (real_plus
                 (real_mult (real_plus real_one (real_opp eta)) (cw_log y Hy))
                 (real_mult eta (cw_log y Hy))))
           y).
  - apply real_eq_sym.
    exact (cauchy_real_exp_plus
             (real_mult (real_plus real_one (real_opp eta)) (cw_log y Hy))
             (real_mult eta (cw_log y Hy))).
  - apply (real_eq_trans
             (cauchy_real_exp
                (real_plus
                   (real_mult (real_plus real_one (real_opp eta)) (cw_log y Hy))
                   (real_mult eta (cw_log y Hy))))
             (cauchy_real_exp
                (real_mult (cw_log y Hy)
                   (real_plus (real_plus real_one (real_opp eta)) eta)))
             y).
    + apply cauchy_real_exp_wd.
      apply (real_eq_trans
               (real_plus
                  (real_mult (real_plus real_one (real_opp eta)) (cw_log y Hy))
                  (real_mult eta (cw_log y Hy)))
               (real_plus
                  (real_mult (cw_log y Hy) (real_plus real_one (real_opp eta)))
                  (real_mult (cw_log y Hy) eta))
               (real_mult (cw_log y Hy)
                  (real_plus (real_plus real_one (real_opp eta)) eta))).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult (real_plus real_one (real_opp eta)) (cw_log y Hy))
                 (real_mult eta (cw_log y Hy))
                 (real_mult (cw_log y Hy) (real_plus real_one (real_opp eta)))
                 (real_mult (cw_log y Hy) eta)).
        -- exact (real_mult_comm (real_plus real_one (real_opp eta)) (cw_log y Hy)).
        -- exact (real_mult_comm eta (cw_log y Hy)).
      * exact (real_eq_sym _ _ (real_distrib (cw_log y Hy)
                    (real_plus real_one (real_opp eta)) eta)).
+ apply (real_eq_trans
               (cauchy_real_exp
                  (real_mult (cw_log y Hy)
                     (real_plus (real_plus real_one (real_opp eta)) eta)))
               (cauchy_real_exp (cw_log y Hy))
               y).
  * apply cauchy_real_exp_wd.
    apply (real_eq_trans
             (real_mult (cw_log y Hy)
                (real_plus (real_plus real_one (real_opp eta)) eta))
             (real_mult (cw_log y Hy) real_one)
             (cw_log y Hy)).
    -- apply (RealSetoid.real_eq_mult_compat
               (cw_log y Hy)
               (real_plus (real_plus real_one (real_opp eta)) eta)
               (cw_log y Hy) real_one).
      ++ exact (real_eq_refl (cw_log y Hy)).
      ++ destruct eta as [e He].
         apply real_eq_of_zero_diff.
         intro k.
         simpl.
         ring.
    -- exact (real_mult_one (cw_log y Hy)).
  * exact (cw_log_exp_right y Hy).
Qed.

(* 对角单位槽：r := p ⟹ Z == 1（AA22 gwe_diag_zero 的 LogZ 对偶形） *)
Lemma lgz_diag_one : forall (n : nat) (p : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnp : real_eq (real_list_sum nat p (List.seq 0 n)) real_one),
  real_eq (real_interp_Z n p p eta Hp Hp) real_one.
Proof.
  intros n p eta Hp Hnp.
  unfold real_interp_Z.
  apply (real_eq_trans
           (real_list_sum nat
              (fun i : nat => real_mult
                 (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
                 (real_pow_pos (p i) eta (Hp i)))
              (List.seq 0 n))
           (real_list_sum nat p (List.seq 0 n))
           real_one).
  - apply real_list_sum_ext.
    intro i.
    exact (lgz_pow_split (p i) (Hp i) eta).
  - exact Hnp.
Qed.

(* 对角左支灭绝：r := p 时 real_lt Z 1 驳斥（AA22 gwe_diag_no_gap 对偶形） *)
Lemma lgz_diag_no_gap : forall (n : nat) (p : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnp : real_eq (real_list_sum nat p (List.seq 0 n)) real_one),
  real_lt (real_interp_Z n p p eta Hp Hp) real_one -> forall A : Set, A.
Proof.
  intros n p eta Hp Hnp Hlt A.
  destruct (real_lt_not_eq (real_interp_Z n p p eta Hp Hp) real_one
              Hlt (lgz_diag_one n p eta Hp Hnp)).
Qed.

(* ============================================================ *)
(* Part 6：弱严格上界 + 具体反向（rLPO ⟹ 墙）                        *)
(* ============================================================ *)

(* 弱严格上界：∀eps>0, Z < 1+eps（real_interp_Z_le_one_eps 的 Or 两支各通） *)
Lemma lgz_zle_weak_lt :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnp : real_eq (real_list_sum nat p (List.seq 0 n)) real_one)
    (Hnr : real_eq (real_list_sum nat r (List.seq 0 n)) real_one)
    (Heta : real_lt real_zero eta) (Hetale : real_le eta real_one)
    (eps : Real), real_lt real_zero eps ->
  real_lt (real_interp_Z n p r eta Hp Hr) (real_plus real_one eps).
Proof.
  intros n p r eta Hp Hr Hnp Hnr Heta Hetale eps Heps.
  assert (Hstep : real_lt (real_plus real_one (real_mult eps lgz_half))
                          (real_plus real_one eps))
    by (apply (lgz_one_half_lt_one eps Heps)).
  destruct (real_interp_Z_le_one_eps n p r eta Hp Hr Hnp Hnr Heta Hetale
              (real_mult eps lgz_half)
              (real_mult_positive eps lgz_half Heps
                 (real_inv_pos_pos (real_plus real_one real_one)
                    (real_plus_positive real_one real_one
                       real_lt_zero_one real_lt_zero_one)))) as [Hlt | Heq].
  - exact (real_lt_trans (real_interp_Z n p r eta Hp Hr)
             (real_plus real_one (real_mult eps lgz_half))
             (real_plus real_one eps) Hlt Hstep).
  - exact (lgz_le_lt_trans (real_interp_Z n p r eta Hp Hr)
             (real_plus real_one (real_mult eps lgz_half))
             (real_plus real_one eps) (RealSetoid.real_eq_le _ _ Heq) Hstep).
Qed.

(* 具体反向：受限 LPO ⟹ LogZ 墙（Z ≤ 1 精确判定形） *)
Theorem lgz_lpo_zle : rLPO -> lgz_LogZWall.
Proof.
  intros Hdec n p r eta Hp Hr Hnp Hnr Heta Hetale.
  assert (Hhalfpos : real_lt real_zero lgz_half)
    by exact (real_inv_pos_pos (real_plus real_one real_one)
                (real_plus_positive real_one real_one
                   real_lt_zero_one real_lt_zero_one)).
  destruct (lgz_half_eventual_ub) as [Nv HNv].
  destruct (Hdec (real_plus real_one
                    (real_opp (real_interp_Z n p r eta Hp Hr))))
    as [[c [Hc [N HN]]] | Hz].
  - (* |1−Z| ≥ c ⟹ Z < 1（Q 层两分消去 ≥1 支） *)
    apply inl.
    assert (Hcpos : Qlt 0 c) by (apply QltT_to_Qlt; exact Hc).
    assert (Hcp : real_lt real_zero (real_const c)).
    { unfold real_lt.
      exists (c * (1#2)). split.
      - apply Qlt_to_QltT.
        assert (H0 : 0 * (1#2) < c * (1#2))
          by (apply (Qmult_lt_compat_r 0 c (1#2));
              [exact lgz_q_pos_half | exact Hcpos]).
        rewrite Qmult_0_l in H0.
        exact H0.
      - exists O. intros n0 _. apply Qlt_to_QltT.
        assert (Hcz : projT1 (real_const c) n0 == c) by reflexivity.
        rewrite Hcz.
        assert (Hz0 : projT1 real_zero n0 == 0) by reflexivity.
        rewrite Hz0.
        lra. }
    destruct (lgz_zle_weak_lt n p r eta Hp Hr Hnp Hnr Heta Hetale
                (real_mult (real_const c) lgz_half)
                (real_mult_positive (real_const c) lgz_half Hcp Hhalfpos))
      as [eps2 [Heps2 [N2 HN2]]].
    exists c. split.
    + exact Hc.
    + exists (Nat.max N (Nat.max N2 Nv)). intros m Hm.
      assert (HmN : NatLe N m).
      { apply NatLe_lift.
        pose proof (NatLe_drop _ _ Hm) as Hdn.
        lia. }
      assert (HmN2 : NatLe N2 m).
      { apply NatLe_lift.
        pose proof (NatLe_drop _ _ Hm) as Hdn.
        lia. }
      assert (HmNv : NatLe Nv m).
      { apply NatLe_lift.
        pose proof (NatLe_drop _ _ Hm) as Hdn.
        lia. }
      assert (Hone : projT1 real_one m == 1) by reflexivity.
      assert (Hcz : projT1 (real_const c) m == c) by reflexivity.
      set (Zm := projT1 (real_interp_Z n p r eta Hp Hr) m) in *.
      (* HN 换形：c < |1 − Zm|（Qeq 位移桥） *)
      assert (Habs1 : Qlt c (Qabs (1 - Zm))).
      { pose proof (HN m HmN) as HNn.
        pose proof (QltT_to_Qlt c
                      (Qabs
                         (projT1 (real_plus real_one
                                    (real_opp (real_interp_Z n p r eta Hp Hr))) m)) HNn) as HNn'.
        apply (lgz_qlt_shift_r c
                 (projT1 (real_plus real_one
                            (real_opp (real_interp_Z n p r eta Hp Hr))) m)
                 (1 - Zm)).
        - unfold Zm.
          rewrite (real_plus_proj real_one
                     (real_opp (real_interp_Z n p r eta Hp Hr)) m).
          rewrite (real_opp_proj (real_interp_Z n p r eta Hp Hr) m).
          lra.
        - exact HNn'. }
      pose proof (HN2 m HmN2) as H2r.
      pose proof (HNv m HmNv) as H58.
      (* H2r 换形：eps2 < 1 + c·half_m − Zm *)
      assert (H2r' : Qlt eps2 (1 + c * projT1 lgz_half m - Zm)).
      { pose proof (QltT_to_Qlt eps2
                      (projT1 (real_plus real_one
                                 (real_mult (real_const c) lgz_half)) m -
                       projT1 (real_interp_Z n p r eta Hp Hr) m) H2r) as H2r'.
        apply (lgz_qlt_shift2_r eps2
                 (projT1 (real_plus real_one
                            (real_mult (real_const c) lgz_half)) m -
                  projT1 (real_interp_Z n p r eta Hp Hr) m)
                 (1 + c * projT1 lgz_half m - Zm)).
        - unfold Zm.
          rewrite (real_plus_proj real_one
                     (real_mult (real_const c) lgz_half) m).
          rewrite (real_mult_proj (real_const c) lgz_half m).
          rewrite Hcz.
          rewrite Hone.
          lra.
        - exact H2r'. }
      (* 半量桥：c·half_m < c *)
      assert (Hchc : Qlt (c * projT1 lgz_half m) c).
      { assert (H1 : Qlt (projT1 lgz_half m * c) ((5#8) * c))
          by (apply (Qmult_lt_compat_r (projT1 lgz_half m) (5#8) c);
              [exact Hcpos | exact H58]).
        assert (H2 : Qlt ((5#8) * c) (1 * c))
          by (apply (Qmult_lt_compat_r (5#8) 1 c);
              [exact Hcpos | apply (proj2 (Qlt_alt (5#8) 1)); reflexivity]).
        assert (H3 : 1 * c == c) by ring.
        rewrite H3 in H2.
        assert (Hr4 : projT1 lgz_half m * c == c * projT1 lgz_half m) by ring.
        apply (lgz_qlt_shift (projT1 lgz_half m * c)
                 (c * projT1 lgz_half m) c).
        - exact Hr4.
        - exact (Qlt_trans _ _ _ H1 H2). }
      (* Zm < 1 + c·half_m（弱严格上界的直接读出） *)
      assert (Hs1 : Qlt Zm (1 + c * projT1 lgz_half m)).
      { assert (Hpos2 : Qlt 0 eps2) by (apply QltT_to_Qlt; exact Heps2).
        lra. }
      assert (Hs3 : Qlt Zm (1 + c)).
      { apply (Qlt_trans Zm (1 + c * projT1 lgz_half m) (1 + c)).
        - exact Hs1.
        - apply (lgz_q_plus_lt_l (c * projT1 lgz_half m) c 1).
          exact Hchc. }
      destruct (Qlt_le_dec Zm 1) as [Hlt1 | Hge1].
      { (* Z_m < 1：c < 1 − Z_m 直得 *)
        apply Qlt_to_QltT.
        assert (Habsp : Qabs (1 - Zm) == 1 - Zm)
          by (apply Qabs_pos; lra).
        apply (lgz_qlt_shift2_r c (1 - Zm) (projT1 real_one m - Zm)).
        { rewrite Hone.
          ring. }
        { exact (lgz_qlt_shift2_r c (Qabs (1 - Zm)) (1 - Zm) Habsp Habs1). } }
      { (* Z_m ≥ 1：与 HN 矛盾，消去 *)
        exfalso.
        assert (Hle : Qle (1 - Zm) 0) by lra.
        assert (Habsp : Qabs (1 - Zm) == - (1 - Zm))
          by (apply q_abs_neg_eq; exact Hle).
        assert (HN2c : Qlt c (- (1 - Zm)))
          by (apply (lgz_qlt_shift2_r c (Qabs (1 - Zm)) (- (1 - Zm)));
              [ exact Habsp | exact Habs1 ]).
        apply (Qlt_irrefl c).
        apply (Qlt_le_trans c (Zm - 1) c).
        { apply (lgz_qlt_shift2_r c (- (1 - Zm)) (Zm - 1)).
          - ring.
          - exact HN2c. }
        { lra. } }
  - (* 1−Z 逐点归零 ⟹ Z == 1（右支） *)
    apply inr.
    intros del Hdel.
    destruct (Hz del Hdel) as [N HN].
    exists N. intros m Hm.
    assert (Hone : projT1 real_one m == 1) by reflexivity.
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (projT1 (real_interp_Z n p r eta Hp Hr) m - projT1 real_one m))
             (Qabs (projT1 real_one m - projT1 (real_interp_Z n p r eta Hp Hr) m)) del).
    + apply q_eq_le.
      rewrite <- (Qabs_opp (projT1 real_one m - projT1 (real_interp_Z n p r eta Hp Hr) m)).
      apply q_abs_congr.
      ring.
    + pose proof (HN m Hm) as HNn.
      pose proof (QltT_to_Qlt
                    (Qabs
                       (projT1 (real_plus real_one
                                  (real_opp (real_interp_Z n p r eta Hp Hr))) m)) del HNn) as HNn'.
      apply (lgz_qlt_abs_shift
               (projT1 (real_plus real_one
                          (real_opp (real_interp_Z n p r eta Hp Hr))) m)
               (projT1 real_one m - projT1 (real_interp_Z n p r eta Hp Hr) m) del).
      { rewrite (real_plus_proj real_one
                   (real_opp (real_interp_Z n p r eta Hp Hr)) m).
        rewrite (real_opp_proj (real_interp_Z n p r eta Hp Hr) m).
        rewrite Hone.
        ring. }
      { exact HNn'. }
Qed.

(* ============================================================ *)
(* Part 7：判定件——合账（泛型正向 + 具体反向）                        *)
(* ============================================================ *)

Definition lgz_equivalence :
  And (forall (ZWf : Real -> Real),
         (forall x : Real,
             sigT (fun xi : Real =>
               real_eq (ZWf xi)
                 (real_plus real_one (real_opp (real_mult x x))))) ->
         (forall x : Real, real_le (ZWf x) real_one) -> rLPO)
      (rLPO -> lgz_LogZWall) :=
  (lgz_log_z_wall_lpo, lgz_lpo_zle).

(* ============================================================ *)
(* 判定打印                                                         *)
(* ============================================================ *)

Print Assumptions lgz_log_z_wall_lpo.
Print Assumptions lgz_lpo_zle.
Print Assumptions lgz_equivalence.
Print Assumptions lgz_diag_one.
Print Assumptions lgz_diag_no_gap.

(* ============================ §4 件位 CZB12（组 E-STAGING-CZB12） ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpRealLeB UpReqEnvelopeDual UpReqConstEnvelope UpReqDyadicLog.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.PeanoNat Lia.

(* ============================================================ *)
(* §1 log 2 载体：−log(1/2) = −(1·(−ln2))，二进制有理点 1/2 轴的取反    *)
(* ============================================================ *)
Definition ltb_log_two : Real := real_opp (dyd_axis_neg 0).

(* ============================================================ *)
(* §2 相容性：与既有 inline 常数面（c3e_ln2_real，交错调和柯西实数）      *)
(*    逐点同一（real_eq），即 dyd_ln2 的取反翻转让两面相容。              *)
(* ============================================================ *)
Theorem ltb_log_two_eq_ln2 : real_eq ltb_log_two dyd_ln2.
Proof.
  apply real_eq_of_zero_diff. intro n.
  unfold ltb_log_two, dyd_axis_neg.
  repeat rewrite real_opp_proj.
  repeat rewrite real_mult_proj.
  repeat rewrite real_const_proj.
  repeat rewrite real_opp_proj.
  assert (Hz1 : (Z.of_nat (Nat.succ 0) # 1) == (1#1)%Q) by reflexivity.
  rewrite Hz1.
  ring.
Qed.

(* ============================================================ *)
(* §3 log 2 闭式双边包络（ln(1/2) 上/下包络取反翻转装载；宽 2·t2 n）      *)
(* ============================================================ *)
Theorem ltb_log_two_env : forall n : nat,
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo) ltb_log_two)
        (And (real_le_b ltb_log_two (real_const hi))
             (QeqT (hi - lo) (2 * t2 n))))).
Proof.
  intro n.
  destruct (dyd_ln_env_neg 0 n) as [lo0 [hi0 [Hlo [Hhi Hw]]]].
  exists ((- hi0)%Q). exists ((- lo0)%Q).
  unfold ltb_log_two.
  split.
  - (* 下端 −hi0：Hhi 取反翻转 + const 负号归一 *)
    apply (dyd_le_b_eq_l _ _ _
             (dyd_le_b_opp_flip _ _ Hhi)
             (real_eq_sym _ _ (dyd_opp_const_eq hi0))).
  - split.
    + (* 上端 −lo0：Hlo 取反翻转 + const 负号归一 *)
      apply (dyd_le_b_eq_r _ _ _
               (dyd_le_b_opp_flip _ _ Hlo)
               (dyd_opp_const_eq lo0)).
    + (* 宽：(−lo0)−(−hi0) == hi0−lo0 == 2·(1·t2 n) == 2·t2 n *)
      apply qeq_imp_qeqT. apply qeqT_imp_qeq in Hw.
      setoid_replace ((- lo0) - (- hi0))%Q with (hi0 - lo0)%Q by ring.
      rewrite Hw.
      assert (Hz1 : (Z.of_nat (Nat.succ 0) # 1) == (1#1)%Q) by reflexivity.
      rewrite Hz1. ring.
Qed.

(* ============================================================ *)
(* §4 Q 层速率：包络宽 2·t2 n = 1/(n+1) 构造性收敛（c3e_env_rate_ln2      *)
(*    逐字实例；t2 为定义性同项）。                                       *)
(* ============================================================ *)
Theorem ltb_log_two_rate : forall eps : Q, Qlt 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qlt (2 * t2 n) eps).
Proof. intros eps Heps. exact (c3e_env_rate_ln2 eps Heps). Qed.

(* ============================================================ *)
(* §5 机面：real_log 2（dyd_const_pos 正性见证位）闭式夹逼 [1/2, 1]。      *)
(*    下件 = evd_log_ge_inv_one_B（1 − 1/m 形，端点经 real_inv_pos        *)
(*    常数投影归一）；上件 = real_log_le_linear_B（m − 1 形）。            *)
(* ============================================================ *)
Lemma ltb_two_Qpos : Qlt 0 (2#1)%Q.
Proof. unfold Qlt, Qlt_bool. exact eq_refl. Qed.

Theorem ltb_log_two_machine_bounds :
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo)
                    (real_log (real_const (2#1)%Q)
                              (dyd_const_pos (2#1)%Q ltb_two_Qpos)))
        (And (real_le_b (real_log (real_const (2#1)%Q)
                                   (dyd_const_pos (2#1)%Q ltb_two_Qpos))
                        (real_const hi))
             (QeqT (hi - lo) ((1#1)%Q - (1#2)%Q))))).
Proof.
  assert (Hnorm_lo :
    real_eq (real_plus real_one
               (real_opp (real_inv_pos (real_const (2#1)%Q)
                          (dyd_const_pos (2#1)%Q ltb_two_Qpos))))
            (real_const (1#2)%Q)).
  { apply real_eq_of_zero_diff. intro n.
    repeat rewrite real_plus_proj.
    repeat rewrite real_opp_proj.
    rewrite dyd_one_proj.
    rewrite (dyd_const_inv_proj (2#1)%Q ltb_two_Qpos n).
    repeat rewrite real_const_proj.
    assert (Hhalf : (1 / (2#1)%Q) == (1#2)%Q) by reflexivity.
    rewrite Hhalf. ring. }
  assert (Hnorm_hi :
    real_eq (real_plus (real_const (2#1)%Q) (real_opp real_one))
            (real_const (1#1)%Q)).
  { apply real_eq_of_zero_diff. intro n.
    repeat rewrite real_plus_proj.
    repeat rewrite real_opp_proj.
    repeat rewrite real_const_proj.
    rewrite dyd_one_proj. ring. }
  exists ((1#2)%Q). exists ((1#1)%Q). split.
  - (* 下：1 − 1/2 = 1/2 *)
    apply (dyd_le_b_eq_l _ _ _
             (evd_log_ge_inv_one_B (real_const (2#1)%Q)
                (dyd_const_pos (2#1)%Q ltb_two_Qpos))
             Hnorm_lo).
  - split.
    + (* 上：2 − 1 = 1 *)
      apply (dyd_le_b_eq_r _ _ _
               (real_log_le_linear_B (real_const (2#1)%Q)
                  (dyd_const_pos (2#1)%Q ltb_two_Qpos))
               Hnorm_hi).
    + (* 宽：1 − 1/2 自证 *)
      apply qeq_imp_qeqT. apply Qeq_refl.
Qed.

(* ============================================================ *)
(* §6 公理面留痕（Print Assumptions 全主件核验 Closed）                    *)
(* ============================================================ *)
Print Assumptions ltb_log_two_eq_ln2.
Print Assumptions ltb_log_two_env.
Print Assumptions ltb_log_two_rate.
Print Assumptions ltb_log_two_machine_bounds.
Print Assumptions ltb_two_Qpos.
