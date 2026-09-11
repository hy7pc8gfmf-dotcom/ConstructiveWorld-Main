(* ============================================================ *)
(* UpReqLogCompD2.v —— 槽 7 装配收口席：req_temp_strict_ident2 复合重建放电    *)
(*   目标槽 = req_temp_strict_ident2@UpFirewallReq:144（七槽判词之槽 7：       *)
(*   纯装配工时阻塞、链完备零缺件，由本席直接装配收口）。                      *)
(*   组装路线（前席判词 E-STAGING 20260910 + E-LOGC-1/2 配方）：               *)
(*     T6 两例（logc_relative_entropy_temp_decomp @ (t1,t2)/(t2,t1) 实例化）   *)
(*     + T5 换形（logc_entropy_temp_explicit：-H(t) ≡ -E(t)/t - log Z(t)）     *)
(*     → 8 项置换坍缩（logZ 双抵消 + X:=1/t1-1/t2 数缩）→ distrib 收口。       *)
(*   消去核：UpReqLogCompD Part 0 logc_cancel_left/logc_plus_assoc_cancel      *)
(*     已备；本席新增 Part 0 置换助件三件（纯 req 代数：swap_mid/exchange/     *)
(*     logpair_zero），全程 req 求和桥机只经 T5/T6 消费，零逐点私开。          *)
(* ------------------------------------------------------------------ *)
(* 供给槽（与 UpReqLogCompD LogcTemp 节同位，零新增）：                        *)
(*   sum 桥机三件 tsum_ext/tsum_add/tsum_linear + zt_spec + zt_pos             *)
(*   + B1 tsup_compat + B2 tsup_log_exp_neg（七件，全为 T5/T6 既有供给形）。   *)
(* 防撞：logc2_ 前缀 + logc_temp_strict_ident2，全库 attn/001 grep 零命中      *)
(*   （建前 2026-09-10 逐名实查；文件名 UpReqLogCompD2 零命中）。              *)
(* 红线：Set 层零 Prop（结论全 req/lt 接口 Set 值）；全 Qed 闭合；零公理；      *)
(*   既有文件零改（只消费 .vo）；零 git；温控 guard 错峰（复用 cpu_guard.ps1，  *)
(*   零改既有脚本）。req_minus δ 透明（UpReqAlgebra:58 = plus a (opp b)），     *)
(*   放电件陈述与 UpFirewallReq:144 原文同位（minus 形），证内 unfold 换形。    *)
(* 编译配方：cpu_guard.ps1 负载包装（CoreN 绑核）                              *)
(*   coqc -Q . "" -Q "..\001" "" UpReqLogCompD2.v（经 .cmd 批处理，零裸调）     *)
(* G4：coqchk -Q . "" -Q "..\001" "" UpReqLogCompD2（长窗，禁 -o）             *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Export G05_LogSmall.
Require Export G05_LogSmall.
Require Import UpReqLogCompD.
Require Import UpReqAlgebra.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Part 0：置换助件（泛型 RIS；纯 req 代数，零供给槽）                         *)
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

(* P3：对消零件 (x-y)+(y-x) ≡ 0（槽 7 logZ 双抵消核） *)
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
(* Part 1：温度节（供给槽与 UpReqLogCompD LogcTemp 节同位，零新增）            *)
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
(* req_Z_temp_spec 槽（UpFirewallReq 同位） *)
Hypothesis zt_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (energy s)))).
(* zt_pos 槽 = UpReqTempEntropy req_Z_temp_pos 产物位 *)
Hypothesis zt_pos : forall (t : R) (Ht : lt zero t), lt zero (Z_temp t).
(* B1/B2 供给槽（同 UpReqLogCompD LogcTemp） *)
Hypothesis tsup_compat : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Hypothesis tsup_log_exp_neg : forall u : R,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).

(* Q1【T5 换形】：-H(t) ≡ -E(t)/t - log Z(t)（T6 节内 HoppH 同型升为独立件） *)
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
(*   KL(t2‖t1) ≡ (E2/t1 - E2/t2) + (log Z1 - log Z2)                          *)
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
  - (* T6 实例（t2 位:=t1, t1 位:=t2）：KL(t2‖t1) ≡ (-H2 + E2/t1) + log Z1 *)
    exact (logc_relative_entropy_temp_decomp S sumf tsum_ext tsum_add tsum_linear
              energy Z_temp zt_spec zt_pos tsup_compat tsup_log_exp_neg
              t1 Ht1 t2 Ht2).
  - (* 8 项之一翼：-H2 换形 → (-E2/t2 - log Z2 + E2/t1) + log Z1 → 置换 *)
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
(*   KL(t1‖t2) ≡ (E1/t2 - E1/t1) + (log Z2 - log Z1)                          *)
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
  - (* T6 实例（原位）：KL(t1‖t2) ≡ (-H1 + E1/t2) + log Z2 *)
    exact (logc_relative_entropy_temp_decomp S sumf tsum_ext tsum_add tsum_linear
              energy Z_temp zt_spec zt_pos tsup_compat tsup_log_exp_neg
              t2 Ht2 t1 Ht1).
  - (* 8 项之另一翼：-H1 换形 → (-E1/t1 - log Z1 + E1/t2) + log Z2 → 置换 *)
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

(* Q4【槽 7 放电件】：KL(t2‖t1)+KL(t1‖t2) ≡ (1/t1-1/t2)·(E2-E1)              *)
(*   （req_temp_strict_ident2@UpFirewallReq:144 复合重建；req_minus δ 透明，   *)
(*   证内 unfold 换 plus/opp 形后 8 项置换坍缩 + distrib 收口）                *)
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
  - (* distrib 收口：X·(E2-E1) ≡ X·E2 + X·(-E1) ≡ 4 项数缩形（反向链） *)
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
