(* ==========================================================================)
   UpAblDistLogEq.v — dist_log_eq_linear 前提的具体 Regular-Real 载体实例供给
   使命: 族E eq 侧闭合件：主件 ydle_dist_log_eq_linear（前提语句逐字对齐）、短链重证件、全显式实例参形，及具体层孪生证书二件担提取见证面。
   依赖: CW_ConstructiveWorld_219、G07_KLWall、UpReqKLSTangent、UpReqAlgebra。
   对标: 对数切线不等式 log x ≤ x−1 的等号情形（凸分析）。
   构造性: 本件为零承认词面件（无新增假设声明、无经典逻辑导入、无提取公理占位）；语句面全 req/lt 接口 Set 值；全 Qed 闭合；新名 ydle_ 前缀全库唯一。
   编译配方: Rocq 9.1 直调 coqc（无 -Q），cpu_guard 包裹，-o 输出临时目录。
   ========================================================================== *)

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
Require Import G07_KLWall.
Require Import UpReqKLSTangent.
Require Import UpReqAlgebra.

Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* §1 重证短链——S07/G07 本源骨架（不经 t1/t34 成品件）                          *)
(*   证明骨架与 t34_log_eq_linear_weak 先例同款：                               *)
(*     real_weak_trich（S07:5719 双否形弱三分，直觉主义有效不触 LPO）           *)
(*     + klst_log_tangent_neg（0<x<1 支，G07:2568）                             *)
(*     + klst_log_tangent_pos（1<x 支，G07:173）                                *)
(*     + RealSetoid.real_lt_compat（切点前提沿 req 的传输，成对形）             *)
(*     + real_lt_irrefl（S02:2391）收紧。                                       *)
(* ============================================================ *)

Lemma ydle_dist_log_eq_linear_short : forall (x : Real) (Hx : lt zero x),
  req (log x Hx) (req_minus x one) -> req x one.
Proof.
  intros x Hx Heqlin.
  (* 中间断言：接口投影 req/lt/log/req_minus 在 RealEnhancedReal 实例上与        *)
  (* 具体层 real_eq/real_lt/real_log/plus-opp 形态互通（t34 先例同款转换判定）。  *)
  assert (Heq : real_eq (real_log x Hx) (real_plus x (real_opp real_one)))
    by exact Heqlin.
  apply (real_weak_trich x real_one).
  - (* 情形 x < 1：负支切线 klst_log_tangent_neg 与恒等代换 Heq ⟹ x−1 < x−1，由 real_lt_irrefl 排除。 *)
    intro Hlt.
    assert (Htan : real_lt (real_log x Hx) (real_plus x (real_opp real_one)))
      by exact (klst_log_tangent_neg x Hx Hlt).
    exact (real_lt_irrefl (real_plus x (real_opp real_one))
             (RealSetoid.real_lt_compat (real_log x Hx)
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             Heq
                             (real_eq_refl (real_plus x (real_opp real_one)))
                             Htan)).
  - (* 情形 1 < x：正支切线 klst_log_tangent_pos 与同款收紧排除。 *)
    intro Hlt.
    assert (Htan : real_lt (real_log x Hx) (real_plus x (real_opp real_one)))
      by exact (klst_log_tangent_pos x Hx Hlt).
    exact (real_lt_irrefl (real_plus x (real_opp real_one))
             (RealSetoid.real_lt_compat (real_log x Hx)
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             Heq
                             (real_eq_refl (real_plus x (real_opp real_one)))
                             Htan)).
Qed.

(* ============================================================ *)
(* §2 主件——t34 骨架经形态转换直供该前提：                                     *)
(*   经 UpReqKLSTangent.t1_log_eq_linear_inject（G07/S07 链成品）零假设直接推得；*)
(*   与 §1 互为独立复核（主件走成品链，短链走本源骨架）。                       *)
(* ============================================================ *)

Lemma ydle_dist_log_eq_linear : forall (x : Real) (Hx : lt zero x),
  req (log x Hx) (req_minus x one) -> req x one.
Proof.
  intros x Hx Heqlin.
  exact (t1_log_eq_linear_inject x Hx Heqlin).
Qed.

(* ============================================================ *)
(* §3 全显式实例参形——供 UpReqDist Section ReqFEP 出节位使用                    *)
(*   出节后前提实参形 = @lt/@req/@log/@req_minus 全带实例参；                   *)
(*   本件全显式重述主件，使用面逐参代入免推参。                                 *)
(* ============================================================ *)

Lemma ydle_dist_log_eq_linear_ex :
  forall (x : Real)
         (Hx : @lt Real RealEnhancedReal (@zero Real RealEnhancedReal) x),
    @req Real RealEnhancedReal
         (@log Real RealEnhancedReal x Hx)
         (@req_minus Real RealEnhancedReal x (@one Real RealEnhancedReal)) ->
    @req Real RealEnhancedReal x (@one Real RealEnhancedReal).
Proof.
  intros x Hx Heqlin.
  exact (ydle_dist_log_eq_linear x Hx Heqlin).
Qed.

(* ============================================================ *)
(* §4 具体层孪生证书——提取见证面                                               *)
(*   语句形 = t1_log_eq_linear_inject 同构（real_lt/real_eq 直陈），            *)
(*   与接口形主件/短链同内容（两层在 RealEnhancedReal 上形态互通）。             *)
(*   已验证：该形提取零残留（对照 UpReqKLSTangent.ml 的 t1 提取体）。            *)
(* ============================================================ *)

Lemma ydle_dist_log_eq_linear_real : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log x Hx) (real_plus x (real_opp real_one)) -> real_eq x real_one.
Proof.
  intros x Hx Heq.
  exact (t1_log_eq_linear_inject x Hx Heq).
Qed.

Lemma ydle_dist_log_eq_linear_short_real : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log x Hx) (real_plus x (real_opp real_one)) -> real_eq x real_one.
Proof.
  intros x Hx Heq.
  apply (real_weak_trich x real_one).
  - (* 情形 x < 1：负支切线 klst_log_tangent_neg 与恒等代换 Heq ⟹ x−1 < x−1，由 real_lt_irrefl 排除。 *)
    intro Hlt.
    assert (Htan : real_lt (real_log x Hx) (real_plus x (real_opp real_one)))
      by exact (klst_log_tangent_neg x Hx Hlt).
    exact (real_lt_irrefl (real_plus x (real_opp real_one))
             (RealSetoid.real_lt_compat (real_log x Hx)
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             Heq
                             (real_eq_refl (real_plus x (real_opp real_one)))
                             Htan)).
  - (* 情形 1 < x：正支切线 klst_log_tangent_pos 与同款收紧排除。 *)
    intro Hlt.
    assert (Htan : real_lt (real_log x Hx) (real_plus x (real_opp real_one)))
      by exact (klst_log_tangent_pos x Hx Hlt).
    exact (real_lt_irrefl (real_plus x (real_opp real_one))
             (RealSetoid.real_lt_compat (real_log x Hx)
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             Heq
                             (real_eq_refl (real_plus x (real_opp real_one)))
                             Htan)).
Qed.

(* ============================================================ *)
(* 提取核验位：单条合并命令列全部常量（多条抽取命令会互相覆写 .ml，             *)
(*   一律单命令 + let 计数核验）。只列具体层孪生二件——接口形不作提取出口        *)
(*   （形态差注记见头注）。                                                     *)
(* ============================================================ *)

Separate Extraction ydle_dist_log_eq_linear_real
                    ydle_dist_log_eq_linear_short_real.
