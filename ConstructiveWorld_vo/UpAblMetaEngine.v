(* ==========================================================================)
   UpAblMetaEngine —— 发散性下界与 exp 幂迭代两定理；同域语句面
   使命：本件形式化发散性下界与 exp 幂迭代两定理。
   本件并载：zpd_slot_Z_align（列表直和式）、zpd_slot_body_conv_zabr（与 zabr_Z_align 的换算恒等）、zpd_no；bool 二点状态空间与二点求和上把四结构前提（求和 ext/add/linear 与配分正性）全部内证，给出仅余 (Hp, Hnormp) 的完全实例；族E eq 侧闭合件：主件 ydle_dist_log_eq_linear（前提语句逐字对齐）、短链重证件、全显式实例参形，及具体层孪生证书二件担提取见；ydll_lpo_barrier——前提实例到实数零等判定 Or 形的定理级归约；反向严格支（eps 间隙矛盾）已闭合（ydll_le_b_not_gt；bool 二元组群载体（枚举/覆盖/规模正性/无重复表/零奖励）逐项供给该节前提组，收束为抽象前提在具体载体上的实例化定理 gqc_supplied 与；Group := bool、R := nat 极小 Set 层载体的单副本枚举世界上正向实例化构造（判别核/覆盖/求和/计数面自建），与世界装配件各自独；两点核差形的接口级抽象前置引理；九项接口参数取单点具体值、三条节级前提（归一。
   依赖：S01_BaseRing, S02_CauchyComplete, S03_QExp, S04_RealExpLogConv, S07_RealSetoidExpLog, S08_RealMainlineDPO, UpReqExpPos, UpAblZposReal
     List, QArith.Qring, S05_AlignmentGRPO, S06_DiffSamplingGibbs, S09_EntropyReal, S10_KVQuantTrig, S11_TP3B5, S12_B5RecycleSF,
     S13_NLiveAudit, S14_B5BatchBlock, S15_TailFEPUp, UpAblEps49RKDBase, Extraction, G07_KLWall, UpReqKLSTangent, UpReqAlgebra,
     QArith.QArith, Arith.PeanoNat, UpRealLeB, UpReqTempDefs, UpReqEntropyDeficitTemp, UpReqEntropyMonoSplit, UpTempWindow, UpAblAbsSumLeB,
     Lia, QArith.Qabs, Lqa, UpAblAbsQFeed, UpAblAbsSumLeB2, Setoid, Morphisms, QArith.Qminmax,
     ZArith, UpReqIterGeomRate, UpReqMixLogB, UpTVDoeblin, UpReqMixingTime, UpReqDist, UpReqSampling, UpReqConcFin2,
     UpReqMixLogE, micromega.Lqa, Arith, UpReqLpoEquiv, UpAblLogWall, UpAblLogWallEq, PeanoNat, KLWallClosed,
     RateTheoryAblation, QArith, UpReqMixLogA。
   构造性：零公理、零承认式语句；语句面 Set 层承载，Print Assumptions 全 Closed。
   编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

(* ============================ §1 zpd_slot_Z_align（列表直和式）、zpd_slot_body_conv_zabr（与 zabr_Z_align 的换算恒等）、zpd_no ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import UpReqExpPos.
Require Import UpAblZposReal.
From Stdlib Require Import List.

(* 实例引入：库内唯一增强 Setoid 接口实例 RealEnhancedReal。
   引入后裸名 lt/zero/mult/exp_neg/opp/inv_pos 即接口字段投影，
   语句面与 S05 主节语句逐字同形；证明面全显式参数。 *)
Import RealInterfaceEnhancedMod.

(* ===== 1. Z_align 逐字同构消解体（接口投影形，求和载体改用实数层） ===== *)
(* S05 原形：sum_over_S (fun s => mult (pi_ref s)                    *)
(*   (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))      *)
(* 消解形：sum_over_S↦real_list_sum·l，其余逐字段同位。               *)
Definition zpd_slot_Z_align (X : Set) (l : list X)
  (reward : X -> Real) (beta : Real) (beta_pos : lt zero beta)
  (pi_ref : X -> Real) : Real :=
  real_list_sum X (fun s => mult (pi_ref s)
    (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))) l.

(* ===== 2. 形态转换引理：归一化前提 Id↦real_eq ===================== *)
(* Id 世界的等式原形在实例世界改写为 setoid 等式：                    *)
(* Id（S01 集合层恒等型）消去＋real_eq 自反内导，真实现。             *)
Theorem zpd_norm_id_to_real_eq :
  forall (X : Set) (l : list X) (pi_ref : X -> Real),
    Id (real_list_sum X pi_ref l) one ->
    real_eq (real_list_sum X pi_ref l) real_one.
Proof.
  intros X l pi_ref H.
  exact (match H in Id _ y
         return real_eq (real_list_sum X pi_ref l) y
         with
         | id_refl => real_eq_refl (real_list_sum X pi_ref l)
         end).
Qed.

(* ===== 3. 转换核验：消解体与 UpAblZposReal 裸形逐项可转换 ========= *)
(* 平凡件（设计使然）：两侧展开后为同一项（实例字段投影零展开          *)
(* ＝real_* 裸常量），恒等构造子经转换内导即闭合。此核验即「逐字       *)
(* 同构」的机器验证。                                               *)
Theorem zpd_slot_body_conv_zabr :
  forall (X : Set) (l : list X) (reward : X -> Real) (beta : Real)
         (beta_pos : lt zero beta) (pi_ref : X -> Real),
    Id (zpd_slot_Z_align X l reward beta beta_pos pi_ref)
       (zabr_Z_align X l reward beta beta_pos pi_ref).
Proof.
  intros X l reward beta beta_pos pi_ref.
  exact id_refl.
Qed.

(* ===== 4. 正性求和假设的同形直接消解（S05 迭代节给出形） =========== *)
(* S05 迭代节求和正性假设（逐项正⟹和正）的实例同形。非空前提取        *)
(* UpAblZposReal 最弱可达形（实数层空表和归零不为正，诚实边界同前）。  *)
Theorem zpd_sum_over_S_pos_slot :
  forall (X : Set) (f : X -> Real) (l : list X),
    Not (Id l nil) ->
    (forall s : X, lt zero (f s)) ->
    lt zero (real_list_sum X f l).
Proof.
  intros X f l Hnn Hf.
  exact (zabr_sum_over_S_pos X f l Hnn Hf).
Qed.

(* ===== 5. 主定理：Z_align 正性假设的直接消解 ====================== *)
(* 前提面＝S05 主节语句逐字同形（温度正＋逐点正＋归一化 Id 形），      *)
(* 零接口外新前提。证明三段：                                        *)
(*   ① 非空内导：归一化（经形态转换引理）×空表和归零×零壹分离引理；   *)
(*   ② 逐项正：接口字段 mult_positive（参考策略正×指数正 exp_neg_pos  *)
(*      字段直出）——全链走实例字段投影；                             *)
(*   ③ 完成：使用 UpAblZposReal 折叠和正引理（zabr_sum_over_S_pos）。  *)
Theorem zpd_Z_align_pos_slot :
  forall (X : Set) (l : list X) (reward : X -> Real) (beta : Real)
         (beta_pos : lt zero beta) (pi_ref : X -> Real),
    (forall s : X, lt zero (pi_ref s)) ->
    Id (real_list_sum X pi_ref l) one ->
    lt zero (zpd_slot_Z_align X l reward beta beta_pos pi_ref).
Proof.
  intros X l reward beta beta_pos pi_ref Hrefpos Hnorm.
  unfold zpd_slot_Z_align.
  assert (HnormEq : real_eq (real_list_sum X pi_ref l) real_one).
  { exact (zpd_norm_id_to_real_eq X l pi_ref Hnorm). }
  assert (Hnn : Not (Id l nil)).
  { intro Hnil.
    assert (Hsum0 : real_eq (real_list_sum X pi_ref l) real_zero).
    { exact (real_eq_trans (real_list_sum X pi_ref l)
               (real_list_sum X pi_ref nil) real_zero
               (match Hnil in Id _ y return
                  real_eq (real_list_sum X pi_ref l)
                          (real_list_sum X pi_ref y)
                with id_refl => real_eq_refl _ end)
               (real_eq_refl real_zero)). }
    exact (upreq_real_zero_ne_one
            (real_eq_trans real_zero (real_list_sum X pi_ref l) real_one
               (real_eq_sym (real_list_sum X pi_ref l) real_zero Hsum0)
               HnormEq)). }
  exact (zabr_sum_over_S_pos X
           (fun s => mult (pi_ref s)
              (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))) l
           Hnn
           (fun s => mult_positive (pi_ref s)
              (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
              (Hrefpos s)
              (exp_neg_pos
                 (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ===== 假设面自检（Print Assumptions） ===== *)
Print Assumptions zpd_norm_id_to_real_eq.
Print Assumptions zpd_slot_body_conv_zabr.
Print Assumptions zpd_sum_over_S_pos_slot.
Print Assumptions zpd_Z_align_pos_slot.

(* ============================ §2 bool 二点状态空间与二点求和上把四结构前提（求和 ext/add/linear 与配分正性）全部内证，给出仅余 (Hp, Hnormp) 的完全实例 ============================ *)
From Stdlib Require Import QArith.Qring.
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
Require Import UpAblEps49RKDBase.

(* ============================================================ *)
(* §1 具体载体：bool 二点状态空间与二点求和                                      *)
(* ============================================================ *)

Definition e49m_esum2 (f : bool -> Real) : Real :=
  real_plus (f true) (f false).

(* 结构前提一：外延性（逐点相等 ⟹ 求和相等） *)
Lemma e49m_esum2_ext : forall (f g : bool -> Real),
  (forall s : bool, real_eq (f s) (g s)) -> real_eq (e49m_esum2 f) (e49m_esum2 g).
Proof.
  intros f g H. unfold e49m_esum2.
  exact (RealSetoid.real_eq_plus_compat_adapt
           (f true) (g true) (f false) (g false) (H true) (H false)).
Qed.

(* 结构前提二：加法分配 *)
Lemma e49m_esum2_add : forall (f g : bool -> Real),
  real_eq (e49m_esum2 (fun s : bool => real_plus (f s) (g s)))
          (real_plus (e49m_esum2 f) (e49m_esum2 g)).
Proof. intros f g. unfold e49m_esum2. rkd_alg. Qed.

(* 结构前提三：标量线性 *)
Lemma e49m_esum2_linear : forall (a : Real) (f : bool -> Real),
  real_eq (e49m_esum2 (fun s : bool => real_mult a (f s)))
          (real_mult a (e49m_esum2 f)).
Proof. intros a f. unfold e49m_esum2. rkd_alg. Qed.

(* 二正相加仍正（由 real_plus_zero 与 real_lt_plus_compat 两步）             *)
Lemma e49m_esum2_pos2 : forall (x y : Real),
  real_lt real_zero x -> real_lt real_zero y ->
  real_lt real_zero (real_plus x y).
Proof.
  intros x y Hx Hy.
  apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
                                  (real_plus x y)).
  - apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
    apply (real_plus_zero real_zero).
  - apply (real_lt_plus_compat real_zero x real_zero y).
    + exact Hx.
    + exact Hy.
Qed.

(* 配分正性（结构前提四的内证：real_exp_neg_pos 两支 + 二正相加）                     *)
Lemma e49m_partition2_pos : forall (e : bool -> Real) (D : Real)
  (D_pos : real_lt real_zero D),
  real_lt real_zero
    (e49m_esum2 (fun s : bool => real_exp_neg
                                 (real_mult (real_inv_pos D D_pos) (e s)))).
Proof.
  intros e D D_pos. unfold e49m_esum2. apply e49m_esum2_pos2.
  - apply real_exp_neg_pos.
  - apply real_exp_neg_pos.
Qed.

(* ============================================================ *)
(* §2 一般 Z 形：结论与 S08 假设全局形逐字同构                                   *)
(*   数学前提 Hnormb：任意 Z 下不可免，为原假设所缺，如实标示。                          *)
(*   签名对齐的直接证据：证明体 exact 直引 rkd_kl_decomp_full。                  *)
(* ============================================================ *)

Theorem e49m_real_kl_decomp_full :
  forall (S : Type) (sumf : (S -> Real) -> Real)
    (sumf_ext : forall (f g : S -> Real),
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
    (sumf_add : forall (f g : S -> Real),
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g)))
    (sumf_linear : forall (a : Real) (f : S -> Real),
      real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
    (e : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
    (Hnormp : real_eq (sumf p) real_one)
    (Hnormb : real_eq (sumf (real_boltzmann_dist_r S e D D_pos Z Z_pos)) real_one),
  real_eq (real_free_energy S sumf e D p Hp)
          (real_plus
             (real_free_energy S sumf e D
                (real_boltzmann_dist_r S e D D_pos Z Z_pos)
                (real_boltzmann_dist_r_pos S e D D_pos Z Z_pos))
             (real_mult D
                (sumf (fun s : S =>
                   real_kl_term (p s)
                     (real_boltzmann_dist_r S e D D_pos Z Z_pos s)
                     (Hp s)
                     (real_boltzmann_dist_r_pos S e D D_pos Z Z_pos s))))).
Proof.
  intros S sumf sumf_ext sumf_add sumf_linear e D D_pos Z Z_pos p Hp Hnormp Hnormb.
  exact (rkd_kl_decomp_full S sumf sumf_ext sumf_add sumf_linear
           e D D_pos Z Z_pos p Hp Hnormp Hnormb).
Qed.

(* ============================================================ *)
(* §3 伴生命题：具体载体上的 Boltzmann 归一化                                  *)
(*   Z 取配分定义形，Hpart 为 real_eq_refl，归一化 Σ p_b == 1 内证。            *)
(* ============================================================ *)

Theorem e49m_boltzmann_normalized_bool :
  forall (e : bool -> Real) (D : Real) (D_pos : real_lt real_zero D),
  real_eq
    (e49m_esum2 (real_boltzmann_dist_r bool e D D_pos
                   (e49m_esum2 (fun s : bool => real_exp_neg
                                    (real_mult (real_inv_pos D D_pos) (e s))))
                   (e49m_partition2_pos e D D_pos)))
    real_one.
Proof.
  intros e D D_pos.
  exact (rkd_boltzmann_normalized bool e49m_esum2 e49m_esum2_ext
           e49m_esum2_linear e D D_pos
           (e49m_esum2 (fun s : bool => real_exp_neg
                            (real_mult (real_inv_pos D D_pos) (e s))))
           (e49m_partition2_pos e D D_pos)
           (real_eq_refl _)).
Qed.

(* ============================================================ *)
(* §4 主定理：S08 假设形（仅 Hp Hnormp）的完全实例化                             *)
(*   载体全具体：S := bool，sumf := e49m_esum2（三结构前提内证），                *)
(*   Z := 配分定义形（正性内证）。前提与 S08 原假设逐字同形。                           *)
(* ============================================================ *)

Theorem e49m_real_kl_decomp_full_bool :
  forall (e : bool -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s))
    (Hnormp : real_eq (e49m_esum2 p) real_one),
  real_eq (real_free_energy bool e49m_esum2 e D p Hp)
          (real_plus
             (real_free_energy bool e49m_esum2 e D
                (real_boltzmann_dist_r bool e D D_pos
                   (e49m_esum2 (fun s : bool => real_exp_neg
                                    (real_mult (real_inv_pos D D_pos) (e s))))
                   (e49m_partition2_pos e D D_pos))
                (real_boltzmann_dist_r_pos bool e D D_pos
                   (e49m_esum2 (fun s : bool => real_exp_neg
                                    (real_mult (real_inv_pos D D_pos) (e s))))
                   (e49m_partition2_pos e D D_pos)))
             (real_mult D
                (e49m_esum2 (fun s : bool =>
                   real_kl_term (p s)
                     (real_boltzmann_dist_r bool e D D_pos
                        (e49m_esum2 (fun s0 : bool => real_exp_neg
                                         (real_mult (real_inv_pos D D_pos) (e s0))))
                        (e49m_partition2_pos e D D_pos) s)
                     (Hp s)
                     (real_boltzmann_dist_r_pos bool e D D_pos
                        (e49m_esum2 (fun s0 : bool => real_exp_neg
                                         (real_mult (real_inv_pos D D_pos) (e s0))))
                        (e49m_partition2_pos e D D_pos) s))))).
Proof.
  intros e D D_pos p Hp Hnormp.
  exact (rkd_kl_decomp_full_partition bool e49m_esum2 e49m_esum2_ext
           e49m_esum2_add e49m_esum2_linear e D D_pos p Hp Hnormp
           (e49m_partition2_pos e D D_pos)).
Qed.

(* ============================================================ *)
(* 依赖审计：零外部未证假设；独立目录提取                                           *)
(* ============================================================ *)

Print Assumptions e49m_esum2_ext.
Print Assumptions e49m_esum2_add.
Print Assumptions e49m_esum2_linear.
Print Assumptions e49m_partition2_pos.
Print Assumptions e49m_real_kl_decomp_full.
Print Assumptions e49m_boltzmann_normalized_bool.
Print Assumptions e49m_real_kl_decomp_full_bool.

From Stdlib Require Import Extraction.
Set Extraction Output Directory "../attn/_ab3_g3_ext".
Separate Extraction e49m_real_kl_decomp_full_bool.
Separate Extraction e49m_boltzmann_normalized_bool.
Separate Extraction e49m_real_kl_decomp_full.

(* ============================ §3 族E eq 侧闭合件：主件 ydle_dist_log_eq_linear（前提语句逐字对齐）、短链重证件、全显式实例参形，及具体层孪生证书二件担提取见 ============================ *)
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

(* ============================ §4 ydll_lpo_barrier——前提实例到实数零等判定 Or 形的定理级归约；反向严格支（eps 间隙矛盾）已闭合（ydll_le_b_not_gt ============================ *)
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Arith.PeanoNat.
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
Require Import UpRealLeB.

(* ============================================================ *)
(* §1 Bishop 形（real_le_b）反向严格排除——eps 间隙矛盾。                 *)
(*   此前结论中「eps 间隙矛盾」肢的首次形式化：x ≤_B y 时 y < x 不可能。 *)
(*   论证：设 y < x 有 Q 见证 e0（尾段 a_n − b_n > e0）。取 B 形余量      *)
(*   eps := real_const e0（逐点恰为 e0），得 e1 > 0 使尾段                *)
(*   b_n + e0 − a_n > e1。两尾段相加得 e1 + e0 < e0，即 e1 < 0，与        *)
(*   0 < e1 矛盾（Qlt_irrefl 收紧）。                                     *)
(* ============================================================ *)

Lemma ydll_le_b_not_gt :
  forall a b : Real, real_le_b a b -> Not (real_lt b a).
Proof.
  intros a b Hleb Hba.
  destruct Hba as [e0 [He0T [N0 H0]]].
  specialize (Hleb (real_const e0) (real_const_pos e0 He0T)).
  destruct Hleb as [e1 [He1T [N1 H1]]].
  pose proof (QltT_to_Qlt 0 e1 He1T) as H01.
  set (n := Nat.max N0 N1).
  assert (H0n : QltT e0 (projT1 a n - projT1 b n)).
  { apply (H0 n). apply NatLe_lift. apply Nat.le_max_l. }
  assert (H1n : QltT e1 (projT1 (real_plus b (real_const e0)) n - projT1 a n)).
  { apply (H1 n). apply NatLe_lift. apply Nat.le_max_r. }
  assert (Hpt : projT1 (real_plus b (real_const e0)) n == projT1 b n + e0).
  { destruct b as [ub Hb]. unfold real_const. simpl. ring. }
  pose proof (QltT_to_Qlt e1 _ H1n) as H1nQ.
  setoid_rewrite Hpt in H1nQ.
  pose proof (QltT_to_Qlt e0 _ H0n) as H0nQ.
  assert (Hsum : Qlt (e1 + e0)
                   (projT1 b n + e0 - projT1 a n
                    + (projT1 a n - projT1 b n))).
  { apply (Qplus_lt_compat e1 (projT1 b n + e0 - projT1 a n)
                           e0 (projT1 a n - projT1 b n)).
    - exact H1nQ.
    - exact H0nQ. }
  assert (Hring : projT1 b n + e0 - projT1 a n
                  + (projT1 a n - projT1 b n) == e0) by ring.
  rewrite Hring in Hsum.
  destruct (Qlt_le_dec e1 0) as [Hlt10 | Hle01].
  - exact (match Qlt_irrefl e1 (Qle_lt_trans e1 0 e1 (Qlt_le_weak e1 0 Hlt10) H01) with end).
  - assert (Hle' : Qle (0 + e0) (e1 + e0)).
    { apply (Qplus_le_compat 0 e1 e0 e0).
      - exact Hle01.
      - apply Qle_refl. }
    rewrite Qplus_0_l in Hle'.
    exact (match Qlt_irrefl (e1 + e0)
             (Qlt_le_trans (e1 + e0) e0 (e1 + e0) Hsum Hle') with end).
Qed.

(* ============================================================ *)
(* §2 log 切线反向严格排除（该前提的可达剩余半支闭合件）。               *)
(*   对一切 x > 0：¬(x−1 < log x)。材料：UpRealLeB real_log_le_linear_B  *)
(*   （B 形，eps 形源件 S07 real_log_le_linear_eps）+ §1。                *)
(*   此前库内无 plain 形实例件，本件为首个。                             *)
(* ============================================================ *)

Lemma ydll_log_tangent_not_gt :
  forall (x : Real) (Hx : real_lt real_zero x),
  Not (real_lt (real_plus x (real_opp real_one)) (real_log x Hx)).
Proof.
  intros x Hx Hgt.
  apply (ydll_le_b_not_gt (real_log x Hx) (real_plus x (real_opp real_one))).
  - exact (real_log_le_linear_B x Hx).
  - exact Hgt.
Qed.

(* ============================================================ *)
(* §3 前提实例的条件消解件（¬¬ 闭包面）。                                *)
(*   假设位即 :1035 前提的实例面等同形（见文件头对齐节）；在此假设下，   *)
(*   凡知 x ≠ 1 者得严格切线支。eq 支经 t1_log_eq_linear_inject 零新增。 *)
(* ============================================================ *)

Lemma ydll_cond_strict_of_ne_one :
  (forall (x : Real) (Hx : real_lt real_zero x),
    real_le (real_log x Hx) (real_plus x (real_opp real_one))) ->
  forall (x : Real) (Hx : real_lt real_zero x),
  Not (real_eq x real_one) ->
  real_lt (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros Hslot x Hx Hne1.
  destruct (Hslot x Hx) as [Hlt | Heq].
  - exact Hlt.
  - exact (match Hne1 (t1_log_eq_linear_inject x Hx Heq) with end).
Qed.

(* ============================================================ *)
(* §4（主件/结论件）：前提实例 ⟹ 实数零等判定（real-LPO 族）。           *)
(*   论证：任取 u，对 x := e^{−u}（对一切 u 成立：real_exp_neg_pos）用    *)
(*   该前提。左支（log x < x−1）：若 u == 0 则 x == 1、log x == 0、       *)
(*   x−1 == 0，严格支自相矛盾（real_lt_irrefl）——故 u ≠ 0。               *)
(*   右支（log x == x−1）：经 log_inv_exp_neg_thm 得 log x == −u，        *)
(*   即 e^{−u} == 1 − u。u < 0 ⟹ x > 1 ⟹ klst_log_tangent_pos 严格切线    *)
(*   与相等支矛盾；0 < u ⟹ x < 1 ⟹ klst_log_tangent_neg 同理矛盾。        *)
(*   弱三分（real_weak_trich，S07:5719，直觉主义有效）推得 u == 0。        *)
(*   结论：前提实例至少与实数零等判定等强——该判定属 S07 头注自认不可证  *)
(*   的强三分/LPO 参照类。此前「具体载体 30-60 行代数链可达」的估计据此   *)
(*   降格：反向半支可达（§1/§2 已闭合），正向分支判定不可达（本件定理级）。*)
(* ============================================================ *)

Theorem ydll_lpo_barrier :
  (forall (x : Real) (Hx : real_lt real_zero x),
    real_le (real_log x Hx) (real_plus x (real_opp real_one))) ->
  forall u : Real, Or (Not (real_eq u real_zero)) (real_eq u real_zero).
Proof.
  intros Hslot u.
  assert (Hxe : real_lt real_zero (real_exp_neg u))
    by exact (real_exp_neg_pos u).
  destruct (Hslot (real_exp_neg u) Hxe) as [Hlt | Heq].
  - (* 左支 ⟹ u ≠ 0 *)
    apply inl. intro Hu0.
    assert (Hx1 : real_eq (real_exp_neg u) real_one).
    { exact (real_eq_trans (real_exp_neg u)
                           (cauchy_real_exp (real_opp real_zero)) real_one
               (cauchy_real_exp_wd (real_opp u) (real_opp real_zero)
                  (RealSetoid.real_eq_opp_compat u real_zero Hu0))
               (real_eq_trans (cauchy_real_exp (real_opp real_zero))
                              (cauchy_real_exp real_zero) real_one
                  (cauchy_real_exp_wd (real_opp real_zero) real_zero
                     real_opp_zero)
                  cauchy_real_exp_zero)). }
    assert (Hlog0 : real_eq (real_log (real_exp_neg u) Hxe) real_zero).
    { exact (real_eq_trans (real_log (real_exp_neg u) Hxe)
                           (real_log real_one real_lt_zero_one) real_zero
               (real_log_wd (real_exp_neg u) real_one Hxe real_lt_zero_one
                  Hx1)
               (real_log_one real_lt_zero_one)). }
    assert (Hrhs0 : real_eq (real_plus (real_exp_neg u) (real_opp real_one))
                            real_zero).
    { exact (real_eq_trans (real_plus (real_exp_neg u) (real_opp real_one))
                           (real_plus real_one (real_opp real_one)) real_zero
               (RealSetoid.real_eq_plus_compat (real_exp_neg u)
                  (real_opp real_one) real_one (real_opp real_one) Hx1
                  (real_eq_refl (real_opp real_one)))
               (real_plus_opp real_one)). }
    exact (real_lt_irrefl real_zero
             (RealSetoid.real_lt_compat (real_log (real_exp_neg u) Hxe)
                                        real_zero
                                        (real_plus (real_exp_neg u)
                                           (real_opp real_one))
                                        real_zero
                                        Hlog0 Hrhs0 Hlt)).
  - (* 右支 ⟹ 双侧切线排除 ⟹ 弱三分推得 u == 0 *)
    assert (Hequ : real_eq (real_log (real_exp_neg u) Hxe) (real_opp u)).
    { exact (log_inv_exp_neg_thm (real_opp u) Hxe). }
    assert (Hreq : real_eq (real_opp u)
                           (real_plus (real_exp_neg u) (real_opp real_one))).
    { exact (real_eq_trans (real_opp u) (real_log (real_exp_neg u) Hxe)
                           (real_plus (real_exp_neg u) (real_opp real_one))
               (real_eq_sym (real_log (real_exp_neg u) Hxe) (real_opp u) Hequ)
               Heq). }
    assert (Hneg : Not (real_lt u real_zero)).
    { intro Hult.
      assert (Houpos : real_lt real_zero (real_opp u)).
      { exact (RealSetoid.real_lt_id_l real_zero (real_opp real_zero)
                 (real_opp u)
                 (real_eq_sym (real_opp real_zero) real_zero real_opp_zero)
                 (real_opp_lt_compat u real_zero Hult)). }
      assert (Hx1lt : real_lt real_one (real_exp_neg u)).
      { exact (RealSetoid.real_lt_id_l real_one (cauchy_real_exp real_zero)
                 (real_exp_neg u)
                 (real_eq_sym (cauchy_real_exp real_zero) real_one
                    cauchy_real_exp_zero)
                 (cauchy_real_exp_mono real_zero (real_opp u) Houpos)). }
      exact (real_lt_irrefl (real_plus (real_exp_neg u) (real_opp real_one))
               (RealSetoid.real_lt_compat (real_log (real_exp_neg u) Hxe)
                                          (real_plus (real_exp_neg u)
                                             (real_opp real_one))
                                          (real_plus (real_exp_neg u)
                                             (real_opp real_one))
                                          (real_plus (real_exp_neg u)
                                             (real_opp real_one))
                                          Heq
                                          (real_eq_refl (real_plus
                                             (real_exp_neg u)
                                             (real_opp real_one)))
                                          (klst_log_tangent_pos
                                             (real_exp_neg u) Hxe Hx1lt))). }
    assert (Hpos : Not (real_lt real_zero u)).
    { intro Hugt.
      assert (Hxlt1 : real_lt (real_exp_neg u) real_one).
      { exact (RealSetoid.real_lt_id_r (cauchy_real_exp (real_opp u))
                 (cauchy_real_exp real_zero) real_one cauchy_real_exp_zero
                 (cauchy_real_exp_mono (real_opp u) real_zero
                    (real_lt_zero_opp u Hugt))). }
      exact (real_lt_irrefl (real_plus (real_exp_neg u) (real_opp real_one))
               (RealSetoid.real_lt_compat (real_log (real_exp_neg u) Hxe)
                                          (real_plus (real_exp_neg u)
                                             (real_opp real_one))
                                          (real_plus (real_exp_neg u)
                                             (real_opp real_one))
                                          (real_plus (real_exp_neg u)
                                             (real_opp real_one))
                                          Heq
                                          (real_eq_refl (real_plus
                                             (real_exp_neg u)
                                             (real_opp real_one)))
                                          (klst_log_tangent_neg
                                             (real_exp_neg u) Hxe Hxlt1))). }
    apply inr. exact (real_weak_trich u real_zero Hneg Hpos).
Qed.

(* ============================================================ *)
(* 收尾核验：四件逐条（全须 Closed under the global context）             *)
(* ============================================================ *)

Print Assumptions ydll_le_b_not_gt.
Print Assumptions ydll_log_tangent_not_gt.
Print Assumptions ydll_cond_strict_of_ne_one.
Print Assumptions ydll_lpo_barrier.

(* ============================ §5 bool 二元组群载体（枚举/覆盖/规模正性/无重复表/零奖励）逐项供给该节前提组，收束为抽象前提在具体载体上的实例化定理 gqc_supplied 与 ============================ *)
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
Import ListNotations.

Section GQCWorld.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* ===== §1 具体载体世界：二元组群（bool 两点枚举型） ===== *)

Definition gqc_Group : Set := bool.
Definition gqc_enum : list gqc_Group := [true; false].

(* ===== §2 覆盖枚举表前提（group_cover : forall i, InT i grp_enum） ===== *)

Lemma gqc_cover : forall i : gqc_Group, InT i gqc_enum.
Proof.
  intro i. destruct i.
  - exact (InT_here true (false :: nil)).
  - exact (InT_next false true (false :: nil) (InT_here false (@nil bool))).
Qed.

(* ===== §3 grp_eq_dec 可判等前提：bool 载体可判等实例（本件非平凡承载点） ===== *)
(* Id 为 S01 Set 层归纳等词；判别＝构造子冲突的依赖消去（大消去）。     *)
(* Or 为 S01 Set 层别名 Or:=A+B，逐支 @inl/@inr 见证，非经典排除律。    *)

Lemma gqc_true_neq_false : Not (Id true false).
Proof. intro h. inversion h. Qed.

Lemma gqc_false_neq_true : Not (Id false true).
Proof. intro h. inversion h. Qed.

Definition gqc_grp_eq_dec : forall i j : gqc_Group, Or (Id i j) (Not (Id i j)) :=
  fun i j =>
    match i as a return (Or (Id a j) (Not (Id a j))) with
    | true =>
        match j as b return (Or (Id true b) (Not (Id true b))) with
        | true => @inl _ _ id_refl
        | false => @inr _ _ gqc_true_neq_false
        end
    | false =>
        match j as b return (Or (Id false b) (Not (Id false b))) with
        | true => @inr _ _ gqc_false_neq_true
        | false => @inl _ _ id_refl
        end
    end.

(* ===== §4 reward_group 前提：零奖励常值（该前提位置无特殊要求） ===== *)

Definition gqc_reward : gqc_Group -> R := fun _ => zero.

(* ===== §5 规模正性前提（源模块实名 G_pos；规模＝二元组群，|枚举|=2） ===== *)

Lemma gqc_G_pos : lt zero (UpGRPO219.nat_to_R_g (length gqc_enum)).
Proof.
  exact (UpGRPO219.nat_to_R_g_pos (Datatypes.S O)).
Qed.

(* ===== §6 无重复表前提（Hnd_g : nodup_g Group group_enum） ===== *)
(* InT 判别工具：nil 位空匹配＋构造子冲突消解（inversion）。           *)

Lemma gqc_InT_nil_empty : forall b : gqc_Group, InT b nil -> Empty_set.
Proof. intros b Hin. inversion Hin. Qed.

Lemma gqc_notin_tf : InT true (false :: nil) -> Empty_set.
Proof. intro Hin. now inversion Hin. Qed.

Lemma gqc_notin_ft : InT false (true :: nil) -> Empty_set.
Proof. intro Hin. now inversion Hin. Qed.

Definition gqc_Hnd : UpGRPO219.nodup_g gqc_Group gqc_enum :=
  (gqc_notin_tf, (gqc_InT_nil_empty false, tt)).

(* ===== §7 封装证书（前提组封装记录型：仿 S17 keep_dec 实例先例） ===== *)
(* 前提序＝源模块声明序（Group/group_enum/group_cover/grp_eq_dec/          *)
(*   reward_group/G_pos/Hnd_g）；实层轴以抽象参量入包泛量化。            *)

Inductive gqc_pack : Type :=
| gqc_pack_intro :
    forall (Grp : Set) (grp_enum : list Grp)
           (group_cover : forall i : Grp, InT i grp_enum)
           (grp_eq_dec : forall i j : Grp, Or (Id i j) (Not (Id i j)))
           (reward_group : Grp -> R)
           (G_pos : lt zero (UpGRPO219.nat_to_R_g (length grp_enum)))
           (Hnd_g : UpGRPO219.nodup_g Grp grp_enum),
      gqc_pack.

Theorem gqc_supplied : gqc_pack.
Proof.
  exact (gqc_pack_intro gqc_Group gqc_enum gqc_cover gqc_grp_eq_dec
                        gqc_reward gqc_G_pos gqc_Hnd).
Qed.

(* ===== §8 抽象前提在具体载体上的实例化消解（源模块 B2/B3 主定理） ===== *)

Theorem gqc_indicator_sum_one_bool : forall j : gqc_Group,
  InT j gqc_enum ->
  Id (UpGRPO219.list_sum_g gqc_Group (fun i : gqc_Group =>
        match gqc_grp_eq_dec i j with
        | inl _ => one
        | inr _ => zero
        end) gqc_enum) one.
Proof.
  intro j. intro Hin.
  exact (UpGRPO219.grpo_indicator_sum_one gqc_Group gqc_enum gqc_grp_eq_dec
                                          gqc_Hnd j Hin).
Qed.

Theorem gqc_uniform_mass_bool : forall j : gqc_Group,
  InT j gqc_enum ->
  Id (UpGRPO219.list_sum_g gqc_Group (fun i : gqc_Group =>
        mult (inv_pos (UpGRPO219.nat_to_R_g (length gqc_enum)) gqc_G_pos)
             (match gqc_grp_eq_dec i j with
              | inl _ => one
              | inr _ => zero
              end)) gqc_enum)
     (inv_pos (UpGRPO219.nat_to_R_g (length gqc_enum)) gqc_G_pos).
Proof.
  intro j. intro Hin.
  exact (UpGRPO219.grpo_uniform_mass gqc_Group gqc_enum gqc_grp_eq_dec
                                     gqc_G_pos gqc_Hnd j Hin).
Qed.

End GQCWorld.

(* ===== 收尾：公理依赖核验 ===== *)

Print Assumptions gqc_supplied.
Print Assumptions gqc_indicator_sum_one_bool.
Print Assumptions gqc_uniform_mass_bool.

(* ============================ §6 Group := bool、R := nat 极小 Set 层载体的单副本枚举世界上正向实例化构造（判别核/覆盖/求和/计数面自建），与世界装配件各自独 ============================ *)
Inductive Id {A : Set} (x : A) : A -> Set :=
| id_refl : Id x x.

Arguments id_refl {A} {x}.

Definition Or (A B : Set) : Set := A + B.
Definition Not (A : Set) : Set := A -> Empty_set.

Definition id_sym {A : Set} {x y : A} (p : Id x y) : Id y x :=
  match p with
  | id_refl => id_refl
  end.

Definition id_trans {A : Set} {x y z : A} (p : Id x y) (q : Id y z) : Id x z :=
  match p, q with
  | id_refl, id_refl => id_refl
  end.

Definition id_cong {A B : Set} (f : A -> B) {x y : A} (p : Id x y) : Id (f x) (f y) :=
  match p with
  | id_refl => id_refl
  end.

Definition id_cong2 {A B C : Set} (f : A -> B -> C) {x x' : A} {y y' : B}
                    (p : Id x x') (q : Id y y') : Id (f x y) (f x' y') :=
  match p, q with
  | id_refl, id_refl => id_refl
  end.

(* 构造性 list 成员关系（Set 层，S01 同型） *)
Inductive InT {A : Set} (x : A) : list A -> Set :=
| InT_here : forall l, InT x (x :: l)
| InT_next : forall y l, InT x l -> InT x (y :: l).

Arguments InT_here {A} x l.
Arguments InT_next {A} x y l H.

Definition not_InT {A : Set} (x : A) (l : list A) : Set :=
  InT x l -> Empty_set.

(* 成员关系 cons 头尾二分（依赖消去回送形，替代反转策略） *)
Lemma InT_cons_cases : forall (A : Set) (j a : A) (rest : list A),
  InT j (a :: rest) -> Or (Id j a) (InT j rest).
Proof.
  intros A j a rest Hin.
  refine
    (match Hin as Hin0 in (InT _ l0)
           return (match l0 with
                   | nil => unit
                   | cons b rest0 => Or (Id j b) (InT j rest0)
                   end)
     with
     | InT_here _ rest0 => @inl _ _ id_refl
     | InT_next _ b rest0 Hin2 => @inr _ _ Hin2
     end).
Qed.

(* ================= §1 nat 载体 R 侧极小算术（S01 同型名） ================= *)

Definition zero : nat := O.
Definition one : nat := Datatypes.S O.

Fixpoint rplus (a b : nat) : nat :=
  match a with
  | O => b
  | Datatypes.S a' => Datatypes.S (rplus a' b)
  end.

Lemma plus_zero : forall b : nat, Id (rplus b zero) b.
Proof.
  intro b. induction b as [| b IH].
  - apply id_refl.
  - cbn [rplus]. apply (id_cong (fun n : nat => Datatypes.S n)). exact IH.
Qed.

Lemma plus_S_swap : forall a b : nat,
  Id (rplus a (Datatypes.S b)) (Datatypes.S (rplus a b)).
Proof.
  intro a. intro b. induction a as [| a IH].
  - apply id_refl.
  - cbn [rplus]. apply (id_cong (fun n : nat => Datatypes.S n)). exact IH.
Qed.

Lemma plus_comm : forall a b : nat, Id (rplus a b) (rplus b a).
Proof.
  intro a. intro b. induction a as [| a IH].
  - cbn [rplus]. apply (id_sym (plus_zero b)).
  - cbn [rplus]. apply (id_trans (id_cong (fun n : nat => Datatypes.S n) IH)).
    apply (id_sym (plus_S_swap b a)).
Qed.

Lemma plus_assoc : forall a b c : nat,
  Id (rplus a (rplus b c)) (rplus (rplus a b) c).
Proof.
  intros a b c. induction a as [| a IH].
  - apply id_refl.
  - cbn [rplus]. apply (id_cong (fun n : nat => Datatypes.S n)). exact IH.
Qed.

(* Set 层序（自建，禁 sig 形）：ltT a b := leT (S a) b *)
Fixpoint leT (a b : nat) : Set :=
  match a with
  | O => unit
  | Datatypes.S a' =>
      match b with
      | O => Empty_set
      | Datatypes.S b' => leT a' b'
      end
  end.

Definition ltT (a b : nat) : Set := leT (Datatypes.S a) b.

(* nat 到载体的嵌入（S15:1430 同型） *)
Fixpoint nat_to_R_g (k : nat) : nat :=
  match k with
  | O => zero
  | Datatypes.S m => rplus one (nat_to_R_g m)
  end.

Lemma nat_to_R_g_pos : forall k : nat, ltT zero (nat_to_R_g (Datatypes.S k)).
Proof.
  intro k. exact tt.
Qed.

(* ================= §2 bool 二元枚举世界（前提逐项供给） ================= *)

(* 世界承载体：Group := bool *)
(* 前提 grp_eq_dec 的实例化核心：bool 判定到 @inl/@inr 依赖消去 *)
Lemma btt_ne_bff : Not (Id true false).
Proof.
  intro h. exact (match h with end).
Qed.

Lemma bff_ne_btt : Not (Id false true).
Proof.
  intro h. exact (match h with end).
Qed.

Definition bg_grp_eq_dec : forall i j : bool, Or (Id i j) (Not (Id i j)) :=
  fun i j =>
    match i as x return (forall j0 : bool, Or (Id x j0) (Not (Id x j0))) with
    | true =>
        fun j0 =>
          match j0 as y return (Or (Id true y) (Not (Id true y))) with
          | true => @inl (Id true true) (Not (Id true true)) id_refl
          | false => @inr (Id true false) (Not (Id true false)) btt_ne_bff
          end
    | false =>
        fun j0 =>
          match j0 as y return (Or (Id false y) (Not (Id false y))) with
          | true => @inr (Id false true) (Not (Id false true)) bff_ne_btt
          | false => @inl (Id false false) (Not (Id false false)) id_refl
          end
    end j.

(* 伴生前提照 S15:1408-1419 实形逐项供给 *)
Definition bg_enum : list bool := true :: false :: nil.

Definition bg_cover : forall i : bool, InT i bg_enum :=
  fun i =>
    match i as x return (InT x (true :: false :: nil)) with
    | true => InT_here true (false :: nil)
    | false => InT_next false true (false :: nil) (InT_here false nil)
    end.

(* 数据位（直接给出，照 S17 常零函数先例）：reward_group := 常零 *)
Definition bg_reward : bool -> nat := fun _ : bool => zero.

(* 组大小正性伴生（G := nat_to_R_g (length enum)，G_pos 前提） *)
Definition bg_G : nat := nat_to_R_g (length bg_enum).
Definition bg_G_pos : ltT zero bg_G := tt.

(* Set 层无重复谓词（S15:1662 同型，载体泛型） *)
Fixpoint nodup_g {A : Set} (l : list A) : Set :=
  match l with
  | nil => unit
  | cons x t => prod (not_InT x t) (nodup_g t)
  end.

Definition bg_nodup_enum : nodup_g bg_enum :=
  @pair (not_InT true (false :: nil)) (nodup_g (false :: nil))
    (fun Hin : InT true (false :: nil) =>
       match Hin with
       | InT_next _ false nil Hin2 => match Hin2 with end
       end)
    (@pair (not_InT false nil) unit
       (fun Hin : InT false nil => match Hin with end) tt).

(* ================= §3 GRPO 枚举节计数器（grp_eq_dec 实例驱动） ================= *)

(* 组求和（列表 fold，载体 Id 层；S15:1448 同型，载体泛型） *)
Fixpoint list_sum_g {A : Set} (f : A -> nat) (l : list A) : nat :=
  match l with
  | nil => zero
  | cons i rest => rplus (f i) (list_sum_g f rest)
  end.

Lemma list_sum_g_zero_fn : forall (A : Set) (f : A -> nat) (l : list A),
  (forall i : A, InT i l -> Id (f i) zero) ->
  Id (list_sum_g f l) zero.
Proof.
  intros A f l H. induction l as [| x rest IH].
  - apply id_refl.
  - apply (id_trans (id_cong2 rplus (H x (InT_here x rest))
                                (id_refl : Id (list_sum_g f rest) (list_sum_g f rest)))).
    apply (id_trans (plus_comm zero (list_sum_g f rest))).
    apply (id_trans (plus_zero (list_sum_g f rest))).
    exact (IH (fun i : A => fun Hin : InT i rest => H i (InT_next i x rest Hin))).
Qed.

(* 计数器（实例 bg_grp_eq_dec 驱动；S15:1462 同型） *)
Fixpoint count_g (j : bool) (l : list bool) : nat :=
  match l with
  | nil => O
  | cons x rest =>
      match bg_grp_eq_dec x j with
      | inl _ => Datatypes.S (count_g j rest)
      | inr _ => count_g j rest
      end
  end.

Fixpoint removeT_g (j : bool) (l : list bool) : list bool :=
  match l with
  | nil => nil
  | cons x rest =>
      match bg_grp_eq_dec x j with
      | inl _ => removeT_g j rest
      | inr _ => x :: removeT_g j rest
      end
  end.

Lemma InT_transport : forall (x y : bool) (l : list bool),
  Id x y -> InT x l -> InT y l.
Proof.
  intros x y l H Hin. destruct H. exact Hin.
Qed.

Lemma not_InT_count_zero : forall (j : bool) (l : list bool),
  not_InT j l -> @Id nat (count_g j l) O.
Proof.
  intros j l. induction l as [| x rest IH]; intro Hn.
  - apply id_refl.
  - cbn [count_g]. destruct (bg_grp_eq_dec x j) as [Hxj | Hnxj].
    + exact (match Hn (InT_transport x j (x :: rest) Hxj (InT_here x rest)) with end).
    + exact (IH (fun Hin : InT j rest => Hn (InT_next j x rest Hin))).
Qed.

(* 头元素 ≠ j ⟹ 成员关系在尾部（S15:1654 同型，经 InT_cons_cases） *)
Lemma InT_tail_of_neq : forall (j a : bool) (rest : list bool),
  Not (Id a j) -> InT j (a :: rest) -> InT j rest.
Proof.
  intros j a rest Hne Hin.
  destruct (InT_cons_cases bool j a rest Hin) as [Hja | Hrest].
  - exact (match Hne (id_sym Hja) with end).
  - exact Hrest.
Qed.

Lemma count_zero_remove_id : forall (j : bool) (l : list bool),
  @Id nat (count_g j l) O -> @Id (list bool) (removeT_g j l) l.
Proof.
  intros j l. induction l as [| x rest IH]; intro Hc.
  - apply id_refl.
  - cbn [count_g] in Hc. cbn [removeT_g].
    destruct (bg_grp_eq_dec x j) as [Hxj | Hnxj].
    + inversion Hc.
    + apply (id_cong (fun l0 : list bool => cons x l0)). exact (IH Hc).
Qed.

Lemma remove_notin_aux : forall (j x : bool) (l : list bool),
  InT x (removeT_g j l) -> Not (Id x j).
Proof.
  intros j x l. induction l as [| y rest IH]; intro Hin.
  - exact (match Hin with end).
  - cbn [removeT_g] in Hin.
    destruct (bg_grp_eq_dec y j) as [Hyj | Hnyj].
    + exact (IH Hin).
    + destruct (InT_cons_cases bool x y (removeT_g j rest) Hin) as [Hxy | Hrest].
      * exact (fun hxj : Id x j => Hnyj (id_trans (id_sym Hxy) hxj)).
      * exact (IH Hrest).
Qed.

(* 恰计一次的拆分：count == 1 ⟹ Σ l f == f j + Σ (removeT_g j l) f *)
Lemma split_count_one_id : forall (f : bool -> nat) (j : bool) (l : list bool),
  @Id nat (count_g j l) (Datatypes.S O) ->
  Id (list_sum_g f l) (rplus (f j) (list_sum_g f (removeT_g j l))).
Proof.
  intros f j l. induction l as [| x rest IH]; intro Hc.
  - inversion Hc.
  - cbn [count_g] in Hc. cbn [removeT_g].
    destruct (bg_grp_eq_dec x j) as [Hxj | Hnxj].
    + assert (Hc0 : @Id nat (count_g j rest) O).
      { exact (id_cong Nat.pred Hc). }
      assert (Hrid : @Id (list bool) (removeT_g j rest) rest)
        by exact (count_zero_remove_id j rest Hc0).
      apply (id_trans (id_cong2 rplus (id_cong f Hxj)
                                     (id_refl : Id (list_sum_g f rest)
                                                   (list_sum_g f rest)))).
      apply (id_cong2 rplus (id_refl : Id (f j) (f j))
                           (id_cong (fun l0 : list bool => list_sum_g f l0)
                                    (id_sym Hrid))).
    + apply (id_trans (id_cong2 rplus (id_refl : Id (f x) (f x)) (IH Hc))).
      apply (id_trans (plus_assoc (f x) (f j) (list_sum_g f (removeT_g j rest)))).
      apply (id_trans (id_cong2 rplus (plus_comm (f x) (f j))
                                     (id_refl : Id (list_sum_g f (removeT_g j rest))
                                                   (list_sum_g f (removeT_g j rest))))).
      apply (id_sym (plus_assoc (f j) (f x) (list_sum_g f (removeT_g j rest)))).
Qed.

(* 恰计一次（B1，S15:1672 同型）：覆盖 + 无重复 ⟹ 每元素恰计一次 *)
Theorem grpo_count_one : forall (l : list bool) (Hnd : nodup_g l)
    (j : bool), InT j l -> @Id nat (count_g j l) (Datatypes.S O).
Proof.
  intros l Hnd. induction l as [| a rest IH]; intros j Hin.
  - exact (match Hin with end).
  - destruct Hnd as [Hnhead Hndrest].
    cbn [count_g]. destruct (bg_grp_eq_dec a j) as [Haj | Hanj].
    + apply (id_cong (fun n : nat => Datatypes.S n)).
      apply (not_InT_count_zero j rest
               (fun Hin : InT j rest =>
                  Hnhead (InT_transport j a rest (id_sym Haj) Hin))).
    + exact (IH Hndrest j (InT_tail_of_neq j a rest Hanj Hin)).
Qed.

(* ================= §4 主件——可判等前提的具体载体实例化通路证书 ================= *)

(* 照 S17 keep_dec 实例证书体例：前提语句逐字入证 + 实例供给 + 使用位实例化。 *)

(* ① 前提语句逐字（S15:1419 形，载体 bool）：Set 层语句 *)
Definition gqd_slot_statement : Set :=
  forall i j : bool, Or (Id i j) (Not (Id i j)).

(* ② 实例（bool 判定到 @inl/@inr 依赖消去，见 §2）：
      gqd_slot_statement 的供给项 = bg_grp_eq_dec *)

(* ③ 主件证书：可判等前提的具体载体实例化通路
      S15:1419 前提经 bg_grp_eq_dec 实例化 ⟹ GRPO 枚举节 B1（每元素恰计一次）
      在世界枚举 bg_enum 上成立。 *)
Theorem gqd_discharge_certificate :
  forall (j : bool), InT j bg_enum ->
    @Id nat (count_g j bg_enum) (Datatypes.S O).
Proof.
  exact (fun j Hin => grpo_count_one bg_enum bg_nodup_enum j Hin).
Qed.

(* ④ 使用位实例化示范：GRPO 枚举节 B2 indicator 求和恒等式（S15:1690 同型）
      —— Σ_{i∈enum} indicator(i) == 1，indicator 由实例 bg_grp_eq_dec 逐位分派。 *)
Theorem gqd_grpo_indicator_sum_one : forall (j : bool),
  InT j bg_enum ->
  Id (list_sum_g (fun i : bool => match bg_grp_eq_dec i j with
                                  | inl _ => one
                                  | inr _ => zero
                                  end) bg_enum) one.
Proof.
  intros j Hin.
  assert (Hc1 : @Id nat (count_g j bg_enum) (Datatypes.S O))
    by exact (grpo_count_one bg_enum bg_nodup_enum j Hin).
  assert (Hsplit := split_count_one_id
                      (fun i : bool => match bg_grp_eq_dec i j with
                                       | inl _ => one
                                       | inr _ => zero
                                       end) j bg_enum Hc1).
  assert (Hfj : Id (match bg_grp_eq_dec j j with
                    | inl _ => one
                    | inr _ => zero
                    end) one).
  { destruct (bg_grp_eq_dec j j) as [Hjj | Hjj].
    - apply id_refl.
    - exact (match Hjj (id_refl : Id j j) with end). }
  assert (Hrest : Id (list_sum_g (fun i : bool => match bg_grp_eq_dec i j with
                                                  | inl _ => one
                                                  | inr _ => zero
                                                  end)
                             (removeT_g j bg_enum)) zero).
  { apply list_sum_g_zero_fn.
    intro i. intro HinR.
    assert (Hne : Not (Id i j)) by exact (remove_notin_aux j i bg_enum HinR).
    destruct (bg_grp_eq_dec i j) as [Hxj | Hnxj].
    - exact (match Hne Hxj with end).
    - apply id_refl. }
  apply (id_trans Hsplit).
  apply (id_trans (id_cong2 rplus Hfj Hrest)).
  apply (plus_zero one).
Qed.

(* ⑤ 提取面对照：判定核（bg_grp_eq_dec 的计算内容投影，纯 bool 构造）
      与核↔前提实例化正确性证书（提取面 Obj.magic=0 的依据）。 *)
Definition bg_dec_core (i j : bool) : bool :=
  match i with
  | true =>
      match j with
      | true => true
      | false => false
      end
  | false =>
      match j with
      | true => false
      | false => true
      end
  end.

Lemma bg_grp_eq_dec_core_correct : forall i j : bool,
  match bg_grp_eq_dec i j with
  | inl _ => Id (bg_dec_core i j) true
  | inr _ => Id (bg_dec_core i j) false
  end.
Proof.
  intros i j.
  (* 分情形：bool 载体四支判定——inl 支判定核 bg_dec_core 归约为 true，inr 支归约为
     false，逐支以 Id 自反见证 @id_refl 连显式右端项收束。 *)
  destruct i; destruct j; cbn [bg_grp_eq_dec bg_dec_core].
  - exact (@id_refl _ true).
  - exact (@id_refl _ false).
  - exact (@id_refl _ false).
  - exact (@id_refl _ true).
Qed.

(* 该位公理依赖核验（应全为 Closed） *)
Print Assumptions bg_grp_eq_dec.
Print Assumptions grpo_count_one.
Print Assumptions gqd_discharge_certificate.
Print Assumptions gqd_grpo_indicator_sum_one.
Print Assumptions bg_grp_eq_dec_core_correct.

(* 提取面：判定核可执行性（Separate Extraction 单命令；
   提取闭包=纯 bool 构造，Obj.magic=0 核验。实例 bg_grp_eq_dec 全式与
   计数器属 Set 层证书面：其 Not 支反证消去为证明内容，提取必擦除为
   Obj.magic，故不参与本提取件。） *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_y6_grpdis_ex".
Separate Extraction bg_dec_core.

(* ============================ §7 两点核差形的接口级抽象前置引理 ============================ *)
From Stdlib Require Import QArith.Qring.
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

(* ============================================================ *)
(* 接口 Context：RealInterfaceEnhanced（abs 族字段可用系）               *)
(* ============================================================ *)

Section TwoPtAbsInterface.

Context {RI : RealInterfaceEnhanced}.

Local Existing Instance RI_base.

Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.

(* ---------------------------------------------------------- *)
(* M1 · 正余量右吸收（接口级）                                      *)
(*   le a b ＋ 0 < c ⟹ le a (b+c)。                                  *)
(*   构造（接口 le 无 Or 解开字段，Or 分拆路线不可迁移——              *)
(*   纯 le 通道构造）：a ≤ a+0 ≤ a+c（0 < c 经 lt_le_iff inl 注入      *)
(*   升 le，le_plus_compat 承载）≤ b+c（le_plus_compat），le_trans 收束。 *)
(* ---------------------------------------------------------- *)

Lemma uap_le_add_r : forall a b c : R,
  le a b -> lt zero c -> le a (plus b c).
Proof.
  intros a b c Hab Hc.
  apply (le_trans a (plus a c) (plus b c)).
  - apply (le_id_l a (plus a zero) (plus a c)).
    + exact (id_sym (plus_zero a)).
    + apply (le_plus_compat a a zero c).
      * apply le_refl.
      * apply (lt_le_iff zero c). apply inl. exact Hc.
  - apply (le_plus_compat a b c c).
    + exact Hab.
    + apply le_refl.
Qed.

(* ---------------------------------------------------------- *)
(* M2 · 差恒等链（uap_diff_stitch）：(a−b)+(b−c) ≡ a−c              *)
(*   构造（五步恒等链路线的接口级复现，全部 id_trans/id_cong 逐项）：      *)
(*   ① plus_assoc (a−b) b (b−c) 反向展开；                            *)
(*   ② id_cong（plus a）收拢到内层 opp b+(b+(opp c))；                 *)
(*   ③ plus_assoc (opp b) b (opp c) 反向展开；                        *)
(*   ④ id_cong2 plus：opp b+b ≡ 0（plus_comm＋plus_opp）逐项运输；     *)
(*   ⑤ 0+(opp c) ≡ opp c（plus_comm＋plus_zero）。                    *)
(* ---------------------------------------------------------- *)

Lemma uap_diff_stitch : forall a b c : R,
  Id (plus (plus a (opp b)) (plus b (opp c))) (plus a (opp c)).
Proof.
  intros a b c.
  apply (id_trans (id_sym (plus_assoc a (opp b) (plus b (opp c))))).
  apply (id_cong (fun t : R => plus a t)).
  apply (id_trans (plus_assoc (opp b) b (opp c))).
  apply (id_trans (id_cong2 plus
           (id_trans (plus_comm (opp b) b) (plus_opp b)) (id_refl))).
  apply (id_trans (plus_comm zero (opp c))).
  apply (plus_zero (opp c)).
Qed.

(* ---------------------------------------------------------- *)
(* M3 · 主件：两点核差形逐 eps 形（接口级供给）                        *)
(*   |a−c| ≤ (|a−b|+|b−c|)+eps（0 < eps）。                            *)
(*   构造：应用接口 abs_triangle 字段（real_abs_triangle 两点核        *)
(*   的抽象化）于实例 (a−b, b−c)，id_cong abs 把两点核左端           *)
(*   经 M2 恒等链接到 |a−c|，右端经 M1 正余量右吸收承担 eps。        *)
(* ---------------------------------------------------------- *)

Theorem uap_abs_diff_triangle_le_eps :
  forall a b c eps : R,
    lt zero eps ->
    le (abs (plus a (opp c)))
       (plus (plus (abs (plus a (opp b))) (abs (plus b (opp c)))) eps).
Proof.
  intros a b c eps Heps.
  apply (le_id_l (abs (plus a (opp c)))
                 (abs (plus (plus a (opp b)) (plus b (opp c))))).
  - exact (id_sym (id_cong abs (uap_diff_stitch a b c))).
  - apply (uap_le_add_r
             (abs (plus (plus a (opp b)) (plus b (opp c))))
             (plus (abs (plus a (opp b))) (abs (plus b (opp c)))) eps).
    + exact (abs_triangle (plus a (opp b)) (plus b (opp c))).
    + exact Heps.
Qed.

(* ---------------------------------------------------------- *)
(* M4 · 接口级 Bishop 形（plain-eps 逐 eps 语义，显式 Set 值）          *)
(*   uap_le_b x y := ∀eps>0, x ≤ y+eps（对应 real_le_closure_b_one     *)
(*   前提位；接口 le 无 Or 解开字段，strict 完成形接口级不可达，        *)
(*   本语义为可达最强形的诚实对应物——显式说明）。                      *)
(* ---------------------------------------------------------- *)

Definition uap_le_b (x y : R) : Set :=
  forall eps : R, lt zero eps -> le x (plus y eps).

Theorem uap_abs_diff_triangle_le_B :
  forall a b c : R,
    uap_le_b (abs (plus a (opp c)))
             (plus (abs (plus a (opp b))) (abs (plus b (opp c)))).
Proof.
  intros a b c eps Heps.
  exact (uap_abs_diff_triangle_le_eps a b c eps Heps).
Qed.

End TwoPtAbsInterface.

(* ============================================================ *)
(* 审计注记：Print Assumptions 预期全 Closed（零外部未证假设）           *)
(* ============================================================ *)

Print Assumptions uap_le_add_r.
Print Assumptions uap_diff_stitch.
Print Assumptions uap_abs_diff_triangle_le_eps.
Print Assumptions uap_abs_diff_triangle_le_B.

(* ============================ §8 九项接口参数取单点具体值、三条节级前提（归一化/能量钉/KL 归零）实算成立，源模块出节五定理（熵单峰分裂）全参应用为具体实例 uab1_dischar ============================ *)
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
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqEntropyMonoSplit.

(* ============ §1 · 实例供给：九项接口/数据参数的具体值 ============ *)

Definition uab1_sum : (unit -> Real) -> Real :=
  fun f : unit -> Real => f tt.

Definition uab1_sumpos
  : forall f : unit -> Real,
      (forall s : unit, real_lt real_zero (f s)) ->
      real_lt real_zero (uab1_sum f) :=
  fun (f : unit -> Real)
      (Hf : forall s : unit, real_lt real_zero (f s)) => Hf tt.

Definition uab1_ext : forall f g : unit -> Real,
    (forall s : unit, real_eq (f s) (g s)) ->
    real_eq (uab1_sum f) (uab1_sum g) :=
  fun (f g : unit -> Real)
      (H : forall s : unit, real_eq (f s) (g s)) => H tt.

Definition uab1_le : forall f g : unit -> Real,
    (forall s : unit, real_le (f s) (g s)) ->
    real_le (uab1_sum f) (uab1_sum g) :=
  fun (f g : unit -> Real)
      (H : forall s : unit, real_le (f s) (g s)) => H tt.

Definition uab1_linear : forall (a : Real) (f : unit -> Real),
    real_eq (uab1_sum (fun s : unit => real_mult a (f s)))
            (real_mult a (uab1_sum f)) :=
  fun (a : Real) (f : unit -> Real) => real_eq_refl (real_mult a (f tt)).

Definition uab1_add : forall f g : unit -> Real,
    real_eq (uab1_sum (fun s : unit => real_plus (f s) (g s)))
            (real_plus (uab1_sum f) (uab1_sum g)) :=
  fun (f g : unit -> Real) => real_eq_refl (real_plus (f tt) (g tt)).

Definition uab1_T_star : Real := real_one.
Definition uab1_T_star_pos : real_lt real_zero uab1_T_star := real_lt_zero_one.
Definition uab1_energy : unit -> Real := fun _ : unit => real_one.

(* ============ §2 · 源模块速记件的显式参形（与源模块 Let 速记同体展开） ============ *)

Definition uab1_bd (u : Real) (Hu : real_lt real_zero u) : unit -> Real :=
  real_boltzmann_dist_temp unit uab1_sum uab1_sumpos u Hu uab1_energy.

Definition uab1_bd_pos (u : Real) (Hu : real_lt real_zero u)
  : forall s : unit, real_lt real_zero (uab1_bd u Hu s) :=
  real_boltzmann_dist_temp_pos unit uab1_sum uab1_sumpos u Hu uab1_energy.

Definition uab1_ent (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_entropy_dist unit uab1_sum (uab1_bd u Hu) (uab1_bd_pos u Hu).

(* KL 方向注记：uab1_kl u = KL(p_u ‖ p_{t*})——p_u 居第一分布位， *)
(* p_{t*} 居参考位；uab1_T_star 全参取 real_one。 *)
Definition uab1_kl (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_KL_temp unit uab1_sum uab1_sumpos uab1_T_star uab1_T_star_pos uab1_energy
               (uab1_bd u Hu) (uab1_bd_pos u Hu).

(* ============ §3 · 工具引理（单位元/零元的左恒等，环律两行自证） ============ *)

Lemma uab1_mult_one_l : forall x : Real,
  real_eq (real_mult real_one x) x.
Proof.
  intro x. exact (real_eq_trans _ _ _ (real_mult_comm real_one x) (real_mult_one x)).
Qed.

Lemma uab1_plus_zero_l : forall x : Real,
  real_eq (real_plus real_zero x) x.
Proof.
  intro x. exact (real_eq_trans _ _ _ (real_plus_comm real_zero x) (real_plus_zero x)).
Qed.

(* ============ §4 · 链 A：Gibbs 族归一化（uab1_bt_pt_one） ============ *)
(* 单点载体温 t 处 p_t(tt) == 1：配分函数 Z_t 定义性收敛到能量因子自身，    *)
(* 乘积经 real_mult_comm 换序后由 real_inv_pos_correct 一步归一。           *)

Lemma uab1_bt_pt_one : forall (t : Real) (Ht : real_lt real_zero t),
  real_eq (uab1_bd t Ht tt) real_one.
Proof.
  intros t Ht.
  pose proof
    (real_inv_pos_correct
       (real_Z_temp unit uab1_sum t Ht uab1_energy)
       (real_Z_temp_pos unit uab1_sum uab1_sumpos
          t Ht uab1_energy)) as Hinv.
  assert (Hswap : real_eq (uab1_bd t Ht tt)
                    (real_mult
                       (real_boltzmann_factor_temp unit t Ht uab1_energy tt)
                       (real_inv_pos
                          (real_Z_temp unit uab1_sum t Ht uab1_energy)
                          (real_Z_temp_pos unit uab1_sum uab1_sumpos
                             t Ht uab1_energy)))).
  { exact (real_mult_comm
             (real_inv_pos
                (real_Z_temp unit uab1_sum t Ht uab1_energy)
                (real_Z_temp_pos unit uab1_sum uab1_sumpos
                   t Ht uab1_energy))
             (real_boltzmann_factor_temp unit t Ht uab1_energy tt)). }
  exact (real_eq_trans (uab1_bd t Ht tt)
           (real_mult
              (real_boltzmann_factor_temp unit t Ht uab1_energy tt)
              (real_inv_pos
                 (real_Z_temp unit uab1_sum t Ht uab1_energy)
                 (real_Z_temp_pos unit uab1_sum uab1_sumpos
                    t Ht uab1_energy)))
           real_one Hswap Hinv).
Qed.

(* ============ §5 · 链 B：能量钉前提（uab1_Hpinned） ============ *)
(* 语句形＝源模块节级前提 Hpinned 的全参具体化：                              *)
(*   sum (fun s => p_u(s)·e(s)) == E(p_{t*})。                              *)
(* 实算：两侧各自经 real_mult_one 归到 p(·)(tt)，再由链 A 在温 u 与          *)
(* 温 T_star=1 两实例下各归一为 1。                                         *)
(* 能量取任意非零函数即成立（本件取常值 1）——归一化谱系全链给出。          *)

Lemma uab1_Hpinned :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (uab1_sum
         (fun s : unit =>
            real_mult (uab1_bd u Hu s) (uab1_energy s)))
      (real_energy_exp_temp unit uab1_sum uab1_sumpos
         uab1_T_star uab1_T_star_pos uab1_energy).
Proof.
  intros u Hu.
  apply (real_eq_trans
           (uab1_sum
              (fun s : unit =>
                 real_mult (uab1_bd u Hu s) (uab1_energy s)))
           (uab1_bd u Hu tt)
           (real_energy_exp_temp unit uab1_sum uab1_sumpos
              uab1_T_star uab1_T_star_pos uab1_energy)).
  - exact (real_mult_one (uab1_bd u Hu tt)).
  - exact (real_eq_trans
             (uab1_bd u Hu tt)
             real_one
             (real_energy_exp_temp unit uab1_sum uab1_sumpos
                uab1_T_star uab1_T_star_pos uab1_energy)
             (uab1_bt_pt_one u Hu)
             (real_eq_sym
                (real_energy_exp_temp unit uab1_sum uab1_sumpos
                   uab1_T_star uab1_T_star_pos uab1_energy)
                real_one
                (real_eq_trans
                   (real_energy_exp_temp unit uab1_sum uab1_sumpos
                      uab1_T_star uab1_T_star_pos uab1_energy)
                   (uab1_bd uab1_T_star uab1_T_star_pos tt)
                   real_one
                   (real_mult_one (uab1_bd uab1_T_star uab1_T_star_pos tt))
                   (uab1_bt_pt_one uab1_T_star uab1_T_star_pos)))).
Qed.

(* ============ §6 · 链 C：KL 归零（uab1_kl_zero） ============ *)
(* KL(p_u‖p_{t*}) ≡ Σ p_u·(log p_u − log p_{t*}) 单点求和收敛为             *)
(* p_u(tt)·(log p_u(tt) − log p_{t*}(tt))；两对数经链 A、real_log_wd 与     *)
(* real_log_one 各归零，再经加/乘兼容引理收拢为零。                         *)

Lemma uab1_kl_zero : forall (u : Real) (Hu : real_lt real_zero u),
  real_eq (uab1_kl u Hu) real_zero.
Proof.
  intros u Hu.
  assert (Hlu : real_eq
             (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
             real_zero).
  { exact (real_eq_trans
             (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
             (real_log real_one real_lt_zero_one)
             real_zero
             (real_log_wd
                (uab1_bd u Hu tt) real_one
                (uab1_bd_pos u Hu tt) real_lt_zero_one
                (uab1_bt_pt_one u Hu))
             (real_log_one real_lt_zero_one)). }
  assert (Hl1 : real_eq
             (real_log (uab1_bd uab1_T_star uab1_T_star_pos tt)
                       (uab1_bd_pos uab1_T_star uab1_T_star_pos tt))
             real_zero).
  { exact (real_eq_trans
             (real_log (uab1_bd uab1_T_star uab1_T_star_pos tt)
                       (uab1_bd_pos uab1_T_star uab1_T_star_pos tt))
             (real_log real_one real_lt_zero_one)
             real_zero
             (real_log_wd
                (uab1_bd uab1_T_star uab1_T_star_pos tt) real_one
                (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)
                real_lt_zero_one
                (uab1_bt_pt_one uab1_T_star uab1_T_star_pos))
             (real_log_one real_lt_zero_one)). }
  apply (real_eq_trans
           (uab1_kl u Hu)
           (real_mult
              (uab1_bd u Hu tt)
              (real_plus
                 (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                 (real_opp
                    (real_log
                       (uab1_bd uab1_T_star uab1_T_star_pos tt)
                       (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)))))
           real_zero).
  - exact (real_eq_refl
             (real_mult
                (uab1_bd u Hu tt)
                (real_plus
                   (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                   (real_opp
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)))))).
  - exact (real_eq_trans
             (real_mult
                (uab1_bd u Hu tt)
                (real_plus
                   (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                   (real_opp
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)))))
             (real_mult real_one (real_plus real_zero (real_opp real_zero)))
             real_zero
             (RealSetoid.real_eq_mult_compat_adapt
                (uab1_bd u Hu tt) real_one
                (real_plus
                   (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                   (real_opp
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt))))
                (real_plus real_zero (real_opp real_zero))
                (uab1_bt_pt_one u Hu)
                (RealSetoid.real_eq_plus_compat_adapt
                   (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                   real_zero
                   (real_opp
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)))
                   (real_opp real_zero)
                   Hlu
                   (RealSetoid.real_eq_opp_compat
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt))
                      real_zero
                      Hl1)))
             (real_eq_trans
                (real_mult real_one (real_plus real_zero (real_opp real_zero)))
                (real_mult real_one real_zero)
                real_zero
                (RealSetoid.real_eq_mult_compat_adapt
                   real_one real_one
                   (real_plus real_zero (real_opp real_zero))
                   real_zero
                   (real_eq_refl real_one)
                   (real_plus_opp real_zero))
                (uab1_mult_one_l real_zero))).
Qed.

(* ============ §7 · KL 增长前提（uab1_Hkl_right，eps 松弛形） ============ *)
(* 语句形＝源模块节级前提 Hkl_right 的全参具体化（uab1_T_star 取 real_one）。   *)
(* 实算：KL(v)==KL(u)==0（链 C）⟹(KL_v−KL_u)+eps==eps，再经 0<eps 序迁移。   *)

Lemma uab1_Hkl_right :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le uab1_T_star u -> real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
           eps).
Proof.
  intros u v Hu Hv _ _ eps Heps.
  pose proof (uab1_kl_zero v Hv) as Hv0.
  pose proof (uab1_kl_zero u Hu) as Hu0.
  assert (Hdiff : real_eq
                    (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                    real_zero).
  { exact (RealSetoid.real_eq_plus_compat_adapt
             (uab1_kl v Hv) real_zero
             (real_opp (uab1_kl u Hu)) (real_opp real_zero)
             Hv0
             (RealSetoid.real_eq_opp_compat (uab1_kl u Hu) real_zero Hu0)). }
  assert (Hsum : real_eq
                   (real_plus
                      (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                      eps)
                   eps).
  { exact (real_eq_trans
             (real_plus
                (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                eps)
             (real_plus real_zero eps)
             eps
             (RealSetoid.real_eq_plus_compat_adapt
                (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                real_zero
                eps eps
                Hdiff
                (real_eq_refl eps))
             (uab1_plus_zero_l eps)). }
  exact (inl
           (RealSetoid.real_lt_compat
              real_zero real_zero
              eps
              (real_plus
                 (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                 eps)
              (real_eq_refl real_zero)
              (real_eq_sym
                 (real_plus
                    (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                    eps)
                 eps
                 Hsum)
              Heps)).
Qed.

(* ============ §8 · KL 衰减前提（uab1_Hkl_left，与增长前提对偶） ============ *)

Lemma uab1_Hkl_left :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v -> real_le v uab1_T_star ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
           eps).
Proof.
  intros u v Hu Hv _ _ eps Heps.
  pose proof (uab1_kl_zero u Hu) as Hu0.
  pose proof (uab1_kl_zero v Hv) as Hv0.
  assert (Hdiff : real_eq
                    (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                    real_zero).
  { exact (RealSetoid.real_eq_plus_compat_adapt
             (uab1_kl u Hu) real_zero
             (real_opp (uab1_kl v Hv)) (real_opp real_zero)
             Hu0
             (RealSetoid.real_eq_opp_compat (uab1_kl v Hv) real_zero Hv0)). }
  assert (Hsum : real_eq
                   (real_plus
                      (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                      eps)
                   eps).
  { exact (real_eq_trans
             (real_plus
                (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                eps)
             (real_plus real_zero eps)
             eps
             (RealSetoid.real_eq_plus_compat_adapt
                (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                real_zero
                eps eps
                Hdiff
                (real_eq_refl eps))
             (uab1_plus_zero_l eps)). }
  exact (inl
           (RealSetoid.real_lt_compat
              real_zero real_zero
              eps
              (real_plus
                 (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                 eps)
              (real_eq_refl real_zero)
              (real_eq_sym
                 (real_plus
                    (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                    eps)
                 eps
                 Hsum)
              Heps)).
Qed.

(* ============ §9 · 源模块出节五定理的全参落实（具体无假设实例） ============ *)

(* uab1_discharge_pinned_kl_entropy_eq（约束片熵亏恒等式）：KL + S == S_star。 *)
Theorem uab1_discharge_pinned_kl_entropy_eq :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq (real_plus (uab1_kl u Hu) (uab1_ent u Hu))
            (uab1_ent uab1_T_star uab1_T_star_pos).
Proof.
  intros u Hu.
  exact (ems_pinned_kl_entropy_eq
           unit uab1_sum uab1_sumpos
           uab1_ext uab1_linear uab1_add
           uab1_T_star uab1_T_star_pos uab1_energy
           uab1_Hpinned u Hu).
Qed.

(* uab1_discharge_antitone_above（降支）：t* ≤ u ≤ v ⟹ S(p_v) ≤ S(p_u) + eps。 *)
Theorem uab1_discharge_antitone_above :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le uab1_T_star u -> real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (uab1_ent v Hv) (real_plus (uab1_ent u Hu) eps).
Proof.
  intros u v Hu Hv Htu Huv eps Heps.
  exact (snd
           (ems_entropy_split_at_peak
              unit uab1_sum uab1_sumpos
              uab1_ext uab1_linear uab1_add
              uab1_T_star uab1_T_star_pos uab1_energy
              uab1_Hpinned uab1_Hkl_right uab1_Hkl_left)
           u v Hu Hv Htu Huv eps Heps).
Qed.

(* uab1_discharge_mono_below（升支）：u ≤ v ≤ t* ⟹ S(p_u) ≤ S(p_v) + eps。 *)
Theorem uab1_discharge_mono_below :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v -> real_le v uab1_T_star ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (uab1_ent u Hu) (real_plus (uab1_ent v Hv) eps).
Proof.
  intros u v Hu Hv Huv Hvt eps Heps.
  exact (fst
           (ems_entropy_split_at_peak
              unit uab1_sum uab1_sumpos
              uab1_ext uab1_linear uab1_add
              uab1_T_star uab1_T_star_pos uab1_energy
              uab1_Hpinned uab1_Hkl_right uab1_Hkl_left)
           u v Hu Hv Huv Hvt eps Heps).
Qed.

(* uab1_discharge_peak_bound（峰界；源模块出节形另含 le 接口参数）：          *)
(* 一切正温的熵 ≤ 峰熵 + eps。 *)
Theorem uab1_discharge_peak_bound :
  forall (u : Real) (Hu : real_lt real_zero u),
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (uab1_ent u Hu)
              (real_plus (uab1_ent uab1_T_star uab1_T_star_pos) eps).
Proof.
  intros u Hu eps Heps.
  exact (ems_entropy_peak_bound_above
           unit uab1_sum uab1_sumpos
           uab1_ext uab1_le uab1_linear uab1_add
           uab1_T_star uab1_T_star_pos uab1_energy
           uab1_Hpinned
           u Hu eps Heps).
Qed.

(* uab1_discharge_split（分裂主件）：升支与降支两全称语句的乘积合取形。 *)
Theorem uab1_discharge_split :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le u v -> real_le v uab1_T_star ->
     forall eps : Real,
       real_lt real_zero eps ->
       real_le (uab1_ent u Hu) (real_plus (uab1_ent v Hv) eps)) *
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le uab1_T_star u -> real_le u v ->
     forall eps : Real,
       real_lt real_zero eps ->
       real_le (uab1_ent v Hv) (real_plus (uab1_ent u Hu) eps)).
Proof.
  split.
  - exact uab1_discharge_mono_below.
  - exact uab1_discharge_antitone_above.
Qed.

(* ============ §10 · 假设审计（Print Assumptions 全 Closed 为判据） ============ *)
Print Assumptions uab1_bt_pt_one.
Print Assumptions uab1_Hpinned.
Print Assumptions uab1_kl_zero.
Print Assumptions uab1_Hkl_right.
Print Assumptions uab1_Hkl_left.
Print Assumptions uab1_discharge_pinned_kl_entropy_eq.
Print Assumptions uab1_discharge_antitone_above.
Print Assumptions uab1_discharge_mono_below.
Print Assumptions uab1_discharge_peak_bound.
Print Assumptions uab1_discharge_split.

(* ============================ §9 ntl_tw_diff_tri_B/ntl_tw_diff_tri_eps（温度窗差的 ≤_B/ε 三角形）、ntl_tw_arm_upper/ntl_ ============================ *)
From Stdlib Require Import List.
From Stdlib Require Import QArith.Qring.
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
Require Import UpTempWindow.
Require Import UpAblAbsSumLeB.

(* ============================================================ *)
(* Part 0 · 签名核验（依赖签名漂移即编译报错）                          *)
(* ============================================================ *)

Check tw_h_le.                   (* 接口语句实形（节卸载后） *)
Check tw_unif_dist.              (* 1/N（卸载后三参） *)
Check tw_wT.                     (* 窗口权重（卸载后七参） *)
Check tw_E2.                     (* e^{2Δ/T}（Delta 首参） *)
Check tw_E2L.                    (* e^{−2Δ/T} *)
Check uabS4_le_add_r.            (* 正余量右吸收（主件使用） *)
Check uabS4_abs_diff_triangle_le_eps. (* 两点核差三角不等式（逐 eps 形，转换层用） *)
Check uabS4_abs_diff_triangle_le_B.   (* 两点核差三角不等式（B 形，转换层用） *)
Check real_le_closure_b_one.     (* B 形单步闭包引理 *)
Check real_le_to_le_b.           (* plain⟹B 单向转换引理 *)
Check tw_abs_le.                 (* |x| ≤ c 两支组合器 *)
Check tw_ring_sub_mult.          (* x·y + −y == (x + −1)·y *)
Check tw_ring_sub_mult_l.        (* y + −(x·y) == (1 + −x)·y *)
Check tw_wT_le_E2invN.           (* 正分支源：w ≤ E2·(1/N) *)
Check tw_E2LinvN_le_wT.          (* 负分支源：E2L·(1/N) ≤ w *)
Check tw_one_minus_exp_le.       (* 1−e^{−E} ≤ e^{E}−1 *)
Check real_le_plus_compat.       (* 加法保序 *)
Check real_le_mult_compat.       (* 正系数乘法保序 *)
Check real_le_trans.             (* 序传递 *)
Check real_opp_plus.             (* −(a+b) == −a + −b *)
Check real_opp_opp.              (* −(−x) == x *)
Check real_plus_comm.            (* 交换 *)
Check real_inv_pos_pos.          (* inv 正性 *)
Check real_minus_r.              (* a−b := a + −b *)

(* ============================================================ *)
(* Part 1 · 转换层：两点核差三角不等式的窗口三点实例                    *)
(*   三点实例化：a := w_T(x)、b := E2L·(1/N)、c := 1/N。               *)
(*   余量差见头注形态差异①：本层两件较接口语句的锐界更宽。             *)
(* ============================================================ *)

Corollary ntl_tw_diff_tri_B : forall (Tok : Set) (states : list Tok)
  (states_nonempty : Not (Id states nil)) (zz : Tok -> Real) (Delta : Real)
  (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le_b
    (real_abs (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                            (tw_unif_dist Tok states states_nonempty)))
    (real_plus
       (real_abs (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                  (real_mult (tw_E2L Delta T Ht)
                             (tw_unif_dist Tok states states_nonempty))))
       (real_abs (real_minus_r
                    (real_mult (tw_E2L Delta T Ht)
                               (tw_unif_dist Tok states states_nonempty))
                    (tw_unif_dist Tok states states_nonempty)))).
Proof.
  intros Tok states states_nonempty zz Delta T Ht x.
  exact (uabS4_abs_diff_triangle_le_B
           (tw_wT Tok states states_nonempty zz T Ht x)
           (real_mult (tw_E2L Delta T Ht)
                      (tw_unif_dist Tok states states_nonempty))
           (tw_unif_dist Tok states states_nonempty)).
Qed.

Corollary ntl_tw_diff_tri_eps : forall (Tok : Set) (states : list Tok)
  (states_nonempty : Not (Id states nil)) (zz : Tok -> Real) (Delta : Real)
  (T : Real) (Ht : real_lt real_zero T) (x : Tok) (e : Real),
  real_lt real_zero e ->
  real_le
    (real_abs (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                            (tw_unif_dist Tok states states_nonempty)))
    (real_plus
       (real_plus
          (real_abs (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                     (real_mult (tw_E2L Delta T Ht)
                                (tw_unif_dist Tok states states_nonempty))))
          (real_abs (real_minus_r
                       (real_mult (tw_E2L Delta T Ht)
                                  (tw_unif_dist Tok states states_nonempty))
                       (tw_unif_dist Tok states states_nonempty))))
       e).
Proof.
  intros Tok states states_nonempty zz Delta T Ht x e He.
  exact (uabS4_abs_diff_triangle_le_eps
           (tw_wT Tok states states_nonempty zz T Ht x)
           (real_mult (tw_E2L Delta T Ht)
                      (tw_unif_dist Tok states states_nonempty))
           (tw_unif_dist Tok states states_nonempty) e He).
Qed.

(* ============================================================ *)
(* Part 2 · 两支基件：接口语句锐界的两支（B 形主件与 plain 形依赖模块共用）*)
(*   正分支：w − (1/N) ≤ (E2 − 1)·(1/N)——tw_wT_le_E2invN ＋ 加法保序   *)
(*         ＋ tw_ring_sub_mult 换形。                                   *)
(*   负分支：−(w − (1/N)) ≤ (E2 − 1)·(1/N)——tw_E2LinvN_le_wT 经负号    *)
(*         翻转得 u−w ≤ u−E2L·u ≡ (1−E2L)·u ≤ (E2−1)·u                  *)
(*         （tw_one_minus_exp_le 实例）。                                *)
(* ============================================================ *)

Lemma ntl_tw_arm_upper : forall (Tok : Set) (states : list Tok)
  (states_nonempty : Not (Id states nil)) (zz : Tok -> Real) (Delta : Real)
  (Hlo : forall x : Tok, real_le (real_opp Delta) (zz x))
  (Hhi : forall x : Tok, real_le (zz x) Delta)
  (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le
    (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                  (tw_unif_dist Tok states states_nonempty))
    (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
               (tw_unif_dist Tok states states_nonempty)).
Proof.
  intros Tok states states_nonempty zz Delta Hlo Hhi T Ht x.
  apply (tw_le_eq_r
           (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                         (tw_unif_dist Tok states states_nonempty))
           (real_minus_r (real_mult (tw_E2 Delta T Ht)
                                    (tw_unif_dist Tok states states_nonempty))
                         (tw_unif_dist Tok states states_nonempty))
           (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
                      (tw_unif_dist Tok states states_nonempty))).
  - apply (real_le_plus_compat
             (tw_wT Tok states states_nonempty zz T Ht x)
             (real_mult (tw_E2 Delta T Ht)
                        (tw_unif_dist Tok states states_nonempty))
             (real_opp (tw_unif_dist Tok states states_nonempty))
             (real_opp (tw_unif_dist Tok states states_nonempty))).
    + exact (tw_wT_le_E2invN Tok states states_nonempty zz Delta Hlo Hhi T Ht x).
    + apply real_le_refl.
  - exact (tw_ring_sub_mult (tw_E2 Delta T Ht)
                            (tw_unif_dist Tok states states_nonempty)).
Qed.

Lemma ntl_tw_arm_lower : forall (Tok : Set) (states : list Tok)
  (states_nonempty : Not (Id states nil)) (zz : Tok -> Real) (Delta : Real)
  (HDelta : real_lt real_zero Delta)
  (Hlo : forall x : Tok, real_le (real_opp Delta) (zz x))
  (Hhi : forall x : Tok, real_le (zz x) Delta)
  (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le
    (real_opp (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                            (tw_unif_dist Tok states states_nonempty)))
    (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
               (tw_unif_dist Tok states states_nonempty)).
Proof.
  intros Tok states states_nonempty zz Delta HDelta Hlo Hhi T Ht x.
  assert (HinvN : real_lt real_zero (tw_unif_dist Tok states states_nonempty))
    by (unfold tw_unif_dist; apply real_inv_pos_pos).
  (* 步1：u − w ≤ u − E2L·u（负号翻转负分支源） *)
  assert (Hstep1 : real_le
            (real_minus_r (tw_unif_dist Tok states states_nonempty)
                          (tw_wT Tok states states_nonempty zz T Ht x))
            (real_minus_r (tw_unif_dist Tok states states_nonempty)
               (real_mult (tw_E2L Delta T Ht)
                          (tw_unif_dist Tok states states_nonempty)))).
  { apply (real_le_plus_compat
             (tw_unif_dist Tok states states_nonempty)
             (tw_unif_dist Tok states states_nonempty)
             (real_opp (tw_wT Tok states states_nonempty zz T Ht x))
             (real_opp (real_mult (tw_E2L Delta T Ht)
                                  (tw_unif_dist Tok states states_nonempty)))).
    - apply real_le_refl.
    - apply (tw_le_opp_compat
               (real_mult (tw_E2L Delta T Ht)
                          (tw_unif_dist Tok states states_nonempty))
               (tw_wT Tok states states_nonempty zz T Ht x)).
      exact (tw_E2LinvN_le_wT Tok states states_nonempty zz Delta Hlo Hhi T Ht x). }
  (* 步2：u − E2L·u ≡ (1−E2L)·u（换形） *)
  assert (Hreshape : real_eq
            (real_minus_r (tw_unif_dist Tok states states_nonempty)
               (real_mult (tw_E2L Delta T Ht)
                          (tw_unif_dist Tok states states_nonempty)))
            (real_mult (real_plus real_one (real_opp (tw_E2L Delta T Ht)))
                       (tw_unif_dist Tok states states_nonempty)))
    by exact (tw_ring_sub_mult_l (tw_E2L Delta T Ht)
                                 (tw_unif_dist Tok states states_nonempty)).
  (* 步3：(1−E2L)·u ≤ (E2−1)·u（1−e^{−E} ≤ e^{E}−1 实例） *)
  assert (Hstep2 : real_le
            (real_mult (real_plus real_one (real_opp (tw_E2L Delta T Ht)))
                       (tw_unif_dist Tok states states_nonempty))
            (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
                       (tw_unif_dist Tok states states_nonempty)))
    by exact (real_le_mult_compat
                (real_plus real_one (real_opp (tw_E2L Delta T Ht)))
                (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
                (tw_unif_dist Tok states states_nonempty) HinvN
                (tw_one_minus_exp_le (tw_u2 Delta T Ht)
                                     (tw_u2_pos Delta HDelta T Ht))).
  (* 核心链：u − w ≤ (E2−1)·u *)
  assert (Hcore : real_le
            (real_minus_r (tw_unif_dist Tok states states_nonempty)
                          (tw_wT Tok states states_nonempty zz T Ht x))
            (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
                       (tw_unif_dist Tok states states_nonempty))).
  { apply (real_le_trans
             (real_minus_r (tw_unif_dist Tok states states_nonempty)
                           (tw_wT Tok states states_nonempty zz T Ht x))
             (real_minus_r (tw_unif_dist Tok states states_nonempty)
                (real_mult (tw_E2L Delta T Ht)
                           (tw_unif_dist Tok states states_nonempty)))
             (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
                        (tw_unif_dist Tok states states_nonempty))).
    - exact Hstep1.
    - apply (real_le_trans
               (real_minus_r (tw_unif_dist Tok states states_nonempty)
                  (real_mult (tw_E2L Delta T Ht)
                             (tw_unif_dist Tok states states_nonempty)))
               (real_mult (real_plus real_one (real_opp (tw_E2L Delta T Ht)))
                          (tw_unif_dist Tok states states_nonempty))
               (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
                          (tw_unif_dist Tok states states_nonempty))).
      + exact (inr Hreshape).
      + exact Hstep2. }
  (* 对称换形：u − w ≡ −(w − u)（opp_plus ＋ opp_opp ＋ comm 三步） *)
  assert (Hsym : real_eq
            (real_minus_r (tw_unif_dist Tok states states_nonempty)
                          (tw_wT Tok states states_nonempty zz T Ht x))
            (real_opp (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                                    (tw_unif_dist Tok states states_nonempty)))).
  { eapply real_eq_trans.
    - apply real_plus_comm.
    - apply real_eq_sym.
      eapply real_eq_trans.
      + apply real_opp_plus.
      + apply (RealSetoid.real_eq_plus_compat
                 (real_opp (tw_wT Tok states states_nonempty zz T Ht x))
                 (real_opp (real_opp (tw_unif_dist Tok states states_nonempty)))
                 (real_opp (tw_wT Tok states states_nonempty zz T Ht x))
                 (tw_unif_dist Tok states states_nonempty)).
        * apply real_eq_refl.
        * apply real_opp_opp. }
  (* 合成：tw_le_eq_l（le a b ＋ eq a c ⟹ le c b） *)
  exact (tw_le_eq_l
           (real_minus_r (tw_unif_dist Tok states states_nonempty)
                         (tw_wT Tok states states_nonempty zz T Ht x))
           (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
                      (tw_unif_dist Tok states states_nonempty))
           (real_opp (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                                   (tw_unif_dist Tok states states_nonempty)))
           Hcore Hsym).
Qed.

(* ============================================================ *)
(* Part 3 · 主件 A：接口语句锐界的 B 形供给（可达最强形）                *)
(*   语句：接口语句实形（UpTempWindow 节卸载后）外层谓词取 real_le_b，   *)
(*   其余逐字同位。证明：real_le_closure_b_one 单步收拢 ＋ 两支经        *)
(*   经 uabS4_le_add_r 右吸收正余量 eps。                               *)
(* ============================================================ *)

Corollary ntl_tw_h_le_b_feed : forall (Tok : Set) (states : list Tok)
  (states_nonempty : Not (Id states nil)) (zz : Tok -> Real) (Delta : Real)
  (HDelta : real_lt real_zero Delta)
  (Hlo : forall x : Tok, real_le (real_opp Delta) (zz x))
  (Hhi : forall x : Tok, real_le (zz x) Delta)
  (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le_b
    (real_abs (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                            (tw_unif_dist Tok states states_nonempty)))
    (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
               (tw_unif_dist Tok states states_nonempty)).
Proof.
  intros Tok states states_nonempty zz Delta HDelta Hlo Hhi T Ht x.
  apply real_le_closure_b_one. intros e He.
  apply tw_abs_le.
  - exact (uabS4_le_add_r _ _ _
             (ntl_tw_arm_upper Tok states states_nonempty zz Delta Hlo Hhi T Ht x)
             He).
  - exact (uabS4_le_add_r _ _ _
             (ntl_tw_arm_lower Tok states states_nonempty zz Delta HDelta Hlo Hhi T Ht x)
             He).
Qed.

(* ============================================================ *)
(* Part 4 · 主件 B：plain 形依赖模块（语句与接口语句实形逐字对齐）         *)
(*   语句＝tw_h_le 节卸载后外形逐字（世界接口同位同序）；证明＝两支      *)
(*   重组（tw_abs_le 内构 Or 分支），不调用语句本体（独立重建，          *)
(*   与语句本体结论内容等价——如实注记：本件为该界的 plain 形供给）。    *)
(* ============================================================ *)

Corollary ntl_tw_h_le_feed : forall (Tok : Set) (states : list Tok)
  (states_nonempty : Not (Id states nil)) (zz : Tok -> Real) (Delta : Real)
  (HDelta : real_lt real_zero Delta)
  (Hlo : forall x : Tok, real_le (real_opp Delta) (zz x))
  (Hhi : forall x : Tok, real_le (zz x) Delta)
  (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le
    (real_abs (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                            (tw_unif_dist Tok states states_nonempty)))
    (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
               (tw_unif_dist Tok states states_nonempty)).
Proof.
  intros Tok states states_nonempty zz Delta HDelta Hlo Hhi T Ht x.
  apply tw_abs_le.
  - exact (ntl_tw_arm_upper Tok states states_nonempty zz Delta Hlo Hhi T Ht x).
  - exact (ntl_tw_arm_lower Tok states states_nonempty zz Delta HDelta Hlo Hhi T Ht x).
Qed.

(* 转换演示：plain 形依赖模块经单向转换引理得 B 形＝主件 A 同语句          *)
Corollary ntl_tw_h_le_feed_to_b : forall (Tok : Set) (states : list Tok)
  (states_nonempty : Not (Id states nil)) (zz : Tok -> Real) (Delta : Real)
  (HDelta : real_lt real_zero Delta)
  (Hlo : forall x : Tok, real_le (real_opp Delta) (zz x))
  (Hhi : forall x : Tok, real_le (zz x) Delta)
  (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le_b
    (real_abs (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                            (tw_unif_dist Tok states states_nonempty)))
    (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
               (tw_unif_dist Tok states states_nonempty)).
Proof.
  intros Tok states states_nonempty zz Delta HDelta Hlo Hhi T Ht x.
  exact (real_le_to_le_b _ _
           (ntl_tw_h_le_feed Tok states states_nonempty zz Delta
                             HDelta Hlo Hhi T Ht x)).
Qed.

(* ============================================================ *)
(* 假设审计：全件 Closed（零外部未证假设）                               *)
(* ============================================================ *)

Print Assumptions ntl_tw_diff_tri_eps.
Print Assumptions ntl_tw_diff_tri_B.
Print Assumptions ntl_tw_arm_upper.
Print Assumptions ntl_tw_arm_lower.
Print Assumptions ntl_tw_h_le_b_feed.
Print Assumptions ntl_tw_h_le_feed.
Print Assumptions ntl_tw_h_le_feed_to_b.

(* ============================ §10 为 S10_KVQuantTrig 五处同形调用点 （destruct (q_arch_geom B) as [N0 HN0]）提供退化支供给。其目标形 ============================ *)
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.
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

(* ============================================================ *)
(* §0 · 库内符号核验（签名不符即编译失败）                                  *)
(* ============================================================ *)

Check QleT'. Check QleT'_to_Qle. Check Qle_to_QleT'.
Check NatLe. Check NatLe_drop.
Check Qle_of_nat. Check qeq_le. Check Qle_trans.
Check Qle_antisym. Check Qmult_0_r.
Check q_arch_geom.

(* ============================================================ *)
(* §1 · 主件：B≤0 退化支 N:=0 平凡给出（目标形逐字同形）                   *)
(* ============================================================ *)

(* A.1 主件：退化侧假设 2B ≤T 0 下，N:=0 即为合格见证——
   2B ≤ 0 ≤ (t+1)#1 链：首段由假设直接承（QleT'_to_Qle 化为 Qle），
   次段 Qle_of_nat 0 (t+1) 显式实例（Z.of_nat 0 # 1 与 0 定义性重合，
   应用即转换判定；nat 前提 (0 ≤ t+1)%nat 由 le_S，le_n 归纳链闭）。 *)
Lemma sb0_arch_geom_degen : forall B : Q,
  QleT' (Qmult (1 + 1)%Q B) 0 ->
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intros B HB.
  exists 0%nat.
  intros t Ht.
  apply Qle_to_QleT'.
  apply (Qle_trans _ 0).
  - exact (QleT'_to_Qle _ _ HB).
  - apply (Qle_of_nat 0 (t + 1)). clear Ht. induction t as [| t IHt]. + apply le_S. apply le_n. + apply le_S. exact IHt.
Qed.

(* ============================================================ *)
(* §2 · 合并件：调用点环境假设下的退化支给出                                 *)
(* ============================================================ *)

(* B.1 合并件：S10 五处同形调用点的局部假设 QleT' 0 B（非负界）之下，退化支
   即夹零支（0 ≤ B ≤ 0 ⟹ B=0）。由序对称性（Qle_antisym）内联收 B==0，
   由零乘（Qmult_0_r）收 (1+1)%Q·0==0，而后入主件 A.1。 *)
Corollary sb0_arch_geom_zero_merge : forall B : Q,
  QleT' 0 B -> QleT' B 0 ->
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intros B HBpos HBneg.
  apply (sb0_arch_geom_degen B).
  apply Qle_to_QleT'.
  apply qeq_le.
  assert (HBeq : B == 0).
  { apply Qle_antisym.
    - exact (QleT'_to_Qle _ _ HBneg).
    - exact (QleT'_to_Qle _ _ HBpos). }
  rewrite HBeq.
  apply Qmult_0_r.
Qed.

(* ============================================================ *)
(* 假设审计：以下各件 Print Assumptions 均为 Closed（零外部未证假设）      *)
(* ============================================================ *)

Print Assumptions sb0_arch_geom_degen.
Print Assumptions sb0_arch_geom_zero_merge.

(* ============================ §11 S10 cauchy_real_sin/cos 输入柯西模的依赖模块 使命：为 S10_KVQuantTrig 的 cauchy_real_sin 与 ============================ *)
From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
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

(* real_zero 的底层序列（与 S02 中 real_zero 之底层序列同形，独立具名以便引用） *)
Definition ucm_zero_seq : Qseq := fun _ : nat => 0%Q.

(* A. 输入柯西模（零序列输入面）：
   cauchy u 在切口 eps/(2*C) 的实例，见证 N1 := O。 *)
Corollary ucm_input_slot_zero : forall (eps C : Q),
  QltT 0 eps -> QltT 0 C ->
  sigT (fun N1 : nat => forall m n : nat, NatLe N1 m -> NatLe N1 n ->
    QltT (Qabs (ucm_zero_seq m - ucm_zero_seq n)) (eps / (2 * C))).
Proof.
  intros eps C Heps HC.
  exists O.
  intros m n Hm Hn.
  unfold ucm_zero_seq.
  simpl.
  apply (qltT_div_pos eps (2 * C)).
  - exact Heps.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat 2 C).
    + unfold Qlt. simpl. lia.
    + apply QltT_to_Qlt. exact HC.
Qed.

(* B. 输入柯西模（常值序列输入面，覆盖 real_const c 族使用处）：
   cauchy (fun _ => c) 在切口 eps/(2*C) 的实例，见证 N1 := O。 *)
Corollary ucm_input_slot_const : forall (c eps C : Q),
  QltT 0 eps -> QltT 0 C ->
  sigT (fun N1 : nat => forall m n : nat, NatLe N1 m -> NatLe N1 n ->
    QltT (Qabs (c - c)) (eps / (2 * C))).
Proof.
  intros c eps C Heps HC.
  exists O.
  intros m n Hm Hn.
  apply (qltT_eq_compat_l 0 (Qabs (c - c))).
  - apply Qeq_sym. apply q_abs_self_zero.
  - apply (qltT_div_pos eps (2 * C)).
    + exact Heps.
    + apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat 2 C).
      * unfold Qlt. simpl. lia.
      * apply QltT_to_Qlt. exact HC.
Qed.

(* C. 具体输入证书：real_zero 输入下 sin 部分和序列的柯西证书，
   见证 N := O（cauchy_real_sin 之 N1 在此输入面具体为 O）。 *)
Corollary ucm_sin_zero_cauchy :
  cauchy (fun n : nat => sin_partial n (projT1 real_zero n)).
Proof.
  intros eps Heps.
  exists O.
  intros m n Hm Hn.
  change (sin_partial m (projT1 real_zero m)) with (sin_partial m 0).
  change (sin_partial n (projT1 real_zero n)) with (sin_partial n 0).
  assert (H1 : sin_partial m 0 - sin_partial n 0 == 0).
  { rewrite (sc_sin_partial_zero m). rewrite (sc_sin_partial_zero n). ring. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
  - apply qeq_le.
    apply (Qabs_wd (sin_partial m 0 - sin_partial n 0) 0). exact H1.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* D. 具体输入证书：real_zero 输入下 cos 部分和序列的柯西证书，
   见证 N := O（cauchy_real_cos 之 N1 在此输入面具体为 O）。 *)
Corollary ucm_cos_zero_cauchy :
  cauchy (fun n : nat => cos_partial n (projT1 real_zero n)).
Proof.
  intros eps Heps.
  exists O.
  intros m n Hm Hn.
  change (cos_partial m (projT1 real_zero m)) with (cos_partial m 0).
  change (cos_partial n (projT1 real_zero n)) with (cos_partial n 0).
  assert (H1 : cos_partial m 0 - cos_partial n 0 == 0).
  { rewrite (sc_cos_partial_one m). rewrite (sc_cos_partial_one n). ring. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
  - apply qeq_le.
    apply (Qabs_wd (cos_partial m 0 - cos_partial n 0) 0). exact H1.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* 假设审计：以下四件 Print Assumptions 均为 Closed（零外部未证假设） *)
Print Assumptions ucm_input_slot_zero.
Print Assumptions ucm_input_slot_const.
Print Assumptions ucm_sin_zero_cauchy.
Print Assumptions ucm_cos_zero_cauchy.

(* ============================ §12 半量重构恒等式的系数参数化形 keh_split_reconst（c+c==1 即可）、两点核差 ε/2 前后分摊普适引理 keh_eps_half_a ============================ *)
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

(* ---------- §0 局部代数包（基座左形对应的右形；照 UpKVDrift_P2 体例） ---------- *)

(* 0 + a == a（库内 real_plus_zero 只给 a + 0 == a，此为左形） *)
Lemma keh_plus_zero_l : forall a : Real, real_eq (real_plus real_zero a) a.
Proof.
  intro a.
  exact (real_eq_trans (real_plus real_zero a) (real_plus a real_zero) a
           (real_plus_comm real_zero a) (real_plus_zero a)).
Qed.

(* 1·a == a（real_mult_one 为右形 a·1 == a，此为对应左形） *)
Lemma keh_one_mult_l : forall a : Real, real_eq (real_mult real_one a) a.
Proof.
  intro a.
  exact (real_eq_trans (real_mult real_one a) (real_mult a real_one) a
           (real_mult_comm real_one a) (real_mult_one a)).
Qed.

(* 右分配：(a + b)·c == a·c + b·c（real_distrib 为左形；经 real_mult_comm 转换） *)
Lemma keh_distrib_r : forall a b c0 : Real,
  real_eq (real_mult (real_plus a b) c0)
          (real_plus (real_mult a c0) (real_mult b c0)).
Proof.
  intros a b c0.
  apply (real_eq_trans (real_mult (real_plus a b) c0)
                       (real_mult c0 (real_plus a b)) _).
  - apply real_mult_comm.
  - apply (real_eq_trans (real_mult c0 (real_plus a b))
             (real_plus (real_mult c0 a) (real_mult c0 b)) _).
    + exact (real_distrib c0 a b).
    + apply (RealSetoid.real_eq_plus_compat (real_mult c0 a) (real_mult c0 b)
               (real_mult a c0) (real_mult b c0)
               (real_mult_comm c0 a) (real_mult_comm c0 b)).
Qed.

(* 2 = 1 + 1 > 0 *)
Lemma keh_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus real_one real_one)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_lt_plus_compat; exact real_lt_zero_one.
Qed.

(* t + t == (1+1)·t *)
Lemma keh_self_two : forall t : Real,
  real_eq (real_plus t t) (real_mult (real_plus real_one real_one) t).
Proof.
  intro t.
  apply (real_eq_trans
           (real_plus t t)
           (real_plus (real_mult t real_one) (real_mult t real_one))
           (real_mult (real_plus real_one real_one) t)).
  - apply (RealSetoid.real_eq_plus_compat t t (real_mult t real_one)
             (real_mult t real_one)
             (real_eq_sym (real_mult t real_one) t (real_mult_one t))
             (real_eq_sym (real_mult t real_one) t (real_mult_one t))).
  - apply (real_eq_trans
             (real_plus (real_mult t real_one) (real_mult t real_one))
             (real_plus (real_mult real_one t) (real_mult real_one t))
             (real_mult (real_plus real_one real_one) t)).
    + apply (RealSetoid.real_eq_plus_compat (real_mult t real_one)
               (real_mult t real_one) (real_mult real_one t) (real_mult real_one t)
               (real_mult_comm t real_one) (real_mult_comm t real_one)).
    + exact (real_eq_sym _ _ (keh_distrib_r real_one real_one t)).
Qed.

(* ---------- §1 普适供给引理（本件主增量） ---------- *)

(* 1a. 半量重构恒等式（系数参数化）：任取半量系数 c，只要 c + c == 1， *)
(*   则两半份 (c·ε)+(c·ε) 恰重构整 ε。内联版 Hhh 为 inv(1+1) 专用； *)
(*   此处对任意倍元分解 c 开放（分配律＋倍元恒等式两步，与系数 *)
(*   构造路线无关）。 *)
Lemma keh_split_reconst : forall c eps : Real,
  real_eq (real_plus c c) real_one ->
  real_eq (real_plus (real_mult c eps) (real_mult c eps)) eps.
Proof.
  intros c eps Hcc.
  apply (real_eq_trans
           (real_plus (real_mult c eps) (real_mult c eps))
           (real_mult (real_plus c c) eps)
           eps).
  - apply real_eq_sym. apply keh_distrib_r.
  - apply (real_eq_trans
             (real_mult (real_plus c c) eps)
             (real_mult real_one eps)
             eps).
    + apply (RealSetoid.real_eq_mult_compat
               (real_plus c c) eps real_one eps
               Hcc (real_eq_refl eps)).
    + apply keh_one_mult_l.
Qed.

(* 1b. 半量正性传输：0 < c 且 0 < ε ⟹ 0 < c·ε *)
Lemma keh_split_pos : forall c eps : Real,
  real_lt real_zero c ->
  real_lt real_zero eps ->
  real_lt real_zero (real_mult c eps).
Proof.
  intros c eps Hc Heps. exact (real_mult_pos_compat c eps Hc Heps).
Qed.

(* 1c. 主供给引理·两点核差形 ε/2 前后分摊： *)
(*   三角面给 |a+b| ≤ |a|+|b|+c·ε（前半份），归纳面给 |b| ≤ B+c·ε *)
(*   （后半份），经 1a 重构恒等式将两半份合并为整 ε。内联位点 *)
(*   （UpKVDrift_P2）为本引理在 a:=f w、b:=Σrest、B:=Σrest|f|、 *)
(*   c:=inv(1+1) 的一次特例展开。 *)
Lemma keh_eps_half_amort : forall a b B c eps : Real,
  real_lt real_zero eps ->
  real_eq (real_plus c c) real_one ->
  real_lt real_zero c ->
  real_le (real_abs (real_plus a b))
          (real_plus (real_plus (real_abs a) (real_abs b)) (real_mult c eps)) ->
  real_le (real_abs b) (real_plus B (real_mult c eps)) ->
  real_le (real_abs (real_plus a b))
          (real_plus (real_plus (real_abs a) B) eps).
Proof.
  intros a b B c eps Heps Hcc Hc Htri Hib.
  apply (real_le_trans
           (real_abs (real_plus a b))
           (real_plus (real_plus (real_abs a) (real_abs b)) (real_mult c eps))
           (real_plus (real_plus (real_abs a) B) eps)
           Htri).
  apply (real_le_trans
           (real_plus (real_plus (real_abs a) (real_abs b)) (real_mult c eps))
           (real_plus
              (real_plus (real_abs a) (real_plus B (real_mult c eps)))
              (real_mult c eps))
           (real_plus (real_plus (real_abs a) B) eps)).
  - apply real_le_plus_compat.
    + apply real_le_plus_compat.
      * apply real_le_refl.
      * exact Hib.
    + apply real_le_refl.
  - apply (RealSetoid.real_eq_le _ _
             (real_eq_trans
                (real_plus
                   (real_plus (real_abs a) (real_plus B (real_mult c eps)))
                   (real_mult c eps))
                (real_plus
                   (real_plus (real_plus (real_abs a) B) (real_mult c eps))
                   (real_mult c eps))
                (real_plus (real_plus (real_abs a) B) eps)
                (RealSetoid.real_eq_plus_compat
                   (real_plus (real_abs a) (real_plus B (real_mult c eps)))
                   (real_mult c eps)
                   (real_plus (real_plus (real_abs a) B) (real_mult c eps))
                   (real_mult c eps)
                   (real_plus_assoc (real_abs a) B (real_mult c eps))
                   (real_eq_refl (real_mult c eps)))
                (real_eq_trans
                   (real_plus
                      (real_plus (real_plus (real_abs a) B) (real_mult c eps))
                      (real_mult c eps))
                   (real_plus
                      (real_plus (real_abs a) B)
                      (real_plus (real_mult c eps) (real_mult c eps)))
                   (real_plus (real_plus (real_abs a) B) eps)
                   (real_eq_sym _ _
                      (real_plus_assoc (real_plus (real_abs a) B)
                         (real_mult c eps) (real_mult c eps)))
                   (RealSetoid.real_eq_plus_compat
                      (real_plus (real_abs a) B)
                      (real_plus (real_mult c eps) (real_mult c eps))
                      (real_plus (real_abs a) B) eps
                      (real_eq_refl (real_plus (real_abs a) B))
                      (keh_split_reconst c eps Hcc))))).
Qed.

(* ---------- §2 规范半量供给包（inv(1+1) 实例；内联实形的命名供给） ---------- *)

Definition keh_half : Real :=
  real_inv_pos (real_plus real_one real_one) keh_two_pos.

Lemma keh_half_pos : real_lt real_zero keh_half.
Proof.
  exact (real_inv_pos_pos (real_plus real_one real_one) keh_two_pos).
Qed.

(* inv(1+1) + inv(1+1) == 1（倍元恒等式：内联 Hinv2one 的命名形） *)
Lemma keh_half_double : real_eq (real_plus keh_half keh_half) real_one.
Proof.
  apply (real_eq_trans
           (real_plus keh_half keh_half)
           (real_mult (real_plus real_one real_one) keh_half)
           real_one).
  - exact (keh_self_two keh_half).
  - exact (real_inv_pos_correct (real_plus real_one real_one) keh_two_pos).
Qed.

Lemma keh_half_share_pos : forall eps : Real,
  real_lt real_zero eps -> real_lt real_zero (real_mult keh_half eps).
Proof.
  intros eps Heps. exact (keh_split_pos keh_half eps keh_half_pos Heps).
Qed.

Lemma keh_half_share_reconst : forall eps : Real,
  real_eq (real_plus (real_mult keh_half eps) (real_mult keh_half eps)) eps.
Proof.
  intros eps. exact (keh_split_reconst keh_half eps keh_half_double).
Qed.

(* ---------- §3 KV 原语句回接 Corollary（原内联位点语句的等价重述形） ---------- *)

(* 语句面与 UpKVDrift_P2.kv_abs_triangle_list_eps 同构；cons 归纳步经 *)
(* keh_eps_half_amort＋规范半量包供给，分摊不再内联。 *)
Corollary keh_kv_abs_triangle_list_eps : forall (X : Set) (f : X -> Real)
  (l : list X) (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x : X => real_abs (f x)) l) eps).
Proof.
  intros X f l. induction l as [| w rest IH]; intros eps Heps.
  - apply (real_le_trans
             (real_abs (real_list_sum X f (@nil X))) real_zero
             (real_plus real_zero eps)).
    + apply RealSetoid.real_eq_le. exact real_abs_zero_req.
    + apply real_le_from_lt_aux.
      apply (RealSetoid.real_lt_id_r real_zero eps (real_plus real_zero eps)
               (real_eq_sym _ _ (keh_plus_zero_l eps)) Heps).
  - cbn [real_list_sum].
    apply (keh_eps_half_amort (f w) (real_list_sum X f rest)
             (real_list_sum X (fun x : X => real_abs (f x)) rest)
             keh_half eps Heps keh_half_double keh_half_pos).
    + exact (real_abs_triangle_le_eps (f w) (real_list_sum X f rest)
               (real_mult keh_half eps) (keh_half_share_pos eps Heps)).
    + exact (IH (real_mult keh_half eps) (keh_half_share_pos eps Heps)).
Qed.

(* ============================ §13 S10 内 Qabs 同族绝对值三角第二依赖模块（15 处） ============================ *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
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
Require Import UpAblAbsQFeed.

(* ============================================================ *)
(* §0 · 库内符号核验（签名不符即编译失败）                                  *)
(* ============================================================ *)

Check QleT'. Check Qabs. Check Qplus. Check Qminus. Check Qopp.
Check uaq_abs_triangle_plus.

(* ============================================================ *)
(* §A · 15 处调用点逐件供给（语句面全 QleT' Set 层）                        *)
(* ============================================================ *)

(* uaq2_s10_6282_band（sc_cs_sq_err_le 三角步骤｜实参 xs:=cos 双重和, ys:=sin 双重和） *)
Corollary uaq2_s10_6282_band : forall xs ys : Q,
  QleT' (Qabs (xs + ys)) (Qabs xs + Qabs ys).
Proof.
  intros xs ys.
  (* 刀：uaq_abs_triangle_plus 引擎体整体内联（模板＝UpAblAbsQFeed.v:59-61：
     转换桥 Qle_to_QleT'＋stdlib Qabs_triangle），xs/ys 实例化。 *)
  apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* 不可化批量登记（9 条跨件单跳直引）：uaq2_s10_7633_mid_err／10643_h3／
   10644_h2／10852_bands／11009_d1d2／11195_seq_plus／11220_split／
   12138_seq_plus／12168_split——均为 uaq_abs_triangle_plus 逐字同形实例
   （本件版记「证明增量零」供给体例之单跳最短形），批量登记不凑数。 *)

(* uaq2_s10_7633_mid_err（cos 中点缺陷和分解｜实参 x:=cauchy_real_cos 投影项, q:=cos_partial K1 m） *)
Corollary uaq2_s10_7633_mid_err : forall x q : Q,
  QleT' (Qabs ((x - q) + q)) (Qabs (x - q) + Qabs q).
Proof. intros x q. apply uaq_abs_triangle_plus. Qed.

(* uaq2_s10_8224_inv_pt（cos_inv_pt 差和链｜实参 a:=cos_partial k u, b:=cos_partial k v, c:=projT1 real_zero k） *)
Corollary uaq2_s10_8224_inv_pt : forall a b c : Q,
  QleT' (Qabs ((a - c) + (c - b))) (Qabs (a - c) + Qabs (c - b)).
Proof.
  intros a b c.
  (* 刀：uaq_abs_triangle_plus 引擎体整体内联（模板＝UpAblAbsQFeed.v:59-61：
     转换桥 Qle_to_QleT'＋stdlib Qabs_triangle），a/b/c 实例化。 *)
  apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* uaq2_s10_8485_root_cauchy（根收敛柯西链｜实参 p:=cos_partial n (cos_zero_seq n),
   m:=cos_partial n (cos_zero_seq N0), z:=projT1 real_zero n） *)
Corollary uaq2_s10_8485_root_cauchy : forall p m z : Q,
  QleT' (Qabs ((p - m) + (m - z))) (Qabs (p - m) + Qabs (m - z)).
Proof.
  intros p m z.
  (* 刀：uaq_abs_triangle_plus 引擎体整体内联（模板＝UpAblAbsQFeed.v:59-61：
     转换桥 Qle_to_QleT'＋stdlib Qabs_triangle），p/m/z 实例化。 *)
  apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* uaq2_s10_10642_h4（sc_add_sin_err 四带 Ht1｜实参 b1..b4：四条带和） *)
Corollary uaq2_s10_10642_h4 : forall b1 b2 b3 b4 : Q,
  QleT' (Qabs (((b1 + b2) + b3) + b4)) (Qabs ((b1 + b2) + b3) + Qabs b4).
Proof.
  intros b1 b2 b3 b4.
  (* 刀：uaq_abs_triangle_plus 引擎体整体内联（模板＝UpAblAbsQFeed.v:59-61：
     转换桥 Qle_to_QleT'＋stdlib Qabs_triangle），b1..b4 实例化。 *)
  apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* uaq2_s10_10643_h3（同引理 Ht2） *)
Corollary uaq2_s10_10643_h3 : forall b1 b2 b3 : Q,
  QleT' (Qabs ((b1 + b2) + b3)) (Qabs (b1 + b2) + Qabs b3).
Proof. intros b1 b2 b3. apply uaq_abs_triangle_plus. Qed.

(* uaq2_s10_10644_h2（同引理 Ht3） *)
Corollary uaq2_s10_10644_h2 : forall b1 b2 : Q,
  QleT' (Qabs (b1 + b2)) (Qabs b1 + Qabs b2).
Proof. exact uaq_abs_triangle_plus. Qed.

(* uaq2_s10_10852_bands（sc_add_band_abs 带和三角｜实参 up:=上带和, r:=右带和） *)
Corollary uaq2_s10_10852_bands : forall up r : Q,
  QleT' (Qabs (up + r)) (Qabs up + Qabs r).
Proof. exact uaq_abs_triangle_plus. Qed.

(* uaq2_s10_11009_d1d2（sc_add_sin_err_bound 三角｜实参 d1:=cs 族带, d2:=余带） *)
Corollary uaq2_s10_11009_d1d2 : forall d1 d2 : Q,
  QleT' (Qabs (d1 + d2)) (Qabs d1 + Qabs d2).
Proof. exact uaq_abs_triangle_plus. Qed.

(* uaq2_s10_11195_seq_plus（rs_add_sin HsumMT 步｜逐字同形，实参 un:=u n, vn:=v n 序列项） *)
Corollary uaq2_s10_11195_seq_plus : forall un vn : Q,
  QleT' (Qabs (un + vn)) (Qabs un + Qabs vn).
Proof. exact uaq_abs_triangle_plus. Qed.

(* uaq2_s10_11220_split（rs_add_sin 代数拆分和三角｜实参 e1:=逐项残差, e2:=2n 项残差） *)
Corollary uaq2_s10_11220_split : forall e1 e2 : Q,
  QleT' (Qabs (e1 + e2)) (Qabs e1 + Qabs e2).
Proof. exact uaq_abs_triangle_plus. Qed.

(* uaq2_s10_11938_outer（sc_add_cos_err_abs 双三角外层｜实参 dc:=Dc 带, ds:=Ds 带, an:=An 反对称带） *)
Corollary uaq2_s10_11938_outer : forall dc ds an : Q,
  QleT' (Qabs ((dc - ds) + an)) (Qabs (dc - ds) + Qabs an).
Proof.
  intros dc ds an.
  (* 刀：uaq_abs_triangle_plus 引擎体整体内联（模板＝UpAblAbsQFeed.v:59-61：
     转换桥 Qle_to_QleT'＋stdlib Qabs_triangle），dc/ds/an 实例化。 *)
  apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* uaq2_s10_11944_inner（同引理内嵌负带三角｜实参 dc:=Dc, ds:=Ds；b 实例化为 Qopp ds） *)
Corollary uaq2_s10_11944_inner : forall dc ds : Q,
  QleT' (Qabs (dc + Qopp ds)) (Qabs dc + Qabs (Qopp ds)).
Proof.
  intros dc ds.
  (* 刀：uaq_abs_triangle_plus 引擎体整体内联（模板＝UpAblAbsQFeed.v:59-61：
     转换桥 Qle_to_QleT'＋stdlib Qabs_triangle），dc/ds（ys:=Qopp ds 位） 实例化。 *)
  apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* uaq2_s10_12138_seq_plus（rs_add_cos HsumMT 步｜逐字同形，实参 un:=u n, vn:=v n 序列项） *)
Corollary uaq2_s10_12138_seq_plus : forall un vn : Q,
  QleT' (Qabs (un + vn)) (Qabs un + Qabs vn).
Proof. exact uaq_abs_triangle_plus. Qed.

(* uaq2_s10_12168_split（rs_add_cos 代数拆分和三角｜实参 e1:=逐项残差, e2:=2n 项残差） *)
Corollary uaq2_s10_12168_split : forall e1 e2 : Q,
  QleT' (Qabs (e1 + e2)) (Qabs e1 + Qabs e2).
Proof. exact uaq_abs_triangle_plus. Qed.

(* ============================================================ *)
(* 假设审计：以下各件 Print Assumptions 均为 Closed（零外部未证假设）      *)
(* ============================================================ *)

Print Assumptions uaq2_s10_6282_band.
Print Assumptions uaq2_s10_7633_mid_err.
Print Assumptions uaq2_s10_8224_inv_pt.
Print Assumptions uaq2_s10_8485_root_cauchy.
Print Assumptions uaq2_s10_10642_h4.
Print Assumptions uaq2_s10_10643_h3.
Print Assumptions uaq2_s10_10644_h2.
Print Assumptions uaq2_s10_10852_bands.
Print Assumptions uaq2_s10_11009_d1d2.
Print Assumptions uaq2_s10_11195_seq_plus.
Print Assumptions uaq2_s10_11220_split.
Print Assumptions uaq2_s10_11938_outer.
Print Assumptions uaq2_s10_11944_inner.
Print Assumptions uaq2_s10_12138_seq_plus.
Print Assumptions uaq2_s10_12168_split.

(* ============================ §14 本件形式化 Q 层下取整深度的阿基米德见证： 1/(N+2)#1 形分式上界逼近任意正 Q（uabS4b_arch_N 指标显式） ============================ *)
From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
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
Require Import UpAblAbsSumLeB2.
Require Import UpAblAbsQFeed.

(* ============================================================ *)
(* §0 · 依赖签名核验（所引标识符漂移即编译期暴露） *)
(* ============================================================ *)

Check QltT. Check QleT'.
Check QltT_to_Qlt. Check Qlt_to_QltT. Check Qle_to_QleT'.
Check qltT_eq_compat_l. Check qleT'_ltT_ltT. Check qeq_le.
Check Qeq_sym. Check Qeq_trans. Check Qabs_wd. Check Qabs_pos.
Check Qle_trans.
Check uabS4b_arch_N. Check uabS4b_null_lt. Check uabS4b_null_mono.
Check uabS4b_null_nonneg. Check uabS4b_pos_succ_Z.
Check uaq_qfloor_abs_margin.
Check NatLe_drop.
Check Qmult_lt_0_compat. Check Qinv_lt_0_compat.
Check q_arch_inv. Check q_arch_geom. Check arch_decay.
Check lp_four. Check sc_lp_four_pos. Check sc_lp_four_arch_lt.

(* ============================================================ *)
(* §A · 单位分数核：N := S(uabS4b_arch_N u) 满足 q_arch_inv 结论形      *)
(* ============================================================ *)

(* A.1 核引理：N := S(uabS4b_arch_N u) 时 1/(N+2)#1 <T u。证明链：
   uabS4b_null_lt 给 1/(n+1) <T u；uabS4b_null_mono 给
   1/(n+2) ≤ 1/(n+1)；再以 Z 恒等式 uabS4b_pos_succ_Z 作 Qeq 改写成 #1 分母形。 *)
Lemma qfd_arch_inv_core : forall u : Q, QltT 0 u ->
  QltT (1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2) # 1)) u.
Proof.
  intros u Hu.
  assert (Hzk : Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2)
                = Z.pos (Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1))).
  { rewrite uabS4b_pos_succ_Z. lia. }
  assert (Hstep : 1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2) # 1)
                  == (1#(Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1)))%Q).
  { rewrite Hzk. reflexivity. }
  apply (qltT_eq_compat_l
           (1#(Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1)))
           (1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2) # 1))
           u
           (Qeq_sym _ _ Hstep)).
  apply (qleT'_ltT_ltT
           (1#(Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1)))
           (1#(Pos.of_succ_nat (uabS4b_arch_N u)))
           u).
  - apply Qle_to_QleT'. apply uabS4b_null_mono. generalize (uabS4b_arch_N u) as n. intro n. apply le_S. induction n as [| n IHn]. + apply le_S. apply le_n. + apply le_n_S. exact IHn.
  - exact (uabS4b_null_lt u Hu).
Qed.

(* A.2 结论形实例：q_arch_inv 结论所要求的 sigT(N, 1/(N+2)#1 < u) 形的
   具体见证——指标取具体自然数 S(uabS4b_arch_N u)，无阿基米德不透明环节。
   下游凡对 q_arch_inv (eps / lp_four) 作 destruct 后以 exists 供证的
   见证位，均可以此具体值实例化；plain-Qlt 面经 QltT_to_Qlt 一步转换即得。 *)
Corollary qfd_arch_inv_instT : forall u : Q, QltT 0 u ->
  sigT (fun N : nat => QltT (1 / (Z.of_nat (N + 2) # 1)) u).
Proof.
  intros u Hu.
  exists (Datatypes.S (uabS4b_arch_N u)).
  apply qfd_arch_inv_core.
  exact Hu.
Qed.

(* ============================================================ *)
(* §B · 绝对值下的界：Qabs(1/(N+2)#1) <T u                              *)
(* ============================================================ *)

(* B.1 绝对值界：Qabs(1/(S(uabS4b_arch_N u)+2)#1) <T u——先证
   Qabs(1/(n+2)#1) ≤ Qabs(1/(n+1)#1)（n := uabS4b_arch_N u，经
   qeq_le/Qabs_wd/Qabs_pos），尾句 exact uaq_qfloor_abs_margin 收尾。 *)
Corollary qfd_pi_margin_absT : forall u : Q, QltT 0 u ->
  QltT (Qabs (1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2) # 1))) u.
Proof.
  intros u Hu.
  assert (Hstep : QleT' (Qabs (1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2) # 1)))
                        (Qabs (1#(Pos.of_succ_nat (uabS4b_arch_N u))))).
  { apply Qle_to_QleT'.
    apply (Qle_trans _ (1#(Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1)))).
    - apply qeq_le.
      apply (Qeq_trans _ (Qabs (1#(Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1))))).
      + apply Qabs_wd.
        assert (Hzk1 : 1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2) # 1)
                       == (1#(Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1)))%Q).
        { assert (Hzk : Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2)
                        = Z.pos (Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1))).
          { rewrite uabS4b_pos_succ_Z. lia. }
          rewrite Hzk. reflexivity. }
        exact Hzk1.
      + apply Qabs_pos. apply uabS4b_null_nonneg.
    - apply (Qle_trans _ (1#(Pos.of_succ_nat (uabS4b_arch_N u)))).
      + apply uabS4b_null_mono. generalize (uabS4b_arch_N u) as n. intro n. apply le_S. induction n as [| n IHn]. * apply le_S. apply le_n. * apply le_n_S. exact IHn.
      + apply qeq_le.
        apply (Qeq_sym (Qabs (1#(Pos.of_succ_nat (uabS4b_arch_N u))))
                       (1#(Pos.of_succ_nat (uabS4b_arch_N u)))).
        apply Qabs_pos. apply uabS4b_null_nonneg. }
  apply (qleT'_ltT_ltT
           (Qabs (1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2) # 1)))
           (Qabs (1#(Pos.of_succ_nat (uabS4b_arch_N u))))
           u).
  - exact Hstep.
  - exact (uaq_qfloor_abs_margin u Hu).
Qed.

(* ============================================================ *)
(* §C · 四倍尾量：lp_four · 1/(N+2)#1 <T eps                            *)
(* ============================================================ *)

(* C.1 π-Leibniz 四倍尾量：应用 sc_lp_four_arch_lt（plain-Qlt 面，经
   QltT_to_Qlt 转换），指标以 N := S(uabS4b_arch_N(eps/lp_four)) 实例化；
   eps/lp_four 的正性由 Qmult_lt_0_compat、Qinv_lt_0_compat 与 sc_lp_four_pos 推得。 *)
Corollary qfd_pi_four_marginT : forall eps : Q, QltT 0 eps ->
  QltT (lp_four * (1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N (eps / lp_four)) + 2) # 1))) eps.
Proof.
  intros eps Hep.
  assert (Hq4 : QltT 0 (eps / lp_four)).
  { apply Qlt_to_QltT. unfold Qdiv.
    apply (Qmult_lt_0_compat eps (Qinv lp_four)).
    - apply QltT_to_Qlt. exact Hep.
    - apply Qinv_lt_0_compat. exact sc_lp_four_pos. }
  apply Qlt_to_QltT.
  apply (sc_lp_four_arch_lt eps (Datatypes.S (uabS4b_arch_N (eps / lp_four)))).
  - exact (QltT_to_Qlt _ _ Hep).
  - apply QltT_to_Qlt. apply (qfd_arch_inv_core (eps / lp_four) Hq4).
Qed.

(* ============================================================ *)
(* §D · 假设审计：四定理 Print Assumptions 全 Closed（零外部未证假设）      *)
(* ============================================================ *)

Print Assumptions qfd_arch_inv_core.
Print Assumptions qfd_arch_inv_instT.
Print Assumptions qfd_pi_margin_absT.
Print Assumptions qfd_pi_four_marginT.

(* ============================ §15 调和序列 ucl_harm_seq 的完备性与极限＝0 （real_lim 面非平凡具体输入实例） ============================ *)
From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Setoid.
From Stdlib Require Import Arith.PeanoNat.
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

(* 调和型尾项：ucl_harm n := 1/(n+2)（与 q_arch_inv 的单位分数形同形，
   q_arch_inv/q_arch_inv_mono/q_arch_inv_pos 经定义展开直接应用）。 *)
Definition ucl_harm (n : nat) : Q := (1 / (Z.of_nat (n + 2) # 1))%Q.

(* 具体序列：第 n 项＝常值实数 1/(n+2)——每一项各自具体、整体非平凡
   （非常值序列，非 real_zero/real_const 退化输入） *)
Definition ucl_harm_seq : nat -> Real := fun n => real_const (ucl_harm n).

(* 基件一：正性——由 q_arch_inv_pos 经 ucl_harm 定义展开直接推得 *)
Lemma ucl_harm_pos : forall n : nat, Qlt 0 (ucl_harm n).
Proof. intro n. exact (q_arch_inv_pos n). Qed.

(* 基件二：单调（n ≤ m ⟹ 1/(m+2) ≤ 1/(n+2)，分母增大则值减小；
   n < m 情形循 q_arch_inv_mono 的 Qinv_lt_contravar 链得严格不等） *)
Lemma ucl_harm_mono : forall n m : nat, (n <= m)%nat -> Qle (ucl_harm m) (ucl_harm n).
Proof.
  intros n m Hle.
  destruct (Nat.eq_dec n m) as [Heq | Hne].
  - subst. apply Qle_refl.
  - assert (Hlt : (n < m)%nat) by lia.
    apply Qlt_le_weak.
    setoid_replace (ucl_harm m) with (/ (Z.of_nat (m + 2) # 1))
      by (unfold ucl_harm, Qdiv; apply Qmult_1_l).
    setoid_replace (ucl_harm n) with (/ (Z.of_nat (n + 2) # 1))
      by (unfold ucl_harm, Qdiv; apply Qmult_1_l).
    assert (HposN : Qlt 0 (Z.of_nat (n + 2) # 1)) by (unfold Qlt; simpl; lia).
    assert (HposM : Qlt 0 (Z.of_nat (m + 2) # 1)) by (unfold Qlt; simpl; lia).
    apply (proj1 (Qinv_lt_contravar (Z.of_nat (n + 2) # 1) (Z.of_nat (m + 2) # 1)
                  HposN HposM)).
    unfold Qlt. simpl. lia.
Qed.

(* 基件三：尾界（N ≤ n 且 ucl_harm N < eps ⟹ ucl_harm n < eps，由单调性） *)
Lemma ucl_harm_tail_lt : forall (eps : Q) (N n : nat),
  (N <= n)%nat -> Qlt (ucl_harm N) eps -> Qlt (ucl_harm n) eps.
Proof.
  intros eps N n Hn Hlt.
  apply (Qle_lt_trans (ucl_harm n) (ucl_harm N) eps).
  - apply ucl_harm_mono. exact Hn.
  - exact Hlt.
Qed.

(* 基件四：双侧尾差界（0 ≤ a,b < e ⟹ |a − b| < e；应用 q_abs_lt_two_sided，
   两侧各以 Qopp_lt_compat 与 Qplus_le_compat 的单调链推得） *)
Lemma ucl_harm_diff_abs_lt : forall (a b e : Q),
  Qlt 0 e -> Qle 0 a -> Qle 0 b -> Qlt a e -> Qlt b e -> Qlt (Qabs (a - b)) e.
Proof.
  intros a b e He Hap Hbp Hae Hbe.
  apply (q_abs_lt_two_sided (a - b) e He).
  - (* −e < a − b：−e < −b（Qopp_lt_compat 反号）＋ −b ≤ −b + a（Qplus_le_compat） *)
    assert (H1 : Qlt (- e) (- b)) by (apply Qopp_lt_compat; exact Hbe).
    assert (H2 : Qle ((- b) + 0) ((- b) + a)).
    { apply (Qplus_le_compat (- b) (- b) 0 a).
      - apply Qle_refl.
      - exact Hap. }
    setoid_replace ((- b) + 0) with (- b) in H2 by ring.
    setoid_replace ((- b) + a) with (a - b) in H2 by ring.
    exact (Qlt_le_trans (- e) (- b) (a - b) H1 H2).
  - (* a − b < e：a − b = a + (−b) ≤ a + 0（Qplus_le_compat，−b ≤ 0）< e *)
    assert (H3 : Qle ((- b) + 0) ((- b) + b)).
    { apply (Qplus_le_compat (- b) (- b) 0 b).
      - apply Qle_refl.
      - exact Hbp. }
    setoid_replace ((- b) + 0) with (- b) in H3 by ring.
    setoid_replace ((- b) + b) with 0 in H3 by ring.
    assert (H4 : Qle (a + (- b)) (a + 0)).
    { apply (Qplus_le_compat a a (- b) 0).
      - apply Qle_refl.
      - exact H3. }
    setoid_replace (a + (- b)) with (a - b) in H4 by ring.
    setoid_replace (a + 0) with a in H4 by ring.
    exact (Qle_lt_trans (a - b) a e H4 Hae).
Qed.

(* A. 双柯西条件的实例化：real_cauchy_complete 前提所要求的实值双柯西条件
   （同形）在 ucl_harm_seq 面的实例。见证 N := q_arch_inv(eps/2) 的实例——
   阿基米德阈值（对比 ucm_ 系的 N := O，此处为非平凡见证）。 *)
Corollary ucl_harm_cauchy :
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat,
      (N <= m)%nat -> (N <= n)%nat ->
      And (real_lt (real_plus (ucl_harm_seq m) (real_opp (ucl_harm_seq n))) (real_const eps))
          (real_lt (real_plus (ucl_harm_seq n) (real_opp (ucl_harm_seq m))) (real_const eps))).
Proof.
  intros eps Heps.
  assert (Heps2 : QltT 0 (eps / 2)%Q).
  { apply Qlt_to_QltT. apply Qlt_shift_div_l.
    - reflexivity.
    - simpl. apply QltT_to_Qlt. exact Heps. }
  assert (Hepsq : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Heps2q : Qlt 0 (eps / 2)) by (apply QltT_to_Qlt; exact Heps2).
  destruct (q_arch_inv (eps / 2)%Q Heps2q) as [N0 HN0].
  exists N0.
  intros m n Hm Hn.
  assert (Hmb : Qlt (ucl_harm m) (eps / 2)%Q)
    by (apply (ucl_harm_tail_lt (eps / 2)%Q N0 m Hm HN0)).
  assert (Hnb : Qlt (ucl_harm n) (eps / 2)%Q)
    by (apply (ucl_harm_tail_lt (eps / 2)%Q N0 n Hn HN0)).
  assert (Hmpos : Qle 0 (ucl_harm m)) by (apply Qlt_le_weak; apply ucl_harm_pos).
  assert (Hnpos : Qle 0 (ucl_harm n)) by (apply Qlt_le_weak; apply ucl_harm_pos).
  assert (Habs : Qlt (Qabs (ucl_harm m - ucl_harm n)) (eps / 2)%Q)
    by (apply (ucl_harm_diff_abs_lt (ucl_harm m) (ucl_harm n) (eps / 2)%Q
               Heps2q Hmpos Hnpos Hmb Hnb)).
  assert (Habs2 : Qlt (Qabs (ucl_harm n - ucl_harm m)) (eps / 2)%Q)
    by (apply (ucl_harm_diff_abs_lt (ucl_harm n) (ucl_harm m) (eps / 2)%Q
               Heps2q Hnpos Hmpos Hnb Hmb)).
  split.
  - (* 前向：eps − (a − b) == (b − a) + eps（ring）⟹ q_bound_eps_half *)
    exists (eps / 2)%Q. split.
    + exact Heps2.
    + exists O. intros k Hk.
      change (projT1 (real_plus (ucl_harm_seq m) (real_opp (ucl_harm_seq n))) k)
        with (ucl_harm m - ucl_harm n)%Q.
      change (projT1 (real_const eps) k) with eps.
      apply Qlt_to_QltT.
      setoid_replace (eps - (ucl_harm m - ucl_harm n))
        with ((ucl_harm n - ucl_harm m) + eps) by ring.
      exact (q_bound_eps_half (ucl_harm n - ucl_harm m) eps Hepsq Habs2).
  - (* 反向：对称（m、n 互换）⟹ q_bound_eps_half *)
    exists (eps / 2)%Q. split.
    + exact Heps2.
    + exists O. intros k Hk.
      change (projT1 (real_plus (ucl_harm_seq n) (real_opp (ucl_harm_seq m))) k)
        with (ucl_harm n - ucl_harm m)%Q.
      change (projT1 (real_const eps) k) with eps.
      apply Qlt_to_QltT.
      setoid_replace (eps - (ucl_harm n - ucl_harm m))
        with ((ucl_harm m - ucl_harm n) + eps) by ring.
      exact (q_bound_eps_half (ucl_harm m - ucl_harm n) eps Hepsq Habs).
Qed.

(* B. 完备性的实际使用：real_cauchy_complete（Bishop 正则化、零自由变元）
   应用于具体调和序列面——产出抽象正则化对角线极限。 *)
Corollary ucl_harm_complete :
  sigT (fun l : Real => real_lim ucl_harm_seq l).
Proof. exact (real_cauchy_complete ucl_harm_seq ucl_harm_cauchy). Qed.

(* C. 具体极限：ucl_harm_seq 收敛到 real_const 0，
   见证 N := q_arch_inv(eps/2) 的实例（阿基米德阈值）。 *)
Corollary ucl_harm_lim_zero : real_lim ucl_harm_seq (real_const 0).
Proof.
  intros eps Heps.
  assert (Heps2 : QltT 0 (eps / 2)%Q).
  { apply Qlt_to_QltT. apply Qlt_shift_div_l.
    - reflexivity.
    - simpl. apply QltT_to_Qlt. exact Heps. }
  assert (Hepsq : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Heps2q : Qlt 0 (eps / 2)) by (apply QltT_to_Qlt; exact Heps2).
  destruct (q_arch_inv (eps / 2)%Q Heps2q) as [N0 HN0].
  exists N0.
  intros n Hn.
  assert (Hnb : Qlt (ucl_harm n) (eps / 2)%Q)
    by (apply (ucl_harm_tail_lt (eps / 2)%Q N0 n Hn HN0)).
  assert (Hnpos : Qle 0 (ucl_harm n)) by (apply Qlt_le_weak; apply ucl_harm_pos).
  assert (HabsC : Qlt (Qabs (ucl_harm n - 0)) (eps / 2)%Q)
    by (apply (ucl_harm_diff_abs_lt (ucl_harm n) 0 (eps / 2)%Q
               Heps2q Hnpos (Qle_refl 0) Hnb Heps2q)).
  assert (HabsC2 : Qlt (Qabs (0 - ucl_harm n)) (eps / 2)%Q)
    by (apply (ucl_harm_diff_abs_lt 0 (ucl_harm n) (eps / 2)%Q
               Heps2q (Qle_refl 0) Hnpos Heps2q Hnb)).
  split.
  - (* 前向：(0 + eps) − x == (0 − x) + eps（ring，真等式）⟹ q_bound_eps_half *)
    exists (eps / 2)%Q. split.
    + exact Heps2.
    + exists O. intros k Hk.
      change (projT1 (ucl_harm_seq n) k) with (ucl_harm n).
      change (projT1 (real_plus (real_const 0) (real_const eps)) k) with (0 + eps)%Q.
      apply Qlt_to_QltT.
      setoid_replace ((0 + eps) - ucl_harm n) with ((0 - ucl_harm n) + eps) by ring.
      exact (q_bound_eps_half (0 - ucl_harm n) eps Hepsq HabsC2).
  - (* 反向：x − (0 + −eps) == (x − 0) + eps（ring）⟹ q_bound_eps_half *)
    exists (eps / 2)%Q. split.
    + exact Heps2.
    + exists O. intros k Hk.
      change (projT1 (ucl_harm_seq n) k) with (ucl_harm n).
      change (projT1 (real_plus (real_const 0) (real_opp (real_const eps))) k)
        with (0 + - eps)%Q.
      apply Qlt_to_QltT.
      setoid_replace (ucl_harm n - (0 + - eps))
        with ((ucl_harm n - 0) + eps) by ring.
      exact (q_bound_eps_half (ucl_harm n - 0) eps Hepsq HabsC).
Qed.

(* D. 唯一性：real_lim_unique 将 ucl_harm_complete 的抽象正则化对角线极限
   与 real_const 0 等同（完备性与唯一性联用，real_eq 为 Set 层逐 eps 相等）。 *)
Corollary ucl_harm_limit_eq_zero :
  real_eq (projT1 ucl_harm_complete) (real_const 0).
Proof.
  exact (real_lim_unique ucl_harm_seq (projT1 ucl_harm_complete) (real_const 0)
         (projT2 ucl_harm_complete) ucl_harm_lim_zero).
Qed.

(* 假设审计：八件 Print Assumptions 全 Closed *)
Print Assumptions ucl_harm_pos.
Print Assumptions ucl_harm_mono.
Print Assumptions ucl_harm_tail_lt.
Print Assumptions ucl_harm_diff_abs_lt.
Print Assumptions ucl_harm_cauchy.
Print Assumptions ucl_harm_complete.
Print Assumptions ucl_harm_lim_zero.
Print Assumptions ucl_harm_limit_eq_zero.

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ---------- 局部载体 ---------- *)

Fixpoint mte_nat_to_R (n : nat) : Real :=
  match n with
  | O => real_zero
  | Datatypes.S m => real_plus real_one (mte_nat_to_R m)
  end.

Fixpoint mte_rpow (b : Real) (n : nat) : Real :=
  match n with
  | O => real_one
  | Datatypes.S m => real_mult b (mte_rpow b m)
  end.

(* ---------- 逐点 Q 级加法平移（eps 见证的直接构造） ---------- *)

(* a < b ⟹ a+c < b+c *)
Lemma mte_lt_plus_r : forall a b c : Real,
  real_lt a b -> real_lt (real_plus a c) (real_plus b c).
Proof.
  intros a b c Hlt.
  destruct Hlt as [eps [Heps [N HN]]].
  unfold real_lt.
  exists eps. split.
  - exact Heps.
  - exists N. intros n Hn.
    assert (Hpt : projT1 (real_plus b c) n - projT1 (real_plus a c) n
                  == projT1 b n - projT1 a n).
    { assert (Ha : projT1 (real_plus a c) n == projT1 a n + projT1 c n)
        by (apply real_plus_proj).
      assert (Hb : projT1 (real_plus b c) n == projT1 b n + projT1 c n)
        by (apply real_plus_proj).
      rewrite Hb, Ha. field.
    }
    assert (Hcmp : Qcompare eps (projT1 (real_plus b c) n - projT1 (real_plus a c) n)
                 = Qcompare eps (projT1 b n - projT1 a n)).
    { apply (Qcompare_comp eps eps (Qeq_refl eps)). exact Hpt. }
    unfold QltT, Qlt_bool. rewrite Hcmp. exact (HN n Hn).
Qed.

(* 任意 z：z < 壹 + z *)
Lemma mte_lt_plus_one : forall z : Real,
  real_lt z (real_plus real_one z).
Proof.
  intro z.
  destruct real_lt_zero_one as [eps [Heps [N HN]]].
  unfold real_lt.
  exists eps. split.
  - exact Heps.
  - exists N. intros n Hn.
    assert (Hpt : projT1 (real_plus real_one z) n - projT1 z n
                  == projT1 real_one n - projT1 real_zero n).
    { assert (Hp : projT1 (real_plus real_one z) n == projT1 real_one n + projT1 z n)
        by (apply real_plus_proj).
      assert (H1v : projT1 real_one n == 1%Q) by reflexivity.
      assert (H0v : projT1 real_zero n == 0%Q) by reflexivity.
      rewrite Hp, H1v, H0v. field.
    }
    assert (Hcmp : Qcompare eps (projT1 (real_plus real_one z) n - projT1 z n)
                 = Qcompare eps (projT1 real_one n - projT1 real_zero n)).
    { apply (Qcompare_comp eps eps (Qeq_refl eps)). exact Hpt. }
    unfold QltT, Qlt_bool. rewrite Hcmp. exact (HN n Hn).
Qed.

(* ---------- 序运输 ---------- *)

(* 相等换左端 *)
Lemma mte_le_congr : forall a b c : Real,
  real_eq a b -> real_le a c -> real_le b c.
Proof.
  intros a b c Heq Hle.
  unfold real_le in Hle.
  destruct Hle as [Hlt | Heqc].
  - left. exact (real_eq_lt_lt b a c (real_eq_sym a b Heq) Hlt).
  - right. exact (real_eq_trans b a c (real_eq_sym a b Heq) Heqc).
Qed.

(* 相等换左端（反方向）：a == b ⟹ b ≤ c ⟹ a ≤ c *)
Lemma mte_le_congr_l : forall a b c : Real,
  real_eq a b -> real_le b c -> real_le a c.
Proof.
  intros a b c Heq Hle.
  unfold real_le in Hle.
  destruct Hle as [Hlt | Heqc].
  - left. exact (real_eq_lt_lt a b c Heq Hlt).
  - right. exact (real_eq_trans a b c Heq Heqc).
Qed.

(* 相等换右端 *)
Lemma mte_le_congr_r : forall a b c : Real,
  real_le a b -> real_eq b c -> real_le a c.
Proof.
  intros a b c Hle Heq.
  unfold real_le in Hle.
  destruct Hle as [Hlt | Heqb].
  - left. exact (real_lt_eq_lt a b c Hlt Heq).
  - right. exact (real_eq_trans a b c Heqb Heq).
Qed.

(* 严格+弱 传递拼接 *)
Lemma mte_lt_le_trans : forall a b c : Real,
  real_lt a b -> real_le b c -> real_lt a c.
Proof.
  intros a b c Hlt Hle.
  unfold real_le in Hle.
  destruct Hle as [Hlt2 | Heq2].
  - exact (real_lt_trans a b c Hlt Hlt2).
  - exact (real_lt_eq_lt a b c Hlt Heq2).
Qed.

(* 严格左加法：u < v ⟹ w+u < w+v *)
Lemma mte_lt_plus_l : forall u v w : Real,
  real_lt u v -> real_lt (real_plus w u) (real_plus w v).
Proof.
  intros u v w Huv.
  apply (real_eq_lt_lt (real_plus w u) (real_plus u w) (real_plus w v)).
  - exact (real_plus_comm w u).
  - exact (real_lt_eq_lt (real_plus u w) (real_plus v w) (real_plus w v)
             (mte_lt_plus_r u v w Huv) (real_plus_comm v w)).
Qed.

(* ≤ 加法双兼容 *)
Lemma mte_le_plus_compat : forall a b c d : Real,
  real_le a b -> real_le c d -> real_le (real_plus a c) (real_plus b d).
Proof.
  intros a b c d Hle1 Hle2.
  unfold real_le in Hle1, Hle2.
  destruct Hle1 as [Hlt1 | Heq1]; destruct Hle2 as [Hlt2 | Heq2].
  - left. exact (real_lt_plus_compat a b c d Hlt1 Hlt2).
  - left. exact (real_lt_eq_lt (real_plus a c) (real_plus b c) (real_plus b d)
                   (mte_lt_plus_r a b c Hlt1)
                   (RealSetoid.real_eq_plus_compat b c b d (real_eq_refl b) Heq2)).
  - left. exact (real_eq_lt_lt (real_plus a c) (real_plus b c) (real_plus b d)
                   (RealSetoid.real_eq_plus_compat a c b c Heq1 (real_eq_refl c))
                   (mte_lt_plus_l c d b Hlt2)).
  - right. exact (RealSetoid.real_eq_plus_compat a c b d Heq1 Heq2).
Qed.

(* ≤ 乘法右兼容 *)
Lemma mte_le_mult_compat_r : forall a b c : Real,
  real_le a b -> real_lt real_zero c -> real_le (real_mult a c) (real_mult b c).
Proof.
  intros a b c Hle Hc.
  unfold real_le in Hle.
  destruct Hle as [Hlt | Heq].
  - left. exact (real_mult_lt_compat a b c Hlt Hc).
  - right. exact (RealSetoid.real_eq_mult_compat a c b c Heq (real_eq_refl c)).
Qed.

(* ---------- nat 嵌入的正性 ---------- *)

(* n·z ≥ 零（z > 零 严格前提） *)
Lemma mte_nat_mult_pos : forall (n : nat) (z : Real),
  real_lt real_zero z -> real_le real_zero (real_mult (mte_nat_to_R n) z).
Proof.
  intros n z Hz.
  induction n as [| n IH].
  - right.
    exact (real_eq_sym _ _
             (real_eq_trans (real_mult (mte_nat_to_R 0) z)
                            (real_mult z (mte_nat_to_R 0)) real_zero
                 (real_mult_comm (mte_nat_to_R 0) z) (real_mult_zero z))).
  - assert (E : real_eq (real_mult (mte_nat_to_R (Datatypes.S n)) z)
                        (real_plus (real_mult (mte_nat_to_R n) z) z)).
    { apply (real_eq_trans _ (real_mult z (real_plus real_one (mte_nat_to_R n)))).
      - exact (real_mult_comm (real_plus real_one (mte_nat_to_R n)) z).
      - apply (real_eq_trans _
                 (real_plus (real_mult z real_one) (real_mult z (mte_nat_to_R n)))).
        + exact (real_distrib z real_one (mte_nat_to_R n)).
        + apply (real_eq_trans _ (real_plus z (real_mult z (mte_nat_to_R n)))).
          * exact (RealSetoid.real_eq_plus_compat (real_mult z real_one)
                     (real_mult z (mte_nat_to_R n))
                     z (real_mult z (mte_nat_to_R n))
                     (real_mult_one z)
                     (real_eq_refl (real_mult z (mte_nat_to_R n)))).
          * exact (real_eq_trans (real_plus z (real_mult z (mte_nat_to_R n)))
                     (real_plus (real_mult z (mte_nat_to_R n)) z)
                     (real_plus (real_mult (mte_nat_to_R n) z) z)
                     (real_plus_comm z (real_mult z (mte_nat_to_R n)))
                     (RealSetoid.real_eq_plus_compat (real_mult z (mte_nat_to_R n)) z
                        (real_mult (mte_nat_to_R n) z) z
                        (real_mult_comm z (mte_nat_to_R n)) (real_eq_refl z))).
    }
    unfold real_le in IH.
    destruct IH as [HltI | HeqI].
    + left.
      apply (real_lt_eq_lt real_zero (real_plus z (real_mult (mte_nat_to_R n) z))
               (real_mult (mte_nat_to_R (Datatypes.S n)) z)).
      * exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                 (real_plus z (real_mult (mte_nat_to_R n) z))
                 (real_eq_sym (real_plus real_zero real_zero) real_zero
                    (real_plus_zero real_zero))
                 (real_lt_plus_compat real_zero z real_zero
                    (real_mult (mte_nat_to_R n) z) Hz HltI)).
      * exact (real_eq_trans (real_plus z (real_mult (mte_nat_to_R n) z))
                 (real_plus (real_mult (mte_nat_to_R n) z) z)
                 (real_mult (mte_nat_to_R (Datatypes.S n)) z)
                 (real_plus_comm z (real_mult (mte_nat_to_R n) z))
                 (real_eq_sym _ _ E)).
    + left.
      apply (real_lt_eq_lt real_zero z (real_mult (mte_nat_to_R (Datatypes.S n)) z) Hz).
      * apply (real_eq_trans z (real_plus z real_zero)).
        -- exact (real_eq_sym (real_plus z real_zero) z (real_plus_zero z)).
        -- apply (real_eq_trans _ (real_plus z (real_mult (mte_nat_to_R n) z))).
           ++ exact (RealSetoid.real_eq_plus_compat z real_zero z
                        (real_mult (mte_nat_to_R n) z)
                        (real_eq_refl z) HeqI).
           ++ apply (real_eq_trans _
                        (real_plus (real_mult (mte_nat_to_R n) z) z)).
              ** exact (real_plus_comm z (real_mult (mte_nat_to_R n) z)).
              ** exact (real_eq_sym _ _ E).
Qed.

(* 后继嵌入严格正 *)
Lemma mte_nat_to_R_S_pos : forall n : nat,
  real_lt real_zero (mte_nat_to_R (Datatypes.S n)).
Proof.
  intro n.
  destruct (mte_nat_mult_pos n real_one real_lt_zero_one) as [HltH | HeqH].
  - assert (Hn : real_lt real_zero (mte_nat_to_R n))
      by (exact (real_lt_eq_lt real_zero (real_mult (mte_nat_to_R n) real_one)
                   (mte_nat_to_R n) HltH (real_mult_one (mte_nat_to_R n)))).
    exact (real_plus_positive real_one (mte_nat_to_R n) real_lt_zero_one Hn).
  - apply (real_lt_eq_lt real_zero real_one).
    + exact real_lt_zero_one.
    + apply (real_eq_trans _ (real_plus real_one real_zero)).
      * exact (real_eq_sym (real_plus real_one real_zero) real_one (real_plus_zero real_one)).
      * exact (RealSetoid.real_eq_plus_compat real_one real_zero real_one
                 (mte_nat_to_R n)
                 (real_eq_refl real_one)
                 (real_eq_sym (mte_nat_to_R n) real_zero
                    (real_eq_trans (mte_nat_to_R n)
                       (real_mult (mte_nat_to_R n) real_one) real_zero
                       (real_eq_sym _ _ (real_mult_one (mte_nat_to_R n)))
                       (real_eq_sym _ _ HeqH)))).
Qed.

(* ---------- 常量桥（real_const ↔ mte_nat_to_R） ---------- *)

(* Q 相等换实常量相等 *)
Lemma mte_const_ext : forall c d : Q, c == d -> real_eq (real_const c) (real_const d).
Proof.
  intros c d Hcd. apply real_eq_of_zero_diff. intro k.
  assert (H1 : projT1 (real_const c) k == c) by (unfold real_const; reflexivity).
  assert (H2 : projT1 (real_const d) k == d) by (unfold real_const; reflexivity).
  rewrite H1, H2.
  destruct c as [a ca]; destruct d as [b cb].
  unfold Qeq in Hcd. simpl in Hcd.
  unfold Qminus, Qeq. simpl.
  rewrite Hcd. ring.
Qed.

(* 实常量加法同态 *)
Lemma mte_const_plus : forall c d : Q,
  real_eq (real_plus (real_const c) (real_const d)) (real_const (c + d)%Q).
Proof.
  intros c d. apply real_eq_of_zero_diff. intro k.
  assert (H1 : projT1 (real_plus (real_const c) (real_const d)) k
               == projT1 (real_const c) k + projT1 (real_const d) k)
    by (apply real_plus_proj).
  rewrite H1.
  assert (H2 : projT1 (real_const c) k == c) by (unfold real_const; reflexivity).
  assert (H3 : projT1 (real_const d) k == d) by (unfold real_const; reflexivity).
  assert (H4 : projT1 (real_const (c + d)%Q) k == (c + d)%Q)
    by (unfold real_const; reflexivity).
  rewrite H2, H3, H4. field.
Qed.

(* nat 嵌入 == 常量嵌入（供 real_arch 调用） *)
Lemma mte_nat_const_eq : forall n : nat,
  real_eq (mte_nat_to_R n) (real_const (Z.of_nat n # 1)%Q).
Proof.
  intro n. induction n as [| n IH].
  - apply real_eq_of_zero_diff. intro k.
    assert (H1 : projT1 (mte_nat_to_R 0) k == 0%Q) by reflexivity.
    assert (H2 : projT1 (real_const (Z.of_nat 0 # 1)%Q) k == (Z.of_nat 0 # 1)%Q)
      by (unfold real_const; reflexivity).
    rewrite H1, H2.
    assert (Hz : Z.of_nat 0 = 0%Z) by reflexivity.
    rewrite Hz. field.
  - assert (Hzs : Z.of_nat (Datatypes.S n) = Z.succ (Z.of_nat n))
      by apply Znat.Nat2Z.inj_succ.
    assert (Hzq : (Z.of_nat (Datatypes.S n) # 1)%Q == (1 + (Z.of_nat n # 1))%Q).
    { unfold Qeq. rewrite Hzs. cbn [Qnum Qden Qplus].
      rewrite !Z.mul_1_r. symmetry. apply Z.add_1_l. }
    apply (real_eq_trans _ (real_plus real_one (real_const (Z.of_nat n # 1)%Q))).
    + exact (RealSetoid.real_eq_plus_compat real_one (mte_nat_to_R n) real_one
               (real_const (Z.of_nat n # 1)%Q)
               (real_eq_refl real_one) IH).
    + apply (real_eq_trans _ (real_const (1 + (Z.of_nat n # 1))%Q)).
      * apply (real_eq_trans _
                 (real_plus (real_const (1#1)%Q) (real_const (Z.of_nat n # 1)%Q))).
        -- apply (RealSetoid.real_eq_plus_compat real_one
                       (real_const (Z.of_nat n # 1)%Q)
                       (real_const (1#1)%Q) (real_const (Z.of_nat n # 1)%Q)).
           ++ apply real_eq_of_zero_diff. intro k.
              assert (Ha : projT1 (real_const (1#1)%Q) k == (1#1)%Q)
                by (unfold real_const; reflexivity).
              assert (Hb1 : projT1 real_one k == 1%Q) by reflexivity.
              rewrite Ha, Hb1. field.
           ++ exact (real_eq_refl (real_const (Z.of_nat n # 1)%Q)).
        -- exact (mte_const_plus (1#1)%Q (Z.of_nat n # 1)%Q).
      * apply (mte_const_ext (1 + (Z.of_nat n # 1))%Q
                 (Z.of_nat (Datatypes.S n) # 1)%Q).
        exact (Qeq_sym _ _ Hzq).
Qed.

(* ---------- 幂的基本性 ---------- *)

Lemma mte_rpow_pos : forall (b : Real) (n : nat),
  real_lt real_zero b -> real_lt real_zero (mte_rpow b n).
Proof.
  intros b n Hb. induction n as [| n IH].
  - exact real_lt_zero_one.
  - exact (real_mult_pos_compat b (mte_rpow b n) Hb IH).
Qed.

(* 底 > 壹 ⟹ 幂逐步严格增 *)
Lemma mte_rpow_step_lt : forall (b : Real) (n : nat),
  real_lt real_one b -> real_lt (mte_rpow b n) (mte_rpow b (Datatypes.S n)).
Proof.
  intros b n Hb.
  assert (Hbp : real_lt real_zero b)
    by (exact (real_lt_trans real_zero real_one b real_lt_zero_one Hb)).
  assert (Hstep : real_lt (real_mult (mte_rpow b n) real_one)
                          (real_mult (mte_rpow b n) b)).
  { exact (real_mult_lt_compat_l real_one b (mte_rpow b n) Hb
             (mte_rpow_pos b n Hbp)). }
  apply (real_lt_eq_lt _ (real_mult (mte_rpow b n) b)).
  - exact (real_eq_lt_lt (mte_rpow b n) (real_mult (mte_rpow b n) real_one)
             (real_mult (mte_rpow b n) b)
             (real_eq_sym (real_mult (mte_rpow b n) real_one) (mte_rpow b n)
                (real_mult_one (mte_rpow b n))) Hstep).
  - exact (real_mult_comm (mte_rpow b n) b).
Qed.

(* 底 > 壹 ⟹ m 处幂 < m+S d 处幂 *)
Lemma mte_rpow_mono_add : forall (b : Real) (m d : nat),
  real_lt real_one b -> real_lt (mte_rpow b m) (mte_rpow b (m + Datatypes.S d)).
Proof.
  intros b m d Hb.
  induction d as [| d IH].
  - rewrite (Nat.add_succ_r m 0%nat). rewrite (Nat.add_0_r m).
    exact (mte_rpow_step_lt b m Hb).
  - rewrite (Nat.add_succ_r m (Datatypes.S d)).
    exact (real_lt_trans (mte_rpow b m) (mte_rpow b (m + Datatypes.S d))
             (mte_rpow b (Datatypes.S (m + Datatypes.S d))) IH
             (mte_rpow_step_lt b (m + Datatypes.S d) Hb)).
Qed.

(* 底相等换幂相等 *)
Lemma mte_rpow_ext : forall (a b : Real) (n : nat),
  real_eq a b -> real_eq (mte_rpow a n) (mte_rpow b n).
Proof.
  intros a b n Heq. induction n as [| n IH].
  - exact (real_eq_refl real_one).
  - exact (RealSetoid.real_eq_mult_compat a (mte_rpow a n) b (mte_rpow b n) Heq IH).
Qed.

(* ---------- 伯努利型下界：(壹+h)^n ≥ 壹 + n·h ---------- *)

Lemma mte_pow_ge : forall (h : Real) (n : nat),
  real_lt real_zero h ->
  real_le (real_plus real_one (real_mult (mte_nat_to_R n) h))
          (mte_rpow (real_plus real_one h) n).
Proof.
  intros h n Hh. induction n as [| n IH].
  - right.
    apply (real_eq_trans _ (real_plus real_one real_zero)).
    + exact (RealSetoid.real_eq_plus_compat real_one
               (real_mult (mte_nat_to_R 0) h) real_one real_zero
               (real_eq_refl real_one)
               (real_eq_trans (real_mult (mte_nat_to_R 0) h)
                  (real_mult h (mte_nat_to_R 0)) real_zero
                  (real_mult_comm (mte_nat_to_R 0) h) (real_mult_zero h))).
    + exact (real_plus_zero real_one).
  - (* 归纳步：(壹+n̄h)(壹+h) = 壹+n̄h+h+n̄(hh) ≥ 壹+n̄h+h = 壹+(S n)·h *)
    assert (H1h : real_lt real_zero (real_plus real_one h))
      by (exact (real_plus_positive real_one h real_lt_zero_one Hh)).
    assert (Hsq : real_le real_zero (real_mult (mte_nat_to_R n) (real_mult h h)))
      by (exact (mte_nat_mult_pos n (real_mult h h) (real_mult_pos_compat h h Hh Hh))).
    assert (Eshift : real_eq (real_mult (mte_nat_to_R (Datatypes.S n)) h)
                             (real_plus (real_mult (mte_nat_to_R n) h) h)).
    { apply (real_eq_trans _ (real_mult h (real_plus real_one (mte_nat_to_R n)))).
      - exact (real_mult_comm (real_plus real_one (mte_nat_to_R n)) h).
      - apply (real_eq_trans _
                 (real_plus (real_mult h real_one) (real_mult h (mte_nat_to_R n)))).
        + exact (real_distrib h real_one (mte_nat_to_R n)).
        + apply (real_eq_trans _ (real_plus h (real_mult h (mte_nat_to_R n)))).
          * exact (RealSetoid.real_eq_plus_compat (real_mult h real_one)
                     (real_mult h (mte_nat_to_R n))
                     h (real_mult h (mte_nat_to_R n))
                     (real_mult_one h)
                     (real_eq_refl (real_mult h (mte_nat_to_R n)))).
          * exact (real_eq_trans (real_plus h (real_mult h (mte_nat_to_R n)))
                     (real_plus h (real_mult (mte_nat_to_R n) h))
                     (real_plus (real_mult (mte_nat_to_R n) h) h)
                     (RealSetoid.real_eq_plus_compat h (real_mult h (mte_nat_to_R n))
                        h (real_mult (mte_nat_to_R n) h)
                        (real_eq_refl h) (real_mult_comm h (mte_nat_to_R n)))
                     (real_plus_comm h (real_mult (mte_nat_to_R n) h))).
    }
    (* 展开恒等：L == (壹+n̄h) + (h + n̄·(h·h))，其中 L = (壹+n̄h)·(壹+h) *)
    assert (HAh : real_eq (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h)) h)
                          (real_plus h (real_mult (mte_nat_to_R n) (real_mult h h)))).
    { apply (real_eq_trans _ (real_mult h (real_plus real_one (real_mult (mte_nat_to_R n) h)))).
      - exact (real_mult_comm (real_plus real_one (real_mult (mte_nat_to_R n) h)) h).
      - apply (real_eq_trans _
                 (real_plus (real_mult h real_one)
                            (real_mult h (real_mult (mte_nat_to_R n) h)))).
        + exact (real_distrib h real_one (real_mult (mte_nat_to_R n) h)).
        + exact (RealSetoid.real_eq_plus_compat (real_mult h real_one)
                   (real_mult h (real_mult (mte_nat_to_R n) h))
                   h (real_mult (mte_nat_to_R n) (real_mult h h))
                   (real_mult_one h)
                   (real_eq_trans (real_mult h (real_mult (mte_nat_to_R n) h))
                      (real_mult (real_mult (mte_nat_to_R n) h) h)
                      (real_mult (mte_nat_to_R n) (real_mult h h))
                      (real_mult_comm h (real_mult (mte_nat_to_R n) h))
                      (real_eq_sym _ _ (real_mult_assoc (mte_nat_to_R n) h h)))).
    }
    assert (EL : real_eq (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h))
                                    (real_plus real_one h))
                         (real_plus (real_plus real_one (real_mult (mte_nat_to_R n) h))
                                    (real_plus h
                                       (real_mult (mte_nat_to_R n) (real_mult h h))))).
    { apply (real_eq_trans _
               (real_plus (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h)) real_one)
                          (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h)) h))).
      - exact (real_distrib (real_plus real_one (real_mult (mte_nat_to_R n) h))
                 real_one h).
      - apply (real_eq_trans _
                 (real_plus (real_plus real_one (real_mult (mte_nat_to_R n) h))
                            (real_plus h (real_mult (mte_nat_to_R n) (real_mult h h))))).
        + exact (RealSetoid.real_eq_plus_compat
                    (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h)) real_one)
                    (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h)) h)
                    (real_plus real_one (real_mult (mte_nat_to_R n) h))
                    (real_plus h (real_mult (mte_nat_to_R n) (real_mult h h)))
                    (real_mult_one (real_plus real_one (real_mult (mte_nat_to_R n) h)))
                    HAh).
        + exact (real_eq_refl
                    (real_plus (real_plus real_one (real_mult (mte_nat_to_R n) h))
                               (real_plus h
                                          (real_mult (mte_nat_to_R n) (real_mult h h))))).
    }
    (* 目标换形：壹+(S n)·h == (壹+n̄h)+h *)
    assert (E5 : real_eq (real_plus real_one
                            (real_mult (mte_nat_to_R (Datatypes.S n)) h))
                         (real_plus (real_plus real_one (real_mult (mte_nat_to_R n) h)) h)).
    { apply (real_eq_trans _
               (real_plus real_one
                  (real_plus (real_mult (mte_nat_to_R n) h) h))).
      - exact (RealSetoid.real_eq_plus_compat real_one
                  (real_mult (mte_nat_to_R (Datatypes.S n)) h)
                  real_one (real_plus (real_mult (mte_nat_to_R n) h) h)
                  (real_eq_refl real_one) Eshift).
      - apply (real_eq_trans _
                 (real_plus real_one
                    (real_plus h (real_mult (mte_nat_to_R n) h)))).
        + apply (RealSetoid.real_eq_plus_compat real_one
                    (real_plus (real_mult (mte_nat_to_R n) h) h)
                    real_one (real_plus h (real_mult (mte_nat_to_R n) h))
                    (real_eq_refl real_one)
                    (real_plus_comm (real_mult (mte_nat_to_R n) h) h)).
        + apply (real_eq_trans _
                     (real_plus (real_plus real_one h)
                                (real_mult (mte_nat_to_R n) h))).
          * exact (real_plus_assoc real_one h (real_mult (mte_nat_to_R n) h)).
          * apply (real_eq_trans _
                       (real_plus (real_mult (mte_nat_to_R n) h)
                                  (real_plus real_one h))).
            -- exact (real_plus_comm (real_plus real_one h)
                        (real_mult (mte_nat_to_R n) h)).
            -- apply (real_eq_trans _
                         (real_plus (real_plus (real_mult (mte_nat_to_R n) h) real_one) h)).
               ++ exact (real_plus_assoc (real_mult (mte_nat_to_R n) h) real_one h).
               ++ exact (RealSetoid.real_eq_plus_compat
                            (real_plus (real_mult (mte_nat_to_R n) h) real_one)
                            h
                            (real_plus real_one (real_mult (mte_nat_to_R n) h))
                            h
                            (real_plus_comm (real_mult (mte_nat_to_R n) h) real_one)
                            (real_eq_refl h)).
    }
    assert (Hle_h : real_le h
                      (real_plus h (real_mult (mte_nat_to_R n) (real_mult h h)))).
    { apply (mte_le_congr (real_plus h real_zero) h).
      - exact (real_plus_zero h).
      - assert (Hhh : real_le h h).
        { right. exact (real_eq_refl h). }
        exact (mte_le_plus_compat h h real_zero
                 (real_mult (mte_nat_to_R n) (real_mult h h)) Hhh Hsq).
    }
    assert (Hle3 : real_le (real_plus (real_plus real_one (real_mult (mte_nat_to_R n) h)) h)
                           (real_plus (real_plus real_one (real_mult (mte_nat_to_R n) h))
                                      (real_plus h
                                         (real_mult (mte_nat_to_R n) (real_mult h h))))).
    { apply (mte_le_plus_compat
               (real_plus real_one (real_mult (mte_nat_to_R n) h))
               (real_plus real_one (real_mult (mte_nat_to_R n) h))
               h (real_plus h (real_mult (mte_nat_to_R n) (real_mult h h)))).
      - right. exact (real_eq_refl (real_plus real_one (real_mult (mte_nat_to_R n) h))).
      - exact Hle_h.
    }
    assert (Hle4 : real_le (real_plus (real_plus real_one (real_mult (mte_nat_to_R n) h)) h)
                           (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h))
                                      (real_plus real_one h))).
    { apply (mte_le_congr_r _ _ _ Hle3 (real_eq_sym _ _ EL)). }
    assert (Hle5 : real_le (real_plus real_one
                              (real_mult (mte_nat_to_R (Datatypes.S n)) h))
                           (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h))
                                      (real_plus real_one h))).
    { apply (mte_le_congr_l _ _ _ E5 Hle4). }
    exact (real_le_trans
             (real_plus real_one (real_mult (mte_nat_to_R (Datatypes.S n)) h))
             (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h))
                        (real_plus real_one h))
             (mte_rpow (real_plus real_one h) (Datatypes.S n))
             Hle5
             (mte_le_congr_r (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h))
                                (real_plus real_one h))
                (real_mult (mte_rpow (real_plus real_one h) n) (real_plus real_one h))
                (mte_rpow (real_plus real_one h) (Datatypes.S n))
                (mte_le_mult_compat_r (real_plus real_one (real_mult (mte_nat_to_R n) h))
                   (mte_rpow (real_plus real_one h) n)
                   (real_plus real_one h) IH H1h)
                (real_mult_comm (mte_rpow (real_plus real_one h) n)
                   (real_plus real_one h)))).

Qed.

(* ---------- 件②a：exp 的 nat 倍迭代 ---------- *)

Theorem mte_exp_pow_iter : forall (x : Real) (n : nat),
  real_eq (cauchy_real_exp (real_mult x (mte_nat_to_R n)))
          (mte_rpow (cauchy_real_exp x) n).
Proof.
  intros x n. induction n as [| n IH].
  - apply (real_eq_trans _ real_one).
    + apply (real_eq_trans _ (cauchy_real_exp real_zero)).
      * exact (cauchy_real_exp_wd _ _ (real_mult_zero x)).
      * exact cauchy_real_exp_zero.
    + exact (real_eq_refl real_one).
  - apply (real_eq_trans _
               (cauchy_real_exp (real_plus (real_mult x real_one)
                                           (real_mult x (mte_nat_to_R n))))).
    + exact (cauchy_real_exp_wd _ _ (real_distrib x real_one (mte_nat_to_R n))).
    + apply (real_eq_trans _
                 (cauchy_real_exp (real_plus x (real_mult x (mte_nat_to_R n))))).
      * apply (cauchy_real_exp_wd _ _).
        exact (RealSetoid.real_eq_plus_compat (real_mult x real_one)
                   (real_mult x (mte_nat_to_R n))
                   x (real_mult x (mte_nat_to_R n))
                   (real_mult_one x) (real_eq_refl (real_mult x (mte_nat_to_R n)))).
      * apply (real_eq_trans _
                   (real_mult (cauchy_real_exp x)
                              (cauchy_real_exp (real_mult x (mte_nat_to_R n))))).
        -- exact (cauchy_real_exp_plus x (real_mult x (mte_nat_to_R n))).
        -- apply (real_eq_trans _
                       (real_mult (cauchy_real_exp x)
                                  (mte_rpow (cauchy_real_exp x) n))).
           ++ exact (RealSetoid.real_eq_mult_compat (cauchy_real_exp x)
                        (cauchy_real_exp (real_mult x (mte_nat_to_R n)))
                        (cauchy_real_exp x) (mte_rpow (cauchy_real_exp x) n)
                        (real_eq_refl (cauchy_real_exp x)) IH).
           ++ exact (real_eq_refl
                        (real_mult (cauchy_real_exp x)
                                   (mte_rpow (cauchy_real_exp x) n))).
Qed.

(* ---------- 件①：1/T 发散见证 ---------- *)

Theorem mte_inv_divergence : forall delta : Real,
  real_lt real_zero delta ->
  forall M : nat,
  sigT (fun T0 => And (real_lt real_zero T0)
         (forall T : Real, real_lt real_zero T -> real_lt T T0 ->
            real_lt (real_mult (mte_nat_to_R M) T) delta)).
Proof.
  intros delta Hdelta M.
  destruct M as [| M].
  - exists (real_mult delta (real_inv_pos (mte_nat_to_R 1) (mte_nat_to_R_S_pos 0))).
    split.
    + exact (real_mult_pos_compat delta
                (real_inv_pos (mte_nat_to_R 1) (mte_nat_to_R_S_pos 0))
                Hdelta (real_inv_pos_pos (mte_nat_to_R 1) (mte_nat_to_R_S_pos 0))).
    + intros T HTpos HTlt.
      apply (real_eq_lt_lt (real_mult (mte_nat_to_R 0) T) real_zero delta).
      * exact (real_eq_trans (real_mult (mte_nat_to_R 0) T)
                 (real_mult T (mte_nat_to_R 0)) real_zero
                 (real_mult_comm (mte_nat_to_R 0) T) (real_mult_zero T)).
      * exact Hdelta.
  - assert (HMpos : real_lt real_zero (mte_nat_to_R (Datatypes.S M)))
      by (exact (mte_nat_to_R_S_pos M)).
    assert (Hinvpos : real_lt real_zero
                        (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos))
      by (exact (real_inv_pos_pos (mte_nat_to_R (Datatypes.S M)) HMpos)).
    exists (real_mult delta (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)).
    split.
    + exact (real_mult_pos_compat delta
                (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)
                Hdelta Hinvpos).
    + intros T HTpos HTlt.
      assert (H1 : real_lt (real_mult (mte_nat_to_R (Datatypes.S M)) T)
                           (real_mult (mte_nat_to_R (Datatypes.S M))
                                      (real_mult delta
                                                 (real_inv_pos
                                                    (mte_nat_to_R (Datatypes.S M))
                                                    HMpos)))).
      { exact (real_mult_lt_compat_l T
                  (real_mult delta (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos))
                  (mte_nat_to_R (Datatypes.S M)) HTlt HMpos). }
      assert (E2 : real_eq (real_mult (mte_nat_to_R (Datatypes.S M))
                                      (real_mult delta
                                                 (real_inv_pos
                                                    (mte_nat_to_R (Datatypes.S M))
                                                    HMpos)))
                           (real_mult delta
                                      (real_mult (mte_nat_to_R (Datatypes.S M))
                                                 (real_inv_pos
                                                    (mte_nat_to_R (Datatypes.S M))
                                                    HMpos)))).
      { apply (real_eq_trans _
                   (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) delta)
                              (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos))).
        - exact (real_mult_assoc (mte_nat_to_R (Datatypes.S M)) delta
                    (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)).
        - exact (real_eq_trans
                    (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) delta)
                               (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos))
                    (real_mult (real_mult delta (mte_nat_to_R (Datatypes.S M)))
                               (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos))
                    (real_mult delta
                               (real_mult (mte_nat_to_R (Datatypes.S M))
                                          (real_inv_pos (mte_nat_to_R (Datatypes.S M))
                                                        HMpos)))
                    (RealSetoid.real_eq_mult_compat
                       (real_mult (mte_nat_to_R (Datatypes.S M)) delta)
                       (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)
                       (real_mult delta (mte_nat_to_R (Datatypes.S M)))
                       (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)
                       (real_mult_comm (mte_nat_to_R (Datatypes.S M)) delta)
                       (real_eq_refl (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)))
                    (real_eq_sym _ _
                       (real_mult_assoc delta (mte_nat_to_R (Datatypes.S M))
                          (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)))).
      }
      assert (E3 : real_eq (real_mult (mte_nat_to_R (Datatypes.S M))
                                      (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos))
                           real_one)
        by (exact (real_inv_pos_correct (mte_nat_to_R (Datatypes.S M)) HMpos)).
      assert (Edelta : real_eq (real_mult (mte_nat_to_R (Datatypes.S M))
                                          (real_mult delta
                                                     (real_inv_pos (mte_nat_to_R (Datatypes.S M))
                                                                  HMpos)))
                               delta).
      { apply (real_eq_trans _
                   (real_mult delta
                              (real_mult (mte_nat_to_R (Datatypes.S M))
                                         (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)))).
        - exact E2.
        - apply (real_eq_trans _ (real_mult delta real_one)).
          + exact (RealSetoid.real_eq_mult_compat delta
                       (real_mult (mte_nat_to_R (Datatypes.S M))
                                  (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos))
                       delta real_one (real_eq_refl delta) E3).
          + exact (real_mult_one delta).
      }
      exact (real_lt_eq_lt (real_mult (mte_nat_to_R (Datatypes.S M)) T)
               (real_mult (mte_nat_to_R (Datatypes.S M))
                          (real_mult delta
                                     (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)))
               delta H1 Edelta).
Qed.

(* ---------- 件②b：exp 正向发散下界 ---------- *)

Theorem mte_exp_divergence : forall x : Real,
  real_lt real_zero x ->
  forall M : nat,
  sigT (fun N => forall n : nat, Nat.le N n ->
    real_lt (mte_nat_to_R M) (mte_rpow (cauchy_real_exp x) n)).
Proof.
  intros x Hx M.
  assert (Hb : real_lt real_one (cauchy_real_exp x))
    by (exact (cauchy_real_exp_gt_one x Hx)).
  set (h := real_plus (cauchy_real_exp x) (real_opp real_one)).
  assert (Hh : real_lt real_zero h)
    by (exact (cauchy_real_exp_minus_one_pos x Hx)).
  assert (Hinv : real_lt real_zero (real_inv_pos h Hh))
    by (exact (real_inv_pos_pos h Hh)).
  assert (Eexp : real_eq (cauchy_real_exp x) (real_plus real_one h)).
  { assert (Hneg : real_eq (real_plus (real_opp real_one) real_one) real_zero)
      by (exact (real_eq_trans (real_plus (real_opp real_one) real_one)
                  (real_plus real_one (real_opp real_one)) real_zero
                  (real_plus_comm (real_opp real_one) real_one)
                  (real_plus_opp real_one))).
    apply (real_eq_sym (real_plus real_one h) (cauchy_real_exp x)).
    apply (real_eq_trans _
               (real_plus (real_plus (cauchy_real_exp x) (real_opp real_one)) real_one)).
    - apply (real_eq_trans _ (real_plus h real_one)).
      + exact (real_plus_comm real_one h).
      + exact (real_eq_refl (real_plus h real_one)).
    - apply (real_eq_trans _
                 (real_plus (cauchy_real_exp x)
                            (real_plus (real_opp real_one) real_one))).
      + exact (real_eq_sym _
                   (real_plus (real_plus (cauchy_real_exp x) (real_opp real_one))
                              real_one)
                   (real_plus_assoc (cauchy_real_exp x) (real_opp real_one) real_one)).
      + apply (real_eq_trans _ (real_plus (cauchy_real_exp x) real_zero)).
        * exact (RealSetoid.real_eq_plus_compat (cauchy_real_exp x)
                     (real_plus (real_opp real_one) real_one)
                     (cauchy_real_exp x) real_zero
                     (real_eq_refl (cauchy_real_exp x)) Hneg).
        * exact (real_plus_zero (cauchy_real_exp x)).
  }
  assert (Hbp : real_lt real_zero (cauchy_real_exp x))
    by (exact (real_lt_trans real_zero real_one (cauchy_real_exp x)
                 real_lt_zero_one Hb)).
  destruct (real_arch (real_mult (mte_nat_to_R M) (real_inv_pos h Hh)))
    as [n0 [Hn2 HBlt]].
  assert (Einv : real_eq (real_mult (real_mult (mte_nat_to_R M) (real_inv_pos h Hh)) h)
                         (mte_nat_to_R M)).
  { apply (real_eq_trans _
               (real_mult (mte_nat_to_R M) (real_mult (real_inv_pos h Hh) h))).
    - exact (real_eq_sym (real_mult (mte_nat_to_R M) (real_mult (real_inv_pos h Hh) h))
                   (real_mult (real_mult (mte_nat_to_R M) (real_inv_pos h Hh)) h)
                   (real_mult_assoc (mte_nat_to_R M) (real_inv_pos h Hh) h)).
    - apply (real_eq_trans _
                   (real_mult (mte_nat_to_R M) (real_mult h (real_inv_pos h Hh)))).
      + exact (RealSetoid.real_eq_mult_compat (mte_nat_to_R M)
                   (real_mult (real_inv_pos h Hh) h)
                   (mte_nat_to_R M) (real_mult h (real_inv_pos h Hh))
                   (real_eq_refl (mte_nat_to_R M)) (real_mult_comm (real_inv_pos h Hh) h)).
      + apply (real_eq_trans _ (real_mult (mte_nat_to_R M) real_one)).
        * exact (RealSetoid.real_eq_mult_compat (mte_nat_to_R M)
                     (real_mult h (real_inv_pos h Hh))
                     (mte_nat_to_R M) real_one
                     (real_eq_refl (mte_nat_to_R M)) (real_inv_pos_correct h Hh)).
        * exact (real_mult_one (mte_nat_to_R M)).
  }
  assert (H5 : real_lt (mte_nat_to_R M) (real_mult (mte_nat_to_R n0) h)).
  { apply (real_lt_eq_lt _ (real_mult (real_const (Z.of_nat n0 # 1)%Q) h)).
    - exact (real_eq_lt_lt (mte_nat_to_R M)
               (real_mult (real_mult (mte_nat_to_R M) (real_inv_pos h Hh)) h)
               (real_mult (real_const (Z.of_nat n0 # 1)%Q) h)
               (real_eq_sym _ _ Einv)
               (real_mult_lt_compat (real_mult (mte_nat_to_R M) (real_inv_pos h Hh))
                  (real_const (Z.of_nat n0 # 1)%Q) h HBlt Hh)).
    - exact (RealSetoid.real_eq_mult_compat (real_const (Z.of_nat n0 # 1)%Q) h
                 (mte_nat_to_R n0) h
                 (real_eq_sym _ _ (mte_nat_const_eq n0)) (real_eq_refl h)).
  }
  assert (Hpow : real_le (real_plus real_one (real_mult (mte_nat_to_R n0) h))
                         (mte_rpow (cauchy_real_exp x) n0)).
  { apply (mte_le_congr_r _ (mte_rpow (real_plus real_one h) n0)).
    - exact (mte_pow_ge h n0 Hh).
    - exact (mte_rpow_ext (real_plus real_one h) (cauchy_real_exp x) n0
               (real_eq_sym _ _ Eexp)).
  }
  assert (Hbase : real_lt (mte_nat_to_R M) (mte_rpow (cauchy_real_exp x) n0)).
  { apply (mte_lt_le_trans (mte_nat_to_R M)
               (real_plus real_one (real_mult (mte_nat_to_R n0) h))).
    - exact (real_lt_trans (mte_nat_to_R M) (real_mult (mte_nat_to_R n0) h)
               (real_plus real_one (real_mult (mte_nat_to_R n0) h)) H5
               (mte_lt_plus_one (real_mult (mte_nat_to_R n0) h))).
    - exact Hpow.
  }
  exists n0. intros n Hn.
  destruct (Nat.eq_dec n n0) as [Heq | Hne].
  - rewrite Heq. exact Hbase.
  - assert (Hgt : (n = n0 + Datatypes.S (n - Datatypes.S n0))%nat).
    { (* 差量分解：由 Nat.sub_add 得 n = (n−n₀)+n₀（E1）；
         又 n≠n₀，故 n−n₀>0，立 S(n−S n₀)=n−n₀（E2，零支经 E1 导 n=n₀ 反设）；
         E3 以 E2 与加法交换律桥接，与 E1 级联得分解式 *)
      assert (E1 : (n = (n - n0) + n0)%nat)
        by (symmetry; apply Nat.sub_add; exact Hn).
      assert (E2 : Datatypes.S (n - Datatypes.S n0) = (n - n0)%nat).
      { rewrite Nat.sub_succ_r. destruct ((n - n0)%nat) as [| q] eqn:Hq.
        - exfalso.
          assert (Hnn0 : n = n0) by (rewrite E1; reflexivity).
          exact (Hne Hnn0).
        - reflexivity. }
      assert (E3 : (n0 + Datatypes.S (n - Datatypes.S n0))%nat =
                   ((n - n0) + n0)%nat).
      { rewrite (Nat.add_comm n0 (Datatypes.S (n - Datatypes.S n0))),
                E2. reflexivity. }
      exact (eq_trans E1 (eq_sym E3)). }
    rewrite Hgt.
    exact (real_lt_trans (mte_nat_to_R M) (mte_rpow (cauchy_real_exp x) n0)
             (mte_rpow (cauchy_real_exp x)
                (n0 + Datatypes.S (n - Datatypes.S n0)))
             Hbase (mte_rpow_mono_add (cauchy_real_exp x) n0
                      (n - Datatypes.S n0) Hb)).
Qed.

(* ---------- 假设审计：全件零公理 ---------- *)
Print Assumptions mte_lt_plus_r.
Print Assumptions mte_lt_plus_one.
Print Assumptions mte_le_congr.
Print Assumptions mte_le_congr_r.
Print Assumptions mte_lt_le_trans.
Print Assumptions mte_le_plus_compat.
Print Assumptions mte_le_mult_compat_r.
Print Assumptions mte_nat_mult_pos.
Print Assumptions mte_nat_to_R_S_pos.
Print Assumptions mte_const_ext.
Print Assumptions mte_const_plus.
Print Assumptions mte_nat_const_eq.
Print Assumptions mte_rpow_pos.
Print Assumptions mte_rpow_step_lt.
Print Assumptions mte_rpow_mono_add.
Print Assumptions mte_rpow_ext.
Print Assumptions mte_pow_ge.
Print Assumptions mte_exp_pow_iter.
Print Assumptions mte_inv_divergence.
Print Assumptions mte_exp_divergence.

(* ============================ §16 率代数接口 rap_alg（Record 六字段：率列/预算/可判定测试/单调递减操作化/过站窗存在/语义桥）与主定理 rap_k_select（封装到 ============================ *)
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
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
Require Import UpReqIterGeomRate.
Require Import UpReqMixLogB.
Require Import UpTVDoeblin.
Require Import UpReqMixingTime.

(* ============================================================ *)
(* §1 率代数接口（件①）——可算法化率形的充分条件刻画                        *)
(* ============================================================ *)

Record rap_alg : Type := mk_rap_alg {
  rap_rate   : nat -> Real;
  rap_budget : Real;
  rap_test   : nat -> bool;
  rap_mono   : mixb_mono rap_test;
  rap_pass   : sigT (fun k : nat => rap_test k = true);
  rap_bridge : forall n : nat,
                 rap_test n = true -> real_lt (rap_rate n) rap_budget
}.

(* ============================================================ *)
(* §2 搜索辅助引理与主定理（件②）                                          *)
(* ============================================================ *)

(* bool 同站真假矛盾辅助引理（窗站穷尽矛盾情形用）                          *)
Lemma rap_bool_contra : forall b : bool, b = true -> b = false -> False.
Proof.
  intros b H1 H2. rewrite H1 in H2. discriminate H2.
Qed.

(* 辅助引理：双相 fuel 给定下 mixb_sel 的输出站必过测试                     *)
(*（mixb_sel_scale 第一合取支的 Set 面出口——Prop 只以引理应用形态       *)
(*  进 Defined 体，零 Prop 消去） *)
Lemma rap_sel_true : forall (test : nat -> bool) (K k r c : nat),
  mixb_mono test -> test 0%nat = false -> test k = true ->
  (forall j : nat, (j < k)%nat -> test j = false) ->
  (1 <= k)%nat -> (k <= K)%nat -> (2 <= K)%nat ->
  mixb_sel test (Datatypes.S (Datatypes.S (Nat.log2 K)))
           (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r, c) ->
  test r = true.
Proof.
  intros test K k r c Hm H0 Htk Hmin H1 HK HK2 Hsel.
  destruct (mixb_sel_scale test K k r c Hm H0 Htk Hmin H1 HK HK2 Hsel)
    as [Hrk _].
  rewrite Hrk. exact Htk.
Qed.

(* 主定理：凡入封装率形皆可预算驱动返回步数（最小过站，对数测试）           *)
Definition rap_k_select (p : rap_alg) :
  sigT (fun k : nat => real_lt (rap_rate p k) (rap_budget p)).
Proof.
  destruct p as [rate budget test mono pass bridge].
  destruct (test 0%nat) eqn:E0.
  - (* 零站即过：k := 0 经桥一步闭合 *)
    exact (existT _ 0%nat (bridge 0%nat E0)).
  - (* 窗站 kw → 界 K := max(kw,2) → 最小站 kmin → 双相搜索 → 桥 *)
    destruct pass as [kw Hkw].
    destruct (igr_k_enum test kw) as [kmin|] eqn:Eenum.
    + pose proof (igr_k_enum_sound test kw kmin Eenum) as Hsnd.
      pose proof (igr_k_enum_min test kw kmin Eenum) as Hmin.
      pose proof (mixb_enum_le test kw kmin Eenum) as HminK.
      assert (H1 : (1 <= kmin)%nat).
      { destruct kmin as [| m]. exfalso. congruence. exact (le_n_S 0 m (le_0_n m)). }
      assert (HK : (kmin <= Nat.max kw 2)%nat)
        by (exact (Nat.le_trans kmin kw (Nat.max kw 2) HminK
                    (Nat.le_max_l kw 2))).
      assert (HK2 : (2 <= Nat.max kw 2)%nat) by (apply Nat.le_max_r).
      destruct (mixb_sel test
                  (Datatypes.S (Datatypes.S (Nat.log2 (Nat.max kw 2))))
                  (Datatypes.S (Datatypes.S (Nat.log2 (Nat.max kw 2)))))
        as [r c] eqn:Esel.
      exact (existT _ r
               (bridge r
                  (rap_sel_true test (Nat.max kw 2) kmin r c mono E0 Hsnd
                     Hmin H1 HK HK2 Esel))).
    + (* 无窗矛盾：kw ≤ kw 燃料下枚举必有站 *)
      exact (False_rect _
               (rap_bool_contra (test kw) Hkw
                  (igr_k_enum_none test kw Eenum kw (Nat.le_refl kw)))).
Defined.

(* _le 对偶（一步推得） *)
Definition rap_k_select_le (p : rap_alg) :
  sigT (fun k : nat => real_le (rap_rate p k) (rap_budget p)).
Proof.
  destruct (rap_k_select p) as [k Hk].
  exact (existT _ k
           (RealSetoid.real_lt_le_iff_req (rap_rate p k) (rap_budget p)
              (inl Hk))).
Defined.

(* 量级界（Qed 面）：返回站过、以下全败、测试次数 ≤ 2·log₂K+5              *)
Corollary rap_k_select_account : forall (p : rap_alg) (kw r c : nat),
  rap_test p 0%nat = false ->
  rap_test p kw = true ->
  mixb_sel (rap_test p)
    (Datatypes.S (Datatypes.S (Nat.log2 (Nat.max kw 2))))
    (Datatypes.S (Datatypes.S (Nat.log2 (Nat.max kw 2)))) = (r, c) ->
  rap_test p r = true /\
  (forall j : nat, (j < r)%nat -> rap_test p j = false) /\
  (c <= 2 * (Nat.log2 (Nat.max kw 2)) + 5)%nat.
Proof.
  intros p kw r c H0 Hkw Esel.
  destruct (igr_k_enum (rap_test p) kw) as [kmin|] eqn:Eenum.
  - pose proof (igr_k_enum_sound (rap_test p) kw kmin Eenum) as Hsnd.
    pose proof (igr_k_enum_min (rap_test p) kw kmin Eenum) as Hmin.
    pose proof (mixb_enum_le (rap_test p) kw kmin Eenum) as HminK.
    assert (H1 : (1 <= kmin)%nat).
    { destruct kmin as [| m].
      - rewrite H0 in Hsnd. discriminate Hsnd.
      - exact (le_n_S 0 m (le_0_n m)). }
    assert (HK : (kmin <= Nat.max kw 2)%nat)
      by (exact (Nat.le_trans kmin kw (Nat.max kw 2) HminK
                  (Nat.le_max_l kw 2))).
    destruct (mixb_sel_scale (rap_test p) (Nat.max kw 2) kmin r c
                (rap_mono p) H0 Hsnd Hmin H1 HK (Nat.le_max_r kw 2) Esel)
      as [Hrk Hcnt].
    rewrite Hrk.
    split; [ exact Hsnd | split; [ exact Hmin | exact Hcnt ] ].
  - exfalso.
    exact (rap_bool_contra (rap_test p kw) Hkw
             (igr_k_enum_none (rap_test p) kw Eenum kw (Nat.le_refl kw))).
Qed.

(* ============================================================ *)
(* §3 几何率实例（件③，real_ 面 tv_rpow 形）                               *)
(* ============================================================ *)

Local Open Scope Q_scope.

(* 包级实例：rate k := κ^k·A，测试 := mixb_qtest κ0 v b0（Q 层可判定），  *)
(* 桥 := mixb_real_chain 回传链，窗 := real_arch 兜底 + Q-Bernoulli 反解。 *)
(* 证书拆显式参数、构造器直出（体内零 destruct）——投影换算面保归约，    *)
(* 使用侧推论在自身体内做证书拆分。 *)
(* ——mix_k_select 语义的包级复现（语义级实例，不逐字回替）。 *)
Definition rap_geom_alg (kappa A B : Real) (v : Q)
  (Hk1 : real_lt real_zero kappa)
  (HA : real_le real_zero A)
  (epsK : Q) (HepsK : QltT 0 epsK) (NK : nat)
  (HNK : forall n : nat, NatLe NK n -> QltT epsK (projT1 real_one n - projT1 kappa n))
  (Hvc : real_le A (real_const v))
  (epsB : Q) (HepsB : QltT 0 epsB) (NB : nat)
  (HNB : forall n : nat, NatLe NB n -> QltT epsB (projT1 B n - projT1 real_zero n))
  : rap_alg.
Proof.
  assert (Hk0 : 0 < 1 - mixb_mu epsK)
    by (apply mixb_kappa0_pos; exact (QltT_to_Qlt 0 epsK HepsK)).
  assert (Hk0lt : 1 - mixb_mu epsK < 1)
    by (apply mixb_kappa0_lt_one; exact (QltT_to_Qlt 0 epsK HepsK)).
  assert (Hb0 : 0 < epsB * (1 # 2)).
  { apply (Qmult_lt_0_compat epsB (1 # 2)).
    - exact (QltT_to_Qlt 0 epsB HepsB).
    - exact mixb_q_12_pos. }
  assert (Hv0 : 0 <= v) by exact (mixb_v_nonneg A v HA Hvc).
  assert (Hk0le : real_le kappa (real_const (1 - mixb_mu epsK))).
  { apply (RealSetoid.real_lt_le_iff_req). left.
    exact (mixb_kappa0_bridge kappa epsK NK HepsK HNK). }
  assert (Hc0pos : real_lt real_zero (real_const (1 - mixb_mu epsK)))
    by exact (mixb_qpos_const_lt _ Hk0).
  assert (Hbb : real_lt (real_const (epsB * (1 # 2))) B)
    by exact (mixb_b0_bridge B epsB NB HepsB HNB).
  apply (mk_rap_alg (fun k : nat => real_mult (tv_rpow kappa k) A) B
           (mixb_qtest (1 - mixb_mu epsK) v (epsB * (1 # 2)))).
  - (* 单调：Q 幂递减 × v 非负 ⟹ 过站集上闭 *)
    exact (mixb_qtest_mono (1 - mixb_mu epsK) v (epsB * (1 # 2)) Hk0
             (Qlt_le_weak (1 - mixb_mu epsK) 1 Hk0lt) Hv0).
  - (* 过站窗：real_arch 兜底 + Q-Bernoulli 反解 *)
    pose (wb := ((1 - (1 - mixb_mu epsK)) * (epsB * (1 # 2)))%Q).
    assert (Hwbpos : 0 < wb).
    { pose proof (mixb_mu_pos epsK (QltT_to_Qlt 0 epsK HepsK)) as Hmu.
      unfold wb.
      apply (Qmult_lt_0_compat (1 - (1 - mixb_mu epsK))
               (epsB * (1 # 2))); [ lra | exact Hb0 ]. }
    assert (Hwbne : ~ (wb == 0)).
    { intro He. apply (Qlt_not_eq 0 wb Hwbpos). apply mixb_qeq_sym.
      exact He. }
    destruct (real_arch (real_const (v * Qinv wb))) as [nA Hpair].
    destruct Hpair as [Hnge2 Harchlt].
    assert (Hqarch : Qlt (v * Qinv wb) (Z.of_nat nA # 1))
      by exact (mixb_const_lt_to_Qlt _ _ Harchlt).
    assert (Hwin : Qle v ((Z.of_nat nA # 1) * wb)).
    { apply Qlt_le_weak.
      apply (Qle_lt_trans v ((v * Qinv wb) * wb)
               ((Z.of_nat nA # 1) * wb)).
      - apply qeq_le. apply mixb_qeq_sym.
        exact (mixb_qmul_inv_cancel v wb Hwbpos).
      - exact (Qmult_lt_compat_r (v * Qinv wb) (Z.of_nat nA # 1) wb
                 Hwbpos Hqarch). }
    assert (HpassnA : mixb_qtest (1 - mixb_mu epsK) v (epsB * (1 # 2)) nA
                      = true).
    { apply (mixb_window_test_true (1 - mixb_mu epsK) v (epsB * (1 # 2))
               nA Hk0 Hk0lt Hv0 Hb0); [ lia | exact Hwin ]. }
    exact (existT _ nA HpassnA).
  - (* Real 语义桥：测试真值 ⟹ κ^n·A < B（mixb 回传链） *)
    intros n Hn.
    exact (mixb_real_chain kappa A B (1 - mixb_mu epsK) v (epsB * (1 # 2))
             n Hk1 Hk0le Hc0pos HA Hvc Hbb Hn).
Defined.

(* 包级语义复现：几何率形 κ^k·A 的预算驱动步返回（mix_k_select 语义）      *)
(* ——证书拆分在本推论体内完成，包构造器直出故投影换算一步闭合。           *)
Corollary rap_geom_k_select : forall (kappa A B : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero A -> real_lt real_zero B ->
  sigT (fun v : Q => real_le A (real_const v)) ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) A) B).
Proof.
  intros kappa A B Hk1 Hk2 HA Hb Htv.
  destruct Hk2 as [epsK [HepsK [NK HNK]]].
  destruct Hb as [epsB [HepsB [NB HNB]]].
  destruct Htv as [v Hvc].
  exact (rap_k_select
           (rap_geom_alg kappa A B v Hk1 HA epsK HepsK NK HNK Hvc
              epsB HepsB NB HNB)).
Defined.

(* 率形单调递减（接口 rap_mono 字段的实例层语义化）：κ ≤ 1 收缩因子        *)
Theorem rap_geom_rate_dec : forall (kappa A : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero A ->
  forall (n : nat),
  real_le (real_mult (tv_rpow kappa (Datatypes.S n)) A)
          (real_mult (tv_rpow kappa n) A).
Proof.
  intros kappa A Hk1 Hk2 HA n.
  assert (Hk2le : real_le kappa real_one).
  { exact (RealSetoid.real_lt_le_iff_req kappa real_one (inl Hk2)). }
  assert (Hnn : real_le real_zero (tv_rpow kappa n)).
  { exact (mix_rpow_nonneg kappa n
             (RealSetoid.real_lt_le_iff_req real_zero kappa (inl Hk1))). }
  assert (Hstep : real_le (real_mult kappa (tv_rpow kappa n))
                          (real_mult real_one (tv_rpow kappa n)))
    by (exact (real_le_mult_compat_weak kappa real_one (tv_rpow kappa n)
                 Hnn Hk2le)).
  apply (real_le_trans _ (real_mult (real_mult real_one (tv_rpow kappa n)) A)
                        (real_mult (tv_rpow kappa n) A)).
  - apply (real_le_trans _ (real_mult (real_mult kappa (tv_rpow kappa n)) A)).
    + apply (RealSetoid.real_eq_le).
      exact (real_eq_refl (real_mult (real_mult kappa (tv_rpow kappa n)) A)).
    + exact (real_le_mult_compat_weak
               (real_mult kappa (tv_rpow kappa n))
               (real_mult real_one (tv_rpow kappa n)) A HA Hstep).
  - apply (RealSetoid.real_eq_le).
    exact (RealSetoid.real_eq_mult_compat
             (real_mult real_one (tv_rpow kappa n)) A
             (tv_rpow kappa n) A
             (mix_mult_one_l (tv_rpow kappa n)) (real_eq_refl A)).
Qed.

(* ============================================================ *)
(* 假设审计（零承认件，全 Closed 预期）                                     *)
(* ============================================================ *)

Print Assumptions rap_sel_true.
Print Assumptions rap_k_select.
Print Assumptions rap_k_select_le.
Print Assumptions rap_k_select_account.
Print Assumptions rap_geom_alg.
Print Assumptions rap_geom_k_select.
Print Assumptions rap_geom_rate_dec.

(* ============================ §17 slm_slack_select（抽象松弛组合定理：预算劈半——几何半边 mix_k_select 与线性半边 eps:=(1/n)·(B/4) 合流） ============================ *)
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
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSampling.
Require Import UpTVDoeblin.
Require Import UpReqIterGeomRate.
Require Import UpReqConcFin2.
Require Import UpReqMixingTime.
Import RealInterfaceEnhancedMod.

(* ---- 帮件一：κ 幂乘积非负（收缩环节的见证供给，对任意 κ ≤ 1 与 A ≥ 0） ---- *)

Lemma slm_pow_mult_nonneg : forall (kappa A : Real),
  le zero kappa -> le kappa one -> le zero A ->
  forall (n : nat), le zero (mult (req_r_pow kappa n) A).
Proof.
  intros kappa A Hk0 Hk1 HA n.
  induction n as [| m IH].
  - exact (le_id_r zero A (mult (req_r_pow kappa 0%nat) A)
             (req_sym _ _ (cf2_mult_one_l A)) HA).
  - assert (Hmid : le (mult kappa (mult (req_r_pow kappa m) A))
                      (mult (req_r_pow kappa m) A))
      by (exact (cf2_le_mult_one kappa (mult (req_r_pow kappa m) A) IH Hk1)).
    assert (Hz : le zero (mult kappa (mult (req_r_pow kappa m) A)))
      by (exact (le_id_l zero (mult zero (mult (req_r_pow kappa m) A))
                   (mult kappa (mult (req_r_pow kappa m) A))
                   (req_sym _ _
                      (req_trans (mult zero (mult (req_r_pow kappa m) A))
                                 (mult (mult (req_r_pow kappa m) A) zero)
                                 zero
                                 (mult_comm zero
                                    (mult (req_r_pow kappa m) A))
                                 (mult_zero (mult (req_r_pow kappa m) A))))
                   (le_mult_compat_weak zero kappa
                      (mult (req_r_pow kappa m) A) IH Hk0))).
    exact (le_id_r zero (mult kappa (mult (req_r_pow kappa m) A))
             (mult (mult kappa (req_r_pow kappa m)) A)
             (mult_assoc kappa (req_r_pow kappa m) A) Hz).
Defined.

(* ---- 帮件二：tv_rpow 面与 req_r_pow 面的形态转换适配引理（归纳桥，req 逐位） ----
   两 Fixpoint 参数结构不同（req_r_pow 带 R/RIS 参数），stuck 点上转换
   不闭合，故按归纳构造 req 桥；基座 Real 上两幂同体归约。 *)

Lemma slm_rpow_tvpow : forall (kappa : Real) (n : nat),
  req (req_r_pow kappa n) (tv_rpow kappa n).
Proof.
  intros kappa n.
  induction n as [| m IH].
  - exact (req_refl (tv_rpow kappa 0%nat)).
  - exact (req_mult_compat kappa kappa (req_r_pow kappa m)
             (tv_rpow kappa m) (req_refl kappa) IH).
Defined.

(* ---- 件①：抽象松弛组合定理（率界接口 + 无条件选择器，零 k₀ 前提） ----
   四证书照 mix_k_select 前提面（0<κ<1、0≤A、0<B）；Hsl 为「松弛率界」
   接口：rate n ≤ κⁿ·A + n·eps 对每个 eps>0（cf2_tv_iter_mu0 界形的
   抽象化）。结论：显式返回 k := S k_g 使 rate k < B（_le 形推论随后）。 *)

Theorem slm_slack_select : forall (rate : nat -> Real) (kappa A budget : Real),
  lt zero kappa -> lt kappa one ->
  le zero A -> lt zero budget ->
  (forall (n : nat) (eps : Real), lt zero eps ->
     le (rate n) (plus (mult (req_r_pow kappa n) A)
                       (mult (reqd_nat_to_R n) eps))) ->
  sigT (fun k : nat => lt (rate (Datatypes.S k)) budget).
Proof.
  intros rate kappa A budget Hk1 Hk2 HA Hbudget Hsl.
  assert (Hk0 : le zero kappa)
    by (exact (lt_le_iff zero kappa (inl Hk1))).
  assert (Hk2le : le kappa one)
    by (exact (lt_le_iff kappa one (inl Hk2))).
  assert (Hinv2pos : lt zero cf2_inv_two)
    by (exact (inv_pos_pos (plus one one) req_two_pos)).
  assert (HX0 : lt zero (mult cf2_inv_two budget))
    by (exact (mult_positive cf2_inv_two budget Hinv2pos Hbudget)).
  assert (HY0 : lt zero (mult cf2_inv_two (mult cf2_inv_two budget)))
    by (exact (mult_positive cf2_inv_two (mult cf2_inv_two budget)
                Hinv2pos HX0)).
  (* 几何半边：无条件件选择器对 (κ, A, B/2) 取 k_g（零 k₀、零几何前提） *)
  destruct (mix_k_select kappa A (mult cf2_inv_two budget) Hk1 Hk2 HA HX0)
    as [kg Hkg].
  (* 形态转换适配：tv_rpow/real_mult 面 -> req_r_pow/mult 面
     （slm_rpow_tvpow 归纳桥 + req_mult_compat/req_lt_compat 转换） *)
  assert (HkgI : lt (mult (req_r_pow kappa kg) A)
                    (mult cf2_inv_two budget)).
  { exact (req_lt_compat (mult (tv_rpow kappa kg) A)
             (mult (req_r_pow kappa kg) A)
             (mult cf2_inv_two budget) (mult cf2_inv_two budget)
             (req_mult_compat (tv_rpow kappa kg) (req_r_pow kappa kg) A A
                (req_sym _ _ (slm_rpow_tvpow kappa kg)) (req_refl A))
             (req_refl (mult cf2_inv_two budget))
             Hkg). }
  (* 收缩环节：κ^{S k_g}·A ≤ κ^{k_g}·A *)
  assert (Hshr : le (mult (req_r_pow kappa (Datatypes.S kg)) A)
                    (mult (req_r_pow kappa kg) A)).
  { exact (le_id_l (mult (mult kappa (req_r_pow kappa kg)) A)
             (mult kappa (mult (req_r_pow kappa kg) A))
             (mult (req_r_pow kappa kg) A)
             (req_sym _ _ (mult_assoc kappa (req_r_pow kappa kg) A))
             (cf2_le_mult_one kappa (mult (req_r_pow kappa kg) A)
                (slm_pow_mult_nonneg kappa A Hk0 Hk2le HA kg) Hk2le)). }
  assert (Hgeolt : lt (mult (req_r_pow kappa (Datatypes.S kg)) A)
                      (mult cf2_inv_two budget))
    by (exact (le_lt_trans _ _ _ Hshr HkgI)).
  (* 线性半边：eps := (1/n)·(B/4) 于候选点 n := S k_g 构造（正性 + 消逆） *)
  assert (Heps : lt zero (mult (inv_pos (reqd_nat_to_R (Datatypes.S kg))
                                          (reqd_nat_to_R_pos kg))
                               (mult cf2_inv_two (mult cf2_inv_two budget))))
    by (exact (mult_positive (inv_pos (reqd_nat_to_R (Datatypes.S kg))
                                       (reqd_nat_to_R_pos kg))
                             (mult cf2_inv_two (mult cf2_inv_two budget))
                             (inv_pos_pos (reqd_nat_to_R (Datatypes.S kg))
                                          (reqd_nat_to_R_pos kg))
                             HY0)).
  assert (Hiter : le (rate (Datatypes.S kg))
                    (plus (mult (req_r_pow kappa (Datatypes.S kg)) A)
                          (mult cf2_inv_two (mult cf2_inv_two budget)))).
  { exact (le_id_r (rate (Datatypes.S kg))
             (plus (mult (req_r_pow kappa (Datatypes.S kg)) A)
                   (mult (reqd_nat_to_R (Datatypes.S kg))
                      (mult (inv_pos (reqd_nat_to_R (Datatypes.S kg))
                                     (reqd_nat_to_R_pos kg))
                            (mult cf2_inv_two (mult cf2_inv_two budget)))))
             (plus (mult (req_r_pow kappa (Datatypes.S kg)) A)
                   (mult cf2_inv_two (mult cf2_inv_two budget)))
             (req_plus_compat
                (mult (req_r_pow kappa (Datatypes.S kg)) A)
                (mult (req_r_pow kappa (Datatypes.S kg)) A)
                (mult (reqd_nat_to_R (Datatypes.S kg))
                   (mult (inv_pos (reqd_nat_to_R (Datatypes.S kg))
                                  (reqd_nat_to_R_pos kg))
                         (mult cf2_inv_two (mult cf2_inv_two budget))))
                (mult cf2_inv_two (mult cf2_inv_two budget))
                (req_refl (mult (req_r_pow kappa (Datatypes.S kg)) A))
                (cf2_inv_cancel (mult cf2_inv_two (mult cf2_inv_two budget))
                   kg))
             (Hsl (Datatypes.S kg) _ Heps)). }
  (* 合流：B/4 < B/2 严格不等式 + B/2 + B/2 = B 合成（cf2 辅助引理族） *)
  assert (HYX : lt (mult cf2_inv_two (mult cf2_inv_two budget))
                   (mult cf2_inv_two budget)).
  { exact (lt_id_r (mult cf2_inv_two (mult cf2_inv_two budget))
             (mult one (mult cf2_inv_two budget))
             (mult cf2_inv_two budget)
             (cf2_mult_one_l (mult cf2_inv_two budget))
             (lt_mult_compat cf2_inv_two one (mult cf2_inv_two budget)
                HX0 cf2_inv2_lt_one)). }
  assert (Hcomb : lt (plus (mult (req_r_pow kappa (Datatypes.S kg)) A)
                           (mult cf2_inv_two (mult cf2_inv_two budget)))
                     (plus (mult cf2_inv_two budget)
                           (mult cf2_inv_two budget))).
  { exact (cf2_lt_plus_compat_lt_le
             (mult (req_r_pow kappa (Datatypes.S kg)) A)
             (mult cf2_inv_two budget)
             (mult cf2_inv_two (mult cf2_inv_two budget))
             (mult cf2_inv_two budget)
             Hgeolt (lt_le_iff (mult cf2_inv_two (mult cf2_inv_two budget))
                        (mult cf2_inv_two budget) (inl HYX))). }
  exact (existT (fun k : nat => lt (rate (Datatypes.S k)) budget)
           kg
           (le_lt_trans (rate (Datatypes.S kg))
              (plus (mult (req_r_pow kappa (Datatypes.S kg)) A)
                    (mult cf2_inv_two (mult cf2_inv_two budget)))
              budget Hiter
              (lt_id_r (plus (mult (req_r_pow kappa (Datatypes.S kg)) A)
                             (mult cf2_inv_two (mult cf2_inv_two budget)))
                       (plus (mult cf2_inv_two budget)
                             (mult cf2_inv_two budget))
                       budget (cf2_two_inv_budget budget) Hcomb))).
Defined.

(* ---- 件① le 形推论（一步推得：严格不等式走 Or 左支） ---- *)

Corollary slm_slack_select_le :
  forall (rate : nat -> Real) (kappa A budget : Real),
  lt zero kappa -> lt kappa one ->
  le zero A -> lt zero budget ->
  (forall (n : nat) (eps : Real), lt zero eps ->
     le (rate n) (plus (mult (req_r_pow kappa n) A)
                       (mult (reqd_nat_to_R n) eps))) ->
  sigT (fun k : nat => le (rate (Datatypes.S k)) budget).
Proof.
  intros rate kappa A budget Hk1 Hk2 HA Hbudget Hsl.
  destruct (slm_slack_select rate kappa A budget Hk1 Hk2 HA Hbudget Hsl)
    as [k Hk].
  exact (existT (fun k : nat => le (rate (Datatypes.S k)) budget) k
           (lt_le_iff (rate (Datatypes.S k)) budget (inl Hk))).
Defined.

(* ---- 帮件二：cf2_omd < 1（δ* > 0 严格平移：omd < omd + δ* = 1） ---- *)

Lemma slm_omd_lt_one : lt cf2_omd one.
Proof.
  exact (lt_id_r cf2_omd (plus cf2_omd cf2_delta_star) one           (req_trans (plus cf2_omd cf2_delta_star)                      (plus cf2_delta_star cf2_omd) one                      (plus_comm cf2_omd cf2_delta_star)                      cf2_aux_ds_omd)           (igr_lt_plus_r cf2_omd cf2_delta_star cf2_ds_pos)).
Defined.

(* ---- 件②：Fin2 无条件形（零 k₀ 前提版） ----
   原 cf2_mixing_time_le 的 k₀ 输入前提与几何衰减前提
   （omd^{k0}·TV₀ ≤ B/2）由此内部化消去：k₀ 不再是输入，而由件①的
   无条件选择器在预算劈半内算出（强化：原形见件③推论）。 *)

Theorem slm_cf2_mixing_full : forall budget : Real,
  lt zero budget ->
  sigT (fun k : nat =>
        lt (cf2_tv (cf2_titer k cf2_mu0) (cf2_titer k cf2_nu0)) budget).
Proof.
  intros budget Hbudget.
  destruct (slm_slack_select
              (fun n : nat => cf2_tv (cf2_titer n cf2_mu0)
                                     (cf2_titer n cf2_nu0))
              cf2_omd (cf2_tv cf2_mu0 cf2_nu0) budget
              cf2_omd_pos slm_omd_lt_one cf2_tv_nonneg Hbudget
              cf2_tv_iter_mu0) as [k Hk].
  exact (existT (fun k : nat =>
            lt (cf2_tv (cf2_titer k cf2_mu0) (cf2_titer k cf2_nu0)) budget)
           (Datatypes.S k) Hk).
Defined.

(* ---- 件③：转换推论（向后兼容） ----
   原 cf2_mixing_time_le 的完整语句面（k₀ + 几何衰减前提）从件②一步
   直推：几何前提与 k₀ 在件②下为冗余前提，照原面全数保留以兼容旧
   使用面——原形由此成为件② + 冗余前提的转换读法。 *)

Corollary slm_cf2_le_of_full : forall (budget : Real) (k0 : nat),
  lt zero budget ->
  le (mult (req_r_pow cf2_omd k0) (cf2_tv cf2_mu0 cf2_nu0))
     (mult cf2_inv_two budget) ->
  sigT (fun k : nat =>
        lt (cf2_tv (cf2_titer k cf2_mu0) (cf2_titer k cf2_nu0)) budget).
Proof.
  intros budget k0 Hbudget Hgeo.
  exact (slm_cf2_mixing_full budget Hbudget).
Defined.

(* ============================================================ *)
(* 假设审计（零承认件，全 Closed 预期）                                    *)
(* ============================================================ *)

Print Assumptions slm_pow_mult_nonneg.
Print Assumptions slm_slack_select.
Print Assumptions slm_slack_select_le.
Print Assumptions slm_omd_lt_one.
Print Assumptions slm_cf2_mixing_full.
Print Assumptions slm_cf2_le_of_full.

(* ============================ §18 Q 层 Bernoulli 幂下界与 Doeblin 界无界性件 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqMixLogE.
From Stdlib Require Import QArith.QArith QArith.Qminmax ZArith.ZArith
               Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import micromega.Lqa.

Local Open Scope Q_scope.

(* ============================================================ *)
(* 第 0 层：幂载体与 (S n) 倒数数字面                                *)
(* ============================================================ *)

(* 幂载体（本件自备 Fixpoint：形状同 mixe_qpow/qpow，库内各件自备      *)
(* 同形件为惯例；定理 A 语句面用本件载体，保持 mqd_ 前缀自洽）         *)
Fixpoint mqd_pow (w : Q) (k : nat) : Q :=
  match k with
  | O => 1
  | Datatypes.S m => w * mqd_pow w m
  end.

(* (S n) 的 Q 倒数：1/(S N)，除法以倒数积承载（规格书见证 min 项）      *)
Definition mqd_invSN (n : nat) : Q := (1 # Pos.of_nat (Datatypes.S n))%Q.

Lemma mqd_znat_le_posS : forall n : nat,
  (Z.of_nat n <= Z.pos (Pos.of_nat (Datatypes.S n)))%Z.
Proof.
  intro n. induction n as [| m IH].
  - change (Z.of_nat 0) with 0%Z.
    apply Z.lt_le_incl. apply Pos2Z.pos_is_pos.
  - rewrite Nat2Z.inj_succ.
    replace (Z.pos (Pos.of_nat (Datatypes.S (Datatypes.S m))))
      with (Z.pos (Pos.succ (Pos.of_nat (Datatypes.S m)))) by reflexivity.
    rewrite Pos2Z.inj_succ. lia.
Qed.

Lemma mqd_invSN_pos : forall n : nat, Qlt 0 (mqd_invSN n).
Proof.
  intro n. unfold mqd_invSN, Qlt. cbn [Qnum Qden].
  (* 目标即 Z 严格序 0·den lo < 1·den 0：以 Z.mul_0_l/Z.mul_1_l 显式    *)
  (* 归约两侧乘法，余下 0 < 1 由零侧分母位正数 1 的正性见证             *)
  (* Pos2Z.is_pos 构造                                                  *)
  rewrite Z.mul_0_l, Z.mul_1_l.
  exact (Pos2Z.is_pos 1%positive).
Qed.

Lemma mqd_invSN_le1 : forall n : nat, Qle (mqd_invSN n) 1.
Proof.
  intro n. unfold mqd_invSN, Qle. cbn [Qnum Qden].
  (* 目标即 Z 序 1·1 ≤ 1·den：两侧乘法以 Z.mul_1_l 归约，               *)
  (* 1 ≤ Z.pos den 经 Z.le_succ_l（1 与 Z.succ 0 可转换）化为           *)
  (* 0 < Z.pos den，由分母位 Pos.of_nat (S n) 的正性见证构造             *)
  rewrite !Z.mul_1_l.
  apply (proj2 (Z.le_succ_l 0 (Z.pos (Pos.of_nat (Datatypes.S n))))).
  apply Pos2Z.is_pos.
Qed.

Lemma mqd_kQ_inv_le : forall n : nat,
  Qle (mixe_qofnat n * mqd_invSN n) 1.
Proof.
  intro n. unfold mqd_invSN, Qle, Qmult, mixe_qofnat. cbn [Qnum Qden].
  rewrite Pos.mul_1_l.
  (* 目标即 Z 序 Z.of_nat n·1·1 ≤ 1·den：正数位积以 Pos.mul_1_l 归约，  *)
  (* 两侧乘法单位元以 Z.mul_1_r/Z.mul_1_l 逐步归约，                    *)
  (* 余下 Z 序结论即既有构造性引理 mqd_znat_le_posS n                   *)
  rewrite !Z.mul_1_r, Z.mul_1_l.
  exact (mqd_znat_le_posS n).
Qed.

(* ============================================================ *)
(* 件①：规格书缺口 G1——Bernoulli 幂下界 (1−x)^N ≥ 1−N·x（0≤x≤1）    *)
(* ============================================================ *)

Lemma mqd_bernoulli_lower : forall (x : Q) (n : nat),
  Qle 0 x -> Qle x 1 ->
  Qle (1 - mixe_qofnat n * x) (mqd_pow (1 - x) n).
Proof.
  intros x n Hx0 Hx1.
  assert (Hmx : Qle 0 (1 - x)) by exact (mixe_sub_nonneg x Hx1).
  induction n as [| n IH].
  - apply (mixe_qle_eq_l (1 - mixe_qofnat 0 * x) 1 1).
    + change (mixe_qofnat 0) with 0%Q. ring.
    + apply Qle_refl.
  - cbn [mqd_pow].
    assert (Hk0 : Qle 0 (mixe_qofnat n)) by exact (mixe_qofnat_nonneg n).
    assert (Hxx : Qle 0 (mixe_qofnat n * x * x))
      by exact (mixe_qmult_nonneg (mixe_qofnat n * x) x
                  (mixe_qmult_nonneg (mixe_qofnat n) x Hk0 Hx0) Hx0).
    (* 链：A ≤ A + k·x² == (1−x)·(1−k·x) ≤ (1−x)·(1−x)^n *)
    assert (Hstep1 : Qle (1 - (1 + mixe_qofnat n) * x)
                         ((1 - (1 + mixe_qofnat n) * x)
                            + mixe_qofnat n * x * x))
      by lra.
    assert (Hstep2 : ((1 - (1 + mixe_qofnat n) * x)
                        + mixe_qofnat n * x * x)
                     == ((1 - x) * (1 - mixe_qofnat n * x))) by ring.
    assert (HBD : Qle (1 - (1 + mixe_qofnat n) * x)
                      ((1 - x) * (1 - mixe_qofnat n * x)))
      by exact (mixe_qle_eq_r _ _ _ Hstep1 Hstep2).
    assert (Hstep3 : Qle ((1 - x) * (1 - mixe_qofnat n * x))
                          ((1 - x) * mqd_pow (1 - x) n))
      by exact (mixe_qmult_le_l (1 - x) (1 - mixe_qofnat n * x)
                  (mqd_pow (1 - x) n) Hmx IH).
    apply (mixe_qle_eq_l (1 - mixe_qofnat (Datatypes.S n) * x)
             (1 - (1 + mixe_qofnat n) * x)
             ((1 - x) * mqd_pow (1 - x) n)).
    + rewrite (mixe_qofnat_S n). ring.
    + exact (Qle_trans _ _ _ HBD Hstep3).
Qed.

(* G1 出口：QleT' 面（Set 层判定证书） *)
Lemma mqd_bernoulli_lowerT : forall (x : Q) (n : nat),
  QleT' 0 x -> QleT' x 1 ->
  QleT' (1 - mixe_qofnat n * x) (mqd_pow (1 - x) n).
Proof.
  intros x n Hx0 Hx1. apply Qle_to_QleT'.
  exact (mqd_bernoulli_lower x n
           (QleT'_to_Qle 0 x Hx0) (QleT'_to_Qle x 1 Hx1)).
Qed.

(* 使用+桥接件：任务说明 (1−w)^k·(1+k·w) ≤ 1 形——直接使用库内            *)
(* mixe_bern_sharp（UpReqMixLogE F1 锐化 Bernoulli 上形），T 化出口     *)
Lemma mqd_bern_complement : forall (w : Q) (k : nat),
  QleT' 0 w -> QleT' w 1 ->
  QleT' (mixe_qpow (1 - w) k * (1 + mixe_qofnat k * w)) 1.
Proof.
  intros w k Hw0 Hw1. apply Qle_to_QleT'.
  exact (mixe_bern_sharp w k
           (QleT'_to_Qle 0 w Hw0) (QleT'_to_Qle w 1 Hw1)).
Qed.

(* ============================================================ *)
(* 件② 支撑：见证的界与收缩关键式                                    *)
(* ============================================================ *)

(* 见证收缩关键式：lo ≤ (1−r)·inv(S N) ∧ 0<lo<1 ⟹ N·lo² < 1−r         *)
Lemma mqd_shrink_key : forall (N : nat) (lo r : Q),
  Qlt 0 lo -> Qlt lo 1 -> Qlt 0 (1 - r) ->
  Qle lo ((1 - r) * mqd_invSN N) ->
  Qlt (mixe_qofnat N * (lo * lo)) (1 - r).
Proof.
  intros N lo r Hlo Hlo1 Hrp Hle.
  assert (Hlp : Qle 0 lo) by exact (Qlt_le_weak 0 lo Hlo).
  assert (Hu : Qlt 0 ((1 - r) * mqd_invSN N)).
  { apply (mixe_qlt_eq_l 0 (0 * mqd_invSN N) ((1 - r) * mqd_invSN N)).
    - ring.
    - exact (Qmult_lt_compat_r 0 (1 - r) (mqd_invSN N)
               (mqd_invSN_pos N) Hrp). }
  assert (Hs1 : Qle (lo * lo) (lo * ((1 - r) * mqd_invSN N)))
    by exact (mixe_qmult_le_l lo lo ((1 - r) * mqd_invSN N) Hlp Hle).
  assert (Hs2 : Qlt (lo * ((1 - r) * mqd_invSN N))
                    ((1 - r) * mqd_invSN N)).
  { apply (mixe_qlt_eq_r (1 * ((1 - r) * mqd_invSN N))
             ((1 - r) * mqd_invSN N) (lo * ((1 - r) * mqd_invSN N))).
    - ring.
    - exact (Qmult_lt_compat_r lo 1 ((1 - r) * mqd_invSN N) Hu Hlo1). }
  assert (Hs3 : Qlt (lo * lo) ((1 - r) * mqd_invSN N))
    by exact (Qle_lt_trans _ _ _ Hs1 Hs2).
  destruct N as [| m].
  - apply (mixe_qlt_eq_l (mixe_qofnat 0 * (lo * lo)) 0 (1 - r)).
    + change (mixe_qofnat 0) with 0%Q. ring.
    + exact Hrp.
  - assert (HkQpos : Qlt 0 (mixe_qofnat (Datatypes.S m))).
    { pose proof (mixe_qofnat_nonneg m) as Hmn.
      apply (mixe_qlt_eq_r (1 + mixe_qofnat m)
               (mixe_qofnat (Datatypes.S m)) 0).
      - exact (Qeq_sym (mixe_qofnat (Datatypes.S m))
                 (1 + mixe_qofnat m) (mixe_qofnat_S m)).
      - lra. }
    assert (Hs4 : Qle (mixe_qofnat (Datatypes.S m)
                         * ((1 - r) * mqd_invSN (Datatypes.S m)))
                      (1 - r)).
    { apply (mixe_qle_eq_l
               (mixe_qofnat (Datatypes.S m)
                  * ((1 - r) * mqd_invSN (Datatypes.S m)))
               (mixe_qofnat (Datatypes.S m)
                  * mqd_invSN (Datatypes.S m) * (1 - r))
               (1 - r)).
      - ring.
      - apply (mixe_qle_eq_r
                 (mixe_qofnat (Datatypes.S m)
                    * mqd_invSN (Datatypes.S m) * (1 - r))
                 (1 * (1 - r)) (1 - r)).
        + exact (Qmult_le_compat_r (mixe_qofnat (Datatypes.S m)
                        * mqd_invSN (Datatypes.S m)) 1 (1 - r)
                        (mqd_kQ_inv_le (Datatypes.S m))
                        (Qlt_le_weak 0 (1 - r) Hrp)).
        + ring. }
    assert (Hs5 : Qlt (mixe_qofnat (Datatypes.S m) * (lo * lo))
                      (mixe_qofnat (Datatypes.S m)
                         * ((1 - r) * mqd_invSN (Datatypes.S m)))).
    { apply (mixe_qlt_eq_l
               (mixe_qofnat (Datatypes.S m) * (lo * lo))
               ((lo * lo) * mixe_qofnat (Datatypes.S m))
               (mixe_qofnat (Datatypes.S m)
                  * ((1 - r) * mqd_invSN (Datatypes.S m)))).
      - ring.
      - apply (mixe_qlt_eq_r
                 (((1 - r) * mqd_invSN (Datatypes.S m))
                    * mixe_qofnat (Datatypes.S m))
                 (mixe_qofnat (Datatypes.S m)
                    * ((1 - r) * mqd_invSN (Datatypes.S m)))
                 ((lo * lo) * mixe_qofnat (Datatypes.S m))).
        + ring.
        + exact (Qmult_lt_compat_r (lo * lo)
                   ((1 - r) * mqd_invSN (Datatypes.S m))
                   (mixe_qofnat (Datatypes.S m)) HkQpos Hs3). }
    exact (Qlt_le_trans _ _ _ Hs5 Hs4).
Qed.

(* 见证三界：0 < lo < lo0 ∧ lo < 1（lo := Qmin (lo0/2) ((1−r)·inv)）   *)
Lemma mqd_witness_bounds : forall (N : nat) (lo0 r : Q),
  Qlt 0 lo0 -> Qlt 0 r -> Qlt r 1 ->
  Qlt 0 (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
  /\ Qlt (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) lo0
  /\ Qlt (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) 1.
Proof.
  intros N lo0 r Hlo0 Hr0 Hr1.
  assert (Hrp : Qlt 0 (1 - r)) by lra.
  assert (Hhalf : Qlt 0 (1 # 2)%Q) by lra.
  assert (Hr1l : Qlt (1 - r) 1) by lra.
  assert (Ha : Qlt 0 (lo0 * (1 # 2)%Q)).
  { apply (mixe_qlt_eq_l 0 (0 * (1 # 2)%Q) (lo0 * (1 # 2)%Q)).
    - ring.
    - exact (Qmult_lt_compat_r 0 lo0 (1 # 2)%Q Hhalf Hlo0). }
  assert (Hu : Qlt 0 ((1 - r) * mqd_invSN N)).
  { apply (mixe_qlt_eq_l 0 (0 * mqd_invSN N) ((1 - r) * mqd_invSN N)).
    - ring.
    - exact (Qmult_lt_compat_r 0 (1 - r) (mqd_invSN N)
               (mqd_invSN_pos N) Hrp). }
  split; [exact (Q.min_glb_lt _ _ _ Ha Hu) | split].
  - assert (Hminle : Qle (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
                         (lo0 * (1 # 2)%Q))
      by exact (Q.le_min_l (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)).
    assert (Halo : Qlt (lo0 * (1 # 2)%Q) lo0).
    { apply (mixe_qlt_eq_l (lo0 * (1 # 2)%Q) ((1 # 2)%Q * lo0) lo0).
      - ring.
      - apply (mixe_qlt_eq_r (1 * lo0) lo0 ((1 # 2)%Q * lo0)).
        + ring.
        + exact (Qmult_lt_compat_r (1 # 2)%Q 1 lo0 Hlo0 Hhalf). }
    exact (Qle_lt_trans _ _ _ Hminle Halo).
  - assert (Hminle : Qle (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
                         ((1 - r) * mqd_invSN N))
      by exact (Q.le_min_r (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)).
    assert (Hule : Qle ((1 - r) * mqd_invSN N) (1 - r)).
    { apply (mixe_qle_eq_l ((1 - r) * mqd_invSN N)
               (mqd_invSN N * (1 - r)) (1 - r)).
      - ring.
      - apply (mixe_qle_eq_r (mqd_invSN N * (1 - r)) (1 * (1 - r)) (1 - r)).
        + exact (Qmult_le_compat_r (mqd_invSN N) 1 (1 - r)
                    (mqd_invSN_le1 N) (Qlt_le_weak 0 (1 - r) Hrp)).
        + ring. }
    exact (Qle_lt_trans _ _ _ (Qle_trans _ _ _ Hminle Hule) Hr1l).
Qed.

(* ============================================================ *)
(* 件②：定理 A——Q 层 Doeblin 界无界性（QltT 见证形，规格书 §1.2）      *)
(*   语句与规格书 §1.2 逐点对应：0<lo0/0<r/r<1 以 QltT 证书面承载，      *)
(*   合取以 S01.And（Set 积型）承载；结论第三支即 QltT r ((1−lo²)^N)。  *)
(* ============================================================ *)

Theorem mqd_q_doeblin_bound_unbounded :
  forall (N : nat) (lo0 r : Q),
    QltT 0 lo0 -> QltT 0 r -> QltT r 1 ->
    sigT (fun lo : Q =>
      And (QltT 0 lo)
        (And (QltT lo lo0)
           (QltT r (mqd_pow (1 - lo * lo) N)))).
Proof.
  intros N lo0 r Hlo0T Hr0T Hr1T.
  assert (Hlo0 : Qlt 0 lo0) by exact (QltT_to_Qlt 0 lo0 Hlo0T).
  assert (Hr0 : Qlt 0 r) by exact (QltT_to_Qlt 0 r Hr0T).
  assert (Hr1 : Qlt r 1) by exact (QltT_to_Qlt r 1 Hr1T).
  refine (existT (fun lo : Q =>
             And (QltT 0 lo)
               (And (QltT lo lo0)
                  (QltT r (mqd_pow (1 - lo * lo) N))))
             (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) _).
  destruct (mqd_witness_bounds N lo0 r Hlo0 Hr0 Hr1) as [W1 [W2 W3]].
  (* 收缩关键式：N·lo² < 1−r *)
  assert (Hshr : Qlt (mixe_qofnat N *
                       (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                        Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)))
                  (1 - r)).
  { apply (mqd_shrink_key N
             (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) r).
    - exact W1.
    - exact W3.
    - lra.
    - exact (Q.le_min_r (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)). }
  (* Bernoulli 装配：r < 1 − N·lo² ≤ (1−lo²)^N *)
  assert (Hx0 : Qle 0 (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                            Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))).
  { exact (mixe_qmult_nonneg (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
             (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
             (Qlt_le_weak 0 _ W1) (Qlt_le_weak 0 _ W1)). }
  assert (Hx1 : Qle (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                      Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) 1).
  { apply (Qle_trans
             (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
              Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
             (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) 1).
    - apply (mixe_qle_eq_r
               (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
               (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) * 1)
               (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))).
      + exact (mixe_qmult_le_l
                 (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
                 (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) 1
                 (Qlt_le_weak 0 _ W1) (Qlt_le_weak _ 1 W3)).
      + ring.
    - exact (Qlt_le_weak _ 1 W3). }
  pose proof (mqd_bernoulli_lower
                (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                 Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) N
                Hx0 Hx1) as HB.
  assert (HK : Qlt r (mqd_pow
                (1 - Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                        Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) N)).
  { apply (Qlt_le_trans r
             (1 - mixe_qofnat N *
                (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                 Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)))
             (mqd_pow
                (1 - Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                        Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) N)).
    - lra.
    - exact HB. }
  split; [exact (Qlt_to_QltT 0 _ W1) | split].
  - exact (Qlt_to_QltT _ lo0 W2).
  - exact (Qlt_to_QltT r _ HK).
Defined.

(* ============================================================ *)
(* 证人注册面（G2/G5 口径：全件 Print Assumptions）                    *)
(* ============================================================ *)

Print Assumptions mqd_pow.
Print Assumptions mqd_invSN.
Print Assumptions mqd_znat_le_posS.
Print Assumptions mqd_invSN_pos.
Print Assumptions mqd_invSN_le1.
Print Assumptions mqd_kQ_inv_le.
Print Assumptions mqd_bernoulli_lower.
Print Assumptions mqd_bernoulli_lowerT.
Print Assumptions mqd_bern_complement.
Print Assumptions mqd_shrink_key.
Print Assumptions mqd_witness_bounds.
Print Assumptions mqd_q_doeblin_bound_unbounded.

(* ============================ §19 lgwd_sign_of_apart（离零支出符号提取）、lgwd_station_decide（rLPO 站点判定）、lgwd_MinSelD/lgw ============================ *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import Extraction.
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
Require Import UpTVDoeblin.
Require Import UpReqLpoEquiv.
Require Import UpReqMixingTime.
Require Import UpAblLogWall.
Require Import UpAblLogWallEq.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 0：Q 层支点与本件新核心——符号提取支（L3 未消解项消解）                   *)
(* ============================================================ *)

Lemma lgwd_q_half_pos : Qlt 0 (1#2).
Proof.
  exact (proj2 (Qlt_alt 0 (1#2)) (@eq_refl comparison Lt)).
Qed.

(* 符号提取：rLPO 离零支（尾项一致正隙 c，∀n≥N: c<|x_n|）+ Cauchy 模数      *)
(*   （eps:=c/2）⟹ 尾项（max N M 起）符号一致 ⟹ 采样点有理比较即得整支符号。*)
(*   产出 Or(0<x, x<0)——rLPO 独力供给符号面，L3「非负 Or 族」未消解项在此消解。 *)
Lemma lgwd_sign_of_apart : forall x : Real,
  sigT (fun c : Q =>
    And (QltT 0 c)
        (sigT (fun N : nat => forall n : nat, NatLe N n ->
          QltT c (Qabs (projT1 x n))))) ->
  Or (real_lt real_zero x) (real_lt x real_zero).
Proof.
  intros x Hap.
  destruct Hap as [c [Hc0T [Nc HNc]]].
  assert (Hc0 : Qlt 0 c) by (apply QltT_to_Qlt; exact Hc0T).
  assert (Hc2T : QltT 0 (c * (1#2))).
  { apply Qlt_to_QltT.
    assert (Hm : 0 * (1#2) < c * (1#2))
      by (apply Qmult_lt_compat_r; [exact lgwd_q_half_pos | exact Hc0]).
    rewrite Qmult_0_l in Hm. exact Hm. }
  destruct x as [u Hu].
  destruct (Hu (c * (1#2)) Hc2T) as [M HM].
  assert (HNcP : NatLe Nc (Nat.max Nc M)) by (apply NatLe_lift; lia).
  assert (HMP : NatLe M (Nat.max Nc M)) by (apply NatLe_lift; lia).
  specialize (HNc (Nat.max Nc M) HNcP).
  apply QltT_to_Qlt in HNc.
  (* HNc : c < |u P| ；HM : |u n − u P| < c/2（n ≥ P） *)
  destruct (Qlt_le_dec 0 (u (Nat.max Nc M))) as [Hp | Hn].
  - (* 正支：采样点为正 ⟹ 0 < x（尾项一致 > c/2） *)
    apply inl. unfold real_lt. exists (c * (1#2)). split.
    + exact Hc2T.
    + exists (Nat.max Nc M). intros n HnPM.
      assert (HMn : NatLe M n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max Nc M).
        - exact (NatLe_drop M (Nat.max Nc M) HMP).
        - exact (NatLe_drop (Nat.max Nc M) n HnPM). }
      specialize (HM n (Nat.max Nc M) HMn HMP).
      apply QltT_to_Qlt in HM.
      assert (HuP : u (Nat.max Nc M) == Qabs (u (Nat.max Nc M))).
      { symmetry. apply Qabs_pos. apply Qlt_le_weak. exact Hp. }
      assert (HcP : c < u (Nat.max Nc M)) by (rewrite HuP; exact HNc).
      apply Qlt_to_QltT.
      assert (Hz0 : projT1 real_zero n == 0) by reflexivity.
      rewrite Hz0.
      assert (Hm1 : u n - 0 == u n) by ring.
      rewrite Hm1.
      (* HM : |u n − u P| < c/2 ⟹ u P − u n < c/2（经 |−a|=|a| 迁移） *)
      assert (Hneg1 : u (Nat.max Nc M) - u n == - (u n - u (Nat.max Nc M))) by ring.
      assert (H1 : u (Nat.max Nc M) - u n < c * (1#2)).
      { rewrite Hneg1.
        apply (Qle_lt_trans (- (u n - u (Nat.max Nc M)))
                (Qabs (u n - u (Nat.max Nc M))) (c * (1#2))).
        - rewrite <- (Qabs_opp (u n - u (Nat.max Nc M))).
          apply lgwe_q_le_abs.
        - exact HM. }
      (* 链：c/2 + (uP−un) < c/2 + c/2 = c < uP = (uP−un) + un ⟹ 消去 ⟹ c/2 < un *)
      assert (H2 : c * (1#2) + (u (Nat.max Nc M) - u n) < c).
      { assert (Ht : c * (1#2) + (u (Nat.max Nc M) - u n)
                     < c * (1#2) + c * (1#2))
          by (apply (proj2 (Qplus_lt_r (u (Nat.max Nc M) - u n)
                              (c * (1#2)) (c * (1#2)))); exact H1).
        assert (Hr : c * (1#2) + c * (1#2) == c) by ring.
        rewrite Hr in Ht. exact Ht. }
      assert (H4 : c * (1#2) + (u (Nat.max Nc M) - u n) < u (Nat.max Nc M)).
      { apply (Qlt_trans _ c _ H2 HcP). }
      apply (proj1 (Qplus_lt_r (c * (1#2)) (u n) (u (Nat.max Nc M) - u n))).
      assert (H5 : (u (Nat.max Nc M) - u n) + u n == u (Nat.max Nc M)) by ring.
      rewrite H5.
      assert (H6 : (u (Nat.max Nc M) - u n) + c * (1#2)
                   == c * (1#2) + (u (Nat.max Nc M) - u n)) by ring.
      rewrite H6. exact H4.
  - (* 负支：采样点非正 ⟹ x < 0（尾项一致 < −c/2） *)
    apply inr. unfold real_lt. exists (c * (1#2)). split.
    + exact Hc2T.
    + exists (Nat.max Nc M). intros n HnPM.
      assert (HMn : NatLe M n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max Nc M).
        - exact (NatLe_drop M (Nat.max Nc M) HMP).
        - exact (NatLe_drop (Nat.max Nc M) n HnPM). }
      specialize (HM n (Nat.max Nc M) HMn HMP).
      apply QltT_to_Qlt in HM.
      apply Qlt_to_QltT.
      assert (HabsP : Qabs (u (Nat.max Nc M)) == - u (Nat.max Nc M))
        by (apply q_abs_neg_eq; exact Hn).
      rewrite HabsP in HNc.
      (* HNc : c < −u P ⟹ u P < −c *)
      assert (HuPn : u (Nat.max Nc M) < - c).
      { apply (proj1 (Qplus_lt_r (u (Nat.max Nc M)) (- c) c)).
        assert (Hr1 : c + - c == 0) by ring.
        rewrite Hr1.
        assert (Ht : u (Nat.max Nc M) + c < u (Nat.max Nc M) + - u (Nat.max Nc M))
          by (apply (proj2 (Qplus_lt_r c (- u (Nat.max Nc M))
                              (u (Nat.max Nc M)))); exact HNc).
        assert (Hr2 : u (Nat.max Nc M) + - u (Nat.max Nc M) == 0) by ring.
        rewrite Hr2 in Ht.
        assert (Hr3 : c + u (Nat.max Nc M) == u (Nat.max Nc M) + c) by ring.
        rewrite Hr3. exact Ht. }
      (* HM : |u n − u P| < c/2 ⟹ u n − u P < c/2（直用 a ≤ |a|） *)
      assert (H1 : u n - u (Nat.max Nc M) < c * (1#2)).
      { apply (Qle_lt_trans (u n - u (Nat.max Nc M))
                (Qabs (u n - u (Nat.max Nc M))) (c * (1#2))).
        - apply lgwe_q_le_abs.
        - exact HM. }
      assert (H3 : u n < u (Nat.max Nc M) + c * (1#2)).
      { assert (Ht : u (Nat.max Nc M) + (u n - u (Nat.max Nc M))
                     < u (Nat.max Nc M) + c * (1#2))
          by (apply (proj2 (Qplus_lt_r (u n - u (Nat.max Nc M))
                              (c * (1#2)) (u (Nat.max Nc M)))); exact H1).
        assert (Hr : u (Nat.max Nc M) + (u n - u (Nat.max Nc M)) == u n) by ring.
        rewrite <- Hr. exact Ht. }
      assert (H4 : u (Nat.max Nc M) + c * (1#2) < - c * (1#2)).
      { assert (Ht : c * (1#2) + u (Nat.max Nc M) < c * (1#2) + - c)
          by (apply (proj2 (Qplus_lt_r (u (Nat.max Nc M)) (- c)
                              (c * (1#2)))); exact HuPn).
        assert (Hr1 : c * (1#2) + u (Nat.max Nc M)
                      == u (Nat.max Nc M) + c * (1#2)) by ring.
        rewrite Hr1 in Ht.
        assert (Hr2 : c * (1#2) + - c == - c * (1#2)) by ring.
        rewrite Hr2 in Ht. exact Ht. }
      assert (H5 : u n < - c * (1#2)) by (exact (Qlt_trans _ _ _ H3 H4)).
      (* 目标：c/2 < 0 − u n *)
      assert (Hz0 : projT1 real_zero n == 0) by reflexivity.
      rewrite Hz0.
      assert (H6 : c * (1#2) + u n < 0).
      { assert (Ht : c * (1#2) + u n < c * (1#2) + - c * (1#2))
          by (apply (proj2 (Qplus_lt_r (u n) (- c * (1#2)) (c * (1#2)))); exact H5).
        assert (Hr : c * (1#2) + - c * (1#2) == 0) by ring.
        rewrite Hr in Ht. exact Ht. }
      apply (proj1 (Qplus_lt_r (c * (1#2)) (0 - u n) (u n))).
      assert (Hr2 : u n + (0 - u n) == 0) by ring.
      rewrite Hr2.
      assert (Hr3 : u n + c * (1#2) == c * (1#2) + u n) by ring.
      rewrite Hr3. exact H6.
Qed.

(* ============================================================ *)
(* Part 1：逐站判定（仅需 rLPO——免 L3 非负 Or 族前提）                       *)
(* ============================================================ *)

(* 否证新桥：差量严格负（real_lt (差量) 0）驳站账供隙支                      *)
(*   （供隙 eps0 < B_n−z_n 与负隙 eps < 0−(B_n−z_n) 在 max N0 N 处相撞：      *)
(*    eps0 + eps < 0 与 0 < eps0 + eps 相撞） *)
Lemma lgwd_test_refute_of_neg :
  forall (kappa TV0 budget : Real) (j : nat),
  real_lt (lgwe_diff kappa TV0 budget j) real_zero ->
  lgw_test kappa TV0 budget j -> Empty_set.
Proof.
  intros kappa TV0 budget j Hneg Htk.
  unfold lgw_test in Htk. unfold real_lt in Htk, Hneg.
  destruct Htk as [eps0 [Heps0 [N0 HN0]]].
  destruct Hneg as [eps [Heps [N HN]]].
  assert (Hm0 : NatLe N0 (Nat.max N0 N)) by (apply NatLe_lift; lia).
  assert (Hm1 : NatLe N (Nat.max N0 N)) by (apply NatLe_lift; lia).
  specialize (HN0 _ Hm0). specialize (HN _ Hm1).
  apply QltT_to_Qlt in HN0. apply QltT_to_Qlt in HN.
  apply QltT_to_Qlt in Heps0. apply QltT_to_Qlt in Heps.
  rewrite (real_mult_proj (lgw_rpow kappa j) TV0 (Nat.max N0 N)) in HN0.
  rewrite (lgwe_diff_proj kappa TV0 budget j (Nat.max N0 N)) in HN.
  assert (Hz0 : projT1 real_zero (Nat.max N0 N) == 0) by reflexivity.
  rewrite Hz0 in HN.
  set (X := projT1 budget (Nat.max N0 N)
            - projT1 (lgw_rpow kappa j) (Nat.max N0 N) * projT1 TV0 (Nat.max N0 N)) in *.
  (* HN0 : eps0 < X ；HN : eps < 0 − X ⟹ X < −eps *)
  assert (HX : X < - eps).
  { apply (proj1 (Qplus_lt_r X (- eps) eps)).
    assert (Hr1 : eps + - eps == 0) by ring.
    rewrite Hr1.
    assert (Ht : X + eps < X + (0 - X))
      by (apply (proj2 (Qplus_lt_r eps (0 - X) X)); exact HN).
    assert (Hr2 : X + (0 - X) == 0) by ring.
    rewrite Hr2 in Ht.
    assert (Hr3 : eps + X == X + eps) by ring.
    rewrite Hr3. exact Ht. }
  assert (Hcol : eps0 < - eps) by (exact (Qlt_trans _ _ _ HN0 HX)).
  assert (Hsum : eps0 + eps < 0).
  { assert (Ht : eps + eps0 < 0).
    { assert (Ht2 : eps + eps0 < eps + - eps)
        by (apply (proj2 (Qplus_lt_r eps0 (- eps) eps)); exact Hcol).
      assert (Hr1 : eps + - eps == 0) by ring.
      rewrite Hr1 in Ht2. exact Ht2. }
    assert (Hr2 : eps + eps0 == eps0 + eps) by ring.
    rewrite Hr2 in Ht. exact Ht. }
  assert (Hpos : 0 < eps0 + eps).
  { assert (Ht : 0 + 0 < eps0 + eps) by (apply Qplus_lt_compat; assumption).
    assert (Hr : 0 + 0 == 0) by ring.
    rewrite Hr in Ht. exact Ht. }
  destruct (Qlt_irrefl (eps0 + eps)
             (Qlt_trans (eps0 + eps) 0 (eps0 + eps) Hsum Hpos)).
Qed.

(* 逐站判定主件：rLPO 独力供给（归零支短路否证照 L3；离零支经符号支两账）    *)
Theorem lgwd_station_decide :
  forall (kappa TV0 budget : Real) (j : nat),
  rLPO -> lgwe_station_dec kappa TV0 budget j.
Proof.
  intros kappa TV0 budget j Hrlpo.
  destruct (Hrlpo (lgwe_diff kappa TV0 budget j)) as [Hap | Hzero].
  - destruct (lgwd_sign_of_apart _ Hap) as [Hpos | Hneg].
    + apply inl. exact (lgwe_test_of_diff kappa TV0 budget j Hpos).
    + apply inr. exact (lgwd_test_refute_of_neg kappa TV0 budget j Hneg).
  - apply inr. exact (lgwe_test_refute_of_zero kappa TV0 budget j Hzero).
Qed.

(* ============================================================ *)
(* Part 2：件① 修正规格 + 件② 可证支                                        *)
(* ============================================================ *)

(* 件①：带四前提的最小站选择器（两账形照 N2 lgw_min_sel_spec 逐字复用；      *)
(*   四前提恰好排除 L3 自撞点 κ=TV₀=B=1） *)
Definition lgwd_MinSelD : Set :=
  forall kappa TV0 budget : Real,
    real_lt real_zero kappa -> real_lt kappa real_one ->
    real_lt real_zero TV0 -> real_lt real_zero budget ->
    sigT (fun k : nat => lgw_min_sel_spec kappa TV0 budget k).

(* 件②：rLPO -> 四前提 -> lgwd_MinSelD（上界=mix_k_select；逐站判定=        *)
(*   Part 1 新支；线性扫=L3 lgwe_scan 原件；幂列重述=L3 lgwe_rpow_eq_tv）   *)
Theorem lgwd_inhabited : rLPO -> lgwd_MinSelD.
Proof.
  intros Hrlpo kappa TV0 budget Hk1 Hk2 Ha Hb.
  (* 必过站上界：mix_k_select（严格正 TV₀ 经 real_lt_le_iff_req 换 le 形） *)
  assert (Hale : real_le real_zero TV0).
  { apply (RealSetoid.real_lt_le_iff_req real_zero TV0). left. exact Ha. }
  destruct (mix_k_select kappa TV0 budget Hk1 Hk2 Hale Hb) as [kp Hmix].
  (* tv_rpow 形重述回 lgw_test 面（L3 原桥） *)
  assert (Hpass : lgw_test kappa TV0 budget kp).
  { unfold lgw_test.
    apply (real_eq_lt_lt (real_mult (lgw_rpow kappa kp) TV0)
                         (real_mult (tv_rpow kappa kp) TV0) budget).
    - apply (RealSetoid.real_eq_mult_compat (lgw_rpow kappa kp) TV0
                (tv_rpow kappa kp) TV0).
      + exact (lgwe_rpow_eq_tv kappa kp).
      + apply real_eq_refl.
    - exact Hmix. }
  (* 逐站可判定测试：rLPO 全供给（本件新支） *)
  assert (Hdec : forall j : nat, lgwe_station_dec kappa TV0 budget j).
  { intros j. exact (lgwd_station_decide kappa TV0 budget j Hrlpo). }
  (* 线性扫 [0,k_pass] + 两账封装（L3 lgwe_scan 原件） *)
  destruct (lgwe_scan kappa TV0 budget Hdec kp) as [[k [Hk Hspec]] | Hall].
  - exists k. exact Hspec.
  - assert (Hkk : NatLe kp kp) by (apply NatLe_lift; lia).
    destruct (Hall kp Hkk Hpass).
Qed.

(* ============================================================ *)
(* Part 3：件③ 非空虚归约支（half 三站实例——最小站数值即序信息）            *)
(* ============================================================ *)

(* half 常量的两前提（选择器实例化时反复使用） *)
Lemma lgwd_half_pos : real_lt real_zero lgw_half.
Proof.
  unfold real_lt. exists (1#4). split.
  - apply Qlt_to_QltT. exact (proj2 (Qlt_alt 0 (1#4)) (@eq_refl comparison Lt)).
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    exact (proj2 (Qlt_alt (1#4) (projT1 lgw_half n - projT1 real_zero n))
             (@eq_refl comparison Lt)).
Qed.

Lemma lgwd_half_lt_one : real_lt lgw_half real_one.
Proof.
  unfold real_lt. exists (1#4). split.
  - apply Qlt_to_QltT. exact (proj2 (Qlt_alt 0 (1#4)) (@eq_refl comparison Lt)).
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    exact (proj2 (Qlt_alt (1#4) (projT1 real_one n - projT1 lgw_half n))
             (@eq_refl comparison Lt)).
Qed.

(* 件③ 主件：选择器施于 (κ,B,x):=(half,half,x)，x∈(0,1]：                   *)
(*   最小站 k=0 ⟹ x<half ⟹ x<1；k=1 ⟹ x<1；k≥2 ⟹ 站 1 否证，与前件 x≤1     *)
(*   的左支相撞出空、右支（x=1）随取——序证书从最小站账提取，非前件直投影。   *)
Theorem lgwd_decision : lgwd_MinSelD ->
  forall x : Real, real_lt real_zero x -> real_le x real_one ->
    Or (real_lt x real_one) (real_eq x real_one).
Proof.
  intros HselD x Hx0 Hx1.
  destruct (HselD lgw_half x lgw_half
              lgwd_half_pos lgwd_half_lt_one Hx0 lgwd_half_pos) as [k Hacc].
  destruct Hacc as [Htk Hbel].
  destruct k as [| [| m]].
  - apply inl. exact (lgw_test0_lt_one x Htk).
  - apply inl. exact (lgw_test1_lt_one x Htk).
  - assert (Href1 : lgw_test lgw_half x lgw_half 1%nat -> Empty_set).
    { intros Ht1. apply (Hbel 1%nat).
      - apply NatLe_lift. lia.
      - exact Ht1. }
    destruct Hx1 as [Hlt1 | Heq1].
    + destruct (Href1 (lgw_test1_of_lt_one x Hlt1)).
    + apply inr. exact Heq1.
Qed.

(* 锐化件：免 x≤1 前件——「x<1 可判定」对一切 0<x 成立，结论非任何前件投影，  *)
(*   为归约支非平凡性的独立判据 *)
Definition lgwd_station_decD (x : Real) : Set :=
  Or (real_lt x real_one) (real_lt x real_one -> Empty_set).

Theorem lgwd_decision_dec : lgwd_MinSelD ->
  forall x : Real, real_lt real_zero x -> lgwd_station_decD x.
Proof.
  intros HselD x Hx0.
  destruct (HselD lgw_half x lgw_half
              lgwd_half_pos lgwd_half_lt_one Hx0 lgwd_half_pos) as [k Hacc].
  destruct Hacc as [Htk Hbel].
  destruct k as [| [| m]].
  - apply inl. exact (lgw_test0_lt_one x Htk).
  - apply inl. exact (lgw_test1_lt_one x Htk).
  - assert (Href1 : lgw_test lgw_half x lgw_half 1%nat -> Empty_set).
    { intros Ht1. apply (Hbel 1%nat).
      - apply NatLe_lift. lia.
      - exact Ht1. }
    apply inr. intros Hlt1.
    destruct (Href1 (lgw_test1_of_lt_one x Hlt1)).
Qed.

(* ============================================================ *)
(* Part 4：件④ 等价定装 + 对照注记件                                        *)
(* ============================================================ *)

(* LPO 实例面：(0,1] 上序分解决策族（件③ 重述目标） *)
Definition lgwd_lpo_family : Set :=
  forall x : Real, real_lt real_zero x -> real_le x real_one ->
    Or (real_lt x real_one) (real_eq x real_one).

(* 等价定装：⟸=件② 特化（rLPO 建逐点选择器，四前提真实使用）；              *)
(*   ⟹=件③+LPO 实例重述（选择器出序证书族）。S01 Set-And 承载（Set 支不可   *)
(*   入 Prop 合取，照 L3/AA15R 口径）。 *)
Theorem lgwd_equivalence : forall kappa TV0 budget : Real,
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_lt real_zero TV0 -> real_lt real_zero budget ->
  And (lgwd_MinSelD -> lgwd_lpo_family)
      (rLPO -> sigT (fun k : nat => lgw_min_sel_spec kappa TV0 budget k)).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hb. split.
  - intros HselD x Hx0 Hx1. exact (lgwd_decision HselD x Hx0 Hx1).
  - intros Hrlpo. exact (lgwd_inhabited Hrlpo kappa TV0 budget Hk1 Hk2 Ha Hb).
Qed.

(* 对照注记件：使用 L3 发现件——无前件全称形构造性可驳（空 Set），            *)
(*   故四前提必要；对照留存于 UpAblLogWallEq。 *)
Theorem lgwd_contrast_refutable : lgw_MinSel -> Empty_set.
Proof. exact lgwe_minsel_refutable. Qed.

(* ============================================================ *)
(* Part 5：摘要输出（G2/G3 关卡面）                                          *)
(* ============================================================ *)

Print Assumptions lgwd_MinSelD.
Print Assumptions lgwd_station_decide.
Print Assumptions lgwd_inhabited.
Print Assumptions lgwd_decision.
Print Assumptions lgwd_decision_dec.
Print Assumptions lgwd_equivalence.
Print Assumptions lgwd_contrast_refutable.
Print Assumptions lgwd_sign_of_apart.
Print Assumptions lgwd_test_refute_of_neg.

Separate Extraction lgwd_MinSelD lgwd_lpo_family lgwd_station_decide
  lgwd_inhabited lgwd_decision lgwd_decision_dec lgwd_equivalence.

(* ============================ §20 局限(1b)·神谕 Real 层对数选择器 ============================ *)
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Extraction.
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
Require Import UpTVDoeblin.
Require Import UpReqIterGeomRate.
Require Import UpReqMixLogB.
Require Import KLWallClosed.
Require Import RateTheoryAblation.
Require Import UpRealLeB.
Require Import G07_KLWall.

(* ============================================================ *)
(* Part 0：换形小件（real_le_b 的两侧 eq 运载；real_le 侧使用                   *)
(*   RealSetoid.real_le_compat 既有件）                                       *)
(* ============================================================ *)

Lemma loso_le_b_compat : forall x y x' y' : Real,
  real_eq x x' -> real_eq y y' -> real_le_b x y -> real_le_b x' y'.
Proof.
  intros x y x' y' Hx Hy Hb. unfold real_le_b in *. intros eps Heps.
  apply (RealSetoid.real_lt_compat x x' (real_plus y eps) (real_plus y' eps)).
  - exact Hx.
  - exact (RealSetoid.real_eq_plus_compat y eps y' eps Hy (real_eq_refl eps)).
  - exact (Hb eps Heps).
Qed.

(* ============================================================ *)
(* Part 1：件① 探测前件（loso_test_oracle）+ 检验 + 语义桥 + 神谕在场实证       *)
(* ============================================================ *)

(* 每站语义两账：真支供隙（real_lt），假支否证（real_le budget ≤ κ^k·TV₀）。 *)
(* bool 等式取基座 Id（Set 层恒等族）——语句面全 Set。                       *)
Definition loso_sem (kappa TV0 budget : Real) (b : bool) (k : nat) : Set :=
  And (Id b true -> real_lt (real_mult (tv_rpow kappa k) TV0) budget)
      (Id b false -> real_le budget (real_mult (tv_rpow kappa k) TV0)).

(* 件①：逐站可判定探测的诚实前件（神谕形）。 *)
Definition loso_test_oracle (kappa TV0 budget : Real) : Set :=
  forall k : nat, sigT (fun b : bool => loso_sem kappa TV0 budget b k).

(* 检验件：神谕第 k 站返回的 bool——直接代入泛型搜索核的 test 函数。 *)
Definition loso_probe (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget) : nat -> bool :=
  fun k => projT1 (Htest k).

(* Prop 面桥（Qed 伴生，不入提取签名）：探测真 ⟹ 供隙。 *)
Lemma loso_oracle_true_lt : forall (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget) (k : nat),
  loso_probe kappa TV0 budget Htest k = true ->
  real_lt (real_mult (tv_rpow kappa k) TV0) budget.
Proof.
  intros kappa TV0 budget Htest k H. unfold loso_probe in H.
  destruct (Htest k) as [b Hcert] eqn:EH.
  cbn [projT1] in H. subst b.
  destruct Hcert as [Hc1 Hc2]. exact (Hc1 (@id_refl bool true)).
Qed.

(* Prop 面桥（Qed 伴生）：探测假 ⟹ 否证。 *)
Lemma loso_oracle_false_le : forall (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget) (k : nat),
  loso_probe kappa TV0 budget Htest k = false ->
  real_le budget (real_mult (tv_rpow kappa k) TV0).
Proof.
  intros kappa TV0 budget Htest k H. unfold loso_probe in H.
  destruct (Htest k) as [b Hcert] eqn:EH.
  cbn [projT1] in H. subst b.
  destruct Hcert as [Hc1 Hc2]. exact (Hc2 (@id_refl bool false)).
Qed.

(* —— 神谕在场实证钉（N2 lgw_oracle_pin 的正向对偶）：const 层本前件可实现 —— *)
(*    （Qcompare 可判定分裂供 bool，mixb const 桥供 Real 语义两账）——本前件    *)
(*    非空泛假设，序判定缺位仅在离开 const 层处成墙。                          *)
Lemma loso_oracle_const : forall (a v b0 : Q),
  loso_test_oracle (real_const a) (real_const v) (real_const b0).
Proof.
  intros a v b0 k.
  pose (X := (Qmult (igr_qpow a k) v)%Q).
  assert (Heq : real_eq (real_mult (tv_rpow (real_const a) k) (real_const v))
                  (real_const X)).
  { apply (real_eq_trans
             (real_mult (tv_rpow (real_const a) k) (real_const v))
             (real_mult (real_const (igr_qpow a k)) (real_const v))
             (real_const X)).
    - exact (RealSetoid.real_eq_mult_compat (tv_rpow (real_const a) k)
               (real_const v) (real_const (igr_qpow a k)) (real_const v)
               (mixb_const_rpow_eq a k) (real_eq_refl (real_const v))).
    - exact (real_eq_sym (real_const (Qmult (igr_qpow a k) v))
               (real_mult (real_const (igr_qpow a k)) (real_const v))
               (mixb_const_mult (igr_qpow a k) v)). }
  assert (Heqs : real_eq (real_const X)
                   (real_mult (tv_rpow (real_const a) k) (real_const v))).
  { exact (real_eq_sym (real_mult (tv_rpow (real_const a) k) (real_const v))
             (real_const X) Heq). }
  destruct (Qcompare b0 X) eqn:E.
  - (* Eq：假支（否证） *)
    unfold Qcompare in E.
    pose proof (proj1 (Z.compare_eq_iff (Qnum b0 * QDen X)%Z
                         (Qnum X * QDen b0)%Z) E) as Hze.
    exists false. split.
    + intro Hid. inversion Hid.
    + intro Hdead.
      exact (RealSetoid.real_le_compat (real_const b0) (real_const b0)
               (real_const X)
               (real_mult (tv_rpow (real_const a) k) (real_const v))
               (real_eq_refl (real_const b0)) Heqs
               (mixb_qle_const_le b0 X (qeq_le b0 X Hze))).
  - (* Lt：假支（否证） *)
    unfold Qcompare in E.
    pose proof (proj1 (Z.compare_lt_iff (Qnum b0 * QDen X)%Z
                         (Qnum X * QDen b0)%Z) E) as Hzl.
    exists false. split.
    + intro Hid. inversion Hid.
    + intro Hdead.
      exact (RealSetoid.real_le_compat (real_const b0) (real_const b0)
               (real_const X)
               (real_mult (tv_rpow (real_const a) k) (real_const v))
               (real_eq_refl (real_const b0)) Heqs
               (mixb_qle_const_le b0 X (Qlt_le_weak b0 X Hzl))).
  - (* Gt：真支（供隙）——Z.compare_gt_iff 直接回取 Qlt X b0 *)
    unfold Qcompare in E.
    pose proof (proj1 (Z.compare_gt_iff (Qnum b0 * QDen X)%Z
                         (Qnum X * QDen b0)%Z) E) as Hzg.
    exists true. split.
    + intro Hdead.
      exact (RealSetoid.real_lt_compat (real_const X)
               (real_mult (tv_rpow (real_const a) k) (real_const v))
               (real_const b0) (real_const b0)
               (real_eq_sym (real_mult (tv_rpow (real_const a) k)
                                 (real_const v)) (real_const X) Heq)
               (real_eq_refl (real_const b0))
               (mixb_Qlt_const_lt X b0 Hzg)).
    + intro Hid. inversion Hid.
Qed.

(* ============================================================ *)
(* Part 2：单调性支——幂列递减                                                  *)
(*   (a) 实形使用轨（Bishop 形，klc_closed_powb_mono / rta_strict_branch_real）*)
(*   (b) 本件承重轨（Or 编码 real_le 形，直接归纳）                            *)
(* ============================================================ *)

(* —— (a) 轨一：klc_closed_powb_mono 实形（底 1−κ，0≤κ≤1 全量）经             *)
(*    rta_rpow_powb_eq 运载至 tv_rpow（rta_omd_powb_mono_b 同法） —— *)
(* —— (a) 轨运载器：powb_pow ⟶ tv_rpow 的 Bishop 单调迁移（rta §5 同法） —— *)
Lemma loso_le_b_rpow_transport : forall (B : Real) (m n : nat),
  real_le_b (powb_pow B m) (powb_pow B n) ->
  real_le_b (tv_rpow B m) (tv_rpow B n).
Proof.
  intros B m n Hbb.
  apply (loso_le_b_compat (powb_pow B m) (powb_pow B n)).
  - exact (real_eq_sym (tv_rpow B m) (powb_pow B m) (rta_rpow_powb_eq B m)).
  - exact (real_eq_sym (tv_rpow B n) (powb_pow B n) (rta_rpow_powb_eq B n)).
  - exact Hbb.
Qed.

Lemma loso_powb_mono_b : forall (kappa : Real) (j j' : nat),
  real_le real_zero kappa -> real_le kappa real_one -> (j <= j')%nat ->
  real_le_b (tv_rpow (real_plus real_one (real_opp kappa)) j')
            (tv_rpow (real_plus real_one (real_opp kappa)) j).
Proof.
  intros kappa j j' H0 H1 Hjj.
  apply (loso_le_b_rpow_transport (real_plus real_one (real_opp kappa)) j' j).
  exact (klc_closed_powb_mono kappa j j' H0 H1 (NatLe_lift j j' Hjj)).
Qed.

(* —— (a) 轨二：rta_strict_branch_real 实形（0≤κ<1 严格支封装）运载 —— *)
Lemma loso_strict_shrink : forall (kappa : Real) (j j' : nat),
  real_le real_zero kappa -> real_lt kappa real_one -> (j <= j')%nat ->
  prod (real_lt real_zero (real_plus real_one (real_opp kappa)))
       (real_le_b (tv_rpow (real_plus real_one (real_opp kappa)) j')
                  (tv_rpow (real_plus real_one (real_opp kappa)) j)).
Proof.
  intros kappa j j' H0 Hlt Hjj.
  pose proof (rta_strict_branch_real kappa j j' H0 Hlt (NatLe_lift j j' Hjj))
    as [Hpos Hbb].
  split.
  - exact Hpos.
  - apply (loso_le_b_rpow_transport (real_plus real_one (real_opp kappa)) j' j).
    exact Hbb.
Qed.

(* —— (b) 轨关键件：Or 编码 real_le 形幂非负不变量 —— *)
Lemma loso_rpow_nonneg : forall (kappa : Real) (k : nat),
  real_le real_zero kappa -> real_le real_zero (tv_rpow kappa k).
Proof.
  intros kappa k H0. induction k as [| m IH].
  - exact (inl real_lt_zero_one).
  - cbn [tv_rpow].
    apply (real_le_trans real_zero (real_mult real_zero (tv_rpow kappa m))
             (real_mult kappa (tv_rpow kappa m))).
    + apply (RealSetoid.real_eq_le real_zero
               (real_mult real_zero (tv_rpow kappa m))).
      exact (real_eq_sym (real_mult real_zero (tv_rpow kappa m)) real_zero
               (real_eq_trans (real_mult real_zero (tv_rpow kappa m))
                  (real_mult (tv_rpow kappa m) real_zero) real_zero
                  (real_mult_comm real_zero (tv_rpow kappa m))
                  (real_mult_zero (tv_rpow kappa m)))).
    + exact (real_le_mult_compat_weak real_zero kappa (tv_rpow kappa m) IH H0).
Qed.

(* —— (b) 轨关键件：单步递减 κ^{S m} ≤ κ^m（0≤κ≤1） —— *)
Lemma loso_rpow_step_le : forall (kappa : Real) (m : nat),
  real_le real_zero kappa -> real_le kappa real_one ->
  real_le (tv_rpow kappa (Datatypes.S m)) (tv_rpow kappa m).
Proof.
  intros kappa m H0 H1.
  pose proof (loso_rpow_nonneg kappa m H0) as Hnn.
  cbn [tv_rpow].
  apply (real_le_trans (real_mult kappa (tv_rpow kappa m))
           (real_mult real_one (tv_rpow kappa m)) (tv_rpow kappa m)).
  - exact (real_le_mult_compat_weak kappa real_one (tv_rpow kappa m) Hnn H1).
  - exact (RealSetoid.real_eq_le (real_mult real_one (tv_rpow kappa m))
             (tv_rpow kappa m)
             (real_eq_trans (real_mult real_one (tv_rpow kappa m))
                (real_mult (tv_rpow kappa m) real_one) (tv_rpow kappa m)
                (real_mult_comm real_one (tv_rpow kappa m))
                (real_mult_one (tv_rpow kappa m)))).
Qed.

(* —— (b) 轨主件：全量指数单调 κ^{j'} ≤ κ^j（0≤κ≤1，Or 编码 real_le 形）。
   klc_powb_mono_weak 同款 nat 归纳 + NatLe_lift/drop 桥绕行）—— *)
Lemma loso_rpow_dec_le : forall (kappa : Real) (j j' : nat),
  real_le real_zero kappa -> real_le kappa real_one -> NatLe j j' ->
  real_le (tv_rpow kappa j') (tv_rpow kappa j).
Proof.
  intros kappa j j' H0 H1. revert j. induction j' as [| m IH]; intros j Hjj.
  - (* j' = 0：NatLe j 0 ⟹ j = 0（leb (S n) 0 ≡ false 爆破） *)
    destruct j as [| n].
    + exact (real_le_refl (tv_rpow kappa 0%nat)).
    + exfalso.
      unfold NatLe in Hjj.
      pose proof (@id_trans bool (Nat.leb (Datatypes.S n) 0%nat) false true
                    (@id_refl bool false) Hjj) as Hbad.
      inversion Hbad.
  - (* j' = S m：leb j m 分裂（klc_powb_mono_weak 同法） *)
    destruct (Nat.leb j m) eqn:E2.
    + apply (real_le_trans (tv_rpow kappa (Datatypes.S m))
               (tv_rpow kappa m) (tv_rpow kappa j)).
      * exact (loso_rpow_step_le kappa m H0 H1).
      * apply IH. apply (NatLe_lift j m).
        exact (proj1 (Nat.leb_le j m) E2).
    + pose proof (proj1 (Nat.leb_gt j m) E2) as Hgt.
      pose proof (NatLe_drop j (Datatypes.S m) Hjj) as Hjle.
      assert (Heq : j = Datatypes.S m) by lia.
      rewrite Heq. exact (real_le_refl (tv_rpow kappa (Datatypes.S m))).
Qed.

(* ============================================================ *)
(* Part 3：检验单调账（真支供隙+假支否证+幂列递减 ⟹ 过站集上闭）               *)
(* ============================================================ *)

Lemma loso_probe_mono : forall (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget),
  real_le real_zero kappa -> real_le kappa real_one ->
  real_le real_zero TV0 ->
  mixb_mono (loso_probe kappa TV0 budget Htest).
Proof.
  intros kappa TV0 budget Htest Hk0 Hk1 Ha j j' Hjj Hj.
  pose proof (loso_rpow_dec_le kappa j j' Hk0 Hk1 (NatLe_lift j j' Hjj))
    as Hdec.
  (* 站 j 语义：探测真 ⟹ κ^j·TV₀ < budget *)
  assert (Hltj : real_lt (real_mult (tv_rpow kappa j) TV0) budget).
  { exact (loso_oracle_true_lt kappa TV0 budget Htest j Hj). }
  (* 站 j' 语义取支 *)
  destruct (Htest j') as [b Hcert] eqn:Ej'.
  unfold loso_probe. rewrite Ej'. cbn [projT1].
  destruct b as [].
  - reflexivity.
  - exfalso.
    (* 假支语义证书：budget ≤ κ^{j'}·TV₀ *)
    destruct Hcert as [Hc1 Hc2].
    pose proof (Hc2 (@id_refl bool false)) as Hlej'.
    (* 幂列递减 × 乘法弱保序 ⟹ budget ≤ κ^j·TV₀，与供隙支相撞 *)
    assert (Hmul : real_le (real_mult (tv_rpow kappa j') TV0)
                     (real_mult (tv_rpow kappa j) TV0))
      by exact (real_le_mult_compat_weak (tv_rpow kappa j')
                  (tv_rpow kappa j) TV0 Ha Hdec).
    assert (Hbl : real_le budget (real_mult (tv_rpow kappa j) TV0))
      by exact (real_le_trans budget (real_mult (tv_rpow kappa j') TV0)
                  (real_mult (tv_rpow kappa j) TV0) Hlej' Hmul).
    unfold real_le in Hbl. destruct Hbl as [Hltb | Heqb].
    + exact (match (real_lt_irrefl (real_mult (tv_rpow kappa j) TV0)
                     (real_lt_trans (real_mult (tv_rpow kappa j) TV0) budget
                        (real_mult (tv_rpow kappa j) TV0) Hltj Hltb)) with end).
    + exact (match (real_lt_irrefl (real_mult (tv_rpow kappa j) TV0)
                     (RealSetoid.real_lt_compat
                        (real_mult (tv_rpow kappa j) TV0)
                        (real_mult (tv_rpow kappa j) TV0)
                        budget (real_mult (tv_rpow kappa j) TV0)
                        (real_eq_refl (real_mult (tv_rpow kappa j) TV0))
                        Heqb Hltj)) with end).
Qed.

(* ============================================================ *)
(* Part 4：件③ 账面——Prop 三账 + Real 侧语义两账                              *)
(* ============================================================ *)

(* 三账（Prop 面，mixb_qsel_account_ex 神谕化副本）：返回站通过、以下全败、      *)
(* 比较数对数级（fuel 双相 2+⌊log₂K⌋ 配给，量级 2·log₂K+5）。 *)
Theorem loso_sel_accounts : forall (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget)
  (Hk0 : real_le real_zero kappa) (Hk1 : real_le kappa real_one)
  (Ha : real_le real_zero TV0)
  (K r c : nat),
  (2 <= K)%nat ->
  loso_probe kappa TV0 budget Htest 0%nat = false ->
  (exists k : nat, (k <= K)%nat /\
                   loso_probe kappa TV0 budget Htest k = true) ->
  mixb_sel (loso_probe kappa TV0 budget Htest)
    (Datatypes.S (Datatypes.S (Nat.log2 K)))
    (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r, c) ->
  loso_probe kappa TV0 budget Htest r = true /\
  (forall j : nat, (j < r)%nat ->
                   loso_probe kappa TV0 budget Htest j = false) /\
  (c <= 2 * (Nat.log2 K) + 5)%nat.
Proof.
  intros kappa TV0 budget Htest Hk0 Hk1 Ha K r c HK2 Hmiss0 Hhit Hsel.
  pose proof (loso_probe_mono kappa TV0 budget Htest Hk0 Hk1 Ha) as Hmono.
  destruct Hhit as [k0 [Hk0K Hk0pass]].
  destruct (igr_k_enum (loso_probe kappa TV0 budget Htest) K) as [kmin|]
    eqn:Eenum.
  - (* 窗内最小通过站命中：mixb_sel_scale 量级记录收束 *)
    pose proof (igr_k_enum_sound _ _ _ Eenum) as Hpassmin.
    pose proof (igr_k_enum_min _ _ _ Eenum) as Hminmin.
    pose proof (mixb_enum_le _ _ _ Eenum) as HminK.
    assert (Hkmin1 : (1 <= kmin)%nat).
    { destruct kmin as [| m].
      - rewrite Hmiss0 in Hpassmin. discriminate Hpassmin.
      - exact (le_n_S 0 m (le_0_n m)). }
    destruct (mixb_sel_scale (loso_probe kappa TV0 budget Htest) K kmin r c
                Hmono Hmiss0 Hpassmin Hminmin Hkmin1 HminK HK2 Hsel)
      as [Hr Hc].
    rewrite Hr. split.
    + exact Hpassmin.
    + split.
      * exact Hminmin.
      * exact Hc.
  - (* None 支与窗命中假设相撞 *)
    exfalso.
    pose proof (igr_k_enum_none (loso_probe kappa TV0 budget Htest) K Eenum
                  k0 Hk0K) as HF.
    rewrite Hk0pass in HF. discriminate HF.
Qed.

(* Real 侧通过账（真支供隙）：输出站 r 处 κ^r·TV₀ < budget。 *)
Theorem loso_sel_pass : forall (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget)
  (Hk0 : real_le real_zero kappa) (Hk1 : real_le kappa real_one)
  (Ha : real_le real_zero TV0)
  (K r c : nat),
  (2 <= K)%nat ->
  loso_probe kappa TV0 budget Htest 0%nat = false ->
  (exists k : nat, (k <= K)%nat /\
                   loso_probe kappa TV0 budget Htest k = true) ->
  mixb_sel (loso_probe kappa TV0 budget Htest)
    (Datatypes.S (Datatypes.S (Nat.log2 K)))
    (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r, c) ->
  real_lt (real_mult (tv_rpow kappa r) TV0) budget.
Proof.
  intros kappa TV0 budget Htest Hk0 Hk1 Ha K r c HK2 Hmiss0 Hhit Hsel.
  destruct (loso_sel_accounts kappa TV0 budget Htest Hk0 Hk1 Ha K r c
               HK2 Hmiss0 Hhit Hsel) as [Hpass _].
  exact (loso_oracle_true_lt kappa TV0 budget Htest r Hpass).
Qed.

(* Real 侧全败账（假支否证）：j < r ⟹ budget ≤ κ^j·TV₀（真最小站下向界，       *)
(* mixa_min_real_below 形的神谕化副本）。                                      *)
Theorem loso_sel_below_fail : forall (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget)
  (Hk0 : real_le real_zero kappa) (Hk1 : real_le kappa real_one)
  (Ha : real_le real_zero TV0)
  (K r c : nat),
  (2 <= K)%nat ->
  loso_probe kappa TV0 budget Htest 0%nat = false ->
  (exists k : nat, (k <= K)%nat /\
                   loso_probe kappa TV0 budget Htest k = true) ->
  mixb_sel (loso_probe kappa TV0 budget Htest)
    (Datatypes.S (Datatypes.S (Nat.log2 K)))
    (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r, c) ->
  forall j : nat, (j < r)%nat ->
    real_le budget (real_mult (tv_rpow kappa j) TV0).
Proof.
  intros kappa TV0 budget Htest Hk0 Hk1 Ha K r c HK2 Hmiss0 Hhit Hsel
    j Hj.
  destruct (loso_sel_accounts kappa TV0 budget Htest Hk0 Hk1 Ha K r c
               HK2 Hmiss0 Hhit Hsel) as [Hpass Hrest].
  destruct Hrest as [Hmin _].
  exact (loso_oracle_false_le kappa TV0 budget Htest j (Hmin j Hj)).
Qed.

(* ============================================================ *)
(* Part 5：件② 对数选择器（Defined sigT 可提取）+ le 形（§6.3 先例同构）        *)
(* ============================================================ *)

Definition loso_k_select_log (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget)
  (Hk0 : real_le real_zero kappa) (Hk1 : real_le kappa real_one)
  (Ha : real_le real_zero TV0)
  (K : nat) (HK2 : (2 <= K)%nat)
  (Hmiss0 : loso_probe kappa TV0 budget Htest 0%nat = false)
  (Hhit : exists k : nat, (k <= K)%nat /\
                          loso_probe kappa TV0 budget Htest k = true)
  : sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  destruct (mixb_sel (loso_probe kappa TV0 budget Htest)
              (Datatypes.S (Datatypes.S (Nat.log2 K)))
              (Datatypes.S (Datatypes.S (Nat.log2 K)))) as [r c] eqn:Hsel.
  exists r.
  exact (loso_sel_pass kappa TV0 budget Htest Hk0 Hk1 Ha K r c
           HK2 Hmiss0 Hhit Hsel).
Defined.

(* le 形（§6.3 le 形诚实前件先例同构：real_lt_le_iff_req 左支直给） *)
Definition loso_k_select_log_le (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget)
  (Hk0 : real_le real_zero kappa) (Hk1 : real_le kappa real_one)
  (Ha : real_le real_zero TV0)
  (K : nat) (HK2 : (2 <= K)%nat)
  (Hmiss0 : loso_probe kappa TV0 budget Htest 0%nat = false)
  (Hhit : exists k : nat, (k <= K)%nat /\
                          loso_probe kappa TV0 budget Htest k = true)
  : sigT (fun k : nat => real_le (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  destruct (loso_k_select_log kappa TV0 budget Htest Hk0 Hk1 Ha K HK2
              Hmiss0 Hhit) as [k Hk].
  exists k.
  exact (RealSetoid.real_lt_le_iff_req (real_mult (tv_rpow kappa k) TV0)
           budget (inl Hk)).
Defined.

(* ============================================================ *)
(* Part 6：审计口（G2/G3 关卡面）                                              *)
(* ============================================================ *)

Print Assumptions loso_sem.
Print Assumptions loso_test_oracle.
Print Assumptions loso_probe.
Print Assumptions loso_oracle_true_lt.
Print Assumptions loso_oracle_false_le.
Print Assumptions loso_oracle_const.
Print Assumptions loso_powb_mono_b.
Print Assumptions loso_strict_shrink.
Print Assumptions loso_rpow_nonneg.
Print Assumptions loso_rpow_step_le.
Print Assumptions loso_rpow_dec_le.
Print Assumptions loso_probe_mono.
Print Assumptions loso_sel_accounts.
Print Assumptions loso_sel_pass.
Print Assumptions loso_sel_below_fail.
Print Assumptions loso_k_select_log.
Print Assumptions loso_k_select_log_le.

Separate Extraction loso_sem loso_test_oracle loso_probe loso_k_select_log loso_k_select_log_le.

(* ============================ §21 二叉决策树归纳类型基建件 ============================ *)
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

(* ============ ① dtree 归纳类型 + 计数 Fixpoint ============ *)

Inductive dtree : Type :=
| dt_leaf : nat -> dtree              (* 叶：标注答案值 *)
| dt_node : dtree -> dtree -> dtree.  (* 内部：左/右子树 *)

(* 叶数计数 *)
Fixpoint dt_leaves (t : dtree) : nat :=
  match t with
  | dt_leaf _ => 1
  | dt_node l r => dt_leaves l + dt_leaves r
  end.

(* 内部节点计数 *)
Fixpoint dt_internal (t : dtree) : nat :=
  match t with
  | dt_leaf _ => 0
  | dt_node l r => Datatypes.S (dt_internal l + dt_internal r)
  end.

(* 深度计数：叶深度 0，内部 1 + max(左深, 右深) *)
Fixpoint dt_depth (t : dtree) : nat :=
  match t with
  | dt_leaf _ => 0
  | dt_node l r => Datatypes.S (Nat.max (dt_depth l) (dt_depth r))
  end.

(* 叶答案值序列（按中序展开；提取面 list nat） *)
Fixpoint dt_leafvals (t : dtree) : list nat :=
  match t with
  | dt_leaf a => [a]
  | dt_node l r => dt_leafvals l ++ dt_leafvals r
  end.

(* 执行求值器：oracle 依当前子树定向（真支走左/假支走右），
   返回到达叶所标注的答案值。Set 面全可提取。 *)
Fixpoint dt_run_val (route : dtree -> bool) (t : dtree) : nat :=
  match t with
  | dt_leaf a => a
  | dt_node l r => if route (dt_node l r)
                   then dt_run_val route l
                   else dt_run_val route r
  end.

(* ============ 帮件：叶数恒正 ============ *)

Lemma dt_leaves_pos : forall t, (1 <= dt_leaves t)%nat.
Proof.
  induction t as [a | l IHl r IHr]; simpl; lia.
Qed.

(* ============ ② 结构引理：叶数 = 内部数 + 1 ============ *)

Lemma dt_leaves_eq : forall t, dt_leaves t = (dt_internal t + 1)%nat.
Proof.
  induction t as [a | l IHl r IHr]; simpl.
  - reflexivity.
  - simpl in IHl, IHr. lia.
Qed.

(* ============ ③ 结构引理：深度 ≥ log₂(叶数) ============ *)

Lemma dt_depth_ge_log2 : forall t,
  (1 <= dt_leaves t)%nat -> (Nat.log2 (dt_leaves t) <= dt_depth t)%nat.
Proof.
  induction t as [a | l IHl r IHr]; intros Hle.
  - cbn [dt_leaves dt_depth]. rewrite Nat.log2_1. lia.
  - assert (Hpl : (1 <= dt_leaves l)%nat) by apply dt_leaves_pos.
    assert (Hpr : (1 <= dt_leaves r)%nat) by apply dt_leaves_pos.
    specialize (IHl Hpl). specialize (IHr Hpr).
    cbn [dt_leaves dt_depth].
    set (m := Nat.max (dt_depth l) (dt_depth r)) in *.
    assert (Hml : (Nat.log2 (dt_leaves l) <= m)%nat) by (unfold m; lia).
    assert (Hmr : (Nat.log2 (dt_leaves r) <= m)%nat) by (unfold m; lia).
    (* 上界：两子树叶数各 < 2^(S m) ⇒ 和 < 2^(S (S m)) *)
    destruct (Nat.log2_spec (dt_leaves l) Hpl) as [A1 B1].
    destruct (Nat.log2_spec (dt_leaves r) Hpr) as [A2 B2].
    assert (P1 : (2 ^ (Datatypes.S (Nat.log2 (dt_leaves l))) <= 2 ^ (Datatypes.S m))%nat)
      by (apply Nat.pow_le_mono_r; lia).
    assert (P2 : (2 ^ (Datatypes.S (Nat.log2 (dt_leaves r))) <= 2 ^ (Datatypes.S m))%nat)
      by (apply Nat.pow_le_mono_r; lia).
    assert (Hlt : (dt_leaves l + dt_leaves r
                   < 2 ^ (Datatypes.S (Datatypes.S m)))%nat).
    { rewrite !Nat.pow_succ_r'.
      rewrite !Nat.pow_succ_r' in B1. rewrite !Nat.pow_succ_r' in B2.
      rewrite !Nat.pow_succ_r' in P1. rewrite !Nat.pow_succ_r' in P2.
      lia. }
    (* 和 < 2^(S (S m)) ⇒ log₂和 < S (S m) ⇒ log₂和 ≤ S m = 深度 *)
    assert (Hpos : (0 < dt_leaves l + dt_leaves r)%nat) by lia.
    assert (Hlog := proj1
      (Nat.log2_lt_pow2 (dt_leaves l + dt_leaves r) (Datatypes.S (Datatypes.S m)) Hpos) Hlt).
    lia.
Qed.

(* ============ ④ 正确性框架（BY-LB-1 计数供基） ============ *)

(* 求值器答案必落在叶值序列内（正确性挂钩件） *)
Lemma dt_run_val_leaf : forall (route : dtree -> bool) (t : dtree),
  In (dt_run_val route t) (dt_leafvals t).
Proof.
  intros route. induction t as [a | l IHl r IHr].
  - simpl. left. reflexivity.
  - simpl. destruct (route (dt_node l r)).
    + apply in_or_app. left. exact IHl.
    + apply in_or_app. right. exact IHr.
Qed.

(* 叶值序列长度 = 叶数（提取面桥） *)
Lemma dt_leafvals_len : forall t, length (dt_leafvals t) = dt_leaves t.
Proof.
  induction t as [a | l IHl r IHr]; simpl.
  - reflexivity.
  - rewrite length_app, IHl, IHr. reflexivity.
Qed.

(* 注入映射下序像无重复（seq 域上） *)
Lemma nodup_map_inj_range : forall (f : nat -> nat) (len start : nat),
  (forall i j, (i < start + len)%nat -> (j < start + len)%nat ->
               f i = f j -> i = j) ->
  NoDup (map f (seq start len)).
Proof.
  intros f len. induction len as [| len IHlen]; intros start Hinj.
  - simpl. constructor.
  - simpl. constructor.
    + intros HIn. apply in_map_iff in HIn. destruct HIn as [j [Hf Hj]].
      apply in_seq in Hj.
      assert (Hjs : j = start) by (apply Hinj; lia).
      lia.
    + apply IHlen. intros i j Hi Hj Hf. apply Hinj; lia.
Qed.

(* 计数引理（BY-LB-1 基座）：S K 个可能输入的答案值两两相异且
   全被树 t 的叶值序列覆盖 ⇒ 叶数 ≥ S K（各需一叶） *)
Lemma dt_leaves_ge_distinct : forall (t : dtree) (f : nat -> nat) (K : nat),
  (forall i, (i <= K)%nat -> In (f i) (dt_leafvals t)) ->
  (forall i j, (i <= K)%nat -> (j <= K)%nat -> f i = f j -> i = j) ->
  (Datatypes.S K <= dt_leaves t)%nat.
Proof.
  intros t f K Hcov Hinj.
  assert (Hnd : NoDup (map f (seq 0 (Datatypes.S K)))).
  { apply nodup_map_inj_range. intros i j Hi Hj Hf. apply Hinj; lia. }
  assert (Hincl : incl (map f (seq 0 (Datatypes.S K))) (dt_leafvals t)).
  { intros y Hy. apply in_map_iff in Hy. destruct Hy as [i [Heq Hi]].
    apply in_seq in Hi. subst y. apply Hcov. lia. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  rewrite length_map, length_seq in Hlen.
  rewrite <- dt_leafvals_len. exact Hlen.
Qed.

(* 下界主形（BY-LB-1 直接供基）：S K 个可能输入各需一叶 ⇒
   深度 ≥ log₂(S K) *)
Theorem dt_lb_count : forall (t : dtree) (f : nat -> nat) (K : nat),
  (forall i, (i <= K)%nat -> In (f i) (dt_leafvals t)) ->
  (forall i j, (i <= K)%nat -> (j <= K)%nat -> f i = f j -> i = j) ->
  (Nat.log2 (Datatypes.S K) <= dt_depth t)%nat.
Proof.
  intros t f K Hcov Hinj.
  assert (Hge : (Datatypes.S K <= dt_leaves t)%nat)
    by (apply (dt_leaves_ge_distinct t f K); assumption).
  assert (Hp : (1 <= dt_leaves t)%nat) by apply dt_leaves_pos.
  pose proof (dt_depth_ge_log2 t Hp) as H0.
  assert (Hmono : (Nat.log2 (Datatypes.S K) <= Nat.log2 (dt_leaves t))%nat)
    by (apply Nat.log2_le_mono; exact Hge).
  lia.
Qed.

(* ============ 审计口（G2 PA 全 Closed 预期） ============ *)

Print Assumptions dt_leaves_eq.
Print Assumptions dt_depth_ge_log2.
Print Assumptions dt_run_val_leaf.
Print Assumptions dt_leafvals_len.
Print Assumptions dt_leaves_ge_distinct.
Print Assumptions dt_lb_count.

(* ============================ §22 macnt_bsearch / macnt_bsearch_result / macnt_bsearch_c_le 语句面 ============================ *)
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import QArith.
Require Import UpReqMixLogA.

Local Open Scope Q_scope.

(* ================= §1 计数伴随二分与基础性质 ================= *)

(** 计数伴随函数：与 mixa_bsearch 相同的分枝骨架，额外累计谓词求值次数。
    返回 (搜索结果, 谓词求值次数)；两枝递归调用经 let 约束共享一份计算。 *)
Fixpoint macnt_bsearch (test : nat -> bool) (f lo hi : nat) : nat * nat :=
  match f with
  | Datatypes.O => (lo, Datatypes.O)
  | Datatypes.S f' =>
      if Nat.eqb lo hi then (lo, Datatypes.O)
      else if test (Nat.div2 (Nat.add lo hi))
        then let r := macnt_bsearch test f' lo (Nat.div2 (Nat.add lo hi)) in
             (fst r, Datatypes.S (snd r))
        else let r := macnt_bsearch test f' (Datatypes.S (Nat.div2 (Nat.add lo hi))) hi in
             (fst r, Datatypes.S (snd r))
  end.

(** 计数不空：macnt_bsearch 的搜索结果与 mixa_bsearch 逐点一致。
    两函数的分枝骨架逐枝相同（区间端点相等判定、中点谓词判定、两枝递归），
    对燃料参数作归纳，按两个布尔判定分情形后由归纳假设即得。 *)
Lemma macnt_bsearch_result : forall (test : nat -> bool) (f lo hi : nat),
  fst (macnt_bsearch test f lo hi) = mixa_bsearch test f lo hi.
Proof.
  intros test f. induction f as [| f IH]; intros lo hi.
  - reflexivity.
  - cbn [macnt_bsearch mixa_bsearch]. cbv zeta. cbn [fst snd].
    destruct (Nat.eqb lo hi); [reflexivity |].
    destruct (test (Nat.div2 (Nat.add lo hi))); cbn [fst snd];
      rewrite IH; reflexivity.
Qed.

(** 计数上界：谓词求值次数不超过燃料配给（无条件：不需单调性、
    端点通过性或任何窗口前提）。每层燃料至多一次谓词求值：
    区间端点相等的层与燃料耗尽的层零次。对燃料参数归纳。 *)
Lemma macnt_bsearch_c_le : forall (test : nat -> bool) (f lo hi : nat),
  Nat.le (snd (macnt_bsearch test f lo hi)) f.
Proof.
  intros test f. induction f as [| f IH]; intros lo hi.
  - cbn [macnt_bsearch snd]. lia.
  - cbn [macnt_bsearch]. destruct (Nat.eqb lo hi).
    + cbn [snd]. lia.
    + destruct (test (Nat.div2 (Nat.add lo hi))).
      * cbv zeta. cbn [snd].
        specialize (IH lo (Nat.div2 (Nat.add lo hi))). lia.
      * cbv zeta. cbn [snd].
        specialize (IH (Datatypes.S (Nat.div2 (Nat.add lo hi))) hi). lia.
Qed.

(* ================= §2 量级实例形与 Q 层选择器实例 ================= *)

(** 量级实例（窗口宽 K）：区间 [0,K]（候选数 S K = K+1 面，含 K=0）上
    以燃料 S(log₂(S K)) 运行，与 mixa_fuel_log 的配给一致；
    谓词求值次数 ≤ S(log₂(S K)) = log₂(K+1)+1。由 macnt_bsearch_c_le
    以燃料配给实例化直接推得。 *)
Theorem macnt_win_count : forall (test : nat -> bool) (K : nat),
  Nat.le (snd (macnt_bsearch test (Datatypes.S (Nat.log2 (Datatypes.S K))) 0 K))
         (Datatypes.S (Nat.log2 (Datatypes.S K))).
Proof.
  intros test K.
  pose proof (macnt_bsearch_c_le test
               (Datatypes.S (Nat.log2 (Datatypes.S K))) 0 K).
  lia.
Qed.

(** Q 层选择器实例的计数不空：mixa_k_log_of k0 v b0 的求值结果等于
    计数伴随函数在完全相同实参下的第一分量；故其谓词求值次数即
    macnt_bsearch 的计数分量。由 macnt_bsearch_result 直接推得。 *)
Theorem macnt_k_log_of_exec : forall (k0 v b0 : Q),
  mixa_k_log_of k0 v b0 =
  fst (macnt_bsearch (mixa_test k0 v b0)
         (Datatypes.S (Nat.log2 (Datatypes.S (mixa_win v (1 - k0) b0))))
         0 (mixa_win v (1 - k0) b0)).
Proof.
  intros k0 v b0. unfold mixa_k_log_of.
  symmetry. apply macnt_bsearch_result.
Qed.

(** 主计数定理（A 路选择器的显式计数形）：Q 层选择器 mixa_k_log_of k0 v b0
    执行中的谓词求值次数 ≤ S(log₂(S K_win)) = log₂(K_win+1)+1，
    其中窗口上端 K_win = mixa_win v (1-k0) b0。语句无条件：
    不需 Qlt 0 k0 等四个正性前提（计数与正确性相互独立）。 *)
Theorem macnt_k_log_of_count : forall (k0 v b0 : Q),
  Nat.le (snd (macnt_bsearch (mixa_test k0 v b0)
                (Datatypes.S (Nat.log2 (Datatypes.S (mixa_win v (1 - k0) b0))))
                0 (mixa_win v (1 - k0) b0)))
         (Datatypes.S (Nat.log2 (Datatypes.S (mixa_win v (1 - k0) b0)))).
Proof.
  intros k0 v b0.
  apply (macnt_bsearch_c_le (mixa_test k0 v b0)
           (Datatypes.S (Nat.log2 (Datatypes.S (mixa_win v (1 - k0) b0))))
           0 (mixa_win v (1 - k0) b0)).
Qed.

(** 与正确性合取的完整语句：在 mixa_sel_accounts 的四个 Q 正性前提下，
    mixa_k_log_of 的返回值通过判定、其下方全部不通过、且谓词求值次数
    ≤ S(log₂(S K_win))——两个正确性结论与计数上界一并成立。 *)
Theorem macnt_sel_accounts_count : forall k0 v b0 : Q,
  Qlt 0 k0 -> Qlt k0 (1#1) -> Qlt 0 v -> Qlt 0 b0 ->
  mixa_test k0 v b0 (mixa_k_log_of k0 v b0) = true /\
  (forall j : nat, Nat.lt j (mixa_k_log_of k0 v b0) ->
     mixa_test k0 v b0 j = false) /\
  Nat.le (snd (macnt_bsearch (mixa_test k0 v b0)
                (Datatypes.S (Nat.log2 (Datatypes.S (mixa_win v (1 - k0) b0))))
                0 (mixa_win v (1 - k0) b0)))
         (Datatypes.S (Nat.log2 (Datatypes.S (mixa_win v (1 - k0) b0)))).
Proof.
  intros k0 v b0 Hk0 Hk1 Hv Hb.
  pose proof (mixa_sel_accounts k0 v b0 Hk0 Hk1 Hv Hb) as [Ht Hmin].
  pose proof (macnt_k_log_of_count k0 v b0) as Hc.
  split; [exact Ht | split; [exact Hmin | exact Hc]].
Qed.

(* 追印面：全部证明件预期零承认闭 *)
Print Assumptions macnt_bsearch_result.
Print Assumptions macnt_bsearch_c_le.
Print Assumptions macnt_win_count.
Print Assumptions macnt_k_log_of_exec.
Print Assumptions macnt_k_log_of_count.
Print Assumptions macnt_sel_accounts_count.

(* ============================ §23 UpReqMixLogB 的 mixb_bsearch 求值计数上界原为燃料加一 ============================ *)
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
Require Import UpReqMixLogB.

(* ================= §1 二分相计数紧形（无条件） ================= *)

(** 计数紧形：mixb_bsearch 的谓词求值次数不超过燃料（无需单调性、
    端点通过性或任何窗口前提）。对燃料归纳：
    燃料零层返回 (hi, 0)，求值次数为零，界 0 ≤ 0 无松弛成立；
    递归层按定义展开后计数为 S c'，归纳假设给出 c' ≤ f'；
    中点索引比较 Nat.ltb 为假时的早退层计数为一，而燃料 S f' ≥ 1。 *)
Lemma msharp_bsearch_c_le : forall (test : nat -> bool) (f lo hi : nat),
  (snd (mixb_bsearch test f lo hi) <= f)%nat.
Proof.
  intros test f. induction f as [| f IH]; intros lo hi.
  - cbn [mixb_bsearch fst snd]. lia.
  - cbn [mixb_bsearch]. destruct (Nat.ltb lo (Nat.div2 (lo + hi)%nat)).
    + destruct (test (Nat.div2 (lo + hi)%nat)).
      * cbv zeta. cbn [fst snd].
        specialize (IH lo (Nat.div2 (lo + hi)%nat)). cbn [fst snd] in IH. lia.
      * cbv zeta. cbn [fst snd].
        specialize (IH (Nat.div2 (lo + hi)%nat) hi). cbn [fst snd] in IH. lia.
    + cbn [fst snd]. lia.
Qed.

(** 复合计数紧形：两相选择器 mixb_sel 的谓词求值次数不超过双相燃料之和
    （对 mixb_sel_count 的 S(f1+f2) 同步去松弛；倍增相计数界
    mixb_gallop_c_le 原本即为紧形 c1 ≤ f1）。 *)
Theorem msharp_sel_count : forall (test : nat -> bool) (f1 f2 : nat),
  (snd (mixb_sel test f1 f2) <= (f1 + f2))%nat.
Proof.
  intros test f1 f2.
  destruct (mixb_gallop test f1 0%nat 1%nat) as [[l h] c1] eqn:Eg.
  destruct (mixb_bsearch test f2 l h) as [r c2] eqn:Eb.
  pose proof (mixb_gallop_c_le test f1 0%nat 1%nat) as H1.
  rewrite Eg in H1. cbn [fst snd] in H1.
  pose proof (msharp_bsearch_c_le test f2 l h) as H2.
  rewrite Eb in H2. cbn [fst snd] in H2.
  assert (Hs : mixb_sel test f1 f2 = (r, (c1 + c2)%nat))
    by exact (mixb_sel_eq test f1 f2 l h c1 r c2 Eg Eb).
  rewrite Hs. cbn [snd]. lia.
Qed.

(* ================= §2 二分相可靠性合取与量级定理紧形 ================= *)

(** 二分相可靠性合取紧形：在单调性、端点夹逼（lo < hi、test lo = false、
    test hi = true）、过站前提（test k = true 与下方全假）与窗口宽
    hi - lo ≤ 2 ^ f 之下，mixb_bsearch 返回恰为最小通过站 k，
    且求值次数 c ≤ f（对 mixb_bsearch_account 的 c ≤ S f 去松弛）。
    对燃料归纳：燃料零层返回 (hi, 0)，窗口宽 ≤ 1 迫使 hi = lo + 1，
    端点夹逼给出 k = hi，计数 0 ≤ 0；递归层由归纳假设 c' ≤ f'
    得 S c' ≤ S f'；早退层窗口宽 ≤ 2^(S f') 与中点 ≤ lo 迫使
    hi = lo + 1，返回 (hi, 1) 而 S f' ≥ 1。 *)
Lemma msharp_bsearch_account : forall (test : nat -> bool) (f k lo hi r c : nat),
  mixb_mono test -> (lo < hi)%nat -> test lo = false -> test hi = true ->
  test k = true -> (forall j : nat, (j < k)%nat -> test j = false) ->
  (hi - lo <= 2 ^ f)%nat ->
  mixb_bsearch test f lo hi = (r, c) ->
  (r = k /\ c <= f)%nat.
Proof.
  intros test f. induction f as [| f IH]; intros k lo hi r c
    Hmono Hlt Hlo Hhi Htk Hmin Hw Heq.
  - assert (Hklo : (lo < k)%nat).
    { destruct (Nat.le_gt_cases k lo) as [Hc | Hc].
      - exfalso. rewrite (Hmono k lo Hc Htk) in Hlo. discriminate Hlo.
      - exact Hc. }
    assert (Hkhi : (k <= hi)%nat).
    { destruct (Nat.le_gt_cases k hi) as [Hc | Hc].
      - exact Hc.
      - exfalso. rewrite (Hmin hi Hc) in Hhi. discriminate Hhi. }
    cbn [Nat.pow] in Hw. cbn [mixb_bsearch] in Heq.
    injection Heq; intros; subst.
    split; [lia | lia].
  - assert (Hklo : (lo < k)%nat).
    { destruct (Nat.le_gt_cases k lo) as [Hc | Hc].
      - exfalso. rewrite (Hmono k lo Hc Htk) in Hlo. discriminate Hlo.
      - exact Hc. }
    assert (Hkhi : (k <= hi)%nat).
    { destruct (Nat.le_gt_cases k hi) as [Hc | Hc].
      - exact Hc.
      - exfalso. rewrite (Hmin hi Hc) in Hhi. discriminate Hhi. }
    assert (H2 : (2 <> 0)%nat) by lia.
    pose proof (Nat.div_mod (lo + hi)%nat 2%nat H2) as Hdm.
    pose proof (Nat.mod_upper_bound (lo + hi)%nat 2%nat H2) as Hm.
    rewrite mixb_bsearch_S in Heq.
    destruct (Nat.ltb lo (Nat.div2 (lo + hi)%nat)) eqn:Eltb.
    + assert (Hmidlo : (lo < Nat.div2 (lo + hi)%nat)%nat)
        by (apply Nat.ltb_lt; exact Eltb).
      assert (Hmidhi : (Nat.div2 (lo + hi)%nat < hi)%nat).
      { rewrite Nat.div2_div. lia. }
      assert (Hwd : (hi - lo <= 2 * 2 ^ f)%nat).
      { replace (2 ^ Datatypes.S f)%nat with (2 * 2 ^ f)%nat in Hw
          by (cbn [Nat.pow]; lia).
        lia. }
      destruct (test (Nat.div2 (lo + hi)%nat)) eqn:Emid.
      * assert (Hkmid : (k <= Nat.div2 (lo + hi)%nat)%nat).
        { destruct (Nat.le_gt_cases k (Nat.div2 (lo + hi)%nat)) as [Hc | Hc].
          - exact Hc.
          - exfalso. rewrite (Hmin (Nat.div2 (lo + hi)%nat) Hc) in Emid.
            discriminate Emid. }
        assert (Hw2 : (Nat.div2 (lo + hi)%nat - lo <= 2 ^ f)%nat).
        { assert (Hsh : (Nat.div2 (lo + hi)%nat = lo + Nat.div2 (hi - lo)%nat)%nat).
          { replace (lo + hi)%nat with (2 * lo + (hi - lo))%nat by lia.
            apply mixb_div2_shift. }
          rewrite Hsh.
          replace (lo + Nat.div2 (hi - lo) - lo)%nat
            with (Nat.div2 (hi - lo))%nat by lia.
          apply mixb_div2_le. exact Hwd. }
        destruct (mixb_bsearch test f lo (Nat.div2 (lo + hi)%nat))
          as [r1 c1] eqn:E1.
        cbv zeta in Heq. cbn [fst snd] in Heq.
        injection Heq as Eqr Eqc.
        destruct (IH k lo (Nat.div2 (lo + hi)%nat) r1 c1
                    Hmono Hmidlo Hlo Emid Htk Hmin Hw2 E1) as [Hr1 Hc1].
        rewrite <- Eqr, <- Eqc.
        split; [exact Hr1 | lia].
      * assert (Hmidk : (Nat.div2 (lo + hi)%nat < k)%nat).
        { destruct (Nat.le_gt_cases k (Nat.div2 (lo + hi)%nat)) as [Hc | Hc].
          - exfalso. rewrite (Hmono k (Nat.div2 (lo + hi)%nat) Hc Htk) in Emid.
            discriminate Emid.
          - exact Hc. }
        assert (Hw2 : (hi - Nat.div2 (lo + hi)%nat <= 2 ^ f)%nat).
        { assert (Hsh : (Nat.div2 (lo + hi)%nat = lo + Nat.div2 (hi - lo)%nat)%nat).
          { replace (lo + hi)%nat with (2 * lo + (hi - lo))%nat by lia.
            apply mixb_div2_shift. }
          rewrite Hsh.
          replace (hi - (lo + Nat.div2 (hi - lo)))%nat
            with ((hi - lo) - Nat.div2 (hi - lo))%nat by lia.
          apply mixb_div2_split. exact Hwd. }
        destruct (mixb_bsearch test f (Nat.div2 (lo + hi)%nat) hi)
          as [r2 c2] eqn:E2.
        cbv zeta in Heq. cbn [fst snd] in Heq.
        injection Heq as Eqr Eqc.
        destruct (IH k (Nat.div2 (lo + hi)%nat) hi r2 c2
                    Hmono Hmidhi Emid Hhi Htk Hmin Hw2 E2) as [Hr2 Hc2].
        rewrite <- Eqr, <- Eqc.
        split; [exact Hr2 | lia].
    + assert (Hmle : (Nat.div2 (lo + hi)%nat <= lo)%nat)
        by (apply Nat.ltb_ge; exact Eltb).
      rewrite Nat.div2_div in Hmle.
      assert (Hheq : (hi = lo + 1)%nat) by lia.
      cbn [fst snd] in Heq. injection Heq; intros; subst.
      split; [lia | lia].
Qed.

(** 量级定理紧形：双相燃料 S(S(log2 K)) 配给下，mixb_sel 返回恰为
    可判定谓词的最小通过站，且谓词求值次数 ≤ 2·log₂K + 4。
    倍增相计数 c1 ≤ S(S(log2 K)) 由 mixb_gallop_account 给出（原本即紧）；
    二分相宽度前提 h - l ≤ 2^(S(S(log2 K))) 由 mixb_gallop_width_le 的
    末站宽度交割供给；二分相计数 c2 ≤ S(S(log2 K)) 由
    msharp_bsearch_account 的紧形给出；两相计数相加
    (log₂K + 2) + (log₂K + 2) = 2·log₂K + 4 由 lia 收束。 *)
Theorem msharp_sel_scale : forall (test : nat -> bool) (K k r c : nat),
  mixb_mono test -> test 0%nat = false ->
  test k = true -> (forall j : nat, (j < k)%nat -> test j = false) ->
  (1 <= k -> k <= K -> 2 <= K ->
  mixb_sel test (Datatypes.S (Datatypes.S (Nat.log2 K)))
           (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r, c) ->
  r = k /\ c <= 2 * (Nat.log2 K) + 4)%nat.
Proof.
  intros test K k r c Hmono H0 Htk Hmin Hk1 HkK HK2 Hsel.
  pose proof (Nat.log2_spec K) as Hspec.
  assert (HK0 : (0 < K)%nat) by lia.
  specialize (Hspec HK0).
  assert (Hlt01 : (0 < 1)%nat) by exact (Nat.lt_0_succ 0).
  destruct (mixb_gallop test (Datatypes.S (Datatypes.S (Nat.log2 K))) 0%nat 1%nat)
    as [[l h] c1] eqn:Eg.
  destruct (mixb_bsearch test (Datatypes.S (Datatypes.S (Nat.log2 K))) l h)
    as [r2 c2] eqn:Eb.
  assert (Hselc : mixb_sel test (Datatypes.S (Datatypes.S (Nat.log2 K)))
                    (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r2, (c1 + c2)%nat))
    by exact (mixb_sel_eq test (Datatypes.S (Datatypes.S (Nat.log2 K)))
                (Datatypes.S (Datatypes.S (Nat.log2 K))) l h c1 r2 c2 Eg Eb).
  rewrite Hselc in Hsel. injection Hsel; intros; subst.
  assert (Hreach : (k <= 1 + (1 - 0) * 2 ^ (Datatypes.S (Nat.log2 K)))%nat).
  { replace (2 ^ Datatypes.S (Nat.log2 K))%nat
      with (2 * 2 ^ Nat.log2 K)%nat by (cbn [Nat.pow]; lia).
    destruct Hspec as [_ Hup]. cbn [Nat.pow] in Hup. lia. }
  pose proof (mixb_gallop_account test (Datatypes.S (Nat.log2 K)) k 0%nat 1%nat
                l h c1 Hmono Hlt01 H0 Htk Hmin Hreach Eg) as Hgl.
  destruct Hgl as [Hgl1 [Hgl2 [Hgl3 Hgl4]]].
  pose proof (mixb_gallop_width_le test (Datatypes.S (Nat.log2 K)) 0%nat 1%nat
                l h c1 Hlt01 Eg) as Hwd.
  replace (1 - 0)%nat with 1%nat in Hwd by lia.
  replace (2 ^ Datatypes.S (Datatypes.S (Nat.log2 K)) * 1)%nat
    with (2 ^ Datatypes.S (Datatypes.S (Nat.log2 K)))%nat in Hwd by lia.
  pose proof (msharp_bsearch_account test (Datatypes.S (Datatypes.S (Nat.log2 K)))
                k l h r c2 Hmono Hgl1 Hgl3 Hgl2 Htk Hmin Hwd Eb) as Hbs.
  destruct Hbs as [Hbs1 Hbs2].
  split; [exact Hbs1 | lia].
Qed.

(* 追印面：全部证明件预期零承认闭 *)
Print Assumptions msharp_bsearch_c_le.
Print Assumptions msharp_sel_count.
Print Assumptions msharp_bsearch_account.
Print Assumptions msharp_sel_scale.

(* ============================ §24 mtl_mult_zero_l / mtl_sum2 / mtl_row_alg 语句面 ============================ *)
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
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSampling.
Require Import UpReqConcFin2.
Import RealInterfaceEnhancedMod.

(* ---- 帮件〇：左零乘（mult_zero 字段只有右零形；零在左经 comm 桥） ---- *)

Lemma mtl_mult_zero_l : forall a : Real, req (mult zero a) zero.
Proof.
  intro a.
  apply (req_trans _ (mult a zero) zero).
  - exact (mult_comm zero a).
  - exact (mult_zero a).
Defined.

(* ---- 帮件一：二枚举求和形状（cf2_sumf 折叠定义级展开） ---- *)

Lemma mtl_sum2 : forall g : bool -> Real,
  req (cf2_sumf g) (plus (g true) (g false)).
Proof.
  intro g.
  apply (req_trans _ (plus (g true) (plus (g false) zero)) _).
  - exact (req_refl (plus (g true) (plus (g false) zero))).
  - exact (req_plus_compat (g true) (g true) (plus (g false) zero) (g false)
             (req_refl (g true)) (plus_zero (g false))).
Defined.

(* ---- 帮件二：行值代数——正 f 的 f·inv(f+f) 恒等于 inv_two ---- *)

Lemma mtl_row_alg : forall (f : Real) (Hf : lt zero f),
  req (mult f (inv_pos (plus f f) (plus_positive f f Hf Hf))) cf2_inv_two.
Proof.
  intros f Hf.
  apply (req_trans _
           (mult f (mult (inv_pos f Hf) (inv_pos (plus one one) req_two_pos)))
           cf2_inv_two).
  - apply (req_mult_compat f f _ _ (req_refl f)).
    apply (req_trans _
             (inv_pos (mult f (plus one one))
                      (mult_positive f (plus one one) Hf req_two_pos)) _).
    + apply (inv_pos_ext (plus f f) (mult f (plus one one))
               (plus_positive f f Hf Hf)
               (mult_positive f (plus one one) Hf req_two_pos)).
      apply (req_sym _ _).
      apply (req_trans _ (mult (plus one one) f) _).
      * exact (mult_comm f (plus one one)).
      * exact (req_two_mult f).
    + exact (req_inv_pos_mult_distr f (plus one one) Hf req_two_pos).
  - apply (req_trans _
             (mult (mult f (inv_pos f Hf))
                   (inv_pos (plus one one) req_two_pos)) _).
    + exact (mult_assoc f (inv_pos f Hf) (inv_pos (plus one one) req_two_pos)).
    + apply (req_trans _
               (mult one (inv_pos (plus one one) req_two_pos)) cf2_inv_two).
      * apply (req_mult_compat _ _ _ _).
        -- exact (inv_pos_correct f Hf).
        -- exact (req_refl (inv_pos (plus one one) req_two_pos)).
      * exact (req_mult_one_l (inv_pos (plus one one) req_two_pos)).
Defined.

(* ---- 帮件三：核行值——cf2 核每行恒等于 inv_two（行内 logit 恒定的代数后果） ---- *)

Definition mtl_fac_t : Real :=
  rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos) one).

Definition mtl_fac_f : Real :=
  rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos) (opp one)).

Lemma mtl_fac_t_pos : lt zero mtl_fac_t.
Proof. exact (epp_pos (mult (inv_pos cf2_temp cf2_temp_pos) one)). Defined.

Lemma mtl_fac_f_pos : lt zero mtl_fac_f.
Proof. exact (epp_pos (mult (inv_pos cf2_temp cf2_temp_pos) (opp one))). Defined.

Lemma mtl_kernel_val_t : forall s' : bool, req (cf2_kernel true s') cf2_inv_two.
Proof.
  intro s'.
  apply (req_trans _
           (mult mtl_fac_t
              (inv_pos (plus mtl_fac_t mtl_fac_t)
                 (plus_positive mtl_fac_t mtl_fac_t
                    mtl_fac_t_pos mtl_fac_t_pos)))
           cf2_inv_two).
  - apply (req_mult_compat _ _ _ _ (req_refl _)).
    apply (inv_pos_ext (cf2_Zrow true) (plus mtl_fac_t mtl_fac_t)
             (cf2_Zrow_pos true)
             (plus_positive mtl_fac_t mtl_fac_t
                mtl_fac_t_pos mtl_fac_t_pos)).
    apply (req_trans _
             (plus (rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos)
                                      (cf2_z true true)))
                   (rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos)
                                      (cf2_z true false)))) _).
    + exact (mtl_sum2 (fun s0 : bool =>
                rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos)
                                   (cf2_z true s0)))).
    + exact (req_plus_compat _ _ _ _ (req_refl _) (req_refl _)).
  - exact (mtl_row_alg mtl_fac_t mtl_fac_t_pos).
Defined.

Lemma mtl_kernel_val_f : forall s' : bool, req (cf2_kernel false s') cf2_inv_two.
Proof.
  intro s'.
  apply (req_trans _
           (mult mtl_fac_f
              (inv_pos (plus mtl_fac_f mtl_fac_f)
                 (plus_positive mtl_fac_f mtl_fac_f
                    mtl_fac_f_pos mtl_fac_f_pos)))
           cf2_inv_two).
  - apply (req_mult_compat _ _ _ _ (req_refl _)).
    apply (inv_pos_ext (cf2_Zrow false) (plus mtl_fac_f mtl_fac_f)
             (cf2_Zrow_pos false)
             (plus_positive mtl_fac_f mtl_fac_f
                mtl_fac_f_pos mtl_fac_f_pos)).
    apply (req_trans _
             (plus (rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos)
                                      (cf2_z false true)))
                   (rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos)
                                      (cf2_z false false)))) _).
    + exact (mtl_sum2 (fun s0 : bool =>
                rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos)
                                   (cf2_z false s0)))).
    + exact (req_plus_compat _ _ _ _ (req_refl _) (req_refl _)).
  - exact (mtl_row_alg mtl_fac_f mtl_fac_f_pos).
Defined.

(* ---- 帮件四：单步压平——点质量对一步后逐点同值 == inv_two ---- *)

Lemma mtl_pt_t : forall s' : bool, req (cf2_k_step cf2_mu0 s') cf2_inv_two.
Proof.
  intro s'.
  apply (req_trans _
           (plus (mult (cf2_mu0 true) (cf2_kernel true s'))
                 (plus (mult (cf2_mu0 false) (cf2_kernel false s')) zero))
           cf2_inv_two).
  - exact (req_refl _).
  - apply (req_trans _
             (plus (cf2_kernel true s') (plus zero zero)) _).
    + exact (req_plus_compat _ _ _ _
               (req_mult_one_l (cf2_kernel true s'))
               (req_plus_compat _ _ _ _
                  (mtl_mult_zero_l (cf2_kernel false s')) (req_refl zero))).
    + apply (req_trans _ (plus (cf2_kernel true s') zero) _).
      * exact (req_plus_compat _ _ _ _ (req_refl _) (plus_zero zero)).
      * apply (req_trans _ (cf2_kernel true s') cf2_inv_two).
        -- exact (plus_zero (cf2_kernel true s')).
        -- exact (mtl_kernel_val_t s').
Defined.

Lemma mtl_pt_n : forall s' : bool, req (cf2_k_step cf2_nu0 s') cf2_inv_two.
Proof.
  intro s'.
  apply (req_trans _
           (plus (mult (cf2_nu0 true) (cf2_kernel true s'))
                 (plus (mult (cf2_nu0 false) (cf2_kernel false s')) zero))
           cf2_inv_two).
  - exact (req_refl _).
  - apply (req_trans _
             (plus zero (plus (cf2_kernel false s') zero)) _).
    + exact (req_plus_compat _ _ _ _
               (mtl_mult_zero_l (cf2_kernel true s'))
               (req_plus_compat _ _ _ _
                  (req_mult_one_l (cf2_kernel false s'))
                  (req_refl zero))).
    + apply (req_trans _ (plus (cf2_kernel false s') zero) _).
      * exact (req_plus_zero_l (plus (cf2_kernel false s') zero)).
      * apply (req_trans _ (cf2_kernel false s') cf2_inv_two).
        -- exact (plus_zero (cf2_kernel false s')).
        -- exact (mtl_kernel_val_f s').
Defined.

(* titer 1 与 k_step 的定义级同体换形 *)
Lemma mtl_t1_t : forall s' : bool, req (cf2_titer 1%nat cf2_mu0 s') cf2_inv_two.
Proof. intro s'. exact (mtl_pt_t s'). Defined.

Lemma mtl_t1_n : forall s' : bool, req (cf2_titer 1%nat cf2_nu0 s') cf2_inv_two.
Proof. intro s'. exact (mtl_pt_n s'). Defined.

(* ---- 帮件五：n=1 处 TV == zero ---- *)

Lemma mtl_pt_abs : forall s : bool,
  req (abs (req_minus (cf2_titer 1%nat cf2_mu0 s) (cf2_titer 1%nat cf2_nu0 s)))
      zero.
Proof.
  intro s.
  assert (Hd : req (req_minus (cf2_titer 1%nat cf2_mu0 s)
                              (cf2_titer 1%nat cf2_nu0 s)) zero).
  { apply (req_trans _ (req_minus cf2_inv_two cf2_inv_two) zero).
    - exact (reqd_minus_compat _ _ _ _ (mtl_t1_t s) (mtl_t1_n s)).
    - exact (plus_opp cf2_inv_two). }
  apply (req_trans _
             (req_minus (cf2_titer 1%nat cf2_mu0 s)
                        (cf2_titer 1%nat cf2_nu0 s)) zero).
  - exact (cf2_bs_abs _ (lt_le_iff _ _ (inr (req_sym _ _ Hd)))).
  - exact Hd.
Defined.

Lemma mtl_tv_one_zero :
  req (cf2_tv (cf2_titer 1%nat cf2_mu0) (cf2_titer 1%nat cf2_nu0)) zero.
Proof.
  apply (req_trans _
           (mult cf2_inv_two
              (cf2_sumf (fun s : bool =>
                   abs (req_minus (cf2_titer 1%nat cf2_mu0 s)
                                  (cf2_titer 1%nat cf2_nu0 s)))))
           zero).
  - exact (req_refl (mult cf2_inv_two
                (cf2_sumf (fun s : bool =>
                     abs (req_minus (cf2_titer 1%nat cf2_mu0 s)
                                    (cf2_titer 1%nat cf2_nu0 s)))))).
  - exact (req_trans _ _ _
             (req_mult_compat cf2_inv_two cf2_inv_two
                (cf2_sumf (fun s : bool =>
                     abs (req_minus (cf2_titer 1%nat cf2_mu0 s)
                                    (cf2_titer 1%nat cf2_nu0 s))))
                (cf2_sumf (fun _ : bool => zero))
                (req_refl cf2_inv_two)
                (req_trans _ _ _
                   (mtl_sum2 (fun s : bool =>
                        abs (req_minus (cf2_titer 1%nat cf2_mu0 s)
                                       (cf2_titer 1%nat cf2_nu0 s))))
                   (req_trans _ _ _
                      (req_plus_compat
                         (abs (req_minus (cf2_titer 1%nat cf2_mu0 true)
                                     (cf2_titer 1%nat cf2_nu0 true)))
                         zero
                         (abs (req_minus (cf2_titer 1%nat cf2_mu0 false)
                                     (cf2_titer 1%nat cf2_nu0 false)))
                         zero
                         (mtl_pt_abs true) (mtl_pt_abs false))
                      (req_plus_zero_l zero))))
             (req_trans _ _ _
                (req_mult_compat cf2_inv_two cf2_inv_two
                   (cf2_sumf (fun _ : bool => zero)) zero
                   (req_refl cf2_inv_two)
                   (req_trans _ _ _
                      (mtl_sum2 (fun _ : bool => zero))
                      (req_plus_zero_l zero)))
                (mult_zero cf2_inv_two))).
Defined.

(* ---- 帮件六：TV0 == one；omd^1 == omd；W := omd·TV0 的同值与正性 ---- *)

Lemma mtl_tv0_one : req (cf2_tv cf2_mu0 cf2_nu0) one.
Proof.
  apply (req_trans _ (mult cf2_inv_two (plus one one)) one).
  - exact (req_mult_compat cf2_inv_two cf2_inv_two
             (cf2_sumf (fun s : bool =>
                  abs (req_minus (cf2_mu0 s) (cf2_nu0 s))))
             (plus one one) (req_refl cf2_inv_two) cf2_tv_sum_one).
  - apply (req_trans _ (mult (plus one one) cf2_inv_two) one).
    + exact (mult_comm cf2_inv_two (plus one one)).
    + exact (inv_pos_correct (plus one one) req_two_pos).
Defined.

Lemma mtl_rpow1_omd : req (req_r_pow cf2_omd 1%nat) cf2_omd.
Proof.
  apply (req_trans _ (mult cf2_omd (req_r_pow cf2_omd 0%nat)) cf2_omd).
  - exact (req_refl _).
  - exact (req_mult_one_r cf2_omd).
Defined.

Definition mtl_W : Real :=
  mult (req_r_pow cf2_omd 1%nat) (cf2_tv cf2_mu0 cf2_nu0).

Lemma mtl_W_omd : req mtl_W cf2_omd.
Proof.
  apply (req_trans _ (mult cf2_omd one) cf2_omd).
  - exact (req_mult_compat _ _ _ _ mtl_rpow1_omd mtl_tv0_one).
  - exact (req_mult_one_r cf2_omd).
Defined.

Lemma mtl_W_pos : lt zero mtl_W.
Proof.
  exact (mult_positive _ _
           (lt_id_r zero cf2_omd (req_r_pow cf2_omd 1%nat)
              (req_sym _ _ mtl_rpow1_omd) cf2_omd_pos)
           cf2_tv_pos).
Defined.

(* ---- 帮件七：预算 B := delta_star·W 严格落在 (0, W) 内 ---- *)

Lemma mtl_B_lt_W : lt (mult cf2_delta_star mtl_W) mtl_W.
Proof.
  exact (lt_id_r (mult cf2_delta_star mtl_W) (mult one mtl_W) mtl_W
           (req_mult_one_l mtl_W)
           (lt_mult_compat cf2_delta_star one mtl_W mtl_W_pos cf2_ds_lt_one)).
Defined.

Lemma mtl_B_pos : lt zero (mult cf2_delta_star mtl_W).
Proof.
  exact (mult_positive cf2_delta_star mtl_W cf2_ds_pos mtl_W_pos).
Defined.

(* ============ 主件甲：下界步引理在 n:=1 处的机器反驳 ============ *)

Theorem mtl_refute_lower :
  Not (le (mult (req_r_pow cf2_omd 1%nat) (cf2_tv cf2_mu0 cf2_nu0))
          (cf2_tv (cf2_titer 1%nat cf2_mu0) (cf2_titer 1%nat cf2_nu0))).
Proof.
  intro H.
  assert (Hle0 : le mtl_W zero).
  { apply (le_trans mtl_W
              (cf2_tv (cf2_titer 1%nat cf2_mu0) (cf2_titer 1%nat cf2_nu0)) zero).
    - exact (le_id_l mtl_W
               (mult (req_r_pow cf2_omd 1%nat) (cf2_tv cf2_mu0 cf2_nu0))
               (cf2_tv (cf2_titer 1%nat cf2_mu0) (cf2_titer 1%nat cf2_nu0))
               (req_refl (mult (req_r_pow cf2_omd 1%nat)
                               (cf2_tv cf2_mu0 cf2_nu0))) H).
    - exact (le_id_r
               (cf2_tv (cf2_titer 1%nat cf2_mu0) (cf2_titer 1%nat cf2_nu0))
               zero zero (req_refl zero)
               (le_id_r
                  (cf2_tv (cf2_titer 1%nat cf2_mu0) (cf2_titer 1%nat cf2_nu0))
                  (cf2_tv (cf2_titer 1%nat cf2_mu0) (cf2_titer 1%nat cf2_nu0))
                  zero mtl_tv_one_zero
                  (le_refl
                     (cf2_tv (cf2_titer 1%nat cf2_mu0)
                             (cf2_titer 1%nat cf2_nu0))))).
  }
  apply (lt_irrefl zero).
  exact (lt_id_r zero cf2_omd zero
           (le_antisym cf2_omd zero
              (le_trans cf2_omd mtl_W zero
                 (le_id_l cf2_omd mtl_W mtl_W
                    (req_sym _ _ mtl_W_omd) (le_refl mtl_W))
                 Hle0)
              (lt_le_iff zero cf2_omd (inl cf2_omd_pos)))
           cf2_omd_pos).
Defined.

(* ============ 主件乙：未混合下界推论的机器反驳 ============ *)
(*   乙语句：forall n B, lt B (omd^n·TV0) -> lt B (TV(n))。                      *)
(*   取 n:=1、B:=delta_star·W：前件真（mtl_B_lt_W），后件导 lt B zero，           *)
(*   与 mtl_B_pos 相撞。                                                        *)

Theorem mtl_no_mixing_refuted :
  Not (forall (n : nat) (B : Real),
    lt B (mult (req_r_pow cf2_omd n) (cf2_tv cf2_mu0 cf2_nu0)) ->
    lt B (cf2_tv (cf2_titer n cf2_mu0) (cf2_titer n cf2_nu0))).
Proof.
  intro H.
  assert (Hc : lt (mult cf2_delta_star mtl_W)
                  (cf2_tv (cf2_titer 1%nat cf2_mu0)
                          (cf2_titer 1%nat cf2_nu0))).
  { exact (H 1%nat (mult cf2_delta_star mtl_W) mtl_B_lt_W). }
  apply (lt_irrefl zero).
  exact (lt_trans zero (mult cf2_delta_star mtl_W) zero
           mtl_B_pos (lt_id_r _ _ zero mtl_tv_one_zero Hc)).
Defined.

(* ============ 四项自检：全件 Closed（零新假设） ============ *)

Print Assumptions mtl_sum2.
Print Assumptions mtl_row_alg.
Print Assumptions mtl_kernel_val_t.
Print Assumptions mtl_kernel_val_f.
Print Assumptions mtl_pt_t.
Print Assumptions mtl_pt_n.
Print Assumptions mtl_tv_one_zero.
Print Assumptions mtl_tv0_one.
Print Assumptions mtl_W_omd.
Print Assumptions mtl_B_lt_W.
Print Assumptions mtl_refute_lower.
Print Assumptions mtl_no_mixing_refuted.
