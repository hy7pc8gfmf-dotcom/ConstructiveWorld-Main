(* ============================================================ *)
(* mach_fold_chain.v —— π/4 的 Machin 表示：折叠定理与 π 值桥        *)
(*                                                                *)
(* ── 使命：J. Machin (1706) 恒等式的级数表示折叠：                   *)
(*    4·arctan(1/5) − arctan(1/239) == arctan(1)，                  *)
(*    即 mach_pi_quarter 的实值等于 arctan(1) 的级数实值              *)
(*    （定理 mach_fold_chain）；以及它与 Leibniz π 级数值的           *)
(*    乘法相容桥（定理 mach_edge_one）：                              *)
(*    4·mach_pi_quarter == cauchy_real_pi_leibniz。                  *)
(*   组装路径：arctan(1/5) 的加倍（和角引理在 (1/5, 1/5) 处）、        *)
(*   差角引理在 (5/12, 1/239) 处、和角引理在 (5/12, 1183/2873)        *)
(*   处的三次实例化，由 real_eq 的加法/乘法相容与结合律串联；          *)
(*   tan 值的有理恒等由 Q 层封闭分数验算件供给                         *)
(*   （加倍值 5/12、差角值 1183/2873、和角值 1）。                    *)
(* ── 依赖：mach_fold_q（Q 层折叠验算与实数层组装定义面）、            *)
(*   mach_atan_addsub（和/差角引理、arctan 部分和外延件、             *)
(*   实数环组装件）、S01–S11 已编译链（Real 型、                     *)
(*   cauchy_real_arctan、arctan_one_real、a3_h4_value_bridge）；      *)
(*   Stdlib QArith、Lia。                                            *)
(* ── 对标：J. Machin (1706) 的 π/4 公式；stdlib Reals 层 Machin      *)
(*   公式件；本库 S11 的 a3_h4_value_bridge（4·arctan(1) == π_L）。   *)
(* ── 构造性注记：纯构造性；零公理；零承认语句。全部步骤为既有引理的    *)
(*   显式实例化与 real_eq 代数组装（加法/乘法相容、结合律、逐点投影    *)
(*   外延），无新解析内容；arctan 实值对逐点界见证的无关性与对         *)
(*   有理常值相等的外延性沿逐点投影归约直证；Q 层封闭分数经全计算      *)
(*   归约后字面相等闭合。                                            *)
(* ── 编译配方：coqc -native-compiler no -q -Q . "" mach_fold_chain.v *)
(*   （世界目录需含 S01–S14 与 mach_fold_q、mach_atan_addsub          *)
(*   的已编译件。）                                                  *)
(* ============================================================ *)

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
Require Import mach_fold_q.
Require Import mach_atan_addsub.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
From Stdlib Require Import ZArith.
Import PropositionConvergenceCore.
Opaque Qred.

(* ============================================================ *)
(* 第一节 折叠链的封闭分数前提与换形验算                              *)
(*                                                                *)
(*   值域检即和角引理前提 0 < u、0 < v、u < 1、v < 1 与第五前提        *)
(*   u + v + u·v ≤ 1 在 u = 1/5（加倍步）与 u = 5/12、               *)
(*   v = 1183/2873（终步）处的逐点成立；换形件连接和角引理结论的       *)
(*   (u+v)/(1−u·v) 形与验算件的字面形。                              *)
(* ============================================================ *)

Lemma mach_q_pos_1_5 : QltT 0 (1 # 5).
Proof.
  apply Qlt_to_QltT.
  change (0 * 5 < 1 * 1)%Z.
  lia.
Qed.

Lemma mach_q_lt1_1_5 : QltT (1 # 5) 1.
Proof.
  apply Qlt_to_QltT.
  change (1 * 1 < 1 * 5)%Z.
  lia.
Qed.

(* 加倍步第五前提：1/5 + 1/5 + 1/25 = 11/25 ≤ 1。 *)
Lemma mach_q_le_1_5_double : QleT' ((1 # 5) + (1 # 5) + (1 # 5) * (1 # 5)) 1.
Proof.
  apply Qle_to_QleT'.
  change ((10 * 25 + 1 * 25) * 1 <= 1 * (25 * 25))%Z.
  lia.
Qed.

Lemma mach_q_pos_1183_2873 : QltT 0 (1183 # 2873).
Proof.
  apply Qlt_to_QltT.
  change (0 * 2873 < 1183 * 1)%Z.
  lia.
Qed.

(* 终步第五前提：分子 28561 + 5915 = 34476 与分母 34476·34476 之比
   恰为 1（28561 = 13⁴，见 mach_q_decompose_28561）。 *)
Lemma mach_q_le_add_premise :
  QleT' ((5 # 12) + (1183 # 2873) + (5 # 12) * (1183 # 2873)) 1.
Proof.
  apply Qle_to_QleT'.
  change ((28561 * 34476 + 5915 * 34476) * 1 <= 1 * (34476 * 34476))%Z.
  lia.
Qed.

(* 加倍步 tan 值换形：(1/5 + 1/5)/(1 − 1/25) == 5/12，
   与 mach_q_tan2a 的 2·(1/5) 形互为换形。 *)
Lemma mach_q_add_transform_1_5 :
  QeqT (((1 # 5) + (1 # 5)) / (1 - (1 # 5) * (1 # 5))) (5 # 12).
Proof.
  apply qeq_imp_qeqT.
  vm_compute.
  reflexivity.
Qed.

(* ============================================================ *)
(* 第二节 arctan 实值的见证无关性与常值外延性                          *)
(* ============================================================ *)

(* arctan 实值只依赖自变元，不依赖逐点界见证的选取。 *)
Lemma mach_arctan_bound_irrelevance :
  forall (x : Real)
         (Hx Hy : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
    real_eq (cauchy_real_arctan x Hx) (cauchy_real_arctan x Hy).
Proof.
  intros x Hx Hy.
  apply mach_real_eq_pt.
  intro n.
  apply qeq_imp_qeqT.
  rewrite (arctan_real_proj x Hx n).
  rewrite (arctan_real_proj x Hy n).
  reflexivity.
Qed.

(* 有理常值相等时，两份逐点界见证下的 arctan 实值相等
   （部分和沿 Qeq 外延，见 mach_arctan_partial_ext）。 *)
Lemma mach_arctan_const_ext :
  forall (a b : Q)
         (Ha : forall n : nat, QleT' (Qabs (projT1 (real_const a) n)) 1)
         (Hb : forall n : nat, QleT' (Qabs (projT1 (real_const b) n)) 1),
    QeqT a b ->
    real_eq (cauchy_real_arctan (real_const a) Ha)
            (cauchy_real_arctan (real_const b) Hb).
Proof.
  intros a b Ha Hb HabT.
  pose proof (qeqT_imp_qeq a b HabT) as Hab.
  apply mach_real_eq_pt.
  intro n.
  apply qeq_imp_qeqT.
  rewrite (arctan_real_proj (real_const a) Ha n).
  rewrite (arctan_real_proj (real_const b) Hb n).
  rewrite (real_const_proj a n).
  rewrite (real_const_proj b n).
  exact (qeqT_imp_qeq _ _ (mach_arctan_partial_ext n a b HabT)).
Qed.

(* ============================================================ *)
(* 第三节 折叠定理                                                    *)
(*                                                                *)
(*   受控枢轴：D = arctan(5/12)、Bsub = arctan(1/239)（差角引理       *)
(*   自变元见证形）、W = arctan(1183/2873)。组装五段：               *)
(*   ① 4·A − B == 4·A − Bsub（见证换形）；                           *)
(*   ② 4·A == D + D（加倍引理实例＋乘法常量线性分配）；               *)
(*   ③ (D+D) − Bsub == D + (D − Bsub)（结合律）；                    *)
(*   ④ D − Bsub == W（差角引理实例＋差角值 1183/2873 换形）；          *)
(*   ⑤ D + W == arctan(1)（和角引理实例＋和角值 1 换形）。            *)
(* ============================================================ *)

Theorem mach_fold_chain : real_eq mach_pi_quarter arctan_one_real.
Proof.
  unfold mach_pi_quarter.
  set (Dcert := mach_pt_bound_of_lt (5 # 12)
                  (qleT'_ltT_ltT 0 (1 # 239) (5 # 12)
                     (qltT_leT' 0 (1 # 239) mach_q_range_0_lt_1_239T)
                     mach_q_range_1_239_lt_5_12T)
                  mach_q_range_5_12_lt1T).
  set (D := cauchy_real_arctan (real_const (5 # 12)) Dcert).
  set (Bsubcert := mach_pt_bound_of_lt (1 # 239) mach_q_range_0_lt_1_239T
                     (qleT'_ltT_ltT (1 # 239) (5 # 12) 1
                        (qltT_leT' (1 # 239) (5 # 12) mach_q_range_1_239_lt_5_12T)
                        mach_q_range_5_12_lt1T)).
  set (Bsub := cauchy_real_arctan (real_const (1 # 239)) Bsubcert).
  set (Wcert := mach_pt_bound_of_lt (1183 # 2873)
                  mach_q_pos_1183_2873 mach_q_range_1183_2873_lt1T).
  set (W := cauchy_real_arctan (real_const (1183 # 2873)) Wcert).
  (* 三次引理实例：差角（5/12, 1/239）、终步和角（5/12, 1183/2873）、
     加倍和角（1/5, 1/5）。 *)
  pose proof (mach_atan_sub (5 # 12) (1 # 239)
              mach_q_range_0_lt_1_239T mach_q_range_1_239_lt_5_12T
              mach_q_range_5_12_lt1T) as Hsub.
  pose proof (mach_atan_add (5 # 12) (1183 # 2873)
              (qleT'_ltT_ltT 0 (1 # 239) (5 # 12)
                 (qltT_leT' 0 (1 # 239) mach_q_range_0_lt_1_239T)
                 mach_q_range_1_239_lt_5_12T)
              mach_q_pos_1183_2873 mach_q_range_5_12_lt1T
              mach_q_range_1183_2873_lt1T mach_q_le_add_premise) as Hadd.
  pose proof (mach_atan_add (1 # 5) (1 # 5) mach_q_pos_1_5 mach_q_pos_1_5
              mach_q_lt1_1_5 mach_q_lt1_1_5 mach_q_le_1_5_double) as Hdbl.
  (* 加倍：2·A == A + A。 *)
  pose proof (mach_real_const_one_mult mach_atan_one_fifth) as Hone.
  assert (H2A : real_eq (real_mult (real_const 2) mach_atan_one_fifth)
                        (real_plus mach_atan_one_fifth mach_atan_one_fifth)).
  { eapply real_eq_trans.
    - exact (real_eq_sym _ _ (mach_real_const_lin2 mach_atan_one_fifth 1 1)).
    - apply (RealSetoid.real_eq_plus_compat _ _ _ _); exact Hone. }
  (* 加倍引理结论的见证换形：arctan((1/5+1/5)/(1−1/25)) == D。 *)
  pose proof (mach_arctan_bound_irrelevance (real_const (1 # 5)) mach_pt_bound_1_5
                 (mach_pt_bound_of_lt (1 # 5) mach_q_pos_1_5 mach_q_lt1_1_5)) as HA_c.
  assert (HAA : real_eq (real_plus mach_atan_one_fifth mach_atan_one_fifth) D).
  { eapply real_eq_trans.
    - apply (RealSetoid.real_eq_plus_compat mach_atan_one_fifth mach_atan_one_fifth
              (cauchy_real_arctan (real_const (1 # 5))
                 (mach_pt_bound_of_lt (1 # 5) mach_q_pos_1_5 mach_q_lt1_1_5))
              (cauchy_real_arctan (real_const (1 # 5))
                 (mach_pt_bound_of_lt (1 # 5) mach_q_pos_1_5 mach_q_lt1_1_5)));
      [exact HA_c | exact HA_c].
    - eapply real_eq_trans.
      + exact Hdbl.
      + apply (mach_arctan_const_ext _ (5 # 12) _ Dcert mach_q_add_transform_1_5). }
  (* 4·A == (A+A)+(A+A) == D + D。 *)
  assert (H4ADD : real_eq (real_mult (real_const 4) mach_atan_one_fifth)
                          (real_plus D D)).
  { eapply real_eq_trans.
    - exact (real_eq_sym _ _ (mach_real_const_lin2 mach_atan_one_fifth 2 2)).
    - eapply real_eq_trans.
      + apply (RealSetoid.real_eq_plus_compat
                 (real_mult (real_const 2) mach_atan_one_fifth)
                 (real_mult (real_const 2) mach_atan_one_fifth)
                 (real_plus mach_atan_one_fifth mach_atan_one_fifth)
                 (real_plus mach_atan_one_fifth mach_atan_one_fifth));
         [exact H2A | exact H2A].
      + apply (RealSetoid.real_eq_plus_compat
                 (real_plus mach_atan_one_fifth mach_atan_one_fifth)
                 (real_plus mach_atan_one_fifth mach_atan_one_fifth)
                 D D); [exact HAA | exact HAA]. }
  (* 差角收拢：D − Bsub == W（经差角值 1183/2873 的换形）。 *)
  assert (Hsubleg : real_eq (real_plus D (real_opp Bsub)) W).
  { eapply real_eq_trans.
    - exact Hsub.
    - apply (mach_arctan_const_ext _ (1183 # 2873) _ Wcert mach_q_diff_transformT). }
  (* 和角收拢：D + W == arctan(1)（经和角值 1 的换形）。 *)
  assert (Hfin : real_eq (real_plus D W)
                   (cauchy_real_arctan (real_const 1) atan1_pt_bound)).
  { eapply real_eq_trans.
    - exact Hadd.
    - apply (mach_arctan_const_ext _ 1 _ atan1_pt_bound mach_q_add_transformT). }
  (* 五段串联。 *)
  assert (HL0 : real_eq (real_plus (real_mult (real_const 4) mach_atan_one_fifth)
                                   (real_opp mach_atan_1_239))
                        (real_plus (real_mult (real_const 4) mach_atan_one_fifth)
                                   (real_opp Bsub))).
  { apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_opp_compat _ _).
      apply (mach_arctan_bound_irrelevance (real_const (1 # 239))
              mach_pt_bound_1_239 Bsubcert). }
  assert (HL1 : real_eq (real_plus (real_mult (real_const 4) mach_atan_one_fifth)
                                   (real_opp Bsub))
                        (real_plus (real_plus D D) (real_opp Bsub))).
  { apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    - exact H4ADD.
    - apply real_eq_refl. }
  assert (HL2 : real_eq (real_plus (real_plus D D) (real_opp Bsub))
                        (real_plus D (real_plus D (real_opp Bsub)))).
  { exact (real_eq_sym _ _ (mach_real_plus_assoc D D (real_opp Bsub))). }
  assert (HL3 : real_eq (real_plus D (real_plus D (real_opp Bsub)))
                        (real_plus D W)).
  { apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    - apply real_eq_refl.
    - exact Hsubleg. }
  exact (real_eq_trans _ _ _ HL0
           (real_eq_trans _ _ _ HL1
              (real_eq_trans _ _ _ HL2 (real_eq_trans _ _ _ HL3 Hfin)))).
Qed.

(* ============================================================ *)
(* 第四节 π 值桥                                                      *)
(*                                                                *)
(*   两段传递：4·mach_pi_quarter == 4·arctan_one_real                  *)
(*   （折叠定理的乘法相容）与 4·arctan_one_real == π_L（S11 的          *)
(*   a3_h4_value_bridge 原样复用）。                                  *)
(* ============================================================ *)

Theorem mach_edge_one :
  real_eq (real_mult (real_const 4) mach_pi_quarter) cauchy_real_pi_leibniz.
Proof.
  apply (real_eq_trans _ (real_mult (real_const 4) arctan_one_real)).
  - apply (RealSetoid.real_eq_mult_compat _ _ _ _).
    + apply real_eq_refl.
    + exact mach_fold_chain.
  - exact a3_h4_value_bridge.
Qed.
