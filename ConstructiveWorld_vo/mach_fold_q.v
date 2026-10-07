(* ============================================================ *)
(* mach_fold_q.v —— π/4 的 Machin 表示：Q 层折叠验算件与组装定义面  *)
(*                                                                *)
(* ── 使命：为 Machin 恒等式                                        *)
(*    4·arctan(1/5) − arctan(1/239) == arctan(1)（即 π/4）          *)
(*   的两步 arctan 折叠提供 Q 层封闭分数验算与实数层组装定义面：      *)
(*    差角变换 (u−v)/(1+u·v) == 1183/2873、和角变换                 *)
(*    (u+w)/(1−u·w) == 1（u = 5/12，v = 1/239，w = 1183/2873）、     *)
(*    tan 倍角形 2·(1/5)/(1−(1/5)²) == 5/12、折叠链中间分数验算、     *)
(*    值域检（0 < 1/239 < 5/12 < 1、w < 1、u·w < 1）、结构分解       *)
(*    28561 = 13⁴；以及逐点界件（泛形 mach_pt_bound_of_lt 与         *)
(*    1/5、1/239 两实例）和组装定义面 mach_atan_one_fifth、          *)
(*    mach_atan_1_239、mach_pi_quarter。                             *)
(* ── 依赖：S01–S11 已编译链（Real 型、real_const、                 *)
(*   cauchy_real_arctan、QleT' 系）；Stdlib QArith、Qabs、ZArith、   *)
(*   Lia。                                                          *)
(* ── 对标：J. Machin (1706) 的 π/4 公式；对照 stdlib Reals 层      *)
(*   Machin 公式件与本库 arctan 级数链（S11 arctan_one_real）。      *)
(* ── 构造性注记：纯构造性；零公理；零承认语句。Qeq 域验算语句均为    *)
(*   封闭分数，经全计算归约后字面相等闭合；值域检经 change 化 Z 交乘  *)
(*   形后 lia 闭合；逐点界件沿 Qabs 单位域逐点直证；组装定义面为      *)
(*   逐点常序列的单位域实例化。                                      *)
(* ── 编译配方：unset COQLIB ROCQLIB 后                             *)
(*   coqc -native-compiler no -q -Q . "" mach_fold_q.v               *)
(*   （需上游 S01–S11 已编译件与本文同目录可解析。）                  *)
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
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
From Stdlib Require Import ZArith.
Import PropositionConvergenceCore.
Opaque Qred.

(* ============================================================ *)
(* 第一节 差角与和角变换的 Q 层封闭验算                              *)
(*                                                                *)
(*   差角恒等式：arctan u − arctan v = arctan((u−v)/(1+u·v))。       *)
(*   取 u = 5/12（即 tan(2·arctan(1/5))，见 mach_q_tan2a）、         *)
(*   v = 1/239：                                                    *)
(*     (5/12 − 1/239)/(1 + 5/2868)                                  *)
(*       = (1183/2868)/(2873/2868) = 1183/2873。                     *)
(*                                                                *)
(*   和角恒等式：arctan u + arctan w = arctan((u+w)/(1−u·w))。       *)
(*   取 w = 1183/2873：                                             *)
(*     (5/12 + 1183/2873)/(1 − 5915/34476)                          *)
(*       = (28561/34476)/(28561/34476) = 1 = tan(arctan 1)。         *)
(*   两次应用后即得 4·arctan(1/5) − arctan(1/239) = arctan(1)。      *)
(* ============================================================ *)

(* 差角变换核：arctan(5/12) − arctan(1/239) 折叠为 arctan(1183/2873)
   的 tan 值封闭验算。 *)
(* Set 层语句形（QeqT），供折叠定理语句面引用。 *)
Lemma mach_q_diff_transformT :
  QeqT ((((5 # 12) - (1 # 239)) / (1 + (5 # 12) * (1 # 239)))) (1183 # 2873).
Proof.
  apply qeq_imp_qeqT.
  vm_compute.
  reflexivity.
Qed.

Lemma mach_q_diff_transform :
  QeqT ((((5 # 12) - (1 # 239)) / (1 + (5 # 12) * (1 # 239)))) (1183 # 2873).
Proof.
  vm_compute.
  reflexivity.
Qed.

(* 和角变换核：arctan(5/12) + arctan(1183/2873) 折叠为 arctan(1)
   的 tan 值封闭验算。 *)
(* Set 层语句形（QeqT），供折叠定理语句面引用。 *)
Lemma mach_q_add_transformT :
  QeqT ((((5 # 12) + (1183 # 2873)) / (1 - (5 # 12) * (1183 # 2873)))) 1.
Proof.
  apply qeq_imp_qeqT.
  vm_compute.
  reflexivity.
Qed.

Lemma mach_q_add_transform :
  QeqT ((((5 # 12) + (1183 # 2873)) / (1 - (5 # 12) * (1183 # 2873)))) 1.
Proof.
  vm_compute.
  reflexivity.
Qed.

(* tan 倍角形：tan(2·a) = 2·tan a / (1 − tan²a)，
   a = arctan(1/5) 时给 tan(2·a) = 5/12。 *)
Lemma mach_q_tan2a :
  QeqT (((2 * (1 # 5)) / (1 - (1 # 5) * (1 # 5)))) (5 # 12).
Proof.
  vm_compute.
  reflexivity.
Qed.

(* 折叠链中间分数逐项验算（分子/分母两侧），对应差角一步的
   (1183/2868)/(2873/2868) 与和角一步的 (28561/34476) 之比。 *)
Lemma mach_q_diff_mid_num : QeqT ((5 # 12) - (1 # 239)) (1183 # 2868).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma mach_q_diff_mid_den :
  QeqT (1 + (5 # 12) * (1 # 239)) (2873 # 2868).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma mach_q_add_mid_num : QeqT ((5 # 12) + (1183 # 2873)) (28561 # 34476).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma mach_q_add_mid_den :
  QeqT (1 - (5 # 12) * (1183 # 2873)) (28561 # 34476).
Proof.
  vm_compute.
  reflexivity.
Qed.

(* ============================================================ *)
(* 第二节 值域检                                                    *)
(*                                                                *)
(*   Qlt p q 展开为交乘严格序 Qnum p · QDen q < Qnum q · QDen p。     *)
(*   以下各条即差角引理前提 0 < v、v < u、u < 1 与和角引理前提       *)
(*   u < 1、v < 1（及其推论 u·v < 1）在 u = 5/12、v = 1/239、        *)
(*   w = 1183/2873 处的逐点成立。                                    *)
(* ============================================================ *)

(* Set 层语句形（QltT），值域检伴件。 *)
Lemma mach_q_range_5_12_lt1T : QltT (5 # 12) 1.
Proof.
  apply Qlt_to_QltT.
  change (5 * 1 < 1 * 12)%Z.
  lia.
Qed.

Lemma mach_q_range_5_12_lt1 : QltT (5 # 12) 1.
Proof.
  apply Qlt_to_QltT.
  change (5 * 1 < 1 * 12)%Z.
  lia.
Qed.

Lemma mach_q_range_1183_2873_lt1T : QltT (1183 # 2873) 1.
Proof.
  apply Qlt_to_QltT.
  change (1183 * 1 < 1 * 2873)%Z.
  lia.
Qed.

Lemma mach_q_range_1183_2873_lt1 : QltT (1183 # 2873) 1.
Proof.
  apply Qlt_to_QltT.
  change (1183 * 1 < 1 * 2873)%Z.
  lia.
Qed.

Lemma mach_q_range_0_lt_1_239T : QltT 0 (1 # 239).
Proof.
  apply Qlt_to_QltT.
  change (0 * 239 < 1 * 1)%Z.
  lia.
Qed.

Lemma mach_q_range_0_lt_1_239 : QltT 0 (1 # 239).
Proof.
  apply Qlt_to_QltT.
  change (0 * 239 < 1 * 1)%Z.
  lia.
Qed.

Lemma mach_q_range_1_239_lt_5_12T : QltT (1 # 239) (5 # 12).
Proof.
  apply Qlt_to_QltT.
  change (1 * 12 < 5 * 239)%Z.
  lia.
Qed.

Lemma mach_q_range_1_239_lt_5_12 : QltT (1 # 239) (5 # 12).
Proof.
  apply Qlt_to_QltT.
  change (1 * 12 < 5 * 239)%Z.
  lia.
Qed.

Lemma mach_q_range_mult_lt1 : QltT ((5 # 12) * (1183 # 2873)) 1.
Proof.
  apply Qlt_to_QltT.
  change (5915 * 1 < 1 * 34476)%Z.
  lia.
Qed.

(* ============================================================ *)
(* 第三节 结构分解                                                   *)
(*                                                                *)
(*   28561 = 13⁴：差角一步给出分子 1183 = 5·239 − 12 与分母           *)
(*   2873 = 12·239 + 5；和角一步的分子 5·2873 + 1183·12 = 28561       *)
(*   与其分母 12·2873 − 5·1183 = 28561 相等，故和角比值化简为 1。     *)
(* ============================================================ *)

Lemma mach_q_decompose_28561 : (28561 = 13 ^ 4)%Z.
Proof.
  reflexivity.
Qed.

(* ============================================================ *)
(* 第四节 逐点界件（单位域前提的供给面）                              *)
(*                                                                *)
(*   cauchy_real_arctan 的前提为逐点界：对每个 n，                    *)
(*   |projT1 x n| ≤ 1。泛形件由 0 < u 与 u < 1 直推；两实例件         *)
(*   为封闭分数的直算特例。                                          *)
(* ============================================================ *)

(* 泛形逐点界：0 < u < 1 时实常值序列 u 落在单位域内。 *)
Lemma mach_pt_bound_of_lt :
  forall u : Q, QltT 0 u -> QltT u 1 ->
    forall n : nat, QleT' (Qabs (projT1 (real_const u) n)) 1.
Proof.
  intros u Hu0T Hu1T n.
  pose proof (QltT_to_Qlt 0 u Hu0T) as Hu0.
  pose proof (QltT_to_Qlt u 1 Hu1T) as Hu1.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs u) _).
  - apply qeq_imp_qle.
    apply (Qabs_wd (projT1 (real_const u) n) u).
    apply real_const_proj.
  - apply (Qle_trans _ u).
    + apply qeq_imp_qle.
      apply Qabs_pos.
      apply (Qlt_le_weak 0 u).
      exact Hu0.
    + apply (Qlt_le_weak u 1).
      exact Hu1.
Qed.

(* 实例逐点界：u = 1/5。 *)
Lemma mach_pt_bound_1_5 :
  forall n : nat, QleT' (Qabs (projT1 (real_const (1 # 5)) n)) 1.
Proof.
  intro n.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (1 # 5)) _).
  - apply qeq_imp_qle.
    apply (Qabs_wd (projT1 (real_const (1 # 5)) n) (1 # 5)).
    apply real_const_proj.
  - change (1 * 1 <= 1 * 5)%Z.
    lia.
Qed.

(* 实例逐点界：u = 1/239。 *)
Lemma mach_pt_bound_1_239 :
  forall n : nat, QleT' (Qabs (projT1 (real_const (1 # 239)) n)) 1.
Proof.
  intro n.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (1 # 239)) _).
  - apply qeq_imp_qle.
    apply (Qabs_wd (projT1 (real_const (1 # 239)) n) (1 # 239)).
    apply real_const_proj.
  - change (1 * 1 <= 1 * 239)%Z.
    lia.
Qed.

(* ============================================================ *)
(* 第五节 组装定义面                                                 *)
(*                                                                *)
(*   Machin 顶点 θ' := 4·arctan(1/5) − arctan(1/239) 的实数层        *)
(*   定义面：两个单位域 arctan 级数实值与它们的线性组合。              *)
(* ============================================================ *)

Definition mach_atan_one_fifth : Real :=
  cauchy_real_arctan (real_const (1 # 5)) mach_pt_bound_1_5.

Definition mach_atan_1_239 : Real :=
  cauchy_real_arctan (real_const (1 # 239)) mach_pt_bound_1_239.

Definition mach_pi_quarter : Real :=
  real_plus (real_mult (real_const 4) mach_atan_one_fifth)
            (real_opp mach_atan_1_239).
