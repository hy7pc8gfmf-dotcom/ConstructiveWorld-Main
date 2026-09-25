(* ==========================================================================)
   UpAblEps66Pos.v — 重要性权重与优势余量的正性
   使命: e66p_pi_old_boltzmann/e66p_pi_old_pos（旧策略 Boltzmann 形正性）、e66p_sum2 两点和外推族、e66p_res_weight_pos/e66p_res_weight_pos_margin（权重正性与余量）与 e66p_real_advantage_pos_margin。
   依赖: S01_BaseRing、S02_CauchyComplete、S03_QExp、S04_RealExpLogConv、S05_AlignmentGRPO、S06_DiffSamplingGibbs等；Stdlib Extraction
   对标: 重要性采样权重正性与组优势余量下界（策略梯度 clip 分析面）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.

(* ################ 件一：real_pi_old_pos 参数位的实例（Boltzmann 形逐点正性） ####### *)
(* 对照 S08_RealMainlineDPO 的 real_boltzmann_dist_r（inv(Z)·e^{−e(s)/D}）形，    *)
(* 及其正性结论 real_boltzmann_dist_r_pos；本件于独立载体独立陈述与证明。          *)

Section E66PPiOldPos.

Variable S : Type.

Definition e66p_pi_old_boltzmann (energy : S -> Real) (D Z : Real)
           (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z)
           (s : S) : Real :=
  real_mult (real_inv_pos Z Z_pos)
            (real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s))).

Theorem e66p_pi_old_pos :
  forall (energy : S -> Real) (D Z : Real)
         (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z) (s : S),
    real_lt real_zero (e66p_pi_old_boltzmann energy D Z D_pos Z_pos s).
Proof.
  intros energy D Z D_pos Z_pos s.
  unfold e66p_pi_old_boltzmann.
  apply real_mult_positive.
  - apply real_inv_pos_pos.
  - apply real_exp_neg_pos.
Qed.

End E66PPiOldPos.

(* ################ 两点具体和：bool 载体上的有限和（枚举 true::false） ########## *)
(* 对照 S08_RealMainlineDPO Section RealPPOMain 的求和接口四参数位                    *)
(* （外延、保序、加法、齐次）：e66p_sum2 给出其在两点载体上的具体实例。            *)

Definition e66p_sum2 (f : bool -> Real) : Real :=
  real_plus (f true) (f false).

Lemma e66p_sum2_ext : forall f g : bool -> Real,
  (forall s : bool, real_eq (f s) (g s)) ->
  real_eq (e66p_sum2 f) (e66p_sum2 g).
Proof.
  intros f g H. unfold e66p_sum2.
  apply (RealSetoid.real_eq_plus_compat (f true) (f false) (g true) (g false)).
  - apply H.
  - apply H.
Qed.

Lemma e66p_sum2_le : forall f g : bool -> Real,
  (forall s : bool, real_le (f s) (g s)) ->
  real_le (e66p_sum2 f) (e66p_sum2 g).
Proof.
  intros f g H. unfold e66p_sum2.
  apply real_le_plus_compat.
  - apply H.
  - apply H.
Qed.

(* 加法性：由结合律与交换律将 (a+b)+(c+d) 重排为 (a+c)+(b+d)。 *)
Lemma e66p_sum2_add : forall f g : bool -> Real,
  real_eq (e66p_sum2 (fun s : bool => real_plus (f s) (g s)))
          (real_plus (e66p_sum2 f) (e66p_sum2 g)).
Proof.
  intros f g. unfold e66p_sum2.
  assert (H2 : real_eq (real_plus (real_plus (f true) (g true)) (f false))
                       (real_plus (real_plus (f true) (f false)) (g true))).
  { apply (real_eq_trans _
             (real_plus (f true) (real_plus (g true) (f false)))).
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (real_eq_trans _
               (real_plus (f true) (real_plus (f false) (g true)))).
      + apply (RealSetoid.real_eq_plus_compat (f true)
                 (real_plus (g true) (f false)) (f true)
                 (real_plus (f false) (g true))).
        * apply real_eq_refl.
        * apply real_plus_comm.
      + apply real_plus_assoc. }
  apply (real_eq_trans _
           (real_plus (real_plus (real_plus (f true) (g true)) (f false)) (g false))).
  - apply real_plus_assoc.
  - apply (real_eq_trans _
             (real_plus (real_plus (real_plus (f true) (f false)) (g true)) (g false))).
    + apply (RealSetoid.real_eq_plus_compat _ _ _ _ H2 (real_eq_refl (g false))).
    + apply real_eq_sym. apply real_plus_assoc.
Qed.

Lemma e66p_sum2_linear : forall (a : Real) (f : bool -> Real),
  real_eq (e66p_sum2 (fun s : bool => real_mult a (f s)))
          (real_mult a (e66p_sum2 f)).
Proof.
  intros a f. unfold e66p_sum2.
  apply real_eq_sym. apply real_distrib.
Qed.

(* ################ 件三：残差权 E := Σ pi_old·adv 的严格正性 ################### *)
(* 构造要点：单点下界 + 逐项非负 + 求和保序 + 零和恒等式重排 + 序复合。           *)
(* 用途：为 UpRealLeB 的 real_ppo_conservative_B 之前提                          *)
(*   real_lt real_zero real_ppo_res_weight 提供实例供给。                        *)

Lemma e66p_term_le_of_lt : forall x : Real,
  real_lt real_zero x -> real_le real_zero x.
Proof.
  intros x H. left. exact H.
Qed.

Theorem e66p_res_weight_pos :
  forall (pi_old adv : bool -> Real),
    (forall s : bool, real_lt real_zero (pi_old s)) ->
    (forall s : bool, real_lt real_zero (adv s)) ->
    real_lt real_zero (e66p_sum2 (fun s : bool => real_mult (pi_old s) (adv s))).
Proof.
  intros pi_old adv Hpi Hadv.
  assert (Hft : real_lt real_zero (real_mult (pi_old true) (adv true))).
  { apply real_mult_positive; [apply Hpi | apply Hadv]. }
  assert (Hterm : forall s : bool, real_le real_zero (real_mult (pi_old s) (adv s))).
  { intro s. apply e66p_term_le_of_lt.
    apply real_mult_positive; [apply Hpi | apply Hadv]. }
  (* 单点下界：由 0 ≤ f(false) 与求和保序，得 f(true)+0 ≤ f(true)+f(false)。 *)
  assert (Hstep : real_le (real_plus (real_mult (pi_old true) (adv true)) real_zero)
                          (e66p_sum2 (fun s : bool => real_mult (pi_old s) (adv s)))).
  { unfold e66p_sum2. apply real_le_plus_compat.
    - apply real_le_refl.
    - apply Hterm. }
  assert (Hge : real_le (real_mult (pi_old true) (adv true))
                        (e66p_sum2 (fun s : bool => real_mult (pi_old s) (adv s)))).
  { apply (RealSetoid.real_le_id_l
             (real_mult (pi_old true) (adv true))
             (real_plus (real_mult (pi_old true) (adv true)) real_zero)
             (e66p_sum2 (fun s : bool => real_mult (pi_old s) (adv s)))).
    - apply real_eq_sym. apply real_plus_zero.
    - exact Hstep. }
  apply (real_lt_le_trans real_zero
           (real_mult (pi_old true) (adv true))
           (e66p_sum2 (fun s : bool => real_mult (pi_old s) (adv s)))).
  - exact Hft.
  - exact Hge.
Qed.

(* ################ 件二：real_advantage_pos 参数位的边际条件形 #################### *)
(* 以 beta·eps 的显式边际前提为条件，结论即源文件 real_advantage_pos 参数位语句之形。   *)
(* 证明两步：由乘法正性得 0 < beta·eps，再由 real_lt 与 real_le 的传递复合。      *)
(* adv 的逐点严格正性对任意 adv 不成立，故取条件形为其构造性表述。                *)

Theorem e66p_real_advantage_pos_margin :
  forall (S : Type) (adv : S -> Real) (beta eps : Real),
    real_lt real_zero beta ->
    real_lt real_zero eps ->
    (forall s : S, real_le (real_mult beta eps) (adv s)) ->
    forall s : S, real_lt real_zero (adv s).
Proof.
  intros S adv beta eps Hbeta Heps Hm s.
  apply (real_lt_le_trans real_zero (real_mult beta eps) (adv s)).
  - apply real_mult_positive; [exact Hbeta | exact Heps].
  - exact (Hm s).
Qed.

(* ################ 件四：边际前提全链下的 E > 0（件二与件三合成） ############## *)
(* 逐点 beta·eps 边际前提 ⟹ adv 逐点严格正 ⟹ 残差权 E := Σ pi_old·adv 严格正，    *)
(* 即件三在边际前提下的可达供给形。                                              *)

Theorem e66p_res_weight_pos_margin :
  forall (pi_old adv : bool -> Real) (beta eps : Real),
    (forall s : bool, real_lt real_zero (pi_old s)) ->
    real_lt real_zero beta ->
    real_lt real_zero eps ->
    (forall s : bool, real_le (real_mult beta eps) (adv s)) ->
    real_lt real_zero (e66p_sum2 (fun s : bool => real_mult (pi_old s) (adv s))).
Proof.
  intros pi_old adv beta eps Hpi Hbeta Heps Hm.
  apply e66p_res_weight_pos.
  - exact Hpi.
  - intro s. apply (e66p_real_advantage_pos_margin bool adv beta eps Hbeta Heps Hm s).
Qed.

(* ############ 提取核验：e66p_sum2 与 e66p_pi_old_boltzmann 的计算内容提取 ##### *)

From Stdlib Require Import Extraction.
Set Extraction Output Directory "attn/ab6ex".
Extraction "e66p_ab6_sum2" e66p_sum2.
Extraction "e66p_ab6_boltz" e66p_pi_old_boltzmann.

(* ############ 假设闭包核验：以下各定理的假设闭包应为空（Closed） ############## *)

Print Assumptions e66p_pi_old_pos.
Print Assumptions e66p_sum2_ext.
Print Assumptions e66p_sum2_le.
Print Assumptions e66p_sum2_add.
Print Assumptions e66p_sum2_linear.
Print Assumptions e66p_res_weight_pos.
Print Assumptions e66p_real_advantage_pos_margin.
Print Assumptions e66p_res_weight_pos_margin.
