(* ==========================================================================)
   UpAblEps66Body.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：e66p_pi_old_boltzmann、e66p_pi_old_pos、e66p_sum2、e66p_sum2_ext、e66p_sum2_le、e66p_sum2_add、e66p_sum2_linear、e66p_term_le_of_lt、e66p_res_weight_pos。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
From Stdlib Require Import Extraction.
Require Import S08_RealMainlineDPO.
Require Import UpAblEps66Sum.

(* ================= §1 e66p_pi_old_boltzmann 族 ================= *)
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
(* ================= §2 tx2_pi_old 族 ================= *)
(* ############ 实例定义面：π_old 与重要性比率的 Boltzmann 形实例 ####### *)

(* π_old 实例：Boltzmann 形载体件 e66p_pi_old_boltzmann，正性由 e66p_pi_old_pos 供给。 *)
Definition tx2_pi_old (energy : bool -> Real) (D Z : Real)
           (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z)
           (s : bool) : Real :=
  e66p_pi_old_boltzmann bool energy D Z D_pos Z_pos s.

(* 重要性比率 ρ 实例：S08 的 real_importance_ratio_ 应用于上述实例
   （π_old 取 e66p_pi_old_boltzmann，其正性前提取 e66p_pi_old_pos）。 *)
Definition tx2_rho (pi_star energy : bool -> Real) (D Z : Real)
           (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z)
           (s : bool) : Real :=
  real_importance_ratio_ bool pi_star
    (e66p_pi_old_boltzmann bool energy D Z D_pos Z_pos)
    (e66p_pi_old_pos bool energy D Z D_pos Z_pos) s.

(* ############ 主件①：任意 Set 载体与任意枚举表上的实例 ############ *)
(* 剩余前提：D>0、Z>0（π_old 的正性见证）；β>0、eps>0、               *)
(*   ∀s. β·eps ≤ adv(s)（advantage 参数位的 β·eps 边际前提）。             *)

Theorem tx2_ppo66_enum :
  forall (S0 : Set) (enum0 : list S0) (pi_star energy adv : S0 -> Real)
         (D Z beta epsR : Real)
         (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z)
         (Hbeta : real_lt real_zero beta),
    real_lt real_zero epsR ->
    (forall s : S0, real_le (real_mult beta epsR) (adv s)) ->
    real_le
      (e66s_sumf S0 enum0
         (fun s : S0 =>
            real_mult (e66p_pi_old_boltzmann S0 energy D Z D_pos Z_pos s)
              (real_mult
                 (real_min
                    (real_importance_ratio_ S0 pi_star
                       (e66p_pi_old_boltzmann S0 energy D Z D_pos Z_pos)
                       (e66p_pi_old_pos S0 energy D Z D_pos Z_pos) s)
                    (real_ppo_clip_ epsR
                       (real_importance_ratio_ S0 pi_star
                          (e66p_pi_old_boltzmann S0 energy D Z D_pos Z_pos)
                          (e66p_pi_old_pos S0 energy D Z D_pos Z_pos) s)))
                 (adv s))))
      (real_plus
         (e66s_sumf S0 enum0
            (fun s : S0 =>
               real_mult (e66p_pi_old_boltzmann S0 energy D Z D_pos Z_pos s)
                 (real_mult (real_importance_ratio_ S0 pi_star
                               (e66p_pi_old_boltzmann S0 energy D Z D_pos Z_pos)
                               (e66p_pi_old_pos S0 energy D Z D_pos Z_pos) s)
                            (adv s))))
         (e66s_sumf S0 enum0
            (fun s : S0 =>
               real_mult (e66p_pi_old_boltzmann S0 energy D Z D_pos Z_pos s)
                 (real_mult epsR (adv s))))).
Proof.
  intros S0 enum0 pi_star energy adv D Z beta epsR D_pos Z_pos Hbeta Heps Hm.
  exact (real_ppo_conservative_eps S0 (e66s_sumf S0 enum0)
           (e66s_real_sum_over_S_ext S0 enum0)
           (e66s_real_sum_over_S_le S0 enum0)
           (e66s_real_sum_over_S_add S0 enum0)
           pi_star (e66p_pi_old_boltzmann S0 energy D Z D_pos Z_pos)
           (e66p_pi_old_pos S0 energy D Z D_pos Z_pos)
           adv (e66p_real_advantage_pos_margin S0 adv beta epsR Hbeta Heps Hm)
           epsR epsR Heps).
Qed.

(* ############ 主件②：bool 二元载体上的实例 ############ *)
(* 剩余前提与主件①同形（β·eps 边际前提）。 *)

Theorem tx2_ppo66_flag :
  forall (pi_star energy adv : bool -> Real) (D Z beta epsR : Real)
         (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z)
         (Hbeta : real_lt real_zero beta),
    real_lt real_zero epsR ->
    (forall s : bool, real_le (real_mult beta epsR) (adv s)) ->
    real_le
      (e66s_flag_sumf
         (fun s : bool =>
            real_mult (tx2_pi_old energy D Z D_pos Z_pos s)
              (real_mult
                 (real_min (tx2_rho pi_star energy D Z D_pos Z_pos s)
                           (real_ppo_clip_ epsR (tx2_rho pi_star energy D Z D_pos Z_pos s)))
                 (adv s))))
      (real_plus
         (e66s_flag_sumf
            (fun s : bool =>
               real_mult (tx2_pi_old energy D Z D_pos Z_pos s)
                 (real_mult (tx2_rho pi_star energy D Z D_pos Z_pos s) (adv s))))
         (e66s_flag_sumf
            (fun s : bool =>
               real_mult (tx2_pi_old energy D Z D_pos Z_pos s)
                 (real_mult epsR (adv s))))).
Proof.
  intros pi_star energy adv D Z beta epsR D_pos Z_pos Hbeta Heps Hm.
  exact (real_ppo_conservative_eps bool e66s_flag_sumf
           e66s_flag_ext e66s_flag_le e66s_flag_add
           pi_star (e66p_pi_old_boltzmann bool energy D Z D_pos Z_pos)
           (e66p_pi_old_pos bool energy D Z D_pos Z_pos)
           adv (e66p_real_advantage_pos_margin bool adv beta epsR Hbeta Heps Hm)
           epsR epsR Heps).
Qed.

(* ############ 主件③：无假设位版（adv 取定 Boltzmann 形） ############ *)
(* advantage 参数位不再留任何前提：adv := Boltzmann(energy2,D2,Z2)，        *)
(* 其逐点正性由 e66p_pi_old_pos 无条件供给。                            *)
(* 剩余前提仅余数据正性：D>0、Z>0、D2>0、Z2>0、eps>0——无接口假设位。    *)

Theorem tx2_ppo66_flag_closed :
  forall (pi_star energy1 energy2 : bool -> Real) (D Z D2 Z2 epsR : Real)
         (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z)
         (D2_pos : real_lt real_zero D2) (Z2_pos : real_lt real_zero Z2),
    real_lt real_zero epsR ->
    real_le
      (e66s_flag_sumf
         (fun s : bool =>
            real_mult (tx2_pi_old energy1 D Z D_pos Z_pos s)
              (real_mult
                 (real_min (tx2_rho pi_star energy1 D Z D_pos Z_pos s)
                           (real_ppo_clip_ epsR (tx2_rho pi_star energy1 D Z D_pos Z_pos s)))
                 (e66p_pi_old_boltzmann bool energy2 D2 Z2 D2_pos Z2_pos s))))
      (real_plus
         (e66s_flag_sumf
            (fun s : bool =>
               real_mult (tx2_pi_old energy1 D Z D_pos Z_pos s)
                 (real_mult (tx2_rho pi_star energy1 D Z D_pos Z_pos s)
                            (e66p_pi_old_boltzmann bool energy2 D2 Z2 D2_pos Z2_pos s))))
         (e66s_flag_sumf
            (fun s : bool =>
               real_mult (tx2_pi_old energy1 D Z D_pos Z_pos s)
                 (real_mult epsR
                            (e66p_pi_old_boltzmann bool energy2 D2 Z2 D2_pos Z2_pos s))))).
Proof.
  intros pi_star energy1 energy2 D Z D2 Z2 epsR D_pos Z_pos D2_pos Z2_pos Heps.
  exact (real_ppo_conservative_eps bool e66s_flag_sumf
           e66s_flag_ext e66s_flag_le e66s_flag_add
           pi_star (e66p_pi_old_boltzmann bool energy1 D Z D_pos Z_pos)
           (e66p_pi_old_pos bool energy1 D Z D_pos Z_pos)
           (e66p_pi_old_boltzmann bool energy2 D2 Z2 D2_pos Z2_pos)
           (e66p_pi_old_pos bool energy2 D2 Z2 D2_pos Z2_pos)
           epsR epsR Heps).
Qed.

(* ############ 残差权具体形：Σ π_old·(eps·adv) 在 bool 载体上的实例（供提取） ### *)

Definition tx2_flag_resid_weight (energy adv : bool -> Real) (D Z epsR : Real)
           (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z)
           : Real :=
  e66s_flag_sumf (fun s : bool =>
    real_mult (tx2_pi_old energy D Z D_pos Z_pos s) (real_mult epsR (adv s))).

(* ############ 提取核验：tx2_pi_old、tx2_rho、tx2_flag_resid_weight 的计算内容提取 # *)

Set Extraction Output Directory "attn/tx2ex".
Extraction "tx2_66body" tx2_pi_old tx2_rho tx2_flag_resid_weight.

(* ############ 假设闭包核验：以下各定理的假设闭包应为空（Closed） ############## *)

Print Assumptions tx2_ppo66_enum.
Print Assumptions tx2_ppo66_flag.
Print Assumptions tx2_ppo66_flag_closed.
Print Assumptions tx2_flag_resid_weight.
