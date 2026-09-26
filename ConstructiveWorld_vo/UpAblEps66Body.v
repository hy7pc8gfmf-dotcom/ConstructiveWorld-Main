(* ============================================================ *)
(* UpAblEps66Body.v                                              *)
(*                                                               *)
(* 使命：本件形式化 S08 定理 6.6 本体 real_ppo_conservative_eps 的    *)
(*   具体实例——以已供给的求和接口实例（UpAblEps66Sum）与正性实例      *)
(*   （UpAblEps66Pos）代入 Section RealPPOMain 的各假设位，           *)
(*   产出下游直接可用的定理三件：                                   *)
(*                                                               *)
(*   ① tx2_ppo66_enum：任意 Set 载体与任意枚举表上的实例，            *)
(*     剩余前提为 β·eps 边际前提（advantage 参数位的条件形）；             *)
(*   ② tx2_ppo66_flag：bool 二元载体（枚举 true::false）上的实例，     *)
(*     剩余前提同①；                                                *)
(*   ③ tx2_ppo66_flag_closed：bool 载体上取定 adv 为 Boltzmann 形      *)
(*     （e66p_pi_old_boltzmann），其逐点正性由 e66p_pi_old_pos        *)
(*     无条件供给——无剩余假设位，前提仅余数据正性前提                 *)
(*     （D、Z、D2、Z2、eps > 0 的见证形）。                           *)
(*                                                               *)
(*   各假设位的实例化对应：求和外延、保序、加法三参数位分别由             *)
(*   e66s_flag_* 与 e66s_real_sum_over_S_* 供给，求和算子参数位由          *)
(*   e66s_flag_sumf / e66s_sumf 供给，π_old 正性参数由                  *)
(*   e66p_pi_old_pos 供给，advantage 正性参数由边际条件形                *)
(*   e66p_real_advantage_pos_margin 供给（adv 的逐点严格正性对         *)
(*   任意 adv 不成立，条件形为其构造性表述）。                         *)
(*                                                               *)
(*   结构注记：Section RealPPOMain 关闭后，real_ppo_conservative_eps  *)
(*   的各假设位成为显式参数；本件以实例逐一代入，由 exact 一步        *)
(*   完成，无重证。                                                  *)
(*                                                               *)
(* 依赖：S01_BaseRing – S08_RealMainlineDPO（本体所在）、              *)
(*   UpAblEps66Sum（求和接口三件与 bool 载体实例）、                   *)
(*   UpAblEps66Pos（正性两件）。                                     *)
(*                                                               *)
(* 构造性：纯构造性、零承认、全 Qed；语句面全 Set 层（real_lt 为      *)
(*   见证和形、real_le 为 S01 的 Or 和型可解码形），无裸 Prop；        *)
(*   标识符前缀 tx2_。                                              *)
(*                                                               *)
(* 编译：Rocq 9.1 直调 coqc，cpu_guard 限核包裹。验证编译一律         *)
(*   -o 临时目录，树内 .vo 不重写。                                  *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import UpAblEps66Sum.
Require Import UpAblEps66Pos.

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

From Stdlib Require Import Extraction.
Set Extraction Output Directory "attn/tx2ex".
Extraction "tx2_66body" tx2_pi_old tx2_rho tx2_flag_resid_weight.

(* ############ 假设闭包核验：以下各定理的假设闭包应为空（Closed） ############## *)

Print Assumptions tx2_ppo66_enum.
Print Assumptions tx2_ppo66_flag.
Print Assumptions tx2_ppo66_flag_closed.
Print Assumptions tx2_flag_resid_weight.
