(* ==========================================================================)
   EpsOptimalReach.v — 有限表上的 ε-最优选取与梯度下降可达界
   使命: traj_table 迭代表与其成员/非空/迭代命中引理、finite_table_eps_optimal_witness（有限非空表 ε-最优见证）、trajectory_eps_optimal_reach 与 quad_cost_descent_eps_bound（二次代价下降 ε-界）。
   依赖: CW_ConstructiveWorld_219、S01_BaseRing、S02_CauchyComplete、S07_RealSetoidExpLog、S12_B5RecycleSF、UpReqArgminEngine；Stdlib List、QArith、Lia
   对标: 有限点集 ε-最优选取（argmin 的构造性 ε 松弛形）与梯度下降法的二次函数收敛界。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。存在性命题以 sigT 见证形给出。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S12_B5RecycleSF.
Require Import UpReqArgminEngine.
From Stdlib Require Import List QArith Lia.
Import ListNotations.
Import RealInterfaceEnhancedMod.
Open Scope Q_scope.

(* ============================================================ *)
(* 段1：下降轨迹有限采样表（B 件链侧，Q 载体）                     *)
(* ============================================================ *)

(* 采样表 traj_table h t x n = [x; step x; …; stepⁿ x]，
   第 i 项 = sf_grad_descent h t x i（n+1 个点）。 *)
Fixpoint traj_table (h t x : Q) (n : nat) : list Q :=
  match n with
  | O => x :: nil
  | Datatypes.S n' => x :: traj_table h t (sf_grad_step h t x) n'
  end.

Lemma head_InT_traj_table : forall (h t x : Q) (n : nat),
  InT x (traj_table h t x n).
Proof.
  intros h t x n. revert x. induction n as [| n' IH]; intros x; cbn [traj_table].
  - apply InT_here.
  - apply InT_here.
Qed.

(* 表非空（nil 支配案经构造子失配 inversion 闭合——引擎件同位先例） *)
Lemma traj_table_nonempty : forall (h t x : Q) (n : nat),
  Not (Id (traj_table h t x n) nil).
Proof.
  intros h t x n. revert t x. induction n as [| n' IH]; intros t x Hnil;
    cbn [traj_table] in Hnil.
  - inversion Hnil.
  - inversion Hnil.
Qed.

(* 遍历件：第 j 个迭代点必在表中（j ≤ n）——主件 (a) 面的轨迹具体化 *)
Lemma traj_table_iterate_mem : forall (h t x : Q) (n j : nat),
  (j <= n)%nat -> InT (sf_grad_descent h t x j) (traj_table h t x n).
Proof.
  intros h t x n. revert x. induction n as [| n' IH]; intros x j Hj.
  - assert (E : j = 0%nat) by lia.
    rewrite E. cbn [sf_grad_descent traj_table]. apply InT_here.
  - revert Hj. destruct j as [| j']; intros Hj.
    + cbn [sf_grad_descent traj_table]. apply InT_here.
    + cbn [sf_grad_descent traj_table]. apply InT_next.
      apply IH. lia.
Qed.

(* ε-传递件（Q 层）：u ≤ v ∧ 0 ≤ eps ⟹ u ≤ v + eps（QleT' 出口） *)
Lemma qlep_add_eps : forall (u v eps : Q),
  QleT' u v -> QleT' 0 eps -> QleT' u (v + eps).
Proof.
  intros u v eps Huv Heps.
  apply Qle_to_QleT'.
  apply (Qle_trans u v (v + eps)).
  - apply QleT'_to_Qle. exact Huv.
  - apply (Qle_trans v (v + 0) (v + eps)).
    + apply sf_qeq_le. exact (Qeq_sym (v + 0) v (Qplus_0_r v)).
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply QleT'_to_Qle. exact Heps.
Qed.

(* ============================================================ *)
(* 段2：抽象 argmin ε-最优见证（A 件引擎侧）                       *)
(* ============================================================ *)
Section EpsOptimalReachCore.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable A : Set.
Variable key : A -> R.
(* 桥假设位 1+2（UpReqArgminEngine Section 同位：le 二分 / 三分判定） *)
Hypothesis hle_dec : forall a b : R, Or (le a b) (Not (le a b)).
Hypothesis hlt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a)).

(* 支撑件 ε-松化：支配 u ≤ v 加 eps ≥ 0 ⟹ ε-支配 u ≤ v + eps。
   装配：le_trans × (req→le 经 lt_le_iff 右支) × le_plus_compat。 *)
Lemma eps_loosen : forall (u v eps : R),
  le u v -> le zero eps -> le u (plus v eps).
Proof.
  intros u v eps Huv Heps.
  apply (le_trans u v (plus v eps)).
  - exact Huv.
  - apply (le_trans v (plus v zero) (plus v eps)).
    + apply lt_le_iff. apply inr.
      exact (req_sym (plus v zero) v (plus_zero v)).
    + apply le_plus_compat.
      * apply le_refl.
      * exact Heps.
Qed.

(* ε-最优可达见证形（Set 层 sigT 封装：成员 + 支配 + ε-支配） *)
Definition optimal_pick_witness (l : list A) (default : A) (eps : R) : Set :=
  sigT (fun xstar =>
    And (InT xstar l)
        (And (forall w : A, InT w l -> le (key xstar) (key w))
             (forall w : A, InT w l -> le (key xstar) (plus (key w) eps)))).

(* 主件：任意有限非空表 + 任意非负比较阈 eps ⟹ argmin 点的
   支配/逼近 sigT 见证。证书由 A 件引擎直供：
   成员 = rae_pick_mem，支配 = rae_pick_optimal，ε-形 = eps_loosen。 *)
Theorem finite_table_eps_optimal_witness :
  forall (l : list A) (default : A) (eps : R),
    Not (Id l nil) -> le zero eps ->
    optimal_pick_witness l default eps.
Proof.
  intros l default eps Hne Heps.
  refine (existT _ (rae_pick A key hle_dec l default) _).
  split.
  - exact (@rae_pick_mem R RIS A key hle_dec l default Hne).
  - split.
    + intros w Hw.
      exact (@rae_pick_optimal R RIS A key hle_dec hlt_dec l default w Hw).
    + intros w Hw.
      exact (eps_loosen (key (rae_pick A key hle_dec l default)) (key w) eps
               (@rae_pick_optimal R RIS A key hle_dec hlt_dec l default w Hw)
               Heps).
Qed.

End EpsOptimalReachCore.

(* ============================================================ *)
(* 段3：合成——有限轨迹上的 ε-最优可达 + quad_cost 一档对接         *)
(* ============================================================ *)

(* 合成主件：下降轨迹采样表上的 ε-最优可达见证。
   A := Q（B 件轨迹点载体），key 抽象（任意代价函数），
   支配证书由段2 主件在 l := traj_table h t x0 n 接口参数实例化。
   出口：sigT + And + InT + RIS le，零 Prop 语句面。 *)
Theorem trajectory_eps_optimal_reach :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (keyQ : Q -> R)
         (hle_dec : forall a b : R, Or (le a b) (Not (le a b)))
         (hlt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a)))
         (h t x0 : Q) (eps : R) (n : nat),
    le zero eps ->
    sigT (fun xstar =>
      And (InT xstar (traj_table h t x0 n))
          (And (forall w : Q, InT w (traj_table h t x0 n)
                             -> le (keyQ xstar) (keyQ w))
               (forall w : Q, InT w (traj_table h t x0 n)
                             -> le (keyQ xstar) (plus (keyQ w) eps)))).
Proof.
  intros R RIS keyQ hle_dec hlt_dec h t x0 eps n Heps.
  exact (@finite_table_eps_optimal_witness R RIS Q keyQ hle_dec hlt_dec           (traj_table h t x0 n) x0 eps           (traj_table_nonempty h t x0 n) Heps).
Qed.

(* B 件对接（一档）：n 步下降终点的 ε-上界。
   sf_grad_descent_convergence（QleT' 精确收缩界）+ qlep_add_eps 松化。
   注：Q 无 RIS 实例（见头注），故 Q 层 key 实例化走 QleT' 链。 *)
Theorem quad_cost_descent_eps_bound :
  forall (h t x0 eps : Q) (n : nat),
    QltT 0 h -> QltT h 2 -> QleT' 0 eps ->
    QleT' (sf_quad_cost t (sf_grad_descent h t x0 n))
          (qpow2 ((1 - h) * (1 - h)) n * sf_quad_cost t x0 + eps).
Proof.
  intros h t x0 eps n Hh H2 Heps.
  exact (qlep_add_eps (sf_quad_cost t (sf_grad_descent h t x0 n))           (qpow2 ((1 - h) * (1 - h)) n * sf_quad_cost t x0) eps           (sf_grad_descent_convergence h t x0 n Hh H2) Heps).
Qed.

(* 审查留痕面：G4（≥1 语句） *)
Print Assumptions finite_table_eps_optimal_witness.
Print Assumptions trajectory_eps_optimal_reach.
Print Assumptions quad_cost_descent_eps_bound.
Print Assumptions traj_table_iterate_mem.
