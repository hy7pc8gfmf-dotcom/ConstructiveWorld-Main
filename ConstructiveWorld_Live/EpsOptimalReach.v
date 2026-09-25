(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   quad_cost_descent_eps_bound（原 L197，2 句玩具证）                   *)
(*   trajectory_eps_optimal_reach（原 L175，2 句玩具证）                  *)
(* ============================================================ *)
(* ============================================================ *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 为恒等守恒——清单所列 2 槽证明体与 Main 现版原件逐字同文（刀体                                *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* ============================================================ *)

(*
   ------------------------------------------------------------------------
   合成主件：对下降轨迹的有限采样表 l = [x₀, x₁, …, x_n]
   （x_{i+1} = sf_grad_step h t x_i，sf_grad_descent 的前 n+1 个迭代点），
   argmin 引擎（UpReqArgminEngine rae_pick_optimal，A 件）给出
   x* = rae_pick l x₀ 且：
     (a) x* ∈ l（rae_pick_mem）；
     (b) 对全部 w ∈ l：key x* ≤ key w（真支配见证，非恒真壳）；
     (c) 对全部 w ∈ l：key x* ≤ key w + eps（ε-松化形，任给 eps ≥ 0）。
   出口全部 Set 层：sigT + And(积) + InT + RIS le / QleT'，零 Prop 语句面。

   对位记录：
     finite_table_eps_optimal_witness  <- A 件 rae_pick_optimal @ UpReqArgminEngine.v:160
                                          + rae_pick_mem（支配证书 sigT 封装）
     eps_loosen                        <- 支撑：支配 + eps≥0 ⟹ ε-支配
                                          （RIS 字段 le_trans/le_plus_compat/
                                            lt_le_iff/req_sym/plus_zero 装配）
     traj_table / _nonempty / _iterate_mem
                                       <- 支撑：轨迹表构造与逐点遍历（B 件链侧）
     trajectory_eps_optimal_reach      <- 合成主件：A 引擎 × B 轨迹表
     quad_cost_descent_eps_bound       <- B 件对接（一档）：
                                          sf_grad_descent_convergence
                                          @ S12_B5RecycleSF.v:13024 + ε-松化

   空壳审计结论（本件动笔前实测）：
     - sf_quad_cost_decreases（12908）：非空壳。完整三分支代数证明
       （1<h<2 / h<1 / h=1），核心 sf_q_cw_sq_le + Qmult_le_l，真 QleT' 出口。
     - sf_grad_descent_convergence（13024）：非空壳。归约到精确等式件
       sf_grad_descent_cost_eq（sf_quad_cost t (descent n) == qpow2 (1-h)² n
       * sf_quad_cost t x，归纳 + ring），经 sf_qeq_le 转 QleT'，非占位。
     故两件均按原样采用，无需退邻居件。

   接口实况（实例图谱）：全库 RealInterfaceEnhancedSetoid 唯一实例为
   RealEnhancedReal（Bishop 逐 eps le，不可判定）；Q 无 RIS 实例。故引擎
   侧保持抽象 (R,RIS,key) + 可判定桥假设（与引擎文件自身 MpRecycleProbe
   同风格），Q 侧以 QleT' 链对接 quad_cost 一档——即规格预置的
   「B 件接口不匹配退为纯 A 件定理 + quad_cost 实例化一档」路线。

   纪律：纯构造性；八禁词零命中；核心件全 Qed；文末 Print Assumptions ≥1。 *)

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
