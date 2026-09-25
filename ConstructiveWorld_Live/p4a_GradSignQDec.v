(* ============================================================ *)
(* ToyR 玩具证替换件 —— T269 台账席 战役包AD（tier2 末批二）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   gsq_kappa_pos（原 L100，4 句玩具证）                                 *)
(* ============================================================ *)

(* ============================================================ *)
(* p4a_GradSignQDec.v —— 席 CZC10（E-STAGING-CZC10）              *)
(*   论文4《资源受限收敛动力学与PCT》假设消融施工：T56 普查档条 4-4    *)
(*   （B 可消融，坐标 L385/L430 开放项 6）。                         *)
(*                                                                *)
(*   槽语句：real_sign_dec 显式三分假设（全符号梯度衰减版的条件化）。   *)
(*   无条件版=LPO 证墙（库内 UpReqLpoEquiv/GibbsWallEquiv/PinWall     *)
(*   三面墙资产已定理化，本件不碰）；本件施工【实例面】：              *)
(*   有理值梯度可计算实例（grad : Q -> Q，S := Q 位势点载体）上，      *)
(*   用 stdlib 构造性三分判定 Q_dec（QArith_base:1075，三支           *)
(*   {x<y}+{y<x}+{x==y}）装填梯度符号分支，消去符号假设，              *)
(*   同型装载 S09_EntropyReal.v:6240 real_grad_decay_full_sign_iter   *)
(*   （RealKappaSignReal 节主定理：|g(x_{n+k})| ≤ κ^k·|g(x_n)|）。     *)
(*                                                                *)
(*   交付面：                                                        *)
(*   主件1 gsq_grad_step_abs_contraction_full：单步全符号收缩           *)
(*         |g(step x)| ≤ κ·|g x|，三分支由 Q_dec 驱动（=S09 节内        *)
(*         real_grad_step_abs_contraction_full 的有理实例面）；        *)
(*   主件2 gsq_grad_decay_full_sign_iter：全符号轨道几何衰减            *)
(*         |g(x_{n+k})| ≤ κ^k·|g(x_n)|（real_grad_decay_full_sign_iter *)
(*         同型装载，κ := 1−ημ 显式前件化）；                         *)
(*   主件3 gsq_grad_tail_budget：给定 N 见证前提的尾界预算              *)
(*         （对偶 UpBudgetReal.v:676 geo_tail_budget 的 Q 层同构，      *)
(*         供 4-5 r_arch_pow 选 N 见证口直接使用）。                   *)
(*                                                                *)
(*   纪律：纯构造性（Q_dec 为和类型构造判定，零经典逻辑）；              *)
(*   前提全显式前件化（论文5"零接口 Variable"纪律）；                  *)
(*   自足零库依赖（仅 stdlib Q 算术）；G1-G4 四关候跑。                *)
(* ============================================================ *)

From Stdlib Require Import QArith_base Qring Qabs Lia.

(* ---- 定义面：线性凸位势梯度实例（势 Φ(x)=μx²/2 的梯度 g(x)=μx） ---- *)

(* 收缩系数 κ := 1 − ημ（显式前件化：0<η, 0<μ, ημ<1 ⟹ κ∈(0,1)） *)
Definition gsq_kappa (eta mu : Q) : Q := 1 - eta * mu.

(* 有理值梯度实例：g(x) := μ·x *)
Definition gsq_grad (mu x : Q) : Q := mu * x.

(* 符号分支动力学：梯度正负两支走下降步 x − η·g(x)，零支驻留。
   三分支由构造性三分判定 Q_dec 驱动——本件消去 real_sign_dec 假设的承重结构。 *)
Definition gsq_step (eta mu x : Q) : Q :=
  match Q_dec (gsq_grad mu x) 0 with
  | inleft (left _) => x - eta * (gsq_grad mu x)
  | inleft (right _) => x - eta * (gsq_grad mu x)
  | inright _ => x
  end.

(* 轨道迭代 x_0 ↦ x_n *)
Fixpoint gsq_iter (eta mu : Q) (n : nat) (x : Q) : Q :=
  match n with
  | O => x
  | S m => gsq_step eta mu (gsq_iter eta mu m x)
  end.

(* 几何幂 κ^n（左乘形态，与 UpBudgetReal real_pow:55 同构） *)
Fixpoint gsq_pow (k : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S m => k * gsq_pow k m
  end.

(* ---- Q 层序桥（Qeq → Qle/Qlt 运输，自足） ---- *)

Lemma gsq_qeq_le : forall a b : Q, a == b -> a <= b.
Proof.
  intros a b H. unfold Qeq in H. unfold Qle.
  rewrite H. apply Z.le_refl.
Qed.

Lemma gsq_qeq_lt_r : forall a b c : Q, b == c -> a < b -> a < c.
Proof.
  intros a b c Hbc Hab.
  apply (Qlt_le_trans a b c).
  - exact Hab.
  - apply gsq_qeq_le. exact Hbc.
Qed.

Lemma gsq_qeq_lt_l : forall a b c : Q, a == b -> b < c -> a < c.
Proof.
  intros a b c Hab Hbc.
  apply (Qle_lt_trans a b c).
  - apply gsq_qeq_le. exact Hab.
  - exact Hbc.
Qed.

Lemma gsq_mult_pos : forall a b : Q, 0 < a -> 0 < b -> 0 < a * b.
Proof.
  intros a b Ha Hb.
  apply (gsq_qeq_lt_r 0%Q (b * a)%Q (a * b)).
  - apply Qmult_comm.
  - apply (gsq_qeq_lt_l 0%Q (0 * a)%Q).
    + apply Qeq_sym. apply Qmult_0_l.
    + apply (Qmult_lt_compat_r 0 (b) (a) Ha Hb).
Qed.

(* ---- κ ∈ (0,1) 良定（Qlt_minus_iff 承载） ---- *)

Lemma gsq_kappa_pos : forall eta mu : Q,
  0 < eta -> 0 < mu -> eta * mu < 1 -> 0 < gsq_kappa eta mu.
Proof.
  intros eta mu He Hmu Hk.
  unfold gsq_kappa.
  apply (proj1 (Qlt_minus_iff (eta * mu) 1)).
  exact Hk.
Qed.

Lemma gsq_kappa_lt_one : forall eta mu : Q,
  0 < eta * mu -> gsq_kappa eta mu < 1.
Proof.
  intros eta mu Hm.
  unfold gsq_kappa.
  apply (proj2 (Qlt_minus_iff (1 - eta * mu)%Q 1)).
  apply (gsq_qeq_lt_r 0%Q (eta * mu) (1 + -(1 - eta * mu))%Q).
  - ring.
  - exact Hm.
Qed.

(* ---- 单步动力学值：step x == κ·x（三分支统一闭合） ---- *)

Lemma gsq_step_val : forall eta mu x : Q,
  gsq_step eta mu x == gsq_kappa eta mu * x.
Proof.
  intros eta mu x. unfold gsq_step, gsq_kappa.
  destruct (Q_dec (gsq_grad mu x) 0) as [[Hlt | Hgt] | Heq].
  - unfold gsq_grad in *. ring.
  - unfold gsq_grad in *. ring.
  - assert (Ht : (1 - eta * mu) * x == x - eta * (mu * x)) by ring.
    unfold gsq_grad in Heq |- *.
    rewrite Ht, Heq. ring.
Qed.

(* ---- 主件1：单步全符号收缩 |g(step x)| ≤ κ·|g x|
      （Q_dec 三分支装载 = 消去 real_sign_dec 假设的实例面交付） ---- *)

Lemma gsq_grad_step_abs_contraction_full : forall eta mu x : Q,
  0 < eta -> 0 < mu -> eta * mu < 1 ->
  Qle (Qabs (gsq_grad mu (gsq_step eta mu x)))
      (gsq_kappa eta mu * Qabs (gsq_grad mu x)).
Proof.
  intros eta mu x He Hmu Hk.
  assert (Hval : Qabs (gsq_grad mu (gsq_step eta mu x))
                 == gsq_kappa eta mu * Qabs (gsq_grad mu x)).
  { unfold gsq_grad.
    rewrite (gsq_step_val eta mu x).
    rewrite (Qabs_Qmult mu (gsq_kappa eta mu * x)).
    rewrite (Qabs_Qmult (gsq_kappa eta mu) x).
    rewrite (Qabs_pos (gsq_kappa eta mu)
               (Qlt_le_weak _ _ (gsq_kappa_pos eta mu He Hmu Hk))).
    rewrite (Qabs_Qmult mu x).
    ring. }
  exact (gsq_qeq_le _ _ Hval).
Qed.

(* ---- 左乘保序（Qmult_le_compat_r 因子序重述） ---- *)

Lemma gsq_le_mult_compat_l : forall a x y : Q,
  0 <= a -> Qle x y -> Qle (a * x) (a * y).
Proof.
  intros a x y Ha Hxy.
  apply (Qle_trans _ (x * a)).
  - apply gsq_qeq_le. apply Qmult_comm.
  - apply (Qle_trans _ (y * a)).
    + apply Qmult_le_compat_r; assumption.
    + apply gsq_qeq_le. apply Qmult_comm.
Qed.

(* ---- 几何幂正性 ---- *)

Lemma gsq_pow_nonneg : forall (k : Q) (n : nat), 0 < k -> 0 <= gsq_pow k n.
Proof.
  intros k n Hk. induction n as [| n IH].
  - cbn [gsq_pow]. apply (Qlt_le_weak _ _).
    unfold Qlt, Qle. cbn. lia.
  - cbn [gsq_pow]. apply (Qle_trans _ (0 * gsq_pow k n)%Q).
    + apply gsq_qeq_le. apply Qeq_sym. apply Qmult_0_l.
    + apply Qmult_le_compat_r; [apply (Qlt_le_weak _ _ Hk) | exact IH].
Qed.

(* ---- 几何幂反单调（real_pow_anti_mono 同型：N ≤ n ⟹ κ^n ≤ κ^N） ---- *)

Lemma gsq_pow_anti_mono : forall (k : Q) (n m : nat),
  0 < k -> k < 1 -> (n <= m)%nat -> Qle (gsq_pow k m) (gsq_pow k n).
Proof.
  intros k n m Hk Hk1 Hnm.
  assert (Hcore : forall j : nat, Qle (gsq_pow k (n + j)%nat) (gsq_pow k n)).
  { intros j. induction j as [| j IHj].
    - replace (n + 0)%nat with n by lia. apply Qle_refl.
    - replace (n + S j)%nat with (S (n + j))%nat by lia.
      cbn [gsq_pow].
      apply (Qle_trans _ (k * gsq_pow k n)%Q).
      + apply gsq_le_mult_compat_l;
          [apply (Qlt_le_weak _ _ Hk) | exact IHj].
      + apply (Qle_trans _ (1 * gsq_pow k n)%Q).
        * apply Qmult_le_compat_r;
            [apply (Qlt_le_weak _ _ Hk1) | apply gsq_pow_nonneg; exact Hk].
        * apply gsq_qeq_le. apply Qmult_1_l. }
  assert (Hq : m = (n + (m - n))%nat) by lia. rewrite Hq. apply Hcore.
Qed.

(* ---- 主件2：全符号轨道几何衰减（real_grad_decay_full_sign_iter 同型装载） ---- *)

Theorem gsq_grad_decay_full_sign_iter : forall (eta mu x0 : Q) (n k : nat),
  0 < eta -> 0 < mu -> eta * mu < 1 ->
  Qle (Qabs (gsq_grad mu (gsq_iter eta mu (n + k) x0)))
      (gsq_pow (gsq_kappa eta mu) k * Qabs (gsq_grad mu (gsq_iter eta mu n x0))).
Proof.
  intros eta mu x0 n k He Hmu Hk.
  assert (Hkap : 0 < gsq_kappa eta mu) by (apply gsq_kappa_pos; assumption).
  induction k as [| k IH].
  - replace (n + 0)%nat with n by lia. cbn [gsq_pow].
    apply gsq_qeq_le. apply Qeq_sym. apply Qmult_1_l.
  - replace (n + S k)%nat with (S (n + k))%nat by lia.
    cbn [gsq_iter gsq_pow].
    apply (Qle_trans _ (gsq_kappa eta mu
                          * Qabs (gsq_grad mu (gsq_iter eta mu (n + k) x0)))).
    + apply gsq_grad_step_abs_contraction_full; assumption.
    + apply (Qle_trans _ (gsq_kappa eta mu
                            * (gsq_pow (gsq_kappa eta mu) k
                               * Qabs (gsq_grad mu (gsq_iter eta mu n x0))))).
      * apply gsq_le_mult_compat_l;
          [apply (Qlt_le_weak _ _ Hkap) | exact IH].
      * apply gsq_qeq_le. apply Qmult_assoc.
Qed.

(* ---- 主件3：尾界预算（geo_tail_budget Q 层对偶：给 N 见证前提出尾界） ---- *)

Theorem gsq_grad_tail_budget : forall (eta mu x0 : Q) (N n : nat) (eps : Q),
  0 < eta -> 0 < mu -> eta * mu < 1 ->
  (N <= n)%nat ->
  Qlt (gsq_pow (gsq_kappa eta mu) N * Qabs (gsq_grad mu x0)) eps ->
  Qlt (Qabs (gsq_grad mu (gsq_iter eta mu n x0))) eps.
Proof.
  intros eta mu x0 N n eps He Hmu Hk Hn Hbudget.
  assert (Hkpos : 0 < eta * mu) by (apply gsq_mult_pos; assumption).
  assert (Hkap : 0 < gsq_kappa eta mu) by (apply gsq_kappa_pos; assumption).
  assert (Hk1 : gsq_kappa eta mu < 1) by (apply gsq_kappa_lt_one; exact Hkpos).
  assert (Hdec : Qle (Qabs (gsq_grad mu (gsq_iter eta mu n x0)))
                     (gsq_pow (gsq_kappa eta mu) n * Qabs (gsq_grad mu x0))).
  { replace n with (0 + n)%nat by lia.
    apply (gsq_grad_decay_full_sign_iter eta mu x0 0 n He Hmu Hk). }
  apply (Qle_lt_trans _ (gsq_pow (gsq_kappa eta mu) N * Qabs (gsq_grad mu x0))).
  - apply (Qle_trans _ (gsq_pow (gsq_kappa eta mu) n * Qabs (gsq_grad mu x0))).
    + exact Hdec.
    + apply Qmult_le_compat_r;
        [apply gsq_pow_anti_mono; assumption | apply Qabs_nonneg].
  - exact Hbudget.
Qed.

(* ---- 四关备件：PA 口径 + G3 提取检验 ---- *)

Print Assumptions gsq_grad_step_abs_contraction_full.
Print Assumptions gsq_grad_decay_full_sign_iter.
Print Assumptions gsq_grad_tail_budget.

From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
Extraction "p4a_gradsignqdec.ml" gsq_grad_decay_full_sign_iter gsq_grad_tail_budget.

Print Assumptions gsq_kappa_pos.
