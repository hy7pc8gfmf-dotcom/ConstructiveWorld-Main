(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* QstepConvergenceBound.v —— 位 C9：qstep 迭代收敛步数界          *)
(*   （A4 移植榜 T9：迭代 eps 形模板 → Q 层 qstep 轨道移植）          *)
(* ------------------------------------------------------------ *)
(* 受体（单步收缩引擎，直接使用 .vo）：                               *)
(*   S13_NLiveAudit.v L461 qstep_contracts：                        *)
(*     forall h x g, QltT 0 h -> QleT' h (Qabs (g - x)) ->          *)
(*       QId (Qabs (g - qstep h x g)) (Qabs (g - x) - h).           *)
(*   qstep h x g = x + h * qsign (g - x)（L407）。                  *)
(* 供体（迭代 eps 形模板，结构移植）：                                *)
(*   UpReqGeomIter.v L587 geodi_iter_one_step_eps /                  *)
(*   L663 two_steps_eps / L777 policy_iter_kl_geom_iter_eps：        *)
(*   「t 步幂 κ^t·KL0 + eps 出口 + 可计算步数」形。                  *)
(* ------------------------------------------------------------ *)
(* 合成主件（全部 Q 层、出口零 Prop 语句面）：                        *)
(*   qstep_iter_geometric_bound：                                   *)
(*     forall r x0 xg k, QltT r 1 -> QleT' 0 r ->                   *)
(*       QleT' (Qabs (xg - qiter r x0 xg k)) (qpow r k * Qabs (xg - x0)) *)
(*     （前提面照 qstep_contracts 的 QltT/QleT' 面；内含 QId 精确形    *)
(*      qiter_dist_geometric_id：dist_k == r^k·dist_0。）            *)
(*   qstep_step_bound：                                             *)
(*     forall r x0 xg eps, QltT 0 r -> QltT r 1 -> QltT' 0 eps ->    *)
(*       sigT (fun N => forall k, (N <= k)%nat ->                   *)
(*         QleT' (Qabs (xg - qiter r x0 xg k)) eps)                 *)
(*     其中 N = qstep_step_N := Z.to_nat (Qceiling (d0/(eps·(1−r)))) *)
(*     —— 由 r<1 的几何倒数经 Qceiling 的显式可计算步数公式。          *)
(* 支撑件 ≥2：                                                       *)
(*   qpow_mono_dec（r<1 幂单调递减件，QleT' 面）                     *)
(*   qiter_dist_recur（迭代距离递推件，QId 面，逐例使用受体）          *)
(*   qbern_kt（Bernoulli 型幂界：(1+kt)·r^k ≤ 1，可计算步数引擎）     *)
(* ------------------------------------------------------------ *)
(* 红线自审：出口 QltT'/QleT'/sigT；零 承认 族、零经典逻辑；          *)
(*   文末 Print Assumptions ≥2；nat 加法全限定 PeanoNat.Nat.add；     *)
(*   Q_scope 内 change 项带 %nat/%Z 标注；apply 显式喂项序；           *)
(*   本版 stdlib 无 Qabs_eq——Qabs_pos/Qabs_neg + Q_dec 三分替代。    *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import UpReqGeomIter.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith ZArith.ZArith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ============================================================ *)
(* A. 薄壳严格 T 面：QltT'（对偶 S02 QleT' 的 bool 反映形；           *)
(*    S02 只有 QltT/QleT'，补严格比较的 T' 面）                  *)
(* ============================================================ *)

Definition QltT' (x y : Q) : Set := Id (Qlt_bool x y) true.

Lemma QltT'_to_QltT : forall x y : Q, QltT' x y -> QltT x y.
Proof. intros x y H. exact H. Qed.

Lemma QltT'_to_Qlt : forall x y : Q, QltT' x y -> Qlt x y.
Proof. intros x y H. exact (QltT_to_Qlt x y H). Qed.

Lemma Qlt_to_QltT' : forall x y : Q, Qlt x y -> QltT' x y.
Proof. intros x y H. exact (Qlt_to_QltT x y H). Qed.

(* ============================================================ *)
(* B. Prop-Q 有序小件（全部经 Qplus_le_compat + Qeq 同余装配，        *)
(*    避免 lia 对 Q 分母结构的依赖）                                 *)
(* ============================================================ *)

Lemma qle_congr_l' : forall a b c : Q, a == b -> Qle a c -> Qle b c.
Proof. exact qle_congr_l. Qed.

Lemma qle_neq_imp_lt : forall x y : Q, Qle x y -> ~ (x == y) -> Qlt x y.
Proof.
  intros x y Hle Hne. destruct (Q_dec x y) as [[Hlt | Hgt] | Heq].
  - exact Hlt.
  - exfalso. exact (Qlt_irrefl y (Qlt_le_trans y x y Hgt Hle)).
  - exfalso. apply Hne. exact Heq.
Qed.

Lemma qle_pos_minus : forall a b : Q, Qle a b -> Qle 0 (b - a).
Proof.
  intros a b Hle.
  apply (qle_congr_l (a + - a) 0 (b - a)).
  - ring.
  - apply (qle_congr_r (a + - a) (b + - a) (b - a)).
    + ring.
    + exact (Qplus_le_compat a b (- a) (- a) Hle (Qle_refl (- a))).
Qed.

Lemma qle_minus_pos : forall a b : Q, Qle 0 (b - a) -> Qle a b.
Proof.
  intros a b H.
  apply (qle_congr_l (0 + a) a b).
  - ring.
  - apply (qle_congr_r (0 + a) ((b - a) + a) b).
    + ring.
    + exact (Qplus_le_compat 0 (b - a) a a H (Qle_refl a)).
Qed.

Lemma qlt_pos_minus : forall a b : Q, Qlt a b -> Qlt 0 (b - a).
Proof.
  intros a b Hlt.
  apply (qle_neq_imp_lt 0 (b - a)).
  - apply qle_pos_minus. exact (Qlt_le_weak a b Hlt).
  - intro Hz.
    assert (Hz' : b - a == 0) by (exact (Qeq_sym 0 (b - a) Hz)).
    assert (Hba : b == a).
    { apply (Qeq_trans b ((b - a) + a) a).
      - ring.
      - rewrite Hz'. ring. }
    rewrite Hba in Hlt. exact (Qlt_irrefl a Hlt).
Qed.

Lemma qle_neg : forall x : Q, Qle x 0 -> Qle 0 (- x).
Proof.
  intros x H.
  apply (qle_congr_l (x + - x) 0 (- x)).
  - ring.
  - apply (qle_congr_r (x + - x) (0 + - x) (- x)).
    + ring.
    + exact (Qplus_le_compat x 0 (- x) (- x) H (Qle_refl (- x))).
Qed.

Lemma qlt_neg : forall x : Q, Qlt x 0 -> Qlt 0 (- x).
Proof.
  intros x H.
  apply (qle_neq_imp_lt 0 (- x)).
  - apply qle_neg. exact (Qlt_le_weak x 0 H).
  - intro Hz.
    assert (Hz' : - x == 0) by (exact (Qeq_sym 0 (- x) Hz)).
    assert (Hx0 : x == 0).
    { apply (Qeq_trans x (- (- x)) 0).
      - ring.
      - rewrite Hz'. reflexivity. }
    rewrite Hx0 in H. exact (Qlt_irrefl 0 H).
Qed.

Lemma qltT_pos_minus : forall a b : Q, QltT a b -> QltT 0 (b - a).
Proof.
  intros a b Hab. apply Qlt_to_QltT'.
  apply qlt_pos_minus. exact (QltT_to_Qlt a b Hab).
Qed.

Lemma qleT'_one_minus : forall r : Q, QleT' 0 r -> QleT' (1 - r) 1.
Proof.
  intros r H. apply Qle_to_QleT'.
  apply (qle_minus_pos (1 - r) 1).
  apply (qle_congr_r 0 r (1 - (1 - r))).
  - ring.
  - exact (QleT'_to_Qle 0 r H).
Qed.

(* Qabs 三分小件：|y| == 0 ⟺ y == 0；y == 0 \/ 0 < |y|。 *)
Lemma qabs_eq0_imp : forall y : Q, Qabs y == 0 -> y == 0.
Proof.
  intros y Hy. destruct (Q_dec y 0) as [[Hy1 | Hy1] | Hy1].
  - (* y < 0 *)
    exfalso.
    assert (Hle : Qle y 0) by (exact (Qlt_le_weak y 0 Hy1)).
    rewrite (Qabs_neg y Hle) in Hy.
    assert (Hy0 : y == 0).
    { apply (Qeq_trans y (- (- y)) 0).
      - ring.
      - rewrite Hy. reflexivity. }
    rewrite Hy0 in Hy1. exact (Qlt_irrefl 0 Hy1).
  - (* 0 < y *)
    exfalso.
    assert (Hle : Qle 0 y) by (exact (Qlt_le_weak 0 y Hy1)).
    rewrite (Qabs_pos y Hle) in Hy.
    rewrite Hy in Hy1. exact (Qlt_irrefl 0 Hy1).
  - (* y == 0 *)
    exact Hy1.
Qed.

Lemma qlt_abs_cases : forall y : Q, y == 0 \/ Qlt 0 (Qabs y).
Proof.
  intros y. destruct (Q_dec y 0) as [[Hy | Hy] | Hy].
  - (* y < 0 *)
    right.
    assert (Hle : Qle y 0) by (exact (Qlt_le_weak y 0 Hy)).
    rewrite (Qabs_neg y Hle). apply qlt_neg. exact Hy.
  - (* 0 < y *)
    right.
    assert (Hle : Qle 0 y) by (exact (Qlt_le_weak 0 y Hy)).
    rewrite (Qabs_pos y Hle). exact Hy.
  - (* y == 0 *)
    left. exact Hy.
Qed.

(* Qabs 对 Qeq 的同余（stdlib 未注册 Qabs 形态隐喻，自证）：
   只用整项重写 + 已注册的 Qopp/Qlt 形态隐喻。 *)
Lemma qabs_eq_compat : forall x y : Q, x == y -> Qabs x == Qabs y.
Proof.
  intros x y Hxy. destruct (Q_dec x 0) as [[Hx | Hx] | Hx].
  - (* x < 0 *)
    assert (Hle : Qle x 0) by (exact (Qlt_le_weak x 0 Hx)).
    rewrite (Qabs_neg x Hle).
    assert (Hy : Qlt y 0).
    { rewrite <- Hxy. exact Hx. }
    assert (Hle2 : Qle y 0) by (exact (Qlt_le_weak y 0 Hy)).
    rewrite (Qabs_neg y Hle2).
    rewrite Hxy. reflexivity.
  - (* 0 < x *)
    assert (Hle : Qle 0 x) by (exact (Qlt_le_weak 0 x Hx)).
    rewrite (Qabs_pos x Hle).
    assert (Hy : Qlt 0 y).
    { rewrite <- Hxy. exact Hx. }
    assert (Hle2 : Qle 0 y) by (exact (Qlt_le_weak 0 y Hy)).
    rewrite (Qabs_pos y Hle2). exact Hxy.
  - (* x == 0 *)
    assert (Hz1 : Qabs x == 0).
    { apply (Qeq_trans (Qabs x) x 0).
      - exact (Qabs_pos x (qeq_imp_qle 0 x (Qeq_sym x 0 Hx))).
      - exact Hx. }
    assert (Hy : y == 0).
    { rewrite <- Hxy. exact Hx. }
    assert (Hz2 : Qabs y == 0).
    { apply (Qeq_trans (Qabs y) y 0).
      - exact (Qabs_pos y (qeq_imp_qle 0 y (Qeq_sym y 0 Hy))).
      - exact Hy. }
    exact (Qeq_trans (Qabs x) 0 (Qabs y) Hz1 (Qeq_sym (Qabs y) 0 Hz2)).
Qed.

(* ============================================================ *)
(* C. 幂载体与幂单调递减件（支撑件一）                                *)
(* ============================================================ *)

Fixpoint qpow (r : Q) (k : nat) : Q :=
  match k with
  | O => 1
  | Datatypes.S k' => r * qpow r k'
  end.

Lemma qpow_nonneg : forall (k : nat) (r : Q), Qle 0 r -> Qle 0 (qpow r k).
Proof.
  induction k as [| k IH]; intros r Hr.
  - exact Qle_0_1.
  - change (qpow r (Datatypes.S k)) with (r * qpow r k).
    apply (qle_congr_l (0 * qpow r k) 0 (r * qpow r k)).
    + ring.
    + exact (Qmult_le_compat_r 0 r (qpow r k) Hr (IH r Hr)).
Qed.

(* 支撑件一（r<1 幂单调递减，QleT' 面）：0 ≤ r ≤ 1 ⟹ r^(k+1) ≤ r^k。 *)
Lemma qpow_mono_dec :
  forall (r : Q) (k : nat), QleT' 0 r -> QleT' r 1 ->
    QleT' (qpow r (Datatypes.S k)) (qpow r k).
Proof.
  intros r k H0 H1.
  change (qpow r (Datatypes.S k)) with (r * qpow r k).
  assert (Hqpos : QleT' 0 (qpow r k))
    by (exact (Qle_to_QleT' 0 (qpow r k) (qpow_nonneg k r (QleT'_to_Qle 0 r H0)))).
  apply (qleT'_trans (r * qpow r k) (1 * qpow r k) (qpow r k)).
  - exact (qleT'_mult_compat_r r 1 (qpow r k) Hqpos H1).
  - apply (qeq_leT' (1 * qpow r k) (qpow r k)). ring.
Qed.

(* ============================================================ *)
(* D. 迭代轨道与距离递推件（支撑件二；受体 qstep 逐例使用）             *)
(* ============================================================ *)

(* 受体步映射上的迭代轨道：x_0 := x0，
   x_{k+1} = qstep ((1−r)·|x* − x_k|) x* x_k（率 r，步长 (1−r)·|d|）。
   前提面照 qstep_contracts：0 < h ≤ |g−x| 的比率化：
   QltT r 1（⟹ 0 < 1−r）与 QleT' 0 r（⟹ (1−r) ≤ 1）。 *)
Fixpoint qiter (r x xg : Q) (k : nat) : Q :=
  match k with
  | O => x
  | Datatypes.S k' => qstep ((1 - r) * Qabs (xg - qiter r x xg k')) (qiter r x xg k') xg
  end.

(* 支撑件二（迭代距离递推件，QId 面）：
   主例（0 < |x* − x_k|）喂受体 qstep_contracts；退化例（x_k == x*）归零。
   三分用 Set 层 Q_dec（Prop 判别式不可消去入 Set，红线纪律）。 *)
Lemma qiter_dist_recur_pos :
  forall (r x xg : Q) (k : nat),
    QltT r 1 -> QleT' 0 r -> QltT 0 (Qabs (xg - qiter r x xg k)) ->
    QId (Qabs (xg - qiter r x xg (Datatypes.S k)))
        (r * Qabs (xg - qiter r x xg k)).
Proof.
  intros r x xg k Hr1 Hr0 Hp.
  assert (Ht : QltT 0 (1 - r)) by (exact (qltT_pos_minus r 1 Hr1)).
  assert (P1 : QltT 0 ((1 - r) * Qabs (xg - qiter r x xg k))).
  { exact (qmult_ltT_0_compat (1 - r) (Qabs (xg - qiter r x xg k)) Ht Hp). }
  assert (P2 : QleT' ((1 - r) * Qabs (xg - qiter r x xg k))
                     (Qabs (xg - qiter r x xg k))).
  { apply (qleT'_trans ((1 - r) * Qabs (xg - qiter r x xg k))
                       (1 * Qabs (xg - qiter r x xg k))
                       (Qabs (xg - qiter r x xg k))).
    - exact (qleT'_mult_compat_r (1 - r) 1 (Qabs (xg - qiter r x xg k))
               (qabs_nonnegT (xg - qiter r x xg k))
               (qleT'_one_minus r Hr0)).
    - apply (qeq_leT' (1 * Qabs (xg - qiter r x xg k))
                      (Qabs (xg - qiter r x xg k))). ring. }
  apply qid_intro.
  apply (Qeq_trans (Qabs (xg - qstep ((1 - r) * Qabs (xg - qiter r x xg k))
                              (qiter r x xg k) xg))
                   (Qabs (xg - qiter r x xg k)
                      - (1 - r) * Qabs (xg - qiter r x xg k))
                   (r * Qabs (xg - qiter r x xg k))).
  + exact (qid_elim (Qabs (xg - qstep ((1 - r) * Qabs (xg - qiter r x xg k))
                                (qiter r x xg k) xg))
                    (Qabs (xg - qiter r x xg k)
                       - (1 - r) * Qabs (xg - qiter r x xg k))
                    (qstep_contracts ((1 - r) * Qabs (xg - qiter r x xg k))
                                     (qiter r x xg k) xg P1 P2)).
  + ring.
Qed.

Lemma qiter_dist_recur :
  forall (r x xg : Q) (k : nat),
    QltT r 1 -> QleT' 0 r ->
    QId (Qabs (xg - qiter r x xg (Datatypes.S k))) (r * Qabs (xg - qiter r x xg k)).
Proof.
  intros r x xg k Hr1 Hr0.
  destruct (Q_dec (xg - qiter r x xg k) 0) as [[Hlt0 | Hgt0] | Heq0].
  - (* x* − x_k < 0：|·| == −(·) > 0 *)
    apply (qiter_dist_recur_pos r x xg k Hr1 Hr0).
    apply Qlt_to_QltT.
    assert (Hle : Qle (xg - qiter r x xg k) 0)
      by (exact (Qlt_le_weak (xg - qiter r x xg k) 0 Hlt0)).
    rewrite (Qabs_neg (xg - qiter r x xg k) Hle).
    apply qlt_neg. exact Hlt0.
  - (* x* − x_k > 0：|·| == · > 0 *)
    apply (qiter_dist_recur_pos r x xg k Hr1 Hr0).
    apply Qlt_to_QltT.
    assert (Hle : Qle 0 (xg - qiter r x xg k))
      by (exact (Qlt_le_weak 0 (xg - qiter r x xg k) Hgt0)).
    rewrite (Qabs_pos (xg - qiter r x xg k) Hle). exact Hgt0.
  - (* 退化例：x* − x_k == 0 *)
    assert (Hxk : qiter r x xg k == xg).
    { apply (Qeq_trans (qiter r x xg k) (xg - (xg - qiter r x xg k)) xg).
      - ring.
      - rewrite Heq0. ring. }
    assert (Hzabs : Qabs (xg - qiter r x xg k) == 0).
    { apply (Qeq_trans (Qabs (xg - qiter r x xg k))
                       (xg - qiter r x xg k) 0).
      - exact (Qabs_pos (xg - qiter r x xg k)
                        (qeq_imp_qle 0 (xg - qiter r x xg k)
                          (Qeq_sym (xg - qiter r x xg k) 0 Heq0))).
      - exact Heq0. }
    apply qid_intro.
    apply (Qeq_trans (Qabs (xg - qstep ((1 - r) * Qabs (xg - qiter r x xg k))
                                  (qiter r x xg k) xg))
                     0
                     (r * Qabs (xg - qiter r x xg k))).
    + apply (qabs_eq_compat
               (xg - qstep ((1 - r) * Qabs (xg - qiter r x xg k))
                           (qiter r x xg k) xg)
               0).
      unfold qstep.
      rewrite (qsign_zero (xg - qiter r x xg k) Heq0).
      rewrite Hzabs.
      rewrite Hxk.
      ring.
    + rewrite Hzabs. ring.
Qed.

(* 精确几何形：dist_k == r^k · dist_0（QId 面）。 *)
Lemma qiter_dist_geometric_id :
  forall (r x xg : Q) (k : nat),
    QltT r 1 -> QleT' 0 r ->
    QId (Qabs (xg - qiter r x xg k)) (qpow r k * Qabs (xg - x)).
Proof.
  intros r x xg k. induction k as [| k IH]; intros Hr1 Hr0.
  - change (qiter r x xg 0) with x.
    change (qpow r 0) with 1.
    apply qid_intro. ring.
  - change (qiter r x xg (Datatypes.S k))
      with (qstep ((1 - r) * Qabs (xg - qiter r x xg k))
                  (qiter r x xg k) xg).
    apply qid_intro.
    apply (Qeq_trans (Qabs (xg - qstep ((1 - r) * Qabs (xg - qiter r x xg k))
                                  (qiter r x xg k) xg))
                     (r * Qabs (xg - qiter r x xg k))
                     (qpow r (Datatypes.S k) * Qabs (xg - x))).
    + exact (qid_elim (Qabs (xg - qstep ((1 - r) * Qabs (xg - qiter r x xg k))
                                    (qiter r x xg k) xg))
                      (r * Qabs (xg - qiter r x xg k))
                      (qiter_dist_recur r x xg k Hr1 Hr0)).
    + rewrite (qid_elim (Qabs (xg - qiter r x xg k))
                        (qpow r k * Qabs (xg - x)) (IH Hr1 Hr0)).
      change (qpow r (Datatypes.S k)) with (r * qpow r k).
      ring.
Qed.

(* ============================================================ *)
(* E. 主件一：迭代 k 步距离 ≤ r^k · 初距（QleT' 出口）                *)
(* ============================================================ *)

Theorem qstep_iter_geometric_bound :
  forall (r x0 xg : Q) (k : nat),
    QltT r 1 -> QleT' 0 r ->
    QleT' (Qabs (xg - qiter r x0 xg k)) (qpow r k * Qabs (xg - x0)).
Proof.
  intros r x0 xg k Hr1 Hr0.
  apply (qeq_leT' (Qabs (xg - qiter r x0 xg k)) (qpow r k * Qabs (xg - x0))).
  exact (qid_elim (Qabs (xg - qiter r x0 xg k)) (qpow r k * Qabs (xg - x0))
                  (qiter_dist_geometric_id r x0 xg k Hr1 Hr0)).
Qed.

(* ============================================================ *)
(* F. Bernoulli 型幂界（可计算步数引擎）：(1 + kt)·r^k ≤ 1            *)
(*    证法：r = 1−t 归一 + (1+(k+1)t)r == (1+kt) − (k+1)t² 一步      *)
(*    递推（Qsquare_nonneg 喂非负余项），零经典逻辑。                 *)
(* ============================================================ *)

Definition QofN (k : nat) : Q := (Z.of_nat k # 1)%Q.

Lemma QofN_succ : forall k : nat, QofN (Datatypes.S k) == QofN k + 1.
Proof.
  intros k. unfold QofN, Qeq.
  cbn [Qnum Qden Qplus].
  rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma QofN_0 : QofN 0 == 0.
Proof. unfold QofN. reflexivity. Qed.

Lemma qle0_QofN_succ : forall k : nat, Qle 0 (QofN k + 1).
Proof.
  intros k. unfold QofN, Qle. cbn [Qnum Qden Qplus]. lia.
Qed.

Lemma qbern_kt : forall (r t : Q) (k : nat),
  Qlt 0 t -> r + t == 1 -> Qle 0 r ->
  (1 + QofN k * t) * qpow r k <= 1.
Proof.
  intros r t k Ht Hrt Hr0. induction k as [| k IH].
  - rewrite QofN_0.
    change (qpow r 0) with 1.
    apply (qeq_imp_qle ((1 + 0 * t) * 1) 1). ring.
  - rewrite (QofN_succ k).
    change (qpow r (Datatypes.S k)) with (r * qpow r k).
    assert (Hr' : r == 1 - t).
    { apply (Qeq_trans r (r + t - t) (1 - t)).
      - ring.
      - rewrite Hrt. reflexivity. }
    (* 率等价形经 Qmult_comp 换元（qpow 内 r 不可达，禁 rewrite） *)
    apply (qle_congr_l ((1 + (QofN k + 1) * t) * ((1 - t) * qpow r k))
                       ((1 + (QofN k + 1) * t) * (r * qpow r k)) 1).
    + exact (@Qmult_comp (1 + (QofN k + 1) * t) (1 + (QofN k + 1) * t)
               (Qeq_refl (1 + (QofN k + 1) * t))
               ((1 - t) * qpow r k) (r * qpow r k)
               (Qeq_sym (r * qpow r k) ((1 - t) * qpow r k)
                  (@Qmult_comp r (1 - t) Hr' (qpow r k) (qpow r k)
                     (Qeq_refl (qpow r k))))).
    + assert (Hstep : (1 + (QofN k + 1) * t) * ((1 - t) * qpow r k)
                      == ((1 + QofN k * t) - (QofN k + 1) * (t * t)) * qpow r k)
        by ring.
      rewrite Hstep.
      assert (Hsq : Qle 0 ((QofN k + 1) * (t * t))).
      { apply (qle_congr_l (0 * (t * t)) 0 ((QofN k + 1) * (t * t))).
        - ring.
        - exact (Qmult_le_compat_r 0 (QofN k + 1) (t * t)
                   (qle0_QofN_succ k) (Qsquare_nonneg t)). }
      assert (Hpos : Qle 0 (qpow r k)) by (exact (qpow_nonneg k r Hr0)).
      apply (Qle_trans (((1 + QofN k * t) - (QofN k + 1) * (t * t)) * qpow r k)
                       ((1 + QofN k * t) * qpow r k) 1).
      * apply (Qmult_le_compat_r ((1 + QofN k * t) - (QofN k + 1) * (t * t))
                                 (1 + QofN k * t) (qpow r k)).
        -- apply (Qle_trans ((1 + QofN k * t) - (QofN k + 1) * (t * t))
                            (((1 + QofN k * t) - (QofN k + 1) * (t * t))
                               + (QofN k + 1) * (t * t))
                            (1 + QofN k * t)).
           ++ exact (Qle_plus_nonneg_r ((1 + QofN k * t) - (QofN k + 1) * (t * t))
                                       ((QofN k + 1) * (t * t)) Hsq).
           ++ apply (qeq_imp_qle (((1 + QofN k * t) - (QofN k + 1) * (t * t))
                                    + (QofN k + 1) * (t * t))
                                 (1 + QofN k * t)). ring.
        -- exact Hpos.
      * exact IH.
Qed.

(* ============================================================ *)
(* G. 主件二：可计算步数界（sigT 出口，显式 N 公式）                   *)
(*    N = Z.to_nat (Qceiling (d0 / (eps·(1−r))))                     *)
(*    —— 由 r<1 与初距的几何倒数经 Qceiling 构造。                    *)
(* ============================================================ *)

Definition qstep_step_N (r x0 xg eps : Q) : nat :=
  Z.to_nat (Qceiling (Qabs (xg - x0) / (eps * (1 - r)))).

(* 主例引擎：0 < 初距 时显式 N 的达标证明（Qceiling 链 + Bernoulli 幂界）。 *)
Lemma qstep_step_bound_main :
  forall (r x0 xg eps : Q) (k : nat),
    QltT 0 r -> QltT r 1 -> QltT' 0 eps -> Qlt 0 (Qabs (xg - x0)) ->
    (qstep_step_N r x0 xg eps <= k)%nat ->
    QleT' (Qabs (xg - qiter r x0 xg k)) eps.
Proof.
  intros r x0 xg eps k Hr0 Hr1 Heps Hd Hk.
  unfold qstep_step_N in Hk.
  assert (HepsT : QltT 0 eps) by (exact (QltT'_to_QltT 0 eps Heps)).
  assert (Htp : Qlt 0 (1 - r)) by (exact (QltT_to_Qlt 0 (1 - r)
                                          (qltT_pos_minus r 1 Hr1))).
  assert (Hrt : r + (1 - r) == 1) by ring.
  assert (Hr0p : Qle 0 r)
    by (exact (QleT'_to_Qle 0 r (qltT_leT' 0 r Hr0))).
  assert (Hzp : QltT 0 (eps * (1 - r)))
    by (exact (qmult_ltT_0_compat eps (1 - r) HepsT
                 (qltT_pos_minus r 1 Hr1))).
  assert (Hzne : ~ (eps * (1 - r) == 0)).
  { intro Hc. exact (qltT_not_eq_zero (eps * (1 - r)) Hzp Hc). }
  (* num := d0/(eps·(1−r)) 的 Qceiling 链 *)
  assert (Hnump : Qlt 0 (Qabs (xg - x0) / (eps * (1 - r)))).
  { apply (QltT_to_Qlt 0 _). apply (qltT_div_pos (Qabs (xg - x0)) (eps * (1 - r))).
    - exact (Qlt_to_QltT _ _ Hd).
    - exact Hzp. }
  assert (Hq0 : Qle 0 (inject_Z (Qceiling (Qabs (xg - x0) / (eps * (1 - r)))))).
  { apply (Qle_trans 0 (Qabs (xg - x0) / (eps * (1 - r)))
                      (inject_Z (Qceiling (Qabs (xg - x0) / (eps * (1 - r)))))).
    - exact (Qlt_le_weak 0 _ Hnump).
    - apply Qle_ceiling. }
  assert (Hzc : (0 <= Qceiling (Qabs (xg - x0) / (eps * (1 - r))))%Z).
  { unfold Qle, inject_Z in Hq0. cbn [Qnum Qden] in Hq0. lia. }
  assert (HNz : Z.of_nat (Z.to_nat (Qceiling (Qabs (xg - x0) / (eps * (1 - r)))))
                = Qceiling (Qabs (xg - x0) / (eps * (1 - r)))).
  { exact (Z2Nat.id _ Hzc). }
  assert (Hzk : (Qceiling (Qabs (xg - x0) / (eps * (1 - r))) <= Z.of_nat k)%Z).
  { rewrite <- HNz. lia. }
  assert (HqN : Qle (inject_Z (Qceiling (Qabs (xg - x0) / (eps * (1 - r)))))
                    (QofN k)).
  { unfold QofN, inject_Z, Qle. cbn [Qnum Qden].
    rewrite <- HNz. lia. }
  (* num ≤ QofN k，乘回 eps·(1−r) 得 d0 ≤ QofN k·(eps·(1−r)) *)
  assert (HnumN : Qle (Qabs (xg - x0) / (eps * (1 - r))) (QofN k)).
  { apply (Qle_trans (Qabs (xg - x0) / (eps * (1 - r)))
                     (inject_Z (Qceiling (Qabs (xg - x0) / (eps * (1 - r)))))
                     (QofN k)).
    - apply Qle_ceiling.
    - exact HqN. }
  assert (Hmul : Qle ((Qabs (xg - x0) / (eps * (1 - r))) * (eps * (1 - r)))
                     (QofN k * (eps * (1 - r)))).
  { apply (Qmult_le_compat_r (Qabs (xg - x0) / (eps * (1 - r))) (QofN k)
                             (eps * (1 - r)) HnumN).
    exact (Qlt_le_weak 0 (eps * (1 - r))
             (QltT_to_Qlt 0 (eps * (1 - r)) Hzp)). }
  assert (Hf : Qle (Qabs (xg - x0)) (QofN k * (eps * (1 - r)))).
  { apply (qle_congr_l ((Qabs (xg - x0) / (eps * (1 - r))) * (eps * (1 - r)))
                       (Qabs (xg - x0)) (QofN k * (eps * (1 - r)))).
    - apply (Qeq_trans ((Qabs (xg - x0) / (eps * (1 - r))) * (eps * (1 - r)))
                       ((eps * (1 - r)) * (Qabs (xg - x0) / (eps * (1 - r))))
                       (Qabs (xg - x0))).
      + ring.
      + exact (Qmult_div_r (Qabs (xg - x0)) (eps * (1 - r)) Hzne).
    - exact Hmul. }
  (* Bernoulli 幂界 + 尾链闭合（Prop-Q 层） *)
  assert (Hb : Qle ((1 + QofN k * (1 - r)) * qpow r k) 1).
  { exact (qbern_kt r (1 - r) k Htp Hrt Hr0p). }
  assert (Hb' : Qle (QofN k * (1 - r) * qpow r k) 1).
  { assert (Hb2 : Qle (qpow r k + QofN k * (1 - r) * qpow r k)
                      (qpow r k + (1 - qpow r k))).
    { apply (qle_congr_r (qpow r k + QofN k * (1 - r) * qpow r k) 1
                         (qpow r k + (1 - qpow r k))).
      - ring.
      - apply (qle_congr_l ((1 + QofN k * (1 - r)) * qpow r k)
                           (qpow r k + QofN k * (1 - r) * qpow r k) 1).
        + ring.
        + exact Hb. }
    assert (Hb3 : Qle (QofN k * (1 - r) * qpow r k) (1 - qpow r k)).
    { exact (proj1 (Qplus_le_r (QofN k * (1 - r) * qpow r k)
                               (1 - qpow r k) (qpow r k)) Hb2). }
    assert (Hpos : Qle 0 (qpow r k)) by (exact (qpow_nonneg k r Hr0p)).
    apply (Qle_trans (QofN k * (1 - r) * qpow r k) (1 - qpow r k) 1 Hb3).
    apply (qle_minus_pos (1 - qpow r k) 1).
    apply (qle_congr_r 0 (qpow r k) (1 - (1 - qpow r k))).
    - ring.
    - exact Hpos. }
  assert (Hpos : Qle 0 (qpow r k)) by (exact (qpow_nonneg k r Hr0p)).
  assert (Hs2 : Qle (Qabs (xg - x0) * qpow r k)
                    ((QofN k * (eps * (1 - r))) * qpow r k)).
  { exact (Qmult_le_compat_r (Qabs (xg - x0)) (QofN k * (eps * (1 - r)))
                             (qpow r k) Hf Hpos). }
  assert (Hs3 : Qle (qpow r k * Qabs (xg - x0))
                    ((QofN k * (eps * (1 - r))) * qpow r k)).
  { apply (qle_congr_l (Qabs (xg - x0) * qpow r k)
                       (qpow r k * Qabs (xg - x0))
                       ((QofN k * (eps * (1 - r))) * qpow r k)).
    - ring.
    - exact Hs2. }
  assert (Hs4 : Qle (qpow r k * Qabs (xg - x0))
                    ((QofN k * (1 - r) * qpow r k) * eps)).
  { apply (qle_congr_r (qpow r k * Qabs (xg - x0))
                       ((QofN k * (eps * (1 - r))) * qpow r k)
                       ((QofN k * (1 - r) * qpow r k) * eps)).
    - ring.
    - exact Hs3. }
  assert (Hs5 : Qle (qpow r k * Qabs (xg - x0)) (1 * eps)).
  { apply (Qle_trans (qpow r k * Qabs (xg - x0))
                     ((QofN k * (1 - r) * qpow r k) * eps) (1 * eps) Hs4).
    apply (Qmult_le_compat_r (QofN k * (1 - r) * qpow r k) 1 eps Hb').
    exact (Qlt_le_weak 0 eps (QltT'_to_Qlt 0 eps Heps)). }
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs (xg - qiter r x0 xg k)) (qpow r k * Qabs (xg - x0)) eps).
  - apply (qeq_imp_qle (Qabs (xg - qiter r x0 xg k)) (qpow r k * Qabs (xg - x0))).
    exact (qid_elim (Qabs (xg - qiter r x0 xg k)) (qpow r k * Qabs (xg - x0))
                    (qiter_dist_geometric_id r x0 xg k Hr1 (qltT_leT' 0 r Hr0))).
  - apply (qle_congr_r (qpow r k * Qabs (xg - x0)) (1 * eps) eps).
    + ring.
    + exact Hs5.
Qed.

Theorem qstep_step_bound :
  forall (r x0 xg eps : Q),
    QltT 0 r -> QltT r 1 -> QltT' 0 eps ->
    sigT (fun N : nat =>
            forall k : nat, (N <= k)%nat ->
              QleT' (Qabs (xg - qiter r x0 xg k)) eps).
Proof.
  intros r x0 xg eps Hr0 Hr1 Heps.
  assert (HepsT : QltT 0 eps) by (exact (QltT'_to_QltT 0 eps Heps)).
  assert (Hep : Qlt 0 eps) by (exact (QltT_to_Qlt 0 eps HepsT)).
  assert (Ht : QltT 0 (1 - r)) by (exact (qltT_pos_minus r 1 Hr1)).
  assert (Htp : Qlt 0 (1 - r)) by (exact (QltT_to_Qlt 0 (1 - r) Ht)).
  assert (Hrt : r + (1 - r) == 1) by ring.
  assert (Hr0t : QleT' 0 r) by (exact (qltT_leT' 0 r Hr0)).
  assert (Hr0p : Qle 0 r) by (exact (QleT'_to_Qle 0 r Hr0t)).
  assert (Hzp : QltT 0 (eps * (1 - r)))
    by (exact (qmult_ltT_0_compat eps (1 - r) HepsT Ht)).
  assert (Hzne : ~ (eps * (1 - r) == 0)).
  { intro Hc. exact (qltT_not_eq_zero (eps * (1 - r)) Hzp Hc). }
  destruct (Q_dec (Qabs (xg - x0)) 0) as [[Hd | Hd] | Hd].
  - (* 初距 < 0：矛盾（Qabs 非负） *)
    exfalso.
    assert (Hnn : Qle 0 (Qabs (xg - x0))) by (exact (Qabs_nonneg (xg - x0))).
    exact (Qlt_irrefl (Qabs (xg - x0))
            (Qlt_le_trans (Qabs (xg - x0)) 0 (Qabs (xg - x0)) Hd Hnn)).
  - (* 主例：0 < d0 —— 装配主界引理 *)
    exists (qstep_step_N r x0 xg eps).
    intros k Hk.
    exact (qstep_step_bound_main r x0 xg eps k Hr0 Hr1 Heps Hd Hk).
  - (* 初距为零：N := 0 恒达标 *)
    exists 0%nat. intros k _.
    assert (Hzd : Qabs (xg - qiter r x0 xg k) == 0).
    { assert (Hgeo : Qabs (xg - qiter r x0 xg k)
                       == qpow r k * Qabs (xg - x0)).
      { exact (qid_elim (Qabs (xg - qiter r x0 xg k))
                        (qpow r k * Qabs (xg - x0))
                        (qiter_dist_geometric_id r x0 xg k Hr1 Hr0t)). }
      rewrite Hd in Hgeo.
      apply (Qeq_trans (Qabs (xg - qiter r x0 xg k)) (qpow r k * 0) 0).
      - exact Hgeo.
      - ring. }
    apply (qleT'_trans (Qabs (xg - qiter r x0 xg k)) 0 eps).
    + apply (qeq_leT' (Qabs (xg - qiter r x0 xg k)) 0). exact Hzd.
    + exact (qltT_leT' 0 eps HepsT).
Qed.

(* ============================================================ *)
(* H. 假设审计（G4 留痕面）                                          *)
(* ============================================================ *)

Print Assumptions qstep_iter_geometric_bound.
Print Assumptions qiter_dist_recur.
Print Assumptions qpow_mono_dec.
Print Assumptions qstep_step_bound.
