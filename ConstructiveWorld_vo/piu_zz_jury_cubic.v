(*
  piu_zz_jury_cubic.v — third-order Schur–Jury criterion over Q; part 2a of
  the Poincaré root-limit engine build.

  使命：三阶 Schur–Jury 判据的 Q 承载件：Jury 表不等式组的显式有理形（单位圆与
  一般半径两种）、Jury 表形与 Schur 归约二次形的双向等价（判据核）、二次基底
  健全性（实根模界）、与特征多项式 piu_zz_charpoly_int 的公度接续及引擎系数
  (Ainf,Binf,Cinf) 在半径 25000 的具体判定实例；主判据定理（Jury 组 ↔ 全根模
  界）语句面以注释冻结，证明核留待后续部分。
  依赖：Stdlib QArith, Qring, Lia；本地件 piu_zz_poincare_engine（Ainf/Binf/
  Cinf、charpoly_int、piu_zz_charpoly 接口）与 piu_zz_gauss_pair（qeqT 皿·
  消解波起引）。Q 序推理全程走显式引理链
  （Qplus_lt_r/Qopp_lt_compat/Qmult_lt_r 系），无黑箱求解器依赖。
  对标：J. Schur, J. reine angew. Math. 147 (1918) 205-232；J. Jury, "A note
  on the stability of discrete systems"（三项 Jury 表）；E. I. Jury & B. D. O.
  Anderson, IEEE Trans. Automatic Control（经典三阶稳定性四条件）；S. Elaydi,
  An Introduction to Difference Equations, 3rd ed.（Schur 稳定性章）。
  构造性：语句面全部承于 Set（QltT/QltabsT/QleT 皿、qeqT 皿与 prod 组合；单元
  判定皿 QltabsT 以双侧不等式承载绝对值，全程无复根对象、无实数分析；消解波将 33 条 Prop 结论全数落 Set 载体——Qlt 系走 QltT、Qle 系走本件 QleT
  皿、Qeq 系走 qeqT、False 系走 Empty_set，qltabsT_l/qltabsT_r 两逃逸口除名
  消解）；判定实例与公度引理为可计算 Q 字面，零未证语句入模块。
  编译配方：rocq c -native-compiler no -q -Q . "" piu_zz_jury_cubic.v
*)

From Stdlib Require Import QArith Qring Lia.
Require Import piu_zz_poincare_engine.
Require Import piu_zz_gauss_pair.

(* ------------------------------------------------------------------ *)
(* Set-carried rational strict-order carriers.  |x| < y is carried      *)
(* two-sided (-x < y and x < y); no complex numbers and no real         *)
(* analysis appear anywhere in the file.                                *)
(* ------------------------------------------------------------------ *)

Inductive QltT (x y : Q) : Set :=
| qltT_intro : (x < y)%Q -> QltT x y.

Inductive QltabsT (x y : Q) : Set :=
| qltabsT_intro : (- x < y)%Q -> (x < y)%Q -> QltabsT x y.

Inductive QleT (x y : Q) : Set :=
| QleT_intro : (x <= y)%Q -> QleT x y.

(* ------------------------------------------------------------------ *)
(* Rational order-core toolkit: explicit lemma chains only.             *)
(* ------------------------------------------------------------------ *)

Lemma piu_zz_qplus_lt_r : forall x y z : Q, QltT x y -> QltT (z + x) (z + y)%Q.
Proof.
  intros x y z H. apply qltT_intro. destruct H as [H].
  apply (proj2 (Qplus_lt_r x y z)). exact H.
Qed.

Lemma piu_zz_qplus_le_r : forall x y z : Q, QleT x y -> QleT (z + x) (z + y)%Q.
Proof.
  intros x y z H. apply QleT_intro. destruct H as [H].
  apply (proj2 (Qplus_le_r x y z)). exact H.
Qed.

Lemma piu_zz_q01 : QltT 0%Q 1%Q.
Proof. apply qltT_intro. unfold Qlt. reflexivity. Qed.

Lemma piu_zz_qpos_1pc : forall c : Q, QltT (- c) 1%Q -> QltT 0%Q (1 + c)%Q.
Proof.
  intros c H.
  assert (H2 : QltT (c + - c)%Q (c + 1)%Q)
    by (apply (piu_zz_qplus_lt_r (- c) 1%Q c H)).
  apply qltT_intro.
  destruct H2 as [H2].
  rewrite Qplus_opp_r in H2.
  rewrite Qplus_comm in H2.
  exact H2.
Qed.

Lemma piu_zz_qpos_1mc : forall c : Q, QltT c 1%Q -> QltT 0%Q (1 - c)%Q.
Proof.
  intros c H.
  assert (H2 : QltT (- c + c)%Q (- c + 1)%Q)
    by (apply (piu_zz_qplus_lt_r c 1%Q (- c) H)).
  apply qltT_intro.
  destruct H2 as [H2].
  rewrite (Qplus_comm (- c) c) in H2.
  rewrite Qplus_opp_r in H2.
  rewrite (Qplus_comm (- c) 1) in H2.
  exact H2.
Qed.

Lemma piu_zz_qpos_of_qle1 : forall z : Q, QleT 1%Q z -> QltT 0%Q z.
Proof.
  intros z H. apply qltT_intro. destruct H as [H].
  apply (Qlt_le_trans 0%Q 1%Q z).
  - unfold Qlt. vm_compute. reflexivity.
  - exact H.
Qed.

Lemma piu_zz_qle_sub1 : forall z : Q, QleT 1%Q z -> QleT 0%Q (z - 1)%Q.
Proof.
  intros z H.
  assert (H2 : QleT (-1 + 1)%Q (-1 + z)%Q)
    by (apply (piu_zz_qplus_le_r 1%Q z (-1) H)).
  apply QleT_intro.
  destruct H2 as [H2].
  rewrite (Qplus_comm (-1) 1) in H2.
  rewrite Qplus_opp_r in H2.
  rewrite (Qplus_comm (-1) z) in H2.
  exact H2.
Qed.

Lemma piu_zz_qlt_sum : forall x y : Q, QleT 0%Q x -> QltT 0%Q y%Q ->
  QltT 0%Q (x + y)%Q.
Proof.
  intros x y Hx Hy.
  assert (Hxy : QltT (x + 0)%Q (x + y)%Q)
    by (apply (piu_zz_qplus_lt_r 0%Q y x Hy)).
  apply qltT_intro.
  destruct Hxy as [Hxy]. destruct Hx as [Hx].
  rewrite Qplus_0_r in Hxy.
  exact (Qle_lt_trans 0%Q x (x + y) Hx Hxy).
Qed.

Lemma piu_zz_qlt_of_pos_diff : forall x y : Q, QltT 0%Q (x - y)%Q -> QltT y x.
Proof.
  intros x y H.
  assert (H2 : QltT (y + 0)%Q (y + (x - y))%Q)
    by (apply (piu_zz_qplus_lt_r 0%Q (x - y) y H)).
  apply qltT_intro.
  destruct H2 as [H2].
  rewrite Qplus_0_r in H2.
  assert (Hrid : (y + (x - y) == x)%Q) by ring.
  rewrite Hrid in H2. exact H2.
Qed.

Lemma piu_zz_pos_diff_of_qlt : forall x y : Q, QltT y x -> QltT 0%Q (x - y)%Q.
Proof.
  intros x y H.
  assert (H2 : QltT (- y + y)%Q (- y + x)%Q)
    by (apply (piu_zz_qplus_lt_r y x (- y) H)).
  apply qltT_intro.
  destruct H2 as [H2].
  rewrite (Qplus_comm (- y) y) in H2.
  rewrite Qplus_opp_r in H2.
  rewrite (Qplus_comm (- y) x) in H2.
  exact H2.
Qed.

Lemma piu_zz_qlt_of_pos_sum : forall x y : Q, QltT 0%Q (x + y)%Q ->
  QltT (- y) x.
Proof.
  intros x y H.
  assert (H2 : QltT (- y + 0)%Q (- y + (x + y))%Q)
    by (apply (piu_zz_qplus_lt_r 0%Q (x + y) (- y) H)).
  apply qltT_intro.
  destruct H2 as [H2].
  rewrite Qplus_0_r in H2.
  assert (Hrid : (- y + (x + y) == x)%Q) by ring.
  rewrite Hrid in H2. exact H2.
Qed.

Lemma piu_zz_pos_sum_of_qlt : forall x y : Q, QltT (- y) x ->
  QltT 0%Q (x + y)%Q.
Proof.
  intros x y H.
  assert (H2 : QltT (y + - y)%Q (y + x)%Q)
    by (apply (piu_zz_qplus_lt_r (- y) x y H)).
  apply qltT_intro.
  destruct H2 as [H2].
  rewrite Qplus_opp_r in H2.
  rewrite Qplus_comm in H2.
  exact H2.
Qed.

Lemma piu_zz_qpos_pqp1 : forall p q : Q, QltT (- p) (1 + q)%Q ->
  QltT 0%Q (p + q + 1)%Q.
Proof.
  intros p q H. destruct H as [H].
  assert (Hsw : (- (1 + q) < p)%Q).
  { assert (H1 : (- (1 + q) < - (- p))%Q) by (apply Qopp_lt_compat; exact H).
    assert (Hrid : (- (- p) == p)%Q) by ring.
    rewrite Hrid in H1. exact H1. }
  assert (Hrid2 : (p + q + 1 == p + (1 + q))%Q) by ring.
  destruct (piu_zz_pos_sum_of_qlt p (1 + q)%Q (qltT_intro _ _ Hsw)) as [Ht].
  rewrite <- Hrid2 in Ht.
  apply qltT_intro. exact Ht.
Qed.

Lemma piu_zz_qpos_zmq : forall z q : Q, QleT 1%Q z -> QltT q 1%Q ->
  QltT 0%Q (z - q)%Q.
Proof.
  intros z q H1 H2.
  assert (Hz : QltT 0%Q (z - 1 + (1 - q))%Q).
  { apply piu_zz_qlt_sum.
    - apply piu_zz_qle_sub1; exact H1.
    - apply piu_zz_qpos_1mc; exact H2. }
  apply qltT_intro.
  destruct Hz as [Hz].
  assert (Hrid : (z - 1 + (1 - q) == z - q)%Q) by ring.
  rewrite Hrid in Hz. exact Hz.
Qed.

Lemma piu_zz_qle_of_qlt0 : forall x : Q, QltT 0%Q x -> QleT 0%Q x.
Proof. intros x H. apply QleT_intro. destruct H as [H].
  apply (Qlt_le_weak 0%Q x). exact H. Qed.

Lemma piu_zz_qlt_neg_swap1 : forall z : Q, QltT (-1) z -> QltT (- z) 1%Q.
Proof.
  intros z H.
  assert (H2 : QltT (- z)%Q (- (-1))%Q).
  { apply qltT_intro. apply Qopp_lt_compat. destruct H as [H]. exact H. }
  apply qltT_intro.
  destruct H2 as [H2].
  rewrite (Qopp_involutive 1%Q) in H2. exact H2.
Qed.

Lemma piu_zz_qle_neg_swap1 : forall z : Q, QleT z (-1)%Q -> QleT 1%Q (- z).
Proof.
  intros z H.
  apply QleT_intro.
  rewrite <- (Qopp_involutive 1%Q).
  apply Qopp_le_compat. destruct H as [H]. exact H.
Qed.

(* Case split fuel: the 9.1 toolface has no Qle_lt_dec; Qle_bool plus
   Qle_bool_iff / Qnot_le_lt carries the two-sided split. *)
Lemma piu_zz_qlt_of_qle_bool_false : forall x y : Q,
  Qle_bool x y = false -> QltT y x.
Proof.
  intros x y Hb.
  apply qltT_intro.
  apply Qnot_le_lt.
  intros Hle.
  assert (Ht : Qle_bool x y = true) by (apply Qle_bool_iff; exact Hle).
  rewrite Hb in Ht. discriminate Ht.
Qed.

Lemma piu_zz_qlt00_false : QltT 0%Q 0%Q -> Empty_set.
Proof. intros H. destruct H as [H]. unfold Qlt in H. vm_compute in H.
  discriminate H. Qed.

(* Multiplicative transfer (positive scalars), via Qmult_lt_r. *)
Lemma piu_zz_qpos_mul_r : forall x k : Q, QltT 0%Q k -> QltT 0%Q x ->
  QltT 0%Q (x * k)%Q.
Proof. intros x k Hk Hx. apply qltT_intro. destruct Hk as [Hk].
  destruct Hx as [Hx]. apply Qmult_lt_0_compat; assumption. Qed.

Lemma piu_zz_qpos_mul_l : forall x k : Q, QltT 0%Q k -> QltT 0%Q x ->
  QltT 0%Q (k * x)%Q.
Proof. intros x k Hk Hx. apply qltT_intro. destruct Hk as [Hk].
  destruct Hx as [Hx]. apply Qmult_lt_0_compat; assumption. Qed.

Lemma piu_zz_qpos_of_mul_r : forall x k : Q, QltT 0%Q k ->
  QltT 0%Q (x * k)%Q -> QltT 0%Q x.
Proof.
  intros x k Hk H. apply qltT_intro.
  destruct Hk as [Hk]. destruct H as [H].
  apply (proj1 (Qmult_lt_r 0%Q x k Hk)).
  rewrite Qmult_0_l. exact H.
Qed.

Lemma piu_zz_qpos_of_mul_l : forall x k : Q, QltT 0%Q k ->
  QltT 0%Q (k * x)%Q -> QltT 0%Q x.
Proof.
  intros x k Hk H.
  apply qltT_intro.
  destruct Hk as [Hk]. destruct H as [H].
  apply (proj1 (Qmult_lt_r 0%Q x k Hk)).
  rewrite (Qmult_0_l k). rewrite <- (Qmult_comm k x). exact H.
Qed.

(* Sixth-power positivity, used by the radius-r scale transfers. *)
Lemma piu_zz_qpos_r6 : forall r : Q, QltT 0%Q r ->
  QltT 0%Q (r*r*r*r*r*r)%Q.
Proof.
  intros r Hr.
  apply qltT_intro.
  destruct Hr as [Hr].
  assert (Hr2 : (0 < r*r)%Q) by (apply (Qmult_lt_0_compat r r); assumption).
  assert (Hr3 : (0 < r*r*r)%Q)
    by (apply (Qmult_lt_0_compat (r*r) r); assumption).
  assert (Hr4 : (0 < r*r*r*r)%Q)
    by (apply (Qmult_lt_0_compat (r*r*r) r); assumption).
  assert (Hr5 : (0 < r*r*r*r*r)%Q)
    by (apply (Qmult_lt_0_compat (r*r*r*r) r); assumption).
  apply (Qmult_lt_0_compat (r*r*r*r*r) r); assumption.
Qed.

(* Rational algebra identities used as rewrite rules. *)
Lemma piu_zz_jury_diff_sq : forall c : Q,
  qeqT ((1 - c) * (1 + c))%Q (1 - c*c)%Q.
Proof. intros c. apply qeqT_intro. ring. Qed.

Lemma piu_zz_jury_diff_sq_gen : forall c r : Q,
  qeqT ((r*r*r - c) * (r*r*r + c))%Q (r*r*r*r*r*r - c*c)%Q.
Proof. intros c r. apply qeqT_intro. ring. Qed.

Lemma piu_zz_jury_fact_pos : forall a b c : Q,
  qeqT (1 - c*c + (b - a*c) - (a - b*c))%Q ((1 + c)*(1 - a + b - c))%Q.
Proof. intros a b c. apply qeqT_intro. ring. Qed.

Lemma piu_zz_jury_fact_neg : forall a b c : Q,
  qeqT (1 - c*c + (b - a*c) + (a - b*c))%Q ((1 - c)*(1 + a + b + c))%Q.
Proof. intros a b c. apply qeqT_intro. ring. Qed.

Lemma piu_zz_quad_factor : forall p q z : Q,
  qeqT ((z - 1) * (z - q) + z * (p + q + 1))%Q (z*z + p*z + q)%Q.
Proof. intros p q z. apply qeqT_intro. ring. Qed.

(* ------------------------------------------------------------------ *)
(* Born piece 1a: the Jury table in explicit rational form at unit      *)
(* radius.  For the monic cubic f(lam) = lam^3 + a*lam^2 + b*lam + c    *)
(* the four Schur-Jury conditions read:                                 *)
(*   J1 |c| < 1,  J2 1 + a + b + c > 0,  J3 1 - a + b - c > 0,          *)
(*   J4 |b - a*c| < 1 - c*c.                                            *)
(* The table-reduction denominator 1 - c*c is nonzero as a consequence  *)
(* of J1 (remark below), so the table step needs no extra premise.      *)
(* ------------------------------------------------------------------ *)

Definition piu_zz_jury1_conds (a b c : Q) : Set :=
  QltabsT c 1%Q
  * (QltT 0%Q (1 + a + b + c)%Q
  * (QltT 0%Q (1 - a + b - c)%Q
  * QltabsT (b - a*c)%Q (1 - c*c)%Q)).

Remark piu_zz_jury1_tab_nonzero : forall c : Q,
  (- c < 1)%Q -> (c < 1)%Q -> (1 - c*c <> 0)%Q.
Proof.
  intros c Hn Hp.
  assert (H1 : (0 < 1 + c)%Q)
    by (destruct (piu_zz_qpos_1pc c (qltT_intro _ _ Hn)) as [Ht]; exact Ht).
  assert (H2 : (0 < 1 - c)%Q)
    by (destruct (piu_zz_qpos_1mc c (qltT_intro _ _ Hp)) as [Ht]; exact Ht).
  assert (H3 : (0 < (1 - c) * (1 + c))%Q)
    by (apply Qmult_lt_0_compat; assumption).
  pose proof (match piu_zz_jury_diff_sq c as _ in qeqT a b
              return (a == b)%Q with
              | qeqT_intro _ _ e => e
              end) as Hd.
  rewrite Hd in H3.
  intros Heq. rewrite Heq in H3. clear Heq.
  destruct (piu_zz_qlt00_false (qltT_intro _ _ H3)).
Qed.

(* ------------------------------------------------------------------ *)
(* Born piece 1b: the Jury table in explicit rational form at radius r. *)
(* Scaling lam = r*mu turns the unit conditions into purely polynomial  *)
(* inequalities (multiplied through by the positive powers r^3, r^6):   *)
(*   J1 |c| < r^3,                                                      *)
(*   J2 r^3 + a*r^2 + b*r + c > 0,                                      *)
(*   J3 r^3 - a*r^2 + b*r - c > 0,                                      *)
(*   J4 r^6 - c*c - r^2*(b*r^2 - a*c) > 0  and                          *)
(*      r^6 - c*c + r^2*(b*r^2 - a*c) > 0                               *)
(* (J4 is r^2 * |b*r^2 - a*c| < r^6 - c^2 carried two-sided).           *)
(* ------------------------------------------------------------------ *)

Definition piu_zz_jury_conds (a b c r : Q) : Set :=
  QltabsT c (r*r*r)%Q
  * (QltT 0%Q (r*r*r + a*(r*r) + b*r + c)%Q
  * (QltT 0%Q (r*r*r - a*(r*r) + b*r - c)%Q
  * (QltT 0%Q (r*r*r*r*r*r - c*c - r*r*(b*(r*r) - a*c))%Q
  * QltT 0%Q (r*r*r*r*r*r - c*c + r*r*(b*(r*r) - a*c))%Q))).

Remark piu_zz_jury_tab_nonzero_gen : forall c r : Q,
  (- c < r*r*r)%Q -> (c < r*r*r)%Q -> (r*r*r*r*r*r - c*c <> 0)%Q.
Proof.
  intros c r Hn Hp.
  assert (H1 : (0 < r*r*r + c)%Q)
    by (destruct (piu_zz_pos_sum_of_qlt (r*r*r)%Q c%Q
                    (qltT_intro _ _ Hn)) as [Ht]; exact Ht).
  assert (H2 : (0 < r*r*r - c)%Q)
    by (destruct (piu_zz_pos_diff_of_qlt (r*r*r)%Q c%Q
                    (qltT_intro _ _ Hp)) as [Ht]; exact Ht).
  assert (H3 : (0 < (r*r*r - c) * (r*r*r + c))%Q)
    by (apply Qmult_lt_0_compat; assumption).
  pose proof (match piu_zz_jury_diff_sq_gen c r as _ in qeqT a b
              return (a == b)%Q with
              | qeqT_intro _ _ e => e
              end) as Hd.
  rewrite Hd in H3.
  intros Heq. rewrite Heq in H3. clear Heq.
  destruct (piu_zz_qlt00_false (qltT_intro _ _ H3)).
Qed.

(* Scale transfer, engine direction: conditions at radius r in the      *)
(* coefficients (a,b,c) give the unit-radius conditions for the scaled  *)
(* triple (a/r, b/r^2, c/r^3), expressed through scaling equations to   *)
(* avoid rational division in the statement.                            *)
Lemma piu_zz_jury_scale_to_unit :
  forall (a a' b b' c c' r : Q), (0 < r)%Q ->
  (a == a' * r)%Q -> (b == b' * (r*r))%Q -> (c == c' * (r*r*r))%Q ->
  piu_zz_jury_conds a b c r -> piu_zz_jury1_conds a' b' c'.
Proof.
  intros a a' b b' c c' r Hr Ha Hb Hc
    [HJ1 [HJ2 [HJ3 [HJ4an HJ4bp]]]].
  assert (Hr3 : QltT 0%Q (r*r*r)%Q).
  { apply qltT_intro. apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat; exact Hr.
    - exact Hr. }
  assert (Hr6 : QltT 0%Q (r*r*r*r*r*r)%Q)
    by (apply piu_zz_qpos_r6; apply qltT_intro; exact Hr).
  destruct HJ1 as [H1n H1p]. destruct HJ2 as [H2]. destruct HJ3 as [H3].
  destruct HJ4an as [H4an]. destruct HJ4bp as [H4bp].
  split.
  - apply qltabsT_intro.
    + assert (Hfin : QltT 0%Q ((r*r*r) * (1 + c'))%Q).
      { assert (Hpos0 : (0 < r*r*r - - c)%Q)
          by (destruct (piu_zz_pos_diff_of_qlt (r*r*r)%Q (- c)%Q
                 (qltT_intro _ _ H1n)) as [Ht]; exact Ht).
        assert (Hrid : (r*r*r - - c == r*r*r + c)%Q) by ring.
        rewrite Hrid in Hpos0.
        assert (Hq : (r*r*r + c == (r*r*r) * (1 + c'))%Q)
          by (rewrite Hc; ring).
        rewrite Hq in Hpos0.
        apply qltT_intro. exact Hpos0. }
      assert (Hpos : QltT 0%Q (1 + c')%Q)
        by (apply (piu_zz_qpos_of_mul_l (1 + c') (r*r*r) Hr3 Hfin)).
      assert (Ht : QltT (- c') 1%Q)
        by (apply piu_zz_qlt_of_pos_sum; exact Hpos).
      destruct Ht as [Ht]. exact Ht.
    + assert (Hfin : QltT 0%Q ((r*r*r) * (1 - c'))%Q).
      { assert (Hpos0 : (0 < r*r*r - c)%Q)
          by (destruct (piu_zz_pos_diff_of_qlt (r*r*r)%Q c%Q
                 (qltT_intro _ _ H1p)) as [Ht]; exact Ht).
        assert (Hq : (r*r*r - c == (r*r*r) * (1 - c'))%Q)
          by (rewrite Hc; ring).
        rewrite Hq in Hpos0.
        apply qltT_intro. exact Hpos0. }
      assert (Hpos : QltT 0%Q (1 - c')%Q)
        by (apply (piu_zz_qpos_of_mul_l (1 - c') (r*r*r) Hr3 Hfin)).
      assert (Ht : QltT c' 1%Q)
        by (apply piu_zz_qlt_of_pos_diff; exact Hpos).
      destruct Ht as [Ht]. exact Ht.
  - split.
    + assert (Hfin : QltT 0%Q ((r*r*r) * (1 + a' + b' + c'))%Q).
      { apply qltT_intro.
        assert (Hq : ((r*r*r) * (1 + a' + b' + c')
                       == r*r*r + a*(r*r) + b*r + c)%Q)
          by (rewrite Ha, Hb, Hc; ring).
        rewrite Hq. exact H2. }
      apply (piu_zz_qpos_of_mul_l (1 + a' + b' + c') (r*r*r) Hr3 Hfin).
    + split.
      * assert (Hfin : QltT 0%Q ((r*r*r) * (1 - a' + b' - c'))%Q).
        { apply qltT_intro.
          assert (Hq : ((r*r*r) * (1 - a' + b' - c')
                         == r*r*r - a*(r*r) + b*r - c)%Q)
            by (rewrite Ha, Hb, Hc; ring).
          rewrite Hq. exact H3. }
        apply (piu_zz_qpos_of_mul_l (1 - a' + b' - c') (r*r*r) Hr3 Hfin).
      * split.
        -- assert (Hfin : QltT 0%Q ((r*r*r*r*r*r)
                             * (1 - c'*c' + (b' - a'*c')))%Q).
           { apply qltT_intro.
             assert (Hq : ((r*r*r*r*r*r) * (1 - c'*c' + (b' - a'*c'))
                            == r*r*r*r*r*r - c*c
                               + r*r*(b*(r*r) - a*c))%Q)
               by (rewrite Ha, Hb, Hc; ring).
             rewrite Hq. exact H4bp. }
           assert (Hpos : QltT 0%Q (1 - c'*c' + (b' - a'*c'))%Q)
             by (apply (piu_zz_qpos_of_mul_l (1 - c'*c' + (b' - a'*c'))
                        (r*r*r*r*r*r) Hr6 Hfin)).
           assert (Ht : QltT (- (b' - a'*c')) (1 - c'*c')%Q)
             by (apply piu_zz_qlt_of_pos_sum; exact Hpos).
           destruct Ht as [Ht]. exact Ht.
        -- assert (Hfin : QltT 0%Q ((r*r*r*r*r*r)
                             * (1 - c'*c' - (b' - a'*c')))%Q).
           { apply qltT_intro.
             assert (Hq : ((r*r*r*r*r*r) * (1 - c'*c' - (b' - a'*c'))
                            == r*r*r*r*r*r - c*c
                               - r*r*(b*(r*r) - a*c))%Q)
               by (rewrite Ha, Hb, Hc; ring).
             rewrite Hq. exact H4an. }
           assert (Hpos : QltT 0%Q (1 - c'*c' - (b' - a'*c'))%Q)
             by (apply (piu_zz_qpos_of_mul_l (1 - c'*c' - (b' - a'*c'))
                        (r*r*r*r*r*r) Hr6 Hfin)).
           assert (Ht : QltT (b' - a'*c') (1 - c'*c')%Q)
             by (apply piu_zz_qlt_of_pos_diff; exact Hpos).
           destruct Ht as [Ht]. exact Ht.
Qed.

(* Scale transfer, inverse direction: unit-radius conditions for a      *)
(* scaled triple give the radius-r conditions for the unscaled          *)
(* coefficients.                                                        *)
Lemma piu_zz_jury_scale_from_unit :
  forall (a a' b b' c c' r : Q), (0 < r)%Q ->
  (a == a' * r)%Q -> (b == b' * (r*r))%Q -> (c == c' * (r*r*r))%Q ->
  piu_zz_jury1_conds a' b' c' -> piu_zz_jury_conds a b c r.
Proof.
  intros a a' b b' c c' r Hr Ha Hb Hc
    [HJ1 [HJ2 [HJ3 HJ4]]].
  assert (Hr2 : (0 < r*r)%Q) by (apply Qmult_lt_0_compat; assumption).
  assert (Hr3 : QltT 0%Q (r*r*r)%Q)
    by (apply qltT_intro; apply Qmult_lt_0_compat; assumption).
  assert (Hr6 : QltT 0%Q (r*r*r*r*r*r)%Q)
    by (apply piu_zz_qpos_r6; apply qltT_intro; exact Hr).
  destruct HJ1 as [H1n H1p]. destruct HJ2 as [H2]. destruct HJ3 as [H3].
  destruct HJ4 as [H4n H4p].
  split.
  - apply qltabsT_intro.
    + assert (Hfin : QltT 0%Q ((1 + c') * (r*r*r))%Q).
      { apply qltT_intro.
        apply piu_zz_qpos_mul_r.
        - exact Hr3.
        - apply piu_zz_qpos_1pc. apply qltT_intro. exact H1n. }
      assert (HfinP : (0 < (1 + c') * (r*r*r))%Q)
        by (destruct Hfin as [Ht]; exact Ht).
      assert (Hq : ((1 + c') * (r*r*r) == r*r*r + c)%Q)
        by (rewrite Hc; ring).
      rewrite Hq in HfinP.
      assert (Ht : QltT (- c) (r*r*r)%Q)
        by (apply piu_zz_qlt_of_pos_sum; apply qltT_intro; exact HfinP).
      destruct Ht as [Ht]. exact Ht.
    + assert (Hfin : QltT 0%Q ((r*r*r) * (1 - c'))%Q).
      { apply qltT_intro.
        apply piu_zz_qpos_mul_l.
        - exact Hr3.
        - apply piu_zz_qpos_1mc. apply qltT_intro. exact H1p. }
      assert (HfinP : (0 < (r*r*r) * (1 - c'))%Q)
        by (destruct Hfin as [Ht]; exact Ht).
      assert (Hq : ((r*r*r) * (1 - c') == r*r*r - c)%Q)
        by (rewrite Hc; ring).
      rewrite Hq in HfinP.
      assert (Ht : QltT c (r*r*r)%Q)
        by (apply piu_zz_qlt_of_pos_diff; apply qltT_intro; exact HfinP).
      destruct Ht as [Ht]. exact Ht.
  - split.
    + apply qltT_intro.
      assert (Hq : (r*r*r + a*(r*r) + b*r + c
                    == (r*r*r) * (1 + a' + b' + c'))%Q)
        by (rewrite Ha, Hb, Hc; ring).
      rewrite Hq.
      apply piu_zz_qpos_mul_r.
      * apply qltT_intro. exact H2.
      * exact Hr3.
    + split.
      * apply qltT_intro.
        assert (Hq : (r*r*r - a*(r*r) + b*r - c
                      == (r*r*r) * (1 - a' + b' - c'))%Q)
          by (rewrite Ha, Hb, Hc; ring).
        rewrite Hq.
        apply piu_zz_qpos_mul_r.
        -- apply qltT_intro. exact H3.
        -- exact Hr3.
      * split.
        -- apply qltT_intro.
           assert (Hq : (r*r*r*r*r*r - c*c - r*r*(b*(r*r) - a*c)
                          == (r*r*r*r*r*r)
                             * (1 - c'*c' - (b' - a'*c')))%Q)
             by (rewrite Ha, Hb, Hc; ring).
           rewrite Hq.
           apply piu_zz_qpos_mul_l.
           ++ exact Hr6.
           ++ apply piu_zz_pos_diff_of_qlt. apply qltT_intro. exact H4p.
        -- apply qltT_intro.
           assert (Hq : (r*r*r*r*r*r - c*c + r*r*(b*(r*r) - a*c)
                          == (r*r*r*r*r*r)
                             * (1 - c'*c' + (b' - a'*c')))%Q)
             by (rewrite Ha, Hb, Hc; ring).
           rewrite Hq.
           apply piu_zz_qpos_mul_l.
           ++ exact Hr6.
           ++ apply piu_zz_pos_sum_of_qlt. apply qltT_intro. exact H4n.
Qed.

(* ------------------------------------------------------------------ *)
(* Born piece 2: the Schur-reduction core at unit radius (form-A        *)
(* algebraic kernel).  With k = c the Schur reduction of                *)
(* f(lam) = lam^3 + a*lam^2 + b*lam + c produces the quadratic          *)
(*   lam^2 + p*lam + q,  p = (a - b*c)/(1 - c*c),                       *)
(*                      q = (b - a*c)/(1 - c*c),                        *)
(* and the unit-disk condition for f is equivalent to |c| < 1 together  *)
(* with the quadratic conditions |q| < 1 and |p| < 1 + q.  Clearing the *)
(* positive denominator 1 - c*c carries both reduced conditions         *)
(* two-sided, giving piu_zz_schur_red below; the equivalence with the   *)
(* Jury table is pure rational algebra, the whole content being the     *)
(* two factorizations piu_zz_jury_fact_pos / piu_zz_jury_fact_neg.      *)
(* ------------------------------------------------------------------ *)

Definition piu_zz_schur_red (a b c : Q) : Set :=
  QltabsT c 1%Q
  * (QltabsT (b - a*c)%Q (1 - c*c)%Q
  * QltabsT (a - b*c)%Q (1 - c*c + (b - a*c))%Q).

Lemma piu_zz_jury1_to_schur_red : forall a b c : Q,
  piu_zz_jury1_conds a b c -> piu_zz_schur_red a b c.
Proof.
  intros a b c [HJ1 [HJ2 [HJ3 [HJ4n HJ4p]]]].
  destruct HJ2 as [H2]. destruct HJ3 as [H3].
  destruct HJ1 as [H1n H1p].
  split.
  - apply qltabsT_intro; [ exact H1n | exact H1p ].
  - split.
    + split; [ exact HJ4n | exact HJ4p ].
    + apply qltabsT_intro.
      * assert (Hd : (0 < (1 - c)*(1 + a + b + c))%Q).
        { apply Qmult_lt_0_compat.
          - destruct (piu_zz_qpos_1mc c (qltT_intro _ _ H1p)) as [Ht].
            exact Ht.
          - exact H2. }
        pose proof (match piu_zz_jury_fact_neg a b c as _ in qeqT a b
                    return (a == b)%Q with
                    | qeqT_intro _ _ e => e
                    end) as Hfn.
        rewrite <- Hfn in Hd.
        assert (Ht : QltT (- (a - b*c)) (1 - c*c + (b - a*c))%Q)
          by (apply piu_zz_qlt_of_pos_sum; apply qltT_intro; exact Hd).
        destruct Ht as [Ht]. exact Ht.
      * assert (Hd : (0 < (1 + c)*(1 - a + b - c))%Q).
        { apply Qmult_lt_0_compat.
          - destruct (piu_zz_qpos_1pc c (qltT_intro _ _ H1n)) as [Ht].
            exact Ht.
          - exact H3. }
        pose proof (match piu_zz_jury_fact_pos a b c as _ in qeqT a b
                    return (a == b)%Q with
                    | qeqT_intro _ _ e => e
                    end) as Hfp.
        rewrite <- Hfp in Hd.
        assert (Ht : QltT (a - b*c) (1 - c*c + (b - a*c))%Q)
          by (apply piu_zz_qlt_of_pos_diff; apply qltT_intro; exact Hd).
        destruct Ht as [Ht]. exact Ht.
Qed.

Lemma piu_zz_schur_red_to_jury1 : forall a b c : Q,
  piu_zz_schur_red a b c -> piu_zz_jury1_conds a b c.
Proof.
  intros a b c [HS1 [HS2 [HS3n HS3p]]].
  split.
  - exact HS1.
  - split.
    + apply qltT_intro.
      assert (Hs : (0 < (1 - c*c + (b - a*c)) - (- (a - b*c)))%Q)
        by (destruct (piu_zz_pos_diff_of_qlt (1 - c*c + (b - a*c))%Q
                        (- (a - b*c))%Q (qltT_intro _ _ HS3n)) as [Ht];
            exact Ht).
      assert (Hrid : ((1 - c*c + (b - a*c)) - (- (a - b*c))
                       == 1 - c*c + (b - a*c) + (a - b*c))%Q) by ring.
      rewrite Hrid in Hs.
      pose proof (match piu_zz_jury_fact_neg a b c as _ in qeqT a b
                  return (a == b)%Q with
                  | qeqT_intro _ _ e => e
                  end) as Hfn.
      rewrite Hfn in Hs.
      apply (piu_zz_qpos_of_mul_l (1 + a + b + c) (1 - c)).
      * destruct HS1 as [H1n H1p]. apply piu_zz_qpos_1mc.
        apply qltT_intro. exact H1p.
      * apply qltT_intro. exact Hs.
    + split.
      * apply qltT_intro.
        assert (Hs : (0 < (1 - c*c + (b - a*c)) - (a - b*c))%Q)
          by (destruct (piu_zz_pos_diff_of_qlt (1 - c*c + (b - a*c))%Q
                          (a - b*c)%Q (qltT_intro _ _ HS3p)) as [Ht];
              exact Ht).
        pose proof (match piu_zz_jury_fact_pos a b c as _ in qeqT a b
                    return (a == b)%Q with
                    | qeqT_intro _ _ e => e
                    end) as Hfp.
        rewrite Hfp in Hs.
        apply (piu_zz_qpos_of_mul_l (1 - a + b - c) (1 + c)).
        -- destruct HS1 as [H1n H1p]. apply piu_zz_qpos_1pc.
           apply qltT_intro. exact H1n.
        -- apply qltT_intro. exact Hs.
      * exact HS2.
Qed.

(* ------------------------------------------------------------------ *)
(* Born piece 2b: quadratic base case of the Schur chain, real-root     *)
(* face.  If |q| < 1 and |p| < 1 + q then every rational (indeed every  *)
(* real) root of lam^2 + p*lam + q lies strictly inside the unit disk.  *)
(* The certificate is the factorization piu_zz_quad_factor,             *)
(*   lam^2 + p*lam + q = (lam - 1)*(lam - q) + lam*(p + q + 1),         *)
(* whose two summands are nonnegative resp. positive once lam >= 1.     *)
(* ------------------------------------------------------------------ *)

Lemma piu_zz_quad_no_root_ge1 : forall p q z : Q,
  QltabsT q 1%Q -> QltabsT p (1 + q)%Q -> QleT 1%Q z ->
  qeqT (z*z + p*z + q)%Q 0%Q -> Empty_set.
Proof.
  intros p q z Hq Hp Hge Heq0.
  destruct Hq as [Hqn Hqp]. destruct Hp as [Hpn Hpp].
  assert (Hz : QltT 0%Q z) by (apply piu_zz_qpos_of_qle1; exact Hge).
  assert (Hzq : QltT 0%Q (z - q)%Q).
  { apply piu_zz_qpos_zmq.
    - exact Hge.
    - apply qltT_intro. exact Hqp. }
  assert (HA : (0 <= (z - 1) * (z - q))%Q).
  { apply Qmult_le_0_compat.
    - destruct (piu_zz_qle_sub1 z Hge) as [Ht]. exact Ht.
    - destruct (piu_zz_qle_of_qlt0 (z - q)%Q Hzq) as [Ht]. exact Ht. }
  assert (HB : QltT 0%Q (z * (p + q + 1))%Q).
  { apply piu_zz_qpos_mul_l.
    - exact Hz.
    - apply piu_zz_qpos_pqp1. apply qltT_intro. exact Hpn. }
  assert (HposC : QltT 0%Q ((z - 1) * (z - q) + z * (p + q + 1))%Q).
  { apply piu_zz_qlt_sum.
    - apply QleT_intro. exact HA.
    - exact HB. }
  assert (Hpos : (0 < (z - 1) * (z - q) + z * (p + q + 1))%Q)
    by (destruct HposC as [Ht]; exact Ht).
  pose proof (match piu_zz_quad_factor p q z as _ in qeqT a b
              return (a == b)%Q with
              | qeqT_intro _ _ e => e
              end) as Hfac.
  rewrite Hfac in Hpos.
  pose proof (match Heq0 as _ in qeqT a b return (a == b)%Q with
              | qeqT_intro _ _ e => e
              end) as Heq.
  rewrite Heq in Hpos.
  exact (piu_zz_qlt00_false (qltT_intro _ _ Hpos)).
Qed.

Lemma piu_zz_quad_schur_sound : forall p q z : Q,
  QltabsT q 1%Q -> QltabsT p (1 + q)%Q ->
  (z*z + p*z + q == 0)%Q -> QltabsT z 1%Q.
Proof.
  intros p q z Hq Hp Heq.
  destruct Hp as [Hpn Hpp].
  apply qltabsT_intro.
  - destruct (Qle_bool z (-1)%Q) eqn:Hb.
    + exfalso.
      apply Qle_bool_iff in Hb.
      assert (Hgez : QleT 1%Q (- z)%Q)
        by (apply piu_zz_qle_neg_swap1; apply QleT_intro; exact Hb).
      assert (Halt : QltabsT (- p) (1 + q)%Q).
      { apply qltabsT_intro.
        - rewrite (Qopp_involutive p). exact Hpp.
        - exact Hpn. }
      assert (Heqz : qeqT ((- z) * (- z) + (- p) * (- z) + q)%Q 0%Q).
      { apply qeqT_intro.
        assert (Hq3 : ((- z) * (- z) + (- p) * (- z) + q
                        == z*z + p*z + q)%Q) by ring.
        rewrite Hq3. exact Heq. }
      destruct (piu_zz_quad_no_root_ge1 (- p) q (- z)%Q Hq Halt Hgez Heqz).
    + apply piu_zz_qlt_neg_swap1.
      apply piu_zz_qlt_of_qle_bool_false. exact Hb.
  - destruct (Qle_bool 1%Q z) eqn:Hb.
    + exfalso.
      apply Qle_bool_iff in Hb.
      assert (Heqz : qeqT (z*z + p*z + q)%Q 0%Q)
        by (apply qeqT_intro; exact Heq).
      destruct (piu_zz_quad_no_root_ge1 p q z Hq
                  (qltabsT_intro p (1 + q)%Q Hpn Hpp)
                  (QleT_intro 1%Q z%Q Hb) Heqz).
    + apply piu_zz_qlt_of_qle_bool_false. exact Hb.
Qed.

(* ------------------------------------------------------------------ *)
(* Born piece 3: the wiring face to the engine characteristic           *)
(* polynomial.  The generic Jury cubic at the engine coefficient triple *)
(* is, after clearing the denominator 108, exactly the integer form     *)
(* piu_zz_charpoly_int of piu_zz_poincare_engine; and the triple        *)
(* satisfies the radius-r Jury table at r = 25000, which brackets the   *)
(* dominant root from above with an explicit rational margin (the       *)
(* numerical reading:  |Cinf| = 2048/108 ~ 18.96 << r^3,                *)
(* f(25000) ~ 1.97e12 > 0,  -f(-25000) > 0,  J4 margin ~ 2.4e26).       *)
(* ------------------------------------------------------------------ *)

Definition piu_zz_jury_poly (a b c lam : Q) : Q :=
  (lam*lam*lam + a*(lam*lam) + b*lam + c)%Q.

Definition piu_zz_jury_engine_poly (lam : Q) : Q :=
  piu_zz_jury_poly piu_zz_Ainf piu_zz_Binf piu_zz_Cinf lam.

Lemma piu_zz_jury_engine_poly_commuted : forall lam : Q,
  qeqT (108 * piu_zz_jury_engine_poly lam)%Q (piu_zz_charpoly_int lam).
Proof.
  intros lam.
  apply qeqT_intro.
  unfold piu_zz_jury_engine_poly, piu_zz_jury_poly,
    piu_zz_Ainf, piu_zz_Binf, piu_zz_Cinf, piu_zz_charpoly_int.
  ring.
Qed.

Definition piu_zz_jury_engine_radius : Q := 25000%Q.

Lemma piu_zz_jury_instance_engine :
  piu_zz_jury_conds piu_zz_Ainf piu_zz_Binf piu_zz_Cinf
    piu_zz_jury_engine_radius.
Proof.
  unfold piu_zz_jury_conds, piu_zz_Ainf, piu_zz_Binf, piu_zz_Cinf,
    piu_zz_jury_engine_radius.
  repeat split; unfold Qlt; vm_compute; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Decision data face: the five comparison operands of the Jury table   *)
(* as one computable rational tuple, together with the engine instance. *)
(* ------------------------------------------------------------------ *)

Definition piu_zz_jury_qty (a b c r : Q) : Q * Q * Q * Q * Q :=
  (c,
   r*r*r + a*(r*r) + b*r + c,
   r*r*r - a*(r*r) + b*r - c,
   r*r*r*r*r*r - c*c - r*r*(b*(r*r) - a*c),
   r*r*r*r*r*r - c*c + r*r*(b*(r*r) - a*c))%Q.

Definition piu_zz_jury_witness : Q * Q * Q * Q * Q :=
  piu_zz_jury_qty piu_zz_Ainf piu_zz_Binf piu_zz_Cinf
    piu_zz_jury_engine_radius.

(* ================================================================== *)
(* FROZEN STATEMENT — piu_zz_jury_cubic_criterion                       *)
(* (proof core reserved for later parts; frozen here as a comment so    *)
(* that this compiled module carries no unproved claim)                 *)
(*                                                                      *)
(*   The root side of the criterion, carried purely in rational         *)
(*   coefficients (no complex root objects), is assembled in two        *)
(*   stages:                                                            *)
(*   (i)  circle separation: the resultant of f(X) = X^3 + a*X^2 +      *)
(*        b*X + c and h(X) = c*X^3 + b*r^2*X^2 + a*r^4*X + r^6 is       *)
(*        nonzero — a rational decidable statement equivalent to f      *)
(*        having no root on the circle |z| = r;                         *)
(*   (ii) the Schur count: the sign chain of the recursive Schur        *)
(*        reduction (born here at the first step: piu_zz_jury1_conds    *)
(*        vs piu_zz_schur_red, plus the quadratic base case             *)
(*        piu_zz_quad_schur_sound) deciding that all three roots lie    *)
(*        strictly inside the circle.                                   *)
(*                                                                      *)
(*   Theorem piu_zz_jury_cubic_criterion :                              *)
(*     forall a b c r : Q, (0 < r)%Q ->                                 *)
(*     piu_zz_jury_conds a b c r <->                                    *)
(*       (circle separation (i)) /\ (Schur count (ii)).                 *)
(*                                                                      *)
(*   Sufficiency direction status: steps (i)+(ii) reduce the deep part  *)
(*   to the Schur-Cohn induction over the complex-root pairing; the     *)
(*   rational-root face alone is strictly weaker (the polynomial        *)
(*   X^3 - 2 has no rational root yet violates J1), so no one-direction *)
(*   rational-root reading of the master statement is sound.            *)
(*                                                                      *)
(* Sub-lemma checklist (statement shape / difficulty / proof outlook):  *)
(*  L2a-1 scale transfer both directions — Proved above                   *)
(*        (piu_zz_jury_scale_to_unit / _from_unit).                     *)
(*  L2a-2 unit Jury table vs Schur-reduced quadratic conditions, both   *)
(*        directions (the reduction-step algebra) — Proved above          *)
(*        (piu_zz_jury1_to_schur_red / piu_zz_schur_red_to_jury1).      *)
(*  L2a-3 quadratic base case, real-root soundness — Proved above         *)
(*        (piu_zz_quad_no_root_ge1 / piu_zz_quad_schur_sound).          *)
(*  L2a-4 table-denominator nonvanishing from J1 — Proved above           *)
(*        (piu_zz_jury1_tab_nonzero / piu_zz_jury_tab_nonzero_gen).     *)
(*  L2a-5 wiring: engine poly commutation + concrete instance at        *)
(*        r = 25000 — Proved above (piu_zz_jury_engine_poly_commuted,     *)
(*        piu_zz_jury_instance_engine).                                 *)
(*  L2a-alpha resultant face: the 6x6 Sylvester determinant of f and h  *)
(*        as a rational polynomial in (a,b,c,r), its nonvanishing       *)
(*        carried in QneqT — mechanical but verbose — born-able next    *)
(*        part (determinant by cofactor over Q; no division needed).    *)
(*  L2a-beta Schur-Cohn sufficiency: jury table implies all (complex)   *)
(*        roots inside the circle, closing the induction started by     *)
(*        L2a-2/3 against the root pairing of the Schur transform —     *)
(*        the research core of the criterion; routes: Schur-Cohn        *)
(*        determinantal form, or Hermite-Fujiwara inertia counted by    *)
(*        principal-minor signs (Sylvester criterion).                  *)
(*  L2a-gamma engine instantiation at r = rho plus/minus eps with       *)
(*        rational interval certificates for (Ainf,Binf,Cinf),          *)
(*        mechanical after L2a-beta; the r = 25000 outer certificate    *)
(*        is already born (L2a-5) and the pairing with Vieta            *)
(*        |N1|^2 = 512/(27*N3) supplies the inner radius data.          *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Audit: assumption accounting and decision-data extraction probe.     *)
(* ------------------------------------------------------------------ *)

Print Assumptions piu_zz_qpos_of_mul_r.
Print Assumptions piu_zz_qpos_of_mul_l.
Print Assumptions piu_zz_qpos_mul_r.
Print Assumptions piu_zz_qpos_mul_l.
Print Assumptions piu_zz_qpos_1pc.
Print Assumptions piu_zz_qpos_1mc.
Print Assumptions piu_zz_qpos_of_qle1.
Print Assumptions piu_zz_qpos_pqp1.
Print Assumptions piu_zz_qle_sub1.
Print Assumptions piu_zz_qlt_sum.
Print Assumptions piu_zz_qlt_of_pos_diff.
Print Assumptions piu_zz_pos_diff_of_qlt.
Print Assumptions piu_zz_qlt_of_pos_sum.
Print Assumptions piu_zz_pos_sum_of_qlt.
Print Assumptions piu_zz_qpos_zmq.
Print Assumptions piu_zz_qlt_neg_swap1.
Print Assumptions piu_zz_qle_neg_swap1.
Print Assumptions piu_zz_jury1_tab_nonzero.
Print Assumptions piu_zz_jury_tab_nonzero_gen.
Print Assumptions piu_zz_jury_scale_to_unit.
Print Assumptions piu_zz_jury_scale_from_unit.
Print Assumptions piu_zz_jury1_to_schur_red.
Print Assumptions piu_zz_schur_red_to_jury1.
Print Assumptions piu_zz_quad_no_root_ge1.
Print Assumptions piu_zz_quad_schur_sound.
Print Assumptions piu_zz_jury_engine_poly_commuted.
Print Assumptions piu_zz_jury_instance_engine.
Print Assumptions piu_zz_qpos_r6.
Print Assumptions piu_zz_qlt_of_qle_bool_false.
(* 补审块：33 条消解面中原件漏审的 10 条（qltabsT_l/qltabsT_r 两行
   系除名消解随件除位，故现行 29 行＋补审 10 行＝39 行全 Closed）。 *)
Print Assumptions piu_zz_q01.
Print Assumptions piu_zz_qplus_lt_r.
Print Assumptions piu_zz_qplus_le_r.
Print Assumptions piu_zz_qlt00_false.
Print Assumptions piu_zz_qle_of_qlt0.
Print Assumptions piu_zz_jury_diff_sq.
Print Assumptions piu_zz_jury_diff_sq_gen.
Print Assumptions piu_zz_jury_fact_pos.
Print Assumptions piu_zz_jury_fact_neg.
Print Assumptions piu_zz_quad_factor.

Extraction "piu_zz_jury_data.ml" piu_zz_jury_qty piu_zz_jury_witness.
