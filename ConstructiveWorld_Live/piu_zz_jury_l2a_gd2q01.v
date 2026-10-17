(*
  piu_zz_jury_l2a_gd2q01.v — L2a-alpha resultant face of the third-order
  Jury criterion; slice on top of piu_zz_jury_cubic.

  使命：结式面 born 块——(i) 自足 Q 系行列式工具箱（余子式展开，无除法）；
  (ii) f(X)=X^3+aX^2+bX+c 与圆多项式 h(X)=X^3*f(r^2/X)=cX^3+b r^2 X^2+
  a r^4 X+r^6 的 6x6 Sylvester 行列式构造（转置取向）与结式函数；
  (iii) 核向量行组合的六条求值恒等式（降幂权 (z^5,z^4,z^3,z^2,z,1)，
  逐列读出 z^2*f, z*f, f, z^2*h, z*h, h）；(iv) 引擎系数在 r=25000 的
  结式非零 QneqT 判定实例。主桥（公共根⟹结式零）语句面注释冻结，
  证明核留待后续部分（交替性工具包），编译模块不携带未证承诺。

  依赖：Stdlib QArith, Qring, Lia, List；池内件 piu_zz_poincare_engine
  （QneqT/qneqT_intro）、piu_zz_jury_cubic（piu_zz_jury_poly）与
  piu_zz_gauss_pair（qeqT/qeqT_intro——refit 波新增，Set 承载
  Q 恒等式皿：11 条 Qeq 结论语句改形载体）。
  对标：J. J. Sylvester (1840) 结式行列式；J. Schur, J. reine angew. Math.
  147 (1918)；E. I. Jury & B. D. O. Anderson, IEEE T-AC（三阶稳定性）。
  构造性：数据面全 Set（QneqT 判定实例；qdet/sylvT/rev_poly 全透明可
  提取；refit 波起 11 条 Q 恒等式以 qeqT Set 皿承载——
  qdet_0/1/2/3_diag/zero_row2 + eval_f1..h3），全程无复根对象、无实分析、
  无除法；冻结块=纯注释。
  编译配方：先编 piu_zz_poincare_engine.v 与 piu_zz_jury_cubic.v，再
  cpu_guard 包裹下 rocq c -native-compiler no -q -Q . "" 本件。
*)

From Stdlib Require Import QArith Qring Lia List.
Require Import piu_zz_poincare_engine.
Require Import piu_zz_jury_cubic.
Require Import piu_zz_gauss_pair.

(* ------------------------------------------------------------------ *)
(* Born piece 1: a self-contained determinant toolbox over Q.           *)
(* qdet n m computes the determinant of the n x n matrix m (list of     *)
(* rows) by cofactor expansion along the first row; n is the fuel.      *)
(* No division, no Prop elimination: fully extractable.                 *)
(* ------------------------------------------------------------------ *)

Fixpoint piu_zz_l2a_drop_nth (j : nat) (l : list Q) : list Q :=
  match l with
  | nil => nil
  | cons x xs =>
      match j with
      | 0%nat => xs
      | S j' => cons x (piu_zz_l2a_drop_nth j' xs)
      end
  end.

Fixpoint piu_zz_l2a_drop_col (j : nat) (m : list (list Q)) : list (list Q) :=
  match m with
  | nil => nil
  | cons rw rest => cons (piu_zz_l2a_drop_nth j rw) (piu_zz_l2a_drop_col j rest)
  end.

Definition piu_zz_l2a_minor (j : nat) (rows : list (list Q)) : list (list Q) :=
  map (piu_zz_l2a_drop_nth j) rows.

Fixpoint piu_zz_l2a_qdet (n : nat) (m : list (list Q)) : Q :=
  match n with
  | 0%nat => 1%Q
  | S n' =>
      match m with
      | nil => 0%Q
      | cons r rows =>
          fold_right (fun j acc =>
            (if Nat.even j then 1%Q else (-1)%Q) * nth j r 0%Q
            * piu_zz_l2a_qdet n' (piu_zz_l2a_minor j rows) + acc) 0%Q
            (seq 0 (S n'))
      end
  end.

Lemma piu_zz_l2a_qdet_0 : forall m, qeqT (piu_zz_l2a_qdet 0 m) 1%Q.
Proof. intros m. apply qeqT_intro. reflexivity. Qed.

Lemma piu_zz_l2a_qdet_1 : forall x,
  qeqT (piu_zz_l2a_qdet 1 (cons (cons x nil) nil)) x.
Proof. intros x. apply qeqT_intro. cbn. ring. Qed.

Lemma piu_zz_l2a_qdet_2 : forall a b c d,
  qeqT (piu_zz_l2a_qdet 2 (cons (cons a (cons b nil)) (cons (cons c (cons d nil)) nil)))
       ((a * d - b * c)%Q).
Proof. intros a b c d. apply qeqT_intro. cbn. ring. Qed.

Lemma piu_zz_l2a_qdet_3_diag : forall a b c,
  qeqT (piu_zz_l2a_qdet 3 (cons (cons a (cons 0 (cons 0 nil)))
                                (cons (cons 0 (cons b (cons 0 nil)))
                                   (cons (cons 0 (cons 0 (cons c nil))) nil))))
       ((a * b * c)%Q).
Proof. intros a b c. apply qeqT_intro. cbn. ring. Qed.

Lemma piu_zz_l2a_qdet_zero_row2 : forall c d,
  qeqT (piu_zz_l2a_qdet 2 (cons (cons 0 (cons 0 nil)) (cons (cons c (cons d nil)) nil)))
       0%Q.
Proof. intros c d. apply qeqT_intro. cbn. ring. Qed.

(* ------------------------------------------------------------------ *)
(* Born piece 2: the circle polynomial h(X) = X^3 * f(r^2/X) and the    *)
(* 6x6 Sylvester matrix of f and h, transposed orientation (rows of     *)
(* sylvT are the columns of the classical matrix; the classical         *)
(* determinant is transpose-invariant, so the nonvanishing face is the  *)
(* same — remark only, no unproved claim is attached to a name here).   *)
(* ------------------------------------------------------------------ *)

Definition piu_zz_l2a_rev_poly (a b c r z : Q) : Q :=
  (c * (z * z * z) + b * (r * r) * (z * z)
   + a * (r * r * r * r) * z + r * r * r * r * r * r)%Q.

Definition piu_zz_l2a_row6 (x1 x2 x3 x4 x5 x6 : Q) : list Q :=
  cons x1 (cons x2 (cons x3 (cons x4 (cons x5 (cons x6 nil))))).

Definition piu_zz_l2a_sylvT (a b c r : Q) : list (list Q) :=
  cons (piu_zz_l2a_row6 1 0 0 c 0 0)
    (cons (piu_zz_l2a_row6 a 1 0 (b * (r * r)) c 0)
      (cons (piu_zz_l2a_row6 b a 1 (a * (r * r * r * r)) (b * (r * r)) c)
        (cons (piu_zz_l2a_row6 c b a (r * r * r * r * r * r)
                 (a * (r * r * r * r)) (b * (r * r)))
          (cons (piu_zz_l2a_row6 0 c b 0 (r * r * r * r * r * r)
                   (a * (r * r * r * r)))
            (cons (piu_zz_l2a_row6 0 0 c 0 0 (r * r * r * r * r * r)) nil))))).

Definition piu_zz_l2a_resultant (a b c r : Q) : Q :=
  piu_zz_l2a_qdet 6 (piu_zz_l2a_sylvT a b c r).

(* ------------------------------------------------------------------ *)
(* Born piece 3: the six evaluation identities — the raw material of    *)
(* the kernel-row-combination argument.  The columns of sylvT are the   *)
(* coefficient-shift rows of the classical Sylvester matrix, so the     *)
(* column sums weighted by the descending powers (z^5,z^4,z^3,z^2,z,1)  *)
(* evaluate z^2*f, z*f, f, z^2*h, z*h, h respectively.                  *)
(* ------------------------------------------------------------------ *)

Lemma piu_zz_l2a_eval_f1 : forall (a b c r z : Q),
  qeqT ((1 * (z * z * z * z * z) + a * (z * z * z * z) + b * (z * z * z)
         + c * (z * z) + 0 * z + 0 * 1)%Q)
       ((z * (z * piu_zz_jury_poly a b c z))%Q).
Proof. intros a b c r z. apply qeqT_intro. unfold piu_zz_jury_poly. ring. Qed.

Lemma piu_zz_l2a_eval_f2 : forall (a b c r z : Q),
  qeqT ((0 * (z * z * z * z * z) + 1 * (z * z * z * z) + a * (z * z * z)
         + b * (z * z) + c * z + 0 * 1)%Q)
       ((z * piu_zz_jury_poly a b c z)%Q).
Proof. intros a b c r z. apply qeqT_intro. unfold piu_zz_jury_poly. ring. Qed.

Lemma piu_zz_l2a_eval_f3 : forall (a b c r z : Q),
  qeqT ((0 * (z * z * z * z * z) + 0 * (z * z * z * z) + 1 * (z * z * z)
         + a * (z * z) + b * z + c * 1)%Q)
       ((piu_zz_jury_poly a b c z)%Q).
Proof. intros a b c r z. apply qeqT_intro. unfold piu_zz_jury_poly. ring. Qed.

Lemma piu_zz_l2a_eval_h1 : forall (a b c r z : Q),
  qeqT ((c * (z * z * z * z * z) + b * (r * r) * (z * z * z * z)
         + a * (r * r * r * r) * (z * z * z)
         + (r * r * r * r * r * r) * (z * z) + 0 * z + 0 * 1)%Q)
       ((z * (z * piu_zz_l2a_rev_poly a b c r z))%Q).
Proof. intros a b c r z. apply qeqT_intro. unfold piu_zz_l2a_rev_poly. ring. Qed.

Lemma piu_zz_l2a_eval_h2 : forall (a b c r z : Q),
  qeqT ((0 * (z * z * z * z * z) + c * (z * z * z * z) + b * (r * r) * (z * z * z)
         + a * (r * r * r * r) * (z * z) + (r * r * r * r * r * r) * z + 0 * 1)%Q)
       ((z * piu_zz_l2a_rev_poly a b c r z)%Q).
Proof. intros a b c r z. apply qeqT_intro. unfold piu_zz_l2a_rev_poly. ring. Qed.

Lemma piu_zz_l2a_eval_h3 : forall (a b c r z : Q),
  qeqT ((0 * (z * z * z * z * z) + 0 * (z * z * z * z) + c * (z * z * z)
         + b * (r * r) * (z * z) + a * (r * r * r * r) * z
         + (r * r * r * r * r * r) * 1)%Q)
       ((piu_zz_l2a_rev_poly a b c r z)%Q).
Proof. intros a b c r z. apply qeqT_intro. unfold piu_zz_l2a_rev_poly. ring. Qed.

(* ------------------------------------------------------------------ *)
(* Born piece 4: the engine decision instance at r = 25000.  The        *)
(* resultant of the engine polynomial pair is a nonzero rational        *)
(* (QneqT, Set-carried); decided by pure computation, no assumption.    *)
(* ------------------------------------------------------------------ *)

Definition piu_zz_l2a_resultant_engine_value : Q :=
  piu_zz_l2a_resultant piu_zz_Ainf piu_zz_Binf piu_zz_Cinf
    piu_zz_jury_engine_radius.

Lemma piu_zz_l2a_resultant_engine_qneq :
  QneqT piu_zz_l2a_resultant_engine_value 0%Q.
Proof.
  apply qneqT_intro. intro Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* ================================================================== *)
(* FROZEN STATEMENT — the L2a-alpha main bridge (proof core reserved    *)
(* for later parts; frozen here as a comment so that this compiled      *)
(* module carries no unproved claim).                                   *)
(*                                                                      *)
(*   Theorem piu_zz_l2a_common_root_resultant_zero :                    *)
(*     forall (a b c r z : Q),                                          *)
(*       (piu_zz_jury_poly a b c z == 0)%Q ->                           *)
(*       (piu_zz_l2a_rev_poly a b c r z == 0)%Q ->                      *)
(*       (piu_zz_l2a_resultant a b c r == 0)%Q.                         *)
(*                                                                      *)
(*   Route: the six born eval lemmas give the row combination           *)
(*   sum_j w_j * row_j(sylvT) = (z^2*f, z*f, f, z^2*h, z*h, h) with     *)
(*   w = (z^5,z^4,z^3,z^2,z,1), which is the zero vector under the      *)
(*   two hypotheses; then kill the first row of sylvT by the standard   *)
(*   alternating-determinant argument.                                  *)
(*                                                                      *)
(*   Sub-lemma checklist (statement shape / status):                    *)
(*    ALT-1 adjacent row swap flips the determinant sign — born-able    *)
(*        mechanically (specific instances close by cbn+ring; generic   *)
(*        list version by induction on the fuel).                       *)
(*    ALT-2 two equal rows force determinant zero — born-able after     *)
(*        ALT-1 (bubble one copy next to the other).                    *)
(*    ALT-3 adding a multiple of another row to row 1 preserves the     *)
(*        determinant — born-able after ALT-1/2 (additivity in row 1    *)
(*        plus the repeated-row vanishing).                             *)
(*    ALT-4 assembly: apply ALT-3 five times with weights z..z^5,       *)
(*        conclude via the zero-row cofactor vanishing and the six      *)
(*        born eval lemmas (piu_zz_l2a_eval_f1..h3).                    *)
(*                                                                      *)
(*   Permanently out of Q-world scope (remark, not a debt): the         *)
(*   converse "resultant zero implies a common root" needs the          *)
(*   algebraic closure (fundamental theorem of algebra) and the         *)
(*   "no root on |z|=r" reading needs complex conjugation; in this      *)
(*   rational-carried world the honest decision form is the QneqT       *)
(*   nonvanishing instance born above together with the contrapositive  *)
(*   of the frozen bridge once ALT-1..4 close it.                       *)
(*                                                                      *)
(*   Mechanical next items: (a) the quadratic-instance bridge           *)
(*   (2x2 reversal, case split r^2 = q vs r^2 <> q with cancellation    *)
(*   via Qmult_integral — full bridge born-able at degree 2);           *)
(*   (b) the explicit expanded polynomial face of the 6x6 resultant     *)
(*   (canonical form by ring_simplify, one ring-verified lemma).        *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Audit: assumption accounting and data-level extraction probe.        *)
(* ------------------------------------------------------------------ *)

Print Assumptions piu_zz_l2a_qdet_0.
Print Assumptions piu_zz_l2a_qdet_1.
Print Assumptions piu_zz_l2a_qdet_2.
Print Assumptions piu_zz_l2a_qdet_3_diag.
Print Assumptions piu_zz_l2a_qdet_zero_row2.
Print Assumptions piu_zz_l2a_eval_f1.
Print Assumptions piu_zz_l2a_eval_f2.
Print Assumptions piu_zz_l2a_eval_f3.
Print Assumptions piu_zz_l2a_eval_h1.
Print Assumptions piu_zz_l2a_eval_h2.
Print Assumptions piu_zz_l2a_eval_h3.
Print Assumptions piu_zz_l2a_resultant_engine_qneq.

Extraction "piu_zz_l2a_gd2q01_data.ml" piu_zz_l2a_qdet piu_zz_l2a_sylvT
  piu_zz_l2a_rev_poly piu_zz_l2a_resultant.
