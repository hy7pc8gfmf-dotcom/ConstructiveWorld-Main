(* ==================================================================== *)
(* LW1ZPoly.v — The ring of univariate polynomials with integer          *)
(* coefficients, together with its formal derivative.                    *)
(*                                                                       *)
(* 模块名＋数学使命: LW1ZPoly 实现 Z[X] 的加法、标量乘、乘法、次数与      *)
(*   形式导数，是后续 Hermite 插值与 e 的超越性论证的代数基础层。         *)
(*   另含求值函子 eval_Z 的同态性（对加法与乘法）与乘积求导恒等式的       *)
(*   eval_Z 形（list 层陈述经 ZPOLYPRUNE 卡判假，eval 形为已验证通路）。   *)
(*   系数表约定：低次项在前（constant term at the head of the list），     *)
(*   零多项式记为空表（nil）；允许表尾出现非规范的后导零（non-canonical    *)
(*   trailing zeros are permitted; equality is list equality, and every   *)
(*   lemma below is stated and proved for this exact representation).     *)
(*   次数约定：零多项式的次数规定为 0。                                    *)
(* 依赖清单 (Stdlib only): ZArith, Lia                                    *)
(* 对标行: stdlib 的多项式库仅作命名参照，未 Require，无外部对标。         *)
(* 构造性注记: 全部定义为结构性递归的真算法；每条证明均由归纳与改写完成，  *)
(*   无任何假设常量；全件在全局语境下封闭（经 Print Assumptions 与        *)
(*   coqchk 复核）。                                                      *)
(* 编译配方：coqc -Q . "" LW1ZPoly.v                                     *)
(* ==================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(* A polynomial is its coefficient table, low degree first:
   the table (cons a0 (cons a1 (cons a2 nil))) denotes
   a0 + a1*X + a2*X^2 + ... . *)
Definition zpoly := list Z.

(* -------------------------------------------------------------------- *)
(* Addition: pointwise, padding the shorter table with zeros.            *)
(* -------------------------------------------------------------------- *)

Fixpoint zpoly_add (p q : zpoly) : zpoly :=
  match p with
  | nil => q
  | cons a p' =>
      match q with
      | nil => p
      | cons b q' => cons (a + b) (zpoly_add p' q')
      end
  end.

Lemma zpoly_add_comm : forall p q : zpoly, zpoly_add p q = zpoly_add q p.
Proof.
  induction p as [|a p' IH]; intros q; destruct q as [|b q'];
    simpl; try reflexivity.
  (* 归纳步：由 n 到 S n — the two heads add commutatively in Z. *)
  rewrite (IH q'). rewrite Z.add_comm. reflexivity.
Qed.

Lemma zpoly_add_assoc : forall p q r : zpoly,
  zpoly_add (zpoly_add p q) r = zpoly_add p (zpoly_add q r).
Proof.
  induction p as [|a p' IH]; intros q r;
    destruct q as [|b q']; destruct r as [|c r']; simpl; try reflexivity.
  (* 归纳步：由 n 到 S n — heads associate in Z, tails by induction. *)
  rewrite (IH q' r'). f_equal. lia.
Qed.

(* Right unit: appending the empty table changes nothing. *)
Lemma zpoly_add_nil_r : forall p : zpoly, zpoly_add p nil = p.
Proof.
  intros p. destruct p as [|a p']; reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(* Scalar multiplication by an integer coefficient.  Multiplying by 0    *)
(* returns the empty table exactly, which keeps the product recursion    *)
(* predictable at the degenerate coefficient.                            *)
(* -------------------------------------------------------------------- *)

Fixpoint zpoly_scalar (c : Z) (p : zpoly) : zpoly :=
  match p with
  | nil => nil
  | cons a p' => if Z.eqb c 0 then nil else cons (c * a) (zpoly_scalar c p')
  end.

Lemma zpoly_scalar_0 : forall p : zpoly, zpoly_scalar 0 p = nil.
Proof.
  induction p as [|a p' IH]; simpl; reflexivity.
Qed.

Lemma zpoly_scalar_add : forall (c : Z) (p q : zpoly),
  zpoly_scalar c (zpoly_add p q) =
  zpoly_add (zpoly_scalar c p) (zpoly_scalar c q).
Proof.
  intros c p q. destruct (Z.eqb c 0) eqn:Ec.
  - apply Z.eqb_eq in Ec. subst c. rewrite !zpoly_scalar_0. reflexivity.
  - revert q.
    induction p as [|a p' IH]; intros q; destruct q as [|b q'];
      simpl; try rewrite Ec; try reflexivity.
    (* 归纳步：由 n 到 S n — the coefficient distributes over the heads. *)
    rewrite IH. rewrite Z.mul_add_distr_l. reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(* Multiplication: convolution.  For p with head coefficient a and tail  *)
(* p' one has p * q = a * q + X * (p' * q), where X * r shifts the table *)
(* of r right by one position (a zero at the head, since the head        *)
(* carries degree 0).                                                    *)
(* -------------------------------------------------------------------- *)

Fixpoint zpoly_mul (p q : zpoly) : zpoly :=
  match p with
  | nil => nil
  | cons a p' =>
      zpoly_add (zpoly_scalar a q) (cons 0 (zpoly_mul p' q))
  end.

Lemma zpoly_mul_cons0 : forall (d q : zpoly),
  zpoly_mul (cons 0 d) q = cons 0 (zpoly_mul d q).
Proof.
  intros d q. simpl. rewrite zpoly_scalar_0. reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(* Degree.  zpoly_deg_go scans the table carrying the index of its head; *)
(* the result is the largest index of a nonzero coefficient, and 0 for   *)
(* the zero polynomial (declared convention).                            *)
(* -------------------------------------------------------------------- *)

Fixpoint zpoly_deg_go (i : nat) (p : zpoly) : nat :=
  match p with
  | nil => 0
  | cons a p' =>
      if Z.eqb a 0
      then zpoly_deg_go (S i) p'
      else Nat.max i (zpoly_deg_go (S i) p')
  end.

Definition zpoly_degree (p : zpoly) : nat := zpoly_deg_go 0 p.

(* -------------------------------------------------------------------- *)
(* Formal derivative.  Writing p = a0 + X * t with t the polynomial of   *)
(* the tail coefficients, the derivative of p is t + X * t'.  This gives *)
(* a structural recursion with no index accumulator.                     *)
(* -------------------------------------------------------------------- *)

Fixpoint zpoly_deriv (p : zpoly) : zpoly :=
  match p with
  | nil => nil
  | cons a p' => zpoly_add p' (cons 0 (zpoly_deriv p'))
  end.

(* The derivative ignores the constant term, so a shifted table merely   *)
(* loses its head zero: deriv (X-shifted m) = m + X * deriv m. *)
Lemma zpoly_deriv_cons0 : forall m : zpoly,
  zpoly_deriv (cons 0 m) = zpoly_add m (cons 0 (zpoly_deriv m)).
Proof.
  intros m. reflexivity.
Qed.

Lemma zpoly_deriv_add : forall p q : zpoly,
  zpoly_deriv (zpoly_add p q) =
  zpoly_add (zpoly_deriv p) (zpoly_deriv q).
Proof.
  induction p as [|a p' IH]; intros q.
  - reflexivity.
  - destruct q as [|b q'].
    + simpl. rewrite zpoly_add_nil_r. reflexivity.
    + (* 归纳步：由 n 到 S n — differentiate termwise, then regroup the    *)
      (* three summands by associativity and commutativity of addition.   *)
      simpl.
      rewrite IH.
      rewrite (zpoly_add_assoc p' q'
                 (cons 0 (zpoly_add (zpoly_deriv p') (zpoly_deriv q')))).
      rewrite (zpoly_add_assoc p' (cons 0 (zpoly_deriv p'))
                 (zpoly_add q' (cons 0 (zpoly_deriv q')))).
      rewrite <- (zpoly_add_assoc (cons 0 (zpoly_deriv p')) q'
                    (cons 0 (zpoly_deriv q'))).
      rewrite (zpoly_add_comm (cons 0 (zpoly_deriv p')) q').
      rewrite (zpoly_add_assoc q' (cons 0 (zpoly_deriv p'))
                 (cons 0 (zpoly_deriv q'))).
      simpl. reflexivity.
Qed.

Lemma zpoly_deriv_scalar : forall (c : Z) (p : zpoly),
  zpoly_deriv (zpoly_scalar c p) = zpoly_scalar c (zpoly_deriv p).
Proof.
  intros c p. destruct (Z.eqb c 0) eqn:Ec.
  - apply Z.eqb_eq in Ec. subst c.
    rewrite !zpoly_scalar_0. reflexivity.
  - induction p as [|a p' IH].
    + reflexivity.
    + (* 归纳步：由 n 到 S n — the constant c passes through the          *)
      (* differentiation, coefficientwise by c * 0 = 0.                   *)
      simpl. rewrite Ec. simpl. rewrite IH.
      rewrite zpoly_scalar_add. simpl. rewrite Ec.
      rewrite Z.mul_0_r. reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(* Evaluation at an integer point (ascending powers: each step           *)
(* contributes a_i * z^i and advances the running power by one factor z). *)
(* -------------------------------------------------------------------- *)

Fixpoint zpoly_eval_go (z pow : Z) (p : zpoly) : Z :=
  match p with
  | nil => 0
  | cons a p' => a * pow + zpoly_eval_go z (z * pow) p'
  end.

Definition zpoly_eval_Z (p : zpoly) (z : Z) : Z := zpoly_eval_go z 1 p.

Lemma zpoly_eval_go_add : forall (p q : zpoly) (z pow : Z),
  zpoly_eval_go z pow (zpoly_add p q) =
  zpoly_eval_go z pow p + zpoly_eval_go z pow q.
Proof.
  induction p as [|a p' IH]; intros q z pow; destruct q as [|b q'];
    simpl; try lia.
  (* 归纳步：由 n 到 S n — distribute over the heads, then apply the      *)
  (* induction conclusion to the padded tails.                           *)
  rewrite IH. rewrite Z.mul_add_distr_r. lia.
Qed.

Lemma zpoly_eval_add : forall (p q : zpoly) (z : Z),
  zpoly_eval_Z (zpoly_add p q) z = zpoly_eval_Z p z + zpoly_eval_Z q z.
Proof.
  intros p q z. unfold zpoly_eval_Z. apply zpoly_eval_go_add.
Qed.

(* -------------------------------------------------------------------- *)
(* Evaluation is multiplicative.  The go-level statement carries a free  *)
(* running power: the value of a product table at power pow equals the   *)
(* value of p at pow times the value of q at power 1.  Two auxiliary     *)
(* identities (scaling and power rescaling of the running value) feed    *)
(* the induction; the top-level form instantiates pow with 1.            *)
(* -------------------------------------------------------------------- *)

(* Scaling every coefficient by c scales the value by c. *)
Lemma zpoly_eval_go_scalar : forall (c : Z) (q : zpoly) (z pow : Z),
  zpoly_eval_go z pow (zpoly_scalar c q) = c * zpoly_eval_go z pow q.
Proof.
  intros c q. induction q as [|b q' IH]; intros z pow.
  - simpl. lia.
  - simpl. destruct (Z.eqb c 0) eqn:Ec.
    + apply Z.eqb_eq in Ec. subst c. simpl. lia.
    + (* 归纳步：由 n 到 S n — the factor c passes to the head product.   *)
      simpl. rewrite IH. ring.
Qed.

(* Raising the running power to z is worth one factor of pow. *)
Lemma zpoly_eval_go_pow : forall (p : zpoly) (z pow : Z),
  zpoly_eval_go z pow p = pow * zpoly_eval_go z 1 p.
Proof.
  induction p as [|a p' IH]; intros z pow.
  - simpl. lia.
  - (* 归纳步：由 n 到 S n — the running power advances on both sides, so  *)
    (* the induction instance fires at z * pow and at z * 1.             *)
    simpl. rewrite (IH z (z * pow)). rewrite (IH z (z * 1)). ring.
Qed.

Lemma zpoly_eval_go_mul : forall (p q : zpoly) (z pow : Z),
  zpoly_eval_go z pow (zpoly_mul p q) =
  zpoly_eval_go z pow p * zpoly_eval_go z 1 q.
Proof.
  intros p q. induction p as [|a p' IH]; intros z pow.
  - simpl. lia.
  - (* 归纳步：由 n 到 S n — split a*q + X*(p'*q), evaluate each part.    *)
    simpl. rewrite zpoly_eval_go_add. rewrite zpoly_eval_go_scalar. simpl.
    rewrite IH. rewrite (zpoly_eval_go_pow q z pow). ring.
Qed.

Lemma zpoly_eval_Z_mul : forall (p q : zpoly) (x : Z),
  zpoly_eval_Z (zpoly_mul p q) x = zpoly_eval_Z p x * zpoly_eval_Z q x.
Proof.
  intros p q x. unfold zpoly_eval_Z. apply zpoly_eval_go_mul.
Qed.

(* A leading zero contributes nothing by itself but multiplies the       *)
(* running power by z. *)
Lemma zpoly_eval_go_cons0 : forall (r : zpoly) (z pow : Z),
  zpoly_eval_go z pow (cons 0 r) = zpoly_eval_go z (z * pow) r.
Proof.
  intros r z pow. simpl. lia.
Qed.

(* -------------------------------------------------------------------- *)
(* The product rule at the level of values.  The list-level statement    *)
(* is false in this representation (zero pruning of scalar products),    *)
(* but both sides evaluate identically: induction on p reduces the       *)
(* goal, via the additivity and multiplicativity of the evaluator, to    *)
(* a ring identity between integer evaluation values.                    *)
(* -------------------------------------------------------------------- *)

Lemma zpoly_eval_go_deriv_mul : forall (p q : zpoly) (z pow : Z),
  zpoly_eval_go z pow (zpoly_deriv (zpoly_mul p q)) =
  zpoly_eval_go z pow
    (zpoly_add (zpoly_mul (zpoly_deriv p) q)
               (zpoly_mul p (zpoly_deriv q))).
Proof.
  intros p q. induction p as [|a p' IH]; intros z pow.
  - simpl. reflexivity.
  - (* Unfold the product by its defining recursion, then differentiate  *)
    (* the two summands by deriv_add / deriv_cons0 / deriv_scalar.       *)
    assert (Hm : zpoly_mul (cons a p') q =
                 zpoly_add (zpoly_scalar a q) (cons 0 (zpoly_mul p' q)))
      by reflexivity.
    rewrite Hm.
    rewrite zpoly_deriv_add.
    rewrite zpoly_deriv_cons0.
    rewrite zpoly_deriv_scalar.
    assert (Hd : zpoly_deriv (cons a p') =
                 zpoly_add p' (cons 0 (zpoly_deriv p'))) by reflexivity.
    rewrite Hd.
    (* Evaluate both sides additively / multiplicatively down to Z. *)
    rewrite !zpoly_eval_go_add.
    rewrite !zpoly_eval_go_mul.
    rewrite !zpoly_eval_go_add.
    rewrite !zpoly_eval_go_scalar.
    rewrite !zpoly_eval_go_cons0.
    rewrite IH.
    rewrite !zpoly_eval_go_add.
    rewrite !zpoly_eval_go_mul.
    (* Unfold the head value of the shifted factor and normalise the      *)
    (* scalar term by the power rescaling, then the goal is a Z identity. *)
    assert (Hc : zpoly_eval_go z pow (cons a p') =
                 a * pow + zpoly_eval_go z (z * pow) p') by reflexivity.
    rewrite Hc.
    rewrite (zpoly_eval_go_pow (zpoly_deriv q) z pow).
    ring.
Qed.

Lemma zpoly_deriv_mul : forall (p q : zpoly) (x : Z),
  zpoly_eval_Z (zpoly_deriv (zpoly_mul p q)) x =
  zpoly_eval_Z (zpoly_add (zpoly_mul (zpoly_deriv p) q)
                          (zpoly_mul p (zpoly_deriv q))) x.
Proof.
  intros p q x. unfold zpoly_eval_Z. apply zpoly_eval_go_deriv_mul.
Qed.

(* -------------------------------------------------------------------- *)
(* Ring export of the evaluator.  The three pointwise identities —       *)
(* additivity, multiplicativity and scalar linearity of zpoly_eval_Z —   *)
(* are stated under one uniform naming scheme and grouped into a single  *)
(* entry for downstream consumers (Hermite coefficient accounting and    *)
(* evaluation of the e-transcendence chain at integer points).           *)
(* Packaging form (self-declared): one Lemma whose statement is the      *)
(* iterated conjunction (and) of the three eval_Z-level pointwise        *)
(* equations; every carrier is Set-sorted data (zpoly, Z) compared by    *)
(* Leibniz equality, and every conjunct is discharged by an exact        *)
(* reference to a lemma proved above, so no identity is proved twice.    *)
(* -------------------------------------------------------------------- *)

(* Additive member under the uniform name: exact reference to the       *)
(* verified additive identity (the statements are alpha-equivalent).    *)
Lemma zpoly_eval_Z_add : forall (p q : zpoly) (x : Z),
  zpoly_eval_Z (zpoly_add p q) x = zpoly_eval_Z p x + zpoly_eval_Z q x.
Proof.
  exact zpoly_eval_add.
Qed.

(* Scalar member: multiplying the table by k multiplies the value by k. *)
Lemma zpoly_eval_Z_scalar : forall (k : Z) (p : zpoly) (x : Z),
  zpoly_eval_Z (zpoly_scalar k p) x = k * zpoly_eval_Z p x.
Proof.
  intros k p x. unfold zpoly_eval_Z. apply zpoly_eval_go_scalar.
Qed.

(* The grouped export: evaluation at any integer point respects the     *)
(* pointwise operations — addition, multiplication and scalar           *)
(* multiplication — in one conjunctive statement.                       *)
Lemma zpoly_eval_Z_ring_hom : forall (p q : zpoly) (k x : Z),
  zpoly_eval_Z (zpoly_add p q) x = zpoly_eval_Z p x + zpoly_eval_Z q x
  /\ zpoly_eval_Z (zpoly_mul p q) x = zpoly_eval_Z p x * zpoly_eval_Z q x
  /\ zpoly_eval_Z (zpoly_scalar k p) x = k * zpoly_eval_Z p x.
Proof.
  intros p q k x. split.
  - exact (zpoly_eval_add p q x).
  - split.
    + exact (zpoly_eval_Z_mul p q x).
    + exact (zpoly_eval_Z_scalar k p x).
Qed.
