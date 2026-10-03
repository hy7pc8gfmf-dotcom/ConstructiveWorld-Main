(* ========================================================================= *)
(* LW2IntegMachine - the e^{-t}-kernel endpoint functional machine: the      *)
(* integration-by-parts algebraization driving the M2 Hermite integrator.    *)
(* 模块名：LW2IntegMachine.  数学使命：for a rational polynomial f, the       *)
(* endpoint functional lw2_exp_L E K f X := eps K f (0) - E * eps K f (X)    *)
(* (eps K f = the truncated antiderivative table sum_{k<K} f^{(k)} provided  *)
(* by LW2Hermite) algebraizes int_0^X e^{-t} f(t) dt, the weight surviving   *)
(* only as the explicit scalar E (= e^{-X}); no weight function is built.    *)
(* 主件 lw2_exp_int_parts：L f == f(0) - E * f(X) + L f' whenever            *)
(* length f <= K, the algebraized integration-by-parts step for e^{-t} * f.  *)
(* Companion: nil base case, fuel stability (K >= length f immaterial), the  *)
(* closed form L f == sum_k f^{(k)}(0) - E * sum_k f^{(k)}(X), Q-bilinearity.*)
(* 路线裁决：route 2 (common abstraction layer), the layer being LW2Hermite   *)
(* lw2_eps (its kernel identity is commented "the algebraized exponential-   *)
(* weight equation"); the LW0Endpoint IBP family lw0_qp_pair_ibp is the      *)
(* weight-free bilinear pairing q * ai(f*g,0)(q) with no weight slot.        *)
(* 远端声明：the S05 master LW0Endpoint (2080 lines, md5 cb265ac1) supplies  *)
(* the sin/cos real-layer wrappers; here the infinite endpoint enters only   *)
(* via the explicit scalar E over finite X (finite-sum closed form, no       *)
(* limiting construction); downstream explicit bounds follow that recipe.    *)
(* 依赖清单：LW2Hermite (lw2_eps, lw2_eps_eval, lw2_eps_eval_sum,            *)
(* lw2_eps_deriv_kernel, lw2_qsum0/lw2_eval_di/lw2_len_deriv laws),          *)
(* transitively LW0QPoly; Stdlib QArith, Lia.  LW0Endpoint stays outside     *)
(* this Require closure on purpose.  对标行：Hermite 1873 (C. R. Acad. Sci.  *)
(* Paris 77); standard iterated integration by parts.                        *)
(* 构造性注记：structurally recursive Fixpoints and Qeq equations only; no   *)
(* logical premises beyond nat orderings.  编译配方：env COQLIB/ROCQLIB set  *)
(* to the Rocq 9.1 library; coqc.exe -q -Q . "" and coqchk per sandbox file. *)
(* ========================================================================= *)

From Stdlib Require Import QArith Lia Arith.
Require Import LW0QPoly.
Require Import LW2Hermite.

(* ------------------------------------------------------------------ *)
(* Section 1.  The endpoint functional and its elementary laws.        *)
(* ------------------------------------------------------------------ *)

(* The e^{-t}-kernel endpoint functional: the truncated antiderivative     *)
(* table evaluated at the two endpoints, combined with the explicit        *)
(* exponential scalar E (= e^{-X}).  Orientation chosen so that the        *)
(* machine recursion below matches the standard integration-by-parts step. *)
Definition lw2_exp_L (E : Q) (K : nat) (f : QPoly) (X : Q) : Q :=
  qpoly_eval (lw2_eps K f) 0%Q - E * qpoly_eval (lw2_eps K f) X.

(* Nil base case: the machine integrates nothing on the zero polynomial. *)
Lemma lw2_exp_L_nil : forall E K X,
  lw2_exp_L E K nil X == 0.
Proof.
  intros E K X.
  assert (Hn : (length (@nil Q) <= K)%nat) by (cbn [length]; lia).
  unfold lw2_exp_L.
  rewrite (lw2_eps_eval K nil 0%Q Hn), (lw2_eps_eval K nil X Hn).
  assert (Hy : qpoly_eval (lw2_eps (length (@nil Q)) nil) 0%Q == 0)
    by reflexivity.
  assert (Hz : qpoly_eval (lw2_eps (length (@nil Q)) nil) X == 0)
    by reflexivity.
  rewrite Hy, Hz.
  ring.
Qed.

(* Fuel stability: any table depth K at least the coefficient length of f  *)
(* yields the same functional value, so consumers may pick K := length f.  *)
Lemma lw2_exp_L_fuel : forall E K f X,
  (length f <= K)%nat ->
  lw2_exp_L E K f X == lw2_exp_L E (length f) f X.
Proof.
  intros E K f X HK.
  unfold lw2_exp_L.
  rewrite (lw2_eps_eval K f 0%Q HK), (lw2_eps_eval K f X HK).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 2.  Evaluation laws of the table under polynomial algebra.  *)
(* ------------------------------------------------------------------ *)

(* Evaluation-layer additivity of the table. *)
Lemma lw2_eps_eval_add : forall K u v x,
  qpoly_eval (lw2_eps K (qpoly_add u v)) x ==
  qpoly_eval (lw2_eps K u) x + qpoly_eval (lw2_eps K v) x.
Proof.
  intros K u v x.
  rewrite !lw2_eps_eval_sum.
  rewrite <- lw2_qsum0_add.
  apply lw2_qsum0_ext.
  intros j _.
  apply lw2_eval_di_add.
Qed.

(* Evaluation-layer homogeneity of the table. *)
Lemma lw2_eps_eval_scalar : forall K c f x,
  qpoly_eval (lw2_eps K (qpoly_scalar c f)) x ==
  c * qpoly_eval (lw2_eps K f) x.
Proof.
  intros K c f x.
  rewrite !lw2_eps_eval_sum.
  rewrite <- (lw2_qsum0_scale K (fun k => qpoly_eval (qpoly_deriv_iter k f) x) c).
  apply lw2_qsum0_ext.
  intros j _.
  apply lw2_eval_di_scalar.
Qed.

(* The bridge: applying the table to the derivative equals differentiating  *)
(* the table, at evaluation level.  This is what lets the machine recursion *)
(* fire on lw2_eps_deriv_kernel.                                            *)
Lemma lw2_eps_deriv_point : forall K f x,
  qpoly_eval (lw2_eps K (qpoly_deriv f)) x ==
  qpoly_eval (qpoly_deriv (lw2_eps K f)) x.
Proof.
  intros K f x.
  rewrite lw2_eps_deriv_sum, !lw2_eps_eval_sum.
  apply lw2_qsum0_ext.
  intros j _.
  rewrite <- qpoly_deriv_iter_commute.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 3.  The machine: integration by parts, algebraized.         *)
(* ------------------------------------------------------------------ *)

(* 主件：the e^{-t} * f integration-by-parts step.  For any table depth K   *)
(* covering f, the endpoint functional satisfies the one-step recursion     *)
(* L E K f X = f(0) - E * f(X) + L E K f' X; iterating down to the nil      *)
(* polynomial integrates e^{-t} * f in deg f machine steps.                 *)
Lemma lw2_exp_int_parts : forall E K f X,
  (length f <= K)%nat ->
  lw2_exp_L E K f X ==
  qpoly_eval f 0%Q - E * qpoly_eval f X + lw2_exp_L E K (qpoly_deriv f) X.
Proof.
  intros E K f X HK.
  assert (HD : (length (qpoly_deriv f) <= K)%nat).
  { eapply Nat.le_trans.
    - apply lw2_len_deriv.
    - exact HK. }
  unfold lw2_exp_L.
  rewrite (lw2_eps_deriv_point K f 0%Q), (lw2_eps_deriv_point K f X).
  rewrite (lw2_eps_deriv_kernel K f 0%Q HK), (lw2_eps_deriv_kernel K f X HK).
  ring.
Qed.

(* Q-bilinearity of the machine: additivity. *)
Lemma lw2_exp_L_add : forall E K u v X,
  lw2_exp_L E K (qpoly_add u v) X ==
  lw2_exp_L E K u X + lw2_exp_L E K v X.
Proof.
  intros E K u v X.
  unfold lw2_exp_L.
  rewrite (lw2_eps_eval_add K u v 0%Q), (lw2_eps_eval_add K u v X).
  ring.
Qed.

(* Q-bilinearity of the machine: homogeneity. *)
Lemma lw2_exp_L_scalar : forall E K c f X,
  lw2_exp_L E K (qpoly_scalar c f) X == c * lw2_exp_L E K f X.
Proof.
  intros E K c f X.
  unfold lw2_exp_L.
  rewrite (lw2_eps_eval_scalar K c f 0%Q), (lw2_eps_eval_scalar K c f X).
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 4.  The explicit closed form (endpoint value combination).  *)
(* ------------------------------------------------------------------ *)

(* The closed form: the functional is the explicit combination of the       *)
(* truncated antiderivative endpoint values  sum_{k<K} f^{(k)}(0)           *)
(* - E * sum_{k<K} f^{(k)}(X).  With K := length f this is a finite         *)
(* rational expression in the derivatives of f at the two endpoints; the    *)
(* exponential suppression of the far endpoint is carried entirely by the   *)
(* explicit scalar E, with no limiting construction anywhere.               *)
Lemma lw2_exp_L_closed_form : forall E K f X,
  lw2_exp_L E K f X ==
  lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) 0%Q) K
  - E * lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) X) K.
Proof.
  intros E K f X.
  unfold lw2_exp_L.
  rewrite (lw2_eps_eval_sum K f 0%Q), (lw2_eps_eval_sum K f X).
  reflexivity.
Qed.

Print Assumptions lw2_exp_L.
Print Assumptions lw2_exp_int_parts.
Print Assumptions lw2_exp_L_nil.
Print Assumptions lw2_exp_L_fuel.
Print Assumptions lw2_exp_L_add.
Print Assumptions lw2_exp_L_scalar.
Print Assumptions lw2_exp_L_closed_form.
Print Assumptions lw2_eps_deriv_point.

From Stdlib Require Import Extraction.
Separate Extraction lw2_exp_L lw2_exp_int_parts lw2_exp_L_closed_form
  lw2_exp_L_fuel lw2_exp_L_add lw2_exp_L_scalar lw2_exp_L_nil
  lw2_eps_deriv_point lw2_eps_eval_add lw2_eps_eval_scalar.
