(* LW3DualBridge.v                                                           *)
(* 使命：M3 变体线缺供双件——其一 k 迭代对偶引理（381 缺供 a：任意阶求导穿过  *)
(*       标量算子的求值面恒等，一般 k 与一般标量的 Qeq 一般形，覆盖 381      *)
(*       k=1 件为其一阶特例）；其二 λ 标量线性一般形（381 缺供 d：对任意     *)
(*       标量 c 有 λ(c·f)==c·λ(f)，并落缩放桥一般形 q_fact m·λ(f_s)==λ(f)    *)
(*       的一般 m 版与锚例两尺度实例，将 381 的 -265/-15 双尺度值钉升格为    *)
(*       一般恒等引理）。                                                    *)
(* 依赖：LW3ETranscendental（只读正本）及其 Require 闭包 S02/S03/LW0/        *)
(*       LW1/LW2 系；库内承件 lw0_coef_iter_scalar（LW2Hermite 一般 k 系数    *)
(*       面对偶在件）、lw2_eval_coef_sum（求值-系数和桥）、lw2_qsum0_ext、   *)
(*       lw2_qsum0_scale、lw2_qsum0_extend、lw0_coef_beyond、               *)
(*       lw0_q_fact_ge_one；锚例面自 _tlw381_famscale 逐字复刻（v c74d6b6b， *)
(*       vo 1f0dd529，384 同批自足工艺，381 件只读）。                       *)
(* 对标：E-STAGING-LW0-NOEVALIFT（检索索引 L1860：多项式级改写走系数级载体， *)
(*       本件对偶恒等经系数面在件引理与求值-系数和桥合成，零 eval 级拼装）； *)
(*       E-STAGING-LW3-PROBEPIN（检索索引 L1766：值钉透明归约路径）；        *)
(*       attn\_tlw381 记录缺供清单 a/d 两项与三路线勘形；attn\_tlw384 记录    *)
(*       红发记录（Qeq 点wise 目标先归约再 ring 的乘数顺序坑）。             *)
(* 构造性：语句面全 Qeq 等式形与 nat le 数据判定前提（381/384 在件同面），   *)
(*       零 Prop 语句新增、零前提承载位、零假设承载；值钉走 Qeq_bool         *)
(*       match 形（381 同批工艺）；提取并集仅数据名四件（同 381 四名）。     *)
(* 编译配方：coqc 全路径 -q -Q . "" -Q ConstructiveWorld-Main/               *)
(*       ConstructiveWorld_vo ""，cpu_guard 包裹，SW2 双 export 全字面。     *)
Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import QArith_base.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW1ZPoly.
Require Import LW2Hermite.
Require Import LW2IntegMachine.
Require Import LW0FactGrowth.
Require Import LW2UpperBound.
Require Import LW2NivenInt.
Require Import LW3ETranscendental.
(* LW1ZPoly opens Z_scope at file level and the open leaks through the      *)
(* Require chain, so the bare product default lands on Z.mul; reopen the    *)
(* rational scope for this file.  Every nat/Z arithmetic occurrence in      *)
(* this file carries an explicit scope annotation, so no reading changes.   *)
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Section 0.  The 381 anchor faces, replicated verbatim (self-        *)
(* contained sandbox style, per the 384 precedent).                    *)
(* ------------------------------------------------------------------ *)

(* The anchor source polynomial one plus t.                                *)
Definition p381 : zpoly := cons 1%Z (cons 1%Z nil).

(* The two explicit scales of the joint accounting: one and zero.         *)
Definition N1_381 : nat := 1.
Definition N0_381 : nat := 0.

(* The rank of the factorial-reciprocal scale constant.                   *)
Definition m381 : nat := 7.

(* The factorial-reciprocal scale constant at rank m.                     *)
Definition lw381_scale_const (m : nat) : Q := / (q_fact m)%Q.

(* The scaled family face: the built integrand under the factorial-       *)
(* reciprocal scalar.                                                     *)
Definition lw381_fbuild_scaled (p : zpoly) (sg N m : nat) : QPoly :=
  qpoly_scalar (lw381_scale_const m) (lw3_fbuild p sg N).

(* The node counts and family instances at both scales.                   *)
Definition n1_381 : nat := lw3_nodecount p381 N1_381.
Definition n0_381 : nat := lw3_nodecount p381 N0_381.
Definition f1_381 : QPoly := lw381_fbuild_scaled p381 (lw3_deg p381) N1_381 m381.
Definition f0_381 : QPoly := lw381_fbuild_scaled p381 (lw3_deg p381) N0_381 m381.

(* ------------------------------------------------------------------ *)
(* Section 1.  Missing supply (a): the iterated-derivative duality.    *)
(* Differentiation of every order passes through the scalar operator,  *)
(* so each order-k derivative value of the scaled family is the scale  *)
(* constant times the unscaled one.  The coefficient-face general-k    *)
(* law is already in the library (lw0_coef_iter_scalar); the eval      *)
(* face follows through the evaluation-as-coefficient-sum bridge over  *)
(* a common bound, so no length-alignment law and no zero-tail law     *)
(* are needed beyond the library extend lemma.                         *)
(* ------------------------------------------------------------------ *)

(* Evaluation equals the coefficient-power sum over any upper bound.  *)
Lemma lw387_eval_coef_sum_bound : forall (L : nat) (p : QPoly) (x : Q),
  (length p <= L)%nat ->
  qpoly_eval p x ==
  lw2_qsum0 (fun j => lw0_coef j p * lw2_qpow x j) L.
Proof.
  intros L p x HL.
  rewrite (lw2_eval_coef_sum p x).
  symmetry.
  apply lw2_qsum0_extend.
  - exact HL.
  - intros j H1 H2.
    rewrite (lw0_coef_beyond j p H1).
    ring.
Qed.

(* The iterated-derivative duality: differentiation of every order k    *)
(* passes through the scalar at every evaluation point.                 *)
Lemma lw387_deriv_iter_eval_scalar : forall (k : nat) (a : Q) (p : QPoly) (x : Q),
  qpoly_eval (qpoly_deriv_iter k (qpoly_scalar a p)) x ==
  (a * qpoly_eval (qpoly_deriv_iter k p) x)%Q.
Proof.
  intros k a p x.
  rewrite (lw387_eval_coef_sum_bound
             (length (qpoly_deriv_iter k (qpoly_scalar a p)) +
              length (qpoly_deriv_iter k p))%nat
             (qpoly_deriv_iter k (qpoly_scalar a p)) x).
  - rewrite (lw387_eval_coef_sum_bound
               (length (qpoly_deriv_iter k (qpoly_scalar a p)) +
                length (qpoly_deriv_iter k p))%nat
               (qpoly_deriv_iter k p) x).
    + rewrite (lw2_qsum0_ext
                 (length (qpoly_deriv_iter k (qpoly_scalar a p)) +
                  length (qpoly_deriv_iter k p))%nat
                 (fun j => lw0_coef j (qpoly_deriv_iter k (qpoly_scalar a p)) *
                           lw2_qpow x j)
                 (fun j => a * (lw0_coef j (qpoly_deriv_iter k p) *
                                lw2_qpow x j))).
      * rewrite (lw2_qsum0_scale
                   (length (qpoly_deriv_iter k (qpoly_scalar a p)) +
                    length (qpoly_deriv_iter k p))%nat
                   (fun j => lw0_coef j (qpoly_deriv_iter k p) * lw2_qpow x j)
                   a).
        reflexivity.
      * intros j Hj.
        rewrite lw0_coef_iter_scalar.
        ring.
    + lia.
  - lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 2.  Missing supply (d): the scalar linearity of the node    *)
(* functional lambda, in general form.                                 *)
(* ------------------------------------------------------------------ *)

(* The node functional is linear in the polynomial under any scalar:    *)
(* lambda of the scaled polynomial equals the scalar times lambda.      *)
Lemma lw387_lambda_scalar : forall (n : nat) (c : Q) (f : QPoly),
  lw2_lambda n (qpoly_scalar c f) == (c * lw2_lambda n f)%Q.
Proof.
  intros n c f.
  assert (Hlen : (length (qpoly_scalar c f) = length f)%nat).
  { induction f as [|b f IH].
    - reflexivity.
    - cbn [qpoly_scalar length]. rewrite IH. reflexivity. }
  unfold lw2_lambda.
  rewrite Hlen.
  rewrite (lw2_qsum0_ext
             (Datatypes.S (Datatypes.S n))
             (fun j => lw2_qsum0
                         (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
                            qpoly_eval (qpoly_deriv_iter k (qpoly_scalar c f))
                                       (lw2_node j))
                         (length f))
             (fun j => c * lw2_qsum0
                         (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
                            qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
                         (length f))).
  - rewrite (lw2_qsum0_scale
               (Datatypes.S (Datatypes.S n))
               (fun j => lw2_qsum0
                           (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
                              qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
                           (length f)) c).
    reflexivity.
  - intros j Hj.
    rewrite (lw2_qsum0_ext
               (length f)
               (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
                  qpoly_eval (qpoly_deriv_iter k (qpoly_scalar c f))
                             (lw2_node j))
               (fun k => c * (((lw2_lambda_coef n j k) # 1)%Q *
                  qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))).
    + rewrite (lw2_qsum0_scale (length f)
                 (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
                    qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) c).
      reflexivity.
    + intros k Hk.
      rewrite lw387_deriv_iter_eval_scalar.
      ring.
Qed.

(* The scaled-family bridge in general rank form: multiplying the node  *)
(* functional value of the factorial-reciprocal scaled family by the    *)
(* rank-m factorial restores the unscaled functional value, for every   *)
(* family instance and every scale rank.                                *)
Lemma lw387_bridge_scaled_gen : forall (p : zpoly) (sg N m n : nat),
  ((q_fact m)%Q * lw2_lambda n (lw381_fbuild_scaled p sg N m) ==
   lw2_lambda n (lw3_fbuild p sg N))%Q.
Proof.
  intros p sg N m n.
  unfold lw381_fbuild_scaled, lw381_scale_const.
  rewrite lw387_lambda_scalar.
  rewrite Qmult_assoc.
  rewrite (Qmult_inv_r (q_fact m)).
  - rewrite Qmult_1_l. reflexivity.
  - assert (Hge : QleT' 1 (q_fact m)) by apply lw0_q_fact_ge_one.
    apply QleT'_to_Qle in Hge.
    intro H0.
    rewrite H0 in Hge.
    unfold Qle in Hge.
    cbn in Hge.
    lia.
Qed.

(* The bridge at the anchor instance, scale one: the general rank form  *)
(* specialized to the rank-seven scaled family at scale one.            *)
Corollary lw387_bridge1_gen : ((q_fact m381)%Q * lw2_lambda n1_381 f1_381 ==
   lw2_lambda n1_381 (lw3_fbuild p381 (lw3_deg p381) N1_381))%Q.
Proof. exact (lw387_bridge_scaled_gen p381 (lw3_deg p381) N1_381 m381 n1_381). Qed.

(* The bridge at the anchor instance, scale zero.                       *)
Corollary lw387_bridge0_gen : ((q_fact m381)%Q * lw2_lambda n0_381 f0_381 ==
   lw2_lambda n0_381 (lw3_fbuild p381 (lw3_deg p381) N0_381))%Q.
Proof. exact (lw387_bridge_scaled_gen p381 (lw3_deg p381) N0_381 m381 n0_381). Qed.

(* ------------------------------------------------------------------ *)
(* Section 3.  A third-scale numeric witness.                          *)
(* ------------------------------------------------------------------ *)

(* A numeric witness at a fresh scale constant three, beyond the two    *)
(* anchor scales of the 381 batch: the node functional value of the     *)
(* triple-scaled family is three times the scaled value, that is        *)
(* minus seven hundred ninety five over five thousand forty.            *)
Definition lw387_lam3s_val :
  match Qeq_bool (lw2_lambda n1_381 (qpoly_scalar (3 # 1)%Q f1_381))
                 ((-795) # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Print Assumptions lw387_eval_coef_sum_bound.
Print Assumptions lw387_deriv_iter_eval_scalar.
Print Assumptions lw387_lambda_scalar.
Print Assumptions lw387_bridge_scaled_gen.
Print Assumptions lw387_bridge1_gen.
Print Assumptions lw387_bridge0_gen.
Print Assumptions lw387_lam3s_val.

From Stdlib Require Import Extraction.
Separate Extraction p381 m381 n1_381 n0_381.
