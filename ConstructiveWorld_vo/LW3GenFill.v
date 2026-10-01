(* LW3GenFill.v                                                        *)
(* 使命：lw381_joint_target 的 general-p 填装——把 384 锚例（p=[1;1] 双尺度  *)
(*       sigT 填装）升格为一般 p 的条件形：逐节点界族经 384 吸收路线一般化  *)
(*       （单点绝对值≤逐节点全和，对任意多项式成立），加权总和对缩放家族    *)
(*       分解为「未缩放侧增长量 B(p,N) × 阶乘倒数」，m 门槛＝显式数据前件   *)
(*       QltT (B p N) (q_fact m)，配 λ 面三推论（缩放侧上界、条件严格小于   *)
(*       一、未缩放侧以 B 为无条件的界）与锚例双尺度回归填装。              *)
(* 依赖：_tlw381_famscale（v c74d6b6b，承载形与 nodewsum/wsum/pnode_fam/    *)
(*       joint_target 正本名面）、_tlw384_fill（vo 2f02066b，pt_le_nodewsum  *)
(*       吸收件）、_tlw384_vtsum（vo 9aba7ed7，lambda_upper_nodes_vt 主件）、*)
(*       _tlw387_dual（vo 13079ff4，deriv_iter_eval_scalar 与 bridge 系）；  *)
(*       库内承件 lw2_qsum0_scale／lw2_qsum0_ext／QleT'／QltT 桥系／        *)
(*       Qmult_lt_compat_r／Qmult_inv_r／Qinv_lt_0_compat／Qabs_pos／       *)
(*       lw0_q_fact_ge_one。Require 顺序令 _tlw381_famscale 后入，正本名    *)
(*       面胜出（384/387 自足复刻副本让位，防遮蔽）。                       *)
(* 对标：E-STAGING-LW0-NOEVALIFT（检索索引 L1860：对偶换算全走系数级在件    *)
(*       引理与求值-系数桥，零 eval 级拼装）；E-STAGING-LW3-PROBEPIN        *)
(*       （检索索引 L1766：锚例回归钉走透明归约路径）；attn\_tlw381 记录     *)
(*       §三.2 承载形、attn\_tlw384 记录吸收路线（member_abs_le＋pt_le_      *)
(*       nodewsum）、attn\_tlw387 记录对偶件与一般 m 桥。                   *)
(* 构造性：语句面全 Set——前提位仅 QltT/QleT' 数据判定与 nat le/lt，结论面   *)
(*       sigT＋And＋QltT（381 在件同面）；零假设承载位、零新增命题语句；    *)
(*       锚例回归钉走 Qeq_bool match 形（381 同批工艺）；提取并集仅数据名   *)
(*       四件（同 381 四名）。                                              *)
(* 编译配方：coqc 全路径 -q -Q . "" -Q ConstructiveWorld-Main/              *)
(*       ConstructiveWorld_vo ""，cpu_guard 包裹，SW2 双 export 全字面。    *)
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
Require Import LW3DualBridge.
Require Import LW3JointFill.
Require Import LW3VarTSumBound.
Require Import LW3FamScale.
(* LW1ZPoly opens Z_scope at file level and the open leaks through the      *)
(* Require chain, so the bare product default lands on Z.mul; reopen the    *)
(* rational scope for this file.  Every nat/Z arithmetic occurrence in      *)
(* this file carries an explicit scope annotation, so no reading changes.   *)
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Section 1.  Scalar linearity of the per-node full sum.              *)
(* ------------------------------------------------------------------ *)

(* The scalar recursion preserves the length of a polynomial: the build    *)
(* copies one entry per step, so the two lengths advance together.         *)
Lemma lw391_length_scalar : forall (a : Q) (f : QPoly),
  (length (qpoly_scalar a f) = length f)%nat.
Proof.
  intros a f. induction f as [| b f IH].
  - reflexivity.
  - cbn [qpoly_scalar length]. rewrite IH. reflexivity.
Qed.

(* The factorial rank is strictly positive, so the scale constant is       *)
(* strictly positive as well.                                              *)
Lemma lw391_qfact_pos : forall (m : nat), Qlt (0#1)%Q (q_fact m).
Proof.
  intro m. apply (Qlt_le_trans (0#1)%Q (1#1)%Q (q_fact m)).
  - apply QltT_to_Qlt. apply qltT_0_1.
  - apply QleT'_to_Qle. apply lw0_q_fact_ge_one.
Qed.

(* The per-node full sum is linear in the scalar, in absolute-value form:  *)
(* differentiating passes through the scalar at every order, and the       *)
(* absolute value of a product splits into the product of absolute values. *)
Lemma lw391_nodewsum_scalar : forall (a : Q) (f : QPoly) (j : nat),
  lw381_nodewsum (qpoly_scalar a f) j == (Qabs a * lw381_nodewsum f j)%Q.
Proof.
  intros a f j. unfold lw381_nodewsum.
  rewrite lw391_length_scalar.
  rewrite <- (lw2_qsum0_scale (length f)
    (fun k => Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))) (Qabs a)).
  apply lw2_qsum0_ext. intros k Hk.
  rewrite lw387_deriv_iter_eval_scalar.
  rewrite Qabs_Qmult. reflexivity.
Qed.

(* The node-summed form of the same linearity: summing the per-node full   *)
(* sums of the scaled family yields the scale constant times the sum over  *)
(* the unscaled family.                                                    *)
Lemma lw391_nodewsum_sum_scalar : forall (a : Q) (f : QPoly) (n : nat),
  lw2_qsum0 (fun j => lw381_nodewsum (qpoly_scalar a f) j) n ==
  (Qabs a * lw2_qsum0 (fun j => lw381_nodewsum f j) n)%Q.
Proof.
  intros a f n.
  rewrite <- (lw2_qsum0_scale n (fun j => lw381_nodewsum f j) (Qabs a)).
  apply lw2_qsum0_ext. intros j Hj. apply lw391_nodewsum_scalar.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 2.  The weighted total of the scaled family decomposes into  *)
(* the unscaled growth quantity times the factorial reciprocal.         *)
(* ------------------------------------------------------------------ *)

(* The growth quantity of the family at p and N: the order count of the    *)
(* unscaled build times the node-summed bound over the node grid.          *)
Definition lw391_wsum_unscaled (p : zpoly) (N : nat) : Q :=
  lw0_q_of_nat (length (lw3_fbuild p (lw3_deg p) N)) *
  lw2_qsum0 (fun j => lw381_nodewsum (lw3_fbuild p (lw3_deg p) N) j)
            (Datatypes.S (Datatypes.S (lw3_nodecount p N))).

(* Decomposition: weighting the per-node full sums of the scaled family    *)
(* equals the growth quantity times the factorial reciprocal.              *)
Lemma lw391_wsum_scaled_decomp : forall (p : zpoly) (N m : nat),
  lw381_wsum p N m (fun j => lw381_nodewsum (lw381_fbuild_scaled p (lw3_deg p) N m) j) ==
  (lw391_wsum_unscaled p N * lw381_scale_const m)%Q.
Proof.
  intros p N m.
  unfold lw381_wsum, lw391_wsum_unscaled, lw381_fbuild_scaled. cbv beta.
  rewrite lw391_length_scalar.
  rewrite lw391_nodewsum_sum_scalar.
  assert (Hab : Qabs (lw381_scale_const m) == lw381_scale_const m).
  { unfold lw381_scale_const. apply Qabs_pos.
    apply Qlt_le_weak. apply Qinv_lt_0_compat. apply lw391_qfact_pos. }
  rewrite Hab. ring.
Qed.

(* Conditional strict reversal of the weighted total: once the growth      *)
(* quantity falls below the rank-m factorial, the weighted total of the    *)
(* scaled family falls below one.                                          *)
Theorem lw391_wsum_lt1_cond : forall (p : zpoly) (N m : nat),
  QltT (lw391_wsum_unscaled p N) (q_fact m) ->
  QltT (lw381_wsum p N m (fun j => lw381_nodewsum (lw381_fbuild_scaled p (lw3_deg p) N m) j))
       (1#1)%Q.
Proof.
  intros p N m Hcond.
  assert (Hpos : Qlt (0#1)%Q (q_fact m)) by apply lw391_qfact_pos.
  apply Qlt_to_QltT.
  rewrite lw391_wsum_scaled_decomp.
  assert (Hinv : q_fact m * lw381_scale_const m == (1#1)%Q).
  { unfold lw381_scale_const. apply Qmult_inv_r. intro Heq. symmetry in Heq.
    exact (Qlt_not_eq (0#1)%Q (q_fact m) Hpos Heq). }
  rewrite <- Hinv.
  apply (Qmult_lt_compat_r (lw391_wsum_unscaled p N) (q_fact m) (lw381_scale_const m)).
  - unfold lw381_scale_const. apply Qinv_lt_0_compat. exact Hpos.
  - apply QltT_to_Qlt. exact Hcond.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 3.  The general-p fill of the joint target.                 *)
(* ------------------------------------------------------------------ *)

(* The per-node bound premise in general form: any family dominating the   *)
(* per-node full sums of the scaled build covers every derivative value at *)
(* every node (the absorption route, rank-general).                        *)
Lemma lw391_pnode_fam_gen : forall (p : zpoly) (N m : nat) (Ef : nat -> Q),
  (forall (j : nat), Nat.le j (Datatypes.S (lw3_nodecount p N)) ->
     QleT' (lw381_nodewsum (lw381_fbuild_scaled p (lw3_deg p) N m) j) (Ef j)) ->
  lw381_pnode_fam p N m Ef.
Proof.
  intros p N m Ef H j k Hj Hk.
  apply (qleT'_trans _ (lw381_nodewsum (lw381_fbuild_scaled p (lw3_deg p) N m) j)).
  - apply (lw384_pt_le_nodewsum (lw381_fbuild_scaled p (lw3_deg p) N m) j k Hk).
  - apply H. exact Hj.
Qed.

(* The general-p fill: the joint target holds at every source polynomial   *)
(* and every rank, conditional on the growth quantity staying below the    *)
(* factorial of the chosen rank.                                           *)
Theorem lw391_joint_gen : forall (p : zpoly) (N m : nat),
  QltT (lw391_wsum_unscaled p N) (q_fact m) ->
  lw381_joint_target p N m.
Proof.
  intros p N m Hcond.
  exists (fun j => lw381_nodewsum (lw381_fbuild_scaled p (lw3_deg p) N m) j).
  split.
  - intros j k Hj Hk.
    exact (lw384_pt_le_nodewsum (lw381_fbuild_scaled p (lw3_deg p) N m) j k Hk).
  - exact (lw391_wsum_lt1_cond p N m Hcond).
Qed.

(* ------------------------------------------------------------------ *)
(* Section 4.  The functional-value face: upper bounds and the         *)
(* conditional strict reversal.                                        *)
(* ------------------------------------------------------------------ *)

(* The functional value of the scaled family is covered by its weighted    *)
(* total at every source polynomial, rank and scale.                       *)
Corollary lw391_lambda_upper_scaled : forall (p : zpoly) (N m : nat),
  QleT' (Qabs (lw2_lambda (lw3_nodecount p N) (lw381_fbuild_scaled p (lw3_deg p) N m)))
        (lw381_wsum p N m (fun j => lw381_nodewsum (lw381_fbuild_scaled p (lw3_deg p) N m) j)).
Proof.
  intros p N m. unfold lw381_wsum. cbv beta.
  apply (lw384_lambda_upper_nodes_vt (lw3_nodecount p N)
          (lw381_fbuild_scaled p (lw3_deg p) N m)
          (fun j => lw381_nodewsum (lw381_fbuild_scaled p (lw3_deg p) N m) j)).
  intros j k Hj Hk. apply (lw384_pt_le_nodewsum _ j k Hk).
Qed.

(* Conditional strict reversal on the functional-value face: under the     *)
(* same rank threshold, the absolute functional value of the scaled family *)
(* falls below one.                                                        *)
Corollary lw391_lambda_lt1_cond : forall (p : zpoly) (N m : nat),
  QltT (lw391_wsum_unscaled p N) (q_fact m) ->
  QltT (Qabs (lw2_lambda (lw3_nodecount p N) (lw381_fbuild_scaled p (lw3_deg p) N m)))
       (1#1)%Q.
Proof.
  intros p N m Hcond. apply Qlt_to_QltT.
  apply (Qle_lt_trans _
          (lw381_wsum p N m (fun j => lw381_nodewsum (lw381_fbuild_scaled p (lw3_deg p) N m) j))).
  - apply QleT'_to_Qle. apply lw391_lambda_upper_scaled.
  - apply QltT_to_Qlt. apply lw391_wsum_lt1_cond. exact Hcond.
Qed.

(* The unscaled functional value is covered by the growth quantity itself, *)
(* unconditionally in the rank: the scaled value at rank zero carries the  *)
(* unscaled family back, and the factorial reciprocal is one there.        *)
Corollary lw391_lambda_upper_unscaled : forall (p : zpoly) (N : nat),
  QleT' (Qabs (lw2_lambda (lw3_nodecount p N) (lw3_fbuild p (lw3_deg p) N)))
        (lw391_wsum_unscaled p N).
Proof.
  intros p N.
  assert (Hq0 : q_fact 0 == (1#1)%Q) by reflexivity.
  assert (Hlu : lw2_lambda (lw3_nodecount p N) (lw3_fbuild p (lw3_deg p) N) ==
                lw2_lambda (lw3_nodecount p N)
                           (lw381_fbuild_scaled p (lw3_deg p) N 0)).
  { rewrite <- (lw387_bridge_scaled_gen p (lw3_deg p) N 0 (lw3_nodecount p N)).
    rewrite Hq0. apply Qmult_1_l. }
  assert (Hmid : lw381_wsum p N 0
           (fun j => lw381_nodewsum (lw381_fbuild_scaled p (lw3_deg p) N 0) j) ==
                 (lw391_wsum_unscaled p N)).
  { rewrite lw391_wsum_scaled_decomp.
    assert (Hs0 : lw381_scale_const 0 == (1#1)%Q) by reflexivity.
    rewrite Hs0. apply Qmult_1_r. }
  assert (Hstep1 : QleT' (Qabs (lw2_lambda (lw3_nodecount p N)
                            (lw3_fbuild p (lw3_deg p) N)))
                    (lw381_wsum p N 0
                      (fun j => lw381_nodewsum (lw381_fbuild_scaled p (lw3_deg p) N 0) j))).
  { apply (lw2u_qleT'_eq_l _ (Qabs (lw2_lambda (lw3_nodecount p N)
              (lw381_fbuild_scaled p (lw3_deg p) N 0)))).
    - apply (lw391_lambda_upper_scaled p N 0).
    - apply (lw3_Qabs_congr _ _ Hlu). }
  exact (lw2u_qleT'_eq_r _ _ _ Hstep1 Hmid).
Qed.

(* ------------------------------------------------------------------ *)
(* Section 5.  Anchor regression at the two certified scales.          *)
(* ------------------------------------------------------------------ *)

(* Growth quantity at scale one equals 2452: the per-node full sums of the *)
(* unscaled build sum to 613 and the order count is 4.                     *)
Definition lw391_cond_val1 :
  match Qeq_bool (lw391_wsum_unscaled p381 N1_381) (2452 # 1)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

(* Growth quantity at scale zero equals 102.                               *)
Definition lw391_cond_val0 :
  match Qeq_bool (lw391_wsum_unscaled p381 N0_381) (102 # 1)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

(* The general fill specializes to the certified anchor at scale one.      *)
Corollary lw391_anchor_fill1 : lw381_joint_target p381 N1_381 m381.
Proof. apply (lw391_joint_gen p381 N1_381 m381). vm_compute. constructor. Qed.

(* The general fill specializes to the certified anchor at scale zero.     *)
Corollary lw391_anchor_fill0 : lw381_joint_target p381 N0_381 m381.
Proof. apply (lw391_joint_gen p381 N0_381 m381). vm_compute. constructor. Qed.

Print Assumptions lw391_length_scalar.
Print Assumptions lw391_qfact_pos.
Print Assumptions lw391_nodewsum_scalar.
Print Assumptions lw391_nodewsum_sum_scalar.
Print Assumptions lw391_wsum_unscaled.
Print Assumptions lw391_wsum_scaled_decomp.
Print Assumptions lw391_wsum_lt1_cond.
Print Assumptions lw391_pnode_fam_gen.
Print Assumptions lw391_joint_gen.
Print Assumptions lw391_lambda_upper_scaled.
Print Assumptions lw391_lambda_lt1_cond.
Print Assumptions lw391_lambda_upper_unscaled.
Print Assumptions lw391_cond_val1.
Print Assumptions lw391_cond_val0.
Print Assumptions lw391_anchor_fill1.
Print Assumptions lw391_anchor_fill0.

From Stdlib Require Import Extraction.
Separate Extraction p381 m381 n1_381 n0_381.
