(* 模块：b1_kernel_pointwise.v —— arctan 核逐点衰减界（有理短证书双档）。
   使命：Beukers-arctan 单积分核 x(1−x)/(1+x²) 于 [0,1] 的逐点支配面。
   勘形画像①原文给 (√2−1)/2（无理，不可作 Q 证书）；本件按 ζ(2) 锐化线
   「有理短证书改写」工艺选定两档有理证书（完全平方判别式证书，全 x 无条件）：
     档一 θ₄ = 1/4 ：5·((1+x²)−4x(1−x)) = (5x−2)²+1 ≥ 1；
     档二 θ₂₄ = 5/24 ：29·((5(1+x²))−24x(1−x)) = (29x−12)²+1 ≥ 1。
   配幂次抬升（q_pow_mono）与正性肢（B3 见证先例·正性肢配方迁移）。
   真实 sup = 6/29（x = 2/5，锚二）与 5/24 = 0.20833… 空隙 0.6% 级，
   如实登记（后续如需可再锐化，不构成本件义务）。
   依赖：S01_BaseRing、S02_CauchyComplete（QltT/QeqT/QleT' 桥）、S03_QExp
   （q_pow 与 q_pow_mono）；Stdlib QArith/Qabs/Qfield（ring 通路）。
   构造性：语句面全 Set（QltT/QeqT/QleT'）；证明体直链 Q 算术，ring 只入
   等式证书位；零公理、零经典逻辑、零 solver 收尾于主语句。
   编译配方：source Live/toolchain/env.sh 后经 cpu_guard 包裹
   rocq c -native-compiler no -q -Q . "" b1_kernel_pointwise.v。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith Arith.Arith.
From Stdlib Require Import Setoid Morphisms Qfield.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.

Open Scope Q_scope.

(* ========== §0 微工具箱（全名逐一 REPL 验证过的 stdlib/S02 桥） ========== *)

(* QleT 降 Qle（QleT = Or QltT (Id x y)，S02 无现成降桥，自携） *)
Lemma b1_qleT_imp_qle : forall x y : Q, QleT x y -> Qle x y.
Proof.
  intros x y H. destruct H as [Hlt | Heq].
  - exact (Qlt_le_weak _ _ (QltT_to_Qlt _ _ Hlt)).
  - rewrite Heq. apply Qle_refl.
Qed.

(* x ≤ 1 ⟹ 0 ≤ 1−x *)
Lemma b1_sub_ge0 : forall x : Q, QleT' x 1 -> Qle 0 (1 - x).
Proof.
  intros x Hx1.
  setoid_replace (1 - x)%Q with ((- x) + 1)%Q by ring.
  replace 0%Q with ((-1) + 1)%Q by reflexivity.
  apply (Qplus_le_compat (-1) (- x) 1 1).
  - exact (Qopp_le_compat x 1 (QleT'_to_Qle _ _ Hx1)).
  - apply Qle_refl.
Qed.

(* 0 < 1（计算判定） *)
Lemma b1_0lt1 : Qlt 0 1.
Proof. unfold Qlt. reflexivity. Qed.

(* 正数倒数仍正 *)
Lemma b1_inv_pos : forall D : Q, Qlt 0 D -> Qlt 0 (/ D).
Proof. intros D HD. apply Qinv_lt_0_compat. exact HD. Qed.

(* Z 层平方非负（Q 层平方非负的承重件） *)
Lemma b1_zsq_nonneg : forall z : Z, (0 <= z * z)%Z.
Proof.
  intro z. unfold Z.le. destruct z as [| p | p].
  - cbn. intro Hc. discriminate Hc.
  - cbn. exact (Zle_0_pos (p * p)).
  - cbn. exact (Zle_0_pos (p * p)).
Qed.

(* Q 平方非负（两档证书的公共承重）：Qle 展开为 Z 交叉积比较直读 *)
Lemma b1_qsq_nonneg : forall z : Q, Qle 0 (z * z).
Proof.
  intro z. unfold Qle, Qmult, Qnum, Qden, Qinv, Qminus. simpl.
  destruct z as [zn zd]. cbn.
  rewrite Z.mul_1_r.
  exact (b1_zsq_nonneg zn).
Qed.

(* 1 + x² > 0（无条件） *)
Lemma b1_den_pos : forall x : Q, Qlt 0 (1 + x * x).
Proof.
  intro x. apply (Qlt_le_trans 0 1 (1 + x * x)).
  - exact b1_0lt1.
  - assert (H1 : Qle (1 + 0) (1 + x * x))
      by (apply (proj2 (Qplus_le_r 0 (x * x) 1)); apply b1_qsq_nonneg).
    replace (1 + 0)%Q with 1%Q in H1 by reflexivity.
    exact H1.
Qed.

(* z² + 1 > 0 与 1 ≤ z² + 1 *)
Lemma b1_qsq_plus1_pos : forall z : Q, Qlt 0 (z * z + 1).
Proof.
  intro z. apply (Qle_lt_trans 0 (z * z) (z * z + 1)).
  - apply b1_qsq_nonneg.
  - assert (H2 : Qlt (z * z + 0) (z * z + 1))
      by (apply (proj2 (Qplus_lt_r 0 1 (z * z))); exact b1_0lt1).
    setoid_replace (z * z + 0)%Q with (z * z)%Q in H2 by ring.
    exact H2.
Qed.

Lemma b1_qsq_plus1_ge1 : forall z : Q, Qle 1 (z * z + 1).
Proof.
  intro z.
  assert (H1 : Qle (1 + 0) (1 + z * z))
    by (apply (proj2 (Qplus_le_r 0 (z * z) 1)); apply b1_qsq_nonneg).
  replace (1 + 0)%Q with 1%Q in H1 by reflexivity.
  setoid_replace (1 + z * z)%Q with (z * z + 1)%Q in H1 by ring.
  exact H1.
Qed.

(* A − B > 0 ⟹ B < A *)
Lemma b1_pos_diff_lt : forall A B : Q, Qlt 0 (A - B) -> Qlt B A.
Proof.
  intros A B H. apply (proj2 (Qlt_minus_iff B A)).
  setoid_replace (A + - B)%Q with (A - B)%Q by (unfold Qminus; ring).
  exact H.
Qed.

(* 核分子非负：0 ≤ x ≤ 1 ⟹ 0 ≤ x(1−x) *)
Lemma b1_kernel_num_nonneg : forall x : Q,
  QleT 0 x -> QleT' x 1 -> Qle 0 (x * (1 - x)).
Proof.
  intros x Hx0 Hx1.
  apply (Qmult_le_0_compat x (1 - x)).
  - exact (b1_qleT_imp_qle _ _ Hx0).
  - exact (b1_sub_ge0 x Hx1).
Qed.

(* 核分子严格正：0 < x < 1 *)
Lemma b1_kernel_num_pos : forall x : Q,
  QltT 0 x -> QltT x 1 -> Qlt 0 (x * (1 - x)).
Proof.
  intros x Hx0 Hx1.
  assert (Hn : Qlt 0 (1 - x)).
  { apply (proj1 (Qlt_minus_iff x 1)). exact (QltT_to_Qlt _ _ Hx1). }
  apply Qmult_lt_0_compat.
  - exact (QltT_to_Qlt _ _ Hx0).
  - exact Hn.
Qed.

(* ========== §1 档一：θ₄ = 1/4 完全平方证书 ========== *)

(* 清分母恒等式：5·((1+x²)−4x(1−x)) = (5x−2)²+1（ring 等式证书） *)
Lemma b1_kernel_margin_eq4 : forall x : Q,
  QeqT (5 * ((1 + x * x) - 4 * (x * (1 - x))))%Q
       ((5 * x - 2) * (5 * x - 2) + 1)%Q.
Proof.
  intro x. apply qeq_imp_qeqT. ring.
Qed.

(* 逐点严格支配：4x(1−x) < 1+x²（全 x ∈ Q 无条件） *)
Theorem b1_kernel_pointwise_lt4 : forall x : Q,
  QltT (4 * (x * (1 - x))) (1 + x * x).
Proof.
  intro x.
  set (D := ((1 + x * x) - 4 * (x * (1 - x)))%Q).
  set (S := ((5 * x - 2) * (5 * x - 2) + 1)%Q).
  assert (Hme : 5 * D == S) by (apply (qeqT_imp_qeq _ _ (b1_kernel_margin_eq4 x))).
  assert (Hge : Qle 1 S) by exact (b1_qsq_plus1_ge1 (5 * x - 2)).
  (* 1·(1/5) ≤ S·(1/5) == 5·D·(1/5) == D *)
  assert (H21 : Qle (1 * (1 # 5)) (S * (1 # 5))).
  { apply (Qmult_le_compat_r 1 S (1 # 5)).
    - exact Hge.
    - apply Qlt_le_weak. exact b1_0lt1. }
  setoid_replace (1 * (1 # 5))%Q with (1 # 5)%Q in H21 by ring.
  rewrite <- Hme in H21.
  setoid_replace (5 * D * (1 # 5))%Q with D%Q in H21 by ring.
  assert (HD : Qlt 0 D).
  { apply (Qlt_le_trans 0 (1 # 5) D). - exact b1_0lt1. - exact H21. }
  apply Qlt_to_QltT.
  exact (b1_pos_diff_lt (1 + x * x) (4 * (x * (1 - x))) HD).
Qed.

(* 档一比值面：0 ≤ x ≤ 1 ⟹ x(1−x)/(1+x²) ≤ 1/4 *)
Theorem b1_kernel_ratio_le4 : forall x : Q,
  QleT 0 x -> QleT' x 1 ->
  QleT' ((x * (1 - x)) / (1 + x * x)) (1 # 4).
Proof.
  intros x Hx0 Hx1.
  pose proof (b1_den_pos x) as Hden.
  pose proof (QltT_to_Qlt _ _ (b1_kernel_pointwise_lt4 x)) as Hpt.
  (* 4·num < den ⟹ num ≤ den·(1/4) *)
  assert (Hstep1 : Qle (x * (1 - x)) ((1 + x * x) * (1 # 4))).
  { pose proof (Qmult_le_compat_r (4 * (x * (1 - x))) (1 + x * x) (1 # 4)
                  (Qlt_le_weak _ _ Hpt) (Qlt_le_weak _ _ b1_0lt1)) as H1.
    setoid_replace ((4 * (x * (1 - x))) * (1 # 4))%Q with (x * (1 - x))%Q in H1 by ring.
    exact H1. }
  (* 倒数归约：(den·(1/4))·(/den) == 1/4（倒数原子化后 ring 折叠） *)
  assert (Hcol : ((1 + x * x) * (1 # 4)) * (/ (1 + x * x)) == (1 # 4)).
  { remember (/ (1 + x * x)) as u eqn:Eu.
    assert (Hid : (1 + x * x) * u == 1).
    { subst u. apply Qmult_inv_r.
      intro Hc. apply (Qlt_not_eq 0 (1 + x * x) Hden).
      apply (Qeq_sym (1 + x * x) 0). exact Hc. }
    setoid_replace (((1 + x * x) * (1 # 4)) * u)%Q
      with ((1 # 4) * ((1 + x * x) * u))%Q by ring.
    rewrite Hid. apply Qmult_1_r. }
  apply Qle_to_QleT'.
  setoid_replace ((x * (1 - x)) / (1 + x * x))%Q
    with ((x * (1 - x)) * (/ (1 + x * x)))%Q by reflexivity.
  rewrite <- Hcol.
  apply (Qmult_le_compat_r (x * (1 - x)) ((1 + x * x) * (1 # 4)) (/ (1 + x * x)) Hstep1).
  apply Qlt_le_weak. apply (b1_inv_pos (1 + x * x)). exact Hden.
Qed.

(* ========== §2 档二：θ₂₄ = 5/24 有理短证书（锐化档） ========== *)

Lemma b1_kernel_margin_eq24 : forall x : Q,
  QeqT (29 * ((5 * (1 + x * x)) - 24 * (x * (1 - x))))%Q
       ((29 * x - 12) * (29 * x - 12) + 1)%Q.
Proof.
  intro x. apply qeq_imp_qeqT. ring.
Qed.

Theorem b1_kernel_pointwise_lt24 : forall x : Q,
  QltT (24 * (x * (1 - x))) (5 * (1 + x * x)).
Proof.
  intro x.
  set (D := ((5 * (1 + x * x)) - 24 * (x * (1 - x)))%Q).
  set (S := ((29 * x - 12) * (29 * x - 12) + 1)%Q).
  assert (Hme : 29 * D == S) by (apply (qeqT_imp_qeq _ _ (b1_kernel_margin_eq24 x))).
  assert (Hge : Qle 1 S) by exact (b1_qsq_plus1_ge1 (29 * x - 12)).
  assert (H21 : Qle (1 * (1 # 29)) (S * (1 # 29))).
  { apply (Qmult_le_compat_r 1 S (1 # 29)).
    - exact Hge.
    - apply Qlt_le_weak. exact b1_0lt1. }
  setoid_replace (1 * (1 # 29))%Q with (1 # 29)%Q in H21 by ring.
  rewrite <- Hme in H21.
  setoid_replace (29 * D * (1 # 29))%Q with D%Q in H21 by ring.
  assert (HD : Qlt 0 D).
  { apply (Qlt_le_trans 0 (1 # 29) D). - exact b1_0lt1. - exact H21. }
  apply Qlt_to_QltT.
  exact (b1_pos_diff_lt (5 * (1 + x * x)) (24 * (x * (1 - x))) HD).
Qed.

(* 档二比值面：x(1−x)/(1+x²) ≤ 5/24 *)
Theorem b1_kernel_ratio_le24 : forall x : Q,
  QleT 0 x -> QleT' x 1 ->
  QleT' ((x * (1 - x)) / (1 + x * x)) (5 # 24).
Proof.
  intros x Hx0 Hx1.
  pose proof (b1_den_pos x) as Hden.
  pose proof (QltT_to_Qlt _ _ (b1_kernel_pointwise_lt24 x)) as Hpt.
  (* 24·num < 5·den ⟹ num ≤ den·(5/24) *)
  assert (Hstep1 : Qle (x * (1 - x)) ((1 + x * x) * (5 # 24))).
  { pose proof (Qmult_le_compat_r (24 * (x * (1 - x))) (5 * (1 + x * x)) (1 # 24)
                  (Qlt_le_weak _ _ Hpt) (Qlt_le_weak _ _ b1_0lt1)) as H1.
    setoid_replace ((24 * (x * (1 - x))) * (1 # 24))%Q with (x * (1 - x))%Q in H1 by ring.
    setoid_replace ((5 * (1 + x * x)) * (1 # 24))%Q with ((1 + x * x) * (5 # 24))%Q in H1 by ring.
    exact H1. }
  assert (Hcol : ((1 + x * x) * (5 # 24)) * (/ (1 + x * x)) == (5 # 24)).
  { remember (/ (1 + x * x)) as u eqn:Eu.
    assert (Hid : (1 + x * x) * u == 1).
    { subst u. apply Qmult_inv_r.
      intro Hc. apply (Qlt_not_eq 0 (1 + x * x) Hden).
      apply (Qeq_sym (1 + x * x) 0). exact Hc. }
    setoid_replace (((1 + x * x) * (5 # 24)) * u)%Q
      with ((5 # 24) * ((1 + x * x) * u))%Q by ring.
    rewrite Hid. apply Qmult_1_r. }
  apply Qle_to_QleT'.
  setoid_replace ((x * (1 - x)) / (1 + x * x))%Q
    with ((x * (1 - x)) * (/ (1 + x * x)))%Q by reflexivity.
  rewrite <- Hcol.
  apply (Qmult_le_compat_r (x * (1 - x)) ((1 + x * x) * (5 # 24)) (/ (1 + x * x)) Hstep1).
  apply Qlt_le_weak. apply (b1_inv_pos (1 + x * x)). exact Hden.
Qed.

(* ========== §3 幂次抬升（单调 q_pow） ========== *)

Theorem b1_kernel_pow_le24 : forall (n : nat) (x : Q),
  QleT 0 x -> QleT' x 1 ->
  QleT' (q_pow ((x * (1 - x)) / (1 + x * x)) n) (q_pow (5 # 24) n).
Proof.
  intros n x Hx0 Hx1.
  apply Qle_to_QleT'.
  apply (q_pow_mono _ _ n).
  - replace ((x * (1 - x)) / (1 + x * x))%Q
      with ((x * (1 - x)) * (/ (1 + x * x)))%Q by reflexivity.
    apply (Qmult_le_0_compat (x * (1 - x)) (/ (1 + x * x))).
    + exact (b1_kernel_num_nonneg x Hx0 Hx1).
    + apply Qlt_le_weak. apply (b1_inv_pos (1 + x * x)). exact (b1_den_pos x).
  - exact (QleT'_to_Qle _ _ (b1_kernel_ratio_le24 x Hx0 Hx1)).
Qed.

(* ========== §4 正性肢（B3 先例配方迁移：核于开区间严格正） ========== *)

Theorem b1_kernel_pos : forall x : Q,
  QltT 0 x -> QltT x 1 -> QltT 0 ((x * (1 - x)) / (1 + x * x)).
Proof.
  intros x Hx0 Hx1.
  apply Qlt_to_QltT.
  setoid_replace ((x * (1 - x)) / (1 + x * x))%Q
    with ((x * (1 - x)) * (/ (1 + x * x)))%Q by reflexivity.
  apply Qmult_lt_0_compat.
  - exact (b1_kernel_num_pos x Hx0 Hx1).
  - apply (b1_inv_pos (1 + x * x)). exact (b1_den_pos x).
Qed.

(* ========== §5 数值锚（独立复算比对点） ========== *)

(* 锚一：x = 1/2：核比值 = 1/5（精确有理数算术：1/4 ÷ 5/4 = 1/5） *)
Lemma b1_kernel_anchor_half :
  QeqT (((1 # 2) * (1 - (1 # 2))) / (1 + (1 # 2) * (1 # 2))) (1 # 5).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* 锚二：x = 2/5（真 sup 位）：核比值 = 6/29（≈0.2069 < 5/24 ≈ 0.2083） *)
Lemma b1_kernel_anchor_twofifth :
  QeqT (((2 # 5) * (1 - (2 # 5))) / (1 + (2 # 5) * (2 # 5))) (6 # 29).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* 锚三：锐化档余量：5/24 − 6/29 = 1/696 > 0（档二未饱和的机械凭证） *)
Lemma b1_kernel_anchor_gap :
  QeqT ((5 # 24) - (6 # 29)) (1 # 696).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma b1_kernel_anchor_gap_pos : QltT 0 ((5 # 24) - (6 # 29)).
Proof. apply Qlt_to_QltT. unfold Qlt. reflexivity. Qed.

(* ========== §6 在件检验与假设审计 ========== *)

Check b1_kernel_pointwise_lt4.
Check b1_kernel_ratio_le4.
Check b1_kernel_pointwise_lt24.
Check b1_kernel_ratio_le24.
Check b1_kernel_pow_le24.
Check b1_kernel_pos.
Check b1_kernel_num_nonneg.
Check b1_kernel_num_pos.
Check b1_kernel_anchor_half.
Check b1_kernel_anchor_twofifth.
Check b1_kernel_anchor_gap.

Print Assumptions b1_kernel_pointwise_lt4.
Print Assumptions b1_kernel_ratio_le4.
Print Assumptions b1_kernel_pointwise_lt24.
Print Assumptions b1_kernel_ratio_le24.
Print Assumptions b1_kernel_pow_le24.
Print Assumptions b1_kernel_pos.
