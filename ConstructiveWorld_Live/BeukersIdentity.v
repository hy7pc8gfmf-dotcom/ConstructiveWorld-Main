(* ==========================================================================)
   BeukersIdentity.v — Beukers 型 q_n 平方和恒等式与归一化因子的有理层语句化
   使命: bi_D 反转平方和恒等式 bi_D_eq_qtilde（Σ C(n,k)^2 反转归位 == bk_Qn_qtilde n）、bi_core_qtilde/bi_norm_factor（2^(n+1)·q_n 与 2^(2n+1)·q_n(1/2) 的 QeqT 桥）、bi_Qn_half_gt1/bi_square_disc 严格下界族与 bi_n1_anchor 数值锚组。
   依赖: S01_BaseRing、S02_CauchyComplete、S03_QExp、BeukersLists；Stdlib QArith、Setoid
   对标: Apéry–Beukers 型收敛加速序列的整数支恒等式（q_n = Σ_k C(n,k)^2 与 3^n 增长律）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import BeukersLists.

Open Scope nat_scope.

(* ============================================================ *)
(* §A Delannoy 核心（升幂和承载）与反转归位                              *)
(*   bi_D n = Σ_{k≤n} C(n,n−k)²·2^{n−k}，换元 j = n−k 即升幂和          *)
(*   Σ_{j≤n} C(n,j)²·2^j（反转和经 bk_psd 的递归结构承载）。            *)
(* ============================================================ *)

Definition bi_D (n : nat) : nat :=
  bk_psd (fun k => bkC n (n - k) * bkC n (n - k)) (Datatypes.S n).

(* 反转归位：C(n,k)² 对称（bk_Qn_sym）⟹ 反转和 == q̃_n 逐项归位
   （bk_psd_ext 逐点窗口 k < S n ⟺ k ≤ n 恰在对称域内） *)
Lemma bi_D_eq_qtilde : forall n : nat, bi_D n = bk_Qn_qtilde n.
Proof.
  intro n. unfold bi_D, bk_Qn_qtilde.
  apply bk_psd_ext. intros k Hk.
  assert (Hkle : k <= n) by lia.
  rewrite (bk_Qn_sym n k Hkle).
  reflexivity.
Qed.

(* 主件①：Delannoy 核心 == q̃_n（QeqT Set 面） *)
Theorem bi_core_qtilde : forall n : nat,
  QeqT ((Z.of_nat (bi_D n) # 1)%Q) ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n. apply qeq_imp_qeqT.
  rewrite bi_D_eq_qtilde. reflexivity.
Qed.

(* Q 层 2 幂：q_pow (2#1) n == Q#2^n（换算辅助引理） *)
Lemma bi_q_pow_2 : forall n : nat, q_pow (2 # 1)%Q n == (Z.of_nat (2 ^ n) # 1)%Q.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH.
    replace (2 # 1)%Q with (Z.of_nat 2 # 1)%Q by reflexivity.
    replace (2 ^ Datatypes.S n)%nat with (2 * 2 ^ n)%nat by (cbn [Nat.pow]; lia).
    apply bk_Qmul_nat.
Qed.

(* ============================================================ *)
(* §B 主件②：真归一因子闭式 2^{n+1}·q̃_n == 2^{2n+1}·Q_n(1/2)            *)
(*   （真恒等式 ln2 − x'_n = I_n/(2^{n+1}·q̃_n) 的归一档；                *)
(*    2^{n+1}·q̃_n = 2^{2n+1}·Q_n(1/2) 即 2^{−(2n+1)} 归一的正确落点）    *)
(* ============================================================ *)

Theorem bi_norm_factor : forall n : nat,
  QeqT ((Z.of_nat (2 ^ (Datatypes.S n) * bk_Qn_qtilde n) # 1)%Q)
       ((q_pow (2 # 1)%Q (Datatypes.S (2 * n)) * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q).
Proof.
  intro n. apply qeq_imp_qeqT.
  replace (Datatypes.S (2 * n))%nat with (Datatypes.S n + n)%nat by lia.
  rewrite q_pow_add.
  transitivity ((q_pow (2 # 1)%Q (Datatypes.S n) * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q).
  - rewrite bi_q_pow_2. apply Qeq_sym. apply bk_Qmul_nat.
  - assert (Hh := bk_Qn_half_closed n).
    rewrite <- Qmult_assoc. rewrite Hh. reflexivity.
Qed.

(* ============================================================ *)
(* §C Q 层支撑引理（Prop 面，仅作推理辅助）                              *)
(* ============================================================ *)

(* 同分母 Qlt（Z 面直译） *)
Lemma bi_Qlt_same_den : forall (a b : Z) (d : positive),
  (a < b)%Z -> Qlt (a # d) (b # d).
Proof.
  intros a b d Hab.
  assert (Hd : (0 < Z.pos d)%Z) by apply Pos2Z.is_pos.
  unfold Qlt. cbn [Qnum Qden]. nia.
Qed.

(* Qlt 沿 Qeq 运输 *)
Lemma bi_qlt_eq : forall a b c d : Q, Qlt a b -> a == c -> b == d -> Qlt c d.
Proof.
  intros a b c d Hab Hac Hbd.
  rewrite <- Hac, <- Hbd. exact Hab.
Qed.

(* 正 q 幂 *)
Lemma bi_q_pow_pos2 : forall n : nat, Qlt 0%Q (q_pow (2 # 1)%Q n).
Proof.
  induction n as [| n IH].
  - cbn [q_pow]. unfold Qlt. cbn [Qnum Qden]. lia.
  - cbn [q_pow]. apply Qmult_lt_0_compat.
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + exact IH.
Qed.

(* 正乘消去：a·q < c·q 且 0 < q ⟹ a < c *)
Lemma bi_Qlt_mul_cancel_r : forall a c q : Q,
  Qlt 0%Q q -> Qlt (a * q)%Q (c * q)%Q -> Qlt a c.
Proof.
  intros a c q Hq0 Hlt.
  destruct (Qlt_le_dec a c) as [Hac | Hca].
  - exact Hac.
  - exfalso. apply (Qlt_not_le (a * q)%Q (c * q)%Q Hlt).
    apply Qmult_le_compat_r.
    + exact Hca.
    + apply Qlt_le_weak. exact Hq0.
Qed.

(* 3^k > 0（幂正性，供 nia/lia 使用） *)
Lemma bi_pow3_pos : forall k : nat, (0 < 3 ^ k)%nat.
Proof.
  intro k. induction k as [| k IH].
  - cbn [Nat.pow]. lia.
  - cbn [Nat.pow]. lia.
Qed.

(* 2^n < 3^n（n≥1） *)
Lemma bi_half_gt_nat : forall n : nat, 1 <= n -> (2 ^ n < 3 ^ n)%nat.
Proof.
  intros n. induction n as [| n IH]; intros Hn.
  - cbn [Nat.pow]. lia.
  - destruct n as [| m].
    + cbn [Nat.pow]. lia.
    + assert (Hm : 1 <= Datatypes.S m) by lia. specialize (IH Hm).
      assert (Hp := bi_pow3_pos (Datatypes.S m)).
      rewrite (Nat.pow_succ_r' 2 (Datatypes.S m)), (Nat.pow_succ_r' 3 (Datatypes.S m)).
      nia.
Qed.

(* ============================================================ *)
(* ============================================================ *)

Theorem bi_Qn_half_gt1 : forall n : nat, 1 <= n ->
  QltT (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q).
Proof.
  intros n Hn.
  assert (Hge := bk_Qn_ge_3pow_nat n).
  assert (H23 := bi_half_gt_nat n Hn).
  assert (Hq : (2 ^ n < bk_Qn_qtilde n)%nat) by lia.
  assert (Hz : (Z.of_nat (2 ^ n) < Z.of_nat (bk_Qn_qtilde n))%Z)
    by (apply Nat2Z.inj_lt; exact Hq).
  assert (HQ : Qlt (Z.of_nat (2 ^ n) # 1) (Z.of_nat (bk_Qn_qtilde n) # 1))
    by (apply bi_Qlt_same_den; exact Hz).
  assert (Hh := bk_Qn_half_closed n).
  assert (HQ2 : Qlt ((q_pow (2 # 1)%Q n * (1 # 1))%Q)
                    ((q_pow (2 # 1)%Q n * bkQ (bk_Qn_list n) (1 # 2))%Q)).
  { apply (bi_qlt_eq _ _ _ _ HQ).
    - rewrite bi_q_pow_2. symmetry. apply Qmult_1_r.
    - apply Qeq_sym. exact Hh. }
  assert (HQ3 : Qlt (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q)).
  { apply (bi_Qlt_mul_cancel_r (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q)
             (q_pow (2 # 1)%Q n)).
    - apply bi_q_pow_pos2.
    - apply (bi_qlt_eq _ _ _ _ HQ2); ring. }
  apply Qlt_to_QltT. exact HQ3.
Qed.

(* Q_n(1/2) ≠ 1（n≥1）——平方归一强迫 Q_n(1/2)==1 的否证件 *)
Lemma bi_half_not1 : forall n : nat, 1 <= n ->
  ~ (bkQ (bk_Qn_list n) (1 # 2)%Q == 1 # 1)%Q.
Proof.
  intros n Hn He.
  assert (Hlt := QltT_to_Qlt (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q)
                   (bi_Qn_half_gt1 n Hn)).
  exact (Qlt_not_eq (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q) Hlt (Qeq_sym _ _ He)).
Qed.

(* ============================================================ *)
(* §E 主件④：平方归一分离见证（x < x²，n≥1 全域）                        *)
(*   则强迫 Q_n(1/2)² == Q_n(1/2)，即 Q_n(1/2) == 1——被 §D 否证。        *)
(* ============================================================ *)

Theorem bi_square_disc : forall n : nat, 1 <= n ->
  QltT (bkQ (bk_Qn_list n) (1 # 2)%Q)
       ((bkQ (bk_Qn_list n) (1 # 2)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q).
Proof.
  intros n Hn.
  assert (Hlt := QltT_to_Qlt (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q)
                   (bi_Qn_half_gt1 n Hn)).
  assert (H2 : Qlt ((1 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q)
                   ((bkQ (bk_Qn_list n) (1 # 2)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q).
  { apply Qmult_lt_compat_r.
    - apply (Qlt_trans 0%Q (1 # 1)%Q).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + exact Hlt.
    - exact Hlt. }
  apply Qlt_to_QltT.
  apply (bi_qlt_eq _ _ _ _ H2); ring.
Qed.

(* ============================================================ *)
(* §F 数值锚（n=1：q̃_1 = 3，2^{2·1+1}·Q_1(1/2) = 12，Q_1(1/2)=3/2）      *)
(* ============================================================ *)

Theorem bi_n1_anchor : QeqT ((Z.of_nat (2 ^ 2 * bk_Qn_qtilde 1) # 1)%Q) (12 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bi_Qn_half_n1 : QeqT (bkQ (bk_Qn_list 1) (1 # 2)%Q) (3 # 2)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* 假设审计：Print Assumptions                                          *)
(* ============================================================ *)

Print Assumptions bi_core_qtilde.
Print Assumptions bi_norm_factor.
Print Assumptions bi_Qn_half_gt1.
Print Assumptions bi_square_disc.
Print Assumptions bi_n1_anchor.
Print Assumptions bi_Qn_half_n1.
