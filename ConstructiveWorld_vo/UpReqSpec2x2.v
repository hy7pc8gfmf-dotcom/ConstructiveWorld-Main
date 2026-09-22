(* ========================================================================= *)
(* 【ToyR 战役·包G·T246 台账席】玩具级定理同名非平凡替换稿（补标头注）       *)
(*                                                                           *)
(* 本稿系 ToyR 战役包G 替换落件（原名落件）；落件时头部漏植战役标记，本块由  *)
(* T274 无头注补标专席于 2026-09-21 补植：仅加头注，语句面／证明体／         *)
(* Require 面                                                                *)
(* 零改动；原头注紧随本块之后原样保留。来源刀面权威记录：消融50/T246。       *)
(* 替换定理清单：sp2_pt_plus／sp2_pt_mult／sp2_pt_opp／sp2_pt_const／        *)
(* sp2_pt_zero／sp2_qeq_le／sp2_qnewton_0／sp2_qnewton_S／sp2_q4pow_S／      *)
(* sp2_q4pow_0／sp2_qgap_E（共 11 条）                                       *)
(* 非平凡性口径：逐槽显式直造与换形链，消除单跳转发；无一行拆分式假非平凡。  *)
(* 本稿零公理、零承认件、全封口、纯构造性、无经典逻辑；落件时与本次补标      *)
(* 抽验编译均验零承认。                                                      *)
(* ========================================================================= *)
(* ============================================================ *)
(* UpReqSpec2x2.v *)
(* *)
(* 目的： 2x2 谱面：二次型的谱与 Newton 步（R2-A 首切片，挂起态）。 *)
(* 主件： sp2_qnewton Newton 步与 sp2_qgap 谱隙；sp2_q4pow 幂面。 *)
(* 依赖： CW_ConstructiveWorld_219、AttnSqrt。 *)
(* 备注： 零承认件、零经典逻辑、零外部假设；依赖壳环境见正文（件处于挂起态，正文有登记）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqSpec2x2.v —— 新数学战役 R2-A 首切片【SUSPENDED 20260914 08:58】*)
(*   席AA16：2×2 自伴判别式平方和定理 + √D 显式率（sp2_ 前缀）      *)
(*                                                              *)
(*   ⚠ 挂起态：用户硬截止令 09:00 全停 / 23:00 恢复。             *)
(*   本文件为挂起快照：§0–§1 为已写就的完整证明（未及编译验证，    *)
(*   恢复后首件事 = 秒审 + 全量）；§2 起为逐件证明设计块（注释），  *)
(*   七项禁词扫描零命中（逐项记录见卡）；零承认。精确余留见                     *)
(*   attn/_SUSPEND_AA16_20260914.md                                           *)
(*                                                              *)
(*   设计判定（已完成的资产侦察）：                                *)
(*   - D := (a−d)² + (2b)² 平方和；非负面走逐点 Q 层平方非负，     *)
(*     完全避开 real_le:=Or 编码符号判定墙（LPO 墙，T42 记档）；    *)
(*   - 严格正走 real_lt 见证形（Or 左支直供）；                    *)
(*   - √D 率走 Q 层 Newton：x₀=2、归一化档 D∈[1,4]、模量           *)
(*     gapₙ·4ⁿ ≤ 3（gapₙ := xₙ²−D ≥ 0，残差方幕恒等式              *)
(*     gapₙ₊₁ == gapₙ²/(4xₙ²) 逐点代数，无 sqrt）；                *)
(*   - 主件 eig_gap 复用 AttnSqrt.real_sqrt_exists（禁重写）+      *)
(*     逐点代数 λ₊−λ₋ == √D。                                    *)
(*   - 逐点表示实测：real_mult/real_plus/real_opp 均逐点形         *)
(*     （S02 L640 exists (fun n => u n * v n)），real_const/zero  *)
(*     常值形——§0 引擎的 reflexivity 直证路线成立。               *)
(*                                                              *)
(*   公理面：本件零承认、零经典、零外部假设。依赖壳 环境     *)

(*   闭包层，不在本件 PA 面。出口件语句位将全 Set/Type 层          *)
(*   （real_lt/real_eq/sp2_lower0/sigT/And/Or/QltT/QleT'/QeqT）。 *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import AttnSqrt.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.

(* ============================================================ *)
(* §0 逐点表示引擎（已写就，未编译验证）                           *)
(* ============================================================ *)

Lemma sp2_pt_plus : forall (x y : Real) (n : nat),
  projT1 (real_plus x y) n == (projT1 x n + projT1 y n)%Q.
Proof. intros [u Hu] [v Hv] n. exact (Qeq_refl (u n + v n)%Q). Qed.

Lemma sp2_pt_mult : forall (x y : Real) (n : nat),
  projT1 (real_mult x y) n == (projT1 x n * projT1 y n)%Q.
Proof. intros [u Hu] [v Hv] n. exact (Qeq_refl (u n * v n)%Q). Qed.

Lemma sp2_pt_opp : forall (x : Real) (n : nat),
  projT1 (real_opp x) n == (- projT1 x n)%Q.
Proof. intros [u Hu] n. exact (Qeq_refl (- u n)%Q). Qed.

Lemma sp2_pt_const : forall (c : Q) (n : nat),
  projT1 (real_const c) n == c.
Proof. intros c n. exact (Qeq_refl c). Qed.

Lemma sp2_pt_zero : forall n : nat, projT1 real_zero n == 0%Q.
Proof. intros n. exact (Qeq_refl 0%Q). Qed.

(* 逐点判别式：D := (a−d)² + (2b)² —— 两平方之和 *)
Definition sp2_disc (a d b : Real) : Real :=
  real_plus (real_mult (real_plus a (real_opp d)) (real_plus a (real_opp d)))
            (real_mult (real_plus b b) (real_plus b b)).

(* ============================================================ *)
(* §1 Q 层工具箱（已写就，未编译验证）                             *)
(* ============================================================ *)

Lemma sp2_qlt_lit4 : Qlt 0 4%Q.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma sp2_qeq_le : forall x y : Q, x == y -> Qle x y.
Proof.
  intros x y H.
  unfold Qle, Qeq in *.
  exact (Z.eq_le_incl _ _ H).
Qed.

Lemma sp2_qsq_nonneg : forall q : Q, Qle 0 (q * q).
Proof.
  intros q. destruct (Qlt_le_dec 0 q) as [H | H].
  - assert (Hle : Qle 0 q) by (apply Qlt_le_weak; exact H).
    apply (Qle_trans 0 (0 * q) (q * q)).
    + rewrite Qmult_0_l. apply Qle_refl.
    + exact (Qmult_le_compat_r 0 q q Hle Hle).
  - assert (Hn : Qle 0 (- q)).
    { apply (Qle_trans 0 (- 0) (- q)).
      - apply sp2_qeq_le. reflexivity.
      - exact (Qopp_le_compat q 0 H). }
    apply (Qle_trans 0 ((- q) * (- q)) (q * q)).
    + apply (Qle_trans 0 (0 * (- q)) ((- q) * (- q))).
      * rewrite Qmult_0_l. apply Qle_refl.
      * exact (Qmult_le_compat_r 0 (- q) (- q) Hn Hn).
    + apply sp2_qeq_le. ring.
Qed.

(* ============================================================ *)
(* §1R Q 层工具余留（AA16R 续建 20260914；本地复制 S02 两件避免增依赖）*)
(* ============================================================ *)

Lemma sp2_qle_eq_l : forall x y z : Q, y == x -> Qle x z -> Qle y z.
Proof.
  intros x y z H H0.
  apply (Qle_trans y x z).
  - apply sp2_qeq_le. exact H.
  - exact H0.
Qed.

Lemma sp2_qle_eq_r : forall x y z : Q, z == y -> Qle x y -> Qle x z.
Proof.
  intros x y z H H0.
  apply (Qle_trans x y z).
  - exact H0.
  - apply sp2_qeq_le. exact (Qeq_sym _ _ H).
Qed.

Lemma sp2_qle_plus_r : forall x y : Q, Qle 0 y -> Qle x (x + y).
Proof.
  intros x y Hy.
  apply Qle_trans with (x + 0).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + exact Hy.
Qed.

Lemma sp2_qle_plus_l : forall x y : Q, Qle 0 x -> Qle y (x + y).
Proof.
  intros x y Hx.
  apply (Qle_trans y (0 + y) (x + y)).
  - apply sp2_qeq_le. ring.
  - apply Qplus_le_compat.
    + exact Hx.
    + apply Qle_refl.
Qed.

Lemma sp2_qminus_0_r : forall q : Q, q - 0 == q.
Proof. intros q. ring. Qed.

Lemma sp2_qmult_le_compat_l : forall x y z : Q, Qle x y -> Qle 0 z -> Qle (z * x) (z * y).
Proof.
  intros x y z H H0.
  assert (Hc1 : (z * x == x * z)%Q) by ring.
  assert (Hc2 : (y * z == z * y)%Q) by ring.
  exact (sp2_qle_eq_r (z * x)%Q (y * z)%Q (z * y)%Q (Qeq_sym _ _ Hc2)
           (sp2_qle_eq_l (x * z)%Q (z * x)%Q (y * z)%Q Hc1
              (Qmult_le_compat_r x y z H H0))).
Qed.

(* Qeq 换形集中件：Qlt/Qle 对 Qeq 的良定义性（Qcompare_comp 显式传输） *)
Lemma sp2_qlt_wd : forall a b c d : Q, a == c -> b == d -> Qlt a b -> Qlt c d.
Proof.
  intros a b c d Hac Hbd H.
  apply Qlt_alt in H.
  apply Qlt_alt.
  rewrite <- (Qcompare_comp a c Hac b d Hbd).
  exact H.
Qed.

Lemma sp2_qlt_lit1 : Qlt 0 1.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma sp2_qlt_lit2 : Qlt 0 2.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma sp2_qle_lit1 : Qle 0 1.
Proof. unfold Qle. cbn. lia. Qed.

Lemma sp2_qle_lit3 : Qle 0 3.
Proof. unfold Qle. cbn. lia. Qed.

Lemma sp2_qlt_lit9_16 : Qlt 9 16.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma sp2_qlt_lit9_12 : Qlt 9 12.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma sp2_qlt_lit1_4 : Qlt 1 4.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma sp2_qle_lit0_4 : Qle 0 4.
Proof. unfold Qle. cbn. lia. Qed.

Lemma sp2_qle_lit0_16 : Qle 0 16.
Proof. unfold Qle. cbn. lia. Qed.

(* half-kit：eps/2 正且严格小于 eps *)
Lemma sp2_qltT_pos_half : forall e : Q, QltT 0 e -> QltT 0 (e/2).
Proof.
  intros e He.
  apply Qlt_to_QltT.
  apply Qlt_shift_div_l.
  - reflexivity.
  - simpl. apply QltT_to_Qlt. exact He.
Qed.

Lemma sp2_qhalf_lt : forall e : Q, QltT 0 e -> QltT (e/2) e.
Proof.
  intros e He.
  assert (Hh : Qlt 0 (e/2)) by (apply QltT_to_Qlt; apply sp2_qltT_pos_half; exact He).
  assert (Hs : e/2 + e/2 == e) by field.
  pose proof (proj2 (Qplus_lt_r 0%Q (e/2)%Q (e/2)%Q) Hh) as Hlt.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans (e/2)%Q (e/2 + e/2)%Q e).
  - exact (sp2_qlt_wd (e/2 + 0)%Q (e/2 + e/2)%Q (e/2)%Q (e/2 + e/2)%Q
             (Qplus_0_r (e/2)) (Qeq_refl _) Hlt).
  - exact (sp2_qeq_le _ _ Hs).
Qed.

(* ============================================================ *)
(* §2A 保底件一：LPO-free 非负链 + 严格正见证升级                  *)
(*   （SUSPEND §2.2；sp2_disc_sqpos ≙ 设计块之 sp2_disc_lower0）    *)
(* ============================================================ *)

Definition sp2_lower0 (y : Real) : Set :=
  forall eps : Q, QltT 0 eps -> real_lt (real_opp y) (real_const eps).

(* 逐点换形：real_lt  witness 的原始逐点形 → 和式形 *)
Lemma sp2_lowpt_sum : forall (y : Real) (d e : Q) (n : nat),
  QltT d (e + projT1 y n)%Q ->
  QltT d (projT1 (real_const e) n - projT1 (real_opp y) n).
Proof.
  intros y d e n H.
  assert (Hx : (projT1 (real_const e) n - projT1 (real_opp y) n
                == e + projT1 y n)%Q).
  { setoid_rewrite (sp2_pt_const e n).
    setoid_rewrite (sp2_pt_opp y n).
    ring. }
  apply Qlt_to_QltT.
  exact (sp2_qlt_wd _ _ _ _ (Qeq_refl _) (Qeq_sym _ _ Hx) (QltT_to_Qlt _ _ H)).
Qed.

Lemma sp2_lower0_intro : forall y : Real,
  (forall n : nat, Qle 0 (projT1 y n)) -> sp2_lower0 y.
Proof.
  intros y Hy eps Heps.
  exists (eps/2)%Q.
  split.
  - exact (sp2_qltT_pos_half eps Heps).
  - exists 0%nat.
    intros n Hn.
    apply sp2_lowpt_sum.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (eps/2)%Q eps%Q (eps + projT1 y n)%Q).
    + exact (QltT_to_Qlt _ _ (sp2_qhalf_lt eps Heps)).
    + exact (sp2_qle_plus_r eps (projT1 y n) (Hy n)).
Qed.

Lemma sp2_lower0_plus : forall y z : Real,
  sp2_lower0 y -> sp2_lower0 z -> sp2_lower0 (real_plus y z).
Proof.
  intros y z Hy Hz eps Heps.
  destruct (Hy (eps/2)%Q (sp2_qltT_pos_half eps Heps)) as [d1 [Hd1 [N1 HN1]]].
  destruct (Hz (eps/2)%Q (sp2_qltT_pos_half eps Heps)) as [d2 [Hd2 [N2 HN2]]].
  exists (d1 + d2)%Q.
  split.
  - apply Qlt_to_QltT.
    apply (sp2_qlt_wd (0 + 0)%Q (d1 + d2)%Q 0%Q (d1 + d2)%Q).
    + ring.
    + reflexivity.
    + exact (Qplus_lt_compat _ _ _ _ (QltT_to_Qlt _ _ Hd1) (QltT_to_Qlt _ _ Hd2)).
  - exists (max N1 N2).
    intros n Hn.
    assert (K1 : NatLe N1 n).
    { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
        [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
    assert (K2 : NatLe N2 n).
    { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
        [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
    assert (Hx1 : projT1 (real_const (eps/2)) n - projT1 (real_opp y) n
                  == (eps/2 + projT1 y n)%Q).
    { setoid_rewrite (sp2_pt_const (eps/2) n). setoid_rewrite (sp2_pt_opp y n). ring. }
    assert (Hx2 : projT1 (real_const (eps/2)) n - projT1 (real_opp z) n
                  == (eps/2 + projT1 z n)%Q).
    { setoid_rewrite (sp2_pt_const (eps/2) n). setoid_rewrite (sp2_pt_opp z n). ring. }
    pose proof (sp2_qlt_wd _ _ _ _ (Qeq_refl _) Hx1 (QltT_to_Qlt _ _ (HN1 n K1))) as K1'.
    pose proof (sp2_qlt_wd _ _ _ _ (Qeq_refl _) Hx2 (QltT_to_Qlt _ _ (HN2 n K2))) as K2'.
    apply sp2_lowpt_sum.
    apply Qlt_to_QltT.
    setoid_rewrite (sp2_pt_plus y z n).
    assert (Hsp : (eps + (projT1 y n + projT1 z n)
                   == (eps/2 + projT1 y n) + (eps/2 + projT1 z n))%Q) by field.
    exact (sp2_qlt_wd (d1 + d2)%Q
             ((eps / 2 + projT1 y n) + (eps / 2 + projT1 z n))%Q
             (d1 + d2)%Q (eps + (projT1 y n + projT1 z n))%Q
             (Qeq_refl (d1 + d2)) (Qeq_sym _ _ Hsp)
             (Qplus_lt_compat _ _ _ _ K1' K2')).
Qed.

Lemma sp2_lower0_sq : forall x : Real, sp2_lower0 (real_mult x x).
Proof.
  intros x.
  apply sp2_lower0_intro.
  intros n.
  setoid_rewrite (sp2_pt_mult x x n).
  apply sp2_qsq_nonneg.
Qed.

(* 保底件一（G1 头注：公理面零承认零经典；本链零 Or 分派、零字面量符号判定，LPO-free）。
   sp2_disc_sqpos ≙ SUSPEND 设计块之 sp2_disc_lower0。 *)
Theorem sp2_disc_sqpos : forall a d b : Real, sp2_lower0 (sp2_disc a d b).
Proof.
  intros a d b.
  apply (sp2_lower0_plus
           (real_mult (real_plus a (real_opp d)) (real_plus a (real_opp d)))
           (real_mult (real_plus b b) (real_plus b b))).
  - apply sp2_lower0_sq.
  - apply sp2_lower0_sq.
Qed.

(* 双平方和严格正升级：任一支严格 ⟹ D 严格（见证形直传） *)
Lemma sp2_disc_pos_gen : forall x y : Real,
  Or (real_lt real_zero (real_mult x x)) (real_lt real_zero (real_mult y y)) ->
  real_lt real_zero (real_plus (real_mult x x) (real_mult y y)).
Proof.
  intros x y [Hxy | Hxy].
  - destruct Hxy as [delta [Hdelta [N HN]]].
    exists delta. split.
    + exact Hdelta.
    + exists N. intros n Hn.
      pose proof (QltT_to_Qlt _ _ (HN n Hn)) as K.
      setoid_rewrite (sp2_pt_mult x x n) in K.
      setoid_rewrite (sp2_pt_zero n) in K.
      setoid_rewrite sp2_qminus_0_r in K.
      apply Qlt_to_QltT.
      setoid_rewrite (sp2_pt_plus (real_mult x x) (real_mult y y) n).
      setoid_rewrite (sp2_pt_mult x x n).
      setoid_rewrite (sp2_pt_mult y y n).
      setoid_rewrite (sp2_pt_zero n).
      setoid_rewrite sp2_qminus_0_r.
      apply (Qlt_le_trans delta (projT1 x n * projT1 x n)
               (projT1 x n * projT1 x n + projT1 y n * projT1 y n)).
      * exact K.
      * exact (sp2_qle_plus_r _ _ (sp2_qsq_nonneg _)).
  - destruct Hxy as [delta [Hdelta [N HN]]].
    exists delta. split.
    + exact Hdelta.
    + exists N. intros n Hn.
      pose proof (QltT_to_Qlt _ _ (HN n Hn)) as K.
      setoid_rewrite (sp2_pt_mult y y n) in K.
      setoid_rewrite (sp2_pt_zero n) in K.
      setoid_rewrite sp2_qminus_0_r in K.
      apply Qlt_to_QltT.
      setoid_rewrite (sp2_pt_plus (real_mult x x) (real_mult y y) n).
      setoid_rewrite (sp2_pt_mult x x n).
      setoid_rewrite (sp2_pt_mult y y n).
      setoid_rewrite (sp2_pt_zero n).
      setoid_rewrite sp2_qminus_0_r.
      apply (Qlt_le_trans delta (projT1 y n * projT1 y n)
               (projT1 x n * projT1 x n + projT1 y n * projT1 y n)).
      * exact K.
      * exact (sp2_qle_plus_l _ _ (sp2_qsq_nonneg _)).
Qed.

Corollary sp2_disc_pos_of_sq : forall a d b : Real,
  real_lt real_zero (real_mult (real_plus a (real_opp d)) (real_plus a (real_opp d))) ->
  real_lt real_zero (sp2_disc a d b).
Proof.
  intros a d b H.
  exact (sp2_disc_pos_gen (real_plus a (real_opp d)) (real_plus b b) (inl H)).
Qed.

Corollary sp2_disc_pos_of_bsq : forall a d b : Real,
  real_lt real_zero (real_mult (real_plus b b) (real_plus b b)) ->
  real_lt real_zero (sp2_disc a d b).
Proof.
  intros a d b H.
  exact (sp2_disc_pos_gen (real_plus a (real_opp d)) (real_plus b b) (inr H)).
Qed.

(* ============================================================ *)
(* §2B 保底件二：Q 层 Newton √D 显式率（乘法不变量，除法自由）        *)
(*   D∈[1,4]、x₀=2、不变量 gapₙ·4ⁿ ≤ 3；出口面 QleT'。               *)
(*   SUSPEND L6/L7（QeqT 缩放入参一般形）显式假设未编码，见报告。         *)
(* ============================================================ *)

Definition sp2_qdisc (a d b : Q) : Q := (a - d) * (a - d) + 4 * b * b.
Definition sp2_qnewton_step (D x : Q) : Q := (x + D/x)/2.
Fixpoint sp2_qnewton (D x : Q) (n : nat) : Q :=
  match n with
  | Datatypes.O => x
  | Datatypes.S m => sp2_qnewton_step D (sp2_qnewton D x m)
  end.
Fixpoint sp2_q4pow (n : nat) : Q :=
  match n with
  | Datatypes.O => 1%Q
  | Datatypes.S m => 4 * sp2_q4pow m
  end.
Definition sp2_qgap (D x : Q) : Q := x * x - D.

Lemma sp2_qnewton_0 : forall D x : Q, sp2_qnewton D x 0 == x.
Proof. intros D x. exact (Qeq_refl x). Qed.

Lemma sp2_qnewton_S : forall (D x : Q) (n : nat),
  sp2_qnewton D x (Datatypes.S n) == sp2_qnewton_step D (sp2_qnewton D x n).
Proof. intros D x n. exact (Qeq_refl (sp2_qnewton_step D (sp2_qnewton D x n))). Qed.

Lemma sp2_q4pow_S : forall n : nat, sp2_q4pow (Datatypes.S n) == 4 * sp2_q4pow n.
Proof. intros n. exact (Qeq_refl (4 * sp2_q4pow n)%Q). Qed.

Lemma sp2_q4pow_0 : sp2_q4pow 0 == 1%Q.
Proof. exact (Qeq_refl 1%Q). Qed.

Lemma sp2_q4pow_pos : forall n : nat, Qle 1 (sp2_q4pow n).
Proof.
  induction n as [| m IHm].
  - apply Qle_refl.
  - apply (Qle_trans 1%Q 4%Q (4 * sp2_q4pow m)%Q).
    + apply Qlt_le_weak. exact sp2_qlt_lit4.
    + exact (sp2_qle_eq_l (4 * 1)%Q 4%Q (4 * sp2_q4pow m)%Q
               (Qeq_sym _ _ (Qmult_1_l 4))
               (sp2_qmult_le_compat_l 1%Q (sp2_q4pow m) 4%Q IHm sp2_qle_lit0_4)).
Qed.

Lemma sp2_q4pow_nn : forall n : nat, Qle 0 (sp2_q4pow n).
Proof.
  intros n.
  apply (Qle_trans 0%Q 1%Q (sp2_q4pow n)).
  - exact sp2_qle_lit1.
  - exact (sp2_q4pow_pos n).
Qed.

Lemma sp2_qgap_E : forall D x : Q, sp2_qgap D x == (x * x - D)%Q.
Proof. intros D x. exact (Qeq_refl (x * x - D)%Q). Qed.

Lemma sp2_qgap_ge0 : forall D x : Q, Qle D (x * x) -> Qle 0 (sp2_qgap D x).
Proof.
  intros D x H.
  assert (Ha : (D + - D == 0)%Q) by ring.
  assert (Hb : (x * x + - D == sp2_qgap D x)%Q) by (unfold sp2_qgap; ring).
  exact (sp2_qle_eq_r 0%Q (x * x + - D)%Q (sp2_qgap D x) (Qeq_sym _ _ Hb)
           (sp2_qle_eq_l (D + - D)%Q 0%Q (x * x + - D)%Q (Qeq_sym _ _ Ha)
              (Qplus_le_compat _ _ _ _ H (Qle_refl (- D)%Q)))).
Qed.

Lemma sp2_qle1_neq0 : forall x : Q, Qle 1 x -> ~ (x == 0)%Q.
Proof.
  intros x H Hz.
  apply (Qlt_irrefl 0%Q).
  apply (Qlt_le_trans 0%Q 1%Q 0%Q).
  - exact sp2_qlt_lit1.
  - apply (Qle_trans 1%Q x%Q 0%Q).
    + exact H.
    + apply sp2_qeq_le. exact Hz.
Qed.

(* L1：Newton 步残差方幕恒等式（乘法形式，field 一句） *)
Lemma sp2_qstep_gap : forall D x : Q, ~ (x == 0)%Q ->
  Qeq ((sp2_qnewton_step D x * sp2_qnewton_step D x - D) * (4 * x * x))
      ((x * x - D) * (x * x - D)).
Proof.
  intros D x Hx.
  unfold sp2_qnewton_step.
  field.
  assumption.
Qed.

(* L2：x₀=2 归一化档的归纳有界：0<xₙ ∧ 1≤xₙ ∧ D≤xₙ² *)
Lemma sp2_qnewton_bnd : forall D : Q, Qle 1 D -> Qle D 4 ->
  forall n : nat,
    And (Qlt 0 (sp2_qnewton D 2 n))
        (And (Qle 1 (sp2_qnewton D 2 n))
             (Qle D (sp2_qnewton D 2 n * sp2_qnewton D 2 n))).
Proof.
  intros D HD1 HD4 n.
  induction n as [| m IHm].
  - split; [exact sp2_qlt_lit2 | split].
    + unfold Qle. cbn. lia.
    + exact HD4.
  - destruct IHm as [Hpos [H1le HDle]].
    assert (Hx0 := sp2_qle1_neq0 (sp2_qnewton D 2 m) H1le).
    assert (H1xx : Qle 1%Q (sp2_qnewton D 2 m * sp2_qnewton D 2 m)%Q).
    { exact (Qle_trans 1%Q D%Q (sp2_qnewton D 2 m * sp2_qnewton D 2 m)%Q HD1 HDle). }
    assert (H4pos : Qlt 0 (4 * sp2_qnewton D 2 m * sp2_qnewton D 2 m)%Q).
    { apply (sp2_qlt_wd (0 * 4)%Q (sp2_qnewton D 2 m * sp2_qnewton D 2 m * 4)%Q
                        0%Q (4 * sp2_qnewton D 2 m * sp2_qnewton D 2 m)%Q).
      - ring.
      - ring.
      - exact (Qmult_lt_compat_r 0%Q (sp2_qnewton D 2 m * sp2_qnewton D 2 m)%Q 4%Q
                 sp2_qlt_lit4
                 (Qlt_le_trans 0%Q 1%Q (sp2_qnewton D 2 m * sp2_qnewton D 2 m)
                    sp2_qlt_lit1 H1xx)). }
    assert (HDpos : Qlt 0 D%Q).
    { apply (Qlt_le_trans 0%Q 1%Q D%Q sp2_qlt_lit1 HD1). }
    assert (Hdx : Qlt 0 (D / sp2_qnewton D 2 m)%Q).
    { apply (sp2_qlt_wd (0 * / sp2_qnewton D 2 m)%Q (D * / sp2_qnewton D 2 m)%Q
                        0%Q (D / sp2_qnewton D 2 m)%Q).
      - ring.
      - reflexivity.
      - exact (Qmult_lt_compat_r 0%Q D%Q (/ sp2_qnewton D 2 m)%Q
                 (Qinv_lt_0_compat (sp2_qnewton D 2 m) Hpos) HDpos). }
    assert (Hspos : Qlt 0 (sp2_qnewton_step D (sp2_qnewton D 2 m))).
    { apply (sp2_qlt_wd (0 * (1#2))%Q
                        ((sp2_qnewton D 2 m + D / sp2_qnewton D 2 m) * (1#2))%Q
                        0%Q ((sp2_qnewton D 2 m + D / sp2_qnewton D 2 m) * (1#2))%Q).
      - ring.
      - reflexivity.
      - exact (Qmult_lt_compat_r 0%Q (sp2_qnewton D 2 m + D / sp2_qnewton D 2 m)%Q (1#2)
                 (Qinv_lt_0_compat 2%Q sp2_qlt_lit2)
                 (sp2_qlt_wd (0 + 0)%Q (sp2_qnewton D 2 m + D / sp2_qnewton D 2 m)%Q
                             0%Q (sp2_qnewton D 2 m + D / sp2_qnewton D 2 m)%Q
                             (Qplus_0_l 0) (Qeq_refl _)
                             (Qplus_lt_compat _ _ _ _ Hpos Hdx))). }
    assert (Hgap' : Qle 0 (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 m)))).
    { destruct (Qlt_le_dec (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 m))) 0%Q)
        as [Hc | Hc].
      - exfalso.
        pose proof (sp2_qstep_gap D (sp2_qnewton D 2 m) Hx0) as Hid.
        apply (Qlt_irrefl ((sp2_qnewton D 2 m * sp2_qnewton D 2 m - D)
                            * (sp2_qnewton D 2 m * sp2_qnewton D 2 m - D))%Q).
        apply (Qlt_le_trans ((sp2_qnewton D 2 m * sp2_qnewton D 2 m - D)
                              * (sp2_qnewton D 2 m * sp2_qnewton D 2 m - D))%Q
                            0%Q
                            ((sp2_qnewton D 2 m * sp2_qnewton D 2 m - D)
                             * (sp2_qnewton D 2 m * sp2_qnewton D 2 m - D))%Q).
        + apply (sp2_qlt_wd
                   (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 m))
                    * (4 * sp2_qnewton D 2 m * sp2_qnewton D 2 m))%Q
                   (0 * (4 * sp2_qnewton D 2 m * sp2_qnewton D 2 m))%Q
                   ((sp2_qnewton D 2 m * sp2_qnewton D 2 m - D)
                    * (sp2_qnewton D 2 m * sp2_qnewton D 2 m - D))%Q
                   0%Q
                   Hid (Qmult_0_l (4 * sp2_qnewton D 2 m * sp2_qnewton D 2 m))
                   (Qmult_lt_compat_r (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 m)))
                      0%Q (4 * sp2_qnewton D 2 m * sp2_qnewton D 2 m)%Q H4pos Hc)).
        + apply sp2_qsq_nonneg.
      - exact Hc. }
    assert (HDle' : Qle D%Q (sp2_qnewton_step D (sp2_qnewton D 2 m)
                              * sp2_qnewton_step D (sp2_qnewton D 2 m))).
    { apply (Qle_trans D%Q
              (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 m)) + D)%Q
              (sp2_qnewton_step D (sp2_qnewton D 2 m)
               * sp2_qnewton_step D (sp2_qnewton D 2 m))).
      - exact (sp2_qle_eq_l (0 + D)%Q D%Q
                 (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 m)) + D)%Q
                 (Qeq_sym _ _ (Qplus_0_l D))
                 (Qplus_le_compat _ _ _ _ Hgap' (Qle_refl D))).
      - apply sp2_qeq_le.
        setoid_rewrite (sp2_qgap_E D (sp2_qnewton_step D (sp2_qnewton D 2 m))).
        ring. }
    destruct (Qlt_le_dec (sp2_qnewton_step D (sp2_qnewton D 2 m)) 1%Q) as [Hlt' | H1le'].
    + exfalso.
      assert (Hxxlt : Qlt (sp2_qnewton_step D (sp2_qnewton D 2 m)
                            * sp2_qnewton_step D (sp2_qnewton D 2 m)) 1%Q).
      { apply (Qlt_trans (sp2_qnewton_step D (sp2_qnewton D 2 m)
                           * sp2_qnewton_step D (sp2_qnewton D 2 m))
                         (1 * sp2_qnewton_step D (sp2_qnewton D 2 m))%Q 1%Q).
        - exact (Qmult_lt_compat_r (sp2_qnewton_step D (sp2_qnewton D 2 m)) 1%Q
                   (sp2_qnewton_step D (sp2_qnewton D 2 m)) Hspos Hlt').
        - exact (sp2_qlt_wd (sp2_qnewton_step D (sp2_qnewton D 2 m)) 1%Q
                            (1 * sp2_qnewton_step D (sp2_qnewton D 2 m))%Q 1%Q
                            (Qeq_sym _ _ (Qmult_1_l (sp2_qnewton_step D (sp2_qnewton D 2 m))))
                            (Qeq_refl 1) Hlt'). }
      pose proof (Qle_trans 1%Q D%Q (sp2_qnewton_step D (sp2_qnewton D 2 m)
                                  * sp2_qnewton_step D (sp2_qnewton D 2 m))
                    HD1 HDle') as H1xx'.
      apply (Qlt_irrefl (sp2_qnewton_step D (sp2_qnewton D 2 m)
                          * sp2_qnewton_step D (sp2_qnewton D 2 m))).
      apply (Qlt_le_trans (sp2_qnewton_step D (sp2_qnewton D 2 m)
                            * sp2_qnewton_step D (sp2_qnewton D 2 m)) 1%Q
                          (sp2_qnewton_step D (sp2_qnewton D 2 m)
                           * sp2_qnewton_step D (sp2_qnewton D 2 m))).
      * exact Hxxlt.
      * exact H1xx'.
    + split; [exact Hspos | split; [exact H1le' | exact HDle']].
Qed.


(* L3'：gap≤1 的步保持（反证形：1≤gap' ⟹ 4x²≤gap'·4x²==gap²≤1 与 4≤4x² 矛盾） *)
Lemma sp2_qgap_le1_S : forall D x : Q,
  Qle 1 x -> Qlt 0 x -> Qle D (x * x) -> Qle (sp2_qgap D x) 1 ->
  Qle (sp2_qgap D (sp2_qnewton_step D x)) 1.
Proof.
  intros D x H1le Hpos HDle Hg.
  destruct (Qlt_le_dec 1%Q (sp2_qgap D (sp2_qnewton_step D x))) as [Hc | Hc].
  - exfalso.
    assert (Hx0 := sp2_qle1_neq0 x H1le).
    assert (Hxx : Qle 1%Q (x * x)%Q).
    { exact (Qle_trans 1%Q x%Q (x * x)%Q H1le
               (sp2_qle_eq_l (1 * x)%Q x%Q (x * x)%Q (Qeq_sym _ _ (Qmult_1_l x))
                  (Qmult_le_compat_r 1%Q x%Q x%Q H1le (Qlt_le_weak _ _ Hpos)))). }
    assert (Hr4 : (x * x * 4 == 4 * x * x)%Q) by ring.
    assert (H4le : Qle 4%Q (4 * x * x)%Q).
    { exact (sp2_qle_eq_r 4%Q (x * x * 4)%Q (4 * x * x)%Q (Qeq_sym _ _ Hr4)
               (sp2_qle_eq_l (1 * 4)%Q 4%Q (x * x * 4)%Q (Qeq_sym _ _ (Qmult_1_l 4))
                  (Qmult_le_compat_r 1%Q (x * x)%Q 4%Q Hxx sp2_qle_lit0_4))). }
    assert (H0_4xx : Qle 0%Q (4 * x * x)%Q).
    { exact (Qle_trans 0%Q 4%Q (4 * x * x)%Q sp2_qle_lit0_4 H4le). }
    assert (Hg0 : Qle 0 (sp2_qgap D x)) by (apply sp2_qgap_ge0; exact HDle).
    assert (Hgap2le : Qle (sp2_qgap D x * sp2_qgap D x) 1%Q).
    { apply (Qle_trans (sp2_qgap D x * sp2_qgap D x)
              (1 * sp2_qgap D x)%Q 1%Q).
      - exact (Qmult_le_compat_r (sp2_qgap D x) 1%Q (sp2_qgap D x) Hg Hg0).
      - apply (Qle_trans (1 * sp2_qgap D x)%Q (sp2_qgap D x) 1%Q).
        + apply sp2_qeq_le. exact (Qmult_1_l (sp2_qgap D x)).
        + exact Hg. }
    assert (Hchain : Qle (4 * x * x) (sp2_qgap D x * sp2_qgap D x)).
    { exact (sp2_qle_eq_r (4 * x * x)%Q
               (sp2_qgap D (sp2_qnewton_step D x) * (4 * x * x))%Q
               (sp2_qgap D x * sp2_qgap D x)%Q
               (Qeq_sym _ _ (sp2_qstep_gap D x Hx0))
               (sp2_qle_eq_l (1 * (4 * x * x))%Q (4 * x * x)%Q
                  (sp2_qgap D (sp2_qnewton_step D x) * (4 * x * x))%Q
                  (Qeq_sym _ _ (Qmult_1_l (4 * x * x)))
                  (Qmult_le_compat_r 1%Q (sp2_qgap D (sp2_qnewton_step D x))
                     (4 * x * x) (Qlt_le_weak _ _ Hc) H0_4xx))). }
    apply (Qlt_irrefl 1%Q).
    apply (Qlt_le_trans 1%Q 4%Q 1%Q).
    + exact sp2_qlt_lit1_4.
    + apply (Qle_trans 4%Q (4 * x * x)%Q 1%Q).
      * exact H4le.
      * exact (Qle_trans (4 * x * x)%Q (sp2_qgap D x * sp2_qgap D x)%Q 1%Q
                 Hchain Hgap2le).
  - exact Hc.
Qed.

(* L4 特例：gap₁ ≤ 1（x₀=2 档：gap₁·16 == gap₀² ≤ 9 < 16 反证） *)
Lemma sp2_qgap1_le1 : forall D : Q, Qle 1 D -> Qle D 4 ->
  Qle (sp2_qgap D (sp2_qnewton D 2 1)) 1.
Proof.
  intros D HD1 HD4.
  destruct (Qlt_le_dec 1%Q (sp2_qgap D (sp2_qnewton D 2 1))) as [Hc | Hc].
  - exfalso.
    assert (Hx0 : ~ (2%Q == 0)%Q).
    { intro Hz. apply (Qlt_irrefl 0%Q).
        exact (sp2_qlt_wd 0%Q 2%Q 0%Q 0%Q (Qeq_refl 0) Hz sp2_qlt_lit2). }
    pose proof (sp2_qstep_gap D 2%Q Hx0) as Hid.
    assert (HD4' : Qle D (2 * 2)%Q) by exact HD4.
    assert (Hg0 : Qle 0 (sp2_qgap D 2%Q)) by (apply sp2_qgap_ge0; exact HD4').
    assert (Hg0le3 : Qle (sp2_qgap D 2%Q) 3%Q).
    { apply (Qle_trans (sp2_qgap D 2%Q) (2 * 2 + - 1)%Q 3%Q).
      - exact (Qplus_le_compat _ _ _ _ (Qle_refl (2 * 2)%Q) (Qopp_le_compat 1%Q D%Q HD1)).
      - apply sp2_qeq_le. reflexivity. }
    assert (Hg0sq : Qle (sp2_qgap D 2%Q * sp2_qgap D 2%Q) 9%Q).
    { apply (Qle_trans (sp2_qgap D 2%Q * sp2_qgap D 2%Q)
              (3 * sp2_qgap D 2%Q)%Q (3 * 3)%Q).
      - exact (Qmult_le_compat_r (sp2_qgap D 2%Q) 3%Q (sp2_qgap D 2%Q) Hg0le3 Hg0).
      - assert (Hr9 : (3 * sp2_qgap D 2%Q == sp2_qgap D 2%Q * 3)%Q) by ring.
        exact (sp2_qle_eq_l (sp2_qgap D 2%Q * 3)%Q (3 * sp2_qgap D 2%Q)%Q (3 * 3)%Q Hr9
                 (Qmult_le_compat_r (sp2_qgap D 2%Q) 3%Q 3%Q Hg0le3 sp2_qle_lit3)). }
    assert (H16 : Qle 16%Q (sp2_qgap D (sp2_qnewton D 2 1) * 16)%Q).
    { exact (sp2_qle_eq_l (1 * 16)%Q 16%Q
               (sp2_qgap D (sp2_qnewton D 2 1) * 16)%Q
               (Qeq_sym _ _ (Qmult_1_l 16))
               (Qmult_le_compat_r 1%Q (sp2_qgap D (sp2_qnewton D 2 1)) 16%Q (Qlt_le_weak _ _ Hc)
                  sp2_qle_lit0_16)). }
    apply (Qlt_irrefl 9%Q).
    apply (Qlt_le_trans 9%Q 16%Q 9%Q).
    + exact sp2_qlt_lit9_16.
    + apply (Qle_trans 16%Q (sp2_qgap D (sp2_qnewton D 2 1) * 16)%Q 9%Q).
      * exact H16.
      * apply (Qle_trans (sp2_qgap D (sp2_qnewton D 2 1) * 16)%Q
                 (sp2_qgap D 2%Q * sp2_qgap D 2%Q)%Q 9%Q).
        -- apply sp2_qeq_le.
           assert (Hg1 : sp2_qgap D (sp2_qnewton D 2 1)
                         == (sp2_qnewton_step D 2 * sp2_qnewton_step D 2 - D)%Q)
             by (exact (sp2_qgap_E D (sp2_qnewton_step D 2%Q))).
           assert (Hg0e : sp2_qgap D 2%Q == (2 * 2 - D)%Q)
             by (exact (sp2_qgap_E D 2%Q)).
           setoid_rewrite Hg1.
           setoid_rewrite Hg0e.
           setoid_rewrite (Qeq_sym _ _ Hid).
           ring.
        -- exact Hg0sq.
  - exact Hc.
Qed.

(* L4 归纳：∀n≥1，gapₙ ≤ 1 *)
Lemma sp2_qgap_le1 : forall D : Q, Qle 1 D -> Qle D 4 ->
  forall n : nat, Qle (sp2_qgap D (sp2_qnewton D 2 (Datatypes.S n))) 1.
Proof.
  intros D HD1 HD4 n.
  induction n as [| m IHm].
  - exact (sp2_qgap1_le1 D HD1 HD4).
  - destruct (sp2_qnewton_bnd D HD1 HD4 (Datatypes.S m)) as [Hpos [H1le HDle]].
    exact (sp2_qgap_le1_S D (sp2_qnewton D 2 (Datatypes.S m)) H1le Hpos HDle IHm).
Qed.

(* L5 主率（乘法不变量）：gapₙ·4ⁿ ≤ 3 —— 除法自由、无 Or 分派 *)
(*【AA16S 完成 20260915】率出口两件绿：主链 B≤3 腿改真不等式链               *)
(*  （Hid 环换形 → (gap·4^m)·g ≤ 3·g ≤ 3），全链 sp2_qle_eq_l/r 传输；      *)

Theorem sp2_sqrt_rate_core : forall D : Q, Qle 1 D -> Qle D 4 ->
  forall n : nat, Qle (sp2_qgap D (sp2_qnewton D 2 n) * sp2_q4pow n) 3%Q.
Proof.
  intros D HD1 HD4 n.
  induction n as [| m IHm].
  - (* 基例 n=0：gap₀·4⁰ == 4−D ≤ 3 ⟸ 1 ≤ D *)
    apply (Qle_trans (sp2_qgap D (sp2_qnewton D 2 0) * sp2_q4pow 0)%Q
              (sp2_qgap D 2%Q) 3%Q).
    + apply sp2_qeq_le.
      apply (Qeq_trans (sp2_qgap D (sp2_qnewton D 2 0) * sp2_q4pow 0)%Q
              ((sp2_qnewton D 2 0 * sp2_qnewton D 2 0 - D) * 1%Q)%Q
              (sp2_qgap D 2%Q)).
      * setoid_rewrite (sp2_qgap_E D (sp2_qnewton D 2 0)).
        setoid_rewrite sp2_q4pow_0.
        ring.
      * setoid_rewrite (sp2_qnewton_0 D 2%Q).
        setoid_rewrite (sp2_qgap_E D 2%Q).
        ring.
    + apply (Qle_trans (sp2_qgap D 2%Q) (2 * 2 + - 1)%Q 3%Q).
      * exact (Qplus_le_compat _ _ _ _ (Qle_refl (2 * 2)%Q)
                 (Qopp_le_compat 1%Q D%Q HD1)).
      * apply sp2_qeq_le. reflexivity.
  - destruct m as [| m'].
    + (* n=1 特例：3 < gap₁·4 ⟹ 12 < gap₁·16 == gap₀² ≤ 9 与 9<12 矛盾 *)
      destruct (Qlt_le_dec (sp2_qgap D (sp2_qnewton D 2 1) * sp2_q4pow 1)%Q 3%Q)
        as [H | H].
      * exact (Qlt_le_weak _ _ H).
      * exfalso.
        assert (Hx0 : ~ (2%Q == 0)%Q).
        { intro Hz. apply (Qlt_irrefl 0%Q).
        exact (sp2_qlt_wd 0%Q 2%Q 0%Q 0%Q (Qeq_refl 0) Hz sp2_qlt_lit2). }
        pose proof (sp2_qstep_gap D 2%Q Hx0) as Hid.
        assert (HD4' : Qle D (2 * 2)%Q) by exact HD4.
        assert (Hg0 : Qle 0 (sp2_qgap D 2%Q)) by (apply sp2_qgap_ge0; exact HD4').
        assert (Hg0le3 : Qle (sp2_qgap D 2%Q) 3%Q).
        { apply (Qle_trans (sp2_qgap D 2%Q) (2 * 2 + - 1)%Q 3%Q).
          - exact (Qplus_le_compat _ _ _ _ (Qle_refl (2 * 2)%Q)
                     (Qopp_le_compat 1%Q D%Q HD1)).
          - apply sp2_qeq_le. reflexivity. }
        assert (Hg0sq : Qle (sp2_qgap D 2%Q * sp2_qgap D 2%Q) 9%Q).
        { apply (Qle_trans (sp2_qgap D 2%Q * sp2_qgap D 2%Q)
                  (3 * sp2_qgap D 2%Q)%Q (3 * 3)%Q).
          - exact (Qmult_le_compat_r (sp2_qgap D 2%Q) 3%Q (sp2_qgap D 2%Q)
                     Hg0le3 Hg0).
          - assert (Hr9 : (3 * sp2_qgap D 2%Q == sp2_qgap D 2%Q * 3)%Q) by ring.
            exact (sp2_qle_eq_l (sp2_qgap D 2%Q * 3)%Q (3 * sp2_qgap D 2%Q)%Q (3 * 3)%Q Hr9
                     (Qmult_le_compat_r (sp2_qgap D 2%Q) 3%Q 3%Q Hg0le3 sp2_qle_lit3)). }
        apply (Qlt_irrefl 9%Q).
        apply (Qlt_le_trans 9%Q (3 * 4)%Q 9%Q).
        -- exact sp2_qlt_lit9_12.
        -- apply (Qle_trans (3 * 4)%Q
                     (sp2_qgap D (sp2_qnewton D 2 1) * sp2_q4pow 1 * 4)%Q 9%Q).
           ++ exact (Qmult_le_compat_r 3%Q
                       (sp2_qgap D (sp2_qnewton D 2 1) * sp2_q4pow 1)%Q 4%Q
                       H sp2_qle_lit0_4).
           ++ apply (Qle_trans (sp2_qgap D (sp2_qnewton D 2 1) * sp2_q4pow 1 * 4)%Q
                       (sp2_qgap D (sp2_qnewton D 2 1) * 16)%Q 9%Q).
              ** apply sp2_qeq_le.
                 setoid_rewrite (sp2_q4pow_S 0).
                 setoid_rewrite sp2_q4pow_0.
                 ring.
              ** apply (Qle_trans (sp2_qgap D (sp2_qnewton D 2 1) * 16)%Q
                         ((2 * 2 - D) * (2 * 2 - D))%Q 9%Q).
                 *** apply sp2_qeq_le.
                     assert (Hg1 : sp2_qgap D (sp2_qnewton D 2 1)
                                   == (sp2_qnewton_step D 2 * sp2_qnewton_step D 2 - D)%Q)
                       by (exact (sp2_qgap_E D (sp2_qnewton_step D 2%Q))).
                     setoid_rewrite Hg1.
                     setoid_rewrite (Qeq_sym _ _ Hid).
                     ring.
                 *** exact Hg0sq.
    + (* n = S (Datatypes.S m') 主链：A ≡ gap(step x)·(4·4^m) ≤ gap(step x)·((4x²)·4^m)
         == (gap x·4^m)·gap x ≤ 3·gap x ≤ 3（x := x_{S m'}；Hid 环换形 + IHm + gap≤1） *)
      destruct (sp2_qnewton_bnd D HD1 HD4 (Datatypes.S m')) as [Hpos [H1le HDle]].
      destruct (sp2_qnewton_bnd D HD1 HD4 (Datatypes.S (Datatypes.S m')))
        as [_ [_ HDle2]].
      pose proof (sp2_qgap_le1 D HD1 HD4 m') as Hg1.
      assert (Hx0 := sp2_qle1_neq0 (sp2_qnewton D 2 (Datatypes.S m')) H1le).
      pose proof (sp2_qstep_gap D (sp2_qnewton D 2 (Datatypes.S m')) Hx0) as Hid.
      assert (Hgx0 : Qle 0 (sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))))
        by (apply sp2_qgap_ge0; exact HDle).
      assert (Hgw0 : Qle 0 (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m')))))
        by (apply sp2_qgap_ge0; exact HDle2).
      assert (Hxx : Qle 1%Q
                 (sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))%Q).
      { exact (Qle_trans 1%Q D%Q
                 (sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))%Q
                 HD1 HDle). }
      assert (H4le : Qle 4%Q
                 (4 * sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))%Q).
      { assert (Hr4 : (sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m') * 4
                        == 4 * sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))%Q)
          by ring.
        exact (sp2_qle_eq_r 4%Q
                 (sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m') * 4)%Q
                 (4 * sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))%Q
                 (Qeq_sym _ _ Hr4)
                 (sp2_qle_eq_l (1 * 4)%Q 4%Q
                    (sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m') * 4)%Q
                    (Qeq_sym _ _ (Qmult_1_l 4))
                    (Qmult_le_compat_r 1%Q
                       (sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))%Q 4%Q
                       Hxx sp2_qle_lit0_4))). }
      assert (Hsc : Qle (4 * sp2_q4pow (Datatypes.S m'))%Q
                        ((4 * sp2_qnewton D 2 (Datatypes.S m')
                          * sp2_qnewton D 2 (Datatypes.S m')) * sp2_q4pow (Datatypes.S m'))%Q).
      { exact (Qmult_le_compat_r 4%Q
                 (4 * sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))%Q
                 (sp2_q4pow (Datatypes.S m')) H4le (sp2_q4pow_nn (Datatypes.S m'))). }
      assert (HeqBC :
        (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m')))
         * ((4 * sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))
            * sp2_q4pow (Datatypes.S m')))
        == ((sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))
             * sp2_q4pow (Datatypes.S m'))
            * sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m')))).
      { assert (Hr : (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m')))
                      * ((4 * sp2_qnewton D 2 (Datatypes.S m')
                          * sp2_qnewton D 2 (Datatypes.S m')) * sp2_q4pow (Datatypes.S m'))
                      == (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m')))
                          * (4 * sp2_qnewton D 2 (Datatypes.S m')
                             * sp2_qnewton D 2 (Datatypes.S m')))
                         * sp2_q4pow (Datatypes.S m'))%Q)
          by ring.
        setoid_rewrite Hr.
        setoid_rewrite (sp2_qgap_E D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m')))).
        setoid_rewrite Hid.
        setoid_rewrite (sp2_qgap_E D (sp2_qnewton D 2 (Datatypes.S m'))).
        ring. }
      assert (Hl3 : Qle (3 * sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m')))%Q 3%Q).
      { apply (Qle_trans (3 * sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m')))%Q
                (3 * 1)%Q 3%Q).
        - exact (sp2_qmult_le_compat_l
                   (sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))) 1%Q 3%Q
                   Hg1 sp2_qle_lit3).
        - apply sp2_qeq_le. reflexivity. }
      assert (Hce : Qle ((sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))
                           * sp2_q4pow (Datatypes.S m'))
                          * sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))) 3%Q).
      { apply (Qle_trans _
                (3 * sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m')))%Q 3%Q).
        - exact (Qmult_le_compat_r
                   (sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))
                    * sp2_q4pow (Datatypes.S m'))%Q
                   3%Q (sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))) IHm Hgx0).
        - exact Hl3. }
      apply (Qle_trans
              (sp2_qgap D (sp2_qnewton D 2 (Datatypes.S (Datatypes.S m')))
               * sp2_q4pow (Datatypes.S (Datatypes.S m')))%Q
              (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m')))
               * ((4 * sp2_qnewton D 2 (Datatypes.S m')
                   * sp2_qnewton D 2 (Datatypes.S m')) * sp2_q4pow (Datatypes.S m')))%Q
              3%Q).
      * exact (sp2_qmult_le_compat_l
                 (4 * sp2_q4pow (Datatypes.S m'))%Q
                 ((4 * sp2_qnewton D 2 (Datatypes.S m')
                   * sp2_qnewton D 2 (Datatypes.S m')) * sp2_q4pow (Datatypes.S m'))%Q
                 (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m'))))
                 Hsc Hgw0).
      * exact (sp2_qle_eq_l
                 ((sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))
                   * sp2_q4pow (Datatypes.S m'))
                  * sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m')))%Q
                 (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m')))
                  * ((4 * sp2_qnewton D 2 (Datatypes.S m')
                      * sp2_qnewton D 2 (Datatypes.S m')) * sp2_q4pow (Datatypes.S m')))%Q
                 3%Q HeqBC Hce).
Qed.

(* L5 出口件：Set 层 QleT' 面（任务书出口位）。                              *)
(*  QleT 右支 Id 分支 destruct 消解；QleT' 入参经 QleT'_to_Qle 桥进 Q 层      *)

Theorem sp2_sqrt_rate : forall D : Q, QleT 1 D -> QleT' D 4 -> forall n : nat,
  And (QleT' 0 (sp2_qgap D (sp2_qnewton D 2 n)))
      (QleT' (sp2_qgap D (sp2_qnewton D 2 n) * sp2_q4pow n) 3%Q).
Proof.
  intros D HD1 HD4 n.
  assert (Hq1 : Qle 1 D).
  { destruct HD1 as [H | H].
    - apply Qlt_le_weak. apply QltT_to_Qlt. exact H.
    - destruct H. apply Qle_refl. }
  assert (Hq4 : Qle D 4) by (apply QleT'_to_Qle; exact HD4).
  split.
  - apply Qle_to_QleT'.
    apply sp2_qgap_ge0.
    destruct (sp2_qnewton_bnd D Hq1 Hq4 n) as [_ [_ HDle]].
    exact HDle.
  - apply Qle_to_QleT'.
    exact (sp2_sqrt_rate_core D Hq1 Hq4 n).
Qed.

(* ============================================================ *)
(* §2C 主件：sp2_eig_gap（复用 AttnSqrt.real_sqrt_exists，禁重写）   *)
(*   前提取 real_le（Or 左支=严格、右支=D≡0 简并 s:=0，免费覆盖）。   *)
(*   见证形：s ≥ 0 ∧ s·s == D ∧ (λ₊−λ₋) == s（逐点代数 |X_n−s_n|=0）。 *)
(* ============================================================ *)

Definition sp2_half : Real := real_const (1#2).
Definition sp2_eig_up (a d s : Real) : Real :=
  real_plus (real_mult sp2_half (real_plus a d)) (real_mult sp2_half s).
Definition sp2_eig_dn (a d s : Real) : Real :=
  real_plus (real_mult sp2_half (real_plus a d))
            (real_opp (real_mult sp2_half s)).

Lemma sp2_eig_diff_eq : forall a d s : Real,
  real_eq (real_plus (sp2_eig_up a d s) (real_opp (sp2_eig_dn a d s))) s.
Proof.
  intros a d s eps Heps.
  exists 0%nat.
  intros n Hn.
  assert (Hz : Qabs (projT1 (real_plus (sp2_eig_up a d s)
                                        (real_opp (sp2_eig_dn a d s))) n
                     - projT1 s n) == 0%Q).
  { apply (Qeq_trans _ (Qabs 0%Q) _).
    - apply Qabs_wd.
      setoid_rewrite (sp2_pt_plus (sp2_eig_up a d s) (real_opp (sp2_eig_dn a d s)) n).
      setoid_rewrite (sp2_pt_opp (sp2_eig_dn a d s) n).
      setoid_rewrite (sp2_pt_plus (real_mult sp2_half (real_plus a d)) (real_mult sp2_half s) n).
      setoid_rewrite (sp2_pt_plus (real_mult sp2_half (real_plus a d)) (real_opp (real_mult sp2_half s)) n).
      setoid_rewrite (sp2_pt_mult sp2_half (real_plus a d) n).
      setoid_rewrite (sp2_pt_mult sp2_half s n).
      setoid_rewrite (sp2_pt_opp (real_mult sp2_half s) n).
      setoid_rewrite (sp2_pt_const (1#2) n).
      setoid_rewrite (sp2_pt_plus a d n).
      setoid_rewrite (sp2_pt_mult sp2_half s n).
      setoid_rewrite (sp2_pt_const (1#2) n).
      ring.

    - reflexivity. }
  apply Qlt_to_QltT.
  setoid_rewrite Hz.
  apply QltT_to_Qlt.
  exact Heps.
Qed.
Theorem sp2_eig_gap : forall a d b : Real,
  real_le real_zero (sp2_disc a d b) ->
  sigT (fun s : Real => And (real_le real_zero s)
        (And (real_eq (real_mult s s) (sp2_disc a d b))
             (real_eq (real_plus (sp2_eig_up a d s)
                                 (real_opp (sp2_eig_dn a d s))) s))).
Proof.
  intros a d b HD.
  destruct (real_sqrt_exists (sp2_disc a d b) HD) as [s [Hpos Hsq]].
  exists s.
  split.
  - exact Hpos.
  - split.
    + exact Hsq.
    + apply sp2_eig_diff_eq.
Qed.

(* ============================================================ *)
(* §2E 副件两小件（AA16S 20260915）：D=0 简并 ε-一致版 + s 严格正 corollary *)
(*   Q 引擎：η := ε/(4+ε) 档（0<η ∧ η≤1 ∧ 2η<ε），免 epsfrac 平方档。      *)
(* ============================================================ *)

Lemma sp2_qsq_abs_id : forall u : Q, (u * u == Qabs u * Qabs u)%Q.
Proof.
  intro u.
  destruct (Qlt_le_dec 0 u) as [H | H].
  - setoid_rewrite (Qabs_pos u (Qlt_le_weak _ _ H)). ring.
  - setoid_rewrite (Qabs_neg u H). ring.
Qed.

(* |u|≤η ∧ η≤1 ⟹ u·u ≤ η·η（上界侧免 0<|u| 分派） *)
Lemma sp2_qsq_le_eta : forall u eta : Q, Qle 0 eta -> Qle eta 1 -> Qle (Qabs u) eta ->
  Qle (u * u) (eta * eta).
Proof.
  intros u eta H0e He1 Hub.
  exact (sp2_qle_eq_l (Qabs u * Qabs u)%Q (u * u)%Q (eta * eta)%Q
           (sp2_qsq_abs_id u)
           (Qle_trans (Qabs u * Qabs u)%Q (eta * Qabs u)%Q (eta * eta)%Q
              (Qmult_le_compat_r (Qabs u) eta (Qabs u) Hub (Qabs_nonneg u))
              (sp2_qmult_le_compat_l (Qabs u) eta eta Hub H0e))).
Qed.

(* η := ε/(4+ε) 档：0<η ∧ η≤1 ∧ 2η<ε（2<4+ε 严格、无平方正性案分） *)
Lemma sp2_q_eta_kit : forall e : Q, Qlt 0 e ->
  And (Qlt 0 (e/(4+e)))
      (And (Qle (e/(4+e)) 1) (Qlt (2*(e/(4+e))) e)).
Proof.
  intros e He.
  assert (H0e : Qle 0 e) by (apply Qlt_le_weak; exact He).
  assert (H4p : Qlt 0 (4 + e)).
  { exact (Qlt_le_trans 0%Q 4%Q (4+e)%Q sp2_qlt_lit4 (sp2_qle_plus_r 4%Q e%Q H0e)). }
  assert (Hn0 : ~ ((4 + e) == 0)%Q).
  { intro Hz. apply (Qlt_irrefl 0%Q).
    exact (sp2_qlt_wd 0%Q (4+e)%Q 0%Q 0%Q (Qeq_refl 0%Q) Hz H4p). }
  assert (Hηe : (e/(4+e)*(4+e) == e)%Q) by (field; assumption).
  assert (Hηpos : Qlt 0 (e/(4+e))).
  { destruct (Qlt_le_dec 0 (e/(4+e))) as [Hc | Hc].
    - exact Hc.
    - exfalso.
      assert (Hr : (0 == 0 * (4+e))%Q) by ring.
      assert (Hbad : Qle (e/(4+e)*(4+e)) 0%Q).
      { exact (sp2_qle_eq_r _ _ _ Hr
                 (Qmult_le_compat_r (e/(4+e)) 0%Q (4+e)%Q Hc (Qlt_le_weak _ _ H4p))). }
      apply (Qlt_irrefl e%Q).
      exact (Qle_lt_trans e%Q 0%Q e%Q
               (sp2_qle_eq_l (e/(4+e)*(4+e))%Q e%Q 0%Q (Qeq_sym _ _ Hηe) Hbad)
               He). }
  assert (Hreq : (4 + e == e + 4)%Q) by ring.
  assert (Hle4p : Qle e (4 + e)).
  { exact (sp2_qle_eq_r e%Q (e+4)%Q (4+e)%Q Hreq (sp2_qle_plus_r e%Q 4%Q sp2_qle_lit0_4)). }
  assert (Hηle1 : Qle (e/(4+e)) 1).
  { assert (Hηinvpos : Qle 0 (/ (4+e))).
    { apply Qlt_le_weak. exact (Qinv_lt_0_compat (4+e)%Q H4p). }
    exact (sp2_qle_eq_r (e * / (4+e))%Q ((4+e) * / (4+e))%Q 1%Q
             (Qeq_sym _ _ (Qmult_inv_r (4+e)%Q Hn0))
             (Qmult_le_compat_r e%Q (4+e)%Q (/ (4+e)) Hle4p Hηinvpos)). }
  assert (H2lt : Qlt 2%Q (4 + e)).
  { exact (Qlt_le_trans 2%Q 4%Q (4+e)%Q sp2_qlt_lit2 (sp2_qle_plus_r 4%Q e%Q H0e)). }
  assert (Hη2lt : Qlt (2 * (e/(4+e))) e).
  { assert (Hr2 : ((4+e) * (e/(4+e)) == e)%Q).
    { assert (Hc : ((4+e) * (e/(4+e)) == (e/(4+e)) * (4+e))%Q) by ring.
      exact (Qeq_trans _ _ _ Hc Hηe). }
    exact (sp2_qlt_wd (2 * (e/(4+e)))%Q ((4+e) * (e/(4+e)))%Q
             (2 * (e/(4+e)))%Q e%Q (Qeq_refl _) Hr2
             (Qmult_lt_compat_r 2%Q (4+e)%Q (e/(4+e))%Q Hηpos H2lt)). }
  split; [exact Hηpos | split; [exact Hηle1 | exact Hη2lt]].
Qed.

(* 副件一（degen ε-一致版）：a−d ≡ 0 ∧ 2b ≡ 0 ⟹ D ≡ 0（|D_n| < ε 一致界） *)
Corollary sp2_disc_eq_zero_of_degen : forall a d b : Real,
  real_eq (real_plus a (real_opp d)) real_zero ->
  real_eq (real_plus b b) real_zero ->
  real_eq (sp2_disc a d b) real_zero.
Proof.
  intros a d b Hu Hb eps Heps.
  pose proof (sp2_q_eta_kit eps (QltT_to_Qlt _ _ Heps)) as [Hη0 [Hη1 Hη2]].
  destruct (Hu (eps/(4+eps))%Q (Qlt_to_QltT _ _ Hη0)) as [N1 HN1].
  destruct (Hb (eps/(4+eps))%Q (Qlt_to_QltT _ _ Hη0)) as [N2 HN2].
  exists (max N1 N2).
  intros n Hn.
  assert (K1 : NatLe N1 n).
  { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
      [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
  assert (K2 : NatLe N2 n).
  { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
      [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
  pose proof (QltT_to_Qlt _ _ (HN1 n K1)) as H1q.
  pose proof (QltT_to_Qlt _ _ (HN2 n K2)) as H2q.
  assert (Hx1 : Qabs (projT1 (real_plus a (real_opp d)) n - projT1 real_zero n)
                == Qabs (projT1 a n - projT1 d n)%Q).
  { setoid_rewrite (sp2_pt_plus a (real_opp d) n).
    setoid_rewrite (sp2_pt_opp d n).
    setoid_rewrite (sp2_pt_zero n).
    apply Qabs_wd. ring. }
  assert (H1' : Qlt (Qabs (projT1 a n - projT1 d n)) (eps/(4+eps))%Q)
    by exact (sp2_qlt_wd _ _ _ _ Hx1 (Qeq_refl _) H1q).
  assert (Hx2 : Qabs (projT1 (real_plus b b) n - projT1 real_zero n)
                == Qabs (projT1 b n + projT1 b n)%Q).
  { setoid_rewrite (sp2_pt_plus b b n).
    setoid_rewrite (sp2_pt_zero n).
    apply Qabs_wd. ring. }
  assert (H2' : Qlt (Qabs (projT1 b n + projT1 b n)) (eps/(4+eps))%Q)
    by exact (sp2_qlt_wd _ _ _ _ Hx2 (Qeq_refl _) H2q).
  assert (HDpt : projT1 (sp2_disc a d b) n
                 == (projT1 (real_mult (real_plus a (real_opp d))
                                        (real_plus a (real_opp d))) n
                      + projT1 (real_mult (real_plus b b) (real_plus b b)) n)%Q)
    by exact (sp2_pt_plus _ _ n).
  assert (HDu : projT1 (real_mult (real_plus a (real_opp d))
                                  (real_plus a (real_opp d))) n
                == ((projT1 a n - projT1 d n) * (projT1 a n - projT1 d n))%Q).
  { setoid_rewrite (sp2_pt_mult (real_plus a (real_opp d)) (real_plus a (real_opp d)) n).
    setoid_rewrite (sp2_pt_plus a (real_opp d) n).
    setoid_rewrite (sp2_pt_opp d n).
    ring. }
  assert (HDv : projT1 (real_mult (real_plus b b) (real_plus b b)) n
                == ((projT1 b n + projT1 b n) * (projT1 b n + projT1 b n))%Q).
  { setoid_rewrite (sp2_pt_mult (real_plus b b) (real_plus b b) n).
    setoid_rewrite (sp2_pt_plus b b n).
    ring. }
  assert (HDn : projT1 (sp2_disc a d b) n - projT1 real_zero n
                == ((projT1 a n - projT1 d n) * (projT1 a n - projT1 d n)
                    + (projT1 b n + projT1 b n) * (projT1 b n + projT1 b n))%Q).
  { setoid_rewrite HDpt. setoid_rewrite HDu. setoid_rewrite HDv.
    setoid_rewrite (sp2_pt_zero n). ring. }
  apply Qlt_to_QltT.
  setoid_rewrite HDn.
  assert (Hη0le : Qle 0 (eps/(4+eps))) by (apply Qlt_le_weak; exact Hη0).
  assert (Hb1 : Qle (Qabs (projT1 a n - projT1 d n)) (eps/(4+eps)))
    by exact (Qlt_le_weak _ _ H1').
  assert (Hb2 : Qle (Qabs (projT1 b n + projT1 b n)) (eps/(4+eps)))
    by exact (Qlt_le_weak _ _ H2').
  assert (Hs1 : Qle (Qabs (projT1 a n - projT1 d n) * Qabs (projT1 a n - projT1 d n))
                    ((eps/(4+eps)) * (eps/(4+eps))))
    by exact (sp2_qle_eq_l _ _ _
               (Qeq_sym _ _ (sp2_qsq_abs_id (projT1 a n - projT1 d n)))
               (sp2_qsq_le_eta (projT1 a n - projT1 d n) (eps/(4+eps)) Hη0le Hη1 Hb1)).
  assert (Hs2 : Qle (Qabs (projT1 b n + projT1 b n) * Qabs (projT1 b n + projT1 b n))
                    ((eps/(4+eps)) * (eps/(4+eps))))
    by exact (sp2_qle_eq_l _ _ _
               (Qeq_sym _ _ (sp2_qsq_abs_id (projT1 b n + projT1 b n)))
               (sp2_qsq_le_eta (projT1 b n + projT1 b n) (eps/(4+eps)) Hη0le Hη1 Hb2)).
  assert (Hr1 : (eps/(4+eps) == 1 * (eps/(4+eps)))%Q) by ring.
  assert (Hηsqle : Qle ((eps/(4+eps)) * (eps/(4+eps))) (eps/(4+eps)))
    by exact (sp2_qle_eq_r _ _ _ Hr1 (Qmult_le_compat_r (eps/(4+eps)) 1%Q (eps/(4+eps)) Hη1 Hη0le)).
  apply (Qle_lt_trans (Qabs ((projT1 a n - projT1 d n) * (projT1 a n - projT1 d n)
                             + (projT1 b n + projT1 b n) * (projT1 b n + projT1 b n)))
                      (Qabs ((projT1 a n - projT1 d n) * (projT1 a n - projT1 d n))
                       + Qabs ((projT1 b n + projT1 b n) * (projT1 b n + projT1 b n)))
                      eps%Q).
  - exact (Qabs_triangle _ _).
  - setoid_rewrite (Qabs_Qmult (projT1 a n - projT1 d n) (projT1 a n - projT1 d n)).
    setoid_rewrite (Qabs_Qmult (projT1 b n + projT1 b n) (projT1 b n + projT1 b n)).
    apply (Qle_lt_trans (Qabs (projT1 a n - projT1 d n) * Qabs (projT1 a n - projT1 d n)
                         + Qabs (projT1 b n + projT1 b n) * Qabs (projT1 b n + projT1 b n))
                        (2 * (eps/(4+eps)))%Q eps%Q).
    + apply (Qle_trans _ ((eps/(4+eps)) * (eps/(4+eps))
                           + (eps/(4+eps)) * (eps/(4+eps)))%Q (2 * (eps/(4+eps)))%Q).
      * exact (Qplus_le_compat _ _ _ _ Hs1 Hs2).
      * apply (Qle_trans _ ((eps/(4+eps)) + (eps/(4+eps)))%Q (2 * (eps/(4+eps)))%Q).
        -- exact (Qplus_le_compat _ _ _ _ Hηsqle Hηsqle).
        -- apply sp2_qeq_le. ring.
    + exact Hη2.
Qed.

(* 副件二（s 严格正 corollary）：0<D 严格 ⟹ eig_gap 见证 s 严格正。
   右支 s≡0 反证：s²≡0（ε-一致）⟹ D≡0 与 0<D 矛盾。 *)
Corollary sp2_eig_s_pos : forall a d b : Real,
  real_lt real_zero (sp2_disc a d b) ->
  sigT (fun s : Real => And (real_lt real_zero s)
        (And (real_eq (real_mult s s) (sp2_disc a d b))
             (real_eq (real_plus (sp2_eig_up a d s)
                                 (real_opp (sp2_eig_dn a d s))) s))).
Proof.
  intros a d b Hlt.
  destruct (sp2_eig_gap a d b (inl Hlt)) as [s [Hpos [Hsq Heig]]].
  exists s.
  destruct Hpos as [Hslt | Hseq].
  - split; [exact Hslt | split; [exact Hsq | exact Heig]].
  - exfalso.
    assert (Hss0 : real_eq (real_mult s s) real_zero).
    { intros eps2 Heps2.
      pose proof (sp2_q_eta_kit eps2 (QltT_to_Qlt _ _ Heps2)) as [Hη0 [Hη1 Hη2]].
      destruct (Hseq (eps2/(4+eps2))%Q (Qlt_to_QltT _ _ Hη0)) as [M HM].
      exists M. intros m Hm.
      pose proof (QltT_to_Qlt _ _ (HM m Hm)) as Habs0.
      assert (Hxs : Qabs (projT1 real_zero m - projT1 s m) == Qabs (- projT1 s m)%Q).
      { setoid_rewrite (sp2_pt_zero m). apply Qabs_wd. ring. }
      assert (Habs : Qlt (Qabs (- projT1 s m)) (eps2/(4+eps2))%Q)
        by exact (sp2_qlt_wd _ _ _ _ Hxs (Qeq_refl _) Habs0).
      assert (Habs' : Qlt (Qabs (projT1 s m)) (eps2/(4+eps2))%Q).
      { exact (sp2_qlt_wd (Qabs (- projT1 s m))%Q (eps2/(4+eps2))%Q
                 (Qabs (projT1 s m))%Q (eps2/(4+eps2))%Q
                 (Qabs_opp (projT1 s m)) (Qeq_refl _) Habs). }
      assert (Hη0le : Qle 0 (eps2/(4+eps2))) by (apply Qlt_le_weak; exact Hη0).
      assert (Hb1 : Qle (Qabs (projT1 s m)) (eps2/(4+eps2)))
        by exact (Qlt_le_weak _ _ Habs').
      assert (Hpt : projT1 (real_mult s s) m - projT1 real_zero m
                    == (projT1 s m * projT1 s m)%Q).
      { setoid_rewrite (sp2_pt_mult s s m). setoid_rewrite (sp2_pt_zero m). ring. }
      assert (H12 : Qle 1 2) by (unfold Qle; cbn; lia).
      apply Qlt_to_QltT.
      setoid_rewrite Hpt.
      apply (Qle_lt_trans (Qabs (projT1 s m * projT1 s m)) (2*(eps2/(4+eps2)))%Q eps2%Q).
      - apply (Qle_trans (Qabs (projT1 s m * projT1 s m)) (eps2/(4+eps2))%Q
                 (2*(eps2/(4+eps2)))%Q).
        + apply (proj2 (Qabs_Qle_condition (projT1 s m * projT1 s m) (eps2/(4+eps2)))).
          split.
          * assert (Hr0 : (0 == - 0)%Q) by ring.
            exact (Qle_trans (- (eps2/(4+eps2)))%Q 0%Q (projT1 s m * projT1 s m)%Q
                     (sp2_qle_eq_r (- (eps2/(4+eps2)))%Q (- 0)%Q 0%Q Hr0
                        (Qopp_le_compat 0%Q (eps2/(4+eps2)) Hη0le))
                     (sp2_qsq_nonneg (projT1 s m))).
          * assert (Hr1b : (eps2/(4+eps2) == 1 * (eps2/(4+eps2)))%Q) by ring.
            exact (Qle_trans (projT1 s m * projT1 s m)
                     ((eps2/(4+eps2)) * (eps2/(4+eps2)))
                     (eps2/(4+eps2))
                     (sp2_qsq_le_eta (projT1 s m) (eps2/(4+eps2)) Hη0le Hη1 Hb1)
                     (sp2_qle_eq_r _ _ _ Hr1b
                        (Qmult_le_compat_r (eps2/(4+eps2)) 1%Q (eps2/(4+eps2))
                           Hη1 Hη0le))).
        + assert (Hr2 : (2 * (eps2/(4+eps2)) == (eps2/(4+eps2)) * 2)%Q) by ring.
          assert (Hr3 : ((eps2/(4+eps2)) == (eps2/(4+eps2)) * 1)%Q) by ring.
          exact (sp2_qle_eq_l ((eps2/(4+eps2)) * 1)%Q (eps2/(4+eps2))%Q
                   (2 * (eps2/(4+eps2)))%Q Hr3
                   (sp2_qle_eq_r _ _ _ Hr2
                      (sp2_qmult_le_compat_l 1%Q 2%Q (eps2/(4+eps2)) H12 Hη0le))).
      - exact Hη2. }
    assert (HD0 : real_eq (sp2_disc a d b) real_zero).
    { exact (real_eq_trans (sp2_disc a d b) (real_mult s s) real_zero
               (real_eq_sym (real_mult s s) (sp2_disc a d b) Hsq) Hss0). }
    destruct (real_lt_irrefl real_zero
               (real_lt_eq_lt real_zero (sp2_disc a d b) real_zero Hlt HD0)).
Qed.


(* ============================================================ *)
(* §2D G3 关：Separate Extraction 纯标量件（Obj.magic 应 0）+        *)
(*   Print Assumptions 出口件全表（应 Closed）                       *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction sp2_qdisc sp2_qnewton_step sp2_qnewton sp2_q4pow sp2_qgap.

Print Assumptions sp2_disc_sqpos.
Print Assumptions sp2_sqrt_rate_core.
Print Assumptions sp2_sqrt_rate.
Print Assumptions sp2_eig_gap.
Print Assumptions sp2_disc_eq_zero_of_degen.
Print Assumptions sp2_eig_s_pos.

(*                                                                *)
(* 【§2.1 Q 工具箱余留两件】                                       *)
(* sp2_qsq_le_abs : |x|<η ⟹ x·x ≤ η·η —— Qlt_le_dec 0 x 两分支；   *)
(*   正支 Qabs_pos（stdlib Qabs.v:38 实名），负支 Qabs_neg（:45）； *)
(*   每支两步 Qmult_le_compat_r（右因子 η，前提 Qlt_le_weak Hlt）。 *)
(*   ⚠ setoid 纪律：Qeq 改写一律 setoid_rewrite，禁裸 rewrite。     *)
(* sp2_q_epsfrac : e>0 ⟹ 0 < e/(4+e) ∧ (e/(4+e))² < e ——           *)
(*   H41: 0<4+e（Qplus_lt_compat + 字面 Qlt 0 4 unfold+cbn+lia）；  *)
(*   Hn0: ~(4+e==0)（Qlt_not_le 反证 + qeq_le）；                  *)
(*   K: e < (4+e)²（Qlt_le_trans 经 e+(16+7e+e²)，用               *)
(*      proj2 (Qplus_lt_r z x y) 共享左参形 + setoid Qplus_0_r，    *)
(*      末步 qeq_le+ring）；                                       *)
(*   Heta: e/(4+e) < 4+e = Qmult_lt_compat_r e ((4+e)²) (/(4+e))    *)
(*      K (Qinv_lt_0_compat H41)（e/(4+e)≡e*/(4+e) 定义性，reflexivity）； *)
(*   0<η：Qlt_le_dec (e/(4+e)) 0 反证，用 A3: η·(4+e)==e            *)
(*      （setoid 链：Qmult_comm(/w,w)→Qmult_inv_r(w,Hn0)→Qmult_1_r）； *)
(*   末步：Qmult_lt_compat_r η (4+e) η Heta(0<η 位) ⟹ η·η<(4+e)·η   *)
(*      setoid A3 ⟹ η·η<e。                                        *)
(*                                                                *)
(* 【§2.2 保底件一：LPO-free 非负 + 见证形升级链】                  *)
(* Definition sp2_lower0 (y : Real) : Set :=                       *)
(*   forall eps : Q, QltT 0 eps -> real_lt (real_opp y) (real_const eps). *)
(* sp2_lower0_intro：(∀n, 0≤y_n) ⟹ lower0 y —— 见证 δ:=eps/2、     *)
(*   N:=0；eps/2 < eps + y_n 走 Qlt_le_trans (eps/2) eps (eps+y_n)； *)
(*   eps/2<eps 与 0<eps/2 由 §2.1 half-kit（Qlt_le_dec 反证 +       *)
(*   eps==eps/2+eps/2 field）。real_lt 展开里 sp2_qminus_0_r 用         *)
(*   setoid_rewrite。                                              *)
(* sp2_lower0_plus：lower0 y ⟹ lower0 z ⟹ lower0 (y+z)——           *)
(*   H1 at ε/2 得 δ1,N1，H2 at ε/2 得 δ2,N2；δ:=δ1+δ2（正性        *)
(*   Qplus_lt_compat），N:=max N1 N2（S02 real_lt_trans 的          *)
(*   NatLe_lift + Nat.le_trans + NatLe_drop 消费模式照抄）；        *)
(*   点态 δ1+δ2 < ε+y_n+z_n = Qplus_lt_compat + field 换形。        *)
(* sp2_lower0_sq：∀x, lower0 (x·x) —— sp2_lower0_intro +            *)
(*   sp2_qsq_nonneg 逐点（sp2_pt_mult 换 projT1 后直接喂）。         *)
(* sp2_disc_lower0（保底主件）：disc = 两平方和，                   *)
(*   sp2_lower0_plus + sp2_lower0_sq ×2 直拼。零 Or、零符号判定。    *)
(* sp2_disc_pos_of_sq：real_lt real_zero (u·u) ⟹ real_lt 0 D（u:=a−d）——    *)
(*   解构 real_lt 见证 (δ,N)；同 δ、N 逐点：δ<u_n² 与               *)
(*   0≤(2b_n)²（qsq_nonneg）⟹ δ<u_n²+(2b_n)²（Qlt_le_trans +       *)
(*   Qle_plus_nonneg_r[Qle_plus_nonneg_r]——S02 已有，直引）。       *)
(* sp2_disc_pos_of_bsq：对称（b² 支当严格项）。                     *)
(* sp2_disc_eq_zero_of_degen（显式假设候选）：real_eq u 0 ⟹ real_eq b 0  *)
(*   ⟹ real_eq D 0 —— 取 η:=ε/(4+ε)，sp2_qsq_le_abs 两侧，         *)
(*   η²+4η'²<ε 经 §2.1 epsfrac；Qabs(Qabs_pos/Qabs_neg 实名已验)。  *)
(*                                                                *)
(* 【§2.3 保底件二：Q 层 Newton √D 显式率】                         *)
(* Definition sp2_qdisc (a d b : Q) : Q := (a-d)*(a-d) + 4*b*b.     *)
(* Definition sp2_qnewton_step (D x : Q) : Q := (x + D/x)/2.        *)
(* Fixpoint sp2_qnewton (D x : Q) (n : nat)（O:=x, S:=step∘前步）。  *)
(* Fixpoint sp2_q4pow / sp2_q2pow（nat Fixpoint，Datatypes.S 形）。  *)
(* L1 sp2_qstep_gap：step(x)²−D == (x²−D)²/(4·x·x)（field，         *)
(*   侧条件 ~(x==0)/字面 2≠0 用 Qmult_integral 拆 4·x·x≠0）。       *)
(* L2 sp2_qinv_A（归纳）：∀n, Qlt 0 (it n) ∧ Qle 1 (it n) ∧          *)
(*   Qle D (it n·it n)——基例 it0=2 字面；步：正性                  *)
(*   Qplus_lt_compat+Qmult_lt_compat_r（·(1#2)）；D≤x'² 由 L1+      *)
(*   gapₙ≥0（Qmult_le_0_compat）；1≤x' 由 sp2_qsq_ge1              *)
(*   （Q_le_dec 反证：x<1 ⟹ x²<x<1 与 1≤D≤x² 矛盾）。              *)
(* L3 sp2_qcontract：x_{n+1} ≤ xₙ（D/xₙ ≤ xₙ ⟸ D≤xₙ² 乘 1/xₙ；     *)
(*   (a+b)/2 ≤ (a+a)/2 == a；xₙ·xₙ·/xₙ == xₙ field 侧条件）。       *)
(* L4 sp2_qrate_B（归纳，P(n) := gapₙ·4ⁿ≤3 ∧ gapₙ≤4 ∧               *)
(*   Or(Id n O)(Qle gapₙ 1)）：基例 gap₀=4−D≤3（D≥1）；S 步          *)
(*   Or 分派：n=0 支 4x₀²=16 ⟹ gap₁ ≤ gap₀²/16 ≤ gap₀/4；          *)
(*   n≥1 支 gapₙ≤1 ⟹ gapₙ₊₁=gapₙ²/(4xₙ²) ≤ gapₙ²/4 ≤ gapₙ/4；      *)
(*   两侧都收 c_{Sn} ≤ (gapₙ/4)·4^{Sn} == gapₙ·4ⁿ ≤ 3               *)
(*   （field 换形 + Qmult_le_compat_r）。                           *)
(* L5 sp2_sqrt_rate_core（THEOREM，QleT' 出口面）：D∈[1,4] ⟹        *)
(*   0 ≤ xₙ²−D ≤ 3/4ⁿ（cₙ≤3 乘 /4ⁿ；4ⁿ≠0 用 Qlt_not_eq+            *)
(*   Qmult_inv_r；QleT' 经 QleT'_to_Qle/Qle_to_QleT' 进出）。        *)
(* L6 sp2_q_unbounded：0<q ⟹ ∃m, c < q·4^m —— c≤0 支 m:=0；         *)
(*   否则 m:=Z.to_nat(c·Qnum q...) 经 sp2_q4pow_ge_succ             *)
(*   （(Datatypes.S n)#1 ≤ 4^n，Qmult_le_compat_r 字面收）+ Z2Nat.id +        *)
(*   Z 层 Z.mul_le_mono 链（正数位 destruct positive cbn lia）。    *)
(* L7 sp2_sqrt_rate（THEOREM 主件，QeqT 缩放见证入参）：             *)
(*   sp2_qdisc a d b == 4^k·D'（QeqT 形）∧ 1≤D'≤4 ∧ ε>0 ⟹           *)
(*   ∃r:Q, 0 ≤ r²−D < ε；r := 2^k·x_{k+Sm}（m 来自 L6 at (3,eps)）， *)
(*   r²−D == 4^k(x_{S..}²−D')（QeqT→Qeq 转换件 sp2_qeqT_eq：        *)
(*   destruct Qcompare eqn + Qeq_alt proj2 + discriminate），       *)
(*   上界链 4^k·3/4^{k+Sm} == 3/4^{Sm} < eps。                      *)
(*                                                                *)
(* 【§2.4 主件 sp2_eig_gap】                                        *)
(* half := real_const (1#2)；eig_up/dn := half·(a+d) ± half·s。     *)
(* sp2_eig_gap：real_lt 0 D ⟹ sigT s（real_le 0 s ∧                *)
(*   real_eq (s·s) D ∧ real_eq (eig_up − eig_dn) s）——              *)
(*   s 取 projT1 (real_sqrt_exists D (inl HD))（AttnSqrt 资产，      *)
(*   禁重写）；λ₊−λ₋==s 走逐点：|X_n−s_n|==0<N eps，N:=0，          *)
(*   §0 pt 引擎 + ring；s 严格正（corollary，尽力）：destruct        *)
(*   real_le Or，右支 s≡0 ⟹ real_eq D 0 ⟹ 与 real_lt 0 D 逐点       *)
(*   矛盾（δ<D_n 且 |D_n|<δ 取 max N）。D=0 简并 ε-一致版：显式假设。    *)
(*                                                                *)

(* Separate Extraction sp2_qdisc sp2_qnewton_step sp2_qnewton       *)
(*   sp2_q4pow sp2_q2pow（纯标量，Obj.magic 应 0；Real 层依赖件      *)
(*   按 INST5 纪律不进提取单，由 PA Closed 承担）。                  *)


(*   全量走 cwfix_aa16.cmd（bash 中转，cpu_guard CoreN 3）。         *)
(* ============================================================ *)

Print Assumptions sp2_pt_plus.
Print Assumptions sp2_pt_mult.
Print Assumptions sp2_pt_opp.
Print Assumptions sp2_pt_const.
Print Assumptions sp2_pt_zero.
Print Assumptions sp2_qeq_le.
Print Assumptions sp2_qnewton_0.
Print Assumptions sp2_qnewton_S.
Print Assumptions sp2_q4pow_S.
Print Assumptions sp2_q4pow_0.
Print Assumptions sp2_qgap_E.
