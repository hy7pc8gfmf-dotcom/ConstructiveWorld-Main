(* 五字段指针｜使命：√5 闭式分离常元主定理——√2 首件闭式无理性测度向 √5 的
   全套推广。对任意有理数 q = a/b（b 为正分母），显式常元 c(q) = 1/(16·b²) 满足 QltT 0 c 且 real_const c < |√5 − q|（Newton 序列 x(0)=9/4、
   x(n+1)=(x(n)+5/x(n))/2 之极限的实度量）。此为 Liouville 型下界 |√5 − a/b| > C/b² 的构造性显式实现，常元由 Qeq 确定、可提取可复算。
   常元确定链（诚实申报）：确定 C=16。自建锐衰减 dms5_e_sharp （e(n)·5184·2^n ≤ 1，基底值 e(1)=1/10368 精确值逐半推进，较通用
   2^-(n+1) 形锐 2592 倍）+ u5c_pow4（4k² ≤ 2^(k+3)）得统一 e 界 e(n0) ≤ 1/(16b²)（16b² ≤ 4·2^(b+3) ≤ 5184·2^(b+3)）；
   四分支边距归一为 3/(16b²) ≤ |q−x(n0)|：分支一 q≤0 需 3/16 ≤ 9/5 ✓； 分支二 0<q 且 q²<5 需 3/16 ≤ 2/9（27 ≤ 32 ✓，点态下界 (5−q²)·2/9，
   整隙 5b²−a² ≥ 1）；分支三 5<q²≤(9/4)² 需 3/16 ≤ 7/36（108 ≤ 112 ✓， 由 q−x = (μ−δ)/(q+x) ≥ (2/9)(μ−δ)、μ ≥ 1/b² 整隙、δ=2e ≤ 1/(8b²)
   得 μ−δ ≥ 7/(8b²)）；分支四 q>9/4 需 3/16 ≤ 1/(4b)（12b ≤ 16b² ✓， 整隙 4a−9b ≥ 1）。拒 12 档申报：C=12 时分支二需 1/4 ≤ 2/9 即
   9 ≤ 8，假——12 档数学不可达，非工程妥协；16 档全分支成立。 证明结构：①统一逃逸窗口 dms5_escape_closed_window：n0 := Z.to_nat (Z.pos b) + 3
   四分支给出 e(n0) < |q−x(n0)|；②三倍边距核 dms5_margin_trine： 3/(16b²) ≤ |q−x(n0)|（四分支 Qle 链、证体内 Prop 合法）；③边距成形：
   c+c+e(n0) ≤ 3/(16b²) ≤ |q−x(n0)| 经 lic_qlt_minus_add_r 移项与 u5c_qle_add_cancel_r 右端消去得 QleT' (c+c) (|q−x(n0)|−e(n0))；
   ④装配边距参数化通用桥 dmec_escape_to_dist_any（任意 c ≤ 边距/2 皆分离）与 Qeq_refl 确定。推论 u5c_sqrt5_closed_measure_q
   重述为任意 Q 的 q 形（QDen 确定）。自携 dms5_ 前缀副本之语句面逐条对应上游 √5 实例件 u5c_inst_sqrt5.v（该件居上游树、不在本池
   加载路径，故自携副本；衰减/幂界按 √5 实际命名面实例化并增锐化段）。 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、SumInvFactEscape、
   UpReqBanachNormOpp、UpReqIrrationalCriterion、UpReqSqrt3Irrational、 u5c_aux_natpow（已完成：u5c_pow4/u5c_qle_add_cancel_r 复用）、
   u5c_dm_escape_to_dist_any（已完成：通用桥复用）；Stdlib
   QArith、Qabs、ZArith、Arith、Bool、Lia、Setoid、Morphisms、Qfield。
   对标行：#225/ConstructiveWorld_vo/u5c_inst_sqrt5.v（is5_ 命名面逐条
   对应表：dms5_x/delta/e/x_pos/x_lb/x_ub/sq_ge5/mono_le/delta_step/
   sixteenth/e_step/decay/gap_lower/tail/vanish/no_sqrtZ/no_sqrt5）；
   u5c_sqrt2_closed_measure.v（√2 冻结版主定理形态）；
   u5c_dm_escape_to_dist_any.v dmec_escape_to_dist_any（装配桥）。
   构造性注记：语句面全 Set 层（sigT/prod/QltT/QleT'/real_lt），零 Prop
   前提位；证明体内 Prop 推导合法（Qle 链与整数整隙）；常元正性
   0 < 1/(16b²) 与四分支边距全为具体数值计算（cbn + nia/lia），零经典
   逻辑、零承认、零全局假设；新定义面仅 dms5_escape_closed_window
   （Defined 透明）与序列 Fixpoint，无新 Inductive；主定理装配链
   非单发空壳（四分支 + 衰减归纳 + 整隙 mod-5 下降实质推导）。
   编译配方：source Live/toolchain/env.sh 后
   rocq c -native-compiler no -q -Q . "" u5c_sqrt5_closed_measure.v。 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
Require Import u5c_aux_natpow.
Require Import u5c_dm_escape_to_dist_any.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* 平方余态：z² ≡ 0 (mod 5) 则 z ≡ 0 (mod 5)——
   剩余 1..4 的平方各为 1 或 4（mod 5），逐格枚举 *)
Lemma dms5_mod5_sq : forall z : Z, ((z * z) mod 5 = 0)%Z -> (z mod 5 = 0)%Z.
Proof.
  intros z H.
  assert (Hr : (z mod 5 = 0)%Z \/ (z mod 5 = 1)%Z \/ (z mod 5 = 2)%Z \/
               (z mod 5 = 3)%Z \/ (z mod 5 = 4)%Z).
  { pose proof (Z.mod_pos_bound z 5 (ltac:(lia))) as Hb. lia. }
  destruct Hr as [Hr | [Hr | [Hr | [Hr | Hr]]]]; [exact Hr | | | | ].
  - (* z = 5k+1：z² = 5·(5k²+2k)+1 *)
    exfalso.
    pose proof (Z.div_mod z 5 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 5)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 5 * (5 * k * k + 2 * k) + 1)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 5 = 1)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 5%Z ((5 * k * k + 2 * k)%Z) 1%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
  - (* z = 5k+2：z² = 5·(5k²+4k)+4 *)
    exfalso.
    pose proof (Z.div_mod z 5 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 5)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 5 * (5 * k * k + 4 * k) + 4)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 5 = 4)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 5%Z ((5 * k * k + 4 * k)%Z) 4%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
  - (* z = 5k+3：z² = 5·(5k²+6k+1)+4 *)
    exfalso.
    pose proof (Z.div_mod z 5 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 5)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 5 * (5 * k * k + 6 * k + 1) + 4)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 5 = 4)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 5%Z ((5 * k * k + 6 * k + 1)%Z) 4%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
  - (* z = 5k+4：z² = 5·(5k²+8k+3)+1 *)
    exfalso.
    pose proof (Z.div_mod z 5 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 5)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 5 * (5 * k * k + 8 * k + 3) + 1)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 5 = 1)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 5%Z ((5 * k * k + 8 * k + 3)%Z) 1%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
Qed.

(* 整除下降：a² = 5b²（b > 0）不可能——5|a ⟹ 25|a² ⟹ 5|b，
   对 Z.to_nat b 归纳，b 严格缩减；全构造，无经典逻辑 *)
Lemma dms5_no_sqrtZ : forall a b : Z, (0 < b)%Z -> (a * a = 5 * (b * b))%Z -> False.
Proof.
  assert (Hgen : forall n : nat, forall a b : Z, (0 < b)%Z ->
    (a * a = 5 * (b * b))%Z -> (Z.to_nat b <= n)%nat -> False).
  { induction n as [|n IH]; intros a b Hb Heq Hn.
    - assert (Hb0 : (b = 0)%Z).
      { pose proof (Z2Nat.id b (ltac:(lia))) as Hzz.
        apply Nat.le_0_r in Hn. rewrite Hn in Hzz. cbn in Hzz.
        symmetry. exact Hzz. }
      lia.
    - (* 5|a、5|b、b 严格降 *)
      assert (Ham : ((a * a) mod 5 = 0)%Z).
      { rewrite Heq.
        symmetry. apply (Zmod_unique ((5 * (b * b))%Z) 5%Z ((b * b)%Z) 0%Z); lia. }
      assert (Hae : (a mod 5 = 0)%Z) by (apply dms5_mod5_sq; exact Ham).
      pose proof (Z.div_mod a 5 (ltac:(lia))) as Hza. rewrite Hae in Hza.
      remember (a / 5)%Z as a1 eqn:Ea1.
      assert (Ha1 : (a = 5 * a1)%Z) by lia.
      clear Hza Ea1 Hae Ham.
      assert (Hbb : (b * b = 5 * (a1 * a1))%Z).
      { rewrite Ha1 in Heq.
        replace ((5 * a1)%Z * (5 * a1)%Z)%Z with (25 * (a1 * a1)%Z)%Z in Heq by ring.
        replace (25 * (a1 * a1)%Z)%Z with (5 * (5 * (a1 * a1)%Z)%Z)%Z in Heq by ring.
        lia. }
      assert (Hbm : ((b * b) mod 5 = 0)%Z).
      { rewrite Hbb.
        symmetry. apply (Zmod_unique ((5 * (a1 * a1))%Z) 5%Z ((a1 * a1)%Z) 0%Z); lia. }
      assert (Hbe : (b mod 5 = 0)%Z) by (apply dms5_mod5_sq; exact Hbm).
      pose proof (Z.div_mod b 5 (ltac:(lia))) as Hzb. rewrite Hbe in Hzb.
      remember (b / 5)%Z as b1 eqn:Eb1.
      assert (Hb1 : (b = 5 * b1)%Z) by lia.
      apply (IH a1 b1).
      + lia.
      + rewrite Hb1 in Hbb.
        replace ((5 * b1)%Z * (5 * b1)%Z)%Z with (25 * (b1 * b1)%Z)%Z in Hbb by ring.
        replace (25 * (b1 * b1)%Z)%Z with (5 * (5 * (b1 * b1)%Z)%Z)%Z in Hbb by ring.
        lia.
      + pose proof (Z2Nat.inj_mul b b1 (ltac:(lia)) (ltac:(lia))) as Hmm.
        pose proof (Z2Nat.id b (ltac:(lia))) as Hz1.
        pose proof (Z2Nat.id b1 (ltac:(lia))) as Hz2.
        lia. }
  intros a b Hb Heq.
  apply (Hgen (Z.to_nat b) a b Hb Heq (Nat.le_refl _)).
Qed.

Lemma dms5_no_sqrt5 : forall q : Q, QeqT (q * q) 5%Q -> False.
Proof.
  intros q Hq. apply qeqT_imp_qeq in Hq. destruct q as [a b].
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (Heq : (a * a = 5 * (Z.pos b * Z.pos b))%Z).
  { unfold Qeq, Qmult in Hq. cbn in Hq.
    assert (Hb1 : (Z.pos (b * b) = Z.pos b * Z.pos b)%Z) by apply Pos2Z.inj_mul.
    lia. }
  exact (dms5_no_sqrtZ a (Z.pos b) Hb Heq).
Qed.
(* ============================================================ *)
(* S3：Newton 序列（x_0=9/4，步 (x+5/x)/2）及其 Q 层基本量              *)
(* ============================================================ *)

Fixpoint dms5_x (n : nat) : Q :=
  match n with
  | O => (9 # 4)%Q
  | Datatypes.S m => (dms5_x m + 5%Q / dms5_x m) * (1 # 2)
  end.

Definition dms5_delta (n : nat) : Q := dms5_x n * dms5_x n - 5%Q.
Definition dms5_e (n : nat) : Q := (1 # 2) * dms5_delta n.

Lemma dms5_x1 : QeqT (dms5_x 1) (161 # 72).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.
(* 序列基本性质（正性/下界 9/5/单调/δ 代数） *)

Lemma dms5_div5_pos : forall v : Q, QltT 0 v -> QltT 0 (5%Q / v).
Proof.
  intros v Hv. apply QltT_to_Qlt in Hv. apply Qlt_to_QltT.
  unfold Qdiv.
  apply (Qmult_lt_0_compat (5#1) (Qinv v)).
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - apply (Qinv_lt_0_compat v Hv).
Qed.

Lemma dms5_x_pos : forall n : nat, QltT 0 (dms5_x n).
Proof.
  induction n as [|n IH].
  - apply Qlt_to_QltT. unfold Qlt. cbn [dms5_x Qnum Qden]. lia.
  - apply Qlt_to_QltT. cbn [dms5_x]. apply (Qmult_lt_0_compat _ (1 # 2)).
    + apply ir2_qpos_add;
        [exact (QltT_to_Qlt _ _ IH) | exact (QltT_to_Qlt _ _ (dms5_div5_pos _ IH))].
    + unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

Lemma dms5_delta_succ_mul : forall n : nat,
  QeqT (dms5_delta (Datatypes.S n) * (4 * (dms5_x n * dms5_x n)))
       (dms5_delta n * dms5_delta n).
Proof.
  intro n. apply qeq_imp_qeqT. unfold dms5_delta. cbn [dms5_x].
  field.
  intro Heq. apply (Qlt_not_eq 0%Q (dms5_x n) (QltT_to_Qlt _ _ (dms5_x_pos n))).
  apply Qeq_sym. exact Heq.
Qed.

Lemma dms5_delta_ge0 : forall n : nat, QleT' 0 (dms5_delta n).
Proof.
  induction n as [|n IH].
  - apply Qle_to_QleT'. unfold dms5_delta, Qle, Qmult, Qminus, Qplus, Qopp.
    cbn [dms5_x Qnum Qden]. lia.
  - apply Qle_to_QleT'. assert (HM : Qlt 0%Q (4 * (dms5_x n * dms5_x n))).
    { apply (Qmult_lt_0_compat (4#1) (dms5_x n * dms5_x n)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - apply (Qmult_lt_0_compat (dms5_x n) (dms5_x n));
          exact (QltT_to_Qlt _ _ (dms5_x_pos n)). }
    pose proof (qeqT_imp_qeq _ _ (dms5_delta_succ_mul n)) as Hmul.
    assert (Hsq : Qle 0 (dms5_delta n * dms5_delta n)).
    { destruct (dms5_delta n) as [dn dd] eqn:Ed.
      pose proof (QleT'_to_Qle _ _ IH) as H0.
      rewrite ?Ed in H0. unfold Qle in H0. cbn [Qnum Qden] in H0.
      unfold Qle, Qmult. rewrite ?Ed. cbn [Qnum Qden]. nia. }
    apply (ir2_ge0_of_mul _ _ HM).
    rewrite Hmul. exact Hsq.
Qed.

Lemma dms5_delta_pos : forall n : nat, QltT 0 (dms5_delta n).
Proof.
  intro n. apply Qlt_to_QltT.
  pose proof (QleT'_to_Qle _ _ (dms5_delta_ge0 n)) as Hge.
  destruct (Qeq_dec (dms5_delta n) 0%Q) as [Hz | Hne].
  - exfalso. apply (dms5_no_sqrt5 (dms5_x n)).
    apply qeq_imp_qeqT.
    unfold dms5_delta in Hz.
    rewrite <- (lic_qlt_minus_add_r (dms5_x n * dms5_x n) 5%Q).
    rewrite Hz. reflexivity.
  - destruct (Qlt_le_dec 0%Q (dms5_delta n)) as [Hlt | Hle].
    + exact Hlt.
    + exfalso. apply Hne. apply (Qle_antisym (dms5_delta n) 0%Q Hle Hge).
Qed.

Lemma dms5_sq_ge5 : forall n : nat, QleT' 5%Q (dms5_x n * dms5_x n).
Proof.
  intro n. apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ (dms5_delta_ge0 n)) as H.
  assert (Hr : ((dms5_x n * dms5_x n - 5) + 5 == dms5_x n * dms5_x n)%Q)
    by apply lic_qlt_minus_add_r.
  rewrite <- Hr.
  apply (Qle_trans 5%Q (0%Q + 5%Q)%Q ((dms5_x n * dms5_x n - 5%Q)%Q + 5%Q)%Q).
  - rewrite Qplus_0_l. apply Qle_refl.
  - apply Qplus_le_compat; [exact H | apply Qle_refl].
Qed.

Lemma dms5_x_lb : forall n : nat, QleT' (9 # 5) (dms5_x n).
Proof.
  intro n. apply Qle_to_QleT'.
  pose proof (QltT_to_Qlt _ _ (dms5_x_pos n)) as Hp.
  destruct (Qlt_le_dec (dms5_x n) (9#5)) as [Hlt | Hle].
  - exfalso.
    assert (H1 : Qlt ((dms5_x n) * (dms5_x n)) ((9#5) * (dms5_x n))).
    { apply (Qmult_lt_compat_r (dms5_x n) (9#5) (dms5_x n)); [exact Hp | exact Hlt]. }
    assert (H2 : Qlt ((9#5) * (dms5_x n)) ((9#5) * (9#5))).
    { rewrite (Qmult_comm (9#5) (dms5_x n)).
      apply (Qmult_lt_compat_r (dms5_x n) (9#5) (9#5)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - exact Hlt. }
    assert (H3 : Qlt (dms5_x n * dms5_x n) 5%Q).
    { apply (Qlt_trans _ ((9#5) * (9#5))).
      - apply (Qlt_trans _ ((9#5) * (dms5_x n))); [exact H1 | exact H2].
      - unfold Qlt, Qmult. cbn [Qnum Qden]. lia. }
    apply (Qlt_not_le (dms5_x n * dms5_x n) 5%Q).
    + exact H3.
    + exact (QleT'_to_Qle _ _ (dms5_sq_ge5 n)).
  - exact Hle.
Qed.

Lemma dms5_mono : forall n : nat, QleT' (dms5_x (Datatypes.S n)) (dms5_x n).
Proof.
  intro n. apply Qle_to_QleT'. cbn [dms5_x].
  pose proof (QleT'_to_Qle _ _ (dms5_sq_ge5 n)) as H5.
  pose proof (QltT_to_Qlt _ _ (dms5_x_pos n)) as Hxp.
  destruct (dms5_x n) as [a b] eqn:Ex.
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (H5c : (5 * Z.pos b * Z.pos b <= a * a)%Z).
  { pose proof H5 as H5'. rewrite ?Ex in H5'.
    unfold Qle, Qmult in H5'. cbn [Qnum Qden] in H5'. nia. }
  assert (Hne : ~ ((a # b) == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0%Q (a # b) Hxp).
    apply Qeq_sym. exact Hc. }
  assert (Hbb : ((a # b) * Qinv (a # b))%Q == 1%Q).
  { pose proof (bno_mul_div_self (a # b) Hne) as Hbb0.
    unfold Qdiv in Hbb0. rewrite Qmult_1_l in Hbb0. exact Hbb0. }
  assert (Hivp : Qle 0%Q (Qinv (a # b)))
    by (apply ir2_inv_pos; exact Hxp).
  assert (Hinv : Qle (5%Q / (a # b)) (a # b)).
  { apply (Qle_trans _ (((a # b) * (a # b)) * Qinv (a # b))%Q).
    - apply Qmult_le_compat_r; [exact H5 | exact Hivp].
    - apply qeq_le.
      rewrite <- (Qmult_assoc (a # b) (a # b) (Qinv (a # b))).
      rewrite Hbb. apply Qmult_1_r. }
  apply (Qle_trans _ (((a # b) + (a # b)) * (1 # 2))%Q).
  - apply Qmult_le_compat_r.
    + apply (Qplus_le_compat (a # b) (a # b)
               (5%Q / (a # b)) (a # b));
        [apply Qle_refl | exact Hinv].
    + unfold Qle. cbn [Qnum Qden]. lia.
  - assert (Hr : ((((a # b) + (a # b)) * (1 # 2))
                   == (a # b))%Q) by ring.
    rewrite Hr. apply Qle_refl.
Qed.

Lemma dms5_mono_le : forall n k : nat, (1 <= n)%nat -> (n <= k)%nat ->
  QleT' (dms5_x k) (dms5_x n).
Proof.
  intros n k Hn1 Hnk. apply Qle_to_QleT'.
  assert (Hgen : forall d : nat, dms5_x (n + d) <= dms5_x n).
  { induction d as [|d IHd].
    - rewrite Nat.add_0_r. apply Qle_refl.
    - replace (n + Datatypes.S d)%nat with (Datatypes.S (n + d))%nat by lia.
      apply (Qle_trans _ (dms5_x (n + d))).
      + exact (QleT'_to_Qle _ _ (dms5_mono (n + d))).
      + exact IHd. }
  replace k with (n + (k - n))%nat by lia.
  apply Hgen.
Qed.

(* 上界 9/4 对全体 n 成立（种子即 9/4，全列单调降） *)
Lemma dms5_x_ub : forall n : nat, QleT' (dms5_x n) (9 # 4).
Proof.
  intro n. apply Qle_to_QleT'. destruct n as [|n'].
  - cbn [dms5_x]. apply Qle_refl.
  - apply (Qle_trans _ (dms5_x 1)).
    + exact (QleT'_to_Qle _ _
               (dms5_mono_le 1 (Datatypes.S n') (ltac:(lia)) (ltac:(lia)))).
    + rewrite (qeqT_imp_qeq _ _ dms5_x1). unfold Qle. cbn [Qnum Qden]. lia.
Qed.
(* ============================================================ *)
(* S4：误差窗口衰减（δ ≤ 1/16；δ(Sn) ≤ δn/192；e_n ≤ 1/2^{n+1}）       *)
(* ============================================================ *)

Lemma dms5_delta_step : forall n : nat, (1 <= n)%nat -> QleT' (dms5_delta n) (1#16) ->
  QleT' (dms5_delta (Datatypes.S n)) ((1#192) * dms5_delta n).
Proof.
  intros n Hn1 Hdu. apply QleT'_to_Qle in Hdu. apply Qle_to_QleT'.
  pose proof (QltT_to_Qlt _ _ (dms5_x_pos n)) as Hxp.
  assert (Hlb : Qle ((9#5) * (9#5)) (dms5_x n * dms5_x n)).
  { apply (Qle_trans _ ((9#5) * dms5_x n)%Q).
    - apply ir2_mult_le_compat_l;
        [exact (QleT'_to_Qle _ _ (dms5_x_lb n)) | unfold Qle; cbn; lia].
    - apply Qmult_le_compat_r;
        [exact (QleT'_to_Qle _ _ (dms5_x_lb n))
         | apply Qlt_le_weak; exact (QltT_to_Qlt _ _ (dms5_x_pos n))]. }
  assert (H12 : Qle 12%Q (4 * (dms5_x n * dms5_x n))).
  { apply (Qle_trans _ ((4#1) * ((9#5) * (9#5)))%Q).
    - unfold Qle, Qmult. cbn [Qnum Qden]. lia.
    - rewrite (Qmult_comm (4#1) ((9#5) * (9#5))).
      rewrite (Qmult_comm (4#1) (dms5_x n * dms5_x n)).
      apply Qmult_le_compat_r; [exact Hlb | unfold Qle; cbn; lia]. }
  pose proof (qeqT_imp_qeq _ _ (dms5_delta_succ_mul n)) as Hmul.
  pose proof (QleT'_to_Qle _ _ (dms5_delta_ge0 (Datatypes.S n))) as HdS0.
  assert (Ha : Qle (12 * dms5_delta (Datatypes.S n)) (dms5_delta n * dms5_delta n)).
  { rewrite <- Hmul.
    rewrite (Qmult_comm (dms5_delta (Datatypes.S n)) (4 * (dms5_x n * dms5_x n))).
    apply Qmult_le_compat_r; [exact H12 | exact HdS0]. }
  assert (Hb : Qle (dms5_delta n * dms5_delta n) ((1#16) * dms5_delta n)).
  { apply (Qmult_le_compat_r (dms5_delta n) (1#16) (dms5_delta n));
      [exact Hdu | exact (QleT'_to_Qle _ _ (dms5_delta_ge0 n))]. }
  assert (Hc : Qle (12 * dms5_delta (Datatypes.S n)) ((1#16) * dms5_delta n))
    by (apply (Qle_trans _ (dms5_delta n * dms5_delta n)); assumption).
  apply (Qle_trans (dms5_delta (Datatypes.S n))
    (((1#16) * dms5_delta n) * Qinv (12#1)) ((1#192) * dms5_delta n)).
  - apply (ir2_le_mul_inv (dms5_delta (Datatypes.S n)) ((1#16) * dms5_delta n) (12#1)).
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + rewrite (Qmult_comm (dms5_delta (Datatypes.S n)) (12#1)). exact Hc.
  - assert (Hc2 : Qinv (12#1) == (1#12)%Q) by reflexivity.
    rewrite Hc2. apply qeq_le. ring.
Qed.

Lemma dms5_sixteenth : forall n : nat, (1 <= n)%nat -> QleT' (dms5_delta n) (1#16).
Proof.
  induction n as [|n IH].
  - intro Hn0. apply Qle_to_QleT'. lia.
  - intro Hle0. apply Qle_to_QleT'. destruct n as [|n].
    + change (dms5_delta 1) with (1 # 5184)%Q.
      unfold Qle. cbn [Qnum Qden]. lia.
    + assert (Hn1 : (1 <= Datatypes.S n)%nat) by lia.
      pose proof (IH Hn1) as Hdu.
      apply (Qle_trans _ ((1#192) * dms5_delta (Datatypes.S n))).
      * exact (QleT'_to_Qle _ _
                 (dms5_delta_step (Datatypes.S n) (ltac:(lia)) Hdu)).
      * apply (Qle_trans _ ((1#192) * (1#16))%Q).
        -- apply ir2_mult_le_compat_l;
             [exact (QleT'_to_Qle _ _ Hdu) | unfold Qle; cbn; lia].
        -- unfold Qle, Qmult. cbn [Qnum Qden]. lia.
Qed.

Lemma dms5_e_step : forall n : nat, (1 <= n)%nat ->
  QleT' (dms5_e (Datatypes.S n)) ((1#2) * dms5_e n).
Proof.
  intros n Hn1. apply Qle_to_QleT'. unfold dms5_e.
  apply (Qle_trans _ ((1#2) * ((1#192) * dms5_delta n))%Q).
  - rewrite (Qmult_comm (1#2) (dms5_delta (Datatypes.S n))).
    rewrite (Qmult_comm (1#2) ((1#192) * dms5_delta n)).
    pose proof (dms5_sixteenth n Hn1) as Hdu.
    apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ (dms5_delta_step n Hn1 Hdu)).
    + unfold Qle. cbn [Qnum Qden]. lia.
  - destruct (dms5_delta n) as [dn dd] eqn:Edn.
    pose proof (QleT'_to_Qle _ _ (dms5_delta_ge0 n)) as Hge. rewrite Edn in Hge.
    unfold Qle in Hge. cbn [Qnum Qden] in Hge.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    unfold Qle, Qmult. cbn [Qnum Qden]. nia.
Qed.
Lemma dms5_decay : forall n : nat,
  QleT' (dms5_e (Datatypes.S n) * ir2_qp (Datatypes.S (Datatypes.S n))) 1%Q.
Proof.
  induction n as [|n IH].
  - apply Qle_to_QleT'. change (dms5_e 1) with (1 # 10368)%Q.
    change (ir2_qp 2) with (4 # 1)%Q.
    unfold Qle, Qmult. cbn [Qnum Qden]. lia.
  - apply Qle_to_QleT'.
    apply (Qle_trans _ (((1#2) * dms5_e (Datatypes.S n))
                          * ((2#1) * ir2_qp (Datatypes.S (Datatypes.S n))))%Q).
    + rewrite ir2_qp_def.
      apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ (dms5_e_step (Datatypes.S n) (ltac:(lia)))).
      * apply Qlt_le_weak.
        apply (Qmult_lt_0_compat (2#1) (ir2_qp (Datatypes.S (Datatypes.S n)))).
        -- unfold Qlt. cbn [Qnum Qden]. lia.
        -- apply ir2_qp_pos.
    + rewrite ir2_qp_def.
      assert (Hr : ((((1#2) * dms5_e (Datatypes.S n))
                      * ((2#1) * ir2_qp (Datatypes.S (Datatypes.S n))))
                     == (dms5_e (Datatypes.S n)
                          * ir2_qp (Datatypes.S (Datatypes.S n))))%Q) by ring.
      rewrite Hr. exact (QleT'_to_Qle _ _ IH).
Qed.
(* ============================================================ *)
(* S4'：锐衰减链（e(n) ≤ 1/(5184·2^n)，n ≥ 1）与闭式常元 e 界确定       *)
(* ============================================================ *)

(* 锐衰减：e(n)·(5184·2^n) ≤ 1（n ≥ 1）——基底值 e(1)=1/10368 精确值
   逐半衰变推进；较 2^-(n+1) 通用形锐 2592 倍，是常元 16 档的钥匙 *)
Lemma dms5_e_sharp : forall n : nat, (1 <= n)%nat ->
  QleT' (dms5_e n * (5184 * ir2_qp n)) 1%Q.
Proof.
  induction n as [|n IH]; intro Hn.
  - apply Qle_to_QleT'. lia.
  - apply Qle_to_QleT'. destruct n as [|n].
    + change (dms5_e 1) with (1 # 10368)%Q.
      change (ir2_qp 1) with (2 # 1)%Q.
      unfold Qle, Qmult. cbn [Qnum Qden Qmult]. lia.
    + assert (Hn' : (1 <= Datatypes.S n)%nat) by lia.
      rewrite (ir2_qp_def (Datatypes.S n)).
      apply (Qle_trans _ (((1#2) * dms5_e (Datatypes.S n))
                            * (5184 * ((2#1) * ir2_qp (Datatypes.S n))))%Q).
      * apply (Qmult_le_compat_r _ _
                 (5184 * ((2#1) * ir2_qp (Datatypes.S n)))).
        -- exact (QleT'_to_Qle _ _ (dms5_e_step (Datatypes.S n) Hn')).
        -- apply Qlt_le_weak.
           apply (Qmult_lt_0_compat (5184#1)
                      ((2#1) * ir2_qp (Datatypes.S n))).
           ++ unfold Qlt. cbn [Qnum Qden]. lia.
           ++ apply (Qmult_lt_0_compat (2#1) (ir2_qp (Datatypes.S n)));
                [unfold Qlt; cbn [Qnum Qden]; lia | apply ir2_qp_pos].
      * assert (Hr : ((((1#2) * dms5_e (Datatypes.S n))
                        * (5184 * ((2#1) * ir2_qp (Datatypes.S n))))
                       == (dms5_e (Datatypes.S n)
                            * (5184 * ir2_qp (Datatypes.S n))))%Q) by ring.
        rewrite Hr. exact (QleT'_to_Qle _ _ (IH Hn')).
Qed.

(* ============================================================ *)
(* S4''：统一 e 界：n ≥ den+3 时 e(n) ≤ 1/(16b²)——常元确定 C=16 的供给引理 *)
(* ============================================================ *)

Lemma dms5_e_bnd : forall (b : positive) (n : nat),
  (Z.to_nat (Z.pos b) + 3 <= n)%nat -> QleT' (dms5_e n) ((1 # (16 * (b * b)))%Q).
Proof.
  intros b n Hge. apply Qle_to_QleT'.
  assert (Hn1 : (1 <= n)%nat) by (pose proof (Nat.le_0_l (Z.to_nat (Z.pos b))); lia).
  pose proof (QleT'_to_Qle _ _ (dms5_e_sharp n Hn1)) as Hsh.
  assert (Hb1 : (1 <= Z.to_nat (Z.pos b))%nat).
  { destruct (Z.to_nat (Z.pos b)) as [|k] eqn:Ek; [ | lia].
    exfalso. pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz.
    rewrite Ek in Hz. cbn in Hz. lia. }
  assert (Hkb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b) by (apply Z2Nat.id; lia).
  assert (Hpow : (2 ^ (Z.to_nat (Z.pos b) + 3) <= 2 ^ n)%nat)
    by (apply Nat.pow_le_mono_r; lia).
  assert (H16 : (4 * (4 * Z.to_nat (Z.pos b) * Z.to_nat (Z.pos b))
                 <= 5184 * 2 ^ (Z.to_nat (Z.pos b) + 3))%nat).
  { pose proof (u5c_pow4 (Z.to_nat (Z.pos b)) Hb1) as Hp4.
    pose proof (Nat.mul_le_mono_l (4 * Z.to_nat (Z.pos b) * Z.to_nat (Z.pos b))
                  (2 ^ (Z.to_nat (Z.pos b) + 3)) 4 Hp4) as Hm1.
    apply (Nat.le_trans _ (4 * 2 ^ (Z.to_nat (Z.pos b) + 3))%nat).
    - exact Hm1.
    - rewrite (Nat.mul_comm 4 (2 ^ (Z.to_nat (Z.pos b) + 3))).
      rewrite (Nat.mul_comm 5184 (2 ^ (Z.to_nat (Z.pos b) + 3))).
      exact (Nat.mul_le_mono_l 4 5184 (2 ^ (Z.to_nat (Z.pos b) + 3))
               (proj1 (Nat.leb_le 4 5184) eq_refl)). }
  assert (HZ : (16 * (Z.pos b * Z.pos b)
                <= 5184 * Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3)))%Z).
  { pose proof (proj1 (Nat2Z.inj_le _ _) H16) as H.
    rewrite !Nat2Z.inj_mul in H. rewrite Hkb in H. cbn [Z.of_nat] in H.
    (* lia 对非线性积作句法原子化（(4b)·b ≠ b·b），故走等式 replace+exact *)
    replace (16 * (Z.pos b * Z.pos b))%Z
      with (4 * (4 * Z.pos b * Z.pos b))%Z by lia.
    exact H. }
  rewrite (ir2_qp_pow n) in Hsh.
  assert (Hnatab : (Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3)) <= Z.of_nat (2 ^ n))%Z)
    by (apply Nat2Z.inj_le; exact Hpow).
  assert (Hen : Qle 0%Q (dms5_e n)).
  { unfold dms5_e.
    apply (Qle_trans _ (((1#2) * 0%Q)%Q)).
    - apply qeq_le. reflexivity.
    - apply (ir2_mult_le_compat_l 0%Q (dms5_delta n) (1#2));
        [exact (QleT'_to_Qle _ _ (dms5_delta_ge0 n))
         | unfold Qle; cbn [Qnum Qden]; lia]. }
  assert (HstepB : Qle ((dms5_e n
                          * (5184 * ((Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3))) # 1)))%Q)
                        1%Q).
  { apply (Qle_trans _ ((dms5_e n
                          * (5184 * ((Z.of_nat (2 ^ n)) # 1)))%Q)).
    - apply (ir2_mult_le_compat_l _ _ (dms5_e n)).
      + unfold Qle, Qmult. cbn [Qnum Qden]. lia.
      + exact Hen.
    - exact Hsh. }
  assert (H1p : (1 <= 2 ^ (Z.to_nat (Z.pos b) + 3))%nat).
  { apply (Nat.le_trans 1 (2 ^ 0)%nat).
    - change (2 ^ 0)%nat with 1%nat. apply Nat.le_refl.
    - apply Nat.pow_le_mono_r; lia. }
  assert (HC : Qle (dms5_e n)
                   (Qinv ((5184 * Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3))) # 1)%Q)).
  { apply (ir2_le_inv ((5184 * Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3))) # 1)%Q
             (dms5_e n)).
    - unfold Qlt. cbn [Qnum Qden]. lia.
    - rewrite (Qmult_comm ((5184 * Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3))) # 1)
                (dms5_e n)).
      exact HstepB. }
  assert (HD : Qle (Qinv ((5184 * Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3))) # 1)%Q)
                   ((1 # (16 * (b * b)))%Q)).
  { apply (Qle_trans _ (Qinv ((Z.pos (16 * (b * b))) # 1)%Q)).
    - apply (ir2_inv_le ((Z.pos (16 * (b * b))) # 1)%Q
               ((5184 * Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3))) # 1)%Q).
      + unfold Qlt. cbn [Qnum Qden]. pose proof (Pos2Z.is_pos b). lia.
      + unfold Qle, Qmult. cbn [Qnum Qden].
        rewrite ?Pos2Z.inj_mul. rewrite !Z.mul_1_r.
        change (Z.pos 16) with 16%Z.
        exact HZ.
    - apply qeq_le. reflexivity. }
  exact (Qle_trans _ _ _ HC HD).
Qed.
(* ============================================================ *)
(* S5：逃逸间隙引理（√5 与任一有理数的 Q 层可判间隙）                    *)
(* ============================================================ *)

(* 下侧间隙：q²<5 时 (5−q²)·(2/9) ≤ x_N−q（x_N ≤ 9/4 ⟹ 1/(x_N+q) ≥ 2/9） *)
Lemma dms5_gap_lower : forall u v : Q,
  QleT' 0 v -> QleT' v u -> QleT' u (9#4) -> QleT' 5 (u*u) -> QltT (v*v) 5 ->
  QleT' ((5 - v*v) * (2#9)) (u - v).
Proof.
  intros u v Hv0 Hvu Hub H5 Hsq.
  apply QleT'_to_Qle in Hv0.
  apply QleT'_to_Qle in Hvu.
  apply QleT'_to_Qle in Hub.
  apply QleT'_to_Qle in H5.
  apply QltT_to_Qlt in Hsq.
  apply Qle_to_QleT'.
  assert (Hu0 : Qle 0 u) by (apply (Qle_trans 0 v u); assumption).
  assert (Huv0 : Qlt 0%Q (u + v)).
  { destruct (Qlt_le_dec 0%Q (u + v)) as [Hlt | Hle].
    - exact Hlt.
    - exfalso.
      assert (Huu : Qle u (u + v)).
      { apply (Qle_trans u (u + 0%Q) (u + v)).
        - apply qeq_le. symmetry. apply Qplus_0_r.
        - apply (Qplus_le_compat u u 0%Q v); [apply Qle_refl | exact Hv0]. }
      assert (Hu : u == 0%Q).
      { apply (Qle_antisym u 0%Q).
        - apply (Qle_trans u (u + v) 0%Q); [exact Huu | exact Hle].
        - exact Hu0. }
      pose proof H5 as H5'. rewrite Hu in H5'.
      unfold Qle, Qmult in H5'. cbn [Qnum Qden] in H5'.
      clear Hu Huu Hle. lia. }
  assert (Hne : ~ ((u + v)%Q == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (u + v) Huv0); rewrite Hc; apply Qeq_refl).
  assert (Hbridge : ((u - v) == (u*u - v*v) * Qinv (u + v))%Q).
  { pose proof (bno_mul_div_self (u + v) Hne) as Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((u - v) * (u + v)) * Qinv (u + v)) == (u - v))%Q).
    { rewrite <- (Qmult_assoc (u - v) (u + v) (Qinv (u + v))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite ir2_sq_diff in Hpm. exact (Qeq_sym _ _ Hpm). }
  assert (Hw0 : Qle 0%Q (5 - v*v))
    by (apply Qlt_le_weak; apply (lic_qlt_0_minus (v*v) 5%Q Hsq)).
  assert (Hub2 : Qle (u + v) (9#2)).
  { apply (Qle_trans _ ((9#4) + (9#4))%Q).
    - apply (Qplus_le_compat u (9#4) v (9#4)).
      + exact Hub.
      + apply (Qle_trans v u (9#4)); assumption.
    - unfold Qle, Qplus, Qmult. cbn [Qnum Qden]. lia. }
  assert (Hivp : Qle 0%Q (Qinv (u + v))) by (apply ir2_inv_pos; exact Huv0).
  rewrite Hbridge.
  apply (Qle_trans _ ((u*u - v*v) * Qinv (u + v))%Q).
  - apply (Qle_trans _ ((5 - v*v) * Qinv (u + v))%Q).
    + apply ir2_mult_le_compat_l.
      * apply (ir2_inv_le (u + v) (9#2)); [exact Huv0 | exact Hub2].
      * exact Hw0.
    + apply Qmult_le_compat_r.
      * unfold Qminus. apply ir2_add_le_r. exact H5.
      * exact Hivp.
  - apply Qle_refl.
Qed.
(* ============================================================ *)
(* S6：源定理三前件实例（尾控/窗口宽消失/逃逸窗口）                        *)
(* ============================================================ *)

Definition dms5_tail : lic_tail_bounded dms5_x dms5_e.
Proof.
  intros n k Hn1 Hnk.
  pose proof (QleT'_to_Qle _ _ (dms5_mono_le n k Hn1 Hnk)) as Hmono.
  pose proof (QleT'_to_Qle _ _ (dms5_delta_ge0 n)) as Hd0n.
  pose proof (QltT_to_Qlt _ _ (dms5_delta_pos n)) as Hdpn.
  assert (Habs : Qabs ((dms5_x k - dms5_x n)%Q) == (dms5_x n - dms5_x k)%Q).
  { rewrite Qabs_Qminus. apply ir2_abs_sub. exact Hmono. }
  assert (Hsumpos : Qlt 0 (dms5_x n + dms5_x k)).
  { apply ir2_qpos_add.
    - apply (Qlt_le_trans 0%Q (9#5) (dms5_x n)).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + exact (QleT'_to_Qle _ _ (dms5_x_lb n)).
    - apply (Qlt_le_trans 0%Q (9#5) (dms5_x k)).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + exact (QleT'_to_Qle _ _ (dms5_x_lb k)). }
  assert (Hsumne : ~ ((dms5_x n + dms5_x k) == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (dms5_x n + dms5_x k) Hsumpos);
        rewrite Hc; apply Qeq_refl).
  assert (Hbridge : (((dms5_x n - dms5_x k)
                      == (dms5_delta n - dms5_delta k) * Qinv (dms5_x n + dms5_x k))%Q)).
  { pose proof (bno_mul_div_self (dms5_x n + dms5_x k) Hsumne) as Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((dms5_x n - dms5_x k) * (dms5_x n + dms5_x k))
                    * Qinv (dms5_x n + dms5_x k)) == (dms5_x n - dms5_x k))%Q).
    { rewrite <- (Qmult_assoc (dms5_x n - dms5_x k) (dms5_x n + dms5_x k)
                    (Qinv (dms5_x n + dms5_x k))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite ir2_sq_diff in Hpm.
    assert (Hsh : ((dms5_x n * dms5_x n - dms5_x k * dms5_x k)
                   == (dms5_delta n - dms5_delta k))%Q)
      by (unfold dms5_delta; ring).
    rewrite Hsh in Hpm. exact (Qeq_sym _ _ Hpm). }
  apply Qlt_to_QltT. rewrite Habs. rewrite Hbridge.
  assert (Hsumb : Qle ((18#5)) (dms5_x n + dms5_x k)).
  { apply (Qle_trans _ ((9#5) + (9#5))%Q).
    - apply qeq_le. reflexivity.
    - apply (Qplus_le_compat (9#5) (dms5_x n) (9#5) (dms5_x k));
        [exact (QleT'_to_Qle _ _ (dms5_x_lb n))
         | exact (QleT'_to_Qle _ _ (dms5_x_lb k))]. }
  assert (Hinvp : Qle 0%Q (Qinv (dms5_x n + dms5_x k)))
    by (apply ir2_inv_pos; exact Hsumpos).
  assert (Hstep1 : Qle ((dms5_delta n - dms5_delta k) * Qinv (dms5_x n + dms5_x k))
                     (dms5_delta n * Qinv (dms5_x n + dms5_x k))).
  { apply Qmult_le_compat_r.
    - unfold Qminus, Qle, Qopp in *.
      destruct (dms5_delta n) as [dn dd] eqn:Edn.
      destruct (dms5_delta k) as [ek ed] eqn:Edk.
      pose proof (QleT'_to_Qle _ _ (dms5_delta_ge0 k)) as H0k.
      rewrite Edk in H0k. unfold Qle in H0k. cbn [Qnum Qden] in H0k.
      cbn [Qnum Qden Qplus Qopp Qmult].
      assert (Hdd0 : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
      assert (Hed0 : (0 < Z.pos ed)%Z) by apply Pos2Z.is_pos.
      nia.
    - exact Hinvp. }
  assert (Hstep2 : Qle (dms5_delta n * Qinv (dms5_x n + dms5_x k))
                     (dms5_delta n * Qinv ((18#5)))).
  { rewrite (Qmult_comm (dms5_delta n) (Qinv (dms5_x n + dms5_x k))).
    rewrite (Qmult_comm (dms5_delta n) (Qinv ((18#5)))).
    apply Qmult_le_compat_r.
    - apply (ir2_inv_le (18#5) (dms5_x n + dms5_x k));
        [unfold Qlt; cbn [Qnum Qden]; lia | exact Hsumb].
    - exact Hd0n. }
  assert (Hstep3 : Qlt (dms5_delta n * Qinv ((18#5))) ((1#2) * dms5_delta n)).
  { destruct (dms5_delta n) as [dn dd] eqn:Edn.
    pose proof (QltT_to_Qlt _ _ (dms5_delta_pos n)) as Hdp.
    rewrite Edn in Hdp. unfold Qlt in Hdp. cbn [Qnum Qden] in Hdp.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    unfold Qlt, Qmult, Qinv. cbn [Qnum Qden Qinv]. nia. }
  apply (Qle_lt_trans ((dms5_delta n - dms5_delta k) * Qinv (dms5_x n + dms5_x k))
          (dms5_delta n * Qinv (dms5_x n + dms5_x k)) ((1#2) * dms5_delta n)).
  - exact Hstep1.
  - apply (Qle_lt_trans (dms5_delta n * Qinv (dms5_x n + dms5_x k))
            (dms5_delta n * Qinv ((18#5))) ((1#2) * dms5_delta n)).
    + exact Hstep2.
    + exact Hstep3.
Defined.

Definition dms5_vanish : lic_vanish dms5_e.
Proof.
  intros eps Heps. destruct eps as [pn pd].
  pose proof (QltT_to_Qlt 0%Q (pn # pd) Heps) as Heps0.
  unfold Qlt in Heps0. cbn [Qnum Qden] in Heps0.
  assert (Hpn : (0 < pn)%Z) by lia.
  assert (Hpd : (0 < Z.pos pd)%Z) by apply Pos2Z.is_pos.
  exists (Z.to_nat (Z.pos pd) + 1)%nat.
  intros n Hn. destruct n as [|n'].
  - lia.
  - apply Qlt_to_QltT.
    apply (Qle_lt_trans (dms5_e (Datatypes.S n'))
            (Qinv (ir2_qp (Datatypes.S (Datatypes.S n')))) ((pn # pd)%Q)).
    + apply (ir2_le_inv (ir2_qp (Datatypes.S (Datatypes.S n')))
               (dms5_e (Datatypes.S n'))).
      * apply ir2_qp_pos.
      * rewrite (Qmult_comm (ir2_qp (Datatypes.S (Datatypes.S n')))
                            (dms5_e (Datatypes.S n'))).
        exact (QleT'_to_Qle _ _ (dms5_decay n')).
    + apply (Qlt_le_trans (Qinv (ir2_qp (Datatypes.S (Datatypes.S n'))))
              (Qinv (Z.pos pd # 1)) ((pn # pd)%Q)).
      * apply (ir2_inv_lt (ir2_qp (Datatypes.S (Datatypes.S n'))) (Z.pos pd # 1)).
        -- apply ir2_qp_pos.
        -- unfold Qlt. cbn [Qnum Qden]. lia.
        -- rewrite ir2_qp_pow.
           replace (Datatypes.S (Datatypes.S n'))%nat with (n' + 2)%nat by lia.
           assert (Hzc : (Z.pos pd <= Z.of_nat n')%Z).
           { assert (Hle : (Z.to_nat (Z.pos pd) + 1 <= Datatypes.S n')%nat) by lia.
             pose proof (proj1 (Nat2Z.inj_le _ _) Hle) as Hz.
             rewrite Nat2Z.inj_add, Nat2Z.inj_succ in Hz.
             pose proof (Z2Nat.id (Z.pos pd) (ltac:(lia))) as Hz2.
             cbn in Hz. lia. }
           pose proof (proj1 (Nat2Z.inj_le _ _) (ir2_pow_ge (n' + 2))) as Hpg.
           unfold Qlt. cbn [Qnum Qden]. lia.
      * unfold Qle, Qinv. cbn [Qnum Qden]. nia.
Qed.
(* ============================================================ *)
(* S7：三倍边距核：3/(16b²) ≤ |q − x(n0)|（四分支，常元确定链核心）        *)
(* ============================================================ *)

(* 四分支边距核（除 e 界假设外全自足；数值链经预检：分支二 3/16 ≤ 2/9
   即 27 ≤ 32；分支三 3/16 ≤ 7/36 即 108 ≤ 112；分支四 12b ≤ 16b²；
   分支一 15 ≤ 144b²） *)
Lemma dms5_margin_trine : forall (a : Z) (b : positive) (n0 : nat),
  (1 <= n0)%nat -> QleT' (dms5_e n0) ((1 # (16 * (b * b)))%Q) ->
  QleT' ((3 # (16 * (b * b)))%Q) (Qabs (((a # b)%Q - dms5_x n0)%Q)).
Proof.
  intros a b n0 Hn01 Heb.
  apply QleT'_to_Qle in Heb.
  apply Qle_to_QleT'.
  assert (Hz : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  pose proof (QleT'_to_Qle _ _ (dms5_x_lb n0)) as Hxlb.
  pose proof (dms5_x_ub n0) as Hxub.
  pose proof (dms5_sq_ge5 n0) as Hx2.
  pose proof (QltT_to_Qlt _ _ (dms5_x_pos n0)) as Hxpos.
  destruct (Qlt_le_dec 0%Q (a # b)%Q) as [Hq0 | Hq0].
  - destruct (Qlt_le_dec ((a # b)%Q * (a # b)%Q) 5%Q) as [Hlt5 | Hge5].
    + (* 分支二：0 < q 且 q² < 5 *)
      assert (Hqx : Qle (a # b)%Q (dms5_x n0)).
      { destruct (Qlt_le_dec (dms5_x n0) (a # b)%Q) as [Hxq | Hle].
        - exfalso.
          apply (Qlt_not_le ((a # b)%Q * (a # b)%Q) 5%Q Hlt5).
          apply (Qle_trans 5%Q (dms5_x n0 * dms5_x n0)
                  ((a # b)%Q * (a # b)%Q)).
          + exact (QleT'_to_Qle _ _ Hx2).
          + apply (ir2_sq_mono (a # b)%Q (dms5_x n0)).
            * apply Qlt_le_weak. exact Hxpos.
            * apply Qlt_le_weak. exact Hxq.
        - exact Hle. }
      rewrite (Qabs_Qminus (a # b)%Q (dms5_x n0)).
      rewrite (ir2_abs_sub (dms5_x n0) (a # b)%Q Hqx).
      apply (Qle_trans _ (((5 - (a # b)%Q * (a # b)%Q) * (2#9))%Q)).
      * assert (Hzint : (a * a < 5 * (Z.pos b * Z.pos b))%Z).
        { pose proof Hlt5 as Hh. unfold Qlt, Qmult in Hh.
          cbn [Qnum Qden] in Hh. rewrite (Pos2Z.inj_mul b b) in Hh. nia. }
        unfold Qle, Qminus, Qmult, Qplus, Qopp;
          cbn [Qnum Qden Qminus Qmult Qplus Qopp];
          rewrite ?Pos2Z.inj_mul; nia.
      * exact (QleT'_to_Qle _ _
            (dms5_gap_lower (dms5_x n0) (a # b)%Q
               (Qle_to_QleT' _ _ (Qlt_le_weak 0%Q (a # b)%Q Hq0))
               (Qle_to_QleT' _ _ Hqx) Hxub Hx2
               (Qlt_to_QltT _ _ Hlt5))).
    + destruct (Qle_lt_or_eq 5%Q ((a # b)%Q * (a # b)%Q) Hge5) as [Hlt5 | Heq].
      * destruct (Qlt_le_dec (9#4) (a # b)%Q) as [Hqgt | Hq32].
        -- (* 分支四：q > 9/4 *)
           assert (Hside : Qle (dms5_x n0) (a # b)%Q).
           { apply (Qle_trans (dms5_x n0) (9#4) (a # b)%Q);
               [exact (QleT'_to_Qle _ _ Hxub) | apply Qlt_le_weak; exact Hqgt]. }
           rewrite (ir2_abs_sub (a # b)%Q (dms5_x n0) Hside).
           apply (Qle_trans _ ((1 # (4 * b))%Q)).
           { apply (Qle_trans _ ((3 # (16 * (b * b)))%Q)).
             - unfold Qle. cbn [Qnum Qden].
               rewrite ?Pos2Z.inj_mul. pose proof (Pos2Z.is_pos b). nia.
             - unfold Qle. cbn [Qnum Qden].
               rewrite ?Pos2Z.inj_mul. nia. }
           apply (Qle_trans _ (((a # b)%Q - (9#4))%Q)).
           { assert (Hgap : (9 * Z.pos b < 4 * a)%Z).
             { pose proof Hqgt as Hh. unfold Qlt, Qmult in Hh.
               cbn [Qnum Qden] in Hh. nia. }
             unfold Qle, Qminus, Qplus, Qopp;
               cbn [Qnum Qden Qminus Qplus Qopp Qmult];
               rewrite ?Pos2Z.inj_mul; nia. }
           apply (Qplus_le_compat (a # b)%Q (a # b)%Q (- (9#4))%Q
                    (- dms5_x n0)%Q).
           { apply Qle_refl. }
           { apply (Qopp_le_compat (dms5_x n0) (9#4)%Q
                      (QleT'_to_Qle _ _ Hxub)). }
        -- (* 分支三：5 < q² 且 q ≤ 9/4 *)
           assert (Hzpos : (5 * (Z.pos b * Z.pos b) < a * a)%Z).
           { pose proof Hlt5 as Hh. unfold Qlt, Qmult in Hh.
             cbn [Qnum Qden] in Hh. rewrite (Pos2Z.inj_mul b b) in Hh. nia. }
           assert (Hmu : Qle (1 # (b * b)) ((a # b)%Q * (a # b)%Q - 5%Q)%Q).
           { unfold Qle, Qminus, Qmult, Qplus, Qopp;
               cbn [Qnum Qden Qminus Qmult Qplus Qopp];
               rewrite ?Pos2Z.inj_mul; nia. }
           assert (Ed : (dms5_delta n0 == (2#1) * dms5_e n0)%Q)
             by (unfold dms5_e; ring).
           assert (Hdel : Qle (dms5_delta n0) ((1 # (8 * (b * b)))%Q)).
           { rewrite Ed. apply (Qle_trans _ ((2#1) * ((1 # (16 * (b * b)))%Q))).
             - apply (ir2_mult_le_compat_l (dms5_e n0)
                        ((1 # (16 * (b * b)))%Q) (2#1));
                 [exact Heb | unfold Qle; cbn [Qnum Qden]; lia].
             - apply qeq_le. unfold Qeq, Qmult;
                 cbn [Qnum Qden Qmult]; rewrite ?Pos2Z.inj_mul; ring. }
           assert (Hmud : Qle (((1 # (b * b))%Q - (1 # (8 * (b * b)))%Q))
                              ((((a # b)%Q * (a # b)%Q - 5%Q)
                                - dms5_delta n0)%Q)).
           { apply (Qplus_le_compat (1 # (b * b))
                      ((a # b)%Q * (a # b)%Q - 5%Q)%Q
                      (- (1 # (8 * (b * b))))%Q (- dms5_delta n0)%Q).
             - exact Hmu.
             - apply (Qopp_le_compat (dms5_delta n0)
                        ((1 # (8 * (b * b)))%Q) Hdel). }
           assert (HDpos : Qle 0%Q
                              ((((a # b)%Q * (a # b)%Q - 5%Q)
                                - dms5_delta n0)%Q)).
           { apply (Qle_trans 0%Q
                  (((1 # (b * b))%Q - (1 # (8 * (b * b)))%Q))%Q _).
             - unfold Qle, Qminus, Qmult, Qplus, Qopp;
                 cbn [Qnum Qden Qminus Qmult Qplus Qopp];
                 rewrite ?Pos2Z.inj_mul; nia.
             - exact Hmud. }
           assert (Hqxp : Qlt 0%Q ((a # b)%Q + dms5_x n0)%Q).
           { apply (ir2_qpos_add (a # b)%Q (dms5_x n0));
               [exact Hq0 | exact Hxpos]. }
           assert (Hqxn : ~ ((a # b)%Q + dms5_x n0 == 0%Q)).
           { intro Hc. apply (Qlt_not_eq 0%Q ((a # b)%Q + dms5_x n0) Hqxp).
             apply Qeq_sym. exact Hc. }
           assert (Hbridge : (((a # b)%Q - dms5_x n0) ==
              ((((a # b)%Q * (a # b)%Q - 5%Q) - dms5_delta n0)%Q
                * Qinv ((a # b)%Q + dms5_x n0)))%Q).
           { pose proof (bno_mul_div_self ((a # b)%Q + dms5_x n0) Hqxn) as Hbd.
             unfold Qdiv in Hbd. rewrite Qmult_1_l in Hbd.
             assert (Hpm : (((((a # b)%Q - dms5_x n0) * ((a # b)%Q + dms5_x n0))
                              * Qinv ((a # b)%Q + dms5_x n0))
                             == ((a # b)%Q - dms5_x n0))%Q).
             { rewrite <- (Qmult_assoc ((a # b)%Q - dms5_x n0)
                            ((a # b)%Q + dms5_x n0)
                            (Qinv ((a # b)%Q + dms5_x n0))).
               rewrite Hbd. apply Qmult_1_r. }
             rewrite ir2_sq_diff in Hpm.
             assert (Hsh : (((a # b)%Q * (a # b)%Q - dms5_x n0 * dms5_x n0)
                             == (((a # b)%Q * (a # b)%Q - 5%Q)
                                 - dms5_delta n0))%Q)
               by (unfold dms5_delta; ring).
             rewrite Hsh in Hpm. exact (Qeq_sym _ _ Hpm). }
           assert (Hqxb : Qle ((a # b)%Q + dms5_x n0) (9#2)%Q).
           { apply (Qle_trans _ (((9#4) + (9#4))%Q)).
             - apply (Qplus_le_compat (a # b)%Q (9#4)%Q (dms5_x n0) (9#4)%Q);
                 [exact Hq32 | exact (QleT'_to_Qle _ _ Hxub)].
             - apply qeq_le. reflexivity. }
           assert (Hinv : Qle (Qinv (9#2)) (Qinv ((a # b)%Q + dms5_x n0))).
           { apply (ir2_inv_le ((a # b)%Q + dms5_x n0) (9#2)%Q);
               [exact Hqxp | exact Hqxb]. }
           assert (Hd3 : Qle ((3 # (16 * (b * b)))%Q)
              (((((a # b)%Q * (a # b)%Q - 5%Q) - dms5_delta n0)%Q)
                * (2#9))%Q).
           { apply (Qle_trans _
                ((((1 # (b * b))%Q - (1 # (8 * (b * b)))%Q)) * (2#9))%Q).
             - unfold Qle, Qminus, Qmult, Qplus, Qopp;
                 cbn [Qnum Qden Qminus Qmult Qplus Qopp];
                 rewrite ?Pos2Z.inj_mul; nia.
             - apply (Qmult_le_compat_r _ _ (2#9));
                 [exact Hmud | unfold Qle; cbn [Qnum Qden]; lia]. }
           assert (Hbige : Qle
              (((((a # b)%Q * (a # b)%Q - 5%Q) - dms5_delta n0)%Q) * (2#9))%Q
              ((a # b)%Q - dms5_x n0)%Q).
           { rewrite Hbridge.
             assert (E29 : ((2#9)%Q == Qinv (9#2))) by reflexivity.
             rewrite E29.
             apply (ir2_mult_le_compat_l (Qinv (9#2))
                      (Qinv ((a # b)%Q + dms5_x n0))
                      ((((a # b)%Q * (a # b)%Q - 5%Q) - dms5_delta n0)%Q)).
             - exact Hinv.
             - exact HDpos. }
           assert (Hsum0 : Qle 0%Q ((3 # (16 * (b * b)))%Q)).
           { unfold Qle. cbn [Qnum Qden]. lia. }
           assert (Hge0 : Qle 0%Q ((a # b)%Q - dms5_x n0)%Q).
           { apply (Qle_trans 0%Q ((3 # (16 * (b * b)))%Q)
                    ((a # b)%Q - dms5_x n0)%Q).
             - exact Hsum0.
             - apply (Qle_trans _
                        (((((a # b)%Q * (a # b)%Q - 5%Q)
                           - dms5_delta n0)%Q) * (2#9))%Q).
               + exact Hd3.
               + exact Hbige. }
           assert (Hside : Qle (dms5_x n0) (a # b)%Q).
           { apply (Qle_trans (dms5_x n0)
                     (((a # b)%Q - dms5_x n0 + dms5_x n0)%Q) (a # b)%Q).
             - apply (Qle_trans (dms5_x n0) ((0%Q + dms5_x n0)%Q)
                      (((a # b)%Q - dms5_x n0 + dms5_x n0)%Q)).
               + rewrite Qplus_0_l. apply Qle_refl.
               + apply (Qplus_le_compat 0%Q ((a # b)%Q - dms5_x n0)%Q
                          (dms5_x n0) (dms5_x n0));
                   [exact Hge0 | apply Qle_refl].
             - apply qeq_le.
               unfold Qeq, Qminus, Qplus, Qopp;
                 cbn [Qnum Qden Qplus Qopp];
                 rewrite ?Pos2Z.inj_mul; ring. }
           rewrite (ir2_abs_sub (a # b)%Q (dms5_x n0) Hside).
           exact (Qle_trans _ _ _ Hd3 Hbige).
      * exfalso. exact (dms5_no_sqrt5 (a # b)%Q (qeq_imp_qeqT _ _ (Qeq_sym _ _ Heq))).
  - (* 分支一：q ≤ 0 *)
    assert (Hqx : Qle (a # b)%Q (dms5_x n0)).
    { apply (Qle_trans (a # b)%Q 0%Q (dms5_x n0)).
      - exact Hq0.
      - apply (Qle_trans 0%Q (9#5) (dms5_x n0)).
        + unfold Qle. cbn [Qnum Qden]. lia.
        + exact Hxlb. }
    rewrite (Qabs_Qminus (a # b)%Q (dms5_x n0)).
    rewrite (ir2_abs_sub (dms5_x n0) (a # b)%Q Hqx).
    apply (Qle_trans _ (9#5)%Q).
    + unfold Qle. cbn [Qnum Qden].
      rewrite ?Pos2Z.inj_mul. pose proof (Pos2Z.is_pos b). nia.
    + pose proof (Qopp_le_compat (a # b)%Q 0%Q Hq0) as Hnq.
      cbn [Qopp Z.opp] in Hnq.
      apply (Qle_trans (9#5) (dms5_x n0) ((dms5_x n0 + (- (a # b)))%Q)).
      * exact Hxlb.
      * apply (Qle_trans (dms5_x n0) ((dms5_x n0 + 0%Q)%Q)
                 ((dms5_x n0 + (- (a # b)))%Q)).
        -- rewrite Qplus_0_r. apply Qle_refl.
        -- apply (Qplus_le_compat (dms5_x n0) (dms5_x n0) 0%Q
                   (- (a # b))%Q); [apply Qle_refl | exact Hnq].
Qed.

(* ============================================================ *)
(* S8：统一逃逸窗（n0 := den(q)+3 四分支）与边距成形包裹                   *)
(* ============================================================ *)

Definition dms5_escape_closed_window : forall (a : Z) (b : positive),
  sigT (fun n : nat => And ((Z.to_nat (Z.pos b) + 3 <= n)%nat)
        (QltT (dms5_e n) (Qabs (((a # b)%Q - dms5_x n)%Q)))).
Proof.
  intros a b.
  exists (Z.to_nat (Z.pos b) + 3)%nat.
  split.
  - apply Nat.le_refl.
  - assert (Hn01 : (1 <= Z.to_nat (Z.pos b) + 3)%nat).
    { pose proof (Nat.le_0_l (Z.to_nat (Z.pos b))). lia. }
    pose proof (dms5_e_bnd b (Z.to_nat (Z.pos b) + 3) (Nat.le_refl _)) as Heb.
    pose proof (dms5_margin_trine a b (Z.to_nat (Z.pos b) + 3) Hn01 Heb) as Htri.
    assert (Hstep : Qlt ((1 # (16 * (b * b)))%Q)
                         (((1 # (16 * (b * b)))%Q
                           + (1 # (16 * (b * b)))%Q)%Q)).
    { unfold Qlt, Qplus. cbn [Qnum Qden Qplus].
      rewrite ?Pos2Z.inj_mul. pose proof (Pos2Z.is_pos b). nia. }
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (dms5_e (Z.to_nat (Z.pos b) + 3))
            (((1 # (16 * (b * b)))%Q + (1 # (16 * (b * b)))%Q)%Q)
            (Qabs (((a # b)%Q - dms5_x (Z.to_nat (Z.pos b) + 3))%Q))).
    + apply (Qle_lt_trans (dms5_e (Z.to_nat (Z.pos b) + 3))
               (1 # (16 * (b * b)))%Q _).
      * exact (QleT'_to_Qle _ _ Heb).
      * exact Hstep.
    + apply (Qle_trans _ ((3 # (16 * (b * b)))%Q)).
      * unfold Qle, Qplus. cbn [Qnum Qden Qplus].
        rewrite ?Pos2Z.inj_mul. pose proof (Pos2Z.is_pos b). nia.
      * exact (QleT'_to_Qle _ _ Htri).
Defined.

Lemma dms5_margin_closed : forall (a : Z) (b : positive) (n0 : nat),
  (1 <= n0)%nat -> QleT' (dms5_e n0) ((1 # (16 * (b * b)))%Q) ->
  QleT' (((1 # (16 * (b * b)))%Q + (1 # (16 * (b * b)))%Q + dms5_e n0)%Q)
      (Qabs (((a # b)%Q - dms5_x n0)%Q)).
Proof.
  intros a b n0 Hn01 Heb.
  apply QleT'_to_Qle in Heb.
  apply Qle_to_QleT'.
  apply (Qle_trans _ ((3 # (16 * (b * b)))%Q)).
  - apply (Qle_trans _ (((1 # (16 * (b * b)))%Q
                          + (1 # (16 * (b * b)))%Q
                          + (1 # (16 * (b * b)))%Q)%Q)).
    + apply Qplus_le_compat; [apply Qle_refl | exact Heb].
    + apply qeq_le. unfold Qeq, Qplus, Qmult.
      cbn [Qnum Qden Qplus Qmult]. rewrite ?Pos2Z.inj_mul. ring.
  - exact (QleT'_to_Qle _ _
             (dms5_margin_trine a b n0 Hn01 (Qle_to_QleT' _ _ Heb))).
Qed.

(* ============================================================ *)
(* S9：主定理（闭式常元 1/(16b²) + Qeq 确定 + 实度量分离）与 q 形推论       *)
(* ============================================================ *)

Theorem u5c_sqrt5_closed_measure : forall (a : Z) (b : positive),
  sigT (fun c : Q => And (QltT 0 c)
    (And (QeqT c ((1 # (16 * (b * b)))%Q))
         (real_lt (real_const c)
            (real_metric (existT (fun u : Qseq => cauchy u) dms5_x
                              (lic_seq_cauchy dms5_x dms5_e dms5_tail
                                              dms5_vanish))
               (real_const ((a # b)%Q)))))).
Proof.
  intros a b.
  destruct (dms5_escape_closed_window a b) as [n0 [Hge Hesc]].
  pose proof (dms5_e_bnd b n0 Hge) as Heb.
  assert (Hn01 : (1 <= n0)%nat)
    by (pose proof (Nat.le_0_l (Z.to_nat (Z.pos b))); lia).
  assert (Hc0 : QltT 0 ((1 # (16 * (b * b)))%Q)).
  { apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. lia. }
  pose proof (dms5_margin_closed a b n0 Hn01 Heb) as Hraw.
  apply QleT'_to_Qle in Hraw.
  rewrite <- (lic_qlt_minus_add_r (Qabs (((a # b)%Q - dms5_x n0)%Q))
                (dms5_e n0)) in Hraw.
  assert (Hmargin : QleT' (((1 # (16 * (b * b)))%Q
                             + (1 # (16 * (b * b)))%Q))
                          (((Qabs (((a # b)%Q - dms5_x n0)%Q))
                            - dms5_e n0)%Q)).
  { exact (u5c_qle_add_cancel_r _ _ (dms5_e n0) (Qle_to_QleT' _ _ Hraw)). }
  exists ((1 # (16 * (b * b)))%Q).
  split.
  - exact Hc0.
  - split.
    + apply qeq_imp_qeqT. apply Qeq_refl.
    + exact (snd (projT2 (dmec_escape_to_dist_any dms5_x dms5_e dms5_tail
                dms5_vanish (a # b)%Q n0 Hn01 Hesc
                ((1 # (16 * (b * b)))%Q) Hc0 Hmargin))).
Qed.

(* 推论（q 形：QDen 确定）。语句面最小修复申报：原正分母形
   (1 # (16 * (QDen q * QDen q)))%Q 无法 typecheck（# 记号右元须为
   positive，而 QDen q : Z），依任务指令先例改 Z 分母除法形
   (1#1) / ((16 * (QDen q * QDen q))%Z # 1)（有理数值恒同，即
   1/(16·QDen q²)）；Ekey 以 Pos2Z.inj_mul 双步归束 Qinv 后
   conversion 反射收尾。 *)
Theorem u5c_sqrt5_closed_measure_q : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (And (QeqT c (((1 # 1)%Q / ((16 * (QDen q * QDen q))%Z # 1)%Q)%Q))
         (real_lt (real_const c)
            (real_metric (existT (fun u : Qseq => cauchy u) dms5_x
                              (lic_seq_cauchy dms5_x dms5_e dms5_tail
                                              dms5_vanish))
               (real_const q))))).
Proof.
  intro q. destruct q as [a b].
  destruct (u5c_sqrt5_closed_measure a b) as [c [Hc0 [Heq Hlt]]].
  exists c. split.
  - exact Hc0.
  - split.
    + assert (Ekey : Qinv ((16 * (Z.pos b * Z.pos b))%Z # 1)%Q
                       == (1 # (16 * (b * b)))%Q).
      { rewrite <- (Pos2Z.inj_mul b b).
        rewrite <- (Pos2Z.inj_mul 16 (b * b)). reflexivity. }
      assert (EQd : QDen ((a # b)%Q) = Z.pos b) by reflexivity.
      apply qeq_imp_qeqT.
      unfold Qdiv. rewrite EQd. rewrite Qmult_1_l. rewrite Ekey.
      exact (qeqT_imp_qeq _ _ Heq).
    + exact Hlt.
Qed.

From Stdlib Require Import Extraction.
Separate Extraction u5c_sqrt5_closed_measure u5c_sqrt5_closed_measure_q.

Print Assumptions u5c_sqrt5_closed_measure.
Print Assumptions u5c_sqrt5_closed_measure_q.
