(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(* 五字段指针｜使命：√5（Newton 序列 X = lim x(n)，x(0)=9/4、
   x(n+1) = (x(n) + 5/x(n))/2）的无理性分离定理——逃逸点显式装配版。
   对任意有理数 q，取逃逸窗见证 is5_escape q 的显式逃逸点 n0
   （e(n0) < |q − x(n0)|，e(n) = (x(n)² − 5)/2），由通用分离引理
   u5c_escape_to_dist 得 Q 层正分离常数 c := (|q − x(n0)| − e(n0))/2 使
   real_const c < |√5 − q|。装配实例与 u5c_inst_sqrt3 逐条同构；种子取 9/4
   而非 2：√5 > 2 使自 2 起步的首项误差 x(0)²−5 为负，自 9/4（即 Newton
   自 2 迭代一步）起步则全列误差为正且序列单调降，与 √2/√3 实例的
   引理假设形完全一致。附带供件：mod-5 非平方引理（整数层剩余表＋
   自然数归纳整除下降，零经典逻辑；既约性并不需要）与闭式定量常数
   c(q) = 1/(b(|a|+3b)) 的 Q 层定量形（正性＋c(q) ≤ |q²−5|/3，
   其中 |√5−q| ≥ |q²−5|/(|q|+√5) ≥ (1/3)|q²−5| 的实层一段属
   实极限值定理，不在本件范围）。
   依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、SumInvFactEscape、UpReqBanachNormOpp、
   UpReqIrrationalCriterion、UpReqSqrt3Irrational、u5c_bridge；Stdlib QArith、Qabs、ZArith、Arith、Bool。
   对标行：UpReqSqrt3Irrational.v is3_escape、is3_sqrt3_irrational_criterion
   （√5 实例为同构改编）；u5c_bridge.v u5c_escape_to_dist。
   构造性注记：语句面全 Set 层，零 Prop 前提位；mod-5 引理为剩余表
   有限枚举＋归纳下降的纯整数构造，零经典逻辑；见证解构与引理装配全构造。
   编译配方：coqc -native-compiler no -q -Q . "" -Q <ConstructiveWorld_vo 树> ""。 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
Require Import u5c_bridge.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* S1：mod-5 非平方引理（剩余表＋整除下降）                            *)
(* ============================================================ *)

(* 平方余态：z² ≡ 0 (mod 5) 则 z ≡ 0 (mod 5)——
   剩余 1..4 的平方各为 1 或 4（mod 5），逐格枚举 *)
Lemma is5_mod5_sq : forall z : Z, ((z * z) mod 5 = 0)%Z -> (z mod 5 = 0)%Z.
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
Lemma is5_no_sqrtZ : forall a b : Z, (0 < b)%Z -> (a * a = 5 * (b * b))%Z -> False.
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
      assert (Hae : (a mod 5 = 0)%Z) by (apply is5_mod5_sq; exact Ham).
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
      assert (Hbe : (b mod 5 = 0)%Z) by (apply is5_mod5_sq; exact Hbm).
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

Lemma is5_no_sqrt5 : forall q : Q, ~ (q * q == 5%Q).
Proof.
  intros q Hq. destruct q as [a b].
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (Heq : (a * a = 5 * (Z.pos b * Z.pos b))%Z).
  { unfold Qeq, Qmult in Hq. cbn in Hq.
    assert (Hb1 : (Z.pos (b * b) = Z.pos b * Z.pos b)%Z) by apply Pos2Z.inj_mul.
    lia. }
  exact (is5_no_sqrtZ a (Z.pos b) Hb Heq).
Qed.

(* ============================================================ *)
(* S2：闭式定量常数 c(q) = 1/(b(|a|+3b)) 的 Q 层定量形                 *)
(* ============================================================ *)

(* 交叉乘恒等式：q = a/b ⟹ (q² − 5)·b² = a² − 5b²（环语言重排＋
   构造子可逆计算，不经 Qinv 归一） *)
Lemma is5_frac_sq_cross : forall (q : Q) (a b : Z),
  q == (a # 1)%Q / ((b # 1)%Q) -> (0 < b)%Z ->
  ((q * q - 5%Q)%Q * ((b * b) # 1)%Q == ((a * a - 5 * (b * b)) # 1)%Q)%Q.
Proof.
  intros q a b Hq Hb.
  assert (Hb01 : Qlt 0%Q ((b # 1)%Q)) by (unfold Qlt; cbn [Qnum Qden]; lia).
  assert (Hne0 : ~ ((b # 1)%Q == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0%Q ((b # 1)%Q) Hb01).
    apply Qeq_sym. exact Hc. }
  assert (Hss : (((b # 1)%Q * Qinv ((b # 1)%Q))%Q == 1%Q)).
  { pose proof (bno_mul_div_self ((b # 1)%Q) Hne0) as H1.
    unfold Qdiv in H1. rewrite Qmult_1_l in H1. exact H1. }
  assert (Hqb : ((q * (b # 1)%Q)%Q == (a # 1)%Q)%Q).
  { rewrite Hq. unfold Qdiv.
    rewrite <- (Qmult_assoc (a # 1)%Q (Qinv ((b # 1)%Q)) ((b # 1)%Q)).
    rewrite (Qmult_comm (Qinv ((b # 1)%Q)) ((b # 1)%Q)).
    rewrite Hss. apply Qmult_1_r. }
  assert (Hbb1 : (((b * b) # 1)%Q == ((b # 1)%Q * (b # 1)%Q)%Q)) by reflexivity.
  assert (Haa1 : (((a # 1)%Q * (a # 1)%Q)%Q == ((a * a) # 1)%Q)) by reflexivity.
  assert (H551 : (((5 # 1)%Q * ((b # 1)%Q * (b # 1)%Q))%Q == ((5 * (b * b)) # 1)%Q))
    by reflexivity.
  assert (Hqq2 : ((q * q * ((b * b) # 1)%Q)%Q == ((a # 1)%Q * (a # 1)%Q)%Q)).
  { rewrite Hbb1.
    assert (Hrq : ((q * q * ((b # 1)%Q * (b # 1)%Q))%Q
                   == (q * (b # 1)%Q) * (q * (b # 1)%Q))%Q) by ring.
    rewrite Hrq. rewrite Hqb. reflexivity. }
  assert (Hcross : (((q * q - 5%Q)%Q * ((b * b) # 1)%Q)%Q
                    == ((q * q) * ((b * b) # 1)%Q
                        - (5 # 1)%Q * ((b * b) # 1)%Q)%Q)) by ring.
  rewrite Hcross. rewrite Hqq2. rewrite Haa1. rewrite H551.
  (* ((a*a)#1 − (5*(b*b))#1) == ((a*a − 5*(b*b))#1)：Z 层直算 *)
  unfold Qminus, Qeq, Qopp, Qplus. cbn [Qnum Qden]. lia.
Qed.

(* 整值间隙的 Q 层定量形：q = a/b（b > 0）且 q² ≠ 5 时
   b²·|q² − 5| ≥ 1（由 |a² − 5b²| ≥ 1，mod-5 引理保证非退化） *)
Lemma is5_sq_gap_ge1 : forall (q : Q) (a b : Z),
  q == (a # 1)%Q / ((b # 1)%Q) -> (0 < b)%Z -> (a * a <> 5 * (b * b))%Z ->
  Qle 1%Q (Qabs ((q * q - 5%Q)%Q) * ((b * b) # 1)%Q).
Proof.
  intros q a b Hq Hb Hne.
  pose proof (is5_frac_sq_cross q a b Hq Hb) as Hcross.
  assert (E : (Qabs ((q * q - 5%Q)%Q) * ((b * b) # 1)%Q)%Q
              == Qabs (((q * q - 5%Q)%Q * ((b * b) # 1)%Q))).
  { setoid_rewrite (Qabs_Qmult (q * q - 5%Q)%Q (((b * b) # 1)%Q)).
    assert (Habsb : Qabs (((b * b) # 1)%Q) == ((b * b) # 1)%Q).
    { apply Qabs_pos. unfold Qle. cbn [Qnum Qden]. lia. }
    setoid_rewrite Habsb. apply Qeq_refl. }
  rewrite E. rewrite Hcross.
  destruct (Z_lt_le_dec (a * a - 5 * (b * b)) 0) as [Hneg | Hpos].
  - (* a² − 5b² < 0：Qabs_neg 直取＋Qopp_le_compat 保号 *)
    assert (HXle : ((a * a - 5 * (b * b)) # 1)%Q <= 0%Q).
    { unfold Qle. cbn [Qnum Qden]. lia. }
    assert (Hneg1 : ((a * a - 5 * (b * b)) # 1)%Q <= (-1)%Q).
    { unfold Qle. cbn [Qnum Qden]. lia. }
    pose proof (Qopp_le_compat _ _ Hneg1) as Hopp.
    rewrite (Qabs_neg _ HXle). exact Hopp.
  - (* a² − 5b² ≥ 1（Hne 排除零） *)
    assert (Habsx : Qabs (((a * a - 5 * (b * b)) # 1)%Q)
                    == ((a * a - 5 * (b * b)) # 1)%Q).
    { apply Qabs_pos. unfold Qle. cbn [Qnum Qden]. lia. }
    rewrite Habsx. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* 三分之一逆元恒等式：(1/3)·(1/s) = 1/(3s)（逆元唯一性手工链，
   全原语引理，不经 Qinv 体归约） *)
Lemma is5_third_inv : forall s : Q, Qlt 0 s ->
  ((1 # 3) * Qinv s == Qinv ((3 # 1) * s))%Q.
Proof.
  intros s Hs.
  assert (Hs0 : ~ (s == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0%Q s Hs). apply Qeq_sym. exact Hc. }
  assert (Hss1 : (Qinv s * s == 1%Q)%Q).
  { pose proof (bno_mul_div_self s Hs0) as H1.
    unfold Qdiv in H1. rewrite Qmult_1_l in H1.
    rewrite (Qmult_comm s) in H1. exact H1. }
  assert (H3s0 : ~ ((3 # 1) * s == 0%Q)).
  { intro Hc.
    assert (HH : Qlt 0%Q ((3 # 1) * s)%Q).
    { apply (Qmult_lt_0_compat (3 # 1) s); [unfold Qlt; cbn [Qnum Qden]; lia | exact Hs]. }
    apply (Qlt_not_eq 0%Q _ HH). apply Qeq_sym. exact Hc. }
  (* 逆元唯一性：x·(3s) == 1 ⟹ x == /(3s) *)
  assert (Huniq : forall x : Q, (x * ((3 # 1) * s) == 1%Q)%Q ->
    x == Qinv ((3 # 1) * s)).
  { intros x Hx.
    pose proof (bno_mul_div_self ((3 # 1) * s) H3s0) as Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    rewrite <- (Qmult_1_r x). rewrite <- Hb.
    rewrite (Qmult_assoc x ((3 # 1) * s) (Qinv ((3 # 1) * s))).
    rewrite Hx. rewrite Qmult_1_l. apply Qeq_refl. }
  apply Huniq.
  (* ((1/3)·/s)·(3s) == 1 *)
  assert (Hr : ((((1 # 3) * Qinv s) * ((3 # 1) * s))
                == ((1 # 3) * (3 # 1)) * (Qinv s * s))%Q) by ring.
  rewrite Hr.
  assert (H13 : (((1 # 3) * (3 # 1))%Q == 1%Q)) by reflexivity.
  rewrite H13. rewrite Hss1. rewrite Qmult_1_r. apply Qeq_refl.
Qed.

(* 闭式常数：c(q) := 1/(b(|a|+3b)) 为正，且 c(q) ≤ |q²−5|/(3b²)
   （结合 b ≥ 1 得 c(q) ≤ |q²−5|/3；再结合实层
   |√5−q| ≥ |q²−5|/(|q|+√5) 与 √5 < 3 即得 |√5−q| ≥ c(q)；
   实层一段属实极限值定理，不在本件范围） *)
Lemma is5_closed_form_const : forall (q : Q) (a b : Z),
  q == (a # 1)%Q / ((b # 1)%Q) -> (0 < b)%Z -> (a * a <> 5 * (b * b))%Z ->
  And (QltT 0 (Qinv ((b * (Z.abs a + 3 * b)) # 1)%Q))
      (Qle (Qinv ((b * (Z.abs a + 3 * b)) # 1)%Q)
           ((1 # 3) * Qabs ((q * q - 5%Q)%Q))%Q).
Proof.
  intros q a b Hq Hb Hne. split.
  - apply Qlt_to_QltT.
    apply (Qinv_lt_0_compat ((b * (Z.abs a + 3 * b)) # 1)%Q).
    unfold Qlt. cbn [Qnum Qden]. pose proof (Z.abs_nonneg a). lia.
  - assert (Hbbpos : Qlt 0%Q (((b * b) # 1)%Q)).
    { unfold Qlt. cbn [Qnum Qden]. lia. }
    assert (Hstep1 : Qle (Qinv ((b * (Z.abs a + 3 * b)) # 1)%Q)
                         ((1 # 3) * Qinv (((b * b) # 1)%Q))%Q).
    { apply (Qle_trans _ (Qinv ((3 # 1) * ((b * b) # 1))%Q)).
      - apply (ir2_inv_le ((3 # 1) * ((b * b) # 1))
                 ((b * (Z.abs a + 3 * b)) # 1)).
        + unfold Qlt, Qmult. cbn [Qnum Qden]. lia.
        + unfold Qle, Qmult. cbn [Qnum Qden].
          pose proof (Z.abs_nonneg a). lia.
      - apply qeq_le. apply Qeq_sym.
        exact (is5_third_inv (((b * b) # 1)%Q) Hbbpos). }
    assert (Hstep2 : Qle ((1 # 3) * Qinv (((b * b) # 1)%Q)%Q)
                         ((1 # 3) * Qabs ((q * q - 5%Q)%Q))%Q).
    { rewrite (Qmult_comm (1 # 3) (Qinv (((b * b) # 1)%Q))).
      rewrite (Qmult_comm (1 # 3) (Qabs ((q * q - 5%Q)%Q))).
      apply Qmult_le_compat_r.
      - pose proof (is5_sq_gap_ge1 q a b Hq Hb Hne) as Hgap.
        apply ir2_ge_inv.
        + exact Hbbpos.
        + rewrite (Qmult_comm (((b * b) # 1)%Q)). exact Hgap.
      - unfold Qle. cbn [Qnum Qden]. lia. }
    apply (Qle_trans _ ((1 # 3) * Qinv (((b * b) # 1)%Q))%Q);
      [exact Hstep1 | exact Hstep2].
Qed.

(* ============================================================ *)
(* S3：Newton 序列（x_0=9/4，步 (x+5/x)/2）及其 Q 层基本量              *)
(* ============================================================ *)

Fixpoint is5_x (n : nat) : Q :=
  match n with
  | O => (9 # 4)%Q
  | Datatypes.S m => (is5_x m + 5%Q / is5_x m) * (1 # 2)
  end.

Definition is5_delta (n : nat) : Q := is5_x n * is5_x n - 5%Q.
Definition is5_e (n : nat) : Q := (1 # 2) * is5_delta n.

Lemma is5_x1 : is5_x 1 == (161 # 72).
Proof. reflexivity. Qed.

(* 5j² ≤ 2^{j+8}（is3_pow7sq 同构：供 q²<5 支 5·den² ≤ qp(SN) 严格窗） *)
Lemma is5_step5 : forall j : nat, (3 <= j)%nat -> (10 * j + 5 <= 5 * j * j)%nat.
Proof.
  induction j as [|j IH]; intro Hj.
  - lia.
  - replace (5 * Datatypes.S j * Datatypes.S j)%nat
      with (5 * j * j + 10 * j + 5)%nat by ring.
    destruct (Nat.le_gt_cases 4 (Datatypes.S j)) as [Hj4 | Hjlt].
    + assert (Hj3 : (3 <= j)%nat) by lia.
      specialize (IH Hj3). lia.
    + destruct j as [|[|j']]; lia.
Qed.

Lemma is5_pow5sq : forall j : nat, (5 * j * j <= 2 ^ (j + 8))%nat.
Proof.
  assert (Haux : forall j : nat, (5 * j * j <= 2 ^ (8 + j))%nat).
  { induction j as [|j IH].
    - apply (proj1 (Nat.leb_le _ _)). vm_compute. reflexivity.
    - replace (8 + Datatypes.S j)%nat with (Datatypes.S (8 + j))%nat by lia.
      rewrite Nat.pow_succ_r'.
      destruct (Nat.le_gt_cases 3 j) as [Hj3 | Hjlt].
      + replace (5 * Datatypes.S j * Datatypes.S j)%nat
          with (5 * j * j + 10 * j + 5)%nat by ring.
        pose proof (is5_step5 j Hj3). lia.
      + destruct j as [|j'].
        * apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
        * destruct j' as [|j''].
          -- apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
          -- destruct j'' as [|j'''].
             ++ apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
             ++ lia. }
  intro j. rewrite (Nat.add_comm j 8). apply Haux.
Qed.

(* 序列基本性质（正性/下界 9/5/单调/δ 代数） *)

Lemma is5_div5_pos : forall v : Q, Qlt 0 v -> Qlt 0 (5%Q / v).
Proof.
  intros v Hv. unfold Qdiv.
  apply (Qmult_lt_0_compat (5#1) (Qinv v)).
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - apply (Qinv_lt_0_compat v Hv).
Qed.

Lemma is5_x_pos : forall n : nat, Qlt 0 (is5_x n).
Proof.
  induction n as [|n IH].
  - unfold Qlt. cbn [is5_x Qnum Qden]. lia.
  - cbn [is5_x]. apply (Qmult_lt_0_compat _ (1 # 2)).
    + apply ir2_qpos_add; [exact IH | apply is5_div5_pos; exact IH].
    + unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

Lemma is5_delta_succ_mul : forall n : nat,
  (is5_delta (Datatypes.S n) * (4 * (is5_x n * is5_x n)) == is5_delta n * is5_delta n)%Q.
Proof.
  intro n. unfold is5_delta. cbn [is5_x].
  field.
  intro Heq. apply (Qlt_not_eq 0%Q (is5_x n) (is5_x_pos n)).
  apply Qeq_sym. exact Heq.
Qed.

Lemma is5_delta_ge0 : forall n : nat, Qle 0 (is5_delta n).
Proof.
  induction n as [|n IH].
  - unfold is5_delta, Qle, Qmult, Qminus, Qplus, Qopp.
    cbn [is5_x Qnum Qden]. lia.
  - assert (HM : Qlt 0%Q (4 * (is5_x n * is5_x n))).
    { apply (Qmult_lt_0_compat (4#1) (is5_x n * is5_x n)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - apply (Qmult_lt_0_compat (is5_x n) (is5_x n)); exact (is5_x_pos n). }
    pose proof (is5_delta_succ_mul n) as Hmul.
    assert (Hsq : Qle 0 (is5_delta n * is5_delta n)).
    { destruct (is5_delta n) as [dn dd] eqn:Ed.
      pose proof IH as H0.
      rewrite ?Ed in H0. unfold Qle in H0. cbn [Qnum Qden] in H0.
      unfold Qle, Qmult. rewrite ?Ed. cbn [Qnum Qden]. nia. }
    apply (ir2_ge0_of_mul _ _ HM).
    rewrite Hmul. exact Hsq.
Qed.

Lemma is5_delta_pos : forall n : nat, Qlt 0 (is5_delta n).
Proof.
  intro n. pose proof (is5_delta_ge0 n) as Hge.
  destruct (Qeq_dec (is5_delta n) 0%Q) as [Hz | Hne].
  - exfalso. apply (is5_no_sqrt5 (is5_x n)).
    unfold is5_delta in Hz.
    rewrite <- (lic_qlt_minus_add_r (is5_x n * is5_x n) 5%Q).
    rewrite Hz. reflexivity.
  - destruct (Qlt_le_dec 0%Q (is5_delta n)) as [Hlt | Hle].
    + exact Hlt.
    + exfalso. apply Hne. apply (Qle_antisym (is5_delta n) 0%Q Hle Hge).
Qed.

Lemma is5_sq_ge5 : forall n : nat, Qle 5%Q (is5_x n * is5_x n).
Proof.
  intro n. pose proof (is5_delta_ge0 n) as H.
  assert (Hr : ((is5_x n * is5_x n - 5) + 5 == is5_x n * is5_x n)%Q)
    by apply lic_qlt_minus_add_r.
  rewrite <- Hr.
  apply (Qle_trans 5%Q (0%Q + 5%Q)%Q ((is5_x n * is5_x n - 5%Q)%Q + 5%Q)%Q).
  - rewrite Qplus_0_l. apply Qle_refl.
  - apply Qplus_le_compat; [exact H | apply Qle_refl].
Qed.

Lemma is5_x_lb : forall n : nat, (9 # 5) <= is5_x n.
Proof.
  intro n. pose proof (is5_x_pos n) as Hp.
  destruct (Qlt_le_dec (is5_x n) (9#5)) as [Hlt | Hle].
  - exfalso.
    assert (H1 : Qlt ((is5_x n) * (is5_x n)) ((9#5) * (is5_x n))).
    { apply (Qmult_lt_compat_r (is5_x n) (9#5) (is5_x n)); [exact Hp | exact Hlt]. }
    assert (H2 : Qlt ((9#5) * (is5_x n)) ((9#5) * (9#5))).
    { rewrite (Qmult_comm (9#5) (is5_x n)).
      apply (Qmult_lt_compat_r (is5_x n) (9#5) (9#5)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - exact Hlt. }
    assert (H3 : Qlt (is5_x n * is5_x n) 5%Q).
    { apply (Qlt_trans _ ((9#5) * (9#5))).
      - apply (Qlt_trans _ ((9#5) * (is5_x n))); [exact H1 | exact H2].
      - unfold Qlt, Qmult. cbn [Qnum Qden]. lia. }
    apply (Qlt_not_le (is5_x n * is5_x n) 5%Q).
    + exact H3.
    + apply is5_sq_ge5.
  - exact Hle.
Qed.

Lemma is5_mono : forall n : nat, is5_x (Datatypes.S n) <= is5_x n.
Proof.
  intro n. cbn [is5_x].
  pose proof (is5_sq_ge5 n) as H5.
  pose proof (is5_x_pos n) as Hxp.
  destruct (is5_x n) as [a b] eqn:Ex.
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

Lemma is5_mono_le : forall n k : nat, (1 <= n)%nat -> (n <= k)%nat ->
  is5_x k <= is5_x n.
Proof.
  intros n k Hn1 Hnk.
  assert (Hgen : forall d : nat, is5_x (n + d) <= is5_x n).
  { induction d as [|d IHd].
    - rewrite Nat.add_0_r. apply Qle_refl.
    - replace (n + Datatypes.S d)%nat with (Datatypes.S (n + d))%nat by lia.
      apply (Qle_trans _ (is5_x (n + d))).
      + apply is5_mono.
      + exact IHd. }
  replace k with (n + (k - n))%nat by lia.
  apply Hgen.
Qed.

(* 上界 9/4 对全体 n 成立（种子即 9/4，全列单调降） *)
Lemma is5_x_ub : forall n : nat, is5_x n <= (9 # 4).
Proof.
  intro n. destruct n as [|n'].
  - cbn [is5_x]. apply Qle_refl.
  - apply (Qle_trans _ (is5_x 1)).
    + apply (is5_mono_le 1 (Datatypes.S n')); lia.
    + rewrite is5_x1. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* ============================================================ *)
(* S4：误差窗衰减（δ ≤ 1/16；δ(Sn) ≤ δn/192；e_n ≤ 1/2^{n+1}）        *)
(* ============================================================ *)

Lemma is5_delta_step : forall n : nat, (1 <= n)%nat -> Qle (is5_delta n) (1#16) ->
  Qle (is5_delta (Datatypes.S n)) ((1#192) * is5_delta n).
Proof.
  intros n Hn1 Hdu.
  pose proof (is5_x_pos n) as Hxp.
  assert (Hlb : Qle ((9#5) * (9#5)) (is5_x n * is5_x n)).
  { apply (Qle_trans _ ((9#5) * is5_x n)%Q).
    - apply ir2_mult_le_compat_l; [apply (is5_x_lb n) | unfold Qle; cbn; lia].
    - apply Qmult_le_compat_r; [apply (is5_x_lb n) | apply Qlt_le_weak; apply (is5_x_pos n)]. }
  assert (H12 : Qle 12%Q (4 * (is5_x n * is5_x n))).
  { apply (Qle_trans _ ((4#1) * ((9#5) * (9#5)))%Q).
    - unfold Qle, Qmult. cbn [Qnum Qden]. lia.
    - rewrite (Qmult_comm (4#1) ((9#5) * (9#5))).
      rewrite (Qmult_comm (4#1) (is5_x n * is5_x n)).
      apply Qmult_le_compat_r; [exact Hlb | unfold Qle; cbn; lia]. }
  pose proof (is5_delta_succ_mul n) as Hmul.
  pose proof (is5_delta_ge0 (Datatypes.S n)) as HdS0.
  assert (Ha : Qle (12 * is5_delta (Datatypes.S n)) (is5_delta n * is5_delta n)).
  { rewrite <- Hmul.
    rewrite (Qmult_comm (is5_delta (Datatypes.S n)) (4 * (is5_x n * is5_x n))).
    apply Qmult_le_compat_r; [exact H12 | exact HdS0]. }
  assert (Hb : Qle (is5_delta n * is5_delta n) ((1#16) * is5_delta n)).
  { apply (Qmult_le_compat_r (is5_delta n) (1#16) (is5_delta n));
      [exact Hdu | apply (is5_delta_ge0 n)]. }
  assert (Hc : Qle (12 * is5_delta (Datatypes.S n)) ((1#16) * is5_delta n))
    by (apply (Qle_trans _ (is5_delta n * is5_delta n)); assumption).
  apply (Qle_trans (is5_delta (Datatypes.S n))
    (((1#16) * is5_delta n) * Qinv (12#1)) ((1#192) * is5_delta n)).
  - apply (ir2_le_mul_inv (is5_delta (Datatypes.S n)) ((1#16) * is5_delta n) (12#1)).
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + rewrite (Qmult_comm (is5_delta (Datatypes.S n)) (12#1)). exact Hc.
  - assert (Hc2 : Qinv (12#1) == (1#12)%Q) by reflexivity.
    rewrite Hc2. apply qeq_le. ring.
Qed.

Lemma is5_sixteenth : forall n : nat, (1 <= n)%nat -> Qle (is5_delta n) (1#16).
Proof.
  induction n as [|n IH].
  - lia.
  - destruct n as [|n].
    + change (is5_delta 1) with (1 # 5184)%Q.
      unfold Qle. cbn [Qnum Qden]. lia.
    + intro Hle0. assert (Hn1 : (1 <= Datatypes.S n)%nat) by lia.
      pose proof (IH Hn1) as Hdu.
      apply (Qle_trans _ ((1#192) * is5_delta (Datatypes.S n))).
      * apply (is5_delta_step (Datatypes.S n)); [lia | exact Hdu].
      * apply (Qle_trans _ ((1#192) * (1#16))%Q).
        -- apply ir2_mult_le_compat_l; [exact Hdu | unfold Qle; cbn; lia].
        -- unfold Qle, Qmult. cbn [Qnum Qden]. lia.
Qed.

Lemma is5_e_step : forall n : nat, (1 <= n)%nat ->
  Qle (is5_e (Datatypes.S n)) ((1#2) * is5_e n).
Proof.
  intros n Hn1. unfold is5_e.
  apply (Qle_trans _ ((1#2) * ((1#192) * is5_delta n))%Q).
  - rewrite (Qmult_comm (1#2) (is5_delta (Datatypes.S n))).
    rewrite (Qmult_comm (1#2) ((1#192) * is5_delta n)).
    pose proof (is5_sixteenth n Hn1) as Hdu.
    apply Qmult_le_compat_r.
    + apply (is5_delta_step n); [exact Hn1 | exact Hdu].
    + unfold Qle. cbn [Qnum Qden]. lia.
  - destruct (is5_delta n) as [dn dd] eqn:Edn.
    pose proof (is5_delta_ge0 n) as Hge. rewrite Edn in Hge.
    unfold Qle in Hge. cbn [Qnum Qden] in Hge.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    unfold Qle, Qmult. cbn [Qnum Qden]. nia.
Qed.

Lemma is5_e_to_delta : forall n : nat,
  (is5_e n * ir2_qp (Datatypes.S n) == is5_delta n * ir2_qp n)%Q.
Proof.
  intro n. unfold is5_e. rewrite ir2_qp_def. ring.
Qed.

Lemma is5_decay : forall n : nat,
  Qle (is5_e (Datatypes.S n) * ir2_qp (Datatypes.S (Datatypes.S n))) 1%Q.
Proof.
  induction n as [|n IH].
  - change (is5_e 1) with (1 # 10368)%Q.
    change (ir2_qp 2) with (4 # 1)%Q.
    unfold Qle, Qmult. cbn [Qnum Qden]. lia.
  - apply (Qle_trans _ (((1#2) * is5_e (Datatypes.S n))
                          * ((2#1) * ir2_qp (Datatypes.S (Datatypes.S n))))%Q).
    + rewrite ir2_qp_def.
      apply Qmult_le_compat_r.
      * apply (is5_e_step (Datatypes.S n)). lia.
      * apply Qlt_le_weak.
        apply (Qmult_lt_0_compat (2#1) (ir2_qp (Datatypes.S (Datatypes.S n)))).
        -- unfold Qlt. cbn [Qnum Qden]. lia.
        -- apply ir2_qp_pos.
    + rewrite ir2_qp_def.
      assert (Hr : ((((1#2) * is5_e (Datatypes.S n))
                      * ((2#1) * ir2_qp (Datatypes.S (Datatypes.S n))))
                     == (is5_e (Datatypes.S n)
                          * ir2_qp (Datatypes.S (Datatypes.S n))))%Q) by ring.
      rewrite Hr. exact IH.
Qed.

Lemma is5_delta_pow_le : forall n : nat, (1 <= n)%nat ->
  Qle (is5_delta n * ir2_qp n) 1%Q.
Proof.
  intros n Hn. rewrite <- (is5_e_to_delta n).
  destruct n as [|n'].
  - lia.
  - apply (is5_decay n').
Qed.

(* ============================================================ *)
(* S5：逃逸间隙引理（√5 与任一有理数的 Q 层可判间隙）                    *)
(* ============================================================ *)

(* 下侧间隙：q²<5 时 (5−q²)·(2/9) ≤ x_N−q（x_N ≤ 9/4 ⟹ 1/(x_N+q) ≥ 2/9） *)
Lemma is5_gap_lower : forall u v : Q,
  Qle 0 v -> Qle v u -> Qle u (9#4) -> Qle 5 (u*u) -> Qlt (v*v) 5 ->
  Qle ((5 - v*v) * (2#9)) (u - v).
Proof.
  intros u v Hv0 Hvu Hub H5 Hsq.
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

(* 上侧小间隙：5<q²≤(9/4)² 且 d ≤ (4/13)(v²−5) ⟹ d/2 < v−u
   （严格性来源：13 < 20 = 4·5，即 1/(5b²) < (4/13)/b²） *)
Lemma is5_gap_upper_small : forall u v d : Q,
  Qlt 0 u -> Qlt 0 v -> Qlt u v -> Qle v (9#4) -> Qlt 5 (v*v) ->
  d == (u*u - 5) -> Qle 0 d -> Qle d ((4#13) * (v*v - 5)) ->
  Qlt (d * (1#2)) (v - u).
Proof.
  intros u v d Hu0 Hv0 Huv Hv94 Hsq Hd Hdu Hdle.
  assert (Hw0 : Qlt 0 (v*v - 5)) by (apply (lic_qlt_0_minus 5%Q (v*v)); exact Hsq).
  assert (Hpu : Qlt 0%Q (v + u)) by (apply ir2_qpos_add; assumption).
  assert (Hne : ~ ((v + u)%Q == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (v + u) Hpu); rewrite Hc; apply Qeq_refl).
  assert (Hbridge : ((v - u) == (v*v - u*u) * Qinv (v + u))%Q).
  { pose proof (bno_mul_div_self (v + u) Hne) as Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((v - u) * (v + u)) * Qinv (v + u)) == (v - u))%Q).
    { rewrite <- (Qmult_assoc (v - u) (v + u) (Qinv (v + u))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite (ir2_sq_diff v u) in Hpm. exact (Qeq_sym _ _ Hpm). }
  assert (Hsh : ((v*v - u*u) == ((v*v - 5) - d))%Q) by (rewrite Hd; ring).
  assert (Hvu2 : Qlt 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 5)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
    destruct v as [vn vd].
    unfold Qlt, Qle, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  assert (Hvup : Qlt (v + u) (9#2)).
  { apply (Qlt_le_trans (v + u) (v + v) (9#2)).
    - apply (lic_qlt_add_l v u v Huv).
    - apply (Qle_trans _ ((9#4) + (9#4))%Q).
      + apply (Qplus_le_compat v (9#4) v (9#4)); [exact Hv94 | exact Hv94].
      + apply qeq_le. reflexivity. }
  apply (Qle_lt_trans (d * (1#2)) ((v*v - u*u) * (2#9)) (v - u)).
  - apply (Qle_trans _ ((2#13) * (v*v - 5))%Q).
    + destruct (v*v - 5)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
      rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
      unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
      cbn [Qnum Qden Qplus] in *.
      assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
      assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
      lia.
    + assert (H913 : Qle ((9#13) * (v*v - 5)) (v*v - u*u)).
      { rewrite Hsh.
        destruct (v*v - 5)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
        rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
        destruct v as [vn vd].
        unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
        cbn [Qnum Qden Qplus] in *.
        assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
        assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
        nia. }
      assert (Hr29 : (((2#13) * (v*v - 5)) == ((2#9) * ((9#13) * (v*v - 5))))%Q)
        by ring.
      apply (Qle_trans _ ((2#9) * ((9#13) * (v*v - 5)))%Q).
      * rewrite Hr29. apply Qle_refl.
      * rewrite (Qmult_comm (2#9) ((9#13) * (v*v - 5))).
        apply Qmult_le_compat_r; [exact H913 | unfold Qle; cbn; lia].
  - rewrite Hbridge.
    rewrite (Qmult_comm (v*v - u*u) (2#9)).
    rewrite (Qmult_comm (v*v - u*u) (Qinv (v + u))).
    apply (Qmult_lt_compat_r (2#9) (Qinv (v + u)) (v*v - u*u)).
    + exact Hvu2.
    + apply (ir2_inv_lt (9#2) (v + u)).
      * unfold Qlt. cbn [Qnum Qden]. lia.
      * exact Hpu.
      * exact Hvup.
Qed.

(* 上侧大间隙：q > 9/4 且 (v+1)d ≤ v²−5 ⟹ d/2 < v−u（与常数无关） *)
Lemma is5_gap_upper_big : forall u v d : Q,
  Qlt 0 u -> Qlt u v -> (9#4) <= v -> Qlt 5 (v*v) ->
  d == (u*u - 5) -> Qle 0 d -> Qle ((v + 1) * d) (v*v - 5) ->
  Qlt (d * (1#2)) (v - u).
Proof.
  intros u v d Hu0 Huv Hv94 Hsq Hd Hdu Hd1.
  assert (Hw0 : Qlt 0 (v*v - 5)) by (apply (lic_qlt_0_minus 5%Q (v*v)); exact Hsq).
  assert (Hvp : Qlt 0 v).
  { apply (Qlt_le_trans 0%Q (9#4) v); [unfold Qlt; cbn; lia | exact Hv94]. }
  assert (Hpvu : Qlt 0%Q (v + u)) by (apply ir2_qpos_add; [exact Hvp | exact Hu0]).
  assert (Hne : ~ ((v + u)%Q == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (v + u) Hpvu); rewrite Hc; apply Qeq_refl).
  assert (Hbridge : ((v - u) == (v*v - u*u) * Qinv (v + u))%Q).
  { pose proof (bno_mul_div_self (v + u) Hne) as Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((v - u) * (v + u)) * Qinv (v + u)) == (v - u))%Q).
    { rewrite <- (Qmult_assoc (v - u) (v + u) (Qinv (v + u))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite (ir2_sq_diff v u) in Hpm. exact (Qeq_sym _ _ Hpm). }
  assert (Hsh : ((v*v - u*u) == ((v*v - 5) - d))%Q) by (rewrite Hd; ring).
  assert (Hvu2 : Qle 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 5)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    destruct v as [vn vd].
    rewrite ?Ew, ?Ed in Hw0, Hd1, Hdu.
    unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  assert (H2vp : Qlt 0%Q ((2#1) * v)).
  { apply (Qmult_lt_0_compat (2#1) v); [unfold Qlt; cbn; lia | exact Hvp]. }
  assert (Huv2 : Qle (v + u) ((2#1) * v)).
  { apply (Qle_trans (v + u) (v + v) ((2#1) * v)).
    - apply (Qplus_le_compat v v u v); [apply Qle_refl | apply Qlt_le_weak; exact Huv].
    - apply qeq_le. ring. }
  assert (Hdv : Qle (d * v) ((v*v - 5) - d)).
  { destruct (v*v - 5)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    destruct v as [vn vd].
    rewrite ?Ew, ?Ed in Hw0, Hd1, Hdu.
    unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  assert (Hkey : Qle (d * (1#2)) (((v*v - 5) - d) * Qinv ((2#1) * v))).
  { apply (ir2_le_mul_inv (d * (1#2)) ((v*v - 5) - d) ((2#1) * v)).
    - exact H2vp.
    - assert (Hring : (((d * (1#2)) * ((2#1) * v)) == (d * v))%Q) by ring.
      rewrite Hring. exact Hdv. }
  assert (Hvu2p : Qlt 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 5)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    destruct v as [vn vd].
    rewrite ?Ew, ?Ed in Hw0, Hd1, Hdu.
    unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  apply (Qle_lt_trans (d * (1#2)) (((v*v - 5) - d) * Qinv ((2#1) * v)) (v - u)).
  - exact Hkey.
  - apply (Qle_lt_trans (((v*v - 5) - d) * Qinv ((2#1) * v))
            ((v*v - u*u) * Qinv ((2#1) * v)) (v - u)).
    + assert (Hle2 : Qle (v*v - 5 - d) (v*v - u*u)).
      { rewrite Hd. apply qeq_le. ring. }
      apply Qmult_le_compat_r; [exact Hle2 | apply ir2_inv_pos; exact H2vp].
    + rewrite Hbridge.
      rewrite (Qmult_comm (v*v - u*u) (Qinv ((2#1) * v))).
      rewrite (Qmult_comm (v*v - u*u) (Qinv (v + u))).
      apply (Qmult_lt_compat_r (Qinv ((2#1) * v)) (Qinv (v + u)) (v*v - u*u)).
      * exact Hvu2p.
      * apply (ir2_inv_lt ((2#1) * v) (v + u)).
        -- exact H2vp.
        -- exact Hpvu.
        -- assert (Hr2 : (v + v == (2#1) * v)%Q) by ring.
           rewrite <- Hr2. apply (lic_qlt_add_l v u v Huv).
Qed.

(* ============================================================ *)
(* S6：母定理三前件实例（尾控/窗宽消失/逃逸窗）                          *)
(* ============================================================ *)

Definition is5_tail : lic_tail_bounded is5_x is5_e.
Proof.
  intros n k Hn1 Hnk.
  pose proof (is5_mono_le n k Hn1 Hnk) as Hmono.
  pose proof (is5_delta_ge0 n) as Hd0n.
  pose proof (is5_delta_pos n) as Hdpn.
  assert (Habs : Qabs ((is5_x k - is5_x n)%Q) == (is5_x n - is5_x k)%Q).
  { rewrite Qabs_Qminus. apply ir2_abs_sub. exact Hmono. }
  assert (Hsumpos : Qlt 0 (is5_x n + is5_x k)).
  { apply ir2_qpos_add.
    - apply (Qlt_le_trans 0%Q (9#5) (is5_x n)).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + apply (is5_x_lb n).
    - apply (Qlt_le_trans 0%Q (9#5) (is5_x k)).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + apply (is5_x_lb k). }
  assert (Hsumne : ~ ((is5_x n + is5_x k) == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (is5_x n + is5_x k) Hsumpos);
        rewrite Hc; apply Qeq_refl).
  assert (Hbridge : (((is5_x n - is5_x k)
                      == (is5_delta n - is5_delta k) * Qinv (is5_x n + is5_x k))%Q)).
  { pose proof (bno_mul_div_self (is5_x n + is5_x k) Hsumne) as Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((is5_x n - is5_x k) * (is5_x n + is5_x k))
                    * Qinv (is5_x n + is5_x k)) == (is5_x n - is5_x k))%Q).
    { rewrite <- (Qmult_assoc (is5_x n - is5_x k) (is5_x n + is5_x k)
                    (Qinv (is5_x n + is5_x k))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite ir2_sq_diff in Hpm.
    assert (Hsh : ((is5_x n * is5_x n - is5_x k * is5_x k)
                   == (is5_delta n - is5_delta k))%Q)
      by (unfold is5_delta; ring).
    rewrite Hsh in Hpm. exact (Qeq_sym _ _ Hpm). }
  apply Qlt_to_QltT. rewrite Habs. rewrite Hbridge.
  assert (Hsumb : Qle ((18#5)) (is5_x n + is5_x k)).
  { apply (Qle_trans _ ((9#5) + (9#5))%Q).
    - apply qeq_le. reflexivity.
    - apply (Qplus_le_compat (9#5) (is5_x n) (9#5) (is5_x k));
        [apply (is5_x_lb n) | apply (is5_x_lb k)]. }
  assert (Hinvp : Qle 0%Q (Qinv (is5_x n + is5_x k)))
    by (apply ir2_inv_pos; exact Hsumpos).
  assert (Hstep1 : Qle ((is5_delta n - is5_delta k) * Qinv (is5_x n + is5_x k))
                     (is5_delta n * Qinv (is5_x n + is5_x k))).
  { apply Qmult_le_compat_r.
    - unfold Qminus, Qle, Qopp in *.
      destruct (is5_delta n) as [dn dd] eqn:Edn.
      destruct (is5_delta k) as [ek ed] eqn:Edk.
      pose proof (is5_delta_ge0 k) as H0k.
      rewrite Edk in H0k. unfold Qle in H0k. cbn [Qnum Qden] in H0k.
      cbn [Qnum Qden Qplus Qopp Qmult].
      assert (Hdd0 : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
      assert (Hed0 : (0 < Z.pos ed)%Z) by apply Pos2Z.is_pos.
      nia.
    - exact Hinvp. }
  assert (Hstep2 : Qle (is5_delta n * Qinv (is5_x n + is5_x k))
                     (is5_delta n * Qinv ((18#5)))).
  { rewrite (Qmult_comm (is5_delta n) (Qinv (is5_x n + is5_x k))).
    rewrite (Qmult_comm (is5_delta n) (Qinv ((18#5)))).
    apply Qmult_le_compat_r.
    - apply (ir2_inv_le (18#5) (is5_x n + is5_x k));
        [unfold Qlt; cbn [Qnum Qden]; lia | exact Hsumb].
    - exact Hd0n. }
  assert (Hstep3 : Qlt (is5_delta n * Qinv ((18#5))) ((1#2) * is5_delta n)).
  { destruct (is5_delta n) as [dn dd] eqn:Edn.
    pose proof (is5_delta_pos n) as Hdp.
    rewrite Edn in Hdp. unfold Qlt in Hdp. cbn [Qnum Qden] in Hdp.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    unfold Qlt, Qmult, Qinv. cbn [Qnum Qden Qinv]. nia. }
  apply (Qle_lt_trans ((is5_delta n - is5_delta k) * Qinv (is5_x n + is5_x k))
          (is5_delta n * Qinv (is5_x n + is5_x k)) ((1#2) * is5_delta n)).
  - exact Hstep1.
  - apply (Qle_lt_trans (is5_delta n * Qinv (is5_x n + is5_x k))
            (is5_delta n * Qinv ((18#5))) ((1#2) * is5_delta n)).
    + exact Hstep2.
    + exact Hstep3.
Defined.

Definition is5_vanish : lic_vanish is5_e.
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
    apply (Qle_lt_trans (is5_e (Datatypes.S n'))
            (Qinv (ir2_qp (Datatypes.S (Datatypes.S n')))) ((pn # pd)%Q)).
    + apply (ir2_le_inv (ir2_qp (Datatypes.S (Datatypes.S n')))
               (is5_e (Datatypes.S n'))).
      * apply ir2_qp_pos.
      * rewrite (Qmult_comm (ir2_qp (Datatypes.S (Datatypes.S n')))
                            (is5_e (Datatypes.S n'))).
        apply (is5_decay n').
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

Definition is5_escape : lic_escape_window is5_x is5_e.
Proof.
  intro q.
  destruct (Qlt_bool 0%Q q) eqn:Hpos.
  - pose proof (lic_qlt_bool_true 0%Q q Hpos) as Hq0.
    destruct (Qlt_bool (q * q) 5%Q) eqn:H5b.
    + (* q² < 5：N := den(q) + 8，x_N 自上方追上 q *)
      pose proof (lic_qlt_bool_true (q * q) 5%Q H5b) as H5.
      destruct q as [a b].
      assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
      assert (Hkb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b) by (apply Z2Nat.id; lia).
      assert (Hkb1 : (1 <= Z.to_nat (Z.pos b))%nat).
      { destruct (Z.to_nat (Z.pos b)) as [|k'] eqn:Ek; [ | lia].
        exfalso. pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz.
        rewrite Ek in Hz. cbn in Hz. lia. }
      exists (Z.to_nat (Z.pos b) + 8)%nat. split. lia.
      apply Qlt_to_QltT.
      assert (Hxsq : Qle 5%Q (is5_x (Z.to_nat (Z.pos b) + 8)
                                * is5_x (Z.to_nat (Z.pos b) + 8)))
        by apply is5_sq_ge5.
      assert (Hqx : Qlt ((a # b) * (a # b))
                    (is5_x (Z.to_nat (Z.pos b) + 8)
                     * is5_x (Z.to_nat (Z.pos b) + 8)))
        by (apply (Qlt_le_trans ((a # b) * (a # b)) 5%Q
                    (is5_x (Z.to_nat (Z.pos b) + 8)
                     * is5_x (Z.to_nat (Z.pos b) + 8))); assumption).
      assert (Hqle : Qlt (a # b) (is5_x (Z.to_nat (Z.pos b) + 8)))
        by (apply (ir2_lt_of_sq (is5_x (Z.to_nat (Z.pos b) + 8)) (a # b));
            [apply Qlt_le_weak; apply (is5_x_pos (Z.to_nat (Z.pos b) + 8))
            | apply Qlt_le_weak; exact Hq0 | exact Hqx]).
      assert (Habs : Qabs ((a # b) - is5_x (Z.to_nat (Z.pos b) + 8))%Q
                     == (is5_x (Z.to_nat (Z.pos b) + 8) - (a # b))%Q).
      { rewrite Qabs_Qminus. apply ir2_abs_sub. apply Qlt_le_weak. exact Hqle. }
      rewrite Habs.
      apply (Qlt_le_trans (is5_e (Z.to_nat (Z.pos b) + 8))
              (Qinv ((5 * (Z.pos b * Z.pos b)) # 1))
              (is5_x (Z.to_nat (Z.pos b) + 8) - (a # b))%Q).
      * apply (Qle_lt_trans (is5_e (Z.to_nat (Z.pos b) + 8))
                (Qinv (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8))))
                (Qinv ((5 * (Z.pos b * Z.pos b)) # 1))).
        -- apply (ir2_le_inv (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                   (is5_e (Z.to_nat (Z.pos b) + 8))).
           ++ apply ir2_qp_pos.
           ++ rewrite (Qmult_comm (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                       (is5_e (Z.to_nat (Z.pos b) + 8))).
              replace (Z.to_nat (Z.pos b) + 8)%nat
                with (Datatypes.S (Z.to_nat (Z.pos b) + 7))%nat by lia.
              apply (is5_decay (Z.to_nat (Z.pos b) + 7)).
        -- apply (ir2_inv_lt (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                   ((5 * (Z.pos b * Z.pos b)) # 1)).
           ++ apply ir2_qp_pos.
           ++ unfold Qlt. cbn [Qnum Qden]. lia.
           ++ rewrite ir2_qp_pow.
              replace (Datatypes.S (Z.to_nat (Z.pos b) + 8))%nat
                with (Z.to_nat (Z.pos b) + 8 + 1)%nat by lia.
              assert (Hb3 : (2 ^ (Z.to_nat (Z.pos b) + 8 + 1)
                             = 2 * 2 ^ (Z.to_nat (Z.pos b) + 8))%nat)
                by (rewrite Nat.pow_add_r, Nat.pow_1_r, Nat.mul_comm; reflexivity).
              assert (Hzp : (1 <= Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 8)))%Z).
              { pose proof (ir2_pow_ge (Z.to_nat (Z.pos b) + 8)) as Hp.
                apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
                rewrite Nat2Z.inj_succ in Hp. lia. }
              assert (Hz : (5 * (Z.pos b * Z.pos b)
                            <= Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 8)))%Z).
              { pose proof (is5_pow5sq (Z.to_nat (Z.pos b))) as Hp.
                apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
                rewrite !Nat2Z.inj_mul in Hp.
                rewrite Hkb in Hp. cbn [Z.of_nat] in Hp. lia. }
              pose proof (f_equal Z.of_nat Hb3) as Hb4.
              rewrite Nat2Z.inj_mul in Hb4. cbn [Z.of_nat] in Hb4.
              unfold Qlt. cbn [Qnum Qden]. lia.
      * apply (Qle_trans _ ((5 - (a # b) * (a # b))
                             * (2#9))%Q).
        -- apply (ir2_ge_inv ((5 * (Z.pos b * Z.pos b)) # 1)
                   (((5 - (a # b) * (a # b)) * (2#9))%Q)).
           ++ unfold Qlt. cbn [Qnum Qden]. lia.
           ++ unfold Qle, Qmult, Qminus.
              pose proof H5 as H5'. unfold Qlt, Qmult, Qminus in H5'.
              cbn [Qnum Qden Qplus Qopp] in H5' |- *.
              assert (Hb1 : (1 <= Z.pos b)%Z) by lia.
              nia.
        -- apply (is5_gap_lower (is5_x (Z.to_nat (Z.pos b) + 8)) (a # b)).
           ++ apply Qlt_le_weak. exact Hq0.
           ++ apply Qlt_le_weak. exact Hqle.
           ++ apply is5_x_ub.
           ++ exact Hxsq.
           ++ exact H5.
    + (* 5 ≤ q² *)
      pose proof (lic_qlt_bool_false_le (q * q) 5%Q H5b) as Hge5.
      destruct (Qeq_dec (q * q) 5%Q) as [Heq5 | Hne5].
      * exfalso. exact (is5_no_sqrt5 q Heq5).
      * destruct (Qlt_bool 5%Q (q * q)) eqn:H5lt.
        -- pose proof (lic_qlt_bool_true 5%Q (q * q) H5lt) as Hlt5.
           destruct (Qlt_bool (9#4) q) eqn:H94b.
           ++ (* 9/4 < q：N := num(q) + den(q) + 1，x_N 自下方逼近 *)
              pose proof (lic_qlt_bool_true (9#4) q H94b) as H94.
              destruct q as [a b].
              assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
              assert (H94z : (9 * Z.pos b < 4 * a)%Z).
              { pose proof H94 as H94'. unfold Qlt in H94'.
                cbn [Qnum Qden] in H94'. lia. }
              assert (Hz5 : (5 * (Z.pos b * Z.pos b) + 1 <= a * a)%Z).
              { pose proof Hlt5 as H5'. unfold Qlt, Qmult in H5'.
                cbn [Qnum Qden] in H5'. lia. }
              assert (Hkba : Z.of_nat (Z.to_nat a) = a)
                by (apply Z2Nat.id; lia).
              assert (Hkbb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b)
                by (apply Z2Nat.id; lia).
              assert (HpowN : ((a + Z.pos b) * Z.pos b
                               <= Z.of_nat (2 ^ (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1)))%Z).
              { replace (Z.to_nat a + Z.to_nat (Z.pos b) + 1)%nat
                  with (Datatypes.S (Z.to_nat a + Z.to_nat (Z.pos b))) by lia.
                rewrite Nat.pow_succ_r'. rewrite Nat.pow_add_r.
                pose proof (ir2_pow_ge (Z.to_nat a)) as H1.
                pose proof (ir2_pow_ge (Z.to_nat (Z.pos b))) as H2.
                apply (proj1 (Nat2Z.inj_le _ _)) in H1.
                apply (proj1 (Nat2Z.inj_le _ _)) in H2.
                rewrite Nat2Z.inj_succ in H1, H2.
                pose proof (Z2Nat.id a (ltac:(lia))) as Hz3w.
                pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz4w.
                rewrite Hz3w in H1. rewrite Hz4w in H2.
                rewrite !Nat2Z.inj_mul. cbn [Z.of_nat].
                nia. }
              exists (Z.to_nat a + Z.to_nat (Z.pos b) + 1)%nat. split. lia.
              apply Qlt_to_QltT.
              assert (Hdpow : Qle (is5_delta (Z.to_nat a
                                              + Z.to_nat (Z.pos b) + 1)
                                    * ir2_qp (Z.to_nat a
                                              + Z.to_nat (Z.pos b) + 1)) 1%Q).
              { apply (is5_delta_pow_le). lia. }
              assert (Hbnd : Qle (((a # b) + 1)
                                  * is5_delta (Z.to_nat a
                                               + Z.to_nat (Z.pos b) + 1))
                           (((a # b) * (a # b)) - 5%Q)%Q).
              { apply (Qle_trans _ (((a # b) + 1)
                                    * Qinv (ir2_qp (Z.to_nat a
                                             + Z.to_nat (Z.pos b) + 1)))%Q).
                - apply ir2_mult_le_compat_l.
                  + apply (ir2_le_inv (ir2_qp (Z.to_nat a
                                          + Z.to_nat (Z.pos b) + 1))
                              (is5_delta (Z.to_nat a
                                           + Z.to_nat (Z.pos b) + 1))).
                    * apply ir2_qp_pos.
                    * rewrite (Qmult_comm (ir2_qp (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1))
                                (is5_delta (Z.to_nat a
                                             + Z.to_nat (Z.pos b) + 1))).
                      exact Hdpow.
                  + apply (Qle_trans 0%Q (a # b) ((a # b) + 1)%Q).
                    * apply Qlt_le_weak. exact Hq0.
                    * apply Qlt_le_weak.
                      apply (lic_qlt_lt_add_r (a # b) 1%Q).
                      unfold Qlt. cbn [Qnum Qden]. lia.
                - rewrite (ir2_qp_pow (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
                  assert (Hzp1 : (1 <= Z.of_nat (2 ^ (Z.to_nat a
                                                   + Z.to_nat (Z.pos b) + 1)))%Z).
                  { pose proof (ir2_pow_ge (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1)) as Hp.
                    apply (proj1 (Nat2Z.inj_le _ _)) in Hp. lia. }
                  destruct (Z.of_nat (2 ^ (Z.to_nat a
                                           + Z.to_nat (Z.pos b) + 1)))
                    as [|pp|pp] eqn:Ez; try lia.
                  rewrite ?Ez in HpowN.
                  unfold Qle, Qmult, Qminus, Qinv.
                  cbn [Qnum Qden Qplus Qopp] in HpowN |- *.
                  assert (Hbp : (1 <= Z.pos b)%Z) by lia.
                  nia. }
              assert (Hdl : Qlt (is5_delta (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1))
                            (((a # b) * (a # b)) - 5%Q)%Q).
              { destruct (is5_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                  as [dn dd] eqn:Ed.
                rewrite (ir2_qp_pow (Z.to_nat a
                          + Z.to_nat (Z.pos b) + 1)) in Hdpow.
                rewrite ?Ed in Hdpow, Hbnd.
                pose proof (is5_delta_pos (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1)) as Hdp5.
                rewrite ?Ed in Hdp5.
                unfold Qle, Qlt in *.
                cbn [Qnum Qden Qmult Qminus Qopp Qplus] in *.
                assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
                nia. }
              assert (Hxq : Qlt (is5_x (Z.to_nat a
                                       + Z.to_nat (Z.pos b) + 1))
                                (a # b)).
              { apply (ir2_lt_of_sq (a # b)
                        (is5_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))).
                - apply Qlt_le_weak. exact Hq0.
                - apply Qlt_le_weak.
                  apply (is5_x_pos (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
                - pose proof Hdl as Hdl'.
                  unfold is5_delta in Hdl'.
                  pose proof (lic_qlt_minus_add_r ((a # b) * (a # b)) 5%Q)
                    as Hr1.
                  pose proof (lic_qlt_minus_add_r
                                (is5_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 * is5_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                                5%Q) as Hr2.
                  apply (Qle_lt_trans
                          (is5_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                           * is5_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                          ((is5_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                            * is5_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                            - 5%Q) + 5%Q)%Q
                          ((a # b) * (a # b))).
                  + apply (qeq_le _ _ (Qeq_sym _ _ Hr2)).
                  + apply (lic_qlt_comp_r
                              (((a # b) * (a # b) - 5%Q) + 5%Q)%Q
                              ((a # b) * (a # b))
                              ((is5_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                * is5_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                - 5%Q) + 5%Q)%Q).
                    * exact Hr1.
                    * apply (lic_qlt_add_r
                                (is5_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 * is5_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 - 5%Q)%Q
                                ((a # b) * (a # b) - 5%Q)%Q
                                5%Q Hdl'). }
              assert (HeqN : (is5_e (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                              == is5_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                  * (1#2))%Q).
              { unfold is5_e. ring. }
              rewrite HeqN.
              rewrite (ir2_abs_sub (a # b)
                        (is5_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)))
                by (apply Qlt_le_weak; exact Hxq).
              apply (is5_gap_upper_big
                      (is5_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                      (a # b)
                      (is5_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1))).
              ** apply (is5_x_pos (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
              ** exact Hxq.
              ** apply Qlt_le_weak. exact H94.
              ** exact Hlt5.
              ** reflexivity.
              ** apply (is5_delta_ge0 (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
              ** exact Hbnd.
           ++ (* 5 < q² 且 q ≤ 9/4：N := den(q) + 8，窗 4/13（x_N 自下方追上 q） *)
              pose proof (lic_qlt_bool_false_le (9#4) q H94b) as H94.
              destruct q as [a b].
              assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
              assert (Hkb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b) by (apply Z2Nat.id; lia).
              assert (Hkb1 : (1 <= Z.to_nat (Z.pos b))%nat).
              { destruct (Z.to_nat (Z.pos b)) as [|k'] eqn:Ek; [ | lia].
                exfalso. pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz.
                rewrite Ek in Hz. cbn in Hz. lia. }
              assert (Hq5z : (5 * (Z.pos b * Z.pos b) + 1 <= a * a)%Z).
              { pose proof Hlt5 as H5'. unfold Qlt, Qmult in H5'.
                cbn [Qnum Qden] in H5'. lia. }
              exists (Z.to_nat (Z.pos b) + 8)%nat. split. lia.
              apply Qlt_to_QltT.
              assert (Hpow5 : (5 * (Z.pos b * Z.pos b)
                               <= Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 8)))%Z).
              { pose proof (is5_pow5sq (Z.to_nat (Z.pos b))) as Hp.
                apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
                rewrite !Nat2Z.inj_mul in Hp. rewrite Hkb in Hp.
                cbn [Z.of_nat] in Hp. lia. }
              assert (Hdpow : Qle (is5_delta (Z.to_nat (Z.pos b) + 8)
                                    * ir2_qp (Z.to_nat (Z.pos b) + 8)) 1%Q)
                by (apply is5_delta_pow_le; lia).
              rewrite (ir2_qp_pow (Z.to_nat (Z.pos b) + 8)) in Hdpow.
              assert (H413 : Qlt (is5_delta (Z.to_nat (Z.pos b) + 8))
                              (((4#13) * (((a # b) * (a # b)) - 5%Q))%Q)).
              { destruct (is5_delta (Z.to_nat (Z.pos b) + 8)) as [dn dd] eqn:Ed.
                rewrite ?Ed in Hdpow.
                pose proof (is5_delta_pos (Z.to_nat (Z.pos b) + 8)) as Hdp.
                rewrite Ed in Hdp. unfold Qlt in Hdp. cbn [Qnum Qden] in Hdp.
                unfold Qle, Qmult in Hdpow. cbn [Qnum Qden] in Hdpow.
                unfold Qlt, Qmult, Qminus. cbn [Qnum Qden Qplus Qopp] in Hdp, Hdpow |- *.
                assert (Hdd0 : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
                assert (Hbp : (1 <= Z.pos b)%Z) by lia.
                nia. }
              assert (Hdl : Qlt (is5_delta (Z.to_nat (Z.pos b) + 8))
                              ((((a # b) * (a # b)) - 5%Q)%Q)).
              { apply (Qlt_le_trans (is5_delta (Z.to_nat (Z.pos b) + 8))
                        (((4#13) * (((a # b) * (a # b)) - 5%Q))%Q)
                        ((((a # b) * (a # b)) - 5%Q)%Q)).
                - exact H413.
                - apply (Qle_trans _ (1%Q * (((a # b) * (a # b)) - 5%Q))%Q).
                  + apply Qmult_le_compat_r.
                    * unfold Qle. cbn [Qnum Qden]. lia.
                    * apply Qlt_le_weak.
                      apply (lic_qlt_0_minus 5%Q ((a # b) * (a # b)) Hlt5).
                  + apply qeq_le. apply Qmult_1_l. }
              assert (Hqx : Qlt (is5_x (Z.to_nat (Z.pos b) + 8)
                                  * is5_x (Z.to_nat (Z.pos b) + 8))
                            ((a # b) * (a # b))).
              { assert (Hr : (((is5_x (Z.to_nat (Z.pos b) + 8)
                                * is5_x (Z.to_nat (Z.pos b) + 8) - 5%Q) + 5%Q)
                              == (is5_x (Z.to_nat (Z.pos b) + 8)
                                   * is5_x (Z.to_nat (Z.pos b) + 8)))%Q)
                  by apply lic_qlt_minus_add_r.
                rewrite <- Hr.
                apply (Qlt_le_trans _ ((((a # b) * (a # b)) - 5%Q) + 5%Q)%Q).
                - apply (lic_qlt_add_r _ _ 5%Q Hdl).
                - apply qeq_le. apply lic_qlt_minus_add_r. }
              assert (Hqle : Qlt (is5_x (Z.to_nat (Z.pos b) + 8)) (a # b))
                by (apply (ir2_lt_of_sq (a # b) (is5_x (Z.to_nat (Z.pos b) + 8)));
                    [apply Qlt_le_weak; exact Hq0
                    | apply Qlt_le_weak;
                       apply (is5_x_pos (Z.to_nat (Z.pos b) + 8))
                    | exact Hqx]).
              rewrite (ir2_abs_sub (a # b) (is5_x (Z.to_nat (Z.pos b) + 8)))
                by (apply Qlt_le_weak; exact Hqle).
              assert (Heq8 : (is5_e (Z.to_nat (Z.pos b) + 8)
                              == is5_delta (Z.to_nat (Z.pos b) + 8)
                                  * (1#2))%Q).
              { unfold is5_e. ring. }
              rewrite Heq8.
              apply (is5_gap_upper_small
                      (is5_x (Z.to_nat (Z.pos b) + 8)) (a # b)
                      (is5_delta (Z.to_nat (Z.pos b) + 8))).
              ** apply (is5_x_pos (Z.to_nat (Z.pos b) + 8)).
              ** exact Hq0.
              ** exact Hqle.
              ** exact H94.
              ** exact Hlt5.
              ** reflexivity.
              ** apply (is5_delta_ge0 (Z.to_nat (Z.pos b) + 8)).
              ** apply Qlt_le_weak. exact H413.
        -- (* ¬(5 < q²) 且 5 ≤ q² ⟹ q² == 5 ⟹ 与 is5_no_sqrt5 矛盾 *)
           exfalso. apply Hne5.
           pose proof (lic_qlt_bool_false_le 5%Q (q * q) H5lt) as Hle5'.
           apply (Qle_antisym (q * q) 5%Q); [exact Hle5' | exact Hge5].
  - (* q ≤ 0 *)
    pose proof (lic_qlt_bool_false_le 0%Q q Hpos) as Hq0.
    destruct q as [qn qd].
    assert (Hqd : (0 < Z.pos qd)%Z) by apply Pos2Z.is_pos.
    exists 1%nat. split. lia.
    apply Qlt_to_QltT.
    rewrite (Qabs_Qminus (qn # qd) (is5_x 1)).
    rewrite (ir2_abs_sub (is5_x 1) (qn # qd)).
    2: { apply (Qle_trans (qn # qd) 0%Q (is5_x 1)).
         - exact Hq0.
         - apply Qlt_le_weak. apply (is5_x_pos 1). }
    rewrite is5_x1.
    assert (Heq1 : is5_e 1 == (1#10368)%Q) by reflexivity.
    rewrite Heq1.
    unfold Qle in Hq0. cbn [Qnum Qden] in Hq0.
    unfold Qlt, Qminus. cbn [Qnum Qden Qopp Qplus]. lia.
Defined.

(* ============================================================ *)
(* S7：u5c 装配实例（与 u5c_inst_sqrt3 同构）       *)
(* ============================================================ *)

Theorem u5c_sqrt5_criterion_escape_pt : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) is5_x
                            (lic_seq_cauchy is5_x is5_e is5_tail is5_vanish))
       (real_const q)))).
Proof.
  intro q.
  destruct (is5_escape q) as [n0 [Hn01 Hesc]].
  exact (u5c_escape_to_dist is5_x is5_e is5_tail is5_vanish q n0 Hn01 Hesc).
Qed.

