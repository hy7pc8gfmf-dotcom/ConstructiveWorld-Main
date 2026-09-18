(* ============================================================ *)
(* UpReqSqrt3Irrational.v                                        *)
(*                                                               *)
(* 目的：母定理 lic_irrational_criterion 的第三实例装配：             *)
(*       is3_sqrt3_irrational_criterion —— √3 的构造性无理性          *)
(*       （Q 层 Newton 迭代 x_{n+1} = (x_n + 3/x_n)/2，x_0 = 2，       *)
(*         x_1 = 7/4；误差窗 d_n = (x_n²−3)/2，显式指数衰减：          *)
(*         11·d_{n+1} ≤ d_n²（因 4x_n² ≥ 100/9 > 11）、d_n ≤ 1/16     *)
(*         ⟹ d_{n+1} ≤ d_n/176；逃逸窗由 q² 对 3 的可判定比较 +        *)
(*         1/den(q)² 型间隙供给：q²<3 走 is3_gap_lower（因子 2/7），    *)
(*         3<q²≤(7/4)² 走 is3_gap_upper_small（窗 4/11，严格性来源      *)
(*         11 < 12=4·3），q>(7/4)² 走 is3_gap_upper_big；vanish 复用    *)
(*         lic_vanish 的 N=den(eps)+1 配方与 ir2_qp=2^n 列）。         *)
(* 路线：ir2 √2 成活范式同构改参（2→3、3/2→7/4、下界 7/5→5/3）；        *)
(*       主定理真走 exact 装配（lic_irrational_criterion               *)
(*       is3_x is3_e is3_tail is3_escape is3_vanish q），零旁路。      *)
(* 命名：is3_ 前缀（开工全树 grep 零撞名）。                            *)
(* 公理面：本件纯构造性（零经典逻辑、零排中、零认授（未证断言））；         *)
(*       语句面全 Set 层（sigT/And/real_lt/QltT 形，无 Prop 泄露位）；  *)
(*       证内 Prop（Qlt/Qle）仅作 Q 层推理脚手架，不进结论面；           *)
(*       判定一律 Qlt_bool 路线（Qle_lt_or_eq 类 Prop 消去零出现）。    *)
(* 依赖：UpReqIrrationalCriterion（母定理件，只读）；                   *)
(*       UpReqIrrationalInstances（√2 成活机械，Require 消费其导出面：   *)
(*       ir2_qp/qp_pos/qp_pow/pow_ge/pow3sq/step_le 及通用 Q 层小件，    *)
(*       只读禁改）；Stdlib QArith、ZArith、Arith、Lia、Lra、Qfield。    *)
(* 泛化注记（√n 族雏形，仅注记不落码）：对任意非平方 n，Newton 列          *)
(*       x_{k+1}=(x_k+n/x_k)/2 的误差窗恒满足 d_{k+1}·(4x_k²)=d_k²，     *)
(*       衰减常数由 x_k 下界 L（L²<n）的 4L² 拆出；Z 层递降需 k|z²⟹k|z  *)
(*       的素除子引理（本件 3 的情形以 mod-3 三支判定给出，Set 层合规）。  *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqIrrationalInstances.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Lra Qfield.

(* ============================================================ *)
(* S1：Z 层——3 无有理平方根（无穷递降，mod-3 三支判定）                *)
(* ============================================================ *)

Lemma is3_mod3_sq : forall z : Z, ((z * z) mod 3 = 0)%Z -> (z mod 3 = 0)%Z.
Proof.
  intros z H.
  assert (Hr : (z mod 3 = 0)%Z \/ (z mod 3 = 1)%Z \/ (z mod 3 = 2)%Z).
  { pose proof (Z.mod_pos_bound z 3 (ltac:(lia))) as Hb. lia. }
  destruct Hr as [Hr | [Hr | Hr]]; [exact Hr | | ].
  - (* z = 3k+1：z² = 3·(3k²+2k)+1，mod 3 = 1 ≠ 0 *)
    exfalso.
    pose proof (Z.div_mod z 3 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 3)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 3 * (3 * k * k + 2 * k) + 1)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 3 = 1)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 3%Z ((3 * k * k + 2 * k)%Z) 1%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
  - (* z = 3k+2：z² = 3·(3k²+4k+1)+1，mod 3 = 1 ≠ 0 *)
    exfalso.
    pose proof (Z.div_mod z 3 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 3)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 3 * (3 * k * k + 4 * k + 1) + 1)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 3 = 1)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 3%Z ((3 * k * k + 4 * k + 1)%Z) 1%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
Qed.

Lemma is3_no_sqrtZ : forall a b : Z, (0 < b)%Z -> (a * a = 3 * (b * b))%Z -> False.
Proof.
  assert (Hgen : forall n : nat, forall a b : Z, (0 < b)%Z ->
    (a * a = 3 * (b * b))%Z -> (Z.to_nat b <= n)%nat -> False).
  { induction n as [|n IH]; intros a b Hb Heq Hn.
    - assert (Hb0 : (b = 0)%Z).
      { pose proof (Z2Nat.id b (ltac:(lia))) as Hzz.
        apply Nat.le_0_r in Hn. rewrite Hn in Hzz. cbn in Hzz.
        symmetry. exact Hzz. }
      lia.
    - (* a 被 3 整除、b 被 3 整除、b 严格降 *)
      assert (Ham : ((a * a) mod 3 = 0)%Z).
      { rewrite Heq.
        symmetry. apply (Zmod_unique ((3 * (b * b))%Z) 3%Z ((b * b)%Z) 0%Z); lia. }
      assert (Hae : (a mod 3 = 0)%Z) by (apply is3_mod3_sq; exact Ham).
      pose proof (Z.div_mod a 3 (ltac:(lia))) as Hza. rewrite Hae in Hza.
      remember (a / 3)%Z as a1 eqn:Ea1.
      assert (Ha1 : (a = 3 * a1)%Z) by lia.
      clear Hza Ea1 Hae Ham.
      assert (Hbb : (b * b = 3 * (a1 * a1))%Z).
      { rewrite Ha1 in Heq.
        replace ((3 * a1)%Z * (3 * a1)%Z)%Z with (9 * (a1 * a1)%Z)%Z in Heq by ring.
        replace (9 * (a1 * a1)%Z)%Z with (3 * (3 * (a1 * a1)%Z)%Z)%Z in Heq by ring.
        lia. }
      assert (Hbm : ((b * b) mod 3 = 0)%Z).
      { rewrite Hbb.
        symmetry. apply (Zmod_unique ((3 * (a1 * a1))%Z) 3%Z ((a1 * a1)%Z) 0%Z); lia. }
      assert (Hbe : (b mod 3 = 0)%Z) by (apply is3_mod3_sq; exact Hbm).
      pose proof (Z.div_mod b 3 (ltac:(lia))) as Hzb. rewrite Hbe in Hzb.
      remember (b / 3)%Z as b1 eqn:Eb1.
      assert (Hb1 : (b = 3 * b1)%Z) by lia.
      apply (IH a1 b1).
      + lia.
      + rewrite Hb1 in Hbb.
        replace ((3 * b1)%Z * (3 * b1)%Z)%Z with (9 * (b1 * b1)%Z)%Z in Hbb by ring.
        replace (9 * (b1 * b1)%Z)%Z with (3 * (3 * (b1 * b1)%Z)%Z)%Z in Hbb by ring.
        lia.
      + pose proof (Z2Nat.inj_mul b b1 (ltac:(lia)) (ltac:(lia))) as Hmm.
        pose proof (Z2Nat.id b (ltac:(lia))) as Hz1.
        pose proof (Z2Nat.id b1 (ltac:(lia))) as Hz2.
        lia. }
  intros a b Hb Heq.
  apply (Hgen (Z.to_nat b) a b Hb Heq (Nat.le_refl _)).
Qed.

Lemma is3_no_sqrt3 : forall q : Q, ~ (q * q == 3%Q).
Proof.
  intros q Hq. destruct q as [a b].
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (Heq : (a * a = 3 * (Z.pos b * Z.pos b))%Z).
  { unfold Qeq, Qmult in Hq. cbn in Hq.
    assert (Hb1 : (Z.pos (b * b) = Z.pos b * Z.pos b)%Z) by apply Pos2Z.inj_mul.
    lia. }
  exact (is3_no_sqrtZ a (Z.pos b) Hb Heq).
Qed.

(* ============================================================ *)
(* S2：Newton 序列（x_0=2，步 (x+3/x)/2）及其 Q 层基本量                *)
(* ============================================================ *)

Fixpoint is3_x (n : nat) : Q :=
  match n with
  | O => 2%Q
  | Datatypes.S m => (is3_x m + 3%Q / is3_x m) * (1 # 2)
  end.

Definition is3_delta (n : nat) : Q := is3_x n * is3_x n - 3%Q.
Definition is3_e (n : nat) : Q := (1 # 2) * is3_delta n.

Lemma is3_x1 : is3_x 1 == (7 # 4).
Proof. reflexivity. Qed.

(* 7j² ≤ 2^{j+8}（is3_pow3sq 同构：供 q²<3 支 7·den² ≤ qp(SN) 严格窗） *)
Lemma is3_step7 : forall j : nat, (3 <= j)%nat -> (14 * j + 7 <= 7 * j * j)%nat.
Proof.
  induction j as [|j IH]; intro Hj.
  - lia.
  - replace (7 * Datatypes.S j * Datatypes.S j)%nat
      with (7 * j * j + 14 * j + 7)%nat by ring.
    destruct (Nat.le_gt_cases 4 (Datatypes.S j)) as [Hj4 | Hjlt].
    + assert (Hj3 : (3 <= j)%nat) by lia.
      specialize (IH Hj3). lia.
    + destruct j as [|[|j']]; lia.
Qed.

Lemma is3_pow7sq : forall j : nat, (7 * j * j <= 2 ^ (j + 8))%nat.
Proof.
  assert (Haux : forall j : nat, (7 * j * j <= 2 ^ (8 + j))%nat).
  { induction j as [|j IH].
    - apply (proj1 (Nat.leb_le _ _)). vm_compute. reflexivity.
    - replace (8 + Datatypes.S j)%nat with (Datatypes.S (8 + j))%nat by lia.
      rewrite Nat.pow_succ_r'.
      destruct (Nat.le_gt_cases 3 j) as [Hj3 | Hjlt].
      + replace (7 * Datatypes.S j * Datatypes.S j)%nat
          with (7 * j * j + 14 * j + 7)%nat by ring.
        pose proof (is3_step7 j Hj3). lia.
      + destruct j as [|j'].
        * apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
        * destruct j' as [|j''].
          -- apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
          -- destruct j'' as [|j'''].
             ++ apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
             ++ lia. }
  intro j. rewrite (Nat.add_comm j 8). apply Haux.
Qed.

(* ============================================================ *)
(* S3：序列基本性质（正性/下界 5/3/单调/δ 代数）                        *)
(* ============================================================ *)

(* 3/x > 0（x > 0） *)
Lemma is3_div3_pos : forall v : Q, Qlt 0 v -> Qlt 0 (3%Q / v).
Proof.
  intros v Hv. unfold Qdiv.
  apply (Qmult_lt_0_compat (3#1) (Qinv v)).
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - apply (Qinv_lt_0_compat v Hv).
Qed.

Lemma is3_x_pos : forall n : nat, Qlt 0 (is3_x n).
Proof.
  induction n as [|n IH].
  - unfold Qlt. cbn [is3_x Qnum Qden]. lia.
  - cbn [is3_x]. apply (Qmult_lt_0_compat _ (1 # 2)).
    + apply ir2_qpos_add; [exact IH | apply is3_div3_pos; exact IH].
    + unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

Lemma is3_delta_succ_mul : forall n : nat,
  (is3_delta (Datatypes.S n) * (4 * (is3_x n * is3_x n)) == is3_delta n * is3_delta n)%Q.
Proof.
  intro n. unfold is3_delta. cbn [is3_x].
  field.
  intro Heq. apply (Qlt_not_eq 0%Q (is3_x n) (is3_x_pos n)).
  apply Qeq_sym. exact Heq.
Qed.

Lemma is3_delta_ge0 : forall n : nat, Qle 0 (is3_delta n).
Proof.
  induction n as [|n IH].
  - unfold is3_delta, Qle, Qmult, Qminus, Qplus, Qopp.
    cbn [is3_x Qnum Qden]. lia.
  - assert (HM : Qlt 0%Q (4 * (is3_x n * is3_x n))).
    { apply (Qmult_lt_0_compat (4#1) (is3_x n * is3_x n)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - apply (Qmult_lt_0_compat (is3_x n) (is3_x n)); exact (is3_x_pos n). }
    pose proof (is3_delta_succ_mul n) as Hmul.
    assert (Hsq : Qle 0 (is3_delta n * is3_delta n)).
    { destruct (is3_delta n) as [dn dd] eqn:Ed.
      pose proof IH as H0.
      rewrite ?Ed in H0. unfold Qle in H0. cbn [Qnum Qden] in H0.
      unfold Qle, Qmult. rewrite ?Ed. cbn [Qnum Qden]. nia. }
    apply (ir2_ge0_of_mul _ _ HM).
    rewrite Hmul. exact Hsq.
Qed.

Lemma is3_delta_pos : forall n : nat, Qlt 0 (is3_delta n).
Proof.
  intro n. pose proof (is3_delta_ge0 n) as Hge.
  destruct (Qeq_dec (is3_delta n) 0%Q) as [Hz | Hne].
  - exfalso. apply (is3_no_sqrt3 (is3_x n)).
    unfold is3_delta in Hz.
    rewrite <- (lic_qlt_minus_add_r (is3_x n * is3_x n) 3%Q).
    rewrite Hz. reflexivity.
  - destruct (Qlt_le_dec 0%Q (is3_delta n)) as [Hlt | Hle].
    + exact Hlt.
    + exfalso. apply Hne. apply (Qle_antisym (is3_delta n) 0%Q Hle Hge).
Qed.

Lemma is3_sq_ge3 : forall n : nat, Qle 3%Q (is3_x n * is3_x n).
Proof.
  intro n. pose proof (is3_delta_ge0 n) as H.
  assert (Hr : ((is3_x n * is3_x n - 3) + 3 == is3_x n * is3_x n)%Q)
    by apply lic_qlt_minus_add_r.
  rewrite <- Hr.
  apply (Qle_trans 3%Q (0%Q + 3%Q)%Q ((is3_x n * is3_x n - 3)%Q + 3%Q)%Q).
  - rewrite Qplus_0_l. apply Qle_refl.
  - apply Qplus_le_compat; [exact H | apply Qle_refl].
Qed.

Lemma is3_x_lb : forall n : nat, (5 # 3) <= is3_x n.
Proof.
  intro n. pose proof (is3_x_pos n) as Hp.
  destruct (Qlt_le_dec (is3_x n) (5#3)) as [Hlt | Hle].
  - exfalso.
    assert (H1 : Qlt ((is3_x n) * (is3_x n)) ((5#3) * (is3_x n))).
    { apply (Qmult_lt_compat_r (is3_x n) (5#3) (is3_x n)); [exact Hp | exact Hlt]. }
    assert (H2 : Qlt ((5#3) * (is3_x n)) ((5#3) * (5#3))).
    { rewrite (Qmult_comm (5#3) (is3_x n)).
      apply (Qmult_lt_compat_r (is3_x n) (5#3) (5#3)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - exact Hlt. }
    assert (H3 : Qlt (is3_x n * is3_x n) 3%Q).
    { apply (Qlt_trans _ ((5#3) * (5#3))).
      - apply (Qlt_trans _ ((5#3) * (is3_x n))); [exact H1 | exact H2].
      - unfold Qlt, Qmult. cbn [Qnum Qden]. lia. }
    apply (Qlt_not_le (is3_x n * is3_x n) 3%Q).
    + exact H3.
    + apply is3_sq_ge3.
  - exact Hle.
Qed.

Lemma is3_mono : forall n : nat, is3_x (Datatypes.S n) <= is3_x n.
Proof.
  intro n. cbn [is3_x].
  pose proof (is3_sq_ge3 n) as H3.
  pose proof (is3_x_pos n) as Hxp.
  destruct (is3_x n) as [a b] eqn:Ex.
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (H3c : (3 * Z.pos b * Z.pos b <= a * a)%Z).
  { pose proof H3 as H3'. rewrite ?Ex in H3'.
    unfold Qle, Qmult in H3'. cbn [Qnum Qden] in H3'. nia. }
  assert (Hne : ~ ((a # b) == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0%Q (a # b) Hxp).
    apply Qeq_sym. exact Hc. }
  assert (Hbb : ((a # b) * Qinv (a # b))%Q == 1%Q).
  { pose proof (bno_mul_div_self (a # b) Hne) as Hbb0.
    unfold Qdiv in Hbb0. rewrite Qmult_1_l in Hbb0. exact Hbb0. }
  assert (Hivp : Qle 0%Q (Qinv (a # b)))
    by (apply ir2_inv_pos; exact Hxp).
  assert (Hinv : Qle (3%Q / (a # b)) (a # b)).
  { apply (Qle_trans _ (((a # b) * (a # b)) * Qinv (a # b))%Q).
    - apply Qmult_le_compat_r; [exact H3 | exact Hivp].
    - apply qeq_le.
      rewrite <- (Qmult_assoc (a # b) (a # b) (Qinv (a # b))).
      rewrite Hbb. apply Qmult_1_r. }
  apply (Qle_trans _ (((a # b) + (a # b)) * (1 # 2))%Q).
  - apply Qmult_le_compat_r.
    + apply (Qplus_le_compat (a # b) (a # b)
               (3%Q / (a # b)) (a # b));
        [apply Qle_refl | exact Hinv].
    + unfold Qle. cbn [Qnum Qden]. lia.
  - assert (Hr : ((((a # b) + (a # b)) * (1 # 2))
                   == (a # b))%Q) by ring.
    rewrite Hr. apply Qle_refl.
Qed.

Lemma is3_mono_le : forall n k : nat, (1 <= n)%nat -> (n <= k)%nat ->
  is3_x k <= is3_x n.
Proof.
  intros n k Hn1 Hnk.
  assert (Hgen : forall d : nat, is3_x (n + d) <= is3_x n).
  { induction d as [|d IHd].
    - rewrite Nat.add_0_r. apply Qle_refl.
    - replace (n + Datatypes.S d)%nat with (Datatypes.S (n + d))%nat by lia.
      apply (Qle_trans _ (is3_x (n + d))).
      + apply is3_mono.
      + exact IHd. }
  replace k with (n + (k - n))%nat by lia.
  apply Hgen.
Qed.

Lemma is3_x_ub : forall n : nat, (1 <= n)%nat -> is3_x n <= (7 # 4).
Proof.
  intros n Hn. destruct n as [|n'].
  - lia.
  - apply (Qle_trans _ (is3_x 1)).
    + apply (is3_mono_le 1 (Datatypes.S n')); lia.
    + rewrite is3_x1. apply Qle_refl.
Qed.

(* ============================================================ *)
(* S4：误差窗衰减（δ ≤ 1/16；δ(Sn) ≤ δn/176；e_n ≤ 1/2^{n+1}）        *)
(* ============================================================ *)

Lemma is3_delta_step : forall n : nat, (1 <= n)%nat -> Qle (is3_delta n) (1#16) ->
  Qle (is3_delta (Datatypes.S n)) ((1#176) * is3_delta n).
Proof.
  intros n Hn1 Hdu.
  pose proof (is3_x_pos n) as Hxp.
  assert (Hlb : Qle ((5#3) * (5#3)) (is3_x n * is3_x n)).
  { apply (Qle_trans _ ((5#3) * is3_x n)%Q).
    - apply ir2_mult_le_compat_l; [apply (is3_x_lb n) | unfold Qle; cbn; lia].
    - apply Qmult_le_compat_r; [apply (is3_x_lb n) | apply Qlt_le_weak; apply (is3_x_pos n)]. }
  assert (H11 : Qle 11%Q (4 * (is3_x n * is3_x n))).
  { apply (Qle_trans _ ((4#1) * ((5#3) * (5#3)))%Q).
    - unfold Qle, Qmult. cbn [Qnum Qden]. lia.
    - rewrite (Qmult_comm (4#1) ((5#3) * (5#3))).
      rewrite (Qmult_comm (4#1) (is3_x n * is3_x n)).
      apply Qmult_le_compat_r; [exact Hlb | unfold Qle; cbn; lia]. }
  pose proof (is3_delta_succ_mul n) as Hmul.
  pose proof (is3_delta_ge0 (Datatypes.S n)) as HdS0.
  assert (Ha : Qle (11 * is3_delta (Datatypes.S n)) (is3_delta n * is3_delta n)).
  { rewrite <- Hmul.
    rewrite (Qmult_comm (is3_delta (Datatypes.S n)) (4 * (is3_x n * is3_x n))).
    apply Qmult_le_compat_r; [exact H11 | exact HdS0]. }
  assert (Hb : Qle (is3_delta n * is3_delta n) ((1#16) * is3_delta n)).
  { apply (Qmult_le_compat_r (is3_delta n) (1#16) (is3_delta n));
      [exact Hdu | apply (is3_delta_ge0 n)]. }
  assert (Hc : Qle (11 * is3_delta (Datatypes.S n)) ((1#16) * is3_delta n))
    by (apply (Qle_trans _ (is3_delta n * is3_delta n)); assumption).
  apply (Qle_trans (is3_delta (Datatypes.S n))
    (((1#16) * is3_delta n) * Qinv (11#1)) ((1#176) * is3_delta n)).
  - apply (ir2_le_mul_inv (is3_delta (Datatypes.S n)) ((1#16) * is3_delta n) (11#1)).
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + rewrite (Qmult_comm (is3_delta (Datatypes.S n)) (11#1)). exact Hc.
  - assert (Hc2 : Qinv (11#1) == (1#11)%Q) by reflexivity.
    rewrite Hc2. apply qeq_le. ring.
Qed.

Lemma is3_sixteenth : forall n : nat, (1 <= n)%nat -> Qle (is3_delta n) (1#16).
Proof.
  induction n as [|n IH].
  - lia.
  - destruct n as [|n].
    + change (is3_delta 1) with (1 # 16)%Q.
      unfold Qle. cbn [Qnum Qden]. lia.
    + intro Hle0. assert (Hn1 : (1 <= Datatypes.S n)%nat) by lia.
      pose proof (IH Hn1) as Hdu.
      apply (Qle_trans _ ((1#176) * is3_delta (Datatypes.S n))).
      * apply (is3_delta_step (Datatypes.S n)); [lia | exact Hdu].
      * apply (Qle_trans _ ((1#176) * (1#16))%Q).
        -- apply ir2_mult_le_compat_l; [exact Hdu | unfold Qle; cbn; lia].
        -- unfold Qle, Qmult. cbn [Qnum Qden]. lia.
Qed.

Lemma is3_e_step : forall n : nat, (1 <= n)%nat ->
  Qle (is3_e (Datatypes.S n)) ((1#2) * is3_e n).
Proof.
  intros n Hn1. unfold is3_e.
  apply (Qle_trans _ ((1#2) * ((1#176) * is3_delta n))%Q).
  - rewrite (Qmult_comm (1#2) (is3_delta (Datatypes.S n))).
    rewrite (Qmult_comm (1#2) ((1#176) * is3_delta n)).
    pose proof (is3_sixteenth n Hn1) as Hdu.
    apply Qmult_le_compat_r.
    + apply (is3_delta_step n); [exact Hn1 | exact Hdu].
    + unfold Qle. cbn [Qnum Qden]. lia.
  - destruct (is3_delta n) as [dn dd] eqn:Edn.
    pose proof (is3_delta_ge0 n) as Hge. rewrite Edn in Hge.
    unfold Qle in Hge. cbn [Qnum Qden] in Hge.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    unfold Qle, Qmult. cbn [Qnum Qden]. nia.
Qed.

Lemma is3_e_to_delta : forall n : nat,
  (is3_e n * ir2_qp (Datatypes.S n) == is3_delta n * ir2_qp n)%Q.
Proof.
  intro n. unfold is3_e. rewrite ir2_qp_def. ring.
Qed.

Lemma is3_decay : forall n : nat,
  Qle (is3_e (Datatypes.S n) * ir2_qp (Datatypes.S (Datatypes.S n))) 1%Q.
Proof.
  induction n as [|n IH].
  - change (is3_e 1) with (1 # 32)%Q.
    change (ir2_qp 2) with (4 # 1)%Q.
    unfold Qle, Qmult. cbn [Qnum Qden]. lia.
  - apply (Qle_trans _ (((1#2) * is3_e (Datatypes.S n))
                          * ((2#1) * ir2_qp (Datatypes.S (Datatypes.S n))))%Q).
    + rewrite ir2_qp_def.
      apply Qmult_le_compat_r.
      * apply (is3_e_step (Datatypes.S n)). lia.
      * apply Qlt_le_weak.
        apply (Qmult_lt_0_compat (2#1) (ir2_qp (Datatypes.S (Datatypes.S n)))).
        -- unfold Qlt. cbn [Qnum Qden]. lia.
        -- apply ir2_qp_pos.
    + rewrite ir2_qp_def.
      assert (Hr : ((((1#2) * is3_e (Datatypes.S n))
                      * ((2#1) * ir2_qp (Datatypes.S (Datatypes.S n))))
                     == (is3_e (Datatypes.S n)
                          * ir2_qp (Datatypes.S (Datatypes.S n))))%Q) by ring.
      rewrite Hr. exact IH.
Qed.

Lemma is3_delta_pow_le : forall n : nat, (1 <= n)%nat ->
  Qle (is3_delta n * ir2_qp n) 1%Q.
Proof.
  intros n Hn. rewrite <- (is3_e_to_delta n).
  destruct n as [|n'].
  - lia.
  - apply (is3_decay n').
Qed.

(* ============================================================ *)
(* S5：逃逸间隙引理（√3 与任一有理数的 Q 层可判间隙）                    *)
(* ============================================================ *)

(* 下侧间隙：q²<3 时 (3−q²)·(2/7) ≤ x_N−q（x_N ≤ 7/4 ⟹ 1/(x_N+q) ≥ 2/7） *)
Lemma is3_gap_lower : forall u v : Q,
  Qle 0 v -> Qle v u -> Qle u (7#4) -> Qle 3 (u*u) -> Qlt (v*v) 3 ->
  Qle ((3 - v*v) * (2#7)) (u - v).
Proof.
  intros u v Hv0 Hvu Hub H3 Hsq.
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
      pose proof H3 as H3'. rewrite Hu in H3'.
      unfold Qle, Qmult in H3'. cbn [Qnum Qden] in H3'.
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
  assert (Hw0 : Qle 0%Q (3 - v*v))
    by (apply Qlt_le_weak; apply (lic_qlt_0_minus (v*v) 3%Q Hsq)).
  assert (Hub2 : Qle (u + v) (7#2)).
  { apply (Qle_trans _ ((7#4) + (7#4))%Q).
    - apply (Qplus_le_compat u (7#4) v (7#4)).
      + exact Hub.
      + apply (Qle_trans v u (7#4)); assumption.
    - unfold Qle, Qplus, Qmult. cbn [Qnum Qden]. lia. }
  assert (Hivp : Qle 0%Q (Qinv (u + v))) by (apply ir2_inv_pos; exact Huv0).
  rewrite Hbridge.
  apply (Qle_trans _ ((u*u - v*v) * Qinv (u + v))%Q).
  - apply (Qle_trans _ ((3 - v*v) * Qinv (u + v))%Q).
    + apply ir2_mult_le_compat_l.
      * apply (ir2_inv_le (u + v) (7#2)); [exact Huv0 | exact Hub2].
      * exact Hw0.
    + apply Qmult_le_compat_r.
      * unfold Qminus. apply ir2_add_le_r. exact H3.
      * exact Hivp.
  - apply Qle_refl.
Qed.

(* 上侧小间隙：3<q²≤(7/4)² 且 d ≤ (4/11)(v²−3) ⟹ d/2 < v−u
   （严格性来源：11 < 12 = 4·3，即 1/(3b²) < (4/11)/b²） *)
Lemma is3_gap_upper_small : forall u v d : Q,
  Qlt 0 u -> Qlt 0 v -> Qlt u v -> Qle v (7#4) -> Qlt 3 (v*v) ->
  d == (u*u - 3) -> Qle 0 d -> Qle d ((4#11) * (v*v - 3)) ->
  Qlt (d * (1#2)) (v - u).
Proof.
  intros u v d Hu0 Hv0 Huv Hv74 Hsq Hd Hdu Hdle.
  assert (Hw0 : Qlt 0 (v*v - 3)) by (apply (lic_qlt_0_minus 3%Q (v*v)); exact Hsq).
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
  assert (Hsh : ((v*v - u*u) == ((v*v - 3) - d))%Q) by (rewrite Hd; ring).
  assert (Hvu2 : Qlt 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 3)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
    destruct v as [vn vd].
    unfold Qlt, Qle, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  assert (Hvup : Qlt (v + u) (7#2)).
  { apply (Qlt_le_trans (v + u) (v + v) (7#2)).
    - apply (lic_qlt_add_l v u v Huv).
    - apply (Qle_trans _ ((7#4) + (7#4))%Q).
      + apply (Qplus_le_compat v (7#4) v (7#4)); [exact Hv74 | exact Hv74].
      + apply qeq_le. reflexivity. }
  apply (Qle_lt_trans (d * (1#2)) ((v*v - u*u) * (2#7)) (v - u)).
  - apply (Qle_trans _ ((2#11) * (v*v - 3))%Q).
    + destruct (v*v - 3)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
      rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
      unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
      cbn [Qnum Qden Qplus] in *.
      assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
      assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
      lia.
    + assert (H711 : Qle ((7#11) * (v*v - 3)) (v*v - u*u)).
      { rewrite Hsh.
        destruct (v*v - 3)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
        rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
        destruct v as [vn vd].
        unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
        cbn [Qnum Qden Qplus] in *.
        assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
        assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
        nia. }
      assert (Hr27 : (((2#11) * (v*v - 3)) == ((2#7) * ((7#11) * (v*v - 3))))%Q)
        by ring.
      apply (Qle_trans _ ((2#7) * ((7#11) * (v*v - 3)))%Q).
      * rewrite Hr27. apply Qle_refl.
      * rewrite (Qmult_comm (2#7) ((7#11) * (v*v - 3))).
        apply Qmult_le_compat_r; [exact H711 | unfold Qle; cbn; lia].
  - rewrite Hbridge.
    rewrite (Qmult_comm (v*v - u*u) (2#7)).
    rewrite (Qmult_comm (v*v - u*u) (Qinv (v + u))).
    apply (Qmult_lt_compat_r (2#7) (Qinv (v + u)) (v*v - u*u)).
    + exact Hvu2.
    + apply (ir2_inv_lt (7#2) (v + u)).
      * unfold Qlt. cbn [Qnum Qden]. lia.
      * exact Hpu.
      * exact Hvup.
Qed.

(* 上侧大间隙：q > 7/4 且 (v+1)d ≤ v²−3 ⟹ d/2 < v−u（与常数无关） *)
Lemma is3_gap_upper_big : forall u v d : Q,
  Qlt 0 u -> Qlt u v -> (7#4) <= v -> Qlt 3 (v*v) ->
  d == (u*u - 3) -> Qle 0 d -> Qle ((v + 1) * d) (v*v - 3) ->
  Qlt (d * (1#2)) (v - u).
Proof.
  intros u v d Hu0 Huv Hv74 Hsq Hd Hdu Hd1.
  assert (Hw0 : Qlt 0 (v*v - 3)) by (apply (lic_qlt_0_minus 3%Q (v*v)); exact Hsq).
  assert (Hvp : Qlt 0 v).
  { apply (Qlt_le_trans 0%Q (7#4) v); [unfold Qlt; cbn; lia | exact Hv74]. }
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
  assert (Hsh : ((v*v - u*u) == ((v*v - 3) - d))%Q) by (rewrite Hd; ring).
  assert (Hvu2 : Qle 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 3)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
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
  assert (Hdv : Qle (d * v) ((v*v - 3) - d)).
  { destruct (v*v - 3)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    destruct v as [vn vd].
    rewrite ?Ew, ?Ed in Hw0, Hd1, Hdu.
    unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  assert (Hkey : Qle (d * (1#2)) (((v*v - 3) - d) * Qinv ((2#1) * v))).
  { apply (ir2_le_mul_inv (d * (1#2)) ((v*v - 3) - d) ((2#1) * v)).
    - exact H2vp.
    - assert (Hring : (((d * (1#2)) * ((2#1) * v)) == (d * v))%Q) by ring.
      rewrite Hring. exact Hdv. }
  assert (Hvu2p : Qlt 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 3)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    destruct v as [vn vd].
    rewrite ?Ew, ?Ed in Hw0, Hd1, Hdu.
    unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  apply (Qle_lt_trans (d * (1#2)) (((v*v - 3) - d) * Qinv ((2#1) * v)) (v - u)).
  - exact Hkey.
  - apply (Qle_lt_trans (((v*v - 3) - d) * Qinv ((2#1) * v))
            ((v*v - u*u) * Qinv ((2#1) * v)) (v - u)).
    + assert (Hle2 : Qle (v*v - 3 - d) (v*v - u*u)).
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

Definition is3_tail : lic_tail_bounded is3_x is3_e.
Proof.
  intros n k Hn1 Hnk.
  pose proof (is3_mono_le n k Hn1 Hnk) as Hmono.
  pose proof (is3_delta_ge0 n) as Hd0n.
  pose proof (is3_delta_pos n) as Hdpn.
  assert (Habs : Qabs ((is3_x k - is3_x n)%Q) == (is3_x n - is3_x k)%Q).
  { rewrite Qabs_Qminus. apply ir2_abs_sub. exact Hmono. }
  assert (Hsumpos : Qlt 0 (is3_x n + is3_x k)).
  { apply ir2_qpos_add.
    - apply (Qlt_le_trans 0%Q (5#3) (is3_x n)).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + apply (is3_x_lb n).
    - apply (Qlt_le_trans 0%Q (5#3) (is3_x k)).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + apply (is3_x_lb k). }
  assert (Hsumne : ~ ((is3_x n + is3_x k) == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (is3_x n + is3_x k) Hsumpos);
        rewrite Hc; apply Qeq_refl).
  assert (Hbridge : (((is3_x n - is3_x k)
                      == (is3_delta n - is3_delta k) * Qinv (is3_x n + is3_x k))%Q)).
  { pose proof (bno_mul_div_self (is3_x n + is3_x k) Hsumne) as Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((is3_x n - is3_x k) * (is3_x n + is3_x k))
                    * Qinv (is3_x n + is3_x k)) == (is3_x n - is3_x k))%Q).
    { rewrite <- (Qmult_assoc (is3_x n - is3_x k) (is3_x n + is3_x k)
                    (Qinv (is3_x n + is3_x k))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite ir2_sq_diff in Hpm.
    assert (Hsh : ((is3_x n * is3_x n - is3_x k * is3_x k)
                   == (is3_delta n - is3_delta k))%Q)
      by (unfold is3_delta; ring).
    rewrite Hsh in Hpm. exact (Qeq_sym _ _ Hpm). }
  apply Qlt_to_QltT. rewrite Habs. rewrite Hbridge.
  assert (Hsumb : Qle ((10#3)) (is3_x n + is3_x k)).
  { apply (Qle_trans _ ((5#3) + (5#3))%Q).
    - apply qeq_le. reflexivity.
    - apply (Qplus_le_compat (5#3) (is3_x n) (5#3) (is3_x k));
        [apply (is3_x_lb n) | apply (is3_x_lb k)]. }
  assert (Hinvp : Qle 0%Q (Qinv (is3_x n + is3_x k)))
    by (apply ir2_inv_pos; exact Hsumpos).
  assert (Hstep1 : Qle ((is3_delta n - is3_delta k) * Qinv (is3_x n + is3_x k))
                     (is3_delta n * Qinv (is3_x n + is3_x k))).
  { apply Qmult_le_compat_r.
    - unfold Qminus, Qle, Qopp in *.
      destruct (is3_delta n) as [dn dd] eqn:Edn.
      destruct (is3_delta k) as [ek ed] eqn:Edk.
      pose proof (is3_delta_ge0 k) as H0k.
      rewrite Edk in H0k. unfold Qle in H0k. cbn [Qnum Qden] in H0k.
      cbn [Qnum Qden Qplus Qopp Qmult].
      assert (Hdd0 : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
      assert (Hed0 : (0 < Z.pos ed)%Z) by apply Pos2Z.is_pos.
      nia.
    - exact Hinvp. }
  assert (Hstep2 : Qle (is3_delta n * Qinv (is3_x n + is3_x k))
                     (is3_delta n * Qinv ((10#3)))).
  { rewrite (Qmult_comm (is3_delta n) (Qinv (is3_x n + is3_x k))).
    rewrite (Qmult_comm (is3_delta n) (Qinv ((10#3)))).
    apply Qmult_le_compat_r.
    - apply (ir2_inv_le (10#3) (is3_x n + is3_x k));
        [unfold Qlt; cbn [Qnum Qden]; lia | exact Hsumb].
    - exact Hd0n. }
  assert (Hstep3 : Qlt (is3_delta n * Qinv ((10#3))) ((1#2) * is3_delta n)).
  { destruct (is3_delta n) as [dn dd] eqn:Edn.
    pose proof (is3_delta_pos n) as Hdp.
    rewrite Edn in Hdp. unfold Qlt in Hdp. cbn [Qnum Qden] in Hdp.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    unfold Qlt, Qmult, Qinv. cbn [Qnum Qden Qinv]. nia. }
  apply (Qle_lt_trans ((is3_delta n - is3_delta k) * Qinv (is3_x n + is3_x k))
          (is3_delta n * Qinv (is3_x n + is3_x k)) ((1#2) * is3_delta n)).
  - exact Hstep1.
  - apply (Qle_lt_trans (is3_delta n * Qinv (is3_x n + is3_x k))
            (is3_delta n * Qinv ((10#3))) ((1#2) * is3_delta n)).
    + exact Hstep2.
    + exact Hstep3.
Defined.

Definition is3_vanish : lic_vanish is3_e.
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
    apply (Qle_lt_trans (is3_e (Datatypes.S n'))
            (Qinv (ir2_qp (Datatypes.S (Datatypes.S n')))) ((pn # pd)%Q)).
    + apply (ir2_le_inv (ir2_qp (Datatypes.S (Datatypes.S n')))
               (is3_e (Datatypes.S n'))).
      * apply ir2_qp_pos.
      * rewrite (Qmult_comm (ir2_qp (Datatypes.S (Datatypes.S n')))
                            (is3_e (Datatypes.S n'))).
        apply (is3_decay n').
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

Definition is3_escape : lic_escape_window is3_x is3_e.
Proof.
  intro q.
  destruct (Qlt_bool 0%Q q) eqn:Hpos.
  - pose proof (lic_qlt_bool_true 0%Q q Hpos) as Hq0.
    destruct (Qlt_bool (q * q) 3%Q) eqn:H3b.
    + (* q² < 3：N := den(q) + 8，x_N 自上方追上 q *)
      pose proof (lic_qlt_bool_true (q * q) 3%Q H3b) as H3.
      destruct q as [a b].
      assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
      assert (Hkb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b) by (apply Z2Nat.id; lia).
      assert (Hkb1 : (1 <= Z.to_nat (Z.pos b))%nat).
      { destruct (Z.to_nat (Z.pos b)) as [|k'] eqn:Ek; [ | lia].
        exfalso. pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz.
        rewrite Ek in Hz. cbn in Hz. lia. }
      exists (Z.to_nat (Z.pos b) + 8)%nat. split. lia.
      apply Qlt_to_QltT.
      assert (Hxsq : Qle 3%Q (is3_x (Z.to_nat (Z.pos b) + 8)
                                * is3_x (Z.to_nat (Z.pos b) + 8)))
        by apply is3_sq_ge3.
      assert (Hqx : Qlt ((a # b) * (a # b))
                    (is3_x (Z.to_nat (Z.pos b) + 8)
                     * is3_x (Z.to_nat (Z.pos b) + 8)))
        by (apply (Qlt_le_trans ((a # b) * (a # b)) 3%Q
                    (is3_x (Z.to_nat (Z.pos b) + 8)
                     * is3_x (Z.to_nat (Z.pos b) + 8))); assumption).
      assert (Hqle : Qlt (a # b) (is3_x (Z.to_nat (Z.pos b) + 8)))
        by (apply (ir2_lt_of_sq (is3_x (Z.to_nat (Z.pos b) + 8)) (a # b));
            [apply Qlt_le_weak; apply (is3_x_pos (Z.to_nat (Z.pos b) + 8))
            | apply Qlt_le_weak; exact Hq0 | exact Hqx]).
      assert (Habs : Qabs ((a # b) - is3_x (Z.to_nat (Z.pos b) + 8))%Q
                     == (is3_x (Z.to_nat (Z.pos b) + 8) - (a # b))%Q).
      { rewrite Qabs_Qminus. apply ir2_abs_sub. apply Qlt_le_weak. exact Hqle. }
      rewrite Habs.
      apply (Qlt_le_trans (is3_e (Z.to_nat (Z.pos b) + 8))
              (Qinv ((7 * (Z.pos b * Z.pos b)) # 1))
              (is3_x (Z.to_nat (Z.pos b) + 8) - (a # b))%Q).
      * apply (Qle_lt_trans (is3_e (Z.to_nat (Z.pos b) + 8))
                (Qinv (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8))))
                (Qinv ((7 * (Z.pos b * Z.pos b)) # 1))).
        -- apply (ir2_le_inv (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                   (is3_e (Z.to_nat (Z.pos b) + 8))).
           ++ apply ir2_qp_pos.
           ++ rewrite (Qmult_comm (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                       (is3_e (Z.to_nat (Z.pos b) + 8))).
              replace (Z.to_nat (Z.pos b) + 8)%nat
                with (Datatypes.S (Z.to_nat (Z.pos b) + 7))%nat by lia.
              apply (is3_decay (Z.to_nat (Z.pos b) + 7)).
        -- apply (ir2_inv_lt (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                   ((7 * (Z.pos b * Z.pos b)) # 1)).
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
              assert (Hz : (7 * (Z.pos b * Z.pos b)
                            <= Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 8)))%Z).
              { pose proof (is3_pow7sq (Z.to_nat (Z.pos b))) as Hp.
                apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
                rewrite !Nat2Z.inj_mul in Hp.
                rewrite Hkb in Hp. cbn [Z.of_nat] in Hp. lia. }
              pose proof (f_equal Z.of_nat Hb3) as Hb4.
              rewrite Nat2Z.inj_mul in Hb4. cbn [Z.of_nat] in Hb4.
              unfold Qlt. cbn [Qnum Qden]. lia.
      * apply (Qle_trans _ ((3 - (a # b) * (a # b))
                             * (2#7))%Q).
        -- apply (ir2_ge_inv ((7 * (Z.pos b * Z.pos b)) # 1)
                   (((3 - (a # b) * (a # b)) * (2#7))%Q)).
           ++ unfold Qlt. cbn [Qnum Qden]. lia.
           ++ unfold Qle, Qmult, Qminus.
              pose proof H3 as H3'. unfold Qlt, Qmult, Qminus in H3'.
              cbn [Qnum Qden Qplus Qopp] in H3' |- *.
              assert (Hb1 : (1 <= Z.pos b)%Z) by lia.
              nia.
        -- apply (is3_gap_lower (is3_x (Z.to_nat (Z.pos b) + 8)) (a # b)).
           ++ apply Qlt_le_weak. exact Hq0.
           ++ apply Qlt_le_weak. exact Hqle.
           ++ apply is3_x_ub. lia.
           ++ exact Hxsq.
           ++ exact H3.
    + (* 3 ≤ q² *)
      pose proof (lic_qlt_bool_false_le (q * q) 3%Q H3b) as Hge3.
      destruct (Qeq_dec (q * q) 3%Q) as [Heq3 | Hne3].
      * exfalso. exact (is3_no_sqrt3 q Heq3).
      * destruct (Qlt_bool 3%Q (q * q)) eqn:H3lt.
        -- pose proof (lic_qlt_bool_true 3%Q (q * q) H3lt) as Hlt3.
           destruct (Qlt_bool (7#4) q) eqn:H74b.
           ++ (* 7/4 < q：N := num(q) + den(q) + 1，x_N 自下方逼近 *)
              pose proof (lic_qlt_bool_true (7#4) q H74b) as H74.
              destruct q as [a b].
              assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
              assert (H74z : (7 * Z.pos b < 4 * a)%Z).
              { pose proof H74 as H74'. unfold Qlt in H74'.
                cbn [Qnum Qden] in H74'. lia. }
              assert (Hz3 : (3 * (Z.pos b * Z.pos b) + 1 <= a * a)%Z).
              { pose proof Hlt3 as H3'. unfold Qlt, Qmult in H3'.
                cbn [Qnum Qden] in H3'. lia. }
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
              assert (Hdpow : Qle (is3_delta (Z.to_nat a
                                              + Z.to_nat (Z.pos b) + 1)
                                    * ir2_qp (Z.to_nat a
                                              + Z.to_nat (Z.pos b) + 1)) 1%Q).
              { apply (is3_delta_pow_le). lia. }
              assert (Hbnd : Qle (((a # b) + 1)
                                  * is3_delta (Z.to_nat a
                                               + Z.to_nat (Z.pos b) + 1))
                           (((a # b) * (a # b)) - 3%Q)%Q).
              { apply (Qle_trans _ (((a # b) + 1)
                                    * Qinv (ir2_qp (Z.to_nat a
                                             + Z.to_nat (Z.pos b) + 1)))%Q).
                - apply ir2_mult_le_compat_l.
                  + apply (ir2_le_inv (ir2_qp (Z.to_nat a
                                          + Z.to_nat (Z.pos b) + 1))
                              (is3_delta (Z.to_nat a
                                           + Z.to_nat (Z.pos b) + 1))).
                    * apply ir2_qp_pos.
                    * rewrite (Qmult_comm (ir2_qp (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1))
                                (is3_delta (Z.to_nat a
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
              assert (Hdl : Qlt (is3_delta (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1))
                            (((a # b) * (a # b)) - 3%Q)%Q).
              { destruct (is3_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                  as [dn dd] eqn:Ed.
                rewrite (ir2_qp_pow (Z.to_nat a
                          + Z.to_nat (Z.pos b) + 1)) in Hdpow.
                rewrite ?Ed in Hdpow, Hbnd.
                pose proof (is3_delta_pos (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1)) as Hdp3.
                rewrite ?Ed in Hdp3.
                unfold Qle, Qlt in *.
                cbn [Qnum Qden Qmult Qminus Qopp Qplus] in *.
                assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
                nia. }
              assert (Hxq : Qlt (is3_x (Z.to_nat a
                                       + Z.to_nat (Z.pos b) + 1))
                                (a # b)).
              { apply (ir2_lt_of_sq (a # b)
                        (is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))).
                - apply Qlt_le_weak. exact Hq0.
                - apply Qlt_le_weak.
                  apply (is3_x_pos (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
                - pose proof Hdl as Hdl'.
                  unfold is3_delta in Hdl'.
                  pose proof (lic_qlt_minus_add_r ((a # b) * (a # b)) 3%Q)
                    as Hr1.
                  pose proof (lic_qlt_minus_add_r
                                (is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 * is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                                3%Q) as Hr2.
                  apply (Qle_lt_trans
                          (is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                           * is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                          ((is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                            * is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                            - 3%Q) + 3%Q)%Q
                          ((a # b) * (a # b))).
                  + apply (qeq_le _ _ (Qeq_sym _ _ Hr2)).
                  + apply (lic_qlt_comp_r
                              (((a # b) * (a # b) - 3%Q) + 3%Q)%Q
                              ((a # b) * (a # b))
                              ((is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                * is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                - 3%Q) + 3%Q)%Q).
                    * exact Hr1.
                    * apply (lic_qlt_add_r
                                (is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 * is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 - 3%Q)%Q
                                ((a # b) * (a # b) - 3%Q)%Q
                                3%Q Hdl'). }
              assert (HeqN : (is3_e (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                              == is3_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                  * (1#2))%Q).
              { unfold is3_e. ring. }
              rewrite HeqN.
              rewrite (ir2_abs_sub (a # b)
                        (is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)))
                by (apply Qlt_le_weak; exact Hxq).
              apply (is3_gap_upper_big
                      (is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                      (a # b)
                      (is3_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1))).
              ** apply (is3_x_pos (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
              ** exact Hxq.
              ** apply Qlt_le_weak. exact H74.
              ** exact Hlt3.
              ** reflexivity.
              ** apply (is3_delta_ge0 (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
              ** exact Hbnd.
           ++ (* 3 < q² 且 q ≤ 7/4：N := den(q) + 8，窗 4/11（x_N 自下方追上 q） *)
              pose proof (lic_qlt_bool_false_le (7#4) q H74b) as H74.
              destruct q as [a b].
              assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
              assert (Hkb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b) by (apply Z2Nat.id; lia).
              assert (Hkb1 : (1 <= Z.to_nat (Z.pos b))%nat).
              { destruct (Z.to_nat (Z.pos b)) as [|k'] eqn:Ek; [ | lia].
                exfalso. pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz.
                rewrite Ek in Hz. cbn in Hz. lia. }
              assert (Hq3z : (3 * (Z.pos b * Z.pos b) + 1 <= a * a)%Z).
              { pose proof Hlt3 as H3'. unfold Qlt, Qmult in H3'.
                cbn [Qnum Qden] in H3'. lia. }
              exists (Z.to_nat (Z.pos b) + 8)%nat. split. lia.
              apply Qlt_to_QltT.
              assert (Hpow3 : (3 * (Z.pos b * Z.pos b)
                               <= Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 8)))%Z).
              { pose proof (ir2_pow3sq (Z.to_nat (Z.pos b))) as Hp.
                apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
                rewrite !Nat2Z.inj_mul in Hp. rewrite Hkb in Hp.
                cbn [Z.of_nat] in Hp. lia. }
              assert (Hdpow : Qle (is3_delta (Z.to_nat (Z.pos b) + 8)
                                    * ir2_qp (Z.to_nat (Z.pos b) + 8)) 1%Q)
                by (apply is3_delta_pow_le; lia).
              rewrite (ir2_qp_pow (Z.to_nat (Z.pos b) + 8)) in Hdpow.
              assert (H411 : Qlt (is3_delta (Z.to_nat (Z.pos b) + 8))
                              (((4#11) * (((a # b) * (a # b)) - 3%Q))%Q)).
              { destruct (is3_delta (Z.to_nat (Z.pos b) + 8)) as [dn dd] eqn:Ed.
                rewrite ?Ed in Hdpow.
                pose proof (is3_delta_pos (Z.to_nat (Z.pos b) + 8)) as Hdp.
                rewrite Ed in Hdp. unfold Qlt in Hdp. cbn [Qnum Qden] in Hdp.
                unfold Qle, Qlt, Qmult in Hdpow. cbn [Qnum Qden] in Hdpow.
                unfold Qlt, Qmult, Qminus. cbn [Qnum Qden Qplus Qopp] in Hdp, Hdpow |- *.
                assert (Hdd0 : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
                assert (Hbp : (1 <= Z.pos b)%Z) by lia.
                nia. }
              assert (Hdl : Qlt (is3_delta (Z.to_nat (Z.pos b) + 8))
                              ((((a # b) * (a # b)) - 3%Q)%Q)).
              { apply (Qlt_le_trans (is3_delta (Z.to_nat (Z.pos b) + 8))
                        (((4#11) * (((a # b) * (a # b)) - 3%Q))%Q)
                        ((((a # b) * (a # b)) - 3%Q)%Q)).
                - exact H411.
                - apply (Qle_trans _ (1%Q * (((a # b) * (a # b)) - 3%Q))%Q).
                  + apply Qmult_le_compat_r.
                    * unfold Qle. cbn [Qnum Qden]. lia.
                    * apply Qlt_le_weak.
                      apply (lic_qlt_0_minus 3%Q ((a # b) * (a # b)) Hlt3).
                  + apply qeq_le. apply Qmult_1_l. }
              assert (Hqx : Qlt (is3_x (Z.to_nat (Z.pos b) + 8)
                                  * is3_x (Z.to_nat (Z.pos b) + 8))
                            ((a # b) * (a # b))).
              { assert (Hr : (((is3_x (Z.to_nat (Z.pos b) + 8)
                                * is3_x (Z.to_nat (Z.pos b) + 8) - 3%Q) + 3%Q)
                              == (is3_x (Z.to_nat (Z.pos b) + 8)
                                   * is3_x (Z.to_nat (Z.pos b) + 8)))%Q)
                  by apply lic_qlt_minus_add_r.
                rewrite <- Hr.
                apply (Qlt_le_trans _ ((((a # b) * (a # b)) - 3%Q) + 3%Q)%Q).
                - apply (lic_qlt_add_r _ _ 3%Q Hdl).
                - apply qeq_le. apply lic_qlt_minus_add_r. }
              assert (Hqle : Qlt (is3_x (Z.to_nat (Z.pos b) + 8)) (a # b))
                by (apply (ir2_lt_of_sq (a # b) (is3_x (Z.to_nat (Z.pos b) + 8)));
                    [apply Qlt_le_weak; exact Hq0
                    | apply Qlt_le_weak;
                       apply (is3_x_pos (Z.to_nat (Z.pos b) + 8))
                    | exact Hqx]).
              rewrite (ir2_abs_sub (a # b) (is3_x (Z.to_nat (Z.pos b) + 8)))
                by (apply Qlt_le_weak; exact Hqle).
              assert (Heq8 : (is3_e (Z.to_nat (Z.pos b) + 8)
                              == is3_delta (Z.to_nat (Z.pos b) + 8)
                                  * (1#2))%Q).
              { unfold is3_e. ring. }
              rewrite Heq8.
              apply (is3_gap_upper_small
                      (is3_x (Z.to_nat (Z.pos b) + 8)) (a # b)
                      (is3_delta (Z.to_nat (Z.pos b) + 8))).
              ** apply (is3_x_pos (Z.to_nat (Z.pos b) + 8)).
              ** exact Hq0.
              ** exact Hqle.
              ** exact H74.
              ** exact Hlt3.
              ** reflexivity.
              ** apply (is3_delta_ge0 (Z.to_nat (Z.pos b) + 8)).
              ** apply Qlt_le_weak. exact H411.
        -- (* ¬(3 < q²) 且 3 ≤ q² ⟹ q² == 3 ⟹ 与 is3_no_sqrt3 矛盾 *)
           exfalso. apply Hne3.
           pose proof (lic_qlt_bool_false_le 3%Q (q * q) H3lt) as Hle3'.
           apply (Qle_antisym (q * q) 3%Q); [exact Hle3' | exact Hge3].
  - (* q ≤ 0 *)
    pose proof (lic_qlt_bool_false_le 0%Q q Hpos) as Hq0.
    destruct q as [qn qd].
    assert (Hqd : (0 < Z.pos qd)%Z) by apply Pos2Z.is_pos.
    exists 1%nat. split. lia.
    apply Qlt_to_QltT.
    rewrite (Qabs_Qminus (qn # qd) (is3_x 1)).
    rewrite (ir2_abs_sub (is3_x 1) (qn # qd)).
    2: { apply (Qle_trans (qn # qd) 0%Q (is3_x 1)).
         - exact Hq0.
         - apply Qlt_le_weak. apply (is3_x_pos 1). }
    rewrite is3_x1.
    assert (Heq1 : is3_e 1 == (1#32)%Q) by reflexivity.
    rewrite Heq1.
    unfold Qle in Hq0. cbn [Qnum Qden] in Hq0.
    unfold Qlt, Qminus. cbn [Qnum Qden Qopp Qplus]. lia.
Defined.

(* ============================================================ *)
(* S7：主定理装配（真走母定理 exact 装配，零旁路）+ 提取探针 + 公理面自审 *)
(* ============================================================ *)

Theorem is3_sqrt3_irrational_criterion : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u)
                            is3_x
                            (lic_seq_cauchy is3_x is3_e is3_tail is3_vanish))
       (real_const q)))).
Proof.
  intro q.
  exact (lic_irrational_criterion is3_x is3_e is3_tail is3_escape is3_vanish q).
Qed.

From Stdlib Require Import Extraction.
Separate Extraction is3_sqrt3_irrational_criterion is3_tail is3_vanish
  is3_escape is3_x is3_delta is3_e is3_decay is3_gap_lower
  is3_gap_upper_small is3_gap_upper_big is3_no_sqrt3.

Print Assumptions is3_sqrt3_irrational_criterion.
