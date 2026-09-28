(* ========================================================================== *)
(* abl_Ln2_native_escape_03.v — ln2 原生逃逸路线首步（独立消融件）             *)
(* 使命：Ln2Escape.v 头注 :31-36 自报的「lne_B 整性面 × 递推 d_n 做窗内/       *)
(*   窗外二分」路线首步。lne_B 整性面三件树内已闭合（lne_B_posT/              *)
(*   lne_B_le_p4/lne_B_int）；本件落地其配对面——递推母线 d_n = 2^n·n! 的      *)
(*   整性梯：                                                                *)
(*   ① abl3_dn_xn_int：d_n·x_n ∈ Z（sif_d 递推模式原生移植）；                 *)
(*   ② abl3_dn_q_int：n ≥ den q ⟹ d_n·q ∈ Z（v|n! 整除梯）；                   *)
(*   ③ abl3_native_gap：q ≠ x_n（Set 面严格分离前提）⟹ |q − x_n| ≥            *)
(*      1/d_n = 2^{-n}/n!（原生间隙地板）；                                   *)
(*   ④ abl3_floor_le_window：地板 ≤ 判定窗 2^{-n}（全 n 无条件，因子 1/n! ≤ 1）*)
(*      ——「窗放不进」的形式化证书；                                          *)
(*   ⑤ abl3_escape_of_floor_beat：地板击穿窗则单点逃逸成立（条件逃逸接口，     *)
(*      未来逼近面的挂载位）。                                                *)
(* 与母判据 lic_irrational_criterion 的关系：母判据三槽（尾控/逃逸窗/消失）中  *)
(*   本件只涉逃逸窗槽 Hw : lic_escape_window ln2i_x ln2i_e 的供给难度侧：      *)
(*   ③+④ 合取即「经 d_n 母线的原生间隙地板在任何指标处都不超过判定窗」         *)
(*   （v·n! ≥ 1 恒成立），故首步二分在本路线内无法升格为无条件                 *)
(*   ln2i_escape_spec——与 Ln2Escape 头注 :32-35「窗放不进」数值论证吻合。     *)
(*   逃逸窗槽的 unconditional 闭合须 d_n² 档 Hermite 间隙步（母线×分母方幂与  *)
(*   部分和耦合），即一级 Padé ④⑤ 肢面；实例化 ⑤ 的击穿前提即经              *)
(*   lic_irrational_criterion 得条件形判定。                                 *)
(* 数学结论：逃逸窗见证 n(q) 的存在蕴涵 X 与 q 的正分离（尾控夹逼），故无条件   *)
(*   逃逸窗 ≡ 对每 q 的构造性分离数据；地板/窗之比 1/n! ≤ 1 不随 n 增长——     *)
(*   首步路线数学闭合；升格唯 Padé 逼近面。命名：abl3_ 前缀（零撞名）。        *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、SumInvFactEscape          *)
(*   （sif_d 递推模式基座）、UpReqBanachNormOpp、UpReqIrrationalCriterion      *)
(*   （母判据件，只读使用）、UpReqLn2Irrational（ln2i_x/ln2i_e/ln2i_p2         *)
(*   序列面）；Stdlib QArith、ZArith、Arith（Factorial）、Lia、Qfield。         *)
(* 构造性：纯构造性（零经典逻辑、零排中、零认授）；语句面结论全 Set 层          *)
(*   （sigT/And/QltT/QleT'/QeqT 形）；整除/序型箭头前提（nat/Z 层）为          *)
(*   匿名量化前提（C 类，库先例同构）。编译配方：rocq c -Q <池> ""。           *)
(* ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqLn2Irrational.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* §1 递推母线：d_0 = 1，d_{S m} = 2·(S m)·d_m（即 2^n·n!）            *)
(* ============================================================ *)

Fixpoint abl3_dn (n : nat) : Q :=
  match n with
  | O => (1 # 1)
  | Datatypes.S m => ((2 # 1) * ((Z.of_nat (Datatypes.S m)) # 1)) * abl3_dn m
  end.

Lemma abl3_dn_succ : forall m : nat,
  abl3_dn (Datatypes.S m) == ((2 # 1) * ((Z.of_nat (Datatypes.S m)) # 1)) * abl3_dn m.
Proof.
  intro m. exact (Qeq_refl (((2 # 1) * ((Z.of_nat (Datatypes.S m)) # 1)) * abl3_dn m)%Q).
Qed.

Lemma abl3_dn_pos : forall n : nat, Qlt 0 (abl3_dn n).
Proof.
  induction n as [|n IH].
  - unfold Qlt. cbn [abl3_dn Qnum Qden]. lia.
  - rewrite abl3_dn_succ. apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; unfold Qlt; cbn [Qnum Qden]; lia.
    + exact IH.
Qed.

(* Z 承载：d_n == (2^n)#1 · (n!)#1 *)
Lemma abl3_dn_Z : forall n : nat,
  abl3_dn n == ((Z.of_nat (2 ^ n)) # 1) * ((Z.of_nat (fact n)) # 1).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite abl3_dn_succ. rewrite IH.
    rewrite Nat.pow_succ_r'.
    replace (fact (Datatypes.S n)) with (Datatypes.S n * fact n)%nat by reflexivity.
    rewrite !Nat2Z.inj_mul. cbn [Z.of_nat].
    unfold Qmult, Qeq. cbn [Qnum Qden Pos.mul]. lia.
Qed.

Lemma abl3_fact_ge1 : forall n : nat, (1 <= fact n)%nat.
Proof.
  induction n as [|n IH]; cbn [fact].
  - lia.
  - nia.
Qed.

(* n! 的整除梯：1 ≤ v ≤ n ⟹ n! = v·c（显式商见证） *)
Lemma abl3_fact_dvd : forall v n : nat, (1 <= v)%nat -> (v <= n)%nat ->
  sigT (fun c : nat => fact n = (v * c)%nat).
Proof.
  intros v n. induction n as [|n IH]; intros Hle Hle2.
  - lia.
  - destruct (Nat.eq_dec v (Datatypes.S n)) as [E | NE].
    + subst v. exists (fact n). cbn [fact]. lia.
    + assert (Hvn : (v <= n)%nat) by lia.
      destruct (IH ltac:(lia) Hvn) as [c Hc].
      exists (Datatypes.S n * c)%nat. cbn [fact]. lia.
Qed.

(* ============================================================ *)
(* §2 整性梯主件：d_n·x_n ∈ Z（sif_d 递推模式原生移植）                  *)
(*   递推核：d_{S m}·t_{S m} = 2(S m)·d_m/((S m)·2^{S m}) = d_m/2^m       *)
(*           = m!（整步进，与 e 链 n!·s_{n+1} = (n+1)·n!·s_n + 1 同型）   *)
(* ============================================================ *)

Lemma abl3_dn_t : forall m : nat,
  abl3_dn (Datatypes.S m) * ln2i_t (Datatypes.S m) == ((Z.of_nat (fact m)) # 1).
Proof.
  intro m. unfold ln2i_t.
  replace (2 ^ Datatypes.S m)%nat with (2 * 2 ^ m)%nat
    by (rewrite Nat.pow_succ_r'; reflexivity).
  rewrite abl3_dn_succ. rewrite (abl3_dn_Z m).
  pose proof (Nat2Z.inj_mul 2 (2 ^ m)) as Hm.
  pose proof (ln2i_powZ_pos m) as Hp.
  destruct ((Z.of_nat (Datatypes.S m) * Z.of_nat ((2 * 2 ^ m)%nat))%Z) as [|p|p] eqn:E.
  - exfalso. nia.
  - unfold Qinv, Qmult, Qeq. cbn [Qnum Qden Pos.mul]. nia.
  - unfold Qinv, Qmult, Qeq. cbn [Qnum Qden Pos.mul]. nia.
Qed.

Theorem abl3_dn_xn_int : forall n : nat,
  sigT (fun z : Z => QeqT (abl3_dn n * ln2i_x n) (z # 1)).
Proof.
  induction n as [|n IH].
  - exists 0%Z. apply qeq_imp_qeqT. cbn [abl3_dn ln2i_x].
    unfold Qmult, Qeq. cbn [Qnum Qden Pos.mul]. lia.
  - destruct IH as [z Hz].
    assert (Hzq : abl3_dn n * ln2i_x n == (z # 1))
      by (apply qeqT_imp_qeq; exact Hz).
    exists ((2 * Z.of_nat (Datatypes.S n)) * z + Z.of_nat (fact n))%Z.
    apply qeq_imp_qeqT.
    cbn [ln2i_x].
    transitivity (abl3_dn (Datatypes.S n) * ln2i_x n
                  + abl3_dn (Datatypes.S n) * ln2i_t (Datatypes.S n))%Q.
    + ring.
    + rewrite (abl3_dn_t n). rewrite abl3_dn_succ.
      (* 目标积在 abl3_dn_succ 改写后为左结合，Hzq 模式因结合律错位失配
         ——先以 Qmult_assoc 重排结合，再改写。 *)
      rewrite <- (Qmult_assoc ((2 # 1) * ((Z.of_nat (Datatypes.S n)) # 1))
                   (abl3_dn n) (ln2i_x n)). rewrite Hzq.
      unfold Qplus, Qmult, Qeq. cbn [Qnum Qden Pos.mul]. lia.
Qed.

(* ============================================================ *)
(* §3 同乘整性：n ≥ den q ⟹ d_n·q ∈ Z                                   *)
(* ============================================================ *)

Theorem abl3_dn_q_int : forall (u : Z) (pv : positive) (n : nat),
  (Z.pos pv <= Z.of_nat n)%Z ->
  sigT (fun z : Z => QeqT (abl3_dn n * ((u # pv)%Q)) (z # 1)).
Proof.
  intros u pv n Hd.
  pose (vn := Z.to_nat (Z.pos pv)).
  assert (Hpv : Z.pos pv = Z.of_nat vn)
    by (unfold vn; symmetry; apply Z2Nat.id; apply Z.lt_le_incl; apply Pos2Z.is_pos).
  assert (Hvn : (vn <= n)%nat).
  { apply (proj2 (Nat2Z.inj_le vn n)). rewrite <- Hpv. exact Hd. }
  assert (Hvn1 : (1 <= vn)%nat).
  { apply (proj2 (Nat2Z.inj_lt 0 vn)). rewrite <- Hpv. apply Pos2Z.is_pos. }
  destruct (abl3_fact_dvd vn n Hvn1 Hvn) as [c Hc].
  exists ((Z.of_nat (2 ^ n)) * (Z.of_nat c) * u)%Z.
  apply qeq_imp_qeqT.
  rewrite (abl3_dn_Z n).
  unfold Qmult, Qeq. cbn [Qnum Qden Pos.mul].
  rewrite Hc. rewrite Hpv. rewrite !Nat2Z.inj_mul. cbn [Z.of_nat]. lia.
Qed.

(* ============================================================ *)
(* §4 原生间隙地板：q ≠ x_n（Set 面分离前提）⟹ |q − x_n| ≥ 1/d_n          *)
(*   （1/d_n = 2^{-n}/n!；头注 :26-27「2/(n!·2^n) 级」间隙的母线显式形）    *)
(* ============================================================ *)

Theorem abl3_native_gap : forall (u : Z) (pv : positive) (n : nat),
  (Z.pos pv <= Z.of_nat n)%Z ->
  QltT 0 (Qabs (((u # pv)%Q - ln2i_x n)%Q)) ->
  QleT' (Qinv (abl3_dn n)) (Qabs (((u # pv)%Q - ln2i_x n)%Q)).
Proof.
  intros u pv n Hd Hpos.
  destruct (abl3_dn_xn_int n) as [z2 Hz2].
  destruct (abl3_dn_q_int u pv n Hd) as [z1 Hz1].
  assert (Hne : ~ (abl3_dn n == 0%Q)).
  { intro E. pose proof (abl3_dn_pos n) as Hp.
    exact (Qlt_not_eq 0%Q (abl3_dn n) Hp (eq_sym E)). }
  (* 核心缩放等式：d_n·(q − x_n) == (z1 − z2)#1 *)
  assert (Hscale : abl3_dn n * ((u # pv)%Q - ln2i_x n)%Q == ((z1 - z2) # 1)%Q).
  { apply qeqT_imp_qeq in Hz1. apply qeqT_imp_qeq in Hz2.
    transitivity ((abl3_dn n * (u # pv)%Q - abl3_dn n * ln2i_x n)%Q).
    { ring. }
    rewrite Hz1. rewrite Hz2.
    (* Qmake-Z 原子环式 ring 不透视——走 Z 层 unfold。 *)
    unfold Qminus, Qplus, Qopp, Qmult, Qeq. cbn [Qnum Qden Pos.mul]. lia. }
  assert (Habs : Qabs (abl3_dn n * ((u # pv)%Q - ln2i_x n)%Q)
                 == abl3_dn n * Qabs (((u # pv)%Q - ln2i_x n)%Q)).
  { rewrite (Qabs_Qmult (abl3_dn n) (((u # pv)%Q - ln2i_x n)%Q)).
    rewrite (Qabs_pos (abl3_dn n) (Qlt_le_weak 0%Q (abl3_dn n) (abl3_dn_pos n))).
    reflexivity. }
  pose proof (QltT_to_Qlt _ _ Hpos) as Hposq.
  assert (Hspos : Qlt 0 (abl3_dn n * Qabs (((u # pv)%Q - ln2i_x n)%Q))).
  { apply Qmult_lt_0_compat.
    - exact (abl3_dn_pos n).
    - exact Hposq. }
  (* 故 |z1 − z2| ≥ 1（非零整数绝对值地板） *)
  assert (Hzne : ~ ((z1 - z2)%Z = 0%Z)).
  { intro E.
    assert (Habs0 : Qlt 0 (Qabs (abl3_dn n * ((u # pv)%Q - ln2i_x n)%Q))).
    { rewrite Habs. exact Hspos. }
    rewrite Hscale in Habs0.
    rewrite E in Habs0. cbn [Qabs] in Habs0.
    unfold Qlt in Habs0. cbn [Qnum Qden] in Habs0. lia. }
  assert (Habsform : Qabs (((z1 - z2) # 1)%Q) == ((Z.abs (z1 - z2)) # 1)%Q)
    by reflexivity.
  pose proof (proj2 (Z.abs_pos (z1 - z2)) Hzne) as Habsz.
  assert (Hchain : Qle (1 # 1) (abl3_dn n * Qabs (((u # pv)%Q - ln2i_x n)%Q))).
  { rewrite <- Habs. rewrite Hscale. rewrite Habsform.
    unfold Qle. cbn [Qnum Qden]. lia. }
  (* d_n·|g| ≥ 1 ⟹ |g| ≥ 1/d_n（右乘 Qinv d_n） *)
  assert (Hinvpos : Qlt 0 (Qinv (abl3_dn n)))
    by (apply Qinv_lt_0_compat; exact (abl3_dn_pos n)).
  assert (Hdn1 : abl3_dn n * Qinv (abl3_dn n) == 1%Q)
    by (apply Qmult_inv_r; exact Hne).
  assert (H1 : Qle ((1 # 1) * Qinv (abl3_dn n))
                   ((abl3_dn n * Qabs (((u # pv)%Q - ln2i_x n)%Q))
                      * Qinv (abl3_dn n)))
    by (apply Qmult_le_compat_r; [exact Hchain | apply Qlt_le_weak; exact Hinvpos]).
  assert (E2 : ((abl3_dn n * Qabs (((u # pv)%Q - ln2i_x n)%Q)) * Qinv (abl3_dn n))%Q
               == (Qabs (((u # pv)%Q - ln2i_x n)%Q)
                     * (abl3_dn n * Qinv (abl3_dn n)))%Q) by ring.
  rewrite E2, Hdn1, Qmult_1_r in H1.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qinv (abl3_dn n)) ((1 # 1) * Qinv (abl3_dn n))
                   (Qabs (((u # pv)%Q - ln2i_x n)%Q))).
  - apply qeq_le. symmetry. apply Qmult_1_l.
  - exact H1.
Qed.

(* ============================================================ *)
(* §5 窗适配证书：地板 ≤ 判定窗（全 n 无条件）——「窗放不进」形式化          *)
(*   因子恒等式：1/d_n = (1/n!)·2^{-n}，1/n! ≤ 1 恒成立且不随 n 增长，       *)
(*   故经 d_n 母线的原生间隙在任何指标处都不超过判定窗 ln2i_e n = 2^{-n}。   *)
(* ============================================================ *)

Theorem abl3_floor_le_window : forall n : nat, QleT' (Qinv (abl3_dn n)) (ln2i_e n).
Proof.
  intro n. unfold ln2i_e. apply Qle_to_QleT'.
  pose proof (abl3_dn_Z n) as HZ.
  pose proof (abl3_fact_ge1 n) as Hf1.
  assert (Hc1 : Qle (Qinv ((Z.of_nat (fact n)) # 1)) (Qinv (1 # 1))).
  { apply (ln2i_inv_le (1 # 1) ((Z.of_nat (fact n)) # 1)).
    - unfold Qlt. cbn [Qnum Qden]. lia.
    - unfold Qle. cbn [Qnum Qden]. lia. }
  pose proof (Qmult_le_compat_r (Qinv ((Z.of_nat (fact n)) # 1)) (Qinv (1 # 1))
                (Qinv (ln2i_p2 n)) Hc1
                (Qlt_le_weak 0%Q (Qinv (ln2i_p2 n)) (ln2i_inv_pos n))) as Hstep.
  assert (E10 : Qinv (1 # 1) == (1 # 1)%Q) by reflexivity.
  rewrite E10 in Hstep.
  apply (Qle_trans (Qinv (abl3_dn n))
                   (Qinv (ln2i_p2 n) * Qinv ((Z.of_nat (fact n)) # 1))
                   (Qinv (ln2i_p2 n))).
  - apply qeq_le.
    rewrite HZ. rewrite ln2i_p2_Z.
    rewrite (Qinv_mult_distr ((Z.of_nat (2 ^ n)) # 1) ((Z.of_nat (fact n)) # 1)).
    reflexivity.
  - apply (Qle_trans _ (Qinv ((Z.of_nat (fact n)) # 1) * Qinv (ln2i_p2 n))).
    + apply qeq_le. ring.
    + apply (Qle_trans _ ((1 # 1) * Qinv (ln2i_p2 n))).
      * exact Hstep.
      * apply qeq_le. apply Qmult_1_l.
Qed.

(* ============================================================ *)
(* §6 条件逃逸接口：地板击穿窗则单点逃逸成立（未来逼近面挂载位）              *)
(*   逃逸窗槽 lic_escape_window 的单点形。击穿前提（第三前提）在本路线      *)
(*   内无实例（§4+§5 合取证其与地板恒矛盾于增长向），其真例化=一级          *)
(*   T1–T7 Padé ④⑤ 肢面——届时本接口即母判据条件形的直接应用位。            *)
(* ============================================================ *)

Theorem abl3_escape_of_floor_beat : forall (q : Q) (n : nat), (1 <= n)%nat ->
  QltT 0 (Qabs ((q - ln2i_x n)%Q)) ->
  QltT (ln2i_e n) (Qinv (abl3_dn n)) ->
  sigT (fun m : nat => And ((1 <= m)%nat)
    (QltT (ln2i_e m) (Qabs ((q - ln2i_x m)%Q)))).
Proof.
  intros q n Hn1 Hsep Hbeat.
  exists n. split.
  - exact Hn1.
  - exfalso.
    (* 击穿前提（窗小于地板）与 §5 地板不超窗恒矛盾（本路线内无实例）
       ——夹出 Qlt 自反矛盾后以 ex falso 收束。 *)
    pose proof (abl3_floor_le_window n) as Hfw.
    pose proof (QltT_to_Qlt _ _ Hbeat) as Hblt.
    pose proof (QleT'_to_Qle _ _ Hfw) as Hfle.
    exact (Qlt_not_eq (Qinv (abl3_dn n)) (Qinv (abl3_dn n))
             (Qle_lt_trans (Qinv (abl3_dn n)) (ln2i_e n) (Qinv (abl3_dn n))
                Hfle Hblt)
             (Qeq_refl (Qinv (abl3_dn n)))).
Qed.

(* ============================================================ *)
(* §7 提取检验 + 公理面自审                                              *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abl3_dn abl3_dn_xn_int abl3_dn_q_int
  abl3_native_gap abl3_floor_le_window abl3_escape_of_floor_beat.

Print Assumptions abl3_dn_xn_int.
Print Assumptions abl3_dn_q_int.
Print Assumptions abl3_native_gap.
Print Assumptions abl3_floor_le_window.
Print Assumptions abl3_escape_of_floor_beat.
