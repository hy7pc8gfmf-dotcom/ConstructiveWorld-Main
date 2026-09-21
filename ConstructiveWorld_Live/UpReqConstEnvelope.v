(* ============================================================ *)
(* ToyR 玩具证替换件 —— T260 台账席 战役包U（tier2 批量面第十一批）   *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列玩具位中真刀位  *)
(* 之证明体替换为显式见证微刀（裸 reflexivity 换 Qeq_refl 显式项；   *)
(* apply 反射位换全参显式见证项），非刀位玩具体与其余全部文本逐字    *)
(* 保留，声明面与引用面零改动，零新增 Require，证明结尾记号与原件    *)
(* 逐件守恒，纯构造性收口，文尾保留原件 Print Assumptions 追印面。    *)
(* 清单：                                                          *)
(*   c3e_real_zero_proj（原 L165，显式见证微刀 1 处）                        *)
(*   c3e_ln2_proj（原 L471，显式见证微刀 1 处）                              *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqConstEnvelope.v —— 席 Q9（EXPL1 候选 C3 深探席）          *)
(*   三常数包络母定理：显式尾界双边有理包络                        *)
(*   （相位=分析重转编译重）                                      *)
(*                                                                *)
(* 使命：把 e/ln2/π 的五处 inline 同型包络计算粗粒化为一个母定理——    *)
(*   「显式尾界双边有理包络」：给定 Real x 的部分和 s0、显式尾界       *)
(*   t0（单边宽度证书）与指标 n，部分和给出 x 的构造性双边有理包络     *)
(*   （Bishop 形 real_le_b，Q4 evd 接口同形），一母三子              *)
(*   （c3e_env_ln2 / c3e_env_e / c3e_env_pi 实例）。                *)
(*                                                                *)
(* EXPL1 判词（五处 inline 位点实测，重整化流信号=待合并同型重复）：   *)
(*   ① e×3：S03_QExp.v:702 / :1058 / :1139 三处消费                 *)
(*      exp_tail_abs_geom2（:622，全库最高供体消费之一）做同型          *)
(*      「部分和±尾界」包络推理；                                    *)
(*   ② π×2：S10_KVQuantTrig.v:8807 real_pi_leibniz_lt_ten_thirds    *)
(*      与 :8830 real_pi_leibniz_between_tenthirds——手搓「常数+余量   *)
(*      +N 阈值」inline 夹逼；S11_TP3B5.v:1534 a3_diag_abs 同族对角    *)
(*      桥（级数尾账）。                                             *)
(*   ③ ln2：G05_LogSmall.v:976 logd_log_two_pos_real——正性假设面，     *)
(*      本席 ln2 子件自建交错调和柯西实数与之独立并存（对接            *)
(*      real_log 2 需 log_seq 桥，独立工程，挂账）。                  *)
(*                                                                *)
(* 分层：                                                           *)
(*   S0 Q 层小件：三分拆、|z| 双侧界、sub_le_self、倒数比较。          *)
(*   S1 母定理 c3e_env_mother：lo := s0 − t0、hi := s0 + t0 给        *)
(*        real_le_b (real_const lo) x ≤_B ≤_B real_le_b x (real_const hi) *)
(*        且 hi − lo == 2·t0（sigT 打包 lo hi）。                     *)
(*        形态校准注记：任务书「hi−lo ≤ tail n」按证书语义落为          *)
(*        hi−lo == 2·t0（t0 为单边宽度，双侧端点各让一步）；           *)
(*        Bishop 形 = Q4 接口预埋（evd_le_b_mult_pos_l 同形族，        *)
(*        正数左乘放大器可直接复合于包络端点）。                       *)
(*   S2 ln2 子件（全构造性自建单跳）：交错调和配对正项级数              *)
(*        Σ(1/(2j+1)−1/(2j+2))，伸缩尾界 1/(2n+2)，自建柯西实数        *)
(*        c3e_ln2_real，经母定理导出。                                *)
(*   S3 e 子件：消费 exp_tail_abs_geom2（S03:622）链——                *)
(*        exp_tail_abs_le → exp_tail_abs_geom2 实例化于 A=1，换        *)
(*        Real 层（exp_const_proj 投影桥），经母定理导出。             *)
(*   S4 π 子件：消费 sc_lp_odd_diff_bound（S10:2787 级数尾件在盘，     *)
(*        任务书预判的「级数尾缺件降档」不发生，全形态导出）+           *)
(*        real_pi_leibniz_proj 投影桥，经母定理导出。                  *)
(*   S5 G3 速率：c3e_env_rate（模量线性族 N_c(eps) 形，与论文 3        *)
(*        §10.5 接口对齐——q_arch_inv 的 N 即 ⌈·⌉ 构造位）+            *)
(*        c3e_env_rate_ln2 实例（c:=1）。π 速率同族（c:=2，           *)
(*        c3e_inv_le_inv 直给）；e 为阶乘衰减（严格快于线性族，        *)
(*        速率件如实从缺）。                                          *)
(*                                                                *)
(* 领土：本件独立新文件，零改他席产物；在飞禁碰件未触碰。              *)
(* Require 仅消费 .vo 基座：CW_ConstructiveWorld_219（S01..S15       *)
(*   Require Export 聚合面）、UpRealLeB（real_le_b 完成件）。         *)
(*                                                                *)
(* 【公理面】本件零新公理、零 Hypothesis 位、零经典公理；              *)
(*   文末对全部主件 Print Assumptions 核验 Closed。                   *)
(* 红线：纯构造性；主件结论全 Set 层（sigT/real_le_b/QeqT；real_lt    *)
(*   内嵌 And 为 Q4 evd 同款已验形态）；零 Obj.magic（不进提取面）；    *)
(*   三实例必须真走母定理（禁平行抄写）。                              *)
(* 数值 sanity（python fractions 验算在案，20260917）：               *)
(*   ln2 n=4: [1627/2520 − 1/10, +1/10] ∋ ln2=0.693147 ✓             *)
(*   e   n=5: [2.716667−1/60, +1/60] ∋ e=2.718282 ✓                  *)
(*   π   n=2: [2.976046−4/13, +4/13] ∋ π=3.141593 ✓                  *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.PeanoNat Lia.

(* ============================================================ *)
(* S0. Q 层小件                                                     *)
(* ============================================================ *)

(* 三分拆：0 < z 或 z ≤ 0（Qcompare 0 z 分支，Qlt_alt/Qeq_alt/Qgt_alt） *)
Lemma c3e_ztri : forall z : Q, Or (Qlt 0 z) (Qle z 0).
Proof.
  intro z.
  destruct (Qcompare 0 z) eqn:E.
  - right. apply qeq_le. apply (Qeq_sym 0 z). apply (proj2 (Qeq_alt 0 z)). exact E.
  - left. apply (proj2 (Qlt_alt 0 z)). exact E.
  - right. apply (Qlt_le_weak z 0). apply (proj2 (Qgt_alt 0 z)). exact E.
Qed.

(* z ≤ |z|（Q 层） *)
Lemma c3e_qle_abs : forall z : Q, Qle z (Qabs z).
Proof.
  intro z.
  destruct (c3e_ztri z) as [Hz | Hz].
  - rewrite (Qabs_pos z (Qlt_le_weak 0 z Hz)). apply Qle_refl.
  - rewrite (Qabs_neg z Hz).
    apply (proj2 (Qle_minus_iff z (- z))).
    setoid_replace (- z - z) with (-(z + z)) by ring.
    apply (Qle_trans _ (- (0 + 0))).
    + setoid_replace (- (0 + 0)) with 0 by ring. apply Qle_refl.
    + apply (Qopp_le_compat (z + z) (0 + 0)).
      apply (Qplus_le_compat z 0 z 0); [ exact Hz | exact Hz ].
Qed.

(* −|z| ≤ z（Q 层） *)
Lemma c3e_neg_abs_le : forall z : Q, Qle (- Qabs z) z.
Proof.
  intro z.
  destruct (c3e_ztri z) as [Hz | Hz].
  - rewrite (Qabs_pos z (Qlt_le_weak 0 z Hz)).
    apply (Qle_trans (- z) 0 z).
    + apply (Qle_trans (- z) (- 0) 0).
      * apply (Qopp_le_compat 0 z). exact (Qlt_le_weak 0 z Hz).
      * setoid_replace (- 0) with 0 by ring. apply Qle_refl.
    + exact (Qlt_le_weak 0 z Hz).
  - rewrite (Qabs_neg z Hz).
    setoid_replace (- (- z)) with z by ring.
    apply Qle_refl.
Qed.

(* |z| ≤ w ⟹ 0 ≤ z + w ∧ 0 ≤ w − z（母定理证书的 Q 内核） *)
Lemma c3e_abs_two : forall (z w : Q), Qle (Qabs z) w ->
  And (Qle 0 (z + w)) (Qle 0 (w - z)).
Proof.
  intros z w H. split.
  - apply (Qle_trans _ ((- Qabs z) + Qabs z)).
    + setoid_replace ((- Qabs z) + Qabs z) with 0 by ring. apply Qle_refl.
    + apply (Qle_trans _ (z + Qabs z)).
      * apply (Qplus_le_compat (- Qabs z) z (Qabs z) (Qabs z)).
        -- apply c3e_neg_abs_le.
        -- apply Qle_refl.
      * apply (Qplus_le_compat z z (Qabs z) w).
        -- apply Qle_refl.
        -- exact H.
  - apply (Qle_trans _ (w - Qabs z)).
    + exact (proj1 (Qle_minus_iff (Qabs z) w) H).
    + setoid_replace (w - Qabs z) with (w + (- Qabs z)) by ring.
      setoid_replace (w - z) with (w + (- z)) by ring.
      apply (Qplus_le_compat w w (- Qabs z) (- z)).
      * apply Qle_refl.
      * apply (Qopp_le_compat z (Qabs z)). apply c3e_qle_abs.
Qed.

(* U − V ≤ U（V ≥ 0；伸缩尾界的收尾步） *)
Lemma c3e_sub_le_self : forall (U V : Q), Qle 0 V -> Qle (U - V) U.
Proof.
  intros U V Hv.
  setoid_replace (U - V) with (U + (- V)) by ring.
  apply (Qle_trans _ (U + 0)).
  - apply (Qplus_le_compat U U (- V) 0).
    + apply Qle_refl.
    + setoid_replace 0 with (- 0) by ring.
      apply (Qopp_le_compat 0 V). exact Hv.
  - setoid_replace (U + 0) with U by ring. apply Qle_refl.
Qed.

(* 倒数比较：b ≤ a ⟹ 1/(a+2) ≤ 1/(b+2)（q_le_div_le 直推） *)
Lemma c3e_inv_le_inv : forall a b : nat, (b <= a)%nat ->
  Qle (1 / (Z.of_nat (a + 2) # 1)) (1 / (Z.of_nat (b + 2) # 1)).
Proof.
  intros a b Hab.
  apply (q_le_div_le 1 (Z.of_nat (a + 2) # 1) 1 (Z.of_nat (b + 2) # 1)).
  - unfold Qlt; simpl; lia.
  - unfold Qlt; simpl; lia.
  - setoid_replace (1 * (Z.of_nat (b + 2) # 1))
      with (Z.of_nat (b + 2) # 1) by (apply Qmult_1_l).
    setoid_replace (1 * (Z.of_nat (a + 2) # 1))
      with (Z.of_nat (a + 2) # 1) by (apply Qmult_1_l).
    unfold Qle; simpl; lia.
Qed.

(* projT1 real_zero k == 0（real_zero Defined 直约） *)
Lemma c3e_real_zero_proj : forall k : nat, projT1 real_zero k == 0.
Proof. intro k. exact (Qeq_refl (projT1 real_zero k)). Qed.

(* ============================================================ *)
(* S1. 母定理：显式尾界双边有理包络（c3e_env_mother）                 *)
(* ============================================================ *)

(* 给定 x : Real、部分和 s0、显式尾界 t0（单边宽度证书）与指标 n：
   若对一切 k ≥ n 有 s0 − t0 ≤ projT1 x k ≤ s0 + t0，
   则 lo := s0 − t0、hi := s0 + t0 构成 x 的 Bishop 形双边有理包络：
   lo ≤_B x ≤_B hi，且 hi − lo == 2·t0。 *)
Theorem c3e_env_mother : forall (x : Real) (s0 t0 : Q) (n : nat),
  (forall k : nat, (n <= k)%nat ->
    And (Qle (s0 - t0) (projT1 x k))
        (Qle (projT1 x k) (s0 + t0))) ->
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo) x)
        (And (real_le_b x (real_const hi))
             (QeqT (hi - lo) (2 * t0))))).
Proof.
  intros x s0 t0 n Hptw.
  exists (s0 - t0). exists (s0 + t0).
  split.
  - (* 下侧：real_const (s0 − t0) ≤_B x *)
    unfold real_le_b. intros eps Heps.
    unfold real_lt in Heps. unfold real_lt.
    destruct Heps as [d [Hd [N0 HN0]]].
    exists d. split.
    + exact Hd.
    + exists (Nat.max N0 n). intros k HkN.
      apply Qlt_to_QltT.
      assert (HkLe : (n <= k)%nat).
      { apply (Nat.le_trans n (Nat.max N0 n) k).
        - apply Nat.le_max_r.
        - apply (NatLe_drop _ _ HkN). }
      assert (HkN0 : NatLe N0 k).
      { apply NatLe_lift. apply (Nat.le_trans N0 (Nat.max N0 n) k).
        - apply Nat.le_max_l.
        - apply (NatLe_drop _ _ HkN). }
      destruct (Hptw k HkLe) as [Hlo Hhi].
      specialize (HN0 k HkN0). apply QltT_to_Qlt in HN0.
      rewrite c3e_real_zero_proj in HN0.
      assert (Hz0 : projT1 eps k - 0 == projT1 eps k) by ring.
      rewrite Hz0 in HN0.
      rewrite (real_plus_proj x eps k).
      rewrite (real_const_proj (s0 - t0) k).
      assert (Hshift : Qle (projT1 eps k)
                           (projT1 x k + projT1 eps k - (s0 - t0))).
      { apply (proj2 (Qle_minus_iff (projT1 eps k)
                        (projT1 x k + projT1 eps k - (s0 - t0)))).
        setoid_replace (projT1 x k + projT1 eps k - (s0 - t0) - projT1 eps k)
          with (projT1 x k - (s0 - t0)) by ring.
        exact (proj1 (Qle_minus_iff (s0 - t0) (projT1 x k)) Hlo). }
      exact (Qlt_le_trans d (projT1 eps k) _ HN0 Hshift).
  - (* 上侧：x ≤_B real_const (s0 + t0) *)
    split.
    unfold real_le_b. intros eps Heps.
    unfold real_lt in Heps. unfold real_lt.
    destruct Heps as [d [Hd [N0 HN0]]].
    exists d. split.
    + exact Hd.
    + exists (Nat.max N0 n). intros k HkN.
      apply Qlt_to_QltT.
      assert (HkLe : (n <= k)%nat).
      { apply (Nat.le_trans n (Nat.max N0 n) k).
        - apply Nat.le_max_r.
        - apply (NatLe_drop _ _ HkN). }
      assert (HkN0 : NatLe N0 k).
      { apply NatLe_lift. apply (Nat.le_trans N0 (Nat.max N0 n) k).
        - apply Nat.le_max_l.
        - apply (NatLe_drop _ _ HkN). }
      destruct (Hptw k HkLe) as [Hlo Hhi].
      specialize (HN0 k HkN0). apply QltT_to_Qlt in HN0.
      rewrite c3e_real_zero_proj in HN0.
      assert (Hz0 : projT1 eps k - 0 == projT1 eps k) by ring.
      rewrite Hz0 in HN0.
      rewrite (real_plus_proj (real_const (s0 + t0)) eps k).
      rewrite (real_const_proj (s0 + t0) k).
      assert (Hshift : Qle (projT1 eps k)
                           (s0 + t0 + projT1 eps k - projT1 x k)).
      { apply (proj2 (Qle_minus_iff (projT1 eps k)
                        (s0 + t0 + projT1 eps k - projT1 x k))).
        setoid_replace (s0 + t0 + projT1 eps k - projT1 x k - projT1 eps k)
          with (s0 + t0 - projT1 x k) by ring.
        exact (proj1 (Qle_minus_iff (projT1 x k) (s0 + t0)) Hhi). }
      exact (Qlt_le_trans d (projT1 eps k) _ HN0 Hshift).
    + (* 宽度：hi − lo == 2·t0 *)
      apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* S2. ln2 子件：交错调和配对正项级数（全构造性自建单跳）              *)
(* ============================================================ *)

(* 配对交错调和项：1/(2j+1) − 1/(2j+2)（正项、递减） *)
Definition c3e_l2_term (j : nat) : Q :=
  1 / (Z.of_nat (2 * j + 1) # 1) - 1 / (Z.of_nat (2 * j + 2) # 1).

Fixpoint c3e_l2_sum (m : nat) : Q :=
  match m with
  | Datatypes.O => c3e_l2_term 0
  | Datatypes.S p => c3e_l2_sum p + c3e_l2_term (Datatypes.S p)
  end.

(* 项的伸缩上界：term (Datatypes.S p) ≤ 1/(2p+2) − 1/(2p+4) *)
Lemma c3e_l2_term_le : forall p : nat,
  Qle (c3e_l2_term (Datatypes.S p))
      (1 / (Z.of_nat (2 * p + 2) # 1) - 1 / (Z.of_nat (2 * p + 4) # 1)).
Proof.
  intro p.
  unfold c3e_l2_term.
  replace (Z.of_nat (2 * Datatypes.S p + 1)) with (Z.of_nat (2 * p + 3)) by lia.
  replace (Z.of_nat (2 * Datatypes.S p + 2)) with (Z.of_nat (2 * p + 4)) by lia.
  setoid_replace (1 / (Z.of_nat (2 * p + 3) # 1) - 1 / (Z.of_nat (2 * p + 4) # 1))
    with (- (1 / (Z.of_nat (2 * p + 4) # 1)) + 1 / (Z.of_nat (2 * p + 3) # 1)) by ring.
  setoid_replace (1 / (Z.of_nat (2 * p + 2) # 1) - 1 / (Z.of_nat (2 * p + 4) # 1))
    with (- (1 / (Z.of_nat (2 * p + 4) # 1)) + 1 / (Z.of_nat (2 * p + 2) # 1)) by ring.
  apply (Qplus_le_compat (- (1 / (Z.of_nat (2 * p + 4) # 1)))
                         (- (1 / (Z.of_nat (2 * p + 4) # 1)))
                         (1 / (Z.of_nat (2 * p + 3) # 1))
                         (1 / (Z.of_nat (2 * p + 2) # 1))).
  - apply Qle_refl.
  - apply (q_le_div_le 1 (Z.of_nat (2 * p + 3) # 1) 1 (Z.of_nat (2 * p + 2) # 1)).
    + unfold Qlt; simpl; lia.
    + unfold Qlt; simpl; lia.
    + setoid_replace (1 * (Z.of_nat (2 * p + 2) # 1))
        with (Z.of_nat (2 * p + 2) # 1) by (apply Qmult_1_l).
      setoid_replace (1 * (Z.of_nat (2 * p + 3) # 1))
        with (Z.of_nat (2 * p + 3) # 1) by (apply Qmult_1_l).
      unfold Qle; simpl; lia.
Qed.

(* 项正性：term (Datatypes.S p) ≥ 0 *)
Lemma c3e_l2_term_pos : forall p : nat, Qle 0 (c3e_l2_term (Datatypes.S p)).
Proof.
  intro p.
  unfold c3e_l2_term.
  replace (Z.of_nat (2 * Datatypes.S p + 1)) with (Z.of_nat (2 * p + 3)) by lia.
  replace (Z.of_nat (2 * Datatypes.S p + 2)) with (Z.of_nat (2 * p + 4)) by lia.
  apply (proj1 (Qle_minus_iff (1 / (Z.of_nat (2 * p + 4) # 1))
                              (1 / (Z.of_nat (2 * p + 3) # 1)))).
  apply (q_le_div_le 1 (Z.of_nat (2 * p + 4) # 1) 1 (Z.of_nat (2 * p + 3) # 1)).
  - unfold Qlt; simpl; lia.
  - unfold Qlt; simpl; lia.
  - setoid_replace (1 * (Z.of_nat (2 * p + 3) # 1))
      with (Z.of_nat (2 * p + 3) # 1) by (apply Qmult_1_l).
    setoid_replace (1 * (Z.of_nat (2 * p + 4) # 1))
      with (Z.of_nat (2 * p + 4) # 1) by (apply Qmult_1_l).
    unfold Qle; simpl; lia.
Qed.

(* 部分和单调：步进 + 链 *)
Lemma c3e_l2_sum_step : forall m : nat, Qle (c3e_l2_sum m) (c3e_l2_sum (Datatypes.S m)).
Proof.
  intro m.
  setoid_replace (c3e_l2_sum (Datatypes.S m)) with (c3e_l2_sum m + c3e_l2_term (Datatypes.S m))
    by reflexivity.
  apply Qle_plus_nonneg_r.
  apply c3e_l2_term_pos.
Qed.

Lemma c3e_l2_mono : forall m n : nat, (m <= n)%nat -> Qle (c3e_l2_sum m) (c3e_l2_sum n).
Proof.
  intros m n. induction n as [| n IH]; intro Hmn.
  - assert (Hm0 : (m = 0)%nat) by lia. subst m. apply Qle_refl.
  - destruct (Nat.eq_dec m (Datatypes.S n)) as [He | Hne].
    + subst m. apply Qle_refl.
    + assert (Hmn' : (m <= n)%nat) by lia.
      apply (Qle_trans _ (c3e_l2_sum n)).
      * apply IH. exact Hmn'.
      * apply c3e_l2_sum_step.
Qed.

(* 伸缩尾界（核心单跳）：n ≤ m ⟹ s m − s n ≤ 1/(2n+2) − 1/(2m+2) *)
Lemma c3e_l2_inv : forall m n : nat, (n <= m)%nat ->
  Qle (c3e_l2_sum m - c3e_l2_sum n)
      (1 / (Z.of_nat (2 * n + 2) # 1) - 1 / (Z.of_nat (2 * m + 2) # 1)).
Proof.
  intros m n. induction m as [| m IH]; intro Hnm.
  - assert (Hn0 : (n = 0)%nat) by lia. subst n.
    apply qeq_le. ring.
  - destruct (Nat.eq_dec n (Datatypes.S m)) as [He | Hne].
    + subst n.
      apply qeq_le. ring.
    + assert (Hnm' : (n <= m)%nat) by lia.
      specialize (IH Hnm').
      assert (Hstep : c3e_l2_sum (Datatypes.S m)
                      == c3e_l2_sum m + c3e_l2_term (Datatypes.S m)) by reflexivity.
      rewrite Hstep.
      setoid_replace ((c3e_l2_sum m + c3e_l2_term (Datatypes.S m)) - c3e_l2_sum n)
        with ((c3e_l2_sum m - c3e_l2_sum n) + c3e_l2_term (Datatypes.S m)) by ring.
      apply (Qle_trans _ ((1 / (Z.of_nat (2 * n + 2) # 1)
                           - 1 / (Z.of_nat (2 * m + 2) # 1))
                          + (1 / (Z.of_nat (2 * m + 2) # 1)
                             - 1 / (Z.of_nat (2 * Datatypes.S m + 2) # 1)))).
      * apply (Qplus_le_compat (c3e_l2_sum m - c3e_l2_sum n)
                               (1 / (Z.of_nat (2 * n + 2) # 1)
                                - 1 / (Z.of_nat (2 * m + 2) # 1))
                               (c3e_l2_term (Datatypes.S m))
                               (1 / (Z.of_nat (2 * m + 2) # 1)
                                - 1 / (Z.of_nat (2 * Datatypes.S m + 2) # 1))).
        -- exact IH.
        -- replace (Z.of_nat (2 * Datatypes.S m + 2)) with (Z.of_nat (2 * m + 4)) by lia.
           apply c3e_l2_term_le.
      * setoid_replace ((1 / (Z.of_nat (2 * n + 2) # 1)
                         - 1 / (Z.of_nat (2 * m + 2) # 1))
                        + (1 / (Z.of_nat (2 * m + 2) # 1)
                           - 1 / (Z.of_nat (2 * Datatypes.S m + 2) # 1)))
          with (1 / (Z.of_nat (2 * n + 2) # 1)
                - 1 / (Z.of_nat (2 * Datatypes.S m + 2) # 1)) by ring.
        apply Qle_refl.
Qed.

(* 单边宽度证书（供母定理）：n ≤ k ⟹ s n − U ≤ s k ≤ s n + U，
   U := 1/(2n+2) *)
Lemma c3e_l2_cert : forall n k : nat, (n <= k)%nat ->
  And (Qle (c3e_l2_sum n - 1 / (Z.of_nat (2 * n + 2) # 1)) (c3e_l2_sum k))
      (Qle (c3e_l2_sum k) (c3e_l2_sum n + 1 / (Z.of_nat (2 * n + 2) # 1))).
Proof.
  intros n k Hnk. split.
  - (* s n − U ≤ s n ≤ s k *)
    apply (Qle_trans _ (c3e_l2_sum n)).
    + apply (proj2 (Qle_minus_iff (c3e_l2_sum n - 1 / (Z.of_nat (2 * n + 2) # 1))
                                  (c3e_l2_sum n))).
      setoid_replace (c3e_l2_sum n - (c3e_l2_sum n - 1 / (Z.of_nat (2 * n + 2) # 1)))
        with (1 / (Z.of_nat (2 * n + 2) # 1)) by ring.
      apply (Qlt_le_weak 0 (1 / (Z.of_nat (2 * n + 2) # 1))).
      exact (q_arch_inv_pos (2 * n)).
    + apply c3e_l2_mono. exact Hnk.
  - (* s k ≤ s n + U：s k − s n ≤ U − V ≤ U *)
    apply (proj2 (Qle_minus_iff (c3e_l2_sum k)
                                (c3e_l2_sum n + 1 / (Z.of_nat (2 * n + 2) # 1)))).
    setoid_replace (c3e_l2_sum n + 1 / (Z.of_nat (2 * n + 2) # 1) - c3e_l2_sum k)
      with (1 / (Z.of_nat (2 * n + 2) # 1) - (c3e_l2_sum k - c3e_l2_sum n)) by ring.
    apply (Qle_trans _ (1 / (Z.of_nat (2 * k + 2) # 1))).
    + apply (Qlt_le_weak 0 (1 / (Z.of_nat (2 * k + 2) # 1))).
      exact (q_arch_inv_pos (2 * k)).
    + apply (proj2 (Qle_minus_iff (1 / (Z.of_nat (2 * k + 2) # 1))
                                  (1 / (Z.of_nat (2 * n + 2) # 1)
                                   - (c3e_l2_sum k - c3e_l2_sum n)))).
      setoid_replace (1 / (Z.of_nat (2 * n + 2) # 1)
                      - (c3e_l2_sum k - c3e_l2_sum n)
                      - 1 / (Z.of_nat (2 * k + 2) # 1))
        with ((1 / (Z.of_nat (2 * n + 2) # 1)
               - 1 / (Z.of_nat (2 * k + 2) # 1))
              - (c3e_l2_sum k - c3e_l2_sum n)) by ring.
      exact (proj1 (Qle_minus_iff (c3e_l2_sum k - c3e_l2_sum n)
                                  (1 / (Z.of_nat (2 * n + 2) # 1)
                                   - 1 / (Z.of_nat (2 * k + 2) # 1)))
                   (c3e_l2_inv k n Hnk)).
Qed.


(* ============================================================ *)
(* S2 续：ln2 的柯西实数（自建：交错调和配对级数极限）                 *)
(* ============================================================ *)

(* ln2 的柯西实数（自建：交错调和配对级数极限） *)
Definition c3e_ln2_real : Real.
Proof.
  exists (c3e_l2_sum).
  intros eps Heps.
  destruct (q_arch_inv eps (QltT_to_Qlt 0 eps Heps)) as [N HN].
  exists N. intros m n Hm Hn.
  apply Qlt_to_QltT.
  destruct (Nat.leb m n) eqn:E.
  - apply Nat.leb_le in E.
    (* m ≤ n：|s m − s n| = s n − s m ≤ 1/(2m+2) ≤ 1/(N+2) < eps *)
    rewrite (sc_lp_abs_sym (c3e_l2_sum m) (c3e_l2_sum n)).
    assert (Hpos : Qle 0 (c3e_l2_sum n - c3e_l2_sum m)).
    { apply (proj1 (Qle_minus_iff (c3e_l2_sum m) (c3e_l2_sum n))).
      apply c3e_l2_mono. exact E. }
    rewrite (Qabs_pos (c3e_l2_sum n - c3e_l2_sum m) Hpos).
    apply (Qle_lt_trans _ (1 / (Z.of_nat (N + 2) # 1))).
    + apply (Qle_trans _ (1 / (Z.of_nat (2 * m + 2) # 1))).
      * apply (Qle_trans _ (1 / (Z.of_nat (2 * m + 2) # 1)
                            - 1 / (Z.of_nat (2 * n + 2) # 1))).
        -- exact (c3e_l2_inv n m E).
        -- apply c3e_sub_le_self.
           apply (Qlt_le_weak 0 (1 / (Z.of_nat (2 * n + 2) # 1))).
           exact (q_arch_inv_pos (2 * n)).
      * apply c3e_inv_le_inv.
        assert (Hm' : (N <= m)%nat) by (apply (NatLe_drop _ _ Hm)).
        lia.
    + exact HN.
  - apply Nat.leb_gt in E.
    assert (Hnm : (n <= m)%nat) by lia.
    assert (Hn' : (N <= n)%nat) by (apply (NatLe_drop _ _ Hn)).
    (* n < m：|s m − s n| = s m − s n ≤ 1/(2n+2) ≤ 1/(N+2) < eps *)
    assert (Hpos : Qle 0 (c3e_l2_sum m - c3e_l2_sum n)).
    { apply (proj1 (Qle_minus_iff (c3e_l2_sum n) (c3e_l2_sum m))).
      apply c3e_l2_mono. exact Hnm. }
    rewrite (Qabs_pos (c3e_l2_sum m - c3e_l2_sum n) Hpos).
    apply (Qle_lt_trans _ (1 / (Z.of_nat (N + 2) # 1))).
    + apply (Qle_trans _ (1 / (Z.of_nat (2 * n + 2) # 1))).
      * apply (Qle_trans _ (1 / (Z.of_nat (2 * n + 2) # 1)
                            - 1 / (Z.of_nat (2 * m + 2) # 1))).
        -- exact (c3e_l2_inv m n Hnm).
        -- apply c3e_sub_le_self.
           apply (Qlt_le_weak 0 (1 / (Z.of_nat (2 * m + 2) # 1))).
           exact (q_arch_inv_pos (2 * m)).
      * apply c3e_inv_le_inv. lia.
    + exact HN.
Defined.

(* ln2 柯西实数投影（定义性） *)
Lemma c3e_ln2_proj : forall k : nat, projT1 c3e_ln2_real k == c3e_l2_sum k.
Proof. intro k. exact (Qeq_refl (projT1 c3e_ln2_real k)). Qed.

(* ln2 子件：经母定理导出（proof 即 c3e_env_mother 实例，禁平行抄写） *)
Theorem c3e_env_ln2 : forall n : nat,
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo) c3e_ln2_real)
        (And (real_le_b c3e_ln2_real (real_const hi))
             (QeqT (hi - lo) (2 * (1 / (Z.of_nat (2 * n + 2) # 1))))))).
Proof.
  intro n.
  apply (c3e_env_mother c3e_ln2_real (c3e_l2_sum n)
                        (1 / (Z.of_nat (2 * n + 2) # 1)) n).
  intros k Hk.
  exact (c3e_l2_cert n k Hk).
Qed.

(* ============================================================ *)
(* S3. e 子件：消费 exp_tail_abs_geom2 链换 Real 层                  *)
(* ============================================================ *)

(* e 子件：x := e^1 的柯西实数，s n := exp_partial n 1，
   t n := (1^n/n!)·2（exp_tail_abs_geom2 实例化于 A=1，须 n ≥ 1）。
   消费链：exp_tail_abs_le（|tail| ≤ tail_abs）→ exp_tail_abs_geom2
   （S03:622 供体）→ 母定理换 Real 层。 *)
Theorem c3e_env_e : forall n : nat, (1 <= n)%nat ->
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo) (cauchy_real_exp (real_const 1)))
        (And (real_le_b (cauchy_real_exp (real_const 1)) (real_const hi))
             (QeqT (hi - lo) (2 * ((q_pow 1 n / q_fact n) * (1 + 1)%Q)))))).
Proof.
  intros n Hn.
  apply (c3e_env_mother (cauchy_real_exp (real_const 1)) (exp_partial n 1)
                        ((q_pow 1 n / q_fact n) * (1 + 1)%Q) n).
  intros k Hk.
  assert (Hz : exp_partial k 1 - exp_partial n 1 == exp_tail n k 1)
    by (apply exp_partial_diff_tail; exact Hk).
  assert (Habs : Qle (Qabs (exp_tail n k 1))
                     ((q_pow 1 n / q_fact n) * (1 + 1)%Q)).
  { apply (Qle_trans _ (exp_tail_abs n k (Qabs 1))).
    - apply exp_tail_abs_le.
    - apply (Qle_trans _ (exp_tail_abs n k 1)).
      + apply qeq_le. apply (exp_tail_abs_wd n k (Qabs 1) 1). reflexivity.
      + apply (exp_tail_abs_geom2 1 n k).
        * unfold Qle; simpl; lia.
        * intros t Ht. unfold Qle; simpl; lia.
        * exact Hk. }
  destruct (c3e_abs_two (exp_tail n k 1)
                        ((q_pow 1 n / q_fact n) * (1 + 1)%Q) Habs)
    as [Hzlo Hzhi].
  split.
  - (* exp_partial n 1 − t ≤ exp_partial k 1 ⟸ 0 ≤ z + t *)
    rewrite (exp_const_proj 1 k).
    apply (proj2 (Qle_minus_iff (exp_partial n 1 - (q_pow 1 n / q_fact n) * (1 + 1)%Q)
                                (exp_partial k 1))).
    setoid_replace (exp_partial k 1
                    - (exp_partial n 1 - (q_pow 1 n / q_fact n) * (1 + 1)%Q))
      with (exp_tail n k 1 + (q_pow 1 n / q_fact n) * (1 + 1)%Q).
    + exact Hzlo.
    + rewrite <- Hz. ring.
  - (* exp_partial k 1 ≤ exp_partial n 1 + t ⟸ 0 ≤ t − z *)
    rewrite (exp_const_proj 1 k).
    apply (proj2 (Qle_minus_iff (exp_partial k 1)
                                (exp_partial n 1
                                 + (q_pow 1 n / q_fact n) * (1 + 1)%Q))).
    setoid_replace (exp_partial n 1 + (q_pow 1 n / q_fact n) * (1 + 1)%Q
                    - exp_partial k 1)
      with ((q_pow 1 n / q_fact n) * (1 + 1)%Q - exp_tail n k 1).
    + exact Hzhi.
    + rewrite <- Hz. ring.
Qed.

(* ============================================================ *)
(* S4. π 子件：消费 sc_lp_odd_diff_bound 级数尾换 Real 层             *)
(* ============================================================ *)

(* π 子件：x := π_L = Cauchy(4·lp_odd)，s n := 4·lp_odd n（即 π_L 自身
   投影，real_pi_leibniz_proj），t n := 4·lp_a(2n+2) = 4/(4n+5)
   （sc_lp_odd_diff_bound 级数尾 × 4）。 *)
Theorem c3e_env_pi : forall n : nat,
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo) cauchy_real_pi_leibniz)
        (And (real_le_b cauchy_real_pi_leibniz (real_const hi))
             (QeqT (hi - lo) (2 * (lp_four * lp_a (2 * n + 2))))))).
Proof.
  intro n.
  apply (c3e_env_mother cauchy_real_pi_leibniz (lp_four * lp_odd n)
                        (lp_four * lp_a (2 * n + 2)) n).
  intros k Hk.
  split.
  - (* 4·lp_odd n − 4·tail ≤ 4·lp_odd k *)
    rewrite (real_pi_leibniz_proj k).
    apply (Qle_trans _ (lp_four * lp_odd n)).
    + apply (proj2 (Qle_minus_iff (lp_four * lp_odd n - lp_four * lp_a (2 * n + 2))
                                  (lp_four * lp_odd n))).
      setoid_replace (lp_four * lp_odd n
                      - (lp_four * lp_odd n - lp_four * lp_a (2 * n + 2)))
        with (lp_four * lp_a (2 * n + 2)) by ring.
      apply (Qle_trans _ (0 * lp_a (2 * n + 2))).
      * setoid_replace (0 * lp_a (2 * n + 2)) with 0 by ring. apply Qle_refl.
      * apply (Qmult_le_compat_r 0 lp_four (lp_a (2 * n + 2))).
        -- apply sc_lp_four_nonneg.
        -- apply sc_lpa_nonneg.
    + setoid_replace (lp_four * lp_odd n) with (lp_odd n * lp_four) by ring.
      setoid_replace (lp_four * lp_odd k) with (lp_odd k * lp_four) by ring.
      apply (Qmult_le_compat_r (lp_odd n) (lp_odd k) lp_four).
      * apply sc_lp_odd_chain. exact Hk.
      * apply sc_lp_four_nonneg.
  - (* 4·lp_odd k ≤ 4·lp_odd n + 4·tail *)
    rewrite (real_pi_leibniz_proj k).
    setoid_replace (lp_four * lp_odd k) with (lp_odd k * lp_four) by ring.
    setoid_replace (lp_four * lp_odd n + lp_four * lp_a (2 * n + 2))
      with ((lp_odd n + lp_a (2 * n + 2)) * lp_four) by ring.
    apply (Qmult_le_compat_r (lp_odd k) (lp_odd n + lp_a (2 * n + 2)) lp_four).
    + apply (proj2 (Qle_minus_iff (lp_odd k) (lp_odd n + lp_a (2 * n + 2)))).
      setoid_replace (lp_odd n + lp_a (2 * n + 2) - lp_odd k)
        with (lp_a (2 * n + 2) - (lp_odd k - lp_odd n)) by ring.
      exact (proj1 (Qle_minus_iff (lp_odd k - lp_odd n) (lp_a (2 * n + 2)))
                   (sc_lp_odd_diff_bound n k Hk)).
    + apply sc_lp_four_nonneg.
Qed.

(* ============================================================ *)
(* S5. G3 速率：模量线性族 N_c(eps) 形（论文 3 §10.5 接口对齐）        *)
(* ============================================================ *)

(* 通率：tail n ≤ c/(n+1)、c > 0 ⟹ ∀eps>0 ∃N=⌈c/eps⌉+1 形模量，
   n ≥ N ⟹ 2·tail n < eps（q_arch_inv 的 N 即 ceiling 构造位） *)
Theorem c3e_env_rate : forall (tail : nat -> Q) (c : Q),
  Qlt 0 c ->
  (forall n : nat, Qle (2 * tail n) (c / (Z.of_nat (n + 1) # 1))) ->
  forall eps : Q, Qlt 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qlt (2 * tail n) eps).
Proof.
  intros tail c Hc Hrate eps Heps.
  assert (Hec : Qlt 0 (eps / c)).
  { unfold Qdiv.
    apply (Qmult_lt_0_compat eps (Qinv c)).
    - exact Heps.
    - apply Qinv_lt_0_compat. exact Hc. }
  destruct (q_arch_inv (eps / c) Hec) as [N HN].
  exists (Datatypes.S N). intros n Hn.
  apply (Qle_lt_trans _ (c / (Z.of_nat (N + 2) # 1))).
  - apply (Qle_trans _ (c / (Z.of_nat (n + 1) # 1))).
    + apply Hrate.
    + apply (q_le_div_le c (Z.of_nat (n + 1) # 1) c (Z.of_nat (N + 2) # 1)).
      * unfold Qlt; simpl; lia.
      * unfold Qlt; simpl; lia.
      * setoid_replace (c * (Z.of_nat (N + 2) # 1))
          with ((Z.of_nat (N + 2) # 1) * c) by ring.
        setoid_replace (c * (Z.of_nat (n + 1) # 1))
          with ((Z.of_nat (n + 1) # 1) * c) by ring.
        apply (Qmult_le_compat_r (Z.of_nat (N + 2) # 1) (Z.of_nat (n + 1) # 1) c).
        -- unfold Qle; simpl; lia.
        -- apply (Qlt_le_weak 0 c). exact Hc.
  - (* c/(N+2) < eps：1/(N+2) < eps/c 乘 c > 0 *)
    assert (Hw : c / (Z.of_nat (N + 2) # 1) == (1 / (Z.of_nat (N + 2) # 1)) * c).
    { field. intro Hz.
      apply (Qlt_not_eq 0 (Z.of_nat (N + 2) # 1)).
      - unfold Qlt; simpl; lia.
      - apply Qeq_sym. exact Hz. }
    assert (He : eps == (eps / c) * c).
    { field. intro Hz. apply (Qlt_not_eq 0 c Hc). exact (Qeq_sym _ _ Hz). }
    rewrite Hw. rewrite He.
    apply (Qmult_lt_compat_r (1 / (Z.of_nat (N + 2) # 1)) (eps / c) c Hc HN).
Qed.

(* a·(1/X) == a/X（Qdiv 展开一步；绕开 field 旁证坑） *)
Lemma c3e_mul_inv_div : forall (a X : Q), a * (1 / X) == a / X.
Proof.
  intros a X. unfold Qdiv. rewrite Qmult_1_l. reflexivity.
Qed.

(* ln2 速率实例：宽度 2·tail n == 1/(n+1) 形（c := 2 线性族，注入上界
   2·(1/(2n+2)) ≤ 2/(n+1) 由 q_le_div_le 直给） *)
Theorem c3e_env_rate_ln2 : forall eps : Q, Qlt 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qlt (2 * (1 / (Z.of_nat (2 * n + 2) # 1))) eps).
Proof.
  intros eps Heps.
  apply (c3e_env_rate (fun v => 1 / (Z.of_nat (2 * v + 2) # 1)) 2).
  - unfold Qlt; simpl; lia.
  - intro n.
    setoid_replace (2 * (1 / (Z.of_nat (2 * n + 2) # 1)))
      with (2 / (Z.of_nat (2 * n + 2) # 1)) by (apply c3e_mul_inv_div).
    apply (q_le_div_le 2 (Z.of_nat (2 * n + 2) # 1) 2 (Z.of_nat (n + 1) # 1)).
    * unfold Qlt; simpl; lia.
    * unfold Qlt; simpl; lia.
    * setoid_replace (2 * (Z.of_nat (n + 1) # 1))
        with ((Z.of_nat (n + 1) # 1) * 2) by ring.
      setoid_replace (2 * (Z.of_nat (2 * n + 2) # 1))
        with ((Z.of_nat (2 * n + 2) # 1) * 2) by ring.
      apply (Qmult_le_compat_r (Z.of_nat (n + 1) # 1) (Z.of_nat (2 * n + 2) # 1) 2).
      -- unfold Qle; simpl; lia.
      -- unfold Qle; simpl; lia.
  - exact Heps.
Qed.

(* ============================================================ *)
(* 公理面核验                                                        *)
(* ============================================================ *)

Print Assumptions c3e_env_mother.
Print Assumptions c3e_env_ln2.
Print Assumptions c3e_env_e.
Print Assumptions c3e_env_pi.
Print Assumptions c3e_env_rate.
Print Assumptions c3e_env_rate_ln2.
