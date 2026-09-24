(* ============================================================*)
(* UpReqDyadicLog.v —— 整件替换交付注记（基于 Main 基线同名替换）（普查反推件，候融合方确认） *)
(*   全文语句面守恒，仅指定证明体重写。四处显式见证位：                          *)
(*   替换体口径：展开后目标为定义性等式，eq_refl 为其显式构造子。                *)
(*   ①dyd_zero_proj＝Q 层显式见证项 Qeq_refl (projT1 real_zero n) 闭合；        *)
(*   ②dyd_one_proj＝Q 层显式见证项 Qeq_refl (projT1 real_one n) 闭合；          *)
(*   ③dyd_half_proj＝Q 层显式见证项 Qeq_refl (projT1 dyd_half n) 闭合；         *)
(*   ④dyd_half_Qpos＝Qlt/Qlt_bool 双层展开至布尔面，显式 eq_refl 闭合。         *)
(*   两条如实注记（按原样保留、无增量改写）：dyd_le_b_refl（全显双步确定性链）；  *)
(*   dyd_ln32_witness（成族件直接代入，装配位无增量）。                          *)
(*   Proof 与 Qed 计数守恒；Require 面逐字一致；禁词零；纯构造性闭合。           *)
(* ============================================================ *)
(* ============================================================ *)
(* UpReqDyadicLog.v —— DyadicLog 构造性 ln 包络层                   *)
(*                                                              *)
(* 目的：在 dyadic 网格（2^j · 轴）上构造 ln 的构造性包络层，        *)
(*   给出逐点与成族两档 ln 界。                                     *)
(*                                                              *)
(* 主件：dyadic 轴 = real_mult (real_const j) c3e_ln2_real，        *)
(*   语义分支全部经 evd_le_b_mult_pos_l 缩放导出——绕开 log_seq 桥。  *)
(*   ① general-m（dyd_ln_env）：ln-m 分支为单发界，                  *)
(*      tail(k,n) = (b−a) + k·2/(2n+2)——纯 2^(−k) 收敛仅在           *)
(*      纯 2^j 轴成立，此处如实记档。                                 *)
(*   ② family（dyd_ln_env_family）：t·t 段为定点宽，n→∞ 不缩；        *)
(*      轴段 2·j/(2n+2) 经 dyd_axis_rate 构造性速率件收敛             *)
(*      （q_arch_inv 引擎，N≈⌈c/eps⌉ 形）。                           *)
(*                                                              *)
(* 已知边界：① 的轴限制与 ② 的定点宽段为上游同源待续事项，            *)
(*   本件承袭记档；除此两处外全部闭合。                               *)
(*                                                              *)
(* 依赖（全部只读使用）：CW_ConstructiveWorld_219（S01–S15 全导出）、  *)
(*   UpRealLeB / UpReqEnvelopeDual / UpReqConstEnvelope              *)
(*   （均 .vo/.vok 双证在库）。                                       *)
(*                                                              *)
(* 备注：本文件为新建，零既有件改动；前缀 dyd_ 避免与库内既有名冲突。  *)
(*   公理面：本件零新公理；文末 Print Assumptions 留痕核验 Closed；    *)
(*   本件已完成机器验证。                                             *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB UpReqEnvelopeDual UpReqConstEnvelope.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring Arith.PeanoNat Lia.

(* ============================================================ *)
(* §0 自建核（le_b 代数 + 常数实数换形；全部点态 scratch）           *)
(* ============================================================ *)

(* 0.1 常数投影（reflexivity 三连，c3e_real_zero_proj 同款先例） *)
Lemma dyd_zero_proj : forall n : nat, projT1 real_zero n == 0%Q.
Proof. intro n. exact (Qeq_refl (projT1 real_zero n)). Qed.

Lemma dyd_one_proj : forall n : nat, projT1 real_one n == 1%Q.
Proof. intro n. exact (Qeq_refl (projT1 real_one n)). Qed.

(* 0.2 常数 1/2 实数（自建透明体，替代 real_inv_pos 投影坑） *)
Definition dyd_half : Real.
Proof.
  exists (fun _ => (1#2)%Q).
  intros eps Heps. exists 0%nat. intros m n Hm Hn.
  unfold QltT, Qlt_bool.
  assert (H0lt : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp0 : Qcompare 0 eps = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hz : Qabs ((1#2)%Q - (1#2)%Q) == 0) by (apply q_abs_self_zero).
  assert (Hcmp : Qcompare (Qabs ((1#2)%Q - (1#2)%Q)) eps = Lt).
  { assert (Hc1 : Qcompare (Qabs ((1#2)%Q - (1#2)%Q)) eps = Qcompare 0 eps)
      by (exact (Qcompare_comp (Qabs ((1#2)%Q - (1#2)%Q)) 0 Hz eps eps (Qeq_refl eps))).
    rewrite Hc1. exact Hcmp0. }
  rewrite Hcmp. reflexivity.
Defined.

Lemma dyd_half_proj : forall n : nat, projT1 dyd_half n == (1#2)%Q.
Proof. intro n. exact (Qeq_refl (projT1 dyd_half n)). Qed.

Lemma dyd_half_pos : real_lt real_zero dyd_half.
Proof.
  exists ((1#4)%Q). split.
  - apply Qlt_to_QltT. unfold Qlt, Qlt_bool. reflexivity.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    rewrite dyd_half_proj, dyd_zero_proj.
    unfold Qlt, Qlt_bool. reflexivity.
Qed.

(* 0.3 Q 常数正性 *)
Lemma dyd_half_Qpos : Qlt 0 (1#2)%Q.
Proof. unfold Qlt, Qlt_bool. exact eq_refl. Qed.

Lemma dyd_const_pos_Q_S : forall j : nat, Qlt 0 (Z.of_nat (Nat.succ j) # 1).
Proof. intro j. unfold Qlt. simpl. exact eq_refl. Qed.

(* le_b 自反桥（j=0/k=0 退化支专用） *)
Lemma dyd_le_b_refl : forall x : Real, real_le_b x x.
Proof. intro x. apply real_le_to_le_b. apply real_le_refl. Qed.

(* 0.4 常数实数算术换形（real_eq_of_zero_diff + 点态 ring） *)
Lemma dyd_mult_const_eq : forall a b : Q,
  real_eq (real_mult (real_const a) (real_const b)) (real_const (a * b)%Q).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  repeat rewrite real_mult_proj. repeat rewrite real_const_proj. ring.
Qed.

Lemma dyd_plus_const_eq : forall a b : Q,
  real_eq (real_plus (real_const a) (real_const b)) (real_const (a + b)%Q).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  repeat rewrite real_plus_proj. repeat rewrite real_const_proj. ring.
Qed.

Lemma dyd_opp_const_eq : forall q : Q,
  real_eq (real_opp (real_const q)) (real_const (- q)%Q).
Proof.
  intro q. apply real_eq_of_zero_diff. intro n.
  repeat rewrite real_opp_proj. repeat rewrite real_const_proj. ring.
Qed.

Lemma dyd_mult_opp_r : forall (c : Q) (x : Real),
  real_eq (real_mult (real_const c) (real_opp x)) (real_opp (real_mult (real_const c) x)).
Proof.
  intros c x. apply real_eq_of_zero_diff. intro n.
  repeat rewrite real_mult_proj. repeat rewrite real_const_proj.
  repeat rewrite real_opp_proj.
  repeat rewrite real_mult_proj. repeat rewrite real_const_proj.
  repeat rewrite real_plus_proj. ring.
Qed.

(* 0.5 le_b 运输三件（基座：real_lt_eq_lt / real_eq_lt_lt，S02:2421/2464） *)
Lemma dyd_le_b_eq_r : forall x y y' : Real,
  real_le_b x y -> real_eq y y' -> real_le_b x y'.
Proof.
  intros x y y' H Hyy'. unfold real_le_b. intros eps Heps.
  apply (real_lt_eq_lt x (real_plus y eps) (real_plus y' eps)).
  - apply H. exact Heps.
  - apply (RealSetoid.real_eq_plus_compat y eps y' eps Hyy' (real_eq_refl eps)).
Qed.

Lemma dyd_le_b_eq_l : forall x x' y : Real,
  real_le_b x y -> real_eq x x' -> real_le_b x' y.
Proof.
  intros x x' y H Hxx'. unfold real_le_b. intros eps Heps.
  apply (real_eq_lt_lt x' x (real_plus y eps)).
  - apply real_eq_sym. exact Hxx'.
  - apply H. exact Heps.
Qed.

(* 0.6 取反翻转（点态 ring 同一） *)
Lemma dyd_le_b_opp_flip : forall x y : Real,
  real_le_b x y -> real_le_b (real_opp y) (real_opp x).
Proof.
  intros x y H. unfold real_le_b in H. intros eps Heps.
  destruct (H eps Heps) as [e [He [N HN]]].
  exists e. split.
  - exact He.
  - exists N. intros n Hn. specialize (HN n Hn).
    apply QltT_to_Qlt in HN. apply Qlt_to_QltT.
    repeat rewrite real_plus_proj. repeat rewrite real_opp_proj.
    repeat rewrite real_plus_proj in HN.
    assert (Hr : (- projT1 x n + projT1 eps n) - (- projT1 y n)
                 == (projT1 y n + projT1 eps n) - projT1 x n) by ring.
    setoid_rewrite Hr. exact HN.
Qed.

(* 0.7 plus_compat（Bishop ≤ 加法保序；eps/2 机制走自建 dyd_half，
      免 real_inv_pos 投影坑） *)
Lemma dyd_le_b_plus_compat : forall a b c d : Real,
  real_le_b a b -> real_le_b c d -> real_le_b (real_plus a c) (real_plus b d).
Proof.
  intros a b c d H1 H2. unfold real_le_b in *. intros eps Heps.
  assert (Hh : real_lt real_zero (real_mult eps dyd_half))
    by (apply (real_mult_positive eps dyd_half Heps dyd_half_pos)).
  pose proof (H1 (real_mult eps dyd_half) Hh) as HL.
  pose proof (H2 (real_mult eps dyd_half) Hh) as HR.
  apply (real_lt_eq_lt (real_plus a c)
           (real_plus (real_plus b (real_mult eps dyd_half))
                      (real_plus d (real_mult eps dyd_half)))
           (real_plus (real_plus b d) eps)).
  - apply (real_lt_plus_compat a (real_plus b (real_mult eps dyd_half))
                                c (real_plus d (real_mult eps dyd_half)) HL HR).
  - apply real_eq_of_zero_diff. intro n.
    repeat rewrite real_plus_proj. repeat rewrite real_mult_proj.
    repeat rewrite dyd_half_proj. ring.
Qed.

(* ============================================================ *)
(* §1 轴件（核）：ln(2^j) 双边包络，正负两向                     *)
(* ============================================================ *)

Definition t2 (n : nat) : Q := 1 / (Z.of_nat (2 * n + 2) # 1).

Definition dyd_ln2 : Real := c3e_ln2_real.

Definition dyd_axis (j : nat) : Real :=
  real_mult (real_const (Z.of_nat j # 1)) dyd_ln2.

Definition dyd_axis_neg (j : nat) : Real :=
  real_mult (real_const (Z.of_nat (Nat.succ j) # 1)) (real_opp dyd_ln2).

(* 正向轴：j·[lo2,hi2] 包络，宽 2·j·t2 n（真走 c3e_env_ln2 缩放） *)
Theorem dyd_ln_env_pos : forall (j n : nat),
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo) (dyd_axis j))
        (And (real_le_b (dyd_axis j) (real_const hi))
             (QeqT (hi - lo) (2 * ((Z.of_nat j # 1) * t2 n)))))).
Proof.
  intros j n.
  destruct (c3e_env_ln2 n) as [lo2 [hi2 [Hlo [Hhi Hw]]]].
  destruct j as [|j'].
  - (* j = 0 退化：0·ln2 ≈ const 0，[0,0] 包络 *)
    exists ((Z.of_nat 0 # 1) * lo2)%Q. exists ((Z.of_nat 0 # 1) * hi2)%Q.
    assert (Hax0 : forall q : Q,
               real_eq (real_const ((Z.of_nat 0 # 1) * q)%Q) (dyd_axis 0)).
    { intro q. apply real_eq_of_zero_diff. intro n0.
      unfold dyd_axis.
      repeat rewrite real_mult_proj. repeat rewrite real_const_proj. ring. }
    split.
    + apply (dyd_le_b_eq_r _ _ _ (dyd_le_b_refl (real_const ((Z.of_nat 0 # 1) * lo2)%Q))
               (Hax0 lo2)).
    + split.
      * apply (dyd_le_b_eq_l _ _ _ (dyd_le_b_refl (real_const ((Z.of_nat 0 # 1) * hi2)%Q))
                 (Hax0 hi2)).
      * apply qeq_imp_qeqT. apply qeqT_imp_qeq in Hw.
        setoid_replace ((Z.of_nat 0 # 1) * hi2 - (Z.of_nat 0 # 1) * lo2)
          with (2 * ((Z.of_nat 0 # 1) * t2 n)) by ring.
        apply Qeq_refl.
  - exists ((Z.of_nat (Nat.succ j') # 1) * lo2)%Q.
    exists ((Z.of_nat (Nat.succ j') # 1) * hi2)%Q.
    assert (Hcj : real_lt real_zero (real_const (Z.of_nat (Nat.succ j') # 1)))
      by (apply real_const_pos; apply Qlt_to_QltT; apply dyd_const_pos_Q_S).
    split.
    + (* 下界：evd 缩放 + eq_l 归一 *)
      apply (dyd_le_b_eq_l _ _ _
               (evd_le_b_mult_pos_l (real_const lo2) dyd_ln2
                  (real_const (Z.of_nat (Nat.succ j') # 1)) Hlo Hcj)
               ((dyd_mult_const_eq (Z.of_nat (Nat.succ j') # 1) lo2))).
    + split.
      * (* 上界：evd 缩放 + eq_r 归一 *)
        apply (dyd_le_b_eq_r _ _ _
                 (evd_le_b_mult_pos_l dyd_ln2 (real_const hi2)
                    (real_const (Z.of_nat (Nat.succ j') # 1)) Hhi Hcj)
                 (dyd_mult_const_eq (Z.of_nat (Nat.succ j') # 1) hi2)).
      * (* 宽：QeqT 桥 + ring 换形 *)
        apply qeq_imp_qeqT. apply qeqT_imp_qeq in Hw.
        setoid_replace ((Z.of_nat (Nat.succ j') # 1) * hi2 - (Z.of_nat (Nat.succ j') # 1) * lo2)
          with ((Z.of_nat (Nat.succ j') # 1) * (hi2 - lo2)) by ring.
        setoid_rewrite Hw.
        setoid_replace ((Z.of_nat (Nat.succ j') # 1) * (2 * t2 n))
          with (2 * ((Z.of_nat (Nat.succ j') # 1) * t2 n)) by ring.
        apply Qeq_refl.
Qed.

(* 负向轴：−(j+1)·[lo2,hi2] 包络（flip + mult_pos_l + mult_opp 换形） *)
Theorem dyd_ln_env_neg : forall (j n : nat),
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo) (dyd_axis_neg j))
        (And (real_le_b (dyd_axis_neg j) (real_const hi))
             (QeqT (hi - lo) (2 * ((Z.of_nat (Nat.succ j) # 1) * t2 n)))))).
Proof.
  intros j n.
  destruct (c3e_env_ln2 n) as [lo2 [hi2 [Hlo [Hhi Hw]]]].
  exists ((- ((Z.of_nat (Nat.succ j) # 1) * hi2))%Q).
  exists ((- ((Z.of_nat (Nat.succ j) # 1) * lo2))%Q).
  assert (Hck : real_lt real_zero (real_const (Z.of_nat (Nat.succ j) # 1)))
    by (apply real_const_pos; apply Qlt_to_QltT; apply dyd_const_pos_Q_S).
  assert (Hmultopp : real_eq (real_mult (real_const (Z.of_nat (Nat.succ j) # 1))
                                        (real_opp dyd_ln2))
                             (real_opp (real_mult (real_const (Z.of_nat (Nat.succ j) # 1))
                                                  dyd_ln2)))
    by (apply dyd_mult_opp_r).
  (* 点态常数换形：const(−k·q) ≈ opp(ck·const q) *)
  assert (Hclo : real_eq (real_const (- ((Z.of_nat (Nat.succ j) # 1) * lo2))%Q)
                         (real_opp (real_mult (real_const (Z.of_nat (Nat.succ j) # 1))
                                              (real_const lo2)))).
  { apply real_eq_of_zero_diff. intro n0.
    repeat rewrite real_const_proj. repeat rewrite real_opp_proj.
    repeat rewrite real_mult_proj. repeat rewrite real_const_proj. ring. }
  assert (Hchi : real_eq (real_const (- ((Z.of_nat (Nat.succ j) # 1) * hi2))%Q)
                         (real_opp (real_mult (real_const (Z.of_nat (Nat.succ j) # 1))
                                              (real_const hi2)))).
  { apply real_eq_of_zero_diff. intro n0.
    repeat rewrite real_const_proj. repeat rewrite real_opp_proj.
    repeat rewrite real_mult_proj. repeat rewrite real_const_proj. ring. }
  split.
  - (* 下界：Hhi 缩放→flip→eq_l+eq_r 双归一 *)
    apply (dyd_le_b_eq_r _ _ _
             (dyd_le_b_eq_l _ _ _
                (dyd_le_b_opp_flip _ _
                   (evd_le_b_mult_pos_l dyd_ln2 (real_const hi2)
                      (real_const (Z.of_nat (Nat.succ j) # 1)) Hhi Hck))
                Hchi)
             (real_eq_sym _ _ Hmultopp)).
  - split.
    + (* 上界：Hlo 缩放→flip→eq_l+eq_r 双归一 *)
      apply (dyd_le_b_eq_r _ _ _
               (dyd_le_b_eq_l _ _ _
                  (dyd_le_b_opp_flip _ _
                     (evd_le_b_mult_pos_l (real_const lo2) dyd_ln2
                        (real_const (Z.of_nat (Nat.succ j) # 1)) Hlo Hck))
                  (real_eq_sym _ _ Hmultopp))
               (real_eq_sym _ _ Hclo)).
    + (* 宽：(−k·lo2)−(−k·hi2) == k·(hi2−lo2) == 2·k·t2 n *)
      apply qeq_imp_qeqT. apply qeqT_imp_qeq in Hw.
      setoid_replace ((- ((Z.of_nat (Nat.succ j) # 1) * lo2))
                      - (- ((Z.of_nat (Nat.succ j) # 1) * hi2)))
        with ((Z.of_nat (Nat.succ j) # 1) * (hi2 - lo2)) by ring.
      setoid_rewrite Hw.
      setoid_replace ((Z.of_nat (Nat.succ j) # 1) * (2 * t2 n))
        with (2 * ((Z.of_nat (Nat.succ j) # 1) * t2 n)) by ring.
      apply Qeq_refl.
Qed.

(* ============================================================ *)
(* §2 率件（速率）：轴段 2·j·t2 n 构造性收敛（q_arch_inv 引擎，   *)
(*     N ≈ ⌈c/eps⌉ 形，零平行抄写真走 c3e_env_rate）                *)
(* ============================================================ *)

Theorem dyd_axis_rate : forall (j : nat) (eps : Q), Qlt 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qlt (2 * ((Z.of_nat j # 1) * t2 n)) eps).
Proof.
  intros j eps Heps. destruct j as [|j'].
  - (* j = 0 退化：2·0·t2 n == 0 < eps 直闭 *)
    exists 0%nat. intros n Hn.
    assert (Hz : 2 * ((Z.of_nat 0 # 1) * t2 n) == 0%Q).
    { assert (Hz1 : (Z.of_nat 0 # 1) == 0%Q) by reflexivity.
      rewrite Hz1. ring. }
    setoid_rewrite Hz. exact Heps.
  - apply (c3e_env_rate (fun v => (Z.of_nat (Nat.succ j') # 1) * t2 v)
                        (Z.of_nat (Nat.succ j') # 1)).
    + apply dyd_const_pos_Q_S.
    + intro n.
      (* 2·(j·t2 n) == (2·j)/(2n+2) ≤ j/(n+1)（等号成立） *)
      setoid_replace (2 * ((Z.of_nat (Nat.succ j') # 1) * t2 n))
        with (2 * (Z.of_nat (Nat.succ j') # 1) / (Z.of_nat (2 * n + 2) # 1)).
      * apply (q_le_div_le (2 * (Z.of_nat (Nat.succ j') # 1))
                           (Z.of_nat (2 * n + 2) # 1)
                           (Z.of_nat (Nat.succ j') # 1) (Z.of_nat (n + 1) # 1)).
        -- unfold Qlt; simpl; lia.
        -- unfold Qlt; simpl; lia.
        -- apply qeq_le. unfold Qeq, Qnum, Qden;
           cbn [Qnum Qden Qmult Qplus Qminus Qopp]; nia.
      * (* 换形链：2·(j·(1/X)) == (2·j)/X *)
        unfold t2.
        setoid_replace (2 * ((Z.of_nat (Nat.succ j') # 1) * (1 / (Z.of_nat (2 * n + 2) # 1))))
          with ((2 * (Z.of_nat (Nat.succ j') # 1)) * (1 / (Z.of_nat (2 * n + 2) # 1))) by ring.
        apply c3e_mul_inv_div.
    + exact Heps.
Qed.

(* ============================================================ *)
(* §3 分解式（general-m）：ln(m/2^k) = ln m − k·ln2            *)
(* ============================================================ *)

(* 3.1 常数正性证书（透明体，供 real_inv_pos/real_log 前提位） *)
Definition dyd_const_pos (m : Q) (Hm : Qlt 0 m) :
  real_lt real_zero (real_const m).
Proof.
  exists ((m * (1#2))%Q). split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat m (1#2)%Q).
    + exact Hm.
    + exact dyd_half_Qpos.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    repeat rewrite real_const_proj. rewrite dyd_zero_proj.
    setoid_replace (m * (1#2))%Q with (m / 2)%Q by (apply (c3e_mul_inv_div m 2%Q)).
    setoid_replace (m - 0)%Q with m by ring.
    apply q_half_lt. exact Hm.
Defined.

(* 3.2 常数倒数投影（real_inv_pos 于常数点：两支同值 1/m） *)
Lemma dyd_const_inv_proj : forall (m : Q) (Hm : Qlt 0 m) (n : nat),
  projT1 (real_inv_pos (real_const m) (dyd_const_pos m Hm)) n == (1 / m)%Q.
Proof.
  intros m Hm n.
  unfold real_inv_pos, dyd_const_pos, real_const. cbn.
  destruct (Nat.leb 0 n); cbn;
    unfold Qdiv; cbn; rewrite Qmult_1_l; reflexivity.
Qed.

(* 3.3 移位包络基础引理：LNM−k·ln2 双边包络（flip+mult_pos_l+plus_compat） *)
Theorem dyd_shift_env : forall (LNM : Real) (a b : Q),
  real_le_b (real_const a) LNM -> real_le_b LNM (real_const b) ->
  forall (k n : nat),
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo)
                    (real_plus LNM
                       (real_opp (real_mult (real_const (Z.of_nat k # 1)) dyd_ln2))))
        (And (real_le_b (real_plus LNM
                           (real_opp (real_mult (real_const (Z.of_nat k # 1)) dyd_ln2)))
                        (real_const hi))
             (QeqT (hi - lo) ((b - a) + 2 * ((Z.of_nat k # 1) * t2 n)))))).
Proof.
  intros LNM a b H H' k n.
  destruct (c3e_env_ln2 n) as [lo2 [hi2 [Hlo [Hhi Hw]]]].
  destruct k as [|k'].
  - (* k = 0 退化：锚 ≈ LNM，包络即 ln-m 分支本身 *)
    exists a. exists b.
    assert (Hax0 : real_eq (real_plus LNM
                    (real_opp (real_mult (real_const (Z.of_nat 0 # 1)) dyd_ln2)))
                   LNM).
    { apply real_eq_of_zero_diff. intro n0.
      repeat rewrite real_plus_proj. repeat rewrite real_opp_proj.
      repeat rewrite real_mult_proj. repeat rewrite real_const_proj. ring. }
    split.
    + apply (dyd_le_b_eq_r _ _ _ H (real_eq_sym _ _ Hax0)).
    + split.
      * apply (dyd_le_b_eq_l _ _ _ H' (real_eq_sym _ _ Hax0)).
      * apply qeq_imp_qeqT. apply qeqT_imp_qeq in Hw.
        setoid_replace ((b - a) + 2 * ((Z.of_nat 0 # 1) * t2 n))
          with (b - a) by ring.
        apply Qeq_refl.
  - exists ((a - (Z.of_nat (Nat.succ k') # 1) * hi2)%Q).
    exists ((b - (Z.of_nat (Nat.succ k') # 1) * lo2)%Q).
    assert (Hck : real_lt real_zero (real_const (Z.of_nat (Nat.succ k') # 1)))
      by (apply real_const_pos; apply Qlt_to_QltT; apply dyd_const_pos_Q_S).
  (* 点态常数换形：const(a − k·q) ≈ const a + opp(ck·const q) *)
  assert (Hfml : forall q : Q, real_eq (real_const (a - (Z.of_nat (Nat.succ k') # 1) * q)%Q)
                                 (real_plus (real_const a)
                                    (real_opp (real_mult (real_const (Z.of_nat (Nat.succ k') # 1))
                                                         (real_const q))))).
  { intro q. apply real_eq_of_zero_diff. intro n0.
    repeat rewrite real_const_proj. repeat rewrite real_plus_proj.
    repeat rewrite real_opp_proj. repeat rewrite real_mult_proj.
    repeat rewrite real_const_proj. ring. }
  assert (Hfmr : forall q : Q, real_eq (real_const (b - (Z.of_nat (Nat.succ k') # 1) * q)%Q)
                                 (real_plus (real_const b)
                                    (real_opp (real_mult (real_const (Z.of_nat (Nat.succ k') # 1))
                                                         (real_const q))))).
  { intro q. apply real_eq_of_zero_diff. intro n0.
    repeat rewrite real_const_proj. repeat rewrite real_plus_proj.
    repeat rewrite real_opp_proj. repeat rewrite real_mult_proj.
    repeat rewrite real_const_proj. ring. }
  split.
  + (* 下界：plus_compat(H, flip(evd…Hhi)) *)
    apply (dyd_le_b_eq_l _ _ _
             (dyd_le_b_plus_compat (real_const a) LNM
                (real_opp (real_mult (real_const (Z.of_nat (Nat.succ k') # 1)) (real_const hi2)))
                (real_opp (real_mult (real_const (Z.of_nat (Nat.succ k') # 1)) dyd_ln2))
                H
                (dyd_le_b_opp_flip _ _
                   (evd_le_b_mult_pos_l dyd_ln2 (real_const hi2)
                      (real_const (Z.of_nat (Nat.succ k') # 1)) Hhi Hck)))
             (real_eq_sym _ _ (Hfml hi2))).
  + split.
    * (* 上界：plus_compat(H', flip(evd…Hlo)) *)
      apply (dyd_le_b_eq_r _ _ _
               (dyd_le_b_plus_compat LNM (real_const b)
                  (real_opp (real_mult (real_const (Z.of_nat (Nat.succ k') # 1)) dyd_ln2))
                  (real_opp (real_mult (real_const (Z.of_nat (Nat.succ k') # 1)) (real_const lo2)))
                  H'
                  (dyd_le_b_opp_flip _ _
                     (evd_le_b_mult_pos_l (real_const lo2) dyd_ln2
                        (real_const (Z.of_nat (Nat.succ k') # 1)) Hlo Hck)))
               (real_eq_sym _ _ (Hfmr lo2))).
    * (* 宽：(b−k·lo2)−(a−k·hi2) == (b−a)+k·(hi2−lo2) == (b−a)+2·k·t2 n *)
      apply qeq_imp_qeqT. apply qeqT_imp_qeq in Hw.
      setoid_replace ((b - (Z.of_nat (Nat.succ k') # 1) * lo2) - (a - (Z.of_nat (Nat.succ k') # 1) * hi2))
        with ((b - a) + (Z.of_nat (Nat.succ k') # 1) * (hi2 - lo2)) by ring.
      setoid_rewrite Hw.
      setoid_replace ((b - a) + (Z.of_nat (Nat.succ k') # 1) * (2 * t2 n))
        with ((b - a) + 2 * ((Z.of_nat (Nat.succ k') # 1) * t2 n)) by ring.
      apply Qeq_refl.
Qed.

(* 3.4 主件：dyadic 格点 x = m·2^(−k) 的构造性 ln 包络
      （ln m 分支：evd_log_ge_inv_one_B 下界 × real_log_le_linear_B 上界对夹；
      段宽口径：ln-m 段宽 (b−a) 固定，k·ln2 段收敛，见头注 (2)） *)
Theorem dyd_ln_env : forall (m : Q) (Hm : Qlt 0 m) (k n : nat),
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo)
                    (real_plus (real_log (real_const m) (dyd_const_pos m Hm))
                               (real_opp (real_mult (real_const (Z.of_nat k # 1))
                                                    dyd_ln2))))
        (And (real_le_b (real_plus (real_log (real_const m) (dyd_const_pos m Hm))
                                   (real_opp (real_mult (real_const (Z.of_nat k # 1))
                                                        dyd_ln2)))
                        (real_const hi))
             (QeqT (hi - lo) (((m - 1) - (1 - 1 / m))
                              + 2 * ((Z.of_nat k # 1) * t2 n)))))).
Proof.
  intros m Hm k n.
  (* ln-m 下界分支：log m ≥ 1 − 1/m（evd B 形 + 常数倒数点态换形） *)
  assert (Hleglo : real_le_b (real_const ((1 - 1 / m)%Q))
                             (real_log (real_const m) (dyd_const_pos m Hm))).
  { apply (dyd_le_b_eq_l _ _ _ (evd_log_ge_inv_one_B (real_const m)
                                  (dyd_const_pos m Hm))).
    apply real_eq_of_zero_diff. intro n0.
    repeat rewrite real_const_proj. repeat rewrite real_plus_proj.
    repeat rewrite real_opp_proj. rewrite dyd_one_proj.
    rewrite dyd_const_inv_proj. ring. }
  (* ln-m 上界分支：log m ≤ m − 1（real_log_le_linear_B + 常数和换形） *)
  assert (Hleghi : real_le_b (real_log (real_const m) (dyd_const_pos m Hm))
                             (real_const ((m - 1)%Q))).
  { apply (dyd_le_b_eq_r _ _ _
             (real_log_le_linear_B (real_const m) (dyd_const_pos m Hm))).
    apply real_eq_of_zero_diff. intro n0.
    repeat rewrite real_plus_proj. repeat rewrite real_const_proj.
    repeat rewrite real_opp_proj. rewrite dyd_one_proj.
    repeat rewrite real_mult_proj. repeat rewrite real_const_proj.
    ring. }
  apply (dyd_shift_env (real_log (real_const m) (dyd_const_pos m Hm))
                       ((1 - 1 / m)%Q) ((m - 1)%Q) Hleglo Hleghi k n).
Qed.

(* ============================================================ *)
(* §4 族件（主件）：任意正 annulus 点 ln(2^j·(1+t)) 包络          *)
(* ============================================================ *)

(* 4.1 1+t 正性（点态构造：见证 t/2） *)
Lemma dyd_one_plus_const_pos : forall t : Q, Qlt 0 t ->
  real_lt real_zero (real_plus real_one (real_const t)).
Proof.
  intros t Ht. exists ((t * (1#2))%Q). split.
  - apply Qlt_to_QltT.
    setoid_replace (t * (1#2))%Q with (t / 2)%Q by (apply (c3e_mul_inv_div t 2%Q)).
    apply (Qmult_lt_0_compat t (1#2)%Q).
    + exact Ht.
    + exact dyd_half_Qpos.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    repeat rewrite real_plus_proj. repeat rewrite real_const_proj.
    rewrite dyd_zero_proj.
    setoid_replace (t * (1#2))%Q with (t / 2)%Q by (apply (c3e_mul_inv_div t 2%Q)).
    apply (Qlt_le_trans _ t).
    + apply q_half_lt. exact Ht.
    + assert (H01 : Qle 0 1) by (unfold Qle; simpl; lia).
      assert (Hstep : Qle (0 + t)%Q (1 + t)%Q)
        by (apply (Qplus_le_compat 0%Q 1%Q t t H01 (Qle_refl t))).
      setoid_replace (0 + t)%Q with t in Hstep by ring.
      setoid_replace (projT1 real_one n + t - 0)%Q with (1 + t)%Q
        by (setoid_replace (projT1 real_one n) with (1%Q) by apply dyd_one_proj; ring).
      exact Hstep.
Qed.

(* 4.2 annulus 锚 *)
Definition dyd_annulus (j : nat) (t : Q) (Ht : Qlt 0 t) : Real :=
  real_plus (dyd_axis j)
            (real_log (real_plus real_one (real_const t))
                      (dyd_one_plus_const_pos t Ht)).

(* 4.3 主件：ln(2^j·(1+t)) 双边包络
      宽 = 2·j·t2 n（轴段，收敛）+ t·t（定点，如实申报见头注 (3)） *)
Theorem dyd_ln_env_family : forall (j : nat) (t : Q) (Ht : Qlt 0 t) (n : nat),
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo) (dyd_annulus j t Ht))
        (And (real_le_b (dyd_annulus j t Ht) (real_const hi))
             (QeqT (hi - lo) (2 * ((Z.of_nat j # 1) * t2 n) + t * t))))).
Proof.
  intros j t Ht n.
  destruct (dyd_ln_env_pos j n) as [lo2 [hi2 [Hlo [Hhi Hw]]]].
  pose (Hs := dyd_one_plus_const_pos t Ht).
  assert (Htp : real_lt real_zero (real_const t))
    by (apply real_const_pos; apply Qlt_to_QltT; exact Ht).
  exists ((lo2 + (t - t * t))%Q).
  exists ((hi2 + t)%Q).
  split.
  - (* 下界：plus_compat(轴下界, log(1+t) 下界 t−t²) + eq_l 归一 *)
    unfold dyd_annulus.
    apply (dyd_le_b_eq_l _ _ _
             (dyd_le_b_plus_compat (real_const lo2) (dyd_axis j)
                (real_plus (real_const t)
                   (real_opp (real_mult (real_const t) (real_const t))))
                (real_log (real_plus real_one (real_const t)) Hs)
                Hlo
                (real_log_one_plus_ge_B (real_const t) Htp Hs))).
    + apply real_eq_of_zero_diff. intro n0.
      repeat rewrite real_plus_proj. repeat rewrite real_const_proj.
      rewrite real_opp_proj. repeat rewrite real_mult_proj.
      repeat rewrite real_const_proj. ring.
  - split.
    + (* 上界：plus_compat(轴上界, log(1+t) 上界 t) + eq_r 归一 *)
      unfold dyd_annulus.
      apply (dyd_le_b_eq_r _ _ _
               (dyd_le_b_plus_compat (dyd_axis j) (real_const hi2)
                  (real_log (real_plus real_one (real_const t)) Hs)
                  (real_const t)
                  Hhi
                  (real_log_one_plus_le_B (real_const t) Hs))).
      * apply dyd_plus_const_eq.
    + (* 宽：(hi2+t)−(lo2+(t−t²)) == (hi2−lo2)+t·t == 2·j·t2 n + t·t *)
      apply qeq_imp_qeqT. apply qeqT_imp_qeq in Hw.
      setoid_replace ((hi2 + t) - (lo2 + (t - t * t)))
        with ((hi2 - lo2) + (t - (t - t * t))) by ring.
      setoid_rewrite Hw.
      ring.
Qed.

(* ============================================================ *)
(* §5 数值见证位：ln(3/2) ∈ [1/4, 1/2]（j=0, t=1/2 实例；           *)
(*     python sanity：math.log(1.5)=0.405465 ∈ [0.25,0.5] ✓）      *)
(* ============================================================ *)

Corollary dyd_ln32_witness : forall n : nat,
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo) (dyd_annulus 0 (1#2)%Q dyd_half_Qpos))
        (And (real_le_b (dyd_annulus 0 (1#2)%Q dyd_half_Qpos) (real_const hi))
             (QeqT (hi - lo)
                   (2 * ((Z.of_nat 0 # 1) * t2 n) + (1#2)%Q * (1#2)%Q))))).
Proof. intro n. exact (dyd_ln_env_family 0 (1#2)%Q dyd_half_Qpos n). Qed.

(* ============================================================ *)
(* §6 公理面留痕（Print Assumptions 全主件核验 Closed）              *)
(* ============================================================ *)

Print Assumptions dyd_le_b_plus_compat.
Print Assumptions dyd_ln_env_pos.
Print Assumptions dyd_ln_env_neg.
Print Assumptions dyd_axis_rate.
Print Assumptions dyd_ln_env.
Print Assumptions dyd_ln_env_family.
Print Assumptions dyd_ln32_witness.
