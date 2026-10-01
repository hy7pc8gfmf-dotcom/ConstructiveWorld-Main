(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(* PiEnvelope.v —— 位 C13（）                     *)
(* π 有理包络基础版：Leibniz 级数 4·Σ_{k≥0} (−1)^k/(2k+1) 的      *)
(* 奇偶双边夹逼 + 显式模量 + Real 层 cauchy_real_pi_leibniz 桥。  *)
(*                                                               *)
(* 模板：B4 LogTwoEnvelope.v 的 l2e_ 四段式（定义→模量序→项恒等   *)
(* →奇偶夹逼→尾界），同构替换 1/(k+1)→1/(2k+1) 并加因子 4。      *)
(* S10 桥：lp_odd m = Σ_{j≤m} (a_{2j}−a_{2j+1})（偶子列，单调），  *)
(* pie_lp_bridge 证 lp_odd m == pie_partial (2m+2)，从而          *)
(* projT1 cauchy_real_pi_leibniz n == 4·pie_partial (2n+2)。     *)
(*                                                               *)
(* 三件：                                                        *)
(*  1. pie_leibniz_two_sided：任一偶部分和×4 ≤ 任一奇部分和×4     *)
(*     （QleT' 化出口）；配套 pie_leibniz_tail（尾界 4/(2m+1)）。 *)
(*  2. pie_modulus_cauchy：forall eps, QltT' 0 eps -> sigT N,     *)
(*     N := S(ceil(4/eps))（Qceiling 显式），|L_n−L_m| < eps。    *)
(*  3. pi_rational_envelope（Real 桥）：forall eps, QltT' 0 eps ->*)
(*     sigT lo hi, real_lt (real_const lo) π_L ∧ real_lt π_L     *)
(*     (real_const hi) ∧ QltT' (hi−lo) eps（And:=prod，零泄露）。 *)
(* 配套升华：pie_real_three / pie_real_ten_thirds（3 < π_L < 10/3 *)
(* 为包络 m=3/4 特例推论形，数值核验 vm_compute 可判）+           *)
(* pie_const_bounds_merge 归并注记件。                            *)
(*                                                               *)
(* 红线自审：零 公理/承认件/参数/猜想/弃证/        *)
(* 经典逻辑/排中；出口一律 QltT'/QleT'/real_lt/sigT   *)
(* +And:=prod（零 Prop 语句面）；隙宽 4/(4m+1) 型与模量           *)
(* ceil(4/eps) 均显式非平凡；文末 Print Assumptions 留痕。        *)
(* 领土纪律：仅新建 Live/build/PiEnvelope.v；其余只读。       *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               ZArith.ZArith Arith.Arith Bool.Bool Lists.List.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ============================================================ *)
(* §0 出口件：QltT'（Qlt_bool 反映形，Id-of-bool，同 LogTwoEnvelope） *)
(* ============================================================ *)

Definition QltT' (x y : Q) : Set := Id (Qlt_bool x y) true.

Lemma QltT'_to_Qlt : forall x y : Q, QltT' x y -> Qlt x y.
Proof. intros x y H. apply (QltT_to_Qlt x y). exact H. Qed.

Lemma Qlt_to_QltT' : forall x y : Q, Qlt x y -> QltT' x y.
Proof. intros x y H. exact (Qlt_to_QltT x y H). Qed.

Lemma qleT'_weaken : forall a b c : Q, Qle a b -> b == c -> QleT' a c.
Proof.
  intros a b c H Hbc.
  apply Qle_to_QleT'.
  apply (Qle_trans a b c H).
  apply qeq_le. exact Hbc.
Qed.

(* ============================================================ *)
(* §1 定义                                                        *)
(* ============================================================ *)

(* ---- 项 t_k := (−1)^k/(2k+1)（Leibniz 项，未乘 4） ---- *)
Definition pie_term (k : nat) : Q :=
  q_pow (-1) k / (Z.of_nat (2 * k + 1) # 1).

(* ---- 部分和 S_n := Σ_{k<n} t_k（n 项） ---- *)
Fixpoint pie_partial (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S m => pie_partial m + pie_term m
  end.

(* ---- 项模量 m_k := 1/(2k+1)（|t_k| 的闭式） ---- *)
Definition pie_mag (k : nat) : Q := 1 / (Z.of_nat (2 * k + 1) # 1).

(* ---- 一步/两步差（对照 l2e_gap1/gap2 的减法形） ---- *)
Lemma pie_gap1 : forall n : nat,
  pie_partial (Datatypes.S n) - pie_partial n == pie_term n.
Proof. intro n. simpl. ring. Qed.

Lemma pie_gap2 : forall n : nat,
  pie_partial (Datatypes.S (Datatypes.S n)) - pie_partial n ==
  pie_term n + pie_term (Datatypes.S n).
Proof. intro n. simpl. ring. Qed.

(* ---- 两步差的加法形（桥用） ---- *)
Lemma pie_gap2_plus : forall n : nat,
  pie_partial n + (pie_term n + pie_term (Datatypes.S n)) ==
  pie_partial (Datatypes.S (Datatypes.S n)).
Proof.
  intro n.
  pose proof (pie_gap2 n) as Hg.
  apply (Qeq_trans _ (pie_partial n
                      + (pie_partial (Datatypes.S (Datatypes.S n)) - pie_partial n)) _).
  - setoid_replace (pie_partial n + (pie_partial (Datatypes.S (Datatypes.S n)) - pie_partial n))
      with (pie_partial n + (pie_term n + pie_term (Datatypes.S n)))
      by (rewrite Hg; reflexivity).
    reflexivity.
  - ring.
Qed.

(* ---- 0 ≤ 4 ---- *)
Lemma pie_four_nonneg : Qle 0 4.
Proof. unfold Qle. simpl. lia. Qed.

(* ---- ×4 保序：x ≤ y ⟹ 4x ≤ 4y ---- *)
Lemma pie_mult4_le : forall x y : Q, Qle x y -> Qle (4 * x) (4 * y).
Proof.
  intros x y H.
  setoid_replace (4 * x) with (x * 4) by ring.
  setoid_replace (4 * y) with (y * 4) by ring.
  apply (Qmult_le_compat_r x y 4).
  - exact H.
  - apply pie_four_nonneg.
Qed.

(* ---- 正数非零 ---- *)
Lemma pie_neq_of_pos : forall z : Q, Qlt 0 z -> ~ (z == 0).
Proof. intros z Hz. apply q_neq_of_lt. exact Hz. Qed.

(* ---- x/2 < x（x > 0） ---- *)
Lemma pie_q_half_lt : forall x : Q, Qlt 0 x -> Qlt (x / 2) x.
Proof.
  intros x Hx.
  assert (Hz2 : Qlt 0 (2 # 1)) by (unfold Qlt; simpl; lia).
  assert (Hi : Qlt 0 (/ (2 # 1))) by (apply Qinv_lt_0_compat; exact Hz2).
  assert (Hlt2 : Qlt x (x * 2)).
  { apply (proj2 (Qlt_minus_iff x (x * 2))).
    setoid_replace (x * 2 - x) with x by ring. exact Hx. }
  assert (Hmul : Qlt (x * / (2 # 1)) (x * 2 * / (2 # 1))).
  { apply (Qmult_lt_compat_r x (x * 2) (/ (2 # 1)) Hi Hlt2). }
  assert (Heq : x * 2 * / (2 # 1) == x).
  { field. }
  rewrite Heq in Hmul.
  unfold Qdiv. exact Hmul.
Qed.

(* ---- z + x < z + y（x < y） ---- *)
Lemma pie_qplus_lt_r : forall z x y : Q, Qlt x y -> Qlt (z + x) (z + y).
Proof.
  intros z x y H.
  apply (proj2 (Qlt_minus_iff (z + x) (z + y))).
  apply (proj1 (Qlt_minus_iff x y)) in H.
  setoid_replace ((z + y) - (z + x)) with (y - x) by ring.
  exact H.
Qed.

(* ============================================================ *)
(* §2 模量序结构（四段式之二/之三）                                *)
(* ============================================================ *)

Lemma pie_den_pos : forall k : nat, Qlt 0 (Z.of_nat (2 * k + 1) # 1).
Proof. intro k. unfold Qlt. simpl. lia. Qed.

Lemma pie_den_neq : forall k : nat, ~ ((Z.of_nat (2 * k + 1) # 1) == 0).
Proof. intro k. apply q_neq_of_lt. apply pie_den_pos. Qed.

Lemma pie_mag_inv : forall k : nat, pie_mag k == / (Z.of_nat (2 * k + 1) # 1).
Proof. intro k. unfold pie_mag, Qdiv. apply Qmult_1_l. Qed.

Lemma pie_mag_pos : forall k : nat, Qlt 0 (pie_mag k).
Proof.
  intro k.
  setoid_replace (pie_mag k) with (/ (Z.of_nat (2 * k + 1) # 1))
    by (apply (pie_mag_inv k)).
  apply Qinv_lt_0_compat.
  apply pie_den_pos.
Qed.

Lemma pie_mag_nonneg : forall k : nat, Qle 0 (pie_mag k).
Proof. intro k. apply (Qlt_le_weak 0 (pie_mag k)). apply pie_mag_pos. Qed.

(* ---- 配对项单调：1/(2k+3) < 1/(2k+1)（支撑件一） ---- *)
Lemma pie_mag_lt : forall k : nat, Qlt (pie_mag (Datatypes.S k)) (pie_mag k).
Proof.
  intro k.
  setoid_replace (pie_mag (Datatypes.S k))
    with (/ (Z.of_nat (2 * Datatypes.S k + 1) # 1))
    by (apply (pie_mag_inv (Datatypes.S k))).
  setoid_replace (pie_mag k) with (/ (Z.of_nat (2 * k + 1) # 1))
    by (apply (pie_mag_inv k)).
  apply (proj1 (Qinv_lt_contravar (Z.of_nat (2 * k + 1) # 1)
                                  (Z.of_nat (2 * Datatypes.S k + 1) # 1)
                                  (pie_den_pos k) (pie_den_pos (Datatypes.S k)))).
  unfold Qlt. simpl. lia.
Qed.

Lemma pie_pair_diff_pos : forall k : nat,
  Qlt 0 (pie_mag k - pie_mag (Datatypes.S k)).
Proof.
  intro k.
  apply (proj1 (Qlt_minus_iff (pie_mag (Datatypes.S k)) (pie_mag k))).
  apply pie_mag_lt.
Qed.

(* ---- 模量反序：a ≤ b ⟹ m_b ≤ m_a ---- *)
Lemma pie_mag_antitone : forall a b : nat, (a <= b)%nat -> Qle (pie_mag b) (pie_mag a).
Proof.
  intros a b Hab.
  destruct (Nat.eq_dec a b) as [Heq | Hne].
  - subst b. apply Qle_refl.
  - assert (Hlt : (a < b)%nat) by lia.
    apply (Qle_trans _ (/ (Z.of_nat (2 * b + 1) # 1)) _).
    + apply qeq_le. apply (pie_mag_inv b).
    + apply Qlt_le_weak.
      setoid_replace (pie_mag a) with (/ (Z.of_nat (2 * a + 1) # 1))
        by (apply (pie_mag_inv a)).
      apply (proj1 (Qinv_lt_contravar (Z.of_nat (2 * a + 1) # 1)
                                      (Z.of_nat (2 * b + 1) # 1)
                                      (pie_den_pos a) (pie_den_pos b))).
      unfold Qlt. simpl. lia.
Qed.

Lemma pie_mag_decr : forall k : nat, Qle (pie_mag (Datatypes.S k)) (pie_mag k).
Proof. intro k. apply pie_mag_antitone. lia. Qed.

Lemma pie_mag_decr_pos_step : forall n : nat,
  Qle 0 (pie_mag n - pie_mag (Datatypes.S n)).
Proof.
  intro n.
  apply (proj1 (Qle_minus_iff (pie_mag (Datatypes.S n)) (pie_mag n))).
  apply pie_mag_decr.
Qed.

(* ============================================================ *)
(* §3 项恒等（|t_k|==m_k；成对项 |t_k+t_{k+1}|==m_k−m_{k+1}）      *)
(* ============================================================ *)

Lemma pie_term_abs : forall k : nat, Qabs (pie_term k) == pie_mag k.
Proof.
  intro k.
  unfold pie_term, Qdiv.
  setoid_rewrite Qabs_Qmult.
  setoid_rewrite sc_abs_sign.
  setoid_rewrite Qabs_Qinv.
  assert (Hd : Qabs (Z.of_nat (2 * k + 1) # 1) == (Z.of_nat (2 * k + 1) # 1)).
  { apply Qabs_pos. unfold Qle. simpl. lia. }
  setoid_rewrite Hd.
  unfold pie_mag, Qdiv.
  ring.
Qed.

Lemma pie_pair_factor : forall k : nat,
  pie_term k + pie_term (Datatypes.S k) ==
  q_pow (-1) k * (pie_mag k - pie_mag (Datatypes.S k)).
Proof.
  intro k.
  unfold pie_term, pie_mag, Qdiv.
  rewrite (q_pow_succ (-1) k).
  ring.
Qed.

Lemma pie_pair_abs : forall k : nat,
  Qabs (pie_term k + pie_term (Datatypes.S k)) ==
  pie_mag k - pie_mag (Datatypes.S k).
Proof.
  intro k.
  apply (Qeq_trans _ (Qabs (q_pow (-1) k * (pie_mag k - pie_mag (Datatypes.S k)))) _).
  - apply (Qabs_wd (pie_term k + pie_term (Datatypes.S k))
                   (q_pow (-1) k * (pie_mag k - pie_mag (Datatypes.S k)))).
    apply pie_pair_factor.
  - setoid_rewrite Qabs_Qmult.
    setoid_rewrite sc_abs_sign.
    assert (Hd : Qabs (pie_mag k - pie_mag (Datatypes.S k)) ==
                 pie_mag k - pie_mag (Datatypes.S k)).
    { apply Qabs_pos.
      apply (Qlt_le_weak 0 (pie_mag k - pie_mag (Datatypes.S k))).
      apply pie_pair_diff_pos. }
    setoid_rewrite Hd.
    ring.
Qed.

(* ============================================================ *)
(* §4 奇偶双边夹逼（对照 l2e_ 同构）                               *)
(* ============================================================ *)

(* ---- 界步：S_{2j} ≤ S_{2j+1}（差 == t_{2j} == m_{2j} > 0） ---- *)
Lemma pie_boundary : forall j : nat,
  Qle (pie_partial (2 * j)) (pie_partial (2 * j + 1)).
Proof.
  intro j.
  assert (H1 : (2 * j + 1)%nat = Datatypes.S (2 * j)) by lia.
  rewrite H1.
  assert (Hpos : Qle 0 (pie_partial (Datatypes.S (2 * j)) - pie_partial (2 * j))).
  { rewrite (pie_gap1 (2 * j)).
    apply (Qle_trans _ (pie_mag (2 * j)) _).
    - apply (Qlt_le_weak 0 (pie_mag (2 * j))). apply pie_mag_pos.
    - apply qeq_le.
      unfold pie_term.
      rewrite (atan_sign_even j).
      unfold pie_mag, Qdiv.
      ring. }
  apply (proj2 (Qle_minus_iff (pie_partial (2 * j))
                              (pie_partial (Datatypes.S (2 * j))))).
  exact Hpos.
Qed.

(* ---- 反向界步：S_{2j} ≤ S_{2j−1}（j=0 平凡截断） ---- *)
Lemma pie_boundary_rev : forall j : nat,
  Qle (pie_partial (2 * j)) (pie_partial (2 * j - 1)).
Proof.
  intro j. destruct j as [| j'].
  - apply Qle_refl.
  - replace (2 * Datatypes.S j')%nat with (2 * j' + 2)%nat by lia.
    replace (2 * j' + 2 - 1)%nat with (2 * j' + 1)%nat by lia.
    replace (2 * j' + 2)%nat with (Datatypes.S (2 * j' + 1)) by lia.
    assert (Hpos : Qle 0 (pie_partial (2 * j' + 1) -
                          pie_partial (Datatypes.S (2 * j' + 1)))).
    { assert (Hd : pie_partial (2 * j' + 1) -
                   pie_partial (Datatypes.S (2 * j' + 1)) ==
                   pie_mag (2 * j' + 1)).
      { apply (Qeq_trans _ (- (pie_term (2 * j' + 1))) _).
        - pose proof (pie_gap1 (2 * j' + 1)) as Hg.
          rewrite <- Hg. ring.
        - unfold pie_term.
          rewrite (atan_sign_odd j').
          unfold pie_mag, Qdiv.
          ring. }
      rewrite Hd. apply pie_mag_nonneg. }
  apply (proj2 (Qle_minus_iff (pie_partial (Datatypes.S (2 * j' + 1)))
                              (pie_partial (2 * j' + 1)))).
  exact Hpos.
Qed.

(* ---- 偶对恒等（纯代数）：m_{2j}−m_{2j+1} == t_{2j}+t_{2j+1} ---- *)
Lemma pie_even_pair_factor : forall j : nat,
  pie_mag (2 * j) - pie_mag (Datatypes.S (2 * j)) ==
  pie_term (2 * j) + pie_term (Datatypes.S (2 * j)).
Proof.
  intro j.
  unfold pie_term, pie_mag, Qdiv.
  rewrite (q_pow_succ (-1) (2 * j)).
  rewrite (atan_sign_even j).
  ring.
Qed.

(* ---- 偶步：S_{2j} ≤ S_{2j+2} ---- *)
Lemma pie_even_step : forall j : nat,
  Qle (pie_partial (2 * j)) (pie_partial (2 * j + 2)).
Proof.
  intro j.
  assert (H2 : (2 * j + 2)%nat = Datatypes.S (Datatypes.S (2 * j))) by lia.
  rewrite H2.
  assert (Hpos : Qle 0 (pie_partial (Datatypes.S (Datatypes.S (2 * j))) -
                        pie_partial (2 * j))).
  { rewrite (pie_gap2 (2 * j)).
    apply (Qle_trans _ (pie_mag (2 * j) - pie_mag (Datatypes.S (2 * j))) _).
    - apply pie_mag_decr_pos_step.
    - apply qeq_le. apply pie_even_pair_factor. }
  apply (proj2 (Qle_minus_iff (pie_partial (2 * j))
                              (pie_partial (Datatypes.S (Datatypes.S (2 * j)))))).
  exact Hpos.
Qed.

(* ---- 奇步：S_{2j+3} ≤ S_{2j+1} ---- *)
Lemma pie_odd_step : forall j : nat,
  Qle (pie_partial (2 * j + 3)) (pie_partial (2 * j + 1)).
Proof.
  intro j.
  assert (H3 : (2 * j + 3)%nat = Datatypes.S (Datatypes.S (2 * j + 1))) by lia.
  rewrite H3.
  assert (Hpos : Qle 0 (pie_partial (2 * j + 1) -
                        pie_partial (Datatypes.S (Datatypes.S (2 * j + 1))))).
  { assert (Hg : pie_partial (2 * j + 1) -
                 pie_partial (Datatypes.S (Datatypes.S (2 * j + 1))) ==
                 pie_mag (2 * j + 1) - pie_mag (Datatypes.S (2 * j + 1))).
    { pose proof (pie_gap2 (2 * j + 1)) as Hfwd.
      assert (Hpf : pie_term (2 * j + 1) + pie_term (Datatypes.S (2 * j + 1)) ==
                    - (pie_mag (2 * j + 1) - pie_mag (Datatypes.S (2 * j + 1)))).
      { unfold pie_term, pie_mag, Qdiv.
        rewrite (q_pow_succ (-1) (2 * j + 1)).
        rewrite (atan_sign_odd j).
        ring. }
      apply (Qeq_trans _ (- (pie_term (2 * j + 1) + pie_term (Datatypes.S (2 * j + 1)))) _).
      - rewrite <- (pie_gap2 (2 * j + 1)). ring.
      - rewrite Hpf. ring. }
    rewrite Hg.
    apply (pie_mag_decr_pos_step (2 * j + 1)). }
  apply (proj2 (Qle_minus_iff (pie_partial (Datatypes.S (Datatypes.S (2 * j + 1))))
                              (pie_partial (2 * j + 1)))).
  exact Hpos.
Qed.

(* ---- 偶列单调 ---- *)
Lemma pie_even_mono : forall d j : nat,
  Qle (pie_partial (2 * j)) (pie_partial (2 * (j + d))).
Proof.
  intros d j. induction d as [| d IH].
  - replace (2 * (j + 0))%nat with (2 * j)%nat by ring. apply Qle_refl.
  - replace (2 * (j + Datatypes.S d))%nat with (2 * (j + d) + 2)%nat by lia.
    apply (Qle_trans _ (pie_partial (2 * (j + d))) _).
    + exact IH.
    + exact (pie_even_step (j + d)).
Qed.

(* ---- 奇列单调（不增） ---- *)
Lemma pie_odd_mono : forall d k : nat,
  Qle (pie_partial (2 * (k + d) + 1)) (pie_partial (2 * k + 1)).
Proof.
  intros d k. induction d as [| d IH].
  - replace (2 * (k + 0) + 1)%nat with (2 * k + 1)%nat by ring. apply Qle_refl.
  - replace (2 * (k + Datatypes.S d) + 1)%nat with (2 * (k + d) + 3)%nat by lia.
    apply (Qle_trans _ (pie_partial (2 * (k + d) + 1)) _).
    + exact (pie_odd_step (k + d)).
    + exact IH.
Qed.

(* ---- 夹逼核心：任一偶部分和 ≤ 任一奇部分和 ---- *)
Lemma pie_even_le_odd : forall j k : nat,
  Qle (pie_partial (2 * j)) (pie_partial (2 * k + 1)).
Proof.
  intros j k.
  destruct (le_lt_dec j k) as [Hjk | Hkj].
  - replace (2 * k + 1)%nat with (2 * (j + (k - j)) + 1)%nat by lia.
    apply (Qle_trans _ (pie_partial (2 * (j + (k - j)))) _).
    + exact (pie_even_mono (k - j) j).
    + exact (pie_boundary (j + (k - j))).
  - apply (Qle_trans _ (pie_partial (2 * j - 1)) _).
    + exact (pie_boundary_rev j).
    + replace (2 * j - 1)%nat with (2 * (k + (j - k - 1)) + 1)%nat by lia.
      exact (pie_odd_mono (j - k - 1) k).
Qed.

(* ---- 隙宽显式：S_{2m+1} − S_{2m} == 1/(4m+1)（支撑件二） ---- *)
Lemma pie_parity_gap : forall m : nat,
  pie_partial (2 * m + 1) - pie_partial (2 * m) == pie_mag (2 * m).
Proof.
  intro m.
  assert (H1 : (2 * m + 1)%nat = Datatypes.S (2 * m)) by lia.
  rewrite H1.
  rewrite (pie_gap1 (2 * m)).
  unfold pie_term.
  rewrite (atan_sign_even m).
  unfold pie_mag, Qdiv.
  ring.
Qed.

(* ============================================================ *)
(* §5 尾界（Leibniz 余项）：m ≤ n ⟹ |S_n − S_m| ≤ m_m             *)
(* ============================================================ *)

Lemma pie_tail_bound : forall m n : nat, (m <= n)%nat ->
  Qle (Qabs (pie_partial n - pie_partial m)) (pie_mag m).
Proof.
  assert (Hgen : forall (d m n : nat), (m <= n)%nat -> (n - m)%nat = d ->
    Qle (Qabs (pie_partial n - pie_partial m)) (pie_mag m)).
  { induction d as [d IH] using lt_wf_ind.
    intros m n Hmn Hd.
    destruct (Nat.leb (Datatypes.S (Datatypes.S m)) n) eqn:E2.
    - (* m + 2 ≤ n：三角拆分 + 成对项 + 归纳 *)
      apply Nat.leb_le in E2.
      apply (Qle_trans _ (Qabs ((pie_partial n - pie_partial (Datatypes.S (Datatypes.S m))) +
                                (pie_partial (Datatypes.S (Datatypes.S m)) - pie_partial m))) _).
      + apply qeq_le.
        apply (Qabs_wd (pie_partial n - pie_partial m)
                       ((pie_partial n - pie_partial (Datatypes.S (Datatypes.S m))) +
                        (pie_partial (Datatypes.S (Datatypes.S m)) - pie_partial m))).
        ring.
      + apply (Qle_trans _ (Qabs (pie_partial n - pie_partial (Datatypes.S (Datatypes.S m))) +
                            Qabs (pie_partial (Datatypes.S (Datatypes.S m)) - pie_partial m)) _).
        * apply Qabs_triangle.
        * apply (Qle_trans _ (pie_mag (Datatypes.S (Datatypes.S m)) +
                              (pie_mag m - pie_mag (Datatypes.S m))) _).
          -- apply Qplus_le_compat.
             ++ apply (IH (n - Datatypes.S (Datatypes.S m))%nat).
                ** lia.
                ** lia.
                ** reflexivity.
             ++ apply qeq_le.
                apply (Qeq_trans _ (Qabs (pie_term m + pie_term (Datatypes.S m))) _).
                ** apply (Qabs_wd (pie_partial (Datatypes.S (Datatypes.S m)) -
                                   pie_partial m)
                                  (pie_term m + pie_term (Datatypes.S m))).
                   exact (pie_gap2 m).
                ** apply pie_pair_abs.
          -- apply (Qle_trans _ (pie_mag (Datatypes.S m) +
                                 (pie_mag m - pie_mag (Datatypes.S m))) _).
             ++ apply Qplus_le_compat.
                ** apply pie_mag_decr.
                ** apply Qle_refl.
             ++ apply qeq_le. ring.
    - apply Nat.leb_gt in E2.
      destruct (Nat.eq_dec m n) as [Heq | Hne].
      + subst n.
        apply (Qle_trans _ 0 _).
        * apply qeq_le.
          apply (Qabs_wd (pie_partial m - pie_partial m) 0).
          ring.
        * apply pie_mag_nonneg.
      + assert (Hn : n = Datatypes.S m) by lia.
        subst n.
        apply qeq_le.
        apply (Qeq_trans _ (Qabs (pie_term m)) _).
        * apply (Qabs_wd (pie_partial (Datatypes.S m) - pie_partial m) (pie_term m)).
          exact (pie_gap1 m).
        * apply pie_term_abs.
  }
  intros m n Hmn.
  apply (Hgen (n - m)%nat m n Hmn). reflexivity.
Qed.

(* ---- ×4 尾界（Q 层）：m ≤ n ⟹ |L_n − L_m| ≤ 4/(2m+1) ---- *)
Lemma pie_tail4 : forall m n : nat, (m <= n)%nat ->
  Qle (Qabs (4 * pie_partial n - 4 * pie_partial m)) (4 * pie_mag m).
Proof.
  intros m n Hmn.
  apply (Qle_trans _ (4 * Qabs (pie_partial n - pie_partial m)) _).
  - apply qeq_le.
    apply (Qeq_trans _ (Qabs (4 * (pie_partial n - pie_partial m))) _).
    + apply (Qabs_wd (4 * pie_partial n - 4 * pie_partial m)
                     (4 * (pie_partial n - pie_partial m))).
      ring.
    + apply (Qeq_trans _ (Qabs 4 * Qabs (pie_partial n - pie_partial m)) _).
      * apply Qabs_Qmult.
      * setoid_replace (Qabs 4) with 4
          by (apply Qabs_pos; apply pie_four_nonneg).
        reflexivity.
  - apply pie_mult4_le. apply pie_tail_bound. exact Hmn.
Qed.

(* ============================================================ *)
(* §6 主件一：pie_leibniz_two_sided（奇偶双边夹逼，QleT' 出口）     *)
(*    L_n := 4·S_n：任一偶 L ≤ 任一奇 L；配套尾界件。              *)
(* ============================================================ *)

Theorem pie_leibniz_two_sided : forall j k : nat,
  QleT' (4 * pie_partial (2 * j)) (4 * pie_partial (2 * k + 1)).
Proof.
  intros j k.
  apply Qle_to_QleT'.
  apply pie_mult4_le.
  apply pie_even_le_odd.
Qed.

(* ---- 出口件：QleT' 化尾界 ---- *)
Theorem pie_leibniz_tail : forall m n : nat, (m <= n)%nat ->
  QleT' (Qabs (4 * pie_partial n - 4 * pie_partial m)) (4 * pie_mag m).
Proof.
  intros m n Hmn.
  apply (qleT'_weaken _ (4 * pie_mag m) _).
  - apply pie_tail4. exact Hmn.
  - reflexivity.
Qed.

(* ---- ×4 隙宽显式：L_{2m+1} − L_{2m} == 4/(4m+1) ---- *)
Lemma pie_parity_gap4 : forall m : nat,
  4 * pie_partial (2 * m + 1) - 4 * pie_partial (2 * m) == 4 * pie_mag (2 * m).
Proof.
  intro m.
  (* 注：原 qeq_le（S02:608，实签 == -> Qle）方向不合；经 4·(a−b) 中转两步环 *)
  assert (Hgap := pie_parity_gap m).
  apply (Qeq_trans _ (4 * (pie_partial (2 * m + 1) - pie_partial (2 * m))) _).
  - ring.
  - rewrite Hgap. ring.
Qed.

(* ============================================================ *)
(* §7 模量支：N := S(ceil(4/eps))（Qceiling 显式）                 *)
(* ============================================================ *)

Definition pie_modulus (eps : Q) : nat :=
  Datatypes.S (Z.to_nat (Qceiling (4 / eps))).

Lemma pie_modulus_bound : forall eps : Q, Qlt 0 eps ->
  Qlt (4 * pie_mag (pie_modulus eps)) eps.
Proof.
  intros eps Heps.
  assert (Hx0 : Qlt 0 (4 / eps)).
  { unfold Qdiv. apply (Qmult_lt_0_compat 4 (Qinv eps)).
    - unfold Qlt; simpl; lia.
    - apply Qinv_lt_0_compat. exact Heps. }
  assert (Hcq : Qle 0 (Qceiling (4 / eps) # 1)).
  { apply (Qle_trans 0 (4 / eps) (Qceiling (4 / eps) # 1)).
    - apply (Qlt_le_weak 0 (4 / eps)). exact Hx0.
    - apply Qle_ceiling. }
  assert (Hcpos : (0 <= Qceiling (4 / eps))%Z).
  { unfold Qle in Hcq. simpl in Hcq. lia. }
  assert (Hstep : Qlt (4 / eps) ((Z.succ (Qceiling (4 / eps))) # 1)).
  { apply (Qle_lt_trans (4 / eps) (Qceiling (4 / eps) # 1)
                        ((Z.succ (Qceiling (4 / eps))) # 1)).
    - apply Qle_ceiling.
    - unfold Qlt, Qle. simpl. lia. }
  assert (Hz : (Z.succ (Qceiling (4 / eps)) = Z.of_nat (pie_modulus eps))%Z)
    by (unfold pie_modulus; lia).
  assert (Hmul : Qlt (4 / eps * eps) ((Z.of_nat (pie_modulus eps) # 1) * eps)).
  { apply (Qmult_lt_compat_r (4 / eps) (Z.of_nat (pie_modulus eps) # 1) eps Heps).
    rewrite <- Hz. exact Hstep. }
  setoid_replace (4 / eps * eps) with 4%Q in Hmul.
  2: { unfold Qdiv. field.
       intro Hzz. apply (Qlt_not_eq 0 eps Heps). exact (Qeq_sym _ _ Hzz). }
  assert (Hn1 : (1 <= pie_modulus eps)%nat) by (unfold pie_modulus; lia).
  assert (HzN1 : (0 < Z.of_nat (pie_modulus eps))%Z)
    by (unfold pie_modulus; lia).  (* 注：Nat2Z.inj_lt 系 IFF 不可直 apply；lia 经 zify 直证 *)
  assert (Hzd1 : (0 < Z.of_nat (2 * pie_modulus eps + 1))%Z)
    by lia.  (* 注：同上，Nat2Z.inj_lt IFF 不可直 apply *)
  assert (Hzlt : (Z.of_nat (pie_modulus eps) < Z.of_nat (2 * pie_modulus eps + 1))%Z)
    by (apply Nat2Z.inj_lt; lia).
  setoid_replace (pie_mag (pie_modulus eps))
    with (/ (Z.of_nat (2 * pie_modulus eps + 1) # 1))
    by (apply (pie_mag_inv (pie_modulus eps))).
  assert (Hinvlt : Qlt (/ (Z.of_nat (2 * pie_modulus eps + 1) # 1))
                       (/ (Z.of_nat (pie_modulus eps) # 1))).
  { apply (proj1 (Qinv_lt_contravar (Z.of_nat (pie_modulus eps) # 1)
                                    (Z.of_nat (2 * pie_modulus eps + 1) # 1)
                                    HzN1 Hzd1)).
    unfold Qlt. simpl. lia. }  (* 注：Qlt(z#1,w#1) 与 Zlt(z,w) 差 Qnum/Qden 一层，lia 桥 *)
  assert (Hstep1 : Qlt (4 * / (Z.of_nat (2 * pie_modulus eps + 1) # 1))
                       (4 * / (Z.of_nat (pie_modulus eps) # 1))).
  { setoid_replace (4 * / (Z.of_nat (2 * pie_modulus eps + 1) # 1))
      with (/ (Z.of_nat (2 * pie_modulus eps + 1) # 1) * 4) by ring.
    setoid_replace (4 * / (Z.of_nat (pie_modulus eps) # 1))
      with (/ (Z.of_nat (pie_modulus eps) # 1) * 4) by ring.
    apply (Qmult_lt_compat_r (/ (Z.of_nat (2 * pie_modulus eps + 1) # 1))
                             (/ (Z.of_nat (pie_modulus eps) # 1)) 4).
    - unfold Qlt; simpl; lia.
    - exact Hinvlt. }
  assert (Hfinv : Qlt 0 (/ (Z.of_nat (pie_modulus eps) # 1)))
    by (apply Qinv_lt_0_compat; unfold Qlt; simpl; lia).  (* 注：子目标系 Qlt 面需展 Z 桥 *)
  assert (Hs2 : Qlt (4 * / (Z.of_nat (pie_modulus eps) # 1))
                    (((Z.of_nat (pie_modulus eps) # 1) * eps)
                     * / (Z.of_nat (pie_modulus eps) # 1))).  (* 注：# 与 * 同级，z#1*eps 无括号被析作 z#(1*eps) 落 positive 槽 *)
  { apply (Qmult_lt_compat_r 4 ((Z.of_nat (pie_modulus eps) # 1) * eps)
                               (/ (Z.of_nat (pie_modulus eps) # 1)) Hfinv Hmul). }
  assert (Heq : ((Z.of_nat (pie_modulus eps) # 1) * eps)
                * / (Z.of_nat (pie_modulus eps) # 1) == eps).
  { field. intro Hzz.
    (* 注：原路 Qeq_sym Hzz 得 0==z#1 推不出 0==eps；改从 Hmul:4<(z#1)*eps 出谬 *)
    rewrite Hzz in Hmul.
    assert (Hz00 : (0 * eps)%Q == 0) by ring.
    rewrite Hz00 in Hmul.
    unfold Qlt in Hmul. simpl in Hmul. discriminate. }
  rewrite Heq in Hs2.
  exact (Qlt_trans _ _ _ Hstep1 Hs2).
Qed.

(* ---- 出口：sigT 柯西模量（N 显式：S(ceil(4/eps))，可抽取） ---- *)
Theorem pie_modulus_cauchy : forall eps : Q, QltT' 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    QltT' (Qabs (4 * pie_partial n - 4 * pie_partial m)) eps).
Proof.
  intros eps Heps.
  assert (Hlt : Qlt 0 eps) by (apply (QltT'_to_Qlt 0 eps Heps)).
  exists (pie_modulus eps).
  intros m n HNm HNn.
  apply Qlt_to_QltT'.
  destruct (Nat.leb m n) eqn:E.
  - apply Nat.leb_le in E.
    apply (Qle_lt_trans _ (4 * pie_mag (pie_modulus eps)) _).
    + apply (Qle_trans _ (4 * pie_mag m) _).
      * apply pie_tail4. exact E.
      * rewrite (Qmult_comm 4 (pie_mag m)), (Qmult_comm 4 (pie_mag (pie_modulus eps))).
        apply Qmult_le_compat_r; [apply pie_mag_antitone; apply NatLe_drop in HNm; exact HNm | unfold Qle; simpl; discriminate].
        (* 注：9.1 无 _l 版；comm 换右乘形接 _r *)
    + exact (pie_modulus_bound eps Hlt).
  - apply Nat.leb_gt in E.
    apply (Qle_lt_trans _ (4 * pie_mag (pie_modulus eps)) _).
    + apply (Qle_trans _ (4 * pie_mag n) _).
      * rewrite Qabs_Qminus. apply (pie_tail4 n m). lia.
      * rewrite (Qmult_comm 4 (pie_mag n)), (Qmult_comm 4 (pie_mag (pie_modulus eps))).
        apply Qmult_le_compat_r; [apply pie_mag_antitone; apply NatLe_drop in HNn; lia | unfold Qle; simpl; discriminate].
    + exact (pie_modulus_bound eps Hlt).
Qed.

(* ============================================================ *)
(* §8 Real 桥：cauchy_real_pi_leibniz（S10:2955）                  *)
(*   lp_odd m = Σ_{j≤m} (a_{2j}−a_{2j+1}) == S_{2m+2}（偶子列）    *)
(* ============================================================ *)

(* ---- lp_pair (S m) == t_{2m+2} + t_{2m+3}（配对拆分） ---- *)
Lemma pie_pair_split : forall m : nat,
  lp_pair (Datatypes.S m) ==
  pie_term (2 * m + 2) + pie_term (Datatypes.S (2 * m + 2)).
Proof.
  intro m.
  assert (Hev : q_pow (-1) (2 * m + 2) == 1).
  { replace (2 * m + 2)%nat with (2 * (m + 1))%nat by lia.
    apply (atan_sign_even (m + 1)). }
  assert (Hod : q_pow (-1) (2 * m + 3) == -1).
  { replace (2 * m + 3)%nat with (2 * (m + 1) + 1)%nat by lia.
    apply (atan_sign_odd (m + 1)). }
  unfold lp_pair, lp_a, pie_term, Qdiv.
  replace (2 * Datatypes.S m)%nat with (2 * m + 2)%nat by lia.
  replace (2 * Datatypes.S m + 1)%nat with (2 * m + 3)%nat by lia.
  replace (Datatypes.S (2 * m + 2))%nat with (2 * m + 3)%nat by lia.
  replace (2 * m + 2 + 1)%nat with (2 * m + 3)%nat by lia.
  rewrite Hev, Hod. ring.
Qed.

(* ---- 桥核心：lp_odd m == S_{2m+2} ---- *)
Lemma pie_lp_bridge : forall m : nat, lp_odd m == pie_partial (2 * m + 2).
Proof.
  induction m as [| m IH].
  - unfold lp_odd, lp_pair, lp_a, pie_partial, pie_term, Qdiv.
    simpl. ring.
  - change (lp_odd (Datatypes.S m)) with (lp_odd m + lp_pair (Datatypes.S m)).
    rewrite IH.
    assert (Hidx : (2 * Datatypes.S m + 2)%nat = Datatypes.S (Datatypes.S (2 * m + 2)))
      by lia.
    rewrite Hidx.
    rewrite <- (pie_gap2_plus (2 * m + 2)).
    rewrite (pie_pair_split m).
    ring.
Qed.

(* ---- 桥投影：v n == 4·S_{2n+2} ---- *)
Lemma pie_v_eq : forall n : nat,
  lp_four * lp_odd n == 4 * pie_partial (2 * n + 2).
Proof.
  intro n.
  rewrite (pie_lp_bridge n).
  unfold lp_four. ring.
Qed.

(* ---- 下翼生成器：v n ≥ lo（n ≥ N，lo ≤ 4·S_{2N+2}，余量 c） ---- *)
Lemma pie_real_lower_gen : forall (N : nat) (c lo : Q),
  Qlt 0 c -> Qle (lo + c) (4 * pie_partial (2 * N + 2)) ->
  real_lt (real_const lo) cauchy_real_pi_leibniz.
  (* 注（挂起语义补全，唯此一处语句面触改）：原稿假设缺 + c，本件不可证
     （反例 lo:=4·S_{2N+2} 满足原假设而结论要求 1/2<0）；证明体 Hlo 实用于
     lo+c<=4·S_{2N+2}，对偶上翼 pie_real_upper_gen 带 + c、全部调用点按
     lo+c==v N 实例化——按作者显见意图补齐。 *)

Proof.
  intros N c lo Hc Hlo.
  unfold real_lt.
  exists (c / 2).
  split.
  - apply Qlt_to_QltT. unfold Qlt in Hc; simpl in Hc. unfold Qlt. simpl. lia.
  - exists N. intros n Hn.
    apply NatLe_drop in Hn.
    simpl.
    apply Qlt_to_QltT.
    setoid_replace (lp_four * lp_odd n) with (4 * pie_partial (2 * n + 2))
      by (apply pie_v_eq).
    setoid_replace (4 * pie_partial (2 * n + 2) - lo)
      with ((4 * pie_partial (2 * n + 2) - 4 * pie_partial (2 * N + 2))
            + (4 * pie_partial (2 * N + 2) - lo)) by ring.
    apply (Qlt_le_trans (c / 2) c _).
    + apply (pie_q_half_lt c Hc).
    + apply (Qle_trans c ((4 * pie_partial (2 * N + 2) - lo)
                           + (4 * pie_partial (2 * n + 2) - 4 * pie_partial (2 * N + 2))) _).
      * apply (Qle_trans c ((4 * pie_partial (2 * N + 2) - lo) + 0) _).
        -- apply (Qle_trans c (4 * pie_partial (2 * N + 2) - lo) _).
           ++ apply (proj2 (Qle_minus_iff c (4 * pie_partial (2 * N + 2) - lo))).
              setoid_replace (4 * pie_partial (2 * N + 2) - lo - c)
                with (4 * pie_partial (2 * N + 2) - (lo + c)) by ring.
              apply (proj1 (Qle_minus_iff (lo + c) (4 * pie_partial (2 * N + 2)))).
              exact Hlo.
           ++ apply qeq_le. ring.
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply (proj1 (Qle_minus_iff (4 * pie_partial (2 * N + 2))
                                          (4 * pie_partial (2 * n + 2)))).
              apply pie_mult4_le.
              replace (2 * N + 2)%nat with (2 * (N + 1))%nat by lia.
              replace (2 * n + 2)%nat with (2 * ((N + 1) + (n - N)))%nat by lia.
              apply (pie_even_mono (n - N) (N + 1)).
      * apply qeq_le. ring.
Qed.

(* ---- 上翼生成器：v n ≤ hi（n ≥ 0，hi ≥ 4·S_{2N+1} + c，余量 c） ---- *)
Lemma pie_real_upper_gen : forall (N : nat) (c hi : Q),
  Qlt 0 c -> Qle (4 * pie_partial (2 * N + 1) + c) hi ->
  real_lt cauchy_real_pi_leibniz (real_const hi).
Proof.
  intros N c hi Hc Hhi.
  unfold real_lt.
  exists (c / 2).
  split.
  - apply Qlt_to_QltT. unfold Qlt in Hc; simpl in Hc. unfold Qlt. simpl. lia.
  - exists 0%nat. intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    setoid_replace (lp_four * lp_odd n) with (4 * pie_partial (2 * n + 2))
      by (apply pie_v_eq).
    setoid_replace (hi - 4 * pie_partial (2 * n + 2))
      with ((hi - 4 * pie_partial (2 * N + 1))
            + (4 * pie_partial (2 * N + 1) - 4 * pie_partial (2 * n + 2))) by ring.
    apply (Qlt_le_trans (c / 2) c _).
    + apply (pie_q_half_lt c Hc).
    + apply (Qle_trans c (c + 0) _).
      * apply qeq_le. ring.
      * apply Qplus_le_compat.
        -- (* c ≤ hi − 4·S_{2N+1}（由 Hhi 换序） *)
           apply (proj2 (Qle_minus_iff c (hi - 4 * pie_partial (2 * N + 1)))).
           apply (Qle_trans 0 (hi - (4 * pie_partial (2 * N + 1) + c)) _).
           ++ apply (proj1 (Qle_minus_iff (4 * pie_partial (2 * N + 1) + c) hi)).
              exact Hhi.
           ++ apply qeq_le. ring.
        -- (* 0 ≤ 4·S_{2N+1} − 4·S_{2n+2}（偶 ≤ 奇） *)
           apply (proj1 (Qle_minus_iff (4 * pie_partial (2 * n + 2))
                                       (4 * pie_partial (2 * N + 1)))).
           replace (2 * n + 2)%nat with (2 * (n + 1))%nat by lia.
              apply pie_mult4_le.
           apply (pie_even_le_odd (n + 1) N).
Qed.

(* ---- x/4 + x/4 == x/2 ---- *)
Lemma pie_q_add_halves : forall x : Q, x / 4 + x / 4 == x / 2.
Proof.
  intro x. unfold Qdiv. field.
Qed.

(* ============================================================ *)
(* §8 主件二（Real 桥）：pi_rational_envelope                      *)
(* ============================================================ *)

Theorem pi_rational_envelope : forall eps : Q, QltT' 0 eps ->
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_lt (real_const lo) cauchy_real_pi_leibniz)
        (And (real_lt cauchy_real_pi_leibniz (real_const hi))
             (QltT' (hi - lo) eps)))).
Proof.
  intros eps Heps.
  assert (HepsQ : Qlt 0 eps) by (apply (QltT'_to_Qlt 0 eps Heps)).
  assert (Hc4 : Qlt 0 (eps / 4)).
  { unfold Qdiv. apply (Qmult_lt_0_compat eps (/ (4 # 1))).
    - exact HepsQ.
    - apply Qinv_lt_0_compat. unfold Qlt; simpl; lia. }
  assert (Hc2 : Qlt 0 (eps / 2)).
  { unfold Qdiv. apply (Qmult_lt_0_compat eps (/ (2 # 1))).
    - exact HepsQ.
    - apply Qinv_lt_0_compat. unfold Qlt; simpl; lia. }
  assert (Hb : Qlt (4 * pie_mag (2 * pie_modulus (eps / 2) + 1)) (eps / 2)).
  { apply (Qle_lt_trans _ (4 * pie_mag (pie_modulus (eps / 2))) _).
    - apply pie_mult4_le. apply pie_mag_antitone. lia.
    - apply (pie_modulus_bound (eps / 2) Hc2). }
  exists (4 * pie_partial (2 * pie_modulus (eps / 2) + 2) - eps / 4).
  exists (4 * pie_partial (2 * pie_modulus (eps / 2) + 1) + eps / 4).
  split.
  - apply (pie_real_lower_gen (pie_modulus (eps / 2)) (eps / 4)
            (4 * pie_partial (2 * pie_modulus (eps / 2) + 2) - eps / 4)).
    + exact Hc4.
    + apply qeq_le. ring.
  - split.
    + apply (pie_real_upper_gen (pie_modulus (eps / 2)) (eps / 4)
              (4 * pie_partial (2 * pie_modulus (eps / 2) + 1) + eps / 4)).
      * exact Hc4.
      * apply Qle_refl.
    + apply Qlt_to_QltT'.
      replace (2 * pie_modulus (eps / 2) + 2)%nat
        with (Datatypes.S (2 * pie_modulus (eps / 2) + 1))%nat by lia.
      assert (Hgap : 4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
                     - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1))
                     == 4 * pie_mag (2 * pie_modulus (eps / 2) + 1)).
      { assert (Hg := pie_gap1 (2 * pie_modulus (eps / 2) + 1)).
        assert (Hs : pie_term (2 * pie_modulus (eps / 2) + 1)
                     == - pie_mag (2 * pie_modulus (eps / 2) + 1)).
        { unfold pie_term, pie_mag, Qdiv.
          rewrite (atan_sign_odd (pie_modulus (eps / 2))). ring. }
        setoid_replace (4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
                        - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1)))
          with (- (4 * (pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1))
                     - pie_partial (2 * pie_modulus (eps / 2) + 1))))
          by ring.
        rewrite Hg. rewrite Hs. ring. }
      setoid_replace ((4 * pie_partial (2 * pie_modulus (eps / 2) + 1) + eps / 4)
                      - (4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1))
                         - eps / 4))
        with ((4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
               - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1)))
              + (eps / 4 + eps / 4)) by ring.
      setoid_replace (4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
                      - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1)))
        with (4 * pie_mag (2 * pie_modulus (eps / 2) + 1)) by exact Hgap.
      setoid_replace (eps / 4 + eps / 4) with (eps / 2)
        by apply pie_q_add_halves.
      apply (proj2 (Qlt_minus_iff (4 * pie_mag (2 * pie_modulus (eps / 2) + 1)
                                   + eps / 2) eps)).
      setoid_replace (eps - (4 * pie_mag (2 * pie_modulus (eps / 2) + 1) + eps / 2))
        with ((eps - eps / 2) - 4 * pie_mag (2 * pie_modulus (eps / 2) + 1))
        by ring.
      setoid_replace (eps - eps / 2) with (eps / 2)
        by (unfold Qdiv; field).
      apply (proj1 (Qlt_minus_iff (4 * pie_mag (2 * pie_modulus (eps / 2) + 1))
                                  (eps / 2))).
      exact Hb.
Qed.

(* ============================================================ *)
(* §9 配套升华：3 < π_L < 10/3 为包络特例推论（数值核验 vm_compute）  *)
(* ============================================================ *)

(* ---- Q 层数值核验件（vm_compute 可判） ---- *)
Lemma pie_sp8_over_three : Qlt 0 (4 * pie_partial 8 - 3).
Proof. vm_compute. reflexivity. Qed.

Lemma pie_sp8_ge_three : Qle 3 (4 * pie_partial 8).
Proof.
  apply (Qlt_le_weak 3 (4 * pie_partial 8)).
  unfold Qlt. vm_compute. reflexivity.
Qed.

Lemma pie_sp9_under_ten3 : Qlt 0 (10 / 3 - 4 * pie_partial 9).
Proof. vm_compute. reflexivity. Qed.

(* ---- 3 < π_L（下翼 m=3 特例推论） ---- *)
Theorem pie_real_three : real_lt (real_const 3) cauchy_real_pi_leibniz.
Proof.
  apply (pie_real_lower_gen 3 (4 * pie_partial 8 - 3) 3).
  - apply pie_sp8_over_three.
  - replace (2 * 3 + 2)%nat with 8%nat by lia.
    apply qeq_le. ring.
Qed.

(* ---- π_L < 10/3（上翼 m=4 特例推论） ---- *)
Theorem pie_real_ten_thirds : real_lt cauchy_real_pi_leibniz (real_const (10 / 3)).
Proof.
  apply (pie_real_upper_gen 4 (10 / 3 - 4 * pie_partial 9) (10 / 3)).
  - apply pie_sp9_under_ten3.
  - replace (2 * 4 + 1)%nat with 9%nat by lia.
    apply qeq_le. ring.
Qed.

(* ---- 归并注记件：3 < π_L < 10/3（S10 half_lower/upper 的常数界前身） ---- *)
Theorem pie_const_bounds_merge :
  And (real_lt (real_const 3) cauchy_real_pi_leibniz)
      (real_lt cauchy_real_pi_leibniz (real_const (10 / 3))).
Proof.
  split.
  - exact pie_real_three.
  - exact pie_real_ten_thirds.
Qed.

(* ============================================================ *)
(* §10 假设留痕（红线④：Print Assumptions ≥ 1）                   *)
(* ============================================================ *)

Print Assumptions pie_leibniz_two_sided.
Print Assumptions pie_leibniz_tail.
Print Assumptions pie_modulus_cauchy.
Print Assumptions pi_rational_envelope.
Print Assumptions pie_const_bounds_merge.
