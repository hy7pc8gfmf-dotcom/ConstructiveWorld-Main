(* ============================================================
   LogTwoEnvelope —— 使命行：ln2 交错级数的 Q 层双边包络件。
   本件形式化 ln2 = Σ_{k≥0} (−1)^k/(k+1) 交错级数的 Q 层双边包络三件套
   （出口全 Set 层）：
   1. l2e_alt_partial：部分和 S_n（Z.of_nat # 1 构造）；
   2. l2e_alt_two_sided（QleT' 出口）：forall m n, m ≤ n ->
      QleT' (Qabs (S_n − S_m)) (1/(m+1))——尾界显式公式；配套奇偶
      双边夹逼件（l2e_even_le_odd / l2e_parity_gap / l2e_even_mono /
      l2e_odd_mono）：任一偶部分和 ≤ 任一奇部分和，相邻偶奇之差
      == 1/(2m+1) 显式（ln2 本体是 real 层对象，本件对 Q 层交替和
      独立建理——奇偶单调两翼＋显式隙宽，纯 Q 层落实）；
   3. l2e_cauchy_modulus：forall eps, QltT' 0 eps -> sigT N,
      forall m n, N ≤ m -> N ≤ n -> QltT' (Qabs (S_n − S_m)) eps，
      N := l2e_modulus eps = S (Z.to_nat (Qceiling (1/eps)))——
      ceil(1/eps) 显式可抽取。
   模量序结构：恒等 l2e_mag_inv、正性 l2e_den_pos/l2e_mag_pos、
   严格递减 l2e_mag_lt、单调 l2e_mag_decr（委托 l2e_mag_antitone）、
   成对项恒等 l2e_pair_abs：|t_k+t_{k+1}| == m_k−m_{k+1}。
   依赖：CW_ConstructiveWorld_219；stdlib QArith.QArith、QArith.Qabs、
   QArith.Qround、ZArith.ZArith、Arith.Arith、Bool.Bool、Lists.List、
   Setoid、Morphisms、Lia、QArith.Qminmax。
   对标：mathlib 交错级数 Leibniz 部分和包络形；stdlib QArith 序/绝对值引理族。
   构造性注记：出口一律 QltT'/QleT'/NatLe/sigT（Id-of-bool 形）；零经典逻辑；
   尾界 1/(m+1) 为显式公式；分母正性 l2e_den_pos 以显式 Z 正性见证构造
   （Pos2Z.pos_is_pos，不经一键算术自动战术）；文末 Print Assumptions 追印。
   编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。
   ============================================================*)

Require Import CW_ConstructiveWorld_219.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               ZArith.ZArith Arith.Arith Bool.Bool Lists.List.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ============================================================ *)
(* §0 Set 层出口件：QltT'（Qlt_bool 反映形，Id-of-bool，同 QltT） *)
(* ============================================================ *)
(* 库内已有 QltT/QleT'（S02）；本件按同形语句面命名补 QltT'。      *)

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
  apply qeq_le.
  exact Hbc.
Qed.

(* ============================================================ *)
(* §1 定义（四段式之一：定义）                                    *)
(* ============================================================ *)

(* ---- 项 t_k := (−1)^k/(k+1) ---- *)
Definition l2e_term (k : nat) : Q :=
  q_pow (-1) k / (Z.of_nat (Datatypes.S k) # 1).

(* ---- 部分和 S_n := Σ_{k=0}^{n−1} t_k（n 项） ---- *)
Fixpoint l2e_alt_partial (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S m => l2e_alt_partial m + l2e_term m
  end.

(* ---- 项模量 m_k := 1/(k+1)（|t_k| 的闭式；对照 atan_mag） ---- *)
Definition l2e_mag (k : nat) : Q := 1 / (Z.of_nat (Datatypes.S k) # 1).

(* ---- 一步差：S_{n+1} − S_n == t_n；两步差 S_{n+2} − S_n == t_n + t_{n+1} ---- *)
Lemma l2e_gap1 : forall n : nat,
  l2e_alt_partial (Datatypes.S n) - l2e_alt_partial n == l2e_term n.
Proof. intro n. simpl. ring. Qed.

Lemma l2e_gap2 : forall n : nat,
  l2e_alt_partial (Datatypes.S (Datatypes.S n)) - l2e_alt_partial n ==
  l2e_term n + l2e_term (Datatypes.S n).
Proof. intro n. simpl. ring. Qed.

(* ============================================================ *)
(* §2 模量序结构（四段式之二/之三：恒等 + 单调）                   *)
(* ============================================================ *)

Lemma l2e_den_pos : forall k : nat, Qlt 0 (Z.of_nat (Datatypes.S k) # 1).
Proof.
  intro k. unfold Qlt. cbn [Qnum Qden].
  (* Z 层化：乘积归约后 Z.of_nat (S k) 依定义化为 Z.pos (Pos.of_succ_nat *)
  (* k)，取正性见证 Pos2Z.pos_is_pos                                    *)
  rewrite Z.mul_0_l, Z.mul_1_r.
  change (Z.of_nat (Datatypes.S k)) with (Z.pos (Pos.of_succ_nat k)).
  apply Pos2Z.pos_is_pos.
Qed.

Lemma l2e_den_neq : forall k : nat, ~ ((Z.of_nat (Datatypes.S k) # 1) == 0).
Proof. intro k. apply q_neq_of_lt. apply l2e_den_pos. Qed.

(* ---- 1/d == /d 桥（Qdiv 展平） ---- *)
Lemma l2e_mag_inv : forall k : nat, l2e_mag k == / (Z.of_nat (Datatypes.S k) # 1).
Proof. intro k. unfold l2e_mag, Qdiv. apply Qmult_1_l. Qed.

Lemma l2e_mag_pos : forall k : nat, Qlt 0 (l2e_mag k).
Proof.
  intro k.
  setoid_replace (l2e_mag k) with (/ (Z.of_nat (Datatypes.S k) # 1))
    by (apply (l2e_mag_inv k)).
  apply Qinv_lt_0_compat.
  apply l2e_den_pos.
Qed.

Lemma l2e_mag_nonneg : forall k : nat, Qle 0 (l2e_mag k).
Proof.
  intro k.
  apply (Qlt_le_weak 0 (l2e_mag k)).
  apply l2e_mag_pos.
Qed.

(* ---- 严格递减：m_{k+1} < m_k（倒数反序；对照 atan_mag_decr 证明芯） ---- *)
Lemma l2e_mag_lt : forall k : nat, Qlt (l2e_mag (Datatypes.S k)) (l2e_mag k).
Proof.
  intro k.
  setoid_replace (l2e_mag (Datatypes.S k)) with (/ (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1))
    by (apply (l2e_mag_inv (Datatypes.S k))).
  setoid_replace (l2e_mag k) with (/ (Z.of_nat (Datatypes.S k) # 1))
    by (apply (l2e_mag_inv k)).
  apply (proj1 (Qinv_lt_contravar (Z.of_nat (Datatypes.S k) # 1)
                                  (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)
                                  (l2e_den_pos k) (l2e_den_pos (Datatypes.S k)))).
  (* 收束：倒数反序的核=S k < S (S k)，Z 层由 inj_succ 化为后继一步严格序 *)
  unfold Qlt. cbn [Qnum Qden].
  rewrite (Znat.Nat2Z.inj_succ (Datatypes.S k)), !Z.mul_1_r.
  exact (Z.lt_succ_diag_r (Z.of_nat (Datatypes.S k))).
Qed.

(* ---- 模量差为正：m_k − m_{k+1} > 0 ---- *)
Lemma l2e_pair_diff_pos : forall k : nat,
  Qlt 0 (l2e_mag k - l2e_mag (Datatypes.S k)).
Proof.
  intro k.
  apply (proj1 (Qlt_minus_iff (l2e_mag (Datatypes.S k)) (l2e_mag k))).
  apply l2e_mag_lt.
Qed.

(* ---- 模量反序（N ≤ M ⟹ m_M ≤ m_N；对照 atan_inv_chain） ---- *)
Lemma l2e_mag_antitone : forall a b : nat, (a <= b)%nat -> Qle (l2e_mag b) (l2e_mag a).
Proof.
  intros a b Hab.
  destruct (Nat.eq_dec a b) as [Heq | Hne].
  - subst b. apply Qle_refl.
  - assert (Hlt : (a < b)%nat) by lia.
    apply (Qle_trans _ (/ (Z.of_nat (Datatypes.S b) # 1)) _).
    + apply qeq_le. apply (l2e_mag_inv b).
    + apply Qlt_le_weak.
      setoid_replace (l2e_mag a) with (/ (Z.of_nat (Datatypes.S a) # 1))
        by (apply (l2e_mag_inv a)).
      apply (proj1 (Qinv_lt_contravar (Z.of_nat (Datatypes.S a) # 1)
                                      (Z.of_nat (Datatypes.S b) # 1)
                                      (l2e_den_pos a) (l2e_den_pos b))).
      (* 收束：a < b 经后继单调（Z.succ_lt_mono）平移到 Z 层分母序 *)
      unfold Qlt. cbn [Qnum Qden]. rewrite !Znat.Nat2Z.inj_succ, !Z.mul_1_r.
      exact (proj1 (Z.succ_lt_mono (Z.of_nat a) (Z.of_nat b))
                   (proj1 (Znat.Nat2Z.inj_lt a b) Hlt)).
Qed.

(* ---- 单调：m_{k+1} ≤ m_k（对照 atan_mag_decr） ---- *)
Lemma l2e_mag_decr : forall k : nat, Qle (l2e_mag (Datatypes.S k)) (l2e_mag k).
Proof. intro k. apply l2e_mag_antitone. lia. Qed.

Lemma l2e_mag_decr_pos_step : forall n : nat, Qle 0 (l2e_mag n - l2e_mag (Datatypes.S n)).
Proof.
  intro n.
  apply (proj1 (Qle_minus_iff (l2e_mag (Datatypes.S n)) (l2e_mag n))).
  apply l2e_mag_decr.
Qed.

(* ============================================================ *)
(* §3 项恒等（|t_k|==m_k；成对项 |t_k+t_{k+1}|==m_k−m_{k+1}）      *)
(* ============================================================ *)

(* ---- |t_k| == m_k（对照 arctan_term_abs） ---- *)
Lemma l2e_term_abs : forall k : nat, Qabs (l2e_term k) == l2e_mag k.
Proof.
  intro k.
  unfold l2e_term, Qdiv.
  setoid_rewrite Qabs_Qmult.
  setoid_rewrite sc_abs_sign.
  setoid_rewrite Qabs_Qinv.
  assert (Hd : Qabs (Z.of_nat (Datatypes.S k) # 1) ==
               (Z.of_nat (Datatypes.S k) # 1)).
  { apply Qabs_pos. apply Qlt_le_weak. apply l2e_den_pos. }
  setoid_rewrite Hd.
  unfold l2e_mag, Qdiv.
  ring.
Qed.

(* ---- 成对项代数分解（对照 atan_pair_factor） ---- *)
Lemma l2e_pair_factor : forall k : nat,
  l2e_term k + l2e_term (Datatypes.S k) ==
  q_pow (-1) k * (l2e_mag k - l2e_mag (Datatypes.S k)).
Proof.
  intro k.
  unfold l2e_term, l2e_mag, Qdiv.
  rewrite (q_pow_succ (-1) k).
  ring.
Qed.

(* ---- 成对项界：|t_k + t_{k+1}| == m_k − m_{k+1}（对照 atan_pair_abs） ---- *)
Lemma l2e_pair_abs : forall k : nat,
  Qabs (l2e_term k + l2e_term (Datatypes.S k)) ==
  l2e_mag k - l2e_mag (Datatypes.S k).
Proof.
  intro k.
  apply (Qeq_trans _ (Qabs (q_pow (-1) k * (l2e_mag k - l2e_mag (Datatypes.S k)))) _).
  - apply (Qabs_wd (l2e_term k + l2e_term (Datatypes.S k))
                   (q_pow (-1) k * (l2e_mag k - l2e_mag (Datatypes.S k)))).
    apply l2e_pair_factor.
  - setoid_rewrite Qabs_Qmult.
    setoid_rewrite sc_abs_sign.
    assert (Hd : Qabs (l2e_mag k - l2e_mag (Datatypes.S k)) ==
                 l2e_mag k - l2e_mag (Datatypes.S k)).
    { apply Qabs_pos.
      apply (Qlt_le_weak 0 (l2e_mag k - l2e_mag (Datatypes.S k))).
      apply l2e_pair_diff_pos. }
    setoid_rewrite Hd.
    ring.
Qed.

(* ============================================================ *)
(* §4 奇偶双边夹逼（对照 atan_sign_even/odd）                     *)
(*   两翼：偶列不减（l2e_even_mono）、奇列不增（l2e_odd_mono）；   *)
(*   夹口：任一偶部分和 ≤ 任一奇部分和（l2e_even_le_odd），        *)
(*   隙宽显式：S_{2m+1} − S_{2m} == 1/(2m+1)（l2e_parity_gap）。   *)
(* ============================================================ *)

(* ---- 界步：S_{2j} ≤ S_{2j+1}（差 == t_{2j} == m_{2j} > 0） ---- *)
Lemma l2e_boundary : forall j : nat, Qle (l2e_alt_partial (2 * j)) (l2e_alt_partial (2 * j + 1)).
Proof.
  intro j.
  assert (H1 : (2 * j + 1)%nat = Datatypes.S (2 * j)) by (exact (Nat.add_1_r (2 * j))).
  rewrite H1.
  assert (Hpos : Qle 0 (l2e_alt_partial (Datatypes.S (2 * j)) - l2e_alt_partial (2 * j))).
  { rewrite (l2e_gap1 (2 * j)).
    apply (Qle_trans _ (l2e_mag (2 * j)) _).
    - apply (Qlt_le_weak 0 (l2e_mag (2 * j))). apply l2e_mag_pos.
    - apply qeq_le.
      unfold l2e_term.
      rewrite (atan_sign_even j).
      unfold l2e_mag, Qdiv.
      ring. }
  apply (proj2 (Qle_minus_iff (l2e_alt_partial (2 * j))
                              (l2e_alt_partial (Datatypes.S (2 * j))))).
  exact Hpos.
Qed.

(* ---- 反向界步：S_{2j} ≤ S_{2j−1}（j=0 时 nat 截断为平凡） ---- *)
Lemma l2e_boundary_rev : forall j : nat,
  Qle (l2e_alt_partial (2 * j)) (l2e_alt_partial (2 * j - 1)).
Proof.
  intro j. destruct j as [| j'].
  - apply Qle_refl.
  - replace (2 * Datatypes.S j')%nat with (2 * j' + 2)%nat by (exact (eq_sym (Nat.mul_succ_r 2 j'))).
    replace (2 * j' + 2 - 1)%nat with (2 * j' + 1)%nat by lia.
    replace (2 * j' + 2)%nat with (Datatypes.S (2 * j' + 1)) by (exact (eq_sym (Nat.add_succ_r (2 * j') 1))).
    assert (Hpos : Qle 0 (l2e_alt_partial (2 * j' + 1) -
                          l2e_alt_partial (Datatypes.S (2 * j' + 1)))).
    { assert (Hd : l2e_alt_partial (2 * j' + 1) -
                   l2e_alt_partial (Datatypes.S (2 * j' + 1)) ==
                   l2e_mag (2 * j' + 1)).
      { apply (Qeq_trans _ (- (l2e_term (2 * j' + 1))) _).
        - pose proof (l2e_gap1 (2 * j' + 1)) as Hg.
          rewrite <- Hg. ring.
        - unfold l2e_term.
          rewrite (atan_sign_odd j').
          unfold l2e_mag, Qdiv.
          ring. }
      rewrite Hd. apply l2e_mag_nonneg. }
    apply (proj2 (Qle_minus_iff (l2e_alt_partial (Datatypes.S (2 * j' + 1)))
                                (l2e_alt_partial (2 * j' + 1)))).
    exact Hpos.
Qed.

(* ---- 偶步：S_{2j} ≤ S_{2j+2}（差 == 成对项 == m_{2j}−m_{2j+1} ≥ 0） ---- *)
(* ---- 偶对恒等（纯代数）：t_{2j}+t_{2j+1} == m_{2j}−m_{2j+1} ---- *)
Lemma l2e_even_pair_factor : forall j : nat,
  l2e_mag (2 * j) - l2e_mag (Datatypes.S (2 * j)) ==
  l2e_term (2 * j) + l2e_term (Datatypes.S (2 * j)).
Proof.
  intro j.
  unfold l2e_term, l2e_mag, Qdiv.
  rewrite (q_pow_succ (-1) (2 * j)).
  rewrite (atan_sign_even j).
  ring.
Qed.

Lemma l2e_even_step : forall j : nat, Qle (l2e_alt_partial (2 * j)) (l2e_alt_partial (2 * j + 2)).
Proof.
  intro j.
  assert (H2 : (2 * j + 2)%nat = Datatypes.S (Datatypes.S (2 * j))) by lia.
  rewrite H2.
  assert (Hpos : Qle 0 (l2e_alt_partial (Datatypes.S (Datatypes.S (2 * j))) -
                        l2e_alt_partial (2 * j))).
  { rewrite (l2e_gap2 (2 * j)).
    apply (Qle_trans _ (l2e_mag (2 * j) - l2e_mag (Datatypes.S (2 * j))) _).
    - apply l2e_mag_decr_pos_step.
    - apply qeq_le. apply l2e_even_pair_factor. }
  apply (proj2 (Qle_minus_iff (l2e_alt_partial (2 * j))
                              (l2e_alt_partial (Datatypes.S (Datatypes.S (2 * j)))))).
  exact Hpos.
Qed.

(* ---- 奇步：S_{2j+3} ≤ S_{2j+1}（差反向：−成对项 == m_{2j+1}−m_{2j+2} ≥ 0） ---- *)
Lemma l2e_odd_step : forall j : nat, Qle (l2e_alt_partial (2 * j + 3)) (l2e_alt_partial (2 * j + 1)).
Proof.
  intro j.
  assert (H3 : (2 * j + 3)%nat = Datatypes.S (Datatypes.S (2 * j + 1))) by lia.
  rewrite H3.
  assert (Hpos : Qle 0 (l2e_alt_partial (2 * j + 1) -
                        l2e_alt_partial (Datatypes.S (Datatypes.S (2 * j + 1))))).
  { assert (Hg : l2e_alt_partial (2 * j + 1) -
                 l2e_alt_partial (Datatypes.S (Datatypes.S (2 * j + 1))) ==
                 l2e_mag (2 * j + 1) - l2e_mag (Datatypes.S (2 * j + 1))).
    { pose proof (l2e_gap2 (2 * j + 1)) as Hfwd.
      assert (Hpf : l2e_term (2 * j + 1) + l2e_term (Datatypes.S (2 * j + 1)) ==
                    - (l2e_mag (2 * j + 1) - l2e_mag (Datatypes.S (2 * j + 1)))).
      { unfold l2e_term, l2e_mag, Qdiv.
        rewrite (q_pow_succ (-1) (2 * j + 1)).
        rewrite (atan_sign_odd j).
        ring. }
      apply (Qeq_trans _ (- (l2e_term (2 * j + 1) + l2e_term (Datatypes.S (2 * j + 1)))) _).
      - rewrite <- (l2e_gap2 (2 * j + 1)). ring.
      - rewrite Hpf. ring. }
    rewrite Hg.
    apply (l2e_mag_decr_pos_step (2 * j + 1)). }
  apply (proj2 (Qle_minus_iff (l2e_alt_partial (Datatypes.S (Datatypes.S (2 * j + 1))))
                              (l2e_alt_partial (2 * j + 1)))).
  exact Hpos.
Qed.

(* ---- 偶列单调（沿 d 不减） ---- *)
Lemma l2e_even_mono : forall d j : nat,
  Qle (l2e_alt_partial (2 * j)) (l2e_alt_partial (2 * (j + d))).
Proof.
  intros d j. induction d as [| d IH].
  - replace (2 * (j + 0))%nat with (2 * j)%nat by ring. apply Qle_refl.
  - replace (2 * (j + Datatypes.S d))%nat with (2 * (j + d) + 2)%nat by (rewrite (Nat.add_succ_r j d); symmetry; apply Nat.mul_succ_r).
    apply (Qle_trans _ (l2e_alt_partial (2 * (j + d))) _).
    + exact IH.
    + exact (l2e_even_step (j + d)).
Qed.

(* ---- 奇列单调（沿 d 不增） ---- *)
Lemma l2e_odd_mono : forall d k : nat,
  Qle (l2e_alt_partial (2 * (k + d) + 1)) (l2e_alt_partial (2 * k + 1)).
Proof.
  intros d k. induction d as [| d IH].
  - replace (2 * (k + 0) + 1)%nat with (2 * k + 1)%nat by ring. apply Qle_refl.
  - replace (2 * (k + Datatypes.S d) + 1)%nat with (2 * (k + d) + 3)%nat by lia.
    apply (Qle_trans _ (l2e_alt_partial (2 * (k + d) + 1)) _).
    + exact (l2e_odd_step (k + d)).
    + exact IH.
Qed.

(* ---- 夹逼核心：任一偶部分和 ≤ 任一奇部分和 ---- *)
Lemma l2e_even_le_odd : forall j k : nat,
  Qle (l2e_alt_partial (2 * j)) (l2e_alt_partial (2 * k + 1)).
Proof.
  intros j k.
  destruct (le_lt_dec j k) as [Hjk | Hkj].
  - (* j ≤ k：S_{2j} ≤_{偶列} S_{2k} ≤_{界步} S_{2k+1} *)
    replace (2 * k + 1)%nat with (2 * (j + (k - j)) + 1)%nat by lia.
    apply (Qle_trans _ (l2e_alt_partial (2 * (j + (k - j)))) _).
    + exact (l2e_even_mono (k - j) j).
    + exact (l2e_boundary (j + (k - j))).
  - (* k < j：S_{2j} ≤_{反向界步} S_{2j−1} ≤_{奇列} S_{2k+1} *)
    apply (Qle_trans _ (l2e_alt_partial (2 * j - 1)) _).
    + exact (l2e_boundary_rev j).
    + replace (2 * j - 1)%nat with (2 * (k + (j - k - 1)) + 1)%nat by lia.
      exact (l2e_odd_mono (j - k - 1) k).
Qed.

(* ---- 隙宽显式：S_{2m+1} − S_{2m} == 1/(2m+1) ---- *)
Lemma l2e_parity_gap : forall m : nat,
  l2e_alt_partial (2 * m + 1) - l2e_alt_partial (2 * m) == l2e_mag (2 * m).
Proof.
  intro m.
  assert (H1 : (2 * m + 1)%nat = Datatypes.S (2 * m)) by (exact (Nat.add_1_r (2 * m))).
  rewrite H1.
  rewrite (l2e_gap1 (2 * m)).
  unfold l2e_term.
  rewrite (atan_sign_even m).
  unfold l2e_mag, Qdiv.
  ring.
Qed.

(* ============================================================ *)
(* §5 尾界（四段式之四：Leibniz 余项；对照 atan_tail_bound）       *)
(*   m ≤ n ⟹ |S_n − S_m| ≤ m_m == 1/(m+1)（显式公式）            *)
(* ============================================================ *)

Lemma l2e_tail_bound : forall m n : nat, (m <= n)%nat ->
  Qle (Qabs (l2e_alt_partial n - l2e_alt_partial m)) (l2e_mag m).
Proof.
  assert (Hgen : forall (d m n : nat), (m <= n)%nat -> (n - m)%nat = d ->
    Qle (Qabs (l2e_alt_partial n - l2e_alt_partial m)) (l2e_mag m)).
  { induction d as [d IH] using lt_wf_ind.
    intros m n Hmn Hd.
    destruct (Nat.leb (Datatypes.S (Datatypes.S m)) n) eqn:E2.
    - (* m + 2 ≤ n：三角拆分 + 成对项 + 归纳（下界 m+2） *)
      apply Nat.leb_le in E2.
      apply (Qle_trans _ (Qabs ((l2e_alt_partial n - l2e_alt_partial (Datatypes.S (Datatypes.S m))) +
                                (l2e_alt_partial (Datatypes.S (Datatypes.S m)) - l2e_alt_partial m))) _).
      + apply qeq_le.
        apply (Qabs_wd (l2e_alt_partial n - l2e_alt_partial m)
                       ((l2e_alt_partial n - l2e_alt_partial (Datatypes.S (Datatypes.S m))) +
                        (l2e_alt_partial (Datatypes.S (Datatypes.S m)) - l2e_alt_partial m))).
        ring.
      + apply (Qle_trans _ (Qabs (l2e_alt_partial n - l2e_alt_partial (Datatypes.S (Datatypes.S m))) +
                            Qabs (l2e_alt_partial (Datatypes.S (Datatypes.S m)) - l2e_alt_partial m)) _).
        * apply Qabs_triangle.
        * apply (Qle_trans _ (l2e_mag (Datatypes.S (Datatypes.S m)) +
                              (l2e_mag m - l2e_mag (Datatypes.S m))) _).
          -- apply Qplus_le_compat.
             ++ (* |S_n − S_{m+2}| ≤ m_{m+2}（IH，下界 m+2） *)
                apply (IH (n - Datatypes.S (Datatypes.S m))%nat).
                ** lia.
                ** lia.
                ** reflexivity.
             ++ (* |S_{m+2} − S_m| == |t_m + t_{m+1}| == m_m − m_{m+1} *)
                apply qeq_le.
                apply (Qeq_trans _ (Qabs (l2e_term m + l2e_term (Datatypes.S m))) _).
                ** apply (Qabs_wd (l2e_alt_partial (Datatypes.S (Datatypes.S m)) -
                                   l2e_alt_partial m)
                                  (l2e_term m + l2e_term (Datatypes.S m))).
                   exact (l2e_gap2 m).
                ** apply l2e_pair_abs.
          -- (* m_{m+2} ≤ m_{m+1} ⟹ 和 ≤ m_{m+1} + (m_m − m_{m+1}) == m_m *)
             apply (Qle_trans _ (l2e_mag (Datatypes.S m) +
                                 (l2e_mag m - l2e_mag (Datatypes.S m))) _).
             ++ apply Qplus_le_compat.
                ** apply l2e_mag_decr.
                ** apply Qle_refl.
             ++ apply qeq_le. ring.
    - (* n ≤ S m：n = m 或 n = S m *)
      apply Nat.leb_gt in E2.
      destruct (Nat.eq_dec m n) as [Heq | Hne].
      + (* n = m：差 0 ≤ m_m *)
        subst n.
        apply (Qle_trans _ 0 _).
        * apply qeq_le.
          apply (Qabs_wd (l2e_alt_partial m - l2e_alt_partial m) 0).
          ring.
        * apply l2e_mag_nonneg.
      + (* n = S m：差 == |t_m| == m_m *)
        assert (Hn : n = Datatypes.S m) by lia.
        subst n.
        apply qeq_le.
        apply (Qeq_trans _ (Qabs (l2e_term m)) _).
        * apply (Qabs_wd (l2e_alt_partial (Datatypes.S m) - l2e_alt_partial m) (l2e_term m)).
          exact (l2e_gap1 m).
        * apply l2e_term_abs.
  }
  intros m n Hmn.
  apply (Hgen (n - m)%nat m n Hmn). reflexivity.
Qed.

(* ============================================================ *)
(* §6 出口二（QleT' 化）：l2e_alt_two_sided                       *)
(* ============================================================ *)

Theorem l2e_alt_two_sided : forall m n : nat, (m <= n)%nat ->
  QleT' (Qabs (l2e_alt_partial n - l2e_alt_partial m)) (1 / ((Z.of_nat m + 1) # 1)).
Proof.
  intros m n Hmn.
  apply (qleT'_weaken _ (l2e_mag m) _).
  - apply l2e_tail_bound. exact Hmn.
  - assert (Hb : (Z.of_nat m + 1)%Z = Z.of_nat (Datatypes.S m)) by (exact (eq_trans (Z.add_1_r (Z.of_nat m)) (eq_sym (Znat.Nat2Z.inj_succ m)))).
    unfold l2e_mag. rewrite Hb. reflexivity.
Qed.

(* ============================================================ *)
(* §7 出口三：显式模量 N := S(ceil(1/eps))（Qceiling）+ sigT 柯西件 *)
(*   （对照 arctan_partial_cauchy；见证 N 由 Qround 的            *)
(*   Qceiling 显式给出，可抽取）                                  *)
(* ============================================================ *)

Definition l2e_modulus (eps : Q) : nat :=
  Datatypes.S (Z.to_nat (Qceiling (Qinv eps))).

Lemma l2e_modulus_bound : forall eps : Q, Qlt 0 eps ->
  Qlt (l2e_mag (l2e_modulus eps)) eps.
Proof.
  intros eps Heps.
  assert (Hx0 : Qlt 0 (Qinv eps)) by (apply Qinv_lt_0_compat; exact Heps).
  assert (Hcq : Qle 0 (Qceiling (Qinv eps) # 1)).
  { apply (Qle_trans 0 (Qinv eps) (Qceiling (Qinv eps) # 1)).
    - apply (Qlt_le_weak 0 (Qinv eps)). exact Hx0.
    - apply Qle_ceiling. }
  assert (Hcpos : (0 <= Qceiling (Qinv eps))%Z).
  { unfold Qle in Hcq. cbn [Qnum Qden] in Hcq.
    rewrite Z.mul_0_l, Z.mul_1_r in Hcq. exact Hcq. }
  assert (Hstep : Qlt (Qinv eps) ((Z.succ (Qceiling (Qinv eps))) # 1)).
  { apply (Qle_lt_trans (Qinv eps) (Qceiling (Qinv eps) # 1)
                        ((Z.succ (Qceiling (Qinv eps))) # 1)).
    - apply Qle_ceiling.
    - unfold Qlt, Qle. cbn [Qnum Qden]. rewrite !Z.mul_1_r.
      exact (Z.lt_succ_diag_r (Qceiling (Qinv eps))). }
  assert (Hz : (Z.succ (Qceiling (Qinv eps)) = Z.of_nat (l2e_modulus eps))%Z)
    by (unfold l2e_modulus; lia).
  assert (Hmul : Qlt (Qinv eps * eps) ((Z.of_nat (l2e_modulus eps) # 1) * eps)).
  { apply (Qmult_lt_compat_r (Qinv eps) (Z.of_nat (l2e_modulus eps) # 1) eps Heps).
    rewrite <- Hz. exact Hstep. }
  setoid_replace (Qinv eps * eps) with 1%Q in Hmul.
  2: { field. intro Hzz. apply (Qlt_not_eq 0 eps Heps). exact (Qeq_sym _ _ Hzz). }
  setoid_replace ((Z.of_nat (l2e_modulus eps) # 1) * eps)
    with (eps * (Z.of_nat (l2e_modulus eps) # 1)) in Hmul by ring.
  assert (Hd1 : Qlt 0 (Z.of_nat (l2e_modulus eps) # 1)).
  { unfold Qlt. cbn [Qnum Qden]. rewrite Z.mul_0_l, Z.mul_1_r.
    assert (Hge : (1 <= Z.of_nat (l2e_modulus eps))%Z).
    { (* 模量=S(Z.to_nat _)：非负性（Nat2Z.is_nonneg）经后继单调前向给出 1<=_ *)
      unfold l2e_modulus. rewrite Znat.Nat2Z.inj_succ.
      exact (proj1 (Z.succ_le_mono 0 (Z.of_nat (Z.to_nat (Qceiling (Qinv eps)))))
                   (Znat.Nat2Z.is_nonneg (Z.to_nat (Qceiling (Qinv eps))))). }
    apply (Z.lt_le_trans 0 1 (Z.of_nat (l2e_modulus eps)) (Pos2Z.pos_is_pos 1) Hge). }
  assert (Hd2 : Qlt 0 (Z.of_nat (Datatypes.S (l2e_modulus eps)) # 1))
    by (apply (l2e_den_pos (l2e_modulus eps))).
  assert (Hlt2 : Qlt (Z.of_nat (l2e_modulus eps) # 1)
                     (Z.of_nat (Datatypes.S (l2e_modulus eps)) # 1))
    by (unfold Qlt; cbn [Qnum Qden];
        rewrite Znat.Nat2Z.inj_succ, !Z.mul_1_r;
        exact (Z.lt_succ_diag_r (Z.of_nat (l2e_modulus eps)))).
  setoid_replace (l2e_mag (l2e_modulus eps))
    with (/ (Z.of_nat (Datatypes.S (l2e_modulus eps)) # 1))
    by (apply (l2e_mag_inv (l2e_modulus eps))).
  apply (Qle_lt_trans _ (/ (Z.of_nat (l2e_modulus eps) # 1)) _).
  - apply Qlt_le_weak.
    apply (proj1 (Qinv_lt_contravar (Z.of_nat (l2e_modulus eps) # 1)
                                    (Z.of_nat (Datatypes.S (l2e_modulus eps)) # 1)
                                    Hd1 Hd2)).
    exact Hlt2.
  - apply Qlt_shift_inv_r.
    + exact Hd1.
    + exact Hmul.
Qed.

(* ---- 出口三：sigT 柯西模量（N 显式：ceil(1/eps)+1，可抽取） ---- *)
Theorem l2e_cauchy_modulus : forall eps : Q, QltT' 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    QltT' (Qabs (l2e_alt_partial n - l2e_alt_partial m)) eps).
Proof.
  intros eps Heps.
  assert (Hlt : Qlt 0 eps) by (apply (QltT'_to_Qlt 0 eps Heps)).
  exists (l2e_modulus eps).
  intros m n HNm HNn.
  apply Qlt_to_QltT'.
  destruct (Nat.leb m n) eqn:E.
  - (* m ≤ n：|S_n − S_m| ≤ m_m ≤ m_N < eps *)
    apply Nat.leb_le in E.
    apply (Qle_lt_trans _ (l2e_mag (l2e_modulus eps)) _).
    + apply (Qle_trans _ (l2e_mag m) _).
      * apply l2e_tail_bound. exact E.
      * apply l2e_mag_antitone.
        apply NatLe_drop in HNm. exact HNm.
    + exact (l2e_modulus_bound eps Hlt).
  - (* n < m：Qabs_Qminus 对折后同链（用 n） *)
    apply Nat.leb_gt in E.
    apply (Qle_lt_trans _ (l2e_mag (l2e_modulus eps)) _).
    + apply (Qle_trans _ (l2e_mag n) _).
      * rewrite Qabs_Qminus. apply (l2e_tail_bound n m). lia.
      * apply l2e_mag_antitone.
        apply NatLe_drop in HNn. lia.
    + exact (l2e_modulus_bound eps Hlt).
Qed.

(* ============================================================ *)
(* §8 审计注记（文末 Print Assumptions 追印）                     *)
(* ============================================================ *)

Print Assumptions l2e_alt_two_sided.
Print Assumptions l2e_cauchy_modulus.
Print Assumptions l2e_parity_gap.
Print Assumptions l2e_even_le_odd.
