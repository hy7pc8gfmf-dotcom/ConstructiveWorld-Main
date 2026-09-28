(* ==========================================================================)
   abl_W9_pi_widen_13.v — π 零点唯一桥扩域消融（上界 2 → 7/2）
   源件: ConstructiveWorld_Live/S10_KVQuantTrig.v（只读对照）。
   使命: abl13_cos_pi_half_unique_widened2：
     forall w, 3/2 < w -> w < 7/2 -> cos w == 0 -> w == cos_pi_half。
     源件 cos_pi_half_unique（S10:8610）槽 2=扩域消融轴；既有 widened 形
     cos_pi_half_unique_widened（S10:9465）已把上界 5/3 放宽到 2，本件
     为该轴第二步：2→7/2。
   数学内核：w ∈ (2,7/2) 段 cos 无零——构造性证法：
   (i)  尾偶配对归纳：k ≥ 4、t² ≤ 49/4 ⟹ cos_partial k t ≤ cos_partial 4 t
        （项 a_j = |t|^{2j}/(2j)! 自 j ≥ 5 递减，偶步 −(a_{2m+1}−a_{2m+2}) ≤ 0）；
   (ii) S4 锚：换元 s := t²−4 ∈ [0,33/4]，
        cos_partial 4 t + 2/5 == (s⁴−40s³+1104s²−9152s−640)/40320 ≤ −640/40320 < 0
        （两组支配：s³(s−40) ≤ 0、s(1104s−9152) ≤ 0——一次换元纯有理支配，
         免微积分、免大数浮点数值计算）；
   (iii) 装配：逐点 Q 可判定分支 w_n ≤ 2（承袭 widened 形逆界装配）/
        w_n > 2（锚 −2/5 与对角界 |cos_partial n w_n| < eps/8 相容仅当
        eps > 16/5，此时 |w_n−z_n| ≤ 2 < 16/5 ≤ eps 直接放行）。
   依赖: 现势库实存件 S01/S02/S03/S10（隔离池 /tmp/x13pool，自基池现势链真拷）。
   构造性: 纯构造性 / 无经典面 / 零承认词面 / 全件 Qed 闭合；
     尾 Print Assumptions 全 Closed；Extraction 后 Obj.magic=0。
   编译配方: cd /tmp/x13pool && source <workspace>/Live/toolchain/env.sh &&
     bash <workspace>/Live/toolchain/cpu_guard.sh -- rocq c -q -native-compiler no
     -Q /tmp/x13pool "" abl_W9_pi_widen_13.v（cwd 异地、节流）。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround ZArith.
From Stdlib Require Import Lia QArith.Qminmax.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.

(* ============================================================ *)
(* Part 1 · Q 层微机械（平方非负/绝对值/除法保序/符号因子）      *)
(* ============================================================ *)

(* 平方非负：t² ≥ 0（构造性二分，零经典） *)
Lemma abl13_qsq_nonneg : forall t : Q, Qle 0 (t * t).
Proof.
  intro t.
  destruct (Qlt_le_dec 0 t) as [Hpos | Hneg].
  - apply (Qmult_le_0_compat t t).
    + apply Qlt_le_weak. exact Hpos.
    + apply Qlt_le_weak. exact Hpos.
  - assert (Hopp : Qle 0 (- t)).
    { assert (H := Qopp_le_compat t 0 Hneg).
      assert (Hz : - 0 == 0) by ring.
      rewrite Hz in H. exact H. }
    assert (Hr : t * t == (- t) * (- t)) by ring.
    rewrite Hr.
    apply (Qmult_le_0_compat (- t) (- t) Hopp Hopp).
Qed.

(* t² == |t|·|t| *)
Lemma abl13_qsq_abs : forall t : Q, t * t == Qabs t * Qabs t.
Proof.
  intro t.
  assert (H1 : Qabs (t * t) == Qabs t * Qabs t) by apply Qabs_Qmult.
  assert (H2 : Qabs (t * t) == t * t) by (apply Qabs_pos; apply abl13_qsq_nonneg).
  rewrite <- H1. symmetry. exact H2.
Qed.

(* 正模除法保序：0 < M、a·M ≤ b·M ⟹ a ≤ b（Qle_dec 构造性二分） *)
Lemma abl13_qdiv_le : forall a b M : Q, Qlt 0 M -> Qle (a * M) (b * M) -> Qle a b.
Proof.
  intros a b M HM H.
  destruct (Qlt_le_dec b a) as [Hlt | Hle].
  - exfalso.
    assert (Hlt2 : Qlt (b * M) (a * M)) by (apply (Qmult_lt_compat_r b a M); [exact HM | exact Hlt]).
    exact (Qlt_irrefl (b * M) (Qlt_le_trans (b * M) (a * M) (b * M) Hlt2 H)).
  - exact Hle.
Qed.

(* |x| ≤ c 由两侧界（0 ≤ c） *)
Lemma abl13_qabs_le : forall x c : Q, Qle 0 c -> Qle (- c) x -> Qle x c -> Qle (Qabs x) c.
Proof.
  intros x c Hc0 Hlo Hhi.
  destruct (Qlt_le_dec 0 x) as [Hpos | Hnonpos].
  - rewrite (Qabs_pos x (Qlt_le_weak 0 x Hpos)). exact Hhi.
  - assert (Hnx : Qle 0 (- x)).
    { assert (H := Qopp_le_compat x 0 Hnonpos).
      assert (Hz : - 0 == 0) by ring.
      rewrite Hz in H. exact H. }
    rewrite <- (Qabs_opp x).
    rewrite (Qabs_pos (- x) Hnx).
    assert (Hc : Qle (- x) c).
    { assert (H := Qopp_le_compat (- c) x Hlo).
      assert (Hr : - (- c) == c) by ring.
      rewrite Hr in H. exact H. }
    exact Hc.
Qed.

(* |x| < d ⟹ −d < x *)
Lemma abl13_qabs_lt_opp : forall x d : Q, Qlt (Qabs x) d -> Qlt (- d) x.
Proof.
  intros x d H.
  assert (Hle : Qle (- x) (Qabs x)).
  { rewrite <- (Qabs_opp x). apply Qle_Qabs. }
  assert (Hlt : Qlt (- x) d) by (apply (Qle_lt_trans (- x) (Qabs x) d); [exact Hle | exact H]).
  assert (Hr : - (- x) == x) by ring.
  rewrite <- Hr.
  apply (Qopp_lt_compat (- x) d Hlt).
Qed.

(* 非正项右加消去：z ≤ 0 ⟹ x + z ≤ x
   （四显参 Qplus_le_compat + ring 消 +0。裸 apply Qplus_le_compat
    于 RHS=cos_partial (2·S m') t 时统一器将该索引头归约暴露 Qplus 形而错误
    分解 RHS，本 helper 结论形 ?x+?z ≤ ?x
    右端为裸变元，分解陷阱结构性排除。） *)
Lemma abl13_qplus_nonpos_le : forall x z : Q, Qle z 0 -> Qle (x + z) x.
Proof.
  intros x z Hz.
  assert (H0 : x + 0 == x) by ring.
  apply (Qle_trans _ (x + 0) _).
  - apply (Qplus_le_compat x x z 0); [apply Qle_refl | exact Hz].
  - rewrite H0. apply Qle_refl.
Qed.

(* (−1) 的偶次幂/奇次幂（S 形指标，供 cos_term 符号改写） *)
Lemma abl13_qpow_neg1_S2 : forall n : nat, q_pow (-1) (Datatypes.S (Datatypes.S n)) == q_pow (-1) n.
Proof.
  intro n. cbn [q_pow]. ring.
Qed.

Lemma abl13_qpow_neg1_even : forall m : nat, q_pow (-1) (2 * m) == 1.
Proof.
  induction m as [| m IH].
  - reflexivity.
  - replace (2 * (Datatypes.S m))%nat with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
    rewrite abl13_qpow_neg1_S2. exact IH.
Qed.

Lemma abl13_qpow_neg1_odd : forall m : nat, q_pow (-1) (Datatypes.S (2 * m)) == (-1)%Q.
Proof.
  induction m as [| m IH].
  - replace (Datatypes.S (2 * 0))%nat with (Datatypes.S 0)%nat by lia.
    cbn [q_pow]. ring.
  - replace (Datatypes.S (2 * (Datatypes.S m)))%nat
      with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat by lia.
    rewrite abl13_qpow_neg1_S2. exact IH.
Qed.

(* 偶指数幂的绝对值恒等：t^{2k} == |t|^{2k}（经 Qabs + 偶幂非负） *)
Lemma abl13_qpow_even_abs : forall (k : nat) (t : Q), q_pow t (2 * k) == q_pow (Qabs t) (2 * k).
Proof.
  intros k t.
  assert (Hpos : Qle 0 (q_pow t (2 * k))).
  { induction k as [| k IHk].
    - replace (2 * 0)%nat with 0%nat by lia. cbn [q_pow]. unfold Qle; simpl; lia.
    - replace (2 * (Datatypes.S k))%nat with (Datatypes.S (Datatypes.S (2 * k)))%nat by lia.
      cbn [q_pow].
      assert (Hr : t * (t * q_pow t (2 * k)) == (t * t) * q_pow t (2 * k)) by ring.
      rewrite Hr.
      apply (Qmult_le_0_compat (t * t) (q_pow t (2 * k))).
      + apply abl13_qsq_nonneg.
      + exact IHk. }
  assert (H1 : q_pow t (2 * k) == Qabs (q_pow t (2 * k))).
  { symmetry. apply Qabs_pos. exact Hpos. }
  assert (H2 : Qabs (q_pow t (2 * k)) == q_pow (Qabs t) (2 * k)).
  { rewrite q_pow_abs. reflexivity. }
  rewrite H1. rewrite H2. reflexivity.
Qed.

(* 级数项绝对值形：a_j(t) := |t|^{2j}/(2j)! *)
Definition abl13_a (j : nat) (t : Q) : Q := q_pow (Qabs t) (2 * j) / q_fact (2 * j).

Lemma abl13_a_nonneg : forall j t, Qle 0 (abl13_a j t).
Proof.
  intros j t. unfold abl13_a. apply q_pow_fact_nonneg. apply Qabs_nonneg.
Qed.

(* q_fact、字面 Z-Q 形非零（field 侧条件备料） *)
Lemma abl13_qfact_neq0 : forall k : nat, ~ (q_fact k == 0).
Proof.
  intros k Heq.
  assert (H : Qlt 0 (q_fact k)) by apply q_fact_pos.
  rewrite Heq in H. exact (Qlt_irrefl 0 H).
Qed.

Lemma abl13_zQ_neq0 : forall k : nat, ~ ((Z.of_nat (Datatypes.S k) # 1) == 0).
Proof.
  intros k Heq.
  assert (H : Qlt 0 ((Z.of_nat (Datatypes.S k) # 1))).
  { unfold Qlt. simpl. lia. }
  rewrite Heq in H. exact (Qlt_irrefl 0 H).
Qed.

(* 除法消去：X/D·D == X（D ≠ 0；Qdiv 展开 + Qmult_inv_r + 环重排，免 field） *)
Lemma abl13_qdiv_cancel : forall X D : Q, ~ (D == 0) -> (X / D) * D == X.
Proof.
  intros X D HD.
  unfold Qdiv.
  rewrite <- Qmult_assoc.
  assert (Hinv : Qinv D * D == 1).
  { rewrite (Qmult_comm (Qinv D) D). apply Qmult_inv_r. exact HD. }
  rewrite Hinv.
  rewrite Qmult_1_r.
  reflexivity.
Qed.

(* 正底幂非负 *)
Lemma abl13_qpow_nonneg : forall (k : nat) (A : Q), Qle 0 A -> Qle 0 (q_pow A k).
Proof.
  intros k A H.
  induction k as [| k IH].
  - cbn [q_pow]. unfold Qle; simpl; lia.
  - cbn [q_pow]. apply (Qmult_le_0_compat A (q_pow A k)); [exact H | exact IH].
Qed.

(* 项递减：j ≥ 2、t² ≤ 49/4 ⟹ a(S j) ≤ a j
   （比值 a(S j)/a j == t²/((2j+1)(2j+2)) ≤ (49/4)/30 < 1；
     闭合走除法消去引理——Qdiv 展开 + Qmult_inv_r + 环重排，全程免 field） *)
Lemma abl13_a_decr : forall (j : nat) (t : Q), (2 <= j)%nat -> Qle (t * t) (49 / 4) ->
  Qle (abl13_a (Datatypes.S j) t) (abl13_a j t).
Proof.
  intros j t Hj Htt.
  assert (HA : t * t == Qabs t * Qabs t) by apply abl13_qsq_abs.
  (* 两新因子（Q 形）：Z1 := 2j+1 ≥ 5、Z2 := 2j+2 ≥ 6（j ≥ 2） *)
  assert (Hb1 : Qle 5 ((Z.of_nat (Datatypes.S (2 * j)) # 1))).
  { unfold Qle. simpl. lia. }
  assert (Hb2 : Qle 6 ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))).
  { unfold Qle. simpl. lia. }
  assert (Hb3 : Qle 30 ((Z.of_nat (Datatypes.S (2 * j)) # 1)
                        * (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))).
  { apply (Qle_trans 30 (6 * (Z.of_nat (Datatypes.S (2 * j)) # 1)) _).
    - unfold Qle. simpl. lia.
    - assert (Hr : (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)
                   * (Z.of_nat (Datatypes.S (2 * j)) # 1) ==
                   (Z.of_nat (Datatypes.S (2 * j)) # 1)
                   * (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)) by ring.
      rewrite <- Hr.
      apply (Qmult_le_compat_r 6 (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)
                                 (Z.of_nat (Datatypes.S (2 * j)) # 1)).
      + exact Hb2.
      + unfold Qle. simpl. lia. }
  assert (Hbridge : Qle (Qabs t * Qabs t)
                        ((Z.of_nat (Datatypes.S (2 * j)) # 1)
                         * (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))).
  { apply (Qle_trans _ (49 / 4) _).
    - rewrite <- HA. exact Htt.
    - apply (Qle_trans _ 30 _).
      + unfold Qle, Qdiv. simpl. lia.
      + exact Hb3. }
  (* 整除数 D' := Z2·(Z1·D0) 及其正性 *)
  assert (Hz2pos : Qlt 0 ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))).
  { apply (Qlt_le_trans 0 6 _); [unfold Qlt; simpl; lia | exact Hb2]. }
  assert (Hz1D0pos : Qlt 0 ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j))).
  { apply (Qmult_lt_0_compat _ _).
    - apply (Qlt_le_trans 0 5 _); [unfold Qlt; simpl; lia | exact Hb1].
    - apply q_fact_pos. }
  assert (HDpos : Qlt 0 ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                         ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j)))).
  { apply (Qmult_lt_0_compat _ _ Hz2pos Hz1D0pos). }
  (* a(S j) 的 cbn 展开形 *)
  assert (Hexpand : abl13_a (Datatypes.S j) t ==
                    (Qabs t * (Qabs t * q_pow (Qabs t) (2 * j))) /
                    ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                     ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j)))).
  { unfold abl13_a.
    replace (2 * (Datatypes.S j))%nat
      with (Datatypes.S (Datatypes.S (2 * j)))%nat by lia.
    cbn [q_pow q_fact]. reflexivity. }
  (* 消去一：a(S j)·D' == A²·P0 *)
  assert (Hcancel1 : abl13_a (Datatypes.S j) t *
                     ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                      ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j))) ==
                     (Qabs t * Qabs t) * q_pow (Qabs t) (2 * j)).
  { rewrite Hexpand.
    assert (Hstep : (Qabs t * (Qabs t * q_pow (Qabs t) (2 * j))) /
                    ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                     ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j))) *
                    ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                     ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j))) ==
                    (Qabs t * (Qabs t * q_pow (Qabs t) (2 * j)))).
    { apply abl13_qdiv_cancel.
      intro Heq.
      rewrite Heq in HDpos.
      exact (Qlt_irrefl 0 HDpos). }
    rewrite Hstep. ring. }
  (* 消去二：a j·D' == Z2·Z1·P0 *)
  assert (Hcancel2 : abl13_a j t *
                     ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                      ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j))) ==
                     ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                      (Z.of_nat (Datatypes.S (2 * j)) # 1)) * q_pow (Qabs t) (2 * j)).
  { unfold abl13_a. unfold Qdiv.
    assert (Hinv : Qinv (q_fact (2 * j)) * q_fact (2 * j) == 1).
    { rewrite (Qmult_comm (Qinv (q_fact (2 * j))) (q_fact (2 * j))).
      apply Qmult_inv_r. apply abl13_qfact_neq0. }
    assert (Hrr : (q_pow (Qabs t) (2 * j) * Qinv (q_fact (2 * j))) *
                  ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                   ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j))) ==
                  (((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                    (Z.of_nat (Datatypes.S (2 * j)) # 1)) * q_pow (Qabs t) (2 * j)) *
                  (Qinv (q_fact (2 * j)) * q_fact (2 * j))) by ring.
    rewrite Hrr. rewrite Hinv.
    rewrite Qmult_1_r. reflexivity. }
  apply (abl13_qdiv_le (abl13_a (Datatypes.S j) t) (abl13_a j t)
                       ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                        ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j)))).
  - exact HDpos.
  - rewrite Hcancel1. rewrite Hcancel2.
    assert (Hbr : (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                  (Z.of_nat (Datatypes.S (2 * j)) # 1) ==
                  (Z.of_nat (Datatypes.S (2 * j)) # 1) *
                  (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)) by ring.
    rewrite Hbr.
    apply (Qmult_le_compat_r (Qabs t * Qabs t)
            ((Z.of_nat (Datatypes.S (2 * j)) # 1)
             * (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))
            (q_pow (Qabs t) (2 * j))).
    + exact Hbridge.
    + apply abl13_qpow_nonneg. apply Qabs_nonneg.
Qed.

(* ============================================================ *)
(* Part 2 · S4 包络：k ≥ 4、t² ≤ 49/4 ⟹ cos_partial k t ≤ cos_partial 4 t *)
(* ============================================================ *)

(* 偶指标归纳：cos_partial (2m) ≤ cos_partial 4（m ≥ 2） *)
Lemma abl13_cp_even_le : forall (m : nat) (t : Q), (2 <= m)%nat -> Qle (t * t) (49 / 4) ->
  Qle (cos_partial (2 * m) t) (cos_partial 4 t).
Proof.
  intros m t. induction m as [| m IH]; intros Hm Htt.
  - exfalso. lia.
  - destruct m as [| m'].
    + exfalso. lia.
    + assert (Hunfold : cos_partial (2 * Datatypes.S (Datatypes.S m')) t ==
                        (cos_partial (2 * Datatypes.S m') t
                         + cos_term (Datatypes.S (2 * Datatypes.S m')) t)
                        + cos_term (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t).
      { replace (2 * Datatypes.S (Datatypes.S m'))%nat
          with (Datatypes.S (Datatypes.S (2 * Datatypes.S m')))%nat by lia.
        cbn [cos_partial]. reflexivity. }
      rewrite Hunfold.
      assert (Hc1 : cos_term (Datatypes.S (2 * Datatypes.S m')) t
                    == - abl13_a (Datatypes.S (2 * Datatypes.S m')) t).
      { unfold cos_term, abl13_a.
        rewrite abl13_qpow_neg1_odd.
        rewrite (abl13_qpow_even_abs (Datatypes.S (2 * Datatypes.S m')) t).
        ring. }
      assert (Hc2 : cos_term (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t
                    == abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t).
      { unfold cos_term, abl13_a.
        rewrite abl13_qpow_neg1_S2.
        rewrite abl13_qpow_neg1_even.
        rewrite (abl13_qpow_even_abs (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t).
        ring. }
      rewrite Hc1, Hc2.
      assert (Hneg : Qle (- abl13_a (Datatypes.S (2 * Datatypes.S m')) t
                          + abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t) 0).
      { assert (Hr : - abl13_a (Datatypes.S (2 * Datatypes.S m')) t
                     + abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t ==
                     - (abl13_a (Datatypes.S (2 * Datatypes.S m')) t
                        - abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t)) by ring.
        rewrite Hr.
        assert (Hz : - 0 == 0) by ring.
        rewrite <- Hz.
        apply (Qopp_le_compat 0 (abl13_a (Datatypes.S (2 * Datatypes.S m')) t -
                                 abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t)).
        apply (proj1 (Qle_minus_iff (abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t)
                                    (abl13_a (Datatypes.S (2 * Datatypes.S m')) t))).
        apply (abl13_a_decr (Datatypes.S (2 * Datatypes.S m')) t); [lia | exact Htt]. }
      assert (Hrr : (cos_partial (2 * Datatypes.S m') t
                     + (- abl13_a (Datatypes.S (2 * Datatypes.S m')) t))
                    + abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t ==
                    cos_partial (2 * Datatypes.S m') t
                    + ((- abl13_a (Datatypes.S (2 * Datatypes.S m')) t)
                       + abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t)) by ring.
      rewrite Hrr.
      destruct m' as [| m''].
      * (* m'=0（原 m=2）时 IH 前提 2≤S 0 不真（lia 判明），
           且 Qle_trans 一肢 cp 2 ≤ cp 4 数学为假（t²≤49/4<56 ⟹ cp4<cp2）
           ——本基例主目标改自反闭合：cp4 = cp2+（−a3+a4）与 LHS 逐项相同；
           注：具体指数 rewrite 须显式实例（evar 在 mul 头下不可解） *)
         (* X13 R7 修：LHS 长指数词面先归一为 3/4 短形（replace by reflexivity），
            免 Qle_refl 两侧词面差；Q 加法结合非转换可通，故再以 Hrb 重括号对齐 *)
         replace (abl13_a (Datatypes.S (2 * Datatypes.S 0)) t)
           with (abl13_a 3 t) by reflexivity.
         replace (abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S 0))) t)
           with (abl13_a 4 t) by reflexivity.
         assert (Hcp4 : cos_partial 4 t ==
                        (cos_partial (2 * Datatypes.S 0) t + cos_term 3 t)
                        + cos_term 4 t)
           by (cbn [cos_partial]; reflexivity).
         assert (Hc3 : cos_term 3 t == - abl13_a 3 t).
         { unfold cos_term, abl13_a.
           rewrite (abl13_qpow_neg1_odd 1).
           rewrite (abl13_qpow_even_abs 3 t).
           ring. }
         assert (Hc4 : cos_term 4 t == abl13_a 4 t).
         { unfold cos_term, abl13_a.
           rewrite (abl13_qpow_neg1_even 2).
           rewrite (abl13_qpow_even_abs 4 t).
           ring. }
         rewrite Hcp4. rewrite Hc3, Hc4.
         assert (Hrb : (cos_partial (2 * Datatypes.S 0) t + (- abl13_a 3 t))
                       + abl13_a 4 t
                       == cos_partial (2 * Datatypes.S 0) t
                          + (- abl13_a 3 t + abl13_a 4 t)) by ring.
         rewrite Hrb.
         apply Qle_refl.
      * apply (Qle_trans _ (cos_partial (2 * Datatypes.S (Datatypes.S m'')) t) _).
        -- apply abl13_qplus_nonpos_le. exact Hneg.
        -- apply IH; [lia | exact Htt].
Qed.

(* S4 包络主引理：k ≥ 4、t² ≤ 49/4 ⟹ cos_partial k t ≤ cos_partial 4 t
   （偶 k 直用偶归纳；奇 k = 2m+1 末项 −a(2m+1) ≤ 0 再挂偶归纳） *)
Lemma abl13_cp_le_s4 : forall (k : nat) (t : Q), (4 <= k)%nat -> Qle (t * t) (49 / 4) ->
  Qle (cos_partial k t) (cos_partial 4 t).
Proof.
  intros k t Hk Htt.
  destruct (Nat.Even_or_Odd k) as [[m Hm] | [m Hm]].
  - subst k. assert (Hm2 : (2 <= m)%nat) by lia.
    exact (abl13_cp_even_le m t Hm2 Htt).
  - subst k. assert (Hm2 : (2 <= m)%nat) by lia.
    replace (2 * m + 1)%nat with (Datatypes.S (2 * m))%nat by lia.
    cbn [cos_partial].
    assert (Hc : cos_term (Datatypes.S (2 * m)) t == - abl13_a (Datatypes.S (2 * m)) t).
    { unfold cos_term, abl13_a.
      rewrite abl13_qpow_neg1_odd.
      rewrite (abl13_qpow_even_abs (Datatypes.S (2 * m)) t).
      ring. }
    rewrite Hc.
    assert (Hneg : Qle (- abl13_a (Datatypes.S (2 * m)) t) 0).
    { assert (H := Qopp_le_compat 0 (abl13_a (Datatypes.S (2 * m)) t) (abl13_a_nonneg (Datatypes.S (2 * m)) t)).
      assert (Hz : - 0 == 0) by ring.
      rewrite Hz in H. exact H. }
    apply (Qle_trans _ (cos_partial (2 * m) t) _).
    + apply abl13_qplus_nonpos_le. exact Hneg.
    + exact (abl13_cp_even_le m t Hm2 Htt).
Qed.

(* ============================================================ *)
(* Part 3 · S4 锚：2 ≤ t ≤ 7/2 ⟹ cos_partial 4 t ≤ −2/5          *)
(*   换元 s := t²−4 ∈ [0,33/4]；                                 *)
(*   cos_partial 4 t + 2/5 == (s⁴−40s³+1104s²−9152s−640)/40320；  *)
(*   两组支配 s³(s−40) ≤ 0、s(1104s−9152) ≤ 0 ⟹ 分子 ≤ −640 < 0。 *)
(* ============================================================ *)

(* 窗内平方界：2 ≤ t ≤ 7/2 ⟹ t² ≤ 49/4 *)
Lemma abl13_sq_window : forall t : Q, Qle 2 t -> Qle t (7 / 2) -> Qle (t * t) (49 / 4).
Proof.
  intros t Ht2 Ht72.
  assert (Ht0 : Qle 0 t).
  { apply (Qle_trans 0 2 t); [unfold Qle; simpl; lia | exact Ht2]. }
  assert (Hc : (7 / 2) * t == t * (7 / 2)) by ring.
  assert (Hv : (7 / 2) * (7 / 2) == 49 / 4) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
  apply (Qle_trans _ ((7 / 2) * (7 / 2)) _).
  - apply (Qle_trans _ ((7 / 2) * t) _).
    + apply (Qmult_le_compat_r t (7 / 2) t); [exact Ht72 | exact Ht0].
    + rewrite Hc. apply (Qmult_le_compat_r t (7 / 2) (7 / 2)); [exact Ht72 | unfold Qle, Qdiv; simpl; lia].
  - rewrite Hv. apply Qle_refl.
Qed.

(* cos_partial 4 t == 1 − t²/2 + t⁴/24 − t⁶/720 + t⁸/40320（(t*t) 原子形，供换元改写） *)
Lemma abl13_cp4_G : forall t : Q,
  cos_partial 4 t ==
  1 - (t * t) / 2 + (t * t) * (t * t) / 24
    - (t * t) * (t * t) * (t * t) / 720
    + (t * t) * (t * t) * (t * t) * (t * t) / 40320.
Proof.
  intro t.
  (* cos_term 无 match 结构，限定 cbn 乃至全量 cbn 均因
     「无构头进展」拒展（两轮皆报 not a valid field equation）——
     先 cbn [cos_partial] 摊开和式，再 unfold cos_term 强制展开，
     后 cbn 归约数值系数，终由 field 闭合 *)
  cbn [cos_partial]. unfold cos_term. cbn.
  field; unfold Qeq; simpl; lia.
Qed.

(* G(u) + 2/5 的换元支配恒等式（纯 field） *)
Lemma abl13_G_P : forall u : Q,
  1 - u / 2 + u * u / 24 - u * u * u / 720 + u * u * u * u / 40320 + 2 / 5 ==
  ((u - 4) * (u - 4) * (u - 4) * (u - 4)
   - 40 * ((u - 4) * (u - 4) * (u - 4))
   + 1104 * ((u - 4) * (u - 4))
   - 9152 * (u - 4) - 640) * (1 / 40320).
Proof.
  intro u. unfold Qdiv. field; unfold Qeq; simpl; lia.
Qed.

Lemma abl13_cp4_le_neg25 : forall t : Q, Qle 2 t -> Qle t (7 / 2) ->
  Qle (cos_partial 4 t) (- (2 / 5)).
Proof.
  intros t Ht2 Ht72.
  assert (Hsq : Qle 4 (t * t)).
  { apply (Qle_trans _ (2 * t) _).
    - (* 注：Q 乘法不可换转换，2*t 与 t*2 词面须先归一再喂 _r
         （原 Qmult_le_compat_r 2 t 2 结论 2*2≤t*2 与目标 4≤2*t 失配） *)
      assert (Hc : t * 2 == 2 * t) by ring.
      rewrite <- Hc.
      replace 4 with (2 * 2) by reflexivity.
      apply (Qmult_le_compat_r 2 t 2); [exact Ht2 | unfold Qle; simpl; lia].
    - apply (Qmult_le_compat_r 2 t t); [exact Ht2 | apply (Qle_trans 0 2 t); [unfold Qle; simpl; lia | exact Ht2]]. }
  assert (Htt : Qle (t * t) (49 / 4)) by (apply abl13_sq_window; assumption).
  remember (t * t - 4) as s eqn:Hsdef.
  assert (Hs4 : t * t == s + 4) by (rewrite Hsdef; ring).
  assert (Hs0 : Qle 0 s) by (rewrite Hsdef; apply (proj1 (Qle_minus_iff 4 (t * t))); exact Hsq).
  assert (Hs33 : Qle s (33 / 4)).
  { rewrite Hsdef.
    apply (Qle_trans _ (49 / 4 - 4) _).
    - apply (Qplus_le_compat (t * t) (49 / 4) (- 4) (- 4)); [exact Htt | apply Qle_refl].
    - assert (Hr : 49 / 4 - 4 == 33 / 4) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      rewrite Hr. apply Qle_refl. }
  assert (HG : cos_partial 4 t ==
               1 - (s + 4) / 2 + (s + 4) * (s + 4) / 24
                 - (s + 4) * (s + 4) * (s + 4) / 720
                 + (s + 4) * (s + 4) * (s + 4) * (s + 4) / 40320).
  { rewrite abl13_cp4_G. rewrite Hs4. reflexivity. }
  assert (Hexp : cos_partial 4 t + 2 / 5 ==
                 ((s * s * s * s - 40 * (s * s * s) + 1104 * (s * s) - 9152 * s - 640))
                 * (1 / 40320)).
  { rewrite HG. rewrite (abl13_G_P (s + 4)).
    (* 注：改写残留 (s+4-4) 与 s 词面差（Q 减法非转换可通，
       reflexivity 败）——ring 多项式归一闭合 *)
    ring. }
  (* 支配一：s⁴ − 40s³ == s³(s−40) ≤ 0（0 ≤ s ≤ 33/4 < 40） *)
  assert (Hd1 : Qle (s * s * s * s - 40 * (s * s * s)) 0).
  { assert (Hs3 : Qle 0 (s * s * s)).
    { apply (Qmult_le_0_compat (s * s) s).
      - apply (Qmult_le_0_compat s s); exact Hs0.
      - exact Hs0. }
    (* 注：原 Hs40 块（proj1(Qle_minus_iff s 40) 结论 0≤40+s⁻ 与目标
         s−40≤0 错位，apply 必败）整块撤除——其唯一使用者 Hpos 已改为
         proj1 直证 0≤40-s，不再依赖 Hs40 *)
    assert (Hr : s * s * s * s - 40 * (s * s * s) == (s * s * s) * (s - 40)) by ring.
    rewrite Hr.
    assert (Hpos : Qle 0 ((s * s * s) * (40 - s))).
    { apply (Qmult_le_0_compat (s * s * s) (40 - s)).
      - exact Hs3.
      - (* 注：proj2(Qle_minus_iff (s-40) 0) 结论系 s-40≤0，与本目标
           0≤40-s 错位——改 proj1 直证 0≤40-s（由 s≤33/4≤40） *)
        apply (proj1 (Qle_minus_iff s 40)).
        apply (Qle_trans s (33 / 4) 40); [exact Hs33 | unfold Qle, Qdiv; simpl; lia]. }
    assert (Hneg0 := Qopp_le_compat 0 ((s * s * s) * (40 - s)) Hpos).
    assert (Hz : - 0 == 0) by ring.
    rewrite Hz in Hneg0.
    assert (Hr2 : - ((s * s * s) * (40 - s)) == (s * s * s) * (s - 40)) by ring.
    rewrite Hr2 in Hneg0. exact Hneg0. }
  (* 支配二：1104s² − 9152s == s(1104s−9152) ≤ 0（1104·(33/4) == 9108 < 9152） *)
  assert (Hd2 : Qle (1104 * (s * s) - 9152 * s) 0).
  { assert (Hb : Qle (1104 * s) 9108).
    { assert (H := Qmult_le_compat_r s (33 / 4) 1104 Hs33).
      assert (Hv : (33 / 4) * 1104 == 9108) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      assert (Hc : 1104 * s == s * 1104) by ring.
      rewrite <- Hc in H. rewrite Hv in H.
      (* 注：Qmult_le_compat_r 第二前提 0≤1104 未喂，H 系未取用箭头
         （exact 直接败）——补喂后闭合 *)
      apply H.
      apply Qlt_le_weak. change (Qlt 0 1104). compute. reflexivity. }
    assert (Hlt : Qle (1104 * s) 9152).
    { apply (Qle_trans (1104 * s) 9108 9152); [exact Hb | apply Qlt_le_weak; unfold Qlt; simpl; lia]. }
    assert (Hinner : Qle 0 (9152 - 1104 * s)).
    { (* 注（静态排雷同轮）：Hm 即 0≤9152+−(1104s)，与目标 0≤9152−1104s
         仅 Qminus 词面差（转换可通）——原 Qopp_le_compat 步骤前提错位
         （Hm 之型 0≤9152−1104s 被误用作 1104s−9152≤0，词法应用必型误）整段撤除 *)
      exact (proj1 (Qle_minus_iff (1104 * s) 9152) Hlt). }
    assert (Hr : 1104 * (s * s) - 9152 * s == s * (1104 * s - 9152)) by ring.
    rewrite Hr.
    assert (Hpos : Qle 0 (s * (9152 - 1104 * s))).
    { apply (Qmult_le_0_compat s (9152 - 1104 * s)); [exact Hs0 | exact Hinner]. }
    assert (Hneg0 := Qopp_le_compat 0 (s * (9152 - 1104 * s)) Hpos).
    assert (Hz : - 0 == 0) by ring.
    rewrite Hz in Hneg0.
    assert (Hr2 : - (s * (9152 - 1104 * s)) == s * (1104 * s - 9152)) by ring.
    rewrite Hr2 in Hneg0. exact Hneg0. }
  (* 分子 ≤ −640 *)
  assert (HPle : Qle (s * s * s * s - 40 * (s * s * s) + 1104 * (s * s) - 9152 * s - 640) (- 640)).
  { assert (Hsum : s * s * s * s - 40 * (s * s * s) + 1104 * (s * s) - 9152 * s - 640 ==
                   ((s * s * s * s - 40 * (s * s * s)) + (1104 * (s * s) - 9152 * s)) + (- 640)) by ring.
    rewrite Hsum.
    apply (Qle_trans _ (0 + 0 + (- 640)) _).
    - apply Qplus_le_compat.
      + apply Qplus_le_compat; [exact Hd1 | exact Hd2].
      + apply Qle_refl.
    - assert (Hn : 0 + 0 + (- 640) == - 640) by ring.
      rewrite Hn. apply Qle_refl. }
  (* 组装：cos_partial 4 t + 2/5 ≤ 0 ⟹ cos_partial 4 t ≤ −2/5 *)
  assert (Hfin : Qle (cos_partial 4 t + 2 / 5) 0).
  { rewrite Hexp.
    apply (Qle_trans _ ((- 640) * (1 / 40320)) _).
    - apply (Qmult_le_compat_r _ _ (1 / 40320)).
      + exact HPle.
      + apply Qlt_le_weak. change (Qlt 0 (1 / 40320)). compute. reflexivity.
    - apply Qlt_le_weak.
      assert (Hval : (- 640) * (1 / 40320) == - (1 / 63)) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      rewrite Hval.
      unfold Qlt. simpl. lia. }
  apply (proj2 (Qle_minus_iff (cos_partial 4 t) (- (2 / 5)))).
  assert (Hr0 : - (2 / 5) - cos_partial 4 t == - (cos_partial 4 t + 2 / 5)) by ring.
  rewrite Hr0.
  assert (Hz : - 0 == 0) by ring.
  rewrite <- Hz.
  apply (Qopp_le_compat (cos_partial 4 t + 2 / 5) 0 Hfin).
Qed.

(* 主锚：k ≥ 4、2 ≤ t ≤ 7/2 ⟹ cos_partial k t ≤ −2/5 *)
Lemma abl13_cos_partial_neg25 : forall (k : nat) (t : Q), (4 <= k)%nat ->
  Qle 2 t -> Qle t (7 / 2) -> Qle (cos_partial k t) (- (2 / 5)).
Proof.
  intros k t Hk Ht2 Ht72.
  apply (Qle_trans _ (cos_partial 4 t) _).
  - apply abl13_cp_le_s4; [exact Hk | apply abl13_sq_window; assumption].
  - apply abl13_cp4_le_neg25; assumption.
Qed.

(* ============================================================ *)
(* Part 4 · 主定理：cos 零点唯一桥扩域 (3/2,7/2)                 *)
(*   沿 cos_pi_half_unique_widened（S10:9465）的 eps 装配，     *)
(*   上端点 2 → 7/2；新增分支 w_n > 2 由主锚 −2/5 闭合。          *)
(* ============================================================ *)

Lemma abl13_cos_pi_half_unique_widened2 : forall (w : Real),
  real_lt (real_const (3 / 2)) w -> real_lt w (real_const (7 / 2)) ->
  real_eq (cauchy_real_cos w) real_zero ->
  real_eq w cos_pi_half.
Proof.
  intros w Hlow Hup Hw0.
  intros eps Heps.
  assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Heps8 : Qlt 0 (eps / 8)).
  { apply (Qlt_shift_div_l 0 eps 8).
    - change (Qlt 0 8). compute. reflexivity.
    - simpl. exact HepsQ. }
  (* 逐点界来源：w 侧（端点 + cos w == 0 对角）、z 侧（cos_zero_lower/upper + cos z == 0 对角） *)
  destruct (real_lt_lower_pt (3 / 2) w Hlow) as [Nlo HNlo].
  destruct (real_lt_upper_pt (7 / 2) w Hup) as [Nup HNup].
  destruct (cos_eq_zero_diag_bound w Hw0 (eps / 8) Heps8) as [Nwd Hwd].
  destruct (cos_eq_zero_diag_bound cos_pi_half real_cos_pi_half_zero (eps / 8) Heps8) as [Nzd Hzd].
  (* X13 R3 修：q_pow_arch 系 S07_RealSetoidExpLog 件，S10 对其仅 Require Import
     不传播名字，裸名不可见——改限定名引用，免整件 Import 引发重名遮蔽风险 *)
  destruct (S07_RealSetoidExpLog.q_pow_arch 1 (eps / 8)) as [t Ht].
  { apply Qlt_le_weak. change (Qlt 0 1). compute. reflexivity. }
  { exact Heps8. }
  set (A := Nat.max Nlo (Nat.max Nup (Nat.max Nwd Nzd))).
  exists (Nat.max 4 (Nat.max A (Datatypes.S t))).
  intros n Hn.
  apply Qlt_to_QltT.
  (* 注：分支 (b) 主锚 abl13_cos_partial_neg25 需 4≤n（S4 包络 4 项起），
     见证下界 2→4，Hn4/Hn2 双派生（cos_inv_dist_le2 仍取 Hn2） *)
  assert (Hn4 : (4 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 4 (Nat.max A (Datatypes.S t))) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
  assert (Hn2 : (2 <= n)%nat) by (apply (Nat.le_trans _ 4 _); [lia | exact Hn4]).
  assert (HnAt : (Nat.max A (Datatypes.S t) <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 4 (Nat.max A (Datatypes.S t))) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
  assert (HnA : (A <= n)%nat) by (apply (Nat.le_trans _ (Nat.max A (Datatypes.S t)) _); [apply Nat.le_max_l | exact HnAt]).
  assert (Hnlo : (Nlo <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nlo (Nat.max Nup (Nat.max Nwd Nzd))) _); [apply Nat.le_max_l | ].
    unfold A in HnA. exact HnA. }
  assert (Hnup : (Nup <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_l | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  assert (Hnwd : (Nwd <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nwd Nzd) _); [apply Nat.le_max_l | ].
    apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  assert (Hnzd : (Nzd <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nwd Nzd) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  (* w_n ∈ (3/2, 7/2)、z_n ∈ (3/2, 5/3)（Q 层） *)
  assert (Hwlo : Qle (3 / 2) (projT1 w n)) by (apply Qlt_le_weak; apply (HNlo n); exact Hnlo).
  assert (Hwup : Qle (projT1 w n) (7 / 2)) by (apply Qlt_le_weak; apply (HNup n); exact Hnup).
  assert (Hzlo : Qle (3 / 2) (cos_zero_seq n)) by (apply Qlt_le_weak; apply cos_zero_lower).
  assert (Hzup : Qle (cos_zero_seq n) (5 / 3)) by (apply Qlt_le_weak; apply cos_zero_upper).
  assert (Hzup2 : Qle (cos_zero_seq n) 2).
  { apply (Qle_trans _ (5 / 3) _); [exact Hzup | change (Qle (5 / 3) 2); unfold Qle, Qdiv; simpl; lia]. }
  (* cos w_n 与 cos z_n 的对角界 < eps/8 *)
  assert (Hwpt : Qlt (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n)) (eps / 8)).
  { apply (Hwd n). exact Hnwd. }
  assert (Hzpt : Qlt (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n)) (eps / 8)).
  { apply (Hzd n). exact Hnzd. }
  (* 逐点 Q 可判定分支：w_n ≤ 2（逆界装配）或 2 < w_n（主锚闭合） *)
  destruct (Qlt_le_dec (projT1 w n) 2) as [Hw2 | Hwgt2].
  - (* 分支 (a)：w_n ≤ 2 —— 承袭 widened 形（v ≤ 2 逆界） *)
    assert (Hw2le : Qle (projT1 w n) 2) by (apply Qlt_le_weak; exact Hw2).
    destruct (Qlt_le_dec (cos_zero_seq n) (projT1 w n)) as [Hzw | Hwz].
    + (* z_n < w_n：u := z_n、v := w_n *)
      assert (Hd : Qlt (projT1 w n - cos_zero_seq n) (2 * (eps / 8 + eps / 8))).
      { apply (cos_inv_dist_le2 (cos_zero_seq n) (projT1 w n) (eps / 8) (eps / 8) n).
        - exact Hn2.
        - exact Hzlo.
        - apply Qlt_le_weak. exact Hzw.
        - exact Hw2le.
        - apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n - projT1 real_zero n))
                              (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n))
                              (eps / 8)).
          + apply qeq_le. apply Qabs_wd.
            assert (Hp : projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n ==
                         projT1 (cauchy_real_cos cos_pi_half) n).
            { cbn [projT1 cauchy_real_cos cos_pi_half real_const]. reflexivity. }
            rewrite Hp. reflexivity.
          + exact Hzpt.
        - assert (Hwpt' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n)) (eps / 8)).
          { apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n))
                                (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n))
                                (eps / 8)).
            - apply qeq_le. apply Qabs_wd.
              assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 w n))) n == projT1 (cauchy_real_cos w) n).
              { rewrite (real_cos_proj (real_const (projT1 w n)) n). rewrite (real_cos_proj w n). reflexivity. }
              rewrite Hq. reflexivity.
            - exact Hwpt. }
          exact Hwpt'.
      }
      apply (Qle_lt_trans (Qabs (projT1 w n - cos_zero_seq n)) (projT1 w n - cos_zero_seq n) eps).
      * apply qeq_le. apply Qabs_pos. apply (proj1 (Qle_minus_iff (cos_zero_seq n) (projT1 w n))). apply Qlt_le_weak. exact Hzw.
      * apply (Qle_lt_trans _ (2 * (eps / 8 + eps / 8)) _).
        -- apply Qlt_le_weak. exact Hd.
        -- assert (Hm : 2 * (eps / 8 + eps / 8) == eps / 2) by (unfold Qdiv; field).
           apply (Qle_lt_trans (2 * (eps / 8 + eps / 8)) (eps / 2) eps).
           ++ apply qeq_le. exact Hm.
           ++ apply (proj2 (Qlt_minus_iff (eps / 2) eps)).
              apply (Qlt_le_trans 0 (eps / 2) (eps - eps / 2)).
              ** apply (Qlt_shift_div_l 0 eps 2).
                 --- change (Qlt 0 2). compute. reflexivity.
                 --- simpl. exact HepsQ.
              ** apply qeq_le. unfold Qminus. field.
    + (* w_n ≤ z_n：u := w_n、v := z_n（对称） *)
      assert (Hwpt' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n)) (eps / 8)).
      { apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n))
                            (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n))
                            (eps / 8)).
        - apply qeq_le. apply Qabs_wd.
          assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 w n))) n == projT1 (cauchy_real_cos w) n).
          { rewrite (real_cos_proj (real_const (projT1 w n)) n). rewrite (real_cos_proj w n). reflexivity. }
          rewrite Hq. reflexivity.
        - exact Hwpt. }
      assert (Hd : Qlt (cos_zero_seq n - projT1 w n) (2 * (eps / 8 + eps / 8))).
      { apply (cos_inv_dist_le2 (projT1 w n) (cos_zero_seq n) (eps / 8) (eps / 8) n).
        - exact Hn2.
        - exact Hwlo.
        - exact Hwz.
        - exact Hzup2.
        - exact Hwpt'.
        - apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n - projT1 real_zero n))
                              (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n))
                              (eps / 8)).
          + apply qeq_le. apply Qabs_wd.
            assert (Hp : projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n ==
                         projT1 (cauchy_real_cos cos_pi_half) n).
            { cbn [projT1 cauchy_real_cos cos_pi_half real_const]. reflexivity. }
            rewrite Hp. reflexivity.
          + exact Hzpt. }
      apply (Qle_lt_trans (Qabs (projT1 w n - cos_zero_seq n)) (cos_zero_seq n - projT1 w n) eps).
      * rewrite (Qabs_Qminus (projT1 w n) (cos_zero_seq n)).
        apply qeq_le. apply Qabs_pos. apply (proj1 (Qle_minus_iff (projT1 w n) (cos_zero_seq n))). exact Hwz.
      * apply (Qle_lt_trans _ (2 * (eps / 8 + eps / 8)) _).
        -- apply Qlt_le_weak. exact Hd.
        -- assert (Hm : 2 * (eps / 8 + eps / 8) == eps / 2) by (unfold Qdiv; field).
           apply (Qle_lt_trans (2 * (eps / 8 + eps / 8)) (eps / 2) eps).
           ++ apply qeq_le. exact Hm.
           ++ apply (proj2 (Qlt_minus_iff (eps / 2) eps)).
              apply (Qlt_le_trans 0 (eps / 2) (eps - eps / 2)).
              ** apply (Qlt_shift_div_l 0 eps 2).
                 --- change (Qlt 0 2). compute. reflexivity.
                 --- simpl. exact HepsQ.
              ** apply qeq_le. unfold Qminus. field.
  - (* 分支 (b)：2 < w_n —— 主锚 cos_partial n w_n ≤ −2/5 与对角界 |cos_partial n w_n| < eps/8
       相容仅当 eps > 16/5；此时 |w_n − z_n| ≤ 2 < 16/5 ≤ eps 直接放行 *)
    assert (Hanch : Qle (cos_partial n (projT1 w n)) (- (2 / 5))).
    { apply (abl13_cos_partial_neg25 n (projT1 w n) Hn4).
      - (* 注：Qlt_le_dec 第二支即 Qle（非 Qlt），Hwgt2 直接 exact *)
        exact Hwgt2.
      - exact Hwup. }
    assert (Hwdc : Qlt (Qabs (cos_partial n (projT1 w n) - projT1 real_zero n)) (eps / 8)).
    { pose proof (Hwd n Hnwd) as Hw. rewrite (real_cos_proj w n) in Hw. exact Hw. }
    assert (Hwdc2 : Qlt (Qabs (cos_partial n (projT1 w n))) (eps / 8)).
    { apply (Qle_lt_trans (Qabs (cos_partial n (projT1 w n)))
                          (Qabs (cos_partial n (projT1 w n) - projT1 real_zero n)) (eps / 8)).
      - apply qeq_le. apply Qabs_wd.
        assert (Hr : cos_partial n (projT1 w n) == cos_partial n (projT1 w n) - projT1 real_zero n).
        { cbn [projT1 real_zero]. ring. }
        exact Hr.
      - exact Hwdc. }
    destruct (Qlt_le_dec (16 / 5) eps) as [Hepsbig | Hepssmall].
    + (* eps > 16/5：|w_n − z_n| ≤ 2 < 16/5 < eps *)
      apply (Qle_lt_trans (Qabs (projT1 w n - cos_zero_seq n)) 2 eps).
      * apply abl13_qabs_le.
        -- change (Qle 0 2). unfold Qle; simpl; lia.
        -- (* −2 ≤ w_n − z_n（2 ≤ w_n、z_n ≤ 5/3 ⟹ 0 ≤ w_n − z_n） *)
           assert (Hzw0 : Qle (cos_zero_seq n) (projT1 w n)).
           { apply (Qle_trans (cos_zero_seq n) 2 (projT1 w n)).
             - apply (Qle_trans (cos_zero_seq n) (5 / 3) 2); [exact Hzup | change (Qle (5 / 3) 2); unfold Qle, Qdiv; simpl; lia].
             - exact Hwgt2. }
           apply (Qle_trans (- 2) 0 (projT1 w n - cos_zero_seq n)).
           ++ unfold Qle; simpl; lia.
           ++ apply (proj1 (Qle_minus_iff (cos_zero_seq n) (projT1 w n))). exact Hzw0.
        -- (* w_n − z_n ≤ 2（w_n < 7/2 ≤ 2 + z_n） *)
           assert (Hlt2 : Qlt (projT1 w n - cos_zero_seq n) 2).
           { apply (proj2 (Qlt_minus_iff (projT1 w n - cos_zero_seq n) 2)).
             assert (Hr : 2 - (projT1 w n - cos_zero_seq n) == (2 + cos_zero_seq n) - projT1 w n) by ring.
             rewrite Hr.
             apply (proj1 (Qlt_minus_iff (projT1 w n) (2 + cos_zero_seq n))).
             apply (Qlt_le_trans (projT1 w n) (7 / 2) (2 + cos_zero_seq n)).
             --- exact (HNup n Hnup).
             --- assert (Hr7 : 7 / 2 == 2 + 3 / 2) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
                 rewrite Hr7.
                 apply Qplus_le_compat; [change (Qle 2 2); apply Qle_refl | exact Hzlo]. }
           exact (Qlt_le_weak _ _ Hlt2).
      * apply (Qlt_le_trans 2 (16 / 5) eps).
        -- change (Qlt 2 (16 / 5)). unfold Qlt, Qdiv; simpl; lia.
        -- apply Qlt_le_weak. exact Hepsbig.
    + (* eps ≤ 16/5：矛盾（−eps/8 < cos_partial n w_n ≤ −2/5 ⟹ eps/8 > 2/5） *)
      exfalso.
      assert (Hle8 : Qle (eps / 8) (2 / 5)).
      { assert (Hd : eps / 8 == eps * (1 / 8)) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
        assert (Hd2 : 2 / 5 == (16 / 5) * (1 / 8)) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
        rewrite Hd, Hd2.
        apply (Qmult_le_compat_r eps (16 / 5) (1 / 8)).
        - exact Hepssmall.
        - apply Qlt_le_weak. change (Qlt 0 (1 / 8)). compute. reflexivity. }
      assert (Hopp8 : Qlt (- (eps / 8)) (cos_partial n (projT1 w n))).
      { apply (abl13_qabs_lt_opp _ (eps / 8) Hwdc2). }
      assert (Hpre : Qlt (- (eps / 8)) (- (2 / 5))).
      { apply (Qlt_le_trans (- (eps / 8)) (cos_partial n (projT1 w n)) (- (2 / 5)));
          [exact Hopp8 | exact Hanch]. }
      assert (Hlt25 : Qlt (2 / 5) (eps / 8)).
      { assert (Hq := Qopp_lt_compat (- (eps / 8)) (- (2 / 5)) Hpre).
        assert (Hr1 : - (- (2 / 5)) == 2 / 5) by ring.
        assert (Hr2 : - (- (eps / 8)) == eps / 8) by ring.
        rewrite Hr1, Hr2 in Hq. exact Hq. }
      exact (Qlt_irrefl (2 / 5) (Qlt_le_trans (2 / 5) (eps / 8) (2 / 5) Hlt25 Hle8)).
Qed.

(* ============================================================ *)
(* Part 5 · 强度关系：widened2 ⟹ widened（机器核验的强化链）      *)
(*   扩域形前提严格更弱（w < 2 ⟹ w < 7/2），实例集严格超集。      *)
(* ============================================================ *)

Lemma abl13_real_lt_le_widen : forall x : Real, real_lt x (real_const 2) -> real_lt x (real_const (7 / 2)).
Proof.
  intros x [eps [Heps [N HN]]].
  exists eps. split; [exact Heps | ].
  exists N. intros n Hn.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans eps (projT1 (real_const 2) n - projT1 x n) ((7 / 2) - projT1 x n)).
  - apply QltT_to_Qlt. exact (HN n Hn).
  - assert (Hle2 : Qle (projT1 (real_const 2) n) (7 / 2)).
    { rewrite (real_const_proj 2 n). unfold Qle, Qdiv; simpl; lia. }
    assert (Hr : (projT1 (real_const 2) n - projT1 x n) == (projT1 (real_const 2) n + (- projT1 x n))) by ring.
    rewrite Hr.
    assert (Hr2 : ((7 / 2) - projT1 x n) == ((7 / 2) + (- projT1 x n))) by ring.
    rewrite Hr2.
    apply Qplus_le_compat; [exact Hle2 | apply Qle_refl].
Qed.

Corollary abl13_widened_of_widened2 : forall (w : Real),
  real_lt (real_const (3 / 2)) w -> real_lt w (real_const 2) ->
  real_eq (cauchy_real_cos w) real_zero ->
  real_eq w cos_pi_half.
Proof.
  intros w Hlow Hup Hw0.
  apply (abl13_cos_pi_half_unique_widened2 w Hlow).
  - apply abl13_real_lt_le_widen. exact Hup.
  - exact Hw0.
Qed.

(* ============================================================ *)
(* Part 6 · 承认面终验 + 提取检验                                *)
(* ============================================================ *)

(* PA 语句与 26 定理逐件对账（三账零差） *)
Print Assumptions abl13_qsq_nonneg.
Print Assumptions abl13_qsq_abs.
Print Assumptions abl13_qdiv_le.
Print Assumptions abl13_qabs_le.
Print Assumptions abl13_qabs_lt_opp.
Print Assumptions abl13_qplus_nonpos_le.
Print Assumptions abl13_qpow_neg1_S2.
Print Assumptions abl13_qpow_neg1_even.
Print Assumptions abl13_qpow_neg1_odd.
Print Assumptions abl13_qpow_even_abs.
Print Assumptions abl13_a_nonneg.
Print Assumptions abl13_qfact_neq0.
Print Assumptions abl13_zQ_neq0.
Print Assumptions abl13_qdiv_cancel.
Print Assumptions abl13_qpow_nonneg.
Print Assumptions abl13_a_decr.
Print Assumptions abl13_cp_even_le.
Print Assumptions abl13_cp_le_s4.
Print Assumptions abl13_sq_window.
Print Assumptions abl13_cp4_G.
Print Assumptions abl13_G_P.
Print Assumptions abl13_cp4_le_neg25.
Print Assumptions abl13_cos_partial_neg25.
Print Assumptions abl13_cos_pi_half_unique_widened2.
Print Assumptions abl13_real_lt_le_widen.
Print Assumptions abl13_widened_of_widened2.

(* 提取检验：Set 层数据面（Q 级锚 + Real 级主定理各一）；
   判据=提取产物 Obj.magic 计数 0。 *)
Recursive Extraction abl13_cos_partial_neg25.
Recursive Extraction abl13_widened_of_widened2.
