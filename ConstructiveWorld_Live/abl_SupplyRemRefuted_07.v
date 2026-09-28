(* ============================================================ *)
(* T0SupplyRemRefuted.v — T0 供给缺口攻坚侦察·隔离池试编件（v3）            *)
(* 使命：证 ~ sa_supply_rem（⑤肢在 n=3 处对一切 B:nat->Z 不可满足）。      *)
(* 路线：ln2b_le_pt_slack 吸收 Hup 3 的 real_le（Or-编码双支统一），        *)
(*   与 Q 窗（k>=40 ⟹ ∀z:Z, |1008·x_k − z| > 1/4）在 k₀=max(K,40) 对撞。   *)
(* 数值核（精确 Q）：sa_A 3 = 2^4·q̃_3 = 16·63 = 1008；                    *)
(*   窗：x_15 = 31972079/46126080；下侧 1008·x_15 > 1397/2（裕 0.1905）；   *)
(*   上侧 1008·(x_15+2^−15+2^−40) < 2795/4（裕 0.0287）。                  *)
(* 战术纪律：禁 goal 级 replace/rewrite 触发 nat 加法分解枚举发散；          *)
(*   一律 pose proof 具象实例 + 假设内具象模式改写 + bi_qlt_eq 运输。        *)
(* 依赖：池内本地现编 17 件 .vo（Windows 信任缓存与本地 9.1 Corelib digest  *)
(*   不同源，直接加载失败——side 链绕开）。                                  *)
(* 构造性：零公理零认授（Print Assumptions 机械核验）。                     *)
(* 编译配方：依赖件同池真拷，rocq c -Q <池> ""。                            *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqLn2Irrational.
Require Import BeukersLists.
Require Import BeukersIdentity.
Require Import Ln2Escape.
Require Import Ln2Bridge.
Require Import SupplyAssembly.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* §1 数值锚（vm_compute 档；全部绕开一元大幂）                            *)
(* ============================================================ *)

Lemma t0_saA3_Z : sa_A 3 = 1008%Z.
Proof. unfold sa_A. vm_compute. reflexivity. Qed.

Lemma t0_saA3_Q : ((sa_A 3) # 1)%Q == (1008 # 1)%Q.
Proof. unfold Qeq. rewrite t0_saA3_Z. cbn. lia. Qed.

Lemma t0_theta3 : q_pow sa_theta 3 == (1 # 8)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma t0_eps8_pos : QltT 0 ((1 # 8)%Q).
Proof. apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. lia. Qed.

(* 锚①：1008·x_15 > 1397/2（= 698.5；真值 698.6905，裕 0.19） *)
Lemma t0_x15_lo : QltT ((1397 # 2)%Q) (((1008 # 1)%Q * ln2i_x 15)%Q).
Proof. apply Qlt_to_QltT. vm_compute. reflexivity. Qed.

(* 锚②：1008·(x_15 + 2^−15) < 2795/4（= 698.75；真值 698.7213，裕 0.0287） *)
Lemma t0_x15_hi :
  QltT (((1008 # 1)%Q * (ln2i_x 15 + Qinv (ln2i_p2 15))%Q)%Q)
       ((2795 # 4)%Q).
Proof. apply Qlt_to_QltT. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §2 窗引理：k ≥ 40 ⟹ 1008·x_k ∈ (1397/2, 2795/4)                       *)
(* ============================================================ *)

Lemma t0_win : forall k : nat, (40 <= k)%nat ->
  Qlt ((1397 # 2)%Q) (((1008 # 1)%Q * ln2i_x k)%Q)
  /\ Qlt (((1008 # 1)%Q * ln2i_x k)%Q) ((2795 # 4)%Q).
Proof.
  intros k Hk.
  (* 单 gsum 直连（绕开 ln2i_gsum 15 25 封闭大项的转换探测） *)
  assert (E1 : k = (15 + (k - 15))%nat) by lia.
  pose proof (ln2i_x_add 15%nat (k - 15)%nat) as H1.
  rewrite <- E1 in H1.
  (* H1 : ln2i_x k == ln2i_x 15 + ln2i_gsum 15 (k - 15) *)
  assert (Hg : Qlt (ln2i_gsum 15 (k - 15)) (Qinv (ln2i_p2 15)))
    by apply ln2i_gsum_lt.
  assert (Hxlt : Qlt (ln2i_x k)
                  (ln2i_x 15 + Qinv (ln2i_p2 15))%Q).
  { apply (bi_qlt_eq (ln2i_x 15 + ln2i_gsum 15 (k - 15))%Q
             (ln2i_x 15 + Qinv (ln2i_p2 15))%Q (ln2i_x k)
             (ln2i_x 15 + Qinv (ln2i_p2 15))%Q).
    - apply (proj2 (Qplus_lt_r (ln2i_gsum 15 (k - 15))
               (Qinv (ln2i_p2 15)) (ln2i_x 15))).
      exact Hg.
    - exact (Qeq_sym _ _ H1).
    - apply Qeq_refl. }
  split.
  - (* 下侧：1397/2 < 1008·x_15 ≤ 1008·x_k（x_k ≥ x_15 由单调） *)
    apply (Qlt_le_trans (1397 # 2)%Q ((1008 # 1)%Q * ln2i_x 15)%Q
             ((1008 # 1)%Q * ln2i_x k)%Q).
    + apply QltT_to_Qlt. exact t0_x15_lo.
    + rewrite (Qmult_comm (1008 # 1)%Q (ln2i_x 15)).
      rewrite (Qmult_comm (1008 # 1)%Q (ln2i_x k)).
      apply (Qmult_le_compat_r (ln2i_x 15) (ln2i_x k) (1008 # 1)%Q).
      * apply ln2i_mono. lia.
      * unfold Qle. cbn [Qnum Qden]. lia.
  - (* 上侧：1008·x_k < 1008·(x_15+2^−15) < 2795/4 *)
    apply (Qlt_trans _ ((1008 # 1)%Q
                          * (ln2i_x 15 + Qinv (ln2i_p2 15))%Q)%Q _).
    + rewrite (Qmult_comm (1008 # 1)%Q (ln2i_x k)).
      rewrite (Qmult_comm (1008 # 1)%Q
                (ln2i_x 15 + Qinv (ln2i_p2 15))%Q).
      apply (Qmult_lt_compat_r (ln2i_x k)
               (ln2i_x 15 + Qinv (ln2i_p2 15))%Q (1008 # 1)%Q);
        [unfold Qlt; cbn [Qnum Qden]; lia | exact Hxlt].
    + apply QltT_to_Qlt. exact t0_x15_hi.
Qed.

(* ============================================================ *)
(* §3 离整引理：k ≥ 40 ⟹ ∀z:Z, |1008·x_k − z| > 1/4                      *)
(* ============================================================ *)

Lemma t0_offint : forall k : nat, (40 <= k)%nat -> forall z : Z,
  Qlt ((1 # 4)%Q) (Qabs ((((1008 # 1)%Q) * ln2i_x k - (z # 1)%Q)%Q)).
Proof.
  intros k Hk z.
  destruct (Z.le_gt_cases z 698%Z) as [Hz | Hz].
  - (* z ≤ 698：Qabs 取正支，u − z ≥ u − 698 > 1397/2 − 698 = 1/2 > 1/4 *)
    assert (HzQ : Qle ((z # 1)%Q) ((698 # 1)%Q))
      by (unfold Qle; cbn [Qnum Qden]; lia).
    assert (Hpos : Qle ((z # 1)%Q) ((1008 # 1)%Q * ln2i_x k)%Q).
    { apply (Qle_trans (z # 1)%Q (698 # 1)%Q _); [exact HzQ |].
      apply (Qle_trans (698 # 1)%Q (1397 # 2)%Q _).
      - unfold Qle. cbn [Qnum Qden]. lia.
      - apply Qlt_le_weak. apply (proj1 (t0_win k Hk)). }
    rewrite (ln2i_abs_sub _ _ Hpos).
    apply (Qlt_trans (1 # 4)%Q (1 # 2)%Q _).
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + assert (Hneg : Qle (Qopp (698 # 1)) (Qopp (z # 1)))
        by (apply (Qopp_le_compat (z # 1) (698 # 1)); exact HzQ).
      assert (H1 : Qlt (((1397 # 2)%Q + Qopp (698 # 1))%Q)
                       (((1008 # 1)%Q * ln2i_x k + Qopp (698 # 1))%Q))
        by (apply (proj2 (Qplus_lt_l (1397 # 2)%Q
                    ((1008 # 1)%Q * ln2i_x k)%Q (Qopp (698 # 1))));
            apply (proj1 (t0_win k Hk))).
      assert (H2 : Qle (((1008 # 1)%Q * ln2i_x k + Qopp (698 # 1))%Q)
                       (((1008 # 1)%Q * ln2i_x k + Qopp (z # 1))%Q))
        by (apply (Qplus_le_compat ((1008 # 1)%Q * ln2i_x k)%Q
                    ((1008 # 1)%Q * ln2i_x k)%Q (Qopp (698 # 1)) (Qopp (z # 1)));
            [apply Qle_refl | exact Hneg]).
      assert (Hr : ((1397 # 2)%Q + Qopp (698 # 1))%Q == (1 # 2)%Q)
        by reflexivity.
      rewrite Hr in H1.
      exact (Qlt_le_trans (1 # 2)%Q _ _ H1 H2).
  - (* z ≥ 699：Qabs 取负支，z − u ≥ z − 2795/4 > 699 − 2795/4 = 1/4 *)
    assert (Huz : Qle ((1008 # 1)%Q * ln2i_x k)%Q ((z # 1)%Q)).
    { apply (Qle_trans _ (2795 # 4)%Q _).
      - apply Qlt_le_weak. apply (proj2 (t0_win k Hk)).
      - apply (Qle_trans (2795 # 4)%Q (699 # 1)%Q _).
        + unfold Qle. cbn [Qnum Qden]. lia.
        + unfold Qle. cbn [Qnum Qden]. lia. }
    rewrite (Qabs_Qminus _ _).
    rewrite (ln2i_abs_sub (z # 1) _ Huz).
    assert (Hbase : Qle ((1 # 4)%Q) ((z # 1)%Q + Qopp ((2795 # 4)%Q))%Q).
    { apply (Qle_trans (1 # 4)%Q ((699 # 1)%Q + Qopp ((2795 # 4)%Q))%Q _).
      - apply qeq_le. reflexivity.
      - apply (Qplus_le_compat (699 # 1) (z # 1) (Qopp (2795 # 4))
                 (Qopp (2795 # 4))); [unfold Qle; cbn [Qnum Qden]; lia
                                    | apply Qle_refl]. }
    assert (Hstrict : Qlt ((z # 1)%Q + Qopp ((2795 # 4)%Q))%Q
                           ((z # 1)%Q + Qopp (((1008 # 1)%Q * ln2i_x k)%Q))%Q).
    { apply (proj2 (Qplus_lt_r (Qopp (2795 # 4))
               (Qopp ((1008 # 1)%Q * ln2i_x k)) (z # 1))).
      apply (Qopp_lt_compat _ _). apply (proj2 (t0_win k Hk)). }
    exact (Qle_lt_trans (1 # 4)%Q _ _ Hbase Hstrict).
Qed.

(* ============================================================ *)
(* §4 主件：sa_supply_rem 无居民 + 假设审计                                *)
(* ============================================================ *)

Theorem t0_supply_rem_refuted : sa_supply_rem -> False.
Proof.
  intros [B [Hlow Hup]].
  destruct (ln2b_le_pt_slack (ln2b_line sa_A B 3)
             (real_const (q_pow sa_theta 3)) (Hup 3%nat)
             ((1 # 8)%Q) t0_eps8_pos) as [K HK].
  specialize (HK (Nat.max K 40%nat) (Nat.le_max_l _ _)).
  pose proof (QltT_to_Qlt _ _ HK) as HKq.
  rewrite (real_const_proj (q_pow sa_theta 3) (Nat.max K 40)) in HKq.
  rewrite t0_theta3 in HKq.
  rewrite (ln2b_line_pt sa_A B 3 (Nat.max K 40)) in HKq.
  rewrite t0_saA3_Q in HKq.
  pose proof (t0_offint (Nat.max K 40%nat) (Nat.le_max_r _ _) (B 3%nat)) as Hdistq.
  assert (Hs : ((1 # 8)%Q + (1 # 8)%Q)%Q == (1 # 4)%Q) by reflexivity.
  rewrite Hs in HKq.
  exact (Qlt_not_eq (1 # 4)%Q (1 # 4)%Q (Qlt_trans _ _ _ Hdistq HKq)
           (Qeq_refl (1 # 4)%Q)).
Qed.

Print Assumptions t0_supply_rem_refuted.
