(* u6a_dammroze_quant.v
   使命：Gregory-Leibniz 部分和族 G_n := 4·pie_partial n 与几何值 pi
   （cauchy_real_pi_leibniz）的逐指标定量分离：对每个指标 n 给出显式正有理
   证书 c_n := 2·(pie_mag n − pie_mag (S n))（闭式 4/((2n+1)(2n+3))），
   使 n 偶时 G_n + c_n < pi、n 奇时 pi < G_n − c_n；
   两翼合取即 c_n < |pi − G_n| 逐 n 成立。
   依赖：S01_BaseRing、S02_CauchyComplete、S11_TP3B5、PiEnvelope。
   对标：Lean 4 Dammroze 形式化「Gregory-Leibniz 构造的完成 ≠ 有限见证
   提取器」之否定性结果；本件为其定量肯定形（逐率距离证书族）。
   构造性：主语句全 Set 层（sigT/And/QltT'/real_lt），证书为显式有理
   表达式，零公理零经典逻辑；Print Assumptions 两主定理应 Closed。
   编译配方：coqc -native-compiler no -q -Q <ConstructiveWorld_vo> "" 。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import Lia ZArith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import PiEnvelope.

(* ============================================================ *)
(* §1 证书 c_n = 2·(pie_mag n − pie_mag (S n)) 及其正性             *)
(* ============================================================ *)

Definition u6a_cert (n : nat) : Q := (2 * (pie_mag n - pie_mag (Datatypes.S n)))%Q.

(* 分母正性（field 侧条件与模量比较用） *)
Lemma u6a_den1_pos : forall n : nat, Qlt 0 (Z.of_nat (2 * n + 1) # 1)%Q.
Proof.
  intro n. unfold Qlt. simpl.
  assert (H : (0 < 2 * n + 1)%nat) by lia.
  apply Nat2Z.inj_lt in H. lia.
Qed.

Lemma u6a_den3_pos : forall n : nat, Qlt 0 (Z.of_nat (2 * n + 3) # 1)%Q.
Proof.
  intro n. unfold Qlt. simpl.
  assert (H : (0 < 2 * n + 3)%nat) by lia.
  apply Nat2Z.inj_lt in H. lia.
Qed.

(* mag 严格递减：pie_mag (S n) < pie_mag n *)
Lemma u6a_mag_strict : forall n : nat, Qlt (pie_mag (Datatypes.S n)) (pie_mag n).
Proof.
  intro n.
  rewrite (pie_mag_inv n), (pie_mag_inv (Datatypes.S n)).
  replace (2 * Datatypes.S n + 1)%nat with (2 * n + 3)%nat by lia.
  assert (H1 := u6a_den1_pos n).
  assert (H2 := u6a_den3_pos n).
  assert (H3 : Qlt (Z.of_nat (2 * n + 1) # 1) (Z.of_nat (2 * n + 3) # 1)%Q).
  { unfold Qlt. simpl. assert (H : (2 * n + 1 < 2 * n + 3)%nat) by lia.
    apply Nat2Z.inj_lt in H. lia. }
  apply (proj1 (Qinv_lt_contravar (Z.of_nat (2 * n + 1) # 1)
                                  (Z.of_nat (2 * n + 3) # 1) H1 H2)).
  exact H3.
Qed.

Lemma u6a_cert_pos : forall n : nat, Qlt 0 (u6a_cert n).
Proof.
  intro n. unfold u6a_cert.
  assert (Hd : Qlt 0 (pie_mag n - pie_mag (Datatypes.S n))).
  { apply (proj1 (Qlt_minus_iff (pie_mag (Datatypes.S n)) (pie_mag n))).
    apply u6a_mag_strict. }
  apply (Qmult_lt_0_compat 2 (pie_mag n - pie_mag (Datatypes.S n))).
  - unfold Qlt. simpl. lia.
  - exact Hd.
Qed.

Lemma u6a_cert_posT' : forall n : nat, QltT' 0 (u6a_cert n).
Proof. intro n. apply Qlt_to_QltT'. apply u6a_cert_pos. Qed.

(* 闭式注记：由 pie_mag_inv（pie_mag k == 1/(2k+1)），c_n == 4/((2n+1)(2n+3))
   归约为 2·(1/(2n+1) − 1/(2n+3)) 的分式算术；本件未以 field 战术化简
   （Q-field 实例在本环境被上游模块遮蔽），闭式按分式算术逐项核对。 *)

(* ============================================================ *)
(* §2 项符号：t_{2j} = +pie_mag (2j)，t_{2j+1} = −pie_mag (2j+1)    *)
(* ============================================================ *)

Lemma u6a_term_even : forall j : nat,
  pie_term (2 * j) == (pie_mag (2 * j))%Q.
Proof.
  intro j. unfold pie_term, pie_mag.
  rewrite (atan_sign_even j).
  replace (2 * (2 * j) + 1)%nat with (4 * j + 1)%nat by lia.
  reflexivity.
Qed.

Lemma u6a_term_odd : forall j : nat,
  pie_term (2 * j + 1) == (- pie_mag (2 * j + 1))%Q.
Proof.
  intro j. unfold pie_term, pie_mag.
  rewrite (atan_sign_odd j).
  replace (2 * (2 * j + 1) + 1)%nat with (4 * j + 3)%nat by lia.
  unfold Qdiv. ring.
Qed.

Lemma u6a_term_even2 : forall m : nat,
  pie_term (2 * m + 2) == (pie_mag (2 * m + 2))%Q.
Proof.
  intro m. replace (2 * m + 2)%nat with (2 * Datatypes.S m)%nat by lia.
  apply u6a_term_even.
Qed.

(* ============================================================ *)
(* §3 两步差闭式（一字链：parity_gap4/gap1 + 项符号 + ring）        *)
(*    4·S_{2j+2} − 4·S_{2j} = 4·mag(2j) − 4·mag(2j+1) = 2·c_{2j}   *)
(*    4·S_{2j+1} − 4·S_{2j+3} = 4·mag(2j+1) − 4·mag(2j+2) = 2·c_{2j+1} *)
(* ============================================================ *)

Lemma u6a_gap2_cert_even : forall j : nat,
  (4 * pie_partial (2 * j + 2) - 4 * pie_partial (2 * j))%Q
  == (2 * u6a_cert (2 * j))%Q.
Proof.
  intro j.
  assert (Hb : (4 * pie_partial (2 * j + 2) - 4 * pie_partial (2 * j + 1)
                == - 4 * pie_mag (2 * j + 1))%Q).
  { replace (2 * j + 2)%nat with (Datatypes.S (2 * j + 1))%nat by lia.
    setoid_replace (4 * pie_partial (Datatypes.S (2 * j + 1))
                    - 4 * pie_partial (2 * j + 1))
      with (4 * (pie_partial (Datatypes.S (2 * j + 1))
                 - pie_partial (2 * j + 1))) by ring.
    rewrite (pie_gap1 (2 * j + 1)), (u6a_term_odd j). ring. }
  unfold u6a_cert.
  replace (pie_mag (Datatypes.S (2 * j))) with (pie_mag (2 * j + 1))
    by (f_equal; lia).
  setoid_replace (4 * pie_partial (2 * j + 2) - 4 * pie_partial (2 * j))
    with ((4 * pie_partial (2 * j + 1) - 4 * pie_partial (2 * j))
          + (4 * pie_partial (2 * j + 2) - 4 * pie_partial (2 * j + 1))) by ring.
  rewrite (pie_parity_gap4 j), Hb. ring.
Qed.

Lemma u6a_gap2_cert_odd : forall j : nat,
  (4 * pie_partial (2 * j + 1) - 4 * pie_partial (2 * j + 3))%Q
  == (2 * u6a_cert (2 * j + 1))%Q.
Proof.
  intro j.
  assert (Ha : (4 * pie_partial (2 * j + 1) - 4 * pie_partial (2 * j + 2)
                == 4 * pie_mag (2 * j + 1))%Q).
  { replace (2 * j + 2)%nat with (Datatypes.S (2 * j + 1))%nat by lia.
    setoid_replace (4 * pie_partial (2 * j + 1)
                    - 4 * pie_partial (Datatypes.S (2 * j + 1)))
      with (- (4 * (pie_partial (Datatypes.S (2 * j + 1))
                   - pie_partial (2 * j + 1)))) by ring.
    rewrite (pie_gap1 (2 * j + 1)), (u6a_term_odd j). ring. }
  assert (Hc : (4 * pie_partial (2 * j + 3) - 4 * pie_partial (2 * j + 2)
                == 4 * pie_mag (2 * j + 2))%Q).
  { replace (2 * j + 3)%nat with (Datatypes.S (2 * j + 2))%nat by lia.
    setoid_replace (4 * pie_partial (Datatypes.S (2 * j + 2))
                    - 4 * pie_partial (2 * j + 2))
      with (4 * (pie_partial (Datatypes.S (2 * j + 2))
                 - pie_partial (2 * j + 2))) by ring.
    rewrite (pie_gap1 (2 * j + 2)), (u6a_term_even2 j). ring. }
  unfold u6a_cert.
  replace (pie_mag (Datatypes.S (2 * j + 1))) with (pie_mag (2 * j + 2))
    by (f_equal; lia).
  setoid_replace (4 * pie_partial (2 * j + 1) - 4 * pie_partial (2 * j + 3))
    with ((4 * pie_partial (2 * j + 1) - 4 * pie_partial (2 * j + 2))
          - (4 * pie_partial (2 * j + 3) - 4 * pie_partial (2 * j + 2))) by ring.
  rewrite Ha, Hc. ring.
Qed.

(* ============================================================ *)
(* §4 证书桥（下翼/上翼）                                          *)
(* ============================================================ *)

Lemma u6a_bridge_even : forall j : nat,
  (4 * pie_partial (2 * j) + 2 * u6a_cert (2 * j))%Q
  == 4 * pie_partial (2 * j + 2).
Proof.
  intro j. rewrite <- (u6a_gap2_cert_even j). ring.
Qed.

Lemma u6a_bridge_odd : forall j : nat,
  (4 * pie_partial (2 * j + 1) - 2 * u6a_cert (2 * j + 1))%Q
  == 4 * pie_partial (2 * j + 3).
Proof.
  intro j. rewrite <- (u6a_gap2_cert_odd j). ring.
Qed.

(* ============================================================ *)
(* §5 主定理：逐指标分离证书（下翼/上翼一对，全称无条件）              *)
(* ============================================================ *)

(* 下翼：n 偶（n = 2j），c_n = u6a_cert n，G_n + c_n < pi *)
Theorem u6a_even_sep : forall j : nat,
  sigT (fun c : Q => And (QltT' 0 c)
    (real_lt (real_const (4 * pie_partial (2 * j) + c))
             cauchy_real_pi_leibniz)).
Proof.
  intro j. exists (u6a_cert (2 * j)). split.
  - apply u6a_cert_posT'.
  - apply (pie_real_lower_gen j (u6a_cert (2 * j))
             (4 * pie_partial (2 * j) + u6a_cert (2 * j))).
    + apply u6a_cert_pos.
    + setoid_replace (4 * pie_partial (2 * j) + u6a_cert (2 * j) + u6a_cert (2 * j))
        with (4 * pie_partial (2 * j) + 2 * u6a_cert (2 * j)) by ring.
      apply qeq_le. apply u6a_bridge_even.
Qed.

(* 上翼：n 奇（n = 2j+1），c_n = u6a_cert n，pi < G_n − c_n *)
Theorem u6a_odd_sep : forall j : nat,
  sigT (fun c : Q => And (QltT' 0 c)
    (real_lt cauchy_real_pi_leibniz
             (real_const (4 * pie_partial (2 * j + 1) - c)))).
Proof.
  intro j. exists (u6a_cert (2 * j + 1)). split.
  - apply u6a_cert_posT'.
  - apply (pie_real_upper_gen (Datatypes.S j) (u6a_cert (2 * j + 1))
             (4 * pie_partial (2 * j + 1) - u6a_cert (2 * j + 1))).
    + apply u6a_cert_pos.
    + replace (2 * Datatypes.S j + 1)%nat with (2 * j + 3)%nat by lia.
      apply qeq_le.
      assert (Hb := u6a_bridge_odd j).
      setoid_replace (4 * pie_partial (2 * j + 3) + u6a_cert (2 * j + 1))
        with (4 * pie_partial (2 * j + 1) - 2 * u6a_cert (2 * j + 1)
              + u6a_cert (2 * j + 1)) by (rewrite Hb; ring).
      ring.
Qed.

(* 检验：假设审计（应两行 Closed under the global context） *)
Print Assumptions u6a_even_sep.
Print Assumptions u6a_odd_sep.

(* 检验：可提取性（生成 ml 后 Obj.magic 计数应为 0） *)
From Stdlib Require Import Extraction.
Separate Extraction u6a_even_sep u6a_odd_sep.
