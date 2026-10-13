(* ===================================================================== *)
(* 模块：u5c_zeta2_a2_tail                                               *)
(* 使命：ζ(2) 级数面收敛尾界定理族——部分和 zb2_Isum n M 在阈值窗           *)
(*   （n² ≤ S J）上的平方衰减尾界机，及 decay 件 zb2_dc_sep_small 显式     *)
(*   前提 II（zb2_Isum (S m) M ≤ (1/4)(1/10)^m）对全称 M 的实例。内容：    *)
(*   ① A2′ 因子：(n+j+1)(j+3) ≤ (j+1)(2n+j+2)，条件形 2 ≤ n、3 ≤ j        *)
(*      （差 = (n−1)(j−1)−2；阈值窗内 j ≥ n²−1 保证 3 ≤ j）；             *)
(*   ② 合成：N³·(j+3) ≤ (j+1)·((S j)·D²)（N = (n+j+1)³、D = 2n+j+2，      *)
(*      A2′ 因子与 B 因子按乘积序传递拼合）；                             *)
(*   ③ 平方衰减交叉步：阈值窗内 term(n,S j)·(j+3) ≤ term(n,j)·(j+1)；      *)
(*   ④ 势函数单调：term(n,j)·(j+1)(j+2) 窗内不增；                        *)
(*   ⑤ 收敛尾界机：M ≥ J 时 Isum(n,M) ≤ Isum(n,J) + (J+1)·term(n,J)       *)
(*      （势界归纳：Isum(n,M) + (M+1)·term(n,M) 随 M 不增）；             *)
(*   ⑥ 对接形终句：Isum(S m,M) ≤ (1/4)(1/10)^m 对全称 M，逐点封顶证书与    *)
(*      裂项步档恒等式以显式命名前提在句（与 u5c_zeta2_a1_sign 终形前提形   *)
(*      逐字同源的双前提对接面）。                                        *)
(* 依赖：Stdlib（QArith/ZArith/Arith/Lia/Qfield/Setoid）；缓存根           *)
(*   S01_BaseRing、S02_CauchyComplete、S03_QExp、BeukersLists；           *)
(*   tmine04 池 abl_z2_itg_carrier（zb2_term/zb2_Isum/zb2_term_pos）；    *)
(*   本池 u5c_zeta2_gapA（比率律 zb2_ga_term_ratio、B 因子 zb2_ga_B_le、   *)
(*   数值面 zb2_ga_natpos_lt/ge、取消律 zb2_ga_cancel_r、乘积序            *)
(*   zb2_ga_mult_le、后继数值面 zb2_ga_qsucc）、u5c_zeta2_a1_sign（前缀界  *)
(*   zb2_ia_init_bound、单调性 zb2_ia_Isum_mono_M、合计预算               *)
(*   zb2_ia_C1C2_cond）。零外部证书器、零实数层、零经典逻辑、零全局假设。  *)
(* 构造性：纯构造性、零承认式语句；语句结论全 Set 层（QleT' 为 Qle_bool    *)
(*   反映形），量化前提均显式命名于语句内；归纳与情形分析经可判定通路      *)
(*   （Nat.eq_dec、le_lt_dec）；系数不等式经 nat 单调引理与 lia 线性通路， *)
(*   有理式恒等变形经 ring 整式通路；Q 层等式重写在降层（Qle）后进行。     *)
(* 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*   ulimit -s 65532 && cd 沙箱/现役/abl_zeta2_pool &&                    *)
(*   rocq c -native-compiler no -q -Q . ""                                *)
(*   -Q <绝对路径>/abl_tmine04_pool/zeta2 ""                              *)
(*   -Q <绝对路径>/vo_local_world_unified_0930 "" u5c_zeta2_a2_tail.v     *)
(*   （三根 -Q 配平：本池/tmine04 池/缓存根）。                           *)
(* 对标：Beukers, A note on the irrationality of ζ(2) and ζ(3), Bull.     *)
(*   London Math. Soc. 11 (1979) 级数估计（Σ 1/(t(t+1)) 裂项尾界模板、     *)
(*   势函数 telescoping 机制）；勘形文书 _tdm225Z2 §三 A′-2。              *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
From Stdlib Require Import QArith.Qfield.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_itg_carrier.
Require Import u5c_zeta2_gapA u5c_zeta2_a1_sign.

Open Scope Q_scope.

(* ===================================================================== *)
(* §1 A2′ 因子与合成（阈值条件形）                                         *)
(* ===================================================================== *)

(* A2′ 因子：(n+j+1)(j+3) ≤ (j+1)(2n+j+2)，差 = (n−1)(j−1)−2，
   于 2 ≤ n、3 ≤ j 成立（(n,j)=(2,3) 处取等）。注：差式含 (n−1) 与
   (j−2) 因子，n = 1 或 j = 2 时可为负（(1,j) 恒负、(2,2) 处 −1），
   故条件形携带 2 ≤ n 与 3 ≤ j。 *)
Lemma zb2_ib_A2_le : forall n j : nat,
  (2 <= n)%nat -> (3 <= j)%nat ->
  QleT' ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
        ((Z.of_nat (j + 1) # 1) * (Z.of_nat (2 * n + j + 2) # 1)).
Proof.
  intros n j Hn Hj. apply Qle_to_QleT'. unfold Qle.
  cbn [Qnum Qden Qmult Pos.mul].
  assert (HN : (2 <= (n - 1) * (j - 1))%nat).
  { replace 2%nat with (1 * 2)%nat by lia.
    apply Nat.mul_le_mono; lia. }
  lia.
Qed.

(* 合成：阈值窗内 N·(j+3) ≤ (j+1)·((S j)·D²)，其中
   N = (n+j+1)³、D = (2n+j+2)。铸法 = A2′ 因子与 B 因子按乘积序传递拼合：
   (n+j+1)(j+3) ≤ (j+1)D 与 (n+j+1)² ≤ (S j)D 相乘。
   j = 2 档由阈值排除（2 ≤ n 时 n² ≥ 4 ⟹ S j ≥ 4 ⟹ j ≥ 3）。 *)
Lemma zb2_ib_ND_le : forall n j : nat,
  (2 <= n)%nat -> (2 <= j)%nat -> (n * n <= Datatypes.S j)%nat ->
  Qle ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
       * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
      ((Z.of_nat (j + 1) # 1)
       * ((Z.of_nat (Datatypes.S j) # 1)
          * (Z.of_nat (2 * n + j + 2) # 1)
          * (Z.of_nat (2 * n + j + 2) # 1))).
Proof.
  intros n j Hn Hj Hsq.
  assert (Hj3 : (3 <= j)%nat).
  { assert (Hnn : (2 * 2 <= n * n)%nat) by (apply Nat.mul_le_mono; lia).
    lia. }
  pose proof (QleT'_to_Qle _ _ (zb2_ib_A2_le n j Hn Hj3)) as HA.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_B_le n j Hsq)) as HB.
  replace (j + 1)%nat with (Datatypes.S j)%nat in HB by lia.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_natpos_ge (n + j + 1))) as Hn1.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_natpos_ge (j + 3))) as Hj3q.
  assert (Ha0 : 0 <= (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
    by (apply Qmult_le_0_compat; assumption).
  assert (Hc0 : 0 <= (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1))
    by (apply Qmult_le_0_compat; assumption).
  assert (E1 : ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
                * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
             == ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
                * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)))
    by ring.
  rewrite E1.
  apply (Qle_trans
           (((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
            * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)))
           (((Z.of_nat (j + 1) # 1) * (Z.of_nat (2 * n + j + 2) # 1))
            * ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (2 * n + j + 2) # 1)))).
  - apply (zb2_ga_mult_le _ _ _ _ Ha0 Hc0 HA HB).
  - assert (E : ((Z.of_nat (j + 1) # 1) * (Z.of_nat (2 * n + j + 2) # 1))
                * ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (2 * n + j + 2) # 1))
             == (Z.of_nat (j + 1) # 1)
                * ((Z.of_nat (Datatypes.S j) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1)))
      by ring.
    rewrite E. apply Qle_refl.
Qed.

(* ===================================================================== *)
(* §2 平方衰减交叉步与势函数单调                                           *)
(* ===================================================================== *)

(* 平方衰减交叉步：阈值窗内 term(n,S j)·(j+3) ≤ term(n,j)·(j+1)。
   铸法：比率律把左端尺度化到 term(j)·N³·(j+3)，合成不等式给
   N³·(j+3) ≤ (j+1)·((S j)·D²)，按乘积序传递后以 (S j)·D² > 0 取消。 *)
Theorem zb2_ib_term_step_sq : forall n j : nat,
  (2 <= n)%nat -> (2 <= j)%nat -> (n * n <= Datatypes.S j)%nat ->
  QleT' (zb2_term n (Datatypes.S j) * (Z.of_nat (j + 3) # 1))
        (zb2_term n j * (Z.of_nat (j + 1) # 1)).
Proof.
  intros n j Hn Hj Hsq. apply Qle_to_QleT'.
  assert (Hj1 : (1 <= Datatypes.S j)%nat) by lia.
  assert (Hd2 : (1 <= 2 * n + j + 2)%nat) by lia.
  pose proof (QltT_to_Qlt _ _ (zb2_ga_natpos_lt (Datatypes.S j) Hj1)) as Hj1p.
  pose proof (QltT_to_Qlt _ _ (zb2_ga_natpos_lt (2 * n + j + 2) Hd2)) as Hd2p.
  assert (HD : 0 < (Z.of_nat (Datatypes.S j) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1)).
  { apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat; assumption.
    - exact Hd2p. }
  pose proof (qeqT_imp_qeq _ _ (zb2_ga_term_ratio n j)) as Hr.
  replace (n + Datatypes.S j + n + 1)%nat with (2 * n + j + 2)%nat in Hr by lia.
  replace (n + Datatypes.S j)%nat with (n + j + 1)%nat in Hr by lia.
  pose proof (zb2_ib_ND_le n j Hn Hj Hsq) as HN.
  pose proof (QltT_to_Qlt _ _ (zb2_term_pos n j)) as Htp.
  assert (Htp0 : 0 <= zb2_term n j) by (apply (Qlt_le_weak 0); exact Htp).
  assert (E1 : (zb2_term n (Datatypes.S j) * (Z.of_nat (j + 3) # 1))
               * ((Z.of_nat (Datatypes.S j) # 1)
                  * (Z.of_nat (2 * n + j + 2) # 1)
                  * (Z.of_nat (2 * n + j + 2) # 1))
            == (zb2_term n (Datatypes.S j)
                * ((Z.of_nat (Datatypes.S j) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1)))
               * (Z.of_nat (j + 3) # 1))
    by ring.
  assert (E2 : (zb2_term n j
                * ((Z.of_nat (n + j + 1) # 1)
                   * (Z.of_nat (n + j + 1) # 1)
                   * (Z.of_nat (n + j + 1) # 1)))
               * (Z.of_nat (j + 3) # 1)
            == zb2_term n j
               * ((Z.of_nat (n + j + 1) # 1)
                  * (Z.of_nat (n + j + 1) # 1)
                  * (Z.of_nat (n + j + 1) # 1)
                  * (Z.of_nat (j + 3) # 1)))
    by ring.
  apply (zb2_ga_cancel_r _ _
           ((Z.of_nat (Datatypes.S j) # 1)
            * (Z.of_nat (2 * n + j + 2) # 1)
            * (Z.of_nat (2 * n + j + 2) # 1)) HD).
  apply (Qle_trans _ (zb2_term n j
        * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
           * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1)))).
  - rewrite E1. rewrite Hr. rewrite E2. apply Qle_refl.
  - assert (HE : (zb2_term n j * (Z.of_nat (j + 1) # 1))
                 * ((Z.of_nat (Datatypes.S j) # 1)
                    * (Z.of_nat (2 * n + j + 2) # 1)
                    * (Z.of_nat (2 * n + j + 2) # 1))
              == zb2_term n j
                 * ((Z.of_nat (j + 1) # 1)
                    * ((Z.of_nat (Datatypes.S j) # 1)
                       * (Z.of_nat (2 * n + j + 2) # 1)
                       * (Z.of_nat (2 * n + j + 2) # 1))))
      by ring.
    rewrite HE.
    apply (zb2_ga_mult_le (zb2_term n j) (zb2_term n j)).
    + exact Htp0.
    + assert (HN0 : 0 <= (Z.of_nat (n + j + 1) # 1)
                          * (Z.of_nat (n + j + 1) # 1)
                          * (Z.of_nat (n + j + 1) # 1)
                          * (Z.of_nat (j + 3) # 1)).
      { apply Qmult_le_0_compat.
        - apply Qmult_le_0_compat.
          + apply Qmult_le_0_compat.
            * apply QleT'_to_Qle. apply (zb2_ga_natpos_ge (n + j + 1)).
            * apply QleT'_to_Qle. apply (zb2_ga_natpos_ge (n + j + 1)).
          + apply QleT'_to_Qle. apply (zb2_ga_natpos_ge (n + j + 1)).
        - apply QleT'_to_Qle. apply (zb2_ga_natpos_ge (j + 3)). }
      exact HN0.
    + apply Qle_refl.
    + exact HN.
Qed.

(* 势函数单调：阈值窗内 term(n,S j)·(j+2)·(j+3) ≤ term(n,j)·(S j)·(j+2)，
   即势 E(j) = term(n,j)·(j+1)(j+2) 随 j 不增。交叉步两侧同乘 (j+2) ≥ 0。 *)
Lemma zb2_ib_term_E_mono : forall n j : nat,
  (2 <= n)%nat -> (2 <= j)%nat -> (n * n <= Datatypes.S j)%nat ->
  QleT' (zb2_term n (Datatypes.S j) * (Z.of_nat (j + 2) # 1)
         * (Z.of_nat (j + 3) # 1))
        (zb2_term n j * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1)).
Proof.
  intros n j Hn Hj Hsq.
  pose proof (zb2_ib_term_step_sq n j Hn Hj Hsq) as Hstep.
  replace (j + 1)%nat with (Datatypes.S j)%nat in Hstep by lia.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ Hstep) as Hs.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_natpos_ge (j + 2))) as Hj2ge.
  assert (E1 : (zb2_term n (Datatypes.S j) * (Z.of_nat (j + 2) # 1)
                * (Z.of_nat (j + 3) # 1))
             == (zb2_term n (Datatypes.S j) * (Z.of_nat (j + 3) # 1))
                * (Z.of_nat (j + 2) # 1))
    by ring.
  rewrite E1. exact (Qmult_le_compat_r _ _ _ Hs Hj2ge).
Qed.

(* ===================================================================== *)
(* §3 势界归纳与收敛尾界机                                                 *)
(* ===================================================================== *)

(* 势界：阈值窗内势 Isum(n,M) + (M+1)·term(n,M) 随 M 不增。
   对 M 归纳：步档以平方衰减交叉步（j := M 实例）收项——
   term(n,S M) + (M+2)·term(n,S M) = (M+3)·term(n,S M) ≤ (M+1)·term(n,M)。 *)
Lemma zb2_ib_pot_bound : forall n J M : nat,
  (J <= M)%nat -> (2 <= J)%nat -> (2 <= n)%nat -> (n * n <= Datatypes.S J)%nat ->
  Qle (zb2_Isum n M + (Z.of_nat (Datatypes.S M) # 1) * zb2_term n M)
      (zb2_Isum n J + (Z.of_nat (Datatypes.S J) # 1) * zb2_term n J).
Proof.
  intros n J M HJM HJ2 Hn Hsq. revert HJM.
  induction M as [| M IH]; intro HJM.
  - exfalso. lia.
  - destruct (Nat.eq_dec J (Datatypes.S M)) as [Heq | Hne].
    + subst J. apply Qle_refl.
    + assert (HJM' : (J <= M)%nat) by lia.
      assert (HM2 : (2 <= M)%nat) by lia.
      assert (HsqM : (n * n <= Datatypes.S M)%nat) by lia.
      pose proof (IH HJM') as IHq.
      pose proof (zb2_ib_term_step_sq n M Hn HM2 HsqM) as Hstep.
      replace (M + 1)%nat with (Datatypes.S M)%nat in Hstep by lia.
      assert (Hs2 : Qle ((Z.of_nat (M + 3) # 1) * zb2_term n (Datatypes.S M))
                        ((Z.of_nat (Datatypes.S M) # 1) * zb2_term n M)).
      { pose proof (QleT'_to_Qle _ _ Hstep) as Hs0.
        assert (Ea : (Z.of_nat (M + 3) # 1) * zb2_term n (Datatypes.S M)
                   == zb2_term n (Datatypes.S M) * (Z.of_nat (M + 3) # 1)) by ring.
        assert (Eb : (Z.of_nat (Datatypes.S M) # 1) * zb2_term n M
                   == zb2_term n M * (Z.of_nat (Datatypes.S M) # 1)) by ring.
        rewrite Ea, Eb. exact Hs0. }
      assert (Hq3 : (Z.of_nat (M + 3) # 1) == 3 + (Z.of_nat M # 1)).
      { replace (M + 3)%nat with
          (Datatypes.S (Datatypes.S (Datatypes.S M)))%nat by lia.
        rewrite !zb2_ga_qsucc. ring. }
      cbn [zb2_Isum].
      assert (E : zb2_Isum n M + zb2_term n (Datatypes.S M)
                  + (Z.of_nat (Datatypes.S (Datatypes.S M)) # 1)
                    * zb2_term n (Datatypes.S M)
               == zb2_Isum n M
                  + (Z.of_nat (M + 3) # 1) * zb2_term n (Datatypes.S M)).
      { rewrite Hq3. rewrite ?zb2_ga_qsucc. ring. }
      rewrite E.
      apply (Qle_trans _ (zb2_Isum n M
                          + (Z.of_nat (Datatypes.S M) # 1) * zb2_term n M)).
      * apply (Qplus_le_compat _ _ _ _ (Qle_refl _) Hs2).
      * exact IHq.
Qed.

(* 收敛尾界机：阈值窗内起步则任意 M ≥ J 的部分和被
   Isum(n,J) + (J+1)·term(n,J) 封顶（θ = 1 的多项式幂形尾界，
   与势的恒正性合账：Isum(n,M) ≤ 势(M) ≤ 势(J)）。 *)
Theorem zb2_ib_Isum_tail_conv : forall n J M : nat,
  (J <= M)%nat -> (2 <= J)%nat -> (2 <= n)%nat -> (n * n <= Datatypes.S J)%nat ->
  QleT' (zb2_Isum n M)
        (zb2_Isum n J + (Z.of_nat (Datatypes.S J) # 1) * zb2_term n J).
Proof.
  intros n J M HJM HJ2 Hn Hsq.
  pose proof (zb2_ib_pot_bound n J M HJM HJ2 Hn Hsq) as Hpot.
  apply Qle_to_QleT'.
  apply (Qle_trans (zb2_Isum n M)
                   (zb2_Isum n M + (Z.of_nat (Datatypes.S M) # 1) * zb2_term n M)).
  - apply (Qle_trans (zb2_Isum n M) (zb2_Isum n M + 0)).
    + rewrite Qplus_0_r. apply Qle_refl.
    + apply (Qplus_le_compat _ _ _ _ (Qle_refl _)).
      apply Qmult_le_0_compat.
      * apply QleT'_to_Qle. apply zb2_ga_natpos_ge.
      * apply (Qlt_le_weak 0). apply QltT_to_Qlt. apply zb2_term_pos.
  - exact Hpot.
Qed.

(* ===================================================================== *)
(* §4 合计预算与对接形（sep_small 前提 II 全称实例）                         *)
(* ===================================================================== *)

(* 合计预算：尾段预留以 (1/10) 兑现（3/20 预算内），与前缀常数 1/10
   合计 1/5 ≤ 1/4。本形为合计预算接口在尾段常数取值 c2 = 1/10 处的
   实例，供装配面核验。 *)
Lemma zb2_ib_C2_delivered : Qle (zb2_ia_C1 + (1 # 10)) (1 # 4).
Proof.
  apply (zb2_ia_C1C2_cond (1 # 10)).
  - unfold Qle. cbn [Qnum Qden]. lia.
  - unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* 对接形终句（sep_small 前提 II 全称实例）：n = S m、J = m²+2m
   （阈值 S J = (S m)²），对全称 M：M ≥ J 时走收敛尾界机，尾项
   (J+1)·term(S m,J) 经逐点封顶证书（j := J 单点实例）与 (j+2) ≥ 1
   放大折算为 (1/10)(1/10)^m；M < J 时走前缀单调性与前缀界终形。
   逐点封顶证书与裂项步档恒等式均以显式命名前提在句（与
   u5c_zeta2_a1_sign 终形前提形逐字同源）。 *)
Theorem zb2_ib_sep2_closed : forall m M : nat, (8 <= m)%nat ->
  (forall j : nat, (j <= m * m + 2 * m)%nat ->
     QleT' (zb2_term (Datatypes.S m) j
            * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
           ((1 # 10) * q_pow (1 # 10) m)) ->
  (forall J' : nat, zb2_ia_Wsum (Datatypes.S J') == zb2_ia_Wsum J' + zb2_ia_W J') ->
  QleT' (zb2_Isum (Datatypes.S m) M) ((1 # 4) * q_pow (1 # 10) m).
Proof.
  intros m M Hm Hpw Hws.
  pose proof (zb2_ia_init_bound m Hm Hpw Hws) as Hinit.
  assert (Hq0 : Qle 0 (q_pow (1 # 10) m))
    by (apply q_pow_nonneg; unfold Qle; cbn [Qnum Qden]; lia).
  destruct (le_lt_dec (m * m + 2 * m) M) as [HMJ | Hlt].
  - assert (HJ2 : (2 <= m * m + 2 * m)%nat) by lia.
    assert (Hn2 : (2 <= Datatypes.S m)%nat) by lia.
    assert (Hsq : (Datatypes.S m * Datatypes.S m
                   <= Datatypes.S (m * m + 2 * m))%nat) by nia.
    pose proof (zb2_ib_Isum_tail_conv (Datatypes.S m) (m * m + 2 * m) M
                  HMJ HJ2 Hn2 Hsq) as Htail.
    pose proof (Hpw (m * m + 2 * m)%nat (Nat.le_refl _)) as HpwJ.
    pose proof (QleT'_to_Qle _ _ HpwJ) as Hpwq.
    pose proof (QleT'_to_Qle _ _ (zb2_ga_natpos_ge (Datatypes.S (m * m + 2 * m)))) as HJge.
    pose proof (QltT_to_Qlt _ _ (zb2_term_pos (Datatypes.S m) (m * m + 2 * m))) as Htp.
    assert (Htp0 : 0 <= zb2_term (Datatypes.S m) (m * m + 2 * m))
      by (apply (Qlt_le_weak 0); exact Htp).
    assert (Hone : Qle 1 (Z.of_nat (m * m + 2 * m + 2) # 1))
      by (unfold Qle; cbn [Qnum Qden]; lia).
    assert (Hscale : Qle ((Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1)
                          * zb2_term (Datatypes.S m) (m * m + 2 * m))
                         (zb2_term (Datatypes.S m) (m * m + 2 * m)
                          * (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1)
                          * (Z.of_nat (m * m + 2 * m + 2) # 1))).
    { assert (Ha0 : Qle (1 * (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1))
                        ((Z.of_nat (m * m + 2 * m + 2) # 1)
                         * (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1))).
      { apply (Qmult_le_compat_r 1 (Z.of_nat (m * m + 2 * m + 2) # 1)
                 (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1) Hone HJge). }
      rewrite Qmult_1_l in Ha0.
      pose proof (Qmult_le_compat_r _ _ _ Ha0 Htp0) as Hb.
      assert (E : ((Z.of_nat (m * m + 2 * m + 2) # 1)
                   * (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1))
                  * zb2_term (Datatypes.S m) (m * m + 2 * m)
               == zb2_term (Datatypes.S m) (m * m + 2 * m)
                  * (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1)
                  * (Z.of_nat (m * m + 2 * m + 2) # 1)) by ring.
      rewrite E in Hb. exact Hb. }
    apply Qle_to_QleT'.
    apply (Qle_trans (zb2_Isum (Datatypes.S m) M)
                     (zb2_Isum (Datatypes.S m) (m * m + 2 * m)
                      + (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1)
                        * zb2_term (Datatypes.S m) (m * m + 2 * m))).
    + exact (QleT'_to_Qle _ _ Htail).
    + apply (Qle_trans _ (zb2_Isum (Datatypes.S m) (m * m + 2 * m)
                          + (1 # 10) * q_pow (1 # 10) m)).
      * apply (Qplus_le_compat _ _ _ _ (Qle_refl _)).
        apply (Qle_trans _ (zb2_term (Datatypes.S m) (m * m + 2 * m)
                            * (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1)
                            * (Z.of_nat (m * m + 2 * m + 2) # 1))).
        -- exact Hscale.
        -- exact Hpwq.
      * apply (Qle_trans _ ((1 # 10) * q_pow (1 # 10) m
                            + (1 # 10) * q_pow (1 # 10) m)).
        -- apply (Qplus_le_compat _ _ _ _).
           ++ exact (QleT'_to_Qle _ _ Hinit).
           ++ apply Qle_refl.
        -- assert (Eq : ((1 # 10) * q_pow (1 # 10) m
                         + (1 # 10) * q_pow (1 # 10) m)
                     == ((1 # 5) * q_pow (1 # 10) m)) by ring.
           rewrite Eq.
           apply (Qmult_le_compat_r (1 # 5) (1 # 4) (q_pow (1 # 10) m)).
           ++ unfold Qle. cbn [Qnum Qden]. lia.
           ++ exact Hq0.
  - assert (HM : (M <= m * m + 2 * m)%nat) by lia.
    pose proof (QleT'_to_Qle _ _
                  (zb2_ia_Isum_mono_M (Datatypes.S m) M (m * m + 2 * m) HM)) as Hmono.
    apply Qle_to_QleT'.
    apply (Qle_trans (zb2_Isum (Datatypes.S m) M)
                     (zb2_Isum (Datatypes.S m) (m * m + 2 * m))).
    + exact Hmono.
    + apply (Qle_trans _ ((1 # 10) * q_pow (1 # 10) m)).
      * exact (QleT'_to_Qle _ _ Hinit).
      * apply (Qmult_le_compat_r (1 # 10) (1 # 4) (q_pow (1 # 10) m)).
        -- unfold Qle. cbn [Qnum Qden]. lia.
        -- exact Hq0.
Qed.

(* ===================================================================== *)
(* §5 尾舱：语句公理面自检                                                 *)
(* ===================================================================== *)

Print Assumptions zb2_ib_A2_le.
Print Assumptions zb2_ib_ND_le.
Print Assumptions zb2_ib_term_step_sq.
Print Assumptions zb2_ib_term_E_mono.
Print Assumptions zb2_ib_pot_bound.
Print Assumptions zb2_ib_Isum_tail_conv.
Print Assumptions zb2_ib_C2_delivered.
Print Assumptions zb2_ib_sep2_closed.
