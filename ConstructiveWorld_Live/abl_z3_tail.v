(* ===================================================================== *)
(*  abl_z3_tail.v —— ζ(3) 级数面立方收敛尾界机（比率律+交叉步+前缀界+对接）  *)
(* ===================================================================== *)
(*  使命：建立部分和 zb3_Isum n M 的立方衰减尾界机，及 decay 件              *)
(*    zb3_dc_sep3_small 显式前提（zb3_Isum (S m) M ≤ (1/4)(1/40)^m）对       *)
(*    全称 M 的实例。① 比率律（无除法 Qeq 形）：term(n,S j)·(j+1)·D³ =      *)
(*    term(n,j)·(n+j+1)⁴（D = 2n+j+2；ζ(2) 面比率律的立方版）；② 立方合成    *)
(*    因子：窗内 (n+j+1)⁴·(j+3) ≤ (j+1)·((S j)·D³)（A′ 因子、B 因子与       *)
(*    平凡因子三件按乘积序拼合）；③ 立方衰减交叉步：窗内                    *)
(*    term(n,S j)·(j+3) ≤ term(n,j)·(j+1)；④ 势函数单调与收敛尾界机：窗内   *)
(*    势 Isum(n,M)+(M+1)·term(n,M) 随 M 不增，故 M ≥ J 时 Isum(n,M) ≤       *)
(*    Isum(n,J)+(J+1)·term(n,J)；⑤ 前缀界机（权面 W = 1/((j+1)(j+2))、      *)
(*    裂项部分和 ≤ 1 的标量抽取求和，逐点封顶证书以显式命名前提在句）；      *)
(*    ⑥ 对接形终句：Isum(S m,M) ≤ (1/4)(1/40)^m 对全称 M（前缀 1/8 +        *)
(*    尾段 1/8 合计 1/4；阈值 5 ≤ m 与竞争判定面相配）。                     *)
(*  依赖：缓存根 S01_BaseRing S02_CauchyComplete S03_QExp；池内              *)
(*    abl_z2_pointwise（Set 层序见证）、abl_z3_itg_carrier（zb3_term 族）、  *)
(*    u5c_zeta2_gapA（比率基建）、u5c_zeta2_a1_sign（单调性）、              *)
(*    u5c_zeta2_a2_tail（A′ 因子）、u5c_zeta2_gapB（Q 嵌入桥）。             *)
(*  对标：Beukers 1979 ζ(3) 级数估计（裂项 Σ 1/(t(t+1)) 尾界模板、势函数     *)
(*    telescoping 机制）。                                                  *)
(*  构造性：纯构造性、零假设声明、零承认词面；语句结论全 Set 层              *)
(*    （QleT'/QeqT），量化前提均显式命名于语句内；归纳与情形分析经可判定通路。*)
(*  编译配方：rocq c -native-compiler no -q -Q . "" abl_z3_tail.v                *)
(*    （cpu_guard v3 包裹·串行≤1）；PA 16/16 Closed。                        *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
From Stdlib Require Import QArith.Qfield.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists
              PolyIntegral PadeErrorIntegral.
Require Import abl_z2_pointwise.
Require Import abl_z3_itg_carrier.
Require Import u5c_zeta2_gapA u5c_zeta2_a1_sign u5c_zeta2_a2_tail u5c_zeta2_gapB.

Open Scope Q_scope.

(* 分母原子非零（递归形：q_fact 原子、(S k)#1 原子及其正乘积） *)
Ltac zb3_ga_nonzero :=
  repeat split;
  first [ apply zb2_ga_pos_neq0; apply q_fact_pos
        | apply zb2_ga_pos_neq0; apply QltT_to_Qlt; apply zb2_ga_natpos_lt; lia
        | apply zb2_ga_pos_neq0; apply Qmult_lt_0_compat; zb3_ga_nonzero ].

(* ============================================================ *)
(* §1 比率律（立方版·交叉相乘 Qeq 形）                                   *)
(* ============================================================ *)

(* 比率律：term(n, j+1)·(j+1)·(2n+j+2)³ = term(n, j)·(n+j+1)⁴。
   即 r_j = (n+j+1)⁴/((j+1)(2n+j+2)³) 的无除法形。
   铸法：q_fact 后继展开（三次 Beta 因子同步）后代入 bkC 步进。 *)
Lemma zb3_term_ratio : forall n j : nat,
  QeqT (zb3_term n (Datatypes.S j)
        * ((Z.of_nat (Datatypes.S j) # 1)
           * ((Z.of_nat (n + Datatypes.S j + n + 1) # 1)
              * ((Z.of_nat (n + Datatypes.S j + n + 1) # 1)
                 * (Z.of_nat (n + Datatypes.S j + n + 1) # 1)))))
       (zb3_term n j
        * ((Z.of_nat (n + Datatypes.S j) # 1)
           * ((Z.of_nat (n + Datatypes.S j) # 1)
              * ((Z.of_nat (n + Datatypes.S j) # 1)
                 * (Z.of_nat (n + Datatypes.S j) # 1))))).
Proof.
  intros n j. apply qeq_imp_qeqT. unfold zb3_term.
  replace (n + Datatypes.S j + n + 1)%nat with (Datatypes.S (n + j + n + 1)) by lia.
  replace (n + Datatypes.S j)%nat with (Datatypes.S (n + j)) by lia.
  rewrite (q_fact_succ (n + j)). rewrite (q_fact_succ (n + j + n + 1)).
  pose proof (zb2_ga_bkC_step n j) as Hs.
  replace (n + Datatypes.S j)%nat with (Datatypes.S (n + j)) in Hs by lia.
  assert (HbkQ : (Z.of_nat (bkC (Datatypes.S (n + j)) n) # 1)
                 * (Z.of_nat (Datatypes.S j) # 1)
              == (Z.of_nat (bkC (n + j) n) # 1)
                 * (Z.of_nat (Datatypes.S (n + j)) # 1)).
  { assert (Hz : (Z.of_nat (bkC (Datatypes.S (n + j)) n) * Z.of_nat (Datatypes.S j)
               = Z.of_nat (bkC (n + j) n) * Z.of_nat (Datatypes.S (n + j)))%Z).
    { rewrite <- !Nat2Z.inj_mul. f_equal. exact Hs. }
    unfold Qeq. cbn [Qnum Qden Qmult]. rewrite Hz. lia. }
  transitivity ((Z.of_nat (bkC (Datatypes.S (n + j)) n) # 1)
                * (Z.of_nat (Datatypes.S j) # 1)
                * ((Z.of_nat (Datatypes.S (n + j)) # 1)
                   * ((Z.of_nat (Datatypes.S (n + j)) # 1)
                      * (Z.of_nat (Datatypes.S (n + j)) # 1)))
                * (q_fact (n + j) * q_fact n / q_fact (n + j + n + 1))
                * (q_fact (n + j) * q_fact n / q_fact (n + j + n + 1))
                * (q_fact (n + j) * q_fact n / q_fact (n + j + n + 1))).
  { field; zb3_ga_nonzero. }
  rewrite HbkQ.
  field; zb3_ga_nonzero.
Qed.

(* ============================================================ *)
(* §2 立方合成因子与交叉步                                                *)
(* ============================================================ *)

(* 立方合成因子：窗内 (n+j+1)⁴·(j+3) ≤ (j+1)·((S j)·D³)。
   铸法 = A′ 因子（zb2_ib_A2_le）与 B 因子（zb2_ga_B_le）及平凡因子
   n+j+1 ≤ D 三件按乘积序传递拼合。 *)
Lemma zb3_ib_ND_le : forall n j : nat,
  (2 <= n)%nat -> (2 <= j)%nat -> (n * n <= Datatypes.S j)%nat ->
  Qle ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
       * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
       * (Z.of_nat (j + 3) # 1))
      ((Z.of_nat (j + 1) # 1)
       * ((Z.of_nat (Datatypes.S j) # 1)
          * ((Z.of_nat (2 * n + j + 2) # 1)
             * ((Z.of_nat (2 * n + j + 2) # 1)
                * (Z.of_nat (2 * n + j + 2) # 1))))).
Proof.
  intros n j Hn Hj Hsq.
  assert (Hj3 : (3 <= j)%nat).
  { assert (Hnn : (2 * 2 <= n * n)%nat) by (apply Nat.mul_le_mono; lia).
    lia. }
  pose proof (QleT'_to_Qle _ _ (zb2_ib_A2_le n j Hn Hj3)) as HA.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_B_le n j Hsq)) as HB.
  replace (j + 1)%nat with (Datatypes.S j)%nat in HB by lia.
  assert (HC : QleT' ((Z.of_nat (n + j + 1) # 1)) ((Z.of_nat (2 * n + j + 2) # 1)))
    by (apply zb2gb_Qnat_le; lia).
  pose proof (QleT'_to_Qle _ _ HC) as HCq.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_natpos_ge (n + j + 1))) as Hn1.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_natpos_ge (j + 3))) as Hj3q.
  assert (Ha0 : 0 <= (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
    by (apply Qmult_le_0_compat; assumption).
  assert (Hc0 : 0 <= (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1))
    by (apply Qmult_le_0_compat; assumption).
  assert (Hstep1 : ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
                   * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1))
                <= ((Z.of_nat (j + 1) # 1) * (Z.of_nat (2 * n + j + 2) # 1))
                   * ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (2 * n + j + 2) # 1)))
    by (apply (zb2_ga_mult_le _ _ _ _ Ha0 Hc0 HA HB)).
  assert (Ha1 : 0 <= ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
                     * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)))
    by (apply Qmult_le_0_compat; assumption).
  assert (Hstep2 : (((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
                    * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)))
                   * (Z.of_nat (n + j + 1) # 1)
                <= (((Z.of_nat (j + 1) # 1) * (Z.of_nat (2 * n + j + 2) # 1))
                    * ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (2 * n + j + 2) # 1)))
                   * (Z.of_nat (2 * n + j + 2) # 1))
    by (apply (zb2_ga_mult_le _ _ _ _ Ha1 Hn1 Hstep1 HCq)).
  assert (E : (((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
               * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)))
              * (Z.of_nat (n + j + 1) # 1)
           == (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
              * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
              * (Z.of_nat (j + 3) # 1)) by ring.
  assert (F : (((Z.of_nat (j + 1) # 1) * (Z.of_nat (2 * n + j + 2) # 1))
               * ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (2 * n + j + 2) # 1)))
              * (Z.of_nat (2 * n + j + 2) # 1)
           == (Z.of_nat (j + 1) # 1)
              * ((Z.of_nat (Datatypes.S j) # 1)
                 * ((Z.of_nat (2 * n + j + 2) # 1)
                    * ((Z.of_nat (2 * n + j + 2) # 1)
                       * (Z.of_nat (2 * n + j + 2) # 1))))) by ring.
  rewrite E in Hstep2. rewrite F in Hstep2. exact Hstep2.
Qed.

(* 立方衰减交叉步：窗内 term(n,S j)·(j+3) ≤ term(n,j)·(j+1)。
   铸法：比率律把左端尺度化到 term(j)·(n+j+1)⁴·(j+3)，立方合成因子收束
   后按 (S j)·D³ > 0 取消。 *)
Theorem zb3_ib_term_step : forall n j : nat,
  (2 <= n)%nat -> (2 <= j)%nat -> (n * n <= Datatypes.S j)%nat ->
  QleT' (zb3_term n (Datatypes.S j) * (Z.of_nat (j + 3) # 1))
        (zb3_term n j * (Z.of_nat (j + 1) # 1)).
Proof.
  intros n j Hn Hj Hsq. apply Qle_to_QleT'.
  assert (Hj1 : (1 <= Datatypes.S j)%nat) by lia.
  assert (Hd2 : (1 <= 2 * n + j + 2)%nat) by lia.
  pose proof (QltT_to_Qlt _ _ (zb2_ga_natpos_lt (Datatypes.S j) Hj1)) as Hj1p.
  pose proof (QltT_to_Qlt _ _ (zb2_ga_natpos_lt (2 * n + j + 2) Hd2)) as Hd2p.
  assert (HD : 0 < (Z.of_nat (Datatypes.S j) # 1)
                   * ((Z.of_nat (2 * n + j + 2) # 1)
                      * ((Z.of_nat (2 * n + j + 2) # 1)
                         * (Z.of_nat (2 * n + j + 2) # 1)))).
  { apply Qmult_lt_0_compat.
    - exact Hj1p.
    - apply Qmult_lt_0_compat; [ exact Hd2p
        | apply Qmult_lt_0_compat; [ exact Hd2p | exact Hd2p ] ]. }
  pose proof (qeqT_imp_qeq _ _ (zb3_term_ratio n j)) as Hr.
  replace (n + Datatypes.S j + n + 1)%nat with (2 * n + j + 2)%nat in Hr by lia.
  replace (n + Datatypes.S j)%nat with (n + j + 1)%nat in Hr by lia.
  pose proof (zb3_ib_ND_le n j Hn Hj Hsq) as HN.
  pose proof (QltT_to_Qlt _ _ (zb3_term_pos n j)) as Htp.
  assert (Htp0 : 0 <= zb3_term n j) by (apply (Qlt_le_weak 0); exact Htp).
  assert (E1 : (zb3_term n (Datatypes.S j) * (Z.of_nat (j + 3) # 1))
               * ((Z.of_nat (Datatypes.S j) # 1)
                  * ((Z.of_nat (2 * n + j + 2) # 1)
                     * ((Z.of_nat (2 * n + j + 2) # 1)
                        * (Z.of_nat (2 * n + j + 2) # 1))))
            == (zb3_term n (Datatypes.S j)
                * ((Z.of_nat (Datatypes.S j) # 1)
                   * ((Z.of_nat (2 * n + j + 2) # 1)
                      * ((Z.of_nat (2 * n + j + 2) # 1)
                         * (Z.of_nat (2 * n + j + 2) # 1)))))
               * (Z.of_nat (j + 3) # 1))
    by ring.
  assert (E2 : (zb3_term n j
                * ((Z.of_nat (n + j + 1) # 1)
                   * ((Z.of_nat (n + j + 1) # 1)
                      * ((Z.of_nat (n + j + 1) # 1)
                         * (Z.of_nat (n + j + 1) # 1)))))
               * (Z.of_nat (j + 3) # 1)
            == zb3_term n j
               * ((Z.of_nat (n + j + 1) # 1)
                  * ((Z.of_nat (n + j + 1) # 1)
                     * ((Z.of_nat (n + j + 1) # 1)
                        * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))))))
    by ring.
  apply (zb2_ga_cancel_r _ _
           ((Z.of_nat (Datatypes.S j) # 1)
            * ((Z.of_nat (2 * n + j + 2) # 1)
               * ((Z.of_nat (2 * n + j + 2) # 1)
                  * (Z.of_nat (2 * n + j + 2) # 1)))) HD).
  apply (Qle_trans _ (zb3_term n j
        * ((Z.of_nat (n + j + 1) # 1)
           * ((Z.of_nat (n + j + 1) # 1)
              * ((Z.of_nat (n + j + 1) # 1)
                 * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))))))).
  - rewrite E1. rewrite Hr. rewrite E2. apply Qle_refl.
  - assert (HE : (zb3_term n j * (Z.of_nat (j + 1) # 1))
                 * ((Z.of_nat (Datatypes.S j) # 1)
                    * ((Z.of_nat (2 * n + j + 2) # 1)
                       * ((Z.of_nat (2 * n + j + 2) # 1)
                          * (Z.of_nat (2 * n + j + 2) # 1))))
              == zb3_term n j
                 * ((Z.of_nat (j + 1) # 1)
                    * ((Z.of_nat (Datatypes.S j) # 1)
                       * ((Z.of_nat (2 * n + j + 2) # 1)
                          * ((Z.of_nat (2 * n + j + 2) # 1)
                             * (Z.of_nat (2 * n + j + 2) # 1))))))
      by ring.
    rewrite HE.
    apply (zb2_ga_mult_le (zb3_term n j) (zb3_term n j)).
    + exact Htp0.
    + assert (HN0 : 0 <= (Z.of_nat (n + j + 1) # 1)
                          * ((Z.of_nat (n + j + 1) # 1)
                             * ((Z.of_nat (n + j + 1) # 1)
                                * ((Z.of_nat (n + j + 1) # 1)
                                   * (Z.of_nat (j + 3) # 1))))).
      { apply Qmult_le_0_compat.
        - apply QleT'_to_Qle. apply (zb2_ga_natpos_ge (n + j + 1)).
        - apply Qmult_le_0_compat.
          + apply QleT'_to_Qle. apply (zb2_ga_natpos_ge (n + j + 1)).
          + apply Qmult_le_0_compat.
            * apply QleT'_to_Qle. apply (zb2_ga_natpos_ge (n + j + 1)).
            * apply Qmult_le_0_compat
              ; [ apply (QleT'_to_Qle _ _); apply (zb2_ga_natpos_ge (n + j + 1))
                | apply (QleT'_to_Qle _ _); apply (zb2_ga_natpos_ge (j + 3)) ]. }
      exact HN0.
      + apply Qle_refl.
      + assert (Hs : (Z.of_nat (n + j + 1) # 1)
                     * ((Z.of_nat (n + j + 1) # 1)
                        * ((Z.of_nat (n + j + 1) # 1)
                           * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))))
                  == ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
                      * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
                      * (Z.of_nat (j + 3) # 1))) by ring.
        rewrite Hs. exact HN.
Qed.

(* 势函数单调：窗内 term(n,S j)·(j+2)·(j+3) ≤ term(n,j)·(S j)·(j+2)，
   即势 E(j) = term(n,j)·(j+1)(j+2) 随 j 不增。 *)
Lemma zb3_ib_term_E_mono : forall n j : nat,
  (2 <= n)%nat -> (2 <= j)%nat -> (n * n <= Datatypes.S j)%nat ->
  QleT' (zb3_term n (Datatypes.S j) * (Z.of_nat (j + 2) # 1)
         * (Z.of_nat (j + 3) # 1))
        (zb3_term n j * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1)).
Proof.
  intros n j Hn Hj Hsq.
  pose proof (zb3_ib_term_step n j Hn Hj Hsq) as Hstep.
  replace (j + 1)%nat with (Datatypes.S j)%nat in Hstep by lia.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ Hstep) as Hs.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_natpos_ge (j + 2))) as Hj2ge.
  assert (E1 : (zb3_term n (Datatypes.S j) * (Z.of_nat (j + 2) # 1)
                * (Z.of_nat (j + 3) # 1))
             == (zb3_term n (Datatypes.S j) * (Z.of_nat (j + 3) # 1))
                * (Z.of_nat (j + 2) # 1))
    by ring.
  rewrite E1. exact (Qmult_le_compat_r _ _ _ Hs Hj2ge).
Qed.

(* ============================================================ *)
(* §3 势界归纳与收敛尾界机                                                 *)
(* ============================================================ *)

(* 势界：窗内势 Isum(n,M) + (M+1)·term(n,M) 随 M 不增。 *)
Lemma zb3_ib_pot_bound : forall n J M : nat,
  (J <= M)%nat -> (2 <= J)%nat -> (2 <= n)%nat -> (n * n <= Datatypes.S J)%nat ->
  Qle (zb3_Isum n M + (Z.of_nat (Datatypes.S M) # 1) * zb3_term n M)
      (zb3_Isum n J + (Z.of_nat (Datatypes.S J) # 1) * zb3_term n J).
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
      pose proof (zb3_ib_term_step n M Hn HM2 HsqM) as Hstep.
      replace (M + 1)%nat with (Datatypes.S M)%nat in Hstep by lia.
      assert (Hs2 : Qle ((Z.of_nat (M + 3) # 1) * zb3_term n (Datatypes.S M))
                        ((Z.of_nat (Datatypes.S M) # 1) * zb3_term n M)).
      { pose proof (QleT'_to_Qle _ _ Hstep) as Hs0.
        assert (Ea : (Z.of_nat (M + 3) # 1) * zb3_term n (Datatypes.S M)
                   == zb3_term n (Datatypes.S M) * (Z.of_nat (M + 3) # 1)) by ring.
        assert (Eb : (Z.of_nat (Datatypes.S M) # 1) * zb3_term n M
                   == zb3_term n M * (Z.of_nat (Datatypes.S M) # 1)) by ring.
        rewrite Ea, Eb. exact Hs0. }
      assert (Hq3 : (Z.of_nat (M + 3) # 1) == 3 + (Z.of_nat M # 1)).
      { replace (M + 3)%nat with
          (Datatypes.S (Datatypes.S (Datatypes.S M)))%nat by lia.
        rewrite !zb2_ga_qsucc. ring. }
      cbn [zb3_Isum].
      assert (E : zb3_Isum n M + zb3_term n (Datatypes.S M)
                  + (Z.of_nat (Datatypes.S (Datatypes.S M)) # 1)
                    * zb3_term n (Datatypes.S M)
               == zb3_Isum n M
                  + (Z.of_nat (M + 3) # 1) * zb3_term n (Datatypes.S M)).
      { rewrite Hq3. rewrite ?zb2_ga_qsucc. ring. }
      rewrite E.
      apply (Qle_trans _ (zb3_Isum n M
                          + (Z.of_nat (Datatypes.S M) # 1) * zb3_term n M)).
      * apply (Qplus_le_compat _ _ _ _ (Qle_refl _) Hs2).
      * exact IHq.
Qed.

(* 收敛尾界机：窗内起步则任意 M ≥ J 的部分和被
   Isum(n,J) + (J+1)·term(n,J) 封顶。 *)
Theorem zb3_ib_Isum_tail_conv : forall n J M : nat,
  (J <= M)%nat -> (2 <= J)%nat -> (2 <= n)%nat -> (n * n <= Datatypes.S J)%nat ->
  QleT' (zb3_Isum n M)
        (zb3_Isum n J + (Z.of_nat (Datatypes.S J) # 1) * zb3_term n J).
Proof.
  intros n J M HJM HJ2 Hn Hsq.
  pose proof (zb3_ib_pot_bound n J M HJM HJ2 Hn Hsq) as Hpot.
  apply Qle_to_QleT'.
  apply (Qle_trans (zb3_Isum n M)
                   (zb3_Isum n M + (Z.of_nat (Datatypes.S M) # 1) * zb3_term n M)).
  - apply (Qle_trans (zb3_Isum n M) (zb3_Isum n M + 0)).
    + rewrite Qplus_0_r. apply Qle_refl.
    + apply (Qplus_le_compat _ _ _ _ (Qle_refl _)).
      apply Qmult_le_0_compat.
      * apply QleT'_to_Qle. apply zb2_ga_natpos_ge.
      * apply (Qlt_le_weak 0). apply QltT_to_Qlt. apply zb3_term_pos.
  - exact Hpot.
Qed.

(* ============================================================ *)
(* §4 权面与前缀界机（逐点封顶证书以显式命名前提在句）                       *)
(* ============================================================ *)

(* 权面：W j = 1/((j+1)(j+2)) *)
Definition zb3_ia_W (j : nat) : Q :=
  1 / ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1)).

(* 权面部分和：Wsum J = Σ_{j<J} W j = 1 − 1/(J+1)（裂项精确闭式） *)
Definition zb3_ia_Wsum (J : nat) : Q := 1 - 1 / (Z.of_nat (Datatypes.S J) # 1).

(* 乘权消去：a·(1/w)·w = a（w ≠ 0） *)
Lemma zb3_ia_field_canc : forall a w : Q,
  ~ (w == 0) -> (a * / w * w == a)%Q.
Proof.
  intros a w Hw. rewrite <- Qmult_assoc.
  rewrite <- (Qmult_comm w (/ w)). rewrite (Qmult_inv_r w Hw). apply Qmult_1_r.
Qed.

(* 权面部分和不超过 1 *)
Lemma zb3_ia_Wsum_le_1 : forall J : nat, Qle (zb3_ia_Wsum J) 1.
Proof.
  intro J. unfold zb3_ia_Wsum. unfold Qle.
  destruct (Z.of_nat (Datatypes.S J)) as [| p | p] eqn:E.
  - unfold Qminus. cbn [Qnum Qden Qinv Qdiv Qmult Qplus Qopp]. lia.
  - unfold Qminus. cbn [Qnum Qden Qinv Qdiv Qmult Qplus Qopp].
    rewrite ?Pos.mul_1_r. lia.
  - exfalso. pose proof (Nat2Z.is_nonneg (Datatypes.S J)) as Hp.
    rewrite E in Hp. lia.
Qed.

(* 标量抽取求和机：逐项 term ≤ c·W 界 ⟹ 前缀和 ≤ c·Wsum 界 *)
Lemma zb3_ia_Isum_scalar : forall n J : nat, forall c : Q,
  (forall J' : nat, zb3_ia_Wsum (Datatypes.S J') == zb3_ia_Wsum J' + zb3_ia_W J') ->
  (1 <= J)%nat ->
  (forall j : nat, (j < J)%nat -> QleT' (zb3_term n j) (c * zb3_ia_W j)) ->
  QleT' (zb3_Isum n (J - 1)) (c * zb3_ia_Wsum J).
Proof.
  intros n J c Hws. induction J as [| J IH]; intro HJ.
  - exfalso. lia.
  - destruct J as [| J'].
    + (* 基档 J = 1 *)
      intro Hterm.
      replace (Datatypes.S 0 - 1)%nat with 0%nat by lia.
      cbn [zb3_Isum].
      specialize (Hterm 0%nat (Nat.lt_0_succ 0)).
      assert (HE : zb3_ia_Wsum 1 == zb3_ia_W 0).
      { unfold zb3_ia_Wsum, zb3_ia_W, Qeq, Qplus, Qminus, Qdiv, Qmult, Qinv.
        simpl. lia. }
      apply Qle_to_QleT'.
      rewrite HE. exact (QleT'_to_Qle _ _ Hterm).
    + (* 步档 J = S (S J') ≥ 2 *)
      intro Hterm.
      replace (Datatypes.S (Datatypes.S J') - 1)%nat with (Datatypes.S J') by lia.
      assert (HJ' : (1 <= Datatypes.S J')%nat) by lia.
      assert (Hterm' : forall j : nat, (j < Datatypes.S J')%nat ->
                QleT' (zb3_term n j) (c * zb3_ia_W j)).
      { intros j Hj. apply Hterm. lia. }
      pose proof (IH HJ' Hterm') as IHq.
      replace (Datatypes.S J' - 1)%nat with J'%nat in IHq by lia.
      cbn [zb3_Isum].
      apply Qle_to_QleT'.
      rewrite (Hws (Datatypes.S J')).
      assert (HE : (c * (zb3_ia_Wsum (Datatypes.S J') + zb3_ia_W (Datatypes.S J')))
                == (c * zb3_ia_Wsum (Datatypes.S J') + c * zb3_ia_W (Datatypes.S J'))).
      { apply Qmult_plus_distr_r. }
      rewrite HE.
      apply (Qplus_le_compat _ _ _ _).
      * exact (QleT'_to_Qle _ _ IHq).
      * exact (QleT'_to_Qle _ _ (Hterm (Datatypes.S J')
                   (Nat.lt_succ_diag_r (Datatypes.S J')))).
Qed.

(* 常数折算：c·Wsum J ≤ c·1（Wsum ≤ 1 与 c ≥ 0 的乘积序合账） *)
Lemma zb3_ia_cWsum_le_c : forall (m J : nat), (1 <= J)%nat ->
  Qle (((1 # 8) * q_pow (1 # 40) m) * zb3_ia_Wsum J)
      (((1 # 8) * q_pow (1 # 40) m) * 1).
Proof.
  intros m J HJ.
  rewrite (Qmult_comm ((1 # 8) * q_pow (1 # 40) m) (zb3_ia_Wsum J)).
  rewrite (Qmult_comm ((1 # 8) * q_pow (1 # 40) m) 1).
  apply Qmult_le_compat_r.
  - exact (zb3_ia_Wsum_le_1 J).
  - apply Qmult_le_0_compat.
    + unfold Qle. cbn [Qnum Qden]. lia.
    + apply q_pow_nonneg. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* 前缀界终形：逐点封顶证书（Hpw）与裂项步档恒等式（Hws）给定 ⟹
   窗 J₀ = m²+2m 的前缀部分和 ≤ (1/8)·(1/40)^m。 *)
Theorem zb3_ia_init_bound : forall m : nat,
  (forall j : nat, (j <= m * m + 2 * m)%nat ->
     QleT' (zb3_term (Datatypes.S m) j
            * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
           ((1 # 8) * q_pow (1 # 40) m)) ->
  (forall J' : nat, zb3_ia_Wsum (Datatypes.S J') == zb3_ia_Wsum J' + zb3_ia_W J') ->
  QleT' (zb3_Isum (Datatypes.S m) (m * m + 2 * m))
        ((1 # 8) * q_pow (1 # 40) m).
Proof.
  intros m Hpw Hws.
  assert (HJ1 : (1 <= m * m + 2 * m + 1)%nat) by lia.
  assert (Hpt : forall j : nat, (j < m * m + 2 * m + 1)%nat ->
           QleT' (zb3_term (Datatypes.S m) j)
                 (((1 # 8) * q_pow (1 # 40) m) * zb3_ia_W j)).
  { intros j Hj.
    assert (Hjw : (j <= m * m + 2 * m)%nat) by lia.
    specialize (Hpw j Hjw).
    pose proof (QleT'_to_Qle _ _ Hpw) as Hle.
    rewrite <- (Qmult_assoc (zb3_term (Datatypes.S m) j)) in Hle.
    assert (Hwpos : 0 < (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1)).
    { apply Qmult_lt_0_compat; apply (QltT_to_Qlt _ _); apply zb2_ga_natpos_lt; lia. }
    assert (Hwne : ~ ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1) == 0))
      by exact (zb2_ga_pos_neq0 _ Hwpos).
    apply Qle_to_QleT'.
    apply (zb2_ga_cancel_r (zb3_term (Datatypes.S m) j)
             (((1 # 8) * q_pow (1 # 40) m) * zb3_ia_W j)
             ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1)) Hwpos).
    assert (HE : (((1 # 8) * q_pow (1 # 40) m) * zb3_ia_W j)
                 * ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
              == ((1 # 8) * q_pow (1 # 40) m)).
    { unfold zb3_ia_W, Qdiv. rewrite Qmult_1_l.
      apply zb3_ia_field_canc. exact Hwne. }
    rewrite HE. exact Hle. }
  pose proof (zb3_ia_Isum_scalar (Datatypes.S m) (m * m + 2 * m + 1)
                ((1 # 8) * q_pow (1 # 40) m) Hws HJ1 Hpt) as Hpre.
  replace (m * m + 2 * m + 1 - 1)%nat with (m * m + 2 * m)%nat in Hpre by lia.
  pose proof (zb3_ia_cWsum_le_c m (m * m + 2 * m + 1) HJ1) as Hcw.
  rewrite (Qmult_1_r ((1 # 8) * q_pow (1 # 40) m)) in Hcw.
  apply Qle_to_QleT'.
  apply (Qle_trans (zb3_Isum (Datatypes.S m) (m * m + 2 * m))
                   (((1 # 8) * q_pow (1 # 40) m) * zb3_ia_Wsum (m * m + 2 * m + 1))
                   ((1 # 8) * q_pow (1 # 40) m)).
  - exact (QleT'_to_Qle _ _ Hpre).
  - exact Hcw.
Qed.

(* 部分和单调：M ≤ M' ⟹ Isum(n,M) ≤ Isum(n,M')（zb3_term 严格正性归纳） *)
Lemma zb3_ia_Isum_mono_M : forall n M M' : nat,
  (M <= M')%nat -> QleT' (zb3_Isum n M) (zb3_Isum n M').
Proof.
  intros n M M' H. revert H. induction M' as [| M' IH]; intro H.
  - assert (HM0 : (M = 0)%nat) by lia. subst M.
    apply Qle_to_QleT'. apply Qle_refl.
  - destruct (Nat.eq_dec M (Datatypes.S M')) as [Heq | Hne].
    + subst M. apply Qle_to_QleT'. apply Qle_refl.
    + assert (HM : (M <= M')%nat) by lia.
      apply Qle_to_QleT'. cbn [zb3_Isum].
      apply (Qle_trans (zb3_Isum n M) (zb3_Isum n M' + 0)
                       (zb3_Isum n M' + zb3_term n (Datatypes.S M'))).
      * rewrite Qplus_0_r. exact (QleT'_to_Qle _ _ (IH HM)).
      * apply (Qplus_le_compat _ _ _ _).
        -- apply Qle_refl.
        -- apply Qlt_le_weak. apply QltT_to_Qlt. apply zb3_term_pos.
Qed.

(* ============================================================ *)
(* §5 对接形终句（前缀 1/8 + 尾段 1/8 合计 1/4）                            *)
(* ============================================================ *)

(* 对接形终句：阈值 5 ≤ m、逐点封顶证书 Hpw 与裂项步档恒等式 Hws 给定 ⟹
   Isum(S m, M) ≤ (1/4)(1/40)^m 对全称 M。 *)
Theorem zb3_ib_sep3_closed : forall m M : nat, (5 <= m)%nat ->
  (forall j : nat, (j <= m * m + 2 * m)%nat ->
     QleT' (zb3_term (Datatypes.S m) j
            * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
           ((1 # 8) * q_pow (1 # 40) m)) ->
  (forall J' : nat, zb3_ia_Wsum (Datatypes.S J') == zb3_ia_Wsum J' + zb3_ia_W J') ->
  QleT' (zb3_Isum (Datatypes.S m) M) ((1 # 4) * q_pow (1 # 40) m).
Proof.
  intros m M Hm Hpw Hws.
  pose proof (zb3_ia_init_bound m Hpw Hws) as Hinit.
  assert (HJ0 : (2 <= m * m + 2 * m)%nat) by lia.
  assert (Hn2 : (2 <= Datatypes.S m)%nat) by lia.
  assert (Hsq : (Datatypes.S m * Datatypes.S m
                 <= Datatypes.S (m * m + 2 * m))%nat) by nia.
  (* 尾段标量：term(S m, J₀)·(S J₀) ≤ c（封顶证书除以权分母的粗档） *)
  assert (HpwJ : QleT' (zb3_term (Datatypes.S m) (m * m + 2 * m)
                        * (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1)
                        * (Z.of_nat (m * m + 2 * m + 2) # 1))
                       ((1 # 8) * q_pow (1 # 40) m))
    by (apply Hpw; apply Nat.le_refl).
  assert (Htail : Qle ((Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1)
                       * zb3_term (Datatypes.S m) (m * m + 2 * m))
                      ((1 # 8) * q_pow (1 # 40) m)).
  { assert (Hterm_capped : zb3_term (Datatypes.S m) (m * m + 2 * m)
                           * (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1)
                        <= ((1 # 8) * q_pow (1 # 40) m)).
    { pose proof (QleT'_to_Qle _ _ HpwJ) as Hle.
      assert (Hw1 : (1 # 1)%Q <= (Z.of_nat (m * m + 2 * m + 2) # 1)%Q).
      { assert (Hc : QleT' ((Z.of_nat 1 # 1)%Q)
                       ((Z.of_nat (m * m + 2 * m + 2) # 1)%Q))
          by (apply zb2gb_Qnat_le; lia).
        exact (QleT'_to_Qle _ _ Hc). }
      assert (Hterm1 : 0 <= zb3_term (Datatypes.S m) (m * m + 2 * m))
        by (apply (Qlt_le_weak 0); apply QltT_to_Qlt; apply zb3_term_pos).
      assert (Hscal : 0 <= zb3_term (Datatypes.S m) (m * m + 2 * m)
                           * (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1))
        by (apply Qmult_le_0_compat
           ; [ exact Hterm1 | apply QleT'_to_Qle; apply zb2_ga_natpos_ge ]).
      pose proof (Qmult_le_compat_r (1 # 1)%Q
                    ((Z.of_nat (m * m + 2 * m + 2) # 1)%Q)
                    (zb3_term (Datatypes.S m) (m * m + 2 * m)
                     * (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1))
                    Hw1 Hscal) as Hmult.
      rewrite Qmult_1_l in Hmult.
      assert (E : (Z.of_nat (m * m + 2 * m + 2) # 1)
                  * (zb3_term (Datatypes.S m) (m * m + 2 * m)
                     * (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1))
               == zb3_term (Datatypes.S m) (m * m + 2 * m)
                  * ((Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1)
                     * (Z.of_nat (m * m + 2 * m + 2) # 1))) by ring.
      rewrite E in Hmult.
      rewrite <- (Qmult_assoc (zb3_term (Datatypes.S m) (m * m + 2 * m))) in Hle.
      apply (Qle_trans _ (zb3_term (Datatypes.S m) (m * m + 2 * m)
                          * ((Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1)
                             * (Z.of_nat (m * m + 2 * m + 2) # 1))))
      ; [ exact Hmult | exact Hle ]. }
    assert (Esw : (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1)
                  * zb3_term (Datatypes.S m) (m * m + 2 * m)
               == zb3_term (Datatypes.S m) (m * m + 2 * m)
                  * (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1)) by ring.
    rewrite Esw. exact Hterm_capped. }
  assert (Hq0 : Qle 0 (q_pow (1 # 40) m))
    by (apply q_pow_nonneg; unfold Qle; cbn [Qnum Qden]; lia).
  destruct (le_lt_dec (m * m + 2 * m) M) as [HMJ | Hlt].
  - (* 主情形：M ≥ J₀，前缀 + 尾段 *)
    pose proof (zb3_ib_Isum_tail_conv (Datatypes.S m) (m * m + 2 * m) M
                  HMJ HJ0 Hn2 Hsq) as Htailconv.
    apply Qle_to_QleT'.
    apply (Qle_trans (zb3_Isum (Datatypes.S m) M)
                     (zb3_Isum (Datatypes.S m) (m * m + 2 * m)
                      + (Z.of_nat (Datatypes.S (m * m + 2 * m)) # 1)
                        * zb3_term (Datatypes.S m) (m * m + 2 * m))).
    + exact (QleT'_to_Qle _ _ Htailconv).
    + apply (Qle_trans _
               (((1 # 8) * q_pow (1 # 40) m)
                + ((1 # 8) * q_pow (1 # 40) m))).
      * apply Qplus_le_compat.
        -- exact (QleT'_to_Qle _ _ Hinit).
        -- exact Htail.
      * assert (E : ((1 # 8) * q_pow (1 # 40) m) + ((1 # 8) * q_pow (1 # 40) m)
                 == (1 # 4) * q_pow (1 # 40) m) by ring.
        rewrite E. apply Qle_refl.
  - (* 平移情形：M < J₀，部分和单调 *)
    pose proof (zb3_ia_Isum_mono_M (Datatypes.S m) M (m * m + 2 * m)
                  (Nat.lt_le_incl _ _ Hlt)) as Hmono.
    apply Qle_to_QleT'.
    apply (Qle_trans (zb3_Isum (Datatypes.S m) M)
                     (zb3_Isum (Datatypes.S m) (m * m + 2 * m))).
    + exact (QleT'_to_Qle _ _ Hmono).
    + apply (Qle_trans _ (((1 # 8) * q_pow (1 # 40) m))).
      * exact (QleT'_to_Qle _ _ Hinit).
      * assert (E : ((1 # 8) * q_pow (1 # 40) m) + ((1 # 8) * q_pow (1 # 40) m)
                 == (1 # 4) * q_pow (1 # 40) m) by ring.
        rewrite <- E.
        apply (zb2_add_ge0_le ((1 # 8) * q_pow (1 # 40) m)
                               ((1 # 8) * q_pow (1 # 40) m)).
        apply (Qmult_le_0_compat (1 # 8) (q_pow (1 # 40) m))
        ; [ unfold Qle; cbn [Qnum Qden]; lia
          | apply q_pow_nonneg; unfold Qle; cbn [Qnum Qden]; lia ].
Qed.

(* ============================================================ *)
(* §6 数值锚（计算链判定件·辅助面豁免）                                   *)
(* ============================================================ *)

(* 权面锚：W 0 = 1/2、W 1 = 1/6 *)
Lemma zb3_ia_W_0_anchor : zb3_ia_W 0 == (1 # 2).
Proof. reflexivity. Qed.

Lemma zb3_ia_W_1_anchor : zb3_ia_W 1 == (1 # 6).
Proof. reflexivity. Qed.

(* 窗锚：J₀ = m²+2m 在 m = 5 处取 35；比率数值样例 term(3,1) 与
   比率律自检（term(3,1)·1·8³ = term(3,0)·4⁴ 的计算面） *)
Lemma zb3_ratio_anchor : zb3_term 3 1 * ((1 # 1) * ((8 # 1) * ((8 # 1) * (8 # 1))))
  == zb3_term 3 0 * ((4 # 1) * ((4 # 1) * ((4 # 1) * (4 # 1)))).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §7 尾舱：主语句公理面自检                                             *)
(* ============================================================ *)

Print Assumptions zb3_term_ratio.
Print Assumptions zb3_ib_ND_le.
Print Assumptions zb3_ib_term_step.
Print Assumptions zb3_ib_term_E_mono.
Print Assumptions zb3_ib_pot_bound.
Print Assumptions zb3_ib_Isum_tail_conv.
Print Assumptions zb3_ia_Isum_mono_M.
Print Assumptions zb3_ia_field_canc.
Print Assumptions zb3_ia_Wsum_le_1.
Print Assumptions zb3_ia_Isum_scalar.
Print Assumptions zb3_ia_cWsum_le_c.
Print Assumptions zb3_ia_init_bound.
Print Assumptions zb3_ib_sep3_closed.
Print Assumptions zb3_ia_W_0_anchor.
Print Assumptions zb3_ia_W_1_anchor.
Print Assumptions zb3_ratio_anchor.
