(* ===================================================================== *)
(* 模块：u5c_zeta2_band                                                  *)
(* 数学使命：ζ(2) 线逐点封顶量 Wt n j := zb2_term n j·(j+1)·(j+2) 的       *)
(*   无窗界闭合：∀ m j, 8 ≤ m -> Wt (S m) j ≤ (1/10)^(m+1)。              *)
(*   路线＝同列跨档迁移（same-k 行迁移）：                                  *)
(*     · 行比率恒等式 Wt(S n,k)·(2n+k+2)²(2n+k+3)² == Wt(n,k)·(n+1)(n+k+1)³ *)
(*       （zb2_term 定义直展，清分母与 q_fact 步档展开后，公共正因子        *)
(*       取消，残式即 Pascal 步档恒等式 C(n+k+1,S n)·(S n) = C(n+k,n)(n+k+1) *)
(*       的三次幂形）；                                                    *)
(*     · 迁移不等式 10·(n+1)(n+k+1)³ ≤ (2n+k+2)²(2n+k+3)²（n ≥ 2, k ≤ S n， *)
(*       最紧点 k = n+1，差 = (n+1)²(n²+56n+64) > 0）；                     *)
(*     · 封顶步进 cap(n,k) -> cap(S n,k)（cap n k :<=> Wt n k·10^n ≤ 1）；  *)
(*     · 整行归纳（基座 n = 9 全窗，右缘走降档单调律合拢）。                *)
(*   数值纪律：行比率、迁移不等式、封顶链与基座边距全部经精确有理数        *)
(*   独立复算（网格 n < 30 × k < n+10、n ∈ [2,60) × k ≤ n+1、              *)
(*   n ∈ [9,36) × k ≤ n+2、m ∈ [8,30) × j < 200 均零反例）。               *)
(* 依赖：缓存根 S01_BaseRing、S02_CauchyComplete、S03_QExp、BeukersLists；  *)
(*   tmine04 池 abl_z2_itg_carrier；本池 u5c_zeta2_gapA、u5c_zeta2_a1_sign、 *)
(*   u5c_zeta2_sup（Wt 定义/消去律/降档链）、u5c_zeta2_sup2                 *)
(*   （Pascal 桥/q_fact 正性/幂逆桥/m=8 全窗）。                            *)
(* 构造性：纯构造性、零全局假设声明、零承认式语句；语句结论全 Set 层        *)
(*   （QeqT/QleT'），nat 证书前提为语句假设位非公理位；代数步全走 ring      *)
(*   整式通路与假设重写（禁 field），系数不等式走 nat 侧 nia。               *)
(* 编译配方：cd abl_dmw1_pool/A2 &&                                         *)
(*   coqc -native-compiler no -q -Q . "" -Q _world "" u5c_zeta2_band.v      *)
(* 对标：Beukers, Bull. London Math. Soc. 11 (1979) 级数估计；              *)
(*   same-k 行迁移＝逐档同列比率链（同列跨档衰减比 ≤ 1 于全带域）。          *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_itg_carrier.
Require Import u5c_zeta2_gapA u5c_zeta2_a1_sign u5c_zeta2_sup u5c_zeta2_sup2.

Open Scope Q_scope.

(* ===================================================================== *)
(* §1 Pascal 步档：bkC(n+k+1, S n)·(S n) == bkC(n+k, n)·(n+k+1)            *)
(* ===================================================================== *)

Lemma zb2b_step1 : forall n k : nat,
  QeqT ((Z.of_nat (bkC (n + k + 1) (Datatypes.S n)) # 1) * (Z.of_nat (Datatypes.S n) # 1))
       ((Z.of_nat (bkC (n + k) n) # 1) * (Z.of_nat (n + k + 1) # 1)).
Proof.
  intros n k.
  pose proof (zb2s2_qfact_bkC_bridge (Datatypes.S n + k) (Datatypes.S n) (ltac:(lia))) as HB1.
  replace (Datatypes.S n + k - Datatypes.S n)%nat with k%nat in HB1 by lia.
  replace (Datatypes.S n + k)%nat with (n + k + 1)%nat in HB1 by lia.
  pose proof (zb2s2_qfact_bkC_bridge (n + k) n (ltac:(lia))) as HB0.
  replace (n + k - n)%nat with k%nat in HB0 by lia.
  assert (QS1' : q_fact (Datatypes.S n) == (Z.of_nat (Datatypes.S n) # 1) * q_fact n) by reflexivity.
  assert (QSk1 : q_fact (n + k + 1) == (Z.of_nat (n + k + 1) # 1) * q_fact (n + k)).
  { replace (n + k + 1)%nat with (Datatypes.S (n + k))%nat by lia. reflexivity. }
  pose proof (zb2s2_qfact_pos (Datatypes.S n)) as Hpa.
  pose proof (zb2s2_qfact_pos n) as Hpb.
  pose proof (zb2s2_qfact_pos k) as Hpc.
  assert (HWpos : 0 < (q_fact (Datatypes.S n) * (q_fact n * q_fact k))%Q).
  { apply Qmult_lt_0_compat.
    - apply QltT_to_Qlt. exact Hpa.
    - apply Qmult_lt_0_compat.
      + apply QltT_to_Qlt. exact Hpb.
      + apply QltT_to_Qlt. exact Hpc. }
  assert (HWne : ~ ((q_fact (Datatypes.S n) * (q_fact n * q_fact k)) == 0)%Q)
    by (apply zb2_ga_pos_neq0; exact HWpos).
  apply qeq_imp_qeqT.
  apply (zb2_sup_qeq_cancel_r _ _ _ HWne).
  assert (HregL : ((Z.of_nat (bkC (n + k + 1) (Datatypes.S n)) # 1)
                   * (Z.of_nat (Datatypes.S n) # 1)
                   * (q_fact (Datatypes.S n) * (q_fact n * q_fact k)))
                == ((q_fact (Datatypes.S n) * q_fact k
                     * (Z.of_nat (bkC (n + k + 1) (Datatypes.S n)) # 1))
                    * ((Z.of_nat (Datatypes.S n) # 1) * q_fact n))) by ring.
  rewrite HregL, <- HB1.
  assert (HregR : ((Z.of_nat (bkC (n + k) n) # 1) * (Z.of_nat (n + k + 1) # 1)
                   * (q_fact (Datatypes.S n) * (q_fact n * q_fact k)))
                == ((Z.of_nat (n + k + 1) # 1)
                    * (q_fact (Datatypes.S n)
                       * ((q_fact n * q_fact k)
                          * (Z.of_nat (bkC (n + k) n) # 1))))) by ring.
  rewrite HregR, <- HB0, QSk1, QS1'. ring.
Qed.

(* ===================================================================== *)
(* §2 同列行比率恒等式：                                                    *)
(*   Wt(S n,k)·(2n+k+2)²(2n+k+3)² == Wt(n,k)·(S n)·(n+k+1)³                *)
(* ===================================================================== *)

Theorem zb2b_row_ratio : forall n k : nat,
  QeqT (zb2_sup_Wt (Datatypes.S n) k
        * ((Z.of_nat (2 * n + k + 2) # 1) * (Z.of_nat (2 * n + k + 2) # 1)
           * (Z.of_nat (2 * n + k + 3) # 1) * (Z.of_nat (2 * n + k + 3) # 1)))
       (zb2_sup_Wt n k
        * ((Z.of_nat (Datatypes.S n) # 1) * (Z.of_nat (n + k + 1) # 1)
           * (Z.of_nat (n + k + 1) # 1) * (Z.of_nat (n + k + 1) # 1))).
Proof.
  intros n k.
  pose proof (zb2b_step1 n k) as P1T.
  pose proof (qeqT_imp_qeq _ _ P1T) as P1.
  pose proof (zb2s2_qfact_pos (2 * n + k + 3)) as Hp33.
  pose proof (zb2s2_qfact_pos (2 * n + k + 1)) as Hp31.
  assert (Hne33 : ~ (q_fact (2 * n + k + 3) == 0)%Q)
    by (apply zb2_ga_pos_neq0; apply QltT_to_Qlt; exact Hp33).
  assert (Hne31 : ~ (q_fact (2 * n + k + 1) == 0)%Q)
    by (apply zb2_ga_pos_neq0; apply QltT_to_Qlt; exact Hp31).
  assert (HQDpos : 0 < (q_fact (2 * n + k + 3)
                        * (q_fact (2 * n + k + 3)
                           * (q_fact (2 * n + k + 1) * q_fact (2 * n + k + 1))))%Q).
  { apply Qmult_lt_0_compat.
    - apply QltT_to_Qlt. exact Hp33.
    - apply Qmult_lt_0_compat.
      + apply QltT_to_Qlt. exact Hp33.
      + apply Qmult_lt_0_compat.
        * apply QltT_to_Qlt. exact Hp31.
        * apply QltT_to_Qlt. exact Hp31. }
  assert (HQDne : ~ ((q_fact (2 * n + k + 3)
                      * (q_fact (2 * n + k + 3)
                         * (q_fact (2 * n + k + 1) * q_fact (2 * n + k + 1)))) == 0)%Q)
    by (apply zb2_ga_pos_neq0; exact HQDpos).
  unfold zb2_sup_Wt, zb2_term, Qdiv.
  replace (Datatypes.S n + k + Datatypes.S n + 1)%nat with (2 * n + k + 3)%nat by lia.
  replace (n + k + n + 1)%nat with (2 * n + k + 1)%nat by lia.
  replace (Datatypes.S n + k)%nat with (n + k + 1)%nat by lia.
  apply qeq_imp_qeqT.
  apply (zb2_sup_qeq_cancel_r _ _ _ HQDne).
  assert (HP33 : (q_fact (2 * n + k + 3) * / q_fact (2 * n + k + 3))%Q == 1%Q)
    by (apply Qmult_inv_r; exact Hne33).
  assert (HP31 : (q_fact (2 * n + k + 1) * / q_fact (2 * n + k + 1))%Q == 1%Q)
    by (apply Qmult_inv_r; exact Hne31).
  assert (QS1' : q_fact (Datatypes.S n) == (Z.of_nat (Datatypes.S n) # 1) * q_fact n) by reflexivity.
  assert (QS1'' : q_fact (n + k + 1) == (Z.of_nat (n + k + 1) # 1) * q_fact (n + k)).
  { replace (n + k + 1)%nat with (Datatypes.S (n + k))%nat by lia. reflexivity. }
  assert (QS32 : q_fact (2 * n + k + 2)
              == (Z.of_nat (2 * n + k + 2) # 1) * q_fact (2 * n + k + 1)).
  { replace (2 * n + k + 2)%nat with (Datatypes.S (2 * n + k + 1))%nat by lia.
    reflexivity. }
  assert (QS33 : q_fact (2 * n + k + 3)
              == (Z.of_nat (2 * n + k + 3) # 1)
                 * ((Z.of_nat (2 * n + k + 2) # 1) * q_fact (2 * n + k + 1))).
  { replace (2 * n + k + 3)%nat with (Datatypes.S (2 * n + k + 2))%nat by lia.
    cbn [q_fact]. rewrite QS32. reflexivity. }
  (* 左侧：清分母后 q_fact(2n+k+3)² 与分子逆元对消 *)
  transitivity
    ((Z.of_nat (bkC (n + k + 1) (Datatypes.S n)) # 1)
     * ((q_fact (2 * n + k + 3) * / q_fact (2 * n + k + 3))
        * ((q_fact (2 * n + k + 3) * / q_fact (2 * n + k + 3))
           * (q_fact (n + k + 1)
              * ((q_fact (n + k + 1)
                  * ((q_fact (Datatypes.S n)
                     * ((q_fact (Datatypes.S n)
                        * (((Z.of_nat (Datatypes.S k) # 1) * (Z.of_nat (k + 2) # 1))
                           * (((Z.of_nat (2 * n + k + 2) # 1)
                               * ((Z.of_nat (2 * n + k + 2) # 1)
                                  * ((Z.of_nat (2 * n + k + 3) # 1)
                                     * (Z.of_nat (2 * n + k + 3) # 1))))
                              * (q_fact (2 * n + k + 1) * q_fact (2 * n + k + 1)))))))))))))).
  { ring. }
  rewrite HP33.
  (* 右侧：对称化后清分母，q_fact(2n+k+1)² 与分子逆元对消 *)
  symmetry.
  transitivity
    ((Z.of_nat (bkC (n + k) n) # 1)
     * ((q_fact (2 * n + k + 1) * / q_fact (2 * n + k + 1))
        * ((q_fact (2 * n + k + 1) * / q_fact (2 * n + k + 1))
           * ((q_fact (n + k) * (q_fact (n + k) * (q_fact n * q_fact n)))
              * ((Z.of_nat (Datatypes.S k) # 1)
                 * ((Z.of_nat (k + 2) # 1)
                    * ((Z.of_nat (Datatypes.S n) # 1)
                       * (((Z.of_nat (n + k + 1) # 1)
                           * ((Z.of_nat (n + k + 1) # 1) * (Z.of_nat (n + k + 1) # 1)))
                          * (q_fact (2 * n + k + 3) * q_fact (2 * n + k + 3)))))))))).
  { ring. }
  rewrite QS1'', QS1', QS33, HP31.
  (* 两翼同归一组正原子，残式经 §1 步档恒等式 P1 终桥合账 *)
  transitivity
    ((((((((Z.of_nat (bkC (n + k) n) # 1) * (Z.of_nat (n + k + 1) # 1)) * (Z.of_nat (n + k + 1) # 1)) * (Z.of_nat (n + k + 1) # 1)) * (Z.of_nat (Datatypes.S n) # 1)) * (Z.of_nat (Datatypes.S k) # 1)) * (Z.of_nat (k + 2) # 1))
    * (((Z.of_nat (2 * n + k + 2) # 1) * ((Z.of_nat (2 * n + k + 2) # 1) * ((Z.of_nat (2 * n + k + 3) # 1) * (Z.of_nat (2 * n + k + 3) # 1)))) * ((q_fact (n + k)) * ((q_fact (n + k)) * ((q_fact n) * (q_fact n)))) * ((q_fact (2 * n + k + 1)) * (q_fact (2 * n + k + 1))))).
  { ring. }
  rewrite <- P1. ring.
Qed.

(* ===================================================================== *)
(* §3 迁移不等式：10·(n+1)(n+k+1)³ ≤ (2n+k+2)²(2n+k+3)²（n ≥ 2, k ≤ S n）   *)
(*   最紧点 k = n+1：差 = (n+1)²(n²+56n+64) > 0。                           *)
(* ===================================================================== *)

Theorem zb2b_T : forall n k : nat, (2 <= n)%nat -> (k <= Datatypes.S n)%nat ->
  (10 * (n + 1) * (n + k + 1) * (n + k + 1) * (n + k + 1)
   <= (2 * n + k + 2) * (2 * n + k + 2) * (2 * n + k + 3) * (2 * n + k + 3))%nat.
Proof.
  intros n k Hn Hk.
  remember (Datatypes.S n - k)%nat as u eqn:Eu.
  assert (Hub : (k + u = Datatypes.S n)%nat) by lia.
  assert (Hle : (u <= Datatypes.S n)%nat) by lia.
  remember (n - 2)%nat as v eqn:Ev.
  assert (Hvb : (n = 2 + v)%nat) by lia.
  subst n.
  assert (Hk2 : k = (Datatypes.S (2 + v) - u)%nat) by lia.
  subst k.
  nia.
Qed.

(* ===================================================================== *)
(* §4 封顶步进：cap(n,k) -> cap(S n,k)（cap n k :<=> Wt n k·10^n ≤ 1）       *)
(* ===================================================================== *)

Theorem zb2b_transfer : forall n k : nat, (2 <= n)%nat -> (k <= Datatypes.S n)%nat ->
  QleT' (zb2_sup_Wt n k * (Z.of_nat (10 ^ n) # 1)) 1%Q ->
  QleT' (zb2_sup_Wt (Datatypes.S n) k * (Z.of_nat (10 ^ Datatypes.S n) # 1)) 1%Q.
Proof.
  intros n k Hn Hk Hcap.
  pose proof (qeqT_imp_qeq _ _ (zb2b_row_ratio n k)) as Hrr.
  pose proof (zb2b_T n k Hn Hk) as HT.
  assert (HTQ : ((Z.of_nat 10 # 1)
                 * ((Z.of_nat (Datatypes.S n) # 1) * (Z.of_nat (n + k + 1) # 1)
                    * (Z.of_nat (n + k + 1) # 1) * (Z.of_nat (n + k + 1) # 1)))
              <= ((Z.of_nat (2 * n + k + 2) # 1) * (Z.of_nat (2 * n + k + 2) # 1)
                  * (Z.of_nat (2 * n + k + 3) # 1) * (Z.of_nat (2 * n + k + 3) # 1))%Q).
  { unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
    assert (Hz : (Z.of_nat 10
                  * (Z.of_nat (Datatypes.S n)
                     * (Z.of_nat (n + k + 1)
                        * (Z.of_nat (n + k + 1) * Z.of_nat (n + k + 1))))
               <= Z.of_nat (2 * n + k + 2)
                  * (Z.of_nat (2 * n + k + 2)
                     * (Z.of_nat (2 * n + k + 3) * Z.of_nat (2 * n + k + 3))))%Z).
    { rewrite <- !Nat2Z.inj_mul. apply (proj1 (Nat2Z.inj_le _ _)). nia. }
    nia. }
  assert (EP : (Z.of_nat (10 ^ Datatypes.S n) # 1)
            == (Z.of_nat 10 # 1) * (Z.of_nat (10 ^ n) # 1)).
  { replace (10 ^ Datatypes.S n)%nat with (10 * 10 ^ n)%nat by (cbn [Nat.pow]; lia).
    unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. rewrite Nat2Z.inj_mul. lia. }
  assert (HMM2pos : 0 < ((Z.of_nat (2 * n + k + 2) # 1) * (Z.of_nat (2 * n + k + 2) # 1)
                         * (Z.of_nat (2 * n + k + 3) # 1) * (Z.of_nat (2 * n + k + 3) # 1))%Q).
  { apply zb2_sup_P4_lt; apply zb2_ia_natpos_lt; lia. }
  assert (HMM2ne : ~ (((Z.of_nat (2 * n + k + 2) # 1) * (Z.of_nat (2 * n + k + 2) # 1)
                       * (Z.of_nat (2 * n + k + 3) # 1) * (Z.of_nat (2 * n + k + 3) # 1)) == 0)%Q)
    by (apply zb2_ga_pos_neq0; exact HMM2pos).
  apply Qle_to_QleT'.
  apply (zb2_ia_cancel_r
          (zb2_sup_Wt (Datatypes.S n) k * (Z.of_nat (10 ^ Datatypes.S n) # 1)) 1%Q
          ((Z.of_nat (2 * n + k + 2) # 1) * (Z.of_nat (2 * n + k + 2) # 1)
           * (Z.of_nat (2 * n + k + 3) # 1) * (Z.of_nat (2 * n + k + 3) # 1)) HMM2pos).
  assert (HE1 : ((zb2_sup_Wt (Datatypes.S n) k * (Z.of_nat (10 ^ Datatypes.S n) # 1))
                 * ((Z.of_nat (2 * n + k + 2) # 1) * (Z.of_nat (2 * n + k + 2) # 1)
                    * (Z.of_nat (2 * n + k + 3) # 1) * (Z.of_nat (2 * n + k + 3) # 1)))
             == ((zb2_sup_Wt (Datatypes.S n) k
                  * ((Z.of_nat (2 * n + k + 2) # 1) * (Z.of_nat (2 * n + k + 2) # 1)
                     * (Z.of_nat (2 * n + k + 3) # 1) * (Z.of_nat (2 * n + k + 3) # 1)))
                 * (Z.of_nat (10 ^ Datatypes.S n) # 1))) by ring.
  rewrite HE1, EP, Hrr.
  assert (HE2 : (((zb2_sup_Wt n k
                   * ((Z.of_nat (Datatypes.S n) # 1) * (Z.of_nat (n + k + 1) # 1)
                      * (Z.of_nat (n + k + 1) # 1) * (Z.of_nat (n + k + 1) # 1)))
                  * ((Z.of_nat 10 # 1) * (Z.of_nat (10 ^ n) # 1))))
             == ((zb2_sup_Wt n k * (Z.of_nat (10 ^ n) # 1))
                 * ((Z.of_nat 10 # 1)
                    * ((Z.of_nat (Datatypes.S n) # 1) * (Z.of_nat (n + k + 1) # 1)
                       * (Z.of_nat (n + k + 1) # 1) * (Z.of_nat (n + k + 1) # 1))))) by ring.
  rewrite HE2.
  apply (Qle_trans _ (1%Q * ((Z.of_nat 10 # 1)
                             * ((Z.of_nat (Datatypes.S n) # 1) * (Z.of_nat (n + k + 1) # 1)
                                * (Z.of_nat (n + k + 1) # 1) * (Z.of_nat (n + k + 1) # 1))))).
  - apply Qmult_le_compat_r.
    + apply QleT'_to_Qle. exact Hcap.
    + apply Qmult_le_0_compat.
      * apply zb2_ia_natpos_ge.
      * apply Qmult_le_0_compat.
        -- apply Qmult_le_0_compat.
           ++ apply Qmult_le_0_compat.
              ** apply zb2_ia_natpos_ge.
              ** apply zb2_ia_natpos_ge.
           ++ apply zb2_ia_natpos_ge.
        -- apply zb2_ia_natpos_ge.
  - rewrite !Qmult_1_l. exact HTQ.
Qed.

(* ===================================================================== *)
(* §5 整行封顶：9 ≤ n 时全列 cap（基座 n = 9 全窗，步进＝§4，右缘＝降档链）   *)
(* ===================================================================== *)

Theorem zb2b_cap_row : forall n : nat, (9 <= n)%nat ->
  forall j : nat, QleT' (zb2_sup_Wt n j * (Z.of_nat (10 ^ n) # 1)) 1%Q.
Proof.
  intro n. induction n as [| n IH]; intro Hn.
  - exfalso. lia.
  - destruct (Nat.eq_dec n 8) as [H8 | Hne].
    + subst n. intro j.
      replace (Datatypes.S 8)%nat with 9%nat by lia.
      pose proof (zb2s2_Hpw_window_m8 j) as HW.
      pose proof (zb2s2_tenth_inv 8) as HTI.
      replace (Datatypes.S 8)%nat with 9%nat in HTI by lia.
      apply Qle_to_QleT'.
      apply (Qle_trans (zb2_sup_Wt 9 j * (Z.of_nat (10 ^ 9) # 1))
                       (((1 # 10) * q_pow (1 # 10) 8) * (Z.of_nat (10 ^ 9) # 1)) 1%Q).
      * apply Qmult_le_compat_r.
        -- apply QleT'_to_Qle. exact HW.
        -- apply zb2_ia_natpos_ge.
      * rewrite <- HTI. apply Qle_refl.
    + assert (Hn9 : (9 <= n)%nat) by lia.
      intro j.
      destruct (le_lt_dec j (Datatypes.S n)) as [Hjle | Hjgt].
      * apply (zb2b_transfer n j); [lia | lia | apply IH; exact Hn9].
      * apply Qle_to_QleT'.
        assert (Hd : j = (Datatypes.S n + (j - Datatypes.S n))%nat) by lia.
        pose proof (zb2_sup_fall_chain (Datatypes.S n) (j - Datatypes.S n) ltac:(lia)) as Hfc.
        rewrite <- Hd in Hfc.
        pose proof (zb2b_transfer n (Datatypes.S n) ltac:(lia) ltac:(lia)
                     (IH Hn9 (Datatypes.S n))) as HcapSn.
        apply (Qle_trans (zb2_sup_Wt (Datatypes.S n) j * (Z.of_nat (10 ^ Datatypes.S n) # 1))
                         (zb2_sup_Wt (Datatypes.S n) (Datatypes.S n)
                          * (Z.of_nat (10 ^ Datatypes.S n) # 1)) 1%Q).
        -- apply Qmult_le_compat_r; [exact Hfc | apply zb2_ia_natpos_ge].
        -- apply QleT'_to_Qle. exact HcapSn.
Qed.

(* 逐点封顶（整行封顶的特例化）。 *)
Theorem zb2b_cap : forall n k : nat, (9 <= n)%nat ->
  QleT' (zb2_sup_Wt n k * (Z.of_nat (10 ^ n) # 1)) 1%Q.
Proof.
  intros n k Hn. apply (zb2b_cap_row n Hn k).
Qed.

(* ===================================================================== *)
(* §6 终形：∀ m j, 8 ≤ m -> Wt(S m, j) ≤ (1/10)^(m+1)（零前提·无窗界）       *)
(* ===================================================================== *)

Theorem zb2b_Hpw_closed : forall m j : nat, (8 <= m)%nat ->
  QleT' (zb2_sup_Wt (Datatypes.S m) j) ((1 # 10) * q_pow (1 # 10) m).
Proof.
  intros m j Hm. destruct (Nat.eq_dec m 8) as [H8 | Hne].
  - subst m. replace (Datatypes.S 8)%nat with 9%nat by lia.
    apply (zb2s2_Hpw_window_m8 j).
  - assert (Hm9 : (9 <= m)%nat) by lia.
    pose proof (zb2b_cap_row (Datatypes.S m) ltac:(lia) j) as Hcap.
    pose proof (zb2s2_tenth_inv m) as HTI.
    apply Qle_to_QleT'.
    apply (zb2_ia_cancel_r (zb2_sup_Wt (Datatypes.S m) j) ((1 # 10) * q_pow (1 # 10) m)
             (Z.of_nat (10 ^ Datatypes.S m) # 1)).
    + apply zb2_ia_natpos_lt.
      assert (Hnz : (10 ^ Datatypes.S m <> 0)%nat) by (apply Nat.pow_nonzero; lia).
      lia.
    + apply (Qle_trans (zb2_sup_Wt (Datatypes.S m) j * (Z.of_nat (10 ^ Datatypes.S m) # 1)) 1%Q
               (((1 # 10) * q_pow (1 # 10) m) * (Z.of_nat (10 ^ Datatypes.S m) # 1))).
      * apply QleT'_to_Qle. exact Hcap.
      * rewrite <- HTI. apply Qle_refl.
Qed.

(* ===================================================================== *)
(* §7 尾舱：语句公理面自检                                                  *)
(* ===================================================================== *)

Print Assumptions zb2b_step1.
Print Assumptions zb2b_row_ratio.
Print Assumptions zb2b_T.
Print Assumptions zb2b_transfer.
Print Assumptions zb2b_cap_row.
Print Assumptions zb2b_cap.
Print Assumptions zb2b_Hpw_closed.
