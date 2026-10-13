(* ===================================================================== *)
(* 模块：u5c_zeta2_sup2                                                  *)
(* 使命：ζ(2) 线 Hpw 峰带有穷带族（k0 ≤ (m−1)/2）的二项式尾部下界机。      *)
(*   核心精确恒等式：逐点封顶量 zb2_sup_Wt n k 满足                       *)
(*     Wt(n,k)·((n+1)·C(2n+k+1,n+1))² == C(n+k,n)·(k+1)·(k+2)            *)
(*   （C(2n+k+1,n+1) = 大指标二项式系数；由 (2n+k+1)! = C·(n+1)!·(n+k)!   *)
(*   的 Pascal 归纳恒等式桥接 q_fact 而铸）。据此带族逐点封顶证书         *)
(*   Wt(S m,k) ≤ (1/10)·(1/10)^m 归约为纯 nat 二项式不等式：              *)
(*     10^(S m)·(k+1)·(k+2)·C(S m+k,S m) ≤ (S m+1)²·C(2m+k+3,m+2)²。     *)
(*   配合 u5c_zeta2_sup 的峰带归约定理 zb2_sup_Hpw_reduce，得窗口机：      *)
(*   带族 [k0, m+1] 的 nat 证书族在句即得全窗 ∀j 逐点封顶。               *)
(*   m = 8 档（带 [3,9] 七点）证书逐点可计算，故全窗封顶无条件闭合；       *)
(*   更高 m 档的带族证书属熵型下界（C(3n+1,n) ≥ (27/4)^n 型），本件       *)
(*   不铸，以显式 nat 前提位在句（GAPASUME 诚实接口，语句面零承认）。      *)
(* 依赖：Stdlib（QArith/ZArith/Arith/Lia/Setoid）；缓存根 S01_BaseRing、   *)
(*   S02_CauchyComplete、S03_QExp、BeukersLists（bkC/Pascal/正性件）；     *)
(*   tmine04 池 abl_z2_itg_carrier；本池 u5c_zeta2_gapA、u5c_zeta2_a1_sign、 *)
(*   u5c_zeta2_sup（zb2_sup_Wt/qeq_cancel_r/P4_lt/Hpw_reduce）。           *)
(* 构造性：纯构造性、零全局假设声明、零承认式语句；语句结论全 Set 层       *)
(*   （QleT'/QeqT），nat 证书前提为语句假设位非公理位；代数步全走 ring     *)
(*   整式通路与假设重写（逆元面走 Qmult_inv_r/Qinv 恒等，禁 field）。      *)
(* 编译配方：source Live/toolchain/env.sh && cd 沙箱/现役/abl_zeta2_pool && *)
(*   rocq c -native-compiler no -q -Q . ""                                *)
(*   -Q <绝对路径>/abl_tmine04_pool/zeta2 ""                              *)
(*   -Q <绝对路径>/vo_local_world_unified_0930 "" u5c_zeta2_sup2.v        *)
(* 对标：Beukers, Bull. London Math. Soc. 11 (1979) 级数估计；中央二项式   *)
(*   系数熵下界 C(m,r) ≥ (m/r)^r 型初等估计文献（Stirling 前初等档）。      *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_itg_carrier.
Require Import u5c_zeta2_gapA u5c_zeta2_a1_sign u5c_zeta2_sup.

Open Scope Q_scope.

(* ===================================================================== *)
(* §0 基础件：q_fact 正性与 10 的幂逆桥                                    *)
(* ===================================================================== *)

(* q_fact 严格正（逐档正因子乘积归纳） *)
Lemma zb2s2_qfact_pos : forall n : nat, QltT 0 (q_fact n).
Proof.
  induction n as [| n IH].
  - exact qltT_0_1.
  - cbn [q_fact]. apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + apply QltT_to_Qlt. exact IH.
Qed.

(* (1/10)·(1/10)^m·10^(m+1) == 1：封顶常数的幂逆桥（对 m 归纳） *)
Lemma zb2s2_tenth_inv : forall m : nat,
  (1 # 10) * q_pow (1 # 10) m * (Z.of_nat (10 ^ Datatypes.S m) # 1) == 1%Q.
Proof.
  induction m as [| m IH].
  - cbn [q_pow Nat.pow]. unfold Qeq, Qmult. cbn [Qnum Qden Qmult Pos.mul]. lia.
  - assert (EP : (Z.of_nat (10 ^ Datatypes.S (Datatypes.S m)) # 1)
              == (Z.of_nat 10 # 1) * (Z.of_nat (10 ^ Datatypes.S m) # 1)).
    { replace (10 ^ Datatypes.S (Datatypes.S m))%nat
        with (10 * 10 ^ Datatypes.S m)%nat by (cbn [Nat.pow]; lia).
      unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. rewrite Nat2Z.inj_mul. lia. }
    assert (E10 : (1 # 10) * (Z.of_nat 10 # 1) == 1%Q).
    { unfold Qeq, Qmult. cbn [Qnum Qden Qmult Pos.mul]. lia. }
    assert (ER : (1 # 10) * q_pow (1 # 10) (Datatypes.S m)
                 * (Z.of_nat (10 ^ Datatypes.S (Datatypes.S m)) # 1)
              == ((1 # 10) * q_pow (1 # 10) m * (Z.of_nat (10 ^ Datatypes.S m) # 1))
                 * ((1 # 10) * (Z.of_nat 10 # 1))).
    { cbn [q_pow]. rewrite EP. ring. }
    rewrite ER, IH, E10. reflexivity.
Qed.

(* ===================================================================== *)
(* §1 Pascal 桥：(2n+k+1)! = C(2n+k+1,n+1)·(n+1)!·(n+k)! 的 q_fact 形      *)
(* ===================================================================== *)

(* 一般形：N! = C(N,r)·r!·(N−r)!（对 N 归纳，Pascal 展开步档以
   双生恒等式两侧 IH 互喂；Q 层全 ring 整式通路）。 *)
Lemma zb2s2_qfact_bkC_bridge : forall N r : nat, (r <= N)%nat ->
  q_fact N == q_fact r * q_fact (N - r) * (Z.of_nat (bkC N r) # 1)%Q.
Proof.
  intro N. induction N as [| N IH]; intros r Hr.
  - assert (Hr0 : r = 0%nat) by lia. subst r.
    unfold Qeq. cbn [Nat.sub q_fact bkC Qmult Pos.mul Qnum Qden]. lia.
  - destruct r as [| r'].
    + cbn [Nat.sub bkC q_fact]. ring.
    + destruct (Nat.eq_dec r' N) as [Heq | Hne].
      * subst r'. rewrite bkC_diag.
        replace (Datatypes.S N - Datatypes.S N)%nat with 0%nat by lia.
        cbn [q_fact]. ring.
      * assert (Hr1 : (r' <= N)%nat) by lia.
        assert (Hr2 : (Datatypes.S r' <= N)%nat) by lia.
        pose proof (bkC_pascal_shift N (Datatypes.S r')) as HP.
        cbv iota in HP.
        pose proof (IH r' Hr1) as IH1.
        pose proof (IH (Datatypes.S r') Hr2) as IH2.
        assert (Eq1 : q_fact (N - r')
                   == (Z.of_nat (N - r') # 1) * q_fact (N - Datatypes.S r')).
        { assert (Eq0 : (N - r')%nat = Datatypes.S (N - Datatypes.S r')) by lia.
          rewrite Eq0. reflexivity. }
        assert (KEY : q_fact (Datatypes.S r') * q_fact (N - r')
                      * (Z.of_nat (bkC N (Datatypes.S r')) # 1)
                   == (Z.of_nat (N - r') # 1) * q_fact N).
        { rewrite Eq1.
          assert (K1 : q_fact (Datatypes.S r')
                       * ((Z.of_nat (N - r') # 1) * q_fact (N - Datatypes.S r'))
                       * (Z.of_nat (bkC N (Datatypes.S r')) # 1)
                    == (Z.of_nat (N - r') # 1)
                       * (q_fact (Datatypes.S r') * q_fact (N - Datatypes.S r')
                          * (Z.of_nat (bkC N (Datatypes.S r')) # 1))) by ring.
          rewrite K1, IH2. reflexivity. }
        assert (Eplus : (Z.of_nat (bkC N r' + bkC N (Datatypes.S r')) # 1)
                     == (Z.of_nat (bkC N r') # 1)
                        + (Z.of_nat (bkC N (Datatypes.S r')) # 1)).
        { unfold Qeq, Qplus. cbn [Qnum Qden Qmult]. rewrite Nat2Z.inj_add. lia. }
        rewrite <- HP. rewrite Eplus.
        replace (Datatypes.S N - Datatypes.S r')%nat with (N - r')%nat by lia.
        cbn [q_fact].
        assert (RW : (Z.of_nat (Datatypes.S r') # 1) * q_fact r' * q_fact (N - r')
                     * ((Z.of_nat (bkC N r') # 1) + (Z.of_nat (bkC N (Datatypes.S r')) # 1))
                  == (Z.of_nat (Datatypes.S r') # 1)
                     * (q_fact r' * q_fact (N - r') * (Z.of_nat (bkC N r') # 1))
                     + (Z.of_nat (N - r') # 1)
                       * (q_fact (Datatypes.S r') * q_fact (N - Datatypes.S r')
                          * (Z.of_nat (bkC N (Datatypes.S r')) # 1))).
        { rewrite Eq1.
          assert (Hs : q_fact (Datatypes.S r')
                    == (Z.of_nat (Datatypes.S r') # 1) * q_fact r') by reflexivity.
          rewrite Hs. ring. }
        rewrite RW, <- IH1, <- IH2.
        rewrite <- Qmult_plus_distr_l.
        assert (EF : (Z.of_nat (Datatypes.S r') # 1) + (Z.of_nat (N - r') # 1)
                  == (Z.of_nat (Datatypes.S N) # 1)).
        { unfold Qeq, Qplus. cbn [Qnum Qden Qmult]. lia. }
        rewrite EF. reflexivity.
Qed.

(* ===================================================================== *)
(* §2 核心精确恒等式：Wt(n,k)·((n+1)·C(2n+k+1,n+1))² == C(n+k,n)·(k+1)(k+2) *)
(* ===================================================================== *)

Lemma zb2s2_Wt_binom_eq : forall n k : nat,
  QeqT (zb2_sup_Wt n k
        * ((Z.of_nat (Datatypes.S n) # 1) * (Z.of_nat (Datatypes.S n) # 1)
           * (Z.of_nat (bkC (n + k + n + 1) (Datatypes.S n)) # 1)
           * (Z.of_nat (bkC (n + k + n + 1) (Datatypes.S n)) # 1)))
       ((Z.of_nat (bkC (n + k) n) # 1)
        * (Z.of_nat (Datatypes.S k) # 1) * (Z.of_nat (k + 2) # 1)).
Proof.
  intros n k.
  pose proof (zb2s2_qfact_bkC_bridge (n + k + n + 1) (Datatypes.S n) (ltac:(lia)))
    as HB0.
  replace (n + k + n + 1 - Datatypes.S n)%nat with (n + k)%nat in HB0 by lia.
  assert (HBq : q_fact (Datatypes.S n)
             == (Z.of_nat (Datatypes.S n) # 1) * q_fact n) by reflexivity.
  rewrite HBq in HB0.
  assert (EB : (Z.of_nat (Datatypes.S n * bkC (n + k + n + 1) (Datatypes.S n)) # 1)
            == (Z.of_nat (Datatypes.S n) # 1)
               * (Z.of_nat (bkC (n + k + n + 1) (Datatypes.S n)) # 1)).
  { unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. rewrite Nat2Z.inj_mul. lia. }
  assert (HB0' : q_fact (n + k + n + 1)
              == q_fact (n + k) * q_fact n
                 * (Z.of_nat (Datatypes.S n * bkC (n + k + n + 1) (Datatypes.S n)) # 1)).
  { rewrite EB, HB0. ring. }
  assert (HDp : 0 < (Z.of_nat (Datatypes.S n * bkC (n + k + n + 1) (Datatypes.S n)) # 1)%Q).
  { apply QltT_to_Qlt. apply zb2_ga_natpos_lt.
    pose proof (bkC_pos (n + k + n + 1) (Datatypes.S n) (ltac:(lia))). lia. }
  assert (HDn : ~ (Z.of_nat (Datatypes.S n * bkC (n + k + n + 1) (Datatypes.S n)) # 1 == 0))
    by (apply zb2_ga_pos_neq0; exact HDp).
  assert (HBf : (q_fact (n + k) * q_fact n / q_fact (n + k + n + 1))%Q
             == (/ (Z.of_nat (Datatypes.S n * bkC (n + k + n + 1) (Datatypes.S n)) # 1))%Q).
  { unfold Qdiv.
    apply (zb2_sup_qeq_cancel_r
             (q_fact (n + k) * q_fact n * / q_fact (n + k + n + 1))
             (/ (Z.of_nat (Datatypes.S n * bkC (n + k + n + 1) (Datatypes.S n)) # 1))
             _ HDn).
    transitivity (1%Q).
    - assert (HApos : 0 < q_fact (n + k) * q_fact n)
        by (apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply zb2s2_qfact_pos).
      assert (E1 : q_fact (n + k) * q_fact n
                   * / q_fact (n + k + n + 1)
                   * (Z.of_nat (Datatypes.S n * bkC (n + k + n + 1) (Datatypes.S n)) # 1)
                == (q_fact (n + k) * q_fact n
                    * (Z.of_nat (Datatypes.S n * bkC (n + k + n + 1) (Datatypes.S n)) # 1))
                   * / (q_fact (n + k) * q_fact n
                        * (Z.of_nat (Datatypes.S n * bkC (n + k + n + 1) (Datatypes.S n)) # 1))).
      { rewrite HB0'. ring. }
      rewrite E1. apply Qmult_inv_r.
      apply zb2_ga_pos_neq0. apply Qmult_lt_0_compat; assumption.
    - assert (E2 : / (Z.of_nat (Datatypes.S n * bkC (n + k + n + 1) (Datatypes.S n)) # 1)
                   * (Z.of_nat (Datatypes.S n * bkC (n + k + n + 1) (Datatypes.S n)) # 1)
                == 1).
      { rewrite Qmult_comm. apply Qmult_inv_r. exact HDn. }
      exact (Qeq_sym _ _ E2). }
  remember ((Z.of_nat (Datatypes.S n) # 1)
            * (Z.of_nat (bkC (n + k + n + 1) (Datatypes.S n)) # 1))%Q as X eqn:EXdef.
  apply qeq_imp_qeqT. unfold zb2_sup_Wt, zb2_term.
  rewrite HBf. rewrite EB.
  transitivity ((Z.of_nat (bkC (n + k) n) # 1) * (Z.of_nat (Datatypes.S k) # 1)
                * (Z.of_nat (k + 2) # 1)
                * ((/ X * X) * (/ X * X))).
  { rewrite EXdef. ring. }
  assert (EXX : (/ X * X)%Q == 1%Q).
  { rewrite Qmult_comm. apply Qmult_inv_r. rewrite EXdef.
    apply zb2_ga_pos_neq0. apply Qmult_lt_0_compat; apply QltT_to_Qlt.
    - apply zb2_ga_natpos_lt. lia.
    - apply zb2_ga_natpos_lt. apply bkC_pos. lia. }
  rewrite EXX. ring.
Qed.

(* ===================================================================== *)
(* §3 带族逐点证书机：nat 二项式证书 ⟹ 逐点封顶                            *)
(* ===================================================================== *)

(* 带族逐点证书定理：nat 二项式不等式（10^(m+1)·(k+1)(k+2)·C(m+1+k,m+1)
   ≤ (m+2)²·C(2m+k+3,m+2)²）在句即得 Wt(m+1,k) ≤ (1/10)·(1/10)^m。
   m = 8 档证书逐点可计算（§5）；更高档属熵型下界，显式前提位在句。 *)
Theorem zb2s2_band_cert : forall m k : nat,
  ((10 ^ Datatypes.S m) * (k + 1) * (k + 2) * bkC (Datatypes.S m + k) (Datatypes.S m)
   <= (Datatypes.S m + 1) * (Datatypes.S m + 1)
      * bkC (Datatypes.S m + k + Datatypes.S m + 1) (Datatypes.S (Datatypes.S m))
      * bkC (Datatypes.S m + k + Datatypes.S m + 1) (Datatypes.S (Datatypes.S m)))%nat ->
  QleT' (zb2_sup_Wt (Datatypes.S m) k) ((1 # 10) * q_pow (1 # 10) m).
Proof.
  intros m k Hcert.
  pose proof (zb2s2_Wt_binom_eq (Datatypes.S m) k) as Hbin.
  pose proof (qeqT_imp_qeq _ _ Hbin) as HbinQ.
  apply Qle_to_QleT'.
  assert (HCpos : 0 < (((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)
                        * (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)
                        * (Z.of_nat (bkC (Datatypes.S m + k + Datatypes.S m + 1)
                                        (Datatypes.S (Datatypes.S m))) # 1)
                        * (Z.of_nat (bkC (Datatypes.S m + k + Datatypes.S m + 1)
                                        (Datatypes.S (Datatypes.S m))) # 1))
                       * (Z.of_nat (10 ^ Datatypes.S m) # 1))%Q).
  { apply Qmult_lt_0_compat.
    - apply zb2_sup_P4_lt; apply zb2_ia_natpos_lt; try lia; apply bkC_pos; lia.
    - apply QltT_to_Qlt. apply zb2_ga_natpos_lt.
      assert (Hnz : (10 ^ Datatypes.S m <> 0)%nat) by (apply Nat.pow_nonzero; lia).
      lia. }
  apply (zb2_ia_cancel_r _ _ _ HCpos).
  assert (E1 : zb2_sup_Wt (Datatypes.S m) k
               * ((((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) * (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)
                    * (Z.of_nat (bkC (Datatypes.S m + k + Datatypes.S m + 1)
                                    (Datatypes.S (Datatypes.S m))) # 1)
                    * (Z.of_nat (bkC (Datatypes.S m + k + Datatypes.S m + 1)
                                    (Datatypes.S (Datatypes.S m))) # 1))
                   * (Z.of_nat (10 ^ Datatypes.S m) # 1)))
            == (Z.of_nat (bkC (Datatypes.S m + k) (Datatypes.S m)) # 1)
               * (Z.of_nat (Datatypes.S k) # 1) * (Z.of_nat (k + 2) # 1)
               * (Z.of_nat (10 ^ Datatypes.S m) # 1)).
  { rewrite Qmult_assoc, HbinQ. reflexivity. }
  assert (E2 : (1 # 10) * q_pow (1 # 10) m
               * ((((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) * (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)
                    * (Z.of_nat (bkC (Datatypes.S m + k + Datatypes.S m + 1)
                                    (Datatypes.S (Datatypes.S m))) # 1)
                    * (Z.of_nat (bkC (Datatypes.S m + k + Datatypes.S m + 1)
                                    (Datatypes.S (Datatypes.S m))) # 1))
                   * (Z.of_nat (10 ^ Datatypes.S m) # 1)))
            == ((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) * (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)
                * (Z.of_nat (bkC (Datatypes.S m + k + Datatypes.S m + 1)
                                (Datatypes.S (Datatypes.S m))) # 1)
                * (Z.of_nat (bkC (Datatypes.S m + k + Datatypes.S m + 1)
                                 (Datatypes.S (Datatypes.S m))) # 1))).
  { transitivity (((1 # 10) * q_pow (1 # 10) m * (Z.of_nat (10 ^ Datatypes.S m) # 1))
                  * ((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) * (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)
                     * (Z.of_nat (bkC (Datatypes.S m + k + Datatypes.S m + 1)
                                     (Datatypes.S (Datatypes.S m))) # 1)
                     * (Z.of_nat (bkC (Datatypes.S m + k + Datatypes.S m + 1)
                                      (Datatypes.S (Datatypes.S m))) # 1))).
    - ring.
    - rewrite zb2s2_tenth_inv. ring. }
  rewrite E1, E2.
  unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
  assert (Hz : (Z.of_nat (bkC (Datatypes.S m + k) (Datatypes.S m))
                * Z.of_nat (Datatypes.S k) * Z.of_nat (k + 2)
                * Z.of_nat (10 ^ Datatypes.S m)
             <= Z.of_nat (Datatypes.S m + 1) * Z.of_nat (Datatypes.S m + 1)
                * Z.of_nat (bkC (Datatypes.S m + k + Datatypes.S m + 1)
                                (Datatypes.S (Datatypes.S m)))
                * Z.of_nat (bkC (Datatypes.S m + k + Datatypes.S m + 1)
                                (Datatypes.S (Datatypes.S m))))%Z).
  { rewrite <- !Nat2Z.inj_mul. apply (proj1 (Nat2Z.inj_le _ _)). nia. }
  nia.
Qed.

(* ===================================================================== *)
(* §4 窗口机：带族 nat 证书族 + 峰带归约 ⟹ 全窗逐点封顶                     *)
(* ===================================================================== *)

(* 全窗封顶机：8 ≤ m、2·k0+2 ≤ m+1 时，带族 [k0, m+1] 的 nat 二项式
   证书族在句即得 ∀j 的 Wt(m+1,j) ≤ (1/10)·(1/10)^m（与 sup 峰带归约
   定理逐字对接：j < k0 升档链、带内直取、j > m+1 降档链）。 *)
Theorem zb2s2_Hpw_window : forall m k0 : nat, (8 <= m)%nat ->
  (2 * k0 + 2 <= Datatypes.S m)%nat ->
  (forall k : nat, (k0 <= k <= Datatypes.S m)%nat ->
     ((10 ^ Datatypes.S m) * (k + 1) * (k + 2) * bkC (Datatypes.S m + k) (Datatypes.S m)
      <= (Datatypes.S m + 1) * (Datatypes.S m + 1)
         * bkC (Datatypes.S m + k + Datatypes.S m + 1) (Datatypes.S (Datatypes.S m))
         * bkC (Datatypes.S m + k + Datatypes.S m + 1) (Datatypes.S (Datatypes.S m)))%nat) ->
  forall j : nat,
     QleT' (zb2_sup_Wt (Datatypes.S m) j) ((1 # 10) * q_pow (1 # 10) m).
Proof.
  intros m k0 Hm Hk0 Hband j.
  apply (zb2_sup_Hpw_reduce m k0 Hm Hk0).
  intros k Hk. apply zb2s2_band_cert. apply Hband. exact Hk.
Qed.

(* ===================================================================== *)
(* §5 m = 8 档无条件闭合：带 [3,9] 七点证书（数值化后线性可计算）            *)
(* ===================================================================== *)

(* 带内二项式系数数值件（Z 形·DM-A2 重铸）：经 §1 Pascal 桥反解（q_fact 线性
   求值）。数值全在 Z 二进制层合账——nat ≥5000 字面量呈 of_num_uint 滞涨形态，
   lia 不可判（原封存件于此红）。★独立复算修正：原封存件 zb2s2_bkC_25_10 抄作
   3268766，精确复算 C(25,10)=3268760（假件拦截四连·禁转抄未复算数）。 *)Lemma zb2s2_bkCZ_12_9 : Z.of_nat (bkC 12 9) = 220%Z.
Proof.
  pose proof (zb2s2_qfact_bkC_bridge 12 9 (ltac:(lia))) as H.
  cbn [Nat.sub q_fact] in H.
  unfold Qeq in H. cbn [Qnum Qden Qmult Pos.mul] in H.
  lia.
Qed.
Lemma zb2s2_bkCZ_13_9 : Z.of_nat (bkC 13 9) = 715%Z.
Proof.
  pose proof (zb2s2_qfact_bkC_bridge 13 9 (ltac:(lia))) as H.
  cbn [Nat.sub q_fact] in H.
  unfold Qeq in H. cbn [Qnum Qden Qmult Pos.mul] in H.
  lia.
Qed.
Lemma zb2s2_bkCZ_14_9 : Z.of_nat (bkC 14 9) = 2002%Z.
Proof.
  pose proof (zb2s2_qfact_bkC_bridge 14 9 (ltac:(lia))) as H.
  cbn [Nat.sub q_fact] in H.
  unfold Qeq in H. cbn [Qnum Qden Qmult Pos.mul] in H.
  lia.
Qed.
Lemma zb2s2_bkCZ_15_9 : Z.of_nat (bkC 15 9) = 5005%Z.
Proof.
  pose proof (zb2s2_qfact_bkC_bridge 15 9 (ltac:(lia))) as H.
  cbn [Nat.sub q_fact] in H.
  unfold Qeq in H. cbn [Qnum Qden Qmult Pos.mul] in H.
  lia.
Qed.
Lemma zb2s2_bkCZ_16_9 : Z.of_nat (bkC 16 9) = 11440%Z.
Proof.
  pose proof (zb2s2_qfact_bkC_bridge 16 9 (ltac:(lia))) as H.
  cbn [Nat.sub q_fact] in H.
  unfold Qeq in H. cbn [Qnum Qden Qmult Pos.mul] in H.
  lia.
Qed.
Lemma zb2s2_bkCZ_17_9 : Z.of_nat (bkC 17 9) = 24310%Z.
Proof.
  pose proof (zb2s2_qfact_bkC_bridge 17 9 (ltac:(lia))) as H.
  cbn [Nat.sub q_fact] in H.
  unfold Qeq in H. cbn [Qnum Qden Qmult Pos.mul] in H.
  lia.
Qed.
Lemma zb2s2_bkCZ_18_9 : Z.of_nat (bkC 18 9) = 48620%Z.
Proof.
  pose proof (zb2s2_qfact_bkC_bridge 18 9 (ltac:(lia))) as H.
  cbn [Nat.sub q_fact] in H.
  unfold Qeq in H. cbn [Qnum Qden Qmult Pos.mul] in H.
  lia.
Qed.
Lemma zb2s2_bkCZ_22_10 : Z.of_nat (bkC 22 10) = 646646%Z.
Proof.
  pose proof (zb2s2_qfact_bkC_bridge 22 10 (ltac:(lia))) as H.
  cbn [Nat.sub q_fact] in H.
  unfold Qeq in H. cbn [Qnum Qden Qmult Pos.mul] in H.
  lia.
Qed.
Lemma zb2s2_bkCZ_23_10 : Z.of_nat (bkC 23 10) = 1144066%Z.
Proof.
  pose proof (zb2s2_qfact_bkC_bridge 23 10 (ltac:(lia))) as H.
  cbn [Nat.sub q_fact] in H.
  unfold Qeq in H. cbn [Qnum Qden Qmult Pos.mul] in H.
  lia.
Qed.
Lemma zb2s2_bkCZ_24_10 : Z.of_nat (bkC 24 10) = 1961256%Z.
Proof.
  pose proof (zb2s2_qfact_bkC_bridge 24 10 (ltac:(lia))) as H.
  cbn [Nat.sub q_fact] in H.
  unfold Qeq in H. cbn [Qnum Qden Qmult Pos.mul] in H.
  lia.
Qed.
Lemma zb2s2_bkCZ_25_10 : Z.of_nat (bkC 25 10) = 3268760%Z.
Proof.
  pose proof (zb2s2_qfact_bkC_bridge 25 10 (ltac:(lia))) as H.
  cbn [Nat.sub q_fact] in H.
  unfold Qeq in H. cbn [Qnum Qden Qmult Pos.mul] in H.
  lia.
Qed.
Lemma zb2s2_bkCZ_26_10 : Z.of_nat (bkC 26 10) = 5311735%Z.
Proof.
  pose proof (zb2s2_qfact_bkC_bridge 26 10 (ltac:(lia))) as H.
  cbn [Nat.sub q_fact] in H.
  unfold Qeq in H. cbn [Qnum Qden Qmult Pos.mul] in H.
  lia.
Qed.
Lemma zb2s2_bkCZ_27_10 : Z.of_nat (bkC 27 10) = 8436285%Z.
Proof.
  pose proof (zb2s2_qfact_bkC_bridge 27 10 (ltac:(lia))) as H.
  cbn [Nat.sub q_fact] in H.
  unfold Qeq in H. cbn [Qnum Qden Qmult Pos.mul] in H.
  lia.
Qed.
Lemma zb2s2_bkCZ_28_10 : Z.of_nat (bkC 28 10) = 13123110%Z.
Proof.
  pose proof (zb2s2_qfact_bkC_bridge 28 10 (ltac:(lia))) as H.
  cbn [Nat.sub q_fact] in H.
  unfold Qeq in H. cbn [Qnum Qden Qmult Pos.mul] in H.
  lia.
Qed.
Lemma zb2s2_cert_m8_k3 : (10 ^ 9 * 4 * 5 * bkC 12 9 <= 10 * 10 * bkC 22 10 * bkC 22 10)%nat.
Proof.
  apply (proj2 (Nat2Z.inj_le _ _)).
  rewrite !Nat2Z.inj_mul, !Nat2Z.inj_pow.
  rewrite zb2s2_bkCZ_12_9, !zb2s2_bkCZ_22_10.
  cbn [Z.pow Z.of_nat]. lia.
Qed.
Lemma zb2s2_cert_m8_k4 : (10 ^ 9 * 5 * 6 * bkC 13 9 <= 10 * 10 * bkC 23 10 * bkC 23 10)%nat.
Proof.
  apply (proj2 (Nat2Z.inj_le _ _)).
  rewrite !Nat2Z.inj_mul, !Nat2Z.inj_pow.
  rewrite zb2s2_bkCZ_13_9, !zb2s2_bkCZ_23_10.
  cbn [Z.pow Z.of_nat]. lia.
Qed.
Lemma zb2s2_cert_m8_k5 : (10 ^ 9 * 6 * 7 * bkC 14 9 <= 10 * 10 * bkC 24 10 * bkC 24 10)%nat.
Proof.
  apply (proj2 (Nat2Z.inj_le _ _)).
  rewrite !Nat2Z.inj_mul, !Nat2Z.inj_pow.
  rewrite zb2s2_bkCZ_14_9, !zb2s2_bkCZ_24_10.
  cbn [Z.pow Z.of_nat]. lia.
Qed.
Lemma zb2s2_cert_m8_k6 : (10 ^ 9 * 7 * 8 * bkC 15 9 <= 10 * 10 * bkC 25 10 * bkC 25 10)%nat.
Proof.
  apply (proj2 (Nat2Z.inj_le _ _)).
  rewrite !Nat2Z.inj_mul, !Nat2Z.inj_pow.
  rewrite zb2s2_bkCZ_15_9, !zb2s2_bkCZ_25_10.
  cbn [Z.pow Z.of_nat]. lia.
Qed.
Lemma zb2s2_cert_m8_k7 : (10 ^ 9 * 8 * 9 * bkC 16 9 <= 10 * 10 * bkC 26 10 * bkC 26 10)%nat.
Proof.
  apply (proj2 (Nat2Z.inj_le _ _)).
  rewrite !Nat2Z.inj_mul, !Nat2Z.inj_pow.
  rewrite zb2s2_bkCZ_16_9, !zb2s2_bkCZ_26_10.
  cbn [Z.pow Z.of_nat]. lia.
Qed.
Lemma zb2s2_cert_m8_k8 : (10 ^ 9 * 9 * 10 * bkC 17 9 <= 10 * 10 * bkC 27 10 * bkC 27 10)%nat.
Proof.
  apply (proj2 (Nat2Z.inj_le _ _)).
  rewrite !Nat2Z.inj_mul, !Nat2Z.inj_pow.
  rewrite zb2s2_bkCZ_17_9, !zb2s2_bkCZ_27_10.
  cbn [Z.pow Z.of_nat]. lia.
Qed.
Lemma zb2s2_cert_m8_k9 : (10 ^ 9 * 10 * 11 * bkC 18 9 <= 10 * 10 * bkC 28 10 * bkC 28 10)%nat.
Proof.
  apply (proj2 (Nat2Z.inj_le _ _)).
  rewrite !Nat2Z.inj_mul, !Nat2Z.inj_pow.
  rewrite zb2s2_bkCZ_18_9, !zb2s2_bkCZ_28_10.
  cbn [Z.pow Z.of_nat]. lia.
Qed.
(* m = 8 档带族证书族逐点对接：带 [3,9] 七点 nat 证书全部由上述数值件
   线性闭出，全窗封顶无条件成立。 *)
Theorem zb2s2_Hpw_window_m8 : forall j : nat,
  QleT' (zb2_sup_Wt 9 j) ((1 # 10) * q_pow (1 # 10) 8).
Proof.
  apply (zb2s2_Hpw_window 8 3).
  - lia.
  - lia.
  - intros k Hk.
    (* 原封存件此处为扁平 10 支 intro-pattern（对 nat 非法·从未编达此点），
       DM-A2 重铸为 10 层嵌套 S-剥枝形。 *)
    destruct k as [|[|[|[|[|[|[|[|[|[|kR]]]]]]]]]]; try lia.
    + apply zb2s2_cert_m8_k3.
    + apply zb2s2_cert_m8_k4.
    + apply zb2s2_cert_m8_k5.
    + apply zb2s2_cert_m8_k6.
    + apply zb2s2_cert_m8_k7.
    + apply zb2s2_cert_m8_k8.
    + apply zb2s2_cert_m8_k9.
Qed.

(* ===================================================================== *)
(* §6 尾舱：语句公理面自检                                                  *)
(* ===================================================================== *)

Print Assumptions zb2s2_qfact_pos.
Print Assumptions zb2s2_tenth_inv.
Print Assumptions zb2s2_qfact_bkC_bridge.
Print Assumptions zb2s2_Wt_binom_eq.
Print Assumptions zb2s2_band_cert.
Print Assumptions zb2s2_Hpw_window.
Print Assumptions zb2s2_Hpw_window_m8.
