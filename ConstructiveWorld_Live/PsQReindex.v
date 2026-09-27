(* ==========================================================================)
   PsQReindex.v — Beukers 变体级数的换序与衰减引理
   使命: rx_psQ_reindex（psQ 升幂与 bk_psd 降幂的换基，一般 n）、对角系数主件 rx_bv_c_diag（bv_c n n == q̃_n）、以及项比率十字衰减链 rx_bkC_ratio/rx_decay_nat/rx_term_decayQ——为部分和单调衰减给出 Q 层构造。
   依赖: QArith、List、Arith、ZArith、Lia；S01_BaseRing、S02_CauchyComplete、S03_QExp、PadeErrorIntegral、BeukersLists、BeukersVariant。
   对标: Delannoy 数与 Padé 逼近系数的恒等式（组合数学）。
   构造性: 零承认词面（全件 Qed）；语句面 Set（主件 QeqT/QleT′/QltT），Qeq/Qle 支撑引理 Prop 面仅作推理；可提取（独立检验文件 Obj.magic 计数 0）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树原地重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import  PadeErrorIntegral BeukersLists BeukersVariant.

Open Scope nat_scope.

(* ============================================================ *)
(* §A bk_psQ 工具三件：限位外延 / 首项剥离 / 公因子外提                   *)
(* ============================================================ *)

(* 限位逐点 Qeq ⟹ 和相等（k < N 处逐点） *)
Lemma rx_psQ_ext_lt : forall (N : nat) (f g : nat -> Q) (z : Q),
  (forall k : nat, k < N -> f k == g k) ->
  bk_psQ f N z == bk_psQ g N z.
Proof.
  intros N. induction N as [| N IH]; intros f g z H.
  - reflexivity.
  - cbn [bk_psQ].
    rewrite (IH f g z) by (intros k Hk; apply H; lia).
    rewrite (H N) by lia.
    reflexivity.
Qed.

(* 首项剥离：bk_psQ g (S N) z == g 0 + z·Σ_{k<N} g(S k)·z^k *)
Lemma rx_psQ_shift : forall (N : nat) (g : nat -> Q) (z : Q),
  bk_psQ g (Datatypes.S N) z == g 0 + z * bk_psQ (fun k : nat => g (Datatypes.S k)) N z.
Proof.
  intros N. induction N as [| N IH]; intros g z.
  - cbn [bk_psQ q_pow]. ring.
  - change (bk_psQ g (Datatypes.S (Datatypes.S N)) z)
      with ((bk_psQ g (Datatypes.S N) z
              + g (Datatypes.S N) * q_pow z (Datatypes.S N))%Q).
    change (bk_psQ (fun k : nat => g (Datatypes.S k)) (Datatypes.S N) z)
      with ((bk_psQ (fun k : nat => g (Datatypes.S k)) N z
              + g (Datatypes.S N) * q_pow z N)%Q).
    change (q_pow z (Datatypes.S N)) with (z * q_pow z N)%Q.
    rewrite IH. ring.
Qed.

(* 公因子外提：Σ c·h(k)·z^k == c·Σ h(k)·z^k *)
Lemma rx_psQ_scale : forall (N : nat) (c : Q) (h : nat -> Q) (z : Q),
  bk_psQ (fun k : nat => (c * h k)%Q) N z == c * bk_psQ h N z.
Proof.
  intros N. induction N as [| N IH]; intros c h z.
  - cbn [bk_psQ]. ring.
  - change (bk_psQ (fun k : nat => (c * h k)%Q) (Datatypes.S N) z)
      with ((bk_psQ (fun k : nat => (c * h k)%Q) N z
              + c * h N * q_pow z N)%Q).
    change (bk_psQ h (Datatypes.S N) z)
      with ((bk_psQ h N z + h N * q_pow z N)%Q).
    change (q_pow z (Datatypes.S N)) with (z * q_pow z N)%Q.
    rewrite IH. ring.
Qed.

(* ============================================================ *)
(* §B 主件①：reindex 换基小引理（升幂指标反转）                           *)
(* ============================================================ *)

Theorem rx_psQ_reindex : forall (n : nat) (g : nat -> Q),
  bk_psQ (fun k : nat => (g (Nat.sub n k) * q_pow (2 # 1)%Q k)%Q) (Datatypes.S n) 1%Q
  == bk_psQ (fun k : nat => (g k * q_pow (2 # 1)%Q (Nat.sub n k))%Q) (Datatypes.S n) 1%Q.
Proof.
  intros n. induction n as [| n IH]; intros g.
  - cbn [bk_psQ q_pow Nat.sub]. ring.
  - (* 左侧：首项剥离——g(S n) + 2·Σ_{k≤n} g(n−k)·2^k *)
    rewrite (rx_psQ_shift (Datatypes.S n)
               (fun k : nat => (g (Nat.sub (Datatypes.S n) k) * q_pow (2 # 1)%Q k)%Q) 1%Q).
    cbv beta.
    replace (Nat.sub (Datatypes.S n) 0) with (Datatypes.S n) by lia.
    replace (q_pow (2 # 1)%Q 0) with 1%Q by reflexivity.
    assert (Hb : bk_psQ (fun k : nat =>
                           (g (Nat.sub (Datatypes.S n) (Datatypes.S k))
                              * q_pow (2 # 1)%Q (Datatypes.S k))%Q)
                        (Datatypes.S n) 1%Q
                 == (2 # 1)%Q * bk_psQ (fun k : nat =>
                                           (g (Nat.sub n k) * q_pow (2 # 1)%Q k)%Q)
                                       (Datatypes.S n) 1%Q).
    { transitivity (bk_psQ (fun k : nat =>
                              ((2 # 1)%Q * (g (Nat.sub n k) * q_pow (2 # 1)%Q k))%Q)
                           (Datatypes.S n) 1%Q).
      - apply rx_psQ_ext_lt. intros k Hk.
        replace (Nat.sub (Datatypes.S n) (Datatypes.S k)) with (n - k) by lia.
        cbn [q_pow]. ring.
      - apply rx_psQ_scale. }
    rewrite Hb. rewrite IH.
    (* 右侧：末项剥离——2·Σ_{k≤n} g(k)·2^{n−k} + g(S n) *)
    assert (Hrhs : bk_psQ (fun k : nat =>
                             (g k * q_pow (2 # 1)%Q (Nat.sub (Datatypes.S n) k))%Q)
                          (Datatypes.S (Datatypes.S n)) 1%Q
                   == (2 # 1)%Q * bk_psQ (fun k : nat =>
                                             (g k * q_pow (2 # 1)%Q (Nat.sub n k))%Q)
                                         (Datatypes.S n) 1%Q
                      + g (Datatypes.S n)).
    { change (bk_psQ (fun k : nat =>
                        (g k * q_pow (2 # 1)%Q (Nat.sub (Datatypes.S n) k))%Q)
                     (Datatypes.S (Datatypes.S n)) 1%Q)
        with ((bk_psQ (fun k : nat =>
                         (g k * q_pow (2 # 1)%Q (Nat.sub (Datatypes.S n) k))%Q)
                     (Datatypes.S n) 1%Q
              + g (Datatypes.S n)
                   * q_pow (2 # 1)%Q (Nat.sub (Datatypes.S n) (Datatypes.S n))
                   * q_pow (1 # 1)%Q (Datatypes.S n))%Q).
      replace (Datatypes.S n - Datatypes.S n) with 0%nat by lia.
      cbn [q_pow].
      rewrite bk_q_pow_one.
      assert (Hc : bk_psQ (fun k : nat =>
                             (g k * q_pow (2 # 1)%Q (Nat.sub (Datatypes.S n) k))%Q)
                          (Datatypes.S n) 1%Q
                   == (2 # 1)%Q * bk_psQ (fun k : nat =>
                                             (g k * q_pow (2 # 1)%Q (Nat.sub n k))%Q)
                                         (Datatypes.S n) 1%Q).
      { transitivity (bk_psQ (fun k : nat =>
                                ((2 # 1)%Q * (g k * q_pow (2 # 1)%Q (n - k)))%Q)
                             (Datatypes.S n) 1%Q).
        - apply rx_psQ_ext_lt. intros k Hk.
          replace (Datatypes.S n - k) with (Datatypes.S (n - k)) by lia.
          cbn [q_pow]. ring.
        - apply rx_psQ_scale. }
      rewrite Hc. ring. }
    rewrite Hrhs. ring.
Qed.

(* ============================================================ *)
(* §C 主件①推论：bv_c n n == q̃_n（一般 n，QeqT Set 面）                 *)
(* ============================================================ *)

Lemma rx_negpow_double : forall k : nat, bv_negpow (k + k) == 1%Q.
Proof.
  intro k. induction k as [| k IH].
  - reflexivity.
  - replace (Datatypes.S k + Datatypes.S k)
      with (Datatypes.S (Datatypes.S (k + k))) by lia.
    cbn [bv_negpow]. rewrite IH. ring.
Qed.

(* nat 降幂和的 Q 像 == 升幂位权 bk_psQ（bk_half_psd 的反转变体） *)
Lemma rx_psdQ_desc : forall (n : nat) (h : nat -> nat),
  (Z.of_nat (bk_psd h (Datatypes.S n)) # 1)%Q
  == bk_psQ (fun k : nat =>
               ((Z.of_nat (h k) # 1) * q_pow (2 # 1)%Q (n - k))%Q)
            (Datatypes.S n) 1%Q.
Proof.
  intros n. induction n as [| n IH]; intros h.
  - cbn [bk_psd bk_psQ q_pow Nat.sub].
    replace (2 * 0)%nat with 0%nat by lia.
    cbn [Nat.add]. ring.
  - change (Z.of_nat (bk_psd h (Datatypes.S (Datatypes.S n))) # 1)
      with ((Z.of_nat (2 * bk_psd h (Datatypes.S n) + h (Datatypes.S n)) # 1))%Q.
    change (bk_psQ (fun k : nat =>
                      ((Z.of_nat (h k) # 1) * q_pow (2 # 1)%Q (Datatypes.S n - k))%Q)
                   (Datatypes.S (Datatypes.S n)) 1%Q)
      with ((bk_psQ (fun k : nat =>
                       ((Z.of_nat (h k) # 1) * q_pow (2 # 1)%Q (Datatypes.S n - k))%Q)
                   (Datatypes.S n) 1%Q
            + (Z.of_nat (h (Datatypes.S n)) # 1)
                 * q_pow (2 # 1)%Q (Datatypes.S n - Datatypes.S n)
                 * q_pow (1 # 1)%Q (Datatypes.S n))%Q).
    replace (Datatypes.S n - Datatypes.S n) with 0%nat by lia.
    cbn [q_pow].
    rewrite bk_q_pow_one.
    repeat rewrite Qmult_1_r.
    assert (Hc : bk_psQ (fun k : nat =>
                           ((Z.of_nat (h k) # 1)
                              * q_pow (2 # 1)%Q (Datatypes.S n - k))%Q)
                        (Datatypes.S n) 1%Q
                 == (2 # 1)%Q * bk_psQ (fun k : nat =>
                                           ((Z.of_nat (h k) # 1)
                                              * q_pow (2 # 1)%Q (n - k))%Q)
                                       (Datatypes.S n) 1%Q).
    { transitivity (bk_psQ (fun k : nat =>
                              ((2 # 1)%Q
                                 * ((Z.of_nat (h k) # 1)
                                    * q_pow (2 # 1)%Q (n - k)))%Q)
                           (Datatypes.S n) 1%Q).
      - apply rx_psQ_ext_lt. intros k Hk.
        replace (Datatypes.S n - k) with (Datatypes.S (n - k)) by lia.
        cbn [q_pow]. ring.
      - apply rx_psQ_scale. }
    rewrite Hc. rewrite <- IH.
    replace (2 # 1)%Q with (Z.of_nat 2 # 1)%Q by reflexivity.
    rewrite bk_Qmul_nat.
    symmetry. apply bk_Qadd_nat.
Qed.

(* 主件①推论：Laurent 对角系数 bv_c n n == q̃_n（一般 n） *)
Theorem rx_bv_c_diag : forall n : nat,
  QeqT (bv_c n n) ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n. apply qeq_imp_qeqT. unfold bv_c.
  assert (Hnp : bv_negpow (n + n) == 1%Q) by apply rx_negpow_double.
  rewrite Hnp, Qmult_1_l.
  (* 点态归一：门 true、2 幂指标 n−(n−a)=a、乘法交换归位 *)
  transitivity (bk_psQ (fun k : nat =>
                          ((Z.of_nat (bkC n (n - k) * bkC n k) # 1)
                             * q_pow (2 # 1)%Q k)%Q)
                       (Datatypes.S n) 1%Q).
  { apply rx_psQ_ext_lt. intros a Ha. cbv beta.
    assert (Ha1 : Nat.leb a n = true) by (apply Nat.leb_le; lia).
    assert (Ha2 : Nat.leb (n - a) n = true) by (apply Nat.leb_le; lia).
    rewrite Ha1, Ha2. cbn [andb].
    replace (n - (n - a)) with a by lia.
    replace (bkC n a * bkC n (n - a)) with (bkC n (n - a) * bkC n a)
      by (rewrite Nat.mul_comm; reflexivity).
    reflexivity. }
  (* reindex：升幂指标反转（以带红ex形对接引理句面） *)
  transitivity (bk_psQ (fun k : nat =>
                          ((fun i : nat =>
                              (Z.of_nat (bkC n i * bkC n (n - i)) # 1)%Q)
                             (Nat.sub n k) * q_pow (2 # 1)%Q k)%Q)
                       (Datatypes.S n) 1%Q).
  { apply rx_psQ_ext_lt. intros k Hk. cbv beta.
    replace (n - (n - k)) with k by lia. reflexivity. }
  assert (Hri := rx_psQ_reindex n
                   (fun i : nat => (Z.of_nat (bkC n i * bkC n (n - i)) # 1)%Q)).
  rewrite Hri.
  (* 降幂 nat 和承载 + 对称归位 == q̃_n（与 bv_delannoy_eq_qtilde 同链） *)
  transitivity (Z.of_nat (bk_psd (fun k : nat => bkC n k * bkC n (n - k))
                                  (Datatypes.S n)) # 1).
  { symmetry. apply (rx_psdQ_desc n (fun i : nat => bkC n i * bkC n (n - i))). }
  assert (Hext : bk_psd (fun k : nat => bkC n k * bkC n (n - k)) (Datatypes.S n)
                = bk_psd (fun k : nat => bkC n k * bkC n k) (Datatypes.S n)).
  { apply bk_psd_ext. intros k Hk.
    rewrite (bk_Qn_sym n k) by lia. reflexivity. }
  rewrite Hext. unfold bk_Qn_qtilde. reflexivity.
Qed.

(* 数值锚：q̃_3 == 63（与 bv_c33_anchor 对角互证） *)
Theorem rx_qtilde3_anchor : QeqT ((Z.of_nat (bk_Qn_qtilde 3) # 1)%Q) (63 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 对角数值锚：bv_c 3 3 == q̃_3（一般件的实例落地） *)
Theorem rx_c33_qtilde3 : QeqT (bv_c 3 3) ((Z.of_nat (bk_Qn_qtilde 3) # 1)%Q).
Proof. apply rx_bv_c_diag. Qed.

(* ============================================================ *)
(* §D 件2 可证首件：项比率十字衰减链（收敛桥不同族判定的机器承载）          *)
(* ============================================================ *)

(* 副件：第零列 C(j, 0) = 1 *)
Lemma rx_bkC_col0 : forall j : nat, bkC j 0 = 1.
Proof.
  induction j as [| j IH].
  - reflexivity.
  - cbn [bkC]. reflexivity.
Qed.

(* 副件：副对角线 C(S j, j) = S j *)
Lemma rx_bkC_subdiag : forall j : nat, bkC (Datatypes.S j) j = Datatypes.S j.
Proof.
  induction j as [| j IH].
  - reflexivity.
  - change (bkC (Datatypes.S (Datatypes.S j)) (Datatypes.S j))
      with (bkC (Datatypes.S j) j + bkC (Datatypes.S j) (Datatypes.S j)).
    rewrite (bkC_diag (Datatypes.S j)). rewrite IH. lia.
Qed.

(* 副件：第二列 C(j, 1) = j *)
Lemma rx_bkC_row1 : forall j : nat, bkC j 1 = j.
Proof.
  induction j as [| j IH].
  - reflexivity.
  - change (bkC (Datatypes.S j) 1) with (bkC j 0 + bkC j 1).
    rewrite rx_bkC_col0. rewrite IH. lia.
Qed.

(* 吸收恒等：C(j,k)·(j−k) == C(j,k+1)·(k+1)（k+1 ≤ j） *)
Lemma rx_bkC_absorb : forall j k : nat,
  Datatypes.S k <= j -> bkC j k * (j - k) = bkC j (Datatypes.S k) * Datatypes.S k.
Proof.
  induction j as [| j IH]; intros k Hk.
  - lia.
  - destruct k as [| k'].
    + change (bkC (Datatypes.S j) 0) with 1%nat.
      change (bkC (Datatypes.S j) (Datatypes.S 0)) with (bkC j 0 + bkC j 1).
      change (Datatypes.S j - 0) with (Datatypes.S j).
      rewrite rx_bkC_col0. rewrite rx_bkC_row1. lia.
    + cbn [bkC Nat.sub].
      destruct (le_lt_dec (Datatypes.S (Datatypes.S k')) j) as [Hjj | Hjj].
      * assert (IH1 := IH k' ltac:(lia)).
        assert (IH2 := IH (Datatypes.S k') ltac:(lia)).
        assert (HspL : (bkC j k' + bkC j (Datatypes.S k')) * (j - k')
                     = bkC j k' * (j - k') + bkC j (Datatypes.S k') * (j - k')) by ring.
        assert (HspR : (bkC j (Datatypes.S k') + bkC j (Datatypes.S (Datatypes.S k')))
                         * Datatypes.S (Datatypes.S k')
                     = bkC j (Datatypes.S k') * Datatypes.S (Datatypes.S k')
                       + bkC j (Datatypes.S (Datatypes.S k'))
                         * Datatypes.S (Datatypes.S k')) by ring.
        rewrite HspL, IH1, HspR, <- IH2.
        rewrite <- (Nat.mul_add_distr_l (bkC j (Datatypes.S k'))
                      (Datatypes.S k') (j - k')).
        replace (Datatypes.S k' + (j - k')) with (Datatypes.S j) by lia.
        rewrite <- (Nat.mul_add_distr_l (bkC j (Datatypes.S k'))
                      (Datatypes.S (Datatypes.S k')) (j - Datatypes.S k')).
        replace (Datatypes.S (Datatypes.S k') + (j - Datatypes.S k'))
          with (Datatypes.S j) by lia.
        reflexivity.
      * assert (Hk'j : Datatypes.S k' = j) by lia.
        subst j.
        rewrite rx_bkC_subdiag.
        rewrite (bkC_diag (Datatypes.S k')).
        rewrite (bkC_out (Datatypes.S k') (Datatypes.S (Datatypes.S k'))) by lia.
        replace (Datatypes.S k' - k') with 1%nat by lia.
        lia.
Qed.

(* 比率恒等：C(j+1,k)·(j+1−k) == C(j,k)·(j+1)（k ≤ j） *)
Lemma rx_bkC_ratio : forall j k : nat,
  k <= j -> bkC (Datatypes.S j) k * (Datatypes.S j - k) = bkC j k * Datatypes.S j.
Proof.
  induction j as [| j IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. reflexivity.
  - destruct k as [| k'].
    + reflexivity.
    + change (bkC (Datatypes.S (Datatypes.S j)) (Datatypes.S k'))
        with (bkC (Datatypes.S j) k' + bkC (Datatypes.S j) (Datatypes.S k')).
      change (Datatypes.S (Datatypes.S j) - Datatypes.S k')
        with (Datatypes.S j - k').
      destruct (le_lt_dec (Datatypes.S k') j) as [Hle | Hlt].
      * assert (Hab := rx_bkC_absorb j k' Hle).
        assert (IH1 := IH k' ltac:(lia)).
        assert (Hsp : (bkC (Datatypes.S j) k' + bkC (Datatypes.S j) (Datatypes.S k'))
                        * (Datatypes.S j - k')
                    = bkC (Datatypes.S j) k' * (Datatypes.S j - k')
                      + bkC (Datatypes.S j) (Datatypes.S k') * (Datatypes.S j - k')) by ring.
        rewrite Hsp, IH1.
        assert (HB : bkC (Datatypes.S j) (Datatypes.S k')
                   = bkC j k' + bkC j (Datatypes.S k')) by reflexivity.
        rewrite HB.
        rewrite (Nat.mul_add_distr_r (bkC j k') (bkC j (Datatypes.S k'))
                   (Datatypes.S j - k')).
        rewrite (Nat.mul_add_distr_r (bkC j k') (bkC j (Datatypes.S k'))
                   (Datatypes.S (Datatypes.S j))).
        replace (Datatypes.S j - k') with (Datatypes.S (j - k')) by lia.
        remember (Nat.sub j k') as d eqn:Hddef.
        assert (Hdrel : Datatypes.S d + k' = Datatypes.S k' + d) by lia.
        replace (Datatypes.S (Datatypes.S j)) with (Datatypes.S d + Datatypes.S k') by lia.
        replace (Datatypes.S j) with (Datatypes.S d + k') by lia.
        rewrite (Nat.mul_add_distr_l (bkC j k') (Datatypes.S d) k').
        rewrite (Nat.mul_add_distr_l (bkC j (Datatypes.S k'))
                   (Datatypes.S d) (Datatypes.S k')).
        rewrite <- Hab.
        nia.
      * assert (Hkj : k' = j) by lia. subst k'.
        rewrite rx_bkC_subdiag.
        rewrite (bkC_diag (Datatypes.S j)).
        replace (Datatypes.S j - j) with 1%nat by lia.
        lia.
Qed.

(* 全正系数三次型关键不等式（m = n + d 展开，差全正，ring + lia 定口） *)
Lemma rx_key_d : forall n d : nat,
  (n + (n + d) + 1) * ((n + 2 * (n + d) + 1) * (n + 2 * (n + d) + 2))
  <= ((3 * n + 2 * (n + d) + 3) * (3 * n + 2 * (n + d) + 4)) * ((n + d) + 1).
Proof.
  intros n d.
  assert (Hexp : (n + (n + d) + 1) * ((n + 2 * (n + d) + 1) * (n + 2 * (n + d) + 2))
                 + (7 * n * n * n + 12 * n * n * d + 4 * n * d * d + 33 * n * n
                    + 36 * n * d + 34 * n + 8 * d * d + 18 * d + 10)
               = ((3 * n + 2 * (n + d) + 3) * (3 * n + 2 * (n + d) + 4))
                 * ((n + d) + 1)) by ring.
  assert (HP : 0 <= (7 * n * n * n + 12 * n * n * d + 4 * n * d * d + 33 * n * n
                    + 36 * n * d + 34 * n + 8 * d * d + 18 * d + 10))
    by apply Nat.le_0_l.
  lia.
Qed.

(* 衰减 nat 核：n ≤ m ⟹ C(n+m+1,n)·(n+2m+1)(n+2m+2) ≤ C(n+m,n)·(3n+2m+3)(3n+2m+4) *)
Lemma rx_decay_nat : forall n m : nat,
  n <= m ->
  bkC (Datatypes.S (n + m)) n * ((n + 2 * m + 1) * (n + 2 * m + 2))
  <= bkC (n + m) n * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4)).
Proof.
  intros n m Hnm.
  assert (Hr := rx_bkC_ratio (n + m) n ltac:(lia)).
  replace (Datatypes.S (n + m) - n) with (m + 1) in Hr by lia.
  replace (Datatypes.S (n + m)) with (n + m + 1) in Hr by lia.
  assert (Hkey : (n + m + 1) * ((n + 2 * m + 1) * (n + 2 * m + 2))
                 <= ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4)) * (m + 1)).
  { replace m with (n + (m - n)) by lia. apply (rx_key_d n (m - n)). }
  assert (HswapL : bkC (Datatypes.S (n + m)) n
                     * ((n + 2 * m + 1) * (n + 2 * m + 2)) * (m + 1)
                 = bkC (Datatypes.S (n + m)) n * (m + 1)
                     * ((n + 2 * m + 1) * (n + 2 * m + 2))) by ring.
  assert (Hstep : bkC (Datatypes.S (n + m)) n
                    * ((n + 2 * m + 1) * (n + 2 * m + 2)) * (m + 1)
                  <= bkC (n + m) n * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4))
                       * (m + 1)).
  { rewrite HswapL.
    replace (Datatypes.S (n + m)) with (n + m + 1) by lia.
    rewrite Hr.
    rewrite <- (Nat.mul_assoc (bkC (n + m) n) (n + m + 1)
                  ((n + 2 * m + 1) * (n + 2 * m + 2))).
    rewrite <- (Nat.mul_assoc (bkC (n + m) n)
                  ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4)) (m + 1)).
    apply Nat.mul_le_mono_l. exact Hkey. }
  destruct (le_lt_dec (bkC (Datatypes.S (n + m)) n
                         * ((n + 2 * m + 1) * (n + 2 * m + 2)))
                      (bkC (n + m) n
                         * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4))))
    as [Hle | Hlt].
  - exact Hle.
  - exfalso.
    assert (Hlt2 := proj1 (Nat.mul_lt_mono_pos_r (m + 1) _ _ ltac:(lia)) Hlt).
    exact (Nat.lt_irrefl _ (Nat.le_lt_trans _ _ _ Hstep Hlt2)).
Qed.

(* Q 层小副件：正 Z 的单位分母像严格正 *)
Lemma rx_Qlt_Z1 : forall z : Z, (0 < z)%Z -> Qlt 0 (z # 1)%Q.
Proof.
  intros z Hz. unfold Qlt. cbn [Qnum Qden].
  rewrite !Z.mul_1_r. exact Hz.
Qed.

(* Qeq→Qle 桥接引理（stdlib 9.x 无 Qeq_le；按 DTPT_Entropy 的 xq_Qeq_le 同型写入本件） *)
Lemma rx_Qeq_le : forall x y : Q, x == y -> Qle x y.
Proof.
  intros x y H. rewrite <- H. apply Qle_refl.
Qed.

(* 衰减 Q 面：n ≤ m ⟹ bv_term n (S m) ≤ bv_term n m（QleT' Set 面） *)
Theorem rx_term_decayQ : forall n m : nat,
  n <= m -> QleT' (bv_term n (Datatypes.S m)) (bv_term n m).
Proof.
  intros n m Hnm. apply Qle_to_QleT'.
  assert (HposD : (0 < Z.of_nat (3 * n + 2 * m + 3))%Z) by lia.
  assert (HposE : (0 < Z.of_nat (3 * n + 2 * m + 4))%Z) by lia.
  assert (Hpm : (0 < (1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                    * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))%Q).
  { apply Qmult_lt_0_compat.
    - unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat.
        apply rx_Qlt_Z1. lia.
    - unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat.
        apply rx_Qlt_Z1. lia. }
  assert (Hpm0 : (0 <= (1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                      * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))%Q)
    by (apply Qlt_le_weak; exact Hpm).
  assert (HshapeS : bv_term n (Datatypes.S m)
    == ((Z.of_nat (bkC (Datatypes.S (n + m)) n) # 1)
          * ((Z.of_nat (n + 2 * m + 1) # 1) * (Z.of_nat (n + 2 * m + 2) # 1)
               * ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                  * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))))
          * (q_fact (n + 2 * m) * q_fact (2 * n + 1) / q_fact (3 * n + 2 * m + 2))).
  { unfold bv_term, Qdiv.
    replace (n + Datatypes.S m) with (Datatypes.S (n + m)) by lia.
    replace (n + 2 * Datatypes.S m)
      with (Datatypes.S (Datatypes.S (n + 2 * m))) by lia.
    replace (3 * n + 2 * Datatypes.S m + 2)
      with (Datatypes.S (Datatypes.S (3 * n + 2 * m + 2))) by lia.
    rewrite (q_fact_succ (Datatypes.S (n + 2 * m))), (q_fact_succ (n + 2 * m)).
    rewrite (q_fact_succ (Datatypes.S (3 * n + 2 * m + 2))),
            (q_fact_succ (3 * n + 2 * m + 2)).
    rewrite !Qinv_mult_distr.
    replace (Datatypes.S (Datatypes.S (n + 2 * m))) with (n + 2 * m + 2) by lia.
    replace (Datatypes.S (n + 2 * m)) with (n + 2 * m + 1) by lia.
    replace (Datatypes.S (Datatypes.S (3 * n + 2 * m + 2)))
      with (3 * n + 2 * m + 4) by lia.
    replace (Datatypes.S (3 * n + 2 * m + 2)) with (3 * n + 2 * m + 3) by lia.
    ring. }
  assert (HshapeT : bv_term n m
    == (Z.of_nat (bkC (n + m) n) # 1)
         * (q_fact (n + 2 * m) * q_fact (2 * n + 1) / q_fact (3 * n + 2 * m + 2))).
  { unfold bv_term, Qdiv. reflexivity. }
  assert (Hdec1 : (Z.of_nat (bkC (Datatypes.S (n + m)) n) # 1)
                    * ((Z.of_nat (n + 2 * m + 1) # 1)
                       * (Z.of_nat (n + 2 * m + 2) # 1))
                  == (Z.of_nat (bkC (Datatypes.S (n + m)) n
                                   * ((n + 2 * m + 1) * (n + 2 * m + 2))) # 1)).
  { repeat rewrite bk_Qmul_nat. reflexivity. }
  assert (Hdec2 : (Z.of_nat (bkC (n + m) n) # 1)
                    * ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                       * (Z.of_nat (3 * n + 2 * m + 4) # 1))
                  == (Z.of_nat (bkC (n + m) n
                                   * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4))) # 1)).
  { repeat rewrite bk_Qmul_nat. reflexivity. }
  assert (HdecQ : Qle ((Z.of_nat (bkC (Datatypes.S (n + m)) n) # 1)
                         * ((Z.of_nat (n + 2 * m + 1) # 1)
                            * (Z.of_nat (n + 2 * m + 2) # 1)))
                      ((Z.of_nat (bkC (n + m) n) # 1)
                         * ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                            * (Z.of_nat (3 * n + 2 * m + 4) # 1)))).
  { assert (H0 := bk_Qle_nat
                    (bkC (Datatypes.S (n + m)) n * ((n + 2 * m + 1) * (n + 2 * m + 2)))
                    (bkC (n + m) n * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4)))
                    (rx_decay_nat n m Hnm)).
    rewrite <- Hdec1 in H0. rewrite <- Hdec2 in H0. exact H0. }
  assert (HinvP : ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                     * (Z.of_nat (3 * n + 2 * m + 4) # 1))
                    * ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                       * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))
                  == 1%Q).
  { unfold Qdiv.
    rewrite !Qmult_1_l.
    rewrite <- (Qinv_mult_distr (Z.of_nat (3 * n + 2 * m + 3) # 1)
                                (Z.of_nat (3 * n + 2 * m + 4) # 1)).
    apply Qmult_inv_r.
    assert (HposAB : Qlt 0 ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                              * (Z.of_nat (3 * n + 2 * m + 4) # 1))).
    { apply Qmult_lt_0_compat; apply rx_Qlt_Z1; lia. }
    intro Hc. apply (Qlt_not_eq 0%Q _ HposAB). exact (Qeq_sym _ _ Hc). }
  assert (Hmul : Qle (((Z.of_nat (bkC (Datatypes.S (n + m)) n) # 1)
                         * ((Z.of_nat (n + 2 * m + 1) # 1)
                            * (Z.of_nat (n + 2 * m + 2) # 1)))
                        * ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                           * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1))))
                      (((Z.of_nat (bkC (n + m) n) # 1)
                         * ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                            * (Z.of_nat (3 * n + 2 * m + 4) # 1)))
                        * ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                           * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1))))).
  { apply Qmult_le_compat_r; assumption. }
  assert (E2 : (((Z.of_nat (bkC (n + m) n) # 1)
                   * ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                      * (Z.of_nat (3 * n + 2 * m + 4) # 1)))
                  * ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                     * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1))))
               == (Z.of_nat (bkC (n + m) n) # 1)).
  { rewrite <- (Qmult_assoc (Z.of_nat (bkC (n + m) n) # 1)
                  ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                     * (Z.of_nat (3 * n + 2 * m + 4) # 1))
                  ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                   * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))).
    rewrite HinvP. apply Qmult_1_r. }
  rewrite HshapeS, HshapeT.
  apply Qmult_le_compat_r.
  - apply (Qle_trans _ (((Z.of_nat (bkC (n + m) n) # 1)
                           * ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                              * (Z.of_nat (3 * n + 2 * m + 4) # 1)))
                          * ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                             * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1))))).
    + apply (Qle_trans _ ((Z.of_nat (bkC (Datatypes.S (n + m)) n) # 1)
                              * ((Z.of_nat (n + 2 * m + 1) # 1)
                                   * (Z.of_nat (n + 2 * m + 2) # 1))
                              * ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                                   * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1))))).
      { apply (rx_Qeq_le _ _). ring. }
      { exact Hmul. }
    + rewrite E2. apply Qle_refl.
  - apply Qlt_le_weak.
    unfold Qdiv.
    apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; apply q_fact_pos.
    + apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* 数值锚：n = m = 2 处衰减严格（x < y 分离见证） *)
Theorem rx_term_decay_anchor : QltT (bv_term 2 3) (bv_term 2 2).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* 假设审计留痕：Print Assumptions（G4 复核位）                          *)
(* ============================================================ *)

Print Assumptions rx_psQ_reindex.
Print Assumptions rx_bv_c_diag.
Print Assumptions rx_term_decayQ.
Print Assumptions rx_term_decay_anchor.
