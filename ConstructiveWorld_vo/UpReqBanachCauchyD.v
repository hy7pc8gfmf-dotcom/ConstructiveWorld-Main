(* ==========================================================================)
   UpReqBanachCauchyD.v — Banach-Cauchy D：双重和的对角-三角估计
   使命: bxcd_ 系：bsum 折叠代数（pad_split/snoc/rev）、二项式项（binom_pos/fact/fact2）、F/G 范数界、Q2_bound 系与 bxcd_prod_near_one（乘积近一主定理）。
   依赖: S01_BaseRing、S02_CauchyComplete、S03_QExp、UpReqBanachExp/Prod/Double/ExpBasic/Add、UpReqNormConv、UpReqBanachProd2、UpReqBanachInvPre、BanachNoHyp；Stdlib QArith、Arith、ZArith、Setoid、Morphisms、Lia。
   对标: (1+x) 型双重和的范数估计（Banach 代数中的二项式展开控制）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachProd.
Require Import UpReqBanachDouble.
Require Import UpReqBanachExpBasic.
Require Import UpReqBanachAdd.
Require Import UpReqNormConv.
Require Import UpReqBanachProd2.
Require Import UpReqBanachInvPre.
Require Import BanachNoHyp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith ZArith.ZArith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia.

(* 级数项族：F a k := a^k/k!，G a k := (-a)^k/k! *)
Definition bxcd_F (B : BanachAlg) (a : (@BA B)) (k : nat) : (@BA B) :=
  @bmult B (bpow B a k) (@bcoef B (/ q_fact k)).

Definition bxcd_G (B : BanachAlg) (a : (@BA B)) (k : nat) : (@BA B) :=
  @bmult B (bpow B (bopp a) k) (@bcoef B (/ q_fact k)).

(* Q 项族：A c k := c^k/k! *)
Definition bxcd_A (c : Q) (k : nat) : Q := (q_pow c k / q_fact k)%Q.

(* 余项（方块减三角）：行 j 内 i > n-j 的对角外项之和 *)
Definition bxcd_U (B : BanachAlg) (a : (@BA B)) (n : nat) : (@BA B) :=
  bsum B (Datatypes.S n)
    (fun j : nat => bsum B (Datatypes.S n)
       (fun i : nat =>
          if Nat.ltb (n - j) i
          then @bmult B (bxcd_F B a j) (bxcd_G B a i)
          else @bzero B)).

(* ============================================================ *)
(* ① 等词代数小件                                                *)
(* ============================================================ *)

Lemma bxcd_bsum_zero : forall (B : BanachAlg) (n : nat) (f : nat -> (@BA B)),
  (forall k : nat, @bae B (f k) (@bzero B)) ->
  @bae B (bsum B n f) (@bzero B).
Proof.
  intros B n f Hf. induction n as [| m IH].
  - apply (@bae_refl B).
  - change (bsum B (Datatypes.S m) f) with (@bplus B (bsum B m f) (f m)).
    eapply bae_trans.
    + apply (@bplus_wd_l B (bsum B m f) (@bzero B) (f m)).
      exact IH.
    + eapply bae_trans.
      * exact (bplus_zero_l B (f m)).
      * exact (Hf m).
Qed.

(* 和分裂（补零垫）：Σ_{j≤n} F j == Σ_{j≤m} F j + Σ_{j≤n}[m<j] F j *)
Lemma bxcd_bsum_pad_split : forall (B : BanachAlg) (m n : nat)
                                   (F : nat -> (@BA B)),
  (m <= n)%nat ->
  @bae B (bsum B (Datatypes.S n) F)
         (@bplus B (bsum B (Datatypes.S m) F)
                   (bsum B (Datatypes.S n)
                      (fun j : nat =>
                         if Nat.ltb m j then F j else @bzero B))).
Proof.
  intros B m n F Hmn. induction n as [| n' IH].
  - assert (Hm : m = 0%nat) by lia. subst m.
    apply (@bae_sym B).
    eapply bae_trans.
    + apply (@bplus_wd_r B (@bplus B (@bzero B) (@bzero B)) (@bzero B)
                           (@bplus B (@bzero B) (F 0%nat))).
      exact (@bplus_zero_l B (@bzero B)).
    + exact (@bplus_zero B (@bplus B (@bzero B) (F 0%nat))).
  - destruct (Nat.eq_dec m (Datatypes.S n')) as [Heq | Hne].
    + subst m.
      assert (Hp : @bae B (bsum B (Datatypes.S (Datatypes.S n'))
                  (fun j : nat =>
                     if Nat.ltb (Datatypes.S n') j then F j else @bzero B))
                  (@bzero B)).
      { eapply bae_trans.
        - apply (bsum_ext B (Datatypes.S (Datatypes.S n'))
                  (fun j : nat =>
                     if Nat.ltb (Datatypes.S n') j then F j else @bzero B)
                  (fun j : nat => @bzero B)).
          intros k Hk.
          destruct (Nat.ltb (Datatypes.S n') k) eqn:Ek.
          + apply Nat.ltb_lt in Ek. exfalso. lia.
          + apply (@bae_refl B).
        - apply (bxcd_bsum_zero B _ (fun j : nat => @bzero B)).
          intros k. apply (@bae_refl B). }
      eapply bae_trans.
      * apply (@bae_sym B).
        eapply bae_trans.
        -- apply (@bplus_wd_r B (bsum B (Datatypes.S (Datatypes.S n'))
                                   (fun j : nat =>
                                      if Nat.ltb (Datatypes.S n') j
                                      then F j else @bzero B))
                           (@bzero B)
                           (bsum B (Datatypes.S (Datatypes.S n')) F)).
           exact Hp.
        -- exact (@bplus_zero B (bsum B (Datatypes.S (Datatypes.S n')) F)).
      * apply (@bae_refl B).
    + assert (Hmlt : Nat.ltb m (Datatypes.S n') = true)
        by (apply Nat.ltb_lt; lia).
      assert (Hmn' : (m <= n')%nat) by lia.
      change (bsum B (Datatypes.S (Datatypes.S n')) F)
        with (@bplus B (bsum B (Datatypes.S n') F) (F (Datatypes.S n'))).
      change (bsum B (Datatypes.S (Datatypes.S n'))
                (fun j : nat => if Nat.ltb m j then F j else @bzero B))
        with (@bplus B (bsum B (Datatypes.S n')
                          (fun j : nat => if Nat.ltb m j then F j else @bzero B))
                       (if Nat.ltb m (Datatypes.S n')
                        then F (Datatypes.S n') else @bzero B)).
      rewrite Hmlt.
      eapply bae_trans.
      * apply (@bplus_wd_l B). exact (IH Hmn').
      * apply (@bae_sym B).
        exact (@bplus_assoc B (bsum B (Datatypes.S m) F)
                (bsum B (Datatypes.S n')
                   (fun j : nat => if Nat.ltb m j then F j else @bzero B))
                (F (Datatypes.S n'))).
Qed.
(* 尾项拆出（定义形）：Σ_{j≤S n} f j == (Σ_{j<n} f j) + f n *)
Lemma bxcd_bsum_snoc : forall (B : BanachAlg) (n : nat) (f : nat -> (@BA B)),
  @bae B (bsum B (Datatypes.S n) f) (@bplus B (bsum B n f) (f n)).
Proof.
  intros B n f. apply (@bae_refl B).
Qed.

(* 和反序：Σ_{j≤n} h j == Σ_{j≤n} h (n−j) *)
Lemma bxcd_bsum_rev : forall (B : BanachAlg) (n : nat) (h : nat -> (@BA B)),
  @bae B (bsum B (Datatypes.S n) h)
         (bsum B (Datatypes.S n) (fun j : nat => h (Nat.sub n j))).
Proof.
  intros B n. induction n as [| n' IH]; intros h.
  - apply (@bae_refl B).
    (* 中件 M := h (S n') + Σ_{k≤n'} h (n'−k) *)
  - apply (@bae_trans B _
      (@bplus B (h (Datatypes.S n'))
                (bsum B (Datatypes.S n')
                   (fun k : nat => h (Nat.sub n' k)))) _).
    + eapply bae_trans.
      * apply (@bplus_comm B (bsum B (Datatypes.S n') h)
                              (h (Datatypes.S n'))).
      * apply (@bplus_wd_r B (bsum B (Datatypes.S n') h)
                 (bsum B (Datatypes.S n')
                    (fun k : nat => h (Nat.sub n' k)))
                 (h (Datatypes.S n'))).
        exact (IH h).
    + (* h (S n') + Σ_{k≤n'} h (n'−k) == Σ_{j≤S n'} h (S n'−j)（rot） *)
      apply (@bae_sym B).
      apply (@bsum_rot B (Datatypes.S n')
               (fun j : nat => h (Nat.sub (Datatypes.S n') j))).
Qed.
(* 对角块 == 和式（t = G 下标升序）：dline i k == Σ_{t≤k} F(i+k−t)·G t *)
Lemma bxcd_dline_bsum : forall (B : BanachAlg)
                               (F G : nat -> (@BA B)) (i k : nat),
  @bae B (bd2_dline B F G i k)
         (bsum B (Datatypes.S k)
            (fun t : nat =>
               @bmult B (F (Nat.add i (Nat.sub k t))) (G t))).
Proof.
  intros B F G i k. revert i. induction k as [| m IH]; intros i.
  - assert (Hi : ((Nat.add i (Nat.sub 0%nat 0%nat)) = i)%nat) by lia.
    change (bsum B (Datatypes.S 0%nat)
              (fun t : nat => @bmult B (F (Nat.add i (Nat.sub 0%nat t))) (G t)))
      with (@bplus B (@bzero B)
              (@bmult B (F (Nat.add i (Nat.sub 0%nat 0%nat))) (G 0%nat))).
    rewrite Hi.
    apply (@bae_sym B).
    apply (@bplus_zero_l B (@bmult B (F i) (G 0%nat))).
  - change (bd2_dline B F G i (Datatypes.S m))
      with (@bplus B (@bmult B (F i) (G (Datatypes.S m)))
                     (bd2_dline B F G (Datatypes.S i) m)).
    change (bsum B (Datatypes.S (Datatypes.S m))
              (fun t : nat => @bmult B (F (Nat.add i (Nat.sub (Datatypes.S m) t)))
                                       (G t)))
      with (@bplus B (bsum B (Datatypes.S m)
                       (fun t : nat =>
                          @bmult B (F (Nat.add i (Nat.sub (Datatypes.S m) t)))
                                   (G t)))
                     (@bmult B (F (Nat.add i (Nat.sub (Datatypes.S m) (Datatypes.S m))))
                              (G (Datatypes.S m)))).
    assert (Hi0 : ((Nat.add i (Nat.sub (Datatypes.S m) (Datatypes.S m))) = i)%nat) by lia.
    rewrite Hi0.
    apply (@bae_trans B _
      (@bplus B (@bmult B (F i) (G (Datatypes.S m)))
                (bsum B (Datatypes.S m)
                   (fun t : nat =>
                      @bmult B (F (Nat.add (Datatypes.S i) (Nat.sub m t)))
                               (G t)))) _).
    + apply (@bplus_wd_r B (bd2_dline B F G (Datatypes.S i) m)
                           (bsum B (Datatypes.S m)
                              (fun t : nat =>
                                 @bmult B (F (Nat.add (Datatypes.S i)
                                                      (Nat.sub m t)))
                                          (G t)))
                           (@bmult B (F i) (G (Datatypes.S m)))).
      exact (IH (Datatypes.S i)).
    + eapply bae_trans.
      * apply (@bplus_wd_r B
                 (bsum B (Datatypes.S m)
                    (fun t : nat =>
                       @bmult B (F (Nat.add (Datatypes.S i) (Nat.sub m t)))
                                (G t)))
                 (bsum B (Datatypes.S m)
                    (fun t : nat =>
                       @bmult B (F (Nat.add i (Nat.sub (Datatypes.S m) t)))
                                (G t)))
                 (@bmult B (F i) (G (Datatypes.S m)))).
        apply (bsum_ext B (Datatypes.S m)
          (fun t : nat =>
             @bmult B (F (Nat.add (Datatypes.S i) (Nat.sub m t))) (G t))
          (fun t : nat =>
             @bmult B (F (Nat.add i (Nat.sub (Datatypes.S m) t))) (G t))).
        intros t Ht.
        assert (Hij : (Nat.add (Datatypes.S i) (Nat.sub m t))
                      = (Nat.add i (Nat.sub (Datatypes.S m) t))) by lia.
        rewrite Hij.
        apply (@bae_refl B).
      * apply (@bplus_comm B (@bmult B (F i) (G (Datatypes.S m)))
                             (bsum B (Datatypes.S m)
                                (fun t : nat =>
                                   @bmult B (F (Nat.add i
                                                      (Nat.sub (Datatypes.S m) t)))
                                            (G t)))).
Qed.

(* diagf == bsum（同递归形） *)
Lemma bxcd_diagf_bsum : forall (B : BanachAlg)
                               (F G : nat -> (@BA B)) (i n : nat),
  @bae B (bd2_diagf B F G i n)
         (bsum B (Datatypes.S n)
            (fun k : nat => bd2_dline B F G i k)).
Proof.
  intros B F G i n. induction n as [| m IH].
  - apply (@bae_sym B).
    apply (@bplus_zero_l B (bd2_dline B F G i 0%nat)).
  - change (bd2_diagf B F G i (Datatypes.S m))
      with (@bplus B (bd2_diagf B F G i m)
                     (bd2_dline B F G i (Datatypes.S m))).
    change (bsum B (Datatypes.S (Datatypes.S m))
              (fun k : nat => bd2_dline B F G i k))
      with (@bplus B (bsum B (Datatypes.S m)
                          (fun k : nat => bd2_dline B F G i k))
                     (bd2_dline B F G i (Datatypes.S m))).
    apply (@bplus_wd_l B). exact IH.
Qed.

(* ============================================================ *)
(* ② 标量中心重排（依存 Prod2 bpr2_bterm_split，零新证）          *)
(* ============================================================ *)

(* 项级：F a j · G a i == (a^j·(-a)^i)·bcoef(/j!·/i!)
   —— Prod2 交付的七步标量中心链（a^j·b^i 乘序不动）直接特化。 *)
Lemma bxcd_scal_term : forall (B : BanachAlg) (a : (@BA B)) (j i : nat),
  @bae B (@bmult B (bxcd_F B a j) (bxcd_G B a i))
         (@bmult B (@bmult B (bpow B a j) (bpow B (@bopp B a) i))
                   (@bcoef B (Qinv (q_fact j) * Qinv (q_fact i))%Q)).
Proof.
  intros B a j i.
  unfold bxcd_F, bxcd_G.
  assert (Hs := bpr2_bterm_split B a (bopp a) (Nat.add j i) j).
  assert (Hij : (Nat.sub (Nat.add j i) j = i)%nat) by lia.
  rewrite Hij in Hs.
  exact Hs.
Qed.

(* ============================================================ *)
(* ③ Q 层系数桥（Pascal↔阶乘，bpa_binom 出界/配对坍缩段）         *)
(* ============================================================ *)

(* 组合数正性（j ≤ k；配对归纳，出界/对角边界清零） *)
Lemma bxcd_binom_pos : forall k j : nat, (j <= k)%nat -> Qlt 0 (bpa_binom k j).
Proof.
  induction k as [| k' IH]; intros j Hj.
  - assert (Hj0 : j = 0%nat) by lia. subst j.
    exact (q_fact_pos 0%nat).
  - destruct (Nat.eq_dec j (Datatypes.S k')) as [Heq | Hne].
    + subst j.
      change (bpa_binom (Datatypes.S k') (Datatypes.S k'))
        with ((bpa_binom k' k' + bpa_binom k' (Datatypes.S k'))%Q).
      rewrite (bpa_binom_out k' (Datatypes.S k') ltac:(lia)).
      rewrite (bpa_binom_diag k').
      exact (q_fact_pos 0%nat).
    + destruct j as [| j'].
      * exact (q_fact_pos 0%nat).
      * change (bpa_binom (Datatypes.S k') (Datatypes.S j'))
          with ((bpa_binom k' j' + bpa_binom k' (Datatypes.S j'))%Q).
        apply (Qplus_lt_compat 0%Q (bpa_binom k' j') 0%Q
                 (bpa_binom k' (Datatypes.S j'))
                 (IH j' ltac:(lia))
                 (IH (Datatypes.S j') ltac:(lia))).
Qed.

(* 整式桥：C(k,j)·j!·(k−j)! == k!（j ≤ k；双 IH 乘 Z 系数合并） *)
Lemma bxcd_binom_fact2 : forall k j : nat, (j <= k)%nat ->
  ((bpa_binom k j * q_fact j) * q_fact (Nat.sub k j) == q_fact k)%Q.
Proof.
  induction k as [| k' IH]; intros j Hj.
  - assert (Hj0 : j = 0%nat) by lia. subst j. reflexivity.
  - destruct (Nat.eq_dec j (Datatypes.S k')) as [Heq | Hne].
    + subst j.
      change (bpa_binom (Datatypes.S k') (Datatypes.S k'))
        with ((bpa_binom k' k' + bpa_binom k' (Datatypes.S k'))%Q).
      rewrite (bpa_binom_out k' (Datatypes.S k') ltac:(lia)).
      rewrite (bpa_binom_diag k').
      assert (Hz0 : Nat.sub (Datatypes.S k') (Datatypes.S k') = 0%nat) by lia.
      rewrite Hz0.
      change (q_fact 0%nat) with 1%Q.
      ring.
    + destruct j as [| j'].
      * assert (Hs : (Nat.sub (Datatypes.S k') 0%nat) = (Datatypes.S k')) by lia.
        rewrite Hs.
        change (bpa_binom (Datatypes.S k') 0%nat) with 1%Q.
        change (q_fact 0%nat) with 1%Q.
        ring.
      * change (bpa_binom (Datatypes.S k') (Datatypes.S j'))
          with ((bpa_binom k' j' + bpa_binom k' (Datatypes.S j'))%Q).
        assert (Hjk : (Datatypes.S j' <= k')%nat) by lia.
        assert (Hrk : (Nat.sub k' j' = Datatypes.S (Nat.sub k' (Datatypes.S j')))) by lia.
        assert (Hrk' : Nat.sub (Datatypes.S k') (Datatypes.S j')
                       = Datatypes.S (Nat.sub k' (Datatypes.S j'))) by lia.
        assert (IH1 := IH j' ltac:(lia)).
        assert (IH2 := IH (Datatypes.S j') ltac:(lia)).
        rewrite Hrk in IH1. rewrite Hrk'.
        change (q_fact (Datatypes.S j'))
          with ((Z.of_nat (Datatypes.S j') # 1) * q_fact j')%Q.
        change (q_fact (Datatypes.S j'))
          with ((Z.of_nat (Datatypes.S j') # 1) * q_fact j')%Q in IH2.
        change (q_fact (Datatypes.S (Nat.sub k' (Datatypes.S j'))))
          with ((Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j'))) # 1)
                * q_fact (Nat.sub k' (Datatypes.S j')))%Q.
        change (q_fact (Datatypes.S (Nat.sub k' (Datatypes.S j'))))
          with ((Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j'))) # 1)
                * q_fact (Nat.sub k' (Datatypes.S j')))%Q in IH1.
        change (q_fact (Datatypes.S k'))
          with ((Z.of_nat (Datatypes.S k') # 1) * q_fact k')%Q.
        assert (Hn1 : (Nat.sub k' (Datatypes.S j') + Datatypes.S j')%nat
                      = k')
          by (apply Nat.sub_add; exact Hjk).
        assert (Hz : (Z.of_nat (Datatypes.S j')
                      + Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j'))))%Z
                     = Z.of_nat (Datatypes.S k')).
        { assert (Hn : (Datatypes.S j'
                        + Datatypes.S (Nat.sub k' (Datatypes.S j')))%nat
                       = Datatypes.S k').
          { rewrite (Nat.add_succ_r (Datatypes.S j')
                      (Nat.sub k' (Datatypes.S j'))).
            apply f_equal.
            rewrite (Nat.add_comm (Datatypes.S j')
                      (Nat.sub k' (Datatypes.S j'))).
            exact Hn1. }
          rewrite <- Nat2Z.inj_add. rewrite Hn. reflexivity. }
        assert (Hz2 : ((Z.of_nat (Datatypes.S j') # 1)
                       + (Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j'))) # 1))%Q
                      == (Z.of_nat (Datatypes.S k') # 1)%Q).
        { unfold Qeq. cbn [Qnum Qden Qplus].
          repeat rewrite Z.mul_1_l. repeat rewrite Z.mul_1_r.
          rewrite Hz. reflexivity. }
        transitivity (((bpa_binom k' j' * ((Z.of_nat (Datatypes.S j') # 1)
                                            * q_fact j'))
                       * ((Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j')))
                           # 1) * q_fact (Nat.sub k' (Datatypes.S j'))))
                      + (bpa_binom k' (Datatypes.S j')
                         * ((Z.of_nat (Datatypes.S j') # 1) * q_fact j'))
                       * ((Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j')))
                           # 1) * q_fact (Nat.sub k' (Datatypes.S j'))))%Q.
        { ring. }
        transitivity ((((bpa_binom k' j' * q_fact j')
                        * ((Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j')))
                            # 1) * q_fact (Nat.sub k' (Datatypes.S j'))))
                       * (Z.of_nat (Datatypes.S j') # 1))
                      + ((bpa_binom k' (Datatypes.S j')
                            * ((Z.of_nat (Datatypes.S j') # 1) * q_fact j'))
                         * q_fact (Nat.sub k' (Datatypes.S j')))
                       * (Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j')))
                           # 1))%Q.
        { ring. }
        rewrite IH1. rewrite IH2.
        transitivity (((Z.of_nat (Datatypes.S j') # 1)
                       + (Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j')))
                           # 1)) * q_fact k')%Q.
        { ring. }
        rewrite Hz2. reflexivity.
Qed.

(* 逆式桥：C(k,j)·/k! == /j!·/(k−j)!（j ≤ k；fact2+右消去四步） *)
Lemma bxcd_binom_fact : forall k j : nat, (j <= k)%nat ->
  ((bpa_binom k j * / q_fact k) == / q_fact j * / q_fact (Nat.sub k j))%Q.
Proof.
  intros k j Hj.
  assert (H2 := bxcd_binom_fact2 k j Hj).
  assert (HLX : Qlt 0 ((q_fact j * q_fact (Nat.sub k j))%Q))
    by (apply ncv_qmult_lt0; apply q_fact_pos).
  assert (HX : ~ (q_fact j * q_fact (Nat.sub k j))%Q == 0)
    by exact (q_neq_of_lt _ HLX).
  assert (HY : ~ q_fact k == 0) by exact (q_neq_of_lt _ (q_fact_pos k)).
  transitivity (((bpa_binom k j * / q_fact k) * 1)%Q).
  { symmetry. apply Qmult_1_r. }
  transitivity (((bpa_binom k j * / q_fact k)
                 * ((q_fact j * q_fact (Nat.sub k j))
                    * / (q_fact j * q_fact (Nat.sub k j)))))%Q.
  { rewrite <- (Qmult_inv_r (q_fact j * q_fact (Nat.sub k j))%Q HX).
    reflexivity. }
  transitivity ((((bpa_binom k j * q_fact j) * q_fact (Nat.sub k j))
                 * / q_fact k)
                * / (q_fact j * q_fact (Nat.sub k j)))%Q.
  { ring. }
  rewrite H2.
  transitivity (((q_fact k * / q_fact k)
                 * / (q_fact j * q_fact (Nat.sub k j))))%Q.
  { ring. }
  rewrite (Qmult_inv_r (q_fact k) HY).
  transitivity ((/ (q_fact j * q_fact (Nat.sub k j)))%Q).
  { apply Qmult_1_l. }
  apply Qinv_mult_distr.
Qed.

(* ============================================================ *)
(* ④ 方块分解：P == bone + U（柯西方块→三角坍缩→余项）            *)
(* ============================================================ *)

Definition bxcd_T (B : BanachAlg) (a : (@BA B)) (n : nat) : (@BA B) :=
  bsum B (Datatypes.S n)
    (fun j : nat => bsum B (Datatypes.S (Nat.sub n j))
       (fun i : nat => @bmult B (bxcd_F B a j) (bxcd_G B a i))).

(* 对角块 == 二项式行：dline→反序→逐项标量桥→二项式行 *)
Lemma bxcd_dline_binom_term : forall (B : BanachAlg) (a : (@BA B)),
  forall k : nat,
    @bae B (bd2_dline B (bxcd_F B a) (bxcd_G B a) 0%nat k)
           (@bmult B (bpow B (@bplus B a (@bopp B a)) k)
                     (@bcoef B (/ q_fact k))).
Proof.
  intros B a k.
  apply (@bae_trans B _
    (bsum B (Datatypes.S k)
       (fun j : nat =>
          @bmult B (@bcoef B (bpa_binom k j * / q_fact k)%Q)
                   (@bmult B (bpow B a j)
                             (bpow B (@bopp B a) (Nat.sub k j))))) _).
  - apply (@bae_trans B _
      (bsum B (Datatypes.S k)
         (fun t : nat =>
            @bmult B (bxcd_F B a (Nat.sub k t)) (bxcd_G B a t))) _).
    + exact (bxcd_dline_bsum B (bxcd_F B a) (bxcd_G B a) 0%nat k).
    + apply (@bae_trans B _
        (bsum B (Datatypes.S k)
           (fun j : nat =>
              @bmult B (bxcd_F B a (Nat.sub k (Nat.sub k j)))
                       (bxcd_G B a (Nat.sub k j)))) _).
      * exact (bxcd_bsum_rev B k
                  (fun x : nat =>
                     @bmult B (bxcd_F B a (Nat.sub k x)) (bxcd_G B a x))).
      * apply bsum_ext. intros j Hj.
        assert (Hkj : ((Nat.sub k (Nat.sub k j)) = j)%nat) by lia.
        rewrite Hkj.
        eapply bae_trans.
        -- exact (bxcd_scal_term B a j (Nat.sub k j)).
        -- apply (@bae_trans B _
              (@bmult B (@bcoef B (Qinv (q_fact j)
                                        * Qinv (q_fact (Nat.sub k j)))%Q)
                        (@bmult B (bpow B a j)
                                  (bpow B (@bopp B a) (Nat.sub k j)))) _).
           ++ exact (@bcoef_comm B
                       (Qinv (q_fact j) * Qinv (q_fact (Nat.sub k j)))%Q
                       (@bmult B (bpow B a j)
                                (bpow B (@bopp B a) (Nat.sub k j)))).
           ++ apply (@bpr2_bmult_wd_l B _ _ _).
              apply (@bcoef_wd B).
              symmetry. exact (bxcd_binom_fact k j ltac:(lia)).
  - apply (@bae_sym B).
    exact (bnh_esp_term_binom B a (@bopp B a)
             (binv_mult_opp_swap B a) k).
Qed.

(* 三角和 == 单位元 *)
Lemma bxcd_tri_bone : forall (B : BanachAlg) (a : (@BA B)),
  forall n : nat, @bae B (bxcd_T B a n) (@bone B).
Proof.
  intros B a n.
  apply (@bae_trans B _ (bd2_tri B n (bxcd_F B a) (bxcd_G B a)) _).
  - apply (@bae_sym B).
    apply (@bae_trans B _
      (bsum B (Datatypes.S n)
         (fun i : nat => @bmult B (bxcd_F B a i)
                    (bsum B (Datatypes.S (Nat.sub n i)) (bxcd_G B a)))) _).
    + exact (bd2_tri_eq_rect_row B n (bxcd_F B a) (bxcd_G B a)).
    + apply bsum_ext. intros j _.
      apply (@bae_sym B).
      exact (bsum_mult_l B (Datatypes.S (Nat.sub n j)) (bxcd_F B a j)
               (bxcd_G B a)).
  - apply (@bae_trans B _ (bd2_diag B n (bxcd_F B a) (bxcd_G B a)) _).
    + exact (bd2_tri_eq_diag B n (bxcd_F B a) (bxcd_G B a)).
    + apply (@bae_trans B _
        (exp_series_partial B (@bplus B a (@bopp B a)) n) _).
      * apply (@bae_trans B _
          (bsum B (Datatypes.S n)
             (fun k : nat =>
                bd2_dline B (bxcd_F B a) (bxcd_G B a) 0%nat k)) _).
        -- exact (bxcd_diagf_bsum B (bxcd_F B a) (bxcd_G B a) 0%nat n).
        -- apply (@bae_trans B _
              (bsum B (Datatypes.S n)
                 (fun k : nat =>
                    @bmult B (bpow B (@bplus B a (@bopp B a)) k)
                              (@bcoef B (/ q_fact k)))) _).
           ++ apply (@bsum_ext B (Datatypes.S n)
                 (fun k : nat => bd2_dline B (bxcd_F B a) (bxcd_G B a) 0%nat k)
                 (fun k : nat =>
                    @bmult B (bpow B (@bplus B a (@bopp B a)) k)
                              (@bcoef B (/ q_fact k)))).
              intros k _.
              exact (bxcd_dline_binom_term B a k).
           ++ apply (@bae_sym B).
              exact (esp_as_bsum B (@bplus B a (@bopp B a)) n).
      * exact (binv_esp_opp_add B a n).
Qed.

(* 主分解：P == bone + U *)
Lemma bxcd_prod_split : forall (B : BanachAlg) (a : (@BA B)),
  forall n : nat,
    @bae B (@bmult B (exp_series_partial B a n)
                     (exp_series_partial B (@bopp B a) n))
           (@bplus B (@bone B) (bxcd_U B a n)).
Proof.
  intros B a n.
  apply (@bae_trans B _
    (bsum B (Datatypes.S n)
       (fun j : nat => bsum B (Datatypes.S n)
          (fun i : nat => @bmult B (bxcd_F B a j) (bxcd_G B a i)))) _).
  { exact (esp_prod_square B a (@bopp B a) n). }
  apply (@bae_trans B _
    (bsum B (Datatypes.S n)
       (fun j : nat =>
          @bplus B (bsum B (Datatypes.S (Nat.sub n j))
                      (fun i : nat => @bmult B (bxcd_F B a j) (bxcd_G B a i)))
                   (bsum B (Datatypes.S n)
                      (fun i : nat =>
                         if Nat.ltb (Nat.sub n j) i
                         then @bmult B (bxcd_F B a j) (bxcd_G B a i)
                         else @bzero B)))) _).
  { apply bsum_ext. intros j _. apply bxcd_bsum_pad_split. lia. }
  apply (@bae_trans B _ (@bplus B (bxcd_T B a n) (bxcd_U B a n)) _).
  { exact (bsum_plus B (Datatypes.S n)
             (fun j : nat => bsum B (Datatypes.S (Nat.sub n j))
                              (fun i : nat => @bmult B (bxcd_F B a j)
                                                (bxcd_G B a i)))
             (fun j : nat => bsum B (Datatypes.S n)
                              (fun i : nat =>
                                 if Nat.ltb (Nat.sub n j) i
                                 then @bmult B (bxcd_F B a j) (bxcd_G B a i)
                                 else @bzero B))). }
  apply (@bplus_wd_l B (bxcd_T B a n) (@bone B) (bxcd_U B a n)).
  exact (bxcd_tri_bone B a n).
Qed.

(* 范数桥：bae P (bone+U) ⟹ ‖P−bone‖ == ‖U‖ *)
Lemma bxcd_prod_close : forall (B : BanachAlg) (a : (@BA B)) (n : nat)
                               (U : (@BA B)),
  @bae B (@bmult B (exp_series_partial B a n)
                   (exp_series_partial B (@bopp B a) n))
         (@bplus B (@bone B) U) ->
  QeqT (@bnorm B (@bplus B (@bmult B (exp_series_partial B a n)
                                    (exp_series_partial B (@bopp B a) n))
                          (@bopp B (@bone B)))) (@bnorm B U).
Proof.
  intros B a n U H. apply (@bnorm_wd B).
  eapply bae_trans.
  { exact (@bplus_wd B (@bmult B (exp_series_partial B a n)
                              (exp_series_partial B (@bopp B a) n))
                       (@bopp B (@bone B))
                       (@bplus B (@bone B) U) (@bopp B (@bone B))
                       H (@bae_refl B (@bopp B (@bone B)))). }
  apply (@bae_trans B _ (@bplus B (@bplus B (@bone B) (@bopp B (@bone B))) U) _).
  { exact (@bplus_middle_swap B (@bone B) U (@bopp B (@bone B))). }
  apply (@bae_trans B _ (@bplus B (@bzero B) U) _).
  { apply (@bplus_wd_l B (@bplus B (@bone B) (@bopp B (@bone B))) (@bzero B) U
             (@bplus_opp B (@bone B))). }
  exact (bplus_zero_l B U).
Qed.

(* ============================================================ *)
(* ⑤ 范数尾界（NormConv+尾和控制）                                *)
(* ============================================================ *)

Lemma bxcd_bsum_norm_le : forall (B : BanachAlg) (x : nat -> (@BA B)) (n : nat),
  QleT' (@bnorm B (bsum B (Datatypes.S n) x))
        (ncv_qsum (fun k : nat => @bnorm B (x k)) (Datatypes.S n)).
Proof.
  intros B x n. induction n as [| m IH].
  - change (bsum B (Datatypes.S 0%nat) x)
      with (@bplus B (@bzero B) (x 0%nat)).
    change (ncv_qsum (fun k : nat => @bnorm B (x k)) (Datatypes.S 0%nat))
      with (ncv_qsum (fun k : nat => @bnorm B (x k)) 0%nat + @bnorm B (x 0%nat))%Q.
    change (ncv_qsum (fun k : nat => @bnorm B (x k)) 0%nat) with 0%Q.
    eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _
               (@bnorm_wd B (@bplus B (@bzero B) (x 0%nat)) (x 0%nat)
                  (@bplus_zero_l B (x 0%nat))))).
    apply qeq_leT'. apply Qeq_sym. apply Qplus_0_l.
  - change (bsum B (Datatypes.S (Datatypes.S m)) x)
      with (@bplus B (bsum B (Datatypes.S m) x) (x (Datatypes.S m))).
    change (ncv_qsum (fun k => @bnorm B (x k)) (Datatypes.S (Datatypes.S m)))
      with (ncv_qsum (fun k => @bnorm B (x k)) (Datatypes.S m)
            + @bnorm B (x (Datatypes.S m)))%Q.
    eapply qleT'_trans.
    + exact (@bnorm_plus B (bsum B (Datatypes.S m) x) (x (Datatypes.S m))).
    + apply (qleT'_plus_compat _ _ _ _).
      * exact IH.
      * apply qleT'_refl.
Qed.

Lemma bxcd_F_norm_le : forall (B : BanachAlg) (a : (@BA B)) (c : Q),
  Id c (@bnorm B a) ->
  forall j : nat, Qle (@bnorm B (bxcd_F B a j)) (bxcd_A c j).
Proof.
  intros B a c Hc j. unfold bxcd_F, bxcd_A.
  eapply Qle_trans.
  - exact (QleT'_to_Qle _ _
            (@bnorm_mult B (bpow B a j) (@bcoef B (/ q_fact j)))).
  - rewrite (@bnorm_coef_qeq B (/ q_fact j)).
    apply (Qle_trans _ ((q_pow (@bnorm B a) j) * Qabs (/ q_fact j))%Q).
    + apply (Qmult_le_compat_r (@bnorm B (bpow B a j))
                               (q_pow (@bnorm B a) j) (Qabs (/ q_fact j))).
      * apply QleT'_to_Qle. exact (bnorm_bpow B a j).
      * rewrite (Qabs_pos (/ q_fact j)
                   (Qlt_le_weak 0 (/ q_fact j)
                      (Qinv_lt_0_compat _ (q_fact_pos j)))).
        apply Qlt_le_weak. exact (Qinv_lt_0_compat _ (q_fact_pos j)).
    + rewrite <- Hc.
      rewrite (Qabs_pos (/ q_fact j)
                 (Qlt_le_weak 0 (/ q_fact j)
                    (Qinv_lt_0_compat _ (q_fact_pos j)))).
      apply Qle_refl.
Qed.

Lemma bxcd_G_norm_le : forall (B : BanachAlg) (a : (@BA B)) (c : Q),
  Id c (@bnorm B a) ->
  forall i : nat, Qle (@bnorm B (bxcd_G B a i)) (bxcd_A c i).
Proof.
  intros B a c Hc i. unfold bxcd_G, bxcd_A.
  eapply Qle_trans.
  - exact (QleT'_to_Qle _ _
            (@bnorm_mult B (bpow B (@bopp B a) i) (@bcoef B (/ q_fact i)))).
  - rewrite (@bnorm_coef_qeq B (/ q_fact i)).
    apply (Qle_trans _ ((q_pow (@bnorm B a) i) * Qabs (/ q_fact i))%Q).
    + apply (Qmult_le_compat_r (@bnorm B (bpow B (@bopp B a) i))
                               (q_pow (@bnorm B a) i) (Qabs (/ q_fact i))).
      * apply QleT'_to_Qle.
        apply (qleT'_trans _ (q_pow (@bnorm B (@bopp B a)) i)%Q _).
        -- exact (bnorm_bpow B (@bopp B a) i).
        -- rewrite (@bnorm_opp B a). apply qleT'_refl.
      * rewrite (Qabs_pos (/ q_fact i)
                   (Qlt_le_weak 0 (/ q_fact i)
                      (Qinv_lt_0_compat _ (q_fact_pos i)))).
        apply Qlt_le_weak. exact (Qinv_lt_0_compat _ (q_fact_pos i)).
    + rewrite <- Hc.
      rewrite (Qabs_pos (/ q_fact i)
                 (Qlt_le_weak 0 (/ q_fact i)
                    (Qinv_lt_0_compat _ (q_fact_pos i)))).
      apply Qle_refl.
Qed.

(* 4 参乘法单调（全参非负限定；stdlib 无裸 Qmult_le_compat） *)
Lemma bxcd_Qmult_le_compat_nonneg : forall u v w x : Q,
  Qle u v -> Qle w x -> Qle 0 w -> Qle 0 v ->
  Qle (u * w) (v * x).
Proof.
  intros u v w x Huv Hwx Hw Hv.
  apply (Qle_trans _ (v * w)%Q).
  - exact (Qmult_le_compat_r u v w Huv Hw).
  - rewrite (Qmult_comm v w).
    apply (Qle_trans _ (x * v)%Q).
    + exact (Qmult_le_compat_r w x v Hwx Hv).
    + rewrite (Qmult_comm x v). apply Qle_refl.
Qed.

Lemma bxcd_Qmult_le_compat_l : forall u v w : Q,
  Qle 0 w -> Qle u v -> Qle (w * u) (w * v).
Proof.
  intros u v w Hw Huv.
  rewrite (Qmult_comm w u), (Qmult_comm w v).
  exact (Qmult_le_compat_r u v w Huv Hw).
Qed.

Lemma bxcd_A_ge0 : forall (c : Q), Qle 0 c -> forall i : nat, Qle 0 (bxcd_A c i).
Proof.
  intros c Hc i. unfold bxcd_A.
  apply (Qle_trans _ (((q_pow c i / q_fact i) * (1 + 1)%Q) * / (1 + 1)%Q)%Q).
  - assert (Hm : Qle (0 * 0)%Q
                   (((q_pow c i / q_fact i) * (1 + 1)%Q) * / (1 + 1)%Q)%Q)
      by (apply bxcd_Qmult_le_compat_nonneg;
            [ exact (q_pow_fact2_nonneg c i Hc)
            | apply Qlt_le_weak; change (1+1)%Q with (q_fact 2%nat);
              apply Qinv_lt_0_compat; apply q_fact_pos
            | apply Qle_refl
            | exact (q_pow_fact2_nonneg c i Hc) ]).
    rewrite Qmult_0_l in Hm. exact Hm.
  - assert (Hf : (((q_pow c i / q_fact i) * (1 + 1)%Q) * / (1 + 1)%Q)
                 == (q_pow c i / q_fact i)).
    { field; apply q_neq_of_lt; exact (q_fact_pos i). }
    rewrite Hf. apply Qle_refl.
Qed.


Lemma bxcd_term_norm : forall (B : BanachAlg) (a : (@BA B)) (c : Q),
  Id c (@bnorm B a) ->
  forall j i : nat,
    Qle (@bnorm B (@bmult B (bxcd_F B a j) (bxcd_G B a i)))
        ((bxcd_A c j * bxcd_A c i)%Q).
Proof.
  intros B a c Hc j i.
  eapply Qle_trans.
  - exact (QleT'_to_Qle _ _ (@bnorm_mult B (bxcd_F B a j) (bxcd_G B a i))).
  - assert (Hc0 : Qle 0 c)
      by (rewrite Hc; apply QleT'_to_Qle; apply (@bnorm_pos B a)).
    apply bxcd_Qmult_le_compat_nonneg.
    + exact (bxcd_F_norm_le B a c Hc j).
    + exact (bxcd_G_norm_le B a c Hc i).
    + apply QleT'_to_Qle. exact (@bnorm_pos B (bxcd_G B a i)).
    + apply bxcd_A_ge0. exact Hc0.
Qed.

Lemma bxcd_qtail_ge0 : forall (c : Q), Qle 0 c ->
  forall m n : nat, Qle 0 (exp_tail_abs m n c).
Proof.
  intros c Hc m. induction n as [| n' IH].
  - apply Qle_refl.
  - change (exp_tail_abs m (Datatypes.S n') c)
      with ((exp_tail_abs m n' c
             + (if Nat.leb m n'
                then (q_pow c (Datatypes.S n') / q_fact (Datatypes.S n'))%Q
                else 0%Q))%Q).
    destruct (Nat.leb m n').
    + exact (Qplus_le_compat 0 (exp_tail_abs m n' c) 0
               (q_pow c (Datatypes.S n') / q_fact (Datatypes.S n')) IH
               (bxcd_A_ge0 c Hc (Datatypes.S n'))).
    + rewrite (Qplus_0_r (exp_tail_abs m n' c)). exact IH.
Qed.

Lemma bxcd_qtail_add : forall (c : Q) (m p n : nat),
  (m <= p)%nat -> (p <= n)%nat ->
  exp_tail_abs m n c == (exp_tail_abs m p c + exp_tail_abs p n c)%Q.
Proof.
  intros c m p n Hmp Hpn. induction n as [| n' IH].
  - assert (Hp0 : p = 0%nat) by lia. subst p.
    change (exp_tail_abs 0%nat 0%nat c) with 0%Q.
    ring.
  - destruct (Nat.eq_dec p (Datatypes.S n')) as [Heq | Hne].
    + subst p.
      rewrite (exp_tail_abs_le_m (Datatypes.S n') (Datatypes.S n') c (Nat.le_refl _)).
      ring.
    + assert (Hpn' : (p <= n')%nat) by lia.
      change (exp_tail_abs m (Datatypes.S n') c)
        with ((exp_tail_abs m n' c
               + (if Nat.leb m n'
                  then (q_pow c (Datatypes.S n') / q_fact (Datatypes.S n'))%Q
                  else 0%Q))%Q).
      change (exp_tail_abs p (Datatypes.S n') c)
        with ((exp_tail_abs p n' c
               + (if Nat.leb p n'
                  then (q_pow c (Datatypes.S n') / q_fact (Datatypes.S n'))%Q
                  else 0%Q))%Q).
      assert (Hm1 : Nat.leb m n' = true) by (apply Nat.leb_le; lia).
      assert (Hp1 : Nat.leb p n' = true) by (apply Nat.leb_le; lia).
      rewrite Hm1, Hp1, IH by lia. ring.
Qed.

Lemma bxcd_qtail_mono : forall (c : Q), Qle 0 c -> forall (k1 k2 n : nat),
  (k1 <= k2)%nat -> (k2 <= n)%nat ->
  Qle (exp_tail_abs k2 n c) (exp_tail_abs k1 n c).
Proof.
  intros c Hc0 k1 k2 n H12 H2n.
  rewrite (bxcd_qtail_add c k1 k2 n H12 H2n).
  assert (Hg : Qle 0 (exp_tail_abs k1 k2 c)) by (apply bxcd_qtail_ge0; exact Hc0).
  assert (Hz : Qle (exp_tail_abs k2 n c + 0%Q)
                   (exp_tail_abs k2 n c + exp_tail_abs k1 k2 c))
    by (apply Qplus_le_compat; [apply Qle_refl | exact Hg]).
  rewrite (Qplus_0_r (exp_tail_abs k2 n c)) in Hz.
  rewrite (Qplus_comm (exp_tail_abs k2 n c) (exp_tail_abs k1 k2 c)) in Hz.
  exact Hz.
Qed.

Lemma bxcd_qsum_plus : forall (f g : nat -> Q) (n : nat),
  ncv_qsum (fun k : nat => (f k + g k)%Q) n == (ncv_qsum f n + ncv_qsum g n)%Q.
Proof.
  intros f g n. induction n as [| m IH].
  - reflexivity.
  - change (ncv_qsum (fun k : nat => (f k + g k)%Q) (Datatypes.S m))
      with ((ncv_qsum (fun k : nat => (f k + g k)%Q) m + (f m + g m)%Q)%Q).
    change (ncv_qsum f (Datatypes.S m)) with ((ncv_qsum f m + f m)%Q).
    change (ncv_qsum g (Datatypes.S m)) with ((ncv_qsum g m + g m)%Q).
    rewrite IH. ring.
Qed.

Lemma bxcd_qsum_scalar_r : forall (f : nat -> Q) (c : Q) (n : nat),
  ncv_qsum (fun k : nat => (f k * c)%Q) n == (ncv_qsum f n * c)%Q.
Proof.
  intros f c n. induction n as [| m IH].
  - reflexivity.
  - change (ncv_qsum (fun k : nat => (f k * c)%Q) (Datatypes.S m))
      with ((ncv_qsum (fun k : nat => (f k * c)%Q) m + (f m * c)%Q)%Q).
    change (ncv_qsum f (Datatypes.S m)) with ((ncv_qsum f m + f m)%Q).
    rewrite IH. ring.
Qed.

Lemma bxcd_qsum_head_shift : forall (c : Q) (k : nat),
  ncv_qsum (fun i : nat => bxcd_A c (Datatypes.S i)) k == exp_tail_abs 0%nat k c.
Proof.
  intros c k. induction k as [| m IH].
  - reflexivity.
  - change (ncv_qsum (fun i : nat => bxcd_A c (Datatypes.S i)) (Datatypes.S m))
      with ((ncv_qsum (fun i : nat => bxcd_A c (Datatypes.S i)) m
             + bxcd_A c (Datatypes.S m))%Q).
    change (exp_tail_abs 0%nat (Datatypes.S m) c)
      with ((exp_tail_abs 0%nat m c
             + (if Nat.leb 0%nat m
                then (q_pow c (Datatypes.S m) / q_fact (Datatypes.S m))%Q
                else 0%Q))%Q).
    assert (Hl : Nat.leb 0%nat m = true) by (destruct m; reflexivity).
    rewrite Hl, IH. reflexivity.
Qed.


Lemma bxcd_padsum_tail : forall (c b0 : Q) (t n : nat),
  ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q)
           (Datatypes.S n)
    == (b0 * exp_tail_abs t n c)%Q.
Proof.
  intros c b0 t n. induction n as [| n' IH].
  - change (ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q)
              (Datatypes.S 0%nat))
      with ((if Nat.ltb t 0%nat then (b0 * bxcd_A c 0%nat)%Q else 0%Q)%Q).
    change (exp_tail_abs t 0%nat c) with 0%Q.
    assert (H0 : Nat.ltb t 0%nat = false) by reflexivity.
    rewrite H0.
    change (if false then (b0 * bxcd_A c 0%nat)%Q else 0%Q) with 0%Q.
    ring.
  - change (ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q)
              (Datatypes.S (Datatypes.S n')))
      with ((ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q)
             (Datatypes.S n')
             + (if Nat.ltb t (Datatypes.S n')
                then (b0 * bxcd_A c (Datatypes.S n'))%Q
                else 0%Q))%Q).
    change (exp_tail_abs t (Datatypes.S n') c)
      with ((exp_tail_abs t n' c
             + (if Nat.leb t n'
                then (q_pow c (Datatypes.S n') / q_fact (Datatypes.S n'))%Q
                else 0%Q))%Q).
    rewrite IH.
    assert (Hg : Nat.ltb t (Datatypes.S n') = Nat.leb t n') by reflexivity.
    rewrite Hg.
    unfold bxcd_A. destruct (Nat.leb t n'); ring.
Qed.

Lemma bxcd_row_le : forall (c b0 : Q) (t n : nat),
  (t <= n)%nat -> Qle 0 b0 -> Qle 0 c ->
  Qle (ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q) n)
      (b0 * exp_tail_abs t n c).
Proof.
  intros c b0 t n Htn Hb0 Hc0.
  assert (Hfn : Qle 0 (if Nat.ltb t n then (b0 * bxcd_A c n)%Q else 0%Q)).
  { destruct (Nat.ltb t n).
    - assert (Hm : Qle (0 * 0)%Q (b0 * bxcd_A c n)%Q)
        by (apply bxcd_Qmult_le_compat_nonneg;
            [exact Hb0 | apply bxcd_A_ge0; exact Hc0 | apply Qle_refl
            | exact Hb0]).
      rewrite Qmult_0_l in Hm. exact Hm.
    - apply Qle_refl. }
  assert (Hstep : Qle (ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q) n)
                      (ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q) (Datatypes.S n))).
  { rewrite <- (Qplus_0_r (ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q) n)).
    apply Qplus_le_compat; [apply Qle_refl | exact Hfn]. }
  eapply Qle_trans. exact Hstep.
  rewrite (bxcd_padsum_tail c b0 t n). apply Qle_refl.
Qed.

Lemma bxcd_U_norm_le : forall (B : BanachAlg) (a : (@BA B)) (c : Q) (n : nat),
  Id c (@bnorm B a) ->
  QleT' (@bnorm B (bxcd_U B a n))
        (ncv_qsum (fun j : nat =>
            ncv_qsum (fun i : nat =>
               if Nat.ltb (Nat.sub n j) i
               then (bxcd_A c j * bxcd_A c i)%Q else 0%Q) (Datatypes.S n))
           (Datatypes.S n)).
Proof.
  intros B a c n Hc. unfold bxcd_U.
  eapply qleT'_trans.
  { apply (bxcd_bsum_norm_le B
              (fun j : nat => bsum B (Datatypes.S n)
                 (fun i : nat =>
                    if Nat.ltb (Nat.sub n j) i
                    then @bmult B (bxcd_F B a j) (bxcd_G B a i)
                    else @bzero B)) n). }
  apply ncv_qsum_le. intros j.
  eapply qleT'_trans.
  { apply (bxcd_bsum_norm_le B
              (fun i : nat =>
                 if Nat.ltb (Nat.sub n j) i
                 then @bmult B (bxcd_F B a j) (bxcd_G B a i)
                 else @bzero B) n). }
  apply ncv_qsum_le. intros i.
  destruct (Nat.ltb (Nat.sub n j) i).
  - exact (Qle_to_QleT' _ _ (bxcd_term_norm B a c Hc j i)).
  - rewrite (@bnorm_zero B). apply qleT'_refl.
Qed.

(* Q2 ≤ E·tail + E·tail（尾和控制主件） *)
Lemma bxcd_Q2_bound : forall (c : Q) (K n : nat) (E : Q),
  Qle 0 c ->
  (forall u : nat, (K <= u)%nat -> Qle ((1 + 1)%Q * c) (Z.of_nat (u + 1) # 1)) ->
  Qle 0 E ->
  Qle (exp_tail_abs 0%nat K c + bxcd_A c K * (1 + 1)%Q) E ->
  (forall m : nat, Qle (ncv_qsum (fun i : nat => bxcd_A c i) m) E) ->
  (2 * K <= n)%nat ->
  Qle (ncv_qsum (fun j : nat =>
          ncv_qsum (fun i : nat =>
             if Nat.ltb (Nat.sub n j) i
             then (bxcd_A c j * bxcd_A c i)%Q else 0%Q) (Datatypes.S n))
         (Datatypes.S n))
      ((E * exp_tail_abs K n c
        + E * exp_tail_abs K n c)%Q).
Proof.
  intros c K n E Hc0 Harch HEpos HE2 HE Hk2.
  assert (Hkn : (K <= n)%nat).
  { pose proof (Nat.div2_odd n) as Hd. destruct (Nat.odd n); cbn [Nat.b2n] in Hd; lia. }
  assert (Hkn2 : (2 * K <= n)%nat).
  { pose proof (Nat.div2_odd n) as Hd. destruct (Nat.odd n); cbn [Nat.b2n] in Hd; lia. }
  apply (Qle_trans _
    (ncv_qsum (fun j : nat =>
        (bxcd_A c j * exp_tail_abs (K) n c
         + (if Nat.ltb (K) j then (E * bxcd_A c j)%Q else 0%Q))%Q)
        (Datatypes.S n))).
  - apply QleT'_to_Qle. apply ncv_qsum_le. intros j. apply Qle_to_QleT'.
    eapply Qle_trans.
    + rewrite (bxcd_padsum_tail c (bxcd_A c j) (Nat.sub n j) n).
      apply Qle_refl.
    + destruct (Nat.ltb (K) j) eqn:Ekj.
      * (* k < j：A_j·tail(n−j) ≤ A_j·tail(0,n) = A_j·(tail0K+tailKn) ≤ A_j·(tailKn+E) = 右端 *)
        assert (Htle : Qle (exp_tail_abs 0%nat K c)
                         (exp_tail_abs K n c + E)%Q).
        { apply (Qle_trans _ (exp_tail_abs 0%nat K c
                             + bxcd_A c K * (1 + 1)%Q)%Q).
          - assert (Haug : Qle (exp_tail_abs 0%nat K c + 0%Q)
                          (exp_tail_abs 0%nat K c + bxcd_A c K * (1 + 1)%Q)%Q)
                  by (apply Qplus_le_compat; [apply Qle_refl
                                             | apply QleT'_to_Qle;
                                               apply (qleT'_mult_compat_r
                                                        0%Q (bxcd_A c K) (1 + 1)%Q);
                                               [apply Qle_to_QleT';
                                                 apply Q2_nonneg
                                               | apply Qle_to_QleT';
                                                 apply bxcd_A_ge0; exact Hc0]]).
            rewrite (Qplus_0_r (exp_tail_abs 0%nat K c)) in Haug.
            exact Haug.
          - apply (Qle_trans _ E).
            ++ exact HE2.
            ++ assert (Hzero : Qle 0 (exp_tail_abs K n c))
                 by (apply bxcd_qtail_ge0; exact Hc0).
               assert (Hr : Qle E (E + exp_tail_abs K n c))
                 by exact (Qle_plus_nonneg_r E (exp_tail_abs K n c) Hzero).
               rewrite (Qplus_comm E (exp_tail_abs K n c)) in Hr.
               exact Hr. }
        eapply (Qle_trans _ (bxcd_A c j * exp_tail_abs 0%nat n c)%Q).
        -- apply (@bxcd_Qmult_le_compat_l
                    (exp_tail_abs (Nat.sub n j) n c)
                    (exp_tail_abs 0%nat n c) (bxcd_A c j)
                    (bxcd_A_ge0 c Hc0 j)
                    (bxcd_qtail_mono c Hc0 0%nat (Nat.sub n j) n
                       (Nat.le_0_l _) ltac:(lia))).
        -- eapply (Qle_trans _ (bxcd_A c j
                   * (exp_tail_abs 0%nat K c + exp_tail_abs K n c))%Q).
           ++ rewrite (bxcd_qtail_add c 0%nat K n (Nat.le_0_l K) ltac:(lia)).
              apply (Qle_refl _).
           ++ assert (HT0 : Qle (exp_tail_abs 0%nat K c) E).
              { apply (Qle_trans _ (exp_tail_abs 0%nat K c
                                   + bxcd_A c K * (1 + 1)%Q)%Q).
                - assert (Hz : Qle (exp_tail_abs 0%nat K c + 0%Q)
                              (exp_tail_abs 0%nat K c
                               + bxcd_A c K * (1 + 1)%Q)%Q).
                  { apply Qplus_le_compat; [apply Qle_refl
                                           | apply QleT'_to_Qle].
                    apply (qleT'_mult_compat_r
                             0%Q (bxcd_A c K) (1 + 1)%Q).
                    ++ apply Qle_to_QleT'. apply Q2_nonneg.
                    ++ apply Qle_to_QleT'. apply bxcd_A_ge0; exact Hc0. }
                  rewrite (Qplus_0_r (exp_tail_abs 0%nat K c)) in Hz.
                  exact Hz.
                - exact HE2. }
              assert (Hsum : Qle (exp_tail_abs 0%nat K c + exp_tail_abs K n c)
                                (exp_tail_abs K n c + E)%Q).
              { apply (Qle_trans _ (E + exp_tail_abs K n c)%Q).
                - apply Qplus_le_compat; [exact HT0 | apply Qle_refl].
                - rewrite (Qplus_comm E (exp_tail_abs K n c)).
                  apply Qle_refl. }
              rewrite (Qmult_comm E (bxcd_A c j)).
              rewrite <- (Qmult_plus_distr_r (bxcd_A c j)
                            (exp_tail_abs K n c) E).
              apply (@bxcd_Qmult_le_compat_l
                       (exp_tail_abs 0%nat K c + exp_tail_abs K n c)%Q
                       (exp_tail_abs K n c + E)%Q (bxcd_A c j)
                       (bxcd_A_ge0 c Hc0 j) Hsum).
      * (* j ≤ k：尾(n−j) ≤ 尾(k) *)
        apply Nat.ltb_ge in Ekj.
        eapply (Qle_trans _ (bxcd_A c j * exp_tail_abs (K) n c)%Q).
        -- apply (bxcd_Qmult_le_compat_l _ _ (bxcd_A c j)).
           ++ apply (bxcd_A_ge0 c Hc0 j).
           ++ apply (bxcd_qtail_mono c Hc0 (K) (Nat.sub n j) n
                       ltac:(lia) ltac:(lia)).
        -- exact (Qle_plus_nonneg_r (bxcd_A c j * exp_tail_abs (K) n c) 0%Q
                    (Qle_refl 0%Q)).
  - assert (Hsplit := bxcd_qsum_plus
               (fun j : nat => bxcd_A c j * exp_tail_abs (K) n c)
               (fun j : nat =>
                  if Nat.ltb (K) j then (E * bxcd_A c j)%Q else 0%Q)
               (Datatypes.S n)).
    rewrite Hsplit.
    apply Qplus_le_compat.
    + rewrite (bxcd_qsum_scalar_r (fun j : nat => bxcd_A c j)
                 (exp_tail_abs (K) n c) (Datatypes.S n)).
      exact (Qmult_le_compat_r
               (ncv_qsum (fun i : nat => bxcd_A c i) (Datatypes.S n)) E
               (exp_tail_abs (K) n c)
               (HE (Datatypes.S n))
               (bxcd_qtail_ge0 c Hc0 (K) n)).
    + rewrite (bxcd_padsum_tail c E (K) n). apply Qle_refl.
Qed.

(* CD12：终局可用 div2 n 尾段形。K 形界（bxcd_Q2_bound）的尾段起点固定于 K，
   不随 n 收缩，终局链（Htl=尾(div2 n,n)<q/D + bxcd_q_div_lt r:=2E<D）数学上
   必须以随 n 收缩的尾段为界。逐行分割于 M=div2 n：
   j≤M 行 mono（n−j≥n−M≥M），j>M 行 qtail_add 拆段后尾(n−j,M)≤尾(0,M)≤E
   （尾(0,M)=尾(0,K)+尾(K,M)≤(E−A_K·2)+A_K·2=HE2）。聚合与 K 形同构。 *)
Lemma bxcd_Q2_bound_M : forall (c : Q) (K n : nat) (E : Q),
  Qle 0 c ->
  (forall u : nat, (K <= u)%nat -> Qle ((1 + 1)%Q * c) (Z.of_nat (u + 1) # 1)) ->
  Qle 0 E ->
  Qle (exp_tail_abs 0%nat K c + bxcd_A c K * (1 + 1)%Q) E ->
  (forall m : nat, Qle (ncv_qsum (fun i : nat => bxcd_A c i) m) E) ->
  (2 * K <= n)%nat ->
  Qle (ncv_qsum (fun j : nat =>
          ncv_qsum (fun i : nat =>
             if Nat.ltb (Nat.sub n j) i
             then (bxcd_A c j * bxcd_A c i)%Q else 0%Q) (Datatypes.S n))
         (Datatypes.S n))
      ((E * exp_tail_abs (Nat.div2 n) n c
        + E * exp_tail_abs (Nat.div2 n) n c)%Q).
Proof.
  intros c K n E Hc0 Harch HEpos HE2 HE Hk2.
  assert (H2M : (2 * Nat.div2 n <= n)%nat).
  { pose proof (Nat.div2_odd n) as Hd. destruct (Nat.odd n); cbn [Nat.b2n] in Hd; lia. }
  assert (HKM : (K <= Nat.div2 n)%nat).
  { pose proof (Nat.div2_odd n) as Hd. destruct (Nat.odd n); cbn [Nat.b2n] in Hd; lia. }
  assert (Hdbound : (n <= 2 * Nat.div2 n + 1)%nat).
  { pose proof (Nat.div2_odd n) as Hd. destruct (Nat.odd n); cbn [Nat.b2n] in Hd; lia. }
  assert (Ht0M : Qle (exp_tail_abs 0%nat (Nat.div2 n) c) E).
  { rewrite (bxcd_qtail_add c 0%nat K (Nat.div2 n) (Nat.le_0_l K) HKM).
    apply (Qle_trans _ (exp_tail_abs 0%nat K c
                       + bxcd_A c K * (1 + 1)%Q)%Q).
    - apply Qplus_le_compat; [apply Qle_refl | ].
      exact (exp_tail_abs_geom2 c K (Nat.div2 n) Hc0 Harch HKM).
    - exact HE2. }
  apply (Qle_trans _
    (ncv_qsum (fun j : nat =>
        (bxcd_A c j * exp_tail_abs (Nat.div2 n) n c
         + (if Nat.ltb (Nat.div2 n) j then (E * bxcd_A c j)%Q else 0%Q))%Q)
        (Datatypes.S n))).
  - apply QleT'_to_Qle. apply ncv_qsum_le. intros j. apply Qle_to_QleT'.
    eapply Qle_trans.
    + rewrite (bxcd_padsum_tail c (bxcd_A c j) (Nat.sub n j) n).
      apply Qle_refl.
    + destruct (Nat.ltb (Nat.div2 n) j) eqn:EMj.
      * (* div2 n < j：尾(n−j,n)=尾(n−j,M)+尾(M,n)，尾(n−j,M)≤尾(0,M)≤E *)
        apply Nat.ltb_lt in EMj.
        assert (HnjM : (Nat.sub n j <= Nat.div2 n)%nat) by lia.
        assert (Ht1 : Qle (exp_tail_abs (Nat.sub n j) (Nat.div2 n) c) E).
        { apply (Qle_trans _ (exp_tail_abs 0%nat (Nat.div2 n) c)).
          - apply (bxcd_qtail_mono c Hc0 0%nat (Nat.sub n j) (Nat.div2 n)
                     (Nat.le_0_l _) HnjM).
          - exact Ht0M. }
        rewrite (bxcd_qtail_add c (Nat.sub n j) (Nat.div2 n) n HnjM
                   ltac:(lia)).
        rewrite (Qmult_plus_distr_r (bxcd_A c j)
                   (exp_tail_abs (Nat.sub n j) (Nat.div2 n) c)
                   (exp_tail_abs (Nat.div2 n) n c)).
        rewrite (Qplus_comm (bxcd_A c j * exp_tail_abs (Nat.sub n j) (Nat.div2 n) c)
                            (bxcd_A c j * exp_tail_abs (Nat.div2 n) n c)).
        apply Qplus_le_compat; [apply Qle_refl | ].
        rewrite (Qmult_comm E (bxcd_A c j)).
        exact (bxcd_Qmult_le_compat_l (exp_tail_abs (Nat.sub n j) (Nat.div2 n) c)
                 E (bxcd_A c j) (bxcd_A_ge0 c Hc0 j) Ht1).
      * (* j ≤ div2 n：尾(n−j,n) ≤ 尾(div2 n,n) *)
        apply Nat.ltb_ge in EMj.
        eapply (Qle_trans _ (bxcd_A c j * exp_tail_abs (Nat.div2 n) n c)%Q).
        -- apply (bxcd_Qmult_le_compat_l _ _ (bxcd_A c j)).
           ++ apply (bxcd_A_ge0 c Hc0 j).
           ++ apply (bxcd_qtail_mono c Hc0 (Nat.div2 n) (Nat.sub n j) n
                       ltac:(lia) ltac:(lia)).
        -- exact (Qle_plus_nonneg_r
                    (bxcd_A c j * exp_tail_abs (Nat.div2 n) n c) 0%Q
                    (Qle_refl 0%Q)).
  - assert (Hsplit := bxcd_qsum_plus
               (fun j : nat => bxcd_A c j * exp_tail_abs (Nat.div2 n) n c)
               (fun j : nat =>
                  if Nat.ltb (Nat.div2 n) j then (E * bxcd_A c j)%Q else 0%Q)
               (Datatypes.S n)).
    rewrite Hsplit.
    apply Qplus_le_compat.
    + rewrite (bxcd_qsum_scalar_r (fun j : nat => bxcd_A c j)
                 (exp_tail_abs (Nat.div2 n) n c) (Datatypes.S n)).
      exact (Qmult_le_compat_r
               (ncv_qsum (fun i : nat => bxcd_A c i) (Datatypes.S n)) E
               (exp_tail_abs (Nat.div2 n) n c)
               (HE (Datatypes.S n))
               (bxcd_qtail_ge0 c Hc0 (Nat.div2 n) n)).
    + rewrite (bxcd_padsum_tail c E (Nat.div2 n) n). apply Qle_refl.
Qed.

(* ============================================================ *)
(* ⑥ 保底件主件：部分和乘积到 1 的 ε-近邻                          *)
(* ============================================================ *)


Lemma bxcd_q_div_lt : forall r D q : Q,
  Qlt 0 q -> Qle 0 r -> Qlt r D -> Qlt 0 D -> Qlt (r * (q * / D)) q.
Proof.
  intros r D q Hq Hr HD' HrD.
  apply (Qlt_le_trans _ (D * (q * / D))%Q).
  - apply (Qmult_lt_compat_r).
    + apply ncv_qmult_lt0.
      * exact Hq.
      * apply Qinv_lt_0_compat. exact HrD.
    + exact HD'.
  - assert (Hdd : (D * (q * / D))%Q == q)
      by (field; apply q_neq_of_lt; exact HrD).
    rewrite Hdd. apply Qle_refl.
Qed.
Theorem bxcd_prod_near_one : forall (B : BanachAlg) (a : (@BA B)),
  forall q : Q, QltT 0 q ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QltT (@bnorm B (@bplus B (@bmult B (exp_series_partial B a n)
                                        (exp_series_partial B (@bopp B a) n))
                              (@bopp B (@bone B)))) q).
Proof.
  intros B a q Hq.
  assert (Hc0 : Qle 0 (@bnorm B a)) by (apply QleT'_to_Qle; apply (@bnorm_pos B a)).
  assert (H01 : Qlt 0 1%Q).
  { pose proof (q_fact_pos 0%nat) as H. change (q_fact 0%nat) with 1%Q in H. exact H. }
  destruct (q_arch_geom (@bnorm B a)) as [K HK].
  assert (Harch : forall u : nat, (K <= u)%nat ->
            Qle ((1 + 1)%Q * (@bnorm B a)) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. apply QleT'_to_Qle. exact (HK u (NatLe_lift K u Hu)). }
  assert (HE2 : Qle (exp_tail_abs 0%nat K (@bnorm B a)
                      + bxcd_A (@bnorm B a) K * (1 + 1)%Q)
                    (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                          + bxcd_A (@bnorm B a) K * (1 + 1)%Q))%Q).
  { apply (Qle_trans _ (0 + (exp_tail_abs 0%nat K (@bnorm B a)
                              + bxcd_A (@bnorm B a) K * (1 + 1)%Q))%Q).
    - rewrite (Qplus_0_l (exp_tail_abs 0%nat K (@bnorm B a)
                            + bxcd_A (@bnorm B a) K * (1 + 1)%Q)).
      apply Qle_refl.
    - apply (@Qplus_le_compat 0%Q 1%Q
                (exp_tail_abs 0%nat K (@bnorm B a)
                 + bxcd_A (@bnorm B a) K * (1 + 1)%Q)%Q
                (exp_tail_abs 0%nat K (@bnorm B a)
                 + bxcd_A (@bnorm B a) K * (1 + 1)%Q)%Q).
      ++ exact (Qlt_le_weak 0%Q 1%Q H01).
      ++ apply Qle_refl. }
  assert (HE : forall m : nat,
           Qle (ncv_qsum (fun i : nat => bxcd_A (@bnorm B a) i) m)
               (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                     + bxcd_A (@bnorm B a) K * (1 + 1)%Q))%Q).
  { intros m. destruct m as [| m'].
    - apply (Qle_trans _ 1%Q).
      + exact (Qlt_le_weak 0%Q 1%Q H01).
      + assert (Hz3 : Qle 0 (exp_tail_abs 0%nat K (@bnorm B a)
                           + bxcd_A (@bnorm B a) K * (1 + 1)%Q)%Q).
        { assert (Hg3 : Qle 0 (bxcd_A (@bnorm B a) K * (1 + 1)%Q)).
          { apply QleT'_to_Qle.
            apply (qleT'_mult_compat_r 0%Q (bxcd_A (@bnorm B a) K) (1 + 1)%Q).
            ++ apply Qle_to_QleT'. apply Q2_nonneg.
            ++ apply Qle_to_QleT'. apply bxcd_A_ge0; exact Hc0. }
          apply (@Qplus_le_compat 0%Q (exp_tail_abs 0%nat K (@bnorm B a))
                    0%Q (bxcd_A (@bnorm B a) K * (1 + 1)%Q)).
          ++ apply bxcd_qtail_ge0; exact Hc0.
          ++ exact Hg3. }
        exact (Qle_plus_nonneg_r 1%Q (exp_tail_abs 0%nat K (@bnorm B a)
                     + bxcd_A (@bnorm B a) K * (1 + 1)%Q)%Q Hz3).
    - assert (Hsplit : ncv_qsum (fun i : nat => bxcd_A (@bnorm B a) i)
                         (Datatypes.S m')
                       == (1 + ncv_qsum (fun i : nat =>
                             bxcd_A (@bnorm B a) (Datatypes.S i)) m')%Q).
      { induction m' as [| m'' IH2].
        - change (ncv_qsum (fun i : nat => bxcd_A (@bnorm B a) i)
                    (Datatypes.S 0%nat))
            with ((ncv_qsum (fun i : nat => bxcd_A (@bnorm B a) i) 0%nat
                   + bxcd_A (@bnorm B a) 0%nat)%Q).
          change (ncv_qsum (fun i : nat => bxcd_A (@bnorm B a) i) 0%nat) with 0%Q.
          unfold bxcd_A. change (q_pow (@bnorm B a) 0%nat) with 1%Q.
          change (q_fact 0%nat) with 1%Q. unfold Qdiv. simpl.
          change (ncv_qsum (fun i : nat =>
                   bxcd_A (@bnorm B a) (Datatypes.S i)) 0%nat) with 0%Q.
          change (1 + ncv_qsum (fun i : nat =>
                   bxcd_A (@bnorm B a) (Datatypes.S i)) 0%nat)%Q with 1%Q.
          reflexivity.
        - change (ncv_qsum (fun i : nat => bxcd_A (@bnorm B a) i)
                    (Datatypes.S (Datatypes.S m'')))
            with ((ncv_qsum (fun i : nat => bxcd_A (@bnorm B a) i)
                    (Datatypes.S m'') + bxcd_A (@bnorm B a) (Datatypes.S m''))%Q).
          change (ncv_qsum (fun i : nat =>
                   bxcd_A (@bnorm B a) (Datatypes.S i))
                   (Datatypes.S m''))%Q
            with (ncv_qsum (fun i : nat =>
                   bxcd_A (@bnorm B a) (Datatypes.S i)) m''
                  + bxcd_A (@bnorm B a) (Datatypes.S m''))%Q.
          rewrite IH2.
          rewrite (Qplus_assoc 1%Q
                     (ncv_qsum (fun i : nat =>
                        bxcd_A (@bnorm B a) (Datatypes.S i)) m'')
                     (bxcd_A (@bnorm B a) (Datatypes.S m''))).
          reflexivity. }
      rewrite Hsplit, bxcd_qsum_head_shift.
      destruct (Nat.leb_spec m' K) as [HmK | HmK].
      + (* case m' <= K : tail(0,m') <= tail(0,K) + A_K*2 via split at m' *)
        apply Qplus_le_compat; [apply Qle_refl | ].
        assert (Hz : Qle 0 (exp_tail_abs m' K (@bnorm B a)
                            + bxcd_A (@bnorm B a) K * (1 + 1)%Q)%Q).
        { apply (@Qplus_le_compat 0%Q (exp_tail_abs m' K (@bnorm B a))
                    0%Q (bxcd_A (@bnorm B a) K * (1 + 1)%Q)).
          ++ apply bxcd_qtail_ge0; exact Hc0.
          ++ apply QleT'_to_Qle.
             apply (qleT'_mult_compat_r 0%Q (bxcd_A (@bnorm B a) K) (1 + 1)%Q).
             ** apply Qle_to_QleT'. apply Q2_nonneg.
             ** apply Qle_to_QleT'. apply bxcd_A_ge0; exact Hc0. }
        rewrite (bxcd_qtail_add (@bnorm B a) 0%nat m' K
                   (Nat.le_0_l m') HmK).
        apply (Qle_trans _
                 (exp_tail_abs 0%nat m' (@bnorm B a)
                  + (exp_tail_abs m' K (@bnorm B a)
                     + bxcd_A (@bnorm B a) K * (1 + 1)%Q))%Q).
        * apply Qle_plus_nonneg_r. exact Hz.
        * rewrite (Qplus_assoc (exp_tail_abs 0%nat m' (@bnorm B a))
                    (exp_tail_abs m' K (@bnorm B a))
                    (bxcd_A (@bnorm B a) K * (1 + 1)%Q)).
          apply Qle_refl.
      + (* case K < m' : tail(0,m') = tail(0,K) + tail(K,m'), geom2 at K *)
        apply Qplus_le_compat; [apply Qle_refl | ].
        rewrite (bxcd_qtail_add (@bnorm B a) 0%nat K m'
                   (Nat.le_0_l K) (Nat.lt_le_incl K m' HmK)).
        apply Qplus_le_compat; [apply Qle_refl
                               | exact (exp_tail_abs_geom2 (@bnorm B a) K m'
                                          Hc0 Harch (Nat.lt_le_incl K m' HmK))]. }
  assert (HE0 : Qle 0 (exp_tail_abs 0%nat K (@bnorm B a)
                       + bxcd_A (@bnorm B a) K * (1 + 1)%Q)%Q).
  { apply (@Qplus_le_compat 0%Q (exp_tail_abs 0%nat K (@bnorm B a))
              0%Q (bxcd_A (@bnorm B a) K * (1 + 1)%Q)).
    ++ apply bxcd_qtail_ge0. exact Hc0.
    ++ exact (q_pow_fact2_nonneg (@bnorm B a) K Hc0). }
  assert (HEpos : Qle 0 (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                              + bxcd_A (@bnorm B a) K * (1 + 1)%Q))%Q).
  { apply (Qle_trans _ 1%Q).
    - exact (Qlt_le_weak 0%Q 1%Q H01).
    - exact (Qle_plus_nonneg_r 1%Q (exp_tail_abs 0%nat K (@bnorm B a)
                     + bxcd_A (@bnorm B a) K * (1 + 1)%Q)%Q HE0). }
  assert (Heq : ((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                        + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                 + (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                         + bxcd_A (@bnorm B a) K * (1 + 1)%Q)))%Q
              == ((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                        + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                  * (1 + 1))%Q) by ring.
  assert (HED : Qlt ((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                            + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                     + (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                             + bxcd_A (@bnorm B a) K * (1 + 1)%Q)))
                    (((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                            + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                      * (1 + 1))%Q + 1)).
  { rewrite Heq.
    pose proof (proj2 (Qplus_lt_r 0%Q 1%Q
                  ((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                          + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                   * (1 + 1))%Q) H01) as Hlt1.
    rewrite (Qplus_0_r ((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                              + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                        * (1 + 1))%Q) in Hlt1.
    exact Hlt1. }
  assert (HD : Qlt 0 (((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                               + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                        * (1 + 1))%Q + 1)).
  { apply (Qlt_le_trans _
             (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                    + bxcd_A (@bnorm B a) K * (1 + 1)%Q))).
    - exact (Qlt_le_trans 0%Q 1%Q
               (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                      + bxcd_A (@bnorm B a) K * (1 + 1)%Q)) H01
               (Qle_plus_nonneg_r 1%Q (exp_tail_abs 0%nat K (@bnorm B a)
                    + bxcd_A (@bnorm B a) K * (1 + 1)%Q)%Q HE0)).
    - rewrite <- Heq.
      apply (Qle_trans _
               ((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                      + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                + (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                        + bxcd_A (@bnorm B a) K * (1 + 1)%Q)))%Q).
      + apply Qle_plus_nonneg_r. exact HEpos.
      + apply Qle_plus_nonneg_r. exact (Qlt_le_weak 0%Q 1%Q H01). }
  assert (Heps : Qlt 0 (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                                 + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                          * (1 + 1))%Q + 1))).
  { apply ncv_qmult_lt0.
    - exact (QltT_to_Qlt 0%Q q Hq).
    - apply Qinv_lt_0_compat. exact HD. }
  destruct (arch_decay (bxcd_A (@bnorm B a) K * (1 + 1)%Q)
              (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                               + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                        * (1 + 1))%Q + 1))
              (Qle_to_QleT' _ _ (q_pow_fact2_nonneg (@bnorm B a) K Hc0))
              (Qlt_to_QltT 0%Q _ Heps)
   ) as [t Hdec].
  exists (2 * (K + Datatypes.S t))%nat.
  intros n HN. apply NatLe_drop in HN.
  pose proof (Nat.div2_odd n) as Hodd.
  assert (HkM : (K + Datatypes.S t <= Nat.div2 n)%nat).
  { destruct (Nat.odd n); cbn [Nat.b2n] in Hodd; lia. }
  assert (Hk2 : (2 * K <= n)%nat) by lia.
  assert (Hlt : Qlt (exp_tail_abs (Nat.div2 n) n (@bnorm B a))
                    (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                                   + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                            * (1 + 1))%Q + 1))).
  { apply (Qle_lt_trans _
             ((q_pow (@bnorm B a) (Nat.div2 n) / q_fact (Nat.div2 n))
              * (1 + 1))%Q).
    - exact (exp_tail_abs_geom2 (@bnorm B a) (Nat.div2 n) n Hc0
               (fun u Hu => Harch u (Nat.le_trans K (Nat.div2 n) u
                          (Nat.le_trans K (K + Datatypes.S t) (Nat.div2 n)
                             (Nat.le_add_r K (Datatypes.S t)) HkM) Hu))
               ltac:(pose proof (Nat.div2_odd n) as Hd;
                     destruct (Nat.odd n); cbn [Nat.b2n] in Hd; lia)).
    - exact (exp_tail_arch (@bnorm B a) K t (Nat.div2 n)
               (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                                + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                         * (1 + 1))%Q + 1))
               Hc0 Harch Heps (QltT_to_Qlt _ _ Hdec) HkM). }
  pose proof (bxcd_Q2_bound_M (@bnorm B a) K n
                (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                      + bxcd_A (@bnorm B a) K * (1 + 1)%Q))%Q
                Hc0 Harch HEpos HE2 HE Hk2) as HQ2.
  pose proof (bxcd_prod_split B a n) as Hsplit.
  pose proof (bxcd_prod_close B a n (bxcd_U B a n) Hsplit) as Hclose.
  eapply (QeqT_Qlt_bool_cong _ _ _ (qeqT_sym_hw _ _ Hclose)).
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _
           (ncv_qsum (fun j : nat =>
               ncv_qsum (fun i : nat =>
                  if Nat.ltb (Nat.sub n j) i
                  then (bxcd_A (@bnorm B a) j * bxcd_A (@bnorm B a) i)%Q
                  else 0%Q) (Datatypes.S n)) (Datatypes.S n)) q).
  - exact (QleT'_to_Qle _ _ (bxcd_U_norm_le B a (@bnorm B a) n id_refl)).
  - assert (Htl : Qle (exp_tail_abs (Nat.div2 n) n (@bnorm B a))
                      (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                                       + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                                * (1 + 1))%Q + 1)))
      by (apply Qlt_le_weak; exact Hlt).
    eapply Qle_lt_trans.
    + exact HQ2.
    + eapply Qle_lt_trans.
      * apply Qplus_le_compat.
        -- exact (bxcd_Qmult_le_compat_l
                    (exp_tail_abs (Nat.div2 n) n (@bnorm B a))
                    (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                                     + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                             * (1 + 1))%Q + 1))
                    (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                          + bxcd_A (@bnorm B a) K * (1 + 1)%Q))%Q
                    HEpos Htl).
        -- exact (bxcd_Qmult_le_compat_l
                    (exp_tail_abs (Nat.div2 n) n (@bnorm B a))
                    (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                                     + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                             * (1 + 1))%Q + 1))
                    (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                          + bxcd_A (@bnorm B a) K * (1 + 1)%Q))%Q
                    HEpos Htl).
      * assert (Hgen : forall u1 v1 : Q,
                     (u1 * v1 + u1 * v1)%Q == ((u1 + u1) * v1)%Q)
            by (intros u1 v1; ring).
        rewrite (Hgen (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                                + bxcd_A (@bnorm B a) K * (1 + 1)%Q))%Q
                      (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                                       + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                                * (1 + 1))%Q + 1))).
        exact (bxcd_q_div_lt
                 ((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                        + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                  + (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                          + bxcd_A (@bnorm B a) K * (1 + 1)%Q)))
                 (((1 + (exp_tail_abs 0%nat K (@bnorm B a)
                         + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                   * (1 + 1))%Q + 1) q
                 (QltT_to_Qlt 0%Q q Hq)
                 (Qplus_le_compat 0%Q (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                                         + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                                  0%Q (1 + (exp_tail_abs 0%nat K (@bnorm B a)
                                         + bxcd_A (@bnorm B a) K * (1 + 1)%Q))
                                  HEpos HEpos)
                 HED HD).
Qed.

(* ---- ToyR 追印：清单件假设面逐件打印，判读全闭 ---- *)
Print Assumptions bxcd_bsum_snoc.
