(* ==========================================================================)
   SqrtfCauchyArch.v — 二幂半幂族与 Archimedean 衰减
   使命: sfcy_pow2/sfcy_pow_half（2^k 与 2^(−k/2) 族）、sfcy_pow_half_inv_pow2（互逆恒等）、sfcy_const_* 有理常值嵌入桥与 sfcy_arch_decay_real/sfcy_arch_decay_slot（∀ c ε>0 ∃k，c·2^(−k/2) < ε）。
   依赖: CW_ConstructiveWorld_219、S01_BaseRing、S02_CauchyComplete、S03_QExp、S07_RealSetoidExpLog、UpReqAlgebra等；Stdlib Extraction、QArith、ZArith、Lia
   对标: Archimedean 性质的定量形（几何衰减尾项）与 2 的平方根半幂构造。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。存在性命题以 sigT 见证形给出。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
From Stdlib Require Import QArith ZArith Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import UpReqAlgebra.
Require Import SqrtfCauchy.
Import RealInterfaceEnhancedMod.

(* ============ §0 nat 面：2^n 与 n < 2^n ============ *)

Fixpoint sfcy_npow2 (n : nat) : nat :=
  match n with
  | Datatypes.O => Datatypes.S Datatypes.O
  | Datatypes.S n' => 2 * sfcy_npow2 n'
  end.

Lemma sfcy_nat_lt_npow2 : forall n : nat,
  (n < sfcy_npow2 n)%nat /\ (1 <= sfcy_npow2 n)%nat.
Proof.
  induction n as [| n IH].
  - simpl. lia.
  - destruct IH as [IH1 IH2]. simpl. lia.
Qed.

(* ============ §1 two/half 面（与宿主 sfc_pow_half 配对同形） ============ *)
(* sfcy_two 与 sfc_half 的 ι 展开面（real_plus real_one real_one +      *)
(* req_two_pos）syntactic 同形，half 配对走 conversion。                 *)

Definition sfcy_two : Real := real_plus real_one real_one.

Definition sfcy_two_pos : real_lt real_zero sfcy_two :=
  @plus_positive Real RealEnhancedReal real_one real_one
    (@one_pos Real RealEnhancedReal) (@one_pos Real RealEnhancedReal).

Definition sfcy_half : Real :=
  real_inv_pos sfcy_two (@req_two_pos Real RealEnhancedReal).

Lemma sfcy_half_pos : real_lt real_zero sfcy_half.
Proof.
  exact (real_inv_pos_pos sfcy_two  (@req_two_pos Real RealEnhancedReal)).
Qed.

Lemma sfcy_pow_half_pos : forall k : nat,
  real_lt real_zero (sfc_pow_half k).
Proof.
  induction k as [| k IH].
  - exact (@one_pos Real RealEnhancedReal).
  - exact (@mult_positive Real RealEnhancedReal _ sfcy_half IH sfcy_half_pos).
Qed.

(* ============ §2 const 桥接引理（real_arch 输出面 ⟷ 接口代数面） ============ *)

Lemma sfcy_const_one : real_eq (real_const (1 # 1)) real_one.
Proof.
  apply real_eq_of_zero_diff. intro n.
  rewrite real_const_proj. unfold real_one. cbn [projT1]. ring.
Qed.

Lemma sfcy_const_two : real_eq (real_const (2 # 1)) sfcy_two.
Proof.
  apply real_eq_of_zero_diff. intro n.
  rewrite real_const_proj. unfold sfcy_two.
  rewrite real_plus_proj.
  unfold real_one. cbn [projT1]. ring.
Qed.

Lemma sfcy_const_wd : forall a b : Q, Qeq a b ->
  real_eq (real_const a) (real_const b).
Proof.
  intros a b H. apply real_eq_of_zero_diff. intro n.
  rewrite real_const_proj, real_const_proj. rewrite H. ring.
Qed.

Lemma sfcy_const_mult : forall a b : Q,
  real_eq (real_mult (real_const a) (real_const b)) (real_const (a * b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  rewrite real_mult_proj, real_const_proj, real_const_proj, real_const_proj.
  ring.
Qed.

Lemma sfcy_qlt_z1 : forall z w : Z, (z < w)%Z -> Qlt (z # 1) (w # 1).
Proof.
  intros z w H. unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

(* ============ §3 接口 two 幂族与归拢件（构造④） ============ *)

Fixpoint sfcy_pow2 (k : nat) : Real :=
  match k with
  | Datatypes.O => real_one
  | Datatypes.S k' => real_mult (sfcy_pow2 k') sfcy_two
  end.

Lemma sfcy_pow2_pos : forall k : nat, real_lt real_zero (sfcy_pow2 k).
Proof.
  induction k as [| k IH].
  - exact (@one_pos Real RealEnhancedReal).
  - exact (@mult_positive Real RealEnhancedReal _ sfcy_two IH sfcy_two_pos).
Qed.

(* 逆恒等：pow_half k · 2^k == one（req 面，归纳 + inv_pos_correct） *)
Lemma sfcy_pow_half_inv_pow2 : forall k : nat,
  real_eq (real_mult (sfc_pow_half k) (sfcy_pow2 k)) real_one.
Proof.
  induction k as [| k IH].
  - exact (@mult_one Real RealEnhancedReal real_one).
  - (* (X·h)·(Y·t) ≡ X·(h·(t·Y)) ≡ X·((h·t)·Y) ≡ X·(one·Y) ≡ X·Y ≡ one *)
    assert (HT : real_eq (real_mult sfcy_half sfcy_two) real_one).
    { exact (real_eq_trans _ _ _
               (@mult_comm Real RealEnhancedReal sfcy_half sfcy_two)
               (real_inv_pos_correct sfcy_two
                  (@req_two_pos Real RealEnhancedReal))). }
    assert (H1 : real_eq
              (real_mult (real_mult (sfc_pow_half k) sfcy_half)
                         (real_mult (sfcy_pow2 k) sfcy_two))
              (real_mult (sfc_pow_half k)
                         (real_mult sfcy_half
                                    (real_mult (sfcy_pow2 k) sfcy_two)))).
    { apply (@req_sym Real RealEnhancedReal _).
      exact (@mult_assoc Real RealEnhancedReal (sfc_pow_half k) sfcy_half
               (real_mult (sfcy_pow2 k) sfcy_two)). }
    assert (H2 : real_eq
              (real_mult sfcy_half (real_mult (sfcy_pow2 k) sfcy_two))
              (real_mult (real_mult sfcy_half sfcy_two) (sfcy_pow2 k))).
    { apply (@req_trans Real RealEnhancedReal _
                (real_mult sfcy_half
                           (real_mult sfcy_two (sfcy_pow2 k)))).
      - apply (@req_mult_compat Real RealEnhancedReal sfcy_half sfcy_half
                  (real_mult (sfcy_pow2 k) sfcy_two)
                  (real_mult sfcy_two (sfcy_pow2 k))).
        + exact (real_eq_refl sfcy_half).
        + exact (@mult_comm Real RealEnhancedReal (sfcy_pow2 k) sfcy_two).
      - exact (@mult_assoc Real RealEnhancedReal sfcy_half sfcy_two
                 (sfcy_pow2 k)). }
    assert (H3 : real_eq
              (real_mult (sfc_pow_half k)
                         (real_mult sfcy_half
                                    (real_mult (sfcy_pow2 k) sfcy_two)))
              (real_mult (sfc_pow_half k)
                         (real_mult (real_mult sfcy_half sfcy_two)
                                    (sfcy_pow2 k)))).
    { exact (@req_mult_compat Real RealEnhancedReal (sfc_pow_half k)
                (sfc_pow_half k)
                (real_mult sfcy_half (real_mult (sfcy_pow2 k) sfcy_two))
                (real_mult (real_mult sfcy_half sfcy_two) (sfcy_pow2 k))
                (real_eq_refl (sfc_pow_half k)) H2). }
    assert (H4 : real_eq
              (real_mult (sfc_pow_half k)
                         (real_mult (real_mult sfcy_half sfcy_two)
                                    (sfcy_pow2 k)))
              (real_mult (sfc_pow_half k)
                         (real_mult real_one (sfcy_pow2 k)))).
    { exact (@req_mult_compat Real RealEnhancedReal (sfc_pow_half k)
                (sfc_pow_half k)
                (real_mult (real_mult sfcy_half sfcy_two) (sfcy_pow2 k))
                (real_mult real_one (sfcy_pow2 k))
                (real_eq_refl (sfc_pow_half k))
                (@req_mult_compat Real RealEnhancedReal
                   (real_mult sfcy_half sfcy_two) real_one
                   (sfcy_pow2 k) (sfcy_pow2 k)
                   HT (real_eq_refl (sfcy_pow2 k)))). }
    assert (H5 : real_eq
              (real_mult (sfc_pow_half k)
                         (real_mult real_one (sfcy_pow2 k)))
              (real_mult (sfc_pow_half k) (sfcy_pow2 k))).
    { apply (@req_mult_compat Real RealEnhancedReal (sfc_pow_half k)
                (sfc_pow_half k) (real_mult real_one (sfcy_pow2 k))
                (sfcy_pow2 k)).
      - exact (real_eq_refl (sfc_pow_half k)).
      - exact (real_eq_trans _ _ _
                  (@mult_comm Real RealEnhancedReal real_one (sfcy_pow2 k))
                  (@mult_one Real RealEnhancedReal (sfcy_pow2 k))). }
    exact (real_eq_trans _ _ _
             (real_eq_trans _ _ _ H1 (real_eq_trans _ _ _ H3 H4))
             (real_eq_trans _ _ _ H5 IH)).
Qed.

(* 2^k 的 const 形：2^k == const (Z.of_nat (2^k) # 1)（归纳 + const 乘法同态） *)
Lemma sfcy_pow2_const : forall k : nat,
  real_eq (sfcy_pow2 k)
          (real_const (Z.of_nat (sfcy_npow2 k) # 1)).
Proof.
  induction k as [| k IH].
  - exact (real_eq_sym _ _ sfcy_const_one).
  - assert (Heq : sfcy_npow2 (Datatypes.S k) = (2 * sfcy_npow2 k)%nat)
      by reflexivity.
    rewrite Heq.
    apply (@req_trans Real RealEnhancedReal
              (real_mult (sfcy_pow2 k) sfcy_two)
              (real_mult (real_const (Z.of_nat (sfcy_npow2 k) # 1))
                         (real_const (2 # 1)))
              (real_const (Z.of_nat (2 * sfcy_npow2 k) # 1))).
    + apply (@req_mult_compat Real RealEnhancedReal (sfcy_pow2 k)
                (real_const (Z.of_nat (sfcy_npow2 k) # 1)) sfcy_two
                (real_const (2 # 1))).
      * exact IH.
      * exact (real_eq_sym _ _ sfcy_const_two).
    + (* B→C：const 乘法同态 + const 内 Qeq 换头（二段 trans 复合肢） *)
      assert (Hq : Qeq ((Z.of_nat (sfcy_npow2 k) # 1) * (2 # 1))
                       (Z.of_nat (2 * sfcy_npow2 k) # 1)).
      { unfold Qeq. cbn [Qnum Qden Qmult].
        rewrite Nat2Z.inj_mul.
        change (Z.of_nat 2) with 2%Z.
        change (Z.pos (1 * 1)) with 1%Z.
        ring. }
      exact (real_eq_trans _ _ _
               (sfcy_const_mult (Z.of_nat (sfcy_npow2 k) # 1) (2 # 1))
               (sfcy_const_wd _ _ Hq)).
Qed.

(* const n < 2^n（real_const_lt 严格 + Qlt nat→Z→Q 桥 + req 换头） *)
Lemma sfcy_const_lt_pow2 : forall n : nat, (1 <= n)%nat ->
  real_lt (real_const (Z.of_nat n # 1)) (sfcy_pow2 n).
Proof.
  intros n Hn.
  assert (Hlt : (Z.of_nat n < Z.of_nat (sfcy_npow2 n))%Z).
  { apply Nat2Z.inj_lt. exact (proj1 (sfcy_nat_lt_npow2 n)). }
  apply (@req_lt_compat Real RealEnhancedReal
            (real_const (Z.of_nat n # 1)) (real_const (Z.of_nat n # 1))
            (real_const (Z.of_nat (sfcy_npow2 n) # 1)) (sfcy_pow2 n)).
  - exact (real_eq_refl (real_const (Z.of_nat n # 1))).
  - exact (real_eq_sym _ _ (sfcy_pow2_const n)).
  - exact (real_const_lt _ _ (sfcy_qlt_z1 _ _ Hlt)).
Qed.

(* ============ §4 假设位3 主件（素颜面）+ 显式应用桥（构造①②⑤） ============ *)

Theorem sfcy_arch_decay_real : forall c eps : Real,
  real_le real_zero c -> real_lt real_zero eps ->
  sigT (fun k : nat =>
    real_lt (real_mult c (sfc_pow_half k)) eps).
Proof.
  intros c eps Hle Heps.
  unfold real_le in Hle.
  destruct Hle as [Hclt | Heq].
  - (* lt 支：real_arch 施于 B := c·inv(eps)（构造②） *)
    destruct (real_arch (real_mult c (real_inv_pos eps Heps)))
      as [n [Hn2 Hn]].
    assert (Hn1 : (1 <= n)%nat) by lia.
    exists n.
    (* ① const n < 2^n，与 real_arch 输出传输到 2^n 面（构造③④） *)
    assert (Harch : real_lt (real_mult c (real_inv_pos eps Heps))
                            (sfcy_pow2 n)).
    { exact (@lt_trans Real RealEnhancedReal
              (real_mult c (real_inv_pos eps Heps))
              (real_const (Z.of_nat n # 1)) (sfcy_pow2 n)
              Hn (sfcy_const_lt_pow2 n Hn1)). }
    (* ② 乘正 half^n：lt_mult_compat 完成（构造⑤） *)
    assert (HA : real_lt
              (real_mult (real_mult c (real_inv_pos eps Heps))
                         (sfc_pow_half n))
              (real_mult (sfcy_pow2 n) (sfc_pow_half n))).
    { exact (@lt_mult_compat Real RealEnhancedReal
                (real_mult c (real_inv_pos eps Heps)) (sfcy_pow2 n)
                (sfc_pow_half n) (sfcy_pow_half_pos n) Harch). }
    assert (HB : real_eq (real_mult (sfcy_pow2 n) (sfc_pow_half n)) real_one).
    { exact (real_eq_trans _ _ _
              (@mult_comm Real RealEnhancedReal (sfcy_pow2 n)
                          (sfc_pow_half n))
              (sfcy_pow_half_inv_pow2 n)). }
    assert (HC : real_lt
              (real_mult (real_mult c (real_inv_pos eps Heps))
                         (sfc_pow_half n)) real_one).
    { exact (@req_lt_compat Real RealEnhancedReal
                (real_mult (real_mult c (real_inv_pos eps Heps))
                           (sfc_pow_half n))
                (real_mult (real_mult c (real_inv_pos eps Heps))
                           (sfc_pow_half n))
                (real_mult (sfcy_pow2 n) (sfc_pow_half n)) real_one
                (real_eq_refl _)
                HB HA). }
    (* ③ 再乘正 eps，req 重排收 c·half^n < eps *)
    assert (HD : real_lt
              (real_mult (real_mult (real_mult c (real_inv_pos eps Heps))
                                    (sfc_pow_half n)) eps)
              (real_mult real_one eps)).
    { exact (@lt_mult_compat Real RealEnhancedReal
                (real_mult (real_mult c (real_inv_pos eps Heps))
                           (sfc_pow_half n)) real_one eps Heps HC). }
    (* req 换头：((c·E)·B)·eps ≡ (c·E)·(B·eps) ≡ c·(E·(B·eps))
       ≡ c·(E·(eps·B)) ≡ c·((E·eps)·B) ≡ c·(B·(E·eps)) ≡ (c·B)·(E·eps) *)
    assert (Hswap : real_eq
              (real_mult (real_mult (real_mult c (real_inv_pos eps Heps))
                                    (sfc_pow_half n)) eps)
              (real_mult (real_mult c (sfc_pow_half n))
                         (real_mult (real_inv_pos eps Heps) eps))).
    { assert (Hs1 : real_eq
                (real_mult (real_mult (real_mult c (real_inv_pos eps Heps))
                                      (sfc_pow_half n)) eps)
                (real_mult (real_mult c (real_inv_pos eps Heps))
                           (real_mult (sfc_pow_half n) eps))).
      { apply (@req_sym Real RealEnhancedReal _).
        exact (@mult_assoc Real RealEnhancedReal
                 (real_mult c (real_inv_pos eps Heps)) (sfc_pow_half n) eps). }
      assert (Hs2 : real_eq
                (real_mult (real_mult c (real_inv_pos eps Heps))
                           (real_mult (sfc_pow_half n) eps))
                (real_mult c
                           (real_mult (real_inv_pos eps Heps)
                                      (real_mult (sfc_pow_half n) eps)))).
      { apply (@req_sym Real RealEnhancedReal _).
        exact (@mult_assoc Real RealEnhancedReal c (real_inv_pos eps Heps)
                 (real_mult (sfc_pow_half n) eps)). }
      assert (Hs3 : real_eq
                (real_mult c
                           (real_mult (real_inv_pos eps Heps)
                                      (real_mult (sfc_pow_half n) eps)))
                (real_mult c
                           (real_mult (real_inv_pos eps Heps)
                                      (real_mult eps (sfc_pow_half n))))).
      { apply (@req_mult_compat Real RealEnhancedReal c c _ _
                  (real_eq_refl c)).
        exact (@req_mult_compat Real RealEnhancedReal
                   (real_inv_pos eps Heps) (real_inv_pos eps Heps)
                   (real_mult (sfc_pow_half n) eps)
                   (real_mult eps (sfc_pow_half n))
                   (real_eq_refl (real_inv_pos eps Heps))
                   (@mult_comm Real RealEnhancedReal
                      (sfc_pow_half n) eps)). }
      assert (Hs4 : real_eq
                (real_mult c
                           (real_mult (real_inv_pos eps Heps)
                                      (real_mult eps (sfc_pow_half n))))
                (real_mult c
                           (real_mult (real_mult (real_inv_pos eps Heps) eps)
                                      (sfc_pow_half n)))).
      { apply (@req_mult_compat Real RealEnhancedReal c c _ _
                  (real_eq_refl c)).
        exact (@mult_assoc Real RealEnhancedReal (real_inv_pos eps Heps) eps
                 (sfc_pow_half n)). }
      assert (Hs5 : real_eq
                (real_mult c
                           (real_mult (real_mult (real_inv_pos eps Heps) eps)
                                      (sfc_pow_half n)))
                (real_mult c
                           (real_mult (sfc_pow_half n)
                                      (real_mult (real_inv_pos eps Heps)
                                                 eps)))).
      { apply (@req_mult_compat Real RealEnhancedReal c c _ _
                  (real_eq_refl c)).
        exact (@mult_comm Real RealEnhancedReal
                 (real_mult (real_inv_pos eps Heps) eps) (sfc_pow_half n)). }
      assert (Hs6 : real_eq
                (real_mult c
                           (real_mult (sfc_pow_half n)
                                      (real_mult (real_inv_pos eps Heps)
                                                 eps)))
                (real_mult (real_mult c (sfc_pow_half n))
                           (real_mult (real_inv_pos eps Heps) eps))).
      { exact (@mult_assoc Real RealEnhancedReal c (sfc_pow_half n)
                 (real_mult (real_inv_pos eps Heps) eps)). }
      exact (real_eq_trans _ _ _ Hs1
               (real_eq_trans _ _ _ Hs2
                  (real_eq_trans _ _ _ Hs3
                     (real_eq_trans _ _ _ Hs4
                        (real_eq_trans _ _ _ Hs5 Hs6))))). }
    assert (Hrhs : real_eq (real_mult real_one eps) eps).
    { apply (@req_trans Real RealEnhancedReal
                (real_mult real_one eps) (real_mult eps real_one) eps).
      - exact (@mult_comm Real RealEnhancedReal real_one eps).
      - exact (@mult_one Real RealEnhancedReal eps). }
    exact (@req_lt_compat Real RealEnhancedReal
              (real_mult (real_mult (real_mult c (real_inv_pos eps Heps))
                                    (sfc_pow_half n)) eps)
              (real_mult c (sfc_pow_half n))
              (real_mult real_one eps) eps
              (real_eq_trans _ _ _ Hswap
                 (real_eq_trans _ _ _
                    (@req_mult_compat Real RealEnhancedReal
                       (real_mult c (sfc_pow_half n))
                       (real_mult c (sfc_pow_half n))
                       (real_mult (real_inv_pos eps Heps) eps) real_one
                       (real_eq_refl (real_mult c (sfc_pow_half n)))
                       (real_eq_trans _ _ _
                          (@mult_comm Real RealEnhancedReal
                             (real_inv_pos eps Heps) eps)
                          (@inv_pos_correct Real RealEnhancedReal eps Heps)))
                    (@mult_one Real RealEnhancedReal
                       (real_mult c (sfc_pow_half n)))))
              Hrhs HD).
  - (* eq 支：c == 0，k := 0。mult_one + Heq 得 req zero (c·one)，
       lt zero eps 经 req_lt_compat 传输收 lt (c·one) eps *)
    exists Datatypes.O.
    exact (@req_lt_compat Real RealEnhancedReal
              real_zero (real_mult c real_one) eps eps
          (real_eq_sym _ _
             (real_eq_trans _ _ _
                (@mult_one Real RealEnhancedReal c)
                (real_eq_sym _ _ Heq)))
              (real_eq_refl eps) Heps).
Qed.

(* 假设位3 显式应用桥（宿主假设位语句逐字，接口投影面；依存位 SqrtfCauchy.v:1070）
   ——素颜面到接口面只走实例 delta/iota，exact 一行（与 sfcx_*_slot 同式）。
   接入：sfc_arch_decay 参位 ← 本件。 *)
Theorem sfcy_arch_decay_slot :
  forall c eps : Real,
  @le Real RealEnhancedReal (@zero Real RealEnhancedReal) c ->
  @lt Real RealEnhancedReal (@zero Real RealEnhancedReal) eps ->
  sigT (fun k : nat =>
    @lt Real RealEnhancedReal
        (@mult Real RealEnhancedReal c (sfc_pow_half k)) eps).
Proof. exact sfcy_arch_decay_real. Qed.

(* ============ 四关自证面：G3 提取检验 + G4 假设审计口 ============ *)
(* 两主件证明体全走 real_* 素颜顶层函数链与接口投影 δ 面预判            *)
(* Obj.magic = 0（与 sfcx_G3 同判据）。                              *)

Extraction "sfcy_G3.ml" sfcy_arch_decay_real.

Print Assumptions sfcy_arch_decay_real.
Print Assumptions sfcy_arch_decay_slot.
