(* ==========================================================================)
   KLWallClosed.v — KL 墙闭端：零退化分支的幂单调闭合
   使命: klc_closed_powb_mono（Real 载体全域版 (1−η)^{t1} ≤_B (1−η)^t）、klc_strict_branch/one_branch（Q 载体两支）、klc_closed_Q（可判定分裂 × 统一收缩 × 分支附加证书 sigT 组装）、弱前提引擎件（klc_powb_mono_weak/le_mult_r_weak）。
   依赖: CW_ConstructiveWorld_219、UpRealLeB/2、G07_KLWall；Stdlib PeanoNat、QArith.Qring、Lia、Extraction。
   对标: 几何收缩率 η=1 端的零退化分支处理（Pinsker 型证明的闭端修补）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import G07_KLWall.

(* ============================================================ *)
(* Part A：Q 层换形三件（闭端两支的可判定分裂燃料）                  *)
(* ============================================================ *)

(* η < 1（QltT）⟹ 0 < 1−η（QltT）——严格支正性证书的 Q 层源 *)
Lemma klc_q_lt_zero_minus : forall eta : Q,
  QltT eta (1#1) -> QltT (0#1) (1 - eta)%Q.
Proof.
  intros eta H. apply Qlt_to_QltT.
  apply (proj1 (Qlt_minus_iff eta (1#1))).
  apply QltT_to_Qlt. exact H.
Qed.

(* η ≤ 1（QleT'）⟹ 0 ≤ 1−η（QleT'）：Qopp 反向 + 左平移 + ring 换形 *)
Lemma klc_q_bound_lower : forall eta : Q,
  QleT' eta (1#1) -> QleT' (0#1) (1 - eta)%Q.
Proof.
  intros eta H. apply Qle_to_QleT'.
  assert (H1 : Qle eta (1#1)) by (apply QleT'_to_Qle; exact H).
  pose proof (Qopp_le_compat eta (1#1) H1) as Ho.
  (* 9.1 适配：stdlib 名 Qplus_le_compat_l 并入 Qplus_le_compat（x<=y -> z<=t -> x+z<=y+t），右因子取自反；
     结论形状经 ring 换形对齐目标（Q 载体 Z 层不可互逆的参数序差） *)
  pose proof (Qplus_le_compat (Qopp (1#1)) (Qopp eta) (1#1) (1#1) Ho (Qle_refl (1#1))) as Hp.
  assert (E0 : (Qplus (Qopp (1#1)) (1#1))%Q == (0#1)) by ring.
  assert (E0b : (Qplus (Qopp eta) (1#1))%Q == (Qplus (1#1) (Qopp eta))%Q) by ring.
  rewrite E0, E0b in Hp. exact Hp.
Qed.

(* 0 ≤ η（QleT'）⟹ 1−η ≤ 1（QleT'）：Qopp 反向 + 左平移 + ring 换形 *)
Lemma klc_q_bound_upper : forall eta : Q,
  QleT' (0#1) eta -> QleT' (1 - eta)%Q (1#1).
Proof.
  intros eta H. apply Qle_to_QleT'.
  assert (H0 : Qle (0#1) eta) by (apply QleT'_to_Qle; exact H).
  pose proof (Qopp_le_compat (0#1) eta H0) as Ho.
  assert (Ez : (Qopp (0#1))%Q == (0#1)) by ring.
  rewrite Ez in Ho.
  pose proof (Qplus_le_compat (1#1) (1#1) (Qopp eta) (0#1) (Qle_refl (1#1)) Ho) as Hp.
  assert (E1 : (Qplus (1#1) (0#1))%Q == (1#1)) by ring.
  rewrite E1 in Hp.
  exact Hp.
Qed.

(* ============================================================ *)
(* Part B：real_const 序桥三件（Q 载体收缩率进 Real 层的桥）          *)
(* ============================================================ *)

Lemma klc_const_eq : forall c d : Q,
  QeqT c d -> real_eq (real_const c) (real_const d).
Proof.
  intros c d H. unfold QeqT in H.
  destruct (Qcompare c d) eqn:E; try rewrite E in H; simpl in H.
  - (* Eq 支：Qeq_alt 反映后逐点常值差归零 *)
    apply real_eq_of_zero_diff. intro n.
    rewrite (real_const_proj c n), (real_const_proj d n).
    rewrite (proj2 (Qeq_alt c d) E). ring.
  - inversion H.
  - inversion H.
Qed.

(* QleT' 序沿 real_const 保序至 real_le（Or(lt,eq) 逐支装配） *)
Lemma klc_const_le : forall c d : Q,
  QleT' c d -> real_le (real_const c) (real_const d).
Proof.
  intros c d H. unfold QleT', Qle_bool in H.
  destruct (Qcompare c d) eqn:E; try rewrite E in H; simpl in H.
  - (* Eq 支：real_const 等式换形 *)
    assert (HQ : QeqT c d) by (unfold QeqT; rewrite E; exact H).
    exact (inr (klc_const_eq c d HQ)).
  - (* Lt 支：real_const_lt 严格序直通 *)
    assert (HL : Qlt c d) by (apply Qlt_alt; exact E).
    exact (inl (real_const_lt c d HL)).
  - (* Gt 被 QleT' 反映证伪 *)
    destruct (id_false_true H).
Qed.

(* 闭端可判定分裂引擎件：Qcompare 三分 ⟹ 严格支 / 零退化支 二选一。
   第二支取 QeqT（bool 反映形）——S02 QleT 的 Id 支对变元 η 构造性不可得，
   消融注释同款判定，故本件是 QleT 的可构造精化。 *)
Lemma klc_split_one : forall eta : Q,
  QleT' eta (1#1) -> sum (QltT eta (1#1)) (QeqT eta (1#1)).
Proof.
  intros eta H. unfold QleT', Qle_bool in H.
  destruct (Qcompare eta (1#1)) eqn:E; try rewrite E in H; simpl in H.
  - (* Eq 支：零退化支（bool 反映形） *)
    assert (HQ : QeqT eta (1#1)) by (unfold QeqT; rewrite E; exact H).
    exact (inr HQ).
  - (* Lt 支：严格收缩支 *)
    assert (HL : QltT eta (1#1)) by (unfold QltT, Qlt_bool; rewrite E; exact H).
    exact (inl HL).
  - (* Gt 被 QleT' 反映证伪 *)
    destruct (id_false_true H).
Qed.

(* ============================================================ *)
(* Part C：Real 层弱序代数（0≤η≤1 弱前提的闭端核心；零三分律使用）     *)
(* ============================================================ *)

Lemma klc_le_refl : forall x : Real, real_le x x.
Proof. intros x. exact (inr (real_eq_refl x)). Qed.

Lemma klc_le_id_l : forall a b c : Real,
  real_eq a b -> real_le b c -> real_le a c.
Proof.
  intros a b c Hab Hbc. unfold real_le in Hbc. destruct Hbc as [Hlt | Heq].
  - exact (inl (real_eq_lt_lt a b c Hab Hlt)).
  - exact (inr (real_eq_trans a b c Hab Heq)).
Qed.

Lemma klc_le_id_r : forall a b c : Real,
  real_eq b c -> real_le a b -> real_le a c.
Proof.
  intros a b c Hbc Hab. unfold real_le in Hab. destruct Hab as [Hlt | Heq].
  - exact (inl (real_lt_eq_lt a b c Hlt Hbc)).
  - exact (inr (real_eq_trans a b c Heq Hbc)).
Qed.

(* 弱乘法右保序：a ≤ b 且 0 ≤ c ⟹ a·c ≤ b·c。
   Or(lt,eq) 四支全装配：lt×lt 走 real_mult_lt_compat；含 eq 支走
   real_eq_mult_compat + real_mult_zero(_l) 等式换形——零精确比较。 *)
Lemma klc_le_mult_r_weak : forall a b c : Real,
  real_le a b -> real_le real_zero c ->
  real_le (real_mult a c) (real_mult b c).
Proof.
  intros a b c Hab Hc. unfold real_le in Hab, Hc.
  destruct Hab as [Hlt | Heq]; destruct Hc as [Hc | Hc0].
  - exact (inl (real_mult_lt_compat a b c Hlt Hc)).
  - assert (HL : real_eq (real_mult a c) real_zero).
    { apply (real_eq_trans _ (real_mult a real_zero) _).
      - exact (RealSetoid.real_eq_mult_compat a c a real_zero
                 (real_eq_refl a) (real_eq_sym _ _ Hc0)).
      - apply real_mult_zero. }
    assert (HR : real_eq (real_mult b c) real_zero).
    { apply (real_eq_trans _ (real_mult b real_zero) _).
      - exact (RealSetoid.real_eq_mult_compat b c b real_zero
                 (real_eq_refl b) (real_eq_sym _ _ Hc0)).
      - apply real_mult_zero. }
    exact (inr (real_eq_trans (real_mult a c) real_zero (real_mult b c)
                  HL (real_eq_sym _ _ HR))).
  - exact (inr (RealSetoid.real_eq_mult_compat a c b c Heq (real_eq_refl c))).
  - exact (inr (RealSetoid.real_eq_mult_compat a c b c Heq (real_eq_refl c))).
Qed.

(* 非负乘法封闭：0 ≤ a 且 0 ≤ b ⟹ 0 ≤ a·b（Or 四支同法装配） *)
Lemma klc_mult_nonneg : forall a b : Real,
  real_le real_zero a -> real_le real_zero b ->
  real_le real_zero (real_mult a b).
Proof.
  intros a b Ha Hb. unfold real_le in Ha, Hb.
  destruct Ha as [Ha | Ha0]; destruct Hb as [Hb | Hb0].
  - exact (inl (real_mult_positive a b Ha Hb)).
  - assert (HL : real_eq (real_mult a b) real_zero).
    { apply (real_eq_trans _ (real_mult a real_zero) _).
      - exact (RealSetoid.real_eq_mult_compat a b a real_zero
                 (real_eq_refl a) (real_eq_sym _ _ Hb0)).
      - apply real_mult_zero. }
    exact (inr (real_eq_sym _ _ HL)).
  - assert (HL : real_eq (real_mult a b) real_zero).
    { apply (real_eq_trans _ (real_mult real_zero b) _).
      - exact (RealSetoid.real_eq_mult_compat a b real_zero b
                 (real_eq_sym _ _ Ha0) (real_eq_refl b)).
      - apply (real_eq_trans (real_mult real_zero b)
                 (real_mult b real_zero) real_zero).
        + apply real_mult_comm.
        + apply real_mult_zero. }
    exact (inr (real_eq_sym _ _ HL)).
  - assert (HL : real_eq (real_mult a b) real_zero).
    { apply (real_eq_trans _ (real_mult real_zero b) _).
      - exact (RealSetoid.real_eq_mult_compat a b real_zero b
                 (real_eq_sym _ _ Ha0) (real_eq_refl b)).
      - apply (real_eq_trans (real_mult real_zero b)
                 (real_mult b real_zero) real_zero).
        + apply real_mult_comm.
        + apply real_mult_zero. }
    exact (inr (real_eq_sym _ _ HL)).
Qed.

(* 弱正性归纳：0 ≤ base ⟹ 0 ≤ base^t（powb_pow 全域，零严格正前提） *)
Lemma klc_powb_nonneg : forall (base : Real) (t : nat),
  real_le real_zero base -> real_le real_zero (powb_pow base t).
Proof.
  intros base t Hb. induction t as [| m IH].
  - exact (inl real_lt_zero_one).
  - cbn [powb_pow]. exact (klc_mult_nonneg base (powb_pow base m) Hb IH).
Qed.

(* (1−η)+η == 1 的无条件换形基座（G07 powb_one_minus_eta_base_le_one
   同款 Heqsum 链：assoc/comm/plus_opp/plus_zero，零假设） *)
Lemma klc_one_minus_eta_plus_eta_eq_one : forall eta : Real,
  real_eq (real_plus (real_plus real_one (real_opp eta)) eta) real_one.
Proof.
  intro eta.
  apply (real_eq_trans _ (real_plus real_one (real_plus (real_opp eta) eta)) _).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans _ (real_plus real_one (real_plus eta (real_opp eta))) _).
    + apply (RealSetoid.real_eq_plus_compat real_one
               (real_plus (real_opp eta) eta) real_one
               (real_plus eta (real_opp eta))).
      * apply real_eq_refl.
      * apply real_plus_comm.
    + apply (real_eq_trans _ (real_plus real_one real_zero) _).
      * apply (RealSetoid.real_eq_plus_compat real_one
                 (real_plus eta (real_opp eta)) real_one real_zero).
        -- apply real_eq_refl.
        -- apply real_plus_opp.
      * apply real_plus_zero.
Qed.

(* 闭端上界：0 ≤ η ⟹ 1−η ≤ 1（弱版：G07 主定理同件去严格化——
   lt 支 (1−η) < (1−η)+η == 1；eq 支（η==0）(1−η) == (1−η)+η == 1） *)
Lemma klc_one_minus_eta_le_one_weak : forall eta : Real,
  real_le real_zero eta ->
  real_le (real_plus real_one (real_opp eta)) real_one.
Proof.
  intros eta H0. unfold real_le in H0. destruct H0 as [Hlt | Heq].
  - pose proof (real_lt_plus_r_zero (real_plus real_one (real_opp eta)) eta
                  Hlt) as Hlt0.
    exact (inl (real_lt_eq_lt (real_plus real_one (real_opp eta))
                  (real_plus (real_plus real_one (real_opp eta)) eta)
                  real_one Hlt0 (klc_one_minus_eta_plus_eta_eq_one eta))).
  - assert (He1 : real_eq (real_plus real_one (real_opp eta))
                    (real_plus (real_plus real_one (real_opp eta)) eta)).
    { apply (real_eq_trans _ (real_plus (real_plus real_one (real_opp eta))
                                real_zero) _).
      - apply real_eq_sym. apply real_plus_zero.
      - apply (RealSetoid.real_eq_plus_compat
                 (real_plus real_one (real_opp eta)) real_zero
                 (real_plus real_one (real_opp eta)) eta
                 (real_eq_refl (real_plus real_one (real_opp eta))) Heq). }
    exact (inr (real_eq_trans (real_plus real_one (real_opp eta))
                  (real_plus (real_plus real_one (real_opp eta)) eta)
                  real_one He1 (klc_one_minus_eta_plus_eta_eq_one eta))).
Qed.

(* 闭端下界：η ≤ 1 ⟹ 0 ≤ 1−η（Qopp 反向 + 加法兼容 + (1+−1)==0 换形；
   eta==1 时支路给 Or 右支等式 0 == 1−1——零退化支的 ≤ 证书形） *)
Lemma klc_one_minus_eta_nonneg_weak : forall eta : Real,
  real_le eta real_one ->
  real_le real_zero (real_plus real_one (real_opp eta)).
Proof.
  intros eta H1.
  pose proof (real_opp_le_compat eta real_one H1) as Hopp.
  pose proof (real_le_plus_compat real_one real_one
                (real_opp real_one) (real_opp eta)
                (klc_le_refl real_one) Hopp) as Hp.
  exact (klc_le_id_l (real_plus real_one (real_opp real_one)) real_zero
           (real_plus real_one (real_opp eta)) (real_plus_opp real_one) Hp).
Qed.

(* ============================================================ *)
(* Part D：powb 弱单调引擎（powb_mono_dec 同构去严格化：               *)
(*   严格正前提 real_lt real_zero base 全程降为 real_le——零退化支       *)
(*   base==0 就此被吸收，上游注记所指的严格正性证书不再被需要）          *)
(* ============================================================ *)

(* base^{S n} ≤_B base^n（弱前提版：base·u ≤ 1·u == u；≤_B 传递完成） *)
Lemma klc_sub_one_weak : forall (base : Real) (n : nat),
  real_le real_zero base -> real_le base real_one ->
  real_le_b (powb_pow base (Datatypes.S n)) (powb_pow base n).
Proof.
  intros base n H0 H1. cbn [powb_pow]. unfold real_le_b. intros eps Heps.
  pose proof (klc_powb_nonneg base n H0) as Hunonneg.
  pose proof (klc_le_mult_r_weak base real_one (powb_pow base n) H1
                Hunonneg) as Hmul.
  pose proof (klc_le_id_r (real_mult base (powb_pow base n))
                (real_mult real_one (powb_pow base n)) (powb_pow base n)
                (real_eq_trans (real_mult real_one (powb_pow base n))
                   (real_mult (powb_pow base n) real_one)
                   (powb_pow base n)
                   (real_mult_comm real_one (powb_pow base n))
                   (real_mult_one (powb_pow base n))) Hmul) as Hle.
  pose proof (real_le_to_le_b (real_mult base (powb_pow base n))
                (powb_pow base n) Hle) as HB1.
  pose proof (real_le_to_le_b (powb_pow base n)
                (real_plus (powb_pow base n) eps)
                (inl (real_lt_plus_r_zero (powb_pow base n) eps Heps))) as HB2.
  exact (HB1 eps Heps).
Qed.

(* base^t ≤_B 1（弱前提版） *)
Lemma klc_le_one_pow_weak : forall (base : Real) (t : nat),
  real_le real_zero base -> real_le base real_one ->
  real_le_b (powb_pow base t) real_one.
Proof.
  intros base t H0 H1. induction t as [| m IH].
  - exact (powb_le_b_refl real_one).
  - apply (real_le_b_trans (powb_pow base (Datatypes.S m))
             (powb_pow base m) real_one).
    + exact (klc_sub_one_weak base m H0 H1).
    + exact IH.
Qed.

(* 幂单调全量件（Set 层序界 NatLe；powb_mono_dec 逐支对应副本，弱前提） *)
Lemma klc_powb_mono_weak : forall (base : Real) (m : nat),
  real_le real_zero base -> real_le base real_one ->
  forall n : nat, NatLe n m ->
  real_le_b (powb_pow base m) (powb_pow base n).
Proof.
  intros base m H0 H1. induction m as [| m IH]; intros n Hnm.
  - destruct n as [| n1].
    + exact (powb_le_b_refl (powb_pow base 0)).
    + (* NatLe (S n1) 0 即 Id false true，零案例爆破 *)
      destruct (id_false_true Hnm).
  - destruct n as [| n1].
    + exact (klc_le_one_pow_weak base (Datatypes.S m) H0 H1).
    + destruct (Nat.leb (Datatypes.S n1) m) eqn:E2.
      * (* S n1 ≤ m：sub_one_weak + IH 传递链 *)
        apply (real_le_b_trans (powb_pow base (Datatypes.S m))
                 (powb_pow base m) (powb_pow base (Datatypes.S n1))).
        -- exact (klc_sub_one_weak base m H0 H1).
        -- apply IH.
           apply (NatLe_lift (Datatypes.S n1) m).
           apply (proj1 (Nat.leb_le (Datatypes.S n1) m)). exact E2.
      * (* n1 = m：Nat 反对称回代后自反 *)
        pose proof (proj1 (Nat.leb_gt (Datatypes.S n1) m) E2) as Hgt.
        pose proof (NatLe_drop n1 m Hnm) as Hn1m.
        pose proof (Nat.le_antisymm n1 m Hn1m
                     (proj1 (Nat.lt_succ_r m n1) Hgt)) as Heq.
        rewrite Heq.
        exact (powb_le_b_refl (powb_pow base (Datatypes.S m))).
Qed.

(* ============================================================ *)
(* Part E：主定理。                                                      *)
(*   E.1 Real 载体闭端全域版：0 ≤ η ≤ 1（real_le Set 层 Or 编码）下      *)
(*       (1−η)^{t1} ≤_B (1−η)^t——零退化分支被弱单调吸收，即上游注记     *)
(*       所要求的另设零退化分支之 ≤_B 形。                              *)
(*   E.2/E.3 Q 载体两支定理（严格收缩支 + 零退化非增支）。               *)
(*   E.4 Q 载体闭端组装：可判定分裂 × 统一收缩 × 分支附加证书 sigT 组合。*)
(* ============================================================ *)

Theorem klc_closed_powb_mono : forall (eta : Real) (t t1 : nat),
  real_le real_zero eta -> real_le eta real_one -> NatLe t t1 ->
  real_le_b (powb_pow (real_plus real_one (real_opp eta)) t1)
            (powb_pow (real_plus real_one (real_opp eta)) t).
Proof.
  intros eta t t1 H0 H1 Hle.
  exact (klc_powb_mono_weak (real_plus real_one (real_opp eta)) t1
           (klc_one_minus_eta_nonneg_weak eta H1)
           (klc_one_minus_eta_le_one_weak eta H0) t Hle).
Qed.

(* 严格收缩支：0 ≤ η < 1（Q 载体）⟹ 1−η > 0 严格正证书 + 全量 ≤_B 收缩。
   严格正证书正是上游判定「Real 层 1−η==0 与 1−η>0 不可分」所缺——
   Q 载体下由 Qcompare 可判定分裂构造性取得。 *)
Theorem klc_strict_branch : forall (eta : Q) (t t1 : nat),
  QleT' (0#1) eta -> QltT eta (1#1) -> NatLe t t1 ->
  prod (real_lt real_zero (real_const (1 - eta)%Q))
       (real_le_b (powb_pow (real_const (1 - eta)%Q) t1)
                  (powb_pow (real_const (1 - eta)%Q) t)).
Proof.
  intros eta t t1 H0 Hlt Hle. split.
  - exact (real_const_pos (1 - eta)%Q (klc_q_lt_zero_minus eta Hlt)).
  - apply (klc_powb_mono_weak (real_const (1 - eta)%Q) t1).
    + apply klc_const_le. apply Qle_to_QleT'.
      apply Qlt_le_weak.
      apply (proj1 (Qlt_minus_iff eta (1#1))).
      apply QltT_to_Qlt. exact Hlt.
    + apply klc_const_le. exact (klc_q_bound_upper eta H0).
    + exact Hle.
Qed.

(* 零退化非增支：η == 1（QeqT）⟹ 1−η == 0，幂链常值 0，≤_B 单调平凡成立 *)
Theorem klc_one_branch : forall (eta : Q) (t t1 : nat),
  QeqT eta (1#1) -> NatLe t t1 ->
  real_le_b (powb_pow (real_const (1 - eta)%Q) t1)
            (powb_pow (real_const (1 - eta)%Q) t).
Proof.
  intros eta t t1 Heq Hle. unfold QeqT in Heq.
  destruct (Qcompare eta (1#1)) eqn:E; try rewrite E in Heq; simpl in Heq.
  - (* Eq 支：η == 1 ⟹ 1−η == 0，幂链常值 0 *)
    pose proof (proj2 (Qeq_alt eta (1#1)) E) as Het.
    assert (Hz : (1 - eta)%Q == (0#1)) by (rewrite Het; ring).
    assert (Hb1 : QleT' (0#1) (1 - eta)%Q)
      by (apply Qle_to_QleT'; rewrite Hz; apply Qle_refl).
    assert (Hb2 : QleT' (1 - eta)%Q (1#1))
      by (apply Qle_to_QleT'; rewrite Hz; unfold Qle; simpl; lia).
    apply (klc_powb_mono_weak (real_const (1 - eta)%Q) t1).
    + apply klc_const_le. exact Hb1.
    + apply klc_const_le. exact Hb2.
    + exact Hle.
  - inversion Heq.
  - inversion Heq.
Qed.

(* 闭端组装（Q 载体）：0 ≤ η ≤ 1 ⟹ sigT 组合
   「可判定分裂证书 s ×（统一 ≤_B 收缩 × 分支附加证书）」：
   inl 支附加 (1−η)^{t1} > 0（严格正证书——上游注记所指缺口件的
   构造性到位），
   inr 支附加 unit（零退化支平凡）。 *)
Theorem klc_closed_Q : forall (eta : Q) (t t1 : nat),
  QleT' (0#1) eta -> QleT' eta (1#1) -> NatLe t t1 ->
  sigT (fun s : sum (QltT eta (1#1)) (QeqT eta (1#1)) =>
    prod (real_le_b (powb_pow (real_const (1 - eta)%Q) t1)
                    (powb_pow (real_const (1 - eta)%Q) t))
         (match s return Set with
          | inl _ => real_lt real_zero (powb_pow (real_const (1 - eta)%Q) t1)
          | inr _ => unit
          end)).
Proof.
  intros eta t t1 H0 H1 Hle.
  pose proof (klc_split_one eta H1) as Hs.
  exists Hs. split.
  - (* 统一 ≤_B 收缩：两支共享（弱单调引擎全域成立） *)
    apply (klc_powb_mono_weak (real_const (1 - eta)%Q) t1).
    + apply klc_const_le. exact (klc_q_bound_lower eta H1).
    + apply klc_const_le. exact (klc_q_bound_upper eta H0).
    + exact Hle.
  - (* 分支附加证书 *)
    destruct Hs as [Hlt | Heq].
    + exact (powb_pos_lt (real_const (1 - eta)%Q) t1
               (real_const_pos (1 - eta)%Q (klc_q_lt_zero_minus eta Hlt))).
    + exact tt.
Qed.

(* ============================================================ *)
(* 检验审计：提取 Obj.magic 计数应为 0 + 语句假设闭包                   *)
(* ============================================================ *)

Extraction "klc_G3.ml" klc_closed_powb_mono klc_closed_Q klc_strict_branch
  klc_one_branch klc_split_one klc_powb_mono_weak.

Print Assumptions klc_closed_powb_mono.
Print Assumptions klc_closed_Q.
Print Assumptions klc_strict_branch.
Print Assumptions klc_one_branch.
Print Assumptions klc_split_one.
Print Assumptions klc_powb_mono_weak.
