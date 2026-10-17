(* piu_zz_kernel_face_gd2p01.v — 剩余双出口件.

  使命：①件（积分核件）的剩余双出口，语句面：
    - 双出口一（核正性）：I_{A,B}(n)>0 的离散形。
      底砖 = 被积核 R_n(x) = 5 x^{2n} (x^4+6x^2+25)^{2n} / ((5+x)^{3n+1}(5-x)^{3n+1})
      在实段 (0,5) 上严格正（Q 承载，ZZ 式(2) R(x)，式(1) 第二等号的核）；
      非零源出口 = b_n := π 的系数（j=0 项提取，ZZ Lemma 6 关键计算
      ∫(1/(5+x)+1/(5-x))dx = πi/2 给出结构恒等式 b_n = (-1)^n · A_0/2）：
      A_0 ≠ 0 ⟹ b_n ≠ 0（案A 源位；点态 n=1 已 vm_compute 实证）。
    - 双出口二（尺寸粗界·完整性出口）：|kernel_n(x)| ≤ 2^{37n}（|x| ≤ 1, n ≥ 1），
      与 kernel_sum 的 |A_j| ≤ 2^{37n}（piu_zz_crude_size）同族粗界，只作护栏。
  σ 收紧走渐近引擎（另件）；wₙ 装配/Face-LINF 属后续部分。

  依赖：piu_zz_gauss_pair + piu_zz_kernel_sum＋stdlib
  （QArith/ZArith/Lia/Qring/Qabs）。

  构造性：全语句 Set 承载（qltT/qnzT 仿照 qeqT/qleT 先例）；零
  未证假设出口；数据全透明可计算（qpow/bcoef/kernel 均 vm_compute
  可归约）。

  订正：G6R 点名的 19 条 Q 面 Prop 结论语句
  全数消解为 Set 承载（前提面一律保持原文，仅结论换岸）：
  qltT_to_Qlt（T→Prop 逃逸口）除名，同 kernel_sum qleT_to_Qle/qeqT_eq 律；
  qnzT_neq 改形「qeqT 见证 → Empty_set」（Not 载体）；
  qpow_one/qplus_inv_r/qabs_mult/qpow_qmake_nat 改返 qeqT；
  qpow_nonneg/qpow_le_mono/qeq_le_l/qinv_le_one/qabs_le_bounds（qleT 有序对，
  And:=A*B 对照形）/qfive_add_ge/qfive_sub_ge/qabs_div_pos 改返 qleT；
  qpow_pos/qplus_pos_pos/qplus_pos_le/qsub_pos/qinv_pos 改返 qltT。
  载体全部取自 kernel_sum/gauss_pair 现成皿，零新铸；证明体内使用位以
  match 消除取 Prop 形（禁新命名 Prop 适配引理）。

  编译配方：bash cpu_guard.sh -- rocq c -native-compiler no -q -Q . "" piu_zz_kernel_face_gd2p01.v

  对标：ZZ 2020 v2（arXiv:1912.06345）式(1)(2)、Lemma 6 关键计算、G01 §2-① 双出口 v2、
  A01 §3 常数档案；样点对拍 A01 档案：A_1,0 = −2392（修正版 kernel_sum，样点 2x bug
  已回归档案值），bcoef 1 = (−1)^1·A_0/2 = +1196。 *)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import QArith.Qabs.
Require Import piu_zz_gauss_pair.
Require Import piu_zz_kernel_sum.

(* rider：16 使用位随 kernel_sum 改形联动——
   Qmult_le_compat_l→Qmult_le_compat_l_spec（qleT 皿）9 位、Qsq_nonneg（qleT 皿）
   7 位；体内 match-elim（qleT_intro 场消除）取 Prop 形（A 案，
   禁新命名 Prop 适配引理）。 *)

(* ------------------------------------------------------------------ *)
(* Set 承载谓词：qltT（仿照 qleT）、qnzT（Set 承载非零见证）             *)
(* ------------------------------------------------------------------ *)

Inductive qltT : Q -> Q -> Set :=
| qltT_intro : forall a b : Q, (a < b)%Q -> qltT a b.

Lemma qltT_of_Qlt : forall x y : Q, (x < y)%Q -> qltT x y.
Proof. intros x y H. apply qltT_intro. exact H. Qed.

Inductive qnzT : Q -> Set :=
| qnzT_intro : forall a : Q, ~ (a == (0 # 1)%Q) -> qnzT a.

Lemma qnzT_neq : forall (a : Q) (h : qnzT a), qeqT a (0 # 1)%Q -> Empty_set.
Proof.
  intros a h H0. destruct h as [a0 Hne].
  pose proof (match H0 as H1 in qeqT u v return (u == v)%Q with
              | qeqT_intro _ _ Hw => Hw end) as Hprop.
  destruct (Hne Hprop).
Qed.

(* ------------------------------------------------------------------ *)
(* nat 指数 Q 幂                                                        *)
(* ------------------------------------------------------------------ *)

Fixpoint qpow (x : Q) (k : nat) : Q :=
  match k with
  | O => (1 # 1)%Q
  | S k' => x * qpow x k'
  end.

Lemma qpow_one : forall k : nat, qeqT (qpow (1 # 1)%Q k) (1 # 1)%Q.
Proof.
  induction k as [| k IH]; cbn [qpow].
  - apply qeqT_refl.
  - eapply qeqT_trans.
    + apply (qeqT_mul_l (qpow (1 # 1)%Q k) (1 # 1)%Q (1 # 1)%Q IH).
    + apply qeqT_intro. apply Qmult_1_l.
Qed.

Lemma qpow_nonneg : forall (k : nat) (a : Q),
  ((0 # 1)%Q <= a)%Q -> qleT (0 # 1)%Q (qpow a k).
Proof.
  induction k as [| k IH]; intros a Ha.
  - cbn [qpow]. apply qleT_intro. unfold Qle. cbn. lia.
  - cbn [qpow]. apply qleT_intro.
    pose proof (match (IH a Ha) as H0 in qleT c d return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as HI.
    apply (Qle_trans (0 # 1) ((0 # 1)%Q * qpow a k) (a * qpow a k)).
    + rewrite Qmult_0_l. apply Qle_refl.
    + apply Qmult_le_compat_r; [ exact Ha | exact HI ].
Qed.

Lemma qpow_pos : forall (k : nat) (x : Q), (0 < x)%Q -> qltT (0 # 1)%Q (qpow x k).
Proof.
  induction k as [| k IH]; intros x Hx.
  - apply qltT_intro. unfold Qlt. cbn. lia.
  - apply qltT_intro. cbn [qpow]. apply Qmult_lt_0_compat.
    + exact Hx.
    + exact (match IH x Hx as H0 in qltT c d return (c < d)%Q with
             | qltT_intro _ _ h => h end).
Qed.

Lemma qpow_le_mono : forall (k : nat) (a b : Q),
  ((0 # 1)%Q <= a)%Q -> (a <= b)%Q -> qleT (qpow a k) (qpow b k).
Proof.
  induction k as [| k IH]; intros a b Ha Hb.
  - cbn [qpow]. apply qleT_intro. apply Qle_refl.
  - cbn [qpow].
    pose proof (match (qpow_nonneg k a Ha) as H0 in qleT c d return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as Hqa'.
    eapply qleT_trans.
    + apply (qleT_mul_le_compat_r a b (qpow a k) Hqa' (qleT_of_Qle Hb)).
    + apply qleT_of_Qle.
      pose proof (match (Qmult_le_compat_l_spec (IH a b Ha Hb)
                  (qleT_of_Qle (Qle_trans (0 # 1) a b Ha Hb))) as H0 in qleT c d return (c <= d)%Q with
       | qleT_intro _ _ h => h end) as H.
      exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* Q 正性/序微引理（stdlib 序引理 + 常数桥，零裸积）                     *)
(* ------------------------------------------------------------------ *)

Lemma qplus_inv_r : forall q : Q, qeqT (q + (- q)) (0 # 1)%Q.
Proof.
  intros q. destruct q as [qn qd]. apply qeqT_intro.
  unfold Qeq. cbn [Qplus Qopp Qnum Qden Pos.mul]. lia.
Qed.

Lemma qplus_pos_pos : forall a b : Q,
  ((0 # 1)%Q < a)%Q -> ((0 # 1)%Q < b)%Q -> qltT (0 # 1)%Q (a + b).
Proof.
  intros a b Ha Hb. apply qltT_intro.
  assert (H00 : ((0 # 1)%Q == (0 # 1)%Q + (0 # 1)%Q)%Q) by reflexivity.
  rewrite H00. apply (Qplus_lt_compat (0 # 1) a (0 # 1) b); assumption.
Qed.

Lemma qplus_pos_le : forall a b : Q,
  ((0 # 1)%Q <= a)%Q -> ((0 # 1)%Q < b)%Q -> qltT (0 # 1)%Q (a + b).
Proof.
  intros a b Ha Hb. apply qltT_intro. rewrite (Qplus_comm a b).
  assert (H00 : ((0 # 1)%Q == (0 # 1)%Q + (0 # 1)%Q)%Q) by reflexivity.
  rewrite H00. apply (Qplus_lt_le_compat (0 # 1) b (0 # 1) a); assumption.
Qed.

Lemma qsub_pos : forall a b : Q, (b < a)%Q -> qltT (0 # 1)%Q (a - b).
Proof.
  intros a b H. apply qltT_intro.
  pose proof (match (qplus_inv_r b) as H0 in qeqT u v return (u == v)%Q with
              | qeqT_intro _ _ h => h end) as Hinv.
  rewrite <- Hinv.
  apply (Qplus_lt_le_compat b a (- b) (- b)).
  - exact H.
  - apply Qle_refl.
Qed.

Lemma qeq_le_l : forall a b : Q, (a == b)%Q -> qleT a b.
Proof.
  intros a b H. apply qleT_intro. unfold Qle. rewrite H. apply Z.le_refl.
Qed.

Lemma qinv_pos : forall b : Q, (0 < b)%Q -> qltT (0 # 1)%Q (/ b).
Proof.
  intros b Hb. apply qltT_intro.
  destruct b as [bn bd].
  unfold Qlt in Hb. cbn [Qnum Qden] in Hb.
  unfold Qlt. destruct bn as [| p | p]; cbn [Qinv Qnum Qden]; lia.
Qed.

Lemma qinv_le_one : forall v : Q, ((1 # 1)%Q <= v)%Q -> qleT (Qabs (/ v)) (1 # 1)%Q.
Proof.
  intros v Hv. apply qleT_intro.
  destruct v as [vn vd].
  unfold Qle in Hv. cbn [Qnum Qden] in Hv.
  unfold Qabs, Qle.
  destruct vn as [| p | p]; cbn [Qinv Qnum Qden Z.abs]; lia.
Qed.

Lemma qabs_mult : forall a b : Q, qeqT (Qabs (a * b)) (Qabs a * Qabs b).
Proof.
  intros a b. destruct a as [an ad]. destruct b as [bn bd].
  apply qeqT_intro.
  unfold Qabs, Qeq. cbn [Qmult Qnum Qden].
  rewrite Z.abs_mul. reflexivity.
Qed.

Lemma qabs_le_bounds : forall x : Q,
  (Qabs x <= (1 # 1)%Q)%Q -> qleT ((-1 # 1)%Q) x * qleT x ((1 # 1)%Q).
Proof.
  intros x H. split.
  - apply qleT_intro.
    destruct (Qlt_le_dec 0 x) as [Hlt | Hle].
    + rewrite (Qabs_pos x (Qlt_le_weak 0 x Hlt)) in H.
      apply (Qle_trans (-1 # 1) (0 # 1)).
      * unfold Qle. cbn. lia.
      * apply (Qlt_le_weak 0 x). exact Hlt.
    + rewrite (Qabs_neg x Hle) in H.
      pose proof (Qopp_le_compat (- x) (1 # 1) H) as H1.
      assert (H2 : ((- (1 # 1)) == (-1 # 1))%Q) by reflexivity.
      rewrite H2 in H1.
      assert (H3 : (- (- x) == x)%Q) by ring.
      rewrite H3 in H1.
      exact H1.
  - apply qleT_intro.
    destruct (Qlt_le_dec 0 x) as [Hlt | Hle].
    + rewrite (Qabs_pos x (Qlt_le_weak 0 x Hlt)) in H. exact H.
    + apply (Qle_trans x (0 # 1)).
      * exact Hle.
      * unfold Qle. cbn. lia.
Qed.

Lemma qfive_add_ge : forall x : Q, ((-1 # 1)%Q <= x)%Q -> qleT (4 # 1)%Q ((5 # 1)%Q + x).
Proof.
  intros x H. apply qleT_intro.
  destruct x as [xn xd].
  unfold Qle in H. cbn [Qnum Qden] in H.
  unfold Qle. cbn [Qplus Qnum Qden]. lia.
Qed.

Lemma qfive_sub_ge : forall x : Q, (x <= (1 # 1)%Q)%Q -> qleT (4 # 1)%Q ((5 # 1)%Q - x).
Proof.
  intros x H. apply qleT_intro.
  destruct x as [xn xd].
  unfold Qle in H. cbn [Qnum Qden] in H.
  unfold Qle. cbn [Qminus Qplus Qopp Qnum Qden]. lia.
Qed.

(* |a/d| ≤ a 当 a ≥ 0, d ≥ 1 *)
Lemma qabs_div_pos : forall a d : Q,
  ((0 # 1)%Q <= a)%Q -> ((1 # 1)%Q <= d)%Q -> qleT (Qabs (Qdiv a d)) a.
Proof.
  intros a d Ha Hd. apply qleT_intro.
  assert (Heq : (Qabs (Qdiv a d) == Qabs a * Qabs (/ d))%Q).
  { pose proof (match (qabs_mult a (/ d)) as H0 in qeqT u v return (u == v)%Q with
                | qeqT_intro _ _ h => h end) as Hm.
    exact Hm. }
  assert (Hinvp : (0 < / d)%Q).
  { assert (Hd1 : ((0 # 1)%Q < (1 # 1)%Q)%Q) by (unfold Qlt; cbn; lia).
    pose proof (match (qinv_pos d (Qlt_le_trans (0 # 1) (1 # 1) d Hd1 Hd))
                as H0 in qltT c d0 return (c < d0)%Q with
                | qltT_intro _ _ h => h end) as H.
    exact H. }
  assert (Hinv1 : (/ d <= (1 # 1)%Q)%Q).
  { pose proof (match (qinv_le_one d Hd) as H0 in qleT c d0 return (c <= d0)%Q with
                | qleT_intro _ _ h => h end) as Hq.
    rewrite (Qabs_pos (/ d) (Qlt_le_weak (0 # 1)%Q (/ d) Hinvp)) in Hq.
    exact Hq. }
  rewrite Heq.
  rewrite (Qabs_pos a Ha).
  rewrite (Qabs_pos (/ d) (Qlt_le_weak (0 # 1)%Q (/ d) Hinvp)).
  eapply Qle_trans.
  - pose proof (match (Qmult_le_compat_l_spec (qleT_of_Qle Hinv1) (qleT_of_Qle Ha)) as H0 in qleT c d return (c <= d)%Q with
       | qleT_intro _ _ h => h end) as H. exact H.
  - rewrite Qmult_1_r. apply Qle_refl.
Qed.

(* nat 幂换算 *)
Lemma pow32_2n : forall n : nat, (32 ^ (2 * n) = 2 ^ (10 * n))%nat.
Proof.
  intros n. replace (32)%nat with (2 ^ 5)%nat by reflexivity.
  rewrite <- Nat.pow_mul_r.
  replace (5 * (2 * n))%nat with (10 * n)%nat by lia.
  reflexivity.
Qed.

Lemma qpow_qmake_nat : forall p k : nat,
  qeqT (qpow ((Z.of_nat p # 1)%Q) k) ((Z.of_nat (p ^ k)) # 1)%Q.
Proof.
  intros p k. induction k as [| k IH].
  - cbn [qpow Qmult]. rewrite Nat.pow_0_r. apply qeqT_refl.
  - cbn [qpow]. rewrite Nat.pow_succ_r'. rewrite Nat2Z.inj_mul.
    eapply qeqT_trans.
    + apply (qeqT_mul_l (qpow ((Z.of_nat p # 1)%Q) k) ((Z.of_nat (p ^ k)) # 1)%Q
                        ((Z.of_nat p # 1)%Q) IH).
    + cbn [Qmult Pos.mul]. apply qeqT_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* 定义面：被积核（ZZ 式(2) R(x)）与 π 系数（j=0 提取，b_n=(-1)^n·A_0/2） *)
(* ------------------------------------------------------------------ *)

Definition piu_zz_poly4 (x : Q) : Q :=
  (((x * x) * (x * x)) + ((6 # 1)%Q * (x * x)) + (25 # 1)%Q)%Q.

Definition piu_zz_kernel (n : nat) (x : Q) : Q :=
  Qdiv
    ((5 # 1)%Q * (qpow (x * x) (2 * n) * qpow (piu_zz_poly4 x) (2 * n))%Q)
    (qpow ((5 # 1)%Q + x) (3 * n + 1) * qpow ((5 # 1)%Q - x) (3 * n + 1))%Q.

Definition piu_zz_bcoef (n : nat) : Q :=
  (zz_sign n * (piu_zz_Aj n 0 * (1 # 2)%Q))%Q.

(* ------------------------------------------------------------------ *)
(* 双出口一（核正性）：被积核严格正（I_{A,B}(n)>0 的离散核底）            *)
(* ------------------------------------------------------------------ *)

Theorem piu_zz_kernel_pos : forall (n : nat) (x : Q),
  ((0 # 1)%Q < x)%Q -> (x < (5 # 1)%Q)%Q ->
  qltT (0 # 1)%Q (piu_zz_kernel n x).
Proof.
  intros n x Hx Hx5.
  assert (Hxx : ((0 # 1)%Q < (x * x))%Q) by (apply Qmult_lt_0_compat; assumption).
  assert (H6 : ((0 # 1)%Q <= (6 # 1)%Q * (x * x))%Q).
  { eapply Qle_trans;
      [ | apply (Qmult_le_compat_r (0 # 1) (6 # 1) (x * x));
          [ unfold Qle; cbn; lia | pose proof (match (Qsq_nonneg x) as H0 in qleT c d return (c <= d)%Q with
       | qleT_intro _ _ h => h end) as H; exact H ] ].
    rewrite Qmult_0_l. apply Qle_refl. }
  assert (Hsum0 : ((0 # 1)%Q <= ((x * x) * (x * x) + (6 # 1)%Q * (x * x)))%Q).
  { assert (H00 : ((0 # 1)%Q == (0 # 1)%Q + (0 # 1)%Q)%Q) by reflexivity.
    rewrite H00. apply Qplus_le_compat.
    + pose proof (match (Qsq_nonneg (x * x)) as H0 in qleT c d return (c <= d)%Q with
       | qleT_intro _ _ h => h end) as H. exact H.
    + exact H6. }
  assert (Hp4 : ((0 # 1)%Q < piu_zz_poly4 x)%Q).
  { assert (Hlt4 : qltT (0 # 1)%Q
                (((x * x) * (x * x) + (6 # 1)%Q * (x * x)) + (25 # 1)%Q)%Q).
    { unfold piu_zz_poly4.
      apply (qplus_pos_le ((x * x) * (x * x) + (6 # 1)%Q * (x * x))%Q (25 # 1)%Q).
      - exact Hsum0.
      - unfold Qlt. cbn. lia. }
    unfold piu_zz_poly4.
    exact (match Hlt4 as H0 in qltT c d return (c < d)%Q with
           | qltT_intro _ _ h => h end). }
  assert (Hq1 : ((0 # 1)%Q < qpow (x * x) (2 * n))%Q).
  { pose proof (match (qpow_pos (2 * n) (x * x) Hxx) as H0 in qltT c d return (c < d)%Q with
                | qltT_intro _ _ h => h end) as H.
    exact H. }
  assert (Hq2 : ((0 # 1)%Q < qpow (piu_zz_poly4 x) (2 * n))%Q).
  { pose proof (match (qpow_pos (2 * n) (piu_zz_poly4 x) Hp4) as H0 in qltT c d return (c < d)%Q with
                | qltT_intro _ _ h => h end) as H.
    exact H. }
  assert (Hdx : ((0 # 1)%Q < ((5 # 1)%Q + x))%Q).
  { assert (H05 : ((0 # 1)%Q < (5 # 1)%Q)%Q) by (unfold Qlt; cbn; lia).
    pose proof (match (qplus_pos_pos (5 # 1)%Q x H05 Hx) as H0 in qltT c d return (c < d)%Q with
                | qltT_intro _ _ h => h end) as H.
    exact H. }
  assert (Hdxp : ((0 # 1)%Q < ((5 # 1)%Q - x))%Q).
  { pose proof (match (qsub_pos (5 # 1)%Q x Hx5) as H0 in qltT c d return (c < d)%Q with
                | qltT_intro _ _ h => h end) as H.
    exact H. }
  assert (HD : ((0 # 1)%Q <
                (qpow ((5 # 1)%Q + x) (3 * n + 1) * qpow ((5 # 1)%Q - x) (3 * n + 1)))%Q).
  { apply Qmult_lt_0_compat.
    - exact (match (qpow_pos (3 * n + 1) ((5 # 1)%Q + x) Hdx) as H0 in qltT c d return (c < d)%Q with
             | qltT_intro _ _ h => h end).
    - exact (match (qpow_pos (3 * n + 1) ((5 # 1)%Q - x) Hdxp) as H0 in qltT c d return (c < d)%Q with
             | qltT_intro _ _ h => h end). }
  apply qltT_of_Qlt. unfold piu_zz_kernel. cbn [Qdiv].
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat.
    + unfold Qlt. cbn. lia.
    + apply Qmult_lt_0_compat; [ exact Hq1 | exact Hq2 ].
  - exact (match (qinv_pos ((qpow ((5 # 1)%Q + x) (3 * n + 1)
                            * qpow ((5 # 1)%Q - x) (3 * n + 1))%Q) HD)
           as H0 in qltT c d return (c < d)%Q with
           | qltT_intro _ _ h => h end).
Qed.

(* ------------------------------------------------------------------ *)
(* 双出口二（尺寸粗界）：|kernel_n(x)| ≤ 2^{37n}（|x|≤1, n≥1）           *)
(* ------------------------------------------------------------------ *)

Theorem piu_zz_kernel_size : forall (n : nat) (x : Q),
  (Qabs x <= (1 # 1)%Q)%Q -> (0 < n)%nat ->
  qleT (Qabs (piu_zz_kernel n x)) ((Z.of_nat (2 ^ (37 * n)) # 1)%Q).
Proof.
  intros n x Habs Hn.
  destruct (qabs_le_bounds x Habs) as [Hm1 H1].
  pose proof (match Hm1 as H0 in qleT c d return (c <= d)%Q with
              | qleT_intro _ _ h => h end) as Hm1'.
  pose proof (match H1 as H0 in qleT c d return (c <= d)%Q with
              | qleT_intro _ _ h => h end) as H1p.
  assert (H01 : ((0 # 1)%Q <= (1 # 1)%Q)%Q) by (unfold Qle; cbn; lia).
  assert (H04 : ((0 # 1)%Q <= (4 # 1)%Q)%Q) by (unfold Qle; cbn; lia).
  assert (H14 : ((1 # 1)%Q <= (4 # 1)%Q)%Q) by (unfold Qle; cbn; lia).
  pose proof (match (qfive_add_ge x Hm1') as H0 in qleT c d return (c <= d)%Q with
              | qleT_intro _ _ h => h end) as Hbx1.
  pose proof (match (qfive_sub_ge x H1p) as H0 in qleT c d return (c <= d)%Q with
              | qleT_intro _ _ h => h end) as Hbx2.
  assert (Hstep4 : (qpow (1 # 1)%Q (3 * n + 1) <= qpow (4 # 1)%Q (3 * n + 1))%Q).
  { pose proof (match (qpow_le_mono (3 * n + 1) (1 # 1) (4 # 1) H01 H14)
                as H0 in qleT c d return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as H.
    exact H. }
  assert (HA1 : ((1 # 1)%Q <= qpow ((5 # 1)%Q + x) (3 * n + 1))%Q).
  { pose proof (match (qpow_le_mono (3 * n + 1) (4 # 1) ((5 # 1)%Q + x) H04 Hbx1)
                as H0 in qleT c d return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as HA1'.
    pose proof (match (qpow_one (3 * n + 1)) as H0 in qeqT u v return (u == v)%Q with
                | qeqT_intro _ _ h => h end) as Hq1.
    rewrite <- Hq1.
    eapply Qle_trans; [ exact Hstep4 | exact HA1' ]. }
  assert (HA2 : ((1 # 1)%Q <= qpow ((5 # 1)%Q - x) (3 * n + 1))%Q).
  { pose proof (match (qpow_le_mono (3 * n + 1) (4 # 1) ((5 # 1)%Q - x) H04 Hbx2)
                as H0 in qleT c d return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as HA2'.
    pose proof (match (qpow_one (3 * n + 1)) as H0 in qeqT u v return (u == v)%Q with
                | qeqT_intro _ _ h => h end) as Hq1.
    rewrite <- Hq1.
    eapply Qle_trans; [ exact Hstep4 | exact HA2' ]. }
  assert (HD1 : ((1 # 1)%Q <=
                (qpow ((5 # 1)%Q + x) (3 * n + 1) * qpow ((5 # 1)%Q - x) (3 * n + 1)))%Q).
  { assert (Hunit : (((1 # 1)%Q * (1 # 1)%Q) == (1 # 1)%Q)%Q) by reflexivity.
    rewrite <- Hunit.
    eapply Qle_trans.
    - apply (Qmult_le_compat_r (1 # 1) (qpow ((5 # 1)%Q + x) (3 * n + 1)) (1 # 1)).
      + exact HA1.
      + unfold Qle. cbn. lia.
    - assert (Hdxq0 : ((0 # 1)%Q <= qpow ((5 # 1)%Q + x) (3 * n + 1))%Q).
      { assert (Hdxqp : qltT (0 # 1)%Q (qpow ((5 # 1)%Q + x) (3 * n + 1))).
        { apply (qpow_pos (3 * n + 1)).
          apply (Qlt_le_trans (0 # 1) (4 # 1)); [ unfold Qlt; cbn; lia | exact Hbx1 ]. }
        apply (Qlt_le_weak (0 # 1)%Q (qpow ((5 # 1)%Q + x) (3 * n + 1))).
        exact (match Hdxqp as H0 in qltT c d return (c < d)%Q with
               | qltT_intro _ _ h => h end). }
      pose proof (match (Qmult_le_compat_l_spec (qleT_of_Qle HA2) (qleT_of_Qle Hdxq0)) as H0 in qleT c d return (c <= d)%Q with
       | qleT_intro _ _ h => h end) as H. exact H. }
  assert (Hxx1 : ((x * x) <= (1 # 1)%Q)%Q).
  { destruct (Qlt_le_dec 0 x) as [Hlt | Hle].
    - rewrite (Qabs_pos x (Qlt_le_weak 0 x Hlt)) in Habs.
      assert (Hs1 : ((x * x) <= ((1 # 1)%Q * x))%Q)
        by (apply (Qmult_le_compat_r x (1 # 1));
            [ exact Habs | apply (Qlt_le_weak 0); exact Hlt ]).
      assert (Hs2 : (((1 # 1)%Q * x) <= ((1 # 1)%Q * (1 # 1)%Q))%Q).
      { pose proof (match (Qmult_le_compat_l_spec (qleT_of_Qle Habs) (qleT_of_Qle H01)) as H0 in qleT c d return (c <= d)%Q with
       | qleT_intro _ _ h => h end) as H. exact H. }
      assert (He11 : (((1 # 1)%Q * (1 # 1)%Q) == (1 # 1)%Q)%Q) by reflexivity.
      eapply Qle_trans; [ exact Hs1 | ].
      eapply Qle_trans; [ exact Hs2 | ].
      rewrite He11. apply Qle_refl.
    - rewrite (Qabs_neg x Hle) in Habs.
      assert (Hneg : ((x * x) == ((- x) * (- x)))%Q) by ring.
      rewrite Hneg.
      assert (Hnx : ((0 # 1)%Q <= (- x))%Q).
      { pose proof (Qopp_le_compat x (0 # 1) Hle) as H1'.
        assert (H2' : ((- (0 # 1)) == (0 # 1))%Q) by reflexivity.
        rewrite H2' in H1'. exact H1'. }
      assert (Hs1 : (((- x) * (- x)) <= ((1 # 1)%Q * (- x)))%Q)
        by (apply (Qmult_le_compat_r (- x) (1 # 1)); [ exact Habs | exact Hnx ]).
      assert (Hs2 : (((1 # 1)%Q * (- x)) <= ((1 # 1)%Q * (1 # 1)%Q))%Q).
      { pose proof (match (Qmult_le_compat_l_spec (qleT_of_Qle Habs) (qleT_of_Qle H01)) as H0 in qleT c d return (c <= d)%Q with
       | qleT_intro _ _ h => h end) as H. exact H. }
      assert (He11 : (((1 # 1)%Q * (1 # 1)%Q) == (1 # 1)%Q)%Q) by reflexivity.
      eapply Qle_trans; [ exact Hs1 | ].
      eapply Qle_trans; [ exact Hs2 | ].
      rewrite He11. apply Qle_refl. }
  assert (Hx4 : (((x * x) * (x * x)) <= ((1 # 1)%Q * (1 # 1)%Q))%Q).
  { eapply Qle_trans.
    - apply (Qmult_le_compat_r (x * x) (1 # 1) (x * x));
        [ exact Hxx1 | pose proof (match (Qsq_nonneg x) as H0 in qleT c d return (c <= d)%Q with
       | qleT_intro _ _ h => h end) as H; exact H ].
    - pose proof (match (Qmult_le_compat_l_spec (qleT_of_Qle Hxx1) (qleT_of_Qle H01)) as H0 in qleT c d return (c <= d)%Q with
       | qleT_intro _ _ h => h end) as H. exact H. }
  assert (H06 : ((0 # 1)%Q <= (6 # 1)%Q)%Q) by (unfold Qle; cbn; lia).
  assert (Hx6 : (((6 # 1)%Q * (x * x)) <= ((6 # 1)%Q * (1 # 1)%Q))%Q).
  { pose proof (match (Qmult_le_compat_l_spec (qleT_of_Qle Hxx1) (qleT_of_Qle H06)) as H0 in qleT c d return (c <= d)%Q with
       | qleT_intro _ _ h => h end) as H. exact H. }
  assert (Hp4b : (piu_zz_poly4 x <=
                (((1 # 1)%Q * (1 # 1)%Q) + ((6 # 1)%Q * (1 # 1)%Q)) + (25 # 1)%Q)%Q).
  { unfold piu_zz_poly4. apply Qplus_le_compat.
    - apply Qplus_le_compat; [ exact Hx4 | exact Hx6 ].
    - apply Qle_refl. }
  assert (H4b : ((0 # 1)%Q <= piu_zz_poly4 x)%Q).
  { assert (Hp4pos : ((0 # 1)%Q < piu_zz_poly4 x)%Q).
    { assert (Hsum0 : ((0 # 1)%Q <= ((x * x) * (x * x) + (6 # 1)%Q * (x * x)))%Q).
      { assert (H00 : ((0 # 1)%Q == (0 # 1)%Q + (0 # 1)%Q)%Q) by reflexivity.
        rewrite H00. apply Qplus_le_compat.
        + pose proof (match (Qsq_nonneg (x * x)) as H0 in qleT c d return (c <= d)%Q with
       | qleT_intro _ _ h => h end) as H. exact H.
        + eapply Qle_trans;
            [ | apply (Qmult_le_compat_r (0 # 1) (6 # 1) (x * x));
                [ unfold Qle; cbn; lia | pose proof (match (Qsq_nonneg x) as H0 in qleT c d return (c <= d)%Q with
       | qleT_intro _ _ h => h end) as H; exact H ] ].
          rewrite Qmult_0_l. apply Qle_refl. }
      assert (Hlt4 : qltT (0 # 1)%Q
                  (((x * x) * (x * x) + (6 # 1)%Q * (x * x)) + (25 # 1)%Q)%Q).
      { unfold piu_zz_poly4.
        apply (qplus_pos_le ((x * x) * (x * x) + (6 # 1)%Q * (x * x))%Q (25 # 1)%Q).
        - exact Hsum0.
        - unfold Qlt. cbn. lia. }
      unfold piu_zz_poly4.
      exact (match Hlt4 as H0 in qltT c d return (c < d)%Q with
             | qltT_intro _ _ h => h end). }
    apply (Qlt_le_weak (0 # 1)%Q (piu_zz_poly4 x)). exact Hp4pos. }
  assert (H32q : ((((1 # 1)%Q * (1 # 1)%Q) + ((6 # 1)%Q * (1 # 1)%Q)) + (25 # 1)%Q)
                == ((Z.of_nat 32) # 1)%Q) by reflexivity.
  assert (Hq32 : (qpow (piu_zz_poly4 x) (2 * n) <= ((Z.of_nat (2 ^ (10 * n))) # 1)%Q)%Q).
  { assert (Hconv : (qpow (((Z.of_nat 32) # 1)%Q) (2 * n)
                   == ((Z.of_nat (32 ^ (2 * n))) # 1)%Q)).
    { pose proof (match (qpow_qmake_nat 32 (2 * n)) as H0 in qeqT u v return (u == v)%Q with
                  | qeqT_intro _ _ h => h end) as H.
      exact H. }
    assert (Hpow : ((32 ^ (2 * n)) = (2 ^ (10 * n)))%nat) by apply pow32_2n.
    assert (Hp432 : (piu_zz_poly4 x <= ((Z.of_nat 32) # 1)%Q)%Q).
    { rewrite <- H32q. exact Hp4b. }
    pose proof (match (qpow_le_mono (2 * n) (piu_zz_poly4 x) ((Z.of_nat 32) # 1) H4b Hp432)
                as H0 in qleT c d return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as Hmono.
    eapply Qle_trans; [ exact Hmono | ].
    rewrite Hconv. rewrite Hpow. apply Qle_refl. }
  pose proof (match (Qsq_nonneg x) as H0 in qleT c d return (c <= d)%Q with
              | qleT_intro _ _ h => h end) as Hxx0p.
  assert (Hqxx : (qpow (x * x) (2 * n) <= (1 # 1)%Q)%Q).
  { pose proof (match (qpow_le_mono (2 * n) (x * x) (1 # 1) Hxx0p Hxx1)
                as H0 in qleT c d return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as Hmono.
    pose proof (match (qpow_one (2 * n)) as H0 in qeqT u v return (u == v)%Q with
                | qeqT_intro _ _ h => h end) as Hq1.
    rewrite Hq1 in Hmono. exact Hmono. }
  assert (Hqxx0 : ((0 # 1)%Q <= qpow (x * x) (2 * n))%Q).
  { pose proof (match (qpow_nonneg (2 * n) (x * x) Hxx0p)
                as H0 in qleT c d return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as H.
    exact H. }
  assert (Hp40 : ((0 # 1)%Q <= qpow (piu_zz_poly4 x) (2 * n))%Q).
  { pose proof (match (qpow_nonneg (2 * n) (piu_zz_poly4 x) H4b)
                as H0 in qleT c d return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as H.
    exact H. }
  assert (Hprod0 : ((0 # 1)%Q <=
                  (qpow (x * x) (2 * n) * qpow (piu_zz_poly4 x) (2 * n)))%Q).
  { eapply Qle_trans;
      [ | apply (Qmult_le_compat_r (0 # 1) (qpow (x * x) (2 * n))
                   (qpow (piu_zz_poly4 x) (2 * n)));
          [ exact Hqxx0 | exact Hp40 ] ].
    rewrite Qmult_0_l. apply Qle_refl. }
  assert (Hprod1 : ((qpow (x * x) (2 * n) * qpow (piu_zz_poly4 x) (2 * n)) <=
                  ((1 # 1)%Q * ((Z.of_nat (2 ^ (10 * n))) # 1)))%Q).
  { eapply Qle_trans.
    - apply (Qmult_le_compat_r (qpow (x * x) (2 * n)) (1 # 1));
        [ exact Hqxx | exact Hp40 ].
    - pose proof (match (Qmult_le_compat_l_spec (qleT_of_Qle Hq32) (qleT_of_Qle H01)) as H0 in qleT c d return (c <= d)%Q with
       | qleT_intro _ _ h => h end) as H. exact H. }
  assert (H58 : (((5 # 1)%Q * ((Z.of_nat (2 ^ (10 * n))) # 1))%Q <=
               (((1 # 1)%Q * ((Z.of_nat (2 ^ (10 * n + 3))) # 1))%Q))%Q).
  { assert (HLle : (((5 # 1)%Q * ((Z.of_nat (2 ^ (10 * n))) # 1))%Q <=
                  (((Z.of_nat (5 * 2 ^ (10 * n))) # 1)%Q))%Q).
    { unfold Qle. cbn [Qmult Qnum Qden Pos.mul]. rewrite !Z.mul_1_r.
      replace 5%Z with (Z.of_nat 5)%Z by reflexivity.
      rewrite <- Nat2Z.inj_mul.
      apply (proj1 (Nat2Z.inj_le (5 * 2 ^ (10 * n)) (5 * 2 ^ (10 * n)))).
      apply Nat.le_refl. }
    assert (HRle2 : (((Z.of_nat (1 * 2 ^ (10 * n + 3))) # 1)%Q <=
                   (((1 # 1)%Q * ((Z.of_nat (2 ^ (10 * n + 3))) # 1))%Q))%Q).
    { unfold Qle. cbn [Qmult Qnum Qden Pos.mul]. rewrite !Z.mul_1_r.
      replace (1 * Z.of_nat (2 ^ (10 * n + 3)))%Z
        with (Z.of_nat (2 ^ (10 * n + 3)))%Z by lia.
      apply (proj1 (Nat2Z.inj_le (1 * 2 ^ (10 * n + 3)) (2 ^ (10 * n + 3)))).
      lia. }
    eapply Qle_trans; [ exact HLle | ].
    eapply Qle_trans; [ | exact HRle2 ].
    unfold Qle. cbn [Qnum Qden]. repeat rewrite Z.mul_1_r.
    apply (proj1 (Nat2Z.inj_le (5 * 2 ^ (10 * n)) (1 * 2 ^ (10 * n + 3)))).
    assert (Hpow : (1 * 2 ^ (10 * n + 3) = 8 * 2 ^ (10 * n))%nat).
    { replace (10 * n + 3)%nat with (3 + 10 * n)%nat by lia.
      rewrite Nat.pow_add_r.
      replace (2 ^ 3)%nat with 8%nat by reflexivity.
      lia. }
    rewrite Hpow.
    apply (Nat.mul_le_mono_r 5 8 (2 ^ (10 * n))).
    lia. }
  assert (H05 : ((0 # 1)%Q <= (5 # 1)%Q)%Q) by (unfold Qle; cbn; lia).
  assert (HNB : (((5 # 1)%Q * (qpow (x * x) (2 * n) * qpow (piu_zz_poly4 x) (2 * n))) <=
               (((1 # 1)%Q * ((Z.of_nat (2 ^ (10 * n + 3))) # 1))%Q))%Q).
  { eapply Qle_trans.
    - pose proof (match (Qmult_le_compat_l_spec (qleT_of_Qle Hprod1) (qleT_of_Qle H05)) as H0 in qleT c d return (c <= d)%Q with
       | qleT_intro _ _ h => h end) as H. exact H.
    - rewrite Qmult_1_l. exact H58. }
  assert (H37 : (((Z.of_nat (2 ^ (10 * n + 3))) # 1)%Q
               <= ((Z.of_nat (2 ^ (37 * n))) # 1)%Q)%Q).
  { unfold Qle. cbn [Qnum Qden Qmult].
    repeat rewrite Z.mul_1_r.
    apply (proj1 (Nat2Z.inj_le (2 ^ (10 * n + 3)) (2 ^ (37 * n)))).
    apply Nat.pow_le_mono_r; lia. }
  assert (HkN : qleT (Qabs (piu_zz_kernel n x))
                  ((5 # 1)%Q * (qpow (x * x) (2 * n) * qpow (piu_zz_poly4 x) (2 * n)))%Q).
  { unfold piu_zz_kernel.
    apply (qabs_div_pos ((5 # 1)%Q * (qpow (x * x) (2 * n) * qpow (piu_zz_poly4 x) (2 * n)))
                        (qpow ((5 # 1)%Q + x) (3 * n + 1)
                       * qpow ((5 # 1)%Q - x) (3 * n + 1))).
    - (* 0 ≤ 分子 *)
      eapply Qle_trans;
        [ | apply (Qmult_le_compat_r (0 # 1) (5 # 1)
             (qpow (x * x) (2 * n) * qpow (piu_zz_poly4 x) (2 * n)));
            [ unfold Qle; cbn; lia | exact Hprod0 ] ].
      rewrite Qmult_0_l. apply Qle_refl.
    - exact HD1. }
  assert (HNBq : qleT ((5 # 1)%Q * (qpow (x * x) (2 * n) * qpow (piu_zz_poly4 x) (2 * n)))
                      ((Z.of_nat (2 ^ (37 * n)) # 1)%Q)).
  { assert (HNB2 : (((5 # 1)%Q * (qpow (x * x) (2 * n) * qpow (piu_zz_poly4 x) (2 * n))) <=
                   ((Z.of_nat (2 ^ (37 * n))) # 1)%Q)%Q).
    { pose proof (match (qeq_le_l ((1 # 1)%Q * ((Z.of_nat (2 ^ (10 * n + 3))) # 1))
                        ((Z.of_nat (2 ^ (10 * n + 3))) # 1)
                        (Qmult_1_l ((Z.of_nat (2 ^ (10 * n + 3))) # 1)))
                  as H0 in qleT c d return (c <= d)%Q with
                  | qleT_intro _ _ h => h end) as H1y.
      exact (Qle_trans ((5 # 1)%Q * (qpow (x * x) (2 * n) * qpow (piu_zz_poly4 x) (2 * n)))
                       ((1 # 1)%Q * ((Z.of_nat (2 ^ (10 * n + 3))) # 1))
                       ((Z.of_nat (2 ^ (37 * n))) # 1) HNB
             (Qle_trans ((1 # 1)%Q * ((Z.of_nat (2 ^ (10 * n + 3))) # 1))
                        ((Z.of_nat (2 ^ (10 * n + 3))) # 1)
                        ((Z.of_nat (2 ^ (37 * n))) # 1) H1y H37)). }
    apply qleT_of_Qle. exact HNB2. }
  eapply qleT_trans.
  - exact HkN.
  - exact HNBq.
Qed.

(* ------------------------------------------------------------------ *)
(* 双出口一（非零源）：b_n = (-1)^n·A_0/2 结构恒等面（定义即恒等式）      *)
(* ------------------------------------------------------------------ *)

Theorem piu_zz_b_nonzero : forall n : nat,
  qnzT (piu_zz_Aj n 0) -> qnzT (piu_zz_bcoef n).
Proof.
  intros n Hq. apply (qnzT_intro (piu_zz_bcoef n)). intro Hbc.
  destruct (Qmult_integral _ _ Hbc) as [Hs0 | Hr0].
  - unfold zz_sign in Hs0. destruct (Nat.even n); vm_compute in Hs0; discriminate.
  - destruct (Qmult_integral _ _ Hr0) as [HA0' | Hh0].
    + destruct (qnzT_neq (piu_zz_Aj n 0) Hq
                  (qeqT_intro (piu_zz_Aj n 0) (0 # 1)%Q HA0')).
    + vm_compute in Hh0. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* vm_compute 样点 2 枚（n=1；对拍 A01 档案，L01S ×2 倍差口径）           *)
(* ------------------------------------------------------------------ *)

Lemma piu_zz_bcoef_sample_n1 : qeqT (piu_zz_bcoef 1) ((1196 # 1)%Q).
Proof. apply qeqT_intro. vm_compute. reflexivity. Qed.

Lemma piu_zz_kernel_sample_n1 : qeqT (piu_zz_kernel 1 (1 # 1)%Q) ((5120 # 331776)%Q).
Proof. apply qeqT_intro. vm_compute. reflexivity. Qed.

Lemma piu_zz_kernel_pos_sample_n1 : qltT (0 # 1)%Q (piu_zz_kernel 1 (1 # 1)%Q).
Proof. apply (piu_zz_kernel_pos 1 (1 # 1)).
  - unfold Qlt. cbn. lia.
  - unfold Qlt. cbn. lia.
Qed.

Print Assumptions qltT_of_Qlt.
Print Assumptions qnzT_neq.
Print Assumptions qpow_one.
Print Assumptions qpow_nonneg.
Print Assumptions qpow_pos.
Print Assumptions qpow_le_mono.
Print Assumptions qplus_inv_r.
Print Assumptions qplus_pos_pos.
Print Assumptions qplus_pos_le.
Print Assumptions qsub_pos.
Print Assumptions qeq_le_l.
Print Assumptions qinv_pos.
Print Assumptions qinv_le_one.
Print Assumptions qabs_mult.
Print Assumptions qabs_le_bounds.
Print Assumptions qfive_add_ge.
Print Assumptions qfive_sub_ge.
Print Assumptions qabs_div_pos.
Print Assumptions pow32_2n.
Print Assumptions qpow_qmake_nat.
Print Assumptions piu_zz_kernel_pos.
Print Assumptions piu_zz_kernel_size.
Print Assumptions piu_zz_b_nonzero.
Print Assumptions piu_zz_bcoef_sample_n1.
Print Assumptions piu_zz_kernel_sample_n1.
Print Assumptions piu_zz_kernel_pos_sample_n1.
