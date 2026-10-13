(* 五字段指针｜模块：piu1886_kbounds.v。
   数学使命：Niven 型交错和多项式 F = lw0_F(lw0_niven_f q b n) n 的
   Q 层闭式界量——主定理两件：BF = |F(q)| ≤ κ₁、BFd = |F'(q)| ≤ κ₀，
   其中 κ₁/κ₀ 为逐项绝对值的有限和（lw0_qsum）闭式，逐项值取
   lw0_z_lo 端点闭式的绝对值；支撑面＝统一 q 端点镜式桥
   eval(D^k f, q) == lw0_alt k · eval(D^k f, 0)（全 k·含奇阶）与
   导数版 F 展开。附 κ₁/κ₀ 正性肢、正闭式逐项在 a 的单调肢及其
   有限和提升、kernel n_sel 实例化合流面。
   依赖清单：Stdlib QArith/QArith.Qabs/QArith.Qminmax/Lia/ZArith/
   Arith.Arith；LW0PiIrrational（lw0_F/lw0_F_eval_qsum/lw0_niven_f/
   lw0_niven_mirror/lw0_z_lo/lw0_niven_deriv_conn_lo_ab/
   lw0_niven_deriv_zero_0_ab/lw0_qsum/lw0_alt/lw0_zsign/lw0_binom/
   lw0_ratio/lw0_pi_mono/lw0_pi_qminus_pow/lw0_eval_iter_congr/
   lw0_eval_deriv_iter_scalar/lw0_n_select/lw0_pi_d0_of）。
   对标行：LW0LeibSeparation BF/BFd 显式上下界规划（交错和 max-项主导
   比值闭式）的界量基层；逐项闭式＝1862 第二镜式 f^(d)(q) 闭式，其库内
   认证承载＝lw0_niven_deriv_conn_lo_ab（全 k ≥ n 无上界前提）。
   构造性注记：零公理/零承认式/零经典逻辑；主定理与正性/单调主语句
   以 QleT'/Qabs（Set 面）承载，定义一律 Defined 透明；等值面 ==
   (Qeq) 与辅助记录引理（qsum 求和机制·逐项单调）沿库内既有惯例，
   作用域限于主定理语句的使用。语句面零 Qeq 方程前提（预防性
   约束兑现）。
   编译配方：coqc -native-compiler no -q -Q . "" -Q <vo>/Local ""
   -Q <vo> ""（cwd 本件沙箱；cpu_guard v3 包裹；SW2 全字面双
   export COQLIB/ROCQLIB；魔数 436f712100015ff4 一致性核验）。
   命名：piu1886_ 前缀。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qminmax.
From Stdlib Require Import Lia ZArith Arith.Arith.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0PiIrrational.

(* ---------- §1 有限和引擎：绝对值三角与逐项支配 ---------- *)

Lemma piu1886_qsum_abs_le : forall (g : nat -> Q) (m : nat),
  Qle (Qabs (lw0_qsum g m)) (lw0_qsum (fun i => Qabs (g i)) m).
Proof.
  intros g m. induction m as [|m IH].
  - cbn [lw0_qsum]. apply Qle_refl.
  - cbn [lw0_qsum].
    apply (Qle_trans _ (Qabs (lw0_qsum g m) + Qabs (g (Datatypes.S m)))%Q).
    + apply Qabs_triangle.
    + apply Qplus_le_compat; [ exact IH | apply Qle_refl ].
Qed.

Lemma piu1886_qsum_le : forall (g h : nat -> Q) (m : nat),
  (forall i, (i <= m)%nat -> Qle (g i) (h i)) ->
  Qle (lw0_qsum g m) (lw0_qsum h m).
Proof.
  intros g h m. induction m as [|m IH]; intro H.
  - cbn [lw0_qsum]. apply H. apply Nat.le_0_l.
  - cbn [lw0_qsum]. apply Qplus_le_compat.
    + apply IH. intros i Hi. apply H. lia.
    + apply H. lia.
Qed.

Lemma piu1886_qsum_0_le : forall (g : nat -> Q) (m : nat),
  (forall i, Qle 0 (g i)) -> Qle 0 (lw0_qsum g m).
Proof.
  intros g m. induction m as [|m IH]; intro H.
  - cbn [lw0_qsum]. apply H.
  - cbn [lw0_qsum].
    replace 0%Q with (0 + 0)%Q by reflexivity.
    apply (Qplus_le_compat 0%Q (lw0_qsum g m) 0%Q (g (Datatypes.S m))).
    + apply IH. exact H.
    + apply H.
Qed.

(* ---------- §2 统一 q 端点镜式桥（全 k·偶奇两阶齐载） ---------- *)

Lemma piu1886_niven_deriv_mirror_alt : forall (a : Z) (b : positive) (n k : nat),
  qpoly_eval (qpoly_deriv_iter k (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n))
             ((a # b)%Q)
  == lw0_alt k *
     qpoly_eval (qpoly_deriv_iter k (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n)) 0.
Proof.
  intros a b n k. unfold lw0_niven_f.
  rewrite (lw0_eval_deriv_iter_scalar k _
             (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow (a # b)%Q n))
             ((a # b)%Q)).
  rewrite (lw0_eval_deriv_iter_scalar k _
             (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow (a # b)%Q n)) 0).
  rewrite (lw0_niven_mirror (a # b)%Q n n k).
  rewrite (lw0_eval_iter_congr k
             (qpoly_mul (lw0_pi_qminus_pow (a # b)%Q n) (lw0_pi_mono n))
             (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow (a # b)%Q n)) 0
             (fun i => lw0_mul_comm (lw0_pi_qminus_pow (a # b)%Q n)
                                    (lw0_pi_mono n) i)).
  ring.
Qed.

Lemma piu1886_alt_even1 : forall j : nat, lw0_alt (2 * j) == 1%Q.
Proof.
  intros j. replace (2 * j)%nat with (j + j)%nat by lia.
  apply lw0_alt_double.
Qed.

Lemma piu1886_alt_sq : forall k : nat, lw0_alt k * lw0_alt k == 1%Q.
Proof.
  intros k. destruct (Nat.even k) eqn:E.
  - rewrite (lw0_alt_even_val k E). ring.
  - rewrite (lw0_alt_odd_val k E). ring.
Qed.

Lemma piu1886_niven_deriv_even_q : forall (a : Z) (b : positive) (n j : nat),
  (n <= 2 * j)%nat ->
  qpoly_eval (qpoly_deriv_iter (2 * j) (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n))
             ((a # b)%Q)
  == lw0_z_lo a (Zpos b) n (2 * j).
Proof.
  intros a b n j Hj.
  rewrite piu1886_niven_deriv_mirror_alt, piu1886_alt_even1, Qmult_1_l.
  apply (lw0_niven_deriv_conn_lo_ab a b n (2 * j)%nat Hj).
Qed.

Lemma piu1886_niven_deriv_odd_q : forall (a : Z) (b : positive) (n j : nat),
  (n <= Datatypes.S (2 * j))%nat ->
  qpoly_eval (qpoly_deriv_iter (Datatypes.S (2 * j))
                (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n)) ((a # b)%Q)
  == lw0_alt (Datatypes.S (2 * j)) *
     lw0_z_lo a (Zpos b) n (Datatypes.S (2 * j))%nat.
Proof.
  intros a b n j Hj.
  rewrite piu1886_niven_deriv_mirror_alt.
  rewrite (lw0_niven_deriv_conn_lo_ab a b n (Datatypes.S (2 * j))%nat Hj).
  reflexivity.
Qed.

Lemma piu1886_niven_deriv_even_q_zero : forall (a : Z) (b : positive) (n j : nat),
  (2 * j < n)%nat ->
  qpoly_eval (qpoly_deriv_iter (2 * j) (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n))
             ((a # b)%Q)
  == 0%Q.
Proof.
  intros a b n j Hj.
  rewrite piu1886_niven_deriv_mirror_alt, piu1886_alt_even1, Qmult_1_l.
  apply (lw0_niven_deriv_zero_0_ab a b n (2 * j)%nat Hj).
Qed.

Lemma piu1886_niven_deriv_odd_q_zero : forall (a : Z) (b : positive) (n j : nat),
  (Datatypes.S (2 * j) < n)%nat ->
  qpoly_eval (qpoly_deriv_iter (Datatypes.S (2 * j))
                (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n)) ((a # b)%Q)
  == 0%Q.
Proof.
  intros a b n j Hj.
  rewrite piu1886_niven_deriv_mirror_alt.
  rewrite (lw0_niven_deriv_zero_0_ab a b n (Datatypes.S (2 * j))%nat Hj).
  ring.
Qed.

(* ---------- §3 F 导数版展开（qsum 形） ---------- *)

Lemma piu1886_eval_deriv_scalar : forall (a : Q) (p : qpoly) (x : Q),
  qpoly_eval (qpoly_deriv (qpoly_scalar a p)) x
  == a * qpoly_eval (qpoly_deriv p) x.
Proof.
  intros a p x.
  replace (qpoly_deriv (qpoly_scalar a p))
    with (qpoly_deriv_iter 1 (qpoly_scalar a p)) by reflexivity.
  rewrite (lw0_eval_deriv_iter_scalar 1 a p x). reflexivity.
Qed.

Lemma piu1886_deriv_F_eval_qsum : forall (f : qpoly) (J : nat) (x : Q),
  qpoly_eval (qpoly_deriv (lw0_F f J)) x
  == lw0_qsum (fun j : nat =>
         lw0_alt j * qpoly_eval (qpoly_deriv_iter (Datatypes.S (2 * j)) f) x) J.
Proof.
  intros f J x. induction J as [|J IH].
  - unfold lw0_F, lw0_F_aux. cbn [lw0_qsum].
    change (Datatypes.S (2 * 0))%nat with 1%nat.
    change (qpoly_deriv_iter 1 f) with (qpoly_deriv f).
    change (lw0_alt 0%nat) with 1%Q.
    rewrite piu1886_eval_deriv_scalar. reflexivity.
  - unfold lw0_F. cbn [lw0_F_aux].
    change (lw0_F_aux f 1%Q J) with (lw0_F f J).
    rewrite (lw0_deriv_add_eval (lw0_F f J)
               (qpoly_scalar (1 * lw0_alt (Datatypes.S J))%Q
                  (qpoly_deriv_iter (2 * Datatypes.S J) f)) x).
    rewrite IH.
    rewrite (piu1886_eval_deriv_scalar (1 * lw0_alt (Datatypes.S J))%Q
               (qpoly_deriv_iter (2 * Datatypes.S J) f) x).
    change (qpoly_deriv (qpoly_deriv_iter (2 * Datatypes.S J) f))
      with (qpoly_deriv_iter (Datatypes.S (2 * Datatypes.S J)) f).
    cbn [lw0_qsum]. ring.
Qed.

(* ---------- §4 κ₁/κ₀ 闭式定义（逐项绝对值有限和） ---------- *)

Definition piu1886_k1 (a : Z) (b : positive) (n : nat) : Q :=
  lw0_qsum (fun j : nat =>
    if Nat.leb n (2 * j)
    then Qabs (lw0_z_lo a (Zpos b) n (2 * j))
    else (0 # 1)%Q) n.

Definition piu1886_k0 (a : Z) (b : positive) (n : nat) : Q :=
  lw0_qsum (fun j : nat =>
    if Nat.leb n (Datatypes.S (2 * j))
    then Qabs (lw0_z_lo a (Zpos b) n (Datatypes.S (2 * j)))
    else (0 # 1)%Q) n.

(* ---------- §5 交替系数绝对值桥 ---------- *)

Lemma piu1886_Qabs_1 : Qabs 1%Q == 1%Q.
Proof. reflexivity. Qed.

Lemma piu1886_Qabs_alt_mul : forall (j : nat) (z : Q), Qabs (lw0_alt j * z) == Qabs z.
Proof.
  intros j z. rewrite Qabs_Qmult.
  destruct (Nat.even j) eqn:Ej.
  - rewrite (lw0_alt_even_val j Ej), piu1886_Qabs_1, Qmult_1_l. reflexivity.
  - rewrite (lw0_alt_odd_val j Ej).
    replace (Qabs (-1%Q)) with (1%Q) by reflexivity.
    apply Qmult_1_l.
Qed.

Lemma piu1886_Qabs_alt2_mul : forall (k l : nat) (z : Q),
  Qabs (lw0_alt k * (lw0_alt l * z)) == Qabs z.
Proof.
  intros k l z. rewrite <- (piu1886_Qabs_alt_mul l z).
  apply piu1886_Qabs_alt_mul.
Qed.


(* ---------- §6 主定理两件：BF ≤ κ₁·BFd ≤ κ₀ ---------- *)

Theorem piu1886_bf_le_k1 : forall (a : Z) (b : positive) (n : nat),
  QleT' (Qabs (qpoly_eval (lw0_F (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n) n)
                           ((a # b)%Q)))
        (piu1886_k1 a b n).
Proof.
  intros a b n. unfold piu1886_k1. apply Qle_to_QleT'.
  rewrite (lw0_F_eval_qsum (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n) n ((a # b)%Q)).
  apply (Qle_trans _ (lw0_qsum (fun j : nat =>
           Qabs (lw0_alt j * qpoly_eval
                   (qpoly_deriv_iter (2 * j)%nat
                      (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n)) ((a # b)%Q))) n)).
  - apply piu1886_qsum_abs_le.
  - apply piu1886_qsum_le. intros i Hi. cbn beta.
    destruct (Nat.leb n (2 * i)) eqn:Ei.
    + apply Nat.leb_le in Ei.
      rewrite piu1886_Qabs_alt_mul.
      rewrite (piu1886_niven_deriv_even_q a b n i Ei).
      apply Qle_refl.
    + apply Nat.leb_gt in Ei.
      rewrite piu1886_Qabs_alt_mul.
      rewrite (piu1886_niven_deriv_even_q_zero a b n i Ei).
      replace (Qabs 0%Q) with (0%Q) by reflexivity. apply Qle_refl.
Qed.

Theorem piu1886_bfd_le_k0 : forall (a : Z) (b : positive) (n : nat),
  QleT' (Qabs (qpoly_eval (qpoly_deriv
                   (lw0_F (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n) n))
                   ((a # b)%Q)))
        (piu1886_k0 a b n).
Proof.
  intros a b n. unfold piu1886_k0. apply Qle_to_QleT'.
  rewrite (piu1886_deriv_F_eval_qsum
             (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n) n ((a # b)%Q)).
  apply (Qle_trans _ (lw0_qsum (fun j : nat =>
           Qabs (lw0_alt j * qpoly_eval
                   (qpoly_deriv_iter (Datatypes.S (2 * j))%nat
                      (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n)) ((a # b)%Q))) n)).
  - apply piu1886_qsum_abs_le.
  - apply piu1886_qsum_le. intros i Hi. cbn beta.
    destruct (Nat.leb n (Datatypes.S (2 * i))) eqn:Ei.
    + apply Nat.leb_le in Ei.
      rewrite (piu1886_niven_deriv_odd_q a b n i Ei).
      rewrite piu1886_Qabs_alt2_mul.
      apply Qle_refl.
    + apply Nat.leb_gt in Ei.
      rewrite piu1886_Qabs_alt_mul.
      rewrite (piu1886_niven_deriv_odd_q_zero a b n i Ei).
      replace (Qabs 0%Q) with (0%Q) by reflexivity. apply Qle_refl.
Qed.

(* ---------- §7 正性肢 ---------- *)

Theorem piu1886_k1_pos : forall (a : Z) (b : positive) (n : nat),
  QleT' 0 (piu1886_k1 a b n).
Proof.
  intros a b n. unfold piu1886_k1. apply Qle_to_QleT'.
  apply piu1886_qsum_0_le.
  intros i. cbn beta.
  destruct (Nat.leb n (2 * i)); [ apply Qabs_nonneg | ].
  unfold Qle. cbn [Qnum Qden]. lia.
Qed.

Theorem piu1886_k0_pos : forall (a : Z) (b : positive) (n : nat),
  QleT' 0 (piu1886_k0 a b n).
Proof.
  intros a b n. unfold piu1886_k0. apply Qle_to_QleT'.
  apply piu1886_qsum_0_le.
  intros i. cbn beta.
  destruct (Nat.leb n (Datatypes.S (2 * i))); [ apply Qabs_nonneg | ].
  unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* ---------- §8 正闭式与 a-单调肢 ---------- *)

Lemma piu1886_Qle_make_le : forall (u v : Z),
  Qle (u # 1)%Q (v # 1)%Q -> (u <= v)%Z.
Proof. intros u v H. unfold Qle in H. cbn in H. lia. Qed.

Lemma piu1886_le_Qle_make : forall (u v : Z),
  (u <= v)%Z -> Qle (u # 1)%Q (v # 1)%Q.
Proof. intros u v H. unfold Qle. cbn. lia. Qed.

Lemma piu1886_Qle_make_0 : forall (u : Z),
  (0 <= u)%Z -> Qle 0%Q (u # 1)%Q.
Proof. intros u H. unfold Qle. cbn. lia. Qed.

Definition piu1886_wbf_term (a : Z) (b : positive) (n j : nat) : Q :=
  if Nat.leb n (2 * j)
  then ((Z.of_nat (lw0_binom n (2 * j - n)) * Zpower_nat a (2 * n - 2 * j)
         * Zpower_nat (Z.pos b) (2 * j - n)
         * Z.of_nat (lw0_ratio n (2 * j))) # 1)%Q
  else (0 # 1)%Q.

Definition piu1886_wbfd_term (a : Z) (b : positive) (n j : nat) : Q :=
  if Nat.leb n (Datatypes.S (2 * j))
  then ((Z.of_nat (lw0_binom n (Datatypes.S (2 * j) - n))
         * Zpower_nat a (2 * n - Datatypes.S (2 * j))
         * Zpower_nat (Z.pos b) (Datatypes.S (2 * j) - n)
         * Z.of_nat (lw0_ratio n (Datatypes.S (2 * j)))) # 1)%Q
  else (0 # 1)%Q.

Lemma piu1886_Zmul_nonneg : forall (x y : Z),
  (0 <= x)%Z -> (0 <= y)%Z -> (0 <= x * y)%Z.
Proof.
  intros x y Hx Hy.
  destruct y as [|y'|y'].
  - simpl. lia.
  - destruct x as [|x'|x'].
    + simpl. lia.
    + simpl. lia.
    + simpl in Hx. lia.
  - simpl in Hy. lia.
Qed.

Lemma piu1886_Zpower_nat_pos : forall (x : Z) (m : nat),
  (0 <= x)%Z -> (0 <= Zpower_nat x m)%Z.
Proof.
  intros x m H. induction m as [|m IH].
  - rewrite Zpower_nat_0_r. lia.
  - rewrite Zpower_nat_succ_r. apply piu1886_Zmul_nonneg; assumption.
Qed.

Lemma piu1886_Zpower_nat_mono : forall (x y : Z) (m : nat),
  (0 <= x)%Z -> (x <= y)%Z -> (Zpower_nat x m <= Zpower_nat y m)%Z.
Proof.
  intros x y m H0 Hxy. induction m as [|m IH].
  - rewrite Zpower_nat_0_r, Zpower_nat_0_r. lia.
  - rewrite (Zpower_nat_succ_r m x), (Zpower_nat_succ_r m y).
    apply (Z.le_trans _ (y * Zpower_nat x m)%Z).
    + apply Zmult_le_compat_r;
        [ exact Hxy | apply piu1886_Zpower_nat_pos; exact H0 ].
    + apply Zmult_le_compat_l; [ exact IH | ].
      lia.
Qed.

Lemma piu1886_wbf_term_mono : forall (a a' : Z) (b : positive) (n j : nat),
  (0 <= a)%Z -> (a <= a')%Z ->
  Qle (piu1886_wbf_term a b n j) (piu1886_wbf_term a' b n j).
Proof.
  intros a a' b n j H0 Hle. unfold piu1886_wbf_term.
  destruct (Nat.leb n (2 * j)); [ | apply Qle_refl ].
  assert (Hbp : (0 < Z.pos b)%Z) by (destruct b; simpl; lia).
  pose proof (piu1886_Zpower_nat_pos (Z.pos b) (2 * j - n)
                (Z.lt_le_incl 0 (Z.pos b) Hbp)) as Hbn.
  unfold Qle. cbn [Qnum Qden].
  apply Zmult_le_compat_r; [ | lia ].
  apply Zmult_le_compat_r; [ | lia ].
  apply Zmult_le_compat_r; [ | exact Hbn ].
  apply Zmult_le_compat_l; [ apply piu1886_Zpower_nat_mono; assumption | lia ].
Qed.

Lemma piu1886_wbfd_term_mono : forall (a a' : Z) (b : positive) (n j : nat),
  (0 <= a)%Z -> (a <= a')%Z ->
  Qle (piu1886_wbfd_term a b n j) (piu1886_wbfd_term a' b n j).
Proof.
  intros a a' b n j H0 Hle. unfold piu1886_wbfd_term.
  destruct (Nat.leb n (Datatypes.S (2 * j))); [ | apply Qle_refl ].
  assert (Hbp : (0 < Z.pos b)%Z) by (destruct b; simpl; lia).
  pose proof (piu1886_Zpower_nat_pos (Z.pos b) (Datatypes.S (2 * j) - n)
                (Z.lt_le_incl 0 (Z.pos b) Hbp)) as Hbn.
  unfold Qle. cbn [Qnum Qden].
  apply Zmult_le_compat_r; [ | lia ].
  apply Zmult_le_compat_r; [ | lia ].
  apply Zmult_le_compat_r; [ | exact Hbn ].
  apply Zmult_le_compat_l; [ apply piu1886_Zpower_nat_mono; assumption | lia ].
Qed.

Theorem piu1886_wbf_qsum_mono : forall (a a' : Z) (b : positive) (n : nat),
  (0 <= a)%Z -> (a <= a')%Z ->
  Qle (lw0_qsum (piu1886_wbf_term a b n) n)
      (lw0_qsum (piu1886_wbf_term a' b n) n).
Proof.
  intros a a' b n H0 Hle. apply piu1886_qsum_le.
  intros i Hi. apply piu1886_wbf_term_mono; assumption.
Qed.

Theorem piu1886_wbfd_qsum_mono : forall (a a' : Z) (b : positive) (n : nat),
  (0 <= a)%Z -> (a <= a')%Z ->
  Qle (lw0_qsum (piu1886_wbfd_term a b n) n)
      (lw0_qsum (piu1886_wbfd_term a' b n) n).
Proof.
  intros a a' b n H0 Hle. apply piu1886_qsum_le.
  intros i Hi. apply piu1886_wbfd_term_mono; assumption.
Qed.

(* ---------- §9 kernel n_sel 实例化合流面 ---------- *)

Theorem piu1886_bf_le_k1_nsel : forall (a : Z) (b : positive),
  QleT' (Qabs (qpoly_eval
           (lw0_F (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q
                    (lw0_n_select (10 * lw0_pi_d0_of (Zpos b # 1)%Q) 0 + 1)%nat)
                  (lw0_n_select (10 * lw0_pi_d0_of (Zpos b # 1)%Q) 0 + 1)%nat)
           ((a # b)%Q)))
        (piu1886_k1 a b (lw0_n_select (10 * lw0_pi_d0_of (Zpos b # 1)%Q) 0 + 1)%nat).
Proof. intros a b. apply piu1886_bf_le_k1. Qed.

Theorem piu1886_bfd_le_k0_nsel : forall (a : Z) (b : positive),
  QleT' (Qabs (qpoly_eval (qpoly_deriv
           (lw0_F (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q
                    (lw0_n_select (10 * lw0_pi_d0_of (Zpos b # 1)%Q) 0 + 1)%nat)
                  (lw0_n_select (10 * lw0_pi_d0_of (Zpos b # 1)%Q) 0 + 1)%nat))
           ((a # b)%Q)))
        (piu1886_k0 a b (lw0_n_select (10 * lw0_pi_d0_of (Zpos b # 1)%Q) 0 + 1)%nat).
Proof. intros a b. apply piu1886_bfd_le_k0. Qed.

(* ========== 编译出口核对 ========== *)

Check piu1886_qsum_abs_le.
Check piu1886_qsum_le.
Check piu1886_qsum_0_le.
Check piu1886_niven_deriv_mirror_alt.
Check piu1886_niven_deriv_even_q.
Check piu1886_niven_deriv_odd_q.
Check piu1886_niven_deriv_even_q_zero.
Check piu1886_niven_deriv_odd_q_zero.
Check piu1886_deriv_F_eval_qsum.
Check piu1886_k1.
Check piu1886_k0.
Check piu1886_Qabs_alt_mul.
Check piu1886_bf_le_k1.
Check piu1886_bfd_le_k0.
Check piu1886_k1_pos.
Check piu1886_k0_pos.
Check piu1886_wbf_term_mono.
Check piu1886_wbfd_term_mono.
Check piu1886_wbf_qsum_mono.
Check piu1886_wbfd_qsum_mono.
Check piu1886_bf_le_k1_nsel.
Check piu1886_bfd_le_k0_nsel.

Print Assumptions piu1886_bf_le_k1.
Print Assumptions piu1886_bfd_le_k0.
Print Assumptions piu1886_k1_pos.
Print Assumptions piu1886_k0_pos.
Print Assumptions piu1886_wbf_qsum_mono.
Print Assumptions piu1886_wbfd_qsum_mono.
Print Assumptions piu1886_bf_le_k1_nsel.
Print Assumptions piu1886_bfd_le_k0_nsel.
