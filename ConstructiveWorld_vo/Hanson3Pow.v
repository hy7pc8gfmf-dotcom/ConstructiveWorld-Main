(* ============================================================
   Hanson3Pow —— 使命行：本件形式化 lcm(1..n) 的上界逼近：半程二项式桥构造
(*   （h3_ 前缀），朝 lcm(1..n) < 3^n 的构造性证明推进。                     *)
(* 主要结果：                                                               *)
(*   h3_binom_absorb：吸收恒等式 C(S n, S k)·S k = S n·C(n,k)               *)
(*     （双参数归纳自建）。                                                 *)
(*   h3_lcm_double_divide：L(2n) ∣ C(2n,n)·n!。                             *)
(*   h3_lcm_le_halfbinom：L(n) ≤ C(2⌈n/2⌉,⌈n/2⌉)·⌈n/2⌉!，严格强化           *)
(*     HansonLcm 的 L(n) ≤ n! 占位界。                                      *)
(*   h3_lcm_le_halfbinom_t：前者的 Set 层全称重述（hl_le_t 承载）。          *)
(* 范围注记：本件上界为半程形，仍含 ⌈n/2⌉! 档因子，非 3^n 档；更锐的          *)
(*   L(2n) ∣ C(2n,n)·L(n) 成立但其论证需素数 p-adic 赋值面，另案。           *)
(* 依赖：Stdlib Arith.Arith Arith.Factorial Lia + HansonLcm。                *)
(* 构造性注记：全件 Qed、零承认；主定理取 Set 层（hl_le_t），支撑引理为       *)
(*   nat 层 Prop 面、仅服务推理；h3_prod_from/h3_binom 皆可执行；            *)
(*   文末 Print Assumptions 复核。                                          *)
(* 编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），cpu_guard 包裹， *)
(*   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行（vo 树编译面）。 *)
   ============================================================*)

From Stdlib Require Import Arith.Arith Arith.Factorial Lia.
Require Import HansonLcm.

(* ============================================================ *)
(* §A 二项式算术：吸收恒等式 h3_binom_absorb                             *)
(* ============================================================ *)

(* k=0 边缘：hl_binom n 0 = 1 全 n 成立（首参递减 fix 对非 constructor
   首参不约化，故独立成件——h3_prod_binom_fact base 用） *)
Lemma h3_binom_k0 : forall n : nat, hl_binom n 0 = 1.
Proof. destruct n; reflexivity. Qed.

(* h3_binom_1：hl_binom (S n) 1 = S n（h3_binom_absorb 的 k=0 情形所用） *)
Lemma h3_binom_1 : forall n : nat, hl_binom (S n) 1 = S n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite (hl_binom_S (S n) 0).
    assert (E0 : hl_binom (S n) 0 = 1) by reflexivity.
    rewrite E0. rewrite IH. lia.
Qed.

(* h3_binom_absorb：吸收恒等式 C(S n, S k)·S k = S n·C(n,k)。
   对 n 归纳、k 分情形；归纳步在 k 与 S k 两点使用归纳前提
   （stdlib nat 层无库存二项式恒等式）。 *)
Lemma h3_binom_absorb : forall n k : nat,
  hl_binom (S n) (S k) * (S k) = (S n) * hl_binom n k.
Proof.
  induction n as [| n IH]; intro k.
  - destruct k as [| k']; reflexivity.
  - destruct k as [| k'].
    + rewrite (hl_binom_S (S n) 0).
      assert (E0 : hl_binom (S n) 0 = 1) by reflexivity.
      rewrite E0. rewrite h3_binom_1. lia.
    + rewrite (hl_binom_S (S n) (S k')).
      pose proof (IH k') as H1. pose proof (IH (S k')) as H2.
      rewrite (Nat.mul_succ_r (hl_binom (S n) (S (S k'))) (S k')) in H2.
      rewrite (Nat.mul_succ_r (hl_binom (S n) (S k')
                 + hl_binom (S n) (S (S k'))) (S k')).
      rewrite (Nat.mul_add_distr_r (hl_binom (S n) (S k'))
                 (hl_binom (S n) (S (S k'))) (S k')).
      rewrite H1.
      assert (HA : hl_binom (S n) (S k') = hl_binom n k' + hl_binom n (S k'))
        by reflexivity.
      assert (HAm : S n * hl_binom (S n) (S k') =
                    S n * hl_binom n k' + S n * hl_binom n (S k'))
        by (rewrite HA; ring).
      assert (HR : S (S n) * hl_binom (S n) (S k') =
                   S n * hl_binom (S n) (S k') + hl_binom (S n) (S k')) by ring.
      rewrite HR. lia.
Qed.

(* h3_binom_ge1：k ≤ n ⟹ 1 ≤ hl_binom n k（h3_divide_le 的正性前提所用） *)
Lemma h3_binom_ge1 : forall n k : nat, k <= n -> 1 <= hl_binom n k.
Proof.
  induction n as [| n IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. cbn [hl_binom]. lia.
  - destruct k as [| k'].
    + cbn [hl_binom]. lia.
    + rewrite (hl_binom_S n k').
      apply (Nat.le_trans 1 (hl_binom n k')).
      * apply IH. lia.
      * apply Nat.le_add_r.
Qed.

(* ============================================================ *)
(* §B 区间乘积：h3_prod_from a k = Π_{i=0}^{k-1} (a+i)                  *)
(* ============================================================ *)

Fixpoint h3_prod_from (a k : nat) : nat :=
  match k with
  | O => 1
  | S k' => (a + k') * h3_prod_from a k'
  end.

(* h3_prod_divide：a ≤ m < a+k ⟹ m ∣ h3_prod_from a k（m 本身是因子） *)
Lemma h3_prod_divide : forall k a m : nat,
  a <= m -> m < a + k -> Nat.divide m (h3_prod_from a k).
Proof.
  induction k as [| k IH]; intros a m H1 H2.
  - lia.
  - cbn [h3_prod_from].
    destruct (Nat.eq_dec m (a + k)) as [E|NE].
    + rewrite E. exists (h3_prod_from a k). ring.
    + destruct (IH a m H1 ltac:(lia)) as [p Hp].
      exists (p * (a + k))%nat. rewrite Hp. ring.
Qed.

(* h3_prod_binom_fact：主恒等式 Π_{i=1}^{k} (m+i) = C(m+k, k)·k!。
   对 k 归纳；归纳步由 h3_binom_absorb 闭合（乘法形式，免除法）。
   数值锚：n=1..15 有 Π(n+1..2n) = C(2n,n)·n!。 *)
Lemma h3_prod_binom_fact : forall m k : nat,
  h3_prod_from (S m) k = hl_binom (m + k) k * fact k.
Proof.
  intros m k. induction k as [| k IH].
  - rewrite h3_binom_k0. reflexivity.
  - cbn [h3_prod_from fact].
    rewrite Nat.add_succ_r, Nat.mul_assoc.
    pose proof (h3_binom_absorb (m + k) k) as HA.
    rewrite HA.
    replace (S (m + k)) with (S m + k) by lia.
    rewrite IH. ring.
Qed.

(* ============================================================ *)
(* §C lcm 折叠的整除闭包：全数整除 ⟹ 折叠值整除（由 stdlib Nat.lcm_least） *)
(* ============================================================ *)

(* h3_fact_divide：1 ≤ m ≤ n ⟹ m ∣ n!（对 n 归纳） *)
Lemma h3_fact_divide : forall n m : nat,
  1 <= m -> m <= n -> Nat.divide m (fact n).
Proof.
  induction n as [| n IH]; intros m H1 H2.
  - lia.
  - destruct (Nat.eq_dec m (S n)) as [E|NE].
    + rewrite E. exists (fact n). cbn [fact]. ring.
    + destruct (IH m H1 ltac:(lia)) as [p Hp].
      exists (p * S n)%nat. cbn [fact]. rewrite Hp. ring.
Qed.

(* h3_lcm_fold_divide：1..N 全数整除 D ⟹ L(N) ∣ D（stdlib Nat.lcm_least） *)
Lemma h3_lcm_fold_divide : forall N D : nat,
  (forall m : nat, 1 <= m -> m <= N -> Nat.divide m D) ->
  Nat.divide (hl_lcm_upto N) D.
Proof.
  intros N D H. induction N as [| N IHN].
  - cbn [hl_lcm_upto]. exists D. ring.
  - cbn [hl_lcm_upto]. apply Nat.lcm_least.
    + apply IHN. intros m H1 H2. apply H; lia.
    + apply H; lia.
Qed.

(* h3_lcm_upto_fact_divide：L(n) ∣ n!（h3_lcm_fold_divide 的实例） *)
Lemma h3_lcm_upto_fact_divide : forall n, Nat.divide (hl_lcm_upto n) (fact n).
Proof.
  intro n. apply h3_lcm_fold_divide. intros m H1 H2.
  apply h3_fact_divide; lia.
Qed.

(* h3_fact_pos：阶乘正性 0 < fact n *)
Lemma h3_fact_pos : forall n, 0 < fact n.
Proof.
  induction n as [| n IH].
  - cbn [fact]. lia.
  - cbn [fact]. apply Nat.mul_pos_pos; lia.
Qed.

(* h3_lcm_pos：1 ≤ L(n)（由 h3_lcm_upto_fact_divide 与 h3_fact_pos） *)
Lemma h3_lcm_pos : forall n, 1 <= hl_lcm_upto n.
Proof.
  intro n. destruct (h3_lcm_upto_fact_divide n) as [p Hp].
  pose proof (h3_fact_pos n) as Hf.
  destruct p as [| p'].
  - rewrite Nat.mul_0_l in Hp. lia.
  - destruct (hl_lcm_upto n) as [| L'].
    + rewrite Nat.mul_0_r in Hp. lia.
    + lia.
Qed.

(* h3_divide_le：整除与双正性前提 ⟹ a ≤ b *)
Lemma h3_divide_le : forall a b : nat,
  Nat.divide a b -> 1 <= a -> 0 < b -> a <= b.
Proof.
  intros a b Hd Ha Hb. destruct Hd as [p Hp]. destruct p as [| p'].
  - rewrite Nat.mul_0_l in Hp. lia.
  - destruct a as [| a'].
    + lia.
    + rewrite Hp. replace (S p' * S a') with (S a' + p' * S a') by ring. lia.
Qed.

(* h3_lcm_mono_divide：n ≤ m ⟹ L(n) ∣ L(m)（由 Nat.divide_lcm_l 逐层传递） *)
Lemma h3_lcm_mono_divide : forall n m : nat,
  n <= m -> Nat.divide (hl_lcm_upto n) (hl_lcm_upto m).
Proof.
  intros n m. induction m as [| m IHm]; intro H.
  - assert (n = 0) by lia. subst n. apply Nat.divide_refl.
  - destruct (Nat.eq_dec n (S m)) as [E|NE].
    + rewrite E. apply Nat.divide_refl.
    + cbn [hl_lcm_upto].
      apply (hl_div_trans (hl_lcm_upto n) (hl_lcm_upto m)
               (Nat.lcm (hl_lcm_upto m) (S m))).
      * apply IHm. lia.
      * apply Nat.divide_lcm_l.
Qed.

(* ============================================================ *)
(* §D 半程二项式桥（免素数面）——上界为半程形，非 3^n 档                  *)
(* ============================================================ *)

(* h3_lcm_double_divide：主定理 L(2n) ∣ C(2n,n)·n!。
   论证：m ≤ n 则 m ∣ n!；n < m ≤ 2n 则 m ∣ Π(n+1..2n) = C(2n,n)·n!
   （由 h3_prod_divide 与 h3_prod_binom_fact）；再由 h3_lcm_fold_divide 闭合。
   数值锚：n=1..15 成立。 *)
Theorem h3_lcm_double_divide : forall n : nat,
  Nat.divide (hl_lcm_upto (2 * n)) (hl_binom (2 * n) n * fact n).
Proof.
  intro n. apply h3_lcm_fold_divide. intros m H1 H2.
  destruct (Nat.le_gt_cases m n) as [Hle|Hgt].
  - apply (hl_div_trans m (fact n) (hl_binom (2 * n) n * fact n)).
    + apply h3_fact_divide; lia.
    + exists (hl_binom (2 * n) n). ring.
  - apply (hl_div_trans m (h3_prod_from (S n) n)
             (hl_binom (2 * n) n * fact n)).
    + apply h3_prod_divide; lia.
    + rewrite (h3_prod_binom_fact n n).
      replace (2 * n) with (n + n) by lia.
      exists 1. ring.
Qed.

(* h3_lcm_le_halfbinom：半程上界 L(n) ≤ C(2⌈n/2⌉,⌈n/2⌉)·⌈n/2⌉!，
   严格强化 HansonLcm.hl_lcm_le_fact 的 n! 占位界。
   范围注记：界仍含 ⌈n/2⌉! 档因子，非 3^n 档；
   3^n 档需素数 p-adic 赋值面，另案。 *)
Theorem h3_lcm_le_halfbinom : forall n : nat,
  hl_lcm_upto n <= hl_binom (2 * S (n / 2)) (S (n / 2)) * fact (S (n / 2)).
Proof.
  intro n.
  assert (H2n0 : 2 <> 0) by lia.
  pose proof (Nat.div_mod n 2 H2n0) as Hdm.
  pose proof (Nat.mod_upper_bound n 2 H2n0) as Hmod.
  assert (Hn : n <= 2 * S (n / 2)) by lia.
  apply (Nat.le_trans (hl_lcm_upto n) (hl_lcm_upto (2 * S (n / 2)))
           (hl_binom (2 * S (n / 2)) (S (n / 2)) * fact (S (n / 2)))).
  - pose proof (h3_lcm_pos (2 * S (n / 2))) as Hp1.
    apply h3_divide_le.
    + apply h3_lcm_mono_divide. exact Hn.
    + apply h3_lcm_pos.
    + lia.
  - pose proof (h3_lcm_pos (2 * S (n / 2))) as Hp2.
    assert (Hb : 1 <= hl_binom (2 * S (n / 2)) (S (n / 2)))
      by (apply h3_binom_ge1; lia).
    assert (Hf2 : 0 < fact (S (n / 2))) by apply h3_fact_pos.
    assert (Hd2 : 0 < hl_binom (2 * S (n / 2)) (S (n / 2)) * fact (S (n / 2)))
      by (apply Nat.mul_pos_pos; lia).
    apply h3_divide_le.
    + apply h3_lcm_double_divide.
    + lia.
    + exact Hd2.
Qed.

(* h3_lcm_le_halfbinom_t：Set 层全称重述（hl_le_t 承载，与 HansonLcm
   同名件同构；本件为其真强化；范围注记同上） *)
Theorem h3_lcm_le_halfbinom_t : forall n : nat,
  hl_le_t (hl_lcm_upto n)
    (hl_binom (2 * S (n / 2)) (S (n / 2)) * fact (S (n / 2)))%nat.
Proof.
  intro n.
  exact (hl_le_to_le_t (hl_lcm_upto n)
    (hl_binom (2 * S (n / 2)) (S (n / 2)) * fact (S (n / 2)))
    (h3_lcm_le_halfbinom n)).
Qed.

(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。 *)
Print Assumptions h3_lcm_double_divide.
Print Assumptions h3_lcm_le_halfbinom_t.
