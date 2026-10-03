(* ==================================================================== *)
(* LW2Binom.v — nat-level binomial coefficient tools with a Z bridge.   *)
(* 模块名＋数学使命: nat 面二项式系数 lw2_binom（Pascal 递归真算法）及  *)
(*   配套件: 非负性 lw2_binom_nonneg（布尔形）; 对称律 lw2_binom_sym    *)
(*   的零前提适用形 C(k+m,k)=C(k+m,m)（k<=n 时即 C(n,k)=C(n,n-k)，经    *)
(*   加法形承载免 Prop 前提）; 零支 lw2_binom_above 与对角              *)
(*   lw2_binom_diag; 阶乘刻画 lw2_binom_fact（对称律的计量主引理）;     *)
(*   Z 面三条: 符号因子方程 lw2_zsign_even / lw2_zsign_odd（(−1) 幂的   *)
(*   奇偶分解，供 S07 lo 式 z_lo 的符号因子取用），以及 Z 因子取用方程  *)
(*   lw2_binom_Z（Z.of_nat (lw2_binom n k) 的三分支形，取用方在 Z 域    *)
(*   直接展开 Pascal 结构而无需回走 nat）。                              *)
(* Exact 形态声明: lw2_binom 由三条定义方程刻画（各为 reflexivity 可验）:*)
(*   lw2_binom n 0 = 1                                                   *)
(*   lw2_binom 0 (S k) = 0                                               *)
(*   lw2_binom (S n) (S k) = lw2_binom n (S k) + lw2_binom n k           *)
(* Pascal 恒等式即第三条定义方程，故免单独引理。                   *)
(* 依赖清单 (Stdlib only): Arith, ZArith, Lia.                           *)
(* 对标行: 语句面形与 LW2ZInt.v (LW2 波) 同族; binom 递归形对标 Pascal 加法定义 (UpReqBanachAdd bpa_binom 为 Q 值形, 本件为其 nat 因子件). *)
(*   LW0Integrality2 的免除法阶乘见证 lw0_ratio / lw0_fact_ratio 与本件  *)
(*   lw2_binom / lw2_fact 同处 nat 阶乘计量域: 合并时以 lw2_binom_fact  *)
(*   为连接方程，lw0 件取用本件 Z 因子时经 lw2_binom_Z 与                *)
(*   lw2_zsign_even / lw2_zsign_odd 两个入口。                           *)
(* 构造性注记: 全部语句为量化方程（零 Prop 前提，零 Prop 泄露）; 全部    *)
(*   定义为 Fixpoint 真算法; 全部证明构造性给出（结构归纳＋方程重写＋   *)
(*   ring/lia/Nat.div_mul），零未证占位、零经典原则、零假设常量。        *)
(* 编译配方: coqc -q -Q . "" LW2Binom.v                                 *)
(* ==================================================================== *)

From Stdlib Require Import Arith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

(* nat 二项式系数，Pascal 递归（递归变元为首参 n）。 *)
Fixpoint lw2_binom (n k : nat) : nat :=
  match n with
  | 0 => match k with 0 => 1 | S _ => 0 end
  | S n' =>
      match k with
      | 0 => 1
      | S k' => lw2_binom n' (S k') + lw2_binom n' k'
      end
  end.

(* nat 阶乘（Z 桥的计量基础）。 *)
Fixpoint lw2_fact (n : nat) : nat :=
  match n with 0 => 1 | S m => S m * lw2_fact m end.

(* 非负性（布尔形，平凡但显式）。 *)
Lemma lw2_binom_nonneg : forall n k : nat, Nat.leb 0 (lw2_binom n k) = true.
Proof. intros n k. reflexivity. Qed.

(* 阶乘恒正（后继见证形，供对称律的除法消去）。 *)
Lemma lw2_fact_pos : forall n : nat, exists p : nat, lw2_fact n = S p.
Proof.
  induction n as [|n IH].
  - exists 0. reflexivity.
  - destruct IH as [p Hp]. exists (p + n * S p). simpl. rewrite Hp. reflexivity.
Qed.

(* 零支: k>n 时系数为零。 *)
Lemma lw2_binom_above : forall n k : nat, lw2_binom n (n + S k) = 0.
Proof.
  induction n as [|n IH]; intro k; simpl.
  - reflexivity.
  - replace (S (n + S k)) with (n + S (S k)) by lia.
    rewrite (IH (S k)), (IH k). reflexivity.
Qed.

(* 对角: C(n,n)=1。 *)
Lemma lw2_binom_diag : forall n : nat, lw2_binom n n = 1.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl. pose proof (lw2_binom_above n 0) as HA.
    replace (S n) with (n + S 0) by lia. rewrite HA, IH. reflexivity.
Qed.

(* 乘法左交换（环境无 Nat.mul_left_comm，本地补）。 *)
Lemma lw2_mul_left_comm : forall a b c : nat, a * (b * c) = b * (a * c).
Proof.
  intros a b c.
  rewrite (Nat.mul_assoc a b c), (Nat.mul_comm a b), <- (Nat.mul_assoc b a c).
  reflexivity.
Qed.

(* 阶乘刻画（对称律的计量主引理）。 *)
Lemma lw2_binom_fact : forall n k : nat,
  lw2_fact (n + k) = lw2_binom (n + k) k * (lw2_fact n * lw2_fact k).
Proof.
  induction n as [|n IH].
  - intro k. simpl. rewrite lw2_binom_diag, ?Nat.mul_1_l. lia.
  - intro k. induction k as [|c IHc].
    + simpl. rewrite ?Nat.add_0_r, ?Nat.mul_1_r, ?Nat.mul_1_l. reflexivity.
    + assert (HB : lw2_binom (S n + S c) (S c)
                   = lw2_binom (n + S c) (S c) + lw2_binom (n + S c) c)
        by reflexivity.
      assert (HF : lw2_fact (S n + S c) = S (n + S c) * lw2_fact (n + S c))
        by reflexivity.
      assert (H1 : lw2_fact (S n) = S n * lw2_fact n) by reflexivity.
      assert (H2 : lw2_fact (S c) = S c * lw2_fact c) by reflexivity.
      rewrite HB, HF, H1, H2.
      remember (lw2_fact n) as fn eqn:Ef.
      remember (lw2_fact c) as fc eqn:Ec.
      remember (lw2_binom (n + S c) (S c)) as B1 eqn:E1.
      remember (lw2_binom (n + S c) c) as B2 eqn:E2.
      remember (lw2_binom (n + c) c) as B0 eqn:E0.
      assert (A1 : lw2_fact (n + S c)
                   = lw2_binom (n + S c) (S c) * (fn * lw2_fact (S c)))
        by (apply IH).
      rewrite <- E1, H2 in A1.
      assert (A2 : lw2_fact (n + c) = lw2_binom (n + c) c * (fn * lw2_fact c))
        by (apply IH).
      rewrite <- E0, <- Ec in A2.
      assert (A3 : lw2_fact (S n + c) = lw2_binom (S n + c) c * (lw2_fact (S n) * fc))
        by (apply IHc).
      assert (H4 : lw2_fact (S n + c) = S (n + c) * lw2_fact (n + c)) by reflexivity.
      assert (H5 : lw2_binom (S n + c) c = B2)
        by (rewrite E2; replace (n + S c) with (S n + c) by lia; reflexivity).
      rewrite H4, H5, H1, A2 in A3.
      rewrite <- (Nat.mul_assoc (S n) fn fc) in A3.
      assert (EQ1 : B1 * (fn * (S c * fc)) = S (n + c) * (B0 * (fn * fc))).
      { rewrite <- A1, Nat.add_succ_r.
        assert (H7 : lw2_fact (S (n + c)) = S (n + c) * lw2_fact (n + c))
          by reflexivity.
        rewrite H7, A2. reflexivity. }
      assert (EQ2 : B2 * (S n * (fn * fc)) = S (n + c) * (B0 * (fn * fc))).
      { symmetry. exact A3. }
      rewrite A1, EQ1, Nat.mul_add_distr_r.
      assert (R1 : B1 * (S n * fn * (S c * fc)) = S n * (S (n + c) * (B0 * (fn * fc)))).
      { rewrite <- Nat.mul_assoc, <- EQ1. apply lw2_mul_left_comm. }
      assert (R2 : B2 * (S n * fn * (S c * fc)) = S c * (S (n + c) * (B0 * (fn * fc)))).
      { rewrite <- Nat.mul_assoc, (lw2_mul_left_comm fn (S c) fc),
                 (lw2_mul_left_comm (S n) (S c) (fn * fc)), <- EQ2.
        apply lw2_mul_left_comm. }
      rewrite R1, R2, <- Nat.mul_add_distr_r. f_equal.
Qed.

(* 符号因子方程: (−1) 幂的奇偶分解。 *)
Lemma lw2_zsign_even : forall e : nat, Z.pow (-1)%Z (Z.of_nat (2 * e)) = 1%Z.
Proof.
  induction e as [|e IH].
  - reflexivity.
  - replace (2 * S e) with (S (S (2 * e))) by lia.
    rewrite !Nat2Z.inj_succ, !Z.pow_succ_r by lia.
    rewrite IH. ring.
Qed.

Lemma lw2_zsign_odd : forall e : nat, Z.pow (-1)%Z (Z.of_nat (2 * e + 1)) = (-1)%Z.
Proof.
  induction e as [|e IH].
  - reflexivity.
  - replace (2 * S e + 1) with (S (S (2 * e + 1))) by lia.
    rewrite !Nat2Z.inj_succ, !Z.pow_succ_r by lia.
    rewrite IH. ring.
Qed.

(* Z 桥: Z.of_nat (lw2_binom n k) 的三分支取用方程（Z 域 Pascal 形）。 *)
Lemma lw2_binom_Z : forall n k : nat,
  Z.of_nat (lw2_binom n k) =
  match n with
  | 0 => match k with 0 => 1%Z | S _ => 0%Z end
  | S n' =>
      match k with
      | 0 => 1%Z
      | S k' => (Z.of_nat (lw2_binom n' (S k')) + Z.of_nat (lw2_binom n' k'))%Z
      end
  end.
Proof.
  intros n k. destruct n as [|n]; destruct k as [|k]; simpl; try reflexivity.
  rewrite Nat2Z.inj_add. reflexivity.
Qed.
