(* ============================================================ *)
(* 模块名：abl_Pr_euclid_03 —— 素数域成域件单第 3 件（Euclid 无穷素数构造性版：n!+1 路线，最小依赖） *)
(* 使命：①互素核三件——peu_dvd_both_1（k∣a ∧ k∣(a+1) ⟹ k=1，无前提      *)
(*   极简形，nat 三分支：k=0 乘零爆炸／e≤c 乘单调夹挤／e=S c 情形       *)
(*   mul_succ_l 线性即得）；peu_dvd_fact（1≤k≤n ⟹ k∏i n!，n 归纳        *)
(*   两分支：k=S n 直取／k≤n 乘结合律接续）；peu_coprime_core           *)
(*   （1≤k≤n ⟹ Nat.gcd k (n!+1)=1 等式形——gcd 可计算，等式即           *)
(*   构造性出口）。②见证机：peu_next n = n!+1 的最小素因子              *)
(*   （proj1_sig 投影件 1 sigT 接口 pr_min_factor_exists，按件 1        *)
(*   签名适配原形，可计算 Fixpoint 承载）＋正确性双引理；③主定理：      *)
(*   peu_next_gt（n < peu_next n——反设 p≤n 则 p∣n! 与 p∣(n!+1)         *)
(*   夹出 p=1，与 p≥2 矛盾）＋sigT 见证全形 peu_exists_gt：forall       *)
(*   n, {p | n<p /\ pr_prime p}（Defined，可计算见证，非纯存在命题）。  *)
(* 设计依据：素数域成域件单设计文书 §成域件单 ③；互素核三件先行闭合再闭主定理，无接口残留。 *)
(* 依赖清单：件 1 abl_Pr_core_01（pr_prime／pr_min_factor_exists，拷入   *)
(*   本池同编）＋纯 Stdlib（Arith.Arith／Arith.Factorial／List／Bool／   *)
(*   Lia）。factorial 取 stdlib 9.1 Arith.Factorial 在册定义 fact        *)
(*   Fixpoint（O→1，S n→S n*fact n）＋lt_O_fact／fact_le——零自建        *)
(*   （大数行为：unary，烟测实例≤6，n!≤720）。                           *)
(* 构造性注记：Set 面承载——主语句 peu_exists_gt 全 sigT 见证形          *)
(*   （Defined 可提取）；Prop 面谓词 pr_prime 仅作推理脚手架（件 1 同款）；*)
(*   互素核走 gcd 等式形（等式即构造）；否定面全走 exfalso＋lia 爆炸     *)
(*   （本安装无 Not，全件零 not/~/<> 书写）；零公理零承认零经典逻辑；    *)
(*   计算件 peu_next／peu_coprime_core 一阶 nat 可提取；数值定装走       *)
(*   小实例 vm_compute（实例≤6）。                                       *)
(* 编译配方：source <toolchain>/env.sh && unset COQLIB ROCQLIB &&        *)
(*   ulimit -s 65532 && nice -19 rocq c -native-compiler no -Q <池> ""   *)
(*   abl_Pr_core_01.v；再同配方 -Q <池> "" -Q . "" 编本件。               *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith Arith.Factorial List Bool Lia.
Require Import abl_Pr_core_01.

(* ---- §0 factorial 在册性锚（stdlib 9.1 Arith.Factorial 直引） ---- *)

Lemma peu_fact_pos : forall n : nat, 1 <= fact n.
Proof. intros n. apply lt_O_fact. Qed.

Lemma peu_fact1_ge2 : forall n : nat, 2 <= fact n + 1.
Proof. intros n. assert (H := peu_fact_pos n). lia. Qed.

(* ---- §1 互素核三件 ---- *)

(* 核 1：同整除相邻二数者必为 1（k∏a ∧ k∣a+1 ⟹ k=1；无前提极简形） *)
Lemma peu_dvd_both_1 : forall k a : nat,
  Nat.divide k a -> Nat.divide k (a + 1) -> k = 1.
Proof.
  intros k a [c Hc] [e He].
  destruct k as [|k'].
  - rewrite Nat.mul_0_r in Hc, He. exfalso. lia.
  - destruct (le_lt_dec e c) as [Hec|Hce].
    + exfalso.
      assert (Hle : e * (S k') <= c * (S k')).
      { apply Nat.mul_le_mono_r. exact Hec. }
      lia.
    + assert (Hsc : S c * (S k') <= e * (S k')).
      { apply Nat.mul_le_mono_r. lia. }
      rewrite Nat.mul_succ_l in Hsc.
      lia.
Qed.

(* 核 2：k∣i n!（1≤k≤n；n 归纳） *)
Lemma peu_dvd_fact : forall n k : nat,
  1 <= k -> k <= n -> Nat.divide k (fact n).
Proof.
  intros n. induction n as [|n IH]; intros k Hk1 Hkn.
  - exfalso. lia.
  - destruct (Nat.eq_dec k (S n)) as [Heq|Hne].
    + subst k. exists (fact n).
      change (fact (S n)) with (S n * fact n).
      apply Nat.mul_comm.
    + assert (Hkn' : k <= n) by lia.
      destruct (IH k Hk1 Hkn') as [c Hc].
      exists (S n * c).
      change (fact (S n)) with (S n * fact n).
      rewrite Hc.
      apply Nat.mul_assoc.
Qed.

(* 核 3：互素核主件——1≤k≤n ⟹ gcd(k, n!+1)=1（等式形即构造性出口：
   d=gcd ∣k 链 divide_trans 得 d∣i n!，与 d∣n!+1 同入核 1 夹出 d=1） *)
Lemma peu_coprime_core : forall n k : nat,
  1 <= k -> k <= n -> Nat.gcd k (fact n + 1) = 1.
Proof.
  intros n k Hk1 Hkn.
  apply (peu_dvd_both_1 (Nat.gcd k (fact n + 1)) (fact n)).
  - apply (Nat.divide_trans (Nat.gcd k (fact n + 1)) k (fact n)).
    + apply Nat.gcd_divide_l.
    + apply peu_dvd_fact; assumption.
  - apply Nat.gcd_divide_r.
Qed.

(* ---- §2 见证机 peu_next（n!+1 的最小素因子；件 1 sigT 接口投影） ---- *)

Definition peu_next (n : nat) : nat :=
  proj1_sig (pr_min_factor_exists (fact n + 1) (peu_fact1_ge2 n)).

Lemma peu_next_pair : forall n : nat,
  Nat.divide (peu_next n) (fact n + 1) /\ pr_prime (peu_next n).
Proof.
  intros n. unfold peu_next.
  exact (proj2_sig (pr_min_factor_exists (fact n + 1) (peu_fact1_ge2 n))).
Qed.

Theorem peu_next_prime : forall n : nat, pr_prime (peu_next n).
Proof. intros n. destruct (peu_next_pair n) as [_ H]. exact H. Qed.

Theorem peu_next_dvd : forall n : nat,
  Nat.divide (peu_next n) (fact n + 1).
Proof. intros n. destruct (peu_next_pair n) as [H _]. exact H. Qed.

(* ---- §3 主定理：n < peu_next n ＋ sigT 见证全形 ---- *)

Theorem peu_next_gt : forall n : nat, n < peu_next n.
Proof.
  intros n. destruct (le_lt_dec (peu_next n) n) as [Hle|Hgt].
  - exfalso.
    assert (Hp2 : 2 <= peu_next n).
    { destruct (peu_next_prime n) as [Hp2 _]. exact Hp2. }
    assert (HdF : Nat.divide (peu_next n) (fact n)).
    { apply peu_dvd_fact; [lia | exact Hle]. }
    assert (H1 : peu_next n = 1).
    { apply (peu_dvd_both_1 (peu_next n) (fact n)).
      - exact HdF.
      - apply peu_next_dvd. }
    lia.
  - exact Hgt.
Qed.

(* sigT 见证全形：∀n 给可计算见证 p>n 且素（非纯存在命题） *)
Theorem peu_exists_gt : forall n : nat, { p : nat | n < p /\ pr_prime p }.
Proof.
  intros n. exists (peu_next n). split.
  - apply peu_next_gt.
  - apply peu_next_prime.
Defined.

(* ---- §4 互素核数值定装烟测（gcd 等式直算，实例≤6） ---- *)

Lemma peu_coprime_smoke_4 : Nat.gcd 4 (fact 4 + 1) = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma peu_coprime_smoke_5 : Nat.gcd 5 (fact 5 + 1) = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma peu_coprime_smoke_6 : Nat.gcd 6 (fact 6 + 1) = 1.
Proof. vm_compute. reflexivity. Qed.

(* ---- §5 见证机端到端数值定装（穿件 1 sigT 接口直算；补上         *)
(*        「sigT 未做端到端数值验证」的未测面）                     ---- *)

Lemma peu_fact_6 : fact 6 = 720.
Proof. vm_compute. reflexivity. Qed.

Lemma peu_next_1 : peu_next 1 = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma peu_next_2 : peu_next 2 = 3.
Proof. vm_compute. reflexivity. Qed.

Lemma peu_next_3 : peu_next 3 = 7.
Proof. vm_compute. reflexivity. Qed.

Lemma peu_next_4 : peu_next 4 = 5.
Proof. vm_compute. reflexivity. Qed.

Lemma peu_next_5 : peu_next 5 = 11.
Proof. vm_compute. reflexivity. Qed.

Lemma peu_next_6 : peu_next 6 = 7.
Proof. vm_compute. reflexivity. Qed.

(* ---- §7 公理审计（Print Assumptions 取证面） ---- *)

Print Assumptions peu_dvd_both_1.
Print Assumptions peu_dvd_fact.
Print Assumptions peu_coprime_core.
Print Assumptions peu_next_dvd.
Print Assumptions peu_next_prime.
Print Assumptions peu_next_gt.
Print Assumptions peu_exists_gt.
