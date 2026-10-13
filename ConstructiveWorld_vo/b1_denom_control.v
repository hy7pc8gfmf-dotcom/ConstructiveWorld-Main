(* 模块：b1_denom_control.v —— 线性形式分母双控（奇清分母层）。
   使命：Beukers-arctan 线性形式的分母双控原语：
     ①双阶乘承载 dfact_odd(n) = 1·3···(2n−1)、dfact_even(n) = 2·4···(2n)；
     ②偶档 2ⁿ·n! 读形（dfact_even = 2ⁿ·n!）；
     ③奇 ≤ 偶 逐档支配（NatLe Set 形）——中心二项折叠 C(2n,n) ≤ 4ⁿ 的
       nat 侧承重（Q 侧 Beta ≤ 1 衰减肢已由件③ b1_seg_beta_le1 经
       pei_fact_le 承载，两件互为表里，零重复）；
     ④奇清分母见证（sigT 乘子见证形）：k ≤ n ⟹ ∃q, q·(2k+1) = dfact_odd(S n)
       ——奇数分母对 (2n+1)!! 的整除性，全构造见证（可提取）；
     ⑤dfact_odd ≥ 1 正性。
   Hanson 全强度链（lcm ≤ 3ⁿ，abl_z2_dub3/valbridge 谱系）另行直用登记
   （HansonLcm 闭包不在本件依赖内，直用件归后续装配面）。
   依赖：S01_BaseRing（Id/NatLe 承载与升降桥）；Stdlib Arith/Lia。
   构造性：主语句面全 Set（sigT 乘子见证＋Id／NatLe）；证明体 n-归纳直链；
   零公理、零经典逻辑。
   编译配方：source Live/toolchain/env.sh 后经 cpu_guard 包裹
   rocq c -native-compiler no -q -Q . "" b1_denom_control.v。 *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Arith.Factorial Lia.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing.

Open Scope nat_scope.

(* ========== §1 双阶乘承载 ========== *)

Fixpoint b1_dfact_odd (n : nat) : nat :=
  match n with
  | O => 1
  | Datatypes.S k => (2 * k + 1) * b1_dfact_odd k
  end.

Fixpoint b1_dfact_even (n : nat) : nat :=
  match n with
  | O => 1
  | Datatypes.S k => (2 * Datatypes.S k) * b1_dfact_even k
  end.

(* 偶档 2ⁿ·n! 读形 *)
Theorem b1_dfact_even_pow : forall n : nat,
  b1_dfact_even n = (2 ^ n) * (fact n).
Proof.
  induction n as [| k IH].
  - reflexivity.
  - cbn [b1_dfact_even fact].
    rewrite IH. rewrite Nat.pow_succ_r'.
    ring.
Qed.

(* 奇档逐项：dfact_odd(S k) = (2k+1)·dfact_odd(k)（定义性读形） *)
Lemma b1_dfact_odd_unfold : forall k : nat,
  b1_dfact_odd (Datatypes.S k) = (2 * k + 1) * b1_dfact_odd k.
Proof. intros k. reflexivity. Qed.

(* ========== §2 奇 ≤ 偶 逐档支配（中心二项 nat 侧承重） ========== *)

Theorem b1_dfact_odd_le_even : forall n : nat,
  NatLe (b1_dfact_odd n) (b1_dfact_even n).
Proof.
  induction n as [| k IH].
  - exact id_refl.
  - apply NatLe_lift.
    apply (Nat.le_trans ((2 * k + 1) * b1_dfact_odd k)
                        ((2 * k + 1) * b1_dfact_even k)
                        ((2 * Datatypes.S k) * b1_dfact_even k)).
    + apply NatLe_drop in IH. apply Nat.mul_le_mono_l. exact IH.
    + replace (2 * Datatypes.S k)%nat with (2 * k + 2)%nat by lia.
      apply Nat.mul_le_mono_r. lia.
Qed.

(* dfact_odd ≥ 1 正性 *)
Theorem b1_dfact_odd_pos : forall n : nat, NatLe 1 (b1_dfact_odd n).
Proof.
  induction n as [| k IH].
  - exact id_refl.
  - apply NatLe_lift.
    apply (Nat.le_trans 1 (1 * b1_dfact_odd k) ((2 * k + 1) * b1_dfact_odd k)).
    + replace (1 * b1_dfact_odd k) with (b1_dfact_odd k) by lia.
      apply NatLe_drop. exact IH.
    + apply Nat.mul_le_mono_r. lia.
Qed.

(* ========== §3 奇清分母见证（sigT 乘子见证形，全构造可提取） ========== *)

(* k ≤ n ⟹ ∃q, q·(2k+1) = dfact_odd(S n)：奇数分母 2k+1 对 (2n+1)!! 整除 *)
Theorem b1_odd_div_dfact : forall (n k : nat), (k <= n)%nat ->
  sigT (fun q : nat => Id (q * (2 * k + 1)) (b1_dfact_odd (Datatypes.S n))).
Proof.
  intros n. induction n as [| n' IHn]; intros k Hk.
  - (* n = 0：k = 0，见证 1 *)
    assert (Hk0 : k = 0%nat) by lia.
    rewrite Hk0. exists 1%nat. reflexivity.
  - (* n = S n'：k = S n' 顶因子档；k ≤ n' 传递档 *)
    destruct (Nat.eq_dec k (Datatypes.S n')) as [Hke | Hkle].
    + rewrite Hke.
      exists (b1_dfact_odd (Datatypes.S n'))%nat.
      rewrite (Nat.mul_comm (b1_dfact_odd (Datatypes.S n'))
                            (2 * Datatypes.S n' + 1)).
      reflexivity.
    + assert (Hk' : (k <= n')%nat) by lia.
      destruct (IHn k Hk') as [q Hq].
      exists ((2 * Datatypes.S n' + 1) * q)%nat.
      apply (@Id_rec nat (q * (2 * k + 1))
               (fun d _ => Id (((2 * Datatypes.S n' + 1) * q) * (2 * k + 1))
                             ((2 * Datatypes.S n' + 1) * d))).
      * rewrite (Nat.mul_assoc (2 * Datatypes.S n' + 1) q (2 * k + 1)).
        apply id_refl.
      * exact Hq.
Qed.

(* ========== §4 数值锚（独立复算比对点） ========== *)

(* 锚一：dfact_odd(4) = 1·3·5·7 = 105 *)
Lemma b1_dfact_odd_anchor : Id (b1_dfact_odd 4) 105.
Proof. reflexivity. Qed.

(* 锚二：dfact_even(4) = 2·4·6·8 = 384 = 2⁴·4! *)
Lemma b1_dfact_even_anchor : Id (b1_dfact_even 4) 384.
Proof. reflexivity. Qed.

(* 锚三：奇清见证实例：15·7 = 105（k=3, n=3） *)
Lemma b1_odd_div_anchor :
  sigT (fun q : nat => Id (q * 7) (b1_dfact_odd 4)).
Proof. exists 15%nat. reflexivity. Qed.

(* 锚四：支配实例：105 ≤ 384 *)
Lemma b1_dfact_le_anchor : NatLe (b1_dfact_odd 4) (b1_dfact_even 4).
Proof. exact id_refl. Qed.

(* ========== §5 在件检验与假设审计 ========== *)

Check b1_dfact_even_pow.
Check b1_dfact_odd_le_even.
Check b1_dfact_odd_pos.
Check b1_odd_div_dfact.
Check b1_dfact_odd_anchor.

Print Assumptions b1_dfact_even_pow.
Print Assumptions b1_dfact_odd_le_even.
Print Assumptions b1_dfact_odd_pos.
Print Assumptions b1_odd_div_dfact.
