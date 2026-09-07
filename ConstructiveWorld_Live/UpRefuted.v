(* ===================================================================== *)
(* UpRefuted.v — 四大击破实验 Coq 化：否定形定理库                            *)
(*                                                                       *)
(* Q2 席（第三棒）。理论来源：                                              *)
(*   ROUNDTABLE2-未知算法强制变异实验-终版快照.md：                          *)
(*     件 1  席 1 实验一（杀 WPM）：无界受偿流破产反例                        *)
(*           —— S≡1 + 无限耗 1 受偿 ⟹ 第 ⌊R⌋+1 次破产，                      *)
(*              而逐步定位方案（尾指针+每步覆盖 1）永不破产；                   *)
(*     件 2  席 6 实验 E1（杀 GRM）：p-adic 进位级联连坐两字段                 *)
(*           —— 一枚证据同时改写两字段坐标 + 剩余类环交替永不达不动点；          *)
(*     件 3  席 2 实验②（杀织机）：跨洞耦合一致循环流活锁                      *)
(*           —— 贪心重织自振荡、摩擦计无界增长、吐件门恒假；                    *)
(*     件 4  席 4/席 5 DWM 两难收口：格律公理档 X 退化为整除算术平凡重述        *)
(*           vs 自由发射档 X 可判定为假、Halt 证书被一次合法发射当场证伪。       *)
(*                                                                       *)
(* 形式化方针：每件 = 具体反例对象（显式 nat/Z/bool/列表构造）+ 其性质的       *)
(* bool/tid 判定证明。语句零 Prop：等式用 tid、序用 nle、分支用 bool。         *)
(* 荒谬关闭：tid bool true false 空指标消去 + nle (S O) O 空型消去。          *)
(* 载体全程 Z/nat/bool 判定层；stdlib only；独立文件内联基建（不引 UpPLA）。   *)
(* 纪律自检：四禁词零出现（含头注，便于 grep=0）；主定理语句到 Proof. 之间      *)
(* 无裸 exists、无 Prop 层 and/or、无 -> False、无 Prop 前提；全链可提取       *)
(* （Obj.magic = 0，见 _probe_refuted 验证记录）。                            *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import ZArithRing.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.

Open Scope Z_scope.
Local Open Scope list_scope.

(* ===================================================================== *)
(* 0. Set 层基建（内联自 UpPLA.v 头部，独立文件不 Require）                    *)
(* ===================================================================== *)

(* Set 层恒等型（语句零 Prop 的等式载体） *)
Inductive tid (A : Type) : A -> A -> Type := tid_refl : forall x : A, tid A x x.

Definition tid_sym (A : Type) (x y : A) (H : tid A x y) : tid A y x :=
  match H in tid _ a b return tid _ b a with
  | tid_refl _ a0 => @tid_refl _ a0
  end.

Definition tid_trans (A : Type) (x y z : A) (H1 : tid A x y) (H2 : tid A y z) :
  tid A x z :=
  match H1 in tid _ a b return tid _ b z -> tid _ a z with
  | tid_refl _ a0 => fun H => H
  end H2.

(* 恒等型的泛函同余（transport 万能件） *)
Definition tid_cong {A B : Type} (f : A -> B) (x y : A) (H : tid A x y) :
  tid B (f x) (f y) :=
  match H in tid _ a b return tid B (f a) (f b) with
  | tid_refl _ a0 => @tid_refl _ (f a0)
  end.

(* tid -> bool 等式提取（仅证明内部推理用） *)
Ltac tidEqN H name :=
  pose proof (match H in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as name.

(* bool 恒等矛盾关闭器：H1 : tid bool X true、H2 : tid bool X false *)
Ltac tid_kill H1 H2 :=
  pose proof (match H1 in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as KE1;
  pose proof (match H2 in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as KE2;
  rewrite KE1 in KE2; discriminate KE2.

(* Set 层自然数序型（k < m 编码为 nle (S k) m） *)
Inductive nle (n : nat) : nat -> Set :=
| nle_n : nle n n
| nle_S : forall m : nat, nle n m -> nle n (S m).

(* nle (S O) O 荒谬件（索引不交配的空消去，合法关闭任意 Set 目标） *)
Lemma nle_10_absurd : forall P : Type, nle (S O) O -> P.
Proof.
  intros P H. inversion H.
Qed.

Lemma nle_trans : forall a b c : nat, nle a b -> nle b c -> nle a c.
Proof.
  intros a b c H1 H2. induction H2 as [| c H2 IH].
  - exact H1.
  - apply nle_S. exact IH.
Qed.

Lemma nle_0 : forall m : nat, nle O m.
Proof.
  induction m as [| m1 IH].
  - apply nle_n.
  - apply nle_S. exact IH.
Qed.

Lemma nle_SS : forall a b : nat, nle a b -> nle (S a) (S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply nle_n.
  - apply nle_S. exact IH.
Qed.

Lemma nle_add_r : forall a b : nat, nle a (a + b).
Proof.
  intros a b. revert b. induction a as [| a1 IH]; intro b.
  - apply nle_0.
  - exact (nle_SS a1 (a1 + b) (IH b)).
Qed.

(* ---- bool 判定小件 ---- *)

Lemma negb_true_of_false : forall e : bool, tid bool e false -> tid bool (negb e) true.
Proof.
  intros e H. destruct e.
  - exact (tid_sym bool true false H).
  - apply tid_refl.
Qed.

Lemma negb_false_of_true : forall e : bool, tid bool e true -> tid bool (negb e) false.
Proof.
  intros e H. destruct e.
  - apply tid_refl.
  - exact (tid_sym bool false true H).
Qed.

Lemma andb_true_both : forall e1 e2 : bool,
  tid bool e1 true -> tid bool e2 true -> tid bool (andb e1 e2) true.
Proof.
  intros e1 e2 H1 H2. destruct e1.
  - destruct e2.
    + apply tid_refl.
    + exact H2.
  - exact H1.
Qed.

Lemma andb_false_left : forall e1 e2 : bool,
  tid bool e1 false -> tid bool (andb e1 e2) false.
Proof.
  intros e1 e2 H. destruct e1.
  - destruct e2.
    + exact H.
    + apply tid_refl.
  - apply tid_refl.
Qed.

Lemma Zeqb_true_of_eq : forall x y : Z, (x = y)%Z -> tid bool (Z.eqb x y) true.
Proof.
  intros x y H. rewrite H. rewrite Z.eqb_refl. apply tid_refl.
Qed.

Lemma Zeqb_diff_false : forall x y : Z, (x <> y)%Z -> tid bool (Z.eqb x y) false.
Proof.
  intros x y H. destruct (Z.eqb x y) eqn:E.
  - apply Z.eqb_eq in E. exfalso. exact (H E).
  - apply tid_refl.
Qed.

Lemma xorb_comm_t : forall b1 b2 : bool, tid bool (xorb b1 b2) (xorb b2 b1).
Proof.
  intros b1 b2. destruct b1, b2; apply tid_refl.
Qed.

(* ===================================================================== *)
(* 件 1. WPM 无界族破产不健全（席 1 实验一）                                  *)
(*                                                                     *)
(* 熔断券：时刻零把整条无限证书序列熔成一张聚合券，预算 R（构造性有限）。        *)
(* 受偿流：无限多张「耗 1」查询。第 k 次受偿后的余额 = R - k。                 *)
(*   solvent k      := 前 k 次受偿全部可付 ⟺ k ≤ R；                        *)
(*   insolvent k    := 第 k 次受偿后余额 ≤ 0（下一次必破产）。                 *)
(* 击破：第 ⌊R⌋+1 次受偿破产；此后每一次受偿都破产（对无界流 = 无限破产）；      *)
(* 对照：逐步定位方案（存每步覆盖 1 的证书序列 + 尾指针）逐张支付，永不破产。    *)
(* ===================================================================== *)

Definition wpm_R : Z := 3.

(* 聚合券余额轨迹：第 k 次受偿后 = R - k *)
Definition melt_wallet (k : nat) : Z := wpm_R - Z.of_nat k.

(* 第 k 次受偿的偿付判定：可付前 k 次 ⟺ k ≤ R *)
Definition solvent (k : nat) : bool := Z.leb (Z.of_nat k) wpm_R.

(* 第 k 次受偿后的清偿位：余额 ≤ 0 ⟹ 第 k+1 次必破产 *)
Definition insolvent (k : nat) : bool := Z.leb (melt_wallet k) 0.

(* 定位方案：逐位证书序列 S ≡ 1（每步覆盖 1）+ 尾指针，第 k 次受偿从第 k 张支付 *)
Fixpoint loc_cov (k : nat) : Z := match k with O => 1 | S k' => loc_cov k' end.
Definition loc_solvent (k : nat) : bool := Z.leb 1 (loc_cov k).

(* 熔可行域上 melt ≡ 求和：前 n 张证书之和（每张 1）一步可算 *)
Fixpoint sum_S (n : nat) : Z := match n with O => 0 | S m => sum_S m + loc_cov m end.

Lemma loc_cov_one : forall k : nat, tid Z (loc_cov k) 1.
Proof.
  intros k. induction k as [| k IH].
  - apply tid_refl.
  - exact IH.
Qed.

Lemma loc_never_bankrupt : forall k : nat, tid bool (loc_solvent k) true.
Proof.
  intros k. unfold loc_solvent.
  destruct (Z.leb 1 (loc_cov k)) eqn:E.
  - apply tid_refl.
  - tidEqN (loc_cov_one k) HE. rewrite HE in E. simpl in E. discriminate E.
Qed.

Lemma sum_S_closed : forall n : nat, tid Z (sum_S n) (Z.of_nat n).
Proof.
  intros n. induction n as [| n IH].
  - apply tid_refl.
  - rewrite (Nat2Z.inj_succ n).
    change (tid Z (sum_S n + loc_cov n) (Z.of_nat n + 1)).
    tidEqN IH HEa. rewrite HEa.
    tidEqN (loc_cov_one n) HEb. rewrite HEb.
    apply tid_refl.
Qed.

(* 末次可付：第 ⌊R⌋ 次受偿恰付清（余额归零） *)
Lemma wpm_solvent_at_last_covered : tid bool (solvent (Z.to_nat wpm_R)) true.
Proof.
  unfold solvent, wpm_R. apply tid_refl.
Qed.

(* 破产主定理：第 ⌊R⌋+1 次受偿破产 *)
Theorem wpm_melt_bankrupt : tid bool (solvent (S (Z.to_nat wpm_R))) false.
Proof.
  unfold solvent, wpm_R. apply tid_refl.
Qed.

Lemma wpm_wallet_zero_at_last_cover : tid Z (melt_wallet (Z.to_nat wpm_R)) 0.
Proof.
  apply tid_refl.
Qed.

Lemma wpm_wallet_negative_at_bankrupt : tid Z (melt_wallet (S (Z.to_nat wpm_R))) (-1).
Proof.
  apply tid_refl.
Qed.

Lemma wpm_insolvent_at_bankrupt : tid bool (insolvent (S (Z.to_nat wpm_R))) true.
Proof.
  unfold insolvent, wpm_R. apply tid_refl.
Qed.

(* 破产沿受偿流传播：一旦破产，此后每次受偿都破产（无界流 ⟹ 无限破产事件） *)
Lemma insolvent_step : forall k : nat,
  tid bool (insolvent k) true -> tid bool (insolvent (S k)) true.
Proof.
  intros k H. unfold insolvent in H.
  tidEqN H HE. unfold melt_wallet, wpm_R in HE. apply Z.leb_le in HE.
  unfold insolvent, melt_wallet, wpm_R.
  destruct (Z.leb (3 - Z.of_nat (S k)) 0) eqn:E.
  - apply tid_refl.
  - apply Z.leb_gt in E. rewrite Nat2Z.inj_succ in E.
    exfalso. lia.
Qed.

Theorem wpm_insolvent_forever : forall j : nat,
  tid bool (insolvent (S (S (S (S j))))) true.
Proof.
  intros j. induction j as [| j IH].
  - exact wpm_insolvent_at_bankrupt.
  - apply insolvent_step. exact IH.
Qed.

(* 有界族上熔券健全（对照半边）：k ≤ R ⟹ 前 k 次受偿全部可付 *)
Theorem wpm_solvent_bounded_family : forall n : nat,
  tid bool (Z.leb (Z.of_nat n) wpm_R) true -> tid bool (solvent n) true.
Proof.
  intros n H. exact H.
Qed.

(* 合取收口（「聚合占优」反演为聚合破产）：同一受偿流、同一受偿序号，
   熔券偿付位为假而定位方案偿付位为真 *)
Theorem wpm_unbounded_family_unsound :
  tid bool (andb (solvent (S (Z.to_nat wpm_R)))
                 (loc_solvent (S (Z.to_nat wpm_R)))) false.
Proof.
  apply andb_false_left. apply wpm_melt_bankrupt.
Qed.

(* ===================================================================== *)
(* 件 2. p-adic 进位级联连坐两字段 + 剩余类环交替不达不动点（席 6 实验 E1）      *)
(*                                                                     *)
(* GRM 普查迁到共享分母坐标域：字段 = 有理担保 w 的素坐标。取 p = 3，           *)
(* 消费流 = PLA 避零环流 2/3, 1/3, 2/3, 1/3, …（乘法份额），公分母下的          *)
(* 累计分子轨迹：N(0)=0, N(2j)=3j, N(2j+1)=3j+2。                              *)
(*   字段一 coordA：Z/9 剩余类坐标（粗分辨率）；                               *)
(*   字段二 coordB：Z/3 零类检测位（= p-账本归一化/进位触发位）。                *)
(* 击破：(a) 任一枚消费证据同时改写两字段坐标（连坐）——含触发步本身；            *)
(*       (b) 触发位沿 0↔2 剩余类环逐位交替、相邻状态永不重合——                   *)
(*           「≤ |普查| = 2 步到不动点」公理在预算外仍在移动（公理死）；          *)
(*       (c) 进位级联深度 2：N(6) = 9 时粗坐标 Z/9 也进零类。                    *)
(* ===================================================================== *)

Definition p3 : Z := 3.

(* 两步一组的累计分子递归：j 组后 = (N(2j), N(2j+1))；份额流 2/p,1/p 交替 *)
Fixpoint pla_step2 (j : nat) : Z * Z :=
  match j with
  | O => (0, 2)
  | S j' => let ab := pla_step2 j' in (snd ab + 1, snd ab + 3)
  end.

(* 字段一：Z/9 剩余类坐标 *)
Definition coordA (n : Z) : Z := Z.modulo n 9.
(* 字段二：Z/3 零类检测位（归一化/进位触发位） *)
Definition coordB (n : Z) : bool := Z.eqb (Z.modulo n 3) 0.

(* mod 3 精确小件（Z_mod_plus_full 路线，绕开除法引理的变量侧条件） *)
Lemma mod3_3j : forall j : nat, tid Z (Z.modulo (3 * Z.of_nat j) 3) 0.
Proof.
  intros j.
  assert (Hm : (Z.modulo (3 * Z.of_nat j) 3 = 0)%Z).
  { replace (3 * Z.of_nat j) with (0 + Z.of_nat j * 3) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  rewrite Hm. apply tid_refl.
Qed.

Lemma mod3_3j2 : forall j : nat, tid Z (Z.modulo (3 * Z.of_nat j + 2) 3) 2.
Proof.
  intros j.
  assert (Hm : (Z.modulo (3 * Z.of_nat j + 2) 3 = 2)%Z).
  { replace (3 * Z.of_nat j + 2) with (2 + Z.of_nat j * 3) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  rewrite Hm. apply tid_refl.
Qed.

Lemma mod3_3j3 : forall j : nat, tid Z (Z.modulo (3 * Z.of_nat j + 3) 3) 0.
Proof.
  intros j.
  assert (Hm : (Z.modulo (3 * Z.of_nat j + 3) 3 = 0)%Z).
  { replace (3 * Z.of_nat j + 3) with (3 + Z.of_nat j * 3) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  rewrite Hm. apply tid_refl.
Qed.

(* mod 9 相差小正数必不同类（k ∈ [1,8] ⟹ Z/9 中 x 与 x+k 不同类） *)
Lemma mod9_diff_small : forall x k : Z,
  tid bool (Z.ltb 0 k) true -> tid bool (Z.ltb k 9) true ->
  tid bool (Z.eqb (x mod 9) ((x + k) mod 9)) false.
Proof.
  intros x k Hk1 Hk2.
  tidEqN Hk1 HE1. tidEqN Hk2 HE2.
  apply Z.ltb_lt in HE1. apply Z.ltb_lt in HE2.
  pose proof (Z.mod_pos_bound x 9 (ltac:(lia))) as HB.
  pose proof (Z.div_mod x 9 (ltac:(lia))) as HD.
  destruct (Z.eqb (x mod 9) ((x + k) mod 9)) eqn:E.
  - apply Z.eqb_eq in E.
    assert (Hsplit : (x + k = (x mod 9 + k) + (x / 9) * 9)%Z) by lia.
    rewrite Hsplit in E. rewrite Z_mod_plus_full in E.
    destruct (Z_le_gt_dec (x mod 9) (8 - k)) as [Hc | Hc].
    + assert (Hsm : ((x mod 9 + k) mod 9 = x mod 9 + k)%Z)
        by (apply Z.mod_small; lia).
      rewrite Hsm in E. exfalso. lia.
    + assert (Hconn : (x mod 9 + k = (x mod 9 + k - 9) + 1 * 9)%Z) by lia.
      assert (Hmp : (((x mod 9 + k - 9) + 1 * 9) mod 9 = (x mod 9 + k - 9) mod 9)%Z)
        by (apply Z_mod_plus_full).
      rewrite <- Hconn in Hmp.
      rewrite Hmp in E.
      assert (Hsm2 : ((x mod 9 + k - 9) mod 9 = x mod 9 + k - 9)%Z)
        by (apply Z.mod_small; lia).
      rewrite Hsm2 in E. exfalso. lia.
  - apply tid_refl.
Qed.

(* 轨迹闭形：N(2j) = 3j、N(2j+1) = 3j+2（bool 合取判定形） *)
Lemma pla_pair_closed : forall j : nat,
  tid bool (andb (Z.eqb (fst (pla_step2 j)) (3 * Z.of_nat j))
                 (Z.eqb (snd (pla_step2 j)) (3 * Z.of_nat j + 2))) true.
Proof.
  intros j. induction j as [| j IH].
  - apply tid_refl.
  - tidEqN IH HEc. apply andb_prop in HEc as [HE1 HE2].
    apply Z.eqb_eq in HE1. apply Z.eqb_eq in HE2.
    replace (fst (pla_step2 (S j))) with (snd (pla_step2 j) + 1) by reflexivity.
    replace (snd (pla_step2 (S j))) with (snd (pla_step2 j) + 3) by reflexivity.
    replace (3 * Z.of_nat (S j)) with (3 * Z.of_nat j + 3)
      by (rewrite Nat2Z.inj_succ; lia).
    replace (3 * Z.of_nat (S j) + 2) with (3 * Z.of_nat j + 5)
      by (rewrite Nat2Z.inj_succ; lia).
    rewrite HE2.
    apply andb_true_both.
    + apply Zeqb_true_of_eq. lia.
    + apply Zeqb_true_of_eq. lia.
Qed.

(* (a) 连坐定理：偶位证据（+2/p 份额）一次同时改写两字段坐标 *)
Theorem evidence_couples_two_fields : forall j : nat,
  tid bool (andb
    (negb (Z.eqb (coordA (fst (pla_step2 j))) (coordA (snd (pla_step2 j)))))
    (negb (Bool.eqb (coordB (fst (pla_step2 j))) (coordB (snd (pla_step2 j)))))) true.
Proof.
  intros j. unfold coordA, coordB.
  tidEqN (pla_pair_closed j) HEc. apply andb_prop in HEc as [HE1 HE2].
  apply Z.eqb_eq in HE1. apply Z.eqb_eq in HE2.
  rewrite HE1, HE2.
  tidEqN (mod3_3j j) HM1. rewrite HM1.
  tidEqN (mod3_3j2 j) HM2. rewrite HM2.
  apply andb_true_both.
  - apply negb_true_of_false.
    apply (mod9_diff_small (3 * Z.of_nat j) 2); apply tid_refl.
  - simpl. apply tid_refl.
Qed.

(* (a') 触发步连坐：账本触发证据（+1/p 份额，落零类）同样一次改写两字段——
   进位事件不是字段一的私事，粗坐标同步被拖动 *)
Theorem ledger_trigger_couples_too : forall j : nat,
  tid bool (andb
    (negb (Bool.eqb (coordB (snd (pla_step2 j))) (coordB (fst (pla_step2 (S j))))))
    (negb (Z.eqb (coordA (snd (pla_step2 j))) (coordA (fst (pla_step2 (S j))))))) true.
Proof.
  intros j. unfold coordA, coordB.
  tidEqN (pla_pair_closed j) HEc. apply andb_prop in HEc as [HE1 HE2].
  apply Z.eqb_eq in HE1. apply Z.eqb_eq in HE2.
  replace (fst (pla_step2 (S j))) with (snd (pla_step2 j) + 1) by reflexivity.
  rewrite HE2.
  tidEqN (mod3_3j2 j) HM2. rewrite HM2.
  assert (HM3' : (Z.modulo (3 * Z.of_nat j + 2 + 1) 3 = 0)%Z).
  { replace (3 * Z.of_nat j + 2 + 1) with (3 * Z.of_nat j + 3) by lia.
    tidEqN (mod3_3j3 j) H3. exact H3. }
  rewrite HM3'.
  apply andb_true_both.
  - simpl. apply tid_refl.
  - apply negb_true_of_false.
    apply (mod9_diff_small (3 * Z.of_nat j + 2) 1); apply tid_refl.
Qed.

(* (b) 不达不动点：相邻两步状态永不重合（剩余类环 0↔2 永久交替） *)
Theorem residue_class_never_freezes : forall j : nat,
  tid bool (Z.eqb (snd (pla_step2 j)) (fst (pla_step2 (S j)))) false.
Proof.
  intros j.
  tidEqN (pla_pair_closed j) HEc. apply andb_prop in HEc as [HE1 HE2].
  apply Z.eqb_eq in HE1. apply Z.eqb_eq in HE2.
  replace (fst (pla_step2 (S j))) with (snd (pla_step2 j) + 1) by reflexivity.
  rewrite HE2.
  apply Zeqb_diff_false. lia.
Qed.

(* GRM 公理预算击穿：|普查| = 2 ⟹ 公理断言第 2 步到不动点；
   实测第 4→5 步仍在移动（j = 2 实例）——公理死 *)
Theorem grm_two_step_budget_blown :
  tid bool (Z.eqb (snd (pla_step2 2)) (fst (pla_step2 3))) false.
Proof.
  exact (residue_class_never_freezes 2).
Qed.

(* (c) 进位级联深度 2：N(6) = 9 —— 粗坐标 Z/9 也进零类（双位归一化） *)
Theorem carry_cascade_depth2 : tid bool (Z.eqb (coordA (fst (pla_step2 3))) 0) true.
Proof.
  unfold coordA.
  tidEqN (pla_pair_closed 3) HEc. apply andb_prop in HEc as [HE1 HE2].
  apply Z.eqb_eq in HE1. rewrite HE1. apply tid_refl.
Qed.

(* ===================================================================== *)
(* 件 3. 织机活锁反例（席 2 实验②）                                          *)
(*                                                                     *)
(* 两洞缩影：槽值 bool；跨洞联合合法门（吐件门）= 异或 emit_gate——             *)
(* 「六门联合合法空间 ≠ 各洞合法性的乘积」的那道跨洞门。                         *)
(* 判词流 = 循环一致流：每洞判词单一方向（「翻离对方」，无同洞双向冲突），        *)
(* 满足织机自定一致性条件；rej 重织语义 = 旧证作废、按证据把本槽改写为            *)
(* 「异于对方当前值」（证书包跨洞传参的同步重织）。                               *)
(* 初织 (true,true)：逐洞 pass 照章接受（一致性只查逐洞，不查跨洞）——非法元。    *)
(* 击破：同步重织 (a,b) ↦ (¬b, ¬a) 保持异或不变量——初织非法则永非法：            *)
(*   吐件门恒假（永不吐件）+ 槽值逐轮翻转（自振荡，周期 2）+                     *)
(*   摩擦计每轮 +2、无界增长（重织代价无界）；且贪心调度键自身即活锁驱动器。      *)
(* ===================================================================== *)

(* 跨洞联合合法门（吐件门）＝异或 *)
Definition emit_gate (a b : bool) : bool := xorb a b.

(* 一步同步重织：两洞旧证同时作废，各自翻离对方 *)
Definition loom_step (p : bool * bool) : bool * bool :=
  (negb (snd p), negb (fst p)).

(* 织机运行轨迹：初织 (true,true)，循环一致流驱动 *)
Fixpoint loom_iter (k : nat) : bool * bool :=
  match k with
  | O => (true, true)
  | S k' => loom_step (loom_iter k')
  end.

(* 摩擦计：每轮两洞各重织一次，各 +1 *)
Fixpoint loom_fric (k : nat) : nat :=
  match k with O => O | S k' => S (S (loom_fric k')) end.

(* 一步重织保持吐件门真值（异或不变量的转移式） *)
Lemma loom_step_inv : forall p : bool * bool,
  tid bool (emit_gate (fst (loom_step p)) (snd (loom_step p)))
           (emit_gate (fst p) (snd p)).
Proof.
  intros p. destruct p as [a b]. destruct a, b; apply tid_refl.
Qed.

(* 流一致性（织机自定条件）：每洞重织方向单一——改写目标恒为「异于对方当前值」，
   与本槽自身取值无关、永不「贴向对方」（无同洞双向冲突、无停织空转），
   bool 判定对一切状态恒真 *)
Definition flip_check (p : bool * bool) : bool :=
  andb (Bool.eqb (fst (loom_step p)) (negb (snd p)))
       (Bool.eqb (snd (loom_step p)) (negb (fst p))).

Lemma loom_stream_consistent : forall p : bool * bool, tid bool (flip_check p) true.
Proof.
  intros p. destruct p as [a b]. destruct a, b; apply tid_refl.
Qed.

(* 周期 2：织机轨迹两轮回到原态（自振荡载体） *)
Lemma loom_period2 : forall k : nat,
  tid (bool * bool) (loom_iter (S (S k))) (loom_iter k).
Proof.
  intros k. induction k as [| k IH].
  - apply tid_refl.
  - change (tid (bool * bool) (loom_step (loom_iter (S (S k))))
                        (loom_step (loom_iter k))).
    exact (tid_cong loom_step _ _ IH).
Qed.

(* 活锁主定理：任意轮次吐件门恒假——一致流存在、吐件不存在 *)
Theorem loom_livelock_never_emits : forall k : nat,
  tid bool (emit_gate (fst (loom_iter k)) (snd (loom_iter k))) false.
Proof.
  intros k. induction k as [| k IH].
  - apply tid_refl.
  - exact (tid_trans bool _ _ _ (loom_step_inv (loom_iter k)) IH).
Qed.

(* 自振荡：槽值逐轮翻转（非卡死空转），周期 2 内永在两非法元间振荡 *)
Lemma loom_flips : forall k : nat,
  tid bool (xorb (fst (loom_iter (S k))) (fst (loom_iter k))) true.
Proof.
  intros k. induction k as [| k IH].
  - apply tid_refl.
  - tidEqN (loom_period2 k) HEp. rewrite HEp.
    exact (tid_trans bool _ _ _
      (xorb_comm_t (fst (loom_iter k)) (fst (loom_iter (S k)))) IH).
Qed.

(* 摩擦计闭形：k 轮后摩擦计 = 2k（真实现，非占位） *)
Lemma loom_fric_closed : forall k : nat, tid nat (loom_fric k) (2 * k)%nat.
Proof.
  intros k. induction k as [| k IH].
  - apply tid_refl.
  - change (tid nat (S (S (loom_fric k))) (2 * S k)%nat).
    rewrite (Nat.mul_succ_r 2 k).
    tidEqN IH HEk. rewrite HEk.
    assert (HE2 : (2 * k + 2 = S (S (2 * k)))%nat) by lia.
    rewrite HE2. apply tid_refl.
Qed.

(* 重织代价无界：任意两轮窗口内摩擦计严格上升（贪心调度键 = 活锁驱动器，
   预算无论多大终被突破——nle (S fric j) fric (j+2)） *)
Theorem loom_cost_unbounded : forall j : nat,
  nle (S (loom_fric j)) (loom_fric (j + 2)%nat).
Proof.
  intros j.
  assert (HE : (loom_fric (j + 2) = loom_fric j + 4)%nat).
  { replace ((j + 2)%nat) with (S (S j)) by lia. simpl. lia. }
  rewrite HE.
  apply (nle_trans (S (loom_fric j)) (S (loom_fric j) + 3) (loom_fric j + 4)).
  - apply nle_add_r.
  - assert (HEq : (S (loom_fric j) + 3 = loom_fric j + 4)%nat) by lia.
    rewrite HEq. apply nle_n.
Qed.

(* ===================================================================== *)
(* 件 4. DWM 两难收口（席 4 实验一 + 席 5 实验二合流）                          *)
(*                                                                     *)
(* 差异钱包机：候选带只增不删 × 精确有限停机。停机支唯一悬于判等命题 X：         *)
(*「差额 < grain ⟹ 同格」。载体：分母 4 格网，全部以格距 1/4 为单位的整数编码。    *)
(* 两难两角：                                                                 *)
(*   自由发射角（不补公理）：X 可判定为假（0 与 1/4 同格判伪），且               *)
(*     Halt 触发后证书被一次合法发射当场证伪——Halt 永伪；                        *)
(*   格律公理角（发射器分母固定）：X 退化为整除算术平凡重述（格距判等 =           *)
(*「Z/2 可除性 + 商相等」），与钱包/颗粒机制零关联——平凡。                        *)
(* ===================================================================== *)

Definition dwm_D : Z := 4.        (* 公分母：格 = {k/4} *)
Definition dwm_grain : Z := 2.    (* grain = 1/2 = 2 格距单位 *)
Definition dwm_W0 : Z := 4.       (* 初始钱包 = 1 = 4 格距单位 *)

(* 判等命题 X 的 bool 化：差额 < grain ⟹ 同格（数值相等） *)
Definition X_test (a b : Z) : bool :=
  if Z.ltb (Z.abs (a - b)) dwm_grain then Z.eqb a b else true.

(* 入场费 = 与最近在场者的格距（空带哨兵 999 永不可达：带内置 a0） *)
Fixpoint dmin (x : Z) (l : list Z) : Z :=
  match l with
  | nil => 999
  | a :: l' => Z.min (Z.abs (x - a)) (dmin x l')
  end.

(* 在场检测（bool） *)
Fixpoint presentb (x : Z) (l : list Z) : bool :=
  match l with
  | nil => false
  | a :: l' => orb (Z.eqb x a) (presentb x l')
  end.

(* 发射机：付费入场，返回（新在场带, 新钱包） *)
Definition dwm_emit (x : Z) (l : list Z) (W : Z) : list Z * Z :=
  (x :: l, W - dmin x l).

(* Halt 证书的 bool 化：「一切未来合法发射皆在场」——对发射 x：
   合法（入场费 ≤ W）⟹ x 在场 *)
Definition halt_cert (x : Z) (l : list Z) (W : Z) : bool :=
  implb (Z.leb (dmin x l) W) (presentb x l).

(* —— 自由发射角：X 可判定为假（两点反例：0 与 1/4，差 1 < grain 2 而异格） —— *)
Theorem dwm_X_refuted : tid bool (X_test 0 1) false.
Proof.
  unfold X_test, dwm_grain. apply tid_refl.
Qed.

(* —— 席 4 细分化反例全程仿真：带内置 [0]，grain = 2，钱包 = 4。
   步 1：发射 1/2（格 2），费 2，钱包→2；步 2：发射 1/4（格 1），费 1，钱包→1 < grain
   ——Halt 触发；步 3：发射 3/4（格 3），费 1 ≤ 钱包 1，合法，且 3 ∉ 在场集
   ——「未来皆同」证书被一次合法发射当场证伪。 —— *)
Definition dwm_W1 : Z := snd (dwm_emit 2 (0 :: nil) dwm_W0).
Definition dwm_W2 : Z := snd (dwm_emit 1 (2 :: 0 :: nil) dwm_W1).

Theorem dwm_wallet_trajectory : tid Z dwm_W2 1.
Proof.
  unfold dwm_W2, dwm_W1, dwm_emit, dwm_W0. apply tid_refl.
Qed.

Theorem dwm_halt_fires : tid bool (Z.ltb dwm_W2 dwm_grain) true.
Proof.
  unfold dwm_W2, dwm_W1, dwm_emit, dwm_W0, dwm_grain. apply tid_refl.
Qed.

Theorem dwm_emit3_legal : tid bool (Z.leb (dmin 3 (2 :: 1 :: 0 :: nil)) dwm_W2) true.
Proof.
  unfold dwm_W2, dwm_W1, dwm_emit, dwm_W0. apply tid_refl.
Qed.

Theorem dwm_emit3_not_present : tid bool (presentb 3 (2 :: 1 :: 0 :: nil)) false.
Proof.
  apply tid_refl.
Qed.

(* Halt 永伪半边：Halt 触发态（钱包 1 < grain 2）下证书对 x = 3 判假 *)
Theorem dwm_halt_cert_refuted : tid bool (halt_cert 3 (2 :: 1 :: 0 :: nil) dwm_W2) false.
Proof.
  unfold halt_cert, dwm_W2, dwm_W1, dwm_emit, dwm_W0. apply tid_refl.
Qed.

(* —— 格律公理角：X 退化为整除算术平凡重述 ——
   补发射器格律（格点 = 2·格距 的倍数）后，同格判等归约为 Z/2 可除性 + 商相等：
   格点 a = 2·ka, b = 2·kb，|a−b| < 2 ⟹ ka = kb——证明过程只动整除算术，
   钱包/颗粒/入场费机制零参与（平凡档）。 *)
Definition lattice_X (a b : Z) : bool :=
  if Z.ltb (Z.abs (a - b)) dwm_grain then Z.eqb (a / 2) (b / 2) else true.

Theorem dwm_lattice_X_trivial : forall a b : Z,
  tid bool (Z.eqb (a mod 2) 0) true -> tid bool (Z.eqb (b mod 2) 0) true ->
  tid bool (lattice_X a b) true.
Proof.
  intros a b Ha Hb.
  tidEqN Ha HEA. tidEqN Hb HEB.
  apply Z.eqb_eq in HEA. apply Z.eqb_eq in HEB.
  pose proof (Z.div_mod a 2 (ltac:(lia))) as HDA.
  pose proof (Z.div_mod b 2 (ltac:(lia))) as HDB.
  rewrite HEA in HDA. rewrite HEB in HDB.
  assert (HA2 : (a = 2 * (a / 2))%Z) by lia.
  assert (HB2 : (b = 2 * (b / 2))%Z) by lia.
  unfold lattice_X, dwm_grain.
  destruct (Z.ltb (Z.abs (a - b)) 2) eqn:E.
  - apply Z.ltb_lt in E.
    rewrite HA2, HB2 in E.
    rewrite <- Z.mul_sub_distr_l in E.
    rewrite Z.abs_mul in E.
    assert (H2abs : (Z.abs 2 = 2)%Z) by reflexivity.
    rewrite H2abs in E.
    destruct (Z_lt_ge_dec (Z.abs (a / 2 - b / 2)) 1) as [Hlt | Hge].
    + assert (Hk : (a / 2 = b / 2)%Z) by lia.
      rewrite Hk. rewrite Z.eqb_refl. apply tid_refl.
    + exfalso. lia.
  - apply tid_refl.
Qed.

(* 两难收口合注：自由发射角 dwm_X_refuted + dwm_halt_cert_refuted（不补则 Halt 永伪）
   与格律公理角 dwm_lattice_X_trivial（补则 X 退化为整除算术平凡重述、与钱包机制
   零关联）合取——押注两头死，DWM 原停机支不可满足或满足即平凡。 *)
