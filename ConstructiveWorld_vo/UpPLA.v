(* ===================================================================== *)
(* UpPLA.v — PLA v2 Coq 落地：p-adic 分层商 + 残基契约 + VCA 估值账户机      *)
(*                                                                       *)
(* 二轮圆桌头部候选（3 票）正式立项。理论来源：                              *)
(*   ROUNDTABLE2.md 席 6 段落末尾【PLA v2 终稿】四击正面收口 + VCA 杂交；      *)
(*   排队席位方案-二轮成果Coq化-20260907.md Q1 条目。                        *)
(*                                                                       *)
(* 载体全程 Z/nat/bool 判定层；零 eps、零序比较、零见证借贷。                 *)
(* 纪律：纯构造性（无 Axiom/Admitted/Parameter/Abort）；语句零 Prop           *)
(* （Set 层 tid 恒等型 + nle 序型 + sumbool 判定分支）；stdlib only。         *)
(*                                                                       *)
(* 四件：                                                                 *)
(*   件 1  p-adic 估值机器 vp（乘法可加 + 整除表征）                          *)
(*   件 2  分层商主件（layer_closed / layer_decide / pla_stratified_quotient  *)
(*         + 席 5 分岔反例收编对照定理）                                     *)
(*   件 3  残基契约显式化（contract 双档，调度器输入参数非隐藏前提）            *)
(*   件 4  VCA 估值账户机（入场费可判定 / 耗散单调 / 进位清偿调度）             *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import ZArithRing.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(* ===================================================================== *)
(* 0. Set 层基建：tid 恒等型 / nle 序型 / 判定存活工具                        *)
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

(* Set 层自然数序型（k < m 编码为 nle (S k) m） *)
Inductive nle (n : nat) : nat -> Set :=
| nle_n : nle n n
| nle_S : forall m : nat, nle n m -> nle n (S m).

Ltac tidE H :=
  pose proof (match H in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as HE.

(* bool 恒等矛盾关闭器：H1 : tid bool X true、H2 : tid bool X false *)
Ltac tid_kill H1 H2 :=
  pose proof (match H1 in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as KE1;
  pose proof (match H2 in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as KE2;
  rewrite KE1 in KE2; discriminate KE2.

(* Set 层 nle 基本件 *)
Lemma leb_refl_tid : forall a : nat, tid bool (Nat.leb a a) true.
Proof.
  intros a. rewrite Nat.leb_refl. apply tid_refl.
Qed.

Lemma leb_S : forall a m : nat,
  tid bool (Nat.leb a m) true -> tid bool (Nat.leb a (S m)) true.
Proof.
  intros a m. revert a. induction m as [| m1 IH]; intros a H.
  - destruct a as [| a1].
    + apply tid_refl.
    + change (tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply tid_refl.
    + exact (IH a1 H).
Qed.

Fixpoint nle_lebF (a b : nat) (H : nle a b) {struct H} :
  tid bool (Nat.leb a b) true :=
  match H as H0 in nle _ bb
  return tid bool (Nat.leb a bb) true with
  | nle_n _ => leb_refl_tid a
  | nle_S _ m H1 => leb_S a m (nle_lebF a m H1)
  end.

Definition nle_leb (b a : nat) (H : nle a b) : tid bool (Nat.leb a b) true :=
  nle_lebF a b H.

(* nle -> nat ≤ 提取（仅证明内部推理用；可重复调用，自动起新名） *)
Ltac nleP H :=
  let HN := fresh "HNle" in
  pose proof
    (proj1 (Nat.leb_le _ _)
       (match (nle_leb _ _ H) in tid _ x y return x = y with
        | tid_refl _ _ => eq_refl
        end)) as HN.

Lemma nle_SS : forall a b : nat, nle a b -> nle (S a) (S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply nle_n.
  - apply nle_S. exact IH.
Qed.

Lemma nle_0 : forall m : nat, nle O m.
Proof.
  induction m as [| m1 IH].
  - apply nle_n.
  - apply nle_S. exact IH.
Qed.

Lemma nle_of_leb : forall b a : nat,
  tid bool (Nat.leb a b) true -> nle a b.
Proof.
  induction b as [| b1 IB]; intros a H.
  - destruct a as [| a1].
    + apply nle_n.
    + change (tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply nle_0.
    + exact (nle_SS a1 b1 (IB a1 H)).
Qed.

(* nat ≤ → tid bool (leb) true 桥（leb_le 的 bool 封装） *)
Lemma lebT : forall a b : nat, (a <= b)%nat -> tid bool (Nat.leb a b) true.
Proof.
  intros a b H. rewrite (proj2 (Nat.leb_le _ _) H). apply tid_refl.
Qed.


Lemma nle_trans : forall a b c : nat, nle a b -> nle b c -> nle a c.
Proof.
  intros a b c H1 H2. induction H2 as [| c H2 IH].
  - exact H1.
  - apply nle_S. exact IH.
Qed.

(* nle 前驱消解：nle (S a) (S b) -> nle a b *)
Lemma nle_pred : forall a b : nat, nle (S a) (S b) -> nle a b.
Proof.
  intros a b H. apply nle_of_leb.
  exact (nle_leb (S b) (S a) H).
Qed.

Lemma nle_add_r : forall a b : nat, nle a (a + b).
Proof.
  intros a b. revert b. induction a as [| a1 IH]; intro b.
  - apply nle_0.
  - exact (nle_SS a1 (a1 + b) (IH b)).
Qed.


(* nle (S O) O 荒谬件（索引不交配的空消去，合法关闭任意 Set 目标） *)
Lemma nle_10_absurd : forall P : Type, nle (S O) O -> P.
Proof.
  intros P H. inversion H.
Qed.

(* Z 层严格序 → nle 编码桥：0 ≤ a < b ⟹ nle (S (to_nat a)) (to_nat b) *)
Lemma zle_to_nle_S : forall a b : Z, (0 <= a)%Z -> (a < b)%Z ->
  nle (S (Z.to_nat a)) (Z.to_nat b).
Proof.
  intros a b Ha Hlt.
  assert (Hb : (0 <= b)%Z) by lia.
  apply nle_of_leb.
  assert (Hleb : (Nat.leb (S (Z.to_nat a)) (Z.to_nat b)) = true).
  { apply Nat.leb_le.
    exact (proj1 (Z2Nat.inj_lt a b Ha Hb) Hlt). }
  rewrite Hleb. apply tid_refl.
Qed.

(* n≠0 ⟹ |n| 的 nat 编码 ≥ (S O) *)
Lemma to_nat_abs_pos : forall n : Z,
  tid bool (Z.eqb n 0) false -> nle (S O) (Z.to_nat (Z.abs n)).
Proof.
  intros n H. tidE H.
  assert (Hne : n <> 0) by (intro Hc; rewrite Hc in HE; discriminate HE).
  apply (zle_to_nle_S 0 (Z.abs n)).
  - lia.
  - pose proof (proj2 (Z.abs_pos n) Hne). lia.
Qed.

(* |x| ≥ (S O) ⟹ x ≠ 0 的 bool 形 *)
Lemma eqb0_false_of_pos : forall x : Z,
  nle (S O) (Z.to_nat (Z.abs x)) -> tid bool (Z.eqb x 0) false.
Proof.
  intros x H. destruct (Z.eqb x 0) eqn:HEq.
  - apply (proj1 (Z.eqb_eq _ _)) in HEq. rewrite HEq in H.
    exact (nle_10_absurd _ H).
  - apply tid_refl.
Qed.

(* ===================================================================== *)
(* 件 1. p-adic 估值机器                                                  *)
(* ===================================================================== *)

(* p 的 Z 形 / 整除测试 / p^k / p^k 整除测试 *)
Definition pZ (p : nat) : Z := Z.of_nat p.
Definition dvdtest (p : nat) (x : Z) : bool := Z.eqb (Z.modulo x (pZ p)) 0.
Definition powZN (p k : nat) : Z := Z.pow (pZ p) (Z.of_nat k).
Definition dwtest (p k : nat) (x : Z) : bool := Z.eqb (Z.modulo x (powZN p k)) 0.

(* 燃料式估值计数。vp p 0 := 0 专用编码（零态由 Z.eqb 守卫直派 0，避免
   nat 编码无穷；消耗方以 Z.eqb n 0 守卫非零——报告注 1）。 *)
Fixpoint vpF (p : nat) (f : nat) (n : Z) {struct f} : nat :=
  match f with
  | O => O
  | S g =>
      if Z.eqb n 0 then O
      else if dvdtest p n then S (vpF p g (Z.div n (pZ p)))
      else O
  end.

(* 公开估值：燃料取 |n|+1（n≠0 且 p≥2 时每步 |n| 至少折半，燃料充分） *)
Definition vp (p : nat) (n : Z) : nat := vpF p (S (Z.to_nat (Z.abs n))) n.

(* 关键递减：p≥2、n≠0、p∣n ⟹ |n/p| < |n|（nle (S k) m 编码 k<m） *)
Lemma zdiv_abs_decr : forall (p : nat) (n : Z), (2 <= p)%nat ->
  tid bool (Z.eqb n 0) false -> tid bool (dvdtest p n) true ->
  nle (S (Z.to_nat (Z.abs (Z.div n (pZ p))))) (Z.to_nat (Z.abs n)).
Proof.
  intros p n Hp Hnz Hd.
  tidE Hnz.
  pose proof (match Hd in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as HE2.
  assert (Hne : n <> 0) by (intro Hc; rewrite Hc in HE; discriminate HE).
  assert (Hpz : (2 <= pZ p)%Z).
  { unfold pZ. apply (proj1 (Nat2Z.inj_le 2 p)). exact Hp. }
  assert (Hpp : (0 <= pZ p)%Z) by lia.
  assert (Hpz0 : pZ p <> 0) by lia.
  assert (Hmod : Z.modulo n (pZ p) = 0) by (apply (proj1 (Z.eqb_eq _ _)); exact HE2).
  assert (Hex : n = pZ p * (Z.div n (pZ p))).
  { pose proof (Z.div_mod n (pZ p) Hpz0) as Hdm. rewrite Hmod in Hdm. lia. }
  assert (Hq0 : Z.div n (pZ p) <> 0).
  { intro Hc. rewrite Hc in Hex. lia. }
  assert (Hqa : (0 < Z.abs (Z.div n (pZ p)))%Z).
  { apply (proj2 (Z.abs_pos (Z.div n (pZ p)))). exact Hq0. }
  assert (Habsm : Z.abs n = pZ p * Z.abs (Z.div n (pZ p))).
  { rewrite Hex at 1. rewrite Z.abs_mul. rewrite (Z.abs_eq (pZ p) Hpp).
    reflexivity. }
  assert (Hm2 : (2 * Z.abs (Z.div n (pZ p)) <= Z.abs n)%Z).
  { rewrite Habsm. apply Z.mul_le_mono_nonneg_r.
    - apply Z.abs_nonneg.
    - exact Hpz. }
  assert (Hlt : (Z.abs (Z.div n (pZ p)) < Z.abs n)%Z) by lia.
  apply zle_to_nle_S.
  - apply Z.abs_nonneg.
  - exact Hlt.
Qed.

(* 除法保持非零：p≥2、n≠0、p∣n ⟹ n/p ≠ 0（bool 形） *)
Lemma zdiv_nz : forall (p : nat) (n : Z), (2 <= p)%nat ->
  tid bool (Z.eqb n 0) false -> tid bool (dvdtest p n) true ->
  tid bool (Z.eqb (Z.div n (pZ p)) 0) false.
Proof.
  intros p n Hp Hnz Hd.
  assert (Hpz : (2 <= pZ p)%Z).
  { unfold pZ. apply (proj1 (Nat2Z.inj_le 2 p)). exact Hp. }
  assert (Hpz0 : pZ p <> 0) by lia.
  tidE Hnz.
  pose proof (match Hd in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as HE2.
  assert (Hne : n <> 0) by (intro Hc; rewrite Hc in HE; discriminate HE).
  assert (Hmod : Z.modulo n (pZ p) = 0) by (apply (proj1 (Z.eqb_eq _ _)); exact HE2).
  assert (Hdm : n = pZ p * (Z.div n (pZ p))).
  { pose proof (Z.div_mod n (pZ p) Hpz0) as Hd0. rewrite Hmod in Hd0. lia. }
  apply eqb0_false_of_pos.
  apply (zle_to_nle_S 0 (Z.abs (Z.div n (pZ p)))).
  - lia.
  - apply (proj2 (Z.abs_pos (Z.div n (pZ p)))).
    intro Hc. rewrite Hc in Hdm. lia.
Qed.

(* 燃料无关性：燃料均盖住 |n| 时计数唯一 *)
Lemma vpF_indep : forall (p B : nat), (2 <= p)%nat ->
  forall (f1 f2 : nat) (n : Z),
    nle (Z.to_nat (Z.abs n)) B ->
    tid bool (Z.eqb n 0) false ->
    nle (Z.to_nat (Z.abs n)) f1 ->
    nle (Z.to_nat (Z.abs n)) f2 ->
    tid nat (vpF p f1 n) (vpF p f2 n).
Proof.
  intros p B Hp. induction B as [| B1 IB]; intros f1 f2 n HnB Hnz Hf1 Hf2.
  - assert (H1 := to_nat_abs_pos n Hnz).
    pose proof (nle_trans _ _ _ H1 HnB) as HC. inversion HC.
  - destruct f1 as [| g1].
    + assert (H1 := to_nat_abs_pos n Hnz).
      pose proof (nle_trans _ _ _ H1 Hf1) as HC. inversion HC.
    + destruct f2 as [| g2].
      * assert (H1 := to_nat_abs_pos n Hnz).
        pose proof (nle_trans _ _ _ H1 Hf2) as HC. inversion HC.
      * cbn [vpF]. tidE Hnz. rewrite HE.
        destruct (dvdtest p n) eqn:Hd.
        -- (* p ∣ n：两边同进入位支，递归比较 n/p 的计数 *)
           assert (Hdt : tid bool (dvdtest p n) true)
             by (rewrite Hd; apply tid_refl).
           apply (tid_cong S).
           apply IB with (n := Z.div n (pZ p)).
           ++ exact (nle_pred _ _
                 (nle_trans _ _ _ (zdiv_abs_decr p n Hp Hnz Hdt) HnB)).
           ++ exact (zdiv_nz p n Hp Hnz Hdt).
           ++ exact (nle_pred _ _
                 (nle_trans _ _ _ (zdiv_abs_decr p n Hp Hnz Hdt) Hf1)).
           ++ exact (nle_pred _ _
                 (nle_trans _ _ _ (zdiv_abs_decr p n Hp Hnz Hdt) Hf2)).
        -- (* p ∤ n：else 支直派 O（destruct 已代入，iota 归约即闭） *)
           apply tid_refl.
Qed.
