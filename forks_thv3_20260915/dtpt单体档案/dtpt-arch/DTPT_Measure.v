(* ============================================================
   DTPT_Measure.v — 频数测度与均匀测度层（席 DTPT-S5 新建面）
   职责：频数/均匀测度层的频数理论补建——§1 频数函数 freq
         （Qeq_bool 判等计数）与可加/同余/零频引理、§2 频数置换
         不变性 freq_perm（对 Permutation 四构造逐核，旗舰件）、
         §3 频数质量守恒 sumf / Sigma_freq 与 sum_freq_dedup（主件）、
         §4 均匀测度 mu 与总质量一 mu_perm + mu_total_mass（主件）。
   依赖：DTPT（dedup / Qmem / Qnodup / Qeqb_* 工具箱）、
         QArith（QArith/Qabs）、List、Arith、Lia、Permutation。
   归并记录：无（原生成模块）。
   认证：零承认零公理；全树 coqchk EXIT=0（2026-09-14）。
   纪律：纯构造性；四关收割；温控协议；Set 层零公理面；全程 Qed
         收口；nat 层一律显式限定（防 DTPT.v 文件头
         Open Scope Q_scope 泄漏：不裸写 + / S / 0）。
   附注：原典映射 D8 计数测度/均匀测度面的频数理论补建。
   ============================================================ *)

Require DTPT.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
Import ListNotations.
Import DTPT.DTPT.

Module DTPT_Measure.

(* ========== §1 频数函数 ========== *)

(* freq l x：元素 x（按 Qeq_bool 判等）在表 l 中的出现次数。
   取值 nat，非负性平凡成立，免证。 *)
Fixpoint freq (l : list Q) (x : Q) : nat :=
  match l with
  | [] => O
  | y :: ys => if Qeq_bool y x then Datatypes.S (freq ys x) else freq ys x
  end.

Lemma freq_nonneg : forall (l : list Q) (x : Q), (0 <= freq l x)%nat.
Proof. intros l x. lia. Qed.

(* 拼接可加性：频数按表分解线性叠加 *)
Lemma freq_app : forall (l p : list Q) (x : Q),
  freq (l ++ p) x = (freq l x + freq p x)%nat.
Proof.
  induction l as [| y ys IH]; intros p x; simpl.
  - reflexivity.
  - destruct (Qeq_bool y x); rewrite IH; reflexivity.
Qed.

(* 频数对 Qeq 相等元素的同余：判等换名不换频 *)
Lemma freq_eq_congr : forall (x y : Q) (l : list Q),
  x == y -> freq l x = freq l y.
Proof.
  intros x y l Hxy. induction l as [| a l IH]; simpl.
  - reflexivity.
  - destruct (Qeq_bool a x) eqn:Ex; destruct (Qeq_bool a y) eqn:Ey.
    + f_equal. exact IH.
    + exfalso.
      assert (Hay : Qeq_bool a y = true).
      { apply (Qeqb_trans a x y);
          [exact Ex | apply Qeqb_true_of; exact Hxy]. }
      rewrite Hay in Ey. discriminate.
    + exfalso.
      assert (Hyx : Qeq_bool y x = true)
        by (rewrite (Qeqb_sym y x); apply Qeqb_true_of; exact Hxy).
      assert (Hax : Qeq_bool a x = true)
        by (apply (Qeqb_trans a y x); [exact Ey | exact Hyx]).
      rewrite Hax in Ex. discriminate.
    + exact IH.
Qed.

(* 非成员则频数为零 *)
Lemma freq_zero_of_notQmem : forall (x : Q) (l : list Q),
  ~ Qmem x l -> freq l x = O.
Proof.
  intros x l. induction l as [| a l IH]; intros Hn.
  - reflexivity.
  - simpl.
    assert (Hax : Qeq_bool a x = false).
    { destruct (Qeq_bool a x) eqn:E.
      - exfalso. apply Hn. apply (proj2 (Qmem_cons x a l)).
        left. rewrite (Qeqb_sym x a). exact E.
      - reflexivity. }
    rewrite Hax. apply IH.
    intro Hc. apply Hn. apply (proj2 (Qmem_cons x a l)). right. exact Hc.
Qed.

(* ========== §2 频数置换不变性（旗舰件） ========== *)

(* 相邻换位守恒：两元素判等布尔四案枚举，案案 refl 闭合 *)
Lemma freq_swap : forall (a b : Q) (l : list Q) (x : Q),
  freq (a :: b :: l) x = freq (b :: a :: l) x.
Proof.
  intros a b l x. simpl.
  destruct (Qeq_bool a x); destruct (Qeq_bool b x); reflexivity.
Qed.

(* 旗舰件：频数沿置换不变——perm_nil 平凡 / perm_skip 判等分票 /
   perm_swap 经 freq_swap / perm_trans 传递链，逐构造核毕 *)
Theorem freq_perm : forall (l p : list Q) (x : Q),
  Permutation l p -> freq l x = freq p x.
Proof.
  intros l p x Hp.
  induction Hp as [| y l0 p0 H IH | a b l0 | l1 l2 l3 H1 IH1 H2 IH2].
  - reflexivity.
  - simpl. destruct (Qeq_bool y x); rewrite IH; reflexivity.
  - exact (freq_swap b a l0 x).
  - rewrite IH1. exact IH2.
Qed.

(* ========== §3 频数质量守恒（主件） ========== *)

(* 支撑表 m 上的频数质量和；m := dedup l 时即总质量 Σ_freq *)
Fixpoint sumf (m l : list Q) : nat :=
  match m with
  | [] => O
  | y :: ys => (freq l y + sumf ys l)%nat
  end.

Definition Sigma_freq (l : list Q) : nat := sumf (dedup l) l.

(* 关键引理：Qnodup 支撑表上，x 的质量份额自 dedup_aux x m 中转记到
   (x :: l) 计数面——被吞元素（与 x 同频者至多一个）经同余搬账，
   余元素在加头表中频数不变增。 *)
Lemma sumf_dedup_aux : forall (m : list Q) (x : Q) (l : list Q),
  Qnodup m ->
  sumf m l
  = ((if existsb (fun z => Qeq_bool x z) m then freq l x else O)
     + sumf (dedup_aux x m) (x :: l))%nat.
Proof.
  intros m x l. induction m as [| y m' IH]; intros Hnd.
  - simpl. reflexivity.
  - simpl in Hnd. destruct Hnd as [Hny Hnd'].
    destruct (Qeq_bool x y) eqn:Hxy.
    + (* 头 y 与 x 同频：被吞，频数经同余搬账 *)
      simpl. rewrite ?Hxy. simpl.
      assert (Hfeq : freq l y = freq l x).
      { apply (freq_eq_congr y x l).
        apply (proj1 (Qeq_bool_iff y x)).
        rewrite (Qeqb_sym y x). exact Hxy. }
      destruct (existsb (fun z => Qeq_bool x z) m') eqn:Em'.
      * exfalso. apply Hny.
        apply (Qmem_weaken x y m'); [unfold Qmem; exact Em' | exact Hxy].
      * specialize (IH Hnd'). simpl in IH.
        rewrite Hfeq. rewrite IH. reflexivity.
    + (* 头 y 与 x 异频：留表，加头 x 不增其频 *)
      simpl. rewrite ?Hxy. simpl. rewrite ?Hxy. simpl.
      specialize (IH Hnd'). rewrite IH.
      destruct (existsb (fun z => Qeq_bool x z) m'); lia.
Qed.

(* 质量守恒：支撑像上的频数总和恰为表长
   （空表时两边皆零，无需非空卫哨；非空版本为其特例） *)
Theorem sum_freq_dedup : forall l : list Q, Sigma_freq l = length l.
Proof.
  intros l. unfold Sigma_freq.
  induction l as [| x xs IH].
  - reflexivity.
  - assert (Hkey := sumf_dedup_aux (dedup xs) x xs (dedup_Qnodup xs)).
    simpl. rewrite (Qeq_bool_refl x). simpl.
    destruct (existsb (fun z => Qeq_bool x z) (dedup xs)) eqn:Hb.
    + simpl in Hkey. rewrite IH in Hkey.
      rewrite Hkey. lia.
    + simpl in Hkey. rewrite IH in Hkey.
      assert (Hnx : ~ Qmem x xs).
      { intro Hc.
        assert (Hp : Qmem x (dedup xs)) by (apply (dedup_Qmem_r xs x); exact Hc).
        unfold Qmem in Hp. rewrite Hp in Hb. discriminate. }
      assert (H0 : freq xs x = O) by (apply freq_zero_of_notQmem; exact Hnx).
      rewrite H0. rewrite Hkey. reflexivity.
Qed.

(* ========== §4 均匀测度与总质量（主件） ========== *)

(* Q 表求和（stdlib list_sum 为 nat 版，Q 版自建） *)
Fixpoint qsum (m : list Q) : Q :=
  match m with
  | [] => 0
  | y :: ys => (y + qsum ys)%Q
  end.

(* # 记号分母须 positive，故均匀测度取 (freq # 1) / (length # 1)，
   语义即 freq/length；length = 0（空表）时为退化值，定理面带非空卫哨。 *)
Definition mu (l : list Q) (x : Q) : Q :=
  ((Z.of_nat (freq l x) # 1) / (Z.of_nat (length l) # 1))%Q.

(* 均匀测度沿置换不变：频数与表长双不变直接放电 *)
Theorem mu_perm : forall (l p : list Q) (x : Q),
  Permutation l p -> mu l x = mu p x.
Proof.
  intros l p x Hp.
  assert (Hf : freq l x = freq p x) by (apply (freq_perm l p x Hp)).
  assert (Hn : length l = length p) by (apply Permutation_length; exact Hp).
  unfold mu. rewrite Hf, Hn. reflexivity.
Qed.

(* #1 形频数表的 Q 求和 = 质量和的 Z 化 *)
Lemma qsum_freq_map : forall (l m : list Q),
  qsum (map (fun y => (Z.of_nat (freq l y) # 1)%Q) m)
  == (Z.of_nat (sumf m l) # 1)%Q.
Proof.
  intros l m. induction m as [| y ys IH]; simpl.
  - reflexivity.
  - rewrite IH.
    rewrite (Znat.Nat2Z.inj_add (freq l y) (sumf ys l)).
    unfold Qplus, Qeq. simpl. lia.
Qed.

(* 逐点除同一 Q 的求和分配（Q 域除法配平的承重件） *)
Lemma qsum_map_div : forall (D : Q) (f : Q -> Q) (m : list Q),
  qsum (map (fun y => (f y / D)%Q) m) == (qsum (map f m) / D)%Q.
Proof.
  intros D f m. induction m as [| y ys IH].
  - cbn [qsum map]. symmetry. apply Qmult_0_l.
  - cbn [qsum map]. rewrite IH. unfold Qdiv. ring.
Qed.

(* 总质量一：非空表的均匀测度在支撑像上求和恰为一
   ——质量守恒经 Z 化搬上 Q 域，除以总长 D 后除法配平 *)
Theorem mu_total_mass : forall l : list Q, l <> [] ->
  qsum (map (mu l) (dedup l)) == 1.
Proof.
  intros l Hne.
  assert (Hpos : (1 <= Z.of_nat (length l))%Z).
  { apply (proj1 (Znat.Nat2Z.inj_le 1 (length l))).
    destruct l as [| y ys].
    - exfalso. apply Hne. reflexivity.
    - simpl. lia. }
  assert (HDne : ~ ((Z.of_nat (length l) # 1)%Q == 0%Q)).
  { intros Hc. unfold Qeq in Hc. simpl in Hc. lia. }
  assert (Hfun : forall y : Q,
           mu l y = ((Z.of_nat (freq l y) # 1) / (Z.of_nat (length l) # 1))%Q)
    by (intros y; reflexivity).
  rewrite (map_ext (mu l)
             (fun y => ((Z.of_nat (freq l y) # 1) / (Z.of_nat (length l) # 1))%Q)
             Hfun).
  rewrite (qsum_map_div (Z.of_nat (length l) # 1)%Q
                        (fun y => (Z.of_nat (freq l y) # 1)%Q)).
  rewrite (qsum_freq_map l (dedup l)).
  pose proof (sum_freq_dedup l) as HS. unfold Sigma_freq in HS. rewrite HS.
  field.
  intros Hc. apply HDne. rewrite Hc. reflexivity.
Qed.

End DTPT_Measure.
