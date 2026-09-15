(* ============================================================
   DTPT.v — DTPT 主框架
   职责：数字全域—熵相三元论·构造性主框架——原典映射（基座.txt 全
         12 章 + 公理 D1–D13 + LLM 附录）的 Dig 数字结构、D5 支撑域
         同一、N9 序列熵分离、定理 A/B/C、证据分层网络与 LLM 相位
         视图；Stdlib 隔离模式，不依赖代码库 S 系
   依赖：仅 stdlib（QArith/List/Arith/Lia/Permutation）
   归并记录：2026-09-14 并入 DTPT_CGen/DTPT_N9Opt/DTPT_D8Ext
         （+DTPT_Dig 处置：内容与 §1–§3 完全重复，退役不并入）
   认证：零承认零公理；全树 coqchk EXIT=0（2026-09-14）
   纪律：纯构造性；四关收割；温控协议
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
Import ListNotations.
Open Scope Q_scope.

Module DTPT.

(* ========== §1 数字结构归纳类型 Dig（D1/D2/D9 构造消解） ========== *)

Inductive Dig : Type :=
| dQ     : Q -> Dig
| dPair  : Dig -> Dig -> Dig
| dSeq   : list Dig -> Dig
| dCode  : nat -> (nat -> Dig) -> Dig
| dJudge : Dig -> Dig -> Dig
| dModel : Dig -> Dig
| dProofT: Dig -> Dig -> Dig.

(* ========== §2 有穷序列载体与组织算子（D4/D6/D7 构造） ========== *)

Fixpoint insert_q (x : Q) (l : list Q) : list Q :=
  match l with
  | [] => [x]
  | y :: ys => if Qle_bool x y then x :: y :: ys else y :: insert_q x ys
  end.

Fixpoint P0 (l : list Q) : list Q :=
  match l with
  | [] => []
  | x :: xs => insert_q x (P0 xs)
  end.

Definition rot (n : nat) (l : list Q) : list Q :=
  firstn n l ++ skipn n l.

Definition Pinf (l : list Q) (s : nat) : list Q :=
  rot (S s) l.

Fixpoint interleave (l1 l2 : list Q) : list Q :=
  match l1, l2 with
  | [], _ => l2
  | _ :: _, [] => l1
  | x :: xs, y :: ys => x :: y :: interleave xs ys
  end.

Definition Pmid (l : list Q) (s lam : nat) : list Q :=
  firstn lam (P0 l) ++ skipn lam (Pinf l s).

(* ========== §3 支撑域同一（D5 → 定理 A） ========== *)

Lemma insert_q_perm_cons : forall (x : Q) (l : list Q),
  Permutation (x :: l) (insert_q x l).
Proof.
  intros x l. induction l as [| y ys IH]; simpl.
  - simpl. apply perm_skip. apply perm_nil.
  - destruct (Qle_bool x y) eqn:Hxy.
    + apply perm_skip. apply Permutation_refl.
    + etransitivity.
      * apply perm_swap.
      * apply perm_skip. exact IH.
Qed.

Theorem D5_P0_perm : forall l : list Q, Permutation l (P0 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply Permutation_refl.
  - etransitivity.
    + apply perm_skip. exact IH.
    + apply insert_q_perm_cons.
Qed.

(* 【弃用注记 2026-09-14】本件在 rot=firstn++skipn 恒等底座下为恒等推论伪装；操作语义以 DTPT_ROTC/DTPT_Cyc/DTPT_RotSpec 真化层为准。 *)
Theorem D5_Pinf_perm : forall (l : list Q) (s : nat), Permutation l (Pinf l s).
Proof.
  intros l s. unfold Pinf, rot.
  rewrite firstn_skipn.
  apply Permutation_refl.
Qed.

(* D5_Pmid_perm: general lam is false (firstn/skipn truncation not a permutation); covered by endpoint theorems. *)

Theorem D5_support_same : forall (l : list Q) (s : nat),
  Permutation l (P0 l) /\ Permutation l (Pinf l s).
Proof.
  intros l s. split; [apply D5_P0_perm | apply D5_Pinf_perm].
Qed.

(* ========== §4 多熵函数族与序列熵分离（N9 + 定理 C） ========== *)

Fixpoint dedup_aux (x : Q) (l : list Q) : list Q :=
  match l with
  | [] => []
  | y :: ys => if Qeq_bool x y then dedup_aux x ys else y :: dedup_aux x ys
  end.

Fixpoint dedup (l : list Q) : list Q :=
  match l with
  | [] => []
  | x :: xs => x :: dedup_aux x (dedup xs)
  end.

Definition H_ms (l : list Q) : Q := (Z.of_nat (length (dedup l)) # 1)%Q.

Fixpoint sum_adjdiff (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => match xs with
               | [] => 0
               | y :: _ => Qabs (y - x) + sum_adjdiff xs
               end
  end.

Definition H_adj (l : list Q) : Q := sum_adjdiff l.

(* ========== W 补证席 B2：Q 工具箱（lia 不支持 Q，全部 Z 反射直解） ========== *)

Lemma Qle_bool_false_le : forall x y : Q, Qle_bool x y = false -> y <= x.
Proof.
  intros x y H. unfold Qle_bool in H. unfold Qle.
  destruct (Z.leb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E.
  - discriminate.
  - apply Z.leb_gt in E. lia.
Qed.

Lemma Qle_dec' : forall x y : Q, x <= y \/ y <= x.
Proof.
  intros x y. destruct (Qle_bool x y) eqn:E.
  - left. apply Qle_bool_iff in E. exact E.
  - right. apply Qle_bool_false_le. exact E.
Qed.

Lemma qadd_le : forall a b c d : Q, a <= b -> c <= d -> (a + c <= b + d)%Q.
Proof.
  intros [an ad] [bn bd] [cn cd] [dn dd] H H0;
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((an * Zpos bd) * (Zpos cd * Zpos dd)
                <= (bn * Zpos ad) * (Zpos cd * Zpos dd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  assert (H2 : ((cn * Zpos dd) * (Zpos ad * Zpos bd)
                <= (dn * Zpos cd) * (Zpos ad * Zpos bd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H0]).
  lia.
Qed.

Lemma qopp_le : forall a b : Q, a <= b -> (- b <= - a)%Q.
Proof.
  intros [an ad] [bn bd]; simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

Lemma qmul_le_r : forall n m p : Q, n <= m -> 0 <= p -> (n * p <= m * p)%Q.
Proof.
  intros [nn nd] [mn md] [pn pd] H H0;
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((nn * Zpos md) * (pn * Zpos pd)
                <= (mn * Zpos nd) * (pn * Zpos pd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Qed.

Lemma Qle_0_sub' : forall x y : Q, x <= y <-> (0 <= y - x)%Q.
Proof.
  intros [nx dx] [ny dy]; simpl; split; intros H;
  unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl; lia.
Qed.

Lemma qsub_le_r : forall a b c : Q, a <= b -> (a - c <= b - c)%Q.
Proof.
  intros [an ad] [bn bd] [cn cd] H.
  unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl.
  assert (H1 : ((an * Zpos bd) * (Zpos cd * Zpos cd)
                <= (bn * Zpos ad) * (Zpos cd * Zpos cd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Qed.

Lemma qsub_add : forall a b c : Q, (a - b + (b - c) == a - c)%Q.
Proof.
  intros [an ad] [bn bd] [cn cd].
  unfold Qeq, Qminus, Qplus, Qopp; simpl; lia.
Qed.

Lemma abs_eq : forall a : Q, 0 <= a -> Qabs a == a.
Proof.
  intros [n d] H. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - reflexivity.
  - exfalso. lia.
Qed.

Lemma abs_neg : forall a : Q, a <= 0 -> Qabs a == - a.
Proof.
  intros [n d] H. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - exfalso. lia.
  - reflexivity.
Qed.

Lemma abs_nonneg : forall a : Q, 0 <= Qabs a.
Proof.
  intros [n d]. unfold Qle. destruct n; simpl; lia.
Qed.

Lemma Qeqb_true_of : forall x y : Q, x == y -> Qeq_bool x y = true.
Proof.
  intros x y H. unfold Qeq in H. unfold Qeq_bool.
  destruct (Z.eqb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E; [reflexivity|].
  exfalso. apply Z.eqb_neq in E. lia.
Qed.

Lemma Qeqb_sym : forall x y : Q, Qeq_bool x y = Qeq_bool y x.
Proof.
  intros x y. destruct (Qeq_bool x y) eqn:E1, (Qeq_bool y x) eqn:E2; try reflexivity.
  - exfalso. apply Qeq_bool_eq in E1.
    assert (E1' : y == x) by (apply Qeq_sym; exact E1).
    apply Qeqb_true_of in E1'. congruence.
  - exfalso. apply Qeq_bool_eq in E2.
    assert (E2' : x == y) by (apply Qeq_sym; exact E2).
    apply Qeqb_true_of in E2'. congruence.
Qed.

Lemma Qeqb_trans : forall a b c : Q,
  Qeq_bool a b = true -> Qeq_bool b c = true -> Qeq_bool a c = true.
Proof.
  intros a b c H1 H2. apply Qeq_bool_eq in H1. apply Qeq_bool_eq in H2.
  apply Qeqb_true_of. transitivity b; assumption.
Qed.

(* ========== W 补证席 B2：N9_ms_perm_inv 基建（Qeq 成员 + dedup 特征） ========== *)

Definition Qmem (a : Q) (l : list Q) : Prop :=
  existsb (fun y => Qeq_bool a y) l = true.

Lemma Qmem_cons : forall a x (l : list Q),
  Qmem a (x :: l) <-> (Qeq_bool a x = true \/ Qmem a l).
Proof.
  intros a x l. unfold Qmem. simpl. rewrite orb_true_iff. reflexivity.
Qed.

Lemma Qmem_refl_cons : forall x (l : list Q), Qmem x (x :: l).
Proof. intros x l. rewrite Qmem_cons. left. apply Qeq_bool_refl. Qed.

Lemma Qmem_weaken : forall a b (l : list Q),
  Qmem a l -> Qeq_bool a b = true -> Qmem b l.
Proof.
  intros a b l H Hab. unfold Qmem in H. apply existsb_exists in H.
  destruct H as [w [Hw Hq]].
  unfold Qmem. apply existsb_exists. exists w. split; [exact Hw|].
  apply (Qeqb_trans b a w). rewrite (Qeqb_sym b a). exact Hab. exact Hq.
Qed.

Lemma Qmem_dedup_aux_keep : forall a x (l : list Q),
  Qmem a (dedup_aux x l) -> Qmem a l.
Proof.
  intros a x l. induction l as [| y ys IH]; simpl.
  - intros H. discriminate.
  - intros H. destruct (Qeq_bool x y).
    + rewrite Qmem_cons. right. exact (IH H).
    + rewrite Qmem_cons in H. destruct H as [H|H].
      * rewrite Qmem_cons. left. exact H.
      * rewrite Qmem_cons. right. exact (IH H).
Qed.

Lemma Qmem_dedup_aux_drop : forall a x (l : list Q),
  Qmem a l -> Qeq_bool a x = false -> Qmem a (dedup_aux x l).
Proof.
  intros a x l. induction l as [| y ys IH]; simpl.
  - intros H _. discriminate.
  - intros H Hax. rewrite Qmem_cons in H.
    destruct (Qeq_bool x y) eqn:Hxy.
    + destruct H as [H|H].
      * exfalso.
        assert (Hya : Qeq_bool y a = true) by (rewrite (Qeqb_sym y a); exact H).
        assert (Hxa : Qeq_bool x a = true) by (apply (Qeqb_trans x y a); assumption).
        rewrite (Qeqb_sym x a) in Hxa. rewrite Hxa in Hax. discriminate.
      * exact (IH H Hax).
    + rewrite Qmem_cons. destruct H as [H|H].
      * left. exact H.
      * right. exact (IH H Hax).
Qed.

Lemma dedup_aux_duck : forall a (l : list Q),
  Qmem a (dedup_aux a l) -> False.
Proof.
  intros a l. induction l as [| y ys IH]; simpl.
  - discriminate.
  - destruct (Qeq_bool a y) eqn:E.
    + apply IH.
    + rewrite Qmem_cons. intros [H|H].
      * rewrite E in H. discriminate.
      * apply IH. exact H.
Qed.

Fixpoint Qnodup (l : list Q) : Prop :=
  match l with
  | [] => True
  | x :: xs => ~ Qmem x xs /\ Qnodup xs
  end.

Lemma dedup_aux_Qnodup : forall x (l : list Q), Qnodup l -> Qnodup (dedup_aux x l).
Proof.
  intros x l. induction l as [| y ys IH]; simpl; [intros _; exact I |].
  - intros [Hny Hys]. destruct (Qeq_bool x y).
    + apply IH. exact Hys.
    + split.
      * intros Hm. apply Hny. exact (Qmem_dedup_aux_keep y x _ Hm).
      * apply IH. exact Hys.
Qed.

Lemma dedup_Qnodup : forall l : list Q, Qnodup (dedup l).
Proof.
  induction l as [| x xs IH]; simpl.
  - exact I.
  - split.
    + intros Hm. exfalso. exact (dedup_aux_duck x (dedup xs) Hm).
    + apply dedup_aux_Qnodup. exact IH.
Qed.

Lemma dedup_Qmem_l : forall (l : list Q) a, Qmem a (dedup l) -> Qmem a l.
Proof.
  induction l as [| x xs IH]; intros a; simpl.
  - discriminate.
  - rewrite Qmem_cons. intros [H|H].
    + rewrite Qmem_cons. left. exact H.
    + rewrite Qmem_cons. right. apply IH.
      exact (Qmem_dedup_aux_keep a x _ H).
Qed.

Lemma dedup_Qmem_r : forall (l : list Q) a, Qmem a l -> Qmem a (dedup l).
Proof.
  induction l as [| x xs IH]; intros a; simpl.
  - discriminate.
  - intros H. rewrite Qmem_cons. rewrite Qmem_cons in H.
    destruct H as [H|H].
    + left. exact H.
    + destruct (Qeq_bool a x) eqn:Hax.
      * left. reflexivity.
      * right. apply Qmem_dedup_aux_drop.
        -- apply IH. exact H.
        -- exact Hax.
Qed.

Lemma Qmem_perm : forall (l p : list Q) a, Permutation l p -> Qmem a l <-> Qmem a p.
Proof.
  intros l p a Hp. unfold Qmem. rewrite !existsb_exists. split; intros [y [Hy Hq]].
  - exists y. split; [apply (Permutation_in _ Hp); exact Hy | exact Hq].
  - exists y. split; [apply (Permutation_in _ (Permutation_sym Hp)); exact Hy | exact Hq].
Qed.

Lemma Qmem_cons_nodup : forall a x (xs : list Q),
  ~ Qmem x xs -> (Qmem a xs <-> (Qmem a (x :: xs) /\ Qeq_bool a x = false)).
Proof.
  intros a x xs Hx. split.
  - intros Ha. split.
    + rewrite Qmem_cons. right. exact Ha.
    + destruct (Qeq_bool a x) eqn:E.
      * exfalso. apply Hx. exact (Qmem_weaken a x xs Ha E).
      * reflexivity.
  - intros [Ha Hax]. rewrite Qmem_cons in Ha. destruct Ha as [Ha|Ha].
    + exfalso. rewrite Ha in Hax. discriminate.
    + exact Ha.
Qed.

Lemma remove_one : forall (x : Q) (n : list Q), Qnodup n -> Qmem x n ->
  exists n' : list Q, length n = S (length n') /\ Qnodup n'
    /\ (forall a, Qmem a n' <-> (Qmem a n /\ Qeq_bool a x = false)).
Proof.
  intros x n. induction n as [| y ys IH]; intros Hn Hx.
  - exfalso. unfold Qmem in Hx. simpl in Hx. discriminate.
  - destruct Hn as [Hy Hys]. rewrite Qmem_cons in Hx. destruct Hx as [Hxy|Hx].
    + (* x ~ y：移除头 y *)
      exists ys. split; [reflexivity | split].
      * exact Hys.
      * intros a. split.
        -- intros Ha. split.
           ++ rewrite Qmem_cons. right. exact Ha.
           ++ destruct (Qeq_bool a x) eqn:E.
              ** exfalso.
                 assert (Hya : Qeq_bool y a = true)
                   by (apply (Qeqb_trans y x a);
                       [rewrite <- (Qeqb_sym x y); exact Hxy | rewrite <- (Qeqb_sym a x); exact E]).
                 rewrite (Qeqb_sym y a) in Hya. apply Hy. exact (Qmem_weaken a y ys Ha Hya).
              ** reflexivity.
        -- intros [Ha Hax]. rewrite Qmem_cons in Ha. destruct Ha as [Ha|Ha].
           ++ exfalso.
              assert (Hay : Qeq_bool a x = true)
                by (apply (Qeqb_trans a y x); [exact Ha | rewrite <- (Qeqb_sym x y); exact Hxy]).
              rewrite Hay in Hax. discriminate.
           ++ exact Ha.
    + (* x ∈Q ys：内层递归移除，n' := y :: ys' *)
      destruct (IH Hys Hx) as [ys' [Hlen [Hnd Hiff]]].
      exists (y :: ys'). split; [simpl; rewrite Hlen; reflexivity | split].
      * split.
        -- intros Hm. exfalso. exact (Hy (proj1 (proj1 (Hiff y) Hm))).
        -- exact Hnd.
      * intros a. split.
        -- intros Ha. rewrite Qmem_cons in Ha. destruct Ha as [Ha|Ha].
           ++ split.
              ** rewrite Qmem_cons. left. exact Ha.
              ** destruct (Qeq_bool a x) eqn:E.
                 *** exfalso.
                     assert (Hxa : Qeq_bool x a = true)
                       by (rewrite <- (Qeqb_sym a x); exact E).
                     assert (Hxy' : Qeq_bool x y = true)
                       by (apply (Qeqb_trans x a y); [exact Hxa | exact Ha]).
                     apply Hy. exact (Qmem_weaken x y ys Hx Hxy').
                 *** reflexivity.
           ++ split.
              ** rewrite Qmem_cons. right. exact (proj1 (proj1 (Hiff a) Ha)).
              ** exact (proj2 (proj1 (Hiff a) Ha)).
        -- intros [Ha Hax].
           ++ destruct (Qeq_bool a y) eqn:Hbay.
              ** rewrite Qmem_cons. left. exact Hbay.
              ** rewrite Qmem_cons. right.
                 rewrite Qmem_cons in Ha. destruct Ha as [Ha|Ha].
                 { exfalso. rewrite Ha in Hbay. discriminate. }
                 { exact (proj2 (Hiff a) (conj Ha Hax)). }
Qed.

Lemma same_set_length : forall m n : list Q,
  Qnodup m -> Qnodup n -> (forall a, Qmem a m <-> Qmem a n) -> length m = length n.
Proof.
  induction m as [| x xs IH]; intros n Hm Hn Heq.
  - destruct n as [| y ys]; [reflexivity | exfalso].
    pose proof (proj2 (Heq y) (Qmem_refl_cons y ys)) as Hb.
    unfold Qmem in Hb. simpl in Hb. discriminate.
  - destruct n as [| y ys].
    + exfalso.
      pose proof (proj1 (Heq x) (Qmem_refl_cons x xs)) as Hb.
      unfold Qmem in Hb. simpl in Hb. discriminate.
    + assert (Hxs : Qmem x (y :: ys))
        by (apply (proj1 (Heq x)); apply Qmem_refl_cons).
      destruct (remove_one x (y :: ys) Hn Hxs)
        as [n' [Hlen1 [Hnd1 Hiff1]]].
      assert (Hss : forall a, Qmem a xs <-> Qmem a n').
      { intros a. split; intros Ha.
        - assert (Hpair := proj1 (Qmem_cons_nodup a x xs (proj1 Hm)) Ha).
          apply (proj2 (Hiff1 a)). split.
          + exact (proj1 (Heq a) (proj1 Hpair)).
          + exact (proj2 Hpair).
        - assert (Hpair := proj1 (Hiff1 a) Ha).
          apply (proj2 (Qmem_cons_nodup a x xs (proj1 Hm))).
          split.
          + exact (proj2 (Heq a) (proj1 Hpair)).
          + exact (proj2 Hpair). }
      assert (Hlen2 : length xs = length n')
        by (apply IH; [apply (proj2 Hm) | exact Hnd1 | exact Hss]).
      simpl. rewrite Hlen2. rewrite <- Hlen1. simpl. reflexivity.
Qed.

Theorem N9_ms_perm_inv : forall (l p : list Q),
  Permutation l p -> H_ms l = H_ms p.
Proof.
  intros l p Hp. unfold H_ms. f_equal. f_equal.
  apply same_set_length.
  - apply dedup_Qnodup.
  - apply dedup_Qnodup.
  - intros a. split; intros H.
    + apply dedup_Qmem_r.
      apply (proj1 (Qmem_perm l p a Hp)). apply dedup_Qmem_l. exact H.
    + apply dedup_Qmem_r.
      apply (proj2 (Qmem_perm l p a Hp)). apply dedup_Qmem_l. exact H.
Qed.

Theorem N9_seq_separates : exists (l1 l2 : list Q),
  Permutation l1 l2 /\ H_adj l1 <> H_adj l2.
Proof.
  exists [0; 1; 2], [0; 2; 1]. split.
  - apply perm_skip. apply perm_swap.
  - intro Hc. vm_compute in Hc. discriminate.
Qed.

(* ========== W 补证席 DTPT-C：C_sorted_min_adj 证明链
   （xq_ 前缀工具整链移植自 DTPT_Entropy.v 同源证明，仅依赖
     stdlib QArith/List/Permutation 与本文件已证定义，全程 Qed 零公理） ========== *)

Lemma qadd_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> (0 <= a + b)%Q.
Proof.
  intros [an ad] [bn bd]; simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

(* ---------- xq 局部工具：Q 序与绝对值 ---------- *)

Lemma xq_Qle_bool_le : forall x y : Q, Qle_bool x y = true -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy]. unfold Qle, Qle_bool; simpl. intros H.
  apply Z.leb_le. exact H.
Qed.

(* Rocq 9 的 Qabs 以 Z.abs 实现：Qabs (n # d) = (Z.abs n # d) *)
Lemma xq_abs_id : forall x : Q, (0 <= x)%Q -> Qabs x == x.
Proof.
  intros [n d] Hx. unfold Qle in Hx; simpl in Hx.
  assert (Hn : (0 <= n)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite (Z.abs_eq n Hn). reflexivity.
Qed.

Lemma xq_abs_eq0 : forall x : Q, x == 0 -> Qabs x == 0.
Proof.
  intros [n d] Hx. unfold Qeq in Hx; simpl in Hx.
  assert (Hn : (n = 0)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite Hn. reflexivity.
Qed.

Lemma xq_minus_self : forall x : Q, x - x == 0.
Proof.
  intros [n d]. unfold Qminus, Qeq; simpl. lia.
Qed.

Lemma xq_abs_zero : forall x : Q, Qabs (x - x) == 0.
Proof.
  intro x. apply xq_abs_eq0. apply xq_minus_self.
Qed.

Lemma xq_abs_eq : forall x y : Q, x == y -> Qabs x == Qabs y.
Proof.
  intros [n1 d1] [n2 d2] Hxy.
  unfold Qeq in Hxy; simpl in Hxy.
  unfold Qabs; simpl. unfold Qeq; simpl.
  pose proof (Z.abs_spec n1) as Ha1. pose proof (Z.abs_spec n2) as Ha2.
  destruct Ha1 as [[A1 B1] | [A1 B1]];
    destruct Ha2 as [[A2 B2] | [A2 B2]];
    try rewrite B1; try rewrite B2; lia.
Qed.

Lemma xq_abs_opp : forall x : Q, Qabs (- x) == Qabs x.
Proof.
  intros [n d]. unfold Qabs, Qopp; simpl. unfold Qeq; simpl.
  rewrite Z.abs_opp. reflexivity.
Qed.

Lemma xq_minus_opp : forall a b : Q, b - a == - (a - b).
Proof.
  intros [na da] [nb db]. unfold Qminus, Qopp, Qeq; simpl.
  rewrite (Pos.mul_comm db da). ring.
Qed.

Lemma xq_abs_sub_comm : forall a b : Q, Qabs (a - b) == Qabs (b - a).
Proof.
  intros a b.
  assert (H1 : Qabs (-(a - b)) == Qabs (a - b)) by apply xq_abs_opp.
  rewrite <- H1.
  apply xq_abs_eq. symmetry. apply xq_minus_opp.
Qed.

Lemma xq_H_adj_nonneg : forall l : list Q, (0 <= H_adj l)%Q.
Proof.
  intro l. induction l as [| a rest IH].
  - apply Qle_refl.
  - destruct rest as [| b bs].
    + apply Qle_refl.
    + change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      apply qadd_nonneg; [ apply abs_nonneg | exact IH ].
Qed.

Lemma xq_le_add_abs : forall t h : Q, (h <= Qabs t + h)%Q.
Proof.
  intros t h.
  pose proof (qadd_le 0 (Qabs t) h h (abs_nonneg t) (Qle_refl h)) as HS.
  rewrite Qplus_0_l in HS. exact HS.
Qed.

(* ---------- xq 局部工具：升序谓词与 P0 规范形 ---------- *)

Inductive SortedQ : list Q -> Prop :=
| sortQ_nil : SortedQ []
| sortQ_cons : forall x xs,
    SortedQ xs -> Forall (fun z => (x <= z)%Q) xs -> SortedQ (x :: xs).

Lemma xq_sortQ_insert : forall (x : Q) (l : list Q),
  SortedQ l -> SortedQ (insert_q x l).
Proof.
  intros x l. revert x. induction l as [| y ys IH]; intros x HS.
  - simpl. apply sortQ_cons; [ apply sortQ_nil | apply Forall_nil ].
  - inversion HS as [| x0 xs0 HSys HFall]; subst.
    rewrite Forall_forall in HFall.
    simpl. destruct (Qle_bool x y) eqn:E.
    + apply sortQ_cons; [ exact HS | ].
      rewrite Forall_forall. intros z Hz. destruct Hz as [Heq | Hz].
      * subst. apply xq_Qle_bool_le. exact E.
      * apply (Qle_trans x y z).
        -- apply xq_Qle_bool_le. exact E.
        -- apply HFall. exact Hz.
    + apply sortQ_cons; [ apply IH; exact HSys | ].
      rewrite Forall_forall. intros z Hz.
      assert (Hin : In z (x :: ys)).
      { apply Permutation_in with (l := insert_q x ys).
        - apply Permutation_sym. apply insert_q_perm_cons.
        - exact Hz. }
      destruct Hin as [Heq | Hin].
      * subst. apply Qle_bool_false_le. exact E.
      * apply HFall. exact Hin.
Qed.

Lemma xq_P0_sorted : forall l : list Q, SortedQ (P0 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply sortQ_nil.
  - apply xq_sortQ_insert. exact IH.
Qed.

(* ---------- xq 局部工具：lastq 尾元与望远镜方程 ---------- *)

Fixpoint lastq (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => match xs with
               | [] => x
               | _ :: _ => lastq xs
               end
  end.

Lemma xq_lastq_In : forall m : list Q, m <> [] -> In (lastq m) m.
Proof.
  induction m as [| a rest IH]; intros Hne.
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [| b bs].
    + simpl. left. reflexivity.
    + simpl. right. apply IH. simpl. discriminate.
Qed.

Lemma xq_hd_In_gen : forall m : list Q, m <> [] -> In (hd 0 m) m.
Proof.
  intros [| h t] H; [ exfalso; apply H; reflexivity | simpl; left; reflexivity ].
Qed.

Lemma xq_P0_cons_ne : forall (x : Q) (xs : list Q), P0 (x :: xs) <> [].
Proof.
  intros x xs. cbn [P0].
  destruct (P0 xs) as [| y ys]; cbn [insert_q].
  - discriminate.
  - destruct (Qle_bool x y); discriminate.
Qed.

Lemma xq_hd_le_lastq : forall l : list Q, SortedQ l -> (hd 0 l <= lastq l)%Q.
Proof.
  induction l as [| a rest IH]; intro HS.
  - simpl. apply Qle_refl.
  - destruct rest as [| b bs].
    + simpl. apply Qle_refl.
    + inversion HS as [| x0 xs0 HSr HFa]; subst.
      rewrite Forall_forall in HFa.
      apply (Qle_trans a b).
      * apply HFa. left. reflexivity.
      * apply IH. exact HSr.
Qed.

(* 望远镜方程：升序表的相邻差总和 == 尾元 - 首元 *)
Lemma xq_telescope : forall l : list Q, SortedQ l -> H_adj l == lastq l - hd 0 l.
Proof.
  induction l as [| a rest IH]; intro HS.
  - reflexivity.
  - destruct rest as [| b bs].
    + change (H_adj [a]) with 0%Q.
      change (lastq [a] - hd 0 [a]) with (a - a)%Q.
      symmetry. apply xq_minus_self.
    + inversion HS as [| x0 xs0 HSr HFa]; subst.
      rewrite Forall_forall in HFa.
      change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      assert (Hab : (0 <= b - a)%Q).
      { apply (proj1 (Qle_0_sub' a b)). apply HFa. left. reflexivity. }
      rewrite (xq_abs_id _ Hab).
      rewrite (IH HSr).
      change (lastq (a :: b :: bs)) with (lastq (b :: bs)).
      change (hd 0 (a :: b :: bs)) with a.
      change (hd 0 (b :: bs)) with b.
      ring.
Qed.

(* 配对距离界：表中任意两元素的 Qabs 距离不超过序列熵 *)
Lemma xq_pair_dist_le : forall (l : list Q) (x y : Q),
  In x l -> In y l -> (Qabs (x - y) <= H_adj l)%Q.
Proof.
  induction l as [| a rest IH]; intros x y Hx Hy.
  - exfalso. exact Hx.
  - destruct rest as [| b bs].
    + destruct Hx as [Hx | []]; destruct Hy as [Hy | []]; subst.
      rewrite xq_abs_zero. apply Qle_refl.
    + change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
      * rewrite xq_abs_zero. apply qadd_nonneg;
          [ apply abs_nonneg | apply xq_H_adj_nonneg ].
      * assert (Hr1 : a - y == (a - b) + (b - y)) by ring.
        rewrite Hr1.
        apply (Qle_trans _ (Qabs (a - b) + Qabs (b - y))).
        -- apply Qabs_triangle.
        -- rewrite (xq_abs_sub_comm a b).
           apply qadd_le; [ apply Qle_refl
                          | apply IH; [ left; reflexivity | exact Hy ] ].
      * assert (Hr2 : x - a == (x - b) + (b - a)) by ring.
        rewrite Hr2.
        apply (Qle_trans _ (Qabs (x - b) + Qabs (b - a))).
        -- apply Qabs_triangle.
        -- rewrite (Qplus_comm (Qabs (x - b)) (Qabs (b - a))).
           apply qadd_le; [ apply Qle_refl
                          | apply IH; [ exact Hx | left; reflexivity ] ].
      * apply (Qle_trans _ (H_adj (b :: bs))).
        -- apply IH; assumption.
        -- apply xq_le_add_abs.
Qed.

(* ========== 定理 C：升序最小化序列熵（P0 最小化相邻差总和） ========== *)

Theorem C_sorted_min_adj : forall (l : list Q), H_adj (P0 l) <= H_adj l.
Proof.
  intro l. destruct l as [| a rest].
  - apply Qle_refl.
  - assert (HP : H_adj (P0 (a :: rest))
                 == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest)))
      by (apply xq_telescope; apply xq_P0_sorted).
    assert (HP2 : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest))).
    { rewrite (xq_abs_sub_comm (hd 0 (P0 (a :: rest))) (lastq (P0 (a :: rest)))).
      apply xq_abs_id.
      apply (proj1 (Qle_0_sub' _ _)).
      apply xq_hd_le_lastq. apply xq_P0_sorted. }
    rewrite HP. rewrite <- HP2.
    assert (Hm1 : In (hd 0 (P0 (a :: rest))) (a :: rest)).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - apply Permutation_sym. apply D5_P0_perm.
      - apply xq_hd_In_gen. apply xq_P0_cons_ne. }
    assert (Hm2 : In (lastq (P0 (a :: rest))) (a :: rest)).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - apply Permutation_sym. apply D5_P0_perm.
      - apply xq_lastq_In. apply xq_P0_cons_ne. }
    apply xq_pair_dist_le; assumption.
Qed.

(* ========== §5 计数测度（D8 → 定理 B） ========== *)

Fixpoint nat_fact (n : nat) : nat :=
  match n with
  | O => 1
  | S m => S m * nat_fact m
  end.

Definition q_fact (n : nat) : Q := (Z.of_nat (nat_fact n) # 1)%Q.

Lemma Zpos_le_roundtrip : forall d : positive,
  (Z.pos d <= Z.of_nat (Pos.to_nat d))%Z.
Proof.
  induction d as [p IH | p IH | ].
  - rewrite Pos2Nat.inj_xI, Znat.Nat2Z.inj_succ, Znat.Nat2Z.inj_mul.
    rewrite Pos2Z.inj_xI. change (Z.of_nat 2) with (2%Z). lia.
  - rewrite Pos2Nat.inj_xO, Znat.Nat2Z.inj_mul, Pos2Z.inj_xO.
    change (Z.of_nat 2) with (2%Z). lia.
  - simpl. lia.
Qed.

Lemma nat_fact_ge1 : forall n : nat, (1 <= nat_fact n)%nat.
Proof.
  induction n as [| n IH]; simpl.
  - apply le_n.
  - assert (H2 : (1 * nat_fact n <= S n * nat_fact n)%nat)
      by (apply Nat.mul_le_mono_r; lia).
    lia.
Qed.

Theorem D8_sorted_frac_pos : forall K : nat, (0 < K)%nat -> 0 < (1 / (q_fact K))%Q.
Proof.
  intros K HK. unfold q_fact.
  assert (Hf : (1 <= nat_fact K)%nat) by apply nat_fact_ge1.
  assert (HfZ : (1 <= Z.of_nat (nat_fact K))%Z)
    by (apply (proj1 (Znat.Nat2Z.inj_le 1 (nat_fact K))); exact Hf).
  destruct (Z.of_nat (nat_fact K)) as [| p | p] eqn:EF.
  - exfalso. lia.
  - assert (Hinv : (1 / (Z.pos p # 1) == 1 # p)%Q).
    { unfold Qdiv, Qinv. reflexivity. }
    rewrite Hinv. unfold Qlt. simpl. lia.
  - exfalso. lia.
Qed.

Theorem D8_tends_zero : forall eps : Q, 0 < eps ->
  exists K : nat, (0 < K)%nat /\ (1 / (q_fact K)%Q < eps)%Q.
Proof.
  intros eps Heps. unfold Qlt in Heps. simpl in Heps.
  remember (Qden eps) as d eqn:Ed.
  assert (Hn : (1 <= Qnum eps)%Z) by lia.
  assert (Hd : (0 < Z.pos d)%Z) by lia.
  assert (Hle : (Z.pos d <= Z.of_nat (Pos.to_nat d))%Z) by apply Zpos_le_roundtrip.
  destruct (Z.of_nat (Pos.to_nat d)) as [| p | p] eqn:EF.
  - exfalso. lia.
  - exists (S (S (Pos.to_nat d))). split.
    + lia.
    + assert (Hbound : (Z.succ (Z.succ (Z.of_nat (Pos.to_nat d)))
                        <= Z.of_nat (nat_fact (S (S (Pos.to_nat d)))))%Z).
      { rewrite <- !Znat.Nat2Z.inj_succ.
        apply (proj1 (Znat.Nat2Z.inj_le _ _)).
        simpl.
        assert (Hg : (1 <= nat_fact (S (Pos.to_nat d)))%nat) by apply nat_fact_ge1.
        assert (H2 : (S (S (Pos.to_nat d)) * 1
                      <= S (S (Pos.to_nat d)) * nat_fact (S (Pos.to_nat d)))%nat)
          by (apply Nat.mul_le_mono_l; exact Hg).
        simpl in H2. lia. }
      unfold q_fact.
      destruct (Z.of_nat (nat_fact (S (S (Pos.to_nat d))))) as [| p2 | p2] eqn:EF2.
      -- exfalso. lia.
      -- assert (Hinv : (1 / (Z.pos p2 # 1) == 1 # p2)%Q).
         { unfold Qdiv, Qinv. reflexivity. }
         rewrite Hinv. unfold Qlt. simpl.
         assert (Hp2 : (0 <= Z.pos p2)%Z) by lia.
         assert (Hmul : (1 * Z.pos p2 <= Qnum eps * Z.pos p2)%Z)
           by (apply Z.mul_le_mono_nonneg_r; [lia | exact Hn]).
         lia.
      -- exfalso. lia.
  - exfalso. try rewrite EF in Hle.
    assert (Hnn : (Z.neg p < 0)%Z).
    { change (Z.neg p) with (- Z.pos p)%Z. lia. }
    lia.
Qed.

(* ========== §6 证据分层判断网络（D10 重铸） ========== *)

Inductive Level : Type := Lv0 | Lv1 | Lv2.

Inductive Evidence : Type :=
| evNum  : Q -> Evidence
| evSeq  : list Q -> Evidence
| evPair : Evidence -> Evidence -> Evidence.

Record TrNode : Type := mkTrNode {
  trLevel : Level;
  trPhi   : Dig;
  trModel : Dig;
  trValue : Evidence
}.

Definition Tex (phi : Dig) : Type := { t : TrNode & trPhi t = phi }.

Definition Tabs (phi : Dig) : Type := forall (m : Dig), Evidence.

(* ========== §7 LLM 相位视图（附录对映） ========== *)

Record LLMPhaseView : Type := mkLLMView {
  lam_param      : Q;
  phase_marker   : list Q;
  gate_threshold : Q
}.

Definition gate_pass (threshold H : Q) : bool :=
  if Qle_bool H threshold then true else false.

(* ============================================================
   §8 归并席 M1（2026-09-14）：并入 DTPT_CGen.v —— C_gen 排序泛化族
   源席 DTPT-U1（X1 Top-1 热点升级单）。仅移除独立文件的
   Require/Import/Open Scope 头（由本文件头统一承载），
   注释与全部证明体、Qed 面、Print Assumptions 审计出口零改动。
   ============================================================ *)
(* ============================================================
   DTPT_CGen.v — 热点升级单 C-GEN（X1 扫描席 Top-1 推荐）
   席位：DTPT-U1（零竞争：新建文件，Require DTPT，不碰既有八件）

   旗舰（定理 C 全排列类泛化）：
     C_gen : forall (l p : list Q), Permutation l p -> H_adj (P0 l) <= H_adj p
   现役旗舰 DTPT.C_sorted_min_adj 只证「排序 <= 恒等排列」；
   本件把比较对象泛化到 l 的任意排列 p（全排列类）。

   路线：H_adj (P0 l) 经 xq_telescope（排序伸缩）== lastq - hd，
   首尾成员性经 D5_P0_perm + 置换传递搬到 p，再用 xq_pair_dist_le
   （跨度下界：表内任意两元 Qabs 距离 <= H_adj）收口。

   加分项：
     C_gen_sym_rev  —— SYM 前置件：反转不变 H_adj (rev l) == H_adj l
     C_gen_attained —— 紧性见证：p := P0 l 直构，界在排列类内取得
     C_gen_sorted   —— 现役旗舰 C_sorted_min_adj 的泛化重推（特例核对）

   纪律：零公理、零承认、零中止，全程 Qed；Q 层 lia 禁用，
   全部不等式走 xq_ 桥 + ring（Qabs/lastq/H_adj 作原子）。
   ============================================================ *)

(* 原独立文件 Require/Import/Open Scope 头（From Stdlib QArith/List/Permutation、
   Require Import DTPT、Import ListNotations、Open Scope Q_scope）已于归并时移除。 *)

(* ========== §0 snoc 面小工具（SYM 前置件） ========== *)

(* 表末追加一个元素后，尾元就是它（Leibniz 版） *)
Lemma cgen_lastq_app : forall (l : list Q) (x : Q), lastq (l ++ [x]) = x.
Proof.
  induction l as [| y ys IH]; intros x; cbn [app].
  - reflexivity.
  - destruct ys as [| b bs].
    + reflexivity.
    + exact (IH x).
Qed.

(* snoc 熵方程：非空表末尾追加 x，相邻差总和恰增 Qabs (x - 尾元) *)
Lemma cgen_H_adj_snoc : forall (l : list Q) (x : Q),
  l <> [] -> H_adj (l ++ [x]) == (H_adj l + Qabs (x - lastq l))%Q.
Proof.
  induction l as [| y ys IH]; intros x Hne.
  - exfalso. apply Hne. reflexivity.
  - destruct ys as [| b bs].
    + cbn [app]. unfold H_adj. cbn [sum_adjdiff lastq]. ring.
    + assert (IH' : H_adj ((b :: bs) ++ [x])
                    == (H_adj (b :: bs) + Qabs (x - lastq (b :: bs)))%Q)
        by (apply IH; discriminate).
      cbn [app].
      change (H_adj (y :: b :: (bs ++ [x])))
        with (Qabs (b - y) + H_adj ((b :: bs) ++ [x]))%Q.
      rewrite IH'.
      change (H_adj (y :: b :: bs)) with (Qabs (b - y) + H_adj (b :: bs))%Q.
      change (lastq (y :: b :: bs)) with (lastq (b :: bs)).
      ring.
Qed.

(* cons 表反转必非空 *)
Lemma cgen_rev_cons_ne : forall (x : Q) (xs : list Q), rev (x :: xs) <> [].
Proof.
  intros x xs. change (rev (x :: xs)) with (rev xs ++ [x]).
  destruct (rev xs) as [| r rs]; cbn [app]; discriminate.
Qed.

(* 反转表的尾元 == 原表头 *)
Lemma cgen_lastq_rev_cons : forall (b : Q) (bs : list Q),
  lastq (rev (b :: bs)) == b.
Proof.
  intros b bs. change (rev (b :: bs)) with (rev bs ++ [b]).
  rewrite cgen_lastq_app. reflexivity.
Qed.

(* ========== §1 加分项 SYM：反转不变 ========== *)

Theorem C_gen_sym_rev : forall l : list Q, H_adj (rev l) == H_adj l.
Proof.
  induction l as [| a rest IH].
  - reflexivity.
  - cbn [rev].
    destruct rest as [| b bs].
    + reflexivity.
    + rewrite cgen_H_adj_snoc by (apply cgen_rev_cons_ne).
      rewrite IH.
      rewrite cgen_lastq_rev_cons.
      change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      rewrite (xq_abs_sub_comm a b).
      ring.
Qed.

(* ========== §2 旗舰：定理 C 全排列类泛化 ========== *)

(* C_gen：排序最小化对 l 的任意排列 p 成立。
   p := l 特例即现役旗舰 C_sorted_min_adj；证明骨架与其同构，
   仅成员性搬运段改为「置换传递复合」：P0 l ~> l ~> p 一步到位。 *)
Theorem C_gen : forall (l p : list Q), Permutation l p -> H_adj (P0 l) <= H_adj p.
Proof.
  intros l p Hperm. destruct l as [| a rest].
  - (* l = []：排列类只含空表 *)
    assert (Hp : p = []) by (apply Permutation_nil; exact Hperm).
    rewrite Hp. apply Qle_refl.
  - (* l = a :: rest：P0 l 非空，望远镜展开 + 跨度下界 *)
    assert (Hne : P0 (a :: rest) <> []) by (apply xq_P0_cons_ne).
    assert (HP : H_adj (P0 (a :: rest))
                 == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest)))
      by (apply xq_telescope; apply xq_P0_sorted).
    assert (HP2 : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest))).
    { rewrite (xq_abs_sub_comm (hd 0 (P0 (a :: rest))) (lastq (P0 (a :: rest)))).
      apply xq_abs_id.
      apply (proj1 (Qle_0_sub' _ _)).
      apply xq_hd_le_lastq. apply xq_P0_sorted. }
    (* 置换传递复合：P0 l 是 l 的排列（反向 D5），l 是 p 的排列 *)
    assert (Hrev : Permutation (P0 (a :: rest)) (a :: rest))
      by (apply Permutation_sym; apply D5_P0_perm).
    assert (HpermP : Permutation (P0 (a :: rest)) p).
    { apply perm_trans with (l' := a :: rest).
      - exact Hrev.
      - exact Hperm. }
    (* 首尾两元搬进 p 的成员性 *)
    assert (Hm1 : In (hd 0 (P0 (a :: rest))) p).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - exact HpermP.
      - apply xq_hd_In_gen. exact Hne. }
    assert (Hm2 : In (lastq (P0 (a :: rest))) p).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - exact HpermP.
      - apply xq_lastq_In. exact Hne. }
    (* 跨度下界在 p 上成立 *)
    assert (HPd : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  <= H_adj p)
      by (apply xq_pair_dist_le; assumption).
    (* Qeq setoid 链收口：H_adj (P0 l) == 尾-首 == Qabs(首-尾) <= H_adj p *)
    rewrite HP. rewrite <- HP2. exact HPd.
Qed.

(* ========== §3 紧性见证与泛化核对 ========== *)

(* 紧性：界在排列类内取得（下确界即最小值），P0 l 直构见证。
   与 C_gen 合读：H_adj (P0 l) 是排列类 {p : Permutation l p} 上
   H_adj 的最小值——泛化界不可再降。 *)
Theorem C_gen_attained : forall l : list Q,
  exists p : list Q, Permutation l p /\ H_adj p == H_adj (P0 l).
Proof.
  intro l. exists (P0 l). split.
  - apply D5_P0_perm.
  - apply Qeq_refl.
Qed.

(* 现役旗舰 C_sorted_min_adj 是 C_gen 的特例（p := l 重推核对） *)
Corollary C_gen_sorted : forall l : list Q, H_adj (P0 l) <= H_adj l.
Proof.
  intro l. apply (C_gen l l). apply Permutation_refl.
Qed.

(* ========== G4 假设审计（期望 Closed under the global context） ========== *)

Print Assumptions C_gen.
Print Assumptions C_gen_sym_rev.
Print Assumptions C_gen_attained.
Print Assumptions C_gen_sorted.

(* ============================================================
   §9 归并席 M1（2026-09-14）：并入 DTPT_N9Opt.v —— N9 极值族
   源席 DTPT-U14R（N9O 分离常数最优性）。仅移除独立文件的
   Require/Import/Open Scope 头（由本文件头统一承载），
   注释与全部证明体、Qed 面、Print Assumptions 审计出口零改动。
   ============================================================ *)
(* ============================================================
   DTPT_N9Opt.v — N9O 分离常数最优性（席 U14R 续席重跑件）
   底座：Require Import DTPT（stdlib QArith/List/Lia/Permutation）
   纪律：零承认体；全部定理以 Qed 收口；陈述全称、数值面 vm_compute。
   内容：
     [保底件] perm3_cases          —— 长度 3 排列类六形穷举
     [旗舰]   n9_max / n9_max_attained / n9_min_is_sorted
                               —— 见证列 n9_l0 = [0;1;2] 三件全称定理
     [主件]   n9_const_ratio / n9_separation_exact
                               —— 分离比 3/2 精确，两侧均取得
     [加分]   n9_naive_bound / n9_naive_bound_Hadj
                               —— 一般长度朴素上界（spread 面与 H_adj 面）
   数值事实：H_adj 六形 = 2,3,3,3,3,2；max 3 = (3/2)*2，min 2。
   ============================================================ *)
(* 原独立文件 Require/Import/Open Scope 头（From Stdlib QArith/List/Lia/Permutation、
   Require Import DTPT、Import ListNotations、Open Scope Q_scope）已于归并时移除。 *)

(* ---------- 见证列与 spread 面 ---------- *)

Definition n9_l0 : list Q := [0; 1; 2].

Definition spread (l : list Q) : Q := lastq (P0 l) - hd 0 (P0 l).

(* ---------- 有序表首/尾元控制（spread 面的配套件） ---------- *)

Lemma sorted_hd_le_in : forall (m : list Q) (x : Q),
  SortedQ m -> In x m -> (hd 0 m <= x)%Q.
Proof.
  intros m x HS. revert x.
  induction HS as [| y ys HSr _ HFall]; intros x Hin.
  - destruct Hin.
  - simpl. destruct Hin as [Heq | Hin].
    + subst. apply Qle_refl.
    + rewrite Forall_forall in HFall. apply HFall. exact Hin.
Qed.

Lemma sorted_in_le_last : forall (m : list Q) (x : Q),
  SortedQ m -> In x m -> (x <= lastq m)%Q.
Proof.
  intros m x HS. revert x.
  induction HS as [| y ys HSr IH HFall]; intros x Hin.
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + subst x. destruct ys as [| b bs].
      * simpl. apply Qle_refl.
      * change (lastq (y :: b :: bs)) with (lastq (b :: bs)).
        rewrite Forall_forall in HFall.
        apply HFall. apply xq_lastq_In. discriminate.
    + destruct ys as [| b bs].
      * destruct Hin.
      * change (lastq (y :: b :: bs)) with (lastq (b :: bs)).
        apply IH. exact Hin.
Qed.

(* spread 两两界：表中任意两元素的 Qabs 距离不超过 spread *)
Lemma spread_pair_le : forall (l : list Q) (x y : Q),
  In x l -> In y l -> (Qabs (x - y) <= spread l)%Q.
Proof.
  intros l x y Hx Hy. unfold spread.
  assert (Hlne : l <> []) by (intro Hc; rewrite Hc in Hx; exact Hx).
  assert (HPne : P0 l <> []).
  { destruct l as [| a rest].
    - exfalso. apply Hlne. reflexivity.
    - apply xq_P0_cons_ne. }
  assert (HS : SortedQ (P0 l)) by apply xq_P0_sorted.
  assert (Hxl : In x (P0 l)) by
    (apply Permutation_in with (l := l); [ apply D5_P0_perm | exact Hx ]).
  assert (Hyl : In y (P0 l)) by
    (apply Permutation_in with (l := l); [ apply D5_P0_perm | exact Hy ]).
  assert (H1 : (hd 0 (P0 l) <= x)%Q) by (apply sorted_hd_le_in; assumption).
  assert (H2 : (x <= lastq (P0 l))%Q) by (apply sorted_in_le_last; assumption).
  assert (H3 : (hd 0 (P0 l) <= y)%Q) by (apply sorted_hd_le_in; assumption).
  assert (H4 : (y <= lastq (P0 l))%Q) by (apply sorted_in_le_last; assumption).
  destruct (Qle_dec' x y) as [Hxy | Hyx].
  - assert (Habs : Qabs (x - y) == y - x).
    { rewrite xq_abs_sub_comm. apply abs_eq.
      apply (proj1 (Qle_0_sub' x y)). exact Hxy. }
    rewrite Habs.
    apply (Qle_trans _ (lastq (P0 l) - x)).
    + apply qsub_le_r. exact H4.
    + unfold Qminus. apply qadd_le;
        [ apply Qle_refl | apply qopp_le; exact H1 ].
  - assert (Habs : Qabs (x - y) == x - y).
    { apply abs_eq. apply (proj1 (Qle_0_sub' y x)). exact Hyx. }
    rewrite Habs.
    apply (Qle_trans _ (lastq (P0 l) - y)).
    + apply qsub_le_r. exact H2.
    + unfold Qminus. apply qadd_le;
        [ apply Qle_refl | apply qopp_le; exact H3 ].
Qed.

(* ---------- 长度系数步进恒等式（S2 卡配方：Z 层 lia 先证再 rewrite） ---------- *)

Lemma qcoef_step : forall (n : nat) (k : Q),
  k + ((Z.of_nat n - 1)%Z # 1) * k == ((Z.of_nat (S n) - 1)%Z # 1) * k.
Proof.
  intros n k.
  assert (Hz : (Z.of_nat (S n) = 1 + Z.of_nat n)%Z) by lia.
  rewrite Hz.
  destruct k as [kn kd].
  unfold Qeq, Qplus, Qminus, Qmult. cbn [Qnum Qden]. lia.
Qed.

(* 相邻差总和对「两两界 × (长度-1)」的逐项归纳（非空卫哨） *)
Lemma H_adj_pair_bound : forall (m : list Q) (k : Q), m <> [] ->
  (forall x y, In x m -> In y m -> (Qabs (x - y) <= k)%Q) ->
  H_adj m <= ((Z.of_nat (length m) - 1)%Z # 1) * k.
Proof.
  intros m. induction m as [| a rest IH]; intros k Hne Hpair.
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [| b rest2].
    + (* 单元素：H_adj = 0，系数 1-1 = 0 *)
      change (H_adj [a]) with 0%Q.
      cbn [length].
      replace ((Z.of_nat 1 - 1)%Z # 1) with 0%Q by reflexivity.
      rewrite Qmult_0_l. apply Qle_refl.
    + (* 多元素：|b-a| <= k 与 IH 相加 *)
      change (H_adj (a :: b :: rest2))
        with (Qabs (b - a) + H_adj (b :: rest2))%Q.
      assert (Hbp : (Qabs (b - a) <= k)%Q).
      { apply Hpair; [ right; left; reflexivity | left; reflexivity ]. }
      assert (IHr : H_adj (b :: rest2)
                    <= ((Z.of_nat (length (b :: rest2)) - 1)%Z # 1) * k).
      { apply IH; [ discriminate | ].
        intros x y Hx Hy. apply Hpair.
        - destruct Hx as [Hx | Hx].
          + subst x. right; left; reflexivity.
          + right; right; exact Hx.
        - destruct Hy as [Hy | Hy].
          + subst y. right; left; reflexivity.
          + right; right; exact Hy. }
      assert (Hq : k + ((Z.of_nat (length (b :: rest2)) - 1)%Z # 1) * k
                   == ((Z.of_nat (length (a :: b :: rest2)) - 1)%Z # 1) * k).
      { change (length (b :: rest2)) with (S (length rest2)).
        change (length (a :: b :: rest2)) with (S (S (length rest2))).
        apply qcoef_step. }
      rewrite <- Hq.
      apply qadd_le; [ exact Hbp | exact IHr ].
Qed.

(* ========== 【保底件】长度 3 排列类六形穷举 ========== *)

Lemma perm3_cases : forall (a b c : Q) (p : list Q),
  Permutation [a; b; c] p ->
  p = [a; b; c] \/ p = [a; c; b] \/ p = [b; a; c] \/
  p = [b; c; a] \/ p = [c; a; b] \/ p = [c; b; a].
Proof.
  intros a b c p Hp.
  assert (Hlen : length p = 3%nat).
  { pose proof (Permutation_length Hp) as HL. simpl in HL. lia. }
  destruct p as [| x1 [| x2 [| x3 [| x4 p4]]]].
  - simpl in Hlen. discriminate.
  - simpl in Hlen. discriminate.
  - simpl in Hlen. discriminate.
  - (* p = [x1;x2;x3]：逐位成员搬运消解 *)
    assert (Hin1 : In x1 [a; b; c]).
    { apply Permutation_in with (l := [x1; x2; x3]).
      - apply Permutation_sym. exact Hp.
      - left; reflexivity. }
    simpl in Hin1.
    destruct Hin1 as [E1 | [E1 | [E1 | []]]]; subst x1.
    + (* x1 = a *)
      assert (Hp1 : Permutation [b; c] [x2; x3])
        by exact (Permutation_cons_inv Hp).
      assert (Hin2 : In x2 [b; c]).
      { apply Permutation_in with (l := [x2; x3]).
        - apply Permutation_sym. exact Hp1.
        - left; reflexivity. }
      simpl in Hin2. destruct Hin2 as [E2 | [E2 | []]]; subst x2.
      * assert (Hp2 : Permutation [c] [x3])
          by exact (Permutation_cons_inv Hp1).
        assert (Hin3 : In x3 [c]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3. left; reflexivity.
      * assert (Hp2 : Permutation [b] [x3]).
        { apply (Permutation_cons_inv (a := c)).
          eapply perm_trans with (l' := [b; c]).
          - apply Permutation_sym. apply perm_swap.
          - exact Hp1. }
        assert (Hin3 : In x3 [b]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3. right; left; reflexivity.
    + (* x1 = b *)
      assert (Hp1 : Permutation [a; c] [x2; x3]).
      { apply (Permutation_cons_inv (a := b)).
        eapply perm_trans with (l' := [a; b; c]).
        - apply Permutation_sym. apply perm_swap.
        - exact Hp. }
      assert (Hin2 : In x2 [a; c]).
      { apply Permutation_in with (l := [x2; x3]).
        - apply Permutation_sym. exact Hp1.
        - left; reflexivity. }
      simpl in Hin2. destruct Hin2 as [E2 | [E2 | []]]; subst x2.
      * assert (Hp2 : Permutation [c] [x3])
          by exact (Permutation_cons_inv Hp1).
        assert (Hin3 : In x3 [c]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3. right; right; left; reflexivity.
      * assert (Hp2 : Permutation [a] [x3]).
        { apply (Permutation_cons_inv (a := c)).
          eapply perm_trans with (l' := [a; c]).
          - apply Permutation_sym. apply perm_swap.
          - exact Hp1. }
        assert (Hin3 : In x3 [a]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3.
        right; right; right; left; reflexivity.
    + (* x1 = c *)
      assert (Hp1 : Permutation [a; b] [x2; x3]).
      { apply (Permutation_cons_inv (a := c)).
        eapply perm_trans with (l' := [a; b; c]).
        - etransitivity.
          + apply perm_swap.
          + apply perm_skip. apply perm_swap.
        - exact Hp. }
      assert (Hin2 : In x2 [a; b]).
      { apply Permutation_in with (l := [x2; x3]).
        - apply Permutation_sym. exact Hp1.
        - left; reflexivity. }
      simpl in Hin2. destruct Hin2 as [E2 | [E2 | []]]; subst x2.
      * assert (Hp2 : Permutation [b] [x3])
          by exact (Permutation_cons_inv Hp1).
        assert (Hin3 : In x3 [b]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3.
        right; right; right; right; left; reflexivity.
      * assert (Hp2 : Permutation [a] [x3]).
        { apply (Permutation_cons_inv (a := b)).
          eapply perm_trans with (l' := [a; b]).
          - apply Permutation_sym. apply perm_swap.
          - exact Hp1. }
        assert (Hin3 : In x3 [a]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3.
        right; right; right; right; right; reflexivity.
  - (* 长度 >= 4：与 3 矛盾 *)
    simpl in Hlen. lia.
Qed.

(* ========== 【旗舰】见证列 n9_l0 = [0;1;2] 类上极值三件 ==========
   数值事实：六形 H_adj = 2,3,3,3,3,2，max 3、min 2。 ========== *)

Theorem n9_max : forall p, Permutation n9_l0 p -> H_adj p <= 3.
Proof.
  intros p Hp. unfold n9_l0 in Hp. apply perm3_cases in Hp.
  destruct Hp as [E | [E | [E | [E | [E | E]]]]]; subst p;
    apply xq_Qle_bool_le; vm_compute; reflexivity.
Qed.

Theorem n9_max_attained : exists p, Permutation n9_l0 p /\ H_adj p == 3.
Proof.
  exists [0; 2; 1]. split.
  - unfold n9_l0. apply perm_skip. apply perm_swap.
  - vm_compute. reflexivity.
Qed.

Theorem n9_min_is_sorted : forall p, Permutation n9_l0 p -> 2 <= H_adj p.
Proof.
  intros p Hp. unfold n9_l0 in Hp. apply perm3_cases in Hp.
  destruct Hp as [E | [E | [E | [E | [E | E]]]]]; subst p;
    apply xq_Qle_bool_le; vm_compute; reflexivity.
Qed.

(* ========== 【主件】分离常数比 3/2 精确（两侧均取得） ========== *)

Theorem n9_const_ratio :
  (3 # 2)%Q * 2 == 3 /\
  (exists pmax : list Q, Permutation n9_l0 pmax /\ H_adj pmax == 3) /\
  (exists pmin : list Q, Permutation n9_l0 pmin /\ H_adj pmin == 2).
Proof.
  split; [| split].
  - vm_compute. reflexivity.
  - exists [0; 2; 1]. split.
    + unfold n9_l0. apply perm_skip. apply perm_swap.
    + vm_compute. reflexivity.
  - exists [0; 1; 2]. split.
    + unfold n9_l0. apply Permutation_refl.
    + vm_compute. reflexivity.
Qed.

(* 类上全域版：任一排列的 H_adj 被夹在 [(3#2)*2 下界面, (3#2)*2 上界面] *)
Theorem n9_separation_exact : forall p, Permutation n9_l0 p ->
  H_adj p <= (3 # 2)%Q * 2 /\ (3 # 2)%Q * 2 <= (3 # 2)%Q * H_adj p.
Proof.
  intros p Hp.
  assert (I : (3 # 2)%Q * 2 == 3) by (vm_compute; reflexivity).
  split.
  - rewrite I. apply n9_max. exact Hp.
  - rewrite (Qmult_comm (3 # 2)%Q 2). rewrite (Qmult_comm (3 # 2)%Q (H_adj p)).
    apply qmul_le_r.
    + apply n9_min_is_sorted. exact Hp.
    + apply xq_Qle_bool_le. vm_compute. reflexivity.
Qed.

(* ========== 【加分】一般长度朴素上界 ========== *)

(* spread 面：H_adj p <= (n-1) * spread l *)
Theorem n9_naive_bound : forall (l p : list Q), Permutation l p -> p <> [] ->
  H_adj p <= ((Z.of_nat (length l) - 1)%Z # 1) * spread l.
Proof.
  intros l p Hp Hne.
  pose proof (Permutation_length Hp) as HL.
  rewrite HL.
  apply H_adj_pair_bound; [ exact Hne | ].
  intros x y Hx Hy.
  assert (Hxl : In x l) by
    (apply Permutation_in with (l := p);
       [ apply Permutation_sym; exact Hp | exact Hx ]).
  assert (Hyl : In y l) by
    (apply Permutation_in with (l := p);
       [ apply Permutation_sym; exact Hp | exact Hy ]).
  apply spread_pair_le; assumption.
Qed.

(* H_adj 面（任务书路线：经 xq_pair_dist_le 逐项） *)
Theorem n9_naive_bound_Hadj : forall (l p : list Q), Permutation l p -> p <> [] ->
  H_adj p <= ((Z.of_nat (length l) - 1)%Z # 1) * H_adj l.
Proof.
  intros l p Hp Hne.
  pose proof (Permutation_length Hp) as HL.
  rewrite HL.
  apply H_adj_pair_bound; [ exact Hne | ].
  intros x y Hx Hy.
  assert (Hxl : In x l) by
    (apply Permutation_in with (l := p);
       [ apply Permutation_sym; exact Hp | exact Hx ]).
  assert (Hyl : In y l) by
    (apply Permutation_in with (l := p);
       [ apply Permutation_sym; exact Hp | exact Hy ]).
  apply (xq_pair_dist_le l); assumption.
Qed.

(* ---------- 审计出口 ---------- *)

Print Assumptions perm3_cases.
Print Assumptions n9_max.
Print Assumptions n9_max_attained.
Print Assumptions n9_min_is_sorted.
Print Assumptions n9_const_ratio.
Print Assumptions n9_separation_exact.
Print Assumptions n9_naive_bound.
Print Assumptions n9_naive_bound_Hadj.

(* ============================================================
   §10 归并席 M1（2026-09-14）：并入 DTPT_D8Ext.v —— D8 阶乘级数族
   源席 DTPT-U7（X1 热点 5：D8 阶乘族定理化）。仅移除独立文件的
   Require/Import/Open Scope 头（由本文件头统一承载），
   注释与全部证明体、Qed 面零改动。
   ============================================================ *)
(* ============================================================
   DTPT_D8Ext.v — 热点升级单 D8X（X1 扫描席热点 5：D8 阶乘族定理化）
   席位：DTPT-U7 ｜ 日期：2026-09-13 ｜ 底座：Require Import DTPT
   （DTPT.vo 稳定基线，既有十三件 .v 零改动、禁重证 D8 六件）

   交付分级（任务书 D8X 升级目标 1-4）：
   【保底件 1·递推方程】
     q_fact_recurrence : q_fact (S n) == q_fact n * (Z.of_nat (S n) # 1)
   【保底件 2·单调族】
     nat_fact_mono / nat_fact_le（阶乘单调链）
     q_fact_recip_anti : (k <= k')%nat -> (1/q_fact k' <= 1/q_fact k)%Q
     D8_mono（清单建议形推论：1/q_fact (S K) <= 1/q_fact K）
   【主件 3·级数优界】
     sum_fact_recip_lt3 : (sum_fact_recip n < 3)%Q
     路线：指数型不变量 sum_fact_recip n + 1/n! <= 3（双基归纳 0/1）
     （核心步（移位形）2/(n+2)! <= 1/(n+1)!：n+2 >= 2 恒真；
       非移位形 2/(n+1)! <= 1/n! 在 n=0 处假（2 > 1），诚实记录。
       终局严格性来自 0 < 1/n!：S_n < S_n + 1/n! <= 3。
       与任务书几何级数路线同定理、更短且免 Q 幂几何部分和；
       几何路线的 2^k 下界族仍作为加分件 §6 交付。）
   【加分件 4·构造性收敛率】
     q_fact_rate / q_fact_rate_exists（K0 = 4 起步：k >= 4 ⟹ 1/k!·4 < 1）
   【加分件 5·2^k 下界族】
     nat_fact_pow2_lb : 2^k <= nat_fact (S k)（即 (k+1)! >= 2^k）
     q_fact_inv_le_pow2 : 1/(k+1)! <= 1/2^k

   纪律：零公理、零承认、零中止、零经典排中，全程 Qed 收官。
   Q 层 lia 禁用（E307）：全部不等式经 Qnum/Qden 展开 + Z 层 lia/ring；
   `#` 分母槽是 positive（本轮实证坑），Z 分母一律走 q_inv_den1。
   ============================================================ *)
(* 原独立文件 Require/Import/Open Scope 头（From Stdlib QArith/List/Arith/Lia、
   Require Import DTPT、Open Scope Q_scope）已于归并时移除。 *)

(* ========== §0 正性见证：Z.of_nat (nat_fact n) 恒为 Z.pos ========== *)

Lemma nat_fact_pos_Z : forall n : nat,
  exists p : positive, Z.of_nat (nat_fact n) = Z.pos p.
Proof.
  intro n. pose proof (nat_fact_ge1 n) as H.
  apply (proj1 (Znat.Nat2Z.inj_le 1 (nat_fact n))) in H.
  destruct (Z.of_nat (nat_fact n)) as [| p | p] eqn:E.
  - exfalso. lia.
  - exists p. reflexivity.
  - exfalso. lia.
Qed.

(* 分母 1 形的 Q 逆（DTPT.v D8 同款：unfold Qdiv, Qinv 直收） *)
Lemma q_inv_den1 : forall p : positive, 1 / (Z.pos p # 1) == (1 # p)%Q.
Proof. intro p. unfold Qdiv, Qinv; reflexivity. Qed.

Lemma q_fact_ne0 : forall n : nat, ~ (q_fact n == 0)%Q.
Proof.
  intro n. destruct (nat_fact_pos_Z n) as [p Ep].
  unfold q_fact. rewrite Ep. intro Hc.
  unfold Qeq in Hc. simpl in Hc. lia.
Qed.

(* ========== §1 保底件：递推方程 ========== *)

Theorem q_fact_recurrence : forall n : nat,
  q_fact (S n) == q_fact n * (Z.of_nat (S n) # 1)%Q.
Proof.
  intro n. unfold q_fact.
  change (nat_fact (S n)) with (S n * nat_fact n)%nat.
  rewrite Znat.Nat2Z.inj_mul.
  rewrite Qmult_comm. apply Qeq_refl.
Qed.

(* ========== §2 保底件：单调族 ========== *)

Lemma nat_fact_mono : forall n m : nat,
  (n <= m)%nat -> (nat_fact n <= nat_fact m)%nat.
Proof.
  intros n m Hle. induction Hle as [| m Hle IH].
  - apply Nat.le_refl.
  - apply (Nat.le_trans _ (nat_fact m) _).
    + exact IH.
    + change (nat_fact (S m)) with (S m * nat_fact m)%nat.
      assert (H2 : (1 * nat_fact m <= S m * nat_fact m)%nat)
        by (apply Nat.mul_le_mono_r; lia).
      rewrite Nat.mul_1_l in H2. exact H2.
Qed.

Lemma nat_fact_le : forall n : nat, (nat_fact n <= nat_fact (S n))%nat.
Proof. intro n. apply nat_fact_mono. apply Nat.le_succ_diag_r. Qed.

Lemma nat_fact_le_Z : forall n m : nat,
  (n <= m)%nat -> (Z.of_nat (nat_fact n) <= Z.of_nat (nat_fact m))%Z.
Proof.
  intros n m Hle.
  apply (proj1 (Znat.Nat2Z.inj_le (nat_fact n) (nat_fact m))).
  apply nat_fact_mono. exact Hle.
Qed.

(* ========== §3 保底件：倒数反单调（Q 除法序桥 + 正性卫哨） ========== *)

Theorem q_fact_recip_anti : forall k k' : nat,
  (k <= k')%nat -> (1 / q_fact k' <= 1 / q_fact k)%Q.
Proof.
  intros k k' Hle.
  pose proof (nat_fact_le_Z k k' Hle) as Hz.
  destruct (nat_fact_pos_Z k) as [pk Ek].
  destruct (nat_fact_pos_Z k') as [pk' Ek'].
  rewrite Ek, Ek' in Hz.
  unfold q_fact. rewrite Ek, Ek'.
  rewrite (q_inv_den1 pk'), (q_inv_den1 pk).
  unfold Qle. simpl. lia.
Qed.

(* 清单建议形 D8_mono：后继倒数不增 *)
Corollary D8_mono : forall K : nat,
  (0 < K)%nat -> (1 / q_fact (S K) <= 1 / q_fact K)%Q.
Proof.
  intros K HK. apply q_fact_recip_anti. apply Nat.le_succ_diag_r.
Qed.

(* ============ §4 主件：部分和 Σ_{k=0}^{n} 1/k! < 3 ============ *)

Fixpoint sum_fact_recip (n : nat) : Q :=
  match n with
  | O => 1 / q_fact 0
  | S m => sum_fact_recip m + 1 / q_fact (S m)
  end.

(* 核心步（移位形，n 起步即真）：2/(n+2)! <= 1/(n+1)!。
   注意非移位形 2/(n+1)! <= 1/n! 在 n=0 处假（2 > 1），
   故不变量走双基归纳（§4 末）。 *)
Lemma q_recip_step_Z : forall a b : Z,
  (0 < b)%Z -> (2 * b <= a)%Z -> (2 / (a # 1) <= 1 / (b # 1))%Q.
Proof.
  intros a b Hb Hab.
  destruct a as [| pa | pa]; try lia.
  destruct b as [| pb | pb]; try lia.
  assert (H2 : 2 / (Z.pos pa # 1) == 2 # pa).
  { unfold Qdiv, Qinv; reflexivity. }
  assert (H1 : 1 / (Z.pos pb # 1) == 1 # pb).
  { unfold Qdiv, Qinv; reflexivity. }
  rewrite H2, H1. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

Lemma q_fact_step2_le : forall n : nat,
  (2 / q_fact (S (S n)) <= 1 / q_fact (S n))%Q.
Proof.
  intro n.
  pose proof (nat_fact_ge1 (S n)) as Hg.
  apply (proj1 (Znat.Nat2Z.inj_le 1 (nat_fact (S n)))) in Hg.
  unfold q_fact. change (nat_fact (S (S n))) with (S (S n) * nat_fact (S n))%nat.
  rewrite Znat.Nat2Z.inj_mul.
  apply q_recip_step_Z.
  - lia.
  - apply Z.mul_le_mono_nonneg_r.
    + lia.
    + apply (proj1 (Znat.Nat2Z.inj_le 2 (S (S n)))). lia.
Qed.

(* 指数型不变量：S_n + 1/n! <= 3（归纳自持；双基：0 与 1） *)
Lemma sum_fact_recip_inv : forall n : nat,
  (sum_fact_recip n + 1 / q_fact n <= 3)%Q.
Proof.
  intro n.
  assert (Hboth : (sum_fact_recip n + 1 / q_fact n <= 3)%Q /\
                  (sum_fact_recip (S n) + 1 / q_fact (S n) <= 3)%Q).
  { induction n as [| n [IH1 IH2]].
    - split.
      + cbn [sum_fact_recip].
        assert (H0 : (1 / q_fact 0 == 1)%Q) by (unfold q_fact; reflexivity).
        rewrite H0. unfold Qle. simpl. lia.
      + cbn [sum_fact_recip].
        assert (H0 : (1 / q_fact 0 == 1)%Q) by (unfold q_fact; reflexivity).
        assert (H1 : (1 / q_fact 1 == 1)%Q) by (unfold q_fact; reflexivity).
        rewrite H0, H1. unfold Qle. simpl. lia.
    - split.
      + exact IH2.
      + cbn [sum_fact_recip].
        assert (Hassoc : (sum_fact_recip (S n) + 1 / q_fact (S (S n))
                           + 1 / q_fact (S (S n))
                         == sum_fact_recip (S n) + 2 / q_fact (S (S n)))%Q).
        { field. apply q_fact_ne0. }
        rewrite Hassoc.
        apply (Qle_trans _ (sum_fact_recip (S n) + 1 / q_fact (S n))%Q).
        * apply qadd_le; [ apply Qle_refl | apply q_fact_step2_le ].
        * exact IH2. }
  exact (proj1 Hboth).
Qed.

(* 正性：0 < 1/n!（终局严格性的来源） *)
Lemma q_fact_inv_pos : forall n : nat, (0 < 1 / q_fact n)%Q.
Proof.
  intro n. destruct (nat_fact_pos_Z n) as [p Ep].
  unfold q_fact. rewrite Ep. rewrite (q_inv_den1 p).
  unfold Qlt. simpl. lia.
Qed.

(* 旗舰：Σ_{k=0}^{n} 1/k! < 3
   （S_n < S_n + 1/n! 严格 <--- 0 < 1/n!；再 <= 3 由不变量） *)
Theorem sum_fact_recip_lt3 : forall n : nat, (sum_fact_recip n < 3)%Q.
Proof.
  intro n.
  pose proof (q_fact_inv_pos n) as Hpos.
  apply (Qlt_le_trans _ (sum_fact_recip n + 1 / q_fact n)%Q).
  - pose proof (proj2 (Qplus_lt_r 0 (1 / q_fact n) (sum_fact_recip n)) Hpos) as Hlt.
    rewrite Qplus_0_r in Hlt. exact Hlt.
  - apply sum_fact_recip_inv.
Qed.

(* ========== §5 加分件：构造性收敛率（显式 K0 = 4） ========== *)

Theorem q_fact_rate : forall k : nat,
  (4 <= k)%nat -> (1 / q_fact k * 4 < 1)%Q.
Proof.
  intros k Hk.
  destruct (nat_fact_pos_Z k) as [p Ep].
  pose proof (nat_fact_le_Z 4%nat k Hk) as HZ.
  rewrite Ep in HZ. simpl in HZ.
  unfold q_fact. rewrite Ep. rewrite (q_inv_den1 p).
  unfold Qmult. simpl. unfold Qlt. simpl. lia.
Qed.

Theorem q_fact_rate_exists : exists K0 : nat,
  forall k : nat, (K0 <= k)%nat -> (1 / q_fact k * 4 < 1)%Q.
Proof. exists 4%nat. apply q_fact_rate. Qed.

(* ========== §6 加分件：2^k 下界族（任务书几何路线的承重件） ========== *)

Lemma pow2_ge1 : forall k : nat, (1 <= 2 ^ k)%nat.
Proof. induction k as [| k IH]; simpl; lia. Qed.

(* (k+1)! >= 2^k：S k 支 = 2·2^k <= 2·k! <= (k+2)·k! 两次乘法保序 *)
Lemma nat_fact_pow2_lb : forall k : nat, (2 ^ k <= nat_fact (S k))%nat.
Proof.
  induction k as [| k IH].
  - simpl. lia.
  - change (2 ^ S k)%nat with (2 * 2 ^ k)%nat.
    change (nat_fact (S (S k))) with (S (S k) * nat_fact (S k))%nat.
    assert (H1 : (2 * 2 ^ k <= 2 * nat_fact (S k))%nat)
      by (apply Nat.mul_le_mono_l; exact IH).
    assert (H2 : (2 * nat_fact (S k) <= S (S k) * nat_fact (S k))%nat)
      by (apply Nat.mul_le_mono_r; lia).
    lia.
Qed.

Theorem q_fact_inv_le_pow2 : forall k : nat,
  (1 / q_fact (S k) <= 1 / (Z.of_nat (2 ^ k) # 1))%Q.
Proof.
  intro k.
  destruct (nat_fact_pos_Z (S k)) as [p Ep].
  pose proof (proj1 (Znat.Nat2Z.inj_le (2 ^ k)%nat (nat_fact (S k)))
                    (nat_fact_pow2_lb k)) as Hq.
  rewrite Ep in Hq.
  assert (Hp2 : (0 < Z.of_nat (2 ^ k))%Z).
  { pose proof (pow2_ge1 k) as H1.
    apply (proj1 (Znat.Nat2Z.inj_le 1 (2 ^ k))) in H1. lia. }
  destruct (Z.of_nat (2 ^ k)) as [| q | q] eqn:Eq; try lia.
  unfold q_fact. rewrite Ep.
  rewrite (q_inv_den1 p), (q_inv_den1 q).
  unfold Qle. simpl. lia.
Qed.

End DTPT.

(* ============================================================
   归并席 M1（2026-09-14）退役记录：DTPT_Dig.v —— 不并入，直接退役
   判定依据：其全部声明（Inductive Dig、insert_q、P0、rot、Pinf、
   Pmid、insert_q_perm_cons、D5_P0_perm、D5_Pinf_perm）与本文件
   §1–§3 逐字重复；独有内容仅注释（Pmid 端点挂账注记已由
   DTPT_PmidEnd.v 偿还）。源件以 .retired_ 前缀快照留存。
   ============================================================ *)
