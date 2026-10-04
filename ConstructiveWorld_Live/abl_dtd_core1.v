(* ==========================================================================
   abl_dtd_core1.v —— DTPT 本体前件参数消解供给·卷一（参数 1–35）。
   ── 使命：宿主 DTPT.v 本体 138 前件参数登记序第 1–35 位（语句坐标
   :129–:532，卷界零重叠）逐参数消解供给，全取 A 直供形：语句面＝登记形经
   dtd_ 前缀映射逐字同构，证明体就地构造真构造、零宿主定理使用（卷一 35
   参数前件全为任意数据上的 Q 序等／成员／置换／布尔判定义务，无条件化不
   可构造）。35 参数＝27 供给＋8 登记：登记 8 位（dedup_aux_duck／Qmem_perm／
   Qmem_cons_nodup／remove_one／same_set_length 等，混载旗或假结论面）照
   登记不供给，其内核在 dtd_dedup_Qnodup 等证体内以构造性重演承载。宿主件
   零字节动，本件零 Require 宿主。
   ── 依赖：仅 stdlib（QArith.QArith／QArith.Qabs／List／Bool／Arith／Lia／
   Permutation＋Extraction 检验面）——零宿主件 Require、零缓存根兄弟件。
   ── 对标行：A 直供零宿主引用先例＝abl_s01_supply.v；数据同构副本惯例＝
   DTPT↔DTPT_Entropy 的 xq_ 簇同名同构维持。
   ── 构造性注记：全件 Qed 真构造，零承认式声明、零悬置前提、零经典逻辑、
   零节变量声明位；语句面全数＝stdlib Q 离散可判定层既成形态（Qle／Qeq／
   eq-bool／Qmem／Qnodup／Permutation 应用位）；本地数据副本 dtd_Qmem／
   dtd_Qnodup／dtd_dedup 系为宿主现档逐字同构、dtd_ 前缀防撞隔离；提取面＝
   数据层真实现（dedup 去重族）＋逐件 Separate Extraction，Obj.magic 零判据。
   ── 编译配方：池 cwd＝沙箱/现役/abl_r85_supply_pool；source Live 库根
   toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 后 nice -19
   rocq c -native-compiler no
   -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
   abl_dtd_core1.v；绿判＝EXIT=0／日志零 Error／.vo 头 8 字节
   436f7121 00015ff4／.vo 新于 .v；第五证 rocq check；产物只落本池。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

(* ============================================================ *)
(* 〇 数据层副本（DTPT.v 现档逐字同构，dtd_ 前缀隔离；见头注④；          *)
(*    dtd_remove 为本件新增计算剔除函数——remove_one 内容的函数化，       *)
(*    提取面真实现成员）                                                *)
(* ============================================================ *)

Fixpoint dtd_dedup_aux (x : Q) (l : list Q) : list Q :=
  match l with
  | [] => []
  | y :: ys => if Qeq_bool x y then dtd_dedup_aux x ys else y :: dtd_dedup_aux x ys
  end.

Fixpoint dtd_dedup (l : list Q) : list Q :=
  match l with
  | [] => []
  | x :: xs => x :: dtd_dedup_aux x (dtd_dedup xs)
  end.

Definition dtd_H_ms (l : list Q) : Q := (Z.of_nat (length (dtd_dedup l)) # 1)%Q.

Definition dtd_Qmem (a : Q) (l : list Q) : Prop :=
  existsb (fun y => Qeq_bool a y) l = true.

Fixpoint dtd_Qnodup (l : list Q) : Prop :=
  match l with
  | [] => True
  | x :: xs => ~ dtd_Qmem x xs /\ dtd_Qnodup xs
  end.

Fixpoint dtd_remove (x : Q) (n : list Q) : list Q :=
  match n with
  | [] => []
  | y :: ys => if Qeq_bool x y then ys else y :: dtd_remove x ys
  end.

(* ============================================================ *)
(* 一 供给定理区（A 直供形；参数 1–17，语句 1–12）                       *)
(* ============================================================ *)

(* 参数 1（DTPT.v:129） *)
Theorem dtd_Qle_bool_false_le : forall x y : Q, Qle_bool x y = false -> y <= x.
Proof.
  intros x y H. unfold Qle_bool in H. unfold Qle.
  destruct (Z.leb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E.
  - discriminate.
  - apply Z.leb_gt in E. lia.
Qed.

(* 参数 2-3（DTPT.v:144） *)
Theorem dtd_qadd_le : forall a b c d : Q, a <= b -> c <= d -> (a + c <= b + d)%Q.
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

(* 参数 4（DTPT.v:157） *)
Theorem dtd_qopp_le : forall a b : Q, a <= b -> (- b <= - a)%Q.
Proof.
  intros [an ad] [bn bd]; simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

(* 参数 5-6（DTPT.v:163） *)
Theorem dtd_qmul_le_r : forall n m p : Q, n <= m -> 0 <= p -> (n * p <= m * p)%Q.
Proof.
  intros [nn nd] [mn md] [pn pd] H H0;
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((nn * Zpos md) * (pn * Zpos pd)
                <= (mn * Zpos nd) * (pn * Zpos pd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Qed.

(* 参数 7（DTPT.v:179） *)
Theorem dtd_qsub_le_r : forall a b c : Q, a <= b -> (a - c <= b - c)%Q.
Proof.
  intros [an ad] [bn bd] [cn cd] H.
  unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl.
  assert (H1 : ((an * Zpos bd) * (Zpos cd * Zpos cd)
                <= (bn * Zpos ad) * (Zpos cd * Zpos cd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Qed.

(* 参数 8（DTPT.v:195） *)
Theorem dtd_abs_eq : forall a : Q, 0 <= a -> Qabs a == a.
Proof.
  intros [n d] H. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - reflexivity.
  - exfalso. lia.
Qed.

(* 参数 9（DTPT.v:204） *)
Theorem dtd_abs_neg : forall a : Q, a <= 0 -> Qabs a == - a.
Proof.
  intros [n d] H. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - exfalso. lia.
  - reflexivity.
Qed.

(* 参数 10（DTPT.v:218） *)
Theorem dtd_Qeqb_true_of : forall x y : Q, x == y -> Qeq_bool x y = true.
Proof.
  intros x y H. unfold Qeq in H. unfold Qeq_bool.
  destruct (Z.eqb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E; [reflexivity|].
  exfalso. apply Z.eqb_neq in E. lia.
Qed.

(* 辅助件 H1：布尔对称（非参数位；参数 11-35 证体基础设施） *)
Lemma dtd_Qeqb_sym : forall x y : Q, Qeq_bool x y = Qeq_bool y x.
Proof.
  intros x y. destruct (Qeq_bool x y) eqn:E1, (Qeq_bool y x) eqn:E2; try reflexivity.
  - exfalso. apply Qeq_bool_eq in E1.
    assert (E1' : y == x) by (apply Qeq_sym; exact E1).
    apply dtd_Qeqb_true_of in E1'. congruence.
  - exfalso. apply Qeq_bool_eq in E2.
    assert (E2' : x == y) by (apply Qeq_sym; exact E2).
    apply dtd_Qeqb_true_of in E2'. congruence.
Qed.

(* 参数 11-12（DTPT.v:236） *)
Theorem dtd_Qeqb_trans : forall a b c : Q,
  Qeq_bool a b = true -> Qeq_bool b c = true -> Qeq_bool a c = true.
Proof.
  intros a b c H1 H2. apply Qeq_bool_eq in H1. apply Qeq_bool_eq in H2.
  apply dtd_Qeqb_true_of. transitivity b; assumption.
Qed.

(* 参数 13-14（DTPT.v:257） *)
Theorem dtd_Qmem_weaken : forall a b (l : list Q),
  dtd_Qmem a l -> Qeq_bool a b = true -> dtd_Qmem b l.
Proof.
  intros a b l H Hab. unfold dtd_Qmem in H. apply existsb_exists in H.
  destruct H as [w [Hw Hq]].
  unfold dtd_Qmem. apply existsb_exists. exists w. split; [exact Hw|].
  apply (dtd_Qeqb_trans b a w). rewrite (dtd_Qeqb_sym b a). exact Hab. exact Hq.
Qed.

(* 参数 15（DTPT.v:266） *)
Theorem dtd_Qmem_dedup_aux_keep : forall a x (l : list Q),
  dtd_Qmem a (dtd_dedup_aux x l) -> dtd_Qmem a l.
Proof.
  intros a x l. induction l as [| y ys IH]; simpl.
  - intros H. discriminate.
  - intros H. destruct (Qeq_bool x y).
    + assert (Hc : dtd_Qmem a (y :: ys)
                   <-> (Qeq_bool a y = true \/ dtd_Qmem a ys))
        by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
      rewrite Hc. right. exact (IH H).
    + assert (Hc : dtd_Qmem a (y :: dtd_dedup_aux x ys)
                   <-> (Qeq_bool a y = true \/ dtd_Qmem a (dtd_dedup_aux x ys)))
        by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
      rewrite Hc in H. destruct H as [H|H].
      * assert (Hc2 : dtd_Qmem a (y :: ys)
                      <-> (Qeq_bool a y = true \/ dtd_Qmem a ys))
          by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
        rewrite Hc2. left. exact H.
      * assert (Hc2 : dtd_Qmem a (y :: ys)
                      <-> (Qeq_bool a y = true \/ dtd_Qmem a ys))
          by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
        rewrite Hc2. right. exact (IH H).
Qed.

(* 参数 16-17（DTPT.v:278） *)
Theorem dtd_Qmem_dedup_aux_drop : forall a x (l : list Q),
  dtd_Qmem a l -> Qeq_bool a x = false -> dtd_Qmem a (dtd_dedup_aux x l).
Proof.
  intros a x l. induction l as [| y ys IH]; simpl.
  - intros H _. discriminate.
  - intros H Hax.
    assert (Hc : dtd_Qmem a (y :: ys)
                 <-> (Qeq_bool a y = true \/ dtd_Qmem a ys))
      by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
    rewrite Hc in H. destruct (Qeq_bool x y) eqn:Hxy.
    + destruct H as [H|H].
      * exfalso.
        assert (Hya : Qeq_bool y a = true) by (rewrite (dtd_Qeqb_sym y a); exact H).
        assert (Hxa : Qeq_bool x a = true) by (apply (dtd_Qeqb_trans x y a); assumption).
        rewrite (dtd_Qeqb_sym x a) in Hxa. rewrite Hxa in Hax. discriminate.
      * exact (IH H Hax).
    + assert (Hc2 : dtd_Qmem a (y :: dtd_dedup_aux x ys)
                    <-> (Qeq_bool a y = true \/ dtd_Qmem a (dtd_dedup_aux x ys)))
        by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
      rewrite Hc2. destruct H as [H|H].
      * left. exact H.
      * right. exact (IH H Hax).
Qed.

(* ============================================================ *)
(* 【只登记】参数 18＝dedup_aux_duck（DTPT.v:296，IN）：结论面含「-> False」 *)
(* 形，自检②（主定理陈述区无假结论面）相抵，照登记不供给；        *)
(* 其反证内核在本件 dtd_dedup_Qnodup 证体内以 assert 形式真实重演（证明    *)
(* 内 Prop 自由位，不泄入语句面），见区二。                                *)
(* ============================================================ *)

(* 参数 19（DTPT.v:314） *)
Theorem dtd_dedup_aux_Qnodup : forall x (l : list Q),
  dtd_Qnodup l -> dtd_Qnodup (dtd_dedup_aux x l).
Proof.
  intros x l. induction l as [| y ys IH]; simpl; [intros _; exact I |].
  - intros [Hny Hys]. destruct (Qeq_bool x y).
    + apply IH. exact Hys.
    + split.
      * intros Hm. apply Hny. exact (dtd_Qmem_dedup_aux_keep y x _ Hm).
      * apply IH. exact Hys.
Qed.

(* 参数 20（DTPT.v:333） *)
Theorem dtd_dedup_Qmem_l : forall (l : list Q) a,
  dtd_Qmem a (dtd_dedup l) -> dtd_Qmem a l.
Proof.
  induction l as [| x xs IH]; intros a; simpl.
  - discriminate.
  - assert (Hc : dtd_Qmem a (x :: dtd_dedup_aux x (dtd_dedup xs))
                 <-> (Qeq_bool a x = true \/ dtd_Qmem a (dtd_dedup_aux x (dtd_dedup xs))))
      by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
    rewrite Hc. intros [H|H].
    + assert (Hc2 : dtd_Qmem a (x :: xs)
                    <-> (Qeq_bool a x = true \/ dtd_Qmem a xs))
        by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
      rewrite Hc2. left. exact H.
    + assert (Hc2 : dtd_Qmem a (x :: xs)
                    <-> (Qeq_bool a x = true \/ dtd_Qmem a xs))
        by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
      rewrite Hc2. right. apply IH.
      exact (dtd_Qmem_dedup_aux_keep a x _ H).
Qed.

(* 参数 21（DTPT.v:343） *)
Theorem dtd_dedup_Qmem_r : forall (l : list Q) a,
  dtd_Qmem a l -> dtd_Qmem a (dtd_dedup l).
Proof.
  induction l as [| x xs IH]; intros a; simpl.
  - discriminate.
  - intros H.
    assert (Hc : dtd_Qmem a (x :: xs)
                 <-> (Qeq_bool a x = true \/ dtd_Qmem a xs))
      by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
    assert (Hc2 : dtd_Qmem a (x :: dtd_dedup_aux x (dtd_dedup xs))
                  <-> (Qeq_bool a x = true \/ dtd_Qmem a (dtd_dedup_aux x (dtd_dedup xs))))
      by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
    rewrite Hc in H. destruct H as [H|H].
    + rewrite Hc2. left. exact H.
    + destruct (Qeq_bool a x) eqn:Hax.
      * rewrite Hc2. left. reflexivity.
      * rewrite Hc2. right. apply dtd_Qmem_dedup_aux_drop.
        -- apply IH. exact H.
        -- exact Hax.
Qed.

(* ============================================================ *)
(* 【只登记】混载旗四条（底册 §2.3 混载形态：等价/否定/存在见证）：        *)
(*   参数 22＝Qmem_perm（DTPT.v:357，PERM，iff 结论面）——照登记不供给；      *)
(*   参数 23＝Qmem_cons_nodup（:364，IN+NOT，否定+iff）——照登记不供给；      *)
(*   参数 24-25＝remove_one（:378，EQ+IN，iff+exists）——照登记不供给，内容   *)
(*   以 dtd_remove 计算剔除＋下列四分解件干净陈述面真实重演；              *)
(*   参数 26-28＝same_set_length（:434，EQ+IFF+IN+Q-ORD，iff）——照登记不供给，*)
(*   内容以 dtd_len_eq_of_mem2（iff 前件化双单向 forall）真实重演。        *)
(* 其分解件全数陈述面干净（原子离散承载），供参数 29 使用；不作为参数位供给记录。 *)
(* ============================================================ *)

(* ============================================================ *)
(* 二 辅助件区（非参数位基础设施；陈述面同守红线二——全原子离散承载）          *)
(* ============================================================ *)

(* 辅助件 H2：剔除函数子列成员（无前提） *)
Lemma dtd_remove_sub_mem : forall a x (n : list Q),
  dtd_Qmem a (dtd_remove x n) -> dtd_Qmem a n.
Proof.
  intros a x n. induction n as [| y ys IH]; simpl.
  - discriminate.
  - intros H. destruct (Qeq_bool x y).
    + assert (Hcc : dtd_Qmem a (y :: ys)
                    <-> (Qeq_bool a y = true \/ dtd_Qmem a ys))
        by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
      rewrite Hcc. right. exact H.
    + assert (Hcc : dtd_Qmem a (y :: dtd_remove x ys)
                    <-> (Qeq_bool a y = true \/ dtd_Qmem a (dtd_remove x ys)))
        by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
      rewrite Hcc in H. destruct H as [H|H].
      * assert (Hcc2 : dtd_Qmem a (y :: ys)
                       <-> (Qeq_bool a y = true \/ dtd_Qmem a ys))
          by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
        rewrite Hcc2. left. exact H.
      * assert (Hcc2 : dtd_Qmem a (y :: ys)
                       <-> (Qeq_bool a y = true \/ dtd_Qmem a ys))
          by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
        rewrite Hcc2. right. exact (IH H).
Qed.

(* 辅助件 H3：剔除函数成员保持（异于剔除元方向） *)
Lemma dtd_remove_mem_in : forall a x (n : list Q),
  dtd_Qmem a n -> Qeq_bool a x = false -> dtd_Qmem a (dtd_remove x n).
Proof.
  intros a x n. induction n as [| y ys IH]; simpl.
  - intros H _. discriminate.
  - intros H Hax.
    assert (Hcc : dtd_Qmem a (y :: ys)
                 <-> (Qeq_bool a y = true \/ dtd_Qmem a ys))
      by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
    rewrite Hcc in H. destruct (Qeq_bool x y) eqn:Hxy.
    + destruct H as [H|H].
      * exfalso.
        assert (Hyx : Qeq_bool y x = true)
          by (rewrite <- (dtd_Qeqb_sym x y); exact Hxy).
        assert (Hayx : Qeq_bool a x = true)
          by (apply (dtd_Qeqb_trans a y x); assumption).
        rewrite Hayx in Hax. discriminate.
      * exact H.
    + assert (Hc2 : dtd_Qmem a (y :: dtd_remove x ys)
                    <-> (Qeq_bool a y = true \/ dtd_Qmem a (dtd_remove x ys)))
        by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
      rewrite Hc2. destruct H as [H|H].
      * left. exact H.
      * right. exact (IH H Hax).
Qed.

(* 辅助件 H4：剔除保持无重 *)
Lemma dtd_remove_nd : forall x (n : list Q),
  dtd_Qnodup n -> dtd_Qmem x n -> dtd_Qnodup (dtd_remove x n).
Proof.
  intros x n. induction n as [| y ys IH]; simpl.
  - intros _ _. exact I.
  - intros Hnd Hx. simpl in Hnd. destruct Hnd as [Hny Hndy].
    destruct (Qeq_bool x y) eqn:Hxy.
    + exact Hndy.
    + assert (Hxys : dtd_Qmem x ys).
      { assert (Hcc : dtd_Qmem x (y :: ys)
                      <-> (Qeq_bool x y = true \/ dtd_Qmem x ys))
          by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
        rewrite Hcc in Hx. destruct Hx as [Hc | Hc].
        - rewrite Hxy in Hc. discriminate.
        - exact Hc. }
      split.
      * intros Hm. apply Hny. exact (dtd_remove_sub_mem y x ys Hm).
      * apply IH.
        -- exact Hndy.
        -- exact Hxys.
Qed.

(* 辅助件 H5：剔除长度恰减一 *)
Lemma dtd_remove_len : forall x (n : list Q),
  dtd_Qmem x n -> length n = S (length (dtd_remove x n)).
Proof.
  intros x n. induction n as [| y ys IH]; simpl.
  - intros H. discriminate.
  - intros H. destruct (Qeq_bool x y) eqn:Hxy.
    + reflexivity.
    + assert (Hcc : dtd_Qmem x (y :: ys)
                    <-> (Qeq_bool x y = true \/ dtd_Qmem x ys))
        by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
      rewrite Hcc in H. destruct H as [H|H].
      * rewrite Hxy in H. discriminate.
      * specialize (IH H). simpl. rewrite <- IH. reflexivity.
Qed.

(* 辅助件 H6 *)
Lemma dtd_Qmem_refl_cons : forall x (l : list Q), dtd_Qmem x (x :: l).
Proof.
  intros x l.
  assert (Hc : dtd_Qmem x (x :: l)
               <-> (Qeq_bool x x = true \/ dtd_Qmem x l))
    by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
  rewrite Hc. left. apply Qeq_bool_refl.
Qed.

(* 辅助件 H7：双单向成员一致＋双侧无重 → 基数相等（same_set_length 内容的 *)
(* 干净陈述面分解版——iff 前件化两单向 forall，句面零混载形态；剔除走      *)
(* dtd_remove 计算函数＋H2-H5 分解件；「剔除元等类无幸存」内核以证内       *)
(* assert（Hkill）真实重演——其内容即参数 18 之 -> False 形，照自检②不入     *)
(* 顶层陈述位，随证明体提取擦除） *)
Lemma dtd_len_eq_of_mem2 : forall m n : list Q,
  dtd_Qnodup m -> dtd_Qnodup n ->
  (forall a, dtd_Qmem a m -> dtd_Qmem a n) ->
  (forall a, dtd_Qmem a n -> dtd_Qmem a m) ->
  length m = length n.
Proof.
  intros m. induction m as [| x xs IH]; intros n Hm Hn Hmn Hnm.
  - destruct n as [| y ys].
    + reflexivity.
    + exfalso.
      pose proof (Hnm y (dtd_Qmem_refl_cons y ys)) as Hc.
      unfold dtd_Qmem in Hc. simpl in Hc. discriminate.
  - destruct n as [| y ys].
    + exfalso.
      pose proof (Hmn x (dtd_Qmem_refl_cons x xs)) as Hc.
      unfold dtd_Qmem in Hc. simpl in Hc. discriminate.
    + simpl in Hm, Hn.
      assert (Hmx : ~ dtd_Qmem x xs) by exact (proj1 Hm).
      assert (Hmxs : dtd_Qnodup xs) by exact (proj2 Hm).
      assert (Hx : dtd_Qmem x (y :: ys)) by (apply Hmn, dtd_Qmem_refl_cons).
      assert (Hkill : forall (u v : Q) (m0 : list Q),
                   dtd_Qnodup m0 -> Qeq_bool u v = true ->
                   dtd_Qmem u (dtd_remove v m0) -> False).
      { intros u v m0. induction m0 as [| y0 ys0 IHk]; simpl.
        - discriminate.
        - intros Hnd Huv H. simpl in Hnd. destruct Hnd as [Hny Hndy].
          destruct (Qeq_bool v y0) eqn:Hvy.
          + assert (Huy : Qeq_bool u y0 = true)
              by (apply (dtd_Qeqb_trans u v y0); assumption).
            apply Hny. exact (dtd_Qmem_weaken u y0 ys0 H Huy).
          + assert (Hcc : dtd_Qmem u (y0 :: dtd_remove v ys0)
                          <-> (Qeq_bool u y0 = true \/ dtd_Qmem u (dtd_remove v ys0)))
              by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
            rewrite Hcc in H. destruct H as [H|H].
            * assert (Hyu : Qeq_bool y0 u = true) by (rewrite (dtd_Qeqb_sym y0 u); exact H).
              assert (Hyv : Qeq_bool y0 v = true) by (apply (dtd_Qeqb_trans y0 u v); assumption).
              rewrite (dtd_Qeqb_sym v y0) in Hvy. rewrite Hyv in Hvy. discriminate.
            * exact (IHk Hndy Huv H). }
      assert (Hnd' : dtd_Qnodup (dtd_remove x (y :: ys)))
        by (apply dtd_remove_nd; [exact Hn | exact Hx]).
      assert (Hlen' : length (y :: ys) = S (length (dtd_remove x (y :: ys))))
        by (apply dtd_remove_len; exact Hx).
      assert (Hlen : length xs = length (dtd_remove x (y :: ys))).
      { apply (IH (dtd_remove x (y :: ys)) Hmxs Hnd').
        - intros a Ha.
          assert (Ham : dtd_Qmem a (x :: xs)).
          { assert (Hcc : dtd_Qmem a (x :: xs)
                          <-> (Qeq_bool a x = true \/ dtd_Qmem a xs))
              by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
            rewrite Hcc. right. exact Ha. }
          pose proof (Hmn a Ham) as Han.
          assert (Haxf : Qeq_bool a x = false).
          { destruct (Qeq_bool a x) eqn:E; [| reflexivity].
            exfalso. apply Hmx. exact (dtd_Qmem_weaken a x xs Ha E). }
          exact (dtd_remove_mem_in a x (y :: ys) Han Haxf).
        - intros a Ha.
          pose proof (dtd_remove_sub_mem a x (y :: ys) Ha) as Han.
          pose proof (Hnm a Han) as Ham'.
          assert (Hcc : dtd_Qmem a (x :: xs)
                        <-> (Qeq_bool a x = true \/ dtd_Qmem a xs))
            by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
          rewrite Hcc in Ham'. destruct Ham' as [Hax | Hax].
          + exfalso. exact (Hkill a x (y :: ys) Hn Hax Ha).
          + exact Hax. }
      rewrite Hlen'. rewrite <- Hlen. reflexivity.
Qed.

(* 辅助件 H8：dedup 无重（dedup_Qnodup :351 同内容——零前件语句，非参数位；  *)
(* 参数 18 反证内核于此证体内 assert 真实重演） *)
Lemma dtd_dedup_Qnodup : forall l : list Q, dtd_Qnodup (dtd_dedup l).
Proof.
  induction l as [| x xs IH]; simpl.
  - exact I.
  - assert (Hduck : forall (a : Q) (m : list Q),
               dtd_Qmem a (dtd_dedup_aux a m) -> False).
    { intros a m. induction m as [| y ys IHd]; simpl.
      - discriminate.
      - destruct (Qeq_bool a y) eqn:E.
        + apply IHd.
        + assert (Hc : dtd_Qmem a (y :: dtd_dedup_aux a ys)
                       <-> (Qeq_bool a y = true \/ dtd_Qmem a (dtd_dedup_aux a ys)))
            by (unfold dtd_Qmem; simpl; rewrite orb_true_iff; reflexivity).
          rewrite Hc. intros [Hd|Hd].
          * rewrite E in Hd. discriminate.
          * apply IHd. exact Hd. }
    split.
    + intros Hm. exact (Hduck x (dtd_dedup xs) Hm).
    + apply dtd_dedup_aux_Qnodup. exact IH.
Qed.

(* ============================================================ *)
(* 三 供给定理区续（参数 29-35，语句 21-26）                              *)
(* ============================================================ *)

(* 参数 29（DTPT.v:465） *)
Theorem dtd_N9_ms_perm_inv : forall (l p : list Q),
  Permutation l p -> dtd_H_ms l = dtd_H_ms p.
Proof.
  intros l p Hp. unfold dtd_H_ms. f_equal. f_equal.
  apply dtd_len_eq_of_mem2.
  - apply dtd_dedup_Qnodup.
  - apply dtd_dedup_Qnodup.
  - intros a Ha.
    pose proof (dtd_dedup_Qmem_l l a Ha) as Hal.
    unfold dtd_Qmem in Hal. apply existsb_exists in Hal.
    destruct Hal as [w [Hw Hq]].
    assert (Hap : dtd_Qmem a p).
    { unfold dtd_Qmem. apply existsb_exists. exists w. split.
      - apply (Permutation_in _ Hp). exact Hw.
      - exact Hq. }
    exact (dtd_dedup_Qmem_r p a Hap).
  - intros a Ha.
    pose proof (dtd_dedup_Qmem_l p a Ha) as Hap.
    unfold dtd_Qmem in Hap. apply existsb_exists in Hap.
    destruct Hap as [w [Hw Hq]].
    assert (Hal : dtd_Qmem a l).
    { unfold dtd_Qmem. apply existsb_exists. exists w. split.
      - apply (Permutation_in _ (Permutation_sym Hp)). exact Hw.
      - exact Hq. }
    exact (dtd_dedup_Qmem_r l a Hal).
Qed.

(* 参数 30-31（DTPT.v:491） *)
Theorem dtd_qadd_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> (0 <= a + b)%Q.
Proof.
  intros [an ad] [bn bd]; simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

(* 参数 32（DTPT.v:499） *)
Theorem dtd_xq_Qle_bool_le : forall x y : Q, Qle_bool x y = true -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy]. unfold Qle, Qle_bool; simpl. intros H.
  apply Z.leb_le. exact H.
Qed.

(* 参数 33（DTPT.v:506） *)
Theorem dtd_xq_abs_id : forall x : Q, (0 <= x)%Q -> Qabs x == x.
Proof.
  intros [n d] Hx. unfold Qle in Hx; simpl in Hx.
  assert (Hn : (0 <= n)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite (Z.abs_eq n Hn). reflexivity.
Qed.

(* 参数 34（DTPT.v:514） *)
Theorem dtd_xq_abs_eq0 : forall x : Q, x == 0 -> Qabs x == 0.
Proof.
  intros [n d] Hx. unfold Qeq in Hx; simpl in Hx.
  assert (Hn : (n = 0)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite Hn. reflexivity.
Qed.

(* 参数 35（DTPT.v:532） *)
Theorem dtd_xq_abs_eq : forall x y : Q, x == y -> Qabs x == Qabs y.
Proof.
  intros [n1 d1] [n2 d2] Hxy.
  unfold Qeq in Hxy; simpl in Hxy.
  unfold Qabs; simpl. unfold Qeq; simpl.
  pose proof (Z.abs_spec n1) as Ha1. pose proof (Z.abs_spec n2) as Ha2.
  destruct Ha1 as [[A1 B1] | [A1 B1]];
    destruct Ha2 as [[A2 B2] | [A2 B2]];
    try rewrite B1; try rewrite B2; lia.
Qed.

(* ============================================================ *)
(* 四 尾置验印区（文件最尾）：逐件承认面验印（全 Closed 判据）——          *)
(*    名清单＝21 供给定理＋8 辅助件＝29 名，与 Qed 计数 29 零差           *)
(* ============================================================ *)

Print Assumptions dtd_Qle_bool_false_le.
Print Assumptions dtd_qadd_le.
Print Assumptions dtd_qopp_le.
Print Assumptions dtd_qmul_le_r.
Print Assumptions dtd_qsub_le_r.
Print Assumptions dtd_abs_eq.
Print Assumptions dtd_abs_neg.
Print Assumptions dtd_Qeqb_true_of.
Print Assumptions dtd_Qeqb_trans.
Print Assumptions dtd_Qmem_weaken.
Print Assumptions dtd_Qmem_dedup_aux_keep.
Print Assumptions dtd_Qmem_dedup_aux_drop.
Print Assumptions dtd_dedup_aux_Qnodup.
Print Assumptions dtd_dedup_Qmem_l.
Print Assumptions dtd_dedup_Qmem_r.
Print Assumptions dtd_N9_ms_perm_inv.
Print Assumptions dtd_qadd_nonneg.
Print Assumptions dtd_xq_Qle_bool_le.
Print Assumptions dtd_xq_abs_id.
Print Assumptions dtd_xq_abs_eq0.
Print Assumptions dtd_xq_abs_eq.
Print Assumptions dtd_Qeqb_sym.
Print Assumptions dtd_remove_sub_mem.
Print Assumptions dtd_remove_mem_in.
Print Assumptions dtd_remove_nd.
Print Assumptions dtd_remove_len.
Print Assumptions dtd_Qmem_refl_cons.
Print Assumptions dtd_len_eq_of_mem2.
Print Assumptions dtd_dedup_Qnodup.

(* ============================================================ *)
(* 五 提取检验区（红线四：可提取验证，Obj.magic 计数＝0 判据）            *)
(*    检验一：数据层真实现（去重族＋剔除函数 Qeq_bool 判定面）；           *)
(*    检验二：29 件定理逐件 Separate Extraction（Prop 结论面随提取擦除，   *)
(*     口径「构造子参提取擦除」惯例；产物归  专属桶）。      *)
(* ============================================================ *)

Separate Extraction dtd_dedup_aux dtd_dedup dtd_H_ms dtd_remove dtd_Qmem dtd_Qnodup.

Separate Extraction dtd_Qle_bool_false_le dtd_qadd_le dtd_qopp_le dtd_qmul_le_r
  dtd_qsub_le_r dtd_abs_eq dtd_abs_neg dtd_Qeqb_true_of dtd_Qeqb_trans
  dtd_Qmem_weaken dtd_Qmem_dedup_aux_keep dtd_Qmem_dedup_aux_drop
  dtd_dedup_aux_Qnodup dtd_dedup_Qmem_l dtd_dedup_Qmem_r dtd_N9_ms_perm_inv
  dtd_qadd_nonneg dtd_xq_Qle_bool_le dtd_xq_abs_id dtd_xq_abs_eq0 dtd_xq_abs_eq
  dtd_Qeqb_sym dtd_remove_sub_mem dtd_remove_mem_in
  dtd_remove_nd dtd_remove_len dtd_Qmem_refl_cons dtd_len_eq_of_mem2
  dtd_dedup_Qnodup.
