(* ============================================================
   DTPT_ROTC.v — 真循环旋转底座（X1 扫描席 A 级发现：伪定理簇真化）
   职责：Pinf 伪装簇真化层操作语义——纯增量新建真循环旋转底座
         rotc = skipn ++ firstn（取尾段接到前段，n 起转一圈），
         证明新相算子非退化：存在列表与转数使
         H_adj (rotc n l) <> H_adj l（旗舰分离件），且真旋转与
         恒等算子 Pinf 结构可分（rotc n l <> l 有闭项见证）。
   依赖：QArith（QArith/Qabs）、List、Lia、Permutation、DTPT
         （H_adj、xq_pair_dist_le 跨度下界引擎）、DTPT_LLM
         （llm_rot_cyclic_perm / llm_rot_cyclic_length 现成置换件
         与长度件——底座纪律：不重证，直接引用）。
   归并记录：无（原生成模块）。
   认证：零承认零公理；全树 coqchk EXIT=0（2026-09-14）。
   纪律：纯构造性；四关收割；温控协议；全程 Qed；
         nat 全显式 %nat（上游 Q_scope 劫持传导）。
   附注：真化动机——DTPT.v 的 rot = firstn ++ skipn 是恒等重构，
         致 Pinf ≡ id、Hsup l n ≡ H_adj l，五件定理成恒等推论伪装；
         X1 定位：DTPT_热点升级清单_X1.md 热点 4【Hsup 族伪定理簇
         真化：真循环旋转底座 rotc】保底/主件/旗舰/加分四层交付。
   ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Permutation.
Require DTPT.
Require DTPT_LLM.
Import ListNotations.
Import DTPT.DTPT.
Import DTPT_LLM.DTPT_LLM.

Module DTPT_ROTC.

(* ========== §1 真循环旋转底座 ========== *)

(* 真循环旋转：取 l 的后段接到前段（DTPT.rot 的 firstn++skipn
   恒等重构之真化替换；X1 热点 4 定义面） *)
Definition rotc (n : nat) (l : list Q) : list Q :=
  skipn n l ++ firstn n l.

(* 真无限相：转 s+1 格（对照 DTPT.Pinf 的恒等坍缩面） *)
Definition Pinf_c (l : list Q) (s : nat) : list Q := rotc (S s) l.

(* ========== §2 保底件：置换与长度 ========== *)

(* 真旋转是置换：两步走——llm_rot_cyclic_perm（skipn++firstn 与 l
   置换等价，Permutation_app_comm + firstn_skipn 合成件）取对称 *)
Theorem rotc_perm : forall (n : nat) (l : list Q),
  Permutation l (rotc n l).
Proof.
  intros n l. unfold rotc.
  apply Permutation_sym.
  apply llm_rot_cyclic_perm.
Qed.

(* 长度不变：直接引用底座 llm_rot_cyclic_length（禁重证） *)
Theorem rotc_length : forall (n : nat) (l : list Q),
  length (rotc n l) = length l.
Proof.
  intros n l. unfold rotc. apply llm_rot_cyclic_length.
Qed.

Theorem Pinf_c_perm : forall (l : list Q) (s : nat),
  Permutation l (Pinf_c l s).
Proof.
  intros l s. unfold Pinf_c. apply rotc_perm.
Qed.

(* ========== §3 主件：周期律与逆元律 ========== *)

(* 零转恒等（app 右零） *)
Lemma rotc_0 : forall l : list Q, rotc 0 l = l.
Proof.
  intros l. unfold rotc. simpl. apply app_nil_r.
Qed.

(* 表长取全：skipn 吃光前段剩后段（对前段归纳） *)
Lemma skipn_all_app : forall (a b : list Q),
  skipn (length a) (a ++ b) = b.
Proof.
  intros a b. induction a as [| x xs IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.

(* 表长取全：firstn 吃光前段（对前段归纳） *)
Lemma firstn_all_app : forall (a b : list Q),
  firstn (length a) (a ++ b) = a.
Proof.
  intros a b. induction a as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* 核心引理：转「前段长」格 = 前后段换位（真旋转的交换子） *)
Lemma rotc_rot_app : forall (a b : list Q),
  rotc (length a) (a ++ b) = b ++ a.
Proof.
  intros a b. unfold rotc.
  rewrite skipn_all_app. rewrite firstn_all_app. reflexivity.
Qed.

(* 逆元律：转 n 格后回转（表长 - n）格复原。
   证法：l 分解为 firstn/skipn 两段（firstn_skipn），pose 折叠
   两段变量护住 n 的替换面，再 rotc_rot_app 两次换位收口。 *)
Theorem rotc_inv : forall (n : nat) (l : list Q),
  (n <= length l)%nat -> rotc ((length l - n)%nat) (rotc n l) = l.
Proof.
  intros n l Hn.
  pose (a := firstn n l).
  pose (b := skipn n l).
  assert (Hla : (length a = n)%nat)
    by exact (firstn_length_le l Hn).
  assert (Hsplit : l = a ++ b)
    by (unfold a, b; symmetry; apply firstn_skipn).
  assert (Hab : (length (a ++ b) - length a = length b)%nat)
    by (rewrite length_app; lia).
  rewrite Hsplit.
  rewrite <- Hla.
  rewrite Hab.
  rewrite !rotc_rot_app.
  reflexivity.
Qed.

(* 周期律：转整一圈（表长格）复原——逆元律在 n := 表长 的特例 *)
Theorem rotc_full : forall l : list Q, rotc (length l) l = l.
Proof.
  intros l.
  assert (H := rotc_inv (length l) l (le_n (length l))).
  assert (Hd : (length l - length l)%nat = 0%nat) by lia.
  rewrite Hd in H.
  rewrite rotc_0 in H.
  exact H.
Qed.

(* ========== §4 旗舰·非退化分离 ========== *)

(* 恒等算子面：DTPT.Pinf 的 rot = firstn++skipn 恒等重构
   （X1 判词的定义面事实，一行 firstn_skipn） *)
Lemma Pinf_true_id : forall (l : list Q) (s : nat), Pinf l s = l.
Proof.
  intros l s. unfold Pinf, rot. apply firstn_skipn.
Qed.

(* 成员经真旋转保持（rotc_perm 搬成员 + Permutation_in） *)
Lemma rotc_in : forall (n : nat) (l : list Q) (x : Q),
  In x l -> In x (rotc n l).
Proof.
  intros n l x Hin.
  exact (Permutation_in x (rotc_perm n l) Hin).
Qed.

(* 加分项：真旋转相算子的跨度下界——表内任意两元的距离
   经置换成员搬移 + xq_pair_dist_le 被 H_adj (rotc n l) 界住 *)
Theorem H_rotc_span_lb : forall (n : nat) (l : list Q) (x y : Q),
  In x l -> In y l -> (Qabs (x - y) <= H_adj (rotc n l))%Q.
Proof.
  intros n l x y Hx Hy.
  apply (xq_pair_dist_le (rotc n l) x y).
  - apply rotc_in. exact Hx.
  - apply rotc_in. exact Hy.
Qed.

(* 加分项·数值见证：见证列 [0;1;2] 上真旋转相算子恒有跨度下界 2
   （首尾差 |0-2| = 2，Qle 闭项判定 reflexivity 直收） *)
Theorem H_rotc_span_lb_wit : forall n : nat,
  (2 <= H_adj (rotc n [0;1;2]))%Q.
Proof.
  intros n.
  apply (Qle_trans 2 (Qabs (0 - 2)) (H_adj (rotc n [0;1;2]))).
  - replace (Qabs (0 - 2)) with 2%Q by reflexivity.
    apply Qle_refl.
  - apply H_rotc_span_lb.
    + simpl. left. reflexivity.
    + simpl. right. right. left. reflexivity.
Qed.

(* 旗舰：真旋转相算子非退化——存在 l 与转数 n 使 H_adj 严格改变。
   见证 [0;1;2] 转 1 格 = [1;2;0]：H_adj 从 2（|1-0|+|2-1|）
   升到 3（|2-1|+|0-2|）。闭 Q 值反例收口：vm_compute 一发 +
   discriminate（B2 卡在册配方）。此件直接反证 Pinf 伪装簇的
   「定理」在真底座下不平凡。 *)
Theorem H_rotc_separates : exists (l : list Q) (n : nat),
  H_adj (rotc n l) <> H_adj l.
Proof.
  exists [0;1;2], 1%nat.
  intro Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* 加分项：与 Pinf 的分离——真旋转与恒等算子结构可分
   （Pinf l s = l 恒等，故见证列上 rotc 1 <> l 结构不等） *)
Theorem rotc_Pinf_separates : exists (l : list Q) (n s : nat),
  rotc n l <> Pinf l s.
Proof.
  exists [0;1;2], 1%nat, 0%nat.
  rewrite Pinf_true_id.
  intro Hc. vm_compute in Hc. discriminate Hc.
Qed.

End DTPT_ROTC.
Import DTPT_ROTC.

(* ========== §5 公理面审计（G4） ========== *)

Print Assumptions rotc_perm.
Print Assumptions rotc_length.
Print Assumptions rotc_inv.
Print Assumptions rotc_full.
Print Assumptions H_rotc_span_lb.
Print Assumptions H_rotc_span_lb_wit.
Print Assumptions H_rotc_separates.
Print Assumptions rotc_Pinf_separates.
