(* ============================================================
   DTPT_Cyc.v — 母文件：排序表循环旋转熵精确理论 + 上确界冻结/谱有限
   （U8 席新建；M5 归并席并入 DTPT_HsupStable.v 后定形）
   ── 标准六字段头 ──
   【一·职责】
     §0-§8（U8 原面）：firstn/skipn 保序 + rotc_two_runs 双升序段分解 +
     H_adj_app_seam 接缝分解 + H_adj (rotc k l) 三项 Qeq 精确闭式（含
     k=0 / k≥表长 / 短表边界与二分合成）+ 3·spread 上界（H_adj_rotc_ub3）
     + qmax2 真动态上确界 Hsup_cyc（单调/界/达到性）+ 数值锚 [0;1;2]。
     §M5-1 起（HsupStable 并入面）：切段四件套 + 局部周期律诚实版
     （守卫加法律/冻结形/双反例定谳）+ qmax2 吸收件 + 跨距单调链 +
     旗舰冻结定理 Hsup_cyc_stable + 谱有限三件 + 冻结数值锚。
     数学锚：l=[a1<=…<=an]，1<=k<=n−1 时 H_adj (rotc k l) =
     (a_n−a_{k+1}) + (a_n−a_1) + (a_k−a_1) <= 3·spread，k=0 与 k=n 取
     最小值 spread（与 C_gen 排序最小 1·spread 成对）；clamp 语义下
     Hsup_cyc l n 在 n = length l 处冻结。
   【二·依赖】
     DTPT（H_adj/xq_ 工具箱/SortedQ）、DTPT_ROTC（rotc 系/rotc_perm/
     rotc_full/rotc_0/rotc_rot_app）、DTPT_Entropy（SortedQ/xq_ 桥，
     与 DTPT 同名同构，Import 序取后者）；stdlib：QArith/Qabs/List/
     Lia/Permutation。无其它 Require。
   【三·归并记录】
     M5 席：DTPT_HsupStable.v（U18-3 拆分席，U8 留账偿还件）全文并入
     本文件尾（§M5-1 分隔注起，除 Require 块外逐字保留），源文件退役
     （.retired_M5 快照留存）。其 Require DTPT/DTPT_ROTC/DTPT_Cyc 三行
     删除——ROTC 依赖经本文件现有 Require DTPT_ROTC 可达。
   【四·对账注记（与下游 DTPT_RotSpec）】
     依 U18-3 归并对账表：本文件 rotc_add_local ↔ RotSpec.rotc_add、
     rotc_freeze_local ↔ RotSpec.rotc_periodic_full、rotc_add_naive_false ↔
     RotSpec.rotc_add_unbounded_false 三对为同语句（或同判反例）异名件
     ——按整合令保留本侧命名（并入件原名的 _local 系），跨文件二选一
     去重留下游消费面统一裁决；rotc_periodic_naive_false 为
     RotSpec.rotc_periodic（守卫周期形）的无守卫 k 形反例补位，互补
     非重复。RotSpec 在下游持有 rotc_add 系现役件，本文件不引用。
   【五·认证】
     全件 Qed（U8 32 件 + 并入 18 件 = 50 件）；Print Assumptions 全
     Closed under the global context；M5 一窗编译全绿（G1-G4 四关证据
     见 DTPT_M5_归并报告.md）；底座零重证零修改。
   【六·纪律】
     零承认（头注不用禁词字面）；全程 Qed；nat 全显式 %nat（上游
     Q_scope 传导）；lia 只用于 nat/Z，Q 侧全走显式引理装配。
   ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Permutation.
Require DTPT.
Require DTPT_ROTC.
Require DTPT_Entropy.
Import ListNotations.
Import DTPT.DTPT.
Import DTPT_ROTC.DTPT_ROTC.
Import DTPT_Entropy.DTPT_Entropy.

Module DTPT_Cyc.

(* ========== §0 通用小工具 ========== *)

(* Qeq 运入 Qle 的桥：Qeq 与 Qle 展开后同为 Qnum/Qden 编码式，
   等式运进不等式由 Z 层 lia 一步收口（不经 setoid rewrite） *)
Lemma cyc_qeq_le : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros x y H. unfold Qeq in H. unfold Qle. lia.
Qed.

(* nat 全覆盖二分：le 或 gt（自证，不依赖 Compare_dec 裸名；
   归纳须先于 m 引入，IH 对 m 全称化后 S 支才可传） *)
Lemma cyc_nat_le_gt_cases : forall n m : nat, (n <= m)%nat \/ (m < n)%nat.
Proof.
  induction n as [| n IH]; intros m; destruct m as [| m].
  - left. lia.
  - left. lia.
  - right. lia.
  - destruct (IH m) as [H | H]; [ left | right ]; lia.
Qed.

(* 三倍自界：0 <= s 时 s <= 3*s（ub3 边界支的公共收口） *)
Lemma cyc_le_triple : forall s : Q, (0 <= s)%Q -> (s <= 3 * s)%Q.
Proof.
  intros s Hs.
  assert (H3 : (3 * s == s + s + s)%Q) by ring.
  apply (Qle_trans s (s + s + s) (3 * s)).
  - apply (proj2 (Qle_0_sub' s (s + s + s))).
    assert (Hr : (s + s + s - s == s + s)%Q) by ring.
    rewrite Hr. exact (qadd_nonneg s s Hs Hs).
  - apply cyc_qeq_le. apply Qeq_sym. exact H3.
Qed.

(* ========== §1 保序底座：firstn/skipn 保成员与保升序 ========== *)

Lemma firstn_incl : forall (l : list Q) (k : nat) (z : Q),
  In z (firstn k l) -> In z l.
Proof.
  induction l as [| a rest IH]; intros k z Hin.
  - destruct k; simpl in Hin; destruct Hin.
  - destruct k as [| k']; simpl in Hin.
    + destruct Hin.
    + destruct Hin as [Hin | Hin].
      * left. exact Hin.
      * right. exact (IH k' z Hin).
Qed.

Lemma skipn_incl : forall (l : list Q) (k : nat) (z : Q),
  In z (skipn k l) -> In z l.
Proof.
  induction l as [| a rest IH]; intros k z Hin.
  - destruct k; simpl in Hin; destruct Hin.
  - destruct k as [| k']; simpl in Hin.
    + exact Hin.
    + right. exact (IH k' z Hin).
Qed.

Lemma firstn_SortedQ : forall (l : list Q) (k : nat),
  SortedQ l -> SortedQ (firstn k l).
Proof.
  induction l as [| a rest IH]; intros k HS.
  - destruct k as [| k']; simpl; apply sortQ_nil.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    destruct k as [| k']; simpl.
    + apply sortQ_nil.
    + apply sortQ_cons.
      * apply IH. exact HSr.
      * apply Forall_forall. intros z Hz. apply HFa.
        exact (firstn_incl rest k' z Hz).
Qed.

Lemma skipn_SortedQ : forall (l : list Q) (k : nat),
  SortedQ l -> SortedQ (skipn k l).
Proof.
  induction l as [| a rest IH]; intros k HS.
  - destruct k as [| k']; simpl; apply sortQ_nil.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    destruct k as [| k']; simpl.
    + apply sortQ_cons;
        [ exact HSr | apply Forall_forall; exact HFa ].
    + apply IH. exact HSr.
Qed.

(* 结构主件：真循环旋转 = 第一段升序 ++ 第二段升序 *)
Theorem rotc_two_runs : forall (k : nat) (l : list Q),
  SortedQ l -> SortedQ (skipn k l) /\ SortedQ (firstn k l).
Proof.
  intros k l HS. split.
  - apply skipn_SortedQ. exact HS.
  - apply firstn_SortedQ. exact HS.
Qed.

(* ========== §2 接缝分解：u++v 熵 = 两段熵 + 接缝绝对值 ========== *)

(* 两段各自非空即可，不要求排序：熵只在接缝处多出一个绝对值 *)
Lemma H_adj_app_seam : forall (u v : list Q),
  u <> [] -> v <> [] ->
  H_adj (u ++ v) == H_adj u + H_adj v + Qabs (hd 0 v - lastq u).
Proof.
  induction u as [| a rest IH]; intros v Hne Hne2.
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [| b bs].
    + destruct v as [| c v'].
      * exfalso. apply Hne2. reflexivity.
      * change (H_adj ([a] ++ c :: v')) with (Qabs (c - a) + H_adj (c :: v'))%Q.
        change (H_adj [a]) with 0%Q.
        change (lastq [a]) with a.
        change (hd 0 (c :: v')) with c.
        ring.
    + change (H_adj ((a :: b :: bs) ++ v))
        with (Qabs (b - a) + H_adj (b :: bs ++ v))%Q.
      change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      change (lastq (a :: b :: bs)) with (lastq (b :: bs)).
      assert (Hne' : b :: bs <> []) by (intro Hcz; discriminate Hcz).
      replace (H_adj (b :: bs ++ v)) with (H_adj ((b :: bs) ++ v))
        by reflexivity.
      rewrite (IH v Hne' Hne2).
      ring.
Qed.

(* ========== §3 边界判别与端元迁移 ========== *)

(* 非空判别：转点严格小于表长时 skipn 段非空 *)
Lemma skipn_ne_of_lt : forall (k : nat) (l : list Q),
  (k < length l)%nat -> skipn k l <> [].
Proof.
  intros k l Hlt Hc.
  assert (Hsplit : l = firstn k l ++ skipn k l)
    by (symmetry; apply firstn_skipn).
  rewrite Hc in Hsplit. rewrite app_nil_r in Hsplit.
  assert (Hle : (k <= length l)%nat) by lia.
  assert (Hlen : (length (firstn k l) = k)%nat)
    by (apply (firstn_length_le l Hle)).
  assert (Hcon : (length l = k)%nat) by (rewrite Hsplit; exact Hlen).
  lia.
Qed.

(* 非空判别：转数非零且不超表长时 firstn 段非空 *)
Lemma firstn_ne_of_lt : forall (k : nat) (l : list Q),
  (0 < k)%nat -> (k <= length l)%nat -> firstn k l <> [].
Proof.
  intros k l H1 H2 Hc.
  destruct l as [| a rest].
  - simpl in H2. lia.
  - destruct k as [| k'].
    + lia.
    + simpl in Hc. discriminate.
Qed.

(* 表长吃满：skipn 段吃空 *)
Lemma rotc_skipn_all : forall (l : list Q) (k : nat),
  (length l <= k)%nat -> skipn k l = [].
Proof.
  induction l as [| a rest IH]; intros k Hk.
  - destruct k; reflexivity.
  - destruct k as [| k'].
    + simpl in Hk. exfalso. lia.
    + simpl. apply IH. simpl in Hk. lia.
Qed.

(* 表长吃满：firstn 段还原全表 *)
Lemma rotc_firstn_all : forall (l : list Q) (k : nat),
  (length l <= k)%nat -> firstn k l = l.
Proof.
  induction l as [| a rest IH]; intros k Hk.
  - destruct k; reflexivity.
  - destruct k as [| k'].
    + simpl in Hk. exfalso. lia.
    + simpl. assert (Hle : (length rest <= k')%nat) by (simpl in Hk; lia).
      rewrite (IH k' Hle). reflexivity.
Qed.

(* 退化判别件：转数不小于表长时真旋转恒等（把弱点钉成定理） *)
Theorem rotc_ge_len_id : forall (k : nat) (l : list Q),
  (length l <= k)%nat -> rotc k l = l.
Proof.
  intros k l Hk. unfold rotc.
  rewrite (rotc_skipn_all l k Hk).
  rewrite (rotc_firstn_all l k Hk).
  reflexivity.
Qed.

(* 尾元迁移：转点严格小于表长时 skipn 段尾元 = 全表尾元 *)
Lemma lastq_skipn_kept : forall (l : list Q) (k : nat),
  (k < length l)%nat -> lastq (skipn k l) = lastq l.
Proof.
  induction l as [| a rest IH]; intros k Hlt.
  - simpl in Hlt. exfalso. lia.
  - destruct k as [| k'].
    + reflexivity.
    + simpl in Hlt. destruct rest as [| b bs].
      * simpl in Hlt. exfalso. lia.
      * simpl. apply IH. lia.
Qed.

(* 首元迁移：转数非零时 firstn 段首元 = 全表首元 *)
Lemma hd_firstn_kept : forall (k : nat) (l : list Q),
  (0 < k)%nat -> hd 0 (firstn k l) = hd 0 l.
Proof.
  intros k l Hk. destruct l as [| a rest].
  - destruct k; simpl; reflexivity.
  - destruct k as [| k'].
    + exfalso. lia.
    + simpl. reflexivity.
Qed.

(* 排序表首元最小：hd 0 l 不超过任意成员 *)
Lemma sorted_hd_min : forall (l : list Q), SortedQ l ->
  forall z : Q, In z l -> (hd 0 l <= z)%Q.
Proof.
  induction l as [| a rest IH]; intros HS z Hin.
  - destruct Hin.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    simpl. destruct Hin as [Hin | Hin].
    + subst. apply Qle_refl.
    + apply HFa. exact Hin.
Qed.

(* 排序表尾元最大：任意成员不超过 lastq *)
Lemma sorted_lastq_max : forall (l : list Q), SortedQ l ->
  forall z : Q, In z l -> (z <= lastq l)%Q.
Proof.
  induction l as [| a rest IH]; intros HS z Hin.
  - destruct Hin.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    destruct rest as [| b bs].
    + destruct Hin as [Hin | Hin].
      * subst. simpl. apply Qle_refl.
      * destruct Hin.
    + destruct Hin as [Hin | Hin].
      * subst. change (lastq (z :: b :: bs)) with (lastq (b :: bs)).
        apply HFa. apply xq_lastq_In. simpl. discriminate.
      * change (lastq (a :: b :: bs)) with (lastq (b :: bs)).
        exact (IH HSr z Hin).
Qed.

(* 区间引理：排序表内两元之差不超过 spread（= lastq − hd） *)
Lemma sorted_sub_le_spread : forall (l : list Q) (z w : Q),
  SortedQ l -> In z l -> In w l -> (z - w <= lastq l - hd 0 l)%Q.
Proof.
  intros l z w HS Hz Hw.
  assert (Hzm : (z <= lastq l)%Q) by (apply (sorted_lastq_max l HS z Hz)).
  assert (Hwn : (hd 0 l <= w)%Q) by (apply (sorted_hd_min l HS w Hw)).
  apply (proj2 (Qle_0_sub' (z - w) (lastq l - hd 0 l))).
  assert (Hr : (lastq l - hd 0 l - (z - w) == (lastq l - z) + (w - hd 0 l))%Q)
    by ring.
  rewrite Hr.
  apply qadd_nonneg.
  - apply (proj1 (Qle_0_sub' z (lastq l))). exact Hzm.
  - apply (proj1 (Qle_0_sub' (hd 0 l) w)). exact Hwn.
Qed.

(* ========== §4 旗舰：排序表循环旋转熵精确闭式 ========== *)

(* 中段精确式：1 <= k < 表长时，rotc k l = [a_{k+1}..a_n; a_1..a_k]，
   相邻差总和 = (尾元−转点) + (尾元−首元) + (转点回卷−首元)。
   证法 = 接缝分解 + 双望远镜（对两段各套 xq_telescope）
   + 接缝项 |hd l − lastq l| 按序褪绝对值。 *)
Theorem H_adj_rotc_exact_mid : forall (k : nat) (l : list Q),
  SortedQ l -> (1 <= k)%nat -> (k < length l)%nat ->
  H_adj (rotc k l) == (lastq l - hd 0 (skipn k l))
                    + (lastq l - hd 0 l)
                    + (lastq (firstn k l) - hd 0 l).
Proof.
  intros k l HS H1 H2.
  assert (HSs : SortedQ (skipn k l)) by (apply skipn_SortedQ; exact HS).
  assert (HSf : SortedQ (firstn k l)) by (apply firstn_SortedQ; exact HS).
  assert (Hnes : skipn k l <> []) by (apply (skipn_ne_of_lt k l H2)).
  assert (Hnef : firstn k l <> []).
  { intro Hc. destruct l as [| a rest].
    - simpl in H2. exfalso. lia.
    - destruct k as [| k'].
      + exfalso. lia.
      + simpl in Hc. discriminate. }
  assert (HE : H_adj (rotc k l) == H_adj (skipn k l ++ firstn k l))
    by reflexivity.
  rewrite HE.
  rewrite (H_adj_app_seam (skipn k l) (firstn k l) Hnes Hnef).
  rewrite (xq_telescope (skipn k l) HSs).
  rewrite (xq_telescope (firstn k l) HSf).
  rewrite (lastq_skipn_kept l k H2).
  rewrite (hd_firstn_kept k l H1).
  assert (Hab : Qabs (hd 0 l - lastq l) == lastq l - hd 0 l).
  { rewrite (xq_abs_sub_comm (hd 0 l) (lastq l)).
    apply xq_abs_id.
    apply (proj1 (Qle_0_sub' (hd 0 l) (lastq l))).
    apply xq_hd_le_lastq. exact HS. }
  rewrite Hab. ring.
Qed.

(* 边界精确式一：零转恒等 *)
Theorem H_adj_rotc_exact_0 : forall l : list Q, SortedQ l ->
  H_adj (rotc 0 l) == lastq l - hd 0 l.
Proof.
  intros l HS. rewrite rotc_0. apply xq_telescope. exact HS.
Qed.

(* 边界精确式二：转数不小于表长恒等 *)
Theorem H_adj_rotc_exact_ge : forall (k : nat) (l : list Q), SortedQ l ->
  (length l <= k)%nat -> H_adj (rotc k l) == lastq l - hd 0 l.
Proof.
  intros k l HS Hk.
  rewrite (rotc_ge_len_id k l Hk). apply xq_telescope. exact HS.
Qed.

(* 边界精确式三：短表（表长不超过 1）任意转数恒等 *)
Theorem H_adj_rotc_exact_short : forall (k : nat) (l : list Q), SortedQ l ->
  (length l <= 1)%nat -> H_adj (rotc k l) == lastq l - hd 0 l.
Proof.
  intros k l HS Hn.
  destruct (cyc_nat_le_gt_cases (length l) k) as [Hle | Hgt].
  - apply (H_adj_rotc_exact_ge k l HS Hle).
  - assert (H0 : (k = 0)%nat) by lia.
    rewrite H0. rewrite rotc_0. apply xq_telescope. exact HS.
Qed.

(* 旗舰二分精确定理：中段取三项闭式，边界取 spread 式，二者必居其一 *)
Theorem H_adj_rotc_sorted_exact : forall (k : nat) (l : list Q), SortedQ l ->
  H_adj (rotc k l) == (lastq l - hd 0 (skipn k l))
                    + (lastq l - hd 0 l)
                    + (lastq (firstn k l) - hd 0 l)
  \/ H_adj (rotc k l) == lastq l - hd 0 l.
Proof.
  intros k l HS.
  destruct (cyc_nat_le_gt_cases (length l) k) as [Hge | Hlt].
  - right. apply (H_adj_rotc_exact_ge k l HS Hge).
  - destruct k as [| k'].
    + right. rewrite rotc_0. apply xq_telescope. exact HS.
    + left.
      assert (H1 : (1 <= S k')%nat) by lia.
      apply (H_adj_rotc_exact_mid (S k') l HS H1 Hlt).
Qed.

(* ========== §5 主件：3·spread 上界（旋转代价 <= 3 倍最小代价） ========== *)

Theorem H_adj_rotc_ub3 : forall (k : nat) (l : list Q),
  SortedQ l -> l <> [] -> (H_adj (rotc k l) <= 3 * (lastq l - hd 0 l))%Q.
Proof.
  intros k l HS Hne.
  assert (Hsp : (0 <= lastq l - hd 0 l)%Q)
    by (apply (proj1 (Qle_0_sub' (hd 0 l) (lastq l)));
        apply xq_hd_le_lastq; exact HS).
  destruct (cyc_nat_le_gt_cases (length l) k) as [Hge | Hlt].
  - (* k >= 表长：恒等支 *)
    rewrite (rotc_ge_len_id k l Hge).
    apply (Qle_trans (H_adj l) (lastq l - hd 0 l) (3 * (lastq l - hd 0 l))).
    + apply cyc_qeq_le. apply xq_telescope. exact HS.
    + apply cyc_le_triple. exact Hsp.
  - destruct k as [| k'].
    + (* 零转支 *)
      rewrite rotc_0.
      apply (Qle_trans (H_adj l) (lastq l - hd 0 l) (3 * (lastq l - hd 0 l))).
      * apply cyc_qeq_le. apply xq_telescope. exact HS.
      * apply cyc_le_triple. exact Hsp.
    + (* 中段支：三项闭式逐项 spread 化后求和 *)
      assert (H1 : (1 <= S k')%nat) by lia.
      assert (Hnef : firstn (S k') l <> [])
        by (apply (firstn_ne_of_lt (S k') l H1); lia).
      assert (Hnes : skipn (S k') l <> [])
        by (apply (skipn_ne_of_lt (S k') l Hlt)).
      assert (HEm : H_adj (rotc (S k') l)
                    == (lastq l - hd 0 (skipn (S k') l))
                     + (lastq l - hd 0 l)
                     + (lastq (firstn (S k') l) - hd 0 l))
        by (apply (H_adj_rotc_exact_mid (S k') l HS H1 Hlt)).
      apply (Qle_trans _ ((lastq l - hd 0 (skipn (S k') l))
                        + (lastq l - hd 0 l)
                        + (lastq (firstn (S k') l) - hd 0 l))
                        (3 * (lastq l - hd 0 l))).
      * apply cyc_qeq_le. exact HEm.
      * assert (HT1 : ((lastq l - hd 0 (skipn (S k') l))
                       <= (lastq l - hd 0 l))%Q).
        { apply (sorted_sub_le_spread l (lastq l)
                   (hd 0 (skipn (S k') l)) HS).
          - apply xq_lastq_In. exact Hne.
          - exact (skipn_incl l (S k') (hd 0 (skipn (S k') l))
                     (xq_hd_In_gen (skipn (S k') l) Hnes)). }
        assert (HT3 : ((lastq (firstn (S k') l) - hd 0 l)
                       <= (lastq l - hd 0 l))%Q).
        { apply (sorted_sub_le_spread l (lastq (firstn (S k') l))
                   (hd 0 l) HS).
          - exact (firstn_incl l (S k') (lastq (firstn (S k') l))
                     (xq_lastq_In (firstn (S k') l) Hnef)).
          - apply xq_hd_In_gen. exact Hne. }
        assert (H3 : (3 * (lastq l - hd 0 l)
                      == (lastq l - hd 0 l) + (lastq l - hd 0 l)
                       + (lastq l - hd 0 l))%Q) by ring.
        apply (Qle_trans _ ((lastq l - hd 0 l) + (lastq l - hd 0 l)
                          + (lastq l - hd 0 l))
                          (3 * (lastq l - hd 0 l))).
        -- apply qadd_le.
           ++ apply qadd_le; [ exact HT1 | apply Qle_refl ].
           ++ exact HT3.
        -- apply cyc_qeq_le. apply Qeq_sym. exact H3.
Qed.

(* ========== §6 加分项：真动态上确界 Hsup_cyc ========== *)

(* 二元最大值：走 Qle_bool 两分，绕开 stdlib 缺席的 Qmax 引理族；
   上界两向只需布尔分支 + Qle_bool_iff/Qle_bool_false_le，零总序前提 *)
Definition qmax2 (x y : Q) : Q := if Qle_bool x y then y else x.

Lemma qmax2_ub_l : forall x y : Q, (x <= qmax2 x y)%Q.
Proof.
  intros x y. unfold qmax2. destruct (Qle_bool x y) eqn:E.
  - apply (proj1 (Qle_bool_iff x y)). exact E.
  - apply Qle_refl.
Qed.

Lemma qmax2_ub_r : forall x y : Q, (y <= qmax2 x y)%Q.
Proof.
  intros x y. unfold qmax2. destruct (Qle_bool x y) eqn:E.
  - apply Qle_refl.
  - apply Qle_bool_false_le. exact E.
Qed.

(* 真动态上确界：前 k+1 个转数（0..k）上 H_adj (rotc i l) 的逐点累积最大 *)
Fixpoint Hsup_cyc (l : list Q) (n : nat) : Q :=
  match n with
  | O => H_adj (rotc 0 l)
  | S n' => qmax2 (Hsup_cyc l n') (H_adj (rotc (S n') l))
  end.

(* 单调：加测一转不减（qmax2_ub_l 一步收口） *)
Theorem Hsup_cyc_mono : forall (l : list Q) (n : nat),
  (Hsup_cyc l n <= Hsup_cyc l (S n))%Q.
Proof.
  intros l n. induction n as [| n IH].
  - cbn [Hsup_cyc]. apply qmax2_ub_l.
  - cbn [Hsup_cyc]. apply qmax2_ub_l.
Qed.

(* 界：真动态上确界也不越过 3·spread *)
Theorem Hsup_cyc_ub : forall (l : list Q) (n : nat), SortedQ l -> l <> [] ->
  (Hsup_cyc l n <= 3 * (lastq l - hd 0 l))%Q.
Proof.
  intros l n HS Hne. induction n as [| n IH].
  - cbn [Hsup_cyc]. apply (H_adj_rotc_ub3 0 l HS Hne).
  - cbn [Hsup_cyc]. unfold qmax2.
    destruct (Qle_bool (Hsup_cyc l n) (H_adj (rotc (S n) l))) eqn:E.
    + apply (H_adj_rotc_ub3 (S n) l HS Hne).
    + exact IH.
Qed.

(* 达到性：上确界总在某个具体转数处取到（布尔分支直接给见证） *)
Theorem Hsup_cyc_attained : forall (l : list Q) (n : nat),
  exists i : nat, (i <= n)%nat /\ Hsup_cyc l n == H_adj (rotc i l).
Proof.
  intros l n. induction n as [| n IH].
  - exists 0%nat. split.
    + lia.
    + cbn [Hsup_cyc]. apply Qeq_refl.
  - destruct IH as [i [Hin Hval]].
    cbn [Hsup_cyc]. unfold qmax2.
    destruct (Qle_bool (Hsup_cyc l n) (H_adj (rotc (S n) l))) eqn:E.
    + exists (S n). split.
      * lia.
      * apply Qeq_refl.
    + exists i. split.
      * lia.
      * exact Hval.
Qed.

(* ========== §7 数值锚 ========== *)

(* 见证列 [0;1;2]：k=1 时 H_adj = |2−1|+|0−2| = 3（闭 Q 值一发判定） *)
Theorem rotc_H_wit_mid : H_adj (rotc 1 [0;1;2]) == 3%Q.
Proof. reflexivity. Qed.

(* 见证列 [0;1;2]：k=0 时 H_adj = spread = 2（最小值锚） *)
Theorem rotc_H_wit_min : H_adj (rotc 0 [0;1;2]) == 2%Q.
Proof. reflexivity. Qed.

(* ========== §8 公理面审计（G4） ========== *)

Print Assumptions rotc_two_runs.
Print Assumptions H_adj_app_seam.
Print Assumptions rotc_ge_len_id.
Print Assumptions H_adj_rotc_exact_mid.
Print Assumptions H_adj_rotc_exact_0.
Print Assumptions H_adj_rotc_exact_ge.
Print Assumptions H_adj_rotc_exact_short.
Print Assumptions H_adj_rotc_sorted_exact.
Print Assumptions H_adj_rotc_ub3.
Print Assumptions Hsup_cyc_mono.
Print Assumptions Hsup_cyc_ub.
Print Assumptions Hsup_cyc_attained.
Print Assumptions rotc_H_wit_mid.
Print Assumptions rotc_H_wit_min.

(* ============================================================
   §M5-1 归并分隔注 —— 以下为原 DTPT_HsupStable.v 全文（U18-3 席）
   M5 席追加至本文件尾：除头部与 Require 块（DTPT/DTPT_ROTC/DTPT_Cyc，
   经本文件头部现有 Require 均可达）外逐字保留，声明序与证法零改动。
   对账注记见本文件头【四】。
   ============================================================ *)
(* ========== §1 切段四件套（skipn/firstn 对 app 的分段自建，
   不赌 stdlib skipn_app/firstn_app 的 9.0 形状） ========== *)

(* m 不超过前段长：skipn m (b++c) 吃进 b 的一段，剩整段 c *)
Lemma hs_skipn_app_le : forall (b : list Q) (m : nat) (c : list Q),
  (m <= length b)%nat -> skipn m (b ++ c) = skipn m b ++ c.
Proof.
  induction b as [| x bs IH]; intros m c Hm.
  - destruct m as [| m'].
    + reflexivity.
    + cbn in Hm. exfalso. lia.
  - destruct m as [| m'].
    + reflexivity.
    + cbn. assert (Hm' : (m' <= length bs)%nat) by (cbn in Hm; lia).
      rewrite (IH m' c Hm'). reflexivity.
Qed.

(* m 不超过前段长：firstn m (b++c) 只吃前段 *)
Lemma hs_firstn_app_le : forall (b : list Q) (m : nat) (c : list Q),
  (m <= length b)%nat -> firstn m (b ++ c) = firstn m b.
Proof.
  induction b as [| x bs IH]; intros m c Hm.
  - destruct m as [| m'].
    + reflexivity.
    + cbn in Hm. exfalso. lia.
  - destruct m as [| m'].
    + reflexivity.
    + cbn. assert (Hm' : (m' <= length bs)%nat) by (cbn in Hm; lia).
      rewrite (IH m' c Hm'). reflexivity.
Qed.

(* 前段长不超过 k：skipn k (a++c) 越过 a，剩 skipn (k - |a|) c *)
Lemma hs_skipn_app_r : forall (a : list Q) (k : nat) (c : list Q),
  (length a <= k)%nat -> skipn k (a ++ c) = skipn (k - length a) c.
Proof.
  induction a as [| x as' IH]; intros k c Hk.
  - destruct k as [| k']; reflexivity.
  - destruct k as [| k'].
    + cbn in Hk. exfalso. lia.
    + cbn. assert (Hk' : (length as' <= k')%nat) by (cbn in Hk; lia).
      apply (IH k' c Hk').
Qed.

(* firstn 对 app 的一般分段（firstn_app 的同形自建件） *)
Lemma hs_firstn_app_gen : forall (a : list Q) (k : nat) (c : list Q),
  firstn k (a ++ c) = firstn k a ++ firstn (k - length a) c.
Proof.
  induction a as [| x as' IH]; intros k c.
  - destruct k as [| k']; reflexivity.
  - destruct k as [| k']; [ reflexivity | cbn; rewrite (IH k' c); reflexivity ].
Qed.

(* ========== §2 保底件·局部周期律（clamp 语义诚实版） ========== *)

(* ①a 守卫版加法律：m + n 不越过表长时旋转次数相加。
   证法：l 分解 a=firstn n l / b=skipn n l（pose 折叠护 n 的
   替换面，U3 卡配方），rotc_rot_app 把 rotc n l 换位成 b++a，
   两侧各自切段后 app_assoc 重排收口。 *)
Theorem rotc_add_local : forall (m n : nat) (l : list Q),
  (m + n <= length l)%nat -> rotc m (rotc n l) = rotc (m + n) l.
Proof.
  intros m n l Hmn.
  assert (Hnle : (n <= length l)%nat) by lia.
  pose (a := firstn n l).
  pose (b := skipn n l).
  assert (Hla : (length a = n)%nat) by exact (firstn_length_le l Hnle).
  assert (Hsplit : l = a ++ b)
    by (unfold a, b; symmetry; apply firstn_skipn).
  assert (Hrot : rotc n l = b ++ a).
  { rewrite <- Hla. rewrite Hsplit. apply rotc_rot_app. }
  assert (Hll : (length l = length a + length b)%nat)
    by (rewrite Hsplit; apply length_app).
  assert (Hmb : (m <= length b)%nat) by lia.
  assert (Hage : (length a <= m + n)%nat) by lia.
  rewrite Hrot. rewrite Hsplit.
  unfold rotc.
  rewrite (hs_skipn_app_le b m a Hmb).
  rewrite (hs_firstn_app_le b m a Hmb).
  rewrite (hs_skipn_app_r a (m + n) b Hage).
  rewrite (hs_firstn_app_gen a (m + n) b).
  rewrite (rotc_firstn_all a (m + n) Hage).
  assert (Hsub : (m + n - length a = m)%nat) by lia.
  rewrite Hsub.
  rewrite <- app_assoc.
  reflexivity.
Qed.

(* ①b 真周期面=冻结形：k + 表长 转已越界，与整一圈同值冻结在 l *)
Theorem rotc_freeze_local : forall (k : nat) (l : list Q),
  rotc (k + length l) l = rotc (length l) l.
Proof.
  intros k l.
  assert (H1 : rotc (k + length l) l = l)
    by (apply rotc_ge_len_id; lia).
  rewrite H1. rewrite rotc_full. reflexivity.
Qed.

(* ①c 诚实裁决件一：无守卫周期式为假（闭反例 [0;1;2], k=1：
   rotc 4 l = l 而 rotc 1 l = [1;2;0]，非退化旋转在） *)
Theorem rotc_periodic_naive_false :
  exists (l : list Q) (k : nat), rotc (k + length l) l <> rotc k l.
Proof.
  exists [0;1;2], 1%nat.
  intro Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* ①c 诚实裁决件二：无守卫加法律为假（闭反例 [0;1;2], m=3, n=1：
   rotc 3 (rotc 1 l) = [1;2;0] 而 rotc 4 l = l） *)
Theorem rotc_add_naive_false :
  exists (l : list Q) (m n : nat), rotc m (rotc n l) <> rotc (m + n) l.
Proof.
  exists [0;1;2], 3%nat, 1%nat.
  intro Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* ========== §3 冻结引擎与旗舰 ========== *)

(* qmax2 吸收已有值：右支不更大时最大值就是左支（Qmax 幂等面） *)
Lemma qmax2_le : forall x y : Q, (y <= x)%Q -> (qmax2 x y <= x)%Q.
Proof.
  intros x y Hy. unfold qmax2. destruct (Qle_bool x y) eqn:E.
  - exact Hy.
  - apply Qle_refl.
Qed.

(* 主件·单调面（跨距版增补）：Hsup_cyc_mono（U8 已证防重引用）
   的相邻步拉成任意跨距 a <= b 的单调链 *)
Theorem Hsup_cyc_mono_from : forall (l : list Q) (a b : nat),
  (a <= b)%nat -> (Hsup_cyc l a <= Hsup_cyc l b)%Q.
Proof.
  intros l a b. induction b as [| b IH].
  - intros Ha. assert (H0 : a = 0%nat) by lia.
    rewrite H0. apply Qle_refl.
  - intros Ha. destruct (cyc_nat_le_gt_cases a b) as [Hle | Hgt].
    + apply (Qle_trans (Hsup_cyc l a) (Hsup_cyc l b) (Hsup_cyc l (S b))).
      * apply IH. exact Hle.
      * apply Hsup_cyc_mono.
    + assert (Ha' : (a = S b)%nat) by lia.
      rewrite Ha'. apply Qle_refl.
Qed.

(* 基值面：H_adj l 就是指标 0 处的谱值（rotc_0 的换算） *)
Lemma H_adj_eq_Hsup0 : forall l : list Q, (H_adj l == Hsup_cyc l 0)%Q.
Proof.
  intros l. cbn [Hsup_cyc]. rewrite rotc_0. apply Qeq_refl.
Qed.

(* 单步冻结：指标越过表长后，加测一转不改变上确界——
   新值 H_adj (rotc (S n) l) = H_adj l（rotc_ge_len_id），
   而 H_adj l <= Hsup_cyc l n（跨距单调链），qmax2 两向吸收 *)
Theorem Hsup_cyc_step_frozen : forall (l : list Q) (n : nat),
  (length l <= n)%nat -> Hsup_cyc l (S n) == Hsup_cyc l n.
Proof.
  intros l n Hn.
  assert (Hle : (length l <= S n)%nat) by lia.
  cbn [Hsup_cyc].
  rewrite (rotc_ge_len_id (S n) l Hle).
  apply Qle_antisym.
  - apply qmax2_le.
    apply (Qle_trans (H_adj l) (Hsup_cyc l 0) (Hsup_cyc l n)).
    + apply cyc_qeq_le. apply H_adj_eq_Hsup0.
    + apply (Hsup_cyc_mono_from l 0 n). lia.
  - apply qmax2_ub_l.
Qed.

(* ========== 旗舰·冻结定理：上确界在 n = 表长 处冻结 ========== *)
(* 路线：对 n 归纳；n >= 表长 支走单步冻结 + 归纳假设（Qeq 传递），
   n < 表长 支由 length l <= S n 夹出 length l = S n（同指数恒等）。 *)
Theorem Hsup_cyc_stable : forall (l : list Q) (n : nat),
  (length l <= n)%nat -> Hsup_cyc l n == Hsup_cyc l (length l).
Proof.
  intros l n. induction n as [| n IH].
  - intros Hn. destruct l as [| a rest].
    + apply Qeq_refl.
    + cbn in Hn. exfalso. lia.
  - intros Hn.
    destruct (cyc_nat_le_gt_cases (length l) n) as [Hle | Hgt].
    + apply (Qeq_trans (Hsup_cyc l (S n)) (Hsup_cyc l n)).
      * apply (Hsup_cyc_step_frozen l n Hle).
      * apply IH. exact Hle.
    + assert (Heq : (length l = S n)%nat) by lia.
      rewrite Heq. apply Qeq_refl.
Qed.

(* ========== §4 加分·谱有限性：旋转谱至多 length l 个不同值 ========== *)

(* 构造性归约：任意转数的 rotc 值都落在前 length l 个转数的谱内
   （k < 表长取 k' = k；k >= 表长取 k' = 0，越界冻结回 rotc 0） *)
Theorem rotc_spectrum_bound : forall (k : nat) (l : list Q),
  exists k' : nat, (k' <= length l - 1)%nat /\ rotc k l = rotc k' l.
Proof.
  intros k l.
  destruct (cyc_nat_le_gt_cases (S k) (length l)) as [Hlt | Hge].
  - exists k. split.
    + lia.
    + reflexivity.
  - assert (Hge' : (length l <= k)%nat) by lia.
    exists 0%nat. split.
    + lia.
    + rewrite (rotc_ge_len_id k l Hge'). rewrite rotc_0. reflexivity.
Qed.

(* 值域面：H_adj 谱同样被前 length l 个转数穷尽 *)
Theorem H_adj_spectrum_bound : forall (k : nat) (l : list Q),
  exists k' : nat,
    (k' <= length l - 1)%nat /\ H_adj (rotc k l) == H_adj (rotc k' l).
Proof.
  intros k l. destruct (rotc_spectrum_bound k l) as [k' [Hle Heq]].
  exists k'. split.
  - exact Hle.
  - rewrite Heq. apply Qeq_refl.
Qed.

(* 谱有限推论：上确界总在 i <= length l 的具体转数处取到
   （Hsup_cyc_attained 的见证越界时换到冻结指标 length l） *)
Theorem Hsup_cyc_attained_range : forall (l : list Q) (n : nat),
  exists i : nat, (i <= length l)%nat /\ Hsup_cyc l n == H_adj (rotc i l).
Proof.
  intros l n.
  destruct (Hsup_cyc_attained l n) as [i [Hin Hval]].
  destruct (cyc_nat_le_gt_cases (S i) (length l)) as [Hlt | Hge].
  - exists i. split.
    + lia.
    + exact Hval.
  - assert (Hge' : (length l <= i)%nat) by lia.
    rewrite (rotc_ge_len_id i l Hge') in Hval.
    exists (length l). split.
    + apply le_n.
    + rewrite rotc_full. exact Hval.
Qed.

(* ========== §5 数值锚 ========== *)

(* 见证列 [0;1;2]（表长 3）：n=5 已冻结，与 n=2 同值 3
   （谱 {2;3}，最大值在 k=1,2 取到）；旗舰闭项一发判定 *)
Theorem Hsup_cyc_stable_wit : Hsup_cyc [0;1;2] 5 == Hsup_cyc [0;1;2] 2.
Proof. reflexivity. Qed.

(* 冻结值就是谱最大 3（对照 rotc_H_wit_mid 的中段锚） *)
Theorem Hsup_cyc_frozen_value_wit : Hsup_cyc [0;1;2] 7 == 3%Q.
Proof. reflexivity. Qed.

End DTPT_Cyc.
Import DTPT_Cyc.

(* ========== §6 公理面审计（G4） ========== *)

Print Assumptions rotc_add_local.
Print Assumptions rotc_freeze_local.
Print Assumptions rotc_periodic_naive_false.
Print Assumptions rotc_add_naive_false.
Print Assumptions Hsup_cyc_mono_from.
Print Assumptions Hsup_cyc_step_frozen.
Print Assumptions Hsup_cyc_stable.
Print Assumptions rotc_spectrum_bound.
Print Assumptions H_adj_spectrum_bound.
Print Assumptions Hsup_cyc_attained_range.
Print Assumptions Hsup_cyc_stable_wit.
Print Assumptions Hsup_cyc_frozen_value_wit.
