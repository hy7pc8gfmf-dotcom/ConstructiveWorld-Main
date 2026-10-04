(* ==========================================================================
   abl_dtr_core1.v —— DTPT_Rotation 前件参数消解供给·卷一（参数 1–36）。
   ── 使命：宿主 DTPT_Rotation.v 本体 106 前件参数登记序第 1–36 位（语句
   坐标 :49–:575，25 条语句）逐参数消解供给，24 条全取 A 直供形：语句面＝
   登记形经 dtr_ 前缀映射逐字同构，证明体就地构造真构造、零宿主件引用
   （卷一 36 参数前件全为任意数据上的 Q 序等／成员／保序／非空卫哨／nat 序
   义务，无条件化不可构造）。36 参数＝35 供给＋1 登记：rotc_two_runs 结论面
   为 Prop 层合取——红线二（禁 Prop 入语句位）与其 And 化 Type 层积形的
   Separate Extraction 单子型拒绝（可提取性）正面相撞，照登记不供给并如实
   申报，其双分量（firstn/skipn 保序）由参数 5/6 两件全数承载零语义流失；
   另非参数位登记两条（H_rotc_separates／rotc_Pinf_separates，存在体旗零
   顶层前件）。宿主件零字节动，本件零 Require 宿主。
   ── 依赖：仅 stdlib（QArith.QArith／QArith.Qabs／List／Bool／Arith／Lia／
   Permutation＋Extraction 检验面）——宿主所需 DTPT/DTPT_Entropy 定义以
   dtr_ 同构副本本地重建（dtr_H_adj／dtr_rotc／dtr_SortedQ 系现档逐字
   同构，同名同构双副本惯例之延续）。
   ── 对标行：A 直供零宿主引用先例＝abl_s01_supply.v 与 abl_dtd_core1。
   ── 构造性注记：全件 Qed 真构造，零承认式声明、零悬置前提、零经典逻辑、
   零节变量声明位；语句面全数＝stdlib Q 离散可判定层既成形态；供给语句面
   零混载形态（零否定／零等价／零存在／零 Prop 层析取合取）；提取面＝数据
   层真实现（rotc/skipn/firstn/sum_adjdiff/lastq 递归真码）＋逐件 Separate
   Extraction，Obj.magic 零判据。
   ── 编译配方：池 cwd＝沙箱/现役/abl_r85_supply_pool；source Live 库根
   toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 后 nice -19
   rocq c -native-compiler no
   -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
   abl_dtr_core1.v；绿判＝EXIT=0／日志零 Error／.vo 头 8 字节
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
(* 〇 数据层副本（宿主 DTPT_Rotation.v 现档逐字同构，dtr_ 前缀隔离；      *)
(*    dtr_sum_adjdiff/dtr_H_adj/dtr_lastq＝DTPT.v :116-:125/:621-:628    *)
(*    同构（宿主经 Import DTPT 使用）；dtr_rotc＝DTPT_Rotation.v :203；   *)
(*    dtr_SortedQ＝DTPT_Entropy.v :270-:273（宿主 Import 序取后者）同构；  *)
(*    全五件＝提取面真实现承载，非参数位）                                *)
(* ============================================================ *)

Fixpoint dtr_sum_adjdiff (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => match xs with
               | [] => 0
               | y :: _ => Qabs (y - x) + dtr_sum_adjdiff xs
               end
  end.

Definition dtr_H_adj (l : list Q) : Q := dtr_sum_adjdiff l.

Fixpoint dtr_lastq (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => match xs with
               | [] => x
               | _ :: _ => dtr_lastq xs
               end
  end.

Definition dtr_rotc (n : nat) (l : list Q) : list Q :=
  skipn n l ++ firstn n l.

Inductive dtr_SortedQ : list Q -> Prop :=
| dtr_sortQ_nil : dtr_SortedQ []
| dtr_sortQ_cons : forall x xs,
    dtr_SortedQ xs -> Forall (fun z => (x <= z)%Q) xs -> dtr_SortedQ (x :: xs).

(* ============================================================ *)
(* 一 供给定理区（参数 1–7，语句 1–7）＋Q 序工具箱                        *)
(* ============================================================ *)

(* 参数 1（DTPT_Rotation.v:49） *)
Theorem dtr_cyc_qeq_le : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros x y H. unfold Qeq in H. unfold Qle. lia.
Qed.

(* 辅助件 A1（DTPT.v:144 同内容 就地构造 重演；非参数位基础设施） *)
Lemma dtr_qadd_le : forall a b c d : Q, a <= b -> c <= d -> (a + c <= b + d)%Q.
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

(* 辅助件 A2（DTPT.v:491 同内容 就地构造 重演；非参数位基础设施） *)
Lemma dtr_qadd_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> (0 <= a + b)%Q.
Proof.
  intros [an ad] [bn bd]; simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

(* 辅助件 A3＝宿主基础件 Qle_0_sub'（DTPT.v:173 iff 形）双向分解之正向       *)
(* （iff 语句位不入顶层，照  「iff 前件化双单向干净陈述面」分解惯例）    *)
Lemma dtr_qle_0_sub_inv : forall x y : Q, x <= y -> (0 <= y - x)%Q.
Proof.
  intros [nx dx] [ny dy] H.
  unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl; lia.
Qed.

(* 辅助件 A4＝Qle_0_sub' 分解之逆向 *)
Lemma dtr_qle_0_sub_intro : forall x y : Q, (0 <= y - x)%Q -> x <= y.
Proof.
  intros [nx dx] [ny dy] H.
  unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl; lia.
Qed.

(* 参数 2（DTPT_Rotation.v:66） *)
Theorem dtr_cyc_le_triple : forall s : Q, (0 <= s)%Q -> (s <= 3 * s)%Q.
Proof.
  intros s Hs.
  assert (H3 : (3 * s == s + s + s)%Q) by ring.
  apply (Qle_trans s (s + s + s) (3 * s)).
  - apply dtr_qle_0_sub_intro.
    assert (Hr : (s + s + s - s == s + s)%Q) by ring.
    rewrite Hr. exact (dtr_qadd_nonneg s s Hs Hs).
  - apply dtr_cyc_qeq_le. apply Qeq_sym. exact H3.
Qed.

(* 参数 3（DTPT_Rotation.v:79） *)
Theorem dtr_firstn_incl : forall (l : list Q) (k : nat) (z : Q),
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

(* 参数 4（DTPT_Rotation.v:91） *)
Theorem dtr_skipn_incl : forall (l : list Q) (k : nat) (z : Q),
  In z (skipn k l) -> In z l.
Proof.
  induction l as [| a rest IH]; intros k z Hin.
  - destruct k; simpl in Hin; destruct Hin.
  - destruct k as [| k']; simpl in Hin.
    + exact Hin.
    + right. exact (IH k' z Hin).
Qed.

(* 参数 5（DTPT_Rotation.v:101） *)
Theorem dtr_firstn_SortedQ : forall (l : list Q) (k : nat),
  dtr_SortedQ l -> dtr_SortedQ (firstn k l).
Proof.
  induction l as [| a rest IH]; intros k HS.
  - destruct k as [| k']; simpl; apply dtr_sortQ_nil.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    destruct k as [| k']; simpl.
    + apply dtr_sortQ_nil.
    + apply dtr_sortQ_cons.
      * apply IH. exact HSr.
      * apply Forall_forall. intros z Hz. apply HFa.
        exact (dtr_firstn_incl rest k' z Hz).
Qed.

(* 参数 6（DTPT_Rotation.v:116） *)
Theorem dtr_skipn_SortedQ : forall (l : list Q) (k : nat),
  dtr_SortedQ l -> dtr_SortedQ (skipn k l).
Proof.
  induction l as [| a rest IH]; intros k HS.
  - destruct k as [| k']; simpl; apply dtr_sortQ_nil.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    destruct k as [| k']; simpl.
    + apply dtr_sortQ_cons;
        [ exact HSr | apply Forall_forall; exact HFa ].
    + apply IH. exact HSr.
Qed.

(* 【只登记】参数 7（DTPT_Rotation.v:130，SORTED）——rotc_two_runs 结论面宿主    *)
(* SortedQ … /\ SortedQ … 系 Prop 层合取位（红线二禁入语句位）；And 化      *)
(* Type 层积形 prod (dtr_SortedQ …) (dtr_SortedQ …) 内核可证（检验  实测）  *)
(* 但 Separate Extraction 实拍拒绝（「The informative inductive type prod    *)
(* has a Prop instance」＝单子型携逻辑参为 Extraction 已知不可处理面），红线  *)
(* 二与红线四相撞，判登记不供给（失败显式申报 见交付报告 §五.1）；其内容双分量   *)
(* ＝参数 5/6 两件供给文件（dtr_firstn_SortedQ/dtr_skipn_SortedQ）全数承载。     *)

(* ============================================================ *)
(* 二 供给定理区续（参数 8–13，语句 8–11）＋xq 工具箱                      *)
(* ============================================================ *)

(* 辅助件 B1（DTPT.v:522 同内容重演） *)
Lemma dtr_xq_minus_self : forall x : Q, x - x == 0.
Proof.
  intros [n d]. unfold Qminus, Qeq; simpl. lia.
Qed.

(* 辅助件 B2（DTPT.v:514 同内容重演） *)
Lemma dtr_xq_abs_eq0 : forall x : Q, x == 0 -> Qabs x == 0.
Proof.
  intros [n d] Hx. unfold Qeq in Hx; simpl in Hx.
  assert (Hn : (n = 0)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite Hn. reflexivity.
Qed.

(* 辅助件 B3（DTPT.v:506 同内容重演） *)
Lemma dtr_xq_abs_id : forall x : Q, (0 <= x)%Q -> Qabs x == x.
Proof.
  intros [n d] Hx. unfold Qle in Hx; simpl in Hx.
  assert (Hn : (0 <= n)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite (Z.abs_eq n Hn). reflexivity.
Qed.

(* 辅助件 B4（DTPT.v:555 同内容重演——stdlib Qabs_Qminus Leibniz 等式一跳，  *)
(* 比 DTPT 三件链更短的 就地构造 位） *)
Lemma dtr_xq_abs_sub_comm : forall a b : Q, Qabs (a - b) == Qabs (b - a).
Proof.
  intros a b. rewrite (Qabs_Qminus a b). apply Qeq_refl.
Qed.

(* 辅助件 B5（DTPT.v:527 同内容重演） *)
Lemma dtr_xq_abs_zero : forall x : Q, Qabs (x - x) == 0.
Proof.
  intro x. apply dtr_xq_abs_eq0. apply dtr_xq_minus_self.
Qed.

(* 辅助件 B6（DTPT.v:563 同内容重演） *)
Lemma dtr_xq_H_adj_nonneg : forall l : list Q, (0 <= dtr_H_adj l)%Q.
Proof.
  intro l. induction l as [| a rest IH].
  - apply Qle_refl.
  - destruct rest as [| b bs].
    + apply Qle_refl.
    + change (dtr_H_adj (a :: b :: bs)) with (Qabs (b - a) + dtr_H_adj (b :: bs))%Q.
      apply dtr_qadd_nonneg; [ apply Qabs_nonneg | exact IH ].
Qed.

(* 辅助件 A5（DTPT.v:573 同内容重演；dtr_qadd_le 使用位） *)
Lemma dtr_xq_le_add_abs : forall t h : Q, (h <= Qabs t + h)%Q.
Proof.
  intros t h.
  pose proof (dtr_qadd_le 0 (Qabs t) h h (Qabs_nonneg t) (Qle_refl h)) as HS.
  rewrite Qplus_0_l in HS. exact HS.
Qed.

(* 辅助件 B7（DTPT.v:688 配对距离界同内容重演；参数 12-13 证体引擎） *)
Lemma dtr_xq_pair_dist_le : forall (l : list Q) (x y : Q),
  In x l -> In y l -> (Qabs (x - y) <= dtr_H_adj l)%Q.
Proof.
  induction l as [| a rest IH]; intros x y Hx Hy.
  - exfalso. exact Hx.
  - destruct rest as [| b bs].
    + destruct Hx as [Hx | []]; destruct Hy as [Hy | []]; subst.
      rewrite dtr_xq_abs_zero. apply Qle_refl.
    + change (dtr_H_adj (a :: b :: bs)) with (Qabs (b - a) + dtr_H_adj (b :: bs))%Q.
      destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
      * rewrite dtr_xq_abs_zero. apply dtr_qadd_nonneg;
          [ apply Qabs_nonneg | apply dtr_xq_H_adj_nonneg ].
      * assert (Hr1 : a - y == (a - b) + (b - y)) by ring.
        rewrite Hr1.
        apply (Qle_trans _ (Qabs (a - b) + Qabs (b - y))).
        -- apply Qabs_triangle.
        -- rewrite (dtr_xq_abs_sub_comm a b).
           apply dtr_qadd_le; [ apply Qle_refl
                              | apply IH; [ left; reflexivity | exact Hy ] ].
      * assert (Hr2 : x - a == (x - b) + (b - a)) by ring.
        rewrite Hr2.
        apply (Qle_trans _ (Qabs (x - b) + Qabs (b - a))).
        -- apply Qabs_triangle.
        -- rewrite (Qplus_comm (Qabs (x - b)) (Qabs (b - a))).
           apply dtr_qadd_le; [ apply Qle_refl
                              | apply IH; [ exact Hx | left; reflexivity ] ].
      * apply (Qle_trans _ (dtr_H_adj (b :: bs))).
        -- apply IH; assumption.
        -- apply dtr_xq_le_add_abs.
Qed.

(* 参数 8-9（DTPT_Rotation.v:141）——NEQ 双卫哨照底册参数面逐字透传 *)
Theorem dtr_H_adj_app_seam : forall (u v : list Q),
  u <> [] -> v <> [] ->
  dtr_H_adj (u ++ v) == dtr_H_adj u + dtr_H_adj v + Qabs (hd 0 v - dtr_lastq u).
Proof.
  induction u as [| a rest IH]; intros v Hne Hne2.
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [| b bs].
    + destruct v as [| c v'].
      * exfalso. apply Hne2. reflexivity.
      * change (dtr_H_adj ([a] ++ c :: v')) with (Qabs (c - a) + dtr_H_adj (c :: v'))%Q.
        change (dtr_H_adj [a]) with 0%Q.
        change (dtr_lastq [a]) with a.
        change (hd 0 (c :: v')) with c.
        ring.
    + change (dtr_H_adj ((a :: b :: bs) ++ v))
        with (Qabs (b - a) + dtr_H_adj (b :: bs ++ v))%Q.
      change (dtr_H_adj (a :: b :: bs)) with (Qabs (b - a) + dtr_H_adj (b :: bs))%Q.
      change (dtr_lastq (a :: b :: bs)) with (dtr_lastq (b :: bs)).
      assert (Hne' : b :: bs <> []) by (intro Hcz; discriminate Hcz).
      replace (dtr_H_adj (b :: bs ++ v)) with (dtr_H_adj ((b :: bs) ++ v))
        by reflexivity.
      rewrite (IH v Hne' Hne2).
      ring.
Qed.

(* 参数 10（DTPT_Rotation.v:282）——skipn_all/firstn_all 走证内联断言（宿主     *)
(* rotc_rot_app 三件链之省 Qed 预算等价重演） *)
Theorem dtr_rotc_inv : forall (n : nat) (l : list Q),
  (n <= length l)%nat -> dtr_rotc ((length l - n)%nat) (dtr_rotc n l) = l.
Proof.
  intros n l Hn.
  assert (Hsa : forall c d : list Q, skipn (length c) (c ++ d) = d).
  { intros c d. induction c as [| x xs IHc]; simpl.
    - reflexivity.
    - exact IHc. }
  assert (Hfa : forall c d : list Q, firstn (length c) (c ++ d) = c).
  { intros c d. induction c as [| x xs IHc]; simpl.
    - reflexivity.
    - rewrite IHc. reflexivity. }
  pose (a := firstn n l).
  pose (b := skipn n l).
  assert (Hla : (length a = n)%nat)
    by exact (firstn_length_le l Hn).
  assert (Hsplit : l = a ++ b)
    by (unfold a, b; symmetry; apply firstn_skipn).
  assert (Hab : (length (a ++ b) - length a = length b)%nat)
    by (rewrite length_app; lia).
  unfold dtr_rotc.
  rewrite Hsplit.
  rewrite <- Hla.
  rewrite Hab.
  rewrite (Hsa a b).
  rewrite (Hfa a b).
  rewrite (Hsa b a).
  rewrite (Hfa b a).
  reflexivity.
Qed.

(* 参数 11（DTPT_Rotation.v:329） *)
Theorem dtr_rotc_in : forall (n : nat) (l : list Q) (x : Q),
  In x l -> In x (dtr_rotc n l).
Proof.
  intros n l x Hin.
  assert (Hp : Permutation l (skipn n l ++ firstn n l)).
  { apply Permutation_sym. etransitivity.
    - apply Permutation_app_comm.
    - rewrite firstn_skipn. apply Permutation_refl. }
  apply (Permutation_in x Hp). exact Hin.
Qed.

(* 参数 12-13（DTPT_Rotation.v:342） *)
Theorem dtr_H_rotc_span_lb : forall (n : nat) (l : list Q) (x y : Q),
  In x l -> In y l -> (Qabs (x - y) <= dtr_H_adj (dtr_rotc n l))%Q.
Proof.
  intros n l x y Hx Hy.
  apply (dtr_xq_pair_dist_le (dtr_rotc n l) x y).
  - apply dtr_rotc_in. exact Hx.
  - apply dtr_rotc_in. exact Hy.
Qed.

(* ============================================================ *)
(* 三 供给定理区续（参数 14–28，语句 12–20）                              *)
(* ============================================================ *)

(* 参数 14（DTPT_Rotation.v:390） *)
Theorem dtr_skipn_ne_of_lt : forall (k : nat) (l : list Q),
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

(* 参数 15-16（DTPT_Rotation.v:405） *)
Theorem dtr_firstn_ne_of_lt : forall (k : nat) (l : list Q),
  (0 < k)%nat -> (k <= length l)%nat -> firstn k l <> [].
Proof.
  intros k l H1 H2 Hc.
  destruct l as [| a rest].
  - simpl in H2. lia.
  - destruct k as [| k'].
    + lia.
    + simpl in Hc. discriminate.
Qed.

(* 参数 17（DTPT_Rotation.v:417） *)
Theorem dtr_rotc_skipn_all : forall (l : list Q) (k : nat),
  (length l <= k)%nat -> skipn k l = [].
Proof.
  induction l as [| a rest IH]; intros k Hk.
  - destruct k; reflexivity.
  - destruct k as [| k'].
    + simpl in Hk. exfalso. lia.
    + simpl. apply IH. simpl in Hk. lia.
Qed.

(* 参数 18（DTPT_Rotation.v:428） *)
Theorem dtr_rotc_firstn_all : forall (l : list Q) (k : nat),
  (length l <= k)%nat -> firstn k l = l.
Proof.
  induction l as [| a rest IH]; intros k Hk.
  - destruct k; reflexivity.
  - destruct k as [| k'].
    + simpl in Hk. exfalso. lia.
    + simpl. assert (Hle : (length rest <= k')%nat) by (simpl in Hk; lia).
      rewrite (IH k' Hle). reflexivity.
Qed.

(* 参数 19（DTPT_Rotation.v:440） *)
Theorem dtr_rotc_ge_len_id : forall (k : nat) (l : list Q),
  (length l <= k)%nat -> dtr_rotc k l = l.
Proof.
  intros k l Hk. unfold dtr_rotc.
  rewrite (dtr_rotc_skipn_all l k Hk).
  rewrite (dtr_rotc_firstn_all l k Hk).
  reflexivity.
Qed.

(* 参数 20（DTPT_Rotation.v:450） *)
Theorem dtr_lastq_skipn_kept : forall (l : list Q) (k : nat),
  (k < length l)%nat -> dtr_lastq (skipn k l) = dtr_lastq l.
Proof.
  induction l as [| a rest IH]; intros k Hlt.
  - simpl in Hlt. exfalso. lia.
  - destruct k as [| k'].
    + reflexivity.
    + simpl in Hlt. destruct rest as [| b bs].
      * simpl in Hlt. exfalso. lia.
      * simpl. apply IH. lia.
Qed.

(* 参数 21（DTPT_Rotation.v:463） *)
Theorem dtr_hd_firstn_kept : forall (k : nat) (l : list Q),
  (0 < k)%nat -> hd 0 (firstn k l) = hd 0 l.
Proof.
  intros k l Hk. destruct l as [| a rest].
  - destruct k; simpl; reflexivity.
  - destruct k as [| k'].
    + exfalso. lia.
    + simpl. reflexivity.
Qed.

(* 参数 22-23（DTPT_Rotation.v:474） *)
Theorem dtr_sorted_hd_min : forall (l : list Q), dtr_SortedQ l ->
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

(* 辅助件 B8（DTPT.v:630 同内容重演；参数 24-25 证体使用位） *)
Lemma dtr_xq_lastq_In : forall m : list Q, m <> [] -> In (dtr_lastq m) m.
Proof.
  induction m as [| a rest IH]; intros Hne.
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [| b bs].
    + simpl. left. reflexivity.
    + simpl. right. apply IH. simpl. discriminate.
Qed.

(* 参数 24-25（DTPT_Rotation.v:487） *)
Theorem dtr_sorted_lastq_max : forall (l : list Q), dtr_SortedQ l ->
  forall z : Q, In z l -> (z <= dtr_lastq l)%Q.
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
      * subst. change (dtr_lastq (z :: b :: bs)) with (dtr_lastq (b :: bs)).
        apply HFa. apply dtr_xq_lastq_In. simpl. discriminate.
      * change (dtr_lastq (a :: b :: bs)) with (dtr_lastq (b :: bs)).
        exact (IH HSr z Hin).
Qed.

(* 参数 26-28（DTPT_Rotation.v:506） *)
Theorem dtr_sorted_sub_le_spread : forall (l : list Q) (z w : Q),
  dtr_SortedQ l -> In z l -> In w l -> (z - w <= dtr_lastq l - hd 0 l)%Q.
Proof.
  intros l z w HS Hz Hw.
  assert (Hzm : (z <= dtr_lastq l)%Q) by (apply (dtr_sorted_lastq_max l HS z Hz)).
  assert (Hwn : (hd 0 l <= w)%Q) by (apply (dtr_sorted_hd_min l HS w Hw)).
  apply (dtr_qle_0_sub_intro (z - w) (dtr_lastq l - hd 0 l)).
  assert (Hr : (dtr_lastq l - hd 0 l - (z - w) == (dtr_lastq l - z) + (w - hd 0 l))%Q)
    by ring.
  rewrite Hr.
  apply dtr_qadd_nonneg.
  - apply (dtr_qle_0_sub_inv z (dtr_lastq l)). exact Hzm.
  - apply (dtr_qle_0_sub_inv (hd 0 l) w). exact Hwn.
Qed.

(* ============================================================ *)
(* 四 供给定理区续（参数 29–36，语句 21–25）＋望远镜方程工具箱             *)
(* ============================================================ *)

(* 辅助件 B9（DTPT.v:652 同内容重演；参数 29-31 证体使用位） *)
Lemma dtr_xq_hd_le_lastq : forall l : list Q,
  dtr_SortedQ l -> (hd 0 l <= dtr_lastq l)%Q.
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

(* 辅助件 B10＝望远镜方程（DTPT.v:666 同内容重演；参数 29-36 证体引擎） *)
Lemma dtr_xq_telescope : forall l : list Q,
  dtr_SortedQ l -> dtr_H_adj l == dtr_lastq l - hd 0 l.
Proof.
  induction l as [| a rest IH]; intro HS.
  - reflexivity.
  - destruct rest as [| b bs].
    + change (dtr_H_adj [a]) with 0%Q.
      change (dtr_lastq [a] - hd 0 [a]) with (a - a)%Q.
      symmetry. apply dtr_xq_minus_self.
    + inversion HS as [| x0 xs0 HSr HFa]; subst.
      rewrite Forall_forall in HFa.
      change (dtr_H_adj (a :: b :: bs)) with (Qabs (b - a) + dtr_H_adj (b :: bs))%Q.
      assert (Hab : (0 <= b - a)%Q).
      { apply (dtr_qle_0_sub_inv a b). apply HFa. left. reflexivity. }
      rewrite (dtr_xq_abs_id _ Hab).
      rewrite (IH HSr).
      change (dtr_lastq (a :: b :: bs)) with (dtr_lastq (b :: bs)).
      change (hd 0 (a :: b :: bs)) with a.
      change (hd 0 (b :: bs)) with b.
      ring.
Qed.

(* 参数 29-31（DTPT_Rotation.v:527） *)
Theorem dtr_H_adj_rotc_exact_mid : forall (k : nat) (l : list Q),
  dtr_SortedQ l -> (1 <= k)%nat -> (k < length l)%nat ->
  dtr_H_adj (dtr_rotc k l) == (dtr_lastq l - hd 0 (skipn k l))
                            + (dtr_lastq l - hd 0 l)
                            + (dtr_lastq (firstn k l) - hd 0 l).
Proof.
  intros k l HS H1 H2.
  assert (HSs : dtr_SortedQ (skipn k l)) by (apply dtr_skipn_SortedQ; exact HS).
  assert (HSf : dtr_SortedQ (firstn k l)) by (apply dtr_firstn_SortedQ; exact HS).
  assert (Hnes : skipn k l <> []) by (apply (dtr_skipn_ne_of_lt k l H2)).
  assert (Hnef : firstn k l <> []).
  { intro Hc. destruct l as [| a rest].
    - simpl in H2. exfalso. lia.
    - destruct k as [| k'].
      + exfalso. lia.
      + simpl in Hc. discriminate. }
  assert (HE : dtr_H_adj (dtr_rotc k l) == dtr_H_adj (skipn k l ++ firstn k l))
    by reflexivity.
  rewrite HE.
  rewrite (dtr_H_adj_app_seam (skipn k l) (firstn k l) Hnes Hnef).
  rewrite (dtr_xq_telescope (skipn k l) HSs).
  rewrite (dtr_xq_telescope (firstn k l) HSf).
  rewrite (dtr_lastq_skipn_kept l k H2).
  rewrite (dtr_hd_firstn_kept k l H1).
  assert (Hab : Qabs (hd 0 l - dtr_lastq l) == dtr_lastq l - hd 0 l).
  { rewrite (dtr_xq_abs_sub_comm (hd 0 l) (dtr_lastq l)).
    apply dtr_xq_abs_id.
    apply (dtr_qle_0_sub_inv (hd 0 l) (dtr_lastq l)).
    apply dtr_xq_hd_le_lastq. exact HS. }
  rewrite Hab. ring.
Qed.

(* 辅助件 A6＝零转恒等（宿主 :245 零前提语句同内容重演；参数 32/35 证体使用位；  *)
(* 非参数位——宿主该件无前件不入 106 参数册） *)
Lemma dtr_rotc_0 : forall l : list Q, dtr_rotc 0 l = l.
Proof.
  intros l. unfold dtr_rotc. simpl.
  induction l as [| a rest IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* 参数 32（DTPT_Rotation.v:560） *)
Theorem dtr_H_adj_rotc_exact_0 : forall l : list Q, dtr_SortedQ l ->
  dtr_H_adj (dtr_rotc 0 l) == dtr_lastq l - hd 0 l.
Proof.
  intros l HS. rewrite dtr_rotc_0. apply dtr_xq_telescope. exact HS.
Qed.

(* 参数 33-34（DTPT_Rotation.v:567） *)
Theorem dtr_H_adj_rotc_exact_ge : forall (k : nat) (l : list Q), dtr_SortedQ l ->
  (length l <= k)%nat -> dtr_H_adj (dtr_rotc k l) == dtr_lastq l - hd 0 l.
Proof.
  intros k l HS Hk.
  rewrite (dtr_rotc_ge_len_id k l Hk). apply dtr_xq_telescope. exact HS.
Qed.

(* 参数 35-36（DTPT_Rotation.v:575）——nat 二分走证内 assert（\/ 不入顶层语句位） *)
Theorem dtr_H_adj_rotc_exact_short : forall (k : nat) (l : list Q), dtr_SortedQ l ->
  (length l <= 1)%nat -> dtr_H_adj (dtr_rotc k l) == dtr_lastq l - hd 0 l.
Proof.
  intros k l HS Hn.
  assert (Hcases : forall p q : nat, (p <= q)%nat \/ (q < p)%nat).
  { intros p. induction p as [| p' IHp]; intros q.
    - left. lia.
    - destruct q as [| q'].
      + right. lia.
      + destruct (IHp q') as [Hle | Hgt]; [left | right]; lia. }
  destruct (Hcases (length l) k) as [Hle | Hgt].
  - apply (dtr_H_adj_rotc_exact_ge k l HS Hle).
  - assert (H0 : (k = 0)%nat) by lia.
    rewrite H0. rewrite dtr_rotc_0. apply dtr_xq_telescope. exact HS.
Qed.

(* ============================================================ *)
(* 五 【只登记】区（非参数位；照任务令如实登记不硬供）                      *)
(*   本卷登记序区间（宿主 :49–:575）内非参数位语句两条（底册 §2.3 混载旗    *)
(*   Rotation 18 条之二）：                                              *)
(*   （1）H_rotc_separates（宿主 :370，exists 旗）——零顶层前件（不入 106  *)
(*        参数册）；结论面「exists l n, H_adj (rotc n l) <> H_adj l」＝Prop   *)
(*        存在见证＋不等式混载双旗面，照任务令「exists 旗位+零顶层前件型    *)
(*        参数实测后如实登记不硬供」处置，零硬供零修订。                 *)
(*   （2）rotc_Pinf_separates（宿主 :379，exists 旗）——零顶层前件；结论面  *)
(*        「exists l n s, rotc n l <> Pinf l s」同款双旗面，同处置。        *)
(*   两条之内容（ witnesses [0;1;2] 转一格非退化）属宿主已证在役面，供给    *)
(*   无参数可记；升级方向＝对 exists 旗内容件已证结论 Type 版 sigT 见证  *)
(*   形后可入后续卷。                                                    *)
(* ============================================================ *)

(* ============================================================ *)
(* 六 尾置验印区（文件最尾）：逐件承认面验印（全 Closed 判据）——           *)
(*    名清单＝24 供给定理＋16 辅助件＝40 名，与 Qed 计数 40 零差           *)
(* ============================================================ *)

Print Assumptions dtr_cyc_qeq_le.
Print Assumptions dtr_cyc_le_triple.
Print Assumptions dtr_firstn_incl.
Print Assumptions dtr_skipn_incl.
Print Assumptions dtr_firstn_SortedQ.
Print Assumptions dtr_skipn_SortedQ.
Print Assumptions dtr_H_adj_app_seam.
Print Assumptions dtr_rotc_inv.
Print Assumptions dtr_rotc_in.
Print Assumptions dtr_H_rotc_span_lb.
Print Assumptions dtr_skipn_ne_of_lt.
Print Assumptions dtr_firstn_ne_of_lt.
Print Assumptions dtr_rotc_skipn_all.
Print Assumptions dtr_rotc_firstn_all.
Print Assumptions dtr_rotc_ge_len_id.
Print Assumptions dtr_lastq_skipn_kept.
Print Assumptions dtr_hd_firstn_kept.
Print Assumptions dtr_sorted_hd_min.
Print Assumptions dtr_sorted_lastq_max.
Print Assumptions dtr_sorted_sub_le_spread.
Print Assumptions dtr_H_adj_rotc_exact_mid.
Print Assumptions dtr_H_adj_rotc_exact_0.
Print Assumptions dtr_H_adj_rotc_exact_ge.
Print Assumptions dtr_H_adj_rotc_exact_short.
Print Assumptions dtr_qadd_le.
Print Assumptions dtr_qadd_nonneg.
Print Assumptions dtr_qle_0_sub_inv.
Print Assumptions dtr_qle_0_sub_intro.
Print Assumptions dtr_xq_minus_self.
Print Assumptions dtr_xq_abs_eq0.
Print Assumptions dtr_xq_abs_id.
Print Assumptions dtr_xq_abs_sub_comm.
Print Assumptions dtr_xq_abs_zero.
Print Assumptions dtr_xq_H_adj_nonneg.
Print Assumptions dtr_xq_le_add_abs.
Print Assumptions dtr_xq_pair_dist_le.
Print Assumptions dtr_xq_lastq_In.
Print Assumptions dtr_xq_hd_le_lastq.
Print Assumptions dtr_xq_telescope.
Print Assumptions dtr_rotc_0.

(* ============================================================ *)
(* 七 提取检验区（红线四：可提取验证，Obj.magic 计数＝0 判据）            *)
(*    检验一：数据层真实现（rotc/skipn/firstn 真旋转码＋sum_adjdiff/      *)
(*    lastq 递归真码＋SortedQ Prop 承载擦除）；                          *)
(*    检验二：41 件定理逐件 Separate Extraction（Prop 结论面随提取擦除，   *)
(*     口径「构造子参提取擦除」惯例；分桶产物归  专属桶——   *)
(*    同文件双 Separate Extraction 同名覆写系  在案惯例，本件两条    *)
(*    仅为编内可提取性自证，真分桶由独立检验件定向重提取执行）。          *)
(* ============================================================ *)

Separate Extraction dtr_sum_adjdiff dtr_H_adj dtr_lastq dtr_rotc dtr_SortedQ.

Separate Extraction dtr_cyc_qeq_le dtr_cyc_le_triple dtr_firstn_incl
  dtr_skipn_incl dtr_firstn_SortedQ dtr_skipn_SortedQ
  dtr_H_adj_app_seam dtr_rotc_inv dtr_rotc_in dtr_H_rotc_span_lb
  dtr_skipn_ne_of_lt dtr_firstn_ne_of_lt dtr_rotc_skipn_all
  dtr_rotc_firstn_all dtr_rotc_ge_len_id dtr_lastq_skipn_kept
  dtr_hd_firstn_kept dtr_sorted_hd_min dtr_sorted_lastq_max
  dtr_sorted_sub_le_spread dtr_H_adj_rotc_exact_mid dtr_H_adj_rotc_exact_0
  dtr_H_adj_rotc_exact_ge dtr_H_adj_rotc_exact_short
  dtr_qadd_le dtr_qadd_nonneg dtr_qle_0_sub_inv dtr_qle_0_sub_intro
  dtr_xq_minus_self dtr_xq_abs_eq0 dtr_xq_abs_id dtr_xq_abs_sub_comm
  dtr_xq_abs_zero dtr_xq_H_adj_nonneg dtr_xq_le_add_abs
  dtr_xq_pair_dist_le dtr_xq_lastq_In dtr_xq_hd_le_lastq
  dtr_xq_telescope dtr_rotc_0.
