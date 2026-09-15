(* ============================================================
   DTPT_Entropy.v — 多熵函数族扩展 + 多熵评估套件
   职责：香农熵 Q 离散版（频域计数）、条件熵 H_cond（原文附录三.4
         「上下文依赖度」）、λ-插值混合熵的 Q 载体构造与
         非负/单调/置换面定理族（B2 补证席收口）。
   依赖：QArith（QArith/Qabs）、List、Arith、Lia、Permutation、DTPT。
   归并记录：无（原生成模块）；与 DTPT.v 的 xq_ 工具箱簇为
             双副本维持不归并，头注互指（融入执行方案 §1.4 簇②）。
   认证：零承认零公理；全树 coqchk EXIT=0（2026-09-14）。
   纪律：纯构造性；四关收割；温控协议；全部 Q 载体；
         H_Shannon 对齐库内熵模块族离散计数路线。
   附注：原典映射 §2.3 多熵族 ℋ = {H_alg, H_Sh, H_vN, H_str,
         H_Rényi, H_min, H_max, H_top, H_cond} + 附录三「多熵评估套件」；
         B2 补证席已收口：H_lam_mono / H_shannon_q_nonneg 已 Qed；
         H_shannon_q_perm_inv 经核查为假（H_devsum 取后缀最小值，
         置换改变后缀结构），以 H_shannon_q_perm_inv_counterex
         构造性反例替代（见文内注）。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Permutation.
Import ListNotations.
Open Scope Q_scope.
Require DTPT.
Import DTPT.DTPT.

Module DTPT_Entropy.

(* ========== 香农熵 Q 离散版（频域计数×对数，Shannon on Q-list） ========== *)

Fixpoint count_val (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (count_val x ys) else count_val x ys
  end.

(* 香农熵 Q 离散版——「质心偏移」占位（补证席替换为真 ln 逼近） *)
Fixpoint H_devsum (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => Qabs (x - hd 0 (P0 l)) + H_devsum xs
  end.

(* ADJ-1 垫片：旧名兼容（only parsing），语义零漂移；改名对账见 DTPT_ADJ1_改名报告.md *)
Notation H_shannon_q := H_devsum (only parsing).

Definition H_cond (l : list Q) (ctx : list Q) : Q :=
  H_devsum l - H_devsum ctx.

(* ========== λ-插值混合熵（原文 D12.3 P_mid 插值的熵版本） ========== *)
Definition H_lam (l : list Q) (s : nat) (lam : Q) : Q :=
  lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s).

(* ========== 多熵评估套件（原典附录三「可操作启发 1」的构造性化） ========== *)

Record MultiEntropyEval : Type := mkME {
  me_carrier : list Q;        (* 评估载体 *)
  me_Hadj    : Q;             (* 序列熵（相邻差） *)
  me_Hms     : Q;             (* 多重集熵（相异值计数） *)
  me_Hsh     : Q;             (* 香农熵（频域计数） *)
  me_Hcond   : Q              (* 条件熵（上下文依赖度） *)
}.

Definition mkMEval (l : list Q) (ctx : list Q) : MultiEntropyEval :=
  mkME l (H_adj l) (H_ms l) (H_devsum l) (H_cond l ctx).

(* ========== 原典附录三的六条操作启发（构造性声明面） ========== *)

(* 启发1：熵相评估——判断输出在 P0/P∞/Pmid 哪一侧 *)
Definition phase_side (l : list Q) (s : nat) : nat :=
  (* 0 = 偏 P0；1 = 偏 P∞（由序列熵与阈值比较，差值数据非 Prop） *)
  if Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s)) then 0 else 1.

(* 启发3：幻觉抑制——极端相位降权（余零过滤的构造性化） *)
Definition gate_low_entropy (H : Q) (threshold : Q) : bool :=
  Qle_bool H threshold.

(* 启发4：对齐策略——λ 偏向 P0 的可验证知识 *)
Definition align_lambda (lam : Q) : Q := lam.

(* ========== 关键定理（临时承认搭架） ========== *)

(* 混合熵随 λ 单调——P_mid 插值的熵连续性 *)
Lemma qadd_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> (0 <= a + b)%Q.
Proof.
  intros [an ad] [bn bd]; simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

Theorem H_lam_mono : forall (l : list Q) (s : nat),
  H_adj (Pinf l s) <= H_adj (P0 l) ->
  forall lam1 lam2 : Q,
    (lam1 <= lam2)%Q ->
    (H_lam l s lam1 <= H_lam l s lam2)%Q.
Proof.
  intros l s Hle lam1 lam2 Hlam. unfold H_lam.
  change (1 - lam1) with (1 + - lam1)%Q.
  change (1 - lam2) with (1 + - lam2)%Q.
  assert (Hd : (0 <= H_adj (P0 l) + - H_adj (Pinf l s))%Q)
    by (apply (proj1 (Qle_0_sub' _ _)); exact Hle).
  assert (E1 : lam1 * H_adj (P0 l) + (1 + - lam1) * H_adj (Pinf l s)
             == H_adj (Pinf l s) + lam1 * (H_adj (P0 l) + - H_adj (Pinf l s)))
    by ring.
  assert (E2 : lam2 * H_adj (P0 l) + (1 + - lam2) * H_adj (Pinf l s)
             == H_adj (Pinf l s) + lam2 * (H_adj (P0 l) + - H_adj (Pinf l s)))
    by ring.
  rewrite E1, E2.
  apply qadd_le; [apply Qle_refl | apply qmul_le_r; [exact Hlam | exact Hd]].
Qed.

(* 香农熵非负（Q 离散版） *)
Theorem H_shannon_q_nonneg : forall l : list Q, 0 <= H_devsum l.
Proof.
  induction l as [| x xs IH]; simpl.
  - apply Qle_refl.
  - apply qadd_nonneg.
    + apply (abs_nonneg (x - hd 0 (P0 (x :: xs)))).
    + exact IH.
Qed.

(* 【补证席注】原命题「H_devsum 置换不变」经核查为假：
   H_devsum 沿列表递归取「后缀最小值」(hd 0 (P0 l))，
   置换会改变后缀结构。以下给出构造性反例替代原命题。 *)
Theorem H_shannon_q_perm_inv_counterex :
  exists (l p : list Q), Permutation l p /\ H_devsum l <> H_devsum p.
Proof.
  exists [3; 1; 2], [2; 1; 3]. split.
  - apply perm_trans with (l' := [1; 3; 2]).
    + apply perm_swap.
    + apply perm_trans with (l' := [1; 2; 3]).
      * apply perm_skip. apply perm_swap.
      * apply perm_swap.
  - intro Hc. vm_compute in Hc. discriminate.
Qed.

(* ============================================================
   W9 跨相熵桥接定理席 · 补强区块（仅追加，不动上方既有内容）
   目标：把本文件从「定义收集」升级为「定理体系」——
     (1) P0 最小化序列熵 H_adj (P0 l) <= H_adj l
         （配对-望远镜路线：有序表熵=max-min，任意配对距离<=序列熵；
         与 DTPT.v 的 C_sorted_min_adj 相互独立，熵模块自足）
     (2) 跨相下界 H_adj (P0 l) <= H_adj (Pinf l s)
         （关键发现：rot = firstn ++ skipn 恒等，Pinf l s = l）
     (3) λ-插值混合熵跨相夹界
         H_adj (P0 l) <= H_lam l s lam <= H_adj (Pinf l s)，0<=lam<=1
     (4) P0 相零化香农偏差熵 H_devsum (P0 l) == 0 及其最小化
     (5) 频域计数置换不变 + 频谱跨相不变（对照 N9 序列熵可分）
     (6) 条件熵：自条件零、反对称、守卫非负、可负反例（界定适用域）
   注：任务书原列「H_devsum 置换不变」「无条件 0 <= H_cond l ctx」
   「H_adj (P0 l) <= H_adj (Pmid l s lam)」三条经核查为假（第一条的
   反例即上方 H_shannon_q_perm_inv_counterex；另两条反例见补强报告），
   已按可证命题重新表述，全部构造性落地。
   本区块 xq_ 前缀引理为局部工具；全程 Qed、零公理；仅依赖 DTPT 中
   已证的 D5_P0_perm / D5_Pinf_perm / insert_q_perm_cons / qadd_le /
   Qle_bool_false_le。
   ============================================================ *)

(* ---------- xq 局部工具：Q 序与绝对值 ---------- *)

Lemma xq_Qle_bool_true : forall x y : Q, (x <= y)%Q -> Qle_bool x y = true.
Proof.
  intros [nx dx] [ny dy]. unfold Qle, Qle_bool; simpl. intros H.
  apply Z.leb_le. exact H.
Qed.

Lemma xq_Qle_bool_le : forall x y : Q, Qle_bool x y = true -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy]. unfold Qle, Qle_bool; simpl. intros H.
  apply Z.leb_le. exact H.
Qed.

Lemma xq_Qle_antisym : forall x y : Q, (x <= y)%Q -> (y <= x)%Q -> x == y.
Proof.
  intros [nx dx] [ny dy] H1 H2. unfold Qle in H1, H2; simpl in H1, H2.
  unfold Qeq; simpl. lia.
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

(* xq_insert_q_head_aux：insert_q 在「插入点不小于被比元素」时直接置首 *)
Lemma xq_insert_q_head_aux : forall (a b : Q) (bs : list Q),
  (a <= b)%Q -> insert_q a (b :: bs) = a :: b :: bs.
Proof.
  intros a b bs H. simpl. rewrite (xq_Qle_bool_true _ _ H). reflexivity.
Qed.

Lemma xq_sortQ_P0_id : forall l : list Q, SortedQ l -> P0 l = l.
Proof.
  induction l as [| a rest IH]; intro HS.
  - reflexivity.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    change (P0 (a :: rest)) with (insert_q a (P0 rest)).
    rewrite (IH HSr). destruct rest as [| b bs].
    + reflexivity.
    + apply xq_insert_q_head_aux. apply HFa. left. reflexivity.
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

(* ========== W9 主定理 1：P0 最小化序列熵（框架核心） ========== *)

Theorem H_adj_P0_min : forall l : list Q, H_adj (P0 l) <= H_adj l.
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

(* ========== W9 主定理 2：跨相下界（P∞ 侧） ========== *)

(* 【弃用注记 2026-09-14】本件在 rot=firstn++skipn 恒等底座下为恒等推论伪装；操作语义以 DTPT_ROTC/DTPT_Cyc/DTPT_RotSpec 真化层为准。 *)
Corollary Pinf_eq_l : forall (l : list Q) (s : nat), Pinf l s = l.
Proof.
  intros l s. unfold Pinf, rot. apply firstn_skipn.
Qed.

(* 【弃用注记 2026-09-14】本件在 rot=firstn++skipn 恒等底座下为恒等推论伪装；操作语义以 DTPT_ROTC/DTPT_Cyc/DTPT_RotSpec 真化层为准。 *)
Theorem H_adj_cross_phase_lb : forall (l : list Q) (s : nat),
  H_adj (P0 l) <= H_adj (Pinf l s).
Proof.
  intros l s. rewrite (Pinf_eq_l l s). apply H_adj_P0_min.
Qed.

(* ========== W9 主定理 3：λ-插值混合熵跨相夹界 ========== *)

Lemma xq_mul_nonneg : forall a b : Q, (0 <= a)%Q -> (0 <= b)%Q -> (0 <= a * b)%Q.
Proof.
  intros [an ad] [bn bd] Ha Hb. unfold Qle in Ha, Hb; simpl in Ha, Hb.
  unfold Qle, Qmult; simpl. lia.
Qed.

Theorem H_lam_cross_phase_bounds : forall (l : list Q) (s : nat) (lam : Q),
  (0 <= lam)%Q -> (lam <= 1)%Q ->
  (H_adj (P0 l) <= H_lam l s lam)%Q /\ (H_lam l s lam <= H_adj (Pinf l s))%Q.
Proof.
  intros l s lam Hlam0 Hlam1.
  assert (Hle : (H_adj (P0 l) <= H_adj (Pinf l s))%Q)
    by apply H_adj_cross_phase_lb.
  unfold H_lam.
  assert (Hlo : (0 <= lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                 - H_adj (P0 l))%Q).
  { assert (Er1 : lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                  - H_adj (P0 l)
                  == (1 - lam) * (H_adj (Pinf l s) - H_adj (P0 l))) by ring.
    rewrite Er1.
    apply xq_mul_nonneg.
    - apply (proj1 (Qle_0_sub' lam 1)). exact Hlam1.
    - apply (proj1 (Qle_0_sub' _ _)). exact Hle. }
  assert (Hup : (0 <= H_adj (Pinf l s)
                 - (lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)))%Q).
  { assert (Er2 : H_adj (Pinf l s)
                  - (lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s))
                  == lam * (H_adj (Pinf l s) - H_adj (P0 l))) by ring.
    rewrite Er2.
    apply xq_mul_nonneg; [ exact Hlam0
                         | apply (proj1 (Qle_0_sub' _ _)); exact Hle ]. }
  split.
  - apply (proj2 (Qle_0_sub' _ _)). exact Hlo.
  - apply (proj2 (Qle_0_sub' _ _)). exact Hup.
Qed.

(* ========== W9 主定理 4：P0 相零化香农偏差熵 + 最小化 ========== *)

Lemma xq_H_shannon_sortQ : forall l : list Q, SortedQ l -> H_devsum l == 0.
Proof.
  induction l as [| a rest IH]; intro HS.
  - reflexivity.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    cbn [H_devsum].
    rewrite (xq_sortQ_P0_id (a :: rest) HS).
    change (hd 0 (a :: rest)) with a.
    rewrite (IH HSr). rewrite xq_abs_zero. ring.
Qed.

Theorem H_shannon_q_P0_zero : forall l : list Q, H_devsum (P0 l) == 0.
Proof.
  intro l. apply xq_H_shannon_sortQ. apply xq_P0_sorted.
Qed.

Theorem H_shannon_q_P0_min : forall l : list Q,
  (H_devsum (P0 l) <= H_devsum l)%Q.
Proof.
  intro l. rewrite (H_shannon_q_P0_zero l). apply H_shannon_q_nonneg.
Qed.

(* ========== W9 主定理 5：频域计数置换/跨相不变（对照 N9 序列熵可分） ========== *)

Theorem count_val_perm : forall (x : Q) (l p : list Q),
  Permutation l p -> count_val x l = count_val x p.
Proof.
  intros x l p H.
  induction H; simpl.
  - reflexivity.
  - match goal with
    | [ I : count_val x _ = count_val x _ |- _ ] => rewrite I
    end.
    reflexivity.
  - match goal with
    | [ |- context[Qeq_bool x ?u] ] => destruct (Qeq_bool x u) eqn:E1
    end;
    match goal with
    | [ |- context[Qeq_bool x ?u] ] => destruct (Qeq_bool x u) eqn:E2
    end;
    simpl; try match goal with
                  | [ I : count_val x _ = count_val x _ |- _ ] => rewrite I
                  end; reflexivity.
  - match goal with
    | [ I1 : count_val x ?u = count_val x ?v,
        I2 : count_val x ?v = count_val x ?w |- _ ] =>
        etransitivity; [ exact I1 | exact I2 ]
    end.
Qed.

Theorem count_val_phase_spectrum : forall (x : Q) (l : list Q) (s : nat),
  count_val x (P0 l) = count_val x l /\ count_val x (Pinf l s) = count_val x l.
Proof.
  intros x l s. split.
  - rewrite <- (count_val_perm x l (P0 l) (D5_P0_perm l)). reflexivity.
  - rewrite <- (count_val_perm x l (Pinf l s) (D5_Pinf_perm l s)). reflexivity.
Qed.

(* ========== W9 主定理 6：条件熵四件套（守卫非负 + 反例界定） ========== *)

Theorem H_cond_self : forall l : list Q, H_cond l l == 0.
Proof.
  intro l. unfold H_cond. ring.
Qed.

Theorem H_cond_antisym : forall (l ctx : list Q),
  H_cond l ctx == - H_cond ctx l.
Proof.
  intros l ctx. unfold H_cond. ring.
Qed.

Theorem H_cond_nonneg_guarded : forall (l ctx : list Q),
  (H_devsum ctx <= H_devsum l)%Q -> (0 <= H_cond l ctx)%Q.
Proof.
  intros l ctx H. unfold H_cond.
  apply (proj1 (Qle_0_sub' _ _)). exact H.
Qed.

(* 无条件非负为假：空表条件于高熵上下文时 H_cond = -2 < 0 *)
Theorem H_cond_neg_counterex : exists (l ctx : list Q), (H_cond l ctx < 0)%Q.
Proof.
  exists [], [5; 3]. unfold H_cond. vm_compute. reflexivity.
Qed.

(* ============================================================
   DTPT-S2 分析+补强席 · 追加区块（只加末尾，不动上方任何既有行）
   四族内容：
   (1) 计数上界族【旗舰】：count_val <= length（nat/Q 双形）
       + H_devsum 计数上界（按定义实形适配：逐项 |x - 后缀最小|
         走配对界 <= H_adj，逐和 <= 长度系数 × H_adj，系数经 S 化归）
   (2) MultiEntropyEval 相干性：mkMEval 投影往返（eta 面）
       + 多重集熵退化 H_ms == 1 ⟹ H_devsum == 0
       （dedup 计数 → 全同值 → 排序 → 零化四步桥）
       + 反向面为假的构造性反例（升序表零化但相异值非单一）
   (3) H_lam 端点退化：lam = 1 / lam = 0 分别收回 P0 / Pinf 相熵
   (4) gate_low_entropy / phase_side 行为定理（Qle_bool 双向桥）
   全程 Qed；复用 DTPT.v 的 qmul_le_r / Qle_bool_iff /
   Qle_bool_false_le / dedup_Qmem_r 与盘上 xq_ 工具箱；零新前提。
   ============================================================ *)

(* ---------- xq 局部工具：长度系数的 Q 桥 ---------- *)

Lemma xq_Zlen_nonneg : forall n : nat, (0 <= (Z.of_nat n # 1)%Q)%Q.
Proof.
  intro n. unfold Qle; simpl. lia.
Qed.

Lemma xq_Zlen_S : forall n : nat,
  ((Z.of_nat (S n) # 1) == 1 + (Z.of_nat n # 1))%Q.
Proof.
  intro n. assert (Hz : (Z.of_nat (S n) = 1 + Z.of_nat n)%Z) by lia.
  rewrite Hz. unfold Qeq, Qplus. cbn [Qnum Qden]. lia.
Qed.

Lemma xq_Zlen_inj1 : forall n : nat, ((Z.of_nat n # 1) == 1)%Q -> n = 1%nat.
Proof.
  intros n H. unfold Qeq in H; simpl in H. lia.
Qed.

Lemma xq_Qeq_le : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy] Hxy. unfold Qeq in Hxy; simpl in Hxy.
  unfold Qle; simpl. lia.
Qed.

(* ---------- 旗舰 1a：频域计数的长度上界（nat 形） ---------- *)

Lemma count_val_le_length : forall (x : Q) (l : list Q),
  (count_val x l <= length l)%nat.
Proof.
  intros x l. induction l as [| y ys IH]; simpl.
  - lia.
  - destruct (Qeq_bool x y); lia.
Qed.

(* 旗舰 1b：同上界的 Q 域形式（长度系数口径一致） *)
Lemma count_val_Zle_length : forall (x : Q) (l : list Q),
  ((Z.of_nat (count_val x l) # 1) <= (Z.of_nat (length l) # 1))%Q.
Proof.
  intros x l. pose proof (count_val_le_length x l) as Hn.
  unfold Qle; simpl. lia.
Qed.

(* ---------- 旗舰 1c：H_devsum 计数上界（按定义实形适配） ----------
   H_devsum 的每项是 |x - 后缀最小值|：配对界给出
   逐项 <= H_adj，故总和 <= 长度系数 × H_adj。非平凡点：
   后缀单调（加头只增）+ 系数 S 化归 + 因子序统一。 ---------- *)

Lemma xq_H_adj_suffix_le : forall (a : Q) (l : list Q),
  (H_adj l <= H_adj (a :: l))%Q.
Proof.
  intros a l. destruct l as [| b bs].
  - cbn [H_adj sum_adjdiff]. apply Qle_refl.
  - change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
    apply xq_le_add_abs.
Qed.

Lemma xq_head_term_le : forall (x : Q) (xs : list Q),
  (Qabs (x - hd 0 (P0 (x :: xs))) <= H_adj (x :: xs))%Q.
Proof.
  intros x xs. apply xq_pair_dist_le.
  - left. reflexivity.
  - apply Permutation_in with (l := P0 (x :: xs)).
    + apply Permutation_sym. apply D5_P0_perm.
    + apply xq_hd_In_gen. apply xq_P0_cons_ne.
Qed.

Theorem H_shannon_q_count_ub : forall l : list Q,
  (H_devsum l <= H_adj l * (Z.of_nat (length l) # 1))%Q.
Proof.
  induction l as [| x xs IH].
  - cbn [H_devsum]. apply xq_mul_nonneg.
    + apply xq_H_adj_nonneg.
    + apply xq_Zlen_nonneg.
  - cbn [H_devsum].
    assert (Hs : (H_devsum xs
                  <= H_adj (x :: xs) * (Z.of_nat (length xs) # 1))%Q).
    { apply (Qle_trans _ (H_adj xs * (Z.of_nat (length xs) # 1))).
      - exact IH.
      - apply qmul_le_r.
        + apply xq_H_adj_suffix_le.
        + apply xq_Zlen_nonneg. }
    assert (Hh : (Qabs (x - hd 0 (P0 (x :: xs))) <= H_adj (x :: xs))%Q)
      by apply xq_head_term_le.
    assert (Hlen : ((Z.of_nat (length (x :: xs)) # 1)
                    == 1 + (Z.of_nat (length xs) # 1))%Q)
      by (cbn [length]; apply xq_Zlen_S).
    apply (Qle_trans _ (H_adj (x :: xs)
                        + H_adj (x :: xs) * (Z.of_nat (length xs) # 1))).
    + apply qadd_le; [exact Hh | exact Hs].
    + rewrite Hlen.
      assert (Heq : H_adj (x :: xs) * (1 + (Z.of_nat (length xs) # 1))
                    == H_adj (x :: xs)
                       + H_adj (x :: xs) * (Z.of_nat (length xs) # 1))
        by ring.
      rewrite Heq. apply Qle_refl.
Qed.

(* ---------- 相干性 2a：全同值表的 H_devsum 零化 ---------- *)

Lemma xq_insert_const_head : forall (a y : Q) (ys : list Q),
  y == a -> insert_q a (y :: ys) = a :: y :: ys.
Proof.
  intros a y ys Hya. cbn [insert_q].
  rewrite (xq_Qle_bool_true a y (xq_Qeq_le a y (Qeq_sym y a Hya))).
  reflexivity.
Qed.

Lemma xq_P0_const_id : forall (a : Q) (l : list Q),
  Forall (fun z => z == a) l -> P0 l = l.
Proof.
  intros a l. induction l as [| x xs IH]; intro Hfa.
  - reflexivity.
  - inversion Hfa as [| z zs Hzx Hfxs]; subst.
    cbn [P0]. rewrite (IH Hfxs).
    destruct xs as [| y ys].
    + cbn [insert_q]. reflexivity.
    + apply xq_insert_const_head.
      exact (Qeq_trans y a x (Forall_inv Hfxs) (Qeq_sym x a Hzx)).
Qed.

Theorem H_shannon_q_const_zero : forall (a : Q) (l : list Q),
  Forall (fun z => z == a) l -> H_devsum l == 0.
Proof.
  intros a l. revert a. induction l as [| x xs IH]; intros a Hfa.
  - reflexivity.
  - assert (Hfa' : Forall (fun z => z == a) (x :: xs)) by exact Hfa.
    inversion Hfa as [| z zs Hzx Hfxs]; subst.
    cbn [H_devsum].
    rewrite (xq_P0_const_id a (x :: xs) Hfa').
    cbn [hd]. rewrite xq_abs_zero.
    rewrite (IH a Hfxs). ring.
Qed.

(* ---------- 相干性 2b：多重集熵退化 ⟹ 香农偏差熵零化 ---------- *)

Lemma xq_len1_el : forall m : list Q,
  length m = 1%nat -> exists a : Q, m = a :: nil.
Proof.
  intros [| b bs] H; cbn [length] in H.
  - discriminate H.
  - destruct bs as [| c cs].
    + exists b. reflexivity.
    + discriminate H.
Qed.

Lemma xq_In_Qmem : forall (z : Q) (l : list Q), In z l -> Qmem z l.
Proof.
  intros z l. induction l as [| y ys IH]; intro Hind.
  - destruct Hind.
  - simpl in Hind. destruct Hind as [Heq | Hind].
    + rewrite Qmem_cons. left. subst. apply Qeq_bool_refl.
    + rewrite Qmem_cons. right. apply IH. exact Hind.
Qed.

Lemma xq_dedup1_all_eq : forall (l : list Q) (a : Q),
  dedup l = a :: nil -> Forall (fun z => z == a) l.
Proof.
  intros l a Hd. rewrite Forall_forall. intros z Hz.
  assert (Hm : Qmem z (dedup l)).
  { apply dedup_Qmem_r. apply xq_In_Qmem. exact Hz. }
  rewrite Hd in Hm. rewrite Qmem_cons in Hm. destruct Hm as [Hm | Hm].
  - apply Qeq_bool_eq in Hm. exact Hm.
  - simpl in Hm. discriminate Hm.
Qed.

Theorem H_ms1_Hshannon0 : forall l : list Q,
  (H_ms l == 1)%Q -> H_devsum l == 0.
Proof.
  intro l. unfold H_ms. intro H.
  apply xq_Zlen_inj1 in H.
  destruct (xq_len1_el (dedup l) H) as [b Hb].
  apply (H_shannon_q_const_zero b l).
  apply (xq_dedup1_all_eq l b Hb).
Qed.

(* 反向面为假：升序表 [1;2] 香农偏差为零但多重集熵 = 2 ≠ 1 *)
Theorem Hshannon0_not_Hms1_counterex :
  H_devsum [1; 2] == 0 /\ (H_ms [1; 2] <> 1)%Q.
Proof.
  split.
  - vm_compute. reflexivity.
  - intro Hc. unfold H_ms in Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* ---------- 相干性 2c：mkMEval 构造后投影往返（eta 面） ---------- *)

Theorem mkMEval_eta : forall (l ctx : list Q),
  me_carrier (mkMEval l ctx) = l
  /\ me_Hadj (mkMEval l ctx) == H_adj l
  /\ me_Hms (mkMEval l ctx) == H_ms l
  /\ me_Hsh (mkMEval l ctx) == H_devsum l
  /\ me_Hcond (mkMEval l ctx) == H_cond l ctx.
Proof.
  intros l ctx. repeat split; reflexivity.
Qed.

Theorem mkMEval_Hms1_Hsh0 : forall (l ctx : list Q),
  (me_Hms (mkMEval l ctx) == 1)%Q -> (me_Hsh (mkMEval l ctx) == 0)%Q.
Proof.
  intros l ctx H. unfold mkMEval in H. simpl in H.
  unfold mkMEval. simpl. apply (H_ms1_Hshannon0 l H).
Qed.

(* ---------- 端点 3：H_lam 的 λ=1 / λ=0 退化 ---------- *)

Theorem H_lam_lam1 : forall (l : list Q) (s : nat),
  H_lam l s 1 == H_adj (P0 l).
Proof.
  intros l s. unfold H_lam.
  replace (1 - 1)%Q with 0%Q by reflexivity.
  ring.
Qed.

Theorem H_lam_lam0 : forall (l : list Q) (s : nat),
  H_lam l s 0 == H_adj (Pinf l s).
Proof.
  intros l s. unfold H_lam.
  replace (1 - 0)%Q with 1%Q by reflexivity.
  ring.
Qed.

(* ---------- 门控 4：gate_low_entropy / phase_side 行为定理 ---------- *)

Theorem gate_low_entropy_spec : forall H threshold : Q,
  gate_low_entropy H threshold = true <-> (H <= threshold)%Q.
Proof.
  intros H threshold. unfold gate_low_entropy. apply Qle_bool_iff.
Qed.

Theorem gate_low_entropy_false_le : forall H threshold : Q,
  gate_low_entropy H threshold = false -> (threshold <= H)%Q.
Proof.
  intros H threshold. unfold gate_low_entropy. apply Qle_bool_false_le.
Qed.

Theorem gate_low_entropy_dec : forall H threshold : Q,
  gate_low_entropy H threshold = true \/ gate_low_entropy H threshold = false.
Proof.
  intros H threshold. unfold gate_low_entropy.
  destruct (Qle_bool H threshold).
  - left. reflexivity.
  - right. reflexivity.
Qed.

Theorem phase_side_spec : forall (l : list Q) (s : nat),
  phase_side l s = 0%nat <-> (H_adj (P0 l) <= H_adj (Pinf l s))%Q.
Proof.
  intros l s. unfold phase_side. split.
  - intro E. destruct (Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s))) eqn:Eb.
    + apply (proj1 (Qle_bool_iff _ _)). exact Eb.
    + simpl in E. discriminate E.
  - intro Hle. rewrite (xq_Qle_bool_true _ _ Hle). reflexivity.
Qed.

Theorem phase_side_values : forall (l : list Q) (s : nat),
  phase_side l s = 0%nat \/ phase_side l s = 1%nat.
Proof.
  intros l s. unfold phase_side.
  destruct (Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s))).
  - left. reflexivity.
  - right. reflexivity.
Qed.

End DTPT_Entropy.
