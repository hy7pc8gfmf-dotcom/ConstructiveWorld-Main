(* ============================================================ *)
(* UpAblBYLowerBound.v *)
(* *)
(* 使命： BY-LB-1 信息论下界定理——布尔比较模型中，任何正确识别 K+1 个       *)
(*   单调阈值位置的决策树，叶数 >= K+1，决策深度 >= Nat.log2 (S K)。          *)
(* 主件： bylb_correct_tree_leaves / bylb_lower_bound（sigT nat 见证出口）。  *)
(* 依赖： 仅 Stdlib：Lists.List（NoDup_cons_iff/NoDup_app_remove_l/r/        *)
(*   in_map/in_map_iff/filter_In/in_seq/seq）、Bool.Bool、Arith.Arith        *)
(*   （Nat.log2_le_mono/Nat.log2_pow2/Nat.pow_le_mono_r/Nat.leb_le/          *)
(*   Nat.leb_gt）、Lia。 *)
(* 对标： stdlib Lists.List 的 NoDup 引理族与 Nat 对数引理族；决策树类型     *)
(*   bylb_dtree 与运行核 bylb_run 为本库独立新置（与 DS-DT 之                *)
(*   UpAblBYDecisionTree.v 独立共存，零同名零依赖）。 *)
(* 构造性注记： 全件 Set 层承载（bylb_dtree : Type，nat 见证）；出口          *)
(*   sigT nat 见证形；零承认；三条 Fixpoint 均结构递归，可提取。              *)
(* 编译配方： Rocq 9.1 直调 coqc -Q . "" UpAblBYLowerBound.v（先 unset       *)
(*   COQLIB/ROCQLIB；批处理 bylb_g2_build.cmd）。 *)
(* ============================================================ *)
(*   选择）、bylb_count_leaves_ge（配分计数）、bylb_correct_tree_leaves、     *)
(*   bylb_lower_bound。全件零承认。 *)
(* ============================================================ *)
(* 并读注（上界侧：UpReqMixLogB.v L832 mixb_sel_scale，语句形                 *)
(*   c <= 2 * (Nat.log2 K) + 5）：本件为全 K+1 面（t ∈ {0,...,K}，            *)
(*   bylb_ft 0 即恒 true 的 0 位阈值），与 A 路选择器候选面（K+1，含          *)
(*   k=0）同面；B 路上界前件面为 K（test 0 = false 排除 k=0），是唯一         *)
(*   本体：同侧每叶至多承载一个阈值位置。 *)
(* ============================================================ *)

From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.

(* ========== 1. 最小布尔比较决策树（nat 查询位，叶带阈值判定标签） ========== *)

Inductive bylb_dtree : Type :=
| bylb_dleaf : nat -> bylb_dtree
| bylb_dnode : nat -> bylb_dtree -> bylb_dtree -> bylb_dtree.

(* 运行核：oracle f 在查询位 n 上答 true 走右、false 走左；叶即停。 *)
Fixpoint bylb_run (T : bylb_dtree) (f : nat -> bool) : bylb_dtree :=
  match T with
  | bylb_dleaf m => bylb_dleaf m
  | bylb_dnode n l r => bylb_run (if f n then r else l) f
  end.

Fixpoint bylb_depth (T : bylb_dtree) : nat :=
  match T with
  | bylb_dleaf _ => 0
  | bylb_dnode _ l r => S (Nat.max (bylb_depth l) (bylb_depth r))
  end.

Fixpoint bylb_nleaves (T : bylb_dtree) : nat :=
  match T with
  | bylb_dleaf _ => 1
  | bylb_dnode _ l r => bylb_nleaves l + bylb_nleaves r
  end.

(* ========== 2. 单调阈值函数族（nat -> bool + 阈值规范） ========== *)

(* 阈值 t 的身份函数：n < t 处 false，n >= t 处 true（t ∈ {0,...,K}）。 *)
Definition bylb_ft (t : nat) : nat -> bool := fun n => t <=? n.

(* 阈值规范：Set 层等式形（bool 等式，非 Prop 序关系出口）。 *)
Definition bylb_thr_spec (t : nat) (f : nat -> bool) : Prop :=
  (forall n, n < t -> f n = false) /\ (forall n, t <= n -> f n = true).

Lemma bylb_ft_spec : forall t : nat, bylb_thr_spec t (bylb_ft t).
Proof.
  intros t. split; intros n H; unfold bylb_ft.
  - apply Nat.leb_gt. exact H.
  - apply Nat.leb_le. exact H.
Qed.

(* 单调性前件：固定阈值 t，点随 n 增长一旦 true 永远 true（点状形）。 *)
Lemma bylb_ft_mono : forall (t n1 n2 : nat),
  n1 <= n2 -> bylb_ft t n1 = true -> bylb_ft t n2 = true.
Proof.
  intros t n1 n2 Hle H. unfold bylb_ft in *.
  apply Nat.leb_le. apply Nat.le_trans with (m := n1).
  - apply Nat.leb_le. exact H.
  - exact Hle.
Qed.

(* ========== 3. NoDup 辅件（引 stdlib NoDup_cons_iff /                     *)
(*    NoDup_app_remove_l / NoDup_app_remove_r） ========== *)

Lemma bylb_nodup_cons_notin : forall (A : Type) (a : A) (l : list A),
  NoDup (a :: l) -> ~ In a l.
Proof.
  intros A a l H. apply NoDup_cons_iff in H. apply H.
Qed.

Lemma bylb_nodup_app_inv : forall (A : Type) (a b : list A),
  NoDup (a ++ b) -> NoDup a /\ NoDup b.
Proof.
  intros A a b H. split.
  - apply (NoDup_app_remove_r a b H).
  - apply (NoDup_app_remove_l a b H).
Qed.

Lemma bylb_nodup_map_inj : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj H. induction H as [| x l Hnin Hnd IH]; cbn [map].
  - constructor.
  - constructor.
    + intros HI. apply in_map_iff in HI. destruct HI as [y [Hfy Hiny]].
      apply Hinj in Hfy. subst y. apply Hnin. exact Hiny.
    + exact IH.
Qed.

Lemma bylb_seq_nodup : forall len start : nat, NoDup (seq start len).
Proof.
  induction len as [| len IH]; intros start; cbn [seq].
  - constructor.
  - constructor.
    + intros HI. apply in_seq in HI. lia.
    + apply IH.
Qed.

(* ========== 4. 配分计数核 ========== *)

(* 节点查询位 n 上，答案 false/true 把阈值表 ts 分为左右两子表； *)
(* 两侧子表的子树运行像各自保持 NoDup。 *)
(* 注：运行像不成立「原表像 = 左子表像 ++ 右子表像」的列表等式（同表 *)
(* 一真一假两阈值时左右序与原序不同），故此处直接证 NoDup 保持， *)
(* 不经过任何列表等式。 *)
Lemma bylb_run_nodup_split :
  forall (n : nat) (l r : bylb_dtree) (ts : list nat),
    NoDup (map (fun t => bylb_run (bylb_dnode n l r) (bylb_ft t)) ts) ->
    NoDup (map (fun t => bylb_run l (bylb_ft t))
               (filter (fun t => negb (bylb_ft t n)) ts)) /\
    NoDup (map (fun t => bylb_run r (bylb_ft t))
               (filter (fun t => bylb_ft t n) ts)).
Proof.
  intros n l r. induction ts as [| t ts IH]; intros Hnd.
  - split; constructor.
  - cbn [map] in Hnd. apply NoDup_cons_iff in Hnd.
    destruct Hnd as [Hnin Hndts]. apply IH in Hndts.
    destruct Hndts as [HndL HndR].
    cbn [filter]. destruct (bylb_ft t n) eqn:E.
    + split.
      * exact HndL.
      * cbn [map negb]. constructor.
        -- intros HI. apply in_map_iff in HI.
           destruct HI as [t' [Hrun Hflt]]. apply filter_In in Hflt.
           destruct Hflt as [Hts Hq].
           assert (Hq' : bylb_ft t' n = true) by exact Hq.
           assert (Hg : bylb_run (bylb_dnode n l r) (bylb_ft t')
                        = bylb_run (bylb_dnode n l r) (bylb_ft t)).
           { cbn [bylb_run]. rewrite Hq'. rewrite E.
             cbn [bylb_run]. rewrite Hrun. reflexivity. }
           apply Hnin. rewrite <- Hg.
           exact (in_map (fun t0 => bylb_run (bylb_dnode n l r) (bylb_ft t0))
                         ts t' Hts).
        -- exact HndR.
    + split.
      * cbn [map negb]. constructor.
        -- intros HI. apply in_map_iff in HI.
           destruct HI as [t' [Hrun Hflt]]. apply filter_In in Hflt.
           destruct Hflt as [Hts Hq].
           assert (Hq' : negb (bylb_ft t' n) = true) by exact Hq.
           apply negb_true_iff in Hq'.
           assert (Hg : bylb_run (bylb_dnode n l r) (bylb_ft t')
                        = bylb_run (bylb_dnode n l r) (bylb_ft t)).
           { cbn [bylb_run]. rewrite Hq'. rewrite E.
             cbn [bylb_run]. rewrite Hrun. reflexivity. }
           apply Hnin. rewrite <- Hg.
           exact (in_map (fun t0 => bylb_run (bylb_dnode n l r) (bylb_ft t0))
                         ts t' Hts).
        -- exact HndL.
      * exact HndR.
Qed.

Lemma bylb_filter_split_length :
  forall (n : nat) (ts : list nat),
    length (filter (fun t => negb (bylb_ft t n)) ts)
    + length (filter (fun t => bylb_ft t n) ts) = length ts.
Proof.
  intros n. induction ts as [| a l IH]; cbn [length filter].
  - reflexivity.
  - destruct (bylb_ft a n); cbn [negb filter length]; lia.
Qed.

(* 主计数：运行像在 ts 上两两不同（NoDup）=> ts 长度 <= 叶数。 *)
(* 叶情形：常值叶至多覆盖 1 个阈值；节点情形：由 bylb_run_nodup_split *)
(* 把 NoDup 传入左右两子表，归纳闭合，加法性给出不等式。 *)
Theorem bylb_count_leaves_ge :
  forall (T : bylb_dtree) (ts : list nat),
    NoDup (map (fun t => bylb_run T (bylb_ft t)) ts) ->
    length ts <= bylb_nleaves T.
Proof.
  intros T. induction T as [m | n l IHl r IHr]; intros ts Hnd.
  - destruct ts as [| t ts].
    + cbn [length bylb_nleaves]. lia.
    + cbn [map bylb_run] in Hnd.
      apply bylb_nodup_cons_notin in Hnd.
      destruct ts as [| a rest]; cbn [length bylb_nleaves]; [lia |].
      exfalso. apply Hnd. cbn [map]. apply in_eq.
  - destruct (bylb_run_nodup_split n l r ts Hnd) as [HndL HndR].
    specialize (IHl (filter (fun t => negb (bylb_ft t n)) ts) HndL).
    specialize (IHr (filter (fun t => bylb_ft t n) ts) HndR).
    cbn [bylb_nleaves].
    pose proof (bylb_filter_split_length n ts) as Hsp.
    rewrite <- Hsp. apply Nat.add_le_mono; assumption.
Qed.

(* ========== 5. 叶数-深度控制与主定理 ========== *)

Lemma bylb_leaves_pow_depth :
  forall T : bylb_dtree, bylb_nleaves T <= 2 ^ bylb_depth T.
Proof.
  intros T. induction T as [m | n l IHl r IHr]; cbn [bylb_nleaves bylb_depth].
  - cbn. lia.
  - assert (Hb : 2 <> 0) by lia.
    assert (H1 : 2 ^ bylb_depth l
                 <= 2 ^ Nat.max (bylb_depth l) (bylb_depth r))
      by (apply Nat.pow_le_mono_r; lia).
    assert (H2 : 2 ^ bylb_depth r
                 <= 2 ^ Nat.max (bylb_depth l) (bylb_depth r))
      by (apply Nat.pow_le_mono_r; lia).
    assert (Hs : 2 ^ S (Nat.max (bylb_depth l) (bylb_depth r))
                 = 2 * 2 ^ Nat.max (bylb_depth l) (bylb_depth r))
      by reflexivity.
    lia.
Qed.

(* 正确性假设取「叶标签即阈值」形：跑完阈值 t 的 oracle 必停在 bylb_dleaf t。 *)
(* 由此 K+1 个阈值的运行像两两不同（构造子注入），计数核给出叶数 >= K+1， *)
(* 叶数 <= 2^深度 给出 log2(S K) <= 深度。 *)
Theorem bylb_correct_tree_leaves :
  forall (K : nat) (T : bylb_dtree),
    (forall t, t <= K -> bylb_run T (bylb_ft t) = bylb_dleaf t) ->
    S K <= bylb_nleaves T /\ Nat.log2 (S K) <= bylb_depth T.
Proof.
  intros K T Hcorr.
  assert (Hme : map (fun t => bylb_run T (bylb_ft t)) (seq 0 (S K))
              = map (fun t => bylb_dleaf t) (seq 0 (S K))).
  { apply map_ext_in. intros t Ht. apply in_seq in Ht. apply Hcorr. lia. }
  assert (Hnd : NoDup (map (fun t => bylb_dleaf t) (seq 0 (S K)))).
  { apply bylb_nodup_map_inj.
    - intros x y Hxy. injection Hxy as Hxy. exact Hxy.
    - apply bylb_seq_nodup. }
  pose proof (bylb_count_leaves_ge T (seq 0 (S K))) as Hcnt.
  rewrite Hme in Hcnt.
  apply Hcnt in Hnd.
  rewrite length_seq in Hnd.
  split.
  - exact Hnd.
  - pose proof (bylb_leaves_pow_depth T) as Hlp.
    transitivity (Nat.log2 (2 ^ bylb_depth T)).
    + apply Nat.log2_le_mono. lia.
    + rewrite (Nat.log2_pow2 (bylb_depth T) (Nat.le_0_l (bylb_depth T))).
      apply Nat.le_refl.
Qed.

(* BY-LB-1 主出口（sigT nat 见证形；witness d := Nat.log2 (S K)）。 *)
(* 注意：0 < K 前件并非必需——K = 0 时 Nat.log2 1 = 0，平凡成立， *)
(* 故按无前件的更强形式陈述（自然数全域）。 *)
Theorem bylb_lower_bound : forall K : nat,
  sigT (fun d : nat =>
    Nat.log2 (S K) <= d /\
    (forall T : bylb_dtree,
        (forall t, t <= K -> bylb_run T (bylb_ft t) = bylb_dleaf t) ->
        d <= bylb_depth T)).
Proof.
  intros K. apply (existT _ (Nat.log2 (S K))). split.
  - apply Nat.le_refl.
  - intros T Hcorr.
    destruct (bylb_correct_tree_leaves K T Hcorr) as [_ Hlog]. exact Hlog.
Qed.

(* ========== G4 审计口 ========== *)

Print Assumptions bylb_count_leaves_ge.
Print Assumptions bylb_correct_tree_leaves.
Print Assumptions bylb_lower_bound.
