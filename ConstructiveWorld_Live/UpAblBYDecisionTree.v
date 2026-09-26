(* ============================================================ UpAblBYDecisionTree.v —— 二叉决策树归纳类型基建件
   （BY-LB-1 信息论下界定理供基；全中文零承认·纯构造性零承认项） 使命：二叉决策树归纳类型基建，供 BY 系信息论下界使用。
      依赖：Stdlib Arith／PeanoNat／List／Lia（零库内件依赖）。 构造性注记：零承认语句，纯构造证明。
   ------------------------------------------------------------ 上游（零改任何既有件）：仅 stdlib（Arith/PeanoNat/List/Lia），
   零 Require 库内件；库内检索（检索索引.md + Live_X 全 .v grep dtree/dt_leaf/dt_node/dt_leaves/dt_depth）零撞名。
   下游使用件：BY-LB-1（信息论下界定理）；参照 UpReqMixLogB.v mixb_sel_scale（L832，c ≤ 2·log₂K+5 量级形）
   ——本件供其树侧对偶基座：S K 个可能输入各需一叶 ⇒ dt_leaves t ≥ S K ⇒ dt_depth t ≥ log₂(S K)。
   ------------------------------------------------------------ 本件五组（dt_ 前缀）：
   ① dtree 归纳类型（dt_leaf 标注答案值 nat / dt_node 左右子树） + 三计数 Fixpoint（dt_leaves / dt_internal / dt_depth）
      + 叶答案值序列 dt_leafvals + 执行求值器 dt_run_val
        （oracle 定向制：route : dtree -> bool 依当前子树定向，
         Set 面全可提取）。
   ② dt_leaves_eq：叶数 = 内部数 + 1（归纳证）。
   ③ dt_depth_ge_log2：深度 ≥ log₂(叶数)（归纳证；
      调用 stdlib Nat.log2_spec / Nat.log2_lt_pow2 /
      Nat.pow_le_mono_r 单调性）。
   ④ 正确性框架（计数引理三件，为 BY-LB-1 供基）：
      dt_run_val_leaf（求值器答案落在叶值序列内——正确性挂钩）
      + dt_leaves_ge_distinct（S K 个输入答案两两相异且全被
        叶值序列覆盖 ⇒ 叶数 ≥ S K）
      + dt_lb_count（合成：log₂(S K) ≤ dt_depth t，即下界主形）。
   ------------------------------------------------------------ 
   红线自审：①零承认项、零经典逻辑、全件闭构造；②主语句全
   Set 层 nat 形（le/eq on nat / bool 路由），无 Not 消去入 Set
   槽；③Fixpoint 四件皆非平凡（结构递归双支）；④Defined 面
   可提取（dtree/dt_leaves/dt_internal/dt_depth/dt_leafvals/
   dt_run_val 全计算件）。
   编译配方（9.1 直调轨，-Q . '' 平面映射；COQLIB/ROCQLIB 净）：
   coqc -Q . '' UpAblBYDecisionTree.v
   ============================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

(* ============ ① dtree 归纳类型 + 计数 Fixpoint ============ *)

Inductive dtree : Type :=
| dt_leaf : nat -> dtree              (* 叶：标注答案值 *)
| dt_node : dtree -> dtree -> dtree.  (* 内部：左/右子树 *)

(* 叶数计数 *)
Fixpoint dt_leaves (t : dtree) : nat :=
  match t with
  | dt_leaf _ => 1
  | dt_node l r => dt_leaves l + dt_leaves r
  end.

(* 内部节点计数 *)
Fixpoint dt_internal (t : dtree) : nat :=
  match t with
  | dt_leaf _ => 0
  | dt_node l r => S (dt_internal l + dt_internal r)
  end.

(* 深度计数：叶深度 0，内部 1 + max(左深, 右深) *)
Fixpoint dt_depth (t : dtree) : nat :=
  match t with
  | dt_leaf _ => 0
  | dt_node l r => S (Nat.max (dt_depth l) (dt_depth r))
  end.

(* 叶答案值序列（按中序展开；提取面 list nat） *)
Fixpoint dt_leafvals (t : dtree) : list nat :=
  match t with
  | dt_leaf a => [a]
  | dt_node l r => dt_leafvals l ++ dt_leafvals r
  end.

(* 执行求值器：oracle 依当前子树定向（真支走左/假支走右），
   返回到达叶所标注的答案值。Set 面全可提取。 *)
Fixpoint dt_run_val (route : dtree -> bool) (t : dtree) : nat :=
  match t with
  | dt_leaf a => a
  | dt_node l r => if route (dt_node l r)
                   then dt_run_val route l
                   else dt_run_val route r
  end.

(* ============ 帮件：叶数恒正 ============ *)

Lemma dt_leaves_pos : forall t, (1 <= dt_leaves t)%nat.
Proof.
  induction t as [a | l IHl r IHr]; simpl; lia.
Qed.

(* ============ ② 结构引理：叶数 = 内部数 + 1 ============ *)

Lemma dt_leaves_eq : forall t, dt_leaves t = dt_internal t + 1.
Proof.
  induction t as [a | l IHl r IHr]; simpl.
  - reflexivity.
  - simpl in IHl, IHr. lia.
Qed.

(* ============ ③ 结构引理：深度 ≥ log₂(叶数) ============ *)

Lemma dt_depth_ge_log2 : forall t,
  (1 <= dt_leaves t)%nat -> (Nat.log2 (dt_leaves t) <= dt_depth t)%nat.
Proof.
  induction t as [a | l IHl r IHr]; intros Hle.
  - cbn [dt_leaves dt_depth]. rewrite Nat.log2_1. lia.
  - assert (Hpl : (1 <= dt_leaves l)%nat) by apply dt_leaves_pos.
    assert (Hpr : (1 <= dt_leaves r)%nat) by apply dt_leaves_pos.
    specialize (IHl Hpl). specialize (IHr Hpr).
    cbn [dt_leaves dt_depth].
    set (m := Nat.max (dt_depth l) (dt_depth r)) in *.
    assert (Hml : (Nat.log2 (dt_leaves l) <= m)%nat) by (unfold m; lia).
    assert (Hmr : (Nat.log2 (dt_leaves r) <= m)%nat) by (unfold m; lia).
    (* 上界：两子树叶数各 < 2^(S m) ⇒ 和 < 2^(S (S m)) *)
    destruct (Nat.log2_spec (dt_leaves l) Hpl) as [A1 B1].
    destruct (Nat.log2_spec (dt_leaves r) Hpr) as [A2 B2].
    assert (P1 : (2 ^ (S (Nat.log2 (dt_leaves l))) <= 2 ^ (S m))%nat)
      by (apply Nat.pow_le_mono_r; lia).
    assert (P2 : (2 ^ (S (Nat.log2 (dt_leaves r))) <= 2 ^ (S m))%nat)
      by (apply Nat.pow_le_mono_r; lia).
    assert (Hlt : (dt_leaves l + dt_leaves r
                   < 2 ^ (S (S m)))%nat).
    { rewrite !Nat.pow_succ_r'.
      rewrite !Nat.pow_succ_r' in B1. rewrite !Nat.pow_succ_r' in B2.
      rewrite !Nat.pow_succ_r' in P1. rewrite !Nat.pow_succ_r' in P2.
      lia. }
    (* 和 < 2^(S (S m)) ⇒ log₂和 < S (S m) ⇒ log₂和 ≤ S m = 深度 *)
    assert (Hpos : (0 < dt_leaves l + dt_leaves r)%nat) by lia.
    assert (Hlog := proj1
      (Nat.log2_lt_pow2 (dt_leaves l + dt_leaves r) (S (S m)) Hpos) Hlt).
    lia.
Qed.

(* ============ ④ 正确性框架（BY-LB-1 计数供基） ============ *)

(* 求值器答案必落在叶值序列内（正确性挂钩件） *)
Lemma dt_run_val_leaf : forall (route : dtree -> bool) (t : dtree),
  In (dt_run_val route t) (dt_leafvals t).
Proof.
  intros route. induction t as [a | l IHl r IHr].
  - simpl. left. reflexivity.
  - simpl. destruct (route (dt_node l r)).
    + apply in_or_app. left. exact IHl.
    + apply in_or_app. right. exact IHr.
Qed.

(* 叶值序列长度 = 叶数（提取面桥） *)
Lemma dt_leafvals_len : forall t, length (dt_leafvals t) = dt_leaves t.
Proof.
  induction t as [a | l IHl r IHr]; simpl.
  - reflexivity.
  - rewrite length_app, IHl, IHr. reflexivity.
Qed.

(* 注入映射下序像无重复（seq 域上） *)
Lemma nodup_map_inj_range : forall (f : nat -> nat) (len start : nat),
  (forall i j, (i < start + len)%nat -> (j < start + len)%nat ->
               f i = f j -> i = j) ->
  NoDup (map f (seq start len)).
Proof.
  intros f len. induction len as [| len IHlen]; intros start Hinj.
  - simpl. constructor.
  - simpl. constructor.
    + intros HIn. apply in_map_iff in HIn. destruct HIn as [j [Hf Hj]].
      apply in_seq in Hj.
      assert (Hjs : j = start) by (apply Hinj; lia).
      lia.
    + apply IHlen. intros i j Hi Hj Hf. apply Hinj; lia.
Qed.

(* 计数引理（BY-LB-1 基座）：S K 个可能输入的答案值两两相异且
   全被树 t 的叶值序列覆盖 ⇒ 叶数 ≥ S K（各需一叶） *)
Lemma dt_leaves_ge_distinct : forall (t : dtree) (f : nat -> nat) (K : nat),
  (forall i, (i <= K)%nat -> In (f i) (dt_leafvals t)) ->
  (forall i j, (i <= K)%nat -> (j <= K)%nat -> f i = f j -> i = j) ->
  (S K <= dt_leaves t)%nat.
Proof.
  intros t f K Hcov Hinj.
  assert (Hnd : NoDup (map f (seq 0 (S K)))).
  { apply nodup_map_inj_range. intros i j Hi Hj Hf. apply Hinj; lia. }
  assert (Hincl : incl (map f (seq 0 (S K))) (dt_leafvals t)).
  { intros y Hy. apply in_map_iff in Hy. destruct Hy as [i [Heq Hi]].
    apply in_seq in Hi. subst y. apply Hcov. lia. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  rewrite length_map, length_seq in Hlen.
  rewrite <- dt_leafvals_len. exact Hlen.
Qed.

(* 下界主形（BY-LB-1 直接供基）：S K 个可能输入各需一叶 ⇒
   深度 ≥ log₂(S K) *)
Theorem dt_lb_count : forall (t : dtree) (f : nat -> nat) (K : nat),
  (forall i, (i <= K)%nat -> In (f i) (dt_leafvals t)) ->
  (forall i j, (i <= K)%nat -> (j <= K)%nat -> f i = f j -> i = j) ->
  (Nat.log2 (S K) <= dt_depth t)%nat.
Proof.
  intros t f K Hcov Hinj.
  assert (Hge : (S K <= dt_leaves t)%nat)
    by (apply (dt_leaves_ge_distinct t f K); assumption).
  assert (Hp : (1 <= dt_leaves t)%nat) by apply dt_leaves_pos.
  pose proof (dt_depth_ge_log2 t Hp) as H0.
  assert (Hmono : (Nat.log2 (S K) <= Nat.log2 (dt_leaves t))%nat)
    by (apply Nat.log2_le_mono; exact Hge).
  lia.
Qed.

(* ============ 审计口（G2 PA 全 Closed 预期） ============ *)

Print Assumptions dt_leaves_eq.
Print Assumptions dt_depth_ge_log2.
Print Assumptions dt_run_val_leaf.
Print Assumptions dt_leafvals_len.
Print Assumptions dt_leaves_ge_distinct.
Print Assumptions dt_lb_count.
