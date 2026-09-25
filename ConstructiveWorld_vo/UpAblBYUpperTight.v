(* ============================================================
   UpAblBYUpperTight —— 使命行：BY-LB-1 信息论地板的可达半边——按区间折半
   构造平衡二分决策树，正确识别 K+1 个单调阈值位置 t∈{0,…,K}（运行像即叶
   标签），且决策深度 <= S (Nat.log2 (S K))。与 UpAblBYLowerBound.v 的
   bylb_lower_bound 并读：正确树的决策深度落在闭区间
   [Nat.log2 (S K), S (Nat.log2 (S K))] 内，信息论地板双侧贴合。
   主件：btight_tight / bylb_tight（sigT 形，witness 为 btight_build 燃料限步
   构造的平衡树）；btight_leaves_tight 并给叶数恰 = S K。
   依赖：UpAblBYLowerBound（bylb_dtree / bylb_run / bylb_depth / bylb_nleaves /
   bylb_ft，Require 引入，零重复定义）；Stdlib：Arith.Arith（Nat.log2_spec /
   Nat.leb_le / Nat.leb_gt / Nat.div_mod_eq / Nat.mod_upper_bound）、Lia。
   对标：stdlib Nat.log2_spec 的双向夹逼（2^(log2 n) <= n < 2^(S (log2 n))）
   对应燃料-宽度关系 w <= 2^f 的选取；区间折半递归对应 Nat.log2 的折半结构。
   构造性注记：全件 Set 层承载；零承认；btight_build 为燃料位上的结构
   Fixpoint，可提取。
   编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。
   ============================================================*)

From Stdlib Require Import Arith.Arith Lia.
Require Import UpAblBYLowerBound.

(* ========== 1. 燃料限步区间折半构造 ========== *)

(* btight_build f lo w：对宽度为 w 的阈值区间 [lo, lo+w-1] 构造平衡二分树。 *)
(* f 为燃料位：f = 0 或 w <= 1 时返回叶 lo；w = S (S w') 时取中点           *)
(* m := lo + w'/2：t <= m 时 bylb_ft t m = true 走第三子树（覆盖 [lo, m]）， *)
(* t > m 时 bylb_ft t m = false 走第二子树（覆盖 [m+1, lo+w-1]）。          *)
Fixpoint btight_build (f lo w : nat) {struct f} : bylb_dtree :=
  match f with
  | 0 => bylb_dleaf lo
  | S f' =>
      match w with
      | 0 => bylb_dleaf lo
      | 1 => bylb_dleaf lo
      | S (S w') =>
          bylb_dnode (lo + w' / 2)
            (btight_build f' (S (lo + w' / 2)) (S w' - w' / 2))
            (btight_build f' lo (S (w' / 2)))
      end
  end.

(* ========== 2. 区间不变量归纳：正确性与燃料深度界 ========== *)

(* 除法事实引理（两处共用）：父宽 S (S w') <= 2 * 2^f 时，                  *)
(* 两子宽 S (w'/2) 与 S w' - w'/2 均 <= 2^f，且 w'/2 <= w'。                *)
(* 奇偶分情形后为纯线性。 *)
Lemma btight_half_fuel : forall (f w' : nat),
  S (S w') <= 2 ^ S f ->
  S (w' / 2) <= 2 ^ f /\ S w' - w' / 2 <= 2 ^ f /\ w' / 2 <= w'.
Proof.
  intros f w' Hw.
  assert (HP : 2 ^ S f = 2 * 2 ^ f) by reflexivity.
  rewrite HP in Hw.
  assert (Hd : w' = 2 * (w' / 2) + w' mod 2) by apply Nat.div_mod_eq.
  assert (Hm : w' mod 2 < 2) by (apply Nat.mod_upper_bound; lia).
  remember (w' / 2) as q eqn:Hq.
  remember (w' mod 2) as r eqn:Hr.
  split.
  - destruct r; lia.
  - split.
    + destruct r; lia.
    + lia.
Qed.

Lemma btight_build_spec : forall (f lo w : nat),
  w <= 2 ^ f ->
  (forall t, lo <= t -> t < lo + w ->
     bylb_run (btight_build f lo w) (bylb_ft t) = bylb_dleaf t)
  /\ bylb_depth (btight_build f lo w) <= f.
Proof.
  intros f. induction f as [| f IH]; intros lo w Hw.
  (* 归纳基：f = 0，则 w <= 1，树为叶 lo。 *)
  - assert (Hw1 : w <= 1) by (cbn in Hw; exact Hw).
    destruct w as [| w'].
    + split.
      * intros t Hlo Hhi. exfalso. lia.
      * cbn [btight_build bylb_depth]. lia.
    + assert (w' = 0) by lia. subst w'.
      split.
      * intros t Hlo Hhi. cbn [btight_build bylb_run].
        assert (Ht : t = lo) by lia. rewrite Ht. reflexivity.
      * cbn [btight_build bylb_depth]. lia.
  (* 归纳步：由 f 到 S f；父宽折半成两子宽（btight_half_fuel），       *)
  (* 正确性按 t <=? lo + w'/2 分流到两子区间，深度取两侧归纳上界。 *)
  - destruct w as [|[|w']].
    + split.
      * intros t Hlo Hhi. exfalso. lia.
      * cbn [btight_build bylb_depth]. lia.
    + split.
      * intros t Hlo Hhi. cbn [btight_build bylb_run].
        assert (Ht : t = lo) by lia. rewrite Ht. reflexivity.
      * cbn [btight_build bylb_depth]. lia.
    + destruct (btight_half_fuel f w' Hw) as [Hq1 [Hq2 Hq3]].
      cbn [btight_build].
      remember (w' / 2) as q eqn:Hq.
      assert (Hq4 : q <= S w') by lia.
      assert (Hsplit : S (S w') = S q + (S w' - q)) by lia.
      destruct (IH lo (S q) Hq1) as [IHcl IHdl].
      destruct (IH (S (lo + q)) (S w' - q) Hq2) as [IHcr IHdr].
      split.
      * intros t Hlo Hhi. cbn [bylb_run].
        destruct (bylb_ft t (lo + q)) eqn:E.
        -- unfold bylb_ft in E. apply Nat.leb_le in E.
           apply IHcl; lia.
        -- unfold bylb_ft in E. apply Nat.leb_gt in E.
           apply IHcr; lia.
      * cbn [bylb_depth]. lia.
Qed.

(* ========== 3. 叶数恰等（与下界侧叶数计数呼应） ========== *)

Lemma btight_nleaves_exact : forall (f lo w : nat),
  1 <= w -> w <= 2 ^ f -> bylb_nleaves (btight_build f lo w) = w.
Proof.
  intros f. induction f as [| f IH]; intros lo w H1 H2.
  - assert (Hw1 : w <= 1) by (cbn in H2; exact H2).
    destruct w as [| w'].
    + exfalso. lia.
    + assert (w' = 0) by lia. subst w'.
      cbn [btight_build bylb_nleaves]. reflexivity.
  - destruct w as [|[|w']].
    + exfalso. lia.
    + cbn [btight_build bylb_nleaves]. reflexivity.
    + destruct (btight_half_fuel f w' H2) as [Hq1 [Hq2 Hq3]].
      cbn [btight_build bylb_nleaves].
      remember (w' / 2) as q eqn:Hq.
      assert (Hp1 : 1 <= S q) by lia.
      assert (Hp2 : 1 <= S w' - q) by lia.
      rewrite (IH lo (S q) Hp1 Hq1).
      rewrite (IH (S (lo + q)) (S w' - q) Hp2 Hq2).
      lia.
Qed.

(* ========== 4. 合成出口：可达半边主定理 ========== *)

(* 三联合形式：正确识别 K+1 个阈值位置 + 叶数恰 = S K + 深度 <= S(log2(S K))。 *)
Theorem btight_leaves_tight : forall K : nat,
  sigT (fun T : bylb_dtree =>
    (forall t, t <= K -> bylb_run T (bylb_ft t) = bylb_dleaf t) /\
    (bylb_nleaves T = S K /\ bylb_depth T <= S (Nat.log2 (S K)))).
Proof.
  intros K.
  assert (Hpos : 0 < S K) by lia.
  destruct (Nat.log2_spec (S K) Hpos) as [_ Hhigh].
  assert (Hw : S K <= 2 ^ S (Nat.log2 (S K))) by lia.
  apply (existT _ (btight_build (S (Nat.log2 (S K))) 0 (S K))).
  destruct (btight_build_spec (S (Nat.log2 (S K))) 0 (S K) Hw) as [Hcorr Hdep].
  assert (Hn : bylb_nleaves (btight_build (S (Nat.log2 (S K))) 0 (S K)) = S K).
  { apply (btight_nleaves_exact (S (Nat.log2 (S K))) 0 (S K)); [lia | exact Hw]. }
  split.
  - intros t Ht. apply Hcorr; lia.
  - split.
    + exact Hn.
    + exact Hdep.
Qed.

(* 目标形（两联合）：存在树，正确识别 K+1 个单调阈值位置，                *)
(* 且深度 <= S (Nat.log2 (S K))。 *)
Theorem btight_tight : forall K : nat,
  sigT (fun T : bylb_dtree =>
    (forall t, t <= K -> bylb_run T (bylb_ft t) = bylb_dleaf t) /\
    bylb_depth T <= S (Nat.log2 (S K))).
Proof.
  intros K. destruct (btight_leaves_tight K) as [T [Hc [Hn Hd]]].
  apply (existT _ T). split.
  - exact Hc.
  - exact Hd.
Qed.

(* 按目标形命名的同体出口（基座件无此名，零冲突）。 *)
Definition bylb_tight : forall K : nat,
  sigT (fun T : bylb_dtree =>
    (forall t, t <= K -> bylb_run T (bylb_ft t) = bylb_dleaf t) /\
    bylb_depth T <= S (Nat.log2 (S K))) := btight_tight.

(* ========== 5. 四关审计口 ========== *)

Print Assumptions btight_half_fuel.
Print Assumptions btight_build_spec.
Print Assumptions btight_nleaves_exact.
Print Assumptions btight_leaves_tight.
Print Assumptions btight_tight.
Print Assumptions bylb_tight.
