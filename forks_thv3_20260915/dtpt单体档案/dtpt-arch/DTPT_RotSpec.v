(* ============================================================
   DTPT_RotSpec.v — 母文件：旋转谱锐化理论 + 相位偏差检测器理论
   （U18 席新建；M5 归并席并入 DTPT_PhCyc.v 后定形）
   ── 标准六字段头 ──
   【一·职责】
     §0-§5（U18 原面）：有界组合律 rotc_add + 周期冻结
     （rotc_periodic/rotc_periodic_full，经 rotc_full）+ rotc_class_folds
     折回基本域 + 接缝序 rs_seam_order + 旗舰锐化上界
     rotc_class_sharp_ub（H_adj (rotc k l) <= 2·spread，锐于 U8 的
     3·spread）+ 锐性取得 rotc_class_sharp_attained（[0;0;2] 界不可再降）
     + 无界组合律反例定谳 rotc_add_unbounded_false。
     §M5-1 起（PhCyc 并入面）：排序最小化排列类泛化 phcyc_min_perm
     + 判别器退化定谳（phase_side_cyc_side_degenerate/side_zero）+
     偏差检测器 phase_dev 及行为定理族（iff 桥/记录面/序面/数值升格/
     稳定面）+ k=0 面条件定理与双见证。
   【二·依赖】
     DTPT（H_adj/P0/Q 工具箱/C_sorted_min_adj）、DTPT_ROTC（rotc 系）、
     DTPT_Entropy（SortedQ/lastq 同名再声明，消费 DTPT_Cyc 语句面必须
     同源类型，按 DTPT_Cyc 内部 Import 序补列）、DTPT_Cyc（精确闭式/
     保序件/cyc_qeq_le 系）、DTPT_Entropy2（qn/freq_q 频率熵族，窄化后
     暂未消费，按单保留）；stdlib：QArith/Qabs/List/Arith/Lia/
     Permutation。无其它 Require。
   【三·归并记录】
     M5 席：DTPT_PhCyc.v（U18-2 拆分席）全文并入本文件尾（§M5-1 分隔
     注起，除头部与 Require 块外逐字保留），源文件退役（.retired_M5
     快照留存）。其 Require DTPT/DTPT_ROTC/DTPT_Entropy 三行与 stdlib
     导入行均与本文件现有 Require 重合，删除后依赖全部可达。
   【四·对账注记（phcyc_min_perm 去重取证）】
     phcyc_min_perm 与 DTPT_CGen.C_gen 同语句（U18-2 已声明本地重推，
     因 C_gen 所在件不在原席允许清单）。M5 去重取证：现役底座
     （DTPT/DTPT_ROTC/DTPT_Entropy/DTPT_Cyc/DTPT_Entropy2）中排序
     最小化仅有 DTPT.C_sorted_min_adj（Permutation l l 恒等特例：
     forall l, H_adj (P0 l) <= H_adj l），排列类全称形不可由其直推
     （须置换搬运 + 跨度下界 + Qeq 链全套骨架）；C_gen 在
     DTPT_CGen.v，位于本文件现 Require 面之外，整合令未授权新增
     Require。结论：保留本地 phcyc_min_perm 并注记，禁硬凑；后续
     若全库 Require 面收编 DTPT_CGen，可改引 C_gen 并删本地版。
   【五·认证】
     全件 Qed（U18 13 件 + 并入 15 件 = 28 件）；Print Assumptions 全
     Closed under the global context；M5 一窗编译全绿（G1-G4 四关
     证据见 DTPT_M5_归并报告.md）；底座零重证零修改。
   【六·纪律】
     零承认（头注不用禁词字面）；全程 Qed；nat 全显式 %nat（上游
     Q_scope 传导劫持：无约束位 `-`/`<=` 会被 Q_scope 吞——探针实证）；
     Q 侧全走显式引理装配，lia 只用于 nat。Q 是 Record（Qeq_bool 为
     记录层面非数值相等，并入面定理口径）。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Permutation.
Require DTPT.
Require DTPT_ROTC.
Require DTPT_Entropy.
Require DTPT_Cyc.
Require DTPT_Entropy2.
Import ListNotations.
Import DTPT.DTPT.
Import DTPT_ROTC.DTPT_ROTC.
Import DTPT_Entropy.DTPT_Entropy.
Import DTPT_Cyc.DTPT_Cyc.
Import DTPT_Entropy2.DTPT_Entropy2.

Module DTPT_RotSpec.

(* ========== §0 工具件 ========== *)

(* 二倍自界：0 <= s 时 s <= 2*s（边界支公共收口，cyc_le_triple 同配方） *)
Lemma rs_le_double : forall s : Q, (0 <= s)%Q -> (s <= 2 * s)%Q.
Proof.
  intros s Hs.
  assert (H2 : (2 * s == s + s)%Q) by ring.
  apply (Qle_trans s (s + s) (2 * s)).
  - apply (proj2 (Qle_0_sub' s (s + s))).
    assert (Hr : (s + s - s == s)%Q) by ring.
    rewrite Hr. exact Hs.
  - apply cyc_qeq_le. apply Qeq_sym. exact H2.
Qed.

(* ========== §1 保底件：有界组合律与周期冻结 ========== *)

(* 核心组合律（有界真命题）：m + n 不越过表长时旋转复合可加。
   证法 = skipn_app/firstn_app 代数 + nat 减法在 m+n<=length l
   之下归零 + skipn_skipn 合并 + firstn_app 拆分右端。 *)
Theorem rotc_add : forall (l : list Q) (m n : nat),
  (m + n <= length l)%nat -> rotc m (rotc n l) = rotc (m + n) l.
Proof.
  intros l m n H. unfold rotc.
  rewrite skipn_app. rewrite firstn_app.
  assert (HA : (length (skipn n l) = length l - n)%nat)
    by apply length_skipn.
  assert (H0 : (m - length (skipn n l))%nat = 0%nat) by (rewrite HA; lia).
  rewrite H0. cbn [skipn firstn]. rewrite app_nil_r.
  rewrite skipn_skipn.
  assert (Hfn : firstn (m + n) l = firstn n l ++ firstn m (skipn n l)).
  { pose proof (firstn_app (m + n) (firstn n l) (skipn n l)) as Hfa.
    rewrite firstn_skipn in Hfa.
    assert (Hfa1 : firstn (m + n) (firstn n l) = firstn n l).
    { rewrite firstn_firstn.
      assert (Hmin : (Nat.min (m + n) n = n)%nat) by (apply Nat.min_r; lia).
      rewrite Hmin. reflexivity. }
    assert (Hfl : (length (firstn n l) = n)%nat)
      by (apply firstn_length_le; lia).
    rewrite Hfa1 in Hfa. rewrite Hfl in Hfa.
    assert (Hm : (m + n - n)%nat = m%nat) by lia.
    rewrite Hm in Hfa. exact Hfa. }
  rewrite Hfn. symmetry. apply app_assoc.
Qed.

(* 诚实钉死：无界组合律的反例（m+n 越过表长即失效）。
   [0;1;2] 上 rotc 1 (rotc 3 l) = [1;2;0] 而 rotc 4 l = l。 *)
Theorem rotc_add_unbounded_false : exists (l : list Q) (m n : nat),
  rotc m (rotc n l) <> rotc (m + n) l.
Proof.
  exists [0; 1; 2], 1%nat, 3%nat.
  intro Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* 周期冻结·逐点形：越界转数与整圈转数重合（经 rotc_full） *)
Theorem rotc_periodic_full : forall (l : list Q) (k : nat),
  rotc (k + length l) l = rotc (length l) l.
Proof.
  intros l k.
  assert (H1 : (length l <= k + length l)%nat) by lia.
  rewrite (rotc_ge_len_id (k + length l) l H1).
  symmetry. apply rotc_full.
Qed.

(* 周期冻结·锚形：转数不小于表长时，再转整圈仍冻结原值 *)
Theorem rotc_periodic : forall (l : list Q) (k : nat),
  (length l <= k)%nat -> rotc (k + length l) l = rotc k l.
Proof.
  intros l k Hk.
  assert (H1 : (length l <= k + length l)%nat) by lia.
  rewrite (rotc_ge_len_id (k + length l) l H1).
  rewrite (rotc_ge_len_id k l Hk).
  reflexivity.
Qed.

(* 旋转类折回：任意转数都等于基本域 0..表长 内某转数的旋转 *)
Theorem rotc_class_folds : forall (l : list Q) (k : nat),
  exists j : nat, (j <= length l)%nat /\ rotc k l = rotc j l.
Proof.
  intros l k. destruct (cyc_nat_le_gt_cases (length l) k) as [Hge | Hlt].
  - (* length l <= k：越界面，折回 0（rotc_ge_len_id + rotc_0） *)
    exists 0%nat. split.
    + apply Nat.le_0_l.
    + rewrite (rotc_ge_len_id k l Hge).
      rewrite rotc_0.
      reflexivity.
  - (* k < length l：k 本身在基本域内 *)
    exists k. split.
    + lia.
    + reflexivity.
Qed.

(* ========== §2 接缝序：锐化引擎（a_k <= a_{k+1}） ========== *)

(* 尾非空剥头：lastq 在构造子尾上定向一步（simpl 卡死面的替代） *)
Lemma rs_lastq_cons_ne : forall (x : Q) (xs : list Q),
  xs <> [] -> lastq (x :: xs) = lastq xs.
Proof.
  intros x xs Hne. destruct xs as [| y ys].
  - exfalso. apply Hne. reflexivity.
  - reflexivity.
Qed.

(* 转点等元：firstn (S j) 的尾元 = skipn j 的首元（同为第 j+1 个元素）。
   对 l 归纳（被归纳者前置，IH 对 j 全称化——U8 参数序坑规避）。 *)
Lemma rs_lastq_firstn_hd_skipn : forall (l : list Q) (j : nat),
  (j < length l)%nat -> lastq (firstn (S j) l) = hd 0 (skipn j l).
Proof.
  induction l as [| a rest IH]; intros j Hj.
  - simpl in Hj. exfalso. lia.
  - destruct j as [| j'].
    + reflexivity.
    + simpl in Hj.
      assert (Hjr : (j' < length rest)%nat) by lia.
      assert (Hne : firstn (S j') rest <> []).
      { apply firstn_ne_of_lt; lia. }
      change (lastq (firstn (S (S j')) (a :: rest)))
        with (lastq (a :: firstn (S j') rest)).
      change (hd 0 (skipn (S j') (a :: rest)))
        with (hd 0 (skipn j' rest)).
      rewrite (rs_lastq_cons_ne a (firstn (S j') rest) Hne).
      apply IH. exact Hjr.
Qed.

(* 相邻段包含：skipn (S j) l 的成员都在 skipn j l 内 *)
Lemma rs_skipn_S_incl : forall (l : list Q) (j : nat) (z : Q),
  In z (skipn (S j) l) -> In z (skipn j l).
Proof.
  induction l as [| a rest IH]; intros j z Hin.
  - destruct j; simpl in Hin; destruct Hin.
  - destruct j as [| j'].
    + simpl in Hin. right. exact Hin.
    + simpl in Hin. simpl. exact (IH j' z Hin).
Qed.

(* 接缝序：1 <= k < 表长时 lastq (firstn k l) <= hd 0 (skipn k l)
   （第 k 元 <= 第 k+1 元，由 skipn (k-1) 段的排序性 + 段包含运输） *)
Lemma rs_seam_order : forall (l : list Q) (k : nat),
  SortedQ l -> (0 < k)%nat -> (k < length l)%nat ->
  (lastq (firstn k l) <= hd 0 (skipn k l))%Q.
Proof.
  intros l k HS H0 Hlt. destruct k as [| k'].
  - exfalso. lia.
  - assert (Hk' : (k' < length l)%nat) by lia.
    assert (E : lastq (firstn (S k') l) = hd 0 (skipn k' l))
      by exact (rs_lastq_firstn_hd_skipn l k' Hk').
    rewrite E.
    apply (sorted_hd_min (skipn k' l) (skipn_SortedQ l k' HS)
                         (hd 0 (skipn (S k') l))).
    apply (rs_skipn_S_incl l k' (hd 0 (skipn (S k') l))).
    apply xq_hd_In_gen. exact (skipn_ne_of_lt (S k') l Hlt).
Qed.

(* ========== §3 旗舰：2·spread 上界（锐化 U8 的 3·spread） ========== *)

Theorem rotc_class_sharp_ub : forall (l : list Q) (k : nat),
  SortedQ l -> (H_adj (rotc k l) <= 2 * (lastq l - hd 0 l))%Q.
Proof.
  intros l k HS.
  assert (Hsp : (0 <= lastq l - hd 0 l)%Q).
  { apply (proj1 (Qle_0_sub' (hd 0 l) (lastq l))).
    apply xq_hd_le_lastq. exact HS. }
  destruct (cyc_nat_le_gt_cases (length l) k) as [Hge | Hlt].
  - (* k >= 表长：恒等支，spread <= 2*spread *)
    rewrite (rotc_ge_len_id k l Hge).
    apply (Qle_trans (H_adj l) (lastq l - hd 0 l)
                     (2 * (lastq l - hd 0 l))).
    + apply cyc_qeq_le. apply xq_telescope. exact HS.
    + apply rs_le_double. exact Hsp.
  - destruct k as [| k'].
    + (* 零转支：同恒等支 *)
      rewrite rotc_0.
      apply (Qle_trans (H_adj l) (lastq l - hd 0 l)
                       (2 * (lastq l - hd 0 l))).
      * apply cyc_qeq_le. apply xq_telescope. exact HS.
      * apply rs_le_double. exact Hsp.
    + (* 中段支：U8 三项闭式 + 接缝序收敛首尾两项 *)
      assert (H1 : (1 <= S k')%nat) by lia.
      assert (HEm : H_adj (rotc (S k') l)
                    == (lastq l - hd 0 (skipn (S k') l))
                     + (lastq l - hd 0 l)
                     + (lastq (firstn (S k') l) - hd 0 l))
        by exact (H_adj_rotc_exact_mid (S k') l HS H1 Hlt).
      assert (Hseam : (lastq (firstn (S k') l)
                       <= hd 0 (skipn (S k') l))%Q)
        by exact (rs_seam_order l (S k') HS H1 Hlt).
      (* 首尾两项之和 <= spread：(a_n−a_{k+1}) + (a_k−a_1) <= a_n−a_1
         由 a_k <= a_{k+1}（接缝序）经 Qle_0_sub' + ring 收口 *)
      assert (Hsum : ((lastq l - hd 0 (skipn (S k') l))
                     + (lastq (firstn (S k') l) - hd 0 l)
                     <= (lastq l - hd 0 l))%Q).
      { apply (proj2 (Qle_0_sub' _ _)).
        assert (Hr : (lastq l - hd 0 l
                      - ((lastq l - hd 0 (skipn (S k') l))
                         + (lastq (firstn (S k') l) - hd 0 l))
                      == hd 0 (skipn (S k') l)
                         - lastq (firstn (S k') l))%Q) by ring.
        rewrite Hr.
        apply (proj1 (Qle_0_sub' (lastq (firstn (S k') l))
                                 (hd 0 (skipn (S k') l)))).
        exact Hseam. }
      apply (Qle_trans _ ((lastq l - hd 0 (skipn (S k') l))
                        + (lastq (firstn (S k') l) - hd 0 l)
                        + (lastq l - hd 0 l))
                        (2 * (lastq l - hd 0 l))).
      * apply cyc_qeq_le. apply (Qeq_trans _ _ _ HEm). ring.
      * assert (H2s : (2 * (lastq l - hd 0 l)
                       == (lastq l - hd 0 l) + (lastq l - hd 0 l))%Q)
          by ring.
        rewrite H2s.
        apply qadd_le.
        -- exact Hsum.
        -- apply Qle_refl.
Qed.

(* ========== §4 主件：锐性取得（界不可再降） ========== *)

(* 见证列 [0;0;2] 排序性（构造子逐层装配 + 字面 Qle 布尔反射） *)
Lemma sorted_wit_002 : SortedQ [0; 0; 2].
Proof.
  apply sortQ_cons.
  - apply sortQ_cons.
    + apply sortQ_cons.
      * apply sortQ_nil.
      * apply Forall_nil.
    + apply Forall_forall. intros z Hz. simpl in Hz.
      destruct Hz as [E | []]; subst z.
      * apply xq_Qle_bool_le. vm_compute. reflexivity.
  - apply Forall_forall. intros z Hz. simpl in Hz.
    destruct Hz as [E | [E | []]]; subst z.
    + apply xq_Qle_bool_le. vm_compute. reflexivity.
    + apply xq_Qle_bool_le. vm_compute. reflexivity.
Qed.

(* 锐性取得：存在排序表与转数使 H_adj (rotc k l) 恰为 2*spread。
   [0;0;2] 转 1 格 = [0;2;0]：H_adj = 2 + 2 = 4 = 2 * (2 - 0)。
   与 rotc_class_sharp_ub 合成：常数 2 是旋转谱上界的精确值。 *)
Theorem rotc_class_sharp_attained : exists (l : list Q) (k : nat),
  SortedQ l /\ H_adj (rotc k l) == 2 * (lastq l - hd 0 l).
Proof.
  exists [0; 0; 2], 1%nat.
  split.
  - apply sorted_wit_002.
  - vm_compute. reflexivity.
Qed.

(* ========== §5 公理面审计（G4） ========== *)

Print Assumptions rotc_add.
Print Assumptions rotc_add_unbounded_false.
Print Assumptions rotc_periodic_full.
Print Assumptions rotc_periodic.
Print Assumptions rotc_class_folds.
Print Assumptions rs_seam_order.
Print Assumptions rotc_class_sharp_ub.
Print Assumptions rotc_class_sharp_attained.

(* ===================================================================== *)
(* §M5-1 归并分隔注 —— 以下为原 DTPT_PhCyc.v 全文（U18-2 拆分席）           *)
(* M5 席追加至本文件尾：除头部与 Require 块（DTPT/DTPT_ROTC/DTPT_Entropy   *)
(* 及 stdlib 导入，均与本文件现有 Require 重合可达）外逐字保留，声明序与    *)
(* 证法零改动。phcyc_min_perm 去重取证与对账注记见本文件头【四】。           *)
(* ===================================================================== *)
(* ===================================================================== *)
(* §1 排序最小化的排列类泛化（底座材料本地重构）                            *)
(* ===================================================================== *)

(* C_gen 同构重推：P0 l 是 l 的排列类上 H_adj 的最小值。
   骨架：非空表望远镜展开 H_adj (P0 l) == lastq - hd，首尾两元经置换
   搬进 p，跨度下界 xq_pair_dist_le 压住，Qeq 链收口。
   逐引理出处（全部 DTPT.v 现役）：xq_P0_cons_ne / xq_telescope /
   xq_P0_sorted / xq_abs_sub_comm / xq_abs_id / Qle_0_sub' /
   xq_hd_le_lastq / D5_P0_perm / xq_hd_In_gen / xq_lastq_In /
   xq_pair_dist_le。 *)
Lemma phcyc_min_perm : forall (l p : list Q),
  Permutation l p -> H_adj (P0 l) <= H_adj p.
Proof.
  intros l p Hperm. destruct l as [| a rest].
  - assert (Hp : p = []) by (apply Permutation_nil; exact Hperm).
    rewrite Hp. apply Qle_refl.
  - assert (Hne : P0 (a :: rest) <> []) by (apply xq_P0_cons_ne).
    assert (HP : H_adj (P0 (a :: rest))
                 == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest)))
      by (apply xq_telescope; apply xq_P0_sorted).
    assert (HP2 : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest))).
    { rewrite (xq_abs_sub_comm (hd 0 (P0 (a :: rest))) (lastq (P0 (a :: rest)))).
      apply xq_abs_id.
      apply (proj1 (Qle_0_sub' _ _)).
      apply xq_hd_le_lastq. apply xq_P0_sorted. }
    assert (Hrev : Permutation (P0 (a :: rest)) (a :: rest))
      by (apply Permutation_sym; apply D5_P0_perm).
    assert (HpermP : Permutation (P0 (a :: rest)) p).
    { apply perm_trans with (l' := a :: rest).
      - exact Hrev.
      - exact Hperm. }
    assert (Hm1 : In (hd 0 (P0 (a :: rest))) p).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - exact HpermP.
      - apply xq_hd_In_gen. exact Hne. }
    assert (Hm2 : In (lastq (P0 (a :: rest))) p).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - exact HpermP.
      - apply xq_lastq_In. exact Hne. }
    assert (HPd : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  <= H_adj p)
      by (apply xq_pair_dist_le; assumption).
    rewrite HP. rewrite <- HP2. exact HPd.
Qed.

(* ===================================================================== *)
(* §2 退化实证：Qle_bool 形判别器恒返 true（「不能比大小」的定理化）         *)
(* ===================================================================== *)

(* 仿旧 phase_side 的 cyc 判别面：Qle_bool (H_adj (P0 l)) (H_adj (rotc k l))
   由 C_gen 泛化（rotc k l 是排列）恒真——该判别器无分辨力。 *)
Theorem phase_side_cyc_side_degenerate :
  forall (l : list Q) (k : nat),
    Qle_bool (H_adj (P0 l)) (H_adj (rotc k l)) = true.
Proof.
  intros l k. apply xq_Qle_bool_true.
  apply phcyc_min_perm. apply rotc_perm.
Qed.

(* 旧式 0/1 判别器形：if Qle_bool ... then 0 else 1 恒返 0（%nat）。 *)
Theorem phase_side_cyc_side_zero :
  forall (l : list Q) (k : nat),
    (if Qle_bool (H_adj (P0 l)) (H_adj (rotc k l)) then 0 else 1)%nat = 0%nat.
Proof.
  intros l k. rewrite phase_side_cyc_side_degenerate. reflexivity.
Qed.

(* ===================================================================== *)
(* §3 旗舰：偏差检测器 phase_dev 与行为定理                                 *)
(* ===================================================================== *)

(* 偏差检测器：检测真旋转相是否（记录层）偏离排序相。
   注意 Qeq_bool 是 Q Record 的原始对比较（分子分母各判等），
   非数值 Qeq 相等——这既是本节定理的口径，也是 §4 诚实障碍的根源。 *)
Definition phase_dev (l : list Q) (k : nat) : bool :=
  negb (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l))).

(* ① 存在性见证：l = [0;1;2]，k = 1 时 H_adj 侧 2#1 与 3#1 记录不等，
   偏差被判出（vm_compute 闭式钉死）。 *)
Theorem phase_dev_witness : exists (l : list Q) (k : nat), phase_dev l k = true.
Proof.
  exists [0; 1; 2]. exists 1%nat. vm_compute. reflexivity.
Qed.

(* ①' 定义 iff 桥：偏差为真 iff 记录层 Qeq_bool 判 false。 *)
Theorem phase_dev_true_iff :
  forall (l : list Q) (k : nat),
    phase_dev l k = true <-> Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l)) = false.
Proof.
  intros l k. unfold phase_dev. split.
  - intro H. destruct (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l))) eqn:E.
    + simpl in H. discriminate H.
    + reflexivity.
  - intro H. rewrite H. reflexivity.
Qed.

(* ② 严格向·记录面：偏差给出两侧的记录层不等。 *)
Theorem phase_dev_rec_ne :
  forall (l : list Q) (k : nat),
    phase_dev l k = true -> H_adj (P0 l) <> H_adj (rotc k l).
Proof.
  intros l k H Heq. unfold phase_dev in H.
  rewrite Heq in H. rewrite Qeq_bool_refl in H. simpl in H. discriminate H.
Qed.

(* ② 严格向·序面：偏差时排序相仍不超过真旋转相（C_gen 面恒真）。 *)
Theorem phase_dev_le :
  forall (l : list Q) (k : nat),
    phase_dev l k = true -> H_adj (P0 l) <= H_adj (rotc k l).
Proof.
  intros l k _. apply phcyc_min_perm. apply rotc_perm.
Qed.

(* ② 严格向·数值升格小引理：Qle_bool 反向判 false 即数值严格小于。
   这是「≤ 且数值不等则 <」的诚实形——Qle_bool/Qlt 都是 Qeq 兼容的
   数值关系，而任务拟用的记录层 Qeq_bool = false 只给记录不等，
   与数值不等不等价（1/2 与 2/4 反例），故升格必须走数值判别面。 *)
Lemma phcyc_qle_false_lt : forall x y : Q, Qle_bool y x = false -> (x < y)%Q.
Proof.
  intros [nx dx] [ny dy]. unfold Qle_bool, Qlt; simpl. intros H.
  apply Z.leb_gt in H. exact H.
Qed.

(* ② 严格向·组合件：数值判别（Qle_bool 反向 false）一次给出
   偏差为真 与 数值严格小于 H_adj (P0 l) < H_adj (rotc k l)。 *)
Theorem phase_dev_strict_of_num :
  forall (l : list Q) (k : nat),
    Qle_bool (H_adj (rotc k l)) (H_adj (P0 l)) = false ->
    phase_dev l k = true /\ (H_adj (P0 l) < H_adj (rotc k l))%Q.
Proof.
  intros l k Hfalse.
  assert (Hlt : (H_adj (P0 l) < H_adj (rotc k l))%Q)
    by (apply phcyc_qle_false_lt; exact Hfalse).
  split.
  - unfold phase_dev.
    destruct (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l))) eqn:E.
    + exfalso.
      assert (Hba : (H_adj (rotc k l) <= H_adj (P0 l))%Q).
      { apply (xq_Qeq_le (H_adj (rotc k l)) (H_adj (P0 l))).
        exact (Qeq_sym (H_adj (P0 l)) (H_adj (rotc k l))
                       (Qeq_bool_eq (H_adj (P0 l)) (H_adj (rotc k l)) E)). }
      rewrite (xq_Qle_bool_true _ _ Hba) in Hfalse. discriminate.
    + reflexivity.
  - exact Hlt.
Qed.

(* ③ 相位稳定性（iff 的 == 侧）：不偏差时两侧数值（记录更强）相等。
   Qeq_bool = true 给记录相等，进而 Qeq 数值相等。 *)
Theorem phase_dev_stable :
  forall (l : list Q) (k : nat),
    phase_dev l k = false -> H_adj (rotc k l) == H_adj (P0 l).
Proof.
  intros l k H. unfold phase_dev in H.
  destruct (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l))) eqn:E.
  - apply Qeq_sym. apply Qeq_bool_eq. exact E.
  - simpl in H. discriminate H.
Qed.

(* ===================================================================== *)
(* §4 k=0 面：相位无旋恒等 + 诚实障碍定谳                                   *)
(* ===================================================================== *)

(* k=0 旋转恒等：rotc 0 l = l，相位（H_adj）数值不变。 *)
Lemma rotc_0_H_adj : forall l : list Q, H_adj (rotc 0 l) == H_adj l.
Proof.
  intros l. rewrite rotc_0. apply Qeq_refl.
Qed.

(* k=0 计算形：偏差化为「排序相 vs 原相位」的记录比较。 *)
Theorem phase_dev_0_eq :
  forall l : list Q,
    phase_dev l 0 = negb (Qeq_bool (H_adj (P0 l)) (H_adj l)).
Proof.
  intro l. unfold phase_dev. rewrite rotc_0. reflexivity.
Qed.

(* k=0 恒不偏差的可证形（条件版）：表已排序（P0 l = l）时零偏差。 *)
Theorem phase_dev_0_of_sorted :
  forall l : list Q, P0 l = l -> phase_dev l 0 = false.
Proof.
  intros l HP. unfold phase_dev. rewrite rotc_0, HP.
  rewrite (Qeqb_true_of (H_adj l) (H_adj l) (Qeq_refl (H_adj l))).
  reflexivity.
Qed.

(* 已排序实例见证：[0;1;2] 在 k=0 无偏差（vm_compute 闭式）。 *)
Theorem phase_dev_0_sorted_example : phase_dev [0; 1; 2] 0 = false.
Proof. vm_compute. reflexivity. Qed.

(* 诚实障碍定谳（反例见证）：任务拟述的「phase_dev l 0 = false 全称」
   在 Q Record 面为假——未排序表 [0;2;1] 在 k=0 判出偏差（其排序相
   H_adj = 2#1 与原相位 H_adj = 3#1 记录不等）。故无条件版不可立，
   以条件版 phase_dev_0_of_sorted + 本见证定谳。 *)
Theorem phase_dev_0_unsorted_counterex : phase_dev [0; 2; 1] 0 = true.
Proof. vm_compute. reflexivity. Qed.

End DTPT_RotSpec.
Import DTPT_RotSpec.

(* ===================================================================== *)
(* G4 假设审计（期望全部 Closed under the global context）                  *)
(* ===================================================================== *)

Print Assumptions phcyc_min_perm.
Print Assumptions phase_side_cyc_side_degenerate.
Print Assumptions phase_side_cyc_side_zero.
Print Assumptions phase_dev_witness.
Print Assumptions phase_dev_true_iff.
Print Assumptions phase_dev_rec_ne.
Print Assumptions phase_dev_le.
Print Assumptions phcyc_qle_false_lt.
Print Assumptions phase_dev_strict_of_num.
Print Assumptions phase_dev_stable.
Print Assumptions rotc_0_H_adj.
Print Assumptions phase_dev_0_eq.
Print Assumptions phase_dev_0_of_sorted.
Print Assumptions phase_dev_0_sorted_example.
Print Assumptions phase_dev_0_unsorted_counterex.
