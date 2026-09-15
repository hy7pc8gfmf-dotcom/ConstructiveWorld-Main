(* ============================================================
   DTPT_Lam.v — H_lam 反向单调、λ-argmin 构造性、align_lambda 救活
                与真旋转底座 λ-相位插值族（M3 归并版）
   ------------------------------------------------------------
   【职责】
   · H_lam 仿射面（原 X2-3 热点升级主体）：H_lam l s lam =
     lam·H_adj(P0 l) + (1-lam)·H_adj(Pinf l s) 是对 lam 的仿射函数
     ——差分恒等式 lam_affine_diff_sub / H_lam_diff_sub、零前提
     反向单调 H_lam_anti_mono、中点凸性、显式端点选择器 lam_opt 族
     （argmin 构造性）、align_lambda 首批消费定理、端点外插
     构造性警戒（见证列 [1;5;2]）。
   · 真旋转底座 λ-相位插值族（M3 并入段）：H_lam_cyc l k lam =
     lam·H_adj(P0 l) + (1-lam)·H_adj(rotc k l)——第二端点由 Pinf 的
     firstn++skipn 恒等重构真化为 rotc（skipn++firstn）真循环相；
     端点双件、k=0 旧面重合诚实锚、差分恒等式与双方向单调、
     与旧件分离双见证（[0;1;2] 转 1 格）、λ-argmin_cyc 族。
   【依赖】stdlib（QArith / Qabs / List）+ 底座 DTPT + DTPT_Entropy
     （H_adj / P0 / Pinf / H_lam / xq 系）+ DTPT_ROTC（rotc / rotc_0
     ——M3 并入新增依赖，拓扑变化如实声明）。
   【归并记录】M3（2026-09-14）：U19 席「λ-相位真循环插值」件整体
     并入本文件尾（其对本文件的 Require 行随之删除，变同文件直引，
     对 DTPT / DTPT_ROTC / DTPT_Entropy 的 Require 保留）；撞名预检
     H_lam_cyc 系 / lam_opt_cyc 全 0 撞（lamcyc_ 系命名天然区分，
     未加前缀）；全工作区无下游 Require 该退役件，源已删、
     .retired_M3 快照留存。
   【认证】旗舰件文尾审计 8 件 Print Assumptions 全 "Closed under
     the global context"（零公理）；.vo 于 M3 归并后重编全绿。
   【纪律】零承认零公理零中途放弃，全程 Qed 收口；nat 全显式
     %nat；lam 区间前提一律显式 (0 <= lam <= 1)%Q 写进陈述。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Q_scope.
Require DTPT.
Require DTPT_ROTC.
Require DTPT_Entropy.
Import DTPT.DTPT.
Import DTPT_ROTC.DTPT_ROTC.
Import DTPT_Entropy.DTPT_Entropy.

Module DTPT_Lam.

(* ========== 【旗舰基座】仿射差分恒等式（无前提 Qeq 代数泛形） ========== *)

(* 泛形：lam ↦ lam·h0 + (1-lam)·h1 的差分 = (lam1-lam2)·(h0-h1)。
   变量序取 λ 在前（与 H_lam 定义 lam * H_adj (P0 l) 同序，消费零换序成本）。
   防御式收口：二目 Qminus 全部 change 成 1 + - x 加法形再 ring
   （qlia 卡第 12 条配方，H_lam_mono 同款模板）。 *)
Lemma lam_affine_diff_sub : forall h0 h1 lam1 lam2 : Q,
  lam1 * h0 + (1 - lam1) * h1 - (lam2 * h0 + (1 - lam2) * h1)
  == (lam1 - lam2) * (h0 - h1).
Proof.
  intros h0 h1 lam1 lam2.
  change (1 - lam1) with (1 + - lam1)%Q.
  change (1 - lam2) with (1 + - lam2)%Q.
  change (lam1 - lam2) with (lam1 + - lam2)%Q.
  change (h0 - h1) with (h0 + - h1)%Q.
  change ((lam1 * h0 + (1 + - lam1) * h1) - (lam2 * h0 + (1 + - lam2) * h1))
    with ((lam1 * h0 + (1 + - lam1) * h1)
          + - (lam2 * h0 + (1 + - lam2) * h1))%Q.
  ring.
Qed.

(* H_lam 实形的差分恒等式：H_lam l s lam1 - H_lam l s lam2
   = (lam1 - lam2) * (H_adj (P0 l) - H_adj (Pinf l s))。 *)
Theorem H_lam_diff_sub : forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  H_lam l s lam1 - H_lam l s lam2
  == (lam1 - lam2) * (H_adj (P0 l) - H_adj (Pinf l s)).
Proof.
  intros l s lam1 lam2. unfold H_lam.
  exact (lam_affine_diff_sub (H_adj (P0 l)) (H_adj (Pinf l s)) lam1 lam2).
Qed.

(* 仿射标准形：H_lam l s lam = h1 + lam * (h0 - h1)。 *)
Theorem H_lam_affine : forall (l : list Q) (s : nat) (lam : Q),
  H_lam l s lam == H_adj (Pinf l s) + lam * (H_adj (P0 l) - H_adj (Pinf l s)).
Proof.
  intros l s lam. unfold H_lam.
  change (1 - lam) with (1 + - lam)%Q.
  change (H_adj (P0 l) - H_adj (Pinf l s))
    with (H_adj (P0 l) + - H_adj (Pinf l s))%Q.
  ring.
Qed.

(* ========== 【旗舰】反向单调：零前提真方向 ========== *)

(* 真单调方向：λ 增 ⟹ H_lam 减。斜率 h0 - h1 <= 0（跨相下界恒成立）
   × (lam1 - lam2) <= 0，两非正之积非负——经 xq_mul_nonneg 两次反号装配。 *)
Theorem H_lam_anti_mono : forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  (lam1 <= lam2)%Q -> (H_lam l s lam2 <= H_lam l s lam1)%Q.
Proof.
  intros l s lam1 lam2 Hlam.
  (* 两因子皆非正：(lam1-lam2) <= 0 且 (h0-h1) <= 0（跨相下界）
     ——先换位成两非正的反号 (lam2-lam1)·(h1-h0) 再做非负乘法装配。 *)
  assert (Hs : (0 <= (lam1 - lam2) * (H_adj (P0 l) - H_adj (Pinf l s)))%Q).
  { assert (Hr : (lam1 - lam2) * (H_adj (P0 l) - H_adj (Pinf l s))
                 == (lam2 - lam1) * (H_adj (Pinf l s) - H_adj (P0 l))).
    { change (lam1 - lam2) with (lam1 + - lam2)%Q.
      change (lam2 - lam1) with (lam2 + - lam1)%Q.
      change (H_adj (P0 l) - H_adj (Pinf l s))
        with (H_adj (P0 l) + - H_adj (Pinf l s))%Q.
      change (H_adj (Pinf l s) - H_adj (P0 l))
        with (H_adj (Pinf l s) + - H_adj (P0 l))%Q.
      ring. }
    rewrite Hr. apply xq_mul_nonneg.
    - apply (proj1 (Qle_0_sub' lam1 lam2)). exact Hlam.
    - apply (proj1 (Qle_0_sub' (H_adj (P0 l)) (H_adj (Pinf l s)))).
      apply H_adj_cross_phase_lb. }
  apply (proj2 (Qle_0_sub' _ _)).
  rewrite (H_lam_diff_sub l s lam1 lam2). exact Hs.
Qed.

(* 递增方向（h1 <= h0 前提下）：既有 H_lam_mono 的差分恒等式重述版。 *)
Theorem H_lam_mono_diff : forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  (H_adj (Pinf l s) <= H_adj (P0 l))%Q ->
  (lam1 <= lam2)%Q -> (H_lam l s lam1 <= H_lam l s lam2)%Q.
Proof.
  intros l s lam1 lam2 Hle Hlam.
  assert (Hs : (0 <= (lam2 - lam1) * (H_adj (P0 l) - H_adj (Pinf l s)))%Q).
  { apply xq_mul_nonneg.
    - apply (proj1 (Qle_0_sub' lam1 lam2)). exact Hlam.
    - apply (proj1 (Qle_0_sub' (H_adj (Pinf l s)) (H_adj (P0 l)))). exact Hle. }
  apply (proj2 (Qle_0_sub' _ _)).
  rewrite (H_lam_diff_sub l s lam2 lam1). exact Hs.
Qed.

(* 斜率为零（h0 == h1）时 H_lam 为常数——既有 mono 空洞性的显式化：
   该情形下两个方向同时成立且结论平庸。 *)
Theorem H_lam_const_when_eq : forall (l : list Q) (s : nat) (lam : Q),
  H_adj (P0 l) == H_adj (Pinf l s) -> H_lam l s lam == H_adj (P0 l).
Proof.
  intros l s lam Heq. unfold H_lam. rewrite Heq. ring.
Qed.

(* 中点凸性等式面（仿射性的对称刻画；除法目标走 field）。 *)
Theorem H_lam_midpoint : forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  H_lam l s ((lam1 + lam2) / 2) == (H_lam l s lam1 + H_lam l s lam2) / 2.
Proof.
  intros l s lam1 lam2. unfold H_lam.
  change (1 - (lam1 + lam2) / 2) with (1 + - ((lam1 + lam2) / 2))%Q.
  change (1 - lam1) with (1 + - lam1)%Q.
  change (1 - lam2) with (1 + - lam2)%Q.
  field.
Qed.

(* ========== 【主件】λ-argmin 构造性：显式端点选择器 ========== *)

(* 最优 λ 的显式选择器：h0 <= h1 时取端点 1（递减到底），否则取端点 0。 *)
Definition lam_opt (h0 h1 : Q) : Q := if Qle_bool h0 h1 then 1 else 0.

Theorem lam_opt_values : forall h0 h1 : Q,
  lam_opt h0 h1 = 1%Q \/ lam_opt h0 h1 = 0%Q.
Proof.
  intros h0 h1. unfold lam_opt.
  destruct (Qle_bool h0 h1).
  - left. reflexivity.
  - right. reflexivity.
Qed.

Theorem lam_opt_range : forall h0 h1 : Q, (0 <= lam_opt h0 h1 <= 1)%Q.
Proof.
  intros h0 h1. destruct (lam_opt_values h0 h1) as [E | E].
  - rewrite E. split.
    + exact (xq_Qle_bool_le 0 1 eq_refl).
    + apply Qle_refl.
  - rewrite E. split.
    + apply Qle_refl.
    + exact (xq_Qle_bool_le 0 1 eq_refl).
Qed.

(* 最优值定理（泛形）：端点选择器的取值不超过 [0,1] 内任意 λ 的取值。
   两分支各化归一次乘法非负装配：
   h0 <= h1 分支取 λ*=1，差 = (1-lam)·(h1-h0)；否则取 λ*=0，差 = lam·(h0-h1)。 *)
Theorem lam_opt_min : forall (h0 h1 lam : Q),
  (0 <= lam <= 1)%Q ->
  (lam_opt h0 h1 * h0 + (1 - lam_opt h0 h1) * h1
   <= lam * h0 + (1 - lam) * h1)%Q.
Proof.
  intros h0 h1 lam H01. destruct H01 as [Hlam0 Hlam1].
  unfold lam_opt. destruct (Qle_bool h0 h1) eqn:E.
  - (* h0 <= h1：λ* = 1，最优值 = h0 *)
    assert (Hd : (0 <= lam * h0 + (1 - lam) * h1 - (1 * h0 + (1 - 1) * h1))%Q).
    { assert (Er : lam * h0 + (1 - lam) * h1 - (1 * h0 + (1 - 1) * h1)
                   == (1 - lam) * (h1 - h0)) by ring.
      rewrite Er. apply xq_mul_nonneg.
      + apply (proj1 (Qle_0_sub' lam 1)). exact Hlam1.
      + apply (proj1 (Qle_0_sub' h0 h1)). apply xq_Qle_bool_le. exact E. }
    apply (proj2 (Qle_0_sub' _ _)). exact Hd.
  - (* h0 > h1：λ* = 0，最优值 = h1 *)
    assert (Hge : (h1 <= h0)%Q) by (apply Qle_bool_false_le; exact E).
    assert (Hd : (0 <= lam * h0 + (1 - lam) * h1 - (0 * h0 + (1 - 0) * h1))%Q).
    { assert (Er : lam * h0 + (1 - lam) * h1 - (0 * h0 + (1 - 0) * h1)
                   == lam * (h0 - h1)) by ring.
      rewrite Er. apply xq_mul_nonneg.
      + exact Hlam0.
      + apply (proj1 (Qle_0_sub' h1 h0)). exact Hge. }
    apply (proj2 (Qle_0_sub' _ _)). exact Hd.
Qed.

(* H_lam 消费版：端点选择器在混合熵上实现 argmin。 *)
Theorem H_lam_lam_opt_min : forall (l : list Q) (s : nat) (lam : Q),
  (0 <= lam <= 1)%Q ->
  (H_lam l s (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s)))
   <= H_lam l s lam)%Q.
Proof.
  intros l s lam H01. destruct H01 as [Hlam0 Hlam1].
  unfold H_lam. apply lam_opt_min. split; assumption.
Qed.

(* 端点求值桥：选择器的取值恒为某一端的相熵（直用底座端点件）。 *)
Theorem H_lam_lam_opt_endpoint : forall (l : list Q) (s : nat),
  H_lam l s (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))) == H_adj (P0 l)
  \/ H_lam l s (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))) == H_adj (Pinf l s).
Proof.
  intros l s. destruct (lam_opt_values (H_adj (P0 l)) (H_adj (Pinf l s)))
    as [E | E].
  - left. rewrite E. apply H_lam_lam1.
  - right. rewrite E. apply H_lam_lam0.
Qed.

(* 诚实锚：本盘跨相下界恒给出 h0 <= h1，故端点选择器恒返 1（P0 相）。
   argmin 的价值在一般代数框架（h0 h1 泛形）而非本盘特值。 *)
Theorem lam_opt_cross_phase : forall (l : list Q) (s : nat),
  lam_opt (H_adj (P0 l)) (H_adj (Pinf l s)) = 1%Q.
Proof.
  intros l s. unfold lam_opt.
  rewrite (xq_Qle_bool_true _ _ (H_adj_cross_phase_lb l s)). reflexivity.
Qed.

(* ========== 【主件】align_lambda 救活：首三个定理消费 ========== *)

(* 底座 L69 的 align_lambda 是字面恒等定义（全盘零消费）。
   本块给它补上行为面：定义即恒等的 eta 面 + 熵面不变 + argmin 稳定性。 *)

Theorem align_lambda_id : forall lam : Q, align_lambda lam == lam.
Proof.
  intro lam. unfold align_lambda. reflexivity.
Qed.

Theorem align_lambda_H_lam : forall (l : list Q) (s : nat) (lam : Q),
  H_lam l s (align_lambda lam) == H_lam l s lam.
Proof.
  (* 恒等定义即 eta 面：unfold 后两侧语法同形，reflexivity 直收
     （Qeq 面内的 rewrite 也救不了 H_lam 应用实参位——该位无 Proper 实例） *)
  intros l s lam. unfold align_lambda. reflexivity.
Qed.

(* argmin 稳定性：对 λ 先 align 再求值，最优值定理照旧成立。 *)
Theorem lam_opt_min_align : forall (l : list Q) (s : nat) (lam : Q),
  (0 <= lam <= 1)%Q ->
  (H_lam l s (align_lambda (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))))
   <= H_lam l s lam)%Q.
Proof.
  intros l s lam H01. destruct H01 as [Hlam0 Hlam1].
  (* Qle 目标下 H_lam 应用实参无 Proper 实例、Qminus 实参更断 setoid 路径
     ——改走 Qeq 面中转：align_lambda_H_lam（Qeq 目标内改写合法）+ Qeq_le 桥 *)
  apply (Qle_trans _ (H_lam l s (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))))).
  - apply xq_Qeq_le. apply align_lambda_H_lam.
  - apply H_lam_lam_opt_min. split; assumption.
Qed.

(* align 保持区间：align_lambda 的像仍在 [0,1] 内。 *)
Theorem align_lambda_range : forall lam : Q,
  (0 <= lam <= 1)%Q -> (0 <= align_lambda lam <= 1)%Q.
Proof.
  intros lam Hr. destruct Hr as [H0 H1]. split.
  - exact H0.
  - exact H1.
Qed.

(* ========== 【加分项】端点外插警戒：越出 [0,1] 即可越出端点带 ========== *)

(* 1 < lam 时 H_lam 可跌破下端 min{h0,h1}：见证列 [1;5;2]
   （h0 = H_adj [1;2;5] = 4，h1 = H_adj [1;5;2] = 7，h0 <= h1 恒成立），
   取 lam = 2 得 H_lam = 2·4 + (1-2)·7 = 1 < 4 = min。vm_compute 数值面。 *)
Theorem H_lam_extrap_below_counterex : exists (l : list Q) (s : nat) (lam : Q),
  (1 < lam)%Q /\
  (H_lam l s lam < H_adj (P0 l))%Q /\
  (H_adj (P0 l) <= H_adj (Pinf l s))%Q.
Proof.
  exists [1; 5; 2], 0%nat, 2%Q. split.
  - vm_compute. reflexivity.
  - split.
    + vm_compute. reflexivity.
    + apply H_adj_cross_phase_lb.
Qed.

(* 对偶面：lam < 0 时 H_lam 可跃升越上端 max{h0,h1}：同一见证列取 lam = -1
   得 H_lam = (-1)·4 + (1-(-1))·7 = 10 > 7 = max。 *)
Theorem H_lam_extrap_above_counterex : exists (l : list Q) (s : nat) (lam : Q),
  (lam < 0)%Q /\
  (H_adj (Pinf l s) < H_lam l s lam)%Q /\
  (H_adj (P0 l) <= H_adj (Pinf l s))%Q.
Proof.
  exists [1; 5; 2], 0%nat, (-1)%Q. split.
  - vm_compute. reflexivity.
  - split.
    + vm_compute. reflexivity.
    + apply H_adj_cross_phase_lb.
Qed.

(* ############################################################
   M3 归并段【U19 件 · 真旋转底座 λ-相位插值族】
   原独立文件整体并入：内容零改动，仅删其对本文件的 Require 行
   （变同文件直引，对 DTPT / DTPT_ROTC / DTPT_Entropy 的 Require
   保留——本文件由此新增对 DTPT_ROTC 的依赖）、审计并档文尾。
   ############################################################ *)

(* ========== 【保底】定义 + 端点 ========== *)

(* 真底座 λ-相位插值：λ=1 全落排序相 P0，λ=0 全落 k 格真旋转相。 *)
Definition H_lam_cyc (l : list Q) (k : nat) (lam : Q) : Q :=
  lam * H_adj (P0 l) + (1 - lam) * H_adj (rotc k l).

(* 端点 λ=1：零乘一乘后只余 P0 相（k 无关——排序端与转数解耦）。 *)
Theorem H_lam_cyc_lam1 : forall (l : list Q) (k : nat),
  H_lam_cyc l k 1 == H_adj (P0 l).
Proof.
  intros l k. unfold H_lam_cyc.
  replace (1 - 1)%Q with 0%Q by reflexivity.
  ring.
Qed.

(* 端点 λ=0：零乘一乘后只余 k 格真旋转相。 *)
Theorem H_lam_cyc_lam0 : forall (l : list Q) (k : nat),
  H_lam_cyc l k 0 == H_adj (rotc k l).
Proof.
  intros l k. unfold H_lam_cyc.
  replace (1 - 0)%Q with 1%Q by reflexivity.
  ring.
Qed.

(* 诚实锚·旧件退化面桥：零转相点 k=0 上真底座插值与旧件 s-坍缩面
   （Pinf 恒等 ⟹ 第二端即原始序 l）完全重合——迁移不丢旧信息。 *)
Theorem H_lam_cyc_k0_oldface : forall (l : list Q) (lam : Q),
  H_lam_cyc l 0%nat lam == lam * H_adj (P0 l) + (1 - lam) * H_adj l.
Proof.
  intros l lam. unfold H_lam_cyc. rewrite rotc_0. reflexivity.
Qed.

(* ========== 【旗舰】差分恒等式 + 双方向单调 ========== *)

(* 差分恒等式：U5 席泛形 lam_affine_diff_sub 的真底座实形——
   H_lam_cyc l k lam1 - H_lam_cyc l k lam2 = (lam1-lam2)·(h0-hk)。
   直接 exact 实例化（禁重证）。 *)
Theorem H_lam_cyc_diff : forall (l : list Q) (k : nat) (lam1 lam2 : Q),
  H_lam_cyc l k lam1 - H_lam_cyc l k lam2
  == (lam1 - lam2) * (H_adj (P0 l) - H_adj (rotc k l)).
Proof.
  intros l k lam1 lam2. unfold H_lam_cyc.
  exact (lam_affine_diff_sub (H_adj (P0 l)) (H_adj (rotc k l)) lam1 lam2).
Qed.

(* 递增方向：旋转端不高于排序端（hk <= h0）时，λ 增 ⟹ 熵增
   （区间前提显式入陈；斜率非负 × 差非负 ⟹ 差分非负）。 *)
Theorem H_lam_cyc_mono_inc : forall (l : list Q) (k : nat) (lam1 lam2 : Q),
  (H_adj (rotc k l) <= H_adj (P0 l))%Q ->
  (0 <= lam1 <= 1)%Q -> (0 <= lam2 <= 1)%Q ->
  (lam1 <= lam2)%Q ->
  (H_lam_cyc l k lam1 <= H_lam_cyc l k lam2)%Q.
Proof.
  intros l k lam1 lam2 Hle _ _ Hlam.
  assert (Hs : (0 <= (lam2 - lam1) * (H_adj (P0 l) - H_adj (rotc k l)))%Q).
  { apply xq_mul_nonneg.
    - apply (proj1 (Qle_0_sub' lam1 lam2)). exact Hlam.
    - apply (proj1 (Qle_0_sub' (H_adj (rotc k l)) (H_adj (P0 l)))). exact Hle. }
  apply (proj2 (Qle_0_sub' _ _)).
  rewrite (H_lam_cyc_diff l k lam2 lam1). exact Hs.
Qed.

(* 递减方向：排序端不高于旋转端（h0 <= hk）时，λ 增 ⟹ 熵减。
   斜率 (h0-hk) <= 0 与差 (lam1-lam2) <= 0 双非正——U5 席反号装配
   配方：先换位恒等式（change 防御 + ring）再做非负乘法。 *)
Theorem H_lam_cyc_mono_dec : forall (l : list Q) (k : nat) (lam1 lam2 : Q),
  (H_adj (P0 l) <= H_adj (rotc k l))%Q ->
  (0 <= lam1 <= 1)%Q -> (0 <= lam2 <= 1)%Q ->
  (lam1 <= lam2)%Q ->
  (H_lam_cyc l k lam2 <= H_lam_cyc l k lam1)%Q.
Proof.
  intros l k lam1 lam2 Hle _ _ Hlam.
  assert (Hs : (0 <= (lam1 - lam2) * (H_adj (P0 l) - H_adj (rotc k l)))%Q).
  { assert (Hr : (lam1 - lam2) * (H_adj (P0 l) - H_adj (rotc k l))
                 == (lam2 - lam1) * (H_adj (rotc k l) - H_adj (P0 l))).
    { change (lam1 - lam2) with (lam1 + - lam2)%Q.
      change (lam2 - lam1) with (lam2 + - lam1)%Q.
      change (H_adj (P0 l) - H_adj (rotc k l))
        with (H_adj (P0 l) + - H_adj (rotc k l))%Q.
      change (H_adj (rotc k l) - H_adj (P0 l))
        with (H_adj (rotc k l) + - H_adj (P0 l))%Q.
      ring. }
    rewrite Hr. apply xq_mul_nonneg.
    - apply (proj1 (Qle_0_sub' lam1 lam2)). exact Hlam.
    - apply (proj1 (Qle_0_sub' (H_adj (P0 l)) (H_adj (rotc k l)))). exact Hle. }
  apply (proj2 (Qle_0_sub' _ _)).
  rewrite (H_lam_cyc_diff l k lam1 lam2). exact Hs.
Qed.

(* ========== 【主件】与旧件的诚实分离 ========== *)

(* 分离件（s-坍缩面形）：存在 l k lam 使真底座插值 ≠ 旧件 s-坍缩面。
   见证复用 U3 席 H_rotc_separates 的 [0;1;2] 转 1 格：
   H_adj (P0 [0;1;2]) = 2，H_adj (rotc 1 [0;1;2]) = H_adj [1;2;0] = 3，
   lam = 1/2：左 = 1 + 3/2 = 5/2 ≠ 1 + 1 = 2 = 右。vm_compute 数值面。 *)
Theorem H_lam_cyc_oldface_separates : exists (l : list Q) (k : nat) (lam : Q),
  H_lam_cyc l k lam <> lam * H_adj (P0 l) + (1 - lam) * H_adj l.
Proof.
  exists [0; 1; 2], 1%nat, (1#2)%Q.
  intro Hc. unfold H_lam_cyc in Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* 分离件（直比形）：固定 s 后与旧 H_lam 直比——Pinf_eq_l 把旧件第二
   端归到原始序，与 s-坍缩面同面，故同一见证列照收。 *)
Theorem H_lam_cyc_H_lam_separates : exists (l : list Q) (k s : nat) (lam : Q),
  H_lam_cyc l k lam <> H_lam l s lam.
Proof.
  exists [0; 1; 2], 1%nat, 0%nat, (1#2)%Q.
  unfold H_lam. rewrite (Pinf_eq_l [0; 1; 2] 0%nat).
  intro Hc. unfold H_lam_cyc in Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* ========== 【加分】λ-argmin_cyc ========== *)

(* 最优 λ 选择器：直接引 U5 席 lam_opt（h0 <= hk 取 1 冲排序端，
   否则取 0 落旋转端）——底座纪律：禁重证。 *)
Definition lam_opt_cyc (h0 hk : Q) : Q := lam_opt h0 hk.

Theorem lam_opt_cyc_values : forall h0 hk : Q,
  lam_opt_cyc h0 hk = 1%Q \/ lam_opt_cyc h0 hk = 0%Q.
Proof.
  intros h0 hk. unfold lam_opt_cyc. exact (lam_opt_values h0 hk).
Qed.

Theorem lam_opt_cyc_range : forall h0 hk : Q,
  (0 <= lam_opt_cyc h0 hk <= 1)%Q.
Proof.
  intros h0 hk. unfold lam_opt_cyc. exact (lam_opt_range h0 hk).
Qed.

(* 最优值定理（真底座消费版）：端点选择器的取值不超过 [0,1] 内
   任意 λ 的真底座插值。unfold 后即 lam_opt_min 原形。 *)
Theorem H_lam_cyc_lam_opt_cyc_min : forall (l : list Q) (k : nat) (lam : Q),
  (0 <= lam <= 1)%Q ->
  (H_lam_cyc l k (lam_opt_cyc (H_adj (P0 l)) (H_adj (rotc k l)))
   <= H_lam_cyc l k lam)%Q.
Proof.
  intros l k lam H01. destruct H01 as [Hlam0 Hlam1].
  unfold H_lam_cyc, lam_opt_cyc.
  apply lam_opt_min. split; assumption.
Qed.

(* 端点求值桥：选择器取值恒为某一端的相熵（排序端或真旋转端）。 *)
Theorem H_lam_cyc_lam_opt_cyc_endpoint : forall (l : list Q) (k : nat),
  H_lam_cyc l k (lam_opt_cyc (H_adj (P0 l)) (H_adj (rotc k l))) == H_adj (P0 l)
  \/ H_lam_cyc l k (lam_opt_cyc (H_adj (P0 l)) (H_adj (rotc k l)))
     == H_adj (rotc k l).
Proof.
  intros l k. unfold lam_opt_cyc.
  destruct (lam_opt_values (H_adj (P0 l)) (H_adj (rotc k l))) as [E | E].
  - left. rewrite E. apply H_lam_cyc_lam1.
  - right. rewrite E. apply H_lam_cyc_lam0.
Qed.

End DTPT_Lam.
Import DTPT_Lam.

(* ========== 旗舰假设审计（M3 归并后 8 件并档） ========== *)

Print Assumptions H_lam_anti_mono.
Print Assumptions H_lam_cyc_diff.
Print Assumptions H_lam_cyc_mono_inc.
Print Assumptions H_lam_cyc_mono_dec.
Print Assumptions H_lam_cyc_oldface_separates.
Print Assumptions H_lam_cyc_H_lam_separates.
Print Assumptions H_lam_cyc_lam_opt_cyc_min.
Print Assumptions H_lam_cyc_lam_opt_cyc_endpoint.
