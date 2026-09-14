(* ============================================================
   DTPT_Bridge_Rot.v — P3 桥接层第六棒（席 P3-B6，2026-09-15）
   职责：旋转族旗舰 Set 形桥接——底座 DTPT_Rotation.v
         （棒 6b 改名件：原 DTPT_Cyc.v 全量 2,005 行，名不变只变
         限定路径；本棒消费其改名后形态）的 Prop 证件升级为
         信息性 Type/Set 面。
     §1 本地信息性类型族 QleT/QeqT（构造子携 Prop 证明参＝提取
        擦除惯例 B1 同款；以 Arguments 显式声明取代全局
        Set Implicit Arguments——B3 坑3 根除，B4 同款）
     §2 保底件：H_rotc_separates_set——非退化分离见证的
        sigT 信息性形（Prop exists 不可消除入 Type，按 B3
        tarski_set 同款直构包装：见证 [0;1;2] 转 1 格照盘照录）
     §3 旗舰件：rotc_class_sharp_ub_set——2·spread 锐化上界的
        QleT 面（盘上 rotc_class_sharp_ub 为 Qle ≤ 面，逐字对齐）
     §4 旗舰副件：rotc_spectrum_bound_set——谱有限性的 sigT
        信息性形（Prop 版二分为 cyc_nat_le_gt_cases 的 or 面，
        不可消除；此处换 stdlib 可计算二分 le_lt_dec 同款直构，
        两支见证与界逐字照盘）
     §5 主件：偏差判别器 phase_dev 可执行面三件——sumbool
        判定器 / 稳定面 QeqT 证书（消费盘上 phase_dev_stable）/
        sigT 偏差见证（消费盘上 phase_dev_witness 直构）
     §6 加分件：H_lam_cyc 端点双件 QeqT 面（消费盘上
        H_lam_cyc_lam1 / H_lam_cyc_lam0）
     §7 提取探针：逐件独立提取，验收 Obj.magic 计数 0
   依赖（全部冻结只读）：DTPT / DTPT_Entropy / DTPT_Rotation
         （棒 6b 改名件；其下游 ROTC/Entropy2 已退役，本文件
         与退役件零接触）。本文件不 Require DTPT_Bridge /
         DTPT_Bridge_Dig（并发席位文件，防竞态；QleT/QeqT 族
         本地镜像，惯例同构 B1 §1 / B4 §1 同款形——依赖链
         DTPT/DTPT_Entropy/DTPT_Rotation 全链 grep 该族名零
         命中，零撞名实测在案）。
   命名：桥件名沿任务书指定（H_rotc_separates_set 等 8 件，
         _set 后缀 B1-B5 惯例）；提取产物 b6_ 前缀；模块
         DTPT_Bridge_Rot 限名隔离。
   认证目标：零承认零公理；Error=0 Warning=0；Obj.magic=0 实测。
   纪律：温控协议 v2（coqc 全机 ≤3 先查后编）；禁碰一切既有 .v
         （本席独占本新建件）；禁 git；nat 字面量全显式 %nat；
         Q_scope 自开。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Extraction.
Import ListNotations.
Require DTPT.
Require DTPT_Entropy.
Require DTPT_Rotation.
Open Scope Q_scope.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.
Import DTPT_Rotation.DTPT_Rotation.

Module DTPT_Bridge_Rot.

(* ========== §1 本地信息性类型族（QleT/QeqT 惯例镜像） ========== *)

Inductive QleT (x y : Q) : Type :=
| qleT_intro : (x <= y)%Q -> QleT x y.

Arguments qleT_intro {x y} _.

Inductive QeqT (x y : Q) : Type :=
| qeqT_intro : (x == y)%Q -> QeqT x y.

Arguments qeqT_intro {x y} _.

(* ========== §2 保底件：非退化分离见证的信息性形 ========== *)

(* 盘上 H_rotc_separates（DTPT_Rotation.v §S5 段）：Prop exists 形
   exists l n, H_adj (rotc n l) <> H_adj l，见证 [0;1;2] 转 1 格
   （H_adj 2 -> 3）。Prop exists 不可消除入 Type，故 sigT 信息性
   形按 B3 tarski_set 同款直构：见证值照盘照录，闭包证明同款
   （vm_compute 一发 + discriminate）。 <> 分量为 Prop 证明参，
   随提取擦除惯例留 __（B1 §G1 同款声明）。 *)
Theorem H_rotc_separates_set :
  {l : list Q & {n : nat & H_adj (rotc n l) <> H_adj l}}.
Proof.
  exists [0;1;2]. exists 1%nat.
  intro Hc. vm_compute in Hc. discriminate Hc.
Defined.

(* ========== §3 旗舰件：2·spread 锐化上界的 QleT 面 ========== *)

(* 盘上 rotc_class_sharp_ub（DTPT_Rotation.v §S6 段）为 Qle ≤ 面：
   forall l k, SortedQ l -> (H_adj (rotc k l) <= 2 * (lastq l - hd 0 l))%Q.
   桥面逐字对齐（任务书草式即此形），qleT_intro 一跳包装。 *)
Theorem rotc_class_sharp_ub_set : forall (l : list Q) (k : nat),
  SortedQ l -> QleT (H_adj (rotc k l)) (2 * (lastq l - hd 0 l)).
Proof.
  intros l k HS. apply qleT_intro.
  exact (rotc_class_sharp_ub l k HS).
Defined.

(* ========== §4 旗舰副件：谱有限性的 sigT 信息性形 ========== *)

(* 盘上 rotc_spectrum_bound（DTPT_Rotation.v §M5-1 段）：
   exists k', (k' <= length l - 1)%nat /\ rotc k l = rotc k' l
   （Leibniz 表等）。其证之二分为 Prop or 面（cyc_nat_le_gt_cases）
   不可消除入 Type；此处换 stdlib 可计算二分 le_lt_dec 同款直构：
   两支见证（k >= 表长取 k' = k；越界冻结回 k' = 0）与界逐字照盘，
   rotc_ge_len_id / rotc_0 消费面不变。 *)
Theorem rotc_spectrum_bound_set : forall (k : nat) (l : list Q),
  {k' : nat & (k' <= length l - 1)%nat /\ rotc k l = rotc k' l}.
Proof.
  intros k l. destruct (le_lt_dec (S k) (length l)) as [Hlt | Hge].
  - exists k. split.
    + lia.
    + reflexivity.
  - assert (Hge' : (length l <= k)%nat) by lia.
    exists 0%nat. split.
    + lia.
    + rewrite (rotc_ge_len_id k l Hge'). rewrite rotc_0. reflexivity.
Defined.

(* ========== §5 主件：偏差判别器 phase_dev 可执行面 ========== *)

(* 盘上 phase_dev（DTPT_Rotation.v §S6 段）本为 bool 值可执行定义：
   negb (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l)))。
   ① sumbool 判定器：bool 二分直构（分支目标被 destruct 抽象为
   计算形——B3 坑1 在案，处方 reflexivity 收口）。 *)
Theorem phase_dev_spec_set : forall (l : list Q) (k : nat),
  {phase_dev l k = true} + {phase_dev l k = false}.
Proof.
  intros l k. destruct (phase_dev l k).
  - left. reflexivity.
  - right. reflexivity.
Defined.

(* ② 稳定面 QeqT 证书：不偏差时两侧数值相等（消费盘上
   phase_dev_stable：phase_dev l k = false -> H_adj (rotc k l)
   == H_adj (P0 l)），qeqT_intro 一跳包装。 *)
Theorem phase_dev_stable_set : forall (l : list Q) (k : nat),
  phase_dev l k = false -> QeqT (H_adj (rotc k l)) (H_adj (P0 l)).
Proof.
  intros l k H. apply qeqT_intro. apply phase_dev_stable. exact H.
Defined.

(* ③ 偏差见证 sigT 信息性形：Prop exists（盘上 phase_dev_witness）
   不可消除，直构同款见证 [0;1;2] 转 1 格（vm_compute 闭式）。 *)
Theorem phase_dev_witness_set : {l : list Q & {k : nat & phase_dev l k = true}}.
Proof.
  exists [0;1;2]. exists 1%nat. vm_compute. reflexivity.
Defined.

(* ========== §6 加分件：H_lam_cyc 端点双件 QeqT 面 ========== *)

(* 盘上 H_lam_cyc_lam1 / H_lam_cyc_lam0（DTPT_Rotation.v §S7 段）：
   λ=1 全落排序相 P0、λ=0 全落 k 格真旋转相。QeqT 一跳包装。 *)
Theorem H_lam_cyc_lam1_set : forall (l : list Q) (k : nat),
  QeqT (H_lam_cyc l k 1) (H_adj (P0 l)).
Proof.
  intros l k. apply qeqT_intro. apply H_lam_cyc_lam1.
Defined.

Theorem H_lam_cyc_lam0_set : forall (l : list Q) (k : nat),
  QeqT (H_lam_cyc l k 0) (H_adj (rotc k l)).
Proof.
  intros l k. apply qeqT_intro. apply H_lam_cyc_lam0.
Defined.

(* ========== §7 提取探针（U12 配方：逐件独立提取，
     验收指标＝Obj.magic 计数 0，验后产物清除） ========== *)

Set Extraction Output Directory ".".
Extraction "b6_H_rotc_separates_set_ext.ml" H_rotc_separates_set.
Extraction "b6_rotc_class_sharp_ub_set_ext.ml" rotc_class_sharp_ub_set.
Extraction "b6_rotc_spectrum_bound_set_ext.ml" rotc_spectrum_bound_set.
Extraction "b6_phase_dev_spec_set_ext.ml" phase_dev_spec_set.
Extraction "b6_phase_dev_stable_set_ext.ml" phase_dev_stable_set.
Extraction "b6_phase_dev_witness_set_ext.ml" phase_dev_witness_set.
Extraction "b6_H_lam_cyc_lam1_set_ext.ml" H_lam_cyc_lam1_set.
Extraction "b6_H_lam_cyc_lam0_set_ext.ml" H_lam_cyc_lam0_set.

(* ========== 终验：公理闭包审计 ========== *)

Print Assumptions H_rotc_separates_set.
Print Assumptions rotc_class_sharp_ub_set.
Print Assumptions rotc_spectrum_bound_set.
Print Assumptions phase_dev_spec_set.
Print Assumptions phase_dev_stable_set.
Print Assumptions phase_dev_witness_set.
Print Assumptions H_lam_cyc_lam1_set.
Print Assumptions H_lam_cyc_lam0_set.

End DTPT_Bridge_Rot.
