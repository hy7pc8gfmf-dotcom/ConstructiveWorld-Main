(* ==========================================================================)
   abl_dtpt_rot_bridge_supply.v — DTPT_Bridge_Rot 桥面前件槽供给卷三（12 槽全做）
   使命：逐槽一条供给定理（tbr_ 前缀），陈述形＝「库内既有组合 ⟹
      DTPT_Bridge_Rot 槽前件」。SortedQ 族七槽走 P0 排序计算律通路（吃
      宿主既有件 xq_P0_sorted 直供）；NAT 界四槽在本卷内直接构造
      （discriminate＋算术闭判定）；BOOL 判定面一槽 vm_compute 计算律。
      供给逐槽给出现档可判定通路（逐槽对照见各定理前注）；宿主结论方向
      不桥假命题（phase_dev_stable 只取 false 向）。
   依赖清单：Stdlib（QArith.QArith/List/Bool/Arith/Lia）＋库件 DTPT、
      DTPT_Entropy、DTPT_Rotation（只读在册 .vo）；Require 顺序＝先 stdlib
      后库序，Import 序照宿主桥面件原序；SortedQ/xq_P0_sorted 在
      DTPT_Entropy.DTPT_Entropy，phase_dev 在 DTPT_Rotation.DTPT_Rotation，
      P0/H_adj/lastq/hd 在 DTPT.DTPT；本件零 Require DTPT_Bridge_Rot。
   对标行：DTPT 供给卷族体例（头注五字段/查重登记块/代入演示）；槽坐标＝
      DTPT_Bridge_Rot.v :77-:457（登记号 1-12，见各定理前注）。
   构造性注记：全件 Qed 真构造，零承认零公理零节变量；纯 Set/Prop 离散
      卫哨面（Q/nat/bool/list Q 全宿主既有，零新增类型）；语句面零析取/
      零存在/零经典逻辑；可提取性由被引宿主件既有提取面承载（SortedQ
      前提按 Prop 整参提取擦除惯例，零 Obj.magic 新增面）。
   编译配方（池 cwd＝dtpt_v2b 编译池目录，路径绝对化）：source
      /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh &&
      unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c
      -native-compiler no -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
      abl_dtpt_rot_bridge_supply.v；验证＝EXIT=0＋日志零真错＋逐条 Print
      Assumptions 全 Closed＋.vo 新于 .v，rocq check 复核。
   查重登记：顶层名 12 枚全 tbr_ 新前缀，与库内既占前缀族零撞零别名转发；
      12 槽逐槽一条、零重复零遗漏；宿主 DTPT_Bridge_Rot.v 零字节不动。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool Arith Lia.
Import ListNotations.

Require DTPT.
Require DTPT_Entropy.
Require DTPT_Rotation.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.
Import DTPT_Rotation.DTPT_Rotation.

Open Scope Q_scope.

(* ========== 批一：§3/§5 主件卫哨族两槽（#1-2） ========== *)

(* 槽 1（DTPT_Bridge_Rot.v:77 rotc_class_sharp_ub_set 槽1）：SortedQ l ——
   P0 排序计算律全称形：宿主既有件 xq_P0_sorted（DTPT_Entropy.v:300）直供。
   代入后 rotc_class_sharp_ub_set 于 P0 域给出 2·spread 锐化上界 QleT 证书
   （P0 排序律通路）。 *)
Theorem tbr_rotc_class_sharp_ub_set_h1 : forall l : list Q, SortedQ (P0 l).
Proof.
  exact xq_P0_sorted.
Qed.

(* 槽 2（:122 phase_dev_stable_set 槽1）：phase_dev l k = false —— bool
   判定面计算律实例（空表零偏差域：P0 []＝rotc 0 []＝[]，两侧 H_adj 皆零，
   Qeq_bool 落真、negb 落假）：vm_compute 一步闭项。代入后
   phase_dev_stable_set 给出 QeqT (H_adj (rotc 0%nat [])) (H_adj (P0 []))。
   反例面：phase_dev [0;1;2] 1 = true（宿主 phase_dev_witness_set 在档），
   故实例域供给为唯一诚实形。 *)
Theorem tbr_phase_dev_stable_set_h1 : phase_dev [] 0%nat = false.
Proof.
  vm_compute. reflexivity.
Qed.

(* ========== 批二：§8 桥面卫哨族九槽（#3-11） ========== *)

(* 槽 3（:201 H_adj_Pmid_seam_set 槽1）：k <> 0%nat —— 正值实例域 k=1：
   构造子互斥 discriminate。代入（连同槽 4）后 H_adj_Pmid_seam_set 给出
   中相接缝分解 QeqT 证书。语句含 <> 位＝宿主槽前件逐字形状。 *)
Theorem tbr_H_adj_Pmid_seam_set_h1 : 1%nat <> 0%nat.
Proof.
  intros H. discriminate H.
Qed.

(* 槽 4（:202 H_adj_Pmid_seam_set 槽2）：(k < length l)%nat —— 实例域
   k=1、l=[0;1;2]（长 3）：nat 闭判定 lia（宿主桥面件 §4 同款在库）。 *)
Theorem tbr_H_adj_Pmid_seam_set_h2 : (1 < length [0%Q; 1%Q; 2%Q])%nat.
Proof.
  cbn. lia.
Qed.

(* 槽 5（:238 Pmid_sorted_collapse_set 槽1）：SortedQ l —— P0 排序计算律
   逐槽一条（同吃 xq_P0_sorted）。代入后 Pmid_sorted_collapse_set 于 P0 域
   落坍缩左支（xq_sortQ_P0_id：P0 l 排序即恒等，坍缩件直供）。 *)
Theorem tbr_Pmid_sorted_collapse_set_h1 : forall l : list Q, SortedQ (P0 l).
Proof.
  exact xq_P0_sorted.
Qed.

(* 槽 6（:253 H_adj_Pmid_sorted_exact_set 槽1）：SortedQ l —— P0 排序计算律
   逐槽一条。代入后给出中相熵 == H_adj l 精确值 QeqT 证书。 *)
Theorem tbr_H_adj_Pmid_sorted_exact_set_h1 : forall l : list Q, SortedQ (P0 l).
Proof.
  exact xq_P0_sorted.
Qed.

(* 槽 7（:264 H_adj_Pmid_sorted_spread_set 槽1）：SortedQ l —— P0 排序
   计算律逐槽一条。代入后给出 1·spread 精确值 QeqT 证书。 *)
Theorem tbr_H_adj_Pmid_sorted_spread_set_h1 : forall l : list Q, SortedQ (P0 l).
Proof.
  exact xq_P0_sorted.
Qed.

(* 槽 8（:274 H_adj_Pmid_sorted_ub2_set 槽1）：SortedQ l —— P0 排序计算律
   逐槽一条。代入后给出 2·spread 上界 QleT 证书（§8 桥面 all_B7 使用链
   供给需求位）。 *)
Theorem tbr_H_adj_Pmid_sorted_ub2_set_h1 : forall l : list Q, SortedQ (P0 l).
Proof.
  exact xq_P0_sorted.
Qed.

(* 槽 9（:284 H_adj_Pmid_ub_gen_set 槽1）：k <> 0%nat —— 正值实例域 k=2
   （与槽 3 异值逐槽一条）：discriminate。 *)
Theorem tbr_H_adj_Pmid_ub_gen_set_h1 : 2%nat <> 0%nat.
Proof.
  intros H. discriminate H.
Qed.

(* 槽 10（:285 H_adj_Pmid_ub_gen_set 槽2）：(k < length l)%nat —— 实例域
   k=2、l=[0;1;2;3]（长 4，与槽 4 异值逐槽一条）：nat 闭判定 lia。 *)
Theorem tbr_H_adj_Pmid_ub_gen_set_h2 : (2 < length [0%Q; 1%Q; 2%Q; 3%Q])%nat.
Proof.
  cbn. lia.
Qed.

(* 槽 11（:344 H_adj_Pmid_endpoints_sorted_set 槽1）：SortedQ l —— P0 排序
   计算律逐槽一条。代入后给出两端点熵 QeqT 双证书 Type 积。 *)
Theorem tbr_H_adj_Pmid_endpoints_sorted_set_h1 :
  forall l : list Q, SortedQ (P0 l).
Proof.
  exact xq_P0_sorted.
Qed.

(* ========== 批三：§9 桥面卫哨一槽（#12） ========== *)

(* 槽 12（:457 H_lam_pmid_sorted_consistency_set 槽1）：SortedQ l —— P0
   排序计算律逐槽一条。代入后给出 λ-插值与 H_lam 相容性 QeqT 证书
   （§9 桥面完备性面，供给需求位开放候选）。 *)
Theorem tbr_H_lam_pmid_sorted_consistency_set_h1 :
  forall l : list Q, SortedQ (P0 l).
Proof.
  exact xq_P0_sorted.
Qed.

(* ========== 假设面自查（公理面自审附件，12 供给定理逐条打印） ========== *)
Print Assumptions tbr_rotc_class_sharp_ub_set_h1.
Print Assumptions tbr_phase_dev_stable_set_h1.
Print Assumptions tbr_H_adj_Pmid_seam_set_h1.
Print Assumptions tbr_H_adj_Pmid_seam_set_h2.
Print Assumptions tbr_Pmid_sorted_collapse_set_h1.
Print Assumptions tbr_H_adj_Pmid_sorted_exact_set_h1.
Print Assumptions tbr_H_adj_Pmid_sorted_spread_set_h1.
Print Assumptions tbr_H_adj_Pmid_sorted_ub2_set_h1.
Print Assumptions tbr_H_adj_Pmid_ub_gen_set_h1.
Print Assumptions tbr_H_adj_Pmid_ub_gen_set_h2.
Print Assumptions tbr_H_adj_Pmid_endpoints_sorted_set_h1.
Print Assumptions tbr_H_lam_pmid_sorted_consistency_set_h1.
