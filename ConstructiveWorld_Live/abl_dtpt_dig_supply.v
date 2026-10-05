(* ==========================================================================)
   abl_dtpt_dig_supply.v — DTPT_DigTheory 前件槽供给卷二（22 槽全做）
   使命：逐槽一条供给定理（tdg_ 前缀），陈述形＝「库内既有组合 ⟹
      DTPT_DigTheory 槽前件」：宿主在库有同形件者直供引述（exact），无者
      在本卷内小步构造（等词改写/构造子反射/尺寸方程改写/bool 判定归约）。
      供给取「槽前件的可满足实例/等词供给形」：宿主槽前件为全称变元上的
      假设，无条件泛形多不恒真，故逐槽给出现档可判定实例域（dQ x/dSeq []/
      dPair dQ dQ/单 cons 表/对角）——逐槽对照见各定理前注。
   依赖清单：Stdlib（QArith.QArith/List/Bool/Arith）＋库件 DTPT、
      DTPT_DigTheory（只读在册 .vo）；Require 顺序＝先 stdlib 后库序；
      透传 Require 不导出短名，本件自 Require 全链并显式 Import（Dig
      构造子族在 DTPT.v:22-28 定义，经 DTPT_DigTheory 依赖链在档）。
   对标行：DTPT 供给卷族体例（头注五字段/查重登记块/代入演示）；槽坐标＝
      DTPT_DigTheory.v :23-:764（登记号 1-22，见各定理前注）。
   构造性注记：全件 Qed 真构造，零承认零公理零节变量；纯 Set 层数据类型
      （Q/nat/bool/Dig/list Dig 全宿主既有，零新增类型）；语句面零析取/
      零存在/零经典逻辑（槽 9 的 <> 位＝宿主槽前件逐字形状）；可提取性由
      被引宿主件既有审计面承载；nat 层显式 %nat、Q 字面一律 %Q。
   编译配方（池 cwd＝dtpt_v2 编译池目录，路径绝对化）：source
      /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh &&
      unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c
      -native-compiler no -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
      abl_dtpt_dig_supply.v；验证＝EXIT=0＋日志零真错＋逐条 Print Assumptions
      全 Closed＋.vo 新于 .v，rocq check 复核；起编前确认无并发编译进程。
   查重登记：顶层名 22 枚全 tdg_ 新前缀，与库内既占 dtd_/dte_/dtr_/dtb_ 及
      tdt_/tbd_ 等同族前缀零撞零别名转发；22 槽逐槽一条、零重复零遗漏；
      宿主 DTPT_DigTheory.v 零字节不动、零重编。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool Arith.
Import ListNotations.

Require DTPT.
Require DTPT_DigTheory.
Import DTPT.DTPT.
Import DTPT_DigTheory.DTPT_DigTheory.

(* ========== 批一：构造子单射族八槽（#1-8，等词供给形） ========== *)

(* 槽 1（DTPT_DigTheory.v:23 dig_inj_dQ 槽1）：dQ x = dQ y —— 等词供给形：
   库内既有组合（Leibniz 等词改写）⟹ 槽前件，代入后 dig_inj_dQ 给出 x = y。 *)
Theorem tdg_dig_inj_dQ_h1 : forall x y : Q, x = y -> dQ x = dQ y.
Proof.
  intros x y H. rewrite H. reflexivity.
Qed.

(* 槽 2（:26 dig_inj_dPair 槽1）：dPair a b = dPair c d —— 等词供给形：
   分量等词改写构造子等词，逐槽一条。 *)
Theorem tdg_dig_inj_dPair_h1 : forall a b c d : Dig,
  a = c -> b = d -> dPair a b = dPair c d.
Proof.
  intros a b c d H1 H2. rewrite H1. rewrite H2. reflexivity.
Qed.

(* 槽 3（:30 dig_inj_dSeq 槽1）：dSeq l1 = dSeq l2 —— 等词供给形：表等词改写。 *)
Theorem tdg_dig_inj_dSeq_h1 : forall l1 l2 : list Dig,
  l1 = l2 -> dSeq l1 = dSeq l2.
Proof.
  intros l1 l2 H. rewrite H. reflexivity.
Qed.

(* 槽 4（:34 dig_inj_dCode 槽1）：dCode n f = dCode m g —— 等词供给形：
   参数位等词＋函数位 Leibniz 等词两支并列改写。 *)
Theorem tdg_dig_inj_dCode_h1 : forall (n m : nat) (f g : nat -> Dig),
  n = m -> f = g -> dCode n f = dCode m g.
Proof.
  intros n m f g Hn Hf. rewrite Hn. rewrite Hf. reflexivity.
Qed.

(* 槽 5（:38 dig_inj_dCode_pointwise 槽1）：dCode n f = dCode m g ——
   同形槽（宿主两件共享同位前件），逐槽一条各立供给。 *)
Theorem tdg_dig_inj_dCode_pointwise_h1 : forall (n m : nat) (f g : nat -> Dig),
  n = m -> f = g -> dCode n f = dCode m g.
Proof.
  intros n m f g Hn Hf. rewrite Hn. rewrite Hf. reflexivity.
Qed.

(* 槽 6（:45 dig_inj_dJudge 槽1）：dJudge a b = dJudge c d —— 等词供给形。 *)
Theorem tdg_dig_inj_dJudge_h1 : forall a b c d : Dig,
  a = c -> b = d -> dJudge a b = dJudge c d.
Proof.
  intros a b c d H1 H2. rewrite H1. rewrite H2. reflexivity.
Qed.

(* 槽 7（:49 dig_inj_dModel 槽1）：dModel a = dModel b —— 等词供给形。 *)
Theorem tdg_dig_inj_dModel_h1 : forall a b : Dig,
  a = b -> dModel a = dModel b.
Proof.
  intros a b H. rewrite H. reflexivity.
Qed.

(* 槽 8（:53 dig_inj_dProofT 槽1）：dProofT a b = dProofT c d —— 等词供给形。 *)
Theorem tdg_dig_inj_dProofT_h1 : forall a b c d : Dig,
  a = c -> b = d -> dProofT a b = dProofT c d.
Proof.
  intros a b c d H1 H2. rewrite H1. rewrite H2. reflexivity.
Qed.

(* ========== 批二：尺寸/投影/数值性族七槽（#9-15） ========== *)

(* 槽 9（:263 dig_lsize_pos 槽1）：l <> [] —— cons 形见证实例域：
   单 cons 表逐字形状永非空（构造子互斥），代入后 dig_lsize_pos 给出
   0 < dig_lsize (x :: l)。语句含 <> 位＝宿主槽前件逐字形状。 *)
Theorem tdg_dig_lsize_pos_h1 : forall (x : Dig) (l : list Dig),
  x :: l <> [].
Proof.
  intros x l H. discriminate H.
Qed.

(* 槽 10（:327 dig_Q_roundtrip 槽1）：d = dQ x —— 对角等词见证：
   实例域 d := dQ x 处前件反射成立，代入后宿主给出 dig_Q (dQ x) = x。 *)
Theorem tdg_dig_Q_roundtrip_h1 : forall x : Q, dQ x = dQ x.
Proof.
  intros x. reflexivity.
Qed.

(* 槽 11（:365 is_num_inv 槽1）：is_num d = true —— 数值域实例 d := dQ x：
   宿主既有件 is_num_eq_dQ（:355）直供。 *)
Theorem tdg_is_num_inv_h1 : forall x : Q, is_num (dQ x) = true.
Proof.
  exact is_num_eq_dQ.
Qed.

(* 槽 12（:374 is_num_inv_sigT 槽1）：is_num d = true —— 同形槽逐槽一条。 *)
Theorem tdg_is_num_inv_sigT_h1 : forall x : Q, is_num (dQ x) = true.
Proof.
  exact is_num_eq_dQ.
Qed.

(* 槽 13（:382 is_num_false_not_dQ 槽1）：is_num d = false —— 非数值域实例
   d := dSeq []：吃宿主诚实边界件 dig_size_one_not_only_num（:421）后件直供。 *)
Theorem tdg_is_num_false_not_dQ_h1 : is_num (dSeq []) = false.
Proof.
  exact (proj2 dig_size_one_not_only_num).
Qed.

(* 槽 14（:390 dig_Q_default0 槽1）：is_num d = false —— 同形槽逐槽一条。 *)
Theorem tdg_dig_Q_default0_h1 : is_num (dSeq []) = false.
Proof.
  exact (proj2 dig_size_one_not_only_num).
Qed.

(* 槽 15（:398 is_num_size1 槽1）：is_num d = true —— 数值域实例逐槽一条。 *)
Theorem tdg_is_num_size1_h1 : forall x : Q, is_num (dQ x) = true.
Proof.
  exact is_num_eq_dQ.
Qed.

(* ========== 批三：判定器/子项序尺寸面七槽（#16-22） ========== *)

(* 槽 16（:513 dig_eqb_size_bound 槽1）：(dig_size a <= n)%nat —— 尺寸实例域
   a := dQ 0、n := 1：吃宿主方程 dig_size_eq_dQ（:172）改写后反射 ≤。 *)
Theorem tdg_dig_eqb_size_bound_h1 : (dig_size (dQ 0%Q) <= 1)%nat.
Proof.
  rewrite dig_size_eq_dQ. apply le_n.
Qed.

(* 槽 17（:513 dig_eqb_size_bound 槽2）：dig_eqb a b = true —— bool 判定面
   本卷内直接构造：对角数值对 (dQ 0, dQ 0) 处判定器归约 Qeq_bool 反射落真。 *)
Theorem tdg_dig_eqb_size_bound_h2 : dig_eqb (dQ 0%Q) (dQ 0%Q) = true.
Proof.
  reflexivity.
Qed.

(* 槽 18（:623 sub_dig_size_bound 槽1）：(dig_size d <= n)%nat —— 尺寸实例域
   d := dQ 0、n := 1（与槽 16 同形，逐槽一条）。 *)
Theorem tdg_sub_dig_size_bound_h1 : (dig_size (dQ 0%Q) <= 1)%nat.
Proof.
  rewrite dig_size_eq_dQ. apply le_n.
Qed.

(* 槽 19（:623 sub_dig_size_bound 槽2）：sub_dig a d = true —— 真子项见证实例：
   吃宿主定义性见证 sub_dig_witness（:604）直供。 *)
Theorem tdg_sub_dig_size_bound_h2 :
  sub_dig (dQ 0%Q) (dPair (dQ 0%Q) (dQ 0%Q)) = true.
Proof.
  exact sub_dig_witness.
Qed.

(* 槽 20（:694 sub_dig_size_mono 槽1）：sub_dig a d = true —— 同形槽逐槽一条。 *)
Theorem tdg_sub_dig_size_mono_h1 :
  sub_dig (dQ 0%Q) (dPair (dQ 0%Q) (dQ 0%Q)) = true.
Proof.
  exact sub_dig_witness.
Qed.

(* 槽 21（:701 sub_dig_size_lt 槽1）：sub_dig a d = true —— 同形槽逐槽一条。 *)
Theorem tdg_sub_dig_size_lt_h1 :
  sub_dig (dQ 0%Q) (dPair (dQ 0%Q) (dQ 0%Q)) = true.
Proof.
  exact sub_dig_witness.
Qed.

(* 槽 22（:764 is_num_h_alg1 槽1）：is_num d = true —— 数值域实例逐槽一条。 *)
Theorem tdg_is_num_h_alg1_h1 : forall x : Q, is_num (dQ x) = true.
Proof.
  exact is_num_eq_dQ.
Qed.

(* ========== 假设面自查（公理面自审附件，22 供给定理逐条打印） ========== *)
Print Assumptions tdg_dig_inj_dQ_h1.
Print Assumptions tdg_dig_inj_dPair_h1.
Print Assumptions tdg_dig_inj_dSeq_h1.
Print Assumptions tdg_dig_inj_dCode_h1.
Print Assumptions tdg_dig_inj_dCode_pointwise_h1.
Print Assumptions tdg_dig_inj_dJudge_h1.
Print Assumptions tdg_dig_inj_dModel_h1.
Print Assumptions tdg_dig_inj_dProofT_h1.
Print Assumptions tdg_dig_lsize_pos_h1.
Print Assumptions tdg_dig_Q_roundtrip_h1.
Print Assumptions tdg_is_num_inv_h1.
Print Assumptions tdg_is_num_inv_sigT_h1.
Print Assumptions tdg_is_num_false_not_dQ_h1.
Print Assumptions tdg_dig_Q_default0_h1.
Print Assumptions tdg_is_num_size1_h1.
Print Assumptions tdg_dig_eqb_size_bound_h1.
Print Assumptions tdg_dig_eqb_size_bound_h2.
Print Assumptions tdg_sub_dig_size_bound_h1.
Print Assumptions tdg_sub_dig_size_bound_h2.
Print Assumptions tdg_sub_dig_size_mono_h1.
Print Assumptions tdg_sub_dig_size_lt_h1.
Print Assumptions tdg_is_num_h_alg1_h1.
