(* ==========================================================================)
   abl_dtpt_truth_supply.v — DTPT_Truth 前件槽供给卷一（24 槽纯计算位）
   使命：逐槽一条供给定理（tdt_ 前缀），陈述形＝「库内既有组合 ⟹
      DTPT_Truth 槽前件」。供给取「槽前件的可满足实例/守恒计算律」形：
      宿主槽前件为全称变元上的假设，无条件泛形多不恒真，故逐槽给出现档
      可判定的实例域（对角/叶/单点表/Lv0 层）或等词供给形——逐槽对照见
      各定理前注。
   依赖清单：Stdlib（QArith.QArith/List/Bool/Arith）＋库件 DTPT、
      DTPT_Truth（只读在册 .vo）；Require 顺序＝先 stdlib 后库序。
   对标行：DTPT 供给卷族体例（头注五字段/查重登记块/代入演示）；槽坐标＝
      DTPT_Truth.v :286-:1391（登记号见各定理前注）。
   构造性注记：全件 Qed 真构造，零承认零公理零节变量；纯 Set 层数据类型
      （bool/nat/Q/list Q/Level/TrNode/Evidence 全宿主既有，零新增类型）；
      语句面零析取/零存在/零经典逻辑/零否定出口；可提取性由被引宿主件
      既有提取面承载（DTPT_Truth 提取块在册，本件零 Obj.magic 面）；
      nat 层显式 Datatypes.S/O/Nat.add（防 Q_scope 劫持）；Q 字面一律 %Q。
   编译配方（池 cwd＝dtpt_v1 编译池目录，路径绝对化）：source
      /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh &&
      unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c
      -native-compiler no -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
      abl_dtpt_truth_supply.v；验证＝EXIT=0＋日志零真错＋逐条 Print
      Assumptions 全 Closed＋.vo 新于 .v，rocq check 复核。
   查重登记：顶层名 24 枚全 tdt_ 新前缀，与库内既占 dtd_/dte_/dtr_/dtb_ 等
      前缀零撞零别名转发；24 槽逐槽一条、零重复零遗漏；宿主 DTPT_Truth.v
      零字节不动、零重编。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool Arith.
Import ListNotations.

Require DTPT.
Require DTPT_Truth.
Import DTPT_Truth.DTPT_Truth.

(* ========== 批一：INV 三槽（#3/7/9，同形实例供给）＋ 传递/桥/审查器前族 ========== *)

(* 槽 3（DTPT_Truth.v:286 neg_truth_at_neg 槽1）：involutive Code neg ——
   泛形被宿主 negS 反例封死（negS_not_involutive），实例供给取库内既有正例
   码世界 Code:=bool、neg:=negb（negb_involutive_self 同形，此处直供引述）。 *)
Theorem tdt_neg_truth_at_neg_h1 : involutive bool negb.
Proof.
  exact negb_involutive_self.
Qed.

(* 槽 7（:395 diag_conj_spec 槽1）：同形 INV 槽，同款实例供给（逐槽一条）。 *)
Theorem tdt_diag_conj_spec_h1 : involutive bool negb.
Proof.
  exact negb_involutive_self.
Qed.

(* 槽 9（:412 tarski_via_renaming 槽1）：同形 INV 槽，同款实例供给。 *)
Theorem tdt_tarski_via_renaming_h1 : involutive bool negb.
Proof.
  exact negb_involutive_self.
Qed.

(* 槽 11（:474 trLevel_geq_trans 槽1）：trLevel_geq t a = true ——
   实例域 a:=Lv0（层判全序底），宿主既有件 trLevel_geq_Lv0（:160）直供。 *)
Theorem tdt_trLevel_geq_trans_h1 : forall t : TrNode, trLevel_geq t Lv0 = true.
Proof.
  exact trLevel_geq_Lv0.
Qed.

(* 槽 12（:475 trLevel_geq_trans 槽2）：level_le b a = true ——
   实例域 b:=Lv0，level_le 定义首支归约恒真，九支判定面本卷内直接构造。 *)
Theorem tdt_trLevel_geq_trans_h2 : forall a : Level, level_le Lv0 a = true.
Proof.
  intros a. destruct a; reflexivity.
Qed.

(* 槽 13（:501 chain_ok_trans 槽1）：chain_ok l1 l2 l3 = true ——
   对角实例 l1=l2=l3，吃宿主既有件 level_le_refl（:58）双支装配。 *)
Theorem tdt_chain_ok_trans_h1 : forall l : Level, chain_ok l l l = true.
Proof.
  intros l. unfold chain_ok. apply andb_true_intro. split;
    apply level_le_refl.
Qed.

(* 槽 14（:616 cv_lv_inj 槽1）：cv_lv a = cv_lv b —— 等词供给形：
   库内既有组合（Leibniz 等词改写）⟹ 槽前件，cv_lv_inj 随之可代入。 *)
Theorem tdt_cv_lv_inj_h1 : forall a b : DTPT.DTPT.Level,
  a = b -> cv_lv a = cv_lv b.
Proof.
  intros a b H. rewrite H. reflexivity.
Qed.

(* 槽 15（:627 cv_lv_antisym_transport 槽1）：level_le (cv_lv a) (cv_lv b) = true ——
   对角实例 a:=b，吃宿主既有件 level_le_refl（:58）。 *)
Theorem tdt_cv_lv_antisym_transport_h1 : forall a : DTPT.DTPT.Level,
  level_le (cv_lv a) (cv_lv a) = true.
Proof.
  intros a. exact (level_le_refl (cv_lv a)).
Qed.

(* 槽 16（:628 cv_lv_antisym_transport 槽2）：level_le (cv_lv b) (cv_lv a) = true ——
   对角实例 b:=a，同款既有件直供（逐槽一条）。 *)
Theorem tdt_cv_lv_antisym_transport_h2 : forall a : DTPT.DTPT.Level,
  level_le (cv_lv a) (cv_lv a) = true.
Proof.
  intros a. exact (level_le_refl (cv_lv a)).
Qed.

(* 槽 17（:699 Tex_fiber_cast 槽1）：DTPT.DTPT.trPhi t = phi ——
   见证节点计算律：t 取 DTPT 侧 mkTrNode lv phi m v，首投影 iota 归约回 phi。 *)
Theorem tdt_Tex_fiber_cast_h1 : forall (lv : DTPT.DTPT.Level)
    (phi m : DTPT.DTPT.Dig) (v : DTPT.DTPT.Evidence),
  DTPT.DTPT.trPhi (DTPT.DTPT.mkTrNode lv phi m v) = phi.
Proof.
  intros lv phi m v. reflexivity.
Qed.

(* 槽 18（:762 audit_node_mono 槽1）：trLevel t' = trLevel t ——
   记录投影计算律：同层槽构造的节点层级投影归约回层指标本身。 *)
Theorem tdt_audit_node_mono_h1 : forall (lv : Level) (p m : DTPT.DTPT.Dig)
    (v : Evidence),
  trLevel (mkTrNode lv p m v) = lv.
Proof.
  intros lv p m v. reflexivity.
Qed.

(* 槽 19（:763 audit_node_mono 槽2）：trValue t' = trValue t ——
   记录投影计算律：值槽同构（尾投影归约回证据指标）。 *)
Theorem tdt_audit_node_mono_h2 : forall (lv : Level) (p m : DTPT.DTPT.Dig)
    (v : Evidence),
  trValue (mkTrNode lv p m v) = v.
Proof.
  intros lv p m v. reflexivity.
Qed.

(* ========== 批二：组合审查定理槽族（#20-26）＋ 内容判定/尺寸槽族（#27-33） ========== *)

(* 槽 20（:809 audit_gate_level_combo 槽1）：(thr1 <= thr2)%Q ——
   Q 全序对角实例 thr1:=thr2，stdlib 既有件 Qle_refl 直供。 *)
Theorem tdt_audit_gate_level_combo_h1 : forall thr : Q, (thr <= thr)%Q.
Proof.
  intros thr. apply Qle_refl.
Qed.

(* 槽 21（:810 audit_gate_level_combo 槽2）：trLevel_geq t a = true ——
   实例域 a:=Lv0，宿主既有件 trLevel_geq_Lv0 直供（与槽 11 同形，逐槽一条）。 *)
Theorem tdt_audit_gate_level_combo_h2 : forall t : TrNode,
  trLevel_geq t Lv0 = true.
Proof.
  exact trLevel_geq_Lv0.
Qed.

(* 槽 22（:811 audit_gate_level_combo 槽3）：level_le b a = true ——
   实例域 b:=Lv0，九支判定面本卷内直接构造（与槽 12 同形）。 *)
Theorem tdt_audit_gate_level_combo_h3 : forall a : Level, level_le Lv0 a = true.
Proof.
  intros a. destruct a; reflexivity.
Qed.

(* 槽 23（:812 audit_gate_level_combo 槽4）：DTPT.DTPT.gate_pass thr1 H = true ——
   对角实例 thr1:=H：库内既有组合（DTPT.v llm_gate_pass_iff :1713 ＋ stdlib
   Qle_refl）⟹ 通过判据在门槛自等处恒开。 *)
Theorem tdt_audit_gate_level_combo_h4 : forall H : Q,
  DTPT.DTPT.gate_pass H H = true.
Proof.
  intros H. exact (proj2 (DTPT.DTPT.llm_gate_pass_iff H H) (Qle_refl H)).
Qed.

(* 槽 24（:825 audit_node_chain_combo 槽1）：(thr1 <= thr2)%Q ——
   Q 全序对角实例（与槽 20 同形，逐槽一条）。 *)
Theorem tdt_audit_node_chain_combo_h1 : forall thr : Q, (thr <= thr)%Q.
Proof.
  intros thr. apply Qle_refl.
Qed.

(* 槽 25（:826 audit_node_chain_combo 槽2）：audit_node t = true ——
   Lv2 层升见证实例域：宿主既有件 audit_node_lv2（:773）逐字直供。 *)
Theorem tdt_audit_node_chain_combo_h2 : forall (p m : DTPT.DTPT.Dig)
    (v : Evidence),
  audit_node (mkTrNode Lv2 p m v) = true.
Proof.
  exact audit_node_lv2.
Qed.

(* 槽 26（:827 audit_node_chain_combo 槽3）：DTPT.DTPT.gate_pass thr1 H = true ——
   对角实例（与槽 23 同形，逐槽一条）。 *)
Theorem tdt_audit_node_chain_combo_h3 : forall H : Q,
  DTPT.DTPT.gate_pass H H = true.
Proof.
  intros H. exact (proj2 (DTPT.DTPT.llm_gate_pass_iff H H) (Qle_refl H)).
Qed.

(* 槽 27（:1079 qlist_eqb_sound 槽1）：qlist_eqb l1 l2 = true ——
   单点表实例域：逐点判定吃宿主既有件 qeqb_refl（:1020）＋空表尾反射。 *)
Theorem tdt_qlist_eqb_sound_h1 : forall q : Q,
  qlist_eqb (q :: nil) (q :: nil) = true.
Proof.
  intros q. simpl. apply andb_true_intro. split.
  - apply qeqb_refl.
  - reflexivity.
Qed.

(* 槽 29（:1103 ev_eqb_cong_sound 槽1）：ev_eqb a b = true ——
   叶实例域（evNum 同值对）：叶判 Qeq_bool 吃宿主既有件 qeqb_refl。 *)
Theorem tdt_ev_eqb_cong_sound_h1 : forall q : Q,
  ev_eqb (evNum q) (evNum q) = true.
Proof.
  intros q. simpl. apply qeqb_refl.
Qed.

(* 槽 31（:1229 ev_eqb_raw_eq 槽1）：ev_eqb_raw a b = true ——
   叶实例域（Leibniz 叶判）：吃宿主既有件 Qraw_eqb_refl（:1169）。 *)
Theorem tdt_ev_eqb_raw_eq_h1 : forall q : Q,
  ev_eqb_raw (evNum q) (evNum q) = true.
Proof.
  intros q. simpl. apply Qraw_eqb_refl.
Qed.

(* 槽 32（:1378 ev_size_ge_2_pair 槽1）：le (S (S O)) (ev_size e) ——
   尺寸见证实例：e := evPair 叶×2，尺寸展开 3 ≥ 2（le_S＋le_n 双步）。 *)
Theorem tdt_ev_size_ge_2_pair_h1 :
  le (Datatypes.S (Datatypes.S O))
     (ev_size (evPair (evNum 0%Q) (evNum 0%Q))).
Proof.
  simpl. apply le_S. apply le_n.
Qed.

(* 槽 33（:1391 ev_pair_decomp_exact 槽1）：同尺寸门槛 ——
   尺寸见证实例（seq+num 异形叶对，逐槽一条）。 *)
Theorem tdt_ev_pair_decomp_exact_h1 :
  le (Datatypes.S (Datatypes.S O))
     (ev_size (evPair (evSeq nil) (evNum 0%Q))).
Proof.
  simpl. apply le_S. apply le_n.
Qed.

(* ========== 假设面自查（公理面自审附件，24 供给定理逐条打印） ========== *)
Print Assumptions tdt_neg_truth_at_neg_h1.
Print Assumptions tdt_diag_conj_spec_h1.
Print Assumptions tdt_tarski_via_renaming_h1.
Print Assumptions tdt_trLevel_geq_trans_h1.
Print Assumptions tdt_trLevel_geq_trans_h2.
Print Assumptions tdt_chain_ok_trans_h1.
Print Assumptions tdt_cv_lv_inj_h1.
Print Assumptions tdt_cv_lv_antisym_transport_h1.
Print Assumptions tdt_cv_lv_antisym_transport_h2.
Print Assumptions tdt_Tex_fiber_cast_h1.
Print Assumptions tdt_audit_node_mono_h1.
Print Assumptions tdt_audit_node_mono_h2.
Print Assumptions tdt_audit_gate_level_combo_h1.
Print Assumptions tdt_audit_gate_level_combo_h2.
Print Assumptions tdt_audit_gate_level_combo_h3.
Print Assumptions tdt_audit_gate_level_combo_h4.
Print Assumptions tdt_audit_node_chain_combo_h1.
Print Assumptions tdt_audit_node_chain_combo_h2.
Print Assumptions tdt_audit_node_chain_combo_h3.
Print Assumptions tdt_qlist_eqb_sound_h1.
Print Assumptions tdt_ev_eqb_cong_sound_h1.
Print Assumptions tdt_ev_eqb_raw_eq_h1.
Print Assumptions tdt_ev_size_ge_2_pair_h1.
Print Assumptions tdt_ev_pair_decomp_exact_h1.
