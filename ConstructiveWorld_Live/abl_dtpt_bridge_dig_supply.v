(* ==========================================================================)
   abl_dtpt_bridge_dig_supply.v — DTPT_Bridge_Dig 前件槽供给卷二另半（10 槽全做）
   使命：逐槽一条供给定理（tdbg_ 前缀），陈述形＝「库内既有组合 ⟹
      DTPT_Bridge_Dig 槽前件」。供给形三类：实例域直供 6 条＋计算律/判定
      归约在本卷内直接构造 2 条＋等词供给形 2 条。宿主槽前件为全称变元上
      的假设，无条件泛形多不恒真（宿主件内反例在档），故逐槽给出现档可
      判定实例域（dQ x/dPair dQ dQ/门对 [3;0;1]×5/对角）——逐槽对照见
      各定理前注；宿主结论方向不桥假命题（dig_dec 只做可靠下近似）。
   依赖清单：Stdlib（QArith.QArith/List/Bool/Arith）＋库件 DTPT、
      DTPT_DigTheory、DTPT_Extract、DTPT_Bridge_Dig（只读在册 .vo）；
      Require 顺序＝先 stdlib 后库序，桥面名由第四 Require 显式直取。
   对标行：DTPT 供给卷族体例（头注五字段/查重登记块/代入演示）；槽坐标＝
      DTPT_Bridge_Dig.v :54-:215（登记号 1-10，见各定理前注）。
   构造性注记：全件 Qed 真构造，零承认零公理零节变量；纯 Set 层数据类型
      （Q/nat/bool/Dig/list Q 全宿主既有，零新增类型）；语句面零析取/零
      存在/零经典逻辑/零否定出口；可提取性由被引宿主件既有提取面承载；
      nat 层显式 %nat、Q 字面一律 %Q（防 Q_scope 劫持）。
   编译配方（池 cwd＝dtpt_v2b 编译池目录，路径绝对化）：source
      /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh &&
      unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c
      -native-compiler no -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
      abl_dtpt_bridge_dig_supply.v；验证＝EXIT=0＋日志零真错＋逐条 Print
      Assumptions 全 Closed＋.vo 新于 .v，rocq check 复核。
   查重登记：顶层名 10 枚全 tdbg_ 新前缀，与库内既占前缀族零撞零别名转发；
      10 槽逐槽一条、零重复零遗漏；宿主 DTPT_Bridge_Dig.v 零字节不动。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool Arith.
Import ListNotations.

Require DTPT.
Require DTPT_DigTheory.
Require DTPT_Extract.
Require DTPT_Bridge_Dig.
Import DTPT.DTPT.
Import DTPT_DigTheory.DTPT_DigTheory.
Import DTPT_Extract.DTPT_Extract.
Import DTPT_Bridge_Dig.DTPT_Bridge_Dig.

Open Scope Q_scope.

(* ========== 批一：判定器/子项序族五槽（#1-5） ========== *)

(* 槽 1（DTPT_Bridge_Dig.v:54 is_num_size1_set 槽1）：is_num d = true ——
   数值域实例 d := dQ x：宿主既有件 is_num_eq_dQ（DTPT_DigTheory.v:355）直供。
   代入后 is_num_size1_set 给出尺寸 1 见证对。 *)
Theorem tdbg_is_num_size1_set_h1 : forall x : Q, is_num (dQ x) = true.
Proof.
  exact is_num_eq_dQ.
Qed.

(* 槽 2（:77 sub_dig_size_mono_set 槽1）：sub_dig a d = true —— 真子项见证
   实例：吃宿主定义性见证 sub_dig_witness（DTPT_DigTheory.v:604）直供。
   代入后 sub_dig_size_mono_set 给出 leb 左支或右支 nat 判定见证。 *)
Theorem tdbg_sub_dig_size_mono_set_h1 :
  sub_dig (dQ 0%Q) (dPair (dQ 0%Q) (dQ 0%Q)) = true.
Proof.
  exact sub_dig_witness.
Qed.

(* 槽 3（:90 sub_dig_size_dec_true 槽1）：sub_dig a d = true —— 同形槽
   逐槽一条（同吃 sub_dig_witness）。代入后 sub_dig_size_dec_true 给出
   Nat.leb (dig_size a) (dig_size d) = true。 *)
Theorem tdbg_sub_dig_size_dec_true_h1 :
  sub_dig (dQ 0%Q) (dPair (dQ 0%Q) (dQ 0%Q)) = true.
Proof.
  exact sub_dig_witness.
Qed.

(* 槽 4（:100 dig_eqb_size_dec_true 槽1）：dig_eqb a b = true —— bool 判定面
   本卷内直接构造：对角数值对 (dQ 0, dQ 0) 处判定器归约 Qeq_bool 反射落真。
   代入后 dig_eqb_size_dec_true 给出尺寸 leb 真支。 *)
Theorem tdbg_dig_eqb_size_dec_true_h1 : dig_eqb (dQ 0%Q) (dQ 0%Q) = true.
Proof.
  reflexivity.
Qed.

(* 槽 5（:112 dig_Q_roundtrip_set 槽1）：d = dQ x —— 对角等词见证：
   实例域 d := dQ x 处前件反射成立（宿主只取 d = dQ x 向，本件同向
   不越界）。代入后 dig_Q_roundtrip_set 给出 dQeqT (dig_Q (dQ x)) x。 *)
Theorem tdbg_dig_Q_roundtrip_set_h1 : forall x : Q, dQ x = dQ x.
Proof.
  intros x. reflexivity.
Qed.

(* ========== 批二：门控全链族两槽（#6-7） ========== *)

(* 槽 6（:146 gate_pass_QleT 槽1）：gate_pass t h = true —— 金标准门对实例
   （阈值 1、H 0，宿主 §2 样例表首行）：吃宿主行为锚 u12_gate_pass_t1_h0
   （DTPT_Extract.v:45）直供。代入后 gate_pass_QleT 给出 dQleT 0 1 证书。
   反例面：gate_pass 1 2 = false（u12_gate_pass_t1_h2 在档），故实例域
   供给为唯一诚实形。 *)
Theorem tdbg_gate_pass_QleT_h1 : gate_pass 1%Q 0%Q = true.
Proof.
  exact u12_gate_pass_t1_h0.
Qed.

(* 槽 7（:160 u12_gate_chain_QleT 槽1）：u12_gate_chain l t = true —— 双门
   放行实例（乱序列 [3;0;1]、阈值 5，宿主 §3 行为锚）：吃
   u12_gate_chain_301_t5（DTPT_Extract.v:133）直供。代入后
   u12_gate_chain_QleT 给出双门 dQleT 证书对（§8 桥面
   all_B7 使用链之供给需求位）。 *)
Theorem tdbg_u12_gate_chain_QleT_h1 : u12_gate_chain [3%Q;0%Q;1%Q] 5%Q = true.
Proof.
  exact u12_gate_chain_301_t5.
Qed.

(* ========== 批三：dig_dec 双判族三槽（#8-10） ========== *)

(* 槽 8（:200 dig_dec_sound 槽1）：a = b —— 等词供给形：Q 值等词 ⟹
   构造子等词（Leibniz 两支并列改写）。代入后 dig_dec_sound 给出
   dig_dec (dQ x) (dQ y) = true（可靠性面）。 *)
Theorem tdbg_dig_dec_sound_h1 : forall x y : Q, x = y -> dQ x = dQ y.
Proof.
  intros x y H. rewrite H. reflexivity.
Qed.

(* 槽 9（:207 dig_dec_shape 槽1）：dig_dec a b = true —— 对角数值对实例
   本卷内直接构造（形状＋尺寸双判落真）。代入后 dig_dec_shape 给出
   dig_tag (dQ 0) = dig_tag (dQ 0)。 *)
Theorem tdbg_dig_dec_shape_h1 : dig_dec (dQ 0%Q) (dQ 0%Q) = true.
Proof.
  reflexivity.
Qed.

(* 槽 10（:215 dig_dec_size 槽1）：dig_dec a b = true —— 宿主 §5 边界见证
   实例（dPair (dQ 0)(dQ 0) 与 dPair (dQ 1)(dQ 0) 同形同尺寸而 Leibniz
   不等——完备性反例对）：吃宿主 dig_dec_not_eq_witness（:225）前件合取支
   直供。代入后 dig_dec_size 给出两码 dig_size 相等；此实例并实录
   「dig_dec = true 不保 Leibniz 相等」之宿主 S5 边界语义。 *)
Theorem tdbg_dig_dec_size_h1 :
  dig_dec (dPair (dQ 0%Q) (dQ 0%Q)) (dPair (dQ 1%Q) (dQ 0%Q)) = true.
Proof.
  exact (proj1 dig_dec_not_eq_witness).
Qed.

(* ========== 假设面自查（公理面自审附件，10 供给定理逐条打印） ========== *)
Print Assumptions tdbg_is_num_size1_set_h1.
Print Assumptions tdbg_sub_dig_size_mono_set_h1.
Print Assumptions tdbg_sub_dig_size_dec_true_h1.
Print Assumptions tdbg_dig_eqb_size_dec_true_h1.
Print Assumptions tdbg_dig_Q_roundtrip_set_h1.
Print Assumptions tdbg_gate_pass_QleT_h1.
Print Assumptions tdbg_u12_gate_chain_QleT_h1.
Print Assumptions tdbg_dig_dec_sound_h1.
Print Assumptions tdbg_dig_dec_shape_h1.
Print Assumptions tdbg_dig_dec_size_h1.
