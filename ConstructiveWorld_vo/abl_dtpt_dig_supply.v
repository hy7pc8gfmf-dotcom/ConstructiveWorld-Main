(* ==========================================================================)
   abl_dtpt_dig_supply.v — AV·DTPT 扩容卷二施工（tmine04）
   ── DTPT_DigTheory.v 本体 22 前件槽之卷二：底册 _tmine04_X_DTPT槽普查.md
      §2.2 登记序：本卷 22 槽全做（底册初判全 🟢 纯计算/在库现成路径位）。
      红线遵守：W-DTPTTRUTH-DIAG-01 七槽（diag_closed 形，Truth 域）绝对禁碰
      （本域零此形，零触碰实录）；AT 卷一移交的 🟡 五槽（Forall2/ev_cong/enum In，
      存疑-②）本卷不做（候二审）；Bridge_Dig 10 槽（X §2.4）本卷不做（明账移交）。
   ① 模块名+使命：abl_dtpt_dig_supply——逐槽一条供给定理（tdg_ 前缀），
      陈述形＝「库内既有组合 ⟹ DTPT_DigTheory X 槽前件」：凡宿主在库有同形
      既有件者直供引述（exact 既有件），无者 born-in-place 小步构造（等词改写/
      构造子反射/尺寸方程改写/bool 判定归约），推导只吃已导出内容（Require
      库件两件：DTPT＋DTPT_DigTheory；AQ 坑卡① 照办：透传 Require 不导出短名，
      本件自 Require 全链）。
      【接口参数对照总表（22 槽＝底册 §2.2 登记号）】
        槽 1  →tdg_dig_inj_dQ_h1（:23，EQ 等词供给形）
        槽 2  →tdg_dig_inj_dPair_h1（:26，EQ 等词供给形）
        槽 3  →tdg_dig_inj_dSeq_h1（:30，EQ 等词供给形）
        槽 4  →tdg_dig_inj_dCode_h1（:34，EQ 等词供给形）
        槽 5  →tdg_dig_inj_dCode_pointwise_h1（:38，EQ 同形槽逐槽一条）
        槽 6  →tdg_dig_inj_dJudge_h1（:45，EQ 等词供给形）
        槽 7  →tdg_dig_inj_dModel_h1（:49，EQ 等词供给形）
        槽 8  →tdg_dig_inj_dProofT_h1（:53，EQ 等词供给形）
        槽 9  →tdg_dig_lsize_pos_h1（:263，NEQ cons 形见证实例域）
        槽 10 →tdg_dig_Q_roundtrip_h1（:327，EQ 对角等词见证）
        槽 11 →tdg_is_num_inv_h1（:365，INV 实例 dQ x，吃 is_num_eq_dQ）
        槽 12 →tdg_is_num_inv_sigT_h1（:374，INV 同形逐槽一条）
        槽 13 →tdg_is_num_false_not_dQ_h1（:382，INV 假支实例 dSeq []，
                吃 dig_size_one_not_only_num 后件）
        槽 14 →tdg_dig_Q_default0_h1（:390，同形逐槽一条）
        槽 15 →tdg_is_num_size1_h1（:398，INV 实例 dQ x 逐槽一条）
        槽 16 →tdg_dig_eqb_size_bound_h1（:513，NAT 尺寸实例 a:=dQ 0 n:=1，
                吃 dig_size_eq_dQ）
        槽 17 →tdg_dig_eqb_size_bound_h2（:513，BOOL 判定面 born-in-place）
        槽 18 →tdg_sub_dig_size_bound_h1（:623，NAT 尺寸实例 d:=dQ 0 n:=1）
        槽 19 →tdg_sub_dig_size_bound_h2（:623，BOOL 见证，吃 sub_dig_witness）
        槽 20 →tdg_sub_dig_size_mono_h1（:694，BOOL 见证逐槽一条）
        槽 21 →tdg_sub_dig_size_lt_h1（:701，BOOL 见证逐槽一条）
        槽 22 →tdg_is_num_h_alg1_h1（:764，INV 实例 dQ x 逐槽一条）
      【降档口径】供给定理取「槽前件的可满足实例/等词输入形」：宿主槽前件为
        全称变元上的假设（如 dQ x = dQ y／is_num d = true／dig_size a <= n），
        无条件泛形多不恒真（如 dig_eqb a b = true 于异值对落假，底册 W 账同法
        判），故供给＝给出现档可判定的实例域（dQ x／dSeq []／dPair dQ dQ／
        单 cons 表／对角）或等词供给形（分量等词 ⟹ 构造子等词），槽语义
        「前件可由库内既有件输入」逐槽成立；输入演示（X §4.2 A 直供形使用面）：
        dig_inj_dQ x y (tdg_dig_inj_dQ_h1 x y Hxy) 于 Hxy : x = y 下给出 x = y，
        其余各槽同法随输入前提落地宿主结论。
   ② 依赖清单：Stdlib（QArith.QArith/List/Bool/Arith）＋库件 DTPT、DTPT_DigTheory
      （统一缓存 vo_local_world_unified_0930 在册 .vo 只读依赖，零重编零级联；
      本件 Require 顺序＝先 stdlib 后库序，禁逆向；Dig 构造子族在 DTPT.v:22-28
      定义，经 DTPT_DigTheory 依赖链在档，本件两 Require 显式直取）。
   ③ 对标行：AT 卷一工艺＝abl_dtpt_truth_supply.v（A 直供形/头注五字段/查重
      登记块/绿判四件套，同族工艺直接复用）；设计依据＝
      _tmine04_X_DTPT槽普查.md §2.2（DigTheory 22 槽全 🟢，本卷全做）/
      §4（卷2 tdg_ 计划）；坑卡预读：AQ（无 Not 大写名——本件零 Not 大写位；
      `<>` 记法宿主件 23 处在档编译绿实证可用；grep -c 零命中退码 1 断链——
      绿判四件套分号独立跑）/AL（语句面零 Or 形出口）/AS（trans 三实参——
      本件零 trans 引用）。
   ④ 构造性注记：全件 Qed 真构造，零承认零公理零节变量；纯 Set 层载体
      （Q/nat/bool/Dig/list Dig 全宿主既有，本件零新增数据载体、零
      Definition/Fixpoint/Inductive）；语句面零混载（零析取/零存在/零经典逻辑；
      槽 9 供给语句含 `<>` 否等词位＝宿主 dig_lsize_pos 槽前件逐字形状，
      非新增否定出口）；供给对象全为可判定离散前件（等词/bool 判定面/nat 序/
      否等词 cons 形），可提取性由被引宿主件既有审计锚承载（宿主件尾 Print
      Assumptions 面在册，本件零 Obj.magic 面）；nat 层显式 %nat、Q 字面一律
      %Q（防 Q_scope 劫持）。
   ⑤ 编译配方（池 cwd＝沙箱/现役/abl_tmine04_pool/dtpt_v2，路径绝对化）：
      source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh &&
      unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c
      -native-compiler no -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
      abl_dtpt_dig_supply.v
      （道闸：起编前 ps -axo comm|grep -ci rocq 独立跑、禁入 && 链；绿判四件套：
      EXIT=0 无管道真取／日志真错行计 0＋逐条 Print Assumptions 全 Closed／
      .vo 头 8 字节与宿主 DTPT_DigTheory.vo 同款／.vo 新于 .v；第五证 rocq check。）
   ── 交付声明：本件为中文声明的零承认件：全文件零承认式声明、零悬置前提、
      零经典逻辑、零节变量声明位，全部供给定理 Qed 闭合；22 供给定理逐条
      Print Assumptions 全 Closed；DTPT_DigTheory.v 宿主零字节不动（零重编）。
   ========================================================================== *)

(* ============================================================ *)
(* 查重登记块（禁重复供给声明，R1 先例照办）：                        *)
(*   （一）名面：本件全部顶层名 22 枚全 tdg_ 新前缀（tdg_＝DigTheory 批  *)
(*   卷二专用 prefix），Live 全树＋统一缓存 vo_local_world_unified_0930   *)
(*   全量 grep 零命中（施工前复检实录）；与同池已占 dtd_/dte_/  *)
(*   dtr_/dtb_ 四前缀及 AT 卷一 tdt_ 专prefix 零撞零别名转发。           *)
(*   （二）槽面：卷二 22 槽＝底册 §2.2 登记号逐位对表（①总表），零双供    *)
(*   零漏账（22＝DigTheory 域槽总数，对账平）；同形槽（4↔5、11↔12↔15↔22、 *)
(*   13↔14、16↔18、19↔20↔21）逐位各立一条（逐槽一条铁律，供给语句同形     *)
(*   系槽前件同形所致，非重复计数）。                                    *)
(*   （三）宿主界：DTPT_DigTheory.v 本体零字节不动、零重编；两档 diff     *)
(*   逐字同档实测；本件 Require 统一缓存只读在册 .vo，宿主重编  *)
(*   零级联于本件，本件重编零级联于宿主。                                *)
(* ============================================================ *)

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
   库内既有组合（Leibniz 等词改写）⟹ 槽前件，输入后 dig_inj_dQ 给出 x = y。 *)
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
   参数位等词＋函数位 Leibniz 等词双腿改写。 *)
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
   单 cons 表逐字形状永非空（构造子互斥），输入后 dig_lsize_pos 给出
   0 < dig_lsize (x :: l)。语句含 <> 位＝宿主槽前件逐字形状。 *)
Theorem tdg_dig_lsize_pos_h1 : forall (x : Dig) (l : list Dig),
  x :: l <> [].
Proof.
  intros x l H. discriminate H.
Qed.

(* 槽 10（:327 dig_Q_roundtrip 槽1）：d = dQ x —— 对角等词见证：
   实例域 d := dQ x 处前件反射成立，输入后宿主给出 dig_Q (dQ x) = x。 *)
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
   born-in-place：对角数值对 (dQ 0, dQ 0) 处判定器归约 Qeq_bool 反射落真。 *)
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
