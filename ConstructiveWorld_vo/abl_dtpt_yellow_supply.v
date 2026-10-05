(* ==========================================================================)
   abl_dtpt_yellow_supply.v — DTPT_Truth 预留证书槽供给卷（5 槽闭合）
   使命：DTPT_Truth 36 槽中预留后行的 5 个证书构造槽（登记号 #28/#30/
      #34/#35/#36）逐槽一条供给定理（tdy_ 前缀）：槽前件在可判定实例域/
      集等价域的真化（Forall2 Qeq 证书逐点装配、ev_cong 构造子证书对角
      叶、枚举成员单见证），推导只吃已导出内容；Check 面代入演示（编译期
      真验证、零新增名）实证证书可接入宿主完备面——见文件尾演示段。
   依赖清单：Stdlib（QArith.QArith/List/Bool/Arith）＋库件 DTPT、
      DTPT_Truth（只读在册 .vo）；Require 顺序＝先 stdlib 后库序。
   对标行：DTPT 供给卷族体例（头注五字段/查重登记块/代入演示）；槽坐标＝
      DTPT_Truth.v :1091-:1513（登记号 #28/#30/#34/#35/#36）。
   构造性注记：全件 Qed 真构造，零承认零公理零节变量；纯 Set 层数据类型
      （Q/list Q/Evidence/Forall2/In 全宿主既有，零新增类型）；语句面零
      析取/零存在/零经典逻辑（Forall2 与 In 为宿主槽前件逐字形状）；nat
      层显式 Datatypes.S/O/Nat.sub（防 Q_scope 劫持）；Q 字面一律 0%Q。
   编译配方（池 cwd＝dtpt_yellow 编译池目录，路径绝对化）：source
      /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh &&
      unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c
      -native-compiler no -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
      abl_dtpt_yellow_supply.v；验证＝EXIT=0＋日志零真错＋逐条 Print
      Assumptions 全 Closed＋.vo 新于 .v，rocq check 复核。
   查重登记：顶层名 5 枚全 tdy_ 新前缀，与库内既占 tdt_/tdg_/tdbg_/tbr_/
      tbd_ 等前缀零撞零别名转发；5 槽逐槽一条、零重复零遗漏；宿主
      DTPT_Truth.v 零字节不动、零重编。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool Arith.
Import ListNotations.

Require DTPT.
Require DTPT_Truth.
Import DTPT_Truth.DTPT_Truth.

(* 槽 28（:1091 qlist_Qeq_complete 槽1）：槽前件 Forall2 Qeq l1 l2 ——
   证书逐点装配实例：单点表 cons/nil 双构造子，Qeq 前件显式代入
   （集等价域，零 Leibniz 面——存疑-③ 取值口径的落定形）。 *)
Theorem tdy_qlist_Qeq_complete_h1 : forall q1 q2 : Q,
  q1 == q2 -> Forall2 Qeq (q1 :: nil) (q2 :: nil).
Proof.
  intros q1 q2 H. constructor.
  - exact H.
  - constructor.
Qed.

(* 槽 30（:1114 ev_cong_eqb_complete 槽1）：槽前件 ev_cong a b ——
   构造子证书实例：ev_cong_num ＋ Qeq_refl 对角叶（同记录形对角域，
   ev_eqb_leibniz_gap 反例面 ：1133 系 Leibniz 方向，对本集等价证书面
   零阻断——存疑-③ 供给取值不依赖同值异形实例的实证）。 *)
Theorem tdy_ev_cong_eqb_complete_h1 : ev_cong (evNum 0%Q) (evNum 0%Q).
Proof.
  apply ev_cong_num. apply Qeq_refl.
Qed.

(* 槽 34（:1444 ev_enum_size_bound 槽1）：槽前件 In e (ev_enum n) ——
   枚举成员实例域：叶单见证 evNum 0%Q 于预算 1 层（宿主 ev_enum_num_0
   于 n:=O 一跳直供）。 *)
Theorem tdy_ev_enum_size_bound_h1 :
  In (evNum 0%Q) (ev_enum (Datatypes.S O)).
Proof.
  exact (ev_enum_num_0 Datatypes.O).
Qed.

(* 槽 35（:1512 ev_enum_pair_member 槽1）：槽前件 In a (ev_enum n) ——
   枚举成员实例域（与槽 34 异值异形逐槽一条）：evSeq nil 于预算 2 层
   （宿主 ev_enum_seq_nil 于 n:=S O 一跳直供）。 *)
Theorem tdy_ev_enum_pair_member_h1 :
  In (evSeq nil) (ev_enum (Datatypes.S (Datatypes.S O))).
Proof.
  exact (ev_enum_seq_nil (Datatypes.S Datatypes.O)).
Qed.

(* 槽 36（:1513 ev_enum_pair_member 槽2）：槽前件 In b (ev_enum (n − ev_size a))
   ——预算差成员实例域：a:=evNum 0%Q、n:=2、b:=evNum 0%Q；ev_size
   （evNum 叶）＝S O 与 Nat.sub 2 (S O)＝S O 按定义归约落预算 1 层
   （ev_enum_num_0 于 n:=O 一跳，转换检查承载）。 *)
Theorem tdy_ev_enum_pair_member_h2 :
  In (evNum 0%Q)
     (ev_enum (Nat.sub (Datatypes.S (Datatypes.S O))
                       (ev_size (evNum 0%Q)))).
Proof.
  exact (ev_enum_num_0 Datatypes.O).
Qed.

(* ========== 代入演示（Check 面：编译期真验证、零新增名） ========== *)
(* 演示一（槽 28 供给 → 宿主 :1091 完备面）：Forall2 证书代入 ⟹ 判定真 *)
Check (qlist_Qeq_complete (0%Q :: nil) (0%Q :: nil)
         (tdy_qlist_Qeq_complete_h1 0%Q 0%Q (Qeq_refl 0%Q))).
(* 演示二（槽 30 供给 → 宿主 :1114 完备面）：ev_cong 证书代入 ⟹ 判定真 *)
Check (ev_cong_eqb_complete (evNum 0%Q) (evNum 0%Q)
         tdy_ev_cong_eqb_complete_h1).
(* 演示三（槽 35＋36 供给 → 宿主 :1511 形状级生成规则）：两枚成员证书
   合并代入 ⟹ 拼接件于预算 3 层在册（a:=evSeq nil 尺寸 1、预算差 2−1＝1、
   右件预算层与槽 36 供给语句定义等值，转换承载） *)
Check (ev_enum_pair_member (Datatypes.S (Datatypes.S O)) (evSeq nil)
         (evNum 0%Q) tdy_ev_enum_pair_member_h1
         tdy_ev_enum_pair_member_h2).

(* ========== 假设面自查（公理面自审附件，5 供给定理逐条打印） ========== *)
Print Assumptions tdy_qlist_Qeq_complete_h1.
Print Assumptions tdy_ev_cong_eqb_complete_h1.
Print Assumptions tdy_ev_enum_size_bound_h1.
Print Assumptions tdy_ev_enum_pair_member_h1.
Print Assumptions tdy_ev_enum_pair_member_h2.
