(* ==========================================================================)
   abl_dtpt_dep_supply.v — DTPT_Bridge_Dep 前件槽残差供给卷
   使命：宿主 DTPT_Bridge_Dep.v 前件槽 1（:175，前件形 forall x : Q,
      In x l -> Qabs x <= B）的两条供给定理（tbd_ 前缀）：闭见证列 [0;0;2]
      上逐元素 Qabs 闭判定（tbd_dep_HB_wit_002，B := 2 为该列精确上确界）；
      P0 单表计算律（tbd_dep_HB_P0_single：In y (P0 [a]) -> Qabs y <=
      Qabs a，B := Qabs a 规范界项）。槽 1 无条件泛形非诚实界假设，供给取
      实例域/计算律两形态；宿主槽 2/3/4 前件由库内既有同形件覆盖
      （dtr_c2_sorted_P0/dtr_c2_P0_cons_ne/dtr_c2_Qle_0_1 等），本件不重复
      供给。
   依赖清单：Stdlib（QArith.QArith/QArith.Qabs/List）＋库件 DTPT（P0 定义＝
      DTPT.v:39、xq_Qle_bool_le＝DTPT.v:499，取 DTPT.DTPT 本尊短名；本件零
      Require DTPT_Bridge_Dep）；Require 顺序＝先 stdlib 后库序。
   对标行：DTPT 供给卷族体例（头注五字段/查重登记块/代入演示）；槽坐标＝
      DTPT_Bridge_Dep.v :175（槽 1-3）/:213（槽 4）。
   构造性注记：全件 Qed 真构造，零承认零公理零节变量；零新增数据类型（零
      Definition/Fixpoint/Inductive）；语句面零析取/零存在/零经典逻辑；
      Q 字面一律 %Q（防 Q_scope 劫持）；vm_compute 用面＝Qle_bool 闭式判定
      （宿主 DTPT.v:1291 同款在库配方）。
   编译配方（池 cwd＝dtpt_dep 编译池目录，路径绝对化）：source
      /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh &&
      unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c
      -native-compiler no -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
      abl_dtpt_dep_supply.v；验证＝EXIT=0＋日志零真错＋逐条 Print Assumptions
      全 Closed＋.vo 新于 .v，rocq check 复核；起编前确认无并发编译进程。
   查重登记：顶层名 2 枚全 tbd_ 新前缀，与库内既占 dtd_/dte_/dtr_/dtb_ 及
      同族 tdt_/tdg_/tdbg_/tbr_ 前缀零撞零别名转发；槽 1 一槽两条、槽 2/3/4
      零新件，4 槽总账零重复零遗漏；宿主文件零字节不动、零重编。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
Import ListNotations.

Require DTPT.
Import DTPT.DTPT.

Open Scope Q_scope.

(* ========== 残差槽 1 供给（:175 槽1 有界卫哨，实例域口径） ========== *)

(* 供给 1〔实例域闭式〕闭见证列 [0;0;2]（＝宿主树 sorted_wit_002（Rotation
   :1233）/库件 dtr_c2_sorted_wit_002 同列，槽 2 既有件同域互证）上的有界
   卫哨：逐元素 In 析取展开＋subst 后 Qabs 闭值判定（Qle_bool 反射，宿主
   DTPT.v:1291 同款配方）。B := 2 为该列精确上确界（元素 2 在列），界紧。 *)
Theorem tbd_dep_HB_wit_002 : forall x : Q, In x [0; 0; 2] -> Qabs x <= 2%Q.
Proof.
  intros x Hx. simpl in Hx.
  destruct Hx as [Hx | [Hx | [Hx | []]]]; subst x.
  - apply xq_Qle_bool_le. vm_compute. reflexivity.
  - apply xq_Qle_bool_le. vm_compute. reflexivity.
  - apply xq_Qle_bool_le. vm_compute. reflexivity.
Qed.

(* 供给 2〔计算律形〕P0 单表闭域全参族：P0 [a] 插入排序单表闭计算＝[a]
   （P0 定义 DTPT.v:39，insert_q 于空表无比较纯构造），元素唯一故 Qabs a
   即精确界（B := Qabs a 规范界项）——与槽 2/3 既有件同处 P0 闭域，
   三卫哨可同域一并代入（全参代入形见宿主供给约定）。 *)
Theorem tbd_dep_HB_P0_single : forall a y : Q,
  In y (P0 [a]) -> Qabs y <= Qabs a.
Proof.
  intros a y Hy.
  assert (E : P0 [a] = [a]) by reflexivity.
  rewrite E in Hy. simpl in Hy.
  destruct Hy as [Hy | []]. subst y.
  apply Qle_refl.
Qed.

(* ========== 逐条 Print Assumptions（公理面自查） ========== *)
Print Assumptions tbd_dep_HB_wit_002.
Print Assumptions tbd_dep_HB_P0_single.
