(* ============================================================ *)
(* UpAblP7_LoHiCross.v —— 温度=1、利差=1 实例上的 LoHi 双侧界与完整夹逼链 *)
(*                                                              *)
(* 数学使命：本件形式化 Softmax 上下界在温度=1、利差=1 具体取值下的实例定理：  *)
(*   uahlc_lo_lt_one_hi_one（lo < 1 ∧ 1 < hi）、uahlc_omd_bounded_one          *)
(*   （0 < 1−lo² < 1，κ:=1−lo²∈(0,1) 实例形）与 uahlc_lo_one_hi_full          *)
(*   （lo<1 ∧ 1<hi ∧ lo<hi 三元合取的完整实例链）。                            *)
(*                                                              *)
(* 来源：源模块 LoHiSqueeze.v 的两节合取定理 lhs_lo_lt_one_hi（段一）与           *)
(*   lhs_omd_bounded（段二）；首波实例件 UpAblP7_LoHiSqueeze.v 的               *)
(*   uahl_lo_lt_hi_one。本件只使用两者的已证出口面。                           *)
(*                                                              *)
(* 依赖清单：S01_BaseRing（inv_pos/one_pos 正性面、And=prod）、                 *)
(*   Paper7Ablation、P7BoundedSoftmaxDeep（p7a_lo_lt_one/p7d_hi_gt_one）、      *)
(*   UpAblP7_LoHiSqueeze（uahl_lo_lt_hi_one）、LoHiSqueeze（源模块全件）。        *)
(*                                                              *)
(* 证明要点：三件均为对源模块一般定理的全参显式实例化（@ 全显给出 RI 束参与      *)
(*   温度:=1（one_pos）、利差:=1（one_pos）及指数族四件 expf_pos/expf_zero/    *)
(*   expf_mono_lt 等）；件二额外需 DO（DecidableOrder）束参——源模块段二证明      *)
(*   内部使用段一的 δ*<1 支；件三左支取件一左支，右支由 p7d_hi_gt_one 与       *)
(*   uahl_lo_lt_hi_one 合取。                                                  *)
(*                                                              *)
(* 指数族的地位：expf 保持抽象（全库暂无具体实例）；invT:=inv_pos one one_pos  *)
(*   为温度倒数的具体形。                                                      *)
(*                                                              *)
(* 构造性注记：语句面全 Set 层（合取用 And=prod，零 Prop 层泄露）；公理面零     *)
(*   新增；文尾 Print Assumptions 逐件全闭合。                                  *)
(*                                                              *)
(* 编译配方：Rocq 9.1 直调、cpu_guard 节流、-o 临时目录输出（树内零写入）。     *)
(* 主要结果一览：                                                             *)
(*   uahlc_lo_lt_one_hi_one : And (lt lo one) (lt one hi)。                    *)
(*   uahlc_omd_bounded_one : And (lt zero (1−lo·lo)) (lt (1−lo·lo) one)。       *)
(*   uahlc_lo_one_hi_full : And (lt lo one) (And (lt one hi) (lt lo hi))。      *)
(* 标识符约定：本件命名以前缀 uahlc_ 区分于源模块 lhs_ 与首波 uahl_ 系列。       *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import Paper7Ablation.
Require Import P7BoundedSoftmaxDeep.
Require Import UpAblP7_LoHiSqueeze.
Require Import LoHiSqueeze.

(* ############ LoHi 实例定理与完整夹逼链 ################## *)
(* Section 参数面＝源模块两节参数之并（RI/DO 束＋指数族四件），温度:=1、利差:=1   *)
(* （由 one_pos 供 inv_pos，invT:=inv_pos one one_pos 具体形）；               *)
(* 指数族 expf 保持抽象（全库暂无具体实例）。                                   *)

Section UahlCross.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos one one_pos.
Let lo := expf (mult invT (opp one)).
Let hi := expf (mult invT one).

(* 件一：源模块 lhs_lo_lt_one_hi 的实例形：
   @ 全显给出两节参数——RI 束参＋温度:=1（one_pos）＋利差:=1（one_pos）＋
   指数族四件；源模块左支内部使用 p7a_lo_lt_one，
   右支使用 p7d_hi_gt_one，invT 正性由源模块自备。 *)
Theorem uahlc_lo_lt_one_hi_one : And (lt lo one) (lt one hi).
Proof.
  exact (@lhs_lo_lt_one_hi RI one one_pos one one_pos
             expf expf_pos expf_zero expf_mono_lt).
Qed.

(* 件二：源模块 lhs_omd_bounded 的实例形：
   @ 全显给出 RI/DO/两节参数全束——DO 束参为源模块段二所独有，
   温度/利差取 1、指数族四件全显；源模块段二证明内部使用段一
   的 δ*<1 支，κ:=1−δ*∈(0,1) 实例形一次构成。 *)
Theorem uahlc_omd_bounded_one :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  exact (@lhs_omd_bounded RI DO one one_pos one one_pos
             expf expf_pos expf_zero expf_mono_lt).
Qed.

(* 件三：lo<1 ∧ 1<hi ∧ lo<hi 的完整实例合取链。
   左支：件一左支（lo<1 实例形）；右支左支：源模块 hi 侧引理 p7d_hi_gt_one
   实例化；右支右支：复用 uahl_lo_lt_hi_one
   （@ 全显给出 RI 束＋指数族四件）——
   LoHi 侧的完整供给。 *)
Theorem uahlc_lo_one_hi_full :
  And (lt lo one) (And (lt one hi) (lt lo hi)).
Proof.
  split.
  - exact (fst uahlc_lo_lt_one_hi_one).
  - split.
    + exact (p7d_hi_gt_one one one_pos one one_pos expf expf_pos
               expf_zero expf_mono_lt).
    + exact (@uahl_lo_lt_hi_one RI expf expf_pos expf_zero expf_mono_lt).
Qed.

End UahlCross.

(* ---- 假设审计（对逐件 Print Assumptions） ---- *)
Print Assumptions uahlc_lo_lt_one_hi_one.
Print Assumptions uahlc_omd_bounded_one.
Print Assumptions uahlc_lo_one_hi_full.
