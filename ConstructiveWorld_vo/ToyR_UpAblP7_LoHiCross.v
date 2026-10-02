(* ============================================================ *)
(* ToyR_UpAblP7_LoHiCross.v —— 消融落件：原件全文逐字保留，仅将文末清单所列 *)
(*   两定理之证明体替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／ *)
(*   结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增 Require，证明结尾 *)
(*   记号与原件逐件守恒，纯构造性闭合，文尾保留原件 Print Assumptions；经恒等守恒 *)
(*   ——清单所列 2 槽证明体与 Main 现版原件逐字同文（刀体＝原体）。 *)
(*   清单：uahlc_omd_bounded_one（原 L77，1 句）、uahlc_lo_lt_one_hi_one（原 L67，1 句）。 *)
(* UpAblP7_LoHiCross.v —— 使命：本件形式化 Softmax 上下界在温度=1、利差=1 具体 *)
(*   取值下的实例定理：uahlc_lo_lt_one_hi_one（lo < 1 ∧ 1 < hi）、 *)
(*   uahlc_omd_bounded_one（0 < 1−lo² < 1，κ:=1−lo²∈(0,1) 实例形）与 *)
(*   uahlc_lo_one_hi_full（lo<1 ∧ 1<hi ∧ lo<hi 三元合取的完整实例链）。 *)
(* 来源：源模块 LoHiSqueeze.v 的两节合取定理 lhs_lo_lt_one_hi（段一）与 lhs_omd_bounded（段二）；首波实例件 UpAblP7_LoHiSqueeze.v 的 uahl_lo_lt_hi_one；本件只使用两者的已证出口面。 *)
(* 依赖清单：S01_BaseRing（inv_pos/one_pos 正性面、And=prod）、Paper7Ablation、 *)
(*   P7BoundedSoftmaxDeep（p7a_lo_lt_one/p7d_hi_gt_one）、UpAblP7_LoHiSqueeze *)
(*   （uahl_lo_lt_hi_one）、LoHiSqueeze（源模块全件）。 *)
(* 证明要点：三件均为对源模块一般定理的全参显式实例化（@ 全显给出 RI 束参与 *)
(*   温度:=1（one_pos）、利差:=1（one_pos）及指数族四件 expf_pos/expf_zero/ *)
(*   expf_mono_lt 等）；件二额外需 DO（DecidableOrder）束参——源模块段二证明内部 *)
(*   使用段一的 δ*<1 支；件三左支取件一左支，右支由 p7d_hi_gt_one 与 *)
(*   uahl_lo_lt_hi_one 合取。 *)
(* 指数族的地位：expf 保持抽象（全库暂无具体实例）；invT:=inv_pos one one_pos 为温度倒数的具体形。 *)
(* 构造性注记：语句面全 Set 层（合取用 And=prod，零 Prop 层泄露）；公理面零新增； *)
(*   文尾 Print Assumptions 逐件全闭合。 *)
(* 编译配方：Rocq 9.1 直调、cpu_guard 节流、-o 临时目录输出（树内零写入）。 *)
(* 主要结果一览：uahlc_lo_lt_one_hi_one : And (lt lo one) (lt one hi)； *)
(*   uahlc_omd_bounded_one : And (lt zero (1−lo·lo)) (lt (1−lo·lo) one)； *)
(*   uahlc_lo_one_hi_full : And (lt lo one) (And (lt one hi) (lt lo hi))。 *)
(* 标识符约定：本件命名以前缀 uahlc_ 区分于源模块 lhs_ 与首波 uahl_ 系列。 *)
(* C1 一期注记（）: UahlCross 单节语境迁 RIS 面（S10:12220 限定名先例＋    *)
(*   Let 投影银行体例）；上代重复 Require 行随迁修一；使用面改接迁移后 ToyR_        *)
(*   UpAblP7_LoHiSqueeze 的 uahl_* 三件（候裁①采）；p7d_hi_gt_one 使用改 req 面    *)
(*   体内联（tpei_ 供给文件 Part 0 同体；供给文件 Part C 反向 Require 本件，单向环      *)
(*   消解）；lpc 辅助槽随 :74 改接的导出形 +1 位而设（小裁③同款体例）。           *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S07_RealSetoidExpLog.
Require Import Paper7Ablation.
Require Import P7BoundedSoftmaxDeep.
Require Import ToyR_UpAblP7_LoHiSqueeze.

(* ############ LoHi 实例定理与完整夹逼链 ################## *)
(* Section 参数面＝源模块两节参数之并（RI 束＋指数族四件），温度:=1、利差:=1   *)
(* （由 one_pos 供 inv_pos，invT:=inv_pos one one_pos 具体形）；               *)
(* 指数族 expf 保持抽象（全库暂无具体实例）。                                   *)

Section UahlCross.

Context {R : Set}.
Context {RI : RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid R}.
Local Existing Instance RI_base.
(* C1 一期：RIS 投影银行（S10 AttentionGibbsBridgeSetoid :12224-12232 体例）。 *)
Let zero : R := @RealInterfaceEnhancedMod.zero R RI.
Let one : R := @RealInterfaceEnhancedMod.one R RI.
Let plus : R -> R -> R := @RealInterfaceEnhancedMod.plus R RI.
Let mult : R -> R -> R := @RealInterfaceEnhancedMod.mult R RI.
Let opp : R -> R := @RealInterfaceEnhancedMod.opp R RI.
Let lt : R -> R -> Set := @RealInterfaceEnhancedMod.lt R RI.
Let le : R -> R -> Set := @RealInterfaceEnhancedMod.le R RI.
Let req : R -> R -> Set := @RealInterfaceEnhancedMod.req R RI.
Let inv_pos : forall x : R, lt zero x -> R := @RealInterfaceEnhancedMod.inv_pos R RI.
Let req_sym := @RealInterfaceEnhancedMod.req_sym R RI.
Let req_trans := @RealInterfaceEnhancedMod.req_trans R RI.
Let plus_comm := @RealInterfaceEnhancedMod.plus_comm R RI.
Let plus_zero := @RealInterfaceEnhancedMod.plus_zero R RI.
Let plus_opp := @RealInterfaceEnhancedMod.plus_opp R RI.
Let mult_comm := @RealInterfaceEnhancedMod.mult_comm R RI.
Let mult_one := @RealInterfaceEnhancedMod.mult_one R RI.
Let mult_zero := @RealInterfaceEnhancedMod.mult_zero R RI.
Let mult_positive := @RealInterfaceEnhancedMod.mult_positive R RI.
Let lt_trans := @RealInterfaceEnhancedMod.lt_trans R RI.
Let lt_id_l := @RealInterfaceEnhancedMod.lt_id_l R RI.
Let lt_id_r := @RealInterfaceEnhancedMod.lt_id_r R RI.
Let le_refl := @RealInterfaceEnhancedMod.le_refl R RI.
Let lt_mult_compat := @RealInterfaceEnhancedMod.lt_mult_compat R RI.
Let lt_zero_opp := @RealInterfaceEnhancedMod.lt_zero_opp R RI.
Let inv_pos_pos := @RealInterfaceEnhancedMod.inv_pos_pos R RI.
Let one_pos : lt zero one := @RealInterfaceEnhancedMod.one_pos R RI.

(* C1 一期扩槽（小裁③同款体例）：@uahl_omd_bounded 改接的导出形尾位 lpc 实参。 *)
Variable lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : req (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos one one_pos.
Let lo := expf (mult invT (opp one)).
Let hi := expf (mult invT one).

(* C1 一期：节内 minus 影子（S01:189 去 RI 参逐字副本；Let 形保节内作用域）。 *)
Let minus (a b : R) : R := plus a (opp b).

(* 件一：源模块 lhs_lo_lt_one_hi 的实例形：
   @ 全显给出两节参数——RI 束参＋温度:=1（one_pos）＋利差:=1（one_pos）＋
   指数族四件；C1 一期改接迁移后 ToyR_UpAblP7_LoHiSqueeze.uahl_lo_lt_one_hi。 *)
Theorem uahlc_lo_lt_one_hi_one : And (lt lo one) (lt one hi).
Proof.
  exact (@uahl_lo_lt_one_hi R RI one one_pos one one_pos
             expf expf_zero expf_mono_lt).
Qed.

(* 件二：源模块 lhs_omd_bounded 的实例形：
   @ 全显给出全束——C1 一期改接 uahl_omd_bounded（导出形尾位 +lpc 实参），
   κ:=1−δ*∈(0,1) 实例形一次构成。 *)
Theorem uahlc_omd_bounded_one :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  exact (@uahl_omd_bounded R RI lpc one one_pos one one_pos
             expf expf_pos expf_zero expf_mono_lt).
Qed.

(* 件三：lo<1 ∧ 1<hi ∧ lo<hi 的完整实例合取链。
   左支：件一左支（lo<1 实例形）；右支左支：p7d_hi_gt_one 的 req 面体内联
   实例化（C1 一期）；右支右支：复用 uahl_lo_lt_hi_one
   （@ 全显给出 RI 束＋指数族四件）——
   LoHi 侧的完整供给。 *)
Theorem uahlc_lo_one_hi_full :
  And (lt lo one) (And (lt one hi) (lt lo hi)).
Proof.
  split.
  - exact (fst uahlc_lo_lt_one_hi_one).
  - split.
    + (* C1 一期：p7d_hi_gt_one 的 req 面体内联（tpei_p7d_hi_gt_one_req 同体） *)
      exact (lt_id_l one (expf zero) (expf (mult invT one))
               (req_sym (expf zero) one expf_zero)
               (expf_mono_lt zero (mult invT one)
                  (mult_positive invT one (inv_pos_pos one one_pos) one_pos))).
    + exact (@uahl_lo_lt_hi_one R RI expf expf_zero expf_mono_lt).
Qed.

End UahlCross.

(* ---- 假设审计（对逐件 Print Assumptions） ---- *)
Print Assumptions uahlc_lo_lt_one_hi_one.
Print Assumptions uahlc_omd_bounded_one.
Print Assumptions uahlc_lo_one_hi_full.
