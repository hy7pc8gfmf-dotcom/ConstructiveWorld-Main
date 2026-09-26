(* ============================================================ *)
(* UpAblD1S16_UpReqMixTime.v —— 本件形式化 UpReqAttnMixTime 余量 12 位语句的接口 *)
(*   封装供给：对任意老层实接口实例 RI，恒可给出 12 位条件形之全部字段。        *)
(*                                                                              *)
(* 依赖：CW_ConstructiveWorld_219——S01 老层接口 RealInterfaceEnhanced，及其     *)
(*   StateSpace、SumOver、lt、le、one、one_pos、szero 等字段与常元；            *)
(*   零 Require 源模块 UpReqAttnMixTime，字段序以源模块声明序为准。                 *)
(* 对标：stdlib——恒等类型 Id 的依赖消去、Or 注入 inl、lt_le_iff 换向。          *)
(* 构造性注记：载体为 Type 层归纳类型 uabd1s16_fmt_pack12；节内以 Context        *)
(*   {RI : RealInterfaceEnhanced} 承载，出节即为全称条件形；零公理零承认，      *)
(*   Print Assumptions 全 Closed；随树可提取。                                  *)
(* 编译配方：Rocq 9.1 coqc 直调，cpu_guard 包裹，-o 输出临时目录，树内零写入。   *)
(*                                                                              *)
(* 12 位语句（字段序＝源模块声明序）：                                            *)
(*   接口三字段：SS : StateSpace RI，SO : SumOver RI SS（构造子显式参数）；      *)
(*   数据九字段：enum（状态枚举）、enum_nonempty（枚举非空）、temp（温度）、     *)
(*   temp_pos（温度为正）、Delta（步长）、Delta_pos（步长为正）、z（评分函数）、 *)
(*   z_lb（评分下界：对任意 s s' : S，le (opp Delta) (z s s')）、z_ub（评分上界： *)
(*   对任意 s s' : S，le (z s s') Delta）。                                      *)
(*                                                                              *)
(* 数据供给（取单点态空间、单位温度与单位步长）：                               *)
(*   enum            := cons szero nil（单点枚举，szero 为 StateSpace 字段）    *)
(*   enum_nonempty   := 单点枚举构造元不交（独立引理 uabd1s16_fmt_enum_ne）      *)
(*   temp / Delta    := one（接口幺元）                                         *)
(*   temp_pos / Delta_pos := one_pos（幺元为正）                                *)
(*   z               := 零函数（fun _ _ => zero）                               *)
(*   z_lb            := le (opp one) zero，由 lt_zero_opp one one_pos 经        *)
(*                      lt_le_iff 与 Or 注入 inl 推得                           *)
(*   z_ub            := le zero one，由 one_pos 经 lt_le_iff 与 inl 推得        *)
(*                                                                              *)
(* 一致性注记：供给取 Delta := one，故 z_lb/z_ub 的界 opp one 与 one 恰为        *)
(*   opp Delta 与 Delta；零函数取值 zero 落于该界内由 one_pos 保证。             *)
(*                                                                              *)
(* 形态注记：老层 RealInterfaceEnhanced 全树无具体实例——库内在册者为 Setoid     *)
(*   姊妹类实例 RealEnhancedReal，且 Setoid→RI 反向转换不在册；故本件以 RI 全称  *)
(*   条件形供给，不依赖任何具体实例，此即如实形态。                             *)
(*                                                                              *)
(* 可达锚注明：uabd1s16_fmt_anchor_setoid 具名声明 Setoid 姊妹类实例的类型实存， *)
(*   属可达面注明，非供给件。                                                   *)
(*                                                                              *)
(* 出节全参形：uabd1s16_fmt_pack12_supplied_global 显式量化 RI，供下游按任意    *)
(*   老层接口实例取用。                                                         *)
(*                                                                              *)
(* 注：可达锚以限定名 RealInterfaceEnhancedMod.RealEnhancedReal 引用，          *)
(*   避免其记录字段名与 S01 老层同名投影相互遮蔽（详见节首注记）。              *)
(*                                                                              *)
(* 节内实例注记：Local Existing Instance RI_base 使节内类型类字段解析可用；     *)
(*   出节后由全称条件形显式量化 RI，不依赖节内隐式实例机制。                    *)
(*                                                                              *)
(* 应用面：MixTime 余量 12 位语句的下游模块可依本条件形逐位代入；               *)
(*   数据九字段的具体值对任意 RI 实例一致，接口三字段由调用方给出。             *)
(*                                                                              *)
(* 边界注记：本件不给出老层 RI 的具体实例构造；此类实例在库内的存在性与         *)
(*   Setoid→RI 反向转换的可用性属上游命题，非本件供给面。                       *)
(*                                                                              *)
(* 注：z_lb 与 z_ub 为逐点陈述（对任意 s s' : S），供给件逐点一致成立。          *)
(*                                                                              *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
(* 注记：本件不导入 RealInterfaceEnhancedMod——其字段名（lt/le/zero/opp 等） *)
(*   会遮蔽 S01 老层同名投影，裸名必须落 S01 老层面；                       *)
(*   可达锚注明件以限定名引用。 *)

(* ============ §1 12 位语句的接口封装条件形（节内 Context，出节全称） ============ *)
(* 字段序＝源模块声明序：SS/SO 接口字段为构造子显式参数；数据九字段逐一对应。 *)

Section UabD1S16Fmt.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Inductive uabd1s16_fmt_pack12 : Type :=
| uabd1s16_fmt_pack12_intro :
    forall (SS : StateSpace RI) (SO : SumOver RI SS),
      forall (enum : list S),
        Not (Id enum nil) ->
        forall (temp : R),
          lt zero temp ->
          forall (Delta : R),
            lt zero Delta ->
            forall (z : S -> S -> R),
              (forall s s' : S, le (opp Delta) (z s s')) ->
              (forall s s' : S, le (z s s') Delta) ->
              uabd1s16_fmt_pack12.

(* ---- 枚举非空供给（独立引理：单点枚举构造元不交） ---- *)
(* 注记：S01 幺等 Id 非原始等号，discriminate 不识别； *)
(*   以依赖消去闭合——指标 nil 给空型、cons 给单型，id_refl 分支落单型。   *)

Lemma uabd1s16_fmt_enum_ne :
  forall SS : StateSpace RI, Not (Id (cons szero nil) nil).
Proof.
  intros SS H.
  exact (match H in Id _ y
         return (match y return Set with
                 | nil => Empty_set
                 | cons _ _ => unit
                 end)
         with
         | id_refl => tt
         end).
Qed.

(* ---- 供给定理：对任意老层接口实例给出数据九字段 ---- *)

Theorem uabd1s16_fmt_pack12_supplied :
  forall (SS : StateSpace RI) (SO : SumOver RI SS), uabd1s16_fmt_pack12.
Proof.
  intros SS SO.
  exact (uabd1s16_fmt_pack12_intro SS SO
           (cons szero nil)
           (uabd1s16_fmt_enum_ne SS)
           one one_pos
           one one_pos
           (fun _ _ : S => zero)
           (fun (_ _ : S) =>
              lt_le_iff (opp one) zero (inl (lt_zero_opp one one_pos)))
           (fun (_ _ : S) => lt_le_iff zero one (inl one_pos))).
Qed.

End UabD1S16Fmt.

(* ============ §2 可达锚注明（具名类型声明，非供给件） ============ *)
(* RealEnhancedReal＝Setoid 姊妹类（req 载体层）在库具体实例的类型实存声明；      *)
(* Setoid→RI 反向转换库内不在册，老层 RI 具体实例仍为零——本件条件形即如实形态。  *)

Definition uabd1s16_fmt_anchor_setoid := RealInterfaceEnhancedMod.RealEnhancedReal.

Check uabd1s16_fmt_anchor_setoid.

(* ============ §3 出节全参形 ============ *)

Theorem uabd1s16_fmt_pack12_supplied_global :
  forall (RI : RealInterfaceEnhanced) (SS : StateSpace RI) (SO : SumOver RI SS),
    @uabd1s16_fmt_pack12 RI.
Proof.
  intros RI SS SO.
  exact (uabd1s16_fmt_pack12_supplied (RI := RI) SS SO).
Qed.

(* ============ §4 假设面审计 ============ *)

Print Assumptions uabd1s16_fmt_pack12_supplied.
Print Assumptions uabd1s16_fmt_pack12_supplied_global.
Print Assumptions uabd1s16_fmt_enum_ne.
Print Assumptions uabd1s16_fmt_anchor_setoid.
