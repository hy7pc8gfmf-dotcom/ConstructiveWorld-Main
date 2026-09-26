(* ============================================================ *)
(* UpAblT10_S04RealExpLogConv.v —— 假设消融战役 T10a 批·翻案验证席      *)
(* 辖区：T8a 勘误表 E-3 指认坐标 S04_RealExpLogConv.v:1388 weak_trich 槽 *)
(* 消融母本：real_weak_trich@S07_RealSetoidExpLog.v:5719（全绿 Qed 收口  *)
(*   L5866；本轮探针后 Check 实测签名零参直给，见 g1 留痕）              *)
(*                                                                      *)
(* 目的：普查对 S04:1388 weak_trich 判 W（三分律墙=rLPO 族）与源注       *)
(*   L1386-87「Real 层 real_weak_trich 已证供给，非 LPO」冲突。本件实测  *)
(*   覆盖面：槽语句形 forall x y, 蕴含链 ¬lt x y -> ¬lt y x -> Id x y    *)
(*   在实例映射 R:=Real、lt:=real_lt、Id:=real_eq 下被绿件整槽覆盖——     *)
(*   逐位对表：参序 x y 同；前提位一 ¬(lt x y)↔¬(real_lt x y) 同位；     *)
(*   前提位二 ¬(lt y x)↔¬(real_lt y x) 同位；结论 Id x y↔real_eq x y。   *)
(*   抽象接口面（R/lt/Id 无解码器）W 注记维持；实例供给面翻 N。           *)
(*                                                                      *)
(* 主件清单（4 件，前缀 uabt10_）：                                      *)
(*   件1 uabt10_weak_trich_real ←槽形 Real 实例放电（E654 直给式；       *)
(*       母件一步直喂；分级 N1 零施工——库内已有等价件，登记坐标即        *)
(*       S07:5719，本件为翻案登记形）                                    *)
(*   件2 uabt10_eq_not_lt_l     ←反向紧致左向：real_eq x y -> ¬real_lt   *)
(*       x y；导出链 real_eq_sym→real_lt_id_r→real_lt_irrefl 三步        *)
(*       （分级 N2 有限消去链）                                          *)
(*   件3 uabt10_eq_not_lt_r     ←反向紧致右向（id_l 运河，对称形）       *)
(*   件4 uabt10_weak_trich_iff  ←双向同义打包：槽形 ⟺ real_eq（Set 层    *)
(*       prod 积）；此件证明槽结论在实例面恰为 setoid 等式，非弱化降档   *)
(*                                                                      *)
(* 分级表：件1 N1（零施工直给）；件2/3 N2（导出链三步）；件4 N2（组装）  *)
(*   全件非 T：件2/3/4 为库内原无的等式-双非lt 同义刻画（全库 grep       *)
(*   real_eq 与双 Not 合取刻画件零命中）。                               *)
(*                                                                      *)
(* 依赖（全部只读消费，原树零改）：S02_CauchyComplete（real_lt_irrefl    *)
(*   L2400、real_eq_sym L2238）、S07_RealSetoidExpLog（绿件 L5719、      *)
(*   RealSetoid.real_lt_id_l/r L449/L456）。                             *)
(* 语句面全 Set 层（real_lt/real_eq : Real -> Real -> Set 实测；Not 用   *)
(*   S01 基座层）；公理面零新增；文尾逐件 Print Assumptions 收尾。        *)
(* 四关留痕：Live_X/attn/logs/g{1..4}-UpAblT10_S04RealExpLogConv.*      *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.

(* 件1 ←S04_RealExpLogConv.v L1388 槽形（逐字换实例 R:=Real,lt:=real_lt,Id:=real_eq） *)
Theorem uabt10_weak_trich_real : forall x y : Real,
  Not (real_lt x y) -> Not (real_lt y x) -> real_eq x y.
Proof.
  exact real_weak_trich.
Qed.

(* 件2 ←反向紧致（左）：等式消去同向 lt（real_lt_id_r: eq b c -> lt a b -> lt a c，取 c:=a） *)
Theorem uabt10_eq_not_lt_l : forall x y : Real,
  real_eq x y -> Not (real_lt x y).
Proof.
  intros x y Hxy Hlt.
  exact (real_lt_irrefl x
          (RealSetoid.real_lt_id_r x y x (real_eq_sym x y Hxy) Hlt)).
Qed.

(* 件3 ←反向紧致（右）：等式消去反向 lt（real_lt_id_l: eq a b -> lt b c -> lt a c，取 c:=a） *)
Theorem uabt10_eq_not_lt_r : forall x y : Real,
  real_eq x y -> Not (real_lt y x).
Proof.
  intros x y Hxy Hyx.
  exact (real_lt_irrefl x (RealSetoid.real_lt_id_l x y x Hxy Hyx)).
Qed.

(* 件4 ←双向同义打包：弱三分槽形 ⟺ setoid 等式（Set 层 prod 积） *)
Theorem uabt10_weak_trich_iff : forall x y : Real,
  prod
    (Not (real_lt x y) -> Not (real_lt y x) -> real_eq x y)
    (real_eq x y -> prod (Not (real_lt x y)) (Not (real_lt y x))).
Proof.
  intros x y.
  split.
  - exact (uabt10_weak_trich_real x y).
  - intros H.
    split.
    + exact (uabt10_eq_not_lt_l x y H).
    + exact (uabt10_eq_not_lt_r x y H).
Qed.

(* 文尾审计口：逐件 Print Assumptions（G2 全 Closed 口径） *)
Print Assumptions uabt10_weak_trich_real.
Print Assumptions uabt10_eq_not_lt_l.
Print Assumptions uabt10_eq_not_lt_r.
Print Assumptions uabt10_weak_trich_iff.
