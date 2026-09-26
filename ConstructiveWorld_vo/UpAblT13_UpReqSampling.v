(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(*   位1 L135 abs_ge_zero_req（abs 面，AbsLeId 直接供给）                              *)
(*   位2 L136 lt_plus_compat_lt_le_h（fa53 面）                                   *)
(*   位3 L737 bs_abs（abs 面双槽同构，=L135 同语句）                               *)
(*   位4 L738 bs_lpc（fa53 面双槽同构，=L136 同语句）                              *)
(* 被消融位语句（现档逐字）：                                                      *)
(*   L135  Variable abs_ge_zero_req : forall a : R, le zero a -> req (abs a) a.    *)
(*   L136-137 Variable lt_plus_compat_lt_le_h : forall a b c d : R,                *)
(*           lt a b -> le c d -> lt (plus a c) (plus b d).                         *)
(*   L737  Variable bs_abs : forall a : R, le zero a -> req (abs a) a.             *)
(*   L738  Variable bs_lpc : forall a b c d : R,                                   *)
(*           lt a b -> le c d -> lt (plus a c) (plus b d).                         *)
(* 实例化消解源版本：fa53_lt_plus_compat_lt_le_dec@fa53_compat_abs.v:103（lpc 两件）；       *)
(*   ali_abs_ge_zero_id@AbsLeId.v:50（abs 两件，构造体=fa53 件3 三分+归谬）。        *)
(* 消融形（诚实登记）：原槽 RIS 接口级不可导（E-STAGING-Firewall-3 位注：           *)
(*   消融须带包），减薄为可判定序数据槽——RI0 典范载体 + DO0 可判定序数据槽，        *)
(*   req 经装配桥 tsi_rie_setoid（req 取 Id 幺等）；载体实例供给形态：              *)
(*   抽象载体上不实例化消解，典范载体上成立（T2b 节7 同形先例）。                          *)
(* 分级：四位全 N1（库内实例化消解件直接供给；abs 面经装配桥 req=Id 定义性转换）。             *)
(* 依赖（只读使用，原树零改）：CW_ConstructiveWorld_219、fa53_compat_abs、          *)
(*   AbsLeId、TempSoftmaxInstantiation。                                           *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import fa53_compat_abs.
Require Import AbsLeId.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13Usamp.

Context {RI0 : RealInterfaceEnhanced}.
Context {DO0 : DecidableOrder RI0}.

(* 位1 ←L135 abs_ge_zero_req（语句逐字，名换前缀） *)
Theorem uabT13_usamp_abs_ge_zero_req :
  forall a : @S01_BaseRing.R RI0, le zero a -> req (abs a) a.
Proof.
  intros a Ha.
  exact (@ali_abs_ge_zero_id RI0 DO0 a Ha).
Qed.

(* 位2 ←L136 lt_plus_compat_lt_le_h（语句逐字，名换前缀） *)
Theorem uabT13_usamp_lpc_h :
  forall a b c d : @S01_BaseRing.R RI0,
    lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Qed.

(* 位3 ←L737 bs_abs（=L135 同语句双槽同构，本件 Corollary 同构禁双计数） *)
Corollary uabT13_usamp_bs_abs :
  forall a : @S01_BaseRing.R RI0, le zero a -> req (abs a) a.
Proof.
  exact uabT13_usamp_abs_ge_zero_req.
Qed.

(* 位4 ←L738 bs_lpc（=L136 同语句双槽同构） *)
Corollary uabT13_usamp_bs_lpc :
  forall a b c d : @S01_BaseRing.R RI0,
    lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  exact uabT13_usamp_lpc_h.
Qed.

End UabT13Usamp.

(* ---- 收尾段（逐件假设面打印，判读全闭） ---- *)
Print Assumptions uabT13_usamp_abs_ge_zero_req.
Print Assumptions uabT13_usamp_lpc_h.
Print Assumptions uabT13_usamp_bs_abs.
Print Assumptions uabT13_usamp_bs_lpc.
