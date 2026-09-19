(* ============================================================ *)
(* UpAblT12_G13.v —— 假设消融战役 T12 扫尾席（sumf 零头 5 位之 G13 3 位）        *)
(* 辖区：G13_EvictFam.v EvictIdReq 节 sumf 接口面（L435/438/441 三位）            *)
(* 放电母本：sumd_*@UpReqSumD                                                   *)
(*                                                              *)
(* 目的：对 G13_EvictFam EvictIdReq 节的 req 求和接口面假设位逐条兑现消融定理：    *)
(*   假设位在具体有限和实例 sumf := sumd_sumf S enum 上全部无条件成立——          *)
(*   前提减薄为纯数据槽（枚举清单），假设位逐条消除。                            *)
(*                                                              *)
(* 主件清单（3 件，前缀 uabT12_，逐件标注被消融位坐标与放电件）：                 *)
(*    A1 uabT12_g13_sum_linear ←L435 sum_linear 放电 sumd_sum_linear@UpReqSumD:135 *)
(*    A2 uabT12_g13_sum_add    ←L438 sum_add    放电 sumd_sum_add@:161          *)
(*    A3 uabT12_g13_sum_ext    ←L441 sum_ext    放电 sumd_sum_ext@:112          *)
(*                                                              *)
(* 分级：3 件全 N1（库内放电件直连；证明体非平凡内容在放电件本体——               *)
(*   列表归纳链 sumd_list_sum_*@UpReqSumD，本件直连不注水）。                    *)
(*   本批辖区无 pos/zero_nonneg 面（节内仅 linear/add/ext 三槽，源注自证）。      *)
(*                                                              *)
(* 依赖（全部只读消费，原树零改）：CW_ConstructiveWorld_219、UpReqSumD。          *)
(*   语句面逐字抽取自现档 G13_EvictFam.v（两树逐字节同验：Main/Live_X           *)
(*   md5 同 fa1cbb4f，917 行；L435/438/441 三位 sed 直取），                    *)
(*   仅 sumf → sumd_sumf S enum 换实例位。原节 Let 别名（zero/plus/mult 等为    *)
(*   接口投影 @R RIS 位）在出节全参形下经实例消解同轨。                          *)
(*                                                              *)
(* 备注：语句面全集合层；公理面零新增；文尾逐件 Print Assumptions 收尾。          *)
(*   四关留痕：Live_X/attn/logs/g{1..4}-UpAblT12_G13.log。                      *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============ EvictIdReq（G13_EvictFam.v L414-442 接口面） ============ *)
(* 原 Context {R}{RIS} + S + sumf；出节全参形：R 显式（RIS 隐式位经类           *)
(* 实例解析），sumf 换 sumd_sumf S enum 实例。                                 *)

(* A1 ←L435 sum_linear（逐字：forall (a : R) (f : S -> R),
   req (sumf (fun s => mult a (f s))) (mult a (sumf f))） *)
Theorem uabT12_g13_sum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros R RIS S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* A2 ←L438 sum_add（逐字：forall f g : S -> R,
   req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g))） *)
Theorem uabT12_g13_sum_add :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    req (sumd_sumf S enum (fun s => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros R RIS S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* A3 ←L441 sum_ext（逐字：forall f g : S -> R,
   (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)） *)
Theorem uabT12_g13_sum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, req (f s) (g s)) ->
    req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabT12_g13_sum_linear.
Print Assumptions uabT12_g13_sum_add.
Print Assumptions uabT12_g13_sum_ext.
