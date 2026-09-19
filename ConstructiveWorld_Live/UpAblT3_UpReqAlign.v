(* ============================================================ *)
(* UpAblT3_UpReqAlign.v —— 假设消融战役 T3 批·席 a（T1a 移交同根余量前 25 位之 13 位） *)
(* 辖区：UpReqAlign.v sumf 接口面（求和假设位四节），放电母本 sumd_*@UpReqSumD *)
(*                                                              *)
(* 目的：对 UpReqAlign 四节（ReqAlignCore/ReqKLProjection/              *)
(*   ReqNaturalGradient/ReqPPORatio）的 sumf 接口面假设位逐条兑现消融定理： *)
(*   假设位（对任意 sumf 算子的接口字段假定）在具体有限和实例            *)
(*   sumf := sumd_sumf S enum（enum 列表和，UpReqSumD 放电机械）上       *)
(*   全部无条件成立——前提减薄为纯数据槽（枚举清单），假设位逐条消除。     *)
(*                                                              *)
(* 主件清单（13 件，前缀 uabT3_，逐件标注被消融位坐标与放电件）：         *)
(*   §A ReqAlignCore（L54-74）：                                      *)
(*    A1 uabT3_reqalign_sum_ext        ←L62 sum_ext   放电 sumd_sum_ext@UpReqSumD:112 *)
(*    A2 uabT3_reqalign_sum_add        ←L64 sum_add   放电 sumd_sum_add@:161 *)
(*    A3 uabT3_reqalign_sum_linear     ←L67 sum_linear 放电 sumd_sum_linear@:135 *)
(*    A4 uabT3_reqalign_sum_pos        ←L70 sum_pos   放电 sumd_sum_pos@:233 *)
(*        （非空数据槽显式参：Not (enum = nil) 与 UpReqSumD 头注            *)
(*          「非空前提显式参」同形同阶；原假设位无此参）                   *)
(*    A5 uabT3_reqalign_sum_le         ←L72 sum_le    放电 sumd_sum_le@:203 *)
(*    A6 uabT3_reqalign_sum_zero_nonneg←L74 sum_zero_nonneg             *)
(*        放电 sumd_sum_zero_nonneg_surj@:400（满射数据槽显式参：          *)
(*        UpReqSumD 裁决注——全称形不可证，满射数据显式参=最大诚实完成；    *)
(*        FA2 普查表 ：74 位放电依据即 ：308(+:400)，本件取 ：400 形）     *)
(*   §B ReqKLProjection（L690-704）：                                  *)
(*    B1 uabT3_reqklproj_sum_ext       ←L694 sum_ext  放电 sumd_sum_ext@:112 *)
(*    B2 uabT3_reqklproj_sum_add       ←L696 sum_add  放电 sumd_sum_add@:161 *)
(*    B3 uabT3_reqklproj_sum_linear    ←L699 sum_linear 放电 sumd_sum_linear@:135 *)
(*    B4 uabT3_reqklproj_sum_le        ←L702 sum_le   放电 sumd_sum_le@:203 *)
(*   §C ReqNaturalGradient（L1121-1125）：                              *)
(*    C1 uabT3_reqnatgrad_sum_zero_nonneg←L1125 sum_zero_nonneg         *)
(*        放电 sumd_sum_zero_nonneg_surj@:400（满射数据槽显式参，同 A6；  *)
(*        FA2 普查表 ：1125 位引 ：308 成员位形——:308 与 ：400 仅槽位     *)
(*        换位（前提端/结论端 forall 互换），一行互换互推同强，取 ：400    *)
(*        与 T1a 批 B6/F6 申报口径统一）                                *)
(*   §D ReqPPORatio（L1202-1208）：                                     *)
(*    D1 uabT3_reqpporatio_sum_ext     ←L1206 sum_ext 放电 sumd_sum_ext@:112 *)
(*    D2 uabT3_reqpporatio_sum_add     ←L1208 sum_add 放电 sumd_sum_add@:161 *)
(*                                                              *)
(* 分级：13 件全 N1（库内放电件直连：被消融假设在库内已有无条件形，        *)
(*   零施工登记坐标=上列放电件行号；证明体非平凡内容在放电件本体——        *)
(*   列表归纳链 sumd_list_sum_*@UpReqSumD，本件直连不注水）。             *)
(*   两处诚实前提形态如实申报（不注水）：                                 *)
(*   · A4 pos 面＝非空数据槽显式参 Not (enum = nil)（UpReqSumD 头注        *)
(*     「非空前提显式参」同形同阶；签名变化 7 口径）；                    *)
(*   · A6/C1 zero_nonneg 面＝满射数据槽显式参 forall s, sumd_in S s enum   *)
(*     （UpReqSumD 裁决注：全称形不可证，席 57 反模型在案）。              *)
(*   数据槽是供给面（具体实例 enum 清单天然携带）非逻辑假定。              *)
(*                                                              *)
(* 依赖（全部只读消费，原树零改）：CW_ConstructiveWorld_219、            *)
(*   UpReqSumD（经其传递 UpReqAlgebra/UpReqDist）。                     *)
(*   语句面逐字抽取自现档 UpReqAlign.v（两树逐字节同验：                  *)
(*   Main/Live_X md5 同 4184e2f0，2026-09-15 版，与 FA2 普查表行号        *)
(*   逐位核对一致），仅 sumf → sumd_sumf S enum 换实例位。               *)
(*                                                              *)
(* 备注：语句面全集合层（req/le/lt 均集合值谓词；非空/满射前提之          *)
(*   Not 位与 UpReqSumD 同形同阶）；公理面零新增；文尾逐件               *)
(*   Print Assumptions 收尾。四关留痕：Live_X/attn/logs/                 *)
(*   g{1..4}-UpAblT3_UpReqAlign.log。                                   *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============ §A ReqAlignCore（UpReqAlign.v L54-74） ============ *)
(* 原 Context {R}{RIS} + S + sumf；出节全参形：R 显式（RIS 隐式位经类    *)
(* 实例解析），sumf 换 sumd_sumf S enum 实例。                          *)

(* A1 ←L62 sum_ext（逐字：forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)） *)
Theorem uabT3_reqalign_sum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* A2 ←L64 sum_add（逐字：req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g))） *)
Theorem uabT3_reqalign_sum_add :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros R RIS S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* A3 ←L67 sum_linear（逐字：forall (a : R) (f : S -> R), req (sumf (fun s => mult a (f s))) (mult a (sumf f))） *)
Theorem uabT3_reqalign_sum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros R RIS S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* A4 ←L70 sum_pos（非空数据槽显式参，sumd_sum_pos@233 同形） *)
Theorem uabT3_reqalign_sum_pos :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> R,
      (forall s : S, lt zero (f s)) -> lt zero (sumd_sumf S enum f).
Proof.
  intros R RIS S enum Hne f H.
  exact (sumd_sum_pos S enum f Hne H).
Qed.

(* A5 ←L72 sum_le *)
Theorem uabT3_reqalign_sum_le :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, le (f s) (g s)) -> le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* A6 ←L74 sum_zero_nonneg（满射数据槽显式参，sumd_sum_zero_nonneg_surj@400 同形；FA2 依据 ：308(+:400)） *)
Theorem uabT3_reqalign_sum_zero_nonneg :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S),
    (forall s : S, sumd_in S s enum) ->
    forall f : S -> R,
      (forall s : S, le zero (f s)) -> req (sumd_sumf S enum f) zero ->
      forall s : S, req (f s) zero.
Proof.
  intros R RIS S enum Hsurj f Hnn H0 s.
  exact (sumd_sum_zero_nonneg_surj S enum f Hsurj Hnn H0 s).
Qed.

(* ============ §B ReqKLProjection（UpReqAlign.v L690-704） ============ *)

(* B1 ←L694 sum_ext *)
Theorem uabT3_reqklproj_sum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* B2 ←L696 sum_add *)
Theorem uabT3_reqklproj_sum_add :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros R RIS S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* B3 ←L699 sum_linear *)
Theorem uabT3_reqklproj_sum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros R RIS S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* B4 ←L702 sum_le *)
Theorem uabT3_reqklproj_sum_le :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, le (f s) (g s)) -> le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* ============ §C ReqNaturalGradient（UpReqAlign.v L1121-1125） ============ *)

(* C1 ←L1125 sum_zero_nonneg（满射数据槽显式参，同 A6；FA2 引 :308 成员位形，:308/:400 一行互换同强） *)
Theorem uabT3_reqnatgrad_sum_zero_nonneg :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S),
    (forall s : S, sumd_in S s enum) ->
    forall f : S -> R,
      (forall s : S, le zero (f s)) -> req (sumd_sumf S enum f) zero ->
      forall s : S, req (f s) zero.
Proof.
  intros R RIS S enum Hsurj f Hnn H0 s.
  exact (sumd_sum_zero_nonneg_surj S enum f Hsurj Hnn H0 s).
Qed.

(* ============ §D ReqPPORatio（UpReqAlign.v L1202-1208） ============ *)

(* D1 ←L1206 sum_ext *)
Theorem uabT3_reqpporatio_sum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* D2 ←L1208 sum_add *)
Theorem uabT3_reqpporatio_sum_add :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros R RIS S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabT3_reqalign_sum_ext.
Print Assumptions uabT3_reqalign_sum_add.
Print Assumptions uabT3_reqalign_sum_linear.
Print Assumptions uabT3_reqalign_sum_pos.
Print Assumptions uabT3_reqalign_sum_le.
Print Assumptions uabT3_reqalign_sum_zero_nonneg.
Print Assumptions uabT3_reqklproj_sum_ext.
Print Assumptions uabT3_reqklproj_sum_add.
Print Assumptions uabT3_reqklproj_sum_linear.
Print Assumptions uabT3_reqklproj_sum_le.
Print Assumptions uabT3_reqnatgrad_sum_zero_nonneg.
Print Assumptions uabT3_reqpporatio_sum_ext.
Print Assumptions uabT3_reqpporatio_sum_add.
