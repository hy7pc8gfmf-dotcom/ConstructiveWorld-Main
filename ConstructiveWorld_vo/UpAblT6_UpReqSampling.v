(* ============================================================ *)
(* UpAblT6_UpReqSampling.v —— 假设消融战役 T6 批·席 a（T3a 移交同根余量前 ≤25 位之 11 位） *)
(* 辖区：UpReqSampling.v sumf 接口面（ReqUContraction/ReqBoundedSoftmax 两节）   *)
(* 放电母本：sumd_*@UpReqSumD                                                   *)
(*                                                              *)
(* 目的：对 UpReqSampling 两节的 sumf 接口面假设位逐条兑现消融定理：              *)
(*   假设位（对任意 sumf 算子的接口字段假定）在具体有限和实例                    *)
(*   sumf := sumd_sumf S enum（enum 列表和，UpReqSumD 放电机械）上               *)
(*   全部无条件成立——前提减薄为纯数据槽（枚举清单），假设位逐条消除。            *)
(*                                                              *)
(* 主件清单（11 件，前缀 uabT6_，逐件标注被消融位坐标与放电件）：                 *)
(*   §A ReqUContraction（L98-136）：                                   *)
(*    A1 uabT6_usamp_sum_ext      ←L105 sum_ext    放电 sumd_sum_ext@UpReqSumD:112 *)
(*    A2 uabT6_usamp_sum_linear   ←L107 sum_linear 放电 sumd_sum_linear@:135 *)
(*    A3 uabT6_usamp_sum_add      ←L110 sum_add    放电 sumd_sum_add@:161 *)
(*    A4 uabT6_usamp_sum_le       ←L113 sum_le     放电 sumd_sum_le@:203 *)
(*    A5 uabT6_usamp_sum_swap_cc  ←L132 sum_swap_cc 放电 sumd_sum_swap@:384 *)
(*        （swap 特形：f 双标函数参 f : S -> S -> R，内外两层 sumf 实例位；     *)
(*          T3a 移交单注意位预勘命中——先 Check 出节签名再落语句，              *)
(*          sumd_sum_swap 出节形与本件语句面逐字同构）                        *)
(*   §B ReqBoundedSoftmax（L700-747）：                                *)
(*    B1 uabT6_bsoft_sum_ext      ←L707 sum_ext    放电 sumd_sum_ext@:112 *)
(*    B2 uabT6_bsoft_sum_linear   ←L709 sum_linear 放电 sumd_sum_linear@:135 *)
(*    B3 uabT6_bsoft_sum_pos      ←L712 sum_pos    放电 sumd_sum_pos@:233 *)
(*        （非空数据槽显式参：Not (enum = nil) 与 UpReqSumD 头注               *)
(*          「非空前提显式参」同形同阶；原假设位无此参）                      *)
(*    B4 uabT6_bsoft_sum_add      ←L714 sum_add    放电 sumd_sum_add@:161 *)
(*    B5 uabT6_bsoft_sum_le       ←L717 sum_le     放电 sumd_sum_le@:203 *)
(*    B6 uabT6_bsoft_sum_eq_list  ←L747 sum_eq_list 放电 sumd_sum_eq_list@:81 *)
(*        （eq_list 特形：结论为列表和桥——原节内引用节自持 Fixpoint           *)
(*          rsq_bs_list_sum，本件以 UpReqSumD 同形自持机械 sumd_list_sum      *)
(*          兑现（UpReqSumD 头注 L69「与 UpReqSampling bs_list_sum 同形        *)
(*          自持」），sumd_sum_eq_list 在具体实例上为定义性 req_refl 件；      *)
(*          移交单注意位预勘第二处命中，同先 Check 纪律落语句）               *)
(*                                                              *)
(* 分级：11 件全 N1（库内放电件直连：被消融假设在库内已有无条件形，               *)
(*   零施工登记坐标=上列放电件行号；证明体非平凡内容在放电件本体——              *)
(*   列表归纳链 sumd_list_sum_*@UpReqSumD，本件直连不注水）。                    *)
(*   一处诚实前提形态如实申报（不注水）：                                       *)
(*   · B3 pos 面＝非空数据槽显式参 Not (enum = nil)（UpReqSumD 头注             *)
(*     「非空前提显式参」同形同阶；签名变化 7 口径）。                          *)
(*   数据槽是供给面（具体实例 enum 清单天然携带）非逻辑假定。                    *)
(*   本批辖区无 zero_nonneg 面（无满射槽参形）；W 邻接位 L116/L719              *)
(*   abs_sum_le_h 属 §3-W1 墙件，未纳入、未触碰。                              *)
(*                                                              *)
(* 依赖（全部只读消费，原树零改）：CW_ConstructiveWorld_219、                   *)
(*   UpReqSumD（经其传递 UpReqAlgebra/UpReqDist）。                            *)
(*   语句面逐字抽取自现档 UpReqSampling.v（两树逐字节同验：                      *)
(*   Main/Live_X md5 同 2ce2c50a，2026-09-15 版，与 FA2 普查表行号              *)
(*   逐位核对一致），仅 sumf → sumd_sumf S enum 换实例位。                     *)
(*                                                              *)
(* 备注：语句面全集合层（req/le/lt 均集合值谓词）；公理面零新增；文尾逐件        *)
(*   Print Assumptions 收尾。四关留痕：Live_X/attn/logs/                        *)
(*   g{1..4}-UpAblT6_UpReqSampling.log。                                       *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============ §A ReqUContraction（UpReqSampling.v L98-136） ============ *)
(* 原 Context {R}{RIS} + S + sumf；出节全参形：R 显式（RIS 隐式位经类          *)
(* 实例解析），sumf 换 sumd_sumf S enum 实例。                                *)

(* A1 ←L105 sum_ext（逐字：forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)） *)
Theorem uabT6_usamp_sum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* A2 ←L107 sum_linear（逐字：forall (a : R) (f : S -> R), req (sumf (fun s : S => mult a (f s))) (mult a (sumf f))） *)
Theorem uabT6_usamp_sum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros R RIS S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* A3 ←L110 sum_add（逐字：forall f g : S -> R, req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g))） *)
Theorem uabT6_usamp_sum_add :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros R RIS S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* A4 ←L113 sum_le（逐字：forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g)） *)
Theorem uabT6_usamp_sum_le :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, le (f s) (g s)) -> le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* A5 ←L132 sum_swap_cc（swap 特形：双标函数参，内外两层 sumf 实例位全换；放电 sumd_sum_swap@384） *)
Theorem uabT6_usamp_sum_swap_cc :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f : S -> S -> R),
    req (sumd_sumf S enum (fun s : S => sumd_sumf S enum (fun s' : S => f s s')))
        (sumd_sumf S enum (fun s' : S => sumd_sumf S enum (fun s : S => f s s'))).
Proof.
  intros R RIS S enum f.
  exact (sumd_sum_swap S enum f).
Qed.

(* ============ §B ReqBoundedSoftmax（UpReqSampling.v L700-747） ============ *)

(* B1 ←L707 sum_ext *)
Theorem uabT6_bsoft_sum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* B2 ←L709 sum_linear *)
Theorem uabT6_bsoft_sum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros R RIS S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* B3 ←L712 sum_pos（非空数据槽显式参，sumd_sum_pos@233 同形） *)
Theorem uabT6_bsoft_sum_pos :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> R,
      (forall s : S, lt zero (f s)) -> lt zero (sumd_sumf S enum f).
Proof.
  intros R RIS S enum Hne f H.
  exact (sumd_sum_pos S enum f Hne H).
Qed.

(* B4 ←L714 sum_add *)
Theorem uabT6_bsoft_sum_add :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros R RIS S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* B5 ←L717 sum_le *)
Theorem uabT6_bsoft_sum_le :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, le (f s) (g s)) -> le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* B6 ←L747 sum_eq_list（eq_list 特形：列表和桥，UpReqSumD 同形自持机械 sumd_list_sum 兑现；放电 sumd_sum_eq_list@81） *)
Theorem uabT6_bsoft_sum_eq_list :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (g : S -> R),
    req (sumd_sumf S enum g) (sumd_list_sum S g enum).
Proof.
  intros R RIS S enum g.
  exact (sumd_sum_eq_list S enum g).
Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabT6_usamp_sum_ext.
Print Assumptions uabT6_usamp_sum_linear.
Print Assumptions uabT6_usamp_sum_add.
Print Assumptions uabT6_usamp_sum_le.
Print Assumptions uabT6_usamp_sum_swap_cc.
Print Assumptions uabT6_bsoft_sum_ext.
Print Assumptions uabT6_bsoft_sum_linear.
Print Assumptions uabT6_bsoft_sum_pos.
Print Assumptions uabT6_bsoft_sum_add.
Print Assumptions uabT6_bsoft_sum_le.
Print Assumptions uabT6_bsoft_sum_eq_list.
