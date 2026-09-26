(* ==========================================================================)
   UpAblD1S17_UpReqAttnGibbs.v — UpReqAttnGibbs 节接口十九项字段的单点实例记录与供给定理
   使命: 热力学配分和正性、逐出分区正性、指数几何衰减 exp_neg_geo_break 等前提的单点见证构造，装配为记录 uabd1s17_gib_pack18 与供给定理；不 Require 源模块本体。
   依赖: CW_ConstructiveWorld_219、UpReqCauchy（req_r_pow）、G07_KLWall（klcx_exp_neg_geo_break_iface）。
   对标: 单点态空间上配分和与逐出分区正性、指数尾衰减的构造性见证。
   构造性: 语句面全 Set 层；全件 Qed 闭合、零承认词面、无经典逻辑；keep_dec 前提在单点态空间上以 inl tt 显式见证；文末对两条主结论逐一 Print Assumptions 全 Closed。
   编译配方: Rocq 9.1 直调 coqc 编译（不带 -Q 包映射），cpu_guard 包裹限载；输出一律 -o 临时目录，树内 .vo 不重写。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqCauchy.
Require Import G07_KLWall.
Import RealInterfaceEnhancedMod.

(* ============ 典范载体实例具名 ============ *)

Definition uabd1s17_ren : RealInterfaceEnhancedSetoid Real :=
  RealInterfaceEnhancedMod.RealEnhancedReal.

(* ============ 接口封装记录：对应源模块 Section ReqAttnGibbs 的节内声明 ============ *)
(* 字段序＝源模块声明序；sum_pos、req_lt_plus_compat_lt_le_h、              *)
(* detailed_balance_r 三项不在本记录中（供给由上述专件承担）。            *)
(* Z_thermo_r/evicted_partition_r 系源模块节内 Definition，本记录相应       *)
(* 字段按其定义体经 δ 归约后逐字展开（与源模块定义可互换）。                *)

Inductive uabd1s17_gib_pack18 : Type :=
| uabd1s17_gib_pack18_intro :
    forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (sumf : (S -> R) -> R)
           (sum_ext : forall f g : S -> R,
                      (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
           (sum_linear : forall (a : R) (f : S -> R),
                         req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)))
           (sum_add : forall f g : S -> R,
                      req (sumf (fun s : S => plus (f s) (g s)))
                          (plus (sumf f) (sumf g)))
           (T : R) (T_pos : lt zero T)
           (D : R) (D_pos : lt zero D) (energy : S -> R)
           (Z_thermo_r_pos :
              lt zero (sumf (fun s : S =>
                        exp_neg (mult (inv_pos D D_pos) (energy s)))))
           (transition : S -> S -> R) (keep : S -> Set)
           (keep_dec : forall s : S, Or (keep s) (Not (keep s)))
           (sum_le : forall f g : S -> R,
                     (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g))
           (abs_sum_le_r : forall f : S -> R,
                           le (abs (sumf f)) (sumf (fun s : S => abs (f s))))
           (evicted_partition_r_pos :
              lt zero (sumf (fun s : S =>
                        if keep_dec s
                        then exp_neg (mult (inv_pos D D_pos) (energy s))
                        else zero)))
           (exp_neg_geo_break :
              forall d : R, lt zero d ->
                forall eps : R, lt zero eps ->
                  sigT (fun N : nat =>
                    le (exp_neg (mult (req_r_pow (plus one one) N) d)) eps)),
      uabd1s17_gib_pack18.

(* ============ exp_neg_geo_break 的供给（转引库中引理） ============ *)
(* 记录字段 req_r_pow 取 UpReqCauchy 出节后的全局同名引理（与源模块         *)
(*   Section 内同名同源）。以下标识符在定义展开后同体，可互换使用：       *)
(*   exp_neg≡real_exp_neg／req_r_pow≡klcx_r_pow／plus one one≡          *)
(*   real_plus real_one real_one。                                       *)

Theorem uabd1s17_gib_geobreak :
  forall d : Real, lt zero d ->
    forall eps : Real, lt zero eps ->
      sigT (fun N : nat =>
        le (exp_neg (mult (req_r_pow (plus one one) N) d)) eps).
Proof.
  intros d Hd eps Heps.
  exact (klcx_exp_neg_geo_break_iface d eps Hd Heps).
Qed.

(* ============ 供给定理：以单点实例给出记录的全部字段 ============ *)

Theorem uabd1s17_gib_pack18_supplied : uabd1s17_gib_pack18.
Proof.
  exact (uabd1s17_gib_pack18_intro
           Real uabd1s17_ren
           unit (fun f : unit -> Real => f tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, req (f s) (g s)) => H tt)
           (fun (a : Real) (f : unit -> Real) =>
              @req_refl Real uabd1s17_ren (mult a (f tt)))
           (fun (f g : unit -> Real) =>
              @req_refl Real uabd1s17_ren (plus (f tt) (g tt)))
           one (@one_pos Real uabd1s17_ren)
           one (@one_pos Real uabd1s17_ren)
           (fun _ : unit => zero)
           (@exp_neg_pos Real uabd1s17_ren
              (mult (inv_pos one (@one_pos Real uabd1s17_ren)) zero))
           (fun (_ _ : unit) => zero)
           (fun _ : unit => unit)
           (fun _ : unit => @inl unit (Not unit) tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, le (f s) (g s)) => H tt)
           (fun f : unit -> Real =>
              @le_refl Real uabd1s17_ren (abs (f tt)))
           (@exp_neg_pos Real uabd1s17_ren
              (mult (inv_pos one (@one_pos Real uabd1s17_ren)) zero))
           uabd1s17_gib_geobreak).
Qed.

(* ============ 假设审计 ============ *)

Print Assumptions uabd1s17_gib_geobreak.
Print Assumptions uabd1s17_gib_pack18_supplied.
