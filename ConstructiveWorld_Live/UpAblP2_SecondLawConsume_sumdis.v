(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpAblP2_SecondLawConsume_sumdis.v —— 假设消融工程 FA-P2  S1          *)
(* 辖区：SecondLawConsume.v SlcSecondLawConsume 节 9 位中 4 个求和槽              *)
(*   （sumpos/sumext/sumlinear/sumadd，Live_X 现档 L132/L135/L137/L139）          *)
(* 实例化消解源文件：real_list_sum 系四件（源文件自身出节全参插件同款）＋                   *)
(*   pnt_list_sum_eq_ext 同语句双轨（普查指引坐标 UpReqPinskerTransport:463）     *)
(*                                                              *)
(* 目的：4 个求和接口槽在具体实例 sumf := real_list_sum X（固定清单 l）上          *)
(*   全部无条件成立——前提减薄为纯数据槽（清单 l＋非空见证），求和假设位逐条消除；  *)
(*   并以出节全参形重装节主件 slc_gain_kl_two_sided_eps（4 槽零假设版）。         *)
(*                                                              *)
(* 主件清单（前缀 uabp2_，逐件标注被消融位坐标与实例化消解件）：                         *)
(*   A1 uabp2_slc_sumpos_list    ←L132 sumpos    实例化消解 real_list_sum_pos           *)
(*   A2 uabp2_slc_sumext_list    ←L135 sumext    实例化消解 real_list_sum_ext           *)
(*       A2t uabp2_slc_sumext_pnt ←同语句 pnt_list_sum_eq_ext 双轨（普查指引）     *)
(*   A3 uabp2_slc_sumlinear_list ←L137 sumlinear 实例化消解 real_list_sum_linear        *)
(*   A4 uabp2_slc_sumadd_list    ←L139 sumadd    实例化消解 real_list_sum_add           *)
(*   A5 uabp2_slc_two_sided_list ←节主件 L235 slc_gain_kl_two_sided_eps           *)
(*       出节全参形：4 求和槽以实例见证直接代入后消除，余槽=S/T/T_pos/energy 数据面    *)
(*                                                              *)
(* 分级（如实申报）：A1–A4 全 N1（库内实例化消解件直连；非平凡内容在实例化消解件本体的         *)
(*   列表归纳链，本件直连不注水）；A5 N2（已证件 slc_kl_le_gain_plus_leg/          *)
(*   slc_gain_le_kl_plus_leg 出节全参组合）。其余 5 槽如实定级（报告表）：          *)
(*   S/sumf/T/energy=数据槽 T，T_pos=证书前提 T——不构定理、不计战果。             *)
(*                                                              *)
(* 依赖（全部只读使用，原树零改）：CW_ConstructiveWorld_219、UpReqTempDefs、       *)
(*   UpReqEntropyDeficitTemp、SecondLawQuantified、SecondLawConsume、              *)
(*   UpReqPinskerTransport。语句面逐字抽取自现档 SecondLawConsume.v               *)
(*   （L130-144 节接口参数、L147-155/L189-197 出节形 About 实证 15 参）。             *)
(*                                                              *)
(* 备注：语句面全集合层（real_lt/real_eq 为集合值型，real_le 为 Or 和型）；        *)
(*   公理面零新增；文尾逐件 Print Assumptions 收尾。                              *)
(*   四关留痕：Live_X/attn/logs/g{1..4}-UpAblP2S1_sumdis.log。                    *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import SecondLawQuantified.
Require Import SecondLawConsume.
Require Import UpReqPinskerTransport.
From Stdlib Require Import List.
Import ListNotations.

(* ============ A1 ←L132-134 sumpos（逐字语句，sumf 换 real_list_sum 实例） ============ *)
(* 原槽（节内）：forall (f : S -> Real),
     (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (sumf f) *)
Theorem uabp2_slc_sumpos_list :
  forall (X : Type) (l : list X) (Hnil : l <> nil) (f : X -> Real),
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum X f l).
Proof.
  intros X l Hnil f Hf.
  exact (real_list_sum_pos X f l Hf Hnil).
Qed.

(* ============ A2 ←L135-136 sumext ============ *)
(* 原槽：forall (f g : S -> Real),
     (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g) *)
Theorem uabp2_slc_sumext_list :
  forall (X : Type) (f g : X -> Real) (l : list X),
    (forall s : X, real_eq (f s) (g s)) ->
    real_eq (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l H.
  exact (real_list_sum_ext X f g l H).
Qed.

(* A2t：同语句 pnt_list_sum_eq_ext 双轨（普查指引坐标 UpReqPinskerTransport:463） *)
Theorem uabp2_slc_sumext_pnt :
  forall (X : Type) (f g : X -> Real) (l : list X),
    (forall s : X, real_eq (f s) (g s)) ->
    real_eq (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l H.
  exact (pnt_list_sum_eq_ext X f g l H).
Qed.

(* ============ A3 ←L137-138 sumlinear ============ *)
(* 原槽：forall (a : Real) (f : S -> Real),
     real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)) *)
Theorem uabp2_slc_sumlinear_list :
  forall (X : Type) (a : Real) (f : X -> Real) (l : list X),
    real_eq (real_list_sum X (fun s : X => real_mult a (f s)) l)
            (real_mult a (real_list_sum X f l)).
Proof.
  intros X a f l.
  exact (real_list_sum_linear X a f l).
Qed.

(* ============ A4 ←L139-141 sumadd ============ *)
(* 原槽：forall (f g : S -> Real),
     real_eq (sumf (fun s : S => real_plus (f s) (g s)))
             (real_plus (sumf f) (sumf g)) *)
Theorem uabp2_slc_sumadd_list :
  forall (X : Type) (f g : X -> Real) (l : list X),
    real_eq (real_list_sum X (fun s : X => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum X f l) (real_list_sum X g l)).
Proof.
  intros X f g l.
  exact (real_list_sum_add X f g l).
Qed.

(* ============ A5 ←节主件 L235 slc_gain_kl_two_sided_eps 之 4 槽零假设版 ============ *)
(* 出节全参形（About 实证 15 参）：X SF SP SE SL SA T Ht energy p Hp Hnp Henergy   *)
(* eps Heps；4 求和槽以实例见证直接代入（源文件自身 L322-324/L358-360 同款插件）。        *)
(* 实例求和机器：SF := fun g => real_list_sum X g l（固定清单 l＋非空见证 Hnil）。  *)
Theorem uabp2_slc_two_sided_list :
  forall (X : Type) (l : list X) (Hnil : l <> nil)
         (T : Real) (Ht : real_lt real_zero T)
         (energy p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
    real_eq (real_list_sum X p l) real_one ->
    real_eq (real_list_sum X (fun s : X => real_mult (p s) (energy s)) l)
            (real_energy_exp_temp X (fun g : X -> Real => real_list_sum X g l)
               (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                  real_list_sum_pos X f l Hf Hnil)
               T Ht energy) ->
    forall eps : Real, real_lt real_zero eps ->
      slc_band
        (real_le (slq_kl_cur_boltz X (fun g : X -> Real => real_list_sum X g l)
                    (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                       real_list_sum_pos X f l Hf Hnil)
                    T Ht energy p Hp)
                 (real_plus (slq_entropy_gain X (fun g : X -> Real => real_list_sum X g l)
                               (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                                  real_list_sum_pos X f l Hf Hnil)
                               T Ht energy p Hp) eps))
        (real_le (slq_entropy_gain X (fun g : X -> Real => real_list_sum X g l)
                    (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                       real_list_sum_pos X f l Hf Hnil)
                    T Ht energy p Hp)
                 (real_plus (slq_kl_cur_boltz X (fun g : X -> Real => real_list_sum X g l)
                               (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                                  real_list_sum_pos X f l Hf Hnil)
                               T Ht energy p Hp) eps)).
Proof.
  intros X l Hnil T Ht energy p Hp Hnp Henergy eps Heps.
  exact (slc_band_intro
           (real_le (slq_kl_cur_boltz X (fun g : X -> Real => real_list_sum X g l)
                       (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                          real_list_sum_pos X f l Hf Hnil)
                       T Ht energy p Hp)
                    (real_plus (slq_entropy_gain X (fun g : X -> Real => real_list_sum X g l)
                                  (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                                     real_list_sum_pos X f l Hf Hnil)
                                  T Ht energy p Hp) eps))
           (real_le (slq_entropy_gain X (fun g : X -> Real => real_list_sum X g l)
                       (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                          real_list_sum_pos X f l Hf Hnil)
                       T Ht energy p Hp)
                    (real_plus (slq_kl_cur_boltz X (fun g : X -> Real => real_list_sum X g l)
                                  (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                                     real_list_sum_pos X f l Hf Hnil)
                                  T Ht energy p Hp) eps))
           (slc_kl_le_gain_plus_leg X
              (fun g : X -> Real => real_list_sum X g l)
              (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                 real_list_sum_pos X f l Hf Hnil)
              (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l)
              (fun (a0 : Real) (f0 : X -> Real) => real_list_sum_linear X a0 f0 l)
              (fun f0 g0 : X -> Real => real_list_sum_add X f0 g0 l)
              T Ht energy p Hp Hnp Henergy eps Heps)
           (slc_gain_le_kl_plus_leg X
              (fun g : X -> Real => real_list_sum X g l)
              (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                 real_list_sum_pos X f l Hf Hnil)
              (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l)
              (fun (a0 : Real) (f0 : X -> Real) => real_list_sum_linear X a0 f0 l)
              (fun f0 g0 : X -> Real => real_list_sum_add X f0 g0 l)
              T Ht energy p Hp Hnp Henergy eps Heps)).
Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabp2_slc_sumpos_list.
Print Assumptions uabp2_slc_sumext_list.
Print Assumptions uabp2_slc_sumext_pnt.
Print Assumptions uabp2_slc_sumlinear_list.
Print Assumptions uabp2_slc_sumadd_list.
Print Assumptions uabp2_slc_two_sided_list.
