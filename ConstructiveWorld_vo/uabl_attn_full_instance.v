(* uabl_attn_full_instance.v — BoundedSoftmax 接口十九字段的 Fin2 默认实例与单入口聚合导出面。 *)
(* 模块使命：Require 一行后，十九字段（expf 六槽/诚实接口三件/世界数据位与证书）以 uabl_ 前缀具名行全部在位，另附 Id 面条件形两件（任一装可判定序的模型给 RI DO 两参即得）。 *)
(* 依赖：CW_ConstructiveWorld_219、AttnDoeblin、UpReqConcFin2、UpReqConcB1、UpAblD1_expf_pack、UpReqSampling、fa53_compat_abs（全部只读引用，基座件零改）。 *)
(* 构造性注记：全件 Set 层承载、零承认位、可提取。DecidableOrder 于柯西实数载体的整体判定实例不存在（属受限线性全称等价族，lt_dec/ord_le_dec/eq_dec 为整体判定槽，UpReqLpoEquiv.v:448 lpn_equivalence 已机器双向归约），故不构造之；值载体侧 bs_abs/bs_lpc 走具体层无条件供件（UpReqConcB1:128、S07:6147），Id 面取条件形由使用方提供实例。 *)
(* 编译配方：ASCII .cmd、COQLIB/ROCQLIB 置空、coqc 9.1 -native-compiler no -Q <库树> ""。 *)

From Stdlib Require Import List.
Import ListNotations.

(* 单入口 Export 面：下游 Require Import uabl_attn_full_instance 一行， *)
(* 即得下列全部名字空间与十九字段具名定义行。                          *)
Require Export S01_BaseRing.
Require Export S02_CauchyComplete.
Require Export S03_QExp.
Require Export S04_RealExpLogConv.
Require Export S05_AlignmentGRPO.
Require Export S06_DiffSamplingGibbs.
Require Export S07_RealSetoidExpLog.
Require Export S08_RealMainlineDPO.
Require Export S09_EntropyReal.
Require Export S10_KVQuantTrig.
Require Export S11_TP3B5.
Require Export S12_B5RecycleSF.
Require Export S13_NLiveAudit.
Require Export S14_B5BatchBlock.
Require Export S15_TailFEPUp.
Require Export AttnDoeblin.
Require Export UpReqConcFin2.
Require Export UpReqConcB1.
Require Export UpAblD1_expf_pack.
Require Export UpReqSampling.


(* 条件形实例化消解源文件（Part E 引用；本件内部 Require 零改） *)
Require Import fa53_compat_abs.

(* ============================================================ *)
(* Part A：行1-6 expf 族（cauchy_real_exp 载体，五证书逐行具名）      *)
(* ============================================================ *)

Definition uabl_expf : Real -> Real := uabd1x_expf.

Definition uabl_expf_pos :
  forall x : Real, real_lt real_zero (uabl_expf x) := uabd1x_expf_pos.

Definition uabl_expf_zero :
  real_eq (uabl_expf real_zero) real_one := uabd1x_expf_zero.

Definition uabl_expf_plus :
  forall a b : Real,
    real_eq (uabl_expf (real_plus a b)) (real_mult (uabl_expf a) (uabl_expf b))
  := uabd1x_expf_plus.

Definition uabl_expf_mono_lt :
  forall a b : Real, real_lt a b -> real_lt (uabl_expf a) (uabl_expf b)
  := uabd1x_expf_mono_lt.

Definition uabl_expf_mono_le :
  forall a b : Real, real_le a b -> real_le (uabl_expf a) (uabl_expf b)
  := uabd1x_expf_mono_le.

(* ============================================================ *)
(* Part B：行7-9 诚实接口三件（具体层无条件供件，零 DO 前提）         *)
(* ============================================================ *)

Definition uabl_bs_swap :
  forall f : bool -> bool -> Real,
    real_eq (cf2_sumf (fun s : bool => cf2_sumf (fun s' : bool => f s s')))
            (cf2_sumf (fun s' : bool => cf2_sumf (fun s : bool => f s s')))
  := cf2_bs_swap.

Definition uabl_bs_abs :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a
  := cb1_bs_abs.

Definition uabl_bs_lpc :
  forall a b c d : Real,
    real_lt a b -> real_le c d -> real_lt (real_plus a c) (real_plus b d)
  := real_lt_plus_compat_lt_le.

(* ============================================================ *)
(* Part C：行10-19 世界数据位＋证书（Fin2 世界，全部既有 cf2 直引）   *)
(* ============================================================ *)

Definition uabl_sumf (f : bool -> Real) : Real := cf2_sumf f.

Definition uabl_enum : list bool := cf2_enum2.

Definition uabl_enum_ne := cf2_enum_ne.

Definition uabl_temp : Real := cf2_temp.

Definition uabl_temp_pos := cf2_temp_pos.

Definition uabl_Delta : Real := cf2_Delta.

Definition uabl_Delta_pos := cf2_Delta_pos.

Definition uabl_z : bool -> bool -> Real := cf2_z.

Definition uabl_z_lb := cf2_z_lb.

Definition uabl_z_ub := cf2_z_ub.

Definition uabl_sum_eq_list := cf2_sum_eq_list.

(* ============================================================ *)
(* Part D：单对象装箱注记——十九字段以 uabl_ 前缀具名行供给（上文 A-C 区），  *)
(*   下游 Require 一行后经 Check/参数位逐行取用；不再另立嵌套装箱大对象，     *)
(*   使每行语句面与其上游源文件逐字同面（零换面转换税）。                     *)

(* Part E：Id 面条件形实例化消解件（(RI DO) 显式前提随件形态）              *)
(*   任一未来装 DecidableOrder 的模型：Require 本件＋给 RI DO 两参，  *)
(*   bs_abs/bs_lpc 两 Id 面槽即实例化消解，零证明体。 *)
(* ============================================================ *)

Section UablIdFaceDischarge.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Theorem uabl_bs_abs_id : forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI DO a Ha).
Qed.

Theorem uabl_bs_lpc_id :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI DO a b c d Hab Hcd).
Qed.

End UablIdFaceDischarge.

(* ============================================================ *)
(* 证据段： Closed 判读＋提取检验（本件编译运行目录产出 .ml，        *)
(*   魔数判读按工程规程执行）                                        *)
(* ============================================================ *)

Print Assumptions uabl_bs_abs_id.
Print Assumptions uabl_bs_lpc_id.
Print Assumptions uabl_expf_pos.
Print Assumptions uabl_bs_abs.

From Stdlib Require Import Extraction.
Separate Extraction uabl_expf uabl_bs_abs uabl_bs_lpc uabl_enum uabl_temp uabl_Delta uabl_z.
