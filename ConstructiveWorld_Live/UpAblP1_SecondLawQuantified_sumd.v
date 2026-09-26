(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(* UpAblP1_SecondLawQuantified_sumd.v                            *)
(*                                                               *)
(* 位：FA-P1S1 （三重述批·件三）｜日期：    *)
(* 工单：attn/_tfap1_普查报告-.md ④ 之 sum 四面封装           *)
(*       （★★★；two_state 整节实例化另账，本件不涉及）。               *)
(* 目的：SecondLawQuantified 受体节 SlqSecondLaw 的 sum 四面假设位        *)
(*       重述：sumpos（:78，使用 11 处）/sumext（:81，使用 5 处）/        *)
(*       sumlinear（:83，使用 5 处）/sumadd（:85，使用 4 处）。           *)
(* 实例化消解源文件（逐字行号直取，a/T6a 已验坐标）：                          *)
(*   sumd_sum_ext@UpReqSumD:112 / sumd_sum_linear@:135 /                 *)
(*   sumd_sum_add@:161 / sumd_sum_pos@:233（SumDischarge 封注册械）。     *)
(* 实例面：sumf 槽的消解实例＝enum 列表和 sumd_sumf（T6a 根）；           *)
(*   载体位取 Set 实例面（sumd 机械 S:Set 口径；SLQ 节 S:Type 的          *)
(*   Set 载体实例即落本面）；sumpos 位非空前提显式承载（UpReqSumD         *)
(*   cons 形诚实完成同口径，Not 位与 UpReqSampling 签名变化 7 同形同阶）。*)
(* 四面语句逐字＝SLQ 声明行的 real_* 素颜面（在 Real 实例下与接口字段面   *)
(*   δ/iota 重合，exact 直接代入一步，sbd_ 先例同式）。                       *)
(* 分级：四面全 N1（普查总表 ④ 逐位坐标即本件施工图）。               *)
(* 纪律：全 Set 层语句（real_lt/real_eq Set 值谓词）；零新增遗留声明形；   *)
(*   全 Qed；宿主与只读树零改；前缀 uabp1_（全库实扫零撞名）。            *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
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
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section SlqSumD：SLQ sum 四面在 sumd 实例上的重述束              *)
(* ============================================================ *)
Section SlqSumD.

Context (S0 : Set).
Context (enum0 : list S0).
Context (enum0_nonempty : Not (enum0 = nil)).

(* sumf 槽实例：enum 列表和（定义件，δ 透明；T6a 根） *)
Definition uabp1_slq_sumf (f : S0 -> Real) : Real := sumd_sumf S0 enum0 f.

(* ============ sumpos 位重述（SLQ :78 语句逐字） ============ *)
(* ← sumd_sum_pos@UpReqSumD:233（非空前提显式承载） *)
Theorem uabp1_slq_sumpos :
  forall f : S0 -> Real,
    (forall s : S0, real_lt real_zero (f s)) ->
    real_lt real_zero (uabp1_slq_sumf f).
Proof.
  intros f H.
  exact (sumd_sum_pos S0 enum0 f enum0_nonempty H).
Qed.

(* ============ sumext 位重述（SLQ :81 语句逐字） ============ *)
(* ← sumd_sum_ext@UpReqSumD:112（普查 19 槽最大面代表件） *)
Theorem uabp1_slq_sumext :
  forall f g : S0 -> Real,
    (forall s : S0, real_eq (f s) (g s)) ->
    real_eq (uabp1_slq_sumf f) (uabp1_slq_sumf g).
Proof.
  intros f g H.
  exact (sumd_sum_ext S0 enum0 f g H).
Qed.

(* ============ sumlinear 位重述（SLQ :83 语句逐字） ============ *)
(* ← sumd_sum_linear@UpReqSumD:135 *)
Theorem uabp1_slq_sumlinear :
  forall (a : Real) (f : S0 -> Real),
    real_eq (uabp1_slq_sumf (fun s : S0 => real_mult a (f s)))
            (real_mult a (uabp1_slq_sumf f)).
Proof.
  intros a f.
  exact (sumd_sum_linear S0 enum0 a f).
Qed.

(* ============ sumadd 位重述（SLQ :85 语句逐字） ============ *)
(* ← sumd_sum_add@UpReqSumD:161 *)
Theorem uabp1_slq_sumadd :
  forall f g : S0 -> Real,
    real_eq (uabp1_slq_sumf (fun s : S0 => real_plus (f s) (g s)))
            (real_plus (uabp1_slq_sumf f) (uabp1_slq_sumf g)).
Proof.
  intros f g.
  exact (sumd_sum_add S0 enum0 f g).
Qed.

End SlqSumD.

(* ============ G3 提取检验（一人一目录 _tp1s1_g3out） ============ *)
(* 求和载体件为本件唯一计算内容（列表 fold）；链复核。          *)
(* 接口字段（zero/plus）经 RIS 记录使用会拉入记录封装体——按两步判读       *)
(* 口径：家规轨（fold 核心体）magic=0 为过关主判据，记录体封装 magic      *)
(* 为擦除伪影逐族登记；四面重述体为等词/序谓词桥面，以说明替代提取。      *)
Set Extraction Output Directory "_tp1s1_g3out".
Extraction "uabp1s1_G3_sumd.ml" uabp1_slq_sumf.

(* ============ G4 检验：假设闭包审计（四面全 Closed 为过关判据） ============ *)
Print Assumptions uabp1_slq_sumpos.
Print Assumptions uabp1_slq_sumext.
Print Assumptions uabp1_slq_sumlinear.
Print Assumptions uabp1_slq_sumadd.
