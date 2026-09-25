(* ============================================================ *)
(* UpAblP1_SqrtfCauchyArch_arch.v —— 使命：宿主 SqrtfCauchy 假设位3        *)
(*   sfc_arch_decay（:58-59，宿主自称可消解但最重划归独立后续件，该后续件  *)
(*   已落库）的重述补齐：论文4 §4.7 消融注已引实例化消解件，本件把宿主     *)
(*   假设位的 discharge 形补成独立配套模块。                              *)
(* 实例化消解源文件（逐字行号直取）：                                     *)
(*   本体 sfcy_arch_decay_real@SqrtfCauchyArch:266（五步构造：            *)
(*     S07:2762 real_arch 种子 + Qlt→lt 桥 + 2^n 归纳 + pow_half 归拢    *)
(*     + 乘正完成）；显式应用桥 sfcy_arch_decay_slot@SqrtfCauchyArch:434 *)
(*     （宿主位语句逐字实例投影面，exact 一行）。                         *)
(* 语句：宿主 :58-59 逐字（R:=Real 实例投影形）；sfc_pow_half 宿主裸调    *)
(*   （R:=Real 由实例 RealEnhancedReal 解析，与源文件同式）。             *)
(* 分级：N1 直接代入零新数学——证明体 exact 一行喂 sfcy_arch_decay_slot。  *)
(* 依存位（宿主，只读核验）：:1198（半衰减链）/ :1325（sfc_newton_cauchy  *)
(*   组装③）。位账：位1 永久阻隔位与位2/4/5/6 不在本件（普查③#1/件一    *)
(*   承装）。                                                             *)
(* 依赖：Stdlib Extraction；CW_ConstructiveWorld_219 SqrtfCauchy          *)
(*   SqrtfCauchyArch（RealInterfaceEnhancedMod）。                        *)
(* 构造性注记：全 Set 层语句（le/lt 接口 Set 值谓词 + sigT 证书面）；     *)
(*   零新增遗留声明形；全 Qed（语句面无承认式构造）；宿主与只读树零改；   *)
(*   前缀 uabp1_（全库实扫零撞名）。                                     *)
(* 编译配方：coqc 9.1 直调（vo 树内 -Q . "" 平面命名空间），信任缓存前置。 *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import SqrtfCauchy.
Require Import SqrtfCauchyArch.
Import RealInterfaceEnhancedMod.

(* ============ 位3 重述：阿基米德幂族位（宿主 :58-59 逐字） ============ *)
Theorem uabp1_sfc_arch_decay_slot :
  forall c eps : Real,
  @le Real RealEnhancedReal (@zero Real RealEnhancedReal) c ->
  @lt Real RealEnhancedReal (@zero Real RealEnhancedReal) eps ->
  sigT (fun k : nat =>
    @lt Real RealEnhancedReal
        (@mult Real RealEnhancedReal c (sfc_pow_half k)) eps).
Proof. exact sfcy_arch_decay_slot. Qed.

(* ============ G3 提取检验（一人一目录 _tp1s1_g3out） ============ *)
(* 本体件计算核心＝nat 证书 witness（real_arch 种子链）。提取链     *)
(* 复核；接口投影链（@lt_mult_compat 等实例字段依存）会拉入               *)
(* RealEnhancedReal 记录封装体——按两步判读口径：多态件家规轨（nat 面       *)
(* 归纳/算术核心）magic=0 为过关主判据，记录体封装 magic 为擦除伪影        *)
(* 逐族登记（与上游 sfcy_G3.ml 剖面核验，零新增判据=计数与分布一致）。 *)
Set Extraction Output Directory "_tp1s1_g3out".
Extraction "uabp1s1_G3_arch.ml" sfcy_arch_decay_real.

(* ============ G4 检验：假设闭包审计（Closed 为过关判据） ============ *)
Print Assumptions uabp1_sfc_arch_decay_slot.
