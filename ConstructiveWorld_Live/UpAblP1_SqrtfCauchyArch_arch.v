(* ============================================================ *)
(* ToyR 玩具证替换件 —— T267 台账席 战役包AB（tier2 十八批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   uabp1_sfc_arch_decay_slot（原 L35，1 句玩具证）                      *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T339 恒等守恒更正注记】2026-09-22 包AW十四 台账席（恒等头注更正第四批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查定谳、T317（包AV六）试点定谳：本件实测为 *)
(* 恒等守恒——清单所列 1 槽证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 槽＋恒等守恒 1 槽；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337／T339 台账。 *)
(* 附记：T277 判级全文恒等；Y 域收尾＋AB 域收尾＋AD 域直推第四批（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblP1_SqrtfCauchyArch_arch.v                                *)
(*                                                               *)
(* 席位：FA-P1S1 论文域消融施工席（三换装批·件二）｜日期：20260919    *)
(* 工单：attn/_tfap1_普查报告-20260919.md ④批3（假设位3 阿基米德       *)
(*       幂族换装复验，★★☆）；方法论：E-STAGING-FA3 三分类卡。        *)
(* 目的：宿主 SqrtfCauchy 假设位3 sfc_arch_decay（:58-59，宿主自称      *)
(*       「可消解但最重划归独立后续件」——该后续件已落库）换装：          *)
(*       论文4 §4.7 消融注已引放电件，本批把宿主假设位的 discharge 形    *)
(*       补齐成独立伴生件。                                            *)
(* 放电母本（逐字行号直取）：                                           *)
(*   本体 sfcy_arch_decay_real@SqrtfCauchyArch:266（五步构造：          *)
(*     S07:2762 real_arch 种子 + Qlt→lt 桥 + 2^n 归纳 + pow_half 归拢    *)
(*     + 乘正完成）；显式应用桥 sfcy_arch_decay_slot@SqrtfCauchyArch:434 *)
(*     （宿主位语句逐字实例投影面，exact 一行）。                       *)
(* 语句：宿主 :58-59 逐字（R:=Real 实例投影形）；sfc_pow_half 宿主裸调   *)
(*       （R:=Real 由实例 RealEnhancedReal 解析，与母本 SqrtfCauchyArch  *)
(*       同式）。                                                       *)
(* 分级：N1 直喂零新数学——证明体 exact 一行喂 sfcy_arch_decay_slot。    *)
(* 消费位（宿主，只读对账）：:1198（半衰减链）/ :1325（sfc_newton_cauchy  *)
(*       组装③）。                                                     *)
(* 位账：位1 永久墙位与位2/4/5/6 不在本件（普查③#1/件一承装）。         *)
(* 纪律：全 Set 层语句（le/lt 接口 Set 值谓词 + sigT 证书面）；          *)
(*       零新增挂账声明形；全 Qed；宿主与只读树零改；                    *)
(*       前缀 uabp1_（全库实扫零撞名）。                                *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import SqrtfCauchy.
Require Import SqrtfCauchyArch.
Import RealInterfaceEnhancedMod.

(* ============ 位3 换装：阿基米德幂族位（宿主 :58-59 逐字） ============ *)
Theorem uabp1_sfc_arch_decay_slot :
  forall c eps : Real,
  @le Real RealEnhancedReal (@zero Real RealEnhancedReal) c ->
  @lt Real RealEnhancedReal (@zero Real RealEnhancedReal) eps ->
  sigT (fun k : nat =>
    @lt Real RealEnhancedReal
        (@mult Real RealEnhancedReal c (sfc_pow_half k)) eps).
Proof. exact sfcy_arch_decay_slot. Qed.

(* ============ G3 提取探针（一人一目录 _tp1s1_g3out） ============ *)
(* 本体件计算核心＝nat 证书 witness（real_arch 种子链）。提取经本席链     *)
(* 复验；接口投影链（@lt_mult_compat 等实例字段消费）会拉入               *)
(* RealEnhancedReal 记录打包体——按两步判读口径：多态件家规轨（nat 面       *)
(* 归纳/算术核心）magic=0 为过关主判据，记录体打包 magic 为擦除伪影        *)
(* 逐族登记（与上游 sfcy_G3.ml 剖面对账，本席零新增判据=计数与分布一致）。 *)
Set Extraction Output Directory "_tp1s1_g3out".
Extraction "uabp1s1_G3_arch.ml" sfcy_arch_decay_real.

(* ============ G4 探针：假设闭包审计（Closed 为过关判据） ============ *)
Print Assumptions uabp1_sfc_arch_decay_slot.
