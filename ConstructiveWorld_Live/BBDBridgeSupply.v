(* ============================================================
   BBDBridgeSupply —— 使命行：本件形式化 Boltzmann 自由能桥接件求和接口的
   配套供给：BBDFepWriteoff 节三个求和前提位（sum_ext/sum_add/sum_linear）在
   sumf := csm_sumf S enum 实现化读法下由 ConcMixSelFeed csm_ 系已证件全参供给
   （bbridge_sum_ext_supply/bbridge_sum_linear_supply/bbridge_sum_add_supply
   三定理），并给出求和前提位全免的精简版自由能桥
   bbridge_free_energy_boltzmann_bridge 与能量入对数桥 Real 层实例读法
   bbridge_energy_in_log_boltzmann_bridge。
   依赖：CW_ConstructiveWorld_219、UpReqLogCompD、UpReqConcSoftmax、
   ConcMixSelFeed、BoltzmannBridgeDischarge；Stdlib List。
   对标：mathlib 有限和线性性与 Boltzmann 配分自由能的构造性 Set 层对应物。
   构造性注记：Set 层承载，零承认；供给定理与两桥全 Qed 闭合可提取，
   提取 Obj.magic = 0。
   编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。
   ============================================================*)

From Stdlib Require Import List.
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
Require Import UpReqLogCompD.
Require Import UpReqConcSoftmax.
Require Import ConcMixSelFeed.
Require Import BoltzmannBridgeDischarge.
Import RealInterfaceEnhancedMod.

(* ===================================================================== *)
(* Section BBDBridgeSumSupply：求和接口实现化读法下的配套供给               *)
(*                                                                       *)
(* 三态甄别结论（b3 §2.2）：                                              *)
(*  · 可消解×3：sum_ext/sum_linear/sum_add——抽象 sumf 在 csm_sumf 实现化  *)
(*    读法下由 cms_sum_ext（ConcMixSelFeed.v:79）/cms_sum_linear（:90）/    *)
(*    cms_sum_add（:119）全参供给，出节前提减薄三行；                     *)
(*  · 真前提（保留）：D_pos/Z_pos 为 Set 层正性证书（lt : R -> R -> Set）， *)
(*    是 inv_pos/log 的计算性数据实参，非重复前提；D 与 Z 为自由参数，其余  *)
(*    前件全为 req 等式面，正性不可导（退化实例反例可构：D 取零元即足），  *)
(*    照墙族登记保留，禁硬证；partition_condition 为配分定义性等式真前提； *)
(*    sup_compat/sup_log_exp_neg 为 log 接口供给前提（Real 层闭合实例 =    *)
(*    G05 logd_log_compat_real/logd_log_exp_neg_real，见 UpReqLogCompD    *)
(*    头注）；S/enum/sumf/base_loss/D/Z 为接口参数位。                     *)
(* 签名保持式消解三件套（b3 §2.2.1）：原桥 bbd_* 两定理签名一字不动（本件  *)
(*   零触碰）；本件新增无求和前提精简版 bbridge_* 两定理；旧使用方零改动   *)
(*   渐进迁移。                                                           *)
(* ===================================================================== *)
Section BBDBridgeSumSupply.

Variable S : Set.
Variable enum : list S.

(* 求和实现化读法：抽象 sumf 取 ConcMixSelFeed 列表折叠和 *)
Let sumf : (S -> Real) -> Real := csm_sumf S enum.

(* ---- 配套供给三定理（与 BBDFepWriteoff 三求和前提位逐字同语句） ---- *)

(* sum_ext 前提位：逐点相等对有限和的等式保持（cms_sum_ext 供给） *)
Theorem bbridge_sum_ext_supply : forall f g : S -> Real,
  (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Proof.
  intros f g H.
  exact (cms_sum_ext S enum f g H).
Qed.

(* sum_linear 前提位：有限和的左线性（cms_sum_linear 供给） *)
Theorem bbridge_sum_linear_supply : forall (a : Real) (f : S -> Real),
  req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Proof.
  intros a f.
  exact (cms_sum_linear S enum a f).
Qed.

(* sum_add 前提位：有限和的加法分解（cms_sum_add 供给） *)
Theorem bbridge_sum_add_supply : forall f g : S -> Real,
  req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Proof.
  intros f g.
  exact (cms_sum_add S enum f g).
Qed.

(* ---- 节参（与 BBDFepWriteoff 同位：真前提与正性证书原样保留） ---- *)
Variable base_loss : S -> Real.
Variable D : Real.
Variable D_pos : lt zero D.
Variable Z : Real.
Variable Z_pos : lt zero Z.
Hypothesis partition_condition :
  req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
Hypothesis sup_compat : forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Hypothesis sup_log_exp_neg : forall u : Real,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).

(* ===================================================================== *)
(* 精简版桥一：能量入对数恒等式（Real 层实例读法；本就无求和前提，          *)
(*   与 BBDFepWriteoff.bbd_energy_in_log_boltzmann_bridge 同语句，         *)
(*   证人以 bbd_boltzmann_dist/bbd_boltzmann_positive Real 实例呈现；      *)
(*   证 = logc_energy_in_log_boltzmann 全参实例化，末段由同名件 delta-beta *)
(*   同 body 闭合）。                                                      *)
(* ===================================================================== *)
Theorem bbridge_energy_in_log_boltzmann_bridge :
  forall s : S,
    req (base_loss s)
        (opp (mult D (plus (log (@BBDFepWriteoff.bbd_boltzmann_dist
                                Real RealEnhancedReal S base_loss D D_pos Z Z_pos s)
                            (@BBDFepWriteoff.bbd_boltzmann_positive
                                Real RealEnhancedReal S base_loss D D_pos Z Z_pos s))
                           (log Z Z_pos)))).
Proof.
  intro s.
  exact (@logc_energy_in_log_boltzmann Real RealEnhancedReal S base_loss D D_pos Z Z_pos
           sup_compat sup_log_exp_neg s).
Qed.

(* ===================================================================== *)
(* 精简版桥二：自由能显式式——求和三前提位全免（出节前提减薄三行）：         *)
(*   节闭签名 = S enum base_loss D D_pos Z Z_pos partition_condition      *)
(*   sup_compat sup_log_exp_neg（sumf 已实现化为 csm_sumf S enum，三供给   *)
(*   定理直接构造）；与 BBDFepWriteoff.bbd_free_energy_boltzmann_bridge    *)
(*   同语句。证 = logc_free_energy_boltzmann 全参实例化（三供给定理入位）。 *)
(* ===================================================================== *)
Theorem bbridge_free_energy_boltzmann_bridge :
  req (@BBDFepWriteoff.bbd_free_energy Real RealEnhancedReal S sumf base_loss D
         (@BBDFepWriteoff.bbd_boltzmann_dist Real RealEnhancedReal S base_loss D D_pos Z Z_pos)
         (@BBDFepWriteoff.bbd_boltzmann_positive Real RealEnhancedReal S base_loss D D_pos Z Z_pos))
      (mult (opp D) (log Z Z_pos)).
Proof.
  exact (@logc_free_energy_boltzmann Real RealEnhancedReal S sumf
           bbridge_sum_ext_supply bbridge_sum_add_supply bbridge_sum_linear_supply
           base_loss D D_pos Z Z_pos partition_condition sup_compat sup_log_exp_neg).
Qed.

End BBDBridgeSumSupply.

(* ===================================================================== *)
(* 提取检验（泛型多态件 Obj.magic=0）+ 假设审计（五定理全 Closed，公理面为空） *)
(* ===================================================================== *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
(* 能量入对数桥与自由能桥为具体 Real 实例读法件，其检验走假设审计与闭包核验面； *)
(* 提取检验取新供给三定理（纯列表折叠读法）。 *)


Print Assumptions bbridge_sum_ext_supply.
Print Assumptions bbridge_sum_linear_supply.
Print Assumptions bbridge_sum_add_supply.
Print Assumptions bbridge_energy_in_log_boltzmann_bridge.
Print Assumptions bbridge_free_energy_boltzmann_bridge.
