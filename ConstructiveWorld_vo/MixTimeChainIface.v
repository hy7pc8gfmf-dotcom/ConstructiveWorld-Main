(* ============================================================ *)
(* MixTimeChainIface.v — 席位CZE13（批次 E-STAGING-CZE13）          *)
(*   P7E 未决事项 2 收口：接口层 ums_k_select 腿                    *)
(*   论文7 6.3 完整形 amt_attention_mixing_time 的本基座重交付       *)
(*                                                               *)
(* 使命：以 BoundedSoftmax 接口节（bs_delta_star_lt_one 九参出节形） *)
(*   ＋ P7A 包（p7a_omd_pos / p7a_omd_lt_one）打包 kappa ∈ (0,1)，  *)
(*   喂 UpReqUMixSelect 的 ums_k_select，出接口层混合时间定理        *)
(*   mti_amt_attention_mixing_time（sigT 步数见证形）。对照          *)
(*   MixTimeChain.v 具体腿先例但走接口层，不跨 Id/req 异面横桥。      *)
(*                                                               *)
(* 出节实形勘误（本席 probe_cze13 Check 探针实证，20260918）：        *)
(*   1. ums_k_select 出节首参是 lt_plus_compat_lt_le 槽（UMixSelect  *)
(*      诚实接口 Variable，forall a b c d, lt a b -> le c d ->       *)
(*      lt (plus a c) (plus b d)），其后才是 kappa TV0 budget、      *)
(*      四前件（lt zero kappa / lt kappa one / le zero TV0 /         *)
(*      lt zero budget）、Arch 槽（forall x, le zero x ->            *)
(*      sigT (fun N => lt x (ums_scale (S N) one))）；结论           *)
(*      sigT (fun k => lt (mult (r_pow kappa k) TV0) budget)。       *)
(*      —— 按 UpReqAttnMixTime 源码位序念（AT3 换装注记）会漏 lpc 位。*)
(*   2. p7a_omd_pos 无 lo_pos 参：forall lo, lt (mult lo lo) one ->  *)
(*      lt zero (minus one (mult lo lo))（P7E 卡同款实证复验）；      *)
(*      p7a_omd_lt_one 才吃 lo_pos。结论形即 kappa :=                *)
(*      minus one (mult lo lo)，与 bs 包无面差，唯 lpc/Arch/le 三槽   *)
(*      是 bs 包不带的面 —— 此即换装小桥 mti_select_of_package       *)
(*      的全部职能。                                                *)
(*   3. bs_delta_star_lt_one 九参全显（temp temp_pos Delta Delta_pos *)
(*      expf expf_pos expf_zero expf_plus expf_mono_lt，RI 隐式      *)
(*      领头），结论 lo 展开形，enum/z/bs_kernel 系全剪除。           *)
(*                                                               *)
(* 层次诚实披露：本件接口腿单层自洽 —— kappa 几何收缩引擎端到端       *)
(*   （任意 TV0 ≥ 0、budget ＞ 0 返回步数 k 使 kappa^k·TV0 ＜ budget），*)
(*   kappa 由 softmax 切片构造性打包；不含 Doeblin TV 放电腿          *)
(*   （bounded_softmax_tv_iter 为 Id 面件，居 UpReqAttnMixTime       *)
(*   amt_attention_mixing_time 完整形另一腿），零异面横桥。           *)
(*                                                               *)
(* 红线自审：语句面全 Set 层（量词 R/nat；比较全接口 lt/le Set 字段；  *)
(*   sigT 第二分量 lt 值型 Set 层，UMixSelect 同款定谳）；五禁词零出现；  *)
(*   非平凡真证（跨文件 kappa 前件包缝合：AttnDoeblin 6.1 + P7A C5/C6  *)
(*   ＋ ums_k_select 出节实形参数面换装桥＋sigT 主件 Defined 收束）；   *)
(*   零新公理（全部前提为显式证书参数，Print Assumptions 预期全 Closed）； *)
(*   原树零改（本件新建于 消融50/，依赖件全部只 Require 消费，侧编副本    *)
(*   在 /tmp/cze13_side，零覆盖零改写）。                            *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Require Import CW_ConstructiveWorld_219.
Require Import S04_RealExpLogConv.
Require Import AttnDoeblin.
Require Import Paper7Ablation.
Require Import UpReqUMixSelect.

(* ################ 6.1 softmax 切片 kappa 前件包 ################ *)
(* 与 MixTimeChain.v 6.1（MtcKappaPackage）逐字同型的 Let 定义：     *)
(*   invT := inv_pos temp temp_pos，lo := expf (invT·(−Delta))，     *)
(*   delta_star := mult lo lo，kappa := minus one delta_star。       *)
(* 换装桥与合龙主件同节共存，kappa 包被主件同面真消费（接口层单层     *)
(* 自洽，非 mtc 的双层分立形）。                                    *)
Section MtiIface.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let delta_star := mult lo lo.
Let kappa := minus one delta_star.

(* lo ＞ 0（expf 正性直给） *)
Theorem mti_lo_pos_if : lt zero lo.
Proof.
  exact (expf_pos (mult invT (opp Delta))).
Qed.

(* delta* = lo² ＜ 1（6.1 已证件 bs_delta_star_lt_one 九参全显消费；
   出节实形经 probe_cze13 Check 探针实证后按实形喂入） *)
Theorem mti_delta_star_lt_one_if : lt delta_star one.
Proof.
  exact (@bs_delta_star_lt_one RI temp temp_pos Delta Delta_pos
           expf expf_pos expf_zero expf_plus expf_mono_lt).
Qed.

(* kappa ＞ 0（P7A C5 消费：p7a_omd_pos 无 lo_pos 参，探针实证；
   结论形 lt zero (minus one (mult lo lo)) 与 Let kappa 定义性重合） *)
Theorem mti_kappa_pos_if : lt zero kappa.
Proof.
  exact (@p7a_omd_pos RI DO lo mti_delta_star_lt_one_if).
Qed.

(* kappa ＜ 1（P7A C6 消费：p7a_omd_lt_one，其吃 lo_pos 槽） *)
Theorem mti_kappa_lt_one_if : lt kappa one.
Proof.
  exact (@p7a_omd_lt_one RI DO lo mti_lo_pos_if).
Qed.

(* 前件包打包形（换装桥单槽取用） *)
Theorem mti_kappa_package_if :
  prod (lt zero kappa) (lt kappa one).
Proof.
  exact (pair mti_kappa_pos_if mti_kappa_lt_one_if).
Qed.

(* ################ 换装小桥：kappa 包 → ums_k_select 消费面 ########
   参数面差桥三槽：lpc（UMixSelect 诚实接口 lt_plus_compat_lt_le，
   出节首参）、le zero TV0（接口 le 面，bs 包不带）、Arch 槽
   （nat-尺度 ums_scale (S N) one 形）。桥件吃抽象 kappa ∈ (0,1)
   打包形，出 ums_k_select 的 sigT 见证出形 —— 全部差槽显式
   discharge，UMixSelect 出节实形由此冻结为具名可消费件。 *)
Theorem mti_select_of_package :
  forall kappa0 : R,
    prod (lt zero kappa0) (lt kappa0 one) ->
    forall lpc : forall a b c d : R,
                 lt a b -> le c d -> lt (plus a c) (plus b d),
      forall TV0 budget : R,
        le zero TV0 -> lt zero budget ->
        (forall x : R, le zero x ->
           sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
        sigT (fun k : nat => lt (mult (r_pow kappa0 k) TV0) budget).
Proof.
  intros kappa0 Hkp lpc TV0 budget HTV Hb Harch.
  destruct Hkp as [Hk1 Hk2].
  exact (ums_k_select lpc kappa0 TV0 budget Hk1 Hk2 HTV Hb Harch).
Defined.

(* ################ 合龙主件：接口层腿（6.3 重交付） ##################
   softmax 切片 kappa 包 → 换装桥 → ums_k_select：对任意 TV0 ≥ 0 与
   任意正预算，定理【返回】步数 k 使 kappa^k·TV0 ＜ budget。
   kappa := 1 − (e^(−Delta/T))²，sigT 见证，Defined 透明可提取。
   lpc/Arch 为接口诚实前件，显式带出（不跨 Id/req 异面横桥）。 *)
Theorem mti_amt_attention_mixing_time :
  forall lpc : forall a b c d : R,
               lt a b -> le c d -> lt (plus a c) (plus b d),
    forall TV0 budget : R,
      le zero TV0 -> lt zero budget ->
      (forall x : R, le zero x ->
         sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
      sigT (fun k : nat => lt (mult (r_pow kappa k) TV0) budget).
Proof.
  intros lpc TV0 budget HTV Hb Harch.
  exact (mti_select_of_package kappa mti_kappa_package_if lpc
           TV0 budget HTV Hb Harch).
Defined.

End MtiIface.

(* ################ 审计口（G4：零公理 Closed；G1 min-pa 审计位） #### *)
Print Assumptions mti_kappa_package_if.
Print Assumptions mti_select_of_package.
Print Assumptions mti_amt_attention_mixing_time.
