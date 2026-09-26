(* ============================================================
   MixTimeChainIface —— 使命行：本件形式化 BoundedSoftmax 接口层注意力混合
   时间的可提取步数见证：以 kappa := 1 − (e^(−Delta/T))² ∈ (0,1) 封装为前提包，
   经参数面适配桥接入 ums_k_select，主定理 mti_amt_attention_mixing_time
   对任意非负初值 TV0 与正预算返回步数 k 使 kappa^k·TV0 ＜ budget（sigT 形）。
   依赖：CW_ConstructiveWorld_219、S04_RealExpLogConv、AttnDoeblin、
   Paper7Ablation、UpReqUMixSelect；载体供给节另引 UpReqConcFin2
   （cf2_temp_pos/cf2_Delta_pos）与 UpAblD1_expf_pack（real_expf_realizable
   的逐位拆包引用形，uabd1x_expf 系）。
   构造性注记：语句面全 Set 层（量词 R/nat；比较全接口 lt/le Set 字段；
   sigT 步数见证第二分量 lt 值型 Set 层）；六前提位的载体供给节在典范
   Real 载体 req 面逐位消解（原抽象假设位声明与既有定理签名零改动）；
   零承认、零经典逻辑、公理面零新增，Print Assumptions 预期全 Closed；
   主件 Defined 透明可提取。出节实形：ums_k_select 出节首参是
   lt_plus_compat_lt_le 位（UMixSelect 诚实接口 Variable，
   forall a b c d, lt a b -> le c d -> lt (plus a c) (plus b d)），
   其后才是 kappa TV0 budget、四前件（lt zero kappa / lt kappa one /
   le zero TV0 / lt zero budget）、Arch 位（forall x, le zero x ->
   sigT (fun N => lt x (ums_scale (S N) one))）；
   结论 sigT (fun k => lt (mult (r_pow kappa k) TV0) budget)。
   p7a_omd_pos 无 lo_pos 参：forall lo, lt (mult lo lo) one ->
   lt zero (minus one (mult lo lo))；p7a_omd_lt_one 以 lo_pos 为前提。
   编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。
   ============================================================*)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
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
Require Import AttnDoeblin.
Require Import Paper7Ablation.
Require Import UpReqUMixSelect.
Require Import UpReqConcFin2.
Require Import UpAblD1_expf_pack.

(* ################ 6.1 softmax 切片 kappa 前件包 ################ *)
(* 与 MixTimeChain.v 6.1（MtcKappaPackage）逐字同型的 Let 定义：     *)
(*   invT := inv_pos temp temp_pos，lo := expf (invT·(−Delta))，     *)
(*   delta_star := mult lo lo，kappa := minus one delta_star。       *)
(* 参数面适配桥与主定理同节共存，kappa 包被主定理同面真使用（接口层单层 *)
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

(* delta* = lo² ＜ 1（6.1 已证件 bs_delta_star_lt_one 九参全显使用；
   出节实形经语句形核验后按实形提供实参） *)
Theorem mti_delta_star_lt_one_if : lt delta_star one.
Proof.
  exact (@bs_delta_star_lt_one RI temp temp_pos Delta Delta_pos
           expf expf_pos expf_zero expf_plus expf_mono_lt).
Qed.

(* kappa ＞ 0（P7A C5 使用：p7a_omd_pos 无 lo_pos 参，语句核验；
   结论形 lt zero (minus one (mult lo lo)) 与 Let kappa 定义性重合） *)
Theorem mti_kappa_pos_if : lt zero kappa.
Proof.
  exact (@p7a_omd_pos RI DO lo mti_delta_star_lt_one_if).
Qed.

(* kappa ＜ 1（P7A C6 使用：p7a_omd_lt_one 以 lo_pos 为前提） *)
Theorem mti_kappa_lt_one_if : lt kappa one.
Proof.
  exact (@p7a_omd_lt_one RI DO lo mti_lo_pos_if).
Qed.

(* 前件包封装形（参数面适配桥单参数位取用） *)
Theorem mti_kappa_package_if :
  prod (lt zero kappa) (lt kappa one).
Proof.
  exact (pair mti_kappa_pos_if mti_kappa_lt_one_if).
Qed.

(* ################ 参数面适配桥：kappa 包 → ums_k_select 使用面 ########
   参数面差位三处：lpc（UMixSelect 诚实接口 lt_plus_compat_lt_le，
   出节首参）、le zero TV0（接口 le 面，bs 包不带）、Arch 位
   （nat-尺度 ums_scale (S N) one 形）。桥接引理以抽象 kappa ∈ (0,1)
   封装形为输入，出 ums_k_select 的 sigT 见证出形 —— 全部差位显式
   消解，UMixSelect 出节实形由此冻结为具名可用件。 *)
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

(* ################ 主定理：接口层构造路线（6.3 重交付） ##################
   softmax 切片 kappa 包 → 参数面适配桥 → ums_k_select：对任意 TV0 ≥ 0 与
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

(* ################ 六前提位的载体供给节（逐位消解） ################
   原六假设位（temp_pos/Delta_pos/expf_pos/expf_zero/expf_plus/
   expf_mono_lt）为 RI 面抽象证书位；本节在典范 Real 载体 req 面
   逐位供给同构语句（字段映照：lt:=real_lt、req:=real_eq、
   zero:=real_zero、one:=real_one、plus:=real_plus、mult:=real_mult）。
   载体：温度=cf2_temp、利差=cf2_Delta（UpReqConcFin2），指数函数=
   uabd1x_expf（real_expf_realizable 的签名投影，其逐位拆包引用形
   uabd1x_expf_pos/zero/plus/mono_lt 见 UpAblD1_expf_pack）。
   原抽象假设位声明与既有定理签名零改动；出节后下游可按本节载体
   组装零前提实例。 *)
Section MtiCarrierSupply.

(* 位 temp_pos：载体温度正性（cf2_temp_pos 全参直引） *)
Theorem mti_temp_pos_supply : real_lt real_zero cf2_temp.
Proof. exact (cf2_temp_pos). Qed.

(* 位 Delta_pos：载体利差正性（cf2_Delta_pos 全参直引） *)
Theorem mti_Delta_pos_supply : real_lt real_zero cf2_Delta.
Proof. exact (cf2_Delta_pos). Qed.

(* 位 expf_pos：载体指数逐点正（uabd1x_expf_pos 直引） *)
Theorem mti_expf_pos_supply : forall x : Real, real_lt real_zero (uabd1x_expf x).
Proof. exact (uabd1x_expf_pos). Qed.

(* 位 expf_zero：载体指数零点幺值（uabd1x_expf_zero 直引） *)
Theorem mti_expf_zero_supply : real_eq (uabd1x_expf real_zero) real_one.
Proof. exact (uabd1x_expf_zero). Qed.

(* 位 expf_plus：载体指数和性（uabd1x_expf_plus 直引） *)
Theorem mti_expf_plus_supply : forall a b : Real,
  real_eq (uabd1x_expf (real_plus a b))
          (real_mult (uabd1x_expf a) (uabd1x_expf b)).
Proof. exact (uabd1x_expf_plus). Qed.

(* 位 expf_mono_lt：载体指数严格单调（uabd1x_expf_mono_lt 直引） *)
Theorem mti_expf_mono_lt_supply : forall a b : Real,
  real_lt a b -> real_lt (uabd1x_expf a) (uabd1x_expf b).
Proof. exact (uabd1x_expf_mono_lt). Qed.

End MtiCarrierSupply.

(* ################ 审计口（G4：零公理 Closed；G1 min-pa 审计位） #### *)
Print Assumptions mti_kappa_package_if.
Print Assumptions mti_select_of_package.
Print Assumptions mti_amt_attention_mixing_time.
Print Assumptions mti_temp_pos_supply.
Print Assumptions mti_Delta_pos_supply.
Print Assumptions mti_expf_pos_supply.
Print Assumptions mti_expf_zero_supply.
Print Assumptions mti_expf_plus_supply.
Print Assumptions mti_expf_mono_lt_supply.
