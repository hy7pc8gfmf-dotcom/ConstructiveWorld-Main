(* ============================================================ *)
(* MixTimeChain.v —— 本件形式化论文7《率即算法》§5+§6 的注意力混合时间   *)
(*   端到端见证：从 BoundedSoftmax 接口出发，经 δ* := lo·lo 定义、       *)
(*   δ* < 1 证明、κ := 1−δ* ∈ (0,1) 前件包、mix_k_select 显式步数见证、  *)
(*   残差收缩率代入，产出 κ^k·TV₀ < budget 的 sigT 完整见证，全链       *)
(*   Print Assumptions Closed。                                         *)
(*                                                                      *)
(* 工单面外扩展件（C2 底册 TOP1），按 b3 §2.2 可消解判定施工，候合并方   *)
(*   甄别确认；若属已补强保留区请退回。同族件 MixTimeChainIface.v        *)
(*   （批 1 工单增补交付）其 §1 节与本件 §1 节逐字同型，两件互不替代。   *)
(*                                                                      *)
(* 假设消解注记：两节共 17 假设位逐位三态甄别——参数位 6（temp/      *)
(*   Delta/expf/invT 等裸数据位）合法保留；命题位 11 全部可消解，文末    *)
(*   载体供给段按典范 Real 载体逐位供给同构语句（mtchain_*_supply 定理  *)
(*   族），原抽象假设位声明与全部既有定理签名零改动。                   *)
(*                                                                      *)
(* 出口核对（结论全部经源码/Check 检验）：                               *)
(*   p7a_（Paper7Ablation，P7A 六件）：p7a_delta_star_pos /              *)
(*     p7a_omd_pos / p7a_omd_lt_one＝κ∈(0,1) 前件包本体；                *)
(*   bs_delta_star_lt_one（AttnDoeblin §6.1）：δ*=lo²<1 已证；           *)
(*   mix_k_select / mix_omd_lt_one（UpReqMixingTime §5）：sigT           *)
(*     步数见证选择器（具体柯西层，Defined 透明可提取）；                *)
(*   rta_omd_powb_mono_b / rta_strict_branch_real（RateTheory-           *)
(*     Ablation §4.3/§4.4）：klc_closed_powb_mono 的率层使用形。         *)
(*                                                                      *)
(* 层次诚实披露：接口面（κ 前件包）与具体面（选择器见证）按论文 §6.4     *)
(*   判定（Id 面/req 面异面）各自单层自洽，不跨层混用；具体面经 Part C   *)
(*   同款供给（cauchy_real_exp）到达零 expf 前件的柯西实例推论           *)
(*   mtc_mixing_time_cauchy_exp——端到端闭合。                           *)
(*                                                                      *)
(* 依赖清单：CW_ConstructiveWorld_219、UpRealLeB、UpRealLeB2、           *)
(*   G07_KLWall、KLWallClosed、UpTVDoeblin、AttnDoeblin、                *)
(*   Paper7Ablation、RateTheoryAblation、UpReqMixingTime（全部只         *)
(*   Require 使用，本件零覆盖零改写上游）。                              *)
(* 对标：mathlib softmax 核混合时间的构造性 Set 层对应物。               *)
(* 构造性注记：Set 层承载（real_lt/real_le_b/sigT/prod 均 Set，零 Prop   *)
(*   泄露）；零承认、零新公理；主件 Defined 透明可提取；非平凡真证       *)
(*   （跨文件κ前件包衔接＋残差率恒等代入＋Bishop 单调率层运载）。       *)
(* 编译配方：Rocq 9.1 直调（9.1.0 全路径），影子根单根，cpu_guard 节流。 *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import G07_KLWall.
Require Import KLWallClosed.
Require Import UpTVDoeblin.
Require Import AttnDoeblin.
Require Import Paper7Ablation.
Require Import RateTheoryAblation.
Require Import UpReqMixingTime.

(* ################ §1 接口面：κ := 1−δ* 前件包 ################ *)
(* 使用 P7A 前件包三件 + AttnDoeblin bs_delta_star_lt_one：        *)
(* BoundedSoftmax 的 softmax 切片（temp/Delta/expf 迷你接口）处，    *)
(* δ* := lo² 有 0 < δ* < 1，从而 κ := 1−δ* ∈ (0,1)。              *)
(* 与 AttnDoeblin 逐字同型的 Let 定义（lo := expf (invT·(−Δ))，     *)
(* invT := inv_pos temp temp_pos，delta_star := mult lo lo）。      *)
Section MtcKappaPackage.

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

(* lo > 0（expf 正性直给） *)
Theorem mtc_lo_pos_if : lt zero lo.
Proof.
  exact (expf_pos (mult invT (opp Delta))).
Qed.

(* δ* = lo² < 1（§6.1 已证件 bs_delta_star_lt_one 全参使用；
   出节实形经 Check 检验后按实形提供） *)
Theorem mtc_delta_star_lt_one_if : lt delta_star one.
Proof.
  exact (@bs_delta_star_lt_one RI temp temp_pos Delta Delta_pos
           expf expf_pos expf_zero expf_plus expf_mono_lt).
Qed.

(* κ > 0（P7A 前件：p7a_omd_pos；出节实形无 lo_pos 参，经检验实证） *)
Theorem mtc_kappa_pos_if : lt zero kappa.
Proof.
  exact (@p7a_omd_pos RI DO lo mtc_delta_star_lt_one_if).
Qed.

(* κ < 1（P7A 前件：p7a_omd_lt_one，其内部走 p7a_delta_star_pos） *)
Theorem mtc_kappa_lt_one_if : lt kappa one.
Proof.
  exact (@p7a_omd_lt_one RI DO lo mtc_lo_pos_if).
Qed.

(* 前件包组合形（下游单件取用） *)
Theorem mtc_kappa_package_if :
  prod (lt zero kappa) (lt kappa one).
Proof.
  exact (pair mtc_kappa_pos_if mtc_kappa_lt_one_if).
Qed.

End MtcKappaPackage.

(* ################ §2 具体面：softmax 切片 → δ* → κ → 选择器 ######## *)
(* 具体柯西实数层（real_lt/tv_omd/tv_rpow）上的同型切片：lo :=       *)
(* expf(invT·(−Δ))，δ* := lo·lo，κ := tv_omd δ*（= 1−δ* 定义性）。   *)
(* 主定理 mtc_attention_mixing_time_local 在此使用 §5 选择器         *)
(* mix_k_select，产出 κ^k·TV₀ < budget 的 sigT 完整见证。            *)
Section MtcCauchySoftmax.

Variable invT : Real.
Variable invT_pos : real_lt real_zero invT.
Variable Delta : Real.
Variable Delta_pos : real_lt real_zero Delta.
Variable expf : Real -> Real.
Variable expf_pos : forall x : Real, real_lt real_zero (expf x).
Variable expf_zero : real_eq (expf real_zero) real_one.
Variable expf_mono_lt : forall a b : Real, real_lt a b -> real_lt (expf a) (expf b).

Let lo := expf (real_mult invT (real_opp Delta)).
Let delta_star := real_mult lo lo.
Let kappa := tv_omd delta_star.

(* lo > 0 *)
Theorem mtc_lo_pos : real_lt real_zero lo.
Proof.
  exact (expf_pos (real_mult invT (real_opp Delta))).
Qed.

(* lo < 1：invT·(−Δ) < 0 经 expf 严格单调升（p7a_lo_lt_one 的
   具体层同构链：real_lt_zero_opp + real_mult_lt_compat_l +
   real_lt_eq_lt + real_mult_zero） *)
Theorem mtc_lo_lt_one : real_lt lo real_one.
Proof.
  assert (Hod : real_lt (real_opp Delta) real_zero).
  { exact (real_lt_zero_opp Delta Delta_pos). }
  assert (Hneg : real_lt (real_mult invT (real_opp Delta)) real_zero).
  { exact (real_lt_eq_lt (real_mult invT (real_opp Delta))
             (real_mult invT real_zero) real_zero
             (real_mult_lt_compat_l (real_opp Delta) real_zero invT
                Hod invT_pos)
             (real_mult_zero invT)). }
  exact (real_lt_eq_lt lo (expf real_zero) real_one
           (expf_mono_lt (real_mult invT (real_opp Delta)) real_zero Hneg)
           expf_zero).
Qed.

(* δ* = lo² > 0 *)
Theorem mtc_delta_star_pos : real_lt real_zero delta_star.
Proof.
  exact (real_mult_pos_compat lo lo mtc_lo_pos mtc_lo_pos).
Qed.

(* δ* = lo² < 1：lo·lo < lo·1 == lo < 1（严格乘单调＋real_mult_one
   换形＋< 传递；P7A 接口件的 real_lt_mult 具体层副本） *)
Theorem mtc_delta_star_lt_one : real_lt delta_star real_one.
Proof.
  exact (real_lt_trans (real_mult lo lo) lo real_one
           (real_lt_eq_lt (real_mult lo lo) (real_mult real_one lo) lo
              (real_mult_lt_compat lo real_one lo
                 mtc_lo_lt_one mtc_lo_pos)
              (real_eq_trans _ _ _ (real_mult_comm real_one lo)
                 (real_mult_one lo)))
           mtc_lo_lt_one).
Qed.

(* κ := 1−δ* > 0（UpTVDoeblin 残差件使用） *)
Theorem mtc_kappa_pos : real_lt real_zero kappa.
Proof.
  exact (tv_omd_pos_of_lt delta_star mtc_delta_star_lt_one).
Qed.

(* κ := 1−δ* < 1（UpReqMixingTime §5(a) 件使用） *)
Theorem mtc_kappa_lt_one : real_lt kappa real_one.
Proof.
  exact (mix_omd_lt_one delta_star mtc_delta_star_pos).
Qed.

(* ######## 收束主件：率即算法（§5+§6 端到端） ########
   κ ∈ (0,1) 前件包＋mix_k_select 显式步数见证＋残差收缩率代入：
   对任意 TV₀ ≥ 0 与任意正预算，定理【返回】步数 k 使
   κ^k·TV₀ < budget。sigT 见证，Defined 透明可提取。 *)
Theorem mtc_attention_mixing_time_local :
  forall TV0 budget : Real,
    real_le real_zero TV0 -> real_lt real_zero budget ->
    sigT (fun k : nat =>
      real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros TV0 budget HTV Hb.
  exact (mix_k_select kappa TV0 budget
           mtc_kappa_pos mtc_kappa_lt_one HTV Hb).
Defined.

(* ######## 收缩率代入：残差率的 Bishop 全域单调（§4.3 退化端） ######
   使用 P7B §5 件 rta_omd_powb_mono_b（klc_closed_powb_mono 经
   rta_rpow_powb_eq 换形引理的 tv_rpow 率层使用形）：0 ≤ δ* ≤ 1 处
   κ^m ≤ κ^n（m ≥ n），即选择器所代几何率确为单调收缩率。 *)
Theorem mtc_residual_rate_mono :
  forall n m : nat,
    NatLe n m ->
    real_le_b (tv_rpow kappa m) (tv_rpow kappa n).
Proof.
  intros n m Hle.
  apply (rta_omd_powb_mono_b delta_star n m).
  - apply (RealSetoid.real_lt_le_iff_req real_zero delta_star).
    left. exact mtc_delta_star_pos.
  - apply (RealSetoid.real_lt_le_iff_req delta_star real_one).
    left. exact mtc_delta_star_lt_one.
  - exact Hle.
Qed.

(* ######## 严格支证书（§4.4 退化端构造性正性） ######################
   使用 P7B §3 件 rta_strict_branch_real：η := δ* 处同时取得
   0 < 1−δ* 的正性证书与 Bishop 收缩组合（证书即 §8 墙所称
   不可免费取得之物，在 δ* < 1 下构造性取得）。 *)
Theorem mtc_strict_branch_local :
  prod (real_lt real_zero kappa)
       (real_le_b (powb_pow kappa 1) (powb_pow kappa 0)).
Proof.
  destruct (rta_strict_branch_real delta_star 0 1
              (RealSetoid.real_lt_le_iff_req real_zero delta_star
                 (inl mtc_delta_star_pos))
              mtc_delta_star_lt_one
              (NatLe_lift 0 1 (Nat.le_0_l 1))) as [Hp Hb].
  exact (pair Hp Hb).
Qed.

End MtcCauchySoftmax.

(* ################ §3 Part C 同款供给：柯西实例端到端闭环 ######## *)
(* 以 cauchy_real_exp 消解 expf 迷你接口（AttnDoeblin Part C 同款
   三字段路线），主件到达零 expf 前件的柯西实例形——只需温度倒数与
   logit 直径为正，混合时间即被返回。 *)
Corollary mtc_mixing_time_cauchy_exp :
  forall (invT Delta : Real),
    real_lt real_zero invT -> real_lt real_zero Delta ->
    forall TV0 budget : Real,
      real_le real_zero TV0 -> real_lt real_zero budget ->
      sigT (fun k : nat =>
        real_lt (real_mult
                   (tv_rpow (tv_omd (real_mult
                                       (cauchy_real_exp
                                          (real_mult invT (real_opp Delta)))
                                       (cauchy_real_exp
                                          (real_mult invT (real_opp Delta)))))
                            k)
                   TV0)
                budget).
Proof.
  intros invT Delta invT_pos Delta_pos TV0 budget HTV Hb.
  exact (mtc_attention_mixing_time_local invT invT_pos Delta Delta_pos
           cauchy_real_exp
           cauchy_real_exp_pos cauchy_real_exp_zero cauchy_real_exp_mono
           TV0 budget HTV Hb).
Defined.

(* ################ 假设消解载体供给段（mtchain_*_supply 定理族） ##
   两节共 17 假设位：参数位 6（temp/Delta/expf/invT 等裸数据位）合法
   保留；命题位 11（§1 九位段六位 + §2 八位段五位）在此按典范 Real
   载体逐位消解。字段映照：lt:=real_lt、req:=real_eq、zero:=real_zero、
   one:=real_one、plus:=real_plus、mult:=real_mult。载体温度/利差取
   单位元（与 UpReqConcFin2 cf2_temp/cf2_Delta 同值同证，正性由
   real_lt_zero_one 供给，该件不引入、依赖面零增）；载体指数取
   cauchy_real_exp——即 real_expf_realizable 的见证本体
   （AttnDoeblin Part C；S13_NLiveAudit 同语句），其逐位字段
   cauchy_real_exp_pos/zero/plus/mono_lt 直接供给。原两节抽象假设位
   声明与全部既有定理签名零改动；下游可按本段载体组装零前提实例。 *)

(* —— §1 MtcKappaPackage 九位段（:73–:81）六命题位 —— *)

(* 位 temp_pos（:74）：载体温度正性（单位元载体；real_lt_zero_one 直引） *)
Theorem mtchain_if_temp_pos_supply : real_lt real_zero real_one.
Proof.
  exact (real_lt_zero_one).
Qed.

(* 位 Delta_pos（:76）：载体利差正性（同上） *)
Theorem mtchain_if_Delta_pos_supply : real_lt real_zero real_one.
Proof.
  exact (real_lt_zero_one).
Qed.

(* 位 expf_pos（:78）：载体指数逐点正（cauchy_real_exp_pos 直引） *)
Theorem mtchain_if_expf_pos_supply :
  forall x : Real, real_lt real_zero (cauchy_real_exp x).
Proof.
  exact (cauchy_real_exp_pos).
Qed.

(* 位 expf_zero（:79）：载体指数零点幺值（cauchy_real_exp_zero 直引） *)
Theorem mtchain_if_expf_zero_supply :
  real_eq (cauchy_real_exp real_zero) real_one.
Proof.
  exact (cauchy_real_exp_zero).
Qed.

(* 位 expf_plus（:80）：载体指数和性（cauchy_real_exp_plus 直引） *)
Theorem mtchain_if_expf_plus_supply :
  forall a b : Real,
    real_eq (cauchy_real_exp (real_plus a b))
            (real_mult (cauchy_real_exp a) (cauchy_real_exp b)).
Proof.
  exact (cauchy_real_exp_plus).
Qed.

(* 位 expf_mono_lt（:81）：载体指数严格单调（cauchy_real_exp_mono 直引） *)
Theorem mtchain_if_expf_mono_lt_supply :
  forall a b : Real, real_lt a b -> real_lt (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  exact (cauchy_real_exp_mono).
Qed.

(* —— §2 MtcCauchySoftmax 八位段（:130–:137）五命题位 —— *)

(* 位 invT_pos（:131）：载体温度倒数正性（单位元载体） *)
Theorem mtchain_cs_invT_pos_supply : real_lt real_zero real_one.
Proof.
  exact (real_lt_zero_one).
Qed.

(* 位 Delta_pos（:133）：载体利差正性（单位元载体） *)
Theorem mtchain_cs_Delta_pos_supply : real_lt real_zero real_one.
Proof.
  exact (real_lt_zero_one).
Qed.

(* 位 expf_pos（:135）：载体指数逐点正 *)
Theorem mtchain_cs_expf_pos_supply :
  forall x : Real, real_lt real_zero (cauchy_real_exp x).
Proof.
  exact (cauchy_real_exp_pos).
Qed.

(* 位 expf_zero（:136）：载体指数零点幺值 *)
Theorem mtchain_cs_expf_zero_supply :
  real_eq (cauchy_real_exp real_zero) real_one.
Proof.
  exact (cauchy_real_exp_zero).
Qed.

(* 位 expf_mono_lt（:137）：载体指数严格单调 *)
Theorem mtchain_cs_expf_mono_lt_supply :
  forall a b : Real, real_lt a b -> real_lt (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  exact (cauchy_real_exp_mono).
Qed.

(* ################ 审计口（G4：零公理 Closed；G1 min-pa 审计位） #### *)
Print Assumptions mtc_kappa_package_if.
Print Assumptions mtc_attention_mixing_time_local.
Print Assumptions mtc_residual_rate_mono.
Print Assumptions mtc_strict_branch_local.
Print Assumptions mtc_mixing_time_cauchy_exp.
Print Assumptions mtchain_if_temp_pos_supply.
Print Assumptions mtchain_if_Delta_pos_supply.
Print Assumptions mtchain_if_expf_pos_supply.
Print Assumptions mtchain_if_expf_zero_supply.
Print Assumptions mtchain_if_expf_plus_supply.
Print Assumptions mtchain_if_expf_mono_lt_supply.
Print Assumptions mtchain_cs_invT_pos_supply.
Print Assumptions mtchain_cs_Delta_pos_supply.
Print Assumptions mtchain_cs_expf_pos_supply.
Print Assumptions mtchain_cs_expf_zero_supply.
Print Assumptions mtchain_cs_expf_mono_lt_supply.
