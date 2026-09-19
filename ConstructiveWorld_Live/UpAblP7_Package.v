(* ============================================================ *)
(* UpAblP7_Package.v —— 论文7 专项消融战役合龙件（PA7-16 席）                  *)
(*   （战役六件 Require 合龙：展幅夹逼 hi 面联合前件包 × 双覆盖互证总装 ×       *)
(*     LoHi 三位一体跨件收口——「战役合龙与总装」合龙件腿）                     *)
(* 零承认件句式：本件为独立伴生真件，全件定理/推论级真 Qed，                    *)
(*   零 公理／零 承认件／零 参数声明／零 猜想／零 弃证；                        *)
(*   零经典逻辑引设；语句面全 Set 层（合取用 S01 And=prod），零 Prop 泄露；      *)
(*   公理面零新增。                                                           *)
(* 装载面：-Q /tmp/pa7_work ""（工作根挂最前，六件模块名本根唯一）＋            *)
(*   -Q /tmp/czn14_union_full ""（母本联合根；T157 实编通行链）。               *)
(* Require 面（战役六件全点名装设，传递面不隐式依赖）：                         *)
(*   母本三件 Paper7Ablation／LoHiSqueeze／P7BoundedSoftmaxDeep（只读），      *)
(*   实例链四件 S01_BaseRing／S02_CauchyComplete／S03_QExp／                   *)
(*   S07_RealSetoidExpLog（柯西实数面供双覆盖支）。                            *)
(* 消费面（战役六件出口，全真 Qed 母件；出节签名经探针件 About 实测）：         *)
(*   位1 uapk7_flagship_hi_kappa（UpAblP7_P7KappaFlagship 旗舰①，              *)
(*       {RI}{DO}+九显参：κ∈(0,1)∧1<hi）——件一之 1<hi 支与 κ 包支；           *)
(*   位2 uaft_one_le_hi_sq_indep（UpAblP7_P7FlagshipTail ②乙独立链，           *)
(*       {RI}+九显参：1≤hi²）与 uaft_one_le_hi_sq_one（②甲实例装配，          *)
(*       {RI}+五显参）——件一展幅半边与件二 one/one 实例面；                    *)
(*   位3 s1inst_dual_cover（UpAblP7_Paper7Ablation_S1inst 互证总装，           *)
(*       sigT 打包：实例层 wd 装配∧直证双覆盖）——件三首双支；                  *)
(*   位4 uabp7_kappa_in01_package（UpAblP7_Paper7Ablation κ∈(0,1) 前件包，     *)
(*       {RI}{DO}+九显参）——件三之 κ 包 Closed 全称供给支；                    *)
(*   位5 uahlc_lo_one_hi_full（UpAblP7_LoHiCross 夹逼族完整形，                *)
(*       {RI}+四显参：lo<1∧1<hi∧lo<hi 三位一体）——件四首支；                  *)
(*   位6 uahl_omd_bounded_half（UpAblP7_LoHiSqueeze 件七，{RI}{DO} 双隐：      *)
(*       二分之一抽象形 κ 包）——件四次支；另母件 p7a_lo_lt_one                *)
(*       （{RI}+七显参）供 lo<1 直击位。                                       *)
(* 合龙定理面（四件，全 Qed，前缀 uapk_ 本件内防撞）：                          *)
(*   件一 uapk_amp_squeeze_hi_face——展幅夹逼 hi 面联合前件包（九参节）：       *)
(*       （lo<1∧1<hi）∧（1≤hi²∧κ∈(0,1)）四支合璧——PA7-10 合龙建议            *)
(*       原文「甲腿件①与②共享 hi 面，可合成展幅夹逼半边」之实现；共享别名面    *)
(*       invT/lo/hi/δ* 与母本逐字同构。                                        *)
(*   件二 uapk_amp_squeeze_one_face——件一之 one/one 实例面（②甲消费位）。     *)
(*   件三 uapk_dual_cover_kappa_assembly——双覆盖互证总装件：                   *)
(*       （实例层 wd 装配∧直证 wd 双覆盖）∧κ 包 Closed 全称供给句。            *)
(*   件四 uapk_lohi_trinity_supply——LoHi 三位一体跨件收口件：                  *)
(*       （lo<1∧1<hi∧lo<hi）∧二分之一形 κ 包——§6.3 前件包完整供给句。        *)
(* 红线自审：语句面全 Set 层；公理面零新增；独立伴生件不并入原模块；             *)
(*   既有 UpAblP7* 六件零改动；全中文零承认件写法（头注与注释同口径）。         *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import Paper7Ablation.
Require Import LoHiSqueeze.
Require Import P7BoundedSoftmaxDeep.
Require Import UpAblP7_Paper7Ablation.
Require Import UpAblP7_LoHiSqueeze.
Require Import UpAblP7_LoHiCross.
Require Import UpAblP7_Paper7Ablation_S1inst.
Require Import UpAblP7_P7KappaFlagship.
Require Import UpAblP7_P7FlagshipTail.

(* ############ 段一：展幅夹逼 hi 面联合前件包（九参节，件一） ################ *)
(* 节前导九槽逐字复刻旗舰①节（AttnDoeblin BoundedSoftmax 同构面）；            *)
(* 四支消费：lo<1←母件 p7a_lo_lt_one；1<hi←旗舰①右支；                        *)
(* 1≤hi²←②乙独立链；κ∈(0,1)←旗舰①左支——「共享 hi 面」合龙。                 *)

Section UapkSqueeze.

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
Let hi := expf (mult invT Delta).
Let delta_star := mult lo lo.

(* 件一 ←任务令合龙a：旗舰①（κ∈(0,1)∧1<hi）×②乙（1≤hi²）共享 hi 面合成。 *)
Theorem uapk_amp_squeeze_hi_face :
  And (And (lt lo one) (lt one hi))
      (And (le one (mult hi hi))
           (And (lt zero (minus one delta_star))
                (lt (minus one delta_star) one))).
Proof.
  split.
  - (* 展幅夹逼半边：lo<1 ∧ 1<hi *)
    split.
    + exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero expf_mono_lt invT
               (inv_pos_pos temp temp_pos)).
    + exact (snd (@uapk7_flagship_hi_kappa RI DO temp temp_pos Delta Delta_pos
                 expf expf_pos expf_zero expf_plus expf_mono_lt)).
  - (* 展幅对偶半边：1≤hi² ∧ κ∈(0,1) *)
    split.
    + exact (@uaft_one_le_hi_sq_indep RI temp temp_pos Delta Delta_pos
                 expf expf_pos expf_zero expf_plus expf_mono_lt).
    + exact (fst (@uapk7_flagship_hi_kappa RI DO temp temp_pos Delta Delta_pos
                 expf expf_pos expf_zero expf_plus expf_mono_lt)).
Qed.

End UapkSqueeze.

(* ############ 段二：件一之 one/one 实例面（②甲消费位，件二） ################ *)
(* 数据双槽取 one（one_pos 供两处正性位），指数族保持抽象（T146 工法档口径）；  *)
(* 四支消费：lo<1←母件 p7a_lo_lt_one @ one/one；1<hi←旗舰① @ one/one 实例支；  *)
(* 1≤hi²←②甲实例装配；κ∈(0,1)←旗舰①左支 @ one/one。                          *)

Section UapkSqueezeOne.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos one one_pos.
Let lo := expf (mult invT (opp one)).
Let hi := expf (mult invT one).
Let delta_star := mult lo lo.

(* 件二 ←任务令合龙a 实例面：②甲（uaft_one_le_hi_sq_one）真消费位。 *)
Corollary uapk_amp_squeeze_one_face :
  And (And (lt lo one) (lt one hi))
      (And (le one (mult hi hi))
           (And (lt zero (minus one delta_star))
                (lt (minus one delta_star) one))).
Proof.
  split.
  - split.
    + exact (p7a_lo_lt_one one one_pos expf expf_zero expf_mono_lt invT
               (inv_pos_pos one one_pos)).
    + exact (snd (@uapk7_flagship_hi_kappa RI DO one one_pos one one_pos
                 expf expf_pos expf_zero expf_plus expf_mono_lt)).
  - split.
    + exact (uaft_one_le_hi_sq_one expf expf_pos expf_zero expf_plus
               expf_mono_lt).
    + exact (fst (@uapk7_flagship_hi_kappa RI DO one one_pos one one_pos
                 expf expf_pos expf_zero expf_plus expf_mono_lt)).
Qed.

End UapkSqueezeOne.

(* ############ 段三：双覆盖互证总装件（件三） ################################ *)
(* 首双支←s1inst_dual_cover 尾支（projT2：实例层 wd 装配∧直证双覆盖）；        *)
(* 次支←κ 包 Closed 全称供给（uabp7_kappa_in01_package 全参出节形）。          *)
(* 节面 {RI}{DO} 仅供 κ 包支出节装配；双覆盖支自身为柯西闭句（零节依赖）。      *)

Section UapkDual.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* 件三 ←任务令合龙b：实例层 wd 装配∧直证双覆盖 + κ 包 Closed 总装句。 *)
Theorem uapk_dual_cover_kappa_assembly :
  And (And (forall a b : Real,
              real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b))
           (forall a b : Real,
              real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b)))
      (forall (temp : R) (temp_pos : lt zero temp) (Delta : R)
              (Delta_pos : lt zero Delta)
              (expf : R -> R) (expf_pos : forall x : R, lt zero (expf x))
              (expf_zero : Id (expf zero) one)
              (expf_plus : forall a b : R,
                 Id (expf (plus a b)) (mult (expf a) (expf b)))
              (expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b)),
         And (lt zero
                 (minus one
                    (mult (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                          (expf (mult (inv_pos temp temp_pos) (opp Delta))))))
             (lt (minus one
                    (mult (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                          (expf (mult (inv_pos temp temp_pos) (opp Delta)))))
                 one)).
Proof.
  split.
  - (* 双覆盖互证总装：装配形∧直证形（S1inst sigT 尾支整取） *)
    exact (projT2 s1inst_dual_cover).
  - (* κ 包 Closed：全称供给句（九参全显出节形） *)
    intros temp temp_pos Delta Delta_pos expf expf_pos expf_zero expf_plus
      expf_mono_lt.
    exact (@uabp7_kappa_in01_package RI DO temp temp_pos Delta Delta_pos
               expf expf_pos expf_zero expf_plus expf_mono_lt).
Qed.

End UapkDual.

(* ############ 段四：LoHi 三位一体跨件收口件（件四） ########################## *)
(* 首支←LoHiCross 件三（uahlc_lo_one_hi_full：lo<1∧1<hi∧lo<hi 三位一体）；     *)
(* 次支←LoHiSqueeze 首波件七（uahl_omd_bounded_half：二分之一抽象形 κ 包）。    *)
(* 别名面 invT/lo/hi 与 LoHiCross 节同构；half/half2 与首波段四同构。           *)

Section UapkLoHi.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos one one_pos.
Let lo := expf (mult invT (opp one)).
Let hi := expf (mult invT one).
Let half := inv_pos (plus one one) two_pos.
Let half2 := mult half half.

(* 件四 ←任务令合龙c：§6.3 前件包完整供给句（LoHi 侧两位跨件合龙）。 *)
Theorem uapk_lohi_trinity_supply :
  And (And (lt lo one) (And (lt one hi) (lt lo hi)))
      (And (lt zero (minus one half2)) (lt (minus one half2) one)).
Proof.
  split.
  - (* 三位一体完整实例链（LoHiCross 出节形，@ 全显喂 RI 束＋指数族四件） *)
    exact (@uahlc_lo_one_hi_full RI expf expf_pos expf_zero expf_mono_lt).
  - (* 二分之一抽象形 κ 包（LoHiSqueeze 件七，{RI}{DO} 双隐 @ 双喂） *)
    exact (@uahl_omd_bounded_half RI DO).
Qed.

End UapkLoHi.

(* ---- PA 收尾段（逐件 Closed 判读；G4 审查留痕面） ---- *)
Print Assumptions uapk_amp_squeeze_hi_face.
Print Assumptions uapk_amp_squeeze_one_face.
Print Assumptions uapk_dual_cover_kappa_assembly.
Print Assumptions uapk_lohi_trinity_supply.
