(* UpAblP7_Package.v —— 论文 7 消融装配层：有界 softmax 展幅夹逼界与柯西       *) (*   实数指数良定义的跨模块合取供给。使命：本件形式化四条装配命题：                  *)
(*   一、uapk_amp_squeeze_hi_face——展幅夹逼 hi 面联合前提：                    *) (*      lo<1 ∧ 1<hi ∧ 1≤hi² ∧ 0<1-δ*<1，其中 lo=expf(invT·(-Delta))，          *)
(*      hi=expf(invT·Delta)，δ*=lo·lo，invT=inv_pos temp temp_pos。            *) (*   二、uapk_amp_squeeze_one_face——上一命题于温度=展幅=one 处的实例形。       *)
(*   三、uapk_dual_cover_kappa_assembly——cauchy_real_exp 保 real_eq 的        *) (*      良定义双份合取，与 0<1-δ*<1 全称封装前提（记号 κ:=1-δ*）之合取。       *)
(*   四、uapk_lohi_trinity_supply——lo<1∧1<hi∧lo<hi 与 0<1-(1/2)²<1 之合取。   *) (* 依赖清单：S01_BaseRing／S02_CauchyComplete／S03_QExp／S07_RealSetoidExpLog；*)
(*   Paper7Ablation／LoHiSqueeze／P7BoundedSoftmaxDeep；                       *) (*   UpAblP7_Paper7Ablation／UpAblP7_LoHiSqueeze／UpAblP7_LoHiCross／          *)
(*   UpAblP7_Paper7Ablation_S1inst／UpAblP7_P7KappaFlagship／UpAblP7_P7FlagshipTail。 *) (* 对标行：无直接对应物（应用装配层）。                                        *)
(* 构造性注记：四定理均 Qed，零公理／零承认／零参数声明／零猜想／零弃证；      *) (*   零经典逻辑引设；语句面全 Set 层（合取用 S01 And=prod），零 Prop 泄露。     *)
(* 编译配方：9.1 直调（coqc 无 -Q），cpu_guard 包裹，-o 输出临时目录。         *) (* 所引出口清单（均真实标识符，全 Qed）：                                      *)
(*   p7a_lo_lt_one（Paper7Ablation）：任意正 invT 处 lo<1。                    *) (*   uapk7_flagship_hi_kappa（UpAblP7_P7KappaFlagship，{RI}{DO}+九参）：       *)
(*     (0<1-δ* ∧ 1-δ*<1) ∧ 1<hi；取 fst 得 0<1-δ*<1，取 snd 得 1<hi。          *)
(*   uaft_one_le_hi_sq_indep（UpAblP7_P7FlagshipTail，九显参）：1≤hi²。        *)
(*   uaft_one_le_hi_sq_one（UpAblP7_P7FlagshipTail，五显参）：one/one 处 1≤hi²。 *)
(*   s1inst_dual_cover（UpAblP7_Paper7Ablation_S1inst）：sigT 封装；           *)
(*     projT1 为抽象指数良定义之见证，projT2 为柯西实数指数良定义之两份合取。  *)
(*   uabp7_kappa_in01_package（UpAblP7_Paper7Ablation，{RI}{DO}+九参）：       *)
(*     0<1-δ*<1 的封装前提（κ:=1-δ*）。                                        *)
(*   uahlc_lo_one_hi_full（UpAblP7_LoHiCross，{RI}+四参）：                    *)
(*     lo<1 ∧ 1<hi ∧ lo<hi。                                                   *)
(*   uahl_omd_bounded_half（UpAblP7_LoHiSqueeze，{RI}{DO} 隐式）：             *)
(*     0<1-(1/2)²<1（抽象指数函数）。                                          *)
(* 节结构：§1 展幅夹逼 hi 面联合前提（九参节）；§2 one/one 实例形；            *)
(*   §3 双覆盖良定义与 κ 封装前提之合取；§4 LoHi 展幅前提与四分之一界。        *)
(* 记号约定（各节同名同构）：invT=inv_pos temp temp_pos；lo=expf(invT·(-Delta))； *)
(*   hi=expf(invT·Delta)；δ*=lo·lo；half=1/2，half2=(1/2)²。                   *)
(* §2 实例数据：温度=展幅=one，故 invT=1、lo=expf(-1)、hi=expf(1)；            *)
(*   正性前提由 one_pos 供给。                                                 *)
(* §1、§4 节内别名与 UpAblP7_P7KappaFlagship／UpAblP7_LoHiCross                *)
(*   相应节逐字同构，实例替换不改变陈述结构。                                  *)
(* 件末对四定理逐一 Print Assumptions，核验公理依赖为零。                      *)

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

(* ================= §1 展幅夹逼 hi 面联合前提（九参节） ================= *)
(* 九个接口参数（temp、Delta、expf 及其性质）与 uapk7_flagship_hi_kappa 的       *)
(*   前提节同构。四条前提来源：lo<1 由 p7a_lo_lt_one；1<hi 与 0<1-δ*<1           *)
(*   由 uapk7_flagship_hi_kappa 之 snd 与 fst；1≤hi² 由 uaft_one_le_hi_sq_indep。 *)

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

(** uapk_amp_squeeze_hi_face：展幅夹逼 hi 面联合前提——lo<1、1<hi、1≤hi²、0<1-δ*<1 四条合取；由 p7a_lo_lt_one、uapk7_flagship_hi_kappa 与 uaft_one_le_hi_sq_indep 在共享 hi 面上合取装配。 *)
Theorem uapk_amp_squeeze_hi_face :
  And (And (lt lo one) (lt one hi))
      (And (le one (mult hi hi))
           (And (lt zero (minus one delta_star))
                (lt (minus one delta_star) one))).
Proof.
  split.
  - (* 合取左肢：lo<1 ∧ 1<hi *)
    split.
    + exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero expf_mono_lt invT
               (inv_pos_pos temp temp_pos)).
    + exact (snd (@uapk7_flagship_hi_kappa RI DO temp temp_pos Delta Delta_pos
                 expf expf_pos expf_zero expf_plus expf_mono_lt)).
  - (* 合取右肢：1≤hi² ∧ 0<1-δ*<1 *)
    split.
    + exact (@uaft_one_le_hi_sq_indep RI temp temp_pos Delta Delta_pos
                 expf expf_pos expf_zero expf_plus expf_mono_lt).
    + exact (fst (@uapk7_flagship_hi_kappa RI DO temp temp_pos Delta Delta_pos
                 expf expf_pos expf_zero expf_plus expf_mono_lt)).
Qed.

End UapkSqueeze.

(* ================= §2 展幅夹逼于 one/one 处的实例形 ================= *)
(* 温度与展幅两个接口参数均取 one（正性由 one_pos 供给），指数族保持抽象；       *)
(*   此时 invT=1、lo=expf(-1)、hi=expf(1)。1≤hi² 由 uaft_one_le_hi_sq_one        *)
(*   直接供给；1<hi 与 0<1-δ*<1 仍由 uapk7_flagship_hi_kappa 两肢给出。          *)

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

(** uapk_amp_squeeze_one_face：§1 于温度=展幅=one 处的实例形；1≤hi² 一肢由 uaft_one_le_hi_sq_one 直接供给，其余同 §1。 *)
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

(* ================= §3 双覆盖良定义与 κ 封装前提之合取 ================= *)
(* 合取左肢取 s1inst_dual_cover 的第二投影 projT2：cauchy_real_exp 保 real_eq  *)
(*   的良定义双份合取。右肢由 uabp7_kappa_in01_package 全参显式给出：           *)
(*   0<1-δ*<1（κ:=1-δ*）；节前提 {RI}{DO} 仅为右肢所需。                        *)

Section UapkDual.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(** uapk_dual_cover_kappa_assembly：cauchy_real_exp 保 real_eq 的良定义双份合取，与九参全称的 0<1-δ*<1 封装前提之合取；左肢取 s1inst_dual_cover 之 projT2，右肢由 uabp7_kappa_in01_package 直接给出。 *)
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
  - (* 左肢：s1inst_dual_cover 的 projT2 一次给出良定义双份合取 *)
    exact (projT2 s1inst_dual_cover).
  - (* 右肢：对九参全称目标，直接应用 uabp7_kappa_in01_package *)
    intros temp temp_pos Delta Delta_pos expf expf_pos expf_zero expf_plus
      expf_mono_lt.
    exact (@uabp7_kappa_in01_package RI DO temp temp_pos Delta Delta_pos
               expf expf_pos expf_zero expf_plus expf_mono_lt).
Qed.

End UapkDual.

(* ================= §4 LoHi 展幅前提与四分之一界之合取 ================= *)
(* 合取左肢由 uahlc_lo_one_hi_full 给出：lo<1 ∧ 1<hi ∧ lo<hi；                  *)
(* 合取右肢由 uahl_omd_bounded_half 给出：0<1-(1/2)²<1（抽象指数函数）。        *)
(* 节内别名 invT／lo／hi 与 UpAblP7_LoHiCross 之节同构；half=1/2，half2=1/4。   *)

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

(** uapk_lohi_trinity_supply：lo<1∧1<hi∧lo<hi 与 0<1-(1/2)²<1 之合取；左肢应用 uahlc_lo_one_hi_full，右肢应用 uahl_omd_bounded_half。 *)
Theorem uapk_lohi_trinity_supply :
  And (And (lt lo one) (And (lt one hi) (lt lo hi)))
      (And (lt zero (minus one half2)) (lt (minus one half2) one)).
Proof.
  split.
  - (* 左肢：uahlc_lo_one_hi_full 以 RI 与指数族四参全显实例化 *)
    exact (@uahlc_lo_one_hi_full RI expf expf_pos expf_zero expf_mono_lt).
  - (* 右肢：uahl_omd_bounded_half，{RI} 与 {DO} 为隐式实例参数 *)
    exact (@uahl_omd_bounded_half RI DO).
Qed.

End UapkLoHi.

(* ---- 收尾：对四定理逐一 Print Assumptions，核验公理依赖为零 ---- *)
Print Assumptions uapk_amp_squeeze_hi_face.
Print Assumptions uapk_amp_squeeze_one_face.
Print Assumptions uapk_dual_cover_kappa_assembly.
Print Assumptions uapk_lohi_trinity_supply.
