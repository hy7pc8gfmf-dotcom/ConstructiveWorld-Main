(* ==========================================================================)
   ToyR_UpAblP7_LoHiSqueeze.v — LoHiSqueeze 源模块四定理的独立重证与三件实例形
   使命: lo<1 与 1<hi 合取、夹逼 lo<hi、δ*∈(0,1)、κ∈(0,1) 基形，及温度=1、利差=1、半量两实例形（uahl_lo_lt_hi_one 等）；不装设源模块，仅依赖其上游并独立重证。
   依赖: S01_BaseRing、S07_RealSetoidExpLog（C1 一期 RIS 语境新增）、Paper7Ablation、P7BoundedSoftmaxDeep。
   对标: mathlib 夹逼（squeeze）与 1−x<1 型界的构造性 Set 层对应。
   构造性: 语句面全 Set 层（合取 S01 And=prod）；零承认词面、可提取；上游出口以 @ 全参显式应用。
   编译配方: Rocq 9.1 直调 coqc，cpu_guard 包裹，-o 临时目录。
   C1 一期注记（）: UahlPair/UahlStar/UahlSbInst 三节语境迁 RIS 面
   （RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid R，S10:12220 限定名先例
   ＋Let 投影银行体例）；UahlHalf 整节零触碰（Id 面语境＋DO 全保）；键控槽
   expf_zero 语句面 Id→req。p7a/p7d 上游使用改 req 面体内联（tpei_ 供给文件
   Part 0 同体；宿主不 Require tpei_ 件——供给文件 Part C 反向 Require 本件，
   单向环消解，处置全录于组位 attn 交割文书）。
   ========================================================================== *)

(* 【双代同文明认·历史档】本件 UahlStar 段原与 UpAblP7_LoHiSqueeze.v 同名段    *)
(* 逐字同文（diff 为空）。 C1 一期 RIS 迁移后，本件 UahlStar/UahlSbInst *)
(* 两节语句面升为 req 面，与上代（Id 面原样在役）正式分叉；上代件零触碰。      *)
Require Import S01_BaseRing.
Require Import S07_RealSetoidExpLog.
Require Import Paper7Ablation.
Require Import P7BoundedSoftmaxDeep.

(* ############ 段一：合取 lo<1∧1<hi、夹逼 lo<hi、δ*∈(0,1)（无序可判定参） ## *)
(* 节变量面与源模块 LoHiSqueeze.v 的 LhsPair 节一致（温度对＋利差对＋指数族四件）。 *)

Section UahlPair.

Context {R : Set}.
Context {RI : RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid R}.
Local Existing Instance RI_base.

(* C1 一期：RIS 投影银行（S10 AttentionGibbsBridgeSetoid :12224-12232 体例；
   裸名字供给＝原文语句面逐字守恒的实现面）。 *)
Let zero : R := @RealInterfaceEnhancedMod.zero R RI.
Let one : R := @RealInterfaceEnhancedMod.one R RI.
Let plus : R -> R -> R := @RealInterfaceEnhancedMod.plus R RI.
Let mult : R -> R -> R := @RealInterfaceEnhancedMod.mult R RI.
Let opp : R -> R := @RealInterfaceEnhancedMod.opp R RI.
Let lt : R -> R -> Set := @RealInterfaceEnhancedMod.lt R RI.
Let le : R -> R -> Set := @RealInterfaceEnhancedMod.le R RI.
Let req : R -> R -> Set := @RealInterfaceEnhancedMod.req R RI.
Let inv_pos : forall x : R, lt zero x -> R := @RealInterfaceEnhancedMod.inv_pos R RI.
Let req_sym := @RealInterfaceEnhancedMod.req_sym R RI.
Let req_trans := @RealInterfaceEnhancedMod.req_trans R RI.
Let plus_comm := @RealInterfaceEnhancedMod.plus_comm R RI.
Let plus_zero := @RealInterfaceEnhancedMod.plus_zero R RI.
Let plus_opp := @RealInterfaceEnhancedMod.plus_opp R RI.
Let mult_comm := @RealInterfaceEnhancedMod.mult_comm R RI.
Let mult_one := @RealInterfaceEnhancedMod.mult_one R RI.
Let mult_zero := @RealInterfaceEnhancedMod.mult_zero R RI.
Let mult_positive := @RealInterfaceEnhancedMod.mult_positive R RI.
Let lt_trans := @RealInterfaceEnhancedMod.lt_trans R RI.
Let lt_id_l := @RealInterfaceEnhancedMod.lt_id_l R RI.
Let lt_id_r := @RealInterfaceEnhancedMod.lt_id_r R RI.
Let le_refl := @RealInterfaceEnhancedMod.le_refl R RI.
Let lt_mult_compat := @RealInterfaceEnhancedMod.lt_mult_compat R RI.
Let lt_zero_opp := @RealInterfaceEnhancedMod.lt_zero_opp R RI.
Let inv_pos_pos := @RealInterfaceEnhancedMod.inv_pos_pos R RI.
Let one_pos : lt zero one := @RealInterfaceEnhancedMod.one_pos R RI.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : req (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).

(* uahl_lo_lt_one_hi（源模块 lhs_lo_lt_one_hi 的独立重证）：左支经              *)
(*   p7a_lo_lt_one，右支经 p7d_hi_gt_one；invT 正性由 inv_pos_pos 提供。      *)
Theorem uahl_lo_lt_one_hi : And (lt lo one) (lt one hi).
Proof.
  split.
  - (* C1 一期：p7a_lo_lt_one 的 req 面体内联（tpei_p7a_lo_lt_one_req 同体） *)
    assert (Hond := lt_zero_opp Delta Delta_pos).
    assert (Hm : lt (mult (opp Delta) invT) zero).
    { apply (lt_id_r (mult (opp Delta) invT) (mult zero invT) zero
               (req_trans (mult zero invT) (mult invT zero) zero
                  (mult_comm zero invT) (mult_zero invT))).
      exact (lt_mult_compat (opp Delta) zero invT
               (inv_pos_pos temp temp_pos) Hond). }
    apply (lt_id_r (expf (mult invT (opp Delta))) (expf zero) one expf_zero).
    apply (expf_mono_lt (mult invT (opp Delta)) zero).
    apply (lt_id_l (mult invT (opp Delta)) (mult (opp Delta) invT) zero
             (mult_comm invT (opp Delta))).
    exact Hm.
  - (* C1 一期：p7d_hi_gt_one 的 req 面体内联（tpei_p7d_hi_gt_one_req 同体） *)
    exact (lt_id_l one (expf zero) (expf (mult invT Delta))
             (req_sym (expf zero) one expf_zero)
             (expf_mono_lt zero (mult invT Delta)
                (mult_positive invT Delta (inv_pos_pos temp temp_pos) Delta_pos))).
Qed.

(* uahl_lo_lt_hi（源模块 lhs_lo_lt_hi 的独立重证）：lt_trans 两步，两支取自 uahl_lo_lt_one_hi 的两肢 *)
Theorem uahl_lo_lt_hi : lt lo hi.
Proof.
  exact (lt_trans lo one hi (fst uahl_lo_lt_one_hi) (snd uahl_lo_lt_one_hi)).
Qed.

(* uahl_delta_star_bounded（源模块 lhs_delta_star_bounded 的独立重证）：        *)
(*   左支 δ*>0 一步直证（RIS mult_positive 字段）；右支 δ*<1 独立三步：        *)
(*   lt_mult_compat、lt_id_l（经 mult_one）与 lt_trans。 *)
Theorem uahl_delta_star_bounded :
  And (lt zero (mult lo lo)) (lt (mult lo lo) one).
Proof.
  assert (Hlo1 : lt lo one).
  { (* C1 一期：p7a_lo_lt_one 的 req 面体内联（同 uahl_lo_lt_one_hi 左支） *)
    assert (Hond := lt_zero_opp Delta Delta_pos).
    assert (Hm : lt (mult (opp Delta) invT) zero).
    { apply (lt_id_r (mult (opp Delta) invT) (mult zero invT) zero
               (req_trans (mult zero invT) (mult invT zero) zero
                  (mult_comm zero invT) (mult_zero invT))).
      exact (lt_mult_compat (opp Delta) zero invT
               (inv_pos_pos temp temp_pos) Hond). }
    apply (lt_id_r (expf (mult invT (opp Delta))) (expf zero) one expf_zero).
    apply (expf_mono_lt (mult invT (opp Delta)) zero).
    apply (lt_id_l (mult invT (opp Delta)) (mult (opp Delta) invT) zero
             (mult_comm invT (opp Delta))).
    exact Hm. }
  split.
  - exact (mult_positive lo lo (expf_pos (mult invT (opp Delta)))
             (expf_pos (mult invT (opp Delta)))).
  - exact (lt_trans (mult lo lo) (mult one lo) one
             (lt_mult_compat lo one lo
                (expf_pos (mult invT (opp Delta))) Hlo1)
             (lt_id_l (mult one lo) lo one
                (req_trans (mult one lo) (mult lo one) lo
                   (mult_comm one lo) (mult_one lo)) Hlo1)).
Qed.

End UahlPair.

(* ############ 段二：uahl_omd_bounded —— κ:=1−δ*∈(0,1)（带可判定序参节） #### *)
(* 节变量面与源模块 LoHiSqueeze.v 的 LhsStar 节一致；C1 一期 RIS 迁移后原      *)
(* Context {DO} 位换插 lpc 辅助槽（一期扩槽裁，UpReqAttnMixTime:79 逐字体例），  *)
(* omd 双链节内内联二步式。 *)

Section UahlStar.

Context {R : Set}.
Context {RI : RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid R}.
Local Existing Instance RI_base.
(* C1 一期：RIS 投影银行（S10 体例，同 UahlPair）。 *)
Let zero : R := @RealInterfaceEnhancedMod.zero R RI.
Let one : R := @RealInterfaceEnhancedMod.one R RI.
Let plus : R -> R -> R := @RealInterfaceEnhancedMod.plus R RI.
Let mult : R -> R -> R := @RealInterfaceEnhancedMod.mult R RI.
Let opp : R -> R := @RealInterfaceEnhancedMod.opp R RI.
Let lt : R -> R -> Set := @RealInterfaceEnhancedMod.lt R RI.
Let le : R -> R -> Set := @RealInterfaceEnhancedMod.le R RI.
Let req : R -> R -> Set := @RealInterfaceEnhancedMod.req R RI.
Let inv_pos : forall x : R, lt zero x -> R := @RealInterfaceEnhancedMod.inv_pos R RI.
Let req_sym := @RealInterfaceEnhancedMod.req_sym R RI.
Let req_trans := @RealInterfaceEnhancedMod.req_trans R RI.
Let req_lt_compat := @RealInterfaceEnhancedMod.req_lt_compat R RI.
Let plus_comm := @RealInterfaceEnhancedMod.plus_comm R RI.
Let plus_zero := @RealInterfaceEnhancedMod.plus_zero R RI.
Let plus_opp := @RealInterfaceEnhancedMod.plus_opp R RI.
Let mult_comm := @RealInterfaceEnhancedMod.mult_comm R RI.
Let mult_one := @RealInterfaceEnhancedMod.mult_one R RI.
Let mult_zero := @RealInterfaceEnhancedMod.mult_zero R RI.
Let mult_positive := @RealInterfaceEnhancedMod.mult_positive R RI.
Let lt_trans := @RealInterfaceEnhancedMod.lt_trans R RI.
Let lt_id_l := @RealInterfaceEnhancedMod.lt_id_l R RI.
Let lt_id_r := @RealInterfaceEnhancedMod.lt_id_r R RI.
Let le_refl := @RealInterfaceEnhancedMod.le_refl R RI.
Let lt_mult_compat := @RealInterfaceEnhancedMod.lt_mult_compat R RI.
Let lt_zero_opp := @RealInterfaceEnhancedMod.lt_zero_opp R RI.
Let inv_pos_pos := @RealInterfaceEnhancedMod.inv_pos_pos R RI.
Let one_pos : lt zero one := @RealInterfaceEnhancedMod.one_pos R RI.

(* C1 一期扩槽（小裁③）：RIS 世界零 DecidableOrder 判例，lpc 具体层无条件供件。 *)
Variable lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : req (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).

(* C1 一期：节内 minus 影子（S01:189 去 RI 参逐字副本；Let 形保节内作用域， *)
(*   出节不泄漏全局——UahlHalf 的 S01 minus 使用零涉）。 *)
Let minus (a b : R) : R := plus a (opp b).

(* uahl_omd_bounded（源模块 lhs_omd_bounded 的独立重证）：左支以 δ*<1 前提       *)
(*   内联 omd_pos 二步链；右支以 0<lo 内联 omd_lt_one 二步链。 *)
Theorem uahl_omd_bounded :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { (* C1 一期：p7a_lo_lt_one 的 req 面体内联（同 UahlPair 左支） *)
    assert (Hond := lt_zero_opp Delta Delta_pos).
    assert (Hm : lt (mult (opp Delta) invT) zero).
    { apply (lt_id_r (mult (opp Delta) invT) (mult zero invT) zero
               (req_trans (mult zero invT) (mult invT zero) zero
                  (mult_comm zero invT) (mult_zero invT))).
      exact (lt_mult_compat (opp Delta) zero invT
               (inv_pos_pos temp temp_pos) Hond). }
    apply (lt_id_r (expf (mult invT (opp Delta))) (expf zero) one expf_zero).
    apply (expf_mono_lt (mult invT (opp Delta)) zero).
    apply (lt_id_l (mult invT (opp Delta)) (mult (opp Delta) invT) zero
             (mult_comm invT (opp Delta))).
    exact Hm. }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp Delta))). }
  split.
  - exact (lt_id_l zero (plus (mult lo lo) (opp (mult lo lo)))
             (plus one (opp (mult lo lo)))
             (req_sym (plus (mult lo lo) (opp (mult lo lo))) zero
                (plus_opp (mult lo lo)))
             (lpc (mult lo lo) one (opp (mult lo lo)) (opp (mult lo lo))
                (lt_trans (mult lo lo) (mult one lo) one
                   (lt_mult_compat lo one lo Hlopos Hlo1)
                   (lt_id_l (mult one lo) lo one
                      (req_trans (mult one lo) (mult lo one) lo
                         (mult_comm one lo) (mult_one lo)) Hlo1))
                (le_refl (opp (mult lo lo))))).
  - exact (req_lt_compat (plus (opp (mult lo lo)) one)
             (plus one (opp (mult lo lo))) (plus zero one) one
             (plus_comm (opp (mult lo lo)) one)
             (req_trans (plus zero one) (plus one zero) one
                (plus_comm zero one) (plus_zero one))
             (lpc (opp (mult lo lo)) zero one one
                (lt_zero_opp (mult lo lo) (mult_positive lo lo Hlopos Hlopos))
                (le_refl one))).
Qed.

End UahlStar.

(* ########## 段三：实例形甲——uahl_omd_bounded/uahl_lo_lt_hi @ 温度:=1、利差:=1 ## *)
(* 温度与利差均取 one（one_pos 提供两处正性位），invT:=inv_pos one one_pos；    *)
(* 指数族保持抽象（全库无具体实数实例）。C1 一期：RIS 迁移＋lpc 扩槽＋minus 影子，  *)
(* 处置式样同段二。 *)

Section UahlSbInst.

Context {R : Set}.
Context {RI : RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid R}.
Local Existing Instance RI_base.
(* C1 一期：RIS 投影银行（S10 体例，同 UahlStar）。 *)
Let zero : R := @RealInterfaceEnhancedMod.zero R RI.
Let one : R := @RealInterfaceEnhancedMod.one R RI.
Let plus : R -> R -> R := @RealInterfaceEnhancedMod.plus R RI.
Let mult : R -> R -> R := @RealInterfaceEnhancedMod.mult R RI.
Let opp : R -> R := @RealInterfaceEnhancedMod.opp R RI.
Let lt : R -> R -> Set := @RealInterfaceEnhancedMod.lt R RI.
Let le : R -> R -> Set := @RealInterfaceEnhancedMod.le R RI.
Let req : R -> R -> Set := @RealInterfaceEnhancedMod.req R RI.
Let inv_pos : forall x : R, lt zero x -> R := @RealInterfaceEnhancedMod.inv_pos R RI.
Let req_sym := @RealInterfaceEnhancedMod.req_sym R RI.
Let req_trans := @RealInterfaceEnhancedMod.req_trans R RI.
Let req_lt_compat := @RealInterfaceEnhancedMod.req_lt_compat R RI.
Let plus_comm := @RealInterfaceEnhancedMod.plus_comm R RI.
Let plus_zero := @RealInterfaceEnhancedMod.plus_zero R RI.
Let plus_opp := @RealInterfaceEnhancedMod.plus_opp R RI.
Let mult_comm := @RealInterfaceEnhancedMod.mult_comm R RI.
Let mult_one := @RealInterfaceEnhancedMod.mult_one R RI.
Let mult_zero := @RealInterfaceEnhancedMod.mult_zero R RI.
Let mult_positive := @RealInterfaceEnhancedMod.mult_positive R RI.
Let lt_trans := @RealInterfaceEnhancedMod.lt_trans R RI.
Let lt_id_l := @RealInterfaceEnhancedMod.lt_id_l R RI.
Let lt_id_r := @RealInterfaceEnhancedMod.lt_id_r R RI.
Let le_refl := @RealInterfaceEnhancedMod.le_refl R RI.
Let lt_mult_compat := @RealInterfaceEnhancedMod.lt_mult_compat R RI.
Let lt_zero_opp := @RealInterfaceEnhancedMod.lt_zero_opp R RI.
Let inv_pos_pos := @RealInterfaceEnhancedMod.inv_pos_pos R RI.
Let one_pos : lt zero one := @RealInterfaceEnhancedMod.one_pos R RI.

(* C1 一期扩槽（小裁③）：同 UahlStar 体例。 *)
Variable lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : req (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos one one_pos.
Let lo := expf (mult invT (opp one)).

(* C1 一期：节内 minus 影子（同 UahlStar）。 *)
Let minus (a b : R) : R := plus a (opp b).

(* uahl_omd_bounded_one（uahl_omd_bounded 于温度:=1、利差:=1 的实例形）：      *)
(*   p7a 体 req 面内联供 lo<1，expf_pos 供 0<lo，omd 双链节内内联。 *)
Theorem uahl_omd_bounded_one :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { (* C1 一期：p7a_lo_lt_one 的 req 面体内联 @ one/one *)
    assert (Hond := lt_zero_opp one one_pos).
    assert (Hm : lt (mult (opp one) invT) zero).
    { apply (lt_id_r (mult (opp one) invT) (mult zero invT) zero
               (req_trans (mult zero invT) (mult invT zero) zero
                  (mult_comm zero invT) (mult_zero invT))).
      exact (lt_mult_compat (opp one) zero invT (inv_pos_pos one one_pos) Hond). }
    apply (lt_id_r (expf (mult invT (opp one))) (expf zero) one expf_zero).
    apply (expf_mono_lt (mult invT (opp one)) zero).
    apply (lt_id_l (mult invT (opp one)) (mult (opp one) invT) zero
             (mult_comm invT (opp one))).
    exact Hm. }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp one))). }
  split.
  - exact (lt_id_l zero (plus (mult lo lo) (opp (mult lo lo)))
             (plus one (opp (mult lo lo)))
             (req_sym (plus (mult lo lo) (opp (mult lo lo))) zero
                (plus_opp (mult lo lo)))
             (lpc (mult lo lo) one (opp (mult lo lo)) (opp (mult lo lo))
                (lt_trans (mult lo lo) (mult one lo) one
                   (lt_mult_compat lo one lo Hlopos Hlo1)
                   (lt_id_l (mult one lo) lo one
                      (req_trans (mult one lo) (mult lo one) lo
                         (mult_comm one lo) (mult_one lo)) Hlo1))
                (le_refl (opp (mult lo lo))))).
  - exact (req_lt_compat (plus (opp (mult lo lo)) one)
             (plus one (opp (mult lo lo))) (plus zero one) one
             (plus_comm (opp (mult lo lo)) one)
             (req_trans (plus zero one) (plus one zero) one
                (plus_comm zero one) (plus_zero one))
             (lpc (opp (mult lo lo)) zero one one
                (lt_zero_opp (mult lo lo) (mult_positive lo lo Hlopos Hlopos))
                (le_refl one))).
Qed.

(* uahl_lo_lt_hi_one（uahl_lo_lt_hi 于同上实例的实例形）：p7a 体 req 面内联    *)
(*   供 lo<1，p7d 体 req 面内联供 1<hi，lt_trans 合成（零 lpc 使用，lpc 不入导出形）。 *)
Theorem uahl_lo_lt_hi_one :
  lt (expf (mult invT (opp one))) (expf (mult invT one)).
Proof.
  assert (Hlo1 : lt (expf (mult invT (opp one))) one).
  { (* C1 一期：p7a_lo_lt_one 的 req 面体内联 @ one/one（同上 Hlo1 块） *)
    assert (Hond := lt_zero_opp one one_pos).
    assert (Hm : lt (mult (opp one) invT) zero).
    { apply (lt_id_r (mult (opp one) invT) (mult zero invT) zero
               (req_trans (mult zero invT) (mult invT zero) zero
                  (mult_comm zero invT) (mult_zero invT))).
      exact (lt_mult_compat (opp one) zero invT (inv_pos_pos one one_pos) Hond). }
    apply (lt_id_r (expf (mult invT (opp one))) (expf zero) one expf_zero).
    apply (expf_mono_lt (mult invT (opp one)) zero).
    apply (lt_id_l (mult invT (opp one)) (mult (opp one) invT) zero
             (mult_comm invT (opp one))).
    exact Hm. }
  exact (lt_trans (expf (mult invT (opp one))) one (expf (mult invT one))
           Hlo1
           (lt_id_l one (expf zero) (expf (mult invT one))
              (req_sym (expf zero) one expf_zero)
              (expf_mono_lt zero (mult invT one)
                 (mult_positive invT one (inv_pos_pos one one_pos) one_pos)))).
Qed.

End UahlSbInst.

(* ############ 段四：实例形乙——uahl_omd_bounded @ lo:=二分之一抽象形 ######## *)
(* lo:=inv_pos (plus one one) two_pos（二分之一，two_pos/inv_pos_pos 提供正性）；*)
(* 左支不经 δ*<1 中转，走独立链：half_twice（半＋半=1，半方＋半方=半）与       *)
(* plus_positive（半方>0）及恒等重排，推得 0<1−1/4；                          *)
(* 右支 @p7a_omd_lt_one。                                                     *)

Section UahlHalf.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Let half := inv_pos (plus one one) two_pos.
Let half2 := mult half half.

(* uahl_omd_bounded_half（实例形乙） *)
Theorem uahl_omd_bounded_half :
  And (lt zero (minus one half2)) (lt (minus one half2) one).
Proof.
  assert (Hhp : lt zero half).
  { exact (inv_pos_pos (plus one one) two_pos). }
  assert (Hh2p : lt zero half2).
  { exact (mult_positive half half Hhp Hhp). }
  assert (Hh2p2 : lt zero (plus half2 half2)).
  { exact (plus_positive half2 half2 Hh2p Hh2p). }
  assert (Hq : Id (plus half2 half2) half).
  { exact (half_twice half). }
  assert (Hone : Id (plus half half) one).
  { exact (id_trans (id_cong (fun x => plus x x) (id_sym (mult_one half)))
                    (half_twice one)). }
  assert (Hone2 : Id one (plus (plus half2 half2) (plus half2 half2))).
  { exact (id_trans (id_sym Hone) (id_sym (id_cong (fun x => plus x x) Hq))). }
  assert (Gup : Id (plus (plus (plus half2 half2) (plus half2 half2))
                         (opp half2))
                   (plus half2 (plus half2 half2))).
  { exact (id_trans
             (id_sym (plus_assoc (plus half2 half2) (plus half2 half2)
                       (opp half2)))
             (id_trans
                (id_cong (fun x => plus (plus half2 half2) x)
                   (id_trans (id_sym (plus_assoc half2 half2 (opp half2)))
                      (id_trans
                         (id_cong (fun w => plus half2 w)
                            (plus_comm half2 (opp half2)))
                         (plus_assoc half2 (opp half2) half2))))
             (id_trans
                (id_cong (fun x => plus (plus half2 half2) x)
                   (id_cong (fun w => plus w half2) (plus_opp half2)))
                (id_trans
                   (id_cong (fun x => plus (plus half2 half2) x)
                      (id_trans (plus_comm zero half2) (plus_zero half2)))
                   (id_sym (plus_assoc half2 half2 half2)))))). }
  assert (Gtotal : Id (minus one half2) (plus half2 (plus half2 half2))).
  { exact (id_trans
             (id_sym (id_cong (fun w => plus w (opp half2)) (id_sym Hone2)))
             Gup). }
  split.
  - exact (lt_id_r zero (plus half2 (plus half2 half2)) (minus one half2)
             (id_sym Gtotal)
             (plus_positive half2 (plus half2 half2) Hh2p Hh2p2)).
  - exact (@p7a_omd_lt_one RI DO half Hhp).
Qed.

End UahlHalf.

(* ---- 收尾段：逐件 Print Assumptions 核验零承认 ---- *)
Print Assumptions uahl_lo_lt_one_hi.
Print Assumptions uahl_lo_lt_hi.
Print Assumptions uahl_delta_star_bounded.
Print Assumptions uahl_omd_bounded.
Print Assumptions uahl_omd_bounded_one.
Print Assumptions uahl_lo_lt_hi_one.
Print Assumptions uahl_omd_bounded_half.
