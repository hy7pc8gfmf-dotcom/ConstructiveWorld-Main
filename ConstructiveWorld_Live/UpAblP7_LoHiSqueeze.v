(* ============================================================ *)
(* UpAblP7_LoHiSqueeze.v —— 论文7 专项消融战役 PA7-05 席首波件               *)
(*   （LoHiSqueeze 辖区·合璧包装四件镜像 + 实例形三件）                       *)
(* 母本：LoHiSqueeze.v（席位P7D 自产合璧件，段一三件+段二一件共四定理；        *)
(*   本件只读消费其上游面，原树零改）。                                       *)
(* 消费面（出口签名实测自探针件全显打表，2026-09-19）：                       *)
(*   位1 p7a_lo_lt_one —— lo<1 剪枝形（利差/利差正性/指数字段/指数零点/       *)
(*       指数单调五参＋invT 正性位；指数字段正性未被母件本位消费故无该参）；   *)
(*   位2 p7d_hi_gt_one —— hi>1 全称八参形；                                  *)
(*   位3 p7a_delta_star_pos —— 0<δ*=lo²；                                    *)
(*   位4 p7a_omd_pos / p7a_omd_lt_one —— κ:=1−δ*∈(0,1) 前件两支，           *)
(*       出口带可判定序参数面（fa53 消费链所致），@ 全显喂参。                *)
(* Require 面勘定：并集根现存 LoHiSqueeze.vo 对 Paper7Ablation 有摘要漂移     *)
(*   （装设假设不一致报错，原文录 T149 台账），故本件不装设母件本身，          *)
(*   Require 面即母件自身上游面 S01_BaseRing＋Paper7Ablation＋                *)
(*   P7BoundedSoftmaxDeep——镜像件全部走上游件直击/独立链复刻真证路，          *)
(*   零母件出节件转发（比母件消费更强的不依赖位）。                           *)
(* 定理面（七件，全 Qed，前缀 uahl_）：                                      *)
(*   件一 母件件a 镜像：合璧包装 lo<1 ∧ 1<hi（Set 层 And）；                  *)
(*   件二 母件件b 镜像：夹逼推论 lo<hi（lt_trans 两步，两支出自件一）；        *)
(*   件三 母件件c 镜像：δ*∈(0,1)（右支 lt_mult_compat 三步独立新导）；         *)
(*   件四 母件件d 镜像（旗舰基形）：κ∈(0,1) 前件包，@ 全显喂参；              *)
(*   件五 旗舰实例形甲：件四 @ 温度:=1、利差:=1、invT:=inv_pos 1 1正          *)
(*       （one_pos＋inv_pos_pos 装配；指数族保持抽象——全库无具体实数实例）；  *)
(*   件六 夹逼族实例位：件二 @ 同上实例（两支出自实例合璧，lt_trans 合龙）；   *)
(*   件七 旗舰实例形乙：件四 @ lo:=二分之一抽象形（inv_pos 2 two_pos），      *)
(*       左支独立链（half_twice 加倍还原＋plus_positive＋恒等洗牌五步）       *)
(*       直放电 0<1−1/4，右支 @p7a_omd_lt_one 直击。                          *)
(* 供给面分层：S01:487 two_pos／S01:237 inv_pos_pos／S01:502 half_twice／     *)
(*   S01:494 half_pos／S01:177 inv_pos_correct／类字段 lt_mult_compat、      *)
(*   lt_id_l、lt_id_r、plus_positive、mult_positive、one_pos；                *)
(*   S03:6420 cauchy_real_exp_pos 属柯西实数异接口（real_lt/cauchy_real_exp   *)
(*   世界），为未来具体 expf 实例装配备料，本波 S01 接口节不消费（异接口不直连）。 *)
(* 红线自审：语句面全 Set 层（合取用 S01 And=prod，零 Prop 泄露）；公理面零    *)
(*   新增；独立伴生件不并入原模块；前缀 uahl_ 本件内防撞；全中文零承认件      *)
(*   写法（头注与注释同口径）。                                               *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import Paper7Ablation.
Require Import P7BoundedSoftmaxDeep.

(* ################ 段一：合璧包装、夹逼推论、δ*∈(0,1) 镜像（无序可判定参） ## *)
(* 节前导逐字复刻母件 LhsPair（八变量面：温度对＋利差对＋指数族四件）。        *)

Section UahlPair.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).

(* 件一 ←母件 lhs_lo_lt_one_hi（上游件直击：p7a_lo_lt_one 剪枝形七参＋       *)
(*   p7d_hi_gt_one 全称八参形；invT 正性位由 inv_pos_pos 放电） *)
Theorem uahl_lo_lt_one_hi : And (lt lo one) (lt one hi).
Proof.
  split.
  - exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)).
  - exact (p7d_hi_gt_one temp temp_pos Delta Delta_pos expf expf_pos
             expf_zero expf_mono_lt).
Qed.

(* 件二 ←母件 lhs_lo_lt_hi（独立链复刻：lt_trans 两步，两支取自件一合璧体） *)
Theorem uahl_lo_lt_hi : lt lo hi.
Proof.
  exact (lt_trans lo one hi (fst uahl_lo_lt_one_hi) (snd uahl_lo_lt_one_hi)).
Qed.

(* 件三 ←母件 lhs_delta_star_bounded（左支 p7a_delta_star_pos 直击；         *)
(*   右支 δ*<1 独立三步新导：lt_mult_compat＋lt_id_l（mult_one 降形）＋       *)
(*   lt_trans，与母件新导进路逐字同构） *)
Theorem uahl_delta_star_bounded :
  And (lt zero (mult lo lo)) (lt (mult lo lo) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  split.
  - exact (p7a_delta_star_pos lo (expf_pos (mult invT (opp Delta)))).
  - exact (lt_trans (mult lo lo) (mult one lo) one
             (lt_mult_compat lo one lo
                (expf_pos (mult invT (opp Delta))) Hlo1)
             (lt_id_l (mult one lo) lo one
                (id_trans (mult_comm one lo) (mult_one lo)) Hlo1)).
Qed.

End UahlPair.

(* ############ 段二：κ:=1−δ*∈(0,1) 前件包镜像（带序可判定参节） ############ *)
(* 节前导逐字复刻母件 LhsStar；p7a_omd_pos/p7a_omd_lt_one 隐式参不可由结论    *)
(* 反推，@ 全参形喂参（fa53 消费链显式喂参先例）。                            *)

Section UahlStar.

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
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).

(* 件四 ←母件 lhs_omd_bounded（旗舰基形镜像：左支 δ*<1 独立三步前件喂        *)
(*   @p7a_omd_pos；右支 lo 正性位喂 @p7a_omd_lt_one——全显喂参） *)
Theorem uahl_omd_bounded :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp Delta))). }
  split.
  - exact (@p7a_omd_pos RI DO lo
             (lt_trans (mult lo lo) (mult one lo) one
                (lt_mult_compat lo one lo Hlopos Hlo1)
                (lt_id_l (mult one lo) lo one
                   (id_trans (mult_comm one lo) (mult_one lo)) Hlo1))).
  - exact (@p7a_omd_lt_one RI DO lo Hlopos).
Qed.

End UahlStar.

(* ########## 段三：实例形甲——件四/件二 @ 温度:=1、利差:=1 具体装配 ########## *)
(* 数据双槽取 one（one_pos 供两处正性位），invT:=inv_pos one one_pos 具体形；  *)
(* 指数族保持抽象（全库无具体实数实例，见 T146 工法档 §一·3）。               *)

Section UahlSbInst.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos one one_pos.
Let lo := expf (mult invT (opp one)).

(* 件五（旗舰实例形甲）←件四 @ 温度:=1、利差:=1（实例装配路：p7a_lo_lt_one    *)
(*   @ one/one 供 lo<1，expf_pos 供 lo 正性，δ*<1 三步链内联，@ 全显喂参） *)
Theorem uahl_omd_bounded_one :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one one one_pos expf expf_zero expf_mono_lt invT
             (inv_pos_pos one one_pos)). }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp one))). }
  split.
  - exact (@p7a_omd_pos RI DO lo
             (lt_trans (mult lo lo) (mult one lo) one
                (lt_mult_compat lo one lo Hlopos Hlo1)
                (lt_id_l (mult one lo) lo one
                   (id_trans (mult_comm one lo) (mult_one lo)) Hlo1))).
  - exact (@p7a_omd_lt_one RI DO lo Hlopos).
Qed.

(* 件六（夹逼族实例位）←件二 @ 同上实例（两支出自实例合璧：p7a_lo_lt_one      *)
(*   @ one/one 供 lo<1，p7d_hi_gt_one @ one/one 供 1<hi，lt_trans 合龙） *)
Theorem uahl_lo_lt_hi_one :
  lt (expf (mult invT (opp one))) (expf (mult invT one)).
Proof.
  exact (lt_trans (expf (mult invT (opp one))) one (expf (mult invT one))
           (p7a_lo_lt_one one one_pos expf expf_zero expf_mono_lt invT
              (inv_pos_pos one one_pos))
           (p7d_hi_gt_one one one_pos one one_pos expf expf_pos expf_zero
              expf_mono_lt)).
Qed.

End UahlSbInst.

(* ############ 段四：实例形乙——件四 @ lo:=二分之一抽象形（独立链） ########## *)
(* lo:=inv_pos (plus one one) two_pos（二分之一，two_pos/inv_pos_pos 供给）；  *)
(* 左支不走 δ*<1 前件装配，改走独立链：half_twice 加倍还原（半＋半=1，        *)
(* 半方＋半方=半）＋plus_positive（半方>0）＋恒等洗牌五步，直放电 0<1−1/4；    *)
(* 右支 @p7a_omd_lt_one 直击。                                                *)

Section UahlHalf.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Let half := inv_pos (plus one one) two_pos.
Let half2 := mult half half.

(* 件七（旗舰实例形乙） *)
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

(* ---- PA 收尾段（逐件 Closed 判读；G4 审查留痕面） ---- *)
Print Assumptions uahl_lo_lt_one_hi.
Print Assumptions uahl_lo_lt_hi.
Print Assumptions uahl_delta_star_bounded.
Print Assumptions uahl_omd_bounded.
Print Assumptions uahl_omd_bounded_one.
Print Assumptions uahl_lo_lt_hi_one.
Print Assumptions uahl_omd_bounded_half.
