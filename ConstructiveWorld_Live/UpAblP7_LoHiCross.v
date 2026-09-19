(* ============================================================ *)
(* UpAblP7_LoHiCross.v —— 论文7 专项消融战役 PA7-13 席次波甲腿件             *)
(*   （LoHiSqueeze 辖区·cross-节合璧实例镜像 + 夹逼族完整形收口）             *)
(* 母本：LoHiSqueeze.v（席位P7D 合璧件：段一 LhsPair 三件＋段二 LhsStar       *)
(*   一件）；姊妹首波件：UpAblP7_LoHiSqueeze.v（PA7-05 七件，uahl_ 面）。     *)
(*   本件只读消费两者出口面，原树与既有件零改。                              *)
(* 消费面（分层打表，2026-09-19 席 PA7-13 实勘）：                           *)
(*   位1 lhs_lo_lt_one_hi —— 母件段一合璧包装定理（Set 层 And=prod）；       *)
(*   位2 lhs_omd_bounded —— 母件段二 κ:=1−δ*∈(0,1) 前件包旗舰（其证明       *)
(*       内部消费段一件 c 之 δ*<1 支——cross-节之枢）；                      *)
(*   位3 uahl_lo_lt_hi_one —— PA7-05 件六夹逼族实例位（lo<hi @ 温度/利差     *)
(*       取一具体装配）；                                                    *)
(*   位4 p7d_hi_gt_one —— 母件 hi 侧引理（1<hi 全称八参形）；                *)
(*   位5 p7a_lo_lt_one —— lo<1 剪枝形（本件经位1/位4 间接消费，不再单列）。  *)
(* 装载面勘定：czn14_union_full 池内 LoHiSqueeze.vo 与 /tmp/pa7_side 重编版   *)
(*   MD5 同一（6c544d0a…），对现行 Paper7Ablation/P7BoundedSoftmaxDeep       *)
(*   摘要一致，标准联合链（pa7_work＋czn14_union_full）直装母件，            *)
(*   无 inconsistent assumptions（席 PA7-13 探针实证，录 T156 台账）。       *)
(* 定理面（三件，全 Qed，前缀 uahlc_）：                                     *)
(*   件一 cross-节合璧实例镜像（甲）：母件合璧包装定理 lhs_lo_lt_one_hi      *)
(*       实例形——@ 全显喂两节参（RI/expf 族束参面＋温度:=1、利差:=1          *)
(*       具体槽位，分层打表后装配），八参一次喂齐；                          *)
(*   件二 cross-节合璧实例镜像（乙）：母件段二 lhs_omd_bounded 实例形——      *)
(*       @ 全显喂 RI/DO/两节参全束（DO 面为段二所独有，两节参分层合流），    *)
(*       κ∈(0,1) 实例包；                                                    *)
(*   件三 夹逼族完整形收口件：lo<1 ∧ 1<hi ∧ lo<hi 三位一体完整实例链         *)
(*       （lo<1 支出自件一左支；1<hi 支直击母件 hi 侧引理 p7d_hi_gt_one；    *)
(*       lo<hi 支复用 PA7-05 件六 uahl_lo_lt_hi_one——论文 §6.3 前件包       *)
(*       的 LoHi 侧完整供给）。                                              *)
(* 供给面分层：S01:237 inv_pos_pos／S01:487 one_pos／inv_pos 正性装配；      *)
(*   类型类束参面依 T151 速览口径（Context 束＋Local Existing Instance）。    *)
(* 红线自审：语句面全 Set 层（合取用 S01 And=prod，零 Prop 泄露）；公理面零   *)
(*   新增；独立伴生件不并入原模块；前缀 uahlc_ 全库防撞（grep 零命中）；      *)
(*   vo_9.1/Live 正本零改；全中文零承认件写法（头注与注释同口径）。           *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import Paper7Ablation.
Require Import P7BoundedSoftmaxDeep.
Require Import UpAblP7_LoHiSqueeze.
Require Import LoHiSqueeze.

(* ############ 段一：cross-节合璧实例镜像与夹逼族完整收口 ################## *)
(* 节面＝母件两节参面之并（RI/DO 束＋指数族四件），槽位取温度:=1、利差:=1     *)
(* （one_pos 供 inv_pos 装配，invT:=inv_pos one one_pos 具体形）；           *)
(* 指数族保持抽象（全库无具体实数实例，见 T146 工法档 §一·3）。               *)

Section UahlCross.

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

(* 件一（cross-节合璧实例镜像·甲）←母件 lhs_lo_lt_one_hi 实例形：
   @ 全显喂两节参——RI 束参＋温度:=1（one_pos）＋利差:=1（one_pos）＋
   指数族四件，八参一次喂齐；母件左支内部消费 p7a_lo_lt_one（剪枝形），
   右支消费 p7d_hi_gt_one（全称八参形），invT 正性位由母件自配。 *)
Theorem uahlc_lo_lt_one_hi_one : And (lt lo one) (lt one hi).
Proof.
  exact (@lhs_lo_lt_one_hi RI one one_pos one one_pos
             expf expf_pos expf_zero expf_mono_lt).
Qed.

(* 件二（cross-节合璧实例镜像·乙）←母件 lhs_omd_bounded 实例形：
   @ 全显喂 RI/DO/两节参全束——DO 面为母件段二所独有（fa53 消费链所致），
   温度/利差槽位取一、指数族四件分层打表后装配；母件证明内部合流段一
   件 c 之 δ*<1 支（cross-节之枢），κ:=1−δ*∈(0,1) 实例包一次成型。 *)
Theorem uahlc_omd_bounded_one :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  exact (@lhs_omd_bounded RI DO one one_pos one one_pos
             expf expf_pos expf_zero expf_mono_lt).
Qed.

(* 件三（夹逼族完整形收口件）：lo<1 ∧ 1<hi ∧ lo<hi 三位一体完整实例链。
   左支：件一左支（lo<1 实例位）；右支左叶：母件 hi 侧引理 p7d_hi_gt_one
   直击（全称八参形 @ 实例槽位）；右支右叶：PA7-05 件六 uahl_lo_lt_hi_one
   复用（@ 全显喂 RI 束＋指数族四件，DO 面经出节剪枝不占位）——
   论文 §6.3 前件包的 LoHi 侧完整供给一次到位。 *)
Theorem uahlc_lo_one_hi_full :
  And (lt lo one) (And (lt one hi) (lt lo hi)).
Proof.
  split.
  - exact (fst uahlc_lo_lt_one_hi_one).
  - split.
    + exact (p7d_hi_gt_one one one_pos one one_pos expf expf_pos
               expf_zero expf_mono_lt).
    + exact (@uahl_lo_lt_hi_one RI expf expf_pos expf_zero expf_mono_lt).
Qed.

End UahlCross.

(* ---- PA 收尾段（逐件 Closed 判读；G4 审查留痕面） ---- *)
Print Assumptions uahlc_lo_lt_one_hi_one.
Print Assumptions uahlc_omd_bounded_one.
Print Assumptions uahlc_lo_one_hi_full.
