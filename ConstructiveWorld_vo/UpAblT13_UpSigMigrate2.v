(* ============================================================ *)
(* UpAblT13_UpSigMigrate2.v —— 假设消融战役 T13a 承接席（批9 b_gibbs 族·乘法消去位） *)
(* 辖区：UpSigMigrate2.v L919 b_mult_cancel（FA2 普查批9〔无批承接〕余量，           *)
(*   总账 §2.2 批9 行点名；同批 908/910 两位已由 T2a 覆盖，本席不重复认领）。        *)
(* 被消融位语句（现档逐字，L919-920）：                                              *)
(*   Hypothesis b_mult_cancel :                                                     *)
(*     forall (a x : R), lt zero a -> req (mult a x) zero -> req x zero.            *)
(* 放电母本：mult_cancel_l@S01_BaseRing.v:906（乘逆元+结合律+交换律真证，             *)
(*   乘法左消去：a > 0 时 a·b = a·c 则 b = c）。                                     *)
(* 消融形（诚实登记）：RI0 典范载体，req 经装配桥 tsi_rie_setoid（req 取 Id 幺等）；   *)
(*   母本无序可判定依赖（Arguments 仅 {RI}），本件无需带包——比批4 lpc 面更净。        *)
(* 证明路线：H : req (a·x) zero 与 mult_zero 对称链 req_trans 成 Id (a·x) (a·zero)，  *)
(*   喂 mult_cancel_l 得 Id x zero，即目标 req x zero（装配桥下定义性同一）。         *)
(* 分级：N1（库内放电件直喂）。                                                      *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、fa53_compat_abs、            *)
(*   AbsLeId、TempSoftmaxInstantiation。                                             *)
(* 四关留痕：Live_X/attn/logs/g{1..4}-UpAblT13_UpSigMigrate2.log                     *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import fa53_compat_abs.
Require Import AbsLeId.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13Sigm2.

Context {RI0 : RealInterfaceEnhanced}.

(* ←UpSigMigrate2.v:919 b_mult_cancel（语句逐字，名换前缀；载体取典范域） *)
Theorem uabT13_sigm2_b_mult_cancel :
  forall a x : @S01_BaseRing.R RI0,
    lt zero a -> req (mult a x) zero -> req x zero.
Proof.
  intros a x Ha H.
  assert (Hid : Id (@S01_BaseRing.mult RI0 a x) (@S01_BaseRing.zero RI0)) by exact H.
  exact (@mult_cancel_l RI0 a x zero Ha
          (S01_BaseRing.id_trans Hid
             (S01_BaseRing.id_sym (@S01_BaseRing.mult_zero RI0 a)))).
Qed.

End UabT13Sigm2.

(* ---- 收尾段（逐件假设面打印，判读全闭） ---- *)
Print Assumptions uabT13_sigm2_b_mult_cancel.
