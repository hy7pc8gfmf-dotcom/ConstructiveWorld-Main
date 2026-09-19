(* ============================================================ *)
(* UpAblT13b_UpReqAlignRestA.v —— 假设消融战役 T13b 承接席（批6 配分正性族）   *)
(* 辖区：UpReqAlignRestA.v 一位（T13a 移交单 §6 批6 行点名，总账 §2.2 批6 余量）*)
(*   位1 UpReqAlignRestA.v:77  Z_align_pos（ReqRestACore 配分正性位）           *)
(* 被消融位语句（现档逐字，:73-74 同节）：                                      *)
(*   Variable Z_align_pos : lt zero (Z_align_req S sumf reward beta beta_pos    *)
(*                                     pi_ref).                                *)
(*   （Z_align_req 即 UpReqAlign.ReqAlignCore 出节件，本节 Require Import        *)
(*     UpReqAlign 后同名直引——六显参形态与其 :74 引用逐字同形。）                *)
(* 放电母本：UpReqAlign.ReqAlignCore 兄弟槽 sum_pos（:68 正和面）加逐点双正链    *)
(*   （mult_positive/exp_neg_pos 接口字段直引）。                               *)
(* 消融形（诚实登记）：同 UpAblT13b_UpReqAlign 位1——正和数据槽显式参；           *)
(*   载体取 S01 典范载体加装配桥 tsi_rie_setoid（T13a 先例桥形照抄）。           *)
(* 分级：N1（库内正和放电族直喂，证明体=逐点双正链）。                           *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、UpReqAlign、            *)
(*   TempSoftmaxInstantiation。                                                *)
(* 四关留痕：Live_X/attn/logs/g{1..4}-UpAblT13b_*.log                          *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlign.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13bRestA.

Context {RI0 : RealInterfaceEnhanced}.
Let R0 : Set := @S01_BaseRing.R RI0.

(* 位1 ←:77（正和面加逐点双正链放电；正和数据槽显式参） *)
Theorem uabT13b_ralt_Zalign_pos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hpos : forall f : S -> R0, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (reward : S -> R0) (beta : R0) (beta_pos : lt zero beta)
         (pi_ref : S -> R0) (Hpi : forall s : S, lt zero (pi_ref s)),
    lt zero (@Z_align_req R0 (tsi_rie_setoid RI0) S sumf reward beta beta_pos pi_ref).
Proof.
  intros S sumf Hpos reward beta beta_pos pi_ref Hpi.
  unfold Z_align_req.
  apply Hpos. intros s.
  exact (mult_positive (pi_ref s)
           (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
           (Hpi s) (exp_neg_pos _)).
Qed.

End UabT13bRestA.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13b_ralt_Zalign_pos.
