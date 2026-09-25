(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(* ============================================================ *)
(* ============================================================ *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* 恒等守恒——清单所列 1 参数位证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* ============================================================ *)

(* ============================================================ *)
(*   位1 UpReqAlignRestA.v:77  Z_align_pos（ReqRestACore 配分正性位）           *)
(* 被消融位语句（现档逐字，:73-74 同节）：                                      *)
(*   Variable Z_align_pos : lt zero (Z_align_req S sumf reward beta beta_pos    *)
(*                                     pi_ref).                                *)
(*   （Z_align_req 即 UpReqAlign.ReqAlignCore 出节件，本节 Require Import        *)
(*     UpReqAlign 后同名直引——六显参形态与其 :74 引用逐字同形。）                *)
(* 实例化消解母本：UpReqAlign.ReqAlignCore 兄弟参数 sum_pos（:68 正和面）加逐点双正链    *)
(*   （mult_positive/exp_neg_pos 接口字段直引）。                               *)
(* 分级：N1（库内正和实例化消解族直接代入，证明体=逐点双正链）。                           *)
(* 依赖（只读依存，原树零改）：CW_ConstructiveWorld_219、UpReqAlign、            *)
(*   TempSoftmaxInstantiation。                                                *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlign.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13bRestA.

Context {RI0 : RealInterfaceEnhanced}.
Let R0 : Set := @S01_BaseRing.R RI0.

(* 位1 ←:77（正和面加逐点双正链实例化消解；正和数据参数位显式参） *)
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
