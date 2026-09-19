(* ============================================================ *)
(* UpAblT9_UpFirewallReq.v —— T9 批 Context 实例束·UpFirewallReq 辖区       *)
(*   （Firewall 五桥面=T1c 已毕，本件只收 Context 束两位，零重叠）          *)
(* 被消融位（普查表 §2 UpFirewallReq 行）：                                *)
(*   位1 UpFirewallReq.v:62  Context {R : Set}                             *)
(*   位2 UpFirewallReq.v:63  Context {RIS : RealInterfaceEnhancedSetoid R}  *)
(* 代表定理（Section FirewallReq 内零数据槽、纯 Context 依赖件）：          *)
(*   位1 ←fw_double_pos@:175                                               *)
(*   位2 ←req_fw_lt_double@:182                                            *)
(* 分级：两位全 N1。位2 出节签名携带 ：103 位 lt_plus_compat 前提           *)
(*   （节内证明体消费该接口位，出节即显式前提参——T1b 偏差账 D1 同形，       *)
(*   消融判词不变：Context 位材料化独立于该前提的供给面）。                 *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、UpFirewallReq。    *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpFirewallReq.
Import RealInterfaceEnhancedMod.

(* 位1 ←:62（rep@:175；R 实例位材料化） *)
Theorem uabT9_fw_ctxR_double_pos :
  forall t : Real, lt zero t -> lt zero (plus t t).
Proof.
  intros t Ht.
  exact (@fw_double_pos Real RealEnhancedReal t Ht).
Qed.

(* 位2 ←:63（rep@:182；RIS 实例位材料化；:103 位前提显式参，单参形同出节签名） *)
Theorem uabT9_fw_ctxRIS_lt_double :
  forall (lpc : forall (a b c d : Real),
            lt a b -> le c d -> lt (plus a c) (plus b d)),
    forall t : Real, lt zero t -> lt t (plus t t).
Proof.
  intros lpc t Ht.
  exact (@req_fw_lt_double Real RealEnhancedReal lpc t Ht).
Qed.

(* ---- PA 收尾 ---- *)
Print Assumptions uabT9_fw_ctxR_double_pos.
Print Assumptions uabT9_fw_ctxRIS_lt_double.
