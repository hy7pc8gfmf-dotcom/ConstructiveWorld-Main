(* ============================================================ *)
(* UpAblT13b_UpSigMigrate2.v —— 假设消融战役 T13b 承接席（批6 配分正性族两位） *)
(* 辖区：UpSigMigrate2.v 两位（T13a 移交单 §6 批6 行点名；T9a 已收 :112 位，     *)
(*   本席零重叠）：                                                            *)
(*   位1 UpSigMigrate2.v:111  Z_pos（ReqFECore 配分正性位）                     *)
(*   位2 UpSigMigrate2.v:891  Z_align_a_pos（ReqAlignCore 对齐配分正性位）       *)
(* 被消融位语句（现档逐字）：                                                   *)
(*   :110-111 Variable Z : R. Variable Z_pos : lt zero Z.（:112 配分条件同节）   *)
(*   :887-891 Definition Z_align_a_sum : R :=                                   *)
(*            sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta  *)
(*                                     beta_pos) (reward s))))).                *)
(*            Variable Z_align_a_pos : lt zero Z_align_a_sum.                   *)
(* 放电母本：                                                                   *)
(*   位1 ←req_Z_temp_pos@UpReqDist:2808 同机制（正和槽+配分槽显式参，           *)
(*         迁移经 lt_id_r/req_sym 接口字段）；                                   *)
(*   位2 ←sumd_sum_pos@UpReqSumD:233 正和族（asum 面无正字段，正和数据槽         *)
(*         显式参）加 mult_positive/exp_neg_pos 逐点双正链。                     *)
(* 消融形（诚实登记）：抽象载体上不放电，典范载体加装配桥 tsi_rie_setoid（       *)
(*   T13a 先例桥形照抄）上成立，正和数据槽显式参。                               *)
(* 分级：两位全 N1。                                                            *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、UpSigMigrate2、         *)
(*   TempSoftmaxInstantiation。                                                 *)
(* 四关留痕：Live_X/attn/logs/g{1..4}-UpAblT13b_*.log                          *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpSigMigrate2.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13bSigm2.

Context {RI0 : RealInterfaceEnhanced}.
Let R0 : Set := @S01_BaseRing.R RI0.

(* 位1 ←:111（配分条件迁移正和正性；正和槽与配分槽显式参） *)
Theorem uabT13b_sigm2_Zpos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hpos : forall f : S -> R0, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (base_loss : S -> R0) (D : R0) (D_pos : lt zero D) (Z : R0),
    req Z (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) ->
    lt zero Z.
Proof.
  intros S sumf Hpos base_loss D D_pos Z Hpc.
  apply (@lt_id_r R0 (tsi_rie_setoid RI0) zero
           (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z).
  - apply req_sym. exact Hpc.
  - apply Hpos. intros s.
    exact (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))).
Qed.

(* 位2 ←:891（正和面加逐点双正链；正和槽显式参） *)
Theorem uabT13b_sigm2_Zalign_a_pos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hpos : forall f : S -> R0, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (reward : S -> R0) (beta : R0) (beta_pos : lt zero beta)
         (pi_ref : S -> R0) (Hpi : forall s : S, lt zero (pi_ref s)),
    lt zero (@Z_align_a_sum R0 (tsi_rie_setoid RI0) S sumf reward beta beta_pos pi_ref).
Proof.
  intros S sumf Hpos reward beta beta_pos pi_ref Hpi.
  unfold Z_align_a_sum.
  apply Hpos. intros s.
  exact (mult_positive (pi_ref s)
           (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
           (Hpi s) (exp_neg_pos _)).
Qed.

End UabT13bSigm2.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13b_sigm2_Zpos.
Print Assumptions uabT13b_sigm2_Zalign_a_pos.
