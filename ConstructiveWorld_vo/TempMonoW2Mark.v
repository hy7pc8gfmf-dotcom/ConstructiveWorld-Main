(* ==========================================================================)
   TempMonoW2Mark.v — 能量期望对温度的单调性
   使命: tmw_req_energy_exp_temp_mono_cond/tmw_req_energy_exp_temp_strict_mono_cond（条件形 le/lt）、tmw_req_energy_exp_temp_mono_full/tmw_req_energy_exp_temp_strict_mono_full（全称形）与 tmw_le_minus_nonneg_fw_et（差非负）。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist、UpReqTempEntropy、UpFirewallReq
   对标: 配分函数能量期望随温度的单调性（热力学量温度响应的正则性）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqTempEntropy.
Require Import UpFirewallReq.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section TmwMonoW2：宿主 Section FirewallReq 见证面与                 *)
(*   UpReqTempEntropy Section ReqTempEntropy 消解面之并集。             *)
(*   见证每型一个，宿主位/消解位同喂。                                  *)
(* ============================================================ *)
Section TmwMonoW2.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- 求和面（宿主 ssum_* 与消解面 fsum_* 同型合并） ---- *)
Hypothesis tmw_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis tmw_sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis tmw_sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis tmw_sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis tmw_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis tmw_sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero ->
    forall s : S, req (f s) zero.

Variable base_loss : S -> R.

(* ---- log 桥面（消解面需求；宿主同位 :98-102 同型） ---- *)
Hypothesis tmw_dist_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis tmw_dist_log_exp_neg :
  forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis tmw_dist_log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).
Hypothesis tmw_dist_log_eq_linear :
  forall (x : R) (Hx : lt zero x),
    req (log x Hx) (req_minus x one) -> req x one.

(* ---- Z_temp 接口（宿主 req_Z_temp_spec 同位） ---- *)
Variable Z_temp : R -> R.
Hypothesis tmw_Z_temp_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

(* ============================================================ *)
(* 条件桥 W2a（槽 :135 语句 + 额外前提显式保留，零放大）：              *)
(*   证 = 消解件 :962 同见证实例全参 exact（δ 通道一步）。              *)
(* ============================================================ *)
Theorem tmw_req_energy_exp_temp_mono_cond :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) ->
  le (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t1 Ht1)
     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t2 Ht2).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hbd.
  exact (UpReqTempEntropy.req_energy_exp_temp_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hbd).
Qed.

(* ============================================================ *)
(* 条件桥 W2b（槽 :138 语句 + 额外前提显式保留，零放大）：              *)
(*   证 = 消解件 :1428 同见证实例全参 exact。                           *)
(* ============================================================ *)
Theorem tmw_req_energy_exp_temp_strict_mono_cond :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (req_relative_entropy S sumf
             (@UpFirewallReq.fw_bt R RIS S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt R RIS S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t1 Ht1)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t1 Ht1)) ->
  lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) ->
  lt zero (req_minus (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hkl Hbd.
  exact (UpReqTempEntropy.req_energy_exp_temp_strict_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl Hbd).
Qed.

(* ============================================================ *)
(* 全强度桥 W2a：宿主 :93 lt_minus_nonneg 槽型单前提 ⟹ 槽 :135 逐字。   *)
(*   inv 反序位实喂消解定理 req_inv_pos_lt_contra（:628，接口闭包       *)
(*   内真证零公理面）——宿主 :91 槽由此免费消解；唯一余留假设 = 宿主      *)
(*   :93 既有槽型（非新增主张）。                                       *)
(* ============================================================ *)
Theorem tmw_req_energy_exp_temp_mono_full :
  (forall a b : R, lt a b -> lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  le (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t1 Ht1)
     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t2 Ht2).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt.
  exact (UpReqTempEntropy.req_energy_exp_temp_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt           (Hlmn (inv_pos t2 Ht2) (inv_pos t1 Ht1)                 (UpReqTempEntropy.req_inv_pos_lt_contra t1 t2 Ht1 Ht2 Hlt))).
Qed.

(* ============================================================ *)
(* 全强度桥 W2b：同一余留槽型 ⟹ 槽 :138 逐字（其结论即宿主 :369-370    *)
(*   断言目标，依存位形自身）。                                         *)
(* ============================================================ *)
Theorem tmw_req_energy_exp_temp_strict_mono_full :
  (forall a b : R, lt a b -> lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (req_relative_entropy S sumf
             (@UpFirewallReq.fw_bt R RIS S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt R RIS S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t1 Ht1)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t1 Ht1)) ->
  lt zero (req_minus (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt Hkl.
  exact (UpReqTempEntropy.req_energy_exp_temp_strict_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl           (Hlmn (inv_pos t2 Ht2) (inv_pos t1 Ht1)                 (UpReqTempEntropy.req_inv_pos_lt_contra t1 t2 Ht1 Ht2 Hlt))).
Qed.

(* ============================================================ *)
(* 依存位最小演示件：宿主件5 :307-309 断言行逐字复刻——                 *)
(*   req_le_minus_nonneg (fw_et t1)(fw_et t2)(槽W2a 位 ← 全强度桥)。    *)
(* ============================================================ *)
Theorem tmw_le_minus_nonneg_fw_et :
  (forall a b : R, lt a b -> lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  le zero (req_minus (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt.
  exact (req_le_minus_nonneg           (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss                                 Z_temp tmw_Z_temp_spec t1 Ht1)           (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss                                 Z_temp tmw_Z_temp_spec t2 Ht2)           (tmw_req_energy_exp_temp_mono_full Hlmn t1 t2 Ht1 Ht2 Hlt)).
Qed.

End TmwMonoW2.

(* ============================================================ *)
(* Print Assumptions 假设审计（五件全量）。                             *)
(* ============================================================ *)
Print Assumptions tmw_req_energy_exp_temp_mono_cond.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_cond.
Print Assumptions tmw_req_energy_exp_temp_mono_full.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_full.
Print Assumptions tmw_le_minus_nonneg_fw_et.
