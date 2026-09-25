(* ==========================================================================)
   UpAblZposDirect.v — 对齐配分的直和式与正性
   使命: zpd_slot_Z_align（列表直和式）、zpd_slot_body_conv_zabr（与 zabr_Z_align 的换算恒等）、zpd_norm_id_to_real_eq、zpd_sum_over_S_pos_slot 与 zpd_Z_align_pos_slot（正性）。
   依赖: S01_BaseRing、S02_CauchyComplete、S03_QExp、S04_RealExpLogConv、S07_RealSetoidExpLog、S08_RealMainlineDPO等；Stdlib List
   对标: DPO 对齐配分函数的直和实现与正性（归一化前提下的严格正）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import UpReqExpPos.
Require Import UpAblZposReal.
From Stdlib Require Import List.

(* 实例引入：库内唯一增强 Setoid 接口实例 RealEnhancedReal。
   引入后裸名 lt/zero/mult/exp_neg/opp/inv_pos 即接口字段投影，
   语句面与 S05 主节语句逐字同形；证明面全显式参数。 *)
Import RealInterfaceEnhancedMod.

(* ===== 1. Z_align 逐字同构消解体（接口投影形，求和载体改用实数层） ===== *)
(* S05 原形：sum_over_S (fun s => mult (pi_ref s)                    *)
(*   (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))      *)
(* 消解形：sum_over_S↦real_list_sum·l，其余逐字段同位。               *)
Definition zpd_slot_Z_align (X : Set) (l : list X)
  (reward : X -> Real) (beta : Real) (beta_pos : lt zero beta)
  (pi_ref : X -> Real) : Real :=
  real_list_sum X (fun s => mult (pi_ref s)
    (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))) l.

(* ===== 2. 形态转换引理：归一化前提 Id↦real_eq ===================== *)
(* Id 世界的等式原形在实例世界改写为 setoid 等式：                    *)
(* Id（S01 集合层恒等型）消去＋real_eq 自反内导，真实现。             *)
Theorem zpd_norm_id_to_real_eq :
  forall (X : Set) (l : list X) (pi_ref : X -> Real),
    Id (real_list_sum X pi_ref l) one ->
    real_eq (real_list_sum X pi_ref l) real_one.
Proof.
  intros X l pi_ref H.
  exact (match H in Id _ y
         return real_eq (real_list_sum X pi_ref l) y
         with
         | id_refl => real_eq_refl (real_list_sum X pi_ref l)
         end).
Qed.

(* ===== 3. 转换核验：消解体与 UpAblZposReal 裸形逐项可转换 ========= *)
(* 平凡件（设计使然）：两侧展开后为同一项（实例字段投影零展开          *)
(* ＝real_* 裸常量），恒等构造子经转换内导即闭合。此核验即「逐字       *)
(* 同构」的机器验证。                                               *)
Theorem zpd_slot_body_conv_zabr :
  forall (X : Set) (l : list X) (reward : X -> Real) (beta : Real)
         (beta_pos : lt zero beta) (pi_ref : X -> Real),
    Id (zpd_slot_Z_align X l reward beta beta_pos pi_ref)
       (zabr_Z_align X l reward beta beta_pos pi_ref).
Proof.
  intros X l reward beta beta_pos pi_ref.
  exact id_refl.
Qed.

(* ===== 4. 正性求和假设的同形直接消解（S05 迭代节给出形） =========== *)
(* S05 迭代节求和正性假设（逐项正⟹和正）的实例同形。非空前提取        *)
(* UpAblZposReal 最弱可达形（实数层空表和归零不为正，诚实边界同前）。  *)
Theorem zpd_sum_over_S_pos_slot :
  forall (X : Set) (f : X -> Real) (l : list X),
    Not (Id l nil) ->
    (forall s : X, lt zero (f s)) ->
    lt zero (real_list_sum X f l).
Proof.
  intros X f l Hnn Hf.
  exact (zabr_sum_over_S_pos X f l Hnn Hf).
Qed.

(* ===== 5. 主定理：Z_align 正性假设的直接消解 ====================== *)
(* 前提面＝S05 主节语句逐字同形（温度正＋逐点正＋归一化 Id 形），      *)
(* 零接口外新前提。证明三段：                                        *)
(*   ① 非空内导：归一化（经形态转换引理）×空表和归零×零壹分离引理；   *)
(*   ② 逐项正：接口字段 mult_positive（参考策略正×指数正 exp_neg_pos  *)
(*      字段直出）——全链走实例字段投影；                             *)
(*   ③ 完成：使用 UpAblZposReal 折叠和正引理（zabr_sum_over_S_pos）。  *)
Theorem zpd_Z_align_pos_slot :
  forall (X : Set) (l : list X) (reward : X -> Real) (beta : Real)
         (beta_pos : lt zero beta) (pi_ref : X -> Real),
    (forall s : X, lt zero (pi_ref s)) ->
    Id (real_list_sum X pi_ref l) one ->
    lt zero (zpd_slot_Z_align X l reward beta beta_pos pi_ref).
Proof.
  intros X l reward beta beta_pos pi_ref Hrefpos Hnorm.
  unfold zpd_slot_Z_align.
  assert (HnormEq : real_eq (real_list_sum X pi_ref l) real_one).
  { exact (zpd_norm_id_to_real_eq X l pi_ref Hnorm). }
  assert (Hnn : Not (Id l nil)).
  { intro Hnil.
    assert (Hsum0 : real_eq (real_list_sum X pi_ref l) real_zero).
    { exact (real_eq_trans (real_list_sum X pi_ref l)
               (real_list_sum X pi_ref nil) real_zero
               (match Hnil in Id _ y return
                  real_eq (real_list_sum X pi_ref l)
                          (real_list_sum X pi_ref y)
                with id_refl => real_eq_refl _ end)
               (real_eq_refl real_zero)). }
    exact (upreq_real_zero_ne_one
            (real_eq_trans real_zero (real_list_sum X pi_ref l) real_one
               (real_eq_sym (real_list_sum X pi_ref l) real_zero Hsum0)
               HnormEq)). }
  exact (zabr_sum_over_S_pos X
           (fun s => mult (pi_ref s)
              (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))) l
           Hnn
           (fun s => mult_positive (pi_ref s)
              (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
              (Hrefpos s)
              (exp_neg_pos
                 (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ===== 假设面自检（Print Assumptions） ===== *)
Print Assumptions zpd_norm_id_to_real_eq.
Print Assumptions zpd_slot_body_conv_zabr.
Print Assumptions zpd_sum_over_S_pos_slot.
Print Assumptions zpd_Z_align_pos_slot.
