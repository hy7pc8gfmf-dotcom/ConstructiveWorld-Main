(* ============================================================ *)
(* UpAblZposDirect.v —— Z_align 正性假设在增强 Setoid 实例上的直接消解 *)
(*                                                                *)
(* 接口事实（对 S05_AlignmentGRPO 的核实）：                          *)
(*   主节 Section Alignment 接口三元为 Id 系：                        *)
(*     Context {RI : RealInterfaceEnhanced}                          *)
(*     Context {SS : StateSpace RI}                                  *)
(*     Context {SO : SumOver RI SS}                                  *)
(*   接口假设原句：Variable Z_align_pos : lt zero Z_align。            *)
(*   Id 系实例普查：记录构造全库零命中，类型驻留形零命中                *)
(*   （仅抽象使用方与引用面）。按库级既定决策                          *)
(*   「构造性实数上 Id 陈述不可实例化」，该假设在 Id 形下为             *)
(*   结构性不可达（既定结论，非本件新发现）。                          *)
(*                                                                *)
(*   降格交付（本件）：Setoid 同形语句直接消解。库内唯一 Setoid 实例    *)
(*   为 RealEnhancedReal（RealInterfaceEnhancedSetoid Real，全库唯一， *)
(*   见 EpsOptimalReach 实例图谱）。                                  *)
(*   形态差（如实申报）：                                             *)
(*   ① 接口 Id 系→Setoid 系（req:=real_eq 读法）；                    *)
(*   ② 求和载体 sum_over_S→real_list_sum·l（S08 注释自证此即           *)
(*      Section Alignment 的实数层实例化形态）；                       *)
(*   ③ 归一化前提保留 Id 原形，实例内经形态转换引理改写。               *)
(*                                                                *)
(* 主件（一句话）：在库内既有实例上，对任意状态表 l、任意 reward、      *)
(*   任意 beta（温度正）、任意 pi_ref（逐点正＋归一化 Id 形），          *)
(*   上述接口假设的同形直接消解成立——语句面逐字段经接口投影            *)
(*   （lt/zero/mult/exp_neg/opp/inv_pos 全为增强 Setoid 接口字段），   *)
(*   前提面与 S05 主节语句逐字同形（零接口外新前提）。                  *)
(*                                                                *)
(* 件表：                                                           *)
(*   zpd_slot_Z_align：S05 主节 Z_align 定义逐字同构的消解体（求和      *)
(*     载体改用 real_list_sum·l）。                                   *)
(*   zpd_norm_id_to_real_eq：Id→real_eq 形态转换引理（match 内导）。    *)
(*   zpd_slot_body_conv_zabr：消解体与 UpAblZposReal 裸形的转换核验     *)
(*     （平凡件·设计使然——逐字同构性的机器验证）。                    *)
(*   zpd_sum_over_S_pos_slot：正性求和假设的同形直接消解（核验件，      *)
(*     承 UpAblZposReal 非空最弱形，诚实边界同其申报）。                *)
(*   zpd_Z_align_pos_slot：主定理——非空内导（归一化×零壹分离）＋       *)
(*     接口字段逐项正链（mult_positive×exp_neg_pos）＋                 *)
(*     使用 UpAblZposReal 折叠和正引理完成。                           *)
(*                                                                *)
(* 依赖（只读使用，零改动）：S01–S04、S07、S08、UpReqExpPos、           *)
(*   UpAblZposReal。零 S05 装载依赖（语句面逐字同位确定）。             *)
(* 构造性注记：零承认件；纯构造性；全件 Set 层（零命题面泄露）。         *)
(* 编译配方：Rocq 9.1 直调，unset COQLIB/ROCQLIB，cpu_guard 包裹。      *)
(* ============================================================ *)
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
