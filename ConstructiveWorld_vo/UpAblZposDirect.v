(* ============================================================ *)
(* UpAblZposDirect.v —— 论文1 假设 B4 的 S05:54 槽位原句直配件（AB7 席） *)
(*                                                                *)
(* 定谳（第一分岔裁决，盘面实测）：                                  *)
(*   S05 主节 Section Alignment 接口三元为 Id 系：                  *)
(*     Context {RI : RealInterfaceEnhanced}（S05:33）               *)
(*     Context {SS : StateSpace RI}（S05:34）                       *)
(*     Context {SO : SumOver RI SS}（S05:35）                       *)
(*   槽位原句（S05:54）：Variable Z_align_pos : lt zero Z_align.     *)
(*   Id 系实例盘面：记录构造全库零命中；类型驻留形零命中              *)
(*   （仅抽象消费者与桥面引用）。按论文 §9.5 库级决策                 *)
(*   「构造性实数上 Id 陈述不可实例化」，S05:54 槽位原句形直配＝      *)
(*   结构性不可达（承既档，非欠账、非墙文集新增）。                   *)
(*                                                                *)
(*   降格交付（本件）：Setoid 同位语句形直配。库内唯一 Setoid 实例     *)
(*   为 RealEnhancedReal（S07:8566，RealInterfaceEnhancedSetoid      *)
(*   Real，全库唯一——EpsOptimalReach.v:33 实例图谱与盘面一致）。      *)
(*   形态差（诚实申报）：                                            *)
(*   ① 接口 Id 系→Setoid 系（req:=real_eq 读法）；                   *)
(*   ② 求和载体 sum_over_S→real_list_sum·l（S08:288，S08 注释        *)
(*      自证此即 Section Alignment 的实数层实例化形态）；              *)
(*   ③ 归一化前件保留 Id 原形（S05:52 同位），实例内经形态桥换装。     *)
(*                                                                *)
(* 主件（一句话）：在库内既有实例上，对任意状态表 l、任意 reward、     *)
(*   任意 beta（温度正）、任意 pi_ref（逐点正＋归一化 Id 形），        *)
(*   S05:54 槽位原句的同位直配形成立——语句面逐字段经接口投影          *)
(*   （lt/zero/mult/exp_neg/opp/inv_pos 全为增强 Setoid 接口字段），  *)
(*   前件面与 S05:47-52 逐字同位（零接口外新前提）。                  *)
(*                                                                *)
(* 件表：                                                          *)
(*   zpd_slot_Z_align：S05:50-53 逐字同构直配体（求和载体换装）。      *)
(*   zpd_norm_id_to_real_eq：Id↦real_eq 形态桥（真实现，match 内导）。 *)
(*   zpd_slot_body_conv_zabr：直配体与 AB2 裸形的转换证书              *)
(*     （平凡件·设计使然——逐字同构性的机器验证）。                    *)
(*   zpd_sum_over_S_pos_slot：B8 槽位同位直配（换装证书件，            *)
(*     承 AB2 非空最弱形，诚实边界同 AB2 申报）。                     *)
(*   zpd_Z_align_pos_slot：主件——非空内导（归一化×零壹分离）＋        *)
(*     接口字段逐项正链（mult_positive×exp_neg_pos）＋                *)
(*     消费 AB2 折叠和正件收口。                                     *)
(*                                                                *)
(* 依赖（只读消费，零改动）：S01–S04、S07、S08、UpReqExpPos、          *)
(*   UpAblZposReal（AB2 件，.vo 在盘）。零 S05 装载依赖（规避共享树    *)
(*   陈旧 .vo 漂移，承 AB1 绕行纪律；槽位锚定＝语句面逐字同位）。      *)
(* 纪律：零承认件；纯构造性；全件 Set 层（零命题面泄露）；头注与注释   *)
(*   全中文表述；未入 order.txt/_CoqProject，注册归主会话波次。        *)
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

(* 实例面开箱：库内唯一增强 Setoid 接口实例（S07:8566）。
   开箱后裸名 lt/zero/mult/exp_neg/opp/inv_pos 即接口字段投影，
   语句面与 S05:50-54 逐字同位；证明面按 E888 卡配方全显式参数。 *)
Import RealInterfaceEnhancedMod.

(* ===== 1. S05:50-53 逐字同构直配体（接口投影形，求和载体换装） ===== *)
(* S05 原形：sum_over_S (fun s => mult (pi_ref s)                    *)
(*   (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))      *)
(* 直配形：sum_over_S↦real_list_sum·l，其余逐字段同位。               *)
Definition zpd_slot_Z_align (X : Set) (l : list X)
  (reward : X -> Real) (beta : Real) (beta_pos : lt zero beta)
  (pi_ref : X -> Real) : Real :=
  real_list_sum X (fun s => mult (pi_ref s)
    (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))) l.

(* ===== 2. 形态桥：归一化前件 Id↦real_eq（S05:52 槽实形换装） ===== *)
(* Id 世界的等式原形在实例世界换装为 setoid 等式：                    *)
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

(* ===== 3. 转换证书：直配体与 AB2 裸形逐项可转换 ================== *)
(* 平凡件（设计使然）：两侧展开后为同一项（实例字段投影零展开          *)
(* ＝real_* 裸常量），恒等构造子经转换内导即闭合。此证书机器验证      *)
(* 「逐字同构」申报。                                               *)
Theorem zpd_slot_body_conv_zabr :
  forall (X : Set) (l : list X) (reward : X -> Real) (beta : Real)
         (beta_pos : lt zero beta) (pi_ref : X -> Real),
    Id (zpd_slot_Z_align X l reward beta beta_pos pi_ref)
       (zabr_Z_align X l reward beta beta_pos pi_ref).
Proof.
  intros X l reward beta beta_pos pi_ref.
  exact id_refl.
Qed.

(* ===== 4. B8 槽位同位直配（S05:4602 承接形，换装证书件） ========== *)
(* S05 迭代节求和正性槽（逐项正⟹和正）的实例同位形。非空前提取        *)
(* AB2 最弱可达形（实数层空表和归零不为正，诚实边界承 AB2 申报）。    *)
Theorem zpd_sum_over_S_pos_slot :
  forall (X : Set) (f : X -> Real) (l : list X),
    Not (Id l nil) ->
    (forall s : X, lt zero (f s)) ->
    lt zero (real_list_sum X f l).
Proof.
  intros X f l Hnn Hf.
  exact (zabr_sum_over_S_pos X f l Hnn Hf).
Qed.

(* ===== 5. 主件：B4 S05:54 槽位直配 =============================== *)
(* 前件面＝S05:47-52 逐字同位（温度正＋逐点正＋归一化 Id 形），        *)
(* 零接口外新前提。证明三段：                                        *)
(*   ① 非空内导：归一化（形态桥换装）×空表和归零×零壹分离件裁决；     *)
(*   ② 逐项正：接口字段 mult_positive（参考策略正×指数正 exp_neg_pos  *)
(*      字段直出）——全链走实例字段投影；                             *)
(*   ③ 收口：消费 AB2 折叠和正件（zabr_sum_over_S_pos）。             *)
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

(* ===== 审计口：零假设面留痕 ===== *)
Print Assumptions zpd_norm_id_to_real_eq.
Print Assumptions zpd_slot_body_conv_zabr.
Print Assumptions zpd_sum_over_S_pos_slot.
Print Assumptions zpd_Z_align_pos_slot.
