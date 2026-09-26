(* ============================================================ *)
(* SupKLBound.v                                                 *)
(*                                                              *)
(* 目的：有限单纯形上 sup KL 的显式上界——若 m 为 q 的逐点下界且     *)
(*       0 < m，则 Σ_s kl(p_s‖q_s) ≤ log(1/m)。                    *)
(* 主件：skb_sup_kl_log_inv_min : forall (X : Type) (l : list X)     *)
(*       (p q : X -> Real),（逐点 0 < p_s、0 < q_s、p_s ≤ 1、        *)
(*       Σ p == 1，m 逐点 m ≤ q_s、0 < m）⟹                          *)
(*       real_list_sum (kl_term) l ≤ real_log_inv m。               *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、                *)
(*       S07_RealSetoidExpLog、S08_RealMainlineDPO、G01_CoreMicro；   *)
(*       Stdlib List（ListNotations）、Extraction。                  *)
(* 备注：本件补库内缺口（UpReqGeomIter.v:866-869 指出的缺口④：       *)
(*       le_b 乘法保序闭包所需的 KL_0 上界即 sup KL 材料，库内原本    *)
(*       无该上界件）；UpReqPowMonoBridge.v:330-337 已定理化「给定    *)
(*       上界材料则逐 eps 闭合」，本件供给该上界材料本体。语句形      *)
(*       判定（Real 载体、全 Set 层）：即 sup_p KL(p‖q) ≤            *)
(*       log(1/min_s q_s)——顶点 p = δ_s 处取等的经典有限单纯形        *)
(*       KL ≤ 常数界；q 侧归一化不进前提（证明只吃 m ≤ q_s、0 < m，   *)
(*       前提更少、强度更真）。证明路线：逐点四步（① m·p_s ≤ m ≤      *)
(*       q_s；② 乘 inv(p_s) > 0，左端恒等 m ⟹ m ≤ q_s·inv(p_s)；      *)
(*       ③ log 单调 le 版 + opp 翻转 + 乘 p_s > 0 得逐点              *)
(*       real_kl_term 界；④ real_list_sum_le 求和保序 +               *)
(*       real_list_sum_linear_r 常数提出 + Hnormp 归一化）。全件      *)
(*       Qed 零承认式；语句面全 Set（real_lt/real_eq 为 Set，        *)
(*       real_le = 两者之 Set 层 Or 编码，零 Prop 泄露）；            *)
(*       skb_ 前缀防撞。                                             *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import G01_CoreMicro.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Extraction.

(* ============ 辅件1：左因子严格正乘法单调（Or 编码 le 直连） ============ *)
(* 0<c、a≤b ⟹ c·a ≤ c·b：S07 real_le_mult_compat 为右因子版，comm 两跳换形 *)
Lemma skb_le_mult_compat_l : forall a b c : Real,
  real_lt real_zero c -> real_le a b ->
  real_le (real_mult c a) (real_mult c b).
Proof.
  intros a b c Hc Hab.
  assert (Hrc : real_le (real_mult a c) (real_mult b c)).
  { exact (real_le_mult_compat a b c Hc Hab). }
  apply (real_le_trans (real_mult c a) (real_mult a c) (real_mult c b)).
  - apply (RealSetoid.real_eq_le (real_mult c a) (real_mult a c)).
    exact (real_mult_comm c a).
  - apply (real_le_trans (real_mult a c) (real_mult b c) (real_mult c b)).
    + exact Hrc.
    + apply (RealSetoid.real_eq_le (real_mult b c) (real_mult c b)).
      exact (real_mult_comm b c).
Qed.

(* ============ 主件：单纯形 sup KL 上界 ============ *)
(* Σ_s kl(p_s‖q_s) ≤ log(1/m)：m 为 q 逐点下界、0<m 即所求上界件。 *)
Theorem skb_sup_kl_log_inv_min :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (Hp1 : forall s : X, real_le (p s) real_one)
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (m : Real)
    (Hm : forall s : X, real_le m (q s))
    (Hmpos : real_lt real_zero m),
  real_le
    (real_list_sum X
       (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
    (real_log_inv m Hmpos).
Proof.
  intros X l p q Hp Hq Hp1 Hnormp m Hm Hmpos.
  (* ============ 逐点主链 ============ *)
  assert (Hpt : forall s : X,
    real_le (real_kl_term (p s) (q s) (Hp s) (Hq s))
            (real_mult (p s) (real_log_inv m Hmpos))).
  { intro s.
    (* 9.1 全量适配：log 的证明参被 cw_log/log_seq 结构性消费——
       assert 新变量与 real_kl_term 内联项不可转换；改 pose（let 绑定）使
       Hqpinv 依 zeta 折回 real_mult_positive 全形，与 real_kl_term δ 展开对齐 *)
    pose (Hpinv := real_inv_pos_pos (p s) (Hp s)).
    pose (Hqpinv := real_mult_positive (q s) (real_inv_pos (p s) (Hp s))
               (Hq s) Hpinv).
    (* 步①：m·(p s) ≤ m·1 == m ≤ q s *)
    assert (Hmp1 : real_le (real_mult m (p s)) (real_mult m real_one)).
    { exact (skb_le_mult_compat_l (p s) real_one m Hmpos (Hp1 s)). }
    assert (Hmp2 : real_le (real_mult m (p s)) m).
    { apply (real_le_trans (real_mult m (p s)) (real_mult m real_one) m).
      - exact Hmp1.
      - apply (RealSetoid.real_eq_le (real_mult m real_one) m).
        exact (real_mult_one m). }
    assert (Hmp3 : real_le (real_mult m (p s)) (q s)).
    { apply (real_le_trans (real_mult m (p s)) m (q s)).
      - exact Hmp2.
      - exact (Hm s). }
    (* 步②：乘 inv(p s)>0，左端恒等 m ⟹ m ≤ q s·inv(p s) *)
    assert (Hdiv : real_le
             (real_mult (real_mult m (p s)) (real_inv_pos (p s) (Hp s)))
             (real_mult (q s) (real_inv_pos (p s) (Hp s)))).
    { exact (real_le_mult_compat (real_mult m (p s)) (q s)
               (real_inv_pos (p s) (Hp s)) Hpinv Hmp3). }
    assert (Hid : real_eq
             (real_mult (real_mult m (p s)) (real_inv_pos (p s) (Hp s))) m).
    { apply (real_eq_trans
               (real_mult (real_mult m (p s)) (real_inv_pos (p s) (Hp s)))
               (real_mult m (real_mult (p s) (real_inv_pos (p s) (Hp s))))
               m).
      - apply (real_eq_sym
                 (real_mult m (real_mult (p s) (real_inv_pos (p s) (Hp s))))
                 (real_mult (real_mult m (p s))
                    (real_inv_pos (p s) (Hp s)))).
        exact (real_mult_assoc m (p s) (real_inv_pos (p s) (Hp s))).
      - apply (real_eq_trans
                 (real_mult m (real_mult (p s) (real_inv_pos (p s) (Hp s))))
                 (real_mult m real_one) m).
        + apply (RealSetoid.real_eq_mult_compat m
                   (real_mult (p s) (real_inv_pos (p s) (Hp s))) m real_one).
          * apply real_eq_refl.
          * exact (real_inv_pos_correct (p s) (Hp s)).
        + exact (real_mult_one m). }
    assert (Hmle : real_le m (real_mult (q s) (real_inv_pos (p s) (Hp s)))).
    { apply (real_le_trans m
               (real_mult (real_mult m (p s)) (real_inv_pos (p s) (Hp s)))
               (real_mult (q s) (real_inv_pos (p s) (Hp s)))).
      - apply (RealSetoid.real_eq_le m
                 (real_mult (real_mult m (p s))
                    (real_inv_pos (p s) (Hp s)))).
        exact (real_eq_sym (real_mult (real_mult m (p s))
                 (real_inv_pos (p s) (Hp s))) m Hid).
      - exact Hdiv. }
    (* 步③：log 单调 le 版 + opp 翻转 *)
    assert (Hlog : real_le (real_log m Hmpos)
                     (real_log (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                               Hqpinv)).
    { exact (real_log_le_mono m
               (real_mult (q s) (real_inv_pos (p s) (Hp s)))
               Hmpos Hqpinv Hmle). }
    assert (Hopplem : real_le
             (real_opp (real_log
                 (real_mult (q s) (real_inv_pos (p s) (Hp s))) Hqpinv))
             (real_opp (real_log m Hmpos))).
    { exact (real_opp_le_compat (real_log m Hmpos)
               (real_log (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                 Hqpinv) Hlog). }
    (* 步④：乘 p s>0 得逐点界（real_kl_term δ 透明展开；9.1 全量编译下 log 的
       证明参非计算无关——须内联 real_mult_positive 全形，不得走 assert 中转） *)
    exact (skb_le_mult_compat_l
             (real_opp (real_log
                 (real_mult (q s) (real_inv_pos (p s) (Hp s))) Hqpinv))
             (real_opp (real_log m Hmpos))
             (p s) (Hp s) Hopplem). }
  (* ============ 求和阶段 ============ *)
  apply (real_le_trans
           (real_list_sum X
              (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
           (real_list_sum X
              (fun s : X => real_mult (p s) (real_log_inv m Hmpos)) l)
           (real_log_inv m Hmpos)).
  - apply (real_list_sum_le X
             (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s))
             (fun s : X => real_mult (p s) (real_log_inv m Hmpos)) l).
    exact Hpt.
  - (* Σ(p·L) == L·Σp == L·1 == L *)
    apply (RealSetoid.real_eq_le
             (real_list_sum X
                (fun s : X => real_mult (p s) (real_log_inv m Hmpos)) l)
             (real_log_inv m Hmpos)).
    apply (real_eq_trans
             (real_list_sum X
                (fun s : X => real_mult (p s) (real_log_inv m Hmpos)) l)
             (real_mult (real_log_inv m Hmpos) (real_list_sum X p l))
             (real_log_inv m Hmpos)).
    + exact (real_list_sum_linear_r X (real_log_inv m Hmpos) p l).
    + apply (real_eq_trans
               (real_mult (real_log_inv m Hmpos) (real_list_sum X p l))
               (real_mult (real_log_inv m Hmpos) real_one)
               (real_log_inv m Hmpos)).
      * apply (RealSetoid.real_eq_mult_compat (real_log_inv m Hmpos)
                 (real_list_sum X p l) (real_log_inv m Hmpos) real_one).
        -- apply real_eq_refl.
        -- exact Hnormp.
      * exact (real_mult_one (real_log_inv m Hmpos)).
Qed.

(* ============ 提取探针（Obj.magic 计数，配套 skb_g3.v） ============ *)
Extraction "skb_G3.ml" skb_sup_kl_log_inv_min skb_le_mult_compat_l.

(* ============ 自证面：Print Assumptions 假设审计 ============ *)
Print Assumptions skb_le_mult_compat_l.
Print Assumptions skb_sup_kl_log_inv_min.
