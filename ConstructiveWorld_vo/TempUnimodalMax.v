(* ==========================================================================)
   TempUnimodalMax —— 使命：温度单峰性 + 最大熵温度 eps-唯一性；同域语句面
   使命：本件形式化使命：温度单峰性 + 最大熵温度 eps-唯一性。
   本件并载：tmw_req_energy_exp_temp_mono_cond/tmw_req_energy_exp_temp_strict_mono_cond（条。
   依赖：S01_BaseRing, S02_CauchyComplete, S03_QExp, S04_RealExpLogConv, S05_AlignmentGRPO, S06_DiffSamplingGibbs, S07_RealSetoidExpLog, S08_RealMainlineDPO
     S09_EntropyReal, S10_KVQuantTrig, S11_TP3B5, S12_B5RecycleSF, S13_NLiveAudit, S14_B5BatchBlock, S15_TailFEPUp, UpReqAlgebra,
     UpReqDist, UpReqTempEntropy, UpFirewallReq, EnergyTempMonoB, UpReqEntropyMaxTemp, UpReqTempDual。
   构造性：零公理、零承认式语句；语句面 Set 层承载，Print Assumptions 全 Closed。
   编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

(* ============================ §1 tmw_req_energy_exp_temp_mono_cond/tmw_req_energy_exp_temp_strict_mono_cond（条 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
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

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import EnergyTempMonoB.
Require Import UpReqEntropyMaxTemp.
Require Import UpReqTempDual.

(* ============================================================ *)
(* Part 0：list 载体求和面（抽象六口的 cons 载体实例证人）                *)
(* ============================================================ *)

(* cons 非空有限和：Σ_{s ∈ s0::l} f s（retm_ 载体同款） *)
Definition tum_sum (X : Type) (s0 : X) (l : list X) (f : X -> Real) : Real :=
  real_list_sum X f (s0 :: l).

(* 正性口证人：逐点 0 < f s ⟹ 0 < Σ_{s0::l} f
   （real_list_sum_pos 直接代入；cons 非空支路证内 discriminate 使用，
   语句面零 Prop） *)
Lemma tum_sum_pos_wit :
  forall (X : Type) (s0 : X) (l : list X) (f : X -> Real),
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (tum_sum X s0 l f).
Proof.
  intros X s0 l f Hf. unfold tum_sum.
  apply (real_list_sum_pos X f (s0 :: l)).
  - intro s. exact (Hf s).
  - discriminate.
Qed.

(* ============================================================ *)
(* Part 1：温度熵出口（B 层有限系综 Boltzmann 分布的分布熵）              *)
(*   H(t) := Σ_{s ∈ s0::l} p_t(s)·(−log p_t(s))                          *)
(*   （real_entropy_dist 载体实例化；p_t 正性证人 retm_pB_pos 随定义走） *)
(* ============================================================ *)

Definition tum_H (X : Type) (u : X -> Real) (s0 : X) (l : list X)
                 (t : Real) (Ht : real_lt real_zero t) : Real :=
  UpReqTempDefs.real_entropy_dist X (tum_sum X s0 l)
    (RealEnergyTempMono.retm_pB X u s0 l t Ht)
    (RealEnergyTempMono.retm_pB_pos X u s0 l t Ht).

(* 正则温度化 Boltzmann 分布熵（主件二右端同形出口）：
   Hb(t) := Entropy(canonical real_boltzmann_dist_temp，list 载体实例） *)
Definition tum_Hb (X : Type) (u : X -> Real) (s0 : X) (l : list X)
                  (t : Real) (Ht : real_lt real_zero t) : Real :=
  UpReqTempDefs.real_entropy_dist X (tum_sum X s0 l)
    (UpReqTempDefs.real_boltzmann_dist_temp
       X (tum_sum X s0 l) (tum_sum_pos_wit X s0 l) t Ht u)
    (UpReqTempDefs.real_boltzmann_dist_temp_pos
       X (tum_sum X s0 l) (tum_sum_pos_wit X s0 l) t Ht u).

(* ============================================================ *)
(* Part 2：重述桥接引理（可读同能量前提 ⟹ 抽象件字面能量前提）               *)
(*   retm_pB t2 与 real_boltzmann_dist_temp（list 载体实例）逐点换形：   *)
(*   因子序（exp·inv ↔ inv·exp）real_mult_comm + inv 证人差              *)
(*   real_inv_pos_ext（底 real_eq_refl）+ sum ext 换载，三段 trans。     *)
(* ============================================================ *)

Theorem tum_carrier_energy_shape :
  forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
    (t1 : Real) (Ht1 : real_lt real_zero t1) (t2 : Real) (Ht2 : real_lt real_zero t2),
  real_eq (RealEnergyTempMono.retm_Eexp X u s0 l t1 Ht1)
          (RealEnergyTempMono.retm_Eexp X u s0 l t2 Ht2) ->
  real_eq (real_list_sum X
             (fun s : X => real_mult
                (RealEnergyTempMono.retm_pB X u s0 l t1 Ht1 s) (u s)) (s0 :: l))
          (UpReqTempDefs.real_energy_exp_temp X (tum_sum X s0 l) (tum_sum_pos_wit X s0 l) t2 Ht2 u).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 Hsame.
  apply (real_eq_trans
           (real_list_sum X
              (fun s : X => real_mult
                 (RealEnergyTempMono.retm_pB X u s0 l t1 Ht1 s) (u s)) (s0 :: l))
           (RealEnergyTempMono.retm_Eexp X u s0 l t1 Ht1)
           (UpReqTempDefs.real_energy_exp_temp X (tum_sum X s0 l) (tum_sum_pos_wit X s0 l) t2 Ht2 u)).
  - (* 支路 1：retm_Eexp t1 定义性收敛（delta-beta 换形） *)
    unfold RealEnergyTempMono.retm_Eexp. apply real_eq_refl.
  - (* 支路 2：同能量前提 + retm_Eexp t2 ↔ energy_exp_temp 换形 *)
    apply (real_eq_trans
             (RealEnergyTempMono.retm_Eexp X u s0 l t1 Ht1)
             (RealEnergyTempMono.retm_Eexp X u s0 l t2 Ht2)
             (UpReqTempDefs.real_energy_exp_temp X (tum_sum X s0 l) (tum_sum_pos_wit X s0 l) t2 Ht2 u)).
    + exact Hsame.
    + apply (real_eq_trans
               (RealEnergyTempMono.retm_Eexp X u s0 l t2 Ht2)
               (real_list_sum X
                  (fun s : X => real_mult
                     (UpReqTempDefs.real_boltzmann_dist_temp
                        X (tum_sum X s0 l) (tum_sum_pos_wit X s0 l) t2 Ht2 u s) (u s)) (s0 :: l))
               (UpReqTempDefs.real_energy_exp_temp X (tum_sum X s0 l) (tum_sum_pos_wit X s0 l) t2 Ht2 u)).
      * (* 逐点换形：retm_pB t2 s ↔ boltzmann_dist_temp（list 实例）s *)
        apply (real_list_sum_ext X
                 (fun s : X => real_mult
                    (RealEnergyTempMono.retm_pB X u s0 l t2 Ht2 s) (u s))
                 (fun s : X => real_mult
                    (UpReqTempDefs.real_boltzmann_dist_temp
                       X (tum_sum X s0 l) (tum_sum_pos_wit X s0 l) t2 Ht2 u s) (u s))
                 (s0 :: l)).
        intro s.
        apply (RealSetoid.real_eq_mult_compat_adapt
                 (RealEnergyTempMono.retm_pB X u s0 l t2 Ht2 s)
                 (UpReqTempDefs.real_boltzmann_dist_temp
                    X (tum_sum X s0 l) (tum_sum_pos_wit X s0 l) t2 Ht2 u s)
                 (u s) (u s)).
        -- (* retm_pB t2 s == boltz t2 s：因子序 + inv 证人差两跳 *)
           apply (real_eq_trans
                    (real_mult
                       (real_exp_neg (real_mult (real_inv_pos t2 Ht2) (u s)))
                       (real_inv_pos
                          (RealEnergyTempMono.retm_Ztemp X u s0 l t2 Ht2)
                          (RealEnergyTempMono.retm_Ztemp_pos X u s0 l t2 Ht2)))
                    (real_mult
                       (real_inv_pos
                          (RealEnergyTempMono.retm_Ztemp X u s0 l t2 Ht2)
                          (RealEnergyTempMono.retm_Ztemp_pos X u s0 l t2 Ht2))
                       (real_exp_neg (real_mult (real_inv_pos t2 Ht2) (u s))))
                    (UpReqTempDefs.real_boltzmann_dist_temp
                       X (tum_sum X s0 l) (tum_sum_pos_wit X s0 l) t2 Ht2 u s)).
           ++ exact (real_mult_comm
                       (real_exp_neg (real_mult (real_inv_pos t2 Ht2) (u s)))
                       (real_inv_pos
                          (RealEnergyTempMono.retm_Ztemp X u s0 l t2 Ht2)
                          (RealEnergyTempMono.retm_Ztemp_pos X u s0 l t2 Ht2))).
           ++ apply (RealSetoid.real_eq_mult_compat_adapt
                       (real_inv_pos
                          (RealEnergyTempMono.retm_Ztemp X u s0 l t2 Ht2)
                          (RealEnergyTempMono.retm_Ztemp_pos X u s0 l t2 Ht2))
                       (real_inv_pos
                          (UpReqTempDefs.real_Z_temp X (tum_sum X s0 l) t2 Ht2 u)
                          (UpReqTempDefs.real_Z_temp_pos
                             X (tum_sum X s0 l) (tum_sum_pos_wit X s0 l) t2 Ht2 u))
                       (real_exp_neg (real_mult (real_inv_pos t2 Ht2) (u s)))
                       (real_exp_neg (real_mult (real_inv_pos t2 Ht2) (u s)))).
           ** exact (real_inv_pos_ext
                       (RealEnergyTempMono.retm_Ztemp X u s0 l t2 Ht2)
                       (UpReqTempDefs.real_Z_temp X (tum_sum X s0 l) t2 Ht2 u)
                       (RealEnergyTempMono.retm_Ztemp_pos X u s0 l t2 Ht2)
                       (UpReqTempDefs.real_Z_temp_pos
                          X (tum_sum X s0 l) (tum_sum_pos_wit X s0 l) t2 Ht2 u)
                       (real_eq_refl
                          (RealEnergyTempMono.retm_Ztemp X u s0 l t2 Ht2))).
           ** apply real_eq_refl.
        -- apply real_eq_refl.
      * (* energy_exp_temp（list 实例）定义性收敛（delta-beta 换形） *)
        unfold UpReqTempDefs.real_energy_exp_temp. apply real_eq_refl.
Qed.

(* ============================================================ *)
(* Part 3：峰值支（同能量纤维熵 eps-占优，逐 eps 档）——                  *)
(*   real_max_entropy_is_boltzmann_temp_eps @ UpReqEntropyMaxTemp.v:352  *)
(*   的 list 载体全参实例化：p := retm_pB t1，约束温度 T := t2，         *)
(*   同能量前提即纤维条件 E(t1) == E(t2)。分峰段之峰侧件。               *)
(* ============================================================ *)

Theorem tum_entropy_max_eps_same_E :
  forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
    (t1 : Real) (Ht1 : real_lt real_zero t1) (t2 : Real) (Ht2 : real_lt real_zero t2),
  real_eq (RealEnergyTempMono.retm_Eexp X u s0 l t1 Ht1)
          (RealEnergyTempMono.retm_Eexp X u s0 l t2 Ht2) ->
  forall eps : Real,
    real_lt real_zero eps ->
    real_le (tum_H X u s0 l t1 Ht1) (real_plus (tum_Hb X u s0 l t2 Ht2) eps).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 Hsame eps Heps.
  exact (real_max_entropy_is_boltzmann_temp_eps
           X (tum_sum X s0 l) (tum_sum_pos_wit X s0 l)
           (fun (f g : X -> Real) (H : forall s : X, real_eq (f s) (g s)) =>
              real_list_sum_ext X f g (s0 :: l) H)
           (fun (f g : X -> Real) (H : forall s : X, real_le (f s) (g s)) =>
              real_list_sum_le X f g (s0 :: l) H)
           (fun (a : Real) (f : X -> Real) =>
              real_list_sum_linear X a f (s0 :: l))
           (fun (f g : X -> Real) =>
              real_list_sum_add X f g (s0 :: l))
           t2 Ht2 u
           (RealEnergyTempMono.retm_pB X u s0 l t1 Ht1)
           (RealEnergyTempMono.retm_pB_pos X u s0 l t1 Ht1)
           (RealEnergyTempMono.retm_pB_norm X u s0 l t1 Ht1)
           (tum_carrier_energy_shape X u s0 l t1 Ht1 t2 Ht2 Hsame)
           eps Heps).
Qed.

(* 对称件：纤维条件换向后 t1 点同形占优（real_eq_sym 换向 + 全参对偶）   *)
Theorem tum_entropy_max_eps_same_E_sym :
  forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
    (t1 : Real) (Ht1 : real_lt real_zero t1) (t2 : Real) (Ht2 : real_lt real_zero t2),
  real_eq (RealEnergyTempMono.retm_Eexp X u s0 l t1 Ht1)
          (RealEnergyTempMono.retm_Eexp X u s0 l t2 Ht2) ->
  forall eps : Real,
    real_lt real_zero eps ->
    real_le (tum_H X u s0 l t2 Ht2) (real_plus (tum_Hb X u s0 l t1 Ht1) eps).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 Hsame eps Heps.
  exact (tum_entropy_max_eps_same_E X u s0 l t2 Ht2 t1 Ht1
           (real_eq_sym (RealEnergyTempMono.retm_Eexp X u s0 l t1 Ht1)
                        (RealEnergyTempMono.retm_Eexp X u s0 l t2 Ht2) Hsame)
           eps Heps).
Qed.

(* ============================================================ *)
(* Part 4：单调支（B 层 real_le_b 链，三温度传递形）——                   *)
(*   etm_energy_temp_mono_b @ EnergyTempMonoB.v:217 两段                 *)
(*   real_le_b_trans 组合：t1 < t2 < t3 ⟹ E(t1) ≤_B E(t3)。             *)
(* ============================================================ *)

Theorem tum_energy_temp_mono_b_chain :
  forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
    (t1 : Real) (Ht1 : real_lt real_zero t1)
    (t2 : Real) (Ht2 : real_lt real_zero t2)
    (t3 : Real) (Ht3 : real_lt real_zero t3),
  real_lt t1 t2 ->
  real_lt t2 t3 ->
  UpRealLeB.real_le_b (RealEnergyTempMono.retm_Eexp X u s0 l t1 Ht1)
            (RealEnergyTempMono.retm_Eexp X u s0 l t3 Ht3).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 t3 Ht3 Ht12 Ht23.
  exact (UpRealLeB2.real_le_b_trans
           (RealEnergyTempMono.retm_Eexp X u s0 l t1 Ht1)
           (RealEnergyTempMono.retm_Eexp X u s0 l t2 Ht2)
           (RealEnergyTempMono.retm_Eexp X u s0 l t3 Ht3)
           (etm_energy_temp_mono_b X u s0 l t1 Ht1 t2 Ht2 Ht12)
           (etm_energy_temp_mono_b X u s0 l t2 Ht2 t3 Ht3 Ht23)).
Qed.

(* ============================================================ *)
(* 主件一：最大熵温度 eps-唯一性（sigT 见证形，构造性 δ := eps）          *)
(*   同能量纤维上两个最大温度点 t1、t2：对任意 eps > 0 存在见证 d（实给   *)
(*   d := eps），0 < d 且双向熵占优 S(t1) ≤ S(t2)+d ∧ S(t2) ≤ S(t1)+d   *)
(*   ——"两个最大点必 eps-贴近"的构造性出口；出口全 Set（sigT/prod/       *)
(*   real_lt/real_le），零经典逻辑（无"不唯一则矛盾"形）。               *)
(* ============================================================ *)

Theorem tum_max_entropy_temp_eps_unique :
  forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
    (t1 : Real) (Ht1 : real_lt real_zero t1) (t2 : Real) (Ht2 : real_lt real_zero t2),
  real_eq (RealEnergyTempMono.retm_Eexp X u s0 l t1 Ht1)
          (RealEnergyTempMono.retm_Eexp X u s0 l t2 Ht2) ->
  forall eps : Real,
    real_lt real_zero eps ->
    sigT (fun d : Real =>
      prod (real_lt real_zero d)
        (prod (real_le (tum_H X u s0 l t1 Ht1)
                       (real_plus (tum_Hb X u s0 l t2 Ht2) d))
              (real_le (tum_H X u s0 l t2 Ht2)
                       (real_plus (tum_Hb X u s0 l t1 Ht1) d)))).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 Hsame eps Heps.
  exists eps. split.
  - exact Heps.
  - split.
    + exact (tum_entropy_max_eps_same_E X u s0 l t1 Ht1 t2 Ht2 Hsame eps Heps).
    + exact (tum_entropy_max_eps_same_E_sym X u s0 l t1 Ht1 t2 Ht2 Hsame eps Heps).
Qed.

(* ============================================================ *)
(* 主件二：熵-温度单峰双支组合（prod 形，两库件逐字合成）                 *)
(*   单调支：t1 < t2 ⟹ E(t1) ≤_B E(t2)（etm 主件直接代入，B 层链）；         *)
(*   峰值支：同能量纤维条件下 S(t1) ≤ S(t2)+eps（∀eps>0，最大熵主件      *)
(*   list 载体实例直接代入）——沿温度轴约束水平 Bishop 单调、同纤维上          *)
(*   熵取 eps 峰的两支结构，分峰段拆两件的合取出口（And := prod）。       *)
(* ============================================================ *)

Theorem tum_entropy_unimodal_split :
  forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
    (t1 : Real) (Ht1 : real_lt real_zero t1) (t2 : Real) (Ht2 : real_lt real_zero t2),
  real_lt t1 t2 ->
  prod (UpRealLeB.real_le_b (RealEnergyTempMono.retm_Eexp X u s0 l t1 Ht1)
                  (RealEnergyTempMono.retm_Eexp X u s0 l t2 Ht2))
       (real_eq (RealEnergyTempMono.retm_Eexp X u s0 l t1 Ht1)
                (RealEnergyTempMono.retm_Eexp X u s0 l t2 Ht2) ->
        forall eps : Real,
          real_lt real_zero eps ->
          real_le (tum_H X u s0 l t1 Ht1)
                  (real_plus (tum_Hb X u s0 l t2 Ht2) eps)).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 Ht12. split.
  - exact (etm_energy_temp_mono_b X u s0 l t1 Ht1 t2 Ht2 Ht12).
  - exact (tum_entropy_max_eps_same_E X u s0 l t1 Ht1 t2 Ht2).
Qed.

(* ============================================================ *)
(* G4 假设审计口（文末 PA 全量六件）                                     *)
(* ============================================================ *)
Print Assumptions tum_sum_pos_wit.
Print Assumptions tum_carrier_energy_shape.
Print Assumptions tum_entropy_max_eps_same_E.
Print Assumptions tum_entropy_max_eps_same_E_sym.
Print Assumptions tum_energy_temp_mono_b_chain.
Print Assumptions tum_max_entropy_temp_eps_unique.
Print Assumptions tum_entropy_unimodal_split.
