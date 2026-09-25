(* ============================================================ *)
(* TempUnimodalMax.v —— 使命：温度单峰性 + 最大熵温度 eps-唯一性           *)
(*   （B 层构造性形；组合榜组 8）。两件在库主件合成：                     *)
(*   ① etm_energy_temp_mono_b @ EnergyTempMonoB.v:217：                  *)
(*      t1 < t2 ⟹ E(t1) ≤_B E(t2)（Bishop 档能量-温度单调）；            *)
(*   ② real_max_entropy_is_boltzmann_temp_eps @ UpReqEntropyMaxTemp.v:352：*)
(*      同约束能量 E(p) == E_T ⟹ S[p] ≤ S[p_T] + eps（∀eps > 0）。       *)
(*   合成主张：单调支——约束水平 E(t) 沿温度轴 Bishop 单调，并以           *)
(*   real_le_b_trans 组三温度传递链；峰值支——同能量纤维上任意点 t 的熵   *)
(*   逐 eps 被 t* 占优（t* 为该纤维熵的 eps 形峰）；主件一：同纤维两个    *)
(*   最大温度点必熵 eps-贴近（sigT 见证形，构造性 δ := eps）。            *)
(* 载体裁决：retm_ 族用有限状态 list 载体 real_list_sum（s0 :: l）；      *)
(*   UpReqEntropyMaxTemp 用抽象 real_sum_over_S 接口（六口）。合成靠      *)
(*   list 载体实例化抽象接口：tum_sum（cons 非空有限和）+ 五口证人        *)
(*   （real_list_sum_* 库件逐口直接代入，语句面零 Prop）。重述桥接引理    *)
(*   tum_carrier_energy_shape：real_eq (E(t1)) (E(t2)) ⟹ 抽象件字面能量   *)
(*   前提（retm_pB ↔ real_boltzmann_dist_temp 逐点换形 + sum ext 换载）。 *)
(* 依赖（基座库件，只读使用）：CW_ConstructiveWorld_219（S01–S15 薄壳    *)
(*   + real_list_sum_* 五口 + real_le_to_le_b/real_le_b_trans 桥接引理）；*)
(*   EnergyTempMonoB；UpReqEntropyMaxTemp；UpReqTempDual（在库备用，      *)
(*   本稿合成未直接使用，坐标留档）。                                     *)
(* 构造性注记：语句面全 Set（sigT/prod 容器 + real_lt/real_eq/real_le/    *)
(*   real_le_b 出口，零 Or 新增、零 Prop 前提位）；零承认（语句面无承认   *)
(*   式构造）零经典逻辑（唯一性走 sigT 见证 d := eps 构造给出）；全件     *)
(*   Qed 真证；文末 Print Assumptions 全量审计。                         *)
(* 接口参数纪律：本稿全部定理取条件形/同能量显式前提形，零 full 形前提。  *)
(* 编译配方：coqc 9.1 直调（vo 树内 -Q . "" 平面命名空间），信任缓存前置。 *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
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
