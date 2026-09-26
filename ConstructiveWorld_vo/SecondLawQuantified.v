(* ==========================================================================)
   SecondLawQuantified.v — 热力学第二定律的定量化
   使命: slq_second_law_eps_list（ε 形第二定律主件）、entropy_gain_kl_lower/upper（熵增的 KL 上下界）、gibbs_step_fixed（Gibbs 步不动点）、receiver_second_law_quant 与 setoid 框架化（slq_second_law_setoid_frame）。
   依赖: CW_ConstructiveWorld_219、UpReqTempDefs、UpReqEntropyDeficitTemp、UpReqTempDual、TempSoftmaxInstantiation、UpReqSumD、UpReqConcSoftmax、ConcMixSelFeed、UpReqConcFin2；Stdlib List。
   对标: Gibbs 采样步的熵单调性（热力学第二定律的离散定量化）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

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
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqTempDual.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 支撑 2（req→le 单调平移整理件，节外全局）：沿 req 的 le 双侧    *)
(*   运输——精确式 real_eq 升格逐 eps real_le 的关键。             *)
(* ============================================================ *)
Lemma slq_le_resp_req_l : forall (a b c : Real),
  real_eq a b -> real_le b c -> real_le a c.
Proof. intros a b c Hab Hbc. exact (RealSetoid.real_le_compat b a c c (real_eq_sym a b Hab) (real_eq_refl c) Hbc). Qed.

Lemma slq_le_resp_req_r : forall (a b c : Real),
  real_eq b c -> real_le a b -> real_le a c.
Proof. intros a b c Hbc Hab. exact (RealSetoid.real_le_compat a a b c (real_eq_refl a) Hbc Hab). Qed.

(* ============================================================ *)
(* 第一部分：主件——受体 SecondLaw 区块的实例化定量升级（Real 层） *)
(*   载体 = CW219 具体 Real；求和机器照供体节同款抽象参数位。          *)
(* ============================================================ *)

Section SlqSecondLaw.

(* 求和机器诚实参数位（供体节同形同序：S sumf sumpos ext linear add） *)
Variable S : Type.
Variable sumf : (S -> Real) -> Real.
Hypothesis sumpos :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (sumf f).
Hypothesis sumext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis sumlinear : forall (a : Real) (f : S -> Real),
  real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)).
Hypothesis sumadd : forall (f g : S -> Real),
  real_eq (sumf (fun s : S => real_plus (f s) (g s)))
          (real_plus (sumf f) (sumf g)).

(* 温度与能量（前提位照供体节对位：S06 L3338 形） *)
Variable T : Real.
Hypothesis T_pos : real_lt real_zero T.
Variable energy : S -> Real.

(* Boltzmann 均衡分布（受体 dynamics 一步核的重采样目标） *)
Definition slq_boltz : S -> Real :=
  real_boltzmann_dist_temp S sumf sumpos T T_pos energy.
Definition slq_boltz_pos : forall s : S, real_lt real_zero (slq_boltz s) :=
  real_boltzmann_dist_temp_pos S sumf sumpos T T_pos energy.

(* 分布熵（供体 real_entropy_dist：Σ p·(−log p)；受体 entropy_ent 的   *)
(*   分布级对应坐标） *)
Definition slq_entropy (p : S -> Real)
           (Hp : forall s : S, real_lt real_zero (p s)) : Real :=
  real_entropy_dist S sumf p Hp.

(* 熵亏（= 一步热浴演化的熵增见证）：S[p_T] − S[p] *)
Definition slq_entropy_gain (p : S -> Real)
           (Hp : forall s : S, real_lt real_zero (p s)) : Real :=
  real_minus_r (slq_entropy slq_boltz slq_boltz_pos) (slq_entropy p Hp).

(* 熵亏 = KL(当前‖Boltzmann)：供体 real_KL_temp（Σ p·(log p − log p_T)） *)
Definition slq_kl_cur_boltz (p : S -> Real)
           (Hp : forall s : S, real_lt real_zero (p s)) : Real :=
  real_KL_temp S sumf sumpos T T_pos energy p Hp.

(* 受体 dynamics 一步核坐标：Gibbs 热浴核重采样                          *)
(*   step p s' := Σ_s p s · p_T s'（q_kernel 的 Doeblin 中心 p_b 热浴极限）*)
Definition slq_gibbs_step (p : S -> Real) : S -> Real :=
  fun s' : S => sumf (fun s : S => real_mult (p s) (slq_boltz s')).

(* ---------------------------------------------------------- *)
(* 件 1：一步 Gibbs 热浴核不动点（受体 dynamics 实例化内容件）   *)
(*   归一分布的一步热浴更新 ≡ p_T（逐点）。                      *)
(* ---------------------------------------------------------- *)
Theorem slq_gibbs_step_fixed :
  forall (p : S -> Real) (Hnp : real_eq (sumf p) real_one) (s' : S),
    real_eq (slq_gibbs_step p s') (slq_boltz s').
Proof.
  intros p Hnp s'.
  unfold slq_gibbs_step.
  apply (real_eq_trans
           (sumf (fun s : S => real_mult (p s) (slq_boltz s')))
           (real_mult (slq_boltz s') (sumf p))
           (slq_boltz s')).
  - apply (real_eq_trans
             (sumf (fun s : S => real_mult (p s) (slq_boltz s')))
             (sumf (fun s : S => real_mult (slq_boltz s') (p s)))
             (real_mult (slq_boltz s') (sumf p))).
    + apply sumext. intro s. apply real_mult_comm.
    + exact (sumlinear (slq_boltz s') p).
  - apply (real_eq_trans
             (real_mult (slq_boltz s') (sumf p))
             (real_mult (slq_boltz s') real_one)
             (slq_boltz s')).
    + apply (RealSetoid.real_eq_mult_compat (slq_boltz s') (sumf p)
               (slq_boltz s') real_one (real_eq_refl (slq_boltz s')) Hnp).
    + exact (real_mult_one (slq_boltz s')).
Qed.

(* 件 1b：一步核更新分布逐点正（p_T 正性沿 req 运输；real_lt_id_l） *)
Lemma slq_step_pos :
  forall (p : S -> Real) (Hnp : real_eq (sumf p) real_one) (s' : S),
    real_lt real_zero (slq_gibbs_step p s').
Proof.
  intros p Hnp s'.
  pose proof (slq_gibbs_step_fixed p Hnp s') as Hfix.
  pose proof (real_eq_sym (slq_gibbs_step p s') (slq_boltz s') Hfix) as Hsym.
  exact (RealSetoid.real_lt_compat real_zero real_zero
           (slq_boltz s') (slq_gibbs_step p s')
           (real_eq_refl real_zero) Hsym
           (slq_boltz_pos s')).
Qed.

(* 支撑 2b（单调整理件）：分布熵的逐点 req 外延性。 *)
Lemma slq_entropy_dist_ext :
  forall (q r : S -> Real)
         (Hq : forall s : S, real_lt real_zero (q s))
         (Hr : forall s : S, real_lt real_zero (r s)),
    (forall s : S, real_eq (q s) (r s)) ->
    real_eq (slq_entropy q Hq) (slq_entropy r Hr).
Proof.
  intros q r Hq Hr Hwd.
  unfold slq_entropy, real_entropy_dist.
  apply sumext. intro s.
  apply (RealSetoid.real_eq_mult_compat (q s)
           (real_opp (real_log (q s) (Hq s)))
           (r s)
           (real_opp (real_log (r s) (Hr s))) (Hwd s)).
  apply (RealSetoid.real_eq_opp_compat (real_log (q s) (Hq s))
           (real_log (r s) (Hr s))).
  exact (real_log_wd (q s) (r s) (Hq s) (Hr s) (Hwd s)).
Qed.

(* 件 1c：一步核实现熵 ≡ 均衡熵（不动点的熵论读出） *)
Theorem slq_step_entropy_eq_boltz :
  forall (p : S -> Real) (Hnp : real_eq (sumf p) real_one),
    real_eq (slq_entropy (slq_gibbs_step p) (slq_step_pos p Hnp))
            (slq_entropy slq_boltz slq_boltz_pos).
Proof.
  intros p Hnp.
  unfold slq_entropy, real_entropy_dist.
  apply sumext. intro s.
  apply (RealSetoid.real_eq_mult_compat
           (slq_gibbs_step p s)
           (real_opp (real_log (slq_gibbs_step p s) (slq_step_pos p Hnp s)))
           (slq_boltz s)
           (real_opp (real_log (slq_boltz s) (slq_boltz_pos s)))
           (slq_gibbs_step_fixed p Hnp s)).
  apply (RealSetoid.real_eq_opp_compat
           (real_log (slq_gibbs_step p s) (slq_step_pos p Hnp s))
           (real_log (slq_boltz s) (slq_boltz_pos s))).
  exact (real_log_wd (slq_gibbs_step p s) (slq_boltz s)
           (slq_step_pos p Hnp s) (slq_boltz_pos s)
           (slq_gibbs_step_fixed p Hnp s)).
Qed.

(* ---------------------------------------------------------- *)
(* 主件（lower）：KL(当前‖Boltzmann) − 熵亏 ≤ eps                *)
(*   语义：一步 Gibbs 核演化熵增 ≥ 熵亏 − eps（熵亏 = KL）。      *)
(*   链：供体精确式 real_entropy_deficit_kl_temp（熵亏 == KL）    *)
(*   → opp/plus compat 平移 → plus_opp 归零 → lt_le_iff。         *)
(* ---------------------------------------------------------- *)
Theorem slq_entropy_gain_kl_lower :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    forall eps : Real, real_lt real_zero eps ->
      real_le (real_minus_r (slq_kl_cur_boltz p Hp) (slq_entropy_gain p Hp)) eps.
Proof.
  intros p Hp Hnp Henergy eps Heps.
  pose proof (real_entropy_deficit_kl_temp S sumf sumpos sumext sumlinear sumadd
                T T_pos energy p Hp Hnp Henergy) as Hdef.
  apply (slq_le_resp_req_l
           (real_minus_r (slq_kl_cur_boltz p Hp) (slq_entropy_gain p Hp))
           real_zero eps).
  - apply (real_eq_trans
             (real_minus_r (slq_kl_cur_boltz p Hp) (slq_entropy_gain p Hp))
             (real_minus_r (slq_kl_cur_boltz p Hp) (slq_kl_cur_boltz p Hp))
             real_zero).
    + apply (RealSetoid.real_eq_plus_compat
               (slq_kl_cur_boltz p Hp) (real_opp (slq_entropy_gain p Hp))
               (slq_kl_cur_boltz p Hp) (real_opp (slq_kl_cur_boltz p Hp))).
      * exact (real_eq_refl (slq_kl_cur_boltz p Hp)).
      * exact (RealSetoid.real_eq_opp_compat
                 (slq_entropy_gain p Hp) (slq_kl_cur_boltz p Hp) Hdef).
    + exact (real_plus_opp (slq_kl_cur_boltz p Hp)).
  - exact (real_lt_le_iff real_zero eps (inl Heps)).
Qed.

(* 主件（upper）：熵亏 − KL ≤ eps（互补向；语义：熵增 ≤ 熵亏 + eps） *)
Theorem slq_entropy_gain_kl_upper :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    forall eps : Real, real_lt real_zero eps ->
      real_le (real_minus_r (slq_entropy_gain p Hp) (slq_kl_cur_boltz p Hp)) eps.
Proof.
  intros p Hp Hnp Henergy eps Heps.
  pose proof (real_entropy_deficit_kl_temp S sumf sumpos sumext sumlinear sumadd
                T T_pos energy p Hp Hnp Henergy) as Hdef.
  apply (slq_le_resp_req_l
           (real_minus_r (slq_entropy_gain p Hp) (slq_kl_cur_boltz p Hp))
           real_zero eps).
  - apply (real_eq_trans
             (real_minus_r (slq_entropy_gain p Hp) (slq_kl_cur_boltz p Hp))
             (real_minus_r (slq_entropy_gain p Hp) (slq_entropy_gain p Hp))
             real_zero).
    + apply (RealSetoid.real_eq_plus_compat
               (slq_entropy_gain p Hp) (real_opp (slq_kl_cur_boltz p Hp))
               (slq_entropy_gain p Hp) (real_opp (slq_entropy_gain p Hp))).
      * exact (real_eq_refl (slq_entropy_gain p Hp)).
      * exact (RealSetoid.real_eq_opp_compat
                 (slq_kl_cur_boltz p Hp) (slq_entropy_gain p Hp)
                 (real_eq_sym (slq_entropy_gain p Hp) (slq_kl_cur_boltz p Hp)
                              Hdef)).
    + exact (real_plus_opp (slq_entropy_gain p Hp)).
  - exact (real_lt_le_iff real_zero eps (inl Heps)).
Qed.

(* ---------------------------------------------------------- *)
(* 主件（实现形）：一步热浴核演化的实现熵增 ≥ 熵亏 − eps          *)
(*   实现熵增 := S[step p] − S[p]；不动点件 1c ⟹ 实现熵增 == 熵亏，*)
(*   沿 req 平移并入主件 lower 界。                                *)
(* ---------------------------------------------------------- *)
Theorem slq_step_gain_kl_lower :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
         (Hnp : real_eq (sumf p) real_one)
         (Henergy : real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
                      (real_energy_exp_temp S sumf sumpos T T_pos energy))
         (eps : Real) (Heps : real_lt real_zero eps),
    real_le (real_minus_r (slq_kl_cur_boltz p Hp)
                          (real_minus_r
                             (slq_entropy (slq_gibbs_step p) (slq_step_pos p Hnp))
                             (slq_entropy p Hp)))
            eps.
Proof.
  intros p Hp Hnp Henergy eps Heps.
  apply (slq_le_resp_req_l
           (real_minus_r (slq_kl_cur_boltz p Hp)
                         (real_minus_r
                            (slq_entropy (slq_gibbs_step p) (slq_step_pos p Hnp))
                            (slq_entropy p Hp)))
           (real_minus_r (slq_kl_cur_boltz p Hp) (slq_entropy_gain p Hp))
           eps).
  - (* 实现熵增 == 熵亏（件 1c 换载） *)
    apply (RealSetoid.real_eq_plus_compat
             (slq_kl_cur_boltz p Hp)
             (real_opp (real_minus_r
                          (slq_entropy (slq_gibbs_step p) (slq_step_pos p Hnp))
                          (slq_entropy p Hp)))
             (slq_kl_cur_boltz p Hp)
             (real_opp (slq_entropy_gain p Hp))).
    + exact (real_eq_refl (slq_kl_cur_boltz p Hp)).
    + apply (RealSetoid.real_eq_opp_compat
               (real_minus_r (slq_entropy (slq_gibbs_step p) (slq_step_pos p Hnp))
                             (slq_entropy p Hp))
               (slq_entropy_gain p Hp)).
      apply (RealSetoid.real_eq_plus_compat
               (slq_entropy (slq_gibbs_step p) (slq_step_pos p Hnp))
               (real_opp (slq_entropy p Hp))
               (slq_entropy slq_boltz slq_boltz_pos)
               (real_opp (slq_entropy p Hp))).
      * exact (slq_step_entropy_eq_boltz p Hnp).
      * exact (real_eq_refl (real_opp (slq_entropy p Hp))).
  - exact (slq_entropy_gain_kl_lower p Hp Hnp Henergy eps Heps).
Qed.

(* ---------------------------------------------------------- *)
(* 支撑 1（熵亏非负引理 eps 形）：Gibbs 肢为逐支接口前提时        *)
(*   S[p] ≤ S[p_T] + eps——Second Law 定量读法（受体 lt 结论的    *)
(*   实例化逐 eps 升格）。使用 t13_max_entropy_le_eps。           *)
(* ---------------------------------------------------------- *)
Theorem slq_entropy_deficit_nonneg_eps :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    (forall eps : Real, real_lt real_zero eps ->
       real_le real_zero
         (real_plus (slq_kl_cur_boltz p Hp) eps)) ->
    forall eps : Real, real_lt real_zero eps ->
      real_le (slq_entropy p Hp)
              (real_plus (slq_entropy slq_boltz slq_boltz_pos) eps).
Proof.
  intros p Hp Hnp Henergy Hgibbs eps Heps.
  apply (t13_le_plus_opp_shift (slq_entropy p Hp) (real_plus (slq_entropy slq_boltz slq_boltz_pos) eps)).
  apply (RealSetoid.real_le_id_r real_zero
           (real_plus (slq_kl_cur_boltz p Hp) eps)
           (real_plus (real_plus (slq_entropy slq_boltz slq_boltz_pos) eps) (real_opp (slq_entropy p Hp)))).
  - apply (real_eq_trans
             (real_plus (slq_kl_cur_boltz p Hp) eps)
             (real_plus (real_plus (slq_entropy slq_boltz slq_boltz_pos) (real_opp (slq_entropy p Hp))) eps)
             (real_plus (real_plus (slq_entropy slq_boltz slq_boltz_pos) eps) (real_opp (slq_entropy p Hp)))).
    + apply (RealSetoid.real_eq_plus_compat_adapt (slq_kl_cur_boltz p Hp)
               (real_plus (slq_entropy slq_boltz slq_boltz_pos) (real_opp (slq_entropy p Hp))) eps eps).
      * apply real_eq_sym.
        exact (real_entropy_deficit_kl_temp S sumf sumpos sumext sumlinear sumadd
                 T T_pos energy p Hp Hnp Henergy).
      * apply real_eq_refl.
    + apply (real_eq_trans
               (real_plus (real_plus (slq_entropy slq_boltz slq_boltz_pos) (real_opp (slq_entropy p Hp))) eps)
               (real_plus (slq_entropy slq_boltz slq_boltz_pos) (real_plus (real_opp (slq_entropy p Hp)) eps))
               (real_plus (real_plus (slq_entropy slq_boltz slq_boltz_pos) eps) (real_opp (slq_entropy p Hp)))).
      * apply real_eq_sym.
        exact (real_plus_assoc (slq_entropy slq_boltz slq_boltz_pos) (real_opp (slq_entropy p Hp)) eps).
      * apply (real_eq_trans
                 (real_plus (slq_entropy slq_boltz slq_boltz_pos) (real_plus (real_opp (slq_entropy p Hp)) eps))
                 (real_plus (slq_entropy slq_boltz slq_boltz_pos) (real_plus eps (real_opp (slq_entropy p Hp))))
                 (real_plus (real_plus (slq_entropy slq_boltz slq_boltz_pos) eps) (real_opp (slq_entropy p Hp)))).
        -- apply (RealSetoid.real_eq_plus_compat_adapt (slq_entropy slq_boltz slq_boltz_pos) (slq_entropy slq_boltz slq_boltz_pos)
                    (real_plus (real_opp (slq_entropy p Hp)) eps)
                    (real_plus eps (real_opp (slq_entropy p Hp)))
                    (real_eq_refl (slq_entropy slq_boltz slq_boltz_pos))
                    (real_plus_comm (real_opp (slq_entropy p Hp)) eps)).
        -- exact (real_plus_assoc (slq_entropy slq_boltz slq_boltz_pos) eps (real_opp (slq_entropy p Hp))).
  - exact (Hgibbs eps Heps).
Qed.

End SlqSecondLaw.

(* ============================================================ *)
(* 第二部分：熵亏非负引理 eps 形全闭（list 载体）                   *)
(*   real_list_sum 四参数件实例化求和机器；Gibbs 肢由引擎             *)
(*   real_gibbs_inequality_eps + real_KL_temp_kl_term_bridge 闭式   *)
(*   组装（禁 plain KL≥0：全程逐 eps 形）。                         *)
(* ============================================================ *)

Theorem slq_gibbs_leg_list :
  forall (X : Type) (l : list X) (Hnil : l <> nil)
         (T : Real) (Ht : real_lt real_zero T) (energy : X -> Real)
         (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
         (Hnp : real_eq (real_list_sum X p l) real_one)
         (eps : Real) (Heps : real_lt real_zero eps),
    real_le real_zero
      (real_plus
         (real_KL_temp X (fun g : X -> Real => real_list_sum X g l)
            (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
               real_list_sum_pos X f l Hf Hnil)
            T Ht energy p Hp)
         eps).
Proof.
  intros X l Hnil T Ht energy p Hp Hnp eps Heps.
  pose proof (real_KL_temp_kl_term_bridge X (fun g : X -> Real => real_list_sum X g l)
                (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                   real_list_sum_pos X f l Hf Hnil)
                (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l)
                T Ht energy p Hp) as Hbridge.
  pose proof (real_gibbs_inequality_eps X l p
                (real_boltzmann_dist_temp X (fun g : X -> Real => real_list_sum X g l)
                   (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                      real_list_sum_pos X f l Hf Hnil)
                   T Ht energy)
                Hp
                (real_boltzmann_dist_temp_pos X (fun g : X -> Real => real_list_sum X g l)
                   (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                      real_list_sum_pos X f l Hf Hnil)
                   T Ht energy)
                Hnp
                (real_boltzmann_dist_temp_normalized X (fun g : X -> Real => real_list_sum X g l)
                   (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                      real_list_sum_pos X f l Hf Hnil)
                   (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l) (fun a0 : Real => fun f0 : X -> Real => real_list_sum_linear X a0 f0 l)
                   T Ht energy)
                eps Heps) as Heng.
  (* KL_temp ≡ Σ real_kl_term 沿 req 平移入 le *)
  apply (slq_le_resp_req_r
           real_zero
           (real_plus
              (real_list_sum X
                 (fun s : X =>
                    real_kl_term (p s)
                      (real_boltzmann_dist_temp X (fun g : X -> Real => real_list_sum X g l)
                         (fun (f : X -> Real)
                              (Hf : forall s : X, real_lt real_zero (f s)) =>
                            real_list_sum_pos X f l Hf Hnil)
                         T Ht energy s)
                      (Hp s)
                      (real_boltzmann_dist_temp_pos X (fun g : X -> Real => real_list_sum X g l)
                         (fun (f : X -> Real)
                              (Hf : forall s : X, real_lt real_zero (f s)) =>
                            real_list_sum_pos X f l Hf Hnil)
                         T Ht energy s)) l)
              eps)
           (real_plus
              (real_KL_temp X (fun g : X -> Real => real_list_sum X g l)
                 (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                    real_list_sum_pos X f l Hf Hnil)
                 T Ht energy p Hp)
              eps)).
  - apply (real_eq_sym).
    apply (RealSetoid.real_eq_plus_compat
             (real_KL_temp X (fun g : X -> Real => real_list_sum X g l)
                (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                   real_list_sum_pos X f l Hf Hnil)
                T Ht energy p Hp)
             eps
             (real_list_sum X
                (fun s : X =>
                   real_kl_term (p s)
                     (real_boltzmann_dist_temp X (fun g : X -> Real => real_list_sum X g l)
                        (fun (f : X -> Real)
                             (Hf : forall s : X, real_lt real_zero (f s)) =>
                           real_list_sum_pos X f l Hf Hnil)
                        T Ht energy s)
                     (Hp s)
                     (real_boltzmann_dist_temp_pos X (fun g : X -> Real => real_list_sum X g l)
                        (fun (f : X -> Real)
                             (Hf : forall s : X, real_lt real_zero (f s)) =>
                           real_list_sum_pos X f l Hf Hnil)
                        T Ht energy s)) l)
             eps Hbridge (real_eq_refl eps)).
  - exact Heng.
Qed.

(* 第二部分闭合：Second Law 定量读法全闭（Gibbs 肢闭式供给 t13） *)
Theorem slq_second_law_eps_list :
  forall (X : Type) (l : list X) (Hnil : l <> nil)
         (T : Real) (Ht : real_lt real_zero T) (energy : X -> Real)
         (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
         (Hnp : real_eq (real_list_sum X p l) real_one)
         (Henergy : real_eq
                      (real_list_sum X
                         (fun s : X => real_mult (p s) (energy s)) l)
                      (real_energy_exp_temp X (fun g : X -> Real => real_list_sum X g l)
                         (fun (f : X -> Real)
                              (Hf : forall s : X, real_lt real_zero (f s)) =>
                            real_list_sum_pos X f l Hf Hnil)
                         T Ht energy))
         (eps : Real) (Heps : real_lt real_zero eps),
    real_le (real_entropy_dist X (fun g : X -> Real => real_list_sum X g l) p Hp)
            (real_plus
               (real_entropy_dist X (fun g : X -> Real => real_list_sum X g l)
                  (real_boltzmann_dist_temp X (fun g : X -> Real => real_list_sum X g l)
                     (fun (f : X -> Real)
                          (Hf : forall s : X, real_lt real_zero (f s)) =>
                        real_list_sum_pos X f l Hf Hnil)
                     T Ht energy)
                  (real_boltzmann_dist_temp_pos X (fun g : X -> Real => real_list_sum X g l)
                     (fun (f : X -> Real)
                          (Hf : forall s : X, real_lt real_zero (f s)) =>
                        real_list_sum_pos X f l Hf Hnil)
                     T Ht energy))
               eps).
Proof.
  intros X l Hnil T Ht energy p Hp Hnp Henergy eps Heps.
  exact (t13_max_entropy_le_eps X (fun g : X -> Real => real_list_sum X g l)
           (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
              real_list_sum_pos X f l Hf Hnil)
           (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l) (fun a0 : Real => fun f0 : X -> Real => real_list_sum_linear X a0 f0 l) (fun f0 g0 : X -> Real => real_list_sum_add X f0 g0 l)
           T Ht energy p Hp Hnp Henergy
           (fun (e : Real) (He : real_lt real_zero e) =>
              slq_gibbs_leg_list X l Hnil T Ht energy p Hp Hnp e He)
           eps Heps).
Qed.

(* ============================================================ *)
(* 第三部分：Enhanced 侧受体坐标桥（S06 经 CW219 薄壳导出）         *)
(*   接口面全 @S01_BaseRing 全参限定（C4 顶层桥 B2 同款纪律；        *)
(*   裸 lt/le/R 经 Mod 记号会误投 Setoid 类投影，实测已避）。        *)
(* ============================================================ *)

(* 桥 1：受体 entropy_ent（S06:1610）出节体桥（C4 B2 同款 δ 闭合） *)
Theorem slq_entropy_ent_unfold :
  forall (RI : RealInterfaceEnhanced)
         (Omega_A : @S01_BaseRing.R RI -> @S01_BaseRing.R RI)
         (Omega_B : @S01_BaseRing.R RI -> @S01_BaseRing.R RI)
         (E_total k_B E_A : @S01_BaseRing.R RI),
    Id (@entropy_ent RI Omega_A Omega_B E_total k_B E_A)
       (@S01_BaseRing.mult RI k_B
          (@S01_BaseRing.log RI
             (@S01_BaseRing.mult RI (Omega_A E_A)
                (Omega_B (@S01_BaseRing.minus RI E_total E_A))))).
Proof.
  intros RI Omega_A Omega_B E_total k_B E_A.
  unfold entropy_ent, Omega_total_ent.
  exact (@id_refl _ _).
Qed.

(* 桥 2：受体 second_law_irreversible 的定量升级（使用受体定理本体）   *)
(*   严格增 lt 结论 ⟹ 逐 eps le：entropy x ≤ entropy (dynamics x)+eps。 *)
(*   出口 = @le RI（桥 tsi_rie_setoid 的 le 字段规范读法）；平移肢 =    *)
(*   C4 tsi_le_plus_eps_r 复用。前提面照受体本体（Not (Id …) 形）。     *)
Theorem slq_receiver_second_law_quant :
  forall (RI : RealInterfaceEnhanced)
         (entropy dynamics : @S01_BaseRing.R RI -> @S01_BaseRing.R RI)
         (Hstrict : forall x : @S01_BaseRing.R RI,
            Not (Id (dynamics x) x) ->
            @S01_BaseRing.lt RI (entropy x) (entropy (dynamics x)))
         (x : @S01_BaseRing.R RI) (Hx : Not (Id (dynamics x) x))
         (eps : @S01_BaseRing.R RI)
         (Heps : @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) eps),
    @S01_BaseRing.le RI (entropy x)
      (@S01_BaseRing.plus RI (entropy (dynamics x)) eps).
Proof.
  intros RI entropy dynamics Hstrict x Hx eps Heps.
  pose proof (@S06_DiffSamplingGibbs.second_law_irreversible
                RI entropy dynamics Hstrict x Hx) as Hs.
  pose proof (tsi_le_plus_eps_r RI (entropy (dynamics x)) eps Heps) as Hp.
  exact (@RealInterfaceEnhancedMod.lt_le_iff (@S01_BaseRing.R RI) (tsi_rie_setoid RI)
           (entropy x)
           (@S01_BaseRing.plus RI (entropy (dynamics x)) eps)
           (inl (@RealInterfaceEnhancedMod.lt_le_trans
                   (@S01_BaseRing.R RI) (tsi_rie_setoid RI)
                   (entropy x) (entropy (dynamics x))
                   (@S01_BaseRing.plus RI (entropy (dynamics x)) eps)
                   Hs Hp))).
Qed.

(* 桥 2'（Prop 自由孪件）：lt 前提直接形（零 Prop 语句面纪律位） *)
Theorem slq_lt_to_le_eps :
  forall (RI : RealInterfaceEnhanced)
         (a b eps : @S01_BaseRing.R RI),
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) eps ->
    @S01_BaseRing.lt RI a b ->
    @S01_BaseRing.le RI a (@S01_BaseRing.plus RI b eps).
Proof.
  intros RI a b eps Heps Hlt.
  pose proof (@RealInterfaceEnhancedMod.lt_le_trans
                (@S01_BaseRing.R RI) (tsi_rie_setoid RI)
                a b (@S01_BaseRing.plus RI b eps) Hlt
                (tsi_le_plus_eps_r RI b eps Heps)) as Hchain.
  exact (@RealInterfaceEnhancedMod.lt_le_iff (@S01_BaseRing.R RI) (tsi_rie_setoid RI)
           a (@S01_BaseRing.plus RI b eps) (inl Hchain)).
Qed.

(* 桥 3：tsi_rie_setoid 承重出口面——同一定量结论经桥实例 le/plus        *)
(*   字段陈述（与 Enhanced le/plus iota 可转换，exact 闭合；即 C4        *)
(*   头注桥 req/le 端规范模型读法的显式兑现）。                        *)
Definition slq_bridge_le (RI : RealInterfaceEnhanced)
           (a b : @S01_BaseRing.R RI) : Set :=
  @RealInterfaceEnhancedMod.le (@S01_BaseRing.R RI) (tsi_rie_setoid RI) a b.

Theorem slq_second_law_setoid_frame :
  forall (RI : RealInterfaceEnhanced)
         (entropy dynamics : @S01_BaseRing.R RI -> @S01_BaseRing.R RI)
         (x : @S01_BaseRing.R RI) (eps : @S01_BaseRing.R RI)
         (Heps : @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) eps)
         (Hlt : @S01_BaseRing.lt RI (entropy x) (entropy (dynamics x))),
    slq_bridge_le RI (entropy x)
      (@S01_BaseRing.plus RI (entropy (dynamics x)) eps).
Proof.
  intros RI entropy dynamics x eps Heps Hlt.
  unfold slq_bridge_le.
  apply (@RealInterfaceEnhancedMod.lt_le_iff (@S01_BaseRing.R RI) (tsi_rie_setoid RI)
           (entropy x) (@S01_BaseRing.plus RI (entropy (dynamics x)) eps)).
  left.
  exact (@RealInterfaceEnhancedMod.lt_le_trans
           (@S01_BaseRing.R RI) (tsi_rie_setoid RI)
           (entropy x) (entropy (dynamics x))
           (@S01_BaseRing.plus RI (entropy (dynamics x)) eps)
           Hlt (tsi_le_plus_eps_r RI (entropy (dynamics x)) eps Heps)).
Qed.

(* ===================================================================== *)
(* 审查留痕：Print Assumptions（G4）                                       *)
(* ===================================================================== *)
Print Assumptions slq_entropy_gain_kl_lower.
Print Assumptions slq_step_gain_kl_lower.
Print Assumptions slq_second_law_eps_list.
Print Assumptions slq_receiver_second_law_quant.
Print Assumptions slq_second_law_setoid_frame.

(* ################ 假设消解块（C2 底册 #6） ##################### *)
(* sumf 消解实例读法：csm_sumf 列表折叠机（ConcMixSelFeed cms_ 系同键）；   *)
(*   四求和参数位与 T 实例位在此读法下逐一供给。sumpos 参数位的非空性以 cons 形     *)
(*   承载（列表头见证直接供给，零 Prop 前提；任意非空枚举形的整体导出      *)
(*   留待后续批组）。                                                       *)

From Stdlib Require Import List.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import ConcMixSelFeed.
Require Import UpReqConcFin2.

(* sumf 消解实例读法定义件（csm_sumf 的本件别名，delta 透明） *)
Definition slqr_sumf (S0 : Set) (en : list S0) (f : S0 -> Real) : Real :=
  csm_sumf S0 en f.

(* sumext 参数位（语句面取供给同常量系 req 形：逐点外延，与 real_eq 定义性同义）       *)
Theorem slqr_sumext : forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
  (forall s : S0, req (f s) (g s)) ->
  req (slqr_sumf S0 en f) (slqr_sumf S0 en g).
Proof.
  intros S0 en f g H.
  exact (cms_sum_ext S0 en f g H).
Qed.

(* sumlinear 参数位（语句面取供给同常量系 req/mult 形：系数提出） *)
Theorem slqr_sumlinear :
  forall (S0 : Set) (en : list S0) (a : Real) (f : S0 -> Real),
    req (slqr_sumf S0 en (fun s : S0 => mult a (f s)))
            (mult a (slqr_sumf S0 en f)).
Proof.
  intros S0 en a f.
  exact (cms_sum_linear S0 en a f).
Qed.

(* sumadd 参数位（语句面取供给同常量系 req/plus 形：逐点加法分配） *)
Theorem slqr_sumadd : forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
  req (slqr_sumf S0 en (fun s : S0 => plus (f s) (g s)))
          (plus (slqr_sumf S0 en f) (slqr_sumf S0 en g)).
Proof.
  intros S0 en f g.
  exact (cms_sum_add S0 en f g).
Qed.

(* sumpos 参数位（cons 形：非空性由列表头见证承载，零 Prop 前提；               *)
(*   UpReqSumD sumd_list_sum_pos_cons 直接供给，语句面取同款 lt zero 形）        *)
Theorem slqr_sumpos_cons :
  forall (S0 : Set) (f : S0 -> Real) (x : S0) (l : list S0),
    (forall s : S0, lt zero (f s)) ->
    lt zero (slqr_sumf S0 (cons x l) f).
Proof.
  intros S0 f x l H.
  exact (sumd_list_sum_pos_cons S0 f x l H).
Qed.

(* T_pos 参数位三态：抽象 T 的温度正性=真前提嫌疑，按 b3 §2.2 保留并声明为      *)
(*   接口义务，禁硬证。以下仅为具体实例读法证书（T := one），供给源         *)
(*   real_lt_zero_one（S07 同常量直供，slqr_T≡one delta 内核已认）。                     *)
Definition slqr_T : Real := one.

Theorem slqr_T_pos : real_lt real_zero slqr_T.
Proof.
  exact real_lt_zero_one.
Qed.

(* ================= 消解块假设面核验（预期全 Closed） ==================== *)
Print Assumptions slqr_sumext.
Print Assumptions slqr_sumlinear.
Print Assumptions slqr_sumadd.
Print Assumptions slqr_sumpos_cons.
Print Assumptions slqr_T_pos.
