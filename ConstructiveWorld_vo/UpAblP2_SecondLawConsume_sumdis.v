(* ==========================================================================)
   UpAblP2_SecondLawConsume_sumdis.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：slc_minus_r_plus_cancel、slc_plus_r_assoc_cancel、slc_plus_comm_r_shift、slc_kl_le_gain_plus_leg、slc_gain_le_kl_plus_leg、slc_gain_kl_two_sided_eps、slc_gain_ge_kl_minus_eps、slc_kl_boltz_self_zero、slc_second_law_kl_floor_eps_list。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
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
Require Import SecondLawQuantified.
Require Import UpReqPinskerTransport.
From Stdlib Require Import List.

(* ================= §1 slc_minus_r_plus_cancel 族 ================= *)
(* ---------------------------------------------------------- *)
(* 件 0：Set 层带状对（双边定量语句面；set 层 inductive，零 Prop）  *)
(* ---------------------------------------------------------- *)
Inductive slc_band (A B : Set) : Set :=
| slc_band_intro : A -> B -> slc_band A B.

(* ---------------------------------------------------------- *)
(* 件 1–3：real 算术 choreography 三辅助引理（全 real_eq 档）        *)
(*   (a−b)+b == a ／ (a+b)+(−b) == a ＋ (x+y)+(−z) == (x+(−z))+y  *)
(* ---------------------------------------------------------- *)
Lemma slc_minus_r_plus_cancel :
  forall a b : Real,
    real_eq (real_plus (real_minus_r a b) b) a.
Proof.
  intros a b.
  exact (real_eq_trans           (real_plus (real_minus_r a b) b)           (real_plus a (real_plus (real_opp b) b))           a           (real_eq_sym (real_plus a (real_plus (real_opp b) b))                        (real_plus (real_plus a (real_opp b)) b)                        (real_plus_assoc a (real_opp b) b))           (real_eq_trans              (real_plus a (real_plus (real_opp b) b))              (real_plus a (real_plus b (real_opp b)))              a              (RealSetoid.real_eq_plus_compat_adapt a a                 (real_plus (real_opp b) b) (real_plus b (real_opp b))                 (real_eq_refl a) (real_plus_comm (real_opp b) b))              (real_eq_trans                 (real_plus a (real_plus b (real_opp b)))                 (real_plus a real_zero)                 a                 (RealSetoid.real_eq_plus_compat_adapt a a                    (real_plus b (real_opp b)) real_zero                    (real_eq_refl a) (real_plus_opp b))                 (real_plus_zero a)))).
Qed.

Lemma slc_plus_r_assoc_cancel :
  forall a b : Real,
    real_eq (real_plus (real_plus a b) (real_opp b)) a.
Proof.
  intros a b.
  exact (real_eq_trans           (real_plus (real_plus a b) (real_opp b))           (real_plus a (real_plus b (real_opp b)))           a           (real_eq_sym (real_plus a (real_plus b (real_opp b)))                        (real_plus (real_plus a b) (real_opp b))                        (real_plus_assoc a b (real_opp b)))           (real_eq_trans              (real_plus a (real_plus b (real_opp b)))              (real_plus a real_zero)              a              (RealSetoid.real_eq_plus_compat_adapt a a                 (real_plus b (real_opp b)) real_zero                 (real_eq_refl a) (real_plus_opp b))              (real_plus_zero a))).
Qed.

Lemma slc_plus_comm_r_shift :
  forall x y z : Real,
    real_eq (real_plus (real_plus x y) (real_opp z))
            (real_plus (real_plus x (real_opp z)) y).
Proof.
  intros x y z.
  exact (real_eq_trans           (real_plus (real_plus x y) (real_opp z))           (real_plus x (real_plus y (real_opp z)))           (real_plus (real_plus x (real_opp z)) y)           (real_eq_sym (real_plus x (real_plus y (real_opp z)))                        (real_plus (real_plus x y) (real_opp z))                        (real_plus_assoc x y (real_opp z)))           (real_eq_trans              (real_plus x (real_plus y (real_opp z)))              (real_plus x (real_plus (real_opp z) y))              (real_plus (real_plus x (real_opp z)) y)              (RealSetoid.real_eq_plus_compat_adapt x x                 (real_plus y (real_opp z)) (real_plus (real_opp z) y)                 (real_eq_refl x) (real_plus_comm y (real_opp z)))              (real_plus_assoc x (real_opp z) y))).
Qed.

(* 第一部分：任意和机器上的双边使用（Section 槽照 slq 同形同序）    *)

Section SlcSecondLawConsume.

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
Variable T : Real.
Hypothesis T_pos : real_lt real_zero T.
Variable energy : S -> Real.

(* 支路 1：KL ≤ 熵增 + eps（lower 之 plus 形；使用 slq_entropy_gain_kl_lower） *)
Lemma slc_kl_le_gain_plus_leg :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    forall eps : Real, real_lt real_zero eps ->
      real_le (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
              (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps).
Proof.
  intros p Hp Hnp Henergy eps Heps.
  pose proof (slq_entropy_gain_kl_lower S sumf sumpos sumext sumlinear sumadd
                T T_pos energy p Hp Hnp Henergy eps Heps) as Hlow.
  exact (RealSetoid.real_le_id_r
           (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
           (real_plus eps (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
           (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps)
           (real_plus_comm eps (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
           (RealSetoid.real_le_id_l
              (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
              (real_plus (real_minus_r (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                                       (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
                         (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
              (real_plus eps (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
              (real_eq_sym
                 (real_plus (real_minus_r (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                                          (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
                            (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
                 (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                 (slc_minus_r_plus_cancel
                    (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                    (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)))
              (real_le_plus_compat
                 (real_minus_r (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                               (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
                 eps
                 (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                 (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                 Hlow
                 (real_le_refl (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))))).
Qed.

(* 支路 2：熵增 ≤ KL + eps（upper 之 plus 形；使用 slq_entropy_gain_kl_upper） *)
Lemma slc_gain_le_kl_plus_leg :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    forall eps : Real, real_lt real_zero eps ->
      real_le (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
              (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps).
Proof.
  intros p Hp Hnp Henergy eps Heps.
  pose proof (slq_entropy_gain_kl_upper S sumf sumpos sumext sumlinear sumadd
                T T_pos energy p Hp Hnp Henergy eps Heps) as Hup.
  exact (RealSetoid.real_le_id_r
           (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
           (real_plus eps (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
           (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps)
           (real_plus_comm eps (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
           (RealSetoid.real_le_id_l
              (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
              (real_plus (real_minus_r (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                                       (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
                         (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
              (real_plus eps (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
              (real_eq_sym
                 (real_plus (real_minus_r (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                                          (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
                            (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
                 (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                 (slc_minus_r_plus_cancel
                    (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                    (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)))
              (real_le_plus_compat
                 (real_minus_r (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                               (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
                 eps
                 (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                 (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                 Hup
                 (real_le_refl (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))))).
Qed.

(* ---------------------------------------------------------- *)
(* 主件 1：per-eps 双边定量（Set 层带状对，下界+上界合并装配） *)
(*   |S[p_T] − S[p] − KL(p‖p_T)| 的逐 eps 带状读法：                *)
(*   KL ≤ 增 + eps 且 增 ≤ KL + eps。                                *)
(* ---------------------------------------------------------- *)
Theorem slc_gain_kl_two_sided_eps :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    forall eps : Real, real_lt real_zero eps ->
      slc_band
        (real_le (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                 (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps))
        (real_le (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                 (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps)).
Proof.
  intros p Hp Hnp Henergy eps Heps.
  exact (slc_band_intro           (real_le (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)                    (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps))           (real_le (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)                    (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps))           (slc_kl_le_gain_plus_leg p Hp Hnp Henergy eps Heps)           (slc_gain_le_kl_plus_leg p Hp Hnp Henergy eps Heps)).
Qed.

(* ---------------------------------------------------------- *)
(* 主件 2：熵增益 ≥ KL 缺陷 − eps（显式使用形；回喂基座使用位）      *)
(*   real_le (KL − eps) 增——lower 的 minus-r 地板形。               *)
(* ---------------------------------------------------------- *)
Theorem slc_gain_ge_kl_minus_eps :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    forall eps : Real, real_lt real_zero eps ->
      real_le (real_minus_r (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps)
              (slq_entropy_gain S sumf sumpos T T_pos energy p Hp).
Proof.
  intros p Hp Hnp Henergy eps Heps.
  exact (RealSetoid.real_le_id_r           (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) (real_opp eps))           (real_plus (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps)                      (real_opp eps))           (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)           (slc_plus_r_assoc_cancel (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps)           (real_le_plus_compat              (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)              (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps)              (real_opp eps)              (real_opp eps)              (slc_kl_le_gain_plus_leg p Hp Hnp Henergy eps Heps)              (real_le_refl (real_opp eps)))).
Qed.

End SlcSecondLawConsume.

(* 第二部分：list 机器全闭双使用（核心定理 × eps_list 使用链）       *)

(* ---------------------------------------------------------- *)
(* 主件 3：均衡点 KL 归零——核心定理在 p := p_T 处实例化（全闭）      *)
(*   归一化（boltzmann_normalized）+ 同能量（E(p_T) == E_T 定义性）    *)
(*   ⟹ S[p_T] − S[p_T] == KL(p_T‖p_T) ⟹ KL(p_T‖p_T) == 0。          *)
(* ---------------------------------------------------------- *)
Theorem slc_kl_boltz_self_zero :
  forall (X : Type) (l : list X) (Hnil : l <> nil)
         (T : Real) (Ht : real_lt real_zero T) (energy : X -> Real),
    real_eq real_zero
      (slq_kl_cur_boltz X (fun g : X -> Real => real_list_sum X g l)
         (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
            real_list_sum_pos X f l Hf Hnil)
         T Ht energy
         (real_boltzmann_dist_temp X (fun g : X -> Real => real_list_sum X g l)
            (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
               real_list_sum_pos X f l Hf Hnil)
            T Ht energy)
         (real_boltzmann_dist_temp_pos X (fun g : X -> Real => real_list_sum X g l)
            (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
               real_list_sum_pos X f l Hf Hnil)
            T Ht energy)).
Proof.
  intros X l Hnil T Ht energy.
  set (SF := fun g : X -> Real => real_list_sum X g l).
  set (SP := fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
               real_list_sum_pos X f l Hf Hnil).
  set (B := real_boltzmann_dist_temp X SF SP T Ht energy).
  set (Bp := real_boltzmann_dist_temp_pos X SF SP T Ht energy).
  set (SD := real_entropy_dist X SF B Bp).
  pose proof (real_entropy_deficit_kl_temp X SF SP
                (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l)
                (fun (a0 : Real) (f0 : X -> Real) => real_list_sum_linear X a0 f0 l)
                (fun f0 g0 : X -> Real => real_list_sum_add X f0 g0 l)
                T Ht energy B Bp
                (real_boltzmann_dist_temp_normalized X SF SP
                   (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l)
                   (fun (a0 : Real) (f0 : X -> Real) => real_list_sum_linear X a0 f0 l)
                   T Ht energy)
                (real_eq_refl
                   (real_energy_exp_temp X SF SP T Ht energy))) as Hdef.
  unfold real_minus_r in Hdef.
  exact (real_eq_sym
           (real_KL_temp X SF SP T Ht energy B Bp) real_zero
           (real_eq_trans
              (real_KL_temp X SF SP T Ht energy B Bp)
              (real_plus SD (real_opp SD))
              real_zero
              (real_eq_sym (real_plus SD (real_opp SD))
                           (real_KL_temp X SF SP T Ht energy B Bp)
                           Hdef)
              (real_plus_opp SD))).
Qed.

(* ---------------------------------------------------------- *)
(* 主件 4：Second Law eps 档 × 核心恒等式合流 ⟹ KL ≥ −eps            *)
(*   使用 slq_second_law_eps_list（S[p] ≤ S[p_T]+eps）与核心定理      *)
(*   （S[p_T]−S[p] == KL）双源：0 ≤ 增+eps 沿恒等式换载 ⟹ −eps ≤ KL。 *)
(* ---------------------------------------------------------- *)
Theorem slc_second_law_kl_floor_eps_list :
  forall (X : Type) (l : list X) (Hnil : l <> nil)
         (T : Real) (Ht : real_lt real_zero T) (energy : X -> Real)
         (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
         (Hnp : real_eq (real_list_sum X p l) real_one)
         (Henergy : real_eq
                      (real_list_sum X (fun s : X => real_mult (p s) (energy s)) l)
                      (real_energy_exp_temp X (fun g : X -> Real => real_list_sum X g l)
                         (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                            real_list_sum_pos X f l Hf Hnil)
                         T Ht energy))
         (eps : Real) (Heps : real_lt real_zero eps),
    real_le (real_opp eps)
            (slq_kl_cur_boltz X (fun g : X -> Real => real_list_sum X g l)
               (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                  real_list_sum_pos X f l Hf Hnil)
               T Ht energy p Hp).
Proof.
  intros X l Hnil T Ht energy p Hp Hnp Henergy eps Heps.
  pose proof (slq_second_law_eps_list X l Hnil T Ht energy p Hp Hnp Henergy eps Heps) as Hsl.
  pose proof (real_entropy_deficit_kl_temp X
                (fun g : X -> Real => real_list_sum X g l)
                (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                   real_list_sum_pos X f l Hf Hnil)
                (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l)
                (fun (a0 : Real) (f0 : X -> Real) => real_list_sum_linear X a0 f0 l)
                (fun f0 g0 : X -> Real => real_list_sum_add X f0 g0 l)
                T Ht energy p Hp Hnp Henergy) as Hdef.
  set (SF := fun g : X -> Real => real_list_sum X g l) in *.
  set (SP := fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
               real_list_sum_pos X f l Hf Hnil) in *.
  set (Sp := real_entropy_dist X SF p Hp) in *.
  set (Sb := real_entropy_dist X SF
               (real_boltzmann_dist_temp X SF SP T Ht energy)
               (real_boltzmann_dist_temp_pos X SF SP T Ht energy)) in *.
  set (K := real_KL_temp X SF SP T Ht energy p Hp) in *.
  (* 步 1：eps_list 加 −Sp ⟹ 0 ≤ (Sb+eps)+(−Sp) *)
  pose proof (RealSetoid.real_le_id_l real_zero
                (real_plus Sp (real_opp Sp))
                (real_plus (real_plus Sb eps) (real_opp Sp))
                (real_eq_sym (real_plus Sp (real_opp Sp)) real_zero
                             (real_plus_opp Sp))
                (real_le_plus_compat Sp (real_plus Sb eps)
                 (real_opp Sp) (real_opp Sp)
                 Hsl (real_le_refl (real_opp Sp)))) as Hstep1.
  (* 步 2：换序 ⟹ 0 ≤ (Sb+(−Sp))+eps = 0 ≤ 增+eps *)
  pose proof (RealSetoid.real_le_id_r real_zero
                (real_plus (real_plus Sb eps) (real_opp Sp))
                (real_plus (real_plus Sb (real_opp Sp)) eps)
                (slc_plus_comm_r_shift Sb eps Sp)
                Hstep1) as Hstep2.
  (* 步 3：沿核心恒等式 增 == KL 换载 ⟹ 0 ≤ KL+eps *)
  pose proof (RealSetoid.real_le_id_r real_zero
                (real_plus (real_minus_r Sb Sp) eps)
                (real_plus K eps)
                (RealSetoid.real_eq_plus_compat_adapt (real_minus_r Sb Sp) K eps eps
                   Hdef (real_eq_refl eps))
                Hstep2) as Hstep3.
  (* 步 4：加 −eps ⟹ −eps ≤ (KL+eps)+(−eps) *)
  pose proof (real_le_plus_compat real_zero (real_plus K eps)
                 (real_opp eps) (real_opp eps)
                 Hstep3 (real_le_refl (real_opp eps))) as Hstep4.
  (* 步 5：归零闭合 ⟹ −eps ≤ KL *)
  exact (RealSetoid.real_le_id_r (real_opp eps)
           (real_plus (real_plus K eps) (real_opp eps))
           K
           (slc_plus_r_assoc_cancel K eps)
           (RealSetoid.real_le_id_l (real_opp eps)
              (real_plus real_zero (real_opp eps))
              (real_plus (real_plus K eps) (real_opp eps))
              (real_eq_sym (real_plus real_zero (real_opp eps)) (real_opp eps)
                 (real_eq_trans (real_plus real_zero (real_opp eps))
                                (real_plus (real_opp eps) real_zero)
                                (real_opp eps)
                                (real_plus_comm real_zero (real_opp eps))
                                (real_plus_zero (real_opp eps))))
              Hstep4)).
Qed.

(* 审查留痕：Print Assumptions（G4）                                       *)
Print Assumptions slc_gain_kl_two_sided_eps.
Print Assumptions slc_gain_ge_kl_minus_eps.
Print Assumptions slc_kl_boltz_self_zero.
Print Assumptions slc_second_law_kl_floor_eps_list.
(* ================= §2 uabp2_slc_sumpos_list 族 ================= *)
Import ListNotations.

(* ============ A1 ←L132-134 sumpos（逐字语句，sumf 换 real_list_sum 实例） ============ *)
(* 原参数位（节内）：forall (f : S -> Real),
     (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (sumf f) *)
Theorem uabp2_slc_sumpos_list :
  forall (X : Type) (l : list X) (Hnil : l <> nil) (f : X -> Real),
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum X f l).
Proof.
  intros X l Hnil f Hf.
  exact (real_list_sum_pos X f l Hf Hnil).
Qed.

(* ============ A2 ←L135-136 sumext ============ *)
(* 原参数位：forall (f g : S -> Real),
     (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g) *)
Theorem uabp2_slc_sumext_list :
  forall (X : Type) (f g : X -> Real) (l : list X),
    (forall s : X, real_eq (f s) (g s)) ->
    real_eq (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l H.
  exact (real_list_sum_ext X f g l H).
Qed.

Theorem uabp2_slc_sumext_pnt :
  forall (X : Type) (f g : X -> Real) (l : list X),
    (forall s : X, real_eq (f s) (g s)) ->
    real_eq (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l H.
  exact (pnt_list_sum_eq_ext X f g l H).
Qed.

(* ============ A3 ←L137-138 sumlinear ============ *)
(* 原参数位：forall (a : Real) (f : S -> Real),
     real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)) *)
Theorem uabp2_slc_sumlinear_list :
  forall (X : Type) (a : Real) (f : X -> Real) (l : list X),
    real_eq (real_list_sum X (fun s : X => real_mult a (f s)) l)
            (real_mult a (real_list_sum X f l)).
Proof.
  intros X a f l.
  exact (real_list_sum_linear X a f l).
Qed.

(* ============ A4 ←L139-141 sumadd ============ *)
(* 原参数位：forall (f g : S -> Real),
     real_eq (sumf (fun s : S => real_plus (f s) (g s)))
             (real_plus (sumf f) (sumf g)) *)
Theorem uabp2_slc_sumadd_list :
  forall (X : Type) (f g : X -> Real) (l : list X),
    real_eq (real_list_sum X (fun s : X => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum X f l) (real_list_sum X g l)).
Proof.
  intros X f g l.
  exact (real_list_sum_add X f g l).
Qed.

(* ============ A5 ←节主件 L235 slc_gain_kl_two_sided_eps 之 4 槽零假设版 ============ *)
(* 出节全参形（About 实证 15 参）：X SF SP SE SL SA T Ht energy p Hp Hnp Henergy   *)
(* eps Heps；4 求和槽以实例见证直接代入（源文件自身 L322-324/L358-360 同款插件）。        *)
(* 实例求和机器：SF := fun g => real_list_sum X g l（固定清单 l＋非空见证 Hnil）。  *)
Theorem uabp2_slc_two_sided_list :
  forall (X : Type) (l : list X) (Hnil : l <> nil)
         (T : Real) (Ht : real_lt real_zero T)
         (energy p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
    real_eq (real_list_sum X p l) real_one ->
    real_eq (real_list_sum X (fun s : X => real_mult (p s) (energy s)) l)
            (real_energy_exp_temp X (fun g : X -> Real => real_list_sum X g l)
               (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                  real_list_sum_pos X f l Hf Hnil)
               T Ht energy) ->
    forall eps : Real, real_lt real_zero eps ->
      slc_band
        (real_le (slq_kl_cur_boltz X (fun g : X -> Real => real_list_sum X g l)
                    (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                       real_list_sum_pos X f l Hf Hnil)
                    T Ht energy p Hp)
                 (real_plus (slq_entropy_gain X (fun g : X -> Real => real_list_sum X g l)
                               (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                                  real_list_sum_pos X f l Hf Hnil)
                               T Ht energy p Hp) eps))
        (real_le (slq_entropy_gain X (fun g : X -> Real => real_list_sum X g l)
                    (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                       real_list_sum_pos X f l Hf Hnil)
                    T Ht energy p Hp)
                 (real_plus (slq_kl_cur_boltz X (fun g : X -> Real => real_list_sum X g l)
                               (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                                  real_list_sum_pos X f l Hf Hnil)
                               T Ht energy p Hp) eps)).
Proof.
  intros X l Hnil T Ht energy p Hp Hnp Henergy eps Heps.
  exact (slc_band_intro
           (real_le (slq_kl_cur_boltz X (fun g : X -> Real => real_list_sum X g l)
                       (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                          real_list_sum_pos X f l Hf Hnil)
                       T Ht energy p Hp)
                    (real_plus (slq_entropy_gain X (fun g : X -> Real => real_list_sum X g l)
                                  (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                                     real_list_sum_pos X f l Hf Hnil)
                                  T Ht energy p Hp) eps))
           (real_le (slq_entropy_gain X (fun g : X -> Real => real_list_sum X g l)
                       (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                          real_list_sum_pos X f l Hf Hnil)
                       T Ht energy p Hp)
                    (real_plus (slq_kl_cur_boltz X (fun g : X -> Real => real_list_sum X g l)
                                  (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                                     real_list_sum_pos X f l Hf Hnil)
                                  T Ht energy p Hp) eps))
           (slc_kl_le_gain_plus_leg X
              (fun g : X -> Real => real_list_sum X g l)
              (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                 real_list_sum_pos X f l Hf Hnil)
              (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l)
              (fun (a0 : Real) (f0 : X -> Real) => real_list_sum_linear X a0 f0 l)
              (fun f0 g0 : X -> Real => real_list_sum_add X f0 g0 l)
              T Ht energy p Hp Hnp Henergy eps Heps)
           (slc_gain_le_kl_plus_leg X
              (fun g : X -> Real => real_list_sum X g l)
              (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                 real_list_sum_pos X f l Hf Hnil)
              (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l)
              (fun (a0 : Real) (f0 : X -> Real) => real_list_sum_linear X a0 f0 l)
              (fun f0 g0 : X -> Real => real_list_sum_add X f0 g0 l)
              T Ht energy p Hp Hnp Henergy eps Heps)).
Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabp2_slc_sumpos_list.
Print Assumptions uabp2_slc_sumext_list.
Print Assumptions uabp2_slc_sumext_pnt.
Print Assumptions uabp2_slc_sumlinear_list.
Print Assumptions uabp2_slc_sumadd_list.
Print Assumptions uabp2_slc_two_sided_list.
