(* ==========================================================================)
   UpReqELBOTight.v — ELBO 紧性
   使命: t12_tangent_eq（切面等式）、t12_elbo_tight_forward/t12_elbo_tight_backward/t12_elbo_tight（KL 零 ⟺ ELBO 紧，双向）与 t12_elbo_tight_bool/t12_elbo_tight_forward_bool 两点实例。
   依赖: CW_ConstructiveWorld_219、UpReqRealFEP、UpReqELBOEps、UpReqKLSTangent、G08_Gibbs；Stdlib List
   对标: 变分推断 ELBO 紧性（KL(q‖p)=0 当且仅当 q 达后验；自由能变分原理）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

From Stdlib Require Import List.
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
Require Import UpReqRealFEP.
Require Import UpReqELBOEps.
Require Import UpReqKLSTangent.
Require Import G08_Gibbs.
Import ListNotations.

(* ---------------------------------------------------------- *)
(* 件 0：切点式谓词（显式前提形的逐点结论面，Set 层）                    *)
(*   对位 G08 gibbe2_kl_zero_tangent_eq 的逐点结论：                    *)

(* ---------------------------------------------------------- *)

Definition t12_tangent_eq
  (S : Type) (real_base_loss : S -> Real) (D : Real)
  (D_pos : real_lt real_zero D) (Z_align_r : Real)
  (Z_align_r_pos : real_lt real_zero Z_align_r)
  (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s))
  (s : S) :=
  real_eq
    (real_log
       (real_mult (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                  (real_inv_pos (q s) (Hq s)))
       (real_mult_positive
          (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
          (real_inv_pos (q s) (Hq s))
          (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
          (real_inv_pos_pos (q s) (Hq s))))
    (real_plus
       (real_mult (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                  (real_inv_pos (q s) (Hq s)))
       (real_opp real_one)).

(* ---------------------------------------------------------- *)
(* 件 1：紧致核——紧致假设 ⟹ KL ≡ 0（抽象载体）                          *)
(*   ⟹ ELBO ≡ ELBO + D·KL ⟹ 加法消去 ⟹ D·KL ≡ 0 ⟹ D>0 右因子消去      *)
(*   ⟹ KL ≡ 0。                                                         *)
(* ---------------------------------------------------------- *)

Lemma t12_tight_kl_zero :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s)),
  real_eq (real_sum_over_S q) real_one ->
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one ->
  real_eq (real_elbo S real_sum_over_S real_base_loss D q Hq)
          (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos) ->
  real_eq (real_sum_over_S
             (fun s : S => real_kl_term (q s)
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                (Hq s)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
          real_zero.
Proof.
  intros S real_sum_over_S sumf_ext sumf_add sumf_linear
         real_base_loss D D_pos Z_align_r Z_align_r_pos
         q Hq Hnormq Hnormb Htight.
  set (pb := real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (pbpos := real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (KLsum := real_sum_over_S (fun s : S => real_kl_term (q s) (pb s) (Hq s) (pbpos s))).
  assert (Hdec : real_eq (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                         (real_plus (real_elbo S real_sum_over_S real_base_loss D q Hq)
                                    (real_mult D KLsum))).
  { exact (real_evidence_kl_decomp S real_sum_over_S sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb). }
  (* 第 2 步：紧致假设沿等值核运输：ELBO ≡ ELBO + D·KL *)
  assert (Hloop : real_eq (real_elbo S real_sum_over_S real_base_loss D q Hq)
                          (real_plus (real_elbo S real_sum_over_S real_base_loss D q Hq)
                                     (real_mult D KLsum))).
  { exact (real_eq_trans (real_elbo S real_sum_over_S real_base_loss D q Hq)
                         (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                         (real_plus (real_elbo S real_sum_over_S real_base_loss D q Hq)
                                    (real_mult D KLsum))
                         Htight Hdec). }
  (* 第 3 步：加法消去：D·KL ≡ 0（S08 real_eq_plus_cancel_l） *)
  assert (Hdk : real_eq (real_mult D KLsum) real_zero).
  { apply (real_eq_plus_cancel_l (real_elbo S real_sum_over_S real_base_loss D q Hq)
                                 (real_mult D KLsum) real_zero).
    apply (real_eq_trans
             (real_plus (real_elbo S real_sum_over_S real_base_loss D q Hq)
                        (real_mult D KLsum))
             (real_elbo S real_sum_over_S real_base_loss D q Hq)
             (real_plus (real_elbo S real_sum_over_S real_base_loss D q Hq) real_zero)).
    - exact (real_eq_sym (real_elbo S real_sum_over_S real_base_loss D q Hq)
                         (real_plus (real_elbo S real_sum_over_S real_base_loss D q Hq)
                                    (real_mult D KLsum))
                         Hloop).
    - exact (real_eq_sym (real_plus (real_elbo S real_sum_over_S real_base_loss D q Hq) real_zero)
                         (real_elbo S real_sum_over_S real_base_loss D q Hq)
                         (real_plus_zero (real_elbo S real_sum_over_S real_base_loss D q Hq))). }
  (* 第 4 步：D>0 消去：KL ≡ 0（comm 两次 + S08 右因子消去） *)
  apply (real_eq_mult_cancel_r KLsum real_zero D D_pos).
  apply (real_eq_trans (real_mult KLsum D) real_zero (real_mult real_zero D)).
  - apply (real_eq_trans (real_mult KLsum D) (real_mult D KLsum) real_zero).
    + exact (real_mult_comm KLsum D).
    + exact Hdk.
  - exact (real_eq_trans real_zero (real_mult D real_zero) (real_mult real_zero D)
             (real_eq_sym (real_mult D real_zero) real_zero (real_mult_zero D))
             (real_mult_comm D real_zero)).
Qed.

(* ---------------------------------------------------------- *)
(* 件 2：正向半边（抽象载体，显式前提形）——定理 4.8 的 ⟹ 半边           *)
(*   紧致（ELBO ≡ evidence）+ 显式接口前提（KL≡0 ⟹ 逐点切点式）         *)
(*   ⟹ 逐点 q s ≡ p_b s。                                               *)
(*   逐点消去链：切点式 + t1_log_eq_linear_inject（切点⟹一，       *)
(*   无条件）⟹ 比值一 ⟹ gibbe2 主件尾链同款消去 ⟹ q s ≡ p_b s。        *)
(* ---------------------------------------------------------- *)

Theorem t12_elbo_tight_forward :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s)),
  real_eq (real_sum_over_S q) real_one ->
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one ->
  (* 显式接口前提位（载体诚实接口）：KL ≡ 0 ⟹ 逐点切点式；
     bool 载体上由件 5 整链消解（整链件直达），零残留。 *)
  (real_eq (real_sum_over_S
              (fun s : S => real_kl_term (q s)
                 (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                 (Hq s)
                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
           real_zero ->
   forall s : S,
     t12_tangent_eq S real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq s) ->
  real_eq (real_elbo S real_sum_over_S real_base_loss D q Hq)
          (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos) ->
  forall s : S,
    real_eq (q s)
            (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s).
Proof.
  intros S real_sum_over_S sumf_ext sumf_add sumf_linear
         real_base_loss D D_pos Z_align_r Z_align_r_pos
         q Hq Hnormq Hnormb Htan0 Htight s.
  set (pb := real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (pbpos := real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  (* 第 1 步：紧致核（件 1）：KL ≡ 0 *)
  assert (Hkl0 : real_eq (real_sum_over_S
                            (fun s0 : S => real_kl_term (q s0) (pb s0) (Hq s0) (pbpos s0)))
                         real_zero).
  { exact (t12_tight_kl_zero S real_sum_over_S sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb Htight). }
  (* 第 2 步：切点式 + 「切点⟹一」（无条件消解）⟹ 比值一 *)
  assert (Hu1 : real_eq (real_mult (pb s) (real_inv_pos (q s) (Hq s))) real_one).
  { apply (t1_log_eq_linear_inject (real_mult (pb s) (real_inv_pos (q s) (Hq s)))
             (real_mult_positive (pb s) (real_inv_pos (q s) (Hq s))
                (pbpos s) (real_inv_pos_pos (q s) (Hq s)))).
    exact (Htan0 Hkl0 s). }
  (* 第 3 步：比值一 ⟹ q s ≡ p_b s（gibbe2 主件尾链同款） *)
  apply (real_eq_trans (q s)
           (real_mult (q s) (real_mult (pb s) (real_inv_pos (q s) (Hq s))))
           (pb s)).
  - apply (real_eq_trans (q s) (real_mult (q s) real_one)
             (real_mult (q s) (real_mult (pb s) (real_inv_pos (q s) (Hq s))))).
    + exact (real_eq_sym (real_mult (q s) real_one) (q s) (real_mult_one (q s))).
    + exact (RealSetoid.real_eq_mult_compat (q s) real_one (q s)
               (real_mult (pb s) (real_inv_pos (q s) (Hq s)))
               (real_eq_refl (q s))
               (real_eq_sym (real_mult (pb s) (real_inv_pos (q s) (Hq s))) real_one Hu1)).
  - exact (gibbsd_p_mult_ratio (q s) (pb s) (Hq s)).
Qed.

(* ---------------------------------------------------------- *)
(* 件 3：逆向半边（抽象载体，零接口前提）——定理 4.8 的 ⟸ 半边           *)
(*   逐点 q s ≡ p_b s ⟹ 自由能等（rfep_free_energy_ext_r，仅 ext 接口） *)
(*   ⟹ real_opp 兼容 ⟹ ELBO(q) ≡ evidence。                            *)
(* ---------------------------------------------------------- *)

Theorem t12_elbo_tight_backward :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s)),
  (forall s : S,
     real_eq (q s)
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)) ->
  real_eq (real_elbo S real_sum_over_S real_base_loss D q Hq)
          (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos).
Proof.
  intros S real_sum_over_S sumf_ext real_base_loss D D_pos Z_align_r Z_align_r_pos         q Hq Hpoint.
  unfold real_elbo, real_evidence.
  apply (RealSetoid.real_eq_opp_compat           (real_free_energy S real_sum_over_S real_base_loss D q Hq)           (real_free_energy S real_sum_over_S real_base_loss D              (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)              (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))).
  exact (rfep_free_energy_ext_r S real_sum_over_S sumf_ext real_base_loss D q           (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)           Hq (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos)           Hpoint).
Qed.

(* ---------------------------------------------------------- *)
(* 件 4：组装件（抽象载体，prod 双函数记录——Set 层 And 形，零 Prop）     *)
(*   (紧致 ⟹ 逐点 q≡p_b) × (逐点 q≡p_b ⟹ 紧致)。                       *)
(*   即定理 4.8「当且仅当」的 Real 层可达形（显式前提形）。              *)
(* ---------------------------------------------------------- *)

Theorem t12_elbo_tight :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s)),
  real_eq (real_sum_over_S q) real_one ->
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one ->
  (real_eq (real_sum_over_S
              (fun s : S => real_kl_term (q s)
                 (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                 (Hq s)
                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
           real_zero ->
   forall s : S,
     t12_tangent_eq S real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq s) ->
  prod (real_eq (real_elbo S real_sum_over_S real_base_loss D q Hq)
                (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos)
        -> forall s : S,
             real_eq (q s)
                     (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s))
       ((forall s : S,
           real_eq (q s)
                   (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s))
        -> real_eq (real_elbo S real_sum_over_S real_base_loss D q Hq)
                   (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos)).
Proof.
  intros S real_sum_over_S sumf_ext sumf_add sumf_linear
         real_base_loss D D_pos Z_align_r Z_align_r_pos
         q Hq Hnormq Hnormb Htan0.
  split.
  - exact (t12_elbo_tight_forward S real_sum_over_S sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb Htan0).
  - exact (t12_elbo_tight_backward S real_sum_over_S sumf_ext
             real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq).
Qed.

(* ---------------------------------------------------------- *)
(* 件 5：bool 载体完成——显式接口前提整链消解的正向形                     *)
(*   显式前提位由t1_gibbe2_gibbs_equality_bool 整链消解             *)
(*   （KL≡0 ⟹ 逐点 q≡p_b 直达，注入位由 t1_log_eq_linear_inject          *)
(*   无条件供给）：bool 载体上正向半边零接口前提（除物理前提）。         *)
(* ---------------------------------------------------------- *)

Theorem t12_elbo_tight_forward_bool :
  forall (real_base_loss : bool -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : bool -> Real) (Hq : forall s : bool, real_lt real_zero (q s)),
  real_eq (real_list_sum bool q [true; false]) real_one ->
  real_eq (real_list_sum bool
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             [true; false]) real_one ->
  real_eq (real_elbo bool (fun f : bool -> Real => real_list_sum bool f [true; false])
             real_base_loss D q Hq)
          (real_evidence bool (fun f : bool -> Real => real_list_sum bool f [true; false])
             real_base_loss D D_pos Z_align_r Z_align_r_pos) ->
  forall s : bool,
    real_eq (q s)
            (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s).
Proof.
  intros real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb Htight s.
  apply (t1_gibbe2_gibbs_equality_bool q           (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)           Hq           (real_boltzmann_dist_r_pos bool real_base_loss D D_pos Z_align_r Z_align_r_pos)           Hnormq Hnormb).
  exact (t12_tight_kl_zero bool           (fun f : bool -> Real => real_list_sum bool f [true; false])           (fun (f g : bool -> Real)                (Hfg : forall s : bool, real_eq (f s) (g s)) =>              real_list_sum_ext bool f g [true; false] Hfg)           (fun f g : bool -> Real => real_list_sum_add bool f g [true; false])           (fun (a : Real) (f : bool -> Real) =>              real_list_sum_linear bool a f [true; false])           real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb Htight).
Qed.

(* ---------------------------------------------------------- *)
(* 件 6：bool 组装件（prod 双函数记录，零接口前提版）                    *)
(*   定理 4.8 在 gibbe2 样板载体上的全消解形：前提面仅剩                 *)
(*   「q 逐点正 + 双归一化」的显式物理前提。                              *)
(* ---------------------------------------------------------- *)

Theorem t12_elbo_tight_bool :
  forall (real_base_loss : bool -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : bool -> Real) (Hq : forall s : bool, real_lt real_zero (q s)),
  real_eq (real_list_sum bool q [true; false]) real_one ->
  real_eq (real_list_sum bool
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             [true; false]) real_one ->
  prod (real_eq (real_elbo bool (fun f : bool -> Real => real_list_sum bool f [true; false])
                  real_base_loss D q Hq)
                (real_evidence bool (fun f : bool -> Real => real_list_sum bool f [true; false])
                   real_base_loss D D_pos Z_align_r Z_align_r_pos)
        -> forall s : bool,
             real_eq (q s)
                     (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s))
       ((forall s : bool,
           real_eq (q s)
                   (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s))
        -> real_eq (real_elbo bool (fun f : bool -> Real => real_list_sum bool f [true; false])
                      real_base_loss D q Hq)
                   (real_evidence bool (fun f : bool -> Real => real_list_sum bool f [true; false])
                      real_base_loss D D_pos Z_align_r Z_align_r_pos)).
Proof.
  intros real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb.
  split.
  - exact (t12_elbo_tight_forward_bool real_base_loss D D_pos Z_align_r Z_align_r_pos
             q Hq Hnormq Hnormb).
  - intros Hpoint.
    exact (t12_elbo_tight_backward bool
             (fun f : bool -> Real => real_list_sum bool f [true; false])
             (fun (f g : bool -> Real)
                  (Hfg : forall s : bool, real_eq (f s) (g s)) =>
                real_list_sum_ext bool f g [true; false] Hfg)
             real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hpoint).
Qed.
