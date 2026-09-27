(* ==========================================================================)
   UpAblEps49Body.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：e49f_log_exp_neg、e49f_log_inv_pos、e49f_pi_star_r、e49f_boltzmann_log_decomp、e49f_boltzmann_normalized、e49f_kl_term_equiv、e49f_pi_star_align、e49f_gibbs_sum_eps、e49b_part_Z。
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
Require Import UpAblEps49List.
From Stdlib Require Import Extraction.

(* ================= §1 e49f_log_exp_neg 族 ================= *)
From Stdlib Require Import Lists.List.

(* ============ 辅助引理 1：log e^{−u} == −u（对数证明项为 Defined 构造） ============ *)
Lemma e49f_log_exp_neg : forall u : Real,
  real_eq (real_log (real_exp_neg u) (real_exp_neg_pos u)) (real_opp u).
Proof.
  intros u.
  apply (real_eq_trans (real_log (real_exp_neg u) (real_exp_neg_pos u))
                       (real_log (cauchy_real_exp (real_opp u))
                                 (cauchy_real_exp_pos (real_opp u)))
                       (real_opp u)).
  - exact (real_log_wd (real_exp_neg u) (cauchy_real_exp (real_opp u))
             (real_exp_neg_pos u) (cauchy_real_exp_pos (real_opp u))
             (real_eq_refl (real_exp_neg u))).
  - unfold real_log.
    exact (log_inv_exp_neg_thm (real_opp u) (cauchy_real_exp_pos (real_opp u))).
Qed.

(* ============ 辅助引理 2：log inv x == −log x（锚点法） ============     *)
(* 锚点：x·inv x == 1（real_inv_pos_correct）经 real_log_mult 收两侧      *)
(* log，得 log x + log(inv x) == log 1 == 0，加法消去收尾。                *)
Lemma e49f_log_inv_pos : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
          (real_opp (real_log x Hx)).
Proof.
  intros x Hx.
  set (A := real_log x Hx).
  set (B := real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)).
  assert (Hlogm : real_eq
            (real_log (real_mult x (real_inv_pos x Hx))
                      (real_mult_positive x (real_inv_pos x Hx) Hx
                        (real_inv_pos_pos x Hx)))
            real_zero).
  { apply (real_eq_trans
             (real_log (real_mult x (real_inv_pos x Hx))
                       (real_mult_positive x (real_inv_pos x Hx) Hx
                         (real_inv_pos_pos x Hx)))
             (real_log real_one real_lt_zero_one) real_zero).
    - exact (real_log_wd (real_mult x (real_inv_pos x Hx)) real_one
               (real_mult_positive x (real_inv_pos x Hx) Hx
                 (real_inv_pos_pos x Hx))
               real_lt_zero_one (real_inv_pos_correct x Hx)).
    - exact (real_log_one real_lt_zero_one). }
  assert (Hsum : real_eq (real_plus A B) real_zero).
  { apply (real_eq_trans (real_plus A B)
             (real_log (real_mult x (real_inv_pos x Hx))
                       (real_mult_positive x (real_inv_pos x Hx) Hx
                         (real_inv_pos_pos x Hx)))
             real_zero).
    - apply (real_eq_sym
               (real_log (real_mult x (real_inv_pos x Hx))
                         (real_mult_positive x (real_inv_pos x Hx) Hx
                           (real_inv_pos_pos x Hx)))
               (real_plus A B)).
      exact (real_log_mult x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx)).
    - exact Hlogm. }
  apply (real_eq_plus_cancel_l A B (real_opp A)).
  apply (real_eq_trans (real_plus A B) real_zero (real_plus A (real_opp A))).
  - exact Hsum.
  - apply (real_eq_sym (real_plus A (real_opp A)) real_zero).
    apply (real_plus_opp A).
Qed.

(* ============ 实例定义：real_pi_star_r 的换序 softmin 形 ============   *)
Definition e49f_pi_star_r (X : Type) (e : X -> Real) (D : Real)
           (Dpos : real_lt real_zero D) (Z : Real) (Zpos : real_lt real_zero Z)
  : X -> Real :=
  fun s => real_mult (real_exp_neg (real_mult (real_inv_pos D Dpos) (e s)))
                     (real_inv_pos Z Zpos).

(* ============ 件 1：Boltzmann 对数分解（real_boltzmann_log_decomp 逐字实例） ============ *)
Theorem e49f_boltzmann_log_decomp :
  forall (X : Type) (e : X -> Real) (D : Real) (Dpos : real_lt real_zero D)
         (Z : Real) (Zpos : real_lt real_zero Z)
         (s : X)
         (Hpb : real_lt real_zero (real_boltzmann_dist_r X e D Dpos Z Zpos s)),
    real_eq (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s) Hpb)
            (real_opp (real_plus (real_mult (real_inv_pos D Dpos) (e s))
                                 (real_log Z Zpos))).
Proof.
  intros X e D Dpos Z Zpos s Hpb.
  set (Hinv := real_inv_pos_pos Z Zpos).
  set (Hexp := real_exp_neg_pos (real_mult (real_inv_pos D Dpos) (e s))).
  apply (real_eq_trans
           (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s) Hpb)
           (real_plus (real_log (real_inv_pos Z Zpos) Hinv)
                      (real_log (real_exp_neg (real_mult (real_inv_pos D Dpos) (e s))) Hexp))
           (real_opp (real_plus (real_mult (real_inv_pos D Dpos) (e s))
                                (real_log Z Zpos)))).
  - (* witness 桥 + real_log_mult + log exp_neg / log inv             *)
    apply (real_eq_trans
             (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s) Hpb)
             (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                       (real_mult_positive (real_inv_pos Z Zpos)
                          (real_exp_neg (real_mult (real_inv_pos D Dpos) (e s)))
                          Hinv Hexp))
             (real_plus (real_log (real_inv_pos Z Zpos) Hinv)
                        (real_log (real_exp_neg (real_mult (real_inv_pos D Dpos) (e s))) Hexp))).
    + exact (real_log_wd (real_boltzmann_dist_r X e D Dpos Z Zpos s)
               (real_boltzmann_dist_r X e D Dpos Z Zpos s) Hpb
               (real_mult_positive (real_inv_pos Z Zpos)
                  (real_exp_neg (real_mult (real_inv_pos D Dpos) (e s)))
                  Hinv Hexp)
               (real_eq_refl (real_boltzmann_dist_r X e D Dpos Z Zpos s))).
    + exact (real_log_mult (real_inv_pos Z Zpos)
               (real_exp_neg (real_mult (real_inv_pos D Dpos) (e s)))
               Hinv Hexp).
  - (* (−log Z) + (−u) == −(u + log Z) *)
    apply (real_eq_trans
             (real_plus (real_log (real_inv_pos Z Zpos) Hinv)
                        (real_log (real_exp_neg (real_mult (real_inv_pos D Dpos) (e s))) Hexp))
             (real_plus (real_opp (real_log Z Zpos))
                        (real_opp (real_mult (real_inv_pos D Dpos) (e s))))
             (real_opp (real_plus (real_mult (real_inv_pos D Dpos) (e s))
                                  (real_log Z Zpos)))).
    + exact (RealSetoid.real_eq_plus_compat
               (real_log (real_inv_pos Z Zpos) Hinv)
               (real_log (real_exp_neg (real_mult (real_inv_pos D Dpos) (e s))) Hexp)
               (real_opp (real_log Z Zpos))
               (real_opp (real_mult (real_inv_pos D Dpos) (e s)))
               (e49f_log_inv_pos Z Zpos)
               (e49f_log_exp_neg (real_mult (real_inv_pos D Dpos) (e s)))).
    + apply (real_eq_trans
               (real_plus (real_opp (real_log Z Zpos))
                          (real_opp (real_mult (real_inv_pos D Dpos) (e s))))
               (real_opp (real_plus (real_log Z Zpos)
                                    (real_mult (real_inv_pos D Dpos) (e s))))
               (real_opp (real_plus (real_mult (real_inv_pos D Dpos) (e s))
                                    (real_log Z Zpos)))).
      * apply (real_eq_sym
                 (real_opp (real_plus (real_log Z Zpos)
                                      (real_mult (real_inv_pos D Dpos) (e s))))
                 (real_plus (real_opp (real_log Z Zpos))
                            (real_opp (real_mult (real_inv_pos D Dpos) (e s))))).
        apply (real_opp_plus (real_log Z Zpos)
                             (real_mult (real_inv_pos D Dpos) (e s))).
      * apply (RealSetoid.real_eq_opp_compat
                 (real_plus (real_log Z Zpos)
                            (real_mult (real_inv_pos D Dpos) (e s)))
                 (real_plus (real_mult (real_inv_pos D Dpos) (e s))
                            (real_log Z Zpos))).
        apply (real_plus_comm (real_log Z Zpos)
                              (real_mult (real_inv_pos D Dpos) (e s))).
Qed.

(* ============ 件 2：Boltzmann 归一化（real_boltzmann_normalized 实例，HZ 前提显式保留） ============ *)
Theorem e49f_boltzmann_normalized :
  forall (X : Type) (l : list X) (e : X -> Real) (D : Real)
         (Dpos : real_lt real_zero D) (Z : Real) (Zpos : real_lt real_zero Z)
         (HZ : real_eq (real_list_sum X
                 (fun s => real_exp_neg (real_mult (real_inv_pos D Dpos) (e s))) l) Z),
    real_eq (real_list_sum X (real_boltzmann_dist_r X e D Dpos Z Zpos) l)
            real_one.
Proof.
  intros X l e D Dpos Z Zpos HZ.
  apply (real_eq_trans
           (real_list_sum X (real_boltzmann_dist_r X e D Dpos Z Zpos) l)
           (real_mult (real_inv_pos Z Zpos)
                      (real_list_sum X
                         (fun s => real_exp_neg
                                    (real_mult (real_inv_pos D Dpos) (e s))) l))
           real_one).
  - (* Σ (invZ·exp) == invZ · Σ exp：real_list_sum_ext 换序 + real_list_sum_linear_r 提出公因子 *)
    apply (real_eq_trans
             (real_list_sum X (real_boltzmann_dist_r X e D Dpos Z Zpos) l)
             (real_list_sum X
                (fun w => real_mult (real_exp_neg
                          (real_mult (real_inv_pos D Dpos) (e w)))
                       (real_inv_pos Z Zpos)) l)
             (real_mult (real_inv_pos Z Zpos)
                        (real_list_sum X
                           (fun s => real_exp_neg
                                      (real_mult (real_inv_pos D Dpos) (e s))) l))).
    + exact (real_list_sum_ext X
               (fun s => real_mult (real_inv_pos Z Zpos)
                         (real_exp_neg (real_mult (real_inv_pos D Dpos) (e s))))
               (fun w => real_mult (real_exp_neg
                         (real_mult (real_inv_pos D Dpos) (e w)))
                    (real_inv_pos Z Zpos)) l
               (fun s => real_mult_comm (real_inv_pos Z Zpos)
                           (real_exp_neg (real_mult (real_inv_pos D Dpos) (e s))))).
    + exact (real_list_sum_linear_r X (real_inv_pos Z Zpos)
               (fun w => real_exp_neg (real_mult (real_inv_pos D Dpos) (e w))) l).
  - (* invZ · Σexp == invZ · Z == Z·invZ == 1 *)
    apply (real_eq_trans
             (real_mult (real_inv_pos Z Zpos)
                        (real_list_sum X
                           (fun s => real_exp_neg
                                      (real_mult (real_inv_pos D Dpos) (e s))) l))
             (real_mult (real_inv_pos Z Zpos) Z)
             real_one).
    + exact (RealSetoid.real_eq_mult_compat
               (real_inv_pos Z Zpos)
               (real_list_sum X
                  (fun s => real_exp_neg
                             (real_mult (real_inv_pos D Dpos) (e s))) l)
               (real_inv_pos Z Zpos) Z
               (real_eq_refl (real_inv_pos Z Zpos)) HZ).
    + apply (real_eq_trans (real_mult (real_inv_pos Z Zpos) Z)
               (real_mult Z (real_inv_pos Z Zpos)) real_one).
      * exact (real_mult_comm (real_inv_pos Z Zpos) Z).
      * exact (real_inv_pos_correct Z Zpos).
Qed.

(* ============ 件 3：KL 项等价（real_kl_term_equiv 逐字实例） ============ *)
Theorem e49f_kl_term_equiv :
  forall (X : Type) (e : X -> Real) (D : Real) (Dpos : real_lt real_zero D)
         (Z : Real) (Zpos : real_lt real_zero Z)
         (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)) (s : X),
    real_eq (real_mult (p s)
               (real_plus (real_log (p s) (Hp s))
                          (real_opp (real_log
                             (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                             (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)))))
            (real_kl_sum_term X e D Dpos Z Zpos p Hp s).
Proof.
  intros X e D Dpos Z Zpos p Hp s.
  unfold real_kl_sum_term, real_kl_term.
  apply (RealSetoid.real_eq_mult_compat (p s)
           (real_plus (real_log (p s) (Hp s))
                      (real_opp (real_log
                         (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                         (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))))
           (p s)
           (real_opp (real_log
                       (real_mult (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                                  (real_inv_pos (p s) (Hp s)))
                       (real_mult_positive
                          (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                          (real_inv_pos (p s) (Hp s))
                          (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)
                          (real_inv_pos_pos (p s) (Hp s)))))
           (real_eq_refl (p s))).
  (* 内层：log p + −log B == −log(B·inv p) *)
  assert (Hsub4 : real_eq
            (real_log (real_mult (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                        (real_inv_pos (p s) (Hp s)))
                      (real_mult_positive
                         (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                         (real_inv_pos (p s) (Hp s))
                         (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)
                         (real_inv_pos_pos (p s) (Hp s))))
            (real_plus (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                           (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))
                       (real_opp (real_log (p s) (Hp s))))).
  { apply (real_eq_trans
             (real_log (real_mult (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                    (real_inv_pos (p s) (Hp s)))
              (real_mult_positive (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                 (real_inv_pos (p s) (Hp s))
                 (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)
                 (real_inv_pos_pos (p s) (Hp s))))
             (real_plus (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                            (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))
                        (real_log (real_inv_pos (p s) (Hp s))
                                  (real_inv_pos_pos (p s) (Hp s))))
             (real_plus (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                            (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))
                        (real_opp (real_log (p s) (Hp s))))).
    - exact (real_log_mult (real_boltzmann_dist_r X e D Dpos Z Zpos s)
               (real_inv_pos (p s) (Hp s))
               (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)
               (real_inv_pos_pos (p s) (Hp s))).
    - exact (RealSetoid.real_eq_plus_compat
               (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                  (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))
               (real_log (real_inv_pos (p s) (Hp s))
                  (real_inv_pos_pos (p s) (Hp s)))
               (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                  (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))
               (real_opp (real_log (p s) (Hp s)))
               (real_eq_refl (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                            (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)))
               (e49f_log_inv_pos (p s) (Hp s))). }
  (* 目标内层 A + (−B) == −(log(B·inv p))：Hsub4 换符号 + HL123 代数链        *)
  assert (HL123 : real_eq
            (real_opp (real_plus (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                            (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))
                       (real_opp (real_log (p s) (Hp s)))))
            (real_plus (real_log (p s) (Hp s))
                       (real_opp (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                                (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))))).
  { apply (real_eq_trans
             (real_opp (real_plus (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                            (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))
                       (real_opp (real_log (p s) (Hp s)))))
             (real_plus (real_opp (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                              (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)))
                        (real_opp (real_opp (real_log (p s) (Hp s)))))
             (real_plus (real_log (p s) (Hp s))
                        (real_opp (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                                 (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))))).
    - exact (real_opp_plus (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                             (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))
                           (real_opp (real_log (p s) (Hp s)))).
    - apply (real_eq_trans
               (real_plus (real_opp (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                                (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)))
                          (real_opp (real_opp (real_log (p s) (Hp s)))))
               (real_plus (real_opp (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                                (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)))
                          (real_log (p s) (Hp s)))
               (real_plus (real_log (p s) (Hp s))
                          (real_opp (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                                   (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))))).
      + exact (RealSetoid.real_eq_plus_compat
                 (real_opp (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                              (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)))
                 (real_opp (real_opp (real_log (p s) (Hp s))))
                 (real_opp (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                              (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)))
                 (real_log (p s) (Hp s))
                 (real_eq_refl (real_opp (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                                    (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))))
                 (real_opp_opp (real_log (p s) (Hp s)))).
      + exact (real_plus_comm (real_opp (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                                    (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)))
                              (real_log (p s) (Hp s))). }
  apply (real_eq_sym
           (real_opp (real_log (real_mult (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                        (real_inv_pos (p s) (Hp s)))
                     (real_mult_positive (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                        (real_inv_pos (p s) (Hp s))
                        (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)
                        (real_inv_pos_pos (p s) (Hp s)))))
           (real_plus (real_log (p s) (Hp s))
                      (real_opp (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                                (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))))).
  apply (real_eq_trans
           (real_opp (real_log (real_mult (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                        (real_inv_pos (p s) (Hp s)))
                     (real_mult_positive (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                        (real_inv_pos (p s) (Hp s))
                        (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)
                        (real_inv_pos_pos (p s) (Hp s)))))
           (real_opp (real_plus (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                          (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))
                     (real_opp (real_log (p s) (Hp s)))))
           (real_plus (real_log (p s) (Hp s))
                      (real_opp (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                                (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))))).
  - exact (RealSetoid.real_eq_opp_compat
             (real_log (real_mult (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                        (real_inv_pos (p s) (Hp s)))
                   (real_mult_positive (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                      (real_inv_pos (p s) (Hp s))
                      (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s)
                      (real_inv_pos_pos (p s) (Hp s))))
             (real_plus (real_log (real_boltzmann_dist_r X e D Dpos Z Zpos s)
                        (real_boltzmann_dist_r_pos X e D Dpos Z Zpos s))
                   (real_opp (real_log (p s) (Hp s))))
             Hsub4).
  - exact HL123.
Qed.

(* ============ 件 4：π* 对齐（real_pi_star_align 实例，取 e49f_pi_star_r） ============ *)
Theorem e49f_pi_star_align :
  forall (X : Type) (e : X -> Real) (D : Real) (Dpos : real_lt real_zero D)
         (Z : Real) (Zpos : real_lt real_zero Z) (s : X),
    real_eq (e49f_pi_star_r X e D Dpos Z Zpos s)
            (real_boltzmann_dist_r X e D Dpos Z Zpos s).
Proof.
  intros X e D Dpos Z Zpos s.
  unfold e49f_pi_star_r, real_boltzmann_dist_r.
  apply real_mult_comm.
Qed.

(* ============ 件 5：Σ 版 KL ≥ 0 + eps（real_gibbs_sum_eps 实例，直连已证引理） ============ *)
Theorem e49f_gibbs_sum_eps :
  forall (X : Type) (l : list X) (e : X -> Real) (D : Real)
         (Dpos : real_lt real_zero D) (Z : Real) (Zpos : real_lt real_zero Z)
         (HZ : real_eq (real_list_sum X
                 (fun s => real_exp_neg (real_mult (real_inv_pos D Dpos) (e s))) l) Z)
         (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
         (Hnormp : real_eq (real_list_sum X p l) real_one) (eps : Real),
    real_lt real_zero eps ->
    real_le real_zero
      (real_plus (real_list_sum X
                    (fun s => real_kl_sum_term X e D Dpos Z Zpos p Hp s) l)
                 eps).
Proof.
  intros X l e D Dpos Z Zpos HZ p Hp Hnormp eps Heps.
  unfold real_kl_sum_term.
  exact (real_gibbs_inequality_eps X l p
           (real_boltzmann_dist_r X e D Dpos Z Zpos)
           Hp (real_boltzmann_dist_r_pos X e D Dpos Z Zpos)
           Hnormp (e49f_boltzmann_normalized X l e D Dpos Z Zpos HZ)
           eps Heps).
Qed.

(* ============ 依赖审计：逐定理 Print Assumptions ============          *)
Print Assumptions e49f_log_exp_neg.
Print Assumptions e49f_log_inv_pos.
Print Assumptions e49f_boltzmann_log_decomp.
Print Assumptions e49f_boltzmann_normalized.
Print Assumptions e49f_kl_term_equiv.
Print Assumptions e49f_pi_star_align.
Print Assumptions e49f_gibbs_sum_eps.
(* ================= §2 e49b_part_Z 族 ================= *)
From Stdlib Require Import Lists.List.

(* 配分定义形 Z 与其正性证明项（逐 p 内导非空）                                     *)
Definition e49b_part_Z (X : Set) (l : list X) (e : X -> Real) (D : Real)
           (D_pos : real_lt real_zero D) : Real :=
  real_list_sum X (fun s : X => real_exp_neg
                     (real_mult (real_inv_pos D D_pos) (e s))) l.

Definition e49b_part_pos (X : Set) (l : list X) (e : X -> Real) (D : Real)
           (D_pos : real_lt real_zero D)
           (p : X -> Real) (Hnormp : real_eq (real_list_sum X p l) real_one) :
  real_lt real_zero (e49b_part_Z X l e D D_pos) :=
  e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp) e D D_pos.

(* 载体上的 Boltzmann 分布词项（证明项一致内联形）                                 *)
Definition e49b_boltz (X : Set) (l : list X) (e : X -> Real) (D : Real)
           (D_pos : real_lt real_zero D)
           (p : X -> Real) (Hnormp : real_eq (real_list_sum X p l) real_one)
           (s : X) : Real :=
  real_boltzmann_dist_r X e D D_pos
           (e49b_part_Z X l e D D_pos)
           (e49b_part_pos X l e D D_pos p Hnormp) s.

Definition e49b_boltz_pos (X : Set) (l : list X) (e : X -> Real) (D : Real)
           (D_pos : real_lt real_zero D)
           (p : X -> Real) (Hnormp : real_eq (real_list_sum X p l) real_one)
           (s : X) : real_lt real_zero (e49b_boltz X l e D D_pos p Hnormp s) :=
  real_boltzmann_dist_r_pos X e D D_pos
           (e49b_part_Z X l e D D_pos)
           (e49b_part_pos X l e D D_pos p Hnormp) s.

(* 主件：4.9 本体 list 载体无附加接口假设版                                     *)
(* 语句面与 S08 的 real_rlhf_optimal_eps 逐字同构（载体替换表内联）；前提面＝原形：        *)
(* X l e D D_pos pi Hpi Hnormpi eps，非空性由 Hnormpi 内导、配分 Z 取       *)
(* 定义形、正性证明项逐 p 内联（e49b_part_pos）。两处假设位全部替换为已证实例。                *)
Theorem e49b_real_rlhf_optimal_eps_list :
  forall (X : Set) (l : list X) (e : X -> Real) (D : Real)
         (D_pos : real_lt real_zero D)
    (pi : X -> Real) (Hpi : forall s : X, real_lt real_zero (pi s))
    (Hnormpi : real_eq (e49l_sumf X l pi) real_one) (eps : Real),
    real_lt real_zero eps ->
    real_le (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
            (real_plus
               (real_opp (real_free_energy X (e49l_sumf X l) e D
                            (e49b_boltz X l e D D_pos pi Hnormpi)
                            (e49b_boltz_pos X l e D D_pos pi Hnormpi)))
               (real_mult D eps)).
Proof.
  intros X l e D D_pos pi Hpi Hnormpi eps Hepspos.
  set (B := e49b_boltz X l e D D_pos pi Hnormpi).
  set (Bpos := e49b_boltz_pos X l e D D_pos pi Hnormpi).
  set (klsum := (e49l_sumf X l)
                  (fun s : X => real_kl_term (pi s) (B s) (Hpi s) (Bpos s))).
  (* 1. 替换 S08 使用处一：real_kl_decomp_full 假设 → e49l 主件               *)
  (* （F(π) == F(p_b) + D·Σkl，假设形完全实例）。                             *)
  assert (Hkl : real_eq (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                        (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                   (real_mult D klsum)))
    by exact (e49l_real_kl_decomp_full_list X l e D D_pos pi Hpi Hnormpi).
  (* 2. 替换 S08 使用处二：real_gibbs_sum_eps 假设 → e49f 件 5               *)
  (*    （0 ≤ Σkl + eps；HZ 自反：Z 取配分定义形）。                    *)
  assert (Hg : real_le real_zero (real_plus klsum eps))
    by exact (e49f_gibbs_sum_eps X l e D D_pos
               (e49b_part_Z X l e D D_pos)
               (e49b_part_pos X l e D D_pos pi Hnormpi)
               (real_eq_refl (e49b_part_Z X l e D D_pos))
               pi Hpi Hnormpi eps Hepspos).
  (* 3. 0 ≤ D·Σkl + D·eps（D 正乘 + real_distrib）——S08 同款             *)
  assert (Hd : real_le real_zero (real_plus (real_mult D klsum)
                                             (real_mult D eps))).
  {
    apply (real_le_trans real_zero
                         (real_mult D (real_plus klsum eps))
                         (real_plus (real_mult D klsum) (real_mult D eps))).
    - apply (real_le_trans _ (real_mult D real_zero) _).
      + apply (RealSetoid.real_eq_le real_zero (real_mult D real_zero)).
        apply (real_eq_sym _ _ (real_mult_zero D)).
      + apply (RealSetoid.real_le_id_l (real_mult D real_zero) (real_mult real_zero D)
                                       (real_mult D (real_plus klsum eps))).
        * apply (real_mult_comm D real_zero).
        * apply (RealSetoid.real_le_id_r (real_mult real_zero D)
                                         (real_mult (real_plus klsum eps) D)
                                         (real_mult D (real_plus klsum eps))).
          -- apply (real_mult_comm (real_plus klsum eps) D).
          -- apply (real_le_mult_compat real_zero (real_plus klsum eps) D D_pos Hg).
    - apply (RealSetoid.real_eq_le (real_mult D (real_plus klsum eps))
                                   (real_plus (real_mult D klsum) (real_mult D eps))).
      apply (real_distrib D klsum eps).
  }
  (* 4. F(p_b) ≤ F(π) + D·eps（real_le_plus_compat + Hkl 反向）——S08 同款 *)
  assert (Hf : real_le (real_free_energy X (e49l_sumf X l) e D B Bpos)
                       (real_plus (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                                  (real_mult D eps))).
  {
    apply (real_le_trans _ (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                      (real_plus (real_mult D klsum)
                                                 (real_mult D eps))) _).
    - (* F(p_b) == F(p_b) + 0 ≤ F(p_b) + (D·Σkl + D·eps) *)
      apply (real_le_trans _ (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                        real_zero) _).
      + apply (RealSetoid.real_eq_le (real_free_energy X (e49l_sumf X l) e D B Bpos)
                          (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos) real_zero)).
        apply (real_eq_sym _ _ (real_plus_zero (real_free_energy X (e49l_sumf X l) e D B Bpos))).
      + apply (real_le_plus_compat (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                   (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                   real_zero
                                   (real_plus (real_mult D klsum) (real_mult D eps))
                                   (real_le_refl (real_free_energy X (e49l_sumf X l) e D B Bpos))
                                   Hd).
    - (* F(p_b) + (D·Σkl + D·eps) == F(π) + D·eps（结合 + Hkl 反向） *)
      apply (RealSetoid.real_eq_le (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                   (real_plus (real_mult D klsum) (real_mult D eps)))
                        (real_plus (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                                   (real_mult D eps))).
      apply (real_eq_trans _ (real_plus (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                                   (real_mult D klsum))
                                        (real_mult D eps)) _).
      + apply (real_plus_assoc (real_free_energy X (e49l_sumf X l) e D B Bpos)
                               (real_mult D klsum)
                               (real_mult D eps)).
      + apply (RealSetoid.real_eq_plus_compat (real_plus (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                                         (real_mult D klsum))
                                              (real_mult D eps)
                                              (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                                              (real_mult D eps)
                                              (real_eq_sym _ _ Hkl) (real_eq_refl _)).
  }
  (* 5. 取负：J(π) ≤ J(p_b) + D·eps——S08 同款环恒等链                       *)
  assert (Hopp' : real_le (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                     (real_opp (real_mult D eps)))
                          (real_opp (real_free_energy X (e49l_sumf X l) e D B Bpos))).
  {
    apply (RealSetoid.real_le_id_l (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                              (real_opp (real_mult D eps)))
                                   (real_opp (real_plus (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                                                        (real_mult D eps)))
                                   (real_opp (real_free_energy X (e49l_sumf X l) e D B Bpos))).
    - apply (real_eq_sym _ _ (real_opp_plus (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                                            (real_mult D eps))).
    - apply (real_opp_le_compat (real_free_energy X (e49l_sumf X l) e D B Bpos)
                                (real_plus (real_free_energy X (e49l_sumf X l) e D pi Hpi)
                                           (real_mult D eps))
                                Hf).
  }
  apply (real_le_trans (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                       (real_plus (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                             (real_opp (real_mult D eps)))
                                  (real_mult D eps))
                       (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D B Bpos))
                                  (real_mult D eps))).
  - (* A == (A + opp C) + C：环恒等（real_plus_assoc 反向 + real_plus_comm 内层 + real_plus_opp + real_plus_zero） *)
    assert (Hring : real_eq (real_plus (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                                  (real_opp (real_mult D eps)))
                                       (real_mult D eps))
                            (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))).
    {
      apply (real_eq_trans _ (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                        (real_plus (real_opp (real_mult D eps))
                                                   (real_mult D eps))) _).
      - apply (real_eq_sym _ _ (real_plus_assoc (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                                (real_opp (real_mult D eps))
                                                (real_mult D eps))).
      - apply (real_eq_trans _ (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                          (real_plus (real_mult D eps)
                                                     (real_opp (real_mult D eps)))) _).
        + apply (RealSetoid.real_eq_plus_compat (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                                (real_plus (real_opp (real_mult D eps))
                                                           (real_mult D eps))
                                                (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                                (real_plus (real_mult D eps)
                                                           (real_opp (real_mult D eps)))
                                                (real_eq_refl _)
                                                (real_plus_comm (real_opp (real_mult D eps))
                                                                (real_mult D eps))).
        + apply (real_eq_trans _ (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                            real_zero) _).
          * apply (RealSetoid.real_eq_plus_compat (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                                  (real_plus (real_mult D eps)
                                                             (real_opp (real_mult D eps)))
                                                  (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                                  real_zero
                                                  (real_eq_refl _)
                                                  (real_plus_opp (real_mult D eps))).
          * apply (real_plus_zero (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))).
    }
    apply (RealSetoid.real_eq_le (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                 (real_plus (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                                       (real_opp (real_mult D eps)))
                                            (real_mult D eps))).
    apply (real_eq_sym _ _ Hring).
  - (* (A + opp C) + C ≤ B + C：real_le_plus_compat（Hopp' + real_le_refl） *)
    apply (real_le_plus_compat (real_plus (real_opp (real_free_energy X (e49l_sumf X l) e D pi Hpi))
                                          (real_opp (real_mult D eps)))
                               (real_opp (real_free_energy X (e49l_sumf X l) e D B Bpos))
                               (real_mult D eps) (real_mult D eps)
                               Hopp' (real_le_refl (real_mult D eps))).
Qed.

(* 依赖审计：零外部未证假设；独立目录提取                                           *)
Print Assumptions e49b_part_Z.
Print Assumptions e49b_part_pos.
Print Assumptions e49b_boltz.
Print Assumptions e49b_boltz_pos.
Print Assumptions e49b_real_rlhf_optimal_eps_list.

Set Extraction Output Directory "../_x1_body_extract".
(* 单条命令合并提取（多条 Separate Extraction 仅存末条闭包）                       *)
Separate Extraction e49b_part_Z e49b_part_pos e49b_boltz e49b_boltz_pos
  e49b_real_rlhf_optimal_eps_list.
