(* ============================================================ *)
(* UpAblEps49Fam.v — AB4 席：论文1 定理 4.9 诚实接口族·族面五件消融件 *)
(*                                                              *)
(* 目的：S08_RealMainlineDPO.v 节 RealRLHFMain（L2467-2731）内五个 *)
(*       开放接口槽逐件供给 Real 层构造性实例（实例供给型消融）。 *)
(*       承重主件 real_kl_decomp_full（:2527）归 AB3 席，本席零接触。 *)
(*                                                              *)
(* 五件清单（S08 行号 / 本件定理）：                              *)
(*   1. real_boltzmann_log_decomp :2501 -> e49f_boltzmann_log_decomp *)
(*      路线：witness 桥（real_log_wd 对同点异证 log 兼容，规避    *)
(*      cw_log 依赖 Hy 构造 log_seq 的 proof-relevant 陷阱）        *)
(*      + real_log_mult + log e^{-u}==−u（log_inv_exp_neg_thm）    *)
(*      + log inv==−log（自建：x·inv x==1 锚点 + log_mult +        *)
(*      real_log_one + real_eq_plus_cancel_l）+ opp_plus 换形。    *)
(*   2. real_boltzmann_normalized :2505 -> e49f_boltzmann_normalized *)
(*      路线：list 求和槽实例；ext 换序（乘法交换）+ linear_r 拉出  *)
(*      + real_eq_mult_compat（HZ 前提入位）+ real_inv_pos_correct。 *)
(*   3. real_kl_term_equiv        :2508 -> e49f_kl_term_equiv     *)
(*      路线：real_kl_term 定义展开 + real_log_mult（witness 逐字   *)
(*      同 S08 体内）+ log inv==−log + opp_plus/opp_opp/comm 代数。 *)
(*   4. real_pi_star_align        :2519 -> e49f_pi_star_align     *)
(*      路线：real_pi_star_r 槽实例取换序 softmin 形（e49f_pi_star_r）， *)
(*      对齐一步 real_mult_comm。槽为无约束自由变元，实例供给即     *)
(*      闭；变分推导（π* 为自由能极小）接口不表达，列升级方向。     *)
(*   5. real_gibbs_sum_eps        :2522 -> e49f_gibbs_sum_eps     *)
(*      路线：S08 已证 real_gibbs_inequality_eps（出节形 q 任意）   *)
(*      直连，q := Boltzmann 分布，Σq==1 由件2 实例供给；正性词项   *)
(*      全程用 S08 出节 real_boltzmann_dist_r_pos 同一词项。        *)
(*                                                              *)
(* 实例环境（逐字对齐 S08 接口实形，求和槽取具体 list 求和）：      *)
(*   S := X（任意类型）、real_sum_over_S := fun f => real_list_sum X f l、 *)
(*   real_base_loss := e、D/D_pos、Z_align_r/Z_align_r_pos 同名透传、 *)
(*   real_pi_star_r := e49f_pi_star_r。                            *)
(* 显式前提（接口无 Z 定义式，故逐位保留，TempStrict 先例）：        *)
(*   HZ : real_eq (real_list_sum X (fun s => e^{-e(s)/D}) l) Z       *)
(*         （件2、件5 依赖；件1/件3/件4 无需）。                    *)
(* 依赖（只读消费）：S01-S08 全链；不改任何既有件。                *)
(* 备注：零承认件；语句面全 Set 层；文尾逐定理 Print Assumptions。   *)
(* ============================================================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
From Stdlib Require Import Lists.List.

(* ============ 辅助件 1：log e^{−u} == −u（witness 为 Defined 正件） ============ *)
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

(* ============ 辅助件 2：log inv x == −log x（锚点法） ============ *)
(* 锚点：x·inv x == 1（real_inv_pos_correct）经 real_log_mult 收两侧   *)
(* log，得 log x + log(inv x) == log 1 == 0，加法消去收口。            *)
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

(* ============ 实例槽：real_pi_star_r 的换序 softmin 形 ============ *)
Definition e49f_pi_star_r (X : Type) (e : X -> Real) (D : Real)
           (Dpos : real_lt real_zero D) (Z : Real) (Zpos : real_lt real_zero Z)
  : X -> Real :=
  fun s => real_mult (real_exp_neg (real_mult (real_inv_pos D Dpos) (e s)))
                     (real_inv_pos Z Zpos).

(* ============ 件 1：Boltzmann 对数分解（S08:2501 逐字实例） ============ *)
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
  - (* witness 桥 + log_mult + log exp_neg / log inv 两桥 *)
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

(* ============ 件 2：Boltzmann 归一化（S08:2505 实例，HZ 前提显式保留） ============ *)
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
  - (* Σ (invZ·exp) == invZ · Σ exp：ext 换序 + linear_r 拉出 *)
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

(* ============ 件 3：KL 项等价（S08:2508 逐字实例） ============ *)
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
  (* 目标内层 A + (−B) == −(log(B·inv p))：L0 换符号 + L123 代数链 *)
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

(* ============ 件 4：π* 对齐（S08:2519 实例，槽取 e49f_pi_star_r） ============ *)
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

(* ============ 件 5：Σ 版 KL ≥ 0 + eps（S08:2522 实例，直连已证引擎） ============ *)
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

(* ============ 审计口：逐定理 Print Assumptions ============ *)
Print Assumptions e49f_log_exp_neg.
Print Assumptions e49f_log_inv_pos.
Print Assumptions e49f_boltzmann_log_decomp.
Print Assumptions e49f_boltzmann_normalized.
Print Assumptions e49f_kl_term_equiv.
Print Assumptions e49f_pi_star_align.
Print Assumptions e49f_gibbs_sum_eps.
