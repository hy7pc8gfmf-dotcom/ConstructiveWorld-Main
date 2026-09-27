(* ==========================================================================)
   UpStepKL —— step_kl_eta_bound 的 Real 层消解；同域语句面
   使命：本件形式化step_kl_eta_bound 的 Real 层消解。
   本件并载：step_kl 消解的 M3 迭代版 Real 层副本。
   依赖：List, QArith.Qring, S01_BaseRing, S02_CauchyComplete, S03_QExp, S04_RealExpLogConv, S05_AlignmentGRPO, S06_DiffSamplingGibbs
     S07_RealSetoidExpLog, S08_RealMainlineDPO, S09_EntropyReal, S10_KVQuantTrig, S11_TP3B5, S12_B5RecycleSF, S13_NLiveAudit, S14_B5BatchBlock,
     S15_TailFEPUp。
   构造性：零公理、零承认式语句；语句面 Set 层承载，Print Assumptions 全 Closed。
   编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring.
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
Import RealInterfaceEnhancedMod.

(* ========== 桥：lt/eq → le，le 双侧 eq 换形 ========== *)

Lemma kl_lt_le_bridge : forall a b : Real, real_lt a b -> real_le a b.
Proof. intros a b H. unfold real_le. exact (inl H). Qed.

Lemma kl_eq_le_bridge : forall a b : Real, real_eq a b -> real_le a b.
Proof. intros a b H. unfold real_le. exact (inr H). Qed.

Lemma kl_le_eq_r : forall a b c : Real,
  real_le a b -> real_eq b c -> real_le a c.
Proof. intros a b c Hab Hbc. unfold real_le in Hab |- *.
  destruct Hab as [Hlt | Heq].
  - exact (inl (RealSetoid.real_lt_compat a a b c (real_eq_refl a) Hbc Hlt)).
  - exact (inr (real_eq_trans a b c Heq Hbc)). Qed.

Lemma kl_le_eq_l : forall a b c : Real,
  real_le a b -> real_eq a c -> real_le c b.
Proof.
  intros a b c Hab Hac.
  exact (real_le_trans c a b (inr (real_eq_sym a c Hac)) Hab).
  Qed.

(* ========== 环恒等式族（real_eq_of_zero_diff 逐点 ring） ========== *)

Lemma kl_zero_plus_zero : real_eq (real_plus real_zero real_zero) real_zero.
Proof. apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

Lemma kl_plus_zero_l : forall x : Real, real_eq (real_plus real_zero x) x.
Proof. intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. simpl. ring. Qed.

Lemma kl_mult_zero_l : forall x : Real, real_eq (real_mult real_zero x) real_zero.
Proof. intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. simpl. ring. Qed.

Lemma kl_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof. intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. simpl. ring. Qed.

Lemma kl_distrib_r : forall x y z : Real,
  real_eq (real_mult (real_plus x y) z) (real_plus (real_mult x z) (real_mult y z)).
Proof. intros x y z. destruct x as [u Hu]. destruct y as [v Hv]. destruct z as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

(* (1−η) + η == 1 *)
Lemma kl_ring_m_plus_eta : forall eta : Real,
  real_eq (real_plus (real_plus real_one (real_opp eta)) eta) real_one.
Proof. intros eta. destruct eta as [v Hv]. apply real_eq_of_zero_diff.
  intro n. simpl. ring. Qed.

(* Varberg 锥主恒等式：E·m̂·(1+ηs) + E·η·(1+m̂·(−s)) == E，m̂ := 1−η 展开 *)
Lemma kl_ring_core : forall (E eta s : Real),
  real_eq (real_plus
    (real_mult (real_mult E (real_plus real_one (real_opp eta)))
               (real_plus real_one (real_mult eta s)))
    (real_mult (real_mult E eta)
               (real_plus real_one
                 (real_mult (real_plus real_one (real_opp eta)) (real_opp s)))))
    E.
Proof. intros E eta s. destruct E as [u Hu]. destruct eta as [v Hv]. destruct s as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

(* z + η·s == x，其中 z := (1−η)x + ηy、s := x−y *)
Lemma kl_z_tA : forall x y eta : Real,
  real_eq (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                (real_mult eta y))
                     (real_mult eta (real_plus x (real_opp y)))) x.
Proof. intros x y eta. destruct x as [u Hu]. destruct y as [v Hv]. destruct eta as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

(* z + (1−η)·(−s) == y *)
Lemma kl_z_tB : forall x y eta : Real,
  real_eq (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                (real_mult eta y))
                     (real_mult (real_plus real_one (real_opp eta))
                                (real_opp (real_plus x (real_opp y))))) y.
Proof. intros x y eta. destruct x as [u Hu]. destruct y as [v Hv]. destruct eta as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

Lemma kl_sum_prod_r : forall a b w : Real,
  real_eq (real_plus (real_mult a w) (real_mult b w)) (real_mult (real_plus a b) w).
Proof. intros a b w. destruct a as [u Hu]. destruct b as [v Hv]. destruct w as [w' Hw'].
  apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

Lemma kl_swap3 : forall c e w : Real,
  real_eq (real_mult c (real_mult e w)) (real_mult e (real_mult c w)).
Proof. intros c e w. destruct c as [u Hu]. destruct e as [v Hv]. destruct w as [w' Hw'].
  apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

Lemma kl_assoc_swap : forall E m w : Real,
  real_eq (real_mult (real_mult E m) w) (real_mult m (real_mult E w)).
Proof. intros E m w. destruct E as [u Hu]. destruct m as [v Hv]. destruct w as [w' Hw'].
  apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

(* ========== 序辅助 ========== *)

(* η ≤ 1 ⟹ 0 ≤ 1−η（Or 编码逐支） *)
Lemma kl_one_minus_eta_nonneg : forall eta : Real,
  real_le eta real_one -> real_le real_zero (real_plus real_one (real_opp eta)).
Proof.
  intros eta Hle. destruct Hle as [Hlt | Heq].
  - exact (inl (real_eq_lt_lt real_zero (real_plus eta (real_opp eta))
                  (real_plus real_one (real_opp eta))
                  (real_eq_sym (real_plus eta (real_opp eta)) real_zero
                     (real_plus_opp eta))
                  (real_lt_plus_compat_lt_le eta real_one (real_opp eta) (real_opp eta)
                    Hlt (real_le_refl (real_opp eta))))).
  - exact (inr (real_eq_sym (real_plus real_one (real_opp eta)) real_zero
                    (real_eq_trans (real_plus real_one (real_opp eta))
                                 (real_plus eta (real_opp eta)) real_zero
                    (RealSetoid.real_eq_plus_compat real_one (real_opp eta)
                       eta (real_opp eta)
                       (real_eq_sym eta real_one Heq) (real_eq_refl (real_opp eta)))
                    (real_plus_opp eta)))).
Qed.

(* 0 ≤ a、0 < b ⟹ 0 < a+b *)
Lemma kl_le_lt_plus : forall a b : Real,
  real_le real_zero a -> real_lt real_zero b ->
  real_lt real_zero (real_plus a b).
Proof.
  intros a b Ha Hb. destruct Ha as [Hlt | Heq].
  - exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero) (real_plus a b)
             kl_zero_plus_zero
             (real_lt_plus_compat real_zero a real_zero b Hlt Hb)).
  - apply (real_lt_eq_lt real_zero b (real_plus a b) Hb).
    exact (real_eq_sym (real_plus a b) b
             (real_eq_trans (real_plus a b) (real_plus real_zero b) b
                (RealSetoid.real_eq_plus_compat a b real_zero b
                   (real_eq_sym real_zero a Heq) (real_eq_refl b))
                (kl_plus_zero_l b))).
Qed.

(* 0 ≤ m、0 < E ⟹ 0 ≤ E·m（弱乘保序 + eq 换形） *)
Lemma kl_le_mult_weak_swap : forall m E : Real,
  real_le real_zero m -> real_lt real_zero E -> real_le real_zero (real_mult E m).
Proof.
  intros m E Hm HE.
  exact (kl_le_eq_r real_zero (real_mult m E) (real_mult E m)           (kl_le_eq_l (real_mult real_zero E) (real_mult m E) real_zero              (real_le_mult_compat_weak real_zero m E (inl HE) Hm)              (kl_mult_zero_l E))           (real_mult_comm m E)).
Qed.

(* 种子乘正元/非负元：c·(1+t) ≤ c·e^t + c·δ *)
Lemma kl_seed_mul : forall (c t e2 : Real),
  real_le real_zero c -> real_lt real_zero e2 ->
  real_le (real_mult c (real_plus real_one t))
          (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2)).
Proof.
  intros c t e2 Hc0 He2.
  assert (Hseed : real_le (real_plus real_one t) (real_plus (cauchy_real_exp t) e2))
    by (apply real_exp_ge_linear_eps; exact He2).
  assert (Hab : real_le (real_mult (real_plus real_one t) c)
                        (real_mult (real_plus (cauchy_real_exp t) e2) c))
    by (exact (real_le_mult_compat_weak (real_plus real_one t)
                 (real_plus (cauchy_real_exp t) e2) c Hc0 Hseed)).
  assert (Hdis : real_eq (real_mult (real_plus (cauchy_real_exp t) e2) c)
                         (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2)))
    by (exact (real_eq_trans
                 (real_mult (real_plus (cauchy_real_exp t) e2) c)
                 (real_plus (real_mult (cauchy_real_exp t) c) (real_mult e2 c))
                 (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2))
                 (kl_distrib_r (cauchy_real_exp t) e2 c)
                 (RealSetoid.real_eq_plus_compat
                    (real_mult (cauchy_real_exp t) c) (real_mult e2 c)
                    (real_mult c (cauchy_real_exp t)) (real_mult c e2)
                    (real_mult_comm (cauchy_real_exp t) c)
                    (real_mult_comm e2 c)))).
  apply (kl_le_eq_l (real_mult (real_plus real_one t) c)
                    (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2))
                    (real_mult c (real_plus real_one t))).
  - apply (kl_le_eq_r (real_mult (real_plus real_one t) c)
                      (real_mult (real_plus (cauchy_real_exp t) e2) c)
                      (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2))
                      Hab Hdis).
  - apply real_mult_comm.
Qed.


(* ========== M0.1：二点凸性核（Varberg 锥） ==========
   e^{(1−η)x+ηy} ≤ (1−η)·e^x + η·e^y + eps
   【假命题修正】任务说明原陈述方向反了（(1−η)e^x+ηe^y ≤ e^z+eps 为 Jensen
   反向，一般假）。AM-GM a^{1−η}b^η ≤ (1−η)a+ηb 的 e-形态真值为凸性方向
   e^z ≤ 加权和，其证明恰为任务说明给的 Varberg 锥论证（种子两式乘 e^z>0
   加权合并）。本文件按真值方向陈述。 *)
Lemma real_exp_two_point_cvx_eps : forall (x y eta : Real),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (cauchy_real_exp (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                      (real_mult eta y)))
          (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta))
                                            (cauchy_real_exp x))
                                (real_mult eta (cauchy_real_exp y)))
                     eps).
Proof.
  intros x y eta Heta_pos Heta_le eps Heps.
  set (m := real_plus real_one (real_opp eta)).
  set (z := real_plus (real_mult m x) (real_mult eta y)).
  set (s := real_plus x (real_opp y)).
  set (tA := real_mult eta s).
  set (tB := real_mult m (real_opp s)).
  assert (HEpos : real_lt real_zero (cauchy_real_exp z)) by apply cauchy_real_exp_pos.
  set (E := cauchy_real_exp z).
  set (cA := real_mult E m).
  set (cB := real_mult E eta).
  assert (Hm0 : real_le real_zero m)
    by exact (kl_one_minus_eta_nonneg eta Heta_le).
  assert (HcA0 : real_le real_zero cA) by exact (kl_le_mult_weak_swap m E Hm0 HEpos).
  assert (HcBpos : real_lt real_zero cB)
    by exact (real_mult_positive E eta HEpos Heta_pos).
  set (c := real_plus cA cB).
  assert (Hcpos : real_lt real_zero c) by exact (kl_le_lt_plus cA cB HcA0 HcBpos).
  set (d := real_mult eps (real_inv_pos c Hcpos)).
  assert (Hdpos : real_lt real_zero d)
    by exact (real_mult_positive eps (real_inv_pos c Hcpos) Heps
                (real_inv_pos_pos c Hcpos)).
  (* 两种子各乘 cA / cB 后相加 *)
  assert (HseedA : real_le (real_mult cA (real_plus real_one tA))
                           (real_plus (real_mult cA (cauchy_real_exp tA))
                                      (real_mult cA d)))
    by exact (kl_seed_mul cA tA d HcA0 Hdpos).
  assert (HseedB : real_le (real_mult cB (real_plus real_one tB))
                           (real_plus (real_mult cB (cauchy_real_exp tB))
                                      (real_mult cB d)))
    by exact (kl_seed_mul cB tB d (inl HcBpos) Hdpos).
  assert (Hsumle : real_le (real_plus (real_mult cA (real_plus real_one tA))
                                      (real_mult cB (real_plus real_one tB)))
                           (real_plus (real_plus (real_mult cA (cauchy_real_exp tA))
                                                 (real_mult cA d))
                                      (real_plus (real_mult cB (cauchy_real_exp tB))
                                                 (real_mult cB d))))
    by exact (real_le_plus_compat _ _ _ _ HseedA HseedB).
  (* 锥恒等式：加权和左端 == E（展开 m 后纯环） *)
  assert (EqCore : real_eq (real_plus (real_mult cA (real_plus real_one tA))
                                      (real_mult cB (real_plus real_one tB)))
                           E)
    by exact (kl_ring_core E eta s).
  (* e 指数重组：E·e^{tA} == e^x、E·e^{tB} == e^y *)
  assert (HEqA : real_eq (real_mult E (cauchy_real_exp tA)) (cauchy_real_exp x))
    by exact (real_eq_trans (real_mult E (cauchy_real_exp tA))
                            (cauchy_real_exp (real_plus z tA)) (cauchy_real_exp x)
                 (real_eq_sym (cauchy_real_exp (real_plus z tA))
                              (real_mult (cauchy_real_exp z) (cauchy_real_exp tA))
                              (cauchy_real_exp_plus z tA))
                 (cauchy_real_exp_wd (real_plus z tA) x (kl_z_tA x y eta))).
  assert (HEqB : real_eq (real_mult E (cauchy_real_exp tB)) (cauchy_real_exp y))
    by exact (real_eq_trans (real_mult E (cauchy_real_exp tB))
                            (cauchy_real_exp (real_plus z tB)) (cauchy_real_exp y)
                 (real_eq_sym (cauchy_real_exp (real_plus z tB))
                              (real_mult (cauchy_real_exp z) (cauchy_real_exp tB))
                              (cauchy_real_exp_plus z tB))
                 (cauchy_real_exp_wd (real_plus z tB) y (kl_z_tB x y eta))).
  (* 误差吸收：cA·d + cB·d == eps（d := eps·(1/c)） *)
  assert (ErrEq : real_eq (real_plus (real_mult cA d) (real_mult cB d)) eps)
    by exact (real_eq_trans (real_plus (real_mult cA d) (real_mult cB d))
                            (real_mult c d) eps
                 (kl_sum_prod_r cA cB d)
                 (real_eq_trans (real_mult c d)
                    (real_mult eps (real_mult c (real_inv_pos c Hcpos))) eps
                    (kl_swap3 c eps (real_inv_pos c Hcpos))
                    (real_eq_trans
                       (real_mult eps (real_mult c (real_inv_pos c Hcpos)))
                       (real_mult eps real_one) eps
                       (RealSetoid.real_eq_mult_compat eps
                          (real_mult c (real_inv_pos c Hcpos)) eps real_one
                          (real_eq_refl eps) (real_inv_pos_correct c Hcpos))
                       (real_mult_one eps)))).
  (* 终组装 eq：四项重排 + exp 重组 + 误差吸收 *)
  assert (EqFinal : real_eq (real_plus (real_plus (real_mult cA (cauchy_real_exp tA))
                                                  (real_mult cA d))
                                       (real_plus (real_mult cB (cauchy_real_exp tB))
                                                  (real_mult cB d)))
                            (real_plus (real_plus (real_mult m (cauchy_real_exp x))
                                                  (real_mult eta (cauchy_real_exp y)))
                                       eps)).
  { apply (real_eq_trans
             (real_plus (real_plus (real_mult cA (cauchy_real_exp tA)) (real_mult cA d))
                        (real_plus (real_mult cB (cauchy_real_exp tB)) (real_mult cB d)))
             (real_plus (real_plus (real_mult cA (cauchy_real_exp tA))
                                   (real_mult cB (cauchy_real_exp tB)))
                        (real_plus (real_mult cA d) (real_mult cB d)))
             (real_plus (real_plus (real_mult m (cauchy_real_exp x))
                                   (real_mult eta (cauchy_real_exp y))) eps)).
    - exact (real_plus_swap_mid (real_mult cA (cauchy_real_exp tA)) (real_mult cA d)
                                (real_mult cB (cauchy_real_exp tB)) (real_mult cB d)).
    - exact (RealSetoid.real_eq_plus_compat
               (real_plus (real_mult cA (cauchy_real_exp tA))
                          (real_mult cB (cauchy_real_exp tB)))
               (real_plus (real_mult cA d) (real_mult cB d))
               (real_plus (real_mult m (cauchy_real_exp x))
                          (real_mult eta (cauchy_real_exp y)))
               eps
               (RealSetoid.real_eq_plus_compat
                  (real_mult cA (cauchy_real_exp tA))
                  (real_mult cB (cauchy_real_exp tB))
                  (real_mult m (cauchy_real_exp x))
                  (real_mult eta (cauchy_real_exp y))
                  (real_eq_trans (real_mult cA (cauchy_real_exp tA))
                                 (real_mult m (real_mult E (cauchy_real_exp tA)))
                                 (real_mult m (cauchy_real_exp x))
                    (kl_assoc_swap E m (cauchy_real_exp tA))
                    (RealSetoid.real_eq_mult_compat m
                       (real_mult E (cauchy_real_exp tA)) m (cauchy_real_exp x)
                       (real_eq_refl m) HEqA))
                  (real_eq_trans (real_mult cB (cauchy_real_exp tB))
                                 (real_mult eta (real_mult E (cauchy_real_exp tB)))
                                 (real_mult eta (cauchy_real_exp y))
                    (kl_assoc_swap E eta (cauchy_real_exp tB))
                    (RealSetoid.real_eq_mult_compat eta
                       (real_mult E (cauchy_real_exp tB)) eta (cauchy_real_exp y)
                       (real_eq_refl eta) HEqB)))
               ErrEq). }
  exact (kl_le_eq_r E
           (real_plus (real_plus (real_mult cA (cauchy_real_exp tA)) (real_mult cA d))
                      (real_plus (real_mult cB (cauchy_real_exp tB)) (real_mult cB d)))
           (real_plus (real_plus (real_mult m (cauchy_real_exp x))
                                 (real_mult eta (cauchy_real_exp y))) eps)
           (kl_le_eq_l
              (real_plus (real_mult cA (real_plus real_one tA))
                         (real_mult cB (real_plus real_one tB)))
              (real_plus (real_plus (real_mult cA (cauchy_real_exp tA))
                                    (real_mult cA d))
                         (real_plus (real_mult cB (cauchy_real_exp tB))
                                    (real_mult cB d)))
              E Hsumle EqCore)
           EqFinal).
Qed.

(* ========== M0.2：逐点 AM-GM ==========
   a^{1−η}·b^η ≤ (1−η)·a + η·b + eps（a^{α} := e^{α·log a}） *)
Definition real_pow_pos (a alpha : Real) (Ha : real_lt real_zero a) : Real :=
  cauchy_real_exp (real_mult alpha (cw_log a Ha)).

Lemma real_amgm_pointwise_eps : forall (a b eta : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_mult (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                     (real_pow_pos b eta Hb))
          (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                                (real_mult eta b)) eps).
Proof.
  intros a b eta Ha Hb Heta_pos Heta_le eps Heps.
  assert (Hcvx : real_le
            (cauchy_real_exp (real_plus
               (real_mult (real_plus real_one (real_opp eta)) (cw_log a Ha))
               (real_mult eta (cw_log b Hb))))
            (real_plus (real_plus
               (real_mult (real_plus real_one (real_opp eta))
                          (cauchy_real_exp (cw_log a Ha)))
               (real_mult eta (cauchy_real_exp (cw_log b Hb)))) eps))
    by exact (real_exp_two_point_cvx_eps (cw_log a Ha) (cw_log b Hb) eta
                Heta_pos Heta_le eps Heps).
  exact (kl_le_eq_r
           (real_mult (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                      (real_pow_pos b eta Hb))
           (real_plus (real_plus
                        (real_mult (real_plus real_one (real_opp eta))
                                   (cauchy_real_exp (cw_log a Ha)))
                        (real_mult eta (cauchy_real_exp (cw_log b Hb)))) eps)
           (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                                 (real_mult eta b)) eps)
           (kl_le_eq_l
              (cauchy_real_exp (real_plus
                 (real_mult (real_plus real_one (real_opp eta)) (cw_log a Ha))
                 (real_mult eta (cw_log b Hb))))
              (real_plus (real_plus
                            (real_mult (real_plus real_one (real_opp eta))
                                       (cauchy_real_exp (cw_log a Ha)))
                            (real_mult eta (cauchy_real_exp (cw_log b Hb)))) eps)
              (real_mult (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                         (real_pow_pos b eta Hb))
              Hcvx
              (cauchy_real_exp_plus
                 (real_mult (real_plus real_one (real_opp eta)) (cw_log a Ha))
                 (real_mult eta (cw_log b Hb))))
           (RealSetoid.real_eq_plus_compat
              (real_plus (real_mult (real_plus real_one (real_opp eta))
                                    (cauchy_real_exp (cw_log a Ha)))
                         (real_mult eta (cauchy_real_exp (cw_log b Hb))))
              eps
              (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                         (real_mult eta b))
              eps
              (RealSetoid.real_eq_plus_compat
                 (real_mult (real_plus real_one (real_opp eta))
                            (cauchy_real_exp (cw_log a Ha)))
                 (real_mult eta (cauchy_real_exp (cw_log b Hb)))
                 (real_mult (real_plus real_one (real_opp eta)) a)
                 (real_mult eta b)
                 (RealSetoid.real_eq_mult_compat
                    (real_plus real_one (real_opp eta))
                    (cauchy_real_exp (cw_log a Ha))
                    (real_plus real_one (real_opp eta)) a
                    (real_eq_refl (real_plus real_one (real_opp eta)))
                    (cw_log_exp_right a Ha))
                 (RealSetoid.real_eq_mult_compat eta
                    (cauchy_real_exp (cw_log b Hb)) eta b
                    (real_eq_refl eta) (cw_log_exp_right b Hb)))
              (real_eq_refl eps))).
Qed.

(* ========== M1：求和版插值不等式（Z ≤ 1 + eps） ==========
   Z := Σ_i π_t(i)^{1−η}·π*(i)^η ≤ 1 + eps。
   误差吸收：逐点误差取 eps·π_t(i)（正权），归一化 Σπ_t == 1 后总误差
   Σ(eps·π_t) == eps·1 == eps——无除法、无折半，纯归一化吸收。 *)
Lemma real_interp_Z_le_one_eps :
  forall (n : nat) (pit pist : nat -> Real) (eta : Real)
    (Hpit : forall i : nat, real_lt real_zero (pit i))
    (Hpist : forall i : nat, real_lt real_zero (pist i))
    (Hnormp : real_eq (real_list_sum nat pit (seq 0 n)) real_one)
    (Hnormq : real_eq (real_list_sum nat pist (seq 0 n)) real_one),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_list_sum nat
             (fun i : nat => real_mult
                (real_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i))
                (real_pow_pos (pist i) eta (Hpist i)))
             (seq 0 n))
          (real_plus real_one eps).
Proof.
  intros n pit pist eta Hpit Hpist Hnormp Hnormq Heta_pos Heta_le eps Heps.
  set (m := real_plus real_one (real_opp eta)).
  (* 逐点 AM-GM，误差项配权 eps·pit i *)
  assert (Hpt : forall i : nat,
            real_le (real_mult (real_pow_pos (pit i) m (Hpit i))
                               (real_pow_pos (pist i) eta (Hpist i)))
                    (real_plus (real_plus (real_mult m (pit i))
                                          (real_mult eta (pist i)))
                               (real_mult eps (pit i)))).
  { intro i.
    exact (real_amgm_pointwise_eps (pit i) (pist i) eta (Hpit i) (Hpist i)
             Heta_pos Heta_le (real_mult eps (pit i))
             (real_mult_positive eps (pit i) Heps (Hpit i))). }
  assert (Hsumle : real_le
            (real_list_sum nat (fun i : nat => real_mult
                                  (real_pow_pos (pit i) m (Hpit i))
                                  (real_pow_pos (pist i) eta (Hpist i))) (seq 0 n))
            (real_list_sum nat (fun i : nat => real_plus
                                  (real_plus (real_mult m (pit i))
                                             (real_mult eta (pist i)))
                                  (real_mult eps (pit i))) (seq 0 n)))
    by exact (real_list_sum_le nat _ _ (seq 0 n) Hpt).
  (* Qsum == Σf + Σg（f i := m·pit i + η·pist i，g i := eps·pit i） *)
  assert (Hsplit : real_eq
            (real_list_sum nat (fun i : nat => real_plus
                                  (real_plus (real_mult m (pit i))
                                             (real_mult eta (pist i)))
                                  (real_mult eps (pit i))) (seq 0 n))
            (real_plus (real_list_sum nat (fun i : nat => real_plus
                                              (real_mult m (pit i))
                                              (real_mult eta (pist i))) (seq 0 n))
                       (real_list_sum nat (fun i : nat => real_mult eps (pit i))
                          (seq 0 n))))
    by exact (real_list_sum_add nat _ _ (seq 0 n)).
  (* Σf == m·Σpit + η·Σpist == m + η == 1 *)
  assert (Hf : real_eq (real_list_sum nat (fun i : nat => real_plus
                                             (real_mult m (pit i))
                                             (real_mult eta (pist i))) (seq 0 n))
                       real_one).
  { apply (real_eq_trans _
             (real_plus (real_list_sum nat (fun i : nat => real_mult m (pit i)) (seq 0 n))
                        (real_list_sum nat (fun i : nat => real_mult eta (pist i)) (seq 0 n)))).
    - exact (real_list_sum_add nat _ _ (seq 0 n)).
    - apply (real_eq_trans _
                (real_plus (real_mult m (real_list_sum nat pit (seq 0 n)))
                           (real_mult eta (real_list_sum nat pist (seq 0 n))))).
      + exact (RealSetoid.real_eq_plus_compat _ _ _ _
                   (real_list_sum_linear nat m pit (seq 0 n))
                   (real_list_sum_linear nat eta pist (seq 0 n))).
      + apply (real_eq_trans _ (real_plus m eta)).
        * exact (RealSetoid.real_eq_plus_compat
                    (real_mult m (real_list_sum nat pit (seq 0 n)))
                    (real_mult eta (real_list_sum nat pist (seq 0 n))) m eta
                    (real_eq_trans (real_mult m (real_list_sum nat pit (seq 0 n)))
                       (real_mult m real_one) m
                       (RealSetoid.real_eq_mult_compat m
                          (real_list_sum nat pit (seq 0 n)) m real_one
                          (real_eq_refl m) Hnormp)
                       (real_mult_one m))
                    (real_eq_trans (real_mult eta (real_list_sum nat pist (seq 0 n)))
                       (real_mult eta real_one) eta
                       (RealSetoid.real_eq_mult_compat eta
                          (real_list_sum nat pist (seq 0 n)) eta real_one
                          (real_eq_refl eta) Hnormq)
                       (real_mult_one eta))).
        * exact (kl_ring_m_plus_eta eta). }
  (* Σg == eps·Σpit == eps·1 == eps *)
  assert (Hg : real_eq (real_list_sum nat (fun i : nat => real_mult eps (pit i)) (seq 0 n)) eps).
  { apply (real_eq_trans _ (real_mult eps (real_list_sum nat pit (seq 0 n)))).
    - exact (real_list_sum_linear nat eps pit (seq 0 n)).
    - exact (real_eq_trans (real_mult eps (real_list_sum nat pit (seq 0 n)))
                           (real_mult eps real_one) eps
               (RealSetoid.real_eq_mult_compat eps (real_list_sum nat pit (seq 0 n))
                  eps real_one (real_eq_refl eps) Hnormp)
               (real_mult_one eps)). }
  (* 合拢：Z ≤ Σf + Σg == 1 + eps *)
  exact (kl_le_eq_r
           (real_list_sum nat (fun i : nat => real_mult
                                 (real_pow_pos (pit i) m (Hpit i))
                                 (real_pow_pos (pist i) eta (Hpist i))) (seq 0 n))
           (real_list_sum nat (fun i : nat => real_plus
                                 (real_plus (real_mult m (pit i))
                                            (real_mult eta (pist i)))
                                 (real_mult eps (pit i))) (seq 0 n))
           (real_plus real_one eps)
           Hsumle
           (real_eq_trans
              (real_list_sum nat (fun i : nat => real_plus
                                    (real_plus (real_mult m (pit i))
                                               (real_mult eta (pist i)))
                                    (real_mult eps (pit i))) (seq 0 n))
              (real_plus (real_list_sum nat (fun i : nat => real_plus
                                                (real_mult m (pit i))
                                                (real_mult eta (pist i))) (seq 0 n))
                         (real_list_sum nat (fun i : nat => real_mult eps (pit i))
                            (seq 0 n)))
              (real_plus real_one eps)
              Hsplit
              (RealSetoid.real_eq_plus_compat
                 (real_list_sum nat (fun i : nat => real_plus
                                       (real_mult m (pit i))
                                       (real_mult eta (pist i))) (seq 0 n))
                 (real_list_sum nat (fun i : nat => real_mult eps (pit i)) (seq 0 n))
                 real_one eps Hf Hg))).
Qed.

(* ========== M2 前置：log 代数 + 环恒等式 ========== *)

(* a + b == 0 ⟹ b == −a *)
Lemma kl_eq_plus_opp_uniq_r : forall a b : Real,
  real_eq (real_plus a b) real_zero -> real_eq b (real_opp a).
Proof.
  intros a b H.
  assert (Hstep1 : real_eq (real_plus (real_opp a) (real_plus a b))
                           (real_plus (real_opp a) real_zero))
    by exact (RealSetoid.real_eq_plus_compat (real_opp a) (real_plus a b)
                (real_opp a) real_zero (real_eq_refl (real_opp a)) H).
  assert (Hstep2 : real_eq (real_plus (real_opp a) real_zero) (real_opp a))
    by exact (real_plus_zero (real_opp a)).
  assert (Hstep3 : real_eq (real_plus (real_opp a) (real_plus a b)) b).
  { exact (real_eq_trans (real_plus (real_opp a) (real_plus a b))
                         (real_plus (real_plus (real_opp a) a) b) b
             (real_plus_assoc (real_opp a) a b)
             (real_eq_trans (real_plus (real_plus (real_opp a) a) b)
                            (real_plus real_zero b) b
                (RealSetoid.real_eq_plus_compat (real_plus (real_opp a) a) b
                   real_zero b
                   (real_eq_trans (real_plus (real_opp a) a)
                      (real_plus a (real_opp a)) real_zero
                      (real_plus_comm (real_opp a) a) (real_plus_opp a))
                   (real_eq_refl b))
                (kl_plus_zero_l b))). }
  exact (real_eq_trans b (real_plus (real_opp a) (real_plus a b)) (real_opp a)
           (real_eq_sym _ _ Hstep3) (real_eq_trans _ _ _ Hstep1 Hstep2)).
Qed.


Lemma kl_log_inv : forall (x : Real) (Hx : real_lt real_zero x)
    (Hix : real_lt real_zero (real_inv_pos x Hx)),
  real_eq (cw_log (real_inv_pos x Hx) Hix) (real_opp (cw_log x Hx)).
Proof.
  intros x Hx Hix.
  assert (Hprodpos : real_lt real_zero (real_mult x (real_inv_pos x Hx)))
    by exact (real_mult_positive x (real_inv_pos x Hx) Hx Hix).
  assert (Hmult : real_eq (cw_log (real_mult x (real_inv_pos x Hx)) Hprodpos)
                           (real_plus (cw_log x Hx) (cw_log (real_inv_pos x Hx) Hix)))
    by exact (log_inv_mult_thm x (real_inv_pos x Hx) Hx Hix Hprodpos).
  assert (Hone : real_eq (cw_log (real_mult x (real_inv_pos x Hx)) Hprodpos) real_zero).
  { apply (real_eq_trans _ (cw_log real_one real_lt_zero_one)).
    - exact (real_log_wd (real_mult x (real_inv_pos x Hx)) real_one Hprodpos
                real_lt_zero_one (real_inv_pos_correct x Hx)).
    - exact (real_log_one real_lt_zero_one). }
  exact (kl_eq_plus_opp_uniq_r (cw_log x Hx) (cw_log (real_inv_pos x Hx) Hix)
           (real_eq_trans (real_plus (cw_log x Hx) (cw_log (real_inv_pos x Hx) Hix))
              (cw_log (real_mult x (real_inv_pos x Hx)) Hprodpos) real_zero
              (real_eq_sym
                 (cw_log (real_mult x (real_inv_pos x Hx)) Hprodpos)
                 (real_plus (cw_log x Hx) (cw_log (real_inv_pos x Hx) Hix)) Hmult)
              Hone)).
Qed.

(* 环恒等式族 *)
Lemma kl_ring_reassoc : forall X Y Z W : Real,
  real_eq (real_mult (real_mult (real_mult X Y) Z) W)
          (real_mult X (real_mult Y (real_mult Z W))).
Proof. intros X Y Z W. destruct X as [a Ha]. destruct Y as [b Hb]. destruct Z as [c Hc].
  destruct W as [d Hd]. apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

Lemma kl_ring_opp_swap : forall X Y : Real,
  real_eq (real_opp (real_plus X (real_opp Y))) (real_plus Y (real_opp X)).
Proof. intros X Y. destruct X as [a Ha]. destruct Y as [b Hb].
  apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

Lemma kl_ring_log4 : forall eta lp lr LZ : Real,
  real_eq (real_plus (real_mult (real_plus real_one (real_opp eta)) lp)
                     (real_plus (real_mult eta lr)
                                (real_plus (real_opp LZ) (real_opp lp))))
          (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) lp)
                                (real_mult eta lr))
                     (real_plus (real_opp LZ) (real_opp lp))).
Proof. intros eta lp lr LZ. destruct eta as [e He]. destruct lp as [u Hu].
  destruct lr as [v Hv]. destruct LZ as [w Hw]. apply real_eq_of_zero_diff.
  intro n. simpl. ring. Qed.

Lemma kl_ring_neg4 : forall eta lp lr LZ : Real,
  real_eq (real_opp (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) lp)
                                          (real_mult eta lr))
                               (real_plus (real_opp LZ) (real_opp lp))))
          (real_plus (real_mult eta (real_plus lp (real_opp lr))) LZ).
Proof. intros eta lp lr LZ. destruct eta as [e He]. destruct lp as [u Hu].
  destruct lr as [v Hv]. destruct LZ as [w Hw]. apply real_eq_of_zero_diff.
  intro n. simpl. ring. Qed.

Lemma kl_ring_kl_split : forall eta W X Z : Real,
  real_eq (real_mult W (real_plus (real_mult eta X) Z))
          (real_plus (real_mult eta (real_mult W X)) (real_mult W Z)).
Proof. intros eta W X Z. destruct eta as [e He]. destruct W as [w Hw].
  destruct X as [x Hx]. destruct Z as [z Hz]. apply real_eq_of_zero_diff.
  intro n. simpl. ring. Qed.


Lemma kl_log_le_mono : forall (a b : Real) (Ha : real_lt real_zero a)
    (Hb : real_lt real_zero b),
  real_le a b -> real_le (cw_log a Ha) (cw_log b Hb).
Proof.
  intros a b Ha Hb Hab. destruct Hab as [Hlt | Heq].
  - exact (inl (real_log_lt_mono a b Ha Hb Hlt)).
  - exact (inr (real_log_wd a b Ha Hb Heq)).
Qed.

(* ========== M2：KL 恒等组装 ==========
   π_{t+1}(i) := π_t(i)^{1−η}·π*(i)^η / Z（几何插值策略）。
   精确恒等：KL(π_t‖π_{t+1}) == η·KL(π_t‖π★) + log Z（逐点 kl_term 代数 +
   归一化吸收 Σp == 1），再由 M1（Z ≤ 1+eps）+ 严格种子（1+eps < e^eps，
   KL(π_t‖π_{t+1}) ≤ η·KL(π_t‖π★) + eps。 *)

(* 几何插值配分函数 Z := Σ_i π_t(i)^{1−η}·π*(i)^η *)
Definition real_interp_Z (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i)) : Real :=
  real_list_sum nat
    (fun i : nat => real_mult
       (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
       (real_pow_pos (r i) eta (Hr i)))
    (seq 0 n).

(* 下一策略 π_{t+1}(i) := π_t(i)^{1−η}·π*(i)^η / Z *)
Definition real_step_next (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr)) : nat -> Real :=
  fun i : nat => real_mult
    (real_mult (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
               (real_pow_pos (r i) eta (Hr i)))
    (real_inv_pos (real_interp_Z n p r eta Hp Hr) HZ).

Theorem real_step_kl_eta_bound_eps :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnormp : real_eq (real_list_sum nat p (seq 0 n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (seq 0 n)) real_one)
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n p r eta Hp Hr HZ i)),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_list_sum nat
             (fun i : nat => real_kl_term (p i)
                             (real_step_next n p r eta Hp Hr HZ i) (Hp i) (Hqv i))
             (seq 0 n))
          (real_plus (real_mult eta
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (p i) (r i) (Hp i) (Hr i))
                           (seq 0 n)))
                     eps).
Proof.
  intros n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta_pos Heta_le eps Heps.
  set (m := real_plus real_one (real_opp eta)).
  set (Z := real_interp_Z n p r eta Hp Hr).
  set (q := real_step_next n p r eta Hp Hr HZ).
  set (LZ := cw_log Z HZ).
  set (Rsum := real_list_sum nat
                 (fun i : nat => real_kl_term (p i) (r i) (Hp i) (Hr i)) (seq 0 n)).
  (* ---- 逐点 KL 恒等（精确 eq） ---- *)
  assert (Hpi : forall i : nat,
    real_eq (real_kl_term (p i) (q i) (Hp i) (Hqv i))
            (real_plus (real_mult eta (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                       (real_mult (p i) LZ))).
  { intro i.
    set (ipp := real_inv_pos (p i) (Hp i)).
    set (izz := real_inv_pos Z HZ).
    set (pA := real_pow_pos (p i) m (Hp i)).
    set (pB := real_pow_pos (r i) eta (Hr i)).
    
    assert (Hip : real_lt real_zero ipp) by exact (real_inv_pos_pos (p i) (Hp i)).
    assert (Hizp : real_lt real_zero izz) by exact (real_inv_pos_pos Z HZ).
    assert (HpA : real_lt real_zero pA)
      by exact (cauchy_real_exp_pos (real_mult m (cw_log (p i) (Hp i)))).
    assert (HpB : real_lt real_zero pB)
      by exact (cauchy_real_exp_pos (real_mult eta (cw_log (r i) (Hr i)))).
    set (Hqqlog := real_mult_positive (q i) (real_inv_pos (p i) (Hp i)) (Hqv i)
                  (real_inv_pos_pos (p i) (Hp i))).
    set (Hrplog := real_mult_positive (r i) (real_inv_pos (p i) (Hp i)) (Hr i)
                  (real_inv_pos_pos (p i) (Hp i))).
    
    assert (HlA : real_eq (cw_log pA HpA) (real_mult m (cw_log (p i) (Hp i))))
      by exact (log_inv_exp_neg_thm (real_mult m (cw_log (p i) (Hp i))) HpA).
    assert (HlB : real_eq (cw_log pB HpB) (real_mult eta (cw_log (r i) (Hr i))))
      by exact (log_inv_exp_neg_thm (real_mult eta (cw_log (r i) (Hr i))) HpB).
    assert (HlZ : real_eq (cw_log izz Hizp) (real_opp LZ))
      by exact (kl_log_inv Z HZ Hizp).
    assert (HlP : real_eq (cw_log ipp Hip) (real_opp (cw_log (p i) (Hp i))))
      by exact (kl_log_inv (p i) (Hp i) Hip).
    
    assert (Hlogrp : real_eq (cw_log (real_mult (r i) ipp) Hrplog)
                             (real_plus (cw_log (r i) (Hr i))
                                        (real_opp (cw_log (p i) (Hp i))))).
    { exact (real_eq_trans (cw_log (real_mult (r i) ipp) Hrplog)
               (real_plus (cw_log (r i) (Hr i)) (cw_log ipp Hip))
               (real_plus (cw_log (r i) (Hr i)) (real_opp (cw_log (p i) (Hp i))))
               (log_inv_mult_thm (r i) ipp (Hr i) Hip Hrplog)
               (RealSetoid.real_eq_plus_compat (cw_log (r i) (Hr i)) (cw_log ipp Hip)
                  (cw_log (r i) (Hr i)) (real_opp (cw_log (p i) (Hp i)))
                  (real_eq_refl (cw_log (r i) (Hr i))) HlP)). }
    (* q·inv p 参数重排（纯环） *)
    assert (Hring1 : real_eq (real_mult (q i) ipp)
                             (real_mult pA (real_mult pB (real_mult izz ipp))))
      by exact (kl_ring_reassoc pA pB izz ipp).
    assert (Hpos3 : real_lt real_zero (real_mult izz ipp))
      by exact (real_mult_positive izz ipp Hizp Hip).
    assert (Hpos2 : real_lt real_zero (real_mult pB (real_mult izz ipp)))
      by exact (real_mult_positive pB (real_mult izz ipp) HpB Hpos3).
    assert (HAB4 : real_lt real_zero (real_mult pA (real_mult pB (real_mult izz ipp))))
      by exact (real_mult_positive pA (real_mult pB (real_mult izz ipp)) HpA Hpos2).
    
    assert (Hlog4 : real_eq (cw_log (real_mult (q i) ipp) Hqqlog)
                       (real_plus (cw_log pA HpA)
                          (real_plus (cw_log pB HpB)
                             (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))).
    { apply (real_eq_trans (cw_log (real_mult (q i) ipp) Hqqlog)
               (cw_log (real_mult pA (real_mult pB (real_mult izz ipp))) HAB4)
               (real_plus (cw_log pA HpA)
                  (real_plus (cw_log pB HpB)
                     (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))).
      - exact (real_log_wd (real_mult (q i) ipp)
                 (real_mult pA (real_mult pB (real_mult izz ipp))) Hqqlog HAB4 Hring1).
      - exact (real_eq_trans
                  (cw_log (real_mult pA (real_mult pB (real_mult izz ipp))) HAB4)
                  (real_plus (cw_log pA HpA)
                     (cw_log (real_mult pB (real_mult izz ipp)) Hpos2))
                  (real_plus (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))
                  (log_inv_mult_thm pA (real_mult pB (real_mult izz ipp)) HpA Hpos2 HAB4)
                  (RealSetoid.real_eq_plus_compat (cw_log pA HpA)
                     (cw_log (real_mult pB (real_mult izz ipp)) Hpos2)
                     (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip)))
                     (real_eq_refl (cw_log pA HpA))
                     (real_eq_trans
                        (cw_log (real_mult pB (real_mult izz ipp)) Hpos2)
                        (real_plus (cw_log pB HpB) (cw_log (real_mult izz ipp) Hpos3))
                        (real_plus (cw_log pB HpB)
                           (real_plus (cw_log izz Hizp) (cw_log ipp Hip)))
                        (log_inv_mult_thm pB (real_mult izz ipp) HpB Hpos3 Hpos2)
                        (RealSetoid.real_eq_plus_compat (cw_log pB HpB)
                           (cw_log (real_mult izz ipp) Hpos3)
                           (cw_log pB HpB)
                           (real_plus (cw_log izz Hizp) (cw_log ipp Hip))
                           (real_eq_refl (cw_log pB HpB))
                           (log_inv_mult_thm izz ipp Hizp Hip Hpos3))))). }
    
    assert (Hlog4' : real_eq (cw_log (real_mult (q i) ipp) Hqqlog)
                       (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                             (real_mult eta (cw_log (r i) (Hr i))))
                                  (real_plus (real_opp LZ)
                                             (real_opp (cw_log (p i) (Hp i)))))).
    { apply (real_eq_trans (cw_log (real_mult (q i) ipp) Hqqlog)
               (real_plus (cw_log pA HpA)
                  (real_plus (cw_log pB HpB)
                     (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))
               (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                     (real_mult eta (cw_log (r i) (Hr i))))
                          (real_plus (real_opp LZ)
                                     (real_opp (cw_log (p i) (Hp i)))))).
      - exact Hlog4.
      - exact (real_eq_trans
                  (real_plus (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))
                  (real_plus (real_mult m (cw_log (p i) (Hp i)))
                     (real_plus (real_mult eta (cw_log (r i) (Hr i)))
                        (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i))))))
                  (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                        (real_mult eta (cw_log (r i) (Hr i))))
                     (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i)))))
                  (RealSetoid.real_eq_plus_compat (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip)))
                     (real_mult m (cw_log (p i) (Hp i)))
                     (real_plus (real_mult eta (cw_log (r i) (Hr i)))
                        (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i)))))
                     HlA
                     (RealSetoid.real_eq_plus_compat (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip))
                        (real_mult eta (cw_log (r i) (Hr i)))
                        (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i))))
                        HlB
                        (RealSetoid.real_eq_plus_compat (cw_log izz Hizp)
                           (cw_log ipp Hip) (real_opp LZ)
                           (real_opp (cw_log (p i) (Hp i))) HlZ HlP)))
                  (kl_ring_log4 eta (cw_log (p i) (Hp i)) (cw_log (r i) (Hr i)) LZ)). }
    
    assert (Hneg : real_eq (real_opp (cw_log (real_mult (q i) ipp) Hqqlog))
                       (real_plus (real_mult eta
                                     (real_plus (cw_log (p i) (Hp i))
                                                (real_opp (cw_log (r i) (Hr i)))))
                                  LZ)).
    { exact (real_eq_trans (real_opp (cw_log (real_mult (q i) ipp) Hqqlog))
               (real_opp (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                                (real_mult eta (cw_log (r i) (Hr i))))
                                    (real_plus (real_opp LZ)
                                               (real_opp (cw_log (p i) (Hp i))))))
               (real_plus (real_mult eta
                             (real_plus (cw_log (p i) (Hp i))
                                        (real_opp (cw_log (r i) (Hr i)))))
                          LZ)
               (RealSetoid.real_eq_opp_compat
                  (cw_log (real_mult (q i) ipp) Hqqlog)
                  (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                        (real_mult eta (cw_log (r i) (Hr i))))
                     (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i)))))
                  Hlog4')
               (kl_ring_neg4 eta (cw_log (p i) (Hp i)) (cw_log (r i) (Hr i)) LZ)). }
    
    assert (HnegR : real_eq (real_plus (cw_log (p i) (Hp i))
                                       (real_opp (cw_log (r i) (Hr i))))
                            (real_opp (cw_log (real_mult (r i) ipp) Hrplog))).
    { exact (real_eq_trans
                (real_plus (cw_log (p i) (Hp i)) (real_opp (cw_log (r i) (Hr i))))
                (real_opp (real_plus (cw_log (r i) (Hr i))
                                     (real_opp (cw_log (p i) (Hp i)))))
                (real_opp (cw_log (real_mult (r i) ipp) Hrplog))
                (real_eq_sym (real_opp (real_plus (cw_log (r i) (Hr i))
                                                  (real_opp (cw_log (p i) (Hp i)))))
                   (real_plus (cw_log (p i) (Hp i))
                              (real_opp (cw_log (r i) (Hr i))))
                   (kl_ring_opp_swap (cw_log (r i) (Hr i)) (cw_log (p i) (Hp i))))
                (real_eq_sym (real_opp (cw_log (real_mult (r i) ipp) Hrplog))
                   (real_opp (real_plus (cw_log (r i) (Hr i))
                                        (real_opp (cw_log (p i) (Hp i)))))
                   (RealSetoid.real_eq_opp_compat
                      (cw_log (real_mult (r i) ipp) Hrplog)
                      (real_plus (cw_log (r i) (Hr i))
                                 (real_opp (cw_log (p i) (Hp i))))
                      Hlogrp))). }
    (* 终装配：kl(p,q) == η·kl(p,r) + p·LZ *)
    exact (real_eq_trans
              (real_mult (p i) (real_opp (cw_log (real_mult (q i) ipp) Hqqlog)))
              (real_plus
                 (real_mult eta
                    (real_mult (p i)
                       (real_plus (cw_log (p i) (Hp i))
                                  (real_opp (cw_log (r i) (Hr i))))))
                 (real_mult (p i) LZ))
              (real_plus (real_mult eta (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                         (real_mult (p i) LZ))
              (real_eq_trans
                 (real_mult (p i) (real_opp (cw_log (real_mult (q i) ipp) Hqqlog)))
                 (real_mult (p i)
                    (real_plus (real_mult eta
                                  (real_plus (cw_log (p i) (Hp i))
                                             (real_opp (cw_log (r i) (Hr i)))))
                               LZ))
                 (real_plus
                    (real_mult eta
                       (real_mult (p i)
                          (real_plus (cw_log (p i) (Hp i))
                                     (real_opp (cw_log (r i) (Hr i))))))
                    (real_mult (p i) LZ))
                 (RealSetoid.real_eq_mult_compat (p i)
                    (real_opp (cw_log (real_mult (q i) ipp) Hqqlog)) (p i)
                    (real_plus (real_mult eta
                                 (real_plus (cw_log (p i) (Hp i))
                                            (real_opp (cw_log (r i) (Hr i)))))
                               LZ)
                    (real_eq_refl (p i)) Hneg)
                 (kl_ring_kl_split eta (p i)
                    (real_plus (cw_log (p i) (Hp i))
                               (real_opp (cw_log (r i) (Hr i))))
                    LZ))
              (RealSetoid.real_eq_plus_compat
                 (real_mult eta
                    (real_mult (p i)
                       (real_plus (cw_log (p i) (Hp i))
                                  (real_opp (cw_log (r i) (Hr i))))))
                 (real_mult (p i) LZ)
                 (real_mult eta (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                 (real_mult (p i) LZ)
                 (RealSetoid.real_eq_mult_compat eta
                    (real_mult (p i)
                       (real_plus (cw_log (p i) (Hp i))
                                  (real_opp (cw_log (r i) (Hr i)))))
                    eta (real_kl_term (p i) (r i) (Hp i) (Hr i))
                    (real_eq_refl eta)
                    (real_eq_trans
                       (real_mult (p i)
                          (real_plus (cw_log (p i) (Hp i))
                                     (real_opp (cw_log (r i) (Hr i)))))
                       (real_mult (p i)
                          (real_opp (cw_log (real_mult (r i) ipp) Hrplog)))
                       (real_kl_term (p i) (r i) (Hp i) (Hr i))
                       (RealSetoid.real_eq_mult_compat (p i)
                          (real_plus (cw_log (p i) (Hp i))
                                     (real_opp (cw_log (r i) (Hr i))))
                          (p i)
                          (real_opp (cw_log (real_mult (r i) ipp) Hrplog))
                          (real_eq_refl (p i)) HnegR)
                       (real_eq_refl (real_kl_term (p i) (r i) (Hp i) (Hr i)))))
                 (real_eq_refl (real_mult (p i) LZ)))). }
  (* ---- 求和层：Σ kl(p,q) == η·Σ kl(p,r) + LZ（归一化吸收） ---- *)
  assert (Hsum : real_eq
      (real_list_sum nat
         (fun i : nat => real_kl_term (p i) (q i) (Hp i) (Hqv i)) (seq 0 n))
      (real_plus (real_mult eta Rsum) LZ)).
  { apply (real_eq_trans
             (real_list_sum nat
                (fun i : nat => real_kl_term (p i) (q i) (Hp i) (Hqv i)) (seq 0 n))
             (real_list_sum nat
                (fun i : nat => real_plus
                                   (real_mult eta
                                      (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                                   (real_mult (p i) LZ))
                (seq 0 n))
             (real_plus (real_mult eta Rsum) LZ)).
    - exact (real_list_sum_ext nat _ _ (seq 0 n) Hpi).
    - apply (real_eq_trans
                (real_list_sum nat
                   (fun i : nat => real_plus
                                      (real_mult eta
                                         (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                                      (real_mult (p i) LZ))
                   (seq 0 n))
                (real_plus
                   (real_list_sum nat
                      (fun i : nat => real_mult eta
                                       (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                      (seq 0 n))
                   (real_list_sum nat (fun i : nat => real_mult (p i) LZ) (seq 0 n)))
                (real_plus (real_mult eta Rsum) LZ)).
      + exact (real_list_sum_add nat _ _ (seq 0 n)).
      + exact (real_eq_trans
                  (real_plus
                     (real_list_sum nat
                        (fun i : nat => real_mult eta
                                         (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                        (seq 0 n))
                     (real_list_sum nat (fun i : nat => real_mult (p i) LZ)
                        (seq 0 n)))
                  (real_plus (real_mult eta Rsum)
                     (real_mult LZ (real_list_sum nat p (seq 0 n))))
                  (real_plus (real_mult eta Rsum) LZ)
                  (RealSetoid.real_eq_plus_compat
                     (real_list_sum nat
                        (fun i : nat => real_mult eta
                                         (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                        (seq 0 n))
                     (real_list_sum nat (fun i : nat => real_mult (p i) LZ)
                        (seq 0 n))
                     (real_mult eta Rsum)
                     (real_mult LZ (real_list_sum nat p (seq 0 n)))
                     (real_list_sum_linear nat eta
                        (fun i : nat => real_kl_term (p i) (r i) (Hp i) (Hr i))
                        (seq 0 n))
                     (real_list_sum_linear_r nat LZ p (seq 0 n)))
                  (RealSetoid.real_eq_plus_compat (real_mult eta Rsum)
                     (real_mult LZ (real_list_sum nat p (seq 0 n)))
                     (real_mult eta Rsum) LZ
                     (real_eq_refl (real_mult eta Rsum))
                     (real_eq_trans (real_mult LZ (real_list_sum nat p (seq 0 n)))
                        (real_mult LZ real_one) LZ
                        (RealSetoid.real_eq_mult_compat LZ
                           (real_list_sum nat p (seq 0 n)) LZ real_one
                           (real_eq_refl LZ) Hnormp)
                        (real_mult_one LZ)))). }
  (* ---- log Z ≤ eps：M1 + 严格种子 + log 单调 ---- *)
  assert (HLZ : real_le LZ eps).
  { assert (HZle : real_le Z (real_plus real_one eps))
      by exact (real_interp_Z_le_one_eps n p r eta Hp Hr Hnormp Hnormr
                  Heta_pos Heta_le eps Heps).
    assert (Honep : real_lt real_zero (real_plus real_one eps))
      by exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                  (real_plus real_one eps) kl_zero_plus_zero
                  (real_lt_plus_compat real_zero real_one real_zero eps
                     real_lt_zero_one Heps)).
    assert (Hlogle : real_le LZ (cw_log (real_plus real_one eps) Honep))
      by exact (kl_log_le_mono Z (real_plus real_one eps) HZ Honep HZle).
    assert (Hloglt : real_lt (cw_log (real_plus real_one eps) Honep) eps).
    { apply (real_lt_eq_lt (cw_log (real_plus real_one eps) Honep)
               (cw_log (cauchy_real_exp eps) (cauchy_real_exp_pos eps)) eps).
      - exact (real_log_lt_mono (real_plus real_one eps) (cauchy_real_exp eps)
                  Honep (cauchy_real_exp_pos eps) (real_exp_ge_linear eps Heps)).
      - exact (log_inv_exp_neg_thm eps (cauchy_real_exp_pos eps)). }
    exact (real_le_trans LZ (cw_log (real_plus real_one eps) Honep) eps
             Hlogle (inl Hloglt)). }
  (* ---- 终局 ---- *)
  apply (real_le_trans
           (real_list_sum nat
              (fun i : nat => real_kl_term (p i) (q i) (Hp i) (Hqv i)) (seq 0 n))
           (real_plus (real_mult eta Rsum) LZ)
           (real_plus (real_mult eta Rsum) eps)).
  - exact (inr Hsum).
  - exact (real_le_plus_compat (real_mult eta Rsum) (real_mult eta Rsum) LZ eps
             (real_le_refl (real_mult eta Rsum)) HLZ).
Qed.

(* ============================ §1 step_kl 消解的 M3 迭代版 Real 层副本 ============================ *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring.
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
Import RealInterfaceEnhancedMod.
Local Open Scope nat_scope.

(* ========== M3.0 基础定义 ========== *)

(* 离散状态表：n 个状态 [0;1;...;n-1]（list 离散状态世界） *)
Definition m3_states (n : nat) : list nat := seq 0 n.

(* KL 的 list 版：逐项 real_kl_term 折叠求和 *)
Definition m3_kl_list (n : nat) (f g : nat -> Real)
    (Hf : forall i : nat, real_lt real_zero (f i))
    (Hg : forall i : nat, real_lt real_zero (g i)) : Real :=
  real_list_sum nat
    (fun i : nat => real_kl_term (f i) (g i) (Hf i) (Hg i))
    (m3_states n).

(* 几何率底 κ := 1−η *)
Definition m3_kappa (eta : Real) : Real := real_plus real_one (real_opp eta).

(* κ 的 t 次幂（nat 重复乘）※ S 遮蔽 Datatypes.S，须限定名 *)
Fixpoint m3_rpow (a : Real) (t : nat) : Real :=
  match t with
  | Datatypes.O => real_one
  | Datatypes.S t' => real_mult a (m3_rpow a t')
  end.

(* t·x（nat 重复加；逐步误差 eps 的 t 步累积） *)
Fixpoint m3_nmul (k : nat) (x : Real) : Real :=
  match k with
  | Datatypes.O => real_zero
  | Datatypes.S k' => real_plus x (m3_nmul k' x)
  end.

(* 1+1 > 0（对半预算的分母） *)
Lemma m3_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)           (real_plus real_one real_one)           (real_eq_sym (real_plus real_zero real_zero) real_zero              kl_zero_plus_zero)           (real_lt_plus_compat real_zero real_one real_zero real_one              real_lt_zero_one real_lt_zero_one)).
Qed.

(* eps 对半：d := eps·inv(1+1)（M3.1 的双 eps 预算合一） *)
Definition m3_half (eps : Real) : Real :=
  real_mult eps (real_inv_pos (real_plus real_one real_one) m3_two_pos).

Lemma m3_half_pos : forall eps : Real,
  real_lt real_zero eps -> real_lt real_zero (m3_half eps).
Proof.
  intros eps Heps.
  unfold m3_half.
  exact (real_mult_positive eps           (real_inv_pos (real_plus real_one real_one) m3_two_pos)           Heps           (real_inv_pos_pos (real_plus real_one real_one) m3_two_pos)).
Qed.

Lemma m3_half_double_eq : forall eps : Real,
  real_eq (real_plus (m3_half eps) (m3_half eps)) eps.
Proof.
  intros eps. unfold m3_half.
  set (dd := real_mult eps (real_inv_pos (real_plus real_one real_one) m3_two_pos)).
  set (two := real_plus real_one real_one).
  apply (real_eq_trans (real_plus dd dd) (real_mult two dd)).
  - exact (real_eq_trans (real_plus dd dd)
             (real_plus (real_mult real_one dd) (real_mult real_one dd))
             (real_mult two dd)
             (RealSetoid.real_eq_plus_compat dd dd
                (real_mult real_one dd) (real_mult real_one dd)
                (real_eq_sym (real_mult real_one dd) dd (kl_mult_one_l dd))
                (real_eq_sym (real_mult real_one dd) dd (kl_mult_one_l dd)))
             (kl_sum_prod_r real_one real_one dd)).
  - exact (real_eq_trans (real_mult two dd)
             (real_mult eps (real_mult two (real_inv_pos two m3_two_pos)))
             eps
             (kl_swap3 two eps (real_inv_pos two m3_two_pos))
             (real_eq_trans
                (real_mult eps (real_mult two (real_inv_pos two m3_two_pos)))
                (real_mult eps real_one)
                eps
                (RealSetoid.real_eq_mult_compat eps
                   (real_mult two (real_inv_pos two m3_two_pos)) eps real_one
                   (real_eq_refl eps)
                   (real_inv_pos_correct two m3_two_pos))
                (real_mult_one eps))).
Qed.

(* ========== 环 / 序辅助 ========== *)

(* η + (1−η) == 1 *)
Lemma m3_ring_eta_kappa : forall eta : Real,
  real_eq (real_plus eta (m3_kappa eta)) real_one.
Proof.
  intros eta. destruct eta as [v Hv]. unfold m3_kappa.
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* η < 1 ⟹ 0 < 1−η *)
Lemma m3_kappa_pos : forall eta : Real,
  real_lt eta real_one -> real_lt real_zero (m3_kappa eta).
Proof.
  intros eta Hlt.
  unfold m3_kappa.
  exact (real_eq_lt_lt real_zero (real_plus eta (real_opp eta))           (real_plus real_one (real_opp eta))           (real_eq_sym (real_plus eta (real_opp eta)) real_zero              (real_plus_opp eta))           (real_lt_plus_compat_lt_le eta real_one (real_opp eta)              (real_opp eta) Hlt (real_le_refl (real_opp eta)))).
Qed.

(* 0 < η ⟹ 1−η ≤ 1 *)
Lemma m3_kappa_le_one : forall eta : Real,
  real_lt real_zero eta -> real_le (m3_kappa eta) real_one.
Proof.
  intros eta Hpos. unfold m3_kappa. apply kl_lt_le_bridge.
  set (X := real_plus real_one (real_opp eta)).
  assert (Hstep1 : real_lt (real_plus real_zero X) (real_plus eta X))
    by exact (real_lt_plus_compat_lt_le real_zero eta X X Hpos (real_le_refl X)).
  assert (Hstep2 : real_lt (real_plus real_zero X) real_one)
    by exact (real_lt_eq_lt (real_plus real_zero X) (real_plus eta X) real_one
                Hstep1 (m3_ring_eta_kappa eta)).
  exact (real_eq_lt_lt (real_plus real_one (real_opp eta))
           (real_plus real_zero X) real_one
           (real_eq_trans (real_plus real_one (real_opp eta)) X (real_plus real_zero X)
              (real_eq_refl X)
              (real_eq_sym (real_plus real_zero X) X (kl_plus_zero_l X)))
           Hstep2).
Qed.

(* κ ≤ 1、0 ≤ y ⟹ κ·y ≤ y *)
Lemma m3_le_kappa_mul : forall kappa y : Real,
  real_le real_zero y -> real_le kappa real_one ->
  real_le (real_mult kappa y) y.
Proof.
  intros kappa y Hy0 Hk1.
  apply (kl_le_eq_r (real_mult kappa y) (real_mult real_one y) y).
  - exact (real_le_mult_compat_weak kappa real_one y Hy0 Hk1).
  - apply kl_mult_one_l.
Qed.

(* 0 ≤ c、a ≤ b ⟹ c·a ≤ c·b（左乘版） *)
Lemma m3_le_mult_compat_l : forall c a b : Real,
  real_le real_zero c -> real_le a b -> real_le (real_mult c a) (real_mult c b).
Proof.
  intros c a b Hc Hab.
  apply (kl_le_eq_r (real_mult c a) (real_mult b c) (real_mult c b)).
  - apply (kl_le_eq_l (real_mult a c) (real_mult b c) (real_mult c a)).
    + exact (real_le_mult_compat_weak a b c Hc Hab).
    + apply real_mult_comm.
  - apply real_mult_comm.
Qed.

(* 环：a·(b+c) == a·b + a·c *)
Lemma m3_distrib_l : forall a b c : Real,
  real_eq (real_mult a (real_plus b c)) (real_plus (real_mult a b) (real_mult a c)).
Proof.
  intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 环：a·(b·c) == (a·b)·c *)
Lemma m3_ring_reassoc2 : forall a b c : Real,
  real_eq (real_mult a (real_mult b c)) (real_mult (real_mult a b) c).
Proof.
  intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 0 < x ⟹ 0 ≤ t·x *)
Lemma m3_nmul_nonneg : forall (k : nat) (x : Real),
  real_lt real_zero x -> real_le real_zero (m3_nmul k x).
Proof.
  intros k x Hx. induction k as [| k IH].
  - apply real_le_refl.
  - exact (kl_le_eq_l (real_plus real_zero real_zero)
             (real_plus x (m3_nmul k x)) real_zero
             (real_le_plus_compat real_zero x real_zero (m3_nmul k x)
                (kl_lt_le_bridge real_zero x Hx) IH)
             kl_zero_plus_zero).
Qed.

(* n ≠ 0 ⟹ 状态表非空 *)
Lemma m3_seq_nonnil : forall n : nat, n <> 0 -> m3_states n <> nil.
Proof.
  intros n Hn Hnil. unfold m3_states in Hnil.
  destruct n as [| m].
  - exact (Hn eq_refl).
  - simpl in Hnil. discriminate Hnil.
Qed.

(* 逐项正项的 list 和为正（配分函数正性核） *)
Lemma m3_interp_Z_pos2 : forall (n : nat) (Hn : n <> 0) (q r : nat -> Real)
    (k e : Real)
    (Hq : forall i : nat, real_lt real_zero (q i))
    (Hr : forall i : nat, real_lt real_zero (r i)),
  real_lt real_zero
    (real_list_sum nat
       (fun i : nat => real_mult
          (real_pow_pos (q i) k (Hq i)) (real_pow_pos (r i) e (Hr i)))
       (m3_states n)).
Proof.
  intros n Hn q r k e Hq Hr.
  apply (real_list_sum_pos nat).
  - intro i.
    exact (real_mult_positive (real_pow_pos (q i) k (Hq i))
             (real_pow_pos (r i) e (Hr i))
             (cauchy_real_exp_pos (real_mult k (cw_log (q i) (Hq i))))
             (cauchy_real_exp_pos (real_mult e (cw_log (r i) (Hr i))))).
  - exact (m3_seq_nonnil n Hn).
Qed.

(* 同上，结论取 real_interp_Z 原生形态（供 pkg 的 sigT 组件直接对型） *)
Lemma m3_interp_Z_pos3 : forall (n : nat) (Hn : n <> 0) (q r : nat -> Real)
    (k : Real)
    (Hq : forall i : nat, real_lt real_zero (q i))
    (Hr : forall i : nat, real_lt real_zero (r i)),
  real_lt real_zero (real_interp_Z n q r k Hq Hr).
Proof.
  intros n Hn q r k Hq Hr.
  exact (m3_interp_Z_pos2 n Hn q r (real_plus real_one (real_opp k)) k Hq Hr).
Qed.

(* 单步更新逐点正性：π'(i) := (r(i)^{1−k}·p(i)^k)·inv Z > 0 *)
Definition m3_step_pos_pt (n : nat) (r p : nat -> Real) (k : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (HZ : real_lt real_zero (real_interp_Z n r p k Hr Hp))
    (i : nat)
  : real_lt real_zero (real_step_next n r p k Hr Hp HZ i) :=
  real_mult_positive
    (real_mult (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))
               (real_pow_pos (p i) k (Hp i)))
    (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)
    (real_mult_positive
       (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))
       (real_pow_pos (p i) k (Hp i))
       (cauchy_real_exp_pos
          (real_mult (real_plus real_one (real_opp k)) (cw_log (r i) (Hr i))))
       (cauchy_real_exp_pos (real_mult k (cw_log (p i) (Hp i)))))
    (real_inv_pos_pos (real_interp_Z n r p k Hr Hp) HZ).

(* 单步更新归一化：Σ π' == inv Z·Z == 1（配分函数吸收） *)
Lemma m3_step_next_norm : forall (n : nat) (r p : nat -> Real) (k : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (HZ : real_lt real_zero (real_interp_Z n r p k Hr Hp)),
  real_eq
    (real_list_sum nat (real_step_next n r p k Hr Hp HZ) (m3_states n))
    real_one.
Proof.
  intros n r p k Hr Hp HZ.
  exact (real_eq_trans           (real_list_sum nat (real_step_next n r p k Hr Hp HZ) (m3_states n))           (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                      (real_list_sum nat                         (fun i : nat => real_mult                            (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                            (real_pow_pos (p i) k (Hp i)))                         (m3_states n)))           real_one           (real_list_sum_linear_r nat              (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)              (fun i : nat => real_mult                 (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                 (real_pow_pos (p i) k (Hp i)))              (m3_states n))           (real_eq_trans              (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                         (real_list_sum nat                            (fun i : nat => real_mult                               (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                               (real_pow_pos (p i) k (Hp i)))                            (m3_states n)))              (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                         (real_interp_Z n r p k Hr Hp))              real_one              (RealSetoid.real_eq_mult_compat                 (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                 (real_list_sum nat                    (fun i : nat => real_mult                       (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                       (real_pow_pos (p i) k (Hp i)))                    (m3_states n))                 (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                 (real_interp_Z n r p k Hr Hp)                 (real_eq_refl (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ))                 (real_eq_refl (real_interp_Z n r p k Hr Hp)))              (real_eq_trans                 (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                            (real_interp_Z n r p k Hr Hp))                 (real_mult (real_interp_Z n r p k Hr Hp)                            (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ))                 real_one                 (real_mult_comm (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                                 (real_interp_Z n r p k Hr Hp))                 (real_inv_pos_correct (real_interp_Z n r p k Hr Hp) HZ)))).
Qed.

(* ========== 策略迭代序列（sigT 封装：策略+正性+配分函数正性+归一化） ========== *)

(* 迭代包类型：p := π_t 连同其逐点正性、下一步配分函数正性、归一化恒等 *)
Definition m3_pkg_type (n : nat) (r : nat -> Real) (eta : Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) : Type :=
  { p : nat -> Real &
    { Hp : forall i : nat, real_lt real_zero (p i) &
      { HZ : real_lt real_zero (real_interp_Z n r p (m3_kappa eta) Hr Hp) &
        real_eq (real_list_sum nat p (m3_states n)) real_one } } }.

(* π_{t+1}(i) := real_step_next n r π_t (1−η)：几何插值策略更新
   π_{t+1}(i) := π*(i)^η·π_t(i)^{1−η}/Z_t。
   单 Fixpoint（对 t 结构递归），O 情形携带初值四项组，
   S 情形经 m3_step_pos_pt / m3_interp_Z_pos2 / m3_step_next_norm
   同步重建四项组。 *)
Fixpoint m3_pi_pkg (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) {struct t} : m3_pkg_type n r eta Hr :=
  match t with
  | Datatypes.O => existT _ p0 (existT _ Hp0 (existT _ HZ1 Hnorm0))
  | Datatypes.S t' =>
      let pkg := m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t' in
      let p := projT1 pkg in
      let Hp := projT1 (projT2 pkg) in
      let HZ := projT1 (projT2 (projT2 pkg)) in
      (existT _ (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
         (existT _ (fun i : nat => m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i)
           (existT
              (fun HZ' : real_lt real_zero
                          (real_interp_Z n r
                             (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                             (m3_kappa eta) Hr
                             (fun i : nat =>
                                m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i)) =>
                 real_eq
                   (real_list_sum nat
                      (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                      (m3_states n))
                   real_one)
              (m3_interp_Z_pos3 n Hn r
                 (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                 (m3_kappa eta) Hr
                 (fun i : nat => m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i))
              (m3_step_next_norm n r p (m3_kappa eta) Hr Hp HZ)))
       : m3_pkg_type n r eta Hr)
  end.

(* 四投影：迭代策略序列 / 逐点正性 / 配分函数正性 / 归一化 *)
Definition m3_pi_seq (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) : nat -> Real :=
  projT1 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t).

Definition m3_pi_seq_pos (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  forall i : nat,
    real_lt real_zero (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t i) :=
  fun i : nat => projT1 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)) i.

Definition m3_pi_seq_Zpos (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  real_lt real_zero
    (real_interp_Z n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
       (m3_kappa eta) Hr (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)) :=
  projT1 (projT2 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).

Definition m3_pi_seq_norm (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  real_eq
    (real_list_sum nat (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) (m3_states n))
    real_one :=
  projT2 (projT2 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).

(* ========== M3.1 前置：M2 换向单步几何收缩（eps 化 geom_step） ========== *)

(* 单步真几何率（根内 policy_iter_kl_geom_step 的 eps 化副本）：
   KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t) + eps。
   即 本件 的 M2（real_step_kl_eta_bound_eps）在迭代序列第 t 步的
   直接实例化：p-参数位 := r（π*），r-参数位 := π_t，eta-参数位 := κ := 1−η。 *)
Corollary real_iter_step_geom_eps :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
    (real_plus
       (real_mult (m3_kappa eta)
          (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)))
       eps).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1 t eps Heps.
  exact (real_step_kl_eta_bound_eps n r           (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           (m3_kappa eta) Hr           (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           Hnormr (m3_pi_seq_norm n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           (m3_pi_seq_Zpos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))           (m3_kappa_pos eta Heta_lt1) (m3_kappa_le_one eta Heta_pos)           eps Heps).
Qed.

(* ========== M3.1：单步向后 KL 递推（backward_kl_step_le 的 eps 化副本） ========== *)
(* KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t) + KL(π_t‖π_{t+1}) + eps
   路线（对应根内 policy_iter_backward_kl_step_le 的「丢弃负项」）：
   M2 换向实例给 KL(π*‖π_{t+1}) ≤ (1−η)KL(π*‖π_t) + d（d := eps/2），
   Gibbs 下界给 0 ≤ KL(π_t‖π_{t+1}) + d，两式相加后对半预算吸收 eps。 *)
Theorem real_iter_kl_step :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
    (real_plus
       (real_mult (m3_kappa eta)
          (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)))
       (real_plus
          (m3_kl_list n (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
             (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
          eps)).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1 t eps Heps.
  assert (HnormP : forall s : nat,
            real_eq
              (real_list_sum nat (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 s)
                 (m3_states n))
              real_one)
    by exact (m3_pi_seq_norm n p0 r eta Hn Hp0 Hr HZ1 Hnorm0).
  set (A := real_mult (m3_kappa eta)
              (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
                 (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).
  set (B := m3_kl_list n (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
              (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))).
  set (d := m3_half eps).
  apply (real_le_trans
           (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
           (real_plus (real_plus A d) (real_plus B d))
           (real_plus A (real_plus B eps))).
  - apply (real_le_trans
             (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
                (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
             (real_plus A d)
             (real_plus (real_plus A d) (real_plus B d))).
    + (* M2 换向实例：KL(π*‖π_{t+1}) ≤ κ·KL(π*‖π_t) + d *)
      exact (real_step_kl_eta_bound_eps n r
               (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               (m3_kappa eta) Hr
               (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               Hnormr (HnormP t)
               (m3_pi_seq_Zpos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
               (m3_kappa_pos eta Heta_lt1) (m3_kappa_le_one eta Heta_pos)
               d (m3_half_pos eps Heps)).
    + (* (A+d) ≤ (A+d) + (B+d)：Gibbs 下界 0 ≤ B + d *)
      exact (kl_le_eq_l (real_plus (real_plus A d) real_zero)
               (real_plus (real_plus A d) (real_plus B d))
               (real_plus A d)
               (real_le_plus_compat (real_plus A d) (real_plus A d)
                  real_zero (real_plus B d)
                  (real_le_refl (real_plus A d))
                  (real_gibbs_inequality_eps nat (m3_states n)
                     (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
                     (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                     (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
                     (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                     (HnormP t) (HnormP (Datatypes.S t)) d (m3_half_pos eps Heps)))
               (real_plus_zero (real_plus A d))).
  - (* eq 换形：(A+d)+(B+d) == A+(B+eps) *)
    exact (kl_eq_le_bridge (real_plus (real_plus A d) (real_plus B d))
             (real_plus A (real_plus B eps))
             (real_eq_trans (real_plus (real_plus A d) (real_plus B d))
             (real_plus (real_plus A B) (real_plus d d))
             (real_plus A (real_plus B eps))
             (real_plus_swap_mid A d B d)
             (real_eq_trans (real_plus (real_plus A B) (real_plus d d))
                (real_plus (real_plus A B) eps)
                (real_plus A (real_plus B eps))
                (RealSetoid.real_eq_plus_compat (real_plus A B) (real_plus d d)
                   (real_plus A B) eps
                   (real_eq_refl (real_plus A B))
                   (m3_half_double_eq eps))
                (real_eq_sym (real_plus A (real_plus B eps))
                   (real_plus (real_plus A B) eps)
                   (real_plus_assoc A B eps))))).
Qed.

(* ========== M3.2：真几何率迭代（geom_iter 的 eps 化副本） ========== *)
(* KL(π*‖π_t) ≤ (1−η)^t·KL(π*‖π_0) + t·eps
   （根内 policy_iter_kl_geom_iter 的 eps 化副本：单步收缩
     real_iter_step_geom_eps 对 t 归纳，误差按 t 步算术累积。） *)
Theorem real_iter_kl_geom :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))
    (real_plus
       (real_mult (m3_rpow (m3_kappa eta) t)
          (m3_kl_list n r p0 Hr Hp0))
       (m3_nmul t eps)).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1
         t eps Heps.
  induction t as [| t IH].
  - (* t = 0：κ^0 == 1、0·eps == 0，KL ≤ 1·KL + 0 == KL *)
    cbn [m3_rpow m3_nmul].
    apply kl_eq_le_bridge.
    apply (real_eq_sym
             (real_plus
                (real_mult real_one (m3_kl_list n r p0 Hr Hp0)) real_zero)
             (m3_kl_list n r p0 Hr Hp0)).
    exact (real_eq_trans
             (real_plus (real_mult real_one (m3_kl_list n r p0 Hr Hp0))
                        real_zero)
             (real_plus (m3_kl_list n r p0 Hr Hp0) real_zero)
             (m3_kl_list n r p0 Hr Hp0)
             (RealSetoid.real_eq_plus_compat
                (real_mult real_one (m3_kl_list n r p0 Hr Hp0)) real_zero
                (m3_kl_list n r p0 Hr Hp0) real_zero
                (kl_mult_one_l (m3_kl_list n r p0 Hr Hp0))
                (real_eq_refl real_zero))
             (real_plus_zero (m3_kl_list n r p0 Hr Hp0))).
  - (* t = S t：单步收缩 + IH 单调放大 + κ 系数重排 + 误差累积 *)
    cbn [m3_rpow m3_nmul].
    pose proof (real_iter_step_geom_eps n p0 r eta Hn Hp0 Hr HZ1 Hnorm0
                  Hnormr Heta_pos Heta_lt1 t eps Heps) as Hstep.
    set (KL0 := m3_kl_list n r p0 Hr Hp0).
    set (KLt := m3_kl_list n r
                  (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
                  (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)).
    set (KLs := m3_kl_list n r
                  (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                  Hr
                  (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0
                     (Datatypes.S t))).
    set (Y := m3_nmul t eps).
    set (X := real_mult (m3_rpow (m3_kappa eta) t) KL0).
    (* κ·单调：0 ≤ κ、IH ⟹ κ·KL_t ≤ κ·(κ^t·KL0 + t·eps) *)
    assert (Hmono : real_le (real_mult (m3_kappa eta) KLt)
                            (real_mult (m3_kappa eta) (real_plus X Y))).
    { apply (m3_le_mult_compat_l (m3_kappa eta)).
      - exact (kl_lt_le_bridge real_zero (m3_kappa eta)
                 (m3_kappa_pos eta Heta_lt1)).
      - exact IH. }
    (* 单步链：KL_{t+1} ≤ κ·KL_t + eps ≤ κ·(κ^t·KL0 + Y) + eps *)
    assert (Hchain : real_le KLs
                       (real_plus (real_mult (m3_kappa eta) (real_plus X Y))
                          eps)).
    { apply (real_le_trans KLs (real_plus (real_mult (m3_kappa eta) KLt) eps)).
      - exact Hstep.
      - exact (real_le_plus_compat (real_mult (m3_kappa eta) KLt)
                  (real_mult (m3_kappa eta) (real_plus X Y)) eps eps
                  Hmono (real_le_refl eps)). }
    (* 终组装：κ·(X+Y)+eps ≤ (κ·κ^t)·KL0 + (Y+eps)（κ·Y ≤ Y） *)
    apply (real_le_trans KLs
             (real_plus
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                   KL0)
                (real_plus (real_mult (m3_kappa eta) Y) eps))
             (real_plus
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                   KL0)
                (real_plus eps Y))).
    + apply (kl_le_eq_r _ (real_plus (real_mult (m3_kappa eta) (real_plus X Y)) eps)).
      * exact Hchain.
      * exact (real_eq_trans
                 (real_plus (real_mult (m3_kappa eta) (real_plus X Y)) eps)
                 (real_plus (real_plus (real_mult (m3_kappa eta) X)
                              (real_mult (m3_kappa eta) Y)) eps)
                 (real_plus
                    (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                       KL0)
                    (real_plus (real_mult (m3_kappa eta) Y) eps))
                 (RealSetoid.real_eq_plus_compat
                    (real_mult (m3_kappa eta) (real_plus X Y))
                    eps
                    (real_plus (real_mult (m3_kappa eta) X)
                       (real_mult (m3_kappa eta) Y))
                    eps
                    (m3_distrib_l (m3_kappa eta) X Y)
                    (real_eq_refl eps))
                 (real_eq_trans
                    (real_plus
                       (real_plus (real_mult (m3_kappa eta) X)
                          (real_mult (m3_kappa eta) Y)) eps)
                    (real_plus (real_mult (m3_kappa eta) X)
                       (real_plus (real_mult (m3_kappa eta) Y) eps))
                    (real_plus
                       (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                          KL0)
                       (real_plus (real_mult (m3_kappa eta) Y) eps))
                    (real_eq_sym
                       (real_plus (real_mult (m3_kappa eta) X)
                          (real_plus (real_mult (m3_kappa eta) Y) eps))
                       (real_plus
                          (real_plus (real_mult (m3_kappa eta) X)
                             (real_mult (m3_kappa eta) Y)) eps)
                       (real_plus_assoc (real_mult (m3_kappa eta) X)
                          (real_mult (m3_kappa eta) Y) eps))
                    (RealSetoid.real_eq_plus_compat
                       (real_mult (m3_kappa eta) X)
                       (real_plus (real_mult (m3_kappa eta) Y) eps)
                       (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                          KL0)
                       (real_plus (real_mult (m3_kappa eta) Y) eps)
                       (m3_ring_reassoc2 (m3_kappa eta) (m3_rpow (m3_kappa eta) t) KL0)
                       (real_eq_refl (real_plus (real_mult (m3_kappa eta) Y) eps))))).
    + exact (real_le_plus_compat
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0)
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0)
                (real_plus (real_mult (m3_kappa eta) Y) eps)
                (real_plus eps Y)
                (real_le_refl
                   (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0))
                (kl_le_eq_r
                   (real_plus (real_mult (m3_kappa eta) Y) eps)
                   (real_plus Y eps)
                   (real_plus eps Y)
                   (real_le_plus_compat (real_mult (m3_kappa eta) Y) Y eps eps
                      (m3_le_kappa_mul (m3_kappa eta) Y
                         (m3_nmul_nonneg t eps Heps)
                         (m3_kappa_le_one eta Heta_pos))
                      (real_le_refl eps))
                   (real_plus_comm Y eps))).
Qed.
