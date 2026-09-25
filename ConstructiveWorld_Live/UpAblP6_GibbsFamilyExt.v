(* ==========================================================================)
   UpAblP6_GibbsFamilyExt.v — Gibbs 族的温度参数化扩展实例件
   使命: uagfe_gibbs_temp_one_B/temp_two_eps（温度 1 与 ε 形 Gibbs）、le_b_mult_pos_two_temp_flat（双温度乘法正性）与 Jeffreys 对称熵两件（uagfe_jeffreys_sym_temp_B/list_temp_B）。
   依赖: CW_ConstructiveWorld_219、UpRealLeB/2/3、UpReqKLStrictB、GibbsFamilyExt；Stdlib List。
   对标: Gibbs 不等式与 Jeffreys 散度的温度参数化族（信息论）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import List.
Import ListNotations.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import UpReqKLStrictB.
Require Import GibbsFamilyExt.

(* ============================================================ *)
(* §1 uagfe_gibbs_temp_one_B：单位温度 β=1 的逐点 Bishop 上界实例       *)
(* ============================================================ *)

Lemma uagfe_gibbs_temp_one_B : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_le_b (real_mult real_one (real_plus p (real_opp q)))
            (real_mult real_one (real_kl_term p q Hp Hq)).
Proof.
  intros p q Hp Hq.
  exact (gfe_gibbs_core_temp_B p q real_one Hp Hq real_lt_zero_one).
Qed.

(* ============================================================ *)
(* §2 uagfe_gibbs_temp_two_eps：双倍温度 β=2 的逐点 eps 实例形          *)
(* ============================================================ *)

Lemma uagfe_gibbs_temp_two_eps : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (eps : Real) (Heps : real_lt real_zero eps),
  real_le (real_mult (real_plus real_one real_one) (real_plus p (real_opp q)))
          (real_plus
             (real_mult (real_plus real_one real_one)
                        (real_kl_term p q Hp Hq))
             (real_mult (real_plus real_one real_one) (real_mult p eps))).
Proof.
  intros p q Hp Hq eps Heps.
  exact (gfe_gibbs_core_temp_eps p q (real_plus real_one real_one) Hp Hq           (gfe_le_of_lt (real_plus real_one real_one)              (real_plus_positive real_one real_one                 real_lt_zero_one real_lt_zero_one))           eps Heps).
Qed.

(* ============================================================ *)
(* §3 uagfe_le_b_mult_pos_two_temp_flat：两级温度复合平形式               *)
(* ============================================================ *)

Lemma uagfe_le_b_mult_pos_two_temp_flat :
  forall (x y b1 b2 : Real),
  real_lt real_zero b1 -> real_lt real_zero b2 ->
  real_le_b x y ->
  real_le_b (real_mult (real_mult b1 b2) x)
            (real_mult (real_mult b1 b2) y).
Proof.
  intros x y b1 b2 Hb1 Hb2 Hxy.
  apply (gfe_le_b_eq_r (real_mult (real_mult b1 b2) x)
           (real_mult b1 (real_mult b2 y))
           (real_mult (real_mult b1 b2) y)).
  - apply (leb3_le_b_eq_l (real_mult b1 (real_mult b2 x))
             (real_mult (real_mult b1 b2) x)
             (real_mult b1 (real_mult b2 y))).
    + exact (real_mult_assoc b1 b2 x).
    + exact (gfe_le_b_mult_pos (real_mult b2 x) (real_mult b2 y) b1 Hb1
               (gfe_le_b_mult_pos x y b2 Hb2 Hxy)).
  - exact (real_mult_assoc b1 b2 y).
Qed.

(* ============================================================ *)
(* §4 uagfe_jeffreys_sym_temp_B：0 ≤_B β·(kl(p‖q)+kl(q‖p))（点态）        *)
(* ============================================================ *)

Theorem uagfe_jeffreys_sym_temp_B : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_mult b (real_plus (real_kl_term p q Hp Hq)
                            (real_kl_term q p Hq Hp))).
Proof.
  intros p q b Hp Hq Hb.
  apply (leb3_le_b_eq_l (real_mult b real_zero) real_zero
           (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                   (real_kl_term q p Hq Hp)))).
  - exact (real_mult_zero b).
  - exact (gfe_le_b_mult_pos real_zero
             (real_plus (real_kl_term p q Hp Hq)
                        (real_kl_term q p Hq Hp))
             b Hb (gfe_jeffreys_sym_B p q Hp Hq)).
Qed.

(* ============================================================ *)
(* §5 uagfe_jeffreys_sym_list_temp_B（对称 Jeffreys 温度面·有限和）：     *)
(*   0 ≤_B β·Σ_s (kl(p s‖q s)+kl(q s‖p s))                              *)
(* ============================================================ *)

Theorem uagfe_jeffreys_sym_list_temp_B :
  forall (X : Type) (l : list X) (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (b : Real) (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_mult b (real_list_sum X
        (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                (real_kl_term (q s) (p s) (Hq s) (Hp s))) l)).
Proof.
  intros X l p q Hp Hq b Hb.
  apply (leb3_le_b_eq_l (real_mult b real_zero) real_zero
           (real_mult b (real_list_sum X
              (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                      (real_kl_term (q s) (p s) (Hq s) (Hp s)))
              l))).
  - exact (real_mult_zero b).
  - exact (gfe_le_b_mult_pos real_zero
             (real_list_sum X
                (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                        (real_kl_term (q s) (p s) (Hq s) (Hp s)))
                l)
             b Hb (gfe_jeffreys_sym_list_B X l p q Hp Hq)).
Qed.

(* ============================================================ *)
(* 收尾核验：Print Assumptions 五定理全 Closed（零公理零承认）            *)
(* ============================================================ *)

Print Assumptions uagfe_gibbs_temp_one_B.
Print Assumptions uagfe_gibbs_temp_two_eps.
Print Assumptions uagfe_le_b_mult_pos_two_temp_flat.
Print Assumptions uagfe_jeffreys_sym_temp_B.
Print Assumptions uagfe_jeffreys_sym_list_temp_B.
