(* ==========================================================================
   uabd_supply_S08_kl_term_equiv.v
   模块名：uabd_supply_S08_kl_term_equiv
   数学使命：S08_RealMainlineDPO 的 KL 逐点封装槽「real_kl_term p q ≡
     p·(log p − log q)」（KL 项等价，log 除法分解）之换向供给定理。
     S08 内该槽以 real_kl_sum_term（p·(log p − log p_b) 封装）假设位呈现；
     其逐点内容即本件语句对 (p, q) := (p s, p_b s) 之实例。本件由在库
     RealKLDecomp.rkd_kl_point（KL 逐点展开：real_kl_term p q ≡
     p·(log p − log q)）经 real_eq_sym 一步换向，得槽方向的独立具名供给面。
   依赖：S01–S08（real_kl_term/real_log/real_eq 族）、RealKLDecomp
     （rkd_kl_point 根供给）、Stdlib。
   对标行：rkd_kl_point@RealKLDecomp（根构造体承载非平凡性）；本件为
     换向喂形件（槽方向具名化），非占位、非平凡重述之独立槽形。
   构造性注记：全件 Qed 真构造；语句面全 Set 形（real_lt 为 sigT 形、
     real_eq 为逐 eps Set 形）；零 Axiom/Admitted/经典逻辑；文件尾
     Print Assumptions 取 Closed 判据。
   编译配方：coqc -q -Q <主vo树> "" -Q . "" uabd_supply_S08_kl_term_equiv.v
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import RealKLDecomp.

(* 换向供给：p·(log p − log q) ≡ real_kl_term p q（KL 项等价槽方向） *)
Theorem uabd_kl_term_equiv_sym :
  forall (p q : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
    real_eq (real_mult p (real_plus (real_log p Hp) (real_opp (real_log q Hq))))
            (real_kl_term p q Hp Hq).
Proof.
  intros p q Hp Hq.
  apply real_eq_sym.
  exact (rkd_kl_point p q Hp Hq).
Qed.

Print Assumptions uabd_kl_term_equiv_sym.
