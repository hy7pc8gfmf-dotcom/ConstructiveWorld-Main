(* ============================================================ *)
(* UpAblP6_GibbsFamilyExt.v —— T211 / PA6-01（论文6 消融战役）          *)
(* 消融对象：卡 E748（GibbsFamilyExt-温度形与对称Jeffreys形施工-20260918） *)
(* 对象盘面：ConstructiveWorld_Live/GibbsFamilyExt.v（gfe_ 前缀 13 枚，    *)
(*   0 伴生：无变量槽/参数声明/公理/定义件，全引理/定理）                  *)
(* ------------------------------------------------------------------ *)
(* 本件五面（每面注明证明路径，禁转发冒充）：                            *)
(*   P1 uagfe_gibbs_temp_one_B       单位温度 β=1 逐点 Bishop 实例形    *)
(*      路径=实例装配（gfe_gibbs_core_temp_B 于 β:=real_one 装配，        *)
(*      温度前提由 real_lt_zero_one 供给）                              *)
(*   P2 uagfe_gibbs_temp_two_eps     双倍温度 β=2 逐点 eps 实例形        *)
(*      路径=实例装配（gfe_gibbs_core_temp_eps 于 β:=1+1 装配；温度证书   *)
(*      real_plus_positive×real_lt_zero_one 两枚单位证书合成，再经族内    *)
(*      gfe_le_of_lt 桥降级为弱前提）                                   *)
(*   P3 uagfe_le_b_mult_pos_two_temp_flat                            *)
(*      le_b_mult_pos 补位（A5）的消费面重述：两级温度复合平形——          *)
(*      (b1·b2)·x ≤_B (b1·b2)·y（x ≤_B y、0<b1、0<b2）                   *)
(*      路径=上游直击×2 + assoc 换形链（gfe_le_b_mult_pos 两级复合，      *)
(*      gfe_le_b_eq_r / leb3_le_b_eq_l 左右元换形，real_mult_assoc 定向）*)
(*   P4 uagfe_jeffreys_sym_temp_B    对称 Jeffreys 温度面（点态）：       *)
(*      0 ≤_B β·(kl(p‖q)+kl(q‖p))——上游缺席面（上游温度面只有            *)
(*      单 kl gap 形，Jeffreys 和形升温面为本件新组）                    *)
(*      路径=独立链（gfe_jeffreys_sym_B 供 x ≤_B y，gfe_le_b_mult_pos    *)
(*      升温，real_mult_zero+leb3_le_b_eq_l 收零换形）                   *)
(*   P5 uagfe_jeffreys_sym_list_temp_B 对称 Jeffreys 温度面（有限和）：   *)
(*      0 ≤_B β·Σ_s (kl(p s‖q s)+kl(q s‖p s))                           *)
(*      路径=独立链（gfe_jeffreys_sym_list_B 供和形，同 P4 升温链）       *)
(* ------------------------------------------------------------------ *)
(* 红线自审：全 Qed 闭合；real_le/real_lt/real_le_b/real_eq 全 Set 值     *)
(*   （CW219 S01 自建 Or 编码）；零公理零假设位；文尾 Print Assumptions   *)
(*   五面全 Closed。                                                    *)
(* 编译配方：/tmp/pa7_work 内 cpu_guard 温控                             *)
(*   rocq c -Q /tmp/pa7_work "" -Q /tmp/pa6_side "" -Q /tmp/czn14_union_full "" *)
(* 依赖面（全在盘只读，零改上游）：CW_ConstructiveWorld_219（含 S07       *)
(*   real_lt_zero_one/real_plus_positive 出口）、UpRealLeB、UpRealLeB2、  *)
(*   UpRealLeB3、UpReqKLStrictB、GibbsFamilyExt（消融对象本体）。          *)
(* ============================================================ *)

From Stdlib Require Import List.
Import ListNotations.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import UpReqKLStrictB.
Require Import GibbsFamilyExt.

(* ============================================================ *)
(* P1 单位温度 β=1 逐点 Bishop 实例形（实例装配）                         *)
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
(* P2 双倍温度 β=2 逐点 eps 实例形（实例装配＋温度证书合成）               *)
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
  exact (gfe_gibbs_core_temp_eps p q (real_plus real_one real_one) Hp Hq
           (gfe_le_of_lt (real_plus real_one real_one)
              (real_plus_positive real_one real_one
                 real_lt_zero_one real_lt_zero_one))
           eps Heps).
Qed.

(* ============================================================ *)
(* P3 le_b_mult_pos 补位消费面重述：两级温度复合平形                       *)
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
(* P4 对称 Jeffreys 温度面（点态）：0 ≤_B β·(kl(p‖q)+kl(q‖p))             *)
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
(* P5 对称 Jeffreys 温度面（有限和）：                                    *)
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
(* 闭合审计（G4：Print Assumptions 五面全 Closed）                        *)
(* ============================================================ *)

Print Assumptions uagfe_gibbs_temp_one_B.
Print Assumptions uagfe_gibbs_temp_two_eps.
Print Assumptions uagfe_le_b_mult_pos_two_temp_flat.
Print Assumptions uagfe_jeffreys_sym_temp_B.
Print Assumptions uagfe_jeffreys_sym_list_temp_B.
