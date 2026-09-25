(* ============================================================ *)
(* ToyR 玩具证替换件 —— T255 台账席 战役包P（tier2 六批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   kl_le_mult_weak_swap（原 L157，2 句玩具证）                          *)
(*   kl_le_eq_l（原 L40，2 句玩具证）                                     *)
(*   kl_le_eq_r（原 L36，2 句玩具证）                                     *)
(*   kl_eq_le_bridge（原 L33，2 句玩具证）                                *)
(*   kl_lt_le_bridge（原 L30，2 句玩具证）                                *)
(* ============================================================ *)

(* ============================================================ *)
(* UpStepKL.v *)
(* *)
(* 目的： step_kl_eta_bound 的 Real 层 eps 化对应物。 *)
(* 主件： kl_distrib_r 分配律与 kl_ring_m_plus_eta 单步几何不等式。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 为策略迭代真几何率定理的唯一诚实接口的 eps 化形；零公理面、全 Qed、可提取。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpStepKL.v —— step_kl_eta_bound 的 Real 层消解                 *)
(* 论文 1 定理 4.8（策略迭代真几何率）唯一诚实接口的 eps 化对应物：  *)
(*   插值不等式 Z = Σ π_t^{1−η}·π*^η ≤ 1。                        *)
(* 路线：Varberg 锥论证（零 Jensen/Hölder 基建）                  *)
(*   M0.1 二点凸性核（e^{(1−η)x+ηy} ≤ (1−η)e^x + ηe^y + eps）      *)
(*   M0.2 逐点 AM-GM（a^{1−η}b^η ≤ (1−η)a + ηb + eps）            *)
(*   M1  求和版（Σ powprod ≤ 1 + eps，归一化吸收 eps·pit 权）       *)

(* 红线：零 公理/承认件；Set 层语句；全 Qed；可提取。            *)
(* ============================================================ *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
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
   【假命题修正】任务书原陈述方向反了（(1−η)e^x+ηe^y ≤ e^z+eps 为 Jensen
   反向，一般假）。AM-GM a^{1−η}b^η ≤ (1−η)a+ηb 的 e-形态真值为凸性方向
   e^z ≤ 加权和，其证明恰为任务书给的 Varberg 锥论证（种子两式乘 e^z>0
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
