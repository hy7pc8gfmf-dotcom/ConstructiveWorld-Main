(* ============================================================ *)
(* UpAblMetaWorld3.v —— N4 席：非退化 2 元核世界（核行互异）+ TV 精确几何衰减      *)
(*   + 混合时间下界（AID 在 cf2 上反驳的下界件在此世界为真）· 2026-09-20          *)
(*                                                              *)
(* 【世界构造】bool 载体，硬编码对称常数核（Q 可判定，全定义级）：                  *)
(*     K(t,t) = 3/4   K(t,f) = 1/4   K(f,t) = 1/4   K(f,f) = 3/4               *)
(*   常数经 half := inv(2) 的域运算嵌入（1/4 := (1/2)·(1/2)，3/4 := 1−1/4）。     *)
(*   行随机：3/4 + 1/4 = 1（每行）；行互异：第 true 列 3/4 ≠ 1/4（mtw_rows_ne，    *)
(*   经 one ≠ zero 的反证路——与 AID 的 mtl_kernel_val_{t,f}「核每行==inv_two」      *)
(*   行全同病灶成对照：此处两行不等 = 非退化判据。                                 *)
(* 【主结果】点质量对（mu0=[1;0]、nu0=[0;1]）在单步差分耦合下：                    *)
(*     dv(n+1) = dv(n)·(K(t,t)−K(f,t)) = dv(n)·(1/2)，df = −dv（质量守恒+补元），  *)
(*   故 TV(n) == (1/2)^n · TV₀ 精确（mtw_tv_exact_iter），步恒等                   *)
(*   TV(S n) == (1/2)·TV(n)（mtw_tv_step_exact），下界                             *)
(*   budget < (1/2)^n·TV₀ -> lt budget (TV(n))（mtw_no_mixing_below——AID 的        *)
(*   mtl_no_mixing_refuted 同形语句在此世界为真），以及甲形正件                     *)
(*   le ((1/2)^n·TV₀) (TV(n))（mtw_tv_lower——AID 的 mtl_refute_lower 同形在此为真）。*)
(*   跨世界对照：cf2 = 一步即混退化世界（TV(1)==zero）vs 本世界 = 真几何衰减         *)
(*   非退化世界（TV(n) == (1/2)^n ≠ 0）。                                          *)
(* 【红线自审】零承认件；零经典逻辑；零新假设（前提位全显式证书/定理参数）；           *)
(*   语句面全 Set 值（req/le/lt/Not 均基座 Set 层别名），无紫层泄露；                 *)
(*   本件自含（不依赖 cf2 世界件），只读上游零改母本。                               *)
(* 编译配方：9.1 直调轨，unset COQLIB/ROCQLIB，全量 coqc -Q . ""（cpu_guard 包裹）。 *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSampling.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* §0 常数（half/quarter/threeq）与纯代数辅件                                    *)
(* ============================================================ *)

Definition mtw_half : Real := inv_pos (plus one one) req_two_pos.
Definition mtw_quarter : Real := mult mtw_half mtw_half.
Definition mtw_threeq : Real := req_minus one mtw_quarter.

Lemma mtw_half_pos : lt zero mtw_half.
Proof. exact (inv_pos_pos (plus one one) req_two_pos). Defined.

(* quarter + quarter == half（1/4 + 1/4 = 1/2） *)
Lemma mtw_qq_half : req (plus mtw_quarter mtw_quarter) mtw_half.
Proof. exact (req_half_twice mtw_half req_two_pos). Defined.

(* half + half == one（1/2 + 1/2 = 1） *)
Lemma mtw_hh_one : req (plus mtw_half mtw_half) one.
Proof.
  apply (req_trans (plus mtw_half mtw_half)
                   (plus (mult mtw_half one) (mult mtw_half one)) one).
  - exact (req_sym (plus (mult mtw_half one) (mult mtw_half one))
                   (plus mtw_half mtw_half)
                   (req_plus_compat (mult mtw_half one) mtw_half
                                    (mult mtw_half one) mtw_half
                                    (mult_one mtw_half) (mult_one mtw_half))).
  - exact (req_half_twice one req_two_pos).
Defined.

Lemma mtw_oo_one_zero : req (plus (opp one) one) zero.
Proof.
  exact (req_trans (plus (opp one) one) (plus one (opp one)) zero
           (plus_comm (opp one) one) (plus_opp one)).
Defined.

(* (a − b) + b == a *)
Lemma mtw_minus_plus_r : forall a b : Real, req (plus (req_minus a b) b) a.
Proof.
  intros a b. unfold req_minus.
  apply (req_trans (plus (plus a (opp b)) b) (plus a (plus (opp b) b)) a).
  - exact (req_sym (plus a (plus (opp b) b)) (plus (plus a (opp b)) b)
                   (plus_assoc a (opp b) b)).
  - apply (req_trans (plus a (plus (opp b) b)) (plus a zero) a).
    + exact (req_plus_compat a a (plus (opp b) b) zero
               (req_refl a)
               (req_trans (plus (opp b) b) (plus b (opp b)) zero
                  (plus_comm (opp b) b) (plus_opp b))).
    + exact (plus_zero a).
Defined.

(* one − half == half（1 − 1/2 = 1/2） *)
Lemma mtw_moh : req (req_minus one mtw_half) mtw_half.
Proof.
  apply (req_trans (req_minus one mtw_half)
                   (req_minus (plus mtw_half mtw_half) mtw_half) mtw_half).
  - exact (reqd_minus_compat one (plus mtw_half mtw_half) mtw_half mtw_half
             (req_sym (plus mtw_half mtw_half) one mtw_hh_one)
             (req_refl mtw_half)).
  - exact (req_minus_plus_cancel_r mtw_half mtw_half).
Defined.

(* threeq − quarter == half（3/4 − 1/4 = 1/2）——单步差分耦合系数 *)
Lemma mtw_3q_minus_q : req (req_minus mtw_threeq mtw_quarter) mtw_half.
Proof.
  apply (req_trans (req_minus mtw_threeq mtw_quarter)
                   (plus one (plus (opp mtw_quarter) (opp mtw_quarter))) mtw_half).
  - exact (req_sym (plus one (plus (opp mtw_quarter) (opp mtw_quarter)))
                   (plus (plus one (opp mtw_quarter)) (opp mtw_quarter))
                   (plus_assoc one (opp mtw_quarter) (opp mtw_quarter))).
  - apply (req_trans (plus one (plus (opp mtw_quarter) (opp mtw_quarter)))
                     (plus one (opp mtw_half)) mtw_half).
    + exact (req_plus_compat one one
               (plus (opp mtw_quarter) (opp mtw_quarter)) (opp mtw_half)
               (req_refl one)
               (req_trans (plus (opp mtw_quarter) (opp mtw_quarter))
                          (opp (plus mtw_quarter mtw_quarter)) (opp mtw_half)
                  (req_sym (opp (plus mtw_quarter mtw_quarter))
                           (plus (opp mtw_quarter) (opp mtw_quarter))
                           (req_opp_plus mtw_quarter mtw_quarter))
                  (req_opp_compat (plus mtw_quarter mtw_quarter) mtw_half
                                  mtw_qq_half))).
    + exact mtw_moh.
Defined.

(* quarter + half == threeq（1/4 + 1/2 = 3/4） *)
Lemma mtw_q_plus_h : req (plus mtw_quarter mtw_half) mtw_threeq.
Proof.
  apply (req_trans (plus mtw_quarter mtw_half)
                   (plus mtw_quarter (req_minus mtw_threeq mtw_quarter)) mtw_threeq).
  - exact (req_plus_compat mtw_quarter mtw_quarter
             mtw_half (req_minus mtw_threeq mtw_quarter)
             (req_refl mtw_quarter)
             (req_sym (req_minus mtw_threeq mtw_quarter) mtw_half mtw_3q_minus_q)).
  - exact (req_minus_plus_cancel mtw_quarter mtw_threeq).
Defined.

(* ============================================================ *)
(* §1 世界数据：bool 载体 + 硬编码对称常数核 + 迭代器 + TV 算子                    *)
(* ============================================================ *)

Definition mtw_K (s s' : bool) : Real :=
  if s then (if s' then mtw_threeq else mtw_quarter)
       else (if s' then mtw_quarter else mtw_threeq).

(* 核四参显式账：K(t,t)=3/4、K(t,f)=1/4、K(f,t)=1/4、K(f,f)=3/4 *)
Lemma mtw_K_tt : req (mtw_K true true) mtw_threeq.
Proof. exact (req_refl mtw_threeq). Defined.
Lemma mtw_K_tf : req (mtw_K true false) mtw_quarter.
Proof. exact (req_refl mtw_quarter). Defined.
Lemma mtw_K_ft : req (mtw_K false true) mtw_quarter.
Proof. exact (req_refl mtw_quarter). Defined.
Lemma mtw_K_ff : req (mtw_K false false) mtw_threeq.
Proof. exact (req_refl mtw_threeq). Defined.

Definition mtw_sumf (f : bool -> Real) : Real := plus (f true) (f false).

Definition mtw_step (mu : bool -> Real) (s' : bool) : Real :=
  plus (mult (mu true) (mtw_K true s')) (mult (mu false) (mtw_K false s')).

Fixpoint mtw_titer (n : nat) (mu : bool -> Real) : bool -> Real :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => mtw_step (mtw_titer m mu)
  end.

(* 点质量对 *)
Definition mtw_mu0 (s : bool) : Real := if s then one else zero.
Definition mtw_nu0 (s : bool) : Real := if s then zero else one.

(* TV 算子（cf2_tv 同形：(1/2)·Σ|mu−nu|） *)
Definition mtw_tv (mu nu : bool -> Real) : Real :=
  mult mtw_half (mtw_sumf (fun s : bool => abs (req_minus (mu s) (nu s)))).

(* 两列差分（差分耦合演化的主变量） *)
Definition mtw_dv (mu nu : bool -> Real) : Real := req_minus (mu true) (nu true).
Definition mtw_df (mu nu : bool -> Real) : Real := req_minus (mu false) (nu false).

Lemma mtw_mu0_mass : req (mtw_sumf mtw_mu0) one.
Proof. exact (plus_zero one). Defined.

Lemma mtw_nu0_mass : req (mtw_sumf mtw_nu0) one.
Proof. exact (req_plus_zero_l one). Defined.

(* ============================================================ *)
(* §2 Part 1a：行随机账（每行和 = one）+ 行互异账（非退化判据）                    *)
(* ============================================================ *)

Lemma mtw_row_t : req (mtw_sumf (mtw_K true)) one.
Proof. exact (mtw_minus_plus_r one mtw_quarter). Defined.

Lemma mtw_row_f : req (mtw_sumf (mtw_K false)) one.
Proof.
  apply (req_trans (mtw_sumf (mtw_K false))
                   (plus mtw_threeq mtw_quarter) one).
  - exact (plus_comm mtw_quarter mtw_threeq).
  - exact mtw_row_t.
Defined.

(* 行互异：第 true 列 3/4 ≠ 1/4——与 AID 的核行全同病灶正面对照 *)
Lemma mtw_rows_ne : Not (req mtw_threeq mtw_quarter).
Proof.
  intro H.
  assert (Hq1 : req (plus mtw_quarter mtw_quarter) one).
  { apply (req_trans (plus mtw_quarter mtw_quarter)
                     (plus mtw_threeq mtw_quarter) one).
    - exact (req_sym (plus mtw_threeq mtw_quarter) (plus mtw_quarter mtw_quarter)
               (req_plus_compat mtw_threeq mtw_quarter mtw_quarter mtw_quarter
                  H (req_refl mtw_quarter))).
    - exact mtw_row_t. }
  assert (Hho : req mtw_half one).
  { apply (req_trans mtw_half (plus mtw_quarter mtw_quarter) one).
    - exact (req_sym (plus mtw_quarter mtw_quarter) mtw_half mtw_qq_half).
    - exact Hq1. }
  assert (H33 : req (plus one one) one).
  { apply (req_trans (plus one one) (plus mtw_half mtw_half) one).
    - exact (req_plus_compat one mtw_half one mtw_half
               (req_sym mtw_half one Hho) (req_sym mtw_half one Hho)).
    - exact mtw_hh_one. }
  apply (req_one_neq_zero).
  exact (req_plus_cancel_l one one zero
           (req_trans (plus one one) one (plus one zero) H33
              (req_sym (plus one zero) one (plus_zero one)))).
Defined.

(* ============================================================ *)
(* §3 幂的正性（几何衰减基准 (1/2)^n > 0）                                       *)
(* ============================================================ *)

Lemma mtw_rpow_pos : forall n : nat, lt zero (req_r_pow mtw_half n).
Proof.
  intro n. induction n as [| n IH].
  - exact one_pos.
  - exact (mult_positive mtw_half (req_r_pow mtw_half n) mtw_half_pos IH).
Defined.

(* ============================================================ *)
(* §4 差分耦合机器：质量守恒 → 补元 → df = −dv → dv 单步半缩                       *)
(* ============================================================ *)

(* 质量守恒：行随机核保持总质量（自含归纳，对任意分布 mu） *)
Lemma mtw_mass_iter : forall (n : nat) (mu : bool -> Real),
  req (mtw_sumf mu) one -> req (mtw_sumf (mtw_titer n mu)) one.
Proof.
  intro n. induction n as [| n IH]; intros mu Hm.
  - exact Hm.
  - unfold mtw_sumf in *; unfold mtw_step.
    apply (req_trans
             (plus (plus (mult (mtw_titer n mu true) (mtw_K true true))
                         (mult (mtw_titer n mu false) (mtw_K false true)))
                   (plus (mult (mtw_titer n mu true) (mtw_K true false))
                         (mult (mtw_titer n mu false) (mtw_K false false))))
             (plus (plus (mult (mtw_titer n mu true) (mtw_K true true))
                         (mult (mtw_titer n mu true) (mtw_K true false)))
                   (plus (mult (mtw_titer n mu false) (mtw_K false true))
                         (mult (mtw_titer n mu false) (mtw_K false false))))
             one).
    + exact (req_plus_swap_mid
               (mult (mtw_titer n mu true) (mtw_K true true))
               (mult (mtw_titer n mu false) (mtw_K false true))
               (mult (mtw_titer n mu true) (mtw_K true false))
               (mult (mtw_titer n mu false) (mtw_K false false))).
    + apply (req_trans
               (plus (plus (mult (mtw_titer n mu true) (mtw_K true true))
                           (mult (mtw_titer n mu true) (mtw_K true false)))
                     (plus (mult (mtw_titer n mu false) (mtw_K false true))
                           (mult (mtw_titer n mu false) (mtw_K false false))))
               (plus (mult (mtw_titer n mu true) (plus (mtw_K true true) (mtw_K true false)))
                     (mult (mtw_titer n mu false) (plus (mtw_K false true) (mtw_K false false))))
               one).
      * exact (req_plus_compat
                 (plus (mult (mtw_titer n mu true) (mtw_K true true))
                       (mult (mtw_titer n mu true) (mtw_K true false)))
                 (mult (mtw_titer n mu true) (plus (mtw_K true true) (mtw_K true false)))
                 (plus (mult (mtw_titer n mu false) (mtw_K false true))
                       (mult (mtw_titer n mu false) (mtw_K false false)))
                 (mult (mtw_titer n mu false) (plus (mtw_K false true) (mtw_K false false)))
                 (req_sym (mult (mtw_titer n mu true) (plus (mtw_K true true) (mtw_K true false)))
                          (plus (mult (mtw_titer n mu true) (mtw_K true true))
                                (mult (mtw_titer n mu true) (mtw_K true false)))
                          (distrib (mtw_titer n mu true) (mtw_K true true) (mtw_K true false)))
                 (req_sym (mult (mtw_titer n mu false) (plus (mtw_K false true) (mtw_K false false)))
                          (plus (mult (mtw_titer n mu false) (mtw_K false true))
                                (mult (mtw_titer n mu false) (mtw_K false false)))
                          (distrib (mtw_titer n mu false) (mtw_K false true) (mtw_K false false)))).
      * apply (req_trans
                 (plus (mult (mtw_titer n mu true) (plus (mtw_K true true) (mtw_K true false)))
                       (mult (mtw_titer n mu false) (plus (mtw_K false true) (mtw_K false false))))
                 (plus (mult (mtw_titer n mu true) one) (mult (mtw_titer n mu false) one))
                 one).
        -- exact (req_plus_compat
                    (mult (mtw_titer n mu true) (plus (mtw_K true true) (mtw_K true false)))
                    (mult (mtw_titer n mu true) one)
                    (mult (mtw_titer n mu false) (plus (mtw_K false true) (mtw_K false false)))
                    (mult (mtw_titer n mu false) one)
                    (req_mult_compat (mtw_titer n mu true) (mtw_titer n mu true)
                                     (plus (mtw_K true true) (mtw_K true false)) one
                                     (req_refl (mtw_titer n mu true)) mtw_row_t)
                    (req_mult_compat (mtw_titer n mu false) (mtw_titer n mu false)
                                     (plus (mtw_K false true) (mtw_K false false)) one
                                     (req_refl (mtw_titer n mu false)) mtw_row_f)).
        -- apply (req_trans (plus (mult (mtw_titer n mu true) one) (mult (mtw_titer n mu false) one))
                            (plus (mtw_titer n mu true) (mtw_titer n mu false)) one).
           ++ exact (req_plus_compat (mult (mtw_titer n mu true) one) (mtw_titer n mu true)
                                       (mult (mtw_titer n mu false) one) (mtw_titer n mu false)
                                       (mult_one (mtw_titer n mu true))
                                       (mult_one (mtw_titer n mu false))).
           ++ exact (IH mu Hm).
Defined.

(* 补元提取：总质量 one 的二列分布，第二列 == one − 第一列 *)
Lemma mtw_compl : forall mu : bool -> Real,
  req (mtw_sumf mu) one -> req (mu false) (req_minus one (mu true)).
Proof.
  intros mu Hm. unfold mtw_sumf in Hm.
  assert (Hbase : req (plus (opp one) (plus (mu true) (mu false))) zero).
  { exact (req_trans (plus (opp one) (plus (mu true) (mu false)))
                     (plus (opp one) one) zero
             (req_plus_compat (opp one) (opp one)
                (plus (mu true) (mu false)) one (req_refl (opp one)) Hm)
             mtw_oo_one_zero). }
  assert (Ha : req (plus (plus (opp one) (mu true)) (mu false)) zero).
  { exact (req_trans (plus (plus (opp one) (mu true)) (mu false))
                     (plus (opp one) (plus (mu true) (mu false))) zero
             (req_sym (plus (opp one) (plus (mu true) (mu false)))
                      (plus (plus (opp one) (mu true)) (mu false))
                      (plus_assoc (opp one) (mu true) (mu false)))
             Hbase). }
  assert (Hc : req (plus (plus (opp one) (mu true)) (req_minus one (mu true))) zero).
  { exact (req_trans (plus (plus (opp one) (mu true)) (req_minus one (mu true)))
                     (plus (plus (opp one) one) (plus (mu true) (opp (mu true)))) zero
             (req_plus_swap_mid (opp one) (mu true) one (opp (mu true)))
             (req_trans (plus (plus (opp one) one) (plus (mu true) (opp (mu true))))
                        (plus zero zero) zero
                (req_plus_compat (plus (opp one) one) zero
                   (plus (mu true) (opp (mu true))) zero
                   mtw_oo_one_zero (plus_opp (mu true)))
                (plus_zero zero))). }
  exact (req_plus_inv_unique (plus (opp one) (mu true)) (mu false)
           (req_minus one (mu true)) Ha Hc).
Defined.

(* 差分镜像：第二列差 == −第一列差（质量守恒 + 补元的推论，零归纳） *)
Lemma mtw_df_opp_dv : forall n : nat,
  req (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
      (opp (mtw_dv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))).
Proof.
  intro n.
  assert (HX : req ((mtw_titer n mtw_mu0) false)
                   (req_minus one ((mtw_titer n mtw_mu0) true))).
  { exact (mtw_compl (mtw_titer n mtw_mu0) (mtw_mass_iter n mtw_mu0 mtw_mu0_mass)). }
  assert (HY : req ((mtw_titer n mtw_nu0) false)
                   (req_minus one ((mtw_titer n mtw_nu0) true))).
  { exact (mtw_compl (mtw_titer n mtw_nu0) (mtw_mass_iter n mtw_nu0 mtw_nu0_mass)). }
  apply (req_trans (req_minus ((mtw_titer n mtw_mu0) false) ((mtw_titer n mtw_nu0) false))
                   (req_minus (req_minus one ((mtw_titer n mtw_mu0) true))
                              (req_minus one ((mtw_titer n mtw_nu0) true)))
                   (opp (req_minus ((mtw_titer n mtw_mu0) true)
                                   ((mtw_titer n mtw_nu0) true)))).
  - exact (reqd_minus_compat ((mtw_titer n mtw_mu0) false)
             (req_minus one ((mtw_titer n mtw_mu0) true))
             ((mtw_titer n mtw_nu0) false)
             (req_minus one ((mtw_titer n mtw_nu0) true)) HX HY).
  - apply (req_trans (req_minus (req_minus one ((mtw_titer n mtw_mu0) true))
                                (req_minus one ((mtw_titer n mtw_nu0) true)))
                     (req_minus (opp ((mtw_titer n mtw_mu0) true))
                                (opp ((mtw_titer n mtw_nu0) true)))
                     (opp (req_minus ((mtw_titer n mtw_mu0) true)
                                     ((mtw_titer n mtw_nu0) true)))).
    + exact (req_minus_plus_congr_l one (opp ((mtw_titer n mtw_mu0) true))
               (opp ((mtw_titer n mtw_nu0) true))).
    + apply (req_trans (req_minus (opp ((mtw_titer n mtw_mu0) true))
                                  (opp ((mtw_titer n mtw_nu0) true)))
                       (plus (opp ((mtw_titer n mtw_mu0) true))
                             ((mtw_titer n mtw_nu0) true))
                       (opp (req_minus ((mtw_titer n mtw_mu0) true)
                                       ((mtw_titer n mtw_nu0) true)))).
      * exact (req_plus_compat (opp ((mtw_titer n mtw_mu0) true))
                  (opp ((mtw_titer n mtw_mu0) true))
                  (opp (opp ((mtw_titer n mtw_nu0) true)))
                  ((mtw_titer n mtw_nu0) true)
                  (req_refl (opp ((mtw_titer n mtw_mu0) true)))
                  (req_double_neg ((mtw_titer n mtw_nu0) true))).
      * exact (req_sym (opp (req_minus ((mtw_titer n mtw_mu0) true)
                                       ((mtw_titer n mtw_nu0) true)))
                       (plus (opp ((mtw_titer n mtw_mu0) true))
                             ((mtw_titer n mtw_nu0) true))
                       (req_opp_minus ((mtw_titer n mtw_mu0) true)
                                      ((mtw_titer n mtw_nu0) true))).
Defined.

(* 单步差分耦合（泛型）：dv 走核第 true 列的行差系数、df 走第 false 列的 *)
Lemma mtw_dv_step_gen : forall x y : bool -> Real,
  req (mtw_dv (mtw_step x) (mtw_step y))
      (plus (mult (mtw_dv x y) (mtw_K true true))
            (mult (mtw_df x y) (mtw_K false true))).
Proof.
  intros x y. unfold mtw_dv, mtw_df, mtw_step.
  apply (req_trans
           (req_minus (plus (mult (x true) (mtw_K true true))
                            (mult (x false) (mtw_K false true)))
                      (plus (mult (y true) (mtw_K true true))
                            (mult (y false) (mtw_K false true))))
           (plus (req_minus (mult (x true) (mtw_K true true))
                            (mult (y true) (mtw_K true true)))
                 (req_minus (mult (x false) (mtw_K false true))
                            (mult (y false) (mtw_K false true))))
           (plus (mult (req_minus (x true) (y true)) (mtw_K true true))
                 (mult (req_minus (x false) (y false)) (mtw_K false true)))).
  - exact (req_minus_plus_distr (mult (x true) (mtw_K true true))
             (mult (x false) (mtw_K false true))
             (mult (y true) (mtw_K true true))
             (mult (y false) (mtw_K false true))).
  - exact (req_plus_compat
             (req_minus (mult (x true) (mtw_K true true))
                        (mult (y true) (mtw_K true true)))
             (mult (req_minus (x true) (y true)) (mtw_K true true))
             (req_minus (mult (x false) (mtw_K false true))
                        (mult (y false) (mtw_K false true)))
             (mult (req_minus (x false) (y false)) (mtw_K false true))
             (req_minus_factor_pt (x true) (y true) (mtw_K true true))
             (req_minus_factor_pt (x false) (y false) (mtw_K false true))).
Defined.

(* 常数尾件：h·(3/4) − h·(1/4) == h·(1/2) == (1/2)·h *)
Lemma mtw_h_3q_q_half : forall h : Real,
  req (plus (mult h mtw_threeq) (opp (mult h mtw_quarter))) (mult mtw_half h).
Proof.
  intro h.
  apply (req_trans (plus (mult h mtw_threeq) (opp (mult h mtw_quarter)))
                   (mult h (req_minus mtw_threeq mtw_quarter)) (mult mtw_half h)).
  - exact (req_sym (mult h (req_minus mtw_threeq mtw_quarter))
                   (req_minus (mult h mtw_threeq) (mult h mtw_quarter))
                   (req_mult_minus_distr_l h mtw_threeq mtw_quarter)).
  - apply (req_trans (mult h (req_minus mtw_threeq mtw_quarter))
                     (mult h mtw_half) (mult mtw_half h)).
    + exact (req_mult_compat h h (req_minus mtw_threeq mtw_quarter) mtw_half
               (req_refl h) mtw_3q_minus_q).
    + exact (mult_comm h mtw_half).
Defined.

(* 主归纳：dv(n) == (1/2)^n（单步差分耦合 + 镜像，全显式） *)
Lemma mtw_dv_iter : forall n : nat,
  req (mtw_dv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
      (req_r_pow mtw_half n).
Proof.
  intro n. induction n as [| n IH].
  - exact (req_trans (plus one (opp zero)) (plus one zero) one
             (req_plus_compat one one (opp zero) zero
                (req_refl one) reqd_opp_zero)
             (plus_zero one)).
  - assert (Hdf : req (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                      (opp (req_r_pow mtw_half n))).
    { exact (req_trans (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                       (opp (mtw_dv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)))
                       (opp (req_r_pow mtw_half n))
               (mtw_df_opp_dv n)
               (req_opp_compat (mtw_dv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                               (req_r_pow mtw_half n) IH)). }
    apply (req_trans
             (mtw_dv (mtw_titer (Datatypes.S n) mtw_mu0)
                     (mtw_titer (Datatypes.S n) mtw_nu0))
             (plus (mult (mtw_dv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                         (mtw_K true true))
                   (mult (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                         (mtw_K false true)))
             (req_r_pow mtw_half (Datatypes.S n))).
    + exact (mtw_dv_step_gen (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)).
    + apply (req_trans
               (plus (mult (mtw_dv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                           (mtw_K true true))
                     (mult (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                           (mtw_K false true)))
               (plus (mult (req_r_pow mtw_half n) mtw_threeq)
                     (opp (mult (req_r_pow mtw_half n) mtw_quarter)))
               (req_r_pow mtw_half (Datatypes.S n))).
      * exact (req_plus_compat
                 (mult (mtw_dv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                       (mtw_K true true))
                 (mult (req_r_pow mtw_half n) mtw_threeq)
                 (mult (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                       (mtw_K false true))
                 (opp (mult (req_r_pow mtw_half n) mtw_quarter))
                 (req_mult_compat (mtw_dv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                                  (req_r_pow mtw_half n) mtw_threeq mtw_threeq
                                  IH (req_refl mtw_threeq))
                 (req_trans (mult (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)) mtw_quarter)
                            (mult (opp (req_r_pow mtw_half n)) mtw_quarter)
                            (opp (mult (req_r_pow mtw_half n) mtw_quarter))
                            (req_mult_compat (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                                             (opp (req_r_pow mtw_half n)) mtw_quarter mtw_quarter
                                             Hdf (req_refl mtw_quarter))
                            (req_opp_mult_r (req_r_pow mtw_half n) mtw_quarter))).
      * apply (req_trans
                 (plus (mult (req_r_pow mtw_half n) mtw_threeq)
                       (opp (mult (req_r_pow mtw_half n) mtw_quarter)))
                 (plus (mult (req_r_pow mtw_half n) mtw_threeq)
                       (opp (mult (req_r_pow mtw_half n) mtw_quarter)))
                 (req_r_pow mtw_half (Datatypes.S n))).
        -- exact (req_refl (plus (mult (req_r_pow mtw_half n) mtw_threeq)
                                 (opp (mult (req_r_pow mtw_half n) mtw_quarter)))).
        -- exact (mtw_h_3q_q_half (req_r_pow mtw_half n)).
Defined.

Lemma mtw_df_iter : forall n : nat,
  req (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
      (opp (req_r_pow mtw_half n)).
Proof.
  intro n.
  exact (req_trans (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                   (opp (mtw_dv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)))
                   (opp (req_r_pow mtw_half n))
          (mtw_df_opp_dv n)
          (req_opp_compat (mtw_dv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                          (req_r_pow mtw_half n) (mtw_dv_iter n))).
Defined.

(* ============================================================ *)
(* §5 Part 1b+2+3：TV₀ 正性 · 精确迭代 · 步恒等 · 下界                            *)
(* ============================================================ *)

(* TV₀ == one（点质量对） *)
Lemma mtw_tv0_one : req (mtw_tv mtw_mu0 mtw_nu0) one.
Proof.
  assert (Ha1 : req (abs (req_minus (mtw_mu0 true) (mtw_nu0 true))) one).
  { exact (req_trans (abs (req_minus one zero)) (abs one) one
             (req_abs_compat (req_minus one zero) one
                (req_trans (plus one (opp zero)) (plus one zero) one
                   (req_plus_compat one one (opp zero) zero
                      (req_refl one) reqd_opp_zero)
                   (plus_zero one)))
             (abs_pos one one_pos)). }
  assert (Ha2 : req (abs (req_minus (mtw_mu0 false) (mtw_nu0 false))) one).
  { exact (req_trans (abs (req_minus zero one)) (abs (opp one)) one
             (req_trans (abs (req_minus zero one)) (abs (opp one)) (abs one)
                (req_abs_compat (req_minus zero one) (opp one)
                   (req_plus_zero_l (opp one)))
                (abs_opp one))
             (abs_pos one one_pos)). }
  apply (req_trans (mtw_tv mtw_mu0 mtw_nu0)
                   (mult mtw_half (plus one one)) one).
  - exact (req_mult_compat mtw_half mtw_half
             (mtw_sumf (fun s : bool => abs (req_minus (mtw_mu0 s) (mtw_nu0 s))))
             (plus one one)
             (req_refl mtw_half)
             (req_plus_compat (abs (req_minus (mtw_mu0 true) (mtw_nu0 true))) one
                              (abs (req_minus (mtw_mu0 false) (mtw_nu0 false))) one
                              Ha1 Ha2)).
  - exact (req_trans (mult mtw_half (plus one one))
                     (mult (plus one one) mtw_half) one
             (mult_comm mtw_half (plus one one))
             (inv_pos_correct (plus one one) req_two_pos)).
Defined.

(* Part 1c：TV₀ 严格正（非退化判据之电视面） *)
Lemma mtw_tv0_pos : lt zero (mtw_tv mtw_mu0 mtw_nu0).
Proof.
  exact (lt_id_r zero one (mtw_tv mtw_mu0 mtw_nu0)
           (req_sym (mtw_tv mtw_mu0 mtw_nu0) one mtw_tv0_one) one_pos).
Defined.

(* TV(n) == (1/2)^n（精确迭代主账） *)
Lemma mtw_tv_iter_rpow : forall n : nat,
  req (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
      (req_r_pow mtw_half n).
Proof.
  intro n.
  assert (Hdv : req (mtw_dv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                    (req_r_pow mtw_half n)).
  { exact (mtw_dv_iter n). }
  assert (Hdf : req (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                    (opp (req_r_pow mtw_half n))).
  { exact (mtw_df_iter n). }
  assert (Ha1 : req (abs (mtw_dv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)))
                    (req_r_pow mtw_half n)).
  { exact (req_trans (abs (mtw_dv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)))
                     (abs (req_r_pow mtw_half n)) (req_r_pow mtw_half n)
             (req_abs_compat (mtw_dv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                             (req_r_pow mtw_half n) Hdv)
             (abs_pos (req_r_pow mtw_half n) (mtw_rpow_pos n))). }
  assert (Ha2 : req (abs (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)))
                    (req_r_pow mtw_half n)).
  { exact (req_trans (abs (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)))
                     (abs (req_r_pow mtw_half n)) (req_r_pow mtw_half n)
             (req_trans (abs (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)))
                        (abs (opp (req_r_pow mtw_half n)))
                        (abs (req_r_pow mtw_half n))
                (req_abs_compat (mtw_df (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                                (opp (req_r_pow mtw_half n)) Hdf)
                (abs_opp (req_r_pow mtw_half n)))
             (abs_pos (req_r_pow mtw_half n) (mtw_rpow_pos n))). }
  apply (req_trans (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                   (mult mtw_half (plus (req_r_pow mtw_half n) (req_r_pow mtw_half n)))
                   (req_r_pow mtw_half n)).
  - exact (req_mult_compat mtw_half mtw_half
             (mtw_sumf (fun s : bool =>
                   abs (req_minus (mtw_titer n mtw_mu0 s) (mtw_titer n mtw_nu0 s))))
             (plus (req_r_pow mtw_half n) (req_r_pow mtw_half n))
             (req_refl mtw_half)
             (req_plus_compat
                (abs (req_minus (mtw_titer n mtw_mu0 true) (mtw_titer n mtw_nu0 true)))
                (req_r_pow mtw_half n)
                (abs (req_minus (mtw_titer n mtw_mu0 false) (mtw_titer n mtw_nu0 false)))
                (req_r_pow mtw_half n) Ha1 Ha2)).
  - apply (req_trans
             (mult mtw_half (plus (req_r_pow mtw_half n) (req_r_pow mtw_half n)))
             (mult mtw_half (mult (plus one one) (req_r_pow mtw_half n)))
             (req_r_pow mtw_half n)).
    + exact (req_mult_compat mtw_half mtw_half
               (plus (req_r_pow mtw_half n) (req_r_pow mtw_half n))
               (mult (plus one one) (req_r_pow mtw_half n))
               (req_refl mtw_half)
               (req_sym (mult (plus one one) (req_r_pow mtw_half n))
                        (plus (req_r_pow mtw_half n) (req_r_pow mtw_half n))
                        (req_two_mult (req_r_pow mtw_half n)))).
    + apply (req_trans
               (mult mtw_half (mult (plus one one) (req_r_pow mtw_half n)))
               (mult (mult mtw_half (plus one one)) (req_r_pow mtw_half n))
               (req_r_pow mtw_half n)).
      * exact (mult_assoc mtw_half (plus one one) (req_r_pow mtw_half n)).
      * apply (req_trans
                 (mult (mult mtw_half (plus one one)) (req_r_pow mtw_half n))
                 (mult one (req_r_pow mtw_half n))
                 (req_r_pow mtw_half n)).
        -- exact (req_mult_compat (mult mtw_half (plus one one)) one
                     (req_r_pow mtw_half n) (req_r_pow mtw_half n)
                     (req_trans (mult mtw_half (plus one one))
                                (mult (plus one one) mtw_half) one
                                (mult_comm mtw_half (plus one one))
                                (inv_pos_correct (plus one one) req_two_pos))
                     (req_refl (req_r_pow mtw_half n))).
        -- exact (req_mult_one_l (req_r_pow mtw_half n)).
Defined.

(* Part 3 甲：TV(n) == (1/2)^n · TV₀（AID 的 mtl_tv_lower 同形在此世界为真之精确版） *)
Theorem mtw_tv_exact_iter : forall n : nat,
  req (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
      (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0)).
Proof.
  intro n.
  apply (req_trans (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                   (req_r_pow mtw_half n)
                   (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0))).
  - exact (mtw_tv_iter_rpow n).
  - apply (req_trans (req_r_pow mtw_half n)
                     (mult (req_r_pow mtw_half n) one)
                     (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0))).
    + exact (req_sym (mult (req_r_pow mtw_half n) one) (req_r_pow mtw_half n)
               (mult_one (req_r_pow mtw_half n))).
    + exact (req_mult_compat (req_r_pow mtw_half n) (req_r_pow mtw_half n)
               one (mtw_tv mtw_mu0 mtw_nu0)
               (req_refl (req_r_pow mtw_half n))
               (req_sym (mtw_tv mtw_mu0 mtw_nu0) one mtw_tv0_one)).
Defined.

(* Part 2：TV(S n) == (1/2)·TV(n)（步恒等——(1/2)^n 幂律的定义级一步） *)
Theorem mtw_tv_step_exact : forall n : nat,
  req (mtw_tv (mtw_titer (Datatypes.S n) mtw_mu0) (mtw_titer (Datatypes.S n) mtw_nu0))
      (mult mtw_half (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))).
Proof.
  intro n.
  apply (req_trans
           (mtw_tv (mtw_titer (Datatypes.S n) mtw_mu0)
                   (mtw_titer (Datatypes.S n) mtw_nu0))
           (mult (mult mtw_half (req_r_pow mtw_half n)) (mtw_tv mtw_mu0 mtw_nu0))
           (mult mtw_half (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)))).
  - exact (mtw_tv_exact_iter (Datatypes.S n)).
  - apply (req_trans
             (mult (mult mtw_half (req_r_pow mtw_half n)) (mtw_tv mtw_mu0 mtw_nu0))
             (mult mtw_half (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0)))
             (mult mtw_half (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)))).
    + exact (req_sym
               (mult mtw_half (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0)))
               (mult (mult mtw_half (req_r_pow mtw_half n)) (mtw_tv mtw_mu0 mtw_nu0))
               (mult_assoc mtw_half (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0))).
    + exact (req_mult_compat mtw_half mtw_half
               (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0))
               (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
               (req_refl mtw_half)
               (req_sym (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                        (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0))
                        (mtw_tv_exact_iter n))).
Defined.

(* Part 3 乙：混合时间下界（AID 的 mtl_no_mixing_refuted 同形语句在此世界为真）：
   预算 B 严格小于 (1/2)^n·TV₀ 则 B 严格小于 TV(n)——未混合窗下界成立。 *)
Theorem mtw_no_mixing_below : forall (n : nat) (B : Real),
  lt B (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0)) ->
  lt B (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)).
Proof.
  intros n B H.
  exact (lt_id_r B (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0))
                  (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
          (req_sym (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                   (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0))
                   (mtw_tv_exact_iter n)) H).
Defined.

(* 跨世界对照正件：le ((1/2)^n·TV₀) (TV(n))（AID 的 mtl_refute_lower 同形语句
   在此世界为真——精确等值经 le 的 req 支直供，零 Or 分裂） *)
Theorem mtw_tv_lower : forall n : nat,
  le (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0))
     (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)).
Proof.
  intro n.
  exact (lt_le_iff (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0))
                   (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                   (inr (req_sym (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
                                 (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0))
                                 (mtw_tv_exact_iter n)))).
Defined.

(* ============================================================ *)
(* §6 Part 4（量力）：率常数与 minorization 常数证书                              *)
(*   率常数 omd := 1/2（= 第二特征值 = TV 收缩率，与 cf2 的 omd:=1−δ* 解耦）；      *)
(*   minorization 常数 ds := 1/4（= 核最小元）。正性证书全 Q 可判定。              *)
(* ============================================================ *)

Definition mtw_omd : Real := mtw_half.
Definition mtw_ds : Real := mtw_quarter.

Lemma mtw_omd_pos : lt zero mtw_omd.
Proof. exact mtw_half_pos. Defined.

Lemma mtw_ds_pos : lt zero mtw_ds.
Proof. exact (mult_positive mtw_half mtw_half mtw_half_pos mtw_half_pos). Defined.

(* ============================================================ *)
(* 四关自检：全件 Closed（零新假设）                                             *)
(* ============================================================ *)

Print Assumptions mtw_half_pos.
Print Assumptions mtw_qq_half.
Print Assumptions mtw_hh_one.
Print Assumptions mtw_minus_plus_r.
Print Assumptions mtw_moh.
Print Assumptions mtw_3q_minus_q.
Print Assumptions mtw_q_plus_h.
Print Assumptions mtw_K_tt.
Print Assumptions mtw_K_tf.
Print Assumptions mtw_K_ft.
Print Assumptions mtw_K_ff.
Print Assumptions mtw_mu0_mass.
Print Assumptions mtw_nu0_mass.
Print Assumptions mtw_row_t.
Print Assumptions mtw_row_f.
Print Assumptions mtw_rows_ne.
Print Assumptions mtw_rpow_pos.
Print Assumptions mtw_mass_iter.
Print Assumptions mtw_compl.
Print Assumptions mtw_df_opp_dv.
Print Assumptions mtw_dv_step_gen.
Print Assumptions mtw_h_3q_q_half.
Print Assumptions mtw_dv_iter.
Print Assumptions mtw_df_iter.
Print Assumptions mtw_tv0_one.
Print Assumptions mtw_tv0_pos.
Print Assumptions mtw_tv_iter_rpow.
Print Assumptions mtw_tv_exact_iter.
Print Assumptions mtw_tv_step_exact.
Print Assumptions mtw_no_mixing_below.
Print Assumptions mtw_tv_lower.
Print Assumptions mtw_omd_pos.
Print Assumptions mtw_ds_pos.
