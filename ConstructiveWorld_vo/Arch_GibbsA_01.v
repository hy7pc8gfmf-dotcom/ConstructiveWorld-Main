(* ==========================================================================)
   Arch_GibbsA_01.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：gK、gdst、gomd、pi_boltzmann、ga_pi_boltzmann_norm、ga_boltzmann_fixed、ga_titer_fixed、ga_attractor_contraction、ga2_rt。
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
Require Import UpTVDoeblin.
Require Import UpReqSteadyThermo.
Require Import UpReqAlgebra.
Require Import UpReqAlign2.

(* ================= §1 gK 族 ================= *)
(* Section GibbsAttr：离散状态世界 + Gibbs 核 + Boltzmann 载体        *)
(* （A 件 TVDStar 变量面 + B 件 RealThermoSteady 载体槽，两桥并轨）   *)
Section GibbsAttr.

(* ---- A 件（UpTVDoeblin TVDStar）变量面 ---- *)
Variable states : list (list Real).
Variable n_pos : real_lt real_zero (real_of_nat (length states)).
Variable Ttemp : Real.
Variable Ttemp_pos : real_lt real_zero Ttemp.
Variable gamma : Real.
Variable gamma_pos : real_lt real_zero gamma.
Variable z : list Real -> list Real -> Real.
Variable z_lo : forall i j : list Real, real_le (real_opp gamma) (z i j).
Variable z_hi : forall i j : list Real, real_le (z i j) gamma.

(* 诚实接口（A 件同位前提）：|Σf| ≤ Σ|f|（list 版） *)
Variable Labs : forall f : list Real -> Real,
  real_le (real_abs (real_list_sum (list Real) f states))
          (real_list_sum (list Real) (fun w : list Real => real_abs (f w)) states).

(* ---- Gibbs 核（A 件 tvd_K 实例）与显式率（tvd_dstar 实例）---- *)
Definition gK (i j : list Real) : Real :=
  tvd_K states n_pos Ttemp Ttemp_pos z i j.
Definition gdst : Real := tvd_dstar Ttemp Ttemp_pos gamma.
Definition gomd : Real := tv_omd (tvd_dstar Ttemp Ttemp_pos gamma).

(* ---- B 件（UpReqSteadyThermo RealThermoSteady）载体槽 ---- *)
Variable energy : list Real -> Real.
Variable Dcap : Real.
Variable Dcap_pos : real_lt real_zero Dcap.
Variable Zr : Real.
Variable Zr_pos : real_lt real_zero Zr.

(* Boltzmann 分布（B 件载体实例化到 list Real 枚举世界） *)
Definition pi_boltzmann : list Real -> Real :=
  real_boltzmann_prob (list Real) energy Dcap Dcap_pos Zr Zr_pos.

(* 诚实接口（B 件同位前提一）：partition 条件
   Z == Σ e^{−E/T}（real_partition_condition 的枚举和实例形） *)
Variable part_cond : real_eq Zr
  (real_list_sum (list Real)
     (fun s : list Real =>
        real_exp_neg (real_mult (real_inv_pos Dcap Dcap_pos) (energy s)))
     states).

(* 诚实接口（B 件同位前提二）：detailed balance（核 = Gibbs 核 gK）
   π(s)·K(s,s') == π(s')·K(s',s)（real_detailed_balance 实例形） *)
Variable dbalance : forall s s' : list Real,
  real_eq (real_mult (pi_boltzmann s) (gK s s'))
          (real_mult (pi_boltzmann s') (gK s' s)).

(* ① π 是分布：Σπ == 1（partition 条件实例化消解；B 件归一化闭合件）       *)
Lemma ga_pi_boltzmann_norm :
  real_eq (real_list_sum (list Real) pi_boltzmann states) real_one.
Proof.
  apply (real_eq_trans
           (real_list_sum (list Real) pi_boltzmann states)
           (real_mult (real_inv_pos Zr Zr_pos)
              (real_list_sum (list Real)
                 (fun s : list Real =>
                    real_exp_neg
                      (real_mult (real_inv_pos Dcap Dcap_pos) (energy s)))
                 states))
           real_one).
  - (* Σ(inv Z·unnorm) == inv Z·Σ unnorm（real_list_sum_linear；
       LHS 与 Σπ 定义等价——pi_boltzmann 逐点即该乘积项） *)
    exact (real_list_sum_linear (list Real) (real_inv_pos Zr Zr_pos)
             (fun s : list Real =>
                real_exp_neg (real_mult (real_inv_pos Dcap Dcap_pos) (energy s)))
             states).
  - apply (real_eq_trans
             (real_mult (real_inv_pos Zr Zr_pos)
                (real_list_sum (list Real)
                   (fun s : list Real =>
                      real_exp_neg
                        (real_mult (real_inv_pos Dcap Dcap_pos) (energy s)))
                   states))
             (real_mult (real_inv_pos Zr Zr_pos) Zr)
             real_one).
    + apply (RealSetoid.real_eq_mult_compat
               (real_inv_pos Zr Zr_pos)
               (real_list_sum (list Real)
                  (fun s : list Real =>
                     real_exp_neg
                       (real_mult (real_inv_pos Dcap Dcap_pos) (energy s)))
                  states)
               (real_inv_pos Zr Zr_pos) Zr
               (real_eq_refl (real_inv_pos Zr Zr_pos))
               (real_eq_sym _ _ part_cond)).
    + apply (real_eq_trans
               (real_mult (real_inv_pos Zr Zr_pos) Zr)
               (real_mult Zr (real_inv_pos Zr Zr_pos))
               real_one).
      * exact (real_mult_comm (real_inv_pos Zr Zr_pos) Zr).
      * exact (real_inv_pos_correct Zr Zr_pos).
Qed.

(* ② 小连接件：B 件稳态五步链本载体重演 ⟹ π 是 tv_step 不动点        *)
(*   Σ_{s'} π(s')·K(s',s) == π(s)（逐点）——即 A 件迭代器的不动点形。  *)
Theorem ga_boltzmann_fixed : forall s : list Real,
  real_eq (tv_step states gK pi_boltzmann s) (pi_boltzmann s).
Proof.
  intro s.
  unfold tv_step.
  (* 段①：逐点 detailed balance 换轴（实参序 (w s)，B 件绑定序纪律） *)
  assert (Hdb : forall w : list Real,
           real_eq (real_mult (pi_boltzmann w) (gK w s))
                   (real_mult (pi_boltzmann s) (gK s w))).
  { intro w. exact (dbalance w s). }
  (* 段②：求和外延壳（real_list_sum_ext 迁移段①逐点形） *)
  assert (Hext : real_eq
           (real_list_sum (list Real)
              (fun w : list Real => real_mult (pi_boltzmann w) (gK w s)) states)
           (real_list_sum (list Real)
              (fun w : list Real => real_mult (pi_boltzmann s) (gK s w)) states)).
  { exact (real_list_sum_ext (list Real)
             (fun w : list Real => real_mult (pi_boltzmann w) (gK w s))
             (fun w : list Real => real_mult (pi_boltzmann s) (gK s w))
             states Hdb). }
  (* 段③：线性提取 π(s)（real_list_sum_linear） *)
  assert (Hlin : real_eq
           (real_list_sum (list Real)
              (fun w : list Real => real_mult (pi_boltzmann s) (gK s w)) states)
           (real_mult (pi_boltzmann s)
              (real_list_sum (list Real) (fun w : list Real => gK s w) states))).
  { exact (real_list_sum_linear (list Real) (pi_boltzmann s)
             (fun w : list Real => gK s w) states). }
  (* 段④：核行归一化（tvd_K_row 于 gK 行形，delta/eta 换形直取） *)
  assert (Hnorm : real_eq
           (real_list_sum (list Real) (fun w : list Real => gK s w) states)
           real_one).
  { exact (tvd_K_row states n_pos Ttemp Ttemp_pos z s). }
  (* 段⑤：ext/linear 链接 + π(s)·1 == π(s)（mult_compat 对角闭合） *)
  apply (real_eq_trans
           (real_list_sum (list Real)
              (fun w : list Real => real_mult (pi_boltzmann w) (gK w s)) states)
           (real_mult (pi_boltzmann s)
              (real_list_sum (list Real) (fun w : list Real => gK s w) states))
           (pi_boltzmann s)).
  - exact (real_eq_trans
             (real_list_sum (list Real)
                (fun w : list Real => real_mult (pi_boltzmann w) (gK w s)) states)
             (real_list_sum (list Real)
                (fun w : list Real => real_mult (pi_boltzmann s) (gK s w)) states)
             (real_mult (pi_boltzmann s)
                (real_list_sum (list Real) (fun w : list Real => gK s w) states))
             Hext Hlin).
  - apply (real_eq_trans
             (real_mult (pi_boltzmann s)
                (real_list_sum (list Real) (fun w : list Real => gK s w) states))
             (real_mult (pi_boltzmann s) real_one)
             (pi_boltzmann s)).
    + apply (RealSetoid.real_eq_mult_compat
               (pi_boltzmann s)
               (real_list_sum (list Real) (fun w : list Real => gK s w) states)
               (pi_boltzmann s) real_one
               (real_eq_refl (pi_boltzmann s)) Hnorm).
    + exact (real_mult_one (pi_boltzmann s)).
Qed.

(* ③ 不动点沿 A 件迭代器传播：K·π == π ⟹ Kⁿ·π == π（逐点）           *)
Theorem ga_titer_fixed : forall (n : nat) (s : list Real),
  real_eq (tv_titer states gK n pi_boltzmann s) (pi_boltzmann s).
Proof.
  intro n. induction n as [| n IH]; intro s.
  - (* n = 0：tv_titer 0 π ≡ π *)
    apply real_eq_refl.
  - (* n+1：tv_titer(S n) π ≡ tv_step(K, tv_titer n π)；
       求和外延（逐点 IH）+ 不动点假设两步链闭合 *)
    apply (real_eq_trans
             (tv_step states gK (tv_titer states gK n pi_boltzmann) s)
             (tv_step states gK pi_boltzmann s)
             (pi_boltzmann s)).
    + unfold tv_step.
      apply (real_list_sum_ext (list Real)
               (fun i : list Real =>
                  real_mult (tv_titer states gK n pi_boltzmann i) (gK i s))
               (fun i : list Real => real_mult (pi_boltzmann i) (gK i s))
               states).
      intro i.
      apply (RealSetoid.real_eq_mult_compat
               (tv_titer states gK n pi_boltzmann i) (gK i s)
               (pi_boltzmann i) (gK i s)
               (IH i) (real_eq_refl (gK i s))).
    + exact (ga_boltzmann_fixed s).
Qed.

(* ④ 主定理：Gibbs/Boltzmann 吸引性（规格文件「≤ ω^k·TV(μ,π) 形」支）     *)
(*   对一切 n：TV(Kⁿ·μ, π) ≤ (1 − e^{−2γ/T})ⁿ·TV(μ,π)               *)
(*   证明 = A 件 tvd_dstar_iter_contraction（ν := π）+ ③ 不动点       *)
(*   传播 + TV 泛函逐点外延运输。                                    *)
Theorem ga_attractor_contraction : forall (n : nat) (mu : list Real -> Real),
  real_eq (real_list_sum (list Real) mu states) real_one ->
  real_le (tv_doeblin states (tv_titer states gK n mu) pi_boltzmann)
          (real_mult (tv_rpow gomd n) (tv_doeblin states mu pi_boltzmann)).
Proof.
  intros n mu Hmu.
  (* 步 1：TV 泛函运输——第二槽 Kⁿ·π 换成 π（逐点 abs 外延） *)
  assert (HeqTV : real_eq
           (tv_doeblin states (tv_titer states gK n mu) pi_boltzmann)
           (tv_doeblin states (tv_titer states gK n mu)
                       (tv_titer states gK n pi_boltzmann))).
  { unfold tv_doeblin.
    apply (RealSetoid.real_eq_mult_compat
             tv_half
             (real_list_sum (list Real)
                (fun s : list Real =>
                   real_abs
                     (real_minus_r (tv_titer states gK n mu s)
                                   (pi_boltzmann s)))
                states)
             tv_half
             (real_list_sum (list Real)
                (fun s : list Real =>
                   real_abs
                     (real_minus_r (tv_titer states gK n mu s)
                                   (tv_titer states gK n pi_boltzmann s)))
                states)
             (real_eq_refl tv_half)
             (real_list_sum_ext (list Real)
                (fun s : list Real =>
                   real_abs
                     (real_minus_r (tv_titer states gK n mu s)
                                   (pi_boltzmann s)))
                (fun s : list Real =>
                   real_abs
                     (real_minus_r (tv_titer states gK n mu s)
                                   (tv_titer states gK n pi_boltzmann s)))
                states
                (fun s : list Real =>
                   RealSetoid.real_eq_abs_compat
                     (real_minus_r (tv_titer states gK n mu s)
                                   (pi_boltzmann s))
                     (real_minus_r (tv_titer states gK n mu s)
                                   (tv_titer states gK n pi_boltzmann s))
                     (tvd_eq_minus_compat
                        (tv_titer states gK n mu s)
                        (tv_titer states gK n mu s)
                        (pi_boltzmann s)
                        (tv_titer states gK n pi_boltzmann s)
                        (real_eq_refl (tv_titer states gK n mu s))
                        (real_eq_sym _ _ (ga_titer_fixed n s)))))). }
  (* 步 2：A 件主定理于 ν := π 实例化消解，步 1 之链接之 *)
  apply (real_le_trans
           (tv_doeblin states (tv_titer states gK n mu) pi_boltzmann)
           (tv_doeblin states (tv_titer states gK n mu)
                       (tv_titer states gK n pi_boltzmann))
           (real_mult (tv_rpow gomd n) (tv_doeblin states mu pi_boltzmann))).
  - apply (RealSetoid.real_eq_le _ _). exact HeqTV.
  - exact (tvd_dstar_iter_contraction
             states n_pos Ttemp Ttemp_pos gamma gamma_pos z z_lo z_hi
             Labs n mu pi_boltzmann Hmu ga_pi_boltzmann_norm).
Qed.

End GibbsAttr.

(* G4 审计口（≥1 条，全 Closed 预期）                                *)
Print Assumptions ga_boltzmann_fixed.
Print Assumptions ga_titer_fixed.
Print Assumptions ga_attractor_contraction.
(* ================= §2 ga2_rt 族 ================= *)
Import RealInterfaceEnhancedMod.

Section GibbsAssembly.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

(* ---- 求和对接面（UpReqAlign2 Req2AlignCore 同位；本件使用 ext/add/linear    *)
(*   + le 单调槽 ga2_sum_le（UpReqPPOPlain rpl_sum_le 同形）。sum_pos 与       *)
(*   log_inv_exp_neg_req 零使用，诚实剪除（出节参面登记）。                    *)
(*   注意：UpReqAlign2 原节无 le 单调槽——本件增补位，喂定时由实例侧供给）。      *)
Variable sumf : (S -> R) -> R.
Hypothesis ga2_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis ga2_sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis ga2_sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis ga2_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis ga2_log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).

(* ---- 节内组合器（隐式参版，避 elaborator 占位序坑） ---- *)
Definition ga2_rt {x y z : R} (H1 : req x y) (H2 : req y z) : req x z :=
  req_trans x y z H1 H2.
Definition ga2_le_id_l {a b c : R} (H1 : req a b) (H2 : le b c) : le a c :=
  le_id_l a b c H1 H2.
Definition ga2_le_id_r {a b c : R} (H1 : req b c) (H2 : le a b) : le a c :=
  le_id_r a b c H1 H2.

(* ---- 节内辅件 1：opp one 乘法归一（req_opp_mult_r + mult_one 两步） ---- *)
Lemma ga2_mopp_one : forall x : R, req (mult (opp one) x) (opp x).
Proof.
  intro x.
  assert (H1 : req (mult (opp one) x) (opp (mult one x))).
  { exact (req_opp_mult_r one x). }
  assert (H2 : req (mult one x) x).
  { exact (req_mult_one_l x). }
  assert (H3 : req (opp (mult one x)) (opp x)).
  { exact (req_opp_compat (mult one x) x H2). }
  exact (req_trans (mult (opp one) x) (opp (mult one x)) (opp x) H1 H3).
Qed.

(* ---- 节内辅件 2（点态核，S04 gibbs_pointwise 的 req2 面重演）：             *)
(*   p·(1 − q/p − eps) ≤ p·(log p − log q)，逐点 s。                          *)
Lemma ga2_ptw_le :
  forall (p q : S -> R) (eps : R) (s : S)
         (Hps : lt zero (p s)) (Hqs : lt zero (q s)),
    lt zero eps ->
    le (plus (p s) (opp (plus (q s) (mult (p s) eps))))
       (mult (p s) (req_minus (log (p s) Hps) (log (q s) Hqs))).
Proof.
  intros p q eps s Hps Hqs Heps.
  assert (Htan : le (log (mult (q s) (inv_pos (p s) Hps))
                          (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)))
                    (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
    by exact (log_le_linear_eps (mult (q s) (inv_pos (p s) Hps))
                 (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps))
                 eps Heps).
  assert (Hlm : req (log (mult (q s) (inv_pos (p s) Hps))
                         (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)))
                    (plus (log (q s) Hqs) (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))))
    by exact (log_mult (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)).
  (* log(1/p) ≡ −log p（inv_pos_correct 归一 + log 论证换底 + 取消件） *)
  assert (Hlip : req (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))
                     (opp (log (p s) Hps))).
  { assert (Ha : req (log (mult (p s) (inv_pos (p s) Hps))
                          (mult_positive (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps)))
                     (plus (log (p s) Hps) (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))))
      by exact (log_mult (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps)).
    assert (Hb : req (log (mult (p s) (inv_pos (p s) Hps))
                          (mult_positive (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps)))
                     (log one one_pos))
      by exact (ga2_log_req_compat (mult (p s) (inv_pos (p s) Hps)) one
                 (mult_positive (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps))
                 one_pos (inv_pos_correct (p s) Hps)).
    assert (Hc : req (log one one_pos) zero) by exact (log_one one_pos).
    assert (Hd : req (plus (log (p s) Hps)
                           (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))) zero)
      by exact (ga2_rt
                  (req_sym (log (mult (p s) (inv_pos (p s) Hps))
                              (mult_positive (p s) (inv_pos (p s) Hps) Hps
                                (inv_pos_pos (p s) Hps)))
                           (plus (log (p s) Hps)
                                 (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps)))
                           Ha)
                  (ga2_rt Hb Hc)).
    exact (req_plus_inv_unique (log (p s) Hps)
             (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))
             (opp (log (p s) Hps)) Hd (plus_opp (log (p s) Hps))). }
  assert (Hstep3 : req (log (mult (q s) (inv_pos (p s) Hps))
                            (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)))
                       (plus (log (q s) Hqs) (opp (log (p s) Hps))))
    by exact (ga2_rt Hlm
              (req_plus_compat (log (q s) Hqs) (log (q s) Hqs)
                (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps)) (opp (log (p s) Hps))
                (req_refl (log (q s) Hqs)) Hlip)).
  assert (H4 : le (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                  (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
    by exact (ga2_le_id_l
                (req_sym (log (mult (q s) (inv_pos (p s) Hps))
                            (mult_positive (q s) (inv_pos (p s) Hps) Hqs
                              (inv_pos_pos (p s) Hps)))
                         (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                         Hstep3)
                Htan).
  assert (H5 : le (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                  (opp (plus (log (q s) Hqs) (opp (log (p s) Hps)))))
    by exact (opp_le_compat (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                            (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                            H4).
  (* 右肢形归一：opp (plus (log q) (opp (log p))) ≡ req_minus (log p) (log q) *)
  assert (H6 : req (opp (plus (log (q s) Hqs) (opp (log (p s) Hps))))
                   (req_minus (log (p s) Hps) (log (q s) Hqs))).
  { assert (r1 : req (opp (plus (log (q s) Hqs) (opp (log (p s) Hps))))
                     (plus (opp (log (q s) Hqs)) (opp (opp (log (p s) Hps)))))
      by exact (req_opp_plus (log (q s) Hqs) (opp (log (p s) Hps))).
    assert (r2 : req (plus (opp (log (q s) Hqs)) (opp (opp (log (p s) Hps))))
                     (plus (opp (log (q s) Hqs)) (log (p s) Hps)))
      by exact (req_plus_compat (opp (log (q s) Hqs)) (opp (log (q s) Hqs))
                (opp (opp (log (p s) Hps))) (log (p s) Hps)
                (req_refl (opp (log (q s) Hqs))) (req_double_neg (log (p s) Hps))).
    assert (r3 : req (plus (opp (log (q s) Hqs)) (log (p s) Hps))
                     (plus (log (p s) Hps) (opp (log (q s) Hqs))))
      by exact (plus_comm (opp (log (q s) Hqs)) (log (p s) Hps)).
    exact (ga2_rt (ga2_rt r1 r2) r3). }
  assert (H7 : le (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                  (req_minus (log (p s) Hps) (log (q s) Hqs)))
    by exact (ga2_le_id_r H6 H5).
  assert (Hle0 : le zero (p s)) by exact (lt_le_iff zero (p s) (inl Hps)).
  assert (H8 : le (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                  (mult (p s) (req_minus (log (p s) Hps) (log (q s) Hqs))))
    by exact (req_le_mult_compat_r (p s) _ _ Hle0 H7).
  (* 左肢值归一：p·opp(1 − q/p + eps) ≡ plus p (opp (plus q (p·eps)))
     （inv_pos_correct 约分 q/p·p = q + distrib/opp 分配律，req 代数链） *)
  assert (H9 : req (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                   (plus (p s) (opp (plus (q s) (mult (p s) eps))))).
  { assert (d1 : req (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                     (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps)))
      by exact (req_sym (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))
                        (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                        (plus_assoc (mult (q s) (inv_pos (p s) Hps)) (opp one) eps)).
    assert (c1 : req (mult (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                     (plus (mult (p s) (mult (q s) (inv_pos (p s) Hps)))
                           (mult (p s) (plus (opp one) eps))))
      by exact (ga2_rt
                (req_mult_compat (p s) (p s)
                  (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                  (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))
                  (req_refl (p s)) d1)
                (distrib (p s) (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))).
    assert (c2 : req (mult (p s) (mult (q s) (inv_pos (p s) Hps))) (q s)).
    { exact (ga2_rt (mult_assoc (p s) (q s) (inv_pos (p s) Hps))
              (ga2_rt (req_mult_compat (mult (p s) (q s)) (mult (q s) (p s))
                         (inv_pos (p s) Hps) (inv_pos (p s) Hps)
                         (req_mult_comm_rewrite (p s) (q s))
                         (req_refl (inv_pos (p s) Hps)))
                (ga2_rt (req_sym (mult (q s) (mult (p s) (inv_pos (p s) Hps)))
                                 (mult (mult (q s) (p s)) (inv_pos (p s) Hps))
                                 (mult_assoc (q s) (p s) (inv_pos (p s) Hps)))
                  (ga2_rt (req_mult_compat (q s) (q s)
                             (mult (p s) (inv_pos (p s) Hps)) one
                             (req_refl (q s)) (inv_pos_correct (p s) Hps))
                    (mult_one (q s)))))). }
    assert (c3 : req (mult (p s) (plus (opp one) eps)) (plus (opp (p s)) (mult (p s) eps))).
    { assert (m1 : req (mult (p s) (opp one)) (opp (p s)))
        by exact (ga2_rt (req_opp_mult_l (p s) one)
                  (req_opp_compat (mult (p s) one) (p s) (mult_one (p s)))).
      exact (ga2_rt (distrib (p s) (opp one) eps)
              (req_plus_compat (mult (p s) (opp one)) (opp (p s))
                (mult (p s) eps) (mult (p s) eps) m1 (req_refl (mult (p s) eps)))). }
    assert (t2 : req (mult (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                     (plus (q s) (plus (opp (p s)) (mult (p s) eps))))
      by exact (ga2_rt c1
                (ga2_rt
                  (req_plus_compat (mult (p s) (mult (q s) (inv_pos (p s) Hps))) (q s)
                    (mult (p s) (plus (opp one) eps)) (mult (p s) (plus (opp one) eps))
                    c2 (req_refl (mult (p s) (plus (opp one) eps))))
                  (req_plus_compat (q s) (q s)
                    (mult (p s) (plus (opp one) eps)) (plus (opp (p s)) (mult (p s) eps))
                    (req_refl (q s)) c3))).
    assert (c5 : req (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                     (opp (mult (p s) (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps)))))
      by exact (ga2_rt
                (req_opp_mult_l (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                (req_opp_compat (mult (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                  (mult (p s) (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps)))
                  (req_mult_compat (p s) (p s)
                    (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                    (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))
                    (req_refl (p s)) d1))).
    assert (c6 : req (opp (plus (q s) (plus (opp (p s)) (mult (p s) eps))))
                     (plus (p s) (opp (plus (q s) (mult (p s) eps))))).
    { assert (v1 : req (opp (plus (q s) (plus (opp (p s)) (mult (p s) eps))))
                       (plus (opp (q s)) (opp (plus (opp (p s)) (mult (p s) eps)))))
        by exact (req_opp_plus (q s) (plus (opp (p s)) (mult (p s) eps))).
      assert (v2 : req (opp (plus (opp (p s)) (mult (p s) eps)))
                       (plus (opp (opp (p s))) (opp (mult (p s) eps))))
        by exact (req_opp_plus (opp (p s)) (mult (p s) eps)).
      assert (v3 : req (plus (opp (q s)) (opp (plus (opp (p s)) (mult (p s) eps))))
                       (plus (opp (q s)) (plus (opp (opp (p s))) (opp (mult (p s) eps)))))
        by exact (req_plus_compat (opp (q s)) (opp (q s))
                  (opp (plus (opp (p s)) (mult (p s) eps)))
                  (plus (opp (opp (p s))) (opp (mult (p s) eps)))
                  (req_refl (opp (q s))) v2).
      assert (v4 : req (plus (opp (q s)) (opp (opp (p s)))) (plus (opp (q s)) (p s)))
        by exact (req_plus_compat (opp (q s)) (opp (q s)) (opp (opp (p s))) (p s)
                  (req_refl (opp (q s))) (req_double_neg (p s))).
      assert (v5 : req (plus (opp (q s)) (plus (opp (opp (p s))) (opp (mult (p s) eps))))
                       (plus (plus (opp (q s)) (opp (opp (p s)))) (opp (mult (p s) eps))))
        by exact (plus_assoc (opp (q s)) (opp (opp (p s))) (opp (mult (p s) eps))).
      assert (v6 : req (plus (plus (opp (q s)) (opp (opp (p s)))) (opp (mult (p s) eps)))
                       (plus (plus (opp (q s)) (p s)) (opp (mult (p s) eps))))
        by exact (req_plus_compat (plus (opp (q s)) (opp (opp (p s)))) (plus (opp (q s)) (p s))
                  (opp (mult (p s) eps)) (opp (mult (p s) eps)) v4 (req_refl (opp (mult (p s) eps)))).
      assert (v7 : req (plus (plus (opp (q s)) (p s)) (opp (mult (p s) eps)))
                       (plus (plus (p s) (opp (q s))) (opp (mult (p s) eps))))
        by exact (req_plus_compat (plus (opp (q s)) (p s)) (plus (p s) (opp (q s)))
                  (opp (mult (p s) eps)) (opp (mult (p s) eps))
                  (plus_comm (opp (q s)) (p s)) (req_refl (opp (mult (p s) eps)))).
      assert (v8 : req (plus (plus (p s) (opp (q s))) (opp (mult (p s) eps)))
                       (plus (p s) (plus (opp (q s)) (opp (mult (p s) eps)))))
        by exact (req_sym (plus (p s) (plus (opp (q s)) (opp (mult (p s) eps))))
                          (plus (plus (p s) (opp (q s))) (opp (mult (p s) eps)))
                          (plus_assoc (p s) (opp (q s)) (opp (mult (p s) eps)))).
      assert (v9 : req (plus (p s) (plus (opp (q s)) (opp (mult (p s) eps))))
                       (plus (p s) (opp (plus (q s) (mult (p s) eps)))))
        by exact (req_plus_compat (p s) (p s)
                  (plus (opp (q s)) (opp (mult (p s) eps)))
                  (opp (plus (q s) (mult (p s) eps)))
                  (req_refl (p s))
                  (req_sym (opp (plus (q s) (mult (p s) eps)))
                           (plus (opp (q s)) (opp (mult (p s) eps)))
                           (req_opp_plus (q s) (mult (p s) eps)))).
      exact (ga2_rt v1
              (ga2_rt v3
                (ga2_rt v5
                  (ga2_rt v6 (ga2_rt v7 (ga2_rt v8 v9)))))). }
    exact (ga2_rt c5
              (ga2_rt (req_opp_compat
                        (mult (p s) (plus (mult (q s) (inv_pos (p s) Hps))
                                            (plus (opp one) eps)))
                        (plus (q s) (plus (opp (p s)) (mult (p s) eps)))
                        (ga2_rt (req_sym (mult (p s)
                                           (plus (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (opp one)) eps))
                                         (mult (p s)
                                           (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (plus (opp one) eps)))
                                         (req_mult_compat (p s) (p s)
                                           (plus (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (opp one)) eps)
                                           (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (plus (opp one) eps))
                                           (req_refl (p s)) d1))
                                  t2))
                c6)). }
  exact (ga2_le_id_l
          (req_sym (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                   (plus (p s) (opp (plus (q s) (mult (p s) eps)))) H9)
          H8).
Qed.

(* ---- 主件：req2_gibbs_inequality 组装（norm 参数位面 + eps 见证形出口） ----
   出口结论 le zero (plus KL eps)：KL 项 = @req2_rel_ent R RIS S sumf p q Hp Hq
   （与 UpReqU2.v:359 槽语句的 KLE 项 δ 透明逐字同体）。 *)
Lemma ga2_gibbs_eps :
  forall (p q : S -> R)
         (Hp : @req2_pos_dist R RIS S p) (Hq : @req2_pos_dist R RIS S q)
         (Hnp : req (sumf p) one) (Hnq : req (sumf q) one) (eps : R),
    lt zero eps ->
    le zero (plus (@req2_rel_ent R RIS S sumf p q Hp Hq) eps).
Proof.
  intros p q Hp Hq Hnp Hnq eps Heps.
  assert (Hptw : forall s : S,
            le (plus (p s) (opp (plus (q s) (mult (p s) eps))))
               (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
    by (intro s; exact (ga2_ptw_le p q eps s (Hp s) (Hq s) Heps)).
  assert (Hsum : le (sumf (fun s => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                    (sumf (fun s => mult (p s)
                              (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))))
    by exact (ga2_sum_le _ _ Hptw).
  (* 求和代数：ΣG ≡ opp eps（norm 零和 + 线性 + opp one 缩放） *)
  assert (Tr : req (sumf (fun s => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                   (opp eps)).
  { assert (T1 : req (sumf (fun s => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                     (plus (sumf p)
                           (sumf (fun s => opp (plus (q s) (mult (p s) eps))))))
      by exact (ga2_sum_add p (fun s => opp (plus (q s) (mult (p s) eps)))).
    assert (T3e : req (sumf (fun s => opp (plus (q s) (mult (p s) eps))))
                      (plus (opp one) (opp eps))).
    { assert (T3a : req (sumf (fun s => opp (plus (q s) (mult (p s) eps))))
                        (sumf (fun s => plus (opp (q s)) (opp (mult (p s) eps)))))
        by exact (ga2_sum_ext (fun s => opp (plus (q s) (mult (p s) eps)))
                  (fun s => plus (opp (q s)) (opp (mult (p s) eps)))
                  (fun s => req_opp_plus (q s) (mult (p s) eps))).
      assert (T3b : req (sumf (fun s => plus (opp (q s)) (opp (mult (p s) eps))))
                        (plus (sumf (fun s => opp (q s)))
                              (sumf (fun s => opp (mult (p s) eps)))))
        by exact (ga2_sum_add (fun s => opp (q s)) (fun s => opp (mult (p s) eps))).
      assert (A : req (sumf (fun s => opp (q s))) (opp one)).
      { assert (A1 : req (sumf (fun s => opp (q s))) (sumf (fun s => mult (opp one) (q s))))
          by exact (ga2_sum_ext (fun s => opp (q s)) (fun s => mult (opp one) (q s))
                    (fun s => req_sym (mult (opp one) (q s)) (opp (q s))
                                (ga2_mopp_one (q s)))).
        assert (A2 : req (sumf (fun s => mult (opp one) (q s))) (mult (opp one) (sumf q)))
          by exact (ga2_sum_linear (opp one) q).
        assert (A3 : req (mult (opp one) (sumf q)) (mult (opp one) one))
          by exact (req_mult_compat (opp one) (opp one) (sumf q) one
                      (req_refl (opp one)) Hnq).
        assert (A4 : req (mult (opp one) one) (opp one)) by exact (mult_one (opp one)).
        exact (ga2_rt A1 (ga2_rt A2 (ga2_rt A3 A4))). }
      assert (B : req (sumf (fun s => opp (mult (p s) eps))) (opp eps)).
      { assert (B1 : req (sumf (fun s => opp (mult (p s) eps)))
                          (sumf (fun s => mult (opp one) (mult (p s) eps))))
          by exact (ga2_sum_ext (fun s => opp (mult (p s) eps))
                    (fun s => mult (opp one) (mult (p s) eps))
                    (fun s => req_sym (mult (opp one) (mult (p s) eps))
                                (opp (mult (p s) eps))
                                (ga2_mopp_one (mult (p s) eps)))).
        assert (B2 : req (sumf (fun s => mult (opp one) (mult (p s) eps)))
                          (mult (opp one) (sumf (fun s => mult (p s) eps))))
          by exact (ga2_sum_linear (opp one) (fun s => mult (p s) eps)).
        assert (B3 : req (sumf (fun s => mult (p s) eps)) eps).
        { assert (B3a : req (sumf (fun s => mult (p s) eps))
                            (sumf (fun s => mult eps (p s))))
            by exact (ga2_sum_ext (fun s => mult (p s) eps) (fun s => mult eps (p s))
                      (fun s => req_mult_comm_rewrite (p s) eps)).
          assert (B3b : req (sumf (fun s => mult eps (p s))) (mult eps (sumf p)))
            by exact (ga2_sum_linear eps p).
          assert (B3c : req (mult eps (sumf p)) (mult eps one))
            by exact (req_mult_compat eps eps (sumf p) one (req_refl eps) Hnp).
          assert (B3d : req (mult eps one) eps) by exact (mult_one eps).
          exact (ga2_rt B3a (ga2_rt B3b (ga2_rt B3c B3d))). }
        assert (B4 : req (mult (opp one) (sumf (fun s => mult (p s) eps)))
                          (mult (opp one) eps))
          by exact (req_mult_compat (opp one) (opp one)
                    (sumf (fun s => mult (p s) eps)) eps (req_refl (opp one)) B3).
        exact (ga2_rt B1
                (ga2_rt B2 (ga2_rt B4 (ga2_mopp_one eps)))). }
      exact (ga2_rt T3a (ga2_rt T3b
              (req_plus_compat (sumf (fun s => opp (q s))) (opp one)
                (sumf (fun s => opp (mult (p s) eps))) (opp eps) A B))). }
    assert (T4 : req (plus one (plus (opp one) (opp eps))) (opp eps)).
    { assert (e1 : req (plus one (plus (opp one) (opp eps)))
                       (plus (plus one (opp one)) (opp eps)))
        by exact (plus_assoc one (opp one) (opp eps)).
      assert (e2 : req (plus (plus one (opp one)) (opp eps)) (plus zero (opp eps)))
        by exact (req_plus_compat (plus one (opp one)) zero (opp eps) (opp eps)
                  (plus_opp one) (req_refl (opp eps))).
      exact (ga2_rt e1 (ga2_rt e2 (req_plus_zero_l (opp eps)))). }
    exact (ga2_rt T1
            (ga2_rt
              (req_plus_compat (sumf p) one
                (sumf (fun s => opp (plus (q s) (mult (p s) eps))))
                (plus (opp one) (opp eps)) Hnp T3e)
              T4)). }
  assert (HD : le (opp eps)
                  (sumf (fun s => mult (p s)
                            (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))))
    by exact (ga2_le_id_l
                (req_sym (sumf (fun s => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                         (opp eps) Tr)
                Hsum).
  apply (le_id_l zero (plus (opp eps) eps)
          (plus (sumf (fun s => mult (p s)
                        (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))) eps)).
  - exact (ga2_rt (req_sym (plus eps (opp eps)) zero (plus_opp eps))
                  (plus_comm eps (opp eps))).
  - exact (le_plus_compat (opp eps)
            (sumf (fun s => mult (p s)
                      (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
            eps eps HD (le_refl eps)).
Qed.

(* ---- 出口孪生：le (opp eps) KL 形（使用侧夹逼常用向；req 群归一） ---- *)
Corollary ga2_gibbs_eps_opps :
  forall (p q : S -> R)
         (Hp : @req2_pos_dist R RIS S p) (Hq : @req2_pos_dist R RIS S q)
         (Hnp : req (sumf p) one) (Hnq : req (sumf q) one) (eps : R),
    lt zero eps ->
    le (opp eps) (@req2_rel_ent R RIS S sumf p q Hp Hq).
Proof.
  intros p q Hp Hq Hnp Hnq eps Heps.
  assert (Step1 : le (plus zero (opp eps))
                     (plus (plus (@req2_rel_ent R RIS S sumf p q Hp Hq) eps)
                           (opp eps)))
    by exact (le_plus_compat zero
                             (plus (@req2_rel_ent R RIS S sumf p q Hp Hq) eps)
                             (opp eps) (opp eps)
                             (ga2_gibbs_eps p q Hp Hq Hnp Hnq eps Heps)
                             (le_refl (opp eps))).
  assert (Step3 : req (plus (plus (@req2_rel_ent R RIS S sumf p q Hp Hq) eps)
                            (opp eps))
                     (@req2_rel_ent R RIS S sumf p q Hp Hq)).
  { exact (ga2_rt
            (req_sym (plus (@req2_rel_ent R RIS S sumf p q Hp Hq)
                           (plus eps (opp eps)))
                     (plus (plus (@req2_rel_ent R RIS S sumf p q Hp Hq) eps)
                           (opp eps))
                     (plus_assoc (@req2_rel_ent R RIS S sumf p q Hp Hq) eps (opp eps)))
            (ga2_rt
              (req_plus_compat (@req2_rel_ent R RIS S sumf p q Hp Hq)
                (@req2_rel_ent R RIS S sumf p q Hp Hq) (plus eps (opp eps)) zero
                (req_refl (@req2_rel_ent R RIS S sumf p q Hp Hq)) (plus_opp eps))
              (plus_zero (@req2_rel_ent R RIS S sumf p q Hp Hq)))). }
  exact (le_id_l (opp eps) (plus zero (opp eps))
                 (@req2_rel_ent R RIS S sumf p q Hp Hq)
                 (req_sym (plus zero (opp eps)) (opp eps)
                          (req_plus_zero_l (opp eps)))
                 (le_id_r (plus zero (opp eps))
                          (plus (plus (@req2_rel_ent R RIS S sumf p q Hp Hq) eps)
                                (opp eps))
                          (@req2_rel_ent R RIS S sumf p q Hp Hq) Step3 Step1)).
Qed.

End GibbsAssembly.

Print Assumptions ga2_gibbs_eps.
Print Assumptions ga2_gibbs_eps_opps.
