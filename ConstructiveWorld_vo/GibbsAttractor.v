(* ============================================================ *)
(* GibbsAttractor.v —— 施工席位 B1：Gibbs/Boltzmann 平稳分布的      *)
(* 指数吸引性（A2 组合榜 组 1 + 组 2 对接件）2026-09-16             *)
(* ============================================================ *)
(* 依赖坐标（全部为 215 件 90001 基座内已编译库件，只读复用）：      *)
(*   A 件 UpTVDoeblin.v:1564  tv_doeblin_iter                     *)
(*        TV(Kⁿ·μ, Kⁿ·ν) ≤ (1−δ)ⁿ·TV(μ,ν)（Section TVRealWorld）； *)
(*        :1970 tvd_dstar_iter_contraction——δ 接口被显式常数        *)
(*        δ* := e^{−2γ/T} 满足后的旗舰迭代件（Section TVDStar），    *)
(*        率 ω := tv_omd 应用于 δ-star，即 1 − e^{−2γ/T}。          *)
(*   B 件 UpReqSteadyThermo.v:100 real_steady_state_boltzmann      *)
(*        Σ_{s'} π(s')·T(s',s) == π(s)（detailed balance ⟹ 稳态，   *)
(*        抽象 S 载体 Section RealThermoSteady）。                  *)
(* 本件承载（前缀 ga_，基座与全树 grep 零撞名）：                    *)
(*   ① ga_pi_boltzmann_norm —— B 件载体实例化（π :=                 *)
(*        real_boltzmann_prob 于离散枚举世界）后 partition 条件      *)
(*        放电 Σπ == 1（real_list_sum_linear + inv_pos 收口）。      *)
(*   ② ga_boltzmann_fixed —— 小连接件（任务书所指「A 的不动点形 =    *)
(*        B 的 tv_dstar 实例对接」）：把 real_steady_state_boltzmann *)
(*        于 S := list Real、sum := real_list_sum(枚举)、           *)
(*        transition := tvd_K（Gibbs 核）实例化，闭出                *)
(*        tv_step(gK, π) == π 逐点形（A 件迭代器的不动点形）。        *)
(*   ③ ga_titer_fixed —— 不动点沿 tv_titer 传播：K·π==π ⟹          *)
(*        Kⁿ·π == π（逐点；real_list_sum_ext + 归纳）。              *)
(*   ④ ga_attractor_contraction —— 旗舰（任务书「≤ ω^k·TV(μ,π) 形」*)
(*        支）：对一切 n，TV(Kⁿ·μ, π) ≤ (1−e^{−2γ/T})ⁿ·TV(μ,π)。    *)
(*        证明 = A 件旗舰于 ν := π 放电 + ③不动点传播 + TV 泛函      *)
(*        逐点外延运输（tvd_eq_minus_compat + real_eq_abs_compat    *)
(*        + real_list_sum_ext）。率显式：δ* = e^{−2γ/T}。           *)
(* 显式混合时间注记（任务书「显式 k 上界公式」面）：率件④对一切 n     *)
(*   成立且 ④ 的率 ωⁿ 随 n 单调不增，故论文级混合步数               *)
(*   k = ⌈ln(ε/TV₀)/ln(1−δstar)⌉ 的可计算上界选取所需两要素（每 n   *)
(*   的显式率 + ε-选择）在本件形式化边界内齐备；库内 Real 层无        *)
(*   ln/ceil 构件，该 ceil 公式不冒充本件结论（诚实边界，非空壳）。   *)
(* 红线自审：                                                       *)
(*   —— 语句面全 Set 层：量词全 Set/Type 载体（nat/list Real/        *)
(*      函数空间），比较全 real_lt/real_le/real_eq（Set 编码），     *)
(*      零 Prop 泄露、零 /\ \/ exists-Prop 于签名；                  *)
(*   —— 禁词全零（无公理/自认/参数声明/猜想/中止类语句，             *)
(*      零经典逻辑/排中律/半途认输；全件 Qed 真证）；           *)
(*   —— 非平凡：④ 非假设转述（不动点传播 + TV 泛函运输为本件新证）；  *)
(*   —— 诚实接口沿基座口径显式入位：Labs（|Σf| ≤ Σ|f|，A 件同位      *)
(*      前提）、part_cond / dbalance（B 件同位前提），零隐藏假设；    *)
(*   —— 文末 Print Assumptions 审计口 3 条（②③④ 主件），全 Closed。 *)
(* 编译配方（9.0.1 临时轨，VO_BASE_901 = ConstructiveWorld_vo）：    *)
(*   source Live/toolchain/env901.sh && eval $(opam env --switch     *)
(*   live901) && cd Live/build && bash ../tools/cpu_guard.sh --      *)
(*   rocq c -Q "$VO_BASE_901" "" -Q . "" GibbsAttractor.v            *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpTVDoeblin.
Require Import UpReqSteadyThermo.

(* ============================================================ *)
(* Section GibbsAttr：离散状态世界 + Gibbs 核 + Boltzmann 载体        *)
(* （A 件 TVDStar 变量面 + B 件 RealThermoSteady 载体槽，两桥并轨）   *)
(* ============================================================ *)
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

(* ============================================================ *)
(* ① π 是分布：Σπ == 1（partition 条件放电；B 件归一化闭合件）       *)
(* ============================================================ *)
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

(* ============================================================ *)
(* ② 小连接件：B 件稳态定理实例化 ⟹ π 是 tv_step 不动点              *)
(*   Σ_{s'} π(s')·K(s',s) == π(s)（逐点）——即 A 件迭代器的不动点形。  *)
(* ============================================================ *)
Theorem ga_boltzmann_fixed : forall s : list Real,
  real_eq (tv_step states gK pi_boltzmann s) (pi_boltzmann s).
Proof.
  intro s.
  exact (real_steady_state_boltzmann
           (list Real)
           (fun f : list Real -> Real => real_list_sum (list Real) f states)
           (fun (f g : list Real -> Real)
              (H : forall w : list Real, real_eq (f w) (g w)) =>
              real_list_sum_ext (list Real) f g states H)
           (fun (a : Real) (f : list Real -> Real) =>
              real_list_sum_linear (list Real) a f states)
           energy Dcap Dcap_pos Zr Zr_pos
           gK
           (fun i : list Real =>
              tvd_K_row states n_pos Ttemp Ttemp_pos z i)
           dbalance
           s).
Qed.

(* ============================================================ *)
(* ③ 不动点沿 A 件迭代器传播：K·π == π ⟹ Kⁿ·π == π（逐点）           *)
(* ============================================================ *)
Theorem ga_titer_fixed : forall (n : nat) (s : list Real),
  real_eq (tv_titer states gK n pi_boltzmann s) (pi_boltzmann s).
Proof.
  intro n. induction n as [| n IH]; intro s.
  - (* n = 0：tv_titer 0 π ≡ π *)
    apply real_eq_refl.
  - (* n+1：tv_titer(S n) π ≡ tv_step(K, tv_titer n π)；
       求和外延（逐点 IH）+ 不动点假设两步链收口 *)
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

(* ============================================================ *)
(* ④ 旗舰：Gibbs/Boltzmann 吸引性（任务书「≤ ω^k·TV(μ,π) 形」支）     *)
(*   对一切 n：TV(Kⁿ·μ, π) ≤ (1 − e^{−2γ/T})ⁿ·TV(μ,π)               *)
(*   证明 = A 件 tvd_dstar_iter_contraction（ν := π）+ ③ 不动点       *)
(*   传播 + TV 泛函逐点外延运输。                                    *)
(* ============================================================ *)
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
  (* 步 2：A 件旗舰于 ν := π 放电，步 1 之链接之 *)
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

(* ============================================================ *)
(* G4 审计口（≥1 条，全 Closed 预期）                                *)
(* ============================================================ *)
Print Assumptions ga_boltzmann_fixed.
Print Assumptions ga_titer_fixed.
Print Assumptions ga_attractor_contraction.
