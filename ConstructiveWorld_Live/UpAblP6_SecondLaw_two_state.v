(* ===================================================================== *)
(* UpAblP6_SecondLaw_two_state.v —— SecondLawQuantified SlqSecondLaw       *)
(*   节的 two_state 整节实例化供给件（纯构造性；语句面全 Set 层）。          *)
(*                                                                        *)
(* --------------------------------------------------------------------- *)
(* 【使命】源模块 SecondLawQuantified.v Section SlqSecondLaw（九个接口参数  *)
(*   S/sumf/sumpos/sumext/sumlinear/sumadd/T/T_pos/energy）在 two_state     *)
(*   具体载体上整节实例化：载体与求和机器全具体（二元直接和，非 list        *)
(*   机器），节前导件与双向定量锚逐一全参数实例化，另闭合零前提实例。        *)
(* 【范围区分（与三件既有供给不重复）】                                    *)
(*   · UpReqTempDual RealTempDualBool 节（t13_bstate=[true;false]）：bool   *)
(*     载体 + real_list_sum 机器直接实例化四接口参数，结论=能量-熵对偶      *)
(*     sigT 形——本件载体为 Inductive ts_state、求和机器为二元直接和         *)
(*     （四接口参数引理须从实数代数面真证，list 供体不覆盖），              *)
(*     结论=SlqSecondLaw 节内定理的实例化面，两面不相交。                   *)
(*   · SecondLawConsume.v 四出口（slc_gain_kl_two_sided_eps 等）：          *)
(*     任意前提形的 list 应用件，无载体具体化——本件为具体两态载体整节实例化。 *)
(*   · UpAblP1_SecondLawQuantified_sumd.v：sum 四面以 enum 列表和为        *)
(*     假设位的抽象形，其件头明记 two_state 整节实例化不在该件范围——        *)
(*     本件即该实例化，非 sum 接口参数的重复实例化。                        *)
(* 【供体引理（全参显式调用）】                                            *)
(*   · slq_gibbs_step_fixed：S sumf sumpos sumext sumlinear T T_pos        *)
(*     energy p Hnp s'（不动点件）                                         *)
(*   · slq_step_pos：同参数序（一步核逐点正）                              *)
(*   · slq_step_entropy_eq_boltz：同参数序 p Hnp（实现熵≡均衡熵）          *)
(*   · slq_entropy_gain_kl_lower / slq_entropy_gain_kl_upper：S sumf       *)
(*     sumpos sumext sumlinear sumadd T T_pos energy p Hp Hnp Henergy      *)
(*     eps Heps（双向定量锚）                                              *)
(*   · slq_second_law_eps_list：X l Hnil T Ht energy p Hp Hnp Henergy      *)
(*     eps Heps（list 形全闭锚）                                           *)
(*   · real_lt_plus_compat（0<x,0<y→0<x+y 正性加法闭）；real_plus_zero      *)
(*     （x+0==0 右幺）；real_distrib（x·(y+z)==x·y+x·z 左分配）；           *)
(*     real_plus_assoc/comm；real_lt_zero_one；                            *)
(*     RealSetoid.real_eq_plus_compat（交叉序 a~c→b~d→a+b~c+d）；           *)
(*     real_lt_id_l/r；real_boltzmann_dist_temp_normalized/pos（闭节        *)
(*     S sumf sumpos sumext sumlinear T T_pos energy 形）；                 *)
(*     real_energy_exp_temp（定义=Σ p_T·energy，故 p:=p_T 时能量期望前提    *)
(*     real_eq_refl 直接闭合，UpReqTempDual bool 先例同式）。               *)
(* 【装配】(一) 载体 ts_state（Inductive Set 两态）+ ts_sumf 二元直接和，   *)
(*   四接口参数引理真证（sumpos 由正性加法闭+右幺换左；sumlinear 由左分配   *)
(*   反向；sumadd 由四项重组引理 uab23_ts_plus_swap 五步链；sumext 由       *)
(*   交叉序 compat）；(二) Section Uab23TsSlq 开 T/T_pos/energy 三接口      *)
(*   参数（S/sumf/四参数已具体闭合），节前导三件与双向定量锚两件全参数      *)
(*   实例化；(三) 节外 slq_second_law_eps_list 的 two_state 实例面          *)
(*   （X:=ts_state，l:=ts_list=[ts_a;ts_b]，求和机器改用列表和 ts_lsumf）； *)
(*   (四) 零前提实例闭合：T:=real_one（real_lt_zero_one）、energy:=ts_energy *)
(*   （ts_a↦0, ts_b↦1）、p:=Boltzmann 自身，Hnp 由供体给出、Henergy 走定义性 refl。 *)
(* 【构造性注记】出口面全 Set 层 real_eq/real_lt/real_le；零公理零承认；    *)
(*   节内前提出节即消解；全部定理以 Qed 闭合（无一例外）；Print Assumptions  *)
(*   6 处核验；uab23_/ts_ 前缀全库唯一。                                    *)
(* ===================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import SecondLawQuantified.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqTempDefs.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* §1 two_state 载体与二元直接和求和机器（定义面与四接口参数引理） *)
(* ============================================================ *)

(* 载体：两态系统（Set 层具体载体，替代 bool/t13_bstate 的另一选择） *)
Inductive ts_state : Set :=
| ts_a : ts_state
| ts_b : ts_state.

(* 求和机器：二元直接和（非 real_list_sum——四接口参数引理须自证，list 供体不覆盖） *)
Definition ts_sumf (f : ts_state -> Real) : Real :=
  real_plus (f ts_a) (f ts_b).

(* 四项重组引理：(x+y)+(z+w) == (x+z)+(y+w)（sumadd 的核心代数内容；     *)
(*   五步链：两次 assoc 重排 + 中项 comm + compat 组合）                  *)
Lemma uab23_ts_plus_swap :
  forall x y z w : Real,
    real_eq (real_plus (real_plus x y) (real_plus z w))
            (real_plus (real_plus x z) (real_plus y w)).
Proof.
  intros x y z w.
  apply (real_eq_trans
           (real_plus (real_plus x y) (real_plus z w))
           (real_plus x (real_plus y (real_plus z w)))
           (real_plus (real_plus x z) (real_plus y w))).
  - exact (real_eq_sym (real_plus x (real_plus y (real_plus z w)))
             (real_plus (real_plus x y) (real_plus z w))
             (real_plus_assoc x y (real_plus z w))).
  - apply (real_eq_trans
             (real_plus x (real_plus y (real_plus z w)))
             (real_plus x (real_plus z (real_plus y w)))
             (real_plus (real_plus x z) (real_plus y w))).
    + apply (RealSetoid.real_eq_plus_compat x
               (real_plus y (real_plus z w))
               x
               (real_plus z (real_plus y w))
               (real_eq_refl x)).
      apply (real_eq_trans
               (real_plus y (real_plus z w))
               (real_plus (real_plus y z) w)
               (real_plus z (real_plus y w))).
      * exact (real_plus_assoc y z w).
      * apply (real_eq_trans
                 (real_plus (real_plus y z) w)
                 (real_plus (real_plus z y) w)
                 (real_plus z (real_plus y w))).
        -- apply (RealSetoid.real_eq_plus_compat (real_plus y z) w
                    (real_plus z y) w
                    (real_plus_comm y z) (real_eq_refl w)).
        -- exact (real_eq_sym (real_plus z (real_plus y w))
                    (real_plus (real_plus z y) w)
                    (real_plus_assoc z y w)).
    + exact (real_plus_assoc x z (real_plus y w)).
Qed.

(* 接口参数 1：sumpos——逐点正 ⟹ 和正（由 real_lt_plus_compat 与          *)
(*   real_plus_zero 给出：0+0 换回 0）                                    *)
Lemma uab23_ts_sumpos :
  forall f : ts_state -> Real,
    (forall s : ts_state, real_lt real_zero (f s)) ->
    real_lt real_zero (ts_sumf f).
Proof.
  intros f H.
  exact (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
           (real_plus (f ts_a) (f ts_b))
           (real_eq_sym (real_plus real_zero real_zero) real_zero
                        (real_plus_zero real_zero))
           (real_lt_plus_compat real_zero (f ts_a) real_zero (f ts_b)
                                (H ts_a) (H ts_b))).
Qed.

(* 接口参数 2：sumext——逐点 req ⟹ 和 req（real_eq_plus_compat 两分量直接给出） *)
Lemma uab23_ts_sumext :
  forall f g : ts_state -> Real,
    (forall s : ts_state, real_eq (f s) (g s)) ->
    real_eq (ts_sumf f) (ts_sumf g).
Proof.
  intros f g H.
  exact (RealSetoid.real_eq_plus_compat (f ts_a) (f ts_b) (g ts_a) (g ts_b)
           (H ts_a) (H ts_b)).
Qed.

(* 接口参数 3：sumlinear——齐次（左分配 real_distrib 反向） *)
Lemma uab23_ts_sumlinear :
  forall (a : Real) (f : ts_state -> Real),
    real_eq (ts_sumf (fun s : ts_state => real_mult a (f s)))
            (real_mult a (ts_sumf f)).
Proof.
  intros a f.
  exact (real_eq_sym (real_mult a (real_plus (f ts_a) (f ts_b)))
                     (real_plus (real_mult a (f ts_a))
                                (real_mult a (f ts_b)))
                     (real_distrib a (f ts_a) (f ts_b))).
Qed.

(* 接口参数 4：sumadd——可加（四项重组引理实例） *)
Lemma uab23_ts_sumadd :
  forall f g : ts_state -> Real,
    real_eq (ts_sumf (fun s : ts_state => real_plus (f s) (g s)))
            (real_plus (ts_sumf f) (ts_sumf g)).
Proof.
  intros f g.
  exact (uab23_ts_plus_swap (f ts_a) (g ts_a) (f ts_b) (g ts_b)).
Qed.

(* ============================================================ *)
(* §2 SlqSecondLaw 整节实例化前导件（T/T_pos/energy 三接口参数，         *)
(*   载体/机器/四参数已具体闭合；节内定理全参调用逐一实例化）             *)
(* ============================================================ *)

Section Uab23TsSlq.

Variable T : Real.
Hypothesis T_pos : real_lt real_zero T.
Variable energy : ts_state -> Real.

(* 节前导件 1：一步 Gibbs 热浴核不动点（two_state 实例面） *)
Theorem uab23_ts_gibbs_step_fixed :
  forall (p : ts_state -> Real) (Hnp : real_eq (ts_sumf p) real_one)
         (s' : ts_state),
    real_eq (slq_gibbs_step ts_state ts_sumf uab23_ts_sumpos T T_pos energy p s')
            (slq_boltz ts_state ts_sumf uab23_ts_sumpos T T_pos energy s').
Proof.
  intros p Hnp s'.
  exact (slq_gibbs_step_fixed ts_state ts_sumf uab23_ts_sumpos uab23_ts_sumext uab23_ts_sumlinear
           T T_pos energy p Hnp s').
Qed.

(* 节前导件 2：一步核更新分布逐点正（two_state 实例面） *)
Theorem uab23_ts_step_pos :
  forall (p : ts_state -> Real) (Hnp : real_eq (ts_sumf p) real_one)
         (s' : ts_state),
    real_lt real_zero
      (slq_gibbs_step ts_state ts_sumf uab23_ts_sumpos T T_pos energy p s').
Proof.
  intros p Hnp s'.
  exact (slq_step_pos ts_state ts_sumf uab23_ts_sumpos uab23_ts_sumext uab23_ts_sumlinear
           T T_pos energy p Hnp s').
Qed.

(* 节前导件 3：实现熵 ≡ 均衡熵（不动点的熵论读出，two_state 实例面） *)
Theorem uab23_ts_step_entropy_eq_boltz :
  forall (p : ts_state -> Real) (Hnp : real_eq (ts_sumf p) real_one),
    real_eq (slq_entropy ts_state ts_sumf
               (slq_gibbs_step ts_state ts_sumf uab23_ts_sumpos T T_pos energy p)
               (slq_step_pos ts_state ts_sumf uab23_ts_sumpos uab23_ts_sumext uab23_ts_sumlinear
                  T T_pos energy p Hnp))
            (slq_entropy ts_state ts_sumf
               (slq_boltz ts_state ts_sumf uab23_ts_sumpos T T_pos energy)
               (slq_boltz_pos ts_state ts_sumf uab23_ts_sumpos T T_pos energy)).
Proof.
  intros p Hnp.
  exact (slq_step_entropy_eq_boltz ts_state ts_sumf uab23_ts_sumpos uab23_ts_sumext
           uab23_ts_sumlinear T T_pos energy p Hnp).
Qed.

(* 锚定理（lower）实例面：KL(当前‖p_T) − 熵亏 ≤ eps，                    *)
(*   语义：一步 Gibbs 演化熵增 ≥ 熵亏 − eps（two_state 全参数实例化）。   *)
Theorem uab23_ts_gain_kl_lower :
  forall (p : ts_state -> Real) (Hp : forall s : ts_state, real_lt real_zero (p s))
         (Hnp : real_eq (ts_sumf p) real_one)
         (Henergy : real_eq
                      (ts_sumf (fun s : ts_state => real_mult (p s) (energy s)))
                      (real_energy_exp_temp ts_state ts_sumf uab23_ts_sumpos T T_pos energy))
         (eps : Real) (Heps : real_lt real_zero eps),
    real_le (real_minus_r
               (slq_kl_cur_boltz ts_state ts_sumf uab23_ts_sumpos T T_pos energy p Hp)
               (slq_entropy_gain ts_state ts_sumf uab23_ts_sumpos T T_pos energy p Hp))
            eps.
Proof.
  intros p Hp Hnp Henergy eps Heps.
  exact (slq_entropy_gain_kl_lower ts_state ts_sumf uab23_ts_sumpos uab23_ts_sumext
           uab23_ts_sumlinear uab23_ts_sumadd T T_pos energy p Hp Hnp Henergy eps Heps).
Qed.

(* 锚定理（upper）实例面：熵亏 − KL ≤ eps（互补向，two_state 全参数实例化）。 *)
Theorem uab23_ts_gain_kl_upper :
  forall (p : ts_state -> Real) (Hp : forall s : ts_state, real_lt real_zero (p s))
         (Hnp : real_eq (ts_sumf p) real_one)
         (Henergy : real_eq
                      (ts_sumf (fun s : ts_state => real_mult (p s) (energy s)))
                      (real_energy_exp_temp ts_state ts_sumf uab23_ts_sumpos T T_pos energy))
         (eps : Real) (Heps : real_lt real_zero eps),
    real_le (real_minus_r
               (slq_entropy_gain ts_state ts_sumf uab23_ts_sumpos T T_pos energy p Hp)
               (slq_kl_cur_boltz ts_state ts_sumf uab23_ts_sumpos T T_pos energy p Hp))
            eps.
Proof.
  intros p Hp Hnp Henergy eps Heps.
  exact (slq_entropy_gain_kl_upper ts_state ts_sumf uab23_ts_sumpos uab23_ts_sumext
           uab23_ts_sumlinear uab23_ts_sumadd T T_pos energy p Hp Hnp Henergy eps Heps).
Qed.

End Uab23TsSlq.

(* ============================================================ *)
(* §3 slq_second_law_eps_list 的 two_state 实例面                        *)
(*   （X:=ts_state，l:=ts_list=[ts_a;ts_b]，求和机器改用列表和 ts_lsumf） *)
(* ============================================================ *)

Definition ts_list : list ts_state :=
  cons ts_a (cons ts_b (@nil ts_state)).

Definition ts_list_ne : ts_list <> nil.
Proof.
  intro Hl.
  discriminate Hl.
Qed.

Definition ts_lsumf : (ts_state -> Real) -> Real :=
  fun g : ts_state -> Real => real_list_sum ts_state g ts_list.

Definition ts_lsumpos :
  forall f : ts_state -> Real,
    (forall s : ts_state, real_lt real_zero (f s)) ->
    real_lt real_zero (ts_lsumf f) :=
  fun (f : ts_state -> Real) (Hf : forall s : ts_state, real_lt real_zero (f s)) =>
    real_list_sum_pos ts_state f ts_list Hf ts_list_ne.

Theorem uab23_ts_second_law_eps :
  forall (T : Real) (Ht : real_lt real_zero T) (energy p : ts_state -> Real)
         (Hp : forall s : ts_state, real_lt real_zero (p s))
         (Hnp : real_eq (ts_lsumf p) real_one)
         (Henergy : real_eq
                      (ts_lsumf (fun s : ts_state => real_mult (p s) (energy s)))
                      (real_energy_exp_temp ts_state ts_lsumf ts_lsumpos T Ht energy))
         (eps : Real) (Heps : real_lt real_zero eps),
    real_le (real_entropy_dist ts_state ts_lsumf p Hp)
            (real_plus
               (real_entropy_dist ts_state ts_lsumf
                  (slq_boltz ts_state ts_lsumf ts_lsumpos T Ht energy)
                  (slq_boltz_pos ts_state ts_lsumf ts_lsumpos T Ht energy))
               eps).
Proof.
  intros T Ht energy p Hp Hnp Henergy eps Heps.
  exact (slq_second_law_eps_list ts_state ts_list ts_list_ne T Ht energy p Hp
           Hnp Henergy eps Heps).
Qed.

(* ============================================================ *)
(* §4 零前提实例闭合（T:=real_one，energy 具体，p:=Boltzmann 自身）        *)
(*   real_energy_exp_temp 定义=Σ p_T·energy，故能量期望前提定义性 refl；  *)
(*   Hnp 由 real_boltzmann_dist_temp_normalized 供体给出。                *)
(* ============================================================ *)

Definition ts_energy : ts_state -> Real :=
  fun s : ts_state =>
    match s with
    | ts_a => real_zero
    | ts_b => real_one
    end.

Definition uab23_ts_boltz_one : ts_state -> Real :=
  slq_boltz ts_state ts_sumf uab23_ts_sumpos real_one real_lt_zero_one ts_energy.

Definition uab23_ts_boltz_one_pos :
  forall s : ts_state, real_lt real_zero (uab23_ts_boltz_one s) :=
  real_boltzmann_dist_temp_pos ts_state ts_sumf uab23_ts_sumpos real_one
    real_lt_zero_one ts_energy.

Theorem uab23_ts_anchor_closed_lower :
  forall eps : Real, real_lt real_zero eps ->
    real_le (real_minus_r
               (slq_kl_cur_boltz ts_state ts_sumf uab23_ts_sumpos real_one
                  real_lt_zero_one ts_energy
                  uab23_ts_boltz_one uab23_ts_boltz_one_pos)
               (slq_entropy_gain ts_state ts_sumf uab23_ts_sumpos real_one
                  real_lt_zero_one ts_energy
                  uab23_ts_boltz_one uab23_ts_boltz_one_pos))
            eps.
Proof.
  intros eps Heps.
  exact (slq_entropy_gain_kl_lower ts_state ts_sumf uab23_ts_sumpos uab23_ts_sumext
           uab23_ts_sumlinear uab23_ts_sumadd real_one real_lt_zero_one ts_energy
           uab23_ts_boltz_one uab23_ts_boltz_one_pos
           (real_boltzmann_dist_temp_normalized ts_state ts_sumf uab23_ts_sumpos
              uab23_ts_sumext uab23_ts_sumlinear real_one real_lt_zero_one ts_energy)
           (real_eq_refl
              (ts_sumf
                 (fun s : ts_state =>
                    real_mult (uab23_ts_boltz_one s) (ts_energy s))))
           eps Heps).
Qed.

Theorem uab23_ts_anchor_closed_upper :
  forall eps : Real, real_lt real_zero eps ->
    real_le (real_minus_r
               (slq_entropy_gain ts_state ts_sumf uab23_ts_sumpos real_one
                  real_lt_zero_one ts_energy
                  uab23_ts_boltz_one uab23_ts_boltz_one_pos)
               (slq_kl_cur_boltz ts_state ts_sumf uab23_ts_sumpos real_one
                  real_lt_zero_one ts_energy
                  uab23_ts_boltz_one uab23_ts_boltz_one_pos))
            eps.
Proof.
  intros eps Heps.
  exact (slq_entropy_gain_kl_upper ts_state ts_sumf uab23_ts_sumpos uab23_ts_sumext
           uab23_ts_sumlinear uab23_ts_sumadd real_one real_lt_zero_one ts_energy
           uab23_ts_boltz_one uab23_ts_boltz_one_pos
           (real_boltzmann_dist_temp_normalized ts_state ts_sumf uab23_ts_sumpos
              uab23_ts_sumext uab23_ts_sumlinear real_one real_lt_zero_one ts_energy)
           (real_eq_refl
              (ts_sumf
                 (fun s : ts_state =>
                    real_mult (uab23_ts_boltz_one s) (ts_energy s))))
           eps Heps).
Qed.

(* ===================================================================== *)
(* 收尾核验：Print Assumptions 六件全 Closed                              *)
(* ===================================================================== *)
Print Assumptions uab23_ts_step_entropy_eq_boltz.
Print Assumptions uab23_ts_gain_kl_lower.
Print Assumptions uab23_ts_gain_kl_upper.
Print Assumptions uab23_ts_second_law_eps.
Print Assumptions uab23_ts_anchor_closed_lower.
Print Assumptions uab23_ts_anchor_closed_upper.
