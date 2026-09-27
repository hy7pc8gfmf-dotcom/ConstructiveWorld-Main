(* ==========================================================================)
   UpAblP2T1_CertC.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：p2t1b_T2_abs_le_quad_supply、p2t1b_T2_quad_t_le_h_supply、p2t1b_T2_abs_h_sq_supply、p2t1b_T2_db_breaking_bound_supply、p2t1b_g3_pick、p2t1c_T2_abs_le_quad_supply、p2t1c_T2_quad_t_le_h_supply、p2t1c_T2_abs_h_sq_supply、p2t1c_T2_db_breaking_bound_reg。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import List.
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
Require Import UpRealLeB.
Require Import UpRealLeB2.
From Stdlib Require Import Extraction.

(* ================= §1 p2t1b_T2_abs_le_quad_supply 族 ================= *)
From Stdlib Require Import QArith.QArith.

(* ################ 结论 9(e)/(f) 四条具名供给定理（转引 UpRealLeB2） ########## *)

(* p2t1b_T2_abs_le_quad_supply：前提 X ≤ eps1、−X ≤ 2t²+eps2、0<eps1、
   0<eps2；结论 |X| ≤_b 2t²+(eps1+eps2)。证明转引 UpRealLeB2 的
   real_abs_le_quad_B。 *)
Theorem p2t1b_T2_abs_le_quad_supply : forall (X t eps1 eps2 : Real),
  real_le X eps1 ->
  real_le (real_opp X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) ->
  real_lt real_zero eps1 -> real_lt real_zero eps2 ->
  real_le_b (real_abs X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
               (real_plus eps1 eps2)).
Proof.
  intros X t eps1 eps2 HXA HXB HA Htwo.
  exact (real_abs_le_quad_B X t eps1 eps2 HXA HXB HA Htwo).
Qed.

(* p2t1b_T2_quad_t_le_h_supply：前提 0<x、|h| < eps·x²/4、0<eps；结论
   2·(h/x)² ≤_b eps·|h|/2；证明转引 UpRealLeB2 的 real_quad_t_le_h_B。 *)
Theorem p2t1b_T2_quad_t_le_h_supply : forall (x h eps : Real)
    (Hx : real_lt real_zero x),
  real_lt (real_abs h)
    (real_mult
       (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
       (real_mult eps (real_mult x x))) ->
  real_lt real_zero eps ->
  real_le_b
    (real_mult (real_mult (real_mult h (real_inv_pos x Hx))
                          (real_mult h (real_inv_pos x Hx)))
               (real_plus real_one real_one))
    (real_mult (real_mult (real_inv_pos (real_plus real_one real_one)
                             real_two_pos_local) eps)
               (real_abs h)).
Proof.
  intros x h eps Hx Hh Heps.
  exact (real_quad_t_le_h_B x h eps Hx Hh Heps).
Qed.

(* p2t1b_T2_abs_h_sq_supply：前提 0<A、|h|<eps3；结论 A·|h|² ≤_b
   (A·eps3)·|h|；证明转引 UpRealLeB2 的 real_abs_h_sq_le_B。 *)
Theorem p2t1b_T2_abs_h_sq_supply : forall A h eps3 : Real,
  real_lt real_zero A -> real_lt (real_abs h) eps3 ->
  real_le_b (real_mult A (real_mult (real_abs h) (real_abs h)))
            (real_mult (real_mult A eps3) (real_abs h)).
Proof.
  intros A h eps3 HA Hh3.
  exact (real_abs_h_sq_le_B A h eps3 HA Hh3).
Qed.

(* p2t1b_T2_db_breaking_bound_supply：db 破界上界的复合系数形式——16 个
   节参数逐一显式接续（转移核非负与对称、能量 Lipschitz 与下界、
   逐出分区正性等），eps 与 eps′ 并入显式前提；复合系数
   C:=invZ·T·(exp+1) 仅具非负性；转引 UpRealLeB2 的 real_db_breaking_bound_B。 *)
Theorem p2t1b_T2_db_breaking_bound_supply :
  forall (S0 : Type) (keep : S0 -> Set)
         (keep_dec : forall s : S0, Or (keep s) (Not (keep s)))
         (real_transition : S0 -> S0 -> Real)
         (real_transition_nonneg : forall s s' : S0,
            real_le real_zero (real_transition s s'))
         (real_transition_sym : forall s s' : S0,
            real_eq (real_transition s s') (real_transition s' s))
         (real_energy : S0 -> Real)
         (D : Real) (D_pos : real_lt real_zero D)
         (L E_max : Real)
         (real_metric : S0 -> S0 -> Real)
         (real_energy_lipschitz : forall s s' : S0,
            real_le (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))
                    (real_mult L (real_metric s s')))
         (real_energy_lower : forall s : S0,
            real_le (real_opp E_max) (real_energy s))
         (real_sum_over_S : (S0 -> Real) -> Real)
         (real_evicted_partition_pos : real_lt real_zero
            (real_evicted_partition S0 keep keep_dec real_energy D D_pos
               real_sum_over_S))
         (s s' : S0),
    keep s -> keep s' ->
    real_le_b (real_db_breaking S0 keep keep_dec real_transition real_energy
                 D D_pos real_sum_over_S real_evicted_partition_pos s s')
              (real_mult
                 (real_inv_pos (real_evicted_partition S0 keep keep_dec real_energy
                                  D D_pos real_sum_over_S)
                               real_evicted_partition_pos)
                 (real_mult (real_transition s s')
                    (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                       (real_mult
                          (real_mult (real_mult (real_inv_pos D D_pos) L)
                                     (real_metric s s'))
                          (cauchy_real_exp
                             (real_mult (real_mult (real_inv_pos D D_pos) L)
                                        (real_metric s s'))))))).
Proof.
  intros S0 keep keep_dec real_transition real_transition_nonneg
         real_transition_sym real_energy D D_pos L E_max real_metric
         real_energy_lipschitz real_energy_lower real_sum_over_S
         real_evicted_partition_pos s s' Hs Hs'.
  exact (real_db_breaking_bound_B S0 keep keep_dec real_transition
           real_transition_nonneg real_transition_sym real_energy D D_pos
           L E_max real_metric real_energy_lipschitz real_energy_lower
           real_sum_over_S real_evicted_partition_pos s s' Hs Hs').
Qed.

(* ################ 提取核验：见证面取 Q 层纯函数 #################### *)
(* 本件四条供给定理均为实数层接口语句，不入提取集；提取见证面另立 Q 层      *)
(* 纯函数 p2t1b_g3_pick。 *)
Definition p2t1b_g3_pick (n : nat) : Q :=
  (1 # (Pos.succ (Pos.succ (Pos.of_succ_nat n))))%Q.

Set Extraction Output Directory "_tp2t1b_g3out".
Extraction "p2t1b_G3_Cert.ml" p2t1b_g3_pick.

(* ################ 假设审计：对四条供给定理逐一 Print Assumptions ############## *)
Print Assumptions p2t1b_T2_abs_le_quad_supply.
Print Assumptions p2t1b_T2_quad_t_le_h_supply.
Print Assumptions p2t1b_T2_abs_h_sq_supply.
Print Assumptions p2t1b_T2_db_breaking_bound_supply.
(* ================= §2 p2t1c_T2_abs_le_quad_supply 族 ================= *)
From Stdlib Require Import QArith.QArith.

(* ################ 一、结论 9(e) 三条的独立重建 ############################ *)

(* p2t1c_T2_abs_le_quad_supply：|X| ≤_b 2t²＋(eps1＋eps2)。
   前提 X ≤ eps1、−X ≤ 2t²＋eps2、0<eps1、0<eps2。证明：由源件结论
   real_abs_le_quad_eps 经 real_le_closure_b_one 收拢全称 eps 直接推得。 *)
Theorem p2t1c_T2_abs_le_quad_supply : forall (X t eps1 eps2 : Real),
  real_le X eps1 ->
  real_le (real_opp X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) ->
  real_lt real_zero eps1 -> real_lt real_zero eps2 ->
  real_le_b (real_abs X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
               (real_plus eps1 eps2)).
Proof.
  intros X t eps1 eps2 HXA HXB Heps1 Heps2.
  apply real_le_closure_b_one. intros eps Heps.
  exact (real_abs_le_quad_eps X t eps1 eps2 eps HXA HXB Heps1 Heps2 Heps).
Qed.

(* p2t1c_T2_quad_t_le_h_supply：2(h/x)² ≤_b (1/2)·eps·|h|；前提 0<x、
   |h| < eps·x²/4、0<eps；由 real_quad_t_le_h_eps 经 real_le_closure_b_one 推得。 *)
Theorem p2t1c_T2_quad_t_le_h_supply : forall (x h eps : Real)
    (Hx : real_lt real_zero x),
  real_lt (real_abs h)
    (real_mult
       (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
       (real_mult eps (real_mult x x))) ->
  real_lt real_zero eps ->
  real_le_b
    (real_mult (real_mult (real_mult h (real_inv_pos x Hx))
                          (real_mult h (real_inv_pos x Hx)))
               (real_plus real_one real_one))
    (real_mult (real_mult (real_inv_pos (real_plus real_one real_one)
                             real_two_pos_local) eps)
               (real_abs h)).
Proof.
  intros x h eps Hx Hh Heps.
  apply real_le_closure_b_one. intros eps' Heps'.
  exact (real_quad_t_le_h_eps x h eps eps' Hx Hh Heps Heps').
Qed.

(* p2t1c_T2_abs_h_sq_supply：A|h|² ≤_b (A·eps3)·|h|；前提 0<A、|h|<eps3；
   由 real_abs_h_sq_le_eps 经 real_le_closure_b_one 单步推得。 *)
Theorem p2t1c_T2_abs_h_sq_supply : forall A h eps3 : Real,
  real_lt real_zero A -> real_lt (real_abs h) eps3 ->
  real_le_b (real_mult A (real_mult (real_abs h) (real_abs h)))
            (real_mult (real_mult A eps3) (real_abs h)).
Proof.
  intros A h eps3 HA Hh3.
  apply real_le_closure_b_one. intros eps' Heps'.
  exact (real_abs_h_sq_le_eps A h eps3 eps' HA Hh3 Heps').
Qed.

(* ################ 二、结论 9(f) 语句面重述与类型互证         ################ *)

(* p2t1c_T2_db_breaking_bound_reg：db 破界上界（复合系数形）重述定义。
   复合系数为 inv(分区)·T·(exp·…) 形。本 Definition 的类型为语句面的
   独立重述；赋值项取 p2t1b_T2_db_breaking_bound_supply——两者逐字
   一致则类型装配通过，不一致则编译报错（互证由类型检查完成）。 *)
Definition p2t1c_T2_db_breaking_bound_reg :
  forall (S0 : Type) (keep : S0 -> Set)
         (keep_dec : forall s : S0, Or (keep s) (Not (keep s)))
         (real_transition : S0 -> S0 -> Real)
         (real_transition_nonneg : forall s s' : S0,
            real_le real_zero (real_transition s s'))
         (real_transition_sym : forall s s' : S0,
            real_eq (real_transition s s') (real_transition s' s))
         (real_energy : S0 -> Real)
         (D : Real) (D_pos : real_lt real_zero D)
         (L E_max : Real)
         (real_metric : S0 -> S0 -> Real)
         (real_energy_lipschitz : forall s s' : S0,
            real_le (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))
                    (real_mult L (real_metric s s')))
         (real_energy_lower : forall s : S0,
            real_le (real_opp E_max) (real_energy s))
         (real_sum_over_S : (S0 -> Real) -> Real)
         (real_evicted_partition_pos : real_lt real_zero
            (real_evicted_partition S0 keep keep_dec real_energy D D_pos
               real_sum_over_S))
         (s s' : S0),
    keep s -> keep s' ->
    real_le_b (real_db_breaking S0 keep keep_dec real_transition real_energy
                 D D_pos real_sum_over_S real_evicted_partition_pos s s')
              (real_mult
                 (real_inv_pos (real_evicted_partition S0 keep keep_dec real_energy
                                  D D_pos real_sum_over_S)
                               real_evicted_partition_pos)
                 (real_mult (real_transition s s')
                    (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                       (real_mult
                          (real_mult (real_mult (real_inv_pos D D_pos) L)
                                     (real_metric s s'))
                          (cauchy_real_exp
                             (real_mult (real_mult (real_inv_pos D D_pos) L)
                                        (real_metric s s'))))))) :=
  p2t1b_T2_db_breaking_bound_supply.

(* ################ 三、交叉核验：CertB 四具名件对重述语句的类型装配 ########## *)
(* 每条 Check 以本件独立重述语句为型、以 CertB 具名件为项：类型装配
   通过即两者语句面逐字一致（互证由类型检查完成）。 *)

Check (p2t1b_T2_abs_le_quad_supply :
  forall (X t eps1 eps2 : Real),
  real_le X eps1 ->
  real_le (real_opp X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) ->
  real_lt real_zero eps1 -> real_lt real_zero eps2 ->
  real_le_b (real_abs X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
               (real_plus eps1 eps2))).

Check (p2t1b_T2_quad_t_le_h_supply :
  forall (x h eps : Real) (Hx : real_lt real_zero x),
  real_lt (real_abs h)
    (real_mult
       (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
       (real_mult eps (real_mult x x))) ->
  real_lt real_zero eps ->
  real_le_b
    (real_mult (real_mult (real_mult h (real_inv_pos x Hx))
                          (real_mult h (real_inv_pos x Hx)))
               (real_plus real_one real_one))
    (real_mult (real_mult (real_inv_pos (real_plus real_one real_one)
                             real_two_pos_local) eps)
               (real_abs h))).

Check (p2t1b_T2_abs_h_sq_supply :
  forall A h eps3 : Real,
  real_lt real_zero A -> real_lt (real_abs h) eps3 ->
  real_le_b (real_mult A (real_mult (real_abs h) (real_abs h)))
            (real_mult (real_mult A eps3) (real_abs h))).

Check (p2t1b_T2_db_breaking_bound_supply :
  forall (S0 : Type) (keep : S0 -> Set)
         (keep_dec : forall s : S0, Or (keep s) (Not (keep s)))
         (real_transition : S0 -> S0 -> Real)
         (real_transition_nonneg : forall s s' : S0,
            real_le real_zero (real_transition s s'))
         (real_transition_sym : forall s s' : S0,
            real_eq (real_transition s s') (real_transition s' s))
         (real_energy : S0 -> Real)
         (D : Real) (D_pos : real_lt real_zero D)
         (L E_max : Real)
         (real_metric : S0 -> S0 -> Real)
         (real_energy_lipschitz : forall s s' : S0,
            real_le (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))
                    (real_mult L (real_metric s s')))
         (real_energy_lower : forall s : S0,
            real_le (real_opp E_max) (real_energy s))
         (real_sum_over_S : (S0 -> Real) -> Real)
         (real_evicted_partition_pos : real_lt real_zero
            (real_evicted_partition S0 keep keep_dec real_energy D D_pos
               real_sum_over_S))
         (s s' : S0),
    keep s -> keep s' ->
    real_le_b (real_db_breaking S0 keep keep_dec real_transition real_energy
                 D D_pos real_sum_over_S real_evicted_partition_pos s s')
              (real_mult
                 (real_inv_pos (real_evicted_partition S0 keep keep_dec real_energy
                                  D D_pos real_sum_over_S)
                               real_evicted_partition_pos)
                 (real_mult (real_transition s s')
                    (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                       (real_mult
                          (real_mult (real_mult (real_inv_pos D D_pos) L)
                                     (real_metric s s'))
                          (cauchy_real_exp
                             (real_mult (real_mult (real_inv_pos D D_pos) L)
                                        (real_metric s s')))))))).

(* ################ 提取核验：见证面取 Q 层纯函数 #################### *)
(* 实数层接口语句件不入提取集；提取见证面另立 Q 层纯函数，
   主题对位为多 eps 组合的逐点正 eps 供给族 1/(n+2)。 *)
Definition p2t1c_g3_pick (n : nat) : Q :=
  (1 # (Pos.succ (Pos.succ (Pos.of_succ_nat n))))%Q.

Set Extraction Output Directory "_tp2t1c_g3out".
Extraction "p2t1c_G3_Cert.ml" p2t1c_g3_pick.

(* ################ 假设审计：文尾对八条结论逐一 Print Assumptions ############ *)
Print Assumptions p2t1c_T2_abs_le_quad_supply.
Print Assumptions p2t1c_T2_quad_t_le_h_supply.
Print Assumptions p2t1c_T2_abs_h_sq_supply.
Print Assumptions p2t1c_T2_db_breaking_bound_reg.
Print Assumptions p2t1b_T2_abs_le_quad_supply.
Print Assumptions p2t1b_T2_quad_t_le_h_supply.
Print Assumptions p2t1b_T2_abs_h_sq_supply.
Print Assumptions p2t1b_T2_db_breaking_bound_supply.
