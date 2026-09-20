(* ============================================================ *)
(* UpAblP2T1_CertB.v —— 结论 9(e)/(f) 无余量供给证书件（CertB）          *)
(*   数学使命：实数不等式四条的具名供给与 Q 层提取见证。                 *)
(* ============================================================ *)
(* 【使命】将 UpRealLeB2 已建的四条实数不等式引理以具名供给定理形式接入    *)
(*   供给面，对应结论 9(e)/(f) 的余量显式入前提形式；≤_b 记 Set 层序谓词   *)
(*   real_le_b。四条定理均为转引：前提逐一显式承接，证明由 UpRealLeB2      *)
(*   相应引理直接给出，本件不引入新证明。                                  *)
(*   p2t1b_T2_abs_le_quad_supply：|X| ≤ 2t²+eps 的双余量形式；             *)
(*   p2t1b_T2_quad_t_le_h_supply：(h/x)² 的内嵌 |h| 余量形式；             *)
(*   p2t1b_T2_abs_h_sq_supply：A·|h|² 的倍率余量形式；                    *)
(*   p2t1b_T2_db_breaking_bound_supply：db 破界上界的复合系数形式。        *)
(* 【依赖】Stdlib（List／QArith.QArith／Extraction）／CW_ConstructiveWorld_219 *)
(*   ／UpRealLeB／UpRealLeB2（real_abs_le_quad_B、real_quad_t_le_h_B、     *)
(*   real_abs_h_sq_le_B、real_db_breaking_bound_B 供给源）。               *)
(* 【对标】数学原型：分析学中 abs-平方与破界估计的显式余量形式；           *)
(*   mathlib/stdlib 无直接构造对应物。                                     *)
(* 【构造性注记】语句面全 Set 层；全件 Qed 闭合、零承认词面、无经典逻辑。  *)
(*   四条供给定理的前提（含 keep_dec 的排除律前提）逐一显式承接；文末对    *)
(*   四条主结论逐一 Print Assumptions，以全部 Closed 为零外部未证假设判据。 *)
(* 【编译配方】Rocq 9.1 直调 coqc 编译（不带 -Q 包映射），cpu_guard 包裹   *)
(*   限载；输出一律 -o 临时目录，树内 .vo 不重写，信任缓存分毫不动。       *)
(* 【结构总览】§1 p2t1b_T2_abs_le_quad_supply——若 X ≤ eps1 且             *)
(*   −X ≤ 2t²+eps2 且 0<eps1、0<eps2，则 |X| ≤_b 2t²+(eps1+eps2)；         *)
(*   由 real_abs_le_quad_B 直接推得。                                      *)
(*   §2 p2t1b_T2_quad_t_le_h_supply——若 0<x 且 |h| < eps·x²/4 且 0<eps，   *)
(*   则 2·(h/x)² ≤_b eps·|h|/2；由 real_quad_t_le_h_B 直接推得。           *)
(*   §3 p2t1b_T2_abs_h_sq_supply——若 0<A 且 |h|<eps3，则 A·|h|² ≤_b       *)
(*   (A·eps3)·|h|；由 real_abs_h_sq_le_B 直接推得。                       *)
(*   §4 p2t1b_T2_db_breaking_bound_supply——db 破界上界的复合系数形式：    *)
(*   转移核非负与对称、能量 Lipschitz 与下界、逐出分区正性等 16 个节参数   *)
(*   逐一显式承接；复合系数 C:=invZ·T·(exp+1) 仅具非负性；由               *)
(*   real_db_breaking_bound_B 直接推得。                                   *)
(*   §5 提取核验：供给定理均为实数层接口语句不入提取集，见证面另立 Q 层    *)
(*   纯函数 p2t1b_g3_pick；§6 假设审计区。                                 *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.
From Stdlib Require Import Extraction.

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
   节参数逐一显式承接（转移核非负与对称、能量 Lipschitz 与下界、
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
