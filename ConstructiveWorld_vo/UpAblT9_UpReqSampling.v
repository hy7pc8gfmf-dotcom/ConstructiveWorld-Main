(* ==========================================================================)
   UpAblT9_UpReqSampling.v — Context 束两位与 TV 面两位之 UpReqSampling 辖区材料化件
   使命: aux_delta_plus_omd、rsq_bs_list_const_sum、delta_star 实例面与跨模块 minorization（tvd_minorization 全参特化）四定理。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist、UpReqSumD、UpTVDoeblin、UpReqSampling、List。
   对标: 总变差收敛的 minorization 条件实例层。
   构造性: 全 Qed 闭合、零承认词面；req 层 le 在 RealEnhancedReal 实例位定义性等于 real_le，逐字 exact 代入；只读依赖，原树零改。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树原地重编），cpu_guard 包裹限载。
   ========================================================================== *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSumD.
Require Import UpTVDoeblin.
Require Import UpReqSampling.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* 位1 ←:99（rep@:153；R/RIS 实例位材料化） *)
Theorem uabT9_usamp_ctx_delta_plus_omd :
  forall delta : Real, req (plus delta (req_minus one delta)) one.
Proof.
  intro delta.
  exact (@aux_delta_plus_omd Real RealEnhancedReal delta).
Qed.

(* 位2 ←:701（rep@:790；R/RIS 实例位材料化，零接口前提） *)
Theorem uabT9_bsoft_ctx_list_const_sum :
  forall (S : Set) (c : Real) (l : list S),
    req (rsq_bs_list_sum S (fun _ : S => c) l)
       (mult (reqd_nat_to_R (length l)) c).
Proof.
  intros S c l.
  exact (@rsq_bs_list_const_sum Real RealEnhancedReal S c l).
Qed.

(* 位3 ←:126（rep@:935；delta_star 具体实例材料化，TV 面） *)
Theorem uabT9_usamp_delta_star_lt_one :
  forall (temp : Real) (temp_pos : lt zero temp)
         (Delta : Real) (Delta_pos : lt zero Delta),
    lt (mult (rsq_exp_pos_fn (mult (inv_pos temp temp_pos) (opp Delta)))
             (rsq_exp_pos_fn (mult (inv_pos temp temp_pos) (opp Delta)))) one.
Proof.
  intros temp temp_pos Delta Delta_pos.
  exact (@rsq_bs_delta_star_lt_one Real RealEnhancedReal temp temp_pos Delta Delta_pos).
Qed.

(* 位4 ←:131（rep=UpTVDoeblin:1933 实例面；TV 面） *)
Theorem uabT9_usamp_minorization_tvd :
  forall (states : list (list Real))
         (n_pos : real_lt real_zero (real_of_nat (length states)))
         (Ttemp : Real) (Ttemp_pos : real_lt real_zero Ttemp) (gamma : Real)
         (z : list Real -> list Real -> Real),
    (forall i j : list Real, real_le (real_opp gamma) (z i j)) ->
    (forall i j : list Real, real_le (z i j) gamma) ->
    forall i j : list Real,
      le (mult (tvd_dstar Ttemp Ttemp_pos gamma) (tvd_u states n_pos j))
         (tvd_K states n_pos Ttemp Ttemp_pos z i j).
Proof.
  intros states n_pos Ttemp Ttemp_pos gamma z Hlb Hub i j.
  exact (tvd_minorization states n_pos Ttemp Ttemp_pos gamma z Hlb Hub i j).
Qed.

(* ---- PA 收尾 ---- *)
Print Assumptions uabT9_usamp_ctx_delta_plus_omd.
Print Assumptions uabT9_bsoft_ctx_list_const_sum.
Print Assumptions uabT9_usamp_delta_star_lt_one.
Print Assumptions uabT9_usamp_minorization_tvd.
