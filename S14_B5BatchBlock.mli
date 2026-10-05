open BinInt
open BinNums
open Datatypes
open Nat
open QArith_base
open Qabs
open Qminmax
open S01_BaseRing
open S02_CauchyComplete
open S03_QExp
open S07_RealSetoidExpLog
open S08_RealMainlineDPO
open S09_EntropyReal
open S10_KVQuantTrig
open S11_TP3B5
open S12_B5RecycleSF
open Specif

type __ = Obj.t

val b5d1_b3rr_atan_deriv_lin :
  coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Real -> real_lt ->
  (coq_Real, (real_lt, coq_Real -> real_lt -> (nat -> coq_QleT') -> coq_Real
  -> real_lt -> real_le) coq_And) sigT

val b5dD_atan_deriv_b5a_r_exp :
  coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Real -> real_lt ->
  (coq_Real, (real_lt, coq_Real -> real_lt -> (nat -> coq_QleT') -> coq_Real
  -> real_lt -> real_le) coq_And) sigT

val b5dD_vdh_pts_r_exp :
  coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Real -> real_lt -> coq_Q ->
  coq_Q -> coq_QltT -> coq_QltT -> (coq_Real, (real_lt, coq_Real -> real_lt
  -> (nat -> coq_QleT') -> coq_Real -> real_lt -> (nat, __) sigT) coq_And)
  sigT

val b5dM_real_const_pos : coq_Q -> coq_QltT -> real_lt

val b5dM_b5i_one_plus_eps2_pos :
  coq_Real -> coq_Q -> real_lt -> coq_QltT -> real_lt

val b5dM_b5n_eps_proj_lt :
  coq_Real -> real_lt -> (coq_Q, (coq_QltT, (nat, __) sigT) coq_And) sigT

val b5dM_b5c_d_proj_le_one : coq_Real -> (nat, __) sigT

val b5dI_inv_leaf_witness_eq :
  coq_Real -> coq_Q -> real_lt -> coq_QltT -> real_eq

val b5dI_real_mult_positive_exp :
  coq_Real -> coq_Real -> real_lt -> real_lt -> real_lt

val b5dI_sin_atan_diff_closed_r_exp :
  coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> coq_Q -> coq_Q ->
  coq_QleT' -> (nat -> coq_QleT') -> coq_Real -> real_lt -> (coq_Real,
  (real_lt, coq_Real -> real_lt -> (nat -> coq_QleT') -> coq_Real -> real_lt
  -> real_le) coq_And) sigT

val b5dI_cos_atan_diff_closed_r_exp :
  coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> coq_Q -> coq_Q ->
  coq_QleT' -> (nat -> coq_QleT') -> coq_Real -> real_lt -> (coq_Real,
  (real_lt, coq_Real -> real_lt -> (nat -> coq_QleT') -> coq_Real -> real_lt
  -> real_le) coq_And) sigT

val b5dI_E_diff_closed_r_exp :
  coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> coq_Q -> coq_Q ->
  coq_QleT' -> (nat -> coq_QleT') -> coq_Real -> real_lt -> (coq_Real,
  (real_lt, coq_Real -> real_lt -> (nat -> coq_QleT') -> coq_Real -> real_lt
  -> real_le) coq_And) sigT

val b5dJ_two_pos_exp : real_lt

val b5dJ_log_diff_dx_exp :
  coq_Real -> real_lt -> coq_Real -> real_lt -> (coq_Real, (real_lt, coq_Real
  -> real_lt -> real_lt -> coq_Real -> real_lt -> real_le) coq_And) sigT

val b5dJ_LogErr_delta_exp :
  coq_Real -> coq_Real -> real_lt -> (coq_Real, (real_lt, coq_Real ->
  coq_Real -> real_lt -> real_lt -> real_le) coq_And) sigT

val b5d3_exp_arch4_C : coq_Q

val b5d3_exp_arch4_C_ge1 : coq_QleT'

val b5d3_exp_arch4_C_all : nat -> coq_QleT'

val b5dK_real_mult_positive_exp :
  coq_Real -> coq_Real -> real_lt -> real_lt -> real_lt

val b5dK_real_abs_plus_one_pos_exp : coq_Real -> real_lt

val b5dK_real_abs_scaling_le_exp :
  coq_Real -> coq_Real -> coq_Real -> coq_Real -> real_lt -> real_lt ->
  real_le

val b5dK_exp_minus_one_linear_closed_exp :
  coq_Real -> real_lt -> (coq_Real, (real_eq, (real_lt, coq_Real -> real_lt
  -> coq_Real -> real_lt -> real_le) coq_And) coq_And) sigT

val b5dK_gdiff_pts_r_exp :
  coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Real -> real_lt -> coq_Q ->
  coq_Q -> coq_QltT -> coq_QltT -> (coq_Real, (real_lt, coq_Real -> real_lt
  -> coq_Real -> real_lt -> (nat, __) sigT) coq_And) sigT

val b5dK_exp_part_bound_closed_r_exp :
  coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Real -> real_lt ->
  (coq_Real, (real_lt, coq_Real -> real_lt -> coq_Real -> real_lt -> real_le)
  coq_And) sigT

val b5d4_const0_eq_zero : real_eq

val b5d4_S_const0_eq_one : real_eq

val b5dE_const1_eq_one : real_eq

val b5dE_q_pos : coq_Q -> real_lt

val b5dE_half_pos_real : real_lt

val b5dE_log_ub_one : coq_Q -> real_lt

val b5dE_S_lt_exp_half : coq_Q -> real_lt

val b5dE_exp_half_le_two : real_le

val b5dE_S_ub_tail_q : coq_Q -> (nat, __) sigT

val b5dH_E_eq_b5aE : coq_Real -> cw_unit -> real_eq

val b5dH_J_zero0 : real_eq

val b5dH_E_zero_of_J_zero : coq_Real -> cw_unit -> real_eq -> real_eq

val b5dH_real_const_qeq : coq_Q -> coq_Q -> real_eq

val b5dH_plus_const_eq : coq_Q -> coq_Q -> real_eq

val b5dL_tkq : coq_Q -> nat -> nat -> coq_Q

val b5dL_qdiv : coq_Q -> nat -> coq_Q

val b5dL_Qnsum : (nat -> coq_Q) -> nat -> coq_Q

val b5dL_tkC : coq_Q -> nat -> nat -> cw_unit

val b5dL_abs_const : coq_Q -> real_eq

val b5dL_mult_const : coq_Q -> coq_Q -> real_eq

val b5dL_bk : coq_Q -> nat -> coq_Q -> nat -> coq_Q

val b5dL_epsQ1 : nat -> coq_Q -> coq_Q

val b5dL_J_grid_premise :
  coq_Q -> nat -> (nat -> coq_Q) -> (nat -> coq_Q) -> (nat -> __ -> cw_unit
  -> cw_unit -> real_le) -> cw_unit -> cw_unit -> real_le

val b5dL_eps_real_lower :
  coq_Real -> real_lt -> (coq_Q, (coq_QltT, real_le) coq_And) sigT

val b5dL_J_zero_on_grid_premise :
  coq_Q -> nat -> coq_Q -> (nat -> __ -> cw_unit -> cw_unit -> real_le) ->
  cw_unit -> real_le

val b5dL_E_rational_zero_premise :
  coq_Q -> (coq_Q -> __ -> (nat, (coq_NatLe, nat -> __ -> cw_unit -> cw_unit
  -> real_le) coq_And) sigT) -> cw_unit -> real_eq

val b5dP_S_diff_closed_r_M_exp_tail :
  coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> nat -> coq_Real ->
  real_lt -> (coq_Real, (real_lt, coq_Real -> real_lt -> coq_Real -> real_lt
  -> real_le) coq_And) sigT

val b5dQ_min_lb :
  coq_Real -> coq_Real -> coq_Real -> real_lt -> real_lt -> real_lt

val b5dQ_Hq32T : coq_QltT

val b5dQ_chain3 : coq_Q -> coq_Q

val b5dQ_chain4 : coq_Q -> coq_Q

val b5dQ_vB : coq_Q -> coq_Q -> coq_Q

val b5dQ_margin_lemma : coq_Q -> coq_QltT

val b5dQ_vSC : coq_Q -> coq_Q -> coq_Q

val b5dQ_vE : coq_Q -> coq_Q -> coq_Q

val b5dQ_lb_E : coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> real_lt

val b5dQ_Hq14T : coq_QltT

val b5dQ_Hq1T : coq_QltT

val b5dQ_S_tk0_eq_one : coq_Q -> nat -> real_eq

val b5dQ_S_lb_tail_k0 : coq_Q -> nat -> (nat, __) sigT

val b5dQ_S_ub_tail_k0 : coq_Q -> nat -> (nat, __) sigT

val b5dQ_S_ub_tail_restate :
  (nat -> coq_Q) -> (nat, __) sigT -> (nat, __) sigT

val b5dQ_S_lb_tail_kS : coq_Q -> nat -> nat -> (nat, __) sigT

val b5dQ_S_ub_tail_kS : coq_Q -> nat -> nat -> (nat, __) sigT

val b5dQ_tkq_Hxr : coq_Q -> nat -> nat -> nat -> coq_QleT'

val b5dQ_xph_unit : coq_Q -> nat -> nat -> cw_unit

val b5dQ_rhs_bk : coq_Q -> nat -> nat -> coq_Q -> real_eq

val b5dQ_J_tk_succ_bridge :
  coq_Q -> nat -> nat -> cw_unit -> cw_unit -> real_eq

val b5dQ_J_cert_wd : coq_Q -> cw_unit -> cw_unit -> real_eq

val b5dQ_step_inst :
  coq_Q -> nat -> nat -> (nat -> coq_QleT') -> cw_unit -> cw_unit -> cw_unit
  -> coq_Real -> real_le -> real_le

val b5dQ_lbSdiff_cE : coq_Q -> coq_Q -> coq_Q

val b5dQ_lbSdiff_cG : coq_Q -> coq_Q -> coq_Q

val b5dQ_lbSdiff_cS : coq_Q -> coq_Q -> coq_Q

val b5dQ_lbSdiff_val : coq_Q -> coq_Q -> coq_Q

val b5dQ_lb_Sdiff :
  coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> nat -> real_lt

val b5dQ_tau : coq_Q -> coq_Q

val b5dQ_kS : coq_Q -> coq_Q

val b5dQ_m4 : coq_Q -> coq_Q -> coq_Q

val b5dQ_delta0 : coq_Q -> coq_Q -> coq_Q

val b5dQ_p4g_leaf_E :
  coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> real_lt

val b5dQ_p4g_leaf_S :
  coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> nat -> real_lt

val b5dQ_p4g_J_tail_lb_var :
  coq_Q -> coq_Q -> nat -> nat -> (nat -> coq_QleT') -> nat -> nat ->
  (coq_Real, (real_lt, (coq_Real -> real_lt -> (nat -> coq_QleT') -> coq_Real
  -> real_lt -> real_le, real_lt) coq_And) coq_And) sigT

val b5dQ_Hstep :
  coq_Q -> coq_Q -> nat -> nat -> (nat -> coq_QleT') -> nat -> nat -> cw_unit
  -> cw_unit -> real_le

val b5dQ_Hmod :
  coq_Q -> coq_Q -> (nat, (coq_NatLe, nat -> __ -> cw_unit -> cw_unit ->
  real_le) coq_And) sigT

val b5dQ_E_rational_zero : coq_Q -> cw_unit -> real_eq

val b5dS_E_pair_close :
  coq_Q -> (nat, (coq_Q, (coq_QltT, __) coq_And) sigT) sigT

val b5dS_E_zero_on_unit : coq_Real -> cw_unit -> real_lt -> real_lt -> real_eq

val pi_triangle_direct_edge : real_eq
