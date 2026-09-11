
type __ = Obj.t

type empty_set = |

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

val max : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

val gmax : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> 'a1

val gmin : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> 'a1

module Nat :
 sig
  val leb : nat -> nat -> bool

  val max : nat -> nat -> nat

  val min : nat -> nat -> nat
 end

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val to_nat : z -> nat

  val of_nat : nat -> z

  val abs : z -> z
 end

val z_lt_dec : z -> z -> sumbool

val z_lt_ge_dec : z -> z -> sumbool

val z_lt_le_dec : z -> z -> sumbool

type q = { qnum : z; qden : positive }

val qcompare : q -> q -> comparison

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qdiv : q -> q -> q

val qlt_le_dec : q -> q -> sumbool

val qarchimedean : q -> positive

val qabs : q -> q

val qmax : q -> q -> q

val qmin : q -> q -> q

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

type 'a not = 'a -> empty_set

type natLe = bool id

val natLe_lift : nat -> nat -> natLe

type qseq = nat -> q

val qlt_bool : q -> q -> bool

type qltT = bool id

val qlt_to_QltT : q -> q -> qltT

type qleT' = bool id

val qle_to_QleT' : q -> q -> qleT'

val qltT_0_1 : qltT

val qltT_0_2 : qltT

val qltT_0_3 : qltT

val qleT'_refl : q -> qleT'

val qleT'_trans : q -> q -> q -> qleT' -> qleT' -> qleT'

val qltT_leT' : q -> q -> qltT -> qleT'

val qleT'_ltT_ltT : q -> q -> q -> qleT' -> qltT -> qltT

val qltT_leT'_ltT : q -> q -> q -> qltT -> qleT' -> qltT

val qleT'_plus_compat : q -> q -> q -> q -> qleT' -> qleT' -> qleT'

val qleT'_plus_nonneg_rT : q -> q -> qleT' -> qleT'

val qltT_plus_ltT : q -> q -> q -> q -> qltT -> qltT -> qltT

val qltT_plus_leT'_ltT : q -> q -> q -> q -> qltT -> qleT' -> qltT

val qleT'_plus_ltT_ltT : q -> q -> q -> q -> qleT' -> qltT -> qltT

val qleT'_mult_compat_l : q -> q -> q -> qleT' -> qleT' -> qleT'

val qleT'_mult_ltT_compat :
  q -> q -> q -> q -> qltT -> qleT' -> qleT' -> qltT -> qltT

val qmult_ltT_0_compat : q -> q -> qltT -> qltT -> qltT

val qeq_leT' : q -> q -> qleT'

type qeqT = bool id

val qeq_imp_qeqT : q -> q -> qeqT

val qabs_nonnegT : q -> qleT'

val qltT_plus_pos_r : q -> q -> qltT -> qltT -> qltT

val qltT_div_pos : q -> q -> qltT -> qltT -> qltT

val qltT_eq_compat_l : q -> q -> q -> qltT -> qltT

val qltT_eq_compat_r : q -> q -> q -> qltT -> qltT

val qltT_mult_ltT_compat_r : q -> q -> q -> qltT -> qltT -> qltT

type cauchy = q -> qltT -> (nat, nat -> nat -> natLe -> natLe -> qltT) sigT

type real = (qseq, cauchy) sigT

type real_eq = q -> qltT -> (nat, nat -> natLe -> qltT) sigT

val real_plus : real -> real -> real

val real_opp : real -> real

val real_zero : real

type real_lt = (q, (qltT, (nat, nat -> natLe -> qltT) sigT) and0) sigT

type real_le = (real_lt, real_eq) or0

val real_lt_trans : real -> real -> real -> real_lt -> real_lt -> real_lt

val sum_abs_prefix : qseq -> nat -> q

val cauchy_bounded : qseq -> cauchy -> q

val real_norm_bounded : real -> (q, (qltT, nat -> qleT') and0) sigT

val real_mult : real -> real -> real

val real_const : q -> real

type real_lim = q -> qltT -> (nat, nat -> __ -> (real_lt, real_lt) and0) sigT

val real_lim_unique :
  (nat -> real) -> real -> real -> real_lim -> real_lim -> real_eq

val q_arch_inv : q -> (nat, __) sigT

val reg_index : (nat -> nat) -> nat -> nat

val reg_mod : qseq -> cauchy -> nat -> nat

val regularize : qseq -> cauchy -> qseq

val regularize_cauchy : qseq -> cauchy -> cauchy

val regularize_same_real : qseq -> cauchy -> real_eq

val regularized_family : (nat -> real) -> nat -> real

val regularized_family_same : (nat -> real) -> nat -> real_eq

val real_eq_refl : real -> real_eq

val real_eq_sym : real -> real -> real_eq -> real_eq

val real_eq_trans : real -> real -> real -> real_eq -> real_eq -> real_eq

val real_one : real

val real_eq_of_zero_diff : real -> real -> real_eq

val real_plus_comm : real -> real -> real_eq

val real_plus_assoc : real -> real -> real -> real_eq

val real_plus_zero : real -> real_eq

val real_plus_opp : real -> real_eq

val real_mult_comm : real -> real -> real_eq

val real_mult_assoc : real -> real -> real -> real_eq

val real_mult_one : real -> real_eq

val real_mult_zero : real -> real_eq

val real_distrib : real -> real -> real -> real_eq

val real_lt_irrefl : real -> real_lt not

val real_le_refl : real -> real_le

val real_lt_eq_lt : real -> real -> real -> real_lt -> real_eq -> real_lt

val real_eq_lt_lt : real -> real -> real -> real_eq -> real_lt -> real_lt

val real_le_trans : real -> real -> real -> real_le -> real_le -> real_le

val real_eq_minus_compat :
  real -> real -> real -> real -> real_eq -> real_eq -> real_eq

val regularized_family_double_cauchy :
  (nat -> real) -> (q -> qltT -> (nat, nat -> nat -> __ -> __ -> (real_lt,
  real_lt) and0) sigT) -> q -> qltT -> (nat, nat -> nat -> __ -> __ ->
  (real_lt, real_lt) and0) sigT

val regularized_diag_cauchy :
  (nat -> real) -> (q -> qltT -> (nat, nat -> nat -> __ -> __ -> (real_lt,
  real_lt) and0) sigT) -> cauchy

val regularized_diag_close :
  (nat -> real) -> (q -> qltT -> (nat, nat -> nat -> __ -> __ -> (real_lt,
  real_lt) and0) sigT) -> q -> qltT -> (nat, nat -> __ -> (nat, nat -> __ ->
  qltT) sigT) sigT

val real_cauchy_complete :
  (nat -> real) -> (q -> qltT -> (nat, nat -> nat -> __ -> __ -> (real_lt,
  real_lt) and0) sigT) -> (real, real_lim) sigT

val real_lt_le_trans : real -> real -> real -> real_lt -> real_le -> real_lt

val real_le_lt_trans : real -> real -> real -> real_le -> real_lt -> real_lt

val real_le_antisym : real -> real -> real_le -> real_le -> real_eq

val real_lt_le_iff : real -> real -> (real_lt, real id) or0 -> real_le

val real_lt_plus_compat :
  real -> real -> real -> real -> real_lt -> real_lt -> real_lt

val q_pow : q -> nat -> q

val q_fact : nat -> q

val exp_partial : nat -> q -> q

val q_arch_geom : q -> (nat, nat -> natLe -> qleT') sigT

val arch_decay : q -> q -> qleT' -> qltT -> (nat, qltT) sigT

val exp_partial_cauchy : q -> q -> (nat, nat -> nat -> __ -> __ -> qltT) sigT

val exp_series : nat -> q -> q

val exp_partial_cauchy_bounded :
  q -> q -> qleT' -> qltT -> (nat, nat -> nat -> natLe -> natLe -> q -> qleT'
  -> qltT) sigT

val exp_series_arch : q -> qleT' -> (q, (qleT', nat -> qleT') and0) sigT

val cauchy_real_exp : real -> real

val cauchy_real_exp_zero : real_eq

val sum_upto : nat -> (nat -> q) -> q

val exp_partial_tail_small : q -> q -> qleT' -> qleT' -> (nat, __) sigT

val cauchy_real_exp_pos : real -> real_lt

val real_abs : real -> real

val real_metric : real -> real -> real

val real_abs_opp : real -> real_eq

val real_inv_pos : real -> real_lt -> real

val real_inv_pos_correct : real -> real_lt -> real_eq

val real_inv_pos_pos : real -> real_lt -> real_lt

module RealSetoid :
 sig
  val real_eq_le : real -> real -> real_eq -> real_le

  val real_lt_le_iff_req : real -> real -> (real_lt, real_eq) or0 -> real_le

  val real_eq_plus_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_eq

  val real_eq_opp_compat : real -> real -> real_eq -> real_eq

  val real_eq_mult_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_eq

  val real_eq_abs_compat : real -> real -> real_eq -> real_eq

  val real_lt_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_lt -> real_lt

  val real_le_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_le -> real_le

  val real_lt_id_l : real -> real -> real -> real_eq -> real_lt -> real_lt

  val real_lt_id_r : real -> real -> real -> real_eq -> real_lt -> real_lt

  val real_le_id_l : real -> real -> real -> real_eq -> real_le -> real_le

  val real_le_id_r : real -> real -> real -> real_eq -> real_le -> real_le

  val real_metric_sym : real -> real -> real_eq

  val real_metric_zero : real -> real -> real_eq -> real_eq

  val real_metric_lt_const_to_minus :
    (nat -> real) -> nat -> nat -> q -> real_lt -> real_lt

  val real_metric_lt_const_to_minus_comm :
    (nat -> real) -> nat -> nat -> q -> real_lt -> real_lt

  val real_cauchy_complete_metric :
    (nat -> real) -> (real -> real_lt -> (nat, nat -> nat -> __ -> __ ->
    real_lt) sigT) -> (real, real_lim) sigT

  val real_metric_pos_eps : real -> real -> real -> real_lt -> real_le

  val real_metric_triangle_eps :
    real -> real -> real -> real -> real_lt -> real_le

  val eq_Id : 'a1 -> 'a1 -> 'a1 id

  val le_to_NatLe : nat -> nat -> natLe

  val real_cauchy_complete_metric_natle :
    (nat -> real) -> (real -> real_lt -> (nat, nat -> nat -> natLe -> natLe
    -> real_lt) sigT) -> (real, real_lim) sigT

  val real_eq_plus_compat_adapt :
    real -> real -> real -> real -> real_eq -> real_eq -> real_eq

  val real_eq_mult_compat_adapt :
    real -> real -> real -> real -> real_eq -> real_eq -> real_eq
 end

val exp_trunc_arch_seq :
  (nat -> q) -> (nat -> q) -> q -> q -> qleT' -> (nat -> qleT') -> (nat ->
  qleT') -> qltT -> (nat, nat -> __ -> qltT) sigT

val cauchy_real_exp_plus : real -> real -> real_eq

val cauchy_real_exp_gt_one : real -> real_lt -> real_lt

val real_lt_opp_plus : real -> real -> real_lt -> real_lt

val real_mult_pos_compat : real -> real -> real_lt -> real_lt -> real_lt

val cauchy_real_exp_minus_one_pos : real -> real_lt -> real_lt

val cauchy_real_exp_wd : real -> real -> real_eq -> real_eq

val real_mult_minus_factor : real -> real -> real_eq

val cauchy_real_exp_mono : real -> real -> real_lt -> real_lt

val real_arch : real -> (nat, (__, real_lt) and0) sigT

val cauchy_real_exp_gt_const : nat -> real_lt

val real_abs_diff_le_lift : real -> real -> q -> q -> nat -> real_lt

val real_inv_unique : real -> real -> real -> real_eq -> real_eq -> real_eq

val exp_neg_recip : real -> real_lt -> real_eq

val real_const_pos : q -> qltT -> real_lt

val real_inv_lt_contra :
  real -> real -> real_lt -> real_lt -> real_lt -> real_lt

val q_eps16_posT : q -> qltT

val log_testA_eps : real -> q -> q -> q -> bool

val log_testB_eps : real -> q -> q -> q -> bool

val log_m_eps : q -> q -> q

val log_d4_eps : q -> q

val log_K1_eps : q -> q -> q -> nat

val log_K2_eps : real -> q -> q -> q -> nat

val log_q_eps : q -> q -> q -> q

val log_r_eps : real -> q -> q -> q -> q

val log_testA_eps_true_lt : real -> q -> q -> q -> real_lt

val log_testB_eps_true_gt : real -> q -> q -> q -> real_lt

val log_scan :
  real -> q -> q -> q -> nat -> (((q, q) prod, qltT) sigT, bool) prod

val log_scan_spec :
  real -> q -> q -> q -> nat -> real_lt -> real_lt -> ((bool id, (real_lt,
  (real_lt, qeqT) and0) and0) and0, (bool id, nat -> __ -> qleT') and0) or0

val exp_lower_q : real -> real_lt -> (nat, (__, real_lt) and0) sigT

val exp_upper_q : real -> real_lt -> (nat, (__, real_lt) and0) sigT

val log_lower : real -> real_lt -> q

val log_upper : real -> real_lt -> q

val q_pow_arch : q -> q -> (nat, __) sigT

val real_const_lt : q -> q -> real_lt

val real_lt_pt_lt : real -> real -> real_lt -> (nat, __) sigT

val exp_const_lt : q -> q -> real_lt

val approx_span_pt :
  real -> q -> q -> q -> q -> real_lt -> real_lt -> (nat -> qleT') -> (nat,
  __) sigT

val real_abs_lift : q -> real -> q -> q -> nat -> real_lt

val approx_def_test : real -> q -> q -> nat -> real_lt

val approx_root :
  real -> real_lt -> q -> (q, (qltT, (qltT, real_lt) and0) and0) sigT

val log_eps : nat -> q

val log_seq : real -> real_lt -> nat -> q

val approx_root_pt_bound : real -> real_lt -> nat -> (nat, __) sigT

val exp_pos_shape :
  real -> (q, (qltT, (nat, nat -> __ -> qltT) sigT) and0) sigT

val log_seq_cauchy : real -> real_lt -> cauchy

val cw_log : real -> real_lt -> real

val exp_series_arch_shape : q -> qleT' -> (q, (qleT', nat -> qleT') and0) sigT

val cw_log_exp_right : real -> real_lt -> real_eq

val real_lt_not_eq : real -> real -> real_lt -> real_eq not

val real_weak_trich : real -> real -> real_lt not -> real_lt not -> real_eq

val log_inv_one_thm : real_lt -> real_eq

val log_inv_mult_thm :
  real -> real -> real_lt -> real_lt -> real_lt -> real_eq

val real_mult_lt_compat :
  real -> real -> real -> real_lt -> real_lt -> real_lt

val real_mult_lt_compat_l :
  real -> real -> real -> real_lt -> real_lt -> real_lt

val real_inv_pos_lt_contra :
  real -> real -> real_lt -> real_lt -> real_lt -> real_lt

val real_lt_plus_translate : real -> real -> real -> real_lt -> real_lt

val real_lt_plus_compat_lt_le :
  real -> real -> real -> real -> real_lt -> real_le -> real_lt

val real_log_lt_mono :
  real -> real -> real_lt -> real_lt -> real_lt -> real_lt

val real_le_plus_compat :
  real -> real -> real -> real -> real_le -> real_le -> real_le

val real_opp_lt_compat : real -> real -> real_lt -> real_lt

val real_lt_zero_opp : real -> real_lt -> real_lt

val real_opp_le_compat : real -> real -> real_le -> real_le

val real_inv_pos_ext :
  real -> real -> real_lt -> real_lt -> real_eq -> real_eq

val real_inv_pos_le_compat :
  real -> real -> real_lt -> real_lt -> real_le -> real_le

val real_le_mult_compat :
  real -> real -> real -> real_lt -> real_le -> real_le

val real_le_mult_compat_weak :
  real -> real -> real -> real_le -> real_le -> real_le

val real_lt_zero_one : real_lt

val real_plus_positive : real -> real -> real_lt -> real_lt -> real_lt

val real_mult_positive : real -> real -> real_lt -> real_lt -> real_lt

val real_min : real -> real -> real

val real_max : real -> real -> real

val real_abs_zero_req : real_eq

val real_abs_mult_req : real -> real -> real_eq

val real_abs_pos_req : real -> real_lt -> real_eq

val real_abs_nonneg_le_eps : real -> real -> real_lt -> real_le

val real_abs_triangle_le_eps : real -> real -> real -> real_lt -> real_le

val real_eps_witness :
  real -> real_lt -> (q, (qltT, (nat, nat -> __ -> qltT) sigT) and0) sigT

val real_min_le_l_eps : real -> real -> real -> real_lt -> real_le

val real_min_le_r_eps : real -> real -> real -> real_lt -> real_le

val real_min_pos : real -> real -> real_lt -> real_lt -> real_lt

val real_r_max_le_l_eps : real -> real -> real -> real_lt -> real_le

val real_r_max_le_r_eps : real -> real -> real -> real_lt -> real_le

val real_r_max_l_iff : real -> real -> real_le -> real_eq

val real_pos_part : real -> real

val real_pos_part_def : real -> real_eq

val real_pos_part_nonneg_eps : real -> real -> real_lt -> real_le

val real_r_if : ('a1, 'a1 not) or0 -> real -> real -> real

val real_r_if_true : ('a1, 'a1 not) or0 -> real -> real -> 'a1 -> real_eq

val real_r_if_false : ('a1, 'a1 not) or0 -> real -> real -> 'a1 not -> real_eq

val real_exp_neg : real -> real

val real_exp_neg_pos : real -> real_lt

val real_exp_neg_zero : real_eq

val real_opp_plus : real -> real -> real_eq

val real_exp_neg_plus : real -> real -> real_eq

val real_exp_neg_decr : real -> real -> real_lt -> real_lt

val real_exp_neg_le_decr : real -> real -> real_le -> real_le

val real_log : real -> real_lt -> real

val real_log_mult : real -> real -> real_lt -> real_lt -> real_eq

val real_log_one : real_lt -> real_eq

val real_log_inv : real -> real_lt -> real

val real_log_inv_log : real -> real_lt -> real_eq

val real_exp_neg_log_inv : real -> real_lt -> real_eq

module RealInterfaceEnhancedMod :
 sig
  type 'r coq_RealInterfaceEnhancedSetoid = { req_refl : ('r -> __);
                                              req_sym : ('r -> 'r -> __ -> __);
                                              req_trans : ('r -> 'r -> 'r ->
                                                          __ -> __ -> __);
                                              zero : 'r; one : 'r;
                                              plus : ('r -> 'r -> 'r);
                                              mult : ('r -> 'r -> 'r);
                                              opp : ('r -> 'r);
                                              abs : ('r -> 'r);
                                              req_plus_compat : ('r -> 'r ->
                                                                'r -> 'r ->
                                                                __ -> __ ->
                                                                __);
                                              req_mult_compat : ('r -> 'r ->
                                                                'r -> 'r ->
                                                                __ -> __ ->
                                                                __);
                                              req_opp_compat : ('r -> 'r ->
                                                               __ -> __);
                                              req_abs_compat : ('r -> 'r ->
                                                               __ -> __);
                                              req_lt_compat : ('r -> 'r -> 'r
                                                              -> 'r -> __ ->
                                                              __ -> __ -> __);
                                              req_le_compat : ('r -> 'r -> 'r
                                                              -> 'r -> __ ->
                                                              __ -> __ -> __);
                                              plus_assoc : ('r -> 'r -> 'r ->
                                                           __);
                                              plus_comm : ('r -> 'r -> __);
                                              plus_zero : ('r -> __);
                                              plus_opp : ('r -> __);
                                              mult_assoc : ('r -> 'r -> 'r ->
                                                           __);
                                              mult_comm : ('r -> 'r -> __);
                                              mult_one : ('r -> __);
                                              distrib : ('r -> 'r -> 'r -> __);
                                              mult_zero : ('r -> __);
                                              lt_irrefl : ('r -> __ not);
                                              lt_trans : ('r -> 'r -> 'r ->
                                                         __ -> __ -> __);
                                              le_refl : ('r -> __);
                                              le_trans : ('r -> 'r -> 'r ->
                                                         __ -> __ -> __);
                                              le_antisym : ('r -> 'r -> __ ->
                                                           __ -> __);
                                              le_lt_trans : ('r -> 'r -> 'r
                                                            -> __ -> __ -> __);
                                              lt_le_trans : ('r -> 'r -> 'r
                                                            -> __ -> __ -> __);
                                              lt_le_iff : ('r -> 'r -> (__,
                                                          __) or0 -> __);
                                              le_id_l : ('r -> 'r -> 'r -> __
                                                        -> __ -> __);
                                              le_id_r : ('r -> 'r -> 'r -> __
                                                        -> __ -> __);
                                              lt_id_l : ('r -> 'r -> 'r -> __
                                                        -> __ -> __);
                                              lt_id_r : ('r -> 'r -> 'r -> __
                                                        -> __ -> __);
                                              inv_pos : ('r -> __ -> 'r);
                                              inv_pos_correct : ('r -> __ ->
                                                                __);
                                              one_pos : __;
                                              lt_plus_compat : ('r -> 'r ->
                                                               'r -> 'r -> __
                                                               -> __ -> __);
                                              le_plus_compat : ('r -> 'r ->
                                                               'r -> 'r -> __
                                                               -> __ -> __);
                                              plus_positive : ('r -> 'r -> __
                                                              -> __ -> __);
                                              mult_positive : ('r -> 'r -> __
                                                              -> __ -> __);
                                              lt_mult_compat : ('r -> 'r ->
                                                               'r -> __ -> __
                                                               -> __);
                                              le_mult_compat : ('r -> 'r ->
                                                               'r -> __ -> __
                                                               -> __);
                                              le_mult_compat_weak : ('r -> 'r
                                                                    -> 'r ->
                                                                    __ -> __
                                                                    -> __);
                                              opp_lt_compat : ('r -> 'r -> __
                                                              -> __);
                                              lt_zero_opp : ('r -> __ -> __);
                                              opp_le_compat : ('r -> 'r -> __
                                                              -> __);
                                              inv_pos_pos : ('r -> __ -> __);
                                              inv_pos_ext : ('r -> 'r -> __
                                                            -> __ -> __ -> __);
                                              inv_pos_le_compat : ('r -> 'r
                                                                  -> __ -> __
                                                                  -> __ -> __);
                                              min : ('r -> 'r -> 'r);
                                              min_le_l : ('r -> 'r -> 'r ->
                                                         __ -> __);
                                              min_le_r : ('r -> 'r -> 'r ->
                                                         __ -> __);
                                              min_pos : ('r -> 'r -> __ -> __
                                                        -> __);
                                              r_max : ('r -> 'r -> 'r);
                                              r_max_le_l : ('r -> 'r -> 'r ->
                                                           __ -> __);
                                              r_max_le_r : ('r -> 'r -> 'r ->
                                                           __ -> __);
                                              r_max_l_iff : ('r -> 'r -> __
                                                            -> __);
                                              r_max_r_iff : ('r -> 'r -> __
                                                            -> __);
                                              pos_test_lt : ('r -> __ -> __);
                                              lt_pos_test : ('r -> __ -> __);
                                              pos_part : ('r -> 'r);
                                              pos_part_def : ('r -> __);
                                              pos_part_nonneg : ('r -> 'r ->
                                                                __ -> __);
                                              r_if : (__ -> (__, __ not) or0
                                                     -> 'r -> 'r -> 'r);
                                              r_if_true : (__ -> (__, __ not)
                                                          or0 -> 'r -> 'r ->
                                                          __ -> __);
                                              r_if_false : (__ -> (__, __
                                                           not) or0 -> 'r ->
                                                           'r -> __ not -> __);
                                              abs_nonneg : ('r -> 'r -> __ ->
                                                           __);
                                              abs_triangle : ('r -> 'r -> 'r
                                                             -> __ -> __);
                                              abs_zero : __;
                                              abs_mult : ('r -> 'r -> __);
                                              abs_opp : ('r -> __);
                                              abs_pos : ('r -> __ -> __);
                                              exp_neg : ('r -> 'r);
                                              exp_neg_pos : ('r -> __);
                                              exp_neg_zero : __;
                                              exp_neg_plus : ('r -> 'r -> __);
                                              exp_neg_decr : ('r -> 'r -> __
                                                             -> __);
                                              exp_neg_le_decr : ('r -> 'r ->
                                                                __ -> __);
                                              log : ('r -> __ -> 'r);
                                              log_mult : ('r -> 'r -> __ ->
                                                         __ -> __);
                                              log_one : (__ -> __);
                                              log_le_linear_eps : ('r -> __
                                                                  -> 'r -> __
                                                                  -> __);
                                              log_inv : ('r -> __ -> 'r);
                                              log_inv_log : ('r -> __ -> __);
                                              exp_neg_log_inv : ('r -> __ ->
                                                                __);
                                              metric : ('r -> 'r -> 'r);
                                              metric_sym : ('r -> 'r -> __);
                                              metric_pos : ('r -> 'r -> 'r ->
                                                           __ -> __);
                                              metric_zero : ('r -> 'r -> __
                                                            -> __);
                                              metric_triangle : ('r -> 'r ->
                                                                'r -> 'r ->
                                                                __ -> __);
                                              lim_unique : ((nat -> 'r) -> 'r
                                                           -> 'r -> __ -> __
                                                           -> __);
                                              cauchy_complete : ((nat -> 'r)
                                                                -> ('r -> __
                                                                -> (nat, nat
                                                                -> nat ->
                                                                natLe ->
                                                                natLe -> __)
                                                                sigT) -> ('r,
                                                                __) sigT) }

  type 'r req = __

  val req_refl : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 req

  val req_sym :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 req -> 'a1 req

  val req_trans :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 req ->
    'a1 req -> 'a1 req

  val zero : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1

  val one : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1

  val plus : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1

  val mult : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1

  val opp : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1

  type 'r lt = __

  type 'r le = __

  val req_plus_compat :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    req -> 'a1 req -> 'a1 req

  val req_opp_compat :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 req -> 'a1 req

  val plus_assoc :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 req

  val plus_comm : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 req

  val plus_zero : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 req

  val plus_opp : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 req

  val mult_comm : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 req

  val le_antisym :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 le -> 'a1 le ->
    'a1 req

  val lt_le_iff :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> ('a1 lt, 'a1 req)
    or0 -> 'a1 le

  val inv_pos : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 lt -> 'a1

  val inv_pos_correct :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 lt -> 'a1 req

  val one_pos : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 lt

  val mult_positive :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 lt -> 'a1 lt ->
    'a1 lt

  val log : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 lt -> 'a1

  val log_mult :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 lt -> 'a1 lt ->
    'a1 req

  val log_one : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 lt -> 'a1 req

  val real_r_max_r_iff : real -> real -> real_le -> real_eq

  val real_exp_ge_linear_eps : real -> real -> real_lt -> real_le

  val real_log_le_linear_eps : real -> real -> real_lt -> real_lt -> real_le

  val coq_RealEnhancedReal : real coq_RealInterfaceEnhancedSetoid
 end

val real_opp_mult : real -> real -> real_eq

val real_mult_div : real -> real -> real_lt -> real_eq

val real_opp_opp : real -> real_eq

val real_hpq1 : real -> real -> real_lt -> real_eq

val real_hpq2 : real -> real -> real -> real_lt -> real_eq

val real_gibbs_core_eps :
  real -> real -> real_lt -> real_lt -> real -> real_lt -> real_le

val real_list_sum : ('a1 -> real) -> 'a1 list -> real

val real_list_sum_ext :
  ('a1 -> real) -> ('a1 -> real) -> 'a1 list -> ('a1 -> real_eq) -> real_eq

val real_plus_swap_mid : real -> real -> real -> real -> real_eq

val real_list_sum_add : ('a1 -> real) -> ('a1 -> real) -> 'a1 list -> real_eq

val real_list_sum_linear : real -> ('a1 -> real) -> 'a1 list -> real_eq

val real_list_sum_linear_r : real -> ('a1 -> real) -> 'a1 list -> real_eq

val real_opp_zero : real_eq

val real_list_sum_opp : ('a1 -> real) -> 'a1 list -> real_eq

val real_list_sum_le :
  ('a1 -> real) -> ('a1 -> real) -> 'a1 list -> ('a1 -> real_le) -> real_le

val real_kl_term : real -> real -> real_lt -> real_lt -> real

val real_gibbs_inequality_eps :
  'a1 list -> ('a1 -> real) -> ('a1 -> real) -> ('a1 -> real_lt) -> ('a1 ->
  real_lt) -> real_eq -> real_eq -> real -> real_lt -> real_le

val real_log_wd : real -> real -> real_lt -> real_lt -> real_eq -> real_eq

val real_distrib_r_local : real -> real -> real -> real_eq

val real_boltzmann_dist_r :
  ('a1 -> real) -> real -> real_lt -> real -> real_lt -> 'a1 -> real

val real_boltzmann_dist_r_pos :
  ('a1 -> real) -> real -> real_lt -> real -> real_lt -> 'a1 -> real_lt

val real_lt_le_bridge : real -> real -> real_lt -> real_le

val real_eq_le_bridge : real -> real -> real_eq -> real_le

val real_log_le_mono :
  real -> real -> real_lt -> real_lt -> real_le -> real_le

type real_le_b = real -> real_lt -> real_lt

val real_lt_plus_r_zero : real -> real -> real_lt -> real_lt

val real_le_closure_b :
  real -> real -> real -> real_lt -> (real -> real_lt -> real_le) -> real_le_b

val real_le_closure_b_one :
  real -> real -> (real -> real_lt -> real_le) -> real_le_b

val real_log_le_linear_B : real -> real_lt -> real_le_b

val gibbsd_lt_add_opp_r :
  real -> real -> real -> real_lt -> real_lt -> real_lt

val gibbsd_le_b_opp : real -> real -> real_le_b -> real_le_b

val gibbsd_le_b_id_l :
  real -> real -> real -> real_eq -> real_le_b -> real_le_b

val gibbsd_minus_flip : real -> real -> real_eq

val gibbsd_le_b_mult_pos_r :
  real -> real -> real -> real_lt -> real_le_b -> real_le_b

val gibbsd_p_mult_ratio : real -> real -> real_lt -> real_eq

val gibbsd_p_minus_ratio : real -> real -> real_lt -> real_eq

val gibbsd_two_pos : real_lt

val gibbsd_half : real

val gibbsd_half_pos : real_lt

val gibbsd_half_sum : real -> real_eq

val gibbsd_list_sum_le_b :
  ('a1 -> real) -> ('a1 -> real) -> 'a1 list -> ('a1 -> real_le_b) ->
  real_le_b

val gibbsd_list_sum_minus :
  ('a1 -> real) -> ('a1 -> real) -> 'a1 list -> real_eq

val gibbsd_gibbs_pointwise_B :
  ('a1 -> real) -> ('a1 -> real) -> 'a1 -> real_lt -> real_lt -> real_le_b

val gibbsd_gibbs_inequality :
  'a1 list -> ('a1 -> real) -> ('a1 -> real) -> ('a1 -> real_lt) -> ('a1 ->
  real_lt) -> real_eq -> real_eq -> real_le_b

val logd_req_plus_zero_l :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1
  RealInterfaceEnhancedMod.req

val logd_req_opp_opp :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1
  RealInterfaceEnhancedMod.req

val logd_req_plus_zero_r :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1
  -> 'a1 RealInterfaceEnhancedMod.req -> 'a1 RealInterfaceEnhancedMod.req

val logd_log_compat_of_mono :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> ('a1 -> 'a1
  -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.lt ->
  'a1 RealInterfaceEnhancedMod.le -> 'a1 RealInterfaceEnhancedMod.le) -> 'a1
  -> 'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1
  RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.req -> 'a1
  RealInterfaceEnhancedMod.req

val logd_log_inv_one_inv_of_compat :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> ('a1 -> 'a1
  -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.lt ->
  'a1 RealInterfaceEnhancedMod.req -> 'a1 RealInterfaceEnhancedMod.req) ->
  'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.lt
  -> 'a1 RealInterfaceEnhancedMod.req

val logd_log_compat_real :
  real -> real -> real RealInterfaceEnhancedMod.lt -> real
  RealInterfaceEnhancedMod.lt -> real RealInterfaceEnhancedMod.req -> real
  RealInterfaceEnhancedMod.req

val logd_log_inv_one_inv_real :
  real -> real RealInterfaceEnhancedMod.lt -> real
  RealInterfaceEnhancedMod.lt -> real RealInterfaceEnhancedMod.req

val logd_le_b_id_r : real -> real -> real -> real_le_b -> real_eq -> real_le_b

val logd_log_le_linear_eps : real -> real -> real_lt -> real_lt -> real_le

val logd_log_le_linear_B : real -> real_lt -> real_le_b

val logd_log_lt_mono_real :
  real -> real -> real_lt -> real_lt -> real_lt -> real_lt

val logd_log_two_pos_real : real_lt

val logd_kl_term_minus_form : real -> real -> real_lt -> real_lt -> real_eq

val logd_list_sum_kl_minus_form :
  'a1 list -> ('a1 -> real) -> ('a1 -> real) -> ('a1 -> real_lt) -> ('a1 ->
  real_lt) -> real_eq

val logd_gibbs_inequality_minus_B :
  'a1 list -> ('a1 -> real) -> ('a1 -> real) -> ('a1 -> real_lt) -> ('a1 ->
  real_lt) -> real_eq -> real_eq -> real_le_b

val logd_gibbs_inequality_minus_eps :
  'a1 list -> ('a1 -> real) -> ('a1 -> real) -> ('a1 -> real_lt) -> ('a1 ->
  real_lt) -> real_eq -> real_eq -> real -> real_lt -> real_le

val logd_gibbs_sum_eps_boltzmann_list :
  ('a1 -> real) -> real -> real_lt -> real -> real_lt -> 'a1 list -> ('a1 ->
  real) -> ('a1 -> real_lt) -> real_eq -> real_eq -> real -> real_lt ->
  real_le
