
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

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

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

val max : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat :
 sig
  val leb : nat -> nat -> bool

  val max : nat -> nat -> nat
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
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val mul : positive -> positive -> positive
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

  val abs : z -> z
 end

type q = { qnum : z; qden : positive }

val qcompare : q -> q -> comparison

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qdiv : q -> q -> q

val qabs : q -> q

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

type 'a not = 'a -> empty_set

val id_sym : 'a1 -> 'a1 -> 'a1 id -> 'a1 id

type 'a inT =
| InT_here of 'a list
| InT_next of 'a * 'a list * 'a inT

type natLe = bool id

val natLe_lift : nat -> nat -> natLe

type qseq = nat -> q

type qltT = bool id

val qlt_to_QltT : q -> q -> qltT

type qleT' = bool id

val qle_to_QleT' : q -> q -> qleT'

val qltT_0_2 : qltT

val qleT'_trans : q -> q -> q -> qleT' -> qleT' -> qleT'

val qleT'_ltT_ltT : q -> q -> q -> qleT' -> qltT -> qltT

val qltT_leT'_ltT : q -> q -> q -> qltT -> qleT' -> qltT

val qltT_plus_ltT : q -> q -> q -> q -> qltT -> qltT -> qltT

val qleT'_mult_ltT_compat :
  q -> q -> q -> q -> qltT -> qleT' -> qleT' -> qltT -> qltT

val qmult_ltT_0_compat : q -> q -> qltT -> qltT -> qltT

val qeq_leT' : q -> q -> qleT'

val qabs_nonnegT : q -> qleT'

val qltT_div_pos : q -> q -> qltT -> qltT -> qltT

val qltT_eq_compat_l : q -> q -> q -> qltT -> qltT

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

val real_le_refl : real -> real_le

val real_lt_eq_lt : real -> real -> real -> real_lt -> real_eq -> real_lt

val real_eq_lt_lt : real -> real -> real -> real_eq -> real_lt -> real_lt

val real_le_trans : real -> real -> real -> real_le -> real_le -> real_le

val real_lt_le_trans : real -> real -> real -> real_lt -> real_le -> real_lt

val real_lt_le_iff : real -> real -> (real_lt, real id) or0 -> real_le

val real_lt_plus_compat :
  real -> real -> real -> real -> real_lt -> real_lt -> real_lt

val real_abs : real -> real

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

  val real_lt_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_lt -> real_lt

  val real_le_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_le -> real_le

  val real_lt_id_l : real -> real -> real -> real_eq -> real_lt -> real_lt

  val real_lt_id_r : real -> real -> real -> real_eq -> real_lt -> real_lt

  val real_le_id_l : real -> real -> real -> real_eq -> real_le -> real_le

  val real_le_id_r : real -> real -> real -> real_eq -> real_le -> real_le
 end

val real_lt_opp_plus : real -> real -> real_lt -> real_lt

val real_mult_pos_compat : real -> real -> real_lt -> real_lt -> real_lt

val real_mult_lt_compat :
  real -> real -> real -> real_lt -> real_lt -> real_lt

val real_mult_lt_compat_l :
  real -> real -> real -> real_lt -> real_lt -> real_lt

val real_inv_pos_lt_contra :
  real -> real -> real_lt -> real_lt -> real_lt -> real_lt

val real_lt_plus_translate : real -> real -> real -> real_lt -> real_lt

val real_lt_plus_compat_lt_le :
  real -> real -> real -> real -> real_lt -> real_le -> real_lt

val real_le_plus_compat :
  real -> real -> real -> real -> real_le -> real_le -> real_le

val real_inv_pos_ext :
  real -> real -> real_lt -> real_lt -> real_eq -> real_eq

val real_inv_pos_le_compat :
  real -> real -> real_lt -> real_lt -> real_le -> real_le

val real_le_mult_compat :
  real -> real -> real -> real_lt -> real_le -> real_le

val real_le_mult_compat_weak :
  real -> real -> real -> real_le -> real_le -> real_le

val real_lt_zero_one : real_lt

val real_abs_zero_req : real_eq

val real_abs_mult_req : real -> real -> real_eq

val real_abs_pos_req : real -> real_lt -> real_eq

val real_abs_triangle_le_eps : real -> real -> real -> real_lt -> real_le

val real_opp_plus : real -> real -> real_eq

val real_opp_mult : real -> real -> real_eq

val real_opp_mult_r : real -> real -> real_eq

val real_mult_opp_l : real -> real -> real_eq

val real_opp_opp : real -> real_eq

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

val real_list_sum_nonneg :
  ('a1 -> real) -> 'a1 list -> ('a1 -> real_le) -> real_le

val real_of_nat : nat -> real

val real_abs_eq_compat : real -> real -> real_eq -> real_eq

val real_le_mult_compat_r :
  real -> real -> real -> real_le -> real_le -> real_le

val real_minus_r : real -> real -> real

val real_le_from_lt_aux : real -> real -> real_lt -> real_le

val real_le_mult_compat_l_aux :
  real -> real -> real -> real_lt -> real_le -> real_le

val real_le_plus_nonneg_r_aux : real -> real -> real_le -> real_le

val real_le_minus_nonneg_aux : real -> real -> real_le -> real_le

val real_abs_minus_r_nonneg_aux : real -> real -> real_le -> real_eq

val kv_id_transport : 'a1 -> 'a1 -> 'a2 -> 'a1 id -> 'a2

val z_keep : 'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> bool) -> 'a1 -> real

val kv_ofnat_nonneg : nat -> real_le

val kv_ofnat_S_pos : nat -> real_lt

val kv_N_pos :
  'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) ->
  ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> real_lt

val kv_single_le_sum :
  ('a1 -> real) -> 'a1 -> 'a1 list -> 'a1 inT -> ('a1 -> real_le) -> real_le

val z_keep_pos :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
  bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> real_lt

val k_ev :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
  bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> 'a1 -> real

val invZK :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
  bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> real

val tail_row :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> bool) -> 'a1 -> real

val tv_row :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
  bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> real

val lstep : 'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real) -> 'a1 -> real

val kev_iter :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
  bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> nat -> ('a1 -> real) -> 'a1
  -> real

val k_iter :
  'a1 list -> ('a1 -> 'a1 -> real) -> nat -> ('a1 -> real) -> 'a1 -> real

val ddist : 'a1 list -> ('a1 -> real) -> ('a1 -> real) -> real

val kv_plus_zero_l : real -> real_eq

val kv_one_mult_l : real -> real_eq

val kv_two_R_pos : real_lt

val kv_three_R_pos : real_lt

val kv_distrib_r : real -> real -> real -> real_eq

val kv_abs_nonneg_id : real -> real_le -> real_eq

val kv_sum_zero_list : 'a1 list -> real_eq

val kv_sum_const_list : real -> 'a1 list -> real_eq

val kv_inv_absorb : real -> real_lt -> real -> real_eq

val kv_plus_self_two : real -> real_eq

val kv_plus_self_three : real -> real_eq

val kv_merge_regroup : real -> real -> real -> real_eq

val kv_abs_triangle_list_eps :
  ('a1 -> real) -> 'a1 list -> real -> real_lt -> real_le

val kv_swap_list : ('a1 -> 'a1 -> real) -> 'a1 list -> 'a1 list -> real_eq

val kv_share_pos :
  'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) ->
  ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> real -> real_lt ->
  real_lt

val tvL : 'a1 list -> ('a1 -> real) -> ('a1 -> real) -> real

val kv_ZK_plus_tail :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> bool) ->
  'a1 -> real_eq

val kv_tail_one_minus :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> bool) ->
  'a1 -> real_eq

val kv_ZK_le_one :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
  real_lt) -> ('a1 -> bool) -> 'a1 -> real_le

val kv_invZ_ge_one :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
  real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 ->
  real_le

val kv_K_le_Kev_scaled :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
  real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 ->
  'a1 -> real_le

val kv_summand_eq :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
  bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> 'a1 -> real_eq

val kv_summand_scaled :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
  bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> 'a1 -> real_eq

val kv_kev_row_one :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
  bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> real_eq

val kv_gsum_scaled :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
  bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> real_eq

val kv_scaledZ_tail :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
  real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 ->
  real_eq

val kv_tvrow_pointwise :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
  real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 ->
  'a1 -> real_eq

val kv_tvrow_split :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
  real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 ->
  real_eq

val kev_row_tv_exact :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
  real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 ->
  real_eq

val kev_row_tv_bound :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
  real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 ->
  real_le

val kev_row_tv_one_minus_Z :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
  real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 ->
  real_eq

val kv_lstep_minus_pt2 :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real) -> ('a1 -> real) -> 'a1
  -> real_eq

val kv_lstep2_minus_pt :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real) -> ('a1 -> real)
  -> 'a1 -> real_eq

val kv_D_zero : 'a1 list -> ('a1 -> real) -> real_eq

val kv_lstep_norm :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> real) ->
  real_eq

val kv_lstep_nonneg :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_le) -> ('a1 ->
  real) -> ('a1 -> real_le) -> 'a1 -> real_le

val kv_K_ev_nonneg :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
  bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> 'a1 -> real_le

val kv_kev_iter_norm :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
  bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> nat -> ('a1 -> real) ->
  real_eq -> real_eq

val kv_kev_iter_nonneg :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
  bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> nat -> ('a1 -> real) ->
  ('a1 -> real_le) -> 'a1 -> real_le

val kv_dsum_abs_eq :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_le) -> ('a1 ->
  real_eq) -> ('a1 -> real) -> ('a1 -> real) -> real_eq

val kv_nonexpansive :
  'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) ->
  ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> ('a1 -> 'a1 ->
  real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 -> real_le) -> ('a1 -> real) ->
  ('a1 -> real) -> real -> real_lt -> real_le

val kv_minus_split : real -> real -> real -> real_eq

val kv_abs_minus_flip : real -> real -> real_eq

val kv_D_triangle :
  'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) ->
  ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> ('a1 -> real) ->
  ('a1 -> real) -> ('a1 -> real) -> real -> real_lt -> real_le

val kv_dsum_row_err :
  'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
  bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> ('a1 -> real) -> ('a1 ->
  real_le) -> real_eq

val kv_step_drift :
  'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) ->
  ('a1 -> 'a1 -> real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0)
  sigT -> real -> ('a1 -> real_le) -> ('a1 -> real) -> real -> real_lt ->
  real_eq -> ('a1 -> real_le) -> real_le

val kv_regroup4 : real -> real -> real -> real -> real_eq

val kv_drift_P :
  'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) ->
  ('a1 -> 'a1 -> real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0)
  sigT -> real -> ('a1 -> real_le) -> nat -> ('a1 -> real) -> real_eq -> ('a1
  -> real_le) -> real -> real_lt -> real_le

val kv_drift_bound :
  'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) ->
  ('a1 -> 'a1 -> real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0)
  sigT -> real -> ('a1 -> real_le) -> nat -> ('a1 -> real) -> real -> real_eq
  -> ('a1 -> real_le) -> real_lt -> real_le

val kv_drift_bound_tv :
  'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) ->
  ('a1 -> 'a1 -> real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0)
  sigT -> real -> ('a1 -> real_le) -> nat -> ('a1 -> real) -> real -> real_eq
  -> ('a1 -> real_le) -> real_lt -> real_le
