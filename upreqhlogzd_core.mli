
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

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type 'a id =
| Id_refl

type ('a, 'b) or0 = ('a, 'b) sum

type 'a not = 'a -> empty_set

type natLe = bool id

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

  val req_mult_compat :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    req -> 'a1 req -> 'a1 req

  val plus_assoc :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 req

  val plus_comm : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 req

  val plus_zero : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 req

  val plus_opp : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 req

  val mult_comm : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 req

  val mult_one : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 req

  val distrib :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 req

  val le_refl : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 le

  val le_trans :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 le -> 'a1
    le -> 'a1 le

  val lt_le_iff :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> ('a1 lt, 'a1 req)
    or0 -> 'a1 le

  val le_id_l :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 req ->
    'a1 le -> 'a1 le

  val le_id_r :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 req ->
    'a1 le -> 'a1 le

  val inv_pos : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 lt -> 'a1

  val inv_pos_correct :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 lt -> 'a1 req

  val one_pos : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 lt

  val le_plus_compat :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 le
    -> 'a1 le -> 'a1 le

  val mult_positive :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 lt -> 'a1 lt ->
    'a1 lt

  val opp_le_compat :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 le -> 'a1 le

  val inv_pos_pos :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 lt -> 'a1 lt

  val log : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 lt -> 'a1

  val log_mult :
    'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 lt -> 'a1 lt ->
    'a1 req

  val log_one : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 lt -> 'a1 req
 end

val req_minus :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1
  -> 'a1

val req_plus_zero_l :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1
  RealInterfaceEnhancedMod.req

val req_plus_opp_l :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1
  RealInterfaceEnhancedMod.req

val req_add_cancel_l :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1
  -> 'a1 -> 'a1 RealInterfaceEnhancedMod.req -> 'a1
  RealInterfaceEnhancedMod.req

val req_minus_plus_cancel_r :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1
  -> 'a1 RealInterfaceEnhancedMod.req

val req_le_plus_nonneg_r :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1
  -> 'a1 RealInterfaceEnhancedMod.le -> 'a1 RealInterfaceEnhancedMod.le

val z_aud_req :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
  'a1) -> 'a1) -> ('a2 -> bool) -> ('a2 -> 'a1) -> 'a1

val kl_proj_closed :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
  'a1) -> 'a1) -> ('a2 -> bool) -> ('a2 -> 'a1) -> ('a2 -> 'a1
  RealInterfaceEnhancedMod.lt) -> 'a1 RealInterfaceEnhancedMod.lt -> ('a2 ->
  'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.lt) -> 'a2 -> 'a1

val rkl_opp_zero :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1
  RealInterfaceEnhancedMod.req

val req_if_p_le_p :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> ('a2 ->
  bool) -> ('a2 -> 'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.lt) -> 'a2 ->
  'a1 RealInterfaceEnhancedMod.le

val req_Z_aud_le_one :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
  'a1) -> 'a1) -> (('a2 -> 'a1) -> ('a2 -> 'a1) -> ('a2 -> 'a1
  RealInterfaceEnhancedMod.le) -> 'a1 RealInterfaceEnhancedMod.le) -> ('a2 ->
  bool) -> ('a2 -> 'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.lt) -> 'a1
  RealInterfaceEnhancedMod.le

val req_kl_minus_split :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1
  -> 'a1 -> 'a1 RealInterfaceEnhancedMod.req

val rkl_log_inv_one_inv :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> ('a1 -> 'a1
  -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.lt ->
  'a1 RealInterfaceEnhancedMod.req -> 'a1 RealInterfaceEnhancedMod.req) ->
  'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.req

val req_kl_closed_pt :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
  'a1) -> 'a1) -> ('a2 -> bool) -> ('a2 -> 'a1) -> ('a2 -> 'a1
  RealInterfaceEnhancedMod.lt) -> 'a1 RealInterfaceEnhancedMod.lt -> ('a2 ->
  'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.lt) -> 'a2 -> 'a1
  RealInterfaceEnhancedMod.req

val req_kl_closed_sum_split :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
  'a1) -> 'a1) -> (('a2 -> 'a1) -> ('a2 -> 'a1) -> ('a2 -> 'a1
  RealInterfaceEnhancedMod.req) -> 'a1 RealInterfaceEnhancedMod.req) -> (('a2
  -> 'a1) -> ('a2 -> 'a1) -> 'a1 RealInterfaceEnhancedMod.req) -> ('a1 ->
  ('a2 -> 'a1) -> 'a1 RealInterfaceEnhancedMod.req) -> ('a2 -> bool) -> ('a2
  -> 'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.lt) -> 'a1
  RealInterfaceEnhancedMod.lt -> ('a2 -> 'a1) -> ('a2 -> 'a1
  RealInterfaceEnhancedMod.lt) -> 'a1 RealInterfaceEnhancedMod.req

val req_kl_closed_tail_eval :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
  'a1) -> 'a1) -> ('a1 -> 'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1
  RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.req -> 'a1
  RealInterfaceEnhancedMod.req) -> ('a2 -> bool) -> ('a2 -> 'a1) -> 'a1
  RealInterfaceEnhancedMod.lt -> ('a2 -> 'a1) -> ('a2 -> 'a1
  RealInterfaceEnhancedMod.lt) -> 'a1 RealInterfaceEnhancedMod.req -> 'a1
  RealInterfaceEnhancedMod.req

val req_projected_distribution_minimizes_kl :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
  'a1) -> 'a1) -> (('a2 -> 'a1) -> ('a2 -> 'a1) -> ('a2 -> 'a1
  RealInterfaceEnhancedMod.req) -> 'a1 RealInterfaceEnhancedMod.req) -> (('a2
  -> 'a1) -> ('a2 -> 'a1) -> 'a1 RealInterfaceEnhancedMod.req) -> ('a1 ->
  ('a2 -> 'a1) -> 'a1 RealInterfaceEnhancedMod.req) -> ('a1 -> 'a1 -> 'a1
  RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1
  RealInterfaceEnhancedMod.req -> 'a1 RealInterfaceEnhancedMod.req) -> ('a2
  -> bool) -> ('a2 -> 'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.lt) -> 'a1
  RealInterfaceEnhancedMod.lt -> ('a2 -> 'a1) -> ('a2 -> 'a1
  RealInterfaceEnhancedMod.lt) -> 'a1 RealInterfaceEnhancedMod.req -> ('a2 ->
  __ -> 'a1 RealInterfaceEnhancedMod.req) -> 'a1 RealInterfaceEnhancedMod.le
  -> 'a1 RealInterfaceEnhancedMod.le

val hzlogd_log_le_zero_of_le_one :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> ('a1 -> 'a1
  -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.lt ->
  'a1 RealInterfaceEnhancedMod.le -> 'a1 RealInterfaceEnhancedMod.le) -> 'a1
  -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.le ->
  'a1 RealInterfaceEnhancedMod.le

val hzlogd_proj_min_kl_hlogzfree :
  'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
  'a1) -> 'a1) -> (('a2 -> 'a1) -> ('a2 -> 'a1) -> ('a2 -> 'a1
  RealInterfaceEnhancedMod.req) -> 'a1 RealInterfaceEnhancedMod.req) -> (('a2
  -> 'a1) -> ('a2 -> 'a1) -> 'a1 RealInterfaceEnhancedMod.req) -> ('a1 ->
  ('a2 -> 'a1) -> 'a1 RealInterfaceEnhancedMod.req) -> (('a2 -> 'a1) -> ('a2
  -> 'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.le) -> 'a1
  RealInterfaceEnhancedMod.le) -> ('a1 -> 'a1 -> 'a1
  RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1
  RealInterfaceEnhancedMod.req -> 'a1 RealInterfaceEnhancedMod.req) -> ('a2
  -> bool) -> ('a2 -> 'a1) -> 'a1 RealInterfaceEnhancedMod.req -> ('a2 -> 'a1
  RealInterfaceEnhancedMod.lt) -> 'a1 RealInterfaceEnhancedMod.lt -> ('a1 ->
  'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.lt
  -> 'a1 RealInterfaceEnhancedMod.le -> 'a1 RealInterfaceEnhancedMod.le) ->
  ('a2 -> 'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.lt) -> 'a1
  RealInterfaceEnhancedMod.req -> ('a2 -> __ -> 'a1
  RealInterfaceEnhancedMod.req) -> 'a1 RealInterfaceEnhancedMod.le
