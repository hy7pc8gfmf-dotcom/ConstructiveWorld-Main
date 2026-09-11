
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

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

type 'a not = 'a -> empty_set

val id_sym : 'a1 -> 'a1 -> 'a1 id -> 'a1 id

val id_trans : 'a1 -> 'a1 -> 'a1 -> 'a1 id -> 'a1 id -> 'a1 id

val id_cong : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 id -> 'a2 id

val id_cong2 :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 id -> 'a2 id -> 'a3
  id

type natLe = bool id

type realInterface = { zero : __; one : __; plus : (__ -> __ -> __);
                       mult : (__ -> __ -> __); opp : (__ -> __);
                       abs : (__ -> __);
                       plus_assoc : (__ -> __ -> __ -> __ id);
                       plus_comm : (__ -> __ -> __ id);
                       plus_zero : (__ -> __ id); plus_opp : (__ -> __ id);
                       mult_assoc : (__ -> __ -> __ -> __ id);
                       mult_comm : (__ -> __ -> __ id);
                       mult_one : (__ -> __ id);
                       distrib : (__ -> __ -> __ -> __ id);
                       mult_zero : (__ -> __ id); lt_irrefl : (__ -> __ not);
                       lt_trans : (__ -> __ -> __ -> __ -> __ -> __);
                       le_refl : (__ -> __);
                       le_trans : (__ -> __ -> __ -> __ -> __ -> __);
                       le_antisym : (__ -> __ -> __ -> __ -> __ id);
                       le_lt_trans : (__ -> __ -> __ -> __ -> __ -> __);
                       lt_le_trans : (__ -> __ -> __ -> __ -> __ -> __);
                       lt_le_iff : (__ -> __ -> (__, __ id) or0 -> __);
                       le_id_l : (__ -> __ -> __ -> __ id -> __ -> __);
                       le_id_r : (__ -> __ -> __ -> __ id -> __ -> __);
                       lt_id_l : (__ -> __ -> __ -> __ id -> __ -> __);
                       lt_id_r : (__ -> __ -> __ -> __ id -> __ -> __);
                       inv_pos : (__ -> __ -> __);
                       inv_pos_correct : (__ -> __ -> __ id);
                       exp_neg : (__ -> __); exp_neg_pos : (__ -> __);
                       exp_neg_zero : __ id;
                       exp_neg_plus : (__ -> __ -> __ id);
                       log_inv : (__ -> __); log_inv_exp_neg : (__ -> __ id);
                       log_inv_one : __ id;
                       log_inv_mult : (__ -> __ -> __ -> __ -> __ id);
                       metric : (__ -> __ -> __);
                       metric_sym : (__ -> __ -> __ id);
                       metric_pos : (__ -> __ -> __);
                       metric_zero : (__ -> __ -> __ id -> __ id);
                       metric_triangle : (__ -> __ -> __ -> __);
                       lim_unique : ((nat -> __) -> __ -> __ -> __ -> __ ->
                                    __ id);
                       cauchy_complete : ((nat -> __) -> (__ -> __ -> (nat,
                                         nat -> nat -> natLe -> natLe -> __)
                                         sigT) -> (__, __) sigT) }

type r = __

type lt = __

type le = __

val minus : realInterface -> r -> r -> r

type realInterfaceEnhanced = { rI_base : realInterface; one_pos : lt;
                               lt_plus_compat : (r -> r -> r -> r -> lt -> lt
                                                -> lt);
                               le_plus_compat : (r -> r -> r -> r -> le -> le
                                                -> le);
                               plus_positive : (r -> r -> lt -> lt -> lt);
                               mult_positive : (r -> r -> lt -> lt -> lt);
                               lt_mult_compat : (r -> r -> r -> lt -> lt ->
                                                lt);
                               le_mult_compat : (r -> r -> r -> lt -> le ->
                                                le);
                               le_mult_compat_weak : (r -> r -> r -> le -> le
                                                     -> le);
                               opp_lt_compat : (r -> r -> lt -> lt);
                               lt_zero_opp : (r -> lt -> lt);
                               opp_le_compat : (r -> r -> le -> le);
                               inv_pos_pos : (r -> lt -> lt);
                               inv_pos_ext : (r -> r -> lt -> lt -> r id -> r
                                             id);
                               inv_pos_le_compat : (r -> r -> lt -> lt -> le
                                                   -> le);
                               min : (r -> r -> r);
                               min_le_l : (r -> r -> le);
                               min_le_r : (r -> r -> le);
                               min_pos : (r -> r -> lt -> lt -> lt);
                               r_max : (r -> r -> r);
                               r_max_le_l : (r -> r -> le);
                               r_max_le_r : (r -> r -> le);
                               r_max_l_iff : (r -> r -> le -> r id);
                               r_max_r_iff : (r -> r -> le -> r id);
                               pos_test_lt : (r -> __ -> lt);
                               lt_pos_test : (r -> lt -> __);
                               pos_part : (r -> r);
                               pos_part_def : (r -> r id);
                               pos_part_nonneg : (r -> le);
                               r_if : (__ -> (__, __ not) or0 -> r -> r -> r);
                               r_if_true : (__ -> (__, __ not) or0 -> r -> r
                                           -> __ -> r id);
                               r_if_false : (__ -> (__, __ not) or0 -> r -> r
                                            -> __ not -> r id);
                               abs_nonneg : (r -> le);
                               abs_triangle : (r -> r -> le);
                               abs_zero : r id; abs_mult : (r -> r -> r id);
                               abs_opp : (r -> r id);
                               abs_pos : (r -> lt -> r id);
                               exp_neg_decr : (r -> r -> lt -> lt);
                               exp_neg_le_decr : (r -> r -> le -> le);
                               log : (r -> r);
                               log_mult : (r -> r -> lt -> lt -> r id);
                               log_one : r id;
                               log_inv_log : (r -> lt -> r id);
                               exp_neg_log_inv : (r -> r id);
                               log_le_linear : (r -> lt -> le);
                               log_eq_linear : (r -> lt -> r id -> r id) }

val plus_inv_unique :
  realInterfaceEnhanced -> r -> r -> r -> r id -> r id -> r id

val opp_plus : realInterfaceEnhanced -> r -> r -> r id

val mult_plus_distr_r : realInterfaceEnhanced -> r -> r -> r -> r id

val opp_mult_r : realInterfaceEnhanced -> r -> r -> r id

val opp_mult_l : realInterfaceEnhanced -> r -> r -> r id

val double_neg : realInterfaceEnhanced -> r -> r id

val le_plus_nonneg_r : realInterfaceEnhanced -> r -> r -> le -> le

val log_exp_neg : realInterfaceEnhanced -> r -> r id

val log_inv_one_inv : realInterfaceEnhanced -> r -> lt -> r id

val log_div : realInterfaceEnhanced -> r -> r -> lt -> lt -> r id

val minus_plus_cancel : realInterfaceEnhanced -> r -> r -> r id

val opp_minus : realInterfaceEnhanced -> r -> r -> r id

val log_div_neg : realInterfaceEnhanced -> r -> r -> lt -> lt -> r id

val le_mult_compat_r : realInterfaceEnhanced -> r -> r -> r -> le -> le -> le

val mult_minus_distr_l : realInterfaceEnhanced -> r -> r -> r -> r id

val le_minus_nonneg : realInterfaceEnhanced -> r -> r -> le -> le

type stateSpace = { szero : __; splus : (__ -> __ -> __);
                    smult : (r -> __ -> __); sopp : (__ -> __);
                    splus_assoc : (__ -> __ -> __ -> __ id);
                    splus_comm : (__ -> __ -> __ id);
                    splus_zero : (__ -> __ id); splus_opp : (__ -> __ id);
                    smult_one : (__ -> __ id);
                    smult_assoc : (r -> r -> __ -> __ id);
                    smult_distrib_r : (r -> __ -> __ -> __ id);
                    smult_distrib_l : (r -> r -> __ -> __ id);
                    smetric : (__ -> __ -> r);
                    smetric_sym : (__ -> __ -> r id);
                    smetric_pos : (__ -> __ -> le);
                    smetric_zero : (__ -> __ -> r id -> __ id);
                    smetric_triangle : (__ -> __ -> __ -> le);
                    clim_unique : ((nat -> __) -> __ -> __ -> __ -> __ -> __
                                  id);
                    cauchy_complete_S : ((nat -> __) -> (r -> lt -> (nat, nat
                                        -> nat -> natLe -> natLe -> lt) sigT)
                                        -> (__, __) sigT) }

type s = __

type sumOver = { sum_over_S : ((s -> r) -> r);
                 sum_over_S_linear : (r -> (s -> r) -> r id);
                 sum_over_S_add : ((s -> r) -> (s -> r) -> r id);
                 sum_over_S_ext : ((s -> r) -> (s -> r) -> (s -> r id) -> r
                                  id);
                 sum_over_S_le : ((s -> r) -> (s -> r) -> (s -> le) -> le);
                 sum_over_S_nonneg : ((s -> r) -> (s -> le) -> le);
                 sum_over_S_zero_nonneg : ((s -> r) -> (s -> le) -> r id -> s
                                          -> r id);
                 abs_sum_le : ((s -> r) -> le) }

val lt_mult_pos_cancel : realInterfaceEnhanced -> r -> r -> lt -> lt -> lt

type normalized = r id

type positive_dist = s -> lt

val sum_opp :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r id

val sum_over_S_minus :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> (s -> r) -> r
  id

val relative_entropy :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> (s -> r) -> r

val gibbs_pointwise :
  realInterfaceEnhanced -> stateSpace -> (s -> r) -> (s -> r) -> s -> lt ->
  lt -> le

val gibbs_inequality :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> (s -> r) ->
  normalized -> positive_dist -> normalized -> positive_dist -> le

val entropy_dist :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r

val energy_expectation :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> (s -> r) -> r

val entropy_neg_sum :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r id

val le_minus_nonneg_rev : realInterfaceEnhanced -> r -> r -> le -> le

val le_mult_pos_cancel : realInterfaceEnhanced -> r -> r -> lt -> le -> le

val mult_minus_distr_r : realInterfaceEnhanced -> r -> r -> r -> r id

val z_temp_pos :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> lt

val boltzmann_dist_temp :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> s -> r

val energy_exp_temp :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> r

val boltzmann_dist_temp_normalized :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> r id

val boltzmann_dist_temp_pos :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> s -> lt

val boltzmann_log_temp_decomp :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> s -> r id

val entropy_temp_explicit :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> r id

val relative_entropy_temp_decomp :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> (s -> r) ->
  normalized -> r id

val variational_temp_bound :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> (s -> r) ->
  normalized -> positive_dist -> le

val energy_exp_temp_mono :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r -> lt -> lt -> lt -> lt) -> (r -> r -> lt ->
  lt) -> (r -> r) -> (r -> lt -> r id) -> r -> r -> lt -> lt -> lt -> le

val temp_strict_A_chain2 :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> r -> lt -> lt ->
  r id

val temp_strict_ident2 :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> r -> lt -> lt ->
  r id

val energy_exp_temp_strict_mono :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r -> lt -> lt -> lt -> lt) -> (r -> r -> lt ->
  lt) -> (r -> r) -> (r -> lt -> r id) -> r -> r -> lt -> lt -> lt -> lt -> lt

val id_transport : 'a1 -> 'a1 -> 'a1 id -> 'a2 -> 'a2

val fw_energy_eta :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> r id

val fw_lt_double :
  realInterfaceEnhanced -> (r -> r -> r -> r -> lt -> le -> lt) -> r -> lt ->
  lt

val fw_double_pos : realInterfaceEnhanced -> r -> lt -> lt

val recovery_entropy_gain :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> r -> lt -> lt ->
  r id

val entropy_temp_mono :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> (r -> r -> lt -> lt ->
  lt -> lt) -> (r -> r -> lt -> lt) -> r -> r -> lt -> lt -> lt -> le

val entropy_temp_strict_mono :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> (r -> r -> lt -> lt ->
  lt -> lt) -> (r -> r -> lt -> lt) -> (r -> r -> r -> r -> lt -> le -> lt)
  -> r -> r -> lt -> lt -> lt -> lt -> lt

val recovery_entropy_gain_alt :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> r -> lt -> lt ->
  r id

type fw_verdict = (le, (r, r id) sigT) or0

val fw_detect_warm :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> (r -> r -> lt -> lt ->
  lt -> lt) -> (r -> r -> lt -> lt) -> (r -> r -> r -> r -> lt -> le -> lt)
  -> r -> r -> lt -> (r, r id) sigT -> (r, (lt, (lt, (le, r id) and0) and0)
  sigT) sigT

val firewall_loop :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r) ->
  (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> (r -> r -> lt -> lt ->
  lt -> lt) -> (r -> r -> lt -> lt) -> (r -> r -> r -> r -> lt -> le -> lt)
  -> r -> r -> lt -> fw_verdict -> (r, (lt, (le, (le, fw_verdict) and0) and0)
  sigT) sigT
