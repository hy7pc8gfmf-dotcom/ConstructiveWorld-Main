
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

val plus_swap_mid : realInterfaceEnhanced -> r -> r -> r -> r -> r id

val log_exp_neg : realInterfaceEnhanced -> r -> r id

val log_inv_one_inv : realInterfaceEnhanced -> r -> lt -> r id

val exp_neg_opp_log : realInterfaceEnhanced -> r -> lt -> r id

val exp_neg_opp_plus : realInterfaceEnhanced -> r -> r -> r id

val minus_plus_cancel : realInterfaceEnhanced -> r -> r -> r id

val opp_minus : realInterfaceEnhanced -> r -> r -> r id

val mult_minus_distr_l : realInterfaceEnhanced -> r -> r -> r -> r id

val minus_self_zero : realInterfaceEnhanced -> r -> r -> r id -> r id

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

val minus_plus_cancel_gap : realInterfaceEnhanced -> r -> r -> r id

val free_energy :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s -> r)
  -> r

type normalized = r id

type positive_dist = s -> lt

val boltzmann_dist :
  realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> lt -> r -> lt -> s
  -> r

val sum_opp :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r id

val sum_over_S_minus :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> (s -> r) -> r
  id

val boltzmann_normalized :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> r
  -> lt -> r id -> r id

val boltzmann_log_decomp :
  realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> lt -> r -> lt -> s
  -> r id

val free_energy_boltzmann :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> r
  -> lt -> r id -> r id

val energy_in_log_boltzmann :
  realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> lt -> r -> lt -> s
  -> r id

val p_times_energy_decomp :
  realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> lt -> r -> lt -> (s
  -> r) -> s -> r id

val free_energy_kl_decomp :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> r
  -> lt -> r id -> (s -> r) -> normalized -> r id

val free_energy_kl_diff :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> r
  -> lt -> r id -> (s -> r) -> normalized -> r id

val relative_entropy :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> (s -> r) -> r

val mult_minus_distr_r : realInterfaceEnhanced -> r -> r -> r -> r id

val z_align :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r

val pi_star :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> lt -> s -> r

val pi_star_normalized :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> lt -> r id

val align_energy :
  realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> (s -> r) -> s -> r

val align_objective :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s -> r)
  -> (s -> r) -> r

val align_energy_exp :
  realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> lt -> (s -> r) ->
  (s -> lt) -> s -> r id

val align_partition_condition :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> (s -> lt) -> r id

val free_energy_ext :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s -> r)
  -> (s -> r) -> (s -> r) -> (s -> r id) -> r id

val align_boltzmann_is_pi_star :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> (s -> lt) -> lt -> s -> r id

val minus_minus_distr : realInterfaceEnhanced -> r -> r -> r -> r id

val minus_rearrange_four : realInterfaceEnhanced -> r -> r -> r -> r -> r id

val relative_entropy_ext_r :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> (s -> r) ->
  (s -> r) -> (s -> r id) -> r id

val minus_opp_opp : realInterfaceEnhanced -> r -> r -> r id

val rlhf_suboptimality_gap :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> (s -> lt) -> lt -> (s -> r) -> normalized -> positive_dist -> r id

val advantage_aug :
  realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> (s -> r) -> (s ->
  r) -> s -> r

val z_rel :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r -> (s -> r) -> r

val z_rel_pos :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt) -> lt

val energy_t :
  realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> (s -> r) -> r -> (s
  -> r) -> s -> r

val pi_next :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt) -> s
  -> r

val boltzmann_factor_bridge :
  realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> lt -> (s -> r) -> r
  -> (s -> r) -> (s -> lt) -> s -> r id

val z_rel_boltzmann_form :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r -> (s -> r) -> (s -> lt) -> r id

val free_energy_ext_t12 :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s -> r)
  -> (s -> r) -> (s -> r id) -> r id

val rel_free_energy_decomp :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt) -> r
  id -> r id

val reward_expand :
  realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> (s -> r) -> (s ->
  r) -> s -> r id

val sum_over_S_opp_t12 :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r id

val sum_ptimes_opp_scal_t12 :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s -> r)
  -> r id

val sum_ptimes_scal_t12 :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s -> r)
  -> r id

val f_t_simpl_t :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s -> r)
  -> r -> (s -> r) -> r id

val f_t_simpl_next_kl :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt) -> r id

val surrogate_diff_identity :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt) -> r
  id -> (s -> lt) -> r id

val pi_next_pos :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt) -> s
  -> lt

val mult_minus_distr_r_t12 : realInterfaceEnhanced -> r -> r -> r -> r id

val eta_absorb_t12 : realInterfaceEnhanced -> r -> r -> r id

val align_energy_expand :
  realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> (s -> r) -> r -> (s
  -> r) -> s -> r id

val f_align_F_t_rel :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s -> r)
  -> r -> (s -> r) -> (s -> r) -> r id

val align_objective_t12_decomp :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s -> r)
  -> r -> (s -> r) -> (s -> r) -> r id

val j_pi_t_t12 :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s -> r)
  -> r -> (s -> r) -> r id -> r id

val j_pi_next_t12 :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt) -> r id

val f_t_simpl_p :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s -> r)
  -> r -> (s -> r) -> (s -> r) -> r id

val f_t_decomp_p :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt) -> r
  id -> (s -> r) -> normalized -> r id

val sum_grad_cross :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt) -> r id

val grad_cross_identity :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r -> lt -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt)
  -> r id -> (s -> lt) -> r id

val minus_sub_plus_t13 : realInterfaceEnhanced -> r -> r -> r -> r id

val opp_minus_rev_t13 : realInterfaceEnhanced -> r -> r -> r id

val sum_advance_gap :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> (s -> lt) -> lt -> r -> (s -> r) -> (s -> lt) -> r id -> r id

val minus_distr_t13 : realInterfaceEnhanced -> r -> r -> r -> r -> r id

val minus_opp_opp_mult_t13 : realInterfaceEnhanced -> r -> r -> r -> r id

val t13_hexp :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> lt -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt)
  -> r id -> r id

val minus_split_t13 : realInterfaceEnhanced -> r -> r -> r -> r id

val minus_plus_cancel_gap_rev_t13 : realInterfaceEnhanced -> r -> r -> r id

val t13_collapse : realInterfaceEnhanced -> r -> r -> r -> r -> r -> r id

val policy_iter_backward_kl_step_beta :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> (s -> lt) -> lt -> r -> lt -> ((s -> r) -> (s -> lt) -> lt) -> (s
  -> r) -> (s -> lt) -> r id -> (s -> lt) -> r id

val policy_iter_backward_kl_step :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> (s -> lt) -> lt -> r -> lt -> ((s -> r) -> (s -> lt) -> lt) -> (s
  -> r) -> (s -> lt) -> r id -> (s -> lt) -> r id

val policy_iter_gap_diff :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r -> lt -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt)
  -> r id -> r id

val minus_middle_t12 : realInterfaceEnhanced -> r -> r -> r -> r id

val minus_left_cancel_t12 : realInterfaceEnhanced -> r -> r -> r -> r id

val policy_gap_next_exact :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> (s -> lt) -> lt -> r -> lt -> ((s -> r) -> (s -> lt) -> lt) -> (s
  -> r) -> (s -> lt) -> r id -> r id

val policy_gap_decrement_exact :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> lt -> r -> lt -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s
  -> lt) -> r id -> r id

val dpo_loss_step_exact :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> r -> lt -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt)
  -> r id -> r id

val policy_gap_backward_kl_exact :
  realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt -> (s
  -> r) -> (s -> lt) -> lt -> r -> lt -> ((s -> r) -> (s -> lt) -> lt) -> (s
  -> r) -> (s -> lt) -> r id -> r id
