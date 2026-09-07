
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

type 'a list =
| Nil
| Cons of 'a * 'a list

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type sumbool =
| Left
| Right

module Nat =
 struct
  (** val eq_dec : nat -> nat -> sumbool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> Left
            | S _ -> Right)
    | S n0 -> (match m with
               | O -> Right
               | S n1 -> eq_dec n0 n1)
 end

type 'a id =
| Id_refl

type ('a, 'b) or0 = ('a, 'b) sum

type 'a not = 'a -> empty_set

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

(** val free_energy :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s ->
    r) -> r **)

let free_energy rI _ sO =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  (fun base_loss d p ->
  plus0 (sum_over_S0 (fun s0 -> mult0 (p s0) (base_loss s0)))
    (mult0 d (sum_over_S0 (fun s0 -> mult0 (p s0) (log0 (p s0))))))

(** val exp_pos_fn : realInterfaceEnhanced -> r -> r **)

let exp_pos_fn rI =
  let opp0 = rI.rI_base.opp in
  let exp_neg0 = rI.rI_base.exp_neg in (fun x -> exp_neg0 (opp0 x))

type logits = s -> r

(** val partition_function_temp :
    realInterfaceEnhanced -> stateSpace -> sumOver -> r -> lt -> logits -> r **)

let partition_function_temp rI _ sO =
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let sum_over_S0 = sO.sum_over_S in
  (fun t t_pos z ->
  sum_over_S0 (fun s0 -> exp_pos_fn rI (mult0 (inv_pos0 t t_pos) (z s0))))

(** val partition_function_temp_pos :
    realInterfaceEnhanced -> stateSpace -> sumOver -> ((s -> r) -> (s -> lt)
    -> lt) -> r -> lt -> logits -> lt **)

let partition_function_temp_pos rI _ _ =
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  (fun sum_pos_preserved t t_pos z ->
  sum_pos_preserved (fun s0 ->
    exp_neg0 (opp0 (mult0 (inv_pos0 t t_pos) (z s0)))) (fun s0 ->
    rI.rI_base.exp_neg_pos (opp0 (mult0 (inv_pos0 t t_pos) (z s0)))))

(** val softmax_temp :
    realInterfaceEnhanced -> stateSpace -> sumOver -> ((s -> r) -> (s -> lt)
    -> lt) -> r -> lt -> logits -> s -> r **)

let softmax_temp rI sS sO =
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  (fun sum_pos_preserved t t_pos z s0 ->
  mult0 (exp_pos_fn rI (mult0 (inv_pos0 t t_pos) (z s0)))
    (inv_pos0 (partition_function_temp rI sS sO t t_pos z)
      (partition_function_temp_pos rI sS sO sum_pos_preserved t t_pos z)))

(** val list_sum_g2 : realInterfaceEnhanced -> (nat -> r) -> nat list -> r **)

let list_sum_g2 rI =
  let zero0 = rI.rI_base.zero in
  let plus0 = rI.rI_base.plus in
  let rec list_sum_g3 f = function
  | Nil -> zero0
  | Cons (i, rest) -> plus0 (f i) (list_sum_g3 f rest)
  in list_sum_g3

(** val reward2 : realInterfaceEnhanced -> r -> nat -> r **)

let reward2 _ c _ =
  c

(** val indicator2 : realInterfaceEnhanced -> nat -> r **)

let indicator2 rI =
  let zero0 = rI.rI_base.zero in
  let one0 = rI.rI_base.one in
  (fun i -> match Nat.eq_dec i O with
            | Left -> one0
            | Right -> zero0)
