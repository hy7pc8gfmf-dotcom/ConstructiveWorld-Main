
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

(** val id_sym : 'a1 -> 'a1 -> 'a1 id -> 'a1 id **)

let id_sym _ _ _ =
  Id_refl

(** val id_trans : 'a1 -> 'a1 -> 'a1 -> 'a1 id -> 'a1 id -> 'a1 id **)

let id_trans _ _ _ _ _ =
  Id_refl

(** val id_cong : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 id -> 'a2 id **)

let id_cong _ _ _ _ =
  Id_refl

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

(** val minus : realInterface -> r -> r -> r **)

let minus rI a b =
  rI.plus a (rI.opp b)

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

(** val plus_inv_unique :
    realInterfaceEnhanced -> r -> r -> r -> r id -> r id -> r id **)

let plus_inv_unique rI a b c hab hac =
  let h1 =
    id_sym (rI.rI_base.plus b rI.rI_base.zero) b (rI.rI_base.plus_zero b)
  in
  let h2 =
    id_cong (fun x -> rI.rI_base.plus b x) rI.rI_base.zero
      (rI.rI_base.plus a c) (id_sym (rI.rI_base.plus a c) rI.rI_base.zero hac)
  in
  let h3 = rI.rI_base.plus_assoc b a c in
  let h4 =
    id_cong (fun x -> rI.rI_base.plus x c) (rI.rI_base.plus b a)
      (rI.rI_base.plus a b) (rI.rI_base.plus_comm b a)
  in
  let h5 =
    id_cong (fun x -> rI.rI_base.plus x c) (rI.rI_base.plus a b)
      rI.rI_base.zero hab
  in
  let h6 =
    id_trans (rI.rI_base.plus rI.rI_base.zero c)
      (rI.rI_base.plus c rI.rI_base.zero) c
      (rI.rI_base.plus_comm rI.rI_base.zero c) (rI.rI_base.plus_zero c)
  in
  id_trans b (rI.rI_base.plus b rI.rI_base.zero) c h1
    (id_trans (rI.rI_base.plus b rI.rI_base.zero)
      (rI.rI_base.plus b (rI.rI_base.plus a c)) c h2
      (id_trans (rI.rI_base.plus b (rI.rI_base.plus a c))
        (rI.rI_base.plus (rI.rI_base.plus b a) c) c h3
        (id_trans (rI.rI_base.plus (rI.rI_base.plus b a) c)
          (rI.rI_base.plus (rI.rI_base.plus a b) c) c h4
          (id_trans (rI.rI_base.plus (rI.rI_base.plus a b) c)
            (rI.rI_base.plus rI.rI_base.zero c) c h5 h6))))

(** val mult_plus_distr_r : realInterfaceEnhanced -> r -> r -> r -> r id **)

let mult_plus_distr_r rI =
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun a b c ->
  internal_Id_rew_r (rI.rI_base.mult (rI.rI_base.plus a b) c)
    (rI.rI_base.mult c (rI.rI_base.plus a b))
    (internal_Id_rew_r (rI.rI_base.mult c (rI.rI_base.plus a b))
      (rI.rI_base.plus (rI.rI_base.mult c a) (rI.rI_base.mult c b))
      (internal_Id_rew_r (rI.rI_base.mult c a) (rI.rI_base.mult a c)
        (internal_Id_rew_r (rI.rI_base.mult c b) (rI.rI_base.mult b c)
          Id_refl (rI.rI_base.mult_comm c b))
        (rI.rI_base.mult_comm c a))
      (rI.rI_base.distrib c a b))
    (rI.rI_base.mult_comm (rI.rI_base.plus a b) c))

(** val opp_mult_r : realInterfaceEnhanced -> r -> r -> r id **)

let opp_mult_r rI =
  let internal_Id_rew = fun _ f _ _ -> f in
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun a b ->
  plus_inv_unique rI (rI.rI_base.mult a b)
    (rI.rI_base.mult (rI.rI_base.opp a) b)
    (rI.rI_base.opp (rI.rI_base.mult a b))
    (internal_Id_rew
      (rI.rI_base.mult (rI.rI_base.plus a (rI.rI_base.opp a)) b)
      (internal_Id_rew_r (rI.rI_base.plus a (rI.rI_base.opp a))
        rI.rI_base.zero
        (internal_Id_rew_r (rI.rI_base.mult rI.rI_base.zero b)
          (rI.rI_base.mult b rI.rI_base.zero)
          (internal_Id_rew_r (rI.rI_base.mult b rI.rI_base.zero)
            rI.rI_base.zero Id_refl (rI.rI_base.mult_zero b))
          (rI.rI_base.mult_comm rI.rI_base.zero b))
        (rI.rI_base.plus_opp a))
      (rI.rI_base.plus (rI.rI_base.mult a b)
        (rI.rI_base.mult (rI.rI_base.opp a) b))
      (mult_plus_distr_r rI a (rI.rI_base.opp a) b))
    (rI.rI_base.plus_opp (rI.rI_base.mult a b)))

(** val minus_self_zero : realInterfaceEnhanced -> r -> r -> r id -> r id **)

let minus_self_zero rI a b hab =
  let h1 = id_cong (fun x -> rI.rI_base.plus x (rI.rI_base.opp b)) a b hab in
  id_trans (rI.rI_base.plus a (rI.rI_base.opp b))
    (rI.rI_base.plus b (rI.rI_base.opp b)) rI.rI_base.zero h1
    (rI.rI_base.plus_opp b)

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

(** val sum_opp :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r id **)

let sum_opp rI _ sO =
  let one0 = rI.rI_base.one in
  let mult0 = rI.rI_base.mult in
  let sum_over_S0 = sO.sum_over_S in
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun f ->
  let hext =
    sO.sum_over_S_ext (fun s0 -> rI.rI_base.opp (f s0)) (fun s0 ->
      mult0 (rI.rI_base.opp one0) (f s0)) (fun s0 ->
      let h1 = opp_mult_r rI one0 (f s0) in
      let h2 =
        id_cong rI.rI_base.opp (rI.rI_base.mult one0 (f s0)) (f s0)
          (id_trans (rI.rI_base.mult one0 (f s0))
            (rI.rI_base.mult (f s0) one0) (f s0)
            (rI.rI_base.mult_comm one0 (f s0)) (rI.rI_base.mult_one (f s0)))
      in
      id_trans (rI.rI_base.opp (f s0)) (rI.rI_base.opp (mult0 one0 (f s0)))
        (mult0 (rI.rI_base.opp one0) (f s0))
        (id_sym (rI.rI_base.opp (mult0 one0 (f s0))) (rI.rI_base.opp (f s0))
          h2)
        (id_sym (mult0 (rI.rI_base.opp one0) (f s0))
          (rI.rI_base.opp (mult0 one0 (f s0))) h1))
  in
  internal_Id_rew_r (sum_over_S0 (fun s0 -> rI.rI_base.opp (f s0)))
    (sum_over_S0 (fun s0 -> mult0 (rI.rI_base.opp one0) (f s0)))
    (let hlin = sO.sum_over_S_linear (rI.rI_base.opp one0) f in
     internal_Id_rew_r
       (sum_over_S0 (fun s0 -> mult0 (rI.rI_base.opp one0) (f s0)))
       (mult0 (rI.rI_base.opp one0) (sum_over_S0 f))
       (let h1 = opp_mult_r rI one0 (sum_over_S0 f) in
        let h2 =
          id_cong rI.rI_base.opp (rI.rI_base.mult one0 (sum_over_S0 f))
            (sum_over_S0 f)
            (id_trans (rI.rI_base.mult one0 (sum_over_S0 f))
              (rI.rI_base.mult (sum_over_S0 f) one0) (sum_over_S0 f)
              (rI.rI_base.mult_comm one0 (sum_over_S0 f))
              (rI.rI_base.mult_one (sum_over_S0 f)))
        in
        id_trans (mult0 (rI.rI_base.opp one0) (sum_over_S0 f))
          (rI.rI_base.opp (mult0 one0 (sum_over_S0 f)))
          (rI.rI_base.opp (sum_over_S0 f)) h1 h2)
       hlin)
    hext)

(** val sum_over_S_minus :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> (s -> r) ->
    r id **)

let sum_over_S_minus rI sS sO =
  let plus0 = rI.rI_base.plus in
  let sum_over_S0 = sO.sum_over_S in
  (fun f g ->
  let hadd = sO.sum_over_S_add f (fun s0 -> rI.rI_base.opp (g s0)) in
  let hopp = sum_opp rI sS sO g in
  id_trans (sum_over_S0 (fun s0 -> plus0 (f s0) (rI.rI_base.opp (g s0))))
    (plus0 (sum_over_S0 f) (sum_over_S0 (fun s0 -> rI.rI_base.opp (g s0))))
    (plus0 (sum_over_S0 f) (rI.rI_base.opp (sum_over_S0 g))) hadd
    (id_cong (fun x -> plus0 (sum_over_S0 f) x)
      (sum_over_S0 (fun s0 -> rI.rI_base.opp (g s0)))
      (rI.rI_base.opp (sum_over_S0 g)) hopp))

module EvictId =
 struct
  (** val boltzmann_factor :
      realInterfaceEnhanced -> stateSpace -> r -> lt -> (s -> r) -> s -> r **)

  let boltzmann_factor rI _ =
    let mult0 = rI.rI_base.mult in
    let inv_pos0 = rI.rI_base.inv_pos in
    let exp_neg0 = rI.rI_base.exp_neg in
    (fun d d_pos energy s0 -> exp_neg0 (mult0 (inv_pos0 d d_pos) (energy s0)))

  (** val coq_Z_thermo :
      realInterfaceEnhanced -> stateSpace -> sumOver -> r -> lt -> (s -> r)
      -> r **)

  let coq_Z_thermo rI sS sO =
    let sum_over_S0 = sO.sum_over_S in
    (fun d d_pos energy ->
    sum_over_S0 (boltzmann_factor rI sS d d_pos energy))

  (** val evicted_transition :
      realInterfaceEnhanced -> stateSpace -> (s -> s -> r) -> (s -> ('a1, 'a1
      not) or0) -> s -> s -> r **)

  let evicted_transition rI _ transition keep_dec s0 s' =
    let zero0 = rI.rI_base.zero in
    (match keep_dec s0 with
     | Inl _ ->
       (match keep_dec s' with
        | Inl _ -> transition s0 s'
        | Inr _ -> zero0)
     | Inr _ -> zero0)

  (** val evicted_partition :
      realInterfaceEnhanced -> stateSpace -> sumOver -> r -> lt -> (s -> r)
      -> (s -> ('a1, 'a1 not) or0) -> r **)

  let evicted_partition rI sS sO d d_pos energy keep_dec =
    let zero0 = rI.rI_base.zero in
    sO.sum_over_S (fun s0 ->
      match keep_dec s0 with
      | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
      | Inr _ -> zero0)

  (** val evicted_boltzmann :
      realInterfaceEnhanced -> stateSpace -> sumOver -> r -> lt -> (s -> r)
      -> (s -> ('a1, 'a1 not) or0) -> lt -> s -> r **)

  let evicted_boltzmann rI sS sO d d_pos energy keep_dec evicted_partition_pos s0 =
    let zero0 = rI.rI_base.zero in
    let mult0 = rI.rI_base.mult in
    let inv_pos0 = rI.rI_base.inv_pos in
    (match keep_dec s0 with
     | Inl _ ->
       mult0
         (inv_pos0 (evicted_partition rI sS sO d d_pos energy keep_dec)
           evicted_partition_pos)
         (boltzmann_factor rI sS d d_pos energy s0)
     | Inr _ -> zero0)

  (** val opp_zero_u : realInterfaceEnhanced -> r id **)

  let opp_zero_u rI =
    let zero0 = rI.rI_base.zero in
    let opp0 = rI.rI_base.opp in
    plus_inv_unique rI zero0 (opp0 zero0) zero0 (rI.rI_base.plus_opp zero0)
      (rI.rI_base.plus_zero zero0)

  (** val minus_zero_r_u : realInterfaceEnhanced -> r -> r id **)

  let minus_zero_r_u rI =
    let zero0 = rI.rI_base.zero in
    let plus0 = rI.rI_base.plus in
    let opp0 = rI.rI_base.opp in
    (fun a ->
    id_trans (plus0 a (opp0 zero0)) (plus0 a zero0) a
      (id_cong (fun x -> plus0 a x) (opp0 zero0) zero0 (opp_zero_u rI))
      (rI.rI_base.plus_zero a))

  (** val boltzmann_factor_detailed_balance :
      realInterfaceEnhanced -> stateSpace -> sumOver -> r -> lt -> (s -> r)
      -> lt -> (s -> s -> r) -> (s -> s -> r id) -> s -> s -> r id **)

  let boltzmann_factor_detailed_balance rI sS sO =
    let one0 = rI.rI_base.one in
    let mult0 = rI.rI_base.mult in
    let inv_pos0 = rI.rI_base.inv_pos in
    (fun d d_pos energy z_thermo_pos transition detailed_balance s0 s' ->
    let hdb = detailed_balance s0 s' in
    let hZinv =
      rI.rI_base.inv_pos_correct (coq_Z_thermo rI sS sO d d_pos energy)
        z_thermo_pos
    in
    let hZl =
      id_trans
        (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
          (rI.rI_base.mult
            (mult0
              (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
              (boltzmann_factor rI sS d d_pos energy s0))
            (transition s0 s')))
        (rI.rI_base.mult
          (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
            (mult0
              (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
              (boltzmann_factor rI sS d d_pos energy s0)))
          (transition s0 s'))
        (mult0 (boltzmann_factor rI sS d d_pos energy s0) (transition s0 s'))
        (rI.rI_base.mult_assoc (coq_Z_thermo rI sS sO d d_pos energy)
          (mult0
            (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
            (boltzmann_factor rI sS d d_pos energy s0))
          (transition s0 s'))
        (id_cong (fun x -> mult0 x (transition s0 s'))
          (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
            (rI.rI_base.mult
              (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
              (boltzmann_factor rI sS d d_pos energy s0)))
          (boltzmann_factor rI sS d d_pos energy s0)
          (id_trans
            (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
              (rI.rI_base.mult
                (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
                (boltzmann_factor rI sS d d_pos energy s0)))
            (rI.rI_base.mult
              (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
                (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos))
              (boltzmann_factor rI sS d d_pos energy s0))
            (boltzmann_factor rI sS d d_pos energy s0)
            (rI.rI_base.mult_assoc (coq_Z_thermo rI sS sO d d_pos energy)
              (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
              (boltzmann_factor rI sS d d_pos energy s0))
            (id_trans
              (mult0
                (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
                  (rI.rI_base.inv_pos (coq_Z_thermo rI sS sO d d_pos energy)
                    z_thermo_pos))
                (boltzmann_factor rI sS d d_pos energy s0))
              (mult0 rI.rI_base.one
                (boltzmann_factor rI sS d d_pos energy s0))
              (boltzmann_factor rI sS d d_pos energy s0)
              (id_cong (fun x ->
                mult0 x (boltzmann_factor rI sS d d_pos energy s0))
                (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
                  (rI.rI_base.inv_pos (coq_Z_thermo rI sS sO d d_pos energy)
                    z_thermo_pos))
                rI.rI_base.one hZinv)
              (id_trans
                (rI.rI_base.mult one0
                  (boltzmann_factor rI sS d d_pos energy s0))
                (rI.rI_base.mult (boltzmann_factor rI sS d d_pos energy s0)
                  one0)
                (boltzmann_factor rI sS d d_pos energy s0)
                (rI.rI_base.mult_comm one0
                  (boltzmann_factor rI sS d d_pos energy s0))
                (rI.rI_base.mult_one
                  (boltzmann_factor rI sS d d_pos energy s0))))))
    in
    let hZr =
      id_trans
        (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
          (rI.rI_base.mult
            (mult0
              (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
              (boltzmann_factor rI sS d d_pos energy s'))
            (transition s' s0)))
        (rI.rI_base.mult
          (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
            (mult0
              (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
              (boltzmann_factor rI sS d d_pos energy s')))
          (transition s' s0))
        (mult0 (boltzmann_factor rI sS d d_pos energy s') (transition s' s0))
        (rI.rI_base.mult_assoc (coq_Z_thermo rI sS sO d d_pos energy)
          (mult0
            (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
            (boltzmann_factor rI sS d d_pos energy s'))
          (transition s' s0))
        (id_cong (fun x -> mult0 x (transition s' s0))
          (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
            (rI.rI_base.mult
              (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
              (boltzmann_factor rI sS d d_pos energy s')))
          (boltzmann_factor rI sS d d_pos energy s')
          (id_trans
            (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
              (rI.rI_base.mult
                (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
                (boltzmann_factor rI sS d d_pos energy s')))
            (rI.rI_base.mult
              (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
                (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos))
              (boltzmann_factor rI sS d d_pos energy s'))
            (boltzmann_factor rI sS d d_pos energy s')
            (rI.rI_base.mult_assoc (coq_Z_thermo rI sS sO d d_pos energy)
              (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
              (boltzmann_factor rI sS d d_pos energy s'))
            (id_trans
              (mult0
                (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
                  (rI.rI_base.inv_pos (coq_Z_thermo rI sS sO d d_pos energy)
                    z_thermo_pos))
                (boltzmann_factor rI sS d d_pos energy s'))
              (mult0 rI.rI_base.one
                (boltzmann_factor rI sS d d_pos energy s'))
              (boltzmann_factor rI sS d d_pos energy s')
              (id_cong (fun x ->
                mult0 x (boltzmann_factor rI sS d d_pos energy s'))
                (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
                  (rI.rI_base.inv_pos (coq_Z_thermo rI sS sO d d_pos energy)
                    z_thermo_pos))
                rI.rI_base.one hZinv)
              (id_trans
                (rI.rI_base.mult one0
                  (boltzmann_factor rI sS d d_pos energy s'))
                (rI.rI_base.mult (boltzmann_factor rI sS d d_pos energy s')
                  one0)
                (boltzmann_factor rI sS d d_pos energy s')
                (rI.rI_base.mult_comm one0
                  (boltzmann_factor rI sS d d_pos energy s'))
                (rI.rI_base.mult_one
                  (boltzmann_factor rI sS d d_pos energy s'))))))
    in
    id_trans
      (mult0 (boltzmann_factor rI sS d d_pos energy s0) (transition s0 s'))
      (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
        (rI.rI_base.mult
          (mult0
            (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
            (boltzmann_factor rI sS d d_pos energy s0))
          (transition s0 s')))
      (mult0 (boltzmann_factor rI sS d d_pos energy s') (transition s' s0))
      (id_sym
        (rI.rI_base.mult (coq_Z_thermo rI sS sO d d_pos energy)
          (rI.rI_base.mult
            (mult0
              (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
              (boltzmann_factor rI sS d d_pos energy s0))
            (transition s0 s')))
        (mult0 (boltzmann_factor rI sS d d_pos energy s0) (transition s0 s'))
        hZl)
      (id_trans
        (mult0 (coq_Z_thermo rI sS sO d d_pos energy)
          (mult0
            (mult0
              (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
              (boltzmann_factor rI sS d d_pos energy s0))
            (transition s0 s')))
        (mult0 (coq_Z_thermo rI sS sO d d_pos energy)
          (mult0
            (mult0
              (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
              (boltzmann_factor rI sS d d_pos energy s'))
            (transition s' s0)))
        (mult0 (boltzmann_factor rI sS d d_pos energy s') (transition s' s0))
        (id_cong (fun x -> mult0 (coq_Z_thermo rI sS sO d d_pos energy) x)
          (mult0
            (mult0
              (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
              (boltzmann_factor rI sS d d_pos energy s0))
            (transition s0 s'))
          (mult0
            (mult0
              (inv_pos0 (coq_Z_thermo rI sS sO d d_pos energy) z_thermo_pos)
              (boltzmann_factor rI sS d d_pos energy s'))
            (transition s' s0))
          hdb)
        hZr))

  (** val evicted_db_products :
      realInterfaceEnhanced -> stateSpace -> sumOver -> r -> lt -> (s -> r)
      -> lt -> (s -> s -> r) -> (s -> s -> r id) -> (s -> ('a1, 'a1 not) or0)
      -> lt -> s -> s -> r id **)

  let evicted_db_products rI sS sO d d_pos energy z_thermo_pos transition detailed_balance keep_dec evicted_partition_pos s0 s' =
    let zero0 = rI.rI_base.zero in
    let mult0 = rI.rI_base.mult in
    let inv_pos0 = rI.rI_base.inv_pos in
    let o = keep_dec s0 in
    (match o with
     | Inl _ ->
       let o0 = keep_dec s' in
       (match o0 with
        | Inl _ ->
          let hf =
            id_sym
              (mult0 (boltzmann_factor rI sS d d_pos energy s0)
                (transition s0 s'))
              (mult0 (boltzmann_factor rI sS d d_pos energy s')
                (transition s' s0))
              (boltzmann_factor_detailed_balance rI sS sO d d_pos energy
                z_thermo_pos transition detailed_balance s0 s')
          in
          id_trans
            (rI.rI_base.mult
              (rI.rI_base.mult
                (inv_pos0
                  (evicted_partition rI sS sO d d_pos energy keep_dec)
                  evicted_partition_pos)
                (boltzmann_factor rI sS d d_pos energy s'))
              (transition s' s0))
            (rI.rI_base.mult
              (inv_pos0 (evicted_partition rI sS sO d d_pos energy keep_dec)
                evicted_partition_pos)
              (rI.rI_base.mult (boltzmann_factor rI sS d d_pos energy s')
                (transition s' s0)))
            (mult0
              (mult0
                (inv_pos0
                  (evicted_partition rI sS sO d d_pos energy keep_dec)
                  evicted_partition_pos)
                (boltzmann_factor rI sS d d_pos energy s0))
              (transition s0 s'))
            (id_sym
              (rI.rI_base.mult
                (inv_pos0
                  (evicted_partition rI sS sO d d_pos energy keep_dec)
                  evicted_partition_pos)
                (rI.rI_base.mult (boltzmann_factor rI sS d d_pos energy s')
                  (transition s' s0)))
              (rI.rI_base.mult
                (rI.rI_base.mult
                  (inv_pos0
                    (evicted_partition rI sS sO d d_pos energy keep_dec)
                    evicted_partition_pos)
                  (boltzmann_factor rI sS d d_pos energy s'))
                (transition s' s0))
              (rI.rI_base.mult_assoc
                (inv_pos0
                  (evicted_partition rI sS sO d d_pos energy keep_dec)
                  evicted_partition_pos)
                (boltzmann_factor rI sS d d_pos energy s') (transition s' s0)))
            (id_trans
              (mult0
                (inv_pos0
                  (evicted_partition rI sS sO d d_pos energy keep_dec)
                  evicted_partition_pos)
                (mult0 (boltzmann_factor rI sS d d_pos energy s')
                  (transition s' s0)))
              (mult0
                (inv_pos0
                  (evicted_partition rI sS sO d d_pos energy keep_dec)
                  evicted_partition_pos)
                (mult0 (boltzmann_factor rI sS d d_pos energy s0)
                  (transition s0 s')))
              (mult0
                (mult0
                  (inv_pos0
                    (evicted_partition rI sS sO d d_pos energy keep_dec)
                    evicted_partition_pos)
                  (boltzmann_factor rI sS d d_pos energy s0))
                (transition s0 s'))
              (id_cong (fun x ->
                mult0
                  (inv_pos0
                    (evicted_partition rI sS sO d d_pos energy keep_dec)
                    evicted_partition_pos)
                  x)
                (mult0 (boltzmann_factor rI sS d d_pos energy s')
                  (transition s' s0))
                (mult0 (boltzmann_factor rI sS d d_pos energy s0)
                  (transition s0 s'))
                hf)
              (rI.rI_base.mult_assoc
                (inv_pos0
                  (evicted_partition rI sS sO d d_pos energy keep_dec)
                  evicted_partition_pos)
                (boltzmann_factor rI sS d d_pos energy s0) (transition s0 s')))
        | Inr _ ->
          id_trans (rI.rI_base.mult zero0 rI.rI_base.zero) rI.rI_base.zero
            (rI.rI_base.mult
              (mult0
                (inv_pos0
                  (evicted_partition rI sS sO d d_pos energy keep_dec)
                  evicted_partition_pos)
                (boltzmann_factor rI sS d d_pos energy s0))
              rI.rI_base.zero)
            (rI.rI_base.mult_zero zero0)
            (id_sym
              (rI.rI_base.mult
                (mult0
                  (inv_pos0
                    (evicted_partition rI sS sO d d_pos energy keep_dec)
                    evicted_partition_pos)
                  (boltzmann_factor rI sS d d_pos energy s0))
                rI.rI_base.zero)
              rI.rI_base.zero
              (rI.rI_base.mult_zero
                (mult0
                  (inv_pos0
                    (evicted_partition rI sS sO d d_pos energy keep_dec)
                    evicted_partition_pos)
                  (boltzmann_factor rI sS d d_pos energy s0)))))
     | Inr _ ->
       let o0 = keep_dec s' in
       (match o0 with
        | Inl _ ->
          id_trans
            (rI.rI_base.mult
              (mult0
                (inv_pos0
                  (evicted_partition rI sS sO d d_pos energy keep_dec)
                  evicted_partition_pos)
                (boltzmann_factor rI sS d d_pos energy s'))
              rI.rI_base.zero)
            rI.rI_base.zero (rI.rI_base.mult zero0 rI.rI_base.zero)
            (rI.rI_base.mult_zero
              (mult0
                (inv_pos0
                  (evicted_partition rI sS sO d d_pos energy keep_dec)
                  evicted_partition_pos)
                (boltzmann_factor rI sS d d_pos energy s')))
            (id_sym (rI.rI_base.mult zero0 rI.rI_base.zero) rI.rI_base.zero
              (rI.rI_base.mult_zero zero0))
        | Inr _ -> Id_refl))

  (** val eviction_db_breaking_zero :
      realInterfaceEnhanced -> stateSpace -> sumOver -> r -> lt -> (s -> r)
      -> lt -> (s -> s -> r) -> (s -> s -> r id) -> (s -> ('a1, 'a1 not) or0)
      -> lt -> s -> s -> r id **)

  let eviction_db_breaking_zero rI sS sO d d_pos energy z_thermo_pos transition detailed_balance keep_dec evicted_partition_pos s0 s' =
    let zero0 = rI.rI_base.zero in
    let mult0 = rI.rI_base.mult in
    let abs0 = rI.rI_base.abs in
    id_trans
      (abs0
        (minus rI.rI_base
          (mult0
            (evicted_boltzmann rI sS sO d d_pos energy keep_dec
              evicted_partition_pos s0)
            (evicted_transition rI sS transition keep_dec s0 s'))
          (mult0
            (evicted_boltzmann rI sS sO d d_pos energy keep_dec
              evicted_partition_pos s')
            (evicted_transition rI sS transition keep_dec s' s0))))
      (abs0 rI.rI_base.zero) zero0
      (id_cong abs0
        (minus rI.rI_base
          (mult0
            (evicted_boltzmann rI sS sO d d_pos energy keep_dec
              evicted_partition_pos s0)
            (evicted_transition rI sS transition keep_dec s0 s'))
          (mult0
            (evicted_boltzmann rI sS sO d d_pos energy keep_dec
              evicted_partition_pos s')
            (evicted_transition rI sS transition keep_dec s' s0)))
        rI.rI_base.zero
        (minus_self_zero rI
          (mult0
            (evicted_boltzmann rI sS sO d d_pos energy keep_dec
              evicted_partition_pos s0)
            (evicted_transition rI sS transition keep_dec s0 s'))
          (mult0
            (evicted_boltzmann rI sS sO d d_pos energy keep_dec
              evicted_partition_pos s')
            (evicted_transition rI sS transition keep_dec s' s0))
          (id_sym
            (mult0
              (evicted_boltzmann rI sS sO d d_pos energy keep_dec
                evicted_partition_pos s')
              (evicted_transition rI sS transition keep_dec s' s0))
            (mult0
              (evicted_boltzmann rI sS sO d d_pos energy keep_dec
                evicted_partition_pos s0)
              (evicted_transition rI sS transition keep_dec s0 s'))
            (evicted_db_products rI sS sO d d_pos energy z_thermo_pos
              transition detailed_balance keep_dec evicted_partition_pos s0
              s'))))
      rI.abs_zero

  (** val evicted_boltzmann_steady_exact :
      realInterfaceEnhanced -> stateSpace -> sumOver -> r -> lt -> (s -> r)
      -> lt -> (s -> s -> r) -> (s -> s -> r id) -> (s -> ('a1, 'a1 not) or0)
      -> lt -> s -> r id **)

  let evicted_boltzmann_steady_exact rI sS sO d d_pos energy z_thermo_pos transition detailed_balance keep_dec evicted_partition_pos s0 =
    let mult0 = rI.rI_base.mult in
    let sum_over_S0 = sO.sum_over_S in
    id_trans
      (sO.sum_over_S (fun s' ->
        mult0
          (evicted_boltzmann rI sS sO d d_pos energy keep_dec
            evicted_partition_pos s')
          (evicted_transition rI sS transition keep_dec s' s0)))
      (sO.sum_over_S (fun s' ->
        mult0
          (evicted_boltzmann rI sS sO d d_pos energy keep_dec
            evicted_partition_pos s0)
          (evicted_transition rI sS transition keep_dec s0 s')))
      (mult0
        (evicted_boltzmann rI sS sO d d_pos energy keep_dec
          evicted_partition_pos s0)
        (sum_over_S0 (fun s' ->
          evicted_transition rI sS transition keep_dec s0 s')))
      (sO.sum_over_S_ext (fun s' ->
        mult0
          (evicted_boltzmann rI sS sO d d_pos energy keep_dec
            evicted_partition_pos s')
          (evicted_transition rI sS transition keep_dec s' s0))
        (fun s' ->
        mult0
          (evicted_boltzmann rI sS sO d d_pos energy keep_dec
            evicted_partition_pos s0)
          (evicted_transition rI sS transition keep_dec s0 s'))
        (fun s' ->
        id_sym
          (mult0
            (evicted_boltzmann rI sS sO d d_pos energy keep_dec
              evicted_partition_pos s0)
            (evicted_transition rI sS transition keep_dec s0 s'))
          (mult0
            (evicted_boltzmann rI sS sO d d_pos energy keep_dec
              evicted_partition_pos s')
            (evicted_transition rI sS transition keep_dec s' s0))
          (evicted_db_products rI sS sO d d_pos energy z_thermo_pos
            transition detailed_balance keep_dec evicted_partition_pos s' s0)))
      (sO.sum_over_S_linear
        (evicted_boltzmann rI sS sO d d_pos energy keep_dec
          evicted_partition_pos s0)
        (fun s' -> evicted_transition rI sS transition keep_dec s0 s'))

  (** val eviction_transition_pointwise_full :
      realInterfaceEnhanced -> stateSpace -> (s -> s -> r) -> (s -> ('a1, 'a1
      not) or0) -> (s -> 'a1) -> s -> s -> r id **)

  let eviction_transition_pointwise_full _ _ _ keep_dec _ s0 s' =
    let o = keep_dec s0 in
    (match o with
     | Inl _ ->
       let o0 = keep_dec s' in
       (match o0 with
        | Inl _ -> Id_refl
        | Inr _ -> assert false (* absurd case *))
     | Inr _ -> assert false (* absurd case *))

  (** val evicted_transition_row_sum_one :
      realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> s -> r) -> (s
      -> r id) -> (s -> ('a1, 'a1 not) or0) -> (s -> 'a1) -> s -> r id **)

  let evicted_transition_row_sum_one rI sS sO transition transition_normalization keep_dec x s0 =
    let one0 = rI.rI_base.one in
    id_trans
      (sO.sum_over_S (fun s' ->
        evicted_transition rI sS transition keep_dec s0 s'))
      (sO.sum_over_S (fun s' -> transition s0 s')) one0
      (sO.sum_over_S_ext (fun s' ->
        evicted_transition rI sS transition keep_dec s0 s') (fun s' ->
        transition s0 s') (fun s' ->
        eviction_transition_pointwise_full rI sS transition keep_dec x s0 s'))
      (transition_normalization s0)

  (** val evicted_boltzmann_steady_full_keep :
      realInterfaceEnhanced -> stateSpace -> sumOver -> r -> lt -> (s -> r)
      -> lt -> (s -> s -> r) -> (s -> r id) -> (s -> s -> r id) -> (s ->
      ('a1, 'a1 not) or0) -> lt -> (s -> 'a1) -> s -> r id **)

  let evicted_boltzmann_steady_full_keep rI sS sO d d_pos energy z_thermo_pos transition transition_normalization detailed_balance keep_dec evicted_partition_pos x s0 =
    let one0 = rI.rI_base.one in
    let mult0 = rI.rI_base.mult in
    let sum_over_S0 = sO.sum_over_S in
    id_trans
      (sum_over_S0 (fun s' ->
        mult0
          (evicted_boltzmann rI sS sO d d_pos energy keep_dec
            evicted_partition_pos s')
          (evicted_transition rI sS transition keep_dec s' s0)))
      (mult0
        (evicted_boltzmann rI sS sO d d_pos energy keep_dec
          evicted_partition_pos s0)
        (sum_over_S0 (fun s' ->
          evicted_transition rI sS transition keep_dec s0 s')))
      (evicted_boltzmann rI sS sO d d_pos energy keep_dec
        evicted_partition_pos s0)
      (evicted_boltzmann_steady_exact rI sS sO d d_pos energy z_thermo_pos
        transition detailed_balance keep_dec evicted_partition_pos s0)
      (id_trans
        (mult0
          (evicted_boltzmann rI sS sO d d_pos energy keep_dec
            evicted_partition_pos s0)
          (sum_over_S0 (fun s' ->
            evicted_transition rI sS transition keep_dec s0 s')))
        (mult0
          (evicted_boltzmann rI sS sO d d_pos energy keep_dec
            evicted_partition_pos s0)
          one0)
        (evicted_boltzmann rI sS sO d d_pos energy keep_dec
          evicted_partition_pos s0)
        (id_cong (fun x0 ->
          mult0
            (evicted_boltzmann rI sS sO d d_pos energy keep_dec
              evicted_partition_pos s0)
            x0)
          (sum_over_S0 (fun s' ->
            evicted_transition rI sS transition keep_dec s0 s'))
          one0
          (evicted_transition_row_sum_one rI sS sO transition
            transition_normalization keep_dec x s0))
        (rI.rI_base.mult_one
          (evicted_boltzmann rI sS sO d d_pos energy keep_dec
            evicted_partition_pos s0)))

  (** val eviction_steady_deviation_zero :
      realInterfaceEnhanced -> stateSpace -> sumOver -> r -> lt -> (s -> r)
      -> lt -> (s -> s -> r) -> (s -> s -> r id) -> (s -> ('a1, 'a1 not) or0)
      -> lt -> s -> r id **)

  let eviction_steady_deviation_zero rI sS sO d d_pos energy z_thermo_pos transition detailed_balance keep_dec evicted_partition_pos s0 =
    let zero0 = rI.rI_base.zero in
    let mult0 = rI.rI_base.mult in
    let abs0 = rI.rI_base.abs in
    let sum_over_S0 = sO.sum_over_S in
    id_trans
      (abs0
        (minus rI.rI_base
          (sum_over_S0 (fun s' ->
            mult0
              (evicted_boltzmann rI sS sO d d_pos energy keep_dec
                evicted_partition_pos s')
              (evicted_transition rI sS transition keep_dec s' s0)))
          (mult0
            (evicted_boltzmann rI sS sO d d_pos energy keep_dec
              evicted_partition_pos s0)
            (sum_over_S0 (fun s' ->
              evicted_transition rI sS transition keep_dec s0 s')))))
      (abs0 rI.rI_base.zero) zero0
      (id_cong abs0
        (minus rI.rI_base
          (sum_over_S0 (fun s' ->
            mult0
              (evicted_boltzmann rI sS sO d d_pos energy keep_dec
                evicted_partition_pos s')
              (evicted_transition rI sS transition keep_dec s' s0)))
          (mult0
            (evicted_boltzmann rI sS sO d d_pos energy keep_dec
              evicted_partition_pos s0)
            (sum_over_S0 (fun s' ->
              evicted_transition rI sS transition keep_dec s0 s'))))
        rI.rI_base.zero
        (minus_self_zero rI
          (sum_over_S0 (fun s' ->
            mult0
              (evicted_boltzmann rI sS sO d d_pos energy keep_dec
                evicted_partition_pos s')
              (evicted_transition rI sS transition keep_dec s' s0)))
          (mult0
            (evicted_boltzmann rI sS sO d d_pos energy keep_dec
              evicted_partition_pos s0)
            (sum_over_S0 (fun s' ->
              evicted_transition rI sS transition keep_dec s0 s')))
          (evicted_boltzmann_steady_exact rI sS sO d d_pos energy
            z_thermo_pos transition detailed_balance keep_dec
            evicted_partition_pos s0)))
      rI.abs_zero

  (** val partition_increment_pointwise :
      realInterfaceEnhanced -> stateSpace -> r -> lt -> (s -> r) -> (s -> 'a1
      -> 'a2) -> (s -> ('a1, 'a1 not) or0) -> (s -> ('a2, 'a2 not) or0) -> s
      -> r id **)

  let partition_increment_pointwise rI sS d d_pos energy _ kd1 kd2 s0 =
    let zero0 = rI.rI_base.zero in
    let o = kd1 s0 in
    (match o with
     | Inl _ ->
       let o0 = kd2 s0 in
       (match o0 with
        | Inl _ ->
          minus_self_zero rI (boltzmann_factor rI sS d d_pos energy s0)
            (boltzmann_factor rI sS d d_pos energy s0) Id_refl
        | Inr _ -> assert false (* absurd case *))
     | Inr _ ->
       let o0 = kd2 s0 in
       (match o0 with
        | Inl _ ->
          minus_zero_r_u rI (boltzmann_factor rI sS d d_pos energy s0)
        | Inr _ -> minus_self_zero rI zero0 zero0 Id_refl))

  (** val eviction_partition_increment :
      realInterfaceEnhanced -> stateSpace -> sumOver -> r -> lt -> (s -> r)
      -> (s -> 'a1 -> 'a2) -> (s -> ('a1, 'a1 not) or0) -> (s -> ('a2, 'a2
      not) or0) -> r id **)

  let eviction_partition_increment rI sS sO d d_pos energy hsub kd1 kd2 =
    let zero0 = rI.rI_base.zero in
    let sum_over_S0 = sO.sum_over_S in
    id_trans
      (minus rI.rI_base
        (sO.sum_over_S (fun s0 ->
          match kd2 s0 with
          | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
          | Inr _ -> zero0))
        (sO.sum_over_S (fun s0 ->
          match kd1 s0 with
          | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
          | Inr _ -> zero0)))
      (sO.sum_over_S (fun s0 ->
        minus rI.rI_base
          (match kd2 s0 with
           | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
           | Inr _ -> zero0)
          (match kd1 s0 with
           | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
           | Inr _ -> zero0)))
      (sum_over_S0 (fun s0 ->
        match kd2 s0 with
        | Inl _ ->
          (match kd1 s0 with
           | Inl _ -> zero0
           | Inr _ -> boltzmann_factor rI sS d d_pos energy s0)
        | Inr _ -> zero0))
      (id_sym
        (sO.sum_over_S (fun s0 ->
          minus rI.rI_base
            (match kd2 s0 with
             | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
             | Inr _ -> zero0)
            (match kd1 s0 with
             | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
             | Inr _ -> zero0)))
        (minus rI.rI_base
          (sO.sum_over_S (fun s0 ->
            match kd2 s0 with
            | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
            | Inr _ -> zero0))
          (sO.sum_over_S (fun s0 ->
            match kd1 s0 with
            | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
            | Inr _ -> zero0)))
        (sum_over_S_minus rI sS sO (fun s0 ->
          match kd2 s0 with
          | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
          | Inr _ -> zero0) (fun s0 ->
          match kd1 s0 with
          | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
          | Inr _ -> zero0)))
      (sO.sum_over_S_ext (fun s0 ->
        minus rI.rI_base
          (match kd2 s0 with
           | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
           | Inr _ -> zero0)
          (match kd1 s0 with
           | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
           | Inr _ -> zero0))
        (fun s0 ->
        match kd2 s0 with
        | Inl _ ->
          (match kd1 s0 with
           | Inl _ -> zero0
           | Inr _ -> boltzmann_factor rI sS d d_pos energy s0)
        | Inr _ -> zero0) (fun s0 ->
        partition_increment_pointwise rI sS d d_pos energy hsub kd1 kd2 s0))

  (** val eviction_partition_le_full_exact :
      realInterfaceEnhanced -> stateSpace -> sumOver -> r -> lt -> (s -> r)
      -> (s -> ('a1, 'a1 not) or0) -> r id **)

  let eviction_partition_le_full_exact rI sS sO d d_pos energy kd =
    let zero0 = rI.rI_base.zero in
    let sum_over_S0 = sO.sum_over_S in
    id_trans
      (minus rI.rI_base
        (sO.sum_over_S (boltzmann_factor rI sS d d_pos energy))
        (sO.sum_over_S (fun s0 ->
          match kd s0 with
          | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
          | Inr _ -> zero0)))
      (sO.sum_over_S (fun s0 ->
        minus rI.rI_base (boltzmann_factor rI sS d d_pos energy s0)
          (match kd s0 with
           | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
           | Inr _ -> zero0)))
      (sum_over_S0 (fun s0 ->
        match kd s0 with
        | Inl _ -> zero0
        | Inr _ -> boltzmann_factor rI sS d d_pos energy s0))
      (id_sym
        (sO.sum_over_S (fun s0 ->
          minus rI.rI_base (boltzmann_factor rI sS d d_pos energy s0)
            (match kd s0 with
             | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
             | Inr _ -> zero0)))
        (minus rI.rI_base
          (sO.sum_over_S (boltzmann_factor rI sS d d_pos energy))
          (sO.sum_over_S (fun s0 ->
            match kd s0 with
            | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
            | Inr _ -> zero0)))
        (sum_over_S_minus rI sS sO (boltzmann_factor rI sS d d_pos energy)
          (fun s0 ->
          match kd s0 with
          | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
          | Inr _ -> zero0)))
      (sO.sum_over_S_ext (fun s0 ->
        minus rI.rI_base (boltzmann_factor rI sS d d_pos energy s0)
          (match kd s0 with
           | Inl _ -> boltzmann_factor rI sS d d_pos energy s0
           | Inr _ -> zero0))
        (fun s0 ->
        match kd s0 with
        | Inl _ -> zero0
        | Inr _ -> boltzmann_factor rI sS d d_pos energy s0) (fun s0 ->
        let o = kd s0 in
        (match o with
         | Inl _ ->
           minus_self_zero rI (boltzmann_factor rI sS d d_pos energy s0)
             (boltzmann_factor rI sS d d_pos energy s0) Id_refl
         | Inr _ ->
           minus_zero_r_u rI (boltzmann_factor rI sS d d_pos energy s0))))
 end
