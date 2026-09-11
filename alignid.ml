
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

(** val id_cong2 :
    ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 id -> 'a2 id ->
    'a3 id **)

let id_cong2 _ _ _ _ _ _ _ =
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

(** val opp_plus : realInterfaceEnhanced -> r -> r -> r id **)

let opp_plus rI =
  let internal_Id_rew = fun _ f _ _ -> f in
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun a b ->
  id_sym (rI.rI_base.plus (rI.rI_base.opp a) (rI.rI_base.opp b))
    (rI.rI_base.opp (rI.rI_base.plus a b))
    (plus_inv_unique rI (rI.rI_base.plus a b)
      (rI.rI_base.plus (rI.rI_base.opp a) (rI.rI_base.opp b))
      (rI.rI_base.opp (rI.rI_base.plus a b))
      (internal_Id_rew
        (rI.rI_base.plus a
          (rI.rI_base.plus b
            (rI.rI_base.plus (rI.rI_base.opp a) (rI.rI_base.opp b))))
        (internal_Id_rew_r
          (rI.rI_base.plus b
            (rI.rI_base.plus (rI.rI_base.opp a) (rI.rI_base.opp b)))
          (rI.rI_base.plus (rI.rI_base.plus b (rI.rI_base.opp a))
            (rI.rI_base.opp b))
          (internal_Id_rew_r (rI.rI_base.plus b (rI.rI_base.opp a))
            (rI.rI_base.plus (rI.rI_base.opp a) b)
            (internal_Id_rew
              (rI.rI_base.plus (rI.rI_base.opp a)
                (rI.rI_base.plus b (rI.rI_base.opp b)))
              (internal_Id_rew_r (rI.rI_base.plus b (rI.rI_base.opp b))
                rI.rI_base.zero
                (internal_Id_rew_r
                  (rI.rI_base.plus (rI.rI_base.opp a) rI.rI_base.zero)
                  (rI.rI_base.opp a) (rI.rI_base.plus_opp a)
                  (rI.rI_base.plus_zero (rI.rI_base.opp a)))
                (rI.rI_base.plus_opp b))
              (rI.rI_base.plus (rI.rI_base.plus (rI.rI_base.opp a) b)
                (rI.rI_base.opp b))
              (rI.rI_base.plus_assoc (rI.rI_base.opp a) b (rI.rI_base.opp b)))
            (rI.rI_base.plus_comm b (rI.rI_base.opp a)))
          (rI.rI_base.plus_assoc b (rI.rI_base.opp a) (rI.rI_base.opp b)))
        (rI.rI_base.plus (rI.rI_base.plus a b)
          (rI.rI_base.plus (rI.rI_base.opp a) (rI.rI_base.opp b)))
        (rI.rI_base.plus_assoc a b
          (rI.rI_base.plus (rI.rI_base.opp a) (rI.rI_base.opp b))))
      (rI.rI_base.plus_opp (rI.rI_base.plus a b))))

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

(** val opp_mult_l : realInterfaceEnhanced -> r -> r -> r id **)

let opp_mult_l rI =
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun a b ->
  internal_Id_rew_r (rI.rI_base.mult a (rI.rI_base.opp b))
    (rI.rI_base.mult (rI.rI_base.opp b) a)
    (internal_Id_rew_r (rI.rI_base.mult (rI.rI_base.opp b) a)
      (rI.rI_base.opp (rI.rI_base.mult b a))
      (internal_Id_rew_r (rI.rI_base.mult b a) (rI.rI_base.mult a b) Id_refl
        (rI.rI_base.mult_comm b a))
      (opp_mult_r rI b a))
    (rI.rI_base.mult_comm a (rI.rI_base.opp b)))

(** val double_neg : realInterfaceEnhanced -> r -> r id **)

let double_neg rI a =
  id_sym a (rI.rI_base.opp (rI.rI_base.opp a))
    (let h1 = rI.rI_base.plus_zero a in
     let h2 = id_sym (rI.rI_base.plus a rI.rI_base.zero) a h1 in
     let h3 = rI.rI_base.plus_opp (rI.rI_base.opp a) in
     let h4 =
       id_sym
         (rI.rI_base.plus (rI.rI_base.opp a)
           (rI.rI_base.opp (rI.rI_base.opp a)))
         rI.rI_base.zero h3
     in
     let h5 =
       id_cong (fun x -> rI.rI_base.plus a x) rI.rI_base.zero
         (rI.rI_base.plus (rI.rI_base.opp a)
           (rI.rI_base.opp (rI.rI_base.opp a)))
         h4
     in
     let h6 =
       rI.rI_base.plus_assoc a (rI.rI_base.opp a)
         (rI.rI_base.opp (rI.rI_base.opp a))
     in
     let h10 = rI.rI_base.plus_opp a in
     let h7 =
       id_cong (fun x ->
         rI.rI_base.plus x (rI.rI_base.opp (rI.rI_base.opp a)))
         (rI.rI_base.plus a (rI.rI_base.opp a)) rI.rI_base.zero h10
     in
     let h8 =
       rI.rI_base.plus_comm rI.rI_base.zero
         (rI.rI_base.opp (rI.rI_base.opp a))
     in
     let h12 = rI.rI_base.plus_zero (rI.rI_base.opp (rI.rI_base.opp a)) in
     id_trans a (rI.rI_base.plus a rI.rI_base.zero)
       (rI.rI_base.opp (rI.rI_base.opp a)) h2
       (id_trans (rI.rI_base.plus a rI.rI_base.zero)
         (rI.rI_base.plus a
           (rI.rI_base.plus (rI.rI_base.opp a)
             (rI.rI_base.opp (rI.rI_base.opp a))))
         (rI.rI_base.opp (rI.rI_base.opp a)) h5
         (id_trans
           (rI.rI_base.plus a
             (rI.rI_base.plus (rI.rI_base.opp a)
               (rI.rI_base.opp (rI.rI_base.opp a))))
           (rI.rI_base.plus (rI.rI_base.plus a (rI.rI_base.opp a))
             (rI.rI_base.opp (rI.rI_base.opp a)))
           (rI.rI_base.opp (rI.rI_base.opp a)) h6
           (id_trans
             (rI.rI_base.plus (rI.rI_base.plus a (rI.rI_base.opp a))
               (rI.rI_base.opp (rI.rI_base.opp a)))
             (rI.rI_base.plus rI.rI_base.zero
               (rI.rI_base.opp (rI.rI_base.opp a)))
             (rI.rI_base.opp (rI.rI_base.opp a)) h7
             (id_trans
               (rI.rI_base.plus rI.rI_base.zero
                 (rI.rI_base.opp (rI.rI_base.opp a)))
               (rI.rI_base.plus (rI.rI_base.opp (rI.rI_base.opp a))
                 rI.rI_base.zero)
               (rI.rI_base.opp (rI.rI_base.opp a)) h8 h12)))))

(** val plus_swap_mid : realInterfaceEnhanced -> r -> r -> r -> r -> r id **)

let plus_swap_mid rI =
  let internal_Id_rew = fun _ f _ _ -> f in
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun a b c d ->
  internal_Id_rew
    (rI.rI_base.plus a (rI.rI_base.plus b (rI.rI_base.plus c d)))
    (internal_Id_rew_r (rI.rI_base.plus b (rI.rI_base.plus c d))
      (rI.rI_base.plus (rI.rI_base.plus b c) d)
      (internal_Id_rew_r (rI.rI_base.plus b c) (rI.rI_base.plus c b)
        (internal_Id_rew (rI.rI_base.plus c (rI.rI_base.plus b d))
          (internal_Id_rew
            (rI.rI_base.plus a (rI.rI_base.plus c (rI.rI_base.plus b d)))
            Id_refl
            (rI.rI_base.plus (rI.rI_base.plus a c) (rI.rI_base.plus b d))
            (rI.rI_base.plus_assoc a c (rI.rI_base.plus b d)))
          (rI.rI_base.plus (rI.rI_base.plus c b) d)
          (rI.rI_base.plus_assoc c b d))
        (rI.rI_base.plus_comm b c))
      (rI.rI_base.plus_assoc b c d))
    (rI.rI_base.plus (rI.rI_base.plus a b) (rI.rI_base.plus c d))
    (rI.rI_base.plus_assoc a b (rI.rI_base.plus c d)))

(** val log_exp_neg : realInterfaceEnhanced -> r -> r id **)

let log_exp_neg rI x =
  let h1 = rI.rI_base.log_inv_exp_neg x in
  let h2 = rI.log_inv_log (rI.rI_base.exp_neg x) (rI.rI_base.exp_neg_pos x) in
  let h3 =
    id_trans x (rI.rI_base.log_inv (rI.rI_base.exp_neg x))
      (rI.rI_base.opp (rI.log (rI.rI_base.exp_neg x)))
      (id_sym (rI.rI_base.log_inv (rI.rI_base.exp_neg x)) x h1) h2
  in
  id_trans (rI.log (rI.rI_base.exp_neg x))
    (rI.rI_base.opp (rI.rI_base.opp (rI.log (rI.rI_base.exp_neg x))))
    (rI.rI_base.opp x)
    (id_sym (rI.rI_base.opp (rI.rI_base.opp (rI.log (rI.rI_base.exp_neg x))))
      (rI.log (rI.rI_base.exp_neg x))
      (double_neg rI (rI.log (rI.rI_base.exp_neg x))))
    (id_cong rI.rI_base.opp (rI.rI_base.opp (rI.log (rI.rI_base.exp_neg x)))
      x (id_sym x (rI.rI_base.opp (rI.log (rI.rI_base.exp_neg x))) h3))

(** val log_inv_one_inv : realInterfaceEnhanced -> r -> lt -> r id **)

let log_inv_one_inv rI x hx =
  let hprod =
    id_trans (rI.rI_base.mult (rI.rI_base.inv_pos x hx) x)
      (rI.rI_base.mult x (rI.rI_base.inv_pos x hx)) rI.rI_base.one
      (rI.rI_base.mult_comm (rI.rI_base.inv_pos x hx) x)
      (rI.rI_base.inv_pos_correct x hx)
  in
  let hlm = rI.log_mult (rI.rI_base.inv_pos x hx) x (rI.inv_pos_pos x hx) hx
  in
  let hz =
    let hl1 =
      id_trans (rI.log (rI.rI_base.mult (rI.rI_base.inv_pos x hx) x))
        (rI.log rI.rI_base.one) rI.rI_base.zero
        (id_cong rI.log (rI.rI_base.mult (rI.rI_base.inv_pos x hx) x)
          rI.rI_base.one hprod)
        rI.log_one
    in
    id_trans (rI.rI_base.plus (rI.log (rI.rI_base.inv_pos x hx)) (rI.log x))
      (rI.log (rI.rI_base.mult (rI.rI_base.inv_pos x hx) x)) rI.rI_base.zero
      (id_sym (rI.log (rI.rI_base.mult (rI.rI_base.inv_pos x hx) x))
        (rI.rI_base.plus (rI.log (rI.rI_base.inv_pos x hx)) (rI.log x)) hlm)
      hl1
  in
  plus_inv_unique rI (rI.log x) (rI.log (rI.rI_base.inv_pos x hx))
    (rI.rI_base.opp (rI.log x))
    (id_trans (rI.rI_base.plus (rI.log x) (rI.log (rI.rI_base.inv_pos x hx)))
      (rI.rI_base.plus (rI.log (rI.rI_base.inv_pos x hx)) (rI.log x))
      rI.rI_base.zero
      (rI.rI_base.plus_comm (rI.log x) (rI.log (rI.rI_base.inv_pos x hx))) hz)
    (rI.rI_base.plus_opp (rI.log x))

(** val exp_neg_opp_log : realInterfaceEnhanced -> r -> lt -> r id **)

let exp_neg_opp_log rI x hx =
  let h1 = rI.log_inv_log x hx in
  let h2 =
    id_cong (fun t -> rI.rI_base.exp_neg t) (rI.rI_base.opp (rI.log x))
      (rI.rI_base.log_inv x)
      (id_sym (rI.rI_base.log_inv x) (rI.rI_base.opp (rI.log x)) h1)
  in
  let h3 = rI.exp_neg_log_inv x in
  id_trans (rI.rI_base.exp_neg (rI.rI_base.opp (rI.log x)))
    (rI.rI_base.exp_neg (rI.rI_base.log_inv x)) x h2 h3

(** val exp_neg_opp_plus : realInterfaceEnhanced -> r -> r -> r id **)

let exp_neg_opp_plus rI a b =
  let h1 = opp_plus rI a b in
  let h2 =
    id_cong (fun t -> rI.rI_base.exp_neg t)
      (rI.rI_base.opp (rI.rI_base.plus a b))
      (rI.rI_base.plus (rI.rI_base.opp a) (rI.rI_base.opp b)) h1
  in
  let h3 = rI.rI_base.exp_neg_plus (rI.rI_base.opp a) (rI.rI_base.opp b) in
  id_trans (rI.rI_base.exp_neg (rI.rI_base.opp (rI.rI_base.plus a b)))
    (rI.rI_base.exp_neg
      (rI.rI_base.plus (rI.rI_base.opp a) (rI.rI_base.opp b)))
    (rI.rI_base.mult (rI.rI_base.exp_neg (rI.rI_base.opp a))
      (rI.rI_base.exp_neg (rI.rI_base.opp b)))
    h2 h3

(** val minus_plus_cancel : realInterfaceEnhanced -> r -> r -> r id **)

let minus_plus_cancel rI =
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  let internal_Id_rew = fun _ f _ _ -> f in
  (fun a b ->
  internal_Id_rew_r
    (rI.rI_base.plus a (rI.rI_base.plus b (rI.rI_base.opp a)))
    (rI.rI_base.plus (rI.rI_base.plus a b) (rI.rI_base.opp a))
    (internal_Id_rew_r (rI.rI_base.plus a b) (rI.rI_base.plus b a)
      (internal_Id_rew
        (rI.rI_base.plus b (rI.rI_base.plus a (rI.rI_base.opp a)))
        (internal_Id_rew_r (rI.rI_base.plus a (rI.rI_base.opp a))
          rI.rI_base.zero
          (internal_Id_rew_r (rI.rI_base.plus b rI.rI_base.zero) b Id_refl
            (rI.rI_base.plus_zero b))
          (rI.rI_base.plus_opp a))
        (rI.rI_base.plus (rI.rI_base.plus b a) (rI.rI_base.opp a))
        (rI.rI_base.plus_assoc b a (rI.rI_base.opp a)))
      (rI.rI_base.plus_comm a b))
    (rI.rI_base.plus_assoc a b (rI.rI_base.opp a)))

(** val opp_minus : realInterfaceEnhanced -> r -> r -> r id **)

let opp_minus rI =
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun a b ->
  internal_Id_rew_r (rI.rI_base.opp (rI.rI_base.plus a (rI.rI_base.opp b)))
    (rI.rI_base.plus (rI.rI_base.opp a) (rI.rI_base.opp (rI.rI_base.opp b)))
    (internal_Id_rew_r (rI.rI_base.opp (rI.rI_base.opp b)) b Id_refl
      (double_neg rI b))
    (opp_plus rI a (rI.rI_base.opp b)))

(** val mult_minus_distr_l : realInterfaceEnhanced -> r -> r -> r -> r id **)

let mult_minus_distr_l rI =
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun a b c ->
  internal_Id_rew_r
    (rI.rI_base.mult a (rI.rI_base.plus b (rI.rI_base.opp c)))
    (rI.rI_base.plus (rI.rI_base.mult a b)
      (rI.rI_base.mult a (rI.rI_base.opp c)))
    (internal_Id_rew_r (rI.rI_base.mult a (rI.rI_base.opp c))
      (rI.rI_base.opp (rI.rI_base.mult a c)) Id_refl (opp_mult_l rI a c))
    (rI.rI_base.distrib a b (rI.rI_base.opp c)))

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

(** val minus_plus_cancel_gap : realInterfaceEnhanced -> r -> r -> r id **)

let minus_plus_cancel_gap rI =
  let plus0 = rI.rI_base.plus in
  let opp0 = rI.rI_base.opp in
  (fun a b ->
  id_trans (rI.rI_base.plus (rI.rI_base.plus a (opp0 b)) b)
    (rI.rI_base.plus a (rI.rI_base.plus (opp0 b) b)) a
    (id_sym (rI.rI_base.plus a (rI.rI_base.plus (opp0 b) b))
      (rI.rI_base.plus (rI.rI_base.plus a (opp0 b)) b)
      (rI.rI_base.plus_assoc a (opp0 b) b))
    (id_trans (plus0 a (rI.rI_base.plus (opp0 b) b))
      (plus0 a (rI.rI_base.plus b (opp0 b))) a
      (id_cong (fun z -> plus0 a z) (rI.rI_base.plus (opp0 b) b)
        (rI.rI_base.plus b (opp0 b)) (rI.rI_base.plus_comm (opp0 b) b))
      (id_trans (plus0 a (rI.rI_base.plus b (rI.rI_base.opp b)))
        (plus0 a rI.rI_base.zero) a
        (id_cong (fun z -> plus0 a z) (rI.rI_base.plus b (rI.rI_base.opp b))
          rI.rI_base.zero (rI.rI_base.plus_opp b))
        (rI.rI_base.plus_zero a))))

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

type normalized = r id

type positive_dist = s -> lt

(** val boltzmann_dist :
    realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> lt -> r -> lt ->
    s -> r **)

let boltzmann_dist rI _ =
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  (fun base_loss d d_pos z z_pos s0 ->
  mult0 (inv_pos0 z z_pos)
    (exp_neg0 (mult0 (inv_pos0 d d_pos) (base_loss s0))))

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

(** val boltzmann_normalized :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    r -> lt -> r id -> r id **)

let boltzmann_normalized rI _ sO =
  let one0 = rI.rI_base.one in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  let sum_over_S0 = sO.sum_over_S in
  (fun base_loss d d_pos z z_pos partition_condition ->
  let hlin =
    sO.sum_over_S_linear (inv_pos0 z z_pos) (fun s0 ->
      exp_neg0 (mult0 (inv_pos0 d d_pos) (base_loss s0)))
  in
  let hZ =
    id_sym z
      (sum_over_S0 (fun s0 ->
        exp_neg0 (mult0 (inv_pos0 d d_pos) (base_loss s0))))
      partition_condition
  in
  let hcc =
    id_trans (rI.rI_base.mult (inv_pos0 z z_pos) z)
      (rI.rI_base.mult z (inv_pos0 z z_pos)) rI.rI_base.one
      (rI.rI_base.mult_comm (inv_pos0 z z_pos) z)
      (rI.rI_base.inv_pos_correct z z_pos)
  in
  id_trans
    (sum_over_S0 (fun s0 ->
      mult0 (inv_pos0 z z_pos)
        (exp_neg0 (mult0 (inv_pos0 d d_pos) (base_loss s0)))))
    (mult0 (inv_pos0 z z_pos)
      (sum_over_S0 (fun s0 ->
        exp_neg0 (mult0 (inv_pos0 d d_pos) (base_loss s0)))))
    one0 hlin
    (id_trans
      (mult0 (inv_pos0 z z_pos)
        (sum_over_S0 (fun s0 ->
          exp_neg0 (mult0 (inv_pos0 d d_pos) (base_loss s0)))))
      (mult0 (inv_pos0 z z_pos) z) one0
      (id_cong (fun x -> mult0 (inv_pos0 z z_pos) x)
        (sum_over_S0 (fun s0 ->
          exp_neg0 (mult0 (inv_pos0 d d_pos) (base_loss s0))))
        z hZ)
      hcc))

(** val boltzmann_log_decomp :
    realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> lt -> r -> lt ->
    s -> r id **)

let boltzmann_log_decomp rI _ =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  let log0 = rI.log in
  (fun base_loss d d_pos z z_pos ->
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun s0 ->
  let hpos1 = rI.inv_pos_pos z z_pos in
  let hpos2 = rI.rI_base.exp_neg_pos (mult0 (inv_pos0 d d_pos) (base_loss s0))
  in
  let hlm =
    rI.log_mult (inv_pos0 z z_pos)
      (exp_neg0 (mult0 (inv_pos0 d d_pos) (base_loss s0))) hpos1 hpos2
  in
  internal_Id_rew_r
    (log0
      (mult0 (inv_pos0 z z_pos)
        (exp_neg0 (mult0 (inv_pos0 d d_pos) (base_loss s0)))))
    (plus0 (log0 (inv_pos0 z z_pos))
      (log0 (exp_neg0 (mult0 (inv_pos0 d d_pos) (base_loss s0)))))
    (let hli = log_inv_one_inv rI z z_pos in
     internal_Id_rew_r (log0 (inv_pos0 z z_pos)) (rI.rI_base.opp (log0 z))
       (let hle = log_exp_neg rI (mult0 (inv_pos0 d d_pos) (base_loss s0)) in
        internal_Id_rew_r
          (log0 (exp_neg0 (mult0 (inv_pos0 d d_pos) (base_loss s0))))
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))) Id_refl
          hle)
       hli)
    hlm))

(** val free_energy_boltzmann :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    r -> lt -> r id -> r id **)

let free_energy_boltzmann rI sS sO =
  let zero0 = rI.rI_base.zero in
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  (fun base_loss d d_pos z z_pos partition_condition ->
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  let eavg =
    sum_over_S0 (fun s0 ->
      mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0) (base_loss s0))
  in
  let hdist = rI.rI_base.distrib in
  let hoppl = opp_mult_l rI in
  let hoppr = opp_mult_r rI in
  let hassoc = rI.rI_base.mult_assoc in
  let hcomm = rI.rI_base.mult_comm in
  let hmo = rI.rI_base.mult_one in
  let hpa = rI.rI_base.plus_assoc in
  let hpc = rI.rI_base.plus_comm in
  let hpz = rI.rI_base.plus_zero in
  let hpo = rI.rI_base.plus_opp in
  let hpoint = fun s0 ->
    let hld = boltzmann_log_decomp rI sS base_loss d d_pos z z_pos s0 in
    let hc =
      id_cong (fun x ->
        mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0) x)
        (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
        (plus0 (rI.rI_base.opp (log0 z))
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
        hld
    in
    internal_Id_rew_r
      (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
        (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))
      (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
        (plus0 (rI.rI_base.opp (log0 z))
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0)))))
      (internal_Id_rew_r
        (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
          (plus0 (rI.rI_base.opp (log0 z))
            (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0)))))
        (plus0
          (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
            (rI.rI_base.opp (log0 z)))
          (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
            (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0)))))
        (internal_Id_rew_r
          (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
            (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
          (rI.rI_base.opp
            (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
              (mult0 (inv_pos0 d d_pos) (base_loss s0))))
          (let hswap =
             let h1 =
               hassoc (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                 (inv_pos0 d d_pos) (base_loss s0)
             in
             let h2 =
               id_cong (fun x -> mult0 x (base_loss s0))
                 (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                   (inv_pos0 d d_pos))
                 (mult0 (inv_pos0 d d_pos)
                   (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
                 (hcomm (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                   (inv_pos0 d d_pos))
             in
             let h3 =
               id_sym
                 (mult0 (inv_pos0 d d_pos)
                   (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                     (base_loss s0)))
                 (mult0
                   (mult0 (inv_pos0 d d_pos)
                     (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
                   (base_loss s0))
                 (hassoc (inv_pos0 d d_pos)
                   (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                   (base_loss s0))
             in
             id_trans
               (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                 (mult0 (inv_pos0 d d_pos) (base_loss s0)))
               (mult0
                 (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                   (inv_pos0 d d_pos))
                 (base_loss s0))
               (mult0 (inv_pos0 d d_pos)
                 (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                   (base_loss s0)))
               h1
               (id_trans
                 (mult0
                   (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                     (inv_pos0 d d_pos))
                   (base_loss s0))
                 (mult0
                   (mult0 (inv_pos0 d d_pos)
                     (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
                   (base_loss s0))
                 (mult0 (inv_pos0 d d_pos)
                   (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                     (base_loss s0)))
                 h2 h3)
           in
           internal_Id_rew_r
             (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
               (mult0 (inv_pos0 d d_pos) (base_loss s0)))
             (mult0 (inv_pos0 d d_pos)
               (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                 (base_loss s0)))
             Id_refl hswap)
          (hoppl (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
            (mult0 (inv_pos0 d d_pos) (base_loss s0))))
        (hdist (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
          (rI.rI_base.opp (log0 z))
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0)))))
      hc
  in
  let hsum =
    let hext =
      sO.sum_over_S_ext (fun s0 ->
        mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
          (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))
        (fun s0 ->
        plus0
          (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
            (rI.rI_base.opp (log0 z)))
          (rI.rI_base.opp
            (mult0 (inv_pos0 d d_pos)
              (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                (base_loss s0)))))
        hpoint
    in
    internal_Id_rew_r
      (sum_over_S0 (fun s0 ->
        mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
          (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))
      (sum_over_S0 (fun s0 ->
        plus0
          (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
            (rI.rI_base.opp (log0 z)))
          (rI.rI_base.opp
            (mult0 (inv_pos0 d d_pos)
              (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                (base_loss s0))))))
      (let hadd =
         sO.sum_over_S_add (fun s0 ->
           mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
             (rI.rI_base.opp (log0 z)))
           (fun s0 ->
           rI.rI_base.opp
             (mult0 (inv_pos0 d d_pos)
               (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                 (base_loss s0))))
       in
       internal_Id_rew_r
         (sum_over_S0 (fun s0 ->
           plus0
             (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
               (rI.rI_base.opp (log0 z)))
             (rI.rI_base.opp
               (mult0 (inv_pos0 d d_pos)
                 (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                   (base_loss s0))))))
         (plus0
           (sum_over_S0 (fun s0 ->
             mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
               (rI.rI_base.opp (log0 z))))
           (sum_over_S0 (fun s0 ->
             rI.rI_base.opp
               (mult0 (inv_pos0 d d_pos)
                 (mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                   (base_loss s0))))))
         (let hsw1 =
            sO.sum_over_S_ext (fun s0 ->
              mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                (rI.rI_base.opp (log0 z)))
              (fun s0 ->
              mult0 (rI.rI_base.opp (log0 z))
                (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
              (fun s0 ->
              hcomm (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                (rI.rI_base.opp (log0 z)))
          in
          internal_Id_rew_r
            (sum_over_S0 (fun s0 ->
              mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
                (rI.rI_base.opp (log0 z))))
            (sum_over_S0 (fun s0 ->
              mult0 (rI.rI_base.opp (log0 z))
                (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))
            (let hlin1 =
               sO.sum_over_S_linear (rI.rI_base.opp (log0 z))
                 (boltzmann_dist rI sS base_loss d d_pos z z_pos)
             in
             internal_Id_rew_r
               (sum_over_S0 (fun s0 ->
                 mult0 (rI.rI_base.opp (log0 z))
                   (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))
               (mult0 (rI.rI_base.opp (log0 z))
                 (sum_over_S0
                   (boltzmann_dist rI sS base_loss d d_pos z z_pos)))
               (let hnorm =
                  boltzmann_normalized rI sS sO base_loss d d_pos z z_pos
                    partition_condition
                in
                internal_Id_rew_r
                  (sum_over_S0
                    (boltzmann_dist rI sS base_loss d d_pos z z_pos))
                  one0
                  (let hm1 = hmo (rI.rI_base.opp (log0 z)) in
                   internal_Id_rew_r (mult0 (rI.rI_base.opp (log0 z)) one0)
                     (rI.rI_base.opp (log0 z))
                     (let hso =
                        sum_opp rI sS sO (fun s0 ->
                          mult0 (inv_pos0 d d_pos)
                            (mult0
                              (boltzmann_dist rI sS base_loss d d_pos z z_pos
                                s0)
                              (base_loss s0)))
                      in
                      internal_Id_rew_r
                        (sum_over_S0 (fun s0 ->
                          rI.rI_base.opp
                            (mult0 (inv_pos0 d d_pos)
                              (mult0
                                (boltzmann_dist rI sS base_loss d d_pos z
                                  z_pos s0)
                                (base_loss s0)))))
                        (rI.rI_base.opp
                          (sum_over_S0 (fun s0 ->
                            mult0 (inv_pos0 d d_pos)
                              (mult0
                                (boltzmann_dist rI sS base_loss d d_pos z
                                  z_pos s0)
                                (base_loss s0)))))
                        (let hlin2 =
                           sO.sum_over_S_linear (inv_pos0 d d_pos) (fun s0 ->
                             mult0
                               (boltzmann_dist rI sS base_loss d d_pos z
                                 z_pos s0)
                               (base_loss s0))
                         in
                         internal_Id_rew_r
                           (sum_over_S0 (fun s0 ->
                             mult0 (inv_pos0 d d_pos)
                               (mult0
                                 (boltzmann_dist rI sS base_loss d d_pos z
                                   z_pos s0)
                                 (base_loss s0))))
                           (mult0 (inv_pos0 d d_pos)
                             (sum_over_S0 (fun s0 ->
                               mult0
                                 (boltzmann_dist rI sS base_loss d d_pos z
                                   z_pos s0)
                                 (base_loss s0))))
                           Id_refl hlin2)
                        hso)
                     hm1)
                  hnorm)
               hlin1)
            hsw1)
         hadd)
      hext
  in
  internal_Id_rew_r
    (sum_over_S0 (fun s0 ->
      mult0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)
        (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))
    (plus0 (rI.rI_base.opp (log0 z))
      (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) eavg)))
    (let hmd =
       internal_Id_rew_r
         (mult0 d
           (plus0 (rI.rI_base.opp (log0 z))
             (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) eavg))))
         (plus0 (mult0 d (rI.rI_base.opp (log0 z)))
           (mult0 d (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) eavg))))
         (internal_Id_rew_r (mult0 d (rI.rI_base.opp (log0 z)))
           (rI.rI_base.opp (mult0 d (log0 z)))
           (internal_Id_rew_r
             (mult0 d (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) eavg)))
             (rI.rI_base.opp (mult0 d (mult0 (inv_pos0 d d_pos) eavg)))
             (let hmd2 =
                let hcc1 =
                  let ht =
                    id_cong (fun x -> mult0 x eavg)
                      (rI.rI_base.mult d (rI.rI_base.inv_pos d d_pos))
                      rI.rI_base.one (rI.rI_base.inv_pos_correct d d_pos)
                  in
                  let ht2 = hcomm one0 eavg in
                  id_trans (mult0 (mult0 d (inv_pos0 d d_pos)) eavg)
                    (mult0 one0 eavg) eavg ht
                    (id_trans (mult0 one0 eavg) (mult0 eavg one0) eavg ht2
                      (hmo eavg))
                in
                id_trans (mult0 d (mult0 (inv_pos0 d d_pos) eavg))
                  (mult0 (mult0 d (inv_pos0 d d_pos)) eavg) eavg
                  (hassoc d (inv_pos0 d d_pos) eavg) hcc1
              in
              internal_Id_rew_r (mult0 d (mult0 (inv_pos0 d d_pos) eavg))
                eavg Id_refl hmd2)
             (hoppl d (mult0 (inv_pos0 d d_pos) eavg)))
           (hoppl d (log0 z)))
         (hdist d (rI.rI_base.opp (log0 z))
           (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) eavg)))
     in
     internal_Id_rew_r
       (mult0 d
         (plus0 (rI.rI_base.opp (log0 z))
           (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) eavg))))
       (plus0 (rI.rI_base.opp (mult0 d (log0 z))) (rI.rI_base.opp eavg))
       (let hfin =
          let h1 =
            hpa eavg (rI.rI_base.opp (mult0 d (log0 z))) (rI.rI_base.opp eavg)
          in
          let h2 =
            id_cong (fun y -> plus0 y (rI.rI_base.opp eavg))
              (plus0 eavg (rI.rI_base.opp (mult0 d (log0 z))))
              (plus0 (rI.rI_base.opp (mult0 d (log0 z))) eavg)
              (hpc eavg (rI.rI_base.opp (mult0 d (log0 z))))
          in
          let h3 =
            id_sym
              (plus0 (rI.rI_base.opp (mult0 d (log0 z)))
                (plus0 eavg (rI.rI_base.opp eavg)))
              (plus0 (plus0 (rI.rI_base.opp (mult0 d (log0 z))) eavg)
                (rI.rI_base.opp eavg))
              (hpa (rI.rI_base.opp (mult0 d (log0 z))) eavg
                (rI.rI_base.opp eavg))
          in
          let h4 =
            id_cong (fun y -> plus0 (rI.rI_base.opp (mult0 d (log0 z))) y)
              (plus0 eavg (rI.rI_base.opp eavg)) zero0 (hpo eavg)
          in
          let h5 = hpz (rI.rI_base.opp (mult0 d (log0 z))) in
          id_trans
            (plus0 eavg
              (plus0 (rI.rI_base.opp (mult0 d (log0 z)))
                (rI.rI_base.opp eavg)))
            (plus0 (plus0 eavg (rI.rI_base.opp (mult0 d (log0 z))))
              (rI.rI_base.opp eavg))
            (rI.rI_base.opp (mult0 d (log0 z))) h1
            (id_trans
              (plus0 (plus0 eavg (rI.rI_base.opp (mult0 d (log0 z))))
                (rI.rI_base.opp eavg))
              (plus0 (plus0 (rI.rI_base.opp (mult0 d (log0 z))) eavg)
                (rI.rI_base.opp eavg))
              (rI.rI_base.opp (mult0 d (log0 z))) h2
              (id_trans
                (plus0 (plus0 (rI.rI_base.opp (mult0 d (log0 z))) eavg)
                  (rI.rI_base.opp eavg))
                (plus0 (rI.rI_base.opp (mult0 d (log0 z)))
                  (plus0 eavg (rI.rI_base.opp eavg)))
                (rI.rI_base.opp (mult0 d (log0 z))) h3
                (id_trans
                  (plus0 (rI.rI_base.opp (mult0 d (log0 z)))
                    (plus0 eavg (rI.rI_base.opp eavg)))
                  (plus0 (rI.rI_base.opp (mult0 d (log0 z))) zero0)
                  (rI.rI_base.opp (mult0 d (log0 z))) h4 h5)))
        in
        let hoppr2 =
          id_sym (mult0 (rI.rI_base.opp d) (log0 z))
            (rI.rI_base.opp (mult0 d (log0 z))) (hoppr d (log0 z))
        in
        id_trans
          (plus0 eavg
            (plus0 (rI.rI_base.opp (mult0 d (log0 z))) (rI.rI_base.opp eavg)))
          (rI.rI_base.opp (mult0 d (log0 z)))
          (mult0 (rI.rI_base.opp d) (log0 z)) hfin hoppr2)
       hmd)
    hsum)

(** val energy_in_log_boltzmann :
    realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> lt -> r -> lt ->
    s -> r id **)

let energy_in_log_boltzmann rI sS =
  let zero0 = rI.rI_base.zero in
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let log0 = rI.log in
  (fun base_loss d d_pos z z_pos s0 ->
  let hlog = boltzmann_log_decomp rI sS base_loss d d_pos z z_pos s0 in
  let hsum =
    let hc =
      id_cong (fun x -> plus0 x (log0 z))
        (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
        (plus0 (rI.rI_base.opp (log0 z))
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
        hlog
    in
    let h1 =
      id_sym
        (rI.rI_base.plus (rI.rI_base.opp (log0 z))
          (rI.rI_base.plus
            (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0)))
            (log0 z)))
        (rI.rI_base.plus
          (rI.rI_base.plus (rI.rI_base.opp (log0 z))
            (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
          (log0 z))
        (rI.rI_base.plus_assoc (rI.rI_base.opp (log0 z))
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))) 
          (log0 z))
    in
    let h2 =
      id_cong (fun x -> plus0 (rI.rI_base.opp (log0 z)) x)
        (rI.rI_base.plus
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))) 
          (log0 z))
        (rI.rI_base.plus (log0 z)
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
        (rI.rI_base.plus_comm
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))) 
          (log0 z))
    in
    let h3 =
      rI.rI_base.plus_assoc (rI.rI_base.opp (log0 z)) (log0 z)
        (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0)))
    in
    let h4 =
      let h4a =
        id_cong (fun x ->
          plus0 x (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
          (rI.rI_base.plus (rI.rI_base.opp (log0 z)) (log0 z))
          (rI.rI_base.plus (log0 z) (rI.rI_base.opp (log0 z)))
          (rI.rI_base.plus_comm (rI.rI_base.opp (log0 z)) (log0 z))
      in
      let h4b =
        id_cong (fun x ->
          plus0 x (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
          (rI.rI_base.plus (log0 z) (rI.rI_base.opp (log0 z)))
          rI.rI_base.zero (rI.rI_base.plus_opp (log0 z))
      in
      id_trans
        (plus0 (plus0 (rI.rI_base.opp (log0 z)) (log0 z))
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
        (plus0 (plus0 (log0 z) (rI.rI_base.opp (log0 z)))
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
        (plus0 zero0
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
        h4a h4b
    in
    let h5 =
      id_trans
        (rI.rI_base.plus zero0
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
        (rI.rI_base.plus
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))) zero0)
        (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0)))
        (rI.rI_base.plus_comm zero0
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
        (rI.rI_base.plus_zero
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
    in
    id_trans
      (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
        (log0 z))
      (plus0
        (plus0 (rI.rI_base.opp (log0 z))
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
        (log0 z))
      (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))) hc
      (id_trans
        (plus0
          (plus0 (rI.rI_base.opp (log0 z))
            (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
          (log0 z))
        (plus0 (rI.rI_base.opp (log0 z))
          (plus0 (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0)))
            (log0 z)))
        (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))) h1
        (id_trans
          (plus0 (rI.rI_base.opp (log0 z))
            (plus0 (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0)))
              (log0 z)))
          (plus0 (rI.rI_base.opp (log0 z))
            (plus0 (log0 z)
              (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0)))))
          (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))) h2
          (id_trans
            (plus0 (rI.rI_base.opp (log0 z))
              (plus0 (log0 z)
                (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0)))))
            (plus0 (plus0 (rI.rI_base.opp (log0 z)) (log0 z))
              (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
            (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))) h3
            (id_trans
              (plus0 (plus0 (rI.rI_base.opp (log0 z)) (log0 z))
                (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
              (plus0 zero0
                (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
              (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))) h4
              h5))))
  in
  let hmd =
    let hc2 =
      id_cong (fun x -> mult0 d x)
        (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
          (log0 z))
        (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))) hsum
    in
    let hopp = opp_mult_l rI d (mult0 (inv_pos0 d d_pos) (base_loss s0)) in
    let hcc =
      let hma = rI.rI_base.mult_assoc d (inv_pos0 d d_pos) (base_loss s0) in
      let hic =
        id_cong (fun x -> mult0 x (base_loss s0))
          (rI.rI_base.mult d (rI.rI_base.inv_pos d d_pos)) rI.rI_base.one
          (rI.rI_base.inv_pos_correct d d_pos)
      in
      let hm1 =
        id_trans (rI.rI_base.mult one0 (base_loss s0))
          (rI.rI_base.mult (base_loss s0) one0) (base_loss s0)
          (rI.rI_base.mult_comm one0 (base_loss s0))
          (rI.rI_base.mult_one (base_loss s0))
      in
      id_trans (mult0 d (mult0 (inv_pos0 d d_pos) (base_loss s0)))
        (mult0 (mult0 d (inv_pos0 d d_pos)) (base_loss s0)) (base_loss s0)
        hma
        (id_trans (mult0 (mult0 d (inv_pos0 d d_pos)) (base_loss s0))
          (mult0 one0 (base_loss s0)) (base_loss s0) hic hm1)
    in
    id_trans
      (mult0 d
        (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
          (log0 z)))
      (mult0 d (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
      (rI.rI_base.opp (base_loss s0)) hc2
      (id_trans
        (mult0 d (rI.rI_base.opp (mult0 (inv_pos0 d d_pos) (base_loss s0))))
        (rI.rI_base.opp (mult0 d (mult0 (inv_pos0 d d_pos) (base_loss s0))))
        (rI.rI_base.opp (base_loss s0)) hopp
        (id_cong rI.rI_base.opp
          (mult0 d (mult0 (inv_pos0 d d_pos) (base_loss s0))) (base_loss s0)
          hcc))
  in
  let hinv =
    let hd =
      id_cong rI.rI_base.opp
        (mult0 d
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z)))
        (rI.rI_base.opp (base_loss s0)) hmd
    in
    let hdn = double_neg rI (base_loss s0) in
    id_trans
      (rI.rI_base.opp
        (mult0 d
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z))))
      (rI.rI_base.opp (rI.rI_base.opp (base_loss s0))) (base_loss s0) hd hdn
  in
  id_sym
    (rI.rI_base.opp
      (mult0 d
        (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
          (log0 z))))
    (base_loss s0) hinv)

(** val p_times_energy_decomp :
    realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> lt -> r -> lt ->
    (s -> r) -> s -> r id **)

let p_times_energy_decomp rI sS =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let log0 = rI.log in
  (fun base_loss d d_pos z z_pos p s0 ->
  let he = energy_in_log_boltzmann rI sS base_loss d d_pos z z_pos s0 in
  let hc =
    id_cong (fun x -> mult0 (p s0) x) (base_loss s0)
      (rI.rI_base.opp
        (mult0 d
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z))))
      he
  in
  let hopp =
    opp_mult_l rI (p s0)
      (mult0 d
        (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
          (log0 z)))
  in
  let hsw =
    let h1 =
      rI.rI_base.mult_assoc (p s0) d
        (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
          (log0 z))
    in
    let h2 =
      id_cong (fun x ->
        mult0 x
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z)))
        (rI.rI_base.mult (p s0) d) (rI.rI_base.mult d (p s0))
        (rI.rI_base.mult_comm (p s0) d)
    in
    let h3 =
      id_sym
        (rI.rI_base.mult d
          (rI.rI_base.mult (p s0)
            (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
              (log0 z))))
        (rI.rI_base.mult (rI.rI_base.mult d (p s0))
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z)))
        (rI.rI_base.mult_assoc d (p s0)
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z)))
    in
    id_trans
      (mult0 (p s0)
        (mult0 d
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z))))
      (mult0 (mult0 (p s0) d)
        (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
          (log0 z)))
      (mult0 d
        (mult0 (p s0)
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z))))
      h1
      (id_trans
        (mult0 (mult0 (p s0) d)
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z)))
        (mult0 (mult0 d (p s0))
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z)))
        (mult0 d
          (mult0 (p s0)
            (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
              (log0 z))))
        h2 h3)
  in
  let hdist =
    rI.rI_base.distrib (p s0)
      (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)) (log0 z)
  in
  let hsw2 =
    id_trans
      (mult0 (p s0)
        (mult0 d
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z))))
      (mult0 d
        (mult0 (p s0)
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z))))
      (mult0 d
        (plus0
          (mult0 (p s0)
            (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))
          (mult0 (p s0) (log0 z))))
      hsw
      (id_cong (fun x -> mult0 d x)
        (mult0 (p s0)
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z)))
        (plus0
          (mult0 (p s0)
            (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))
          (mult0 (p s0) (log0 z)))
        hdist)
  in
  let hdist2 =
    rI.rI_base.distrib d
      (mult0 (p s0)
        (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))
      (mult0 (p s0) (log0 z))
  in
  let htot =
    id_trans
      (mult0 (p s0)
        (mult0 d
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z))))
      (mult0 d
        (plus0
          (mult0 (p s0)
            (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))
          (mult0 (p s0) (log0 z))))
      (plus0
        (mult0 d
          (mult0 (p s0)
            (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))
        (mult0 d (mult0 (p s0) (log0 z))))
      hsw2 hdist2
  in
  let hop =
    opp_plus rI
      (mult0 d
        (mult0 (p s0)
          (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))
      (mult0 d (mult0 (p s0) (log0 z)))
  in
  let hc2 =
    id_cong rI.rI_base.opp
      (mult0 (p s0)
        (mult0 d
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z))))
      (plus0
        (mult0 d
          (mult0 (p s0)
            (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))
        (mult0 d (mult0 (p s0) (log0 z))))
      htot
  in
  id_trans (mult0 (p s0) (base_loss s0))
    (mult0 (p s0)
      (rI.rI_base.opp
        (mult0 d
          (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
            (log0 z)))))
    (plus0
      (rI.rI_base.opp
        (mult0 d
          (mult0 (p s0)
            (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
      (rI.rI_base.opp (mult0 d (mult0 (p s0) (log0 z)))))
    hc
    (id_trans
      (mult0 (p s0)
        (rI.rI_base.opp
          (mult0 d
            (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
              (log0 z)))))
      (rI.rI_base.opp
        (mult0 (p s0)
          (mult0 d
            (plus0 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
              (log0 z)))))
      (plus0
        (rI.rI_base.opp
          (mult0 d
            (mult0 (p s0)
              (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
        (rI.rI_base.opp (mult0 d (mult0 (p s0) (log0 z)))))
      hopp
      (id_trans
        (rI.rI_base.opp
          (mult0 (p s0)
            (mult0 d
              (plus0
                (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
                (log0 z)))))
        (rI.rI_base.opp
          (plus0
            (mult0 d
              (mult0 (p s0)
                (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))
            (mult0 d (mult0 (p s0) (log0 z)))))
        (plus0
          (rI.rI_base.opp
            (mult0 d
              (mult0 (p s0)
                (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
          (rI.rI_base.opp (mult0 d (mult0 (p s0) (log0 z)))))
        hc2 hop)))

(** val free_energy_kl_decomp :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    r -> lt -> r id -> (s -> r) -> normalized -> r id **)

let free_energy_kl_decomp rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  (fun base_loss d d_pos z z_pos partition_condition ->
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun p hnorm ->
  let hfe_p = Id_refl in
  internal_Id_rew_r (free_energy rI sS sO base_loss d p)
    (plus0 (sum_over_S0 (fun s0 -> mult0 (p s0) (base_loss s0)))
      (mult0 d (sum_over_S0 (fun s0 -> mult0 (p s0) (log0 (p s0))))))
    (let hse =
       let hpt = p_times_energy_decomp rI sS base_loss d d_pos z z_pos p in
       let hext =
         sO.sum_over_S_ext (fun s0 -> mult0 (p s0) (base_loss s0)) (fun s0 ->
           plus0
             (rI.rI_base.opp
               (mult0 d
                 (mult0 (p s0)
                   (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
             (rI.rI_base.opp (mult0 d (mult0 (p s0) (log0 z)))))
           hpt
       in
       internal_Id_rew_r
         (sum_over_S0 (fun s0 -> mult0 (p s0) (base_loss s0)))
         (sum_over_S0 (fun s0 ->
           plus0
             (rI.rI_base.opp
               (mult0 d
                 (mult0 (p s0)
                   (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
             (rI.rI_base.opp (mult0 d (mult0 (p s0) (log0 z))))))
         (let hadd =
            sO.sum_over_S_add (fun s0 ->
              rI.rI_base.opp
                (mult0 d
                  (mult0 (p s0)
                    (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
              (fun s0 -> rI.rI_base.opp (mult0 d (mult0 (p s0) (log0 z))))
          in
          internal_Id_rew_r
            (sum_over_S0 (fun s0 ->
              plus0
                (rI.rI_base.opp
                  (mult0 d
                    (mult0 (p s0)
                      (log0
                        (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
                (rI.rI_base.opp (mult0 d (mult0 (p s0) (log0 z))))))
            (plus0
              (sum_over_S0 (fun s0 ->
                rI.rI_base.opp
                  (mult0 d
                    (mult0 (p s0)
                      (log0
                        (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))))
              (sum_over_S0 (fun s0 ->
                rI.rI_base.opp (mult0 d (mult0 (p s0) (log0 z))))))
            (let hso1 =
               sum_opp rI sS sO (fun s0 ->
                 mult0 d
                   (mult0 (p s0)
                     (log0
                       (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))
             in
             internal_Id_rew_r
               (sum_over_S0 (fun s0 ->
                 rI.rI_base.opp
                   (mult0 d
                     (mult0 (p s0)
                       (log0
                         (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))))
               (rI.rI_base.opp
                 (sum_over_S0 (fun s0 ->
                   mult0 d
                     (mult0 (p s0)
                       (log0
                         (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))))
               (let hlin1 =
                  sO.sum_over_S_linear d (fun s0 ->
                    mult0 (p s0)
                      (log0
                        (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))
                in
                internal_Id_rew_r
                  (sum_over_S0 (fun s0 ->
                    mult0 d
                      (mult0 (p s0)
                        (log0
                          (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
                  (mult0 d
                    (sum_over_S0 (fun s0 ->
                      mult0 (p s0)
                        (log0
                          (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
                  (let hso2 =
                     sum_opp rI sS sO (fun s0 ->
                       mult0 d (mult0 (p s0) (log0 z)))
                   in
                   internal_Id_rew_r
                     (sum_over_S0 (fun s0 ->
                       rI.rI_base.opp (mult0 d (mult0 (p s0) (log0 z)))))
                     (rI.rI_base.opp
                       (sum_over_S0 (fun s0 ->
                         mult0 d (mult0 (p s0) (log0 z)))))
                     (let hlin2 =
                        sO.sum_over_S_linear d (fun s0 ->
                          mult0 (p s0) (log0 z))
                      in
                      internal_Id_rew_r
                        (sum_over_S0 (fun s0 ->
                          mult0 d (mult0 (p s0) (log0 z))))
                        (mult0 d
                          (sum_over_S0 (fun s0 -> mult0 (p s0) (log0 z))))
                        (let hlogZ =
                           let hsw =
                             sO.sum_over_S_ext (fun s0 ->
                               mult0 (p s0) (log0 z)) (fun s0 ->
                               mult0 (log0 z) (p s0)) (fun s0 ->
                               rI.rI_base.mult_comm (p s0) (log0 z))
                           in
                           internal_Id_rew_r
                             (sum_over_S0 (fun s0 -> mult0 (p s0) (log0 z)))
                             (sum_over_S0 (fun s0 -> mult0 (log0 z) (p s0)))
                             (let hl1 = sO.sum_over_S_linear (log0 z) p in
                              internal_Id_rew_r
                                (sum_over_S0 (fun s0 ->
                                  mult0 (log0 z) (p s0)))
                                (mult0 (log0 z) (sum_over_S0 p))
                                (internal_Id_rew_r (sum_over_S0 p) one0
                                  (let hm1 = rI.rI_base.mult_one (log0 z) in
                                   internal_Id_rew_r (mult0 (log0 z) one0)
                                     (log0 z) Id_refl hm1)
                                  hnorm)
                                hl1)
                             hsw
                         in
                         internal_Id_rew_r
                           (sum_over_S0 (fun s0 -> mult0 (p s0) (log0 z)))
                           (log0 z) Id_refl hlogZ)
                        hlin2)
                     hso2)
                  hlin1)
               hso1)
            hadd)
         hext
     in
     internal_Id_rew_r (sum_over_S0 (fun s0 -> mult0 (p s0) (base_loss s0)))
       (plus0
         (rI.rI_base.opp
           (mult0 d
             (sum_over_S0 (fun s0 ->
               mult0 (p s0)
                 (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))))
         (rI.rI_base.opp (mult0 d (log0 z))))
       (let hfb =
          let hfb0 =
            free_energy_boltzmann rI sS sO base_loss d d_pos z z_pos
              partition_condition
          in
          let hoppr = opp_mult_r rI d (log0 z) in
          id_trans
            (free_energy rI sS sO base_loss d
              (boltzmann_dist rI sS base_loss d d_pos z z_pos))
            (mult0 (rI.rI_base.opp d) (log0 z))
            (rI.rI_base.opp (mult0 d (log0 z))) hfb0 hoppr
        in
        internal_Id_rew_r
          (free_energy rI sS sO base_loss d
            (boltzmann_dist rI sS base_loss d d_pos z z_pos))
          (rI.rI_base.opp (mult0 d (log0 z)))
          (let hkl =
             let hpt2 = fun s0 ->
               let hd =
                 rI.rI_base.distrib (p s0) (log0 (p s0))
                   (rI.rI_base.opp
                     (log0
                       (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))
               in
               let ho =
                 opp_mult_l rI (p s0)
                   (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))
               in
               id_trans
                 (mult0 (p s0)
                   (plus0 (log0 (p s0))
                     (rI.rI_base.opp
                       (log0
                         (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
                 (plus0 (mult0 (p s0) (log0 (p s0)))
                   (mult0 (p s0)
                     (rI.rI_base.opp
                       (log0
                         (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
                 (plus0 (mult0 (p s0) (log0 (p s0)))
                   (rI.rI_base.opp
                     (mult0 (p s0)
                       (log0
                         (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
                 hd
                 (id_cong (fun x -> plus0 (mult0 (p s0) (log0 (p s0))) x)
                   (mult0 (p s0)
                     (rI.rI_base.opp
                       (log0
                         (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))
                   (rI.rI_base.opp
                     (mult0 (p s0)
                       (log0
                         (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))
                   ho)
             in
             let hext2 =
               sO.sum_over_S_ext (fun s0 ->
                 mult0 (p s0)
                   (minus rI.rI_base (log0 (p s0))
                     (log0
                       (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))
                 (fun s0 ->
                 plus0 (mult0 (p s0) (log0 (p s0)))
                   (rI.rI_base.opp
                     (mult0 (p s0)
                       (log0
                         (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
                 hpt2
             in
             internal_Id_rew_r
               (sum_over_S0 (fun s0 ->
                 mult0 (p s0)
                   (minus rI.rI_base (log0 (p s0))
                     (log0
                       (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
               (sum_over_S0 (fun s0 ->
                 plus0 (mult0 (p s0) (log0 (p s0)))
                   (rI.rI_base.opp
                     (mult0 (p s0)
                       (log0
                         (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))))
               (let hadd2 =
                  sO.sum_over_S_add (fun s0 -> mult0 (p s0) (log0 (p s0)))
                    (fun s0 ->
                    rI.rI_base.opp
                      (mult0 (p s0)
                        (log0
                          (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))
                in
                internal_Id_rew_r
                  (sum_over_S0 (fun s0 ->
                    plus0 (mult0 (p s0) (log0 (p s0)))
                      (rI.rI_base.opp
                        (mult0 (p s0)
                          (log0
                            (boltzmann_dist rI sS base_loss d d_pos z z_pos
                              s0))))))
                  (plus0 (sum_over_S0 (fun s0 -> mult0 (p s0) (log0 (p s0))))
                    (sum_over_S0 (fun s0 ->
                      rI.rI_base.opp
                        (mult0 (p s0)
                          (log0
                            (boltzmann_dist rI sS base_loss d d_pos z z_pos
                              s0))))))
                  (let hso3 =
                     sum_opp rI sS sO (fun s0 ->
                       mult0 (p s0)
                         (log0
                           (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))
                   in
                   internal_Id_rew_r
                     (sum_over_S0 (fun s0 ->
                       rI.rI_base.opp
                         (mult0 (p s0)
                           (log0
                             (boltzmann_dist rI sS base_loss d d_pos z z_pos
                               s0)))))
                     (rI.rI_base.opp
                       (sum_over_S0 (fun s0 ->
                         mult0 (p s0)
                           (log0
                             (boltzmann_dist rI sS base_loss d d_pos z z_pos
                               s0)))))
                     (let hdistD =
                        rI.rI_base.distrib d
                          (sum_over_S0 (fun s0 -> mult0 (p s0) (log0 (p s0))))
                          (rI.rI_base.opp
                            (sum_over_S0 (fun s0 ->
                              mult0 (p s0)
                                (log0
                                  (boltzmann_dist rI sS base_loss d d_pos z
                                    z_pos s0)))))
                      in
                      let hoppD =
                        opp_mult_l rI d
                          (sum_over_S0 (fun s0 ->
                            mult0 (p s0)
                              (log0
                                (boltzmann_dist rI sS base_loss d d_pos z
                                  z_pos s0))))
                      in
                      id_trans
                        (mult0 d
                          (plus0
                            (sum_over_S0 (fun s0 ->
                              mult0 (p s0) (log0 (p s0))))
                            (rI.rI_base.opp
                              (sum_over_S0 (fun s0 ->
                                mult0 (p s0)
                                  (log0
                                    (boltzmann_dist rI sS base_loss d d_pos z
                                      z_pos s0)))))))
                        (plus0
                          (mult0 d
                            (sum_over_S0 (fun s0 ->
                              mult0 (p s0) (log0 (p s0)))))
                          (mult0 d
                            (rI.rI_base.opp
                              (sum_over_S0 (fun s0 ->
                                mult0 (p s0)
                                  (log0
                                    (boltzmann_dist rI sS base_loss d d_pos z
                                      z_pos s0)))))))
                        (plus0
                          (mult0 d
                            (sum_over_S0 (fun s0 ->
                              mult0 (p s0) (log0 (p s0)))))
                          (rI.rI_base.opp
                            (mult0 d
                              (sum_over_S0 (fun s0 ->
                                mult0 (p s0)
                                  (log0
                                    (boltzmann_dist rI sS base_loss d d_pos z
                                      z_pos s0)))))))
                        hdistD
                        (id_cong (fun x ->
                          plus0
                            (mult0 d
                              (sum_over_S0 (fun s0 ->
                                mult0 (p s0) (log0 (p s0)))))
                            x)
                          (mult0 d
                            (rI.rI_base.opp
                              (sum_over_S0 (fun s0 ->
                                mult0 (p s0)
                                  (log0
                                    (boltzmann_dist rI sS base_loss d d_pos z
                                      z_pos s0))))))
                          (rI.rI_base.opp
                            (mult0 d
                              (sum_over_S0 (fun s0 ->
                                mult0 (p s0)
                                  (log0
                                    (boltzmann_dist rI sS base_loss d d_pos z
                                      z_pos s0))))))
                          hoppD))
                     hso3)
                  hadd2)
               hext2
           in
           let a =
             mult0 d
               (sum_over_S0 (fun s0 ->
                 mult0 (p s0)
                   (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))
           in
           let b =
             mult0 d (sum_over_S0 (fun s0 -> mult0 (p s0) (log0 (p s0))))
           in
           internal_Id_rew_r
             (mult0 d
               (sum_over_S0 (fun s0 ->
                 mult0 (p s0)
                   (minus rI.rI_base (log0 (p s0))
                     (log0
                       (boltzmann_dist rI sS base_loss d d_pos z z_pos s0))))))
             (plus0 b (rI.rI_base.opp a))
             (let h1 =
                id_sym
                  (rI.rI_base.plus (rI.rI_base.opp a)
                    (rI.rI_base.plus (rI.rI_base.opp (mult0 d (log0 z))) b))
                  (rI.rI_base.plus
                    (rI.rI_base.plus (rI.rI_base.opp a)
                      (rI.rI_base.opp (mult0 d (log0 z))))
                    b)
                  (rI.rI_base.plus_assoc (rI.rI_base.opp a)
                    (rI.rI_base.opp (mult0 d (log0 z))) b)
              in
              let h2 =
                id_cong (fun x -> plus0 (rI.rI_base.opp a) x)
                  (rI.rI_base.plus (rI.rI_base.opp (mult0 d (log0 z))) b)
                  (rI.rI_base.plus b (rI.rI_base.opp (mult0 d (log0 z))))
                  (rI.rI_base.plus_comm (rI.rI_base.opp (mult0 d (log0 z))) b)
              in
              let h3 =
                rI.rI_base.plus_assoc (rI.rI_base.opp a) b
                  (rI.rI_base.opp (mult0 d (log0 z)))
              in
              let h4 =
                id_cong (fun x ->
                  plus0 x (rI.rI_base.opp (mult0 d (log0 z))))
                  (rI.rI_base.plus (rI.rI_base.opp a) b)
                  (rI.rI_base.plus b (rI.rI_base.opp a))
                  (rI.rI_base.plus_comm (rI.rI_base.opp a) b)
              in
              let h5 =
                rI.rI_base.plus_comm (plus0 b (rI.rI_base.opp a))
                  (rI.rI_base.opp (mult0 d (log0 z)))
              in
              id_trans
                (plus0
                  (plus0 (rI.rI_base.opp a)
                    (rI.rI_base.opp (mult0 d (log0 z))))
                  b)
                (plus0 (rI.rI_base.opp a)
                  (plus0 (rI.rI_base.opp (mult0 d (log0 z))) b))
                (plus0 (rI.rI_base.opp (mult0 d (log0 z)))
                  (plus0 b (rI.rI_base.opp a)))
                h1
                (id_trans
                  (plus0 (rI.rI_base.opp a)
                    (plus0 (rI.rI_base.opp (mult0 d (log0 z))) b))
                  (plus0 (rI.rI_base.opp a)
                    (plus0 b (rI.rI_base.opp (mult0 d (log0 z)))))
                  (plus0 (rI.rI_base.opp (mult0 d (log0 z)))
                    (plus0 b (rI.rI_base.opp a)))
                  h2
                  (id_trans
                    (plus0 (rI.rI_base.opp a)
                      (plus0 b (rI.rI_base.opp (mult0 d (log0 z)))))
                    (plus0 (plus0 (rI.rI_base.opp a) b)
                      (rI.rI_base.opp (mult0 d (log0 z))))
                    (plus0 (rI.rI_base.opp (mult0 d (log0 z)))
                      (plus0 b (rI.rI_base.opp a)))
                    h3
                    (id_trans
                      (plus0 (plus0 (rI.rI_base.opp a) b)
                        (rI.rI_base.opp (mult0 d (log0 z))))
                      (plus0 (plus0 b (rI.rI_base.opp a))
                        (rI.rI_base.opp (mult0 d (log0 z))))
                      (plus0 (rI.rI_base.opp (mult0 d (log0 z)))
                        (plus0 b (rI.rI_base.opp a)))
                      h4 h5))))
             hkl)
          hfb)
       hse)
    hfe_p))

(** val free_energy_kl_diff :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    r -> lt -> r id -> (s -> r) -> normalized -> r id **)

let free_energy_kl_diff rI sS sO =
  let zero0 = rI.rI_base.zero in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  (fun base_loss d d_pos z z_pos partition_condition ->
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun p hnorm ->
  let hdecomp =
    free_energy_kl_decomp rI sS sO base_loss d d_pos z z_pos
      partition_condition p hnorm
  in
  internal_Id_rew_r (free_energy rI sS sO base_loss d p)
    (plus0
      (free_energy rI sS sO base_loss d
        (boltzmann_dist rI sS base_loss d d_pos z z_pos))
      (mult0 d
        (sum_over_S0 (fun s0 ->
          mult0 (p s0)
            (minus rI.rI_base (log0 (p s0))
              (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))))
    (let fB =
       free_energy rI sS sO base_loss d
         (boltzmann_dist rI sS base_loss d d_pos z z_pos)
     in
     let kL =
       mult0 d
         (sum_over_S0 (fun s0 ->
           mult0 (p s0)
             (minus rI.rI_base (log0 (p s0))
               (log0 (boltzmann_dist rI sS base_loss d d_pos z z_pos s0)))))
     in
     let h1 =
       id_sym (rI.rI_base.plus fB (rI.rI_base.plus kL (rI.rI_base.opp fB)))
         (rI.rI_base.plus (rI.rI_base.plus fB kL) (rI.rI_base.opp fB))
         (rI.rI_base.plus_assoc fB kL (rI.rI_base.opp fB))
     in
     let h2 =
       id_cong (fun x -> plus0 fB x) (rI.rI_base.plus kL (rI.rI_base.opp fB))
         (rI.rI_base.plus (rI.rI_base.opp fB) kL)
         (rI.rI_base.plus_comm kL (rI.rI_base.opp fB))
     in
     let h3 = rI.rI_base.plus_assoc fB (rI.rI_base.opp fB) kL in
     let h4 =
       id_cong (fun x -> plus0 x kL) (rI.rI_base.plus fB (rI.rI_base.opp fB))
         rI.rI_base.zero (rI.rI_base.plus_opp fB)
     in
     let h5 =
       id_trans (rI.rI_base.plus zero0 kL) (rI.rI_base.plus kL zero0) kL
         (rI.rI_base.plus_comm zero0 kL) (rI.rI_base.plus_zero kL)
     in
     id_trans (plus0 (plus0 fB kL) (rI.rI_base.opp fB))
       (plus0 fB (plus0 kL (rI.rI_base.opp fB))) kL h1
       (id_trans (plus0 fB (plus0 kL (rI.rI_base.opp fB)))
         (plus0 fB (plus0 (rI.rI_base.opp fB) kL)) kL h2
         (id_trans (plus0 fB (plus0 (rI.rI_base.opp fB) kL))
           (plus0 (plus0 fB (rI.rI_base.opp fB)) kL) kL h3
           (id_trans (plus0 (plus0 fB (rI.rI_base.opp fB)) kL)
             (plus0 zero0 kL) kL h4 h5))))
    hdecomp))

(** val relative_entropy :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> (s -> r) ->
    r **)

let relative_entropy rI _ sO =
  let mult0 = rI.rI_base.mult in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  (fun p q ->
  sum_over_S0 (fun s0 ->
    mult0 (p s0) (minus rI.rI_base (log0 (p s0)) (log0 (q s0)))))

(** val mult_minus_distr_r : realInterfaceEnhanced -> r -> r -> r -> r id **)

let mult_minus_distr_r rI =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  (fun a b c ->
  id_trans (rI.rI_base.mult (plus0 a (rI.rI_base.opp b)) c)
    (rI.rI_base.mult c (plus0 a (rI.rI_base.opp b)))
    (plus0 (mult0 a c) (rI.rI_base.opp (rI.rI_base.mult b c)))
    (rI.rI_base.mult_comm (plus0 a (rI.rI_base.opp b)) c)
    (id_trans (rI.rI_base.mult c (rI.rI_base.plus a (rI.rI_base.opp b)))
      (rI.rI_base.plus (rI.rI_base.mult c a)
        (rI.rI_base.mult c (rI.rI_base.opp b)))
      (plus0 (mult0 a c) (rI.rI_base.opp (rI.rI_base.mult b c)))
      (rI.rI_base.distrib c a (rI.rI_base.opp b))
      (id_trans (plus0 (rI.rI_base.mult c a) (mult0 c (rI.rI_base.opp b)))
        (plus0 (rI.rI_base.mult a c) (mult0 c (rI.rI_base.opp b)))
        (plus0 (mult0 a c) (rI.rI_base.opp (rI.rI_base.mult b c)))
        (id_cong (fun x -> plus0 x (mult0 c (rI.rI_base.opp b)))
          (rI.rI_base.mult c a) (rI.rI_base.mult a c)
          (rI.rI_base.mult_comm c a))
        (id_trans (plus0 (mult0 a c) (rI.rI_base.mult c (rI.rI_base.opp b)))
          (plus0 (mult0 a c) (rI.rI_base.mult (rI.rI_base.opp b) c))
          (plus0 (mult0 a c) (rI.rI_base.opp (rI.rI_base.mult b c)))
          (id_cong (fun x -> plus0 (mult0 a c) x)
            (rI.rI_base.mult c (rI.rI_base.opp b))
            (rI.rI_base.mult (rI.rI_base.opp b) c)
            (rI.rI_base.mult_comm c (rI.rI_base.opp b)))
          (id_cong (fun x -> plus0 (mult0 a c) x)
            (rI.rI_base.mult (rI.rI_base.opp b) c)
            (rI.rI_base.opp (rI.rI_base.mult b c)) (opp_mult_r rI b c))))))

(** val z_align :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r **)

let z_align rI _ sO =
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta beta_pos pi_ref ->
  sum_over_S0 (fun s0 ->
    mult0 (pi_ref s0)
      (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0))))))

(** val pi_star :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> lt -> s -> r **)

let pi_star rI sS sO =
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  (fun reward beta beta_pos pi_ref z_align_pos s0 ->
  mult0 (inv_pos0 (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos)
    (mult0 (pi_ref s0)
      (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0))))))

(** val pi_star_normalized :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> lt -> r id **)

let pi_star_normalized rI sS sO =
  let one0 = rI.rI_base.one in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta beta_pos pi_ref z_align_pos ->
  let h1 =
    sO.sum_over_S_ext (fun s0 ->
      pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0) (fun s0 ->
      mult0
        (inv_pos0 (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos)
        (mult0 (pi_ref s0)
          (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0))))))
      (fun _ -> Id_refl)
  in
  let h2 =
    sO.sum_over_S_linear
      (inv_pos0 (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos)
      (fun s0 ->
      mult0 (pi_ref s0)
        (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))))
  in
  let h3 =
    id_trans
      (rI.rI_base.mult
        (inv_pos0 (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos)
        (z_align rI sS sO reward beta beta_pos pi_ref))
      (rI.rI_base.mult (z_align rI sS sO reward beta beta_pos pi_ref)
        (inv_pos0 (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos))
      rI.rI_base.one
      (rI.rI_base.mult_comm
        (inv_pos0 (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos)
        (z_align rI sS sO reward beta beta_pos pi_ref))
      (rI.rI_base.inv_pos_correct
        (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos)
  in
  let h4 =
    let hdef = Id_refl in
    id_trans
      (mult0
        (inv_pos0 (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos)
        (z_align rI sS sO reward beta beta_pos pi_ref))
      (mult0
        (inv_pos0 (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos)
        (sum_over_S0 (fun s0 ->
          mult0 (pi_ref s0)
            (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))))))
      one0
      (id_cong (fun x ->
        mult0
          (inv_pos0 (z_align rI sS sO reward beta beta_pos pi_ref)
            z_align_pos)
          x)
        (z_align rI sS sO reward beta beta_pos pi_ref)
        (sum_over_S0 (fun s0 ->
          mult0 (pi_ref s0)
            (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0))))))
        (id_sym
          (sum_over_S0 (fun s0 ->
            mult0 (pi_ref s0)
              (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0))))))
          (z_align rI sS sO reward beta beta_pos pi_ref) hdef))
      h3
  in
  id_trans
    (sum_over_S0 (fun s0 ->
      pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0))
    (sum_over_S0 (fun s0 ->
      mult0
        (inv_pos0 (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos)
        (mult0 (pi_ref s0)
          (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))))))
    one0 h1
    (id_trans
      (sum_over_S0 (fun s0 ->
        mult0
          (inv_pos0 (z_align rI sS sO reward beta beta_pos pi_ref)
            z_align_pos)
          (mult0 (pi_ref s0)
            (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))))))
      (mult0
        (inv_pos0 (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos)
        (sum_over_S0 (fun s0 ->
          mult0 (pi_ref s0)
            (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))))))
      one0 h2 h4))

(** val align_energy :
    realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> (s -> r) -> s -> r **)

let align_energy rI _ =
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let log0 = rI.log in
  (fun reward beta pi_ref s0 ->
  minus rI.rI_base (opp0 (reward s0)) (mult0 beta (log0 (pi_ref s0))))

(** val align_objective :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s ->
    r) -> (s -> r) -> r **)

let align_objective rI sS sO =
  let opp0 = rI.rI_base.opp in
  (fun reward beta pi_ref pi ->
  opp0 (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta pi))

(** val align_energy_exp :
    realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> lt -> (s -> r) ->
    (s -> lt) -> s -> r id **)

let align_energy_exp rI sS =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let log0 = rI.log in
  let exp_neg0 = rI.rI_base.exp_neg in
  (fun reward beta beta_pos pi_ref pi_ref_pos s0 ->
  let h1 =
    let h1a =
      mult_minus_distr_l rI (inv_pos0 beta beta_pos) (opp0 (reward s0))
        (mult0 beta (log0 (pi_ref s0)))
    in
    let h1b = opp_mult_l rI (inv_pos0 beta beta_pos) (reward s0) in
    let h1c =
      let hc1 =
        rI.rI_base.mult_assoc (inv_pos0 beta beta_pos) beta (log0 (pi_ref s0))
      in
      let hc2 =
        id_cong (fun x -> mult0 x (log0 (pi_ref s0)))
          (rI.rI_base.mult (inv_pos0 beta beta_pos) beta) rI.rI_base.one
          (id_trans (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
            (rI.rI_base.mult beta (inv_pos0 beta beta_pos)) rI.rI_base.one
            (rI.rI_base.mult_comm (inv_pos0 beta beta_pos) beta)
            (rI.rI_base.inv_pos_correct beta beta_pos))
      in
      let hc3 =
        id_trans (rI.rI_base.mult one0 (log0 (pi_ref s0)))
          (rI.rI_base.mult (log0 (pi_ref s0)) one0) (log0 (pi_ref s0))
          (rI.rI_base.mult_comm one0 (log0 (pi_ref s0)))
          (rI.rI_base.mult_one (log0 (pi_ref s0)))
      in
      id_trans
        (mult0 (inv_pos0 beta beta_pos) (mult0 beta (log0 (pi_ref s0))))
        (mult0 (mult0 (inv_pos0 beta beta_pos) beta) (log0 (pi_ref s0)))
        (log0 (pi_ref s0)) hc1
        (id_trans
          (mult0 (mult0 (inv_pos0 beta beta_pos) beta) (log0 (pi_ref s0)))
          (mult0 one0 (log0 (pi_ref s0))) (log0 (pi_ref s0)) hc2 hc3)
    in
    let h1d =
      id_trans
        (minus rI.rI_base (mult0 (inv_pos0 beta beta_pos) (opp0 (reward s0)))
          (mult0 (inv_pos0 beta beta_pos) (mult0 beta (log0 (pi_ref s0)))))
        (minus rI.rI_base (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))
          (mult0 (inv_pos0 beta beta_pos) (mult0 beta (log0 (pi_ref s0)))))
        (minus rI.rI_base (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))
          (log0 (pi_ref s0)))
        (id_cong (fun x ->
          minus rI.rI_base x
            (mult0 (inv_pos0 beta beta_pos) (mult0 beta (log0 (pi_ref s0)))))
          (mult0 (inv_pos0 beta beta_pos) (opp0 (reward s0)))
          (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0))) h1b)
        (id_cong (fun x ->
          minus rI.rI_base
            (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0))) x)
          (mult0 (inv_pos0 beta beta_pos) (mult0 beta (log0 (pi_ref s0))))
          (log0 (pi_ref s0)) h1c)
    in
    id_trans
      (mult0 (inv_pos0 beta beta_pos)
        (minus rI.rI_base (opp0 (reward s0)) (mult0 beta (log0 (pi_ref s0)))))
      (minus rI.rI_base (mult0 (inv_pos0 beta beta_pos) (opp0 (reward s0)))
        (mult0 (inv_pos0 beta beta_pos) (mult0 beta (log0 (pi_ref s0)))))
      (minus rI.rI_base (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))
        (log0 (pi_ref s0)))
      h1a h1d
  in
  let h3b =
    let h3b2 =
      id_sym
        (rI.rI_base.opp
          (rI.rI_base.plus (mult0 (inv_pos0 beta beta_pos) (reward s0))
            (log0 (pi_ref s0))))
        (rI.rI_base.plus
          (rI.rI_base.opp (mult0 (inv_pos0 beta beta_pos) (reward s0)))
          (rI.rI_base.opp (log0 (pi_ref s0))))
        (opp_plus rI (mult0 (inv_pos0 beta beta_pos) (reward s0))
          (log0 (pi_ref s0)))
    in
    id_trans
      (mult0 (inv_pos0 beta beta_pos)
        (align_energy rI sS reward beta pi_ref s0))
      (minus rI.rI_base (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))
        (log0 (pi_ref s0)))
      (opp0
        (plus0 (mult0 (inv_pos0 beta beta_pos) (reward s0))
          (log0 (pi_ref s0))))
      h1 h3b2
  in
  let h4 =
    let h4a =
      id_cong exp_neg0
        (mult0 (inv_pos0 beta beta_pos)
          (align_energy rI sS reward beta pi_ref s0))
        (opp0
          (plus0 (mult0 (inv_pos0 beta beta_pos) (reward s0))
            (log0 (pi_ref s0))))
        h3b
    in
    let h4b =
      exp_neg_opp_plus rI (mult0 (inv_pos0 beta beta_pos) (reward s0))
        (log0 (pi_ref s0))
    in
    id_trans
      (exp_neg0
        (mult0 (inv_pos0 beta beta_pos)
          (align_energy rI sS reward beta pi_ref s0)))
      (exp_neg0
        (opp0
          (plus0 (mult0 (inv_pos0 beta beta_pos) (reward s0))
            (log0 (pi_ref s0)))))
      (mult0 (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0))))
        (exp_neg0 (opp0 (log0 (pi_ref s0)))))
      h4a h4b
  in
  let h5 = exp_neg_opp_log rI (pi_ref s0) (pi_ref_pos s0) in
  let h6 =
    let h6a =
      id_cong (fun x ->
        mult0 (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))) x)
        (exp_neg0 (opp0 (log0 (pi_ref s0)))) (pi_ref s0) h5
    in
    let h6b =
      rI.rI_base.mult_comm
        (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0))))
        (pi_ref s0)
    in
    id_trans
      (mult0 (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0))))
        (exp_neg0 (opp0 (log0 (pi_ref s0)))))
      (mult0 (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0))))
        (pi_ref s0))
      (mult0 (pi_ref s0)
        (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))))
      h6a h6b
  in
  id_trans
    (exp_neg0
      (mult0 (inv_pos0 beta beta_pos)
        (align_energy rI sS reward beta pi_ref s0)))
    (mult0 (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0))))
      (exp_neg0 (opp0 (log0 (pi_ref s0)))))
    (mult0 (pi_ref s0)
      (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))))
    h4 h6)

(** val align_partition_condition :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> (s -> lt) -> r id **)

let align_partition_condition rI sS sO =
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  (fun reward beta beta_pos pi_ref pi_ref_pos ->
  sO.sum_over_S_ext (fun s0 ->
    mult0 (pi_ref s0)
      (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))))
    (fun s0 ->
    exp_neg0
      (mult0 (inv_pos0 beta beta_pos)
        (align_energy rI sS reward beta pi_ref s0)))
    (fun s0 ->
    id_sym
      (exp_neg0
        (mult0 (inv_pos0 beta beta_pos)
          (align_energy rI sS reward beta pi_ref s0)))
      (mult0 (pi_ref s0)
        (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))))
      (align_energy_exp rI sS reward beta beta_pos pi_ref pi_ref_pos s0)))

(** val free_energy_ext :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s ->
    r) -> (s -> r) -> (s -> r) -> (s -> r id) -> r id **)

let free_energy_ext rI sS sO =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta pi_ref f g hfg ->
  let h1 =
    sO.sum_over_S_ext (fun s0 ->
      mult0 (f s0) (align_energy rI sS reward beta pi_ref s0)) (fun s0 ->
      mult0 (g s0) (align_energy rI sS reward beta pi_ref s0)) (fun s0 ->
      id_cong (fun x -> mult0 x (align_energy rI sS reward beta pi_ref s0))
        (f s0) (g s0) (hfg s0))
  in
  let h2 =
    sO.sum_over_S_ext (fun s0 -> mult0 (f s0) (log0 (f s0))) (fun s0 ->
      mult0 (g s0) (log0 (g s0))) (fun s0 ->
      let hc1 =
        id_cong (fun x -> mult0 x (log0 (f s0))) (f s0) (g s0) (hfg s0)
      in
      let hc2 = id_cong log0 (f s0) (g s0) (hfg s0) in
      let hc3 =
        id_cong (fun x -> mult0 (g s0) x) (log0 (f s0)) (log0 (g s0)) hc2
      in
      id_trans (mult0 (f s0) (log0 (f s0))) (mult0 (g s0) (log0 (f s0)))
        (mult0 (g s0) (log0 (g s0))) hc1 hc3)
  in
  id_trans
    (plus0
      (sum_over_S0 (fun s0 ->
        mult0 (f s0) (align_energy rI sS reward beta pi_ref s0)))
      (mult0 beta (sum_over_S0 (fun s0 -> mult0 (f s0) (log0 (f s0))))))
    (plus0
      (sum_over_S0 (fun s0 ->
        mult0 (g s0) (align_energy rI sS reward beta pi_ref s0)))
      (mult0 beta (sum_over_S0 (fun s0 -> mult0 (f s0) (log0 (f s0))))))
    (plus0
      (sum_over_S0 (fun s0 ->
        mult0 (g s0) (align_energy rI sS reward beta pi_ref s0)))
      (mult0 beta (sum_over_S0 (fun s0 -> mult0 (g s0) (log0 (g s0))))))
    (id_cong (fun x ->
      plus0 x
        (mult0 beta (sum_over_S0 (fun s0 -> mult0 (f s0) (log0 (f s0))))))
      (sum_over_S0 (fun s0 ->
        mult0 (f s0) (align_energy rI sS reward beta pi_ref s0)))
      (sum_over_S0 (fun s0 ->
        mult0 (g s0) (align_energy rI sS reward beta pi_ref s0)))
      h1)
    (id_cong (fun x ->
      plus0
        (sum_over_S0 (fun s0 ->
          mult0 (g s0) (align_energy rI sS reward beta pi_ref s0)))
        (mult0 beta x))
      (sum_over_S0 (fun s0 -> mult0 (f s0) (log0 (f s0))))
      (sum_over_S0 (fun s0 -> mult0 (g s0) (log0 (g s0)))) h2))

(** val align_boltzmann_is_pi_star :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> (s -> lt) -> lt -> s -> r id **)

let align_boltzmann_is_pi_star rI sS sO =
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  (fun reward beta beta_pos pi_ref pi_ref_pos z_align_pos s0 ->
  let hexp = align_energy_exp rI sS reward beta beta_pos pi_ref pi_ref_pos s0
  in
  id_cong (fun x ->
    mult0
      (inv_pos0 (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos) x)
    (exp_neg0
      (mult0 (inv_pos0 beta beta_pos)
        (align_energy rI sS reward beta pi_ref s0)))
    (mult0 (pi_ref s0)
      (exp_neg0 (opp0 (mult0 (inv_pos0 beta beta_pos) (reward s0)))))
    hexp)

(** val minus_minus_distr : realInterfaceEnhanced -> r -> r -> r -> r id **)

let minus_minus_distr rI =
  let plus0 = rI.rI_base.plus in
  let opp0 = rI.rI_base.opp in
  (fun a b c ->
  let h1 =
    id_sym (rI.rI_base.plus a (rI.rI_base.plus (opp0 b) (opp0 c)))
      (rI.rI_base.plus (rI.rI_base.plus a (opp0 b)) (opp0 c))
      (rI.rI_base.plus_assoc a (opp0 b) (opp0 c))
  in
  let h2 =
    id_cong (fun x -> plus0 a x)
      (rI.rI_base.plus (rI.rI_base.opp b) (rI.rI_base.opp c))
      (rI.rI_base.opp (rI.rI_base.plus b c))
      (id_sym (rI.rI_base.opp (rI.rI_base.plus b c))
        (rI.rI_base.plus (rI.rI_base.opp b) (rI.rI_base.opp c))
        (opp_plus rI b c))
  in
  id_trans (plus0 (plus0 a (opp0 b)) (opp0 c))
    (plus0 a (plus0 (opp0 b) (opp0 c))) (plus0 a (opp0 (plus0 b c))) h1 h2)

(** val minus_rearrange_four :
    realInterfaceEnhanced -> r -> r -> r -> r -> r id **)

let minus_rearrange_four rI =
  let plus0 = rI.rI_base.plus in
  let opp0 = rI.rI_base.opp in
  (fun a b c d ->
  let h1 =
    id_cong (fun x -> plus0 (plus0 a (opp0 b)) x)
      (rI.rI_base.opp (rI.rI_base.plus c (opp0 d))) (plus0 (opp0 c) d)
      (id_trans (rI.rI_base.opp (rI.rI_base.plus c (opp0 d)))
        (rI.rI_base.plus (rI.rI_base.opp c) (rI.rI_base.opp (opp0 d)))
        (plus0 (opp0 c) d) (opp_plus rI c (opp0 d))
        (id_cong (fun y -> plus0 (opp0 c) y)
          (rI.rI_base.opp (rI.rI_base.opp d)) d (double_neg rI d)))
  in
  let h2 = plus_swap_mid rI a (opp0 b) (opp0 c) d in
  let h3 =
    id_cong (fun x -> plus0 (plus0 a (opp0 c)) x) (plus0 (opp0 b) d)
      (rI.rI_base.opp (rI.rI_base.plus b (opp0 d)))
      (id_trans (plus0 (opp0 b) d)
        (plus0 (opp0 b) (rI.rI_base.opp (rI.rI_base.opp d)))
        (rI.rI_base.opp (rI.rI_base.plus b (opp0 d)))
        (id_cong (fun y -> plus0 (opp0 b) y) d
          (rI.rI_base.opp (rI.rI_base.opp d))
          (id_sym (rI.rI_base.opp (rI.rI_base.opp d)) d (double_neg rI d)))
        (id_sym (rI.rI_base.opp (rI.rI_base.plus b (opp0 d)))
          (rI.rI_base.plus (rI.rI_base.opp b) (rI.rI_base.opp (opp0 d)))
          (opp_plus rI b (opp0 d))))
  in
  id_trans (plus0 (plus0 a (opp0 b)) (opp0 (plus0 c (opp0 d))))
    (plus0 (plus0 a (opp0 b)) (plus0 (opp0 c) d))
    (plus0 (plus0 a (opp0 c)) (opp0 (plus0 b (opp0 d)))) h1
    (id_trans (plus0 (plus0 a (opp0 b)) (plus0 (opp0 c) d))
      (plus0 (plus0 a (opp0 c)) (plus0 (opp0 b) d))
      (plus0 (plus0 a (opp0 c)) (opp0 (plus0 b (opp0 d)))) h2 h3))

(** val relative_entropy_ext_r :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> (s -> r) ->
    (s -> r) -> (s -> r id) -> r id **)

let relative_entropy_ext_r rI _ sO =
  let mult0 = rI.rI_base.mult in
  let log0 = rI.log in
  (fun p q1 q2 hext ->
  sO.sum_over_S_ext (fun s0 ->
    rI.rI_base.mult (p s0) (minus rI.rI_base (rI.log (p s0)) (rI.log (q1 s0))))
    (fun s0 ->
    rI.rI_base.mult (p s0) (minus rI.rI_base (rI.log (p s0)) (rI.log (q2 s0))))
    (fun s0 ->
    let hlog = id_cong log0 (q1 s0) (q2 s0) (hext s0) in
    let hminus =
      id_cong2 (minus rI.rI_base) (log0 (p s0)) (log0 (p s0)) (log0 (q1 s0))
        (log0 (q2 s0)) Id_refl hlog
    in
    id_cong (fun x -> mult0 (p s0) x)
      (minus rI.rI_base (log0 (p s0)) (log0 (q1 s0)))
      (minus rI.rI_base (log0 (p s0)) (log0 (q2 s0))) hminus))

(** val minus_opp_opp : realInterfaceEnhanced -> r -> r -> r id **)

let minus_opp_opp rI =
  let plus0 = rI.rI_base.plus in
  let opp0 = rI.rI_base.opp in
  (fun a b ->
  let h1 =
    id_cong (fun x -> plus0 (opp0 a) x) (rI.rI_base.opp (rI.rI_base.opp b)) b
      (double_neg rI b)
  in
  let h2 = rI.rI_base.plus_comm (opp0 a) b in
  id_trans (plus0 (opp0 a) (opp0 (opp0 b))) (plus0 (opp0 a) b)
    (plus0 b (opp0 a)) h1 h2)

(** val rlhf_suboptimality_gap :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> (s -> lt) -> lt -> (s -> r) -> normalized -> positive_dist ->
    r id **)

let rlhf_suboptimality_gap rI sS sO =
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  (fun reward beta beta_pos pi_ref pi_ref_pos z_align_pos pi hnorm _ ->
  let h1 =
    minus_opp_opp rI
      (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta
        (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
      (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta pi)
  in
  let h2_raw =
    free_energy_kl_diff rI sS sO (align_energy rI sS reward beta pi_ref) beta
      beta_pos (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos
      (align_partition_condition rI sS sO reward beta beta_pos pi_ref
        pi_ref_pos)
      pi hnorm
  in
  let hfe_b =
    free_energy_ext rI sS sO reward beta pi_ref
      (boltzmann_dist rI sS (align_energy rI sS reward beta pi_ref) beta
        beta_pos (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos)
      (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
      (align_boltzmann_is_pi_star rI sS sO reward beta beta_pos pi_ref
        pi_ref_pos z_align_pos)
  in
  let hkl_b =
    relative_entropy_ext_r rI sS sO pi
      (boltzmann_dist rI sS (align_energy rI sS reward beta pi_ref) beta
        beta_pos (z_align rI sS sO reward beta beta_pos pi_ref) z_align_pos)
      (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
      (align_boltzmann_is_pi_star rI sS sO reward beta beta_pos pi_ref
        pi_ref_pos z_align_pos)
  in
  let h2 =
    let hlhs =
      id_cong2 (minus rI.rI_base)
        (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta pi)
        (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta pi)
        (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
        (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta
          (boltzmann_dist rI sS (align_energy rI sS reward beta pi_ref) beta
            beta_pos (z_align rI sS sO reward beta beta_pos pi_ref)
            z_align_pos))
        Id_refl
        (id_sym
          (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta
            (boltzmann_dist rI sS (align_energy rI sS reward beta pi_ref)
              beta beta_pos (z_align rI sS sO reward beta beta_pos pi_ref)
              z_align_pos))
          (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
          hfe_b)
    in
    id_trans
      (minus rI.rI_base
        (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta pi)
        (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))
      (minus rI.rI_base
        (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta pi)
        (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta
          (boltzmann_dist rI sS (align_energy rI sS reward beta pi_ref) beta
            beta_pos (z_align rI sS sO reward beta beta_pos pi_ref)
            z_align_pos)))
      (mult0 beta
        (relative_entropy rI sS sO pi
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))
      hlhs
      (id_trans
        (minus rI.rI_base
          (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta
            pi)
          (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta
            (boltzmann_dist rI sS (align_energy rI sS reward beta pi_ref)
              beta beta_pos (z_align rI sS sO reward beta beta_pos pi_ref)
              z_align_pos)))
        (mult0 beta
          (relative_entropy rI sS sO pi
            (boltzmann_dist rI sS (align_energy rI sS reward beta pi_ref)
              beta beta_pos (z_align rI sS sO reward beta beta_pos pi_ref)
              z_align_pos)))
        (mult0 beta
          (relative_entropy rI sS sO pi
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))
        h2_raw
        (id_cong (fun x -> mult0 beta x)
          (relative_entropy rI sS sO pi
            (boltzmann_dist rI sS (align_energy rI sS reward beta pi_ref)
              beta beta_pos (z_align rI sS sO reward beta beta_pos pi_ref)
              z_align_pos))
          (relative_entropy rI sS sO pi
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
          hkl_b))
  in
  id_trans
    (minus rI.rI_base
      (opp0
        (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))
      (opp0
        (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta pi)))
    (minus rI.rI_base
      (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta pi)
      (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta
        (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))
    (mult0 beta
      (relative_entropy rI sS sO pi
        (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))
    h1 h2)

(** val advantage_aug :
    realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> (s -> r) -> (s ->
    r) -> s -> r **)

let advantage_aug rI _ =
  let mult0 = rI.rI_base.mult in
  let log0 = rI.log in
  (fun reward beta pi_ref pi_t s0 ->
  minus rI.rI_base (reward s0)
    (mult0 beta (minus rI.rI_base (log0 (pi_t s0)) (log0 (pi_ref s0)))))

(** val z_rel :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r -> (s -> r) -> r **)

let z_rel rI sS sO =
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta beta_pos pi_ref eta pi_t ->
  sum_over_S0 (fun s0 ->
    mult0 (pi_t s0)
      (exp_neg0
        (opp0
          (mult0 (mult0 eta (inv_pos0 beta beta_pos))
            (advantage_aug rI sS reward beta pi_ref pi_t s0))))))

(** val z_rel_pos :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt)
    -> lt **)

let z_rel_pos rI sS _ =
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  (fun reward beta beta_pos pi_ref eta sum_over_S_pos pi_t hpos ->
  sum_over_S_pos (fun s0 ->
    mult0 (pi_t s0)
      (exp_neg0
        (opp0
          (mult0 (mult0 eta (inv_pos0 beta beta_pos))
            (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
    (fun s0 ->
    rI.mult_positive (pi_t s0)
      (exp_neg0
        (opp0
          (mult0 (mult0 eta (inv_pos0 beta beta_pos))
            (advantage_aug rI sS reward beta pi_ref pi_t s0))))
      (hpos s0)
      (rI.rI_base.exp_neg_pos
        (opp0
          (mult0 (mult0 eta (inv_pos0 beta beta_pos))
            (advantage_aug rI sS reward beta pi_ref pi_t s0))))))

(** val energy_t :
    realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> (s -> r) -> r ->
    (s -> r) -> s -> r **)

let energy_t rI sS =
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let log0 = rI.log in
  (fun reward beta pi_ref eta pi_t s0 ->
  minus rI.rI_base
    (opp0 (mult0 eta (advantage_aug rI sS reward beta pi_ref pi_t s0)))
    (mult0 beta (log0 (pi_t s0))))

(** val pi_next :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt)
    -> s -> r **)

let pi_next rI sS sO =
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  (fun reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos s0 ->
  mult0
    (inv_pos0 (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
      (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
        pi_t_pos))
    (mult0 (pi_t s0)
      (exp_neg0
        (opp0
          (mult0 (mult0 eta (inv_pos0 beta beta_pos))
            (advantage_aug rI sS reward beta pi_ref pi_t s0))))))

(** val boltzmann_factor_bridge :
    realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> lt -> (s -> r) ->
    r -> (s -> r) -> (s -> lt) -> s -> r id **)

let boltzmann_factor_bridge rI _ =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let log0 = rI.log in
  let exp_neg0 = rI.rI_base.exp_neg in
  (fun reward beta beta_pos pi_ref eta pi_t pi_t_pos s0 ->
  let a =
    minus rI.rI_base (reward s0)
      (mult0 beta (minus rI.rI_base (log0 (pi_t s0)) (log0 (pi_ref s0))))
  in
  let h1a =
    id_trans
      (rI.rI_base.mult (inv_pos0 beta beta_pos)
        (rI.rI_base.opp (mult0 eta a)))
      (rI.rI_base.opp
        (rI.rI_base.mult (inv_pos0 beta beta_pos) (mult0 eta a)))
      (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a))
      (opp_mult_l rI (inv_pos0 beta beta_pos) (mult0 eta a))
      (id_cong opp0
        (rI.rI_base.mult (inv_pos0 beta beta_pos) (rI.rI_base.mult eta a))
        (mult0 (rI.rI_base.mult eta (inv_pos0 beta beta_pos)) a)
        (id_trans
          (rI.rI_base.mult (inv_pos0 beta beta_pos) (rI.rI_base.mult eta a))
          (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 beta beta_pos) eta) a)
          (mult0 (rI.rI_base.mult eta (inv_pos0 beta beta_pos)) a)
          (rI.rI_base.mult_assoc (inv_pos0 beta beta_pos) eta a)
          (id_cong (fun x -> mult0 x a)
            (rI.rI_base.mult (inv_pos0 beta beta_pos) eta)
            (rI.rI_base.mult eta (inv_pos0 beta beta_pos))
            (rI.rI_base.mult_comm (inv_pos0 beta beta_pos) eta))))
  in
  let h1b =
    id_trans
      (rI.rI_base.mult (inv_pos0 beta beta_pos)
        (rI.rI_base.mult beta (log0 (pi_t s0))))
      (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
        (log0 (pi_t s0)))
      (log0 (pi_t s0))
      (rI.rI_base.mult_assoc (inv_pos0 beta beta_pos) beta (log0 (pi_t s0)))
      (id_trans
        (mult0 (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
          (log0 (pi_t s0)))
        (mult0 rI.rI_base.one (log0 (pi_t s0))) (log0 (pi_t s0))
        (id_cong (fun x -> mult0 x (log0 (pi_t s0)))
          (rI.rI_base.mult (inv_pos0 beta beta_pos) beta) rI.rI_base.one
          (id_trans (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
            (rI.rI_base.mult beta (inv_pos0 beta beta_pos)) rI.rI_base.one
            (rI.rI_base.mult_comm (inv_pos0 beta beta_pos) beta)
            (rI.rI_base.inv_pos_correct beta beta_pos)))
        (id_trans (rI.rI_base.mult one0 (log0 (pi_t s0)))
          (rI.rI_base.mult (log0 (pi_t s0)) one0) (log0 (pi_t s0))
          (rI.rI_base.mult_comm one0 (log0 (pi_t s0)))
          (rI.rI_base.mult_one (log0 (pi_t s0)))))
  in
  let h1 =
    id_trans
      (rI.rI_base.mult (inv_pos0 beta beta_pos)
        (minus rI.rI_base (opp0 (mult0 eta a)) (mult0 beta (log0 (pi_t s0)))))
      (minus rI.rI_base
        (rI.rI_base.mult (inv_pos0 beta beta_pos) (opp0 (mult0 eta a)))
        (rI.rI_base.mult (inv_pos0 beta beta_pos)
          (mult0 beta (log0 (pi_t s0)))))
      (minus rI.rI_base (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a))
        (log0 (pi_t s0)))
      (mult_minus_distr_l rI (inv_pos0 beta beta_pos) (opp0 (mult0 eta a))
        (mult0 beta (log0 (pi_t s0))))
      (id_trans
        (minus rI.rI_base
          (mult0 (inv_pos0 beta beta_pos) (opp0 (mult0 eta a)))
          (mult0 (inv_pos0 beta beta_pos) (mult0 beta (log0 (pi_t s0)))))
        (minus rI.rI_base
          (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a))
          (mult0 (inv_pos0 beta beta_pos) (mult0 beta (log0 (pi_t s0)))))
        (minus rI.rI_base
          (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a))
          (log0 (pi_t s0)))
        (id_cong (fun x ->
          minus rI.rI_base x
            (mult0 (inv_pos0 beta beta_pos) (mult0 beta (log0 (pi_t s0)))))
          (mult0 (inv_pos0 beta beta_pos) (opp0 (mult0 eta a)))
          (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)) h1a)
        (id_cong (fun x ->
          minus rI.rI_base
            (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)) x)
          (mult0 (inv_pos0 beta beta_pos) (mult0 beta (log0 (pi_t s0))))
          (log0 (pi_t s0)) h1b))
  in
  let h3 =
    id_trans
      (opp0
        (mult0 (inv_pos0 beta beta_pos)
          (minus rI.rI_base (opp0 (mult0 eta a))
            (mult0 beta (log0 (pi_t s0))))))
      (opp0
        (minus rI.rI_base
          (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a))
          (log0 (pi_t s0))))
      (plus0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a) (log0 (pi_t s0)))
      (id_cong opp0
        (mult0 (inv_pos0 beta beta_pos)
          (minus rI.rI_base (opp0 (mult0 eta a))
            (mult0 beta (log0 (pi_t s0)))))
        (minus rI.rI_base
          (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a))
          (log0 (pi_t s0)))
        h1)
      (id_trans
        (rI.rI_base.opp
          (minus rI.rI_base
            (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a))
            (log0 (pi_t s0))))
        (rI.rI_base.plus
          (rI.rI_base.opp
            (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)))
          (log0 (pi_t s0)))
        (plus0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)
          (log0 (pi_t s0)))
        (opp_minus rI (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a))
          (log0 (pi_t s0)))
        (id_cong (fun x -> plus0 x (log0 (pi_t s0)))
          (rI.rI_base.opp
            (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)))
          (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)
          (double_neg rI (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a))))
  in
  let h4 =
    let x =
      mult0 (inv_pos0 beta beta_pos)
        (minus rI.rI_base (opp0 (mult0 eta a)) (mult0 beta (log0 (pi_t s0))))
    in
    id_trans x (rI.rI_base.opp (rI.rI_base.opp x))
      (opp0
        (plus0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)
          (log0 (pi_t s0))))
      (id_sym (rI.rI_base.opp (rI.rI_base.opp x)) x (double_neg rI x))
      (id_sym
        (opp0
          (plus0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)
            (log0 (pi_t s0))))
        (opp0
          (opp0
            (mult0 (inv_pos0 beta beta_pos)
              (minus rI.rI_base (opp0 (mult0 eta a))
                (mult0 beta (log0 (pi_t s0)))))))
        (id_cong opp0
          (plus0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)
            (log0 (pi_t s0)))
          (opp0
            (mult0 (inv_pos0 beta beta_pos)
              (minus rI.rI_base (opp0 (mult0 eta a))
                (mult0 beta (log0 (pi_t s0))))))
          (id_sym
            (opp0
              (mult0 (inv_pos0 beta beta_pos)
                (minus rI.rI_base (opp0 (mult0 eta a))
                  (mult0 beta (log0 (pi_t s0))))))
            (plus0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)
              (log0 (pi_t s0)))
            h3)))
  in
  let h5 =
    id_trans
      (exp_neg0
        (mult0 (inv_pos0 beta beta_pos)
          (minus rI.rI_base (opp0 (mult0 eta a))
            (mult0 beta (log0 (pi_t s0))))))
      (exp_neg0
        (opp0
          (plus0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)
            (log0 (pi_t s0)))))
      (mult0 (exp_neg0 (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)))
        (exp_neg0 (opp0 (log0 (pi_t s0)))))
      (id_cong exp_neg0
        (mult0 (inv_pos0 beta beta_pos)
          (minus rI.rI_base (opp0 (mult0 eta a))
            (mult0 beta (log0 (pi_t s0)))))
        (opp0
          (plus0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)
            (log0 (pi_t s0))))
        h4)
      (exp_neg_opp_plus rI (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)
        (log0 (pi_t s0)))
  in
  let h6 = exp_neg_opp_log rI (pi_t s0) (pi_t_pos s0) in
  id_trans
    (exp_neg0
      (mult0 (inv_pos0 beta beta_pos)
        (minus rI.rI_base (opp0 (mult0 eta a)) (mult0 beta (log0 (pi_t s0))))))
    (mult0 (exp_neg0 (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)))
      (exp_neg0 (opp0 (log0 (pi_t s0)))))
    (mult0 (pi_t s0)
      (exp_neg0 (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a))))
    h5
    (id_trans
      (mult0 (exp_neg0 (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)))
        (exp_neg0 (opp0 (log0 (pi_t s0)))))
      (mult0 (exp_neg0 (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)))
        (pi_t s0))
      (mult0 (pi_t s0)
        (exp_neg0 (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a))))
      (id_cong (fun x ->
        mult0
          (exp_neg0 (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a))) x)
        (exp_neg0 (opp0 (log0 (pi_t s0)))) (pi_t s0) h6)
      (rI.rI_base.mult_comm
        (exp_neg0 (opp0 (mult0 (mult0 eta (inv_pos0 beta beta_pos)) a)))
        (pi_t s0))))

(** val z_rel_boltzmann_form :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r -> (s -> r) -> (s -> lt) -> r id **)

let z_rel_boltzmann_form rI sS sO =
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  (fun reward beta beta_pos pi_ref eta pi_t pi_t_pos ->
  sO.sum_over_S_ext (fun s0 ->
    mult0 (pi_t s0)
      (exp_neg0
        (opp0
          (mult0 (mult0 eta (inv_pos0 beta beta_pos))
            (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
    (fun s0 ->
    exp_neg0
      (mult0 (inv_pos0 beta beta_pos)
        (energy_t rI sS reward beta pi_ref eta pi_t s0)))
    (fun s0 ->
    id_sym
      (exp_neg0
        (mult0 (inv_pos0 beta beta_pos)
          (energy_t rI sS reward beta pi_ref eta pi_t s0)))
      (mult0 (pi_t s0)
        (exp_neg0
          (opp0
            (mult0 (mult0 eta (inv_pos0 beta beta_pos))
              (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
      (boltzmann_factor_bridge rI sS reward beta beta_pos pi_ref eta pi_t
        pi_t_pos s0)))

(** val free_energy_ext_t12 :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s ->
    r) -> (s -> r) -> (s -> r id) -> r id **)

let free_energy_ext_t12 rI _ sO =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let log0 = rI.log in
  (fun energy d p q hpq ->
  id_cong2 plus0 (sO.sum_over_S (fun s0 -> mult0 (p s0) (energy s0)))
    (sO.sum_over_S (fun s0 -> mult0 (q s0) (energy s0)))
    (mult0 d (sO.sum_over_S (fun s0 -> mult0 (p s0) (log0 (p s0)))))
    (mult0 d (sO.sum_over_S (fun s0 -> mult0 (q s0) (log0 (q s0)))))
    (sO.sum_over_S_ext (fun s0 -> mult0 (p s0) (energy s0)) (fun s0 ->
      mult0 (q s0) (energy s0)) (fun s0 ->
      id_cong (fun x -> mult0 x (energy s0)) (p s0) (q s0) (hpq s0)))
    (id_cong (fun x -> mult0 d x)
      (sO.sum_over_S (fun s0 -> mult0 (p s0) (log0 (p s0))))
      (sO.sum_over_S (fun s0 -> mult0 (q s0) (log0 (q s0))))
      (sO.sum_over_S_ext (fun s0 -> mult0 (p s0) (log0 (p s0))) (fun s0 ->
        mult0 (q s0) (log0 (q s0))) (fun s0 ->
        id_cong2 mult0 (p s0) (q s0) (log0 (p s0)) (log0 (q s0)) (hpq s0)
          (id_cong log0 (p s0) (q s0) (hpq s0))))))

(** val rel_free_energy_decomp :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt)
    -> r id -> r id **)

let rel_free_energy_decomp rI sS sO =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let log0 = rI.log in
  let exp_neg0 = rI.rI_base.exp_neg in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos pi_t_norm ->
  let hext = fun s0 ->
    id_cong (fun x ->
      mult0
        (inv_pos0 (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
          (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos))
        x)
      (rI.rI_base.exp_neg
        (rI.rI_base.mult (rI.rI_base.inv_pos beta beta_pos)
          (energy_t rI sS reward beta pi_ref eta pi_t s0)))
      (mult0 (pi_t s0)
        (exp_neg0
          (opp0
            (mult0 (mult0 eta (inv_pos0 beta beta_pos))
              (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
      (boltzmann_factor_bridge rI sS reward beta beta_pos pi_ref eta pi_t
        pi_t_pos s0)
  in
  let hdec =
    free_energy_kl_decomp rI sS sO
      (energy_t rI sS reward beta pi_ref eta pi_t) beta beta_pos
      (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
      (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
        pi_t_pos)
      (z_rel_boltzmann_form rI sS sO reward beta beta_pos pi_ref eta pi_t
        pi_t_pos)
      pi_t pi_t_norm
  in
  id_trans
    (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t) beta
      pi_t)
    (rI.rI_base.plus
      (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t) beta
        (boltzmann_dist rI sS (energy_t rI sS reward beta pi_ref eta pi_t)
          beta beta_pos (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
          (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos)))
      (rI.rI_base.mult beta
        (sO.sum_over_S (fun s0 ->
          rI.rI_base.mult (pi_t s0)
            (minus rI.rI_base (rI.log (pi_t s0))
              (rI.log
                (boltzmann_dist rI sS
                  (energy_t rI sS reward beta pi_ref eta pi_t) beta beta_pos
                  (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
                  (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta
                    sum_over_S_pos pi_t pi_t_pos)
                  s0)))))))
    (plus0
      (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t) beta
        (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
          pi_t_pos))
      (mult0 beta
        (sum_over_S0 (fun s0 ->
          mult0 (pi_t s0)
            (minus rI.rI_base (log0 (pi_t s0))
              (log0
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos s0)))))))
    hdec
    (id_cong2 plus0
      (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t) beta
        (boltzmann_dist rI sS (energy_t rI sS reward beta pi_ref eta pi_t)
          beta beta_pos (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
          (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos)))
      (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t) beta
        (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
          pi_t_pos))
      (mult0 beta
        (sO.sum_over_S (fun s0 ->
          mult0 (pi_t s0)
            (minus rI.rI_base (log0 (pi_t s0))
              (log0
                (boltzmann_dist rI sS
                  (energy_t rI sS reward beta pi_ref eta pi_t) beta beta_pos
                  (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
                  (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta
                    sum_over_S_pos pi_t pi_t_pos)
                  s0))))))
      (mult0 beta
        (sO.sum_over_S (fun s0 ->
          mult0 (pi_t s0)
            (minus rI.rI_base (log0 (pi_t s0))
              (log0
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos s0))))))
      (free_energy_ext_t12 rI sS sO
        (energy_t rI sS reward beta pi_ref eta pi_t) beta
        (boltzmann_dist rI sS (energy_t rI sS reward beta pi_ref eta pi_t)
          beta beta_pos (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
          (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos))
        (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
          pi_t_pos)
        hext)
      (id_cong (fun x -> mult0 beta x)
        (sO.sum_over_S (fun s0 ->
          mult0 (pi_t s0)
            (minus rI.rI_base (log0 (pi_t s0))
              (log0
                (boltzmann_dist rI sS
                  (energy_t rI sS reward beta pi_ref eta pi_t) beta beta_pos
                  (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
                  (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta
                    sum_over_S_pos pi_t pi_t_pos)
                  s0)))))
        (sO.sum_over_S (fun s0 ->
          mult0 (pi_t s0)
            (minus rI.rI_base (log0 (pi_t s0))
              (log0
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos s0)))))
        (sO.sum_over_S_ext (fun s0 ->
          mult0 (pi_t s0)
            (minus rI.rI_base (log0 (pi_t s0))
              (log0
                (boltzmann_dist rI sS
                  (energy_t rI sS reward beta pi_ref eta pi_t) beta beta_pos
                  (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
                  (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta
                    sum_over_S_pos pi_t pi_t_pos)
                  s0))))
          (fun s0 ->
          mult0 (pi_t s0)
            (minus rI.rI_base (log0 (pi_t s0))
              (log0
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos s0))))
          (fun s0 ->
          id_cong (fun y ->
            mult0 (pi_t s0) (minus rI.rI_base (log0 (pi_t s0)) y))
            (log0
              (boltzmann_dist rI sS
                (energy_t rI sS reward beta pi_ref eta pi_t) beta beta_pos
                (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
                (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)
                s0))
            (log0
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos s0))
            (id_cong log0
              (boltzmann_dist rI sS
                (energy_t rI sS reward beta pi_ref eta pi_t) beta beta_pos
                (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
                (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)
                s0)
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos s0)
              (hext s0)))))))

(** val reward_expand :
    realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> (s -> r) -> (s ->
    r) -> s -> r id **)

let reward_expand rI _ =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let log0 = rI.log in
  (fun reward beta pi_ref pi_t s0 ->
  let hc =
    minus_plus_cancel_gap rI (reward s0)
      (mult0 beta (minus rI.rI_base (log0 (pi_t s0)) (log0 (pi_ref s0))))
  in
  id_trans (reward s0)
    (plus0
      (minus rI.rI_base (reward s0)
        (mult0 beta (minus rI.rI_base (log0 (pi_t s0)) (log0 (pi_ref s0)))))
      (mult0 beta (minus rI.rI_base (log0 (pi_t s0)) (log0 (pi_ref s0)))))
    (plus0
      (minus rI.rI_base (reward s0)
        (mult0 beta (minus rI.rI_base (log0 (pi_t s0)) (log0 (pi_ref s0)))))
      (minus rI.rI_base (mult0 beta (log0 (pi_t s0)))
        (mult0 beta (log0 (pi_ref s0)))))
    (id_sym
      (plus0
        (minus rI.rI_base (reward s0)
          (mult0 beta (minus rI.rI_base (log0 (pi_t s0)) (log0 (pi_ref s0)))))
        (mult0 beta (minus rI.rI_base (log0 (pi_t s0)) (log0 (pi_ref s0)))))
      (reward s0) hc)
    (id_cong (fun y ->
      plus0
        (minus rI.rI_base (reward s0)
          (mult0 beta (minus rI.rI_base (log0 (pi_t s0)) (log0 (pi_ref s0)))))
        y)
      (rI.rI_base.mult beta
        (minus rI.rI_base (log0 (pi_t s0)) (log0 (pi_ref s0))))
      (minus rI.rI_base (rI.rI_base.mult beta (log0 (pi_t s0)))
        (rI.rI_base.mult beta (log0 (pi_ref s0))))
      (mult_minus_distr_l rI beta (log0 (pi_t s0)) (log0 (pi_ref s0)))))

(** val sum_over_S_opp_t12 :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r id **)

let sum_over_S_opp_t12 rI _ sO =
  let one0 = rI.rI_base.one in
  let opp0 = rI.rI_base.opp in
  let sum_over_S0 = sO.sum_over_S in
  (fun f ->
  id_trans (sO.sum_over_S (fun s0 -> opp0 (f s0)))
    (sO.sum_over_S (fun s0 -> rI.rI_base.mult (rI.rI_base.opp one0) (f s0)))
    (opp0 (sum_over_S0 f))
    (sO.sum_over_S_ext (fun s0 -> opp0 (f s0)) (fun s0 ->
      rI.rI_base.mult (rI.rI_base.opp one0) (f s0)) (fun s0 ->
      id_sym (rI.rI_base.mult (rI.rI_base.opp one0) (f s0)) (opp0 (f s0))
        (id_trans (rI.rI_base.mult (rI.rI_base.opp one0) (f s0))
          (rI.rI_base.opp (rI.rI_base.mult one0 (f s0))) (opp0 (f s0))
          (opp_mult_r rI one0 (f s0))
          (id_cong opp0 (rI.rI_base.mult one0 (f s0)) (f s0)
            (id_trans (rI.rI_base.mult one0 (f s0))
              (rI.rI_base.mult (f s0) one0) (f s0)
              (rI.rI_base.mult_comm one0 (f s0)) (rI.rI_base.mult_one (f s0)))))))
    (id_trans (sO.sum_over_S (fun s0 -> rI.rI_base.mult (opp0 one0) (f s0)))
      (rI.rI_base.mult (opp0 one0) (sO.sum_over_S f)) (opp0 (sum_over_S0 f))
      (sO.sum_over_S_linear (opp0 one0) f)
      (id_trans (rI.rI_base.mult (rI.rI_base.opp one0) (sum_over_S0 f))
        (rI.rI_base.opp (rI.rI_base.mult one0 (sum_over_S0 f)))
        (opp0 (sum_over_S0 f)) (opp_mult_r rI one0 (sum_over_S0 f))
        (id_cong opp0 (rI.rI_base.mult one0 (sum_over_S0 f)) (sum_over_S0 f)
          (id_trans (rI.rI_base.mult one0 (sum_over_S0 f))
            (rI.rI_base.mult (sum_over_S0 f) one0) (sum_over_S0 f)
            (rI.rI_base.mult_comm one0 (sum_over_S0 f))
            (rI.rI_base.mult_one (sum_over_S0 f)))))))

(** val sum_ptimes_opp_scal_t12 :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s ->
    r) -> r id **)

let sum_ptimes_opp_scal_t12 rI sS sO =
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let sum_over_S0 = sO.sum_over_S in
  (fun pi_t a f ->
  let lf = fun s0 -> mult0 (pi_t s0) (opp0 (mult0 a (f s0))) in
  let rf = fun s0 -> opp0 (mult0 a (mult0 (pi_t s0) (f s0))) in
  let hpt = fun s0 ->
    let hm =
      id_trans (rI.rI_base.mult (pi_t s0) (rI.rI_base.mult a (f s0)))
        (rI.rI_base.mult (rI.rI_base.mult (pi_t s0) a) (f s0))
        (rI.rI_base.mult a (rI.rI_base.mult (pi_t s0) (f s0)))
        (rI.rI_base.mult_assoc (pi_t s0) a (f s0))
        (id_trans (mult0 (rI.rI_base.mult (pi_t s0) a) (f s0))
          (mult0 (rI.rI_base.mult a (pi_t s0)) (f s0))
          (rI.rI_base.mult a (rI.rI_base.mult (pi_t s0) (f s0)))
          (id_cong (fun x -> mult0 x (f s0)) (rI.rI_base.mult (pi_t s0) a)
            (rI.rI_base.mult a (pi_t s0)) (rI.rI_base.mult_comm (pi_t s0) a))
          (id_sym (rI.rI_base.mult a (rI.rI_base.mult (pi_t s0) (f s0)))
            (rI.rI_base.mult (rI.rI_base.mult a (pi_t s0)) (f s0))
            (rI.rI_base.mult_assoc a (pi_t s0) (f s0))))
    in
    id_trans (rI.rI_base.mult (pi_t s0) (rI.rI_base.opp (mult0 a (f s0))))
      (rI.rI_base.opp (rI.rI_base.mult (pi_t s0) (mult0 a (f s0))))
      (opp0 (mult0 a (mult0 (pi_t s0) (f s0))))
      (opp_mult_l rI (pi_t s0) (mult0 a (f s0)))
      (id_cong opp0 (mult0 (pi_t s0) (mult0 a (f s0)))
        (mult0 a (mult0 (pi_t s0) (f s0))) hm)
  in
  let hsumR =
    id_trans
      (sum_over_S0 (fun s0 -> opp0 (mult0 a (mult0 (pi_t s0) (f s0)))))
      (opp0 (sum_over_S0 (fun s0 -> mult0 a (mult0 (pi_t s0) (f s0)))))
      (opp0
        (rI.rI_base.mult a (sO.sum_over_S (fun s0 -> mult0 (pi_t s0) (f s0)))))
      (sum_over_S_opp_t12 rI sS sO (fun s0 ->
        mult0 a (mult0 (pi_t s0) (f s0))))
      (id_cong opp0
        (sO.sum_over_S (fun s0 -> rI.rI_base.mult a (mult0 (pi_t s0) (f s0))))
        (rI.rI_base.mult a (sO.sum_over_S (fun s0 -> mult0 (pi_t s0) (f s0))))
        (sO.sum_over_S_linear a (fun s0 -> mult0 (pi_t s0) (f s0))))
  in
  id_trans (sO.sum_over_S lf) (sO.sum_over_S rf)
    (opp0 (mult0 a (sum_over_S0 (fun s0 -> mult0 (pi_t s0) (f s0)))))
    (sO.sum_over_S_ext lf rf hpt) hsumR)

(** val sum_ptimes_scal_t12 :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s ->
    r) -> r id **)

let sum_ptimes_scal_t12 rI _ sO =
  let mult0 = rI.rI_base.mult in
  let sum_over_S0 = sO.sum_over_S in
  (fun pi_t a f ->
  id_trans
    (sO.sum_over_S (fun s0 ->
      rI.rI_base.mult (pi_t s0) (rI.rI_base.mult a (f s0))))
    (sO.sum_over_S (fun s0 ->
      rI.rI_base.mult a (rI.rI_base.mult (pi_t s0) (f s0))))
    (mult0 a (sum_over_S0 (fun s0 -> mult0 (pi_t s0) (f s0))))
    (sO.sum_over_S_ext (fun s0 ->
      rI.rI_base.mult (pi_t s0) (rI.rI_base.mult a (f s0))) (fun s0 ->
      rI.rI_base.mult a (rI.rI_base.mult (pi_t s0) (f s0))) (fun s0 ->
      id_trans (rI.rI_base.mult (pi_t s0) (rI.rI_base.mult a (f s0)))
        (rI.rI_base.mult (rI.rI_base.mult (pi_t s0) a) (f s0))
        (rI.rI_base.mult a (rI.rI_base.mult (pi_t s0) (f s0)))
        (rI.rI_base.mult_assoc (pi_t s0) a (f s0))
        (id_trans (mult0 (rI.rI_base.mult (pi_t s0) a) (f s0))
          (mult0 (rI.rI_base.mult a (pi_t s0)) (f s0))
          (rI.rI_base.mult a (rI.rI_base.mult (pi_t s0) (f s0)))
          (id_cong (fun x -> mult0 x (f s0)) (rI.rI_base.mult (pi_t s0) a)
            (rI.rI_base.mult a (pi_t s0)) (rI.rI_base.mult_comm (pi_t s0) a))
          (id_sym (rI.rI_base.mult a (rI.rI_base.mult (pi_t s0) (f s0)))
            (rI.rI_base.mult (rI.rI_base.mult a (pi_t s0)) (f s0))
            (rI.rI_base.mult_assoc a (pi_t s0) (f s0))))))
    (sO.sum_over_S_linear a (fun s0 -> mult0 (pi_t s0) (f s0))))

(** val f_t_simpl_t :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s ->
    r) -> r -> (s -> r) -> r id **)

let f_t_simpl_t rI sS sO =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta pi_ref eta pi_t ->
  let a = advantage_aug rI sS reward beta pi_ref pi_t in
  let s1t = sum_over_S0 (fun s0 -> mult0 (pi_t s0) (log0 (pi_t s0))) in
  let h1 = sum_ptimes_opp_scal_t12 rI sS sO pi_t eta a in
  let h2 =
    id_trans
      (sO.sum_over_S (fun s0 ->
        rI.rI_base.mult (pi_t s0) (rI.rI_base.mult beta (log0 (pi_t s0)))))
      (sO.sum_over_S (fun s0 ->
        rI.rI_base.mult beta (rI.rI_base.mult (pi_t s0) (log0 (pi_t s0)))))
      (mult0 beta (sum_over_S0 (fun s0 -> mult0 (pi_t s0) (log0 (pi_t s0)))))
      (sO.sum_over_S_ext (fun s0 ->
        rI.rI_base.mult (pi_t s0) (rI.rI_base.mult beta (log0 (pi_t s0))))
        (fun s0 ->
        rI.rI_base.mult beta (rI.rI_base.mult (pi_t s0) (log0 (pi_t s0))))
        (fun s0 ->
        id_trans
          (rI.rI_base.mult (pi_t s0) (rI.rI_base.mult beta (log0 (pi_t s0))))
          (rI.rI_base.mult (rI.rI_base.mult (pi_t s0) beta) (log0 (pi_t s0)))
          (rI.rI_base.mult beta (rI.rI_base.mult (pi_t s0) (log0 (pi_t s0))))
          (rI.rI_base.mult_assoc (pi_t s0) beta (log0 (pi_t s0)))
          (id_trans (mult0 (rI.rI_base.mult (pi_t s0) beta) (log0 (pi_t s0)))
            (mult0 (rI.rI_base.mult beta (pi_t s0)) (log0 (pi_t s0)))
            (rI.rI_base.mult beta
              (rI.rI_base.mult (pi_t s0) (log0 (pi_t s0))))
            (id_cong (fun x -> mult0 x (log0 (pi_t s0)))
              (rI.rI_base.mult (pi_t s0) beta)
              (rI.rI_base.mult beta (pi_t s0))
              (rI.rI_base.mult_comm (pi_t s0) beta))
            (id_sym
              (rI.rI_base.mult beta
                (rI.rI_base.mult (pi_t s0) (log0 (pi_t s0))))
              (rI.rI_base.mult (rI.rI_base.mult beta (pi_t s0))
                (log0 (pi_t s0)))
              (rI.rI_base.mult_assoc beta (pi_t s0) (log0 (pi_t s0)))))))
      (sO.sum_over_S_linear beta (fun s0 -> mult0 (pi_t s0) (log0 (pi_t s0))))
  in
  let hsum =
    id_trans
      (sO.sum_over_S (fun s0 ->
        rI.rI_base.mult (pi_t s0)
          (minus rI.rI_base (opp0 (mult0 eta (a s0)))
            (mult0 beta (log0 (pi_t s0))))))
      (sO.sum_over_S (fun s0 ->
        minus rI.rI_base
          (rI.rI_base.mult (pi_t s0) (opp0 (mult0 eta (a s0))))
          (rI.rI_base.mult (pi_t s0) (mult0 beta (log0 (pi_t s0))))))
      (minus rI.rI_base
        (opp0 (mult0 eta (sum_over_S0 (fun s0 -> mult0 (pi_t s0) (a s0)))))
        (mult0 beta s1t))
      (sO.sum_over_S_ext (fun s0 ->
        rI.rI_base.mult (pi_t s0)
          (minus rI.rI_base (opp0 (mult0 eta (a s0)))
            (mult0 beta (log0 (pi_t s0)))))
        (fun s0 ->
        minus rI.rI_base
          (rI.rI_base.mult (pi_t s0) (opp0 (mult0 eta (a s0))))
          (rI.rI_base.mult (pi_t s0) (mult0 beta (log0 (pi_t s0)))))
        (fun s0 ->
        mult_minus_distr_l rI (pi_t s0) (opp0 (mult0 eta (a s0)))
          (mult0 beta (log0 (pi_t s0)))))
      (id_trans
        (sO.sum_over_S (fun s0 ->
          minus rI.rI_base (mult0 (pi_t s0) (opp0 (mult0 eta (a s0))))
            (mult0 (pi_t s0) (mult0 beta (log0 (pi_t s0))))))
        (minus rI.rI_base
          (sO.sum_over_S (fun s0 ->
            mult0 (pi_t s0) (opp0 (mult0 eta (a s0)))))
          (sO.sum_over_S (fun s0 ->
            mult0 (pi_t s0) (mult0 beta (log0 (pi_t s0))))))
        (minus rI.rI_base
          (opp0 (mult0 eta (sum_over_S0 (fun s0 -> mult0 (pi_t s0) (a s0)))))
          (mult0 beta s1t))
        (sum_over_S_minus rI sS sO (fun s0 ->
          mult0 (pi_t s0) (opp0 (mult0 eta (a s0)))) (fun s0 ->
          mult0 (pi_t s0) (mult0 beta (log0 (pi_t s0)))))
        (id_cong2 (minus rI.rI_base)
          (sum_over_S0 (fun s0 -> mult0 (pi_t s0) (opp0 (mult0 eta (a s0)))))
          (opp0 (mult0 eta (sum_over_S0 (fun s0 -> mult0 (pi_t s0) (a s0)))))
          (sum_over_S0 (fun s0 ->
            mult0 (pi_t s0) (mult0 beta (log0 (pi_t s0)))))
          (mult0 beta s1t) h1 h2))
  in
  let sX = opp0 (mult0 eta (sum_over_S0 (fun s0 -> mult0 (pi_t s0) (a s0))))
  in
  id_trans
    (plus0
      (sum_over_S0 (fun s0 ->
        mult0 (pi_t s0)
          (minus rI.rI_base (opp0 (mult0 eta (a s0)))
            (mult0 beta (log0 (pi_t s0))))))
      (mult0 beta s1t))
    (plus0
      (minus rI.rI_base
        (opp0 (mult0 eta (sum_over_S0 (fun s0 -> mult0 (pi_t s0) (a s0)))))
        (mult0 beta s1t))
      (mult0 beta s1t))
    sX
    (id_cong2 plus0
      (sum_over_S0 (fun s0 ->
        mult0 (pi_t s0)
          (minus rI.rI_base (opp0 (mult0 eta (a s0)))
            (mult0 beta (log0 (pi_t s0))))))
      (minus rI.rI_base
        (opp0 (mult0 eta (sum_over_S0 (fun s0 -> mult0 (pi_t s0) (a s0)))))
        (mult0 beta s1t))
      (mult0 beta s1t) (mult0 beta s1t) hsum Id_refl)
    (minus_plus_cancel_gap rI sX (mult0 beta s1t)))

(** val f_t_simpl_next_kl :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt)
    -> r id **)

let f_t_simpl_next_kl rI sS sO =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos ->
  let np =
    pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
      pi_t_pos
  in
  let a = advantage_aug rI sS reward beta pi_ref pi_t in
  let s1n = sum_over_S0 (fun s0 -> mult0 (np s0) (log0 (pi_t s0))) in
  let sAn = sum_over_S0 (fun s0 -> mult0 (np s0) (a s0)) in
  let s2n = sum_over_S0 (fun s0 -> mult0 (np s0) (log0 (np s0))) in
  let h1 =
    id_trans
      (sO.sum_over_S (fun s0 ->
        rI.rI_base.mult (np s0)
          (minus rI.rI_base (opp0 (mult0 eta (a s0)))
            (mult0 beta (log0 (pi_t s0))))))
      (sO.sum_over_S (fun s0 ->
        minus rI.rI_base (rI.rI_base.mult (np s0) (opp0 (mult0 eta (a s0))))
          (rI.rI_base.mult (np s0) (mult0 beta (log0 (pi_t s0))))))
      (minus rI.rI_base (opp0 (mult0 eta sAn)) (mult0 beta s1n))
      (sO.sum_over_S_ext (fun s0 ->
        rI.rI_base.mult (np s0)
          (minus rI.rI_base (opp0 (mult0 eta (a s0)))
            (mult0 beta (log0 (pi_t s0)))))
        (fun s0 ->
        minus rI.rI_base (rI.rI_base.mult (np s0) (opp0 (mult0 eta (a s0))))
          (rI.rI_base.mult (np s0) (mult0 beta (log0 (pi_t s0)))))
        (fun s0 ->
        mult_minus_distr_l rI (np s0) (opp0 (mult0 eta (a s0)))
          (mult0 beta (log0 (pi_t s0)))))
      (id_trans
        (sO.sum_over_S (fun s0 ->
          minus rI.rI_base (mult0 (np s0) (opp0 (mult0 eta (a s0))))
            (mult0 (np s0) (mult0 beta (log0 (pi_t s0))))))
        (minus rI.rI_base
          (sO.sum_over_S (fun s0 -> mult0 (np s0) (opp0 (mult0 eta (a s0)))))
          (sO.sum_over_S (fun s0 ->
            mult0 (np s0) (mult0 beta (log0 (pi_t s0))))))
        (minus rI.rI_base (opp0 (mult0 eta sAn)) (mult0 beta s1n))
        (sum_over_S_minus rI sS sO (fun s0 ->
          mult0 (np s0) (opp0 (mult0 eta (a s0)))) (fun s0 ->
          mult0 (np s0) (mult0 beta (log0 (pi_t s0)))))
        (id_cong2 (minus rI.rI_base)
          (sum_over_S0 (fun s0 -> mult0 (np s0) (opp0 (mult0 eta (a s0)))))
          (opp0 (mult0 eta (sum_over_S0 (fun s0 -> mult0 (np s0) (a s0)))))
          (sum_over_S0 (fun s0 ->
            mult0 (np s0) (mult0 beta (log0 (pi_t s0)))))
          (mult0 beta
            (sum_over_S0 (fun s0 -> mult0 (np s0) (log0 (pi_t s0)))))
          (sum_ptimes_opp_scal_t12 rI sS sO np eta a)
          (sum_ptimes_scal_t12 rI sS sO np beta (fun s0 -> log0 (pi_t s0)))))
  in
  let hkl =
    id_trans
      (minus rI.rI_base
        (sO.sum_over_S (fun s0 -> mult0 (np s0) (log0 (np s0))))
        (sO.sum_over_S (fun s0 -> mult0 (np s0) (log0 (pi_t s0)))))
      (sO.sum_over_S (fun s0 ->
        minus rI.rI_base (mult0 (np s0) (log0 (np s0)))
          (mult0 (np s0) (log0 (pi_t s0)))))
      (sum_over_S0 (fun s0 ->
        mult0 (np s0) (minus rI.rI_base (log0 (np s0)) (log0 (pi_t s0)))))
      (id_sym
        (sO.sum_over_S (fun s0 ->
          minus rI.rI_base (mult0 (np s0) (log0 (np s0)))
            (mult0 (np s0) (log0 (pi_t s0)))))
        (minus rI.rI_base
          (sO.sum_over_S (fun s0 -> mult0 (np s0) (log0 (np s0))))
          (sO.sum_over_S (fun s0 -> mult0 (np s0) (log0 (pi_t s0)))))
        (sum_over_S_minus rI sS sO (fun s0 -> mult0 (np s0) (log0 (np s0)))
          (fun s0 -> mult0 (np s0) (log0 (pi_t s0)))))
      (sO.sum_over_S_ext (fun s0 ->
        minus rI.rI_base (rI.rI_base.mult (np s0) (log0 (np s0)))
          (rI.rI_base.mult (np s0) (log0 (pi_t s0))))
        (fun s0 ->
        rI.rI_base.mult (np s0)
          (minus rI.rI_base (log0 (np s0)) (log0 (pi_t s0))))
        (fun s0 ->
        id_sym
          (rI.rI_base.mult (np s0)
            (minus rI.rI_base (log0 (np s0)) (log0 (pi_t s0))))
          (minus rI.rI_base (rI.rI_base.mult (np s0) (log0 (np s0)))
            (rI.rI_base.mult (np s0) (log0 (pi_t s0))))
          (mult_minus_distr_l rI (np s0) (log0 (np s0)) (log0 (pi_t s0)))))
  in
  id_trans
    (plus0
      (sum_over_S0 (fun s0 ->
        mult0 (np s0)
          (minus rI.rI_base (opp0 (mult0 eta (a s0)))
            (mult0 beta (log0 (pi_t s0))))))
      (mult0 beta s2n))
    (plus0 (minus rI.rI_base (opp0 (mult0 eta sAn)) (mult0 beta s1n))
      (mult0 beta s2n))
    (plus0
      (opp0
        (mult0 eta
          (sum_over_S0 (fun s0 ->
            mult0 (np s0)
              (minus rI.rI_base (reward s0)
                (mult0 beta
                  (minus rI.rI_base (log0 (pi_t s0)) (log0 (pi_ref s0)))))))))
      (mult0 beta
        (sO.sum_over_S (fun s0 ->
          rI.rI_base.mult (np s0)
            (minus rI.rI_base (rI.log (np s0)) (rI.log (pi_t s0)))))))
    (id_cong (fun x -> plus0 x (mult0 beta s2n))
      (sum_over_S0 (fun s0 ->
        mult0 (np s0)
          (minus rI.rI_base (opp0 (mult0 eta (a s0)))
            (mult0 beta (log0 (pi_t s0))))))
      (minus rI.rI_base (opp0 (mult0 eta sAn)) (mult0 beta s1n)) h1)
    (let hm =
       id_trans
         (plus0 (rI.rI_base.opp (rI.rI_base.mult beta s1n)) (mult0 beta s2n))
         (plus0 (rI.rI_base.mult beta (rI.rI_base.opp s1n)) (mult0 beta s2n))
         (mult0 beta (rI.rI_base.plus s2n (rI.rI_base.opp s1n)))
         (id_cong2 plus0 (rI.rI_base.opp (rI.rI_base.mult beta s1n))
           (rI.rI_base.mult beta (rI.rI_base.opp s1n)) (mult0 beta s2n)
           (mult0 beta s2n)
           (id_sym (rI.rI_base.mult beta (rI.rI_base.opp s1n))
             (rI.rI_base.opp (rI.rI_base.mult beta s1n))
             (opp_mult_l rI beta s1n))
           Id_refl)
         (id_trans (rI.rI_base.plus (mult0 beta (opp0 s1n)) (mult0 beta s2n))
           (rI.rI_base.plus (mult0 beta s2n) (mult0 beta (opp0 s1n)))
           (rI.rI_base.mult beta (rI.rI_base.plus s2n (opp0 s1n)))
           (rI.rI_base.plus_comm (mult0 beta (opp0 s1n)) (mult0 beta s2n))
           (id_sym (rI.rI_base.mult beta (rI.rI_base.plus s2n (opp0 s1n)))
             (rI.rI_base.plus (rI.rI_base.mult beta s2n)
               (rI.rI_base.mult beta (opp0 s1n)))
             (rI.rI_base.distrib beta s2n (opp0 s1n))))
     in
     id_trans
       (rI.rI_base.plus
         (rI.rI_base.plus (opp0 (mult0 eta sAn)) (opp0 (mult0 beta s1n)))
         (mult0 beta s2n))
       (rI.rI_base.plus (opp0 (mult0 eta sAn))
         (rI.rI_base.plus (opp0 (mult0 beta s1n)) (mult0 beta s2n)))
       (plus0
         (opp0
           (mult0 eta
             (sum_over_S0 (fun s0 ->
               mult0 (np s0)
                 (rI.rI_base.plus (reward s0)
                   (rI.rI_base.opp
                     (mult0 beta
                       (rI.rI_base.plus (log0 (pi_t s0))
                         (rI.rI_base.opp (log0 (pi_ref s0)))))))))))
         (mult0 beta
           (sO.sum_over_S (fun s0 ->
             rI.rI_base.mult (np s0)
               (rI.rI_base.plus (rI.log (np s0))
                 (rI.rI_base.opp (rI.log (pi_t s0))))))))
       (id_sym
         (rI.rI_base.plus (opp0 (mult0 eta sAn))
           (rI.rI_base.plus (opp0 (mult0 beta s1n)) (mult0 beta s2n)))
         (rI.rI_base.plus
           (rI.rI_base.plus (opp0 (mult0 eta sAn)) (opp0 (mult0 beta s1n)))
           (mult0 beta s2n))
         (rI.rI_base.plus_assoc (opp0 (mult0 eta sAn))
           (opp0 (mult0 beta s1n)) (mult0 beta s2n)))
       (id_trans
         (plus0 (opp0 (mult0 eta sAn))
           (plus0 (opp0 (mult0 beta s1n)) (mult0 beta s2n)))
         (plus0 (opp0 (mult0 eta sAn))
           (mult0 beta (minus rI.rI_base s2n s1n)))
         (plus0
           (opp0
             (mult0 eta
               (sum_over_S0 (fun s0 ->
                 mult0 (np s0)
                   (rI.rI_base.plus (reward s0)
                     (rI.rI_base.opp
                       (mult0 beta
                         (rI.rI_base.plus (log0 (pi_t s0))
                           (rI.rI_base.opp (log0 (pi_ref s0)))))))))))
           (mult0 beta
             (sO.sum_over_S (fun s0 ->
               rI.rI_base.mult (np s0)
                 (rI.rI_base.plus (rI.log (np s0))
                   (rI.rI_base.opp (rI.log (pi_t s0))))))))
         (id_cong (fun x -> plus0 (opp0 (mult0 eta sAn)) x)
           (plus0 (opp0 (mult0 beta s1n)) (mult0 beta s2n))
           (mult0 beta (minus rI.rI_base s2n s1n)) hm)
         (id_cong (fun x -> plus0 (opp0 (mult0 eta sAn)) (mult0 beta x))
           (minus rI.rI_base s2n s1n)
           (sum_over_S0 (fun s0 ->
             mult0 (np s0) (minus rI.rI_base (log0 (np s0)) (log0 (pi_t s0)))))
           hkl))))

(** val surrogate_diff_identity :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt)
    -> r id -> (s -> lt) -> r id **)

let surrogate_diff_identity rI sS sO =
  let zero0 = rI.rI_base.zero in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos pi_t_norm _ ->
  let np =
    pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
      pi_t_pos
  in
  let a = advantage_aug rI sS reward beta pi_ref pi_t in
  let xn = sum_over_S0 (fun s0 -> mult0 (np s0) (a s0)) in
  let xt = sum_over_S0 (fun s0 -> mult0 (pi_t s0) (a s0)) in
  let k1 = relative_entropy rI sS sO np pi_t in
  let k2 = relative_entropy rI sS sO pi_t np in
  let hdec =
    rel_free_energy_decomp rI sS sO reward beta beta_pos pi_ref eta
      sum_over_S_pos pi_t pi_t_pos pi_t_norm
  in
  let hFt = f_t_simpl_t rI sS sO reward beta pi_ref eta pi_t in
  let hFn =
    f_t_simpl_next_kl rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
      pi_t pi_t_pos
  in
  let heq =
    id_trans
      (opp0
        (mult0 eta
          (sum_over_S0 (fun s0 ->
            mult0 (pi_t s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
      (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t) beta
        pi_t)
      (plus0 (plus0 (opp0 (mult0 eta xn)) (mult0 beta k1)) (mult0 beta k2))
      (id_sym
        (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
          beta pi_t)
        (opp0
          (mult0 eta
            (sum_over_S0 (fun s0 ->
              mult0 (pi_t s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
        hFt)
      (id_trans
        (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
          beta pi_t)
        (plus0
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos))
          (mult0 beta
            (sum_over_S0 (fun s0 ->
              mult0 (pi_t s0)
                (minus rI.rI_base (log0 (pi_t s0))
                  (log0
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos s0)))))))
        (plus0 (plus0 (opp0 (mult0 eta xn)) (mult0 beta k1)) (mult0 beta k2))
        hdec
        (id_cong2 plus0
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos))
          (plus0
            (opp0
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos s0)
                    (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)
                pi_t)))
          (mult0 beta
            (sum_over_S0 (fun s0 ->
              mult0 (pi_t s0)
                (minus rI.rI_base (log0 (pi_t s0))
                  (log0
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos s0))))))
          (mult0 beta
            (sum_over_S0 (fun s0 ->
              mult0 (pi_t s0)
                (minus rI.rI_base (log0 (pi_t s0))
                  (log0
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos s0))))))
          hFn Id_refl))
  in
  let heq2 =
    id_trans (opp0 (mult0 eta xt))
      (plus0 (plus0 (opp0 (mult0 eta xn)) (mult0 beta k1)) (mult0 beta k2))
      (plus0 (opp0 (mult0 eta xn)) (plus0 (mult0 beta k1) (mult0 beta k2)))
      heq
      (id_sym
        (rI.rI_base.plus (opp0 (mult0 eta xn))
          (rI.rI_base.plus (mult0 beta k1) (mult0 beta k2)))
        (rI.rI_base.plus
          (rI.rI_base.plus (opp0 (mult0 eta xn)) (mult0 beta k1))
          (mult0 beta k2))
        (rI.rI_base.plus_assoc (opp0 (mult0 eta xn)) (mult0 beta k1)
          (mult0 beta k2)))
  in
  let hstep =
    id_trans (plus0 (mult0 eta xn) (opp0 (mult0 eta xt)))
      (plus0 (mult0 eta xn)
        (plus0 (opp0 (mult0 eta xn)) (plus0 (mult0 beta k1) (mult0 beta k2))))
      (plus0 (mult0 beta k1) (mult0 beta k2))
      (id_cong2 plus0 (mult0 eta xn) (mult0 eta xn) (opp0 (mult0 eta xt))
        (plus0 (opp0 (mult0 eta xn)) (plus0 (mult0 beta k1) (mult0 beta k2)))
        Id_refl heq2)
      (id_trans
        (rI.rI_base.plus (mult0 eta xn)
          (rI.rI_base.plus (opp0 (mult0 eta xn))
            (plus0 (mult0 beta k1) (mult0 beta k2))))
        (rI.rI_base.plus
          (rI.rI_base.plus (mult0 eta xn) (opp0 (mult0 eta xn)))
          (plus0 (mult0 beta k1) (mult0 beta k2)))
        (plus0 (mult0 beta k1) (mult0 beta k2))
        (rI.rI_base.plus_assoc (mult0 eta xn) (opp0 (mult0 eta xn))
          (plus0 (mult0 beta k1) (mult0 beta k2)))
        (id_trans
          (plus0
            (rI.rI_base.plus (mult0 eta xn) (rI.rI_base.opp (mult0 eta xn)))
            (plus0 (mult0 beta k1) (mult0 beta k2)))
          (plus0 rI.rI_base.zero (plus0 (mult0 beta k1) (mult0 beta k2)))
          (plus0 (mult0 beta k1) (mult0 beta k2))
          (id_cong (fun x -> plus0 x (plus0 (mult0 beta k1) (mult0 beta k2)))
            (rI.rI_base.plus (mult0 eta xn) (rI.rI_base.opp (mult0 eta xn)))
            rI.rI_base.zero (rI.rI_base.plus_opp (mult0 eta xn)))
          (id_trans
            (rI.rI_base.plus zero0 (plus0 (mult0 beta k1) (mult0 beta k2)))
            (rI.rI_base.plus (plus0 (mult0 beta k1) (mult0 beta k2)) zero0)
            (plus0 (mult0 beta k1) (mult0 beta k2))
            (rI.rI_base.plus_comm zero0
              (plus0 (mult0 beta k1) (mult0 beta k2)))
            (rI.rI_base.plus_zero (plus0 (mult0 beta k1) (mult0 beta k2))))))
  in
  id_trans (rI.rI_base.mult eta (minus rI.rI_base xn xt))
    (minus rI.rI_base (rI.rI_base.mult eta xn) (rI.rI_base.mult eta xt))
    (rI.rI_base.mult beta (rI.rI_base.plus k1 k2))
    (mult_minus_distr_l rI eta xn xt)
    (id_trans (plus0 (mult0 eta xn) (opp0 (mult0 eta xt)))
      (plus0 (mult0 beta k1) (mult0 beta k2))
      (rI.rI_base.mult beta (rI.rI_base.plus k1 k2)) hstep
      (id_sym (rI.rI_base.mult beta (rI.rI_base.plus k1 k2))
        (rI.rI_base.plus (rI.rI_base.mult beta k1) (rI.rI_base.mult beta k2))
        (rI.rI_base.distrib beta k1 k2))))

(** val pi_next_pos :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt)
    -> s -> lt **)

let pi_next_pos rI sS sO =
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  (fun reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos s0 ->
  rI.mult_positive
    (inv_pos0 (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
      (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
        pi_t_pos))
    (mult0 (pi_t s0)
      (exp_neg0
        (opp0
          (mult0 (mult0 eta (inv_pos0 beta beta_pos))
            (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
    (rI.inv_pos_pos (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
      (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
        pi_t_pos))
    (rI.mult_positive (pi_t s0)
      (exp_neg0
        (opp0
          (mult0 (mult0 eta (inv_pos0 beta beta_pos))
            (advantage_aug rI sS reward beta pi_ref pi_t s0))))
      (pi_t_pos s0)
      (rI.rI_base.exp_neg_pos
        (opp0
          (mult0 (mult0 eta (inv_pos0 beta beta_pos))
            (advantage_aug rI sS reward beta pi_ref pi_t s0))))))

(** val mult_minus_distr_r_t12 :
    realInterfaceEnhanced -> r -> r -> r -> r id **)

let mult_minus_distr_r_t12 rI =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  (fun a b c ->
  id_trans (rI.rI_base.mult (plus0 a (opp0 b)) c)
    (rI.rI_base.mult c (plus0 a (opp0 b)))
    (rI.rI_base.plus (mult0 a c) (rI.rI_base.opp (mult0 b c)))
    (rI.rI_base.mult_comm (plus0 a (opp0 b)) c)
    (id_trans (rI.rI_base.mult c (rI.rI_base.plus a (opp0 b)))
      (rI.rI_base.plus (rI.rI_base.mult c a) (rI.rI_base.mult c (opp0 b)))
      (rI.rI_base.plus (mult0 a c) (rI.rI_base.opp (mult0 b c)))
      (rI.rI_base.distrib c a (opp0 b))
      (id_trans (plus0 (rI.rI_base.mult c a) (mult0 c (opp0 b)))
        (plus0 (rI.rI_base.mult a c) (mult0 c (opp0 b)))
        (rI.rI_base.plus (mult0 a c) (rI.rI_base.opp (mult0 b c)))
        (id_cong (fun x -> plus0 x (mult0 c (opp0 b))) (rI.rI_base.mult c a)
          (rI.rI_base.mult a c) (rI.rI_base.mult_comm c a))
        (id_trans (plus0 (mult0 a c) (rI.rI_base.mult c (rI.rI_base.opp b)))
          (plus0 (mult0 a c) (opp0 (rI.rI_base.mult b c)))
          (rI.rI_base.plus (mult0 a c) (rI.rI_base.opp (mult0 b c)))
          (id_cong (fun x -> plus0 (mult0 a c) x)
            (rI.rI_base.mult c (rI.rI_base.opp b))
            (opp0 (rI.rI_base.mult b c))
            (id_trans (rI.rI_base.mult c (rI.rI_base.opp b))
              (rI.rI_base.opp (rI.rI_base.mult c b))
              (opp0 (rI.rI_base.mult b c)) (opp_mult_l rI c b)
              (id_cong opp0 (rI.rI_base.mult c b) (rI.rI_base.mult b c)
                (rI.rI_base.mult_comm c b))))
          Id_refl))))

(** val eta_absorb_t12 : realInterfaceEnhanced -> r -> r -> r id **)

let eta_absorb_t12 rI =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  (fun eta a ->
  let h1 =
    id_trans (rI.rI_base.plus eta (rI.rI_base.plus one0 (opp0 eta)))
      (rI.rI_base.plus (rI.rI_base.plus eta one0) (opp0 eta)) one0
      (rI.rI_base.plus_assoc eta one0 (opp0 eta))
      (id_trans (plus0 (rI.rI_base.plus eta one0) (opp0 eta))
        (plus0 (rI.rI_base.plus one0 eta) (opp0 eta)) one0
        (id_cong (fun x -> plus0 x (opp0 eta)) (rI.rI_base.plus eta one0)
          (rI.rI_base.plus one0 eta) (rI.rI_base.plus_comm eta one0))
        (id_trans (rI.rI_base.plus (rI.rI_base.plus one0 eta) (opp0 eta))
          (rI.rI_base.plus one0 (rI.rI_base.plus eta (opp0 eta))) one0
          (id_sym (rI.rI_base.plus one0 (rI.rI_base.plus eta (opp0 eta)))
            (rI.rI_base.plus (rI.rI_base.plus one0 eta) (opp0 eta))
            (rI.rI_base.plus_assoc one0 eta (opp0 eta)))
          (id_trans (plus0 one0 (rI.rI_base.plus eta (rI.rI_base.opp eta)))
            (plus0 one0 rI.rI_base.zero) one0
            (id_cong (fun x -> plus0 one0 x)
              (rI.rI_base.plus eta (rI.rI_base.opp eta)) rI.rI_base.zero
              (rI.rI_base.plus_opp eta))
            (rI.rI_base.plus_zero one0))))
  in
  let h2 =
    id_cong2 plus0 (rI.rI_base.mult eta a) (rI.rI_base.mult a eta)
      (rI.rI_base.mult (minus rI.rI_base one0 eta) a)
      (rI.rI_base.mult a (minus rI.rI_base one0 eta))
      (rI.rI_base.mult_comm eta a)
      (rI.rI_base.mult_comm (minus rI.rI_base one0 eta) a)
  in
  let h3 =
    id_sym
      (rI.rI_base.mult a (rI.rI_base.plus eta (minus rI.rI_base one0 eta)))
      (rI.rI_base.plus (rI.rI_base.mult a eta)
        (rI.rI_base.mult a (minus rI.rI_base one0 eta)))
      (rI.rI_base.distrib a eta (minus rI.rI_base one0 eta))
  in
  id_trans (plus0 (mult0 eta a) (mult0 (minus rI.rI_base one0 eta) a))
    (plus0 (mult0 a eta) (mult0 a (minus rI.rI_base one0 eta))) a h2
    (id_trans (plus0 (mult0 a eta) (mult0 a (minus rI.rI_base one0 eta)))
      (mult0 a (plus0 eta (minus rI.rI_base one0 eta))) a h3
      (id_trans (mult0 a (plus0 eta (minus rI.rI_base one0 eta)))
        (mult0 a one0) a
        (id_cong (fun x -> mult0 a x) (plus0 eta (minus rI.rI_base one0 eta))
          one0 h1)
        (rI.rI_base.mult_one a))))

(** val align_energy_expand :
    realInterfaceEnhanced -> stateSpace -> (s -> r) -> r -> (s -> r) -> r ->
    (s -> r) -> s -> r id **)

let align_energy_expand rI sS =
  let zero0 = rI.rI_base.zero in
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let log0 = rI.log in
  (fun reward beta pi_ref eta pi_t s0 ->
  let a =
    minus rI.rI_base (reward s0)
      (mult0 beta (minus rI.rI_base (log0 (pi_t s0)) (log0 (pi_ref s0))))
  in
  let b1 = mult0 beta (log0 (pi_t s0)) in
  let b2 = mult0 beta (log0 (pi_ref s0)) in
  let h0 = reward_expand rI sS reward beta pi_ref pi_t s0 in
  let h1 =
    id_trans (opp0 (reward s0)) (opp0 (plus0 a (minus rI.rI_base b1 b2)))
      (plus0 (opp0 a) (plus0 (opp0 b1) b2))
      (id_cong opp0 (reward s0) (plus0 a (minus rI.rI_base b1 b2)) h0)
      (id_trans (rI.rI_base.opp (rI.rI_base.plus a (minus rI.rI_base b1 b2)))
        (rI.rI_base.plus (rI.rI_base.opp a)
          (rI.rI_base.opp (minus rI.rI_base b1 b2)))
        (plus0 (opp0 a) (plus0 (opp0 b1) b2))
        (opp_plus rI a (minus rI.rI_base b1 b2))
        (id_cong (fun x -> plus0 (opp0 a) x)
          (rI.rI_base.opp (minus rI.rI_base b1 b2))
          (rI.rI_base.plus (rI.rI_base.opp b1) b2) (opp_minus rI b1 b2)))
  in
  let h2 =
    id_trans (plus0 (opp0 (reward s0)) (rI.rI_base.opp b2))
      (plus0 (plus0 (opp0 a) (plus0 (opp0 b1) b2)) (rI.rI_base.opp b2))
      (plus0 (opp0 a) (opp0 b1))
      (id_cong2 plus0 (opp0 (reward s0))
        (plus0 (opp0 a) (plus0 (opp0 b1) b2)) (rI.rI_base.opp b2)
        (rI.rI_base.opp b2) h1 Id_refl)
      (id_trans
        (rI.rI_base.plus (rI.rI_base.plus (opp0 a) (plus0 (opp0 b1) b2))
          (opp0 b2))
        (rI.rI_base.plus (opp0 a)
          (rI.rI_base.plus (plus0 (opp0 b1) b2) (opp0 b2)))
        (plus0 (opp0 a) (opp0 b1))
        (id_sym
          (rI.rI_base.plus (opp0 a)
            (rI.rI_base.plus (plus0 (opp0 b1) b2) (opp0 b2)))
          (rI.rI_base.plus (rI.rI_base.plus (opp0 a) (plus0 (opp0 b1) b2))
            (opp0 b2))
          (rI.rI_base.plus_assoc (opp0 a) (plus0 (opp0 b1) b2) (opp0 b2)))
        (id_trans
          (plus0 (opp0 a)
            (rI.rI_base.plus (rI.rI_base.plus (opp0 b1) b2) (opp0 b2)))
          (plus0 (opp0 a)
            (rI.rI_base.plus (opp0 b1) (rI.rI_base.plus b2 (opp0 b2))))
          (plus0 (opp0 a) (opp0 b1))
          (id_cong (fun x -> plus0 (opp0 a) x)
            (rI.rI_base.plus (rI.rI_base.plus (opp0 b1) b2) (opp0 b2))
            (rI.rI_base.plus (opp0 b1) (rI.rI_base.plus b2 (opp0 b2)))
            (id_sym
              (rI.rI_base.plus (opp0 b1) (rI.rI_base.plus b2 (opp0 b2)))
              (rI.rI_base.plus (rI.rI_base.plus (opp0 b1) b2) (opp0 b2))
              (rI.rI_base.plus_assoc (opp0 b1) b2 (opp0 b2))))
          (id_trans
            (plus0 (opp0 a)
              (plus0 (opp0 b1) (rI.rI_base.plus b2 (rI.rI_base.opp b2))))
            (plus0 (opp0 a) (plus0 (opp0 b1) rI.rI_base.zero))
            (plus0 (opp0 a) (opp0 b1))
            (id_cong (fun x -> plus0 (opp0 a) (plus0 (opp0 b1) x))
              (rI.rI_base.plus b2 (rI.rI_base.opp b2)) rI.rI_base.zero
              (rI.rI_base.plus_opp b2))
            (id_cong (fun x -> plus0 (opp0 a) x)
              (rI.rI_base.plus (opp0 b1) rI.rI_base.zero) (opp0 b1)
              (rI.rI_base.plus_zero (opp0 b1))))))
  in
  let h3 =
    id_trans (rI.rI_base.mult (plus0 one0 (opp0 eta)) (opp0 a))
      (rI.rI_base.mult (opp0 a) (plus0 one0 (opp0 eta)))
      (plus0 (opp0 a) (mult0 eta a))
      (rI.rI_base.mult_comm (plus0 one0 (opp0 eta)) (opp0 a))
      (id_trans (rI.rI_base.mult (opp0 a) (rI.rI_base.plus one0 (opp0 eta)))
        (rI.rI_base.plus (rI.rI_base.mult (opp0 a) one0)
          (rI.rI_base.mult (opp0 a) (opp0 eta)))
        (plus0 (opp0 a) (mult0 eta a))
        (rI.rI_base.distrib (opp0 a) one0 (opp0 eta))
        (id_trans
          (plus0 (rI.rI_base.mult (opp0 a) rI.rI_base.one)
            (mult0 (opp0 a) (opp0 eta)))
          (plus0 (opp0 a) (mult0 (opp0 a) (opp0 eta)))
          (plus0 (opp0 a) (mult0 eta a))
          (id_cong (fun x -> plus0 x (mult0 (opp0 a) (opp0 eta)))
            (rI.rI_base.mult (opp0 a) rI.rI_base.one) (opp0 a)
            (rI.rI_base.mult_one (opp0 a)))
          (id_trans
            (plus0 (opp0 a) (rI.rI_base.mult (opp0 a) (rI.rI_base.opp eta)))
            (plus0 (opp0 a) (mult0 a eta)) (plus0 (opp0 a) (mult0 eta a))
            (id_cong (fun x -> plus0 (opp0 a) x)
              (rI.rI_base.mult (opp0 a) (rI.rI_base.opp eta)) (mult0 a eta)
              (id_trans (rI.rI_base.mult (opp0 a) (rI.rI_base.opp eta))
                (rI.rI_base.opp (rI.rI_base.mult (opp0 a) eta)) (mult0 a eta)
                (opp_mult_l rI (opp0 a) eta)
                (id_trans (opp0 (rI.rI_base.mult (rI.rI_base.opp a) eta))
                  (opp0 (rI.rI_base.opp (rI.rI_base.mult a eta)))
                  (mult0 a eta)
                  (id_cong opp0 (rI.rI_base.mult (rI.rI_base.opp a) eta)
                    (rI.rI_base.opp (rI.rI_base.mult a eta))
                    (opp_mult_r rI a eta))
                  (double_neg rI (mult0 a eta)))))
            (id_cong (fun x -> plus0 (opp0 a) x) (rI.rI_base.mult a eta)
              (rI.rI_base.mult eta a) (rI.rI_base.mult_comm a eta)))))
  in
  let h4 =
    id_trans
      (plus0 (plus0 (opp0 (mult0 eta a)) (opp0 b1))
        (mult0 (minus rI.rI_base one0 eta) (opp0 a)))
      (plus0 (plus0 (opp0 (mult0 eta a)) (opp0 b1))
        (plus0 (opp0 a) (mult0 eta a)))
      (plus0 (opp0 a) (opp0 b1))
      (id_cong (fun x -> plus0 (plus0 (opp0 (mult0 eta a)) (opp0 b1)) x)
        (mult0 (minus rI.rI_base one0 eta) (opp0 a))
        (plus0 (opp0 a) (mult0 eta a)) h3)
      (id_trans
        (rI.rI_base.plus (rI.rI_base.plus (opp0 (mult0 eta a)) (opp0 b1))
          (plus0 (opp0 a) (mult0 eta a)))
        (rI.rI_base.plus (opp0 (mult0 eta a))
          (rI.rI_base.plus (opp0 b1) (plus0 (opp0 a) (mult0 eta a))))
        (plus0 (opp0 a) (opp0 b1))
        (id_sym
          (rI.rI_base.plus (opp0 (mult0 eta a))
            (rI.rI_base.plus (opp0 b1) (plus0 (opp0 a) (mult0 eta a))))
          (rI.rI_base.plus (rI.rI_base.plus (opp0 (mult0 eta a)) (opp0 b1))
            (plus0 (opp0 a) (mult0 eta a)))
          (rI.rI_base.plus_assoc (opp0 (mult0 eta a)) (opp0 b1)
            (plus0 (opp0 a) (mult0 eta a))))
        (id_trans
          (plus0 (opp0 (mult0 eta a))
            (plus0 (opp0 b1) (rI.rI_base.plus (opp0 a) (mult0 eta a))))
          (plus0 (opp0 (mult0 eta a))
            (plus0 (opp0 b1) (rI.rI_base.plus (mult0 eta a) (opp0 a))))
          (plus0 (opp0 a) (opp0 b1))
          (id_cong (fun x -> plus0 (opp0 (mult0 eta a)) x)
            (plus0 (opp0 b1) (rI.rI_base.plus (opp0 a) (mult0 eta a)))
            (plus0 (opp0 b1) (rI.rI_base.plus (mult0 eta a) (opp0 a)))
            (id_cong (fun y -> plus0 (opp0 b1) y)
              (rI.rI_base.plus (opp0 a) (mult0 eta a))
              (rI.rI_base.plus (mult0 eta a) (opp0 a))
              (rI.rI_base.plus_comm (opp0 a) (mult0 eta a))))
          (id_trans
            (plus0 (opp0 (mult0 eta a))
              (rI.rI_base.plus (opp0 b1)
                (rI.rI_base.plus (mult0 eta a) (opp0 a))))
            (plus0 (opp0 (mult0 eta a))
              (rI.rI_base.plus (rI.rI_base.plus (opp0 b1) (mult0 eta a))
                (opp0 a)))
            (plus0 (opp0 a) (opp0 b1))
            (id_cong (fun x -> plus0 (opp0 (mult0 eta a)) x)
              (rI.rI_base.plus (opp0 b1)
                (rI.rI_base.plus (mult0 eta a) (opp0 a)))
              (rI.rI_base.plus (rI.rI_base.plus (opp0 b1) (mult0 eta a))
                (opp0 a))
              (rI.rI_base.plus_assoc (opp0 b1) (mult0 eta a) (opp0 a)))
            (id_trans
              (rI.rI_base.plus (opp0 (mult0 eta a))
                (rI.rI_base.plus (plus0 (opp0 b1) (mult0 eta a)) (opp0 a)))
              (rI.rI_base.plus
                (rI.rI_base.plus (opp0 (mult0 eta a))
                  (plus0 (opp0 b1) (mult0 eta a)))
                (opp0 a))
              (plus0 (opp0 a) (opp0 b1))
              (rI.rI_base.plus_assoc (opp0 (mult0 eta a))
                (plus0 (opp0 b1) (mult0 eta a)) (opp0 a))
              (id_trans
                (plus0
                  (plus0 (opp0 (mult0 eta a))
                    (rI.rI_base.plus (opp0 b1) (mult0 eta a)))
                  (opp0 a))
                (plus0
                  (plus0 (opp0 (mult0 eta a))
                    (rI.rI_base.plus (mult0 eta a) (opp0 b1)))
                  (opp0 a))
                (plus0 (opp0 a) (opp0 b1))
                (id_cong (fun x -> plus0 x (opp0 a))
                  (plus0 (opp0 (mult0 eta a))
                    (rI.rI_base.plus (opp0 b1) (mult0 eta a)))
                  (plus0 (opp0 (mult0 eta a))
                    (rI.rI_base.plus (mult0 eta a) (opp0 b1)))
                  (id_cong (fun y -> plus0 (opp0 (mult0 eta a)) y)
                    (rI.rI_base.plus (opp0 b1) (mult0 eta a))
                    (rI.rI_base.plus (mult0 eta a) (opp0 b1))
                    (rI.rI_base.plus_comm (opp0 b1) (mult0 eta a))))
                (id_trans
                  (plus0
                    (rI.rI_base.plus (opp0 (mult0 eta a))
                      (rI.rI_base.plus (mult0 eta a) (opp0 b1)))
                    (opp0 a))
                  (plus0
                    (rI.rI_base.plus
                      (rI.rI_base.plus (opp0 (mult0 eta a)) (mult0 eta a))
                      (opp0 b1))
                    (opp0 a))
                  (plus0 (opp0 a) (opp0 b1))
                  (id_cong (fun x -> plus0 x (opp0 a))
                    (rI.rI_base.plus (opp0 (mult0 eta a))
                      (rI.rI_base.plus (mult0 eta a) (opp0 b1)))
                    (rI.rI_base.plus
                      (rI.rI_base.plus (opp0 (mult0 eta a)) (mult0 eta a))
                      (opp0 b1))
                    (rI.rI_base.plus_assoc (opp0 (mult0 eta a)) (mult0 eta a)
                      (opp0 b1)))
                  (id_trans
                    (plus0
                      (plus0
                        (rI.rI_base.plus (opp0 (mult0 eta a)) (mult0 eta a))
                        (opp0 b1))
                      (opp0 a))
                    (plus0
                      (plus0
                        (rI.rI_base.plus (mult0 eta a) (opp0 (mult0 eta a)))
                        (opp0 b1))
                      (opp0 a))
                    (plus0 (opp0 a) (opp0 b1))
                    (id_cong (fun x -> plus0 x (opp0 a))
                      (plus0
                        (rI.rI_base.plus (opp0 (mult0 eta a)) (mult0 eta a))
                        (opp0 b1))
                      (plus0
                        (rI.rI_base.plus (mult0 eta a) (opp0 (mult0 eta a)))
                        (opp0 b1))
                      (id_cong (fun y -> plus0 y (opp0 b1))
                        (rI.rI_base.plus (opp0 (mult0 eta a)) (mult0 eta a))
                        (rI.rI_base.plus (mult0 eta a) (opp0 (mult0 eta a)))
                        (rI.rI_base.plus_comm (opp0 (mult0 eta a))
                          (mult0 eta a))))
                    (id_trans
                      (plus0
                        (plus0
                          (rI.rI_base.plus (mult0 eta a)
                            (rI.rI_base.opp (mult0 eta a)))
                          (opp0 b1))
                        (opp0 a))
                      (plus0 (plus0 rI.rI_base.zero (opp0 b1)) (opp0 a))
                      (plus0 (opp0 a) (opp0 b1))
                      (id_cong (fun x -> plus0 x (opp0 a))
                        (plus0
                          (rI.rI_base.plus (mult0 eta a)
                            (rI.rI_base.opp (mult0 eta a)))
                          (opp0 b1))
                        (plus0 rI.rI_base.zero (opp0 b1))
                        (id_cong (fun y -> plus0 y (opp0 b1))
                          (rI.rI_base.plus (mult0 eta a)
                            (rI.rI_base.opp (mult0 eta a)))
                          rI.rI_base.zero (rI.rI_base.plus_opp (mult0 eta a))))
                      (id_trans
                        (plus0 (rI.rI_base.plus zero0 (opp0 b1)) (opp0 a))
                        (plus0 (opp0 b1) (opp0 a)) (plus0 (opp0 a) (opp0 b1))
                        (id_cong (fun x -> plus0 x (opp0 a))
                          (rI.rI_base.plus zero0 (opp0 b1)) (opp0 b1)
                          (id_trans (rI.rI_base.plus zero0 (opp0 b1))
                            (rI.rI_base.plus (opp0 b1) zero0) (opp0 b1)
                            (rI.rI_base.plus_comm zero0 (opp0 b1))
                            (rI.rI_base.plus_zero (opp0 b1))))
                        (rI.rI_base.plus_comm (opp0 b1) (opp0 a)))))))))))
  in
  id_trans (minus rI.rI_base (opp0 (reward s0)) b2)
    (plus0 (opp0 a) (opp0 b1))
    (plus0 (minus rI.rI_base (opp0 (mult0 eta a)) b1)
      (mult0 (minus rI.rI_base one0 eta) (opp0 a)))
    h2
    (id_sym
      (plus0 (minus rI.rI_base (opp0 (mult0 eta a)) b1)
        (mult0 (minus rI.rI_base one0 eta) (opp0 a)))
      (plus0 (opp0 a) (opp0 b1)) h4))

(** val f_align_F_t_rel :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s ->
    r) -> r -> (s -> r) -> (s -> r) -> r id **)

let f_align_F_t_rel rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta pi_ref eta pi_t p ->
  let hpt = fun s0 ->
    id_trans (mult0 (p s0) (align_energy rI sS reward beta pi_ref s0))
      (mult0 (p s0)
        (plus0 (energy_t rI sS reward beta pi_ref eta pi_t s0)
          (mult0 (minus rI.rI_base one0 eta)
            (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
      (plus0 (mult0 (p s0) (energy_t rI sS reward beta pi_ref eta pi_t s0))
        (mult0 (p s0)
          (mult0 (minus rI.rI_base one0 eta)
            (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
      (id_cong (fun x -> mult0 (p s0) x)
        (align_energy rI sS reward beta pi_ref s0)
        (plus0 (energy_t rI sS reward beta pi_ref eta pi_t s0)
          (mult0 (minus rI.rI_base one0 eta)
            (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0))))
        (align_energy_expand rI sS reward beta pi_ref eta pi_t s0))
      (rI.rI_base.distrib (p s0)
        (energy_t rI sS reward beta pi_ref eta pi_t s0)
        (mult0 (minus rI.rI_base one0 eta)
          (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0))))
  in
  let hsum =
    id_trans
      (sO.sum_over_S (fun s0 ->
        mult0 (p s0) (align_energy rI sS reward beta pi_ref s0)))
      (sO.sum_over_S (fun s0 ->
        plus0 (mult0 (p s0) (energy_t rI sS reward beta pi_ref eta pi_t s0))
          (mult0 (p s0)
            (mult0 (minus rI.rI_base one0 eta)
              (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0))))))
      (plus0
        (sum_over_S0 (fun s0 ->
          mult0 (p s0) (energy_t rI sS reward beta pi_ref eta pi_t s0)))
        (sum_over_S0 (fun s0 ->
          mult0 (p s0)
            (mult0 (minus rI.rI_base one0 eta)
              (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0))))))
      (sO.sum_over_S_ext (fun s0 ->
        mult0 (p s0) (align_energy rI sS reward beta pi_ref s0)) (fun s0 ->
        plus0 (mult0 (p s0) (energy_t rI sS reward beta pi_ref eta pi_t s0))
          (mult0 (p s0)
            (mult0 (minus rI.rI_base one0 eta)
              (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
        hpt)
      (sO.sum_over_S_add (fun s0 ->
        mult0 (p s0) (energy_t rI sS reward beta pi_ref eta pi_t s0))
        (fun s0 ->
        mult0 (p s0)
          (mult0 (minus rI.rI_base one0 eta)
            (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
  in
  let hscal =
    id_trans
      (sum_over_S0 (fun s0 ->
        mult0 (p s0)
          (mult0 (minus rI.rI_base one0 eta)
            (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
      (mult0 (minus rI.rI_base one0 eta)
        (sum_over_S0 (fun s0 ->
          mult0 (p s0) (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
      (mult0 (minus rI.rI_base one0 eta)
        (opp0
          (sum_over_S0 (fun s0 ->
            mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
      (sum_ptimes_scal_t12 rI sS sO p (minus rI.rI_base one0 eta) (fun s0 ->
        opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0)))
      (id_cong (fun x -> mult0 (minus rI.rI_base one0 eta) x)
        (sO.sum_over_S (fun s0 ->
          rI.rI_base.mult (p s0)
            (rI.rI_base.opp (advantage_aug rI sS reward beta pi_ref pi_t s0))))
        (opp0
          (sum_over_S0 (fun s0 ->
            mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0))))
        (id_trans
          (sO.sum_over_S (fun s0 ->
            rI.rI_base.mult (p s0)
              (rI.rI_base.opp
                (advantage_aug rI sS reward beta pi_ref pi_t s0))))
          (sO.sum_over_S (fun s0 ->
            rI.rI_base.opp
              (rI.rI_base.mult (p s0)
                (advantage_aug rI sS reward beta pi_ref pi_t s0))))
          (opp0
            (sum_over_S0 (fun s0 ->
              mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0))))
          (sO.sum_over_S_ext (fun s0 ->
            rI.rI_base.mult (p s0)
              (rI.rI_base.opp
                (advantage_aug rI sS reward beta pi_ref pi_t s0)))
            (fun s0 ->
            rI.rI_base.opp
              (rI.rI_base.mult (p s0)
                (advantage_aug rI sS reward beta pi_ref pi_t s0)))
            (fun s0 ->
            opp_mult_l rI (p s0)
              (advantage_aug rI sS reward beta pi_ref pi_t s0)))
          (sum_over_S_opp_t12 rI sS sO (fun s0 ->
            mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
  in
  let sEt =
    sum_over_S0 (fun s0 ->
      mult0 (p s0) (energy_t rI sS reward beta pi_ref eta pi_t s0))
  in
  let sEnt = sum_over_S0 (fun s0 -> mult0 (p s0) (log0 (p s0))) in
  let sA =
    sum_over_S0 (fun s0 ->
      mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0))
  in
  let sX =
    sum_over_S0 (fun s0 ->
      mult0 (p s0)
        (mult0 (minus rI.rI_base one0 eta)
          (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0))))
  in
  id_trans
    (plus0
      (sum_over_S0 (fun s0 ->
        mult0 (p s0) (align_energy rI sS reward beta pi_ref s0)))
      (rI.rI_base.mult beta
        (sO.sum_over_S (fun s0 -> rI.rI_base.mult (p s0) (rI.log (p s0))))))
    (plus0
      (plus0
        (sum_over_S0 (fun s0 ->
          mult0 (p s0) (energy_t rI sS reward beta pi_ref eta pi_t s0)))
        (sum_over_S0 (fun s0 ->
          mult0 (p s0)
            (mult0 (minus rI.rI_base one0 eta)
              (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0))))))
      (rI.rI_base.mult beta
        (sO.sum_over_S (fun s0 -> rI.rI_base.mult (p s0) (rI.log (p s0))))))
    (plus0
      (rI.rI_base.plus
        (sO.sum_over_S (fun s0 ->
          rI.rI_base.mult (p s0)
            (energy_t rI sS reward beta pi_ref eta pi_t s0)))
        (rI.rI_base.mult beta
          (sO.sum_over_S (fun s0 -> rI.rI_base.mult (p s0) (rI.log (p s0))))))
      (mult0 (minus rI.rI_base one0 eta) (opp0 sA)))
    (id_cong2 plus0
      (sum_over_S0 (fun s0 ->
        mult0 (p s0) (align_energy rI sS reward beta pi_ref s0)))
      (plus0
        (sum_over_S0 (fun s0 ->
          mult0 (p s0) (energy_t rI sS reward beta pi_ref eta pi_t s0)))
        (sum_over_S0 (fun s0 ->
          mult0 (p s0)
            (mult0 (minus rI.rI_base one0 eta)
              (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0))))))
      (rI.rI_base.mult beta
        (sO.sum_over_S (fun s0 -> rI.rI_base.mult (p s0) (rI.log (p s0)))))
      (rI.rI_base.mult beta
        (sO.sum_over_S (fun s0 -> rI.rI_base.mult (p s0) (rI.log (p s0)))))
      hsum Id_refl)
    (id_trans (rI.rI_base.plus (rI.rI_base.plus sEt sX) (mult0 beta sEnt))
      (rI.rI_base.plus sEt (rI.rI_base.plus sX (mult0 beta sEnt)))
      (plus0
        (rI.rI_base.plus
          (sO.sum_over_S (fun s0 ->
            rI.rI_base.mult (p s0)
              (energy_t rI sS reward beta pi_ref eta pi_t s0)))
          (rI.rI_base.mult beta
            (sO.sum_over_S (fun s0 -> rI.rI_base.mult (p s0) (rI.log (p s0))))))
        (mult0 (minus rI.rI_base one0 eta) (opp0 sA)))
      (id_sym (rI.rI_base.plus sEt (rI.rI_base.plus sX (mult0 beta sEnt)))
        (rI.rI_base.plus (rI.rI_base.plus sEt sX) (mult0 beta sEnt))
        (rI.rI_base.plus_assoc sEt sX (mult0 beta sEnt)))
      (id_trans
        (plus0 sEt
          (plus0
            (sum_over_S0 (fun s0 ->
              mult0 (p s0)
                (mult0 (minus rI.rI_base one0 eta)
                  (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
            (mult0 beta sEnt)))
        (plus0 sEt
          (rI.rI_base.plus (mult0 beta sEnt)
            (mult0 (minus rI.rI_base one0 eta) (opp0 sA))))
        (plus0
          (rI.rI_base.plus
            (sO.sum_over_S (fun s0 ->
              rI.rI_base.mult (p s0)
                (energy_t rI sS reward beta pi_ref eta pi_t s0)))
            (rI.rI_base.mult beta
              (sO.sum_over_S (fun s0 ->
                rI.rI_base.mult (p s0) (rI.log (p s0))))))
          (mult0 (minus rI.rI_base one0 eta) (opp0 sA)))
        (id_cong (fun x -> plus0 sEt x)
          (plus0
            (sum_over_S0 (fun s0 ->
              mult0 (p s0)
                (mult0 (minus rI.rI_base one0 eta)
                  (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
            (mult0 beta sEnt))
          (rI.rI_base.plus (mult0 beta sEnt)
            (mult0 (minus rI.rI_base one0 eta) (opp0 sA)))
          (id_trans
            (plus0
              (sum_over_S0 (fun s0 ->
                mult0 (p s0)
                  (mult0 (minus rI.rI_base one0 eta)
                    (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
              (mult0 beta sEnt))
            (plus0
              (mult0 (minus rI.rI_base one0 eta)
                (opp0
                  (sum_over_S0 (fun s0 ->
                    mult0 (p s0)
                      (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
              (mult0 beta sEnt))
            (rI.rI_base.plus (mult0 beta sEnt)
              (mult0 (minus rI.rI_base one0 eta) (opp0 sA)))
            (id_cong (fun y -> plus0 y (mult0 beta sEnt))
              (sum_over_S0 (fun s0 ->
                mult0 (p s0)
                  (mult0 (minus rI.rI_base one0 eta)
                    (opp0 (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
              (mult0 (minus rI.rI_base one0 eta)
                (opp0
                  (sum_over_S0 (fun s0 ->
                    mult0 (p s0)
                      (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
              hscal)
            (rI.rI_base.plus_comm
              (mult0 (minus rI.rI_base one0 eta) (opp0 sA)) (mult0 beta sEnt))))
        (rI.rI_base.plus_assoc sEt (mult0 beta sEnt)
          (mult0 (minus rI.rI_base one0 eta) (opp0 sA))))))

(** val align_objective_t12_decomp :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s ->
    r) -> r -> (s -> r) -> (s -> r) -> r id **)

let align_objective_t12_decomp rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta pi_ref eta pi_t p ->
  let hrel = f_align_F_t_rel rI sS sO reward beta pi_ref eta pi_t p in
  id_trans
    (opp0
      (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta p))
    (opp0
      (plus0
        (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
          beta p)
        (mult0 (minus rI.rI_base one0 eta)
          (opp0
            (sum_over_S0 (fun s0 ->
              mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))))))
    (plus0
      (opp0
        (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
          beta p))
      (mult0 (minus rI.rI_base one0 eta)
        (sum_over_S0 (fun s0 ->
          mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
    (id_cong opp0
      (free_energy rI sS sO (align_energy rI sS reward beta pi_ref) beta p)
      (plus0
        (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
          beta p)
        (mult0 (minus rI.rI_base one0 eta)
          (opp0
            (sum_over_S0 (fun s0 ->
              mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0))))))
      hrel)
    (id_trans
      (rI.rI_base.opp
        (rI.rI_base.plus
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta p)
          (mult0 (minus rI.rI_base one0 eta)
            (opp0
              (sum_over_S0 (fun s0 ->
                mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))))))
      (rI.rI_base.plus
        (rI.rI_base.opp
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta p))
        (rI.rI_base.opp
          (mult0 (minus rI.rI_base one0 eta)
            (opp0
              (sum_over_S0 (fun s0 ->
                mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))))))
      (plus0
        (opp0
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta p))
        (mult0 (minus rI.rI_base one0 eta)
          (sum_over_S0 (fun s0 ->
            mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
      (opp_plus rI
        (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
          beta p)
        (mult0 (minus rI.rI_base one0 eta)
          (opp0
            (sum_over_S0 (fun s0 ->
              mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0))))))
      (id_cong (fun x ->
        plus0
          (opp0
            (free_energy rI sS sO
              (energy_t rI sS reward beta pi_ref eta pi_t) beta p))
          x)
        (opp0
          (rI.rI_base.mult (minus rI.rI_base one0 eta)
            (rI.rI_base.opp
              (sum_over_S0 (fun s0 ->
                mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0))))))
        (mult0 (minus rI.rI_base one0 eta)
          (sum_over_S0 (fun s0 ->
            mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0))))
        (id_trans
          (opp0
            (rI.rI_base.mult (minus rI.rI_base one0 eta)
              (rI.rI_base.opp
                (sum_over_S0 (fun s0 ->
                  mult0 (p s0)
                    (advantage_aug rI sS reward beta pi_ref pi_t s0))))))
          (opp0
            (rI.rI_base.opp
              (rI.rI_base.mult (minus rI.rI_base one0 eta)
                (sum_over_S0 (fun s0 ->
                  mult0 (p s0)
                    (advantage_aug rI sS reward beta pi_ref pi_t s0))))))
          (mult0 (minus rI.rI_base one0 eta)
            (sum_over_S0 (fun s0 ->
              mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0))))
          (id_cong opp0
            (rI.rI_base.mult (minus rI.rI_base one0 eta)
              (rI.rI_base.opp
                (sum_over_S0 (fun s0 ->
                  mult0 (p s0)
                    (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
            (rI.rI_base.opp
              (rI.rI_base.mult (minus rI.rI_base one0 eta)
                (sum_over_S0 (fun s0 ->
                  mult0 (p s0)
                    (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
            (opp_mult_l rI (minus rI.rI_base one0 eta)
              (sum_over_S0 (fun s0 ->
                mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
          (double_neg rI
            (mult0 (minus rI.rI_base one0 eta)
              (sum_over_S0 (fun s0 ->
                mult0 (p s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))))))))

(** val j_pi_t_t12 :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s ->
    r) -> r -> (s -> r) -> r id -> r id **)

let j_pi_t_t12 rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta pi_ref eta pi_t _ ->
  let hdec =
    align_objective_t12_decomp rI sS sO reward beta pi_ref eta pi_t pi_t
  in
  let hFt = f_t_simpl_t rI sS sO reward beta pi_ref eta pi_t in
  let xt =
    sum_over_S0 (fun s0 ->
      mult0 (pi_t s0) (advantage_aug rI sS reward beta pi_ref pi_t s0))
  in
  id_trans (align_objective rI sS sO reward beta pi_ref pi_t)
    (plus0
      (opp0
        (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
          beta pi_t))
      (mult0 (minus rI.rI_base one0 eta)
        (sum_over_S0 (fun s0 ->
          mult0 (pi_t s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
    xt hdec
    (id_trans
      (plus0
        (opp0
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta pi_t))
        (mult0 (minus rI.rI_base one0 eta) xt))
      (plus0 (mult0 eta xt) (mult0 (minus rI.rI_base one0 eta) xt)) xt
      (id_cong (fun x -> plus0 x (mult0 (minus rI.rI_base one0 eta) xt))
        (opp0
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta pi_t))
        (mult0 eta xt)
        (id_trans
          (opp0
            (free_energy rI sS sO
              (energy_t rI sS reward beta pi_ref eta pi_t) beta pi_t))
          (opp0
            (opp0
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0 (pi_t s0)
                    (advantage_aug rI sS reward beta pi_ref pi_t s0))))))
          (mult0 eta xt)
          (id_cong opp0
            (free_energy rI sS sO
              (energy_t rI sS reward beta pi_ref eta pi_t) beta pi_t)
            (opp0
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0 (pi_t s0)
                    (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
            hFt)
          (double_neg rI (mult0 eta xt))))
      (eta_absorb_t12 rI eta xt)))

(** val j_pi_next_t12 :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt)
    -> r id **)

let j_pi_next_t12 rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos ->
  let hdec =
    align_objective_t12_decomp rI sS sO reward beta pi_ref eta pi_t
      (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
        pi_t_pos)
  in
  let hFn =
    f_t_simpl_next_kl rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
      pi_t pi_t_pos
  in
  let np =
    pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
      pi_t_pos
  in
  let a = advantage_aug rI sS reward beta pi_ref pi_t in
  let xn = sum_over_S0 (fun s0 -> mult0 (np s0) (a s0)) in
  let k1 = relative_entropy rI sS sO np pi_t in
  let hopp =
    id_trans
      (rI.rI_base.opp (rI.rI_base.plus (opp0 (mult0 eta xn)) (mult0 beta k1)))
      (rI.rI_base.plus (rI.rI_base.opp (opp0 (mult0 eta xn)))
        (rI.rI_base.opp (mult0 beta k1)))
      (plus0 (mult0 eta xn) (opp0 (mult0 beta k1)))
      (opp_plus rI (opp0 (mult0 eta xn)) (mult0 beta k1))
      (id_cong2 plus0 (rI.rI_base.opp (rI.rI_base.opp (mult0 eta xn)))
        (mult0 eta xn) (rI.rI_base.opp (mult0 beta k1))
        (rI.rI_base.opp (mult0 beta k1)) (double_neg rI (mult0 eta xn))
        Id_refl)
  in
  id_trans
    (align_objective rI sS sO reward beta pi_ref
      (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
        pi_t_pos))
    (plus0
      (opp0
        (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
          beta
          (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos)))
      (mult0 (minus rI.rI_base one0 eta)
        (sum_over_S0 (fun s0 ->
          mult0
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos s0)
            (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
    (minus rI.rI_base xn (mult0 beta k1)) hdec
    (id_trans
      (plus0
        (opp0
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos)))
        (mult0 (minus rI.rI_base one0 eta) xn))
      (plus0 (plus0 (mult0 eta xn) (opp0 (mult0 beta k1)))
        (mult0 (minus rI.rI_base one0 eta) xn))
      (minus rI.rI_base xn (mult0 beta k1))
      (id_cong (fun x -> plus0 x (mult0 (minus rI.rI_base one0 eta) xn))
        (opp0
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos)))
        (plus0 (mult0 eta xn) (opp0 (mult0 beta k1)))
        (id_trans
          (opp0
            (free_energy rI sS sO
              (energy_t rI sS reward beta pi_ref eta pi_t) beta
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos)))
          (opp0
            (plus0
              (opp0
                (mult0 eta
                  (sum_over_S0 (fun s0 ->
                    mult0
                      (pi_next rI sS sO reward beta beta_pos pi_ref eta
                        sum_over_S_pos pi_t pi_t_pos s0)
                      (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_next rI sS sO reward beta beta_pos pi_ref eta
                    sum_over_S_pos pi_t pi_t_pos)
                  pi_t))))
          (plus0 (mult0 eta xn) (opp0 (mult0 beta k1)))
          (id_cong opp0
            (free_energy rI sS sO
              (energy_t rI sS reward beta pi_ref eta pi_t) beta
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos))
            (plus0
              (opp0
                (mult0 eta
                  (sum_over_S0 (fun s0 ->
                    mult0
                      (pi_next rI sS sO reward beta beta_pos pi_ref eta
                        sum_over_S_pos pi_t pi_t_pos s0)
                      (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_next rI sS sO reward beta beta_pos pi_ref eta
                    sum_over_S_pos pi_t pi_t_pos)
                  pi_t)))
            hFn)
          hopp))
      (id_trans
        (rI.rI_base.plus
          (rI.rI_base.plus (mult0 eta xn) (opp0 (mult0 beta k1)))
          (mult0 (minus rI.rI_base one0 eta) xn))
        (rI.rI_base.plus (mult0 eta xn)
          (rI.rI_base.plus (opp0 (mult0 beta k1))
            (mult0 (minus rI.rI_base one0 eta) xn)))
        (rI.rI_base.plus xn (rI.rI_base.opp (mult0 beta k1)))
        (id_sym
          (rI.rI_base.plus (mult0 eta xn)
            (rI.rI_base.plus (opp0 (mult0 beta k1))
              (mult0 (minus rI.rI_base one0 eta) xn)))
          (rI.rI_base.plus
            (rI.rI_base.plus (mult0 eta xn) (opp0 (mult0 beta k1)))
            (mult0 (minus rI.rI_base one0 eta) xn))
          (rI.rI_base.plus_assoc (mult0 eta xn) (opp0 (mult0 beta k1))
            (mult0 (minus rI.rI_base one0 eta) xn)))
        (id_trans
          (plus0 (mult0 eta xn)
            (rI.rI_base.plus (opp0 (mult0 beta k1))
              (mult0 (minus rI.rI_base one0 eta) xn)))
          (plus0 (mult0 eta xn)
            (rI.rI_base.plus (mult0 (minus rI.rI_base one0 eta) xn)
              (opp0 (mult0 beta k1))))
          (rI.rI_base.plus xn (rI.rI_base.opp (mult0 beta k1)))
          (id_cong (fun x -> plus0 (mult0 eta xn) x)
            (rI.rI_base.plus (opp0 (mult0 beta k1))
              (mult0 (minus rI.rI_base one0 eta) xn))
            (rI.rI_base.plus (mult0 (minus rI.rI_base one0 eta) xn)
              (opp0 (mult0 beta k1)))
            (rI.rI_base.plus_comm (opp0 (mult0 beta k1))
              (mult0 (minus rI.rI_base one0 eta) xn)))
          (id_trans
            (rI.rI_base.plus (mult0 eta xn)
              (rI.rI_base.plus (mult0 (minus rI.rI_base one0 eta) xn)
                (opp0 (mult0 beta k1))))
            (rI.rI_base.plus
              (rI.rI_base.plus (mult0 eta xn)
                (mult0 (minus rI.rI_base one0 eta) xn))
              (opp0 (mult0 beta k1)))
            (rI.rI_base.plus xn (rI.rI_base.opp (mult0 beta k1)))
            (rI.rI_base.plus_assoc (mult0 eta xn)
              (mult0 (minus rI.rI_base one0 eta) xn) (opp0 (mult0 beta k1)))
            (id_cong (fun x -> plus0 x (opp0 (mult0 beta k1)))
              (plus0 (mult0 eta xn) (mult0 (minus rI.rI_base one0 eta) xn))
              xn (eta_absorb_t12 rI eta xn)))))))

(** val f_t_simpl_p :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> (s ->
    r) -> r -> (s -> r) -> (s -> r) -> r id **)

let f_t_simpl_p rI sS sO =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta pi_ref eta ->
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun pi_t p ->
  let a = advantage_aug rI sS reward beta pi_ref pi_t in
  let s1p = sum_over_S0 (fun s0 -> mult0 (p s0) (log0 (pi_t s0))) in
  let x = opp0 (mult0 eta (sum_over_S0 (fun s0 -> mult0 (p s0) (a s0)))) in
  let sp = sum_over_S0 (fun s0 -> mult0 (p s0) (log0 (p s0))) in
  let h1 = sum_ptimes_opp_scal_t12 rI sS sO p eta a in
  let h2 =
    id_trans
      (sO.sum_over_S (fun s0 ->
        rI.rI_base.mult (p s0) (rI.rI_base.mult beta (log0 (pi_t s0)))))
      (sO.sum_over_S (fun s0 ->
        rI.rI_base.mult beta (rI.rI_base.mult (p s0) (log0 (pi_t s0)))))
      (mult0 beta (sum_over_S0 (fun s0 -> mult0 (p s0) (log0 (pi_t s0)))))
      (sO.sum_over_S_ext (fun s0 ->
        rI.rI_base.mult (p s0) (rI.rI_base.mult beta (log0 (pi_t s0))))
        (fun s0 ->
        rI.rI_base.mult beta (rI.rI_base.mult (p s0) (log0 (pi_t s0))))
        (fun s0 ->
        id_trans
          (rI.rI_base.mult (p s0) (rI.rI_base.mult beta (log0 (pi_t s0))))
          (rI.rI_base.mult (rI.rI_base.mult (p s0) beta) (log0 (pi_t s0)))
          (rI.rI_base.mult beta (rI.rI_base.mult (p s0) (log0 (pi_t s0))))
          (rI.rI_base.mult_assoc (p s0) beta (log0 (pi_t s0)))
          (id_trans (mult0 (rI.rI_base.mult (p s0) beta) (log0 (pi_t s0)))
            (mult0 (rI.rI_base.mult beta (p s0)) (log0 (pi_t s0)))
            (rI.rI_base.mult beta (rI.rI_base.mult (p s0) (log0 (pi_t s0))))
            (id_cong (fun x0 -> mult0 x0 (log0 (pi_t s0)))
              (rI.rI_base.mult (p s0) beta) (rI.rI_base.mult beta (p s0))
              (rI.rI_base.mult_comm (p s0) beta))
            (id_sym
              (rI.rI_base.mult beta (rI.rI_base.mult (p s0) (log0 (pi_t s0))))
              (rI.rI_base.mult (rI.rI_base.mult beta (p s0)) (log0 (pi_t s0)))
              (rI.rI_base.mult_assoc beta (p s0) (log0 (pi_t s0)))))))
      (sO.sum_over_S_linear beta (fun s0 -> mult0 (p s0) (log0 (pi_t s0))))
  in
  let hsum =
    id_trans
      (sO.sum_over_S (fun s0 ->
        rI.rI_base.mult (p s0)
          (minus rI.rI_base (opp0 (mult0 eta (a s0)))
            (mult0 beta (log0 (pi_t s0))))))
      (sO.sum_over_S (fun s0 ->
        minus rI.rI_base (rI.rI_base.mult (p s0) (opp0 (mult0 eta (a s0))))
          (rI.rI_base.mult (p s0) (mult0 beta (log0 (pi_t s0))))))
      (minus rI.rI_base
        (opp0 (mult0 eta (sum_over_S0 (fun s0 -> mult0 (p s0) (a s0)))))
        (mult0 beta s1p))
      (sO.sum_over_S_ext (fun s0 ->
        rI.rI_base.mult (p s0)
          (minus rI.rI_base (opp0 (mult0 eta (a s0)))
            (mult0 beta (log0 (pi_t s0)))))
        (fun s0 ->
        minus rI.rI_base (rI.rI_base.mult (p s0) (opp0 (mult0 eta (a s0))))
          (rI.rI_base.mult (p s0) (mult0 beta (log0 (pi_t s0)))))
        (fun s0 ->
        mult_minus_distr_l rI (p s0) (opp0 (mult0 eta (a s0)))
          (mult0 beta (log0 (pi_t s0)))))
      (id_trans
        (sO.sum_over_S (fun s0 ->
          minus rI.rI_base (mult0 (p s0) (opp0 (mult0 eta (a s0))))
            (mult0 (p s0) (mult0 beta (log0 (pi_t s0))))))
        (minus rI.rI_base
          (sO.sum_over_S (fun s0 -> mult0 (p s0) (opp0 (mult0 eta (a s0)))))
          (sO.sum_over_S (fun s0 ->
            mult0 (p s0) (mult0 beta (log0 (pi_t s0))))))
        (minus rI.rI_base
          (opp0 (mult0 eta (sum_over_S0 (fun s0 -> mult0 (p s0) (a s0)))))
          (mult0 beta s1p))
        (sum_over_S_minus rI sS sO (fun s0 ->
          mult0 (p s0) (opp0 (mult0 eta (a s0)))) (fun s0 ->
          mult0 (p s0) (mult0 beta (log0 (pi_t s0)))))
        (id_cong2 (minus rI.rI_base)
          (sum_over_S0 (fun s0 -> mult0 (p s0) (opp0 (mult0 eta (a s0)))))
          (opp0 (mult0 eta (sum_over_S0 (fun s0 -> mult0 (p s0) (a s0)))))
          (sum_over_S0 (fun s0 -> mult0 (p s0) (mult0 beta (log0 (pi_t s0)))))
          (mult0 beta s1p) h1 h2))
  in
  let hkl =
    id_trans
      (minus rI.rI_base
        (sO.sum_over_S (fun s0 -> mult0 (p s0) (log0 (p s0))))
        (sO.sum_over_S (fun s0 -> mult0 (p s0) (log0 (pi_t s0)))))
      (sO.sum_over_S (fun s0 ->
        minus rI.rI_base (mult0 (p s0) (log0 (p s0)))
          (mult0 (p s0) (log0 (pi_t s0)))))
      (sO.sum_over_S (fun s0 ->
        rI.rI_base.mult (p s0)
          (minus rI.rI_base (log0 (p s0)) (log0 (pi_t s0)))))
      (id_sym
        (sO.sum_over_S (fun s0 ->
          minus rI.rI_base (mult0 (p s0) (log0 (p s0)))
            (mult0 (p s0) (log0 (pi_t s0)))))
        (minus rI.rI_base
          (sO.sum_over_S (fun s0 -> mult0 (p s0) (log0 (p s0))))
          (sO.sum_over_S (fun s0 -> mult0 (p s0) (log0 (pi_t s0)))))
        (sum_over_S_minus rI sS sO (fun s0 -> mult0 (p s0) (log0 (p s0)))
          (fun s0 -> mult0 (p s0) (log0 (pi_t s0)))))
      (sO.sum_over_S_ext (fun s0 ->
        minus rI.rI_base (rI.rI_base.mult (p s0) (log0 (p s0)))
          (rI.rI_base.mult (p s0) (log0 (pi_t s0))))
        (fun s0 ->
        rI.rI_base.mult (p s0)
          (minus rI.rI_base (log0 (p s0)) (log0 (pi_t s0))))
        (fun s0 ->
        id_sym
          (rI.rI_base.mult (p s0)
            (minus rI.rI_base (log0 (p s0)) (log0 (pi_t s0))))
          (minus rI.rI_base (rI.rI_base.mult (p s0) (log0 (p s0)))
            (rI.rI_base.mult (p s0) (log0 (pi_t s0))))
          (mult_minus_distr_l rI (p s0) (log0 (p s0)) (log0 (pi_t s0)))))
  in
  let hlin =
    id_sym (rI.rI_base.mult beta (minus rI.rI_base sp s1p))
      (minus rI.rI_base (rI.rI_base.mult beta sp) (rI.rI_base.mult beta s1p))
      (mult_minus_distr_l rI beta sp s1p)
  in
  internal_Id_rew_r
    (sum_over_S0 (fun s0 ->
      mult0 (p s0)
        (minus rI.rI_base (opp0 (mult0 eta (a s0)))
          (mult0 beta (log0 (pi_t s0))))))
    (minus rI.rI_base
      (opp0 (mult0 eta (sum_over_S0 (fun s0 -> mult0 (p s0) (a s0)))))
      (mult0 beta s1p))
    (id_trans
      (rI.rI_base.plus (rI.rI_base.plus x (opp0 (mult0 beta s1p)))
        (mult0 beta sp))
      (rI.rI_base.plus x
        (rI.rI_base.plus (opp0 (mult0 beta s1p)) (mult0 beta sp)))
      (plus0 x
        (mult0 beta
          (sum_over_S0 (fun s0 ->
            mult0 (p s0) (minus rI.rI_base (log0 (p s0)) (log0 (pi_t s0)))))))
      (id_sym
        (rI.rI_base.plus x
          (rI.rI_base.plus (opp0 (mult0 beta s1p)) (mult0 beta sp)))
        (rI.rI_base.plus (rI.rI_base.plus x (opp0 (mult0 beta s1p)))
          (mult0 beta sp))
        (rI.rI_base.plus_assoc x (opp0 (mult0 beta s1p)) (mult0 beta sp)))
      (id_trans
        (plus0 x (rI.rI_base.plus (opp0 (mult0 beta s1p)) (mult0 beta sp)))
        (plus0 x (rI.rI_base.plus (mult0 beta sp) (opp0 (mult0 beta s1p))))
        (plus0 x
          (mult0 beta
            (sum_over_S0 (fun s0 ->
              mult0 (p s0) (minus rI.rI_base (log0 (p s0)) (log0 (pi_t s0)))))))
        (id_cong (fun x0 -> plus0 x x0)
          (rI.rI_base.plus (opp0 (mult0 beta s1p)) (mult0 beta sp))
          (rI.rI_base.plus (mult0 beta sp) (opp0 (mult0 beta s1p)))
          (rI.rI_base.plus_comm (opp0 (mult0 beta s1p)) (mult0 beta sp)))
        (id_trans
          (plus0 x (minus rI.rI_base (mult0 beta sp) (mult0 beta s1p)))
          (plus0 x (mult0 beta (minus rI.rI_base sp s1p)))
          (plus0 x
            (mult0 beta
              (sum_over_S0 (fun s0 ->
                mult0 (p s0) (minus rI.rI_base (log0 (p s0)) (log0 (pi_t s0)))))))
          (id_cong (fun x0 -> plus0 x x0)
            (minus rI.rI_base (mult0 beta sp) (mult0 beta s1p))
            (mult0 beta (minus rI.rI_base sp s1p)) hlin)
          (id_cong (fun x0 -> plus0 x (mult0 beta x0))
            (minus rI.rI_base sp s1p)
            (sum_over_S0 (fun s0 ->
              mult0 (p s0) (minus rI.rI_base (log0 (p s0)) (log0 (pi_t s0)))))
            hkl))))
    hsum))

(** val f_t_decomp_p :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt)
    -> r id -> (s -> r) -> normalized -> r id **)

let f_t_decomp_p rI sS sO =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let log0 = rI.log in
  let exp_neg0 = rI.rI_base.exp_neg in
  (fun reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos _ p hp_norm ->
  let hext = fun s0 ->
    id_cong (fun x ->
      mult0
        (inv_pos0 (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
          (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos))
        x)
      (rI.rI_base.exp_neg
        (rI.rI_base.mult (rI.rI_base.inv_pos beta beta_pos)
          (energy_t rI sS reward beta pi_ref eta pi_t s0)))
      (mult0 (pi_t s0)
        (exp_neg0
          (opp0
            (mult0 (mult0 eta (inv_pos0 beta beta_pos))
              (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
      (boltzmann_factor_bridge rI sS reward beta beta_pos pi_ref eta pi_t
        pi_t_pos s0)
  in
  let hdec =
    free_energy_kl_decomp rI sS sO
      (energy_t rI sS reward beta pi_ref eta pi_t) beta beta_pos
      (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
      (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
        pi_t_pos)
      (z_rel_boltzmann_form rI sS sO reward beta beta_pos pi_ref eta pi_t
        pi_t_pos)
      p hp_norm
  in
  id_trans
    (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t) beta p)
    (rI.rI_base.plus
      (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t) beta
        (boltzmann_dist rI sS (energy_t rI sS reward beta pi_ref eta pi_t)
          beta beta_pos (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
          (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos)))
      (rI.rI_base.mult beta
        (sO.sum_over_S (fun s0 ->
          rI.rI_base.mult (p s0)
            (minus rI.rI_base (rI.log (p s0))
              (rI.log
                (boltzmann_dist rI sS
                  (energy_t rI sS reward beta pi_ref eta pi_t) beta beta_pos
                  (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
                  (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta
                    sum_over_S_pos pi_t pi_t_pos)
                  s0)))))))
    (plus0
      (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t) beta
        (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
          pi_t_pos))
      (mult0 beta
        (relative_entropy rI sS sO p
          (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos))))
    hdec
    (id_cong2 plus0
      (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t) beta
        (boltzmann_dist rI sS (energy_t rI sS reward beta pi_ref eta pi_t)
          beta beta_pos (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
          (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos)))
      (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t) beta
        (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
          pi_t_pos))
      (mult0 beta
        (sO.sum_over_S (fun s0 ->
          mult0 (p s0)
            (minus rI.rI_base (log0 (p s0))
              (log0
                (boltzmann_dist rI sS
                  (energy_t rI sS reward beta pi_ref eta pi_t) beta beta_pos
                  (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
                  (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta
                    sum_over_S_pos pi_t pi_t_pos)
                  s0))))))
      (mult0 beta
        (sO.sum_over_S (fun s0 ->
          mult0 (p s0)
            (minus rI.rI_base (log0 (p s0))
              (log0
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos s0))))))
      (free_energy_ext_t12 rI sS sO
        (energy_t rI sS reward beta pi_ref eta pi_t) beta
        (boltzmann_dist rI sS (energy_t rI sS reward beta pi_ref eta pi_t)
          beta beta_pos (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
          (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos))
        (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
          pi_t_pos)
        hext)
      (id_cong (fun x -> mult0 beta x)
        (sO.sum_over_S (fun s0 ->
          mult0 (p s0)
            (minus rI.rI_base (log0 (p s0))
              (log0
                (boltzmann_dist rI sS
                  (energy_t rI sS reward beta pi_ref eta pi_t) beta beta_pos
                  (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
                  (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta
                    sum_over_S_pos pi_t pi_t_pos)
                  s0)))))
        (sO.sum_over_S (fun s0 ->
          mult0 (p s0)
            (minus rI.rI_base (log0 (p s0))
              (log0
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos s0)))))
        (sO.sum_over_S_ext (fun s0 ->
          mult0 (p s0)
            (minus rI.rI_base (log0 (p s0))
              (log0
                (boltzmann_dist rI sS
                  (energy_t rI sS reward beta pi_ref eta pi_t) beta beta_pos
                  (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
                  (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta
                    sum_over_S_pos pi_t pi_t_pos)
                  s0))))
          (fun s0 ->
          mult0 (p s0)
            (minus rI.rI_base (log0 (p s0))
              (log0
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos s0))))
          (fun s0 ->
          id_cong (fun y -> mult0 (p s0) (minus rI.rI_base (log0 (p s0)) y))
            (log0
              (boltzmann_dist rI sS
                (energy_t rI sS reward beta pi_ref eta pi_t) beta beta_pos
                (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
                (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)
                s0))
            (log0
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos s0))
            (id_cong log0
              (boltzmann_dist rI sS
                (energy_t rI sS reward beta pi_ref eta pi_t) beta beta_pos
                (z_rel rI sS sO reward beta beta_pos pi_ref eta pi_t)
                (z_rel_pos rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)
                s0)
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos s0)
              (hext s0)))))))

(** val sum_grad_cross :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s -> lt)
    -> r id **)

let sum_grad_cross rI sS sO =
  let mult0 = rI.rI_base.mult in
  (fun reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos ->
  let np =
    pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
      pi_t_pos
  in
  let a = advantage_aug rI sS reward beta pi_ref pi_t in
  id_trans
    (minus rI.rI_base (sO.sum_over_S (fun s0 -> mult0 (np s0) (a s0)))
      (sO.sum_over_S (fun s0 -> mult0 (pi_t s0) (a s0))))
    (sO.sum_over_S (fun s0 ->
      minus rI.rI_base (mult0 (np s0) (a s0)) (mult0 (pi_t s0) (a s0))))
    (sO.sum_over_S (fun s0 ->
      rI.rI_base.mult (minus rI.rI_base (np s0) (pi_t s0)) (a s0)))
    (id_sym
      (sO.sum_over_S (fun s0 ->
        minus rI.rI_base (mult0 (np s0) (a s0)) (mult0 (pi_t s0) (a s0))))
      (minus rI.rI_base (sO.sum_over_S (fun s0 -> mult0 (np s0) (a s0)))
        (sO.sum_over_S (fun s0 -> mult0 (pi_t s0) (a s0))))
      (sum_over_S_minus rI sS sO (fun s0 -> mult0 (np s0) (a s0)) (fun s0 ->
        mult0 (pi_t s0) (a s0))))
    (sO.sum_over_S_ext (fun s0 ->
      minus rI.rI_base (rI.rI_base.mult (np s0) (a s0))
        (rI.rI_base.mult (pi_t s0) (a s0)))
      (fun s0 -> rI.rI_base.mult (minus rI.rI_base (np s0) (pi_t s0)) (a s0))
      (fun s0 ->
      id_sym (rI.rI_base.mult (minus rI.rI_base (np s0) (pi_t s0)) (a s0))
        (minus rI.rI_base (rI.rI_base.mult (np s0) (a s0))
          (rI.rI_base.mult (pi_t s0) (a s0)))
        (mult_minus_distr_r rI (np s0) (pi_t s0) (a s0)))))

(** val grad_cross_identity :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r -> lt -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s ->
    lt) -> r id -> (s -> lt) -> r id **)

let grad_cross_identity rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta beta_pos pi_ref eta eta_pos sum_over_S_pos pi_t pi_t_pos pi_t_norm pi_next_pos0 ->
  let np =
    pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
      pi_t_pos
  in
  let a = advantage_aug rI sS reward beta pi_ref pi_t in
  let xn = sum_over_S0 (fun s0 -> mult0 (np s0) (a s0)) in
  let xt = sum_over_S0 (fun s0 -> mult0 (pi_t s0) (a s0)) in
  let k1 = relative_entropy rI sS sO np pi_t in
  let k2 = relative_entropy rI sS sO pi_t np in
  let hsur =
    surrogate_diff_identity rI sS sO reward beta beta_pos pi_ref eta
      sum_over_S_pos pi_t pi_t_pos pi_t_norm pi_next_pos0
  in
  let hone =
    id_cong (fun x -> mult0 x (minus rI.rI_base xn xt))
      (rI.rI_base.mult (inv_pos0 eta eta_pos) eta) rI.rI_base.one
      (id_trans (rI.rI_base.mult (inv_pos0 eta eta_pos) eta)
        (rI.rI_base.mult eta (inv_pos0 eta eta_pos)) rI.rI_base.one
        (rI.rI_base.mult_comm (inv_pos0 eta eta_pos) eta)
        (rI.rI_base.inv_pos_correct eta eta_pos))
  in
  id_trans
    (sum_over_S0 (fun s0 ->
      mult0
        (minus rI.rI_base
          (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos s0)
          (pi_t s0))
        (advantage_aug rI sS reward beta pi_ref pi_t s0)))
    (minus rI.rI_base
      (sum_over_S0 (fun s0 ->
        mult0
          (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos s0)
          (advantage_aug rI sS reward beta pi_ref pi_t s0)))
      (sum_over_S0 (fun s0 ->
        mult0 (pi_t s0) (advantage_aug rI sS reward beta pi_ref pi_t s0))))
    (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 eta eta_pos) beta)
      (plus0 k1 k2))
    (id_sym
      (minus rI.rI_base
        (sum_over_S0 (fun s0 ->
          mult0
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos s0)
            (advantage_aug rI sS reward beta pi_ref pi_t s0)))
        (sum_over_S0 (fun s0 ->
          mult0 (pi_t s0) (advantage_aug rI sS reward beta pi_ref pi_t s0))))
      (sum_over_S0 (fun s0 ->
        mult0
          (minus rI.rI_base
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos s0)
            (pi_t s0))
          (advantage_aug rI sS reward beta pi_ref pi_t s0)))
      (sum_grad_cross rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
        pi_t pi_t_pos))
    (id_trans (minus rI.rI_base xn xt)
      (rI.rI_base.mult one0 (minus rI.rI_base xn xt))
      (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 eta eta_pos) beta)
        (plus0 k1 k2))
      (id_sym (rI.rI_base.mult one0 (minus rI.rI_base xn xt))
        (minus rI.rI_base xn xt)
        (id_trans (rI.rI_base.mult one0 (minus rI.rI_base xn xt))
          (rI.rI_base.mult (minus rI.rI_base xn xt) one0)
          (minus rI.rI_base xn xt)
          (rI.rI_base.mult_comm one0 (minus rI.rI_base xn xt))
          (rI.rI_base.mult_one (minus rI.rI_base xn xt))))
      (id_trans (mult0 one0 (minus rI.rI_base xn xt))
        (mult0 (mult0 (inv_pos0 eta eta_pos) eta) (minus rI.rI_base xn xt))
        (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 eta eta_pos) beta)
          (plus0 k1 k2))
        (id_sym
          (mult0 (mult0 (inv_pos0 eta eta_pos) eta) (minus rI.rI_base xn xt))
          (mult0 one0 (minus rI.rI_base xn xt)) hone)
        (id_trans
          (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 eta eta_pos) eta)
            (minus rI.rI_base xn xt))
          (rI.rI_base.mult (inv_pos0 eta eta_pos)
            (rI.rI_base.mult eta (minus rI.rI_base xn xt)))
          (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 eta eta_pos) beta)
            (plus0 k1 k2))
          (id_sym
            (rI.rI_base.mult (inv_pos0 eta eta_pos)
              (rI.rI_base.mult eta (minus rI.rI_base xn xt)))
            (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 eta eta_pos) eta)
              (minus rI.rI_base xn xt))
            (rI.rI_base.mult_assoc (inv_pos0 eta eta_pos) eta
              (minus rI.rI_base xn xt)))
          (id_trans
            (mult0 (inv_pos0 eta eta_pos)
              (mult0 eta
                (minus rI.rI_base
                  (sum_over_S0 (fun s0 ->
                    mult0
                      (pi_next rI sS sO reward beta beta_pos pi_ref eta
                        sum_over_S_pos pi_t pi_t_pos s0)
                      (advantage_aug rI sS reward beta pi_ref pi_t s0)))
                  (sum_over_S0 (fun s0 ->
                    mult0 (pi_t s0)
                      (advantage_aug rI sS reward beta pi_ref pi_t s0))))))
            (mult0 (inv_pos0 eta eta_pos)
              (mult0 beta
                (plus0
                  (relative_entropy rI sS sO
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos)
                    pi_t)
                  (relative_entropy rI sS sO pi_t
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos)))))
            (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 eta eta_pos) beta)
              (plus0 k1 k2))
            (id_cong (fun x -> mult0 (inv_pos0 eta eta_pos) x)
              (mult0 eta
                (minus rI.rI_base
                  (sum_over_S0 (fun s0 ->
                    mult0
                      (pi_next rI sS sO reward beta beta_pos pi_ref eta
                        sum_over_S_pos pi_t pi_t_pos s0)
                      (advantage_aug rI sS reward beta pi_ref pi_t s0)))
                  (sum_over_S0 (fun s0 ->
                    mult0 (pi_t s0)
                      (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
              (mult0 beta
                (plus0
                  (relative_entropy rI sS sO
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos)
                    pi_t)
                  (relative_entropy rI sS sO pi_t
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos))))
              hsur)
            (rI.rI_base.mult_assoc (inv_pos0 eta eta_pos) beta (plus0 k1 k2)))))))

(** val minus_sub_plus_t13 : realInterfaceEnhanced -> r -> r -> r -> r id **)

let minus_sub_plus_t13 rI =
  let plus0 = rI.rI_base.plus in
  let opp0 = rI.rI_base.opp in
  (fun a b c ->
  id_trans (plus0 a (rI.rI_base.opp (rI.rI_base.plus b c)))
    (plus0 a (rI.rI_base.plus (rI.rI_base.opp b) (rI.rI_base.opp c)))
    (rI.rI_base.plus (rI.rI_base.plus a (opp0 b)) (opp0 c))
    (id_cong (fun x -> plus0 a x) (rI.rI_base.opp (rI.rI_base.plus b c))
      (rI.rI_base.plus (rI.rI_base.opp b) (rI.rI_base.opp c))
      (opp_plus rI b c))
    (rI.rI_base.plus_assoc a (opp0 b) (opp0 c)))

(** val opp_minus_rev_t13 : realInterfaceEnhanced -> r -> r -> r id **)

let opp_minus_rev_t13 rI =
  let plus0 = rI.rI_base.plus in
  let opp0 = rI.rI_base.opp in
  (fun a b ->
  id_sym (rI.rI_base.opp (rI.rI_base.plus b (opp0 a)))
    (rI.rI_base.plus a (opp0 b))
    (id_trans (rI.rI_base.opp (rI.rI_base.plus b (opp0 a)))
      (rI.rI_base.plus (rI.rI_base.opp b) (rI.rI_base.opp (opp0 a)))
      (rI.rI_base.plus a (opp0 b)) (opp_plus rI b (opp0 a))
      (id_trans (plus0 (opp0 b) (rI.rI_base.opp (rI.rI_base.opp a)))
        (plus0 (opp0 b) a) (rI.rI_base.plus a (opp0 b))
        (id_cong (fun x -> plus0 (opp0 b) x)
          (rI.rI_base.opp (rI.rI_base.opp a)) a (double_neg rI a))
        (rI.rI_base.plus_comm (opp0 b) a))))

(** val sum_advance_gap :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> (s -> lt) -> lt -> r -> (s -> r) -> (s -> lt) -> r id -> r id **)

let sum_advance_gap rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta beta_pos pi_ref pi_ref_pos z_align_pos eta pi_t pi_t_pos pi_t_norm ->
  let a = advantage_aug rI sS reward beta pi_ref pi_t in
  let xs =
    sum_over_S0 (fun s0 ->
      mult0 (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
        (a s0))
  in
  let xt = sum_over_S0 (fun s0 -> mult0 (pi_t s0) (a s0)) in
  let hstar =
    let ht12 =
      align_objective_t12_decomp rI sS sO reward beta pi_ref eta pi_t
        (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
    in
    let hFp =
      f_t_simpl_p rI sS sO reward beta pi_ref eta pi_t
        (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
    in
    let hopp =
      id_trans
        (rI.rI_base.opp
          (rI.rI_base.plus
            (opp0
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0)))))
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t))))
        (rI.rI_base.plus
          (rI.rI_base.opp
            (opp0
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0))))))
          (rI.rI_base.opp
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t))))
        (plus0
          (mult0 eta
            (sum_over_S0 (fun s0 ->
              mult0
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
                (a s0))))
          (opp0
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t))))
        (opp_plus rI
          (opp0
            (mult0 eta
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (a s0)))))
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
        (id_cong (fun x ->
          plus0 x
            (opp0
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t))))
          (rI.rI_base.opp
            (rI.rI_base.opp
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0))))))
          (mult0 eta
            (sum_over_S0 (fun s0 ->
              mult0
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
                (a s0))))
          (double_neg rI
            (mult0 eta
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (a s0))))))
    in
    let hmid =
      id_cong2 plus0
        (opp0
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))
        (opp0
          (plus0
            (opp0
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t))))
        (mult0 (minus rI.rI_base one0 eta)
          (sum_over_S0 (fun s0 ->
            mult0
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
              (a s0))))
        (mult0 (minus rI.rI_base one0 eta)
          (sum_over_S0 (fun s0 ->
            mult0
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
              (a s0))))
        (id_cong opp0
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
          (plus0
            (opp0
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t)))
          hFp)
        Id_refl
    in
    let hfinal =
      id_trans
        (rI.rI_base.plus
          (rI.rI_base.plus
            (mult0 eta
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (a s0))))
            (opp0
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t))))
          (mult0 (minus rI.rI_base one0 eta)
            (sum_over_S0 (fun s0 ->
              mult0
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
                (a s0)))))
        (rI.rI_base.plus
          (mult0 eta
            (sum_over_S0 (fun s0 ->
              mult0
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
                (a s0))))
          (rI.rI_base.plus
            (opp0
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t)))
            (mult0 (minus rI.rI_base one0 eta)
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (a s0))))))
        (plus0
          (sum_over_S0 (fun s0 ->
            mult0
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
              (a s0)))
          (opp0
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t))))
        (id_sym
          (rI.rI_base.plus
            (mult0 eta
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (a s0))))
            (rI.rI_base.plus
              (opp0
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t)))
              (mult0 (minus rI.rI_base one0 eta)
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0))))))
          (rI.rI_base.plus
            (rI.rI_base.plus
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0))))
              (opp0
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))))
            (mult0 (minus rI.rI_base one0 eta)
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (a s0)))))
          (rI.rI_base.plus_assoc
            (mult0 eta
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (a s0))))
            (opp0
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t)))
            (mult0 (minus rI.rI_base one0 eta)
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (a s0))))))
        (id_trans
          (plus0
            (mult0 eta
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (a s0))))
            (rI.rI_base.plus
              (opp0
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t)))
              (mult0 (minus rI.rI_base one0 eta)
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0))))))
          (plus0
            (mult0 eta
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (a s0))))
            (rI.rI_base.plus
              (mult0 (minus rI.rI_base one0 eta)
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0))))
              (opp0
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t)))))
          (plus0
            (sum_over_S0 (fun s0 ->
              mult0
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
                (a s0)))
            (opp0
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t))))
          (id_cong (fun x ->
            plus0
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0))))
              x)
            (rI.rI_base.plus
              (opp0
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t)))
              (mult0 (minus rI.rI_base one0 eta)
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0)))))
            (rI.rI_base.plus
              (mult0 (minus rI.rI_base one0 eta)
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0))))
              (opp0
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))))
            (rI.rI_base.plus_comm
              (opp0
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t)))
              (mult0 (minus rI.rI_base one0 eta)
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0))))))
          (id_trans
            (rI.rI_base.plus
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0))))
              (rI.rI_base.plus
                (mult0 (minus rI.rI_base one0 eta)
                  (sum_over_S0 (fun s0 ->
                    mult0
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos s0)
                      (a s0))))
                (opp0
                  (mult0 beta
                    (relative_entropy rI sS sO
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)
                      pi_t)))))
            (rI.rI_base.plus
              (rI.rI_base.plus
                (mult0 eta
                  (sum_over_S0 (fun s0 ->
                    mult0
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos s0)
                      (a s0))))
                (mult0 (minus rI.rI_base one0 eta)
                  (sum_over_S0 (fun s0 ->
                    mult0
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos s0)
                      (a s0)))))
              (opp0
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))))
            (plus0
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (a s0)))
              (opp0
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))))
            (rI.rI_base.plus_assoc
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0))))
              (mult0 (minus rI.rI_base one0 eta)
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0))))
              (opp0
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))))
            (id_cong (fun x ->
              plus0 x
                (opp0
                  (mult0 beta
                    (relative_entropy rI sS sO
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)
                      pi_t))))
              (plus0
                (mult0 eta
                  (sum_over_S0 (fun s0 ->
                    mult0
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos s0)
                      (a s0))))
                (mult0 (minus rI.rI_base one0 eta)
                  (sum_over_S0 (fun s0 ->
                    mult0
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos s0)
                      (a s0)))))
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (a s0)))
              (eta_absorb_t12 rI eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0)))))))
    in
    id_trans
      (align_objective rI sS sO reward beta pi_ref
        (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
      (plus0
        (opp0
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))
        (mult0 (minus rI.rI_base one0 eta)
          (sum_over_S0 (fun s0 ->
            mult0
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
              (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
      (minus rI.rI_base
        (sum_over_S0 (fun s0 ->
          mult0 (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
            (a s0)))
        (mult0 beta
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
      ht12
      (id_trans
        (plus0
          (opp0
            (free_energy rI sS sO
              (energy_t rI sS reward beta pi_ref eta pi_t) beta
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))
          (mult0 (minus rI.rI_base one0 eta)
            (sum_over_S0 (fun s0 ->
              mult0
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
                (a s0)))))
        (plus0
          (opp0
            (plus0
              (opp0
                (mult0 eta
                  (sum_over_S0 (fun s0 ->
                    mult0
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos s0)
                      (a s0)))))
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t))))
          (mult0 (minus rI.rI_base one0 eta)
            (sum_over_S0 (fun s0 ->
              mult0
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
                (a s0)))))
        (plus0
          (sum_over_S0 (fun s0 ->
            mult0
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
              (a s0)))
          (opp0
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t))))
        hmid
        (id_trans
          (plus0
            (opp0
              (plus0
                (opp0
                  (mult0 eta
                    (sum_over_S0 (fun s0 ->
                      mult0
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos s0)
                        (a s0)))))
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))))
            (mult0 (minus rI.rI_base one0 eta)
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (a s0)))))
          (plus0
            (plus0
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0))))
              (opp0
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))))
            (mult0 (minus rI.rI_base one0 eta)
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (a s0)))))
          (plus0
            (sum_over_S0 (fun s0 ->
              mult0
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
                (a s0)))
            (opp0
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t))))
          (id_cong (fun x ->
            plus0 x
              (mult0 (minus rI.rI_base one0 eta)
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0)))))
            (opp0
              (plus0
                (opp0
                  (mult0 eta
                    (sum_over_S0 (fun s0 ->
                      mult0
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos s0)
                        (a s0)))))
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))))
            (plus0
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (a s0))))
              (opp0
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))))
            hopp)
          hfinal))
  in
  let hxs =
    id_trans xs
      (rI.rI_base.plus
        (minus rI.rI_base xs
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
        (mult0 beta
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
      (plus0
        (align_objective rI sS sO reward beta pi_ref
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
        (mult0 beta
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
      (id_sym
        (rI.rI_base.plus
          (minus rI.rI_base xs
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t)))
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
        xs
        (minus_plus_cancel_gap rI xs
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t))))
      (id_cong (fun x ->
        plus0 x
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
        (minus rI.rI_base xs
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
        (align_objective rI sS sO reward beta pi_ref
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
        (id_sym
          (align_objective rI sS sO reward beta pi_ref
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
          (minus rI.rI_base xs
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t)))
          hstar))
  in
  let hxt = j_pi_t_t12 rI sS sO reward beta pi_ref eta pi_t pi_t_norm in
  let hgap =
    rlhf_suboptimality_gap rI sS sO reward beta beta_pos pi_ref pi_ref_pos
      z_align_pos pi_t pi_t_norm pi_t_pos
  in
  id_trans (minus rI.rI_base xt xs)
    (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref pi_t)
      (plus0
        (align_objective rI sS sO reward beta pi_ref
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
        (mult0 beta
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t))))
    (minus rI.rI_base
      (opp0
        (mult0 beta
          (relative_entropy rI sS sO pi_t
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
      (mult0 beta
        (relative_entropy rI sS sO
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
    (id_cong2 (minus rI.rI_base) xt
      (align_objective rI sS sO reward beta pi_ref pi_t) xs
      (plus0
        (align_objective rI sS sO reward beta pi_ref
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
        (mult0 beta
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
      (id_sym (align_objective rI sS sO reward beta pi_ref pi_t) xt hxt) hxs)
    (id_trans
      (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref pi_t)
        (plus0
          (align_objective rI sS sO reward beta pi_ref
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t))))
      (minus rI.rI_base
        (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref pi_t)
          (align_objective rI sS sO reward beta pi_ref
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))
        (mult0 beta
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
      (minus rI.rI_base
        (opp0
          (mult0 beta
            (relative_entropy rI sS sO pi_t
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
        (mult0 beta
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
      (minus_sub_plus_t13 rI
        (align_objective rI sS sO reward beta pi_ref pi_t)
        (align_objective rI sS sO reward beta pi_ref
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
        (mult0 beta
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
      (id_trans
        (minus rI.rI_base
          (minus rI.rI_base
            (align_objective rI sS sO reward beta pi_ref pi_t)
            (align_objective rI sS sO reward beta pi_ref
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
        (minus rI.rI_base
          (opp0
            (minus rI.rI_base
              (align_objective rI sS sO reward beta pi_ref
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
              (align_objective rI sS sO reward beta pi_ref pi_t)))
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
        (minus rI.rI_base
          (opp0
            (mult0 beta
              (relative_entropy rI sS sO pi_t
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
        (id_cong (fun x ->
          minus rI.rI_base x
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t)))
          (minus rI.rI_base
            (align_objective rI sS sO reward beta pi_ref pi_t)
            (align_objective rI sS sO reward beta pi_ref
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))
          (opp0
            (minus rI.rI_base
              (align_objective rI sS sO reward beta pi_ref
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
              (align_objective rI sS sO reward beta pi_ref pi_t)))
          (opp_minus_rev_t13 rI
            (align_objective rI sS sO reward beta pi_ref pi_t)
            (align_objective rI sS sO reward beta pi_ref
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
        (id_trans
          (minus rI.rI_base
            (opp0
              (minus rI.rI_base
                (align_objective rI sS sO reward beta pi_ref
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
                (align_objective rI sS sO reward beta pi_ref pi_t)))
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t)))
          (minus rI.rI_base
            (opp0
              (mult0 beta
                (relative_entropy rI sS sO pi_t
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t)))
          (minus rI.rI_base
            (opp0
              (mult0 beta
                (relative_entropy rI sS sO pi_t
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t)))
          (id_cong (fun x ->
            minus rI.rI_base (opp0 x)
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t)))
            (minus rI.rI_base
              (align_objective rI sS sO reward beta pi_ref
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
              (align_objective rI sS sO reward beta pi_ref pi_t))
            (mult0 beta
              (relative_entropy rI sS sO pi_t
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))
            hgap)
          Id_refl))))

(** val minus_distr_t13 :
    realInterfaceEnhanced -> r -> r -> r -> r -> r id **)

let minus_distr_t13 rI =
  let plus0 = rI.rI_base.plus in
  let opp0 = rI.rI_base.opp in
  (fun a b c d ->
  let hmid =
    id_trans (rI.rI_base.plus b (rI.rI_base.plus (opp0 c) (opp0 d)))
      (rI.rI_base.plus (rI.rI_base.plus b (opp0 c)) (opp0 d))
      (rI.rI_base.plus (opp0 c) (rI.rI_base.plus b (opp0 d)))
      (rI.rI_base.plus_assoc b (opp0 c) (opp0 d))
      (id_trans (plus0 (rI.rI_base.plus b (opp0 c)) (opp0 d))
        (plus0 (rI.rI_base.plus (opp0 c) b) (opp0 d))
        (rI.rI_base.plus (opp0 c) (rI.rI_base.plus b (opp0 d)))
        (id_cong (fun x -> plus0 x (opp0 d)) (rI.rI_base.plus b (opp0 c))
          (rI.rI_base.plus (opp0 c) b) (rI.rI_base.plus_comm b (opp0 c)))
        (id_sym (rI.rI_base.plus (opp0 c) (rI.rI_base.plus b (opp0 d)))
          (rI.rI_base.plus (rI.rI_base.plus (opp0 c) b) (opp0 d))
          (rI.rI_base.plus_assoc (opp0 c) b (opp0 d))))
  in
  id_trans (plus0 (plus0 a b) (rI.rI_base.opp (rI.rI_base.plus c d)))
    (plus0 (plus0 a b)
      (rI.rI_base.plus (rI.rI_base.opp c) (rI.rI_base.opp d)))
    (rI.rI_base.plus (rI.rI_base.plus a (opp0 c)) (plus0 b (opp0 d)))
    (id_cong (fun x -> plus0 (plus0 a b) x)
      (rI.rI_base.opp (rI.rI_base.plus c d))
      (rI.rI_base.plus (rI.rI_base.opp c) (rI.rI_base.opp d))
      (opp_plus rI c d))
    (id_trans
      (rI.rI_base.plus (rI.rI_base.plus a b) (plus0 (opp0 c) (opp0 d)))
      (rI.rI_base.plus a (rI.rI_base.plus b (plus0 (opp0 c) (opp0 d))))
      (rI.rI_base.plus (rI.rI_base.plus a (opp0 c)) (plus0 b (opp0 d)))
      (id_sym
        (rI.rI_base.plus a (rI.rI_base.plus b (plus0 (opp0 c) (opp0 d))))
        (rI.rI_base.plus (rI.rI_base.plus a b) (plus0 (opp0 c) (opp0 d)))
        (rI.rI_base.plus_assoc a b (plus0 (opp0 c) (opp0 d))))
      (id_trans (plus0 a (plus0 b (plus0 (opp0 c) (opp0 d))))
        (plus0 a (plus0 (opp0 c) (plus0 b (opp0 d))))
        (rI.rI_base.plus (rI.rI_base.plus a (opp0 c)) (plus0 b (opp0 d)))
        (id_cong (fun x -> plus0 a x) (plus0 b (plus0 (opp0 c) (opp0 d)))
          (plus0 (opp0 c) (plus0 b (opp0 d))) hmid)
        (rI.rI_base.plus_assoc a (opp0 c) (plus0 b (opp0 d))))))

(** val minus_opp_opp_mult_t13 :
    realInterfaceEnhanced -> r -> r -> r -> r id **)

let minus_opp_opp_mult_t13 rI =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  (fun eta a b ->
  id_trans
    (plus0 (opp0 (mult0 eta a))
      (rI.rI_base.opp (rI.rI_base.opp (mult0 eta b))))
    (plus0 (opp0 (mult0 eta a)) (mult0 eta b))
    (rI.rI_base.mult eta (rI.rI_base.plus b (opp0 a)))
    (id_cong (fun x -> plus0 (opp0 (mult0 eta a)) x)
      (rI.rI_base.opp (rI.rI_base.opp (mult0 eta b))) (mult0 eta b)
      (double_neg rI (mult0 eta b)))
    (id_trans (rI.rI_base.plus (opp0 (mult0 eta a)) (mult0 eta b))
      (rI.rI_base.plus (mult0 eta b) (opp0 (mult0 eta a)))
      (rI.rI_base.mult eta (rI.rI_base.plus b (opp0 a)))
      (rI.rI_base.plus_comm (opp0 (mult0 eta a)) (mult0 eta b))
      (id_trans
        (plus0 (mult0 eta b) (rI.rI_base.opp (rI.rI_base.mult eta a)))
        (plus0 (mult0 eta b) (rI.rI_base.mult eta (rI.rI_base.opp a)))
        (rI.rI_base.mult eta (rI.rI_base.plus b (opp0 a)))
        (id_cong (fun x -> plus0 (mult0 eta b) x)
          (rI.rI_base.opp (rI.rI_base.mult eta a))
          (rI.rI_base.mult eta (rI.rI_base.opp a))
          (id_sym (rI.rI_base.mult eta (rI.rI_base.opp a))
            (rI.rI_base.opp (rI.rI_base.mult eta a)) (opp_mult_l rI eta a)))
        (id_sym (rI.rI_base.mult eta (rI.rI_base.plus b (opp0 a)))
          (rI.rI_base.plus (rI.rI_base.mult eta b)
            (rI.rI_base.mult eta (opp0 a)))
          (rI.rI_base.distrib eta b (opp0 a))))))

(** val t13_hexp :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> lt -> r -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s ->
    lt) -> r id -> r id **)

let t13_hexp rI sS sO =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta beta_pos pi_ref z_align_pos eta sum_over_S_pos pi_t pi_t_pos _ ->
  let np =
    pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
      pi_t_pos
  in
  let a = advantage_aug rI sS reward beta pi_ref pi_t in
  let xs =
    sum_over_S0 (fun s0 ->
      mult0 (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
        (a s0))
  in
  let xn = sum_over_S0 (fun s0 -> mult0 (np s0) (a s0)) in
  let k1 = relative_entropy rI sS sO np pi_t in
  let kst =
    relative_entropy rI sS sO
      (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t
  in
  id_trans
    (minus rI.rI_base (plus0 (opp0 (mult0 eta xs)) (mult0 beta kst))
      (plus0 (opp0 (mult0 eta xn)) (mult0 beta k1)))
    (plus0 (minus rI.rI_base (opp0 (mult0 eta xs)) (opp0 (mult0 eta xn)))
      (minus rI.rI_base (mult0 beta kst) (mult0 beta k1)))
    (plus0 (mult0 eta (minus rI.rI_base xn xs))
      (rI.rI_base.mult beta (minus rI.rI_base kst k1)))
    (minus_distr_t13 rI (opp0 (mult0 eta xs)) (mult0 beta kst)
      (opp0 (mult0 eta xn)) (mult0 beta k1))
    (id_cong2 plus0
      (minus rI.rI_base (opp0 (mult0 eta xs)) (opp0 (mult0 eta xn)))
      (mult0 eta (minus rI.rI_base xn xs))
      (minus rI.rI_base (rI.rI_base.mult beta kst) (rI.rI_base.mult beta k1))
      (rI.rI_base.mult beta (minus rI.rI_base kst k1))
      (minus_opp_opp_mult_t13 rI eta xs xn)
      (id_sym (rI.rI_base.mult beta (minus rI.rI_base kst k1))
        (minus rI.rI_base (rI.rI_base.mult beta kst)
          (rI.rI_base.mult beta k1))
        (mult_minus_distr_l rI beta kst k1))))

(** val minus_split_t13 : realInterfaceEnhanced -> r -> r -> r -> r id **)

let minus_split_t13 rI =
  let plus0 = rI.rI_base.plus in
  let opp0 = rI.rI_base.opp in
  (fun a b c ->
  id_trans (plus0 a (opp0 c))
    (plus0 (rI.rI_base.plus a rI.rI_base.zero) (opp0 c))
    (rI.rI_base.plus (plus0 a (opp0 b)) (rI.rI_base.plus b (opp0 c)))
    (id_sym (plus0 (rI.rI_base.plus a rI.rI_base.zero) (opp0 c))
      (plus0 a (opp0 c))
      (id_cong (fun x -> plus0 x (opp0 c))
        (rI.rI_base.plus a rI.rI_base.zero) a (rI.rI_base.plus_zero a)))
    (id_trans (plus0 (plus0 a rI.rI_base.zero) (opp0 c))
      (plus0 (plus0 a (rI.rI_base.plus (opp0 b) b)) (opp0 c))
      (rI.rI_base.plus (plus0 a (opp0 b)) (rI.rI_base.plus b (opp0 c)))
      (id_sym (plus0 (plus0 a (rI.rI_base.plus (opp0 b) b)) (opp0 c))
        (plus0 (plus0 a rI.rI_base.zero) (opp0 c))
        (id_cong (fun x -> plus0 (plus0 a x) (opp0 c))
          (rI.rI_base.plus (opp0 b) b) rI.rI_base.zero
          (id_trans (rI.rI_base.plus (opp0 b) b) (rI.rI_base.plus b (opp0 b))
            rI.rI_base.zero (rI.rI_base.plus_comm (opp0 b) b)
            (rI.rI_base.plus_opp b))))
      (id_trans
        (plus0 (rI.rI_base.plus a (rI.rI_base.plus (opp0 b) b)) (opp0 c))
        (plus0 (rI.rI_base.plus (rI.rI_base.plus a (opp0 b)) b) (opp0 c))
        (rI.rI_base.plus (plus0 a (opp0 b)) (rI.rI_base.plus b (opp0 c)))
        (id_sym
          (plus0 (rI.rI_base.plus (rI.rI_base.plus a (opp0 b)) b) (opp0 c))
          (plus0 (rI.rI_base.plus a (rI.rI_base.plus (opp0 b) b)) (opp0 c))
          (id_cong (fun x -> plus0 x (opp0 c))
            (rI.rI_base.plus (rI.rI_base.plus a (opp0 b)) b)
            (rI.rI_base.plus a (rI.rI_base.plus (opp0 b) b))
            (id_sym (rI.rI_base.plus a (rI.rI_base.plus (opp0 b) b))
              (rI.rI_base.plus (rI.rI_base.plus a (opp0 b)) b)
              (rI.rI_base.plus_assoc a (opp0 b) b))))
        (id_sym
          (rI.rI_base.plus (plus0 a (opp0 b)) (rI.rI_base.plus b (opp0 c)))
          (rI.rI_base.plus (rI.rI_base.plus (plus0 a (opp0 b)) b) (opp0 c))
          (rI.rI_base.plus_assoc (plus0 a (opp0 b)) b (opp0 c))))))

(** val minus_plus_cancel_gap_rev_t13 :
    realInterfaceEnhanced -> r -> r -> r id **)

let minus_plus_cancel_gap_rev_t13 rI =
  let plus0 = rI.rI_base.plus in
  let opp0 = rI.rI_base.opp in
  (fun a b ->
  id_trans (rI.rI_base.plus (rI.rI_base.plus a b) (opp0 b))
    (rI.rI_base.plus a (rI.rI_base.plus b (opp0 b))) a
    (id_sym (rI.rI_base.plus a (rI.rI_base.plus b (opp0 b)))
      (rI.rI_base.plus (rI.rI_base.plus a b) (opp0 b))
      (rI.rI_base.plus_assoc a b (opp0 b)))
    (id_trans (plus0 a (rI.rI_base.plus b (rI.rI_base.opp b)))
      (plus0 a rI.rI_base.zero) a
      (id_cong (fun x -> plus0 a x) (rI.rI_base.plus b (rI.rI_base.opp b))
        rI.rI_base.zero (rI.rI_base.plus_opp b))
      (rI.rI_base.plus_zero a)))

(** val t13_collapse :
    realInterfaceEnhanced -> r -> r -> r -> r -> r -> r id **)

let t13_collapse rI =
  let zero0 = rI.rI_base.zero in
  let plus0 = rI.rI_base.plus in
  let opp0 = rI.rI_base.opp in
  (fun a b c d e ->
  let x = plus0 (plus0 a b) (plus0 (opp0 c) (opp0 d)) in
  id_trans (rI.rI_base.plus x (rI.rI_base.plus e (opp0 a)))
    (rI.rI_base.plus e (rI.rI_base.plus x (opp0 a)))
    (rI.rI_base.plus (rI.rI_base.plus e (opp0 d)) (plus0 (opp0 c) b))
    (id_trans (rI.rI_base.plus x (rI.rI_base.plus e (opp0 a)))
      (rI.rI_base.plus (rI.rI_base.plus x e) (opp0 a))
      (rI.rI_base.plus e (rI.rI_base.plus x (opp0 a)))
      (rI.rI_base.plus_assoc x e (opp0 a))
      (id_trans (plus0 (rI.rI_base.plus x e) (opp0 a))
        (plus0 (rI.rI_base.plus e x) (opp0 a))
        (rI.rI_base.plus e (rI.rI_base.plus x (opp0 a)))
        (id_cong (fun x0 -> plus0 x0 (opp0 a)) (rI.rI_base.plus x e)
          (rI.rI_base.plus e x) (rI.rI_base.plus_comm x e))
        (id_sym (rI.rI_base.plus e (rI.rI_base.plus x (opp0 a)))
          (rI.rI_base.plus (rI.rI_base.plus e x) (opp0 a))
          (rI.rI_base.plus_assoc e x (opp0 a)))))
    (id_trans (plus0 e (rI.rI_base.plus x (opp0 a)))
      (plus0 e (rI.rI_base.plus (opp0 a) x))
      (rI.rI_base.plus (rI.rI_base.plus e (opp0 d)) (plus0 (opp0 c) b))
      (id_cong (fun x0 -> plus0 e x0) (rI.rI_base.plus x (opp0 a))
        (rI.rI_base.plus (opp0 a) x) (rI.rI_base.plus_comm x (opp0 a)))
      (id_trans
        (plus0 e
          (rI.rI_base.plus (opp0 a)
            (rI.rI_base.plus (plus0 a b) (plus0 (opp0 c) (opp0 d)))))
        (plus0 e
          (rI.rI_base.plus (rI.rI_base.plus (opp0 a) (plus0 a b))
            (plus0 (opp0 c) (opp0 d))))
        (rI.rI_base.plus (rI.rI_base.plus e (opp0 d)) (plus0 (opp0 c) b))
        (id_cong (fun x0 -> plus0 e x0)
          (rI.rI_base.plus (opp0 a)
            (rI.rI_base.plus (plus0 a b) (plus0 (opp0 c) (opp0 d))))
          (rI.rI_base.plus (rI.rI_base.plus (opp0 a) (plus0 a b))
            (plus0 (opp0 c) (opp0 d)))
          (rI.rI_base.plus_assoc (opp0 a) (plus0 a b)
            (plus0 (opp0 c) (opp0 d))))
        (id_trans
          (plus0 e
            (plus0 (rI.rI_base.plus (opp0 a) (rI.rI_base.plus a b))
              (plus0 (opp0 c) (opp0 d))))
          (plus0 e
            (plus0 (rI.rI_base.plus (rI.rI_base.plus (opp0 a) a) b)
              (plus0 (opp0 c) (opp0 d))))
          (rI.rI_base.plus (rI.rI_base.plus e (opp0 d)) (plus0 (opp0 c) b))
          (id_cong (fun x0 -> plus0 e x0)
            (plus0 (rI.rI_base.plus (opp0 a) (rI.rI_base.plus a b))
              (plus0 (opp0 c) (opp0 d)))
            (plus0 (rI.rI_base.plus (rI.rI_base.plus (opp0 a) a) b)
              (plus0 (opp0 c) (opp0 d)))
            (id_cong (fun x0 -> plus0 x0 (plus0 (opp0 c) (opp0 d)))
              (rI.rI_base.plus (opp0 a) (rI.rI_base.plus a b))
              (rI.rI_base.plus (rI.rI_base.plus (opp0 a) a) b)
              (rI.rI_base.plus_assoc (opp0 a) a b)))
          (id_trans
            (plus0 e
              (plus0 (plus0 (rI.rI_base.plus (opp0 a) a) b)
                (plus0 (opp0 c) (opp0 d))))
            (plus0 e
              (plus0 (plus0 rI.rI_base.zero b) (plus0 (opp0 c) (opp0 d))))
            (rI.rI_base.plus (rI.rI_base.plus e (opp0 d)) (plus0 (opp0 c) b))
            (id_cong (fun x0 -> plus0 e x0)
              (plus0 (plus0 (rI.rI_base.plus (opp0 a) a) b)
                (plus0 (opp0 c) (opp0 d)))
              (plus0 (plus0 rI.rI_base.zero b) (plus0 (opp0 c) (opp0 d)))
              (id_cong (fun x0 ->
                plus0 (plus0 x0 b) (plus0 (opp0 c) (opp0 d)))
                (rI.rI_base.plus (opp0 a) a) rI.rI_base.zero
                (id_trans (rI.rI_base.plus (opp0 a) a)
                  (rI.rI_base.plus a (opp0 a)) rI.rI_base.zero
                  (rI.rI_base.plus_comm (opp0 a) a) (rI.rI_base.plus_opp a))))
            (id_trans
              (plus0 e
                (plus0 (rI.rI_base.plus zero0 b) (plus0 (opp0 c) (opp0 d))))
              (plus0 e (plus0 b (plus0 (opp0 c) (opp0 d))))
              (rI.rI_base.plus (rI.rI_base.plus e (opp0 d))
                (plus0 (opp0 c) b))
              (id_cong (fun x0 -> plus0 e x0)
                (plus0 (rI.rI_base.plus zero0 b) (plus0 (opp0 c) (opp0 d)))
                (plus0 b (plus0 (opp0 c) (opp0 d)))
                (id_cong (fun x0 -> plus0 x0 (plus0 (opp0 c) (opp0 d)))
                  (rI.rI_base.plus zero0 b) b
                  (id_trans (rI.rI_base.plus zero0 b)
                    (rI.rI_base.plus b zero0) b
                    (rI.rI_base.plus_comm zero0 b) (rI.rI_base.plus_zero b))))
              (id_trans
                (plus0 e
                  (rI.rI_base.plus b (rI.rI_base.plus (opp0 c) (opp0 d))))
                (plus0 e (plus0 (opp0 d) (rI.rI_base.plus (opp0 c) b)))
                (rI.rI_base.plus (rI.rI_base.plus e (opp0 d))
                  (plus0 (opp0 c) b))
                (id_cong (fun x0 -> plus0 e x0)
                  (rI.rI_base.plus b (rI.rI_base.plus (opp0 c) (opp0 d)))
                  (plus0 (opp0 d) (rI.rI_base.plus (opp0 c) b))
                  (id_trans
                    (rI.rI_base.plus b (rI.rI_base.plus (opp0 c) (opp0 d)))
                    (rI.rI_base.plus (rI.rI_base.plus b (opp0 c)) (opp0 d))
                    (plus0 (opp0 d) (rI.rI_base.plus (opp0 c) b))
                    (rI.rI_base.plus_assoc b (opp0 c) (opp0 d))
                    (id_trans (rI.rI_base.plus (plus0 b (opp0 c)) (opp0 d))
                      (rI.rI_base.plus (opp0 d) (plus0 b (opp0 c)))
                      (plus0 (opp0 d) (rI.rI_base.plus (opp0 c) b))
                      (rI.rI_base.plus_comm (plus0 b (opp0 c)) (opp0 d))
                      (id_cong (fun x0 -> plus0 (opp0 d) x0)
                        (rI.rI_base.plus b (opp0 c))
                        (rI.rI_base.plus (opp0 c) b)
                        (rI.rI_base.plus_comm b (opp0 c))))))
                (rI.rI_base.plus_assoc e (opp0 d) (plus0 (opp0 c) b)))))))))

(** val policy_iter_backward_kl_step_beta :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> (s -> lt) -> lt -> r -> lt -> ((s -> r) -> (s -> lt) -> lt)
    -> (s -> r) -> (s -> lt) -> r id -> (s -> lt) -> r id **)

let policy_iter_backward_kl_step_beta rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta beta_pos pi_ref pi_ref_pos z_align_pos eta eta_pos sum_over_S_pos pi_t pi_t_pos pi_t_norm pi_next_pos0 ->
  let np =
    pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
      pi_t_pos
  in
  let a = advantage_aug rI sS reward beta pi_ref pi_t in
  let xs =
    sum_over_S0 (fun s0 ->
      mult0 (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
        (a s0))
  in
  let xt = sum_over_S0 (fun s0 -> mult0 (pi_t s0) (a s0)) in
  let xn = sum_over_S0 (fun s0 -> mult0 (np s0) (a s0)) in
  let k1 = relative_entropy rI sS sO np pi_t in
  let k2 = relative_entropy rI sS sO pi_t np in
  let kst =
    relative_entropy rI sS sO
      (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t
  in
  let kts =
    relative_entropy rI sS sO pi_t
      (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
  in
  let ksn =
    relative_entropy rI sS sO
      (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) np
  in
  let hdec =
    f_t_decomp_p rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
      pi_t_pos pi_t_norm
      (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
      (pi_star_normalized rI sS sO reward beta beta_pos pi_ref z_align_pos)
  in
  let hFp =
    f_t_simpl_p rI sS sO reward beta pi_ref eta pi_t
      (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
  in
  let hFn =
    f_t_simpl_next_kl rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
      pi_t pi_t_pos
  in
  let hkl0 =
    id_trans
      (minus rI.rI_base
        (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
          beta (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
        (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
          beta np))
      (minus rI.rI_base
        (plus0
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos))
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos))))
        (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
          beta np))
      (mult0 beta ksn)
      (id_cong (fun x ->
        minus rI.rI_base x
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta np))
        (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
          beta (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
        (plus0
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos))
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos))))
        hdec)
      (id_trans
        (minus rI.rI_base
          (rI.rI_base.plus
            (free_energy rI sS sO
              (energy_t rI sS reward beta pi_ref eta pi_t) beta np)
            (mult0 beta ksn))
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta np))
        (minus rI.rI_base
          (rI.rI_base.plus (mult0 beta ksn)
            (free_energy rI sS sO
              (energy_t rI sS reward beta pi_ref eta pi_t) beta np))
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta np))
        (mult0 beta ksn)
        (id_cong (fun x ->
          minus rI.rI_base x
            (free_energy rI sS sO
              (energy_t rI sS reward beta pi_ref eta pi_t) beta np))
          (rI.rI_base.plus
            (free_energy rI sS sO
              (energy_t rI sS reward beta pi_ref eta pi_t) beta np)
            (mult0 beta ksn))
          (rI.rI_base.plus (mult0 beta ksn)
            (free_energy rI sS sO
              (energy_t rI sS reward beta pi_ref eta pi_t) beta np))
          (rI.rI_base.plus_comm
            (free_energy rI sS sO
              (energy_t rI sS reward beta pi_ref eta pi_t) beta np)
            (mult0 beta ksn)))
        (minus_plus_cancel_gap_rev_t13 rI (mult0 beta ksn)
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta np)))
  in
  let hkl1 =
    id_trans
      (minus rI.rI_base
        (plus0
          (opp0
            (mult0 eta
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
        (plus0 (opp0 (mult0 eta xn)) (mult0 beta k1)))
      (minus rI.rI_base
        (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
          beta (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
        (plus0 (opp0 (mult0 eta xn)) (mult0 beta k1)))
      (mult0 beta ksn)
      (id_cong (fun x ->
        minus rI.rI_base x (plus0 (opp0 (mult0 eta xn)) (mult0 beta k1)))
        (plus0
          (opp0
            (mult0 eta
              (sum_over_S0 (fun s0 ->
                mult0
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                    s0)
                  (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
        (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
          beta (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
        (id_sym
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
          (plus0
            (opp0
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos
                      s0)
                    (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t)))
          hFp))
      (id_trans
        (minus rI.rI_base
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
          (plus0
            (opp0
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos s0)
                    (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)
                pi_t))))
        (minus rI.rI_base
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos)))
        (mult0 beta ksn)
        (id_cong (fun x ->
          minus rI.rI_base
            (free_energy rI sS sO
              (energy_t rI sS reward beta pi_ref eta pi_t) beta
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))
            x)
          (plus0
            (opp0
              (mult0 eta
                (sum_over_S0 (fun s0 ->
                  mult0
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos s0)
                    (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)
                pi_t)))
          (free_energy rI sS sO (energy_t rI sS reward beta pi_ref eta pi_t)
            beta
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos))
          (id_sym
            (free_energy rI sS sO
              (energy_t rI sS reward beta pi_ref eta pi_t) beta
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos))
            (plus0
              (opp0
                (mult0 eta
                  (sum_over_S0 (fun s0 ->
                    mult0
                      (pi_next rI sS sO reward beta beta_pos pi_ref eta
                        sum_over_S_pos pi_t pi_t_pos s0)
                      (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_next rI sS sO reward beta beta_pos pi_ref eta
                    sum_over_S_pos pi_t pi_t_pos)
                  pi_t)))
            hFn))
        hkl0)
  in
  let hhexp =
    t13_hexp rI sS sO reward beta beta_pos pi_ref z_align_pos eta
      sum_over_S_pos pi_t pi_t_pos pi_t_norm
  in
  let hmain0 =
    id_trans (mult0 beta ksn)
      (minus rI.rI_base (plus0 (opp0 (mult0 eta xs)) (mult0 beta kst))
        (plus0 (opp0 (mult0 eta xn)) (mult0 beta k1)))
      (plus0
        (mult0 eta
          (minus rI.rI_base
            (sum_over_S0 (fun s0 ->
              mult0
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos s0)
                (advantage_aug rI sS reward beta pi_ref pi_t s0)))
            (sum_over_S0 (fun s0 ->
              mult0
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
                (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
        (mult0 beta
          (minus rI.rI_base
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)
            (relative_entropy rI sS sO
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos)
              pi_t))))
      (id_sym
        (minus rI.rI_base (plus0 (opp0 (mult0 eta xs)) (mult0 beta kst))
          (plus0 (opp0 (mult0 eta xn)) (mult0 beta k1)))
        (mult0 beta ksn) hkl1)
      hhexp
  in
  let heta1 =
    id_trans
      (mult0 eta
        (minus rI.rI_base
          (sum_over_S0 (fun s0 ->
            mult0
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos s0)
              (advantage_aug rI sS reward beta pi_ref pi_t s0)))
          (sum_over_S0 (fun s0 ->
            mult0 (pi_t s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
      (mult0 eta
        (sum_over_S0 (fun s0 ->
          mult0
            (minus rI.rI_base
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos s0)
              (pi_t s0))
            (advantage_aug rI sS reward beta pi_ref pi_t s0))))
      (mult0 beta (plus0 k1 k2))
      (id_cong (fun x -> mult0 eta x)
        (minus rI.rI_base
          (sum_over_S0 (fun s0 ->
            mult0
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos s0)
              (advantage_aug rI sS reward beta pi_ref pi_t s0)))
          (sum_over_S0 (fun s0 ->
            mult0 (pi_t s0) (advantage_aug rI sS reward beta pi_ref pi_t s0))))
        (sum_over_S0 (fun s0 ->
          mult0
            (minus rI.rI_base
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos s0)
              (pi_t s0))
            (advantage_aug rI sS reward beta pi_ref pi_t s0)))
        (sum_grad_cross rI sS sO reward beta beta_pos pi_ref eta
          sum_over_S_pos pi_t pi_t_pos))
      (id_trans
        (mult0 eta
          (sum_over_S0 (fun s0 ->
            mult0
              (minus rI.rI_base
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos s0)
                (pi_t s0))
              (advantage_aug rI sS reward beta pi_ref pi_t s0))))
        (mult0 eta
          (mult0 (mult0 (inv_pos0 eta eta_pos) beta)
            (plus0
              (relative_entropy rI sS sO
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)
                pi_t)
              (relative_entropy rI sS sO pi_t
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)))))
        (mult0 beta (plus0 k1 k2))
        (id_cong (fun x -> mult0 eta x)
          (sum_over_S0 (fun s0 ->
            mult0
              (minus rI.rI_base
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos s0)
                (pi_t s0))
              (advantage_aug rI sS reward beta pi_ref pi_t s0)))
          (mult0 (mult0 (inv_pos0 eta eta_pos) beta)
            (plus0
              (relative_entropy rI sS sO
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)
                pi_t)
              (relative_entropy rI sS sO pi_t
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos))))
          (grad_cross_identity rI sS sO reward beta beta_pos pi_ref eta
            eta_pos sum_over_S_pos pi_t pi_t_pos pi_t_norm pi_next_pos0))
        (id_trans
          (rI.rI_base.mult eta
            (rI.rI_base.mult (mult0 (inv_pos0 eta eta_pos) beta)
              (plus0 k1 k2)))
          (rI.rI_base.mult
            (rI.rI_base.mult eta (mult0 (inv_pos0 eta eta_pos) beta))
            (plus0 k1 k2))
          (mult0 beta (plus0 k1 k2))
          (rI.rI_base.mult_assoc eta (mult0 (inv_pos0 eta eta_pos) beta)
            (plus0 k1 k2))
          (id_trans
            (mult0
              (rI.rI_base.mult eta
                (rI.rI_base.mult (inv_pos0 eta eta_pos) beta))
              (plus0 k1 k2))
            (mult0
              (rI.rI_base.mult (rI.rI_base.mult eta (inv_pos0 eta eta_pos))
                beta)
              (plus0 k1 k2))
            (mult0 beta (plus0 k1 k2))
            (id_cong (fun x -> mult0 x (plus0 k1 k2))
              (rI.rI_base.mult eta
                (rI.rI_base.mult (inv_pos0 eta eta_pos) beta))
              (rI.rI_base.mult (rI.rI_base.mult eta (inv_pos0 eta eta_pos))
                beta)
              (rI.rI_base.mult_assoc eta (inv_pos0 eta eta_pos) beta))
            (id_trans
              (mult0
                (mult0 (rI.rI_base.mult eta (rI.rI_base.inv_pos eta eta_pos))
                  beta)
                (plus0 k1 k2))
              (mult0 (mult0 rI.rI_base.one beta) (plus0 k1 k2))
              (mult0 beta (plus0 k1 k2))
              (id_cong (fun x -> mult0 x (plus0 k1 k2))
                (mult0 (rI.rI_base.mult eta (rI.rI_base.inv_pos eta eta_pos))
                  beta)
                (mult0 rI.rI_base.one beta)
                (id_cong (fun x -> mult0 x beta)
                  (rI.rI_base.mult eta (rI.rI_base.inv_pos eta eta_pos))
                  rI.rI_base.one (rI.rI_base.inv_pos_correct eta eta_pos)))
              (id_cong (fun x -> mult0 x (plus0 k1 k2))
                (rI.rI_base.mult one0 beta) beta
                (id_trans (rI.rI_base.mult one0 beta)
                  (rI.rI_base.mult beta one0) beta
                  (rI.rI_base.mult_comm one0 beta) (rI.rI_base.mult_one beta)))))))
  in
  let heta2 =
    id_trans
      (mult0 eta
        (minus rI.rI_base
          (sum_over_S0 (fun s0 ->
            mult0 (pi_t s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))
          (sum_over_S0 (fun s0 ->
            mult0
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
              (advantage_aug rI sS reward beta pi_ref pi_t s0)))))
      (mult0 eta
        (plus0
          (opp0
            (mult0 beta
              (relative_entropy rI sS sO pi_t
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
          (opp0
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t)))))
      (plus0 (rI.rI_base.opp (rI.rI_base.mult eta (mult0 beta kts)))
        (rI.rI_base.opp (rI.rI_base.mult eta (mult0 beta kst))))
      (id_cong (fun x -> mult0 eta x)
        (minus rI.rI_base
          (sum_over_S0 (fun s0 ->
            mult0 (pi_t s0) (advantage_aug rI sS reward beta pi_ref pi_t s0)))
          (sum_over_S0 (fun s0 ->
            mult0
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
              (advantage_aug rI sS reward beta pi_ref pi_t s0))))
        (plus0
          (opp0
            (mult0 beta
              (relative_entropy rI sS sO pi_t
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
          (opp0
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t))))
        (sum_advance_gap rI sS sO reward beta beta_pos pi_ref pi_ref_pos
          z_align_pos eta pi_t pi_t_pos pi_t_norm))
      (id_trans
        (rI.rI_base.mult eta
          (rI.rI_base.plus (opp0 (mult0 beta kts)) (opp0 (mult0 beta kst))))
        (rI.rI_base.plus (rI.rI_base.mult eta (opp0 (mult0 beta kts)))
          (rI.rI_base.mult eta (opp0 (mult0 beta kst))))
        (plus0 (rI.rI_base.opp (rI.rI_base.mult eta (mult0 beta kts)))
          (rI.rI_base.opp (rI.rI_base.mult eta (mult0 beta kst))))
        (rI.rI_base.distrib eta (opp0 (mult0 beta kts))
          (opp0 (mult0 beta kst)))
        (id_cong2 plus0
          (rI.rI_base.mult eta (rI.rI_base.opp (mult0 beta kts)))
          (rI.rI_base.opp (rI.rI_base.mult eta (mult0 beta kts)))
          (rI.rI_base.mult eta (rI.rI_base.opp (mult0 beta kst)))
          (rI.rI_base.opp (rI.rI_base.mult eta (mult0 beta kst)))
          (opp_mult_l rI eta (mult0 beta kts))
          (opp_mult_l rI eta (mult0 beta kst))))
  in
  let hsplit =
    minus_split_t13 rI (sum_over_S0 (fun s0 -> mult0 (np s0) (a s0)))
      (sum_over_S0 (fun s0 -> mult0 (pi_t s0) (a s0)))
      (sum_over_S0 (fun s0 ->
        mult0 (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos s0)
          (a s0)))
  in
  let heta3 =
    id_trans (mult0 eta (minus rI.rI_base xn xs))
      (mult0 eta (plus0 (minus rI.rI_base xn xt) (minus rI.rI_base xt xs)))
      (rI.rI_base.plus (rI.rI_base.mult eta (minus rI.rI_base xn xt))
        (rI.rI_base.mult eta (minus rI.rI_base xt xs)))
      (id_cong (fun x -> mult0 eta x) (minus rI.rI_base xn xs)
        (plus0 (minus rI.rI_base xn xt) (minus rI.rI_base xt xs)) hsplit)
      (rI.rI_base.distrib eta (minus rI.rI_base xn xt)
        (minus rI.rI_base xt xs))
  in
  let hmid =
    id_trans (mult0 beta ksn)
      (plus0 (mult0 eta (minus rI.rI_base xn xs))
        (mult0 beta (minus rI.rI_base kst k1)))
      (plus0
        (plus0 (mult0 beta (plus0 k1 k2))
          (plus0 (opp0 (mult0 eta (mult0 beta kts)))
            (opp0 (mult0 eta (mult0 beta kst)))))
        (minus rI.rI_base (rI.rI_base.mult beta kst)
          (rI.rI_base.mult beta k1)))
      hmain0
      (id_trans
        (plus0 (mult0 eta (minus rI.rI_base xn xs))
          (mult0 beta (minus rI.rI_base kst k1)))
        (plus0
          (plus0 (mult0 eta (minus rI.rI_base xn xt))
            (mult0 eta (minus rI.rI_base xt xs)))
          (mult0 beta (minus rI.rI_base kst k1)))
        (plus0
          (plus0 (mult0 beta (plus0 k1 k2))
            (plus0 (opp0 (mult0 eta (mult0 beta kts)))
              (opp0 (mult0 eta (mult0 beta kst)))))
          (minus rI.rI_base (rI.rI_base.mult beta kst)
            (rI.rI_base.mult beta k1)))
        (id_cong (fun x -> plus0 x (mult0 beta (minus rI.rI_base kst k1)))
          (mult0 eta (minus rI.rI_base xn xs))
          (plus0 (mult0 eta (minus rI.rI_base xn xt))
            (mult0 eta (minus rI.rI_base xt xs)))
          heta3)
        (id_trans
          (plus0
            (plus0 (mult0 eta (minus rI.rI_base xn xt))
              (mult0 eta (minus rI.rI_base xt xs)))
            (mult0 beta (minus rI.rI_base kst k1)))
          (plus0
            (plus0 (mult0 beta (plus0 k1 k2))
              (mult0 eta (minus rI.rI_base xt xs)))
            (mult0 beta (minus rI.rI_base kst k1)))
          (plus0
            (plus0 (mult0 beta (plus0 k1 k2))
              (plus0 (opp0 (mult0 eta (mult0 beta kts)))
                (opp0 (mult0 eta (mult0 beta kst)))))
            (minus rI.rI_base (rI.rI_base.mult beta kst)
              (rI.rI_base.mult beta k1)))
          (id_cong (fun x ->
            plus0 (plus0 x (mult0 eta (minus rI.rI_base xt xs)))
              (mult0 beta (minus rI.rI_base kst k1)))
            (mult0 eta (minus rI.rI_base xn xt)) (mult0 beta (plus0 k1 k2))
            heta1)
          (id_trans
            (plus0
              (plus0 (mult0 beta (plus0 k1 k2))
                (mult0 eta (minus rI.rI_base xt xs)))
              (mult0 beta (minus rI.rI_base kst k1)))
            (plus0
              (plus0 (mult0 beta (plus0 k1 k2))
                (plus0 (opp0 (mult0 eta (mult0 beta kts)))
                  (opp0 (mult0 eta (mult0 beta kst)))))
              (mult0 beta (minus rI.rI_base kst k1)))
            (plus0
              (plus0 (mult0 beta (plus0 k1 k2))
                (plus0 (opp0 (mult0 eta (mult0 beta kts)))
                  (opp0 (mult0 eta (mult0 beta kst)))))
              (minus rI.rI_base (rI.rI_base.mult beta kst)
                (rI.rI_base.mult beta k1)))
            (id_cong (fun x ->
              plus0 (plus0 (mult0 beta (plus0 k1 k2)) x)
                (mult0 beta (minus rI.rI_base kst k1)))
              (mult0 eta (minus rI.rI_base xt xs))
              (plus0 (opp0 (mult0 eta (mult0 beta kts)))
                (opp0 (mult0 eta (mult0 beta kst))))
              heta2)
            (id_cong (fun x ->
              plus0
                (plus0 (mult0 beta (plus0 k1 k2))
                  (plus0 (opp0 (mult0 eta (mult0 beta kts)))
                    (opp0 (mult0 eta (mult0 beta kst)))))
                x)
              (rI.rI_base.mult beta (minus rI.rI_base kst k1))
              (minus rI.rI_base (rI.rI_base.mult beta kst)
                (rI.rI_base.mult beta k1))
              (mult_minus_distr_l rI beta kst k1)))))
  in
  let hdistr = rI.rI_base.distrib beta k1 k2 in
  let hone =
    id_trans (minus rI.rI_base (mult0 beta kst) (mult0 eta (mult0 beta kst)))
      (minus rI.rI_base (rI.rI_base.mult (mult0 beta kst) rI.rI_base.one)
        (mult0 eta (mult0 beta kst)))
      (rI.rI_base.mult (minus rI.rI_base one0 eta) (mult0 beta kst))
      (id_sym
        (minus rI.rI_base (rI.rI_base.mult (mult0 beta kst) rI.rI_base.one)
          (mult0 eta (mult0 beta kst)))
        (minus rI.rI_base (mult0 beta kst) (mult0 eta (mult0 beta kst)))
        (id_cong (fun x -> minus rI.rI_base x (mult0 eta (mult0 beta kst)))
          (rI.rI_base.mult (mult0 beta kst) rI.rI_base.one) (mult0 beta kst)
          (rI.rI_base.mult_one (mult0 beta kst))))
      (id_trans
        (minus rI.rI_base (rI.rI_base.mult (mult0 beta kst) one0)
          (mult0 eta (mult0 beta kst)))
        (minus rI.rI_base (rI.rI_base.mult one0 (mult0 beta kst))
          (mult0 eta (mult0 beta kst)))
        (rI.rI_base.mult (minus rI.rI_base one0 eta) (mult0 beta kst))
        (id_sym
          (minus rI.rI_base (rI.rI_base.mult one0 (mult0 beta kst))
            (mult0 eta (mult0 beta kst)))
          (minus rI.rI_base (rI.rI_base.mult (mult0 beta kst) one0)
            (mult0 eta (mult0 beta kst)))
          (id_cong (fun x -> minus rI.rI_base x (mult0 eta (mult0 beta kst)))
            (rI.rI_base.mult one0 (mult0 beta kst))
            (rI.rI_base.mult (mult0 beta kst) one0)
            (rI.rI_base.mult_comm one0 (mult0 beta kst))))
        (id_sym
          (rI.rI_base.mult (minus rI.rI_base one0 eta) (mult0 beta kst))
          (minus rI.rI_base (rI.rI_base.mult one0 (mult0 beta kst))
            (rI.rI_base.mult eta (mult0 beta kst)))
          (mult_minus_distr_r rI one0 eta (mult0 beta kst))))
  in
  id_trans (mult0 beta ksn)
    (plus0
      (plus0 (mult0 beta (plus0 k1 k2))
        (plus0 (opp0 (mult0 eta (mult0 beta kts)))
          (opp0 (mult0 eta (mult0 beta kst)))))
      (minus rI.rI_base (mult0 beta kst) (mult0 beta k1)))
    (plus0 (mult0 (minus rI.rI_base one0 eta) (mult0 beta kst))
      (plus0 (opp0 (mult0 eta (mult0 beta kts))) (mult0 beta k2)))
    hmid
    (id_trans
      (plus0
        (plus0 (mult0 beta (plus0 k1 k2))
          (plus0 (opp0 (mult0 eta (mult0 beta kts)))
            (opp0 (mult0 eta (mult0 beta kst)))))
        (minus rI.rI_base (mult0 beta kst) (mult0 beta k1)))
      (plus0
        (plus0 (plus0 (mult0 beta k1) (mult0 beta k2))
          (plus0 (opp0 (mult0 eta (mult0 beta kts)))
            (opp0 (mult0 eta (mult0 beta kst)))))
        (minus rI.rI_base (mult0 beta kst) (mult0 beta k1)))
      (plus0 (mult0 (minus rI.rI_base one0 eta) (mult0 beta kst))
        (plus0 (opp0 (mult0 eta (mult0 beta kts))) (mult0 beta k2)))
      (id_cong (fun x ->
        plus0
          (plus0 x
            (plus0 (opp0 (mult0 eta (mult0 beta kts)))
              (opp0 (mult0 eta (mult0 beta kst)))))
          (minus rI.rI_base (mult0 beta kst) (mult0 beta k1)))
        (mult0 beta (plus0 k1 k2)) (plus0 (mult0 beta k1) (mult0 beta k2))
        hdistr)
      (id_trans
        (plus0
          (plus0 (plus0 (mult0 beta k1) (mult0 beta k2))
            (plus0 (opp0 (mult0 eta (mult0 beta kts)))
              (opp0 (mult0 eta (mult0 beta kst)))))
          (minus rI.rI_base (mult0 beta kst) (mult0 beta k1)))
        (plus0
          (minus rI.rI_base (mult0 beta kst) (mult0 eta (mult0 beta kst)))
          (plus0 (opp0 (mult0 eta (mult0 beta kts))) (mult0 beta k2)))
        (plus0 (mult0 (minus rI.rI_base one0 eta) (mult0 beta kst))
          (plus0 (opp0 (mult0 eta (mult0 beta kts))) (mult0 beta k2)))
        (t13_collapse rI (mult0 beta k1) (mult0 beta k2)
          (mult0 eta (mult0 beta kts)) (mult0 eta (mult0 beta kst))
          (mult0 beta kst))
        (id_cong (fun x ->
          plus0 x (plus0 (opp0 (mult0 eta (mult0 beta kts))) (mult0 beta k2)))
          (minus rI.rI_base (mult0 beta kst) (mult0 eta (mult0 beta kst)))
          (mult0 (minus rI.rI_base one0 eta) (mult0 beta kst)) hone))))

(** val policy_iter_backward_kl_step :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> (s -> lt) -> lt -> r -> lt -> ((s -> r) -> (s -> lt) -> lt)
    -> (s -> r) -> (s -> lt) -> r id -> (s -> lt) -> r id **)

let policy_iter_backward_kl_step rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  (fun reward beta beta_pos pi_ref pi_ref_pos z_align_pos eta eta_pos sum_over_S_pos pi_t pi_t_pos pi_t_norm pi_next_pos0 ->
  let hbeta =
    policy_iter_backward_kl_step_beta rI sS sO reward beta beta_pos pi_ref
      pi_ref_pos z_align_pos eta eta_pos sum_over_S_pos pi_t pi_t_pos
      pi_t_norm pi_next_pos0
  in
  let hbsn =
    id_trans
      (rI.rI_base.mult (inv_pos0 beta beta_pos)
        (rI.rI_base.mult beta
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos))))
      (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
        (relative_entropy rI sS sO
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
          (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos)))
      (relative_entropy rI sS sO
        (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
        (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
          pi_t_pos))
      (rI.rI_base.mult_assoc (inv_pos0 beta beta_pos) beta
        (relative_entropy rI sS sO
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
          (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos)))
      (id_trans
        (mult0 (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos)))
        (mult0 (rI.rI_base.mult beta (inv_pos0 beta beta_pos))
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos)))
        (relative_entropy rI sS sO
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
          (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos))
        (id_cong (fun x ->
          mult0 x
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos)))
          (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
          (rI.rI_base.mult beta (inv_pos0 beta beta_pos))
          (rI.rI_base.mult_comm (inv_pos0 beta beta_pos) beta))
        (id_trans
          (mult0 (rI.rI_base.mult beta (rI.rI_base.inv_pos beta beta_pos))
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos)))
          (mult0 rI.rI_base.one
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos)))
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos))
          (id_cong (fun x ->
            mult0 x
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)))
            (rI.rI_base.mult beta (rI.rI_base.inv_pos beta beta_pos))
            rI.rI_base.one (rI.rI_base.inv_pos_correct beta beta_pos))
          (id_trans
            (rI.rI_base.mult one0
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)))
            (rI.rI_base.mult
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos))
              one0)
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos))
            (rI.rI_base.mult_comm one0
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)))
            (rI.rI_base.mult_one
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos))))))
  in
  let hb1 =
    id_trans
      (rI.rI_base.mult (inv_pos0 beta beta_pos)
        (rI.rI_base.mult (minus rI.rI_base one0 eta)
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t))))
      (rI.rI_base.mult
        (rI.rI_base.mult (inv_pos0 beta beta_pos) (minus rI.rI_base one0 eta))
        (mult0 beta
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
      (mult0 (minus rI.rI_base one0 eta)
        (relative_entropy rI sS sO
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t))
      (rI.rI_base.mult_assoc (inv_pos0 beta beta_pos)
        (minus rI.rI_base one0 eta)
        (mult0 beta
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
      (id_trans
        (mult0
          (rI.rI_base.mult (inv_pos0 beta beta_pos)
            (minus rI.rI_base one0 eta))
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
        (mult0
          (rI.rI_base.mult (minus rI.rI_base one0 eta)
            (inv_pos0 beta beta_pos))
          (mult0 beta
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t)))
        (mult0 (minus rI.rI_base one0 eta)
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t))
        (id_cong (fun x ->
          mult0 x
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t)))
          (rI.rI_base.mult (inv_pos0 beta beta_pos)
            (minus rI.rI_base one0 eta))
          (rI.rI_base.mult (minus rI.rI_base one0 eta)
            (inv_pos0 beta beta_pos))
          (rI.rI_base.mult_comm (inv_pos0 beta beta_pos)
            (minus rI.rI_base one0 eta)))
        (id_trans
          (rI.rI_base.mult
            (rI.rI_base.mult (minus rI.rI_base one0 eta)
              (inv_pos0 beta beta_pos))
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t)))
          (rI.rI_base.mult (minus rI.rI_base one0 eta)
            (rI.rI_base.mult (inv_pos0 beta beta_pos)
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t))))
          (mult0 (minus rI.rI_base one0 eta)
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t))
          (id_sym
            (rI.rI_base.mult (minus rI.rI_base one0 eta)
              (rI.rI_base.mult (inv_pos0 beta beta_pos)
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))))
            (rI.rI_base.mult
              (rI.rI_base.mult (minus rI.rI_base one0 eta)
                (inv_pos0 beta beta_pos))
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t)))
            (rI.rI_base.mult_assoc (minus rI.rI_base one0 eta)
              (inv_pos0 beta beta_pos)
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t))))
          (id_trans
            (mult0 (minus rI.rI_base one0 eta)
              (rI.rI_base.mult (inv_pos0 beta beta_pos)
                (rI.rI_base.mult beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))))
            (mult0 (minus rI.rI_base one0 eta)
              (rI.rI_base.mult
                (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t)))
            (mult0 (minus rI.rI_base one0 eta)
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t))
            (id_cong (fun x -> mult0 (minus rI.rI_base one0 eta) x)
              (rI.rI_base.mult (inv_pos0 beta beta_pos)
                (rI.rI_base.mult beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t)))
              (rI.rI_base.mult
                (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t))
              (rI.rI_base.mult_assoc (inv_pos0 beta beta_pos) beta
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t)))
            (id_trans
              (mult0 (minus rI.rI_base one0 eta)
                (mult0 (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t)))
              (mult0 (minus rI.rI_base one0 eta)
                (mult0 (rI.rI_base.mult beta (inv_pos0 beta beta_pos))
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t)))
              (mult0 (minus rI.rI_base one0 eta)
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t))
              (id_cong (fun x -> mult0 (minus rI.rI_base one0 eta) x)
                (mult0 (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))
                (mult0 (rI.rI_base.mult beta (inv_pos0 beta beta_pos))
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))
                (id_cong (fun x ->
                  mult0 x
                    (relative_entropy rI sS sO
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)
                      pi_t))
                  (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
                  (rI.rI_base.mult beta (inv_pos0 beta beta_pos))
                  (rI.rI_base.mult_comm (inv_pos0 beta beta_pos) beta)))
              (id_trans
                (mult0 (minus rI.rI_base one0 eta)
                  (mult0
                    (rI.rI_base.mult beta (rI.rI_base.inv_pos beta beta_pos))
                    (relative_entropy rI sS sO
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)
                      pi_t)))
                (mult0 (minus rI.rI_base one0 eta)
                  (mult0 rI.rI_base.one
                    (relative_entropy rI sS sO
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)
                      pi_t)))
                (mult0 (minus rI.rI_base one0 eta)
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))
                (id_cong (fun x -> mult0 (minus rI.rI_base one0 eta) x)
                  (mult0
                    (rI.rI_base.mult beta (rI.rI_base.inv_pos beta beta_pos))
                    (relative_entropy rI sS sO
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)
                      pi_t))
                  (mult0 rI.rI_base.one
                    (relative_entropy rI sS sO
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)
                      pi_t))
                  (id_cong (fun x ->
                    mult0 x
                      (relative_entropy rI sS sO
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos)
                        pi_t))
                    (rI.rI_base.mult beta (rI.rI_base.inv_pos beta beta_pos))
                    rI.rI_base.one (rI.rI_base.inv_pos_correct beta beta_pos)))
                (id_cong (fun x -> mult0 (minus rI.rI_base one0 eta) x)
                  (rI.rI_base.mult one0
                    (relative_entropy rI sS sO
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)
                      pi_t))
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t)
                  (id_trans
                    (rI.rI_base.mult one0
                      (relative_entropy rI sS sO
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos)
                        pi_t))
                    (rI.rI_base.mult
                      (relative_entropy rI sS sO
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos)
                        pi_t)
                      one0)
                    (relative_entropy rI sS sO
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)
                      pi_t)
                    (rI.rI_base.mult_comm one0
                      (relative_entropy rI sS sO
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos)
                        pi_t))
                    (rI.rI_base.mult_one
                      (relative_entropy rI sS sO
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos)
                        pi_t)))))))))
  in
  let hb2 =
    id_trans
      (rI.rI_base.mult (inv_pos0 beta beta_pos)
        (rI.rI_base.opp
          (mult0 eta
            (mult0 beta
              (relative_entropy rI sS sO pi_t
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))))
      (rI.rI_base.opp
        (rI.rI_base.mult (inv_pos0 beta beta_pos)
          (mult0 eta
            (mult0 beta
              (relative_entropy rI sS sO pi_t
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))))
      (opp0
        (mult0 eta
          (relative_entropy rI sS sO pi_t
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
      (opp_mult_l rI (inv_pos0 beta beta_pos)
        (mult0 eta
          (mult0 beta
            (relative_entropy rI sS sO pi_t
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))))
      (id_trans
        (opp0
          (rI.rI_base.mult (inv_pos0 beta beta_pos)
            (rI.rI_base.mult eta
              (mult0 beta
                (relative_entropy rI sS sO pi_t
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))))
        (opp0
          (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 beta beta_pos) eta)
            (mult0 beta
              (relative_entropy rI sS sO pi_t
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))))
        (opp0
          (mult0 eta
            (relative_entropy rI sS sO pi_t
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
        (id_cong opp0
          (rI.rI_base.mult (inv_pos0 beta beta_pos)
            (rI.rI_base.mult eta
              (mult0 beta
                (relative_entropy rI sS sO pi_t
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))))
          (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 beta beta_pos) eta)
            (mult0 beta
              (relative_entropy rI sS sO pi_t
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
          (rI.rI_base.mult_assoc (inv_pos0 beta beta_pos) eta
            (mult0 beta
              (relative_entropy rI sS sO pi_t
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))))
        (id_trans
          (opp0
            (mult0 (rI.rI_base.mult (inv_pos0 beta beta_pos) eta)
              (mult0 beta
                (relative_entropy rI sS sO pi_t
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))))
          (opp0
            (mult0 (rI.rI_base.mult eta (inv_pos0 beta beta_pos))
              (mult0 beta
                (relative_entropy rI sS sO pi_t
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))))
          (opp0
            (mult0 eta
              (relative_entropy rI sS sO pi_t
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
          (id_cong opp0
            (mult0 (rI.rI_base.mult (inv_pos0 beta beta_pos) eta)
              (mult0 beta
                (relative_entropy rI sS sO pi_t
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
            (mult0 (rI.rI_base.mult eta (inv_pos0 beta beta_pos))
              (mult0 beta
                (relative_entropy rI sS sO pi_t
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
            (id_cong (fun x ->
              mult0 x
                (mult0 beta
                  (relative_entropy rI sS sO pi_t
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
              (rI.rI_base.mult (inv_pos0 beta beta_pos) eta)
              (rI.rI_base.mult eta (inv_pos0 beta beta_pos))
              (rI.rI_base.mult_comm (inv_pos0 beta beta_pos) eta)))
          (id_trans
            (opp0
              (rI.rI_base.mult (rI.rI_base.mult eta (inv_pos0 beta beta_pos))
                (mult0 beta
                  (relative_entropy rI sS sO pi_t
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))))
            (opp0
              (rI.rI_base.mult eta
                (rI.rI_base.mult (inv_pos0 beta beta_pos)
                  (mult0 beta
                    (relative_entropy rI sS sO pi_t
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos))))))
            (opp0
              (mult0 eta
                (relative_entropy rI sS sO pi_t
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
            (id_cong opp0
              (rI.rI_base.mult (rI.rI_base.mult eta (inv_pos0 beta beta_pos))
                (mult0 beta
                  (relative_entropy rI sS sO pi_t
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
              (rI.rI_base.mult eta
                (rI.rI_base.mult (inv_pos0 beta beta_pos)
                  (mult0 beta
                    (relative_entropy rI sS sO pi_t
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)))))
              (id_sym
                (rI.rI_base.mult eta
                  (rI.rI_base.mult (inv_pos0 beta beta_pos)
                    (mult0 beta
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos)))))
                (rI.rI_base.mult
                  (rI.rI_base.mult eta (inv_pos0 beta beta_pos))
                  (mult0 beta
                    (relative_entropy rI sS sO pi_t
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos))))
                (rI.rI_base.mult_assoc eta (inv_pos0 beta beta_pos)
                  (mult0 beta
                    (relative_entropy rI sS sO pi_t
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos))))))
            (id_trans
              (opp0
                (mult0 eta
                  (rI.rI_base.mult (inv_pos0 beta beta_pos)
                    (rI.rI_base.mult beta
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos))))))
              (opp0
                (mult0 eta
                  (rI.rI_base.mult
                    (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
                    (relative_entropy rI sS sO pi_t
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)))))
              (opp0
                (mult0 eta
                  (relative_entropy rI sS sO pi_t
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
              (id_cong opp0
                (mult0 eta
                  (rI.rI_base.mult (inv_pos0 beta beta_pos)
                    (rI.rI_base.mult beta
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos)))))
                (mult0 eta
                  (rI.rI_base.mult
                    (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
                    (relative_entropy rI sS sO pi_t
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos))))
                (id_cong (fun x -> mult0 eta x)
                  (rI.rI_base.mult (inv_pos0 beta beta_pos)
                    (rI.rI_base.mult beta
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos))))
                  (rI.rI_base.mult
                    (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
                    (relative_entropy rI sS sO pi_t
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)))
                  (rI.rI_base.mult_assoc (inv_pos0 beta beta_pos) beta
                    (relative_entropy rI sS sO pi_t
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)))))
              (id_trans
                (opp0
                  (mult0 eta
                    (mult0 (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos)))))
                (opp0
                  (mult0 eta
                    (mult0 (rI.rI_base.mult beta (inv_pos0 beta beta_pos))
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos)))))
                (opp0
                  (mult0 eta
                    (relative_entropy rI sS sO pi_t
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos))))
                (id_cong opp0
                  (mult0 eta
                    (mult0 (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos))))
                  (mult0 eta
                    (mult0 (rI.rI_base.mult beta (inv_pos0 beta beta_pos))
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos))))
                  (id_cong (fun x -> mult0 eta x)
                    (mult0 (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos)))
                    (mult0 (rI.rI_base.mult beta (inv_pos0 beta beta_pos))
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos)))
                    (id_cong (fun x ->
                      mult0 x
                        (relative_entropy rI sS sO pi_t
                          (pi_star rI sS sO reward beta beta_pos pi_ref
                            z_align_pos)))
                      (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
                      (rI.rI_base.mult beta (inv_pos0 beta beta_pos))
                      (rI.rI_base.mult_comm (inv_pos0 beta beta_pos) beta))))
                (id_trans
                  (opp0
                    (mult0 eta
                      (mult0
                        (rI.rI_base.mult beta
                          (rI.rI_base.inv_pos beta beta_pos))
                        (relative_entropy rI sS sO pi_t
                          (pi_star rI sS sO reward beta beta_pos pi_ref
                            z_align_pos)))))
                  (opp0
                    (mult0 eta
                      (mult0 rI.rI_base.one
                        (relative_entropy rI sS sO pi_t
                          (pi_star rI sS sO reward beta beta_pos pi_ref
                            z_align_pos)))))
                  (opp0
                    (mult0 eta
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos))))
                  (id_cong opp0
                    (mult0 eta
                      (mult0
                        (rI.rI_base.mult beta
                          (rI.rI_base.inv_pos beta beta_pos))
                        (relative_entropy rI sS sO pi_t
                          (pi_star rI sS sO reward beta beta_pos pi_ref
                            z_align_pos))))
                    (mult0 eta
                      (mult0 rI.rI_base.one
                        (relative_entropy rI sS sO pi_t
                          (pi_star rI sS sO reward beta beta_pos pi_ref
                            z_align_pos))))
                    (id_cong (fun x -> mult0 eta x)
                      (mult0
                        (rI.rI_base.mult beta
                          (rI.rI_base.inv_pos beta beta_pos))
                        (relative_entropy rI sS sO pi_t
                          (pi_star rI sS sO reward beta beta_pos pi_ref
                            z_align_pos)))
                      (mult0 rI.rI_base.one
                        (relative_entropy rI sS sO pi_t
                          (pi_star rI sS sO reward beta beta_pos pi_ref
                            z_align_pos)))
                      (id_cong (fun x ->
                        mult0 x
                          (relative_entropy rI sS sO pi_t
                            (pi_star rI sS sO reward beta beta_pos pi_ref
                              z_align_pos)))
                        (rI.rI_base.mult beta
                          (rI.rI_base.inv_pos beta beta_pos))
                        rI.rI_base.one
                        (rI.rI_base.inv_pos_correct beta beta_pos))))
                  (id_cong opp0
                    (mult0 eta
                      (rI.rI_base.mult one0
                        (relative_entropy rI sS sO pi_t
                          (pi_star rI sS sO reward beta beta_pos pi_ref
                            z_align_pos))))
                    (mult0 eta
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos)))
                    (id_cong (fun x -> mult0 eta x)
                      (rI.rI_base.mult one0
                        (relative_entropy rI sS sO pi_t
                          (pi_star rI sS sO reward beta beta_pos pi_ref
                            z_align_pos)))
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos))
                      (id_trans
                        (rI.rI_base.mult one0
                          (relative_entropy rI sS sO pi_t
                            (pi_star rI sS sO reward beta beta_pos pi_ref
                              z_align_pos)))
                        (rI.rI_base.mult
                          (relative_entropy rI sS sO pi_t
                            (pi_star rI sS sO reward beta beta_pos pi_ref
                              z_align_pos))
                          one0)
                        (relative_entropy rI sS sO pi_t
                          (pi_star rI sS sO reward beta beta_pos pi_ref
                            z_align_pos))
                        (rI.rI_base.mult_comm one0
                          (relative_entropy rI sS sO pi_t
                            (pi_star rI sS sO reward beta beta_pos pi_ref
                              z_align_pos)))
                        (rI.rI_base.mult_one
                          (relative_entropy rI sS sO pi_t
                            (pi_star rI sS sO reward beta beta_pos pi_ref
                              z_align_pos))))))))))))
  in
  let hb3 =
    id_trans
      (rI.rI_base.mult (inv_pos0 beta beta_pos)
        (rI.rI_base.mult beta
          (relative_entropy rI sS sO pi_t
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos))))
      (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
        (relative_entropy rI sS sO pi_t
          (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos)))
      (relative_entropy rI sS sO pi_t
        (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
          pi_t_pos))
      (rI.rI_base.mult_assoc (inv_pos0 beta beta_pos) beta
        (relative_entropy rI sS sO pi_t
          (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos)))
      (id_trans
        (mult0 (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
          (relative_entropy rI sS sO pi_t
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos)))
        (mult0 (rI.rI_base.mult beta (inv_pos0 beta beta_pos))
          (relative_entropy rI sS sO pi_t
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos)))
        (relative_entropy rI sS sO pi_t
          (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos))
        (id_cong (fun x ->
          mult0 x
            (relative_entropy rI sS sO pi_t
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos)))
          (rI.rI_base.mult (inv_pos0 beta beta_pos) beta)
          (rI.rI_base.mult beta (inv_pos0 beta beta_pos))
          (rI.rI_base.mult_comm (inv_pos0 beta beta_pos) beta))
        (id_trans
          (mult0 (rI.rI_base.mult beta (rI.rI_base.inv_pos beta beta_pos))
            (relative_entropy rI sS sO pi_t
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos)))
          (mult0 rI.rI_base.one
            (relative_entropy rI sS sO pi_t
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos)))
          (relative_entropy rI sS sO pi_t
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos))
          (id_cong (fun x ->
            mult0 x
              (relative_entropy rI sS sO pi_t
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)))
            (rI.rI_base.mult beta (rI.rI_base.inv_pos beta beta_pos))
            rI.rI_base.one (rI.rI_base.inv_pos_correct beta beta_pos))
          (id_trans
            (rI.rI_base.mult one0
              (relative_entropy rI sS sO pi_t
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)))
            (rI.rI_base.mult
              (relative_entropy rI sS sO pi_t
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos))
              one0)
            (relative_entropy rI sS sO pi_t
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos))
            (rI.rI_base.mult_comm one0
              (relative_entropy rI sS sO pi_t
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)))
            (rI.rI_base.mult_one
              (relative_entropy rI sS sO pi_t
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos))))))
  in
  id_trans
    (relative_entropy rI sS sO
      (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
      (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
        pi_t_pos))
    (mult0 (inv_pos0 beta beta_pos)
      (mult0 beta
        (relative_entropy rI sS sO
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
          (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos))))
    (plus0
      (mult0 (minus rI.rI_base one0 eta)
        (relative_entropy rI sS sO
          (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t))
      (plus0
        (opp0
          (mult0 eta
            (relative_entropy rI sS sO pi_t
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
        (relative_entropy rI sS sO pi_t
          (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
            pi_t pi_t_pos))))
    (id_sym
      (mult0 (inv_pos0 beta beta_pos)
        (mult0 beta
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos))))
      (relative_entropy rI sS sO
        (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
        (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
          pi_t_pos))
      hbsn)
    (id_trans
      (mult0 (inv_pos0 beta beta_pos)
        (mult0 beta
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos))))
      (mult0 (inv_pos0 beta beta_pos)
        (plus0
          (mult0 (minus rI.rI_base one0 eta)
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t)))
          (plus0
            (opp0
              (mult0 eta
                (mult0 beta
                  (relative_entropy rI sS sO pi_t
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))))
            (mult0 beta
              (relative_entropy rI sS sO pi_t
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos))))))
      (plus0
        (mult0 (minus rI.rI_base one0 eta)
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t))
        (plus0
          (opp0
            (mult0 eta
              (relative_entropy rI sS sO pi_t
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
          (relative_entropy rI sS sO pi_t
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos))))
      (id_cong (fun x -> mult0 (inv_pos0 beta beta_pos) x)
        (mult0 beta
          (relative_entropy rI sS sO
            (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
            (pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
              pi_t pi_t_pos)))
        (plus0
          (mult0 (minus rI.rI_base one0 eta)
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t)))
          (plus0
            (opp0
              (mult0 eta
                (mult0 beta
                  (relative_entropy rI sS sO pi_t
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))))
            (mult0 beta
              (relative_entropy rI sS sO pi_t
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)))))
        hbeta)
      (id_trans
        (rI.rI_base.mult (inv_pos0 beta beta_pos)
          (rI.rI_base.plus
            (mult0 (minus rI.rI_base one0 eta)
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t)))
            (plus0
              (opp0
                (mult0 eta
                  (mult0 beta
                    (relative_entropy rI sS sO pi_t
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)))))
              (mult0 beta
                (relative_entropy rI sS sO pi_t
                  (pi_next rI sS sO reward beta beta_pos pi_ref eta
                    sum_over_S_pos pi_t pi_t_pos))))))
        (rI.rI_base.plus
          (rI.rI_base.mult (inv_pos0 beta beta_pos)
            (mult0 (minus rI.rI_base one0 eta)
              (mult0 beta
                (relative_entropy rI sS sO
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                  pi_t))))
          (rI.rI_base.mult (inv_pos0 beta beta_pos)
            (plus0
              (opp0
                (mult0 eta
                  (mult0 beta
                    (relative_entropy rI sS sO pi_t
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)))))
              (mult0 beta
                (relative_entropy rI sS sO pi_t
                  (pi_next rI sS sO reward beta beta_pos pi_ref eta
                    sum_over_S_pos pi_t pi_t_pos))))))
        (plus0
          (mult0 (minus rI.rI_base one0 eta)
            (relative_entropy rI sS sO
              (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos) pi_t))
          (plus0
            (opp0
              (mult0 eta
                (relative_entropy rI sS sO pi_t
                  (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
            (relative_entropy rI sS sO pi_t
              (pi_next rI sS sO reward beta beta_pos pi_ref eta
                sum_over_S_pos pi_t pi_t_pos))))
        (rI.rI_base.distrib (inv_pos0 beta beta_pos)
          (mult0 (minus rI.rI_base one0 eta)
            (mult0 beta
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t)))
          (plus0
            (opp0
              (mult0 eta
                (mult0 beta
                  (relative_entropy rI sS sO pi_t
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)))))
            (mult0 beta
              (relative_entropy rI sS sO pi_t
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)))))
        (id_trans
          (plus0
            (mult0 (inv_pos0 beta beta_pos)
              (mult0 (minus rI.rI_base one0 eta)
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))))
            (rI.rI_base.mult (inv_pos0 beta beta_pos)
              (rI.rI_base.plus
                (opp0
                  (mult0 eta
                    (mult0 beta
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos)))))
                (mult0 beta
                  (relative_entropy rI sS sO pi_t
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos))))))
          (plus0
            (mult0 (inv_pos0 beta beta_pos)
              (mult0 (minus rI.rI_base one0 eta)
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))))
            (rI.rI_base.plus
              (rI.rI_base.mult (inv_pos0 beta beta_pos)
                (opp0
                  (mult0 eta
                    (mult0 beta
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos))))))
              (rI.rI_base.mult (inv_pos0 beta beta_pos)
                (mult0 beta
                  (relative_entropy rI sS sO pi_t
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos))))))
          (plus0
            (mult0 (minus rI.rI_base one0 eta)
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t))
            (plus0
              (opp0
                (mult0 eta
                  (relative_entropy rI sS sO pi_t
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
              (relative_entropy rI sS sO pi_t
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos))))
          (id_cong (fun x ->
            plus0
              (mult0 (inv_pos0 beta beta_pos)
                (mult0 (minus rI.rI_base one0 eta)
                  (mult0 beta
                    (relative_entropy rI sS sO
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)
                      pi_t))))
              x)
            (rI.rI_base.mult (inv_pos0 beta beta_pos)
              (rI.rI_base.plus
                (opp0
                  (mult0 eta
                    (mult0 beta
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos)))))
                (mult0 beta
                  (relative_entropy rI sS sO pi_t
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos)))))
            (rI.rI_base.plus
              (rI.rI_base.mult (inv_pos0 beta beta_pos)
                (opp0
                  (mult0 eta
                    (mult0 beta
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos))))))
              (rI.rI_base.mult (inv_pos0 beta beta_pos)
                (mult0 beta
                  (relative_entropy rI sS sO pi_t
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos)))))
            (rI.rI_base.distrib (inv_pos0 beta beta_pos)
              (opp0
                (mult0 eta
                  (mult0 beta
                    (relative_entropy rI sS sO pi_t
                      (pi_star rI sS sO reward beta beta_pos pi_ref
                        z_align_pos)))))
              (mult0 beta
                (relative_entropy rI sS sO pi_t
                  (pi_next rI sS sO reward beta beta_pos pi_ref eta
                    sum_over_S_pos pi_t pi_t_pos)))))
          (id_cong2 plus0
            (mult0 (inv_pos0 beta beta_pos)
              (mult0 (minus rI.rI_base one0 eta)
                (mult0 beta
                  (relative_entropy rI sS sO
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                    pi_t))))
            (mult0 (minus rI.rI_base one0 eta)
              (relative_entropy rI sS sO
                (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos)
                pi_t))
            (plus0
              (mult0 (inv_pos0 beta beta_pos)
                (opp0
                  (mult0 eta
                    (mult0 beta
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos))))))
              (mult0 (inv_pos0 beta beta_pos)
                (mult0 beta
                  (relative_entropy rI sS sO pi_t
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos)))))
            (plus0
              (opp0
                (mult0 eta
                  (relative_entropy rI sS sO pi_t
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
              (relative_entropy rI sS sO pi_t
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos)))
            hb1
            (id_cong2 plus0
              (mult0 (inv_pos0 beta beta_pos)
                (opp0
                  (mult0 eta
                    (mult0 beta
                      (relative_entropy rI sS sO pi_t
                        (pi_star rI sS sO reward beta beta_pos pi_ref
                          z_align_pos))))))
              (opp0
                (mult0 eta
                  (relative_entropy rI sS sO pi_t
                    (pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos))))
              (mult0 (inv_pos0 beta beta_pos)
                (mult0 beta
                  (relative_entropy rI sS sO pi_t
                    (pi_next rI sS sO reward beta beta_pos pi_ref eta
                      sum_over_S_pos pi_t pi_t_pos))))
              (relative_entropy rI sS sO pi_t
                (pi_next rI sS sO reward beta beta_pos pi_ref eta
                  sum_over_S_pos pi_t pi_t_pos))
              hb2 hb3))))))

(** val policy_iter_gap_diff :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r -> lt -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s ->
    lt) -> r id -> r id **)

let policy_iter_gap_diff rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  let sum_over_S0 = sO.sum_over_S in
  (fun reward beta beta_pos pi_ref eta eta_pos sum_over_S_pos pi_t pi_t_pos pi_t_norm ->
  let np =
    pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
      pi_t_pos
  in
  let a = advantage_aug rI sS reward beta pi_ref pi_t in
  let xn = sum_over_S0 (fun s0 -> mult0 (np s0) (a s0)) in
  let xt = sum_over_S0 (fun s0 -> mult0 (pi_t s0) (a s0)) in
  let k1 = relative_entropy rI sS sO np pi_t in
  let k2 = relative_entropy rI sS sO pi_t np in
  let hJt = j_pi_t_t12 rI sS sO reward beta pi_ref eta pi_t pi_t_norm in
  let hJn =
    j_pi_next_t12 rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
      pi_t pi_t_pos
  in
  let hdiff =
    id_cong2 plus0 (align_objective rI sS sO reward beta pi_ref np)
      (minus rI.rI_base xn (mult0 beta k1))
      (opp0 (align_objective rI sS sO reward beta pi_ref pi_t)) (opp0 xt) hJn
      (id_cong opp0 (align_objective rI sS sO reward beta pi_ref pi_t) xt hJt)
  in
  let hsur =
    surrogate_diff_identity rI sS sO reward beta beta_pos pi_ref eta
      sum_over_S_pos pi_t pi_t_pos pi_t_norm (fun s0 ->
      pi_next_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos
        pi_t pi_t_pos s0)
  in
  let hlc =
    id_trans
      (rI.rI_base.mult (inv_pos0 eta eta_pos)
        (rI.rI_base.mult eta (minus rI.rI_base xn xt)))
      (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 eta eta_pos) eta)
        (minus rI.rI_base xn xt))
      (minus rI.rI_base xn xt)
      (rI.rI_base.mult_assoc (inv_pos0 eta eta_pos) eta
        (minus rI.rI_base xn xt))
      (id_trans
        (mult0 (rI.rI_base.mult (inv_pos0 eta eta_pos) eta)
          (minus rI.rI_base xn xt))
        (mult0 rI.rI_base.one (minus rI.rI_base xn xt))
        (minus rI.rI_base xn xt)
        (id_cong (fun x -> mult0 x (minus rI.rI_base xn xt))
          (rI.rI_base.mult (inv_pos0 eta eta_pos) eta) rI.rI_base.one
          (id_trans (rI.rI_base.mult (inv_pos0 eta eta_pos) eta)
            (rI.rI_base.mult eta (inv_pos0 eta eta_pos)) rI.rI_base.one
            (rI.rI_base.mult_comm (inv_pos0 eta eta_pos) eta)
            (rI.rI_base.inv_pos_correct eta eta_pos)))
        (id_trans (rI.rI_base.mult one0 (minus rI.rI_base xn xt))
          (rI.rI_base.mult (minus rI.rI_base xn xt) one0)
          (minus rI.rI_base xn xt)
          (rI.rI_base.mult_comm one0 (minus rI.rI_base xn xt))
          (rI.rI_base.mult_one (minus rI.rI_base xn xt))))
  in
  let hinv =
    id_trans (minus rI.rI_base xn xt)
      (mult0 (inv_pos0 eta eta_pos) (mult0 eta (minus rI.rI_base xn xt)))
      (mult0 (inv_pos0 eta eta_pos) (mult0 beta (plus0 k1 k2)))
      (id_sym
        (mult0 (inv_pos0 eta eta_pos) (mult0 eta (minus rI.rI_base xn xt)))
        (minus rI.rI_base xn xt) hlc)
      (id_cong (fun x -> mult0 (inv_pos0 eta eta_pos) x)
        (mult0 eta (minus rI.rI_base xn xt)) (mult0 beta (plus0 k1 k2)) hsur)
  in
  let hswap =
    id_trans
      (rI.rI_base.plus (rI.rI_base.plus xn (opp0 (mult0 beta k1))) (opp0 xt))
      (rI.rI_base.plus xn (rI.rI_base.plus (opp0 (mult0 beta k1)) (opp0 xt)))
      (rI.rI_base.plus (rI.rI_base.plus xn (rI.rI_base.opp xt))
        (rI.rI_base.opp (mult0 beta k1)))
      (id_sym
        (rI.rI_base.plus xn
          (rI.rI_base.plus (opp0 (mult0 beta k1)) (opp0 xt)))
        (rI.rI_base.plus (rI.rI_base.plus xn (opp0 (mult0 beta k1)))
          (opp0 xt))
        (rI.rI_base.plus_assoc xn (opp0 (mult0 beta k1)) (opp0 xt)))
      (id_trans (plus0 xn (rI.rI_base.plus (opp0 (mult0 beta k1)) (opp0 xt)))
        (plus0 xn (rI.rI_base.plus (opp0 xt) (opp0 (mult0 beta k1))))
        (rI.rI_base.plus (rI.rI_base.plus xn (rI.rI_base.opp xt))
          (rI.rI_base.opp (mult0 beta k1)))
        (id_cong (fun x -> plus0 xn x)
          (rI.rI_base.plus (opp0 (mult0 beta k1)) (opp0 xt))
          (rI.rI_base.plus (opp0 xt) (opp0 (mult0 beta k1)))
          (rI.rI_base.plus_comm (opp0 (mult0 beta k1)) (opp0 xt)))
        (rI.rI_base.plus_assoc xn (opp0 xt) (opp0 (mult0 beta k1))))
  in
  let hm1 =
    id_trans (rI.rI_base.mult one0 k1) (rI.rI_base.mult k1 one0) k1
      (rI.rI_base.mult_comm one0 k1) (rI.rI_base.mult_one k1)
  in
  let hmm =
    id_trans (minus rI.rI_base (mult0 (inv_pos0 eta eta_pos) k1) k1)
      (minus rI.rI_base (mult0 (inv_pos0 eta eta_pos) k1) (mult0 one0 k1))
      (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0) k1)
      (id_cong (fun x ->
        minus rI.rI_base (mult0 (inv_pos0 eta eta_pos) k1) x) k1
        (mult0 one0 k1) (id_sym (mult0 one0 k1) k1 hm1))
      (id_sym (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0) k1)
        (minus rI.rI_base (mult0 (inv_pos0 eta eta_pos) k1) (mult0 one0 k1))
        (mult_minus_distr_r_t12 rI (inv_pos0 eta eta_pos) one0 k1))
  in
  let hin =
    id_trans
      (plus0 (rI.rI_base.mult (inv_pos0 eta eta_pos) (rI.rI_base.plus k1 k2))
        (opp0 k1))
      (plus0
        (rI.rI_base.plus (rI.rI_base.mult (inv_pos0 eta eta_pos) k1)
          (rI.rI_base.mult (inv_pos0 eta eta_pos) k2))
        (opp0 k1))
      (plus0
        (mult0 (rI.rI_base.plus (inv_pos0 eta eta_pos) (rI.rI_base.opp one0))
          k1)
        (mult0 (inv_pos0 eta eta_pos) k2))
      (id_cong (fun x -> plus0 x (opp0 k1))
        (rI.rI_base.mult (inv_pos0 eta eta_pos) (rI.rI_base.plus k1 k2))
        (rI.rI_base.plus (rI.rI_base.mult (inv_pos0 eta eta_pos) k1)
          (rI.rI_base.mult (inv_pos0 eta eta_pos) k2))
        (rI.rI_base.distrib (inv_pos0 eta eta_pos) k1 k2))
      (id_trans
        (rI.rI_base.plus
          (rI.rI_base.plus (mult0 (inv_pos0 eta eta_pos) k1)
            (mult0 (inv_pos0 eta eta_pos) k2))
          (opp0 k1))
        (rI.rI_base.plus (mult0 (inv_pos0 eta eta_pos) k1)
          (rI.rI_base.plus (mult0 (inv_pos0 eta eta_pos) k2) (opp0 k1)))
        (plus0
          (mult0
            (rI.rI_base.plus (inv_pos0 eta eta_pos) (rI.rI_base.opp one0)) k1)
          (mult0 (inv_pos0 eta eta_pos) k2))
        (id_sym
          (rI.rI_base.plus (mult0 (inv_pos0 eta eta_pos) k1)
            (rI.rI_base.plus (mult0 (inv_pos0 eta eta_pos) k2) (opp0 k1)))
          (rI.rI_base.plus
            (rI.rI_base.plus (mult0 (inv_pos0 eta eta_pos) k1)
              (mult0 (inv_pos0 eta eta_pos) k2))
            (opp0 k1))
          (rI.rI_base.plus_assoc (mult0 (inv_pos0 eta eta_pos) k1)
            (mult0 (inv_pos0 eta eta_pos) k2) (opp0 k1)))
        (id_trans
          (plus0 (mult0 (inv_pos0 eta eta_pos) k1)
            (rI.rI_base.plus (mult0 (inv_pos0 eta eta_pos) k2) (opp0 k1)))
          (plus0 (mult0 (inv_pos0 eta eta_pos) k1)
            (rI.rI_base.plus (opp0 k1) (mult0 (inv_pos0 eta eta_pos) k2)))
          (plus0
            (mult0
              (rI.rI_base.plus (inv_pos0 eta eta_pos) (rI.rI_base.opp one0))
              k1)
            (mult0 (inv_pos0 eta eta_pos) k2))
          (id_cong (fun x -> plus0 (mult0 (inv_pos0 eta eta_pos) k1) x)
            (rI.rI_base.plus (mult0 (inv_pos0 eta eta_pos) k2) (opp0 k1))
            (rI.rI_base.plus (opp0 k1) (mult0 (inv_pos0 eta eta_pos) k2))
            (rI.rI_base.plus_comm (mult0 (inv_pos0 eta eta_pos) k2) (opp0 k1)))
          (id_trans
            (rI.rI_base.plus (mult0 (inv_pos0 eta eta_pos) k1)
              (rI.rI_base.plus (opp0 k1) (mult0 (inv_pos0 eta eta_pos) k2)))
            (rI.rI_base.plus
              (rI.rI_base.plus (mult0 (inv_pos0 eta eta_pos) k1) (opp0 k1))
              (mult0 (inv_pos0 eta eta_pos) k2))
            (plus0
              (mult0
                (rI.rI_base.plus (inv_pos0 eta eta_pos) (rI.rI_base.opp one0))
                k1)
              (mult0 (inv_pos0 eta eta_pos) k2))
            (rI.rI_base.plus_assoc (mult0 (inv_pos0 eta eta_pos) k1)
              (opp0 k1) (mult0 (inv_pos0 eta eta_pos) k2))
            (id_trans
              (plus0 (minus rI.rI_base (mult0 (inv_pos0 eta eta_pos) k1) k1)
                (mult0 (inv_pos0 eta eta_pos) k2))
              (plus0
                (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0) k1)
                (mult0 (inv_pos0 eta eta_pos) k2))
              (plus0
                (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0) k1)
                (mult0 (inv_pos0 eta eta_pos) k2))
              (id_cong (fun x -> plus0 x (mult0 (inv_pos0 eta eta_pos) k2))
                (minus rI.rI_base (mult0 (inv_pos0 eta eta_pos) k1) k1)
                (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0) k1) hmm)
              Id_refl))))
  in
  let hbeta_form =
    id_trans
      (minus rI.rI_base
        (rI.rI_base.mult (inv_pos0 eta eta_pos)
          (rI.rI_base.mult beta (plus0 k1 k2)))
        (mult0 beta k1))
      (minus rI.rI_base
        (rI.rI_base.mult beta
          (rI.rI_base.mult (inv_pos0 eta eta_pos) (plus0 k1 k2)))
        (mult0 beta k1))
      (mult0 beta
        (plus0 (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0) k1)
          (mult0 (inv_pos0 eta eta_pos) k2)))
      (id_cong (fun x -> minus rI.rI_base x (mult0 beta k1))
        (rI.rI_base.mult (inv_pos0 eta eta_pos)
          (rI.rI_base.mult beta (plus0 k1 k2)))
        (rI.rI_base.mult beta
          (rI.rI_base.mult (inv_pos0 eta eta_pos) (plus0 k1 k2)))
        (id_trans
          (rI.rI_base.mult (inv_pos0 eta eta_pos)
            (rI.rI_base.mult beta (plus0 k1 k2)))
          (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 eta eta_pos) beta)
            (plus0 k1 k2))
          (rI.rI_base.mult beta
            (rI.rI_base.mult (inv_pos0 eta eta_pos) (plus0 k1 k2)))
          (rI.rI_base.mult_assoc (inv_pos0 eta eta_pos) beta (plus0 k1 k2))
          (id_trans
            (mult0 (rI.rI_base.mult (inv_pos0 eta eta_pos) beta)
              (plus0 k1 k2))
            (mult0 (rI.rI_base.mult beta (inv_pos0 eta eta_pos))
              (plus0 k1 k2))
            (rI.rI_base.mult beta
              (rI.rI_base.mult (inv_pos0 eta eta_pos) (plus0 k1 k2)))
            (id_cong (fun x -> mult0 x (plus0 k1 k2))
              (rI.rI_base.mult (inv_pos0 eta eta_pos) beta)
              (rI.rI_base.mult beta (inv_pos0 eta eta_pos))
              (rI.rI_base.mult_comm (inv_pos0 eta eta_pos) beta))
            (id_sym
              (rI.rI_base.mult beta
                (rI.rI_base.mult (inv_pos0 eta eta_pos) (plus0 k1 k2)))
              (rI.rI_base.mult (rI.rI_base.mult beta (inv_pos0 eta eta_pos))
                (plus0 k1 k2))
              (rI.rI_base.mult_assoc beta (inv_pos0 eta eta_pos)
                (plus0 k1 k2))))))
      (id_trans
        (minus rI.rI_base
          (rI.rI_base.mult beta (mult0 (inv_pos0 eta eta_pos) (plus0 k1 k2)))
          (rI.rI_base.mult beta k1))
        (rI.rI_base.mult beta
          (minus rI.rI_base (mult0 (inv_pos0 eta eta_pos) (plus0 k1 k2)) k1))
        (mult0 beta
          (plus0 (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0) k1)
            (mult0 (inv_pos0 eta eta_pos) k2)))
        (id_sym
          (rI.rI_base.mult beta
            (minus rI.rI_base (mult0 (inv_pos0 eta eta_pos) (plus0 k1 k2)) k1))
          (minus rI.rI_base
            (rI.rI_base.mult beta
              (mult0 (inv_pos0 eta eta_pos) (plus0 k1 k2)))
            (rI.rI_base.mult beta k1))
          (mult_minus_distr_l rI beta
            (mult0 (inv_pos0 eta eta_pos) (plus0 k1 k2)) k1))
        (id_cong (fun x -> mult0 beta x)
          (minus rI.rI_base (mult0 (inv_pos0 eta eta_pos) (plus0 k1 k2)) k1)
          (plus0 (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0) k1)
            (mult0 (inv_pos0 eta eta_pos) k2))
          hin))
  in
  id_trans
    (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref np)
      (align_objective rI sS sO reward beta pi_ref pi_t))
    (minus rI.rI_base (minus rI.rI_base xn (mult0 beta k1)) xt)
    (mult0 beta
      (plus0 (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0) k1)
        (mult0 (inv_pos0 eta eta_pos) k2)))
    hdiff
    (id_trans (minus rI.rI_base (minus rI.rI_base xn (mult0 beta k1)) xt)
      (minus rI.rI_base (minus rI.rI_base xn xt) (mult0 beta k1))
      (mult0 beta
        (plus0 (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0) k1)
          (mult0 (inv_pos0 eta eta_pos) k2)))
      hswap
      (id_trans (minus rI.rI_base (minus rI.rI_base xn xt) (mult0 beta k1))
        (minus rI.rI_base
          (mult0 (inv_pos0 eta eta_pos) (mult0 beta (plus0 k1 k2)))
          (mult0 beta k1))
        (mult0 beta
          (plus0 (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0) k1)
            (mult0 (inv_pos0 eta eta_pos) k2)))
        (id_cong (fun x -> minus rI.rI_base x (mult0 beta k1))
          (minus rI.rI_base xn xt)
          (mult0 (inv_pos0 eta eta_pos) (mult0 beta (plus0 k1 k2))) hinv)
        hbeta_form)))

(** val minus_middle_t12 : realInterfaceEnhanced -> r -> r -> r -> r id **)

let minus_middle_t12 rI a b c =
  id_trans (minus rI.rI_base (minus rI.rI_base a b) (minus rI.rI_base c b))
    (minus rI.rI_base a (rI.rI_base.plus b (minus rI.rI_base c b)))
    (minus rI.rI_base a c) (minus_minus_distr rI a b (minus rI.rI_base c b))
    (id_cong (fun x -> minus rI.rI_base a x)
      (rI.rI_base.plus b (minus rI.rI_base c b)) c (minus_plus_cancel rI b c))

(** val minus_left_cancel_t12 :
    realInterfaceEnhanced -> r -> r -> r -> r id **)

let minus_left_cancel_t12 rI =
  let zero0 = rI.rI_base.zero in
  let opp0 = rI.rI_base.opp in
  (fun a b c ->
  let hzero =
    let h1 =
      id_trans (rI.rI_base.plus zero0 (opp0 (minus rI.rI_base b c)))
        (rI.rI_base.plus (opp0 (minus rI.rI_base b c)) zero0)
        (opp0 (minus rI.rI_base b c))
        (rI.rI_base.plus_comm zero0 (opp0 (minus rI.rI_base b c)))
        (rI.rI_base.plus_zero (opp0 (minus rI.rI_base b c)))
    in
    let h2 =
      id_trans (rI.rI_base.opp (minus rI.rI_base b c))
        (rI.rI_base.plus (rI.rI_base.opp b) c) (rI.rI_base.plus c (opp0 b))
        (opp_minus rI b c) (rI.rI_base.plus_comm (opp0 b) c)
    in
    id_trans (minus rI.rI_base zero0 (minus rI.rI_base b c))
      (opp0 (minus rI.rI_base b c)) (minus rI.rI_base c b) h1 h2
  in
  id_trans (minus rI.rI_base (minus rI.rI_base a b) (minus rI.rI_base a c))
    (minus rI.rI_base (minus rI.rI_base a a) (minus rI.rI_base b c))
    (minus rI.rI_base c b) (minus_rearrange_four rI a b a c)
    (id_trans
      (minus rI.rI_base (minus rI.rI_base a a) (minus rI.rI_base b c))
      (minus rI.rI_base rI.rI_base.zero (minus rI.rI_base b c))
      (minus rI.rI_base c b)
      (id_cong2 (minus rI.rI_base) (minus rI.rI_base a a) rI.rI_base.zero
        (minus rI.rI_base b c) (minus rI.rI_base b c)
        (minus_self_zero rI a a Id_refl) Id_refl)
      hzero))

(** val policy_gap_next_exact :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> (s -> lt) -> lt -> r -> lt -> ((s -> r) -> (s -> lt) -> lt)
    -> (s -> r) -> (s -> lt) -> r id -> r id **)

let policy_gap_next_exact rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  (fun reward beta beta_pos pi_ref pi_ref_pos z_align_pos eta eta_pos sum_over_S_pos pi_t pi_t_pos pi_t_norm ->
  let ps = pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos in
  let np =
    pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
      pi_t_pos
  in
  let hgap =
    rlhf_suboptimality_gap rI sS sO reward beta beta_pos pi_ref pi_ref_pos
      z_align_pos pi_t pi_t_norm pi_t_pos
  in
  let hdiff =
    policy_iter_gap_diff rI sS sO reward beta beta_pos pi_ref eta eta_pos
      sum_over_S_pos pi_t pi_t_pos pi_t_norm
  in
  id_trans
    (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref ps)
      (align_objective rI sS sO reward beta pi_ref np))
    (minus rI.rI_base
      (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref ps)
        (align_objective rI sS sO reward beta pi_ref pi_t))
      (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref np)
        (align_objective rI sS sO reward beta pi_ref pi_t)))
    (minus rI.rI_base (mult0 beta (relative_entropy rI sS sO pi_t ps))
      (mult0 beta
        (plus0
          (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0)
            (relative_entropy rI sS sO np pi_t))
          (mult0 (inv_pos0 eta eta_pos) (relative_entropy rI sS sO pi_t np)))))
    (id_sym
      (minus rI.rI_base
        (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref ps)
          (align_objective rI sS sO reward beta pi_ref pi_t))
        (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref np)
          (align_objective rI sS sO reward beta pi_ref pi_t)))
      (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref ps)
        (align_objective rI sS sO reward beta pi_ref np))
      (minus_middle_t12 rI (align_objective rI sS sO reward beta pi_ref ps)
        (align_objective rI sS sO reward beta pi_ref pi_t)
        (align_objective rI sS sO reward beta pi_ref np)))
    (id_cong2 (minus rI.rI_base)
      (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref ps)
        (align_objective rI sS sO reward beta pi_ref pi_t))
      (mult0 beta (relative_entropy rI sS sO pi_t ps))
      (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref np)
        (align_objective rI sS sO reward beta pi_ref pi_t))
      (mult0 beta
        (plus0
          (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0)
            (relative_entropy rI sS sO np pi_t))
          (mult0 (inv_pos0 eta eta_pos) (relative_entropy rI sS sO pi_t np))))
      hgap hdiff))

(** val policy_gap_decrement_exact :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> lt -> r -> lt -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) ->
    (s -> lt) -> r id -> r id **)

let policy_gap_decrement_exact rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  (fun reward beta beta_pos pi_ref z_align_pos eta eta_pos sum_over_S_pos pi_t pi_t_pos pi_t_norm ->
  let ps = pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos in
  let np =
    pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
      pi_t_pos
  in
  let hdiff =
    policy_iter_gap_diff rI sS sO reward beta beta_pos pi_ref eta eta_pos
      sum_over_S_pos pi_t pi_t_pos pi_t_norm
  in
  id_trans
    (minus rI.rI_base
      (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref ps)
        (align_objective rI sS sO reward beta pi_ref pi_t))
      (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref ps)
        (align_objective rI sS sO reward beta pi_ref np)))
    (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref np)
      (align_objective rI sS sO reward beta pi_ref pi_t))
    (mult0 beta
      (plus0
        (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0)
          (relative_entropy rI sS sO np pi_t))
        (mult0 (inv_pos0 eta eta_pos) (relative_entropy rI sS sO pi_t np))))
    (minus_left_cancel_t12 rI
      (align_objective rI sS sO reward beta pi_ref ps)
      (align_objective rI sS sO reward beta pi_ref pi_t)
      (align_objective rI sS sO reward beta pi_ref np))
    hdiff)

(** val dpo_loss_step_exact :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> r -> lt -> ((s -> r) -> (s -> lt) -> lt) -> (s -> r) -> (s ->
    lt) -> r id -> r id **)

let dpo_loss_step_exact rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  (fun reward beta beta_pos pi_ref eta eta_pos sum_over_S_pos pi_t pi_t_pos pi_t_norm ->
  let np =
    pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
      pi_t_pos
  in
  let hdiff =
    policy_iter_gap_diff rI sS sO reward beta beta_pos pi_ref eta eta_pos
      sum_over_S_pos pi_t pi_t_pos pi_t_norm
  in
  id_trans
    (minus rI.rI_base
      (rI.rI_base.opp (align_objective rI sS sO reward beta pi_ref pi_t))
      (rI.rI_base.opp (align_objective rI sS sO reward beta pi_ref np)))
    (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref np)
      (align_objective rI sS sO reward beta pi_ref pi_t))
    (mult0 beta
      (plus0
        (mult0 (minus rI.rI_base (inv_pos0 eta eta_pos) one0)
          (relative_entropy rI sS sO np pi_t))
        (mult0 (inv_pos0 eta eta_pos) (relative_entropy rI sS sO pi_t np))))
    (minus_opp_opp rI (align_objective rI sS sO reward beta pi_ref pi_t)
      (align_objective rI sS sO reward beta pi_ref np))
    hdiff)

(** val policy_gap_backward_kl_exact :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r -> lt ->
    (s -> r) -> (s -> lt) -> lt -> r -> lt -> ((s -> r) -> (s -> lt) -> lt)
    -> (s -> r) -> (s -> lt) -> r id -> r id **)

let policy_gap_backward_kl_exact rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  (fun reward beta beta_pos pi_ref pi_ref_pos z_align_pos eta eta_pos sum_over_S_pos pi_t pi_t_pos pi_t_norm ->
  let ps = pi_star rI sS sO reward beta beta_pos pi_ref z_align_pos in
  let np =
    pi_next rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
      pi_t_pos
  in
  let hnextpos = fun s0 ->
    pi_next_pos rI sS sO reward beta beta_pos pi_ref eta sum_over_S_pos pi_t
      pi_t_pos s0
  in
  let hgap =
    rlhf_suboptimality_gap rI sS sO reward beta beta_pos pi_ref pi_ref_pos
      z_align_pos pi_t pi_t_norm pi_t_pos
  in
  let hb =
    policy_iter_backward_kl_step rI sS sO reward beta beta_pos pi_ref
      pi_ref_pos z_align_pos eta eta_pos sum_over_S_pos pi_t pi_t_pos
      pi_t_norm hnextpos
  in
  let hscale1 =
    id_trans
      (rI.rI_base.mult beta
        (rI.rI_base.mult (minus rI.rI_base one0 eta)
          (relative_entropy rI sS sO ps pi_t)))
      (rI.rI_base.mult (rI.rI_base.mult beta (minus rI.rI_base one0 eta))
        (relative_entropy rI sS sO ps pi_t))
      (mult0 (minus rI.rI_base one0 eta)
        (mult0 beta (relative_entropy rI sS sO ps pi_t)))
      (rI.rI_base.mult_assoc beta (minus rI.rI_base one0 eta)
        (relative_entropy rI sS sO ps pi_t))
      (id_trans
        (mult0 (rI.rI_base.mult beta (minus rI.rI_base one0 eta))
          (relative_entropy rI sS sO ps pi_t))
        (mult0 (rI.rI_base.mult (minus rI.rI_base one0 eta) beta)
          (relative_entropy rI sS sO ps pi_t))
        (mult0 (minus rI.rI_base one0 eta)
          (mult0 beta (relative_entropy rI sS sO ps pi_t)))
        (id_cong (fun x -> mult0 x (relative_entropy rI sS sO ps pi_t))
          (rI.rI_base.mult beta (minus rI.rI_base one0 eta))
          (rI.rI_base.mult (minus rI.rI_base one0 eta) beta)
          (rI.rI_base.mult_comm beta (minus rI.rI_base one0 eta)))
        (id_sym
          (rI.rI_base.mult (minus rI.rI_base one0 eta)
            (rI.rI_base.mult beta (relative_entropy rI sS sO ps pi_t)))
          (rI.rI_base.mult (rI.rI_base.mult (minus rI.rI_base one0 eta) beta)
            (relative_entropy rI sS sO ps pi_t))
          (rI.rI_base.mult_assoc (minus rI.rI_base one0 eta) beta
            (relative_entropy rI sS sO ps pi_t))))
  in
  let hswap2 =
    id_trans
      (rI.rI_base.mult beta
        (rI.rI_base.mult eta (relative_entropy rI sS sO pi_t ps)))
      (rI.rI_base.mult (rI.rI_base.mult beta eta)
        (relative_entropy rI sS sO pi_t ps))
      (mult0 eta (mult0 beta (relative_entropy rI sS sO pi_t ps)))
      (rI.rI_base.mult_assoc beta eta (relative_entropy rI sS sO pi_t ps))
      (id_trans
        (mult0 (rI.rI_base.mult beta eta) (relative_entropy rI sS sO pi_t ps))
        (mult0 (rI.rI_base.mult eta beta) (relative_entropy rI sS sO pi_t ps))
        (mult0 eta (mult0 beta (relative_entropy rI sS sO pi_t ps)))
        (id_cong (fun x -> mult0 x (relative_entropy rI sS sO pi_t ps))
          (rI.rI_base.mult beta eta) (rI.rI_base.mult eta beta)
          (rI.rI_base.mult_comm beta eta))
        (id_sym
          (rI.rI_base.mult eta
            (rI.rI_base.mult beta (relative_entropy rI sS sO pi_t ps)))
          (rI.rI_base.mult (rI.rI_base.mult eta beta)
            (relative_entropy rI sS sO pi_t ps))
          (rI.rI_base.mult_assoc eta beta (relative_entropy rI sS sO pi_t ps))))
  in
  let hscale2 =
    id_trans
      (rI.rI_base.mult beta
        (rI.rI_base.opp (mult0 eta (relative_entropy rI sS sO pi_t ps))))
      (rI.rI_base.opp
        (rI.rI_base.mult beta (mult0 eta (relative_entropy rI sS sO pi_t ps))))
      (opp0
        (mult0 eta
          (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref ps)
            (align_objective rI sS sO reward beta pi_ref pi_t))))
      (opp_mult_l rI beta (mult0 eta (relative_entropy rI sS sO pi_t ps)))
      (id_cong opp0
        (mult0 beta (mult0 eta (relative_entropy rI sS sO pi_t ps)))
        (mult0 eta
          (minus rI.rI_base (align_objective rI sS sO reward beta pi_ref ps)
            (align_objective rI sS sO reward beta pi_ref pi_t)))
        (id_trans
          (mult0 beta (mult0 eta (relative_entropy rI sS sO pi_t ps)))
          (mult0 eta (mult0 beta (relative_entropy rI sS sO pi_t ps)))
          (mult0 eta
            (minus rI.rI_base
              (align_objective rI sS sO reward beta pi_ref ps)
              (align_objective rI sS sO reward beta pi_ref pi_t)))
          hswap2
          (id_cong (fun z -> mult0 eta z)
            (mult0 beta (relative_entropy rI sS sO pi_t ps))
            (minus rI.rI_base
              (align_objective rI sS sO reward beta pi_ref ps)
              (align_objective rI sS sO reward beta pi_ref pi_t))
            (id_sym
              (minus rI.rI_base
                (align_objective rI sS sO reward beta pi_ref ps)
                (align_objective rI sS sO reward beta pi_ref pi_t))
              (mult0 beta (relative_entropy rI sS sO pi_t ps)) hgap))))
  in
  let hscale3 =
    id_trans
      (rI.rI_base.mult beta
        (rI.rI_base.plus
          (opp0 (mult0 eta (relative_entropy rI sS sO pi_t ps)))
          (relative_entropy rI sS sO pi_t np)))
      (rI.rI_base.plus
        (rI.rI_base.mult beta
          (opp0 (mult0 eta (relative_entropy rI sS sO pi_t ps))))
        (rI.rI_base.mult beta (relative_entropy rI sS sO pi_t np)))
      (plus0
        (opp0
          (mult0 eta
            (minus rI.rI_base
              (align_objective rI sS sO reward beta pi_ref ps)
              (align_objective rI sS sO reward beta pi_ref pi_t))))
        (rI.rI_base.mult beta (relative_entropy rI sS sO pi_t np)))
      (rI.rI_base.distrib beta
        (opp0 (mult0 eta (relative_entropy rI sS sO pi_t ps)))
        (relative_entropy rI sS sO pi_t np))
      (id_cong2 plus0
        (mult0 beta (opp0 (mult0 eta (relative_entropy rI sS sO pi_t ps))))
        (opp0
          (mult0 eta
            (minus rI.rI_base
              (align_objective rI sS sO reward beta pi_ref ps)
              (align_objective rI sS sO reward beta pi_ref pi_t))))
        (rI.rI_base.mult beta (relative_entropy rI sS sO pi_t np))
        (rI.rI_base.mult beta (relative_entropy rI sS sO pi_t np)) hscale2
        Id_refl)
  in
  let hscale =
    id_trans
      (rI.rI_base.mult beta
        (rI.rI_base.plus
          (mult0 (minus rI.rI_base one0 eta)
            (relative_entropy rI sS sO ps pi_t))
          (plus0 (opp0 (mult0 eta (relative_entropy rI sS sO pi_t ps)))
            (relative_entropy rI sS sO pi_t np))))
      (rI.rI_base.plus
        (rI.rI_base.mult beta
          (mult0 (minus rI.rI_base one0 eta)
            (relative_entropy rI sS sO ps pi_t)))
        (rI.rI_base.mult beta
          (plus0 (opp0 (mult0 eta (relative_entropy rI sS sO pi_t ps)))
            (relative_entropy rI sS sO pi_t np))))
      (plus0
        (mult0 (minus rI.rI_base one0 eta)
          (mult0 beta (relative_entropy rI sS sO ps pi_t)))
        (plus0
          (opp0
            (mult0 eta
              (minus rI.rI_base
                (align_objective rI sS sO reward beta pi_ref ps)
                (align_objective rI sS sO reward beta pi_ref pi_t))))
          (mult0 beta (relative_entropy rI sS sO pi_t np))))
      (rI.rI_base.distrib beta
        (mult0 (minus rI.rI_base one0 eta)
          (relative_entropy rI sS sO ps pi_t))
        (plus0 (opp0 (mult0 eta (relative_entropy rI sS sO pi_t ps)))
          (relative_entropy rI sS sO pi_t np)))
      (id_cong2 plus0
        (mult0 beta
          (mult0 (minus rI.rI_base one0 eta)
            (relative_entropy rI sS sO ps pi_t)))
        (mult0 (minus rI.rI_base one0 eta)
          (mult0 beta (relative_entropy rI sS sO ps pi_t)))
        (mult0 beta
          (plus0 (opp0 (mult0 eta (relative_entropy rI sS sO pi_t ps)))
            (relative_entropy rI sS sO pi_t np)))
        (plus0
          (opp0
            (mult0 eta
              (minus rI.rI_base
                (align_objective rI sS sO reward beta pi_ref ps)
                (align_objective rI sS sO reward beta pi_ref pi_t))))
          (mult0 beta (relative_entropy rI sS sO pi_t np)))
        hscale1 hscale3)
  in
  id_trans (mult0 beta (relative_entropy rI sS sO ps np))
    (mult0 beta
      (plus0
        (mult0 (minus rI.rI_base one0 eta)
          (relative_entropy rI sS sO ps pi_t))
        (plus0 (opp0 (mult0 eta (relative_entropy rI sS sO pi_t ps)))
          (relative_entropy rI sS sO pi_t np))))
    (plus0
      (mult0 (minus rI.rI_base one0 eta)
        (mult0 beta (relative_entropy rI sS sO ps pi_t)))
      (plus0
        (opp0
          (mult0 eta
            (minus rI.rI_base
              (align_objective rI sS sO reward beta pi_ref ps)
              (align_objective rI sS sO reward beta pi_ref pi_t))))
        (mult0 beta (relative_entropy rI sS sO pi_t np))))
    (id_cong (mult0 beta) (relative_entropy rI sS sO ps np)
      (plus0
        (mult0 (minus rI.rI_base one0 eta)
          (relative_entropy rI sS sO ps pi_t))
        (plus0 (opp0 (mult0 eta (relative_entropy rI sS sO pi_t ps)))
          (relative_entropy rI sS sO pi_t np)))
      hb)
    hscale)
