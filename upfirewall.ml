
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

(** val le_plus_nonneg_r : realInterfaceEnhanced -> r -> r -> le -> le **)

let le_plus_nonneg_r rI =
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun a b hb ->
  rI.rI_base.le_trans a (rI.rI_base.plus a rI.rI_base.zero)
    (rI.rI_base.plus a b)
    (internal_Id_rew_r (rI.rI_base.plus a rI.rI_base.zero) a
      (rI.rI_base.le_refl a) (rI.rI_base.plus_zero a))
    (rI.le_plus_compat a a rI.rI_base.zero b (rI.rI_base.le_refl a) hb))

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

(** val log_div : realInterfaceEnhanced -> r -> r -> lt -> lt -> r id **)

let log_div rI a b ha hb =
  let hlm = rI.log_mult a (rI.rI_base.inv_pos b hb) ha (rI.inv_pos_pos b hb)
  in
  let hli = log_inv_one_inv rI b hb in
  id_trans (rI.log (rI.rI_base.mult a (rI.rI_base.inv_pos b hb)))
    (rI.rI_base.plus (rI.log a) (rI.log (rI.rI_base.inv_pos b hb)))
    (rI.rI_base.plus (rI.log a) (rI.rI_base.opp (rI.log b))) hlm
    (id_cong (fun x -> rI.rI_base.plus (rI.log a) x)
      (rI.log (rI.rI_base.inv_pos b hb)) (rI.rI_base.opp (rI.log b)) hli)

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

(** val log_div_neg : realInterfaceEnhanced -> r -> r -> lt -> lt -> r id **)

let log_div_neg rI a b ha hb =
  let h1 = log_div rI a b ha hb in
  let h2 = log_div rI b a hb ha in
  let h3 =
    id_trans (rI.rI_base.plus (rI.log b) (rI.rI_base.opp (rI.log a)))
      (rI.rI_base.plus (rI.rI_base.opp (rI.log a)) (rI.log b))
      (rI.rI_base.opp (minus rI.rI_base (rI.log a) (rI.log b)))
      (rI.rI_base.plus_comm (rI.log b) (rI.rI_base.opp (rI.log a)))
      (id_sym (rI.rI_base.opp (minus rI.rI_base (rI.log a) (rI.log b)))
        (rI.rI_base.plus (rI.rI_base.opp (rI.log a)) (rI.log b))
        (opp_minus rI (rI.log a) (rI.log b)))
  in
  let h4 =
    id_cong rI.rI_base.opp
      (rI.log (rI.rI_base.mult b (rI.rI_base.inv_pos a ha)))
      (minus rI.rI_base (rI.log b) (rI.log a)) h2
  in
  let h5 =
    let h5a =
      id_cong rI.rI_base.opp (minus rI.rI_base (rI.log b) (rI.log a))
        (rI.rI_base.opp (minus rI.rI_base (rI.log a) (rI.log b))) h3
    in
    id_trans (rI.rI_base.opp (minus rI.rI_base (rI.log b) (rI.log a)))
      (rI.rI_base.opp
        (rI.rI_base.opp (minus rI.rI_base (rI.log a) (rI.log b))))
      (minus rI.rI_base (rI.log a) (rI.log b)) h5a
      (double_neg rI (minus rI.rI_base (rI.log a) (rI.log b)))
  in
  let h6 =
    id_trans
      (rI.rI_base.opp (rI.log (rI.rI_base.mult b (rI.rI_base.inv_pos a ha))))
      (rI.rI_base.opp (minus rI.rI_base (rI.log b) (rI.log a)))
      (minus rI.rI_base (rI.log a) (rI.log b)) h4 h5
  in
  id_trans (rI.log (rI.rI_base.mult a (rI.rI_base.inv_pos b hb)))
    (minus rI.rI_base (rI.log a) (rI.log b))
    (rI.rI_base.opp (rI.log (rI.rI_base.mult b (rI.rI_base.inv_pos a ha))))
    h1
    (id_sym
      (rI.rI_base.opp (rI.log (rI.rI_base.mult b (rI.rI_base.inv_pos a ha))))
      (minus rI.rI_base (rI.log a) (rI.log b)) h6)

(** val le_mult_compat_r :
    realInterfaceEnhanced -> r -> r -> r -> le -> le -> le **)

let le_mult_compat_r rI =
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun a b c ha hbc ->
  internal_Id_rew_r (rI.rI_base.mult a b) (rI.rI_base.mult b a)
    (internal_Id_rew_r (rI.rI_base.mult a c) (rI.rI_base.mult c a)
      (rI.le_mult_compat_weak b c a ha hbc) (rI.rI_base.mult_comm a c))
    (rI.rI_base.mult_comm a b))

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

(** val le_minus_nonneg : realInterfaceEnhanced -> r -> r -> le -> le **)

let le_minus_nonneg rI a b hab =
  let h1 =
    rI.le_plus_compat a b (rI.rI_base.opp a) (rI.rI_base.opp a) hab
      (rI.rI_base.le_refl (rI.rI_base.opp a))
  in
  let h2 = rI.rI_base.plus_opp a in
  rI.rI_base.le_id_l rI.rI_base.zero (rI.rI_base.plus a (rI.rI_base.opp a))
    (rI.rI_base.plus b (rI.rI_base.opp a))
    (id_sym (rI.rI_base.plus a (rI.rI_base.opp a)) rI.rI_base.zero h2) h1

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

(** val lt_mult_pos_cancel :
    realInterfaceEnhanced -> r -> r -> lt -> lt -> lt **)

let lt_mult_pos_cancel rI =
  let zero0 = rI.rI_base.zero in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  (fun a c hc h ->
  rI.rI_base.lt_id_r zero0 (mult0 (mult0 a c) (inv_pos0 c hc)) a
    (id_sym a (mult0 (mult0 a c) (inv_pos0 c hc))
      (id_trans a (rI.rI_base.mult a rI.rI_base.one)
        (rI.rI_base.mult (rI.rI_base.mult a c) (inv_pos0 c hc))
        (id_sym (rI.rI_base.mult a rI.rI_base.one) a (rI.rI_base.mult_one a))
        (id_trans (mult0 a rI.rI_base.one)
          (mult0 a (rI.rI_base.mult c (rI.rI_base.inv_pos c hc)))
          (rI.rI_base.mult (rI.rI_base.mult a c) (inv_pos0 c hc))
          (id_cong (fun x -> mult0 a x) rI.rI_base.one
            (rI.rI_base.mult c (rI.rI_base.inv_pos c hc))
            (id_sym (rI.rI_base.mult c (rI.rI_base.inv_pos c hc))
              rI.rI_base.one (rI.rI_base.inv_pos_correct c hc)))
          (rI.rI_base.mult_assoc a c (inv_pos0 c hc)))))
    (rI.mult_positive (mult0 a c) (inv_pos0 c hc) h (rI.inv_pos_pos c hc)))

type normalized = r id

type positive_dist = s -> lt

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

(** val gibbs_pointwise :
    realInterfaceEnhanced -> stateSpace -> (s -> r) -> (s -> r) -> s -> lt ->
    lt -> le **)

let gibbs_pointwise rI _ =
  let zero0 = rI.rI_base.zero in
  let one0 = rI.rI_base.one in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let log0 = rI.log in
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun p q s0 hps hqs ->
  let hratio_pos =
    rI.mult_positive (q s0) (inv_pos0 (p s0) hps) hqs
      (rI.inv_pos_pos (p s0) hps)
  in
  let hlin = rI.log_le_linear (mult0 (q s0) (inv_pos0 (p s0) hps)) hratio_pos
  in
  let hopp =
    rI.opp_le_compat (log0 (mult0 (q s0) (inv_pos0 (p s0) hps)))
      (minus rI.rI_base (mult0 (q s0) (inv_pos0 (p s0) hps)) one0) hlin
  in
  let hld = log_div_neg rI (p s0) (q s0) hps hqs in
  let hrhs =
    let hlogdiv = log_div rI (p s0) (q s0) hps hqs in
    id_sym (mult0 (p s0) (log0 (mult0 (p s0) (inv_pos0 (q s0) hqs))))
      (mult0 (p s0) (minus rI.rI_base (log0 (p s0)) (log0 (q s0))))
      (id_cong (fun x -> mult0 (p s0) x)
        (log0 (mult0 (p s0) (inv_pos0 (q s0) hqs)))
        (minus rI.rI_base (log0 (p s0)) (log0 (q s0))) hlogdiv)
  in
  internal_Id_rew_r
    (mult0 (p s0) (minus rI.rI_base (log0 (p s0)) (log0 (q s0))))
    (mult0 (p s0) (log0 (mult0 (p s0) (inv_pos0 (q s0) hqs))))
    (let hstep1 =
       le_mult_compat_r rI (p s0)
         (rI.rI_base.opp
           (minus rI.rI_base (mult0 (q s0) (inv_pos0 (p s0) hps)) one0))
         (rI.rI_base.opp (log0 (mult0 (q s0) (inv_pos0 (p s0) hps))))
         (rI.rI_base.lt_le_iff zero0 (p s0) (Inl hps)) hopp
     in
     let hstep2 =
       id_cong (fun x -> mult0 (p s0) x)
         (log0 (mult0 (p s0) (inv_pos0 (q s0) hqs)))
         (rI.rI_base.opp (log0 (mult0 (q s0) (inv_pos0 (p s0) hps)))) hld
     in
     let hstep3 =
       internal_Id_rew_r
         (mult0 (p s0) (log0 (mult0 (p s0) (inv_pos0 (q s0) hqs))))
         (mult0 (p s0)
           (rI.rI_base.opp (log0 (mult0 (q s0) (inv_pos0 (p s0) hps)))))
         hstep1 hstep2
     in
     let hlhs =
       let hoppl =
         opp_mult_l rI (p s0)
           (minus rI.rI_base (mult0 (q s0) (inv_pos0 (p s0) hps)) one0)
       in
       let hdist =
         mult_minus_distr_l rI (p s0) (mult0 (q s0) (inv_pos0 (p s0) hps))
           one0
       in
       let hcc =
         let h1 = rI.rI_base.mult_assoc (p s0) (q s0) (inv_pos0 (p s0) hps) in
         let h2 =
           id_cong (fun x -> mult0 x (inv_pos0 (p s0) hps))
             (rI.rI_base.mult (p s0) (q s0)) (rI.rI_base.mult (q s0) (p s0))
             (rI.rI_base.mult_comm (p s0) (q s0))
         in
         let h3 =
           id_sym
             (rI.rI_base.mult (q s0)
               (rI.rI_base.mult (p s0) (inv_pos0 (p s0) hps)))
             (rI.rI_base.mult (rI.rI_base.mult (q s0) (p s0))
               (inv_pos0 (p s0) hps))
             (rI.rI_base.mult_assoc (q s0) (p s0) (inv_pos0 (p s0) hps))
         in
         let h4 =
           id_cong (fun x -> mult0 (q s0) x)
             (rI.rI_base.mult (p s0) (rI.rI_base.inv_pos (p s0) hps))
             rI.rI_base.one (rI.rI_base.inv_pos_correct (p s0) hps)
         in
         let h5 = rI.rI_base.mult_one (q s0) in
         id_trans (mult0 (p s0) (mult0 (q s0) (inv_pos0 (p s0) hps)))
           (mult0 (mult0 (p s0) (q s0)) (inv_pos0 (p s0) hps)) (q s0) h1
           (id_trans (mult0 (mult0 (p s0) (q s0)) (inv_pos0 (p s0) hps))
             (mult0 (mult0 (q s0) (p s0)) (inv_pos0 (p s0) hps)) (q s0) h2
             (id_trans (mult0 (mult0 (q s0) (p s0)) (inv_pos0 (p s0) hps))
               (mult0 (q s0) (mult0 (p s0) (inv_pos0 (p s0) hps))) (q s0) h3
               (id_trans (mult0 (q s0) (mult0 (p s0) (inv_pos0 (p s0) hps)))
                 (mult0 (q s0) one0) (q s0) h4 h5)))
       in
       let hmo = rI.rI_base.mult_one (p s0) in
       let hfull =
         id_trans
           (mult0 (p s0)
             (minus rI.rI_base (mult0 (q s0) (inv_pos0 (p s0) hps)) one0))
           (minus rI.rI_base
             (mult0 (p s0) (mult0 (q s0) (inv_pos0 (p s0) hps)))
             (mult0 (p s0) one0))
           (minus rI.rI_base (q s0) (p s0)) hdist
           (id_trans
             (minus rI.rI_base
               (mult0 (p s0) (mult0 (q s0) (inv_pos0 (p s0) hps)))
               (mult0 (p s0) one0))
             (minus rI.rI_base (q s0) (mult0 (p s0) one0))
             (minus rI.rI_base (q s0) (p s0))
             (id_cong (fun x -> minus rI.rI_base x (mult0 (p s0) one0))
               (mult0 (p s0) (mult0 (q s0) (inv_pos0 (p s0) hps))) (q s0) hcc)
             (id_cong (fun x -> minus rI.rI_base (q s0) x)
               (mult0 (p s0) one0) (p s0) hmo))
       in
       let hopp2 =
         id_trans (rI.rI_base.opp (minus rI.rI_base (q s0) (p s0)))
           (rI.rI_base.plus (rI.rI_base.opp (q s0)) (p s0))
           (rI.rI_base.plus (p s0) (rI.rI_base.opp (q s0)))
           (opp_minus rI (q s0) (p s0))
           (id_sym (rI.rI_base.plus (p s0) (rI.rI_base.opp (q s0)))
             (rI.rI_base.plus (rI.rI_base.opp (q s0)) (p s0))
             (rI.rI_base.plus_comm (p s0) (rI.rI_base.opp (q s0))))
       in
       id_sym
         (mult0 (p s0)
           (rI.rI_base.opp
             (minus rI.rI_base (mult0 (q s0) (inv_pos0 (p s0) hps)) one0)))
         (minus rI.rI_base (p s0) (q s0))
         (id_trans
           (mult0 (p s0)
             (rI.rI_base.opp
               (minus rI.rI_base (mult0 (q s0) (inv_pos0 (p s0) hps)) one0)))
           (rI.rI_base.opp
             (mult0 (p s0)
               (minus rI.rI_base (mult0 (q s0) (inv_pos0 (p s0) hps)) one0)))
           (minus rI.rI_base (p s0) (q s0)) hoppl
           (id_trans
             (rI.rI_base.opp
               (mult0 (p s0)
                 (minus rI.rI_base (mult0 (q s0) (inv_pos0 (p s0) hps)) one0)))
             (rI.rI_base.opp (minus rI.rI_base (q s0) (p s0)))
             (minus rI.rI_base (p s0) (q s0))
             (id_cong rI.rI_base.opp
               (mult0 (p s0)
                 (minus rI.rI_base (mult0 (q s0) (inv_pos0 (p s0) hps)) one0))
               (minus rI.rI_base (q s0) (p s0)) hfull)
             hopp2))
     in
     internal_Id_rew_r (minus rI.rI_base (p s0) (q s0))
       (mult0 (p s0)
         (rI.rI_base.opp
           (minus rI.rI_base (mult0 (q s0) (inv_pos0 (p s0) hps)) one0)))
       hstep3 hlhs)
    hrhs)

(** val gibbs_inequality :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> (s -> r) ->
    normalized -> positive_dist -> normalized -> positive_dist -> le **)

let gibbs_inequality rI sS sO =
  let zero0 = rI.rI_base.zero in
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  let internal_Id_rew = fun _ f _ _ -> f in
  (fun p q hnp hpp hnq hpq ->
  let hpt = fun s0 -> gibbs_pointwise rI sS p q s0 (hpp s0) (hpq s0) in
  let hle =
    sO.sum_over_S_le (fun s0 -> minus rI.rI_base (p s0) (q s0)) (fun s0 ->
      mult0 (p s0) (minus rI.rI_base (log0 (p s0)) (log0 (q s0)))) hpt
  in
  let hsum0 =
    let hadd = sO.sum_over_S_add p (fun s0 -> rI.rI_base.opp (q s0)) in
    let hoppq = sum_opp rI sS sO q in
    let htot =
      id_trans (sum_over_S0 (fun s0 -> plus0 (p s0) (rI.rI_base.opp (q s0))))
        (plus0 (sum_over_S0 p)
          (sum_over_S0 (fun s0 -> rI.rI_base.opp (q s0))))
        (plus0 (sum_over_S0 p) (rI.rI_base.opp (sum_over_S0 q))) hadd
        (id_cong (fun x -> plus0 (sum_over_S0 p) x)
          (sum_over_S0 (fun s0 -> rI.rI_base.opp (q s0)))
          (rI.rI_base.opp (sum_over_S0 q)) hoppq)
    in
    let hfin =
      id_trans (plus0 (sum_over_S0 p) (rI.rI_base.opp (sum_over_S0 q)))
        (plus0 one0 (rI.rI_base.opp (sum_over_S0 q))) rI.rI_base.zero
        (id_cong (fun x -> plus0 x (rI.rI_base.opp (sum_over_S0 q)))
          (sum_over_S0 p) one0 hnp)
        (id_trans (plus0 one0 (rI.rI_base.opp (sum_over_S0 q)))
          (plus0 one0 (rI.rI_base.opp one0)) rI.rI_base.zero
          (id_cong (fun x -> plus0 one0 x) (rI.rI_base.opp (sum_over_S0 q))
            (rI.rI_base.opp one0)
            (id_cong rI.rI_base.opp (sum_over_S0 q) one0 hnq))
          (rI.rI_base.plus_opp one0))
    in
    id_trans (sum_over_S0 (fun s0 -> plus0 (p s0) (rI.rI_base.opp (q s0))))
      (plus0 (sum_over_S0 p) (rI.rI_base.opp (sum_over_S0 q))) zero0 htot hfin
  in
  internal_Id_rew (sum_over_S0 (fun s0 -> minus rI.rI_base (p s0) (q s0)))
    hle zero0 hsum0)

(** val entropy_dist :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r **)

let entropy_dist rI _ sO =
  let mult0 = rI.rI_base.mult in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  (fun p ->
  sum_over_S0 (fun s0 -> mult0 (p s0) (rI.rI_base.opp (log0 (p s0)))))

(** val energy_expectation :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> (s -> r) ->
    r **)

let energy_expectation rI _ sO =
  let mult0 = rI.rI_base.mult in
  let sum_over_S0 = sO.sum_over_S in
  (fun base_loss p -> sum_over_S0 (fun s0 -> mult0 (p s0) (base_loss s0)))

(** val entropy_neg_sum :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> r id **)

let entropy_neg_sum rI sS sO =
  let mult0 = rI.rI_base.mult in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun p ->
  let hpt = fun s0 ->
    let h1 = opp_mult_l rI (p s0) (log0 (p s0)) in
    let h2 =
      id_cong rI.rI_base.opp (mult0 (p s0) (rI.rI_base.opp (log0 (p s0))))
        (rI.rI_base.opp (mult0 (p s0) (log0 (p s0)))) h1
    in
    id_sym (rI.rI_base.opp (mult0 (p s0) (rI.rI_base.opp (log0 (p s0)))))
      (mult0 (p s0) (log0 (p s0)))
      (id_trans
        (rI.rI_base.opp (mult0 (p s0) (rI.rI_base.opp (log0 (p s0)))))
        (rI.rI_base.opp (rI.rI_base.opp (mult0 (p s0) (log0 (p s0)))))
        (mult0 (p s0) (log0 (p s0))) h2
        (double_neg rI (mult0 (p s0) (log0 (p s0)))))
  in
  let hext =
    sO.sum_over_S_ext (fun s0 -> mult0 (p s0) (log0 (p s0))) (fun s0 ->
      rI.rI_base.opp (mult0 (p s0) (rI.rI_base.opp (log0 (p s0))))) hpt
  in
  internal_Id_rew_r (sum_over_S0 (fun s0 -> mult0 (p s0) (log0 (p s0))))
    (sum_over_S0 (fun s0 ->
      rI.rI_base.opp (mult0 (p s0) (rI.rI_base.opp (log0 (p s0))))))
    (sum_opp rI sS sO (fun s0 -> mult0 (p s0) (rI.rI_base.opp (log0 (p s0)))))
    hext)

(** val le_minus_nonneg_rev : realInterfaceEnhanced -> r -> r -> le -> le **)

let le_minus_nonneg_rev rI =
  let zero0 = rI.rI_base.zero in
  let plus0 = rI.rI_base.plus in
  (fun a b h ->
  rI.rI_base.le_id_l a (plus0 (minus rI.rI_base a b) b) b
    (id_trans a (rI.rI_base.plus a rI.rI_base.zero)
      (rI.rI_base.plus (rI.rI_base.plus a (rI.rI_base.opp b)) b)
      (id_sym (rI.rI_base.plus a rI.rI_base.zero) a (rI.rI_base.plus_zero a))
      (id_trans (plus0 a rI.rI_base.zero)
        (plus0 a (rI.rI_base.plus (rI.rI_base.opp b) b))
        (rI.rI_base.plus (rI.rI_base.plus a (rI.rI_base.opp b)) b)
        (id_sym (plus0 a (rI.rI_base.plus (rI.rI_base.opp b) b))
          (plus0 a rI.rI_base.zero)
          (id_cong (fun x -> plus0 a x)
            (rI.rI_base.plus (rI.rI_base.opp b) b) rI.rI_base.zero
            (id_trans (rI.rI_base.plus (rI.rI_base.opp b) b)
              (rI.rI_base.plus b (rI.rI_base.opp b)) rI.rI_base.zero
              (rI.rI_base.plus_comm (rI.rI_base.opp b) b)
              (rI.rI_base.plus_opp b))))
        (rI.rI_base.plus_assoc a (rI.rI_base.opp b) b)))
    (rI.rI_base.le_id_r (plus0 (minus rI.rI_base a b) b) (plus0 zero0 b) b
      (id_trans (rI.rI_base.plus zero0 b) (rI.rI_base.plus b zero0) b
        (rI.rI_base.plus_comm zero0 b) (rI.rI_base.plus_zero b))
      (rI.le_plus_compat (minus rI.rI_base a b) zero0 b b h
        (rI.rI_base.le_refl b))))

(** val le_mult_pos_cancel :
    realInterfaceEnhanced -> r -> r -> lt -> le -> le **)

let le_mult_pos_cancel rI =
  let zero0 = rI.rI_base.zero in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  (fun a c hc h ->
  rI.rI_base.le_id_l a (mult0 (mult0 a c) (inv_pos0 c hc)) zero0
    (id_trans a (rI.rI_base.mult a rI.rI_base.one)
      (rI.rI_base.mult (rI.rI_base.mult a c) (inv_pos0 c hc))
      (id_sym (rI.rI_base.mult a rI.rI_base.one) a (rI.rI_base.mult_one a))
      (id_trans (mult0 a rI.rI_base.one)
        (mult0 a (rI.rI_base.mult c (rI.rI_base.inv_pos c hc)))
        (rI.rI_base.mult (rI.rI_base.mult a c) (inv_pos0 c hc))
        (id_cong (fun x -> mult0 a x) rI.rI_base.one
          (rI.rI_base.mult c (rI.rI_base.inv_pos c hc))
          (id_sym (rI.rI_base.mult c (rI.rI_base.inv_pos c hc))
            rI.rI_base.one (rI.rI_base.inv_pos_correct c hc)))
        (rI.rI_base.mult_assoc a c (inv_pos0 c hc))))
    (rI.rI_base.le_id_r (mult0 (mult0 a c) (inv_pos0 c hc))
      (mult0 zero0 (inv_pos0 c hc)) zero0
      (id_trans (rI.rI_base.mult zero0 (inv_pos0 c hc))
        (rI.rI_base.mult (inv_pos0 c hc) zero0) rI.rI_base.zero
        (rI.rI_base.mult_comm zero0 (inv_pos0 c hc))
        (rI.rI_base.mult_zero (inv_pos0 c hc)))
      (rI.le_mult_compat_weak (mult0 a c) zero0 (inv_pos0 c hc)
        (rI.rI_base.lt_le_iff rI.rI_base.zero (inv_pos0 c hc) (Inl
          (rI.inv_pos_pos c hc)))
        h)))

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

(** val z_temp_pos :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> lt **)

let z_temp_pos rI _ sO =
  let zero0 = rI.rI_base.zero in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  let sum_over_S0 = sO.sum_over_S in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec t ht ->
  rI.rI_base.lt_id_r zero0
    (sum_over_S0 (fun s0 -> exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
    (z_temp t)
    (id_sym (z_temp t)
      (sum_over_S0 (fun s0 ->
        exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
      (z_temp_spec t ht))
    (sum_over_S_pos (fun s0 ->
      exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))) (fun s0 ->
      rI.rI_base.exp_neg_pos (mult0 (inv_pos0 t ht) (base_loss s0)))))

(** val boltzmann_dist_temp :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> s -> r **)

let boltzmann_dist_temp rI sS sO =
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec t ht s0 ->
  mult0
    (inv_pos0 (z_temp t)
      (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t ht))
    (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))

(** val energy_exp_temp :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> r **)

let energy_exp_temp rI sS sO =
  let mult0 = rI.rI_base.mult in
  let sum_over_S0 = sO.sum_over_S in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec t ht ->
  sum_over_S0 (fun s0 ->
    mult0
      (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t ht s0)
      (base_loss s0)))

(** val boltzmann_dist_temp_normalized :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> r id **)

let boltzmann_dist_temp_normalized rI sS sO =
  let one0 = rI.rI_base.one in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  let sum_over_S0 = sO.sum_over_S in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec t ht ->
  let hlin =
    sO.sum_over_S_linear
      (inv_pos0 (z_temp t)
        (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t ht))
      (fun s0 -> exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))
  in
  let hZ =
    id_sym (z_temp t)
      (sum_over_S0 (fun s0 ->
        exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
      (z_temp_spec t ht)
  in
  let hcc =
    id_trans
      (rI.rI_base.mult
        (inv_pos0 (z_temp t)
          (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t
            ht))
        (z_temp t))
      (rI.rI_base.mult (z_temp t)
        (inv_pos0 (z_temp t)
          (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t
            ht)))
      rI.rI_base.one
      (rI.rI_base.mult_comm
        (inv_pos0 (z_temp t)
          (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t
            ht))
        (z_temp t))
      (rI.rI_base.inv_pos_correct (z_temp t)
        (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t ht))
  in
  id_trans
    (sum_over_S0 (fun s0 ->
      mult0
        (inv_pos0 (z_temp t)
          (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t
            ht))
        (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))
    (mult0
      (inv_pos0 (z_temp t)
        (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t ht))
      (sum_over_S0 (fun s0 ->
        exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))
    one0 hlin
    (id_trans
      (mult0
        (inv_pos0 (z_temp t)
          (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t
            ht))
        (sum_over_S0 (fun s0 ->
          exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))
      (mult0
        (inv_pos0 (z_temp t)
          (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t
            ht))
        (z_temp t))
      one0
      (id_cong (fun x ->
        mult0
          (inv_pos0 (z_temp t)
            (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
              t ht))
          x)
        (sum_over_S0 (fun s0 ->
          exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
        (z_temp t) hZ)
      hcc))

(** val boltzmann_dist_temp_pos :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> s -> lt **)

let boltzmann_dist_temp_pos rI sS sO =
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec t ht s0 ->
  rI.mult_positive
    (inv_pos0 (z_temp t)
      (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t ht))
    (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))
    (rI.inv_pos_pos (z_temp t)
      (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t ht))
    (rI.rI_base.exp_neg_pos (mult0 (inv_pos0 t ht) (base_loss s0))))

(** val boltzmann_log_temp_decomp :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> s -> r
    id **)

let boltzmann_log_temp_decomp rI sS sO =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  let log0 = rI.log in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec ->
  let internal_Id_rew_r = fun _ _ hC _ -> hC in
  (fun t ht s0 ->
  let hpos1 =
    rI.inv_pos_pos (z_temp t)
      (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t ht)
  in
  let hpos2 = rI.rI_base.exp_neg_pos (mult0 (inv_pos0 t ht) (base_loss s0)) in
  let hlm =
    rI.log_mult
      (inv_pos0 (z_temp t)
        (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t ht))
      (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))) hpos1 hpos2
  in
  internal_Id_rew_r
    (log0
      (mult0
        (inv_pos0 (z_temp t)
          (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t
            ht))
        (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))
    (plus0
      (log0
        (inv_pos0 (z_temp t)
          (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t
            ht)))
      (log0 (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))
    (let hli =
       log_inv_one_inv rI (z_temp t)
         (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t
           ht)
     in
     internal_Id_rew_r
       (log0
         (inv_pos0 (z_temp t)
           (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t
             ht)))
       (rI.rI_base.opp (log0 (z_temp t)))
       (let hle = log_exp_neg rI (mult0 (inv_pos0 t ht) (base_loss s0)) in
        internal_Id_rew_r
          (log0 (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0))) Id_refl hle)
       hli)
    hlm))

(** val entropy_temp_explicit :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> r id **)

let entropy_temp_explicit rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec t ht ->
  let hpt = fun s0 ->
    let hlog =
      boltzmann_log_temp_decomp rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t ht s0
    in
    let hopp =
      id_trans
        (rI.rI_base.opp
          (rI.rI_base.plus (rI.rI_base.opp (log0 (z_temp t)))
            (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0)))))
        (rI.rI_base.plus (rI.rI_base.opp (rI.rI_base.opp (log0 (z_temp t))))
          (rI.rI_base.opp
            (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0)))))
        (plus0 (log0 (z_temp t)) (mult0 (inv_pos0 t ht) (base_loss s0)))
        (opp_plus rI (rI.rI_base.opp (log0 (z_temp t)))
          (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0))))
        (id_trans
          (plus0 (rI.rI_base.opp (rI.rI_base.opp (log0 (z_temp t))))
            (rI.rI_base.opp
              (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0)))))
          (plus0 (log0 (z_temp t))
            (rI.rI_base.opp
              (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0)))))
          (plus0 (log0 (z_temp t)) (mult0 (inv_pos0 t ht) (base_loss s0)))
          (id_cong (fun x ->
            plus0 x
              (rI.rI_base.opp
                (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0)))))
            (rI.rI_base.opp (rI.rI_base.opp (log0 (z_temp t))))
            (log0 (z_temp t)) (double_neg rI (log0 (z_temp t))))
          (id_cong (fun x -> plus0 (log0 (z_temp t)) x)
            (rI.rI_base.opp
              (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0))))
            (mult0 (inv_pos0 t ht) (base_loss s0))
            (double_neg rI (mult0 (inv_pos0 t ht) (base_loss s0)))))
    in
    let hcomm =
      rI.rI_base.plus_comm (log0 (z_temp t))
        (mult0 (inv_pos0 t ht) (base_loss s0))
    in
    id_trans
      (mult0
        (mult0
          (inv_pos0 (z_temp t)
            (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
              t ht))
          (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
        (rI.rI_base.opp
          (log0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))))
      (mult0
        (mult0
          (inv_pos0 (z_temp t)
            (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
              t ht))
          (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
        (rI.rI_base.opp
          (plus0 (rI.rI_base.opp (log0 (z_temp t)))
            (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0))))))
      (rI.rI_base.plus
        (rI.rI_base.mult
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (mult0 (inv_pos0 t ht) (base_loss s0)))
        (rI.rI_base.mult
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (log0 (z_temp t))))
      (id_cong (fun x ->
        mult0
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (rI.rI_base.opp x))
        (log0
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))
        (plus0 (rI.rI_base.opp (log0 (z_temp t)))
          (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0))))
        hlog)
      (id_trans
        (mult0
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (rI.rI_base.opp
            (plus0 (rI.rI_base.opp (log0 (z_temp t)))
              (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0))))))
        (mult0
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (plus0 (log0 (z_temp t)) (mult0 (inv_pos0 t ht) (base_loss s0))))
        (rI.rI_base.plus
          (rI.rI_base.mult
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            (mult0 (inv_pos0 t ht) (base_loss s0)))
          (rI.rI_base.mult
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            (log0 (z_temp t))))
        (id_cong (fun x ->
          mult0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            x)
          (rI.rI_base.opp
            (plus0 (rI.rI_base.opp (log0 (z_temp t)))
              (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0)))))
          (plus0 (log0 (z_temp t)) (mult0 (inv_pos0 t ht) (base_loss s0)))
          hopp)
        (id_trans
          (mult0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            (plus0 (log0 (z_temp t)) (mult0 (inv_pos0 t ht) (base_loss s0))))
          (mult0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            (plus0 (mult0 (inv_pos0 t ht) (base_loss s0)) (log0 (z_temp t))))
          (rI.rI_base.plus
            (rI.rI_base.mult
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
              (mult0 (inv_pos0 t ht) (base_loss s0)))
            (rI.rI_base.mult
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
              (log0 (z_temp t))))
          (id_cong (fun x ->
            mult0
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
              x)
            (plus0 (log0 (z_temp t)) (mult0 (inv_pos0 t ht) (base_loss s0)))
            (plus0 (mult0 (inv_pos0 t ht) (base_loss s0)) (log0 (z_temp t)))
            hcomm)
          (rI.rI_base.distrib
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            (mult0 (inv_pos0 t ht) (base_loss s0)) (log0 (z_temp t)))))
  in
  let h1 =
    sO.sum_over_S_ext (fun s0 ->
      mult0
        (mult0
          (inv_pos0 (z_temp t)
            (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
              t ht))
          (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
        (rI.rI_base.opp
          (log0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))))
      (fun s0 ->
      plus0
        (mult0
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (mult0 (inv_pos0 t ht) (base_loss s0)))
        (mult0
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (log0 (z_temp t))))
      hpt
  in
  let hadd =
    sO.sum_over_S_add (fun s0 ->
      mult0
        (mult0
          (inv_pos0 (z_temp t)
            (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
              t ht))
          (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
        (mult0 (inv_pos0 t ht) (base_loss s0)))
      (fun s0 ->
      mult0
        (mult0
          (inv_pos0 (z_temp t)
            (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
              t ht))
          (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
        (log0 (z_temp t)))
  in
  let hlin1 =
    let hpt2 = fun s0 ->
      id_trans
        (rI.rI_base.mult
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (mult0 (inv_pos0 t ht) (base_loss s0)))
        (rI.rI_base.mult (mult0 (inv_pos0 t ht) (base_loss s0))
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))
        (mult0 (inv_pos0 t ht)
          (rI.rI_base.mult
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            (base_loss s0)))
        (rI.rI_base.mult_comm
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (mult0 (inv_pos0 t ht) (base_loss s0)))
        (id_trans
          (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 t ht) (base_loss s0))
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))
          (rI.rI_base.mult (inv_pos0 t ht)
            (rI.rI_base.mult (base_loss s0)
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))))
          (mult0 (inv_pos0 t ht)
            (rI.rI_base.mult
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
              (base_loss s0)))
          (id_sym
            (rI.rI_base.mult (inv_pos0 t ht)
              (rI.rI_base.mult (base_loss s0)
                (mult0
                  (inv_pos0 (z_temp t)
                    (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                      z_temp_spec t ht))
                  (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))))
            (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 t ht) (base_loss s0))
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))
            (rI.rI_base.mult_assoc (inv_pos0 t ht) (base_loss s0)
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))))
          (id_cong (fun x -> mult0 (inv_pos0 t ht) x)
            (rI.rI_base.mult (base_loss s0)
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))
            (rI.rI_base.mult
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
              (base_loss s0))
            (rI.rI_base.mult_comm (base_loss s0)
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))))
    in
    id_trans
      (sO.sum_over_S (fun s0 ->
        mult0
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (mult0 (inv_pos0 t ht) (base_loss s0))))
      (sO.sum_over_S (fun s0 ->
        mult0 (inv_pos0 t ht)
          (mult0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            (base_loss s0))))
      (rI.rI_base.mult (inv_pos0 t ht)
        (sO.sum_over_S (fun s0 ->
          mult0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            (base_loss s0))))
      (sO.sum_over_S_ext (fun s0 ->
        mult0
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (mult0 (inv_pos0 t ht) (base_loss s0)))
        (fun s0 ->
        mult0 (inv_pos0 t ht)
          (mult0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            (base_loss s0)))
        hpt2)
      (sO.sum_over_S_linear (inv_pos0 t ht) (fun s0 ->
        mult0
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (base_loss s0)))
  in
  let hlin2 =
    let hpt3 = fun s0 ->
      rI.rI_base.mult_comm
        (mult0
          (inv_pos0 (z_temp t)
            (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
              t ht))
          (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
        (log0 (z_temp t))
    in
    id_trans
      (sO.sum_over_S (fun s0 ->
        mult0
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (log0 (z_temp t))))
      (sO.sum_over_S (fun s0 ->
        mult0 (log0 (z_temp t))
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))))
      (log0 (z_temp t))
      (sO.sum_over_S_ext (fun s0 ->
        mult0
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (log0 (z_temp t)))
        (fun s0 ->
        mult0 (log0 (z_temp t))
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))
        hpt3)
      (id_trans
        (sO.sum_over_S (fun s0 ->
          rI.rI_base.mult (log0 (z_temp t))
            (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
              z_temp_spec t ht s0)))
        (rI.rI_base.mult (log0 (z_temp t))
          (sO.sum_over_S
            (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
              z_temp_spec t ht)))
        (log0 (z_temp t))
        (sO.sum_over_S_linear (log0 (z_temp t))
          (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
            z_temp_spec t ht))
        (id_trans
          (mult0 (log0 (z_temp t))
            (sum_over_S0
              (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht)))
          (mult0 (log0 (z_temp t)) one0) (log0 (z_temp t))
          (id_cong (fun x -> mult0 (log0 (z_temp t)) x)
            (sum_over_S0
              (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            one0
            (boltzmann_dist_temp_normalized rI sS sO base_loss sum_over_S_pos
              z_temp z_temp_spec t ht))
          (rI.rI_base.mult_one (log0 (z_temp t)))))
  in
  id_trans
    (sum_over_S0 (fun s0 ->
      mult0
        (mult0
          (inv_pos0 (z_temp t)
            (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
              t ht))
          (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
        (rI.rI_base.opp
          (log0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))))))
    (sum_over_S0 (fun s0 ->
      plus0
        (mult0
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (mult0 (inv_pos0 t ht) (base_loss s0)))
        (mult0
          (mult0
            (inv_pos0 (z_temp t)
              (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t ht))
            (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
          (log0 (z_temp t)))))
    (plus0
      (mult0 (inv_pos0 t ht)
        (sum_over_S0 (fun s0 ->
          mult0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            (base_loss s0))))
      (log0 (z_temp t)))
    h1
    (id_trans
      (sum_over_S0 (fun s0 ->
        plus0
          (mult0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            (mult0 (inv_pos0 t ht) (base_loss s0)))
          (mult0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            (log0 (z_temp t)))))
      (plus0
        (sum_over_S0 (fun s0 ->
          mult0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            (mult0 (inv_pos0 t ht) (base_loss s0))))
        (sum_over_S0 (fun s0 ->
          mult0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
            (log0 (z_temp t)))))
      (plus0
        (mult0 (inv_pos0 t ht)
          (sum_over_S0 (fun s0 ->
            mult0
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
              (base_loss s0))))
        (log0 (z_temp t)))
      hadd
      (id_trans
        (plus0
          (sum_over_S0 (fun s0 ->
            mult0
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
              (mult0 (inv_pos0 t ht) (base_loss s0))))
          (sum_over_S0 (fun s0 ->
            mult0
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
              (log0 (z_temp t)))))
        (plus0
          (mult0 (inv_pos0 t ht)
            (sum_over_S0 (fun s0 ->
              mult0
                (mult0
                  (inv_pos0 (z_temp t)
                    (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                      z_temp_spec t ht))
                  (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
                (base_loss s0))))
          (sum_over_S0 (fun s0 ->
            mult0
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
              (log0 (z_temp t)))))
        (plus0
          (mult0 (inv_pos0 t ht)
            (sum_over_S0 (fun s0 ->
              mult0
                (mult0
                  (inv_pos0 (z_temp t)
                    (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                      z_temp_spec t ht))
                  (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
                (base_loss s0))))
          (log0 (z_temp t)))
        (id_cong (fun x ->
          plus0 x
            (sum_over_S0 (fun s0 ->
              mult0
                (mult0
                  (inv_pos0 (z_temp t)
                    (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                      z_temp_spec t ht))
                  (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
                (log0 (z_temp t)))))
          (sum_over_S0 (fun s0 ->
            mult0
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
              (mult0 (inv_pos0 t ht) (base_loss s0))))
          (mult0 (inv_pos0 t ht)
            (sum_over_S0 (fun s0 ->
              mult0
                (mult0
                  (inv_pos0 (z_temp t)
                    (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                      z_temp_spec t ht))
                  (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
                (base_loss s0))))
          hlin1)
        (id_cong (fun x ->
          plus0
            (mult0 (inv_pos0 t ht)
              (sum_over_S0 (fun s0 ->
                mult0
                  (mult0
                    (inv_pos0 (z_temp t)
                      (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                        z_temp_spec t ht))
                    (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
                  (base_loss s0))))
            x)
          (sum_over_S0 (fun s0 ->
            mult0
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))
              (log0 (z_temp t))))
          (log0 (z_temp t)) hlin2))))

(** val relative_entropy_temp_decomp :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> (s ->
    r) -> normalized -> r id **)

let relative_entropy_temp_decomp rI sS sO =
  let one0 = rI.rI_base.one in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let exp_neg0 = rI.rI_base.exp_neg in
  let log0 = rI.log in
  let sum_over_S0 = sO.sum_over_S in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec t ht q hnq ->
  let hpt = fun s0 ->
    mult_minus_distr_l rI (q s0) (log0 (q s0))
      (log0
        (mult0
          (inv_pos0 (z_temp t)
            (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
              t ht))
          (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))
  in
  let hq1 = entropy_neg_sum rI sS sO q in
  let hq2 =
    let hpt2 = fun s0 ->
      let hlog =
        boltzmann_log_temp_decomp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t ht s0
      in
      id_trans
        (mult0 (q s0)
          (log0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))))
        (mult0 (q s0)
          (plus0 (rI.rI_base.opp (log0 (z_temp t)))
            (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0)))))
        (rI.rI_base.plus (rI.rI_base.opp (mult0 (q s0) (log0 (z_temp t))))
          (rI.rI_base.opp
            (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0)))))
        (id_cong (fun x -> mult0 (q s0) x)
          (log0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))
          (plus0 (rI.rI_base.opp (log0 (z_temp t)))
            (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0))))
          hlog)
        (id_trans
          (mult0 (q s0)
            (rI.rI_base.plus (rI.rI_base.opp (log0 (z_temp t)))
              (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0)))))
          (mult0 (q s0)
            (rI.rI_base.plus
              (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0)))
              (rI.rI_base.opp (log0 (z_temp t)))))
          (rI.rI_base.plus (rI.rI_base.opp (mult0 (q s0) (log0 (z_temp t))))
            (rI.rI_base.opp
              (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0)))))
          (id_cong (fun x -> mult0 (q s0) x)
            (rI.rI_base.plus (rI.rI_base.opp (log0 (z_temp t)))
              (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0))))
            (rI.rI_base.plus
              (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0)))
              (rI.rI_base.opp (log0 (z_temp t))))
            (rI.rI_base.plus_comm (rI.rI_base.opp (log0 (z_temp t)))
              (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0)))))
          (id_trans
            (rI.rI_base.mult (q s0)
              (rI.rI_base.plus
                (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0)))
                (rI.rI_base.opp (log0 (z_temp t)))))
            (rI.rI_base.plus
              (rI.rI_base.mult (q s0)
                (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0))))
              (rI.rI_base.mult (q s0) (rI.rI_base.opp (log0 (z_temp t)))))
            (rI.rI_base.plus
              (rI.rI_base.opp (mult0 (q s0) (log0 (z_temp t))))
              (rI.rI_base.opp
                (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0)))))
            (rI.rI_base.distrib (q s0)
              (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0)))
              (rI.rI_base.opp (log0 (z_temp t))))
            (id_trans
              (plus0
                (rI.rI_base.mult (q s0)
                  (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0))))
                (mult0 (q s0) (rI.rI_base.opp (log0 (z_temp t)))))
              (plus0
                (rI.rI_base.opp
                  (rI.rI_base.mult (q s0)
                    (mult0 (inv_pos0 t ht) (base_loss s0))))
                (mult0 (q s0) (rI.rI_base.opp (log0 (z_temp t)))))
              (rI.rI_base.plus
                (rI.rI_base.opp (mult0 (q s0) (log0 (z_temp t))))
                (rI.rI_base.opp
                  (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0)))))
              (id_cong (fun x ->
                plus0 x (mult0 (q s0) (rI.rI_base.opp (log0 (z_temp t)))))
                (rI.rI_base.mult (q s0)
                  (rI.rI_base.opp (mult0 (inv_pos0 t ht) (base_loss s0))))
                (rI.rI_base.opp
                  (rI.rI_base.mult (q s0)
                    (mult0 (inv_pos0 t ht) (base_loss s0))))
                (opp_mult_l rI (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))
              (id_trans
                (plus0
                  (rI.rI_base.opp
                    (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))
                  (rI.rI_base.mult (q s0) (rI.rI_base.opp (log0 (z_temp t)))))
                (plus0
                  (rI.rI_base.opp
                    (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))
                  (rI.rI_base.opp (rI.rI_base.mult (q s0) (log0 (z_temp t)))))
                (rI.rI_base.plus
                  (rI.rI_base.opp (mult0 (q s0) (log0 (z_temp t))))
                  (rI.rI_base.opp
                    (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0)))))
                (id_cong (fun x ->
                  plus0
                    (rI.rI_base.opp
                      (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))
                    x)
                  (rI.rI_base.mult (q s0) (rI.rI_base.opp (log0 (z_temp t))))
                  (rI.rI_base.opp (rI.rI_base.mult (q s0) (log0 (z_temp t))))
                  (opp_mult_l rI (q s0) (log0 (z_temp t))))
                (rI.rI_base.plus_comm
                  (rI.rI_base.opp
                    (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))
                  (rI.rI_base.opp (mult0 (q s0) (log0 (z_temp t)))))))))
    in
    let h1 =
      sO.sum_over_S_ext (fun s0 ->
        mult0 (q s0)
          (log0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))))
        (fun s0 ->
        plus0 (rI.rI_base.opp (mult0 (q s0) (log0 (z_temp t))))
          (rI.rI_base.opp
            (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0)))))
        hpt2
    in
    let hadd =
      sO.sum_over_S_add (fun s0 ->
        rI.rI_base.opp (mult0 (q s0) (log0 (z_temp t)))) (fun s0 ->
        rI.rI_base.opp (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))
    in
    let hs1 =
      let hc = fun s0 -> rI.rI_base.mult_comm (q s0) (log0 (z_temp t)) in
      id_trans (sO.sum_over_S (fun s0 -> mult0 (q s0) (log0 (z_temp t))))
        (sO.sum_over_S (fun s0 -> mult0 (log0 (z_temp t)) (q s0)))
        (log0 (z_temp t))
        (sO.sum_over_S_ext (fun s0 -> mult0 (q s0) (log0 (z_temp t)))
          (fun s0 -> mult0 (log0 (z_temp t)) (q s0)) hc)
        (id_trans
          (sO.sum_over_S (fun s0 -> rI.rI_base.mult (log0 (z_temp t)) (q s0)))
          (rI.rI_base.mult (log0 (z_temp t)) (sO.sum_over_S q))
          (log0 (z_temp t)) (sO.sum_over_S_linear (log0 (z_temp t)) q)
          (id_trans (mult0 (log0 (z_temp t)) (sum_over_S0 q))
            (mult0 (log0 (z_temp t)) one0) (log0 (z_temp t))
            (id_cong (fun x -> mult0 (log0 (z_temp t)) x) (sum_over_S0 q)
              one0 hnq)
            (rI.rI_base.mult_one (log0 (z_temp t)))))
    in
    let hs2 =
      let hc2 = fun s0 ->
        id_trans
          (rI.rI_base.mult (q s0) (mult0 (inv_pos0 t ht) (base_loss s0)))
          (rI.rI_base.mult (mult0 (inv_pos0 t ht) (base_loss s0)) (q s0))
          (mult0 (inv_pos0 t ht) (rI.rI_base.mult (q s0) (base_loss s0)))
          (rI.rI_base.mult_comm (q s0) (mult0 (inv_pos0 t ht) (base_loss s0)))
          (id_trans
            (rI.rI_base.mult (rI.rI_base.mult (inv_pos0 t ht) (base_loss s0))
              (q s0))
            (rI.rI_base.mult (inv_pos0 t ht)
              (rI.rI_base.mult (base_loss s0) (q s0)))
            (mult0 (inv_pos0 t ht) (rI.rI_base.mult (q s0) (base_loss s0)))
            (id_sym
              (rI.rI_base.mult (inv_pos0 t ht)
                (rI.rI_base.mult (base_loss s0) (q s0)))
              (rI.rI_base.mult
                (rI.rI_base.mult (inv_pos0 t ht) (base_loss s0)) (q s0))
              (rI.rI_base.mult_assoc (inv_pos0 t ht) (base_loss s0) (q s0)))
            (id_cong (fun x -> mult0 (inv_pos0 t ht) x)
              (rI.rI_base.mult (base_loss s0) (q s0))
              (rI.rI_base.mult (q s0) (base_loss s0))
              (rI.rI_base.mult_comm (base_loss s0) (q s0))))
      in
      id_trans
        (sO.sum_over_S (fun s0 ->
          mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))
        (sO.sum_over_S (fun s0 ->
          mult0 (inv_pos0 t ht) (mult0 (q s0) (base_loss s0))))
        (rI.rI_base.mult (inv_pos0 t ht)
          (sO.sum_over_S (fun s0 -> mult0 (q s0) (base_loss s0))))
        (sO.sum_over_S_ext (fun s0 ->
          mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))) (fun s0 ->
          mult0 (inv_pos0 t ht) (mult0 (q s0) (base_loss s0))) hc2)
        (sO.sum_over_S_linear (inv_pos0 t ht) (fun s0 ->
          mult0 (q s0) (base_loss s0)))
    in
    id_trans
      (sum_over_S0 (fun s0 ->
        mult0 (q s0)
          (log0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))))
      (sum_over_S0 (fun s0 ->
        plus0 (rI.rI_base.opp (mult0 (q s0) (log0 (z_temp t))))
          (rI.rI_base.opp
            (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))))
      (rI.rI_base.plus
        (rI.rI_base.opp
          (mult0 (inv_pos0 t ht)
            (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
        (rI.rI_base.opp (log0 (z_temp t))))
      h1
      (id_trans
        (sum_over_S0 (fun s0 ->
          plus0 (rI.rI_base.opp (mult0 (q s0) (log0 (z_temp t))))
            (rI.rI_base.opp
              (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))))
        (plus0
          (sum_over_S0 (fun s0 ->
            rI.rI_base.opp (mult0 (q s0) (log0 (z_temp t)))))
          (sum_over_S0 (fun s0 ->
            rI.rI_base.opp
              (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))))
        (rI.rI_base.plus
          (rI.rI_base.opp
            (mult0 (inv_pos0 t ht)
              (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
          (rI.rI_base.opp (log0 (z_temp t))))
        hadd
        (id_trans
          (plus0
            (sum_over_S0 (fun s0 ->
              rI.rI_base.opp (mult0 (q s0) (log0 (z_temp t)))))
            (sum_over_S0 (fun s0 ->
              rI.rI_base.opp
                (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))))
          (plus0
            (rI.rI_base.opp
              (sum_over_S0 (fun s0 -> mult0 (q s0) (log0 (z_temp t)))))
            (sum_over_S0 (fun s0 ->
              rI.rI_base.opp
                (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))))
          (rI.rI_base.plus
            (rI.rI_base.opp
              (mult0 (inv_pos0 t ht)
                (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
            (rI.rI_base.opp (log0 (z_temp t))))
          (id_cong (fun x ->
            plus0 x
              (sum_over_S0 (fun s0 ->
                rI.rI_base.opp
                  (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))))
            (sum_over_S0 (fun s0 ->
              rI.rI_base.opp (mult0 (q s0) (log0 (z_temp t)))))
            (rI.rI_base.opp
              (sum_over_S0 (fun s0 -> mult0 (q s0) (log0 (z_temp t)))))
            (sum_opp rI sS sO (fun s0 -> mult0 (q s0) (log0 (z_temp t)))))
          (id_trans
            (plus0
              (rI.rI_base.opp
                (sum_over_S0 (fun s0 -> mult0 (q s0) (log0 (z_temp t)))))
              (sum_over_S0 (fun s0 ->
                rI.rI_base.opp
                  (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))))
            (plus0
              (rI.rI_base.opp
                (sum_over_S0 (fun s0 -> mult0 (q s0) (log0 (z_temp t)))))
              (rI.rI_base.opp
                (sum_over_S0 (fun s0 ->
                  mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))))
            (rI.rI_base.plus
              (rI.rI_base.opp
                (mult0 (inv_pos0 t ht)
                  (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
              (rI.rI_base.opp (log0 (z_temp t))))
            (id_cong (fun x ->
              plus0
                (rI.rI_base.opp
                  (sum_over_S0 (fun s0 -> mult0 (q s0) (log0 (z_temp t)))))
                x)
              (sum_over_S0 (fun s0 ->
                rI.rI_base.opp
                  (mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0)))))
              (rI.rI_base.opp
                (sum_over_S0 (fun s0 ->
                  mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0)))))
              (sum_opp rI sS sO (fun s0 ->
                mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0)))))
            (id_trans
              (plus0
                (rI.rI_base.opp
                  (sum_over_S0 (fun s0 -> mult0 (q s0) (log0 (z_temp t)))))
                (rI.rI_base.opp
                  (sum_over_S0 (fun s0 ->
                    mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))))
              (plus0 (rI.rI_base.opp (log0 (z_temp t)))
                (rI.rI_base.opp
                  (sum_over_S0 (fun s0 ->
                    mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))))
              (rI.rI_base.plus
                (rI.rI_base.opp
                  (mult0 (inv_pos0 t ht)
                    (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
                (rI.rI_base.opp (log0 (z_temp t))))
              (id_cong (fun x ->
                plus0 (rI.rI_base.opp x)
                  (rI.rI_base.opp
                    (sum_over_S0 (fun s0 ->
                      mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))))
                (sum_over_S0 (fun s0 -> mult0 (q s0) (log0 (z_temp t))))
                (log0 (z_temp t)) hs1)
              (id_trans
                (plus0 (rI.rI_base.opp (log0 (z_temp t)))
                  (rI.rI_base.opp
                    (sum_over_S0 (fun s0 ->
                      mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))))
                (plus0 (rI.rI_base.opp (log0 (z_temp t)))
                  (rI.rI_base.opp
                    (mult0 (inv_pos0 t ht)
                      (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0))))))
                (rI.rI_base.plus
                  (rI.rI_base.opp
                    (mult0 (inv_pos0 t ht)
                      (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
                  (rI.rI_base.opp (log0 (z_temp t))))
                (id_cong (fun x ->
                  plus0 (rI.rI_base.opp (log0 (z_temp t))) (rI.rI_base.opp x))
                  (sum_over_S0 (fun s0 ->
                    mult0 (q s0) (mult0 (inv_pos0 t ht) (base_loss s0))))
                  (mult0 (inv_pos0 t ht)
                    (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0))))
                  hs2)
                (rI.rI_base.plus_comm (rI.rI_base.opp (log0 (z_temp t)))
                  (rI.rI_base.opp
                    (mult0 (inv_pos0 t ht)
                      (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))))))))
  in
  let hopp =
    id_trans
      (rI.rI_base.opp
        (rI.rI_base.plus
          (rI.rI_base.opp
            (mult0 (inv_pos0 t ht)
              (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
          (rI.rI_base.opp (log0 (z_temp t)))))
      (rI.rI_base.plus
        (rI.rI_base.opp
          (rI.rI_base.opp
            (mult0 (inv_pos0 t ht)
              (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0))))))
        (rI.rI_base.opp (rI.rI_base.opp (log0 (z_temp t)))))
      (plus0
        (mult0 (inv_pos0 t ht)
          (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0))))
        (log0 (z_temp t)))
      (opp_plus rI
        (rI.rI_base.opp
          (mult0 (inv_pos0 t ht)
            (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
        (rI.rI_base.opp (log0 (z_temp t))))
      (id_trans
        (plus0
          (rI.rI_base.opp
            (rI.rI_base.opp
              (mult0 (inv_pos0 t ht)
                (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0))))))
          (rI.rI_base.opp (rI.rI_base.opp (log0 (z_temp t)))))
        (plus0
          (mult0 (inv_pos0 t ht)
            (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0))))
          (rI.rI_base.opp (rI.rI_base.opp (log0 (z_temp t)))))
        (plus0
          (mult0 (inv_pos0 t ht)
            (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0))))
          (log0 (z_temp t)))
        (id_cong (fun x ->
          plus0 x (rI.rI_base.opp (rI.rI_base.opp (log0 (z_temp t)))))
          (rI.rI_base.opp
            (rI.rI_base.opp
              (mult0 (inv_pos0 t ht)
                (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0))))))
          (mult0 (inv_pos0 t ht)
            (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0))))
          (double_neg rI
            (mult0 (inv_pos0 t ht)
              (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0))))))
        (id_cong (fun x ->
          plus0
            (mult0 (inv_pos0 t ht)
              (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0))))
            x)
          (rI.rI_base.opp (rI.rI_base.opp (log0 (z_temp t))))
          (log0 (z_temp t)) (double_neg rI (log0 (z_temp t)))))
  in
  let hfin =
    id_trans
      (plus0 (sum_over_S0 (fun s0 -> mult0 (q s0) (log0 (q s0))))
        (rI.rI_base.opp
          (sum_over_S0 (fun s0 ->
            mult0 (q s0)
              (log0
                (mult0
                  (inv_pos0 (z_temp t)
                    (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                      z_temp_spec t ht))
                  (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))))))
      (plus0 (rI.rI_base.opp (entropy_dist rI sS sO q))
        (rI.rI_base.opp
          (sum_over_S0 (fun s0 ->
            mult0 (q s0)
              (log0
                (mult0
                  (inv_pos0 (z_temp t)
                    (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                      z_temp_spec t ht))
                  (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))))))
      (rI.rI_base.plus
        (rI.rI_base.plus (rI.rI_base.opp (entropy_dist rI sS sO q))
          (mult0 (inv_pos0 t ht)
            (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
        (log0 (z_temp t)))
      (id_cong (fun x ->
        plus0 x
          (rI.rI_base.opp
            (sum_over_S0 (fun s0 ->
              mult0 (q s0)
                (log0
                  (mult0
                    (inv_pos0 (z_temp t)
                      (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                        z_temp_spec t ht))
                    (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))))))
        (sum_over_S0 (fun s0 -> mult0 (q s0) (log0 (q s0))))
        (rI.rI_base.opp (entropy_dist rI sS sO q)) hq1)
      (id_trans
        (plus0 (rI.rI_base.opp (entropy_dist rI sS sO q))
          (rI.rI_base.opp
            (sum_over_S0 (fun s0 ->
              mult0 (q s0)
                (log0
                  (mult0
                    (inv_pos0 (z_temp t)
                      (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                        z_temp_spec t ht))
                    (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))))))
        (plus0 (rI.rI_base.opp (entropy_dist rI sS sO q))
          (rI.rI_base.opp
            (plus0
              (rI.rI_base.opp
                (mult0 (inv_pos0 t ht)
                  (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
              (rI.rI_base.opp (log0 (z_temp t))))))
        (rI.rI_base.plus
          (rI.rI_base.plus (rI.rI_base.opp (entropy_dist rI sS sO q))
            (mult0 (inv_pos0 t ht)
              (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
          (log0 (z_temp t)))
        (id_cong (fun x ->
          plus0 (rI.rI_base.opp (entropy_dist rI sS sO q)) (rI.rI_base.opp x))
          (sum_over_S0 (fun s0 ->
            mult0 (q s0)
              (log0
                (mult0
                  (inv_pos0 (z_temp t)
                    (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                      z_temp_spec t ht))
                  (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))))
          (plus0
            (rI.rI_base.opp
              (mult0 (inv_pos0 t ht)
                (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
            (rI.rI_base.opp (log0 (z_temp t))))
          hq2)
        (id_trans
          (plus0 (rI.rI_base.opp (entropy_dist rI sS sO q))
            (rI.rI_base.opp
              (plus0
                (rI.rI_base.opp
                  (mult0 (inv_pos0 t ht)
                    (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
                (rI.rI_base.opp (log0 (z_temp t))))))
          (plus0 (rI.rI_base.opp (entropy_dist rI sS sO q))
            (plus0
              (mult0 (inv_pos0 t ht)
                (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0))))
              (log0 (z_temp t))))
          (rI.rI_base.plus
            (rI.rI_base.plus (rI.rI_base.opp (entropy_dist rI sS sO q))
              (mult0 (inv_pos0 t ht)
                (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
            (log0 (z_temp t)))
          (id_cong (fun x ->
            plus0 (rI.rI_base.opp (entropy_dist rI sS sO q)) x)
            (rI.rI_base.opp
              (plus0
                (rI.rI_base.opp
                  (mult0 (inv_pos0 t ht)
                    (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
                (rI.rI_base.opp (log0 (z_temp t)))))
            (plus0
              (mult0 (inv_pos0 t ht)
                (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0))))
              (log0 (z_temp t)))
            hopp)
          (rI.rI_base.plus_assoc (rI.rI_base.opp (entropy_dist rI sS sO q))
            (mult0 (inv_pos0 t ht)
              (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0))))
            (log0 (z_temp t)))))
  in
  let hstep =
    sO.sum_over_S_ext (fun s0 ->
      mult0 (q s0)
        (minus rI.rI_base (log0 (q s0))
          (log0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))))
      (fun s0 ->
      minus rI.rI_base (mult0 (q s0) (log0 (q s0)))
        (mult0 (q s0)
          (log0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))))
      hpt
  in
  id_trans
    (sum_over_S0 (fun s0 ->
      mult0 (q s0)
        (minus rI.rI_base (log0 (q s0))
          (log0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))))))
    (sum_over_S0 (fun s0 ->
      minus rI.rI_base (mult0 (q s0) (log0 (q s0)))
        (mult0 (q s0)
          (log0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))))))
    (plus0
      (plus0 (rI.rI_base.opp (entropy_dist rI sS sO q))
        (mult0 (inv_pos0 t ht)
          (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
      (log0 (z_temp t)))
    hstep
    (id_trans
      (sum_over_S0 (fun s0 ->
        minus rI.rI_base (mult0 (q s0) (log0 (q s0)))
          (mult0 (q s0)
            (log0
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))))))
      (minus rI.rI_base (sum_over_S0 (fun s0 -> mult0 (q s0) (log0 (q s0))))
        (sum_over_S0 (fun s0 ->
          mult0 (q s0)
            (log0
              (mult0
                (inv_pos0 (z_temp t)
                  (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                    z_temp_spec t ht))
                (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0))))))))
      (plus0
        (plus0 (rI.rI_base.opp (entropy_dist rI sS sO q))
          (mult0 (inv_pos0 t ht)
            (sum_over_S0 (fun s0 -> mult0 (q s0) (base_loss s0)))))
        (log0 (z_temp t)))
      (sum_over_S_minus rI sS sO (fun s0 -> mult0 (q s0) (log0 (q s0)))
        (fun s0 ->
        mult0 (q s0)
          (log0
            (mult0
              (inv_pos0 (z_temp t)
                (z_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
                  z_temp_spec t ht))
              (exp_neg0 (mult0 (inv_pos0 t ht) (base_loss s0)))))))
      hfin))

(** val variational_temp_bound :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> (s ->
    r) -> normalized -> positive_dist -> le **)

let variational_temp_bound rI sS sO =
  let zero0 = rI.rI_base.zero in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let log0 = rI.log in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec ->
  let internal_Id_rew = fun _ f _ _ -> f in
  (fun t ht q hnq hpq ->
  let hkl =
    gibbs_inequality rI sS sO q
      (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t ht)
      hnq hpq
      (boltzmann_dist_temp_normalized rI sS sO base_loss sum_over_S_pos
        z_temp z_temp_spec t ht)
      (boltzmann_dist_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t ht)
  in
  let hrel =
    relative_entropy_temp_decomp rI sS sO base_loss sum_over_S_pos z_temp
      z_temp_spec t ht q hnq
  in
  let hkl0 =
    internal_Id_rew
      (relative_entropy rI sS sO q
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t ht))
      hkl
      (plus0
        (plus0 (rI.rI_base.opp (entropy_dist rI sS sO q))
          (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q)))
        (log0 (z_temp t)))
      hrel
  in
  let hstep1 =
    rI.rI_base.le_id_l (entropy_dist rI sS sO q)
      (plus0 (entropy_dist rI sS sO q) zero0)
      (plus0
        (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
        (log0 (z_temp t)))
      (id_sym (rI.rI_base.plus (entropy_dist rI sS sO q) rI.rI_base.zero)
        (entropy_dist rI sS sO q)
        (rI.rI_base.plus_zero (entropy_dist rI sS sO q)))
      (rI.rI_base.le_id_r (plus0 (entropy_dist rI sS sO q) zero0)
        (plus0 (entropy_dist rI sS sO q)
          (plus0
            (plus0 (rI.rI_base.opp (entropy_dist rI sS sO q))
              (mult0 (inv_pos0 t ht)
                (energy_expectation rI sS sO base_loss q)))
            (log0 (z_temp t))))
        (plus0
          (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
          (log0 (z_temp t)))
        (id_trans
          (rI.rI_base.plus (entropy_dist rI sS sO q)
            (rI.rI_base.plus
              (plus0 (rI.rI_base.opp (entropy_dist rI sS sO q))
                (mult0 (inv_pos0 t ht)
                  (energy_expectation rI sS sO base_loss q)))
              (log0 (z_temp t))))
          (rI.rI_base.plus
            (rI.rI_base.plus (entropy_dist rI sS sO q)
              (plus0 (rI.rI_base.opp (entropy_dist rI sS sO q))
                (mult0 (inv_pos0 t ht)
                  (energy_expectation rI sS sO base_loss q))))
            (log0 (z_temp t)))
          (plus0
            (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
            (log0 (z_temp t)))
          (rI.rI_base.plus_assoc (entropy_dist rI sS sO q)
            (plus0 (rI.rI_base.opp (entropy_dist rI sS sO q))
              (mult0 (inv_pos0 t ht)
                (energy_expectation rI sS sO base_loss q)))
            (log0 (z_temp t)))
          (id_trans
            (plus0
              (rI.rI_base.plus (entropy_dist rI sS sO q)
                (rI.rI_base.plus (rI.rI_base.opp (entropy_dist rI sS sO q))
                  (mult0 (inv_pos0 t ht)
                    (energy_expectation rI sS sO base_loss q))))
              (log0 (z_temp t)))
            (plus0
              (rI.rI_base.plus
                (rI.rI_base.plus (entropy_dist rI sS sO q)
                  (rI.rI_base.opp (entropy_dist rI sS sO q)))
                (mult0 (inv_pos0 t ht)
                  (energy_expectation rI sS sO base_loss q)))
              (log0 (z_temp t)))
            (plus0
              (mult0 (inv_pos0 t ht)
                (energy_expectation rI sS sO base_loss q))
              (log0 (z_temp t)))
            (id_cong (fun x -> plus0 x (log0 (z_temp t)))
              (rI.rI_base.plus (entropy_dist rI sS sO q)
                (rI.rI_base.plus (rI.rI_base.opp (entropy_dist rI sS sO q))
                  (mult0 (inv_pos0 t ht)
                    (energy_expectation rI sS sO base_loss q))))
              (rI.rI_base.plus
                (rI.rI_base.plus (entropy_dist rI sS sO q)
                  (rI.rI_base.opp (entropy_dist rI sS sO q)))
                (mult0 (inv_pos0 t ht)
                  (energy_expectation rI sS sO base_loss q)))
              (rI.rI_base.plus_assoc (entropy_dist rI sS sO q)
                (rI.rI_base.opp (entropy_dist rI sS sO q))
                (mult0 (inv_pos0 t ht)
                  (energy_expectation rI sS sO base_loss q))))
            (id_trans
              (plus0
                (plus0
                  (rI.rI_base.plus (entropy_dist rI sS sO q)
                    (rI.rI_base.opp (entropy_dist rI sS sO q)))
                  (mult0 (inv_pos0 t ht)
                    (energy_expectation rI sS sO base_loss q)))
                (log0 (z_temp t)))
              (plus0
                (plus0 rI.rI_base.zero
                  (mult0 (inv_pos0 t ht)
                    (energy_expectation rI sS sO base_loss q)))
                (log0 (z_temp t)))
              (plus0
                (mult0 (inv_pos0 t ht)
                  (energy_expectation rI sS sO base_loss q))
                (log0 (z_temp t)))
              (id_cong (fun x -> plus0 x (log0 (z_temp t)))
                (plus0
                  (rI.rI_base.plus (entropy_dist rI sS sO q)
                    (rI.rI_base.opp (entropy_dist rI sS sO q)))
                  (mult0 (inv_pos0 t ht)
                    (energy_expectation rI sS sO base_loss q)))
                (plus0 rI.rI_base.zero
                  (mult0 (inv_pos0 t ht)
                    (energy_expectation rI sS sO base_loss q)))
                (id_cong (fun x ->
                  plus0 x
                    (mult0 (inv_pos0 t ht)
                      (energy_expectation rI sS sO base_loss q)))
                  (rI.rI_base.plus (entropy_dist rI sS sO q)
                    (rI.rI_base.opp (entropy_dist rI sS sO q)))
                  rI.rI_base.zero
                  (rI.rI_base.plus_opp (entropy_dist rI sS sO q))))
              (id_cong (fun x -> plus0 x (log0 (z_temp t)))
                (rI.rI_base.plus zero0
                  (mult0 (inv_pos0 t ht)
                    (energy_expectation rI sS sO base_loss q)))
                (mult0 (inv_pos0 t ht)
                  (energy_expectation rI sS sO base_loss q))
                (id_trans
                  (rI.rI_base.plus zero0
                    (mult0 (inv_pos0 t ht)
                      (energy_expectation rI sS sO base_loss q)))
                  (rI.rI_base.plus
                    (mult0 (inv_pos0 t ht)
                      (energy_expectation rI sS sO base_loss q))
                    zero0)
                  (mult0 (inv_pos0 t ht)
                    (energy_expectation rI sS sO base_loss q))
                  (rI.rI_base.plus_comm zero0
                    (mult0 (inv_pos0 t ht)
                      (energy_expectation rI sS sO base_loss q)))
                  (rI.rI_base.plus_zero
                    (mult0 (inv_pos0 t ht)
                      (energy_expectation rI sS sO base_loss q))))))))
        (rI.le_plus_compat (entropy_dist rI sS sO q)
          (entropy_dist rI sS sO q) zero0
          (plus0
            (plus0 (rI.rI_base.opp (entropy_dist rI sS sO q))
              (mult0 (inv_pos0 t ht)
                (energy_expectation rI sS sO base_loss q)))
            (log0 (z_temp t)))
          (rI.rI_base.le_refl (entropy_dist rI sS sO q)) hkl0))
  in
  rI.rI_base.le_id_r
    (plus0 (entropy_dist rI sS sO q)
      (rI.rI_base.opp
        (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))))
    (plus0
      (plus0
        (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
        (log0 (z_temp t)))
      (rI.rI_base.opp
        (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))))
    (log0 (z_temp t))
    (id_trans
      (rI.rI_base.plus
        (rI.rI_base.plus
          (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
          (log0 (z_temp t)))
        (rI.rI_base.opp
          (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))))
      (rI.rI_base.plus
        (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
        (rI.rI_base.plus (log0 (z_temp t))
          (rI.rI_base.opp
            (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q)))))
      (log0 (z_temp t))
      (id_sym
        (rI.rI_base.plus
          (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
          (rI.rI_base.plus (log0 (z_temp t))
            (rI.rI_base.opp
              (mult0 (inv_pos0 t ht)
                (energy_expectation rI sS sO base_loss q)))))
        (rI.rI_base.plus
          (rI.rI_base.plus
            (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
            (log0 (z_temp t)))
          (rI.rI_base.opp
            (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))))
        (rI.rI_base.plus_assoc
          (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
          (log0 (z_temp t))
          (rI.rI_base.opp
            (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q)))))
      (id_trans
        (plus0
          (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
          (rI.rI_base.plus (log0 (z_temp t))
            (rI.rI_base.opp
              (mult0 (inv_pos0 t ht)
                (energy_expectation rI sS sO base_loss q)))))
        (plus0
          (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
          (rI.rI_base.plus
            (rI.rI_base.opp
              (mult0 (inv_pos0 t ht)
                (energy_expectation rI sS sO base_loss q)))
            (log0 (z_temp t))))
        (log0 (z_temp t))
        (id_cong (fun x ->
          plus0
            (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
            x)
          (rI.rI_base.plus (log0 (z_temp t))
            (rI.rI_base.opp
              (mult0 (inv_pos0 t ht)
                (energy_expectation rI sS sO base_loss q))))
          (rI.rI_base.plus
            (rI.rI_base.opp
              (mult0 (inv_pos0 t ht)
                (energy_expectation rI sS sO base_loss q)))
            (log0 (z_temp t)))
          (rI.rI_base.plus_comm (log0 (z_temp t))
            (rI.rI_base.opp
              (mult0 (inv_pos0 t ht)
                (energy_expectation rI sS sO base_loss q)))))
        (id_trans
          (rI.rI_base.plus
            (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
            (rI.rI_base.plus
              (rI.rI_base.opp
                (mult0 (inv_pos0 t ht)
                  (energy_expectation rI sS sO base_loss q)))
              (log0 (z_temp t))))
          (rI.rI_base.plus
            (rI.rI_base.plus
              (mult0 (inv_pos0 t ht)
                (energy_expectation rI sS sO base_loss q))
              (rI.rI_base.opp
                (mult0 (inv_pos0 t ht)
                  (energy_expectation rI sS sO base_loss q))))
            (log0 (z_temp t)))
          (log0 (z_temp t))
          (rI.rI_base.plus_assoc
            (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
            (rI.rI_base.opp
              (mult0 (inv_pos0 t ht)
                (energy_expectation rI sS sO base_loss q)))
            (log0 (z_temp t)))
          (id_trans
            (plus0
              (rI.rI_base.plus
                (mult0 (inv_pos0 t ht)
                  (energy_expectation rI sS sO base_loss q))
                (rI.rI_base.opp
                  (mult0 (inv_pos0 t ht)
                    (energy_expectation rI sS sO base_loss q))))
              (log0 (z_temp t)))
            (plus0 rI.rI_base.zero (log0 (z_temp t))) (log0 (z_temp t))
            (id_cong (fun x -> plus0 x (log0 (z_temp t)))
              (rI.rI_base.plus
                (mult0 (inv_pos0 t ht)
                  (energy_expectation rI sS sO base_loss q))
                (rI.rI_base.opp
                  (mult0 (inv_pos0 t ht)
                    (energy_expectation rI sS sO base_loss q))))
              rI.rI_base.zero
              (rI.rI_base.plus_opp
                (mult0 (inv_pos0 t ht)
                  (energy_expectation rI sS sO base_loss q))))
            (id_trans (rI.rI_base.plus zero0 (log0 (z_temp t)))
              (rI.rI_base.plus (log0 (z_temp t)) zero0) (log0 (z_temp t))
              (rI.rI_base.plus_comm zero0 (log0 (z_temp t)))
              (rI.rI_base.plus_zero (log0 (z_temp t))))))))
    (rI.le_plus_compat (entropy_dist rI sS sO q)
      (plus0
        (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q))
        (log0 (z_temp t)))
      (rI.rI_base.opp
        (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q)))
      (rI.rI_base.opp
        (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q)))
      hstep1
      (rI.rI_base.le_refl
        (rI.rI_base.opp
          (mult0 (inv_pos0 t ht) (energy_expectation rI sS sO base_loss q)))))))

(** val energy_exp_temp_mono :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r -> lt -> lt -> lt -> lt) -> (r -> r -> lt
    -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> r -> lt -> lt -> lt -> le **)

let energy_exp_temp_mono rI sS sO =
  let zero0 = rI.rI_base.zero in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let log0 = rI.log in
  (fun base_loss sum_over_S_pos inv_pos_lt_compat lt_minus_nonneg z_temp z_temp_spec t1 t2 ht1 ht2 ht12 ->
  let b1 = inv_pos0 t1 ht1 in
  let b2 = inv_pos0 t2 ht2 in
  let e1 =
    energy_exp_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t1
      ht1
  in
  let e2 =
    energy_exp_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t2
      ht2
  in
  let h1 =
    entropy_dist rI sS sO
      (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t1 ht1)
  in
  let h2 =
    entropy_dist rI sS sO
      (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t2 ht2)
  in
  let z1 = z_temp t1 in
  let z2 = z_temp t2 in
  let hb = inv_pos_lt_compat t1 t2 ht1 ht2 ht12 in
  let hbpos = lt_minus_nonneg b2 b1 hb in
  let hv1 =
    variational_temp_bound rI sS sO base_loss sum_over_S_pos z_temp
      z_temp_spec t1 ht1
      (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t2 ht2)
      (boltzmann_dist_temp_normalized rI sS sO base_loss sum_over_S_pos
        z_temp z_temp_spec t2 ht2)
      (fun s0 ->
      boltzmann_dist_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t2 ht2 s0)
  in
  let hv2 =
    variational_temp_bound rI sS sO base_loss sum_over_S_pos z_temp
      z_temp_spec t2 ht2
      (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t1 ht1)
      (boltzmann_dist_temp_normalized rI sS sO base_loss sum_over_S_pos
        z_temp z_temp_spec t1 ht1)
      (fun s0 ->
      boltzmann_dist_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t1 ht1 s0)
  in
  let hex1 =
    entropy_temp_explicit rI sS sO base_loss sum_over_S_pos z_temp
      z_temp_spec t1 ht1
  in
  let hex2 =
    entropy_temp_explicit rI sS sO base_loss sum_over_S_pos z_temp
      z_temp_spec t2 ht2
  in
  let hv1' =
    rI.rI_base.le_id_l
      (minus rI.rI_base (plus0 (mult0 b2 e2) (log0 z2)) (mult0 b1 e2))
      (minus rI.rI_base h2 (mult0 b1 e2)) (log0 z1)
      (id_cong (fun x -> minus rI.rI_base x (mult0 b1 e2))
        (plus0 (mult0 b2 e2) (log0 z2)) h2
        (id_sym h2 (plus0 (mult0 b2 e2) (log0 z2)) hex2))
      hv1
  in
  let hv2' =
    rI.rI_base.le_id_l
      (minus rI.rI_base (plus0 (mult0 b1 e1) (log0 z1)) (mult0 b2 e1))
      (minus rI.rI_base h1 (mult0 b2 e1)) (log0 z2)
      (id_cong (fun x -> minus rI.rI_base x (mult0 b2 e1))
        (plus0 (mult0 b1 e1) (log0 z1)) h1
        (id_sym h1 (plus0 (mult0 b1 e1) (log0 z1)) hex1))
      hv2
  in
  let hm1 =
    id_trans
      (rI.rI_base.plus (rI.rI_base.plus (mult0 b2 e2) (log0 z2))
        (rI.rI_base.opp (mult0 b1 e2)))
      (rI.rI_base.plus (mult0 b2 e2)
        (rI.rI_base.plus (log0 z2) (rI.rI_base.opp (mult0 b1 e2))))
      (plus0 (mult0 (minus rI.rI_base b2 b1) e2) (log0 z2))
      (id_sym
        (rI.rI_base.plus (mult0 b2 e2)
          (rI.rI_base.plus (log0 z2) (rI.rI_base.opp (mult0 b1 e2))))
        (rI.rI_base.plus (rI.rI_base.plus (mult0 b2 e2) (log0 z2))
          (rI.rI_base.opp (mult0 b1 e2)))
        (rI.rI_base.plus_assoc (mult0 b2 e2) (log0 z2)
          (rI.rI_base.opp (mult0 b1 e2))))
      (id_trans
        (plus0 (mult0 b2 e2)
          (rI.rI_base.plus (log0 z2) (rI.rI_base.opp (mult0 b1 e2))))
        (plus0 (mult0 b2 e2)
          (rI.rI_base.plus (rI.rI_base.opp (mult0 b1 e2)) (log0 z2)))
        (plus0 (mult0 (minus rI.rI_base b2 b1) e2) (log0 z2))
        (id_cong (fun x -> plus0 (mult0 b2 e2) x)
          (rI.rI_base.plus (log0 z2) (rI.rI_base.opp (mult0 b1 e2)))
          (rI.rI_base.plus (rI.rI_base.opp (mult0 b1 e2)) (log0 z2))
          (rI.rI_base.plus_comm (log0 z2) (rI.rI_base.opp (mult0 b1 e2))))
        (id_trans
          (rI.rI_base.plus (mult0 b2 e2)
            (rI.rI_base.plus (rI.rI_base.opp (mult0 b1 e2)) (log0 z2)))
          (rI.rI_base.plus
            (rI.rI_base.plus (mult0 b2 e2) (rI.rI_base.opp (mult0 b1 e2)))
            (log0 z2))
          (plus0 (mult0 (minus rI.rI_base b2 b1) e2) (log0 z2))
          (rI.rI_base.plus_assoc (mult0 b2 e2) (rI.rI_base.opp (mult0 b1 e2))
            (log0 z2))
          (id_sym (plus0 (mult0 (minus rI.rI_base b2 b1) e2) (log0 z2))
            (plus0 (minus rI.rI_base (mult0 b2 e2) (mult0 b1 e2)) (log0 z2))
            (id_cong (fun x -> plus0 x (log0 z2))
              (mult0 (minus rI.rI_base b2 b1) e2)
              (minus rI.rI_base (mult0 b2 e2) (mult0 b1 e2))
              (mult_minus_distr_r rI b2 b1 e2)))))
  in
  let hm2 =
    id_trans
      (rI.rI_base.plus (rI.rI_base.plus (mult0 b1 e1) (log0 z1))
        (rI.rI_base.opp (mult0 b2 e1)))
      (rI.rI_base.plus (mult0 b1 e1)
        (rI.rI_base.plus (log0 z1) (rI.rI_base.opp (mult0 b2 e1))))
      (plus0 (mult0 (minus rI.rI_base b1 b2) e1) (log0 z1))
      (id_sym
        (rI.rI_base.plus (mult0 b1 e1)
          (rI.rI_base.plus (log0 z1) (rI.rI_base.opp (mult0 b2 e1))))
        (rI.rI_base.plus (rI.rI_base.plus (mult0 b1 e1) (log0 z1))
          (rI.rI_base.opp (mult0 b2 e1)))
        (rI.rI_base.plus_assoc (mult0 b1 e1) (log0 z1)
          (rI.rI_base.opp (mult0 b2 e1))))
      (id_trans
        (plus0 (mult0 b1 e1)
          (rI.rI_base.plus (log0 z1) (rI.rI_base.opp (mult0 b2 e1))))
        (plus0 (mult0 b1 e1)
          (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e1)) (log0 z1)))
        (plus0 (mult0 (minus rI.rI_base b1 b2) e1) (log0 z1))
        (id_cong (fun x -> plus0 (mult0 b1 e1) x)
          (rI.rI_base.plus (log0 z1) (rI.rI_base.opp (mult0 b2 e1)))
          (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e1)) (log0 z1))
          (rI.rI_base.plus_comm (log0 z1) (rI.rI_base.opp (mult0 b2 e1))))
        (id_trans
          (rI.rI_base.plus (mult0 b1 e1)
            (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e1)) (log0 z1)))
          (rI.rI_base.plus
            (rI.rI_base.plus (mult0 b1 e1) (rI.rI_base.opp (mult0 b2 e1)))
            (log0 z1))
          (plus0 (mult0 (minus rI.rI_base b1 b2) e1) (log0 z1))
          (rI.rI_base.plus_assoc (mult0 b1 e1) (rI.rI_base.opp (mult0 b2 e1))
            (log0 z1))
          (id_sym (plus0 (mult0 (minus rI.rI_base b1 b2) e1) (log0 z1))
            (plus0 (minus rI.rI_base (mult0 b1 e1) (mult0 b2 e1)) (log0 z1))
            (id_cong (fun x -> plus0 x (log0 z1))
              (mult0 (minus rI.rI_base b1 b2) e1)
              (minus rI.rI_base (mult0 b1 e1) (mult0 b2 e1))
              (mult_minus_distr_r rI b1 b2 e1)))))
  in
  let hv1'' =
    rI.rI_base.le_id_l (plus0 (mult0 (minus rI.rI_base b2 b1) e2) (log0 z2))
      (minus rI.rI_base (plus0 (mult0 b2 e2) (log0 z2)) (mult0 b1 e2))
      (log0 z1)
      (id_sym
        (minus rI.rI_base (plus0 (mult0 b2 e2) (log0 z2)) (mult0 b1 e2))
        (plus0 (mult0 (minus rI.rI_base b2 b1) e2) (log0 z2)) hm1)
      hv1'
  in
  let hv2'' =
    rI.rI_base.le_id_l (plus0 (mult0 (minus rI.rI_base b1 b2) e1) (log0 z1))
      (minus rI.rI_base (plus0 (mult0 b1 e1) (log0 z1)) (mult0 b2 e1))
      (log0 z2)
      (id_sym
        (minus rI.rI_base (plus0 (mult0 b1 e1) (log0 z1)) (mult0 b2 e1))
        (plus0 (mult0 (minus rI.rI_base b1 b2) e1) (log0 z1)) hm2)
      hv2'
  in
  let hshift1 =
    rI.rI_base.le_id_l (mult0 (minus rI.rI_base b2 b1) e2)
      (plus0 (plus0 (mult0 (minus rI.rI_base b2 b1) e2) (log0 z2))
        (rI.rI_base.opp (log0 z2)))
      (minus rI.rI_base (log0 z1) (log0 z2))
      (id_trans (mult0 (minus rI.rI_base b2 b1) e2)
        (rI.rI_base.plus (mult0 (minus rI.rI_base b2 b1) e2) rI.rI_base.zero)
        (rI.rI_base.plus
          (rI.rI_base.plus (mult0 (minus rI.rI_base b2 b1) e2) (log0 z2))
          (rI.rI_base.opp (log0 z2)))
        (id_sym
          (rI.rI_base.plus (mult0 (minus rI.rI_base b2 b1) e2)
            rI.rI_base.zero)
          (mult0 (minus rI.rI_base b2 b1) e2)
          (rI.rI_base.plus_zero (mult0 (minus rI.rI_base b2 b1) e2)))
        (id_sym
          (rI.rI_base.plus
            (rI.rI_base.plus (mult0 (minus rI.rI_base b2 b1) e2) (log0 z2))
            (rI.rI_base.opp (log0 z2)))
          (plus0 (mult0 (minus rI.rI_base b2 b1) e2) rI.rI_base.zero)
          (id_trans
            (rI.rI_base.plus
              (rI.rI_base.plus (mult0 (minus rI.rI_base b2 b1) e2) (log0 z2))
              (rI.rI_base.opp (log0 z2)))
            (rI.rI_base.plus (mult0 (minus rI.rI_base b2 b1) e2)
              (rI.rI_base.plus (log0 z2) (rI.rI_base.opp (log0 z2))))
            (plus0 (mult0 (minus rI.rI_base b2 b1) e2) rI.rI_base.zero)
            (id_sym
              (rI.rI_base.plus (mult0 (minus rI.rI_base b2 b1) e2)
                (rI.rI_base.plus (log0 z2) (rI.rI_base.opp (log0 z2))))
              (rI.rI_base.plus
                (rI.rI_base.plus (mult0 (minus rI.rI_base b2 b1) e2)
                  (log0 z2))
                (rI.rI_base.opp (log0 z2)))
              (rI.rI_base.plus_assoc (mult0 (minus rI.rI_base b2 b1) e2)
                (log0 z2) (rI.rI_base.opp (log0 z2))))
            (id_cong (fun x -> plus0 (mult0 (minus rI.rI_base b2 b1) e2) x)
              (rI.rI_base.plus (log0 z2) (rI.rI_base.opp (log0 z2)))
              rI.rI_base.zero (rI.rI_base.plus_opp (log0 z2))))))
      (rI.le_plus_compat
        (plus0 (mult0 (minus rI.rI_base b2 b1) e2) (log0 z2)) (log0 z1)
        (rI.rI_base.opp (log0 z2)) (rI.rI_base.opp (log0 z2)) hv1''
        (rI.rI_base.le_refl (rI.rI_base.opp (log0 z2))))
  in
  let hshift2 =
    rI.rI_base.le_id_l (mult0 (minus rI.rI_base b1 b2) e1)
      (plus0 (plus0 (mult0 (minus rI.rI_base b1 b2) e1) (log0 z1))
        (rI.rI_base.opp (log0 z1)))
      (minus rI.rI_base (log0 z2) (log0 z1))
      (id_trans (mult0 (minus rI.rI_base b1 b2) e1)
        (rI.rI_base.plus (mult0 (minus rI.rI_base b1 b2) e1) rI.rI_base.zero)
        (rI.rI_base.plus
          (rI.rI_base.plus (mult0 (minus rI.rI_base b1 b2) e1) (log0 z1))
          (rI.rI_base.opp (log0 z1)))
        (id_sym
          (rI.rI_base.plus (mult0 (minus rI.rI_base b1 b2) e1)
            rI.rI_base.zero)
          (mult0 (minus rI.rI_base b1 b2) e1)
          (rI.rI_base.plus_zero (mult0 (minus rI.rI_base b1 b2) e1)))
        (id_sym
          (rI.rI_base.plus
            (rI.rI_base.plus (mult0 (minus rI.rI_base b1 b2) e1) (log0 z1))
            (rI.rI_base.opp (log0 z1)))
          (plus0 (mult0 (minus rI.rI_base b1 b2) e1) rI.rI_base.zero)
          (id_trans
            (rI.rI_base.plus
              (rI.rI_base.plus (mult0 (minus rI.rI_base b1 b2) e1) (log0 z1))
              (rI.rI_base.opp (log0 z1)))
            (rI.rI_base.plus (mult0 (minus rI.rI_base b1 b2) e1)
              (rI.rI_base.plus (log0 z1) (rI.rI_base.opp (log0 z1))))
            (plus0 (mult0 (minus rI.rI_base b1 b2) e1) rI.rI_base.zero)
            (id_sym
              (rI.rI_base.plus (mult0 (minus rI.rI_base b1 b2) e1)
                (rI.rI_base.plus (log0 z1) (rI.rI_base.opp (log0 z1))))
              (rI.rI_base.plus
                (rI.rI_base.plus (mult0 (minus rI.rI_base b1 b2) e1)
                  (log0 z1))
                (rI.rI_base.opp (log0 z1)))
              (rI.rI_base.plus_assoc (mult0 (minus rI.rI_base b1 b2) e1)
                (log0 z1) (rI.rI_base.opp (log0 z1))))
            (id_cong (fun x -> plus0 (mult0 (minus rI.rI_base b1 b2) e1) x)
              (rI.rI_base.plus (log0 z1) (rI.rI_base.opp (log0 z1)))
              rI.rI_base.zero (rI.rI_base.plus_opp (log0 z1))))))
      (rI.le_plus_compat
        (plus0 (mult0 (minus rI.rI_base b1 b2) e1) (log0 z1)) (log0 z2)
        (rI.rI_base.opp (log0 z1)) (rI.rI_base.opp (log0 z1)) hv2''
        (rI.rI_base.le_refl (rI.rI_base.opp (log0 z1))))
  in
  let hsum =
    rI.le_plus_compat (mult0 (minus rI.rI_base b2 b1) e2)
      (minus rI.rI_base (log0 z1) (log0 z2))
      (mult0 (minus rI.rI_base b1 b2) e1)
      (minus rI.rI_base (log0 z2) (log0 z1)) hshift1 hshift2
  in
  let hz =
    id_trans
      (rI.rI_base.plus (rI.rI_base.plus (log0 z1) (rI.rI_base.opp (log0 z2)))
        (plus0 (log0 z2) (rI.rI_base.opp (log0 z1))))
      (rI.rI_base.plus (log0 z1)
        (rI.rI_base.plus (rI.rI_base.opp (log0 z2))
          (plus0 (log0 z2) (rI.rI_base.opp (log0 z1)))))
      rI.rI_base.zero
      (id_sym
        (rI.rI_base.plus (log0 z1)
          (rI.rI_base.plus (rI.rI_base.opp (log0 z2))
            (plus0 (log0 z2) (rI.rI_base.opp (log0 z1)))))
        (rI.rI_base.plus
          (rI.rI_base.plus (log0 z1) (rI.rI_base.opp (log0 z2)))
          (plus0 (log0 z2) (rI.rI_base.opp (log0 z1))))
        (rI.rI_base.plus_assoc (log0 z1) (rI.rI_base.opp (log0 z2))
          (plus0 (log0 z2) (rI.rI_base.opp (log0 z1)))))
      (id_trans
        (plus0 (log0 z1)
          (rI.rI_base.plus (rI.rI_base.opp (log0 z2))
            (rI.rI_base.plus (log0 z2) (rI.rI_base.opp (log0 z1)))))
        (plus0 (log0 z1)
          (rI.rI_base.plus
            (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (log0 z2))
            (rI.rI_base.opp (log0 z1))))
        rI.rI_base.zero
        (id_cong (fun x -> plus0 (log0 z1) x)
          (rI.rI_base.plus (rI.rI_base.opp (log0 z2))
            (rI.rI_base.plus (log0 z2) (rI.rI_base.opp (log0 z1))))
          (rI.rI_base.plus
            (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (log0 z2))
            (rI.rI_base.opp (log0 z1)))
          (rI.rI_base.plus_assoc (rI.rI_base.opp (log0 z2)) (log0 z2)
            (rI.rI_base.opp (log0 z1))))
        (id_trans
          (plus0 (log0 z1)
            (plus0 (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (log0 z2))
              (rI.rI_base.opp (log0 z1))))
          (plus0 (log0 z1) (plus0 rI.rI_base.zero (rI.rI_base.opp (log0 z1))))
          rI.rI_base.zero
          (id_cong (fun x -> plus0 (log0 z1) x)
            (plus0 (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (log0 z2))
              (rI.rI_base.opp (log0 z1)))
            (plus0 rI.rI_base.zero (rI.rI_base.opp (log0 z1)))
            (id_cong (fun x -> plus0 x (rI.rI_base.opp (log0 z1)))
              (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (log0 z2))
              rI.rI_base.zero
              (id_trans
                (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (log0 z2))
                (rI.rI_base.plus (log0 z2) (rI.rI_base.opp (log0 z2)))
                rI.rI_base.zero
                (rI.rI_base.plus_comm (rI.rI_base.opp (log0 z2)) (log0 z2))
                (rI.rI_base.plus_opp (log0 z2)))))
          (id_trans
            (plus0 (log0 z1)
              (rI.rI_base.plus zero0 (rI.rI_base.opp (log0 z1))))
            (plus0 (log0 z1) (rI.rI_base.opp (log0 z1))) rI.rI_base.zero
            (id_cong (fun x -> plus0 (log0 z1) x)
              (rI.rI_base.plus zero0 (rI.rI_base.opp (log0 z1)))
              (rI.rI_base.opp (log0 z1))
              (id_trans (rI.rI_base.plus zero0 (rI.rI_base.opp (log0 z1)))
                (rI.rI_base.plus (rI.rI_base.opp (log0 z1)) zero0)
                (rI.rI_base.opp (log0 z1))
                (rI.rI_base.plus_comm zero0 (rI.rI_base.opp (log0 z1)))
                (rI.rI_base.plus_zero (rI.rI_base.opp (log0 z1)))))
            (rI.rI_base.plus_opp (log0 z1)))))
  in
  let hoppm =
    id_sym (rI.rI_base.opp (rI.rI_base.plus b1 (rI.rI_base.opp b2)))
      (rI.rI_base.plus b2 (rI.rI_base.opp b1))
      (id_trans (rI.rI_base.opp (rI.rI_base.plus b1 (rI.rI_base.opp b2)))
        (rI.rI_base.plus (rI.rI_base.opp b1)
          (rI.rI_base.opp (rI.rI_base.opp b2)))
        (rI.rI_base.plus b2 (rI.rI_base.opp b1))
        (opp_plus rI b1 (rI.rI_base.opp b2))
        (id_trans
          (plus0 (rI.rI_base.opp b1) (rI.rI_base.opp (rI.rI_base.opp b2)))
          (plus0 (rI.rI_base.opp b1) b2)
          (rI.rI_base.plus b2 (rI.rI_base.opp b1))
          (id_cong (fun x -> plus0 (rI.rI_base.opp b1) x)
            (rI.rI_base.opp (rI.rI_base.opp b2)) b2 (double_neg rI b2))
          (rI.rI_base.plus_comm (rI.rI_base.opp b1) b2)))
  in
  let hlhs =
    id_trans
      (plus0 (mult0 (minus rI.rI_base b2 b1) e2)
        (mult0 (minus rI.rI_base b1 b2) e1))
      (plus0 (mult0 (rI.rI_base.opp (minus rI.rI_base b1 b2)) e2)
        (mult0 (minus rI.rI_base b1 b2) e1))
      (mult0 (minus rI.rI_base b1 b2)
        (rI.rI_base.plus e1 (rI.rI_base.opp e2)))
      (id_cong (fun x ->
        plus0 (mult0 x e2) (mult0 (minus rI.rI_base b1 b2) e1))
        (minus rI.rI_base b2 b1) (rI.rI_base.opp (minus rI.rI_base b1 b2))
        hoppm)
      (id_trans
        (plus0 (rI.rI_base.mult (rI.rI_base.opp (minus rI.rI_base b1 b2)) e2)
          (mult0 (minus rI.rI_base b1 b2) e1))
        (plus0 (rI.rI_base.opp (rI.rI_base.mult (minus rI.rI_base b1 b2) e2))
          (mult0 (minus rI.rI_base b1 b2) e1))
        (mult0 (minus rI.rI_base b1 b2)
          (rI.rI_base.plus e1 (rI.rI_base.opp e2)))
        (id_cong (fun x -> plus0 x (mult0 (minus rI.rI_base b1 b2) e1))
          (rI.rI_base.mult (rI.rI_base.opp (minus rI.rI_base b1 b2)) e2)
          (rI.rI_base.opp (rI.rI_base.mult (minus rI.rI_base b1 b2) e2))
          (opp_mult_r rI (minus rI.rI_base b1 b2) e2))
        (id_trans
          (plus0
            (rI.rI_base.opp (rI.rI_base.mult (minus rI.rI_base b1 b2) e2))
            (mult0 (minus rI.rI_base b1 b2) e1))
          (plus0
            (rI.rI_base.mult (minus rI.rI_base b1 b2) (rI.rI_base.opp e2))
            (mult0 (minus rI.rI_base b1 b2) e1))
          (mult0 (minus rI.rI_base b1 b2)
            (rI.rI_base.plus e1 (rI.rI_base.opp e2)))
          (id_cong (fun x -> plus0 x (mult0 (minus rI.rI_base b1 b2) e1))
            (rI.rI_base.opp (rI.rI_base.mult (minus rI.rI_base b1 b2) e2))
            (rI.rI_base.mult (minus rI.rI_base b1 b2) (rI.rI_base.opp e2))
            (id_sym
              (rI.rI_base.mult (minus rI.rI_base b1 b2) (rI.rI_base.opp e2))
              (rI.rI_base.opp (rI.rI_base.mult (minus rI.rI_base b1 b2) e2))
              (opp_mult_l rI (minus rI.rI_base b1 b2) e2)))
          (id_trans
            (rI.rI_base.plus
              (rI.rI_base.mult (minus rI.rI_base b1 b2) (rI.rI_base.opp e2))
              (rI.rI_base.mult (minus rI.rI_base b1 b2) e1))
            (rI.rI_base.mult (minus rI.rI_base b1 b2)
              (rI.rI_base.plus (rI.rI_base.opp e2) e1))
            (mult0 (minus rI.rI_base b1 b2)
              (rI.rI_base.plus e1 (rI.rI_base.opp e2)))
            (id_sym
              (rI.rI_base.mult (minus rI.rI_base b1 b2)
                (rI.rI_base.plus (rI.rI_base.opp e2) e1))
              (rI.rI_base.plus
                (rI.rI_base.mult (minus rI.rI_base b1 b2) (rI.rI_base.opp e2))
                (rI.rI_base.mult (minus rI.rI_base b1 b2) e1))
              (rI.rI_base.distrib (minus rI.rI_base b1 b2)
                (rI.rI_base.opp e2) e1))
            (id_cong (fun x -> mult0 (minus rI.rI_base b1 b2) x)
              (rI.rI_base.plus (rI.rI_base.opp e2) e1)
              (rI.rI_base.plus e1 (rI.rI_base.opp e2))
              (rI.rI_base.plus_comm (rI.rI_base.opp e2) e1)))))
  in
  let hmain =
    rI.rI_base.le_id_l
      (mult0 (minus rI.rI_base b1 b2) (minus rI.rI_base e1 e2))
      (plus0 (mult0 (minus rI.rI_base b2 b1) e2)
        (mult0 (minus rI.rI_base b1 b2) e1))
      zero0
      (id_sym
        (plus0 (mult0 (minus rI.rI_base b2 b1) e2)
          (mult0 (minus rI.rI_base b1 b2) e1))
        (mult0 (minus rI.rI_base b1 b2) (minus rI.rI_base e1 e2)) hlhs)
      (rI.rI_base.le_id_r
        (plus0 (mult0 (minus rI.rI_base b2 b1) e2)
          (mult0 (minus rI.rI_base b1 b2) e1))
        (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
          (minus rI.rI_base (log0 z2) (log0 z1)))
        zero0 hz hsum)
  in
  let hcancel =
    le_mult_pos_cancel rI (minus rI.rI_base e1 e2) (minus rI.rI_base b1 b2)
      hbpos
      (rI.rI_base.le_id_l
        (mult0 (minus rI.rI_base e1 e2) (minus rI.rI_base b1 b2))
        (mult0 (minus rI.rI_base b1 b2) (minus rI.rI_base e1 e2)) zero0
        (rI.rI_base.mult_comm (minus rI.rI_base e1 e2)
          (minus rI.rI_base b1 b2))
        hmain)
  in
  le_minus_nonneg_rev rI e1 e2 hcancel)

(** val temp_strict_A_chain2 :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> r -> lt ->
    lt -> r id **)

let temp_strict_A_chain2 rI sS sO =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let log0 = rI.log in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec t1 t2 ht1 ht2 ->
  let b1 = inv_pos0 t1 ht1 in
  let b2 = inv_pos0 t2 ht2 in
  let e2 =
    energy_exp_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t2
      ht2
  in
  let s2 =
    entropy_dist rI sS sO
      (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t2 ht2)
  in
  let z1 = z_temp t1 in
  let z2 = z_temp t2 in
  let hse =
    entropy_temp_explicit rI sS sO base_loss sum_over_S_pos z_temp
      z_temp_spec t2 ht2
  in
  let h1 =
    id_cong (fun x ->
      plus0 (plus0 (rI.rI_base.opp x) (mult0 b1 e2)) (log0 z1)) s2
      (plus0 (mult0 b2 e2) (log0 z2)) hse
  in
  let h2 =
    id_cong (fun x -> plus0 (plus0 x (mult0 b1 e2)) (log0 z1))
      (rI.rI_base.opp (plus0 (mult0 b2 e2) (log0 z2)))
      (plus0 (rI.rI_base.opp (mult0 b2 e2)) (rI.rI_base.opp (log0 z2)))
      (opp_plus rI (mult0 b2 e2) (log0 z2))
  in
  let h3 =
    id_trans
      (plus0
        (rI.rI_base.plus
          (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e2))
            (rI.rI_base.opp (log0 z2)))
          (mult0 b1 e2))
        (log0 z1))
      (plus0
        (rI.rI_base.plus
          (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e2)) (mult0 b1 e2))
          (rI.rI_base.opp (log0 z2)))
        (log0 z1))
      (plus0 (plus0 (rI.rI_base.opp (mult0 b2 e2)) (mult0 b1 e2))
        (plus0 (rI.rI_base.opp (log0 z2)) (log0 z1)))
      (id_cong (fun x -> plus0 x (log0 z1))
        (rI.rI_base.plus
          (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e2))
            (rI.rI_base.opp (log0 z2)))
          (mult0 b1 e2))
        (rI.rI_base.plus
          (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e2)) (mult0 b1 e2))
          (rI.rI_base.opp (log0 z2)))
        (id_trans
          (rI.rI_base.plus
            (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e2))
              (rI.rI_base.opp (log0 z2)))
            (mult0 b1 e2))
          (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e2))
            (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (mult0 b1 e2)))
          (rI.rI_base.plus
            (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e2)) (mult0 b1 e2))
            (rI.rI_base.opp (log0 z2)))
          (id_sym
            (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e2))
              (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (mult0 b1 e2)))
            (rI.rI_base.plus
              (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e2))
                (rI.rI_base.opp (log0 z2)))
              (mult0 b1 e2))
            (rI.rI_base.plus_assoc (rI.rI_base.opp (mult0 b2 e2))
              (rI.rI_base.opp (log0 z2)) (mult0 b1 e2)))
          (id_trans
            (plus0 (rI.rI_base.opp (mult0 b2 e2))
              (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (mult0 b1 e2)))
            (plus0 (rI.rI_base.opp (mult0 b2 e2))
              (rI.rI_base.plus (mult0 b1 e2) (rI.rI_base.opp (log0 z2))))
            (rI.rI_base.plus
              (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e2)) (mult0 b1 e2))
              (rI.rI_base.opp (log0 z2)))
            (id_cong (fun x -> plus0 (rI.rI_base.opp (mult0 b2 e2)) x)
              (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (mult0 b1 e2))
              (rI.rI_base.plus (mult0 b1 e2) (rI.rI_base.opp (log0 z2)))
              (rI.rI_base.plus_comm (rI.rI_base.opp (log0 z2)) (mult0 b1 e2)))
            (rI.rI_base.plus_assoc (rI.rI_base.opp (mult0 b2 e2))
              (mult0 b1 e2) (rI.rI_base.opp (log0 z2))))))
      (id_sym
        (plus0 (plus0 (rI.rI_base.opp (mult0 b2 e2)) (mult0 b1 e2))
          (plus0 (rI.rI_base.opp (log0 z2)) (log0 z1)))
        (plus0
          (rI.rI_base.plus
            (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e2)) (mult0 b1 e2))
            (rI.rI_base.opp (log0 z2)))
          (log0 z1))
        (rI.rI_base.plus_assoc
          (plus0 (rI.rI_base.opp (mult0 b2 e2)) (mult0 b1 e2))
          (rI.rI_base.opp (log0 z2)) (log0 z1)))
  in
  let h4 =
    id_trans (rI.rI_base.plus (rI.rI_base.opp (mult0 b2 e2)) (mult0 b1 e2))
      (rI.rI_base.plus (mult0 b1 e2) (rI.rI_base.opp (mult0 b2 e2)))
      (mult0 (minus rI.rI_base b1 b2) e2)
      (rI.rI_base.plus_comm (rI.rI_base.opp (mult0 b2 e2)) (mult0 b1 e2))
      (id_sym (mult0 (minus rI.rI_base b1 b2) e2)
        (minus rI.rI_base (mult0 b1 e2) (mult0 b2 e2))
        (mult_minus_distr_r rI b1 b2 e2))
  in
  let h5 = rI.rI_base.plus_comm (rI.rI_base.opp (log0 z2)) (log0 z1) in
  let hm4 =
    id_cong (fun x -> plus0 x (plus0 (rI.rI_base.opp (log0 z2)) (log0 z1)))
      (plus0 (rI.rI_base.opp (mult0 b2 e2)) (mult0 b1 e2))
      (mult0 (minus rI.rI_base b1 b2) e2) h4
  in
  let hfin =
    id_trans
      (plus0 (plus0 (rI.rI_base.opp (mult0 b2 e2)) (mult0 b1 e2))
        (plus0 (rI.rI_base.opp (log0 z2)) (log0 z1)))
      (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
        (plus0 (rI.rI_base.opp (log0 z2)) (log0 z1)))
      (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
        (minus rI.rI_base (log0 z1) (log0 z2)))
      hm4
      (id_cong (fun x -> plus0 (mult0 (minus rI.rI_base b1 b2) e2) x)
        (plus0 (rI.rI_base.opp (log0 z2)) (log0 z1))
        (minus rI.rI_base (log0 z1) (log0 z2)) h5)
  in
  id_trans (plus0 (plus0 (rI.rI_base.opp s2) (mult0 b1 e2)) (log0 z1))
    (plus0
      (plus0 (rI.rI_base.opp (plus0 (mult0 b2 e2) (log0 z2))) (mult0 b1 e2))
      (log0 z1))
    (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
      (minus rI.rI_base (log0 z1) (log0 z2)))
    h1
    (id_trans
      (plus0
        (plus0 (rI.rI_base.opp (plus0 (mult0 b2 e2) (log0 z2))) (mult0 b1 e2))
        (log0 z1))
      (plus0
        (plus0
          (plus0 (rI.rI_base.opp (mult0 b2 e2)) (rI.rI_base.opp (log0 z2)))
          (mult0 b1 e2))
        (log0 z1))
      (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
        (minus rI.rI_base (log0 z1) (log0 z2)))
      h2
      (id_trans
        (plus0
          (plus0
            (plus0 (rI.rI_base.opp (mult0 b2 e2)) (rI.rI_base.opp (log0 z2)))
            (mult0 b1 e2))
          (log0 z1))
        (plus0 (plus0 (rI.rI_base.opp (mult0 b2 e2)) (mult0 b1 e2))
          (plus0 (rI.rI_base.opp (log0 z2)) (log0 z1)))
        (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
          (minus rI.rI_base (log0 z1) (log0 z2)))
        h3 hfin)))

(** val temp_strict_ident2 :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> r -> lt ->
    lt -> r id **)

let temp_strict_ident2 rI sS sO =
  let zero0 = rI.rI_base.zero in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  let log0 = rI.log in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec t1 t2 ht1 ht2 ->
  let b1 = inv_pos0 t1 ht1 in
  let b2 = inv_pos0 t2 ht2 in
  let e1 =
    energy_exp_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t1
      ht1
  in
  let e2 =
    energy_exp_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t2
      ht2
  in
  let z1 = z_temp t1 in
  let z2 = z_temp t2 in
  let hK1 =
    id_trans
      (relative_entropy rI sS sO
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t2 ht2)
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t1 ht1))
      (plus0
        (plus0
          (rI.rI_base.opp
            (entropy_dist rI sS sO
              (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t2 ht2)))
          (mult0 (inv_pos0 t1 ht1)
            (energy_expectation rI sS sO base_loss
              (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t2 ht2))))
        (log0 (z_temp t1)))
      (plus0
        (mult0 (minus rI.rI_base (inv_pos0 t1 ht1) (inv_pos0 t2 ht2))
          (energy_exp_temp rI sS sO base_loss sum_over_S_pos z_temp
            z_temp_spec t2 ht2))
        (minus rI.rI_base (log0 (z_temp t1)) (log0 (z_temp t2))))
      (relative_entropy_temp_decomp rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t1 ht1
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t2 ht2)
        (boltzmann_dist_temp_normalized rI sS sO base_loss sum_over_S_pos
          z_temp z_temp_spec t2 ht2))
      (temp_strict_A_chain2 rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t1 t2 ht1 ht2)
  in
  let hK2 =
    id_trans
      (relative_entropy rI sS sO
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t1 ht1)
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t2 ht2))
      (plus0
        (plus0
          (rI.rI_base.opp
            (entropy_dist rI sS sO
              (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t1 ht1)))
          (mult0 (inv_pos0 t2 ht2)
            (energy_expectation rI sS sO base_loss
              (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
                z_temp_spec t1 ht1))))
        (log0 (z_temp t2)))
      (plus0
        (mult0 (minus rI.rI_base (inv_pos0 t2 ht2) (inv_pos0 t1 ht1))
          (energy_exp_temp rI sS sO base_loss sum_over_S_pos z_temp
            z_temp_spec t1 ht1))
        (minus rI.rI_base (log0 (z_temp t2)) (log0 (z_temp t1))))
      (relative_entropy_temp_decomp rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t2 ht2
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t1 ht1)
        (boltzmann_dist_temp_normalized rI sS sO base_loss sum_over_S_pos
          z_temp z_temp_spec t1 ht1))
      (temp_strict_A_chain2 rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t2 t1 ht2 ht1)
  in
  let hsum =
    id_cong2 plus0
      (relative_entropy rI sS sO
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t2 ht2)
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t1 ht1))
      (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
        (minus rI.rI_base (log0 z1) (log0 z2)))
      (relative_entropy rI sS sO
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t1 ht1)
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t2 ht2))
      (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
        (minus rI.rI_base (log0 z2) (log0 z1)))
      hK1 hK2
  in
  id_trans
    (plus0
      (relative_entropy rI sS sO
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t2 ht2)
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t1 ht1))
      (relative_entropy rI sS sO
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t1 ht1)
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t2 ht2)))
    (plus0
      (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
        (minus rI.rI_base (log0 z1) (log0 z2)))
      (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
        (minus rI.rI_base (log0 z2) (log0 z1))))
    (mult0 (minus rI.rI_base b1 b2) (minus rI.rI_base e2 e1)) hsum
    (let hz =
       id_trans
         (rI.rI_base.plus
           (rI.rI_base.plus (log0 z1) (rI.rI_base.opp (log0 z2)))
           (plus0 (log0 z2) (rI.rI_base.opp (log0 z1))))
         (rI.rI_base.plus (log0 z1)
           (rI.rI_base.plus (rI.rI_base.opp (log0 z2))
             (plus0 (log0 z2) (rI.rI_base.opp (log0 z1)))))
         rI.rI_base.zero
         (id_sym
           (rI.rI_base.plus (log0 z1)
             (rI.rI_base.plus (rI.rI_base.opp (log0 z2))
               (plus0 (log0 z2) (rI.rI_base.opp (log0 z1)))))
           (rI.rI_base.plus
             (rI.rI_base.plus (log0 z1) (rI.rI_base.opp (log0 z2)))
             (plus0 (log0 z2) (rI.rI_base.opp (log0 z1))))
           (rI.rI_base.plus_assoc (log0 z1) (rI.rI_base.opp (log0 z2))
             (plus0 (log0 z2) (rI.rI_base.opp (log0 z1)))))
         (id_trans
           (plus0 (log0 z1)
             (rI.rI_base.plus (rI.rI_base.opp (log0 z2))
               (rI.rI_base.plus (log0 z2) (rI.rI_base.opp (log0 z1)))))
           (plus0 (log0 z1)
             (rI.rI_base.plus
               (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (log0 z2))
               (rI.rI_base.opp (log0 z1))))
           rI.rI_base.zero
           (id_cong (fun x -> plus0 (log0 z1) x)
             (rI.rI_base.plus (rI.rI_base.opp (log0 z2))
               (rI.rI_base.plus (log0 z2) (rI.rI_base.opp (log0 z1))))
             (rI.rI_base.plus
               (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (log0 z2))
               (rI.rI_base.opp (log0 z1)))
             (rI.rI_base.plus_assoc (rI.rI_base.opp (log0 z2)) (log0 z2)
               (rI.rI_base.opp (log0 z1))))
           (id_trans
             (plus0 (log0 z1)
               (plus0 (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (log0 z2))
                 (rI.rI_base.opp (log0 z1))))
             (plus0 (log0 z1)
               (plus0 rI.rI_base.zero (rI.rI_base.opp (log0 z1))))
             rI.rI_base.zero
             (id_cong (fun x -> plus0 (log0 z1) x)
               (plus0 (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (log0 z2))
                 (rI.rI_base.opp (log0 z1)))
               (plus0 rI.rI_base.zero (rI.rI_base.opp (log0 z1)))
               (id_cong (fun x -> plus0 x (rI.rI_base.opp (log0 z1)))
                 (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (log0 z2))
                 rI.rI_base.zero
                 (id_trans
                   (rI.rI_base.plus (rI.rI_base.opp (log0 z2)) (log0 z2))
                   (rI.rI_base.plus (log0 z2) (rI.rI_base.opp (log0 z2)))
                   rI.rI_base.zero
                   (rI.rI_base.plus_comm (rI.rI_base.opp (log0 z2)) (log0 z2))
                   (rI.rI_base.plus_opp (log0 z2)))))
             (id_trans
               (plus0 (log0 z1)
                 (rI.rI_base.plus zero0 (rI.rI_base.opp (log0 z1))))
               (plus0 (log0 z1) (rI.rI_base.opp (log0 z1))) rI.rI_base.zero
               (id_cong (fun x -> plus0 (log0 z1) x)
                 (rI.rI_base.plus zero0 (rI.rI_base.opp (log0 z1)))
                 (rI.rI_base.opp (log0 z1))
                 (id_trans (rI.rI_base.plus zero0 (rI.rI_base.opp (log0 z1)))
                   (rI.rI_base.plus (rI.rI_base.opp (log0 z1)) zero0)
                   (rI.rI_base.opp (log0 z1))
                   (rI.rI_base.plus_comm zero0 (rI.rI_base.opp (log0 z1)))
                   (rI.rI_base.plus_zero (rI.rI_base.opp (log0 z1)))))
               (rI.rI_base.plus_opp (log0 z1)))))
     in
     let hoppm =
       id_sym (rI.rI_base.opp (rI.rI_base.plus b1 (rI.rI_base.opp b2)))
         (rI.rI_base.plus b2 (rI.rI_base.opp b1))
         (id_trans (rI.rI_base.opp (rI.rI_base.plus b1 (rI.rI_base.opp b2)))
           (rI.rI_base.plus (rI.rI_base.opp b1)
             (rI.rI_base.opp (rI.rI_base.opp b2)))
           (rI.rI_base.plus b2 (rI.rI_base.opp b1))
           (opp_plus rI b1 (rI.rI_base.opp b2))
           (id_trans
             (plus0 (rI.rI_base.opp b1) (rI.rI_base.opp (rI.rI_base.opp b2)))
             (plus0 (rI.rI_base.opp b1) b2)
             (rI.rI_base.plus b2 (rI.rI_base.opp b1))
             (id_cong (fun x -> plus0 (rI.rI_base.opp b1) x)
               (rI.rI_base.opp (rI.rI_base.opp b2)) b2 (double_neg rI b2))
             (rI.rI_base.plus_comm (rI.rI_base.opp b1) b2)))
     in
     let hmain2 =
       id_trans
         (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
           (mult0 (minus rI.rI_base b2 b1) e1))
         (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
           (mult0 (rI.rI_base.opp (minus rI.rI_base b1 b2)) e1))
         (rI.rI_base.mult (minus rI.rI_base b1 b2) (minus rI.rI_base e2 e1))
         (id_cong (fun x ->
           plus0 (mult0 (minus rI.rI_base b1 b2) e2) (mult0 x e1))
           (minus rI.rI_base b2 b1) (rI.rI_base.opp (minus rI.rI_base b1 b2))
           hoppm)
         (id_trans
           (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
             (rI.rI_base.mult (rI.rI_base.opp (minus rI.rI_base b1 b2)) e1))
           (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
             (rI.rI_base.opp (rI.rI_base.mult (minus rI.rI_base b1 b2) e1)))
           (rI.rI_base.mult (minus rI.rI_base b1 b2) (minus rI.rI_base e2 e1))
           (id_cong (fun x -> plus0 (mult0 (minus rI.rI_base b1 b2) e2) x)
             (rI.rI_base.mult (rI.rI_base.opp (minus rI.rI_base b1 b2)) e1)
             (rI.rI_base.opp (rI.rI_base.mult (minus rI.rI_base b1 b2) e1))
             (opp_mult_r rI (minus rI.rI_base b1 b2) e1))
           (id_sym
             (rI.rI_base.mult (minus rI.rI_base b1 b2)
               (minus rI.rI_base e2 e1))
             (minus rI.rI_base (rI.rI_base.mult (minus rI.rI_base b1 b2) e2)
               (rI.rI_base.mult (minus rI.rI_base b1 b2) e1))
             (mult_minus_distr_l rI (minus rI.rI_base b1 b2) e2 e1)))
     in
     let h1 =
       id_sym
         (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
           (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
             (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
               (minus rI.rI_base (log0 z2) (log0 z1)))))
         (plus0
           (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
             (minus rI.rI_base (log0 z1) (log0 z2)))
           (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
             (minus rI.rI_base (log0 z2) (log0 z1))))
         (rI.rI_base.plus_assoc (mult0 (minus rI.rI_base b1 b2) e2)
           (minus rI.rI_base (log0 z1) (log0 z2))
           (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
             (minus rI.rI_base (log0 z2) (log0 z1))))
     in
     let h2 =
       let h2a =
         id_cong (fun x -> plus0 (mult0 (minus rI.rI_base b1 b2) e2) x)
           (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
             (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
               (minus rI.rI_base (log0 z2) (log0 z1))))
           (plus0
             (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
               (mult0 (minus rI.rI_base b2 b1) e1))
             (minus rI.rI_base (log0 z2) (log0 z1)))
           (rI.rI_base.plus_assoc (minus rI.rI_base (log0 z1) (log0 z2))
             (mult0 (minus rI.rI_base b2 b1) e1)
             (minus rI.rI_base (log0 z2) (log0 z1)))
       in
       let h2b =
         id_cong (fun x ->
           plus0 (mult0 (minus rI.rI_base b1 b2) e2)
             (plus0 x (minus rI.rI_base (log0 z2) (log0 z1))))
           (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
             (mult0 (minus rI.rI_base b2 b1) e1))
           (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
             (minus rI.rI_base (log0 z1) (log0 z2)))
           (rI.rI_base.plus_comm (minus rI.rI_base (log0 z1) (log0 z2))
             (mult0 (minus rI.rI_base b2 b1) e1))
       in
       let h2c =
         id_cong (fun x -> plus0 (mult0 (minus rI.rI_base b1 b2) e2) x)
           (plus0
             (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
               (minus rI.rI_base (log0 z1) (log0 z2)))
             (minus rI.rI_base (log0 z2) (log0 z1)))
           (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
             (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
               (minus rI.rI_base (log0 z2) (log0 z1))))
           (id_sym
             (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
               (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
                 (minus rI.rI_base (log0 z2) (log0 z1))))
             (plus0
               (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
                 (minus rI.rI_base (log0 z1) (log0 z2)))
               (minus rI.rI_base (log0 z2) (log0 z1)))
             (rI.rI_base.plus_assoc (mult0 (minus rI.rI_base b2 b1) e1)
               (minus rI.rI_base (log0 z1) (log0 z2))
               (minus rI.rI_base (log0 z2) (log0 z1))))
       in
       id_trans
         (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
           (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
             (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
               (minus rI.rI_base (log0 z2) (log0 z1)))))
         (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
           (plus0
             (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
               (mult0 (minus rI.rI_base b2 b1) e1))
             (minus rI.rI_base (log0 z2) (log0 z1))))
         (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
           (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
             (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
               (minus rI.rI_base (log0 z2) (log0 z1)))))
         h2a
         (id_trans
           (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
             (plus0
               (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
                 (mult0 (minus rI.rI_base b2 b1) e1))
               (minus rI.rI_base (log0 z2) (log0 z1))))
           (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
             (plus0
               (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
                 (minus rI.rI_base (log0 z1) (log0 z2)))
               (minus rI.rI_base (log0 z2) (log0 z1))))
           (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
             (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
               (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
                 (minus rI.rI_base (log0 z2) (log0 z1)))))
           h2b h2c)
     in
     let h3 =
       id_cong (fun x -> plus0 (mult0 (minus rI.rI_base b1 b2) e2) x)
         (plus0 (mult0 (minus rI.rI_base b2 b1) e1) zero0)
         (mult0 (minus rI.rI_base b2 b1) e1)
         (rI.rI_base.plus_zero (mult0 (minus rI.rI_base b2 b1) e1))
     in
     let hza =
       id_cong (fun x ->
         plus0 (mult0 (minus rI.rI_base b1 b2) e2)
           (plus0 (mult0 (minus rI.rI_base b2 b1) e1) x))
         (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
           (minus rI.rI_base (log0 z2) (log0 z1)))
         zero0 hz
     in
     id_trans
       (plus0
         (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
           (minus rI.rI_base (log0 z1) (log0 z2)))
         (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
           (minus rI.rI_base (log0 z2) (log0 z1))))
       (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
         (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
           (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
             (minus rI.rI_base (log0 z2) (log0 z1)))))
       (mult0 (minus rI.rI_base b1 b2) (minus rI.rI_base e2 e1)) h1
       (id_trans
         (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
           (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
             (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
               (minus rI.rI_base (log0 z2) (log0 z1)))))
         (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
           (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
             (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
               (minus rI.rI_base (log0 z2) (log0 z1)))))
         (mult0 (minus rI.rI_base b1 b2) (minus rI.rI_base e2 e1)) h2
         (id_trans
           (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
             (plus0 (mult0 (minus rI.rI_base b2 b1) e1)
               (plus0 (minus rI.rI_base (log0 z1) (log0 z2))
                 (minus rI.rI_base (log0 z2) (log0 z1)))))
           (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
             (plus0 (mult0 (minus rI.rI_base b2 b1) e1) zero0))
           (mult0 (minus rI.rI_base b1 b2) (minus rI.rI_base e2 e1)) hza
           (id_trans
             (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
               (plus0 (mult0 (minus rI.rI_base b2 b1) e1) zero0))
             (plus0 (mult0 (minus rI.rI_base b1 b2) e2)
               (mult0 (minus rI.rI_base b2 b1) e1))
             (mult0 (minus rI.rI_base b1 b2) (minus rI.rI_base e2 e1)) h3
             hmain2)))))

(** val energy_exp_temp_strict_mono :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r -> lt -> lt -> lt -> lt) -> (r -> r -> lt
    -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> r -> lt -> lt -> lt -> lt
    -> lt **)

let energy_exp_temp_strict_mono rI sS sO =
  let zero0 = rI.rI_base.zero in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  (fun base_loss sum_over_S_pos inv_pos_lt_compat lt_minus_nonneg z_temp z_temp_spec t1 t2 ht1 ht2 ht12 hkl1 ->
  let b1 = inv_pos0 t1 ht1 in
  let b2 = inv_pos0 t2 ht2 in
  let e1 =
    energy_exp_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t1
      ht1
  in
  let e2 =
    energy_exp_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t2
      ht2
  in
  let b3 =
    boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
      t1 ht1
  in
  let b4 =
    boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
      t2 ht2
  in
  let k1 = relative_entropy rI sS sO b4 b3 in
  let k2 = relative_entropy rI sS sO b3 b4 in
  let hb = inv_pos_lt_compat t1 t2 ht1 ht2 ht12 in
  let hbd = lt_minus_nonneg b2 b1 hb in
  let hkl2 =
    gibbs_inequality rI sS sO
      (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t1 ht1)
      (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t2 ht2)
      (boltzmann_dist_temp_normalized rI sS sO base_loss sum_over_S_pos
        z_temp z_temp_spec t1 ht1)
      (fun s0 ->
      boltzmann_dist_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t1 ht1 s0)
      (boltzmann_dist_temp_normalized rI sS sO base_loss sum_over_S_pos
        z_temp z_temp_spec t2 ht2)
      (fun s0 ->
      boltzmann_dist_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t2 ht2 s0)
  in
  let hklsum =
    rI.rI_base.lt_le_trans zero0 k1 (plus0 k1 k2) hkl1
      (le_plus_nonneg_r rI k1 k2 hkl2)
  in
  let hid =
    temp_strict_ident2 rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
      t1 t2 ht1 ht2
  in
  let hprod =
    rI.rI_base.lt_id_r zero0 (plus0 k1 k2)
      (mult0 (minus rI.rI_base b1 b2) (minus rI.rI_base e2 e1)) hid hklsum
  in
  lt_mult_pos_cancel rI (minus rI.rI_base e2 e1) (minus rI.rI_base b1 b2) hbd
    (rI.rI_base.lt_id_r zero0
      (mult0 (minus rI.rI_base b1 b2) (minus rI.rI_base e2 e1))
      (mult0 (minus rI.rI_base e2 e1) (minus rI.rI_base b1 b2))
      (rI.rI_base.mult_comm (minus rI.rI_base b1 b2) (minus rI.rI_base e2 e1))
      hprod))

(** val id_transport : 'a1 -> 'a1 -> 'a1 id -> 'a2 -> 'a2 **)

let id_transport _ _ _ h =
  h

(** val fw_energy_eta :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> lt -> r id **)

let fw_energy_eta _ _ _ _ _ _ _ _ _ =
  Id_refl

(** val fw_lt_double :
    realInterfaceEnhanced -> (r -> r -> r -> r -> lt -> le -> lt) -> r -> lt
    -> lt **)

let fw_lt_double rI =
  let zero0 = rI.rI_base.zero in
  (fun lt_plus_compat_lt_le t ht ->
  id_transport (rI.rI_base.plus zero0 t) t
    (id_trans (rI.rI_base.plus zero0 t) (rI.rI_base.plus t zero0) t
      (rI.rI_base.plus_comm zero0 t) (rI.rI_base.plus_zero t))
    (lt_plus_compat_lt_le zero0 t t t ht (rI.rI_base.le_refl t)))

(** val fw_double_pos : realInterfaceEnhanced -> r -> lt -> lt **)

let fw_double_pos rI t ht =
  rI.plus_positive t t ht ht

(** val recovery_entropy_gain :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> r -> lt ->
    lt -> r id **)

let recovery_entropy_gain rI sS sO =
  let zero0 = rI.rI_base.zero in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let log0 = rI.log in
  let inv_pos0 = rI.rI_base.inv_pos in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec ->
  let bt = fun t ht ->
    boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
      t ht
  in
  let et = fun t ht ->
    energy_exp_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t ht
  in
  (fun t1 t2 ht1 ht2 ->
  let b2 = inv_pos0 t2 ht2 in
  let e1 = et t1 ht1 in
  let e2 = et t2 ht2 in
  let h1 = entropy_dist rI sS sO (bt t1 ht1) in
  let h2 = entropy_dist rI sS sO (bt t2 ht2) in
  let k = relative_entropy rI sS sO (bt t1 ht1) (bt t2 ht2) in
  let l2 = log0 (z_temp t2) in
  let hex2 =
    entropy_temp_explicit rI sS sO base_loss sum_over_S_pos z_temp
      z_temp_spec t2 ht2
  in
  let hkl =
    id_trans
      (relative_entropy rI sS sO (bt t1 ht1)
        (boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t2 ht2))
      (rI.rI_base.plus
        (rI.rI_base.plus (rI.rI_base.opp (entropy_dist rI sS sO (bt t1 ht1)))
          (rI.rI_base.mult (rI.rI_base.inv_pos t2 ht2)
            (energy_expectation rI sS sO base_loss (bt t1 ht1))))
        (rI.log (z_temp t2)))
      (plus0 (plus0 (opp0 h1) (mult0 b2 e1)) l2)
      (relative_entropy_temp_decomp rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t2 ht2 (bt t1 ht1)
        (boltzmann_dist_temp_normalized rI sS sO base_loss sum_over_S_pos
          z_temp z_temp_spec t1 ht1))
      (id_cong (fun x -> plus0 (plus0 (opp0 h1) (mult0 b2 x)) l2)
        (energy_expectation rI sS sO base_loss (bt t1 ht1)) e1
        (fw_energy_eta rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
          t1 ht1))
  in
  let hd =
    id_trans (rI.rI_base.mult b2 (minus rI.rI_base e2 e1))
      (minus rI.rI_base (rI.rI_base.mult b2 e2) (rI.rI_base.mult b2 e1))
      (plus0 (mult0 b2 e2) (opp0 (mult0 b2 e1)))
      (mult_minus_distr_l rI b2 e2 e1) Id_refl
  in
  let hrot = fun aX ->
    id_trans (rI.rI_base.plus (rI.rI_base.plus (opp0 h1) aX) l2)
      (rI.rI_base.plus (opp0 h1) (rI.rI_base.plus aX l2))
      (plus0 aX (plus0 (opp0 h1) l2))
      (id_sym (rI.rI_base.plus (opp0 h1) (rI.rI_base.plus aX l2))
        (rI.rI_base.plus (rI.rI_base.plus (opp0 h1) aX) l2)
        (rI.rI_base.plus_assoc (opp0 h1) aX l2))
      (id_trans (plus0 (opp0 h1) (rI.rI_base.plus aX l2))
        (plus0 (opp0 h1) (rI.rI_base.plus l2 aX))
        (plus0 aX (plus0 (opp0 h1) l2))
        (id_cong (fun w -> plus0 (opp0 h1) w) (rI.rI_base.plus aX l2)
          (rI.rI_base.plus l2 aX) (rI.rI_base.plus_comm aX l2))
        (id_trans (rI.rI_base.plus (opp0 h1) (rI.rI_base.plus l2 aX))
          (rI.rI_base.plus (rI.rI_base.plus (opp0 h1) l2) aX)
          (plus0 aX (plus0 (opp0 h1) l2))
          (rI.rI_base.plus_assoc (opp0 h1) l2 aX)
          (rI.rI_base.plus_comm (plus0 (opp0 h1) l2) aX)))
  in
  let hchain =
    id_trans
      (plus0 (mult0 b2 (minus rI.rI_base e2 e1))
        (plus0 (plus0 (opp0 h1) (mult0 b2 e1)) l2))
      (plus0 (plus0 (mult0 b2 e2) (opp0 (mult0 b2 e1)))
        (plus0 (plus0 (opp0 h1) (mult0 b2 e1)) l2))
      (plus0 h2 (opp0 h1))
      (id_cong (fun x -> plus0 x (plus0 (plus0 (opp0 h1) (mult0 b2 e1)) l2))
        (mult0 b2 (minus rI.rI_base e2 e1))
        (plus0 (mult0 b2 e2) (opp0 (mult0 b2 e1))) hd)
      (id_trans
        (rI.rI_base.plus (rI.rI_base.plus (mult0 b2 e2) (opp0 (mult0 b2 e1)))
          (plus0 (plus0 (opp0 h1) (mult0 b2 e1)) l2))
        (rI.rI_base.plus (mult0 b2 e2)
          (rI.rI_base.plus (opp0 (mult0 b2 e1))
            (plus0 (plus0 (opp0 h1) (mult0 b2 e1)) l2)))
        (plus0 h2 (opp0 h1))
        (id_sym
          (rI.rI_base.plus (mult0 b2 e2)
            (rI.rI_base.plus (opp0 (mult0 b2 e1))
              (plus0 (plus0 (opp0 h1) (mult0 b2 e1)) l2)))
          (rI.rI_base.plus
            (rI.rI_base.plus (mult0 b2 e2) (opp0 (mult0 b2 e1)))
            (plus0 (plus0 (opp0 h1) (mult0 b2 e1)) l2))
          (rI.rI_base.plus_assoc (mult0 b2 e2) (opp0 (mult0 b2 e1))
            (plus0 (plus0 (opp0 h1) (mult0 b2 e1)) l2)))
        (id_trans
          (plus0 (mult0 b2 e2)
            (plus0 (opp0 (mult0 b2 e1))
              (plus0 (plus0 (opp0 h1) (mult0 b2 e1)) l2)))
          (plus0 (mult0 b2 e2)
            (plus0 (opp0 (mult0 b2 e1))
              (plus0 (mult0 b2 e1) (plus0 (opp0 h1) l2))))
          (plus0 h2 (opp0 h1))
          (id_cong (fun w ->
            plus0 (mult0 b2 e2) (plus0 (opp0 (mult0 b2 e1)) w))
            (plus0 (plus0 (opp0 h1) (mult0 b2 e1)) l2)
            (plus0 (mult0 b2 e1) (plus0 (opp0 h1) l2)) (hrot (mult0 b2 e1)))
          (id_trans
            (plus0 (mult0 b2 e2)
              (rI.rI_base.plus (opp0 (mult0 b2 e1))
                (rI.rI_base.plus (mult0 b2 e1) (plus0 (opp0 h1) l2))))
            (plus0 (mult0 b2 e2)
              (rI.rI_base.plus
                (rI.rI_base.plus (opp0 (mult0 b2 e1)) (mult0 b2 e1))
                (plus0 (opp0 h1) l2)))
            (plus0 h2 (opp0 h1))
            (id_cong (fun w -> plus0 (mult0 b2 e2) w)
              (rI.rI_base.plus (opp0 (mult0 b2 e1))
                (rI.rI_base.plus (mult0 b2 e1) (plus0 (opp0 h1) l2)))
              (rI.rI_base.plus
                (rI.rI_base.plus (opp0 (mult0 b2 e1)) (mult0 b2 e1))
                (plus0 (opp0 h1) l2))
              (rI.rI_base.plus_assoc (opp0 (mult0 b2 e1)) (mult0 b2 e1)
                (plus0 (opp0 h1) l2)))
            (id_trans
              (plus0 (mult0 b2 e2)
                (plus0 (rI.rI_base.plus (opp0 (mult0 b2 e1)) (mult0 b2 e1))
                  (plus0 (opp0 h1) l2)))
              (plus0 (mult0 b2 e2)
                (plus0 rI.rI_base.zero (plus0 (opp0 h1) l2)))
              (plus0 h2 (opp0 h1))
              (id_cong (fun w ->
                plus0 (mult0 b2 e2) (plus0 w (plus0 (opp0 h1) l2)))
                (rI.rI_base.plus (opp0 (mult0 b2 e1)) (mult0 b2 e1))
                rI.rI_base.zero
                (id_trans
                  (rI.rI_base.plus (opp0 (mult0 b2 e1)) (mult0 b2 e1))
                  (rI.rI_base.plus (mult0 b2 e1) (opp0 (mult0 b2 e1)))
                  rI.rI_base.zero
                  (rI.rI_base.plus_comm (opp0 (mult0 b2 e1)) (mult0 b2 e1))
                  (rI.rI_base.plus_opp (mult0 b2 e1))))
              (id_trans
                (plus0 (mult0 b2 e2)
                  (rI.rI_base.plus zero0 (plus0 (opp0 h1) l2)))
                (plus0 (mult0 b2 e2)
                  (rI.rI_base.plus (plus0 (opp0 h1) l2) zero0))
                (plus0 h2 (opp0 h1))
                (id_cong (fun w -> plus0 (mult0 b2 e2) w)
                  (rI.rI_base.plus zero0 (plus0 (opp0 h1) l2))
                  (rI.rI_base.plus (plus0 (opp0 h1) l2) zero0)
                  (rI.rI_base.plus_comm zero0 (plus0 (opp0 h1) l2)))
                (id_trans
                  (plus0 (mult0 b2 e2)
                    (rI.rI_base.plus (plus0 (opp0 h1) l2) rI.rI_base.zero))
                  (plus0 (mult0 b2 e2) (plus0 (opp0 h1) l2))
                  (plus0 h2 (opp0 h1))
                  (id_cong (fun w -> plus0 (mult0 b2 e2) w)
                    (rI.rI_base.plus (plus0 (opp0 h1) l2) rI.rI_base.zero)
                    (plus0 (opp0 h1) l2)
                    (rI.rI_base.plus_zero (plus0 (opp0 h1) l2)))
                  (id_trans
                    (plus0 (mult0 b2 e2) (rI.rI_base.plus (opp0 h1) l2))
                    (plus0 (mult0 b2 e2) (rI.rI_base.plus l2 (opp0 h1)))
                    (plus0 h2 (opp0 h1))
                    (id_cong (fun w -> plus0 (mult0 b2 e2) w)
                      (rI.rI_base.plus (opp0 h1) l2)
                      (rI.rI_base.plus l2 (opp0 h1))
                      (rI.rI_base.plus_comm (opp0 h1) l2))
                    (id_trans
                      (rI.rI_base.plus (mult0 b2 e2)
                        (rI.rI_base.plus l2 (opp0 h1)))
                      (rI.rI_base.plus (rI.rI_base.plus (mult0 b2 e2) l2)
                        (opp0 h1))
                      (plus0 h2 (opp0 h1))
                      (rI.rI_base.plus_assoc (mult0 b2 e2) l2 (opp0 h1))
                      (id_cong (fun w -> plus0 w (opp0 h1))
                        (plus0 (mult0 b2 e2) l2) h2
                        (id_sym h2 (plus0 (mult0 b2 e2) l2) hex2))))))))))
  in
  id_sym (plus0 (mult0 b2 (minus rI.rI_base e2 e1)) k) (plus0 h2 (opp0 h1))
    (id_trans (plus0 (mult0 b2 (minus rI.rI_base e2 e1)) k)
      (plus0 (mult0 b2 (minus rI.rI_base e2 e1))
        (plus0 (plus0 (opp0 h1) (mult0 b2 e1)) l2))
      (plus0 h2 (opp0 h1))
      (id_cong (fun x -> plus0 (mult0 b2 (minus rI.rI_base e2 e1)) x) k
        (plus0 (plus0 (opp0 h1) (mult0 b2 e1)) l2) hkl)
      hchain)))

(** val entropy_temp_mono :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> (r -> r -> lt ->
    lt -> lt -> lt) -> (r -> r -> lt -> lt) -> r -> r -> lt -> lt -> lt -> le **)

let entropy_temp_mono rI sS sO =
  let zero0 = rI.rI_base.zero in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec inv_pos_lt_compat lt_minus_nonneg ->
  let bt = fun t ht ->
    boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
      t ht
  in
  let et = fun t ht ->
    energy_exp_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t ht
  in
  (fun t1 t2 ht1 ht2 hlt ->
  let hdE =
    le_minus_nonneg rI (et t1 ht1) (et t2 ht2)
      (energy_exp_temp_mono rI sS sO base_loss sum_over_S_pos
        inv_pos_lt_compat lt_minus_nonneg z_temp z_temp_spec t1 t2 ht1 ht2
        hlt)
  in
  let hkl =
    gibbs_inequality rI sS sO (bt t1 ht1) (bt t2 ht2)
      (boltzmann_dist_temp_normalized rI sS sO base_loss sum_over_S_pos
        z_temp z_temp_spec t1 ht1)
      (fun s0 ->
      boltzmann_dist_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t1 ht1 s0)
      (boltzmann_dist_temp_normalized rI sS sO base_loss sum_over_S_pos
        z_temp z_temp_spec t2 ht2)
      (fun s0 ->
      boltzmann_dist_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t2 ht2 s0)
  in
  let hb2 =
    rI.rI_base.lt_le_iff zero0 (inv_pos0 t2 ht2) (Inl (rI.inv_pos_pos t2 ht2))
  in
  let hterm =
    rI.rI_base.le_id_l zero0 (mult0 (inv_pos0 t2 ht2) zero0)
      (mult0 (inv_pos0 t2 ht2) (minus rI.rI_base (et t2 ht2) (et t1 ht1)))
      (id_sym (rI.rI_base.mult (inv_pos0 t2 ht2) rI.rI_base.zero)
        rI.rI_base.zero (rI.rI_base.mult_zero (inv_pos0 t2 ht2)))
      (le_mult_compat_r rI (inv_pos0 t2 ht2) zero0
        (minus rI.rI_base (et t2 ht2) (et t1 ht1)) hb2 hdE)
  in
  let hsum =
    rI.rI_base.le_trans zero0
      (mult0 (inv_pos0 t2 ht2) (minus rI.rI_base (et t2 ht2) (et t1 ht1)))
      (plus0
        (mult0 (inv_pos0 t2 ht2) (minus rI.rI_base (et t2 ht2) (et t1 ht1)))
        (relative_entropy rI sS sO (bt t1 ht1) (bt t2 ht2)))
      hterm
      (le_plus_nonneg_r rI
        (mult0 (inv_pos0 t2 ht2) (minus rI.rI_base (et t2 ht2) (et t1 ht1)))
        (relative_entropy rI sS sO (bt t1 ht1) (bt t2 ht2)) hkl)
  in
  let hfin =
    rI.rI_base.le_id_r zero0
      (plus0
        (mult0 (inv_pos0 t2 ht2) (minus rI.rI_base (et t2 ht2) (et t1 ht1)))
        (relative_entropy rI sS sO (bt t1 ht1) (bt t2 ht2)))
      (minus rI.rI_base (entropy_dist rI sS sO (bt t2 ht2))
        (entropy_dist rI sS sO (bt t1 ht1)))
      (id_sym
        (minus rI.rI_base (entropy_dist rI sS sO (bt t2 ht2))
          (entropy_dist rI sS sO (bt t1 ht1)))
        (plus0
          (mult0 (inv_pos0 t2 ht2) (minus rI.rI_base (et t2 ht2) (et t1 ht1)))
          (relative_entropy rI sS sO (bt t1 ht1) (bt t2 ht2)))
        (recovery_entropy_gain rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t1 t2 ht1 ht2))
      hsum
  in
  rI.rI_base.le_id_r (entropy_dist rI sS sO (bt t1 ht1))
    (plus0 (entropy_dist rI sS sO (bt t1 ht1))
      (minus rI.rI_base (entropy_dist rI sS sO (bt t2 ht2))
        (entropy_dist rI sS sO (bt t1 ht1))))
    (entropy_dist rI sS sO (bt t2 ht2))
    (minus_plus_cancel rI (entropy_dist rI sS sO (bt t1 ht1))
      (entropy_dist rI sS sO (bt t2 ht2)))
    (le_plus_nonneg_r rI (entropy_dist rI sS sO (bt t1 ht1))
      (minus rI.rI_base (entropy_dist rI sS sO (bt t2 ht2))
        (entropy_dist rI sS sO (bt t1 ht1)))
      hfin)))

(** val entropy_temp_strict_mono :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> (r -> r -> lt ->
    lt -> lt -> lt) -> (r -> r -> lt -> lt) -> (r -> r -> r -> r -> lt -> le
    -> lt) -> r -> r -> lt -> lt -> lt -> lt -> lt **)

let entropy_temp_strict_mono rI sS sO =
  let zero0 = rI.rI_base.zero in
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let inv_pos0 = rI.rI_base.inv_pos in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec inv_pos_lt_compat lt_minus_nonneg lt_plus_compat_lt_le ->
  let bt = fun t ht ->
    boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
      t ht
  in
  let et = fun t ht ->
    energy_exp_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t ht
  in
  (fun t1 t2 ht1 ht2 hlt hkl12 ->
  let hdE =
    energy_exp_temp_strict_mono rI sS sO base_loss sum_over_S_pos
      inv_pos_lt_compat lt_minus_nonneg z_temp z_temp_spec t1 t2 ht1 ht2 hlt
      hkl12
  in
  let hterm =
    rI.mult_positive (inv_pos0 t2 ht2)
      (minus rI.rI_base (et t2 ht2) (et t1 ht1)) (rI.inv_pos_pos t2 ht2) hdE
  in
  let hkl21 =
    gibbs_inequality rI sS sO (bt t1 ht1) (bt t2 ht2)
      (boltzmann_dist_temp_normalized rI sS sO base_loss sum_over_S_pos
        z_temp z_temp_spec t1 ht1)
      (fun s0 ->
      boltzmann_dist_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t1 ht1 s0)
      (boltzmann_dist_temp_normalized rI sS sO base_loss sum_over_S_pos
        z_temp z_temp_spec t2 ht2)
      (fun s0 ->
      boltzmann_dist_temp_pos rI sS sO base_loss sum_over_S_pos z_temp
        z_temp_spec t2 ht2 s0)
  in
  let hsum =
    rI.rI_base.lt_le_trans zero0
      (mult0 (inv_pos0 t2 ht2) (minus rI.rI_base (et t2 ht2) (et t1 ht1)))
      (plus0
        (mult0 (inv_pos0 t2 ht2) (minus rI.rI_base (et t2 ht2) (et t1 ht1)))
        (relative_entropy rI sS sO (bt t1 ht1) (bt t2 ht2)))
      hterm
      (le_plus_nonneg_r rI
        (mult0 (inv_pos0 t2 ht2) (minus rI.rI_base (et t2 ht2) (et t1 ht1)))
        (relative_entropy rI sS sO (bt t1 ht1) (bt t2 ht2)) hkl21)
  in
  let hfin =
    rI.rI_base.lt_id_r zero0
      (plus0
        (mult0 (inv_pos0 t2 ht2) (minus rI.rI_base (et t2 ht2) (et t1 ht1)))
        (relative_entropy rI sS sO (bt t1 ht1) (bt t2 ht2)))
      (minus rI.rI_base (entropy_dist rI sS sO (bt t2 ht2))
        (entropy_dist rI sS sO (bt t1 ht1)))
      (id_sym
        (minus rI.rI_base (entropy_dist rI sS sO (bt t2 ht2))
          (entropy_dist rI sS sO (bt t1 ht1)))
        (plus0
          (mult0 (inv_pos0 t2 ht2) (minus rI.rI_base (et t2 ht2) (et t1 ht1)))
          (relative_entropy rI sS sO (bt t1 ht1) (bt t2 ht2)))
        (recovery_entropy_gain rI sS sO base_loss sum_over_S_pos z_temp
          z_temp_spec t1 t2 ht1 ht2))
      hsum
  in
  rI.rI_base.lt_id_r (entropy_dist rI sS sO (bt t1 ht1))
    (plus0 (entropy_dist rI sS sO (bt t1 ht1))
      (minus rI.rI_base (entropy_dist rI sS sO (bt t2 ht2))
        (entropy_dist rI sS sO (bt t1 ht1))))
    (entropy_dist rI sS sO (bt t2 ht2))
    (minus_plus_cancel rI (entropy_dist rI sS sO (bt t1 ht1))
      (entropy_dist rI sS sO (bt t2 ht2)))
    (id_transport (rI.rI_base.plus zero0 (entropy_dist rI sS sO (bt t1 ht1)))
      (entropy_dist rI sS sO (bt t1 ht1))
      (id_trans (rI.rI_base.plus zero0 (entropy_dist rI sS sO (bt t1 ht1)))
        (rI.rI_base.plus (entropy_dist rI sS sO (bt t1 ht1)) zero0)
        (entropy_dist rI sS sO (bt t1 ht1))
        (rI.rI_base.plus_comm zero0 (entropy_dist rI sS sO (bt t1 ht1)))
        (rI.rI_base.plus_zero (entropy_dist rI sS sO (bt t1 ht1))))
      (id_transport
        (rI.rI_base.plus
          (minus rI.rI_base (entropy_dist rI sS sO (bt t2 ht2))
            (entropy_dist rI sS sO (bt t1 ht1)))
          (entropy_dist rI sS sO (bt t1 ht1)))
        (rI.rI_base.plus (entropy_dist rI sS sO (bt t1 ht1))
          (minus rI.rI_base (entropy_dist rI sS sO (bt t2 ht2))
            (entropy_dist rI sS sO (bt t1 ht1))))
        (rI.rI_base.plus_comm
          (minus rI.rI_base (entropy_dist rI sS sO (bt t2 ht2))
            (entropy_dist rI sS sO (bt t1 ht1)))
          (entropy_dist rI sS sO (bt t1 ht1)))
        (lt_plus_compat_lt_le zero0
          (minus rI.rI_base (entropy_dist rI sS sO (bt t2 ht2))
            (entropy_dist rI sS sO (bt t1 ht1)))
          (entropy_dist rI sS sO (bt t1 ht1))
          (entropy_dist rI sS sO (bt t1 ht1)) hfin
          (rI.rI_base.le_refl (entropy_dist rI sS sO (bt t1 ht1))))))))

(** val recovery_entropy_gain_alt :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> r -> r -> lt ->
    lt -> r id **)

let recovery_entropy_gain_alt rI sS sO =
  let plus0 = rI.rI_base.plus in
  let mult0 = rI.rI_base.mult in
  let opp0 = rI.rI_base.opp in
  let inv_pos0 = rI.rI_base.inv_pos in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec ->
  let bt = fun t ht ->
    boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
      t ht
  in
  let et = fun t ht ->
    energy_exp_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec t ht
  in
  (fun t1 t2 ht1 ht2 ->
  let b1 = inv_pos0 t1 ht1 in
  let b2 = inv_pos0 t2 ht2 in
  let dE = minus rI.rI_base (et t2 ht2) (et t1 ht1) in
  let k12 = relative_entropy rI sS sO (bt t2 ht2) (bt t1 ht1) in
  let k21 = relative_entropy rI sS sO (bt t1 ht1) (bt t2 ht2) in
  let hsym =
    temp_strict_ident2 rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
      t1 t2 ht1 ht2
  in
  let hb1 =
    id_sym (plus0 b2 (minus rI.rI_base b1 b2)) b1
      (id_trans (rI.rI_base.plus b2 (rI.rI_base.plus b1 (opp0 b2)))
        (rI.rI_base.plus (rI.rI_base.plus b2 b1) (opp0 b2)) b1
        (rI.rI_base.plus_assoc b2 b1 (opp0 b2))
        (id_trans (plus0 (rI.rI_base.plus b2 b1) (opp0 b2))
          (plus0 (rI.rI_base.plus b1 b2) (opp0 b2)) b1
          (id_cong (fun w -> plus0 w (opp0 b2)) (rI.rI_base.plus b2 b1)
            (rI.rI_base.plus b1 b2) (rI.rI_base.plus_comm b2 b1))
          (id_trans (rI.rI_base.plus (rI.rI_base.plus b1 b2) (opp0 b2))
            (rI.rI_base.plus b1 (rI.rI_base.plus b2 (opp0 b2))) b1
            (id_sym (rI.rI_base.plus b1 (rI.rI_base.plus b2 (opp0 b2)))
              (rI.rI_base.plus (rI.rI_base.plus b1 b2) (opp0 b2))
              (rI.rI_base.plus_assoc b1 b2 (opp0 b2)))
            (id_trans (plus0 b1 (rI.rI_base.plus b2 (rI.rI_base.opp b2)))
              (plus0 b1 rI.rI_base.zero) b1
              (id_cong (fun w -> plus0 b1 w)
                (rI.rI_base.plus b2 (rI.rI_base.opp b2)) rI.rI_base.zero
                (rI.rI_base.plus_opp b2))
              (rI.rI_base.plus_zero b1)))))
  in
  let hdistr =
    id_trans (mult0 b1 dE) (mult0 (plus0 b2 (minus rI.rI_base b1 b2)) dE)
      (plus0 (mult0 b2 dE) (mult0 (minus rI.rI_base b1 b2) dE))
      (id_cong (fun w -> mult0 w dE) b1 (plus0 b2 (minus rI.rI_base b1 b2))
        hb1)
      (mult_plus_distr_r rI b2 (minus rI.rI_base b1 b2) dE)
  in
  let hsym' =
    id_trans (mult0 (minus rI.rI_base b1 b2) dE) (plus0 k12 k21)
      (rI.rI_base.plus k21 k12)
      (id_sym (plus0 k12 k21) (mult0 (minus rI.rI_base b1 b2) dE) hsym)
      (rI.rI_base.plus_comm k12 k21)
  in
  let hcancel =
    id_trans (rI.rI_base.plus (rI.rI_base.plus k21 k12) (opp0 k12))
      (rI.rI_base.plus k21 (rI.rI_base.plus k12 (opp0 k12))) k21
      (id_sym (rI.rI_base.plus k21 (rI.rI_base.plus k12 (opp0 k12)))
        (rI.rI_base.plus (rI.rI_base.plus k21 k12) (opp0 k12))
        (rI.rI_base.plus_assoc k21 k12 (opp0 k12)))
      (id_trans (plus0 k21 (rI.rI_base.plus k12 (rI.rI_base.opp k12)))
        (plus0 k21 rI.rI_base.zero) k21
        (id_cong (fun w -> plus0 k21 w)
          (rI.rI_base.plus k12 (rI.rI_base.opp k12)) rI.rI_base.zero
          (rI.rI_base.plus_opp k12))
        (rI.rI_base.plus_zero k21))
  in
  let hstep1 =
    id_trans (plus0 (mult0 b2 dE) k21)
      (plus0 (mult0 b2 dE) (minus rI.rI_base (plus0 k21 k12) k12))
      (minus rI.rI_base (plus0 (mult0 b2 dE) (plus0 k21 k12)) k12)
      (id_cong (fun w -> plus0 (mult0 b2 dE) w) k21
        (minus rI.rI_base (plus0 k21 k12) k12)
        (id_sym (minus rI.rI_base (plus0 k21 k12) k12) k21 hcancel))
      (rI.rI_base.plus_assoc (mult0 b2 dE) (plus0 k21 k12) (opp0 k12))
  in
  let hstep2 =
    id_cong (fun w -> minus rI.rI_base w k12)
      (plus0 (mult0 b2 dE) (plus0 k21 k12)) (mult0 b1 dE)
      (id_sym (mult0 b1 dE) (plus0 (mult0 b2 dE) (plus0 k21 k12))
        (id_trans (mult0 b1 dE)
          (plus0 (mult0 b2 dE) (mult0 (minus rI.rI_base b1 b2) dE))
          (plus0 (mult0 b2 dE) (plus0 k21 k12)) hdistr
          (id_cong (fun w -> plus0 (mult0 b2 dE) w)
            (mult0 (minus rI.rI_base b1 b2) dE) (plus0 k21 k12) hsym')))
  in
  id_trans
    (minus rI.rI_base (entropy_dist rI sS sO (bt t2 ht2))
      (entropy_dist rI sS sO (bt t1 ht1)))
    (plus0
      (mult0 (inv_pos0 t2 ht2) (minus rI.rI_base (et t2 ht2) (et t1 ht1)))
      (relative_entropy rI sS sO (bt t1 ht1) (bt t2 ht2)))
    (minus rI.rI_base (mult0 b1 dE) k12)
    (recovery_entropy_gain rI sS sO base_loss sum_over_S_pos z_temp
      z_temp_spec t1 t2 ht1 ht2)
    (id_trans (plus0 (mult0 b2 dE) k21)
      (minus rI.rI_base (plus0 (mult0 b2 dE) (plus0 k21 k12)) k12)
      (minus rI.rI_base (mult0 b1 dE) k12) hstep1 hstep2)))

type fw_verdict = (le, (r, r id) sigT) or0

(** val fw_detect_warm :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> (r -> r -> lt ->
    lt -> lt -> lt) -> (r -> r -> lt -> lt) -> (r -> r -> r -> r -> lt -> le
    -> lt) -> r -> r -> lt -> (r, r id) sigT -> (r, (lt, (lt, (le, r id)
    and0) and0) sigT) sigT **)

let fw_detect_warm rI sS sO =
  let plus0 = rI.rI_base.plus in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec inv_pos_lt_compat lt_minus_nonneg lt_plus_compat_lt_le _ t ht _ ->
  let ht' = fw_double_pos rI t ht in
  let hup = fw_lt_double rI lt_plus_compat_lt_le t ht in
  ExistT ((plus0 t t), (ExistT (ht', (Pair (hup, (Pair
  ((entropy_temp_mono rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
     inv_pos_lt_compat lt_minus_nonneg t (plus0 t t) ht ht' hup),
  (recovery_entropy_gain rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
    t (plus0 t t) ht ht')))))))))

(** val firewall_loop :
    realInterfaceEnhanced -> stateSpace -> sumOver -> (s -> r) -> ((s -> r)
    -> (s -> lt) -> lt) -> (r -> r) -> (r -> lt -> r id) -> (r -> r -> lt ->
    lt -> lt -> lt) -> (r -> r -> lt -> lt) -> (r -> r -> r -> r -> lt -> le
    -> lt) -> r -> r -> lt -> fw_verdict -> (r, (lt, (le, (le, fw_verdict)
    and0) and0) sigT) sigT **)

let firewall_loop rI sS sO =
  let plus0 = rI.rI_base.plus in
  (fun base_loss sum_over_S_pos z_temp z_temp_spec inv_pos_lt_compat lt_minus_nonneg lt_plus_compat_lt_le ->
  let bt = fun t ht ->
    boltzmann_dist_temp rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
      t ht
  in
  (fun hmin t ht v ->
  match v with
  | Inl l ->
    ExistT (t, (ExistT (ht, (Pair ((rI.rI_base.le_refl t), (Pair
      ((rI.rI_base.le_refl (entropy_dist rI sS sO (bt t ht))), (Inl l))))))))
  | Inr _ ->
    let ht' = fw_double_pos rI t ht in
    let hup = fw_lt_double rI lt_plus_compat_lt_le t ht in
    ExistT ((plus0 t t), (ExistT (ht', (Pair
    ((rI.rI_base.lt_le_iff t (plus0 t t) (Inl hup)), (Pair
    ((entropy_temp_mono rI sS sO base_loss sum_over_S_pos z_temp z_temp_spec
       inv_pos_lt_compat lt_minus_nonneg t (plus0 t t) ht ht' hup),
    (Inr (ExistT
    ((minus rI.rI_base (entropy_dist rI sS sO (bt (plus0 t t) ht')) hmin),
    Id_refl))))))))))))
