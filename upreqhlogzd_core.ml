
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

module RealInterfaceEnhancedMod =
 struct
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

  (** val req_refl : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 req **)

  let req_refl realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.req_refl

  (** val req_sym :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 req -> 'a1 req **)

  let req_sym realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.req_sym

  (** val req_trans :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 req ->
      'a1 req -> 'a1 req **)

  let req_trans realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.req_trans

  (** val zero : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 **)

  let zero realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.zero

  (** val one : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 **)

  let one realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.one

  (** val plus : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 **)

  let plus realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.plus

  (** val mult : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 **)

  let mult realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.mult

  (** val opp : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 **)

  let opp realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.opp

  type 'r lt = __

  type 'r le = __

  (** val req_plus_compat :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
      req -> 'a1 req -> 'a1 req **)

  let req_plus_compat realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.req_plus_compat

  (** val req_mult_compat :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
      req -> 'a1 req -> 'a1 req **)

  let req_mult_compat realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.req_mult_compat

  (** val plus_assoc :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 req **)

  let plus_assoc realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.plus_assoc

  (** val plus_comm :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 req **)

  let plus_comm realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.plus_comm

  (** val plus_zero :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 req **)

  let plus_zero realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.plus_zero

  (** val plus_opp : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 req **)

  let plus_opp realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.plus_opp

  (** val mult_comm :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 req **)

  let mult_comm realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.mult_comm

  (** val mult_one : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 req **)

  let mult_one realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.mult_one

  (** val distrib :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 req **)

  let distrib realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.distrib

  (** val le_refl : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 le **)

  let le_refl realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.le_refl

  (** val le_trans :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 le ->
      'a1 le -> 'a1 le **)

  let le_trans realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.le_trans

  (** val lt_le_iff :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> ('a1 lt, 'a1 req)
      or0 -> 'a1 le **)

  let lt_le_iff realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.lt_le_iff

  (** val le_id_l :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 req ->
      'a1 le -> 'a1 le **)

  let le_id_l realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.le_id_l

  (** val le_id_r :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 req ->
      'a1 le -> 'a1 le **)

  let le_id_r realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.le_id_r

  (** val inv_pos :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 lt -> 'a1 **)

  let inv_pos realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.inv_pos

  (** val inv_pos_correct :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 lt -> 'a1 req **)

  let inv_pos_correct realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.inv_pos_correct

  (** val one_pos : 'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 lt **)

  let one_pos realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.one_pos

  (** val le_plus_compat :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
      le -> 'a1 le -> 'a1 le **)

  let le_plus_compat realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.le_plus_compat

  (** val mult_positive :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 lt -> 'a1 lt
      -> 'a1 lt **)

  let mult_positive realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.mult_positive

  (** val opp_le_compat :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 le -> 'a1 le **)

  let opp_le_compat realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.opp_le_compat

  (** val inv_pos_pos :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 lt -> 'a1 lt **)

  let inv_pos_pos realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.inv_pos_pos

  (** val log :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 lt -> 'a1 **)

  let log realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.log

  (** val log_mult :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 lt -> 'a1 lt
      -> 'a1 req **)

  let log_mult realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.log_mult

  (** val log_one :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 lt -> 'a1 req **)

  let log_one realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.log_one
 end

(** val req_minus :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 ->
    'a1 -> 'a1 **)

let req_minus rIS a b =
  rIS.RealInterfaceEnhancedMod.plus a (rIS.RealInterfaceEnhancedMod.opp b)

(** val req_plus_zero_l :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 ->
    'a1 RealInterfaceEnhancedMod.req **)

let req_plus_zero_l rIS a =
  rIS.RealInterfaceEnhancedMod.req_trans
    (rIS.RealInterfaceEnhancedMod.plus rIS.RealInterfaceEnhancedMod.zero a)
    (rIS.RealInterfaceEnhancedMod.plus a rIS.RealInterfaceEnhancedMod.zero) a
    (rIS.RealInterfaceEnhancedMod.plus_comm rIS.RealInterfaceEnhancedMod.zero
      a)
    (rIS.RealInterfaceEnhancedMod.plus_zero a)

(** val req_plus_opp_l :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 ->
    'a1 RealInterfaceEnhancedMod.req **)

let req_plus_opp_l rIS a =
  rIS.RealInterfaceEnhancedMod.req_trans
    (rIS.RealInterfaceEnhancedMod.plus (rIS.RealInterfaceEnhancedMod.opp a) a)
    (rIS.RealInterfaceEnhancedMod.plus a (rIS.RealInterfaceEnhancedMod.opp a))
    rIS.RealInterfaceEnhancedMod.zero
    (rIS.RealInterfaceEnhancedMod.plus_comm
      (rIS.RealInterfaceEnhancedMod.opp a) a)
    (rIS.RealInterfaceEnhancedMod.plus_opp a)

(** val req_add_cancel_l :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 ->
    'a1 -> 'a1 -> 'a1 RealInterfaceEnhancedMod.req -> 'a1
    RealInterfaceEnhancedMod.req **)

let req_add_cancel_l rIS u v w h =
  rIS.RealInterfaceEnhancedMod.req_trans u
    (rIS.RealInterfaceEnhancedMod.plus u rIS.RealInterfaceEnhancedMod.zero) w
    (rIS.RealInterfaceEnhancedMod.req_sym
      (rIS.RealInterfaceEnhancedMod.plus u rIS.RealInterfaceEnhancedMod.zero)
      u (rIS.RealInterfaceEnhancedMod.plus_zero u))
    (rIS.RealInterfaceEnhancedMod.req_trans
      (rIS.RealInterfaceEnhancedMod.plus u rIS.RealInterfaceEnhancedMod.zero)
      (rIS.RealInterfaceEnhancedMod.plus u
        (rIS.RealInterfaceEnhancedMod.plus v
          (rIS.RealInterfaceEnhancedMod.opp v)))
      w
      (rIS.RealInterfaceEnhancedMod.req_plus_compat u u
        rIS.RealInterfaceEnhancedMod.zero
        (rIS.RealInterfaceEnhancedMod.plus v
          (rIS.RealInterfaceEnhancedMod.opp v))
        (rIS.RealInterfaceEnhancedMod.req_refl u)
        (rIS.RealInterfaceEnhancedMod.req_sym
          (rIS.RealInterfaceEnhancedMod.plus v
            (rIS.RealInterfaceEnhancedMod.opp v))
          rIS.RealInterfaceEnhancedMod.zero
          (rIS.RealInterfaceEnhancedMod.plus_opp v)))
      (rIS.RealInterfaceEnhancedMod.req_trans
        (rIS.RealInterfaceEnhancedMod.plus u
          (rIS.RealInterfaceEnhancedMod.plus v
            (rIS.RealInterfaceEnhancedMod.opp v)))
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.plus u v)
          (rIS.RealInterfaceEnhancedMod.opp v))
        w
        (rIS.RealInterfaceEnhancedMod.plus_assoc u v
          (rIS.RealInterfaceEnhancedMod.opp v))
        (rIS.RealInterfaceEnhancedMod.req_trans
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.plus u v)
            (rIS.RealInterfaceEnhancedMod.opp v))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.plus w v)
            (rIS.RealInterfaceEnhancedMod.opp v))
          w
          (rIS.RealInterfaceEnhancedMod.req_plus_compat
            (rIS.RealInterfaceEnhancedMod.plus u v)
            (rIS.RealInterfaceEnhancedMod.plus w v)
            (rIS.RealInterfaceEnhancedMod.opp v)
            (rIS.RealInterfaceEnhancedMod.opp v) h
            (rIS.RealInterfaceEnhancedMod.req_refl
              (rIS.RealInterfaceEnhancedMod.opp v)))
          (rIS.RealInterfaceEnhancedMod.req_trans
            (rIS.RealInterfaceEnhancedMod.plus
              (rIS.RealInterfaceEnhancedMod.plus w v)
              (rIS.RealInterfaceEnhancedMod.opp v))
            (rIS.RealInterfaceEnhancedMod.plus w
              (rIS.RealInterfaceEnhancedMod.plus v
                (rIS.RealInterfaceEnhancedMod.opp v)))
            w
            (rIS.RealInterfaceEnhancedMod.req_sym
              (rIS.RealInterfaceEnhancedMod.plus w
                (rIS.RealInterfaceEnhancedMod.plus v
                  (rIS.RealInterfaceEnhancedMod.opp v)))
              (rIS.RealInterfaceEnhancedMod.plus
                (rIS.RealInterfaceEnhancedMod.plus w v)
                (rIS.RealInterfaceEnhancedMod.opp v))
              (rIS.RealInterfaceEnhancedMod.plus_assoc w v
                (rIS.RealInterfaceEnhancedMod.opp v)))
            (rIS.RealInterfaceEnhancedMod.req_trans
              (rIS.RealInterfaceEnhancedMod.plus w
                (rIS.RealInterfaceEnhancedMod.plus v
                  (rIS.RealInterfaceEnhancedMod.opp v)))
              (rIS.RealInterfaceEnhancedMod.plus w
                rIS.RealInterfaceEnhancedMod.zero)
              w
              (rIS.RealInterfaceEnhancedMod.req_plus_compat w w
                (rIS.RealInterfaceEnhancedMod.plus v
                  (rIS.RealInterfaceEnhancedMod.opp v))
                rIS.RealInterfaceEnhancedMod.zero
                (rIS.RealInterfaceEnhancedMod.req_refl w)
                (rIS.RealInterfaceEnhancedMod.plus_opp v))
              (rIS.RealInterfaceEnhancedMod.plus_zero w))))))

(** val req_minus_plus_cancel_r :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 ->
    'a1 -> 'a1 RealInterfaceEnhancedMod.req **)

let req_minus_plus_cancel_r rIS a b =
  rIS.RealInterfaceEnhancedMod.req_trans
    (rIS.RealInterfaceEnhancedMod.plus
      (rIS.RealInterfaceEnhancedMod.plus a b)
      (rIS.RealInterfaceEnhancedMod.opp a))
    (rIS.RealInterfaceEnhancedMod.plus a
      (rIS.RealInterfaceEnhancedMod.plus b
        (rIS.RealInterfaceEnhancedMod.opp a)))
    b
    (rIS.RealInterfaceEnhancedMod.req_sym
      (rIS.RealInterfaceEnhancedMod.plus a
        (rIS.RealInterfaceEnhancedMod.plus b
          (rIS.RealInterfaceEnhancedMod.opp a)))
      (rIS.RealInterfaceEnhancedMod.plus
        (rIS.RealInterfaceEnhancedMod.plus a b)
        (rIS.RealInterfaceEnhancedMod.opp a))
      (rIS.RealInterfaceEnhancedMod.plus_assoc a b
        (rIS.RealInterfaceEnhancedMod.opp a)))
    (rIS.RealInterfaceEnhancedMod.req_trans
      (rIS.RealInterfaceEnhancedMod.plus a
        (rIS.RealInterfaceEnhancedMod.plus b
          (rIS.RealInterfaceEnhancedMod.opp a)))
      (rIS.RealInterfaceEnhancedMod.plus a
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.opp a) b))
      b
      (rIS.RealInterfaceEnhancedMod.req_plus_compat a a
        (rIS.RealInterfaceEnhancedMod.plus b
          (rIS.RealInterfaceEnhancedMod.opp a))
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.opp a) b)
        (rIS.RealInterfaceEnhancedMod.req_refl a)
        (rIS.RealInterfaceEnhancedMod.plus_comm b
          (rIS.RealInterfaceEnhancedMod.opp a)))
      (rIS.RealInterfaceEnhancedMod.req_trans
        (rIS.RealInterfaceEnhancedMod.plus a
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.opp a) b))
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.plus a
            (rIS.RealInterfaceEnhancedMod.opp a))
          b)
        b
        (rIS.RealInterfaceEnhancedMod.plus_assoc a
          (rIS.RealInterfaceEnhancedMod.opp a) b)
        (rIS.RealInterfaceEnhancedMod.req_trans
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.plus a
              (rIS.RealInterfaceEnhancedMod.opp a))
            b)
          (rIS.RealInterfaceEnhancedMod.plus
            rIS.RealInterfaceEnhancedMod.zero b)
          b
          (rIS.RealInterfaceEnhancedMod.req_plus_compat
            (rIS.RealInterfaceEnhancedMod.plus a
              (rIS.RealInterfaceEnhancedMod.opp a))
            rIS.RealInterfaceEnhancedMod.zero b b
            (rIS.RealInterfaceEnhancedMod.plus_opp a)
            (rIS.RealInterfaceEnhancedMod.req_refl b))
          (rIS.RealInterfaceEnhancedMod.req_trans
            (rIS.RealInterfaceEnhancedMod.plus
              rIS.RealInterfaceEnhancedMod.zero b)
            (rIS.RealInterfaceEnhancedMod.plus b
              rIS.RealInterfaceEnhancedMod.zero)
            b
            (rIS.RealInterfaceEnhancedMod.plus_comm
              rIS.RealInterfaceEnhancedMod.zero b)
            (rIS.RealInterfaceEnhancedMod.plus_zero b)))))

(** val req_le_plus_nonneg_r :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 ->
    'a1 -> 'a1 RealInterfaceEnhancedMod.le -> 'a1 RealInterfaceEnhancedMod.le **)

let req_le_plus_nonneg_r rIS a b hb =
  rIS.RealInterfaceEnhancedMod.le_trans a
    (rIS.RealInterfaceEnhancedMod.plus a rIS.RealInterfaceEnhancedMod.zero)
    (rIS.RealInterfaceEnhancedMod.plus a b)
    (rIS.RealInterfaceEnhancedMod.le_id_r a a
      (rIS.RealInterfaceEnhancedMod.plus a rIS.RealInterfaceEnhancedMod.zero)
      (rIS.RealInterfaceEnhancedMod.req_sym
        (rIS.RealInterfaceEnhancedMod.plus a
          rIS.RealInterfaceEnhancedMod.zero)
        a (rIS.RealInterfaceEnhancedMod.plus_zero a))
      (rIS.RealInterfaceEnhancedMod.le_refl a))
    (rIS.RealInterfaceEnhancedMod.le_plus_compat a a
      rIS.RealInterfaceEnhancedMod.zero b
      (rIS.RealInterfaceEnhancedMod.le_refl a) hb)

(** val z_aud_req :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
    'a1) -> 'a1) -> ('a2 -> bool) -> ('a2 -> 'a1) -> 'a1 **)

let z_aud_req rIS sumf post_aud p =
  sumf (fun s ->
    match post_aud s with
    | True -> p s
    | False -> rIS.RealInterfaceEnhancedMod.zero)

(** val kl_proj_closed :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
    'a1) -> 'a1) -> ('a2 -> bool) -> ('a2 -> 'a1) -> ('a2 -> 'a1
    RealInterfaceEnhancedMod.lt) -> 'a1 RealInterfaceEnhancedMod.lt -> ('a2
    -> 'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.lt) -> 'a2 -> 'a1 **)

let kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s =
  rIS.RealInterfaceEnhancedMod.mult (q s)
    (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
      (rIS.RealInterfaceEnhancedMod.plus
        (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ))))

(** val rkl_opp_zero :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1
    RealInterfaceEnhancedMod.req **)

let rkl_opp_zero rIS =
  rIS.RealInterfaceEnhancedMod.req_trans
    (rIS.RealInterfaceEnhancedMod.opp rIS.RealInterfaceEnhancedMod.zero)
    (rIS.RealInterfaceEnhancedMod.plus rIS.RealInterfaceEnhancedMod.zero
      (rIS.RealInterfaceEnhancedMod.opp rIS.RealInterfaceEnhancedMod.zero))
    rIS.RealInterfaceEnhancedMod.zero
    (rIS.RealInterfaceEnhancedMod.req_sym
      (rIS.RealInterfaceEnhancedMod.plus rIS.RealInterfaceEnhancedMod.zero
        (rIS.RealInterfaceEnhancedMod.opp rIS.RealInterfaceEnhancedMod.zero))
      (rIS.RealInterfaceEnhancedMod.opp rIS.RealInterfaceEnhancedMod.zero)
      (req_plus_zero_l rIS
        (rIS.RealInterfaceEnhancedMod.opp rIS.RealInterfaceEnhancedMod.zero)))
    (rIS.RealInterfaceEnhancedMod.plus_opp rIS.RealInterfaceEnhancedMod.zero)

(** val req_if_p_le_p :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> ('a2 ->
    bool) -> ('a2 -> 'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.lt) -> 'a2
    -> 'a1 RealInterfaceEnhancedMod.le **)

let req_if_p_le_p rIS post_aud p hp_pos s =
  let b = post_aud s in
  (match b with
   | True -> rIS.RealInterfaceEnhancedMod.le_refl (p s)
   | False ->
     rIS.RealInterfaceEnhancedMod.lt_le_iff rIS.RealInterfaceEnhancedMod.zero
       (p s) (Inl (hp_pos s)))

(** val req_Z_aud_le_one :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
    'a1) -> 'a1) -> (('a2 -> 'a1) -> ('a2 -> 'a1) -> ('a2 -> 'a1
    RealInterfaceEnhancedMod.le) -> 'a1 RealInterfaceEnhancedMod.le) -> ('a2
    -> bool) -> ('a2 -> 'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.lt) ->
    'a1 RealInterfaceEnhancedMod.le **)

let req_Z_aud_le_one rIS _ sum_le post_aud p hp_pos =
  sum_le (fun s ->
    match post_aud s with
    | True -> p s
    | False -> rIS.RealInterfaceEnhancedMod.zero) p
    (req_if_p_le_p rIS post_aud p hp_pos)

(** val req_kl_minus_split :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 ->
    'a1 -> 'a1 -> 'a1 RealInterfaceEnhancedMod.req **)

let req_kl_minus_split rIS a b c =
  rIS.RealInterfaceEnhancedMod.req_trans
    (rIS.RealInterfaceEnhancedMod.plus a (rIS.RealInterfaceEnhancedMod.opp c))
    (rIS.RealInterfaceEnhancedMod.plus a
      (rIS.RealInterfaceEnhancedMod.plus (rIS.RealInterfaceEnhancedMod.opp b)
        (rIS.RealInterfaceEnhancedMod.plus b
          (rIS.RealInterfaceEnhancedMod.opp c))))
    (rIS.RealInterfaceEnhancedMod.plus
      (rIS.RealInterfaceEnhancedMod.plus a
        (rIS.RealInterfaceEnhancedMod.opp b))
      (rIS.RealInterfaceEnhancedMod.plus b
        (rIS.RealInterfaceEnhancedMod.opp c)))
    (rIS.RealInterfaceEnhancedMod.req_plus_compat a a
      (rIS.RealInterfaceEnhancedMod.opp c)
      (rIS.RealInterfaceEnhancedMod.plus (rIS.RealInterfaceEnhancedMod.opp b)
        (rIS.RealInterfaceEnhancedMod.plus b
          (rIS.RealInterfaceEnhancedMod.opp c)))
      (rIS.RealInterfaceEnhancedMod.req_refl a)
      (rIS.RealInterfaceEnhancedMod.req_trans
        (rIS.RealInterfaceEnhancedMod.opp c)
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.opp b) b)
          (rIS.RealInterfaceEnhancedMod.opp c))
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.opp b)
          (rIS.RealInterfaceEnhancedMod.plus b
            (rIS.RealInterfaceEnhancedMod.opp c)))
        (rIS.RealInterfaceEnhancedMod.req_trans
          (rIS.RealInterfaceEnhancedMod.opp c)
          (rIS.RealInterfaceEnhancedMod.plus
            rIS.RealInterfaceEnhancedMod.zero
            (rIS.RealInterfaceEnhancedMod.opp c))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.plus
              (rIS.RealInterfaceEnhancedMod.opp b) b)
            (rIS.RealInterfaceEnhancedMod.opp c))
          (rIS.RealInterfaceEnhancedMod.req_sym
            (rIS.RealInterfaceEnhancedMod.plus
              rIS.RealInterfaceEnhancedMod.zero
              (rIS.RealInterfaceEnhancedMod.opp c))
            (rIS.RealInterfaceEnhancedMod.opp c)
            (req_plus_zero_l rIS (rIS.RealInterfaceEnhancedMod.opp c)))
          (rIS.RealInterfaceEnhancedMod.req_plus_compat
            rIS.RealInterfaceEnhancedMod.zero
            (rIS.RealInterfaceEnhancedMod.plus
              (rIS.RealInterfaceEnhancedMod.opp b) b)
            (rIS.RealInterfaceEnhancedMod.opp c)
            (rIS.RealInterfaceEnhancedMod.opp c)
            (rIS.RealInterfaceEnhancedMod.req_sym
              (rIS.RealInterfaceEnhancedMod.plus
                (rIS.RealInterfaceEnhancedMod.opp b) b)
              rIS.RealInterfaceEnhancedMod.zero (req_plus_opp_l rIS b))
            (rIS.RealInterfaceEnhancedMod.req_refl
              (rIS.RealInterfaceEnhancedMod.opp c))))
        (rIS.RealInterfaceEnhancedMod.req_sym
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.opp b)
            (rIS.RealInterfaceEnhancedMod.plus b
              (rIS.RealInterfaceEnhancedMod.opp c)))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.plus
              (rIS.RealInterfaceEnhancedMod.opp b) b)
            (rIS.RealInterfaceEnhancedMod.opp c))
          (rIS.RealInterfaceEnhancedMod.plus_assoc
            (rIS.RealInterfaceEnhancedMod.opp b) b
            (rIS.RealInterfaceEnhancedMod.opp c)))))
    (rIS.RealInterfaceEnhancedMod.plus_assoc a
      (rIS.RealInterfaceEnhancedMod.opp b)
      (rIS.RealInterfaceEnhancedMod.plus b
        (rIS.RealInterfaceEnhancedMod.opp c)))

(** val rkl_log_inv_one_inv :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> ('a1 ->
    'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.lt
    -> 'a1 RealInterfaceEnhancedMod.req -> 'a1 RealInterfaceEnhancedMod.req)
    -> 'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1
    RealInterfaceEnhancedMod.req **)

let rkl_log_inv_one_inv rIS log_req_compat x hx =
  let hprod =
    rIS.RealInterfaceEnhancedMod.req_trans
      (rIS.RealInterfaceEnhancedMod.mult
        (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x)
      (rIS.RealInterfaceEnhancedMod.mult x
        (rIS.RealInterfaceEnhancedMod.inv_pos x hx))
      rIS.RealInterfaceEnhancedMod.one
      (rIS.RealInterfaceEnhancedMod.mult_comm
        (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x)
      (rIS.RealInterfaceEnhancedMod.inv_pos_correct x hx)
  in
  let hl1 =
    rIS.RealInterfaceEnhancedMod.req_trans
      (rIS.RealInterfaceEnhancedMod.log
        (rIS.RealInterfaceEnhancedMod.mult
          (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x)
        (rIS.RealInterfaceEnhancedMod.mult_positive
          (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos x hx) hx))
      (rIS.RealInterfaceEnhancedMod.log rIS.RealInterfaceEnhancedMod.one
        rIS.RealInterfaceEnhancedMod.one_pos)
      rIS.RealInterfaceEnhancedMod.zero
      (log_req_compat
        (rIS.RealInterfaceEnhancedMod.mult
          (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x)
        rIS.RealInterfaceEnhancedMod.one
        (rIS.RealInterfaceEnhancedMod.mult_positive
          (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos x hx) hx)
        rIS.RealInterfaceEnhancedMod.one_pos hprod)
      (rIS.RealInterfaceEnhancedMod.log_one
        rIS.RealInterfaceEnhancedMod.one_pos)
  in
  req_add_cancel_l rIS
    (rIS.RealInterfaceEnhancedMod.log
      (rIS.RealInterfaceEnhancedMod.inv_pos x hx)
      (rIS.RealInterfaceEnhancedMod.inv_pos_pos x hx))
    (rIS.RealInterfaceEnhancedMod.log x hx)
    (rIS.RealInterfaceEnhancedMod.opp (rIS.RealInterfaceEnhancedMod.log x hx))
    (rIS.RealInterfaceEnhancedMod.req_trans
      (rIS.RealInterfaceEnhancedMod.plus
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos x hx)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos x hx))
        (rIS.RealInterfaceEnhancedMod.log x hx))
      rIS.RealInterfaceEnhancedMod.zero
      (rIS.RealInterfaceEnhancedMod.plus
        (rIS.RealInterfaceEnhancedMod.opp
          (rIS.RealInterfaceEnhancedMod.log x hx))
        (rIS.RealInterfaceEnhancedMod.log x hx))
      (rIS.RealInterfaceEnhancedMod.req_trans
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.log
            (rIS.RealInterfaceEnhancedMod.inv_pos x hx)
            (rIS.RealInterfaceEnhancedMod.inv_pos_pos x hx))
          (rIS.RealInterfaceEnhancedMod.log x hx))
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.mult
            (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x)
          (rIS.RealInterfaceEnhancedMod.mult_positive
            (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x
            (rIS.RealInterfaceEnhancedMod.inv_pos_pos x hx) hx))
        rIS.RealInterfaceEnhancedMod.zero
        (rIS.RealInterfaceEnhancedMod.req_sym
          (rIS.RealInterfaceEnhancedMod.log
            (rIS.RealInterfaceEnhancedMod.mult
              (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x)
            (rIS.RealInterfaceEnhancedMod.mult_positive
              (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos x hx) hx))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos x hx)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos x hx))
            (rIS.RealInterfaceEnhancedMod.log x hx))
          (rIS.RealInterfaceEnhancedMod.log_mult
            (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x
            (rIS.RealInterfaceEnhancedMod.inv_pos_pos x hx) hx))
        hl1)
      (rIS.RealInterfaceEnhancedMod.req_sym
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.opp
            (rIS.RealInterfaceEnhancedMod.log x hx))
          (rIS.RealInterfaceEnhancedMod.log x hx))
        rIS.RealInterfaceEnhancedMod.zero
        (rIS.RealInterfaceEnhancedMod.req_trans
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.opp
              (rIS.RealInterfaceEnhancedMod.log x hx))
            (rIS.RealInterfaceEnhancedMod.log x hx))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.log x hx)
            (rIS.RealInterfaceEnhancedMod.opp
              (rIS.RealInterfaceEnhancedMod.log x hx)))
          rIS.RealInterfaceEnhancedMod.zero
          (rIS.RealInterfaceEnhancedMod.plus_comm
            (rIS.RealInterfaceEnhancedMod.opp
              (rIS.RealInterfaceEnhancedMod.log x hx))
            (rIS.RealInterfaceEnhancedMod.log x hx))
          (rIS.RealInterfaceEnhancedMod.plus_opp
            (rIS.RealInterfaceEnhancedMod.log x hx)))))

(** val req_kl_closed_pt :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
    'a1) -> 'a1) -> ('a2 -> bool) -> ('a2 -> 'a1) -> ('a2 -> 'a1
    RealInterfaceEnhancedMod.lt) -> 'a1 RealInterfaceEnhancedMod.lt -> ('a2
    -> 'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.lt) -> 'a2 -> 'a1
    RealInterfaceEnhancedMod.req **)

let req_kl_closed_pt rIS sumf post_aud p hp_pos hZ q hq s =
  let hcancel =
    req_minus_plus_cancel_r rIS
      (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))
      (rIS.RealInterfaceEnhancedMod.log
        (rIS.RealInterfaceEnhancedMod.inv_pos (z_aud_req rIS sumf post_aud p)
          hZ)
        (rIS.RealInterfaceEnhancedMod.inv_pos_pos
          (z_aud_req rIS sumf post_aud p) hZ))
  in
  let hinner =
    rIS.RealInterfaceEnhancedMod.req_trans
      (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
        (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s)))
      (rIS.RealInterfaceEnhancedMod.plus
        (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos
                (z_aud_req rIS sumf post_aud p) hZ)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                (z_aud_req rIS sumf post_aud p) hZ))))
        (req_minus rIS
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos
                (z_aud_req rIS sumf post_aud p) hZ)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                (z_aud_req rIS sumf post_aud p) hZ)))
          (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))))
      (rIS.RealInterfaceEnhancedMod.plus
        (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos
                (z_aud_req rIS sumf post_aud p) hZ)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                (z_aud_req rIS sumf post_aud p) hZ))))
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ)))
      (req_kl_minus_split rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))
          (rIS.RealInterfaceEnhancedMod.log
            (rIS.RealInterfaceEnhancedMod.inv_pos
              (z_aud_req rIS sumf post_aud p) hZ)
            (rIS.RealInterfaceEnhancedMod.inv_pos_pos
              (z_aud_req rIS sumf post_aud p) hZ)))
        (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s)))
      (rIS.RealInterfaceEnhancedMod.req_plus_compat
        (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos
                (z_aud_req rIS sumf post_aud p) hZ)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                (z_aud_req rIS sumf post_aud p) hZ))))
        (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos
                (z_aud_req rIS sumf post_aud p) hZ)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                (z_aud_req rIS sumf post_aud p) hZ))))
        (req_minus rIS
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos
                (z_aud_req rIS sumf post_aud p) hZ)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                (z_aud_req rIS sumf post_aud p) hZ)))
          (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s)))
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ))
        (rIS.RealInterfaceEnhancedMod.req_refl
          (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
            (rIS.RealInterfaceEnhancedMod.plus
              (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))
              (rIS.RealInterfaceEnhancedMod.log
                (rIS.RealInterfaceEnhancedMod.inv_pos
                  (z_aud_req rIS sumf post_aud p) hZ)
                (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                  (z_aud_req rIS sumf post_aud p) hZ)))))
        hcancel)
  in
  rIS.RealInterfaceEnhancedMod.req_trans
    (rIS.RealInterfaceEnhancedMod.mult (q s)
      (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
        (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))))
    (rIS.RealInterfaceEnhancedMod.mult (q s)
      (rIS.RealInterfaceEnhancedMod.plus
        (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos
                (z_aud_req rIS sumf post_aud p) hZ)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                (z_aud_req rIS sumf post_aud p) hZ))))
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ))))
    (rIS.RealInterfaceEnhancedMod.plus
      (rIS.RealInterfaceEnhancedMod.mult (q s)
        (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos
                (z_aud_req rIS sumf post_aud p) hZ)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                (z_aud_req rIS sumf post_aud p) hZ)))))
      (rIS.RealInterfaceEnhancedMod.mult (q s)
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ))))
    (rIS.RealInterfaceEnhancedMod.req_mult_compat (q s) (q s)
      (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
        (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s)))
      (rIS.RealInterfaceEnhancedMod.plus
        (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos
                (z_aud_req rIS sumf post_aud p) hZ)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                (z_aud_req rIS sumf post_aud p) hZ))))
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ)))
      (rIS.RealInterfaceEnhancedMod.req_refl (q s)) hinner)
    (rIS.RealInterfaceEnhancedMod.distrib (q s)
      (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))
          (rIS.RealInterfaceEnhancedMod.log
            (rIS.RealInterfaceEnhancedMod.inv_pos
              (z_aud_req rIS sumf post_aud p) hZ)
            (rIS.RealInterfaceEnhancedMod.inv_pos_pos
              (z_aud_req rIS sumf post_aud p) hZ))))
      (rIS.RealInterfaceEnhancedMod.log
        (rIS.RealInterfaceEnhancedMod.inv_pos (z_aud_req rIS sumf post_aud p)
          hZ)
        (rIS.RealInterfaceEnhancedMod.inv_pos_pos
          (z_aud_req rIS sumf post_aud p) hZ)))

(** val req_kl_closed_sum_split :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
    'a1) -> 'a1) -> (('a2 -> 'a1) -> ('a2 -> 'a1) -> ('a2 -> 'a1
    RealInterfaceEnhancedMod.req) -> 'a1 RealInterfaceEnhancedMod.req) ->
    (('a2 -> 'a1) -> ('a2 -> 'a1) -> 'a1 RealInterfaceEnhancedMod.req) ->
    ('a1 -> ('a2 -> 'a1) -> 'a1 RealInterfaceEnhancedMod.req) -> ('a2 ->
    bool) -> ('a2 -> 'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.lt) -> 'a1
    RealInterfaceEnhancedMod.lt -> ('a2 -> 'a1) -> ('a2 -> 'a1
    RealInterfaceEnhancedMod.lt) -> 'a1 RealInterfaceEnhancedMod.req **)

let req_kl_closed_sum_split rIS sumf sum_ext sum_add sum_linear post_aud p hp_pos hZ q hq =
  rIS.RealInterfaceEnhancedMod.req_trans
    (sumf (fun s ->
      rIS.RealInterfaceEnhancedMod.mult (q s)
        (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
          (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s)))))
    (sumf (fun s ->
      rIS.RealInterfaceEnhancedMod.plus
        (kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s)
        (rIS.RealInterfaceEnhancedMod.mult (q s)
          (rIS.RealInterfaceEnhancedMod.log
            (rIS.RealInterfaceEnhancedMod.inv_pos
              (z_aud_req rIS sumf post_aud p) hZ)
            (rIS.RealInterfaceEnhancedMod.inv_pos_pos
              (z_aud_req rIS sumf post_aud p) hZ)))))
    (rIS.RealInterfaceEnhancedMod.plus
      (sumf (fun s -> kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s))
      (rIS.RealInterfaceEnhancedMod.mult
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ))
        (sumf q)))
    (sum_ext (fun s ->
      rIS.RealInterfaceEnhancedMod.mult (q s)
        (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
          (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s))))
      (fun s ->
      rIS.RealInterfaceEnhancedMod.plus
        (kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s)
        (rIS.RealInterfaceEnhancedMod.mult (q s)
          (rIS.RealInterfaceEnhancedMod.log
            (rIS.RealInterfaceEnhancedMod.inv_pos
              (z_aud_req rIS sumf post_aud p) hZ)
            (rIS.RealInterfaceEnhancedMod.inv_pos_pos
              (z_aud_req rIS sumf post_aud p) hZ))))
      (fun s -> req_kl_closed_pt rIS sumf post_aud p hp_pos hZ q hq s))
    (rIS.RealInterfaceEnhancedMod.req_trans
      (sumf (fun s ->
        rIS.RealInterfaceEnhancedMod.plus
          (kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s)
          (rIS.RealInterfaceEnhancedMod.mult (q s)
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos
                (z_aud_req rIS sumf post_aud p) hZ)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                (z_aud_req rIS sumf post_aud p) hZ)))))
      (rIS.RealInterfaceEnhancedMod.plus
        (sumf (fun s -> kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s))
        (sumf (fun s ->
          rIS.RealInterfaceEnhancedMod.mult (q s)
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos
                (z_aud_req rIS sumf post_aud p) hZ)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                (z_aud_req rIS sumf post_aud p) hZ)))))
      (rIS.RealInterfaceEnhancedMod.plus
        (sumf (fun s -> kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s))
        (rIS.RealInterfaceEnhancedMod.mult
          (rIS.RealInterfaceEnhancedMod.log
            (rIS.RealInterfaceEnhancedMod.inv_pos
              (z_aud_req rIS sumf post_aud p) hZ)
            (rIS.RealInterfaceEnhancedMod.inv_pos_pos
              (z_aud_req rIS sumf post_aud p) hZ))
          (sumf q)))
      (sum_add (fun s -> kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s)
        (fun s ->
        rIS.RealInterfaceEnhancedMod.mult (q s)
          (rIS.RealInterfaceEnhancedMod.log
            (rIS.RealInterfaceEnhancedMod.inv_pos
              (z_aud_req rIS sumf post_aud p) hZ)
            (rIS.RealInterfaceEnhancedMod.inv_pos_pos
              (z_aud_req rIS sumf post_aud p) hZ))))
      (rIS.RealInterfaceEnhancedMod.req_plus_compat
        (sumf (fun s -> kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s))
        (sumf (fun s -> kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s))
        (sumf (fun s ->
          rIS.RealInterfaceEnhancedMod.mult (q s)
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos
                (z_aud_req rIS sumf post_aud p) hZ)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                (z_aud_req rIS sumf post_aud p) hZ))))
        (rIS.RealInterfaceEnhancedMod.mult
          (rIS.RealInterfaceEnhancedMod.log
            (rIS.RealInterfaceEnhancedMod.inv_pos
              (z_aud_req rIS sumf post_aud p) hZ)
            (rIS.RealInterfaceEnhancedMod.inv_pos_pos
              (z_aud_req rIS sumf post_aud p) hZ))
          (sumf q))
        (rIS.RealInterfaceEnhancedMod.req_refl
          (sumf (fun s ->
            kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s)))
        (rIS.RealInterfaceEnhancedMod.req_trans
          (sumf (fun s ->
            rIS.RealInterfaceEnhancedMod.mult (q s)
              (rIS.RealInterfaceEnhancedMod.log
                (rIS.RealInterfaceEnhancedMod.inv_pos
                  (z_aud_req rIS sumf post_aud p) hZ)
                (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                  (z_aud_req rIS sumf post_aud p) hZ))))
          (sumf (fun s ->
            rIS.RealInterfaceEnhancedMod.mult
              (rIS.RealInterfaceEnhancedMod.log
                (rIS.RealInterfaceEnhancedMod.inv_pos
                  (z_aud_req rIS sumf post_aud p) hZ)
                (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                  (z_aud_req rIS sumf post_aud p) hZ))
              (q s)))
          (rIS.RealInterfaceEnhancedMod.mult
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos
                (z_aud_req rIS sumf post_aud p) hZ)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                (z_aud_req rIS sumf post_aud p) hZ))
            (sumf q))
          (sum_ext (fun s ->
            rIS.RealInterfaceEnhancedMod.mult (q s)
              (rIS.RealInterfaceEnhancedMod.log
                (rIS.RealInterfaceEnhancedMod.inv_pos
                  (z_aud_req rIS sumf post_aud p) hZ)
                (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                  (z_aud_req rIS sumf post_aud p) hZ)))
            (fun s ->
            rIS.RealInterfaceEnhancedMod.mult
              (rIS.RealInterfaceEnhancedMod.log
                (rIS.RealInterfaceEnhancedMod.inv_pos
                  (z_aud_req rIS sumf post_aud p) hZ)
                (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                  (z_aud_req rIS sumf post_aud p) hZ))
              (q s))
            (fun s ->
            rIS.RealInterfaceEnhancedMod.mult_comm (q s)
              (rIS.RealInterfaceEnhancedMod.log
                (rIS.RealInterfaceEnhancedMod.inv_pos
                  (z_aud_req rIS sumf post_aud p) hZ)
                (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                  (z_aud_req rIS sumf post_aud p) hZ))))
          (sum_linear
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos
                (z_aud_req rIS sumf post_aud p) hZ)
              (rIS.RealInterfaceEnhancedMod.inv_pos_pos
                (z_aud_req rIS sumf post_aud p) hZ))
            q))))

(** val req_kl_closed_tail_eval :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
    'a1) -> 'a1) -> ('a1 -> 'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1
    RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.req -> 'a1
    RealInterfaceEnhancedMod.req) -> ('a2 -> bool) -> ('a2 -> 'a1) -> 'a1
    RealInterfaceEnhancedMod.lt -> ('a2 -> 'a1) -> ('a2 -> 'a1
    RealInterfaceEnhancedMod.lt) -> 'a1 RealInterfaceEnhancedMod.req -> 'a1
    RealInterfaceEnhancedMod.req **)

let req_kl_closed_tail_eval rIS sumf log_req_compat post_aud p hZ q _ hqn =
  rIS.RealInterfaceEnhancedMod.req_trans
    (rIS.RealInterfaceEnhancedMod.mult
      (rIS.RealInterfaceEnhancedMod.log
        (rIS.RealInterfaceEnhancedMod.inv_pos (z_aud_req rIS sumf post_aud p)
          hZ)
        (rIS.RealInterfaceEnhancedMod.inv_pos_pos
          (z_aud_req rIS sumf post_aud p) hZ))
      (sumf q))
    (rIS.RealInterfaceEnhancedMod.log
      (rIS.RealInterfaceEnhancedMod.inv_pos (z_aud_req rIS sumf post_aud p)
        hZ)
      (rIS.RealInterfaceEnhancedMod.inv_pos_pos
        (z_aud_req rIS sumf post_aud p) hZ))
    (rIS.RealInterfaceEnhancedMod.opp
      (rIS.RealInterfaceEnhancedMod.log (z_aud_req rIS sumf post_aud p) hZ))
    (rIS.RealInterfaceEnhancedMod.req_trans
      (rIS.RealInterfaceEnhancedMod.mult
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ))
        (sumf q))
      (rIS.RealInterfaceEnhancedMod.mult
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ))
        rIS.RealInterfaceEnhancedMod.one)
      (rIS.RealInterfaceEnhancedMod.log
        (rIS.RealInterfaceEnhancedMod.inv_pos (z_aud_req rIS sumf post_aud p)
          hZ)
        (rIS.RealInterfaceEnhancedMod.inv_pos_pos
          (z_aud_req rIS sumf post_aud p) hZ))
      (rIS.RealInterfaceEnhancedMod.req_mult_compat
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ))
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ))
        (sumf q) rIS.RealInterfaceEnhancedMod.one
        (rIS.RealInterfaceEnhancedMod.req_refl
          (rIS.RealInterfaceEnhancedMod.log
            (rIS.RealInterfaceEnhancedMod.inv_pos
              (z_aud_req rIS sumf post_aud p) hZ)
            (rIS.RealInterfaceEnhancedMod.inv_pos_pos
              (z_aud_req rIS sumf post_aud p) hZ)))
        hqn)
      (rIS.RealInterfaceEnhancedMod.mult_one
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ))))
    (rkl_log_inv_one_inv rIS log_req_compat (z_aud_req rIS sumf post_aud p)
      hZ)

(** val req_projected_distribution_minimizes_kl :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
    'a1) -> 'a1) -> (('a2 -> 'a1) -> ('a2 -> 'a1) -> ('a2 -> 'a1
    RealInterfaceEnhancedMod.req) -> 'a1 RealInterfaceEnhancedMod.req) ->
    (('a2 -> 'a1) -> ('a2 -> 'a1) -> 'a1 RealInterfaceEnhancedMod.req) ->
    ('a1 -> ('a2 -> 'a1) -> 'a1 RealInterfaceEnhancedMod.req) -> ('a1 -> 'a1
    -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.lt ->
    'a1 RealInterfaceEnhancedMod.req -> 'a1 RealInterfaceEnhancedMod.req) ->
    ('a2 -> bool) -> ('a2 -> 'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.lt)
    -> 'a1 RealInterfaceEnhancedMod.lt -> ('a2 -> 'a1) -> ('a2 -> 'a1
    RealInterfaceEnhancedMod.lt) -> 'a1 RealInterfaceEnhancedMod.req -> ('a2
    -> __ -> 'a1 RealInterfaceEnhancedMod.req) -> 'a1
    RealInterfaceEnhancedMod.le -> 'a1 RealInterfaceEnhancedMod.le **)

let req_projected_distribution_minimizes_kl rIS sumf sum_ext sum_add sum_linear log_req_compat post_aud p hp_pos hZ q hq hqn _ hlogZ =
  let hsplit =
    req_kl_closed_sum_split rIS sumf sum_ext sum_add sum_linear post_aud p
      hp_pos hZ q hq
  in
  let htail =
    req_kl_closed_tail_eval rIS sumf log_req_compat post_aud p hZ q hq hqn
  in
  let hge0 =
    rIS.RealInterfaceEnhancedMod.le_id_r rIS.RealInterfaceEnhancedMod.zero
      (rIS.RealInterfaceEnhancedMod.opp
        (rIS.RealInterfaceEnhancedMod.log (z_aud_req rIS sumf post_aud p) hZ))
      (rIS.RealInterfaceEnhancedMod.mult
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ))
        (sumf q))
      (rIS.RealInterfaceEnhancedMod.req_sym
        (rIS.RealInterfaceEnhancedMod.mult
          (rIS.RealInterfaceEnhancedMod.log
            (rIS.RealInterfaceEnhancedMod.inv_pos
              (z_aud_req rIS sumf post_aud p) hZ)
            (rIS.RealInterfaceEnhancedMod.inv_pos_pos
              (z_aud_req rIS sumf post_aud p) hZ))
          (sumf q))
        (rIS.RealInterfaceEnhancedMod.opp
          (rIS.RealInterfaceEnhancedMod.log (z_aud_req rIS sumf post_aud p)
            hZ))
        htail)
      (rIS.RealInterfaceEnhancedMod.le_id_l rIS.RealInterfaceEnhancedMod.zero
        (rIS.RealInterfaceEnhancedMod.opp rIS.RealInterfaceEnhancedMod.zero)
        (rIS.RealInterfaceEnhancedMod.opp
          (rIS.RealInterfaceEnhancedMod.log (z_aud_req rIS sumf post_aud p)
            hZ))
        (rIS.RealInterfaceEnhancedMod.req_sym
          (rIS.RealInterfaceEnhancedMod.opp rIS.RealInterfaceEnhancedMod.zero)
          rIS.RealInterfaceEnhancedMod.zero (rkl_opp_zero rIS))
        (rIS.RealInterfaceEnhancedMod.opp_le_compat
          (rIS.RealInterfaceEnhancedMod.log (z_aud_req rIS sumf post_aud p)
            hZ)
          rIS.RealInterfaceEnhancedMod.zero hlogZ))
  in
  rIS.RealInterfaceEnhancedMod.le_id_r
    (sumf (fun s -> kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s))
    (rIS.RealInterfaceEnhancedMod.plus
      (sumf (fun s -> kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s))
      (rIS.RealInterfaceEnhancedMod.mult
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ))
        (sumf q)))
    (sumf (fun s ->
      rIS.RealInterfaceEnhancedMod.mult (q s)
        (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
          (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s)))))
    (rIS.RealInterfaceEnhancedMod.req_sym
      (sumf (fun s ->
        rIS.RealInterfaceEnhancedMod.mult (q s)
          (req_minus rIS (rIS.RealInterfaceEnhancedMod.log (q s) (hq s))
            (rIS.RealInterfaceEnhancedMod.log (p s) (hp_pos s)))))
      (rIS.RealInterfaceEnhancedMod.plus
        (sumf (fun s -> kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s))
        (rIS.RealInterfaceEnhancedMod.mult
          (rIS.RealInterfaceEnhancedMod.log
            (rIS.RealInterfaceEnhancedMod.inv_pos
              (z_aud_req rIS sumf post_aud p) hZ)
            (rIS.RealInterfaceEnhancedMod.inv_pos_pos
              (z_aud_req rIS sumf post_aud p) hZ))
          (sumf q)))
      hsplit)
    (req_le_plus_nonneg_r rIS
      (sumf (fun s -> kl_proj_closed rIS sumf post_aud p hp_pos hZ q hq s))
      (rIS.RealInterfaceEnhancedMod.mult
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos
            (z_aud_req rIS sumf post_aud p) hZ)
          (rIS.RealInterfaceEnhancedMod.inv_pos_pos
            (z_aud_req rIS sumf post_aud p) hZ))
        (sumf q))
      hge0)

(** val hzlogd_log_le_zero_of_le_one :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> ('a1 ->
    'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.lt
    -> 'a1 RealInterfaceEnhancedMod.le -> 'a1 RealInterfaceEnhancedMod.le) ->
    'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.le
    -> 'a1 RealInterfaceEnhancedMod.le **)

let hzlogd_log_le_zero_of_le_one rIS hmono z hZ hZ1 =
  rIS.RealInterfaceEnhancedMod.le_id_r
    (rIS.RealInterfaceEnhancedMod.log z hZ)
    (rIS.RealInterfaceEnhancedMod.log rIS.RealInterfaceEnhancedMod.one
      rIS.RealInterfaceEnhancedMod.one_pos)
    rIS.RealInterfaceEnhancedMod.zero
    (rIS.RealInterfaceEnhancedMod.log_one
      rIS.RealInterfaceEnhancedMod.one_pos)
    (hmono z rIS.RealInterfaceEnhancedMod.one hZ
      rIS.RealInterfaceEnhancedMod.one_pos hZ1)

(** val hzlogd_proj_min_kl_hlogzfree :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> (('a2 ->
    'a1) -> 'a1) -> (('a2 -> 'a1) -> ('a2 -> 'a1) -> ('a2 -> 'a1
    RealInterfaceEnhancedMod.req) -> 'a1 RealInterfaceEnhancedMod.req) ->
    (('a2 -> 'a1) -> ('a2 -> 'a1) -> 'a1 RealInterfaceEnhancedMod.req) ->
    ('a1 -> ('a2 -> 'a1) -> 'a1 RealInterfaceEnhancedMod.req) -> (('a2 ->
    'a1) -> ('a2 -> 'a1) -> ('a2 -> 'a1 RealInterfaceEnhancedMod.le) -> 'a1
    RealInterfaceEnhancedMod.le) -> ('a1 -> 'a1 -> 'a1
    RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1
    RealInterfaceEnhancedMod.req -> 'a1 RealInterfaceEnhancedMod.req) -> ('a2
    -> bool) -> ('a2 -> 'a1) -> 'a1 RealInterfaceEnhancedMod.req -> ('a2 ->
    'a1 RealInterfaceEnhancedMod.lt) -> 'a1 RealInterfaceEnhancedMod.lt ->
    ('a1 -> 'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1
    RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.le -> 'a1
    RealInterfaceEnhancedMod.le) -> ('a2 -> 'a1) -> ('a2 -> 'a1
    RealInterfaceEnhancedMod.lt) -> 'a1 RealInterfaceEnhancedMod.req -> ('a2
    -> __ -> 'a1 RealInterfaceEnhancedMod.req) -> 'a1
    RealInterfaceEnhancedMod.le **)

let hzlogd_proj_min_kl_hlogzfree rIS sumf sum_ext sum_add sum_linear sum_le log_req_compat post_aud p hp_norm hp_pos hZ hmono q hq hqn hqz =
  req_projected_distribution_minimizes_kl rIS sumf sum_ext sum_add sum_linear
    log_req_compat post_aud p hp_pos hZ q hq hqn hqz
    (hzlogd_log_le_zero_of_le_one rIS hmono (z_aud_req rIS sumf post_aud p)
      hZ
      (rIS.RealInterfaceEnhancedMod.le_id_r (z_aud_req rIS sumf post_aud p)
        (sumf p) rIS.RealInterfaceEnhancedMod.one hp_norm
        (req_Z_aud_le_one rIS sumf sum_le post_aud p hp_pos)))
