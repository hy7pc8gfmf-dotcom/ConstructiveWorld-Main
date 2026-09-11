
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

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat =
 struct
  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')
 end

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True
 end

type q = { qnum : z; qden : positive }

(** val qcompare : q -> q -> comparison **)

let qcompare p q0 =
  Z.compare (Z.mul p.qnum (Zpos q0.qden)) (Z.mul q0.qnum (Zpos p.qden))

(** val qle_bool : q -> q -> bool **)

let qle_bool x y =
  Z.leb (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

type natLe = bool id

(** val qlt_bool : q -> q -> bool **)

let qlt_bool x y =
  match qcompare x y with
  | Lt -> True
  | _ -> False

type qltT = bool id

type qleT' = bool id

(** val q_pow : q -> nat -> q **)

let rec q_pow x = function
| O -> { qnum = (Zpos XH); qden = XH }
| S m -> qmult x (q_pow x m)

module Constitution =
 struct
  type claim_decl = { cl_c0 : q; cl_eps : q; cl_kappa : q; cl_N : nat;
                      cl_id : nat }

  (** val cl_c0 : claim_decl -> q **)

  let cl_c0 c =
    c.cl_c0

  (** val cl_eps : claim_decl -> q **)

  let cl_eps c =
    c.cl_eps

  (** val cl_kappa : claim_decl -> q **)

  let cl_kappa c =
    c.cl_kappa

  (** val cl_N : claim_decl -> nat **)

  let cl_N c =
    c.cl_N

  (** val cl_id : claim_decl -> nat **)

  let cl_id c =
    c.cl_id

  type claim_reject =
  | Coq_rj_kappa
  | Coq_rj_budget
  | Coq_rj_data
  | Coq_rj_reach

  type claim_pass =
    ((qleT', qltT) and0, (natLe, ((qleT', qltT) and0, qltT) and0) and0) and0

  (** val kap_low_dec :
      claim_decl -> (qleT', (bool id, claim_reject) and0) or0 **)

  let kap_low_dec cl =
    match qle_bool { qnum = Z0; qden = XH } cl.cl_kappa with
    | True -> Inl Id_refl
    | False -> Inr (Pair (Id_refl, Coq_rj_kappa))

  (** val kap_high_dec :
      claim_decl -> (qltT, (bool id, claim_reject) and0) or0 **)

  let kap_high_dec cl =
    match qlt_bool cl.cl_kappa { qnum = (Zpos XH); qden = XH } with
    | True -> Inl Id_refl
    | False -> Inr (Pair (Id_refl, Coq_rj_kappa))

  (** val bud_dec :
      claim_decl -> (natLe, (bool id, claim_reject) and0) or0 **)

  let bud_dec cl =
    match Nat.leb (S O) cl.cl_N with
    | True -> Inl Id_refl
    | False -> Inr (Pair (Id_refl, Coq_rj_budget))

  (** val dat_c0_dec :
      claim_decl -> (qleT', (bool id, claim_reject) and0) or0 **)

  let dat_c0_dec cl =
    match qle_bool { qnum = Z0; qden = XH } cl.cl_c0 with
    | True -> Inl Id_refl
    | False -> Inr (Pair (Id_refl, Coq_rj_data))

  (** val dat_eps_dec :
      claim_decl -> (qltT, (bool id, claim_reject) and0) or0 **)

  let dat_eps_dec cl =
    match qlt_bool { qnum = Z0; qden = XH } cl.cl_eps with
    | True -> Inl Id_refl
    | False -> Inr (Pair (Id_refl, Coq_rj_data))

  (** val reach_dec :
      claim_decl -> (qltT, (bool id, claim_reject) and0) or0 **)

  let reach_dec cl =
    match qlt_bool
            (qmult cl.cl_c0
              (q_pow (qminus { qnum = (Zpos XH); qden = XH } cl.cl_kappa)
                cl.cl_N))
            cl.cl_eps with
    | True -> Inl Id_refl
    | False -> Inr (Pair (Id_refl, Coq_rj_reach))

  (** val check_claim : claim_decl -> (claim_pass, claim_reject) or0 **)

  let check_claim cl =
    match kap_low_dec cl with
    | Inl hk0 ->
      (match kap_high_dec cl with
       | Inl hk1 ->
         (match bud_dec cl with
          | Inl hb ->
            (match dat_c0_dec cl with
             | Inl hc0 ->
               (match dat_eps_dec cl with
                | Inl he ->
                  (match reach_dec cl with
                   | Inl hr ->
                     Inl (Pair ((Pair (hk0, hk1)), (Pair (hb, (Pair ((Pair
                       (hc0, he)), hr))))))
                   | Inr a -> let Pair (_, r) = a in Inr r)
                | Inr a -> let Pair (_, r) = a in Inr r)
             | Inr a -> let Pair (_, r) = a in Inr r)
          | Inr a -> let Pair (_, r) = a in Inr r)
       | Inr a -> let Pair (_, r) = a in Inr r)
    | Inr a -> let Pair (_, r) = a in Inr r

  type claim_verdict =
  | Coq_v_pass
  | Coq_v_reject of claim_reject

  (** val check_report : claim_decl -> claim_verdict **)

  let check_report cl =
    match check_claim cl with
    | Inl _ -> Coq_v_pass
    | Inr r -> Coq_v_reject r

  (** val chain_claim : claim_decl -> claim_decl -> claim_decl **)

  let chain_claim a b =
    { cl_c0 = a.cl_c0; cl_eps = b.cl_eps; cl_kappa =
      (qminus (qplus a.cl_kappa b.cl_kappa) (qmult a.cl_kappa b.cl_kappa));
      cl_N = (add a.cl_N b.cl_N); cl_id = a.cl_id }
 end
