
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

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
  | O -> m
  | S n' -> (match m with
             | O -> n
             | S m' -> S (max n' m'))

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

  (** val max : nat -> nat -> nat **)

  let rec max n m =
    match n with
    | O -> m
    | S n' -> (match m with
               | O -> n
               | S m' -> S (max n' m'))
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

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x
 end

type q = { qnum : z; qden : positive }

(** val qcompare : q -> q -> comparison **)

let qcompare p q0 =
  Z.compare (Z.mul p.qnum (Zpos q0.qden)) (Z.mul q0.qnum (Zpos p.qden))

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

(** val qinv : q -> q **)

let qinv x =
  match x.qnum with
  | Z0 -> { qnum = Z0; qden = XH }
  | Zpos p -> { qnum = (Zpos x.qden); qden = p }
  | Zneg p -> { qnum = (Zneg x.qden); qden = p }

(** val qdiv : q -> q -> q **)

let qdiv x y =
  qmult x (qinv y)

(** val qabs : q -> q **)

let qabs x =
  let { qnum = n; qden = d } = x in { qnum = (Z.abs n); qden = d }

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

type 'a not = 'a -> empty_set

(** val id_sym : 'a1 -> 'a1 -> 'a1 id -> 'a1 id **)

let id_sym _ _ _ =
  Id_refl

type 'a inT =
| InT_here of 'a list
| InT_next of 'a * 'a list * 'a inT

type natLe = bool id

(** val natLe_lift : nat -> nat -> natLe **)

let natLe_lift n m =
  let b = Nat.leb n m in
  (match b with
   | True -> Id_refl
   | False -> assert false (* absurd case *))

type qseq = nat -> q

type qltT = bool id

(** val qlt_to_QltT : q -> q -> qltT **)

let qlt_to_QltT x y =
  let c = qcompare x y in
  (match c with
   | Lt -> Id_refl
   | _ -> assert false (* absurd case *))

type qleT' = bool id

(** val qle_to_QleT' : q -> q -> qleT' **)

let qle_to_QleT' x y =
  let c = Z.compare (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))
  in
  (match c with
   | Gt -> assert false (* absurd case *)
   | _ -> Id_refl)

(** val qltT_0_2 : qltT **)

let qltT_0_2 =
  Id_refl

(** val qleT'_trans : q -> q -> q -> qleT' -> qleT' -> qleT' **)

let qleT'_trans x _ z0 _ _ =
  qle_to_QleT' x z0

(** val qleT'_ltT_ltT : q -> q -> q -> qleT' -> qltT -> qltT **)

let qleT'_ltT_ltT x _ z0 _ _ =
  qlt_to_QltT x z0

(** val qltT_leT'_ltT : q -> q -> q -> qltT -> qleT' -> qltT **)

let qltT_leT'_ltT x _ z0 _ _ =
  qlt_to_QltT x z0

(** val qltT_plus_ltT : q -> q -> q -> q -> qltT -> qltT -> qltT **)

let qltT_plus_ltT a b c d _ _ =
  qlt_to_QltT (qplus a c) (qplus b d)

(** val qleT'_mult_ltT_compat :
    q -> q -> q -> q -> qltT -> qleT' -> qleT' -> qltT -> qltT **)

let qleT'_mult_ltT_compat a b c d _ _ _ _ =
  qlt_to_QltT (qmult a c) (qmult b d)

(** val qmult_ltT_0_compat : q -> q -> qltT -> qltT -> qltT **)

let qmult_ltT_0_compat a b _ _ =
  qlt_to_QltT { qnum = Z0; qden = XH } (qmult a b)

(** val qeq_leT' : q -> q -> qleT' **)

let qeq_leT' =
  qle_to_QleT'

(** val qabs_nonnegT : q -> qleT' **)

let qabs_nonnegT x =
  qle_to_QleT' { qnum = Z0; qden = XH } (qabs x)

(** val qltT_div_pos : q -> q -> qltT -> qltT -> qltT **)

let qltT_div_pos x y _ _ =
  qlt_to_QltT { qnum = Z0; qden = XH } (qdiv x y)

(** val qltT_eq_compat_l : q -> q -> q -> qltT -> qltT **)

let qltT_eq_compat_l _ a' b _ =
  qlt_to_QltT a' b

type cauchy = q -> qltT -> (nat, nat -> nat -> natLe -> natLe -> qltT) sigT

type real = (qseq, cauchy) sigT

type real_eq = q -> qltT -> (nat, nat -> natLe -> qltT) sigT

(** val real_plus : real -> real -> real **)

let real_plus x y =
  let ExistT (x0, c) = x in
  let ExistT (x1, c0) = y in
  ExistT ((fun n -> qplus (x0 n) (x1 n)), (fun eps _ ->
  let s =
    c (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x2, _) = s in
  let s0 =
    c0 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x3, _) = s0 in
  ExistT ((max x2 x3), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (qplus (x0 m) (x1 m)) (qplus (x0 n) (x1 n)))) eps))))

(** val real_opp : real -> real **)

let real_opp = function
| ExistT (x0, c) ->
  ExistT ((fun n -> qopp (x0 n)), (fun eps heps ->
    let s = c eps heps in
    let ExistT (x1, _) = s in
    ExistT (x1, (fun m n _ _ ->
    qlt_to_QltT (qabs (qminus (qopp (x0 m)) (qopp (x0 n)))) eps))))

(** val real_zero : real **)

let real_zero =
  ExistT ((fun _ -> { qnum = Z0; qden = XH }), (fun _ heps -> ExistT (O,
    (fun _ _ _ _ -> heps))))

type real_lt = (q, (qltT, (nat, nat -> natLe -> qltT) sigT) and0) sigT

type real_le = (real_lt, real_eq) or0

(** val real_lt_trans :
    real -> real -> real -> real_lt -> real_lt -> real_lt **)

let real_lt_trans x _ z0 hxy hyz =
  let ExistT (x0, a) = hxy in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let ExistT (x2, a0) = hyz in
  let Pair (_, s0) = a0 in
  let ExistT (x3, _) = s0 in
  ExistT ((qplus x0 x2), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qplus x0 x2)), (ExistT
  ((max x1 x3), (fun n _ ->
  qlt_to_QltT (qplus x0 x2) (qminus (projT1 z0 n) (projT1 x n))))))))

(** val sum_abs_prefix : qseq -> nat -> q **)

let rec sum_abs_prefix u = function
| O -> { qnum = Z0; qden = XH }
| S n' -> qplus (sum_abs_prefix u n') (qabs (u n'))

(** val cauchy_bounded : qseq -> cauchy -> q **)

let cauchy_bounded u hu =
  let s = hu { qnum = (Zpos XH); qden = XH } Id_refl in
  let ExistT (x, _) = s in
  qplus (qplus (sum_abs_prefix u x) (qabs (u x))) { qnum = (Zpos XH); qden =
    XH }

(** val real_norm_bounded : real -> (q, (qltT, nat -> qleT') and0) sigT **)

let real_norm_bounded = function
| ExistT (x0, c) ->
  let s = cauchy_bounded x0 c in
  ExistT ((qplus (qabs s) { qnum = (Zpos XH); qden = XH }), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qplus (qabs s) { qnum = (Zpos XH); qden = XH })),
  (fun k ->
  qle_to_QleT' (qabs (projT1 (ExistT (x0, c)) k))
    (qplus (qabs s) { qnum = (Zpos XH); qden = XH })))))

(** val real_mult : real -> real -> real **)

let real_mult x y =
  let ExistT (x0, c) = x in
  let ExistT (x1, c0) = y in
  ExistT ((fun n -> qmult (x0 n) (x1 n)), (fun eps _ ->
  let s = real_norm_bounded (ExistT (x0, c)) in
  let ExistT (x2, a) = s in
  let Pair (_, q0) = a in
  let s0 = real_norm_bounded (ExistT (x1, c0)) in
  let ExistT (x3, a0) = s0 in
  let Pair (_, q1) = a0 in
  let mupos = qplus { qnum = (Zpos XH); qden = XH } (qabs x2) in
  let mvpos = qplus { qnum = (Zpos XH); qden = XH } (qabs x3) in
  let s1 =
    c (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)))
  in
  let ExistT (x4, q2) = s1 in
  let s2 =
    c0 (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
  in
  let ExistT (x5, q3) = s2 in
  ExistT ((max x4 x5), (fun m n _ _ ->
  let hN1' = q2 m n in
  let hN2' = q3 m n in
  let htriT =
    qle_to_QleT' (qabs (qminus (qmult (x0 m) (x1 m)) (qmult (x0 n) (x1 n))))
      (qplus (qmult (qabs (x0 m)) (qabs (qminus (x1 m) (x1 n))))
        (qmult (qabs (x1 n)) (qabs (qminus (x0 m) (x0 n)))))
  in
  let hMu_boundT =
    qleT'_trans (qabs (x0 m)) x2 mupos (q0 m) (qle_to_QleT' x2 mupos)
  in
  let hMv_boundT =
    qleT'_trans (qabs (x1 n)) x3 mvpos (q1 n) (qle_to_QleT' x3 mvpos)
  in
  let ht1T =
    qleT'_mult_ltT_compat (qabs (x0 m)) mupos (qabs (qminus (x1 m) (x1 n)))
      (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos))
      (qlt_to_QltT { qnum = Z0; qden = XH } mupos)
      (qabs_nonnegT (qminus (x1 m) (x1 n))) hMu_boundT
      (hN2' (natLe_lift x5 m) (natLe_lift x5 n))
  in
  let ht2T =
    qleT'_mult_ltT_compat (qabs (x1 n)) mvpos (qabs (qminus (x0 m) (x0 n)))
      (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))
      (qlt_to_QltT { qnum = Z0; qden = XH } mvpos)
      (qabs_nonnegT (qminus (x0 m) (x0 n))) hMv_boundT
      (hN1' (natLe_lift x4 m) (natLe_lift x4 n))
  in
  qleT'_ltT_ltT (qabs (qminus (qmult (x0 m) (x1 m)) (qmult (x0 n) (x1 n))))
    (qplus (qmult (qabs (x0 m)) (qabs (qminus (x1 m) (x1 n))))
      (qmult (qabs (x1 n)) (qabs (qminus (x0 m) (x0 n)))))
    eps htriT
    (qltT_leT'_ltT
      (qplus (qmult (qabs (x0 m)) (qabs (qminus (x1 m) (x1 n))))
        (qmult (qabs (x1 n)) (qabs (qminus (x0 m) (x0 n)))))
      (qplus
        (qmult mupos
          (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
        (qmult mvpos
          (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))))
      eps
      (qltT_plus_ltT (qmult (qabs (x0 m)) (qabs (qminus (x1 m) (x1 n))))
        (qmult mupos
          (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
        (qmult (qabs (x1 n)) (qabs (qminus (x0 m) (x0 n))))
        (qmult mvpos
          (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)))
        ht1T ht2T)
      (qeq_leT'
        (qplus
          (qmult mupos
            (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
          (qmult mvpos
            (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))))
        eps))))))

(** val real_eq_refl : real -> real_eq **)

let real_eq_refl _ _ _ =
  ExistT (O, (fun _ _ -> Id_refl))

(** val real_eq_sym : real -> real -> real_eq -> real_eq **)

let real_eq_sym _ _ hxy =
  hxy

(** val real_eq_trans :
    real -> real -> real -> real_eq -> real_eq -> real_eq **)

let real_eq_trans x _ z0 hxy hyz eps _ =
  let s =
    hxy (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x0, _) = s in
  let s0 =
    hyz (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x1, _) = s0 in
  ExistT ((max x0 x1), (fun n _ ->
  qlt_to_QltT (qabs (qminus (projT1 x n) (projT1 z0 n))) eps))

(** val real_one : real **)

let real_one =
  ExistT ((fun _ -> { qnum = (Zpos XH); qden = XH }), (fun _ _ -> ExistT (O,
    (fun _ _ _ _ -> Id_refl))))

(** val real_eq_of_zero_diff : real -> real -> real_eq **)

let real_eq_of_zero_diff _ _ _ _ =
  ExistT (O, (fun _ _ -> Id_refl))

(** val real_plus_comm : real -> real -> real_eq **)

let real_plus_comm x y =
  real_eq_of_zero_diff (real_plus x y) (real_plus y x)

(** val real_plus_assoc : real -> real -> real -> real_eq **)

let real_plus_assoc x y z0 =
  real_eq_of_zero_diff (real_plus x (real_plus y z0))
    (real_plus (real_plus x y) z0)

(** val real_plus_zero : real -> real_eq **)

let real_plus_zero x =
  real_eq_of_zero_diff (real_plus x real_zero) x

(** val real_plus_opp : real -> real_eq **)

let real_plus_opp x =
  real_eq_of_zero_diff (real_plus x (real_opp x)) real_zero

(** val real_mult_comm : real -> real -> real_eq **)

let real_mult_comm x y =
  real_eq_of_zero_diff (real_mult x y) (real_mult y x)

(** val real_mult_assoc : real -> real -> real -> real_eq **)

let real_mult_assoc x y z0 =
  real_eq_of_zero_diff (real_mult x (real_mult y z0))
    (real_mult (real_mult x y) z0)

(** val real_mult_one : real -> real_eq **)

let real_mult_one x =
  real_eq_of_zero_diff (real_mult x real_one) x

(** val real_mult_zero : real -> real_eq **)

let real_mult_zero x =
  real_eq_of_zero_diff (real_mult x real_zero) real_zero

(** val real_distrib : real -> real -> real -> real_eq **)

let real_distrib x y z0 =
  real_eq_of_zero_diff (real_mult x (real_plus y z0))
    (real_plus (real_mult x y) (real_mult x z0))

(** val real_le_refl : real -> real_le **)

let real_le_refl x =
  Inr (real_eq_refl x)

(** val real_lt_eq_lt :
    real -> real -> real -> real_lt -> real_eq -> real_lt **)

let real_lt_eq_lt x _ z0 hlt hyz =
  let ExistT (x0, a) = hlt in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let s0 =
    hyz (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x2, _) = s0 in
  ExistT ((qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })),
  (ExistT ((max x1 x2), (fun n _ ->
  qlt_to_QltT (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })
    (qminus (projT1 z0 n) (projT1 x n))))))))

(** val real_eq_lt_lt :
    real -> real -> real -> real_eq -> real_lt -> real_lt **)

let real_eq_lt_lt x _ z0 hxy = function
| ExistT (x0, a) ->
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let s0 =
    hxy (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x2, _) = s0 in
  ExistT ((qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })),
  (ExistT ((max x1 x2), (fun n _ ->
  qlt_to_QltT (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })
    (qminus (projT1 z0 n) (projT1 x n))))))))

(** val real_le_trans :
    real -> real -> real -> real_le -> real_le -> real_le **)

let real_le_trans x y z0 hxy hyz =
  match hxy with
  | Inl r ->
    (match hyz with
     | Inl r0 -> Inl (real_lt_trans x y z0 r r0)
     | Inr r0 -> Inl (real_lt_eq_lt x y z0 r r0))
  | Inr r ->
    (match hyz with
     | Inl r0 -> Inl (real_eq_lt_lt x y z0 r r0)
     | Inr r0 -> Inr (real_eq_trans x y z0 r r0))

(** val real_lt_le_trans :
    real -> real -> real -> real_lt -> real_le -> real_lt **)

let real_lt_le_trans x y z0 hlt = function
| Inl r -> real_lt_trans x y z0 hlt r
| Inr r -> real_lt_eq_lt x y z0 hlt r

(** val real_lt_le_iff : real -> real -> (real_lt, real id) or0 -> real_le **)

let real_lt_le_iff x _ = function
| Inl r -> Inl r
| Inr _ -> Inr (real_eq_refl x)

(** val real_lt_plus_compat :
    real -> real -> real -> real -> real_lt -> real_lt -> real_lt **)

let real_lt_plus_compat a b c d hab hcd =
  let ExistT (x, a0) = hab in
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  let ExistT (x1, a1) = hcd in
  let Pair (_, s0) = a1 in
  let ExistT (x2, _) = s0 in
  ExistT ((qplus x x1), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qplus x x1)), (ExistT ((max x0 x2),
  (fun n _ ->
  qlt_to_QltT (qplus x x1)
    (qminus (projT1 (real_plus b d) n) (projT1 (real_plus a c) n))))))))

(** val real_abs : real -> real **)

let real_abs = function
| ExistT (x0, c) ->
  ExistT ((fun n -> qabs (x0 n)), (fun eps heps ->
    let s = c eps heps in
    let ExistT (x1, _) = s in
    ExistT (x1, (fun m n _ _ ->
    qlt_to_QltT (qabs (qminus (qabs (x0 m)) (qabs (x0 n)))) eps))))

(** val real_abs_opp : real -> real_eq **)

let real_abs_opp x eps _ =
  let ExistT (x0, c) = x in
  ExistT (O, (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus
        (projT1 (ExistT ((fun n0 -> qabs (qopp (x0 n0))), (fun eps0 heps ->
          let ExistT (x1, _) = c eps0 heps in
          ExistT (x1, (fun m n0 _ _ ->
          qlt_to_QltT
            (qabs (qminus (qabs (qopp (x0 m))) (qabs (qopp (x0 n0))))) eps0)))))
          n)
        (projT1 (ExistT ((fun n0 -> qabs (x0 n0)), (fun eps0 heps ->
          let ExistT (x1, _) = c eps0 heps in
          ExistT (x1, (fun m n0 _ _ ->
          qlt_to_QltT (qabs (qminus (qabs (x0 m)) (qabs (x0 n0)))) eps0)))))
          n)))
    eps))

(** val real_inv_pos : real -> real_lt -> real **)

let real_inv_pos x hx =
  let ExistT (x0, c) = x in
  let ExistT (x1, a) = hx in
  let Pair (_, s) = a in
  let ExistT (x2, _) = s in
  ExistT ((fun n ->
  match Nat.leb x2 n with
  | True -> qinv (x0 n)
  | False -> qinv (x0 x2)), (fun eps _ ->
  let delta = qmult eps (qmult x1 x1) in
  let hdlt = qlt_to_QltT { qnum = Z0; qden = XH } (qmult eps (qmult x1 x1)) in
  let s0 = c delta hdlt in
  let ExistT (x3, _) = s0 in
  ExistT ((Nat.max x2 x3), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (qinv (x0 m)) (qinv (x0 n)))) eps))))

(** val real_inv_pos_correct : real -> real_lt -> real_eq **)

let real_inv_pos_correct x hx eps _ =
  let ExistT (x0, _) = x in
  let ExistT (_, a) = hx in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  ExistT (x1, (fun n _ ->
  let b = Nat.leb x1 n in
  (match b with
   | True ->
     qlt_to_QltT
       (qabs
         (qminus (qmult (x0 n) (qinv (x0 n))) { qnum = (Zpos XH); qden = XH }))
       eps
   | False -> assert false (* absurd case *))))

(** val real_inv_pos_pos : real -> real_lt -> real_lt **)

let real_inv_pos_pos x hx =
  let ExistT (x0, c) = x in
  let ExistT (_, a) = hx in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let s0 = real_norm_bounded (ExistT (x0, c)) in
  let ExistT (x2, _) = s0 in
  ExistT ((qinv (qplus x2 { qnum = (Zpos XH); qden = XH })), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qinv (qplus x2 { qnum = (Zpos XH); qden = XH }))),
  (ExistT (x1, (fun n _ ->
  let b = Nat.leb x1 n in
  (match b with
   | True ->
     qlt_to_QltT (qinv (qplus x2 { qnum = (Zpos XH); qden = XH }))
       (qminus (qinv (x0 n)) { qnum = Z0; qden = XH })
   | False -> assert false (* absurd case *))))))))

module RealSetoid =
 struct
  (** val real_eq_le : real -> real -> real_eq -> real_le **)

  let real_eq_le _ _ hab =
    Inr hab

  (** val real_lt_le_iff_req :
      real -> real -> (real_lt, real_eq) or0 -> real_le **)

  let real_lt_le_iff_req a b = function
  | Inl r -> real_lt_le_iff a b (Inl r)
  | Inr r -> real_eq_le a b r

  (** val real_eq_plus_compat :
      real -> real -> real -> real -> real_eq -> real_eq -> real_eq **)

  let real_eq_plus_compat a b c d hac hbd eps _ =
    let hhalf0 =
      qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
    in
    let s = hac (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf0 in
    let ExistT (x, _) = s in
    let s0 = hbd (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf0 in
    let ExistT (x0, _) = s0 in
    ExistT ((Nat.max x x0), (fun k _ ->
    qlt_to_QltT
      (qabs (qminus (projT1 (real_plus a b) k) (projT1 (real_plus c d) k)))
      eps))

  (** val real_eq_opp_compat : real -> real -> real_eq -> real_eq **)

  let real_eq_opp_compat a b hab eps heps =
    let s = hab eps heps in
    let ExistT (x, _) = s in
    ExistT (x, (fun k _ ->
    qlt_to_QltT
      (qabs (qminus (projT1 (real_opp a) k) (projT1 (real_opp b) k))) eps))

  (** val real_eq_mult_compat :
      real -> real -> real -> real -> real_eq -> real_eq -> real_eq **)

  let real_eq_mult_compat a b c d hac hbd eps heps =
    let s = real_norm_bounded a in
    let ExistT (x, a0) = s in
    let Pair (_, q0) = a0 in
    let s0 = real_norm_bounded d in
    let ExistT (x0, a1) = s0 in
    let Pair (_, q1) = a1 in
    let mupos = qplus { qnum = (Zpos XH); qden = XH } (qabs x) in
    let mvpos = qplus { qnum = (Zpos XH); qden = XH } (qabs x0) in
    let muposT = qlt_to_QltT { qnum = Z0; qden = XH } mupos in
    let mvposT = qlt_to_QltT { qnum = Z0; qden = XH } mvpos in
    let hepsB =
      qltT_div_pos eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)
        heps
        (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } mupos
          qltT_0_2 muposT)
    in
    let hepsA =
      qltT_div_pos eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)
        heps
        (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } mvpos
          qltT_0_2 mvposT)
    in
    let s1 =
      hbd (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)) hepsB
    in
    let ExistT (x1, q2) = s1 in
    let s2 =
      hac (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)) hepsA
    in
    let ExistT (x2, q3) = s2 in
    ExistT ((Nat.max x1 x2), (fun k _ ->
    qltT_eq_compat_l
      (qabs
        (qminus (qmult (projT1 a k) (projT1 b k))
          (qmult (projT1 c k) (projT1 d k))))
      (qabs (qminus (projT1 (real_mult a b) k) (projT1 (real_mult c d) k)))
      eps
      (let hbdT =
         qle_to_QleT'
           (qabs
             (qminus (qmult (projT1 a k) (projT1 b k))
               (qmult (projT1 c k) (projT1 d k))))
           (qplus
             (qmult (qabs (projT1 a k))
               (qabs (qminus (projT1 b k) (projT1 d k))))
             (qmult (qabs (projT1 d k))
               (qabs (qminus (projT1 a k) (projT1 c k)))))
       in
       let hMa_boundT =
         qleT'_trans (qabs (projT1 a k)) x mupos (q0 k) (qle_to_QleT' x mupos)
       in
       let hMd_boundT =
         qleT'_trans (qabs (projT1 d k)) x0 mvpos (q1 k)
           (qle_to_QleT' x0 mvpos)
       in
       let ht1T =
         qleT'_mult_ltT_compat (qabs (projT1 a k)) mupos
           (qabs (qminus (projT1 b k) (projT1 d k)))
           (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos))
           muposT (qabs_nonnegT (qminus (projT1 b k) (projT1 d k)))
           hMa_boundT (q2 k (natLe_lift x1 k))
       in
       let ht2T =
         qleT'_mult_ltT_compat (qabs (projT1 d k)) mvpos
           (qabs (qminus (projT1 a k) (projT1 c k)))
           (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))
           mvposT (qabs_nonnegT (qminus (projT1 a k) (projT1 c k)))
           hMd_boundT (q3 k (natLe_lift x2 k))
       in
       let ht1bT =
         qeq_leT'
           (qmult mupos
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
       in
       let ht2bT =
         qeq_leT'
           (qmult mvpos
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)))
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
       in
       let ht1T' =
         qltT_leT'_ltT
           (qmult (qabs (projT1 a k))
             (qabs (qminus (projT1 b k) (projT1 d k))))
           (qmult mupos
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht1T ht1bT
       in
       let ht2T' =
         qltT_leT'_ltT
           (qmult (qabs (projT1 d k))
             (qabs (qminus (projT1 a k) (projT1 c k))))
           (qmult mvpos
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)))
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht2T ht2bT
       in
       qleT'_ltT_ltT
         (qabs
           (qminus (qmult (projT1 a k) (projT1 b k))
             (qmult (projT1 c k) (projT1 d k))))
         (qplus
           (qmult (qabs (projT1 a k))
             (qabs (qminus (projT1 b k) (projT1 d k))))
           (qmult (qabs (projT1 d k))
             (qabs (qminus (projT1 a k) (projT1 c k)))))
         eps hbdT
         (qltT_leT'_ltT
           (qplus
             (qmult (qabs (projT1 a k))
               (qabs (qminus (projT1 b k) (projT1 d k))))
             (qmult (qabs (projT1 d k))
               (qabs (qminus (projT1 a k) (projT1 c k)))))
           (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
           eps
           (qltT_plus_ltT
             (qmult (qabs (projT1 a k))
               (qabs (qminus (projT1 b k) (projT1 d k))))
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
             (qmult (qabs (projT1 d k))
               (qabs (qminus (projT1 a k) (projT1 c k))))
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht1T' ht2T')
           (qeq_leT'
             (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
             eps)))))

  (** val real_lt_compat :
      real -> real -> real -> real -> real_eq -> real_eq -> real_lt -> real_lt **)

  let real_lt_compat x1 x2 y1 y2 hx hy hlt =
    real_lt_eq_lt x2 y1 y2
      (real_eq_lt_lt x2 x1 y1 (real_eq_sym x1 x2 hx) hlt) hy

  (** val real_le_compat :
      real -> real -> real -> real -> real_eq -> real_eq -> real_le -> real_le **)

  let real_le_compat x1 x2 y1 y2 hx hy = function
  | Inl r -> Inl (real_lt_compat x1 x2 y1 y2 hx hy r)
  | Inr r ->
    Inr
      (real_eq_trans x2 y1 y2
        (real_eq_trans x2 x1 y1 (real_eq_sym x1 x2 hx) r) hy)

  (** val real_lt_id_l :
      real -> real -> real -> real_eq -> real_lt -> real_lt **)

  let real_lt_id_l =
    real_eq_lt_lt

  (** val real_lt_id_r :
      real -> real -> real -> real_eq -> real_lt -> real_lt **)

  let real_lt_id_r a b c hbc hab =
    real_lt_eq_lt a b c hab hbc

  (** val real_le_id_l :
      real -> real -> real -> real_eq -> real_le -> real_le **)

  let real_le_id_l a b c hab hbc =
    real_le_compat b a c c (real_eq_sym a b hab) (real_eq_refl c) hbc

  (** val real_le_id_r :
      real -> real -> real -> real_eq -> real_le -> real_le **)

  let real_le_id_r a b c hbc hab =
    real_le_compat a a b c (real_eq_refl a) hbc hab
 end

(** val real_lt_opp_plus : real -> real -> real_lt -> real_lt **)

let real_lt_opp_plus x y = function
| ExistT (x0, a) ->
  let Pair (q0, s) = a in
  let ExistT (x1, _) = s in
  ExistT (x0, (Pair (q0, (ExistT (x1, (fun n _ ->
  qlt_to_QltT x0
    (qminus (projT1 (real_plus y (real_opp x)) n) (projT1 real_zero n))))))))

(** val real_mult_pos_compat :
    real -> real -> real_lt -> real_lt -> real_lt **)

let real_mult_pos_compat a b ha hb =
  let ExistT (x, a0) = ha in
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  let ExistT (x1, a1) = hb in
  let Pair (_, s0) = a1 in
  let ExistT (x2, _) = s0 in
  ExistT ((qmult x x1), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qmult x x1)), (ExistT
  ((Nat.max x0 x2), (fun n _ ->
  qlt_to_QltT (qmult x x1)
    (qminus (projT1 (real_mult a b) n) (projT1 real_zero n))))))))

(** val real_mult_lt_compat :
    real -> real -> real -> real_lt -> real_lt -> real_lt **)

let real_mult_lt_compat a b c hab hc =
  let ExistT (x, a0) = hab in
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  let ExistT (x1, a1) = hc in
  let Pair (_, s0) = a1 in
  let ExistT (x2, _) = s0 in
  ExistT ((qmult x x1), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qmult x x1)), (ExistT
  ((Nat.max x0 x2), (fun n _ ->
  qlt_to_QltT (qmult x x1)
    (qminus (projT1 (real_mult b c) n) (projT1 (real_mult a c) n))))))))

(** val real_mult_lt_compat_l :
    real -> real -> real -> real_lt -> real_lt -> real_lt **)

let real_mult_lt_compat_l a b c hab hc =
  real_eq_lt_lt (real_mult c a) (real_mult a c) (real_mult c b)
    (real_mult_comm c a)
    (real_lt_eq_lt (real_mult a c) (real_mult b c) (real_mult c b)
      (real_mult_lt_compat a b c hab hc) (real_mult_comm b c))

(** val real_inv_pos_lt_contra :
    real -> real -> real_lt -> real_lt -> real_lt -> real_lt **)

let real_inv_pos_lt_contra a b ha hb hab =
  real_eq_lt_lt (real_inv_pos b hb)
    (real_mult (real_mult (real_inv_pos a ha) a) (real_inv_pos b hb))
    (real_inv_pos a ha)
    (real_eq_trans (real_inv_pos b hb)
      (real_mult real_one (real_inv_pos b hb))
      (real_mult (real_mult (real_inv_pos a ha) a) (real_inv_pos b hb))
      (real_eq_sym (real_mult real_one (real_inv_pos b hb))
        (real_inv_pos b hb)
        (real_eq_trans (real_mult real_one (real_inv_pos b hb))
          (real_mult (real_inv_pos b hb) real_one) (real_inv_pos b hb)
          (real_mult_comm real_one (real_inv_pos b hb))
          (real_mult_one (real_inv_pos b hb))))
      (RealSetoid.real_eq_mult_compat real_one (real_inv_pos b hb)
        (real_mult (real_inv_pos a ha) a) (real_inv_pos b hb)
        (real_eq_sym (real_mult (real_inv_pos a ha) a) real_one
          (real_eq_trans (real_mult (real_inv_pos a ha) a)
            (real_mult a (real_inv_pos a ha)) real_one
            (real_mult_comm (real_inv_pos a ha) a)
            (real_inv_pos_correct a ha)))
        (real_eq_refl (real_inv_pos b hb))))
    (real_lt_eq_lt
      (real_mult (real_mult (real_inv_pos a ha) a) (real_inv_pos b hb))
      (real_mult (real_mult (real_inv_pos a ha) b) (real_inv_pos b hb))
      (real_inv_pos a ha)
      (real_mult_lt_compat (real_mult (real_inv_pos a ha) a)
        (real_mult (real_inv_pos a ha) b) (real_inv_pos b hb)
        (real_mult_lt_compat_l a b (real_inv_pos a ha) hab
          (real_inv_pos_pos a ha))
        (real_inv_pos_pos b hb))
      (real_eq_trans
        (real_mult (real_mult (real_inv_pos a ha) b) (real_inv_pos b hb))
        (real_mult (real_inv_pos a ha) (real_mult b (real_inv_pos b hb)))
        (real_inv_pos a ha)
        (real_eq_sym
          (real_mult (real_inv_pos a ha) (real_mult b (real_inv_pos b hb)))
          (real_mult (real_mult (real_inv_pos a ha) b) (real_inv_pos b hb))
          (real_mult_assoc (real_inv_pos a ha) b (real_inv_pos b hb)))
        (real_eq_trans
          (real_mult (real_inv_pos a ha) (real_mult b (real_inv_pos b hb)))
          (real_mult (real_inv_pos a ha) real_one) (real_inv_pos a ha)
          (RealSetoid.real_eq_mult_compat (real_inv_pos a ha)
            (real_mult b (real_inv_pos b hb)) (real_inv_pos a ha) real_one
            (real_eq_refl (real_inv_pos a ha)) (real_inv_pos_correct b hb))
          (real_mult_one (real_inv_pos a ha)))))

(** val real_lt_plus_translate :
    real -> real -> real -> real_lt -> real_lt **)

let real_lt_plus_translate b c d = function
| ExistT (x, a) ->
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in
  ExistT (x, (Pair (q0, (ExistT (x0, (fun n _ ->
  qlt_to_QltT x (qminus (projT1 (real_plus b d) n) (projT1 (real_plus b c) n))))))))

(** val real_lt_plus_compat_lt_le :
    real -> real -> real -> real -> real_lt -> real_le -> real_lt **)

let real_lt_plus_compat_lt_le a b c d hab = function
| Inl r -> real_lt_plus_compat a b c d hab r
| Inr r ->
  real_eq_lt_lt (real_plus a c) (real_plus a d) (real_plus b d)
    (RealSetoid.real_eq_plus_compat a c a d (real_eq_refl a) r)
    (real_eq_lt_lt (real_plus a d) (real_plus d a) (real_plus b d)
      (real_plus_comm a d)
      (real_lt_eq_lt (real_plus d a) (real_plus d b) (real_plus b d)
        (real_lt_plus_translate d a b hab) (real_plus_comm d b)))

(** val real_le_plus_compat :
    real -> real -> real -> real -> real_le -> real_le -> real_le **)

let real_le_plus_compat a b c d hab hcd =
  match hab with
  | Inl r ->
    (match hcd with
     | Inl r0 ->
       RealSetoid.real_lt_le_iff_req (real_plus a c) (real_plus b d) (Inl
         (real_lt_plus_compat a b c d r r0))
     | Inr r0 ->
       RealSetoid.real_lt_le_iff_req (real_plus a c) (real_plus b d) (Inl
         (real_lt_plus_compat_lt_le a b c d r (RealSetoid.real_eq_le c d r0))))
  | Inr r ->
    (match hcd with
     | Inl r0 ->
       RealSetoid.real_lt_le_iff_req (real_plus a c) (real_plus b d) (Inl
         (real_eq_lt_lt (real_plus a c) (real_plus b c) (real_plus b d)
           (RealSetoid.real_eq_plus_compat a c b c r (real_eq_refl c))
           (real_lt_plus_translate b c d r0)))
     | Inr r0 ->
       RealSetoid.real_eq_le (real_plus a c) (real_plus b d)
         (RealSetoid.real_eq_plus_compat a c b d r r0))

(** val real_inv_pos_ext :
    real -> real -> real_lt -> real_lt -> real_eq -> real_eq **)

let real_inv_pos_ext x y hx hy heq =
  real_eq_trans (real_inv_pos x hx)
    (real_mult (real_inv_pos x hx) (real_mult y (real_inv_pos y hy)))
    (real_inv_pos y hy)
    (real_eq_trans (real_inv_pos x hx)
      (real_mult (real_inv_pos x hx) real_one)
      (real_mult (real_inv_pos x hx) (real_mult y (real_inv_pos y hy)))
      (real_eq_sym (real_mult (real_inv_pos x hx) real_one)
        (real_inv_pos x hx) (real_mult_one (real_inv_pos x hx)))
      (RealSetoid.real_eq_mult_compat (real_inv_pos x hx) real_one
        (real_inv_pos x hx) (real_mult y (real_inv_pos y hy))
        (real_eq_refl (real_inv_pos x hx))
        (real_eq_sym (real_mult y (real_inv_pos y hy)) real_one
          (real_inv_pos_correct y hy))))
    (real_eq_trans
      (real_mult (real_inv_pos x hx) (real_mult y (real_inv_pos y hy)))
      (real_mult (real_mult (real_inv_pos x hx) y) (real_inv_pos y hy))
      (real_inv_pos y hy)
      (real_mult_assoc (real_inv_pos x hx) y (real_inv_pos y hy))
      (real_eq_trans
        (real_mult (real_mult (real_inv_pos x hx) y) (real_inv_pos y hy))
        (real_mult (real_mult (real_inv_pos x hx) x) (real_inv_pos y hy))
        (real_inv_pos y hy)
        (RealSetoid.real_eq_mult_compat (real_mult (real_inv_pos x hx) y)
          (real_inv_pos y hy) (real_mult (real_inv_pos x hx) x)
          (real_inv_pos y hy)
          (RealSetoid.real_eq_mult_compat (real_inv_pos x hx) y
            (real_inv_pos x hx) x (real_eq_refl (real_inv_pos x hx))
            (real_eq_sym x y heq))
          (real_eq_refl (real_inv_pos y hy)))
        (real_eq_trans
          (real_mult (real_mult (real_inv_pos x hx) x) (real_inv_pos y hy))
          (real_mult real_one (real_inv_pos y hy)) (real_inv_pos y hy)
          (RealSetoid.real_eq_mult_compat (real_mult (real_inv_pos x hx) x)
            (real_inv_pos y hy) real_one (real_inv_pos y hy)
            (real_eq_trans (real_mult (real_inv_pos x hx) x)
              (real_mult x (real_inv_pos x hx)) real_one
              (real_mult_comm (real_inv_pos x hx) x)
              (real_inv_pos_correct x hx))
            (real_eq_refl (real_inv_pos y hy)))
          (real_eq_trans (real_mult real_one (real_inv_pos y hy))
            (real_mult (real_inv_pos y hy) real_one) (real_inv_pos y hy)
            (real_mult_comm real_one (real_inv_pos y hy))
            (real_mult_one (real_inv_pos y hy))))))

(** val real_inv_pos_le_compat :
    real -> real -> real_lt -> real_lt -> real_le -> real_le **)

let real_inv_pos_le_compat a b ha hb = function
| Inl r ->
  RealSetoid.real_lt_le_iff_req (real_inv_pos b hb) (real_inv_pos a ha) (Inl
    (real_inv_pos_lt_contra a b ha hb r))
| Inr r ->
  RealSetoid.real_eq_le (real_inv_pos b hb) (real_inv_pos a ha)
    (real_inv_pos_ext b a hb ha (real_eq_sym a b r))

(** val real_le_mult_compat :
    real -> real -> real -> real_lt -> real_le -> real_le **)

let real_le_mult_compat a b c hc = function
| Inl r ->
  RealSetoid.real_lt_le_iff_req (real_mult a c) (real_mult b c) (Inl
    (real_mult_lt_compat a b c r hc))
| Inr r ->
  RealSetoid.real_eq_le (real_mult a c) (real_mult b c)
    (RealSetoid.real_eq_mult_compat a c b c r (real_eq_refl c))

(** val real_le_mult_compat_weak :
    real -> real -> real -> real_le -> real_le -> real_le **)

let real_le_mult_compat_weak a b c hc hab =
  match hc with
  | Inl r -> real_le_mult_compat a b c r hab
  | Inr r ->
    RealSetoid.real_eq_le (real_mult a c) (real_mult b c)
      (real_eq_trans (real_mult a c) (real_mult a real_zero) (real_mult b c)
        (RealSetoid.real_eq_mult_compat a c a real_zero (real_eq_refl a)
          (real_eq_sym real_zero c r))
        (real_eq_trans (real_mult a real_zero) real_zero (real_mult b c)
          (real_mult_zero a)
          (real_eq_sym (real_mult b c) real_zero
            (real_eq_trans (real_mult b c) (real_mult b real_zero) real_zero
              (RealSetoid.real_eq_mult_compat b c b real_zero
                (real_eq_refl b) (real_eq_sym real_zero c r))
              (real_mult_zero b)))))

(** val real_lt_zero_one : real_lt **)

let real_lt_zero_one =
  ExistT
    ((qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
       XH }),
    (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
         XH })),
    (ExistT (O, (fun n _ ->
    qlt_to_QltT
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH })
      (qminus (projT1 real_one n) (projT1 real_zero n))))))))

(** val real_abs_zero_req : real_eq **)

let real_abs_zero_req =
  real_eq_of_zero_diff (real_abs real_zero) real_zero

(** val real_abs_mult_req : real -> real -> real_eq **)

let real_abs_mult_req a b =
  real_eq_of_zero_diff (real_abs (real_mult a b))
    (real_mult (real_abs a) (real_abs b))

(** val real_abs_pos_req : real -> real_lt -> real_eq **)

let real_abs_pos_req a ha eps _ =
  let ExistT (_, a0) = ha in
  let Pair (_, s) = a0 in
  let ExistT (x, _) = s in
  ExistT (x, (fun n _ ->
  qlt_to_QltT (qabs (qminus (projT1 (real_abs a) n) (projT1 a n))) eps))

(** val real_abs_triangle_le_eps :
    real -> real -> real -> real_lt -> real_le **)

let real_abs_triangle_le_eps a b eps = function
| ExistT (x, a0) ->
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  RealSetoid.real_lt_le_iff_req (real_abs (real_plus a b))
    (real_plus (real_plus (real_abs a) (real_abs b)) eps) (Inl (ExistT
    ((qdiv x { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv x { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (x0, (fun n _ ->
    qlt_to_QltT (qdiv x { qnum = (Zpos (XO XH)); qden = XH })
      (qminus
        (projT1 (real_plus (real_plus (real_abs a) (real_abs b)) eps) n)
        (projT1 (real_abs (real_plus a b)) n))))))))))

(** val real_opp_plus : real -> real -> real_eq **)

let real_opp_plus a b =
  real_eq_of_zero_diff (real_opp (real_plus a b))
    (real_plus (real_opp a) (real_opp b))

(** val real_opp_mult : real -> real -> real_eq **)

let real_opp_mult a b =
  real_eq_of_zero_diff (real_opp (real_mult a b)) (real_mult a (real_opp b))

(** val real_opp_mult_r : real -> real -> real_eq **)

let real_opp_mult_r a b =
  real_eq_of_zero_diff (real_opp (real_mult a b)) (real_mult (real_opp a) b)

(** val real_mult_opp_l : real -> real -> real_eq **)

let real_mult_opp_l a b =
  real_eq_of_zero_diff (real_mult a (real_opp b)) (real_opp (real_mult a b))

(** val real_opp_opp : real -> real_eq **)

let real_opp_opp x =
  real_eq_of_zero_diff (real_opp (real_opp x)) x

(** val real_list_sum : ('a1 -> real) -> 'a1 list -> real **)

let rec real_list_sum f = function
| Nil -> real_zero
| Cons (w, rest) -> real_plus (f w) (real_list_sum f rest)

(** val real_list_sum_ext :
    ('a1 -> real) -> ('a1 -> real) -> 'a1 list -> ('a1 -> real_eq) -> real_eq **)

let rec real_list_sum_ext f g l hfg =
  match l with
  | Nil -> real_eq_refl real_zero
  | Cons (y, l0) ->
    RealSetoid.real_eq_plus_compat (f y) (real_list_sum f l0) (g y)
      (real_list_sum g l0) (hfg y) (real_list_sum_ext f g l0 hfg)

(** val real_plus_swap_mid : real -> real -> real -> real -> real_eq **)

let real_plus_swap_mid a b c d =
  real_eq_trans (real_plus (real_plus a b) (real_plus c d))
    (real_plus a (real_plus b (real_plus c d)))
    (real_plus (real_plus a c) (real_plus b d))
    (real_eq_sym (real_plus a (real_plus b (real_plus c d)))
      (real_plus (real_plus a b) (real_plus c d))
      (real_plus_assoc a b (real_plus c d)))
    (real_eq_trans (real_plus a (real_plus b (real_plus c d)))
      (real_plus a (real_plus (real_plus c d) b))
      (real_plus (real_plus a c) (real_plus b d))
      (RealSetoid.real_eq_plus_compat a (real_plus b (real_plus c d)) a
        (real_plus (real_plus c d) b) (real_eq_refl a)
        (real_plus_comm b (real_plus c d)))
      (real_eq_trans (real_plus a (real_plus (real_plus c d) b))
        (real_plus a (real_plus c (real_plus d b)))
        (real_plus (real_plus a c) (real_plus b d))
        (RealSetoid.real_eq_plus_compat a (real_plus (real_plus c d) b) a
          (real_plus c (real_plus d b)) (real_eq_refl a)
          (real_eq_sym (real_plus c (real_plus d b))
            (real_plus (real_plus c d) b) (real_plus_assoc c d b)))
        (real_eq_trans (real_plus a (real_plus c (real_plus d b)))
          (real_plus a (real_plus c (real_plus b d)))
          (real_plus (real_plus a c) (real_plus b d))
          (RealSetoid.real_eq_plus_compat a (real_plus c (real_plus d b)) a
            (real_plus c (real_plus b d)) (real_eq_refl a)
            (RealSetoid.real_eq_plus_compat c (real_plus d b) c
              (real_plus b d) (real_eq_refl c) (real_plus_comm d b)))
          (real_plus_assoc a c (real_plus b d)))))

(** val real_list_sum_add :
    ('a1 -> real) -> ('a1 -> real) -> 'a1 list -> real_eq **)

let rec real_list_sum_add f g = function
| Nil ->
  real_eq_sym (real_plus real_zero real_zero) real_zero
    (real_plus_zero real_zero)
| Cons (y, l0) ->
  real_eq_trans
    (real_plus (real_plus (f y) (g y))
      (real_list_sum (fun w -> real_plus (f w) (g w)) l0))
    (real_plus (real_plus (f y) (g y))
      (real_plus (real_list_sum f l0) (real_list_sum g l0)))
    (real_plus (real_plus (f y) (real_list_sum f l0))
      (real_plus (g y) (real_list_sum g l0)))
    (RealSetoid.real_eq_plus_compat (real_plus (f y) (g y))
      (real_list_sum (fun w0 -> real_plus (f w0) (g w0)) l0)
      (real_plus (f y) (g y))
      (real_plus (real_list_sum f l0) (real_list_sum g l0))
      (real_eq_refl (real_plus (f y) (g y))) (real_list_sum_add f g l0))
    (real_plus_swap_mid (f y) (g y) (real_list_sum f l0) (real_list_sum g l0))

(** val real_list_sum_linear :
    real -> ('a1 -> real) -> 'a1 list -> real_eq **)

let rec real_list_sum_linear a f = function
| Nil -> real_eq_sym (real_mult a real_zero) real_zero (real_mult_zero a)
| Cons (y, l0) ->
  real_eq_trans
    (real_plus (real_mult a (f y))
      (real_list_sum (fun w -> real_mult a (f w)) l0))
    (real_plus (real_mult a (f y)) (real_mult a (real_list_sum f l0)))
    (real_mult a (real_plus (f y) (real_list_sum f l0)))
    (RealSetoid.real_eq_plus_compat (real_mult a (f y))
      (real_list_sum (fun w0 -> real_mult a (f w0)) l0) (real_mult a (f y))
      (real_mult a (real_list_sum f l0)) (real_eq_refl (real_mult a (f y)))
      (real_list_sum_linear a f l0))
    (real_eq_sym (real_mult a (real_plus (f y) (real_list_sum f l0)))
      (real_plus (real_mult a (f y)) (real_mult a (real_list_sum f l0)))
      (real_distrib a (f y) (real_list_sum f l0)))

(** val real_list_sum_linear_r :
    real -> ('a1 -> real) -> 'a1 list -> real_eq **)

let real_list_sum_linear_r a f l =
  real_eq_trans (real_list_sum (fun w -> real_mult (f w) a) l)
    (real_list_sum (fun w -> real_mult a (f w)) l)
    (real_mult a (real_list_sum f l))
    (real_list_sum_ext (fun w -> real_mult (f w) a) (fun w ->
      real_mult a (f w)) l (fun w -> real_mult_comm (f w) a))
    (real_list_sum_linear a f l)

(** val real_opp_zero : real_eq **)

let real_opp_zero =
  real_eq_trans (real_opp real_zero)
    (real_plus (real_opp real_zero) real_zero) real_zero
    (real_eq_sym (real_plus (real_opp real_zero) real_zero)
      (real_opp real_zero) (real_plus_zero (real_opp real_zero)))
    (real_eq_trans (real_plus (real_opp real_zero) real_zero)
      (real_plus real_zero (real_opp real_zero)) real_zero
      (real_plus_comm (real_opp real_zero) real_zero)
      (real_plus_opp real_zero))

(** val real_list_sum_opp : ('a1 -> real) -> 'a1 list -> real_eq **)

let rec real_list_sum_opp f = function
| Nil -> real_eq_sym (real_opp real_zero) real_zero real_opp_zero
| Cons (y, l0) ->
  real_eq_trans
    (real_plus (real_opp (f y)) (real_list_sum (fun w -> real_opp (f w)) l0))
    (real_plus (real_opp (f y)) (real_opp (real_list_sum f l0)))
    (real_opp (real_plus (f y) (real_list_sum f l0)))
    (RealSetoid.real_eq_plus_compat (real_opp (f y))
      (real_list_sum (fun w0 -> real_opp (f w0)) l0) (real_opp (f y))
      (real_opp (real_list_sum f l0)) (real_eq_refl (real_opp (f y)))
      (real_list_sum_opp f l0))
    (real_eq_sym (real_opp (real_plus (f y) (real_list_sum f l0)))
      (real_plus (real_opp (f y)) (real_opp (real_list_sum f l0)))
      (real_opp_plus (f y) (real_list_sum f l0)))

(** val real_list_sum_le :
    ('a1 -> real) -> ('a1 -> real) -> 'a1 list -> ('a1 -> real_le) -> real_le **)

let rec real_list_sum_le f g l hfg =
  match l with
  | Nil -> real_le_refl real_zero
  | Cons (y, l0) ->
    real_le_plus_compat (f y) (g y) (real_list_sum f l0) (real_list_sum g l0)
      (hfg y) (real_list_sum_le f g l0 hfg)

(** val real_list_sum_nonneg :
    ('a1 -> real) -> 'a1 list -> ('a1 -> real_le) -> real_le **)

let rec real_list_sum_nonneg f l hnonneg =
  match l with
  | Nil -> real_le_refl real_zero
  | Cons (y, l0) ->
    RealSetoid.real_le_id_l real_zero (real_plus real_zero real_zero)
      (real_plus (f y) (real_list_sum f l0))
      (real_eq_sym (real_plus real_zero real_zero) real_zero
        (real_plus_zero real_zero))
      (real_le_plus_compat real_zero (f y) real_zero (real_list_sum f l0)
        (hnonneg y) (real_list_sum_nonneg f l0 hnonneg))

(** val real_of_nat : nat -> real **)

let rec real_of_nat = function
| O -> real_zero
| S n' -> real_plus real_one (real_of_nat n')

(** val real_abs_eq_compat : real -> real -> real_eq -> real_eq **)

let real_abs_eq_compat x y hxy eps heps =
  let s = hxy eps heps in
  let ExistT (x0, _) = s in
  ExistT (x0, (fun n _ ->
  qlt_to_QltT (qabs (qminus (projT1 (real_abs x) n) (projT1 (real_abs y) n)))
    eps))

(** val real_le_mult_compat_r :
    real -> real -> real -> real_le -> real_le -> real_le **)

let real_le_mult_compat_r a b c ha hbc =
  RealSetoid.real_le_id_l (real_mult a b) (real_mult b a) (real_mult a c)
    (real_mult_comm a b)
    (RealSetoid.real_le_id_r (real_mult b a) (real_mult c a) (real_mult a c)
      (real_eq_sym (real_mult a c) (real_mult c a) (real_mult_comm a c))
      (real_le_mult_compat_weak b c a ha hbc))

(** val real_minus_r : real -> real -> real **)

let real_minus_r a b =
  real_plus a (real_opp b)

(** val real_le_from_lt_aux : real -> real -> real_lt -> real_le **)

let real_le_from_lt_aux _ _ h =
  Inl h

(** val real_le_mult_compat_l_aux :
    real -> real -> real -> real_lt -> real_le -> real_le **)

let real_le_mult_compat_l_aux a b c hc hab =
  RealSetoid.real_le_id_l (real_mult c a) (real_mult a c) (real_mult c b)
    (real_mult_comm c a)
    (RealSetoid.real_le_id_r (real_mult a c) (real_mult b c) (real_mult c b)
      (real_mult_comm b c) (real_le_mult_compat a b c hc hab))

(** val real_le_plus_nonneg_r_aux : real -> real -> real_le -> real_le **)

let real_le_plus_nonneg_r_aux a b hb =
  RealSetoid.real_le_id_l a (real_plus a real_zero) (real_plus a b)
    (real_eq_sym (real_plus a real_zero) a (real_plus_zero a))
    (real_le_plus_compat a a real_zero b (real_le_refl a) hb)

(** val real_le_minus_nonneg_aux : real -> real -> real_le -> real_le **)

let real_le_minus_nonneg_aux a b = function
| Inl r ->
  real_le_from_lt_aux real_zero (real_plus b (real_opp a))
    (real_lt_opp_plus a b r)
| Inr r ->
  RealSetoid.real_eq_le real_zero (real_plus b (real_opp a))
    (real_eq_sym (real_plus b (real_opp a)) real_zero
      (real_eq_trans (real_plus b (real_opp a)) (real_plus b (real_opp b))
        real_zero
        (RealSetoid.real_eq_plus_compat b (real_opp a) b (real_opp b)
          (real_eq_refl b) (RealSetoid.real_eq_opp_compat a b r))
        (real_plus_opp b)))

(** val real_abs_minus_r_nonneg_aux : real -> real -> real_le -> real_eq **)

let real_abs_minus_r_nonneg_aux u v huv =
  let hd = real_le_minus_nonneg_aux u v huv in
  let e1 =
    real_eq_trans (real_minus_r u v) (real_plus (real_opp v) u)
      (real_opp (real_plus v (real_opp u))) (real_plus_comm u (real_opp v))
      (real_eq_trans (real_plus (real_opp v) u)
        (real_plus (real_opp v) (real_opp (real_opp u)))
        (real_opp (real_plus v (real_opp u)))
        (RealSetoid.real_eq_plus_compat (real_opp v) u (real_opp v)
          (real_opp (real_opp u)) (real_eq_refl (real_opp v))
          (real_eq_sym (real_opp (real_opp u)) u (real_opp_opp u)))
        (real_eq_sym (real_opp (real_plus v (real_opp u)))
          (real_plus (real_opp v) (real_opp (real_opp u)))
          (real_opp_plus v (real_opp u))))
  in
  let e2 =
    real_eq_trans (real_abs (real_minus_r u v))
      (real_abs (real_opp (real_plus v (real_opp u))))
      (real_abs (real_plus v (real_opp u)))
      (real_abs_eq_compat (real_minus_r u v)
        (real_opp (real_plus v (real_opp u))) e1)
      (real_abs_opp (real_plus v (real_opp u)))
  in
  let e3 =
    match hd with
    | Inl r -> real_abs_pos_req (real_plus v (real_opp u)) r
    | Inr r ->
      real_eq_trans (real_abs (real_plus v (real_opp u))) real_zero
        (real_plus v (real_opp u))
        (real_eq_trans (real_abs (real_plus v (real_opp u)))
          (real_abs real_zero) real_zero
          (real_abs_eq_compat (real_plus v (real_opp u)) real_zero
            (real_eq_sym real_zero (real_plus v (real_opp u)) r))
          real_abs_zero_req)
        r
  in
  real_eq_trans (real_abs (real_minus_r u v))
    (real_abs (real_plus v (real_opp u))) (real_plus v (real_opp u)) e2 e3

(** val kv_id_transport : 'a1 -> 'a1 -> 'a2 -> 'a1 id -> 'a2 **)

let kv_id_transport _ _ p _ =
  p

(** val z_keep :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> bool) -> 'a1 -> real **)

let z_keep states k keep s =
  real_list_sum (fun s' ->
    match keep s' with
    | True -> k s s'
    | False -> real_zero) states

(** val kv_ofnat_nonneg : nat -> real_le **)

let rec kv_ofnat_nonneg = function
| O -> real_le_refl (real_of_nat O)
| S n0 ->
  RealSetoid.real_le_id_l real_zero (real_plus real_zero real_zero)
    (real_plus real_one (real_of_nat n0))
    (real_eq_sym (real_plus real_zero real_zero) real_zero
      (real_plus_zero real_zero))
    (real_le_plus_compat real_zero real_one real_zero (real_of_nat n0)
      (real_le_from_lt_aux real_zero real_one real_lt_zero_one)
      (kv_ofnat_nonneg n0))

(** val kv_ofnat_S_pos : nat -> real_lt **)

let kv_ofnat_S_pos k =
  real_lt_le_trans real_zero real_one (real_plus real_one (real_of_nat k))
    real_lt_zero_one
    (real_le_plus_nonneg_r_aux real_one (real_of_nat k) (kv_ofnat_nonneg k))

(** val kv_N_pos :
    'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq)
    -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> real_lt **)

let kv_N_pos states _ _ _ _ _ =
  match states with
  | Nil -> assert false (* absurd case *)
  | Cons (_, l) -> kv_ofnat_S_pos (length l)

(** val kv_single_le_sum :
    ('a1 -> real) -> 'a1 -> 'a1 list -> 'a1 inT -> ('a1 -> real_le) -> real_le **)

let rec kv_single_le_sum f x _ hin hnn =
  match hin with
  | InT_here l ->
    real_le_plus_nonneg_r_aux (f x) (real_list_sum f l)
      (real_list_sum_nonneg f l hnn)
  | InT_next (y, l, i) ->
    real_le_trans (f x) (real_list_sum f l)
      (real_plus (f y) (real_list_sum f l)) (kv_single_le_sum f x l i hnn)
      (RealSetoid.real_le_id_r (real_list_sum f l)
        (real_plus (real_list_sum f l) (f y))
        (real_plus (f y) (real_list_sum f l))
        (real_plus_comm (real_list_sum f l) (f y))
        (real_le_plus_nonneg_r_aux (real_list_sum f l) (f y) (hnn y)))

(** val z_keep_pos :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
    bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> real_lt **)

let z_keep_pos states k kpos keep keep_nonempty s =
  let ExistT (x, a) = keep_nonempty in
  let Pair (i, i0) = a in
  let hlt0 = kv_id_transport True (keep x) (kpos s x) (id_sym (keep x) True i)
  in
  let hle =
    kv_single_le_sum (fun y ->
      match keep y with
      | True -> k s y
      | False -> real_zero) x states i0 (fun y ->
      let b = keep y in
      (match b with
       | True -> real_le_from_lt_aux real_zero (k s y) (kpos s y)
       | False -> real_le_refl real_zero))
  in
  (match hle with
   | Inl r ->
     real_lt_trans real_zero
       (match keep x with
        | True -> k s x
        | False -> real_zero)
       (z_keep states k keep s) hlt0 r
   | Inr r ->
     real_lt_eq_lt real_zero
       (match keep x with
        | True -> k s x
        | False -> real_zero)
       (z_keep states k keep s) hlt0 r)

(** val k_ev :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
    bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> 'a1 -> real **)

let k_ev states k kpos keep keep_nonempty s s' =
  match keep s' with
  | True ->
    real_mult (k s s')
      (real_inv_pos (z_keep states k keep s)
        (z_keep_pos states k kpos keep keep_nonempty s))
  | False -> real_zero

(** val invZK :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
    bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> real **)

let invZK states k kpos keep keep_nonempty s =
  real_inv_pos (z_keep states k keep s)
    (z_keep_pos states k kpos keep keep_nonempty s)

(** val tail_row :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> bool) -> 'a1 -> real **)

let tail_row states k keep s =
  real_list_sum (fun s' ->
    match keep s' with
    | True -> real_zero
    | False -> k s s') states

(** val tv_row :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
    bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> real **)

let tv_row states k kpos keep keep_nonempty s =
  real_list_sum (fun s' ->
    real_abs
      (real_minus_r (k s s') (k_ev states k kpos keep keep_nonempty s s')))
    states

(** val lstep :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real) -> 'a1 -> real **)

let lstep states p mu s' =
  real_list_sum (fun s -> real_mult (mu s) (p s s')) states

(** val kev_iter :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
    bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> nat -> ('a1 -> real) ->
    'a1 -> real **)

let rec kev_iter states k kpos keep keep_nonempty n mu =
  match n with
  | O -> mu
  | S m ->
    lstep states (k_ev states k kpos keep keep_nonempty)
      (kev_iter states k kpos keep keep_nonempty m mu)

(** val k_iter :
    'a1 list -> ('a1 -> 'a1 -> real) -> nat -> ('a1 -> real) -> 'a1 -> real **)

let rec k_iter states k n mu =
  match n with
  | O -> mu
  | S m -> lstep states k (k_iter states k m mu)

(** val ddist : 'a1 list -> ('a1 -> real) -> ('a1 -> real) -> real **)

let ddist states mu nu =
  real_list_sum (fun x -> real_abs (real_minus_r (mu x) (nu x))) states

(** val kv_plus_zero_l : real -> real_eq **)

let kv_plus_zero_l a =
  real_eq_trans (real_plus real_zero a) (real_plus a real_zero) a
    (real_plus_comm real_zero a) (real_plus_zero a)

(** val kv_one_mult_l : real -> real_eq **)

let kv_one_mult_l a =
  real_eq_trans (real_mult real_one a) (real_mult a real_one) a
    (real_mult_comm real_one a) (real_mult_one a)

(** val kv_two_R_pos : real_lt **)

let kv_two_R_pos =
  RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
    (real_plus real_one real_one)
    (real_eq_sym (real_plus real_zero real_zero) real_zero
      (real_plus_zero real_zero))
    (real_lt_plus_compat real_zero real_one real_zero real_one
      real_lt_zero_one real_lt_zero_one)

(** val kv_three_R_pos : real_lt **)

let kv_three_R_pos =
  RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
    (real_plus (real_plus real_one real_one) real_one)
    (real_eq_sym (real_plus real_zero real_zero) real_zero
      (real_plus_zero real_zero))
    (real_lt_plus_compat real_zero (real_plus real_one real_one) real_zero
      real_one kv_two_R_pos real_lt_zero_one)

(** val kv_distrib_r : real -> real -> real -> real_eq **)

let kv_distrib_r a b c0 =
  real_eq_trans (real_mult (real_plus a b) c0) (real_mult c0 (real_plus a b))
    (real_plus (real_mult a c0) (real_mult b c0))
    (real_mult_comm (real_plus a b) c0)
    (real_eq_trans (real_mult c0 (real_plus a b))
      (real_plus (real_mult c0 a) (real_mult c0 b))
      (real_plus (real_mult a c0) (real_mult b c0)) (real_distrib c0 a b)
      (RealSetoid.real_eq_plus_compat (real_mult c0 a) (real_mult c0 b)
        (real_mult a c0) (real_mult b c0) (real_mult_comm c0 a)
        (real_mult_comm c0 b)))

(** val kv_abs_nonneg_id : real -> real_le -> real_eq **)

let kv_abs_nonneg_id a = function
| Inl r -> real_abs_pos_req a r
| Inr r ->
  real_eq_trans (real_abs a) (real_abs real_zero) a
    (real_abs_eq_compat a real_zero (real_eq_sym real_zero a r))
    (real_eq_trans (real_abs real_zero) real_zero a real_abs_zero_req r)

(** val kv_sum_zero_list : 'a1 list -> real_eq **)

let rec kv_sum_zero_list = function
| Nil -> real_eq_refl real_zero
| Cons (_, l0) ->
  real_eq_trans (real_plus real_zero (real_list_sum (fun _ -> real_zero) l0))
    (real_plus real_zero real_zero) real_zero
    (RealSetoid.real_eq_plus_compat real_zero
      (real_list_sum (fun _ -> real_zero) l0) real_zero real_zero
      (real_eq_refl real_zero) (kv_sum_zero_list l0))
    (real_eq_trans (real_plus real_zero real_zero) real_zero real_zero
      (real_eq_refl (real_plus real_zero real_zero))
      (real_plus_zero real_zero))

(** val kv_sum_const_list : real -> 'a1 list -> real_eq **)

let rec kv_sum_const_list t = function
| Nil ->
  real_eq_sym (real_mult real_zero t) real_zero
    (real_eq_trans (real_mult real_zero t) (real_mult t real_zero) real_zero
      (real_mult_comm real_zero t) (real_mult_zero t))
| Cons (_, l0) ->
  real_eq_trans (real_plus t (real_list_sum (fun _ -> t) l0))
    (real_plus (real_mult real_one t) (real_mult (real_of_nat (length l0)) t))
    (real_mult (real_of_nat (S (length l0))) t)
    (RealSetoid.real_eq_plus_compat t (real_list_sum (fun _ -> t) l0)
      (real_mult real_one t) (real_mult (real_of_nat (length l0)) t)
      (real_eq_sym (real_mult real_one t) t (kv_one_mult_l t))
      (kv_sum_const_list t l0))
    (real_eq_sym (real_mult (real_of_nat (S (length l0))) t)
      (real_plus (real_mult real_one t)
        (real_mult (real_of_nat (length l0)) t))
      (kv_distrib_r real_one (real_of_nat (length l0)) t))

(** val kv_inv_absorb : real -> real_lt -> real -> real_eq **)

let kv_inv_absorb t ht x =
  real_eq_trans (real_mult t (real_mult (real_inv_pos t ht) x))
    (real_mult (real_mult t (real_inv_pos t ht)) x) x
    (real_mult_assoc t (real_inv_pos t ht) x)
    (real_eq_trans (real_mult (real_mult t (real_inv_pos t ht)) x)
      (real_mult real_one x) x
      (RealSetoid.real_eq_mult_compat (real_mult t (real_inv_pos t ht)) x
        real_one x (real_inv_pos_correct t ht) (real_eq_refl x))
      (kv_one_mult_l x))

(** val kv_plus_self_two : real -> real_eq **)

let kv_plus_self_two t =
  real_eq_trans (real_plus t t)
    (real_plus (real_mult t real_one) (real_mult t real_one))
    (real_mult (real_plus real_one real_one) t)
    (RealSetoid.real_eq_plus_compat t t (real_mult t real_one)
      (real_mult t real_one)
      (real_eq_sym (real_mult t real_one) t (real_mult_one t))
      (real_eq_sym (real_mult t real_one) t (real_mult_one t)))
    (real_eq_trans (real_plus (real_mult t real_one) (real_mult t real_one))
      (real_plus (real_mult real_one t) (real_mult real_one t))
      (real_mult (real_plus real_one real_one) t)
      (RealSetoid.real_eq_plus_compat (real_mult t real_one)
        (real_mult t real_one) (real_mult real_one t) (real_mult real_one t)
        (real_mult_comm t real_one) (real_mult_comm t real_one))
      (real_eq_sym (real_mult (real_plus real_one real_one) t)
        (real_plus (real_mult real_one t) (real_mult real_one t))
        (kv_distrib_r real_one real_one t)))

(** val kv_plus_self_three : real -> real_eq **)

let kv_plus_self_three t =
  real_eq_trans (real_plus (real_plus t t) t)
    (real_plus (real_plus (real_mult real_one t) (real_mult real_one t))
      (real_mult real_one t))
    (real_mult (real_plus (real_plus real_one real_one) real_one) t)
    (RealSetoid.real_eq_plus_compat (real_plus t t) t
      (real_plus (real_mult real_one t) (real_mult real_one t))
      (real_mult real_one t)
      (RealSetoid.real_eq_plus_compat t t (real_mult real_one t)
        (real_mult real_one t)
        (real_eq_sym (real_mult real_one t) t (kv_one_mult_l t))
        (real_eq_sym (real_mult real_one t) t (kv_one_mult_l t)))
      (real_eq_sym (real_mult real_one t) t (kv_one_mult_l t)))
    (real_eq_sym
      (real_mult (real_plus (real_plus real_one real_one) real_one) t)
      (real_plus (real_plus (real_mult real_one t) (real_mult real_one t))
        (real_mult real_one t))
      (real_eq_trans
        (real_mult (real_plus (real_plus real_one real_one) real_one) t)
        (real_plus (real_mult (real_plus real_one real_one) t)
          (real_mult real_one t))
        (real_plus (real_plus (real_mult real_one t) (real_mult real_one t))
          (real_mult real_one t))
        (kv_distrib_r (real_plus real_one real_one) real_one t)
        (RealSetoid.real_eq_plus_compat
          (real_mult (real_plus real_one real_one) t) (real_mult real_one t)
          (real_plus (real_mult real_one t) (real_mult real_one t))
          (real_mult real_one t) (kv_distrib_r real_one real_one t)
          (real_eq_refl (real_mult real_one t)))))

(** val kv_merge_regroup : real -> real -> real -> real_eq **)

let kv_merge_regroup a b h =
  real_eq_trans (real_plus (real_plus a (real_plus b h)) h)
    (real_plus (real_plus (real_plus a b) h) h)
    (real_plus (real_plus a b) (real_plus h h))
    (RealSetoid.real_eq_plus_compat (real_plus a (real_plus b h)) h
      (real_plus (real_plus a b) h) h (real_plus_assoc a b h)
      (real_eq_refl h))
    (real_eq_sym (real_plus (real_plus a b) (real_plus h h))
      (real_plus (real_plus (real_plus a b) h) h)
      (real_plus_assoc (real_plus a b) h h))

(** val kv_abs_triangle_list_eps :
    ('a1 -> real) -> 'a1 list -> real -> real_lt -> real_le **)

let rec kv_abs_triangle_list_eps f l eps heps =
  match l with
  | Nil ->
    real_le_trans (real_abs (real_list_sum f Nil)) real_zero
      (real_plus real_zero eps)
      (RealSetoid.real_eq_le (real_abs (real_list_sum f Nil)) real_zero
        real_abs_zero_req)
      (real_le_from_lt_aux real_zero (real_plus real_zero eps)
        (RealSetoid.real_lt_id_r real_zero eps (real_plus real_zero eps)
          (real_eq_sym (real_plus real_zero eps) eps (kv_plus_zero_l eps))
          heps))
  | Cons (y, l0) ->
    let hhalf =
      real_mult_pos_compat
        (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps
        (real_inv_pos_pos (real_plus real_one real_one) kv_two_R_pos) heps
    in
    let hinv2one =
      real_eq_trans
        (real_plus (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
          (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
        (real_mult (real_plus real_one real_one)
          (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
        real_one
        (kv_plus_self_two
          (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
        (real_inv_pos_correct (real_plus real_one real_one) kv_two_R_pos)
    in
    let hhh =
      real_eq_trans
        (real_plus
          (real_mult
            (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps)
          (real_mult
            (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps))
        (real_mult
          (real_plus
            (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
            (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
          eps)
        eps
        (real_eq_sym
          (real_mult
            (real_plus
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
            eps)
          (real_plus
            (real_mult
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps)
            (real_mult
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps))
          (kv_distrib_r
            (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
            (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps))
        (real_eq_trans
          (real_mult
            (real_plus
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
            eps)
          (real_mult real_one eps) eps
          (RealSetoid.real_eq_mult_compat
            (real_plus
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
            eps real_one eps hinv2one (real_eq_refl eps))
          (kv_one_mult_l eps))
    in
    let h1 =
      real_abs_triangle_le_eps (f y) (real_list_sum f l0)
        (real_mult (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
          eps)
        hhalf
    in
    let h2 =
      real_le_plus_compat
        (real_plus (real_abs (f y)) (real_abs (real_list_sum f l0)))
        (real_plus (real_abs (f y))
          (real_plus (real_list_sum (fun x -> real_abs (f x)) l0)
            (real_mult
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps)))
        (real_mult (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
          eps)
        (real_mult (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
          eps)
        (real_le_plus_compat (real_abs (f y)) (real_abs (f y))
          (real_abs (real_list_sum f l0))
          (real_plus (real_list_sum (fun x -> real_abs (f x)) l0)
            (real_mult
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps))
          (real_le_refl (real_abs (f y)))
          (kv_abs_triangle_list_eps f l0
            (real_mult
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps)
            hhalf))
        (real_le_refl
          (real_mult
            (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps))
    in
    let h3 =
      kv_merge_regroup (real_abs (f y))
        (real_list_sum (fun x -> real_abs (f x)) l0)
        (real_mult (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
          eps)
    in
    let h4 =
      RealSetoid.real_eq_le
        (real_plus
          (real_plus (real_abs (f y))
            (real_list_sum (fun x -> real_abs (f x)) l0))
          (real_plus
            (real_mult
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps)
            (real_mult
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps)))
        (real_plus
          (real_plus (real_abs (f y))
            (real_list_sum (fun x -> real_abs (f x)) l0))
          eps)
        (RealSetoid.real_eq_plus_compat
          (real_plus (real_abs (f y))
            (real_list_sum (fun x -> real_abs (f x)) l0))
          (real_plus
            (real_mult
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps)
            (real_mult
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps))
          (real_plus (real_abs (f y))
            (real_list_sum (fun x -> real_abs (f x)) l0))
          eps
          (real_eq_refl
            (real_plus (real_abs (f y))
              (real_list_sum (fun x -> real_abs (f x)) l0)))
          hhh)
    in
    real_le_trans (real_abs (real_plus (f y) (real_list_sum f l0)))
      (real_plus (real_plus (real_abs (f y)) (real_abs (real_list_sum f l0)))
        (real_mult (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
          eps))
      (real_plus
        (real_plus (real_abs (f y))
          (real_list_sum (fun x -> real_abs (f x)) l0))
        eps)
      h1
      (real_le_trans
        (real_plus
          (real_plus (real_abs (f y)) (real_abs (real_list_sum f l0)))
          (real_mult
            (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps))
        (real_plus
          (real_plus (real_abs (f y))
            (real_plus (real_list_sum (fun x -> real_abs (f x)) l0)
              (real_mult
                (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps)))
          (real_mult
            (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps))
        (real_plus
          (real_plus (real_abs (f y))
            (real_list_sum (fun x -> real_abs (f x)) l0))
          eps)
        h2
        (real_le_trans
          (real_plus
            (real_plus (real_abs (f y))
              (real_plus (real_list_sum (fun x -> real_abs (f x)) l0)
                (real_mult
                  (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
                  eps)))
            (real_mult
              (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps))
          (real_plus
            (real_plus (real_abs (f y))
              (real_list_sum (fun x -> real_abs (f x)) l0))
            (real_plus
              (real_mult
                (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps)
              (real_mult
                (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps)))
          (real_plus
            (real_plus (real_abs (f y))
              (real_list_sum (fun x -> real_abs (f x)) l0))
            eps)
          (RealSetoid.real_eq_le
            (real_plus
              (real_plus (real_abs (f y))
                (real_plus (real_list_sum (fun x -> real_abs (f x)) l0)
                  (real_mult
                    (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
                    eps)))
              (real_mult
                (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps))
            (real_plus
              (real_plus (real_abs (f y))
                (real_list_sum (fun x -> real_abs (f x)) l0))
              (real_plus
                (real_mult
                  (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
                  eps)
                (real_mult
                  (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
                  eps)))
            h3)
          h4))

(** val kv_swap_list :
    ('a1 -> 'a1 -> real) -> 'a1 list -> 'a1 list -> real_eq **)

let rec kv_swap_list f = function
| Nil -> kv_sum_zero_list
| Cons (y, l) ->
  (fun l2 ->
    real_eq_trans
      (real_list_sum (fun y0 ->
        real_plus (f y y0) (real_list_sum (fun x0 -> f x0 y0) l)) l2)
      (real_plus (real_list_sum (fun y0 -> f y y0) l2)
        (real_list_sum (fun y0 -> real_list_sum (fun x0 -> f x0 y0) l) l2))
      (real_plus (real_list_sum (fun y0 -> f y y0) l2)
        (real_list_sum (fun x -> real_list_sum (fun y0 -> f x y0) l2) l))
      (real_list_sum_add (fun y0 -> f y y0) (fun y0 ->
        real_list_sum (fun x0 -> f x0 y0) l) l2)
      (RealSetoid.real_eq_plus_compat (real_list_sum (fun y0 -> f y y0) l2)
        (real_list_sum (fun y0 -> real_list_sum (fun x0 -> f x0 y0) l) l2)
        (real_list_sum (fun y0 -> f y y0) l2)
        (real_list_sum (fun x0 -> real_list_sum (fun y0 -> f x0 y0) l2) l)
        (real_eq_refl (real_list_sum (fun y0 -> f y y0) l2))
        (kv_swap_list f l l2)))

(** val kv_share_pos :
    'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq)
    -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> real ->
    real_lt -> real_lt **)

let kv_share_pos states states_ne k krow keep keep_nonempty eps heps =
  real_mult_pos_compat
    (real_inv_pos (real_of_nat (length states))
      (kv_N_pos states states_ne k krow keep keep_nonempty))
    eps
    (real_inv_pos_pos (real_of_nat (length states))
      (kv_N_pos states states_ne k krow keep keep_nonempty))
    heps

(** val tvL : 'a1 list -> ('a1 -> real) -> ('a1 -> real) -> real **)

let tvL states mu nu =
  real_mult (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
    (ddist states mu nu)

(** val kv_ZK_plus_tail :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> bool) ->
    'a1 -> real_eq **)

let kv_ZK_plus_tail states k krow keep s =
  real_eq_trans
    (real_plus (z_keep states k keep s) (tail_row states k keep s))
    (real_list_sum (fun s' ->
      real_plus (match keep s' with
                 | True -> k s s'
                 | False -> real_zero)
        (match keep s' with
         | True -> real_zero
         | False -> k s s'))
      states)
    real_one
    (real_eq_trans
      (real_plus (z_keep states k keep s) (tail_row states k keep s))
      (real_plus
        (real_list_sum (fun s' ->
          match keep s' with
          | True -> k s s'
          | False -> real_zero) states)
        (real_list_sum (fun s' ->
          match keep s' with
          | True -> real_zero
          | False -> k s s') states))
      (real_list_sum (fun s' ->
        real_plus (match keep s' with
                   | True -> k s s'
                   | False -> real_zero)
          (match keep s' with
           | True -> real_zero
           | False -> k s s'))
        states)
      (real_eq_refl
        (real_plus
          (real_list_sum (fun s' ->
            match keep s' with
            | True -> k s s'
            | False -> real_zero) states)
          (real_list_sum (fun s' ->
            match keep s' with
            | True -> real_zero
            | False -> k s s') states)))
      (real_eq_sym
        (real_list_sum (fun s' ->
          real_plus (match keep s' with
                     | True -> k s s'
                     | False -> real_zero)
            (match keep s' with
             | True -> real_zero
             | False -> k s s'))
          states)
        (real_plus
          (real_list_sum (fun s' ->
            match keep s' with
            | True -> k s s'
            | False -> real_zero) states)
          (real_list_sum (fun s' ->
            match keep s' with
            | True -> real_zero
            | False -> k s s') states))
        (real_list_sum_add (fun s' ->
          match keep s' with
          | True -> k s s'
          | False -> real_zero) (fun s' ->
          match keep s' with
          | True -> real_zero
          | False -> k s s') states)))
    (real_eq_trans
      (real_list_sum (fun s' ->
        real_plus (match keep s' with
                   | True -> k s s'
                   | False -> real_zero)
          (match keep s' with
           | True -> real_zero
           | False -> k s s'))
        states)
      (real_list_sum (fun s' -> k s s') states) real_one
      (real_list_sum_ext (fun s' ->
        real_plus (match keep s' with
                   | True -> k s s'
                   | False -> real_zero)
          (match keep s' with
           | True -> real_zero
           | False -> k s s'))
        (fun s' -> k s s') states (fun w ->
        let b = keep w in
        (match b with
         | True -> real_plus_zero (k s w)
         | False -> kv_plus_zero_l (k s w))))
      (krow s))

(** val kv_tail_one_minus :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> bool) ->
    'a1 -> real_eq **)

let kv_tail_one_minus states k krow keep s =
  let hzt = kv_ZK_plus_tail states k krow keep s in
  real_eq_sym (real_minus_r real_one (z_keep states k keep s))
    (tail_row states k keep s)
    (real_eq_trans (real_minus_r real_one (z_keep states k keep s))
      (real_minus_r
        (real_plus (z_keep states k keep s) (tail_row states k keep s))
        (z_keep states k keep s))
      (tail_row states k keep s)
      (real_eq_trans (real_plus real_one (real_opp (z_keep states k keep s)))
        (real_plus
          (real_plus (z_keep states k keep s) (tail_row states k keep s))
          (real_opp (z_keep states k keep s)))
        (real_plus
          (real_plus (z_keep states k keep s) (tail_row states k keep s))
          (real_opp (z_keep states k keep s)))
        (RealSetoid.real_eq_plus_compat real_one
          (real_opp (z_keep states k keep s))
          (real_plus (z_keep states k keep s) (tail_row states k keep s))
          (real_opp (z_keep states k keep s))
          (real_eq_sym
            (real_plus (z_keep states k keep s) (tail_row states k keep s))
            real_one hzt)
          (real_eq_refl (real_opp (z_keep states k keep s))))
        (real_eq_refl
          (real_plus
            (real_plus (z_keep states k keep s) (tail_row states k keep s))
            (real_opp (z_keep states k keep s)))))
      (let hs1 =
         real_eq_sym
           (real_plus (z_keep states k keep s)
             (real_plus (tail_row states k keep s)
               (real_opp (z_keep states k keep s))))
           (real_plus
             (real_plus (z_keep states k keep s) (tail_row states k keep s))
             (real_opp (z_keep states k keep s)))
           (real_plus_assoc (z_keep states k keep s)
             (tail_row states k keep s) (real_opp (z_keep states k keep s)))
       in
       let hs2 =
         RealSetoid.real_eq_plus_compat (z_keep states k keep s)
           (real_plus (tail_row states k keep s)
             (real_opp (z_keep states k keep s)))
           (z_keep states k keep s)
           (real_plus (real_opp (z_keep states k keep s))
             (tail_row states k keep s))
           (real_eq_refl (z_keep states k keep s))
           (real_plus_comm (tail_row states k keep s)
             (real_opp (z_keep states k keep s)))
       in
       let hs3 =
         real_plus_assoc (z_keep states k keep s)
           (real_opp (z_keep states k keep s)) (tail_row states k keep s)
       in
       let hs4 =
         RealSetoid.real_eq_plus_compat
           (real_plus (z_keep states k keep s)
             (real_opp (z_keep states k keep s)))
           (tail_row states k keep s) real_zero (tail_row states k keep s)
           (real_plus_opp (z_keep states k keep s))
           (real_eq_refl (tail_row states k keep s))
       in
       real_eq_trans
         (real_plus
           (real_plus (z_keep states k keep s) (tail_row states k keep s))
           (real_opp (z_keep states k keep s)))
         (real_plus (z_keep states k keep s)
           (real_plus (tail_row states k keep s)
             (real_opp (z_keep states k keep s))))
         (tail_row states k keep s) hs1
         (real_eq_trans
           (real_plus (z_keep states k keep s)
             (real_plus (tail_row states k keep s)
               (real_opp (z_keep states k keep s))))
           (real_plus (z_keep states k keep s)
             (real_plus (real_opp (z_keep states k keep s))
               (tail_row states k keep s)))
           (tail_row states k keep s) hs2
           (real_eq_trans
             (real_plus (z_keep states k keep s)
               (real_plus (real_opp (z_keep states k keep s))
                 (tail_row states k keep s)))
             (real_plus
               (real_plus (z_keep states k keep s)
                 (real_opp (z_keep states k keep s)))
               (tail_row states k keep s))
             (tail_row states k keep s) hs3
             (real_eq_trans
               (real_plus
                 (real_plus (z_keep states k keep s)
                   (real_opp (z_keep states k keep s)))
                 (tail_row states k keep s))
               (real_plus real_zero (tail_row states k keep s))
               (tail_row states k keep s) hs4
               (kv_plus_zero_l (tail_row states k keep s)))))))

(** val kv_ZK_le_one :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
    real_lt) -> ('a1 -> bool) -> 'a1 -> real_le **)

let kv_ZK_le_one states k krow kpos keep s =
  real_le_trans (z_keep states k keep s)
    (real_list_sum (fun s' -> k s s') states) real_one
    (real_list_sum_le (fun s' ->
      match keep s' with
      | True -> k s s'
      | False -> real_zero) (fun s' -> k s s') states (fun w ->
      let b = keep w in
      (match b with
       | True -> real_le_refl (k s w)
       | False -> real_le_from_lt_aux real_zero (k s w) (kpos s w))))
    (RealSetoid.real_eq_le (real_list_sum (fun s' -> k s s') states) real_one
      (krow s))

(** val kv_invZ_ge_one :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
    real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1
    -> real_le **)

let kv_invZ_ge_one states k krow kpos keep keep_nonempty s =
  RealSetoid.real_le_id_l real_one (real_inv_pos real_one real_lt_zero_one)
    (invZK states k kpos keep keep_nonempty s)
    (real_eq_sym (real_inv_pos real_one real_lt_zero_one) real_one
      (real_eq_trans (real_inv_pos real_one real_lt_zero_one)
        (real_mult real_one (real_inv_pos real_one real_lt_zero_one))
        real_one
        (real_eq_sym
          (real_mult real_one (real_inv_pos real_one real_lt_zero_one))
          (real_inv_pos real_one real_lt_zero_one)
          (kv_one_mult_l (real_inv_pos real_one real_lt_zero_one)))
        (real_inv_pos_correct real_one real_lt_zero_one)))
    (real_inv_pos_le_compat (z_keep states k keep s) real_one
      (z_keep_pos states k kpos keep keep_nonempty s) real_lt_zero_one
      (kv_ZK_le_one states k krow kpos keep s))

(** val kv_K_le_Kev_scaled :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
    real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1
    -> 'a1 -> real_le **)

let kv_K_le_Kev_scaled states k krow kpos keep keep_nonempty s s' =
  real_le_trans (k s s') (real_mult (k s s') real_one)
    (real_mult (k s s') (invZK states k kpos keep keep_nonempty s))
    (RealSetoid.real_eq_le (k s s') (real_mult (k s s') real_one)
      (real_eq_sym (real_mult (k s s') real_one) (k s s')
        (real_mult_one (k s s'))))
    (real_le_mult_compat_l_aux real_one
      (invZK states k kpos keep keep_nonempty s) (k s s') (kpos s s')
      (kv_invZ_ge_one states k krow kpos keep keep_nonempty s))

(** val kv_summand_eq :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
    bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> 'a1 -> real_eq **)

let kv_summand_eq states k kpos keep keep_nonempty s w =
  let b = keep w in
  (match b with
   | True ->
     real_eq_refl
       (real_mult (k s w)
         (real_inv_pos (z_keep states k keep s)
           (z_keep_pos states k kpos keep keep_nonempty s)))
   | False ->
     real_eq_sym
       (real_mult real_zero
         (real_inv_pos (z_keep states k keep s)
           (z_keep_pos states k kpos keep keep_nonempty s)))
       real_zero
       (real_eq_trans
         (real_mult real_zero
           (real_inv_pos (z_keep states k keep s)
             (z_keep_pos states k kpos keep keep_nonempty s)))
         (real_mult
           (real_inv_pos (z_keep states k keep s)
             (z_keep_pos states k kpos keep keep_nonempty s))
           real_zero)
         real_zero
         (real_mult_comm real_zero
           (real_inv_pos (z_keep states k keep s)
             (z_keep_pos states k kpos keep keep_nonempty s)))
         (real_mult_zero
           (real_inv_pos (z_keep states k keep s)
             (z_keep_pos states k kpos keep keep_nonempty s)))))

(** val kv_summand_scaled :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
    bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> 'a1 -> real_eq **)

let kv_summand_scaled states k kpos keep keep_nonempty s w =
  let b = keep w in
  (match b with
   | True ->
     real_eq_trans
       (real_minus_r
         (real_mult (k s w)
           (real_inv_pos (z_keep states k keep s)
             (z_keep_pos states k kpos keep keep_nonempty s)))
         (k s w))
       (real_plus
         (real_mult (k s w)
           (real_inv_pos (z_keep states k keep s)
             (z_keep_pos states k kpos keep keep_nonempty s)))
         (real_opp (k s w)))
       (real_mult (k s w)
         (real_minus_r (invZK states k kpos keep keep_nonempty s) real_one))
       (real_eq_refl
         (real_plus
           (real_mult (k s w)
             (real_inv_pos (z_keep states k keep s)
               (z_keep_pos states k kpos keep keep_nonempty s)))
           (real_opp (k s w))))
       (real_eq_trans
         (real_plus
           (real_mult (k s w)
             (real_inv_pos (z_keep states k keep s)
               (z_keep_pos states k kpos keep keep_nonempty s)))
           (real_opp (k s w)))
         (real_plus
           (real_mult (k s w)
             (real_inv_pos (z_keep states k keep s)
               (z_keep_pos states k kpos keep keep_nonempty s)))
           (real_mult (k s w) (real_opp real_one)))
         (real_mult (k s w)
           (real_minus_r (invZK states k kpos keep keep_nonempty s) real_one))
         (RealSetoid.real_eq_plus_compat
           (real_mult (k s w)
             (real_inv_pos (z_keep states k keep s)
               (z_keep_pos states k kpos keep keep_nonempty s)))
           (real_opp (k s w))
           (real_mult (k s w)
             (real_inv_pos (z_keep states k keep s)
               (z_keep_pos states k kpos keep keep_nonempty s)))
           (real_mult (k s w) (real_opp real_one))
           (real_eq_refl
             (real_mult (k s w)
               (real_inv_pos (z_keep states k keep s)
                 (z_keep_pos states k kpos keep keep_nonempty s))))
           (real_eq_trans (real_opp (k s w))
             (real_opp (real_mult (k s w) real_one))
             (real_mult (k s w) (real_opp real_one))
             (RealSetoid.real_eq_opp_compat (k s w)
               (real_mult (k s w) real_one)
               (real_eq_sym (real_mult (k s w) real_one) (k s w)
                 (real_mult_one (k s w))))
             (real_opp_mult (k s w) real_one)))
         (real_eq_sym
           (real_mult (k s w)
             (real_minus_r (invZK states k kpos keep keep_nonempty s)
               real_one))
           (real_plus
             (real_mult (k s w)
               (real_inv_pos (z_keep states k keep s)
                 (z_keep_pos states k kpos keep keep_nonempty s)))
             (real_mult (k s w) (real_opp real_one)))
           (real_distrib (k s w)
             (real_inv_pos (z_keep states k keep s)
               (z_keep_pos states k kpos keep keep_nonempty s))
             (real_opp real_one))))
   | False ->
     real_eq_sym
       (real_mult real_zero
         (real_minus_r (invZK states k kpos keep keep_nonempty s) real_one))
       real_zero
       (real_eq_trans
         (real_mult real_zero
           (real_minus_r (invZK states k kpos keep keep_nonempty s) real_one))
         (real_mult
           (real_minus_r (invZK states k kpos keep keep_nonempty s) real_one)
           real_zero)
         real_zero
         (real_mult_comm real_zero
           (real_minus_r (invZK states k kpos keep keep_nonempty s) real_one))
         (real_mult_zero
           (real_minus_r (invZK states k kpos keep keep_nonempty s) real_one))))

(** val kv_kev_row_one :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
    bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> real_eq **)

let kv_kev_row_one states k kpos keep keep_nonempty s =
  real_eq_trans
    (real_list_sum (fun w ->
      match keep w with
      | True ->
        real_mult (k s w)
          (real_inv_pos (z_keep states k keep s)
            (z_keep_pos states k kpos keep keep_nonempty s))
      | False -> real_zero) states)
    (real_mult
      (real_inv_pos (z_keep states k keep s)
        (z_keep_pos states k kpos keep keep_nonempty s))
      (z_keep states k keep s))
    real_one
    (real_eq_trans
      (real_list_sum (fun w ->
        match keep w with
        | True ->
          real_mult (k s w)
            (real_inv_pos (z_keep states k keep s)
              (z_keep_pos states k kpos keep keep_nonempty s))
        | False -> real_zero) states)
      (real_list_sum (fun w ->
        real_mult (match keep w with
                   | True -> k s w
                   | False -> real_zero)
          (real_inv_pos (z_keep states k keep s)
            (z_keep_pos states k kpos keep keep_nonempty s)))
        states)
      (real_mult
        (real_inv_pos (z_keep states k keep s)
          (z_keep_pos states k kpos keep keep_nonempty s))
        (real_list_sum (fun w ->
          match keep w with
          | True -> k s w
          | False -> real_zero) states))
      (real_list_sum_ext (fun w ->
        match keep w with
        | True ->
          real_mult (k s w)
            (real_inv_pos (z_keep states k keep s)
              (z_keep_pos states k kpos keep keep_nonempty s))
        | False -> real_zero) (fun w ->
        real_mult (match keep w with
                   | True -> k s w
                   | False -> real_zero)
          (real_inv_pos (z_keep states k keep s)
            (z_keep_pos states k kpos keep keep_nonempty s)))
        states (kv_summand_eq states k kpos keep keep_nonempty s))
      (real_list_sum_linear_r
        (real_inv_pos (z_keep states k keep s)
          (z_keep_pos states k kpos keep keep_nonempty s))
        (fun w -> match keep w with
                  | True -> k s w
                  | False -> real_zero)
        states))
    (real_eq_trans
      (real_mult
        (real_inv_pos (z_keep states k keep s)
          (z_keep_pos states k kpos keep keep_nonempty s))
        (z_keep states k keep s))
      (real_mult (z_keep states k keep s)
        (real_inv_pos (z_keep states k keep s)
          (z_keep_pos states k kpos keep keep_nonempty s)))
      real_one
      (real_mult_comm
        (real_inv_pos (z_keep states k keep s)
          (z_keep_pos states k kpos keep keep_nonempty s))
        (z_keep states k keep s))
      (real_inv_pos_correct (z_keep states k keep s)
        (z_keep_pos states k kpos keep keep_nonempty s)))

(** val kv_gsum_scaled :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
    bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> real_eq **)

let kv_gsum_scaled states k kpos keep keep_nonempty s =
  real_eq_trans
    (real_list_sum (fun s' ->
      match keep s' with
      | True ->
        real_minus_r (k_ev states k kpos keep keep_nonempty s s') (k s s')
      | False -> real_zero) states)
    (real_list_sum (fun w ->
      real_mult (match keep w with
                 | True -> k s w
                 | False -> real_zero)
        (real_minus_r (invZK states k kpos keep keep_nonempty s) real_one))
      states)
    (real_mult
      (real_minus_r (invZK states k kpos keep keep_nonempty s) real_one)
      (z_keep states k keep s))
    (real_list_sum_ext (fun s' ->
      match keep s' with
      | True ->
        real_minus_r (k_ev states k kpos keep keep_nonempty s s') (k s s')
      | False -> real_zero) (fun w ->
      real_mult (match keep w with
                 | True -> k s w
                 | False -> real_zero)
        (real_minus_r (invZK states k kpos keep keep_nonempty s) real_one))
      states (fun w ->
      kv_summand_scaled states k kpos keep keep_nonempty s w))
    (real_list_sum_linear_r
      (real_minus_r (invZK states k kpos keep keep_nonempty s) real_one)
      (fun w -> match keep w with
                | True -> k s w
                | False -> real_zero)
      states)

(** val kv_scaledZ_tail :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
    real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1
    -> real_eq **)

let kv_scaledZ_tail states k krow kpos keep keep_nonempty s =
  real_eq_trans
    (real_mult
      (real_minus_r (invZK states k kpos keep keep_nonempty s) real_one)
      (z_keep states k keep s))
    (real_minus_r real_one (z_keep states k keep s))
    (tail_row states k keep s)
    (real_eq_trans
      (real_mult
        (real_minus_r (invZK states k kpos keep keep_nonempty s) real_one)
        (z_keep states k keep s))
      (real_plus
        (real_mult (invZK states k kpos keep keep_nonempty s)
          (z_keep states k keep s))
        (real_mult (real_opp real_one) (z_keep states k keep s)))
      (real_minus_r real_one (z_keep states k keep s))
      (kv_distrib_r (invZK states k kpos keep keep_nonempty s)
        (real_opp real_one) (z_keep states k keep s))
      (RealSetoid.real_eq_plus_compat
        (real_mult (invZK states k kpos keep keep_nonempty s)
          (z_keep states k keep s))
        (real_mult (real_opp real_one) (z_keep states k keep s)) real_one
        (real_opp (z_keep states k keep s))
        (real_eq_trans
          (real_mult (invZK states k kpos keep keep_nonempty s)
            (z_keep states k keep s))
          (real_mult (z_keep states k keep s)
            (invZK states k kpos keep keep_nonempty s))
          real_one
          (real_mult_comm (invZK states k kpos keep keep_nonempty s)
            (z_keep states k keep s))
          (real_inv_pos_correct (z_keep states k keep s)
            (z_keep_pos states k kpos keep keep_nonempty s)))
        (real_eq_trans
          (real_mult (real_opp real_one) (z_keep states k keep s))
          (real_opp (real_mult real_one (z_keep states k keep s)))
          (real_opp (z_keep states k keep s))
          (real_eq_sym
            (real_opp (real_mult real_one (z_keep states k keep s)))
            (real_mult (real_opp real_one) (z_keep states k keep s))
            (real_opp_mult_r real_one (z_keep states k keep s)))
          (RealSetoid.real_eq_opp_compat
            (real_mult real_one (z_keep states k keep s))
            (z_keep states k keep s) (kv_one_mult_l (z_keep states k keep s))))))
    (real_eq_sym (tail_row states k keep s)
      (real_minus_r real_one (z_keep states k keep s))
      (kv_tail_one_minus states k krow keep s))

(** val kv_tvrow_pointwise :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
    real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1
    -> 'a1 -> real_eq **)

let kv_tvrow_pointwise states k krow kpos keep keep_nonempty s w =
  let b = keep w in
  (match b with
   | True ->
     real_abs_minus_r_nonneg_aux (k s w)
       (real_mult (k s w)
         (real_inv_pos (z_keep states k keep s)
           (z_keep_pos states k kpos keep keep_nonempty s)))
       (kv_K_le_Kev_scaled states k krow kpos keep keep_nonempty s w)
   | False ->
     real_eq_trans (real_abs (real_plus (k s w) (real_opp real_zero)))
       (real_abs (k s w)) (k s w)
       (real_abs_eq_compat (real_plus (k s w) (real_opp real_zero)) (k s w)
         (real_eq_trans (real_plus (k s w) (real_opp real_zero))
           (real_plus (k s w) real_zero) (k s w)
           (RealSetoid.real_eq_plus_compat (k s w) (real_opp real_zero)
             (k s w) real_zero (real_eq_refl (k s w)) real_opp_zero)
           (real_plus_zero (k s w))))
       (kv_abs_nonneg_id (k s w)
         (real_le_from_lt_aux real_zero (k s w) (kpos s w))))

(** val kv_tvrow_split :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
    real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1
    -> real_eq **)

let kv_tvrow_split states k krow kpos keep keep_nonempty s =
  real_eq_trans
    (real_list_sum (fun s' ->
      real_abs
        (real_minus_r (k s s') (k_ev states k kpos keep keep_nonempty s s')))
      states)
    (real_plus
      (real_list_sum (fun w ->
        match keep w with
        | True ->
          real_minus_r (k_ev states k kpos keep keep_nonempty s w) (k s w)
        | False -> real_zero) states)
      (real_list_sum (fun w ->
        match keep w with
        | True -> real_zero
        | False -> k s w) states))
    (real_plus
      (real_list_sum (fun s' ->
        match keep s' with
        | True ->
          real_minus_r (k_ev states k kpos keep keep_nonempty s s') (k s s')
        | False -> real_zero) states)
      (tail_row states k keep s))
    (real_eq_trans
      (real_list_sum (fun s' ->
        real_abs
          (real_minus_r (k s s') (k_ev states k kpos keep keep_nonempty s s')))
        states)
      (real_list_sum (fun w ->
        match keep w with
        | True ->
          real_minus_r (k_ev states k kpos keep keep_nonempty s w) (k s w)
        | False -> k s w) states)
      (real_plus
        (real_list_sum (fun w ->
          match keep w with
          | True ->
            real_minus_r (k_ev states k kpos keep keep_nonempty s w) (k s w)
          | False -> real_zero) states)
        (real_list_sum (fun w ->
          match keep w with
          | True -> real_zero
          | False -> k s w) states))
      (real_list_sum_ext (fun s' ->
        real_abs
          (real_minus_r (k s s') (k_ev states k kpos keep keep_nonempty s s')))
        (fun w ->
        match keep w with
        | True ->
          real_minus_r (k_ev states k kpos keep keep_nonempty s w) (k s w)
        | False -> k s w) states
        (kv_tvrow_pointwise states k krow kpos keep keep_nonempty s))
      (real_eq_trans
        (real_list_sum (fun w ->
          match keep w with
          | True ->
            real_minus_r (k_ev states k kpos keep keep_nonempty s w) (k s w)
          | False -> k s w) states)
        (real_list_sum (fun w ->
          real_plus
            (match keep w with
             | True ->
               real_minus_r (k_ev states k kpos keep keep_nonempty s w)
                 (k s w)
             | False -> real_zero)
            (match keep w with
             | True -> real_zero
             | False -> k s w))
          states)
        (real_plus
          (real_list_sum (fun w ->
            match keep w with
            | True ->
              real_minus_r (k_ev states k kpos keep keep_nonempty s w) (k s w)
            | False -> real_zero) states)
          (real_list_sum (fun w ->
            match keep w with
            | True -> real_zero
            | False -> k s w) states))
        (real_list_sum_ext (fun w ->
          match keep w with
          | True ->
            real_minus_r (k_ev states k kpos keep keep_nonempty s w) (k s w)
          | False -> k s w) (fun w ->
          real_plus
            (match keep w with
             | True ->
               real_minus_r (k_ev states k kpos keep keep_nonempty s w)
                 (k s w)
             | False -> real_zero)
            (match keep w with
             | True -> real_zero
             | False -> k s w))
          states (fun w ->
          let b = keep w in
          (match b with
           | True ->
             real_eq_sym
               (real_plus
                 (real_minus_r (k_ev states k kpos keep keep_nonempty s w)
                   (k s w))
                 real_zero)
               (real_minus_r (k_ev states k kpos keep keep_nonempty s w)
                 (k s w))
               (real_plus_zero
                 (real_minus_r (k_ev states k kpos keep keep_nonempty s w)
                   (k s w)))
           | False ->
             real_eq_sym (real_plus real_zero (k s w)) (k s w)
               (kv_plus_zero_l (k s w)))))
        (real_list_sum_add (fun w ->
          match keep w with
          | True ->
            real_minus_r (k_ev states k kpos keep keep_nonempty s w) (k s w)
          | False -> real_zero) (fun w ->
          match keep w with
          | True -> real_zero
          | False -> k s w) states)))
    (real_eq_refl
      (real_plus
        (real_list_sum (fun s' ->
          match keep s' with
          | True ->
            real_minus_r (k_ev states k kpos keep keep_nonempty s s') (k s s')
          | False -> real_zero) states)
        (tail_row states k keep s)))

(** val kev_row_tv_exact :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
    real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1
    -> real_eq **)

let kev_row_tv_exact states k krow kpos keep keep_nonempty s =
  real_eq_trans (tv_row states k kpos keep keep_nonempty s)
    (real_plus
      (real_list_sum (fun s' ->
        match keep s' with
        | True ->
          real_minus_r (k_ev states k kpos keep keep_nonempty s s') (k s s')
        | False -> real_zero) states)
      (tail_row states k keep s))
    (real_plus (tail_row states k keep s) (tail_row states k keep s))
    (kv_tvrow_split states k krow kpos keep keep_nonempty s)
    (RealSetoid.real_eq_plus_compat
      (real_list_sum (fun s' ->
        match keep s' with
        | True ->
          real_minus_r (k_ev states k kpos keep keep_nonempty s s') (k s s')
        | False -> real_zero) states)
      (tail_row states k keep s) (tail_row states k keep s)
      (tail_row states k keep s)
      (real_eq_trans
        (real_list_sum (fun s' ->
          match keep s' with
          | True ->
            real_minus_r (k_ev states k kpos keep keep_nonempty s s') (k s s')
          | False -> real_zero) states)
        (real_mult
          (real_minus_r (invZK states k kpos keep keep_nonempty s) real_one)
          (z_keep states k keep s))
        (tail_row states k keep s)
        (kv_gsum_scaled states k kpos keep keep_nonempty s)
        (kv_scaledZ_tail states k krow kpos keep keep_nonempty s))
      (real_eq_refl (tail_row states k keep s)))

(** val kev_row_tv_bound :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
    real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1
    -> real_le **)

let kev_row_tv_bound states k krow kpos keep keep_nonempty s =
  RealSetoid.real_eq_le (tv_row states k kpos keep keep_nonempty s)
    (real_plus (tail_row states k keep s) (tail_row states k keep s))
    (kev_row_tv_exact states k krow kpos keep keep_nonempty s)

(** val kev_row_tv_one_minus_Z :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 ->
    real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1
    -> real_eq **)

let kev_row_tv_one_minus_Z states k krow kpos keep keep_nonempty s =
  real_eq_trans (tv_row states k kpos keep keep_nonempty s)
    (real_mult (real_plus real_one real_one) (tail_row states k keep s))
    (real_mult (real_plus real_one real_one)
      (real_minus_r real_one (z_keep states k keep s)))
    (real_eq_trans (tv_row states k kpos keep keep_nonempty s)
      (real_plus (tail_row states k keep s) (tail_row states k keep s))
      (real_mult (real_plus real_one real_one) (tail_row states k keep s))
      (kev_row_tv_exact states k krow kpos keep keep_nonempty s)
      (kv_plus_self_two (tail_row states k keep s)))
    (RealSetoid.real_eq_mult_compat (real_plus real_one real_one)
      (tail_row states k keep s) (real_plus real_one real_one)
      (real_minus_r real_one (z_keep states k keep s))
      (real_eq_refl (real_plus real_one real_one))
      (kv_tail_one_minus states k krow keep s))

(** val kv_lstep_minus_pt2 :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real) -> ('a1 -> real) -> 'a1
    -> real_eq **)

let kv_lstep_minus_pt2 states p mu nu s' =
  real_eq_trans
    (real_plus (real_list_sum (fun s -> real_mult (mu s) (p s s')) states)
      (real_opp (real_list_sum (fun s -> real_mult (nu s) (p s s')) states)))
    (real_list_sum (fun s ->
      real_plus (real_mult (mu s) (p s s'))
        (real_opp (real_mult (nu s) (p s s'))))
      states)
    (real_list_sum (fun s ->
      real_mult (real_plus (mu s) (real_opp (nu s))) (p s s')) states)
    (real_eq_trans
      (real_plus (real_list_sum (fun s -> real_mult (mu s) (p s s')) states)
        (real_opp (real_list_sum (fun s -> real_mult (nu s) (p s s')) states)))
      (real_plus (real_list_sum (fun s -> real_mult (mu s) (p s s')) states)
        (real_list_sum (fun s -> real_opp (real_mult (nu s) (p s s'))) states))
      (real_list_sum (fun s ->
        real_plus (real_mult (mu s) (p s s'))
          (real_opp (real_mult (nu s) (p s s'))))
        states)
      (RealSetoid.real_eq_plus_compat
        (real_list_sum (fun s -> real_mult (mu s) (p s s')) states)
        (real_opp (real_list_sum (fun s -> real_mult (nu s) (p s s')) states))
        (real_list_sum (fun s -> real_mult (mu s) (p s s')) states)
        (real_list_sum (fun s -> real_opp (real_mult (nu s) (p s s'))) states)
        (real_eq_refl
          (real_list_sum (fun s -> real_mult (mu s) (p s s')) states))
        (real_eq_sym
          (real_list_sum (fun w -> real_opp (real_mult (nu w) (p w s')))
            states)
          (real_opp
            (real_list_sum (fun s -> real_mult (nu s) (p s s')) states))
          (real_list_sum_opp (fun s -> real_mult (nu s) (p s s')) states)))
      (real_eq_sym
        (real_list_sum (fun s ->
          real_plus (real_mult (mu s) (p s s'))
            (real_opp (real_mult (nu s) (p s s'))))
          states)
        (real_plus
          (real_list_sum (fun s -> real_mult (mu s) (p s s')) states)
          (real_list_sum (fun s -> real_opp (real_mult (nu s) (p s s')))
            states))
        (real_list_sum_add (fun s -> real_mult (mu s) (p s s')) (fun s ->
          real_opp (real_mult (nu s) (p s s'))) states)))
    (real_list_sum_ext (fun s ->
      real_plus (real_mult (mu s) (p s s'))
        (real_opp (real_mult (nu s) (p s s'))))
      (fun s -> real_mult (real_plus (mu s) (real_opp (nu s))) (p s s'))
      states (fun s ->
      real_eq_trans
        (real_plus (real_mult (mu s) (p s s'))
          (real_opp (real_mult (nu s) (p s s'))))
        (real_plus (real_mult (mu s) (p s s'))
          (real_mult (real_opp (nu s)) (p s s')))
        (real_mult (real_plus (mu s) (real_opp (nu s))) (p s s'))
        (RealSetoid.real_eq_plus_compat (real_mult (mu s) (p s s'))
          (real_opp (real_mult (nu s) (p s s'))) (real_mult (mu s) (p s s'))
          (real_mult (real_opp (nu s)) (p s s'))
          (real_eq_refl (real_mult (mu s) (p s s')))
          (real_opp_mult_r (nu s) (p s s')))
        (real_eq_sym
          (real_mult (real_plus (mu s) (real_opp (nu s))) (p s s'))
          (real_plus (real_mult (mu s) (p s s'))
            (real_mult (real_opp (nu s)) (p s s')))
          (kv_distrib_r (mu s) (real_opp (nu s)) (p s s')))))

(** val kv_lstep2_minus_pt :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real) -> ('a1 -> real)
    -> 'a1 -> real_eq **)

let kv_lstep2_minus_pt states p q0 w s' =
  real_eq_trans
    (real_plus (real_list_sum (fun s -> real_mult (w s) (p s s')) states)
      (real_opp (real_list_sum (fun s -> real_mult (w s) (q0 s s')) states)))
    (real_list_sum (fun s ->
      real_plus (real_mult (w s) (p s s'))
        (real_opp (real_mult (w s) (q0 s s'))))
      states)
    (real_list_sum (fun s ->
      real_mult (w s) (real_plus (p s s') (real_opp (q0 s s')))) states)
    (real_eq_trans
      (real_plus (real_list_sum (fun s -> real_mult (w s) (p s s')) states)
        (real_opp (real_list_sum (fun s -> real_mult (w s) (q0 s s')) states)))
      (real_plus (real_list_sum (fun s -> real_mult (w s) (p s s')) states)
        (real_list_sum (fun s -> real_opp (real_mult (w s) (q0 s s'))) states))
      (real_list_sum (fun s ->
        real_plus (real_mult (w s) (p s s'))
          (real_opp (real_mult (w s) (q0 s s'))))
        states)
      (RealSetoid.real_eq_plus_compat
        (real_list_sum (fun s -> real_mult (w s) (p s s')) states)
        (real_opp (real_list_sum (fun s -> real_mult (w s) (q0 s s')) states))
        (real_list_sum (fun s -> real_mult (w s) (p s s')) states)
        (real_list_sum (fun s -> real_opp (real_mult (w s) (q0 s s'))) states)
        (real_eq_refl
          (real_list_sum (fun s -> real_mult (w s) (p s s')) states))
        (real_eq_sym
          (real_list_sum (fun w0 -> real_opp (real_mult (w w0) (q0 w0 s')))
            states)
          (real_opp
            (real_list_sum (fun s -> real_mult (w s) (q0 s s')) states))
          (real_list_sum_opp (fun s -> real_mult (w s) (q0 s s')) states)))
      (real_eq_sym
        (real_list_sum (fun s ->
          real_plus (real_mult (w s) (p s s'))
            (real_opp (real_mult (w s) (q0 s s'))))
          states)
        (real_plus (real_list_sum (fun s -> real_mult (w s) (p s s')) states)
          (real_list_sum (fun s -> real_opp (real_mult (w s) (q0 s s')))
            states))
        (real_list_sum_add (fun s -> real_mult (w s) (p s s')) (fun s ->
          real_opp (real_mult (w s) (q0 s s'))) states)))
    (real_list_sum_ext (fun s ->
      real_plus (real_mult (w s) (p s s'))
        (real_opp (real_mult (w s) (q0 s s'))))
      (fun s -> real_mult (w s) (real_plus (p s s') (real_opp (q0 s s'))))
      states (fun s ->
      real_eq_trans
        (real_plus (real_mult (w s) (p s s'))
          (real_opp (real_mult (w s) (q0 s s'))))
        (real_plus (real_mult (w s) (p s s'))
          (real_mult (w s) (real_opp (q0 s s'))))
        (real_mult (w s) (real_plus (p s s') (real_opp (q0 s s'))))
        (RealSetoid.real_eq_plus_compat (real_mult (w s) (p s s'))
          (real_opp (real_mult (w s) (q0 s s'))) (real_mult (w s) (p s s'))
          (real_mult (w s) (real_opp (q0 s s')))
          (real_eq_refl (real_mult (w s) (p s s')))
          (real_eq_sym (real_mult (w s) (real_opp (q0 s s')))
            (real_opp (real_mult (w s) (q0 s s')))
            (real_mult_opp_l (w s) (q0 s s'))))
        (real_eq_sym
          (real_mult (w s) (real_plus (p s s') (real_opp (q0 s s'))))
          (real_plus (real_mult (w s) (p s s'))
            (real_mult (w s) (real_opp (q0 s s'))))
          (real_distrib (w s) (p s s') (real_opp (q0 s s'))))))

(** val kv_D_zero : 'a1 list -> ('a1 -> real) -> real_eq **)

let kv_D_zero states mu =
  real_eq_trans
    (real_list_sum (fun x -> real_abs (real_minus_r (mu x) (mu x))) states)
    (real_list_sum (fun _ -> real_zero) states) real_zero
    (real_list_sum_ext (fun x -> real_abs (real_minus_r (mu x) (mu x)))
      (fun _ -> real_zero) states (fun x ->
      real_eq_trans (real_abs (real_minus_r (mu x) (mu x)))
        (real_abs real_zero) real_zero
        (real_abs_eq_compat (real_minus_r (mu x) (mu x)) real_zero
          (real_plus_opp (mu x)))
        real_abs_zero_req))
    (kv_sum_zero_list states)

(** val kv_lstep_norm :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq) -> ('a1 -> real) ->
    real_eq **)

let kv_lstep_norm states p hP mu =
  real_eq_trans
    (real_list_sum (fun s' ->
      real_list_sum (fun s -> real_mult (mu s) (p s s')) states) states)
    (real_list_sum (fun s ->
      real_list_sum (fun s' -> real_mult (mu s) (p s s')) states) states)
    (real_list_sum mu states)
    (kv_swap_list (fun x y -> real_mult (mu x) (p x y)) states states)
    (real_list_sum_ext (fun s ->
      real_list_sum (fun s' -> real_mult (mu s) (p s s')) states) mu states
      (fun s ->
      real_eq_trans
        (real_list_sum (fun s' -> real_mult (mu s) (p s s')) states)
        (real_mult (mu s) (real_list_sum (p s) states)) (mu s)
        (real_list_sum_linear (mu s) (p s) states)
        (real_eq_trans (real_mult (mu s) (real_list_sum (p s) states))
          (real_mult (mu s) real_one) (mu s)
          (RealSetoid.real_eq_mult_compat (mu s) (real_list_sum (p s) states)
            (mu s) real_one (real_eq_refl (mu s)) (hP s))
          (real_mult_one (mu s)))))

(** val kv_lstep_nonneg :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_le) -> ('a1 ->
    real) -> ('a1 -> real_le) -> 'a1 -> real_le **)

let kv_lstep_nonneg states p hP mu hmu s' =
  real_list_sum_nonneg (fun s -> real_mult (mu s) (p s s')) states (fun s ->
    RealSetoid.real_le_id_l real_zero (real_mult real_zero (p s s'))
      (real_mult (mu s) (p s s'))
      (real_eq_sym (real_mult real_zero (p s s')) real_zero
        (real_eq_trans (real_mult real_zero (p s s'))
          (real_mult (p s s') real_zero) real_zero
          (real_mult_comm real_zero (p s s')) (real_mult_zero (p s s'))))
      (real_le_mult_compat_weak real_zero (mu s) (p s s') (hP s s') (hmu s)))

(** val kv_K_ev_nonneg :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
    bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> 'a1 -> 'a1 -> real_le **)

let kv_K_ev_nonneg states k kpos keep keep_nonempty s s' =
  let b = keep s' in
  (match b with
   | True ->
     RealSetoid.real_le_id_l real_zero
       (real_mult real_zero
         (real_inv_pos (z_keep states k keep s)
           (z_keep_pos states k kpos keep keep_nonempty s)))
       (real_mult (k s s')
         (real_inv_pos (z_keep states k keep s)
           (z_keep_pos states k kpos keep keep_nonempty s)))
       (real_eq_sym
         (real_mult real_zero
           (real_inv_pos (z_keep states k keep s)
             (z_keep_pos states k kpos keep keep_nonempty s)))
         real_zero
         (real_eq_trans
           (real_mult real_zero
             (real_inv_pos (z_keep states k keep s)
               (z_keep_pos states k kpos keep keep_nonempty s)))
           (real_mult
             (real_inv_pos (z_keep states k keep s)
               (z_keep_pos states k kpos keep keep_nonempty s))
             real_zero)
           real_zero
           (real_mult_comm real_zero
             (real_inv_pos (z_keep states k keep s)
               (z_keep_pos states k kpos keep keep_nonempty s)))
           (real_mult_zero
             (real_inv_pos (z_keep states k keep s)
               (z_keep_pos states k kpos keep keep_nonempty s)))))
       (real_le_mult_compat_weak real_zero (k s s')
         (real_inv_pos (z_keep states k keep s)
           (z_keep_pos states k kpos keep keep_nonempty s))
         (real_le_from_lt_aux real_zero
           (real_inv_pos (z_keep states k keep s)
             (z_keep_pos states k kpos keep keep_nonempty s))
           (real_inv_pos_pos (z_keep states k keep s)
             (z_keep_pos states k kpos keep keep_nonempty s)))
         (real_le_from_lt_aux real_zero (k s s') (kpos s s')))
   | False -> real_le_refl real_zero)

(** val kv_kev_iter_norm :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
    bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> nat -> ('a1 -> real) ->
    real_eq -> real_eq **)

let rec kv_kev_iter_norm states k kpos keep keep_nonempty n mu hmu =
  match n with
  | O -> hmu
  | S n0 ->
    real_eq_trans
      (real_list_sum (fun s' ->
        lstep states (k_ev states k kpos keep keep_nonempty)
          (kev_iter states k kpos keep keep_nonempty n0 mu) s')
        states)
      (real_list_sum (kev_iter states k kpos keep keep_nonempty n0 mu) states)
      real_one
      (kv_lstep_norm states (k_ev states k kpos keep keep_nonempty) (fun s ->
        kv_kev_row_one states k kpos keep keep_nonempty s)
        (kev_iter states k kpos keep keep_nonempty n0 mu))
      (kv_kev_iter_norm states k kpos keep keep_nonempty n0 mu hmu)

(** val kv_kev_iter_nonneg :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
    bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> nat -> ('a1 -> real) ->
    ('a1 -> real_le) -> 'a1 -> real_le **)

let rec kv_kev_iter_nonneg states k kpos keep keep_nonempty n mu hmu =
  match n with
  | O -> hmu
  | S n0 ->
    (fun s' ->
      kv_lstep_nonneg states (k_ev states k kpos keep keep_nonempty)
        (kv_K_ev_nonneg states k kpos keep keep_nonempty)
        (kev_iter states k kpos keep keep_nonempty n0 mu)
        (kv_kev_iter_nonneg states k kpos keep keep_nonempty n0 mu hmu) s')

(** val kv_dsum_abs_eq :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_le) -> ('a1 ->
    real_eq) -> ('a1 -> real) -> ('a1 -> real) -> real_eq **)

let kv_dsum_abs_eq states p hnn hP mu nu =
  real_eq_trans
    (real_list_sum (fun s' ->
      real_list_sum (fun s ->
        real_abs (real_mult (real_minus_r (mu s) (nu s)) (p s s'))) states)
      states)
    (real_list_sum (fun s ->
      real_list_sum (fun s' ->
        real_abs (real_mult (real_minus_r (mu s) (nu s)) (p s s'))) states)
      states)
    (real_list_sum (fun x -> real_abs (real_minus_r (mu x) (nu x))) states)
    (kv_swap_list (fun x y ->
      real_abs (real_mult (real_minus_r (mu x) (nu x)) (p x y))) states
      states)
    (real_list_sum_ext (fun s ->
      real_list_sum (fun s' ->
        real_abs (real_mult (real_minus_r (mu s) (nu s)) (p s s'))) states)
      (fun x -> real_abs (real_minus_r (mu x) (nu x))) states (fun s ->
      real_eq_trans
        (real_list_sum (fun s' ->
          real_abs (real_mult (real_minus_r (mu s) (nu s)) (p s s'))) states)
        (real_mult (real_abs (real_minus_r (mu s) (nu s)))
          (real_list_sum (p s) states))
        (real_abs (real_minus_r (mu s) (nu s)))
        (real_eq_trans
          (real_list_sum (fun s' ->
            real_abs (real_mult (real_minus_r (mu s) (nu s)) (p s s')))
            states)
          (real_list_sum (fun s' ->
            real_mult (real_abs (real_minus_r (mu s) (nu s))) (p s s'))
            states)
          (real_mult (real_abs (real_minus_r (mu s) (nu s)))
            (real_list_sum (p s) states))
          (real_list_sum_ext (fun s' ->
            real_abs (real_mult (real_minus_r (mu s) (nu s)) (p s s')))
            (fun s' ->
            real_mult (real_abs (real_minus_r (mu s) (nu s))) (p s s'))
            states (fun s' ->
            real_eq_trans
              (real_abs (real_mult (real_minus_r (mu s) (nu s)) (p s s')))
              (real_mult (real_abs (real_minus_r (mu s) (nu s)))
                (real_abs (p s s')))
              (real_mult (real_abs (real_minus_r (mu s) (nu s))) (p s s'))
              (real_abs_mult_req (real_minus_r (mu s) (nu s)) (p s s'))
              (RealSetoid.real_eq_mult_compat
                (real_abs (real_minus_r (mu s) (nu s))) (real_abs (p s s'))
                (real_abs (real_minus_r (mu s) (nu s))) (p s s')
                (real_eq_refl (real_abs (real_minus_r (mu s) (nu s))))
                (kv_abs_nonneg_id (p s s') (hnn s s')))))
          (real_list_sum_linear (real_abs (real_minus_r (mu s) (nu s))) 
            (p s) states))
        (real_eq_trans
          (real_mult (real_abs (real_minus_r (mu s) (nu s)))
            (real_list_sum (p s) states))
          (real_mult (real_abs (real_minus_r (mu s) (nu s))) real_one)
          (real_abs (real_minus_r (mu s) (nu s)))
          (RealSetoid.real_eq_mult_compat
            (real_abs (real_minus_r (mu s) (nu s)))
            (real_list_sum (p s) states)
            (real_abs (real_minus_r (mu s) (nu s))) real_one
            (real_eq_refl (real_abs (real_minus_r (mu s) (nu s)))) (hP s))
          (real_mult_one (real_abs (real_minus_r (mu s) (nu s)))))))

(** val kv_nonexpansive :
    'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq)
    -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> ('a1 -> 'a1 ->
    real) -> ('a1 -> real_eq) -> ('a1 -> 'a1 -> real_le) -> ('a1 -> real) ->
    ('a1 -> real) -> real -> real_lt -> real_le **)

let kv_nonexpansive states states_ne k krow keep keep_nonempty p hP hnn mu nu eps heps =
  let hshare =
    kv_share_pos states states_ne k krow keep keep_nonempty eps heps
  in
  real_le_trans
    (real_list_sum (fun s' ->
      real_abs (real_minus_r (lstep states p mu s') (lstep states p nu s')))
      states)
    (real_list_sum (fun s' ->
      real_plus
        (real_list_sum (fun s ->
          real_abs (real_mult (real_minus_r (mu s) (nu s)) (p s s'))) states)
        (real_mult
          (real_inv_pos (real_of_nat (length states))
            (kv_N_pos states states_ne k krow keep keep_nonempty))
          eps))
      states)
    (real_plus
      (real_list_sum (fun x -> real_abs (real_minus_r (mu x) (nu x))) states)
      eps)
    (real_list_sum_le (fun s' ->
      real_abs (real_minus_r (lstep states p mu s') (lstep states p nu s')))
      (fun s' ->
      real_plus
        (real_list_sum (fun s ->
          real_abs (real_mult (real_minus_r (mu s) (nu s)) (p s s'))) states)
        (real_mult
          (real_inv_pos (real_of_nat (length states))
            (kv_N_pos states states_ne k krow keep keep_nonempty))
          eps))
      states (fun s' ->
      real_le_trans
        (real_abs
          (real_minus_r (lstep states p mu s') (lstep states p nu s')))
        (real_abs
          (real_list_sum (fun s ->
            real_mult (real_minus_r (mu s) (nu s)) (p s s')) states))
        (real_plus
          (real_list_sum (fun s ->
            real_abs (real_mult (real_minus_r (mu s) (nu s)) (p s s')))
            states)
          (real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps))
        (Inr
        (real_abs_eq_compat
          (real_minus_r (lstep states p mu s') (lstep states p nu s'))
          (real_list_sum (fun s ->
            real_mult (real_minus_r (mu s) (nu s)) (p s s')) states)
          (kv_lstep_minus_pt2 states p mu nu s')))
        (kv_abs_triangle_list_eps (fun s ->
          real_mult (real_minus_r (mu s) (nu s)) (p s s')) states
          (real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps)
          hshare)))
    (Inr
    (real_eq_trans
      (real_list_sum (fun s' ->
        real_plus
          (real_list_sum (fun s ->
            real_abs (real_mult (real_minus_r (mu s) (nu s)) (p s s')))
            states)
          (real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps))
        states)
      (real_plus
        (real_list_sum (fun s' ->
          real_list_sum (fun s ->
            real_abs (real_mult (real_minus_r (mu s) (nu s)) (p s s'))) states)
          states)
        (real_mult (real_of_nat (length states))
          (real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps)))
      (real_plus
        (real_list_sum (fun x -> real_abs (real_minus_r (mu x) (nu x)))
          states)
        eps)
      (real_eq_trans
        (real_list_sum (fun w ->
          real_plus
            (real_list_sum (fun s0 ->
              real_abs (real_mult (real_minus_r (mu s0) (nu s0)) (p s0 w)))
              states)
            (real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps))
          states)
        (real_plus
          (real_list_sum (fun s ->
            real_list_sum (fun s0 ->
              real_abs (real_mult (real_minus_r (mu s0) (nu s0)) (p s0 s)))
              states)
            states)
          (real_list_sum (fun _ ->
            real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps)
            states))
        (real_plus
          (real_list_sum (fun s ->
            real_list_sum (fun s0 ->
              real_abs (real_mult (real_minus_r (mu s0) (nu s0)) (p s0 s)))
              states)
            states)
          (real_mult (real_of_nat (length states))
            (real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps)))
        (real_list_sum_add (fun s ->
          real_list_sum (fun s0 ->
            real_abs (real_mult (real_minus_r (mu s0) (nu s0)) (p s0 s)))
            states)
          (fun _ ->
          real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps)
          states)
        (RealSetoid.real_eq_plus_compat
          (real_list_sum (fun s ->
            real_list_sum (fun s0 ->
              real_abs (real_mult (real_minus_r (mu s0) (nu s0)) (p s0 s)))
              states)
            states)
          (real_list_sum (fun _ ->
            real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps)
            states)
          (real_list_sum (fun s ->
            real_list_sum (fun s0 ->
              real_abs (real_mult (real_minus_r (mu s0) (nu s0)) (p s0 s)))
              states)
            states)
          (real_mult (real_of_nat (length states))
            (real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps))
          (real_eq_refl
            (real_list_sum (fun s ->
              real_list_sum (fun s0 ->
                real_abs (real_mult (real_minus_r (mu s0) (nu s0)) (p s0 s)))
                states)
              states))
          (kv_sum_const_list
            (real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps)
            states)))
      (RealSetoid.real_eq_plus_compat
        (real_list_sum (fun s' ->
          real_list_sum (fun s ->
            real_abs (real_mult (real_minus_r (mu s) (nu s)) (p s s'))) states)
          states)
        (real_mult (real_of_nat (length states))
          (real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps))
        (real_list_sum (fun x -> real_abs (real_minus_r (mu x) (nu x)))
          states)
        eps (kv_dsum_abs_eq states p hnn hP mu nu)
        (kv_inv_absorb (real_of_nat (length states))
          (kv_N_pos states states_ne k krow keep keep_nonempty) eps))))

(** val kv_minus_split : real -> real -> real -> real_eq **)

let kv_minus_split a b c0 =
  real_eq_sym
    (real_plus (real_plus a (real_opp b)) (real_plus b (real_opp c0)))
    (real_plus a (real_opp c0))
    (real_eq_trans
      (real_plus (real_plus a (real_opp b)) (real_plus b (real_opp c0)))
      (real_plus a (real_plus (real_opp b) (real_plus b (real_opp c0))))
      (real_plus a (real_opp c0))
      (real_eq_sym
        (real_plus a (real_plus (real_opp b) (real_plus b (real_opp c0))))
        (real_plus (real_plus a (real_opp b)) (real_plus b (real_opp c0)))
        (real_plus_assoc a (real_opp b) (real_plus b (real_opp c0))))
      (RealSetoid.real_eq_plus_compat a
        (real_plus (real_opp b) (real_plus b (real_opp c0))) a (real_opp c0)
        (real_eq_refl a)
        (real_eq_trans (real_plus (real_opp b) (real_plus b (real_opp c0)))
          (real_plus (real_plus (real_opp b) b) (real_opp c0)) (real_opp c0)
          (real_plus_assoc (real_opp b) b (real_opp c0))
          (real_eq_trans (real_plus (real_plus (real_opp b) b) (real_opp c0))
            (real_plus real_zero (real_opp c0)) (real_opp c0)
            (RealSetoid.real_eq_plus_compat (real_plus (real_opp b) b)
              (real_opp c0) real_zero (real_opp c0)
              (real_eq_trans (real_plus (real_opp b) b)
                (real_plus b (real_opp b)) real_zero
                (real_plus_comm (real_opp b) b) (real_plus_opp b))
              (real_eq_refl (real_opp c0)))
            (kv_plus_zero_l (real_opp c0))))))

(** val kv_abs_minus_flip : real -> real -> real_eq **)

let kv_abs_minus_flip a b =
  real_eq_trans (real_abs (real_minus_r a b))
    (real_abs (real_opp (real_minus_r a b))) (real_abs (real_minus_r b a))
    (real_eq_sym (real_abs (real_opp (real_minus_r a b)))
      (real_abs (real_minus_r a b)) (real_abs_opp (real_minus_r a b)))
    (real_abs_eq_compat (real_opp (real_minus_r a b)) (real_minus_r b a)
      (real_eq_trans (real_opp (real_plus a (real_opp b)))
        (real_plus (real_opp a) (real_opp (real_opp b)))
        (real_plus b (real_opp a)) (real_opp_plus a (real_opp b))
        (real_eq_trans (real_plus (real_opp a) (real_opp (real_opp b)))
          (real_plus (real_opp a) b) (real_plus b (real_opp a))
          (RealSetoid.real_eq_plus_compat (real_opp a)
            (real_opp (real_opp b)) (real_opp a) b
            (real_eq_refl (real_opp a)) (real_opp_opp b))
          (real_plus_comm (real_opp a) b))))

(** val kv_D_triangle :
    'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq)
    -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> ('a1 -> real)
    -> ('a1 -> real) -> ('a1 -> real) -> real -> real_lt -> real_le **)

let kv_D_triangle states states_ne k krow keep keep_nonempty a b cc eps heps =
  let hshare =
    kv_share_pos states states_ne k krow keep keep_nonempty eps heps
  in
  real_le_trans
    (real_list_sum (fun x -> real_abs (real_minus_r (a x) (cc x))) states)
    (real_list_sum (fun x ->
      real_plus
        (real_plus (real_abs (real_minus_r (a x) (b x)))
          (real_abs (real_minus_r (b x) (cc x))))
        (real_mult
          (real_inv_pos (real_of_nat (length states))
            (kv_N_pos states states_ne k krow keep keep_nonempty))
          eps))
      states)
    (real_plus
      (real_list_sum (fun x -> real_abs (real_minus_r (a x) (b x))) states)
      (real_plus
        (real_list_sum (fun x -> real_abs (real_minus_r (b x) (cc x))) states)
        eps))
    (real_list_sum_le (fun x -> real_abs (real_minus_r (a x) (cc x)))
      (fun x ->
      real_plus
        (real_plus (real_abs (real_minus_r (a x) (b x)))
          (real_abs (real_minus_r (b x) (cc x))))
        (real_mult
          (real_inv_pos (real_of_nat (length states))
            (kv_N_pos states states_ne k krow keep keep_nonempty))
          eps))
      states (fun x ->
      real_le_trans (real_abs (real_minus_r (a x) (cc x)))
        (real_abs
          (real_plus (real_minus_r (a x) (b x)) (real_minus_r (b x) (cc x))))
        (real_plus
          (real_plus (real_abs (real_minus_r (a x) (b x)))
            (real_abs (real_minus_r (b x) (cc x))))
          (real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps))
        (Inr
        (real_abs_eq_compat (real_minus_r (a x) (cc x))
          (real_plus (real_minus_r (a x) (b x)) (real_minus_r (b x) (cc x)))
          (kv_minus_split (a x) (b x) (cc x))))
        (real_abs_triangle_le_eps (real_minus_r (a x) (b x))
          (real_minus_r (b x) (cc x))
          (real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps)
          hshare)))
    (Inr
    (real_eq_trans
      (real_list_sum (fun x ->
        real_plus
          (real_plus (real_abs (real_minus_r (a x) (b x)))
            (real_abs (real_minus_r (b x) (cc x))))
          (real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps))
        states)
      (real_plus
        (real_list_sum (fun x ->
          real_plus (real_abs (real_minus_r (a x) (b x)))
            (real_abs (real_minus_r (b x) (cc x))))
          states)
        (real_mult (real_of_nat (length states))
          (real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps)))
      (real_plus
        (real_list_sum (fun x -> real_abs (real_minus_r (a x) (b x))) states)
        (real_plus
          (real_list_sum (fun x -> real_abs (real_minus_r (b x) (cc x)))
            states)
          eps))
      (real_eq_trans
        (real_list_sum (fun w ->
          real_plus
            (real_plus (real_abs (real_minus_r (a w) (b w)))
              (real_abs (real_minus_r (b w) (cc w))))
            (real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps))
          states)
        (real_plus
          (real_list_sum (fun x ->
            real_plus (real_abs (real_minus_r (a x) (b x)))
              (real_abs (real_minus_r (b x) (cc x))))
            states)
          (real_list_sum (fun _ ->
            real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps)
            states))
        (real_plus
          (real_list_sum (fun x ->
            real_plus (real_abs (real_minus_r (a x) (b x)))
              (real_abs (real_minus_r (b x) (cc x))))
            states)
          (real_mult (real_of_nat (length states))
            (real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps)))
        (real_list_sum_add (fun x ->
          real_plus (real_abs (real_minus_r (a x) (b x)))
            (real_abs (real_minus_r (b x) (cc x))))
          (fun _ ->
          real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps)
          states)
        (RealSetoid.real_eq_plus_compat
          (real_list_sum (fun x ->
            real_plus (real_abs (real_minus_r (a x) (b x)))
              (real_abs (real_minus_r (b x) (cc x))))
            states)
          (real_list_sum (fun _ ->
            real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps)
            states)
          (real_list_sum (fun x ->
            real_plus (real_abs (real_minus_r (a x) (b x)))
              (real_abs (real_minus_r (b x) (cc x))))
            states)
          (real_mult (real_of_nat (length states))
            (real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps))
          (real_eq_refl
            (real_list_sum (fun x ->
              real_plus (real_abs (real_minus_r (a x) (b x)))
                (real_abs (real_minus_r (b x) (cc x))))
              states))
          (kv_sum_const_list
            (real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps)
            states)))
      (real_eq_trans
        (real_plus
          (real_list_sum (fun x ->
            real_plus (real_abs (real_minus_r (a x) (b x)))
              (real_abs (real_minus_r (b x) (cc x))))
            states)
          (real_mult (real_of_nat (length states))
            (real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps)))
        (real_plus
          (real_plus
            (real_list_sum (fun x -> real_abs (real_minus_r (a x) (b x)))
              states)
            (real_list_sum (fun x -> real_abs (real_minus_r (b x) (cc x)))
              states))
          eps)
        (real_plus
          (real_list_sum (fun x -> real_abs (real_minus_r (a x) (b x)))
            states)
          (real_plus
            (real_list_sum (fun x -> real_abs (real_minus_r (b x) (cc x)))
              states)
            eps))
        (RealSetoid.real_eq_plus_compat
          (real_list_sum (fun x ->
            real_plus (real_abs (real_minus_r (a x) (b x)))
              (real_abs (real_minus_r (b x) (cc x))))
            states)
          (real_mult (real_of_nat (length states))
            (real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps))
          (real_plus
            (real_list_sum (fun x -> real_abs (real_minus_r (a x) (b x)))
              states)
            (real_list_sum (fun x -> real_abs (real_minus_r (b x) (cc x)))
              states))
          eps
          (real_list_sum_add (fun x -> real_abs (real_minus_r (a x) (b x)))
            (fun x -> real_abs (real_minus_r (b x) (cc x))) states)
          (kv_inv_absorb (real_of_nat (length states))
            (kv_N_pos states states_ne k krow keep keep_nonempty) eps))
        (real_eq_sym
          (real_plus
            (real_list_sum (fun x -> real_abs (real_minus_r (a x) (b x)))
              states)
            (real_plus
              (real_list_sum (fun x -> real_abs (real_minus_r (b x) (cc x)))
                states)
              eps))
          (real_plus
            (real_plus
              (real_list_sum (fun x -> real_abs (real_minus_r (a x) (b x)))
                states)
              (real_list_sum (fun x -> real_abs (real_minus_r (b x) (cc x)))
                states))
            eps)
          (real_plus_assoc
            (real_list_sum (fun x -> real_abs (real_minus_r (a x) (b x)))
              states)
            (real_list_sum (fun x -> real_abs (real_minus_r (b x) (cc x)))
              states)
            eps)))))

(** val kv_dsum_row_err :
    'a1 list -> ('a1 -> 'a1 -> real) -> ('a1 -> 'a1 -> real_lt) -> ('a1 ->
    bool) -> ('a1, (bool id, 'a1 inT) and0) sigT -> ('a1 -> real) -> ('a1 ->
    real_le) -> real_eq **)

let kv_dsum_row_err states k kpos keep keep_nonempty mu hnn =
  real_eq_trans
    (real_list_sum (fun s' ->
      real_list_sum (fun s ->
        real_abs
          (real_mult (mu s)
            (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
              (k s s'))))
        states)
      states)
    (real_list_sum (fun s ->
      real_list_sum (fun s' ->
        real_abs
          (real_mult (mu s)
            (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
              (k s s'))))
        states)
      states)
    (real_list_sum (fun s ->
      real_mult (mu s) (tv_row states k kpos keep keep_nonempty s)) states)
    (kv_swap_list (fun x y ->
      real_abs
        (real_mult (mu x)
          (real_minus_r (k_ev states k kpos keep keep_nonempty x y) (k x y))))
      states states)
    (real_list_sum_ext (fun s ->
      real_list_sum (fun s' ->
        real_abs
          (real_mult (mu s)
            (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
              (k s s'))))
        states)
      (fun s -> real_mult (mu s) (tv_row states k kpos keep keep_nonempty s))
      states (fun s ->
      real_eq_trans
        (real_list_sum (fun s' ->
          real_abs
            (real_mult (mu s)
              (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
                (k s s'))))
          states)
        (real_list_sum (fun s' ->
          real_mult (mu s)
            (real_abs
              (real_minus_r (k s s')
                (k_ev states k kpos keep keep_nonempty s s'))))
          states)
        (real_mult (mu s) (tv_row states k kpos keep keep_nonempty s))
        (real_list_sum_ext (fun s' ->
          real_abs
            (real_mult (mu s)
              (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
                (k s s'))))
          (fun s' ->
          real_mult (mu s)
            (real_abs
              (real_minus_r (k s s')
                (k_ev states k kpos keep keep_nonempty s s'))))
          states (fun s' ->
          real_eq_trans
            (real_abs
              (real_mult (mu s)
                (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
                  (k s s'))))
            (real_mult (real_abs (mu s))
              (real_abs
                (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
                  (k s s'))))
            (real_mult (mu s)
              (real_abs
                (real_minus_r (k s s')
                  (k_ev states k kpos keep keep_nonempty s s'))))
            (real_abs_mult_req (mu s)
              (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
                (k s s')))
            (RealSetoid.real_eq_mult_compat (real_abs (mu s))
              (real_abs
                (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
                  (k s s')))
              (mu s)
              (real_abs
                (real_minus_r (k s s')
                  (k_ev states k kpos keep keep_nonempty s s')))
              (kv_abs_nonneg_id (mu s) (hnn s))
              (kv_abs_minus_flip (k_ev states k kpos keep keep_nonempty s s')
                (k s s')))))
        (real_list_sum_linear (mu s) (fun w ->
          real_abs
            (real_minus_r (k s w) (k_ev states k kpos keep keep_nonempty s w)))
          states)))

(** val kv_step_drift :
    'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq)
    -> ('a1 -> 'a1 -> real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT)
    and0) sigT -> real -> ('a1 -> real_le) -> ('a1 -> real) -> real ->
    real_lt -> real_eq -> ('a1 -> real_le) -> real_le **)

let kv_step_drift states states_ne k krow kpos keep keep_nonempty c hrow mu eps heps hnorm hnn =
  let hshare =
    kv_share_pos states states_ne k krow keep keep_nonempty eps heps
  in
  real_le_trans
    (real_list_sum (fun s' ->
      real_abs
        (real_minus_r
          (lstep states (k_ev states k kpos keep keep_nonempty) mu s')
          (lstep states k mu s')))
      states)
    (real_list_sum (fun s' ->
      real_plus
        (real_list_sum (fun s ->
          real_abs
            (real_mult (mu s)
              (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
                (k s s'))))
          states)
        (real_mult
          (real_inv_pos (real_of_nat (length states))
            (kv_N_pos states states_ne k krow keep keep_nonempty))
          eps))
      states)
    (real_plus c eps)
    (real_list_sum_le (fun s' ->
      real_abs
        (real_minus_r
          (lstep states (k_ev states k kpos keep keep_nonempty) mu s')
          (lstep states k mu s')))
      (fun s' ->
      real_plus
        (real_list_sum (fun s ->
          real_abs
            (real_mult (mu s)
              (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
                (k s s'))))
          states)
        (real_mult
          (real_inv_pos (real_of_nat (length states))
            (kv_N_pos states states_ne k krow keep keep_nonempty))
          eps))
      states (fun s' ->
      real_le_trans
        (real_abs
          (real_minus_r
            (lstep states (k_ev states k kpos keep keep_nonempty) mu s')
            (lstep states k mu s')))
        (real_abs
          (real_list_sum (fun s ->
            real_mult (mu s)
              (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
                (k s s')))
            states))
        (real_plus
          (real_list_sum (fun s ->
            real_abs
              (real_mult (mu s)
                (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
                  (k s s'))))
            states)
          (real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps))
        (Inr
        (real_abs_eq_compat
          (real_minus_r
            (lstep states (k_ev states k kpos keep keep_nonempty) mu s')
            (lstep states k mu s'))
          (real_list_sum (fun s ->
            real_mult (mu s)
              (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
                (k s s')))
            states)
          (kv_lstep2_minus_pt states (k_ev states k kpos keep keep_nonempty)
            k mu s')))
        (kv_abs_triangle_list_eps (fun s ->
          real_mult (mu s)
            (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
              (k s s')))
          states
          (real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps)
          hshare)))
    (real_le_trans
      (real_list_sum (fun s' ->
        real_plus
          (real_list_sum (fun s ->
            real_abs
              (real_mult (mu s)
                (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
                  (k s s'))))
            states)
          (real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps))
        states)
      (real_plus
        (real_list_sum (fun s ->
          real_mult (mu s) (tv_row states k kpos keep keep_nonempty s))
          states)
        eps)
      (real_plus c eps) (Inr
      (real_eq_trans
        (real_list_sum (fun w ->
          real_plus
            (real_list_sum (fun s ->
              real_abs
                (real_mult (mu s)
                  (real_minus_r (k_ev states k kpos keep keep_nonempty s w)
                    (k s w))))
              states)
            (real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps))
          states)
        (real_plus
          (real_list_sum (fun s' ->
            real_list_sum (fun s ->
              real_abs
                (real_mult (mu s)
                  (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
                    (k s s'))))
              states)
            states)
          (real_list_sum (fun _ ->
            real_mult
              (real_inv_pos (real_of_nat (length states))
                (kv_N_pos states states_ne k krow keep keep_nonempty))
              eps)
            states))
        (real_plus
          (real_list_sum (fun s ->
            real_mult (mu s) (tv_row states k kpos keep keep_nonempty s))
            states)
          eps)
        (real_list_sum_add (fun s' ->
          real_list_sum (fun s ->
            real_abs
              (real_mult (mu s)
                (real_minus_r (k_ev states k kpos keep keep_nonempty s s')
                  (k s s'))))
            states)
          (fun _ ->
          real_mult
            (real_inv_pos (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty))
            eps)
          states)
        (real_eq_trans
          (real_plus
            (real_list_sum (fun s' ->
              real_list_sum (fun s ->
                real_abs
                  (real_mult (mu s)
                    (real_minus_r
                      (k_ev states k kpos keep keep_nonempty s s') (k s s'))))
                states)
              states)
            (real_list_sum (fun _ ->
              real_mult
                (real_inv_pos (real_of_nat (length states))
                  (kv_N_pos states states_ne k krow keep keep_nonempty))
                eps)
              states))
          (real_plus
            (real_list_sum (fun s ->
              real_mult (mu s) (tv_row states k kpos keep keep_nonempty s))
              states)
            (real_mult (real_of_nat (length states))
              (real_mult
                (real_inv_pos (real_of_nat (length states))
                  (kv_N_pos states states_ne k krow keep keep_nonempty))
                eps)))
          (real_plus
            (real_list_sum (fun s ->
              real_mult (mu s) (tv_row states k kpos keep keep_nonempty s))
              states)
            eps)
          (RealSetoid.real_eq_plus_compat
            (real_list_sum (fun s' ->
              real_list_sum (fun s ->
                real_abs
                  (real_mult (mu s)
                    (real_minus_r
                      (k_ev states k kpos keep keep_nonempty s s') (k s s'))))
                states)
              states)
            (real_list_sum (fun _ ->
              real_mult
                (real_inv_pos (real_of_nat (length states))
                  (kv_N_pos states states_ne k krow keep keep_nonempty))
                eps)
              states)
            (real_list_sum (fun s ->
              real_mult (mu s) (tv_row states k kpos keep keep_nonempty s))
              states)
            (real_mult (real_of_nat (length states))
              (real_mult
                (real_inv_pos (real_of_nat (length states))
                  (kv_N_pos states states_ne k krow keep keep_nonempty))
                eps))
            (kv_dsum_row_err states k kpos keep keep_nonempty mu hnn)
            (kv_sum_const_list
              (real_mult
                (real_inv_pos (real_of_nat (length states))
                  (kv_N_pos states states_ne k krow keep keep_nonempty))
                eps)
              states))
          (RealSetoid.real_eq_plus_compat
            (real_list_sum (fun s ->
              real_mult (mu s) (tv_row states k kpos keep keep_nonempty s))
              states)
            (real_mult (real_of_nat (length states))
              (real_mult
                (real_inv_pos (real_of_nat (length states))
                  (kv_N_pos states states_ne k krow keep keep_nonempty))
                eps))
            (real_list_sum (fun s ->
              real_mult (mu s) (tv_row states k kpos keep keep_nonempty s))
              states)
            eps
            (real_eq_refl
              (real_list_sum (fun s ->
                real_mult (mu s) (tv_row states k kpos keep keep_nonempty s))
                states))
            (kv_inv_absorb (real_of_nat (length states))
              (kv_N_pos states states_ne k krow keep keep_nonempty) eps)))))
      (real_le_trans
        (real_plus
          (real_list_sum (fun s ->
            real_mult (mu s) (tv_row states k kpos keep keep_nonempty s))
            states)
          eps)
        (real_plus (real_list_sum (fun s -> real_mult (mu s) c) states) eps)
        (real_plus c eps)
        (real_le_plus_compat
          (real_list_sum (fun s ->
            real_mult (mu s) (tv_row states k kpos keep keep_nonempty s))
            states)
          (real_list_sum (fun s -> real_mult (mu s) c) states) eps eps
          (real_list_sum_le (fun s ->
            real_mult (mu s) (tv_row states k kpos keep keep_nonempty s))
            (fun s -> real_mult (mu s) c) states (fun s ->
            real_le_trans
              (real_mult (mu s) (tv_row states k kpos keep keep_nonempty s))
              (real_mult (tv_row states k kpos keep keep_nonempty s) (mu s))
              (real_mult (mu s) c) (Inr
              (real_mult_comm (mu s)
                (tv_row states k kpos keep keep_nonempty s)))
              (real_le_trans
                (real_mult (tv_row states k kpos keep keep_nonempty s) (mu s))
                (real_mult c (mu s)) (real_mult (mu s) c)
                (real_le_mult_compat_weak
                  (tv_row states k kpos keep keep_nonempty s) c (mu s)
                  (hnn s) (hrow s))
                (Inr (real_mult_comm c (mu s))))))
          (real_le_refl eps))
        (Inr
        (RealSetoid.real_eq_plus_compat
          (real_list_sum (fun s -> real_mult (mu s) c) states) eps c eps
          (real_eq_trans (real_list_sum (fun w -> real_mult (mu w) c) states)
            (real_mult c (real_list_sum mu states)) c
            (real_list_sum_linear_r c mu states)
            (real_eq_trans (real_mult c (real_list_sum mu states))
              (real_mult c real_one) c
              (RealSetoid.real_eq_mult_compat c (real_list_sum mu states) c
                real_one (real_eq_refl c) hnorm)
              (real_mult_one c)))
          (real_eq_refl eps)))))

(** val kv_regroup4 : real -> real -> real -> real -> real_eq **)

let kv_regroup4 a b c0 d =
  real_eq_trans (real_plus (real_plus a b) (real_plus c0 d))
    (real_plus a (real_plus b (real_plus c0 d)))
    (real_plus (real_plus a c0) (real_plus b d))
    (real_eq_sym (real_plus a (real_plus b (real_plus c0 d)))
      (real_plus (real_plus a b) (real_plus c0 d))
      (real_plus_assoc a b (real_plus c0 d)))
    (real_eq_trans (real_plus a (real_plus b (real_plus c0 d)))
      (real_plus a (real_plus c0 (real_plus b d)))
      (real_plus (real_plus a c0) (real_plus b d))
      (RealSetoid.real_eq_plus_compat a (real_plus b (real_plus c0 d)) a
        (real_plus c0 (real_plus b d)) (real_eq_refl a)
        (real_eq_trans (real_plus b (real_plus c0 d))
          (real_plus (real_plus b c0) d) (real_plus c0 (real_plus b d))
          (real_plus_assoc b c0 d)
          (real_eq_trans (real_plus (real_plus b c0) d)
            (real_plus (real_plus c0 b) d) (real_plus c0 (real_plus b d))
            (RealSetoid.real_eq_plus_compat (real_plus b c0) d
              (real_plus c0 b) d (real_plus_comm b c0) (real_eq_refl d))
            (real_eq_sym (real_plus c0 (real_plus b d))
              (real_plus (real_plus c0 b) d) (real_plus_assoc c0 b d)))))
      (real_plus_assoc a c0 (real_plus b d)))

(** val kv_drift_P :
    'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq)
    -> ('a1 -> 'a1 -> real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT)
    and0) sigT -> real -> ('a1 -> real_le) -> nat -> ('a1 -> real) -> real_eq
    -> ('a1 -> real_le) -> real -> real_lt -> real_le **)

let rec kv_drift_P states states_ne k krow kpos keep keep_nonempty c hrow n mu hnorm hnn eps0 heps0 =
  match n with
  | O ->
    RealSetoid.real_eq_le (ddist states mu mu)
      (real_plus (real_mult real_zero c) (real_mult real_zero eps0))
      (real_eq_trans (ddist states mu mu) real_zero
        (real_plus (real_mult real_zero c) (real_mult real_zero eps0))
        (kv_D_zero states mu)
        (real_eq_sym
          (real_plus (real_mult real_zero c) (real_mult real_zero eps0))
          real_zero
          (real_eq_trans
            (real_plus (real_mult real_zero c) (real_mult real_zero eps0))
            (real_plus real_zero real_zero) real_zero
            (RealSetoid.real_eq_plus_compat (real_mult real_zero c)
              (real_mult real_zero eps0) real_zero real_zero
              (real_eq_trans (real_mult real_zero c) (real_mult c real_zero)
                real_zero (real_mult_comm real_zero c) (real_mult_zero c))
              (real_eq_trans (real_mult real_zero eps0)
                (real_mult eps0 real_zero) real_zero
                (real_mult_comm real_zero eps0) (real_mult_zero eps0)))
            (real_plus_zero real_zero))))
  | S n0 ->
    let hXn = kv_kev_iter_norm states k kpos keep keep_nonempty n0 mu hnorm in
    let hXnn = kv_kev_iter_nonneg states k kpos keep keep_nonempty n0 mu hnn
    in
    let ht3 =
      real_mult_pos_compat
        (real_inv_pos (real_plus (real_plus real_one real_one) real_one)
          kv_three_R_pos)
        eps0
        (real_inv_pos_pos (real_plus (real_plus real_one real_one) real_one)
          kv_three_R_pos)
        heps0
    in
    let h3B =
      real_eq_trans
        (real_plus
          (real_mult
            (real_inv_pos (real_plus (real_plus real_one real_one) real_one)
              kv_three_R_pos)
            eps0)
          (real_plus
            (real_mult
              (real_inv_pos
                (real_plus (real_plus real_one real_one) real_one)
                kv_three_R_pos)
              eps0)
            (real_mult
              (real_inv_pos
                (real_plus (real_plus real_one real_one) real_one)
                kv_three_R_pos)
              eps0)))
        (real_plus
          (real_plus
            (real_mult
              (real_inv_pos
                (real_plus (real_plus real_one real_one) real_one)
                kv_three_R_pos)
              eps0)
            (real_mult
              (real_inv_pos
                (real_plus (real_plus real_one real_one) real_one)
                kv_three_R_pos)
              eps0))
          (real_mult
            (real_inv_pos (real_plus (real_plus real_one real_one) real_one)
              kv_three_R_pos)
            eps0))
        eps0
        (real_plus_assoc
          (real_mult
            (real_inv_pos (real_plus (real_plus real_one real_one) real_one)
              kv_three_R_pos)
            eps0)
          (real_mult
            (real_inv_pos (real_plus (real_plus real_one real_one) real_one)
              kv_three_R_pos)
            eps0)
          (real_mult
            (real_inv_pos (real_plus (real_plus real_one real_one) real_one)
              kv_three_R_pos)
            eps0))
        (real_eq_trans
          (real_plus
            (real_plus
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0)
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0))
            (real_mult
              (real_inv_pos
                (real_plus (real_plus real_one real_one) real_one)
                kv_three_R_pos)
              eps0))
          (real_mult (real_plus (real_plus real_one real_one) real_one)
            (real_mult
              (real_inv_pos
                (real_plus (real_plus real_one real_one) real_one)
                kv_three_R_pos)
              eps0))
          eps0
          (kv_plus_self_three
            (real_mult
              (real_inv_pos
                (real_plus (real_plus real_one real_one) real_one)
                kv_three_R_pos)
              eps0))
          (kv_inv_absorb (real_plus (real_plus real_one real_one) real_one)
            kv_three_R_pos eps0))
    in
    real_le_trans
      (ddist states
        (lstep states (k_ev states k kpos keep keep_nonempty)
          (kev_iter states k kpos keep keep_nonempty n0 mu))
        (lstep states k (k_iter states k n0 mu)))
      (real_plus
        (ddist states
          (lstep states (k_ev states k kpos keep keep_nonempty)
            (kev_iter states k kpos keep keep_nonempty n0 mu))
          (lstep states k (kev_iter states k kpos keep keep_nonempty n0 mu)))
        (real_plus
          (ddist states
            (lstep states k (kev_iter states k kpos keep keep_nonempty n0 mu))
            (lstep states k (k_iter states k n0 mu)))
          (real_mult
            (real_inv_pos (real_plus (real_plus real_one real_one) real_one)
              kv_three_R_pos)
            eps0)))
      (real_plus (real_mult (real_plus real_one (real_of_nat n0)) c)
        (real_mult (real_plus real_one (real_of_nat n0)) eps0))
      (kv_D_triangle states states_ne k krow keep keep_nonempty
        (lstep states (k_ev states k kpos keep keep_nonempty)
          (kev_iter states k kpos keep keep_nonempty n0 mu))
        (lstep states k (kev_iter states k kpos keep keep_nonempty n0 mu))
        (lstep states k (k_iter states k n0 mu))
        (real_mult
          (real_inv_pos (real_plus (real_plus real_one real_one) real_one)
            kv_three_R_pos)
          eps0)
        ht3)
      (real_le_trans
        (real_plus
          (ddist states
            (lstep states (k_ev states k kpos keep keep_nonempty)
              (kev_iter states k kpos keep keep_nonempty n0 mu))
            (lstep states k (kev_iter states k kpos keep keep_nonempty n0 mu)))
          (real_plus
            (ddist states
              (lstep states k
                (kev_iter states k kpos keep keep_nonempty n0 mu))
              (lstep states k (k_iter states k n0 mu)))
            (real_mult
              (real_inv_pos
                (real_plus (real_plus real_one real_one) real_one)
                kv_three_R_pos)
              eps0)))
        (real_plus
          (real_plus c
            (real_mult
              (real_inv_pos
                (real_plus (real_plus real_one real_one) real_one)
                kv_three_R_pos)
              eps0))
          (real_plus
            (real_plus (real_mult (real_of_nat n0) c)
              (real_mult (real_of_nat n0) eps0))
            (real_plus
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0)
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0))))
        (real_plus (real_mult (real_plus real_one (real_of_nat n0)) c)
          (real_mult (real_plus real_one (real_of_nat n0)) eps0))
        (real_le_plus_compat
          (ddist states
            (lstep states (k_ev states k kpos keep keep_nonempty)
              (kev_iter states k kpos keep keep_nonempty n0 mu))
            (lstep states k (kev_iter states k kpos keep keep_nonempty n0 mu)))
          (real_plus c
            (real_mult
              (real_inv_pos
                (real_plus (real_plus real_one real_one) real_one)
                kv_three_R_pos)
              eps0))
          (real_plus
            (ddist states
              (lstep states k
                (kev_iter states k kpos keep keep_nonempty n0 mu))
              (lstep states k (k_iter states k n0 mu)))
            (real_mult
              (real_inv_pos
                (real_plus (real_plus real_one real_one) real_one)
                kv_three_R_pos)
              eps0))
          (real_plus
            (real_plus (real_mult (real_of_nat n0) c)
              (real_mult (real_of_nat n0) eps0))
            (real_plus
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0)
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0)))
          (real_le_trans
            (ddist states
              (lstep states (k_ev states k kpos keep keep_nonempty)
                (kev_iter states k kpos keep keep_nonempty n0 mu))
              (lstep states k
                (kev_iter states k kpos keep keep_nonempty n0 mu)))
            (real_plus c
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0))
            (real_plus c
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0))
            (kv_step_drift states states_ne k krow kpos keep keep_nonempty c
              hrow (kev_iter states k kpos keep keep_nonempty n0 mu)
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0)
              ht3 hXn hXnn)
            (Inr
            (RealSetoid.real_eq_plus_compat c
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0)
              c
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0)
              (real_eq_refl c)
              (real_eq_refl
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0)))))
          (real_le_trans
            (real_plus
              (ddist states
                (lstep states k
                  (kev_iter states k kpos keep keep_nonempty n0 mu))
                (lstep states k (k_iter states k n0 mu)))
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0))
            (real_plus
              (real_plus
                (ddist states
                  (kev_iter states k kpos keep keep_nonempty n0 mu)
                  (k_iter states k n0 mu))
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0))
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0))
            (real_plus
              (real_plus (real_mult (real_of_nat n0) c)
                (real_mult (real_of_nat n0) eps0))
              (real_plus
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0)
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0)))
            (real_le_plus_compat
              (ddist states
                (lstep states k
                  (kev_iter states k kpos keep keep_nonempty n0 mu))
                (lstep states k (k_iter states k n0 mu)))
              (real_plus
                (ddist states
                  (kev_iter states k kpos keep keep_nonempty n0 mu)
                  (k_iter states k n0 mu))
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0))
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0)
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0)
              (kv_nonexpansive states states_ne k krow keep keep_nonempty k
                krow (fun s s'' ->
                real_le_from_lt_aux real_zero (k s s'') (kpos s s''))
                (kev_iter states k kpos keep keep_nonempty n0 mu)
                (k_iter states k n0 mu)
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0)
                ht3)
              (real_le_refl
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0)))
            (real_le_trans
              (real_plus
                (real_plus
                  (ddist states
                    (kev_iter states k kpos keep keep_nonempty n0 mu)
                    (k_iter states k n0 mu))
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0))
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0))
              (real_plus
                (real_plus
                  (real_plus (real_mult (real_of_nat n0) c)
                    (real_mult (real_of_nat n0) eps0))
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0))
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0))
              (real_plus
                (real_plus (real_mult (real_of_nat n0) c)
                  (real_mult (real_of_nat n0) eps0))
                (real_plus
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0)
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0)))
              (real_le_plus_compat
                (real_plus
                  (ddist states
                    (kev_iter states k kpos keep keep_nonempty n0 mu)
                    (k_iter states k n0 mu))
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0))
                (real_plus
                  (real_plus (real_mult (real_of_nat n0) c)
                    (real_mult (real_of_nat n0) eps0))
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0))
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0)
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0)
                (real_le_plus_compat
                  (ddist states
                    (kev_iter states k kpos keep keep_nonempty n0 mu)
                    (k_iter states k n0 mu))
                  (real_plus (real_mult (real_of_nat n0) c)
                    (real_mult (real_of_nat n0) eps0))
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0)
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0)
                  (kv_drift_P states states_ne k krow kpos keep keep_nonempty
                    c hrow n0 mu hnorm hnn eps0 heps0)
                  (real_le_refl
                    (real_mult
                      (real_inv_pos
                        (real_plus (real_plus real_one real_one) real_one)
                        kv_three_R_pos)
                      eps0)))
                (real_le_refl
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0)))
              (Inr
              (real_eq_sym
                (real_plus
                  (real_plus (real_mult (real_of_nat n0) c)
                    (real_mult (real_of_nat n0) eps0))
                  (real_plus
                    (real_mult
                      (real_inv_pos
                        (real_plus (real_plus real_one real_one) real_one)
                        kv_three_R_pos)
                      eps0)
                    (real_mult
                      (real_inv_pos
                        (real_plus (real_plus real_one real_one) real_one)
                        kv_three_R_pos)
                      eps0)))
                (real_plus
                  (real_plus
                    (real_plus (real_mult (real_of_nat n0) c)
                      (real_mult (real_of_nat n0) eps0))
                    (real_mult
                      (real_inv_pos
                        (real_plus (real_plus real_one real_one) real_one)
                        kv_three_R_pos)
                      eps0))
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0))
                (real_plus_assoc
                  (real_plus (real_mult (real_of_nat n0) c)
                    (real_mult (real_of_nat n0) eps0))
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0)
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0)))))))
        (real_le_trans
          (real_plus
            (real_plus c
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0))
            (real_plus
              (real_plus (real_mult (real_of_nat n0) c)
                (real_mult (real_of_nat n0) eps0))
              (real_plus
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0)
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0))))
          (real_plus
            (real_plus c
              (real_plus (real_mult (real_of_nat n0) c)
                (real_mult (real_of_nat n0) eps0)))
            eps0)
          (real_plus (real_mult (real_plus real_one (real_of_nat n0)) c)
            (real_mult (real_plus real_one (real_of_nat n0)) eps0))
          (real_le_trans
            (real_plus
              (real_plus c
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0))
              (real_plus
                (real_plus (real_mult (real_of_nat n0) c)
                  (real_mult (real_of_nat n0) eps0))
                (real_plus
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0)
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0))))
            (real_plus
              (real_plus c
                (real_plus (real_mult (real_of_nat n0) c)
                  (real_mult (real_of_nat n0) eps0)))
              (real_plus
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0)
                (real_plus
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0)
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0))))
            (real_plus
              (real_plus c
                (real_plus (real_mult (real_of_nat n0) c)
                  (real_mult (real_of_nat n0) eps0)))
              eps0)
            (Inr
            (kv_regroup4 c
              (real_mult
                (real_inv_pos
                  (real_plus (real_plus real_one real_one) real_one)
                  kv_three_R_pos)
                eps0)
              (real_plus (real_mult (real_of_nat n0) c)
                (real_mult (real_of_nat n0) eps0))
              (real_plus
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0)
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0))))
            (real_le_plus_compat
              (real_plus c
                (real_plus (real_mult (real_of_nat n0) c)
                  (real_mult (real_of_nat n0) eps0)))
              (real_plus c
                (real_plus (real_mult (real_of_nat n0) c)
                  (real_mult (real_of_nat n0) eps0)))
              (real_plus
                (real_mult
                  (real_inv_pos
                    (real_plus (real_plus real_one real_one) real_one)
                    kv_three_R_pos)
                  eps0)
                (real_plus
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0)
                  (real_mult
                    (real_inv_pos
                      (real_plus (real_plus real_one real_one) real_one)
                      kv_three_R_pos)
                    eps0)))
              eps0
              (real_le_refl
                (real_plus c
                  (real_plus (real_mult (real_of_nat n0) c)
                    (real_mult (real_of_nat n0) eps0))))
              (Inr h3B)))
          (Inr
          (real_eq_trans
            (real_plus
              (real_plus c
                (real_plus (real_mult (real_of_nat n0) c)
                  (real_mult (real_of_nat n0) eps0)))
              eps0)
            (real_plus (real_plus c (real_mult (real_of_nat n0) c))
              (real_plus eps0 (real_mult (real_of_nat n0) eps0)))
            (real_plus (real_mult (real_plus real_one (real_of_nat n0)) c)
              (real_mult (real_plus real_one (real_of_nat n0)) eps0))
            (real_eq_trans
              (real_plus
                (real_plus c
                  (real_plus (real_mult (real_of_nat n0) c)
                    (real_mult (real_of_nat n0) eps0)))
                eps0)
              (real_plus c
                (real_plus
                  (real_plus (real_mult (real_of_nat n0) c)
                    (real_mult (real_of_nat n0) eps0))
                  eps0))
              (real_plus (real_plus c (real_mult (real_of_nat n0) c))
                (real_plus eps0 (real_mult (real_of_nat n0) eps0)))
              (real_eq_sym
                (real_plus c
                  (real_plus
                    (real_plus (real_mult (real_of_nat n0) c)
                      (real_mult (real_of_nat n0) eps0))
                    eps0))
                (real_plus
                  (real_plus c
                    (real_plus (real_mult (real_of_nat n0) c)
                      (real_mult (real_of_nat n0) eps0)))
                  eps0)
                (real_plus_assoc c
                  (real_plus (real_mult (real_of_nat n0) c)
                    (real_mult (real_of_nat n0) eps0))
                  eps0))
              (real_eq_trans
                (real_plus c
                  (real_plus
                    (real_plus (real_mult (real_of_nat n0) c)
                      (real_mult (real_of_nat n0) eps0))
                    eps0))
                (real_plus c
                  (real_plus (real_mult (real_of_nat n0) c)
                    (real_plus (real_mult (real_of_nat n0) eps0) eps0)))
                (real_plus (real_plus c (real_mult (real_of_nat n0) c))
                  (real_plus eps0 (real_mult (real_of_nat n0) eps0)))
                (RealSetoid.real_eq_plus_compat c
                  (real_plus
                    (real_plus (real_mult (real_of_nat n0) c)
                      (real_mult (real_of_nat n0) eps0))
                    eps0)
                  c
                  (real_plus (real_mult (real_of_nat n0) c)
                    (real_plus (real_mult (real_of_nat n0) eps0) eps0))
                  (real_eq_refl c)
                  (real_eq_sym
                    (real_plus (real_mult (real_of_nat n0) c)
                      (real_plus (real_mult (real_of_nat n0) eps0) eps0))
                    (real_plus
                      (real_plus (real_mult (real_of_nat n0) c)
                        (real_mult (real_of_nat n0) eps0))
                      eps0)
                    (real_plus_assoc (real_mult (real_of_nat n0) c)
                      (real_mult (real_of_nat n0) eps0) eps0)))
                (real_eq_trans
                  (real_plus c
                    (real_plus (real_mult (real_of_nat n0) c)
                      (real_plus (real_mult (real_of_nat n0) eps0) eps0)))
                  (real_plus c
                    (real_plus (real_mult (real_of_nat n0) c)
                      (real_plus eps0 (real_mult (real_of_nat n0) eps0))))
                  (real_plus (real_plus c (real_mult (real_of_nat n0) c))
                    (real_plus eps0 (real_mult (real_of_nat n0) eps0)))
                  (RealSetoid.real_eq_plus_compat c
                    (real_plus (real_mult (real_of_nat n0) c)
                      (real_plus (real_mult (real_of_nat n0) eps0) eps0))
                    c
                    (real_plus (real_mult (real_of_nat n0) c)
                      (real_plus eps0 (real_mult (real_of_nat n0) eps0)))
                    (real_eq_refl c)
                    (RealSetoid.real_eq_plus_compat
                      (real_mult (real_of_nat n0) c)
                      (real_plus (real_mult (real_of_nat n0) eps0) eps0)
                      (real_mult (real_of_nat n0) c)
                      (real_plus eps0 (real_mult (real_of_nat n0) eps0))
                      (real_eq_refl (real_mult (real_of_nat n0) c))
                      (real_plus_comm (real_mult (real_of_nat n0) eps0) eps0)))
                  (real_plus_assoc c (real_mult (real_of_nat n0) c)
                    (real_plus eps0 (real_mult (real_of_nat n0) eps0))))))
            (RealSetoid.real_eq_plus_compat
              (real_plus c (real_mult (real_of_nat n0) c))
              (real_plus eps0 (real_mult (real_of_nat n0) eps0))
              (real_mult (real_plus real_one (real_of_nat n0)) c)
              (real_mult (real_plus real_one (real_of_nat n0)) eps0)
              (real_eq_trans (real_plus c (real_mult (real_of_nat n0) c))
                (real_plus (real_mult real_one c)
                  (real_mult (real_of_nat n0) c))
                (real_mult (real_plus real_one (real_of_nat n0)) c)
                (RealSetoid.real_eq_plus_compat c
                  (real_mult (real_of_nat n0) c) (real_mult real_one c)
                  (real_mult (real_of_nat n0) c)
                  (real_eq_sym (real_mult real_one c) c (kv_one_mult_l c))
                  (real_eq_refl (real_mult (real_of_nat n0) c)))
                (real_eq_sym
                  (real_mult (real_plus real_one (real_of_nat n0)) c)
                  (real_plus (real_mult real_one c)
                    (real_mult (real_of_nat n0) c))
                  (kv_distrib_r real_one (real_of_nat n0) c)))
              (real_eq_trans
                (real_plus eps0 (real_mult (real_of_nat n0) eps0))
                (real_plus (real_mult real_one eps0)
                  (real_mult (real_of_nat n0) eps0))
                (real_mult (real_plus real_one (real_of_nat n0)) eps0)
                (RealSetoid.real_eq_plus_compat eps0
                  (real_mult (real_of_nat n0) eps0) (real_mult real_one eps0)
                  (real_mult (real_of_nat n0) eps0)
                  (real_eq_sym (real_mult real_one eps0) eps0
                    (kv_one_mult_l eps0))
                  (real_eq_refl (real_mult (real_of_nat n0) eps0)))
                (real_eq_sym
                  (real_mult (real_plus real_one (real_of_nat n0)) eps0)
                  (real_plus (real_mult real_one eps0)
                    (real_mult (real_of_nat n0) eps0))
                  (kv_distrib_r real_one (real_of_nat n0) eps0))))))))

(** val kv_drift_bound :
    'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq)
    -> ('a1 -> 'a1 -> real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT)
    and0) sigT -> real -> ('a1 -> real_le) -> nat -> ('a1 -> real) -> real ->
    real_eq -> ('a1 -> real_le) -> real_lt -> real_le **)

let kv_drift_bound states states_ne k krow kpos keep keep_nonempty c hrow n mu eps hnorm hnn heps =
  match n with
  | O ->
    real_le_trans (ddist states mu mu) eps
      (real_plus (real_mult real_zero c) eps)
      (real_le_trans (ddist states mu mu) real_zero eps
        (RealSetoid.real_eq_le (ddist states mu mu) real_zero
          (kv_D_zero states mu))
        (real_le_from_lt_aux real_zero eps heps))
      (Inr
      (real_eq_sym (real_plus (real_mult real_zero c) eps) eps
        (real_eq_trans (real_plus (real_mult real_zero c) eps)
          (real_plus real_zero eps) eps
          (RealSetoid.real_eq_plus_compat (real_mult real_zero c) eps
            real_zero eps
            (real_eq_trans (real_mult real_zero c) (real_mult c real_zero)
              real_zero (real_mult_comm real_zero c) (real_mult_zero c))
            (real_eq_refl eps))
          (kv_plus_zero_l eps))))
  | S n0 ->
    let hshare =
      real_mult_pos_compat
        (real_inv_pos (real_of_nat (S n0)) (kv_ofnat_S_pos n0)) eps
        (real_inv_pos_pos (real_of_nat (S n0)) (kv_ofnat_S_pos n0)) heps
    in
    real_le_trans
      (ddist states (kev_iter states k kpos keep keep_nonempty (S n0) mu)
        (k_iter states k (S n0) mu))
      (real_plus (real_mult (real_of_nat (S n0)) c)
        (real_mult (real_of_nat (S n0))
          (real_mult (real_inv_pos (real_of_nat (S n0)) (kv_ofnat_S_pos n0))
            eps)))
      (real_plus (real_mult (real_of_nat (S n0)) c) eps)
      (kv_drift_P states states_ne k krow kpos keep keep_nonempty c hrow (S
        n0) mu hnorm hnn
        (real_mult (real_inv_pos (real_of_nat (S n0)) (kv_ofnat_S_pos n0))
          eps)
        hshare)
      (RealSetoid.real_le_id_r
        (real_plus (real_mult (real_of_nat (S n0)) c)
          (real_mult (real_of_nat (S n0))
            (real_mult
              (real_inv_pos (real_of_nat (S n0)) (kv_ofnat_S_pos n0)) eps)))
        (real_plus (real_mult (real_of_nat (S n0)) c)
          (real_mult (real_of_nat (S n0))
            (real_mult
              (real_inv_pos (real_of_nat (S n0)) (kv_ofnat_S_pos n0)) eps)))
        (real_plus (real_mult (real_of_nat (S n0)) c) eps)
        (RealSetoid.real_eq_plus_compat (real_mult (real_of_nat (S n0)) c)
          (real_mult (real_of_nat (S n0))
            (real_mult
              (real_inv_pos (real_of_nat (S n0)) (kv_ofnat_S_pos n0)) eps))
          (real_mult (real_of_nat (S n0)) c) eps
          (real_eq_refl (real_mult (real_of_nat (S n0)) c))
          (kv_inv_absorb (real_of_nat (S n0)) (kv_ofnat_S_pos n0) eps))
        (real_le_refl
          (real_plus (real_mult (real_of_nat (S n0)) c)
            (real_mult (real_of_nat (S n0))
              (real_mult
                (real_inv_pos (real_of_nat (S n0)) (kv_ofnat_S_pos n0)) eps)))))

(** val kv_drift_bound_tv :
    'a1 list -> 'a1 list id not -> ('a1 -> 'a1 -> real) -> ('a1 -> real_eq)
    -> ('a1 -> 'a1 -> real_lt) -> ('a1 -> bool) -> ('a1, (bool id, 'a1 inT)
    and0) sigT -> real -> ('a1 -> real_le) -> nat -> ('a1 -> real) -> real ->
    real_eq -> ('a1 -> real_le) -> real_lt -> real_le **)

let kv_drift_bound_tv states states_ne k krow kpos keep keep_nonempty c hrow n mu eps hnorm hnn heps =
  real_le_mult_compat_r
    (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
    (ddist states (kev_iter states k kpos keep keep_nonempty n mu)
      (k_iter states k n mu))
    (real_plus (real_mult (real_of_nat n) c) eps)
    (real_le_from_lt_aux real_zero
      (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
      (real_inv_pos_pos (real_plus real_one real_one) kv_two_R_pos))
    (kv_drift_bound states states_ne k krow kpos keep keep_nonempty c hrow n
      mu eps hnorm hnn heps)
