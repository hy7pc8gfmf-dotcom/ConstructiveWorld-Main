
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

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

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h

type sumbool =
| Left
| Right

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

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

(** val gmax : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> 'a1 **)

let gmax cmp x y =
  match cmp x y with
  | Lt -> y
  | _ -> x

(** val gmin : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> 'a1 **)

let gmin cmp x y =
  match cmp x y with
  | Gt -> y
  | _ -> x

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

  (** val min : nat -> nat -> nat **)

  let rec min n m =
    match n with
    | O -> O
    | S n' -> (match m with
               | O -> O
               | S m' -> S (min n' m'))
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

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
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

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)
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

  (** val to_nat : z -> nat **)

  let to_nat = function
  | Zpos p -> Pos.to_nat p
  | _ -> O

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Pos.of_succ_nat n0)

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x
 end

(** val z_lt_dec : z -> z -> sumbool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> Left
  | _ -> Right

(** val z_lt_ge_dec : z -> z -> sumbool **)

let z_lt_ge_dec =
  z_lt_dec

(** val z_lt_le_dec : z -> z -> sumbool **)

let z_lt_le_dec =
  z_lt_ge_dec

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

(** val qlt_le_dec : q -> q -> sumbool **)

let qlt_le_dec x y =
  z_lt_le_dec (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qarchimedean : q -> positive **)

let qarchimedean q0 =
  let { qnum = qnum0; qden = _ } = q0 in
  (match qnum0 with
   | Zpos p -> Coq_Pos.add p XH
   | _ -> XH)

(** val qabs : q -> q **)

let qabs x =
  let { qnum = n; qden = d } = x in { qnum = (Z.abs n); qden = d }

(** val qmax : q -> q -> q **)

let qmax =
  gmax qcompare

(** val qmin : q -> q -> q **)

let qmin =
  gmin qcompare

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

type 'a not = 'a -> empty_set

type natLe = bool id

(** val natLe_lift : nat -> nat -> natLe **)

let natLe_lift n m =
  let b = Nat.leb n m in
  (match b with
   | True -> Id_refl
   | False -> assert false (* absurd case *))

type qseq = nat -> q

(** val qlt_bool : q -> q -> bool **)

let qlt_bool x y =
  match qcompare x y with
  | Lt -> True
  | _ -> False

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

(** val qltT_0_1 : qltT **)

let qltT_0_1 =
  Id_refl

(** val qltT_0_2 : qltT **)

let qltT_0_2 =
  Id_refl

(** val qltT_0_3 : qltT **)

let qltT_0_3 =
  Id_refl

(** val qleT'_refl : q -> qleT' **)

let qleT'_refl x =
  qle_to_QleT' x x

(** val qleT'_trans : q -> q -> q -> qleT' -> qleT' -> qleT' **)

let qleT'_trans x _ z0 _ _ =
  qle_to_QleT' x z0

(** val qltT_leT' : q -> q -> qltT -> qleT' **)

let qltT_leT' x y _ =
  qle_to_QleT' x y

(** val qleT'_ltT_ltT : q -> q -> q -> qleT' -> qltT -> qltT **)

let qleT'_ltT_ltT x _ z0 _ _ =
  qlt_to_QltT x z0

(** val qltT_leT'_ltT : q -> q -> q -> qltT -> qleT' -> qltT **)

let qltT_leT'_ltT x _ z0 _ _ =
  qlt_to_QltT x z0

(** val qleT'_plus_compat : q -> q -> q -> q -> qleT' -> qleT' -> qleT' **)

let qleT'_plus_compat a b c d _ _ =
  qle_to_QleT' (qplus a c) (qplus b d)

(** val qleT'_plus_nonneg_rT : q -> q -> qleT' -> qleT' **)

let qleT'_plus_nonneg_rT x y hy =
  qleT'_trans x (qplus x { qnum = Z0; qden = XH }) (qplus x y)
    (qle_to_QleT' x (qplus x { qnum = Z0; qden = XH }))
    (qleT'_plus_compat x x { qnum = Z0; qden = XH } y (qleT'_refl x) hy)

(** val qltT_plus_ltT : q -> q -> q -> q -> qltT -> qltT -> qltT **)

let qltT_plus_ltT a b c d _ _ =
  qlt_to_QltT (qplus a c) (qplus b d)

(** val qltT_plus_leT'_ltT : q -> q -> q -> q -> qltT -> qleT' -> qltT **)

let qltT_plus_leT'_ltT a b c d _ _ =
  qlt_to_QltT (qplus a c) (qplus b d)

(** val qleT'_plus_ltT_ltT : q -> q -> q -> q -> qleT' -> qltT -> qltT **)

let qleT'_plus_ltT_ltT a b c d _ _ =
  qlt_to_QltT (qplus a c) (qplus b d)

(** val qleT'_mult_compat_l : q -> q -> q -> qleT' -> qleT' -> qleT' **)

let qleT'_mult_compat_l x y z0 _ _ =
  qle_to_QleT' (qmult z0 x) (qmult z0 y)

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

type qeqT = bool id

(** val qeq_imp_qeqT : q -> q -> qeqT **)

let qeq_imp_qeqT a b =
  let c = qcompare a b in
  (match c with
   | Eq -> Id_refl
   | _ -> assert false (* absurd case *))

(** val qabs_nonnegT : q -> qleT' **)

let qabs_nonnegT x =
  qle_to_QleT' { qnum = Z0; qden = XH } (qabs x)

(** val qltT_plus_pos_r : q -> q -> qltT -> qltT -> qltT **)

let qltT_plus_pos_r x y _ _ =
  qlt_to_QltT { qnum = Z0; qden = XH } (qplus x y)

(** val qltT_div_pos : q -> q -> qltT -> qltT -> qltT **)

let qltT_div_pos x y _ _ =
  qlt_to_QltT { qnum = Z0; qden = XH } (qdiv x y)

(** val qltT_eq_compat_l : q -> q -> q -> qltT -> qltT **)

let qltT_eq_compat_l _ a' b _ =
  qlt_to_QltT a' b

(** val qltT_eq_compat_r : q -> q -> q -> qltT -> qltT **)

let qltT_eq_compat_r a _ b _ =
  qlt_to_QltT b a

(** val qltT_mult_ltT_compat_r : q -> q -> q -> qltT -> qltT -> qltT **)

let qltT_mult_ltT_compat_r a b c _ _ =
  qlt_to_QltT (qmult a c) (qmult b c)

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

(** val real_const : q -> real **)

let real_const c =
  ExistT ((fun _ -> c), (fun _ _ -> ExistT (O, (fun _ _ _ _ -> Id_refl))))

type real_lim = q -> qltT -> (nat, nat -> __ -> (real_lt, real_lt) and0) sigT

(** val real_lim_unique :
    (nat -> real) -> real -> real -> real_lim -> real_lim -> real_eq **)

let real_lim_unique _ l1 l2 hlim1 hlim2 eps _ =
  let heps4 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH })
  in
  let s = hlim1 (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }) heps4 in
  let ExistT (x, _) = s in
  let s0 = hlim2 (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }) heps4 in
  let ExistT (x0, _) = s0 in
  let ExistT (x1, c) = l1 in
  let ExistT (x2, c0) = l2 in
  let s1 = c (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }) heps4 in
  let ExistT (x3, _) = s1 in
  let s2 = c0 (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }) heps4 in
  let ExistT (x4, _) = s2 in
  ExistT ((max (max x x0) (max x3 x4)), (fun k _ ->
  qlt_to_QltT
    (qabs (qminus (projT1 (ExistT (x1, c)) k) (projT1 (ExistT (x2, c0)) k)))
    eps))

(** val q_arch_inv : q -> (nat, __) sigT **)

let q_arch_inv eps =
  let s = qarchimedean (qdiv { qnum = (Zpos XH); qden = XH } eps) in
  let n = mul (Z.to_nat (Zpos s)) (S (S O)) in ExistT (n, __)

(** val reg_index : (nat -> nat) -> nat -> nat **)

let rec reg_index fmod = function
| O -> fmod O
| S k' -> max (S (reg_index fmod k')) (fmod (S k'))

(** val reg_mod : qseq -> cauchy -> nat -> nat **)

let reg_mod _ hu j =
  projT1
    (hu
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum =
        (Z.of_nat (add j (S (S O)))); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum =
          (Z.of_nat (add j (S (S O)))); qden = XH })))

(** val regularize : qseq -> cauchy -> qseq **)

let regularize u hu k =
  u (reg_index (fun j -> reg_mod u hu j) k)

(** val regularize_cauchy : qseq -> cauchy -> cauchy **)

let regularize_cauchy u hu eps _ =
  let s = q_arch_inv eps in
  let ExistT (x, _) = s in
  ExistT (x, (fun a b _ _ ->
  qlt_to_QltT (qabs (qminus (regularize u hu a) (regularize u hu b))) eps))

(** val regularize_same_real : qseq -> cauchy -> real_eq **)

let regularize_same_real u hu eps _ =
  let hhalf0 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
  in
  let s = hu (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf0 in
  let ExistT (x, _) = s in
  ExistT (x, (fun k _ ->
  qlt_to_QltT
    (qabs
      (qminus
        (projT1 (ExistT ((regularize u hu), (regularize_cauchy u hu))) k)
        (projT1 (ExistT (u, hu)) k)))
    eps))

(** val regularized_family : (nat -> real) -> nat -> real **)

let regularized_family u m =
  ExistT ((regularize (projT1 (u m)) (projT2 (u m))),
    (regularize_cauchy (projT1 (u m)) (projT2 (u m))))

(** val regularized_family_same : (nat -> real) -> nat -> real_eq **)

let regularized_family_same u m =
  regularize_same_real (projT1 (u m)) (projT2 (u m))

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

(** val real_lt_irrefl : real -> real_lt not **)

let real_lt_irrefl _ _ =
  assert false (* absurd case *)

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

(** val real_eq_minus_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_eq **)

let real_eq_minus_compat a b c d hac hbd eps _ =
  let hhalf0 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
  in
  let s = hac (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf0 in
  let ExistT (x, _) = s in
  let s0 = hbd (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf0 in
  let ExistT (x0, _) = s0 in
  ExistT ((max x x0), (fun k _ ->
  qlt_to_QltT
    (qabs
      (qminus (projT1 (real_plus a (real_opp b)) k)
        (projT1 (real_plus c (real_opp d)) k)))
    eps))

(** val regularized_family_double_cauchy :
    (nat -> real) -> (q -> qltT -> (nat, nat -> nat -> __ -> __ -> (real_lt,
    real_lt) and0) sigT) -> q -> qltT -> (nat, nat -> nat -> __ -> __ ->
    (real_lt, real_lt) and0) sigT **)

let regularized_family_double_cauchy u hcau eps heps =
  let s = hcau eps heps in
  let ExistT (x, a) = s in
  ExistT (x, (fun m n _ _ ->
  let a0 = a m n __ __ in
  let Pair (r, r0) = a0 in
  Pair
  ((real_eq_lt_lt
     (real_plus (regularized_family u m) (real_opp (regularized_family u n)))
     (real_plus (u m) (real_opp (u n))) (real_const eps)
     (real_eq_minus_compat (regularized_family u m) (regularized_family u n)
       (u m) (u n) (regularized_family_same u m)
       (regularized_family_same u n))
     r),
  (real_eq_lt_lt
    (real_plus (regularized_family u n) (real_opp (regularized_family u m)))
    (real_plus (u n) (real_opp (u m))) (real_const eps)
    (real_eq_minus_compat (regularized_family u n) (regularized_family u m)
      (u n) (u m) (regularized_family_same u n) (regularized_family_same u m))
    r0))))

(** val regularized_diag_cauchy :
    (nat -> real) -> (q -> qltT -> (nat, nat -> nat -> __ -> __ -> (real_lt,
    real_lt) and0) sigT) -> cauchy **)

let regularized_diag_cauchy u hcau eps _ =
  let heps9 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv eps { qnum = (Zpos (XI (XO (XO XH)))); qden = XH })
  in
  let s = q_arch_inv (qdiv eps { qnum = (Zpos (XI (XO (XO XH)))); qden = XH })
  in
  let ExistT (x, _) = s in
  let hdc = regularized_family_double_cauchy u hcau in
  let s0 = hdc (qdiv eps { qnum = (Zpos (XI (XO (XO XH)))); qden = XH }) heps9
  in
  let ExistT (x0, _) = s0 in
  ExistT ((max x x0), (fun m n _ _ ->
  qlt_to_QltT
    (qabs
      (qminus (projT1 (regularized_family u m) m)
        (projT1 (regularized_family u n) n)))
    eps))

(** val regularized_diag_close :
    (nat -> real) -> (q -> qltT -> (nat, nat -> nat -> __ -> __ -> (real_lt,
    real_lt) and0) sigT) -> q -> qltT -> (nat, nat -> __ -> (nat, nat -> __
    -> qltT) sigT) sigT **)

let regularized_diag_close u hcau eps _ =
  let heps2 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
  in
  let heps6 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv eps { qnum = (Zpos (XO (XI XH))); qden = XH })
  in
  let s = q_arch_inv (qdiv eps { qnum = (Zpos (XO (XI XH))); qden = XH }) in
  let ExistT (x, _) = s in
  let hdc6 = regularized_family_double_cauchy u hcau in
  let s0 = hdc6 (qdiv eps { qnum = (Zpos (XO (XI XH))); qden = XH }) heps6 in
  let ExistT (x0, _) = s0 in
  ExistT ((max x x0), (fun n _ ->
  let hsame = regularized_family_same u n in
  let s1 = hsame (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) heps2 in
  let ExistT (x1, _) = s1 in
  ExistT ((max x1 (max x x0)), (fun k _ ->
  qlt_to_QltT
    (qabs (qminus (projT1 (u n) k) (projT1 (regularized_family u k) k))) eps))))

(** val real_cauchy_complete :
    (nat -> real) -> (q -> qltT -> (nat, nat -> nat -> __ -> __ -> (real_lt,
    real_lt) and0) sigT) -> (real, real_lim) sigT **)

let real_cauchy_complete u hcau =
  let l = ExistT ((fun k -> projT1 (regularized_family u k) k),
    (regularized_diag_cauchy u hcau))
  in
  ExistT (l, (fun eps _ ->
  let heps2 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
  in
  let s =
    regularized_diag_close u hcau
      (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) heps2
  in
  let ExistT (x, s0) = s in
  ExistT (x, (fun n _ ->
  let s1 = s0 n __ in
  let ExistT (x0, _) = s1 in
  Pair ((ExistT ((qdiv eps { qnum = (Zpos (XO XH)); qden = XH }), (Pair
  (heps2, (ExistT (x0, (fun k _ ->
  qlt_to_QltT (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
    (qminus (projT1 (real_plus l (real_const eps)) k) (projT1 (u n) k))))))))),
  (ExistT ((qdiv eps { qnum = (Zpos (XO XH)); qden = XH }), (Pair (heps2,
  (ExistT (x0, (fun k _ ->
  qlt_to_QltT (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
    (qminus (projT1 (u n) k)
      (projT1 (real_plus l (real_opp (real_const eps))) k))))))))))))))

(** val real_lt_le_trans :
    real -> real -> real -> real_lt -> real_le -> real_lt **)

let real_lt_le_trans x y z0 hlt = function
| Inl r -> real_lt_trans x y z0 hlt r
| Inr r -> real_lt_eq_lt x y z0 hlt r

(** val real_le_lt_trans :
    real -> real -> real -> real_le -> real_lt -> real_lt **)

let real_le_lt_trans x y z0 hle hlt =
  match hle with
  | Inl r -> real_lt_trans x y z0 r hlt
  | Inr r -> real_eq_lt_lt x y z0 r hlt

(** val real_le_antisym : real -> real -> real_le -> real_le -> real_eq **)

let real_le_antisym x y hxy hyx =
  match hxy with
  | Inl _ ->
    (match hyx with
     | Inl _ -> assert false (* absurd case *)
     | Inr r -> real_eq_sym y x r)
  | Inr r -> r

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

(** val q_pow : q -> nat -> q **)

let rec q_pow x = function
| O -> { qnum = (Zpos XH); qden = XH }
| S m -> qmult x (q_pow x m)

(** val q_fact : nat -> q **)

let rec q_fact = function
| O -> { qnum = (Zpos XH); qden = XH }
| S m -> qmult { qnum = (Z.of_nat (S m)); qden = XH } (q_fact m)

(** val exp_partial : nat -> q -> q **)

let rec exp_partial n x =
  match n with
  | O -> { qnum = (Zpos XH); qden = XH }
  | S m -> qplus (exp_partial m x) (qdiv (q_pow x (S m)) (q_fact (S m)))

(** val q_arch_geom : q -> (nat, nat -> natLe -> qleT') sigT **)

let q_arch_geom a =
  let s =
    qarchimedean
      (qmult
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH })
        a)
  in
  ExistT ((Coq_Pos.to_nat s), (fun t _ ->
  qle_to_QleT'
    (qmult
      (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden = XH })
      a)
    { qnum = (Z.of_nat (add t (S O))); qden = XH }))

(** val arch_decay : q -> q -> qleT' -> qltT -> (nat, qltT) sigT **)

let arch_decay c eps _ _ =
  let s = qarchimedean (qdiv c eps) in
  ExistT ((Coq_Pos.to_nat s),
  (qlt_to_QltT
    (qmult c
      (q_pow
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH })
        (S (Coq_Pos.to_nat s))))
    eps))

(** val exp_partial_cauchy :
    q -> q -> (nat, nat -> nat -> __ -> __ -> qltT) sigT **)

let exp_partial_cauchy x eps =
  let a = qabs x in
  let s = q_arch_geom a in
  let ExistT (x0, _) = s in
  let c =
    qmult (qdiv (q_pow a x0) (q_fact x0))
      (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden = XH })
  in
  let s0 =
    arch_decay c eps (qle_to_QleT' { qnum = Z0; qden = XH } c)
      (qlt_to_QltT { qnum = Z0; qden = XH } eps)
  in
  let ExistT (x1, _) = s0 in
  ExistT ((add x0 (S x1)), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (exp_partial m x) (exp_partial n x))) eps))

(** val exp_series : nat -> q -> q **)

let rec exp_series n b =
  match n with
  | O -> { qnum = (Zpos XH); qden = XH }
  | S m -> qplus (exp_series m b) (qdiv (q_pow b (S m)) (q_fact (S m)))

(** val exp_partial_cauchy_bounded :
    q -> q -> qleT' -> qltT -> (nat, nat -> nat -> natLe -> natLe -> q ->
    qleT' -> qltT) sigT **)

let exp_partial_cauchy_bounded b eps _ hep =
  let s = q_arch_geom b in
  let ExistT (x, _) = s in
  let c =
    qmult (qdiv (q_pow b x) (q_fact x))
      (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden = XH })
  in
  let s0 = arch_decay c eps (qle_to_QleT' { qnum = Z0; qden = XH } c) hep in
  let ExistT (x0, _) = s0 in
  ExistT ((add x (S x0)), (fun m n _ _ y _ ->
  qlt_to_QltT (qabs (qminus (exp_partial m y) (exp_partial n y))) eps))

(** val exp_series_arch :
    q -> qleT' -> (q, (qleT', nat -> qleT') and0) sigT **)

let exp_series_arch b _ =
  let s = q_arch_geom b in
  let ExistT (x, _) = s in
  let c =
    qplus (exp_series x b)
      (qmult (qdiv (q_pow b x) (q_fact x))
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH }))
  in
  ExistT (c, (Pair ((qle_to_QleT' { qnum = (Zpos XH); qden = XH } c),
  (fun n -> qle_to_QleT' (exp_series n b) c))))

(** val cauchy_real_exp : real -> real **)

let cauchy_real_exp = function
| ExistT (x0, c) ->
  ExistT ((fun n -> exp_partial n (x0 n)), (fun eps heps ->
    let s = real_norm_bounded (ExistT (x0, c)) in
    let ExistT (x1, a) = s in
    let Pair (q0, q1) = a in
    let s0 = exp_series_arch x1 (qltT_leT' { qnum = Z0; qden = XH } x1 q0) in
    let ExistT (x2, a0) = s0 in
    let Pair (q2, q3) = a0 in
    let hCposT =
      qltT_leT'_ltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH }
        x2 qltT_0_1 q2
    in
    let s1 =
      c (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
        (qltT_div_pos eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2)
          heps
          (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } x2
            qltT_0_2 hCposT))
    in
    let ExistT (x3, q4) = s1 in
    let heps2 =
      qltT_div_pos eps { qnum = (Zpos (XO XH)); qden = XH } heps qltT_0_2
    in
    let s2 =
      exp_partial_cauchy_bounded x1
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
        (qltT_leT' { qnum = Z0; qden = XH } x1 q0) heps2
    in
    let ExistT (x4, q5) = s2 in
    ExistT ((Nat.max x3 x4), (fun m n _ _ ->
    qltT_eq_compat_l
      (qabs
        (qplus (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n)))
          (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
      (qabs (qminus (exp_partial m (x0 m)) (exp_partial n (x0 n)))) eps
      (let htriT =
         qle_to_QleT'
           (qabs
             (qplus (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n)))
               (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
           (qplus
             (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
             (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
       in
       let ht1T =
         qleT'_trans
           (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
           (qmult (qabs (qminus (x0 m) (x0 n))) (exp_series m x1))
           (qmult (qabs (qminus (x0 m) (x0 n))) x2)
           (qle_to_QleT'
             (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
             (qmult (qabs (qminus (x0 m) (x0 n))) (exp_series m x1)))
           (qleT'_mult_compat_l (exp_series m x1) x2
             (qabs (qminus (x0 m) (x0 n)))
             (qabs_nonnegT (qminus (x0 m) (x0 n))) (q3 m))
       in
       let ht2T = q5 m n (natLe_lift x4 m) (natLe_lift x4 n) (x0 n) (q1 n) in
       let ht3T =
         qltT_leT'_ltT (qmult (qabs (qminus (x0 m) (x0 n))) x2)
           (qmult (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
             x2)
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
           (qltT_mult_ltT_compat_r (qabs (qminus (x0 m) (x0 n)))
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2)) x2
             hCposT (q4 m n (natLe_lift x3 m) (natLe_lift x3 n)))
           (qeq_leT'
             (qmult
               (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2)) x2)
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
       in
       qleT'_ltT_ltT
         (qabs
           (qplus (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n)))
             (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
         (qplus (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
           (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
         eps htriT
         (qltT_leT'_ltT
           (qplus
             (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
             (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
           (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
           eps
           (qltT_leT'_ltT
             (qplus
               (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
               (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
             (qplus (qmult (qabs (qminus (x0 m) (x0 n))) x2)
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
             (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
             (qleT'_plus_ltT_ltT
               (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
               (qmult (qabs (qminus (x0 m) (x0 n))) x2)
               (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n))))
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht1T ht2T)
             (qltT_leT'
               (qplus (qmult (qabs (qminus (x0 m) (x0 n))) x2)
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
               (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
               (qltT_plus_leT'_ltT (qmult (qabs (qminus (x0 m) (x0 n))) x2)
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht3T
                 (qleT'_refl (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })))))
           (qeq_leT'
             (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
             eps)))))))

(** val cauchy_real_exp_zero : real_eq **)

let cauchy_real_exp_zero eps _ =
  ExistT (O, (fun n _ ->
    qlt_to_QltT { qnum =
      (Z.abs
        (Z.add
          (Z.mul (exp_partial n { qnum = Z0; qden = XH }).qnum (Zpos XH))
          (Zneg (exp_partial n { qnum = Z0; qden = XH }).qden)));
      qden = (Coq_Pos.mul (exp_partial n { qnum = Z0; qden = XH }).qden XH) }
      eps))

(** val sum_upto : nat -> (nat -> q) -> q **)

let rec sum_upto n f =
  match n with
  | O -> { qnum = Z0; qden = XH }
  | S n' -> qplus (sum_upto n' f) (f n')

(** val exp_partial_tail_small :
    q -> q -> qleT' -> qleT' -> (nat, __) sigT **)

let exp_partial_tail_small m c _ _ =
  let s = q_arch_geom m in
  let ExistT (x, _) = s in
  let s0 =
    arch_decay
      (qmult (qdiv (q_pow m x) (q_fact x))
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH }))
      (qdiv { qnum = (Zpos XH); qden = XH } c)
      (qle_to_QleT' { qnum = Z0; qden = XH }
        (qmult (qdiv (q_pow m x) (q_fact x))
          (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
            XH })))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv { qnum = (Zpos XH); qden = XH } c))
  in
  let ExistT (x0, _) = s0 in ExistT ((add x (S x0)), __)

(** val cauchy_real_exp_pos : real -> real_lt **)

let cauchy_real_exp_pos = function
| ExistT (x0, c) ->
  let s = real_norm_bounded (ExistT (x0, c)) in
  let ExistT (x1, a) = s in
  let Pair (q0, _) = a in
  let s0 = exp_series_arch x1 (qltT_leT' { qnum = Z0; qden = XH } x1 q0) in
  let ExistT (x2, a0) = s0 in
  let Pair (q1, _) = a0 in
  let hCposT =
    qltT_leT'_ltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH } x2
      qltT_0_1 q1
  in
  let s1 =
    exp_partial_tail_small x1 x2 (qltT_leT' { qnum = Z0; qden = XH } x1 q0) q1
  in
  let ExistT (x3, _) = s1 in
  ExistT
  ((qdiv { qnum = (Zpos XH); qden = XH }
     (qmult { qnum = (Zpos (XO XH)); qden = XH } x2)),
  (Pair
  ((qltT_div_pos { qnum = (Zpos XH); qden = XH }
     (qmult { qnum = (Zpos (XO XH)); qden = XH } x2) qltT_0_1
     (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } x2 qltT_0_2
       hCposT)),
  (ExistT ((add (mul (S (S O)) x3) (S O)), (fun n _ ->
  qltT_eq_compat_r (qminus (exp_partial n (x0 n)) { qnum = Z0; qden = XH })
    (exp_partial n (x0 n))
    (qdiv { qnum = (Zpos XH); qden = XH }
      (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
    (qlt_to_QltT
      (qdiv { qnum = (Zpos XH); qden = XH }
        (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
      (exp_partial n (x0 n)))))))))

(** val real_abs : real -> real **)

let real_abs = function
| ExistT (x0, c) ->
  ExistT ((fun n -> qabs (x0 n)), (fun eps heps ->
    let s = c eps heps in
    let ExistT (x1, _) = s in
    ExistT (x1, (fun m n _ _ ->
    qlt_to_QltT (qabs (qminus (qabs (x0 m)) (qabs (x0 n)))) eps))))

(** val real_metric : real -> real -> real **)

let real_metric x y =
  real_abs (real_plus x (real_opp y))

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

  (** val real_eq_abs_compat : real -> real -> real_eq -> real_eq **)

  let real_eq_abs_compat a b hab eps heps =
    let s = hab eps heps in
    let ExistT (x, _) = s in
    ExistT (x, (fun k _ ->
    qlt_to_QltT
      (qabs (qminus (projT1 (real_abs a) k) (projT1 (real_abs b) k))) eps))

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

  (** val real_metric_sym : real -> real -> real_eq **)

  let real_metric_sym a b eps _ =
    ExistT (O, (fun k _ ->
      qlt_to_QltT
        (qabs
          (qminus (projT1 (real_metric a b) k) (projT1 (real_metric b a) k)))
        eps))

  (** val real_metric_zero : real -> real -> real_eq -> real_eq **)

  let real_metric_zero a b hab eps heps =
    let s = hab eps heps in
    let ExistT (x, _) = s in
    ExistT (x, (fun k _ ->
    qlt_to_QltT (qabs (qminus (projT1 a k) (projT1 b k))) eps))

  (** val real_metric_lt_const_to_minus :
      (nat -> real) -> nat -> nat -> q -> real_lt -> real_lt **)

  let real_metric_lt_const_to_minus u m n e = function
  | ExistT (x, a) ->
    let Pair (q0, s) = a in
    let ExistT (x0, _) = s in
    ExistT (x, (Pair (q0, (ExistT (x0, (fun k _ ->
    qlt_to_QltT x
      (qminus (projT1 (real_const e) k)
        (projT1 (real_plus (u m) (real_opp (u n))) k))))))))

  (** val real_metric_lt_const_to_minus_comm :
      (nat -> real) -> nat -> nat -> q -> real_lt -> real_lt **)

  let real_metric_lt_const_to_minus_comm u m n e = function
  | ExistT (x, a) ->
    let Pair (q0, s) = a in
    let ExistT (x0, _) = s in
    ExistT (x, (Pair (q0, (ExistT (x0, (fun k _ ->
    qlt_to_QltT x
      (qminus (projT1 (real_const e) k)
        (projT1 (real_plus (u n) (real_opp (u m))) k))))))))

  (** val real_cauchy_complete_metric :
      (nat -> real) -> (real -> real_lt -> (nat, nat -> nat -> __ -> __ ->
      real_lt) sigT) -> (real, real_lim) sigT **)

  let real_cauchy_complete_metric u hcau =
    real_cauchy_complete u (fun e _ ->
      let s =
        hcau (real_const e) (ExistT
          ((qdiv e { qnum = (Zpos (XO XH)); qden = XH }), (Pair
          ((qlt_to_QltT { qnum = Z0; qden = XH }
             (qdiv e { qnum = (Zpos (XO XH)); qden = XH })),
          (ExistT (O, (fun k _ ->
          qlt_to_QltT (qdiv e { qnum = (Zpos (XO XH)); qden = XH })
            (qminus (projT1 (real_const e) k) (projT1 real_zero k)))))))))
      in
      let ExistT (x, r) = s in
      ExistT (x, (fun m n _ _ -> Pair
      ((real_metric_lt_const_to_minus u m n e (r m n __ __)),
      (real_metric_lt_const_to_minus_comm u m n e (r m n __ __))))))

  (** val real_metric_pos_eps : real -> real -> real -> real_lt -> real_le **)

  let real_metric_pos_eps a b eps = function
  | ExistT (x, a0) ->
    let Pair (q0, s) = a0 in
    let ExistT (x0, _) = s in
    Inl (ExistT (x, (Pair (q0, (ExistT (x0, (fun n _ ->
    qlt_to_QltT x
      (qminus (projT1 (real_plus (real_metric a b) eps) n)
        (projT1 real_zero n)))))))))

  (** val real_metric_triangle_eps :
      real -> real -> real -> real -> real_lt -> real_le **)

  let real_metric_triangle_eps a b c eps = function
  | ExistT (x, a0) ->
    let Pair (q0, s) = a0 in
    let ExistT (x0, _) = s in
    Inl (ExistT (x, (Pair (q0, (ExistT (x0, (fun n _ ->
    qlt_to_QltT x
      (qminus
        (projT1
          (real_plus (real_plus (real_metric a b) (real_metric b c)) eps) n)
        (projT1 (real_metric a c) n)))))))))

  (** val eq_Id : 'a1 -> 'a1 -> 'a1 id **)

  let eq_Id _ _ =
    Id_refl

  (** val le_to_NatLe : nat -> nat -> natLe **)

  let le_to_NatLe n m =
    eq_Id (Nat.leb n m) True

  (** val real_cauchy_complete_metric_natle :
      (nat -> real) -> (real -> real_lt -> (nat, nat -> nat -> natLe -> natLe
      -> real_lt) sigT) -> (real, real_lim) sigT **)

  let real_cauchy_complete_metric_natle u hcau =
    real_cauchy_complete_metric u (fun eps heps ->
      let s = hcau eps heps in
      let ExistT (x, r) = s in
      ExistT (x, (fun m n _ _ -> r m n (le_to_NatLe x m) (le_to_NatLe x n))))

  (** val real_eq_plus_compat_adapt :
      real -> real -> real -> real -> real_eq -> real_eq -> real_eq **)

  let real_eq_plus_compat_adapt x1 x2 y1 y2 h12 h34 =
    real_eq_plus_compat x1 y1 x2 y2 h12 h34

  (** val real_eq_mult_compat_adapt :
      real -> real -> real -> real -> real_eq -> real_eq -> real_eq **)

  let real_eq_mult_compat_adapt x1 x2 y1 y2 h12 h34 =
    real_eq_mult_compat x1 y1 x2 y2 h12 h34
 end

(** val exp_trunc_arch_seq :
    (nat -> q) -> (nat -> q) -> q -> q -> qleT' -> (nat -> qleT') -> (nat ->
    qleT') -> qltT -> (nat, nat -> __ -> qltT) sigT **)

let exp_trunc_arch_seq u v b eps hB _ _ _ =
  let s = exp_series_arch b hB in
  let ExistT (x, _) = s in
  let s0 = q_arch_geom b in
  let ExistT (x0, _) = s0 in
  let s1 =
    arch_decay
      (qmult (qdiv (q_pow b x0) (q_fact x0))
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH }))
      (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x))
      (qle_to_QleT' { qnum = Z0; qden = XH }
        (qmult (qdiv (q_pow b x0) (q_fact x0))
          (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
            XH })))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x)))
  in
  let ExistT (x1, _) = s1 in
  ExistT ((add x0 (S x1)), (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus
        (sum_upto (S (mul (S (S O)) n)) (fun j ->
          sum_upto (S (sub (mul (S (S O)) n) j)) (fun i ->
            qmult (qdiv (q_pow (u n) j) (q_fact j))
              (qdiv (q_pow (v n) i) (q_fact i)))))
        (sum_upto (S n) (fun j ->
          sum_upto (S n) (fun i ->
            qmult (qdiv (q_pow (u n) j) (q_fact j))
              (qdiv (q_pow (v n) i) (q_fact i)))))))
    eps))

(** val cauchy_real_exp_plus : real -> real -> real_eq **)

let cauchy_real_exp_plus x y eps heps =
  let ExistT (x0, c) = x in
  let ExistT (x1, c0) = y in
  let s = real_norm_bounded (ExistT (x0, c)) in
  let ExistT (x2, a) = s in
  let Pair (q0, q1) = a in
  let s0 = real_norm_bounded (ExistT (x1, c0)) in
  let ExistT (x3, a0) = s0 in
  let Pair (q2, q3) = a0 in
  let m = qplus x2 x3 in
  let hMposT = qltT_plus_pos_r x2 x3 q0 q2 in
  let hMnonnegT = qltT_leT' { qnum = Z0; qden = XH } m hMposT in
  let huMT = fun n ->
    qleT'_trans (qabs (x0 n)) x2 (qplus x2 x3) (q1 n)
      (qleT'_plus_nonneg_rT x2 x3 (qltT_leT' { qnum = Z0; qden = XH } x3 q2))
  in
  let hvMT = fun n ->
    qleT'_trans (qabs (x1 n)) x3 (qplus x2 x3) (q3 n)
      (qleT'_trans x3 (qplus x3 x2) (qplus x2 x3)
        (qleT'_plus_nonneg_rT x3 x2
          (qltT_leT' { qnum = Z0; qden = XH } x2 q0))
        (qle_to_QleT' (qplus x3 x2) (qplus x2 x3)))
  in
  let heps3T =
    qltT_div_pos eps { qnum = (Zpos (XI XH)); qden = XH } heps qltT_0_3
  in
  let s1 =
    exp_partial_cauchy_bounded m
      (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }) hMnonnegT heps3T
  in
  let ExistT (x4, _) = s1 in
  let s2 =
    exp_trunc_arch_seq x0 x1 m
      (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }) hMnonnegT huMT hvMT
      heps3T
  in
  let ExistT (x5, _) = s2 in
  ExistT ((Nat.max x4 x5), (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus
        (projT1
          (cauchy_real_exp (real_plus (ExistT (x0, c)) (ExistT (x1, c0)))) n)
        (projT1
          (real_mult (cauchy_real_exp (ExistT (x0, c)))
            (cauchy_real_exp (ExistT (x1, c0))))
          n)))
    eps))

(** val cauchy_real_exp_gt_one : real -> real_lt -> real_lt **)

let cauchy_real_exp_gt_one t = function
| ExistT (x, a) ->
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in
  ExistT (x, (Pair (q0, (ExistT ((Nat.max x0 (S O)), (fun n _ ->
  qlt_to_QltT x (qminus (projT1 (cauchy_real_exp t) n) (projT1 real_one n))))))))

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

(** val cauchy_real_exp_minus_one_pos : real -> real_lt -> real_lt **)

let cauchy_real_exp_minus_one_pos t ht =
  let r = cauchy_real_exp_gt_one t ht in
  let ExistT (x, a) = r in
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in
  ExistT (x, (Pair (q0, (ExistT (x0, (fun n _ ->
  qlt_to_QltT x
    (qminus (projT1 (real_plus (cauchy_real_exp t) (real_opp real_one)) n)
      (projT1 real_zero n))))))))

(** val cauchy_real_exp_wd : real -> real -> real_eq -> real_eq **)

let cauchy_real_exp_wd a b hab eps heps =
  let s = real_norm_bounded a in
  let ExistT (x, a0) = s in
  let Pair (q0, _) = a0 in
  let s0 = real_norm_bounded b in
  let ExistT (x0, a1) = s0 in
  let Pair (q1, _) = a1 in
  let m = qplus x x0 in
  let hMposT = qltT_plus_pos_r x x0 q0 q1 in
  let hMnonnegT = qltT_leT' { qnum = Z0; qden = XH } m hMposT in
  let s1 = exp_series_arch m hMnonnegT in
  let ExistT (x1, a2) = s1 in
  let Pair (q2, _) = a2 in
  let hCposT =
    qltT_leT'_ltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH } x1
      qltT_0_1 q2
  in
  let hepsC =
    qltT_div_pos eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x1) heps
      (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } x1 qltT_0_2
        hCposT)
  in
  let s2 =
    hab (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x1)) hepsC
  in
  let ExistT (x2, _) = s2 in
  let heps2T =
    qltT_div_pos eps { qnum = (Zpos (XO XH)); qden = XH } heps qltT_0_2
  in
  let s3 =
    exp_partial_cauchy_bounded m
      (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hMnonnegT heps2T
  in
  let ExistT (x3, _) = s3 in
  ExistT ((Nat.max x2 x3), (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus (projT1 (cauchy_real_exp a) n) (projT1 (cauchy_real_exp b) n)))
    eps))

(** val real_mult_minus_factor : real -> real -> real_eq **)

let real_mult_minus_factor a b =
  real_eq_of_zero_diff (real_plus (real_mult a b) (real_opp a))
    (real_mult a (real_plus b (real_opp real_one)))

(** val cauchy_real_exp_mono : real -> real -> real_lt -> real_lt **)

let cauchy_real_exp_mono x y hxy =
  let hdiff = real_lt_opp_plus x y hxy in
  let hminus = cauchy_real_exp_minus_one_pos (real_plus y (real_opp x)) hdiff
  in
  let hprod =
    real_mult_pos_compat (cauchy_real_exp x)
      (real_plus (cauchy_real_exp (real_plus y (real_opp x)))
        (real_opp real_one))
      (cauchy_real_exp_pos x) hminus
  in
  let hxyeq = real_eq_of_zero_diff y (real_plus x (real_plus y (real_opp x)))
  in
  let hewd =
    cauchy_real_exp_wd y (real_plus x (real_plus y (real_opp x))) hxyeq
  in
  let heplus = cauchy_real_exp_plus x (real_plus y (real_opp x)) in
  let hmain =
    real_eq_trans (cauchy_real_exp y)
      (cauchy_real_exp (real_plus x (real_plus y (real_opp x))))
      (real_mult (cauchy_real_exp x)
        (cauchy_real_exp (real_plus y (real_opp x))))
      hewd heplus
  in
  let hdiffeq =
    real_eq_trans
      (real_plus (cauchy_real_exp y) (real_opp (cauchy_real_exp x)))
      (real_plus
        (real_mult (cauchy_real_exp x)
          (cauchy_real_exp (real_plus y (real_opp x))))
        (real_opp (cauchy_real_exp x)))
      (real_mult (cauchy_real_exp x)
        (real_plus (cauchy_real_exp (real_plus y (real_opp x)))
          (real_opp real_one)))
      (RealSetoid.real_eq_plus_compat (cauchy_real_exp y)
        (real_opp (cauchy_real_exp x))
        (real_mult (cauchy_real_exp x)
          (cauchy_real_exp (real_plus y (real_opp x))))
        (real_opp (cauchy_real_exp x)) hmain
        (real_eq_refl (real_opp (cauchy_real_exp x))))
      (real_mult_minus_factor (cauchy_real_exp x)
        (cauchy_real_exp (real_plus y (real_opp x))))
  in
  let hposdiff =
    real_lt_eq_lt real_zero
      (real_mult (cauchy_real_exp x)
        (real_plus (cauchy_real_exp (real_plus y (real_opp x)))
          (real_opp real_one)))
      (real_plus (cauchy_real_exp y) (real_opp (cauchy_real_exp x))) hprod
      (real_eq_sym
        (real_plus (cauchy_real_exp y) (real_opp (cauchy_real_exp x)))
        (real_mult (cauchy_real_exp x)
          (real_plus (cauchy_real_exp (real_plus y (real_opp x)))
            (real_opp real_one)))
        hdiffeq)
  in
  let ExistT (x0, a) = hposdiff in
  let Pair (q0, s) = a in
  let ExistT (x1, _) = s in
  ExistT (x0, (Pair (q0, (ExistT (x1, (fun n _ ->
  qlt_to_QltT x0
    (qminus (projT1 (cauchy_real_exp y) n) (projT1 (cauchy_real_exp x) n))))))))

(** val real_arch : real -> (nat, (__, real_lt) and0) sigT **)

let real_arch b =
  let s = real_norm_bounded b in
  let ExistT (x, _) = s in
  let s0 = q_arch_geom x in
  let ExistT (x0, _) = s0 in
  ExistT ((add x0 (S (S O))), (Pair (__, (ExistT
  ((qdiv (qminus { qnum = (Z.of_nat (add x0 (S (S O)))); qden = XH } x)
     { qnum = (Zpos (XO XH)); qden = XH }),
  (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv (qminus { qnum = (Z.of_nat (add x0 (S (S O)))); qden = XH } x)
       { qnum = (Zpos (XO XH)); qden = XH })),
  (ExistT (O, (fun k _ ->
  qlt_to_QltT
    (qdiv (qminus { qnum = (Z.of_nat (add x0 (S (S O)))); qden = XH } x)
      { qnum = (Zpos (XO XH)); qden = XH })
    (qminus
      (projT1
        (real_const { qnum = (Z.of_nat (add x0 (S (S O)))); qden = XH }) k)
      (projT1 b k))))))))))))

(** val cauchy_real_exp_gt_const : nat -> real_lt **)

let cauchy_real_exp_gt_const n =
  ExistT
    ((qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
       XH }),
    (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
         XH })),
    (ExistT ((S O), (fun n0 _ ->
    qlt_to_QltT
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH })
      (qminus
        (projT1
          (cauchy_real_exp (real_const { qnum = (Z.of_nat n); qden = XH }))
          n0)
        (projT1 (real_const { qnum = (Z.of_nat n); qden = XH }) n0))))))))

(** val real_abs_diff_le_lift : real -> real -> q -> q -> nat -> real_lt **)

let real_abs_diff_le_lift a b m _UU03b3_ _ =
  let hg4 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv _UU03b3_ { qnum = (Zpos (XO (XO XH))); qden = XH })
  in
  let s =
    projT2 a (qdiv _UU03b3_ { qnum = (Zpos (XO (XO XH))); qden = XH }) hg4
  in
  let ExistT (x, _) = s in
  let s0 =
    projT2 b (qdiv _UU03b3_ { qnum = (Zpos (XO (XO XH))); qden = XH }) hg4
  in
  let ExistT (x0, _) = s0 in
  ExistT ((qdiv _UU03b3_ { qnum = (Zpos (XO XH)); qden = XH }), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv _UU03b3_ { qnum = (Zpos (XO XH)); qden = XH })),
  (ExistT ((Nat.max x x0), (fun n _ ->
  qlt_to_QltT (qdiv _UU03b3_ { qnum = (Zpos (XO XH)); qden = XH })
    (qminus (projT1 (real_const (qplus m _UU03b3_)) n)
      (projT1 (real_abs (real_plus a (real_opp b))) n))))))))

(** val real_inv_unique :
    real -> real -> real -> real_eq -> real_eq -> real_eq **)

let real_inv_unique a b c hab hac =
  real_eq_trans b (real_mult b real_one) c
    (real_eq_sym (real_mult b real_one) b (real_mult_one b))
    (real_eq_trans (real_mult b real_one) (real_mult b (real_mult a c)) c
      (RealSetoid.real_eq_mult_compat b real_one b (real_mult a c)
        (real_eq_refl b) (real_eq_sym (real_mult a c) real_one hac))
      (real_eq_trans (real_mult b (real_mult a c))
        (real_mult (real_mult b a) c) c (real_mult_assoc b a c)
        (real_eq_trans (real_mult (real_mult b a) c)
          (real_mult (real_mult a b) c) c
          (RealSetoid.real_eq_mult_compat (real_mult b a) c (real_mult a b) c
            (real_mult_comm b a) (real_eq_refl c))
          (real_eq_trans (real_mult (real_mult a b) c) (real_mult real_one c)
            c
            (RealSetoid.real_eq_mult_compat (real_mult a b) c real_one c hab
              (real_eq_refl c))
            (real_eq_trans (real_mult real_one c) (real_mult c real_one) c
              (real_mult_comm real_one c) (real_mult_one c))))))

(** val exp_neg_recip : real -> real_lt -> real_eq **)

let exp_neg_recip x hx =
  real_inv_unique (cauchy_real_exp x) (cauchy_real_exp (real_opp x))
    (real_inv_pos (cauchy_real_exp x) hx)
    (real_eq_trans
      (real_mult (cauchy_real_exp x) (cauchy_real_exp (real_opp x)))
      (cauchy_real_exp (real_plus x (real_opp x))) real_one
      (real_eq_sym (cauchy_real_exp (real_plus x (real_opp x)))
        (real_mult (cauchy_real_exp x) (cauchy_real_exp (real_opp x)))
        (cauchy_real_exp_plus x (real_opp x)))
      (real_eq_trans (cauchy_real_exp (real_plus x (real_opp x)))
        (cauchy_real_exp real_zero) real_one
        (cauchy_real_exp_wd (real_plus x (real_opp x)) real_zero
          (real_eq_of_zero_diff (real_plus x (real_opp x)) real_zero))
        cauchy_real_exp_zero))
    (real_inv_pos_correct (cauchy_real_exp x) hx)

(** val real_const_pos : q -> qltT -> real_lt **)

let real_const_pos c _ =
  ExistT ((qdiv c { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv c { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (O, (fun n _ ->
    qlt_to_QltT (qdiv c { qnum = (Zpos (XO XH)); qden = XH })
      (qminus (projT1 (real_const c) n) (projT1 real_zero n))))))))

(** val real_inv_lt_contra :
    real -> real -> real_lt -> real_lt -> real_lt -> real_lt **)

let real_inv_lt_contra a b ha hb hab =
  let ExistT (x, a0) = ha in
  let Pair (q0, s) = a0 in
  let ExistT (x0, q1) = s in
  let ExistT (x1, a1) = hb in
  let Pair (q2, s0) = a1 in
  let ExistT (x2, q3) = s0 in
  let ExistT (x3, a2) = hab in
  let Pair (_, s1) = a2 in
  let ExistT (x4, _) = s1 in
  let s2 = real_norm_bounded a in
  let ExistT (x5, _) = s2 in
  let s3 = real_norm_bounded b in
  let ExistT (x6, _) = s3 in
  ExistT ((qdiv x3 (qmult x5 x6)), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qdiv x3 (qmult x5 x6))), (ExistT
  ((Nat.max (Nat.max x0 x2) x4), (fun n _ ->
  qlt_to_QltT (qdiv x3 (qmult x5 x6))
    (qminus
      (projT1 (real_inv_pos a (ExistT (x, (Pair (q0, (ExistT (x0, q1))))))) n)
      (projT1 (real_inv_pos b (ExistT (x1, (Pair (q2, (ExistT (x2, q3)))))))
        n))))))))

(** val q_eps16_posT : q -> qltT **)

let q_eps16_posT eps =
  qlt_to_QltT { qnum = Z0; qden = XH }
    (qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH })

(** val log_testA_eps : real -> q -> q -> q -> bool **)

let log_testA_eps y a b eps =
  let m = qdiv (qplus a b) { qnum = (Zpos (XO XH)); qden = XH } in
  let d4 = qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH } in
  let k1 = projT1 (exp_partial_cauchy m d4) in
  let k2 = projT1 (projT2 y d4 (q_eps16_posT eps)) in
  qlt_bool
    (qplus (exp_partial k1 m) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    (projT1 y k2)

(** val log_testB_eps : real -> q -> q -> q -> bool **)

let log_testB_eps y a b eps =
  let m = qdiv (qplus a b) { qnum = (Zpos (XO XH)); qden = XH } in
  let d4 = qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH } in
  let k1 = projT1 (exp_partial_cauchy m d4) in
  let k2 = projT1 (projT2 y d4 (q_eps16_posT eps)) in
  qlt_bool
    (qplus (projT1 y k2) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    (exp_partial k1 m)

(** val log_m_eps : q -> q -> q **)

let log_m_eps a b =
  qdiv (qplus a b) { qnum = (Zpos (XO XH)); qden = XH }

(** val log_d4_eps : q -> q **)

let log_d4_eps eps =
  qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH }

(** val log_K1_eps : q -> q -> q -> nat **)

let log_K1_eps a b eps =
  projT1 (exp_partial_cauchy (log_m_eps a b) (log_d4_eps eps))

(** val log_K2_eps : real -> q -> q -> q -> nat **)

let log_K2_eps y _ _ eps =
  projT1 (projT2 y (log_d4_eps eps) (q_eps16_posT eps))

(** val log_q_eps : q -> q -> q -> q **)

let log_q_eps a b eps =
  exp_partial (log_K1_eps a b eps) (log_m_eps a b)

(** val log_r_eps : real -> q -> q -> q -> q **)

let log_r_eps y a b eps =
  projT1 y (log_K2_eps y a b eps)

(** val log_testA_eps_true_lt : real -> q -> q -> q -> real_lt **)

let log_testA_eps_true_lt y a b eps =
  let d4 = log_d4_eps eps in
  let k1 = log_K1_eps a b eps in
  let k2 = log_K2_eps y a b eps in
  let q0 = log_q_eps a b eps in
  let r = log_r_eps y a b eps in
  let heps4 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qminus (qminus r q0) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
  in
  ExistT
  ((qminus (qminus r q0) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4)),
  (Pair (heps4, (ExistT ((Nat.max k1 k2), (fun n _ ->
  qlt_to_QltT
    (qminus (qminus r q0) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    (qminus (projT1 y n)
      (projT1 (cauchy_real_exp (real_const (log_m_eps a b))) n))))))))

(** val log_testB_eps_true_gt : real -> q -> q -> q -> real_lt **)

let log_testB_eps_true_gt y a b eps =
  let d4 = log_d4_eps eps in
  let k1 = log_K1_eps a b eps in
  let k2 = log_K2_eps y a b eps in
  let q0 = log_q_eps a b eps in
  let r = log_r_eps y a b eps in
  let heps4 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qminus (qminus q0 r) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
  in
  ExistT
  ((qminus (qminus q0 r) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4)),
  (Pair (heps4, (ExistT ((Nat.max k1 k2), (fun n _ ->
  qlt_to_QltT
    (qminus (qminus q0 r) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    (qminus (projT1 (cauchy_real_exp (real_const (log_m_eps a b))) n)
      (projT1 y n))))))))

(** val log_scan :
    real -> q -> q -> q -> nat -> (((q, q) prod, qltT) sigT, bool) prod **)

let rec log_scan y a b eps = function
| O -> Pair ((ExistT ((Pair (a, b)), (qlt_to_QltT a b))), True)
| S n' ->
  let m = log_m_eps a b in
  (match log_testA_eps y a b eps with
   | True -> log_scan y m b eps n'
   | False ->
     (match log_testB_eps y a b eps with
      | True -> log_scan y a m eps n'
      | False -> Pair ((ExistT ((Pair (a, b)), (qlt_to_QltT a b))), False)))

(** val log_scan_spec :
    real -> q -> q -> q -> nat -> real_lt -> real_lt -> ((bool id, (real_lt,
    (real_lt, qeqT) and0) and0) and0, (bool id, nat -> __ -> qleT') and0) or0 **)

let rec log_scan_spec y a b eps n hla hrb =
  match n with
  | O ->
    Inl (Pair (Id_refl, (Pair (hla, (Pair (hrb,
      (qeq_imp_qeqT (qminus b a)
        (qmult (qminus b a) { qnum = (Zpos XH); qden = XH }))))))))
  | S n0 ->
    let b0 = log_testA_eps y a b eps in
    (match b0 with
     | True ->
       let hmb = log_testA_eps_true_lt y a b eps in
       let hIH = log_scan_spec y (log_m_eps a b) b eps n0 hmb hrb in
       (match hIH with
        | Inl a0 ->
          Inl
            (let Pair (i, a1) = a0 in
             let Pair (r, a2) = a1 in
             let Pair (r0, _) = a2 in
             Pair (i, (Pair (r, (Pair (r0,
             (qeq_imp_qeqT
               (qminus
                 (snd (projT1 (fst (log_scan y (log_m_eps a b) b eps n0))))
                 (fst (projT1 (fst (log_scan y (log_m_eps a b) b eps n0)))))
               (qmult (qminus b a)
                 (q_pow
                   (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                     XH)); qden = XH })
                   (S n0))))))))))
        | Inr a0 -> Inr a0)
     | False ->
       let b1 = log_testB_eps y a b eps in
       (match b1 with
        | True ->
          let ham = log_testB_eps_true_gt y a b eps in
          let hIH = log_scan_spec y a (log_m_eps a b) eps n0 hla ham in
          (match hIH with
           | Inl a0 ->
             Inl
               (let Pair (i, a1) = a0 in
                let Pair (r, a2) = a1 in
                let Pair (r0, _) = a2 in
                Pair (i, (Pair (r, (Pair (r0,
                (qeq_imp_qeqT
                  (qminus
                    (snd (projT1 (fst (log_scan y a (log_m_eps a b) eps n0))))
                    (fst (projT1 (fst (log_scan y a (log_m_eps a b) eps n0)))))
                  (qmult (qminus b a)
                    (q_pow
                      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos
                        (XO XH)); qden = XH })
                      (S n0))))))))))
           | Inr a0 -> Inr a0)
        | False ->
          Inr (Pair (Id_refl, (fun k _ ->
            qle_to_QleT'
              (qabs
                (qminus
                  (projT1
                    (cauchy_real_exp
                      (real_const
                        (log_m_eps
                          (fst
                            (projT1
                              (fst (Pair ((ExistT ((Pair (a, b)),
                                (qlt_to_QltT a b))), False)))))
                          (snd
                            (projT1
                              (fst (Pair ((ExistT ((Pair (a, b)),
                                (qlt_to_QltT a b))), False))))))))
                    k)
                  (projT1 y k)))
              (qmult { qnum = (Zpos (XO (XO XH))); qden = XH }
                (log_d4_eps eps)))))))

(** val exp_lower_q : real -> real_lt -> (nat, (__, real_lt) and0) sigT **)

let exp_lower_q y = function
| ExistT (x, a) ->
  let Pair (_, s) = a in
  let ExistT (x0, _) = s in
  let h2e =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)
  in
  let hcst = real_const_pos (qdiv { qnum = (Zpos (XO XH)); qden = XH } x) h2e
  in
  let s0 =
    real_arch (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
  in
  let ExistT (x1, a0) = s0 in
  let Pair (_, r) = a0 in
  let hexpN =
    real_lt_trans (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
      (real_const { qnum = (Z.of_nat x1); qden = XH })
      (cauchy_real_exp (real_const { qnum = (Z.of_nat x1); qden = XH })) r
      (cauchy_real_exp_gt_const x1)
  in
  let hexpNpos =
    cauchy_real_exp_pos (real_const { qnum = (Z.of_nat x1); qden = XH })
  in
  ExistT (x1, (Pair (__,
  (real_eq_lt_lt
    (cauchy_real_exp (real_const (qopp { qnum = (Z.of_nat x1); qden = XH })))
    (cauchy_real_exp
      (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH })))
    y
    (cauchy_real_exp_wd
      (real_const (qopp { qnum = (Z.of_nat x1); qden = XH }))
      (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH }))
      (real_eq_of_zero_diff
        (real_const (qopp { qnum = (Z.of_nat x1); qden = XH }))
        (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH }))))
    (real_lt_trans
      (cauchy_real_exp
        (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH })))
      (real_inv_pos
        (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)) hcst)
      y
      (real_eq_lt_lt
        (cauchy_real_exp
          (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH })))
        (real_inv_pos
          (cauchy_real_exp (real_const { qnum = (Z.of_nat x1); qden = XH }))
          hexpNpos)
        (real_inv_pos
          (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)) hcst)
        (exp_neg_recip (real_const { qnum = (Z.of_nat x1); qden = XH })
          hexpNpos)
        (real_inv_lt_contra
          (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
          (cauchy_real_exp (real_const { qnum = (Z.of_nat x1); qden = XH }))
          hcst hexpNpos hexpN))
      (real_eq_lt_lt
        (real_inv_pos
          (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)) hcst)
        (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH })) y
        (real_inv_unique
          (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
          (real_inv_pos
            (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)) hcst)
          (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH }))
          (real_inv_pos_correct
            (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)) hcst)
          (real_eq_of_zero_diff
            (real_mult
              (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
              (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH })))
            real_one))
        (ExistT ((qdiv x { qnum = (Zpos (XO XH)); qden = XH }), (Pair
        ((qlt_to_QltT { qnum = Z0; qden = XH }
           (qdiv x { qnum = (Zpos (XO XH)); qden = XH })),
        (ExistT (x0, (fun n _ ->
        qlt_to_QltT (qdiv x { qnum = (Zpos (XO XH)); qden = XH })
          (qminus (projT1 y n)
            (projT1
              (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH })) n)))))))))))))))

(** val exp_upper_q : real -> real_lt -> (nat, (__, real_lt) and0) sigT **)

let exp_upper_q y _ =
  let s = real_arch y in
  let ExistT (x, a) = s in
  let Pair (_, r) = a in
  ExistT (x, (Pair (__,
  (real_lt_trans y (real_const { qnum = (Z.of_nat x); qden = XH })
    (cauchy_real_exp (real_const { qnum = (Z.of_nat x); qden = XH })) r
    (cauchy_real_exp_gt_const x)))))

(** val log_lower : real -> real_lt -> q **)

let log_lower y hy =
  qopp { qnum = (Z.of_nat (projT1 (exp_lower_q y hy))); qden = XH }

(** val log_upper : real -> real_lt -> q **)

let log_upper y hy =
  { qnum = (Z.of_nat (projT1 (exp_upper_q y hy))); qden = XH }

(** val q_pow_arch : q -> q -> (nat, __) sigT **)

let q_pow_arch d eps =
  let s =
    arch_decay d eps (qle_to_QleT' { qnum = Z0; qden = XH } d)
      (qlt_to_QltT { qnum = Z0; qden = XH } eps)
  in
  let ExistT (x, _) = s in ExistT ((S x), __)

(** val real_const_lt : q -> q -> real_lt **)

let real_const_lt c d =
  ExistT ((qdiv (qminus d c) { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv (qminus d c) { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (O, (fun n _ ->
    qlt_to_QltT (qdiv (qminus d c) { qnum = (Zpos (XO XH)); qden = XH })
      (qminus (projT1 (real_const d) n) (projT1 (real_const c) n))))))))

(** val real_lt_pt_lt : real -> real -> real_lt -> (nat, __) sigT **)

let real_lt_pt_lt _ _ = function
| ExistT (_, a) ->
  let Pair (_, s) = a in let ExistT (x, _) = s in ExistT (x, __)

(** val exp_const_lt : q -> q -> real_lt **)

let exp_const_lt a b =
  cauchy_real_exp_mono (real_const a) (real_const b) (real_const_lt a b)

(** val approx_span_pt :
    real -> q -> q -> q -> q -> real_lt -> real_lt -> (nat -> qleT') -> (nat,
    __) sigT **)

let approx_span_pt y a b _ _ hla hrb _ =
  let m = log_m_eps a b in
  let heam = exp_const_lt a (log_m_eps a b) in
  let hemb = exp_const_lt (log_m_eps a b) b in
  let s = real_lt_pt_lt (cauchy_real_exp (real_const a)) y hla in
  let ExistT (x, _) = s in
  let s0 = real_lt_pt_lt y (cauchy_real_exp (real_const b)) hrb in
  let ExistT (x0, _) = s0 in
  let s1 =
    real_lt_pt_lt (cauchy_real_exp (real_const a))
      (cauchy_real_exp (real_const m)) heam
  in
  let ExistT (x1, _) = s1 in
  let s2 =
    real_lt_pt_lt (cauchy_real_exp (real_const m))
      (cauchy_real_exp (real_const b)) hemb
  in
  let ExistT (x2, _) = s2 in
  ExistT ((Nat.max (Nat.max x x0) (Nat.max x1 x2)), __)

(** val real_abs_lift : q -> real -> q -> q -> nat -> real_lt **)

let real_abs_lift m y m0 _UU03b3_ n0 =
  real_abs_diff_le_lift (cauchy_real_exp (real_const m)) y m0 _UU03b3_ n0

(** val approx_def_test : real -> q -> q -> nat -> real_lt **)

let approx_def_test y mN eps n0 =
  let hlift =
    real_abs_lift mN y
      (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } (log_d4_eps eps))
      (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }) n0
  in
  real_lt_trans
    (real_abs (real_plus (cauchy_real_exp (real_const mN)) (real_opp y)))
    (real_const
      (qplus
        (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } (log_d4_eps eps))
        (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH })))
    (real_const eps) hlift
    (real_const_lt
      (qplus
        (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } (log_d4_eps eps))
        (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }))
      eps)

(** val approx_root :
    real -> real_lt -> q -> (q, (qltT, (qltT, real_lt) and0) and0) sigT **)

let approx_root y hy eps =
  let s = exp_lower_q y hy in
  let ExistT (x, a) = s in
  let Pair (_, r) = a in
  let s0 = exp_upper_q y hy in
  let ExistT (x0, a0) = s0 in
  let Pair (_, r0) = a0 in
  let a1 = qopp { qnum = (Z.of_nat x); qden = XH } in
  let b0 = { qnum = (Z.of_nat x0); qden = XH } in
  let b = qplus (qabs a1) (qabs b0) in
  let s1 = exp_series_arch b (qle_to_QleT' { qnum = Z0; qden = XH } b) in
  let ExistT (x1, a2) = s1 in
  let Pair (_, q0) = a2 in
  let d = qmult (qminus b0 a1) x1 in
  let s2 = q_pow_arch d eps in
  let ExistT (x2, _) = s2 in
  let o = log_scan_spec y a1 b0 eps x2 r r0 in
  (match o with
   | Inl a3 ->
     let Pair (_, a4) = a3 in
     let Pair (r1, a5) = a4 in
     let Pair (r2, _) = a5 in
     let abN = projT1 (fst (log_scan y a1 b0 eps x2)) in
     let aN = fst abN in
     let bN = snd abN in
     let mN = log_m_eps aN bN in
     let s3 = approx_span_pt y aN bN b x1 r1 r2 q0 in
     let ExistT (x3, _) = s3 in
     ExistT (mN, (Pair
     ((qlt_to_QltT (qopp { qnum = (Z.of_nat x); qden = XH }) mN), (Pair
     ((qlt_to_QltT mN { qnum = (Z.of_nat x0); qden = XH }),
     (let hlift =
        real_abs_lift mN y (qmult (qminus bN aN) x1)
          (qdiv
            (qminus eps
              (qmult d
                (q_pow
                  (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                    XH)); qden = XH })
                  x2)))
            { qnum = (Zpos (XO XH)); qden = XH })
          x3
      in
      real_lt_trans
        (real_abs (real_plus (cauchy_real_exp (real_const mN)) (real_opp y)))
        (real_const
          (qplus (qmult (qminus bN aN) x1)
            (qdiv
              (qminus eps
                (qmult d
                  (q_pow
                    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                      XH)); qden = XH })
                    x2)))
              { qnum = (Zpos (XO XH)); qden = XH })))
        (real_const eps) hlift
        (real_const_lt
          (qplus (qmult (qminus bN aN) x1)
            (qdiv
              (qminus eps
                (qmult d
                  (q_pow
                    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                      XH)); qden = XH })
                    x2)))
              { qnum = (Zpos (XO XH)); qden = XH }))
          eps)))))))
   | Inr _ ->
     let abN = projT1 (fst (log_scan y a1 b0 eps x2)) in
     let mN = log_m_eps (fst abN) (snd abN) in
     let n0 =
       Nat.max (log_K1_eps (fst abN) (snd abN) eps)
         (log_K2_eps y (fst abN) (snd abN) eps)
     in
     ExistT (mN, (Pair
     ((qlt_to_QltT (qopp { qnum = (Z.of_nat x); qden = XH }) mN), (Pair
     ((qlt_to_QltT mN { qnum = (Z.of_nat x0); qden = XH }),
     (approx_def_test y mN eps n0)))))))

(** val log_eps : nat -> q **)

let log_eps n =
  q_pow
    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
      XH })
    (S n)

(** val log_seq : real -> real_lt -> nat -> q **)

let log_seq y hy n =
  projT1 (approx_root y hy (log_eps n))

(** val approx_root_pt_bound : real -> real_lt -> nat -> (nat, __) sigT **)

let approx_root_pt_bound y hy n =
  let s = approx_root y hy (log_eps n) in
  let ExistT (x, a) = s in
  let Pair (_, a0) = a in
  let Pair (_, r) = a0 in
  let s0 =
    real_lt_pt_lt
      (real_abs (real_plus (cauchy_real_exp (real_const x)) (real_opp y)))
      (real_const (log_eps n)) r
  in
  let ExistT (x0, _) = s0 in ExistT (x0, __)

(** val exp_pos_shape :
    real -> (q, (qltT, (nat, nat -> __ -> qltT) sigT) and0) sigT **)

let exp_pos_shape x =
  let r = cauchy_real_exp_pos x in
  let ExistT (x0, a) = r in
  let Pair (q0, s) = a in
  let ExistT (x1, q1) = s in
  ExistT (x0, (Pair (q0, (ExistT (x1, (fun n _ -> q1 n (natLe_lift x1 n)))))))

(** val log_seq_cauchy : real -> real_lt -> cauchy **)

let log_seq_cauchy y hy eps _ =
  let a0 = log_lower y hy in
  let s = exp_pos_shape (real_const a0) in
  let ExistT (x, _) = s in
  let delta =
    qdiv (qmult eps x) { qnum = (Zpos (XO (XO (XO XH)))); qden = XH }
  in
  let s0 = q_pow_arch { qnum = (Zpos XH); qden = XH } delta in
  let ExistT (x0, _) = s0 in
  ExistT ((S x0), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (log_seq y hy m) (log_seq y hy n))) eps))

(** val cw_log : real -> real_lt -> real **)

let cw_log y hy =
  ExistT ((log_seq y hy), (log_seq_cauchy y hy))

(** val exp_series_arch_shape :
    q -> qleT' -> (q, (qleT', nat -> qleT') and0) sigT **)

let exp_series_arch_shape =
  exp_series_arch

(** val cw_log_exp_right : real -> real_lt -> real_eq **)

let cw_log_exp_right y hy gamma _ =
  let s =
    exp_series_arch_shape
      (qplus (qabs (log_lower y hy)) (qabs (log_upper y hy)))
      (qle_to_QleT' { qnum = Z0; qden = XH }
        (qplus (qabs (log_lower y hy)) (qabs (log_upper y hy))))
  in
  let ExistT (x, _) = s in
  let hcau =
    log_seq_cauchy y hy
      (qdiv gamma
        (qmult { qnum = (Zpos (XO (XO XH))); qden = XH }
          (qplus x { qnum = (Zpos XH); qden = XH })))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv gamma
          (qmult { qnum = (Zpos (XO (XO XH))); qden = XH }
            (qplus x { qnum = (Zpos XH); qden = XH }))))
  in
  let ExistT (x0, _) = hcau in
  let s0 =
    q_pow_arch { qnum = (Zpos XH); qden = XH }
      (qdiv gamma { qnum = (Zpos (XO (XO XH))); qden = XH })
  in
  let ExistT (x1, _) = s0 in
  let n0 = Nat.max x0 (S x1) in
  let happrox = approx_root_pt_bound y hy n0 in
  let ExistT (x2, _) = happrox in
  ExistT ((Nat.max n0 x2), (fun k _ ->
  qlt_to_QltT
    (qabs (qminus (projT1 (cauchy_real_exp (cw_log y hy)) k) (projT1 y k)))
    gamma))

(** val real_lt_not_eq : real -> real -> real_lt -> real_eq not **)

let real_lt_not_eq _ _ _ _ =
  assert false (* absurd case *)

(** val real_weak_trich :
    real -> real -> real_lt not -> real_lt not -> real_eq **)

let real_weak_trich x y _ _ eps _ =
  let heps3 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv eps { qnum = (Zpos (XI XH)); qden = XH })
  in
  let s = projT2 x (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }) heps3 in
  let ExistT (x0, _) = s in
  let s0 = projT2 y (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }) heps3 in
  let ExistT (x1, _) = s0 in
  let n = Nat.max x0 x1 in
  let hmain = fun n0 ->
    let s1 = qlt_le_dec (qabs (qminus (projT1 x n0) (projT1 y n0))) eps in
    (match s1 with
     | Left -> qlt_to_QltT (qabs (qminus (projT1 x n0) (projT1 y n0))) eps
     | Right -> assert false (* absurd case *))
  in
  ExistT (n, (fun n0 _ -> hmain n0))

(** val log_inv_one_thm : real_lt -> real_eq **)

let log_inv_one_thm h =
  let u = cw_log real_one h in
  let hright = cw_log_exp_right real_one h in
  real_weak_trich u real_zero (fun hult ->
    real_lt_not_eq (cauchy_real_exp u) (cauchy_real_exp real_zero)
      (cauchy_real_exp_mono u real_zero hult)
      (real_eq_trans (cauchy_real_exp u) real_one (cauchy_real_exp real_zero)
        hright
        (real_eq_sym (cauchy_real_exp real_zero) real_one
          cauchy_real_exp_zero)))
    (fun h0lt ->
    real_lt_not_eq (cauchy_real_exp real_zero) (cauchy_real_exp u)
      (cauchy_real_exp_mono real_zero u h0lt)
      (real_eq_trans (cauchy_real_exp real_zero) real_one (cauchy_real_exp u)
        cauchy_real_exp_zero
        (real_eq_sym (cauchy_real_exp u) real_one hright)))

(** val log_inv_mult_thm :
    real -> real -> real_lt -> real_lt -> real_lt -> real_eq **)

let log_inv_mult_thm a b ha hb hab =
  let l = cw_log (real_mult a b) hab in
  let r = real_plus (cw_log a ha) (cw_log b hb) in
  let hL = cw_log_exp_right (real_mult a b) hab in
  let hplus = cauchy_real_exp_plus (cw_log a ha) (cw_log b hb) in
  let hRa = cw_log_exp_right a ha in
  let hRb = cw_log_exp_right b hb in
  let hR =
    real_eq_trans (cauchy_real_exp r)
      (real_mult (cauchy_real_exp (cw_log a ha))
        (cauchy_real_exp (cw_log b hb)))
      (real_mult a b) hplus
      (RealSetoid.real_eq_mult_compat (cauchy_real_exp (cw_log a ha))
        (cauchy_real_exp (cw_log b hb)) a b hRa hRb)
  in
  real_weak_trich l r (fun hLlt ->
    real_lt_not_eq (cauchy_real_exp l) (cauchy_real_exp r)
      (cauchy_real_exp_mono l r hLlt)
      (real_eq_trans (cauchy_real_exp l) (real_mult a b) (cauchy_real_exp r)
        hL (real_eq_sym (cauchy_real_exp r) (real_mult a b) hR)))
    (fun hRlt ->
    real_lt_not_eq (cauchy_real_exp r) (cauchy_real_exp l)
      (cauchy_real_exp_mono r l hRlt)
      (real_eq_trans (cauchy_real_exp r) (real_mult a b) (cauchy_real_exp l)
        hR (real_eq_sym (cauchy_real_exp l) (real_mult a b) hL)))

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

(** val real_log_lt_mono :
    real -> real -> real_lt -> real_lt -> real_lt -> real_lt **)

let real_log_lt_mono a b ha hb = function
| ExistT (x, _) ->
  let b0 =
    qplus
      (qplus (qplus (qabs (log_lower a ha)) (qabs (log_upper a ha)))
        (qabs (log_lower b hb)))
      (qabs (log_upper b hb))
  in
  let s = exp_series_arch_shape b0 (qle_to_QleT' { qnum = Z0; qden = XH } b0)
  in
  let ExistT (x0, _) = s in
  let s0 =
    q_pow_arch { qnum = (Zpos XH); qden = XH }
      (qdiv x { qnum = (Zpos (XO (XO (XO XH)))); qden = XH })
  in
  let ExistT (x1, _) = s0 in
  let s1 =
    log_seq_cauchy b hb
      (qdiv x (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH } x0))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv x (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH } x0)))
  in
  let ExistT (x2, _) = s1 in
  let s2 =
    log_seq_cauchy a ha
      (qdiv x (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH } x0))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv x (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH } x0)))
  in
  let ExistT (x3, _) = s2 in
  let n0 = Nat.max (S x1) (Nat.max x2 x3) in
  ExistT ((qdiv x (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } x0)),
  (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv x (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } x0))),
  (ExistT ((Nat.max (Nat.max x2 x3) n0), (fun n _ ->
  qlt_to_QltT (qdiv x (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } x0))
    (qminus (projT1 (cw_log b hb) n) (projT1 (cw_log a ha) n))))))))

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

(** val real_opp_lt_compat : real -> real -> real_lt -> real_lt **)

let real_opp_lt_compat a b = function
| ExistT (x, a0) ->
  let Pair (q0, s) = a0 in
  let ExistT (x0, _) = s in
  ExistT (x, (Pair (q0, (ExistT (x0, (fun n _ ->
  qlt_to_QltT x (qminus (projT1 (real_opp a) n) (projT1 (real_opp b) n))))))))

(** val real_lt_zero_opp : real -> real_lt -> real_lt **)

let real_lt_zero_opp a ha =
  real_lt_eq_lt (real_opp a) (real_opp real_zero) real_zero
    (real_opp_lt_compat real_zero a ha)
    (real_eq_of_zero_diff (real_opp real_zero) real_zero)

(** val real_opp_le_compat : real -> real -> real_le -> real_le **)

let real_opp_le_compat a b = function
| Inl r ->
  RealSetoid.real_lt_le_iff_req (real_opp b) (real_opp a) (Inl
    (real_opp_lt_compat a b r))
| Inr r ->
  RealSetoid.real_eq_le (real_opp b) (real_opp a)
    (RealSetoid.real_eq_opp_compat b a (real_eq_sym a b r))

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

(** val real_plus_positive : real -> real -> real_lt -> real_lt -> real_lt **)

let real_plus_positive a b ha hb =
  real_eq_lt_lt real_zero (real_plus real_zero real_zero) (real_plus a b)
    (real_eq_sym (real_plus real_zero real_zero) real_zero
      (real_eq_of_zero_diff (real_plus real_zero real_zero) real_zero))
    (real_lt_plus_compat real_zero a real_zero b ha hb)

(** val real_mult_positive : real -> real -> real_lt -> real_lt -> real_lt **)

let real_mult_positive a b ha hb =
  real_eq_lt_lt real_zero (real_mult real_zero b) (real_mult a b)
    (real_eq_sym (real_mult real_zero b) real_zero
      (real_eq_trans (real_mult real_zero b) (real_mult b real_zero)
        real_zero (real_mult_comm real_zero b) (real_mult_zero b)))
    (real_mult_lt_compat real_zero a b ha hb)

(** val real_min : real -> real -> real **)

let real_min a b =
  let ExistT (x, c) = a in
  let ExistT (x0, c0) = b in
  ExistT ((fun n -> qmin (x n) (x0 n)), (fun eps _ ->
  let hhalf =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
  in
  let s = c (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf in
  let ExistT (x1, _) = s in
  let s0 = c0 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf in
  let ExistT (x2, _) = s0 in
  ExistT ((Nat.max x1 x2), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (qmin (x m) (x0 m)) (qmin (x n) (x0 n)))) eps))))

(** val real_max : real -> real -> real **)

let real_max a b =
  let ExistT (x, c) = a in
  let ExistT (x0, c0) = b in
  ExistT ((fun n -> qmax (x n) (x0 n)), (fun eps _ ->
  let hhalf =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
  in
  let s = c (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf in
  let ExistT (x1, _) = s in
  let s0 = c0 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf in
  let ExistT (x2, _) = s0 in
  ExistT ((Nat.max x1 x2), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (qmax (x m) (x0 m)) (qmax (x n) (x0 n)))) eps))))

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

(** val real_abs_nonneg_le_eps : real -> real -> real_lt -> real_le **)

let real_abs_nonneg_le_eps a eps = function
| ExistT (x, a0) ->
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  RealSetoid.real_lt_le_iff_req real_zero (real_plus (real_abs a) eps) (Inl
    (ExistT ((qdiv x { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv x { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (x0, (fun n _ ->
    qlt_to_QltT (qdiv x { qnum = (Zpos (XO XH)); qden = XH })
      (qminus (projT1 (real_plus (real_abs a) eps) n) (projT1 real_zero n))))))))))

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

(** val real_eps_witness :
    real -> real_lt -> (q, (qltT, (nat, nat -> __ -> qltT) sigT) and0) sigT **)

let real_eps_witness eps = function
| ExistT (x, a) ->
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in
  ExistT (x, (Pair (q0, (ExistT (x0, (fun n _ ->
  qlt_to_QltT (qdiv x { qnum = (Zpos (XO XH)); qden = XH }) (projT1 eps n)))))))

(** val real_min_le_l_eps : real -> real -> real -> real_lt -> real_le **)

let real_min_le_l_eps a b eps heps =
  let s = real_eps_witness eps heps in
  let ExistT (x, a0) = s in
  let Pair (_, s0) = a0 in
  let ExistT (x0, _) = s0 in
  RealSetoid.real_lt_le_iff_req (real_min a b) (real_plus a eps) (Inl (ExistT
    ((qdiv x { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv x { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (x0, (fun n _ ->
    qlt_to_QltT (qdiv x { qnum = (Zpos (XO XH)); qden = XH })
      (qminus (projT1 (real_plus a eps) n) (projT1 (real_min a b) n))))))))))

(** val real_min_le_r_eps : real -> real -> real -> real_lt -> real_le **)

let real_min_le_r_eps a b eps heps =
  let s = real_eps_witness eps heps in
  let ExistT (x, a0) = s in
  let Pair (_, s0) = a0 in
  let ExistT (x0, _) = s0 in
  RealSetoid.real_lt_le_iff_req (real_min a b) (real_plus b eps) (Inl (ExistT
    ((qdiv x { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv x { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (x0, (fun n _ ->
    qlt_to_QltT (qdiv x { qnum = (Zpos (XO XH)); qden = XH })
      (qminus (projT1 (real_plus b eps) n) (projT1 (real_min a b) n))))))))))

(** val real_min_pos : real -> real -> real_lt -> real_lt -> real_lt **)

let real_min_pos a b ha hb =
  let ExistT (x, a0) = ha in
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  let ExistT (x1, a1) = hb in
  let Pair (_, s0) = a1 in
  let ExistT (x2, _) = s0 in
  let e = qmin x x1 in
  let he = qlt_to_QltT { qnum = Z0; qden = XH } e in
  ExistT (e, (Pair (he, (ExistT ((Nat.max x0 x2), (fun n _ ->
  qlt_to_QltT e (qminus (projT1 (real_min a b) n) (projT1 real_zero n))))))))

(** val real_r_max_le_l_eps : real -> real -> real -> real_lt -> real_le **)

let real_r_max_le_l_eps a b eps heps =
  let s = real_eps_witness eps heps in
  let ExistT (x, a0) = s in
  let Pair (_, s0) = a0 in
  let ExistT (x0, _) = s0 in
  RealSetoid.real_lt_le_iff_req a (real_plus (real_max a b) eps) (Inl (ExistT
    ((qdiv x { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv x { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (x0, (fun n _ ->
    qlt_to_QltT (qdiv x { qnum = (Zpos (XO XH)); qden = XH })
      (qminus (projT1 (real_plus (real_max a b) eps) n) (projT1 a n))))))))))

(** val real_r_max_le_r_eps : real -> real -> real -> real_lt -> real_le **)

let real_r_max_le_r_eps a b eps heps =
  let s = real_eps_witness eps heps in
  let ExistT (x, a0) = s in
  let Pair (_, s0) = a0 in
  let ExistT (x0, _) = s0 in
  RealSetoid.real_lt_le_iff_req b (real_plus (real_max a b) eps) (Inl (ExistT
    ((qdiv x { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv x { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (x0, (fun n _ ->
    qlt_to_QltT (qdiv x { qnum = (Zpos (XO XH)); qden = XH })
      (qminus (projT1 (real_plus (real_max a b) eps) n) (projT1 b n))))))))))

(** val real_r_max_l_iff : real -> real -> real_le -> real_eq **)

let real_r_max_l_iff a b hba eps heps =
  match hba with
  | Inl r ->
    let ExistT (_, a0) = r in
    let Pair (_, s) = a0 in
    let ExistT (x, _) = s in
    ExistT (x, (fun n _ ->
    qlt_to_QltT (qabs (qminus (projT1 (real_max a b) n) (projT1 a n))) eps))
  | Inr r ->
    let s = r eps heps in
    let ExistT (x, _) = s in
    ExistT (x, (fun n _ ->
    qlt_to_QltT (qabs (qminus (projT1 (real_max a b) n) (projT1 a n))) eps))

(** val real_pos_part : real -> real **)

let real_pos_part a =
  real_max a real_zero

(** val real_pos_part_def : real -> real_eq **)

let real_pos_part_def a =
  real_eq_refl (real_max a real_zero)

(** val real_pos_part_nonneg_eps : real -> real -> real_lt -> real_le **)

let real_pos_part_nonneg_eps a eps heps =
  real_r_max_le_r_eps a real_zero eps heps

(** val real_r_if : ('a1, 'a1 not) or0 -> real -> real -> real **)

let real_r_if hd v_true v_false =
  match hd with
  | Inl _ -> v_true
  | Inr _ -> v_false

(** val real_r_if_true :
    ('a1, 'a1 not) or0 -> real -> real -> 'a1 -> real_eq **)

let real_r_if_true hd v_true _ _ =
  match hd with
  | Inl _ -> real_eq_refl v_true
  | Inr _ -> assert false (* absurd case *)

(** val real_r_if_false :
    ('a1, 'a1 not) or0 -> real -> real -> 'a1 not -> real_eq **)

let real_r_if_false hd _ v_false _ =
  match hd with
  | Inl _ -> assert false (* absurd case *)
  | Inr _ -> real_eq_refl v_false

(** val real_exp_neg : real -> real **)

let real_exp_neg x =
  cauchy_real_exp (real_opp x)

(** val real_exp_neg_pos : real -> real_lt **)

let real_exp_neg_pos x =
  cauchy_real_exp_pos (real_opp x)

(** val real_exp_neg_zero : real_eq **)

let real_exp_neg_zero =
  real_eq_trans (cauchy_real_exp (real_opp real_zero))
    (cauchy_real_exp real_zero) real_one
    (cauchy_real_exp_wd (real_opp real_zero) real_zero
      (real_eq_of_zero_diff (real_opp real_zero) real_zero))
    cauchy_real_exp_zero

(** val real_opp_plus : real -> real -> real_eq **)

let real_opp_plus a b =
  real_eq_of_zero_diff (real_opp (real_plus a b))
    (real_plus (real_opp a) (real_opp b))

(** val real_exp_neg_plus : real -> real -> real_eq **)

let real_exp_neg_plus a b =
  real_eq_trans (cauchy_real_exp (real_opp (real_plus a b)))
    (cauchy_real_exp (real_plus (real_opp a) (real_opp b)))
    (real_mult (cauchy_real_exp (real_opp a)) (cauchy_real_exp (real_opp b)))
    (cauchy_real_exp_wd (real_opp (real_plus a b))
      (real_plus (real_opp a) (real_opp b)) (real_opp_plus a b))
    (cauchy_real_exp_plus (real_opp a) (real_opp b))

(** val real_exp_neg_decr : real -> real -> real_lt -> real_lt **)

let real_exp_neg_decr a b hab =
  cauchy_real_exp_mono (real_opp b) (real_opp a) (real_opp_lt_compat a b hab)

(** val real_exp_neg_le_decr : real -> real -> real_le -> real_le **)

let real_exp_neg_le_decr a b = function
| Inl r ->
  RealSetoid.real_lt_le_iff_req (real_exp_neg b) (real_exp_neg a) (Inl
    (real_exp_neg_decr a b r))
| Inr r ->
  RealSetoid.real_eq_le (real_exp_neg b) (real_exp_neg a)
    (cauchy_real_exp_wd (real_opp b) (real_opp a)
      (RealSetoid.real_eq_opp_compat b a (real_eq_sym a b r)))

(** val real_log : real -> real_lt -> real **)

let real_log =
  cw_log

(** val real_log_mult : real -> real -> real_lt -> real_lt -> real_eq **)

let real_log_mult a b ha hb =
  log_inv_mult_thm a b ha hb (real_mult_positive a b ha hb)

(** val real_log_one : real_lt -> real_eq **)

let real_log_one =
  log_inv_one_thm

(** val real_log_inv : real -> real_lt -> real **)

let real_log_inv x hx =
  real_opp (cw_log x hx)

(** val real_log_inv_log : real -> real_lt -> real_eq **)

let real_log_inv_log x hx =
  real_eq_refl (real_opp (cw_log x hx))

(** val real_exp_neg_log_inv : real -> real_lt -> real_eq **)

let real_exp_neg_log_inv x hx =
  real_eq_trans (cauchy_real_exp (real_opp (real_opp (cw_log x hx))))
    (cauchy_real_exp (cw_log x hx)) x
    (cauchy_real_exp_wd (real_opp (real_opp (cw_log x hx))) (cw_log x hx)
      (real_eq_of_zero_diff (real_opp (real_opp (cw_log x hx))) (cw_log x hx)))
    (cw_log_exp_right x hx)

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

  (** val req_opp_compat :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 req -> 'a1 req **)

  let req_opp_compat realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.req_opp_compat

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

  (** val le_antisym :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 le -> 'a1 le
      -> 'a1 req **)

  let le_antisym realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.le_antisym

  (** val lt_le_iff :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> ('a1 lt, 'a1 req)
      or0 -> 'a1 le **)

  let lt_le_iff realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.lt_le_iff

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

  (** val mult_positive :
      'a1 coq_RealInterfaceEnhancedSetoid -> 'a1 -> 'a1 -> 'a1 lt -> 'a1 lt
      -> 'a1 lt **)

  let mult_positive realInterfaceEnhancedSetoid =
    realInterfaceEnhancedSetoid.mult_positive

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

  (** val real_r_max_r_iff : real -> real -> real_le -> real_eq **)

  let real_r_max_r_iff a b hab eps heps =
    match hab with
    | Inl r ->
      let ExistT (_, a0) = r in
      let Pair (_, s) = a0 in
      let ExistT (x, _) = s in
      ExistT (x, (fun n _ ->
      qlt_to_QltT (qabs (qminus (projT1 (real_max a b) n) (projT1 b n))) eps))
    | Inr r ->
      let s = r eps heps in
      let ExistT (x, _) = s in
      ExistT (x, (fun n _ ->
      qlt_to_QltT (qabs (qminus (projT1 (real_max a b) n) (projT1 b n))) eps))

  (** val real_exp_ge_linear_eps : real -> real -> real_lt -> real_le **)

  let real_exp_ge_linear_eps t eps heps =
    Inl
      (let ExistT (x, a) = heps in
       let Pair (_, s) = a in
       let ExistT (x0, _) = s in
       let s0 = real_norm_bounded t in
       let ExistT (x1, a0) = s0 in
       let Pair (q0, _) = a0 in
       let s1 = exp_series_arch x1 (qltT_leT' { qnum = Z0; qden = XH } x1 q0)
       in
       let ExistT (x2, a1) = s1 in
       let Pair (q1, _) = a1 in
       let s2 =
         exp_partial_tail_small x1 x2
           (qltT_leT' { qnum = Z0; qden = XH } x1 q0) q1
       in
       let ExistT (x3, _) = s2 in
       ExistT ((qdiv x { qnum = (Zpos (XO XH)); qden = XH }), (Pair
       ((qlt_to_QltT { qnum = Z0; qden = XH }
          (qdiv x { qnum = (Zpos (XO XH)); qden = XH })),
       (ExistT ((Nat.max x0 (add (mul (S (S O)) x3) (S (S (S O))))),
       (fun n _ ->
       qlt_to_QltT (qdiv x { qnum = (Zpos (XO XH)); qden = XH })
         (qminus (projT1 (real_plus (cauchy_real_exp t) eps) n)
           (projT1 (real_plus real_one t) n)))))))))

  (** val real_log_le_linear_eps :
      real -> real -> real_lt -> real_lt -> real_le **)

  let real_log_le_linear_eps x eps hx hepspos =
    let y = real_log x hx in
    let h_exp_log = cw_log_exp_right x hx in
    let hlin = real_exp_ge_linear_eps y eps hepspos in
    real_le_trans y
      (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one)) eps)
      (real_plus (real_plus x (real_opp real_one)) eps)
      (real_le_trans y (real_plus (real_plus real_one y) (real_opp real_one))
        (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one)) eps)
        (RealSetoid.real_eq_le y
          (real_plus (real_plus real_one y) (real_opp real_one))
          (real_eq_of_zero_diff y
            (real_plus (real_plus real_one y) (real_opp real_one))))
        (real_le_trans (real_plus (real_plus real_one y) (real_opp real_one))
          (real_plus (real_plus (cauchy_real_exp y) eps) (real_opp real_one))
          (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one)) eps)
          (real_le_plus_compat (real_plus real_one y)
            (real_plus (cauchy_real_exp y) eps) (real_opp real_one)
            (real_opp real_one) hlin (real_le_refl (real_opp real_one)))
          (RealSetoid.real_eq_le
            (real_plus (real_plus (cauchy_real_exp y) eps)
              (real_opp real_one))
            (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one))
              eps)
            (real_eq_trans
              (real_plus (real_plus (cauchy_real_exp y) eps)
                (real_opp real_one))
              (real_plus (cauchy_real_exp y)
                (real_plus eps (real_opp real_one)))
              (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one))
                eps)
              (real_eq_sym
                (real_plus (cauchy_real_exp y)
                  (real_plus eps (real_opp real_one)))
                (real_plus (real_plus (cauchy_real_exp y) eps)
                  (real_opp real_one))
                (real_plus_assoc (cauchy_real_exp y) eps (real_opp real_one)))
              (real_eq_trans
                (real_plus (cauchy_real_exp y)
                  (real_plus eps (real_opp real_one)))
                (real_plus (cauchy_real_exp y)
                  (real_plus (real_opp real_one) eps))
                (real_plus
                  (real_plus (cauchy_real_exp y) (real_opp real_one)) eps)
                (RealSetoid.real_eq_plus_compat (cauchy_real_exp y)
                  (real_plus eps (real_opp real_one)) (cauchy_real_exp y)
                  (real_plus (real_opp real_one) eps)
                  (real_eq_refl (cauchy_real_exp y))
                  (real_plus_comm eps (real_opp real_one)))
                (real_plus_assoc (cauchy_real_exp y) (real_opp real_one) eps))))))
      (real_le_plus_compat
        (real_plus (cauchy_real_exp y) (real_opp real_one))
        (real_plus x (real_opp real_one)) eps eps
        (real_le_plus_compat (cauchy_real_exp y) x (real_opp real_one)
          (real_opp real_one)
          (RealSetoid.real_eq_le (cauchy_real_exp y) x h_exp_log)
          (real_le_refl (real_opp real_one)))
        (real_le_refl eps))

  (** val coq_RealEnhancedReal : real coq_RealInterfaceEnhancedSetoid **)

  let coq_RealEnhancedReal =
    { req_refl = (Obj.magic real_eq_refl); req_sym = (Obj.magic real_eq_sym);
      req_trans = (Obj.magic real_eq_trans); zero = real_zero; one =
      real_one; plus = real_plus; mult = real_mult; opp = real_opp; abs =
      real_abs; req_plus_compat =
      (Obj.magic RealSetoid.real_eq_plus_compat_adapt); req_mult_compat =
      (Obj.magic RealSetoid.real_eq_mult_compat_adapt); req_opp_compat =
      (Obj.magic RealSetoid.real_eq_opp_compat); req_abs_compat =
      (Obj.magic RealSetoid.real_eq_abs_compat); req_lt_compat =
      (Obj.magic RealSetoid.real_lt_compat); req_le_compat =
      (Obj.magic RealSetoid.real_le_compat); plus_assoc =
      (Obj.magic real_plus_assoc); plus_comm = (Obj.magic real_plus_comm);
      plus_zero = (Obj.magic real_plus_zero); plus_opp =
      (Obj.magic real_plus_opp); mult_assoc = (Obj.magic real_mult_assoc);
      mult_comm = (Obj.magic real_mult_comm); mult_one =
      (Obj.magic real_mult_one); distrib = (Obj.magic real_distrib);
      mult_zero = (Obj.magic real_mult_zero); lt_irrefl =
      (Obj.magic real_lt_irrefl); lt_trans = (Obj.magic real_lt_trans);
      le_refl = (Obj.magic real_le_refl); le_trans =
      (Obj.magic real_le_trans); le_antisym = (Obj.magic real_le_antisym);
      le_lt_trans = (Obj.magic real_le_lt_trans); lt_le_trans =
      (Obj.magic real_lt_le_trans); lt_le_iff =
      (Obj.magic RealSetoid.real_lt_le_iff_req); le_id_l =
      (Obj.magic RealSetoid.real_le_id_l); le_id_r =
      (Obj.magic RealSetoid.real_le_id_r); lt_id_l =
      (Obj.magic RealSetoid.real_lt_id_l); lt_id_r =
      (Obj.magic RealSetoid.real_lt_id_r); inv_pos =
      (Obj.magic real_inv_pos); inv_pos_correct =
      (Obj.magic real_inv_pos_correct); one_pos =
      (Obj.magic real_lt_zero_one); lt_plus_compat =
      (Obj.magic real_lt_plus_compat); le_plus_compat =
      (Obj.magic real_le_plus_compat); plus_positive =
      (Obj.magic real_plus_positive); mult_positive =
      (Obj.magic real_mult_positive); lt_mult_compat = (fun a b c hc hab ->
      Obj.magic real_mult_lt_compat a b c hab hc); le_mult_compat =
      (Obj.magic real_le_mult_compat); le_mult_compat_weak =
      (Obj.magic real_le_mult_compat_weak); opp_lt_compat =
      (Obj.magic real_opp_lt_compat); lt_zero_opp =
      (Obj.magic real_lt_zero_opp); opp_le_compat =
      (Obj.magic real_opp_le_compat); inv_pos_pos =
      (Obj.magic real_inv_pos_pos); inv_pos_ext =
      (Obj.magic real_inv_pos_ext); inv_pos_le_compat =
      (Obj.magic real_inv_pos_le_compat); min = real_min; min_le_l =
      (Obj.magic real_min_le_l_eps); min_le_r =
      (Obj.magic real_min_le_r_eps); min_pos = (Obj.magic real_min_pos);
      r_max = real_max; r_max_le_l = (Obj.magic real_r_max_le_l_eps);
      r_max_le_r = (Obj.magic real_r_max_le_r_eps); r_max_l_iff =
      (Obj.magic real_r_max_l_iff); r_max_r_iff =
      (Obj.magic real_r_max_r_iff); pos_test_lt = (fun _ h -> h);
      lt_pos_test = (fun _ h -> h); pos_part = real_pos_part; pos_part_def =
      (Obj.magic real_pos_part_def); pos_part_nonneg =
      (Obj.magic real_pos_part_nonneg_eps); r_if = (fun _ -> real_r_if);
      r_if_true = (Obj.magic (fun _ -> real_r_if_true)); r_if_false =
      (Obj.magic (fun _ -> real_r_if_false)); abs_nonneg =
      (Obj.magic real_abs_nonneg_le_eps); abs_triangle =
      (Obj.magic real_abs_triangle_le_eps); abs_zero =
      (Obj.magic real_abs_zero_req); abs_mult =
      (Obj.magic real_abs_mult_req); abs_opp = (Obj.magic real_abs_opp);
      abs_pos = (Obj.magic real_abs_pos_req); exp_neg = real_exp_neg;
      exp_neg_pos = (Obj.magic real_exp_neg_pos); exp_neg_zero =
      (Obj.magic real_exp_neg_zero); exp_neg_plus =
      (Obj.magic real_exp_neg_plus); exp_neg_decr =
      (Obj.magic real_exp_neg_decr); exp_neg_le_decr =
      (Obj.magic real_exp_neg_le_decr); log = (Obj.magic real_log);
      log_mult = (Obj.magic real_log_mult); log_one =
      (Obj.magic real_log_one); log_le_linear_eps = (fun x hx eps hepspos ->
      Obj.magic real_log_le_linear_eps x eps hx hepspos); log_inv =
      (Obj.magic real_log_inv); log_inv_log = (Obj.magic real_log_inv_log);
      exp_neg_log_inv = (Obj.magic real_exp_neg_log_inv); metric =
      real_metric; metric_sym = (Obj.magic RealSetoid.real_metric_sym);
      metric_pos = (Obj.magic RealSetoid.real_metric_pos_eps); metric_zero =
      (Obj.magic RealSetoid.real_metric_zero); metric_triangle =
      (Obj.magic RealSetoid.real_metric_triangle_eps); lim_unique =
      (Obj.magic real_lim_unique); cauchy_complete =
      (Obj.magic RealSetoid.real_cauchy_complete_metric_natle) }
 end

(** val real_opp_mult : real -> real -> real_eq **)

let real_opp_mult a b =
  real_eq_of_zero_diff (real_opp (real_mult a b)) (real_mult a (real_opp b))

(** val real_mult_div : real -> real -> real_lt -> real_eq **)

let real_mult_div p q0 hp =
  real_eq_trans (real_mult p (real_mult q0 (real_inv_pos p hp)))
    (real_mult (real_mult p q0) (real_inv_pos p hp)) q0
    (real_mult_assoc p q0 (real_inv_pos p hp))
    (real_eq_trans (real_mult (real_mult p q0) (real_inv_pos p hp))
      (real_mult (real_mult q0 p) (real_inv_pos p hp)) q0
      (RealSetoid.real_eq_mult_compat (real_mult p q0) (real_inv_pos p hp)
        (real_mult q0 p) (real_inv_pos p hp) (real_mult_comm p q0)
        (real_eq_refl (real_inv_pos p hp)))
      (real_eq_trans (real_mult (real_mult q0 p) (real_inv_pos p hp))
        (real_mult q0 (real_mult p (real_inv_pos p hp))) q0
        (real_eq_sym (real_mult q0 (real_mult p (real_inv_pos p hp)))
          (real_mult (real_mult q0 p) (real_inv_pos p hp))
          (real_mult_assoc q0 p (real_inv_pos p hp)))
        (real_eq_trans (real_mult q0 (real_mult p (real_inv_pos p hp)))
          (real_mult q0 real_one) q0
          (RealSetoid.real_eq_mult_compat q0
            (real_mult p (real_inv_pos p hp)) q0 real_one (real_eq_refl q0)
            (real_inv_pos_correct p hp))
          (real_mult_one q0))))

(** val real_opp_opp : real -> real_eq **)

let real_opp_opp x =
  real_eq_of_zero_diff (real_opp (real_opp x)) x

(** val real_hpq1 : real -> real -> real_lt -> real_eq **)

let real_hpq1 p q0 hp =
  real_eq_sym
    (real_mult p
      (real_opp
        (real_plus (real_mult q0 (real_inv_pos p hp)) (real_opp real_one))))
    (real_plus p (real_opp q0))
    (let hmid =
       real_eq_trans
         (real_mult p
           (real_plus (real_mult q0 (real_inv_pos p hp)) (real_opp real_one)))
         (real_plus (real_mult p (real_mult q0 (real_inv_pos p hp)))
           (real_mult p (real_opp real_one)))
         (real_plus q0 (real_opp p))
         (real_distrib p (real_mult q0 (real_inv_pos p hp))
           (real_opp real_one))
         (real_eq_trans
           (real_plus (real_mult p (real_mult q0 (real_inv_pos p hp)))
             (real_mult p (real_opp real_one)))
           (real_plus q0 (real_opp (real_mult p real_one)))
           (real_plus q0 (real_opp p))
           (RealSetoid.real_eq_plus_compat
             (real_mult p (real_mult q0 (real_inv_pos p hp)))
             (real_mult p (real_opp real_one)) q0
             (real_opp (real_mult p real_one)) (real_mult_div p q0 hp)
             (real_eq_sym (real_opp (real_mult p real_one))
               (real_mult p (real_opp real_one)) (real_opp_mult p real_one)))
           (RealSetoid.real_eq_plus_compat q0
             (real_opp (real_mult p real_one)) q0 (real_opp p)
             (real_eq_refl q0)
             (RealSetoid.real_eq_opp_compat (real_mult p real_one) p
               (real_mult_one p))))
     in
     real_eq_trans
       (real_mult p
         (real_opp
           (real_plus (real_mult q0 (real_inv_pos p hp)) (real_opp real_one))))
       (real_opp
         (real_mult p
           (real_plus (real_mult q0 (real_inv_pos p hp)) (real_opp real_one))))
       (real_plus p (real_opp q0))
       (real_eq_sym
         (real_opp
           (real_mult p
             (real_plus (real_mult q0 (real_inv_pos p hp))
               (real_opp real_one))))
         (real_mult p
           (real_opp
             (real_plus (real_mult q0 (real_inv_pos p hp))
               (real_opp real_one))))
         (real_opp_mult p
           (real_plus (real_mult q0 (real_inv_pos p hp)) (real_opp real_one))))
       (real_eq_trans
         (real_opp
           (real_mult p
             (real_plus (real_mult q0 (real_inv_pos p hp))
               (real_opp real_one))))
         (real_opp (real_plus q0 (real_opp p))) (real_plus p (real_opp q0))
         (RealSetoid.real_eq_opp_compat
           (real_mult p
             (real_plus (real_mult q0 (real_inv_pos p hp))
               (real_opp real_one)))
           (real_plus q0 (real_opp p)) hmid)
         (real_eq_trans (real_opp (real_plus q0 (real_opp p)))
           (real_plus (real_opp q0) (real_opp (real_opp p)))
           (real_plus p (real_opp q0)) (real_opp_plus q0 (real_opp p))
           (real_eq_trans (real_plus (real_opp q0) (real_opp (real_opp p)))
             (real_plus (real_opp q0) p) (real_plus p (real_opp q0))
             (RealSetoid.real_eq_plus_compat (real_opp q0)
               (real_opp (real_opp p)) (real_opp q0) p
               (real_eq_refl (real_opp q0)) (real_opp_opp p))
             (real_plus_comm (real_opp q0) p)))))

(** val real_hpq2 : real -> real -> real -> real_lt -> real_eq **)

let real_hpq2 p q0 eps hp =
  real_eq_of_zero_diff
    (real_mult p
      (real_opp
        (real_plus (real_mult q0 (real_inv_pos p hp)) (real_opp real_one))))
    (real_plus
      (real_mult p
        (real_opp
          (real_plus
            (real_plus (real_mult q0 (real_inv_pos p hp)) (real_opp real_one))
            eps)))
      (real_mult p eps))

(** val real_gibbs_core_eps :
    real -> real -> real_lt -> real_lt -> real -> real_lt -> real_le **)

let real_gibbs_core_eps p q0 hp hq eps hepspos =
  let hlin =
    RealInterfaceEnhancedMod.real_log_le_linear_eps
      (real_mult q0 (real_inv_pos p hp)) eps
      (real_mult_positive q0 (real_inv_pos p hp) hq (real_inv_pos_pos p hp))
      hepspos
  in
  let hopp =
    real_opp_le_compat
      (real_log (real_mult q0 (real_inv_pos p hp))
        (real_mult_positive q0 (real_inv_pos p hp) hq (real_inv_pos_pos p hp)))
      (real_plus
        (real_plus (real_mult q0 (real_inv_pos p hp)) (real_opp real_one))
        eps)
      hlin
  in
  let hmult =
    real_le_mult_compat
      (real_opp
        (real_plus
          (real_plus (real_mult q0 (real_inv_pos p hp)) (real_opp real_one))
          eps))
      (real_opp
        (real_log (real_mult q0 (real_inv_pos p hp))
          (real_mult_positive q0 (real_inv_pos p hp) hq
            (real_inv_pos_pos p hp))))
      p hp hopp
  in
  real_le_trans (real_plus p (real_opp q0))
    (real_plus
      (real_mult p
        (real_opp
          (real_plus
            (real_plus (real_mult q0 (real_inv_pos p hp)) (real_opp real_one))
            eps)))
      (real_mult p eps))
    (real_plus
      (real_mult p
        (real_opp
          (real_log (real_mult q0 (real_inv_pos p hp))
            (real_mult_positive q0 (real_inv_pos p hp) hq
              (real_inv_pos_pos p hp)))))
      (real_mult p eps))
    (RealSetoid.real_eq_le (real_plus p (real_opp q0))
      (real_plus
        (real_mult p
          (real_opp
            (real_plus
              (real_plus (real_mult q0 (real_inv_pos p hp))
                (real_opp real_one))
              eps)))
        (real_mult p eps))
      (real_eq_trans (real_plus p (real_opp q0))
        (real_mult p
          (real_opp
            (real_plus (real_mult q0 (real_inv_pos p hp)) (real_opp real_one))))
        (real_plus
          (real_mult p
            (real_opp
              (real_plus
                (real_plus (real_mult q0 (real_inv_pos p hp))
                  (real_opp real_one))
                eps)))
          (real_mult p eps))
        (real_hpq1 p q0 hp) (real_hpq2 p q0 eps hp)))
    (real_le_plus_compat
      (real_mult p
        (real_opp
          (real_plus
            (real_plus (real_mult q0 (real_inv_pos p hp)) (real_opp real_one))
            eps)))
      (real_mult p
        (real_opp
          (real_log (real_mult q0 (real_inv_pos p hp))
            (real_mult_positive q0 (real_inv_pos p hp) hq
              (real_inv_pos_pos p hp)))))
      (real_mult p eps) (real_mult p eps)
      (RealSetoid.real_le_id_l
        (real_mult p
          (real_opp
            (real_plus
              (real_plus (real_mult q0 (real_inv_pos p hp))
                (real_opp real_one))
              eps)))
        (real_mult
          (real_opp
            (real_plus
              (real_plus (real_mult q0 (real_inv_pos p hp))
                (real_opp real_one))
              eps))
          p)
        (real_mult p
          (real_opp
            (real_log (real_mult q0 (real_inv_pos p hp))
              (real_mult_positive q0 (real_inv_pos p hp) hq
                (real_inv_pos_pos p hp)))))
        (real_mult_comm p
          (real_opp
            (real_plus
              (real_plus (real_mult q0 (real_inv_pos p hp))
                (real_opp real_one))
              eps)))
        (RealSetoid.real_le_id_r
          (real_mult
            (real_opp
              (real_plus
                (real_plus (real_mult q0 (real_inv_pos p hp))
                  (real_opp real_one))
                eps))
            p)
          (real_mult
            (real_opp
              (real_log (real_mult q0 (real_inv_pos p hp))
                (real_mult_positive q0 (real_inv_pos p hp) hq
                  (real_inv_pos_pos p hp))))
            p)
          (real_mult p
            (real_opp
              (real_log (real_mult q0 (real_inv_pos p hp))
                (real_mult_positive q0 (real_inv_pos p hp) hq
                  (real_inv_pos_pos p hp)))))
          (real_mult_comm
            (real_opp
              (real_log (real_mult q0 (real_inv_pos p hp))
                (real_mult_positive q0 (real_inv_pos p hp) hq
                  (real_inv_pos_pos p hp))))
            p)
          hmult))
      (real_le_refl (real_mult p eps)))

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

(** val real_kl_term : real -> real -> real_lt -> real_lt -> real **)

let real_kl_term p q0 hp hq =
  real_mult p
    (real_opp
      (real_log (real_mult q0 (real_inv_pos p hp))
        (real_mult_positive q0 (real_inv_pos p hp) hq (real_inv_pos_pos p hp))))

(** val real_gibbs_inequality_eps :
    'a1 list -> ('a1 -> real) -> ('a1 -> real) -> ('a1 -> real_lt) -> ('a1 ->
    real_lt) -> real_eq -> real_eq -> real -> real_lt -> real_le **)

let real_gibbs_inequality_eps l p q0 hp hq hnormp hnormq eps hepspos =
  let kLsum =
    real_list_sum (fun s -> real_kl_term (p s) (q0 s) (hp s) (hq s)) l
  in
  let sumPE = real_list_sum (fun s -> real_mult (p s) eps) l in
  let hsum =
    real_list_sum_le (fun s -> real_plus (p s) (real_opp (q0 s))) (fun s ->
      real_plus (real_kl_term (p s) (q0 s) (hp s) (hq s))
        (real_mult (p s) eps))
      l (fun s -> real_gibbs_core_eps (p s) (q0 s) (hp s) (hq s) eps hepspos)
  in
  let hzero =
    real_eq_trans
      (real_list_sum (fun s -> real_plus (p s) (real_opp (q0 s))) l)
      (real_plus (real_list_sum p l)
        (real_list_sum (fun s -> real_opp (q0 s)) l))
      real_zero (real_list_sum_add p (fun s -> real_opp (q0 s)) l)
      (real_eq_trans
        (real_plus (real_list_sum p l)
          (real_list_sum (fun s -> real_opp (q0 s)) l))
        (real_plus real_one (real_opp real_one)) real_zero
        (RealSetoid.real_eq_plus_compat (real_list_sum p l)
          (real_list_sum (fun s -> real_opp (q0 s)) l) real_one
          (real_opp real_one) hnormp
          (real_eq_trans (real_list_sum (fun s -> real_opp (q0 s)) l)
            (real_opp (real_list_sum q0 l)) (real_opp real_one)
            (real_list_sum_opp q0 l)
            (RealSetoid.real_eq_opp_compat (real_list_sum q0 l) real_one
              hnormq)))
        (real_plus_opp real_one))
  in
  let heps =
    real_eq_trans (real_list_sum (fun s -> real_mult (p s) eps) l)
      (real_mult eps (real_list_sum p l)) eps
      (real_list_sum_linear_r eps p l)
      (real_eq_trans (real_mult eps (real_list_sum p l))
        (real_mult eps real_one) eps
        (RealSetoid.real_eq_mult_compat eps (real_list_sum p l) eps real_one
          (real_eq_refl eps) hnormp)
        (real_mult_one eps))
  in
  let hadd =
    real_list_sum_add (fun s -> real_kl_term (p s) (q0 s) (hp s) (hq s))
      (fun s -> real_mult (p s) eps) l
  in
  let hsum2 =
    RealSetoid.real_le_id_r
      (real_list_sum (fun s -> real_plus (p s) (real_opp (q0 s))) l)
      (real_list_sum (fun s ->
        real_plus (real_kl_term (p s) (q0 s) (hp s) (hq s))
          (real_mult (p s) eps))
        l)
      (real_plus kLsum sumPE) hadd hsum
  in
  let hplus =
    RealSetoid.real_eq_plus_compat kLsum sumPE kLsum eps (real_eq_refl kLsum)
      heps
  in
  let hsum' =
    RealSetoid.real_le_id_r
      (real_list_sum (fun s -> real_plus (p s) (real_opp (q0 s))) l)
      (real_plus kLsum sumPE) (real_plus kLsum eps) hplus hsum2
  in
  real_le_trans real_zero
    (real_list_sum (fun s -> real_plus (p s) (real_opp (q0 s))) l)
    (real_plus kLsum eps)
    (RealSetoid.real_eq_le real_zero
      (real_list_sum (fun s -> real_plus (p s) (real_opp (q0 s))) l)
      (real_eq_sym
        (real_list_sum (fun s -> real_plus (p s) (real_opp (q0 s))) l)
        real_zero hzero))
    hsum'

(** val real_log_wd :
    real -> real -> real_lt -> real_lt -> real_eq -> real_eq **)

let real_log_wd a b ha hb hab =
  real_weak_trich (real_log a ha) (real_log b hb) (fun hLlt ->
    real_lt_not_eq (cauchy_real_exp (real_log a ha))
      (cauchy_real_exp (real_log b hb))
      (cauchy_real_exp_mono (real_log a ha) (real_log b hb) hLlt)
      (real_eq_trans (cauchy_real_exp (real_log a ha)) a
        (cauchy_real_exp (real_log b hb)) (cw_log_exp_right a ha)
        (real_eq_trans a b (cauchy_real_exp (real_log b hb)) hab
          (real_eq_sym (cauchy_real_exp (real_log b hb)) b
            (cw_log_exp_right b hb)))))
    (fun hRlt ->
    real_lt_not_eq (cauchy_real_exp (real_log b hb))
      (cauchy_real_exp (real_log a ha))
      (cauchy_real_exp_mono (real_log b hb) (real_log a ha) hRlt)
      (real_eq_trans (cauchy_real_exp (real_log b hb)) b
        (cauchy_real_exp (real_log a ha)) (cw_log_exp_right b hb)
        (real_eq_trans b a (cauchy_real_exp (real_log a ha))
          (real_eq_sym a b hab)
          (real_eq_sym (cauchy_real_exp (real_log a ha)) a
            (cw_log_exp_right a ha)))))

(** val real_distrib_r_local : real -> real -> real -> real_eq **)

let real_distrib_r_local x y z0 =
  real_eq_trans (real_plus (real_mult x z0) (real_mult y z0))
    (real_plus (real_mult z0 x) (real_mult z0 y))
    (real_mult (real_plus x y) z0)
    (RealSetoid.real_eq_plus_compat (real_mult x z0) (real_mult y z0)
      (real_mult z0 x) (real_mult z0 y) (real_mult_comm x z0)
      (real_mult_comm y z0))
    (real_eq_trans (real_plus (real_mult z0 x) (real_mult z0 y))
      (real_mult z0 (real_plus x y)) (real_mult (real_plus x y) z0)
      (real_eq_sym (real_mult z0 (real_plus x y))
        (real_plus (real_mult z0 x) (real_mult z0 y)) (real_distrib z0 x y))
      (real_mult_comm z0 (real_plus x y)))

(** val real_boltzmann_dist_r :
    ('a1 -> real) -> real -> real_lt -> real -> real_lt -> 'a1 -> real **)

let real_boltzmann_dist_r real_base_loss d d_pos z_align_r z_align_r_pos s =
  real_mult (real_inv_pos z_align_r z_align_r_pos)
    (real_exp_neg (real_mult (real_inv_pos d d_pos) (real_base_loss s)))

(** val real_boltzmann_dist_r_pos :
    ('a1 -> real) -> real -> real_lt -> real -> real_lt -> 'a1 -> real_lt **)

let real_boltzmann_dist_r_pos real_base_loss d d_pos z_align_r z_align_r_pos s =
  real_mult_positive (real_inv_pos z_align_r z_align_r_pos)
    (real_exp_neg (real_mult (real_inv_pos d d_pos) (real_base_loss s)))
    (real_inv_pos_pos z_align_r z_align_r_pos)
    (real_exp_neg_pos (real_mult (real_inv_pos d d_pos) (real_base_loss s)))

(** val real_lt_le_bridge : real -> real -> real_lt -> real_le **)

let real_lt_le_bridge _ _ h =
  Inl h

(** val real_eq_le_bridge : real -> real -> real_eq -> real_le **)

let real_eq_le_bridge _ _ h =
  Inr h

(** val real_log_le_mono :
    real -> real -> real_lt -> real_lt -> real_le -> real_le **)

let real_log_le_mono a b ha hb = function
| Inl r ->
  real_lt_le_bridge (real_log a ha) (real_log b hb)
    (real_log_lt_mono a b ha hb r)
| Inr r ->
  real_eq_le_bridge (real_log a ha) (real_log b hb) (real_log_wd a b ha hb r)

type real_le_b = real -> real_lt -> real_lt

(** val real_lt_plus_r_zero : real -> real -> real_lt -> real_lt **)

let real_lt_plus_r_zero y eps heps =
  RealSetoid.real_lt_id_l y (real_plus y real_zero) (real_plus y eps)
    (real_eq_sym (real_plus y real_zero) y (real_plus_zero y))
    (real_lt_plus_translate y real_zero eps heps)

(** val real_le_closure_b :
    real -> real -> real -> real_lt -> (real -> real_lt -> real_le) ->
    real_le_b **)

let real_le_closure_b x y d hD h eps' heps' =
  let hD2 = real_plus_positive d d hD hD in
  let hinv2pos = real_inv_pos_pos (real_plus d d) hD2 in
  let he0pos =
    real_mult_positive eps' (real_inv_pos (real_plus d d) hD2) heps' hinv2pos
  in
  let hkey =
    let hDlt =
      RealSetoid.real_lt_id_l d (real_plus d real_zero) (real_plus d d)
        (real_eq_sym (real_plus d real_zero) d (real_plus_zero d))
        (real_lt_plus_translate d real_zero d hD)
    in
    let hmono = real_inv_pos_lt_contra d (real_plus d d) hD hD2 hDlt in
    let hm1 =
      real_mult_lt_compat (real_inv_pos (real_plus d d) hD2)
        (real_inv_pos d hD) d hmono hD
    in
    let heq1 =
      real_eq_trans (real_mult (real_inv_pos d hD) d)
        (real_mult d (real_inv_pos d hD)) real_one
        (real_mult_comm (real_inv_pos d hD) d) (real_inv_pos_correct d hD)
    in
    let hlt2 =
      RealSetoid.real_lt_id_r
        (real_mult (real_inv_pos (real_plus d d) hD2) d)
        (real_mult (real_inv_pos d hD) d) real_one heq1 hm1
    in
    let hlt3 =
      real_mult_lt_compat_l (real_mult (real_inv_pos (real_plus d d) hD2) d)
        real_one eps' hlt2 heps'
    in
    let hlt4 =
      RealSetoid.real_lt_id_r
        (real_mult eps' (real_mult (real_inv_pos (real_plus d d) hD2) d))
        (real_mult eps' real_one) eps' (real_mult_one eps') hlt3
    in
    let hC1 =
      real_eq_trans
        (real_mult d (real_mult eps' (real_inv_pos (real_plus d d) hD2)))
        (real_mult (real_mult d eps') (real_inv_pos (real_plus d d) hD2))
        (real_mult eps' (real_mult (real_inv_pos (real_plus d d) hD2) d))
        (real_mult_assoc d eps' (real_inv_pos (real_plus d d) hD2))
        (real_eq_trans
          (real_mult (real_mult d eps') (real_inv_pos (real_plus d d) hD2))
          (real_mult (real_mult eps' d) (real_inv_pos (real_plus d d) hD2))
          (real_mult eps' (real_mult (real_inv_pos (real_plus d d) hD2) d))
          (RealSetoid.real_eq_mult_compat (real_mult d eps')
            (real_inv_pos (real_plus d d) hD2) (real_mult eps' d)
            (real_inv_pos (real_plus d d) hD2) (real_mult_comm d eps')
            (real_eq_refl (real_inv_pos (real_plus d d) hD2)))
          (real_eq_trans
            (real_mult (real_mult eps' d) (real_inv_pos (real_plus d d) hD2))
            (real_mult eps' (real_mult d (real_inv_pos (real_plus d d) hD2)))
            (real_mult eps' (real_mult (real_inv_pos (real_plus d d) hD2) d))
            (real_eq_sym
              (real_mult eps'
                (real_mult d (real_inv_pos (real_plus d d) hD2)))
              (real_mult (real_mult eps' d)
                (real_inv_pos (real_plus d d) hD2))
              (real_mult_assoc eps' d (real_inv_pos (real_plus d d) hD2)))
            (RealSetoid.real_eq_mult_compat eps'
              (real_mult d (real_inv_pos (real_plus d d) hD2)) eps'
              (real_mult (real_inv_pos (real_plus d d) hD2) d)
              (real_eq_refl eps')
              (real_mult_comm d (real_inv_pos (real_plus d d) hD2)))))
    in
    RealSetoid.real_lt_id_l
      (real_mult d (real_mult eps' (real_inv_pos (real_plus d d) hD2)))
      (real_mult eps' (real_mult (real_inv_pos (real_plus d d) hD2) d)) eps'
      hC1 hlt4
  in
  let r = h (real_mult eps' (real_inv_pos (real_plus d d) hD2)) he0pos in
  (match r with
   | Inl r0 ->
     real_lt_trans x
       (real_plus y
         (real_mult d (real_mult eps' (real_inv_pos (real_plus d d) hD2))))
       (real_plus y eps') r0
       (real_lt_plus_translate y
         (real_mult d (real_mult eps' (real_inv_pos (real_plus d d) hD2)))
         eps' hkey)
   | Inr r0 ->
     RealSetoid.real_lt_id_l x
       (real_plus y
         (real_mult d (real_mult eps' (real_inv_pos (real_plus d d) hD2))))
       (real_plus y eps') r0
       (real_lt_plus_translate y
         (real_mult d (real_mult eps' (real_inv_pos (real_plus d d) hD2)))
         eps' hkey))

(** val real_le_closure_b_one :
    real -> real -> (real -> real_lt -> real_le) -> real_le_b **)

let real_le_closure_b_one x y h =
  real_le_closure_b x y real_one real_lt_zero_one (fun eps heps ->
    RealSetoid.real_le_id_r x (real_plus y eps)
      (real_plus y (real_mult real_one eps))
      (RealSetoid.real_eq_plus_compat y eps y (real_mult real_one eps)
        (real_eq_refl y)
        (real_eq_trans eps (real_mult eps real_one) (real_mult real_one eps)
          (real_eq_sym (real_mult eps real_one) eps (real_mult_one eps))
          (real_mult_comm eps real_one)))
      (h eps heps))

(** val real_log_le_linear_B : real -> real_lt -> real_le_b **)

let real_log_le_linear_B x hx =
  real_le_closure_b_one (real_log x hx) (real_plus x (real_opp real_one))
    (fun eps heps ->
    RealInterfaceEnhancedMod.real_log_le_linear_eps x eps hx heps)

(** val gibbsd_lt_add_opp_r :
    real -> real -> real -> real_lt -> real_lt -> real_lt **)

let gibbsd_lt_add_opp_r x y e _ hlt =
  RealSetoid.real_lt_compat (real_plus e (real_plus x (real_opp e))) x
    (real_plus e y) (real_plus y e)
    (real_eq_sym x (real_plus e (real_plus x (real_opp e)))
      (real_eq_trans x (real_plus x (real_plus (real_opp e) e))
        (real_plus e (real_plus x (real_opp e)))
        (real_eq_trans x (real_plus x real_zero)
          (real_plus x (real_plus (real_opp e) e))
          (real_eq_sym (real_plus x real_zero) x (real_plus_zero x))
          (RealSetoid.real_eq_plus_compat x real_zero x
            (real_plus (real_opp e) e) (real_eq_refl x)
            (real_eq_trans real_zero (real_plus e (real_opp e))
              (real_plus (real_opp e) e)
              (real_eq_sym (real_plus e (real_opp e)) real_zero
                (real_plus_opp e))
              (real_plus_comm e (real_opp e)))))
        (real_eq_trans (real_plus x (real_plus (real_opp e) e))
          (real_plus (real_plus x (real_opp e)) e)
          (real_plus e (real_plus x (real_opp e)))
          (real_plus_assoc x (real_opp e) e)
          (real_plus_comm (real_plus x (real_opp e)) e))))
    (real_plus_comm e y)
    (real_lt_plus_translate e (real_plus x (real_opp e)) y hlt)

(** val gibbsd_le_b_opp : real -> real -> real_le_b -> real_le_b **)

let gibbsd_le_b_opp a b h eps heps =
  gibbsd_lt_add_opp_r (real_opp b) (real_opp a) eps heps
    (RealSetoid.real_lt_compat (real_opp (real_plus b eps))
      (real_plus (real_opp b) (real_opp eps)) (real_opp a) (real_opp a)
      (real_opp_plus b eps) (real_eq_refl (real_opp a))
      (real_opp_lt_compat a (real_plus b eps) (h eps heps)))

(** val gibbsd_le_b_id_l :
    real -> real -> real -> real_eq -> real_le_b -> real_le_b **)

let gibbsd_le_b_id_l a b c hab h eps heps =
  RealSetoid.real_lt_compat b a (real_plus c eps) (real_plus c eps)
    (real_eq_sym a b hab) (real_eq_refl (real_plus c eps)) (h eps heps)

(** val gibbsd_minus_flip : real -> real -> real_eq **)

let gibbsd_minus_flip a b =
  real_eq_trans (real_opp (real_plus a (real_opp b)))
    (real_plus (real_opp a) (real_opp (real_opp b)))
    (real_plus b (real_opp a)) (real_opp_plus a (real_opp b))
    (real_eq_trans (real_plus (real_opp a) (real_opp (real_opp b)))
      (real_plus (real_opp (real_opp b)) (real_opp a))
      (real_plus b (real_opp a))
      (real_plus_comm (real_opp a) (real_opp (real_opp b)))
      (RealSetoid.real_eq_plus_compat (real_opp (real_opp b)) (real_opp a) b
        (real_opp a) (real_opp_opp b) (real_eq_refl (real_opp a))))

(** val gibbsd_le_b_mult_pos_r :
    real -> real -> real -> real_lt -> real_le_b -> real_le_b **)

let gibbsd_le_b_mult_pos_r c a b hc h eps heps =
  let e0 = real_mult eps (real_inv_pos c hc) in
  let hpos0 =
    real_mult_positive eps (real_inv_pos c hc) heps (real_inv_pos_pos c hc)
  in
  RealSetoid.real_lt_compat (real_mult c a) (real_mult c a)
    (real_mult c (real_plus b e0)) (real_plus (real_mult c b) eps)
    (real_eq_refl (real_mult c a))
    (real_eq_trans (real_mult c (real_plus b e0))
      (real_plus (real_mult c b) (real_mult c e0))
      (real_plus (real_mult c b) eps) (real_distrib c b e0)
      (RealSetoid.real_eq_plus_compat (real_mult c b) (real_mult c e0)
        (real_mult c b) eps (real_eq_refl (real_mult c b))
        (real_eq_trans (real_mult c e0)
          (real_mult eps (real_mult c (real_inv_pos c hc))) eps
          (real_eq_trans (real_mult c e0)
            (real_mult (real_mult eps c) (real_inv_pos c hc))
            (real_mult eps (real_mult c (real_inv_pos c hc)))
            (real_eq_trans (real_mult c e0)
              (real_mult (real_mult c eps) (real_inv_pos c hc))
              (real_mult (real_mult eps c) (real_inv_pos c hc))
              (real_mult_assoc c eps (real_inv_pos c hc))
              (RealSetoid.real_eq_mult_compat (real_mult c eps)
                (real_inv_pos c hc) (real_mult eps c) (real_inv_pos c hc)
                (real_mult_comm c eps) (real_eq_refl (real_inv_pos c hc))))
            (real_eq_sym (real_mult eps (real_mult c (real_inv_pos c hc)))
              (real_mult (real_mult eps c) (real_inv_pos c hc))
              (real_mult_assoc eps c (real_inv_pos c hc))))
          (real_eq_trans (real_mult eps (real_mult c (real_inv_pos c hc)))
            (real_mult eps real_one) eps
            (RealSetoid.real_eq_mult_compat eps
              (real_mult c (real_inv_pos c hc)) eps real_one
              (real_eq_refl eps) (real_inv_pos_correct c hc))
            (real_mult_one eps)))))
    (real_mult_lt_compat_l a (real_plus b e0) c (h e0 hpos0) hc)

(** val gibbsd_p_mult_ratio : real -> real -> real_lt -> real_eq **)

let gibbsd_p_mult_ratio p q0 hp =
  real_eq_trans (real_mult p (real_mult q0 (real_inv_pos p hp)))
    (real_mult q0 (real_mult p (real_inv_pos p hp))) q0
    (real_eq_trans (real_mult p (real_mult q0 (real_inv_pos p hp)))
      (real_mult (real_mult p q0) (real_inv_pos p hp))
      (real_mult q0 (real_mult p (real_inv_pos p hp)))
      (real_mult_assoc p q0 (real_inv_pos p hp))
      (real_eq_trans (real_mult (real_mult p q0) (real_inv_pos p hp))
        (real_mult (real_mult q0 p) (real_inv_pos p hp))
        (real_mult q0 (real_mult p (real_inv_pos p hp)))
        (RealSetoid.real_eq_mult_compat (real_mult p q0) (real_inv_pos p hp)
          (real_mult q0 p) (real_inv_pos p hp) (real_mult_comm p q0)
          (real_eq_refl (real_inv_pos p hp)))
        (real_eq_sym (real_mult q0 (real_mult p (real_inv_pos p hp)))
          (real_mult (real_mult q0 p) (real_inv_pos p hp))
          (real_mult_assoc q0 p (real_inv_pos p hp)))))
    (real_eq_trans (real_mult q0 (real_mult p (real_inv_pos p hp)))
      (real_mult q0 real_one) q0
      (RealSetoid.real_eq_mult_compat q0 (real_mult p (real_inv_pos p hp)) q0
        real_one (real_eq_refl q0) (real_inv_pos_correct p hp))
      (real_mult_one q0))

(** val gibbsd_p_minus_ratio : real -> real -> real_lt -> real_eq **)

let gibbsd_p_minus_ratio p q0 hp =
  real_eq_trans
    (real_mult p
      (real_plus real_one (real_opp (real_mult q0 (real_inv_pos p hp)))))
    (real_plus (real_mult p real_one)
      (real_mult p (real_opp (real_mult q0 (real_inv_pos p hp)))))
    (real_plus p (real_opp q0))
    (real_distrib p real_one (real_opp (real_mult q0 (real_inv_pos p hp))))
    (RealSetoid.real_eq_plus_compat (real_mult p real_one)
      (real_mult p (real_opp (real_mult q0 (real_inv_pos p hp)))) p
      (real_opp q0) (real_mult_one p)
      (real_eq_trans
        (real_mult p (real_opp (real_mult q0 (real_inv_pos p hp))))
        (real_opp (real_mult p (real_mult q0 (real_inv_pos p hp))))
        (real_opp q0)
        (real_eq_sym
          (real_opp (real_mult p (real_mult q0 (real_inv_pos p hp))))
          (real_mult p (real_opp (real_mult q0 (real_inv_pos p hp))))
          (real_opp_mult p (real_mult q0 (real_inv_pos p hp))))
        (RealSetoid.real_eq_opp_compat
          (real_mult p (real_mult q0 (real_inv_pos p hp))) q0
          (gibbsd_p_mult_ratio p q0 hp))))

(** val gibbsd_two_pos : real_lt **)

let gibbsd_two_pos =
  real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one

(** val gibbsd_half : real **)

let gibbsd_half =
  real_inv_pos (real_plus real_one real_one) gibbsd_two_pos

(** val gibbsd_half_pos : real_lt **)

let gibbsd_half_pos =
  real_inv_pos_pos (real_plus real_one real_one) gibbsd_two_pos

(** val gibbsd_half_sum : real -> real_eq **)

let gibbsd_half_sum e =
  real_eq_trans
    (real_plus (real_mult e gibbsd_half) (real_mult e gibbsd_half))
    (real_mult e (real_plus gibbsd_half gibbsd_half)) e
    (real_eq_sym (real_mult e (real_plus gibbsd_half gibbsd_half))
      (real_plus (real_mult e gibbsd_half) (real_mult e gibbsd_half))
      (real_distrib e gibbsd_half gibbsd_half))
    (real_eq_trans (real_mult e (real_plus gibbsd_half gibbsd_half))
      (real_mult e real_one) e
      (RealSetoid.real_eq_mult_compat e (real_plus gibbsd_half gibbsd_half) e
        real_one (real_eq_refl e)
        (real_eq_trans (real_plus gibbsd_half gibbsd_half)
          (real_mult (real_plus real_one real_one) gibbsd_half) real_one
          (real_eq_sym (real_mult (real_plus real_one real_one) gibbsd_half)
            (real_plus gibbsd_half gibbsd_half)
            (real_eq_trans
              (real_mult (real_plus real_one real_one) gibbsd_half)
              (real_plus (real_mult real_one gibbsd_half)
                (real_mult real_one gibbsd_half))
              (real_plus gibbsd_half gibbsd_half)
              (real_eq_sym
                (real_plus (real_mult real_one gibbsd_half)
                  (real_mult real_one gibbsd_half))
                (real_mult (real_plus real_one real_one) gibbsd_half)
                (real_distrib_r_local real_one real_one gibbsd_half))
              (RealSetoid.real_eq_plus_compat
                (real_mult real_one gibbsd_half)
                (real_mult real_one gibbsd_half) gibbsd_half gibbsd_half
                (real_eq_trans (real_mult real_one gibbsd_half)
                  (real_mult gibbsd_half real_one) gibbsd_half
                  (real_mult_comm real_one gibbsd_half)
                  (real_mult_one gibbsd_half))
                (real_eq_trans (real_mult real_one gibbsd_half)
                  (real_mult gibbsd_half real_one) gibbsd_half
                  (real_mult_comm real_one gibbsd_half)
                  (real_mult_one gibbsd_half)))))
          (real_inv_pos_correct (real_plus real_one real_one) gibbsd_two_pos)))
      (real_mult_one e))

(** val gibbsd_list_sum_le_b :
    ('a1 -> real) -> ('a1 -> real) -> 'a1 list -> ('a1 -> real_le_b) ->
    real_le_b **)

let rec gibbsd_list_sum_le_b f g l hpt eps heps =
  match l with
  | Nil -> real_lt_plus_r_zero real_zero eps heps
  | Cons (y, l0) ->
    let hpos = real_mult_positive eps gibbsd_half heps gibbsd_half_pos in
    let ha = hpt y (real_mult eps gibbsd_half) hpos in
    let ht = gibbsd_list_sum_le_b f g l0 hpt (real_mult eps gibbsd_half) hpos
    in
    RealSetoid.real_lt_compat (real_plus (f y) (real_list_sum f l0))
      (real_plus (f y) (real_list_sum f l0))
      (real_plus (real_plus (g y) (real_mult eps gibbsd_half))
        (real_plus (real_list_sum g l0) (real_mult eps gibbsd_half)))
      (real_plus (real_plus (g y) (real_list_sum g l0)) eps)
      (real_eq_refl (real_plus (f y) (real_list_sum f l0)))
      (real_eq_trans
        (real_plus (real_plus (g y) (real_mult eps gibbsd_half))
          (real_plus (real_list_sum g l0) (real_mult eps gibbsd_half)))
        (real_plus (real_plus (g y) (real_list_sum g l0))
          (real_plus (real_mult eps gibbsd_half) (real_mult eps gibbsd_half)))
        (real_plus (real_plus (g y) (real_list_sum g l0)) eps)
        (real_plus_swap_mid (g y) (real_mult eps gibbsd_half)
          (real_list_sum g l0) (real_mult eps gibbsd_half))
        (RealSetoid.real_eq_plus_compat
          (real_plus (g y) (real_list_sum g l0))
          (real_plus (real_mult eps gibbsd_half) (real_mult eps gibbsd_half))
          (real_plus (g y) (real_list_sum g l0)) eps
          (real_eq_refl (real_plus (g y) (real_list_sum g l0)))
          (gibbsd_half_sum eps)))
      (real_lt_plus_compat (f y)
        (real_plus (g y) (real_mult eps gibbsd_half)) (real_list_sum f l0)
        (real_plus (real_list_sum g l0) (real_mult eps gibbsd_half)) ha ht)

(** val gibbsd_list_sum_minus :
    ('a1 -> real) -> ('a1 -> real) -> 'a1 list -> real_eq **)

let gibbsd_list_sum_minus p q0 l =
  real_eq_trans
    (real_list_sum (fun s -> real_plus (p s) (real_opp (q0 s))) l)
    (real_plus (real_list_sum p l)
      (real_list_sum (fun s -> real_opp (q0 s)) l))
    (real_plus (real_list_sum p l) (real_opp (real_list_sum q0 l)))
    (real_list_sum_add p (fun s -> real_opp (q0 s)) l)
    (RealSetoid.real_eq_plus_compat (real_list_sum p l)
      (real_list_sum (fun s -> real_opp (q0 s)) l) (real_list_sum p l)
      (real_opp (real_list_sum q0 l)) (real_eq_refl (real_list_sum p l))
      (real_list_sum_opp q0 l))

(** val gibbsd_gibbs_pointwise_B :
    ('a1 -> real) -> ('a1 -> real) -> 'a1 -> real_lt -> real_lt -> real_le_b **)

let gibbsd_gibbs_pointwise_B p q0 s hps hqs eps heps =
  let rqp = real_mult (q0 s) (real_inv_pos (p s) hps) in
  let hr =
    real_mult_positive (q0 s) (real_inv_pos (p s) hps) hqs
      (real_inv_pos_pos (p s) hps)
  in
  let hlin = real_log_le_linear_B rqp hr in
  let hstep2 =
    gibbsd_le_b_id_l (real_plus real_one (real_opp rqp))
      (real_opp (real_plus rqp (real_opp real_one)))
      (real_opp (real_log rqp hr))
      (real_eq_sym (real_opp (real_plus rqp (real_opp real_one)))
        (real_plus real_one (real_opp rqp)) (gibbsd_minus_flip rqp real_one))
      (gibbsd_le_b_opp (real_log rqp hr) (real_plus rqp (real_opp real_one))
        hlin)
  in
  let hstep3 =
    gibbsd_le_b_mult_pos_r (p s) (real_plus real_one (real_opp rqp))
      (real_opp (real_log rqp hr)) hps hstep2
  in
  gibbsd_le_b_id_l (real_plus (p s) (real_opp (q0 s)))
    (real_mult (p s)
      (real_plus real_one
        (real_opp (real_mult (q0 s) (real_inv_pos (p s) hps)))))
    (real_mult (p s) (real_opp (real_log rqp hr)))
    (real_eq_sym
      (real_mult (p s)
        (real_plus real_one
          (real_opp (real_mult (q0 s) (real_inv_pos (p s) hps)))))
      (real_plus (p s) (real_opp (q0 s)))
      (gibbsd_p_minus_ratio (p s) (q0 s) hps))
    hstep3 eps heps

(** val gibbsd_gibbs_inequality :
    'a1 list -> ('a1 -> real) -> ('a1 -> real) -> ('a1 -> real_lt) -> ('a1 ->
    real_lt) -> real_eq -> real_eq -> real_le_b **)

let gibbsd_gibbs_inequality l p q0 hp hq hnormp hnormq =
  let hle =
    gibbsd_list_sum_le_b (fun s -> real_plus (p s) (real_opp (q0 s)))
      (fun s -> real_kl_term (p s) (q0 s) (hp s) (hq s)) l (fun s ->
      gibbsd_gibbs_pointwise_B p q0 s (hp s) (hq s))
  in
  let hz =
    real_eq_trans
      (real_list_sum (fun s -> real_plus (p s) (real_opp (q0 s))) l)
      (real_plus (real_list_sum p l) (real_opp (real_list_sum q0 l)))
      real_zero (gibbsd_list_sum_minus p q0 l)
      (real_eq_trans
        (real_plus (real_list_sum p l) (real_opp (real_list_sum q0 l)))
        (real_plus real_one (real_opp real_one)) real_zero
        (RealSetoid.real_eq_plus_compat (real_list_sum p l)
          (real_opp (real_list_sum q0 l)) real_one (real_opp real_one) hnormp
          (RealSetoid.real_eq_opp_compat (real_list_sum q0 l) real_one hnormq))
        (real_plus_opp real_one))
  in
  gibbsd_le_b_id_l real_zero
    (real_list_sum (fun s -> real_plus (p s) (real_opp (q0 s))) l)
    (real_list_sum (fun s -> real_kl_term (p s) (q0 s) (hp s) (hq s)) l)
    (real_eq_sym
      (real_list_sum (fun s -> real_plus (p s) (real_opp (q0 s))) l)
      real_zero hz)
    hle

(** val logd_req_plus_zero_l :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 ->
    'a1 RealInterfaceEnhancedMod.req **)

let logd_req_plus_zero_l rIS a =
  rIS.RealInterfaceEnhancedMod.req_trans
    (rIS.RealInterfaceEnhancedMod.plus rIS.RealInterfaceEnhancedMod.zero a)
    (rIS.RealInterfaceEnhancedMod.plus a rIS.RealInterfaceEnhancedMod.zero) a
    (rIS.RealInterfaceEnhancedMod.plus_comm rIS.RealInterfaceEnhancedMod.zero
      a)
    (rIS.RealInterfaceEnhancedMod.plus_zero a)

(** val logd_req_opp_opp :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 ->
    'a1 RealInterfaceEnhancedMod.req **)

let logd_req_opp_opp rIS a =
  let h1 =
    rIS.RealInterfaceEnhancedMod.plus_opp (rIS.RealInterfaceEnhancedMod.opp a)
  in
  let h2 = rIS.RealInterfaceEnhancedMod.plus_opp a in
  rIS.RealInterfaceEnhancedMod.req_trans
    (rIS.RealInterfaceEnhancedMod.opp (rIS.RealInterfaceEnhancedMod.opp a))
    (rIS.RealInterfaceEnhancedMod.plus rIS.RealInterfaceEnhancedMod.zero
      (rIS.RealInterfaceEnhancedMod.opp (rIS.RealInterfaceEnhancedMod.opp a)))
    a
    (rIS.RealInterfaceEnhancedMod.req_sym
      (rIS.RealInterfaceEnhancedMod.plus rIS.RealInterfaceEnhancedMod.zero
        (rIS.RealInterfaceEnhancedMod.opp
          (rIS.RealInterfaceEnhancedMod.opp a)))
      (rIS.RealInterfaceEnhancedMod.opp (rIS.RealInterfaceEnhancedMod.opp a))
      (logd_req_plus_zero_l rIS
        (rIS.RealInterfaceEnhancedMod.opp
          (rIS.RealInterfaceEnhancedMod.opp a))))
    (rIS.RealInterfaceEnhancedMod.req_trans
      (rIS.RealInterfaceEnhancedMod.plus rIS.RealInterfaceEnhancedMod.zero
        (rIS.RealInterfaceEnhancedMod.opp
          (rIS.RealInterfaceEnhancedMod.opp a)))
      (rIS.RealInterfaceEnhancedMod.plus
        (rIS.RealInterfaceEnhancedMod.plus a
          (rIS.RealInterfaceEnhancedMod.opp a))
        (rIS.RealInterfaceEnhancedMod.opp
          (rIS.RealInterfaceEnhancedMod.opp a)))
      a
      (rIS.RealInterfaceEnhancedMod.req_plus_compat
        rIS.RealInterfaceEnhancedMod.zero
        (rIS.RealInterfaceEnhancedMod.plus a
          (rIS.RealInterfaceEnhancedMod.opp a))
        (rIS.RealInterfaceEnhancedMod.opp
          (rIS.RealInterfaceEnhancedMod.opp a))
        (rIS.RealInterfaceEnhancedMod.opp
          (rIS.RealInterfaceEnhancedMod.opp a))
        (rIS.RealInterfaceEnhancedMod.req_sym
          (rIS.RealInterfaceEnhancedMod.plus a
            (rIS.RealInterfaceEnhancedMod.opp a))
          rIS.RealInterfaceEnhancedMod.zero h2)
        (rIS.RealInterfaceEnhancedMod.req_refl
          (rIS.RealInterfaceEnhancedMod.opp
            (rIS.RealInterfaceEnhancedMod.opp a))))
      (rIS.RealInterfaceEnhancedMod.req_trans
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.plus a
            (rIS.RealInterfaceEnhancedMod.opp a))
          (rIS.RealInterfaceEnhancedMod.opp
            (rIS.RealInterfaceEnhancedMod.opp a)))
        (rIS.RealInterfaceEnhancedMod.plus a
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.opp a)
            (rIS.RealInterfaceEnhancedMod.opp
              (rIS.RealInterfaceEnhancedMod.opp a))))
        a
        (rIS.RealInterfaceEnhancedMod.req_sym
          (rIS.RealInterfaceEnhancedMod.plus a
            (rIS.RealInterfaceEnhancedMod.plus
              (rIS.RealInterfaceEnhancedMod.opp a)
              (rIS.RealInterfaceEnhancedMod.opp
                (rIS.RealInterfaceEnhancedMod.opp a))))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.plus a
              (rIS.RealInterfaceEnhancedMod.opp a))
            (rIS.RealInterfaceEnhancedMod.opp
              (rIS.RealInterfaceEnhancedMod.opp a)))
          (rIS.RealInterfaceEnhancedMod.plus_assoc a
            (rIS.RealInterfaceEnhancedMod.opp a)
            (rIS.RealInterfaceEnhancedMod.opp
              (rIS.RealInterfaceEnhancedMod.opp a))))
        (rIS.RealInterfaceEnhancedMod.req_trans
          (rIS.RealInterfaceEnhancedMod.plus a
            (rIS.RealInterfaceEnhancedMod.plus
              (rIS.RealInterfaceEnhancedMod.opp a)
              (rIS.RealInterfaceEnhancedMod.opp
                (rIS.RealInterfaceEnhancedMod.opp a))))
          (rIS.RealInterfaceEnhancedMod.plus a
            rIS.RealInterfaceEnhancedMod.zero)
          a
          (rIS.RealInterfaceEnhancedMod.req_plus_compat a a
            (rIS.RealInterfaceEnhancedMod.plus
              (rIS.RealInterfaceEnhancedMod.opp a)
              (rIS.RealInterfaceEnhancedMod.opp
                (rIS.RealInterfaceEnhancedMod.opp a)))
            rIS.RealInterfaceEnhancedMod.zero
            (rIS.RealInterfaceEnhancedMod.req_refl a) h1)
          (rIS.RealInterfaceEnhancedMod.plus_zero a))))

(** val logd_req_plus_zero_r :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> 'a1 ->
    'a1 -> 'a1 RealInterfaceEnhancedMod.req -> 'a1
    RealInterfaceEnhancedMod.req **)

let logd_req_plus_zero_r rIS a b h =
  rIS.RealInterfaceEnhancedMod.req_trans b
    (rIS.RealInterfaceEnhancedMod.plus rIS.RealInterfaceEnhancedMod.zero b)
    (rIS.RealInterfaceEnhancedMod.opp a)
    (rIS.RealInterfaceEnhancedMod.req_sym
      (rIS.RealInterfaceEnhancedMod.plus rIS.RealInterfaceEnhancedMod.zero b)
      b (logd_req_plus_zero_l rIS b))
    (rIS.RealInterfaceEnhancedMod.req_trans
      (rIS.RealInterfaceEnhancedMod.plus rIS.RealInterfaceEnhancedMod.zero b)
      (rIS.RealInterfaceEnhancedMod.plus
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.opp a) a)
        b)
      (rIS.RealInterfaceEnhancedMod.opp a)
      (rIS.RealInterfaceEnhancedMod.req_plus_compat
        rIS.RealInterfaceEnhancedMod.zero
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.opp a) a)
        b b
        (rIS.RealInterfaceEnhancedMod.req_sym
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.opp a) a)
          rIS.RealInterfaceEnhancedMod.zero
          (rIS.RealInterfaceEnhancedMod.req_trans
            (rIS.RealInterfaceEnhancedMod.plus
              (rIS.RealInterfaceEnhancedMod.opp a) a)
            (rIS.RealInterfaceEnhancedMod.plus a
              (rIS.RealInterfaceEnhancedMod.opp a))
            rIS.RealInterfaceEnhancedMod.zero
            (rIS.RealInterfaceEnhancedMod.plus_comm
              (rIS.RealInterfaceEnhancedMod.opp a) a)
            (rIS.RealInterfaceEnhancedMod.plus_opp a)))
        (rIS.RealInterfaceEnhancedMod.req_refl b))
      (rIS.RealInterfaceEnhancedMod.req_trans
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.opp a) a)
          b)
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.opp a)
          (rIS.RealInterfaceEnhancedMod.plus a b))
        (rIS.RealInterfaceEnhancedMod.opp a)
        (rIS.RealInterfaceEnhancedMod.req_sym
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.opp a)
            (rIS.RealInterfaceEnhancedMod.plus a b))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.plus
              (rIS.RealInterfaceEnhancedMod.opp a) a)
            b)
          (rIS.RealInterfaceEnhancedMod.plus_assoc
            (rIS.RealInterfaceEnhancedMod.opp a) a b))
        (rIS.RealInterfaceEnhancedMod.req_trans
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.opp a)
            (rIS.RealInterfaceEnhancedMod.plus a b))
          (rIS.RealInterfaceEnhancedMod.plus
            (rIS.RealInterfaceEnhancedMod.opp a)
            rIS.RealInterfaceEnhancedMod.zero)
          (rIS.RealInterfaceEnhancedMod.opp a)
          (rIS.RealInterfaceEnhancedMod.req_plus_compat
            (rIS.RealInterfaceEnhancedMod.opp a)
            (rIS.RealInterfaceEnhancedMod.opp a)
            (rIS.RealInterfaceEnhancedMod.plus a b)
            rIS.RealInterfaceEnhancedMod.zero
            (rIS.RealInterfaceEnhancedMod.req_refl
              (rIS.RealInterfaceEnhancedMod.opp a))
            h)
          (rIS.RealInterfaceEnhancedMod.plus_zero
            (rIS.RealInterfaceEnhancedMod.opp a)))))

(** val logd_log_compat_of_mono :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> ('a1 ->
    'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.lt
    -> 'a1 RealInterfaceEnhancedMod.le -> 'a1 RealInterfaceEnhancedMod.le) ->
    'a1 -> 'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1
    RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.req -> 'a1
    RealInterfaceEnhancedMod.req **)

let logd_log_compat_of_mono rIS hmono x y hx hy hxy =
  rIS.RealInterfaceEnhancedMod.le_antisym
    (rIS.RealInterfaceEnhancedMod.log x hx)
    (rIS.RealInterfaceEnhancedMod.log y hy)
    (hmono x y hx hy (rIS.RealInterfaceEnhancedMod.lt_le_iff x y (Inr hxy)))
    (hmono y x hy hx
      (rIS.RealInterfaceEnhancedMod.lt_le_iff y x (Inr
        (rIS.RealInterfaceEnhancedMod.req_sym x y hxy))))

(** val logd_log_inv_one_inv_of_compat :
    'a1 RealInterfaceEnhancedMod.coq_RealInterfaceEnhancedSetoid -> ('a1 ->
    'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.lt
    -> 'a1 RealInterfaceEnhancedMod.req -> 'a1 RealInterfaceEnhancedMod.req)
    -> 'a1 -> 'a1 RealInterfaceEnhancedMod.lt -> 'a1
    RealInterfaceEnhancedMod.lt -> 'a1 RealInterfaceEnhancedMod.req **)

let logd_log_inv_one_inv_of_compat rIS hcompat x hx hi =
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
  let hlog1 =
    rIS.RealInterfaceEnhancedMod.req_trans
      (rIS.RealInterfaceEnhancedMod.log
        (rIS.RealInterfaceEnhancedMod.mult
          (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x)
        (rIS.RealInterfaceEnhancedMod.mult_positive
          (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x hi hx))
      (rIS.RealInterfaceEnhancedMod.log rIS.RealInterfaceEnhancedMod.one
        rIS.RealInterfaceEnhancedMod.one_pos)
      rIS.RealInterfaceEnhancedMod.zero
      (hcompat
        (rIS.RealInterfaceEnhancedMod.mult
          (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x)
        rIS.RealInterfaceEnhancedMod.one
        (rIS.RealInterfaceEnhancedMod.mult_positive
          (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x hi hx)
        rIS.RealInterfaceEnhancedMod.one_pos hprod)
      (rIS.RealInterfaceEnhancedMod.log_one
        rIS.RealInterfaceEnhancedMod.one_pos)
  in
  let hdec =
    rIS.RealInterfaceEnhancedMod.req_trans
      (rIS.RealInterfaceEnhancedMod.plus
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos x hx) hi)
        (rIS.RealInterfaceEnhancedMod.log x hx))
      (rIS.RealInterfaceEnhancedMod.log
        (rIS.RealInterfaceEnhancedMod.mult
          (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x)
        (rIS.RealInterfaceEnhancedMod.mult_positive
          (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x hi hx))
      rIS.RealInterfaceEnhancedMod.zero
      (rIS.RealInterfaceEnhancedMod.req_sym
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.mult
            (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x)
          (rIS.RealInterfaceEnhancedMod.mult_positive
            (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x hi hx))
        (rIS.RealInterfaceEnhancedMod.plus
          (rIS.RealInterfaceEnhancedMod.log
            (rIS.RealInterfaceEnhancedMod.inv_pos x hx) hi)
          (rIS.RealInterfaceEnhancedMod.log x hx))
        (rIS.RealInterfaceEnhancedMod.log_mult
          (rIS.RealInterfaceEnhancedMod.inv_pos x hx) x hi hx))
      hlog1
  in
  rIS.RealInterfaceEnhancedMod.req_sym
    (rIS.RealInterfaceEnhancedMod.opp (rIS.RealInterfaceEnhancedMod.log x hx))
    (rIS.RealInterfaceEnhancedMod.log
      (rIS.RealInterfaceEnhancedMod.inv_pos x hx) hi)
    (rIS.RealInterfaceEnhancedMod.req_trans
      (rIS.RealInterfaceEnhancedMod.opp
        (rIS.RealInterfaceEnhancedMod.log x hx))
      (rIS.RealInterfaceEnhancedMod.opp
        (rIS.RealInterfaceEnhancedMod.opp
          (rIS.RealInterfaceEnhancedMod.log
            (rIS.RealInterfaceEnhancedMod.inv_pos x hx) hi)))
      (rIS.RealInterfaceEnhancedMod.log
        (rIS.RealInterfaceEnhancedMod.inv_pos x hx) hi)
      (rIS.RealInterfaceEnhancedMod.req_sym
        (rIS.RealInterfaceEnhancedMod.opp
          (rIS.RealInterfaceEnhancedMod.opp
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos x hx) hi)))
        (rIS.RealInterfaceEnhancedMod.opp
          (rIS.RealInterfaceEnhancedMod.log x hx))
        (rIS.RealInterfaceEnhancedMod.req_opp_compat
          (rIS.RealInterfaceEnhancedMod.opp
            (rIS.RealInterfaceEnhancedMod.log
              (rIS.RealInterfaceEnhancedMod.inv_pos x hx) hi))
          (rIS.RealInterfaceEnhancedMod.log x hx)
          (rIS.RealInterfaceEnhancedMod.req_sym
            (rIS.RealInterfaceEnhancedMod.log x hx)
            (rIS.RealInterfaceEnhancedMod.opp
              (rIS.RealInterfaceEnhancedMod.log
                (rIS.RealInterfaceEnhancedMod.inv_pos x hx) hi))
            (logd_req_plus_zero_r rIS
              (rIS.RealInterfaceEnhancedMod.log
                (rIS.RealInterfaceEnhancedMod.inv_pos x hx) hi)
              (rIS.RealInterfaceEnhancedMod.log x hx) hdec))))
      (logd_req_opp_opp rIS
        (rIS.RealInterfaceEnhancedMod.log
          (rIS.RealInterfaceEnhancedMod.inv_pos x hx) hi)))

(** val logd_log_compat_real :
    real -> real -> real RealInterfaceEnhancedMod.lt -> real
    RealInterfaceEnhancedMod.lt -> real RealInterfaceEnhancedMod.req -> real
    RealInterfaceEnhancedMod.req **)

let logd_log_compat_real x y hx hy hxy =
  logd_log_compat_of_mono RealInterfaceEnhancedMod.coq_RealEnhancedReal
    (fun a b ha hb hab -> Obj.magic real_log_le_mono a b ha hb hab) x y hx hy
    hxy

(** val logd_log_inv_one_inv_real :
    real -> real RealInterfaceEnhancedMod.lt -> real
    RealInterfaceEnhancedMod.lt -> real RealInterfaceEnhancedMod.req **)

let logd_log_inv_one_inv_real x hx hi =
  logd_log_inv_one_inv_of_compat
    RealInterfaceEnhancedMod.coq_RealEnhancedReal logd_log_compat_real x hx hi

(** val logd_le_b_id_r :
    real -> real -> real -> real_le_b -> real_eq -> real_le_b **)

let logd_le_b_id_r a b c h hab eps heps =
  RealSetoid.real_lt_compat a a (real_plus b eps) (real_plus c eps)
    (real_eq_refl a)
    (RealSetoid.real_eq_plus_compat b eps c eps hab (real_eq_refl eps))
    (h eps heps)

(** val logd_log_le_linear_eps :
    real -> real -> real_lt -> real_lt -> real_le **)

let logd_log_le_linear_eps =
  RealInterfaceEnhancedMod.real_log_le_linear_eps

(** val logd_log_le_linear_B : real -> real_lt -> real_le_b **)

let logd_log_le_linear_B =
  real_log_le_linear_B

(** val logd_log_lt_mono_real :
    real -> real -> real_lt -> real_lt -> real_lt -> real_lt **)

let logd_log_lt_mono_real =
  real_log_lt_mono

(** val logd_log_two_pos_real : real_lt **)

let logd_log_two_pos_real =
  RealSetoid.real_lt_compat (real_log real_one real_lt_zero_one) real_zero
    (real_log (real_plus real_one real_one)
      (real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one))
    (real_log (real_plus real_one real_one)
      (real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one))
    (real_log_one real_lt_zero_one)
    (real_eq_refl
      (real_log (real_plus real_one real_one)
        (real_plus_positive real_one real_one real_lt_zero_one
          real_lt_zero_one)))
    (real_log_lt_mono real_one (real_plus real_one real_one) real_lt_zero_one
      (real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one)
      (RealSetoid.real_lt_compat (real_plus real_one real_zero) real_one
        (real_plus real_one real_one) (real_plus real_one real_one)
        (real_plus_zero real_one)
        (real_eq_refl (real_plus real_one real_one))
        (real_lt_plus_translate real_one real_zero real_one real_lt_zero_one)))

(** val logd_kl_term_minus_form :
    real -> real -> real_lt -> real_lt -> real_eq **)

let logd_kl_term_minus_form p q0 hp hq =
  let hi = real_inv_pos_pos p hp in
  let hr = real_mult_positive q0 (real_inv_pos p hp) hq hi in
  let hlog =
    real_eq_trans (real_log (real_mult q0 (real_inv_pos p hp)) hr)
      (real_plus (real_log q0 hq) (real_log (real_inv_pos p hp) hi))
      (real_plus (real_log q0 hq) (real_opp (real_log p hp)))
      (real_log_mult q0 (real_inv_pos p hp) hq hi)
      (RealSetoid.real_eq_plus_compat (real_log q0 hq)
        (real_log (real_inv_pos p hp) hi) (real_log q0 hq)
        (real_opp (real_log p hp)) (real_eq_refl (real_log q0 hq))
        (Obj.magic logd_log_inv_one_inv_real p hp hi))
  in
  RealSetoid.real_eq_mult_compat p
    (real_opp (real_log (real_mult q0 (real_inv_pos p hp)) hr)) p
    (real_plus (real_log p hp) (real_opp (real_log q0 hq))) (real_eq_refl p)
    (real_eq_trans
      (real_opp (real_log (real_mult q0 (real_inv_pos p hp)) hr))
      (real_opp (real_plus (real_log q0 hq) (real_opp (real_log p hp))))
      (real_plus (real_log p hp) (real_opp (real_log q0 hq)))
      (RealSetoid.real_eq_opp_compat
        (real_log (real_mult q0 (real_inv_pos p hp)) hr)
        (real_plus (real_log q0 hq) (real_opp (real_log p hp))) hlog)
      (real_eq_trans
        (real_opp (real_plus (real_log q0 hq) (real_opp (real_log p hp))))
        (real_plus (real_opp (real_log q0 hq))
          (real_opp (real_opp (real_log p hp))))
        (real_plus (real_log p hp) (real_opp (real_log q0 hq)))
        (real_opp_plus (real_log q0 hq) (real_opp (real_log p hp)))
        (real_eq_trans
          (real_plus (real_opp (real_log q0 hq))
            (real_opp (real_opp (real_log p hp))))
          (real_plus (real_opp (real_opp (real_log p hp)))
            (real_opp (real_log q0 hq)))
          (real_plus (real_log p hp) (real_opp (real_log q0 hq)))
          (real_plus_comm (real_opp (real_log q0 hq))
            (real_opp (real_opp (real_log p hp))))
          (RealSetoid.real_eq_plus_compat
            (real_opp (real_opp (real_log p hp))) (real_opp (real_log q0 hq))
            (real_log p hp) (real_opp (real_log q0 hq))
            (real_opp_opp (real_log p hp))
            (real_eq_refl (real_opp (real_log q0 hq)))))))

(** val logd_list_sum_kl_minus_form :
    'a1 list -> ('a1 -> real) -> ('a1 -> real) -> ('a1 -> real_lt) -> ('a1 ->
    real_lt) -> real_eq **)

let logd_list_sum_kl_minus_form l p q0 hp hq =
  real_list_sum_ext (fun s -> real_kl_term (p s) (q0 s) (hp s) (hq s))
    (fun s ->
    real_mult (p s)
      (real_plus (real_log (p s) (hp s)) (real_opp (real_log (q0 s) (hq s)))))
    l (fun s -> logd_kl_term_minus_form (p s) (q0 s) (hp s) (hq s))

(** val logd_gibbs_inequality_minus_B :
    'a1 list -> ('a1 -> real) -> ('a1 -> real) -> ('a1 -> real_lt) -> ('a1 ->
    real_lt) -> real_eq -> real_eq -> real_le_b **)

let logd_gibbs_inequality_minus_B l p q0 hp hq hnormp hnormq =
  logd_le_b_id_r real_zero
    (real_list_sum (fun s -> real_kl_term (p s) (q0 s) (hp s) (hq s)) l)
    (real_list_sum (fun s ->
      real_mult (p s)
        (real_plus (real_log (p s) (hp s))
          (real_opp (real_log (q0 s) (hq s)))))
      l)
    (gibbsd_gibbs_inequality l p q0 hp hq hnormp hnormq)
    (logd_list_sum_kl_minus_form l p q0 hp hq)

(** val logd_gibbs_inequality_minus_eps :
    'a1 list -> ('a1 -> real) -> ('a1 -> real) -> ('a1 -> real_lt) -> ('a1 ->
    real_lt) -> real_eq -> real_eq -> real -> real_lt -> real_le **)

let logd_gibbs_inequality_minus_eps l p q0 hp hq hnormp hnormq eps heps =
  RealSetoid.real_le_id_r real_zero
    (real_plus
      (real_list_sum (fun s -> real_kl_term (p s) (q0 s) (hp s) (hq s)) l)
      eps)
    (real_plus
      (real_list_sum (fun s ->
        real_mult (p s)
          (real_plus (real_log (p s) (hp s))
            (real_opp (real_log (q0 s) (hq s)))))
        l)
      eps)
    (RealSetoid.real_eq_plus_compat
      (real_list_sum (fun s -> real_kl_term (p s) (q0 s) (hp s) (hq s)) l)
      eps
      (real_list_sum (fun s ->
        real_mult (p s)
          (real_plus (real_log (p s) (hp s))
            (real_opp (real_log (q0 s) (hq s)))))
        l)
      eps (logd_list_sum_kl_minus_form l p q0 hp hq) (real_eq_refl eps))
    (real_gibbs_inequality_eps l p q0 hp hq hnormp hnormq eps heps)

(** val logd_gibbs_sum_eps_boltzmann_list :
    ('a1 -> real) -> real -> real_lt -> real -> real_lt -> 'a1 list -> ('a1
    -> real) -> ('a1 -> real_lt) -> real_eq -> real_eq -> real -> real_lt ->
    real_le **)

let logd_gibbs_sum_eps_boltzmann_list base d d_pos z0 z_pos l p hp hnormp hnormb eps heps =
  real_gibbs_inequality_eps l p (fun s ->
    real_boltzmann_dist_r base d d_pos z0 z_pos s) hp (fun s ->
    real_boltzmann_dist_r_pos base d d_pos z0 z_pos s) hnormp hnormb eps heps
