
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

val compOpp : comparison -> comparison

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat :
 sig
  val leb : nat -> nat -> bool

  val eq_dec : nat -> nat -> sumbool
 end

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val mul : positive -> positive -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison
 end

type q = { qnum : z; qden : positive }

val qcompare : q -> q -> comparison

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

type natLe = bool id

val natLe_lift : nat -> nat -> natLe

val qlt_bool : q -> q -> bool

val q_pow : q -> nat -> q

type natLt = bool id

module RealSetoid :
 sig
  val eq_Id : 'a1 -> 'a1 -> 'a1 id
 end

module StopTime :
 sig
  val st_pred_decay : q -> q -> q -> nat -> bool

  type st_hit =
    (nat, (natLe, (bool id, nat -> natLt -> bool id) and0) and0) sigT

  type st_miss = nat -> natLe -> bool id

  type st_res = (st_hit, st_miss) or0

  val stsearch_step_0 : (nat -> bool) -> st_res

  val stsearch_step_S : (nat -> bool) -> nat -> st_res -> st_res

  val stsearch : (nat -> bool) -> nat -> st_res

  val stsearch_report : (nat -> bool) -> nat -> (nat, bool) prod

  val st_waste : (nat -> bool) -> nat -> nat
 end
