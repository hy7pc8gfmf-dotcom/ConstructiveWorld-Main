
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

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

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

  val abs : z -> z
 end

type q = { qnum : z; qden : positive }

type 'a id =
| Id_refl

type ('a, 'b) or0 = ('a, 'b) sum

type 'a not = 'a -> empty_set

type natLe = bool id

type qseq = nat -> q

type qltT = bool id

type cauchy = q -> qltT -> (nat, nat -> nat -> natLe -> natLe -> qltT) sigT

type real = (qseq, cauchy) sigT

val real_zero : real

val real_one : real

val count_token :
  ('a1 -> 'a1 -> ('a1 id, 'a1 id not) or0) -> 'a1 -> 'a1 list -> nat

val removeT :
  ('a1 -> 'a1 -> ('a1 id, 'a1 id not) or0) -> 'a1 -> 'a1 list -> 'a1 list

val hard_dist : ('a1 -> 'a1 -> ('a1 id, 'a1 id not) or0) -> 'a1 -> 'a1 -> real
