
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

  val leb : z -> z -> bool
 end

type q = { qnum : z; qden : positive }

val qcompare : q -> q -> comparison

val qle_bool : q -> q -> bool

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

type natLe = bool id

val qlt_bool : q -> q -> bool

type qltT = bool id

type qleT' = bool id

val q_pow : q -> nat -> q

module Constitution :
 sig
  type claim_decl = { cl_c0 : q; cl_eps : q; cl_kappa : q; cl_N : nat;
                      cl_id : nat }

  val cl_c0 : claim_decl -> q

  val cl_eps : claim_decl -> q

  val cl_kappa : claim_decl -> q

  val cl_N : claim_decl -> nat

  val cl_id : claim_decl -> nat

  type claim_reject =
  | Coq_rj_kappa
  | Coq_rj_budget
  | Coq_rj_data
  | Coq_rj_reach

  type claim_pass =
    ((qleT', qltT) and0, (natLe, ((qleT', qltT) and0, qltT) and0) and0) and0

  val kap_low_dec : claim_decl -> (qleT', (bool id, claim_reject) and0) or0

  val kap_high_dec : claim_decl -> (qltT, (bool id, claim_reject) and0) or0

  val bud_dec : claim_decl -> (natLe, (bool id, claim_reject) and0) or0

  val dat_c0_dec : claim_decl -> (qleT', (bool id, claim_reject) and0) or0

  val dat_eps_dec : claim_decl -> (qltT, (bool id, claim_reject) and0) or0

  val reach_dec : claim_decl -> (qltT, (bool id, claim_reject) and0) or0

  val check_claim : claim_decl -> (claim_pass, claim_reject) or0

  type claim_verdict =
  | Coq_v_pass
  | Coq_v_reject of claim_reject

  val check_report : claim_decl -> claim_verdict

  val chain_claim : claim_decl -> claim_decl -> claim_decl
 end
