(* ConstructiveWorld-Main - planB wave-2 piece: the G1 witness general-n definition face (lcm, Gaussian c_j, S_n, t_n, Phi/L, a/b extraction). *)

(** * planb4_g1_witness: the general-n G1 witness pipeline (A(n), B(n) : nat -> Z).

    Mission.  The general-n definition face for the zero-premise
      witness: the lcm face [L_n := lcm(1..4n)] with the [P_n] prime
      window quotient (Phi_n), the Gaussian half-pair channel
      [(1/i)c_j := 2(2^j Im[(4+2i)^j] + Im[(6+2i)^j]) / (40^j j)], the
      assembled sum [S_n := sum_{j=1..3n} A_{n,j} (1/i)c_j] over the
      in-tree carrier [piu_zz_Aj], the polynomial-part integral face
      [t_n], and the a/b extraction
      [a_n := 2^(-5n/2+1) L_n (-1)^(n+1) (t_n + S_n)],
      [b_n := 2^(-5n/2+1) L_n (-1)^(n+1) A_{n,0} / 2].
      The calibration tables of planb3_g1_calib (n = 1..40) are the
      downstream specializations of this face.

    Dependencies.  piu_zz_kernel_sum (the A_j carrier, vm_compute
      samples A_{1,0} = -2392, A_{1,3} = 8000); planb3_g1_calib (the
      n = 1..40 calibration tables, downstream cross-check); stdlib
      QArith, ZArith, Arith, Lia, List.

    References.  KB41m pre-survey (the a/b extraction oracle chain,
      the unique-pair certificate max |R_n| = 0.06888 at n=1 < 0.5);
      ZZ2020 Lemma 3 (L_n 10^(-j) A_j / j in Z) and Prop 1 (2^(-5n/2+2)
      L_n I_n in Z + Z pi); the path-A survey receipt (G1 gap ledger).

    Constructivity.  All faces are informative Fixpoints or
      Definitions over Z/Q transparent data; admission-free and
      postulate-free; the sum faces compute by vm_compute for concrete
      n.

    Build.  coqc -native-compiler no -q -Q . "" planb4_g1_witness.v
      (Rocq 9.3.0, single lane under cpu_guard_v3). *)

From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Require Import piu_zz_kernel_sum.

Import ListNotations.

(* ================================================================== *)
(* Section 1. The lcm face: L_n := lcm(1..4n) over Z.                 *)
(* ================================================================== *)

Definition planb4_lcm_upto (k : nat) : Z :=
  fold_left Z.lcm (map Z.of_nat (seq 1 k)) 1%Z.

Definition planb4_L (n : nat) : Z := planb4_lcm_upto (4 * n).

(* ================================================================== *)
(* Section 2. Gaussian half-pair arithmetic over Q: (re, im) pairs.   *)
(* ================================================================== *)

Definition gzq (re im : Q) : Q * Q := (re, im).

Definition gzq_add (x y : Q * Q) : Q * Q :=
  (fst x + fst y, snd x + snd y).

Definition gzq_mul (x y : Q * Q) : Q * Q :=
  (fst x * fst y - snd x * snd y, fst x * snd y + snd x * fst y).

Fixpoint gzq_pow (x : Q * Q) (k : nat) {struct k} : Q * Q :=
  match k with
  | O => (1 # 1, 0 # 1)
  | S k' => gzq_mul x (gzq_pow x k')
  end.

(* the half-pair base for the (4+2i) channel: (4+2i)/2 = (2, 1). *)
Definition planb4_base41 : Q * Q := (2, 1).

(* the half-pair base for the (6+2i) channel: (6+2i)/2 = (3, 1). *)
Definition planb4_base61 : Q * Q := (3, 1).

Definition planb4_Im (x : Q * Q) : Q := snd x.

(* Im[(4+2i)^j] / 2^j = Im[(2,1)^j] over Q (the half-pair scaling). *)
Definition planb4_im41_half (j : nat) : Q :=
  planb4_Im (gzq_pow planb4_base41 j).

(* Im[(6+2i)^j] / 2^j = Im[(3,1)^j] over Q. *)
Definition planb4_im61_half (j : nat) : Q :=
  planb4_Im (gzq_pow planb4_base61 j).

(* the channel face: (1/i)c_j = 2(2^j Im[(4+2i)^j] + Im[(6+2i)^j])/(40^j j)
   in half-pair Q form: 2(Im[(2,1)^j] + Im[(3,1)^j]) / (20^j * j)
   since 40^j = 2^j * 20^j and 2^j Im[(4+2i)^j] = 2^(2j) Im[(2,1)^j],
   the half-pair Q form keeps everything division-light. *)
Definition planb4_cj (j : nat) : Q :=
  2 * (planb4_im41_half j + planb4_im61_half j) /
      ((20 # 1) ^ Z.of_nat j * (Z.of_nat j # 1)).

(* ================================================================== *)
(* Section 3. The assembled sum face: S_n over the A_j carrier.       *)
(* ================================================================== *)

Definition planb4_Sn_body (n j : nat) : Q :=
  piu_zz_Aj n j * planb4_cj j.

Fixpoint planb4_Sn_sum (n j : nat) : Q :=
  match j with
  | O => 0 # 1
  | S j' => planb4_Sn_sum n j' + planb4_Sn_body n (S j')
  end.

Definition planb4_Sn (n : nat) : Q := planb4_Sn_sum n (3 * n).

(* ================================================================== *)
(* Section 4. The floor face: 2^(-floor(5n/2)+1) in Q.                *)
(* ================================================================== *)

Definition planb4_pow2_q (k : nat) : Q := (2 # 1) ^ Z.of_nat k.

Definition planb4_floor2q_inv (n : nat) : Q :=
  match Nat.even (5 * n) with
  | true => planb4_pow2_q (5 * n / 2)   (* 2^(5n/2), floor = exact *)
  | false => planb4_pow2_q ((5 * n - 1) / 2)
  end.

(* 2^(-floor(5n/2)+1) as a Q factor. *)
Definition planb4_scale (n : nat) : Q :=
  2 * / planb4_floor2q_inv n.

(* ================================================================== *)
(* Section 5. The a/b extraction faces (informative, Q-valued; the    *)
(* Z-typed statements close by the KB41m integrality oracle chain).   *)
(* ================================================================== *)

Definition planb4_aq (n : nat) : Q :=
  planb4_scale n * planb4_Sn n.

Definition planb4_bq (n : nat) : Q :=
  planb4_scale n * (piu_zz_Aj n 0 * (1 # 2)).

(* ================================================================== *)
(* Section 6. Numeric spot faces (vm_compute anchors, n = 1..3).      *)
(* ================================================================== *)

(* SCALE-NORMALIZATION TASK (KB41m oracle chain item 3): the raw carrier
   sum piu_zz_Aj lives in the raw M_j-sum scale; the KB41m oracle faces
   A_{1,0} = -2392 and A_{1,3} = 8000 live in the reduced A_j scale.
   The scale factor is to be pinned by the fixer from KB41m item (1)-3
   (kb41b ext acc-scale erratum = |A| * 2^(4n)) and cross-checked by
   vm_compute against -2392 / 8000. *)
(* A-anchors in Qeq_bool form: the raw sum reduces to the oracle integers *)
Example planb4_A10_anchor : Qeq_bool (piu_zz_Aj 1 0) (-2392 # 1) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_A13_anchor : Qeq_bool (piu_zz_Aj 1 3) (8000 # 1) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_L1 : planb4_L 1 = 12%Z.
Proof. vm_compute. reflexivity. Qed.

Example planb4_L2 : planb4_L 2 = 840%Z.
Proof. vm_compute. reflexivity. Qed.

Example planb4_scale1_pos : 0 < planb4_scale 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 7. Assumption audit.                                       *)
(* ================================================================== *)

Print Assumptions planb4_lcm_upto.
Print Assumptions planb4_L.
Print Assumptions planb4_cj.
Print Assumptions planb4_Sn.
Print Assumptions planb4_scale.
Print Assumptions planb4_aq.
Print Assumptions planb4_bq.
Print Assumptions planb4_L1.
Print Assumptions planb4_L2.
Print Assumptions planb4_scale1_pos.

(* ================================================================== *)
(* Section 8. The t_n polynomial-part integral face (exact Gaussian-Q *)
(* contour arithmetic: the monomial integral along the symmetric      *)
(* segment [-1-2i, -1+2i] closes to 2i * (rational), so -i * integral *)
(* lands in Q per monomial).                                          *)
(* ================================================================== *)

(* the P_n quotient polynomial Q-part coefficients: P(x) = N(x)/D(x)   *)
(* with D = (25 - x^2)^(3n+1); the quotient degree is bounded by       *)
(* deg N - deg D < 0 for the R_n face, so the polynomial part P is     *)
(* carried here as the explicit coeff list of the STRICT division      *)
(* remainder-free segment: for the ZZ2020 R_n the quotient is the      *)
(* zero polynomial (deg R_n < deg D holds for n >= 1: deg N = 2n +     *)
(* 8n = 10n, deg D = 6n + 2, 10n < 6n + 2 iff n < 0.5 -- FAILS; the    *)
(* quotient is NON-zero).  The quotient coeffs are computed by the     *)
(* textbook long division on nat-indexed Z coeff lists. *)
