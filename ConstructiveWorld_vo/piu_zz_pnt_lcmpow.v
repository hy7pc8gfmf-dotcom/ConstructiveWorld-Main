(* ==========================================================================
   Module: piu_zz_pnt_lcmpow
   Mission: Power characterization of the least common multiple 1..N for
     the effective-PNT consumption chain: every prime power p^e <= N
     divides lcm(1..N) (node B3.1), distinct prime powers are coprime in
     Set-carried boolean face (node B3.2), every m >= 2 has a prime
     factor and the exact power of a prime dividing m can be stripped
     (node B3.3), and the psi fold zz_psi N (product of primorials of
     the integer k-th roots of N) absorbs every m in [1, N], so
     lcm(1..N) divides zz_psi N (node B3.4).
   Dependencies: piu_zz_padic_clearing (zz_lcm_range, zz_j_div_lcm, Bdiv,
     BidT, Bid, zz_primeb, zz_primeb_prime, zz_primeb_spec,
     zz_nodiv_upto), abl_Pr_erdos_theta (pec_prim), Stdlib
     ZArith/Znumtheory/Wf_nat/List (prime, rel_prime, Gauss,
     Zgcd_1_rel_prime, prime_divisors, prime_ge_2, lt_wf_ind).
   References: the identity psi(N) = sum_{p <= N} floor(log_p N) * ln p,
     consumed in the window assembly of Zeilberger-Zudilin 2020 (Lemma 3
     context, tree module piu_zz_padic_clearing); lcm face is
     zz_lcm_range (fold of Z.lcm over 1..K).
   Constructivity: statement faces Set-carried (Bdiv = sigT witness of
     an equality, BidT = boolean identity); the stdlib Prop lemmas prime,
     rel_prime, Gauss appear in proof bodies only; definitions transparent
     (none in this module beyond lemmas); every lemma closes with a full
     proof under the global context.
   Build: coqc -native-compiler no -q
     -Q <certified vo tree> "" -Q <this directory> ""
     piu_zz_pnt_lcmpow.v  (single compile lane under cpu_guard wrap).
   ========================================================================== *)

From Stdlib Require Import ZArith Arith Wf_nat Lia Bool List.
From Stdlib Require Import Znumtheory.
Require Import piu_zz_padic_clearing.
Require Import abl_Pr_core_01.
Require Import abl_Pr_erdos_core.
Require Import abl_Pr_erdos_theta.

Local Open Scope Z_scope.

(* ================= Section 1. Primality bridge ================= *)

(* The tree trial-division face zz_primeb implies the stdlib Z-level
   predicate prime. Proof: every m in [1, k) with gcd(m, k) > 1 would
   give a divisor g = gcd(m, k) of k with 2 <= g < k, contradicting
   zz_primeb_spec (k has no divisor in [2, k-1]). *)
Lemma zz_primeb_prime_std : forall k : nat,
  zz_primeb k = true -> prime (Z.of_nat k).
Proof.
  intros k Hk.
  pose proof (zz_primeb_prime k Hk) as Hltb.
  apply (proj1 (Nat.ltb_lt 1 k)) in Hltb.
  apply prime_intro.
  - apply (proj1 (Nat2Z.inj_lt 1 k)). exact Hltb.
  - intros m Hm.
    apply (proj1 (Zgcd_1_rel_prime _ _)).
    destruct (Z.eq_dec (Z.gcd m (Z.of_nat k)) 1) as [Hg | Hgne].
    + exact Hg.
    + exfalso.
      pose proof (Z.gcd_divide_l m (Z.of_nat k)) as Hgd1.
      pose proof (Z.gcd_divide_r m (Z.of_nat k)) as Hgd2.
      pose proof (Z.gcd_nonneg m (Z.of_nat k)) as Hgn.
      assert (Hgz : Z.gcd m (Z.of_nat k) <> 0).
      { intro H0. rewrite H0 in Hgd1.
        destruct Hgd1 as [q Hq]. rewrite Z.mul_0_r in Hq. lia. }
      assert (Hg2 : (2 <= Z.gcd m (Z.of_nat k))%Z) by lia.
      assert (Hgle : (Z.gcd m (Z.of_nat k) <= m)%Z)
        by (apply (Z.divide_pos_le _ m); [lia | exact Hgd1]).
      assert (Hglt : (Z.gcd m (Z.of_nat k) < Z.of_nat k)%Z) by lia.
      pose proof (zz_primeb_spec k Hk (Z.gcd m (Z.of_nat k)) Hgn Hglt Hgne)
        as Hb.
      rewrite (proj2 (Z.mod_divide (Z.of_nat k)
                        (Z.gcd m (Z.of_nat k)) Hgz) Hgd2) in Hb.
      discriminate Hb.
Qed.

(* ================= Section 2. Coprimality of prime powers ================= *)

(* Two distinct primes are coprime: a common divisor of p and q other
   than 1 would be a divisor of the prime q different from 1 and q,
   contradicting prime_divisors. *)
Lemma zz_rel_prime_prime_pair : forall p q : nat,
  zz_primeb p = true -> zz_primeb q = true -> (p <> q)%nat ->
  rel_prime (Z.of_nat p) (Z.of_nat q).
Proof.
  intros p q Hp Hq HpQ.
  pose proof (zz_primeb_prime_std p Hp) as Hpp.
  pose proof (zz_primeb_prime_std q Hq) as Hqq.
  pose proof (prime_ge_2 _ Hpp) as Hp2.
  apply (prime_rel_prime (Z.of_nat p) Hpp (Z.of_nat q)).
  intro Hd.
  pose proof (prime_divisors _ Hqq _ Hd) as [Hc | [Hc | [Hc | Hc]]].
  + lia.
  + lia.
  + apply Nat2Z.inj_iff in Hc. congruence.
  + lia.
Qed.

(* Coprimality is stable under raising the right argument to a power:
   rel_prime a (b^(f+1)) = rel_prime a (b * b^f) splits by rel_prime_mult. *)
Lemma zz_rel_prime_pow_r : forall a b : Z, rel_prime a b ->
  forall f : nat, rel_prime a (b ^ Z.of_nat f).
Proof.
  intros a b Hab f. induction f as [|f IH].
  - cbn [Z.of_nat]. apply rel_prime_sym. apply rel_prime_1.
  - assert (Hs : Z.of_nat (S f) = (Z.of_nat f + 1)%Z) by lia.
    rewrite Hs. rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r, Z.mul_comm.
    apply rel_prime_mult; assumption.
Qed.

Lemma zz_rel_prime_pow_l : forall a b : Z, rel_prime a b ->
  forall e : nat, rel_prime (a ^ Z.of_nat e) b.
Proof.
  intros a b Hab e. apply rel_prime_sym.
  apply zz_rel_prime_pow_r.
  apply rel_prime_sym. exact Hab.
Qed.

(* Node B3.2 (born face, Set-carried): distinct prime powers are
   coprime, in the boolean gcd face used across the tree. *)
Theorem zz_ppow_coprime : forall (p q e f : nat),
  BidT (zz_primeb p) -> BidT (zz_primeb q) -> (p <> q)%nat ->
  BidT (Z.eqb (Z.gcd (Z.of_nat p ^ Z.of_nat e)
                     (Z.of_nat q ^ Z.of_nat f)) 1).
Proof.
  intros p q e f Hbp Hbq Hne.
  apply BidT_elim in Hbp. apply BidT_elim in Hbq.
  apply BidT_intro. apply Z.eqb_eq.
  apply (proj2 (Zgcd_1_rel_prime _ _)).
  apply zz_rel_prime_pow_l.
  apply zz_rel_prime_pow_r.
  apply rel_prime_sym.
  apply zz_rel_prime_prime_pair.
  - exact Hbq.
  - exact Hbp.
  - congruence.
Qed.

(* ================= Section 3. lcm power absorption and combiners ================= *)

(* Node B3.1 (born face, Set-carried): a prime power p^e with
   1 <= p^e <= N divides lcm(1..N), because lcm(1..N) absorbs every
   integer in [1, N] (zz_j_div_lcm). *)
Theorem zz_lcm_range_pow_divides : forall (N p e : nat),
  (1 <= p ^ e)%nat -> (p ^ e <= N)%nat ->
  Bdiv (Z.of_nat (p ^ e)) (zz_lcm_range N).
Proof.
  intros N p e Hlo Hhi.
  apply zz_j_div_lcm.
  apply BidT_intro. apply Bool.andb_true_iff. split.
  - apply Nat.ltb_lt. exact Hlo.
  - apply Nat.leb_le. exact Hhi.
Qed.

(* Divisibility combination: a divides c and b divides d imply the
   product a*b divides the product c*d (witness the swapped product of
   the two quotient witnesses). *)
Theorem zz_bdiv_mul_combine : forall a b c d : Z,
  Bdiv a c -> Bdiv b d -> Bdiv (a * b) (c * d).
Proof.
  intros a b c d [x Hx] [y Hy].
  exists (y * x).
  apply Bid_elim in Hx. apply Bid_elim in Hy.
  apply Bid_intro.
  replace (a * b * (y * x)) with (a * x * (b * y)) by ring.
  rewrite Hx, Hy. reflexivity.
Qed.

(* Coprime splitting: a divides the product b*c and gcd(a, b) = 1 imply
   a divides c. The witness is constructed arithmetically as z / b: the
   stdlib Gauss lemma runs at the Prop level to certify b divides z, the
   resulting zero-modulus equation feeds the division identity
   Z.div_mod, and b cancels by Z.mul_cancel_l. The degenerate case b = 0
   forces a = ±1 (Z.gcd_0_r) and is closed with witness ±c directly. *)
Theorem zz_bdiv_gauss_split : forall a b c : Z,
  Bdiv a (b * c) -> Z.gcd a b = 1 -> Bdiv a c.
Proof.
  intros a b c [z Hz] Hg.
  apply Bid_elim in Hz.
  assert (Hbz : (b | z)).
  { apply (Gauss b a z).
    - exists c. rewrite Hz. ring.
    - apply rel_prime_sym. exact (proj1 (Zgcd_1_rel_prime a b) Hg). }
  assert (Hmod : z mod b = 0) by (apply Zdivide_mod; exact Hbz).
  destruct (Z.eq_dec b 0) as [Hb0 | Hbne].
  - rewrite Hb0, Z.gcd_0_r in Hg.
    destruct (Z.eq_dec a 1) as [Ha1 | Ha1].
    + exists c. apply Bid_intro. rewrite Ha1. ring.
    + destruct (Z.eq_dec a (-1)) as [Ham | Ham].
      * exists (- c). apply Bid_intro. rewrite Ham. ring.
      * exfalso.
        destruct (Z.le_gt_cases 0 a) as [Hpos | Hneg].
        -- rewrite Z.abs_eq in Hg by exact Hpos. lia.
        -- rewrite Z.abs_neq in Hg by lia. lia.
  - assert (Hdm0 : z = b * (z / b) + z mod b) by (apply Z.div_mod; exact Hbne).
    rewrite Hmod in Hdm0. rewrite Z.add_0_r in Hdm0.
    rewrite Hdm0 in Hz.
    exists (z / b). apply Bid_intro.
    assert (H1 : ((a * (z / b)) - c) * b = 0).
    { replace (((a * (z / b)) - c) * b)
        with (a * (b * (z / b)) - b * c) by ring.
      rewrite Hz. ring. }
    destruct (proj1 (Z.mul_eq_0 _ _) H1) as [E | E]; lia.
Qed.

(* ================= Section 5. Divisibility combiners ================= *)

(* Bdiv passes through right multiplication of the target. *)
Lemma zz_bdiv_mul_absorb_r : forall a b c : Z,
  Bdiv a b -> Bdiv a (b * c).
Proof.
  intros a b c [z Hz]. apply Bid_elim in Hz.
  exists (z * c). apply Bid_intro.
  replace (a * (z * c)) with (a * z * c) by ring.
  rewrite Hz. reflexivity.
Qed.

(* Bdiv transitivity. *)
Lemma zz_bdiv_trans : forall a b c : Z,
  Bdiv a b -> Bdiv b c -> Bdiv a c.
Proof.
  intros a b c [x Hx] [y Hy]. apply Bid_elim in Hx. apply Bid_elim in Hy.
  exists (x * y). apply Bid_intro.
  replace (a * (x * y)) with (a * x * y) by ring.
  rewrite Hx. exact Hy.
Qed.

(* Two coprime divisors of M have coprime product dividing M: from
   M = a * w and gcd(b, a) = 1, Gauss moves b down to the quotient w. *)
Lemma zz_bdiv_coprime_combine : forall a b M : Z,
  (0 < a)%Z -> Bdiv a M -> Bdiv b M -> Z.gcd a b = 1 -> Bdiv (a * b) M.
Proof.
  intros a b M Ha [w Hw] [y Hy] Hg.
  apply Bid_elim in Hw. apply Bid_elim in Hy.
  assert (Hba : Z.gcd b a = 1) by (rewrite Z.gcd_comm; exact Hg).
  assert (Hbw : Bdiv b (a * w)).
  { exists y. apply Bid_intro. rewrite Hy. symmetry. exact Hw. }
  destruct (zz_bdiv_gauss_split b a w Hbw Hba) as [z Hz].
  apply Bid_elim in Hz.
  exists z. apply Bid_intro.
  replace (a * b * z) with (a * (b * z)) by ring.
  rewrite Hz, <- Hw. ring.
Qed.

(* ================= Section 6. Prime factor existence (B3.3) ================= *)

(* Bridge from the tree trial-division face to the certified-tree prime
   predicate: a divisor d of k with 2 <= d < k would make k mod d zero,
   contradicting zz_primeb_spec. *)
Lemma zz_primeb_pr_prime : forall k : nat, zz_primeb k = true -> pr_prime k.
Proof.
  intros k Hk. split.
  - pose proof (zz_primeb_prime k Hk) as H1.
    apply (proj1 (Nat.ltb_lt 1 k)) in H1. lia.
  - intros d Hd2 Hdlt Hdiv.
    pose proof (zz_primeb_spec k Hk (Z.of_nat d) ltac:(lia) ltac:(lia) ltac:(lia))
      as Hne.
    destruct Hdiv as [q Hq].
    assert (HdZ : (Z.of_nat d | Z.of_nat k)%Z).
    { exists (Z.of_nat q). rewrite <- Nat2Z.inj_mul, Hq. reflexivity. }
    apply Zdivide_mod in HdZ. rewrite HdZ in Hne. discriminate.
Qed.

(* When the trial-division fold answers false, a divisor in [2, d] has
   been found (witness extracted along the fold). *)
Lemma zz_nodiv_upto_false_wit : forall (d : nat) (k : Z),
  zz_nodiv_upto k d = false ->
  sigT (fun e : nat => prod (BidT (Nat.leb 2 e))
        (prod (BidT (Nat.leb e d))
              (BidT (Z.eqb (k mod Z.of_nat e) 0)))).
Proof.
  intro d. induction d as [|d IH]; intros k H.
  - cbn [zz_nodiv_upto] in H. discriminate H.
  - cbn [zz_nodiv_upto] in H.
    destruct (Z.ltb (Z.of_nat (S d)) 2) eqn:Hlt.
    + discriminate H.
    + destruct (Z.eqb (k mod Z.of_nat (S d)) 0) eqn:He.
      * assert (Hge : (2 <= S d)%nat).
        { apply (proj1 (Z.ltb_ge _ _)) in Hlt. lia. }
        exists (S d). split.
        -- apply BidT_intro. apply Nat.leb_le. exact Hge.
        -- split.
           ++ apply BidT_intro. apply Nat.leb_le. lia.
           ++ apply BidT_intro. exact He.
      * destruct (IH k H) as [e [Hw2 [Hw3 Hw4]]].
        exists e. split.
        -- exact Hw2.
        -- split.
           ++ apply BidT_elim in Hw3.
              apply (proj1 (Nat.leb_le _ _)) in Hw3.
              apply BidT_intro. apply Nat.leb_le. lia.
           ++ exact Hw4.
Qed.

(* Node B3.3a: every m >= 2 has a prime factor, in the Set-carried face
   (boolean prime flag plus a divisibility witness). The auxiliary form
   inducts on a bound k (Set-valued goals need the bound-induction
   shape; lt_wf_ind is Prop-only). *)
Lemma zz_prime_factor_aux : forall k m : nat, (m <= k)%nat ->
  (2 <= m)%nat ->
  sigT (fun p : nat => prod (BidT (zz_primeb p))
        (Bdiv (Z.of_nat p) (Z.of_nat m))).
Proof.
  induction k as [|k IH]; intros m Hmk Hm.
  - lia.
  - destruct (zz_primeb m) eqn:E.
    * exists m. split.
      -- apply BidT_intro. exact E.
      -- exists 1%Z. apply Bid_intro. ring.
    * assert (Hnd : zz_nodiv_upto (Z.of_nat m) (m - 1)%nat = false).
      { unfold zz_primeb in E. apply Bool.andb_false_iff in E.
        destruct E as [E | E].
        - apply (proj1 (Nat.ltb_ge 1 m)) in E. lia.
        - exact E. }
      destruct (zz_nodiv_upto_false_wit (m - 1)%nat (Z.of_nat m) Hnd)
        as [d [Hd2 [Hdle Hmod]]].
      apply BidT_elim in Hd2. apply BidT_elim in Hdle.
      apply BidT_elim in Hmod.
      apply (proj1 (Nat.leb_le 2 d)) in Hd2.
      apply (proj1 (Nat.leb_le d (m - 1))) in Hdle.
      apply (proj1 (Z.eqb_eq _ _)) in Hmod.
      destruct (IH d ltac:(lia) Hd2) as [p [Hpb Hpd]].
      apply BidT_elim in Hpb.
      exists p. split.
      + apply BidT_intro. exact Hpb.
      + apply (zz_bdiv_trans (Z.of_nat p) (Z.of_nat d) (Z.of_nat m) Hpd).
        apply Bdiv_of_mod; [lia | exact Hmod].
Qed.

Theorem zz_prime_factor_ex : forall m : nat,
  (2 <= m)%nat ->
  sigT (fun p : nat => prod (BidT (zz_primeb p))
        (Bdiv (Z.of_nat p) (Z.of_nat m))).
Proof.
  intro m. apply (zz_prime_factor_aux m m (Nat.le_refl m)).
Qed.

(* Node B3.3b: stripping the exact power of a prime dividing m. For p
   prime with p | m there are e >= 0 and u with m = p^(e+1) * u and
   p not dividing u (both faces Set-carried; the non-divisibility is
   carried by a boolean congruence flag). *)
(* Bound-induction core of node B3.3b (Set-valued goal shape). *)
Lemma zz_prime_strip_aux : forall (k p m : nat), (m <= k)%nat ->
  (1 <= m)%nat -> BidT (zz_primeb p) -> (2 <= p)%nat ->
  Bdiv (Z.of_nat p) (Z.of_nat m) ->
  sigT (fun e : nat => sigT (fun u : Z =>
    prod (Bid Z (Z.of_nat (Nat.pow p (S e)) * u) (Z.of_nat m))
         (BidT (negb (Z.eqb (u mod Z.of_nat p) 0))))).
Proof.
  intros k p. induction k as [|k IH]; intros m Hmk Hm Hpb Hp2 Hd.
  - lia.
  - apply BidT_elim in Hpb.
    destruct Hd as [z Hz]. apply Bid_elim in Hz.
    assert (Hz1 : (1 <= z)%Z) by nia.
    assert (Hzid : Z.of_nat (Z.to_nat z) = z) by (apply Z2Nat.id; lia).
    assert (Hzlt : (z < Z.of_nat m)%Z) by nia.
    rewrite <- Hzid in Hzlt.
    destruct (Z.eq_dec (z mod Z.of_nat p) 0) as [Hmod0 | Hmodne].
    + (* p divides z = m / p: strip recursively *)
      assert (Hq : (Z.to_nat z < m)%nat)
        by (apply (proj2 (Nat2Z.inj_lt _ _)); exact Hzlt).
      assert (Hqdiv : Bdiv (Z.of_nat p) (Z.of_nat (Z.to_nat z))).
      { apply Bdiv_of_mod; [lia |]. rewrite Hzid. exact Hmod0. }
      destruct (IH (Z.to_nat z) ltac:(lia) ltac:(lia) (BidT_intro (zz_primeb p) Hpb)
                  ltac:(lia) Hqdiv) as [e [u [Hu Hnu]]].
      apply Bid_elim in Hu.
      exists (S e). exists u. split.
      * assert (Hpe : Nat.pow p (S (S e)) = (p * Nat.pow p (S e))%nat)
          by (rewrite Nat.pow_succ_r'; reflexivity).
        apply Bid_intro. rewrite Hpe, Nat2Z.inj_mul, <- Hz. nia.
      * exact Hnu.
    + (* p does not divide z: the strip stops with e = 0 *)
      exists 0%nat. exists z. split.
      * apply Bid_intro. rewrite Nat.pow_1_r. exact Hz.
      * apply BidT_intro. apply Bool.negb_true_iff.
        apply (proj2 (Z.eqb_neq _ _)). exact Hmodne.
Qed.

Theorem zz_prime_strip_ex : forall (m p : nat),
  (1 <= m)%nat -> BidT (zz_primeb p) -> (2 <= p)%nat ->
  Bdiv (Z.of_nat p) (Z.of_nat m) ->
  sigT (fun e : nat => sigT (fun u : Z =>
    prod (Bid Z (Z.of_nat (Nat.pow p (S e)) * u) (Z.of_nat m))
         (BidT (negb (Z.eqb (u mod Z.of_nat p) 0))))).
Proof.
  intros m p. apply (zz_prime_strip_aux m p m (Nat.le_refl m)).
Qed.

(* ================= Section 7. Integer k-th root and the psi fold (B3.4) ================= *)

(* Integer k-th root: largest r with r^k <= N, by a one-step recurrence
   that grows the root by at most one as N grows. *)
Fixpoint zz_iroot (k N : nat) : nat :=
  match N with
  | O => O
  | S N' => let r := zz_iroot k N' in
            if Nat.leb (Nat.pow (S r) k) (S N') then S r else r
  end.

Lemma zz_iroot_spec : forall k N : nat, (1 <= k)%nat ->
  (Nat.pow (zz_iroot k N) k <= N)%nat /\
  (N < Nat.pow (S (zz_iroot k N)) k)%nat.
Proof.
  intros k N Hk. destruct k as [|k']; [lia |].
  induction N as [|N IH].
  - split.
    + cbn [zz_iroot Nat.pow]. lia.
    + cbn [zz_iroot]. rewrite Nat.pow_1_l. lia.
  - destruct IH as [IH1 IH2].
    cbn [zz_iroot].
    destruct (Nat.leb (Nat.pow (S (zz_iroot (S k') N)) (S k')) (S N)) eqn:E.
    + apply (proj1 (Nat.leb_le _ _)) in E.
      assert (Hmono : (Nat.pow (S (S (zz_iroot (S k') N))) (S k')
                       > Nat.pow (S (zz_iroot (S k') N)) (S k'))%nat).
      { replace (Nat.pow (S (S (zz_iroot (S k') N))) (S k'))
          with ((S (S (zz_iroot (S k') N))
                * Nat.pow (S (S (zz_iroot (S k') N))) k')%nat)
          by (rewrite Nat.pow_succ_r'; reflexivity).
        replace (Nat.pow (S (zz_iroot (S k') N)) (S k'))
          with ((S (zz_iroot (S k') N)
                * Nat.pow (S (zz_iroot (S k') N)) k')%nat)
          by (rewrite Nat.pow_succ_r'; reflexivity).
        assert (Hge1 : (1 <= Nat.pow (S (zz_iroot (S k') N)) k')%nat).
        { apply Nat.le_trans with (Nat.pow (S (zz_iroot (S k') N)) 0).
          - rewrite Nat.pow_0_r. lia.
          - apply Nat.pow_le_mono_r; lia. }
        assert (Hge2 : (Nat.pow (S (S (zz_iroot (S k') N))) k'
                        >= Nat.pow (S (zz_iroot (S k') N)) k')%nat)
          by (apply Nat.pow_le_mono_l; lia).
        nia. }
      split; [exact E | lia].
    + apply (proj1 (Nat.leb_gt _ _)) in E.
      split; [lia | exact E].
Qed.

Lemma zz_iroot_le_pow : forall k p N : nat, (1 <= k)%nat ->
  (p <= zz_iroot k N)%nat -> (Nat.pow p k <= N)%nat.
Proof.
  intros k p N Hk Hle.
  pose proof (proj1 (zz_iroot_spec k N Hk)) as H1.
  destruct k as [|k2]; [lia |].
  destruct (Nat.eq_dec p 0) as [Hp0 | Hpne].
  - rewrite Hp0. cbn [Nat.pow]. lia.
  - apply Nat.le_trans with (Nat.pow (zz_iroot (S k2) N) (S k2)).
    + apply Nat.pow_le_mono_l. exact Hle.
    + exact H1.
Qed.

Lemma zz_iroot_pow_le : forall k p N : nat, (1 <= k)%nat ->
  (Nat.pow p k <= N)%nat -> (p <= zz_iroot k N)%nat.
Proof.
  intros k p N Hk Hp.
  pose proof (proj2 (zz_iroot_spec k N Hk)) as H2.
  destruct (Nat.le_gt_cases p (zz_iroot k N)) as [Hle | Hgt].
  - exact Hle.
  - exfalso.
    assert (Hge : (S (zz_iroot k N) <= p)%nat) by lia.
    assert (H3 : (Nat.pow (S (zz_iroot k N)) k <= Nat.pow p k)%nat)
      by (apply Nat.pow_le_mono_l; lia).
    lia.
Qed.

Lemma zz_iroot_one : forall N : nat, zz_iroot 1 N = N.
Proof.
  intro N.
  pose proof (proj1 (zz_iroot_spec 1 N ltac:(lia))) as H1.
  pose proof (proj2 (zz_iroot_spec 1 N ltac:(lia))) as H2.
  rewrite Nat.pow_1_r in H1, H2. lia.
Qed.

Lemma zz_iroot_anti : forall k j N : nat, (2 <= j)%nat -> (j <= k)%nat ->
  (zz_iroot k N <= zz_iroot j N)%nat.
Proof.
  intros k j N Hj Hjk.
  pose proof (proj2 (zz_iroot_spec j N ltac:(lia))) as H2.
  pose proof (proj1 (zz_iroot_spec k N ltac:(lia))) as H1.
  destruct (Nat.le_gt_cases (zz_iroot k N) (zz_iroot j N)) as [Hle | Hgt].
  - exact Hle.
  - exfalso.
    assert (Hge : (S (zz_iroot j N) <= zz_iroot k N)%nat) by lia.
    assert (H3 : (Nat.pow (S (zz_iroot j N)) k <= Nat.pow (zz_iroot k N) k)%nat)
      by (apply Nat.pow_le_mono_l; lia).
    assert (H4 : (Nat.pow (S (zz_iroot j N)) j
                  <= Nat.pow (S (zz_iroot j N)) k)%nat)
      by (apply Nat.pow_le_mono_r; lia).
    lia.
Qed.

(* The psi fold: zz_psi_prod N k is the product over i = 1..k of the
   primorial of the integer i-th root of N, and zz_psi N is the full
   fold up to log2 N — the prime-power assembly behind e^psi. *)
Definition zz_psi_fac (N k : nat) : nat := pec_prim (zz_iroot k N).

Fixpoint zz_psi_prod (N k : nat) : nat :=
  match k with
  | O => 1%nat
  | S k' => (zz_psi_prod N k' * zz_psi_fac N (S k'))%nat
  end.

Definition zz_psi (N : nat) : nat := zz_psi_prod N (Nat.log2 N).

(* Count of indices i in [1, k] with p^i <= N. *)
Fixpoint zz_cnt (p N k : nat) : nat :=
  match k with
  | O => 0%nat
  | S k' => (zz_cnt p N k' + (if Nat.leb (Nat.pow p (S k')) N then 1%nat else 0%nat))%nat
  end.

Lemma zz_cnt_S : forall p N k : nat,
  zz_cnt p N (S k) =
  (zz_cnt p N k + (if Nat.leb (Nat.pow p (S k)) N then 1%nat else 0%nat))%nat.
Proof. reflexivity. Qed.

Lemma zz_cnt_S_true : forall p N k : nat, (Nat.pow p (S k) <= N)%nat ->
  zz_cnt p N (S k) = S (zz_cnt p N k).
Proof.
  intros p N k H. rewrite zz_cnt_S.
  replace (Nat.leb (Nat.pow p (S k)) N) with true
    by (symmetry; apply Nat.leb_le; exact H).
  lia.
Qed.

Lemma zz_cnt_S_false : forall p N k : nat, (N < Nat.pow p (S k))%nat ->
  zz_cnt p N (S k) = zz_cnt p N k.
Proof.
  intros p N k H. rewrite zz_cnt_S.
  replace (Nat.leb (Nat.pow p (S k)) N) with false
    by (symmetry; apply Nat.leb_gt; exact H).
  lia.
Qed.

Lemma zz_cnt_step_ge : forall p N l : nat,
  (zz_cnt p N l <= zz_cnt p N (S l))%nat.
Proof.
  intros p N l. rewrite zz_cnt_S.
  destruct (Nat.leb (Nat.pow p (S l)) N); lia.
Qed.

Lemma zz_cnt_mono : forall p N k l : nat, (k <= l)%nat ->
  (zz_cnt p N k <= zz_cnt p N l)%nat.
Proof.
  intros p N k l H. induction l as [|l IH].
  - assert (Hk : k = 0%nat) by lia. rewrite Hk. apply Nat.le_refl.
  - destruct (Nat.eq_dec k (S l)) as [Heq | Hne].
    + rewrite Heq. apply Nat.le_refl.
    + apply Nat.le_trans with (zz_cnt p N l).
      * apply IH. lia.
      * apply zz_cnt_step_ge.
Qed.

Lemma zz_cnt_ge : forall p N k : nat, (2 <= p)%nat ->
  (Nat.pow p k <= N)%nat -> (k <= zz_cnt p N k)%nat.
Proof.
  intros p N k Hp. induction k as [|k IH]; intros Hle.
  - cbn [zz_cnt]. lia.
  - assert (Hle' : (Nat.pow p k <= N)%nat).
    { apply Nat.le_trans with (Nat.pow p (S k)).
      - apply Nat.pow_le_mono_r; lia.
      - exact Hle. }
    specialize (IH Hle').
    rewrite zz_cnt_S_true by exact Hle. lia.
Qed.

(* Membership of the window prime list: a prime p with 1 < p <= 1 + k
   occurs in pec_win 1 k (converse of pec_win_in, by induction). *)
Lemma pec_win_in_intro : forall k p : nat, (1 < p)%nat -> (p <= 1 + k)%nat ->
  pr_prime p -> In p (pec_win 1 k).
Proof.
  intro k. induction k as [|k IH]; intros p Hp1 Hp2 Hpp.
  - lia.
  - cbn [pec_win].
    destruct (Nat.eq_dec p (1 + S k)%nat) as [Heq | Hne].
    + rewrite Heq.
      destruct (pr_prime_bool (1 + S k)) eqn:Eb.
      * simpl. left. reflexivity.
      * exfalso. rewrite <- Heq in Eb.
        rewrite (pr_prime_bool_false p Hpp) in Eb. discriminate.
    + destruct (pr_prime_bool (1 + S k)) eqn:Eb.
      * simpl. right. apply IH; try lia. exact Hpp.
      * apply IH; try lia. exact Hpp.
Qed.

(* Every member of a list divides the folded product: the divisibility
   core runs at the Prop level (list membership is a disjunction), and
   the Set-carried face is packaged through Bdiv_of_mod. *)
Lemma pec_fold_dvd : forall (l : list nat) (p : nat),
  In p l -> (Z.of_nat p | Z.of_nat (fold_right Nat.mul 1%nat l))%Z.
Proof.
  induction l as [|a l IH]; intros p Hin.
  - destruct Hin.
  - cbn [fold_right]. destruct Hin as [Heq | Hin].
    + rewrite Heq. exists (Z.of_nat (fold_right Nat.mul 1%nat l)).
      rewrite Nat2Z.inj_mul. ring.
    + destruct (IH p Hin) as [z0 Hz0].
      exists (Z.of_nat a * z0).
      rewrite Nat2Z.inj_mul, Hz0. ring.
Qed.

Lemma pec_fold_bdiv : forall (l : list nat) (p : nat),
  (2 <= p)%nat -> In p l ->
  Bdiv (Z.of_nat p) (Z.of_nat (fold_right Nat.mul 1%nat l)).
Proof.
  intros l p Hp2 Hin.
  assert (Hp0 : Z.of_nat p <> 0%Z) by lia.
  apply Bdiv_of_mod; [exact Hp0 |].
  apply (proj2 (Z.mod_divide _ _ Hp0)).
  apply pec_fold_dvd. exact Hin.
Qed.

(* Core fold-counting lemma: with multiplicity e <= zz_cnt p N k (the
   count of indices i <= k with p^i <= N), the prime power p^e divides
   the psi fold — each qualifying index contributes one factor p. *)
Theorem zz_psi_prod_pow_div : forall (p N k : nat),
  BidT (zz_primeb p) -> (2 <= p)%nat ->
  forall e : nat, (1 <= e)%nat -> (Nat.pow p e <= N)%nat ->
  (e <= zz_cnt p N k)%nat ->
  Bdiv (Z.of_nat (Nat.pow p e)) (Z.of_nat (zz_psi_prod N k)).
Proof.
  intros p N k Hpb Hp2.
  apply BidT_elim in Hpb. revert Hpb.
  induction k as [|k IH]; intros Hpb e He1 Hle Hcntle.
  - cbn [zz_cnt] in Hcntle. lia.
  - cbn [zz_psi_prod]. rewrite Nat2Z.inj_mul.
    unfold zz_psi_fac, pec_prim.
    destruct (Nat.leb (Nat.pow p (S k)) N) eqn:E.
    + apply (proj1 (Nat.leb_le _ _)) in E.
      rewrite (zz_cnt_S_true p N k E) in Hcntle.
      destruct (Nat.leb e (zz_cnt p N k)) eqn:Hek.
      * apply (proj1 (Nat.leb_le _ _)) in Hek.
        apply zz_bdiv_mul_absorb_r.
        apply IH; try assumption.
      * apply (proj1 (Nat.leb_gt _ _)) in Hek.
        assert (Hpm : (Nat.pow p (e - 1) <= Nat.pow p e)%nat)
          by (apply Nat.pow_le_mono_r; lia).
        assert (Hprev : Bdiv (Z.of_nat (Nat.pow p (e - 1)%nat))
                        (Z.of_nat (zz_psi_prod N k))).
        { destruct (Nat.eq_dec e 1) as [Heq1 | Hegt1].
          - replace (e - 1)%nat with 0%nat by lia.
            rewrite Nat.pow_0_r.
            exists (Z.of_nat (zz_psi_prod N k)). apply Bid_intro.
            change (Z.of_nat 1) with 1%Z. rewrite Z.mul_1_l. reflexivity.
          - apply IH; try assumption; try lia. }
        assert (Hpe : Nat.pow p e = (Nat.pow p (e - 1)%nat * p)%nat).
        { destruct e as [|e']; [lia |].
          rewrite Nat.pow_succ_r'.
          replace (S e' - 1)%nat with e' by lia. apply Nat.mul_comm. }
        rewrite Hpe, Nat2Z.inj_mul.
        assert (Hroot : (p <= zz_iroot (S k) N)%nat)
          by (apply zz_iroot_pow_le with (k := S k); [lia | exact E]).
        assert (Hin : In p (pec_win 1 (zz_iroot (S k) N - 1)%nat)).
        { apply pec_win_in_intro; try lia.
          apply zz_primeb_pr_prime. exact Hpb. }
        apply (zz_bdiv_mul_combine (Z.of_nat (Nat.pow p (e - 1)%nat))
                (Z.of_nat p) (Z.of_nat (zz_psi_prod N k))).
        { exact Hprev. }
        { apply (pec_fold_bdiv (pec_win 1 (zz_iroot (S k) N - 1)%nat) p
                  ltac:(lia) Hin). }
    + apply (proj1 (Nat.leb_gt _ _)) in E.
      rewrite (zz_cnt_S_false p N k E) in Hcntle.
      apply zz_bdiv_mul_absorb_r.
      apply IH; try assumption; try lia.
Qed.

(* Node B3.4: the psi fold absorbs every m in [1, N] — induction on a
   bound peels one prime factor at a time (nodes B3.3a + B3.3b;
   Set-valued goal shape). *)
Lemma zz_psi_absorbs_aux : forall (N k m : nat), (m <= k)%nat ->
  (1 <= N)%nat -> (1 <= m)%nat -> (m <= N)%nat ->
  Bdiv (Z.of_nat m) (Z.of_nat (zz_psi N)).
Proof.
  intros N. induction k as [|k IH]; intros m Hmk HN Hm1 HmN.
  - lia.
  - destruct (Nat.eq_dec m 1) as [Hm1eq | Hm1ne].
    + rewrite Hm1eq. exists (Z.of_nat (zz_psi N)). apply Bid_intro.
      change (Z.of_nat 1) with 1%Z. rewrite Z.mul_1_l. reflexivity.
  + assert (Hm2 : (2 <= m)%nat) by lia.
      destruct (zz_prime_factor_ex m Hm2) as [p [Hpb Hpd]].
      apply BidT_elim in Hpb.
      assert (Hp2 : (2 <= p)%nat).
      { pose proof (zz_primeb_prime p Hpb) as H1p.
        apply (proj1 (Nat.ltb_lt 1 p)) in H1p. lia. }
      destruct (zz_prime_strip_ex m p ltac:(lia) (BidT_intro (zz_primeb p) Hpb) ltac:(lia) Hpd)
        as [e [u [Hu Hnu]]].
      apply Bid_elim in Hu.
      assert (Hp1 : (Nat.pow p 1 <= Nat.pow p (S e))%nat)
        by (apply Nat.pow_le_mono_r; lia).
      rewrite Nat.pow_1_r in Hp1.
      assert (Hpge : (1 <= Nat.pow p (S e))%nat) by lia.
      assert (Hu1 : (1 <= u)%Z) by nia.
      assert (Hum : (Z.of_nat (Nat.pow p (S e)) <= Z.of_nat m)%Z) by nia.
      assert (HumNat : (Nat.pow p (S e) <= m)%nat)
        by (apply (proj2 (Nat2Z.inj_le _ _)); exact Hum).
      assert (HpeN : (Nat.pow p (S e) <= N)%nat) by lia.
      assert (Huid : Z.of_nat (Z.to_nat u) = u) by (apply Z2Nat.id; lia).
      assert (Hult : (Z.to_nat u < m)%nat).
      { apply (proj2 (Nat2Z.inj_lt _ _)). rewrite Huid. nia. }
      assert (Hule : (Z.to_nat u <= N)%nat).
      { apply (proj2 (Nat2Z.inj_le _ _)). rewrite Huid. nia. }
      assert (Hud : Bdiv u (Z.of_nat (zz_psi N))).
      { assert (Hstep := IH (Z.to_nat u) ltac:(lia) HN ltac:(lia) Hule).
        rewrite Huid in Hstep. exact Hstep. }
      assert (Hlog : (S e <= Nat.log2 N)%nat).
      { destruct (Nat.log2_spec N ltac:(lia)) as [Hl1 Hl2].
        assert (Hp2le : (Nat.pow 2 (S e) <= Nat.pow p (S e))%nat)
          by (apply Nat.pow_le_mono_l; lia).
        destruct (Nat.le_gt_cases (S e) (Nat.log2 N)) as [Hok | Hgt].
  + exact Hok.
  + exfalso.
          assert (H4 : (Nat.pow 2 (S (Nat.log2 N)) <= Nat.pow 2 (S e))%nat)
            by (apply Nat.pow_le_mono_r; lia).
          lia. }
      assert (Hcnt : (S e <= zz_cnt p N (Nat.log2 N))%nat).
      { apply Nat.le_trans with (zz_cnt p N (S e)).
  + apply zz_cnt_ge; lia.
  + apply zz_cnt_mono. exact Hlog. }
      assert (Hpow : Bdiv (Z.of_nat (Nat.pow p (S e))) (Z.of_nat (zz_psi N))).
      { unfold zz_psi.
        apply zz_psi_prod_pow_div;
          [apply BidT_intro; exact Hpb | exact Hp2 | lia | exact HpeN
               | exact Hcnt]. }
      assert (Hpowconv : Z.of_nat (Nat.pow p (S e))
                         = Z.of_nat p ^ Z.of_nat (S e))
        by apply Nat2Z.inj_pow.
      assert (Hgcd : Z.gcd (Z.of_nat (Nat.pow p (S e))) u = 1%Z).
      { rewrite Hpowconv. apply (proj2 (Zgcd_1_rel_prime _ _)).
        apply zz_rel_prime_pow_l.
        apply (prime_rel_prime (Z.of_nat p)).
  + apply zz_primeb_prime_std. exact Hpb.
  + intro Hdvd.
          apply Bid_elim in Hnu.
          pose proof (proj1 (Bool.negb_true_iff _) Hnu) as Hne0.
          pose proof (proj1 (Z.eqb_neq _ _) Hne0) as Hne.
          apply Zdivide_mod in Hdvd. rewrite Hdvd in Hne.
          exact (Hne eq_refl). }
      rewrite <- Hu.
      apply zz_bdiv_coprime_combine;
        [lia | exact Hpow | exact Hud | exact Hgcd].
Qed.

Theorem zz_psi_absorbs : forall (N m : nat),
  (1 <= N)%nat -> (1 <= m)%nat -> (m <= N)%nat ->
  Bdiv (Z.of_nat m) (Z.of_nat (zz_psi N)).
Proof.
  intros N m. apply (zz_psi_absorbs_aux N m m (Nat.le_refl m)).
Qed.

(* The lcm of [1, N] divides any common multiple of [1, N]. *)
Lemma zz_lcm_range_common : forall (N : nat) (M : Z),
  (forall j : nat, (1 <= j)%nat -> (j <= N)%nat -> (Z.of_nat j | M)%Z) ->
  (zz_lcm_range N | M)%Z.
Proof.
  induction N as [|N IH]; intros M Hall.
  - apply Z.divide_1_l.
  - cbn [zz_lcm_range]. apply Z.lcm_least.
    + apply IH. intros j H1 H2. apply Hall; lia.
    + apply Hall; lia.
Qed.

Lemma zz_lcm_range_pos : forall N : nat, (1 <= zz_lcm_range N)%Z.
Proof.
  induction N as [|N IH].
  - cbn [zz_lcm_range]. lia.
  - cbn [zz_lcm_range].
    pose proof (Z.lcm_nonneg (zz_lcm_range N) (Z.of_nat (S N))) as Hnn.
    destruct (Z.le_gt_cases 1 (Z.lcm (zz_lcm_range N) (Z.of_nat (S N))))
      as [Hok | Hgt].
    + exact Hok.
    + exfalso.
      assert (H0 : Z.lcm (zz_lcm_range N) (Z.of_nat (S N)) = 0%Z) by lia.
      apply (proj1 (Z.lcm_eq_0 _ _)) in H0.
      destruct H0 as [H0 | H0].
      * rewrite H0 in IH. lia.
      * discriminate H0.
Qed.

(* Node B3.4 (born face, Set-carried): lcm(1..N) divides the psi fold,
   hence lcm(1..N) <= zz_psi N for all N >= 1. *)
Theorem zz_lcm_range_div_psi : forall N : nat, (1 <= N)%nat ->
  Bdiv (zz_lcm_range N) (Z.of_nat (zz_psi N)).
Proof.
  intros N HN.
  assert (Hne : zz_lcm_range N <> 0%Z).
  { pose proof (zz_lcm_range_pos N) as Hp. lia. }
  apply Bdiv_of_mod; [exact Hne |].
  apply (proj2 (Z.mod_divide _ _ Hne)).
  apply zz_lcm_range_common.
  intros j Hj1 Hj2.
  destruct (zz_psi_absorbs N j HN Hj1 Hj2) as [z Hz].
  apply Bid_elim in Hz. exists z. rewrite Z.mul_comm. symmetry. exact Hz.
Qed.

(* ================= Section 4. Certification face ================= *)

Print Assumptions zz_primeb_prime_std.
Print Assumptions zz_ppow_coprime.
Print Assumptions zz_lcm_range_pow_divides.
Print Assumptions zz_bdiv_mul_combine.
Print Assumptions zz_bdiv_gauss_split.
Print Assumptions zz_prime_factor_ex.
Print Assumptions zz_prime_strip_ex.
Print Assumptions zz_psi_prod_pow_div.
Print Assumptions zz_psi_absorbs.
Print Assumptions zz_lcm_range_div_psi.

From Stdlib Require Import Extraction.
Separate Extraction zz_lcm_range_pow_divides zz_bdiv_mul_combine
  zz_bdiv_gauss_split zz_ppow_coprime zz_prime_factor_ex zz_prime_strip_ex
  zz_psi_prod_pow_div zz_psi_absorbs zz_lcm_range_div_psi.
