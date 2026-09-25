(*
   P6：pi_next_req 载体 conv（我节 vs 批 A 节闭面，含 req_Z_rel_pos
   证人证词条位）；P7：KL 语句面 req_refl 全收口可达性 *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require Import G05_LogSmall.
Require Import UpReqAlign4.
Import RealInterfaceEnhancedMod.

Module ConvProbe3T24.
Section ConvProbe3T24.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable eta : R.
Definition pos_dist (p : S -> R) : Set := forall s : S, lt zero (p s).
Definition advantage_aug_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=
  req_minus (reward s)
            (mult beta (req_minus (log (pi_t s) (Hpi_t s)) (log (pi_ref s) (pi_ref_pos s)))).
Definition Z_rel_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) : R :=
  sumf (fun s => mult (pi_t s)
                      (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                          (advantage_aug_req pi_t Hpi_t s))))).
Lemma req_Z_rel_pos :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t), lt zero (Z_rel_req pi_t Hpi_t).
Proof. intros pi_t Hpi_t. unfold Z_rel_req. apply sum_pos. intro s.
  apply mult_positive. - apply Hpi_t. - apply exp_neg_pos. Qed.
Definition pi_next_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=
  mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
       (mult (pi_t s)
             (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                 (advantage_aug_req pi_t Hpi_t s))))).

(* P6：pi_next 载体 conv（req_Z_rel_pos 证人证词条位在其中） *)
Goal forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S),
  req (pi_next_req pi_t Hpi_t s)
      (UpReqAlign4.pi_next_req S sumf sum_pos reward beta beta_pos pi_ref
         pi_ref_pos eta pi_t Hpi_t s).
Proof. intros pi_t Hpi_t s. exact (req_refl (pi_next_req pi_t Hpi_t s)). Qed.

(* P7：KL 面 4 腿 req_refl 收口可达性（我节 req_pi_star_pos 证词条位 vs
   节闭 req_pi_star_pos 应用，包在 relative_entropy_req 里） *)
Definition Z_align_req : R :=
  sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Variable Z_align_pos : lt zero Z_align_req.
Definition pi_star_req (s : S) : R :=
  mult (inv_pos Z_align_req Z_align_pos)
       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Lemma req_pi_star_pos : pos_dist pi_star_req.
Proof. intro s. unfold pi_star_req.
  apply mult_positive. - apply inv_pos_pos. - apply mult_positive.
    + apply pi_ref_pos. + apply exp_neg_pos. Qed.
Definition relative_entropy_req (p q : S -> R) (Hp : pos_dist p) (Hq : pos_dist q) : R :=
  sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))).

Goal req (relative_entropy_req pi_star_req pi_star_req req_pi_star_pos req_pi_star_pos)
         (UpReqAlign4.relative_entropy_req S sumf
            (UpReqAlign4.pi_star_req S sumf reward beta beta_pos pi_ref Z_align_pos)
            (UpReqAlign4.pi_star_req S sumf reward beta beta_pos pi_ref Z_align_pos)
            (UpReqAlign4.req_pi_star_pos S sumf reward beta beta_pos pi_ref
               pi_ref_pos Z_align_pos)
            (UpReqAlign4.req_pi_star_pos S sumf reward beta beta_pos pi_ref
               pi_ref_pos Z_align_pos)).
Proof. exact (req_refl
         (relative_entropy_req pi_star_req pi_star_req req_pi_star_pos
            req_pi_star_pos)). Qed.

End ConvProbe3T24.
End ConvProbe3T24.
