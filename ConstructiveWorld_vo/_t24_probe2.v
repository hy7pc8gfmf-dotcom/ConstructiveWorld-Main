(* _t24_probe2.v — 席T24 批 C 转换失败二分定位（-Full 跑）
   P0 pos_dist 面 → P1 Z_align_req → P2 pi_star_req 逐点 →
   P3 pi_star 证人位（载体+证人）→ P5 Z_rel 证人位 → P4 全语句 *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require Import G05_LogSmall.
Require Import UpReqAlign4.
Import RealInterfaceEnhancedMod.

Module ConvProbeT24.
Section ConvProbeT24.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).

Definition pos_dist (p : S -> R) : Set := forall s : S, lt zero (p s).

(* P0：pos_dist 面 conv（我节常量 vs 节闭全局） *)
Goal forall p : S -> R, pos_dist p -> UpReqAlign4.pos_dist S p.
Proof. intros p Hp. exact Hp. Qed.

Definition Z_align_req : R :=
  sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Variable Z_align_pos : lt zero Z_align_req.

(* P1：Z_align_req conv *)
Goal req Z_align_req (UpReqAlign4.Z_align_req S sumf reward beta beta_pos pi_ref).
Proof. exact (req_refl Z_align_req). Qed.

Definition pi_star_req (s : S) : R :=
  mult (inv_pos Z_align_req Z_align_pos)
       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).

(* P2：pi_star_req 逐点 conv（inv_pos 载体位 = 同一 Z_align_pos 变元） *)
Goal forall s : S, req (pi_star_req s)
  (UpReqAlign4.pi_star_req S sumf reward beta beta_pos pi_ref Z_align_pos s).
Proof. intro s. exact (req_refl (pi_star_req s)). Qed.

(* P3：pi_star 证人位 conv（我的 pos_dist/pi_star_req vs 节闭证人件类型） *)
Lemma my_req_pi_star_pos : pos_dist pi_star_req.
Proof. intro s. unfold pi_star_req.
  apply mult_positive. - apply inv_pos_pos. - apply mult_positive.
    + apply pi_ref_pos. + apply exp_neg_pos. Qed.

Goal pos_dist pi_star_req.
Proof. exact (UpReqAlign4.req_pi_star_pos S sumf reward beta beta_pos
                pi_ref pi_ref_pos Z_align_pos). Qed.

(* P5：Z_rel 链（pi_next 载体核：req_Z_rel_pos 证人位 conv） *)
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Variable eta : R.
Definition advantage_aug_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=
  req_minus (reward s)
            (mult beta (req_minus (log (pi_t s) (Hpi_t s)) (log (pi_ref s) (pi_ref_pos s)))).
Definition Z_rel_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) : R :=
  sumf (fun s => mult (pi_t s)
                      (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                          (advantage_aug_req pi_t Hpi_t s))))).
Lemma my_req_Z_rel_pos :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t), lt zero (Z_rel_req pi_t Hpi_t).
Proof. intros pi_t Hpi_t. unfold Z_rel_req. apply sum_pos. intro s.
  apply mult_positive. - apply Hpi_t. - apply exp_neg_pos. Qed.

Goal forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t),
  lt zero (Z_rel_req pi_t Hpi_t).
Proof. intros pi_t Hpi_t.
  exact (UpReqAlign4.req_Z_rel_pos S sumf sum_pos reward beta beta_pos
           pi_ref pi_ref_pos eta pi_t Hpi_t). Qed.

End ConvProbeT24.
End ConvProbeT24.
