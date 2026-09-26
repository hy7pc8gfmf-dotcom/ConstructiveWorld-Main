(* ==========================================================================)
   AlignIdUnclosed.v — 后向 KL 递推精确恒等式的无条件化组装件
   使命: 以已证桥 req2_backward_kl_step（UpReqAlign3）与 gap 基件 w_subgap_base（UpAlignIdReq）组装出 aiu_backward_kl_exact_uncond——除接口参数外零假设位的后向 KL 逐步递推推论；五段 β 缩放机器逐段复用；原件语句面 KL 参序倒置的判读如实注记。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist、UpReqAlign、UpReqAlign2、UpReqAlign3、UpAlignIdReq（Import RealInterfaceEnhancedMod）。
   对标: 策略梯度的后向 KL 递推恒等式（trust-region 恒等式的形式化）。
   构造性: 全件 Qed 真证；term-mode 显式组装（req_trans/compat 族链，无 destruct）；语句全 Set 层；节内 17 位接口参数为真前提，如实保留为接口义务。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树原地重编），cpu_guard 包裹限载。
   ========================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require Import UpAlignIdReq.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* AiuBackwardKL：件 6 组装链无条件化节                                 *)
(* ============================================================ *)
Section AiuBackwardKL.

Context {R : Set}.
Context {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Hypothesis log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.

Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable eta : R.

(* ---- 局部别名（上游 req2 定义的 δ 透明薄包装，与 UpReqAlign3/        *)
(*      UpAlignIdReq 同式） ---- *)
Definition pos3 (p : S -> R) : Set := @req2_pos_dist R RIS S p.
Definition nrm (p : S -> R) : Set := @req2_norm_one R RIS S sumf p.
Definition KLE (p q : S -> R) (Hp : pos3 p) (Hq : pos3 q) : R :=
  @req2_rel_ent R RIS S sumf p q Hp Hq.
Definition JJ (p : S -> R) (Hp : pos3 p) : R :=
  @req2_J R RIS S sumf reward beta pi_ref pi_ref_pos p Hp.
Definition NPX (pi_t : S -> R) (Hpi_t : pos3 pi_t) (s : S) : R :=
  @req2_pi_next R RIS S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                eta pi_t Hpi_t s.
Definition npx_pos (pi_t : S -> R) (Hpi_t : pos3 pi_t) : pos3 (NPX pi_t Hpi_t) :=
  @req2_pi_next_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                    pi_ref_pos eta pi_t Hpi_t.
Definition ZAL : R :=
  @req2_Z_align R RIS S sumf reward beta beta_pos pi_ref.
Variable ZAL_pos : lt zero ZAL.
Definition PSTR (s : S) : R :=
  @req2_pi_star R RIS S sumf reward beta beta_pos pi_ref ZAL_pos s.
Definition PSTR_pos : pos3 PSTR :=
  @req2_pi_star_pos R RIS S sumf reward beta beta_pos pi_ref pi_ref_pos ZAL_pos.

(* ---- 输入件 1：gap 代换位（UpAlignIdReq.w_subgap_base @ 全参依存）    *)
(*   req_minus (J(pi★) − J(p)) == β·KL(p‖pi★)——件 6 组装链的 Hgap 位。   *)
Lemma aiu_subgap_base : forall (p : S -> R) (Hp : pos3 p) (Hn : nrm p),
  req (req_minus (JJ PSTR PSTR_pos) (JJ p Hp))
      (mult beta (KLE p PSTR Hp PSTR_pos)).
Proof.
  intros p Hp Hn.
  exact (@UpAlignIdReq.w_subgap_base R RIS S sumf sum_ext sum_add sum_linear           log_req_compat log_inv_exp_neg_req           reward beta beta_pos pi_ref pi_ref_pos ZAL_pos p Hp Hn).
Qed.

(* ---- 输入件 2：三 KL 精确恒等桥位（UpReqAlign3.req2_backward_kl_step  *)
(*   @ 全参依存）——件 6 原显式前提位的已证定理供给（PSTR-先序）。        *)
Lemma aiu_bridge_backward_kl_step :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t))
        (plus (mult (req_minus one eta)
                    (KLE PSTR pi_t PSTR_pos Hpi_t))
              (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                    (KLE pi_t (NPX pi_t Hpi_t) Hpi_t
                                (npx_pos pi_t Hpi_t)))).
Proof.
  intros pi_t Hpi_t Hn.
  exact (@req2_backward_kl_step R RIS S sumf sum_ext sum_add sum_linear           sum_pos log_req_compat log_inv_exp_neg_req           reward beta beta_pos pi_ref pi_ref_pos eta ZAL_pos           pi_t Hpi_t Hn).
Qed.

(* ---- 主件：件 6 组装链无条件化（已证桥输入版；PSTR-先序）             *)
(*   β·KL(pi*‖pi_{t+1}) == (1−η)·β·KL(pi*‖pi_t) − η·gap(pi_t) + β·K2     *)
(*   组装链 = 件 6 五段 β 缩放机器逐段同位复用；零假设位。               *)
Theorem aiu_backward_kl_exact_uncond :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (mult beta
              (KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t)))
        (plus (mult (req_minus one eta)
                    (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
              (plus (opp (mult eta
                              (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))))
                    (mult beta
                          (KLE pi_t (NPX pi_t Hpi_t)
                               Hpi_t (npx_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t Hn.
  pose proof (aiu_bridge_backward_kl_step pi_t Hpi_t Hn) as Hbridge.
  assert (Hgap : req (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
                     (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))
    by exact (aiu_subgap_base pi_t Hpi_t Hn).
  (* β 缩放核 1：β·(I·KSP) == I·(β·KSP)，I := 1−η *)
  assert (Hscale1 : req (mult beta (mult (req_minus one eta)
                                         (KLE PSTR pi_t PSTR_pos Hpi_t)))
                        (mult (req_minus one eta)
                              (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))).
  { apply (req_trans
              (mult beta (mult (req_minus one eta)
                               (KLE PSTR pi_t PSTR_pos Hpi_t)))
              (mult (mult beta (req_minus one eta))
                    (KLE PSTR pi_t PSTR_pos Hpi_t))
              (mult (req_minus one eta)
                    (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))).
    - exact (mult_assoc beta (req_minus one eta)
                        (KLE PSTR pi_t PSTR_pos Hpi_t)).
    - apply (req_trans
                (mult (mult beta (req_minus one eta))
                      (KLE PSTR pi_t PSTR_pos Hpi_t))
                (mult (mult (req_minus one eta) beta)
                      (KLE PSTR pi_t PSTR_pos Hpi_t))
                (mult (req_minus one eta)
                      (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))).
      + exact (req_mult_compat (mult beta (req_minus one eta))
                               (mult (req_minus one eta) beta)
                               (KLE PSTR pi_t PSTR_pos Hpi_t)
                               (KLE PSTR pi_t PSTR_pos Hpi_t)
                               (mult_comm beta (req_minus one eta))
                               (req_refl (KLE PSTR pi_t PSTR_pos Hpi_t))).
      + exact (req_sym (mult (req_minus one eta)
                             (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                       (mult (mult (req_minus one eta) beta)
                             (KLE PSTR pi_t PSTR_pos Hpi_t))
                       (mult_assoc (req_minus one eta) beta
                                   (KLE PSTR pi_t PSTR_pos Hpi_t))). }
  (* β 缩放核 2：β·(η·KTS) == η·(β·KTS) *)
  assert (Hswap2 : req (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                       (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))).
  { apply (req_trans
              (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
              (mult (mult beta eta) (KLE pi_t PSTR Hpi_t PSTR_pos))
              (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))).
    - exact (mult_assoc beta eta (KLE pi_t PSTR Hpi_t PSTR_pos)).
    - apply (req_trans
                (mult (mult beta eta) (KLE pi_t PSTR Hpi_t PSTR_pos))
                (mult (mult eta beta) (KLE pi_t PSTR Hpi_t PSTR_pos))
                (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))).
      + exact (req_mult_compat (mult beta eta) (mult eta beta)
                               (KLE pi_t PSTR Hpi_t PSTR_pos)
                               (KLE pi_t PSTR Hpi_t PSTR_pos)
                               (mult_comm beta eta)
                               (req_refl (KLE pi_t PSTR Hpi_t PSTR_pos))).
      + exact (req_sym (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                       (mult (mult eta beta) (KLE pi_t PSTR Hpi_t PSTR_pos))
                       (mult_assoc eta beta (KLE pi_t PSTR Hpi_t PSTR_pos))). }
  (* β·(opp (η·KTS)) == opp (η·gap(pi_t))：req_opp_mult_l + 核 2 + Hgap 代换 *)
  assert (Hscale2 : req (mult beta (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
                        (opp (mult eta
                                   (req_minus (JJ PSTR PSTR_pos)
                                              (JJ pi_t Hpi_t))))).
  { apply (req_trans
              (mult beta (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
              (opp (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
              (opp (mult eta (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))))).
    - exact (req_opp_mult_l beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))).
    - apply (req_opp_compat
                (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                (mult eta (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t)))).
      exact (req_trans
                (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                (mult eta (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t)))
                Hswap2
                (req_mult_compat eta eta
                   (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos))
                   (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
                   (req_refl eta)
                   (req_sym (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
                            (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos))
                            Hgap))). }
  (* β 分配到后半树：β·(B + C) == β·B + β·C，B 项换形 *)
  assert (Hscale3 : req (mult beta (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                         (KLE pi_t (NPX pi_t Hpi_t)
                                              Hpi_t (npx_pos pi_t Hpi_t))))
                        (plus (opp (mult eta
                                            (req_minus (JJ PSTR PSTR_pos)
                                                       (JJ pi_t Hpi_t))))
                              (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                               Hpi_t (npx_pos pi_t Hpi_t))))).
  { apply (req_trans
              (mult beta (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                               (KLE pi_t (NPX pi_t Hpi_t)
                                    Hpi_t (npx_pos pi_t Hpi_t))))
              (plus (mult beta (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
                    (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                     Hpi_t (npx_pos pi_t Hpi_t))))
              (plus (opp (mult eta
                                 (req_minus (JJ PSTR PSTR_pos)
                                            (JJ pi_t Hpi_t))))
                    (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                     Hpi_t (npx_pos pi_t Hpi_t))))).
    - exact (distrib beta
                     (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                     (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t))).
    - exact (req_plus_compat
                (mult beta (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
                (opp (mult eta
                            (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))))
                (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                 Hpi_t (npx_pos pi_t Hpi_t)))
                (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                 Hpi_t (npx_pos pi_t Hpi_t)))
                Hscale2 (req_refl (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                              Hpi_t (npx_pos pi_t Hpi_t))))). }
  (* 全树 β 分配组装 *)
  assert (Hscale : req
              (mult beta (plus (mult (req_minus one eta)
                                     (KLE PSTR pi_t PSTR_pos Hpi_t))
                               (plus (opp (mult eta
                                                  (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                     (KLE pi_t (NPX pi_t Hpi_t)
                                          Hpi_t (npx_pos pi_t Hpi_t)))))
              (plus (mult (req_minus one eta)
                          (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                    (plus (opp (mult eta
                                       (req_minus (JJ PSTR PSTR_pos)
                                                  (JJ pi_t Hpi_t))))
                          (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                           Hpi_t (npx_pos pi_t Hpi_t)))))).
  { apply (req_trans
              (mult beta (plus (mult (req_minus one eta)
                                     (KLE PSTR pi_t PSTR_pos Hpi_t))
                               (plus (opp (mult eta
                                                  (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                     (KLE pi_t (NPX pi_t Hpi_t)
                                          Hpi_t (npx_pos pi_t Hpi_t)))))
              (plus (mult beta (mult (req_minus one eta)
                                     (KLE PSTR pi_t PSTR_pos Hpi_t)))
                    (mult beta (plus (opp (mult eta
                                                   (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                     (KLE pi_t (NPX pi_t Hpi_t)
                                          Hpi_t (npx_pos pi_t Hpi_t)))))
              (plus (mult (req_minus one eta)
                          (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                    (plus (opp (mult eta
                                       (req_minus (JJ PSTR PSTR_pos)
                                                  (JJ pi_t Hpi_t))))
                          (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                           Hpi_t (npx_pos pi_t Hpi_t)))))).
    - exact (distrib beta
                     (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
                     (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                           (KLE pi_t (NPX pi_t Hpi_t)
                                Hpi_t (npx_pos pi_t Hpi_t)))).
    - exact (req_plus_compat
                (mult beta (mult (req_minus one eta)
                                 (KLE PSTR pi_t PSTR_pos Hpi_t)))
                (mult (req_minus one eta)
                      (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                (mult beta (plus (opp (mult eta
                                               (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                 (KLE pi_t (NPX pi_t Hpi_t)
                                      Hpi_t (npx_pos pi_t Hpi_t))))
                (plus (opp (mult eta
                                       (req_minus (JJ PSTR PSTR_pos)
                                                  (JJ pi_t Hpi_t))))
                      (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                           Hpi_t (npx_pos pi_t Hpi_t))))
                Hscale1 Hscale3). }
  (* 闭合：桥位 β 缩放（req_mult_compat + 已证桥 Hbridge）+ 全树分配 Hscale *)
  exact (req_trans
          (mult beta
                (KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t)))
          (mult beta
                (plus (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
                      (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                            (KLE pi_t (NPX pi_t Hpi_t)
                                 Hpi_t (npx_pos pi_t Hpi_t)))))
          (plus (mult (req_minus one eta)
                      (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                (plus (opp (mult eta
                                   (req_minus (JJ PSTR PSTR_pos)
                                              (JJ pi_t Hpi_t))))
                      (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                           Hpi_t (npx_pos pi_t Hpi_t)))))
          (req_mult_compat beta beta
              (KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t))
              (plus (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
                    (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                          (KLE pi_t (NPX pi_t Hpi_t)
                               Hpi_t (npx_pos pi_t Hpi_t))))
              (req_refl beta) Hbridge)
          Hscale).
Qed.

End AiuBackwardKL.

(* ============================================================ *)
(* 公理面自审（文末三条 Print Assumptions；End 之后）                    *)
(* ============================================================ *)
Print Assumptions aiu_subgap_base.
Print Assumptions aiu_bridge_backward_kl_step.
Print Assumptions aiu_backward_kl_exact_uncond.
