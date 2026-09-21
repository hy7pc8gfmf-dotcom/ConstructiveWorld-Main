(* ============================================================ *)
(* ToyR 玩具证替换件 —— T261 台账席 战役包V（tier2 十二批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   aiu_bridge_backward_kl_step（原 L138，2 句玩具证）                   *)
(*   aiu_subgap_base（原 L126，2 句玩具证）                               *)
(* ============================================================ *)

(* ============================================================ *)
(* AlignIdUnclosed.v —— UpAlignIdReq 件 6 无条件化组装席                *)
(*   （席位CWD，批次 E-STAGING-CWD，2026-09-14）                       *)
(*                                                              *)
(* 立项：只读树 UpAlignIdReq.v:325 起旗舰条件恒等式（件 6，              *)
(*   policy_gap_backward_kl_exact——后向 KL 递推换轴精确恒等式，          *)
(*   前提位显式携带「三 KL 精确恒等」）。该前提内容已被 req 同位定理化：  *)
(*   UpReqAlign3.v:3153 req2_backward_kl_step（20260909 收官席五段       *)
(*   组装，全链 Qed 真证）。本席把已证桥喂入件 6 的组装链，产出           *)
(*   无条件推论定理（除接口参数外零假设位，aiu_ 前缀防撞 grep 零命中）。  *)
(*                                                              *)
(* 同位对账表（原 Hypothesis 前提 → 喂入的已证定理）：                  *)
(*   ┌────────────────────────┬──────────────────────────┬              *)
(*   │ 原前提位               │ 原语句（LHS 载体序）      │              *)
(*   ├────────────────────────┼──────────────────────────┤              *)
(*   │ ① UpReqAlign.v:434     │ req (relative_entropy_req│              *)
(*   │   Hypothesis           │   pi_star_req (pi_next…))│              *)
(*   │   req_backward_kl_     │   (RHS)——pi_star-先序    │              *)
(*   │   identity（批3挂账）  │                          │              *)
(*   │ ② UpAlignIdReq.v:331   │ req (KLE (NPX …) PSTR …) │              *)
(*   │   件 6 显式前提位      │   (RHS)——NPX-先序        │              *)
(*   └────────────────────────┴──────────────────────────┘              *)
(*   喂入的已证定理：req2_backward_kl_step（UpReqAlign3.Req3AlignCore，  *)
(*   LHS = req (KLE PSTR (NPX …) …) (RHS)——PSTR-先序）。                *)
(*   对账判定：                                                         *)
(*   ① 与已证桥同位 ✓——req2_rel_ent p q := Σ p·(log p − log q)          *)
(*     = KL(p‖q)，pi_star-先序即 KL(pi*‖pi_{t+1})，与 Id 原件            *)
(*     S05_AlignmentGRPO.v:3967 policy_iter_backward_kl_step 同位。      *)
(*   ② 参序倒置 ✗（本席新发现，机器语句面勘验）：件 6 前提位与结论位      *)
(*     LHS 均为 NPX-先序（KL(pi_{t+1}‖pi★)），与 Id 原件/批 3 挂账位/     *)
(*     已证桥三方全部反向，且与件 6 自身头注「β·KL(pi*‖pi_{t+1})」        *)
(*     不符——属件 6 语句面 KLE 参序错位，其前提位不可由已证桥喂入        *)
(*     （KL 无对称引理，构造性下两向不可互推）。本席无条件件按已证桥      *)
(*     PSTR-先序（即件 6 头注与 Id 原件的意图序）交付：组装链五段         *)
(*     β 缩放机器（Hscale1/Hswap2/Hscale2/Hscale3/Hscale）逐段同位       *)
(*     复用，桥位与 gap 代换位分别由已证定理喂入：                       *)
(*       桥位 ← req2_backward_kl_step（经 aiu_bridge_backward_kl_step）； *)
(*       gap 位 ← UpAlignIdReq.w_subgap_base（经 aiu_subgap_base）。      *)
(*                                                              *)
(* 节参数：与 UpReqAlign3.Req3AlignCore 已证桥的 discharge 签名逐位对齐  *)
(*   （探针 Check 定谳）：S + sumf 六假设 + reward/beta 簇 + eta +       *)
(*   ZAL_pos（Req3AlignCore 的 pi_ref_norm/eta_le_one 未进              *)
(*   req2_backward_kl_step 的 discharge 集，本席节内不设）。别名簇       *)
(*   （pos3/nrm/KLE/JJ/NPX/npx_pos/ZAL/PSTR/PSTR_pos）为上游 req2        *)
(*   定义的 δ 透明薄包装，与 UpAlignIdReq.Part 2 同式（同名遮蔽为        *)
(*   库内既有惯例，UpAlignIdReq 对 UpReqAlign3 同款先例）。              *)
(*                                                              *)
(* 红线自检口径：                                                      *)
(*   —— 禁词全零（按全文件计含头注）；                                  *)
(*   —— 全件 Qed 真证，term-mode 显式组装（req 系无 destruct，全链       *)
(*      req_trans/compat 族），非平凡收口（五段 β 缩放机器复用 +          *)
(*      双喂入点），无 trivial/reflexivity 降级；                        *)
(*   —— 语句全 Set 层：req/lt/le 均 Set 值，前提位仅接口参数              *)
(*      （pos3/nrm 为 Set 别名），零 Prop 泄露、零 -> False；            *)
(*   —— 提取探针 Obj.magic=0（独立小探针，验后删）；                    *)
(*   —— Print Assumptions 全件 Closed（文末三连打，证据在编译日志）。    *)
(* 编译配方：cpu_guard 包装零裸调：rocq c -Q . "" AlignIdUnclosed.v     *)
(* ============================================================ *)

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

(* ---- 喂入件 1：gap 代换位（UpAlignIdReq.w_subgap_base @ 全参消费）    *)
(*   req_minus (J(pi★) − J(p)) == β·KL(p‖pi★)——件 6 组装链的 Hgap 位。   *)
Lemma aiu_subgap_base : forall (p : S -> R) (Hp : pos3 p) (Hn : nrm p),
  req (req_minus (JJ PSTR PSTR_pos) (JJ p Hp))
      (mult beta (KLE p PSTR Hp PSTR_pos)).
Proof.
  intros p Hp Hn.
  exact (@UpAlignIdReq.w_subgap_base R RIS S sumf sum_ext sum_add sum_linear           log_req_compat log_inv_exp_neg_req           reward beta beta_pos pi_ref pi_ref_pos ZAL_pos p Hp Hn).
Qed.

(* ---- 喂入件 2：三 KL 精确恒等桥位（UpReqAlign3.req2_backward_kl_step  *)
(*   @ 全参消费）——件 6 原显式前提位的已证定理供给（PSTR-先序）。        *)
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

(* ---- 主件：件 6 组装链无条件化（已证桥喂入版；PSTR-先序）             *)
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
  (* 收口：桥位 β 缩放（req_mult_compat + 已证桥 Hbridge）+ 全树分配 Hscale *)
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
(* 四关证据（文末三连打；End 之后——E207 卡口径）                        *)
(* ============================================================ *)
Print Assumptions aiu_subgap_base.
Print Assumptions aiu_bridge_backward_kl_step.
Print Assumptions aiu_backward_kl_exact_uncond.
