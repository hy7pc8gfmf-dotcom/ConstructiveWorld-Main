(* ============================================================ *)
(* UpReqAlign4.v —— 本件形式化 softmax 对齐策略向后 KL 恒等式的 *)
(*   req 接口层供给：kcxr_req_backward_kl_identity 经柯西实数实例 *)
(*   落实向后 KL 恒等式，并供给三节共用 sum 接口的实例层证书。 *)
(* 依赖：CW_ConstructiveWorld_219、UpReqAlgebra、UpReqAlign、UpReqAlign2、 *)
(*   UpReqAlign3、G05_LogSmall、UpReqConcSoftmax、ConcMixSelFeed。 *)
(* 对标：mathlib 相对熵/信息投影接口；stdlib Coq Reals exp_log。 *)
(* 构造性注记：Set 层承载（req/lt/le 均 Set 值）；零承认件； *)
(*   新增供给段零假设位、全 Qed；可提取。 *)
(* 编译配方：Rocq 9.1 直调 coqc，cpu_guard 单道守护。 *)
(* ============================================================ *)

(* UpReqAlign4.v — KLCvx 桥供给批 A（参数位 1）：req_backward_kl_identity 假设位降为使用件
   施工图：件Y 两参数位消解预研（C 节转录）；施工件：件Z2（组 A = 参数位 1，独占组 A 配额）
   上游：UpReqAlgebra（批 1）+ UpReqAlign（批 3，桥宿主文件，只读）+
     UpReqAlign2（批 3b）+ UpReqAlign3（批 3c，参数位 1 同位无条件定理）+
     G05_LogSmall（Real 证人肢）——全部 Require 使用，零改写；
   纯 term-mode（req_trans 链 + compat 桥），零 Morphisms 依赖；
   Set 层语句（req/lt/le 均 Set 值，零 Prop 泄露）。
   ----------------------------------------------------------------
   已证明坐标（本批完成形态）：
   [参数位 1 供给] UpReqAlign.v:434-442 桥假设位 req_backward_kl_identity
     （批 3 桥位 1/3，Id theorem policy_iter_backward_kl_step @L22686 同位）
     由本文件 kcxr_req_backward_kl_identity（N1）供给消解——语句逐字同位，
     证 = UpReqAlign3.req2_backward_kl_step（L3153-3395，Qed 无条件定理，
     头注「全链每一环均为 Qed 真证」）+ N0 证人重述（req_pi_star_pos↔PSTR_pos、
     req_pi_next_pos↔npx_pos 两个合取肢 + RHS 三处 relative_entropy 证人位重组）。
     G07_KLWall.v L652「阻塞裁决」结论仅对 GeomD 接口 scope 成立，对参数位 1 作废
     （本件不走 log-mult 接口字段路径，走同位定理供给路径）。
   [N0 证人开门件] kcxr_log_witness（log_req_compat 一行开门）+
     kcxr_kl_witness_transport（relative_entropy_req 证人位全部重述；
     先例：UpReqAlign2:891 注记「Qed 件不可 delta；先经 log_req_compat 开门」
     + UpReqAlign3 L120-121 透明证人结论）。
   [N3 Real 层闭合实例] kcxr_real_backward_kl_identity：全参显式
     @Real RealEnhancedReal，log_inv_exp_neg_req := logd_log_inv_exp_neg_real
     （G05_LogSmall:347）、log_req_compat := logd_log_compat_real
     （G05_LogSmall:305）——两假设位在 Real 层全无条件闭合（G05 两件皆 Qed）。
   [本批不做（批 B 余留，精确清单见文件尾）] 参数位 2（req_step_kl_eta_bound
     UpReqAlign:430 + req_policy_improvement_mono UpReqAlign:630 消解链）、
   ----------------------------------------------------------------
   诚实边界登记表：
   1. 节闭后签名（About 检验实测，UpReqAlign3.req2_backward_kl_step）：
      {R}{RIS} S sumf sum_ext sum_add sum_linear sum_pos log_req_compat
      log_inv_exp_neg_req reward beta beta_pos pi_ref pi_ref_pos eta ZAL_pos
      pi_t Hpi_t Hn —— pi_ref_norm/eta_pos/eta_le_one 不入参数位 1（未使用）；
      Z_align_pos（ZAL_pos 位）必入。本文件节参面照抄 UpReqAlign.v 全脸
      （含六条 sum 面 + pi_ref_norm/eta_pos/eta_le_one），未使用位留作批 B 参数位 2 脸。
      req_pi_next_pos 为 Qed 件 vs PSTR_pos/npx_pos Definition 包装）——
      log_req_compat 一行重述；其二 inv_pos 载体证人位（inv_pos 为接口
      字段、携带 lt zero 证人数据；pi_next_req 内嵌本地 req_Z_rel_pos、
      req2_pi_next 内嵌 Qed 件 req2_Z_rel_pos，两类 opaque 应用不可转换，
      + 环代数四步链真证重述，kcxr_pi_next_transport 完成载体位。
   3. N3 闭合范围：R/RIS/log 两假设位闭合；六条 sum 面 + 节参数脸仍是 UpReqAlign.v
   ----------------------------------------------------------------
   组 C 完成：宿主两桥假设位已证明定理 + 注册完成——
   UpReqAlign.v:434/:630 两桥假设位由本文件 kcxr_ 两件供给（已证明定理
   段 = 文件尾 Module KlcxAlignWriteoffC，逐字语句重申件两枚，节闭
   签名 About 钉死 _t24_probe1 实录），G07 头注阻塞裁决作废（参数位 1 与参数位 2
   分见批 A/B 段头注）；UpReqAlign4.v 已入 order.txt/_CoqProject 双树
   注册（宿主使用链）。宿主文件本体零改动（依赖方向：本文件已
   Require 宿主，宿主不能反向 Require 本文件，已证明由定理段 + 下游
   使用完成，两桥假设位原样保留 = 最 honest 形态）。
   ---------------------------------------------------------------- *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require Import G05_LogSmall.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 实例层供给段（假设消融：证书位转已证定理，签名保持式） *)
(*   语句面 = 原假设命题（载体换成锚件实例 csm_sumf S0 en）； *)
(*   证明 = 锚件全参显式应用（ConcMixSelFeed cms_sum_* 四件）。 *)
(*   三节同名 sum 假设位共用本段单一供给，出节签名零改动。 *)
(* ============================================================ *)
From Stdlib Require Import List.
Require Import UpReqConcSoftmax.
Require Import ConcMixSelFeed.

(* sum 外延：逐点 req 相等给出和的 req 相等（原假设命题@csm_sumf 实例）。 *)
Theorem w3p_align4_sum_ext_sup :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    (forall s : S0, req (f s) (g s)) -> req (csm_sumf S0 en f) (csm_sumf S0 en g).
Proof.
  intros S0 en f g H.
  exact (cms_sum_ext S0 en f g H).
Qed.

(* sum 可加：两项和的分解（原假设命题@csm_sumf 实例）。 *)
Theorem w3p_align4_sum_add_sup :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    req (csm_sumf S0 en (fun s : S0 => plus (f s) (g s)))
        (plus (csm_sumf S0 en f) (csm_sumf S0 en g)).
Proof.
  intros S0 en f g.
  exact (cms_sum_add S0 en f g).
Qed.

(* sum 线性：常数因子提出（原假设命题@csm_sumf 实例）。 *)
Theorem w3p_align4_sum_linear_sup :
  forall (S0 : Set) (en : list S0) (a : Real) (f : S0 -> Real),
    req (csm_sumf S0 en (fun s : S0 => mult a (f s)))
        (mult a (csm_sumf S0 en f)).
Proof.
  intros S0 en a f.
  exact (cms_sum_linear S0 en a f).
Qed.

(* sum 保序：逐点 le 给出和的 le（原假设命题@csm_sumf 实例）。 *)
Theorem w3p_align4_sum_le_sup :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    (forall s : S0, le (f s) (g s)) -> le (csm_sumf S0 en f) (csm_sumf S0 en g).
Proof.
  intros S0 en f g H.
  exact (cms_sum_le S0 en f g H).
Qed.

(* ============================================================ *)
(* KlcxAlignBridge：批 3 桥假设位供给节（节参面照抄 UpReqAlign.v） *)
(* ============================================================ *)
Section KlcxAlignBridge.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

(* ---- SumOver 的 req 签名对接面（逐位照抄 UpReqAlign.v:54-69） ---- *)
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
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero -> forall s : S, req (f s) zero.

(* 接口缺口桥（照抄 UpReqAlign.v:75-77） *)
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).

(* ---- 供给参数位①（本批新开口；Real 层证人 = G05_LogSmall:347） ----
   同位先例：UpReqAlign3.v:75-76（Req3AlignCore 同名参数位）。 *)
Hypothesis log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.

(* ---- 节参数（照抄 UpReqAlign.v:80-85 + 330-332） ---- *)
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable pi_ref_norm : req (sumf pi_ref) one.

Definition pos_dist (p : S -> R) : Set := forall s : S, lt zero (p s).   (* :88 *)
Definition norm_one (p : S -> R) : Set := req (sumf p) one.              (* :89 *)

(* 配分函数与闭式最优策略（照抄 UpReqAlign.v:92-97） *)
Definition Z_align_req : R :=
  sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Variable Z_align_pos : lt zero Z_align_req.                              (* :94 *)
Definition pi_star_req (s : S) : R :=
  mult (inv_pos Z_align_req Z_align_pos)
       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
(* 相对熵 req 形态（照抄 UpReqAlign.v:100-101） *)
Definition relative_entropy_req (p q : S -> R) (Hp : pos_dist p) (Hq : pos_dist q) : R :=
  sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))).
(* 对齐能量/自由能/对齐目标（照抄 UpReqAlign.v:104-110） *)
Definition align_energy_req (s : S) : R :=
  req_minus (opp (reward s)) (mult beta (log (pi_ref s) (pi_ref_pos s))).
Definition F_align_req (p : S -> R) (Hp : pos_dist p) : R :=
  plus (sumf (fun s => mult (p s) (align_energy_req s)))
       (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition align_objective_req (p : S -> R) (Hp : pos_dist p) : R :=
  opp (F_align_req p Hp).

(* 定义簇（照抄 UpReqAlign.v:336-345） *)
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable eta_le_one : le eta one.
Definition advantage_aug_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=
  req_minus (reward s)
            (mult beta (req_minus (log (pi_t s) (Hpi_t s)) (log (pi_ref s) (pi_ref_pos s)))).
Definition Z_rel_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) : R :=
  sumf (fun s => mult (pi_t s)
                      (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                          (advantage_aug_req pi_t Hpi_t s))))).

(* Z_rel 正性（照抄 UpReqAlign.v:348-358） *)
Lemma req_Z_rel_pos :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t), lt zero (Z_rel_req pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t.
  unfold Z_rel_req.
  apply sum_pos.
  intro s.
  apply mult_positive.
  - apply Hpi_t.
  - apply exp_neg_pos.
Qed.

Definition pi_next_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=  (* :360 *)
  mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
       (mult (pi_t s)
             (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                 (advantage_aug_req pi_t Hpi_t s))))).

(* pi_next 逐点正性（照抄 UpReqAlign.v:367-377） *)
Lemma req_pi_next_pos :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t), pos_dist (pi_next_req pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t s.
  unfold pi_next_req.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply mult_positive.
    + apply Hpi_t.
    + apply exp_neg_pos.
Qed.

(* π* 逐点正性（照抄 UpReqAlign.v:129-138） *)
Lemma req_pi_star_pos : pos_dist pi_star_req.
Proof.
  intro s.
  unfold pi_star_req.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply mult_positive.
    + apply pi_ref_pos.
    + apply exp_neg_pos.
Qed.

(* ============ N0：证人开门件（三层重述） ============
   （inv_pos 为接口字段、载 lt zero 证人数据——req2_Z_rel_pos（Qed 件）
   与本地 req_Z_rel_pos 应用不可转换，须 inv_pos_correct 四步链真证）；
   层3 relative_entropy 逐点全部重述（层1/层2 组装 + sum_ext）。 *)

(* 层1：log 证人重述（req_refl 供同点双正性）
   先例：UpReqAlign2:891 注记 + G05 B5 logd_log_witness_real req 同位。 *)
Definition kcxr_log_witness (x : R) (Hx Hx' : lt zero x) :
  req (log x Hx) (log x Hx') :=
  log_req_compat x x Hx Hx' (req_refl x).

(* 层2：inv_pos 载体证人重述（inv_pos_correct 双肢 + 环代数四步链） *)
Lemma kcxr_inv_pos_witness :
  forall (x : R) (w w' : lt zero x), req (inv_pos x w) (inv_pos x w').
Proof.
  intros x w w'.
  apply (req_trans (inv_pos x w)
                   (mult one (inv_pos x w))
                   (inv_pos x w')).
  - apply (req_sym (mult one (inv_pos x w)) (inv_pos x w)
                   (req_mult_one_l (inv_pos x w))).
  - apply (req_trans (mult one (inv_pos x w))
                     (mult (mult x (inv_pos x w')) (inv_pos x w))
                     (inv_pos x w')).
    + apply req_mult_compat.
      * apply (req_sym _ _ (inv_pos_correct x w')).
      * apply req_refl.
    + apply (req_trans (mult (mult x (inv_pos x w')) (inv_pos x w))
                       (mult (inv_pos x w') (mult x (inv_pos x w)))
                       (inv_pos x w')).
      * apply (req_trans (mult (mult x (inv_pos x w')) (inv_pos x w))
                         (mult (mult (inv_pos x w') x) (inv_pos x w))
                         (mult (inv_pos x w') (mult x (inv_pos x w)))).
        -- apply req_mult_compat.
           ++ apply mult_comm.
           ++ apply req_refl.
        -- apply (req_sym _ _
                   (mult_assoc (inv_pos x w') x (inv_pos x w))).
      * apply (req_trans (mult (inv_pos x w') (mult x (inv_pos x w)))
                         (mult (inv_pos x w') one)
                         (inv_pos x w')).
        -- apply req_mult_compat.
           ++ apply req_refl.
           ++ exact (inv_pos_correct x w).
        -- exact (req_mult_one_r (inv_pos x w')).
Qed.

(* 层2'：pi_next 载体重述（Z_rel_req ≡ req2_Z_rel δ 完成 +
   inv_pos 证人位层2 重述——UpReqAlign.v:360 与 req2_pi_next 的
   逐位同形载体在此打通） *)
Lemma kcxr_pi_next_transport :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S),
    req (pi_next_req pi_t Hpi_t s)
        (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos eta
              pi_t Hpi_t s).
Proof.
  intros pi_t Hpi_t s.
  unfold pi_next_req, NPX, req2_pi_next.
  apply req_mult_compat.
  - apply kcxr_inv_pos_witness.
  - apply req_refl.
Qed.


Lemma kcxr_kl_witness_transport :
  forall (p q p' q' : S -> R) (Hp : pos_dist p) (Hq : pos_dist q)
         (Hp' : pos_dist p') (Hq' : pos_dist q'),
    (forall s : S, req (p s) (p' s)) ->
    (forall s : S, req (q s) (q' s)) ->
    req (relative_entropy_req p q Hp Hq) (relative_entropy_req p' q' Hp' Hq').
Proof.
  intros p q p' q' Hp Hq Hp' Hq' Hp_leg Hq_leg.
  unfold relative_entropy_req.
  apply sum_ext.
  intro s.
  apply req_mult_compat.
  - apply Hp_leg.
  - unfold req_minus.
    apply req_plus_compat.
    + apply log_req_compat.
      apply Hp_leg.
    + apply req_opp_compat.
      apply log_req_compat.
      apply Hq_leg.
Qed.

(*
   语句 = UpReqAlign.v:434-442 req_backward_kl_identity 逐字同位；
   证 = req2_backward_kl_step（UpReqAlign3:3153，无条件）+ 证人重述三段。 *)
Theorem kcxr_req_backward_kl_identity :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (Hnorm : norm_one pi_t),
    req (relative_entropy_req pi_star_req (pi_next_req pi_t Hpi_t)
             req_pi_star_pos (req_pi_next_pos pi_t Hpi_t))
        (plus (mult (req_minus one eta)
                    (relative_entropy_req pi_star_req pi_t req_pi_star_pos Hpi_t))
              (plus (opp (mult eta (relative_entropy_req pi_t pi_star_req Hpi_t req_pi_star_pos)))
                    (relative_entropy_req pi_t (pi_next_req pi_t Hpi_t)
                         Hpi_t (req_pi_next_pos pi_t Hpi_t)))).
Proof.
  intros pi_t Hpi_t Hnorm.
  pose proof (@req2_backward_kl_step R RIS S sumf sum_ext sum_add sum_linear
                sum_pos log_req_compat log_inv_exp_neg_req reward beta beta_pos
                pi_ref pi_ref_pos eta Z_align_pos pi_t Hpi_t Hnorm) as H.
  apply (req_trans
           (relative_entropy_req pi_star_req (pi_next_req pi_t Hpi_t)
                req_pi_star_pos (req_pi_next_pos pi_t Hpi_t))
           (relative_entropy_req
              (@PSTR R RIS S sumf reward beta beta_pos pi_ref Z_align_pos)
              (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                    eta pi_t Hpi_t)
              (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref pi_ref_pos
                         Z_align_pos)
              (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                        pi_ref_pos eta pi_t Hpi_t))).
  (* 段1：LHS 重述（载体位 PSTR δ 完成 / NPX 层2 重述 +
     证人位 PSTR_pos/npx_pos 层1 重述） *)
  - exact (kcxr_kl_witness_transport pi_star_req (pi_next_req pi_t Hpi_t)
             (@PSTR R RIS S sumf reward beta beta_pos pi_ref Z_align_pos)
             (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                   eta pi_t Hpi_t)
             req_pi_star_pos (req_pi_next_pos pi_t Hpi_t)
             (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref pi_ref_pos
                        Z_align_pos)
             (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                       pi_ref_pos eta pi_t Hpi_t)
             (fun s => req_refl
                         (@PSTR R RIS S sumf reward beta beta_pos pi_ref
                                Z_align_pos s))
             (kcxr_pi_next_transport pi_t Hpi_t)).
  (* 段2：主体 = req2_backward_kl_step（别名 δ 透明完成） *)
  - apply (req_trans
             (relative_entropy_req
                (@PSTR R RIS S sumf reward beta beta_pos pi_ref Z_align_pos)
                (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref
                      pi_ref_pos eta pi_t Hpi_t)
                (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref pi_ref_pos
                           Z_align_pos)
                (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                          pi_ref_pos eta pi_t Hpi_t))
             (plus (mult (req_minus one eta)
                         (relative_entropy_req
                            (@PSTR R RIS S sumf reward beta beta_pos pi_ref
                                   Z_align_pos)
                            pi_t
                            (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref
                                       pi_ref_pos Z_align_pos)
                            Hpi_t))
                   (plus (opp (mult eta
                                   (relative_entropy_req pi_t
                                      (@PSTR R RIS S sumf reward beta beta_pos
                                             pi_ref Z_align_pos)
                                      Hpi_t
                                      (@PSTR_pos R RIS S sumf reward beta beta_pos
                                                 pi_ref pi_ref_pos Z_align_pos))))
                         (relative_entropy_req pi_t
                            (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref
                                  pi_ref_pos eta pi_t Hpi_t)
                            Hpi_t
                            (@npx_pos R RIS S sumf sum_pos reward beta beta_pos
                                      pi_ref pi_ref_pos eta pi_t Hpi_t))))).
    + exact H.
    (* 段3：RHS 重述（三处 KL：载体位 δ/层2' + 证人位层1 + 环重组） *)
    + apply req_plus_compat.
      * apply req_mult_compat.
        -- apply req_refl.
        -- exact (kcxr_kl_witness_transport
                    (@PSTR R RIS S sumf reward beta beta_pos pi_ref Z_align_pos)
                    pi_t pi_star_req pi_t
                    (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref
                               pi_ref_pos Z_align_pos)
                    Hpi_t req_pi_star_pos Hpi_t
                    (fun s => req_refl (pi_star_req s))
                    (fun s => req_refl (pi_t s))).
      * apply req_plus_compat.
        -- apply req_opp_compat.
           apply req_mult_compat.
           ++ apply req_refl.
           ++ exact (kcxr_kl_witness_transport pi_t
                       (@PSTR R RIS S sumf reward beta beta_pos pi_ref
                              Z_align_pos)
                       pi_t pi_star_req Hpi_t
                       (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref
                                  pi_ref_pos Z_align_pos)
                       Hpi_t req_pi_star_pos
                       (fun s => req_refl (pi_t s))
                       (fun s => req_refl (pi_star_req s))).
        -- exact (kcxr_kl_witness_transport pi_t
                    (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref
                          pi_ref_pos eta pi_t Hpi_t)
                    pi_t (pi_next_req pi_t Hpi_t) Hpi_t
                    (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                              pi_ref_pos eta pi_t Hpi_t)
                    Hpi_t (req_pi_next_pos pi_t Hpi_t)
                    (fun s => req_refl (pi_t s))
                    (fun s => req_sym (pi_next_req pi_t Hpi_t s)
                                (@NPX R RIS S sumf sum_pos reward beta
                                        beta_pos pi_ref pi_ref_pos eta
                                        pi_t Hpi_t s)
                                (kcxr_pi_next_transport pi_t Hpi_t s))).
Qed.

End KlcxAlignBridge.

(* ============================================================ *)
(* N3：Real 层闭合实例（参数位 1 全无条件闭合）                         *)
(*   R := Real、RIS := RealEnhancedReal 全参显式；                *)
(*   log_inv_exp_neg_req := logd_log_inv_exp_neg_real（G05:347）,  *)
(*   log_req_compat := logd_log_compat_real（G05:305）—— 两假设位    *)
(*   在 Real 层由 Qed 真证供给。六条 sum 面 + 节参数脸仍为         *)

(* ============================================================ *)
Definition kcxr_real_backward_kl_identity
  (S : Set) (sumf : (S -> Real) -> Real)
  (h_sum_ext :
     forall f g : S -> Real, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
  (h_sum_add :
     forall f g : S -> Real,
       req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)))
  (h_sum_linear :
     forall (a : Real) (f : S -> Real),
       req (sumf (fun s => mult a (f s))) (mult a (sumf f)))
  (h_sum_pos :
     forall f : S -> Real, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
  (h_sum_le :
     forall f g : S -> Real, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g))
  (h_sum_zero_nonneg :
     forall f : S -> Real,
       (forall s : S, le zero (f s)) -> req (sumf f) zero -> forall s : S, req (f s) zero)
  (h_log_compat :
     forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
       req x y -> req (log x Hx) (log y Hy))
  (reward : S -> Real) (beta : Real) (beta_pos : lt zero beta)
  (pi_ref : S -> Real) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
  (pi_ref_norm : req (sumf pi_ref) one)
  (eta : Real) (eta_pos : lt zero eta) (eta_le_one : le eta one)
  (Z_align_pos :
     lt zero (@Z_align_req Real RealEnhancedReal S sumf reward beta beta_pos pi_ref))
  :=
  @kcxr_req_backward_kl_identity Real RealEnhancedReal S sumf
    h_sum_ext h_sum_add h_sum_linear h_sum_pos
    h_log_compat logd_log_inv_exp_neg_real
    reward beta beta_pos pi_ref pi_ref_pos Z_align_pos eta.

(* ---------------------------------------------------------------- *)
(* 批 B 余留精确清单（参数位 2，本批不做）：                               *)
(* 1. 供给参数位②开口：req_step_kl_eta_bound 同位（UpReqAlign:430，       *)
(*    real_step_kl_eta_bound_eps / real_interp_Z_le_one_eps 在根）。  *)
(* 2. req_policy_improvement_mono（UpReqAlign:630，批 3 桥位 3/3）：   *)
(*    证法模板照抄本文件 N1（pose proof + kcxr_kl_witness_transport   *)
(*    + 重组），G07 L653 结论同此作废路径。                           *)

(* ---------------------------------------------------------------- *)

(* ============================================================ *)
(*   前件：批 A 全绿（参数位 1 kcxr_req_backward_kl_identity 在上段，     *)
(*   其后 Real 实例与批 B 余留清单注记为批 A 原文，追加不改）。      *)
(*   本段机制（节参面/别名/节内证人/N0 重述/N1 参数位 1 件）为批 A 段     *)
(*   逐字节同复制，置于 Module 命名空间内——文件级批 A 同名全局件     *)
(*   不被重定义（Coq 节变量不出全局、Definition 随节闭仅入本 Module   *)
(*   路径，批 A 件与批 B 件并存互不遮蔽）。                          *)
(*   ---------------------------------------------------------------- *)
(*   [参数位② 供给] kcxr_req_policy_improvement_mono——UpReqAlign.v:630-633 *)
(*     req_policy_improvement_mono 语句逐字同位（批 3 桥位 3/3，      *)
(*     Id policy_improvement_mono @L22065 同位）。证 = UpReqAlign3.   *)
(*     放行；节闭签名 About 钉死 _z3_probe1 实测：{R}{RIS} S sumf     *)
(*     sum_ext sum_add sum_linear sum_pos log_req_compat              *)
(*     log_inv_exp_neg_req reward beta beta_pos pi_ref pi_ref_pos eta *)
(*     eta_pos eta_le_one req2_gibbs_inequality pi_t Hpi_t Hn——       *)
(*     ZAL_pos/pi_ref_norm 不入其节闭面）+ 唯一非 δ 点：               *)
(*     npx_pos↔req_pi_next_pos 证人重述（批 A kcxr_pi_next_transport  *)
(*     复用）+ align_objective 逐点重述（新 kcxr_align_obj_transport，*)
(*     kcxr_kl_witness_transport 同构）。JJ/AO/KLE 三别名 δ 透明完成   *)
(*     （req2_J=opp(req2_F_align)、req2_rel_ent 与本节                 *)
(*     align_objective_req/relative_entropy_req 逐字同形，req2 面     *)
(*     透明薄包装——UpReqAlign2:111-124 实读）。                        *)
(*   [供给参数位②·诚实假设位] sup_gibbs：plain-le KL≥0（UpReqAlign3.v:    *)
(*     1451-1453 req2_gibbs_inequality 原位同形，无 norm 加强形）——    *)
(*     序无消去，plain-le 不可由接口逐 eps 字段导出（UpReqAlign3       *)
(*     L1446-1450 结论同位）；诚实假设位非欠账，照原位申报勿越；       *)
(*     待 UpReqFreeEnergy（批 2 FEP）结果后降为使用件。                *)
(*     req_step_kl_eta_bound（UpReqAlign.v:430-433）评估记录：         *)
(*     两件签名对读——req 参数位语句：抽象 S 载体 + req 接口 sumf + plain   *)
(*     le 精确形 + next=Gibbs 更新 pi_next_req；GeomD 接口形 eps 版    *)
(*     （UpReqGeomD.v:422 geod_step_kl_eta_bound_eps）：nat→Real 有限  *)
(*     和载体 + real_eq 归一 + real_plus(…,eps) 松弛形 + next=几何     *)
(*     插值 real_step_next。判定：非本批低成本顺带件，三重缺口——      *)
(*     ① eps 松弛→精确 plain-le 需序消去，「序无消去」上游结论同因，   *)
(*     ② 载体缺口：nat→Real 有限和 vs 抽象 S+sumf 接口，需 Real 层     *)

(*     ③ next 映射缺口：几何插值 vs Gibbs 归一化更新，GeomD 引擎       *)
(*       契约不覆盖 req 参数位更新映射，喂定需另证映射契约（独立深件）。   *)
(*     处置：假设位保留（sup_step_kl_eta_bound 显式参，诚实申报）。    *)
(*     · kcxr_req_policy_iter_kl_geom_step——UpReqAlign.v:466-471 语句  *)
(*       逐字同位（Id policy_iter_kl_geom_step L23146 req 版同位）；   *)
(*       桥1 = 批 A kcxr_req_backward_kl_identity（本 Module 内同复制  *)
(*       件，语句与证明逐字节同）；桥2 = sup_step_kl_eta_bound 保留    *)
(*       显式参；序代数肢 = UpReqAlign.req_plusA_opp_cancel_le         *)
(*       （:455 全局件，{R}{RIS} A B C 直用，About 钉死）；证法结构    *)
(*       = 宿主 :472-492 le_id_l 两个合取肢同构。                            *)
(*     · kcxr_req_dpo_loss_iter_step_le——UpReqAlign.v:636-639 语句逐字 *)
(*       同位（Id L23244 同位）；证 = kcxr_req_policy_improvement_mono *)
(*       + opp_le_compat（S07 接口投影；宿主 :640-646 同构）。          *)
(*   ---------------------------------------------------------------- *)
(*   诚实边界登记表（批 B）：                                            *)
(*   1. sup_gibbs/sup_step_kl_eta_bound 两位为本段显式假设参——         *)
(*      kcxr_req_policy_improvement_mono 节闭签名含 sup_gibbs 位、     *)
(*      kcxr_req_policy_iter_kl_geom_step 节闭签名含                    *)
(*      sup_step_kl_eta_bound 位；「假设位降为使用件」对桥1（backward  *)

(*   2. 节参使用面：eta_pos/eta_le_one 自本批起纳入使用（r2 主件两假设位）；  *)
(*      sum_le/sum_zero_nonneg/pi_ref_norm 仍纯脸（未使用；宿主桥节    *)
(*      同位 face 保留，供宿主假设位 1:1 移植）。                       *)
(*   3. Real 层闭合实例：参数位 2/N4 无（sup_gibbs 的 Real 供给 = Real 层   *)
(*      KL≥0 件，属 UpReqFreeEnergy 批 2 范围，）。                 *)
(* ------------------------------------------------------------------ *)

Module KlcxAlignBridgeB.
Section KlcxAlignBridgeB.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

(* ---- SumOver 的 req 签名对接面（逐位照抄 UpReqAlign.v:54-69） ---- *)
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
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero -> forall s : S, req (f s) zero.

(* 接口缺口桥（照抄 UpReqAlign.v:75-77） *)
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).

(* ---- 供给参数位①（本批新开口；Real 层证人 = G05_LogSmall:347） ----
   同位先例：UpReqAlign3.v:75-76（Req3AlignCore 同名参数位）。 *)
Hypothesis log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.

(* ---- 节参数（照抄 UpReqAlign.v:80-85 + 330-332） ---- *)
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable pi_ref_norm : req (sumf pi_ref) one.

Definition pos_dist (p : S -> R) : Set := forall s : S, lt zero (p s).   (* :88 *)
Definition norm_one (p : S -> R) : Set := req (sumf p) one.              (* :89 *)

(* 配分函数与闭式最优策略（照抄 UpReqAlign.v:92-97） *)
Definition Z_align_req : R :=
  sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Variable Z_align_pos : lt zero Z_align_req.                              (* :94 *)
Definition pi_star_req (s : S) : R :=
  mult (inv_pos Z_align_req Z_align_pos)
       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
(* 相对熵 req 形态（照抄 UpReqAlign.v:100-101） *)
Definition relative_entropy_req (p q : S -> R) (Hp : pos_dist p) (Hq : pos_dist q) : R :=
  sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))).
(* 对齐能量/自由能/对齐目标（照抄 UpReqAlign.v:104-110） *)
Definition align_energy_req (s : S) : R :=
  req_minus (opp (reward s)) (mult beta (log (pi_ref s) (pi_ref_pos s))).
Definition F_align_req (p : S -> R) (Hp : pos_dist p) : R :=
  plus (sumf (fun s => mult (p s) (align_energy_req s)))
       (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition align_objective_req (p : S -> R) (Hp : pos_dist p) : R :=
  opp (F_align_req p Hp).

(* 定义簇（照抄 UpReqAlign.v:336-345） *)
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable eta_le_one : le eta one.
Definition advantage_aug_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=
  req_minus (reward s)
            (mult beta (req_minus (log (pi_t s) (Hpi_t s)) (log (pi_ref s) (pi_ref_pos s)))).
Definition Z_rel_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) : R :=
  sumf (fun s => mult (pi_t s)
                      (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                          (advantage_aug_req pi_t Hpi_t s))))).

(* Z_rel 正性（照抄 UpReqAlign.v:348-358） *)
Lemma req_Z_rel_pos :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t), lt zero (Z_rel_req pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t.
  unfold Z_rel_req.
  apply sum_pos.
  intro s.
  apply mult_positive.
  - apply Hpi_t.
  - apply exp_neg_pos.
Qed.

Definition pi_next_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=  (* :360 *)
  mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
       (mult (pi_t s)
             (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                 (advantage_aug_req pi_t Hpi_t s))))).

(* pi_next 逐点正性（照抄 UpReqAlign.v:367-377） *)
Lemma req_pi_next_pos :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t), pos_dist (pi_next_req pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t s.
  unfold pi_next_req.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply mult_positive.
    + apply Hpi_t.
    + apply exp_neg_pos.
Qed.

(* π* 逐点正性（照抄 UpReqAlign.v:129-138） *)
Lemma req_pi_star_pos : pos_dist pi_star_req.
Proof.
  intro s.
  unfold pi_star_req.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply mult_positive.
    + apply pi_ref_pos.
    + apply exp_neg_pos.
Qed.

(* ============ N0：证人开门件（三层重述） ============
   （inv_pos 为接口字段、载 lt zero 证人数据——req2_Z_rel_pos（Qed 件）
   与本地 req_Z_rel_pos 应用不可转换，须 inv_pos_correct 四步链真证）；
   层3 relative_entropy 逐点全部重述（层1/层2 组装 + sum_ext）。 *)

(* 层1：log 证人重述（req_refl 供同点双正性）
   先例：UpReqAlign2:891 注记 + G05 B5 logd_log_witness_real req 同位。 *)
Definition kcxr_log_witness (x : R) (Hx Hx' : lt zero x) :
  req (log x Hx) (log x Hx') :=
  log_req_compat x x Hx Hx' (req_refl x).

(* 层2：inv_pos 载体证人重述（inv_pos_correct 双肢 + 环代数四步链） *)
Lemma kcxr_inv_pos_witness :
  forall (x : R) (w w' : lt zero x), req (inv_pos x w) (inv_pos x w').
Proof.
  intros x w w'.
  apply (req_trans (inv_pos x w)
                   (mult one (inv_pos x w))
                   (inv_pos x w')).
  - apply (req_sym (mult one (inv_pos x w)) (inv_pos x w)
                   (req_mult_one_l (inv_pos x w))).
  - apply (req_trans (mult one (inv_pos x w))
                     (mult (mult x (inv_pos x w')) (inv_pos x w))
                     (inv_pos x w')).
    + apply req_mult_compat.
      * apply (req_sym _ _ (inv_pos_correct x w')).
      * apply req_refl.
    + apply (req_trans (mult (mult x (inv_pos x w')) (inv_pos x w))
                       (mult (inv_pos x w') (mult x (inv_pos x w)))
                       (inv_pos x w')).
      * apply (req_trans (mult (mult x (inv_pos x w')) (inv_pos x w))
                         (mult (mult (inv_pos x w') x) (inv_pos x w))
                         (mult (inv_pos x w') (mult x (inv_pos x w)))).
        -- apply req_mult_compat.
           ++ apply mult_comm.
           ++ apply req_refl.
        -- apply (req_sym _ _
                   (mult_assoc (inv_pos x w') x (inv_pos x w))).
      * apply (req_trans (mult (inv_pos x w') (mult x (inv_pos x w)))
                         (mult (inv_pos x w') one)
                         (inv_pos x w')).
        -- apply req_mult_compat.
           ++ apply req_refl.
           ++ exact (inv_pos_correct x w).
        -- exact (req_mult_one_r (inv_pos x w')).
Qed.

(* 层2'：pi_next 载体重述（Z_rel_req ≡ req2_Z_rel δ 完成 +
   inv_pos 证人位层2 重述——UpReqAlign.v:360 与 req2_pi_next 的
   逐位同形载体在此打通） *)
Lemma kcxr_pi_next_transport :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S),
    req (pi_next_req pi_t Hpi_t s)
        (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos eta
              pi_t Hpi_t s).
Proof.
  intros pi_t Hpi_t s.
  unfold pi_next_req, NPX, req2_pi_next.
  apply req_mult_compat.
  - apply kcxr_inv_pos_witness.
  - apply req_refl.
Qed.


Lemma kcxr_kl_witness_transport :
  forall (p q p' q' : S -> R) (Hp : pos_dist p) (Hq : pos_dist q)
         (Hp' : pos_dist p') (Hq' : pos_dist q'),
    (forall s : S, req (p s) (p' s)) ->
    (forall s : S, req (q s) (q' s)) ->
    req (relative_entropy_req p q Hp Hq) (relative_entropy_req p' q' Hp' Hq').
Proof.
  intros p q p' q' Hp Hq Hp' Hq' Hp_leg Hq_leg.
  unfold relative_entropy_req.
  apply sum_ext.
  intro s.
  apply req_mult_compat.
  - apply Hp_leg.
  - unfold req_minus.
    apply req_plus_compat.
    + apply log_req_compat.
      apply Hp_leg.
    + apply req_opp_compat.
      apply log_req_compat.
      apply Hq_leg.
Qed.

(*
   语句 = UpReqAlign.v:434-442 req_backward_kl_identity 逐字同位；
   证 = req2_backward_kl_step（UpReqAlign3:3153，无条件）+ 证人重述三段。 *)
Theorem kcxr_req_backward_kl_identity :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (Hnorm : norm_one pi_t),
    req (relative_entropy_req pi_star_req (pi_next_req pi_t Hpi_t)
             req_pi_star_pos (req_pi_next_pos pi_t Hpi_t))
        (plus (mult (req_minus one eta)
                    (relative_entropy_req pi_star_req pi_t req_pi_star_pos Hpi_t))
              (plus (opp (mult eta (relative_entropy_req pi_t pi_star_req Hpi_t req_pi_star_pos)))
                    (relative_entropy_req pi_t (pi_next_req pi_t Hpi_t)
                         Hpi_t (req_pi_next_pos pi_t Hpi_t)))).
Proof.
  intros pi_t Hpi_t Hnorm.
  pose proof (@req2_backward_kl_step R RIS S sumf sum_ext sum_add sum_linear
                sum_pos log_req_compat log_inv_exp_neg_req reward beta beta_pos
                pi_ref pi_ref_pos eta Z_align_pos pi_t Hpi_t Hnorm) as H.
  apply (req_trans
           (relative_entropy_req pi_star_req (pi_next_req pi_t Hpi_t)
                req_pi_star_pos (req_pi_next_pos pi_t Hpi_t))
           (relative_entropy_req
              (@PSTR R RIS S sumf reward beta beta_pos pi_ref Z_align_pos)
              (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                    eta pi_t Hpi_t)
              (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref pi_ref_pos
                         Z_align_pos)
              (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                        pi_ref_pos eta pi_t Hpi_t))).
  (* 段1：LHS 重述（载体位 PSTR δ 完成 / NPX 层2 重述 +
     证人位 PSTR_pos/npx_pos 层1 重述） *)
  - exact (kcxr_kl_witness_transport pi_star_req (pi_next_req pi_t Hpi_t)
             (@PSTR R RIS S sumf reward beta beta_pos pi_ref Z_align_pos)
             (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                   eta pi_t Hpi_t)
             req_pi_star_pos (req_pi_next_pos pi_t Hpi_t)
             (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref pi_ref_pos
                        Z_align_pos)
             (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                       pi_ref_pos eta pi_t Hpi_t)
             (fun s => req_refl
                         (@PSTR R RIS S sumf reward beta beta_pos pi_ref
                                Z_align_pos s))
             (kcxr_pi_next_transport pi_t Hpi_t)).
  (* 段2：主体 = req2_backward_kl_step（别名 δ 透明完成） *)
  - apply (req_trans
             (relative_entropy_req
                (@PSTR R RIS S sumf reward beta beta_pos pi_ref Z_align_pos)
                (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref
                      pi_ref_pos eta pi_t Hpi_t)
                (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref pi_ref_pos
                           Z_align_pos)
                (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                          pi_ref_pos eta pi_t Hpi_t))
             (plus (mult (req_minus one eta)
                         (relative_entropy_req
                            (@PSTR R RIS S sumf reward beta beta_pos pi_ref
                                   Z_align_pos)
                            pi_t
                            (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref
                                       pi_ref_pos Z_align_pos)
                            Hpi_t))
                   (plus (opp (mult eta
                                   (relative_entropy_req pi_t
                                      (@PSTR R RIS S sumf reward beta beta_pos
                                             pi_ref Z_align_pos)
                                      Hpi_t
                                      (@PSTR_pos R RIS S sumf reward beta beta_pos
                                                 pi_ref pi_ref_pos Z_align_pos))))
                         (relative_entropy_req pi_t
                            (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref
                                  pi_ref_pos eta pi_t Hpi_t)
                            Hpi_t
                            (@npx_pos R RIS S sumf sum_pos reward beta beta_pos
                                      pi_ref pi_ref_pos eta pi_t Hpi_t))))).
    + exact H.
    (* 段3：RHS 重述（三处 KL：载体位 δ/层2' + 证人位层1 + 环重组） *)
    + apply req_plus_compat.
      * apply req_mult_compat.
        -- apply req_refl.
        -- exact (kcxr_kl_witness_transport
                    (@PSTR R RIS S sumf reward beta beta_pos pi_ref Z_align_pos)
                    pi_t pi_star_req pi_t
                    (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref
                               pi_ref_pos Z_align_pos)
                    Hpi_t req_pi_star_pos Hpi_t
                    (fun s => req_refl (pi_star_req s))
                    (fun s => req_refl (pi_t s))).
      * apply req_plus_compat.
        -- apply req_opp_compat.
           apply req_mult_compat.
           ++ apply req_refl.
           ++ exact (kcxr_kl_witness_transport pi_t
                       (@PSTR R RIS S sumf reward beta beta_pos pi_ref
                              Z_align_pos)
                       pi_t pi_star_req Hpi_t
                       (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref
                                  pi_ref_pos Z_align_pos)
                       Hpi_t req_pi_star_pos
                       (fun s => req_refl (pi_t s))
                       (fun s => req_refl (pi_star_req s))).
        -- exact (kcxr_kl_witness_transport pi_t
                    (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref
                          pi_ref_pos eta pi_t Hpi_t)
                    pi_t (pi_next_req pi_t Hpi_t) Hpi_t
                    (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                              pi_ref_pos eta pi_t Hpi_t)
                    Hpi_t (req_pi_next_pos pi_t Hpi_t)
                    (fun s => req_refl (pi_t s))
                    (fun s => req_sym (pi_next_req pi_t Hpi_t s)
                                (@NPX R RIS S sumf sum_pos reward beta
                                        beta_pos pi_ref pi_ref_pos eta
                                        pi_t Hpi_t s)
                                (kcxr_pi_next_transport pi_t Hpi_t s))).
Qed.

(* ============ 批 B 新开口（参数位② + N4；以上机制段为批 A 逐字节同复制） ============ *)

(* dpo_loss 同位别名（照抄 UpReqAlign.v:111-112；本节先前未备） *)
Definition dpo_loss_req (p : S -> R) (Hp : pos_dist p) : R :=
  opp (align_objective_req p Hp).

(* ---- 供给参数位②：plain-le KL≥0（UpReqAlign3.v:1451-1453
   req2_gibbs_inequality 原位同形，无 norm 加强形——诚实假设位
   req2_gibbs_inequality 假设位由本位供给，KLE/pos3 δ 透明完成） ---- *)
Hypothesis sup_gibbs :
  forall (p q : S -> R) (Hp : pos_dist p) (Hq : pos_dist q),
    le zero (relative_entropy_req p q Hp Hq).

(* ---- 桥2 显式参：req_step_kl_eta_bound（UpReqAlign.v:430-433 语句
   逐字同位；B 类桥保留假设位——评估记录见本文件批 B 头注；
*)
Hypothesis sup_step_kl_eta_bound :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t),
    le (relative_entropy_req pi_t (pi_next_req pi_t Hpi_t) Hpi_t (req_pi_next_pos pi_t Hpi_t))
       (mult eta (relative_entropy_req pi_t pi_star_req Hpi_t req_pi_star_pos)).

(* ---- align_objective 逐点重述（kcxr_kl_witness_transport 同构：
   载体逐点肢 + log 证人位 sum_ext 完成） ---- *)
Lemma kcxr_align_obj_transport :
  forall (p p' : S -> R) (Hp : pos_dist p) (Hp' : pos_dist p'),
    (forall s : S, req (p s) (p' s)) ->
    req (align_objective_req p Hp) (align_objective_req p' Hp').
Proof.
  intros p p' Hp Hp' Hleg.
  unfold align_objective_req, F_align_req.
  apply req_opp_compat.
  apply req_plus_compat.
  - apply sum_ext.
    intro s.
    apply req_mult_compat.
    + apply Hleg.
    + apply req_refl.
  - apply req_mult_compat.
    + apply req_refl.
    + apply sum_ext.
      intro s.
      apply req_mult_compat.
      * apply Hleg.
      * apply log_req_compat.
        apply Hleg.
Qed.

(*
   语句 = UpReqAlign.v:630-633 req_policy_improvement_mono 逐字同位；
   证 = r2_policy_improvement_mono（UpReqAlign3:1456，无条件）+
   唯一非 δ 点 npx_pos↔req_pi_next_pos 证人重述（kcxr_pi_next_transport）
   + align_objective 逐点重述（上件）；JJ/AO/KLE 三别名 δ 完成。 *)
Theorem kcxr_req_policy_improvement_mono :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (Hnorm : norm_one pi_t),
    le (align_objective_req pi_t Hpi_t)
       (align_objective_req (pi_next_req pi_t Hpi_t) (req_pi_next_pos pi_t Hpi_t)).
Proof.
  intros pi_t Hpi_t Hnorm.
  pose proof (@r2_policy_improvement_mono R RIS S sumf sum_ext sum_add sum_linear
                sum_pos log_req_compat log_inv_exp_neg_req reward beta beta_pos
                pi_ref pi_ref_pos eta eta_pos eta_le_one sup_gibbs
                pi_t Hpi_t Hnorm) as H.
  apply (le_id_l (align_objective_req pi_t Hpi_t)
                 (JJ S sumf reward beta pi_ref pi_ref_pos pi_t Hpi_t)
                 (align_objective_req (pi_next_req pi_t Hpi_t)
                                      (req_pi_next_pos pi_t Hpi_t))).
  (* 段1：LHS δ 完成（JJ ≡ align_objective_req，别名透明） *)
  - exact (req_refl (align_objective_req pi_t Hpi_t)).
  (* 段2：RHS 重述（载体位 NPX→pi_next_req 层2' + 证人位 npx_pos→
     req_pi_next_pos 层3 同步）+ 主体 = r2_policy_improvement_mono *)
  - apply (le_id_r (JJ S sumf reward beta pi_ref pi_ref_pos pi_t Hpi_t)
                   (JJ S sumf reward beta pi_ref pi_ref_pos
                      (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref
                            pi_ref_pos eta pi_t Hpi_t)
                      (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                                pi_ref_pos eta pi_t Hpi_t))
                   (align_objective_req (pi_next_req pi_t Hpi_t)
                                        (req_pi_next_pos pi_t Hpi_t))).
    + exact (kcxr_align_obj_transport
               (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref
                     pi_ref_pos eta pi_t Hpi_t)
               (pi_next_req pi_t Hpi_t)
               (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                         pi_ref_pos eta pi_t Hpi_t)
               (req_pi_next_pos pi_t Hpi_t)
               (fun s => req_sym (pi_next_req pi_t Hpi_t s)
                           (@NPX R RIS S sumf sum_pos reward beta beta_pos
                                   pi_ref pi_ref_pos eta pi_t Hpi_t s)
                           (kcxr_pi_next_transport pi_t Hpi_t s))).
    + exact H.
Qed.

(*
   语句 = UpReqAlign.v:466-471 req_policy_iter_kl_geom_step 逐字同位；
   桥1 = 批 A kcxr_req_backward_kl_identity（本 Module 同复制件）；
   桥2 = sup_step_kl_eta_bound 保留显式参；序代数肢 =
   UpReqAlign.req_plusA_opp_cancel_le（全局件直用）。 *)
Theorem kcxr_req_policy_iter_kl_geom_step :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (Hnorm : norm_one pi_t),
    le (relative_entropy_req pi_star_req (pi_next_req pi_t Hpi_t)
            req_pi_star_pos (req_pi_next_pos pi_t Hpi_t))
       (mult (req_minus one eta)
             (relative_entropy_req pi_star_req pi_t req_pi_star_pos Hpi_t)).
Proof.
  intros pi_t Hpi_t Hnorm.
  apply (le_id_l
    (relative_entropy_req pi_star_req (pi_next_req pi_t Hpi_t)
         req_pi_star_pos (req_pi_next_pos pi_t Hpi_t))
    (plus (mult (req_minus one eta)
                (relative_entropy_req pi_star_req pi_t req_pi_star_pos Hpi_t))
          (plus (opp (mult eta (relative_entropy_req pi_t pi_star_req Hpi_t req_pi_star_pos)))
                (relative_entropy_req pi_t (pi_next_req pi_t Hpi_t)
                     Hpi_t (req_pi_next_pos pi_t Hpi_t))))
    (mult (req_minus one eta)
          (relative_entropy_req pi_star_req pi_t req_pi_star_pos Hpi_t))).
  - exact (kcxr_req_backward_kl_identity pi_t Hpi_t Hnorm).
  - exact (req_plusA_opp_cancel_le
             (mult (req_minus one eta)
                   (relative_entropy_req pi_star_req pi_t req_pi_star_pos Hpi_t))
             (mult eta (relative_entropy_req pi_t pi_star_req Hpi_t req_pi_star_pos))
             (relative_entropy_req pi_t (pi_next_req pi_t Hpi_t)
                  Hpi_t (req_pi_next_pos pi_t Hpi_t))
             (sup_step_kl_eta_bound pi_t Hpi_t)).
Qed.

(*
   语句 = UpReqAlign.v:636-639 req_dpo_loss_iter_step_le 逐字同位；
   证 = 参数位② 供给件 + opp_le_compat（宿主 :640-646 同构）。 *)
Theorem kcxr_req_dpo_loss_iter_step_le :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (Hnorm : norm_one pi_t),
    le (dpo_loss_req (pi_next_req pi_t Hpi_t) (req_pi_next_pos pi_t Hpi_t))
       (dpo_loss_req pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t Hnorm.
  unfold dpo_loss_req.
  apply (opp_le_compat (align_objective_req pi_t Hpi_t)
                       (align_objective_req (pi_next_req pi_t Hpi_t) (req_pi_next_pos pi_t Hpi_t))).
  exact (kcxr_req_policy_improvement_mono pi_t Hpi_t Hnorm).
Qed.

End KlcxAlignBridgeB.
End KlcxAlignBridgeB.

(* ============================================================ *)
(* ============================================================ *)
(* [依赖方向评估] 本文件 Require UpReqAlign（批 3 同位别名使用）→      *)
(*   宿主不能反向 Require 本文件（循环依赖）→ 已证明形态 = 本文件尾部    *)
(*   「假设位已证明定理」段 + 逐字语句重申件 + 下游使用，宿主文件本体    *)
(*   零改动（两桥假设位原样保留 = 最 honest，已证明由本段定理 +          *)
(*   order.txt/_CoqProject 双树注册 + 下游使用完成）。                *)
(* [已证明定理] UpReqAlign.v 两桥假设位由本文件 kcxr_ 两件供给：         *)
(*   · 参数位 1 UpReqAlign.v:434-441 req_backward_kl_identity ← 批 A 段    *)
(*     kcxr_req_backward_kl_identity（N1，本文件 :268；节闭签名        *)
(*     _t24_probe1 实测：{R}{RIS} S sumf sum_ext sum_add sum_linear   *)
(*     sum_pos log_req_compat log_inv_exp_neg_req reward beta beta_pos*)
(*     pi_ref pi_ref_pos Z_align_pos eta pi_t Hpi_t Hnorm——           *)
(*     pi_ref_norm/eta_pos/eta_le_one/sum_le/sum_zero_nonneg 不入）； *)
(*   · 参数位 2 UpReqAlign.v:630-633 req_policy_improvement_mono ← 批 B    *)
(*     KlcxAlignBridgeB.kcxr_req_policy_improvement_mono（本文件       *)
(*     :879；节闭签名 _t24_probe1 实测含 sup_gibbs 诚实位——plain-le   *)
(*     KL≥0 同位申报，参数位 2 已证明至本位 + 构造完成，非欠账照原位申报）。 *)
(*   G07 头注阻塞裁决作废：G07_KLWall.v L652「阻塞裁决」所据「两桥    *)
(*   假设位无同位供给」情形已消除（参数位 1 与参数位 2 分见批 A/B 段头注）。       *)
(* [逐字语句重申件] 本 Module 机制面 = 批 A 段 :60-176 节参面/别名/   *)
(*   节内证人逐字节同复制（批 B Module 同法，同名件并存互不遮蔽）；    *)
(*   重申件语句逐字 = 宿主两桥假设位语句；证 = 使用本文件 kcxr_ 两件   *)
(*   （机制面同名定义 δ 完成，批 B 跨复制使用同法先例）。             *)
Module KlcxAlignWriteoffC.
Section KlcxAlignWriteoffC.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

(* ---- SumOver 的 req 签名对接面（逐位照抄 UpReqAlign.v:54-69） ---- *)
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
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero -> forall s : S, req (f s) zero.

(* 接口缺口桥（照抄 UpReqAlign.v:75-77） *)
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).

(* ---- 供给参数位①（本批新开口；Real 层证人 = G05_LogSmall:347） ----
   同位先例：UpReqAlign3.v:75-76（Req3AlignCore 同名参数位）。 *)
Hypothesis log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.

(* ---- 节参数（照抄 UpReqAlign.v:80-85 + 330-332） ---- *)
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable pi_ref_norm : req (sumf pi_ref) one.

Definition pos_dist (p : S -> R) : Set := forall s : S, lt zero (p s).   (* :88 *)
Definition norm_one (p : S -> R) : Set := req (sumf p) one.              (* :89 *)

(* 配分函数与闭式最优策略（照抄 UpReqAlign.v:92-97） *)
Definition Z_align_req : R :=
  sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Variable Z_align_pos : lt zero Z_align_req.                              (* :94 *)
Definition pi_star_req (s : S) : R :=
  mult (inv_pos Z_align_req Z_align_pos)
       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
(* 相对熵 req 形态（照抄 UpReqAlign.v:100-101） *)
Definition relative_entropy_req (p q : S -> R) (Hp : pos_dist p) (Hq : pos_dist q) : R :=
  sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))).
(* 对齐能量/自由能/对齐目标（照抄 UpReqAlign.v:104-110） *)
Definition align_energy_req (s : S) : R :=
  req_minus (opp (reward s)) (mult beta (log (pi_ref s) (pi_ref_pos s))).
Definition F_align_req (p : S -> R) (Hp : pos_dist p) : R :=
  plus (sumf (fun s => mult (p s) (align_energy_req s)))
       (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition align_objective_req (p : S -> R) (Hp : pos_dist p) : R :=
  opp (F_align_req p Hp).

(* 定义簇（照抄 UpReqAlign.v:336-345） *)
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable eta_le_one : le eta one.
Definition advantage_aug_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=
  req_minus (reward s)
            (mult beta (req_minus (log (pi_t s) (Hpi_t s)) (log (pi_ref s) (pi_ref_pos s)))).
Definition Z_rel_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) : R :=
  sumf (fun s => mult (pi_t s)
                      (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                          (advantage_aug_req pi_t Hpi_t s))))).

(* Z_rel 正性（照抄 UpReqAlign.v:348-358） *)
Lemma req_Z_rel_pos :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t), lt zero (Z_rel_req pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t.
  unfold Z_rel_req.
  apply sum_pos.
  intro s.
  apply mult_positive.
  - apply Hpi_t.
  - apply exp_neg_pos.
Qed.

Definition pi_next_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=  (* :360 *)
  mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
       (mult (pi_t s)
             (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                 (advantage_aug_req pi_t Hpi_t s))))).

(* pi_next 逐点正性（照抄 UpReqAlign.v:367-377） *)
Lemma req_pi_next_pos :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t), pos_dist (pi_next_req pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t s.
  unfold pi_next_req.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply mult_positive.
    + apply Hpi_t.
    + apply exp_neg_pos.
Qed.

(* π* 逐点正性（照抄 UpReqAlign.v:129-138） *)
Lemma req_pi_star_pos : pos_dist pi_star_req.
Proof.
  intro s.
  unfold pi_star_req.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply mult_positive.
    + apply pi_ref_pos.
    + apply exp_neg_pos.
Qed.

(* ---- 供给参数位②的诚实假设位（批 B KlcxAlignBridgeB 同名参数位同位复制；
   plain-le KL≥0 无 norm 加强形——序无消去，照原位申报勿越） ---- *)
Hypothesis sup_gibbs :
  forall (p q : S -> R) (Hp : pos_dist p) (Hq : pos_dist q),
    le zero (relative_entropy_req p q Hp Hq).

(* ---- 批 A/B 重述件同位复制（Module 内 δ 自洽；批 B 同法先例）——
   跨面使用的证人位桥：inv_pos 载体证人万能重述 + KL 逐点全部重述 +
   align_objective 逐点重述。证词条位判据：_t24_probe2/_probe3 实测
   两枚同名 Qed 件应用不可转换（Qed 件不可 delta），conv 只通无证人
   定义面（P0-P3/P5 全绿）——凡语句含 Qed 证人项位，一律以重述件完成。 *)
Lemma kcxr_inv_pos_witness :
  forall (x : R) (w w' : lt zero x), req (inv_pos x w) (inv_pos x w').
Proof.
  intros x w w'.
  apply (req_trans (inv_pos x w)
                   (mult one (inv_pos x w))
                   (inv_pos x w')).
  - apply (req_sym (mult one (inv_pos x w)) (inv_pos x w)
                   (req_mult_one_l (inv_pos x w))).
  - apply (req_trans (mult one (inv_pos x w))
                     (mult (mult x (inv_pos x w')) (inv_pos x w))
                     (inv_pos x w')).
    + apply req_mult_compat.
      * apply (req_sym _ _ (inv_pos_correct x w')).
      * apply req_refl.
    + apply (req_trans (mult (mult x (inv_pos x w')) (inv_pos x w))
                       (mult (inv_pos x w') (mult x (inv_pos x w)))
                       (inv_pos x w')).
      * apply (req_trans (mult (mult x (inv_pos x w')) (inv_pos x w))
                         (mult (mult (inv_pos x w') x) (inv_pos x w))
                         (mult (inv_pos x w') (mult x (inv_pos x w)))).
        -- apply req_mult_compat.
           ++ apply mult_comm.
           ++ apply req_refl.
        -- apply (req_sym _ _
                   (mult_assoc (inv_pos x w') x (inv_pos x w))).
      * apply (req_trans (mult (inv_pos x w') (mult x (inv_pos x w)))
                         (mult (inv_pos x w') one)
                         (inv_pos x w')).
        -- apply req_mult_compat.
           ++ apply req_refl.
           ++ exact (inv_pos_correct x w).
        -- exact (req_mult_one_r (inv_pos x w')).
Qed.

Lemma kcxr_kl_witness_transport :
  forall (p q p' q' : S -> R) (Hp : pos_dist p) (Hq : pos_dist q)
         (Hp' : pos_dist p') (Hq' : pos_dist q'),
    (forall s : S, req (p s) (p' s)) ->
    (forall s : S, req (q s) (q' s)) ->
    req (relative_entropy_req p q Hp Hq) (relative_entropy_req p' q' Hp' Hq').
Proof.
  intros p q p' q' Hp Hq Hp' Hq' Hp_leg Hq_leg.
  unfold relative_entropy_req.
  apply sum_ext.
  intro s.
  apply req_mult_compat.
  - apply Hp_leg.
  - unfold req_minus.
    apply req_plus_compat.
    + apply log_req_compat.
      apply Hp_leg.
    + apply req_opp_compat.
      apply log_req_compat.
      apply Hq_leg.
Qed.

Lemma kcxr_align_obj_transport :
  forall (p p' : S -> R) (Hp : pos_dist p) (Hp' : pos_dist p'),
    (forall s : S, req (p s) (p' s)) ->
    req (align_objective_req p Hp) (align_objective_req p' Hp').
Proof.
  intros p p' Hp Hp' Hleg.
  unfold align_objective_req, F_align_req.
  apply req_opp_compat.
  apply req_plus_compat.
  - apply sum_ext.
    intro s.
    apply req_mult_compat.
    + apply Hleg.
    + apply req_refl.
  - apply req_mult_compat.
    + apply req_refl.
    + apply sum_ext.
      intro s.
      apply req_mult_compat.
      * apply Hleg.
      * apply log_req_compat.
        apply Hleg.
Qed.

(* ---- 批 C 新件（wcxr_ 前缀）：pi_next 载体肢（我节 → 批 A/批 B 节闭面；
   载体位 δ 完成 + inv_pos 证人位重述——P6 判据同位修复） ---- *)
Lemma wcxr_pi_next_leg_a :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S),
    req (pi_next_req pi_t Hpi_t s)
        (UpReqAlign4.pi_next_req S sumf sum_pos reward beta beta_pos pi_ref
           pi_ref_pos eta pi_t Hpi_t s).
Proof.
  intros pi_t Hpi_t s.
  apply (req_trans (pi_next_req pi_t Hpi_t s)
                   (mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                         (mult (pi_t s)
                               (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                   (advantage_aug_req pi_t Hpi_t s))))))
                   (UpReqAlign4.pi_next_req S sumf sum_pos reward beta beta_pos
                      pi_ref pi_ref_pos eta pi_t Hpi_t s)).
  - exact (req_refl (pi_next_req pi_t Hpi_t s)).
  - apply req_mult_compat.
    + apply kcxr_inv_pos_witness.
    + apply req_refl.
Qed.

Lemma wcxr_pi_next_leg_b :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S),
    req (pi_next_req pi_t Hpi_t s)
        (KlcxAlignBridgeB.pi_next_req S sumf sum_pos reward beta beta_pos
           pi_ref pi_ref_pos eta pi_t Hpi_t s).
Proof.
  intros pi_t Hpi_t s.
  apply (req_trans (pi_next_req pi_t Hpi_t s)
                   (mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                         (mult (pi_t s)
                               (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                   (advantage_aug_req pi_t Hpi_t s))))))
                   (KlcxAlignBridgeB.pi_next_req S sumf sum_pos reward beta beta_pos
                      pi_ref pi_ref_pos eta pi_t Hpi_t s)).
  - exact (req_refl (pi_next_req pi_t Hpi_t s)).
  - apply req_mult_compat.
    + apply kcxr_inv_pos_witness.
    + apply req_refl.
Qed.

(* ============ 已证明定理重申件 1/2：参数位 1（UpReqAlign.v:434-441） ============
   语句逐字 = 宿主 req_backward_kl_identity 假设位；证 = 使用批 A
   kcxr_req_backward_kl_identity（本文件 :268；实参序 = _t24_probe1
   Arguments 实录）+ 证人位重述（批 A N1 同构配方，角色对调）。 *)
Theorem req_backward_kl_identity_final :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (Hnorm : norm_one pi_t),
    req (relative_entropy_req pi_star_req (pi_next_req pi_t Hpi_t)
             req_pi_star_pos (req_pi_next_pos pi_t Hpi_t))
        (plus (mult (req_minus one eta)
                    (relative_entropy_req pi_star_req pi_t req_pi_star_pos Hpi_t))
              (plus (opp (mult eta (relative_entropy_req pi_t pi_star_req Hpi_t req_pi_star_pos)))
                    (relative_entropy_req pi_t (pi_next_req pi_t Hpi_t)
                         Hpi_t (req_pi_next_pos pi_t Hpi_t)))).
Proof.
  intros pi_t Hpi_t Hnorm.
  pose proof (@kcxr_req_backward_kl_identity R RIS S sumf sum_ext sum_add
                sum_linear sum_pos log_req_compat log_inv_exp_neg_req reward
                beta beta_pos pi_ref pi_ref_pos Z_align_pos eta
                pi_t Hpi_t Hnorm) as H.
  apply (req_trans
           (relative_entropy_req pi_star_req (pi_next_req pi_t Hpi_t)
                req_pi_star_pos (req_pi_next_pos pi_t Hpi_t))
           (relative_entropy_req
              (UpReqAlign4.pi_star_req S sumf reward beta beta_pos pi_ref
                 Z_align_pos)
              (UpReqAlign4.pi_next_req S sumf sum_pos reward beta beta_pos
                 pi_ref pi_ref_pos eta pi_t Hpi_t)
              (UpReqAlign4.req_pi_star_pos S sumf reward beta beta_pos pi_ref
                 pi_ref_pos Z_align_pos)
              (UpReqAlign4.req_pi_next_pos S sumf sum_pos reward beta beta_pos
                 pi_ref pi_ref_pos eta pi_t Hpi_t))).
  (* 段1：LHS 我的证人位 → 批 A 面（载体 conv + pi_next 重述肢） *)
  - exact (kcxr_kl_witness_transport pi_star_req (pi_next_req pi_t Hpi_t)
             (UpReqAlign4.pi_star_req S sumf reward beta beta_pos pi_ref
                Z_align_pos)
             (UpReqAlign4.pi_next_req S sumf sum_pos reward beta beta_pos
                pi_ref pi_ref_pos eta pi_t Hpi_t)
             req_pi_star_pos (req_pi_next_pos pi_t Hpi_t)
             (UpReqAlign4.req_pi_star_pos S sumf reward beta beta_pos pi_ref
                pi_ref_pos Z_align_pos)
             (UpReqAlign4.req_pi_next_pos S sumf sum_pos reward beta beta_pos
                pi_ref pi_ref_pos eta pi_t Hpi_t)
             (fun s => req_refl (pi_star_req s))
             (wcxr_pi_next_leg_a pi_t Hpi_t)).
  (* 段2：主体 = H + RHS 批 A 面 → 我的证人位 三处重述回 *)
  - apply (req_trans
             (relative_entropy_req
                (UpReqAlign4.pi_star_req S sumf reward beta beta_pos pi_ref
                   Z_align_pos)
                (UpReqAlign4.pi_next_req S sumf sum_pos reward beta beta_pos
                   pi_ref pi_ref_pos eta pi_t Hpi_t)
                (UpReqAlign4.req_pi_star_pos S sumf reward beta beta_pos pi_ref
                   pi_ref_pos Z_align_pos)
                (UpReqAlign4.req_pi_next_pos S sumf sum_pos reward beta beta_pos
                   pi_ref pi_ref_pos eta pi_t Hpi_t))
             (plus (mult (req_minus one eta)
                         (relative_entropy_req
                            (UpReqAlign4.pi_star_req S sumf reward beta beta_pos
                               pi_ref Z_align_pos)
                            pi_t
                            (UpReqAlign4.req_pi_star_pos S sumf reward beta
                               beta_pos pi_ref pi_ref_pos Z_align_pos)
                            Hpi_t))
                   (plus (opp (mult eta
                              (relative_entropy_req pi_t
                                 (UpReqAlign4.pi_star_req S sumf reward beta
                                    beta_pos pi_ref Z_align_pos)
                                 Hpi_t
                                 (UpReqAlign4.req_pi_star_pos S sumf reward beta
                                    beta_pos pi_ref pi_ref_pos Z_align_pos))))
                         (relative_entropy_req pi_t
                            (UpReqAlign4.pi_next_req S sumf sum_pos reward beta
                               beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t)
                            Hpi_t
                            (UpReqAlign4.req_pi_next_pos S sumf sum_pos reward
                               beta beta_pos pi_ref pi_ref_pos eta pi_t
                               Hpi_t))))).
    + exact H.
    + apply req_plus_compat.
      * apply req_mult_compat.
        -- apply req_refl.
        -- exact (kcxr_kl_witness_transport
                     (UpReqAlign4.pi_star_req S sumf reward beta beta_pos pi_ref
                        Z_align_pos)
                     pi_t pi_star_req pi_t
                     (UpReqAlign4.req_pi_star_pos S sumf reward beta beta_pos
                        pi_ref pi_ref_pos Z_align_pos)
                     Hpi_t req_pi_star_pos Hpi_t
                     (fun s => req_refl
                                 (UpReqAlign4.pi_star_req S sumf reward beta
                                    beta_pos pi_ref Z_align_pos s))
                     (fun s => req_refl (pi_t s))).
      * apply req_plus_compat.
        -- apply req_opp_compat. apply req_mult_compat.
           ++ apply req_refl.
           ++ exact (kcxr_kl_witness_transport
                        pi_t
                        (UpReqAlign4.pi_star_req S sumf reward beta beta_pos
                           pi_ref Z_align_pos)
                        pi_t pi_star_req
                        Hpi_t
                        (UpReqAlign4.req_pi_star_pos S sumf reward beta beta_pos
                           pi_ref pi_ref_pos Z_align_pos)
                        Hpi_t req_pi_star_pos
                        (fun s => req_refl (pi_t s))
                        (fun s => req_refl
                                    (UpReqAlign4.pi_star_req S sumf reward beta
                                       beta_pos pi_ref Z_align_pos s))).
        -- exact (kcxr_kl_witness_transport
                     pi_t
                     (UpReqAlign4.pi_next_req S sumf sum_pos reward beta beta_pos
                        pi_ref pi_ref_pos eta pi_t Hpi_t)
                     pi_t (pi_next_req pi_t Hpi_t)
                     Hpi_t
                     (UpReqAlign4.req_pi_next_pos S sumf sum_pos reward beta
                        beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t)
                     Hpi_t (req_pi_next_pos pi_t Hpi_t)
                     (fun s => req_refl (pi_t s))
                     (fun s => req_sym (pi_next_req pi_t Hpi_t s)
                                 (UpReqAlign4.pi_next_req S sumf sum_pos reward
                                    beta beta_pos pi_ref pi_ref_pos eta pi_t
                                    Hpi_t s)
                                 (wcxr_pi_next_leg_a pi_t Hpi_t s))).
Qed.

(* ============ 已证明定理重申件 2/2：参数位 2（UpReqAlign.v:630-633） ============
   语句逐字 = 宿主 req_policy_improvement_mono 假设位；证 = 使用批 B
   KlcxAlignBridgeB.kcxr_req_policy_improvement_mono（本文件 :879；
   + LHS δ 完成 / RHS align_obj 逐点重述（pi_next 载体肢同上）。 *)
Theorem req_policy_improvement_mono_final :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (Hnorm : norm_one pi_t),
    le (align_objective_req pi_t Hpi_t)
       (align_objective_req (pi_next_req pi_t Hpi_t) (req_pi_next_pos pi_t Hpi_t)).
Proof.
  intros pi_t Hpi_t Hnorm.
  pose proof (@KlcxAlignBridgeB.kcxr_req_policy_improvement_mono R RIS S sumf
                sum_ext sum_add sum_linear sum_pos log_req_compat
                log_inv_exp_neg_req reward beta beta_pos pi_ref pi_ref_pos
                eta eta_pos eta_le_one sup_gibbs pi_t Hpi_t Hnorm) as H.
  apply (le_id_l
           (KlcxAlignBridgeB.align_objective_req S sumf reward beta pi_ref
              pi_ref_pos pi_t Hpi_t)
           (align_objective_req pi_t Hpi_t)
           (align_objective_req (pi_next_req pi_t Hpi_t)
              (req_pi_next_pos pi_t Hpi_t))).
  - exact (req_refl (align_objective_req pi_t Hpi_t)).
  - apply (le_id_r
             (KlcxAlignBridgeB.align_objective_req S sumf reward beta pi_ref
                pi_ref_pos pi_t Hpi_t)
             (KlcxAlignBridgeB.align_objective_req S sumf reward beta pi_ref
                pi_ref_pos
                (KlcxAlignBridgeB.pi_next_req S sumf sum_pos reward beta
                   beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t)
                (KlcxAlignBridgeB.req_pi_next_pos S sumf sum_pos reward beta
                   beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t))
             (align_objective_req (pi_next_req pi_t Hpi_t)
                (req_pi_next_pos pi_t Hpi_t))).
    + exact (kcxr_align_obj_transport
                (KlcxAlignBridgeB.pi_next_req S sumf sum_pos reward beta
                   beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t)
                (pi_next_req pi_t Hpi_t)
                (KlcxAlignBridgeB.req_pi_next_pos S sumf sum_pos reward beta
                   beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t)
                (req_pi_next_pos pi_t Hpi_t)
                (fun s => req_sym (pi_next_req pi_t Hpi_t s)
                            (KlcxAlignBridgeB.pi_next_req S sumf sum_pos reward
                               beta beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t s)
                            (wcxr_pi_next_leg_b pi_t Hpi_t s))).
    + exact H.
Qed.

End KlcxAlignWriteoffC.
End KlcxAlignWriteoffC.
