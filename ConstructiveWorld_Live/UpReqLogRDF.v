(* ============================================================ *)
(* UpReqLogRDF.v *)
(* *)
(* 目的： 对数与实数差分面（ReqDiffPlain 载体）的对数定律族。 *)
(* 主件： lrdf_t_abs_eq / lrdf_xh_eq 等对数差分定律与 lrdf_cancel_l_opp。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSLM、UpReqRDF。 *)
(* 备注： 非负/差分/对数三 plain 接口为显式 Variable 前提；对数下界前提显式申报。 *)
(* ============================================================ *)

(* ============================================================ *)

(*   槽 3 = rdf_log_diff@UpReqRDF:1704 S 阻塞 → 缺件 A/B 建设 + 修正消解        *)
(*   2026-09-10                                                            *)
(* ------------------------------------------------------------------ *)


(*    real_log_differentiable@:46386 在盘但为域前提记录形              *)
(*    （RealDifferentiable L44447：f : forall x, 0<x -> Real）+ 尾 slack     *)
(*    （|D| ≤ eps|h|+eps'，Bishop 逐 eps）；reqRDF 形 = 纯函数 f : R -> R    *)
(*    + 精确形 |D| ≤ eps|h|。本件换装完成 = lrdf_log_root（Part 2）。        *)


(*    forall g Hg (dg : reqRDF g), reqRDF (fun z => log (g z) (Hg z))，      *)
(*    df z := inv(g z)·dg z（正性见证型复合求导规则/见证搬运封装）。         *)


(*      reqRDF g 前提位（与 req_rdf_compose@UpReqRDF:1227 显式 dg 同族对照； *)
(*      g 取无正则性正函数时结论无据，本构造性接口层不可证——判「修正消解」， *)
(*      非硬凑原形）。                                                      *)
(*    ②eps'-尾 slack 与精确形之关系：非 Or 编码固有间隙——req 层 le 为抽象    *)
(*      非严格序（非 Or 编码），配合 ReqLogPlain.log_le_linear_plain 精确形   *)
(*      槽（UpReqSLM L143，批5 波0 资产），log(1+t) ≤ t 精确成立（           *)
(*      req_log_one_plus_le@UpReqSLM），尾 slack 消解；精确完成余缺仅为      *)
(*      三个 Or 编码系内点引理的 req 槽形镜像（本件三 Hypothesis 申报位）。   *)
(*    ③消费链消解：rdf_log_diff 唯一消费位 = req_entropy_differentiable      *)

(*      以 lrdf_entropy_differentiable 同链重建（零 rdf_log_diff 变元，      *)
(*      dg 位由 HOmega = req_rdf_mult 产物供给——原节本就有此件，结论：       *)
(*      槽实为「可自供的漏装位」）。                                        *)

(*  [S1] lrdf_abs_lower_pos : lt (abs a) c -> lt zero (plus c a)             *)
(*       —— real_abs_lt_lower@44527（Or 编码系内证）req 槽形镜像；      *)
(*       抽象接口无「双侧加法」lt 原语，正和形为消费可用形。                  *)
(*  [S2] lrdf_abs_le_intro : le u w -> le (opp u) w -> le (abs u) w          *)
(*       —— real_abs_le_quad_eps@46104 四分叉核（Or 编码 |X| 桥）      *)
(*       req 槽形镜像（双侧绝对值引入）。                                    *)
(*  [S3] lrdf_sq_nonneg / lrdf_sq_le_abs_sq : le zero (t·t) /                *)
(*       le (t·t) (|t|·|t|) —— Qsquare_nonneg/q_sq_abs@46130 逐点      *)
(*       Q 层事实 req 槽形镜像（UpReqSLM L20-25 M2 墙结论同族：plain 形需    *)
(*       符号判定，抽象接口不可导）。                                       *)

(*  （UpReqSLM）/ReqLogPlain（UpReqSLM L143，log_le_linear_plain 精确形 +    *)
(*  log_req_compat_plain）。Real 消解随 Real 层战役显式假设（UpReqSLM 头注同判）。*)
(* 路线（核心估计，对标 L46386 主定理结构，req 层重排）：                *)

(*   上界：log(1+t) ≤ t 精确（req_log_one_plus_le）⟹ D ≤ 0 ≤ eps|h|。        *)
(*   下界：t − log(1+t) ≡ t + log inv(1+t) ≤ t + (inv(1+t)−1) ≡ t²·inv(1+t)  *)
(*     （req_log_inv_one_inv + log_le_linear_plain + lrdf_t_plus_inv_minus_  *)
(*     one 环恒等，对标 real_t_minus_log_bound@45024 无 eps 化）             *)
(*     ≤ 2t²（inv(1+t) ≤ 2 ⟸ 1/2 ≤ 1+t）≤ eps·|h|（|t| ≤ min(1/2, eps·x/2)）*)
(*     其中 2t² ≤ eps·|h| 走 |t| ≤ eps·x/2：t² ≤ |t|² ≤ |t|·(eps·x/2)。      *)
(*   δ := min(x/2, (eps·x/2)·x)（对标 δ := min(x/2, eps·x²/4)）。      *)
(*   缺件 B 引擎以同核（lrdf_core_abs_bound 于 t := (g(z+h)−g z)·inv(g z)）   *)
(*   + 误差分解 tt ≡ inv·ds·h + err·inv 组装（budget: |X|≤(eps/2)|h|、       *)
(*   |err·inv|≤(eps/2)|h|）。                                              *)
(* 防撞：lrdf_ 前缀 + 全部新名 21 个，attn 目录全 .v grep 零命中（建前实测    *)
(*    2026-09-10；UpReqLogRDF 文件名零命中）。                              *)
(* 红线：Set 层零 Prop（结论全 req/lt/le/sigT+Set-And 值；Rocq 9 排序多态    *)
(*    Or 仅作 lt_le_iff 入参，零泄露）；全 Qed 闭合；零 公理/承认件/      *)

(* 编译配方：_lrdf_g2.cmd + guard 包装                                       *)


(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSLM.
Require Import UpReqRDF.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Part 0：节假设位组（三申报槽 S1-S3 + 三类槽承接）                              *)
(* ============================================================ *)

Section LRDF.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {RNN : ReqNonnegPlain R}.
Context {RDP : ReqDiffPlain R}.
Context {RLL : ReqLogPlain R}.

(* S1：|a| < c ⟹ 0 < c + a（real_abs_lt_lower req 槽形，正和形） *)
Hypothesis lrdf_abs_lower_pos :
  forall (a c : R), lt (abs a) c -> lt zero (plus c a).

(* S2：u ≤ w ∧ −u ≤ w ⟹ |u| ≤ w（real_abs_le_quad_eps 核 req 槽形） *)
Hypothesis lrdf_abs_le_intro :
  forall (u w : R), le u w -> le (opp u) w -> le (abs u) w.

(* S3a：0 ≤ t²（Qsquare_nonneg 逐点事实 req 槽形） *)
Hypothesis lrdf_sq_nonneg : forall t : R, le zero (mult t t).

(* S3b：t² ≤ |t|²（q_sq_abs@46130 req 槽形） *)
Hypothesis lrdf_sq_le_abs_sq : forall t : R,
  le (mult t t) (mult (abs t) (abs t)).

(* ============================================================ *)
(* Part 0.5：纯接口小件（零槽；环/序/inv 机）                                   *)
(* ============================================================ *)

(* 0.0：req_minus 展开机（req_minus δ 透明；unification 位显式换形用） *)
Lemma lrdf_req_minus_unfold : forall a b : R,
  req (req_minus a b) (plus a (opp b)).
Proof.
  intros a b. exact (req_refl (plus a (opp b))).
Qed.

(* 0.1：1 ≤ c·w ⟹ inv c ≤ w（inv 放缩机） *)
Lemma lrdf_inv_le_of_one_le_mul : forall (c w : R) (Hc : lt zero c),
  le one (mult c w) -> le (inv_pos c Hc) w.
Proof.
  intros c w Hc Hle.
  apply (le_id_l (inv_pos c Hc) (mult one (inv_pos c Hc)) w
           (req_trans (inv_pos c Hc) (mult (inv_pos c Hc) one)
                      (mult one (inv_pos c Hc))
                      (req_sym (mult (inv_pos c Hc) one) (inv_pos c Hc)
                         (mult_one (inv_pos c Hc)))
                      (mult_comm (inv_pos c Hc) one))).
  apply (le_id_r (mult one (inv_pos c Hc)) (mult (mult c w) (inv_pos c Hc)) w).
  - exact (req_trans (mult (mult c w) (inv_pos c Hc))
                     (mult c (mult w (inv_pos c Hc)))
                     w
                     (req_sym (mult c (mult w (inv_pos c Hc)))
                              (mult (mult c w) (inv_pos c Hc))
                              (mult_assoc c w (inv_pos c Hc)))
                     (req_trans (mult c (mult w (inv_pos c Hc)))
                                (mult c (mult (inv_pos c Hc) w))
                                w
                                (req_mult_compat c c (mult w (inv_pos c Hc))
                                                   (mult (inv_pos c Hc) w)
                                                   (req_refl c) (mult_comm w (inv_pos c Hc)))
                                (req_trans (mult c (mult (inv_pos c Hc) w))
                                           (mult (mult c (inv_pos c Hc)) w)
                                           w
                                           (mult_assoc c (inv_pos c Hc) w)
                                           (req_trans (mult (mult c (inv_pos c Hc)) w)
                                                      (mult one w)
                                                      w
                                                      (req_mult_compat (mult c (inv_pos c Hc)) one w w
                                                         (inv_pos_correct c Hc) (req_refl w))
                                                      (req_trans (mult one w) (mult w one) w
                                                                 (mult_comm one w) (mult_one w)))))).
  - exact (le_mult_compat one (mult c w) (inv_pos c Hc) (inv_pos_pos c Hc) Hle).
Qed.

(* 0.2：a·(opp b) ≡ opp (a·b)（opp 出分配；UpReqLogCompD A2 同形独立重建） *)
Lemma lrdf_mult_opp_r : forall a b : R, req (mult a (opp b)) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (mult a (opp b)) (mult a b) (opp (mult a b))).
  apply (req_trans (plus (mult a (opp b)) (mult a b))
                   zero
                   (plus (opp (mult a b)) (mult a b))).
  - apply (req_trans (plus (mult a (opp b)) (mult a b))
                     (mult a (plus (opp b) b))
                     zero).
    + exact (req_sym (mult a (plus (opp b) b))
                     (plus (mult a (opp b)) (mult a b))
                     (distrib a (opp b) b)).
    + apply (req_trans (mult a (plus (opp b) b)) (mult a zero) zero).
      * exact (req_mult_compat a a (plus (opp b) b) zero (req_refl a)
                 (req_trans (plus (opp b) b) (plus b (opp b)) zero
                            (plus_comm (opp b) b) (plus_opp b))).
      * exact (mult_zero a).
  - exact (req_sym (plus (opp (mult a b)) (mult a b)) zero
             (req_trans (plus (opp (mult a b)) (mult a b))
                        (plus (mult a b) (opp (mult a b))) zero
                        (plus_comm (opp (mult a b)) (mult a b)) (plus_opp (mult a b)))).
Qed.

(* 0.3：(u + w) − u ≡ w（右消去） *)
Lemma lrdf_cancel_r : forall u w : R, req (plus (plus u w) (opp u)) w.
Proof.
  intros u w.
  apply (req_trans (plus (plus u w) (opp u)) (plus (plus w u) (opp u)) w).
  - exact (req_plus_compat (plus u w) (plus w u) (opp u) (opp u)
              (plus_comm u w) (req_refl (opp u))).
  - apply (req_trans (plus (plus w u) (opp u)) (plus w (plus u (opp u))) w).
    + exact (req_sym (plus w (plus u (opp u))) (plus (plus w u) (opp u))
               (plus_assoc w u (opp u))).
    + apply (req_trans (plus w (plus u (opp u))) (plus w zero) w).
      * exact (req_plus_compat w w (plus u (opp u)) zero (req_refl w) (plus_opp u)).
      * exact (plus_zero w).
Qed.

(* 0.4：(opp u) + (u + w) ≡ w（左 opp 消去） *)
Lemma lrdf_cancel_l_opp : forall u w : R, req (plus (opp u) (plus u w)) w.
Proof.
  intros u w.
  apply (req_trans (plus (opp u) (plus u w)) (plus (plus (opp u) u) w) w).
  - exact (plus_assoc (opp u) u w).
  - apply (req_trans (plus (plus (opp u) u) w) (plus zero w) w).
    + exact (req_plus_compat (plus (opp u) u) zero w w
               (req_trans (plus (opp u) u) (plus u (opp u)) zero
                          (plus_comm (opp u) u) (plus_opp u))
               (req_refl w)).
    + exact (req_trans (plus zero w) (plus w zero) w (plus_comm zero w) (plus_zero w)).
Qed.

(* 0.5：|a·inv x| ≡ |a|·inv x（x>0；abs_mult + abs_pos） *)
Lemma lrdf_t_abs_eq : forall (x a : R) (Hx : lt zero x),
  req (abs (mult a (inv_pos x Hx))) (mult (abs a) (inv_pos x Hx)).
Proof.
  intros x a Hx.
  apply (req_trans (abs (mult a (inv_pos x Hx)))
                   (mult (abs a) (abs (inv_pos x Hx)))
                   (mult (abs a) (inv_pos x Hx))).
  - exact (abs_mult a (inv_pos x Hx)).
  - exact (req_mult_compat (abs a) (abs a) (abs (inv_pos x Hx)) (inv_pos x Hx)
             (req_refl (abs a)) (abs_pos (inv_pos x Hx) (inv_pos_pos x Hx))).
Qed.

(* 0.6：|a| < b·x ⟹ |a·inv x| < b（x>0；t 小化机，一式两用） *)
Lemma lrdf_t_lt_of : forall (x a b : R) (Hx : lt zero x),
  lt (abs a) (mult b x) -> lt (abs (mult a (inv_pos x Hx))) b.
Proof.
  intros x a b Hx Hlt.
  apply (lt_id_l (abs (mult a (inv_pos x Hx))) (mult (abs a) (inv_pos x Hx)) b
            (lrdf_t_abs_eq x a Hx)).
  apply (lt_id_r (mult (abs a) (inv_pos x Hx)) (mult (mult b x) (inv_pos x Hx)) b).
  - exact (req_trans (mult (mult b x) (inv_pos x Hx))
                     (mult b (mult x (inv_pos x Hx)))
                     b
                     (req_sym (mult b (mult x (inv_pos x Hx)))
                              (mult (mult b x) (inv_pos x Hx))
                              (mult_assoc b x (inv_pos x Hx)))
                     (req_trans (mult b (mult x (inv_pos x Hx)))
                                (mult b one)
                                b
                                (req_mult_compat b b (mult x (inv_pos x Hx)) one
                                   (req_refl b) (inv_pos_correct x Hx))
                                (mult_one b))).
  - exact (lt_mult_compat (abs a) (mult b x) (inv_pos x Hx) (inv_pos_pos x Hx) Hlt).
Qed.

(* 0.7：A ≡ tt + B 形换形：tt ≡ A + B ⟹ opp A ≡ (opp tt) + B（误差分裂机） *)
Lemma lrdf_opp_split_eq : forall (A B tt : R),
  req tt (plus A B) -> req (opp A) (plus (opp tt) B).
Proof.
  intros A B tt H.
  apply (req_trans (opp A) (plus (opp A) (plus (opp B) B)) (plus (opp tt) B)).
  - apply (req_sym (plus (opp A) (plus (opp B) B)) (opp A)).
    apply (req_trans (plus (opp A) (plus (opp B) B)) (plus (opp A) zero) (opp A)).
    + exact (req_plus_compat (opp A) (opp A) (plus (opp B) B) zero
               (req_refl (opp A))
               (req_trans (plus (opp B) B) (plus B (opp B)) zero
                          (plus_comm (opp B) B) (plus_opp B))).
    + exact (plus_zero (opp A)).
  - apply (req_trans (plus (opp A) (plus (opp B) B))
                     (plus (plus (opp A) (opp B)) B)
                     (plus (opp tt) B)).
    + exact (plus_assoc (opp A) (opp B) B).
    + apply (req_plus_compat (plus (opp A) (opp B)) (opp tt) B B
               (req_sym (opp tt) (plus (opp A) (opp B))
                  (req_trans (opp tt) (opp (plus A B))
                             (plus (opp A) (opp B))
                             (req_opp_compat tt (plus A B) H)
                             (req_opp_plus A B)))
               (req_refl B)).
Qed.

(* 0.8：x + h ≡ x·(1 + h·inv x)（x>0；复合换元母恒等） *)
Lemma lrdf_xh_eq : forall (x h : R) (Hx : lt zero x),
  req (plus x h) (mult x (plus one (mult h (inv_pos x Hx)))).
Proof.
  intros x h Hx.
  apply (req_sym (mult x (plus one (mult h (inv_pos x Hx)))) (plus x h)).
  apply (req_trans (mult x (plus one (mult h (inv_pos x Hx))))
                   (plus (mult x one) (mult x (mult h (inv_pos x Hx))))
                   (plus x h)).
  - exact (distrib x one (mult h (inv_pos x Hx))).
  - apply (req_trans (plus (mult x one) (mult x (mult h (inv_pos x Hx))))
                     (plus x (mult h (mult x (inv_pos x Hx))))
                     (plus x h)).
    + exact (req_plus_compat (mult x one) x (mult x (mult h (inv_pos x Hx)))
               (mult h (mult x (inv_pos x Hx)))
               (mult_one x)
               (req_trans (mult x (mult h (inv_pos x Hx)))
                          (mult (mult h x) (inv_pos x Hx))
                          (mult h (mult x (inv_pos x Hx)))
                          (req_trans (mult x (mult h (inv_pos x Hx)))
                                     (mult (mult x h) (inv_pos x Hx))
                                     (mult (mult h x) (inv_pos x Hx))
                                     (mult_assoc x h (inv_pos x Hx))
                                     (req_mult_compat (mult x h) (mult h x)
                                        (inv_pos x Hx) (inv_pos x Hx)
                                        (mult_comm x h) (req_refl (inv_pos x Hx))))
                          (req_sym (mult h (mult x (inv_pos x Hx)))
                                   (mult (mult h x) (inv_pos x Hx))
                                   (mult_assoc h x (inv_pos x Hx))))).
    + apply (req_plus_compat x x (mult h (mult x (inv_pos x Hx))) h
               (req_refl x)
               (req_trans (mult h (mult x (inv_pos x Hx))) (mult h one) h
                          (req_mult_compat h h (mult x (inv_pos x Hx)) one
                             (req_refl h) (inv_pos_correct x Hx))
                          (mult_one h))).
Qed.

(* 0.9：A ≡ s + (A − s)（minus 对拆） *)
Lemma lrdf_plus_minus : forall (A s : R),
  req A (plus s (req_minus A s)).
Proof.
  intros A s.
  apply (req_trans A (plus (req_minus A s) s) (plus s (req_minus A s))).
  - exact (req_rdf_minus_pair A s).
  - exact (plus_comm (req_minus A s) s).
Qed.

(* 0.10：s + u ≡ s·(1 + u·inv s)（s·inv ≡ 1 一般化换元母恒等） *)
Lemma lrdf_s_plus_eq : forall (s uu inv : R) (Hc : req (mult s inv) one),
  req (plus s uu) (mult s (plus one (mult uu inv))).
Proof.
  intros s uu inv Hc.
  apply (req_sym (mult s (plus one (mult uu inv))) (plus s uu)).
  apply (req_trans (mult s (plus one (mult uu inv)))
                   (plus (mult s one) (mult s (mult uu inv)))
                   (plus s uu)).
  - exact (distrib s one (mult uu inv)).
  - apply (req_trans (plus (mult s one) (mult s (mult uu inv)))
                     (plus s (mult uu (mult s inv)))
                     (plus s uu)).
    + exact (req_plus_compat (mult s one) s (mult s (mult uu inv))
               (mult uu (mult s inv))
               (mult_one s)
               (req_trans (mult s (mult uu inv))
                          (mult (mult s uu) inv)
                          (mult uu (mult s inv))
                          (mult_assoc s uu inv)
                          (req_trans (mult (mult s uu) inv)
                                     (mult (mult uu s) inv)
                                     (mult uu (mult s inv))
                                     (req_mult_compat (mult s uu) (mult uu s)
                                        inv inv (mult_comm s uu) (req_refl inv))
                                     (req_sym (mult uu (mult s inv))
                                              (mult (mult uu s) inv)
                                              (mult_assoc uu s inv))))).
    + exact (req_plus_compat s s (mult uu (mult s inv)) uu
               (req_refl s)
               (req_trans (mult uu (mult s inv)) (mult uu one) uu
                          (req_mult_compat uu uu (mult s inv) one
                             (req_refl uu) Hc)
                          (mult_one uu))).
Qed.

(* 0.11：(a·b)·inv ≡ a（b·inv ≡ 1 消去） *)
Lemma lrdf_mul_inv_one : forall (a b inv : R) (Hb : req (mult b inv) one),
  req (mult (mult a b) inv) a.
Proof.
  intros a b inv Hb.
  apply (req_trans (mult (mult a b) inv) (mult a (mult b inv)) a).
  - exact (req_sym (mult a (mult b inv)) (mult (mult a b) inv) (mult_assoc a b inv)).
  - apply (req_trans (mult a (mult b inv)) (mult a one) a).
    + exact (req_mult_compat a a (mult b inv) one (req_refl a) Hb).
    + exact (mult_one a).
Qed.

(* 0.11b：(a·b)·inv ≡ (a·inv)·b（同因子双换位；HB 尾链换元用） *)
Lemma lrdf_mul_h_inv : forall a b inv : R,
  req (mult (mult a b) inv) (mult (mult a inv) b).
Proof.
  intros a b inv.
  exact (req_trans (mult (mult a b) inv) (mult a (mult b inv))
                   (mult (mult a inv) b)
           (req_sym (mult a (mult b inv)) (mult (mult a b) inv)
              (mult_assoc a b inv))
           (req_trans (mult a (mult b inv)) (mult a (mult inv b))
                      (mult (mult a inv) b)
              (req_mult_compat a a (mult b inv) (mult inv b)
                 (req_refl a) (mult_comm b inv))
              (mult_assoc a inv b))).
Qed.

(* ============================================================ *)

(* ============================================================ *)

(* 1.1：环恒等 1 − inv(1+t) ≡ (t)·inv(1+t)（对标 real_succ_minus_one +       *)
(*      real_inv_minus_one_opp_noHt 组合内件） *)
Lemma lrdf_inner_one_opp_inv : forall (t : R) (Hs : lt zero (plus one t)),
  req (plus one (opp (inv_pos (plus one t) Hs)))
      (mult (plus (plus one t) (opp one)) (inv_pos (plus one t) Hs)).
Proof.
  intros t Hs.
  apply (req_trans (plus one (opp (inv_pos (plus one t) Hs)))
                   (plus (mult (plus one t) (inv_pos (plus one t) Hs))
                         (opp (mult (inv_pos (plus one t) Hs) one)))
                   (mult (plus (plus one t) (opp one)) (inv_pos (plus one t) Hs))).
  - exact (req_plus_compat one (mult (plus one t) (inv_pos (plus one t) Hs))
              (opp (inv_pos (plus one t) Hs))
              (opp (mult (inv_pos (plus one t) Hs) one))
              (req_sym (mult (plus one t) (inv_pos (plus one t) Hs)) one
                 (inv_pos_correct (plus one t) Hs))
              (req_opp_compat (inv_pos (plus one t) Hs)
                 (mult (inv_pos (plus one t) Hs) one)
                 (req_sym (mult (inv_pos (plus one t) Hs) one)
                          (inv_pos (plus one t) Hs)
                          (mult_one (inv_pos (plus one t) Hs))))).
  - apply (req_trans (plus (mult (plus one t) (inv_pos (plus one t) Hs))
                           (opp (mult (inv_pos (plus one t) Hs) one)))
                     (plus (mult (inv_pos (plus one t) Hs) (plus one t))
                           (mult (inv_pos (plus one t) Hs) (opp one)))
                     (mult (plus (plus one t) (opp one)) (inv_pos (plus one t) Hs))).
    + exact (req_plus_compat (mult (plus one t) (inv_pos (plus one t) Hs))
               (mult (inv_pos (plus one t) Hs) (plus one t))
               (opp (mult (inv_pos (plus one t) Hs) one))
               (mult (inv_pos (plus one t) Hs) (opp one))
               (mult_comm (plus one t) (inv_pos (plus one t) Hs))
               (req_sym (mult (inv_pos (plus one t) Hs) (opp one))
                        (opp (mult (inv_pos (plus one t) Hs) one))
                        (lrdf_mult_opp_r (inv_pos (plus one t) Hs) one))).
    + apply (req_trans (plus (mult (inv_pos (plus one t) Hs) (plus one t))
                             (mult (inv_pos (plus one t) Hs) (opp one)))
                       (mult (inv_pos (plus one t) Hs) (plus (plus one t) (opp one)))
                       (mult (plus (plus one t) (opp one)) (inv_pos (plus one t) Hs))).
      * exact (req_sym (mult (inv_pos (plus one t) Hs) (plus (plus one t) (opp one)))
                       (plus (mult (inv_pos (plus one t) Hs) (plus one t))
                             (mult (inv_pos (plus one t) Hs) (opp one)))
                       (distrib (inv_pos (plus one t) Hs) (plus one t) (opp one))).
      * exact (mult_comm (inv_pos (plus one t) Hs) (plus (plus one t) (opp one))).
Qed.

(* 1.2：环恒等 t + (inv(1+t) − 1) ≡ t²·inv(1+t)（对标 real_t_plus_inv_      *)
(*      minus_one@:44952；链 = req_set_inv_minus_one_opp@UpReqSLM 反向   *)
(*      + distrib + req_ld3_minus_one_plus_t） *)
Lemma lrdf_t_plus_inv_minus_one : forall (t : R) (Hs : lt zero (plus one t)),
  req (plus t (req_minus (inv_pos (plus one t) Hs) one))
      (mult (mult t t) (inv_pos (plus one t) Hs)).
Proof.
  intros t Hs.
  unfold req_minus.
  apply (req_trans (plus t (plus (inv_pos (plus one t) Hs) (opp one)))
                   (plus t (opp (mult t (inv_pos (plus one t) Hs))))
                   (mult (mult t t) (inv_pos (plus one t) Hs))).
  - apply (req_plus_compat t t (plus (inv_pos (plus one t) Hs) (opp one))
              (opp (mult t (inv_pos (plus one t) Hs)))
              (req_refl t)
              (req_trans (plus (inv_pos (plus one t) Hs) (opp one))
                         (opp (opp (plus (inv_pos (plus one t) Hs) (opp one))))
                         (opp (mult t (inv_pos (plus one t) Hs)))
                         (req_sym (opp (opp (plus (inv_pos (plus one t) Hs) (opp one))))
                                  (plus (inv_pos (plus one t) Hs) (opp one))
                                  (req_double_neg
                                     (plus (inv_pos (plus one t) Hs) (opp one))))
                         (req_sym (opp (mult t (inv_pos (plus one t) Hs)))
                                  (opp (opp (plus (inv_pos (plus one t) Hs) (opp one))))
                                  (req_opp_compat (mult t (inv_pos (plus one t) Hs))
                                     (opp (plus (inv_pos (plus one t) Hs) (opp one)))
                                     (req_trans (mult t (inv_pos (plus one t) Hs))
                                        (opp (req_minus (inv_pos (plus one t) Hs) one))
                                        (opp (plus (inv_pos (plus one t) Hs) (opp one)))
                                        (req_set_inv_minus_one_opp t Hs)
                                        (req_opp_compat (req_minus (inv_pos (plus one t) Hs) one)
                                           (plus (inv_pos (plus one t) Hs) (opp one))
                                           (lrdf_req_minus_unfold
                                              (inv_pos (plus one t) Hs) one))))))).
  - apply (req_trans (plus t (opp (mult t (inv_pos (plus one t) Hs))))
                     (plus (mult t one) (mult t (opp (inv_pos (plus one t) Hs))))
                     (mult (mult t t) (inv_pos (plus one t) Hs))).
    + exact (req_plus_compat t (mult t one)
               (opp (mult t (inv_pos (plus one t) Hs)))
               (mult t (opp (inv_pos (plus one t) Hs)))
               (req_sym (mult t one) t (mult_one t))
               (req_sym (mult t (opp (inv_pos (plus one t) Hs)))
                        (opp (mult t (inv_pos (plus one t) Hs)))
                        (lrdf_mult_opp_r t (inv_pos (plus one t) Hs)))).
    + apply (req_trans (plus (mult t one) (mult t (opp (inv_pos (plus one t) Hs))))
                       (mult t (plus one (opp (inv_pos (plus one t) Hs))))
                       (mult (mult t t) (inv_pos (plus one t) Hs))).
      * exact (req_sym (mult t (plus one (opp (inv_pos (plus one t) Hs))))
                       (plus (mult t one) (mult t (opp (inv_pos (plus one t) Hs))))
                       (distrib t one (opp (inv_pos (plus one t) Hs)))).
      * apply (req_trans (mult t (plus one (opp (inv_pos (plus one t) Hs))))
                         (mult t (mult (plus (plus one t) (opp one))
                                       (inv_pos (plus one t) Hs)))
                         (mult (mult t t) (inv_pos (plus one t) Hs))).
        -- apply (req_mult_compat t t
                     (plus one (opp (inv_pos (plus one t) Hs)))
                     (mult (plus (plus one t) (opp one)) (inv_pos (plus one t) Hs))
                     (req_refl t) (lrdf_inner_one_opp_inv t Hs)).
        -- apply (req_trans (mult t (mult (plus (plus one t) (opp one))
                                            (inv_pos (plus one t) Hs)))
                            (mult t (mult t (inv_pos (plus one t) Hs)))
                            (mult (mult t t) (inv_pos (plus one t) Hs))).
           ++ apply (req_mult_compat t t
                        (mult (plus (plus one t) (opp one)) (inv_pos (plus one t) Hs))
                        (mult t (inv_pos (plus one t) Hs))
                        (req_refl t)
                        (req_mult_compat (plus (plus one t) (opp one)) t
                           (inv_pos (plus one t) Hs) (inv_pos (plus one t) Hs)
                           (req_trans (plus (plus one t) (opp one))
                              (req_minus (plus one t) one)
                              t
                              (req_sym (plus (plus one t) (opp one))
                                 (req_minus (plus one t) one)
                                 (lrdf_req_minus_unfold (plus one t) one))
                              (req_ld3_minus_one_plus_t t))
                           (req_refl (inv_pos (plus one t) Hs)))).
           ++ exact (mult_assoc t t (inv_pos (plus one t) Hs)).
Qed.

(* 1.3：|t| < 1/2 ⟹ 1/2 ≤ 1+t（S1 槽 + 左 opp 消去 + one ≡ 1 − 1/2 链） *)
Lemma lrdf_half_le_one_t : forall t : R,
  lt (abs t) (inv_pos (plus one one) req_two_pos) ->
  le (inv_pos (plus one one) req_two_pos) (plus one t).
Proof.
  intros t Hlt.
  assert (Hle0 : le zero
    (plus (inv_pos (plus one one) req_two_pos) t)).
  { exact (lt_le_iff zero (plus (inv_pos (plus one one) req_two_pos) t)
             (inl (lrdf_abs_lower_pos t (inv_pos (plus one one) req_two_pos) Hlt))). }
  assert (Hcancel : req (plus (opp (inv_pos (plus one one) req_two_pos))
                              (plus (inv_pos (plus one one) req_two_pos) t))
                        t).
  { exact (lrdf_cancel_l_opp (inv_pos (plus one one) req_two_pos) t). }
  assert (Hoeq : le (opp (inv_pos (plus one one) req_two_pos)) t).
  { apply (le_id_l (opp (inv_pos (plus one one) req_two_pos))
                   (plus (opp (inv_pos (plus one one) req_two_pos)) zero) t
             (req_sym (plus (opp (inv_pos (plus one one) req_two_pos)) zero)
                      (opp (inv_pos (plus one one) req_two_pos))
                      (plus_zero (opp (inv_pos (plus one one) req_two_pos))))).
    apply (le_id_r (plus (opp (inv_pos (plus one one) req_two_pos)) zero)
                   (plus (opp (inv_pos (plus one one) req_two_pos))
                         (plus (inv_pos (plus one one) req_two_pos) t))
                   t
                   Hcancel).
    exact (le_plus_compat (opp (inv_pos (plus one one) req_two_pos))
                          (opp (inv_pos (plus one one) req_two_pos))
                          zero
                          (plus (inv_pos (plus one one) req_two_pos) t)
                          (le_refl (opp (inv_pos (plus one one) req_two_pos)))
                          Hle0). }
  assert (Hone : req (plus (inv_pos (plus one one) req_two_pos)
                           (inv_pos (plus one one) req_two_pos))
                     one).
  { exact (req_trans (plus (inv_pos (plus one one) req_two_pos)
                           (inv_pos (plus one one) req_two_pos))
                     (plus (mult (inv_pos (plus one one) req_two_pos) one)
                           (mult (inv_pos (plus one one) req_two_pos) one))
                     one
                     (req_plus_compat (inv_pos (plus one one) req_two_pos)
                        (mult (inv_pos (plus one one) req_two_pos) one)
                        (inv_pos (plus one one) req_two_pos)
                        (mult (inv_pos (plus one one) req_two_pos) one)
                        (req_sym (mult (inv_pos (plus one one) req_two_pos) one)
                                 (inv_pos (plus one one) req_two_pos)
                                 (mult_one (inv_pos (plus one one) req_two_pos)))
                        (req_sym (mult (inv_pos (plus one one) req_two_pos) one)
                                 (inv_pos (plus one one) req_two_pos)
                                 (mult_one (inv_pos (plus one one) req_two_pos))))
                     (req_half_twice one req_two_pos)). }
  assert (Hone' : req (plus one (opp (inv_pos (plus one one) req_two_pos)))
                      (inv_pos (plus one one) req_two_pos)).
  { apply (req_trans (plus one (opp (inv_pos (plus one one) req_two_pos)))
                     (plus (plus (inv_pos (plus one one) req_two_pos)
                                 (inv_pos (plus one one) req_two_pos))
                           (opp (inv_pos (plus one one) req_two_pos)))
                     (inv_pos (plus one one) req_two_pos)).
    - exact (req_plus_compat one
                (plus (inv_pos (plus one one) req_two_pos)
                      (inv_pos (plus one one) req_two_pos))
                (opp (inv_pos (plus one one) req_two_pos))
                (opp (inv_pos (plus one one) req_two_pos))
                (req_sym (plus (inv_pos (plus one one) req_two_pos)
                               (inv_pos (plus one one) req_two_pos))
                         one Hone)
                (req_refl (opp (inv_pos (plus one one) req_two_pos)))).
    - apply (req_trans (plus (plus (inv_pos (plus one one) req_two_pos)
                                   (inv_pos (plus one one) req_two_pos))
                             (opp (inv_pos (plus one one) req_two_pos)))
                       (plus (inv_pos (plus one one) req_two_pos)
                             (plus (inv_pos (plus one one) req_two_pos)
                                   (opp (inv_pos (plus one one) req_two_pos))))
                       (inv_pos (plus one one) req_two_pos)).
      + exact (req_sym (plus (inv_pos (plus one one) req_two_pos)
                             (plus (inv_pos (plus one one) req_two_pos)
                                   (opp (inv_pos (plus one one) req_two_pos))))
                       (plus (plus (inv_pos (plus one one) req_two_pos)
                                   (inv_pos (plus one one) req_two_pos))
                             (opp (inv_pos (plus one one) req_two_pos)))
                       (plus_assoc (inv_pos (plus one one) req_two_pos)
                                   (inv_pos (plus one one) req_two_pos)
                                   (opp (inv_pos (plus one one) req_two_pos)))).
      + apply (req_trans (plus (inv_pos (plus one one) req_two_pos)
                               (plus (inv_pos (plus one one) req_two_pos)
                                     (opp (inv_pos (plus one one) req_two_pos))))
                         (plus (inv_pos (plus one one) req_two_pos) zero)
                         (inv_pos (plus one one) req_two_pos)).
        * exact (req_plus_compat (inv_pos (plus one one) req_two_pos)
                    (inv_pos (plus one one) req_two_pos)
                    (plus (inv_pos (plus one one) req_two_pos)
                          (opp (inv_pos (plus one one) req_two_pos)))
                    zero
                    (req_refl (inv_pos (plus one one) req_two_pos))
                    (plus_opp (inv_pos (plus one one) req_two_pos))).
        * exact (plus_zero (inv_pos (plus one one) req_two_pos)). }
  exact (le_id_l (inv_pos (plus one one) req_two_pos)
                 (plus one (opp (inv_pos (plus one one) req_two_pos)))
                 (plus one t)
                 (req_sym (plus one (opp (inv_pos (plus one one) req_two_pos)))
                          (inv_pos (plus one one) req_two_pos)
                          Hone')
                 (le_plus_compat one one
                    (opp (inv_pos (plus one one) req_two_pos)) t
                    (le_refl one) Hoeq)).
Qed.

(* 1.4：核定理（缺件 A/B 共享）：0 < 1+t ∧ 1/2 ≤ 1+t ∧ |t| ≤ eps/2 ⟹          *)
(*      |log(1+t) − t| ≤ eps·|t|（主定理 X 双臂的无 eps 化）             *)
Lemma lrdf_core_abs_bound :
  forall (t eps : R)
    (H1t : lt zero (plus one t))
    (Hhalf : le (inv_pos (plus one one) req_two_pos) (plus one t))
    (Htb : le (abs t) (mult (inv_pos (plus one one) req_two_pos) eps))
    (Heps : lt zero eps),
    le (abs (plus (log (plus one t) H1t) (opp t))) (mult eps (abs t)).
Proof.
  intros t eps H1t Hhalf Htb Heps.
  assert (HA : le (plus (log (plus one t) H1t) (opp t)) zero).
  { apply (le_id_r (plus (log (plus one t) H1t) (opp t))
                   (plus t (opp t)) zero (plus_opp t)).
    apply (le_id_l (plus (log (plus one t) H1t) (opp t))
                   (plus (log (plus one t) H1t) (opp t))
                   (plus t (opp t))
                   (req_refl (plus (log (plus one t) H1t) (opp t)))).
    exact (le_plus_compat (log (plus one t) H1t) t (opp t) (opp t)
             (req_log_one_plus_le t H1t) (le_refl (opp t))). }
  assert (HA2 : le (plus (log (plus one t) H1t) (opp t)) (mult eps (abs t))).
  { exact (le_trans (plus (log (plus one t) H1t) (opp t)) zero (mult eps (abs t))
              HA (req_rdf_zero_le_mult_abs eps t Heps)). }
  assert (HreqX : req (opp (plus (log (plus one t) H1t) (opp t)))
                      (plus t (opp (log (plus one t) H1t)))).
  { exact (req_trans (opp (plus (log (plus one t) H1t) (opp t)))
                     (plus (opp (log (plus one t) H1t)) (opp (opp t)))
                     (plus t (opp (log (plus one t) H1t)))
                     (req_opp_plus (log (plus one t) H1t) (opp t))
                     (req_trans (plus (opp (log (plus one t) H1t)) (opp (opp t)))
                                (plus (opp (log (plus one t) H1t)) t)
                                (plus t (opp (log (plus one t) H1t)))
                                (req_plus_compat (opp (log (plus one t) H1t))
                                   (opp (log (plus one t) H1t))
                                   (opp (opp t)) t
                                   (req_refl (opp (log (plus one t) H1t)))
                                   (req_double_neg t))
                                (plus_comm (opp (log (plus one t) H1t)) t))). }
  assert (HC : le (plus t (opp (log (plus one t) H1t)))
                  (mult (mult t t) (inv_pos (plus one t) H1t))).
  { apply (le_trans (plus t (opp (log (plus one t) H1t)))
                    (plus t (log (inv_pos (plus one t) H1t)
                                 (inv_pos_pos (plus one t) H1t)))
                    (mult (mult t t) (inv_pos (plus one t) H1t))).
    - apply (le_plus_compat t t
               (opp (log (plus one t) H1t))
               (log (inv_pos (plus one t) H1t)
                    (inv_pos_pos (plus one t) H1t))
               (le_refl t)).
      exact (req_set_eq_le (opp (log (plus one t) H1t))
                           (log (inv_pos (plus one t) H1t)
                                (inv_pos_pos (plus one t) H1t))
                           (req_sym (log (inv_pos (plus one t) H1t)
                                      (inv_pos_pos (plus one t) H1t))
                                    (opp (log (plus one t) H1t))
                                    (req_log_inv_one_inv log_req_compat_plain
                                       (plus one t) H1t))).
    - apply (le_trans (plus t (log (inv_pos (plus one t) H1t)
                                   (inv_pos_pos (plus one t) H1t)))
                      (plus t (req_minus (inv_pos (plus one t) H1t) one))
                      (mult (mult t t) (inv_pos (plus one t) H1t))).
      + exact (le_plus_compat t t
                 (log (inv_pos (plus one t) H1t) (inv_pos_pos (plus one t) H1t))
                 (req_minus (inv_pos (plus one t) H1t) one)
                 (le_refl t)
                 (log_le_linear_plain (inv_pos (plus one t) H1t)
                    (inv_pos_pos (plus one t) H1t))).
      + apply (req_set_eq_le (plus t (req_minus (inv_pos (plus one t) H1t) one))
                             (mult (mult t t) (inv_pos (plus one t) H1t))).
        exact (lrdf_t_plus_inv_minus_one t H1t). }
  assert (HB1 : le (opp (plus (log (plus one t) H1t) (opp t)))
                   (mult (mult t t) (inv_pos (plus one t) H1t))).
  { exact (le_id_l (opp (plus (log (plus one t) H1t) (opp t)))
                   (plus t (opp (log (plus one t) H1t)))
                   (mult (mult t t) (inv_pos (plus one t) H1t))
                   HreqX HC). }
  assert (Hprem : le one (mult (plus one t) (plus one one))).
  { apply (le_id_l one
             (mult (inv_pos (plus one one) req_two_pos) (plus one one))
             (mult (plus one t) (plus one one))).
    - exact (req_sym (mult (inv_pos (plus one one) req_two_pos) (plus one one)) one
                       (req_trans (mult (inv_pos (plus one one) req_two_pos) (plus one one))
                       (mult (plus one one) (inv_pos (plus one one) req_two_pos))
                       one
                       (mult_comm (inv_pos (plus one one) req_two_pos) (plus one one))
                       (inv_pos_correct (plus one one) req_two_pos))).
    - exact (le_mult_compat (inv_pos (plus one one) req_two_pos) (plus one t)
               (plus one one) (req_two_pos) Hhalf). }
  assert (Hinvs2 : le (inv_pos (plus one t) H1t) (plus one one)).
  { exact (lrdf_inv_le_of_one_le_mul (plus one t) (plus one one) H1t Hprem). }
  assert (HD2 : le (mult (mult t t) (inv_pos (plus one t) H1t))
                   (mult (mult t t) (plus one one))).
  { apply (le_id_l (mult (mult t t) (inv_pos (plus one t) H1t))
                   (mult (inv_pos (plus one t) H1t) (mult t t))
                   (mult (mult t t) (plus one one))
                   (mult_comm (mult t t) (inv_pos (plus one t) H1t))).
    apply (le_id_r (mult (inv_pos (plus one t) H1t) (mult t t))
                   (mult (plus one one) (mult t t))
                   (mult (mult t t) (plus one one))
                   (mult_comm (plus one one) (mult t t))).
    exact (le_mult_compat_weak (inv_pos (plus one t) H1t) (plus one one) (mult t t)
             (lrdf_sq_nonneg t) Hinvs2). }
  assert (HH : le (mult t t)
                  (mult (abs t)
                    (mult (inv_pos (plus one one) req_two_pos) eps))).
  { exact (le_trans (mult t t) (mult (abs t) (abs t))
              (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps))
              (lrdf_sq_le_abs_sq t)
              (req_le_mult_compat_r (abs t) (abs t)
                 (mult (inv_pos (plus one one) req_two_pos) eps)
                 (abs_nonneg_plain t) Htb)). }
  assert (RING2 : req (mult (plus one one)
                            (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                     (mult eps (abs t))).
  { exact (req_trans (mult (plus one one) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps))) (mult (mult (plus one one) (abs t)) (mult (inv_pos (plus one one) req_two_pos) eps)) (mult eps (abs t)) (mult_assoc (plus one one) (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)) (req_trans (mult (mult (plus one one) (abs t)) (mult (inv_pos (plus one one) req_two_pos) eps)) (mult (mult (abs t) (plus one one)) (mult (inv_pos (plus one one) req_two_pos) eps)) (mult eps (abs t)) (req_mult_compat (mult (plus one one) (abs t))
                    (mult (abs t) (plus one one))
                    (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (plus one one) req_two_pos) eps)
                    (mult_comm (plus one one) (abs t))
                    (req_refl (mult (inv_pos (plus one one) req_two_pos) eps))) (req_trans (mult (mult (abs t) (plus one one)) (mult (inv_pos (plus one one) req_two_pos) eps)) (mult (abs t) (mult (plus one one) (mult (inv_pos (plus one one) req_two_pos) eps))) (mult eps (abs t)) (req_sym (mult (abs t) (mult (plus one one) (mult (inv_pos (plus one one) req_two_pos) eps)))
             (mult (mult (abs t) (plus one one)) (mult (inv_pos (plus one one) req_two_pos) eps))
             (mult_assoc (abs t) (plus one one) (mult (inv_pos (plus one one) req_two_pos) eps))) (req_trans (mult (abs t) (mult (plus one one) (mult (inv_pos (plus one one) req_two_pos) eps))) (mult (abs t) (mult (mult (plus one one) (inv_pos (plus one one) req_two_pos)) eps)) (mult eps (abs t)) (req_mult_compat (abs t) (abs t)
   (mult (plus one one) (mult (inv_pos (plus one one) req_two_pos) eps))
   (mult (mult (plus one one) (inv_pos (plus one one) req_two_pos)) eps)
   (req_refl (abs t))
   (mult_assoc (plus one one) (inv_pos (plus one one) req_two_pos) eps)) (req_trans (mult (abs t) (mult (mult (plus one one) (inv_pos (plus one one) req_two_pos)) eps)) (mult (abs t) (mult one eps)) (mult eps (abs t)) (req_mult_compat (abs t) (abs t)
   (mult (mult (plus one one) (inv_pos (plus one one) req_two_pos)) eps)
   (mult one eps)
   (req_refl (abs t))
   (req_mult_compat (mult (plus one one) (inv_pos (plus one one) req_two_pos)) one eps eps
      (inv_pos_correct (plus one one) req_two_pos)
      (req_refl eps))) (req_trans (mult (abs t) (mult one eps)) (mult (abs t) eps) (mult eps (abs t)) (req_mult_compat (abs t) (abs t)
   (mult one eps) eps
   (req_refl (abs t))
   (req_trans (mult one eps) (mult eps one) eps
      (mult_comm one eps) (mult_one eps))) (mult_comm (abs t) eps))))))). }
  assert (HD3 : le (mult (mult t t) (plus one one)) (mult eps (abs t))).
  { apply (le_id_l (mult (mult t t) (plus one one))
                   (plus (mult t t) (mult t t))
                   (mult eps (abs t))).
    apply (req_trans (mult (mult t t) (plus one one))
                     (mult (plus one one) (mult t t))
                     (plus (mult t t) (mult t t))
                     (mult_comm (mult t t) (plus one one))
                     (req_two_mult (mult t t))).
    apply (le_trans (plus (mult t t) (mult t t))
                    (plus (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps))
                          (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                    (mult eps (abs t))).
    - exact (le_plus_compat (mult t t) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps))
                            (mult t t) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps))
                            HH HH).
    - apply (le_id_r (plus (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                     (mult (plus one one) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                     (mult eps (abs t))).
      + exact RING2.
      + apply (le_id_l (plus (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                       (mult (plus one one) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                       (mult (plus one one) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))).
        * exact (req_sym (mult (plus one one) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                         (plus (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))
                         (req_two_mult (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))).
        * exact (le_refl (mult (plus one one) (mult (abs t) (mult (inv_pos (plus one one) req_two_pos) eps)))).
  }
  assert (HB2 : le (opp (plus (log (plus one t) H1t) (opp t)))
                   (mult eps (abs t))).
  { exact (le_trans (opp (plus (log (plus one t) H1t) (opp t)))
                    (mult (mult t t) (inv_pos (plus one t) H1t))
                    (mult eps (abs t)) HB1
                    (le_trans (mult (mult t t) (inv_pos (plus one t) H1t))
                              (mult (mult t t) (plus one one))
                              (mult eps (abs t)) HD2 HD3)). }
  exact (lrdf_abs_le_intro (plus (log (plus one t) H1t) (opp t))
           (mult eps (abs t)) HA2 HB2).
Qed.

(* ============================================================ *)

(*   df y := inv y；delta := min(x/2, (eps·x/2)·x)；                            *)
(*   上界 D ≤ 0（req_log_one_plus_le 精确切线）+ 下界 |D| ≤ 2t² ≤ eps·|h|。      *)
(* ============================================================ *)

Theorem lrdf_log_root : forall (Hpos : forall y : R, lt zero y),
  reqRDF (fun y : R => log y (Hpos y)).
Proof.
  intros Hpos.
  exists (fun y : R => inv_pos y (Hpos y)).
  intros x eps Heps.
  assert (Hx : lt zero x) by exact (Hpos x).
  assert (Hdl : lt zero (mult (inv_pos (plus one one) req_two_pos) x)).
  { exact (mult_positive (inv_pos (plus one one) req_two_pos) x (inv_pos_pos (plus one one) req_two_pos) Hx). }
  assert (Hepsx : lt zero (mult eps x)) by exact (mult_positive eps x Heps Hx).
  assert (Hdr : lt zero (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x)).
  { exact (mult_positive (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x
             (mult_positive (inv_pos (plus one one) req_two_pos) (mult eps x)
                (inv_pos_pos (plus one one) req_two_pos) Hepsx)
             Hx). }
  exists (min (mult (inv_pos (plus one one) req_two_pos) x)
              (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x)).
  split.
  - exact (min_pos (mult (inv_pos (plus one one) req_two_pos) x)
                   (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x) Hdl Hdr).
  - intros h Hh.
    assert (Hhl : lt (abs h) (mult (inv_pos (plus one one) req_two_pos) x)).
    { exact (lt_le_trans (abs h)
               (min (mult (inv_pos (plus one one) req_two_pos) x)
                    (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x))
               (mult (inv_pos (plus one one) req_two_pos) x)
               Hh (min_le_l_plain (mult (inv_pos (plus one one) req_two_pos) x)
                     (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x))). }
    assert (Hhr : lt (abs h) (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x)).
    { exact (lt_le_trans (abs h)
               (min (mult (inv_pos (plus one one) req_two_pos) x)
                    (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x))
               (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x)
               Hh (min_le_r_plain (mult (inv_pos (plus one one) req_two_pos) x)
                     (mult (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) x))). }
    assert (Ht2 : lt (abs (mult h (inv_pos x Hx))) (inv_pos (plus one one) req_two_pos)).
    { exact (lrdf_t_lt_of x h (inv_pos (plus one one) req_two_pos) Hx Hhl). }
    assert (Hte :
      lt (abs (mult h (inv_pos x Hx))) (mult (inv_pos (plus one one) req_two_pos) (mult eps x))).
    { exact (lrdf_t_lt_of x h (mult (inv_pos (plus one one) req_two_pos) (mult eps x)) Hx Hhr). }
    assert (H1t : lt zero (plus one (mult h (inv_pos x Hx)))).
    { exact (lrdf_abs_lower_pos (mult h (inv_pos x Hx)) one
               (lt_le_trans (abs (mult h (inv_pos x Hx))) (inv_pos (plus one one) req_two_pos) one
                  Ht2 req_rdf_half_le_one)). }
    assert (Hhalf : le (inv_pos (plus one one) req_two_pos) (plus one (mult h (inv_pos x Hx)))).
    { exact (lrdf_half_le_one_t (mult h (inv_pos x Hx)) Ht2). }
    assert (Hm : lt zero (mult x (plus one (mult h (inv_pos x Hx))))).
    { exact (mult_positive x (plus one (mult h (inv_pos x Hx))) Hx H1t). }
    assert (Hxh : lt zero (plus x h)).
    { exact (req_lt_compat zero zero
               (mult x (plus one (mult h (inv_pos x Hx)))) (plus x h)
               (req_refl zero)
               (req_sym (plus x h)
                  (mult x (plus one (mult h (inv_pos x Hx))))
                  (lrdf_xh_eq x h Hx))
               Hm). }
    assert (HEq : req (plus (log (plus x h) Hxh)
                            (opp (plus (log x Hx) (mult (inv_pos x Hx) h))))
                      (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                            (opp (mult h (inv_pos x Hx))))).
    { apply (req_trans (plus (log (plus x h) Hxh)
                             (opp (plus (log x Hx) (mult (inv_pos x Hx) h))))
                       (plus (log (plus x h) Hxh)
                             (plus (opp (log x Hx))
                                   (opp (mult (inv_pos x Hx) h))))
                       (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                             (opp (mult h (inv_pos x Hx))))).
      - exact (req_plus_compat (log (plus x h) Hxh) (log (plus x h) Hxh)
                 (opp (plus (log x Hx) (mult (inv_pos x Hx) h)))
                 (plus (opp (log x Hx)) (opp (mult (inv_pos x Hx) h)))
                 (req_refl (log (plus x h) Hxh))
                 (req_opp_plus (log x Hx) (mult (inv_pos x Hx) h))).
      - apply (req_trans (plus (log (plus x h) Hxh)
                               (plus (opp (log x Hx))
                                     (opp (mult (inv_pos x Hx) h))))
                         (plus (plus (log (plus x h) Hxh) (opp (log x Hx)))
                               (opp (mult (inv_pos x Hx) h)))
                         (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                               (opp (mult h (inv_pos x Hx))))).
        + exact (plus_assoc (log (plus x h) Hxh) (opp (log x Hx))
                            (opp (mult (inv_pos x Hx) h))).
        + apply (req_trans
                   (plus (plus (log (plus x h) Hxh) (opp (log x Hx)))
                         (opp (mult (inv_pos x Hx) h)))
                   (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                         (opp (mult (inv_pos x Hx) h)))
                   (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                         (opp (mult h (inv_pos x Hx))))).
          * apply (req_plus_compat
                     (plus (log (plus x h) Hxh) (opp (log x Hx)))
                     (log (plus one (mult h (inv_pos x Hx))) H1t)
                     (opp (mult (inv_pos x Hx) h))
                     (opp (mult (inv_pos x Hx) h))
                     (req_trans
                        (plus (log (plus x h) Hxh) (opp (log x Hx)))
                        (plus (log (mult x (plus one (mult h (inv_pos x Hx)))) Hm)
                              (opp (log x Hx)))
                        (log (plus one (mult h (inv_pos x Hx))) H1t)
                        (req_plus_compat (log (plus x h) Hxh)
                           (log (mult x (plus one (mult h (inv_pos x Hx)))) Hm)
                           (opp (log x Hx)) (opp (log x Hx))
                           (log_req_compat_plain (plus x h)
                              (mult x (plus one (mult h (inv_pos x Hx))))
                              Hxh Hm (lrdf_xh_eq x h Hx))
                           (req_refl (opp (log x Hx))))
                        (req_trans
                           (plus (log (mult x (plus one (mult h (inv_pos x Hx)))) Hm)
                                 (opp (log x Hx)))
                           (plus (plus (log x Hx)
                                       (log (plus one (mult h (inv_pos x Hx))) H1t))
                                 (opp (log x Hx)))
                           (log (plus one (mult h (inv_pos x Hx))) H1t)
                           (req_plus_compat
                              (log (mult x (plus one (mult h (inv_pos x Hx)))) Hm)
                              (plus (log x Hx)
                                    (log (plus one (mult h (inv_pos x Hx))) H1t))
                              (opp (log x Hx)) (opp (log x Hx))
                              (req_trans
                                 (log (mult x (plus one (mult h (inv_pos x Hx)))) Hm)
                                 (log (mult x (plus one (mult h (inv_pos x Hx))))
                                    (mult_positive x (plus one (mult h (inv_pos x Hx)))
                                       Hx H1t))
                                 (plus (log x Hx)
                                       (log (plus one (mult h (inv_pos x Hx))) H1t))
                                 (log_req_compat_plain
                                    (mult x (plus one (mult h (inv_pos x Hx))))
                                    (mult x (plus one (mult h (inv_pos x Hx)))) Hm
                                    (mult_positive x (plus one (mult h (inv_pos x Hx)))
                                       Hx H1t)
                                    (req_refl
                                       (mult x (plus one (mult h (inv_pos x Hx))))))
                                 (log_mult x (plus one (mult h (inv_pos x Hx))) Hx H1t))
                              (req_refl (opp (log x Hx))))
                           (lrdf_cancel_r (log x Hx)
                              (log (plus one (mult h (inv_pos x Hx))) H1t))))
                     (req_refl (opp (mult (inv_pos x Hx) h)))).
          * exact (req_plus_compat
                     (log (plus one (mult h (inv_pos x Hx))) H1t)
                     (log (plus one (mult h (inv_pos x Hx))) H1t)
                     (opp (mult (inv_pos x Hx) h))
                     (opp (mult h (inv_pos x Hx)))
                     (req_refl (log (plus one (mult h (inv_pos x Hx))) H1t))
                     (req_opp_compat (mult (inv_pos x Hx) h)
                        (mult h (inv_pos x Hx)) (mult_comm (inv_pos x Hx) h))). }
    assert (Hcore :
      le (abs (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                    (opp (mult h (inv_pos x Hx)))))
         (mult (mult eps x) (abs (mult h (inv_pos x Hx))))).
    { exact (lrdf_core_abs_bound (mult h (inv_pos x Hx)) (mult eps x)
               H1t Hhalf
               (lt_le_iff (abs (mult h (inv_pos x Hx)))
                  (mult (inv_pos (plus one one) req_two_pos) (mult eps x))
                  (inl Hte))
               Hepsx). }
    assert (Hscale :
      req (mult (mult eps x) (abs (mult h (inv_pos x Hx))))
          (mult eps (abs h))).
    { apply (req_trans (mult (mult eps x) (abs (mult h (inv_pos x Hx))))
                       (mult (mult eps x) (mult (abs h) (inv_pos x Hx)))
                       (mult eps (abs h))).
      - exact (req_mult_compat (mult eps x) (mult eps x)
                 (abs (mult h (inv_pos x Hx))) (mult (abs h) (inv_pos x Hx))
                 (req_refl (mult eps x))
                 (lrdf_t_abs_eq x h Hx)).
      - apply (req_trans (mult (mult eps x) (mult (abs h) (inv_pos x Hx)))
                         (mult eps (mult (abs h) (mult x (inv_pos x Hx))))
                         (mult eps (abs h))).
        + exact (req_trans (mult (mult eps x) (mult (abs h) (inv_pos x Hx)))
                           (mult eps (mult x (mult (abs h) (inv_pos x Hx))))
                           (mult eps (mult (abs h) (mult x (inv_pos x Hx))))
                           (req_sym (mult eps (mult x (mult (abs h) (inv_pos x Hx))))
                                    (mult (mult eps x) (mult (abs h) (inv_pos x Hx)))
                                    (mult_assoc eps x (mult (abs h) (inv_pos x Hx))))
                           (req_mult_compat eps eps
                              (mult x (mult (abs h) (inv_pos x Hx)))
                              (mult (abs h) (mult x (inv_pos x Hx)))
                              (req_refl eps)
                              (req_trans (mult x (mult (abs h) (inv_pos x Hx)))
                                 (mult (mult (abs h) (inv_pos x Hx)) x)
                                 (mult (abs h) (mult x (inv_pos x Hx)))
                                 (mult_comm x (mult (abs h) (inv_pos x Hx)))
                                 (req_trans (mult (mult (abs h) (inv_pos x Hx)) x)
                                    (mult (abs h) (mult (inv_pos x Hx) x))
                                    (mult (abs h) (mult x (inv_pos x Hx)))
                                    (req_sym (mult (abs h) (mult (inv_pos x Hx) x))
                                             (mult (mult (abs h) (inv_pos x Hx)) x)
                                             (mult_assoc (abs h) (inv_pos x Hx) x))
                                    (req_mult_compat (abs h) (abs h)
                                       (mult (inv_pos x Hx) x)
                                       (mult x (inv_pos x Hx))
                                       (req_refl (abs h))
                                       (mult_comm (inv_pos x Hx) x)))))).
        + apply (req_trans (mult eps (mult (abs h) (mult x (inv_pos x Hx))))
                           (mult eps (mult (abs h) one))
                           (mult eps (abs h))).
          * exact (req_mult_compat eps eps
                     (mult (abs h) (mult x (inv_pos x Hx)))
                     (mult (abs h) one)
                     (req_refl eps)
                     (req_mult_compat (abs h) (abs h)
                        (mult x (inv_pos x Hx)) one
                        (req_refl (abs h)) (inv_pos_correct x Hx))).
          * exact (req_mult_compat eps eps (mult (abs h) one) (abs h)
                     (req_refl eps) (mult_one (abs h))). }
    exact (le_id_l
             (abs (req_minus (log (plus x h) (Hpos (plus x h)))
                     (plus (log x (Hpos x)) (mult (inv_pos x (Hpos x)) h))))
             (abs (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                        (opp (mult h (inv_pos x Hx)))))
             (mult eps (abs h))
             (req_abs_compat
                (req_minus (log (plus x h) (Hpos (plus x h)))
                   (plus (log x (Hpos x)) (mult (inv_pos x (Hpos x)) h)))
                (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                      (opp (mult h (inv_pos x Hx))))
                (req_trans
                   (req_minus (log (plus x h) (Hpos (plus x h)))
                      (plus (log x (Hpos x)) (mult (inv_pos x (Hpos x)) h)))
                   (plus (log (plus x h) Hxh)
                         (opp (plus (log x Hx) (mult (inv_pos x Hx) h))))
                   (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                         (opp (mult h (inv_pos x Hx))))
                   (req_plus_compat
                      (log (plus x h) (Hpos (plus x h)))
                      (log (plus x h) Hxh)
                      (opp (plus (log x (Hpos x)) (mult (inv_pos x (Hpos x)) h)))
                      (opp (plus (log x Hx) (mult (inv_pos x Hx) h)))
                      (log_req_compat_plain (plus x h) (plus x h)
                         (Hpos (plus x h)) Hxh (req_refl (plus x h)))
                      (req_opp_compat
                         (plus (log x (Hpos x)) (mult (inv_pos x (Hpos x)) h))
                         (plus (log x Hx) (mult (inv_pos x Hx) h))
                         (req_plus_compat
                            (log x (Hpos x)) (log x Hx)
                            (mult (inv_pos x (Hpos x)) h) (mult (inv_pos x Hx) h)
                            (log_req_compat_plain x x (Hpos x) Hx (req_refl x))
                            (req_mult_compat (inv_pos x (Hpos x)) (inv_pos x Hx)
                               h h
                               (inv_pos_ext x x (Hpos x) Hx (req_refl x))
                               (req_refl h)))))
                   HEq))
             (le_id_r
                (abs (plus (log (plus one (mult h (inv_pos x Hx))) H1t)
                           (opp (mult h (inv_pos x Hx)))))
                (mult (mult eps x) (abs (mult h (inv_pos x Hx))))
                (mult eps (abs h)) Hscale Hcore)).
Qed.
(* ============================================================ *)


(*   df z := inv(g z)·dg z；tt := (g(z+h)−g z)·inv(g z)；                      *)
(*   误差 ≡ X + err·inv（lrdf_opp_split_eq 分裂）；budget 双 (eps/2)|h|。      *)
(* ============================================================ *)

Theorem lrdf_rdf_log_diff :
  forall (g : R -> R) (Hg : forall y : R, lt zero (g y)) (dg : reqRDF g),
    reqRDF (fun z : R => log (g z) (Hg z)).
Proof.
  intros g Hg dg.
  exists (fun z : R => mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)).
  intros z eps Heps.
  assert (Hs : lt zero (g z)) by exact (Hg z).
  assert (Hef : lt zero (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))).
  { exact (mult_positive (mult (inv_pos (plus one one) req_two_pos) eps) (g z)
             (req_rdf_half_pos eps Heps) Hs). }
  destruct (rdf_correct g dg z
              (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)) Hef)
    as [d1 [Hd1 Hd2]].
  assert (HK : lt zero
    (mult (plus (abs (rdf_df g dg z))
                (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)))
          (inv_pos (g z) (Hg z)))).
  { exact (mult_positive
             (plus (abs (rdf_df g dg z))
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)))
             (inv_pos (g z) (Hg z))
             (req_plus_le_lt_pos (abs (rdf_df g dg z))
                (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))
                (abs_nonneg_plain (rdf_df g dg z)) Hef)
             (inv_pos_pos (g z) (Hg z))). }
  assert (HKinv : lt zero
    (inv_pos (mult (plus (abs (rdf_df g dg z))
                       (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)))
                 (inv_pos (g z) (Hg z))) HK)).
  { exact (inv_pos_pos (mult (plus (abs (rdf_df g dg z))
                                 (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                       (g z)))
                            (inv_pos (g z) (Hg z))) HK). }
  assert (HepsX : lt zero
    (mult (mult (inv_pos (plus one one) req_two_pos) eps)
          (inv_pos (mult (plus (abs (rdf_df g dg z))
                             (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)))
                       (inv_pos (g z) (Hg z))) HK))).
  { exact (mult_positive (mult (inv_pos (plus one one) req_two_pos) eps)
             (inv_pos (mult (plus (abs (rdf_df g dg z))
                                (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                      (g z)))
                          (inv_pos (g z) (Hg z))) HK)
             (req_rdf_half_pos eps Heps) HKinv). }
  assert (Hda : lt zero
    (mult (mult (inv_pos (plus one one) req_two_pos)
                (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                      (inv_pos (mult (plus (abs (rdf_df g dg z))
                                         (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                               (g z)))
                                    (inv_pos (g z) (Hg z))) HK)))
                (inv_pos (mult (plus (abs (rdf_df g dg z))
                                   (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                         (g z)))
                              (inv_pos (g z) (Hg z))) HK))).
  { exact (mult_positive
             (mult (inv_pos (plus one one) req_two_pos)
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                         (inv_pos (mult (plus (abs (rdf_df g dg z))
                                            (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                  (g z)))
                                       (inv_pos (g z) (Hg z))) HK)))
             (inv_pos (mult (plus (abs (rdf_df g dg z))
                                (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                      (g z)))
                          (inv_pos (g z) (Hg z))) HK)
             (mult_positive (inv_pos (plus one one) req_two_pos)
                (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                      (inv_pos (mult (plus (abs (rdf_df g dg z))
                                         (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                               (g z)))
                                    (inv_pos (g z) (Hg z))) HK))
                (inv_pos_pos (plus one one) req_two_pos) HepsX)
             HKinv). }
  assert (Hdpos : lt zero
    (mult (inv_pos (plus one one) req_two_pos)
          (inv_pos (mult (plus (abs (rdf_df g dg z))
                             (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)))
                       (inv_pos (g z) (Hg z))) HK))).
  { exact (mult_positive (inv_pos (plus one one) req_two_pos)
             (inv_pos (mult (plus (abs (rdf_df g dg z))
                                (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                      (g z)))
                          (inv_pos (g z) (Hg z))) HK)
             (inv_pos_pos (plus one one) req_two_pos) HKinv). }
  exists (min (min d1
                  (mult (mult (inv_pos (plus one one) req_two_pos)
                              (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                    (inv_pos (mult (plus (abs (rdf_df g dg z))
                                                       (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                             (g z)))
                                                  (inv_pos (g z) (Hg z))) HK)))
                        (inv_pos (mult (plus (abs (rdf_df g dg z))
                                           (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                 (g z)))
                                      (inv_pos (g z) (Hg z))) HK)))
                  (mult (inv_pos (plus one one) req_two_pos)
                        (inv_pos (mult (plus (abs (rdf_df g dg z))
                                           (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                 (g z)))
                                      (inv_pos (g z) (Hg z))) HK))).
  split.
  - exact (min_pos (min d1
                       (mult (mult (inv_pos (plus one one) req_two_pos)
                                   (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                         (inv_pos (mult (plus (abs (rdf_df g dg z))
                                                            (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                                  (g z)))
                                                       (inv_pos (g z) (Hg z))) HK)))
                         (inv_pos (mult (plus (abs (rdf_df g dg z))
                                            (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                  (g z)))
                                       (inv_pos (g z) (Hg z))) HK)))
                   (mult (inv_pos (plus one one) req_two_pos)
                         (inv_pos (mult (plus (abs (rdf_df g dg z))
                                            (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                  (g z)))
                                       (inv_pos (g z) (Hg z))) HK))
                   (min_pos d1
                      (mult (mult (inv_pos (plus one one) req_two_pos)
                                  (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                        (inv_pos (mult (plus (abs (rdf_df g dg z))
                                                           (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                                 (g z)))
                                                      (inv_pos (g z) (Hg z))) HK)))
                        (inv_pos (mult (plus (abs (rdf_df g dg z))
                                           (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                 (g z)))
                                      (inv_pos (g z) (Hg z))) HK))
                      Hd1 Hda)
                   Hdpos).
  - intros h Hh.
    assert (Hh_d1 : lt (abs h) d1).
    { exact (lt_le_trans (abs h) (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) d1
               (lt_le_trans (abs h) (min (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                  Hh (min_le_l_plain (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))))
               (min_le_l_plain d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))). }
    assert (Hh_da : lt (abs h) (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))).
    { exact (lt_le_trans (abs h) (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
               (lt_le_trans (abs h) (min (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                  Hh (min_le_l_plain (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))))
               (min_le_r_plain d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))). }
    assert (Hh_dp : lt (abs h) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))).
    { exact (lt_le_trans (abs h) (min (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
               Hh (min_le_r_plain (min d1 (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))). }
    assert (He : le (abs (req_minus (g (plus z h)) (g z))) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (abs h))).
    { exact (req_rdf_delta_bound (g (plus z h)) (g z) (rdf_df g dg z)
               (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)) h (Hd2 h Hh_d1)). }

    assert (RINGKa : req (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))).
    { exact (req_trans (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                 (mult (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                 (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                 (mult_assoc (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                 (req_trans (mult (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                    (mult (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                    (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                    (req_mult_compat (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))) (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)
                       (mult_comm (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))) (req_refl (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                    (req_trans (mult (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                       (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                       (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                       (req_sym (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                          (mult (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                          (mult_assoc (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                       (req_trans (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                          (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) one)
                          (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                          (req_mult_compat (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) one
                             (req_refl (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))) (inv_pos_correct (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                          (mult_one (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))))))). }

    assert (RINGKd : req (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (plus one one) req_two_pos)).
    { exact (req_trans (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                 (mult (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (plus one one) req_two_pos)) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                 (inv_pos (plus one one) req_two_pos)
                 (mult_assoc (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                 (req_trans (mult (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (plus one one) req_two_pos)) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                    (mult (mult (inv_pos (plus one one) req_two_pos) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                    (inv_pos (plus one one) req_two_pos)
                    (req_mult_compat (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (plus one one) req_two_pos)) (mult (inv_pos (plus one one) req_two_pos) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)
                       (mult_comm (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (plus one one) req_two_pos)) (req_refl (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                    (req_trans (mult (mult (inv_pos (plus one one) req_two_pos) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                       (mult (inv_pos (plus one one) req_two_pos) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                       (inv_pos (plus one one) req_two_pos)
                       (req_sym (mult (inv_pos (plus one one) req_two_pos) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                          (mult (mult (inv_pos (plus one one) req_two_pos) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                          (mult_assoc (inv_pos (plus one one) req_two_pos) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                       (req_trans (mult (inv_pos (plus one one) req_two_pos) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                          (mult (inv_pos (plus one one) req_two_pos) one)
                          (inv_pos (plus one one) req_two_pos)
                          (req_mult_compat (inv_pos (plus one one) req_two_pos) (inv_pos (plus one one) req_two_pos) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) one
                             (req_refl (inv_pos (plus one one) req_two_pos)) (inv_pos_correct (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))
                          (mult_one (inv_pos (plus one one) req_two_pos)))))). }

    assert (HtK : le (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))).
    { exact (le_id_l (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                (mult (abs (req_minus (g (plus z h)) (g z))) (inv_pos (g z) (Hg z)))
                (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                (lrdf_t_abs_eq (g z) (req_minus (g (plus z h)) (g z)) (Hg z))
                (le_id_r (mult (abs (req_minus (g (plus z h)) (g z))) (inv_pos (g z) (Hg z)))
                   (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (abs h)) (inv_pos (g z) (Hg z)))
                   (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                   (req_trans (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (abs h)) (inv_pos (g z) (Hg z)))
                      (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (mult (abs h) (inv_pos (g z) (Hg z))))
                      (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                      (req_sym (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (mult (abs h) (inv_pos (g z) (Hg z))))
                         (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (abs h)) (inv_pos (g z) (Hg z)))
                         (mult_assoc (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (abs h) (inv_pos (g z) (Hg z))))
                      (req_trans (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (mult (abs h) (inv_pos (g z) (Hg z))))
                         (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (mult (inv_pos (g z) (Hg z)) (abs h)))
                         (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                         (req_mult_compat (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (mult (abs h) (inv_pos (g z) (Hg z))) (mult (inv_pos (g z) (Hg z)) (abs h))
                            (req_refl (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)))) (mult_comm (abs h) (inv_pos (g z) (Hg z))))
                         (mult_assoc (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)) (abs h))))
                   (le_mult_compat (abs (req_minus (g (plus z h)) (g z)))
                      (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (abs h)) (inv_pos (g z) (Hg z)) (inv_pos_pos (g z) (Hg z)) He))). }
    assert (Hb_core : le (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                        (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))).
    { exact (lt_le_iff (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
               (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
               (inl (lt_id_r (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                       (mult (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                       (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                       (req_trans (mult (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                          (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                          (mult_comm (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) RINGKa)
                       (le_lt_trans (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                          (mult (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                          (mult (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                          (le_id_r (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                             (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                             (mult (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                             (req_sym (mult (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                                (mult_comm (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))))
                             HtK)
                          (lt_mult_compat (abs h) (mult (mult (inv_pos (plus one one) req_two_pos) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK Hh_da))))). }
    assert (Hlt_i2 : lt (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) (inv_pos (plus one one) req_two_pos)).
    { exact (lt_id_r (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
               (mult (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
               (inv_pos (plus one one) req_two_pos)
               (req_trans (mult (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK))) (inv_pos (plus one one) req_two_pos)
                  (mult_comm (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) RINGKd)
               (le_lt_trans (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                  (mult (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                  (mult (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                  (le_id_r (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                     (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                     (mult (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                     (req_sym (mult (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                        (mult_comm (abs h) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))))
                     HtK)
                  (lt_mult_compat (abs h) (mult (inv_pos (plus one one) req_two_pos) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK Hh_dp))). }

    assert (Htt_split : req (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))) (plus (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h) (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))).
    { exact (req_trans (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))
                (mult (plus (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (mult (rdf_df g dg z) h)) (inv_pos (g z) (Hg z)))
                (plus (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h) (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                (req_mult_compat (req_minus (g (plus z h)) (g z)) (plus (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (mult (rdf_df g dg z) h)) (inv_pos (g z) (Hg z)) (inv_pos (g z) (Hg z))
                   (req_minus_split (g (plus z h)) (g z) (mult (rdf_df g dg z) h)) (req_refl (inv_pos (g z) (Hg z))))
                (req_trans (mult (plus (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (mult (rdf_df g dg z) h)) (inv_pos (g z) (Hg z)))
                   (mult (inv_pos (g z) (Hg z)) (plus (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (mult (rdf_df g dg z) h)))
                   (plus (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h) (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                   (mult_comm (plus (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (mult (rdf_df g dg z) h)) (inv_pos (g z) (Hg z)))
                   (req_trans (mult (inv_pos (g z) (Hg z)) (plus (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (mult (rdf_df g dg z) h)))
                      (plus (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (mult (inv_pos (g z) (Hg z)) (mult (rdf_df g dg z) h)))
                      (plus (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h) (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                      (distrib (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (mult (rdf_df g dg z) h))
                      (req_trans (plus (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (mult (inv_pos (g z) (Hg z)) (mult (rdf_df g dg z) h)))
                         (plus (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))
                         (plus (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h) (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                         (req_plus_compat (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (mult (inv_pos (g z) (Hg z)) (mult (rdf_df g dg z) h)) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)
                            (req_refl (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))) (mult_assoc (inv_pos (g z) (Hg z)) (rdf_df g dg z) h))
                         (plus_comm (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))))). }
    assert (H1t : lt zero (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))).
    { exact (lrdf_abs_lower_pos (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))) one
               (lt_le_trans (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                  (inv_pos (plus one one) req_two_pos) one Hlt_i2 req_rdf_half_le_one)). }
    assert (Hhalf : le (inv_pos (plus one one) req_two_pos)
                        (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))).
    { exact (lrdf_half_le_one_t (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))) Hlt_i2). }
    assert (Hprod : req (g (plus z h))
                        (mult (g z) (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))).
    { exact (req_trans (g (plus z h))
               (plus (g z) (req_minus (g (plus z h)) (g z)))
               (mult (g z) (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
               (lrdf_plus_minus (g (plus z h)) (g z))
               (lrdf_s_plus_eq (g z) (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))
                  (inv_pos_correct (g z) (Hg z)))). }
    assert (Hlogchain : req (plus (log (g (plus z h)) (Hg (plus z h))) (opp (log (g z) (Hg z))))
                            (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)).
    { exact (req_trans
               (plus (log (g (plus z h)) (Hg (plus z h))) (opp (log (g z) (Hg z))))
               (plus (log (mult (g z) (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                        (mult_positive (g z)
                           (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                           (Hg z) H1t))
                     (opp (log (g z) (Hg z))))
               (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
               (req_plus_compat (log (g (plus z h)) (Hg (plus z h)))
                  (log (mult (g z) (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                     (mult_positive (g z)
                        (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                        (Hg z) H1t))
                  (opp (log (g z) (Hg z))) (opp (log (g z) (Hg z)))
                  (log_req_compat_plain (g (plus z h))
                     (mult (g z) (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                     (Hg (plus z h))
                     (mult_positive (g z)
                        (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                        (Hg z) H1t)
                     Hprod)
                  (req_refl (opp (log (g z) (Hg z)))))
               (req_trans
                  (plus (log (mult (g z) (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                           (mult_positive (g z)
                              (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                              (Hg z) H1t))
                        (opp (log (g z) (Hg z))))
                  (plus (plus (log (g z) (Hg z))
                              (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t))
                        (opp (log (g z) (Hg z))))
                  (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                  (req_plus_compat
                     (log (mult (g z) (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                        (mult_positive (g z)
                           (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                           (Hg z) H1t))
                     (plus (log (g z) (Hg z))
                           (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t))
                     (opp (log (g z) (Hg z))) (opp (log (g z) (Hg z)))
                     (log_mult (g z)
                        (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                        (Hg z) H1t)
                     (req_refl (opp (log (g z) (Hg z)))))
                  (lrdf_cancel_r (log (g z) (Hg z))
                     (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)))). }
    assert (HEq : req (plus (log (g (plus z h)) (Hg (plus z h)))
                            (opp (plus (log (g z) (Hg z)) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))))
                      (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                                  (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                            (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))).
    { exact (req_trans
               (plus (log (g (plus z h)) (Hg (plus z h)))
                     (opp (plus (log (g z) (Hg z)) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))))
               (plus (log (g (plus z h)) (Hg (plus z h)))
                     (plus (opp (log (g z) (Hg z))) (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))))
               (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                           (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                     (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
               (req_plus_compat (log (g (plus z h)) (Hg (plus z h))) (log (g (plus z h)) (Hg (plus z h)))
                  (opp (plus (log (g z) (Hg z)) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
                  (plus (opp (log (g z) (Hg z))) (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
                  (req_refl (log (g (plus z h)) (Hg (plus z h))))
                  (req_opp_plus (log (g z) (Hg z)) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
               (req_trans
                  (plus (log (g (plus z h)) (Hg (plus z h)))
                        (plus (opp (log (g z) (Hg z))) (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))))
                  (plus (plus (log (g (plus z h)) (Hg (plus z h))) (opp (log (g z) (Hg z))))
                        (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
                  (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                              (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                        (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                  (plus_assoc (log (g (plus z h)) (Hg (plus z h))) (opp (log (g z) (Hg z)))
                     (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
                  (req_trans
                     (plus (plus (log (g (plus z h)) (Hg (plus z h))) (opp (log (g z) (Hg z))))
                           (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
                     (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                           (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
                     (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                                 (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                           (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                     (req_plus_compat
                        (plus (log (g (plus z h)) (Hg (plus z h))) (opp (log (g z) (Hg z))))
                        (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                        (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))
                        (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))
                        Hlogchain
                        (req_refl (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))))
                     (req_trans
                        (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                              (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))
                        (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                              (plus (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                                    (mult (inv_pos (g z) (Hg z))
                                          (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))))
                        (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                                    (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                              (mult (inv_pos (g z) (Hg z))
                                    (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                        (req_plus_compat
                           (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                           (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                           (opp (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))
                           (plus (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                                 (mult (inv_pos (g z) (Hg z))
                                       (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                           (req_refl (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t))
                           (lrdf_opp_split_eq (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)
                              (mult (inv_pos (g z) (Hg z))
                                    (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))
                              (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))
                              Htt_split))
                        (plus_assoc
                           (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                           (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))
                           (mult (inv_pos (g z) (Hg z))
                                 (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))))))). }
    assert (HX : le (abs (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                               (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))))
                    (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                (inv_pos (mult (plus (abs (rdf_df g dg z))
                                                   (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                                         (g z)))
                                              (inv_pos (g z) (Hg z))) HK))
                          (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))).
    { exact (lrdf_core_abs_bound (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))
               (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                     (inv_pos (mult (plus (abs (rdf_df g dg z))
                                        (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                                              (g z)))
                                 (inv_pos (g z) (Hg z))) HK))
               H1t Hhalf Hb_core HepsX). }
    assert (HX2 : le (abs (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t) (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))))
                     (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))).
    { exact (le_trans
                (abs (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t) (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))))
                (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                HX
                (le_trans
                   (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                   (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h)))
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                   (req_le_mult_compat_r (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (abs (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                      (lt_le_iff zero (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (inl HepsX)) HtK)
                   (le_id_l
                      (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h)))
                      (mult (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (abs h))
                      (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                      (mult_assoc (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (abs h))
                      (le_id_l
                         (mult (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (abs h))
                         (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))) (abs h))
                         (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                         (req_mult_compat (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                            (mult (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))))
                            (abs h) (abs h)
                            (req_sym (mult (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))))
                               (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                               (mult_assoc (mult (inv_pos (plus one one) req_two_pos) eps) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))))
                            (req_refl (abs h)))
                         (le_id_l
                            (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))) (abs h))
                            (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) one) (abs h))
                            (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                            (req_mult_compat
                               (mult (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))))
                               (mult (mult (inv_pos (plus one one) req_two_pos) eps) one)
                               (abs h) (abs h)
                               (req_mult_compat (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (plus one one) req_two_pos) eps) (mult (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) one
                                  (req_refl (mult (inv_pos (plus one one) req_two_pos) eps))
                                  (req_trans (mult (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z)))) (mult (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)) one
                                     (mult_comm (inv_pos (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK) (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))))
                                     (inv_pos_correct (mult (plus (abs (rdf_df g dg z)) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))) (inv_pos (g z) (Hg z))) HK)))
                               (req_refl (abs h)))
                            (le_id_l
                               (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) one) (abs h))
                               (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                               (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                               (req_mult_compat (mult (mult (inv_pos (plus one one) req_two_pos) eps) one)
                                  (mult (inv_pos (plus one one) req_two_pos) eps)
                                  (abs h) (abs h)
                                  (mult_one (mult (inv_pos (plus one one) req_two_pos) eps))
                                  (req_refl (abs h)))
                               (le_refl (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))))))))). }
    assert (HB : le (abs (mult (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (inv_pos (g z) (Hg z))))
                    (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))).
    { exact (le_id_l
                (abs (mult (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (inv_pos (g z) (Hg z))))
                (mult (abs (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (inv_pos (g z) (Hg z)))
                (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                (lrdf_t_abs_eq (g z) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (Hg z))
                (le_trans
                   (mult (abs (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (inv_pos (g z) (Hg z)))
                   (mult (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)) (abs h))
                         (inv_pos (g z) (Hg z)))
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                   (le_mult_compat (abs (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))
                      (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)) (abs h))
                      (inv_pos (g z) (Hg z)) (inv_pos_pos (g z) (Hg z)) (Hd2 h Hh_d1))
                   (le_id_l
                      (mult (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z)) (abs h))
                            (inv_pos (g z) (Hg z)))
                      (mult (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))
                                  (inv_pos (g z) (Hg z)))
                            (abs h))
                      (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                      (lrdf_mul_h_inv (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))
                         (abs h) (inv_pos (g z) (Hg z)))
                      (le_id_l
                         (mult (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))
                                     (inv_pos (g z) (Hg z)))
                               (abs h))
                         (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                         (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                         (req_mult_compat
                            (mult (mult (mult (inv_pos (plus one one) req_two_pos) eps) (g z))
                                  (inv_pos (g z) (Hg z)))
                            (mult (inv_pos (plus one one) req_two_pos) eps)
                            (abs h) (abs h)
                            (lrdf_mul_inv_one (mult (inv_pos (plus one one) req_two_pos) eps) (g z)
                               (inv_pos (g z) (Hg z)) (inv_pos_correct (g z) (Hg z)))
                            (req_refl (abs h)))
                         (le_refl (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))))))). }
    exact (le_id_l
              (abs (plus (log (g (plus z h)) (Hg (plus z h)))
                         (opp (plus (log (g z) (Hg z)) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h)))))
              (abs (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                               (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                         (mult (inv_pos (g z) (Hg z))
                               (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))))
              (mult eps (abs h))
              (req_abs_compat
                 (plus (log (g (plus z h)) (Hg (plus z h)))
                       (opp (plus (log (g z) (Hg z)) (mult (mult (inv_pos (g z) (Hg z)) (rdf_df g dg z)) h))))
                 (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                             (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                       (mult (inv_pos (g z) (Hg z))
                             (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                 HEq)
              (le_trans
                 (abs (plus (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                                  (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                            (mult (inv_pos (g z) (Hg z))
                                  (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))))
                 (plus (abs (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                                  (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))))
                       (abs (mult (inv_pos (g z) (Hg z))
                                  (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))))
                 (mult eps (abs h))
                 (req_rdf_abs_triangle
                    (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                          (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))))
                    (mult (inv_pos (g z) (Hg z))
                          (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                 (le_trans
                    (plus (abs (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t)
                                     (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))))
                          (abs (mult (inv_pos (g z) (Hg z))
                                     (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))))
                    (plus (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                          (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h)))
                    (mult eps (abs h))
                    (le_plus_compat (abs (plus (log (plus one (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z)))) H1t) (opp (mult (req_minus (g (plus z h)) (g z)) (inv_pos (g z) (Hg z))))))
                       (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                       (abs (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                       (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h)) HX2 (le_id_l (abs (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))))) (abs (mult (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (inv_pos (g z) (Hg z)))) (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                       (req_abs_compat (mult (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))) (mult (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h))) (inv_pos (g z) (Hg z)))
                          (mult_comm (inv_pos (g z) (Hg z)) (req_minus (g (plus z h)) (plus (g z) (mult (rdf_df g dg z) h)))))
                       HB))
                    (le_id_l (plus (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                                   (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h)))
                       (mult eps (abs h)) (mult eps (abs h))
                       (req_trans (plus (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                                        (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h)))
                                  (plus (mult (inv_pos (plus one one) req_two_pos) (mult eps (abs h)))
                                        (mult (inv_pos (plus one one) req_two_pos) (mult eps (abs h))))
                                  (mult eps (abs h))
                                  (req_plus_compat (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                                     (mult (inv_pos (plus one one) req_two_pos) (mult eps (abs h)))
                                     (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                                     (mult (inv_pos (plus one one) req_two_pos) (mult eps (abs h)))
                                     (req_sym (mult (inv_pos (plus one one) req_two_pos) (mult eps (abs h)))
                                        (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                                        (mult_assoc (inv_pos (plus one one) req_two_pos) eps (abs h)))
                                     (req_sym (mult (inv_pos (plus one one) req_two_pos) (mult eps (abs h)))
                                        (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                                        (mult_assoc (inv_pos (plus one one) req_two_pos) eps (abs h))))
                                  (req_half_twice (mult eps (abs h)) req_two_pos))
                       (le_refl (mult eps (abs h))))))).
Qed.

End LRDF.
