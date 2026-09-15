(* ============================================================ *)
(* UpEntropyGainReq.v *)
(* *)
(* 目的： 熵增益族的 req 抽象载体镜像件。 *)
(* 主件： req_entropy_gain_positive / req_second_law_quant 及 req 形逐步差分引理族。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist。 *)
(* 备注： Id 层陈述经假设位承接逐 eps 化；各 Variable 前提逐位保留。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpEntropyGainReq.v — 签名迁移批 4 第二席：UpEntropyGain 的    *)
(*   req 伴件（11 件）                                           *)
(*   母件：attn\UpEntropyGain.v（榜 A2 second_law_irreversible    *)
(*   升级件，2026-09-07）；规划书批 4「模块伴件」                 *)
(*   伴件形态：req_* 独立伴 Section，与母件同树（attn 目录）      *)
(* -------------------------------------------------------------- *)
(* 覆盖核对（req 件名 -> 母件 Id 原件 @ 行号；件数规则：陈述含 Id  *)
(* 或证明核为 Id 搬运的声明，Variable 假设位计入；grep 实测 11    *)
(* 声明 = 4 件 Id 陈述引理 + 1 件 Id 假设位 + 6 件 Id 搬运定理；  *)
(* 规划书约 10，实测 11，全数结果零冻结）：                        *)
(*   件 1  req 假设位 req_dynamics_gradient_step <- 母件 L64      *)
(*   件 2  req_eg_minus_def                      <- 母件 L84（δ 件）*)
(*   件 3  req_eg_minus_plus_cancel              <- 母件 L88      *)
(*   件 4  req_eg_step_diff                      <- 母件 L99      *)
(*   件 5  req_eg_step_neg_diff                  <- 母件 L115     *)
(*   件 6  req_eg_minus_pos                      <- 母件 L131     *)
(*   件 7  req_eg_tangent_shift                  <- 母件 L141     *)
(*   件 8  req_eg_grad_lower                     <- 母件 L228     *)
(*   件 9  req_entropy_step_gain_lower           <- 母件 L327（旗舰一） *)
(*   件 10 req_entropy_gain_positive             <- 母件 L379     *)
(*   件 11 req_second_law_quant                  <- 母件 L409（旗舰二） *)
(* -------------------------------------------------------------- *)
(* 诚实接口注记（假设位逐位保留，零放大）：                        *)
(*   - gradient_lipschitz / entropy_tangent：le 陈述、零 Id 内容， *)
(*     仅 minus→req_minus 同形平移（母件 L68/L71 同位）。          *)
(*   - abs_ge_value：母件 L76 同位；setoid 接口无 le a (abs a)     *)
(*     字段（仅逐 eps abs_nonneg），假设位原样保留。               *)
(*   - lt_plus_compat_lt_le：母件 L78 同位；setoid 接口仅          *)
(*     strict-strict lt_plus_compat 字段，假设位原样保留。         *)
(*   - 件 2 为 δ 件：req_minus 定义性展开（批 1 登记表 1 同位）。    *)
(* 非平凡性分级：件 8 = A+（本文件最长 req 链，(i)-(vi) 六段全     *)
(*   req 运输）；件 4/5/7/9/11 = A（多跳 req 链真证）；件 3/6 =    *)
(*   A-（短链）；件 10 = B（级联装配）；件 2 = δ 平凡；件 1 =      *)
(*   假设位迁移。                                                  *)
(* 纪律：纯 term-mode（零 rewrite/零 Morphisms）；语句全 Set 层    *)
(*   （req/le/lt 皆接口 Set 字段，零 Prop 泄露）；全 Qed 完成。    *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Import RealInterfaceEnhancedMod.

Section EntropyGainReq.

Context {R : Set}.
Context {RIS : RealInterfaceEnhancedSetoid R}.

Let zero := @zero R RIS.
Let one := @one R RIS.
Let plus := @plus R RIS.
Let mult := @mult R RIS.
Let opp := @opp R RIS.
Let abs := @abs R RIS.
Let lt := @lt R RIS.
Let le := @le R RIS.

(* ===== 诚实接口（母件 L59-79 同位 req 化） ===== *)
Variable entropy : R -> R.
Variable entropy_gradient : R -> R.
Variable dynamics : R -> R.
Variable eta : R.
Variable eta_pos : lt zero eta.

(* 件 1：母件 L64 dynamics_gradient_step 的 req 同形（假设位逐位保留） *)
Variable req_dynamics_gradient_step : forall x : R,
  req (dynamics x) (plus x (mult eta (entropy_gradient x))).

Variable L : R.
Variable L_pos : lt zero L.
(* le 陈述零 Id 内容，minus→req_minus 同形平移（母件 L68 同位） *)
Variable gradient_lipschitz : forall x y : R,
  le (abs (req_minus (entropy_gradient x) (entropy_gradient y)))
     (mult L (abs (req_minus x y))).
(* le 陈述零 Id 内容，minus→req_minus 同形平移（母件 L71 同位） *)
Variable entropy_tangent : forall x y : R,
  le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (req_minus y x))).
(* 母件 L76 同位：setoid 接口无 le a (abs a) 字段，假设位保留 *)
Variable abs_ge_value : forall a : R, le a (abs a).
(* 母件 L78 同位：setoid 接口仅 strict-strict 字段，假设位保留 *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* ===== 件 2：减法 δ 件（req_minus 定义性展开；母件 L84 id_refl 同位） ===== *)
Lemma req_eg_minus_def : forall a b : R, req (req_minus a b) (plus a (opp b)).
Proof.
  intros a b. unfold req_minus.
  exact (req_refl (plus a (opp b))).
Qed.

(* ===== 件 3：减法可逆（母件 L88 链逐处换 req 字段） ===== *)
Lemma req_eg_minus_plus_cancel : forall a b : R,
  req (plus (req_minus a b) b) a.
Proof.
  intros a b. unfold req_minus.
  apply (req_trans (plus (plus a (opp b)) b) (plus a (plus (opp b) b)) a).
  - exact (req_sym (plus a (plus (opp b) b)) (plus (plus a (opp b)) b)
                   (plus_assoc a (opp b) b)).
  - apply (req_trans (plus a (plus (opp b) b)) (plus a (plus b (opp b))) a).
    + exact (req_plus_compat a a (plus (opp b) b) (plus b (opp b))
                             (req_refl a) (plus_comm (opp b) b)).
    + apply (req_trans (plus a (plus b (opp b))) (plus a zero) a).
      * exact (req_plus_compat a a (plus b (opp b)) zero
                               (req_refl a) (plus_opp b)).
      * apply plus_zero.
Qed.

(* ===== 件 4：K0 单步展开（母件 L99 七跳链逐处换 req 字段） ===== *)
Lemma req_eg_step_diff : forall x : R,
  req (req_minus (dynamics x) x) (mult eta (entropy_gradient x)).
Proof.
  intros x. unfold req_minus.
  apply (req_trans (plus (dynamics x) (opp x))
                   (plus (plus x (mult eta (entropy_gradient x))) (opp x))
                   (mult eta (entropy_gradient x))).
  - exact (req_plus_compat (dynamics x)
                           (plus x (mult eta (entropy_gradient x)))
                           (opp x) (opp x)
                           (req_dynamics_gradient_step x) (req_refl (opp x))).
  - apply (req_trans (plus (plus x (mult eta (entropy_gradient x))) (opp x))
                     (plus x (plus (mult eta (entropy_gradient x)) (opp x)))
                     (mult eta (entropy_gradient x))).
    + exact (req_sym (plus x (plus (mult eta (entropy_gradient x)) (opp x)))
                     (plus (plus x (mult eta (entropy_gradient x))) (opp x))
                     (plus_assoc x (mult eta (entropy_gradient x)) (opp x))).
    + apply (req_trans (plus x (plus (mult eta (entropy_gradient x)) (opp x)))
                       (plus x (plus (opp x) (mult eta (entropy_gradient x))))
                       (mult eta (entropy_gradient x))).
      * exact (req_plus_compat x x
                               (plus (mult eta (entropy_gradient x)) (opp x))
                               (plus (opp x) (mult eta (entropy_gradient x)))
                               (req_refl x)
                               (plus_comm (mult eta (entropy_gradient x)) (opp x))).
      * apply (req_trans (plus x (plus (opp x) (mult eta (entropy_gradient x))))
                         (plus (plus x (opp x)) (mult eta (entropy_gradient x)))
                         (mult eta (entropy_gradient x))).
        -- exact (plus_assoc x (opp x) (mult eta (entropy_gradient x))).
        -- apply (req_trans (plus (plus x (opp x)) (mult eta (entropy_gradient x)))
                            (plus zero (mult eta (entropy_gradient x)))
                            (mult eta (entropy_gradient x))).
           ++ exact (req_plus_compat (plus x (opp x)) zero
                                     (mult eta (entropy_gradient x))
                                     (mult eta (entropy_gradient x))
                                     (plus_opp x)
                                     (req_refl (mult eta (entropy_gradient x)))).
           ++ apply (req_trans (plus zero (mult eta (entropy_gradient x)))
                               (plus (mult eta (entropy_gradient x)) zero)
                               (mult eta (entropy_gradient x))).
              ** exact (plus_comm zero (mult eta (entropy_gradient x))).
              ** apply plus_zero.
Qed.

(* ===== 件 5：K0' 反向差（母件 L115 六跳链逐处换 req 字段） ===== *)
Lemma req_eg_step_neg_diff : forall x : R,
  req (req_minus x (dynamics x)) (opp (mult eta (entropy_gradient x))).
Proof.
  intros x. unfold req_minus.
  apply (req_trans (plus x (opp (dynamics x)))
                   (plus x (opp (plus x (mult eta (entropy_gradient x)))))
                   (opp (mult eta (entropy_gradient x)))).
  - exact (req_plus_compat x x (opp (dynamics x))
                              (opp (plus x (mult eta (entropy_gradient x))))
                              (req_refl x)
                              (req_opp_compat (dynamics x)
                                              (plus x (mult eta (entropy_gradient x)))
                                              (req_dynamics_gradient_step x))).
  - apply (req_trans (plus x (opp (plus x (mult eta (entropy_gradient x)))))
                     (plus x (plus (opp x) (opp (mult eta (entropy_gradient x)))))
                     (opp (mult eta (entropy_gradient x)))).
    + exact (req_plus_compat x x (opp (plus x (mult eta (entropy_gradient x))))
                                (plus (opp x) (opp (mult eta (entropy_gradient x))))
                                (req_refl x)
                                (req_opp_plus x (mult eta (entropy_gradient x)))).
    + apply (req_trans (plus x (plus (opp x) (opp (mult eta (entropy_gradient x)))))
                       (plus (plus x (opp x)) (opp (mult eta (entropy_gradient x))))
                       (opp (mult eta (entropy_gradient x)))).
      * exact (plus_assoc x (opp x) (opp (mult eta (entropy_gradient x)))).
      * apply (req_trans (plus (plus x (opp x)) (opp (mult eta (entropy_gradient x))))
                         (plus zero (opp (mult eta (entropy_gradient x))))
                         (opp (mult eta (entropy_gradient x)))).
        -- exact (req_plus_compat (plus x (opp x)) zero
                                  (opp (mult eta (entropy_gradient x)))
                                  (opp (mult eta (entropy_gradient x)))
                                  (plus_opp x)
                                  (req_refl (opp (mult eta (entropy_gradient x))))).
        -- apply (req_trans (plus zero (opp (mult eta (entropy_gradient x))))
                            (plus (opp (mult eta (entropy_gradient x))) zero)
                            (opp (mult eta (entropy_gradient x)))).
           ++ exact (plus_comm zero (opp (mult eta (entropy_gradient x)))).
           ++ apply plus_zero.
Qed.

(* ===== 件 6：严格减正（母件 L131；req 接口 lt_id_l 字段直引） ===== *)
Lemma req_eg_minus_pos : forall u v : R, lt u v -> lt zero (req_minus v u).
Proof.
  intros u v Huv. unfold req_minus.
  apply (lt_id_l zero (plus u (opp u)) (plus v (opp u))
                 (req_sym (plus u (opp u)) zero (plus_opp u))).
  apply (lt_plus_compat_lt_le u v (opp u) (opp u) Huv (le_refl (opp u))).
Qed.

(* ===== 件 7：核 A 切线反向（母件 L141 三段装配逐处换 req 字段） ===== *)
Lemma req_eg_tangent_shift : forall x : R,
  le (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
     (req_minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x.
  pose proof (entropy_tangent (dynamics x) x) as Ht.
  (* 段 A：切线换形 le e (e' − W)，W := g'·(η·g)（req 接口 le_id_r 字段） *)
  assert (Ht1 : le (entropy x)
                   (plus (entropy (dynamics x))
                         (opp (mult (entropy_gradient (dynamics x))
                                    (mult eta (entropy_gradient x)))))).
  { apply (le_id_r (entropy x)
                   (plus (entropy (dynamics x))
                         (mult (entropy_gradient (dynamics x))
                               (req_minus x (dynamics x))))
                   (plus (entropy (dynamics x))
                         (opp (mult (entropy_gradient (dynamics x))
                                    (mult eta (entropy_gradient x)))))).
    - exact (req_plus_compat
                (entropy (dynamics x)) (entropy (dynamics x))
                (mult (entropy_gradient (dynamics x)) (req_minus x (dynamics x)))
                (opp (mult (entropy_gradient (dynamics x))
                           (mult eta (entropy_gradient x))))
                (req_refl (entropy (dynamics x)))
                (req_trans
                   (mult (entropy_gradient (dynamics x)) (req_minus x (dynamics x)))
                   (mult (entropy_gradient (dynamics x))
                         (opp (mult eta (entropy_gradient x))))
                   (opp (mult (entropy_gradient (dynamics x))
                              (mult eta (entropy_gradient x))))
                   (req_mult_compat (entropy_gradient (dynamics x))
                                    (entropy_gradient (dynamics x))
                                    (req_minus x (dynamics x))
                                    (opp (mult eta (entropy_gradient x)))
                                    (req_refl (entropy_gradient (dynamics x)))
                                    (req_eg_step_neg_diff x))
                   (req_opp_mult_l (entropy_gradient (dynamics x))
                                   (mult eta (entropy_gradient x))))).
    - exact Ht. }
  (* 段 B：移项 le (e + W) e'（le_plus_compat + req_eg_minus_plus_cancel 完成） *)
  assert (Ht2 : le (plus (entropy x)
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (entropy (dynamics x))).
  { pose proof (le_plus_compat
                   (entropy x)
                   (plus (entropy (dynamics x))
                         (opp (mult (entropy_gradient (dynamics x))
                                    (mult eta (entropy_gradient x)))))
                   (mult (entropy_gradient (dynamics x))
                         (mult eta (entropy_gradient x)))
                   (mult (entropy_gradient (dynamics x))
                         (mult eta (entropy_gradient x)))
                   Ht1
                   (le_refl (mult (entropy_gradient (dynamics x))
                                  (mult eta (entropy_gradient x))))) as Hadd.
    apply (le_id_r (plus (entropy x)
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (plus (plus (entropy (dynamics x))
                               (opp (mult (entropy_gradient (dynamics x))
                                          (mult eta (entropy_gradient x)))))
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (entropy (dynamics x))).
    - exact (req_eg_minus_plus_cancel (entropy (dynamics x))
                                      (mult (entropy_gradient (dynamics x))
                                            (mult eta (entropy_gradient x)))).
    - exact Hadd. }
  (* 段 C：加 opp e 提取 le W (e' − e)（req 接口 le_id_l 字段） *)
  assert (Hrot : req (plus (plus (entropy x)
                                 (mult (entropy_gradient (dynamics x))
                                       (mult eta (entropy_gradient x))))
                           (opp (entropy x)))
                     (mult (entropy_gradient (dynamics x))
                           (mult eta (entropy_gradient x)))).
  { apply (req_trans
              (plus (plus (entropy x)
                          (mult (entropy_gradient (dynamics x))
                                (mult eta (entropy_gradient x))))
                    (opp (entropy x)))
              (plus (plus (entropy x) (opp (entropy x)))
                    (mult (entropy_gradient (dynamics x))
                          (mult eta (entropy_gradient x))))
              (mult (entropy_gradient (dynamics x))
                    (mult eta (entropy_gradient x)))).
    - exact (reqd_plus_rot (entropy x)
                           (mult (entropy_gradient (dynamics x))
                                 (mult eta (entropy_gradient x)))
                           (opp (entropy x))).
    - apply (req_trans
                (plus (plus (entropy x) (opp (entropy x)))
                      (mult (entropy_gradient (dynamics x))
                            (mult eta (entropy_gradient x))))
                (plus zero (mult (entropy_gradient (dynamics x))
                                 (mult eta (entropy_gradient x))))
                (mult (entropy_gradient (dynamics x))
                      (mult eta (entropy_gradient x)))).
      + exact (req_plus_compat (plus (entropy x) (opp (entropy x))) zero
                               (mult (entropy_gradient (dynamics x))
                                     (mult eta (entropy_gradient x)))
                               (mult (entropy_gradient (dynamics x))
                                     (mult eta (entropy_gradient x)))
                               (plus_opp (entropy x))
                               (req_refl (mult (entropy_gradient (dynamics x))
                                               (mult eta (entropy_gradient x))))).
      + exact (req_trans (plus zero (mult (entropy_gradient (dynamics x))
                                          (mult eta (entropy_gradient x))))
                         (plus (mult (entropy_gradient (dynamics x))
                                     (mult eta (entropy_gradient x))) zero)
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x)))
                         (plus_comm zero (mult (entropy_gradient (dynamics x))
                                               (mult eta (entropy_gradient x))))
                         (plus_zero (mult (entropy_gradient (dynamics x))
                                          (mult eta (entropy_gradient x))))). }
  apply (le_id_l (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
                 (plus (plus (entropy x)
                             (mult (entropy_gradient (dynamics x))
                                   (mult eta (entropy_gradient x))))
                       (opp (entropy x)))
                 (plus (entropy (dynamics x)) (opp (entropy x)))).
  - exact (req_sym
              (plus (plus (entropy x)
                          (mult (entropy_gradient (dynamics x))
                                (mult eta (entropy_gradient x))))
                    (opp (entropy x)))
              (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
              Hrot).
  - exact (le_plus_compat (plus (entropy x)
                                (mult (entropy_gradient (dynamics x))
                                      (mult eta (entropy_gradient x))))
                          (entropy (dynamics x))
                          (opp (entropy x)) (opp (entropy x))
                          Ht2 (le_refl (opp (entropy x)))).
Qed.

(* ===== 件 8：核 B Lipschitz 单边提取（母件 L228；A+ 级：(i)-(vi) 全 req 运输） ===== *)
Lemma req_eg_grad_lower : forall x : R,
  lt zero (entropy_gradient x) ->
  le (mult (req_minus one (mult L eta)) (entropy_gradient x))
     (entropy_gradient (dynamics x)).
Proof.
  intros x Hgx.
  (* (i) |x' − x| == η·g（req 真证：abs 兼容/积/正三跳） *)
  assert (Habsstep : req (abs (req_minus (dynamics x) x))
                         (mult eta (entropy_gradient x))).
  { apply (req_trans (abs (req_minus (dynamics x) x))
                     (abs (mult eta (entropy_gradient x)))
                     (mult eta (entropy_gradient x))).
    - exact (req_abs_compat (req_minus (dynamics x) x)
                            (mult eta (entropy_gradient x))
                            (req_eg_step_diff x)).
    - apply (req_trans (abs (mult eta (entropy_gradient x)))
                       (mult (abs eta) (abs (entropy_gradient x)))
                       (mult eta (entropy_gradient x))).
      + exact (abs_mult eta (entropy_gradient x)).
      + exact (req_mult_compat (abs eta) eta
                               (abs (entropy_gradient x)) (entropy_gradient x)
                               (abs_pos eta eta_pos)
                               (abs_pos (entropy_gradient x) Hgx)). }
  (* |x − x'| == η·g（opp 换形经 abs_opp 字段） *)
  assert (Habsneg : req (abs (req_minus x (dynamics x)))
                        (mult eta (entropy_gradient x))).
  { apply (req_trans (abs (req_minus x (dynamics x)))
                     (abs (opp (mult eta (entropy_gradient x))))
                     (mult eta (entropy_gradient x))).
    - exact (req_abs_compat (req_minus x (dynamics x))
                            (opp (mult eta (entropy_gradient x)))
                            (req_eg_step_neg_diff x)).
    - apply (req_trans (abs (opp (mult eta (entropy_gradient x))))
                       (abs (mult eta (entropy_gradient x)))
                       (mult eta (entropy_gradient x))).
      + exact (abs_opp (mult eta (entropy_gradient x))).
      + exact (req_trans (abs (mult eta (entropy_gradient x)))
                         (mult (abs eta) (abs (entropy_gradient x)))
                         (mult eta (entropy_gradient x))
                         (abs_mult eta (entropy_gradient x))
                         (req_mult_compat (abs eta) eta
                                          (abs (entropy_gradient x))
                                          (entropy_gradient x)
                                          (abs_pos eta eta_pos)
                                          (abs_pos (entropy_gradient x) Hgx))). }
  (* (ii) Lipschitz 在 (x, x') 处（req 接口 le_id_r 字段） *)
  assert (Hlip : le (abs (req_minus (entropy_gradient x)
                                    (entropy_gradient (dynamics x))))
                    (mult L (mult eta (entropy_gradient x)))).
  { apply (le_id_r (abs (req_minus (entropy_gradient x)
                                   (entropy_gradient (dynamics x))))
                   (mult L (abs (req_minus x (dynamics x))))
                   (mult L (mult eta (entropy_gradient x)))).
    - exact (req_mult_compat L L (abs (req_minus x (dynamics x)))
                                (mult eta (entropy_gradient x))
                                (req_refl L) Habsneg).
    - exact (gradient_lipschitz x (dynamics x)). }
  (* (iii) 单边提取（abs_ge_value 假设位消费） *)
  assert (Hone : le (req_minus (entropy_gradient x) (entropy_gradient (dynamics x)))
                    (mult L (mult eta (entropy_gradient x)))).
  { apply (le_trans (req_minus (entropy_gradient x) (entropy_gradient (dynamics x)))
                    (abs (req_minus (entropy_gradient x)
                                    (entropy_gradient (dynamics x))))
                    (mult L (mult eta (entropy_gradient x)))).
    - exact (abs_ge_value (req_minus (entropy_gradient x)
                                     (entropy_gradient (dynamics x)))).
    - exact Hlip. }
  (* (iv) 移项 le g ((Lη)g + g')（req_eg_minus_plus_cancel + le_plus_compat） *)
  assert (H1 : le (entropy_gradient x)
                  (plus (mult L (mult eta (entropy_gradient x)))
                        (entropy_gradient (dynamics x)))).
  { apply (le_id_l (entropy_gradient x)
                   (plus (req_minus (entropy_gradient x)
                                    (entropy_gradient (dynamics x)))
                         (entropy_gradient (dynamics x)))
                   (plus (mult L (mult eta (entropy_gradient x)))
                         (entropy_gradient (dynamics x)))).
    - exact (req_sym (plus (req_minus (entropy_gradient x)
                                      (entropy_gradient (dynamics x)))
                           (entropy_gradient (dynamics x)))
                     (entropy_gradient x)
                     (req_eg_minus_plus_cancel (entropy_gradient x)
                                               (entropy_gradient (dynamics x)))).
    - exact (le_plus_compat (req_minus (entropy_gradient x)
                                       (entropy_gradient (dynamics x)))
                            (mult L (mult eta (entropy_gradient x)))
                            (entropy_gradient (dynamics x))
                            (entropy_gradient (dynamics x))
                            Hone (le_refl (entropy_gradient (dynamics x)))). }
  (* (v) 换形 le (g + opp((Lη)g)) g'（req 接口 le_id_r 字段 + 三跳完成） *)
  assert (H2 : le (plus (entropy_gradient x)
                        (opp (mult L (mult eta (entropy_gradient x)))))
                  (entropy_gradient (dynamics x))).
  { apply (le_id_r (plus (entropy_gradient x)
                         (opp (mult L (mult eta (entropy_gradient x)))))
                   (plus (plus (mult L (mult eta (entropy_gradient x)))
                               (entropy_gradient (dynamics x)))
                         (opp (mult L (mult eta (entropy_gradient x)))))
                   (entropy_gradient (dynamics x))).
    - apply (req_trans
                (plus (plus (mult L (mult eta (entropy_gradient x)))
                            (entropy_gradient (dynamics x)))
                      (opp (mult L (mult eta (entropy_gradient x)))))
                (plus (plus (entropy_gradient (dynamics x))
                            (mult L (mult eta (entropy_gradient x))))
                      (opp (mult L (mult eta (entropy_gradient x)))))
                (entropy_gradient (dynamics x))).
      + exact (req_plus_compat
                  (plus (mult L (mult eta (entropy_gradient x)))
                        (entropy_gradient (dynamics x)))
                  (plus (entropy_gradient (dynamics x))
                        (mult L (mult eta (entropy_gradient x))))
                  (opp (mult L (mult eta (entropy_gradient x))))
                  (opp (mult L (mult eta (entropy_gradient x))))
                  (plus_comm (mult L (mult eta (entropy_gradient x)))
                             (entropy_gradient (dynamics x)))
                  (req_refl (opp (mult L (mult eta (entropy_gradient x)))))).
      + apply (req_trans
                  (plus (plus (entropy_gradient (dynamics x))
                              (mult L (mult eta (entropy_gradient x))))
                        (opp (mult L (mult eta (entropy_gradient x)))))
                  (plus (entropy_gradient (dynamics x)) zero)
                  (entropy_gradient (dynamics x))).
        * exact (req_trans
                    (plus (plus (entropy_gradient (dynamics x))
                                (mult L (mult eta (entropy_gradient x))))
                          (opp (mult L (mult eta (entropy_gradient x)))))
                    (plus (entropy_gradient (dynamics x))
                          (plus (mult L (mult eta (entropy_gradient x)))
                                (opp (mult L (mult eta (entropy_gradient x))))))
                    (plus (entropy_gradient (dynamics x)) zero)
                    (req_sym
                       (plus (entropy_gradient (dynamics x))
                             (plus (mult L (mult eta (entropy_gradient x)))
                                   (opp (mult L (mult eta (entropy_gradient x))))))
                       (plus (plus (entropy_gradient (dynamics x))
                                   (mult L (mult eta (entropy_gradient x))))
                             (opp (mult L (mult eta (entropy_gradient x)))))
                       (plus_assoc (entropy_gradient (dynamics x))
                                   (mult L (mult eta (entropy_gradient x)))
                                   (opp (mult L (mult eta (entropy_gradient x))))))
                    (req_plus_compat (entropy_gradient (dynamics x))
                                     (entropy_gradient (dynamics x))
                                     (plus (mult L (mult eta (entropy_gradient x)))
                                           (opp (mult L (mult eta (entropy_gradient x)))))
                                     zero
                                     (req_refl (entropy_gradient (dynamics x)))
                                     (plus_opp (mult L (mult eta (entropy_gradient x)))))).
        * apply plus_zero.
    - exact (le_plus_compat (entropy_gradient x)
                            (plus (mult L (mult eta (entropy_gradient x)))
                                  (entropy_gradient (dynamics x)))
                            (opp (mult L (mult eta (entropy_gradient x))))
                            (opp (mult L (mult eta (entropy_gradient x))))
                            H1 (le_refl (opp (mult L (mult eta (entropy_gradient x)))))). }
  (* (vi) 终换形：(1 − Lη)·g == g + opp((Lη)·g)（req 两跳） *)
  apply (le_id_l (mult (req_minus one (mult L eta)) (entropy_gradient x))
                 (plus (entropy_gradient x)
                       (opp (mult L (mult eta (entropy_gradient x)))))).
  - exact (req_trans (mult (req_minus one (mult L eta)) (entropy_gradient x))
                     (plus (mult one (entropy_gradient x))
                           (mult (opp (mult L eta)) (entropy_gradient x)))
                     (plus (entropy_gradient x)
                           (opp (mult L (mult eta (entropy_gradient x)))))
                     (req_mult_plus_distr_r one (opp (mult L eta))
                                            (entropy_gradient x))
                     (req_trans
                        (plus (mult one (entropy_gradient x))
                              (mult (opp (mult L eta)) (entropy_gradient x)))
                        (plus (entropy_gradient x)
                              (opp (mult (mult L eta) (entropy_gradient x))))
                        (plus (entropy_gradient x)
                              (opp (mult L (mult eta (entropy_gradient x)))))
                        (req_plus_compat (mult one (entropy_gradient x))
                                         (entropy_gradient x)
                                         (mult (opp (mult L eta)) (entropy_gradient x))
                                         (opp (mult (mult L eta) (entropy_gradient x)))
                                         (req_mult_one_l (entropy_gradient x))
                                         (req_opp_mult_r (mult L eta)
                                                         (entropy_gradient x)))
                        (req_plus_compat (entropy_gradient x) (entropy_gradient x)
                                         (opp (mult (mult L eta) (entropy_gradient x)))
                                         (opp (mult L (mult eta (entropy_gradient x))))
                                         (req_refl (entropy_gradient x))
                                         (req_opp_compat
                                             (mult (mult L eta) (entropy_gradient x))
                                             (mult L (mult eta (entropy_gradient x)))
                                             (req_sym
                                                 (mult L (mult eta (entropy_gradient x)))
                                                 (mult (mult L eta)
                                                       (entropy_gradient x))
                                                 (mult_assoc L eta
                                                             (entropy_gradient x))))))).
  - exact H2.
Qed.

(* ============================================================ *)
(* 件 9（旗舰一）：req_entropy_step_gain_lower                   *)
(*   母件 L327：η(1 − Lη)·g² ≤ e(x') − e(x)。组装：核 B 乘 g>0    *)
(*   （接口 le_mult_compat 字段）再乘 η>0（批 1                  *)
(*   req_le_mult_compat_r），与件 7 级联。                        *)
(* ============================================================ *)
Theorem req_entropy_step_gain_lower : forall x : R,
  lt zero (entropy_gradient x) ->
  le (mult (mult eta (req_minus one (mult L eta)))
           (mult (entropy_gradient x) (entropy_gradient x)))
     (req_minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x Hgx.
  pose proof (req_eg_grad_lower x Hgx) as Hlow.
  pose proof (le_mult_compat (mult (req_minus one (mult L eta)) (entropy_gradient x))
                             (entropy_gradient (dynamics x))
                             (entropy_gradient x) Hgx Hlow) as Hm1.
  assert (Hm1' : le (mult (req_minus one (mult L eta))
                          (mult (entropy_gradient x) (entropy_gradient x)))
                    (mult (entropy_gradient (dynamics x)) (entropy_gradient x))).
  { apply (le_id_l (mult (req_minus one (mult L eta))
                         (mult (entropy_gradient x) (entropy_gradient x)))
                   (mult (mult (req_minus one (mult L eta)) (entropy_gradient x))
                         (entropy_gradient x))
                   (mult (entropy_gradient (dynamics x)) (entropy_gradient x))).
    - exact (mult_assoc (req_minus one (mult L eta)) (entropy_gradient x)
                        (entropy_gradient x)).
    - exact Hm1. }
  pose proof (lt_le_iff zero eta (inl eta_pos)) as Hle_eta.
  pose proof (req_le_mult_compat_r eta
                                   (mult (req_minus one (mult L eta))
                                         (mult (entropy_gradient x) (entropy_gradient x)))
                                   (mult (entropy_gradient (dynamics x))
                                         (entropy_gradient x))
                                   Hle_eta Hm1') as Hm2.
  assert (Hm2' : le (mult (mult eta (req_minus one (mult L eta)))
                          (mult (entropy_gradient x) (entropy_gradient x)))
                    (mult (entropy_gradient (dynamics x))
                          (mult eta (entropy_gradient x)))).
  { apply (le_id_l (mult (mult eta (req_minus one (mult L eta)))
                         (mult (entropy_gradient x) (entropy_gradient x)))
                   (mult eta (mult (req_minus one (mult L eta))
                                   (mult (entropy_gradient x) (entropy_gradient x))))
                   (mult (entropy_gradient (dynamics x))
                         (mult eta (entropy_gradient x)))).
    - exact (req_sym (mult eta (mult (req_minus one (mult L eta))
                                     (mult (entropy_gradient x) (entropy_gradient x))))
                     (mult (mult eta (req_minus one (mult L eta)))
                           (mult (entropy_gradient x) (entropy_gradient x)))
                     (mult_assoc eta (req_minus one (mult L eta))
                                 (mult (entropy_gradient x) (entropy_gradient x)))).
    - apply (le_id_r (mult eta (mult (req_minus one (mult L eta))
                                     (mult (entropy_gradient x) (entropy_gradient x))))
                     (mult eta (mult (entropy_gradient (dynamics x))
                                     (entropy_gradient x)))
                     (mult (entropy_gradient (dynamics x))
                           (mult eta (entropy_gradient x)))).
      + exact (req_trans
                  (mult eta (mult (entropy_gradient (dynamics x)) (entropy_gradient x)))
                  (mult (mult eta (entropy_gradient (dynamics x))) (entropy_gradient x))
                  (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
                  (mult_assoc eta (entropy_gradient (dynamics x)) (entropy_gradient x))
                  (req_trans
                     (mult (mult eta (entropy_gradient (dynamics x))) (entropy_gradient x))
                     (mult (mult (entropy_gradient (dynamics x)) eta) (entropy_gradient x))
                     (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
                     (req_mult_compat (mult eta (entropy_gradient (dynamics x)))
                                      (mult (entropy_gradient (dynamics x)) eta)
                                      (entropy_gradient x) (entropy_gradient x)
                                      (mult_comm eta (entropy_gradient (dynamics x)))
                                      (req_refl (entropy_gradient x)))
                     (req_sym (mult (entropy_gradient (dynamics x))
                                    (mult eta (entropy_gradient x)))
                              (mult (mult (entropy_gradient (dynamics x)) eta)
                                    (entropy_gradient x))
                              (mult_assoc (entropy_gradient (dynamics x)) eta
                                          (entropy_gradient x))))).
      + exact Hm2. }
  exact (le_trans (mult (mult eta (req_minus one (mult L eta)))
                        (mult (entropy_gradient x) (entropy_gradient x)))
                  (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
                  (req_minus (entropy (dynamics x)) (entropy x))
                  Hm2' (req_eg_tangent_shift x)).
Qed.

(* ============================================================ *)
(* 件 10：req_entropy_gain_positive（母件 L379；B 级联装配）      *)
(* ============================================================ *)
Theorem req_entropy_gain_positive : forall x : R,
  lt zero (entropy_gradient x) ->
  lt (mult L eta) one ->
  lt zero (req_minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x Hgx HetaL.
  assert (Hc : lt zero (req_minus one (mult L eta)))
    by exact (req_eg_minus_pos (mult L eta) one HetaL).
  assert (Hc1 : lt zero (mult eta (req_minus one (mult L eta))))
    by exact (mult_positive eta (req_minus one (mult L eta)) eta_pos Hc).
  assert (Haa : lt zero (mult (entropy_gradient x) (entropy_gradient x)))
    by exact (mult_positive (entropy_gradient x) (entropy_gradient x) Hgx Hgx).
  assert (HA : lt zero (mult (mult eta (req_minus one (mult L eta)))
                             (mult (entropy_gradient x) (entropy_gradient x))))
    by exact (mult_positive (mult eta (req_minus one (mult L eta)))
                            (mult (entropy_gradient x) (entropy_gradient x))
                            Hc1 Haa).
  pose proof (req_entropy_step_gain_lower x Hgx) as Hlow.
  exact (lt_le_trans zero
                     (mult (mult eta (req_minus one (mult L eta)))
                           (mult (entropy_gradient x) (entropy_gradient x)))
                     (req_minus (entropy (dynamics x)) (entropy x))
                     HA Hlow).
Qed.

(* ============================================================ *)
(* 件 11（旗舰二）：req_second_law_quant（母件 L409）             *)
(*   根 L27796 SecondLaw 区 strict_entropy_increase 接口假设的    *)
(*   构造性替代在 req 侧的同位重述：具体熵梯度动力学 + 诚实充分    *)
(*   条件（ηL<1、g(x)>0）产出 lt (entropy x) (entropy x')。       *)
(* ============================================================ *)
Theorem req_second_law_quant : forall x : R,
  lt zero (entropy_gradient x) ->
  lt (mult L eta) one ->
  lt (entropy x) (entropy (dynamics x)).
Proof.
  intros x Hgx HetaL.
  pose proof (req_entropy_gain_positive x Hgx HetaL) as Hpos.
  apply (lt_id_r (entropy x)
                 (plus (req_minus (entropy (dynamics x)) (entropy x)) (entropy x))
                 (entropy (dynamics x))).
  - exact (req_eg_minus_plus_cancel (entropy (dynamics x)) (entropy x)).
  - apply (lt_id_l (entropy x) (plus zero (entropy x))
                   (plus (req_minus (entropy (dynamics x)) (entropy x)) (entropy x))).
    + exact (req_trans (entropy x) (plus (entropy x) zero) (plus zero (entropy x))
                       (req_sym (plus (entropy x) zero) (entropy x)
                                (plus_zero (entropy x)))
                       (plus_comm (entropy x) zero)).
    + exact (lt_plus_compat_lt_le zero
                                  (req_minus (entropy (dynamics x)) (entropy x))
                                  (entropy x) (entropy x)
                                  Hpos (le_refl (entropy x))).
Qed.

End EntropyGainReq.
