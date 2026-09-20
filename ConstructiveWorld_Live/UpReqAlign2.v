(* ============================================================ *)
(* UpReqAlign2.v *)
(* *)
(* 目的： 对齐族第二段：求和定律扩充与自由能分解准备。 *)
(* 主件： req2_rel_ent_self_zero / req2_log_inv_one_inv / req2_log_exp_neg 与求和线性族 req2_sum_*。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqAlign。 *)
(* 备注： 承第一段 Section 变量；新增求和定律均为接口字段推导，零新假设位。 *)
(* ============================================================ *)

(* UpReqAlign2.v — 签名迁移批 3b：对齐主体完成（t13/t12 深链伴件 +
   dpo_pair/preference 簇 req 化 + 旗舰链闭合）
   母本：D:\ComplexAnalysis\ConstructiveWorld-Main\docs\签名迁移规划书-20260908.md
     （批 3b 节 = 批 3 附录 D.1（三）深链挂起清单的放行批）
   上游：UpReqAlgebra.v（批 1 代数银行，直接消费）+
     req_kl_minus_split / req_le_of_minus_nonneg）；
   纯 term-mode（req_trans 链 + compat 桥），零 Morphisms 依赖；
   Set 层语句（req/lt/le 均 Set 值，零 Prop 泄露）。
   ----------------------------------------------------------------
   本批实结果（时间盒结算，全件真证零 承认件；余件见文件尾挂起清单）：
       + 批 3 支撑件姊妹重建 12 + 纯环代数辅件 8 + boltzmann 因子桥
       energy_log_pt/sum_E_beta/F_t_beta_form/F_t_simpl_next/
       F_t_rel_decomp/F_t_simpl_t/F_t_simpl_next_kl——其中
       req2_F_t_rel_decomp（F_t(π_t) == F_t(π_next) + β·KL）即 Id
       rel_free_energy_decomp(@21441) 的 req 版，为 mirror-descent
       两条深链共用的核心机器。
   [B] surrogate_diff_identity(@21744)/reward_expand(@21473) 的 req
       后按文件尾挂起清单平移 t12 余件与 t13 链。
   [C] dpo_pair/preference 簇与旗舰链改挂：挂起（逐件坐标与依赖见
       文件尾清单；批 3 两桥位的放行条件已由 [A] 组机器就绪）。
   ----------------------------------------------------------------
   诚实签名变化登记表（规划书 §7.4；沿批 3 形态 + 本批新增）：
   1. log 前提化：req2_rel_ent / req2_F_align / req2_free_energy /
     req2_dpo_pair_loss 全部携带逐点正性参数（批 3 同款）。
   2. minus 载体 = UpReqAlgebra.req_minus（δ 透明同形 Id minus）。
   3. T2① 桥位（与 Id 逐位同构/或挂起依赖，全表）：
      - log_inv_exp_neg_req：Id 接口字段 log_inv_exp_neg（L187）
        的 req 同位——setoid 接口缺对应字段（exp_neg 注入性不可由
        字段导出）；UpReqAlgebra ReqLogBridge 同位桥，本节承接
        （批 3 ReqAlignCore 未承接此桥，本批深链需要：π_next 对数
        展开 log(e^x)==−x 恒等式消费之）。
      - req2_gibbs_inequality：Id 定理 gibbs_inequality（L16629，批 2 FEP 清单）的 req 同位挂起依赖——其 Id 证明
        侧 plain-le KL≥0 不可由接口逐 eps 字段导出（序无消去，
        与批 3 min plain-le 冻结同因）；UpReqFreeEnergy（批 2）
        结果后降为消费件（批 3 bridge_min_free_energy 同先例）。
      - req2_step_kl_eta_bound：B 类 Variable（L23114）的 req
        同位——诚实红线要求保留显式假设位，不消解。
      - req2_inv_pos_lt_contra / req2_log_lt_mono /
        req2_lt_plus_compat_{le_lt,lt_le}：Id 诚实 Variable
        （L21013/21024/21018/21020）的 req 同位（批 1
        ReqStrictOrderBridge 已结果 lt_le/le_lt 两式的消费件形态）。
   4. (d) 冻结（沿批 3 + 本批新增）：ppo_gap_nonneg（消费
     ppo_conservative——min plain-le 冻结同因）、fold_right_ext 与
     list fold 机器（nat/list 层 Id，双层并行）。
   ---------------------------------------------------------------- *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Req2AlignCore：对齐主体完成节                                  *)
(*   （节参数与批 3 ReqAlignCore 逐位对齐 + eta 参数 + 深链桥位）  *)
(* ============================================================ *)
Section Req2AlignCore.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

(* ---- 求和对接面（批 3 同位；本批深链仅需 ext/add/linear/pos） ---- *)
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

(* ---- 接口缺口桥（登记表 3；UpReqAlgebra ReqLogBridge 同位） ---- *)
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Hypothesis log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.

(* ---- 节参数（对齐 Id 系 L18750-18768 / L21240-21242） ---- *)
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable pi_ref_norm : req (sumf pi_ref) one.
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable eta_le_one : le eta one.

(* ---- req2 系节内定义（Id 系同形；log 前提化——登记表 1） ---- *)
Definition req2_pos_dist (p : S -> R) : Set := forall s : S, lt zero (p s).
Definition req2_norm_one (p : S -> R) : Set := req (sumf p) one.

Definition req2_Z_align : R :=
  sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Variable Z_align_pos : lt zero req2_Z_align.
Definition req2_pi_star (s : S) : R :=
  mult (inv_pos req2_Z_align Z_align_pos)
       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).

(* 相对熵 req 形态（Id relative_entropy L16535 的 req 同位，批 3
   relative_entropy_req 姊妹件） *)
Definition req2_rel_ent (p q : S -> R) (Hp : req2_pos_dist p) (Hq : req2_pos_dist q) : R :=
  sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))).

(* 对齐能量 / 自由能 / 对齐目标 / DPO 损失（Id align_energy L18849 /
   free_energy L16520 / align_objective L18855 / dpo_loss 同形） *)
Definition req2_align_energy (s : S) : R :=
  req_minus (opp (reward s)) (mult beta (log (pi_ref s) (pi_ref_pos s))).
Definition req2_F_align (p : S -> R) (Hp : req2_pos_dist p) : R :=
  plus (sumf (fun s => mult (p s) (req2_align_energy s)))
       (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition req2_J (p : S -> R) (Hp : req2_pos_dist p) : R :=
  opp (req2_F_align p Hp).
Definition req2_dpo_loss (p : S -> R) (Hp : req2_pos_dist p) : R :=
  opp (req2_J p Hp).

(* 自由能一般形态（Id free_energy energy D p := Σ p·E + D·Σ p·log p；
   log 前提化：携带逐点正性——登记表 1） *)
Definition req2_free_energy (energy : S -> R) (D : R) (p : S -> R) (Hp : req2_pos_dist p) : R :=
  plus (sumf (fun s => mult (p s) (energy s)))
       (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))).

(* 定义簇（Id advantage_aug/Z_rel/energy_t/pi_next L21247-21270 同形） *)
Definition req2_adv (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t) (s : S) : R :=
  req_minus (reward s)
            (mult beta (req_minus (log (pi_t s) (Hpi_t s)) (log (pi_ref s) (pi_ref_pos s)))).
Definition req2_Z_rel (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t) : R :=
  sumf (fun s => mult (pi_t s)
                      (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                          (req2_adv pi_t Hpi_t s))))).
Definition req2_energy_t (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t) (s : S) : R :=
  req_minus (opp (mult eta (req2_adv pi_t Hpi_t s)))
            (mult beta (log (pi_t s) (Hpi_t s))).

(* Z_rel 正性（Id Z_rel_pos L21253 req 版；先于 pi_next 定义供其引用） *)
Lemma req2_Z_rel_pos :
  forall (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t),
    lt zero (req2_Z_rel pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t.
  unfold req2_Z_rel.
  apply sum_pos.
  intro s.
  apply mult_positive.
  - apply Hpi_t.
  - apply exp_neg_pos.
Qed.

Definition req2_pi_next (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t) (s : S) : R :=
  mult (inv_pos (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t))
       (mult (pi_t s)
             (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                 (req2_adv pi_t Hpi_t s))))).

(* ============ S 组：求和辅件（Id sum_opp/sum_minus/线性簇 req 化） ============ *)

(* Σ 0 == 0（经 sum_linear zero 与逐点 mult zero one == zero） *)
Lemma req2_sum_zero_fun : req (sumf (fun _ : S => zero)) zero.
Proof.
  apply (req_trans (sumf (fun _ : S => zero))
                   (sumf (fun s => mult zero one))
                   zero).
  - apply (sum_ext (fun _ : S => zero) (fun s => mult zero one)).
    intro s.
    apply (req_sym (mult zero one) zero).
    apply (req_trans (mult zero one) (mult one zero) zero
                     (mult_comm zero one) (mult_zero one)).
  - apply (req_trans (sumf (fun s => mult zero one))
                     (mult zero (sumf (fun _ : S => one)))
                     zero).
    + exact (sum_linear zero (fun _ : S => one)).
    + apply (req_trans (mult zero (sumf (fun _ : S => one)))
                       (mult (sumf (fun _ : S => one)) zero) zero
                       (mult_comm zero (sumf (fun _ : S => one)))
                       (mult_zero (sumf (fun _ : S => one)))).
Qed.

(* Σ opp f == opp (Σ f)（Id sum_opp req 版） *)
Lemma req2_sum_opp : forall f : S -> R,
  req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (sum_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))).
    intro s.
    apply (req_sym (mult (opp one) (f s)) (opp (f s))).
    apply (req_trans (mult (opp one) (f s)) (opp (mult one (f s))) (opp (f s))
                     (req_opp_mult_r one (f s))
                     (req_opp_compat (mult one (f s)) (f s) (req_mult_one_l (f s)))).
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f))
                     (opp (sumf f))).
    + exact (sum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f))
                       (opp (mult one (sumf f)))
                       (opp (sumf f))
                       (req_opp_mult_r one (sumf f))
                       (req_opp_compat (mult one (sumf f)) (sumf f) (req_mult_one_l (sumf f)))).
Qed.

(* Σ (f − g) == (Σ f) − (Σ g)（Id sum_over_S_minus req 版） *)
Lemma req2_sum_minus : forall f g : S -> R,
  req (sumf (fun s => req_minus (f s) (g s))) (req_minus (sumf f) (sumf g)).
Proof.
  intros f g. unfold req_minus.
  apply (req_trans (sumf (fun s => plus (f s) (opp (g s))))
                   (plus (sumf f) (sumf (fun s => opp (g s))))
                   (plus (sumf f) (opp (sumf g)))).
  - exact (sum_add f (fun s => opp (g s))).
  - apply (req_plus_compat (sumf f) (sumf f)
                           (sumf (fun s => opp (g s))) (opp (sumf g))
                           (req_refl (sumf f))).
    exact (req2_sum_opp g).
Qed.

(* Σ p·(a·f) == a·Σ p·f（Id sum_ptimes_scal_t12 req 版） *)
Lemma req2_sum_ptimes_scal : forall (p : S -> R) (a : R) (f : S -> R),
  req (sumf (fun s => mult (p s) (mult a (f s))))
      (mult a (sumf (fun s => mult (p s) (f s)))).
Proof.
  intros p a f.
  apply (req_trans (sumf (fun s => mult (p s) (mult a (f s))))
                   (sumf (fun s => mult a (mult (p s) (f s))))
                   (mult a (sumf (fun s => mult (p s) (f s))))).
  - apply (sum_ext (fun s => mult (p s) (mult a (f s)))
                   (fun s => mult a (mult (p s) (f s)))).
    intro s.
    apply (req_trans (mult (p s) (mult a (f s))) (mult (mult (p s) a) (f s))
                     (mult a (mult (p s) (f s)))).
    + apply mult_assoc.
    + apply (req_trans (mult (mult (p s) a) (f s)) (mult (mult a (p s)) (f s))
                       (mult a (mult (p s) (f s)))
                       (req_mult_compat (mult (p s) a) (mult a (p s)) (f s) (f s)
                                        (mult_comm (p s) a) (req_refl (f s)))
                       (req_sym (mult a (mult (p s) (f s)))
                                (mult (mult a (p s)) (f s))
                                (mult_assoc a (p s) (f s)))).
  - exact (sum_linear a (fun s => mult (p s) (f s))).
Qed.

(* Σ p·(opp (a·f)) == opp (a·Σ p·f)（Id sum_ptimes_opp_scal_t12 req 版） *)
Lemma req2_sum_ptimes_opp_scal : forall (p : S -> R) (a : R) (f : S -> R),
  req (sumf (fun s => mult (p s) (opp (mult a (f s)))))
      (opp (mult a (sumf (fun s => mult (p s) (f s))))).
Proof.
  intros p a f.
  apply (req_trans (sumf (fun s => mult (p s) (opp (mult a (f s)))))
                   (sumf (fun s => opp (mult a (mult (p s) (f s)))))
                   (opp (mult a (sumf (fun s => mult (p s) (f s)))))).
  - apply (sum_ext (fun s => mult (p s) (opp (mult a (f s))))
                   (fun s => opp (mult a (mult (p s) (f s))))).
    intro s.
    apply (req_trans (mult (p s) (opp (mult a (f s))))
                     (opp (mult (p s) (mult a (f s))))
                     (opp (mult a (mult (p s) (f s))))).
    + apply req_opp_mult_l.
    + apply (req_opp_compat (mult (p s) (mult a (f s)))
                            (mult a (mult (p s) (f s)))).
      apply (req_trans (mult (p s) (mult a (f s))) (mult (mult (p s) a) (f s))
                       (mult a (mult (p s) (f s)))).
      * apply mult_assoc.
      * apply (req_trans (mult (mult (p s) a) (f s)) (mult (mult a (p s)) (f s))
                         (mult a (mult (p s) (f s)))
                         (req_mult_compat (mult (p s) a) (mult a (p s)) (f s) (f s)
                                          (mult_comm (p s) a) (req_refl (f s)))
                         (req_sym (mult a (mult (p s) (f s)))
                                  (mult (mult a (p s)) (f s))
                                  (mult_assoc a (p s) (f s)))).
  - apply (req_trans (sumf (fun s => opp (mult a (mult (p s) (f s)))))
                     (opp (sumf (fun s => mult a (mult (p s) (f s)))))
                     (opp (mult a (sumf (fun s => mult (p s) (f s)))))).
    + exact (req2_sum_opp (fun s => mult a (mult (p s) (f s)))).
    + exact (req_opp_compat (sumf (fun s => mult a (mult (p s) (f s))))
                            (mult a (sumf (fun s => mult (p s) (f s))))
                            (sum_linear a (fun s => mult (p s) (f s)))).
Qed.

(* Σ p·c == c（Σ p = 1；Id sum_ptimes_opp_const_t12 的常数一般形） *)
Lemma req2_sum_ptimes_const : forall (p : S -> R) (c : R),
  req (sumf p) one -> req (sumf (fun s => mult (p s) c)) c.
Proof.
  intros p c Hn.
  apply (req_trans (sumf (fun s => mult (p s) c))
                   (mult c (sumf p)) c).
  - apply (req_trans (sumf (fun s => mult (p s) c))
                     (sumf (fun s => mult c (p s)))
                     (mult c (sumf p))).
    + apply (sum_ext (fun s => mult (p s) c) (fun s => mult c (p s))
                     (fun s => mult_comm (p s) c)).
    + exact (sum_linear c p).
  - apply (req_trans (mult c (sumf p)) (mult c one) c
                     (req_mult_compat c c (sumf p) one (req_refl c) Hn)
                     (mult_one c)).
Qed.

(* KL(p‖p) == 0（Id relative_entropy_self_zero req 版） *)
Lemma req2_rel_ent_self_zero : forall (p : S -> R) (Hp : req2_pos_dist p),
  req (req2_rel_ent p p Hp Hp) zero.
Proof.
  intros p Hp. unfold req2_rel_ent.
  apply (req_trans (sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (p s) (Hp s)))))
                   (sumf (fun _ : S => zero)) zero).
  - apply (sum_ext (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))))
                   (fun _ : S => zero)).
    intro s.
    apply (req_trans (mult (p s) (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))))
                     (mult (p s) zero) zero).
    + apply (req_mult_compat (p s) (p s)
                             (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))) zero
                             (req_refl (p s))
                             (req_minus_self_zero (log (p s) (Hp s)) (log (p s) (Hp s))
                                                  (req_refl (log (p s) (Hp s))))).
    + apply (req_trans (mult (p s) zero) (mult zero (p s)) zero
                       (mult_comm (p s) zero)
                       (req_trans (mult zero (p s)) (mult (p s) zero) zero
                                  (mult_comm zero (p s)) (mult_zero (p s)))).
  - exact req2_sum_zero_fun.
Qed.



(* log(e^{-x}) == −x（消费批 3 交接件 rkl_log_inv_one_inv，桥 = 节内
   log_req_compat——同款交接形态） *)
Lemma req2_log_inv_one_inv : forall (x : R) (Hx : lt zero x),
  req (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  exact (rkl_log_inv_one_inv log_req_compat x Hx).
Qed.

(* log(e^{x}) == −x（Id 接口字段 log_inv_exp_neg @L187 的 req 同位消费；
   桥 = log_inv_exp_neg_req + 字段 log_inv_log） *)
Lemma req2_log_exp_neg : forall x : R,
  req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intro x.
  assert (Hli : req (log_inv (exp_neg x) (exp_neg_pos x)) x).
  { exact (log_inv_exp_neg_req x). }
  apply (req_opp_eq (log (exp_neg x) (exp_neg_pos x)) (opp x)).
  apply (req_trans (opp (log (exp_neg x) (exp_neg_pos x)))
                   (log_inv (exp_neg x) (exp_neg_pos x))
                   (opp (opp x))).
  - exact (req_sym (log_inv (exp_neg x) (exp_neg_pos x))
                   (opp (log (exp_neg x) (exp_neg_pos x)))
                   (log_inv_log (exp_neg x) (exp_neg_pos x))).
  - apply (req_trans (log_inv (exp_neg x) (exp_neg_pos x)) x (opp (opp x)) Hli).
    + exact (req_sym (opp (opp x)) x (req_double_neg x)).
Qed.

(* ============ T0 组：批 3 支撑件姊妹重建（节内自足） ============ *)

(* opp 的逆（Id opp_eq L19170 req 版；批 3 req_opp_eq 同款真证） *)
Lemma req2_opp_eq : forall a b : R, req (opp a) (opp b) -> req a b.
Proof.
  intros a b Hab.
  apply (req_trans a (opp (opp a)) b).
  - apply (req_sym (opp (opp a)) a). apply req_double_neg.
  - apply (req_trans (opp (opp a)) (opp (opp b)) b).
    + apply (req_opp_compat (opp a) (opp b) Hab).
    + apply req_double_neg.
Qed.

(* π* 逐点正性（Id pi_star_pos L18783 req 版） *)
Lemma req2_pi_star_pos : req2_pos_dist req2_pi_star.
Proof.
  intro s.
  unfold req2_pi_star.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply mult_positive.
    + apply pi_ref_pos.
    + apply exp_neg_pos.
Qed.

(* π* 归一化（Id pi_star_normalized L18790 req 版；批 3 同款真证） *)
Lemma req2_pi_star_normalized : req (sumf req2_pi_star) one.
Proof.
  apply (req_trans (sumf (fun s => mult (inv_pos req2_Z_align Z_align_pos)
                                        (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))
                   (mult (inv_pos req2_Z_align Z_align_pos)
                         (sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))
                   one).
  - exact (sum_linear (inv_pos req2_Z_align Z_align_pos)
                      (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))).
  - apply (req_trans (mult (inv_pos req2_Z_align Z_align_pos)
                           (sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))
                     (mult (inv_pos req2_Z_align Z_align_pos) req2_Z_align)
                     one).
    + apply (req_mult_compat (inv_pos req2_Z_align Z_align_pos)
                             (inv_pos req2_Z_align Z_align_pos)
                             (sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))
                             req2_Z_align).
      * apply req_refl.
      * apply (req_sym req2_Z_align
                       (sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))).
        apply req_refl.
    + apply (req_trans (mult (inv_pos req2_Z_align Z_align_pos) req2_Z_align)
                       (mult req2_Z_align (inv_pos req2_Z_align Z_align_pos))
                       one).
      * apply mult_comm.
      * apply inv_pos_correct.
Qed.

(* Z_rel 正性已在定义区前移（req2_Z_rel_pos）；此处仅余后续件 *)

(* π_next 逐点正性（Id pi_next_pos L21789 req 版） *)
Lemma req2_pi_next_pos :
  forall (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t),
    req2_pos_dist (req2_pi_next pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t s.
  unfold req2_pi_next.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply mult_positive.
    + apply Hpi_t.
    + apply exp_neg_pos.
Qed.

(* π_next 归一化（Id pi_next_normalized L21401 req 版；批 3 同款真证） *)
Lemma req2_pi_next_normalized :
  forall (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t),
    req (sumf (req2_pi_next pi_t Hpi_t)) one.
Proof.
  intros pi_t Hpi_t.
  apply (req_trans (sumf (req2_pi_next pi_t Hpi_t))
                   (mult (inv_pos (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t))
                         (sumf (fun s => mult (pi_t s)
                                              (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                                  (req2_adv pi_t Hpi_t s)))))))
                   one).
  - exact (sum_linear (inv_pos (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t))
                      (fun s => mult (pi_t s)
                                     (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                         (req2_adv pi_t Hpi_t s)))))).
  - apply (req_trans (mult (inv_pos (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t))
                           (sumf (fun s => mult (pi_t s)
                                                (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                                    (req2_adv pi_t Hpi_t s)))))))
                     (mult (inv_pos (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t))
                           (req2_Z_rel pi_t Hpi_t))
                     one).
    + apply (req_mult_compat (inv_pos (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t))
                             (inv_pos (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t))
                             (sumf (fun s => mult (pi_t s)
                                                  (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                                      (req2_adv pi_t Hpi_t s))))))
                             (req2_Z_rel pi_t Hpi_t)).
      * apply req_refl.
      * exact (req_sym (req2_Z_rel pi_t Hpi_t)
                       (sumf (fun s => mult (pi_t s)
                                            (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                                (req2_adv pi_t Hpi_t s))))))
                       (req_refl (req2_Z_rel pi_t Hpi_t))).
    + apply (req_trans (mult (inv_pos (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t))
                             (req2_Z_rel pi_t Hpi_t))
                       (mult (req2_Z_rel pi_t Hpi_t) (inv_pos (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t)))
                       one).
      * apply mult_comm.
      * apply inv_pos_correct.
Qed.

(* 序代数辅件（Id plus_opp_le_zero/plusA_opp_cancel_le L23119/23130
   的 req 版；批 3 同款真证） *)
Lemma req2_plus_opp_le_zero : forall B C : R, le C B -> le (plus (opp B) C) zero.
Proof.
  intros B C HCB.
  apply (le_id_r (plus (opp B) C) (plus (opp B) B) zero
                 (req_trans (plus (opp B) B) (plus B (opp B)) zero
                            (plus_comm (opp B) B) (plus_opp B))).
  apply (le_plus_compat (opp B) (opp B) C B (le_refl (opp B)) HCB).
Qed.

Lemma req2_plusA_opp_cancel_le :
  forall A B C : R, le C B -> le (plus A (plus (opp B) C)) A.
Proof.
  intros A B C HCB.
  apply (le_id_r (plus A (plus (opp B) C)) (plus A zero) A (plus_zero A)).
  apply (le_plus_compat A A (plus (opp B) C) zero (le_refl A)
                        (req2_plus_opp_le_zero B C HCB)).
Qed.

(* le 0 ≤ b−a ⟹ a ≤ b（Id le_nonneg_minus L21805 req 版；
   消费批 3 交接件 req_le_of_minus_nonneg 同形——本节自证 3 行链） *)
Lemma req2_le_of_minus_nonneg : forall a b : R,
  le zero (req_minus b a) -> le a b.
Proof.
  intros a b H.
  apply (le_id_r a (plus a (req_minus b a)) b
                 (req_minus_plus_cancel a b)).
  exact (req_le_plus_nonneg_r a (req_minus b a) H).
Qed.

(* 迭代 Fixpoint req 化（Id policy_iterate L22879 同构；sigT 打包） *)
Fixpoint req2_iter (t : nat) (pi : S -> R) (Hpi : req2_pos_dist pi) :
  { pi' : S -> R & req2_pos_dist pi' } :=
  match t with
  | 0%nat => existT _ pi Hpi
  | Datatypes.S m =>
      let p := req2_iter m pi Hpi in
      existT _ (req2_pi_next (projT1 p) (projT2 p)) (req2_pi_next_pos (projT1 p) (projT2 p))
  end.

(* R 层幂 req 化（Id r_pow L14071 同形） *)
Fixpoint req2_r_pow (x : R) (n : nat) : R :=
  match n with
  | 0%nat => one
  | Datatypes.S m => mult x (req2_r_pow x m)
  end.

(* 迭代保持归一化（Id policy_iter_norm L22890 req 版） *)
Lemma req2_iter_norm :
  forall (t : nat) (pi : S -> R) (Hpi : req2_pos_dist pi),
    req2_norm_one pi -> req2_norm_one (projT1 (req2_iter t pi Hpi)).
Proof.
  intros t pi Hpi Hnorm.
  induction t as [| m IH].
  - exact Hnorm.
  - exact (req2_pi_next_normalized (projT1 (req2_iter m pi Hpi))
                                   (projT2 (req2_iter m pi Hpi))).
Qed.

(* ============ P 组：纯环代数辅件（t12/t13 链共用） ============ *)

(* req_minus 双端兼容 *)
Lemma req2_minus_compat : forall a b c d : R,
  req a b -> req c d -> req (req_minus a c) (req_minus b d).
Proof.
  intros a b c d Hab Hcd. unfold req_minus.
  exact (req_plus_compat a b (opp c) (opp d) Hab (req_opp_compat c d Hcd)).
Qed.

(* β·opp(x+y) == opp(β·x) + opp(β·y) *)
Lemma req2_opp_distrib_collapse : forall b x y : R,
  req (mult b (opp (plus x y))) (plus (opp (mult b x)) (opp (mult b y))).
Proof.
  intros b x y.
  apply (req_trans (mult b (opp (plus x y)))
                   (opp (mult b (plus x y)))
                   (plus (opp (mult b x)) (opp (mult b y)))).
  - apply req_opp_mult_l.
  - apply (req_trans (opp (mult b (plus x y)))
                     (opp (plus (mult b x) (mult b y)))
                     (plus (opp (mult b x)) (opp (mult b y)))).
    + apply (req_opp_compat (mult b (plus x y)) (plus (mult b x) (mult b y))).
      apply distrib.
    + exact (req_opp_plus (mult b x) (mult b y)).
Qed.

(* p·(a·x) == a·(p·x) *)
Lemma req2_ptimes_swap : forall p a x : R,
  req (mult p (mult a x)) (mult a (mult p x)).
Proof.
  intros p a x.
  apply (req_trans (mult p (mult a x)) (mult (mult p a) x)
                   (mult a (mult p x))).
  - apply mult_assoc.
  - apply (req_trans (mult (mult p a) x) (mult (mult a p) x)
                     (mult a (mult p x))
                     (req_mult_compat (mult p a) (mult a p) x x
                                      (mult_comm p a) (req_refl x))
                     (req_sym (mult a (mult p x)) (mult (mult a p) x)
                              (mult_assoc a p x))).
Qed.

(* (−u + w) + u == w *)
Lemma req2_opp_cancel_form : forall u w : R,
  req (plus (plus (opp u) w) u) w.
Proof.
  intros u w.
  apply (req_trans (plus (plus (opp u) w) u)
                   (plus u (plus (opp u) w)) w).
  - apply plus_comm.
  - apply (req_trans (plus u (plus (opp u) w))
                     (plus (plus u (opp u)) w) w).
    + apply plus_assoc.
    + apply (req_trans (plus (plus u (opp u)) w) (plus zero w) w
                       (req_plus_compat (plus u (opp u)) zero w w
                                        (plus_opp u) (req_refl w))
                       (req_plus_zero_l w)).
Qed.

(* iv·(β·x) == x（iv := 1/β） *)
Lemma req2_mult_inv_absorb : forall x : R,
  req (mult (inv_pos beta beta_pos) (mult beta x)) x.
Proof.
  intro x.
  apply (req_trans (mult (inv_pos beta beta_pos) (mult beta x))
                   (mult (mult (inv_pos beta beta_pos) beta) x) x).
  - apply mult_assoc.
  - apply (req_trans (mult (mult (inv_pos beta beta_pos) beta) x)
                     (mult one x) x).
    + apply (req_mult_compat (mult (inv_pos beta beta_pos) beta) one x x
                             (req_trans (mult (inv_pos beta beta_pos) beta)
                                        (mult beta (inv_pos beta beta_pos)) one
                                        (mult_comm (inv_pos beta beta_pos) beta)
                                        (inv_pos_correct beta beta_pos))
                             (req_refl x)).
    + apply req_mult_one_l.
Qed.

(* inv(β)·u == v ⟹ u == β·v *)
Lemma req2_beta_inv_absorb : forall u v : R,
  req (mult (inv_pos beta beta_pos) u) v -> req u (mult beta v).
Proof.
  intros u v H.
  apply (req_trans u (mult beta (mult (inv_pos beta beta_pos) u))
                    (mult beta v)).
  - apply (req_sym (mult beta (mult (inv_pos beta beta_pos) u)) u).
    apply (req_trans (mult beta (mult (inv_pos beta beta_pos) u))
                     (mult (mult beta (inv_pos beta beta_pos)) u) u).
    + apply mult_assoc.
    + apply (req_trans (mult (mult beta (inv_pos beta beta_pos)) u)
                       (mult (mult (inv_pos beta beta_pos) beta) u) u
                       (req_mult_compat (mult beta (inv_pos beta beta_pos))
                                        (mult (inv_pos beta beta_pos) beta) u u
                                        (mult_comm beta (inv_pos beta beta_pos))
                                        (req_refl u))
                       (req_trans (mult (mult (inv_pos beta beta_pos) beta) u)
                                  (mult one u) u
                                  (req_mult_compat (mult (inv_pos beta beta_pos) beta) one
                                                   u u
                                                   (req_trans (mult (inv_pos beta beta_pos) beta)
                                                              (mult beta (inv_pos beta beta_pos)) one
                                                              (mult_comm (inv_pos beta beta_pos) beta)
                                                              (inv_pos_correct beta beta_pos))
                                                   (req_refl u))
                                  (req_mult_one_l u))).
  - apply (req_mult_compat beta beta
                           (mult (inv_pos beta beta_pos) u) v (req_refl beta) H).
Qed.

(* β·((η·inv β)·a) == η·a（Id beta_eta_inv_absorb_t12 L21607 req 版） *)
Lemma req2_beta_eta_inv_absorb : forall a : R,
  req (mult beta (mult (mult eta (inv_pos beta beta_pos)) a)) (mult eta a).
Proof.
  intro a.
  apply (req_trans (mult beta (mult (mult eta (inv_pos beta beta_pos)) a))
                   (mult (mult beta (mult eta (inv_pos beta beta_pos))) a)
                   (mult eta a)).
  - apply mult_assoc.
  - apply (req_trans (mult (mult beta (mult eta (inv_pos beta beta_pos))) a)
                     (mult (mult eta (mult beta (inv_pos beta beta_pos))) a)
                     (mult eta a)).
    + apply (req_mult_compat (mult beta (mult eta (inv_pos beta beta_pos)))
                             (mult eta (mult beta (inv_pos beta beta_pos)))
                             a a
                             (req2_ptimes_swap beta eta (inv_pos beta beta_pos))
                             (req_refl a)).
    + apply (req_trans (mult (mult eta (mult beta (inv_pos beta beta_pos))) a)
                       (mult (mult eta one) a) (mult eta a)
                       (req_mult_compat (mult eta (mult beta (inv_pos beta beta_pos)))
                                        (mult eta one) a a
                                        (req_mult_compat eta eta
                                         (mult beta (inv_pos beta beta_pos)) one
                                         (req_refl eta)
                                         (inv_pos_correct beta beta_pos))
                                        (req_refl a))
                       (req_trans (mult (mult eta one) a)
                                  (mult eta (mult one a))
                                  (mult eta a)
                                  (req_sym (mult eta (mult one a))
                                           (mult (mult eta one) a)
                                           (mult_assoc eta one a))
                                  (req_mult_compat eta eta (mult one a) a
                                                   (req_refl eta) (req_mult_one_l a)))).
Qed.

(* η·a + (1−η)·a == a（Id eta_absorb_t12 L21850 req 版） *)
Lemma req2_eta_absorb : forall a : R,
  req (plus (mult eta a) (mult (req_minus one eta) a)) a.
Proof.
  intro a. unfold req_minus.
  apply (req_trans (plus (mult eta a) (mult (plus one (opp eta)) a))
                   (plus (mult eta a) (plus (mult one a) (mult (opp eta) a)))
                   a).
  - apply (req_plus_compat (mult eta a) (mult eta a)
                           (mult (plus one (opp eta)) a)
                           (plus (mult one a) (mult (opp eta) a))
                           (req_refl (mult eta a))
                           (req_mult_plus_distr_r one (opp eta) a)).
  - apply (req_trans (plus (mult eta a) (plus (mult one a) (mult (opp eta) a)))
                     (plus (plus (mult eta a) (mult one a)) (mult (opp eta) a))
                     a).
    + apply plus_assoc.
    + apply (req_trans (plus (plus (mult eta a) (mult one a)) (mult (opp eta) a))
                       (plus (plus (mult eta a) a) (mult (opp eta) a))
                       a).
      * apply (req_plus_compat (plus (mult eta a) (mult one a))
                               (plus (mult eta a) a)
                               (mult (opp eta) a) (mult (opp eta) a)
                               (req_plus_compat (mult eta a) (mult eta a)
                                                (mult one a) a
                                                (req_refl (mult eta a))
                                                (req_mult_one_l a))
                               (req_refl (mult (opp eta) a))).
      * apply (req_trans (plus (plus (mult eta a) a) (mult (opp eta) a))
                         (plus (plus a (mult eta a)) (mult (opp eta) a))
                         a).
        -- apply (req_plus_compat (plus (mult eta a) a) (plus a (mult eta a))
                                  (mult (opp eta) a) (mult (opp eta) a)
                                  (plus_comm (mult eta a) a) (req_refl (mult (opp eta) a))).
        -- apply (req_trans (plus (plus a (mult eta a)) (mult (opp eta) a))
                            (plus a (plus (mult eta a) (mult (opp eta) a)))
                            a).
           ++ exact (req_sym (plus a (plus (mult eta a) (mult (opp eta) a)))
                             (plus (plus a (mult eta a)) (mult (opp eta) a))
                             (plus_assoc a (mult eta a) (mult (opp eta) a))).
           ++ apply (req_trans (plus a (plus (mult eta a) (mult (opp eta) a)))
                               (plus a (plus (mult eta a) (opp (mult eta a))))
                               a).
              ** apply (req_plus_compat a a
                                        (plus (mult eta a) (mult (opp eta) a))
                                        (plus (mult eta a) (opp (mult eta a)))
                                        (req_refl a)
                                        (req_plus_compat (mult eta a) (mult eta a)
                                                         (mult (opp eta) a)
                                                         (opp (mult eta a))
                                                         (req_refl (mult eta a))
                                                         (req_opp_mult_r eta a))).
              ** apply (req_trans (plus a (plus (mult eta a) (opp (mult eta a))))
                                  (plus a zero) a).
                 --- apply (req_plus_compat a a
                                            (plus (mult eta a) (opp (mult eta a))) zero
                                            (req_refl a) (plus_opp (mult eta a))).
                 --- apply plus_zero.
Qed.

(* ============ T12 组：策略改进深链（Id L21273-22065 req 化） ============ *)

(* 引理 A：Boltzmann 因子桥（Id boltzmann_factor_bridge L21273 req 版） *)
Lemma req2_boltzmann_factor_bridge :
  forall (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t) (s : S),
    req (exp_neg (mult (inv_pos beta beta_pos) (req2_energy_t pi_t Hpi_t s)))
        (mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                           (req2_adv pi_t Hpi_t s))))).
Proof.
  intros pi_t Hpi_t s.
  set (iv := inv_pos beta beta_pos).
  set (lg := log (pi_t s) (Hpi_t s)).
  set (A := req2_adv pi_t Hpi_t s).
  (* H1a : iv·opp(η·A) == opp(M·A) *)
  assert (H1a : req (mult iv (opp (mult eta A))) (opp (mult (mult eta iv) A))).
  { apply (req_trans (mult iv (opp (mult eta A)))
                     (opp (mult iv (mult eta A)))
                     (opp (mult (mult eta iv) A))).
    - apply req_opp_mult_l.
    - apply (req_opp_compat (mult iv (mult eta A)) (mult (mult eta iv) A)).
      apply (req_trans (mult iv (mult eta A)) (mult (mult iv eta) A)
                       (mult (mult eta iv) A)).
      + apply mult_assoc.
      + apply (req_mult_compat (mult iv eta) (mult eta iv) A A
                               (mult_comm iv eta) (req_refl A)). }
  (* H1 : iv·E_t == (opp(M·A)) − lg *)
  assert (H1 : req (mult iv (req2_energy_t pi_t Hpi_t s))
                   (req_minus (opp (mult (mult eta iv) A)) lg)).
  { apply (req_trans (mult iv (req2_energy_t pi_t Hpi_t s))
                     (req_minus (mult iv (opp (mult eta A))) (mult iv (mult beta lg)))
                     (req_minus (opp (mult (mult eta iv) A)) lg)).
    - unfold req2_energy_t. exact (req_mult_minus_distr_l iv (opp (mult eta A)) (mult beta lg)).
    - exact (req2_minus_compat _ _ _ _ H1a (req2_mult_inv_absorb lg)). }
  (* H4 : iv·E_t == opp(M·A + lg) *)
  assert (H4 : req (mult iv (req2_energy_t pi_t Hpi_t s))
                   (opp (plus (mult (mult eta iv) A) lg))).
  { apply (req_trans (mult iv (req2_energy_t pi_t Hpi_t s))
                     (req_minus (opp (mult (mult eta iv) A)) lg)
                     (opp (plus (mult (mult eta iv) A) lg))).
    - exact H1.
    - exact (req_sym (opp (plus (mult (mult eta iv) A) lg))
                     (plus (opp (mult (mult eta iv) A)) (opp lg))
                     (req_opp_plus (mult (mult eta iv) A) lg)). }
  (* H5 : e^{iv·E_t} == e^{−M·A}·e^{−lg} *)
  assert (H5 : req (exp_neg (mult iv (req2_energy_t pi_t Hpi_t s)))
                   (mult (exp_neg (opp (mult (mult eta iv) A))) (exp_neg (opp lg)))).
  { apply (req_trans (exp_neg (mult iv (req2_energy_t pi_t Hpi_t s)))
                     (exp_neg (opp (plus (mult (mult eta iv) A) lg)))
                     (mult (exp_neg (opp (mult (mult eta iv) A))) (exp_neg (opp lg)))).
    - apply exp_neg_req_compat_setoid. exact H4.
    - exact (req_exp_neg_opp_plus (mult (mult eta iv) A) lg). }
  apply (req_trans (exp_neg (mult iv (req2_energy_t pi_t Hpi_t s)))
                   (mult (exp_neg (opp (mult (mult eta iv) A))) (exp_neg (opp lg)))
                   (mult (pi_t s) (exp_neg (opp (mult (mult eta iv) A))))).
  - exact H5.
  - apply (req_trans (mult (exp_neg (opp (mult (mult eta iv) A))) (exp_neg (opp lg)))
                     (mult (exp_neg (opp (mult (mult eta iv) A))) (pi_t s))
                     (mult (pi_t s) (exp_neg (opp (mult (mult eta iv) A))))).
    + apply (req_mult_compat (exp_neg (opp (mult (mult eta iv) A)))
                             (exp_neg (opp (mult (mult eta iv) A)))
                             (exp_neg (opp lg)) (pi_t s)
                             (req_refl (exp_neg (opp (mult (mult eta iv) A))))
                             (req_exp_neg_opp_log (pi_t s) (Hpi_t s))).
    + apply mult_comm.
Qed.

(* 引理 A'：Boltzmann 因子桥的 Z 形（rel_free_energy_decomp 的
   能量-对数点态恒等式原料） *)
Lemma req2_bridge_Z :
  forall (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t) (s : S),
    req (exp_neg (mult (inv_pos beta beta_pos) (req2_energy_t pi_t Hpi_t s)))
        (mult (req2_pi_next pi_t Hpi_t s) (req2_Z_rel pi_t Hpi_t)).
Proof.
  intros pi_t Hpi_t s.
  set (iv := inv_pos beta beta_pos).
  set (Z := req2_Z_rel pi_t Hpi_t).
  set (ivZ := inv_pos (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t)).
  set (W := mult (pi_t s) (exp_neg (opp (mult (mult eta iv) (req2_adv pi_t Hpi_t s))))).
  (* C : (ivZ·W)·Z == W（inv 消去） *)
  assert (HC : req (mult (mult ivZ W) Z) W).
  { exact (req_trans (mult (mult ivZ W) Z)
                     (mult ivZ (mult W Z))
                     W
                     (req_sym (mult ivZ (mult W Z)) (mult (mult ivZ W) Z)
                              (mult_assoc ivZ W Z))
                     (req_trans (mult ivZ (mult W Z))
                                (mult (mult ivZ Z) W)
                                W
                                (req_trans (mult ivZ (mult W Z))
                                           (mult ivZ (mult Z W))
                                           (mult (mult ivZ Z) W)
                                           (req_mult_compat ivZ ivZ (mult W Z) (mult Z W)
                                                            (req_refl ivZ) (mult_comm W Z))
                                           (mult_assoc ivZ Z W))
                                (req_trans (mult (mult ivZ Z) W) (mult one W) W
                                           (req_mult_compat (mult ivZ Z) one W W
                                                            (req_trans (mult ivZ Z) (mult Z ivZ) one
                                                                       (mult_comm ivZ Z)
                                                                       (inv_pos_correct (req2_Z_rel pi_t Hpi_t)
                                                                                        (req2_Z_rel_pos pi_t Hpi_t)))
                                                            (req_refl W))
                                           (req_mult_one_l W)))). }
  apply (req_trans (exp_neg (mult iv (req2_energy_t pi_t Hpi_t s)))
                   W
                   (mult (req2_pi_next pi_t Hpi_t s) Z)).
  - exact (req2_boltzmann_factor_bridge pi_t Hpi_t s).
  - unfold req2_pi_next.
    exact (req_sym (mult (mult ivZ W) (req2_Z_rel pi_t Hpi_t)) W HC).
Qed.

(* 引理 B：Z_rel 的 Boltzmann 形式（Id Z_rel_boltzmann_form L21337 req 版） *)
Lemma req2_Z_rel_boltzmann_form :
  forall (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t),
    req (req2_Z_rel pi_t Hpi_t)
        (sumf (fun s => exp_neg (mult (inv_pos beta beta_pos)
                                      (req2_energy_t pi_t Hpi_t s)))).
Proof.
  intros pi_t Hpi_t.
  unfold req2_Z_rel.
  apply (sum_ext (fun s => mult (pi_t s)
                                (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                    (req2_adv pi_t Hpi_t s)))))
                 (fun s => exp_neg (mult (inv_pos beta beta_pos)
                                         (req2_energy_t pi_t Hpi_t s)))).
  intro s.
  exact (req_sym (exp_neg (mult (inv_pos beta beta_pos)
                                (req2_energy_t pi_t Hpi_t s)))
                 (mult (pi_t s)
                       (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                           (req2_adv pi_t Hpi_t s)))))
                 (req2_boltzmann_factor_bridge pi_t Hpi_t s)).
Qed.

(* 引理 C：π_next 的对数展开（Id pi_next_log_decomp L21350 req 版；
   接口缺口桥 log_inv_exp_neg_req（req2_log_exp_neg）） *)
Lemma req2_pi_next_log_decomp :
  forall (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t) (s : S),
    req (log (req2_pi_next pi_t Hpi_t s) (req2_pi_next_pos pi_t Hpi_t s))
        (plus (log (pi_t s) (Hpi_t s))
              (plus (mult (mult eta (inv_pos beta beta_pos))
                          (req2_adv pi_t Hpi_t s))
                    (opp (log (req2_Z_rel pi_t Hpi_t)
                              (req2_Z_rel_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t s.
  set (iv := inv_pos beta beta_pos).
  set (lg := log (pi_t s) (Hpi_t s)).
  set (lgZ := log (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t)).
  set (X := mult (mult eta iv) (req2_adv pi_t Hpi_t s)).
  set (expm := exp_neg (opp X)).
  set (ivZ := inv_pos (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t)).
  (* 证人显式（Qed 件不可 delta；先经 log_req_compat 开门，其后全透明） *)
  set (Hp1 := inv_pos_pos (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t)).
  set (Hp2 := mult_positive (pi_t s) expm (Hpi_t s) (exp_neg_pos (opp X))).
  set (HpI := mult_positive ivZ (mult (pi_t s) expm) Hp1 Hp2).
  set (Wit := req2_pi_next_pos pi_t Hpi_t s).
  assert (Hstep12 : req (log (mult ivZ (mult (pi_t s) expm)) HpI)
                        (plus (opp lgZ) (plus lg X))).
  { exact (req_trans (log (mult ivZ (mult (pi_t s) expm)) HpI)
           (plus (opp lgZ) (log (mult (pi_t s) expm) Hp2))
           (plus (opp lgZ) (plus lg X))
           (req_trans (log (mult ivZ (mult (pi_t s) expm)) HpI)
                      (plus (log ivZ Hp1) (log (mult (pi_t s) expm) Hp2))
                      (plus (opp lgZ) (log (mult (pi_t s) expm) Hp2))
                      (log_mult ivZ (mult (pi_t s) expm) Hp1 Hp2)
                      (req_plus_compat (log ivZ Hp1) (opp lgZ)
                                       (log (mult (pi_t s) expm) Hp2)
                                       (log (mult (pi_t s) expm) Hp2)
                                       (req2_log_inv_one_inv (req2_Z_rel pi_t Hpi_t)
                                                             (req2_Z_rel_pos pi_t Hpi_t))
                                       (req_refl (log (mult (pi_t s) expm) Hp2))))
           (req_plus_compat (opp lgZ) (opp lgZ)
                            (log (mult (pi_t s) expm) Hp2) (plus lg X)
                            (req_refl (opp lgZ))
                            (req_trans (log (mult (pi_t s) expm) Hp2)
                                       (plus lg (log expm (exp_neg_pos (opp X))))
                                       (plus lg X)
                                       (log_mult (pi_t s) expm (Hpi_t s)
                                                 (exp_neg_pos (opp X)))
                                       (req_plus_compat lg lg
                                                        (log expm (exp_neg_pos (opp X))) X
                                                        (req_refl lg)
                                                        (req_trans
                                                           (log expm (exp_neg_pos (opp X)))
                                                           (opp (opp X)) X
                                                           (req2_log_exp_neg (opp X))
                                                           (req_double_neg X)))))). }
  exact (req_trans (log (req2_pi_next pi_t Hpi_t s) Wit)
                   (log (mult ivZ (mult (pi_t s) expm)) HpI)
                   (plus lg (plus X (opp lgZ)))
                   (log_req_compat (req2_pi_next pi_t Hpi_t s)
                                   (mult ivZ (mult (pi_t s) expm))
                                   Wit HpI (req_refl (req2_pi_next pi_t Hpi_t s)))
                   (req_trans (log (mult ivZ (mult (pi_t s) expm)) HpI)
                              (plus (opp lgZ) (plus lg X))
                              (plus lg (plus X (opp lgZ)))
                              Hstep12
                              (req_trans (plus (opp lgZ) (plus lg X))
                              (plus (plus (opp lgZ) lg) X)
                              (plus lg (plus X (opp lgZ)))
                              (plus_assoc (opp lgZ) lg X)
                              (req_trans (plus (plus (opp lgZ) lg) X)
                                         (plus (plus lg (opp lgZ)) X)
                                         (plus lg (plus X (opp lgZ)))
                                         (req_plus_compat (plus (opp lgZ) lg)
                                                          (plus lg (opp lgZ)) X X
                                                          (plus_comm (opp lgZ) lg)
                                                          (req_refl X))
                                         (req_trans (plus (plus lg (opp lgZ)) X)
                                                    (plus lg (plus (opp lgZ) X))
                                                    (plus lg (plus X (opp lgZ)))
                                                    (req_sym (plus lg (plus (opp lgZ) X))
                                                             (plus (plus lg (opp lgZ)) X)
                                                             (plus_assoc lg (opp lgZ) X))
                                                    (req_plus_compat lg lg
                                                                     (plus (opp lgZ) X)
                                                                     (plus X (opp lgZ))
                                                                     (req_refl lg)
                                                                     (plus_comm (opp lgZ) X))))))).
Qed.

(* ============ T12 组 II：F_t 分解与单调性链 ============ *)


Lemma req2_rel_ent_minus : forall (p q : S -> R) (Hp : req2_pos_dist p) (Hq : req2_pos_dist q),
  req (req2_rel_ent p q Hp Hq)
      (req_minus (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                 (sumf (fun s => mult (p s) (log (q s) (Hq s))))).
Proof.
  intros p q Hp Hq. unfold req2_rel_ent.
  apply (req_trans (sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
                   (sumf (fun s => req_minus (mult (p s) (log (p s) (Hp s)))
                                             (mult (p s) (log (q s) (Hq s)))))
                   (req_minus (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                              (sumf (fun s => mult (p s) (log (q s) (Hq s)))))).
  - apply (sum_ext (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
                   (fun s => req_minus (mult (p s) (log (p s) (Hp s)))
                                       (mult (p s) (log (q s) (Hq s))))).
    intro s. apply req_mult_minus_distr_l.
  - apply req2_sum_minus.
Qed.

(* β·opp(u+v) + β·w == β·w + (opp(β·u) + opp(β·v))（F 坍缩形） *)
Lemma req2_F_collapse : forall (b u v w : R),
  req (plus (mult b (opp (plus u v))) (mult b w))
      (plus (mult b w) (plus (opp (mult b u)) (opp (mult b v)))).
Proof.
  intros b u v w.
  apply (req_trans (plus (mult b (opp (plus u v))) (mult b w))
                   (plus (plus (opp (mult b u)) (opp (mult b v))) (mult b w))
                   (plus (mult b w) (plus (opp (mult b u)) (opp (mult b v))))).
  - apply (req_plus_compat _ _ _ _ (req2_opp_distrib_collapse b u v) (req_refl (mult b w))).
  - apply plus_comm.
Qed.

(* 能量-对数点态恒等式：E_t(s) == β·opp(log π_next(s) + log Z) *)
Lemma req2_energy_log_pt :
  forall (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t) (s : S),
    req (req2_energy_t pi_t Hpi_t s)
        (mult beta (opp (plus (log (req2_pi_next pi_t Hpi_t s) (req2_pi_next_pos pi_t Hpi_t s))
                              (log (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t s.
  set (iv := inv_pos beta beta_pos).
  set (Z := req2_Z_rel pi_t Hpi_t).
  set (Zpos := req2_Z_rel_pos pi_t Hpi_t).
  set (Nps := req2_pi_next pi_t Hpi_t s).
  set (Npos := req2_pi_next_pos pi_t Hpi_t s).
  set (Es := req2_energy_t pi_t Hpi_t s).
  assert (Hlg : req (plus (log Nps Npos) (log Z Zpos)) (opp (mult iv Es))).
  { apply (req_trans (plus (log Nps Npos) (log Z Zpos))
                     (log (mult Nps Z) (mult_positive Nps Z Npos Zpos))
                     (opp (mult iv Es))).
    - exact (req_sym (log (mult Nps Z) (mult_positive Nps Z Npos Zpos))
                     (plus (log Nps Npos) (log Z Zpos))
                     (log_mult Nps Z Npos Zpos)).
    - apply (req_trans (log (mult Nps Z) (mult_positive Nps Z Npos Zpos))
                       (log (exp_neg (mult iv Es)) (exp_neg_pos (mult iv Es)))
                       (opp (mult iv Es))
                       (log_req_compat (mult Nps Z) (exp_neg (mult iv Es))
                                       (mult_positive Nps Z Npos Zpos)
                                       (exp_neg_pos (mult iv Es))
                                       (req_sym (exp_neg (mult iv Es)) (mult Nps Z)
                                                (req2_bridge_Z pi_t Hpi_t s)))
                       (req2_log_exp_neg (mult iv Es))). }
  apply (req2_beta_inv_absorb (req2_energy_t pi_t Hpi_t s)
                              (opp (plus (log Nps Npos) (log Z Zpos)))).
  exact (req_opp_eq (mult iv (req2_energy_t pi_t Hpi_t s))
                    (opp (plus (log Nps Npos) (log Z Zpos)))
                    (req_trans (opp (mult iv (req2_energy_t pi_t Hpi_t s)))
                               (plus (log Nps Npos) (log Z Zpos))
                               (opp (opp (plus (log Nps Npos) (log Z Zpos))))
                               (req_sym (plus (log Nps Npos) (log Z Zpos))
                                        (opp (mult iv (req2_energy_t pi_t Hpi_t s))) Hlg)
                               (req_sym (opp (opp (plus (log Nps Npos) (log Z Zpos))))
                                        (plus (log Nps Npos) (log Z Zpos))
                                        (req_double_neg (plus (log Nps Npos) (log Z Zpos)))))).
Qed.


Lemma req2_sum_E_beta :
  forall (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t)
         (p : S -> R) (Hp : req2_pos_dist p) (Hpn : req (sumf p) one),
    req (sumf (fun s => mult (p s) (req2_energy_t pi_t Hpi_t s)))
        (mult beta (opp (plus (sumf (fun s => mult (p s) (log (req2_pi_next pi_t Hpi_t s) (req2_pi_next_pos pi_t Hpi_t s))))
                              (log (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t p Hp Hpn.
  set (lgN := fun s => log (req2_pi_next pi_t Hpi_t s) (req2_pi_next_pos pi_t Hpi_t s)).
  set (lgZ := log (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t)).
  apply (req_trans (sumf (fun s => mult (p s) (req2_energy_t pi_t Hpi_t s)))
                   (mult beta (sumf (fun s => mult (p s) (opp (plus (lgN s) lgZ)))))
                   (mult beta (opp (plus (sumf (fun s => mult (p s) (lgN s))) lgZ)))).
  - apply (req_trans (sumf (fun s => mult (p s) (req2_energy_t pi_t Hpi_t s)))
                     (sumf (fun s => mult beta (mult (p s) (opp (plus (lgN s) lgZ)))))
                     (mult beta (sumf (fun s => mult (p s) (opp (plus (lgN s) lgZ)))))).
    + apply (sum_ext (fun s => mult (p s) (req2_energy_t pi_t Hpi_t s))
                     (fun s => mult beta (mult (p s) (opp (plus (lgN s) lgZ))))).
      intro s.
      apply (req_trans (mult (p s) (req2_energy_t pi_t Hpi_t s))
                       (mult (p s) (mult beta (opp (plus (lgN s) lgZ))))
                       (mult beta (mult (p s) (opp (plus (lgN s) lgZ))))).
      * exact (req_mult_compat (p s) (p s)
                               (req2_energy_t pi_t Hpi_t s)
                               (mult beta (opp (plus (lgN s) lgZ)))
                               (req_refl (p s))
                               (req2_energy_log_pt pi_t Hpi_t s)).
      * apply req2_ptimes_swap.
    + exact (sum_linear beta (fun s => mult (p s) (opp (plus (lgN s) lgZ)))).
  - apply (req_mult_compat beta beta _ _ (req_refl beta)).
    apply (req_trans (sumf (fun s => mult (p s) (opp (plus (lgN s) lgZ))))
                     (opp (sumf (fun s => mult (p s) (plus (lgN s) lgZ))))
                     (opp (plus (sumf (fun s => mult (p s) (lgN s))) lgZ))).
    + apply (req_trans (sumf (fun s => mult (p s) (opp (plus (lgN s) lgZ))))
                       (sumf (fun s => opp (mult (p s) (plus (lgN s) lgZ))))
                       (opp (sumf (fun s => mult (p s) (plus (lgN s) lgZ))))).
      * apply (sum_ext (fun s => mult (p s) (opp (plus (lgN s) lgZ)))
                       (fun s => opp (mult (p s) (plus (lgN s) lgZ)))
                       (fun s => req_opp_mult_l (p s) (plus (lgN s) lgZ))).
      * exact (req2_sum_opp (fun s => mult (p s) (plus (lgN s) lgZ))).
    + apply (req_opp_compat (sumf (fun s => mult (p s) (plus (lgN s) lgZ)))
                            (plus (sumf (fun s => mult (p s) (lgN s))) lgZ)).
      apply (req_trans (sumf (fun s => mult (p s) (plus (lgN s) lgZ)))
                       (plus (sumf (fun s => mult (p s) (lgN s)))
                             (sumf (fun s => mult (p s) lgZ)))
                       (plus (sumf (fun s => mult (p s) (lgN s))) lgZ)).
      * apply (req_trans (sumf (fun s => mult (p s) (plus (lgN s) lgZ)))
                         (sumf (fun s => plus (mult (p s) (lgN s)) (mult (p s) lgZ)))
                         (plus (sumf (fun s => mult (p s) (lgN s)))
                               (sumf (fun s => mult (p s) lgZ)))).
        -- apply (sum_ext (fun s => mult (p s) (plus (lgN s) lgZ))
                          (fun s => plus (mult (p s) (lgN s)) (mult (p s) lgZ))
                          (fun s => distrib (p s) (lgN s) lgZ)).
        -- apply sum_add.
      * apply (req_plus_compat (sumf (fun s => mult (p s) (lgN s)))
                               (sumf (fun s => mult (p s) (lgN s)))
                               _ lgZ (req_refl (sumf (fun s => mult (p s) (lgN s))))
                               (req2_sum_ptimes_const p lgZ Hpn)).
Qed.


Lemma req2_F_t_beta_form :
  forall (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t)
         (p : S -> R) (Hp : req2_pos_dist p) (Hpn : req (sumf p) one),
    req (req2_free_energy (req2_energy_t pi_t Hpi_t) beta p Hp)
        (plus (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
              (plus (opp (mult beta (sumf (fun s => mult (p s) (log (req2_pi_next pi_t Hpi_t s) (req2_pi_next_pos pi_t Hpi_t s))))))
                    (opp (mult beta (log (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t)))))).
Proof.
  intros pi_t Hpi_t p Hp Hpn.
  unfold req2_free_energy.
  set (Slogp := sumf (fun s => mult (p s) (log (p s) (Hp s)))).
  set (Slogn := sumf (fun s => mult (p s) (log (req2_pi_next pi_t Hpi_t s) (req2_pi_next_pos pi_t Hpi_t s)))).
  set (lgZ := log (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t)).
  assert (HSE : req (sumf (fun s => mult (p s) (req2_energy_t pi_t Hpi_t s)))
                    (mult beta (opp (plus Slogn lgZ))))
    by exact (req2_sum_E_beta pi_t Hpi_t p Hp Hpn).
  apply (req_trans (plus (sumf (fun s => mult (p s) (req2_energy_t pi_t Hpi_t s)))
                         (mult beta Slogp))
                   (plus (mult beta (opp (plus Slogn lgZ))) (mult beta Slogp))
                   (plus (mult beta Slogp) (plus (opp (mult beta Slogn)) (opp (mult beta lgZ))))).
  - exact (req_plus_compat _ _ _ _ HSE (req_refl (mult beta Slogp))).
  - exact (req_trans (plus (mult beta (opp (plus Slogn lgZ))) (mult beta Slogp))
                     (plus (plus (opp (mult beta Slogn)) (opp (mult beta lgZ))) (mult beta Slogp))
                     (plus (mult beta Slogp) (plus (opp (mult beta Slogn)) (opp (mult beta lgZ))))
                     (req_plus_compat (mult beta (opp (plus Slogn lgZ)))
                                      (plus (opp (mult beta Slogn)) (opp (mult beta lgZ)))
                                      (mult beta Slogp) (mult beta Slogp)
                                      (req2_opp_distrib_collapse beta Slogn lgZ)
                                      (req_refl (mult beta Slogp)))
                     (plus_comm (plus (opp (mult beta Slogn)) (opp (mult beta lgZ)))
                                (mult beta Slogp))).
Qed.


Lemma req2_F_t_simpl_next :
  forall (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t),
    req (req2_free_energy (req2_energy_t pi_t Hpi_t) beta
                          (req2_pi_next pi_t Hpi_t) (req2_pi_next_pos pi_t Hpi_t))
        (opp (mult beta (log (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t)))).
Proof.
  intros pi_t Hpi_t.
  set (S2 := sumf (fun s => mult (req2_pi_next pi_t Hpi_t s)
                                 (log (req2_pi_next pi_t Hpi_t s) (req2_pi_next_pos pi_t Hpi_t s)))).
  set (lgZ := log (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t)).
  assert (Hnorm : req (sumf (req2_pi_next pi_t Hpi_t)) one)
    by exact (req2_pi_next_normalized pi_t Hpi_t).
  pose proof (req2_F_t_beta_form pi_t Hpi_t (req2_pi_next pi_t Hpi_t)
                                 (req2_pi_next_pos pi_t Hpi_t) Hnorm) as Hbf.
  apply (req_trans _ (plus (mult beta S2)
                           (plus (opp (mult beta S2)) (opp (mult beta lgZ))))
                    (opp (mult beta lgZ))).
  - exact (req_trans (req2_free_energy (req2_energy_t pi_t Hpi_t) beta
                                       (req2_pi_next pi_t Hpi_t)
                                       (req2_pi_next_pos pi_t Hpi_t))
                     (plus (mult beta S2)
                           (plus (opp (mult beta S2)) (opp (mult beta lgZ))))
                     (plus (mult beta S2)
                           (plus (opp (mult beta S2)) (opp (mult beta lgZ))))
                     Hbf (req_refl (plus (mult beta S2)
                                         (plus (opp (mult beta S2)) (opp (mult beta lgZ)))))).
  - apply (req_trans (plus (mult beta S2)
                           (plus (opp (mult beta S2)) (opp (mult beta lgZ))))
                     (plus (plus (mult beta S2) (opp (mult beta S2))) (opp (mult beta lgZ)))
                     (opp (mult beta lgZ))).
    + apply plus_assoc.
    + apply (req_trans (plus (plus (mult beta S2) (opp (mult beta S2))) (opp (mult beta lgZ)))
                       (plus zero (opp (mult beta lgZ)))
                       (opp (mult beta lgZ))).
      * apply (req_plus_compat (plus (mult beta S2) (opp (mult beta S2))) zero
                               (opp (mult beta lgZ)) (opp (mult beta lgZ))
                               (plus_opp (mult beta S2)) (req_refl (opp (mult beta lgZ)))).
      * apply req_plus_zero_l.
Qed.

(* 核心桥：F_t(π_t) == F_t(π_next) + β·KL(π_t‖π_next)
   （Id rel_free_energy_decomp L21441 的 req 版；β·KL 形式） *)
Lemma req2_F_t_rel_decomp :
  forall (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t) (Hnorm : req2_norm_one pi_t),
    req (req2_free_energy (req2_energy_t pi_t Hpi_t) beta pi_t Hpi_t)
        (plus (req2_free_energy (req2_energy_t pi_t Hpi_t) beta
                                (req2_pi_next pi_t Hpi_t) (req2_pi_next_pos pi_t Hpi_t))
              (mult beta (req2_rel_ent pi_t (req2_pi_next pi_t Hpi_t)
                                            Hpi_t (req2_pi_next_pos pi_t Hpi_t)))).
Proof.
  intros pi_t Hpi_t Hnorm.
  set (S1t := sumf (fun s => mult (pi_t s) (log (pi_t s) (Hpi_t s)))).
  set (S1n := sumf (fun s => mult (pi_t s) (log (req2_pi_next pi_t Hpi_t s) (req2_pi_next_pos pi_t Hpi_t s)))).
  set (lgZ := log (req2_Z_rel pi_t Hpi_t) (req2_Z_rel_pos pi_t Hpi_t)).
  assert (Hnorm' : req (sumf (req2_pi_next pi_t Hpi_t)) one)
    by exact (req2_pi_next_normalized pi_t Hpi_t).
  pose proof (req2_F_t_beta_form pi_t Hpi_t pi_t Hpi_t Hnorm) as HFt.
  pose proof (req2_F_t_simpl_next pi_t Hpi_t) as HFn.
  pose proof (req2_rel_ent_minus pi_t (req2_pi_next pi_t Hpi_t)
                                  Hpi_t (req2_pi_next_pos pi_t Hpi_t)) as HK2raw.
  assert (HK2 : req (mult beta (req2_rel_ent pi_t (req2_pi_next pi_t Hpi_t)
                                              Hpi_t (req2_pi_next_pos pi_t Hpi_t)))
                    (plus (mult beta S1t) (opp (mult beta S1n)))).
  { apply (req_trans (mult beta (req2_rel_ent pi_t (req2_pi_next pi_t Hpi_t)
                                               Hpi_t (req2_pi_next_pos pi_t Hpi_t)))
                     (mult beta (req_minus S1t S1n))
                     (plus (mult beta S1t) (opp (mult beta S1n)))).
    - apply (req_mult_compat beta beta _ _ (req_refl beta)).
      exact HK2raw.
    - exact (req_mult_minus_distr_l beta S1t S1n). }
  apply (req_trans (req2_free_energy (req2_energy_t pi_t Hpi_t) beta pi_t Hpi_t)
                   (plus (mult beta S1t) (plus (opp (mult beta S1n)) (opp (mult beta lgZ))))
                   (plus (req2_free_energy (req2_energy_t pi_t Hpi_t) beta
                                           (req2_pi_next pi_t Hpi_t)
                                           (req2_pi_next_pos pi_t Hpi_t))
                         (mult beta (req2_rel_ent pi_t (req2_pi_next pi_t Hpi_t)
                                                       Hpi_t (req2_pi_next_pos pi_t Hpi_t))))).
  - exact HFt.
  - apply (req_trans (plus (mult beta S1t) (plus (opp (mult beta S1n)) (opp (mult beta lgZ))))
                     (plus (plus (mult beta S1t) (opp (mult beta S1n))) (opp (mult beta lgZ)))
                     (plus (req2_free_energy (req2_energy_t pi_t Hpi_t) beta
                                             (req2_pi_next pi_t Hpi_t)
                                             (req2_pi_next_pos pi_t Hpi_t))
                           (mult beta (req2_rel_ent pi_t (req2_pi_next pi_t Hpi_t)
                                                         Hpi_t (req2_pi_next_pos pi_t Hpi_t))))).
    + apply plus_assoc.
    + apply (req_sym (plus (req2_free_energy (req2_energy_t pi_t Hpi_t) beta
                                             (req2_pi_next pi_t Hpi_t)
                                             (req2_pi_next_pos pi_t Hpi_t))
                           (mult beta (req2_rel_ent pi_t (req2_pi_next pi_t Hpi_t)
                                                         Hpi_t (req2_pi_next_pos pi_t Hpi_t))))
                     (plus (plus (mult beta S1t) (opp (mult beta S1n))) (opp (mult beta lgZ)))).
      apply (req_trans (plus (req2_free_energy (req2_energy_t pi_t Hpi_t) beta
                                               (req2_pi_next pi_t Hpi_t)
                                               (req2_pi_next_pos pi_t Hpi_t))
                             (mult beta (req2_rel_ent pi_t (req2_pi_next pi_t Hpi_t)
                                                           Hpi_t (req2_pi_next_pos pi_t Hpi_t))))
                       (plus (opp (mult beta lgZ)) (plus (mult beta S1t) (opp (mult beta S1n))))
                       (plus (plus (mult beta S1t) (opp (mult beta S1n))) (opp (mult beta lgZ)))).
      * apply (req_plus_compat (req2_free_energy (req2_energy_t pi_t Hpi_t) beta
                                                 (req2_pi_next pi_t Hpi_t)
                                                 (req2_pi_next_pos pi_t Hpi_t))
                               (opp (mult beta lgZ))
                               (mult beta (req2_rel_ent pi_t (req2_pi_next pi_t Hpi_t)
                                                             Hpi_t (req2_pi_next_pos pi_t Hpi_t)))
                               (plus (mult beta S1t) (opp (mult beta S1n)))
                               HFn HK2).
      * apply plus_comm.
Qed.

(* F_t(π_t) == opp(η·Σ π_t·A_t)（Id F_t_simpl_t L21556 req 版；纯代数） *)
Lemma req2_F_t_simpl_t :
  forall (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t),
    req (req2_free_energy (req2_energy_t pi_t Hpi_t) beta pi_t Hpi_t)
        (opp (mult eta (sumf (fun s => mult (pi_t s) (req2_adv pi_t Hpi_t s))))).
Proof.
  intros pi_t Hpi_t.
  unfold req2_free_energy.
  set (SAt := sumf (fun s => mult (pi_t s) (req2_adv pi_t Hpi_t s))).
  set (S1t := sumf (fun s => mult (pi_t s) (log (pi_t s) (Hpi_t s)))).
  assert (HSE : req (sumf (fun s => mult (pi_t s) (req2_energy_t pi_t Hpi_t s)))
                    (req_minus (opp (mult eta SAt)) (mult beta S1t))).
  { apply (req_trans (sumf (fun s => mult (pi_t s) (req2_energy_t pi_t Hpi_t s)))
                     (sumf (fun s => req_minus (mult (pi_t s) (opp (mult eta (req2_adv pi_t Hpi_t s))))
                                               (mult (pi_t s) (mult beta (log (pi_t s) (Hpi_t s))))))
                     (req_minus (opp (mult eta SAt)) (mult beta S1t))).
    - apply (sum_ext (fun s => mult (pi_t s) (req2_energy_t pi_t Hpi_t s))
                     (fun s => req_minus (mult (pi_t s) (opp (mult eta (req2_adv pi_t Hpi_t s))))
                                         (mult (pi_t s) (mult beta (log (pi_t s) (Hpi_t s)))))).
      intro s. unfold req2_energy_t. apply req_mult_minus_distr_l.
    - apply (req_trans (sumf (fun s => req_minus (mult (pi_t s) (opp (mult eta (req2_adv pi_t Hpi_t s))))
                                                 (mult (pi_t s) (mult beta (log (pi_t s) (Hpi_t s))))))
                       (req_minus (sumf (fun s => mult (pi_t s) (opp (mult eta (req2_adv pi_t Hpi_t s)))))
                                  (sumf (fun s => mult (pi_t s) (mult beta (log (pi_t s) (Hpi_t s))))))
                       (req_minus (opp (mult eta SAt)) (mult beta S1t))).
      + exact (req2_sum_minus (fun s => mult (pi_t s) (opp (mult eta (req2_adv pi_t Hpi_t s))))
                              (fun s => mult (pi_t s) (mult beta (log (pi_t s) (Hpi_t s))))).
      + exact (req2_minus_compat _ _ _ _
                (req2_sum_ptimes_opp_scal pi_t eta (fun s => req2_adv pi_t Hpi_t s))
                (req2_sum_ptimes_scal pi_t beta (fun s => log (pi_t s) (Hpi_t s)))). }
  apply (req_trans (plus (sumf (fun s => mult (pi_t s) (req2_energy_t pi_t Hpi_t s)))
                         (mult beta S1t))
                   (plus (req_minus (opp (mult eta SAt)) (mult beta S1t)) (mult beta S1t))
                   (opp (mult eta SAt))).
  - exact (req_plus_compat _ _ _ _ HSE (req_refl (mult beta S1t))).
  - apply (req_trans (plus (req_minus (opp (mult eta SAt)) (mult beta S1t)) (mult beta S1t))
                     (plus (mult beta S1t) (req_minus (opp (mult eta SAt)) (mult beta S1t)))
                     (opp (mult eta SAt))
                     (plus_comm (req_minus (opp (mult eta SAt)) (mult beta S1t)) (mult beta S1t))
                     (req_minus_plus_cancel (mult beta S1t) (opp (mult eta SAt)))).
Qed.

(* F_t(π_next) == opp(η·Σ Np·A) + β·KL(π_next‖π_t)
   （Id F_t_simpl_next_kl L21695 req 版；纯代数 + rel_ent_minus） *)
Lemma req2_F_t_simpl_next_kl :
  forall (pi_t : S -> R) (Hpi_t : req2_pos_dist pi_t),
    req (req2_free_energy (req2_energy_t pi_t Hpi_t) beta
                          (req2_pi_next pi_t Hpi_t) (req2_pi_next_pos pi_t Hpi_t))
        (plus (opp (mult eta (sumf (fun s => mult (req2_pi_next pi_t Hpi_t s)
                                                   (req2_adv pi_t Hpi_t s)))))
              (mult beta (req2_rel_ent (req2_pi_next pi_t Hpi_t) pi_t
                                       (req2_pi_next_pos pi_t Hpi_t) Hpi_t))).
Proof.
  intros pi_t Hpi_t.
  unfold req2_free_energy.
  set (SAn := sumf (fun s => mult (req2_pi_next pi_t Hpi_t s) (req2_adv pi_t Hpi_t s))).
  set (S1n := sumf (fun s => mult (req2_pi_next pi_t Hpi_t s) (log (pi_t s) (Hpi_t s)))).
  set (S2 := sumf (fun s => mult (req2_pi_next pi_t Hpi_t s)
                                 (log (req2_pi_next pi_t Hpi_t s) (req2_pi_next_pos pi_t Hpi_t s)))).
  assert (HSE : req (sumf (fun s => mult (req2_pi_next pi_t Hpi_t s)
                                         (req2_energy_t pi_t Hpi_t s)))
                    (req_minus (opp (mult eta SAn)) (mult beta S1n))).
  { apply (req_trans (sumf (fun s => mult (req2_pi_next pi_t Hpi_t s)
                                          (req2_energy_t pi_t Hpi_t s)))
                     (sumf (fun s => req_minus (mult (req2_pi_next pi_t Hpi_t s)
                                                     (opp (mult eta (req2_adv pi_t Hpi_t s))))
                                               (mult (req2_pi_next pi_t Hpi_t s)
                                                     (mult beta (log (pi_t s) (Hpi_t s))))))
                     (req_minus (opp (mult eta SAn)) (mult beta S1n))).
    - apply (sum_ext (fun s => mult (req2_pi_next pi_t Hpi_t s)
                                    (req2_energy_t pi_t Hpi_t s))
                     (fun s => req_minus (mult (req2_pi_next pi_t Hpi_t s)
                                               (opp (mult eta (req2_adv pi_t Hpi_t s))))
                                         (mult (req2_pi_next pi_t Hpi_t s)
                                               (mult beta (log (pi_t s) (Hpi_t s)))))).
      intro s. unfold req2_energy_t. apply req_mult_minus_distr_l.
    - apply (req_trans (sumf (fun s => req_minus (mult (req2_pi_next pi_t Hpi_t s)
                                                       (opp (mult eta (req2_adv pi_t Hpi_t s))))
                                                 (mult (req2_pi_next pi_t Hpi_t s)
                                                       (mult beta (log (pi_t s) (Hpi_t s))))))
                       (req_minus (sumf (fun s => mult (req2_pi_next pi_t Hpi_t s)
                                                        (opp (mult eta (req2_adv pi_t Hpi_t s)))))
                                  (sumf (fun s => mult (req2_pi_next pi_t Hpi_t s)
                                                        (mult beta (log (pi_t s) (Hpi_t s))))))
                       (req_minus (opp (mult eta SAn)) (mult beta S1n))).
      + exact (req2_sum_minus (fun s => mult (req2_pi_next pi_t Hpi_t s)
                                             (opp (mult eta (req2_adv pi_t Hpi_t s))))
                              (fun s => mult (req2_pi_next pi_t Hpi_t s)
                                             (mult beta (log (pi_t s) (Hpi_t s))))).
      + exact (req2_minus_compat _ _ _ _
                (req2_sum_ptimes_opp_scal (req2_pi_next pi_t Hpi_t) eta
                                          (fun s => req2_adv pi_t Hpi_t s))
                (req2_sum_ptimes_scal (req2_pi_next pi_t Hpi_t) beta
                                      (fun s => log (pi_t s) (Hpi_t s)))). }
  assert (Htail : req (plus (opp (mult beta S1n)) (mult beta S2))
                      (mult beta (req2_rel_ent (req2_pi_next pi_t Hpi_t) pi_t
                                               (req2_pi_next_pos pi_t Hpi_t) Hpi_t))).
  { apply (req_trans (plus (opp (mult beta S1n)) (mult beta S2))
                     (plus (mult beta S2) (opp (mult beta S1n)))
                     (mult beta (req2_rel_ent (req2_pi_next pi_t Hpi_t) pi_t
                                              (req2_pi_next_pos pi_t Hpi_t) Hpi_t))).
    - apply plus_comm.
    - apply (req_trans (plus (mult beta S2) (opp (mult beta S1n)))
                       (req_minus (mult beta S2) (mult beta S1n))
                       (mult beta (req2_rel_ent (req2_pi_next pi_t Hpi_t) pi_t
                                                (req2_pi_next_pos pi_t Hpi_t) Hpi_t))).
      + apply req_refl.
      + apply (req_trans (req_minus (mult beta S2) (mult beta S1n))
                         (mult beta (req_minus S2 S1n))
                         (mult beta (req2_rel_ent (req2_pi_next pi_t Hpi_t) pi_t
                                                  (req2_pi_next_pos pi_t Hpi_t) Hpi_t))
                         (req_sym (mult beta (req_minus S2 S1n))
                                  (req_minus (mult beta S2) (mult beta S1n))
                                  (req_mult_minus_distr_l beta S2 S1n))
                         (req_mult_compat beta beta (req_minus S2 S1n)
                                          (req2_rel_ent (req2_pi_next pi_t Hpi_t) pi_t
                                                        (req2_pi_next_pos pi_t Hpi_t) Hpi_t)
                                          (req_refl beta)
                                          (req_sym (req2_rel_ent (req2_pi_next pi_t Hpi_t) pi_t
                                                                 (req2_pi_next_pos pi_t Hpi_t) Hpi_t)
                                                   (req_minus S2 S1n)
                                                   (req2_rel_ent_minus (req2_pi_next pi_t Hpi_t) pi_t
                                                                       (req2_pi_next_pos pi_t Hpi_t) Hpi_t)))). }
  apply (req_trans (plus (sumf (fun s => mult (req2_pi_next pi_t Hpi_t s)
                                              (req2_energy_t pi_t Hpi_t s)))
                         (mult beta S2))
                   (plus (req_minus (opp (mult eta SAn)) (mult beta S1n)) (mult beta S2))
                   (plus (opp (mult eta SAn))
                         (mult beta (req2_rel_ent (req2_pi_next pi_t Hpi_t) pi_t
                                                  (req2_pi_next_pos pi_t Hpi_t) Hpi_t)))).
  - exact (req_plus_compat _ _ _ _ HSE (req_refl (mult beta S2))).
  - apply (req_trans (plus (req_minus (opp (mult eta SAn)) (mult beta S1n)) (mult beta S2))
                     (plus (opp (mult eta SAn)) (plus (opp (mult beta S1n)) (mult beta S2)))
                     (plus (opp (mult eta SAn))
                           (mult beta (req2_rel_ent (req2_pi_next pi_t Hpi_t) pi_t
                                                    (req2_pi_next_pos pi_t Hpi_t) Hpi_t)))).
    + apply req_sym.
      apply (plus_assoc (opp (mult eta SAn)) (opp (mult beta S1n)) (mult beta S2)).
    + exact (req_plus_compat (opp (mult eta SAn)) (opp (mult eta SAn))
                             (plus (opp (mult beta S1n)) (mult beta S2))
                             (mult beta (req2_rel_ent (req2_pi_next pi_t Hpi_t) pi_t
                                                      (req2_pi_next_pos pi_t Hpi_t) Hpi_t))
                             (req_refl (opp (mult eta SAn))) Htail).
Qed.

(* ============================================================ *)
(* ---- 剩余挂起清单（批 3b 时间盒结算；零 承认件，件件真证） ---- *)
(*                                                                *)
(* 以下件尚未完成 req 化（grep 实证坐标在案；语句同位；模板 = 本    *)
(* 文件已结果同族 req2_* 件；交接批按序平移）：                    *)
(* [已完成关键前置] req2_boltzmann_factor_bridge / req2_bridge_Z /  *)
(*   req2_Z_rel_boltzmann_form / req2_pi_next_log_decomp /          *)
(*   req2_energy_log_pt / req2_sum_E_beta / req2_F_t_beta_form /    *)
(*   req2_F_t_simpl_next / req2_F_t_rel_decomp / req2_F_t_simpl_t / *)
(*   req2_F_t_simpl_next_kl —— t12/t13 两条深链的求和-自由能机器    *)
(*   已全部真证；余下件为纯代数/le 链组装：                         *)
(* [t12 余件] align_energy_expand(@21875)→F_align_F_t_rel(@21949)→  *)
(*   align_objective_t12_decomp(@21997)→J_pi_t(@22016)→J_pi_next    *)
(*   (@22033)→policy_improvement_mono(@22065) 定理化（批 3 桥位 3）。*)
(* [t13 链] F_t_simpl_p(@22218)→F_t_decomp_p(@22280)→               *)
(*   grad_cross_identity(@22328)→sum_advance_gap(@22380，依赖        *)
(*   rlhf_suboptimality_gap@20554)→t13_hexp(@22494)→                *)
(*   backward_kl_step_beta(@22575)→backward_kl_step(@22686，批 3     *)
(*   req_backward_kl_identity 桥位)→step_le(@22790)→iter_le(@22915)  *)
(*   →gap_mono(@23086)。step_kl_weighted 需 sigT 打包（req2_iter     *)
(*   模板）。surrogate_diff_identity(@21744)/reward_expand(@21473)   *)

(* [B 类桥] req2_step_kl_eta_bound(@23114 同位)、req2_gibbs_inequality*)
(*   （gibbs_inequality@16629，批 2 FEP 依赖）、log_req_compat /      *)
(*   log_inv_exp_neg_req（接口缺口桥，本节已承接为 Hypothesis 位）。  *)
(* [dpo_pair/preference 簇] @20115-20330 与 @20865-21200 全清单：     *)
(*   preference 节（denom_pos/implicit_reward_diff/pair_loss_at_star/ *)
(*   total_loss 簇/rel_ent_ext_r）、dpo_reward 簇（@19616-19850）、    *)
(*   rlhf 显式簇（@20290-20620）、sigmoid/DPO 损失簇（@20865-21200）。 *)
(*   sigmoid_strict_inc(@21030) 需 B 类桥 req2_inv_pos_lt_contra /    *)
(*   req2_log_lt_mono（Id 同位 Variable）；ppo_gap_nonneg(@20083)     *)
(*   冻结（ppo_conservative min plain-le 同因，批 3 冻结先例）；       *)
(*   fold_right_ext(@20160) 与 list fold 机器：双层并行（§1.1 边界2）。*)
(* ============================================================ *)
End Req2AlignCore.
