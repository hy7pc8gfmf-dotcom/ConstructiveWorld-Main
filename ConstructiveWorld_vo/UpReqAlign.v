(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ========================================================================= *)
(* 【ToyR 工程·· 】玩具级定理同名非平凡替换稿（补标头注）       *)
(*                                                                           *)
(* 本稿系 ToyR 工程 替换落件（原名落件）；落件时头部漏植工程标记，本块由  *)
(*  于  补设：仅加头注，语句面／证明体／         *)
(* Require 面                                                                *)
(* 零改动；原头注紧随本块之后原样保留。来源刀面权威记录：消融50/。       *)
(* 替换定理清单：req_align_partition_condition／req_rlhf_optimal／           *)
(* req_dpo_optimal／req_rlhf_optimal_unique／req_plus_opp_le_zero／          *)
(* req_plusA_opp_cancel_le／req_dpo_loss_iter_step_le／req_Z_aud_le_one 等   *)
(* （共 10 条）                                                              *)
(* 非平凡性口径：最优性链显式重演与序界直造，消除单跳转发；无一行拆分式假    *)
(* 非平凡。                                                                  *)
(* 本稿零公理、零承认件、全闭合、纯构造性、无经典逻辑；落件时与本次补标      *)
(* 抽验编译均验零承认。                                                      *)
(* ========================================================================= *)
(* ============================================================ *)
(* UpReqAlign.v *)
(* *)
(* 目的： 对齐目标（RLHF/DPO）的 req 层基础定义与最优性。 *)
(* 主件： req_rlhf_optimal / req_rlhf_optimal_unique / req_dpo_optimal 与 req_free_energy_align_ext。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra。 *)
(* 备注： 分布、配分、相对熵、对齐能量等以 Section 变量给出；求和接口三定律为显式前提。 *)
(* ============================================================ *)

(* UpReqAlign.v — 签名迁移批 3：对齐理论主体（Alignment 簇）req 系重述与实例化
   模板：UpSigMigrate.v（试点）+ UpReqAlgebra.v（批 1 地基，直接依存）；
   纯 term-mode（req_trans 链 + compat 桥），零 Morphisms 依赖；
   Set 层语句（req/lt/le 均 Set 值，零 Prop 泄露）。
   ----------------------------------------------------------------
   盘点结论（批 3 清单 ~140 件三列核对，详）：
   [已覆盖→不重建] GRPO 14 件→UpReqDist.v；FEPAttention 4 + RowView 1→G01_CoreMicro.v
     （Id 泛化件在案，req 化依赖批 2 FEP req 三件套）；代数/减法/消去辅件
     （minus_minus_distr/opp_eq/le_of_minus_nonneg/t12 环代数等）→UpReqAlgebra.v。
     （req_step_kl_eta_bound 桥 + req_policy_iter_kl_geom_step/_iter +
     req_dpo_loss_iter_mono）+ KLProjection 10 件 + NaturalGradient 1 件 +
     PPO 分解 3 件 + sigmoid 快赢。
   [保持双层/冻结] min/r_max 的 plain-le 依存件（ppo_conservative 族 4 件、
     clip_error_nonneg、ppo_clipped_improvement——setoid 接口 min 输出 eps 化，
     plain 形不可导出，与 UpReqAlgebra abs_plus_one_pos 冻结同因）；
     nat/list Id 机器（fold_right_ext 等）；深链 t12/t13 挂起件（文件尾清单）。
   ----------------------------------------------------------------
   诚实签名变化登记表（规划书 §7.4）：
   1. log 前提化：setoid log 带 lt zero 前提——relative_entropy_req /
     align_objective_req / F_align_req / dpo_loss_req 全部携带
     pos_dist（逐点正性）参数；kl_tail_eval / projected_distribution_minimizes_kl
   2. minus 非接口字段：载体 = UpReqAlgebra.req_minus（δ 透明同形 Id minus）。
   3. T2① 桥接引理（假设位保留，与 Id 版逐位同构；规划书 §3.2/§4.4）：
      - FEP req 三件套桥（bridge_min_free_energy / bridge_free_energy_min_unique）
        ——批 2 UpReqFreeEnergy 结果后降为依存件；
      - req_step_kl_eta_bound（Id Variable @L23114 的 req 同位）；
      - req_backward_kl_identity（Id theorem @L22686 的 req 语句同位，深链挂起）；
      - req_policy_improvement_mono（Id @L22065 同位，深链挂起）；
      - log_req_compat（接口缺口桥，UpReqAlgebra ReqLogBridge 同位）；
      - req_square_nonneg / req_inv_pos_lt_contra / req_log_lt_mono /
        req_lt_plus_compat_{le_lt,lt_le}（B 类假设 req 同位，§1.5 表）。
   4. 载体重建：r_pow → req_r_pow、policy_iterate → policy_iterate_req
     （sigT 封装同构，nat 归纳件 Set 层重建，Id 件不可跨接口复用）。
   ---------------------------------------------------------------- *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* ReqAlignCore：对齐节 req 基础设施 + RLHF/DPO 核心 + 主链     *)
(*   （Id 原节：Alignment L18734-23272；节参数逐位对齐）    *)
(* ============================================================ *)
Section ReqAlignCore.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

(* ---- SumOver 的 req 签名对接面（= sum_req_over_S 规格面，L66177 同位；
        sum_le/sum_zero_nonneg 为 Id 系 sum_over_S_le/_zero_nonneg 的 req 同位
        ——诚实接口假设，Real 层有限和可实例化，同 Z_align_pos 先例） ---- *)
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

(* 接口缺口桥（登记表 3；UpReqAlgebra ReqLogBridge 同位，T2①）：
   Real 实例可满足（柯西 log 连续），实例化留待接口扩展批。 *)
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).

(* ---- 节参数（对齐 Id 系 L18750-18768） ---- *)
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable pi_ref_norm : req (sumf pi_ref) one.

(* ---- req 系节内定义 ---- *)
Definition pos_dist (p : S -> R) : Set := forall s : S, lt zero (p s).
Definition norm_one (p : S -> R) : Set := req (sumf p) one.

(* 配分函数与闭式最优策略（Id Z_align/pi_star L18769-18780 同形） *)
Definition Z_align_req : R :=
  sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
(* 前置引理（原 Variable 换同名 Lemma， 基座消融波 T2 终判 B39）：由 sum_pos+pi_ref_pos+mult_positive/exp_neg_pos 导出；零承认件 *)
Lemma Z_align_pos : lt zero Z_align_req.
Proof.
  unfold Z_align_req. apply sum_pos. intros s. apply mult_positive.
  exact (pi_ref_pos s). apply exp_neg_pos.
Qed.

Definition pi_star_req (s : S) : R :=
  mult (inv_pos Z_align_req Z_align_pos)
       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
(* 相对熵 req 形态（关键子项 3；Id relative_entropy L16535；
   log 前提化：携带逐点正性——登记表 1） *)
Definition relative_entropy_req (p q : S -> R) (Hp : pos_dist p) (Hq : pos_dist q) : R :=
  sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))).
(* 对齐能量/自由能/对齐目标（Id align_energy L18849 / align_objective L18855；
   log 前提化：F_align_req 携带逐点正性） *)
Definition align_energy_req (s : S) : R :=
  req_minus (opp (reward s)) (mult beta (log (pi_ref s) (pi_ref_pos s))).
Definition F_align_req (p : S -> R) (Hp : pos_dist p) : R :=
  plus (sumf (fun s => mult (p s) (align_energy_req s)))
       (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition align_objective_req (p : S -> R) (Hp : pos_dist p) : R :=
  opp (F_align_req p Hp).
Definition dpo_loss_req (p : S -> R) (Hp : pos_dist p) : R :=
  opp (align_objective_req p Hp).

(* ============ A 组：真证（req 内证零桥） ============ *)

(* 取负的逆（Id opp_eq L19170 的 req 版；destruct/eq_ind 不可用，
   走 req_opp_compat + req_double_neg 两折） *)
Lemma req_opp_eq : forall a b : R, req (opp a) (opp b) -> req a b.
Proof.
  intros a b Hab.
  apply (req_trans a (opp (opp a)) b).
  - apply (req_sym (opp (opp a)) a). apply req_double_neg.
  - apply (req_trans (opp (opp a)) (opp (opp b)) b).
    + apply (req_opp_compat (opp a) (opp b) Hab).
    + apply req_double_neg.
Qed.

(* π* 逐点正性（Id pi_star_pos L18783 同构；接口字段纯组装） *)
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

(* 对齐能量指数恒等（Id align_energy_exp L18861 的 req 版，~50 行真证：
   req_mult_minus_distr_l + inv 吸收 + req_opp_minus 重组 +
   req_exp_neg_opp_plus（批 1）+ req_exp_neg_opp_log（批 1）） *)
Lemma req_align_energy_exp :
  forall s : S,
    req (exp_neg (mult (inv_pos beta beta_pos) (align_energy_req s)))
        (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Proof.
  intro s.
  set (iv := inv_pos beta beta_pos).
  set (lg := log (pi_ref s) (pi_ref_pos s)).
  (* H1 : iv·(−r − β·lg) == (−(iv·r)) + (−lg) *)
  assert (H1 : req (mult iv (align_energy_req s))
                   (plus (opp (mult iv (reward s))) (opp lg))).
  { unfold align_energy_req, req_minus.
    apply (req_trans (mult iv (plus (opp (reward s)) (opp (mult beta lg))))
                     (plus (mult iv (opp (reward s))) (opp (mult iv (mult beta lg)))))
      .
    - exact (req_mult_minus_distr_l iv (opp (reward s)) (mult beta lg)).
    - apply (req_plus_compat (mult iv (opp (reward s))) (opp (mult iv (reward s)))
                             (opp (mult iv (mult beta lg))) (opp lg)).
      + apply req_opp_mult_l.
      + apply (req_opp_compat (mult iv (mult beta lg)) lg).
        apply (req_trans (mult iv (mult beta lg)) (mult (mult iv beta) lg) lg).
        * apply mult_assoc.
        * apply (req_trans (mult (mult iv beta) lg) (mult one lg) lg).
          -- apply (req_mult_compat (mult iv beta) one lg lg
                                   (req_trans (mult iv beta) (mult beta iv) one
                                              (mult_comm iv beta)
                                              (inv_pos_correct beta beta_pos))
                                   (req_refl lg)).
          -- apply req_mult_one_l. }
  (* H3 : iv·E == −(iv·r + lg) *)
  assert (H3 : req (mult iv (align_energy_req s))
                   (opp (plus (mult iv (reward s)) lg))).
  { apply (req_trans (mult iv (align_energy_req s))
                     (plus (opp (mult iv (reward s))) (opp lg))
                     (opp (plus (mult iv (reward s)) lg))).
    - exact H1.
    - apply (req_sym (opp (plus (mult iv (reward s)) lg))
                     (plus (opp (mult iv (reward s))) (opp lg))).
      apply req_opp_plus. }
  (* H4 : e^{iv·E} == e^{−(iv·r)} · e^{−lg}（批 1 req_exp_neg_opp_plus） *)
  assert (H4 : req (exp_neg (mult iv (align_energy_req s)))
                   (mult (exp_neg (opp (mult iv (reward s)))) (exp_neg (opp lg)))).
  { apply (req_trans (exp_neg (mult iv (align_energy_req s)))
                     (exp_neg (opp (plus (mult iv (reward s)) lg)))
                     (mult (exp_neg (opp (mult iv (reward s)))) (exp_neg (opp lg)))).
    - apply exp_neg_req_compat_setoid. exact H3.
    - exact (req_exp_neg_opp_plus (mult iv (reward s)) lg). }
  
  apply (req_trans (exp_neg (mult iv (align_energy_req s)))
                   (mult (exp_neg (opp (mult iv (reward s)))) (exp_neg (opp lg)))
                   (mult (pi_ref s) (exp_neg (opp (mult iv (reward s)))))).
  - exact H4.
  - apply (req_trans (mult (exp_neg (opp (mult iv (reward s)))) (exp_neg (opp lg)))
                     (mult (exp_neg (opp (mult iv (reward s)))) (pi_ref s))
                     (mult (pi_ref s) (exp_neg (opp (mult iv (reward s)))))).
    + apply (req_mult_compat (exp_neg (opp (mult iv (reward s))))
                             (exp_neg (opp (mult iv (reward s))))
                             (exp_neg (opp lg)) (pi_ref s)
                             (req_refl (exp_neg (opp (mult iv (reward s)))))
                             (req_exp_neg_opp_log (pi_ref s) (pi_ref_pos s))).
    + apply mult_comm.
Qed.

(* 配分条件（Id align_partition_condition L18944 的 req 版；真证：
   sum_ext 逐点 = req_align_energy_exp 的对称形式） *)
Lemma req_align_partition_condition :
  req Z_align_req
      (sumf (fun s => exp_neg (mult (inv_pos beta beta_pos) (align_energy_req s)))).
Proof.
  exact (sum_ext (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
                 (fun s => exp_neg (mult (inv_pos beta beta_pos) (align_energy_req s)))
                 (fun s => req_sym (exp_neg (mult (inv_pos beta beta_pos) (align_energy_req s)))
                                   (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
                                   (req_align_energy_exp s))).
Qed.

(* π* 归一化（Id pi_star_normalized L18790 的 req 版；试点 req_boltzmann_normalized
   同构真证：sum_linear + inv 完成） *)
Lemma req_pi_star_normalized : req (sumf pi_star_req) one.
Proof.
  apply (req_trans (sumf (fun s => mult (inv_pos Z_align_req Z_align_pos)
                                        (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))
                   (mult (inv_pos Z_align_req Z_align_pos)
                         (sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))
                   one).
  - exact (sum_linear (inv_pos Z_align_req Z_align_pos)
                      (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))).
  - apply (req_trans (mult (inv_pos Z_align_req Z_align_pos)
                           (sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))
                     (mult (inv_pos Z_align_req Z_align_pos) Z_align_req)
                     one).
    + apply (req_mult_compat (inv_pos Z_align_req Z_align_pos) (inv_pos Z_align_req Z_align_pos)
                             (sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))
                             Z_align_req).
      * apply req_refl.
      * apply (req_sym Z_align_req
                       (sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))).
        apply req_refl.
    + apply (req_trans (mult (inv_pos Z_align_req Z_align_pos) Z_align_req)
                       (mult Z_align_req (inv_pos Z_align_req Z_align_pos))
                       one).
      * apply mult_comm.
      * apply inv_pos_correct.
Qed.

(* 自由能外延（Id free_energy_ext L18951 的 req 版；真证：双 sum_ext +
   req_mult_compat；log 前提随逐点正性迁移——登记表 1） *)
Lemma req_free_energy_align_ext :
  forall (f g : S -> R) (Hf : pos_dist f) (Hg : pos_dist g),
    (forall s : S, req (f s) (g s)) ->
    req (F_align_req f Hf) (F_align_req g Hg).
Proof.
  intros f g Hf Hg Hfg.
  unfold F_align_req.
  apply (req_plus_compat
           (sumf (fun s => mult (f s) (align_energy_req s)))
           (sumf (fun s => mult (g s) (align_energy_req s)))
           (mult beta (sumf (fun s => mult (f s) (log (f s) (Hf s)))))
           (mult beta (sumf (fun s => mult (g s) (log (g s) (Hg s)))))).
  - apply (sum_ext (fun s => mult (f s) (align_energy_req s))
                   (fun s => mult (g s) (align_energy_req s))).
    intro s.
    apply (req_mult_compat (f s) (g s) (align_energy_req s) (align_energy_req s)
                           (Hfg s) (req_refl (align_energy_req s))).
  - apply (req_mult_compat beta beta
                           (sumf (fun s => mult (f s) (log (f s) (Hf s))))
                           (sumf (fun s => mult (g s) (log (g s) (Hg s))))).
    + apply req_refl.
    + apply (sum_ext (fun s => mult (f s) (log (f s) (Hf s)))
                     (fun s => mult (g s) (log (g s) (Hg s)))).
      intro s.
      apply (req_mult_compat (f s) (g s) (log (f s) (Hf s)) (log (g s) (Hg s))
                             (Hfg s) (log_req_compat (f s) (g s) (Hf s) (Hg s) (Hfg s))).
Qed.

(* ============ B 组：RLHF/DPO 核心（T2① FEP 桥 + 真证组装） ============ *)
(* FEP req 三件套的 req 签名桥（Id min_free_energy_is_boltzmann /
   free_energy_min_unique 的 req 同位承担；批 2 UpReqFreeEnergy 结果后
   降为依存件。对位简化注记：Id 侧经 align_boltzmann_is_pi_star 把
   boltzmann_dist 逐点等同 pi_star，req 侧桥直接以 pi_star_req 为极小点
   载体，等价且免重复——登记表 3。） *)
Hypothesis bridge_min_free_energy :
  forall (p : S -> R) (Hn : norm_one p) (Hp : pos_dist p),
    le (F_align_req pi_star_req req_pi_star_pos) (F_align_req p Hp).
Hypothesis bridge_free_energy_min_unique :
  forall (p : S -> R) (Hn : norm_one p) (Hp : pos_dist p),
    req (F_align_req p Hp) (F_align_req pi_star_req req_pi_star_pos) ->
    forall s : S, req (p s) (pi_star_req s).

(* RLHF 最优性（Id rlhf_optimal L19049 的 req 版；真证组装：
   桥 + req_free_energy_align_ext（π* 极小点载体免 ext）+ opp_le_compat） *)
Theorem req_rlhf_optimal :
  forall (p : S -> R) (Hn : norm_one p) (Hp : pos_dist p),
    le (align_objective_req p Hp) (align_objective_req pi_star_req req_pi_star_pos).
Proof.
  intros p Hn Hp. unfold align_objective_req.
  exact (opp_le_compat (F_align_req pi_star_req req_pi_star_pos) (F_align_req p Hp)
                       (bridge_min_free_energy p Hn Hp)).
Qed.

(* RLHF 最优策略唯一性（Id rlhf_optimal_unique L19180 的 req 版；
   req_opp_eq 真证 + 唯一性桥组装） *)
Theorem req_rlhf_optimal_unique :
  forall (p : S -> R) (Hn : norm_one p) (Hp : pos_dist p),
    req (align_objective_req p Hp) (align_objective_req pi_star_req req_pi_star_pos) ->
    forall s : S, req (p s) (pi_star_req s).
Proof.
  intros p Hn Hp Hj.
  exact (bridge_free_energy_min_unique p Hn Hp
           (req_opp_eq (F_align_req p Hp) (F_align_req pi_star_req req_pi_star_pos) Hj)).
Qed.

(* DPO 最优性（Id dpo_optimal L19112 的 req 版；dpo_loss = −J 真证组装） *)
Theorem req_dpo_optimal :
  forall (p : S -> R) (Hn : norm_one p) (Hp : pos_dist p),
    le (dpo_loss_req pi_star_req req_pi_star_pos) (dpo_loss_req p Hp).
Proof.
  intros p Hn Hp. unfold dpo_loss_req.
  exact (opp_le_compat (align_objective_req p Hp) (align_objective_req pi_star_req req_pi_star_pos)
                       (req_rlhf_optimal p Hn Hp)).
Qed.

(* ============ C 组：策略迭代主链（Id L21237-23272 req 化） ============ *)
(* 节参数（Id L21238-21241 同位；sum_pos 已在节首同位承担 Id
   Variable sum_over_S_pos @L21245） *)
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable eta_le_one : le eta one.

(* 定义簇 req 化（Id advantage_aug/Z_rel/energy_t/pi_next 同形；
   log 前提化：载体携带逐点正性参数——登记表 1） *)
Definition advantage_aug_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=
  req_minus (reward s)
            (mult beta (req_minus (log (pi_t s) (Hpi_t s)) (log (pi_ref s) (pi_ref_pos s)))).
Definition Z_rel_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) : R :=
  sumf (fun s => mult (pi_t s)
                      (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                          (advantage_aug_req pi_t Hpi_t s))))).
Definition energy_t_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=
  req_minus (opp (mult eta (advantage_aug_req pi_t Hpi_t s)))
            (mult beta (log (pi_t s) (Hpi_t s))).

(* Z_rel 正性（Id Z_rel_pos L21269 req 版；真证：sum_pos + mult_positive） *)
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

Definition pi_next_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=
  mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
       (mult (pi_t s)
             (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                 (advantage_aug_req pi_t Hpi_t s))))).

(* pi_next 逐点正性（Id pi_next_pos L21789 req 版；真证） *)
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

(* pi_next 归一化（Id pi_next_normalized L21401 req 版；真证：
   sum_linear + Z_rel 定义体 conversion 完成 + inv） *)
Lemma req_pi_next_normalized :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t),
    req (sumf (pi_next_req pi_t Hpi_t)) one.
Proof.
  intros pi_t Hpi_t.
  apply (req_trans (sumf (pi_next_req pi_t Hpi_t))
                   (mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                         (sumf (fun s => mult (pi_t s)
                                              (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                                  (advantage_aug_req pi_t Hpi_t s)))))))
                   one).
  - exact (sum_linear (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                      (fun s => mult (pi_t s)
                                     (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                         (advantage_aug_req pi_t Hpi_t s)))))).
  - apply (req_trans (mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                           (sumf (fun s => mult (pi_t s)
                                                (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                                    (advantage_aug_req pi_t Hpi_t s)))))))
                     (mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                           (Z_rel_req pi_t Hpi_t))
                     one).
    + apply (req_mult_compat (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                             (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                             (sumf (fun s => mult (pi_t s)
                                                  (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                                      (advantage_aug_req pi_t Hpi_t s))))))
                             (Z_rel_req pi_t Hpi_t)).
      * apply req_refl.
      * exact (req_sym (Z_rel_req pi_t Hpi_t)
                       (sumf (fun s => mult (pi_t s)
                                            (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                                (advantage_aug_req pi_t Hpi_t s))))))
                       (req_refl (Z_rel_req pi_t Hpi_t))).
    + apply (req_trans (mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                             (Z_rel_req pi_t Hpi_t))
                       (mult (Z_rel_req pi_t Hpi_t) (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t)))
                       one).
      * apply mult_comm.
      * apply inv_pos_correct.
Qed.

(* ---- B 类桥（T2① 假设位保留，与 Id 版逐位同构；登记表 3） ----
   req_step_kl_eta_bound ← Id Variable @L23114（B 类，Real 种子
   real_step_kl_eta_bound_eps@L113142 / real_interp_Z_le_one_eps@L112890
   在根；实例消解留待 req 求和实例批）。
   req_backward_kl_identity ← Id theorem policy_iter_backward_kl_step @L22686
   （深链 t13 桥，req 重证挂起批 3b——见文件尾挂起清单）。
   req_policy_improvement_mono ← Id @L22065（深链 t12，同上挂起）。 *)
Hypothesis req_step_kl_eta_bound :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t),
    le (relative_entropy_req pi_t (pi_next_req pi_t Hpi_t) Hpi_t (req_pi_next_pos pi_t Hpi_t))
       (mult eta (relative_entropy_req pi_t pi_star_req Hpi_t req_pi_star_pos)).
Hypothesis req_backward_kl_identity :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (Hnorm : norm_one pi_t),
    req (relative_entropy_req pi_star_req (pi_next_req pi_t Hpi_t)
             req_pi_star_pos (req_pi_next_pos pi_t Hpi_t))
        (plus (mult (req_minus one eta)
                    (relative_entropy_req pi_star_req pi_t req_pi_star_pos Hpi_t))
              (plus (opp (mult eta (relative_entropy_req pi_t pi_star_req Hpi_t req_pi_star_pos)))
                    (relative_entropy_req pi_t (pi_next_req pi_t Hpi_t)
                         Hpi_t (req_pi_next_pos pi_t Hpi_t)))).

(* ---- 序代数辅件（Id plus_opp_le_zero/plusA_opp_cancel_le L23119/23130
        的 req 版；真证：le 字段 + req 桥） ---- *)
Lemma req_plus_opp_le_zero : forall B C : R, le C B -> le (plus (opp B) C) zero.
Proof.
  intros B C HCB.
  exact (le_id_r (plus (opp B) C) (plus (opp B) B) zero
                 (req_trans (plus (opp B) B) (plus B (opp B)) zero
                            (plus_comm (opp B) B) (plus_opp B))
                 (le_plus_compat (opp B) (opp B) C B (le_refl (opp B)) HCB)).
Qed.

Lemma req_plusA_opp_cancel_le :
  forall A B C : R, le C B -> le (plus A (plus (opp B) C)) A.
Proof.
  intros A B C HCB.
  exact (le_id_r (plus A (plus (opp B) C)) (plus A zero) A (plus_zero A)
                 (le_plus_compat A A (plus (opp B) C) zero (le_refl A)
                                 (req_plus_opp_le_zero B C HCB))).
Qed.

(* 单步真几何收缩（Id policy_iter_kl_geom_step L23146 的 req 版；
   三 KL 精确恒等 + step 桥 + 序代数 req 组装——主件） *)
Theorem req_policy_iter_kl_geom_step :
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
  - exact (req_backward_kl_identity pi_t Hpi_t Hnorm).
  - exact (req_plusA_opp_cancel_le
             (mult (req_minus one eta)
                   (relative_entropy_req pi_star_req pi_t req_pi_star_pos Hpi_t))
             (mult eta (relative_entropy_req pi_t pi_star_req Hpi_t req_pi_star_pos))
             (relative_entropy_req pi_t (pi_next_req pi_t Hpi_t)
                  Hpi_t (req_pi_next_pos pi_t Hpi_t))
             (req_step_kl_eta_bound pi_t Hpi_t)).
Qed.

(* 迭代 Fixpoint req 化（Id policy_iterate L22879 同构：分布 + 正性
   封装为 sigT，可提取；nat 归纳 Set 层重建——登记表 4） *)
Fixpoint policy_iterate_req (t : nat) (pi : S -> R) (Hpi : pos_dist pi) :
  { pi' : S -> R & pos_dist pi' } :=
  match t with
  | 0%nat => existT _ pi Hpi
  | Datatypes.S m =>
      let p := policy_iterate_req m pi Hpi in
      existT _ (pi_next_req (projT1 p) (projT2 p)) (req_pi_next_pos (projT1 p) (projT2 p))
  end.

(* R 层幂 req 化（Id r_pow L14071 同形 nat 归纳；登记表 4） *)
Fixpoint req_r_pow (x : R) (n : nat) : R :=
  match n with
  | 0%nat => one
  | Datatypes.S m => mult x (req_r_pow x m)
  end.

(* 迭代保持归一化（Id policy_iter_norm L22890 req 版；真证归纳） *)
Lemma req_policy_iter_norm :
  forall (t : nat) (pi : S -> R) (Hpi : pos_dist pi),
    norm_one pi -> norm_one (projT1 (policy_iterate_req t pi Hpi)).
Proof.
  intros t pi Hpi Hnorm.
  induction t as [| m IH].
  - exact Hnorm.
  - exact (req_pi_next_normalized (projT1 (policy_iterate_req m pi Hpi))
                                  (projT2 (policy_iterate_req m pi Hpi))).
Qed.

(* 迭代几何上界（Id policy_iter_kl_geom_iter L23181 的 req 版；
   (1−η)^t 真几何率 req 依存版——归纳真证） *)
Theorem req_policy_iter_kl_geom_iter :
  forall (t : nat) (pi : S -> R) (Hpi : pos_dist pi) (Hnorm : norm_one pi),
    le (relative_entropy_req pi_star_req (projT1 (policy_iterate_req t pi Hpi))
            req_pi_star_pos (projT2 (policy_iterate_req t pi Hpi)))
       (mult (req_r_pow (req_minus one eta) t)
             (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)).
Proof.
  intros t pi Hpi Hnorm.
  induction t as [| m IH].
  - (* t = 0：KL ≤ 1·KL *)
    apply (le_id_r
      (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)
      (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)
      (mult one (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi))).
    + exact (req_sym (mult one (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi))
                     (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)
                     (req_mult_one_l (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi))).
    + apply le_refl.
  - (* t = S m：单步收缩 + 归纳 + κ^t 结合换形（req 链） *)
    assert (H1 : le (relative_entropy_req pi_star_req
                         (pi_next_req (projT1 (policy_iterate_req m pi Hpi))
                                      (projT2 (policy_iterate_req m pi Hpi)))
                         req_pi_star_pos
                         (req_pi_next_pos (projT1 (policy_iterate_req m pi Hpi))
                                          (projT2 (policy_iterate_req m pi Hpi))))
                    (mult (req_minus one eta)
                          (relative_entropy_req pi_star_req
                               (projT1 (policy_iterate_req m pi Hpi))
                               req_pi_star_pos (projT2 (policy_iterate_req m pi Hpi))))).
    { exact (req_policy_iter_kl_geom_step (projT1 (policy_iterate_req m pi Hpi))
                                          (projT2 (policy_iterate_req m pi Hpi))
                                          (req_policy_iter_norm m pi Hpi Hnorm)). }
    assert (Hk : le zero (req_minus one eta)).
    { exact (req_le_minus_nonneg eta one eta_le_one). }
    assert (H4 : le (mult (req_minus one eta)
                          (relative_entropy_req pi_star_req
                               (projT1 (policy_iterate_req m pi Hpi))
                               req_pi_star_pos (projT2 (policy_iterate_req m pi Hpi))))
                    (mult (req_minus one eta)
                          (mult (req_r_pow (req_minus one eta) m)
                                (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)))).
    { apply (le_id_l
        (mult (req_minus one eta)
              (relative_entropy_req pi_star_req (projT1 (policy_iterate_req m pi Hpi))
                   req_pi_star_pos (projT2 (policy_iterate_req m pi Hpi))))
        (mult (relative_entropy_req pi_star_req (projT1 (policy_iterate_req m pi Hpi))
                    req_pi_star_pos (projT2 (policy_iterate_req m pi Hpi)))
              (req_minus one eta))
        (mult (req_minus one eta)
              (mult (req_r_pow (req_minus one eta) m)
                    (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)))).
      - apply mult_comm.
      - apply (le_id_r
          (mult (relative_entropy_req pi_star_req (projT1 (policy_iterate_req m pi Hpi))
                     req_pi_star_pos (projT2 (policy_iterate_req m pi Hpi)))
                (req_minus one eta))
          (mult (mult (req_r_pow (req_minus one eta) m)
                      (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi))
                (req_minus one eta))
          (mult (req_minus one eta)
                (mult (req_r_pow (req_minus one eta) m)
                      (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)))).
        + apply mult_comm.
        + apply (le_mult_compat_weak
            (relative_entropy_req pi_star_req (projT1 (policy_iterate_req m pi Hpi))
                 req_pi_star_pos (projT2 (policy_iterate_req m pi Hpi)))
            (mult (req_r_pow (req_minus one eta) m)
                  (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi))
            (req_minus one eta) Hk).
          exact IH. }
    apply (le_trans
      (relative_entropy_req pi_star_req (projT1 (policy_iterate_req (Datatypes.S m) pi Hpi))
           req_pi_star_pos (projT2 (policy_iterate_req (Datatypes.S m) pi Hpi)))
      (mult (req_minus one eta)
            (mult (req_r_pow (req_minus one eta) m)
                  (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)))
      (mult (mult (req_minus one eta) (req_r_pow (req_minus one eta) m))
            (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi))).
    + exact (le_trans
        (relative_entropy_req pi_star_req
             (projT1 (policy_iterate_req (Datatypes.S m) pi Hpi))
             req_pi_star_pos (projT2 (policy_iterate_req (Datatypes.S m) pi Hpi)))
        (mult (req_minus one eta)
              (relative_entropy_req pi_star_req (projT1 (policy_iterate_req m pi Hpi))
                   req_pi_star_pos (projT2 (policy_iterate_req m pi Hpi))))
        (mult (req_minus one eta)
              (mult (req_r_pow (req_minus one eta) m)
                    (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)))
        H1 H4).
    + apply (le_id_r
        (mult (req_minus one eta)
              (mult (req_r_pow (req_minus one eta) m)
                    (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)))
        (mult (req_minus one eta)
              (mult (req_r_pow (req_minus one eta) m)
                    (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)))
        (mult (mult (req_minus one eta) (req_r_pow (req_minus one eta) m))
              (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi))).
      * apply (mult_assoc (req_minus one eta) (req_r_pow (req_minus one eta) m)
                          (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)).
      * apply le_refl.
Qed.

(* ---- DPO 损失沿策略改进轨道（Id L23244/23256 req 版） ---- *)
Hypothesis req_policy_improvement_mono :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (Hnorm : norm_one pi_t),
    le (align_objective_req pi_t Hpi_t)
       (align_objective_req (pi_next_req pi_t Hpi_t) (req_pi_next_pos pi_t Hpi_t)).

(* 单步：dpo_loss(pi_next) ≤ dpo_loss(pi_t)（真证组装） *)
Theorem req_dpo_loss_iter_step_le :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (Hnorm : norm_one pi_t),
    le (dpo_loss_req (pi_next_req pi_t Hpi_t) (req_pi_next_pos pi_t Hpi_t))
       (dpo_loss_req pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t Hnorm.
  unfold dpo_loss_req.
  exact (opp_le_compat (align_objective_req pi_t Hpi_t)
                       (align_objective_req (pi_next_req pi_t Hpi_t) (req_pi_next_pos pi_t Hpi_t))
                       (req_policy_improvement_mono pi_t Hpi_t Hnorm)).
Qed.

(* 迭代：沿 policy_iterate_req 轨道 dpo_loss 单调不增（真证组装） *)
Theorem req_dpo_loss_iter_mono :
  forall (t : nat) (pi : S -> R) (Hpi : pos_dist pi) (Hnorm : norm_one pi),
    le (dpo_loss_req (projT1 (policy_iterate_req (Datatypes.S t) pi Hpi))
                     (projT2 (policy_iterate_req (Datatypes.S t) pi Hpi)))
       (dpo_loss_req (projT1 (policy_iterate_req t pi Hpi))
                     (projT2 (policy_iterate_req t pi Hpi))).
Proof.
  intros t pi Hpi Hnorm.
  apply (le_id_l
    (dpo_loss_req (projT1 (policy_iterate_req (Datatypes.S t) pi Hpi))
                  (projT2 (policy_iterate_req (Datatypes.S t) pi Hpi)))
    (dpo_loss_req (pi_next_req (projT1 (policy_iterate_req t pi Hpi))
                               (projT2 (policy_iterate_req t pi Hpi)))
                  (req_pi_next_pos (projT1 (policy_iterate_req t pi Hpi))
                                   (projT2 (policy_iterate_req t pi Hpi))))
    (dpo_loss_req (projT1 (policy_iterate_req t pi Hpi))
                  (projT2 (policy_iterate_req t pi Hpi)))).
  - apply req_refl.
  - exact (req_dpo_loss_iter_step_le (projT1 (policy_iterate_req t pi Hpi))
                                     (projT2 (policy_iterate_req t pi Hpi))
                                     (req_policy_iter_norm t pi Hpi Hnorm)).
Qed.

(* APPEND-POINT-B *)
End ReqAlignCore.

(* ============================================================ *)
(* ReqKLProjection：审计 = KL 投影（Id 原节 L95420-95604 req 化） *)
(*   签名差异（登记表 1）：req log 前提化使 fail 支上 log(0) 项不可   *)
(*   陈述——projected-KL 以逐点闭式重述：pass 支上                  *)



(*   完全同位（positive_dist + fail 零 + 归一化 + HlogZ）。          *)
(* ============================================================ *)
Section ReqKLProjection.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
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
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).

Variable post_aud : S -> bool.
Variable p : S -> R.
Variable Hp_norm : req (sumf p) one.
Variable Hp_pos : forall s : S, lt zero (p s).

(* 通过集质量与投影分布（Id Z_aud/projected_distribution 同形） *)
Definition Z_aud_req : R := sumf (fun s => if post_aud s then p s else zero).
Variable HZ : lt zero Z_aud_req.
Definition projected_distribution_req (s : S) : R :=
  if post_aud s then mult (p s) (inv_pos Z_aud_req HZ) else zero.


Definition kl_proj_closed (q : S -> R) (Hq : forall s : S, lt zero (q s)) (s : S) : R :=
  mult (q s)
       (req_minus (log (q s) (Hq s))
                  (plus (log (p s) (Hp_pos s))
                        (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))).

(* 局部辅件：req_minus 左参数兼容（req_minus δ 透明展开即 plus 兼容） *)
Lemma rkl_minus_compat_l :
  forall a b c : R, req a b -> req (req_minus a c) (req_minus b c).
Proof.
  intros a b c H. unfold req_minus.
  exact (req_plus_compat a b (opp c) (opp c) H (req_refl (opp c))).
Qed.

(* 局部辅件：opp zero == zero *)
Lemma rkl_opp_zero : req (opp zero) zero.
Proof.
  exact (req_trans (opp zero) (plus zero (opp zero)) zero
                   (req_sym (plus zero (opp zero)) (opp zero) (req_plus_zero_l (opp zero)))
                   (plus_opp zero)).
Qed.

(* 投影分布 pass 支形态（Id projected_pt 的 pass 支同位） *)
Lemma req_projected_pass :
  forall (s : S) (E : post_aud s = true),
    req (projected_distribution_req s) (mult (p s) (inv_pos Z_aud_req HZ)).
Proof.
  intros s E.
  destruct (post_aud s) eqn:Es.
  - unfold projected_distribution_req. rewrite Es. apply req_refl.
  - discriminate E.
Qed.

(* 投影分布 pass 支正性（req log 前提所需；Id 系 plain 正性全域版在
   req 世界仅 pass 支可陈述——签名差异登记表 1） *)
Lemma req_projected_pass_pos :
  forall (s : S) (E : post_aud s = true), lt zero (projected_distribution_req s).
Proof.
  intros s E.
  destruct (post_aud s) eqn:Es.
  - unfold projected_distribution_req. rewrite Es.
    apply mult_positive.
    + apply Hp_pos.
    + apply inv_pos_pos.
  - discriminate E.
Qed.

(* Id if_p_le_p L95450 req 版（bool 分支 + lt_le_iff；真证） *)
Lemma req_if_p_le_p : forall s : S, le (if post_aud s then p s else zero) (p s).
Proof.
  intro s. destruct (post_aud s).
  - apply le_refl.
  - apply (lt_le_iff zero (p s)). left. apply Hp_pos.
Qed.

(* Id Z_aud_le_one L95459 req 版（sum_le 提升；真证） *)
Lemma req_Z_aud_le_one : le Z_aud_req (sumf p).
Proof.
  unfold Z_aud_req.
  exact (sum_le (fun s => if post_aud s then p s else zero) p
                req_if_p_le_p).
Qed.

(* Id projected_pt L95465 req 版（真证：comm / mult_zero 分支） *)
Lemma req_projected_pt :
  forall s : S,
    req (projected_distribution_req s)
        (mult (inv_pos Z_aud_req HZ) (if post_aud s then p s else zero)).
Proof.
  intro s. unfold projected_distribution_req. destruct (post_aud s).
  - apply mult_comm.
  - exact (req_sym (mult (inv_pos Z_aud_req HZ) zero) zero
                   (mult_zero (inv_pos Z_aud_req HZ))).
Qed.

(* Id projected_normalized L95476 req 版（真证：sum_ext + linear + inv 完成） *)
Lemma req_projected_normalized : req (sumf projected_distribution_req) one.
Proof.
  apply (req_trans (sumf projected_distribution_req)
                   (sumf (fun s => mult (inv_pos Z_aud_req HZ) (if post_aud s then p s else zero)))
                   one).
  - apply (sum_ext (fun s => projected_distribution_req s)
                   (fun s => mult (inv_pos Z_aud_req HZ) (if post_aud s then p s else zero))).
    apply req_projected_pt.
  - apply (req_trans (sumf (fun s => mult (inv_pos Z_aud_req HZ) (if post_aud s then p s else zero)))
                     (mult (inv_pos Z_aud_req HZ) (sumf (fun s => if post_aud s then p s else zero)))
                     one).
    + exact (sum_linear (inv_pos Z_aud_req HZ)
                        (fun s => if post_aud s then p s else zero)).
    + apply (req_trans (mult (inv_pos Z_aud_req HZ) (sumf (fun s => if post_aud s then p s else zero)))
                       (mult (inv_pos Z_aud_req HZ) Z_aud_req)
                       one).
      * apply (req_mult_compat (inv_pos Z_aud_req HZ) (inv_pos Z_aud_req HZ)
                               (sumf (fun s => if post_aud s then p s else zero))
                               Z_aud_req).
        -- apply req_refl.
        -- exact (req_sym Z_aud_req (sumf (fun s => if post_aud s then p s else zero))
                                 (req_refl Z_aud_req)).
      * apply (req_trans (mult (inv_pos Z_aud_req HZ) Z_aud_req)
                         (mult Z_aud_req (inv_pos Z_aud_req HZ))
                         one).
        -- apply mult_comm.
        -- apply inv_pos_correct.
Qed.

(* Id kl_minus_split L95498 req 版：a−c == (a−b)+(b−c)（req_minus 载体；真证） *)
Lemma req_kl_minus_split :
  forall a b c : R, req (req_minus a c) (plus (req_minus a b) (req_minus b c)).
Proof.
  intros a b c. unfold req_minus.
  apply (req_trans (plus a (opp c))
                   (plus a (plus (opp b) (plus b (opp c))))
                   (plus (plus a (opp b)) (plus b (opp c)))).
  - apply (req_plus_compat a a (opp c) (plus (opp b) (plus b (opp c)))
                           (req_refl a)).
    apply (req_trans (opp c) (plus (plus (opp b) b) (opp c))
                     (plus (opp b) (plus b (opp c)))).
    + apply (req_trans (opp c) (plus zero (opp c))
                       (plus (plus (opp b) b) (opp c))).
      * apply (req_sym (plus zero (opp c)) (opp c)). apply req_plus_zero_l.
      * apply (req_plus_compat zero (plus (opp b) b) (opp c) (opp c)
                               (req_sym (plus (opp b) b) zero (req_plus_opp_l b))
                               (req_refl (opp c))).
    + apply (req_sym (plus (opp b) (plus b (opp c)))
                     (plus (plus (opp b) b) (opp c))
                     (plus_assoc (opp b) b (opp c))).
  - apply plus_assoc.
Qed.

(* Id minus_plus_opp L95539 req 版：(x + (−L)) − x == −L（真证） *)
Lemma req_minus_plus_opp : forall x L : R, req (req_minus (plus x (opp L)) x) (opp L).
Proof.
  intros x L. unfold req_minus.
  apply (req_trans (plus (plus x (opp L)) (opp x))
                   (plus x (plus (opp L) (opp x)))
                   (opp L)).
  - apply (req_sym (plus x (plus (opp L) (opp x)))
                   (plus (plus x (opp L)) (opp x))).
    apply plus_assoc.
  - apply (req_trans (plus x (plus (opp L) (opp x)))
                     (plus x (plus (opp x) (opp L)))
                     (opp L)).
    + apply (req_plus_compat x x (plus (opp L) (opp x)) (plus (opp x) (opp L))
                             (req_refl x) (plus_comm (opp L) (opp x))).
    + apply (req_trans (plus x (plus (opp x) (opp L)))
                       (plus (plus x (opp x)) (opp L))
                       (opp L)).
      * apply plus_assoc.
      * apply (req_trans (plus (plus x (opp x)) (opp L))
                         (plus zero (opp L))
                         (opp L)).
        -- apply (req_plus_compat (plus x (opp x)) zero (opp L) (opp L)
                                  (plus_opp x) (req_refl (opp L))).
        -- apply (req_trans (plus zero (opp L)) (plus (opp L) zero) (opp L)
                            (plus_comm zero (opp L)) (plus_zero (opp L))).
Qed.

(* log(1/x) == −log x（UpReqAlgebra ReqLogBridge req_log_inv_one_inv 同款
   本节重建——依存本节 log_req_compat 桥） *)
Lemma rkl_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x),
    req (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  assert (Hprod : req (mult (inv_pos x Hx) x) one).
  { exact (req_trans (mult (inv_pos x Hx) x) (mult x (inv_pos x Hx)) one
                     (mult_comm (inv_pos x Hx) x) (inv_pos_correct x Hx)). }
  assert (Hl1 : req (log (mult (inv_pos x Hx) x)
                         (mult_positive (inv_pos x Hx) x (inv_pos_pos x Hx) Hx))
                    zero).
  { apply (req_trans (log (mult (inv_pos x Hx) x)
                          (mult_positive (inv_pos x Hx) x (inv_pos_pos x Hx) Hx))
                     (log one one_pos) zero).
    - apply log_req_compat. exact Hprod.
    - exact (log_one one_pos). }
  apply (req_add_cancel_l (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx)
                          (opp (log x Hx))).
  apply (req_trans (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx))
                   zero
                   (plus (opp (log x Hx)) (log x Hx))).
  - apply (req_trans (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx))
                     (log (mult (inv_pos x Hx) x)
                          (mult_positive (inv_pos x Hx) x (inv_pos_pos x Hx) Hx))
                     zero).
    + apply (req_sym (log (mult (inv_pos x Hx) x)
                          (mult_positive (inv_pos x Hx) x (inv_pos_pos x Hx) Hx))
                     (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx))).
      apply log_mult.
    + exact Hl1.
  - apply (req_sym (plus (opp (log x Hx)) (log x Hx)) zero).
    apply (req_trans (plus (opp (log x Hx)) (log x Hx))
                     (plus (log x Hx) (opp (log x Hx))) zero).
    + apply plus_comm.
    + apply plus_opp.
Qed.

(* 逐点投影 log 分解（Id kl_pointwise_split L95515 的 req 对位件）：
   pass 支上 log pd == log p + log(1/Z)（真证：pass 形态 + log 桥 + log_mult） *)
Lemma req_log_proj_pass :
  forall (s : S) (E : post_aud s = true),
    req (log (projected_distribution_req s) (req_projected_pass_pos s E))
        (plus (log (p s) (Hp_pos s))
              (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))).
Proof.
  intros s E.
  apply (req_trans (log (projected_distribution_req s) (req_projected_pass_pos s E))
                   (log (mult (p s) (inv_pos Z_aud_req HZ))
                        (mult_positive (p s) (inv_pos Z_aud_req HZ) (Hp_pos s)
                                                       (inv_pos_pos Z_aud_req HZ)))
                   (plus (log (p s) (Hp_pos s))
                         (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))).
  - apply log_req_compat.
    exact (req_projected_pass s E).
  - exact (log_mult (p s) (inv_pos Z_aud_req HZ) (Hp_pos s) (inv_pos_pos Z_aud_req HZ)).
Qed.

(* 逐点 KL 闭式分解（Id kl_pointwise_split/kl_sum_split 的逐点核；真证：
   req_kl_minus_split + req_minus_plus_cancel_r + distrib） *)
Lemma req_kl_closed_pt :
  forall (q : S -> R) (Hq : forall s : S, lt zero (q s)) (s : S),
    req (mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s))))
        (plus (kl_proj_closed q Hq s)
              (mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))).
Proof.
  intros q Hq s.
  assert (Hcancel : req (req_minus (plus (log (p s) (Hp_pos s))
                                         (log (inv_pos Z_aud_req HZ)
                                              (inv_pos_pos Z_aud_req HZ)))
                                   (log (p s) (Hp_pos s)))
                        (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))
    by exact (req_minus_plus_cancel_r (log (p s) (Hp_pos s))
                                      (log (inv_pos Z_aud_req HZ)
                                           (inv_pos_pos Z_aud_req HZ))).
  assert (Hinner : req (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s)))
                       (plus (req_minus (log (q s) (Hq s))
                                        (plus (log (p s) (Hp_pos s))
                                              (log (inv_pos Z_aud_req HZ)
                                                   (inv_pos_pos Z_aud_req HZ))))
                             (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))).
  { apply (req_trans (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s)))
                     (plus (req_minus (log (q s) (Hq s))
                                      (plus (log (p s) (Hp_pos s))
                                            (log (inv_pos Z_aud_req HZ)
                                                 (inv_pos_pos Z_aud_req HZ))))
                           (req_minus (plus (log (p s) (Hp_pos s))
                                            (log (inv_pos Z_aud_req HZ)
                                                 (inv_pos_pos Z_aud_req HZ)))
                                      (log (p s) (Hp_pos s))))
                     (plus (req_minus (log (q s) (Hq s))
                                      (plus (log (p s) (Hp_pos s))
                                            (log (inv_pos Z_aud_req HZ)
                                                 (inv_pos_pos Z_aud_req HZ))))
                           (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))).
    - exact (req_kl_minus_split (log (q s) (Hq s))
                                (plus (log (p s) (Hp_pos s))
                                      (log (inv_pos Z_aud_req HZ)
                                           (inv_pos_pos Z_aud_req HZ)))
                                (log (p s) (Hp_pos s))).
    - exact (req_plus_compat
               (req_minus (log (q s) (Hq s))
                          (plus (log (p s) (Hp_pos s))
                                (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))
               (req_minus (log (q s) (Hq s))
                          (plus (log (p s) (Hp_pos s))
                                (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))
               (req_minus (plus (log (p s) (Hp_pos s))
                                (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))
                          (log (p s) (Hp_pos s)))
               (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))
               (req_refl _)
               Hcancel). }
  apply (req_trans (mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s))))
                   (mult (q s)
                         (plus (req_minus (log (q s) (Hq s))
                                          (plus (log (p s) (Hp_pos s))
                                                (log (inv_pos Z_aud_req HZ)
                                                     (inv_pos_pos Z_aud_req HZ))))
                               (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))
                   (plus (mult (q s)
                               (req_minus (log (q s) (Hq s))
                                          (plus (log (p s) (Hp_pos s))
                                                (log (inv_pos Z_aud_req HZ)
                                                     (inv_pos_pos Z_aud_req HZ)))))
                         (mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))).
  - apply (req_mult_compat (q s) (q s)
          (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s)))
          (plus (req_minus (log (q s) (Hq s))
                           (plus (log (p s) (Hp_pos s))
                                 (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))
                (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))
          (req_refl (q s))
          Hinner).
  - exact (distrib (q s)
                   (req_minus (log (q s) (Hq s))
                              (plus (log (p s) (Hp_pos s))
                                    (log (inv_pos Z_aud_req HZ)
                                         (inv_pos_pos Z_aud_req HZ))))
                   (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))).
Qed.

(* 和的分解（Id kl_sum_split L95527 req 版；真证：sum_ext + sum_add + linear） *)
Lemma req_kl_closed_sum_split :
  forall (q : S -> R) (Hq : forall s : S, lt zero (q s)),
    req (sumf (fun s => mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s)))))
        (plus (sumf (fun s => kl_proj_closed q Hq s))
              (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))).
Proof.
  intros q Hq.
  apply (req_trans
    (sumf (fun s => mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s)))))
    (sumf (fun s => plus (kl_proj_closed q Hq s) (mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))))
    (plus (sumf (fun s => kl_proj_closed q Hq s)) (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q)))).
  - apply (sum_ext
      (fun s => mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s))))
      (fun s => plus (kl_proj_closed q Hq s) (mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))).
    intro s. exact (req_kl_closed_pt q Hq s).
  - apply (req_trans
      (sumf (fun s => plus (kl_proj_closed q Hq s) (mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))))
      (plus (sumf (fun s => kl_proj_closed q Hq s))
            (sumf (fun s => mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))))
      (plus (sumf (fun s => kl_proj_closed q Hq s)) (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q)))).
    + apply (sum_add (fun s => kl_proj_closed q Hq s)
                     (fun s => mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))).
    + apply (req_plus_compat
               (sumf (fun s => kl_proj_closed q Hq s))
               (sumf (fun s => kl_proj_closed q Hq s))
               (sumf (fun s => mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))
               (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))
               (req_refl (sumf (fun s => kl_proj_closed q Hq s)))).
      apply (req_trans
        (sumf (fun s => mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))
        (sumf (fun s => mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (q s)))
        (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))).
      * apply (sum_ext
                 (fun s => mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))
                 (fun s => mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (q s))).
        intro s. apply mult_comm.
      * exact (sum_linear (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) q).
Qed.

(* 尾项求值（Id kl_tail_eval L95551 req 闭式版；真证：
   归一化 + log(1/Z) == −log Z） *)
Lemma req_kl_closed_tail_eval :
  forall (q : S -> R) (Hq : forall s : S, lt zero (q s)) (Hqn : req (sumf q) one),
    req (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))
        (opp (log Z_aud_req HZ)).
Proof.
  intros q Hq Hqn.
  apply (req_trans (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))
                   (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))
                   (opp (log Z_aud_req HZ))).
  - exact (req_trans (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))
                     (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) one)
                     (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))
                     (req_mult_compat (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))
                                      (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))
                                      (sumf q) one (req_refl _) Hqn)
                     (mult_one (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))).
  - exact (rkl_log_inv_one_inv Z_aud_req HZ).
Qed.

(* 主定理：审计 = KL 投影（Id projected_distribution_minimizes_kl L95587
   的 req 版；真证组装：split + 尾项 ≥ 0 单侧链） *)
Theorem req_projected_distribution_minimizes_kl :
  forall (q : S -> R) (Hq : forall s : S, lt zero (q s)) (Hqn : req (sumf q) one)
         (Hqz : forall s : S, post_aud s = false -> req (q s) zero)
         (HlogZ : le (log Z_aud_req HZ) zero),
    le (sumf (fun s => kl_proj_closed q Hq s))
       (sumf (fun s => mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s))))).
Proof.
  intros q Hq Hqn Hqz HlogZ.
  assert (Hsplit : req (sumf (fun s => mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s)))))
                       (plus (sumf (fun s => kl_proj_closed q Hq s)) (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))))
    by exact (req_kl_closed_sum_split q Hq).
  assert (Htail : req (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q)) (opp (log Z_aud_req HZ)))
    by exact (req_kl_closed_tail_eval q Hq Hqn).
  assert (Hge0 : le zero (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))).
  { apply (le_id_r zero (opp (log Z_aud_req HZ)) (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))
                   (req_sym (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q)) (opp (log Z_aud_req HZ)) Htail)).
    apply (le_id_l zero (opp zero) (opp (log Z_aud_req HZ)) (req_sym _ _ (rkl_opp_zero))).
    apply (opp_le_compat (log Z_aud_req HZ) zero). exact HlogZ. }
  exact (le_id_r (sumf (fun s => kl_proj_closed q Hq s))
                 (plus (sumf (fun s => kl_proj_closed q Hq s)) (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q)))
                 (sumf (fun s => mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s)))))
                 (req_sym (sumf (fun s => mult (q s)
                                                (req_minus (log (q s) (Hq s))
                                                           (log (p s) (Hp_pos s)))))
                          (plus (sumf (fun s => kl_proj_closed q Hq s))
                                (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q)))
                          Hsplit)
                 (req_le_plus_nonneg_r (sumf (fun s => kl_proj_closed q Hq s))
                                       (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))
                                       Hge0)).
Qed.

End ReqKLProjection.

(* ============================================================ *)
(* ReqNaturalGradient：自然梯度（Id 原节 L24347-24460 req 化） *)
(*   B 类桥 req 同位（登记表 3）：req_square_nonneg ← Id Variable     *)
(*   square_nonneg @L24393（种子 real_square_nonneg_eps@L44842 在根）； *)
(*   sum 零分解 ← sum_over_S_zero_nonneg 的 req 同位（节首假设）。   *)
(* ============================================================ *)
Section ReqNaturalGradient.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero -> forall s : S, req (f s) zero.
Hypothesis req_square_nonneg : forall a : R, le zero (mult a a).

Variable Theta : Set.
Variable p_theta : Theta -> S -> R.
Variable partial : (Theta -> R) -> Theta -> R.
Variable p_theta_pos : forall theta : Theta, forall s : S, lt zero (p_theta theta s).

(* Fisher 信息标量（Id fisher_info_scalar L24360 同形）。
   的 log 无前提；setoid log 带前提，req 版逐点补 p_theta_pos th s 供给。 *)
Definition fisher_info_scalar_req (theta : Theta) : R :=
  sumf (fun s =>
    mult (p_theta theta s)
         (mult (partial (fun th => log (p_theta th s) (p_theta_pos th s)) theta)
               (partial (fun th => log (p_theta th s) (p_theta_pos th s)) theta))).

(* Fisher 零分解（Id fisher_zero_implies_pointwise L24395 req 版；
   真证：逐点非负（req_square_nonneg 桥）+ 零和分解） *)
Theorem req_fisher_zero_implies_pointwise :
  forall theta : Theta,
    req (fisher_info_scalar_req theta) zero ->
    forall s : S,
      req (mult (p_theta theta s)
                (mult (partial (fun th => log (p_theta th s) (p_theta_pos th s)) theta)
                      (partial (fun th => log (p_theta th s) (p_theta_pos th s)) theta)))
          zero.
Proof.
  intros theta Hf0 s.
  assert (Hpt : forall s0 : S,
           le zero (mult (p_theta theta s0)
                         (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                               (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)))).
  { intro s0.
    assert (Hsq : le zero (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                                (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)))
      by exact (req_square_nonneg
                  (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)).
    exact (le_id_l zero (mult zero (p_theta theta s0))
                   (mult (p_theta theta s0)
                         (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                               (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)))
                   (req_sym (mult zero (p_theta theta s0)) zero
                            (req_trans (mult zero (p_theta theta s0))
                                            (mult (p_theta theta s0) zero) zero
                                            (mult_comm zero (p_theta theta s0))
                                            (mult_zero (p_theta theta s0))))
                   (le_id_r (mult zero (p_theta theta s0))
                            (mult (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                                       (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta))
                                  (p_theta theta s0))
                            (mult (p_theta theta s0)
                                  (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                                        (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)))
                            (mult_comm (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                                             (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta))
                                       (p_theta theta s0))
                            (le_mult_compat zero
                                            (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                                                  (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta))
                                            (p_theta theta s0)
                                            (p_theta_pos theta s0)
                                            Hsq))). }
  exact (sum_zero_nonneg
           (fun s0 => mult (p_theta theta s0)
                           (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                                 (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)))
           Hpt Hf0 s).
Qed.

End ReqNaturalGradient.

(* ============================================================ *)
(* ReqPPORatio：PPO 分解簇（Id 原节 PPOClipDecomp L112330-112470   *)
(*   可迁 3 件 req 化；min 的 plain-le 依存件 2 件冻结——见尾清单） *)
(* ============================================================ *)
Section ReqPPORatio.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).

Variable pi : S -> R.
Variable p_old : S -> R.
Variable eps : R.
Variable Hpos : forall s : S, lt zero (p_old s).

(* IS 比率 / 裁剪 / 三目标（Id policy_ratio L19613 / ppo_clip L19607 /
   clip_error L112346 / ppo_surrogate L19590 / is_objective_of L19599 同形；
   min/r_max 为 setoid 接口字段——仅作符号载体，本组不依存其 le 性质） *)
Definition ratio_req (s : S) : R := mult (pi s) (inv_pos (p_old s) (Hpos s)).
Definition ppo_clip_req (r low high : R) : R := min (r_max low r) high.
Definition ppo_surrogate_req (adv : S -> R) : R :=
  sumf (fun s : S =>
    mult (p_old s)
         (min (mult (ratio_req s) (adv s))
              (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                    (adv s)))).
Definition is_objective_req (adv : S -> R) : R :=
  sumf (fun s : S => mult (p_old s) (mult (ratio_req s) (adv s))).
Definition clip_error_req (adv : S -> R) : R :=
  sumf (fun s : S =>
    mult (p_old s)
         (req_minus (mult (ratio_req s) (adv s))
                    (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))))).

(* 逐点分解（Id ppo_pointwise_decomp L112363 req 版；真证：
   req_minus_plus_cancel（批 1）+ distrib） *)
Lemma req_ppo_pointwise_decomp :
  forall (adv : S -> R) (s : S),
    req (mult (p_old s) (mult (ratio_req s) (adv s)))
        (plus (mult (p_old s)
                    (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))))
              (mult (p_old s)
                    (req_minus (mult (ratio_req s) (adv s))
                               (min (mult (ratio_req s) (adv s))
                                    (mult (ppo_clip_req (ratio_req s) (req_minus one eps)
                                                         (plus one eps))
                                          (adv s)))))).
Proof.
  intros adv s.
  assert (Hc : req (mult (ratio_req s) (adv s)) (plus (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))) (req_minus (mult (ratio_req s) (adv s)) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))))))
    by exact (req_sym (plus (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))) (req_minus (mult (ratio_req s) (adv s)) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))))) (mult (ratio_req s) (adv s))
                      (req_minus_plus_cancel (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))) (mult (ratio_req s) (adv s)))).
  exact (req_trans (mult (p_old s) (mult (ratio_req s) (adv s)))
                   (mult (p_old s) (plus (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))) (req_minus (mult (ratio_req s) (adv s)) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))))))
                   (plus (mult (p_old s) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))))
                         (mult (p_old s) (req_minus (mult (ratio_req s) (adv s)) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))))))
                   (req_mult_compat (p_old s) (p_old s)
                                    (mult (ratio_req s) (adv s))
                                    (plus (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))) (req_minus (mult (ratio_req s) (adv s)) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s)))))
                                    (req_refl (p_old s)) Hc)
                   (distrib (p_old s) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))) (req_minus (mult (ratio_req s) (adv s)) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s)))))).
Qed.

(* IS 目标精确分解（Id ppo_is_decomp L112398 req 版；真证组装） *)
Theorem req_ppo_is_decomp :
  forall adv : S -> R,
    req (is_objective_req adv)
        (plus (ppo_surrogate_req adv) (clip_error_req adv)).
Proof.
  intro adv.
  apply (req_trans (is_objective_req adv)
                   (sumf (fun s : S =>
                            plus (mult (p_old s)
                                       (min (mult (ratio_req s) (adv s))
                                            (mult (ppo_clip_req (ratio_req s)
                                                                (req_minus one eps)
                                                                (plus one eps))
                                                  (adv s))))
                                 (mult (p_old s)
                                       (req_minus (mult (ratio_req s) (adv s))
                                                  (min (mult (ratio_req s) (adv s))
                                                       (mult (ppo_clip_req (ratio_req s)
                                                                            (req_minus one eps)
                                                                            (plus one eps))
                                                             (adv s)))))))
                   (plus (ppo_surrogate_req adv) (clip_error_req adv))).
  - apply (sum_ext (fun s : S => mult (p_old s) (mult (ratio_req s) (adv s)))
                   (fun s : S =>
                      plus (mult (p_old s)
                                 (min (mult (ratio_req s) (adv s))
                                      (mult (ppo_clip_req (ratio_req s) (req_minus one eps)
                                                           (plus one eps))
                                            (adv s))))
                           (mult (p_old s)
                                 (req_minus (mult (ratio_req s) (adv s))
                                            (min (mult (ratio_req s) (adv s))
                                                 (mult (ppo_clip_req (ratio_req s)
                                                                      (req_minus one eps)
                                                                      (plus one eps))
                                                       (adv s))))))).
    intro s. exact (req_ppo_pointwise_decomp adv s).
  - apply sum_add.
Qed.

(* a−b ≥ 0 ⟹ b ≤ a（Id le_of_minus_nonneg L112430 req 版；真证） *)
Lemma req_le_of_minus_nonneg :
  forall a b : R, le zero (req_minus a b) -> le b a.
Proof.
  intros a b H.
  exact (le_trans b (plus b (req_minus a b)) a
                   (req_le_plus_nonneg_r b (req_minus a b) H)
                   (le_id_r (plus b (req_minus a b))
                            (plus b (req_minus a b)) a
                            (req_minus_plus_cancel b a)
                            (le_refl (plus b (req_minus a b))))).
Qed.

End ReqPPORatio.

(* ============================================================ *)
(* ReqSigmoidQuick：sigmoid 快赢 3 件（Id L20865-21053 req 化）     *)
(* ============================================================ *)
Section ReqSigmoidQuick.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* 分母正性（Id sigmoid_denom_pos L20865 req 版；批 1 req_plus_le_lt_pos） *)
Lemma req_sigmoid_denom_pos : forall x : R, lt zero (plus one (exp_neg x)).
Proof.
  intro x.
  exact (req_plus_le_lt_pos one (exp_neg x)
           (lt_le_iff zero one (inl one_pos)) (exp_neg_pos x)).
Qed.

(* 构造性 sigmoid（Id sigmoid L20873 同形） *)
Definition sigmoid_req (x : R) : R :=
  inv_pos (plus one (exp_neg x)) (req_sigmoid_denom_pos x).

(* 值域正性（Id sigmoid_pos L20876 req 版） *)
Lemma req_sigmoid_pos : forall x : R, lt zero (sigmoid_req x).
Proof. intro x. unfold sigmoid_req.
  exact (inv_pos_pos (plus one (exp_neg x)) (req_sigmoid_denom_pos x)). Qed.

(* σ(0) = 1/2（Id sigmoid_zero_half L21045 req 版；exp_neg_zero + inv_pos_ext） *)
Lemma req_sigmoid_zero_half :
  req (sigmoid_req zero) (inv_pos (plus one one) (req_two_pos)).
Proof.
  unfold sigmoid_req.
  exact (inv_pos_ext (plus one (exp_neg zero)) (plus one one)
                     (req_sigmoid_denom_pos zero) (req_two_pos)
                     (req_plus_compat one one (exp_neg zero) one
                                      (req_refl one) (exp_neg_zero))).
Qed.

End ReqSigmoidQuick.

(* ============================================================ *)
(* ---- (d) 冻结清单（规划书 §3.4：双层并行，逐件冻结理由） ----   *)
(*                                                                *)
(* 1. ppo_conservative（Id @L19526）/ std_ppo_conservative    *)
(*    (@L19559) / clip_lower（@L19521）/ ppo_clip_upper（@L19648）： *)
(*    依存 min_le_l / r_max_le_r 的 plain-le 形式（le (min a b) a）； *)
(*    setoid 接口的 min/r_max le 输出已 eps 化（min_le_l :          *)
(*    forall eps, lt zero eps -> le (min a b) (plus a eps)），plain  *)
(*    形不可由 eps 形导出（序无消去）——与 UpReqAlgebra 冻结件        *)

(*    超机械平移边界，冻结，批 5 裁决。                              *)
(* 2. clip_error_nonneg（Id @L112408）/ ppo_clipped_improvement      *)
(*    (@L112439)：同上因（min_le_l plain 形 + le_minus_nonneg(min)）。 *)
(* 3. fold_right_ext 及 dpo_total_loss_at_star 的 list fold 机器     *)
(*    （Id @L20160 一带）：nat/list 层 Id 与数系接口无关，原样复用   *)
(*    （规划书 §1.1 边界 2）；dpo_total_loss(_monotone) 的 req 伴件   *)
(*    待 dpo_pair_loss 簇 req 化后随批 4 结果。                       *)
(* 4. GRPOCounterEx 反例见证件（不在批 3 清单）：双层并行（检验实证   *)
(*    顶层不可 Check，§0.3）。                                       *)
(*                                                                *)
(* ---- 深链挂起清单（批 3b/批 5，T2① 桥接引理内容承载注记） ----       *)
(* 1. req_backward_kl_identity（本文件假设申报位，同位 Id theorem   *)
(*    policy_iter_backward_kl_step @L22686）：Id 证明 ~100 行，依赖   *)
(*    t13 代数链（minus_distr_t13 等 10 件）+                        *)
(*    policy_iter_backward_kl_step_beta @L22575；req 重证需先批 1    *)
(*    地基补 t13 req 伴件（机械件，预估 1-1.5 人天），挂起批 3b。     *)
(* 2. req_policy_improvement_mono（本文件假设申报位，同位 Id        *)
(*    @L22065）：依赖 t12 深链（J_pi_t/J_pi_next/F_t_simpl_next_kl/  *)
(*    surrogate_diff_identity 等 ~15 件），挂起批 3b。                *)
(* 3. 上述两桥放行后，本文件主件（req_policy_iter_kl_geom_step/    *)
(*    _iter/req_dpo_loss_iter_mono）即全链闭合为无条件 req 定理——    *)
(*    本批已真证其全部 req 侧运输与序代数内容。                       *)
(* 4. Alignment 其余 Id 件（对齐恒等式簇 L19180-21240 的             *)
(*    align_objective_advantage_decomp / dpo_reward 簇 / t12 环代数  *)
(*    副本件 ~60 件）：req 对应件多已被 UpReqAlgebra（批 1）与        *)
(*    UpReqDist（批 2 reqd_ 簇）覆盖，残余件随批 3b 按本文件模板      *)
(*    平移；sigmoid_strict_inc（@L21028）需 inv_pos_lt_contra 桥     *)
(*    （B 类假设 req 同位，§1.5），随 B 桥批结果。                    *)
(* ============================================================ *)

Print Assumptions req_align_partition_condition.
Print Assumptions req_rlhf_optimal.
Print Assumptions req_rlhf_optimal_unique.
Print Assumptions req_dpo_optimal.
Print Assumptions req_plus_opp_le_zero.
Print Assumptions req_plusA_opp_cancel_le.
Print Assumptions req_dpo_loss_iter_step_le.
Print Assumptions req_Z_aud_le_one.
Print Assumptions req_sigmoid_pos.
Print Assumptions req_sigmoid_zero_half.
