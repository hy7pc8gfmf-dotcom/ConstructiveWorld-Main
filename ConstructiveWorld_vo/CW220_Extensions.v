(* ============================================================ *)
(* ToyR 玩具证替换件 —— T254 台账席 战役包O（tier2 第五批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   r_arch_pow_attn_real（原 L1537，2 句玩具证）                         *)
(*   one_minus_delta_pos_real（原 L1506，2 句玩具证）                     *)
(*   req_mult_one_l（原 L231，2 句玩具证）                                *)
(*   req_plus_zero_r（原 L224，2 句玩具证）                               *)
(*   hlogz_discharge_full（原 L91，2 句玩具证）                           *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T321 恒等守恒更正注记】2026-09-22 包AW九 台账席（恒等头注更正全量第一批）                     *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经 T277（包AL）全量恒等核查已证结论、T317（包AV六）试点已证结论：本件实测                             *)
(* 为恒等守恒——清单所列 5 槽证明体与 Main 现版原件逐字同文（刀体                                *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此更正。                                        *)
(* 更正口径：真替换 0 槽＋恒等守恒 5 槽；本注记为追加块，上方原头                                  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；台账承载见 T277 附录／T284 修正块／T317 评估册／T321 台账。                        *)
(* 附记：T277 判级全文恒等；包O 全量第一批整批直推（T317 六·1 方案①）                           *)
(* ============================================================ *)

(* ===================================================================== *)
(* CW220_Extensions.v — 扩展层（仅保留活跃分区）                           *)
(*   基座：CW_ConstructiveWorld_219（薄壳 Require Export 全部 15 模块）     *)
(*                                                                    *)
(* 瘦身依据：                                        *)
(*   1. 全量编译 20/99 断于本文件 L12525（Module EvictId 内投影 Let 绑定     *)
(*      `Let R := @R RI` 构建期 dedot 后误解析到 S01_BaseRing.R : Set）——    *)
(*      该病灶随 G13_EvictFam 分区整体剔除而消失。                            *)
(*   2. 原 34 件合并区中 30 件与 Live_X 独立件（Up*.v，四项关卡通过且已收录）      *)
(*      /G 组成员同名冗余，均为旧拷贝，全部剔除。                          *)
(*   3. 活价值只剩两个 Module 的 12 名：                                  *)
(*      - G07_KLWall.G07_KLWall 需要 BudgetReal 4 名：                   *)
(*        r_arch_pow_real / real_pow / one_minus_delta_pos_real /          *)
(*        one_minus_delta_lt_one_real（后两名为根层 UpArchAttn 分区供给，    *)
(*        其 Import BudgetReal 依赖 BudgetReal 先在）。                    *)
(*      - G12_ZPosFam.G12_ZPosFam 需要 SigMigrate 8 名：                   *)
(*        Z_thermo / boltzmann_dist_attn / boltzmann_factor /              *)
(*        cwe_exp_pos_fn / cwe_partition_function_temp / cwe_softmax_temp   *)
(*        / req_attention_is_gibbs_temp / req_mult_opp_l。                 *)
(*   4. 保留分区链闭包：G01_CoreMicro（BudgetReal 的 log_kappa_neg 依存           *)
(*      hlogz_strict）。其余保留分区对被剔除分区零引用（声明名交叉核查       *)
(*      + 限定名扫描双验证；real_log_le_mono 等来自基座 S14）。             *)
(*                                                                    *)
(* 保留分区清单（4 件，原顺序）：                                          *)
(*   G01_CoreMicro      （原 L437–541）                                        *)
(*   UpSigMigrate （原 L1410–1996，Module SigMigrate）                    *)
(*   UpBudgetReal （原 L10250–10967，Module BudgetReal）                  *)
(*   UpArchAttn   （原 L10968–11177，根层，Import BudgetReal）             *)
(* 剔除分区清单见 _lxR 归档（回滚用原件备份          *)
(*   _lxR_backup-CW220-orig-20260911.v）。                               *)
(*                                                                    *)
(* 下游接口零改动：G07 `Require Import CW220_Extensions.` +               *)
(*   `Import CW220_Extensions.BudgetReal.`；G12 `Require Import            *)
(*   CW220_Extensions.` + `@SigMigrate.<名>` 全参形。                     *)
(* ===================================================================== *)

Require Import CW_ConstructiveWorld_219.

(* ---------- G01_CoreMicro ---------- *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
(* ============================================================ *)
(* G01_CoreMicro.v —— 根内 KLProjection 主定理 HlogZ 前提的 Real 层总证明   *)
(*                                                              *)
(* 目标：projected_distribution_minimizes_kl（KLProjection.v L189）  *)
(* 的显式前提 HlogZ : le (log Z_aud) zero 在 Real 层总是成立：        *)
(*   Z_aud ≤ 1（Z_aud_le_one，根内已证）                           *)
(*   ⟹ log Z_aud ≤ log 1 = 0                                      *)
(*     （log 单调 le 版 = G01_CoreMicro.real_log_le_mono；              *)
(*       log 1 == 0 = real_log_one，根内已证）。                    *)
(*                                                              *)
(* 结果清单：                                                      *)
(*   hlogz_discharge       —— 主证明：0 < Z ≤ 1 ⟹ log Z ≤ 0        *)
(*   hlogz_discharge_full  —— 同型对齐版（走 G01_CoreMicro 直用形态）    *)
(*   hlogz_strict          —— 严格版：0 < Z < 1 ⟹ log Z < 0         *)
(*                            （过滤器确实拦截了质量）               *)
(*   hlogz_opp_nonneg      —— KL 尾项形态：0 ≤ opp (log Z)          *)
(*                            （主定理证明中 opp_le_compat 的直接输入）*)
(*                                                              *)
(* 全部 Real 层、Set 层语句（real_lt / real_le / real_eq，Or 编码）、 *)
(* 纯构造、全 Qed 闭合、可提取。                                    *)
(* ============================================================ *)


(* ================================================================ *)
(* 主结果 1：HlogZ 证明（log 单调 le 版直推）                          *)
(*   论证：0 < Za、Za ≤ 1 ⟹ real_log Za ≤ real_log 1 == 0。           *)
(*   real_log_le_mono : real_le a b -> real_le (log a) (log b)       *)
(*   （a b 皆正前提由 HZa 与 real_lt_zero_one 供给）。                 *)
(* ================================================================ *)
Theorem hlogz_discharge :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  assert (Hone : real_lt real_zero real_one) by exact real_lt_zero_one.
  (* 经中项 real_log 1 的 le 链合成 *)
  apply (real_le_trans _ (real_log real_one Hone) _).
  - (* 单调 le 版：Za ≤ 1 ⟹ log Za ≤ log 1 *)
    exact (real_log_le_mono Za real_one HZa Hone HZa1).
  - (* log 1 == 0 经 eq → le 桥（inr 支）升 le *)
    exact (real_eq_le_bridge (real_log real_one Hone) real_zero
             (real_log_one Hone)).
Qed.

(* ================================================================ *)
(* 主结果 2：HlogZ 证明完整版（与 KLProjection 前提对齐）               *)
(*   同型语句，走 G01_CoreMicro 直用形态 real_log_le_zero_of_le_one，      *)
(*   双路互证（单调链合成 / 直用形态殊途同归）。                        *)
(* ================================================================ *)
Theorem hlogz_discharge_full :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  exact (real_log_le_zero_of_le_one Za HZa HZa1).
Qed.

(* ================================================================ *)
(* 附加结果 1：严格版——过滤器确实拦截了质量                            *)
(*   0 < Za < 1 ⟹ log Za < log 1 = 0（lt 严格链）。                   *)
(*   real_log_lt_mono 论 cw_log；real_log 定义性展开（:= cw_log）后    *)
(*   逐项对接，尾端经 real_lt_eq_lt 把 log 1 换成 0。                  *)
(* ================================================================ *)
Theorem hlogz_strict :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_lt Za real_one),
  real_lt (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  assert (Hone : real_lt real_zero real_one) by exact real_lt_zero_one.
  apply (real_lt_eq_lt _ (cw_log real_one Hone) _).
  - (* 严格单调：Za < 1 ⟹ cw_log Za < cw_log 1 *)
    unfold real_log.
    exact (real_log_lt_mono Za real_one HZa Hone HZa1).
  - (* cw_log 1 == 0 *)
    exact (real_log_one Hone).
Qed.

(* ================================================================ *)
(* 附加结果 2：KL 尾项形态——0 ≤ opp (log Z)                           *)
(*   主定理证明里「尾项 T == opp (log Z_aud) ≥ 0」的直接 Real 层供给：  *)
(*   log Z ≤ 0 经 opp 反变（real_opp_le_compat）→ opp 0 ≤ opp (log Z)，*)
(*   再用 opp 0 == 0 的 eq → le 桥（inl 支？否，inr 支）合成。          *)
(* ================================================================ *)
Theorem hlogz_opp_nonneg :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le real_zero (real_opp (real_log Za HZa)).
Proof.
  intros Za HZa HZa1.
  apply (real_le_trans _ (real_opp real_zero) _).
  - (* 0 ≤ opp 0：eq 对称后升 le *)
    exact (real_eq_le_bridge real_zero (real_opp real_zero)
             (real_eq_sym (real_opp real_zero) real_zero real_opp_zero)).
  - (* opp 0 ≤ opp (log Z)：反变 + 主结果 1 *)
    exact (real_opp_le_compat (real_log Za HZa) real_zero
             (hlogz_discharge Za HZa HZa1)).
Qed.

(* 提取检验（Warning 消音：透明度旁路访问清单提示，与 UpGRPO 同法） *)
Set Warnings "-extraction-opaque-accessed".

Extraction "uphlogz.ml" hlogz_discharge hlogz_strict hlogz_opp_nonneg.

(* ---------- UpSigMigrate ---------- *)
Module SigMigrate.
(* UpSigMigrate.v — 抽象层签名对接试点：Id 系 → setoid 系（req := real_eq）
   试点 1（必做）: req_free_energy_kl_decomp —— F[p] == F[p_b] + D·KL(p‖p_b) 的
     setoid 签名版：Section Context 换 RealInterfaceEnhancedSetoid；
     Id → req 全迁移；normalized := req (Σ p) one；log 族带正性前提。
   试点 2（尽力）: req_attention_is_gibbs_temp —— 三前提 + 逐点结论全 req。
   纪律：纯构造性；Set 层（req/lt/le 均 Set 值，语句零 Prop）；
   中间等式全走 req 字段（req_trans 链 + compat 桥），destruct 消去不可用。 *)
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 试点 1：FreeEnergyMinimization 节的 setoid 签名对接           *)
(*   Id 原件：CW L15759-16440（Context {RI : RealInterfaceEnhanced}， *)
(*   StateSpace/SumOver 为 Id 系类，其字段带 Id——故本试点以       *)
(*   req 签名的求和三性质作为节假设申报位（= SumOver 类的       *)
(*   setoid 对接面），对接成本计入报告；上游两条 Id 系已证        *)
(*   引理（energy_in_log_boltzmann / free_energy_boltzmann）以    *)
(*   req 签名桥假设申报位承接，全量迁移外推见报告。            *)
(* ============================================================ *)
Section ReqFreeEnergyPilot.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

(* ---- SumOver 的 req 签名对接面（Id 系 SumOver L1400 的 setoid 副本） ---- *)
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).

(* ---- 节参数（对齐 Id 系 L15778-15791） ---- *)
Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable Z : R.
Variable Z_pos : lt zero Z.
Hypothesis partition_condition :
  req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).

(* ---- 节内定义（setoid 惯例形态） ---- *)
Definition cwe_positive_dist (p : S -> R) : Set := forall s : S, lt zero (p s).
Definition cwe_boltzmann_dist : S -> R :=
  fun s => mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).
(* log 族带正性前提（setoid 接口 L40570），故 free_energy 限定在正性分布上 *)
Definition cwe_free_energy (p : S -> R) (Hp : cwe_positive_dist p) : R :=
  plus (sumf (fun s => mult (p s) (base_loss s)))
       (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition cwe_normalized (p : S -> R) : Set := req (sumf p) one.
Definition rminus (a b : R) : R := plus a (opp b).

(* ---- Boltzmann 分布正性（setoid log 前提所需；接口字段直接组装） ---- *)
Lemma req_boltzmann_positive : cwe_positive_dist cwe_boltzmann_dist.
Proof.
  intro s.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

(* ---- 上游 Id 系已证成果的 req 签名桥（Id 原件 L16116 / L15945） ---- *)
Hypothesis energy_in_log_boltzmann_bridge :
  forall s : S,
    req (base_loss s)
        (opp (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))
                           (log Z Z_pos)))).
Hypothesis free_energy_boltzmann_bridge :
  req (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive)
      (mult (opp D) (log Z Z_pos)).

(* ============================================================ *)
(* A. 代数前奏：req 版 opp 代数（接口字段纯推导，零 destruct，   *)
(*    全 req_trans 链 + compat 桥——Id 系 rewrite 消去不可用）    *)
(* ============================================================ *)

(* 加零右形式：plus_zero 字段只有左形式，右形式走 comm 桥 *)
Lemma req_plus_zero_r : forall a : R, req (plus zero a) a.
Proof.
  intro a.
  exact (req_trans (plus zero a) (plus a zero) a (plus_comm zero a) (plus_zero a)).
Qed.

(* 单位元左形式：mult_one 字段只有右形式 *)
Lemma req_mult_one_l : forall a : R, req (mult one a) a.
Proof.
  intro a.
  exact (req_trans (mult one a) (mult a one) a (mult_comm one a) (mult_one a)).
Qed.

(* 左消去：opp 唯一性的引擎（Id 系经 destruct/注入免费获得，此处 7 段链） *)
Lemma req_add_cancel_l : forall (u v w : R),
  req (plus u v) (plus w v) -> req u w.
Proof.
  intros u v w H.
  apply (req_trans u (plus u zero) w).
  - apply (req_sym (plus u zero) u). apply plus_zero.
  - apply (req_trans (plus u zero) (plus u (plus v (opp v))) w).
    + apply (req_plus_compat u u zero (plus v (opp v))).
      * apply req_refl.
      * apply (req_sym (plus v (opp v)) zero). apply plus_opp.
    + apply (req_trans (plus u (plus v (opp v))) (plus (plus u v) (opp v)) w).
      * apply plus_assoc.
      * apply (req_trans (plus (plus u v) (opp v)) (plus (plus w v) (opp v)) w).
        -- apply (req_plus_compat (plus u v) (plus w v) (opp v) (opp v) H).
           apply req_refl.
        -- apply (req_trans (plus (plus w v) (opp v)) (plus w (plus v (opp v))) w).
           ++ apply (req_sym (plus w (plus v (opp v))) (plus (plus w v) (opp v))).
              apply plus_assoc.
           ++ apply (req_trans (plus w (plus v (opp v))) (plus w zero) w).
              ** apply (req_plus_compat w w (plus v (opp v)) zero).
                 --- apply req_refl.
                 --- apply plus_opp.
              ** apply plus_zero.
Qed.

(* 双重负号：opp (opp a) == a（两次 plus_opp + 消去；Id 系 double_neg 引理） *)
Lemma req_double_neg : forall a : R, req (opp (opp a)) a.
Proof.
  intro a.
  apply (req_add_cancel_l (opp (opp a)) (opp a) a).
  apply (req_trans (plus (opp (opp a)) (opp a)) zero (plus a (opp a))).
  - apply (req_trans (plus (opp (opp a)) (opp a)) (plus (opp a) (opp (opp a))) zero).
    + apply plus_comm.
    + apply plus_opp.
  - apply (req_sym (plus a (opp a)) zero). apply plus_opp.
Qed.

(* 负号分配：opp (a+b) == opp a + opp b（Id 系 opp_plus 引理） *)
Lemma req_opp_plus : forall a b : R, req (opp (plus a b)) (plus (opp a) (opp b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (opp (plus a b)) (plus a b) (plus (opp a) (opp b))).
  apply (req_trans (plus (opp (plus a b)) (plus a b)) zero (plus (plus (opp a) (opp b)) (plus a b))).
  - apply (req_trans (plus (opp (plus a b)) (plus a b)) (plus (plus a b) (opp (plus a b))) zero).
    + apply plus_comm.
    + apply plus_opp.
  - apply (req_sym (plus (plus (opp a) (opp b)) (plus a b)) zero).
    apply (req_trans (plus (plus (opp a) (opp b)) (plus a b))
                     (plus (opp a) (plus (opp b) (plus a b)))
                     zero).
    + apply (req_sym (plus (opp a) (plus (opp b) (plus a b)))
                     (plus (plus (opp a) (opp b)) (plus a b))).
      apply plus_assoc.
    + apply (req_trans (plus (opp a) (plus (opp b) (plus a b)))
                       (plus (opp a) (plus (plus (opp b) a) b))
                       zero).
      * apply (req_plus_compat (opp a) (opp a) (plus (opp b) (plus a b)) (plus (plus (opp b) a) b)).
        -- apply req_refl.
        -- apply plus_assoc.
      * apply (req_trans (plus (opp a) (plus (plus (opp b) a) b))
                         (plus (opp a) (plus (plus a (opp b)) b))
                         zero).
        -- apply (req_plus_compat (opp a) (opp a) (plus (plus (opp b) a) b) (plus (plus a (opp b)) b)).
           ++ apply req_refl.
           ++ apply (req_plus_compat (plus (opp b) a) (plus a (opp b)) b b).
              ** apply plus_comm.
              ** apply req_refl.
        -- apply (req_trans (plus (opp a) (plus (plus a (opp b)) b))
                            (plus (plus (opp a) a) (plus (opp b) b))
                            zero).
           ++ apply (req_trans (plus (opp a) (plus (plus a (opp b)) b))
                               (plus (opp a) (plus a (plus (opp b) b)))
                               (plus (plus (opp a) a) (plus (opp b) b))).
              ** apply (req_plus_compat (opp a) (opp a) (plus (plus a (opp b)) b) (plus a (plus (opp b) b))).
                 --- apply req_refl.
                 --- apply (req_sym (plus a (plus (opp b) b)) (plus (plus a (opp b)) b)). apply plus_assoc.
              ** apply plus_assoc.
           ++ apply (req_trans (plus (plus (opp a) a) (plus (opp b) b)) (plus zero zero) zero).
              ** apply (req_plus_compat (plus (opp a) a) zero (plus (opp b) b) zero).
                 --- apply (req_trans (plus (opp a) a) (plus a (opp a)) zero).
                     +++ apply plus_comm.
                     +++ apply plus_opp.
                 --- apply (req_trans (plus (opp b) b) (plus b (opp b)) zero).
                     +++ apply plus_comm.
                     +++ apply plus_opp.
              ** apply plus_zero.
Qed.

(* mult a (opp b) == opp (mult a b)（Id 系 opp_mult_l 引理） *)
Lemma req_mult_opp_l : forall a b : R, req (mult a (opp b)) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (mult a (opp b)) (mult a b) (opp (mult a b))).
  apply (req_trans (plus (mult a (opp b)) (mult a b)) zero (plus (opp (mult a b)) (mult a b))).
  - apply (req_trans (plus (mult a (opp b)) (mult a b)) (plus (mult a b) (mult a (opp b))) zero).
    + apply plus_comm.
    + apply (req_trans (plus (mult a b) (mult a (opp b))) (mult a (plus b (opp b))) zero).
      * apply (req_sym (mult a (plus b (opp b))) (plus (mult a b) (mult a (opp b)))).
        apply distrib.
      * apply (req_trans (mult a (plus b (opp b))) (mult a zero) zero).
        -- apply (req_mult_compat a a (plus b (opp b)) zero).
           ++ apply req_refl.
           ++ apply plus_opp.
        -- apply mult_zero.
  - apply (req_sym (plus (opp (mult a b)) (mult a b)) zero).
    apply (req_trans (plus (opp (mult a b)) (mult a b)) (plus (mult a b) (opp (mult a b))) zero).
    + apply plus_comm.
    + apply plus_opp.
Qed.

(* mult (opp a) b == opp (mult a b)（Id 系 opp_mult_r 引理，经 comm 桥） *)
Lemma req_opp_mult_l : forall a b : R, req (mult (opp a) b) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_trans (mult (opp a) b) (mult b (opp a)) (opp (mult a b))).
  - apply mult_comm.
  - apply (req_trans (mult b (opp a)) (opp (mult b a)) (opp (mult a b))).
    + apply req_mult_opp_l.
    + apply (req_opp_compat (mult b a) (mult a b)). apply mult_comm.
  Qed.

(* ============================================================ *)
(* B. 求和层 req 引理（SumOver req 对接面之上的转译）            *)
(* ============================================================ *)

(* Σ opp f == opp Σ f（Id 原件 L15801 sum_opp） *)
Lemma req_sum_opp :
  forall f : S -> R, req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (sum_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))).
    intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s))) (mult (opp one) (f s))).
    + apply (req_opp_compat (f s) (mult one (f s))).
      apply (req_sym (mult one (f s)) (f s)). apply req_mult_one_l.
    + apply (req_sym (mult (opp one) (f s)) (opp (mult one (f s)))).
      apply req_opp_mult_l.
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f))
                     (opp (sumf f))).
    + apply (sum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f)) (opp (mult one (sumf f))) (opp (sumf f))).
      * apply req_opp_mult_l.
      * apply (req_opp_compat (mult one (sumf f)) (sumf f)). apply req_mult_one_l.
Qed.

(* Boltzmann 分布归一化（Id 原件 L15846 boltzmann_normalized 的 req 版） *)
Lemma req_boltzmann_normalized : req (sumf cwe_boltzmann_dist) one.
Proof.
  apply (req_trans (sumf cwe_boltzmann_dist)
                   (mult (inv_pos Z Z_pos)
                         (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                   one).
  - exact (sum_linear (inv_pos Z Z_pos)
                      (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
  - apply (req_trans (mult (inv_pos Z Z_pos)
                           (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                     (mult (inv_pos Z Z_pos) Z)
                     one).
    + apply (req_mult_compat (inv_pos Z Z_pos) (inv_pos Z Z_pos)
                             (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z).
      * apply req_refl.
      * apply (req_sym Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))))).
        exact partition_condition.
    + apply (req_trans (mult (inv_pos Z Z_pos) Z) (mult Z (inv_pos Z Z_pos)) one).
      * apply mult_comm.
      * apply inv_pos_correct.
Qed.

(* ============================================================ *)
(* C. 逐点分解（Id 原件 L16198 p_times_energy_decomp 的 req 版） *)
(* ============================================================ *)
Lemma req_p_times_energy_decomp :
  forall (p : S -> R) (s : S),
    req (mult (p s) (base_loss s)) (plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos))))).
Proof.
  intros p s.
  assert (HlegA : req (mult (p s) (base_loss s)) (opp (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))))).
  { apply (req_trans (mult (p s) (base_loss s)) (mult (p s) (opp (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))))).
    - apply (req_mult_compat (p s) (p s) (base_loss s) (opp (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
      * apply req_refl.
      * apply (energy_in_log_boltzmann_bridge s).
    - apply (req_mult_opp_l (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))). }
  assert (Hswap : req (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
  { apply (req_trans (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult (mult (p s) D) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
    - apply mult_assoc.
      - apply (req_trans (mult (mult (p s) D) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (mult (mult D (p s)) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
        * apply (req_mult_compat (mult (p s) D) (mult D (p s)) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))).
          { apply mult_comm. }
          { apply req_refl. }
        * apply (req_sym (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult (mult D (p s)) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))). apply mult_assoc.
  }
  assert (Hdist2 : req (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))).
  { apply (req_trans (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (plus (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))).
    - apply (req_mult_compat D D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (plus (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))).
      + apply req_refl.
      + apply distrib.
    - apply distrib. }
  apply (req_trans (mult (p s) (base_loss s)) (opp (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
  - exact HlegA.
  - apply (req_trans (opp (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
    + apply (req_opp_compat (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))). exact Hswap.
    + apply (req_trans (opp (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (plus (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
      * apply (req_opp_compat (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))). exact Hdist2.
      * apply req_opp_plus.
Qed.
(* ============================================================ *)
(* D. 主迁移：req_free_energy_kl_decomp                        *)
(*    F[p] == F[p_b] + D·KL(p‖p_b)（Id 原件 L16259 的 setoid 签名版） *)
(*    记号：lgpb s := log (cwe_boltzmann_dist s) Hpb；lgps s := log (p s) Hp； *)
(*    A := D·Σ p·lgpb；B := D·Σ p·lgps；DlgZ := D·log Z；        *)
(*    KL := fun s => p s · (lgps s − lgpb s)；Fpb := cwe_free_energy p_b *)
(* ============================================================ *)
Theorem req_free_energy_kl_decomp :
  forall (p : S -> R) (Hp : cwe_normalized p) (p0 : cwe_positive_dist p),
    req (cwe_free_energy p p0)
        (plus (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive)
              (mult D (sumf (fun s =>
                mult (p s) (rminus (log (p s) (p0 s))
                                   (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
Proof.
  intros p Hp p0.
  (* 桥：F[p_b] == mult (opp D) lgZ == opp (D·lgZ)（Id 系步骤 2 的 req 形态） *)
  assert (Hfb' : req (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive)
                     (opp (mult D (log Z Z_pos)))).
  { apply (req_trans (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive)
                     (mult (opp D) (log Z Z_pos))
                     (opp (mult D (log Z Z_pos)))).
    - exact free_energy_boltzmann_bridge.
    - apply req_opp_mult_l. }
  (* 步骤 1：Σ p·E == opp A + opp DlgZ（Id 原件 Hse） *)
  assert (Hse : req (sumf (fun s => mult (p s) (base_loss s)))
                    (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                          (opp (mult D (log Z Z_pos))))).
  { apply (req_trans (sumf (fun s => mult (p s) (base_loss s)))
                     (sumf (fun s => plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                          (opp (mult D (mult (p s) (log Z Z_pos))))))
                     (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (mult D (log Z Z_pos))))).
    - apply (sum_ext (fun s => mult (p s) (base_loss s))
                     (fun s => plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                    (opp (mult D (mult (p s) (log Z Z_pos)))))).
      { intro s. apply req_p_times_energy_decomp. }
    - apply (req_trans (sumf (fun s => plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                            (opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (sumf (fun s => opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                             (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                             (opp (mult D (log Z Z_pos))))).
      { apply sum_add. }
      { apply (req_plus_compat (sumf (fun s => opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                               (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                               (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos)))))
                               (opp (mult D (log Z Z_pos)))).
        - (* Σ opp(D·p·lgpb) == opp(D·Σ p·lgpb)：sum_opp + D 线性提取 *)
          apply (req_trans (sumf (fun s => opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (sumf (fun s => mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
          { apply req_sum_opp. }
          { apply (req_opp_compat (sumf (fun s => mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                  (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
            { apply (sum_linear D (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))). } }
        - (* Σ opp(D·p·lgZ) == opp(D·lgZ)：sum_opp + D 线性 + Σ p·lgZ = lgZ·Σp = lgZ 归一化链 *)
          apply (req_trans (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos)))))
                           (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                           (opp (mult D (log Z Z_pos)))).
          { apply req_sum_opp. }
          { apply (req_trans (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                             (opp (mult D (sumf (fun s => mult (p s) (log Z Z_pos)))))
                             (opp (mult D (log Z Z_pos)))).
            { apply (req_opp_compat (sumf (fun s => mult D (mult (p s) (log Z Z_pos))))
                                    (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))).
              { apply (sum_linear D (fun s => mult (p s) (log Z Z_pos))). } }
            { apply (req_opp_compat (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))
                                    (mult D (log Z Z_pos))).
              { apply (req_mult_compat D D (sumf (fun s => mult (p s) (log Z Z_pos))) (log Z Z_pos)).
                { apply req_refl. }
                { apply (req_trans (sumf (fun s => mult (p s) (log Z Z_pos)))
                                   (sumf (fun s => mult (log Z Z_pos) (p s)))
                                   (log Z Z_pos)).
                  { apply (sum_ext (fun s => mult (p s) (log Z Z_pos)) (fun s => mult (log Z Z_pos) (p s))).
                    { intro s2. apply mult_comm. } }
                  { apply (req_trans (sumf (fun s => mult (log Z Z_pos) (p s)))
                                     (mult (log Z Z_pos) (sumf p))
                                     (log Z Z_pos)).
                    { apply (sum_linear (log Z Z_pos) p). }
                    { apply (req_trans (mult (log Z Z_pos) (sumf p))
                                       (mult (log Z Z_pos) one)
                                       (log Z Z_pos)).
                      { apply (req_mult_compat (log Z Z_pos) (log Z Z_pos) (sumf p) one).
                        { apply req_refl. }
                        { exact Hp. } }
                      { apply mult_one. } } } } } } }
  }
  }
  (* 步骤 3：D·KL == B + opp A（Id 原件 Hkl） *)
  assert (Hkl : req (mult D (sumf (fun s =>
                      mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                    (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                          (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
  { assert (Hpt2 : forall s : S,
        req (mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))
            (plus (mult (p s) (log (p s) (p0 s)))
                  (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
    { intro s. unfold rminus.
      apply (req_trans (mult (p s) (plus (log (p s) (p0 s)) (opp (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                       (plus (mult (p s) (log (p s) (p0 s))) (mult (p s) (opp (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                       (plus (mult (p s) (log (p s) (p0 s)))
                             (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
      { apply distrib. }
      { apply (req_plus_compat (mult (p s) (log (p s) (p0 s))) (mult (p s) (log (p s) (p0 s)))
                               (mult (p s) (opp (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))
                               (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))).
        { apply req_refl. }
        { apply req_mult_opp_l. } } }
    assert (Hinner : req (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                               (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
    { apply (req_trans (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                       (sumf (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                       (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                             (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
      { apply (sum_ext (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))
                       (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
        { exact Hpt2. } }
      { apply (req_trans (sumf (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s)))) (sumf (fun s => opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                               (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
        { apply sum_add. }
        { apply (req_plus_compat (sumf (fun s => mult (p s) (log (p s) (p0 s)))) (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                 (sumf (fun s => opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                 (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
          { apply req_refl. }
          { apply req_sum_opp. } } } }
    apply (req_trans (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                     (mult D (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
    { apply (req_mult_compat D D
                             (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                             (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
      { apply req_refl. }
      { exact Hinner. } }
    apply (req_trans (mult D (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
    { apply distrib. }
    apply (req_plus_compat (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
    { apply req_refl. }
    { apply req_mult_opp_l. } }

  (* 步骤 4：环代数坍缩（Id 原件 Hfin：(opp A + opp DlgZ) + B → opp DlgZ + (B + opp A)） *)
  assert (Hfin : req (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))
                     (plus (opp (mult D (log Z Z_pos))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))))).
  { set (A := (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
    set (DlgZ := (mult D (log Z Z_pos))).
    set (B := (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))).
    apply (req_trans (plus (plus (opp A) (opp DlgZ)) B)
                     (plus (opp A) (plus (opp DlgZ) B))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_sym (plus (opp A) (plus (opp DlgZ) B))
                     (plus (plus (opp A) (opp DlgZ)) B)).
      apply plus_assoc. }
    apply (req_trans (plus (opp A) (plus (opp DlgZ) B))
                     (plus (opp A) (plus B (opp DlgZ)))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_plus_compat (opp A) (opp A) (plus (opp DlgZ) B) (plus B (opp DlgZ))).
      { apply req_refl. }
      { apply plus_comm. } }
    apply (req_trans (plus (opp A) (plus B (opp DlgZ)))
                     (plus (plus (opp A) B) (opp DlgZ))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply plus_assoc. }
    apply (req_trans (plus (plus (opp A) B) (opp DlgZ))
                     (plus (plus B (opp A)) (opp DlgZ))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_plus_compat (plus (opp A) B) (plus B (opp A)) (opp DlgZ) (opp DlgZ)).
      { apply plus_comm. }
      { apply req_refl. } }
    apply plus_comm. }
  (* 装配：Hleg1（cwe_free_energy p 定义展开 conversion + Hse 于 compat 槽）；Hleg2（Hfin + Hfb'/Hkl 反向收尾槽） *)
  assert (Hleg1 : req (cwe_free_energy p p0) (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))).
  { unfold cwe_free_energy.
    apply (req_plus_compat (sumf (fun s => mult (p s) (base_loss s))) (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))).
    { exact Hse. }
    { apply req_refl. } }
  assert (Hleg2 : req (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))) (plus (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive) (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
  { apply (req_trans (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))
                      (plus (opp (mult D (log Z Z_pos))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))))
                      (plus (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive) (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
    { exact Hfin. }
    { apply (req_plus_compat (opp (mult D (log Z Z_pos))) (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))) (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
      { apply (req_sym (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive) (opp (mult D (log Z Z_pos)))). exact Hfb'. }
      { apply (req_sym (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))). exact Hkl. } } }
  exact (req_trans _ _ _ Hleg1 Hleg2).
Qed.

End ReqFreeEnergyPilot.

(* ============================================================ *)
(* 试点 2（尽力）：req_attention_is_gibbs_temp                    *)
(*   Id 原件：CW L28634（AttentionGibbsBridge 节，L27929-28710）。*)
(*   三前提 + 逐点结论全 req 迁移；节内基础设施（exp_pos_fn /      *)
(*   partition_function_temp / softmax_temp / boltzmann_factor /  *)
(*   Z_thermo / boltzmann_dist_attn）按同形定义重建。             *)
(*   接口缺口发现：RealInterfaceEnhancedSetoid 无 exp_neg 兼容     *)
(*   字段（Id 系 id_cong 免费可得），以 req 签名桥假设申报位      *)
(*   承接——Real 实例由 cauchy_real_exp_wd 满足（L40440 先例）。    *)
(* ============================================================ *)
Section ReqGibbsPilot.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_pos : forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
(* 接口缺口桥：exp_neg 的 req 兼容（字段缺失，见上注） *)
Hypothesis req_exp_neg_ext : forall x y : R, req x y -> req (exp_neg x) (exp_neg y).

Variable T : R.
Variable T_pos : lt zero T.
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.
Variable z : S -> R.

Definition cwe_exp_pos_fn (x : R) : R := exp_neg (opp x).
Definition cwe_partition_function_temp : R :=
  sumf (fun s => cwe_exp_pos_fn (mult (inv_pos T T_pos) (z s))).
Hypothesis partition_function_temp_pos : lt zero cwe_partition_function_temp.
Definition cwe_softmax_temp (s : S) : R :=
  mult (cwe_exp_pos_fn (mult (inv_pos T T_pos) (z s)))
       (inv_pos cwe_partition_function_temp partition_function_temp_pos).
Definition boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).
Definition Z_thermo : R := sumf boltzmann_factor.
Variable Z_thermo_pos : lt zero Z_thermo.
Definition boltzmann_dist_attn (s : S) : R :=
  mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s).

Theorem req_attention_is_gibbs_temp :
  (req (inv_pos T T_pos) (inv_pos D D_pos)) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  (req Z_thermo cwe_partition_function_temp) ->
  forall s : S, req (cwe_softmax_temp s) (boltzmann_dist_attn s).
Proof.
  intros HD Henergy HZ s.
  assert (Hf : req (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                   (exp_neg (mult (inv_pos D D_pos) (energy s)))).
  { apply (req_exp_neg_ext (opp (mult (inv_pos T T_pos) (z s)))
                           (mult (inv_pos D D_pos) (energy s))).
    apply (req_trans (opp (mult (inv_pos T T_pos) (z s)))
                     (mult (inv_pos T T_pos) (opp (z s)))
                     (mult (inv_pos D D_pos) (energy s))).
    - exact (req_sym (mult (inv_pos T T_pos) (opp (z s)))
                     (opp (mult (inv_pos T T_pos) (z s)))
                     (req_mult_opp_l (inv_pos T T_pos) (z s))).
    - apply (req_mult_compat (inv_pos T T_pos) (inv_pos D D_pos) (opp (z s)) (energy s)).
      + exact HD.
      + apply (req_sym (energy s) (opp (z s))). apply Henergy. }
  assert (Hie : req (inv_pos Z_thermo Z_thermo_pos)
                    (inv_pos cwe_partition_function_temp partition_function_temp_pos)).
  { apply (inv_pos_ext Z_thermo cwe_partition_function_temp
                       Z_thermo_pos partition_function_temp_pos HZ). }
  unfold cwe_softmax_temp, boltzmann_dist_attn, boltzmann_factor, cwe_exp_pos_fn.
  apply (req_trans (mult (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                             (inv_pos cwe_partition_function_temp partition_function_temp_pos))
                       (mult (exp_neg (mult (inv_pos D D_pos) (energy s)))
                             (inv_pos Z_thermo Z_thermo_pos))
                       (mult (inv_pos Z_thermo Z_thermo_pos)
                             (exp_neg (mult (inv_pos D D_pos) (energy s))))).
    { apply (req_mult_compat (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                             (exp_neg (mult (inv_pos D D_pos) (energy s)))
                             (inv_pos cwe_partition_function_temp partition_function_temp_pos)
                             (inv_pos Z_thermo Z_thermo_pos)).
      { exact Hf. }
      { apply (req_sym (inv_pos Z_thermo Z_thermo_pos) (inv_pos cwe_partition_function_temp partition_function_temp_pos)). exact Hie. } }
    apply mult_comm.
Qed.

End ReqGibbsPilot.
End SigMigrate.

(* ---------- UpBudgetReal ---------- *)
Module BudgetReal.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
(* ============================================================ *)
(* UpBudgetReal.v —— 几何击穿的 Real 层显式迭代预算定理            *)
(*                                                              *)
(* 论文 4（梯度动力学收敛）主贡献「显式迭代预算」的 Real 层载体：    *)
(* 根文件 ConvergenceCauchy 节的接口前提                          *)
(*   r_arch_pow : 0 < a -> 0 < eps -> sigT (fun n => a·κ^n < eps) *)
(* 至今只有接口假设形态；本文件在具体柯西实数（CW_ConstructiveWorld_219 的     *)
(* Real := sigT (fun u : Qseq => cauchy u)）上闭合该缺口：        *)
(*                                                              *)
(* 主结果 r_arch_pow_real：                                      *)
(*   ∀κ a eps（0<κ<1、0<a、0<eps），存在显式 nat 见证 N 使          *)
(*   a·κ^N < eps。                                               *)
(* 构造路线（路线 A，纯 Real 层，无需 Q 层绕行）：                  *)
(*   令 i := 1/κ > 1，c := i − 1 > 0。Bernoulli 不等式             *)
(*   i^N ≥ 1 + (N#1)·c 给出幂下界；预算实数 y := (a/eps)/c 经      *)
(*   real_arch（Real 层 Archimedean，217 根内已证）解出 N，        *)
(*   再经倒数反变（real_inv_pos_lt_contra）与 pow·inv 恒等式        *)
(*   回接 a·κ^N < eps。N 的显式形态：real_arch 给出的 nat。        *)
(*                                                              *)
(* 件 1：预算条件充分性（log 闭式条件）                            *)
(*   r_pow_log_form      log(κ^N) == (N#1)·log κ（归纳）           *)
(*   log_kappa_neg       0<κ<1 ⟹ −log κ > 0（hlogz_strict 证明）   *)
(*   budget_cond_sufficient  N·|log κ| > log a − log eps ⟹ a·κ^N<eps *)
(*   （经 cauchy_real_exp_mono 严格单调 + cw_log_exp_right 反演回接）*)
(*                                                              *)
(* 件 3：论文 4 定理 4.10 尾界形态（纯序代数）                      *)
(*   real_pow_anti_mono  p ≤ q ⟹ κ^q ≤ κ^p                        *)
(*   geo_tail_budget     N ≤ min m n ∧ a·κ^N < eps ⟹ a·κ^{min} < eps *)
(*   budget_min_tail     预算 N 的存在性 + min 尾界组合              *)
(*                                                              *)
(* 纪律：纯构造性（禁词零出现，见技术报告 G1）；                    *)
(*       Set 层语句（real_lt/real_le/real_eq/sigT/And）；           *)
(*       全部 Qed 闭合；依存根内已证机器不重证。                    *)
(* ============================================================ *)


Local Open Scope Q_scope.

(* ============ 0. 具体实数层幂（Real 层 r_pow） ============ *)

Fixpoint real_pow (x : Real) (n : nat) : Real :=
  match n with
  | O => real_one
  | Datatypes.S m => real_mult x (real_pow x m)
  end.

(* 与原始任务表述同名接口：r_pow kappa N 即 real_pow kappa N *)
Notation r_pow := real_pow (only parsing).

(* 幂对 real_eq 的相容性 *)
Lemma real_pow_eq_compat : forall (x y : Real) (n : nat),
  real_eq x y -> real_eq (real_pow x n) (real_pow y n).
Proof.
  intros x y n Hxy. induction n as [| m IH].
  - apply real_eq_refl.
  - cbn [real_pow].
    apply (RealSetoid.real_eq_mult_compat x (real_pow x m) y (real_pow y m)).
    + exact Hxy.
    + exact IH.
Qed.

(* 幂正性：0 < x ⟹ 0 < x^n *)
Lemma cwe_real_pow_pos : forall (x : Real) (n : nat),
  real_lt real_zero x -> real_lt real_zero (real_pow x n).
Proof.
  intros x n Hx. induction n as [| m IH].
  - exact real_lt_zero_one.
  - cbn [real_pow]. exact (real_mult_pos_compat x (real_pow x m) Hx IH).
Qed.

(* ============ 1. 基本代数小工具（217 根内缺位的补齐） ============ *)

(* 0#1 == 0（nat 嵌入零点） *)
Lemma real_const_zero_thm : real_eq (real_const (Z.of_nat 0 # 1)) real_zero.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  change (projT1 (real_const (Z.of_nat 0 # 1)) n) with 0%Q.
  change (projT1 real_zero n) with 0%Q.
  ring.
Qed.

(* 1·x == x（根内 real_mult_one 是 x·1 形态） *)
Lemma real_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans _ (real_mult x real_one)).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

(* 0·x == 0（根内 real_mult_zero 是 x·0 形态） *)
Lemma real_mult_zero_l : forall x : Real, real_eq (real_mult real_zero x) real_zero.
Proof.
  intro x.
  apply (real_eq_trans _ (real_mult x real_zero)).
  - apply real_mult_comm.
  - apply real_mult_zero.
Qed.

(* nat 嵌入乘法后继：(S n)#1·x == (n#1)·x + x *)
Lemma real_nat_mult_succ : forall (n : nat) (x : Real),
  real_eq (real_mult (real_const (Z.of_nat (Datatypes.S n) # 1)) x)
          (real_plus (real_mult (real_const (Z.of_nat n # 1)) x) x).
Proof.
  intros n x.
  apply (real_eq_trans _ (real_mult (real_plus (real_const (Z.of_nat n # 1)) real_one) x)).
  - apply (RealSetoid.real_eq_mult_compat (real_const (Z.of_nat (Datatypes.S n) # 1)) x
                                          (real_plus (real_const (Z.of_nat n # 1)) real_one) x).
    + apply b4_lift_succ.
    + apply real_eq_refl.
  - apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat n # 1)) x)
                                      (real_mult real_one x))).
    + apply (real_eq_sym _ _ (real_distrib_r_local (real_const (Z.of_nat n # 1)) real_one x)).
    + apply (RealSetoid.real_eq_plus_compat (real_mult (real_const (Z.of_nat n # 1)) x)
                                            (real_mult real_one x)
                                            (real_mult (real_const (Z.of_nat n # 1)) x) x).
      * apply real_eq_refl.
      * apply real_mult_one_l.
Qed.

(* 倒数唯一性补充：inv 1 == 1（根内 real_inv_one_local 已有，直接依存） *)
(* （此处不重证；见 real_inv_one_local） *)

(* 倒数正性专用：1 < 1/κ 的桥（real_inv_pos_lt_contra + inv 1 == 1） *)

(* ============ 2. 幂·倒数恒等式（κ^N · (1/κ)^N == 1） ============ *)

Lemma real_pow_inv_pair : forall (k : Real) (Hk : real_lt real_zero k) (n : nat),
  real_eq (real_mult (real_pow k n) (real_pow (real_inv_pos k Hk) n)) real_one.
Proof.
  intros k Hk n. induction n as [| m IH].
  - cbn [real_pow]. apply real_mult_one.
  - cbn [real_pow].
    (* (k·k^m)·(i·i^m) == 1，i := 1/κ *)
    apply (real_eq_trans _ (real_mult (real_mult (real_pow k m) k)
                                      (real_mult (real_inv_pos k Hk)
                                                 (real_pow (real_inv_pos k Hk) m)))).
    + apply (RealSetoid.real_eq_mult_compat
               (real_mult k (real_pow k m))
               (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m))
               (real_mult (real_pow k m) k)
               (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m))).
      * apply real_mult_comm.
      * apply real_eq_refl.
    + apply (real_eq_trans _ (real_mult (real_pow k m)
                                        (real_mult k (real_mult (real_inv_pos k Hk)
                                                                (real_pow (real_inv_pos k Hk) m))))).
      * apply (real_eq_sym _ _ (real_mult_assoc (real_pow k m) k
                         (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m)))).
      * apply (real_eq_trans _ (real_mult (real_pow k m)
                                          (real_mult (real_mult k (real_inv_pos k Hk))
                                                     (real_pow (real_inv_pos k Hk) m)))).
        -- apply (RealSetoid.real_eq_mult_compat (real_pow k m)
                   (real_mult k (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m)))
                   (real_pow k m)
                   (real_mult (real_mult k (real_inv_pos k Hk)) (real_pow (real_inv_pos k Hk) m))).
           ++ apply real_eq_refl.
           ++ apply (real_mult_assoc k (real_inv_pos k Hk)
                                        (real_pow (real_inv_pos k Hk) m)).
        -- apply (real_eq_trans _ (real_mult (real_pow k m)
                                             (real_mult real_one (real_pow (real_inv_pos k Hk) m)))).
           ++ apply (RealSetoid.real_eq_mult_compat (real_pow k m)
                      (real_mult (real_mult k (real_inv_pos k Hk)) (real_pow (real_inv_pos k Hk) m))
                      (real_pow k m)
                      (real_mult real_one (real_pow (real_inv_pos k Hk) m))).
              ** apply real_eq_refl.
              ** apply (RealSetoid.real_eq_mult_compat (real_mult k (real_inv_pos k Hk))
                          (real_pow (real_inv_pos k Hk) m) real_one (real_pow (real_inv_pos k Hk) m)).
                 --- exact (real_inv_pos_correct k Hk).
                 --- apply real_eq_refl.
           ++ apply (real_eq_trans _ (real_mult (real_pow k m)
                                                (real_pow (real_inv_pos k Hk) m))).
              ** apply (RealSetoid.real_eq_mult_compat (real_pow k m)
                          (real_mult real_one (real_pow (real_inv_pos k Hk) m))
                          (real_pow k m) (real_pow (real_inv_pos k Hk) m)).
                 --- apply real_eq_refl.
                 --- apply real_mult_one_l.
              ** exact IH.
Qed.

(* ============ 3. le/lt 辅助（1 ≤ 1+x、0 ≤ (n#1)·x、y < 1+y） ============ *)

Lemma cwe_real_le_one_plus : forall x : Real,
  real_le real_zero x -> real_le real_one (real_plus real_one x).
Proof.
  intros x Hx.
  apply (real_le_trans _ (real_plus real_one real_zero)).
  - apply real_eq_le_bridge.
    apply (real_eq_sym _ _ (real_plus_zero real_one)).
  - exact (real_le_plus_compat real_one real_one real_zero x (real_le_refl real_one) Hx).
Qed.

Lemma real_lt_plus_one : forall y : Real, real_lt y (real_plus real_one y).
Proof.
  intro y.
  apply (real_eq_lt_lt y (real_plus real_zero y) (real_plus real_one y)).
  - exact (real_eq_sym (real_plus real_zero y) y (sf_real_plus_zero_l y)).
  - exact (real_lt_plus_compat_lt_le real_zero real_one y y real_lt_zero_one (real_le_refl y)).
Qed.

(* (n#1)·x 非负：0 < x ⟹ 0 ≤ (n#1)·x（nat 嵌入倍数非负） *)
Lemma real_nat_mult_nonneg : forall (n : nat) (x : Real),
  real_lt real_zero x -> real_le real_zero (real_mult (real_const (Z.of_nat n # 1)) x).
Proof.
  intros n x Hx. induction n as [| m IH].
  - apply real_eq_le_bridge.
    apply (real_eq_trans _ (real_mult real_zero x)).
    + apply (real_eq_sym _ _ (real_mult_zero_l x)).
    + apply (RealSetoid.real_eq_mult_compat real_zero x (real_const (Z.of_nat 0 # 1)) x).
      * apply (real_eq_sym _ _ real_const_zero_thm).
      * apply real_eq_refl.
  - apply real_lt_le_bridge.
    apply (real_lt_eq_lt _ (real_plus (real_mult (real_const (Z.of_nat m # 1)) x) x)).
    + apply (real_lt_eq_lt _ (real_plus x (real_mult (real_const (Z.of_nat m # 1)) x))).
      * apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)).
        -- exact (real_eq_sym _ _ (real_plus_zero real_zero)).
        -- exact (real_lt_plus_compat_lt_le real_zero x real_zero
                    (real_mult (real_const (Z.of_nat m # 1)) x) Hx IH).
      * apply real_plus_comm.
    + apply (real_eq_sym _ _ (real_nat_mult_succ m x)).
Qed.

(* ============ 4. Bernoulli 幂下界：(1+c)^n ≥ 1 + (n#1)·c（c > 0） ============ *)

Lemma bernoulli_pow : forall (c : Real) (Hc : real_lt real_zero c) (n : nat),
  real_le (real_plus real_one (real_mult (real_const (Z.of_nat n # 1)) c))
          (real_pow (real_plus real_one c) n).
Proof.
  intros c Hc n. induction n as [| m IH].
  - cbn [real_pow].
    apply (real_le_trans _ real_one).
    + apply real_eq_le_bridge.
      apply (real_eq_trans _ (real_plus real_one real_zero)).
      * apply (RealSetoid.real_eq_plus_compat real_one
                 (real_mult (real_const (Z.of_nat 0 # 1)) c) real_one real_zero).
        -- apply real_eq_refl.
        -- apply (real_eq_trans _ (real_mult real_zero c)).
           ++ apply (RealSetoid.real_eq_mult_compat (real_const (Z.of_nat 0 # 1)) c
                       real_zero c).
              ** exact real_const_zero_thm.
              ** apply real_eq_refl.
           ++ apply (real_mult_zero_l c).
      * exact (real_plus_zero real_one).
    + apply real_le_refl.
  - cbn [real_pow].
    apply (real_le_trans _ (real_plus (real_plus real_one (real_mult (real_const (Z.of_nat m # 1)) c)) c)).
    + (* 1 + (S m)#1·c == (1 + m#1·c) + c *)
      apply real_eq_le_bridge.
      apply (real_eq_trans _ (real_plus real_one (real_plus (real_mult (real_const (Z.of_nat m # 1)) c) c))).
      * apply (RealSetoid.real_eq_plus_compat real_one
                 (real_mult (real_const (Z.of_nat (Datatypes.S m) # 1)) c)
                 real_one
                 (real_plus (real_mult (real_const (Z.of_nat m # 1)) c) c)).
        -- apply real_eq_refl.
        -- apply (real_nat_mult_succ m c).
      * apply real_plus_assoc.
    + (* (1 + m#1·c) + c ≤ (1+c)·(1+c)^m *)
      apply (real_le_trans _ (real_plus (real_pow (real_plus real_one c) m)
                                        (real_mult c (real_pow (real_plus real_one c) m)))).
      * assert (Hx0 : real_le real_zero (real_mult (real_const (Z.of_nat m # 1)) c))
          by exact (real_nat_mult_nonneg m c Hc).
        assert (H1P : real_le real_one (real_pow (real_plus real_one c) m)).
        { apply (real_le_trans _ (real_plus real_one (real_mult (real_const (Z.of_nat m # 1)) c))).
          - exact (cwe_real_le_one_plus _ Hx0).
          - exact IH. }
        apply (real_le_plus_compat _ _ _ _ IH).
        (* c ≤ c·(1+c)^m *)
        apply (real_le_trans _ (real_mult c real_one)).
        -- apply real_eq_le_bridge.
           apply (real_eq_sym _ _ (real_mult_one c)).
        -- apply (real_le_trans _ (real_mult real_one c)).
           ++ apply real_eq_le_bridge.
              exact (real_mult_comm c real_one).
           ++ apply (real_le_trans _ (real_mult (real_pow (real_plus real_one c) m) c)).
              ** exact (real_le_mult_compat real_one (real_pow (real_plus real_one c) m) c Hc H1P).
              ** apply real_eq_le_bridge.
                 exact (real_mult_comm (real_pow (real_plus real_one c) m) c).
      * (* P + c·P == (1+c)·P *)
        apply real_eq_le_bridge.
        apply (real_eq_trans _ (real_plus (real_mult real_one (real_pow (real_plus real_one c) m))
                                          (real_mult c (real_pow (real_plus real_one c) m)))).
        -- apply (RealSetoid.real_eq_plus_compat (real_pow (real_plus real_one c) m)
                    (real_mult c (real_pow (real_plus real_one c) m))
                    (real_mult real_one (real_pow (real_plus real_one c) m))
                    (real_mult c (real_pow (real_plus real_one c) m))).
           ++ apply (real_eq_sym _ _ (real_mult_one_l (real_pow (real_plus real_one c) m))).
           ++ apply real_eq_refl.
        -- exact (real_distrib_r_local real_one c (real_pow (real_plus real_one c) m)).
Qed.


(* ============ 5. 件 2 主定理：几何击穿的 Real 层显式 nat 预算 ============ *)
(*   N 的显式形态：real_arch 在预算实数 y := (a/eps)/(1/κ − 1) 上解出的 nat。 *)

Theorem r_arch_pow_real :
  forall (kappa : Real) (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (a : Real) (Ha : real_lt real_zero a) (eps : Real) (Heps : real_lt real_zero eps),
  sigT (fun N : nat => real_lt (real_mult a (r_pow kappa N)) eps).
Proof.
  intros kappa Hk1 Hk2 a Ha eps Heps.
  assert (Hinvpos : real_lt real_zero (real_inv_pos kappa Hk1))
    by exact (real_inv_pos_pos kappa Hk1).
  assert (HoneLtInv : real_lt real_one (real_inv_pos kappa Hk1)).
  { apply (real_eq_lt_lt real_one (real_inv_pos real_one real_lt_zero_one)
                         (real_inv_pos kappa Hk1)).
    - apply (real_eq_sym _ _ real_inv_one_local).
    - exact (real_inv_pos_lt_contra kappa real_one Hk1 real_lt_zero_one Hk2). }
  assert (Hc : real_lt real_zero (real_plus (real_inv_pos kappa Hk1) (real_opp real_one)))
    by exact (real_lt_opp_plus real_one (real_inv_pos kappa Hk1) HoneLtInv).
  assert (Hax : real_lt real_zero (real_mult a (real_inv_pos eps Heps)))
    by exact (real_mult_pos_compat a (real_inv_pos eps Heps) Ha (real_inv_pos_pos eps Heps)).
  set (c := real_plus (real_inv_pos kappa Hk1) (real_opp real_one)) in Hc |- *.
  set (x := real_mult a (real_inv_pos eps Heps)) in Hax |- *.
  assert (Hyc : real_lt real_zero (real_mult x (real_inv_pos c Hc)))
    by exact (real_mult_pos_compat x (real_inv_pos c Hc) Hax (real_inv_pos_pos c Hc)).
  destruct (real_arch (real_mult x (real_inv_pos c Hc))) as [N [HN2 HN]].
  (* x < (N#1)·c：(x·(1/c))·c == x（real_mult_div 的换形），再乘 c 保序 *)
  assert (Hxc_lt : real_lt x (real_mult (real_const (Z.of_nat N # 1)) c)).
  { apply (real_eq_lt_lt x (real_mult (real_mult x (real_inv_pos c Hc)) c)).
    - apply (real_eq_trans _ (real_mult c (real_mult x (real_inv_pos c Hc)))).
      + apply (real_eq_sym _ _ (real_mult_div c x Hc)).
      + apply real_mult_comm.
    - exact (real_mult_lt_compat (real_mult x (real_inv_pos c Hc))
               (real_const (Z.of_nat N # 1)) c HN Hc). }
  (* 1 + c == 1/κ *)
  assert (Honec : real_eq (real_plus real_one c) (real_inv_pos kappa Hk1)).
  { unfold c. apply (real_eq_trans _ (real_plus (real_plus real_one (real_inv_pos kappa Hk1))
                                                (real_opp real_one))).
    - apply real_plus_assoc.
    - apply (real_eq_trans _ (real_plus (real_plus (real_inv_pos kappa Hk1) real_one)
                                        (real_opp real_one))).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_plus real_one (real_inv_pos kappa Hk1)) (real_opp real_one)
                 (real_plus (real_inv_pos kappa Hk1) real_one) (real_opp real_one)).
        * apply real_plus_comm.
        * apply real_eq_refl.
      + apply (real_eq_trans _ (real_plus (real_inv_pos kappa Hk1)
                                          (real_plus real_one (real_opp real_one)))).
        * apply (real_eq_sym _ _ (real_plus_assoc (real_inv_pos kappa Hk1) real_one
                                                    (real_opp real_one))).
        * apply (real_eq_trans _ (real_plus (real_inv_pos kappa Hk1) real_zero)).
          -- apply (RealSetoid.real_eq_plus_compat (real_inv_pos kappa Hk1)
                      (real_plus real_one (real_opp real_one))
                      (real_inv_pos kappa Hk1) real_zero).
             ++ apply real_eq_refl.
             ++ apply real_plus_opp.
          -- apply (real_plus_zero (real_inv_pos kappa Hk1)). }
  (* x < 1 + (N#1)·c ≤ (1+c)^N == (1/κ)^N（Bernoulli le + 前段 strict） *)
  assert (Hkey : real_lt x (real_pow (real_inv_pos kappa Hk1) N)).
  { apply (real_lt_eq_lt _ (real_pow (real_plus real_one c) N)).
    - apply (real_lt_le_trans _ (real_plus real_one (real_mult (real_const (Z.of_nat N # 1)) c))).
      + apply (real_lt_trans _ (real_mult (real_const (Z.of_nat N # 1)) c)).
        * exact Hxc_lt.
        * exact (real_lt_plus_one _).
      + exact (bernoulli_pow c Hc N).
    - apply (real_pow_eq_compat _ _ N Honec). }
  (* κ^N == 1/(1/κ)^N（pow·inv 恒等式 + 倒数唯一） *)
  assert (HposN : real_lt real_zero (real_pow (real_inv_pos kappa Hk1) N))
    by exact (cwe_real_pow_pos _ N Hinvpos).
  assert (Hpowinv : real_eq (real_pow kappa N)
                            (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)).
  { apply (real_inv_unique (real_pow (real_inv_pos kappa Hk1) N) (real_pow kappa N)
                           (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)).
    - apply (real_eq_trans _ (real_mult (real_pow kappa N)
                                        (real_pow (real_inv_pos kappa Hk1) N))).
      + apply real_mult_comm.
      + exact (real_pow_inv_pair kappa Hk1 N).
    - exact (real_inv_pos_correct (real_pow (real_inv_pos kappa Hk1) N) HposN). }
  (* 1/x == eps·(1/a)（real_inv_unique 于 x·(eps·(1/a)) == 1） *)
  assert (Hinva : real_eq (real_inv_pos x Hax) (real_mult eps (real_inv_pos a Ha))).
  { apply (real_inv_unique x (real_inv_pos x Hax) (real_mult eps (real_inv_pos a Ha))).
    - exact (real_inv_pos_correct x Hax).
    - apply (real_eq_trans _ (real_mult a
                 (real_mult (real_inv_pos eps Heps) (real_mult eps (real_inv_pos a Ha))))).
      + apply (real_eq_sym _ _ (real_mult_assoc a (real_inv_pos eps Heps)
                                  (real_mult eps (real_inv_pos a Ha)))).
      + apply (real_eq_trans _ (real_mult a
                 (real_mult (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha)))).
        * apply (RealSetoid.real_eq_mult_compat a
                    (real_mult (real_inv_pos eps Heps) (real_mult eps (real_inv_pos a Ha)))
                    a
                    (real_mult (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha))).
          -- apply real_eq_refl.
          -- apply (real_mult_assoc (real_inv_pos eps Heps) eps
                                                       (real_inv_pos a Ha)).
        * apply (real_eq_trans _ (real_mult a (real_mult real_one (real_inv_pos a Ha)))).
          -- apply (RealSetoid.real_eq_mult_compat a
                      (real_mult (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha))
                      a
                      (real_mult real_one (real_inv_pos a Ha))).
             ++ apply real_eq_refl.
             ++ apply (RealSetoid.real_eq_mult_compat
                          (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha)
                          real_one (real_inv_pos a Ha)).
                ** apply (real_eq_trans _ (real_mult eps (real_inv_pos eps Heps))).
                   --- apply real_mult_comm.
                   --- exact (real_inv_pos_correct eps Heps).
                ** apply real_eq_refl.
          -- apply (real_eq_trans _ (real_mult a (real_inv_pos a Ha))).
             ++ apply (RealSetoid.real_eq_mult_compat a
                         (real_mult real_one (real_inv_pos a Ha)) a (real_inv_pos a Ha)).
                ** apply real_eq_refl.
                ** apply real_mult_one_l.
             ++ exact (real_inv_pos_correct a Ha). }
  assert (Hinvlt : real_lt (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)
                           (real_inv_pos x Hax)).
  { exact (real_inv_pos_lt_contra x (real_pow (real_inv_pos kappa Hk1) N) Hax HposN Hkey). }
  (* κ^N < eps·(1/a) *)
  assert (Hklt : real_lt (real_pow kappa N) (real_mult eps (real_inv_pos a Ha))).
  { apply (real_eq_lt_lt _ (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)).
    - exact Hpowinv.
    - exact (real_lt_eq_lt _ _ _ Hinvlt Hinva). }
  exists N.
  apply (real_lt_eq_lt (real_mult a (real_pow kappa N))
                       (real_mult a (real_mult eps (real_inv_pos a Ha)))).
  - exact (real_mult_lt_compat_l (real_pow kappa N)
             (real_mult eps (real_inv_pos a Ha)) a Hklt Ha).
  - exact (real_mult_div a eps Ha).
Qed.

(* ============ 6. 件 1：log 形态闭式条件（Real 层） ============ *)

(* −log κ > 0：0 < κ < 1 ⟹ log κ < 0（G01_CoreMicro.hlogz_strict 证明）⟹ opp 反变 *)
Lemma log_kappa_neg : forall (kappa : Real)
                         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one),
  real_lt real_zero (real_opp (real_log kappa Hk1)).
Proof.
  intros kappa Hk1 Hk2.
  assert (Hneg : real_lt (real_log kappa Hk1) real_zero)
    by exact (hlogz_strict kappa Hk1 Hk2).
  apply (real_eq_lt_lt real_zero (real_opp real_zero) (real_opp (real_log kappa Hk1))).
  - apply (real_eq_sym _ _ real_opp_zero).
  - exact (real_opp_lt_compat (real_log kappa Hk1) real_zero Hneg).
Qed.

(* log 幂恒等式：log(κ^N) == (N#1)·log κ（real_log_mult 归纳） *)
Lemma real_pow_log_form : forall (k : Real) (Hk : real_lt real_zero k) (n : nat),
  real_eq (real_log (real_pow k n) (cwe_real_pow_pos k n Hk))
          (real_mult (real_const (Z.of_nat n # 1)) (real_log k Hk)).
Proof.
  intros k Hk n. induction n as [| m IH].
  - apply (real_eq_trans _ real_zero).
    + apply real_log_one.
    + exact (real_eq_sym (real_mult (real_const (Z.of_nat 0 # 1)) (real_log k Hk)) real_zero
               (real_eq_trans (real_mult (real_const (Z.of_nat 0 # 1)) (real_log k Hk))
                              (real_mult real_zero (real_log k Hk)) real_zero
                              (RealSetoid.real_eq_mult_compat
                                 (real_const (Z.of_nat 0 # 1)) (real_log k Hk)
                                 real_zero (real_log k Hk)
                                 real_const_zero_thm (real_eq_refl (real_log k Hk)))
                              (real_mult_zero_l (real_log k Hk)))).
  - cbn [real_pow].
    apply (real_eq_trans _ (real_plus (real_log k Hk)
                                      (real_log (real_pow k m) (cwe_real_pow_pos k m Hk)))).
    + exact (log_inv_mult_thm k (real_pow k m) Hk (cwe_real_pow_pos k m Hk)
               (cwe_real_pow_pos k (Datatypes.S m) Hk)).
    + apply (real_eq_trans _ (real_plus (real_log k Hk)
                   (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk)))).
      * apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _) IH).
      * apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat m # 1))
                                                        (real_log k Hk))
                                            (real_log k Hk))).
        -- apply (real_plus_comm (real_log k Hk)
                    (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk))).
        -- apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat m # 1))
                                                        (real_log k Hk))
                                             (real_log k Hk))).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk))
                       (real_log k Hk)
                       (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk))
                       (real_log k Hk)).
              ** apply real_eq_refl.
              ** apply real_eq_refl.
           ++ apply (real_eq_sym _ _ (real_nat_mult_succ m (real_log k Hk))).
Qed.

(* 件 1 主件：预算条件充分性
   N·|log κ| > log a − log eps ⟹ a·κ^N < eps
   （经 log 多项式恒等 + cauchy_real_exp_mono 严格单调 + cw_log_exp_right 反演） *)
Theorem budget_cond_sufficient :
  forall (kappa a eps : Real)
         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps) (N : nat),
  real_lt (real_plus (real_log a Ha) (real_opp (real_log eps Heps)))
          (real_mult (real_const (Z.of_nat N # 1)) (real_opp (real_log kappa Hk1))) ->
  real_lt (real_mult a (real_pow kappa N)) eps.
Proof.
  intros kappa a eps Hk1 Hk2 Ha Heps N Hcond.

  (* log(a·κ^N) == log a + N#1·logκ *)
  assert (Hlogpow : real_eq (real_log (real_mult a (real_pow kappa N))
                                      (real_mult_positive a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1)))
                            (real_plus (real_log a Ha)
                                       (real_mult (real_const (Z.of_nat N # 1))
                                                  (real_log kappa Hk1)))).
  { apply (real_eq_trans _ (real_plus (real_log a Ha)
                                      (real_log (real_pow kappa N) (cwe_real_pow_pos kappa N Hk1)))).
    - exact (real_log_mult a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1)).
    - apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _)
               (real_pow_log_form kappa Hk1 N)). }
  (* N#1·logκ == −(N#1·(−logκ)) *)
  assert (Hnegm : real_eq (real_mult (real_const (Z.of_nat N # 1)) (real_log kappa Hk1))
                          (real_opp (real_mult (real_const (Z.of_nat N # 1))
                                               (real_opp (real_log kappa Hk1))))).
  { apply (real_eq_trans _ (real_mult (real_const (Z.of_nat N # 1))
                                      (real_opp (real_opp (real_log kappa Hk1))))).
    - apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)
               (real_eq_sym _ _ (real_opp_opp (real_log kappa Hk1)))).
    - apply real_mult_opp_l. }
  (* 条件换形：log a < N#1·(−logκ) + log eps
     （Hcond 两侧加 log eps：La + −Le < W ⟹ (La + −Le) + Le < W + Le） *)
  assert (Hmid : real_lt (real_log a Ha)
                         (real_plus (real_mult (real_const (Z.of_nat N # 1))
                                               (real_opp (real_log kappa Hk1)))
                                    (real_log eps Heps))).
  { apply (real_eq_lt_lt (real_log a Ha)
            (real_plus (real_plus (real_log a Ha) (real_opp (real_log eps Heps)))
                       (real_log eps Heps))).
    - apply (real_eq_trans _ (real_plus (real_log a Ha)
                   (real_plus (real_opp (real_log eps Heps)) (real_log eps Heps)))).
      + apply (real_eq_sym _ _).
        apply (real_eq_trans _ (real_plus (real_log a Ha) real_zero)).
        * apply (RealSetoid.real_eq_plus_compat (real_log a Ha)
                   (real_plus (real_opp (real_log eps Heps)) (real_log eps Heps))
                   (real_log a Ha) real_zero).
          -- apply real_eq_refl.
          -- exact (real_eq_trans _ _ _
                     (real_plus_comm (real_opp (real_log eps Heps)) (real_log eps Heps))
                     (real_plus_opp (real_log eps Heps))).
        * apply (real_plus_zero (real_log a Ha)).
      + apply (real_plus_assoc (real_log a Ha) (real_opp (real_log eps Heps))
                                 (real_log eps Heps)).
    - exact (real_lt_plus_compat_lt_le _ _ _ _ Hcond (real_le_refl (real_log eps Heps))). }
  (* 加法消去：x == La − W、La < W + Le ⟹ x < Le（件 1 专用纯加法引理） *)
  assert (Hshift : forall (x La Le W : Real),
            real_eq x (real_plus La (real_opp W)) ->
            real_lt La (real_plus W Le) ->
            real_lt x Le).
  { intros x0 La0 Le0 W0 H1 H2.
    apply (real_eq_lt_lt x0 (real_plus La0 (real_opp W0))).
    - exact H1.
    - apply (real_lt_eq_lt _ (real_plus (real_plus W0 Le0) (real_opp W0))).
      + exact (real_lt_plus_compat_lt_le _ _ _ _ H2 (real_le_refl _)).
      + exact (real_eq_trans
                 (real_plus (real_plus W0 Le0) (real_opp W0))
                 (real_plus W0 (real_plus Le0 (real_opp W0)))
                 Le0
                 (real_eq_sym _ _ (real_plus_assoc W0 Le0 (real_opp W0)))
                 (real_eq_trans
                    (real_plus W0 (real_plus Le0 (real_opp W0)))
                    (real_plus (real_plus W0 (real_opp W0)) Le0)
                    Le0
                    (real_eq_trans
                       (real_plus W0 (real_plus Le0 (real_opp W0)))
                       (real_plus W0 (real_plus (real_opp W0) Le0))
                       (real_plus (real_plus W0 (real_opp W0)) Le0)
                       (RealSetoid.real_eq_plus_compat W0 (real_plus Le0 (real_opp W0)) W0
                          (real_plus (real_opp W0) Le0)
                          (real_eq_refl W0)
                          (real_plus_comm Le0 (real_opp W0)))
                       (real_plus_assoc W0 (real_opp W0) Le0))
                    (real_eq_trans
                       (real_plus (real_plus W0 (real_opp W0)) Le0)
                       (real_plus real_zero Le0)
                       Le0
                       (RealSetoid.real_eq_plus_compat (real_plus W0 (real_opp W0)) Le0
                          real_zero Le0
                          (real_plus_opp W0)
                          (real_eq_refl Le0))
                       (sf_real_plus_zero_l Le0)))). }
  (* 组装：log(a·κ^N) == La + −(N#1·(−logκ))、La < W + Le ⟹ log(a·κ^N) < Le *)
  assert (Hlt : real_lt (real_log (real_mult a (real_pow kappa N))
                                  (real_mult_positive a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1)))
                        (real_log eps Heps)).
  { apply (Hshift _ (real_log a Ha) (real_log eps Heps)
             (real_mult (real_const (Z.of_nat N # 1)) (real_opp (real_log kappa Hk1)))).
    - apply (real_eq_trans _ (real_plus (real_log a Ha)
                   (real_mult (real_const (Z.of_nat N # 1)) (real_log kappa Hk1)))).
      + exact Hlogpow.
      + apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _) Hnegm).
    - exact Hmid. }
  (* exp 严格单调 + e^{log y} == y 反演闭合 *)
  apply (real_eq_lt_lt (real_mult a (real_pow kappa N))
           (cauchy_real_exp (real_log (real_mult a (real_pow kappa N))
              (real_mult_positive a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1))))
           eps).
  - apply (real_eq_sym _ _ (cw_log_exp_right (real_mult a (real_pow kappa N))
              (real_mult_positive a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1)))).
  - apply (real_lt_eq_lt _ (cauchy_real_exp (real_log eps Heps))).
    + exact (cauchy_real_exp_mono _ _ Hlt).
    + exact (cw_log_exp_right eps Heps).
Qed.

(* ============ 7. 件 3：论文 4 定理 4.10 尾界形态（纯序代数） ============ *)

(* 幂加法：κ^(p+j) == κ^p · κ^j *)
Lemma real_pow_add_thm : forall (k : Real) (p j : nat),
  real_eq (real_pow k (p + j)%nat) (real_mult (real_pow k p) (real_pow k j)).
Proof.
  intros k p j. induction p as [| p IH].
  - change (real_pow k (0 + j)%nat) with (real_pow k j).
    change (real_pow k 0) with real_one.
    apply (real_eq_sym _ _ (real_mult_one_l (real_pow k j))).
  - replace (Datatypes.S p + j)%nat with (Datatypes.S (p + j))%nat by lia.
    change (real_pow k (Datatypes.S (p + j))) with
           (real_mult k (real_pow k (p + j))).
    apply (real_eq_trans _ (real_mult k (real_mult (real_pow k p) (real_pow k j)))).
    + apply (RealSetoid.real_eq_mult_compat k (real_pow k (p + j)%nat) k
               (real_mult (real_pow k p) (real_pow k j))).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_eq_trans _ (real_mult (real_mult k (real_pow k p)) (real_pow k j))).
      * exact (real_mult_assoc k (real_pow k p) (real_pow k j)).
      * apply real_eq_refl.
Qed.

(* κ ≤ 1 ⟹ κ^j ≤ 1 *)
Lemma real_pow_le_one : forall (k : Real) (Hk1 : real_lt real_zero k)
                          (Hk2 : real_le k real_one) (j : nat),
  real_le (real_pow k j) real_one.
Proof.
  intros k Hk1 Hk2 j. induction j as [| j IH].
  - apply real_le_refl.
  - cbn [real_pow].
    apply (real_le_trans _ (real_mult k real_one)).
    + apply (real_le_trans _ (real_mult (real_pow k j) k)).
      * apply real_eq_le_bridge. exact (real_mult_comm k (real_pow k j)).
      * apply (real_le_trans _ (real_mult real_one k)).
        -- exact (real_le_mult_compat (real_pow k j) real_one k Hk1 IH).
        -- apply real_eq_le_bridge.
           apply (real_eq_trans _ k).
           ++ exact (real_mult_one_l k).
           ++ apply (real_eq_sym _ _ (real_mult_one k)).
      + apply (real_le_trans _ k).
        * apply real_eq_le_bridge. exact (real_mult_one k).
        * exact Hk2.
Qed.

(* 幂反单调：0 < κ ≤ 1、p ≤ q ⟹ κ^q ≤ κ^p *)
Lemma real_pow_anti_mono : forall (k : Real) (Hk1 : real_lt real_zero k)
                              (Hk2 : real_le k real_one) (p q : nat),
  (p <= q)%nat -> real_le (real_pow k q) (real_pow k p).
Proof.
  intros k Hk1 Hk2 p q Hle.
  assert (Hcore : forall j : nat,
            real_le (real_pow k (p + j)%nat) (real_pow k p)).
  { intros j.
    assert (Heq : real_eq (real_pow k (p + j)%nat)
                          (real_mult (real_pow k p) (real_pow k j)))
      by exact (real_pow_add_thm k p j).
    apply (real_le_trans _ (real_mult (real_pow k p) (real_pow k j))).
    - apply real_eq_le_bridge. exact Heq.
    - apply (real_le_trans _ (real_mult (real_pow k j) (real_pow k p))).
      + apply real_eq_le_bridge. exact (real_mult_comm (real_pow k p) (real_pow k j)).
      + apply (real_le_trans _ (real_mult real_one (real_pow k p))).
        * exact (real_le_mult_compat (real_pow k j) real_one (real_pow k p)
                   (cwe_real_pow_pos k p Hk1) (real_pow_le_one k Hk1 Hk2 j)).
        * apply real_eq_le_bridge. exact (real_mult_one_l (real_pow k p)). }
  assert (Hq : q = (p + (q - p))%nat) by lia.
  rewrite Hq. apply Hcore.
Qed.

(* 预算下降：N ≤ min m n 且 a·κ^N < eps ⟹ a·κ^{min m n} < eps
   （论文 4 定理 4.10 尾界 a·κ^{min m n} 的预算证明，纯序代数） *)
Theorem geo_tail_budget :
  forall (kappa a eps : Real)
         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps) (m n N : nat),
  (N <= Nat.min m n)%nat ->
  real_lt (real_mult a (real_pow kappa N)) eps ->
  real_lt (real_mult a (real_pow kappa (Nat.min m n))) eps.
Proof.
  intros kappa a eps Hk1 Hk2 Ha Heps m n N Hmin Hbudget.
  assert (Hk2le : real_le kappa real_one)
    by exact (real_lt_le_bridge kappa real_one Hk2).
  apply (real_le_lt_trans _ (real_mult a (real_pow kappa N))).
  - apply (real_le_trans _ (real_mult (real_pow kappa (Nat.min m n)) a)).
    + apply real_eq_le_bridge.
      exact (real_mult_comm a (real_pow kappa (Nat.min m n))).
    + apply (real_le_trans _ (real_mult (real_pow kappa N) a)).
      * exact (real_le_mult_compat (real_pow kappa (Nat.min m n))
                  (real_pow kappa N) a Ha
                  (real_pow_anti_mono kappa Hk1 Hk2le N (Nat.min m n) Hmin)).
      * apply real_eq_le_bridge.
        exact (real_mult_comm (real_pow kappa N) a).
  - exact Hbudget.
Qed.

(* 组合形态：给出显式预算 N，min 尾界随之证明（定理 4.10 Real 层组装） *)
Theorem budget_min_tail :
  forall (kappa a eps : Real)
         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps),
  sigT (fun N : nat => forall (p q : nat),
    (N <= Nat.min p q)%nat ->
    real_lt (real_mult a (real_pow kappa (Nat.min p q))) eps).
Proof.
  intros kappa a eps Hk1 Hk2 Ha Heps.
  destruct (r_arch_pow_real kappa Hk1 Hk2 a Ha eps Heps) as [N HN].
  exists N.
  intros p q Hpq.
  exact (geo_tail_budget kappa a eps Hk1 Hk2 Ha Heps p q N Hpq HN).
Qed.

(* ============ 8. 提取检验（可执行 OCaml，G3 关卡） ============ *)
Set Warnings "-extraction-opaque-accessed".
Extraction "upbudgetreal.ml" r_arch_pow_real budget_cond_sufficient geo_tail_budget budget_min_tail.

End BudgetReal.

(* ---------- UpArchAttn ---------- *)
From Stdlib Require Import QArith.QArith.
Import BudgetReal.

(* ============================================================ *)
(* UpArchAttn.v —— 榜 A3：r_arch_pow_attn 的 Real 层副本            *)
(*                                                              *)
(* 扫描件背景（分析-219平凡定理热点扫描.md 榜 A3）：        *)
(*   根文件 CW_ConstructiveWorld_219.v 注意力收敛区 L29247 的接口前提 *)
(*     Variable r_arch_pow_attn :                                *)
(*       forall (a : R), lt zero a -> forall eps : R, lt zero eps -> *)
(*         sigT (fun N : nat =>                                  *)
(*           lt (mult a (r_pow (minus one delta) N)) eps),        *)
(*   是几何击破假设 attention_iterate_converges（L29330）的 N 供给口。 *)
(*   它与收敛区已升级的 r_arch_pow（ConvergenceCauchy L14081）同构，  *)
(*   却从未连接到已验收的 Real 层预算机器 UpBudgetReal.r_arch_pow_real *)
(*   （0<κ<1、0<a、0<eps 时 sigT N, a·κ^N < eps）。本文件消除该断连： *)
(*                                                              *)
(* 件 1（主件）r_arch_pow_attn_real：接口前提在具体 Real 层的实例化。 *)
(*   形态对齐映射（检验结论）：                                    *)
(*     R（抽象，RealInterfaceEnhanced 实例参数）                  *)
(*         ⟿ Real（柯西实数 sigT (u : Qseq) (cauchy u)） *)
(*     lt zero / lt ⟿ real_lt real_zero / real_lt（Type 版）       *)
(*     mult ⟿ real_mult                                          *)
(*     minus one delta ⟿ real_plus real_one (real_opp delta)      *)
(*       （Real 层无减法记号，x−y := x+(−y)，同根 L41051 惯例）      *)
(*     r_pow（根 L14071 Fixpoint：O ↦ one, S m ↦ mult x (pow x m)， *)
(*       左乘形态）⟿ real_pow（UpBudgetReal L46 Fixpoint：          *)
(*       O ↦ real_one, S m ↦ real_mult x (pow x m)——同为左乘形态，   *)
(*       定义同构确认：桥为定义级实例化（根 r_pow 活在抽象 R 世界，   *)
(*       跨世界 real_eq 桥不可类型化；UpBudgetReal 已设 Notation      *)
(*       r_pow := real_pow，接口名与函数在 Real 层合一）。           *)
(*     Section Variable delta/delta_pos/delta_lt_one（闭合后消失）  *)
(*         ⟿ 语句显式前提。                                       *)
(*                                                              *)
(* 件 2（组装预演）attention_iterate_converges_real：              *)
(*   依存件 1 + 根 attention_tv_iter_contraction（L29287）结论的     *)
(*   Real 副本链 tv_n ≤ (1−δ)^n·tv_0（根 r_pow_dec_iter_attn 的     *)
(*   Real 副本即 UpBudgetReal.real_pow_anti_mono，直接复用），       *)
(*   给出 sigT 预算 N 见证定理。覆盖面注记：根定理的语义对象        *)
(*   attention_step/tv_dist/boltzmann_dist_attn 生活在抽象 Section  *)
(*   世界，其实例化需在 Real 层整体证明 detailed_balance/           *)
(*   minorization/sum_swap_cc/abs_ge_zero_id_cc/lt_plus_compat 对等 *)
(*   接口前提（天级工程，不属本小件）；按原始任务表述条款以 Real 序列       *)
(*   tv_seq := n ↦ TV(iterate n μ₀, p_b) 承载最小骨架，每步几何      *)
(*   收缩作为副本前提 Hstep 显式列出。主件 1 不受影响。              *)
(*                                                              *)
(* 纪律：纯构造性；Set 层语句（real_lt/real_le/real_eq/sigT）；      *)
(*       全部 Qed 闭合；只依存根内/UpBudgetReal 已证机器。           *)
(* ============================================================ *)


Local Open Scope Q_scope.

(* ============ 1. 1−δ 的 Real 层序引理（κ := 1−δ 良定前提） ============ *)

(* 根 L14270 one_minus_kappa_pos 的 Real 副本：δ < 1 ⟹ 0 < 1−δ *)
Lemma one_minus_delta_pos_real : forall delta : Real,
  real_lt delta real_one ->
  real_lt real_zero (real_plus real_one (real_opp delta)).
Proof.
  intros delta Hd.
  exact (real_lt_opp_plus delta real_one Hd).
Qed.

(* 根注意力区前提的对称支 Real 副本：0 < δ ⟹ 1−δ < 1
   （逐点差零 + real_lt_eq_lt：1−(1−δ) == δ 逐点 ring） *)
Lemma one_minus_delta_lt_one_real : forall delta : Real,
  real_lt real_zero delta ->
  real_lt (real_plus real_one (real_opp delta)) real_one.
Proof.
  intros delta Hd.
  apply (real_lt_zero_minus (real_plus real_one (real_opp delta)) real_one).
  apply (real_lt_eq_lt real_zero delta).
  - exact Hd.
  - apply real_eq_sym.
    apply real_eq_of_zero_diff.
    intro n.
    rewrite (real_plus_proj real_one
               (real_opp (real_plus real_one (real_opp delta))) n).
    rewrite (real_opp_proj (real_plus real_one (real_opp delta)) n).
    rewrite (real_plus_proj real_one (real_opp delta) n).
    rewrite (real_opp_proj delta n).
    cbn [projT1].
    ring.
Qed.

(* ============ 2. 件 1 主件：接口前提的 Real 层实例化 ============ *)

Theorem r_arch_pow_attn_real :
  forall delta : Real, real_lt real_zero delta -> real_lt delta real_one ->
  forall a : Real, real_lt real_zero a ->
  forall eps : Real, real_lt real_zero eps ->
  sigT (fun N : nat =>
    real_lt (real_mult a
              (real_pow (real_plus real_one (real_opp delta)) N)) eps).
Proof.
  intros delta Hd1 Hd2 a Ha eps Heps.
  exact (r_arch_pow_real (real_plus real_one (real_opp delta))           (one_minus_delta_pos_real delta Hd2)           (one_minus_delta_lt_one_real delta Hd1)           a Ha eps Heps).
Qed.

(* ============ 3. 件 2 组装预演：TV 几何衰减链（Real 副本） ============ *)

(* 根 attention_tv_iter_contraction（L29287）结论的 Real 副本链：
   每步 tv_{n+1} ≤ (1−δ)·tv_n ⟹ tv_n ≤ (1−δ)^n·tv₀。
   （根 r_pow_dec_iter_attn 的幂反单调 Real 副本即
     UpBudgetReal.real_pow_anti_mono，件 2 主定理直接复用，不重证。） *)
Lemma tv_iter_decay_real :
  forall (delta : Real)
         (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
         (tv_seq : nat -> Real),
  (forall n : nat,
    real_le (tv_seq (Datatypes.S n))
            (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  forall n : nat,
    real_le (tv_seq n)
            (real_mult (real_pow (real_plus real_one (real_opp delta)) n)
                       (tv_seq Datatypes.O)).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep n.
  assert (Hk1 : real_lt real_zero (real_plus real_one (real_opp delta)))
    by exact (one_minus_delta_pos_real delta Hd2).
  set (kappa := real_plus real_one (real_opp delta)) in *.
  induction n as [| n IH].
  - (* κ^0 ≡ one：1·tv₀ == tv₀ *)
    apply real_eq_le_bridge.
    apply real_eq_sym.
    exact (real_mult_one_l (tv_seq Datatypes.O)).
  - (* tv_{n+1} ≤ κ·tv_n ≤ κ·(κ^n·tv₀) == κ^{n+1}·tv₀ *)
    apply (real_le_trans _ (real_mult kappa (tv_seq n))).
    + exact (Hstep n).
    + apply (real_le_trans _ (real_mult (tv_seq n) kappa)).
      * apply real_eq_le_bridge.
        exact (real_mult_comm kappa (tv_seq n)).
      * apply (real_le_trans _
                 (real_mult (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                            kappa)).
        -- exact (real_le_mult_compat (tv_seq n)
                    (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                    kappa Hk1 IH).
        -- apply real_eq_le_bridge.
           exact (real_eq_trans
                    (real_mult (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                               kappa)
                    (real_mult kappa
                               (real_mult (real_pow kappa n) (tv_seq Datatypes.O)))
                    (real_mult (real_mult kappa (real_pow kappa n))
                               (tv_seq Datatypes.O))
                    (real_mult_comm (real_mult (real_pow kappa n)
                                        (tv_seq Datatypes.O))
                                    kappa)
                    (real_mult_assoc kappa (real_pow kappa n)
                                     (tv_seq Datatypes.O))).
Qed.

(* ============ 4. 件 2 主定理：迭代收敛的 sigT 显式预算见证 ============ *)

(* 根 attention_iterate_converges（L29330）的 Real 层副本组装：
   预算 N 由件 1（r_arch_pow_attn_real）构造；尾界 n ≥ N 由
   tv 衰减链（本文件件 2 前置）+ 幂反单调（real_pow_anti_mono）
   + 件 1 的 a·κ^N < eps 证明。
   覆盖面注记：tv_seq 即根语义对象 n ↦ TV(iterate attention_step n μ₀,
   boltzmann_dist_attn) 的 Real 承载；每步收缩 Hstep 对应根
   attention_tv_contraction 的结论形态。根抽象 Section 的完整
   Real 层实例化需整体证明 detailed_balance/minorization/
   sum_swap_cc/abs_ge_zero_id_cc/lt_plus_compat 对等接口前提，
   天级工程，不属本小件（主件 1 不受影响）。 *)
Theorem attention_iterate_converges_real :
  forall (delta : Real)
         (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
         (tv_seq : nat -> Real),
  (forall n : nat,
    real_le (tv_seq (Datatypes.S n))
            (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  forall eps : Real, real_lt real_zero eps ->
  real_lt real_zero (tv_seq Datatypes.O) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (tv_seq n) eps).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0.
  destruct (r_arch_pow_attn_real delta Hd1 Hd2
             (tv_seq Datatypes.O) Htv0 eps Heps) as [N HN].
  exists N.
  intros n Hn.
  set (kappa := real_plus real_one (real_opp delta)) in *.
  apply (real_le_lt_trans _
           (real_mult (real_pow kappa n) (tv_seq Datatypes.O))).
  - exact (tv_iter_decay_real delta Hd1 Hd2 tv_seq Hstep n).
  - apply (real_le_lt_trans _
             (real_mult (real_pow kappa N) (tv_seq Datatypes.O))).
    + assert (Hk1 : real_lt real_zero kappa)
        by exact (one_minus_delta_pos_real delta Hd2).
      assert (Hk2le : real_le kappa real_one)
        by exact (real_lt_le_bridge kappa real_one
                    (one_minus_delta_lt_one_real delta Hd1)).
      assert (Hanti : real_le (real_pow kappa n) (real_pow kappa N))
        by exact (real_pow_anti_mono kappa Hk1 Hk2le N n Hn).
      exact (real_le_mult_compat (real_pow kappa n) (real_pow kappa N)
               (tv_seq Datatypes.O) Htv0 Hanti).
    + exact (real_eq_lt_lt (real_mult (real_pow kappa N) (tv_seq Datatypes.O))
               (real_mult (tv_seq Datatypes.O) (real_pow kappa N)) eps
               (real_mult_comm (real_pow kappa N) (tv_seq Datatypes.O)) HN).
Qed.

(* ============ 5. 提取检验（G3：零 Obj.magic） ============ *)

Extraction "uparchattn.ml" r_arch_pow_attn_real attention_iterate_converges_real.

