(* ===================================================================== *)
(*  abl_audit_base_v5b.v —— 审计 v5b·S12 余位矿直审闭合件          *)
(* ===================================================================== *)
(*  使命: CS 审计 v5 报告 §①/§⑦ 登记的 S12 余位矿（配额边界余项）的甲形态   *)
(*        直审闭合。主闭合位＝sf_min_pick_spec（最小作用量选取 spec，cmp     *)
(*        参数化，真内容）；余位＝sf_grad_cost_step_eq、sf_consensus_dist_   *)
(*        zero、消息传递 sf_iterate_mp 块、课程学习块、Wasserstein sf_qw2    *)
(*        块、Q-learning 块。共八载体十六使用点：                           *)
(*        ① abj_minpick_two_stage——最小作用量选取 spec 的两段复合形：        *)
(*          以 r1 段选取结果为种子的 r2 段选取不劣于种子、且对 r1++r2 全部   *)
(*          连通候选不劣（连通面＋种子面＋双段候选面四翼）；sf_min_pick_spec *)
(*          两次真行使，三面（连通/种子/候选）各行使两次；And 拆翼走 v5 件   *)
(*          abe_and_l/abe_and_r 管件（链上真使用）。cmp 沿出口参数面 Set 层  *)
(*          （S01.Or:=A+B）显式量化（LPO 墙族沿 S12 自注，接口层禁硬证，     *)
(*          本件沿参数面使用不实例化）。                                    *)
(*        ② abj_minpick_concrete_nohit——同一 spec 的具体无命中实例：        *)
(*          候选路径首态散列不匹配（0≠1）时选取归约为种子（贪心跳过分支     *)
(*          的计算实拍），三面具体成立；cmp 全程量化未被行使（无命中分支    *)
(*          不调用比较接口，born-green 计算）。                             *)
(*        ③ abj_grad_step_general_and_half——单步精确等式引理                *)
(*          （sf_grad_cost_step_eq）的一般形（QId 等式面真行使）与具体实例   *)
(*          （h=1/2、t=0、x=3 两侧均归约 9/8，Qeq_bool 计算闭合）并载。      *)
(*        ④ abj_consensus_pair_zero_both——共识后两体坐标距离为零主定理      *)
(*          （sf_consensus_dist_zero）的正反双配对使用＋具体智能体实例。     *)
(*        ⑤ abj_mp_iter_split_no_regress——消息传递收缩主定理               *)
(*          （sf_message_passing_contractive）的迭代分裂复合形：n 段迭代后  *)
(*          再 m 段迭代不劣于起点（收缩主定理两次真行使，单步前提槽原样     *)
(*          贯通，沿参数面使用）。                                          *)
(*        ⑥ abj_curriculum_two_stage——课程学习单调主定理（节内三槽出节      *)
(*          显式化）的两段课程复合形：先 s1 后 s2 的累计课程不增损失        *)
(*          （主定理两次真行使，逐段 trans 复合）。                         *)
(*        ⑦ abj_qw2_triple——Wasserstein 块三件使用：配对均方对称（一般形   *)
(*          真行使＋具体实例计算）、同分布配对均方为零（一般形＋具体实例    *)
(*          计算）、配对均方＝逐点差平方和（经 qid_intro 入 Set 层 QId）。   *)
(*        ⑧ abj_qupdate_alpha0_pair——Q 学习块：α=0 表值不变主定理一般形    *)
(*          真行使＋具体表格实例（q=[[5]]，α=0 更新后读数不变，Qeq_bool     *)
(*          计算闭合）。                                                    *)
(*        空壳甄别（响亮申报，沿 CS 判例）：本件八闭合位核验全为真定理，    *)
(*        零新空壳；同件在档两处「结论=True」空壳（kmeans/viterbi，E856      *)
(*        前科族）登记不使用，仅列尾舱直审（公理面闭合为真）。              *)
(*  依赖: S01_BaseRing S02_CauchyComplete S12_B5RecycleSF                   *)
(*        （-Q 预编译树 vo_local_world_unified_0930 只读引用）；             *)
(*        abl_audit_base_v5（池内链编前位件，本件使用其 abe_and_l/r 管件，  *)
(*        并于尾舱对其六载体链上复审）；Stdlib（QArith/List/Arith/Lia/     *)
(*        Extraction 出口舱）。                                             *)
(*  构造性: 零承认语句、零经典逻辑、零 Prop 载体：语句面合取全 S01.And       *)
(*        （:=A*B，Set 层），等同全 S01.Id 与 QId/Id(Qeq_bool 面)（Set 层）， *)
(*        比较全 real_le/real_lt/real_eq/QleT'/QId（Set 型）；无 exists、   *)
(*        无否定形书写；量化前提槽（InT/Id/单步前提）全 Set 型 Pi。证明体   *)
(*        全 exact/apply/cbn/id_refl 显式项直交；Prop 面仅现于上游定理出口  *)
(*        的 Qeq 前提经 qid_intro 入 Set 层的必经桥（v5 判例），非载体语句。 *)
(*  编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&        *)
(*        ulimit -s 65532 && nice -19 rocq c -native-compiler no            *)
(*        -Q <池> "" -Q vo_local_world_unified_0930 ""                       *)
(*        <池>/abl_audit_base_v5.v（链编前位，先行）                         *)
(*        <池>/abl_audit_base_v5b.v（本件，道闸 ≤1，独占池 audit_s12b/）。   *)
(*  核验注: ①八闭合位出口签名以 rocq repl Check 实拍为准——              *)
(*        sf_min_pick_spec 形参序为 cmp start goal rest seed（rest 先于      *)
(*        seed），引擎 sf_min_pick 为 cmp start goal seed rest；             *)
(*        sf_curriculum_monotone 出节显式化为 M/step/loss/节前提四槽；       *)
(*        sf_message_passing_contractive 单步前提为显式 forall 前提槽。      *)
(*        ②abj_ 前缀全树 grep 零命中（防撞核验）。③sf_vec_hash：nil→0、     *)
(*        非空→1；sf_path_connects 首尾散列匹配——无命中具体实例沿此全计算   *)
(*        化。④sf_quad_cost t x=(1/2)(x−t)²、sf_grad_step h t x=x−h(x−t)，  *)
(*        具体翼 h=1/2、t=0、x=3 两侧均归约 9/8（Qeq_bool 交叉相乘判定）。   *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S12_B5RecycleSF.
Require Import abl_audit_base_v5.
From Stdlib Require Import QArith.QArith QArith.Qabs
               Lists.List Arith.Arith.
Import ListNotations.
From Stdlib Require Import Lia.
Local Open Scope Q_scope.

(* ============================================================ *)
(* §0 载体一（主闭合位）·最小作用量选取 spec：两段复合形             *)
(*    （sf_min_pick_spec ×2 真行使：连通/种子/候选三面各行使两次）    *)
(* ============================================================ *)

Theorem abj_minpick_two_stage :
  forall (cmp : forall a b : Real, Or (real_le a b) (real_lt b a))
         (start goal : SFVec) (r1 r2 : list (list SFVec)) (seed : list SFVec),
    Id (sf_path_connects start goal seed) true ->
    And (Id (sf_path_connects start goal
               (sf_min_pick cmp start goal
                  (sf_min_pick cmp start goal seed r1) r2)) true)
        (And (real_le (sf_action (sf_min_pick cmp start goal
                                  (sf_min_pick cmp start goal seed r1) r2))
                      (sf_action seed))
             (And (forall x : list SFVec,
                     InT x r1 -> Id (sf_path_connects start goal x) true ->
                     real_le (sf_action (sf_min_pick cmp start goal
                                           (sf_min_pick cmp start goal seed r1) r2))
                             (sf_action x))
                  (forall x : list SFVec,
                     InT x r2 -> Id (sf_path_connects start goal x) true ->
                     real_le (sf_action (sf_min_pick cmp start goal
                                           (sf_min_pick cmp start goal seed r1) r2))
                             (sf_action x)))).
Proof.
  intros cmp start goal r1 r2 seed Hseed.
  (* 第一段：r1 段选取（三面），And 拆翼走 v5 件 abe_and_l/r 管件（链上使用）。 *)
  destruct (sf_min_pick_spec cmp start goal r1 seed Hseed) as [Hc1 Hr1].
  pose proof (abe_and_l _ _ Hr1) as Hb1.
  pose proof (abe_and_r _ _ Hr1) as Hd1.
  (* 第二段：以 r1 段结果为种子的 r2 段选取；连通前提槽由第一段连通面接入。 *)
  destruct (sf_min_pick_spec cmp start goal r2
              (sf_min_pick cmp start goal seed r1) Hc1) as [Hc2 Hr2].
  pose proof (abe_and_l _ _ Hr2) as Hb2.
  pose proof (abe_and_r _ _ Hr2) as Hd2.
  split.
  - (* 连通面：第二段连通面直交。 *)
    exact Hc2.
  - split.
    + (* 种子面：E(二段) ≤ E(一段) ≤ E(seed)，trans 复合两段种子面。 *)
      exact (real_le_trans _ _ _ Hb2 Hb1).
    + split.
      * (* r1 候选面：E(二段) ≤ E(一段) ≤ E(x)，第一段候选面真行使。 *)
        intros x Hx Hcx.
        exact (real_le_trans _ _ _ Hb2 (Hd1 x Hx Hcx)).
      * (* r2 候选面：第二段候选面真行使。 *)
        intros x Hx Hcx.
        exact (Hd2 x Hx Hcx).
Qed.

(* ============================================================ *)
(* §1 载体二·最小作用量选取 spec：具体无命中实例（贪心跳过分支的       *)
(*    计算实拍）。cmp 全程量化未被行使（无命中分支不调用比较接口）。   *)
(* ============================================================ *)

Definition abj_vz : SFVec := real_zero :: nil.
Definition abj_seed_path : list SFVec := abj_vz :: nil.
Definition abj_miss_cands : list (list SFVec) := ((nil : SFVec) :: nil) :: nil.

Theorem abj_minpick_concrete_nohit :
  forall cmp : forall a b : Real, Or (real_le a b) (real_lt b a),
    And (Id (sf_path_connects abj_vz abj_vz
               (sf_min_pick cmp abj_vz abj_vz abj_seed_path abj_miss_cands)) true)
        (And (real_le (sf_action (sf_min_pick cmp abj_vz abj_vz
                                  abj_seed_path abj_miss_cands))
                      (sf_action abj_seed_path))
             (forall x : list SFVec,
                InT x abj_miss_cands ->
                Id (sf_path_connects abj_vz abj_vz x) true ->
                real_le (sf_action (sf_min_pick cmp abj_vz abj_vz
                                      abj_seed_path abj_miss_cands))
                        (sf_action x))).
Proof.
  intros cmp. split.
  - (* 候选 [空向量] 首态散列 0≠1 不命中：选取归约为种子 [abj_vz]， *)
    (* 种子路径首尾均为 abj_vz（散列 1）连通——全计算闭合。           *)
    exact id_refl.
  - split.
    + (* 选取＝种子：能量自反。 *)
      apply real_le_refl.
    + intros x Hx Hcx.
      inversion Hx as [l0 | y l0 Hin]; subst.
      * (* 唯一候选＝[空向量]：散列 0≠1 不命中，连通前提引 false=true 矛盾。 *)
        assert (Hf : sf_path_connects abj_vz abj_vz ((nil : SFVec) :: nil) = true).
        { exact (sf_bool_id_true _ Hcx). }
        unfold abj_vz in Hf.
        cbn [sf_path_connects sf_vec_hash sf_last Nat.eqb andb] in Hf.
        discriminate Hf.
      * (* InT x nil：空表无成员（Rocq 9 对该族指标不剪枝 destruct，      *)
        (* 沿 S12 判例用 inversion 指标内射剪枝）。 *)
        inversion Hin.
Qed.

(* ============================================================ *)
(* §2 载体三·梯度下降单步精确等式：一般形（QId 等式面真行使）与        *)
(*    具体实例（h=1/2、t=0、x=3，两侧均归约 9/8 计算闭合）并载。       *)
(* ============================================================ *)

Theorem abj_grad_step_general_and_half :
  And (forall h t x : Q,
         QId (sf_quad_cost t (sf_grad_step h t x))
             ((1 - h) * (1 - h) * sf_quad_cost t x))
      (QId (sf_quad_cost 0 (sf_grad_step (1#2) 0 3))
           ((1 - (1#2)) * (1 - (1#2)) * sf_quad_cost 0 3)).
Proof.
  split.
  - (* 一般形：上游引理出口为 Qeq（stdlib ==）面，经 qid_intro 入 Set 层 QId。 *)
    intros h t x. apply qid_intro.
    exact (sf_grad_cost_step_eq h t x).
  - (* 具体实例：grad_step=3/2、代价=9/8；(1/2)²·(9/2)=9/8——Qeq_bool 计算。 *)
    exact id_refl.
Qed.

(* ============================================================ *)
(* §3 载体四·共识两体距离为零：正反双配对＋具体智能体实例三翼           *)
(*    （sf_consensus_dist_zero ×3 真行使，real_eq Set 层面）。         *)
(* ============================================================ *)

Theorem abj_consensus_pair_zero_both :
  And (forall a b : SFAgent,
         real_eq (sf_dist_sq (sf_agent_coord (fst (sf_consensus_update a b)))
                             (sf_agent_coord (snd (sf_consensus_update a b))))
                 real_zero)
      (And (forall a b : SFAgent,
              real_eq (sf_dist_sq (sf_agent_coord (fst (sf_consensus_update b a)))
                                  (sf_agent_coord (snd (sf_consensus_update b a))))
                      real_zero)
           (real_eq (sf_dist_sq
                       (sf_agent_coord
                          (fst (sf_consensus_update
                                  (Build_SFAgent 0 (real_zero :: nil))
                                  (Build_SFAgent 1 (real_one :: nil)))))
                       (sf_agent_coord
                          (snd (sf_consensus_update
                                  (Build_SFAgent 0 (real_zero :: nil))
                                  (Build_SFAgent 1 (real_one :: nil))))))
                    real_zero)).
Proof.
  split.
  - (* 正配对：主定理直交。 *)
    intros a b. exact (sf_consensus_dist_zero a b).
  - split.
    + (* 反配对：主定理换位实例（两次行使的第二翼）。 *)
      intros a b. exact (sf_consensus_dist_zero b a).
    + (* 具体实例：智能体 (0,|0|) 与 (1,|1|) 共识后同坐标。 *)
      exact (sf_consensus_dist_zero (Build_SFAgent 0 (real_zero :: nil))
                                    (Build_SFAgent 1 (real_one :: nil))).
Qed.

(* ============================================================ *)
(* §4 载体五·消息传递收缩：迭代分裂复合形——n 段后再 m 段不劣于起点      *)
(*    （收缩主定理两次真行使，单步前提槽原样贯通，沿参数面使用）。      *)
(* ============================================================ *)

Theorem abj_mp_iter_split_no_regress :
  forall (g : SFGraph)
         (Hstep : forall f : list SFVec,
                    real_le (sf_sq_sum (sf_mflatten (sf_message_passing g f)))
                            (sf_sq_sum (sf_mflatten f)))
         (feats : list SFVec) (n m : nat),
    real_le (sf_sq_sum (sf_mflatten (sf_iterate_mp g (sf_iterate_mp g feats n) m)))
            (sf_sq_sum (sf_mflatten feats)).
Proof.
  intros g Hstep feats n m.
  apply (real_le_trans
           (sf_sq_sum (sf_mflatten (sf_iterate_mp g (sf_iterate_mp g feats n) m)))
           (sf_sq_sum (sf_mflatten (sf_iterate_mp g feats n)))
           (sf_sq_sum (sf_mflatten feats))).
  - (* 后 m 段：主定理以「n 段结果表」为起点实例化。 *)
    exact (sf_message_passing_contractive g Hstep (sf_iterate_mp g feats n) m).
  - (* 前 n 段：主定理原位实例化。 *)
    exact (sf_message_passing_contractive g Hstep feats n).
Qed.

(* ============================================================ *)
(* §5 载体六·课程学习单调（节内三槽出节显式化）：两段课程复合形——      *)
(*    先 s1 后 s2 的累计课程不增损失（主定理两次真行使逐段复合）。      *)
(* ============================================================ *)

Theorem abj_curriculum_two_stage :
  forall (M : Set) (step : M -> SFVec -> M) (loss : M -> Real)
         (Hok : forall (m : M) (smp : SFVec),
                  real_le (loss (step m smp)) (loss m))
         (s1 s2 : list SFVec) (m0 : M),
    real_le (loss (sf_curriculum_run M step s2 (sf_curriculum_run M step s1 m0)))
            (loss m0).
Proof.
  intros M step loss Hok s1 s2 m0.
  apply (real_le_trans
           (loss (sf_curriculum_run M step s2 (sf_curriculum_run M step s1 m0)))
           (loss (sf_curriculum_run M step s1 m0))
           (loss m0)).
  - (* 后段 s2：主定理以「s1 段结果模型」为起点实例化。 *)
    exact (sf_curriculum_monotone M step loss Hok s2 (sf_curriculum_run M step s1 m0)).
  - (* 前段 s1：主定理原位实例化。 *)
    exact (sf_curriculum_monotone M step loss Hok s1 m0).
Qed.

(* ============================================================ *)
(* §6 载体七·Wasserstein 块三件：对称（一般形＋具体计算）、同分布零     *)
(*    （一般形＋具体计算）、配对均方＝逐点差平方和（QId 面真行使）。    *)
(* ============================================================ *)

Theorem abj_qw2_triple :
  And (forall mu nu : list Q,
         Id (Qeq_bool (sf_qw2 mu nu) (sf_qw2 nu mu)) true)
      (And (forall mu : list Q,
              Id (Qeq_bool (sf_qw2 mu mu) 0) true)
           (And (forall mu nu : list Q,
                   QId (sf_qw2 mu nu)
                       (sf_qsum (map (fun d : Q => d * d) (sf_qsub mu nu))))
                (And (Id (Qeq_bool (sf_qw2 ((1#2) :: nil) ((1#3) :: nil))
                                 (sf_qw2 ((1#3) :: nil) ((1#2) :: nil))) true)
                     (Id (Qeq_bool (sf_qw2 ((1#2) :: nil) ((1#2) :: nil)) 0) true)))).
Proof.
  split.
  - (* 对称一般形：主定理直交。 *)
    intros mu nu. exact (sf_qw2_sym mu nu).
  - split.
    + (* 同分布零一般形：主定理直交。 *)
      intros mu. exact (sf_qw2_same mu).
    + split.
      * (* 等式面：上游出口为 Qeq 面，经 qid_intro 入 Set 层 QId。 *)
        intros mu nu. apply qid_intro.
        exact (sf_qw2_eq_qsub mu nu).
      * split.
        -- (* 对称具体实例：(1/2,1/3) 两向均归约 (1/36)²，计算闭合。 *)
           exact id_refl.
        -- (* 同分布零具体实例：(1/2)−(1/2)=0，计算闭合。 *)
           exact id_refl.
Qed.

(* ============================================================ *)
(* §7 载体八·Q 学习块：α=0 表值不变主定理一般形真行使＋具体表格实例     *)
(*    （q=[[5]]，α=0 更新后读数不变，Qeq_bool 计算闭合）。             *)
(* ============================================================ *)

Theorem abj_qupdate_alpha0_pair :
  And (forall (q : SFQTable) (s a sp : nat) (r gamma : Q),
         Id (Qeq_bool (nth a (nth s (sf_q_update q s a sp r 0 gamma) nil) 0)
                      (nth a (nth s q nil) 0)) true)
      (Id (Qeq_bool (nth 0 (nth 0 (sf_q_update (((5#1) :: nil) :: nil) 0 0 0
                                    (3#1) 0 (1#2)) nil) 0)
                    (nth 0 (nth 0 (((5#1) :: nil) :: nil) nil) 0)) true).
Proof.
  split.
  - (* 一般形：主定理直交。 *)
    intros q s a sp r gamma. exact (sf_q_update_alpha0 q s a sp r gamma).
  - (* 具体实例：α=0 时新值=旧值=5，更新幂等——Qeq_bool 计算闭合。 *)
    exact id_refl.
Qed.

(* ============================================================ *)
(* §8 尾舱·假设审计（S12 余位矿十二真位直审＋两空壳位直审＋v5 六载体    *)
(*    链审＋本件八载体自审）。判读判据：二十八条全输出                  *)
(*    Closed under the global context。                                *)
(*    注：Require 闭包含 Lqa（Q 域 nra/lra 供给面），coqchk 环境公理    *)
(*    面沿 CT1B 判例与逐定理 PA 定检分账，非本件引入。                 *)
(* ============================================================ *)

(* —— S12 余位矿十二真位（本件直审主体）—— *)
Print Assumptions S12_B5RecycleSF.sf_min_pick_spec.
Print Assumptions S12_B5RecycleSF.sf_minimal_action_exists.
Print Assumptions S12_B5RecycleSF.sf_grad_cost_step_eq.
Print Assumptions S12_B5RecycleSF.sf_consensus_dist_zero.
Print Assumptions S12_B5RecycleSF.sf_message_passing_contractive.
Print Assumptions S12_B5RecycleSF.sf_curriculum_monotone.
Print Assumptions S12_B5RecycleSF.sf_qw2_sym.
Print Assumptions S12_B5RecycleSF.sf_qw2_same.
Print Assumptions S12_B5RecycleSF.sf_qw2_eq_qsub.
Print Assumptions S12_B5RecycleSF.sf_q_update_alpha0.
Print Assumptions S12_B5RecycleSF.sf_q_update_zero_core.
Print Assumptions S12_B5RecycleSF.sf_nth_update_same_qeq.
(* —— 同件在档空壳位（登记不使用，公理面闭合为真）—— *)
Print Assumptions S12_B5RecycleSF.sf_kmeans_nonincrease.
Print Assumptions S12_B5RecycleSF.sf_viterbi_matches.
(* —— v5 前位件六载体链审（链编闭包复核）—— *)
Print Assumptions abe_grad_half_two_step.
Print Assumptions abe_consensus_iter_split.
Print Assumptions abe_consensus_bounded_one.
Print Assumptions abe_uf_self_union_and_pair.
Print Assumptions abe_viterbi_concrete_matched.
Print Assumptions abe_beam_rerun_no_regress.
(* —— 本件八载体自审 —— *)
Print Assumptions abj_minpick_two_stage.
Print Assumptions abj_minpick_concrete_nohit.
Print Assumptions abj_grad_step_general_and_half.
Print Assumptions abj_consensus_pair_zero_both.
Print Assumptions abj_mp_iter_split_no_regress.
Print Assumptions abj_curriculum_two_stage.
Print Assumptions abj_qw2_triple.
Print Assumptions abj_qupdate_alpha0_pair.

(* ============================================================ *)
(* §9 出口舱：载体兼任提取端口（G3：提取面零魔数）                     *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abj_minpick_two_stage abj_minpick_concrete_nohit
  abj_grad_step_general_and_half abj_consensus_pair_zero_both
  abj_mp_iter_split_no_regress abj_curriculum_two_stage
  abj_qw2_triple abj_qupdate_alpha0_pair.
