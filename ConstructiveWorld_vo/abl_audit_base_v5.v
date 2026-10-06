(* ===================================================================== *)
(*  abl_audit_base_v5.v —— 审计载体扩容 v5·S12 引擎正确性面直审闭合件        *)
(* ===================================================================== *)
(*  使命: Z 裸奔 Top（S12 引擎正确性面 1/113：50 Fixpoint 算法大陆的引擎     *)
(*        正确性主定理族）的甲形态直审闭合。本件 Require S12_B5RecycleSF，    *)
(*        对五引擎正确性主定理各铸一条轻量真使用载体（使用＝证明体真实行使   *)
(*        上游定理非空壳），共五载体八使用点：                              *)
(*        ① abe_grad_half_two_step——梯度下降 n 步收敛界主定理               *)
(*          （sf_grad_descent_convergence）在步长 1/2、n=2 的具体实例收敛    *)
(*          面与精确等式面（sf_grad_descent_cost_eq）单语句并载；            *)
(*        ② abe_consensus_iter_split——共识迭代长度分账引理                  *)
(*          （sf_consensus_iter_len）的迭代分裂复合形：k1+k2 两段迭代后      *)
(*          长度账 (L−k1−k2)+k1+k2=L，Set 层 NatLe/Id 包装；                 *)
(*        ③ abe_consensus_bounded_one——共识收敛主定理                       *)
(*          （sf_consensus_converges）在 eps:=real_one 的具体实例 sigT 形；  *)
(*        ④ abe_uf_self_union_and_pair——并查集合并幂等主定理                *)
(*          （sf_uf_union_idempotent_same_root）的一般形（x 自并为恒等）      *)
(*          与具体实例（uf=[(1,0)] 合并 1,0 表不变）并载；                   *)
(*        ⑤ abe_viterbi_concrete_matched——维特比正确性调形使用：Z 报告点名   *)
(*          维特比，核验 sf_viterbi_matches 语句面为「前提→True」空壳        *)
(*          （E856 空壳前科同族，fail-loud 登记调形），降档对维特比函数       *)
(*          本体（sf_viterbi+sf_vec_hash）作三个具体小实例计算使用：         *)
(*          观测命中得路径、观测不中空路径、两步贪心各取当步命中态           *)
(*          （双态表＝空向量｜单零分量向量，沿 sf_vec_hash 0/1 摘要）；       *)
(*        ⑥ abe_beam_rerun_no_regress——束搜索最优性主定理                   *)
(*          （sf_beam_search_optimal）与辅助引理（sf_beam_aux_correct）      *)
(*          双使用：以首轮结果为种子的复核不回退（能量≤首轮结果）且最优性    *)
(*          对候选面保持（能量≤任一候选），全比较接口 cmp 沿 S12 出口       *)
(*          参数面 Set 层（S01.Or:=A+B）显式量化（LPO 墙族沿 S12 自注登记，  *)
(*          接口层禁硬证，本件沿参数面使用不实例化）。                      *)
(*  依赖: S01_BaseRing S02_CauchyComplete S12_B5RecycleSF                   *)
(*        （-Q 预编译树 vo_local_world_unified_0930 只读引用）；             *)
(*        Stdlib（QArith/List/Arith/Lia/Extraction 出口舱）。                *)
(*  构造性: 零承认语句、零经典逻辑、零 Prop 载体：语句面合取全 S01.And       *)
(*        （:=A*B，Set 层），等同全 S01.Id（Set 层），存在/见证全 sigT       *)
(*        （Set 层），nat 序前提全 S01.NatLe（:=Id(Qeq_bool 面) 同族 Set 层）， *)
(*        比较全 real_le/real_lt/QleT'/QId（Set 型）；无 exists/Prop 连词、  *)
(*        无否定形书写；内部辅助件 abe_consensus_iter_add/abe_eq_id 系       *)
(*        stdlib eq 使用管件（上游 iter_len 出口为 stdlib eq 形的必经桥），  *)
(*        非载体语句。证明体全 exact/apply/cbn 显式项直交。                  *)
(*  编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&        *)
(*        ulimit -s 65532 && nice -19 rocq c -native-compiler no             *)
(*        -Q vo_local_world_unified_0930 "" <池>/abl_audit_base_v5.v          *)
(*        （独占池 audit_base_v5/，道闸 ≤1，单件无池内链序）。                *)
(*  核验注: ①五引擎主定理出口签名以 rocq repl Check 实拍为准——           *)
(*        sf_grad_descent_convergence/sf_consensus_iter_len/                *)
(*        sf_consensus_converges/sf_uf_union_idempotent_same_root 四件       *)
(*        顶层面零节参；sf_beam_search_optimal 首参为显式全比较接口          *)
(*        cmp（S12 SFPathEnergy 节 Variable 出节）；sf_viterbi_matches        *)
(*        出口为「前提→True」空壳实拍（本件登记不使用）。②sf_step_half       *)
(*        与 sf_step_half_bounds 为 S12 自带具体实例件，本件直接使用其       *)
(*        And 结构（proj1/proj2 喂收敛主定理前提槽）。③abe_ 前缀全树        *)
(*        grep 零命中。④sf_vec_hash：nil→0、非空→1（演示级摘要），          *)
(*        维特比具体实例沿此可全计算化。                                    *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S12_B5RecycleSF.
From Stdlib Require Import QArith.QArith QArith.Qabs
               Lists.List Arith.Arith.
Import ListNotations.
From Stdlib Require Import Lia.
Local Open Scope Q_scope.

(* ============================================================ *)
(* §0 内部管件舱（stdlib eq 使用桥，非载体语句）                    *)
(* ============================================================ *)

(* stdlib eq → Set 层 Id 桥（上游 iter_len 出口为 stdlib eq 形的必经转换）。 *)
Lemma abe_eq_id : forall (A : Set) (x y : A), x = y -> Id x y.
Proof.
  intros A x y H. destruct H. apply id_refl.
Qed.

(* S01.And（:=A*B，Set 层）消去双翼（And 定义包装的显式 δ 管件）。 *)
Definition abe_and_l (A B : Set) (p : And A B) : A :=
  match p with (a, _) => a end.
Definition abe_and_r (A B : Set) (p : And A B) : B :=
  match p with (_, b) => b end.

(* 共识迭代分裂：k1+k2 两段迭代 ≡ 以 k1 段结果为起点的 k2 段迭代
   （沿 sf_consensus_iter Fixpoint 的内核转换，stdlib eq 形内部管件）。 *)
Lemma abe_consensus_iter_add :
  forall (k1 : nat) (agents : list SFAgent) (k2 : nat),
    sf_consensus_iter agents (k1 + k2)
    = sf_consensus_iter (sf_consensus_iter agents k1) k2.
Proof.
  intros k1. induction k1 as [| k1' IH]; intros agents k2.
  - reflexivity.
  - cbn [Nat.add sf_consensus_iter].
    exact (IH (map (fun p => fst (sf_consensus_update (fst p) (snd p)))
                   (sf_pair_agents agents)) k2).
Qed.

(* ============================================================ *)
(* §1 载体一·梯度下降：n 步收敛界主定理的 1/2 步长两步具体实例        *)
(*    （收敛面 QleT' ＋ 精确等式面 QId 单语句并载，双使用）          *)
(* ============================================================ *)

Theorem abe_grad_half_two_step :
  forall (t x : Q),
    And (QleT' (sf_quad_cost t (sf_grad_descent sf_step_half t x 2))
               (qpow2 ((1 - sf_step_half) * (1 - sf_step_half)) 2
                * sf_quad_cost t x))
        (QId (sf_quad_cost t (sf_grad_descent sf_step_half t x 2))
             (qpow2 ((1 - sf_step_half) * (1 - sf_step_half)) 2
              * sf_quad_cost t x)).
Proof.
  intros t x. split.
  - (* 收敛面：主定理在 h:=1/2、n:=2 具体实例化，前提槽喂 S12 自带 *)
    (* sf_step_half_bounds 的 And 两翼（proj1/proj2 真行使）。          *)
    exact (@sf_grad_descent_convergence sf_step_half t x 2
             (abe_and_l _ _ sf_step_half_bounds)
             (abe_and_r _ _ sf_step_half_bounds)).
  - (* 精确等式面：n 步代价等式主引理具体实例化，经 qid_intro 入 Set 层 QId。 *)
    apply qid_intro.
    exact (sf_grad_descent_cost_eq sf_step_half t 2 x).
Qed.

(* ============================================================ *)
(* §2 载体二·共识迭代（甲）：迭代分裂复合形——长度分账引理双使用        *)
(*    前提 Set 层 NatLe，结论 Set 层 Id。                             *)
(* ============================================================ *)

Theorem abe_consensus_iter_split :
  forall (agents : list SFAgent) (k1 k2 : nat),
    NatLe (k1 + k2) (length agents) ->
    Id ((length (sf_consensus_iter agents (k1 + k2)) + k1) + k2)%nat
       (length agents).
Proof.
  intros agents k1 k2 Hk.
  pose proof (NatLe_drop (k1 + k2) (length agents) Hk) as Hk'.
  assert (Hk1 : (k1 <= length agents)%nat).
  { apply (Nat.le_trans _ (k1 + k2) _ (Nat.le_add_r k1 k2)). exact Hk'. }
  pose proof (sf_consensus_iter_len k1 agents Hk1) as H1.
  assert (Hk2 : (k2 <= length (sf_consensus_iter agents k1))%nat) by lia.
  pose proof (sf_consensus_iter_len k2 (sf_consensus_iter agents k1) Hk2) as H2.
  rewrite (abe_consensus_iter_add k1 agents k2).
  apply abe_eq_id. lia.
Qed.

(* ============================================================ *)
(* §3 载体三·共识迭代（乙）：收敛主定理在 eps:=real_one 的具体实例     *)
(*    （sigT 见证 Set 层；0<1 前提 Set 层 real_lt 显式保留）。         *)
(* ============================================================ *)

Theorem abe_consensus_bounded_one :
  forall (agents : list SFAgent),
    real_lt real_zero real_one ->
    sigT (fun k : nat =>
      forall x y : SFAgent,
        InT x (sf_consensus_iter agents k) ->
        InT y (sf_consensus_iter agents k) ->
        real_le (sf_dist_sq (sf_agent_coord x) (sf_agent_coord y)) real_one).
Proof.
  intros agents H01.
  exact (sf_consensus_converges agents real_one H01).
Qed.

(* ============================================================ *)
(* §4 载体四·并查集：合并幂等主定理的一般形（自并恒等）与             *)
(*    具体实例（uf=[(1,0)] 合并 1,0 根同为 0 表不变）并载，双使用。    *)
(* ============================================================ *)

Theorem abe_uf_self_union_and_pair :
  And (forall (uf : SFUnionFind) (x : nat), Id (sf_uf_union uf x x) uf)
      (Id (sf_uf_union ((1%nat, 0%nat) :: nil) 1%nat 0%nat)
          ((1%nat, 0%nat) :: nil)).
Proof.
  split.
  - (* 一般形：主定理喂 id_refl 根同前提（find2 uf x = find2 uf x 定义性）。 *)
    intros uf x. apply sf_uf_union_idempotent_same_root. apply id_refl.
  - (* 具体实例：find2 在具体表上两根同归 0（cbn 计算实拍），再行使主定理。 *)
    apply sf_uf_union_idempotent_same_root.
    cbn [sf_uf_find2 Nat.eqb]. apply id_refl.
Qed.

(* ============================================================ *)
(* §5 载体五·维特比：函数本体具体小实例计算使用（调形闭合）            *)
(*    Z 报告点名维特比正确性；核验主定理 sf_viterbi_matches 语句面    *)
(*    为「前提→True」空壳（E856 前科同族，登记不使用——使用空壳        *)
(*    即空壳使用，禁）。降档对引擎函数本体（sf_viterbi+sf_vec_hash）  *)
(*    作三个具体小实例：命中得路径／不中空路径／两步贪心各取命中态，   *)
(*    全计算化 born-green（这才是「路径与观察匹配」的真内容供给）。     *)
(* ============================================================ *)

Theorem abe_viterbi_concrete_matched :
  And (Id (sf_viterbi (nil :: nil) (sf_vec_hash nil :: nil)) (nil :: nil))
      (And (Id (sf_viterbi (nil :: nil) (1 :: nil)%nat) nil)
           (Id (sf_viterbi ((nil : SFVec) :: (real_zero :: nil) :: nil)
                           (0 :: 1 :: nil)%nat)
               ((nil : SFVec) :: (real_zero :: nil) :: nil))).
Proof.
  split.
  - (* 观测 [hash nil]=0 命中唯一态：路径=[nil]，长度匹配的真内容。 *)
    exact id_refl.
  - split.
    + (* 观测 1 无态命中：路径空（贪心跳过分支的计算实拍）。 *)
      exact id_refl.
    + (* 观测 [0;1] 对双态表（空向量｜单零分量向量）逐步命中：
         两步各取当步命中态（贪心主循环两分支的计算实拍）。 *)
      exact id_refl.
Qed.

(* ============================================================ *)
(* §6 载体六·束搜索：最优性主定理＋辅助引理双使用——复核不回退且       *)
(*    最优性保持。全比较接口 cmp 沿 S12 出口参数面显式量化            *)
(*    （S01.Or:=A+B Set 层；LPO 墙族沿 S12 自注登记，接口层禁硬证，    *)
(*    本件沿参数面使用不实例化）。                                    *)
(* ============================================================ *)

Theorem abe_beam_rerun_no_regress :
  forall (cmp : forall p q : list SFVec,
            Or (real_le (sf_path_energy p) (sf_path_energy q))
               (real_lt (sf_path_energy q) (sf_path_energy p)))
         (cands : list (list SFVec)) (seed p : list SFVec),
    InT p cands ->
    And (real_le (sf_path_energy (sf_beam_search cmp cands
                    (sf_beam_search cmp cands seed)))
                 (sf_path_energy (sf_beam_search cmp cands seed)))
        (real_le (sf_path_energy (sf_beam_search cmp cands
                    (sf_beam_search cmp cands seed)))
                 (sf_path_energy p)).
Proof.
  intros cmp cands seed p Hin. split.
  - (* 复核不回退：辅助引理以「首轮结果 bs 及其能量」为新种子实例化， *)
    (* proj1 翼（E 复核 ≤ E bs）；sf_beam_search 展开形定义性吻合。      *)
    exact (abe_and_l _ _ (sf_beam_aux_correct cmp cands
                   (sf_beam_search cmp cands seed))).
  - (* 最优性保持：主定理以种子:=首轮结果实例化，InT p cands 原样入位。 *)
    exact (sf_beam_search_optimal cmp cands
             (sf_beam_search cmp cands seed) p Hin).
Qed.

(* ============================================================ *)
(* §7 尾舱·假设审计（S12 引擎面八主定理跨件直审＋本件六载体自审）      *)
(*    判读判据：十四条全输出 Closed under the global context。         *)
(*    前 8 条＝S12 引擎正确性面主定理族的跨件追审（引擎面此前全树      *)
(*    PA 直审缺位，Z 裸奔 Top 本体）；后 6 条＝本件六载体自审。        *)
(*    注：Require 闭包含 Lqa（Q 域 nra/lra 供给面），coqchk 环境公理   *)
(*    面沿 CT1B 判例与逐定理 PA 定检分账，非本件引入。                 *)
(* ============================================================ *)

Print Assumptions S12_B5RecycleSF.sf_grad_descent_convergence.
Print Assumptions S12_B5RecycleSF.sf_grad_descent_cost_eq.
Print Assumptions S12_B5RecycleSF.sf_consensus_iter_len.
Print Assumptions S12_B5RecycleSF.sf_consensus_converges.
Print Assumptions S12_B5RecycleSF.sf_uf_union_idempotent_same_root.
Print Assumptions S12_B5RecycleSF.sf_beam_search_optimal.
Print Assumptions S12_B5RecycleSF.sf_beam_aux_correct.
Print Assumptions S12_B5RecycleSF.sf_viterbi_matches.
Print Assumptions abe_grad_half_two_step.
Print Assumptions abe_consensus_iter_split.
Print Assumptions abe_consensus_bounded_one.
Print Assumptions abe_uf_self_union_and_pair.
Print Assumptions abe_viterbi_concrete_matched.
Print Assumptions abe_beam_rerun_no_regress.

(* ============================================================ *)
(* §8 出口舱：载体兼任提取端口（G3：提取面零魔数）                     *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abe_grad_half_two_step abe_consensus_iter_split
  abe_consensus_bounded_one abe_uf_self_union_and_pair
  abe_viterbi_concrete_matched abe_beam_rerun_no_regress.
