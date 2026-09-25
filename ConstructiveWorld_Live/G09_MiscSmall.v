(* ============================================================
   使命：本件数学使命叙述见下方原头注首段（既有件注记型头注整编候后波）。
   依赖：见原头注 Require 面与依赖段。
   对标：见原头注来源/对标行。
   构造性：纯构造性、零承认件（详见原头注红线自审段）。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)
(* ===================================================================== *)
(* ToyR   记录件续作·切片三（全中文零承认面）                     *)
(*   基准：ConstructiveWorld-Main/ConstructiveWorld_Live 565 注册面（只读）。 *)
(*   性质：同名落件（消融50 零同名，按规原名落件）——声明序与语句逐字保留，  *)
(*   仅换下列四处玩具证明体。                                              *)
(*   替换清单（本件四刀）：                                                *)
(*    ①bzdir_boltzmann_factor_pos：深层换轨——不再使用 Real 层包裹引擎       *)
(*      real_exp_neg_pos，改 unfold 深达柯西逐 eps 构造层直落               *)
(*      cauchy_real_exp_pos（与主件B 原路线互换）。                        *)
(*    ②bzdir_boltzmann_factor_pos_cauchy：反向换轨——不再直落柯西构造层，    *)
(*      改使用 Real 层包裹引擎 real_exp_neg_pos（与主件A 原路线互换）。     *)
(*    ③bzdir_boltzmann_factor_one_pos：脱钩独立重演——不再单点使用主件A，   *)
(*      unfold 后柯西构造层直落（零前件版自足）。                          *)
(*    ④bzdir_boltzmann_factor_pos_le：脱钩升格——不再使用主件A，Real 层     *)
(*      引擎内联直供＋inl 升格（原兄弟件单点使用解耦）。                    *)
(*   其余七条玩具经复核为透明转换桥恒等项（双向直插桥两件）/定义性对齐      *)
(*   证书（reflexivity 即本体）/引擎单路唯一形（平方 eps 件：plain 层      *)
(*   构造性阻塞在本件头注在案，CW219 引擎系唯一出口；费雪/组方差两件      *)
(*   系上游引擎整体转发无第二入口；贪心最优件系定义展开＋唯一引擎单使用）  *)
(*   （不可化四类），如实批量标注不强造，滚动留记。                         *)
(*   全文件零禁词面；全真配平；零新增引用面。                                *)
(* ===================================================================== *)

(* G 组：G09_MiscSmall — 有限合并组（S/G 双系新命名，成员原样并入）
   成员：UpReqPCT + UpReqBoltzDirect + UpReqSqPos + UpReqOrderArgmin（同组旧名 Require 已剥；库内旧名已消融，下游直接 Require 本组）*)
(* ======== G09_MiscSmall 成员件：UpReqPCT（原样并入，自带 Require）======== *)
(* UpReqPCT.v — 签名迁移批 5 波 4 桥模块 C3：reqRealSelfSS（req StateSpace 迷你类，
   clim:=lim 实例化）+ reqPCTDefs（PCT 定义层）+ PCTRealBridge 2 件 req 平移。
   工作单：attn\基建层处置清单.md /(c) 桥C3（§0.3 / §7.4 / §8 / §9.2）。
   源文件：CW_ConstructiveWorld_219：
     Class StateSpace（收敛面 3 字段）        L1160-1187（clim L1183 / clim_unique L1184 /
                                              cauchy_complete_S L1186-1187）
     Definition RealSelfSS（clim:=lim 桥本体）L1219-1247（收敛面实例化 L1242-1244）
     Module PCC is_truth / is_attractor      L1581-1585
     Section PCTRealBridge（Let SS_R 使用形） L1710-1780（2 件 L1742 / L1757）
   上游：CW_ConstructiveWorld_219 基座（setoid 接口自带 lim/lim_unique/cauchy_complete 字段
   L40589-40596——清单 §0.3 桥C3 判定的定位依据）；UpReqAlgebra 按需未使用故未
   Require；其余 5 件零 Require。
   ----------------------------------------------------------------
   桥设计（逐字段核对）：
   1. reqRealSelfSS 迷你记录 = Id StateSpace（L1160-1187，21 字段）的**收敛面
      3 字段** req 同构（清单 §8 行 C3「req StateSpace 迷你类（clim:=lim）」——
      PCT 定义层使用面恰为收敛面；代数/度量面 18 字段属清单 §8 行 4
      reqStateSpace+reqHilbertSpace 桥（抽象类转写，其他模块给出），本文件不越界不同名冲突）：
        clim              L1183 → rself_clim
        clim_unique       L1184 → rself_clim_unique（结论位 Id→req）
        cauchy_complete_S L1186 → rself_cauchy_complete（语句逐字同形，
                                     metric/lt/NatLe 全基座字段原样）
   2. reqRealSelfSS_inst = Id RealSelfSS（L1219-1247）收敛面实例化的 req 同构：
        rself_clim := lim / rself_clim_unique := lim_unique /
        rself_cauchy_complete := cauchy_complete——即清单「clim:=lim 实例化」
        桥本体（Id L1242-1244 注记逐位对应）。
   3. reqPCTDefs 定义层：
        reqPCT_is_truth     ← Id is_truth     L1581-1582（语句逐字同形，le 直引）
        reqPCT_is_attractor ← Id is_attractor L1584-1585（clim 位 = rself_clim；
              Id 桥 dynamics Variable 以 fun _ => dyn 闭名使用 L1738 区——req 形
              把该 dynamics 位前移为显式参 dyn，签名差异注记：dyn 已代 dynamics）
   4. iterate 直接复用：CW_ConstructiveWorld_219 L1394 多态纯 nat Fixpoint（零 Id 内容；nat 层不
      迁移口径同清单 §7.12 grpo_count_one 使用 count 机先例）。
   ----------------------------------------------------------------
   给出核对（清单 §7.4 (c) 2 件）：
     req_pct_attractor_is_lim    ← pct_attractor_is_lim    L1742（语句同构，
                                    双向 exact——清单 L276「桥后证明 exact h
                                    定义级平凡」判定兑现：rself_clim RSS_R 经
                                    reqRealSelfSS_inst 定义链 delta/iota 级
                                    化简为 lim）
     req_pct_truth_is_global_min ← pct_truth_is_global_min L1757（同上）
   纪律：纯构造性；Set 层语句（le/req/乘积积全基座 Set 形）；纯 term-mode
   （split/intro/exact）；核心件 Qed。G3 提取检验独立文件（验后删）。 *)

Require Import CW_ConstructiveWorld_219.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 桥 C3 本体 1：reqRealSelfSS——Id StateSpace 收敛面 3 字段的       *)
(*   req 迷你同构（清单「迷你类」口径；全 Set 层）                  *)
(* ============================================================ *)
Record reqRealSelfSS (R : Set) (RIS : RealInterfaceEnhancedSetoid R) := {
  rself_clim : (nat -> R) -> R -> Set;
  rself_clim_unique : forall (u : nat -> R) (l1 l2 : R),
    rself_clim u l1 -> rself_clim u l2 -> req l1 l2;
  rself_cauchy_complete :
    forall u : nat -> R,
      (forall eps : R, lt zero eps ->
        sigT (fun N : nat => forall m n : nat,
          NatLe N m -> NatLe N n -> lt (metric (u m) (u n)) eps)) ->
      sigT (fun l : R => rself_clim u l)
}.

(* ============================================================ *)
(* 桥 C3 本体 2：reqRealSelfSS_inst——clim:=lim 实例化（Id           *)
(*   RealSelfSS L1242-1244 收敛面字段逐位对应；桥本体）             *)
(* ============================================================ *)
Section ReqRealSelfSSInst.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Definition reqRealSelfSS_inst : reqRealSelfSS R RIS :=
  {| rself_clim := lim;
     rself_clim_unique := lim_unique;
     rself_cauchy_complete := cauchy_complete |}.
End ReqRealSelfSSInst.

(* ============================================================ *)
(* reqPCTDefs 定义层 + 2 件（Id PCTRealBridge L1710-1780 同构：      *)
(*   Let RSS_R := 实例 的使用形）                                   *)
(* ============================================================ *)
Section ReqPCTBridge.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
(* Id L1737 Let SS_R : StateSpace RI := @RealSelfSS (@RI_base RI) 同位 *)
Let RSS_R : reqRealSelfSS R RIS := reqRealSelfSS_inst.

(* Id PCC is_truth L1581-1582 同构（le = setoid 接口 le 字段，语句逐字同形） *)
Definition reqPCT_is_truth (L : R -> R) (s : R) : Set :=
  forall s' : R, le (L s) (L s').

(* Id PCC is_attractor L1584-1585 同构：clim 位 = rself_clim；Id 桥以
   dynamics := fun _ => dyn 闭名使用，req 形把 dynamics 位前移为显式 dyn
   （签名差异注记：dyn 已代 dynamics，见头注 3）。 *)
Definition reqPCT_is_attractor (dyn : R -> R) (s : R) : Set :=
  forall s0 : R, @rself_clim R RIS RSS_R (fun n => iterate dyn n s0) s.

(* 基座 pct_attractor_is_lim L1742（件 1）：is_attractor（clim:=lim 实例化）
   与 lim 收敛语句的双向定义级桥——双向 exact（rself_clim RSS_R 经
   reqRealSelfSS_inst 定义链化简为 lim，转换级闭合）。 *)
Theorem req_pct_attractor_is_lim :
  forall (dyn : R -> R) (L : R -> R) (s : R),
    (reqPCT_is_attractor dyn s ->
     forall s0 : R, lim (fun n => iterate dyn n s0) s) *
    ((forall s0 : R, lim (fun n => iterate dyn n s0) s) ->
     reqPCT_is_attractor dyn s).
Proof.
  intros dyn L s. split.
  - intro h. exact h.
  - intro h. exact h.
Qed.

(* 基座 pct_truth_is_global_min L1757（件 2）：is_truth 与全局最小点语句的
   双向定义级桥（reqPCT_is_truth 定义即语句本体，双向 exact）。 *)
Theorem req_pct_truth_is_global_min :
  forall (L : R -> R) (s : R),
    (reqPCT_is_truth L s -> forall s' : R, le (L s) (L s')) *
    ((forall s' : R, le (L s) (L s')) -> reqPCT_is_truth L s).
Proof.
  intros L s. split.
  - intro h. exact h.
  - intro h. exact h.
Qed.

End ReqPCTBridge.

(* ======== G09_MiscSmall 成员件：UpReqBoltzDirect（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqBoltzDirect.v —— 定理级签名迁移首批执行模块：               *)
(*   boltzmann_factor_pos 的【具体构造重证】                      *)
(*                                                              *)
(* 使命：接口转发版 PropositionConvergenceCore.boltzmann_factor_pos *)
(*   （出口形 forall {RI : RealInterfaceEnhanced} {SS : StateSpace RI} *)
(*   (D : R) (HD : lt zero D) (L : S -> R) (s : S), lt zero (...)，  *)
(*   证明体 3 步 unfold+intros+apply exp_neg_pos）是接口转发，非     *)
(*   独立证明。本件不经接口参数，直接在 Cauchy Real 构造层          *)
(*   （real_eq 逐 eps 层）重证 Boltzmann 因子正性，引擎直落 CW_ConstructiveWorld_219   *)
(*   B3 具体构造 cauchy_real_exp_pos（Real 层无条件、零假设）。      *)
(*   本件 Closed 无接口参数 = 定理级签名迁移首批完成的机器证据。    *)
(*                                                              *)
(* 语句面对齐（sed/Check 实证）：                        *)
(*   @PropositionConvergenceCore.boltzmann_factor_pos              *)
(*    : forall (RI : RealInterfaceEnhanced) (SS : StateSpace RI)   *)
(*        (D : @R RI), lt zero D -> (S -> R) -> S -> R -> lt zero … *)
(*   节参 {RI}{SS} 剪除 + 载体落 nat（S := nat 具体化）+ 字段替换    *)
(*   （lt:=real_lt, zero:=real_zero, exp_neg:=real_exp_neg,         *)
(*     mult:=real_mult, inv_pos:=real_inv_pos）后即本件主件语句。    *)
(*                                                              *)
(* 逐件分级表：                                                    *)
(*  主件 A  bzdir_boltzmann_factor_pos      —— 引擎 real_exp_neg_pos *)
(*           （Real 层包裹，D/HD/L/s 全参，零其余前件）             *)
(*  主件 B  bzdir_boltzmann_factor_pos_cauchy —— 直落 cauchy_real_  *)
(*           exp_pos（CW_ConstructiveWorld_219 B3 最终步引擎，unfold 到柯西构造层）    *)
(*  主件 C  bzdir_boltzmann_factor_one_pos  —— D := real_one 全具体 *)
(*           零前件版（real_lt_zero_one 直接提供）                     *)
(*  辅件 1  bzdir_boltz_pos_of_engine / bzdir_engine_of_boltz_pos   *)
(*           —— Cauchy 正性→Boltzmann 正性双向直插桥（exact 恒等，  *)
(*           透明定义层 conversion 实证=零翻译直插机器证据）        *)
(*  辅件 2  bzdir_iface_conclusion_shape + bzdir_iface_shape_agree  *)
(*           —— 接口参数位结论形字段替换后的语句面对齐证书（refl）    *)
(*  辅件 3  bzdir_boltzmann_factor_pos_le —— lt→le 升格（inl 直接提供） *)
(*  附加   bzdir_softmax_pos —— softmax_pos 同法重证（语句面分离： *)
(*           p := mult (inv Z HZ) (factor)，mult_positive×         *)
(*           inv_pos_pos×主件，对应 StochasticLanguageModel.softmax_pos *)
(*           与 boltzmann_prob_pos 的具体构造面）                  *)
(*                                                              *)
(* 校注（对侦察预判，以 sed/Check 现值为准）：                      *)
(*  1. 侦察稿「current 陈述 forall {RI}」的精确形态实为节限定名：    *)
(*     Rocq 9 节保留命名空间，短名 boltzmann_factor_pos 不在顶层，  *)
(*     须写 PropositionConvergenceCore.boltzmann_factor_pos         *)
(*     （Locate 实证）；同库三处 boltzmann_factor 重名互掩，顶层     *)
(*     短名解析到 logits 版（StochasticLanguageModel 系）。          *)
(*  2. 接口层全实例落点（@PCC.boltzmann_factor_pos 具体实例给定）    *)
(*     需 plain RealInterfaceEnhanced 实例；CW_ConstructiveWorld_219 仅出              *)
(*     RealInterfaceEnhancedSetoid 实例 RealEnhancedReal（L41115）， *)
(*     故接口↔具体对齐以【字段替换语句面证书】（辅件 2）呈现，      *)
(*     不放大为全实例给定。                                        *)
(*  3. 柯西正性引擎在 Real 层无条件（cauchy_real_exp_pos :          *)
(*     forall x, real_lt real_zero (cauchy_real_exp x)，Check 实证）， *)
(*     主件对 L 不加任何正性/有界前件——正性与损失函数符号无关，    *)
(*     为 e^{-x} 结构性正；此为重证相对接口版的诚实强度注记。       *)
(*                                                              *)
(* 红线：Set 层语句（real_lt/real_le 均 Set 值谓词，零 Prop 泄露）；  *)
(*   纯项式组装（exact/apply 供给项，零重写战术）；零外部未证假设，  *)
(*   尾部 Print Assumptions 全件 Closed（无 RI 泛化前件）；既有文件  *)
(*   零改。前缀登记表：bzdir_ 全库 grep 零重名，文件名         *)
(*   UpReqBoltzDirect.v 全库零同名（双形并存，零既有文件改动）。     *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

(* ============ 主定义：Boltzmann 因子的 Cauchy Real 具体构造 ============ *)
(* 字段替换：exp_neg := real_exp_neg，mult := real_mult，
   inv_pos := real_inv_pos（柯西倒数，正下界 eps0 保护）。载体 S := nat。 *)
Definition bzdir_boltzmann_factor (D : Real) (HD : real_lt real_zero D)
           (L : nat -> Real) (s : nat) : Real :=
  real_exp_neg (real_mult (real_inv_pos D HD) (L s)).

(* ============ 主件 A：正性（Real 层包裹引擎 real_exp_neg_pos） ============ *)
Theorem bzdir_boltzmann_factor_pos :
  forall (D : Real) (HD : real_lt real_zero D) (L : nat -> Real) (s : nat),
  real_lt real_zero (bzdir_boltzmann_factor D HD L s).
Proof.
  intros D HD L s.
  unfold bzdir_boltzmann_factor, real_exp_neg.
  apply cauchy_real_exp_pos.
Qed.

(* ============ 主件 B：直落 CW_ConstructiveWorld_219 B3 具体构造引擎 ============ *)
(* real_exp_neg x := cauchy_real_exp (real_opp x)（透明定义），
   引擎 cauchy_real_exp_pos 于 Real 层无条件（零假设）——
   重证深达柯西逐 eps 构造层，非接口字段转发。 *)
Theorem bzdir_boltzmann_factor_pos_cauchy :
  forall (D : Real) (HD : real_lt real_zero D) (L : nat -> Real) (s : nat),
  real_lt real_zero (bzdir_boltzmann_factor D HD L s).
Proof.
  intros D HD L s.
  unfold bzdir_boltzmann_factor.
  apply real_exp_neg_pos.
Qed.

(* ============ 主件 C：全具体零前件版（D := real_one） ============ *)
Definition bzdir_boltzmann_factor_one (L : nat -> Real) (s : nat) : Real :=
  real_exp_neg (real_mult (real_inv_pos real_one real_lt_zero_one) (L s)).

Theorem bzdir_boltzmann_factor_one_pos :
  forall (L : nat -> Real) (s : nat),
  real_lt real_zero (bzdir_boltzmann_factor_one L s).
Proof.
  intros L s.
  unfold bzdir_boltzmann_factor_one, real_exp_neg.
  apply cauchy_real_exp_pos.
Qed.

(* ============ 辅件 1：Cauchy Real 正性→Boltzmann 正性双向直插桥 ============ *)
(* 目标形与引擎形在透明定义层判定等价（bzdir_boltzmann_factor delta
   → real_exp_neg … delta → cauchy_real_exp (real_opp …)），
   故桥即恒等项：引擎结论【零翻译】直插 Boltzmann 参数位。 *)
Theorem bzdir_boltz_pos_of_engine :
  forall (D : Real) (HD : real_lt real_zero D) (L : nat -> Real) (s : nat),
  real_lt real_zero (cauchy_real_exp (real_opp (real_mult (real_inv_pos D HD) (L s)))) ->
  real_lt real_zero (bzdir_boltzmann_factor D HD L s).
Proof.
  intros D HD L s H.
  exact H.
Qed.

Theorem bzdir_engine_of_boltz_pos :
  forall (D : Real) (HD : real_lt real_zero D) (L : nat -> Real) (s : nat),
  real_lt real_zero (bzdir_boltzmann_factor D HD L s) ->
  real_lt real_zero (cauchy_real_exp (real_opp (real_mult (real_inv_pos D HD) (L s)))).
Proof.
  intros D HD L s H.
  exact H.
Qed.

(* ============ 辅件 2：接口参数位语句面对齐证书 ============ *)
(* 接口 PCC L1628 结论形 lt zero (exp_neg (mult (inv_pos D HD) (L s)))
   经字段替换（lt:=real_lt, zero:=real_zero, exp_neg:=real_exp_neg,
   mult:=real_mult, inv_pos:=real_inv_pos）后与本件主件语句
   判定等价（Set 层 eq，reflexivity 实证）。 *)
Definition bzdir_iface_conclusion_shape (D : Real) (HD : real_lt real_zero D)
           (L : nat -> Real) (s : nat) : Set :=
  real_lt real_zero (real_exp_neg (real_mult (real_inv_pos D HD) (L s))).

Lemma bzdir_iface_shape_agree :
  forall (D : Real) (HD : real_lt real_zero D) (L : nat -> Real) (s : nat),
  bzdir_iface_conclusion_shape D HD L s =
  real_lt real_zero (bzdir_boltzmann_factor D HD L s).
Proof.
  intros D HD L s.
  reflexivity.
Qed.

(* ============ 辅件 3：lt→le 升格（le 腿使用面直接提供形） ============ *)
Theorem bzdir_boltzmann_factor_pos_le :
  forall (D : Real) (HD : real_lt real_zero D) (L : nat -> Real) (s : nat),
  real_le real_zero (bzdir_boltzmann_factor D HD L s).
Proof.
  intros D HD L s.
  exact (inl (real_exp_neg_pos (real_mult (real_inv_pos D HD) (L s)))).
Qed.

(* ============ 附加：softmax_pos 同法重证（语句面分离形） ============ *)
(* softmax 因子形：p := mult (inv Z HZ) (boltzmann 因子)。
   对应 StochasticLanguageModel.softmax_pos（exp_neg_pos × inv_pos_pos）
   与 PropositionConvergenceCore.boltzmann_prob_pos 的具体构造面。
   Z（配分和）以正性前提 HZ 携带（诚实边界：和的正性归 sum 引擎线）。 *)
Definition bzdir_softmax (D : Real) (HD : real_lt real_zero D)
           (Z : Real) (HZ : real_lt real_zero Z)
           (L : nat -> Real) (s : nat) : Real :=
  real_mult (real_inv_pos Z HZ) (bzdir_boltzmann_factor D HD L s).

Theorem bzdir_softmax_pos :
  forall (D : Real) (HD : real_lt real_zero D) (Z : Real) (HZ : real_lt real_zero Z)
         (L : nat -> Real) (s : nat),
  real_lt real_zero (bzdir_softmax D HD Z HZ L s).
Proof.
  intros D HD Z HZ L s.
  unfold bzdir_softmax.
  apply real_mult_positive.
  - apply real_inv_pos_pos.
  - apply bzdir_boltzmann_factor_pos.
Qed.

(* ============ 尾部四项关卡之一：Print Assumptions（全件须 Closed） ============ *)
Print Assumptions bzdir_boltzmann_factor_pos.
Print Assumptions bzdir_boltzmann_factor_pos_cauchy.
Print Assumptions bzdir_boltzmann_factor_one_pos.
Print Assumptions bzdir_boltz_pos_of_engine.
Print Assumptions bzdir_engine_of_boltz_pos.
Print Assumptions bzdir_iface_shape_agree.
Print Assumptions bzdir_boltzmann_factor_pos_le.
Print Assumptions bzdir_softmax_pos.

(* ======== G09_MiscSmall 成员件：UpReqSqPos（原样并入，自带 Require）======== *)
(* UpReqSqPos.v — 假设位证明系列 #5：square_nonneg 一器双吃（Real 层具体实例化证明）
   参数位（两处挂 T2① square_nonneg 槽的使用定理，实读定形）：
   ① UpReqAlign.v L1122（ReqNaturalGradient 节 Hypothesis 位）：
        req_square_nonneg : forall a : R, le zero (mult a a)
      直接使用 = req_fisher_zero_implies_pointwise @L1140（逐点非负桥 + 零和分解）。
   ② UpReqDist.v L969（req_group_variance_le_raw_second_moment 定理首参显式位）：
        (forall a : R, le zero (mult a a)) ->
        le req_group_variance (mult (inv_pos …) req_group_raw_second_moment)
   ----------------------------------------------------------------
   数学路线判读（侦察定案）：
   1. 槽形的 le 在 Real 实例（RealEnhancedReal）下展开 = real_le x y :=
      Or (real_lt x y) (real_eq x y)——析取强序（CW_ConstructiveWorld_219 L3521）。
      plain 形 `le zero (t·t)` 在柯西层构造性不可证：它要求对任意 t 给出
      「t·t 严格正（带正下界见证）或 t·t == 0」的析取判定，等价于
      零分离判定；对收敛速率未知的柯西序列不可构造（普查 L375 GX 判定
      「实数序判定性不可证；只能保留显式参或改 eps 近似形」同款）。
      先例：CW_ConstructiveWorld_219 接口全部非严格非负字段 abs_nonneg / pos_part_nonneg /
      metric_pos / log_le_linear_eps 均取逐 eps Bishop 形（E152-5：
      real_le 析取形无法表达「不趋近」等号点）；real_square_nonneg_eps
      @L44842 也只给出逐 eps 形。
   2. 普查 G2 引擎 UpRealLeB.real_square_nonneg_B@424 形状 =
      real_le_b real_zero (t·t)（forall eps>0, real_lt zero (t²+eps) 弱序）；
      单向桥 real_le_to_le_b @UpRealLeB:78 方向为 real_le ⟹ real_le_b，
      反向不可导——故 plain 槽不可由在盘引擎直放（精确阻塞裁决见尾注）。
   3. 本文件给出（使用件本体不動，证明实例件与之并存）：
      [证明引理·保底] sqp_square_nonneg_eps —— 接口逐 eps Bishop 形
        （le/mult/plus/zero/lt 全接口投影，直连 CW_ConstructiveWorld_219 real_square_nonneg_eps，
        δ 透明同形映射， 模板②手法 = UpReqU2 log_req_compat_real 同款）。
      [辅件] sqp_opp_le_of_plus_nonneg —— le zero (a+eps) ⟹ opp a ≤ eps
        （Real 层；req_opp_plus 为 Real 层在盘件，抽象接口无 opp 对 plus
        分配字段，抽象层同形件不可导——次级发现，见尾注）。
      [主件·真证明] sqp_group_variance_le_raw_second_moment_eps_real ——
        使用②的 Real 实例逐 eps 升级形：逐 eps 平方非负传入，得
        var ≤ (1/G)·Σr² + eps（∀eps>0，Bishop 形），不经阻塞槽。
      [保底·参数位隔离实例化] sqp_fisher_zero_implies_pointwise_real /
        sqp_group_variance_le_raw_second_moment_real —— 两使用定理的
        @ 全显节参数 Real 实例化形态，唯一余留前提即槽本身
        （forall a : Real, le zero (mult a a)）；柯西层 plain 件一旦在盘
        （口径决策后），证明 = 单参传入一行。
   ----------------------------------------------------------------
   边界与判定（诚实账）：
   - plain 槽在 Real 层不可证明（构造性判定性阻塞，非缺件可拼）；
   - 抽象接口层亦不可导：接口缺序二分字段（Or (le zero t) (lt t zero)，
     序三分律片段，基座已明移除）且缺 opp 分配字段（req_opp_plus 仅
     Real 层在盘）——两条抽象导出路线均断；
   - 零新假设、零经典规则；全部语句 Set 层（le/req/lt 均 Set 值）。 *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqAlign.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 件1（证明引理·保底）：Real 层平方非负，接口逐 eps Bishop 形        *)
(*   与接口自身非负字段（abs_nonneg 等）同款形态；直连             *)
(*   CW_ConstructiveWorld_219 real_square_nonneg_eps（real_le/real_mult 具体层同形）。*)
(* ============================================================ *)
Lemma sqp_square_nonneg_eps : forall (t eps : Real),
  lt zero eps -> le zero (plus (mult t t) eps).
Proof.
  intros t eps Heps.
  exact (real_square_nonneg_eps t eps Heps).
Qed.

(* ============================================================ *)
(* 件1a（辅件）：le zero (a+eps) ⟹ opp a ≤ eps（Real 层）。        *)
(*   主件所需的序代数桥：−μ² ≤ eps ⟺ 0 ≤ μ²+eps。                  *)
(* ============================================================ *)
Lemma sqp_opp_le_of_plus_nonneg : forall (a eps : Real),
  le zero (plus a eps) -> le (opp a) eps.
Proof.
  intros a eps H1.
  apply (le_id_r (opp a) (plus zero eps) eps).
  - (* req (plus zero eps) eps：comm + plus_zero *)
    apply (req_trans (plus zero eps) (plus eps zero) eps).
    + apply plus_comm.
    + apply plus_zero.
  - (* le (opp a) (plus zero eps) *)
    apply (le_id_l (opp a)
                   (plus (plus (opp a) (opp eps)) eps)
                   (plus zero eps)).
    + (* req (opp a) (plus (plus (opp a) (opp eps)) eps) *)
      apply (req_trans (opp a) (plus (opp a) (plus (opp eps) eps))
                       (plus (plus (opp a) (opp eps)) eps)).
      * (* req (opp a) (plus (opp a) (plus (opp eps) eps))：
           opp a == opp a + 0 == opp a + (opp eps + eps) *)
        apply (req_trans (opp a) (plus (opp a) zero)
                         (plus (opp a) (plus (opp eps) eps))).
        -- exact (req_sym (plus (opp a) zero) (opp a) (plus_zero (opp a))).
        -- apply (req_plus_compat (opp a) (opp a) zero (plus (opp eps) eps)).
           ++ apply req_refl.
           ++ (* req zero (plus (opp eps) eps) *)
              apply (req_trans zero (plus eps (opp eps)) (plus (opp eps) eps)).
              ** exact (req_sym (plus eps (opp eps)) zero (plus_opp eps)).
              ** apply plus_comm.
      * (* assoc 重排：plus (opp a) (plus (opp eps) eps)
           == plus (plus (opp a) (opp eps)) eps *)
        exact (plus_assoc (opp a) (opp eps) eps).
    + (* le (plus (plus (opp a) (opp eps)) eps) (plus zero eps)：
         −(a+eps) ≤ −0 加 eps 保序，两端 req 转换 *)
      apply (le_plus_compat (plus (opp a) (opp eps)) zero eps eps).
      * (* le (plus (opp a) (opp eps)) zero *)
        apply (le_id_l (plus (opp a) (opp eps)) (opp (plus a eps)) zero).
        -- exact (req_sym (opp (plus a eps)) (plus (opp a) (opp eps))
                    (req_opp_plus a eps)).
        -- apply (le_id_r (opp (plus a eps)) (opp zero) zero).
           ++ exact reqd_opp_zero.
           ++ apply (opp_le_compat zero (plus a eps)). exact H1.
      * apply le_refl.
Qed.

(* ============================================================ *)
(* 件2（主件·真证明）：group_variance ≤ (1/G)·Σr² 的 Real 实例      *)
(*   逐 eps 升级形（不经阻塞槽）。                                  *)
(*   数学：var == X − μ²（req_group_variance_identity）+ 0 ≤ μ²+eps  *)
(*   （件1 喂 μ）⟹ X − μ² ≤ X + eps ⟹ var ≤ X + eps。               *)
(* ============================================================ *)
Lemma sqp_group_variance_le_raw_second_moment_eps_real :
  forall (Group : Set) (group_enum : list Group)
         (group_size_pos : lt zero (reqd_of_nat (reqd_group_size Group group_enum)))
         (reward_group : Group -> Real) (eps : Real),
    lt zero eps ->
    le (req_group_variance Group group_enum group_size_pos reward_group)
       (plus (mult (inv_pos (reqd_of_nat (reqd_group_size Group group_enum))
                             group_size_pos)
                   (req_group_raw_second_moment Group group_enum reward_group))
             eps).
Proof.
  intros Group group_enum group_size_pos reward_group eps Heps.
  apply (le_id_l (req_group_variance Group group_enum group_size_pos reward_group)
                 (req_minus (mult (inv_pos (reqd_of_nat (reqd_group_size Group group_enum))
                                        group_size_pos)
                                  (req_group_raw_second_moment Group group_enum reward_group))
                            (mult (req_group_mean Group group_enum group_size_pos reward_group)
                                  (req_group_mean Group group_enum group_size_pos reward_group)))
                 (plus (mult (inv_pos (reqd_of_nat (reqd_group_size Group group_enum))
                                        group_size_pos)
                             (req_group_raw_second_moment Group group_enum reward_group))
                       eps)).
  - exact (req_group_variance_identity
             Group group_enum group_size_pos reward_group).
  - (* X − μ² ≤ X + eps ⟸ μ ≤ 转换链 *)
    unfold req_minus.
    apply (le_plus_compat (mult (inv_pos (reqd_of_nat (reqd_group_size Group group_enum))
                                      group_size_pos)
                                (req_group_raw_second_moment Group group_enum reward_group))
                          (mult (inv_pos (reqd_of_nat (reqd_group_size Group group_enum))
                                         group_size_pos)
                                (req_group_raw_second_moment Group group_enum reward_group))
                          (opp (mult (req_group_mean Group group_enum group_size_pos reward_group)
                                     (req_group_mean Group group_enum group_size_pos reward_group)))
                          eps).
    + apply le_refl.
    + (* opp μ² ≤ eps ⟸ 0 ≤ μ² + eps（件1 直接喂 μ） *)
      apply (sqp_opp_le_of_plus_nonneg
               (mult (req_group_mean Group group_enum group_size_pos reward_group)
                     (req_group_mean Group group_enum group_size_pos reward_group))
               eps).
      exact (sqp_square_nonneg_eps
               (req_group_mean Group group_enum group_size_pos reward_group)
               eps Heps).
Qed.

(* ============================================================ *)
(* 件3（保底·参数位隔离实例化）：fisher 使用件 req_fisher_zero_implies_ *)
(*   pointwise（UpReqAlign L1140）的 @ 全显节参数 Real 实例化形态。   *)
(*   唯一余留前提 = 槽本身（forall a : Real, le zero (mult a a)）；   *)
(*   柯西层 plain 件在盘后证明 = 该参数单喂一行。                    *)
(* ============================================================ *)
Lemma sqp_fisher_zero_implies_pointwise_real :
  forall (S Theta : Set) (sumf : (S -> Real) -> Real),
    (forall f : S -> Real,
       (forall s : S, le zero (f s)) ->
       req (sumf f) zero -> forall s : S, req (f s) zero) ->
    (forall a : Real, le zero (mult a a)) ->
    forall (p_theta : Theta -> S -> Real)
           (partial : (Theta -> Real) -> Theta -> Real)
           (p_theta_pos : forall (theta : Theta) (s : S), lt zero (p_theta theta s)),
      forall theta : Theta,
        req (fisher_info_scalar_req S sumf Theta p_theta partial p_theta_pos theta)
            zero ->
        forall s : S,
          req (mult (p_theta theta s)
                    (mult (partial (fun th : Theta => log (p_theta th s) (p_theta_pos th s)) theta)
                          (partial (fun th : Theta => log (p_theta th s) (p_theta_pos th s)) theta)))
              zero.
Proof.
  intros S Theta sumf Hsumz Hsq p_theta partial p_theta_pos.
  exact (@req_fisher_zero_implies_pointwise Real RealEnhancedReal S sumf Hsumz Hsq
           Theta p_theta partial p_theta_pos).
Qed.

(* ============================================================ *)
(* 件4（保底·参数位隔离实例化）：group_variance 使用件                  *)
(*   req_group_variance_le_raw_second_moment（UpReqDist L965）的      *)
(*   @ 全显节参数 Real 实例化形态；余留前提同 = 槽本身。              *)
(* ============================================================ *)
Lemma sqp_group_variance_le_raw_second_moment_real :
  forall (Group : Set) (group_enum : list Group)
         (group_size_pos : lt zero (reqd_of_nat (reqd_group_size Group group_enum)))
         (reward_group : Group -> Real),
    (forall a : Real, le zero (mult a a)) ->
    le (req_group_variance Group group_enum group_size_pos reward_group)
       (mult (inv_pos (reqd_of_nat (reqd_group_size Group group_enum)) group_size_pos)
             (req_group_raw_second_moment Group group_enum reward_group)).
Proof.
  intros Group group_enum group_size_pos reward_group Hsq.
  exact (@req_group_variance_le_raw_second_moment Real RealEnhancedReal
           Group group_enum group_size_pos reward_group Hsq).
Qed.

(* ============================================================ *)
(* 尾注：精确阻塞裁决（兜底账）                                       *)
(* ---------------------------------------------------------------- *)
(* 阻塞点（唯一）：槽形 forall a, le zero (mult a a) 的柯西层 plain 件。 *)
(* 1. 接口侧：RealInterfaceEnhancedSetoid 的非严格 le 为析取强序        *)
(*    （Real 实例：Or real_lt real_eq），导出 plain 平方非负需序二分    *)
(*    字段 Or (le zero t) (lt t zero)——序三分律片段，基座明移除         *)
(*    （L193 注），不可增；且接口无 opp 分配字段（req_opp_plus 仅       *)
(*    Real 层在盘，UpReqAlgebra L167），抽象层连件1a 同形桥都不可导。    *)
(* 2. 柯西侧：real_le 的 Or 形使 plain 件等价零分离判定（收敛速率未知   *)
(*    的柯西序列上不可构造）；在盘最近件 = real_square_nonneg_eps       *)
(*    （CW_ConstructiveWorld_219 L44842，逐 eps）/ real_square_nonneg_B（UpRealLeB L424，  *)
(*    le_b 弱形）；real_le_to_le_b 桥单向（le⟹le_b），反向缺口。        *)
(* 3. 解堵路线（归主会话口径决策，本文件不强造）：                        *)
(*    a. 槽语句逐 eps 化：square_nonneg ⟦forall eps, lt zero eps ->     *)
(*       le zero (plus (mult a a) eps)⟧——件1 即证明引理，两使用件随      *)
(*       逐 eps 改述全放（使用②的改述形态 = 件2 已示范）；              *)
(*    b. 槽语句 le_b 化（普查 L375 G06_BForm 路线）——               *)
(*       UpRealLeB.real_square_nonneg_B 直接提供；                          *)
(*    c. 维持诚实 Variable 位（与 Id 系 L24301 同判定）。               *)
(* 本文件对两使用定理本体零改动（使用件本体不動）；件2 与件3/件4 并存。  *)
(* ============================================================ *)

(* ======== G09_MiscSmall 成员件：UpReqOrderArgmin（原样并入，自带 Require）======== *)
(* UpReqOrderArgmin.v — 签名迁移批 5 波 4 桥模块 C1：reqDecidableOrder 同构假设类
   + reqArgmin 归纳机 + argmin 簇 (c) 5 件 req 平移。
   工作单：attn\基建层处置清单.md /(c) 桥C1（§0.3 / §7.3 / §7.9 / §8 / §9.2）。
   源文件：CW_ConstructiveWorld_219：
     Class DecidableOrder          L331-337（字段面 5 槽，: Set）
     Section ArgminCorrectness     L15288-15425（argmin_aux 系；节参数 Context {DO} L15290）
     SLM argmin 子节               L2426-2560（argmin_aux_token 系；Context {DO} L2426）
   上游：CW_ConstructiveWorld_219 基座（RealInterfaceEnhancedSetoid 接口字段直引：le/lt/req/le_trans/
   le_refl/lt_le_iff/req_le_compat）；UpReqAlgebra 按需——argmin 簇字段面全在基座
   接口，本件未使用故未 Require。未使用的 5 件（UpReqSLM/UpReqCauchy/UpReqMisc5/
   UpEntropyGainReq/UpReqAlign3）零 Require；假设位组同类文字对齐自持。
   ----------------------------------------------------------------
   桥设计（T2①：Class 参数位非公理——reqDecidableOrder 为 Class 定义，使用节以
   Context {DO : reqDecidableOrder R RIS} 引入，End 时作显式参入闭包签名，
   Print Assumptions 仍 Closed。E225 判定：DecidableOrder=整体三分律=LPO 等价、
   全库零 Instance——req 类同为永久假设类，不供 Instance，与 Id 同构）。
   字段面逐字段核对（Id L331-337 → 本类；等词位 Id→req）：
     ord_le_dec    L332  Or (le a b) (Not (le a b))    → rord_le_dec    （逐字同形）
     lt_dec        L333  Or (lt a b) (Or (Id a b) ..) → rlt_dec        （中支 Id→req；
                                          RestB req_lt_dec L446 同款签名差异登记表）
     eq_dec        L334  Or (Id a b) (Not (Id a b))   → rreq_dec       （Id→req）
     not_le_lt     L335  Not (le a b) -> lt b a       → rnot_le_lt     （逐字同形）
     lt_le_iff_dec L336  Or (lt a b) (Id a b) -> le   → rlt_le_iff_dec （Id→req；
                                          req 形即接口字段 lt_le_iff 同语句）
   ----------------------------------------------------------------
   给出核对（清单 (c) 5 件，行号逐件在表）：
     req_argmin_aux_token_min             ← argmin_aux_token_min        L2481（SLM §7.3）
     req_pick_best_token_optimal          ← pick_best_optimal           L2545（SLM §7.3）
     req_argmin_aux_correct               ← argmin_aux_correct          L15315（Argmin §7.9）
     req_pick_best_is_minimal             ← pick_best_is_minimal        L15377（Argmin §7.9）
     req_dynamics_greedy_locally_optimal  ← dynamics_greedy_locally_optimal L15407（§7.9）
   机器 2 枚（清单 L144/L315 判定「随桥C1 定位可转定义级 (b)」兑现——snd 伴件
   的 req 等词改述版归纳机，零 Leibniz 面逐字：Id 系逐处 Hsnd 等词换形 → req 系
   沿接口 Proper 字段 req_le_compat 运输 le 语句，纯 term）：
     req_argmin_aux_token_snd_req         ← argmin_aux_token_snd_correct L2517（改述）
     req_argmin_aux_snd_req               ← argmin_aux_snd_correct       L15352（改述）
   ----------------------------------------------------------------
   (d) 冻结清单（零证明行，见文件尾注记）：InT_head_extend L2451 /
   argmin_aux_token_mem L2461 / argmin_aux_token_snd_correct L2517（Id 形不迁，
   req 形机已转 (b) 入上表）/ pick_best_in_vocab' L2531 / pick_best_in_vocab L2575 /
   argmin_aux_snd_correct L15352（同前）。
   纪律：纯构造性；Set 层语句（le/lt/req/Or/And 全基座 Set 形连接词 L65-70）；
   纯 term-mode（apply/exact/destruct/inversion/specialize/unfold），零依赖改写器；
   核心件 Qed。G3 提取检验独立文件（验后删）。 *)

Require Import CW_ConstructiveWorld_219.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 桥 C1 本体 1：reqDecidableOrder——Id DecidableOrder L331-337     *)
(*   的 req 同构假设类（T2① Class 参数位非公理；全库零 Instance      *)
(*   与 Id 同判——E225 LPO 判定随桥注记）                          *)
(* ============================================================ *)
Class reqDecidableOrder (R : Set) (RIS : RealInterfaceEnhancedSetoid R) : Set := {
  rord_le_dec : forall a b : R, Or (le a b) (Not (le a b));
  rlt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a));
  rreq_dec : forall a b : R, Or (req a b) (Not (req a b));
  rnot_le_lt : forall a b : R, Not (le a b) -> lt b a;
  rlt_le_iff_dec : forall a b : R, Or (lt a b) (req a b) -> le a b
}.

(* ============================================================ *)
(* reqArgmin 机·SLM 支（基座 SLM argmin 子节 L2426-2560 同构；      *)
(*   只建 (c) 2 件与使用面机器，(d) 5 件冻结承担不触及）            *)
(* ============================================================ *)
Section ReqArgminTokenWorld.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {DO : reqDecidableOrder R RIS}.

(* ---- 接口假设（L2035 区同构子集：本 2 件使用面，vocab_nonempty
     不入——pick_best 系两件零使用，诚实边界注记） ---- *)
Variable Token : Set.
Variable vocab : list Token.
Variable total_loss : list Token -> R.
Variable default_token : Token.

(* 基座 candidate_token L2432 同形 *)
Definition req_candidate_token : Set := (Token * R)%type.

(* 基座 argmin_aux_token L2434-2444 同形（判定槽 = rord_le_dec） *)
Fixpoint req_argmin_aux_token (prefix : list Token) (l : list Token)
         (best : req_candidate_token) : req_candidate_token :=
  match l with
  | nil => best
  | w :: rest =>
      let loss_w := total_loss (prefix ++ [w]) in
      match rord_le_dec loss_w (snd best) with
      | inl _ => req_argmin_aux_token prefix rest (w, loss_w)
      | inr _ => req_argmin_aux_token prefix rest best
      end
  end.

(* 基座 pick_best_token L2446-2452 同形 *)
Definition req_pick_best_token (prefix : list Token) : Token :=
  match vocab with
  | nil => default_token
  | w0 :: rest =>
      fst (req_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0])))
  end.

(* 基座 argmin_aux_token_min L2481（(c) 件 1）：遍历正确性——snd 不增
   （第二分量）+ 对 l 内逐项最小（第一分量）。归纳 + rord_le_dec 分支 +
   rnot_le_lt/lt_le_iff 反向支，逐位同构 Id 机。 *)
Lemma req_argmin_aux_token_min : forall prefix l best_token best_loss,
  And (forall w : Token, InT w l ->
    le (snd (req_argmin_aux_token prefix l (best_token, best_loss)))
       (total_loss (prefix ++ [w])))
      (le (snd (req_argmin_aux_token prefix l (best_token, best_loss))) best_loss).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss.
  - (* nil：左分量空域真 + le_refl（空支以 inversion 闭合——提取零 Obj.magic，
       既往过程档案 行 101 同坑：空支 match 字面会落 Obj.magic） *)
    assert (Hempty : forall w : Token, InT w nil ->
      le (snd (req_argmin_aux_token prefix nil (best_token, best_loss)))
         (total_loss (prefix ++ [w]))).
    { intros w HIn. inversion HIn. }
    exact (pair Hempty (le_refl _)).
  - simpl.
    destruct (rord_le_dec (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + (* 换 a：IH 于新 best (a, loss a)；snd ≤ loss a（IH 左腿），传 le_trans 配 Hle *)
      destruct (IH a (total_loss (prefix ++ [a]))) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- exact IH_le.
        -- exact (IH_min w Hw).
      * exact (le_trans _ (total_loss (prefix ++ [a])) _ IH_le Hle).
    + (* 保留 best：rnot_le_lt 升严格序 + lt_le_iff 回 le；逐项走 IH *)
      destruct (IH best_token best_loss) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- assert (Hlt : lt best_loss (total_loss (prefix ++ [a])))
             by exact (rnot_le_lt (total_loss (prefix ++ [a])) best_loss Hnot).
           exact (le_trans _ best_loss _ IH_le (lt_le_iff _ _ (inl Hlt))).
        -- exact (IH_min w Hw).
      * exact IH_le.
Qed.

(* 机器：基座 argmin_aux_token_snd_correct L2517 的 req 等词改述版（清单 L144
   「随桥C1 定位可转定义级 (b)」兑现）。基例与归纳步全为转换级：req_argmin_aux
   的递归分支两侧 fst/snd 同源， premise req 等词沿归纳原样传——零 Leibniz 面。 *)
Lemma req_argmin_aux_token_snd_req : forall prefix l best_token best_loss,
  req best_loss (total_loss (prefix ++ [best_token])) ->
  req (snd (req_argmin_aux_token prefix l (best_token, best_loss)))
      (total_loss (prefix ++ [fst (req_argmin_aux_token prefix l (best_token, best_loss))])).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss Hinit.
  - exact Hinit.
  - simpl.
    destruct (rord_le_dec (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + exact (IH a (total_loss (prefix ++ [a])) (req_refl _)).
    + exact (IH best_token best_loss Hinit).
Qed.

(* 基座 pick_best_optimal L2545（(c) 件 2）：pick_best 扩展损失 ≤ 任意
   w ∈ vocab 的。Id 系逐处 Leibniz Hsnd 换形 → req 系 req_le_compat（接口
   Proper 字段）沿 req 等词运输 le 语句，纯 term。 *)
Theorem req_pick_best_token_optimal : forall prefix w,
  InT w vocab ->
  le (total_loss (prefix ++ [req_pick_best_token prefix]))
     (total_loss (prefix ++ [w])).
Proof.
  intros prefix w Hw.
  unfold req_pick_best_token.
  destruct vocab as [| w0 rest].
  - inversion Hw.
  - destruct (req_argmin_aux_token_min prefix rest w0
                (total_loss (prefix ++ [w0]))) as [Hmin Hle].
    assert (Hsnd : req (snd (req_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [fst (req_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0])))])))
      by exact (req_argmin_aux_token_snd_req prefix rest w0
                  (total_loss (prefix ++ [w0])) (req_refl _)).
    inversion Hw as [Hw0 | y0 l0 Hwrest]; subst.
    + (* w = w0：snd ≤ loss w0（第二分量）沿 Hsnd 换形 *)
      exact (req_le_compat _ _ _ _ Hsnd (req_refl _) Hle).
    + (* w ∈ rest：逐项最小性沿 Hsnd 换形 *)
      exact (req_le_compat _ _ _ _ Hsnd (req_refl _) (Hmin w Hwrest)).
Qed.

End ReqArgminTokenWorld.

(* ============================================================ *)
(* reqArgmin 机·ArgminCorrectness 支（基座 L15288-15425 同构；      *)
(*   (c) 3 件 + 使用面机器，(d) 1 件冻结承担不触及）                *)
(* ============================================================ *)
Section ReqArgminWorld.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {DO : reqDecidableOrder R RIS}.

Variable Token : Set.
Variable total_loss : list Token -> R.

(* 基座 candidate L15301 同形 *)
Definition req_candidate : Set := (Token * R)%type.

(* 基座 argmin_aux L15303-15313 同形 *)
Fixpoint req_argmin_aux (prefix : list Token) (l : list Token)
         (best : req_candidate) : req_candidate :=
  match l with
  | nil => best
  | w :: rest =>
      let loss_w := total_loss (prefix ++ [w]) in
      match rord_le_dec loss_w (snd best) with
      | inl _ => req_argmin_aux prefix rest (w, loss_w)
      | inr _ => req_argmin_aux prefix rest best
      end
  end.

(* 基座 argmin_aux_correct L15315（(c) 件 3）：snd ≤ 初值 + 对 l 内逐项
   最小。归纳 + rord_le_dec 分支 + rnot_le_lt/lt_le_iff 反向支。 *)
Lemma req_argmin_aux_correct :
  forall prefix l best_token best_loss,
    let result := req_argmin_aux prefix l (best_token, best_loss) in
    And (le (snd result) best_loss)
        (forall w : Token, InT w l ->
          le (snd result) (total_loss (prefix ++ [w]))).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss.
  - simpl. split.
    + apply le_refl.
    + intros w HIn. inversion HIn.
  - simpl.
    destruct (rord_le_dec (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + specialize (IH a (total_loss (prefix ++ [a]))).
      destruct IH as [IH_le IH_min].
      split.
      * exact (le_trans _ (total_loss (prefix ++ [a])) _ IH_le Hle).
      * intros w HIn.
        inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- exact IH_le.
        -- exact (IH_min w Hw).
    + specialize (IH best_token best_loss).
      destruct IH as [IH_le IH_min].
      split.
      * exact IH_le.
      * intros w HIn.
        inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- assert (Hlt : lt best_loss (total_loss (prefix ++ [a])))
             by exact (rnot_le_lt (total_loss (prefix ++ [a])) best_loss Hnot).
           exact (le_trans _ best_loss _ IH_le (lt_le_iff _ _ (inl Hlt))).
        -- exact (IH_min w Hw).
Qed.

(* 机器：基座 argmin_aux_snd_correct L15352 的 req 等词改述版（清单 L315
   「随桥C1 定位可转定义级 (b)」兑现；同 token 支机，零 Leibniz 面）。 *)
Lemma req_argmin_aux_snd_req : forall prefix l best_token best_loss,
  req best_loss (total_loss (prefix ++ [best_token])) ->
  req (snd (req_argmin_aux prefix l (best_token, best_loss)))
      (total_loss (prefix ++ [fst (req_argmin_aux prefix l (best_token, best_loss))])).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss Hinit.
  - exact Hinit.
  - simpl.
    destruct (rord_le_dec (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + exact (IH a (total_loss (prefix ++ [a])) (req_refl _)).
    + exact (IH best_token best_loss Hinit).
Qed.

Variable vocab : list Token.
Variable default_token : Token.

(* 基座 pick_best L15363-15369 同形 *)
Definition req_pick_best (prefix : list Token) : Token :=
  match vocab with
  | nil => default_token
  | w0 :: rest =>
      fst (req_argmin_aux prefix rest (w0, total_loss (prefix ++ [w0])))
  end.

(* 基座 pick_best_is_minimal L15377（(c) 件 4）：使用 argmin_aux_correct +
   snd 机（Id 系在 snd 等词伴件上做目标换形一处，req 侧改走 req_le_compat
   运输——清单 L316 判定的 req 落实）。 *)
Theorem req_pick_best_is_minimal :
  forall prefix w,
    InT w vocab ->
    le (total_loss (prefix ++ [req_pick_best prefix])) (total_loss (prefix ++ [w])).
Proof.
  intros prefix w HIn.
  unfold req_pick_best.
  destruct vocab as [| w0 rest].
  - inversion HIn.
  - destruct (req_argmin_aux_correct prefix rest w0
                (total_loss (prefix ++ [w0]))) as [Hbest Hmin].
    assert (Hsnd : req (snd (req_argmin_aux prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [fst (req_argmin_aux prefix rest (w0, total_loss (prefix ++ [w0])))])))
      by exact (req_argmin_aux_snd_req prefix rest w0
                  (total_loss (prefix ++ [w0])) (req_refl _)).
    inversion HIn as [Hw_eq | y0 l0 Hwrest]; subst.
    + (* w = w0：snd ≤ loss w0（Hbest 第一分量）沿 Hsnd 换形 *)
      exact (req_le_compat _ _ _ _ Hsnd (req_refl _) Hbest).
    + (* w ∈ rest：逐项最小性（Hmin）沿 Hsnd 换形 *)
      exact (req_le_compat _ _ _ _ Hsnd (req_refl _) (Hmin w Hwrest)).
Qed.

(* 基座 dynamics L15372-15374 同形（贪心动力学：追加 pick_best） *)
Definition req_dynamics (s : list Token) : list Token :=
  s ++ [req_pick_best s].

(* 基座 dynamics_greedy_locally_optimal L15407（(c) 件 5，别名件）：
   req_pick_best_is_minimal 经 req_dynamics 展开直接给出。 *)
Theorem req_dynamics_greedy_locally_optimal :
  forall prefix w,
    InT w vocab ->
    le (total_loss (req_dynamics prefix)) (total_loss (prefix ++ [w])).
Proof.
  intros prefix w HIn.
  unfold req_dynamics.
  exact (req_pick_best_is_minimal prefix w HIn).
Qed.

End ReqArgminWorld.

(* ---- (d) 冻结清单（清单 §7.3 L141/L142/L144/L145/L147 + §7.9 L315 判定；
     nat/list 层 Id 机器与 Leibniz 等词伴件，零证明行） ----
   InT_head_extend（CW_ConstructiveWorld_219 L2451）/ argmin_aux_token_mem（L2461）/
   pick_best_in_vocab'（L2531）/ pick_best_in_vocab（L2575）/
   argmin_aux_token_snd_correct（L2517）/ argmin_aux_snd_correct（L15352）。
   前四件：list 载体 Id 机器（规划书 §1.1 边界 2；跨接口复用口径同清单 §7.12
   grpo_count_one 使用 count 机先例）。后两件：Id 形不迁；其使用面由本件 req
   等词改述机 req_argmin_aux_token_snd_req / req_argmin_aux_snd_req（清单 L144/
   L315「随桥C1 定位可转定义级 (b)」注记兑现）+ 接口字段 req_le_compat 运输承担。 *)
