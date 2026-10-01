(* ============================================================
   使命：本件数学使命叙述见下方原头注首段（既有件注记型头注整编尚待后续）。
   依赖：见原头注 Require 面与依赖段。
   对标：见原头注来源/对标行。
   构造性：纯构造性、零承认件（详见原头注红线自审段）。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)
(* G 组：G06_BForm — 有限合并组（S/G 双系新命名，成员原样并入）
   成员：UpReqPPOB + UpReqSumB + UpReqMinPProjB + UpReqLatticeB（同组旧名 Require 已剥；库内旧名已消融，下游直接 Require 本组）*)
(* ======== G06_BForm 成员件：UpReqPPOB（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqPPOB.v —— 定理 6.6 对应物判定 5 升格模块：ppo 保守性 Bishop 完整形 *)
(*   （B 形扩展建造队列  模块 · 侦察规格单目标 2 ·）        *)
(* 主件 real_ppo_conservative_B_full：Σ π_old·min(r,clip r)·adv ≤_B    *)
(*   Σ π_old·r·adv——UpRealLeB.v 有条件件 real_ppo_conservative_B 的     *)
(*   唯一缺口前提「E>0 显式证书」自  模块前提弱化（）起为聚合正   *)
(*   前提直供：Hypothesis 位 lebR_res_weight_pos : real_lt zero E（E :=   *)
(*   Σ π_old·adv，聚合正），闭合组合器用法=前提直接提供（apply 行零改动）——      *)
(*   旧 sum_pos 槽 rplb_sum_pos 与内机导出链（逐点双正两喂→槽提升）整体  *)
(*   退场。主件证明体与 Part C 同构：closure_b 闭合组合器 + res_fold 出节件  *)
(*   + eps 形源件直连（13 参全显）。                                     *)
(* 判定校注（上游注册项 注册项复核，）：逐点 advantage_pos 前提     *)
(*   **不可删**——eps 形源件 real_ppo_conservative_eps（S08 L2342）在     *)
(*   real_le_mult_compat 位逐点使用之（S08 L2367），仅聚合正时主件结论   *)
(*   为假（模型反例：S={1,2}、π≡1、adv=(0.2,−0.1)、r=(1.2,5)、εc=0.1     *)
(*   ⟹ E=0.1>0 而 Σ(r−min(r,clip))·adv = 0.02−0.39 < 0，LHS>RHS）；      *)
(*   故弱化只达证书轴（参数位→聚合正），逐点轴维持照抄源件不变。           *)
(* 红线自审：real_le_b Set 值 forall 型、real_lt sigT Set 层零 Prop 泄露； *)
(*   前提位 pi_old_pos/advantage_pos 照抄源件零新增；纯项模式（real_eq 非  *)
(*   Id 禁改写全链显式组装）；三件全闭合，证据=尾注三连打（日志在案）。     *)
(* ============================================================ *)
From Stdlib Require Import QArith.Qring.
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
Require Import UpRealLeB.
Section RealPPOLeBFull.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
(* 诚实接口：标量提取（Part C 同位复刻） *)
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
           (real_mult a (real_sum_over_S f)).
(* T2① 求和正性槽（显式参位）已随  前提弱化（）退场：
   聚合正 E>0 直升 Hypothesis 位（见 lebR_res_weight 定义后），不再经
   「逐点正 ⟹ 和正」参数位中转。 *)
Variable real_pi_star_ : S -> Real.
Variable real_pi_old : S -> Real.
Variable real_pi_old_pos : forall s : S, real_lt real_zero (real_pi_old s).
Variable real_advantage_fn : S -> Real.
Variable real_advantage_pos : forall s : S, real_lt real_zero (real_advantage_fn s).
Variable epsilon : Real.
(* 残差权系数 E := Σ π_old·adv（Part C 同位定义，与出节件定义可转换） *)
Definition lebR_res_weight : Real :=
  real_sum_over_S (fun s : S => real_mult (real_pi_old s) (real_advantage_fn s)).

(* 聚合正前提（ 前提弱化）：E>0 由内机导出降为前提直供——
   主件闭合组合器用法 apply 行零改动，名字面不变，供给面由「槽+内机导出链」
   换为本 Hypothesis 位（显式参随节证明入出口签名，非全局无据项）。 *)
Hypothesis lebR_res_weight_pos : real_lt real_zero lebR_res_weight.
(* 主件：≤_B 完整形（与 Part C 有条件件同构，E>0 证书由聚合正前提直供） *)
Theorem real_ppo_conservative_B_full :
  real_le_b
    (real_sum_over_S (fun s : S =>
      real_mult (real_pi_old s)
        (real_mult (real_min (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                             (real_ppo_clip_ epsilon (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)))
                   (real_advantage_fn s))))
    (real_sum_over_S (fun s : S =>
      real_mult (real_pi_old s)
        (real_mult (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                   (real_advantage_fn s)))).
Proof.
  apply (real_le_closure_b _ _ lebR_res_weight lebR_res_weight_pos).
  intros eps Heps.
  apply (real_le_trans _
           (real_plus
              (real_sum_over_S (fun s : S =>
                 real_mult (real_pi_old s)
                   (real_mult (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                              (real_advantage_fn s))))
              (real_sum_over_S (fun s : S =>
                 real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))) _).
  - exact (real_ppo_conservative_eps S real_sum_over_S real_sum_over_S_ext
             real_sum_over_S_le real_sum_over_S_add real_pi_star_ real_pi_old
             real_pi_old_pos real_advantage_fn real_advantage_pos epsilon eps Heps).
  - apply (real_le_plus_compat _ _ _ _ (real_le_refl _)).
    apply (RealSetoid.real_eq_le _ _).
    exact (real_ppo_res_fold S real_sum_over_S real_sum_over_S_ext
             real_sum_over_S_linear real_pi_old real_advantage_fn eps).
Qed.
End RealPPOLeBFull.

(* 尾注：出口签名证明序检验打表在案（_wb17_sig_probe）；残差折叠
   real_ppo_res_fold 7 参、eps 形源件 13 参，均全参显喂。 *)
(*  尾注（）：lebR_res_weight_pos 自前提弱化起为节内
   Hypothesis 位，随节证明入主件出口签名（不再以独立常量出口），
   三连打改打主件/残差权定义/证明伴件三件。 *)
Print Assumptions real_ppo_conservative_B_full.
Print Assumptions lebR_res_weight.
(* 伴件 rplb_res_weight_pos_uncond / rplb_sum_pos_discharged 之打印
   在文末证明节后（定义位在后，此处不可引用）。 *)

(* ============================================================ *)
(* 证明节（假设位证明系列 #7 ·； 改注）：求和正性的      *)
(*   构造性载体件——原 rplb_sum_pos 槽随前提弱化退场后，本节作为「逐点    *)
(*   正 ⟹ 和正」在 list 载体上的独立构造真理存续（伴件改由本节直接       *)
(*   重构 E>0 载体面，不再经槽实例化）。                                 *)
(*   载体勘定：CW_ConstructiveWorld_219 RealListSumMain 节 real_list_sum（list Fixpoint， *)
(*   X 泛型，nil 支 real_zero）。语句形态按空支路裁决：空表支 sum 实为  *)
(*   real_zero，严格正不真——语句必带非空前提 Not (Id l nil)             *)
(*   （CW_ConstructiveWorld_219 sum_temp_positive 同款；判例 闭合组合器空支路判据同源）。      *)
(*   先件=求和正性语句的 list 载体实例（归纳真理两支：nil 矛盾直击、     *)
(*   cons real_plus_positive 两喂）；伴件以固定非空 vocab 无条件重构     *)
(*   E>0 载体面（π_old/adv 取常 real_one，证书 real_lt_zero_one，        *)
(*   CW_ConstructiveWorld_219 L39486）——出口零残留。                                     *)
(* ============================================================ *)
Section RplbSumPosDischarged.
Variable X : Set.

(* 证明件：有限和逐项正 ⟹ 和正（非空表前提；rplb_sum_pos 槽的载体实例） *)
Lemma rplb_sum_pos_discharged :
  forall (f : X -> Real) (l : list X),
    Not (Id l nil) ->
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum X f l).
Proof.
  intros f l.
  induction l as [| x rest IH]; intros Hnil Hpos.
  - (* 空表支：非空前提矛盾直击（sum 实为 real_zero，前提在案而真） *)
    contradiction Hnil. apply id_refl.
  - destruct rest as [| y rest'].
    + (* 单元素支：f x + 0 换形回 f x（real_plus_zero 经 real_lt_eq_lt） *)
      exact (real_lt_eq_lt real_zero (f x)
               (real_plus (f x) (real_list_sum X f nil))
               (Hpos x)
               (real_eq_sym (real_plus (f x) (real_list_sum X f nil)) (f x)
                  (real_plus_zero (f x)))).
    + (* 一般 cons 支：real_plus_positive 两喂——逐项正 + 尾表归纳正 *)
      apply (real_plus_positive (f x) (real_list_sum X f (y :: rest'))).
      * apply Hpos.
      * apply IH. intro Hc. inversion Hc. apply Hpos.
Qed.
End RplbSumPosDischarged.

(* 伴件（ 改建）：E>0 载体面的无条件重构——π_old/adv 取常      *)
(*   real_one，经先件（逐点双正 real_mult_positive 两喂 + 求和正性载体   *)
(*   件）直接给出，零依赖弱化后的前提位。 *)
Section RplbResWeightPosUncond.
Variable X : Set.
Variable vocab : list X.
Hypothesis vocab_nonempty : Not (Id vocab nil).

Definition rplb_sum_vocab (f : X -> Real) : Real := real_list_sum X f vocab.

Lemma rplb_res_weight_pos_uncond :
  real_lt real_zero
    (lebR_res_weight X rplb_sum_vocab (fun _ : X => real_one) (fun _ : X => real_one)).
Proof.
  unfold lebR_res_weight, rplb_sum_vocab.
  apply (rplb_sum_pos_discharged X
           (fun s : X => real_mult real_one real_one) vocab vocab_nonempty).
  intro s.
  exact (real_mult_positive real_one real_one real_lt_zero_one real_lt_zero_one).
Qed.
End RplbResWeightPosUncond.

Print Assumptions rplb_sum_pos_discharged.
Print Assumptions rplb_res_weight_pos_uncond.

(* ======== G06_BForm 成员件：UpReqSumB（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqSumB.v —— 逐点 ≤_B 求和提升模块（：real_list_sum_le_b_compat） *)
(*   任务来源：B形扩展建造队列.md 目标 3（两段给出：段1 长度机器    *)
(*   + 逐点基件；段2 nonneg 闭合组合器收尾 + 完整 compat 主件）。           *)
(*                                                                *)
(* 主结果（全部 Set 层、零 Prop 泄露、纯 term-mode 组装）：             *)
(*   段1 sumb_lenR：自持 Real 层列表长度机器（Fixpoint，nil→0、        *)
(*        cons→1+lenR rest）——免 nat 桥：CW_ConstructiveWorld_219 nat 嵌入系 AlgHelpers   *)
(*        节证明件，跨接口不可复用（冻结判定在案），本文件 Real 归纳      *)
(*        自持，零接口依赖。                                           *)
(*   段1 sumb_lenR_nonneg：0 ≤ lenR l（归纳 + 逐项非负加法兼容）。      *)
(*   段1 sumb_sum_const：Σ(常数 c) == lenR l·c（归纳；S 步 = 分布律     *)
(*        + 一元换形，与 lenR 定义步同构——求和面核心换形基础模块）。        *)
(*   段2 sumb_list_sum_le_b：主件——逐点 ≤_B ⟹ 求和 ≤_B（n 元 Bishop  *)
(*        求和面，Fubini 型逐点提升）。给 δ>0：逐点 ≤_B 展开取同一 δ    *)
(*        （免 1/n 拆分——Bishop 序全称面 n 份同 δ 即足，这是本件与      *)
(*        plain-eps 拆分链的本质区别）；逐点取 lt 支经 Or 编码单向桥    *)
(*        升 real_le，real_list_sum_le 保序提升；Σ(g+δ) 换形为          *)
(*        Σg + lenR·δ（add + sum_const 两步）；非负系数闭合组合器           *)
(*        （C:=lenR l，非负证书即段1 件）单步闭合。                     *)
(*                                                                *)
(* 使用面（全 Require 已认证 .vo，零改写上游）：                        *)
(*   CW_ConstructiveWorld_219 real_list_sum 引擎三件（L41491/41498/41543/41634，节证明    *)
(*   签名 X 首参——Check 检验实测）；UpRealLeB2 real_le_closure_b_nonneg *)
(*   （L102 非负系数闭合组合器）；RealSetoid 组合器面（lt_le_iff_req /      *)
(*   le_id_l / le_id_r / eq_plus_compat）。                            *)
(*                                                                *)
(* 红线：零公理零未闭合证明（G1 禁词全零）；Set 层语句（real_le_b      *)
(* 为 Set 值 forall 型，结论零 Prop 泄露）；纯 term-mode 显式组装      *)
(* （real_eq 非 Id，禁 rewrite，全链 real_eq_trans/compat）；全        *)
(* Qed. 闭合；新件 Print Assumptions Closed（文末）。                  *)
(*   邻模块编译期经负载闸自然排队，绑核 1）。                             *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
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
Require Import UpRealLeB.
Require Import UpRealLeB2.

(* ============================================================ *)
(* 段1 · S.1 自持长度机器：lenR（Real 层，免 nat 桥接口）               *)
(* ============================================================ *)

Fixpoint sumb_lenR (X : Type) (l : list X) : Real :=
  match l with
  | nil => real_zero
  | cons _ rest => real_plus real_one (sumb_lenR X rest)
  end.

(* ============================================================ *)
(* 段1 · S.2 长度非负：0 ≤ lenR l                                     *)
(*   归纳：cons 步 0 ≤ 1+lenR rest 经 (0+0 与 0 换形) + 逐项非负兼容。  *)
(* ============================================================ *)

Lemma sumb_lenR_nonneg : forall (X : Type) (l : list X),
  real_le real_zero (sumb_lenR X l).
Proof.
  intros X l. induction l as [| w rest IH]; simpl.
  - apply real_le_refl.
  - apply (RealSetoid.real_le_id_l (real_plus real_zero real_zero) real_zero
                                   (real_plus real_one (sumb_lenR X rest))).
    + apply real_plus_zero.
    + apply (real_le_plus_compat real_zero real_one real_zero (sumb_lenR X rest)).
      * exact (RealSetoid.real_lt_le_iff_req real_zero real_one (inl real_lt_zero_one)).
      * exact IH.
Qed.

(* ============================================================ *)
(* 段1 · S.3 常数和坍缩：Σ(常数 c) == lenR l·c                          *)
(*   归纳：cons 步 c + Σconst rest == c + lenR rest·c（IH）             *)
(*        == 1·c + lenR rest·c（一元换形）== (1+lenR rest)·c（分布律）。 *)
(* ============================================================ *)

Lemma sumb_sum_const : forall (X : Type) (c : Real) (l : list X),
  real_eq (real_list_sum X (fun _ : X => c) l) (real_mult (sumb_lenR X l) c).
Proof.
  intros X c l. induction l as [| w rest IH]; simpl.
  - (* 0 == 0·c：经 c·0 中项（mult_zero 零在右侧，comm 桥接） *)
    apply (real_eq_trans _ (real_mult c real_zero) _).
    + apply real_eq_sym. apply real_mult_zero.
    + apply real_mult_comm.
  - apply (real_eq_trans _
             (real_plus c (real_mult (sumb_lenR X rest) c)) _).
    + apply (RealSetoid.real_eq_plus_compat c
               (real_list_sum X (fun _ : X => c) rest)
               c
               (real_mult (sumb_lenR X rest) c)).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_eq_trans _
               (real_plus (real_mult real_one c)
                          (real_mult (sumb_lenR X rest) c)) _).
      * apply (RealSetoid.real_eq_plus_compat c
                 (real_mult (sumb_lenR X rest) c)
                 (real_mult real_one c)
                 (real_mult (sumb_lenR X rest) c)).
        -- (* c == 1·c：c·1 == c（mult_one 零在右侧）+ comm 桥 *)
           apply (real_eq_trans _ (real_mult c real_one) _).
           ++ apply real_eq_sym. apply real_mult_one.
           ++ apply real_mult_comm.
        -- apply real_eq_refl.
      * (* (1·c)+(lenR·c) == (1+lenR)·c：distrib_r 直连（方向同向，零翻转） *)
        apply real_distrib_r.
Qed.

(* ============================================================ *)
(* 段2 · S.4 主件：逐点 ≤_B 求和提升（n 元 Bishop 求和面）               *)
(*   sumb_list_sum_le_b：逐点 ≤_B ⟹ 求和 ≤_B。                          *)
(*   证明链（原始任务表述规格单闭合设计）：                                    *)
(*     给 δ>0：逐点 ≤_B 展开取同一 δ（免 1/n 拆分——real_le_b 全称面     *)
(*     n 份同 δ 即足）；逐点取 lt 支经 Or 编码单向桥升 real_le           *)
(*     （判定 2 边界内：Or 编码仅作单向桥使用）；real_list_sum_le 保序   *)
(*     提升：Σf ≤ Σ(g+δ)；Σ(g+δ) == Σg + Σ(常数 δ) == Σg + lenR·δ       *)
(*     （add + 段1 sum_const 两步换形）；非负系数闭合组合器单步闭合          *)
(*     （C := lenR l，非负证书 = 段1 lenR_nonneg）。                     *)
(* ============================================================ *)

Lemma sumb_list_sum_le_b : forall (X : Type) (f g : X -> Real) (l : list X),
  (forall w : X, real_le_b (f w) (g w)) ->
  real_le_b (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l H.
  (* 零 unfold：闭合组合器结论即 real_le_b 形直接匹配（外层 δ 全称面由器使用，
     逐点统一 eps 发生在器前提的全称位内） *)
  apply (real_le_closure_b_nonneg
           (real_list_sum X f l)
           (real_list_sum X g l)
           (sumb_lenR X l)).
  - (* 前提 1：0 ≤ C := lenR l（段1 件） *)
    apply sumb_lenR_nonneg.
  - (* 前提 2：∀eps>0, Σf ≤ Σg + lenR·eps *)
    intros eps Heps.
    (* 逐点统一 eps：f w < g w + eps（lt 支）升 real_le（Or 编码 inl 单向桥） *)
    assert (Hpt : forall w : X, real_le (f w) (real_plus (g w) eps)).
    { intro w.
      exact (RealSetoid.real_lt_le_iff_req (f w) (real_plus (g w) eps)
               (inl (H w eps Heps))). }
    pose proof (real_list_sum_le X f (fun w : X => real_plus (g w) eps) l Hpt) as Hsum.
    (* 换形右端：Σ(g+eps) == Σg + Σ(常数 eps) == Σg + lenR·eps *)
    apply (RealSetoid.real_le_id_r
             (real_list_sum X f l)
             (real_list_sum X (fun w : X => real_plus (g w) eps) l)
             (real_plus (real_list_sum X g l)
                        (real_mult (sumb_lenR X l) eps))).
    + apply (real_eq_trans _
               (real_plus (real_list_sum X g l)
                          (real_list_sum X (fun _ : X => eps) l)) _).
      * apply (real_list_sum_add X g (fun _ : X => eps) l).
      * apply (RealSetoid.real_eq_plus_compat (real_list_sum X g l)
                 (real_list_sum X (fun _ : X => eps) l)
                 (real_list_sum X g l)
                 (real_mult (sumb_lenR X l) eps)).
        -- apply real_eq_refl.
        -- apply sumb_sum_const.
    + exact Hsum.
Qed.

(* ============================================================ *)
(* 尾注：诚实登记表（本文件增量判定，接 UpRealLeB2 判定 G1-G6）              *)
(*                                                                *)
(* 【判定 S1｜逐点统一 eps】sumb_list_sum_le_b：可证，且免 1/n 拆分。     *)
(*   根因：real_le_b 系 Set 值全称面（∀eps>0），n 元求和闭合对每个        *)
(*   逐点件取同一 δ 即足——n 份 δ 并入右端后坍缩为 Σ(常数 δ)，由          *)
(*   sum_const 换形为 lenR·δ 一次性计账。这与 plain-eps 族的             *)
(*   eps/2 拆分链（leb2_half_add 基础模块）本质不同：全称余量在 Bishop       *)
(*   面天然可复制，无需构造性对半。                                      *)
(* 【判定 S2｜自持长度机器】sumb_lenR：Real 层 Fixpoint 三行自持，        *)
(*   零 nat 桥接口使用——CW_ConstructiveWorld_219 nat 嵌入系节证明件跨接口不可复用          *)
(*   （冻结判定在案），本文件绕开不使用。lenR 与 length 的数值对齐        *)
(*   无使用面（本设计零 nat 数值，全走 Real 归纳）。                      *)
(* 【判定 S3｜闭合组合器选型】主件走非负系数器（C:=lenR l，证书              *)
(*   sumb_lenR_nonneg）——lenR 的正性（严格）对空表不成立（lenR nil      *)
(*   == 0），故 C>0 证书路线不可用，正是 real_le_closure_b_nonneg        *)
(*   （UpRealLeB2 L102）的规格场景；空表支路经闭合组合器 C+1>0 的            *)
(*   证书加工面自然闭合，零分情形。                                      *)
(* 【判定 S4｜Or 编码使用边界】逐点升格仅使用单向桥（lt 支 inl →        *)
(*   real_le），与判定 2（Or 形 min 反例不可证）边界一致——本件           *)
(*   不主张 Or 形逐点前提升格。                                          *)
(* 【核对】原始任务表述目标 3 规格四件（lenR/lenR_nonneg/sum_const/主件）      *)
(*   全部落盘本文件；前缀 sumb_ 全库零占用（leb3_ 系  领地已用，        *)
(*   本文件分区避让）。判例判定 G2「组合器止步二元」自此补齐 n 元面。      *)
(* 【检查记录】四项关卡卡：G1 禁词全零（含头注注记位）；G2 重编 EXIT=0；      *)
(*   G3 提取检验 Obj.magic 计数为零（检验验后删）；G4 coqchk 认证         *)
(*   9.0 同平台长窗通过。全件 Print Assumptions Closed（见文末）。        *)
(* ============================================================ *)

Print Assumptions sumb_lenR_nonneg.
Print Assumptions sumb_sum_const.
Print Assumptions sumb_list_sum_le_b.

(* ======== G06_BForm 成员件：UpReqMinPProjB（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqMinPProjB.v —— 论文2 W2' 点火件：minp 投影定理的 B 形升格簇    *)
(*   （原始任务表述§九第4项；基座 = UpAuditBridge.v L1070                    *)
(*     real_minp_projection_eps，219 面回并版四项关卡通过——只读禁改，        *)
(*     本文件纯使用，零改写上游）                                     *)
(*                                                                *)
(* 主结果（结论位全 Set 层、零新增逻辑前提、全件真证）：                *)
(*   1. real_minp_projection_eps_B（主件）：                          *)
(*      KL_list(q‖minp) ≤_B KL_list(q‖full)，eps 余量全称消去。        *)
(*      路线 = real_le_closure_b_one 单步闭合 + 基座 eps 形原件直连     *)
(*      （判例判定3：plain-eps 余量族统一 Bishop 闭合；min 反例在案，   *)
(*        经典析取精确形不可证——本件即该裁决的 Bishop 形正解落实）。      *)
(*   2. real_minp_tail_nonneg_B（伴件 A）：尾项非负的 B 形              *)
(*      0 ≤_B Σ kl_tail；链 = uab_kl_tail_eval 等式换形（real_eq_sym）  *)
(*      + real_opp_log_Z_aud_nonneg + 单向桥 real_le_to_le_b。          *)
(*   3. real_minp_projection_B_split（伴件 B）：主件结论的分解路线重证， *)
(*      不使用基座 eps 形定理，改走 伴件A + ≤_B 加法兼容组合器           *)
(*      （UpRealLeB2 real_le_b_plus_compat）+ uab_kl_sum_split 右端     *)
(*      等式换形——与主件构成同结论双路线交叉验证。                       *)
(*   4. 助机四件（umpb_ 前缀，纯 Real 层零节依赖）：≤_B 自反 /           *)
(*      左端等式运输 / 右端等式运输 / 非负右加单调。                     *)
(*                                                                *)
(* 红线自检口径：                                                      *)
(*   —— 禁词全零（按全文件计含头注，判例坑6）；                        *)
(*   —— 全件 Qed 真证（term-mode 显式组装，real_eq 非 Id 禁改写，        *)
(*      全链 real_eq_trans/sym/compat 族），无任何降级占位；             *)
(*   —— 结论位全 Set 层：real_le_b 为 Set 值 forall 型，零 Prop 泄露；   *)
(*   —— 前提位逐字照抄基座证明面（判例组 判定：前提位照抄即升）；      *)
(*      keep 判定的析取/否定前提面为 root MinP 机器接口继承面            *)
(*      （基座同形），本文件零新增逻辑前提；                             *)
(*   —— 节变量逐字复刻基座证明面八参（判例症状3：Check 检验打表对齐，   *)
(*      检验日志 _w2__w2probe_sig.v.compile.log 在案）；                 *)
(*   —— 提取检验 Obj.magic=0（独立小检验，验后删）；                     *)
(*   —— Print Assumptions 全件 Closed under the global context          *)
(*      （文末六连打，证据在编译日志）。                                *)
(* ============================================================ *)

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
Require Import UpAuditBridge.
Require Import UpRealLeB.
Require Import UpRealLeB2.

(* ============================================================ *)
(* 助机区（纯 Real 层，零节依赖，全 term-mode 真证）                    *)
(* ============================================================ *)

(* 助机 1：≤_B 自反（单向桥 + real_le_refl 单步） *)
Lemma umpb_le_b_refl : forall x : Real, real_le_b x x.
Proof.
  intros x. apply real_le_to_le_b. apply real_le_refl.
Qed.

(* 助机 2：≤_B 右端等式运输：x ≤_B y1 且 y1≈y2 给 x ≤_B y2
   （real_eq 逐 eps 近似等价禁改写，走 RealSetoid.lt_id_r + plus_compat） *)
Lemma umpb_le_b_eq_r : forall x y1 y2 : Real,
  real_le_b x y1 -> real_eq y1 y2 -> real_le_b x y2.
Proof.
  intros x y1 y2 H Heq. unfold real_le_b in H. unfold real_le_b.
  intros eps Heps.
  apply (RealSetoid.real_lt_id_r x (real_plus y1 eps) (real_plus y2 eps)).
  - apply (RealSetoid.real_eq_plus_compat y1 eps y2 eps).
    + exact Heq.
    + apply real_eq_refl.
  - exact (H eps Heps).
Qed.

(* 助机 3：≤_B 左端等式运输：x1≈x2 且 x1 ≤_B y 给 x2 ≤_B y *)
Lemma umpb_le_b_eq_l : forall x1 x2 y : Real,
  real_eq x1 x2 -> real_le_b x1 y -> real_le_b x2 y.
Proof.
  intros x1 x2 y Heq H. unfold real_le_b in H. unfold real_le_b.
  intros eps Heps.
  apply (RealSetoid.real_lt_id_l x2 x1 (real_plus y eps)).
  - apply real_eq_sym. exact Heq.
  - exact (H eps Heps).
Qed.

(* 助机 4：≤_B 非负右加：0 ≤_B c 给 a ≤_B a + c
   （B 形版 uab_le_plus_nonneg_r：加法兼容组合器 + a+0≈a 左端运输） *)
Lemma umpb_le_b_plus_nonneg_r : forall a c : Real,
  real_le_b real_zero c -> real_le_b a (real_plus a c).
Proof.
  intros a c Hc.
  apply (umpb_le_b_eq_l (real_plus a real_zero) a (real_plus a c)).
  - apply real_plus_zero.
  - apply (real_le_b_plus_compat a a real_zero c).
    + apply umpb_le_b_refl.
    + exact Hc.
Qed.

(* ============================================================ *)
(* 主节：节变量逐字复刻基座 UpAuditBridge 证明面八参（声明序一致）       *)
(* ============================================================ *)

Section UpReqMinPProjB.

Variable Token : Type.
Variable vocab : list Token.
Variable real_temp_factor : Token -> Real.
Variable real_minp_keep : list Token -> Token -> Set.
Variable real_minp_keep_dec : forall (prefix : list Token) (w : Token),
  Or (real_minp_keep prefix w) (Not (real_minp_keep prefix w)).
Variable uab_temp_sum_pos : forall prefix : list Token,
  real_lt real_zero
    (uab_temp_sum Token vocab real_temp_factor real_minp_keep
                  real_minp_keep_dec prefix).
Variable uab_temp_factor_pos : forall w : Token,
  real_lt real_zero (real_temp_factor w).
Variable uab_Z_full_pos : real_lt real_zero
  (Z_full Token vocab real_temp_factor).

(* ============================================================ *)
(* 主件：KL_list(q‖minp) ≤_B KL_list(q‖full)                           *)
(*   eps 余量全称消去：plain-eps 形逐 eps 界（基座件直连）闭合为          *)
(*   Bishop 形非严格序（D:=one 特化闭合组合器，正性证书 real_lt_zero_one    *)
(*   为 CW_ConstructiveWorld_219 闭合既有件，零新增前提）。                                *)
(* ============================================================ *)

Theorem real_minp_projection_eps_B :
  forall (prefix : list Token) (q : Token -> Real)
    (Hq_norm : real_eq (real_list_sum Token q vocab) real_one)
    (Hq_pos : forall w : Token,
                real_minp_keep prefix w -> real_lt real_zero (q w))
    (Hq_fail : forall w : Token,
                 Not (real_minp_keep prefix w) -> real_eq (q w) real_zero),
  real_le_b
    (real_list_sum Token
       (uab_kl_q_minp Token vocab real_temp_factor real_minp_keep
                      real_minp_keep_dec uab_temp_sum_pos uab_temp_factor_pos
                      prefix q Hq_pos) vocab)
    (real_list_sum Token
       (uab_kl_q_full Token vocab real_temp_factor real_minp_keep
                      real_minp_keep_dec uab_temp_factor_pos uab_Z_full_pos
                      prefix q Hq_pos) vocab).
Proof.
  intros prefix q Hq_norm Hq_pos Hq_fail.
  apply real_le_closure_b_one. intros eps Heps.
  exact (real_minp_projection_eps Token vocab real_temp_factor real_minp_keep
           real_minp_keep_dec uab_temp_sum_pos uab_temp_factor_pos
           uab_Z_full_pos prefix q Hq_norm Hq_pos Hq_fail eps Heps).
Qed.

(* ============================================================ *)
(* 伴件 A：尾项非负的 B 形 0 ≤_B Σ kl_tail                              *)
(*   链 = uab_kl_tail_eval（Σ tail ≈ −log uab_Z_aud）右端换形接基座非负件，   *)
(*   再经单向桥升 B 形——基座主证明 HT 步的独立成件。                     *)
(* ============================================================ *)

Theorem real_minp_tail_nonneg_B :
  forall (prefix : list Token) (q : Token -> Real)
    (Hq_norm : real_eq (real_list_sum Token q vocab) real_one)
    (Hq_pos : forall w : Token,
                real_minp_keep prefix w -> real_lt real_zero (q w))
    (Hq_fail : forall w : Token,
                 Not (real_minp_keep prefix w) -> real_eq (q w) real_zero),
  real_le_b real_zero
    (real_list_sum Token
       (uab_kl_tail Token vocab real_temp_factor real_minp_keep
                    real_minp_keep_dec uab_temp_sum_pos uab_temp_factor_pos
                    uab_Z_full_pos prefix q Hq_pos) vocab).
Proof.
  intros prefix q Hq_norm Hq_pos Hq_fail.
  apply real_le_to_le_b.
  apply (RealSetoid.real_le_id_r real_zero
           (real_opp (real_log
              (uab_Z_aud Token vocab real_temp_factor real_minp_keep
                     real_minp_keep_dec uab_Z_full_pos prefix)
              (uab_Z_aud_pos_cert Token vocab real_temp_factor real_minp_keep
                                  real_minp_keep_dec uab_temp_sum_pos
                                  uab_Z_full_pos prefix)))
           (real_list_sum Token
              (uab_kl_tail Token vocab real_temp_factor real_minp_keep
                           real_minp_keep_dec uab_temp_sum_pos
                           uab_temp_factor_pos uab_Z_full_pos
                           prefix q Hq_pos) vocab)).
  - exact (real_eq_sym _ _
             (uab_kl_tail_eval Token vocab real_temp_factor real_minp_keep
                real_minp_keep_dec uab_temp_sum_pos uab_temp_factor_pos
                uab_Z_full_pos prefix q Hq_norm Hq_pos Hq_fail)).
  - exact (real_opp_log_Z_aud_nonneg Token vocab real_temp_factor
             real_minp_keep real_minp_keep_dec uab_temp_sum_pos
             uab_temp_factor_pos uab_Z_full_pos prefix).
Qed.

(* ============================================================ *)
(* 伴件 B：主件结论的分解路线重证（不使用基座 eps 形定理）                *)
(*   链 = 伴件A（尾项非负 B 形）+ 助机4（非负右加）+ ≤_B 加法兼容组合器   *)
(*   + uab_kl_sum_split 恒等式右端等式换形（助机2）。零 eps 求值。       *)
(* ============================================================ *)

Theorem real_minp_projection_B_split :
  forall (prefix : list Token) (q : Token -> Real)
    (Hq_norm : real_eq (real_list_sum Token q vocab) real_one)
    (Hq_pos : forall w : Token,
                real_minp_keep prefix w -> real_lt real_zero (q w))
    (Hq_fail : forall w : Token,
                 Not (real_minp_keep prefix w) -> real_eq (q w) real_zero),
  real_le_b
    (real_list_sum Token
       (uab_kl_q_minp Token vocab real_temp_factor real_minp_keep
                      real_minp_keep_dec uab_temp_sum_pos uab_temp_factor_pos
                      prefix q Hq_pos) vocab)
    (real_list_sum Token
       (uab_kl_q_full Token vocab real_temp_factor real_minp_keep
                      real_minp_keep_dec uab_temp_factor_pos uab_Z_full_pos
                      prefix q Hq_pos) vocab).
Proof.
  intros prefix q Hq_norm Hq_pos Hq_fail.
  pose proof (real_minp_tail_nonneg_B prefix q Hq_norm Hq_pos Hq_fail)
    as HtailB.
  pose proof (uab_kl_sum_split Token vocab real_temp_factor real_minp_keep
                 real_minp_keep_dec uab_temp_sum_pos uab_temp_factor_pos
                 uab_Z_full_pos prefix q Hq_norm Hq_pos Hq_fail) as Hsplit.
  apply (umpb_le_b_eq_r
           (real_list_sum Token
              (uab_kl_q_minp Token vocab real_temp_factor real_minp_keep
                             real_minp_keep_dec uab_temp_sum_pos
                             uab_temp_factor_pos prefix q Hq_pos) vocab)
           (real_plus
              (real_list_sum Token
                 (uab_kl_q_minp Token vocab real_temp_factor real_minp_keep
                                real_minp_keep_dec uab_temp_sum_pos
                                uab_temp_factor_pos prefix q Hq_pos) vocab)
              (real_list_sum Token
                 (uab_kl_tail Token vocab real_temp_factor real_minp_keep
                              real_minp_keep_dec uab_temp_sum_pos
                              uab_temp_factor_pos uab_Z_full_pos
                              prefix q Hq_pos) vocab))
           (real_list_sum Token
              (uab_kl_q_full Token vocab real_temp_factor real_minp_keep
                             real_minp_keep_dec uab_temp_factor_pos
                             uab_Z_full_pos prefix q Hq_pos) vocab)).
  - apply umpb_le_b_plus_nonneg_r. exact HtailB.
  - exact (real_eq_sym _ _ Hsplit).
Qed.

End UpReqMinPProjB.

(* ============================================================ *)
(* 主定理证据：全件 Print Assumptions（六连打，证据在编译日志）             *)
(* ============================================================ *)

Print Assumptions umpb_le_b_refl.
Print Assumptions umpb_le_b_eq_r.
Print Assumptions umpb_le_b_eq_l.
Print Assumptions umpb_le_b_plus_nonneg_r.
Print Assumptions real_minp_projection_eps_B.
Print Assumptions real_minp_tail_nonneg_B.
Print Assumptions real_minp_projection_B_split.

(* ======== G06_BForm 成员件：UpReqLatticeB（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqLatticeB.v —— B 形格组合面前段（）：strict-lt 新基元 + max 侧 *)
(*   （B 形扩展建造队列  拆分前段模块 · §9.4 格特征强扩展）           *)
(*                                                                *)
(* 定位：侦察模块「B形扩展建造队列」目标 4 前段。min 侧与格      *)
(* 组合律留  后模块；本库只做 strict-lt 基元、两连接件、max 侧三件。   *)
(* 上游使用：UpRealLeB3（运输三件 eq_r/plus_nonneg_r/refl， 给出，   *)
(* .v/.vo 双证新鲜）+ UpRealLeB（闭合组合器 D 置 one 特化 + 单向桥）+      *)
(* CW_ConstructiveWorld_219 锚点（real_max_proj@L39803 Q 层点态投影通道、real_max         *)
(* 逐点 Qmax 编码@L39763、real_lt sigT 见证型@L3517、stdlib 泛型格     *)
(* 严格形 Q.max_lub_lt 与 Q.min_dec、Qopp_le_compat、Qlt_minus_iff）。 *)
(*                                                                *)
(* 校注一则（对侦察单  草图）：逐点 Qmax 上界严格形无需 witness 全     *)
(* 重排——stdlib 泛型格库 Q.max_lub_lt（n<p ⟹ m<p ⟹ max n m<p）       *)
(* 在案可直连，逐点归约后一步闭合；新基元工作量减半，min 对偶           *)
(*（Q.min_glb_lt 同库在案）可由  同法平移。                         *)
(*                                                                *)
(* 六件清单：1 latb_lt_b 严格序基元（∃δ>0，x ≤_B y−δ；sigT+And 形       *)
(*     沿 real_lt 同构，Set 层零 Prop 出面）/ 2 latb_lt_b_to_le_b      *)
(*     严格形 ⟹ ≤_B 连接件（边界右加成对消去）/ 3 latb_real_lt_to_le_b *)
(*     CW_ConstructiveWorld_219 严格序 ⟹ ≤_B（Or 左支单步）/ 4 latb_lt_max_intro 严格     *)
(*     上界引入基元（Q 层通道：min 见证 + max_lub_lt 逐点直连）/        *)
(*   5 latb_max_le_b max 上界格主件（a≤_B c ∧ b≤_B c ⟹ max≤_B c；      *)
(*     同一 d 取 c+eps，左支入 Or 后 one 闭合组合器单步）/ 6 latb_max_le_r  *)
(*     吸收律实例（a≤_B b ⟹ max a b ≤_B b）。                          *)
(*                                                                *)
(* 红线自检口径：                                                      *)
(*   —— 语句面全 Set 层：latb_lt_b 为 sigT 见证型（And 分量系           *)
(*      real_lt 既有同构用法），结论全 real_le_b / real_lt；            *)
(*   —— 零 Or 形不可证面越界：不主张 real_le (real_max a b) c 精确形    *)
(*      （判定 2 同源分支选择面），严格面只走 real_lt 见证；             *)
(*   —— 前提位零新增（正性证书全既有件）；全件真证闭合无降级；           *)
(*   —— 提取检验 Obj.magic=0（独立小检验，验后删）；                    *)
(*   —— Print Assumptions 全件 Closed（文末六连打，证据在编译日志）。   *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qminmax.
From Stdlib Require Import Arith.PeanoNat.
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
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.

Local Open Scope Q_scope.

(* ============================================================ *)
(* 一、strict-lt 新基元与 ≤_B 连接件                                   *)
(* ============================================================ *)

(* 件 1：Bishop 严格序基元：x <ᴮ y := ∃δ>0，x ≤_B y+(−δ)。
   sigT+And 形沿 real_lt 同构（CW_ConstructiveWorld_219 L3517 同款 Set 层封装）；
   边距子句经 real_le_b 表出（零 Prop 出面）。 *)
Definition latb_lt_b (x y : Real) : Set :=
  sigT (fun d : Real => And (real_lt real_zero d)
                            (real_le_b x (real_plus y (real_opp d)))).

(* 件 2：连接件（严格形 ⟹ ≤_B）：x ≤_B y−δ 且 δ>0
   ⟹ x ≤_B (y−δ)+δ == y。右端加正量 δ（nonneg 右加运输件），
   再结合+对消+零元恒等链换形。 *)
Lemma latb_lt_b_to_le_b : forall x y : Real, latb_lt_b x y -> real_le_b x y.
Proof.
  intros x y Hd. destruct Hd as [d [Hdpos Hle]].
  apply (leb3_le_b_eq_r x (real_plus (real_plus y (real_opp d)) d) y).
  - apply (leb3_le_b_plus_nonneg_r x (real_plus y (real_opp d)) d Hle).
    unfold real_le. left. exact Hdpos.
  - assert (Hz : real_eq (real_plus (real_opp d) d) real_zero).
    { apply (real_eq_trans (real_plus (real_opp d) d)
               (real_plus d (real_opp d)) real_zero).
      - apply real_plus_comm.
      - apply real_plus_opp. }
    apply (real_eq_trans (real_plus (real_plus y (real_opp d)) d)
             (real_plus y (real_plus (real_opp d) d)) y).
    + apply real_eq_sym. apply real_plus_assoc.
    + apply (real_eq_trans (real_plus y (real_plus (real_opp d) d))
               (real_plus y real_zero) y).
      * apply (RealSetoid.real_eq_plus_compat y
                 (real_plus (real_opp d) d) y real_zero).
        -- apply real_eq_refl.
        -- exact Hz.
      * apply real_plus_zero.
Qed.

(* 件 3：连接件（CW_ConstructiveWorld_219 严格序 ⟹ ≤_B）：real_lt 即 Or 形左支，
   单向桥单步。 *)
Lemma latb_real_lt_to_le_b : forall x y : Real,
  real_lt x y -> real_le_b x y.
Proof.
  intros x y H. apply real_le_to_le_b. unfold real_le. left. exact H.
Qed.

(* ============================================================ *)
(* 二、max 侧组合件（经 real_max_proj Q 层通道）                        *)
(* ============================================================ *)

(* 件 4：严格上界引入基元：a<d 且 b<d ⟹ max a b<d。
   见证 eps 置 Qmin ea eb（正性经 Q.min_dec 分支）、N 置 max Na Nb；
   逐点归约（real_max_proj 通道）后：aₙ<dₙ−Qmin≤dₙ−ea 侧与 bₙ 侧
   分别经 Qopp_le_compat+Qplus_le_compat 换形，Q.max_lub_lt 一步
   闭合 Qmax，末段 Qlt_minus_iff+ring 恒等换形。 *)
Lemma latb_lt_max_intro : forall a b d : Real,
  real_lt a d -> real_lt b d -> real_lt (real_max a b) d.
Proof.
  intros a b d Ha Hb.
  destruct Ha as [ea [Hea [Na HNa]]].
  destruct Hb as [eb [Heb [Nb HNb]]].
  exists (Qmin ea eb). split.
  - apply Qlt_to_QltT.
    destruct (Q.min_dec ea eb) as [E | E].
    + rewrite E. apply QltT_to_Qlt. exact Hea.
    + rewrite E. apply QltT_to_Qlt. exact Heb.
  - exists (Nat.max Na Nb). intros n Hn.
    apply Qlt_to_QltT.
    rewrite (real_max_proj a b n).
    assert (Han : NatLe Na n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hn). }
    assert (Hbn : NatLe Nb n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_r.
      - exact (NatLe_drop _ _ Hn). }
    pose proof (QltT_to_Qlt _ _ (HNa n Han)) as Q1.
    pose proof (QltT_to_Qlt _ _ (HNb n Hbn)) as Q2.
    assert (Ml : Qle (Qmin ea eb) ea) by apply Q.le_min_l.
    assert (Mr : Qle (Qmin ea eb) eb) by apply Q.le_min_r.
    (* 严格界对翻：ea<dₙ−aₙ ⟹ aₙ<dₙ−ea（Qlt_minus_iff + ring 恒等） *)
    assert (Q1r : projT1 a n < projT1 d n - ea).
    { apply (proj2 (Qlt_minus_iff (projT1 a n) (projT1 d n - ea))).
      assert (Hj1 : (projT1 d n - ea - projT1 a n ==
                     projT1 d n - projT1 a n - ea)%Q)
        by (unfold Qminus; ring).
      rewrite Hj1.
      apply (proj1 (Qlt_minus_iff ea (projT1 d n - projT1 a n))).
      exact Q1. }
    assert (Q2r : projT1 b n < projT1 d n - eb).
    { apply (proj2 (Qlt_minus_iff (projT1 b n) (projT1 d n - eb))).
      assert (Hj2 : (projT1 d n - eb - projT1 b n ==
                     projT1 d n - projT1 b n - eb)%Q)
        by (unfold Qminus; ring).
      rewrite Hj2.
      apply (proj1 (Qlt_minus_iff eb (projT1 d n - projT1 b n))).
      exact Q2. }
    assert (Qa : projT1 a n < projT1 d n - Qmin ea eb).
    { apply (Qlt_le_trans _ (projT1 d n - ea) _ Q1r).
      unfold Qminus. apply Qplus_le_compat.
      - apply Qle_refl.
      - apply Qopp_le_compat. exact Ml. }
    assert (Qb : projT1 b n < projT1 d n - Qmin ea eb).
    { apply (Qlt_le_trans _ (projT1 d n - eb) _ Q2r).
      unfold Qminus. apply Qplus_le_compat.
      - apply Qle_refl.
      - apply Qopp_le_compat. exact Mr. }
    assert (Hmax : Qmax (projT1 a n) (projT1 b n)
                     < projT1 d n - Qmin ea eb)
      by (apply Q.max_lub_lt; assumption).
    apply (proj2 (Qlt_minus_iff (Qmin ea eb)
              (projT1 d n - Qmax (projT1 a n) (projT1 b n)))).
    assert (Hj : (projT1 d n - Qmax (projT1 a n) (projT1 b n)
                    + - Qmin ea eb ==
                  projT1 d n - Qmin ea eb
                    + - Qmax (projT1 a n) (projT1 b n))%Q)
      by (unfold Qminus; ring).
    rewrite Hj.
    apply (proj1 (Qlt_minus_iff (Qmax (projT1 a n) (projT1 b n))
                   (projT1 d n - Qmin ea eb))).
    exact Hmax.
Qed.

(* 件 5（主件）：max 上界格特征：a ≤_B c 且 b ≤_B c ⟹ max a b ≤_B c。
   给 eps>0：两前提同取 d:=c+eps，件 4 一步得 max a b<c+eps（严格），
   Or 左支单步入精确面，one 闭合组合器单步闭合——构造性分支选择难题
   （判定 2 同源）在严格见证面不存在，故无需 eps/2 拆分。 *)
Lemma latb_max_le_b : forall a b c : Real,
  real_le_b a c -> real_le_b b c -> real_le_b (real_max a b) c.
Proof.
  intros a b c Ha Hb.
  apply real_le_closure_b_one.
  intros eps Heps. unfold real_le. left.
  apply latb_lt_max_intro.
  - exact (Ha eps Heps).
  - exact (Hb eps Heps).
Qed.

(* 件 6：吸收律实例：a ≤_B b ⟹ max a b ≤_B b（件 5 + ≤_B 自反）。 *)
Lemma latb_max_le_r : forall a b : Real,
  real_le_b a b -> real_le_b (real_max a b) b.
Proof.
  intros a b H. apply (latb_max_le_b a b b H).
  apply leb3_le_b_refl.
Qed.

(* ============================================================ *)
(* 三、假设审计（全件 Closed，证据在编译日志）                           *)
(* ============================================================ *)

Print Assumptions latb_lt_b.
Print Assumptions latb_lt_b_to_le_b.
Print Assumptions latb_real_lt_to_le_b.
Print Assumptions latb_lt_max_intro.
Print Assumptions latb_max_le_b.
Print Assumptions latb_max_le_r.

(* ============================================================ *)
(* 四、min 侧组合件（ 后段模块追加节）：对偶基元 + 下界格律 + glb 主件 *)
(*                                                                *)
(* 五件清单：7 latb_min_glb 严格下界引入基元（Q 层通道：Qmin 见证 +   *)
(*     Q.min_glb_lt 逐点直连；严格界 e+pₙ<aₙ 平移经 Qle_lt_trans +    *)
(*     Qplus_le_compat；回程余量对翻沿 Qlt_minus_iff 定式）/          *)
(*   8 latb_min_le_b min 下界格主件（c ≤_B a ∧ c ≤_B b ⟹ c ≤_B        *)
(*     min a b；与 max 侧主件不对称——eps 余量挂在 min 外侧，one       *)
(*     闭合组合器单步不可达（max 侧 eps 恰在 latb_lt_max_intro 结论槽     *)
(*     内），走完整逐点证：real_plus_proj 换形 + Qmin 下界平移 +      *)
(*     Q.min_dec 分支闭合）/ 9 latb_min_le_l 下界格律左（免费件实    *)
(*     证：real_min_le_l_B @UpRealLeB L396 直连）/ 10 latb_min_le_r  *)
(*     下界格律右（real_min_le_r_B @UpRealLeB L403 直连）/            *)
(*   11 latb_min_le_le trans 组装件（real_le_b_trans @UpRealLeB2     *)
(*     F.2 + 件 9 两步：min a b ≤_B a ≤_B c ⟹ min a b ≤_B c）。       *)
(*                                                                *)
(* 红线沿  口径：语句面全 Set 层（real_lt sigT 见证形 + real_le_b  *)
(* forall 型，零 Prop 出面）；前提位零新增；全件真证闭合无降级。      *)
(* ============================================================ *)

(* 件 7：严格下界引入基元：p<a 且 p<b ⟹ p<min a b。
   见证 e 置 Qmin ea eb（正性经 Q.min_dec 分支）、N 置 max Na Nb；
   逐点归约（real_min_proj 通道）后：ea<aₙ−pₙ 对翻至 ea+pₙ<aₙ，
   e+pₙ ≤ ea+pₙ 平移（Qle_lt_trans 两步）得 e+pₙ<aₙ 与 e+pₙ<bₙ，
   Q.min_glb_lt 一步闭合 Qmin，末段 Qlt_minus_iff+ring 恒等对翻回
   real_lt 见证形 e<Qmin−pₙ。 *)
Lemma latb_min_glb : forall p a b : Real,
  real_lt p a -> real_lt p b -> real_lt p (real_min a b).
Proof.
  intros p a b Hp Ha.
  destruct Hp as [ea [Hea [Na HNa]]].
  destruct Ha as [eb [Heb [Nb HNb]]].
  exists (Qmin ea eb). split.
  - apply Qlt_to_QltT.
    destruct (Q.min_dec ea eb) as [E | E].
    + rewrite E. apply QltT_to_Qlt. exact Hea.
    + rewrite E. apply QltT_to_Qlt. exact Heb.
  - exists (Nat.max Na Nb). intros n Hn.
    apply Qlt_to_QltT.
    rewrite (real_min_proj a b n).
    assert (Han : NatLe Na n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hn). }
    assert (Hbn : NatLe Nb n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_r.
      - exact (NatLe_drop _ _ Hn). }
    pose proof (QltT_to_Qlt _ _ (HNa n Han)) as Q1.
    pose proof (QltT_to_Qlt _ _ (HNb n Hbn)) as Q2.
    assert (Ml : Qle (Qmin ea eb) ea) by apply Q.le_min_l.
    assert (Mr : Qle (Qmin ea eb) eb) by apply Q.le_min_r.
    (* 严格界对翻：ea<aₙ−pₙ ⟹ ea+pₙ<aₙ（Qlt_minus_iff + ring 恒等） *)
    assert (Q1r : ea + projT1 p n < projT1 a n).
    { apply (proj2 (Qlt_minus_iff (ea + projT1 p n) (projT1 a n))).
      assert (Hj1 : (projT1 a n - (ea + projT1 p n) ==
                     projT1 a n - projT1 p n - ea)%Q)
        by (unfold Qminus; ring).
      rewrite Hj1.
      apply (proj1 (Qlt_minus_iff ea (projT1 a n - projT1 p n))).
      exact Q1. }
    assert (Q2r : eb + projT1 p n < projT1 b n).
    { apply (proj2 (Qlt_minus_iff (eb + projT1 p n) (projT1 b n))).
      assert (Hj2 : (projT1 b n - (eb + projT1 p n) ==
                     projT1 b n - projT1 p n - eb)%Q)
        by (unfold Qminus; ring).
      rewrite Hj2.
      apply (proj1 (Qlt_minus_iff eb (projT1 b n - projT1 p n))).
      exact Q2. }
    (* 下界平移：e+pₙ ≤ ea+pₙ < aₙ 与 e+pₙ ≤ eb+pₙ < bₙ
       （Qle_lt_trans 中项全显式提供实参 + Qplus_le_compat 双前提形） *)
    assert (Qa : Qmin ea eb + projT1 p n < projT1 a n).
    { apply (Qle_lt_trans (Qmin ea eb + projT1 p n)
               (ea + projT1 p n) (projT1 a n)).
      - apply Qplus_le_compat.
        + exact Ml.
        + apply Qle_refl.
      - exact Q1r. }
    assert (Qb : Qmin ea eb + projT1 p n < projT1 b n).
    { apply (Qle_lt_trans (Qmin ea eb + projT1 p n)
               (eb + projT1 p n) (projT1 b n)).
      - apply Qplus_le_compat.
        + exact Mr.
        + apply Qle_refl.
      - exact Q2r. }
    assert (Hmin : Qmin ea eb + projT1 p n
                     < Qmin (projT1 a n) (projT1 b n))
      by (apply Q.min_glb_lt; assumption).
    (* 对翻回见证形：e<Qmin−pₙ ⟺ 0<Qmin−pₙ−e ⟺ 0<Qmin−(e+pₙ) *)
    apply (proj2 (Qlt_minus_iff (Qmin ea eb)
              (Qmin (projT1 a n) (projT1 b n) - projT1 p n))).
    assert (Hj : (Qmin (projT1 a n) (projT1 b n) - projT1 p n
                    - Qmin ea eb ==
                  Qmin (projT1 a n) (projT1 b n)
                    - (Qmin ea eb + projT1 p n))%Q)
      by (unfold Qminus; ring).
    rewrite Hj.
    apply (proj1 (Qlt_minus_iff (Qmin ea eb + projT1 p n)
                   (Qmin (projT1 a n) (projT1 b n)))).
    exact Hmin.
Qed.

(* 件 8（主件）：min 下界格特征：c ≤_B a 且 c ≤_B b ⟹ c ≤_B min a b。
   与件 5 不对称处：eps 余量挂在 min 外侧（目标 c<min a b+eps），
   件 7 结论槽无 eps 位，one 闭合组合器单步不可达——走完整逐点证：
   两前提各取同一 eps，real_plus_proj 换形至 aₙ+epsₙ 侧，Qmin 下界
   平移（Qopp_le_compat）后 Q.min_dec 分支闭合（分支后目标恰为
   左/右支现成严格界）。 *)
Lemma latb_min_le_b : forall c a b : Real,
  real_le_b c a -> real_le_b c b -> real_le_b c (real_min a b).
Proof.
  intros c a b Hca Hcb.
  unfold real_le_b. intros eps Heps.
  pose proof (Hca eps Heps) as L1.
  pose proof (Hcb eps Heps) as L2.
  destruct L1 as [ea [Hea [Na HNa]]].
  destruct L2 as [eb [Heb [Nb HNb]]].
  exists (Qmin ea eb). split.
  - apply Qlt_to_QltT.
    destruct (Q.min_dec ea eb) as [E | E].
    + rewrite E. apply QltT_to_Qlt. exact Hea.
    + rewrite E. apply QltT_to_Qlt. exact Heb.
  - exists (Nat.max Na Nb). intros n Hn.
    apply Qlt_to_QltT.
    rewrite (real_plus_proj (real_min a b) eps n).
    rewrite (real_min_proj a b n).
    assert (Han : NatLe Na n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hn). }
    assert (Hbn : NatLe Nb n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_r.
      - exact (NatLe_drop _ _ Hn). }
    (* 严格界对翻：ea<(a+eps)ₙ−cₙ ⟹ cₙ<(a+eps)ₙ−ea（Qlt_minus_iff+ring） *)
    assert (Q1 : projT1 c n < projT1 a n + projT1 eps n - ea).
    { rewrite <- (real_plus_proj a eps n).
      apply (proj2 (Qlt_minus_iff (projT1 c n)
                (projT1 (real_plus a eps) n - ea))).
      assert (Hj1 : (projT1 (real_plus a eps) n - ea - projT1 c n ==
                     projT1 (real_plus a eps) n - projT1 c n - ea)%Q)
        by (unfold Qminus; ring).
      rewrite Hj1.
      apply (proj1 (Qlt_minus_iff ea
                (projT1 (real_plus a eps) n - projT1 c n))).
      apply QltT_to_Qlt. exact (HNa n Han). }
    assert (Q2 : projT1 c n < projT1 b n + projT1 eps n - eb).
    { rewrite <- (real_plus_proj b eps n).
      apply (proj2 (Qlt_minus_iff (projT1 c n)
                (projT1 (real_plus b eps) n - eb))).
      assert (Hj2 : (projT1 (real_plus b eps) n - eb - projT1 c n ==
                     projT1 (real_plus b eps) n - projT1 c n - eb)%Q)
        by (unfold Qminus; ring).
      rewrite Hj2.
      apply (proj1 (Qlt_minus_iff eb
                (projT1 (real_plus b eps) n - projT1 c n))).
      apply QltT_to_Qlt. exact (HNb n Hbn). }
    assert (Ml : Qle (Qmin ea eb) ea) by apply Q.le_min_l.
    assert (Mr : Qle (Qmin ea eb) eb) by apply Q.le_min_r.
    (* 对翻回 cₙ 左位形：e<X−cₙ ⟺ 0<X−cₙ−e ⟺ 0<X−e−cₙ ⟺ cₙ<X−e *)
    apply (proj2 (Qlt_minus_iff (Qmin ea eb)
              (Qmin (projT1 a n) (projT1 b n) + projT1 eps n
                - projT1 c n))).
    assert (Hj : (Qmin (projT1 a n) (projT1 b n) + projT1 eps n
                    - projT1 c n - Qmin ea eb ==
                  Qmin (projT1 a n) (projT1 b n) + projT1 eps n
                    - Qmin ea eb - projT1 c n)%Q)
      by (unfold Qminus; ring).
    rewrite Hj.
    apply (proj1 (Qlt_minus_iff (projT1 c n)
              (Qmin (projT1 a n) (projT1 b n) + projT1 eps n
                - Qmin ea eb))).
    destruct (Q.min_dec (projT1 a n) (projT1 b n)) as [EM | EM].
    + rewrite EM.
      apply (Qlt_le_trans _ (projT1 a n + projT1 eps n - ea) _ Q1).
      unfold Qminus. apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat. exact Ml.
    + rewrite EM.
      apply (Qlt_le_trans _ (projT1 b n + projT1 eps n - eb) _ Q2).
      unfold Qminus. apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat. exact Mr.
Qed.

(* 件 9：下界格律左：min a b ≤_B a（免费件——交接注记 D.1 实证在案：
   real_min_le_l_B @UpRealLeB L396，签名 forall a b, real_le_b
   (real_min a b) a，逐字同形直连）。 *)
Lemma latb_min_le_l : forall a b : Real, real_le_b (real_min a b) a.
Proof. intros a b. exact (real_min_le_l_B a b). Qed.

(* 件 10：下界格律右：min a b ≤_B b（免费件——D.2 实证在案：
   real_min_le_r_B @UpRealLeB L403 直连）。 *)
Lemma latb_min_le_r : forall a b : Real, real_le_b (real_min a b) b.
Proof. intros a b. exact (real_min_le_r_B a b). Qed.

(* 件 11：trans 组装件：a ≤_B c ⟹ min a b ≤_B c。
   real_le_b_trans @UpRealLeB2 F.2（签名 forall x y z, real_le_b x y
   -> real_le_b y z -> real_le_b x z，.vo 新鲜实证）+ 件 9 两步组装。 *)
Lemma latb_min_le_le : forall a b c : Real,
  real_le_b a c -> real_le_b (real_min a b) c.
Proof.
  intros a b c H. apply (real_le_b_trans (real_min a b) a c).
  - apply real_min_le_l_B.
  - exact H.
Qed.

(* ============================================================ *)
(* 五、 假设审计（全件 Closed，证据在编译日志）                      *)
(* ============================================================ *)

Print Assumptions latb_min_glb.
Print Assumptions latb_min_le_b.
Print Assumptions latb_min_le_l.
Print Assumptions latb_min_le_r.
Print Assumptions latb_min_le_le.

(* ============================================================ *)
(* 六、与基座严格序的互连（假设位证明系列 #8： 决策项复活）          *)
(*     （ 交接注记「节五：latb_lt_b ⟵ real_lt 互连」实装）        *)
(*                                                                *)
(* 目标语句（ 交接注记原文）：real_lt x y ⟹ latb_lt_b x y——        *)
(* 把 CW_ConstructiveWorld_219 基座严格序（real_lt@L3517，Cauchy 追赶型：∃eps>0，∃N，    *)
(* ∀n≥N，eps<yₙ−xₙ）接入 latb_lt_b（∃δ>0，x ≤_B y+(−δ)）。方向单研：  *)
(* 反向（latb_lt_b ⟹ real_lt）不在范围。                            *)
(*                                                                *)
(* 证法（ 卡 §七+校注③路线）：real_lt 见证 (eps,N) 即"最终分离"    *)
(* 窗口；正性 Real δ 置 real_const eps（正性见证 eps·(1/2)，常值序列  *)
(* 窗口 N:=0；正性半量恒等式 eps−eps·(1/2)==eps·(1−1/2) 走 ring      *)
(* 多项式形+闭式 1−1/2==1/2 计算闭合——Q 的「/」系 Qdiv 独立算子，    *)
(* ring 视为不可抽象函数符，含变量的除法式须先化乘法形）；主部对任意  *)
(* 正性 e 取其 sigT 首分量 e0 为余量（正性免新造），窗口相交          *)
(* N:=max N N0：分离窗口经 Qlt_minus_iff 对翻 0<yₙ−xₙ+(−eps)，        *)
(* 追赶窗口给 e0<eₙ（real_zero 逐点化简），Qplus_lt_compat 合流       *)
(* 0+e0<(yₙ−xₙ+(−eps))+eₙ，ring 恒等换形回 real_lt 见证槽            *)
(* （real_plus_proj/real_opp_proj/real_const_proj 逐点展开）。       *)
(* ============================================================ *)

Lemma latb_real_lt_interconnect : forall x y : Real,
  real_lt x y -> latb_lt_b x y.
Proof.
  intros x y H.
  destruct H as [eps [Heps0 [N HN]]].
  pose proof (QltT_to_Qlt _ _ Heps0) as HepsQ.
  assert (Hhalf : Qlt 0 (1 / 2)).
  { vm_compute. reflexivity. }
  assert (Hhalf_eps : Qlt 0 (eps * (1 / 2))).
  { assert (Hz2 : (0 * (1 / 2) == 0)%Q) by (unfold Qminus; ring).
    rewrite <- Hz2.
    exact (proj2 (Qmult_lt_r 0 eps (1 / 2) Hhalf) HepsQ). }
  exists (real_const eps). split.
  - (* δ 正性：见证 eps·(1/2)，常值序列窗口 N:=0 *)
    exists (eps * (1 / 2)). split.
    + apply Qlt_to_QltT. exact Hhalf_eps.
    + exists O. intros n Hn.
      apply Qlt_to_QltT.
      rewrite (real_const_proj eps n).
      assert (Hzp : projT1 real_zero n == 0) by reflexivity.
      rewrite Hzp.
      assert (Hj : (eps - 0 == eps)%Q) by (unfold Qminus; ring).
      rewrite Hj.
      apply (proj2 (Qlt_minus_iff (eps * (1 / 2)) eps)).
      assert (Hj2 : (eps + - (eps * (1 / 2)) == eps * (1 - (1 / 2)))%Q)
        by (unfold Qminus; ring).
      rewrite Hj2.
      assert (Hc : (1 - (1 / 2) == 1 / 2)%Q) by (vm_compute; reflexivity).
      rewrite Hc.
      exact Hhalf_eps.
  - (* 主部：x ≤_B y+(−δ) 逐 eps 闭合 *)
    unfold real_le_b. intros e He.
    destruct He as [e0 [He0pos [N0 HN0]]].
    exists e0. split.
    + exact He0pos.
    + exists (Nat.max N N0). intros n Hn.
      apply Qlt_to_QltT.
      rewrite (real_plus_proj (real_plus y (real_opp (real_const eps))) e n).
      rewrite (real_plus_proj y (real_opp (real_const eps)) n).
      rewrite (real_opp_proj (real_const eps) n).
      rewrite (real_const_proj eps n).
      assert (HnN : NatLe N n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max N N0).
        - apply Nat.le_max_l.
        - exact (NatLe_drop _ _ Hn). }
      assert (HnN0 : NatLe N0 n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max N N0).
        - apply Nat.le_max_r.
        - exact (NatLe_drop _ _ Hn). }
      assert (Hzn : projT1 real_zero n == 0) by reflexivity.
      pose proof (QltT_to_Qlt _ _ (HN0 n HnN0)) as HB.
      rewrite Hzn in HB.
      assert (Hj3 : (projT1 e n - 0 == projT1 e n)%Q) by (unfold Qminus; ring).
      rewrite Hj3 in HB.
      pose proof (QltT_to_Qlt _ _ (HN n HnN)) as Q1.
      assert (HP : 0 < projT1 y n - projT1 x n + - eps).
      { apply (proj1 (Qlt_minus_iff eps (projT1 y n - projT1 x n))).
        exact Q1. }
      assert (Hfin : 0 + e0 < projT1 y n - projT1 x n + - eps + projT1 e n).
      { apply Qplus_lt_compat.
        - exact HP.
        - exact HB. }
      assert (Hj1 : (0 + e0 == e0)%Q) by (apply Qplus_0_l).
      rewrite Hj1 in Hfin.
      assert (Hj4 : (projT1 y n - projT1 x n + - eps + projT1 e n ==
                     projT1 y n + - eps + projT1 e n - projT1 x n)%Q)
        by (unfold Qminus; ring).
      rewrite Hj4 in Hfin.
      exact Hfin.
Qed.

Print Assumptions latb_real_lt_interconnect.
