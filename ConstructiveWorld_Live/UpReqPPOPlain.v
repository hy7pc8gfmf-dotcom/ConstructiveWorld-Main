(* ============================================================ *)
(* UpReqPPOPlain.v *)
(* *)
(* 目的： PPO plain-le 面：裁剪目标与保守性（ReqDiffPlain 载体）。 *)
(* 主件： rpl_ppo_conservative / rpl_std_ppo_conservative / rpl_ppo_gap_nonneg。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqAlign、UpReqRDF。 *)
(* 备注： 序谓词取 plain 形；裁剪误差非负为构造核。 *)
(* ============================================================ *)

(*
   工单：组5裁决书-dpoTotalLoss解冻与min-plainle8件-.md 第二部分
     本批在 UpReqRDF.v Part 0 增量登记，T2① 零证明槽，为后续解锁铺路）。
   ---------------------------------------------------------------------
   槽实例前提位设计（本批核心）：
   - 各节 Context {RDP : ReqDiffPlain R}（UpReqRDF.v Part 0 槽组）——槽实例前提
     = T2① 显式参：随节消解进入各件出口签名，非公理（C1 reqDecidableOrder 先例；
     Print Assumptions 不受影响，全件 Closed）。
   - min 消费位逐件换槽：Id min_le_l/min_le_r（Id 接口 plain 字段）->
     min_le_l_plain/min_le_r_plain（req 槽；req 接口 min_le_l 逐 eps 形
     le (min a b) (plus a eps)，plain 形不可导——冻结根因，本批由槽承接）。
   - 求和槽 rpl_sum_le/rpl_sum_nonneg：节内 Hypothesis 位（UpReqDist L206/
     UpReqAlign L65 sum_le 同位；nonneg 镜像见下方核对注记）。
   ---------------------------------------------------------------------
   逐件核对表（Id 原件 @ CW_ConstructiveWorld_219.v 行号 -> 本文件 req 件）：
     件1 ppo_conservative          L19526 -> rpl_ppo_conservative（min_le_l_plain
          + le_mult_compat_weak 接口字段 + req_le_mult_compat_r@UpReqAlgebra
          L465 + rpl_sum_le 槽；advantage_nonneg 前提位与 Id 同位）
     件2 std_ppo_conservative      L19559 -> rpl_std_ppo_conservative（同上，
          min_le_l_plain 直配双积；无 adv 符号前提与 Id 同位）
     件3 ppo_clip_upper            L19606 -> rpl_ppo_clip_upper（min_le_r_plain
          直引 + rpl_ppo_clip 定义展开，零求和槽）
     件4 ppo_surrogate_conservative L21209 -> rpl_ppo_surrogate_conservative
          （min_le_l_plain + req_le_mult_compat_r + rpl_sum_le 槽；policy_ratio/
          ppo_clip/ppo_surrogate/is_objective_of 定义级 req 同形转写）
     件5 ppo_gap_nonneg            L20083 -> rpl_ppo_gap_nonneg（件1 保守件 +
          req_le_minus_nonneg@UpReqAlgebra L706；minus 位 req_minus）
     件6 clip_error_nonneg         L112408 -> rpl_clip_error_nonneg
          （min_le_l_plain + req_le_minus_nonneg + 伴件1 + 伴件2）
     件7 clip_lower                L19518 -> rpl_clip_lower（r_max_le_r_plain
          自持右参槽直引——路线(a)，见登记表第 6 条）
     件8 ppo_clipped_improvement   L112439 -> rpl_ppo_clipped_improvement（节3，
           扫尾件挂随簇解锁件：ppo_surrogate req 簇（件4 等）结果后
          解锁。Id E1+E2 路线（ppo_is_decomp + clip_error_nonneg + le_plus_
          nonneg_r 装配）由件4 保守件一步替代（le_trans Hsurr + rpl_ppo_
          surrogate_conservative 直得 is_objective_of ≥ 0）；深链伴件 B =
          rpli_is_objective_value_id（Id ppo_surrogate_raw_is_value_improvement
          L20720 同形）本节自持——UpReqPPO.v rppo_ppo_surrogate_raw_is_value_
          消费以 .vo 态为准），按其证明机（比率消去 6 步 + 求和线性 + 归一化
          坍缩）抽象 R + 本节槽面自持镜像，见登记表第 7 条）
   伴件（Id 系有对应、req 侧自足导出）：
     伴件1 rpl_le_mult_nonneg_t12 <- Id le_mult_nonneg_t12 L21825（3 步 req 化：
          le_mult_compat_weak + mult_comm/req_mult_zero_r 换形 + le_id_l）
     伴件2 rpl_sum_nonneg <- Id sum_over_S_nonneg 字段 L1420 的 req 镜像槽。
          核对注记：裁决书原文引「sum_zero_nonneg 槽 UpReqDist L208」——字段面
          实测该槽方向为「Σ=0 且逐点非负 ⟹ 逐点=0」，不供给本件「逐点非负 ⟹
          UpReqMisc5.v reqSumOver rsum_over_S_nonneg L194（Id SumOver 八字段
          req 全镜像已含该字段）。
   ---------------------------------------------------------------------
   诚实签名变化登记表（规划书 §7.4）：
   1. minus -> req_minus（δ 透明 plus a (opp b)，UpReqAlgebra 同形；rpl_clip/
     rpl_ppo_surrogate/rpl_ppo_gap_nonneg/rpl_clip_error 语句面随之）。
   2. Id 节内六件零消费参数不进前提面：pi_old_norm/epsilon_pos（Alignment 节）+
     Hpi:normalized pi（PPOClipDecomp 节，件6 语句与证明零消费——裁决书可建结论
     未列，字段面实测后诚实削减）。
   3. 求和载体：Id sum_over_S（SumOver 类字段）-> 节参 sumf + 槽（UpReqPPO
     Section ReqPPOAdvantage 同位约定）；出口签名以 Check 探针为准（E359）。
   4. rpl_importance_ratio 携带 pi_star 链（reward/beta/pi_ref/Zap 前提位，Id
     L19502 同形；件4 用 policy_ratio 独立参数，与 Id 分工同位）。
   5. 近邻对位注：UpReqAlign L1216-1230 已有定义面近邻 ppo_clip_req/clip_error_req
     （PPO 簇 15 件批结果的 req 定义），但其引理面无本批 6 件保守件（原冻结）；
   6. 件7 增建（ 件16终验件，路线(a)）：clip_lower 冻结解除——Id 原件
     消费 r_max_le_r（右参形 le b (r_max a b)）；UpReqRDF.v ReqDiffPlain 已登记
     r_max_ge_plain 为左参形（le a (r_max a b)，Id r_max_le_l 镜像），方向不覆盖
     右参需求且 r_max 无对称交换桥——故 Id r_max_le_r 的 plain 镜像以本文件节1
     自持槽 r_max_le_r_plain 承接（T2① 零证明槽，与 RDP 槽组同款显式参非公理
   7. 件8 增建（ 扫尾件，挂随簇解锁）：Id PPOClipDecomp 节参
     Hpi:normalized pi 本件消费不削减——req 接口无 normalized 字段，同语义面 =
     req (sumf pi) one 节参 Hnorm 承接（rppo 系 Hnorm 位同形，归一化坍缩消费位）；
     （rpli_ratio_cancel 六步逐点消去 + rpli_sum_opp/rpli_sum_minus 内机 +
     rpli_sum_linear 槽坍缩），槽组 rpli_sum_le/ext/add/linear 全 T2① 假设位。
   ---------------------------------------------------------------------
   纪律：纯构造性；Set 层语句零 Prop 泄露（req/lt/le/Or 均 Set 值）；纯项模式
     （req/le 组合器逐段直引，零Ltac重写层）；假设位 = T2① 显式参非公理；全链可提取。 *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import UpReqRDF.
Import RealInterfaceEnhancedMod.

(* ===================================================================== *)
(* 节1 ReqPPOPlainObj：Id Alignment 节 PPO 块同位（件1/2/3/4/5）              *)
(*   节参数序 = Id L18750-18768 上游链 + L19495-19517 PPO 块（未消费位省略）    *)
(* ===================================================================== *)
Section ReqPPOPlainObj.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {RDP : ReqDiffPlain R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* T2① 求和槽（UpReqDist L206 / UpReqAlign L65 sum_le 同位） *)
Hypothesis rpl_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).

(* T2① 右参槽（Id r_max_le_r plain 镜像：le b (r_max a b)）——ReqDiffPlain 类体
   只读不碰，故节1自持承接，路线(a)解锁 clip_lower（登记表第 6 条） *)
Hypothesis r_max_le_r_plain :
  forall a b : R, le b (r_max a b).

(* T5 扩槽（R120 B39 后，T4R §⑤-A2 配方）：pi_star_req canonical 签名顶入
   sum_pos 位；Zap 槽闲置化保留（防下游语句面引用断裂）。 *)
Hypothesis rpl_sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).

(* ---- Id Alignment 上游链同位（L18750-18762） ---- *)
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
(* T4R2 补位（T5 移交账处方）：rpl_pistar canonical 喂参需 pi_ref_pos 位——
   本节原缺此声明（红 :133 The reference pi_ref_pos was not found）；出节签名 +1，
   本件系单点终端件零下游消费。 *)
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable Zap : lt zero (Z_align_req S sumf reward beta beta_pos pi_ref).

(* ---- Id PPO 块节参同位（L19495-19517；未消费位 pi_old_norm/epsilon_pos 省略） ---- *)
Variable pi_old : S -> R.
Variable pi_old_pos : forall s : S, lt zero (pi_old s).
Variable advantage_fn : S -> R.
Variable advantage_nonneg : forall s : S, le zero (advantage_fn s).
Variable epsilon : R.

(* ---- 定义级 req 同形转写 ---- *)

(* Id pi_star 消费位：L18762 闭式最优策略 -> UpReqAlign pi_star_req 实例化 *)
Definition rpl_pistar (s : S) : R :=
  pi_star_req S sumf rpl_sum_pos reward beta beta_pos pi_ref pi_ref_pos s.

(* Id importance_ratio L19502 同形 *)
Definition rpl_importance_ratio (s : S) : R :=
  mult (rpl_pistar s) (inv_pos (pi_old s) (pi_old_pos s)).

(* Id clip L19506 同形（minus 位 req_minus） *)
Definition rpl_clip (r : R) : R :=
  r_max (min r (plus one epsilon)) (req_minus one epsilon).

(* Id ppo_objective L19510 同形 *)
Definition rpl_ppo_objective : R :=
  sumf (fun s : S => mult (pi_old s)
    (mult (min (rpl_importance_ratio s) (rpl_clip (rpl_importance_ratio s)))
          (advantage_fn s))).

(* Id is_objective L19515 同形 *)
Definition rpl_is_objective : R :=
  sumf (fun s : S => mult (pi_old s) (mult (rpl_importance_ratio s) (advantage_fn s))).

(* Id policy_ratio L19582 同形 *)
Definition rpl_policy_ratio (pi p_old : S -> R) (s : S) (Hpos : lt zero (p_old s)) : R :=
  mult (pi s) (inv_pos (p_old s) Hpos).

(* Id ppo_clip L19586 同形（标准形态 min (r_max low r) high） *)
Definition rpl_ppo_clip (r low high : R) : R :=
  min (r_max low r) high.

(* Id ppo_surrogate L19590 同形（minus 位 req_minus） *)
Definition rpl_ppo_surrogate (pi p_old : S -> R) (adv : S -> R) (eps : R)
  (pi_old_pos : forall s : S, lt zero (p_old s)) : R :=
  sumf (fun s : S => mult (p_old s)
    (min (mult (rpl_policy_ratio pi p_old s (pi_old_pos s)) (adv s))
         (mult (rpl_ppo_clip (rpl_policy_ratio pi p_old s (pi_old_pos s))
                             (req_minus one eps) (plus one eps))
               (adv s)))).

(* Id is_objective_of L19599 同形 *)
Definition rpl_is_objective_of (pi p_old : S -> R) (adv : S -> R)
  (pi_old_pos : forall s : S, lt zero (p_old s)) : R :=
  sumf (fun s : S => mult (p_old s)
    (mult (rpl_policy_ratio pi p_old s (pi_old_pos s)) (adv s))).

(* Id std_ppo_objective L19557 同形 *)
Definition rpl_std_ppo_objective : R :=
  sumf (fun s : S => mult (pi_old s)
    (min (mult (rpl_importance_ratio s) (advantage_fn s))
         (mult (rpl_clip (rpl_importance_ratio s)) (advantage_fn s)))).

(* ===================================================================== *)
(* 件3 rpl_ppo_clip_upper（Id L19606）：裁剪上界，min_le_r_plain 直引        *)
(* ===================================================================== *)
Lemma rpl_ppo_clip_upper :
  forall r low high : R, le (rpl_ppo_clip r low high) high.
Proof.
  intros r low high. unfold rpl_ppo_clip.
  apply min_le_r_plain.
Qed.

(* ===================================================================== *)
(* 件1 rpl_ppo_conservative（Id L19526）：ppo_objective <= is_objective      *)
(*   槽消费：min_le_l_plain；腿：接口字段 le_mult_compat_weak（逐点内积）+    *)
(*   req_le_mult_compat_r（乘 pi_old 非负因子）+ rpl_sum_le 槽（求和提升）    *)
(* ===================================================================== *)
Lemma rpl_ppo_conservative :
  le rpl_ppo_objective rpl_is_objective.
Proof.
  unfold rpl_ppo_objective, rpl_is_objective.
  apply rpl_sum_le.
  intro s.
  assert (Hmin : le (min (rpl_importance_ratio s) (rpl_clip (rpl_importance_ratio s)))
                     (rpl_importance_ratio s))
    by exact (min_le_l_plain (rpl_importance_ratio s)
                             (rpl_clip (rpl_importance_ratio s))).
  assert (Hinner : le (mult (min (rpl_importance_ratio s) (rpl_clip (rpl_importance_ratio s)))
                            (advantage_fn s))
                      (mult (rpl_importance_ratio s) (advantage_fn s)))
    by exact (le_mult_compat_weak
                (min (rpl_importance_ratio s) (rpl_clip (rpl_importance_ratio s)))
                (rpl_importance_ratio s) (advantage_fn s)
                (advantage_nonneg s) Hmin).
  assert (Hpi : le zero (pi_old s))
    by (apply (lt_le_iff _ _); left; apply pi_old_pos).
  exact (req_le_mult_compat_r (pi_old s) _ _ Hpi Hinner).
Qed.

(* ===================================================================== *)
(* 件2 rpl_std_ppo_conservative（Id L19559）：标准形态保守性，无 adv 符号前提  *)
(*   槽消费：min_le_l_plain 直配双积（min (r·A) (clip(r)·A) <= r·A 定义性腿） *)
(* ===================================================================== *)
Lemma rpl_std_ppo_conservative :
  le rpl_std_ppo_objective rpl_is_objective.
Proof.
  unfold rpl_std_ppo_objective, rpl_is_objective.
  apply rpl_sum_le.
  intro s.
  assert (Hmin : le (min (mult (rpl_importance_ratio s) (advantage_fn s))
                         (mult (rpl_clip (rpl_importance_ratio s)) (advantage_fn s)))
                    (mult (rpl_importance_ratio s) (advantage_fn s)))
    by exact (min_le_l_plain (mult (rpl_importance_ratio s) (advantage_fn s))
                             (mult (rpl_clip (rpl_importance_ratio s)) (advantage_fn s))).
  assert (Hpi : le zero (pi_old s))
    by (apply (lt_le_iff _ _); left; apply pi_old_pos).
  exact (req_le_mult_compat_r (pi_old s) _ _ Hpi Hmin).
Qed.

(* ===================================================================== *)
(* 件5 rpl_ppo_gap_nonneg（Id L20083）：IS 目标 - PPO 目标 >= 0              *)
(*   消费：件1 保守件 + req_le_minus_nonneg@UpReqAlgebra L706（minus 位       *)
(*   req_minus 与 Id le_minus_nonneg 逐位同构）                              *)
(* ===================================================================== *)
Lemma rpl_ppo_gap_nonneg :
  le zero (req_minus rpl_is_objective rpl_ppo_objective).
Proof.
  apply (req_le_minus_nonneg rpl_ppo_objective rpl_is_objective).
  exact rpl_ppo_conservative.
Qed.

(* ===================================================================== *)
(* 件4 rpl_ppo_surrogate_conservative（Id L21209）：标准形态代理目标保守性      *)
(*   无 adv 符号前提与 Id 同位（pi_old 为节参，正性在语句内全称）；槽消费：      *)
(*   min_le_l_plain + req_le_mult_compat_r + rpl_sum_le 槽                   *)
(* ===================================================================== *)
Lemma rpl_ppo_surrogate_conservative :
  forall (pi : S -> R) (adv : S -> R) (eps : R),
  forall (Hpi_old_pos : forall s : S, lt zero (pi_old s)),
  le (rpl_ppo_surrogate pi pi_old adv eps Hpi_old_pos)
     (rpl_is_objective_of pi pi_old adv Hpi_old_pos).
Proof.
  intros pi adv eps Hpi_old_pos.
  unfold rpl_ppo_surrogate, rpl_is_objective_of.
  apply rpl_sum_le.
  intro s.
  assert (Hmin : le (min (mult (rpl_policy_ratio pi pi_old s (Hpi_old_pos s)) (adv s))
                         (mult (rpl_ppo_clip (rpl_policy_ratio pi pi_old s (Hpi_old_pos s))
                                             (req_minus one eps) (plus one eps))
                               (adv s)))
                    (mult (rpl_policy_ratio pi pi_old s (Hpi_old_pos s)) (adv s)))
    by exact (min_le_l_plain
                (mult (rpl_policy_ratio pi pi_old s (Hpi_old_pos s)) (adv s))
                (mult (rpl_ppo_clip (rpl_policy_ratio pi pi_old s (Hpi_old_pos s))
                                    (req_minus one eps) (plus one eps))
                      (adv s))).
  assert (Hpi : le zero (pi_old s))
    by (apply (lt_le_iff _ _); left; apply Hpi_old_pos).
  exact (req_le_mult_compat_r (pi_old s) _ _ Hpi Hmin).
Qed.

(* ===================================================================== *)
(* 件7 rpl_clip_lower（Id L19518）：裁剪下界 clip(r) >= 1 - eps               *)
(*   槽消费：r_max_le_r_plain 右参形直引（与 Id 原件 apply r_max_le_r 同位；    *)
(*   minus 位 req_minus 随 rpl_clip 语句面）                                  *)
(* ===================================================================== *)
Lemma rpl_clip_lower :
  forall r : R, le (req_minus one epsilon) (rpl_clip r).
Proof.
  intro r. unfold rpl_clip.
  exact (r_max_le_r_plain (min r (plus one epsilon)) (req_minus one epsilon)).
Qed.

End ReqPPOPlainObj.

(* ===================================================================== *)
(* 节2 ReqPPOPlainClipErr：Id PPOClipDecomp 节同位（件6 + 伴件2）              *)
(*   节参数 = Id L112330-112347（Hpi:normalized pi 位不进本件——件6 语句与      *)
(*   证明零消费，字段面实测后诚实削减，签名登记表第 2 条）                        *)
(* ===================================================================== *)
Section ReqPPOPlainClipErr.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {RDP : ReqDiffPlain R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* T2① nonneg 镜像槽（Id sum_over_S_nonneg 字段 L1420 的 req 承接；
   先例 = UpReqMisc5 reqSumOver rsum_over_S_nonneg L194） *)
Hypothesis rpl_sum_nonneg :
  forall f : S -> R, (forall s : S, le zero (f s)) -> le zero (sumf f).

Variable pi p_old : S -> R.
Variable eps : R.
Variable Hpos : forall s : S, lt zero (p_old s).

(* Id ratio L112347 同形（节1 rpl_policy_ratio 实例化；跨节消费 S 显式参——消解序） *)
Definition rpl_ratio (s : S) : R :=
  rpl_policy_ratio S pi p_old s (Hpos s).

(* Id clip_error L112354 同形（minus 位 req_minus；rpl_ppo_clip 节1 消费） *)
Definition rpl_clip_error (adv : S -> R) : R :=
  sumf (fun s : S =>
    mult (p_old s)
      (req_minus (mult (rpl_ratio s) (adv s))
                 (min (mult (rpl_ratio s) (adv s))
                      (mult (rpl_ppo_clip (rpl_ratio s) (req_minus one eps) (plus one eps))
                            (adv s))))).

(* ===================================================================== *)
(* 伴件1 rpl_le_mult_nonneg_t12（Id le_mult_nonneg_t12 L21825 req 化）：     *)
(*   双非负因子积非负——le_mult_compat_weak + 换形链，3 步自足                *)
(* ===================================================================== *)
Lemma rpl_le_mult_nonneg_t12 :
  forall a b : R, le zero a -> le zero b -> le zero (mult a b).
Proof.
  intros a b Ha Hb.
  assert (Hstep : le (mult zero b) (mult a b))
    by exact (le_mult_compat_weak zero a b Hb Ha).
  assert (Hz : req (mult zero b) zero)
    by exact (req_trans (mult zero b) (mult b zero) zero
                        (mult_comm zero b) (req_mult_zero_r b)).
  exact (le_id_l zero (mult zero b) (mult a b)
                 (req_sym (mult zero b) zero Hz) Hstep).
Qed.

(* ===================================================================== *)
(* 件6 rpl_clip_error_nonneg（Id L112408）：clip 误差非负（无 adv 符号前提）   *)
(*   槽消费：min_le_l_plain（req_le_minus_nonneg 喂腿）+ rpl_sum_nonneg 槽     *)
(*   （伴件1 喂左因子 p_old s 非负）                                          *)
(* ===================================================================== *)
Lemma rpl_clip_error_nonneg : forall adv : S -> R, le zero (rpl_clip_error adv).
Proof.
  intro adv. unfold rpl_clip_error.
  apply rpl_sum_nonneg. intro s.
  apply (rpl_le_mult_nonneg_t12 (p_old s)
    (req_minus (mult (rpl_ratio s) (adv s))
               (min (mult (rpl_ratio s) (adv s))
                    (mult (rpl_ppo_clip (rpl_ratio s) (req_minus one eps) (plus one eps))
                          (adv s))))).
  - exact (lt_le_iff _ _ (inl (Hpos s))).
  - apply (req_le_minus_nonneg
             (min (mult (rpl_ratio s) (adv s))
                  (mult (rpl_ppo_clip (rpl_ratio s) (req_minus one eps) (plus one eps))
                        (adv s)))
             (mult (rpl_ratio s) (adv s))).
    exact (min_le_l_plain (mult (rpl_ratio s) (adv s))
                          (mult (rpl_ppo_clip (rpl_ratio s) (req_minus one eps) (plus one eps))
                                (adv s))).
Qed.

End ReqPPOPlainClipErr.

(* ===================================================================== *)
(* 节3 ReqPPOPlainImprove：Id PPOClipDecomp 节 E3 同位（件8 挂随簇解锁件）    *)
(*   消费：件4 rpl_ppo_surrogate_conservative（同文件节1）——Id E1+E2 路线     *)
(*   （ppo_is_decomp + clip_error_nonneg + le_plus_nonneg_r 装配）由保守件    *)
(*   一步替代（le_trans Hsurr + 件4 直得 is_objective_of ≥ 0；min_le_l_plain *)
(*   槽随件4 内部消费）；深链伴件 B = rpli_is_objective_value_id（Id          *)
(*   ppo_surrogate_raw_is_value_improvement L20720 同形）本节自持：           *)
(*   UpReqPPO.v rppo_ppo_surrogate_raw_is_value_improvement 真证在案但其     *)

(*   证明机（逐点比率消去 6 步 + 求和线性 + 归一化坍缩）抽象 R + 本节槽面     *)
(*   镜像，与 UpReqPPO/UpReqAlign 双向互证先例同构。                          *)
(*   节参数 = Id PPOClipDecomp L112330-112347 同位（pi p_old Hpos；eps 进     *)
(*   件8 语句 forall 位）；Id Hpi:normalized pi 位以 req (sumf pi) one 节参   *)
(*   Hnorm 承接（本件消费不削减——登记表第 7 条）。                              *)
(*   槽组：rpli_sum_le（件4 消费面，节1 同款 T2①）+ rpli_sum_ext/rpli_sum_   *)
(*   add/rpli_sum_linear（UpReqPPO ReqPPOAdvantage 诚实桥假设位同位）。       *)
(* ===================================================================== *)
Section ReqPPOPlainImprove.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {RDP : ReqDiffPlain R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* T2① 槽组：le 槽（件4 消费面）+ req 求和三槽（rppo 同位诚实桥） *)
Hypothesis rpli_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis rpli_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis rpli_sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis rpli_sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).

(* ---- Id PPOClipDecomp 节参同位（L112339-112347） ---- *)
Variable pi p_old : S -> R.
Variable Hpos : forall s : S, lt zero (p_old s).
(* Id Hpi : normalized pi 的 req 同语义面（req 接口无 normalized 字段；
   rppo 系 Hnorm 位同形；归一化坍缩消费位，登记表第 7 条） *)
Variable Hnorm : req (sumf pi) one.

(* Id state_value L19172 / advantage L19176 同形（minus 位 req_minus；
   reward 显式参——Id 系节参 reward 的显式化） *)
Definition rpli_state_value (reward p : S -> R) : R :=
  sumf (fun s : S => mult (p s) (reward s)).
Definition rpli_advantage (reward p : S -> R) (s : S) : R :=
  req_minus (reward s) (rpli_state_value reward p).

(* ---- 内机 0：opp one · x == opp x（rppo_opp_one_mult 同构） ---- *)
Lemma rpli_opp_one_mult : forall x : R, req (mult (opp one) x) (opp x).
Proof.
  intro x.
  apply (req_trans (mult (opp one) x) (opp (mult one x)) (opp x)).
  - exact (req_opp_mult_r one x).
  - apply (req_opp_compat (mult one x) x). exact (req_mult_one_l x).
Qed.

(* ---- 内机 1：Σ opp f == opp Σ f（rppo_sum_opp 同构） ---- *)
Lemma rpli_sum_opp :
  forall f : S -> R, req (sumf (fun s : S => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s : S => opp (f s)))
                   (sumf (fun s : S => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (rpli_sum_ext (fun s : S => opp (f s))
                        (fun s : S => mult (opp one) (f s))).
    intro s. exact (req_sym _ _ (rpli_opp_one_mult (f s))).
  - apply (req_trans (sumf (fun s : S => mult (opp one) (f s)))
                     (mult (opp one) (sumf f))
                     (opp (sumf f))).
    + exact (rpli_sum_linear (opp one) f).
    + exact (rpli_opp_one_mult (sumf f)).
Qed.

(* ---- 内机 2：Σ (f − g) == Σ f − Σ g（req_minus δ 透明 plus a (opp b)） -- *)
Lemma rpli_sum_minus :
  forall f g : S -> R,
    req (sumf (fun s : S => req_minus (f s) (g s)))
        (req_minus (sumf f) (sumf g)).
Proof.
  intros f g.
  apply (req_trans (sumf (fun s : S => req_minus (f s) (g s)))
                   (plus (sumf f) (sumf (fun s : S => opp (g s))))
                   (req_minus (sumf f) (sumf g))).
  - exact (rpli_sum_add f (fun s : S => opp (g s))).
  - exact (req_plus_compat (sumf f) (sumf f)
                           (sumf (fun s : S => opp (g s))) (opp (sumf g))
                           (req_refl (sumf f))
                           (rpli_sum_opp g)).
Qed.

(* ---- 深链伴件 B 前置机：逐点比率消去（rppo Hpt 六步链同构）               *)
(*   p_old·((pi/p_old)·A) == pi·A（rpl_policy_ratio δ 透明展开消费）          *)
Lemma rpli_ratio_cancel :
  forall (reward : S -> R) (s : S),
    req (mult (p_old s)
              (mult (rpl_policy_ratio S pi p_old s (Hpos s))
                    (rpli_advantage reward p_old s)))
        (mult (pi s) (rpli_advantage reward p_old s)).
Proof.
  intros reward s.
  assert (Ha : req (mult (p_old s)
                   (mult (rpl_policy_ratio S pi p_old s (Hpos s))
                         (rpli_advantage reward p_old s)))
                   (mult (mult (p_old s)
                    (mult (pi s) (inv_pos (p_old s) (Hpos s))))
                    (rpli_advantage reward p_old s)))
    by exact (mult_assoc (p_old s) (rpl_policy_ratio S pi p_old s (Hpos s))
                         (rpli_advantage reward p_old s)).
  assert (Hb : req (mult (mult (p_old s)
                          (mult (pi s) (inv_pos (p_old s) (Hpos s))))
                         (rpli_advantage reward p_old s))
                   (mult (mult (mult (p_old s) (pi s))
                          (inv_pos (p_old s) (Hpos s)))
                         (rpli_advantage reward p_old s)))
    by exact (req_mult_compat (mult (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s))))
                              (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s)))
                              (rpli_advantage reward p_old s) (rpli_advantage reward p_old s)
                              (mult_assoc (p_old s) (pi s) (inv_pos (p_old s) (Hpos s)))
                              (req_refl (rpli_advantage reward p_old s))).
  assert (Hc : req (mult (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s)))
                         (rpli_advantage reward p_old s))
                   (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                         (rpli_advantage reward p_old s)))
    by exact (req_mult_compat (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s)))
                              (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                              (rpli_advantage reward p_old s) (rpli_advantage reward p_old s)
                              (req_mult_compat (mult (p_old s) (pi s)) (mult (pi s) (p_old s))
                                               (inv_pos (p_old s) (Hpos s))
                                               (inv_pos (p_old s) (Hpos s))
                                               (mult_comm (p_old s) (pi s))
                                               (req_refl (inv_pos (p_old s) (Hpos s))))
                              (req_refl (rpli_advantage reward p_old s))).
  assert (Hd : req (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                         (rpli_advantage reward p_old s))
                   (mult (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                         (rpli_advantage reward p_old s)))
    by exact (req_mult_compat (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                              (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                              (rpli_advantage reward p_old s) (rpli_advantage reward p_old s)
                              (req_sym _ _ (mult_assoc (pi s) (p_old s)
                                                       (inv_pos (p_old s) (Hpos s))))
                              (req_refl (rpli_advantage reward p_old s))).
  assert (He : req (mult (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                         (rpli_advantage reward p_old s))
                   (mult (mult (pi s) one) (rpli_advantage reward p_old s)))
    by exact (req_mult_compat (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                              (mult (pi s) one)
                              (rpli_advantage reward p_old s) (rpli_advantage reward p_old s)
                              (req_mult_compat (pi s) (pi s)
                                               (mult (p_old s) (inv_pos (p_old s) (Hpos s)))
                                               one
                                               (req_refl (pi s))
                                               (inv_pos_correct (p_old s) (Hpos s)))
                              (req_refl (rpli_advantage reward p_old s))).
  assert (Hf : req (mult (mult (pi s) one) (rpli_advantage reward p_old s))
                   (mult (pi s) (rpli_advantage reward p_old s)))
    by exact (req_mult_compat (mult (pi s) one) (pi s)
                              (rpli_advantage reward p_old s) (rpli_advantage reward p_old s)
                              (mult_one (pi s))
                              (req_refl (rpli_advantage reward p_old s))).
  exact (req_trans _ _ _ Ha (req_trans _ _ _ Hb (req_trans _ _ _ Hc
           (req_trans _ _ _ Hd (req_trans _ _ _ He Hf))))).
Qed.

(* ---- 深链伴件 B：rpli_is_objective_value_id（Id L20720 同形）              *)
(*   L_raw(pi, p_old) = V(pi) − V(p_old)：比率消去（前置机）+ 求和线性 +      *)
(*   归一化坍缩（Hnorm）。                                                    *)
Lemma rpli_is_objective_value_id :
  forall reward : S -> R,
    req (rpl_is_objective_of S sumf pi p_old (rpli_advantage reward p_old) Hpos)
        (req_minus (rpli_state_value reward pi)
                   (rpli_state_value reward p_old)).
Proof.
  intro reward.
  (* 步1+2：逐点比率消去 + sum_ext 提升 *)
  assert (H2 : req (rpl_is_objective_of S sumf pi p_old
                     (rpli_advantage reward p_old) Hpos)
                   (sumf (fun s : S => mult (pi s)
                          (rpli_advantage reward p_old s)))).
  { unfold rpl_is_objective_of.
    apply (rpli_sum_ext (fun s : S => mult (p_old s)
                          (mult (rpl_policy_ratio S pi p_old s (Hpos s))
                                (rpli_advantage reward p_old s)))
                        (fun s : S => mult (pi s)
                          (rpli_advantage reward p_old s))).
    intro s. exact (rpli_ratio_cancel reward s). }
  (* 步3：advantage 展开（δ 透明）+ 逐点乘减分配 + sum_minus *)
  assert (H3 : req (sumf (fun s : S => mult (pi s) (rpli_advantage reward p_old s)))
                   (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                              (sumf (fun s : S =>
                                mult (pi s) (rpli_state_value reward p_old))))).
  { apply (req_trans (sumf (fun s : S => mult (pi s) (rpli_advantage reward p_old s)))
                     (sumf (fun s : S =>
                       req_minus (mult (pi s) (reward s))
                                 (mult (pi s) (rpli_state_value reward p_old))))
                     (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                                (sumf (fun s : S =>
                                  mult (pi s) (rpli_state_value reward p_old))))).
    - apply (rpli_sum_ext (fun s : S => mult (pi s) (rpli_advantage reward p_old s))
                          (fun s : S =>
                            req_minus (mult (pi s) (reward s))
                                      (mult (pi s) (rpli_state_value reward p_old)))).
      intro s. exact (req_mult_minus_distr_l (pi s) (reward s)
                             (rpli_state_value reward p_old)).
    - exact (rpli_sum_minus (fun s : S => mult (pi s) (reward s))
                            (fun s : S => mult (pi s) (rpli_state_value reward p_old))). }
  (* 步4：第二和项常数坍缩 Σ pi·V == V（mult_comm 逐点 + sum_linear + Hnorm） *)
  assert (H4 : req (sumf (fun s : S => mult (pi s) (rpli_state_value reward p_old)))
                   (rpli_state_value reward p_old)).
  { apply (req_trans (sumf (fun s : S => mult (pi s) (rpli_state_value reward p_old)))
                     (sumf (fun s : S => mult (rpli_state_value reward p_old) (pi s)))
                     (rpli_state_value reward p_old)).
    - apply (rpli_sum_ext (fun s : S => mult (pi s) (rpli_state_value reward p_old))
                          (fun s : S => mult (rpli_state_value reward p_old) (pi s))).
      intro s. exact (mult_comm (pi s) (rpli_state_value reward p_old)).
    - apply (req_trans (sumf (fun s : S => mult (rpli_state_value reward p_old) (pi s)))
                       (mult (rpli_state_value reward p_old) (sumf pi))
                       (rpli_state_value reward p_old)).
      + exact (rpli_sum_linear (rpli_state_value reward p_old) pi).
      + apply (req_trans (mult (rpli_state_value reward p_old) (sumf pi))
                         (mult (rpli_state_value reward p_old) one)
                         (rpli_state_value reward p_old)).
        * exact (req_mult_compat (rpli_state_value reward p_old)
                                 (rpli_state_value reward p_old)
                                 (sumf pi) one
                                 (req_refl (rpli_state_value reward p_old)) Hnorm).
        * exact (mult_one (rpli_state_value reward p_old)). }
  (* 步5：req_minus 第二分量沿 H4 运输（opp 位 req_opp_compat），δ 透明完成 *)
  assert (H5 : req (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                              (sumf (fun s : S =>
                                mult (pi s) (rpli_state_value reward p_old))))
                   (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                              (rpli_state_value reward p_old))).
  { exact (req_trans
        (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                   (sumf (fun s : S =>
                     mult (pi s) (rpli_state_value reward p_old))))
        (plus (sumf (fun s : S => mult (pi s) (reward s)))
              (opp (rpli_state_value reward p_old)))
        (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                   (rpli_state_value reward p_old))
        (req_plus_compat (sumf (fun s : S => mult (pi s) (reward s)))
                         (sumf (fun s : S => mult (pi s) (reward s)))
                         (opp (sumf (fun s : S =>
                           mult (pi s) (rpli_state_value reward p_old))))
                         (opp (rpli_state_value reward p_old))
                         (req_refl (sumf (fun s : S => mult (pi s) (reward s))))
                         (req_opp_compat (sumf (fun s : S =>
                           mult (pi s) (rpli_state_value reward p_old)))
                           (rpli_state_value reward p_old) H4))
        (req_refl (plus (sumf (fun s : S => mult (pi s) (reward s)))
                        (opp (rpli_state_value reward p_old))))). }
  apply (req_trans (rpl_is_objective_of S sumf pi p_old
                     (rpli_advantage reward p_old) Hpos)
                   (sumf (fun s : S => mult (pi s) (rpli_advantage reward p_old s)))
                   (req_minus (rpli_state_value reward pi)
                              (rpli_state_value reward p_old))).
  - exact H2.
  - exact (req_trans (sumf (fun s : S => mult (pi s) (rpli_advantage reward p_old s)))
                     (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                                (sumf (fun s : S =>
                                  mult (pi s) (rpli_state_value reward p_old))))
                     (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                                (rpli_state_value reward p_old))
                     H3 H5).
Qed.

(* ===================================================================== *)
(* 件8 rpl_ppo_clipped_improvement（Id L112439）：裁剪代理非负 ⟹ 价值改进      *)
(*   （单侧三件齐备的 req 完成；E1+E2 路线由件4 保守件替代——surrogate ≤       *)
(*   is_objective_of 一步 le_trans；深链伴件 B 换形 + req_le_of_minus_nonneg  *)
(*   @UpReqAlign L1332 完成）                                                 *)
(* ===================================================================== *)
Theorem rpl_ppo_clipped_improvement :
  forall (reward : S -> R) (eps : R),
    le zero (rpl_ppo_surrogate S sumf pi p_old
               (rpli_advantage reward p_old) eps Hpos) ->
    le (rpli_state_value reward p_old) (rpli_state_value reward pi).
Proof.
  intros reward eps Hsurr.
  assert (Hge : le zero (rpl_is_objective_of S sumf pi p_old
                           (rpli_advantage reward p_old) Hpos)).
  { apply (le_trans _ (rpl_ppo_surrogate S sumf pi p_old
                          (rpli_advantage reward p_old) eps Hpos) _).
    - exact Hsurr.
    - exact (rpl_ppo_surrogate_conservative S sumf rpli_sum_le p_old pi
               (rpli_advantage reward p_old) eps Hpos). }
  exact (req_le_of_minus_nonneg _ _
           (le_id_r _ _ _ (rpli_is_objective_value_id reward) Hge)).
Qed.

End ReqPPOPlainImprove.
