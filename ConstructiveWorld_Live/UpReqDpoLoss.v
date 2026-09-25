(* ============================================================ *)
(* UpReqDpoLoss.v *)
(* *)
(* 目的： DPO 损失的 req 层折叠与最优点刻画。 *)
(* 主件： rdl_dpo_total_loss_at_star / rdl_dpo_total_loss_star_characterization 最优点刻画。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqAlign、UpReqAlignRestA。 *)
(* 备注： 奖励、温度与逐点正性为 Variable 前提；折叠外延性 rdl_fold_plus_ext 为构造核。 *)
(* ============================================================ *)

(* UpReqDpoLoss.v — 批5 完成行动清单第 2 项：dpo_total_loss 簇解冻评估（可行）+ 建设
   冻结结论（UpReqAlignRestA.v 头注区3）：“total_loss 簇冻结（fold_right_ext 载体，
     _monotone/_star_characterization (d) 冻结（fold 载体 + nat/list 层 Id 双层并行）。
   ----------------------------------------------------------------
   判定书（解冻依据，证据坐标）：
   1. 冻结前提已消失：其注记「待 dpo_pair_loss 簇 req 化后随批4」——RestA 已结果
     ralt_dpo_pair_loss/ralt_dpo_pair_loss_star/ralt_dpo_pair_loss_at_star
     （UpReqAlignRestA.v L404-462，.vo 出口签名已检验实证）。
   2. 载体形路径：Id 泛型 fold_right_ext（L20160，{A B : Set} 全称形）的 req
     伴件不可直建——req 接口无通用 id_cong 字段（函数外延性敏感件，(d) 冻结维持）。
     ："逐点 req 前提版，语义无变动不冻结"）：fold 递归载体直接归纳，
     rdl_fold_plus_ext_on（InT 限制形，主件）+ rdl_fold_plus_ext（全称形推论）。
   3. 结论：total_loss 簇 3 件全部解冻建成为真证（本文件）；Id 泛型 fold_right_ext
     (d) 冻结维持（泛型形需任意 g 的 compat 场，接口不可表达——诚实边界在案）。
   ----------------------------------------------------------------
   上游（全部 .vo 态使用，开节源码不重编）：CW_ConstructiveWorld_219（基座：
     dpo_total_loss L20152/dpo_total_loss_star L20155/fold_right_ext L20160/
     dpo_total_loss_at_star L20171/dpo_total_loss_monotone L20181/
     dpo_total_loss_star_characterization L20199/InT L99）+ UpReqAlgebra（req_minus/
     req 系代数）+ UpReqAlign（req_pi_star_pos 系）+ UpReqAlignRestA（ralt_* 出口）。
   诚实签名变化登记表（规划书 §7.4 沿用 RestA 决定）：
   1. rdl_pair/rdl_pair req 化携带 Hpi 逐点正性见证位（log 前提化，RestA 登记表 1）。
   2. monotone 逐点前提 le 形与 Id 同位；Hpi1/Hpi2 见证位为诚实新增。
   3. fold 外延件 (b) 化逐点改述（先例：u2_kl_arg2_ext）；InT 限制形为
     characterization 的诚实对偶（Id 原件 L20199 逐元素 InT 供给形）。
   4. 桥假设位自持（RestA 同形，各席自持纪律）：rdl_log_req_compat /
     rdl_log_inv_exp_neg_req；节闭后随件出参，使用以 .vo 出口签名为准
   Set 层语句（req/lt/le 均 Set 值，零 Prop 泄露）；纯 term-mode（req_trans 链 +
     compat 桥），零模性等变结构依赖（禁词扫描全零面）。
   ---------------------------------------------------------------- *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import UpReqAlignRestA.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* ReqDpoLossCore：total_loss 簇 req 化主体节                      *)
(*   （节参数与 RestA ReqRestACore 逐位对齐 + pref_dataset 第十参） *)
(* ============================================================ *)
Section ReqDpoLossCore.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
(* T4R2 扩位（既有节签调整后）：RestA ralt_pistar 系新出节签 sum_pos 位（T5 既成刀面
   同形）；Z_align_pos 槽保留（ralt_dpo_pair_loss_at_star 出节签仍在用）。 *)
Hypothesis rdl_sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable Z_align_pos : lt zero (Z_align_req S sumf reward beta beta_pos pi_ref).
(* ---- 桥假设位（RestA 同形自持；批 1 ReqLogBridge 接口缺口桥同位） ---- *)
Hypothesis rdl_log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Hypothesis rdl_log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Variable Preference : Set.
Variable pref_win : Preference -> S.
Variable pref_lose : Preference -> S.
Variable pref_dataset : list Preference.

(* ---- δ 透明薄包装（U2 主体同款纪律；出参对齐 RestA .vo 出口签名） ---- *)
Definition rdl_pair (pi : S -> R) (Hpi : forall s : S, lt zero (pi s))
           (pref : Preference) : R :=
  ralt_dpo_pair_loss S beta pi_ref pi_ref_pos Preference pref_win pref_lose
                     pi Hpi pref.

Definition rdl_pair_star (pref : Preference) : R :=
  ralt_dpo_pair_loss_star S reward Preference pref_win pref_lose pref.

Definition rdl_diff (pi : S -> R) (Hpi : forall s : S, lt zero (pi s))
           (pref : Preference) : R :=
  ralt_implicit_reward_diff S beta pi_ref pi_ref_pos Preference pref_win pref_lose
                            pi Hpi pref.

Definition rdl_diff_star (pref : Preference) : R :=
  req_minus (reward (pref_win pref)) (reward (pref_lose pref)).

Definition rdl_pistar : S -> R :=
  ralt_pistar S sumf rdl_sum_pos reward beta beta_pos pi_ref pi_ref_pos.

Definition rdl_pistar_pos : forall s : S, lt zero (rdl_pistar s) :=
  ralt_pistar_pos S sumf rdl_sum_pos reward beta beta_pos pi_ref pi_ref_pos.

(* ============ 主件 1：fold 外延 req 载体（(b) 化逐点改述） ============ *)

(* InT 限制形：逐元素 req 前提 ⟹ fold 全体 req。真证：list 归纳 +
   req_plus_compat 双腿链（头元素换形 + 尾栈归纳运输），零函数外延性。
   （Id 泛型 fold_right_ext L20160 的 DPO 实例 req 同位；先例 u2_kl_arg2_ext） *)
Lemma rdl_fold_plus_ext_on :
  forall (f g : Preference -> R) (l : list Preference),
    (forall a, InT a l -> req (f a) (g a)) ->
    req (fold_right (fun p acc => plus (f p) acc) zero l)
        (fold_right (fun p acc => plus (g p) acc) zero l).
Proof.
  intros f g l Hpt.
  induction l as [| p rest IH]; simpl.
  - exact (req_refl zero).
  - apply (req_trans
             (plus (f p) (fold_right (fun p0 acc => plus (f p0) acc) zero rest))
             (plus (g p) (fold_right (fun p0 acc => plus (f p0) acc) zero rest))
             (plus (g p) (fold_right (fun p0 acc => plus (g p0) acc) zero rest))).
    + exact (req_plus_compat (f p) (g p)
               (fold_right (fun p0 acc => plus (f p0) acc) zero rest)
               (fold_right (fun p0 acc => plus (f p0) acc) zero rest)
               (Hpt p (InT_here p rest))
               (req_refl (fold_right (fun p0 acc => plus (f p0) acc) zero rest))).
    + exact (req_plus_compat (g p) (g p)
               (fold_right (fun p0 acc => plus (f p0) acc) zero rest)
               (fold_right (fun p0 acc => plus (g p0) acc) zero rest)
               (req_refl (g p))
               (IH (fun a Hin => Hpt a (InT_next a p rest Hin)))).
Qed.

(* 全称形推论：无 InT 限制的逐点前提版（at_star 使用形；1 行直推） *)
Lemma rdl_fold_plus_ext :
  forall (f g : Preference -> R) (l : list Preference),
    (forall a, req (f a) (g a)) ->
    req (fold_right (fun p acc => plus (f p) acc) zero l)
        (fold_right (fun p acc => plus (g p) acc) zero l).
Proof.
  intros f g l Hpt.
  exact (rdl_fold_plus_ext_on f g l (fun a _ => Hpt a)).
Qed.

(* ============ 定义：总损失 = 单对损失的 fold（基座 L20152/20155 同形） ============ *)

Definition rdl_dpo_total_loss (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) : R :=
  fold_right (fun pref acc => plus (rdl_pair pi Hpi pref) acc) zero pref_dataset.

Definition rdl_dpo_total_loss_star : R :=
  fold_right (fun pref acc => plus (rdl_pair_star pref) acc) zero pref_dataset.

(* ============ 辅件：单对损失 req 外延（前提版；characterization 使用） ============ *)

(* 逐点差分 req 前提 ⟹ 单对损失 req。真证：log 缺口桥 + one 同位 +
   exp_neg 兼容（ralt_dpo_pair_loss_at_star RestA L448 的前提版改述） *)
Lemma rdl_pair_loss_ext :
  forall (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (pref : Preference),
    req (rdl_diff pi Hpi pref) (rdl_diff_star pref) ->
    req (rdl_pair pi Hpi pref) (rdl_pair_star pref).
Proof.
  intros pi Hpi pref Hdiff.
  unfold rdl_pair, rdl_pair_star, ralt_dpo_pair_loss, ralt_dpo_pair_loss_star.
  apply rdl_log_req_compat.
  exact (req_plus_compat one one
           (exp_neg (rdl_diff pi Hpi pref))
           (exp_neg (rdl_diff_star pref))
           (req_refl one)
           (exp_neg_req_compat_setoid (rdl_diff pi Hpi pref)
                                      (rdl_diff_star pref) Hdiff)).
Qed.

(* ============ 主件 2：π* 处总损失 = 显式常数（基座 L20171 同位） ============ *)

Theorem rdl_dpo_total_loss_at_star :
  req (rdl_dpo_total_loss rdl_pistar rdl_pistar_pos) rdl_dpo_total_loss_star.
Proof.
  unfold rdl_dpo_total_loss, rdl_dpo_total_loss_star.
  apply (rdl_fold_plus_ext_on (rdl_pair rdl_pistar rdl_pistar_pos)
                              rdl_pair_star pref_dataset).
  intros a Hin.
  unfold rdl_pair, rdl_pair_star.
  exact (ralt_dpo_pair_loss_at_star S sumf rdl_sum_pos reward beta beta_pos
           pi_ref pi_ref_pos Z_align_pos rdl_log_req_compat
           rdl_log_inv_exp_neg_req Preference pref_win pref_lose a).
Qed.

(* ============ 主件 3：总损失单调性（基座 L20181 同位） ============ *)

Theorem rdl_dpo_total_loss_monotone :
  forall (pi1 pi2 : S -> R)
         (Hpi1 : forall s : S, lt zero (pi1 s))
         (Hpi2 : forall s : S, lt zero (pi2 s)),
    (forall pref, InT pref pref_dataset ->
       le (rdl_pair pi2 Hpi2 pref) (rdl_pair pi1 Hpi1 pref)) ->
    le (rdl_dpo_total_loss pi2 Hpi2) (rdl_dpo_total_loss pi1 Hpi1).
Proof.
  intros pi1 pi2 Hpi1 Hpi2 Hpt.
  unfold rdl_dpo_total_loss.
  induction pref_dataset as [| p rest IH]; simpl.
  - apply le_refl.
  - apply le_plus_compat.
    + exact (Hpt p (InT_here p rest)).
    + apply IH. intros pref Hin. exact (Hpt pref (InT_next pref p rest Hin)).
Qed.

(* ============ 主件 4：π* 处局部最优性刻画（基座 L20199 同位） ============ *)

Theorem rdl_dpo_total_loss_star_characterization :
  forall (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)),
    (forall pref, InT pref pref_dataset ->
       req (rdl_diff pi Hpi pref) (rdl_diff_star pref)) ->
    req (rdl_dpo_total_loss pi Hpi) rdl_dpo_total_loss_star.
Proof.
  intros pi Hpi Heq.
  unfold rdl_dpo_total_loss, rdl_dpo_total_loss_star.
  apply (rdl_fold_plus_ext_on (rdl_pair pi Hpi) rdl_pair_star pref_dataset).
  intros a Hin.
  apply rdl_pair_loss_ext.
  exact (Heq a Hin).
Qed.

End ReqDpoLossCore.

(* ----------------------------------------------------------------
   - 结果 6 件：rdl_fold_plus_ext_on（主件，(b) 化逐点 req 载体）+
     rdl_fold_plus_ext（全称形推论）+ rdl_pair_loss_ext（前提版辅件）+
     rdl_dpo_total_loss_at_star / rdl_dpo_total_loss_monotone /
     rdl_dpo_total_loss_star_characterization（簇 3 件真证）。
     另 δ 透明薄包装 6（rdl_pair/_star/_diff/_diff_star/_pistar/_pistar_pos）
     与定义 2（rdl_dpo_total_loss/_star）不计件数。
   - Id 泛型 fold_right_ext（L20160）(d) 冻结维持：泛型 {A B} 形需任意
     fold 函数的 compat 场，req 接口不可表达（函数外延性敏感边界在案）；
     DPO 实例形已由本件 (b) 化完成。
   - 使用入口：Require Import UpReqDpoLoss.
   ---------------------------------------------------------------- *)
