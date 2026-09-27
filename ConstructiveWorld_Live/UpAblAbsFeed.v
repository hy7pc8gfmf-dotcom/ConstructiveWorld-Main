(* ==========================================================================)
   UpAblAbsFeed.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：uabS4e_bform_to_eps、uabS4e_single_sum_eps、uabS4e_sumf、uabS4e_p2_abs_sum_le_B、uabS4e_p2_single_sum_eps、uabS4e_p2_single_sum_eps_direct、uabS4e_p2_margin_tight、uabf_kv_abs_triangle_list_eps、uabf_kv_abs_triangle_list_B。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import Extraction.
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
Require Import UpAblAbsSumLeB.
From Stdlib Require Import List.
Require Import UpAblAbsSumLeB2.

(* ================= §1 uabS4e_bform_to_eps 族 ================= *)
(* §0 库内接口核对（Check 逐项对照真实签名）                              *)

Check uabS4_abs_list_sum_le_B.   (* B 形依赖模块：|Σ_l f| ≤_B Σ_l|f|（出自 UpAblAbsSumLeB） *)
Check uabS4_abs_list_sum_le_eps. (* B 形的逐 eps 内联反演（UpAblAbsSumLeB B.3，对照件） *)
Check uabS4_lt_double_margin_le_half_contr. (* 倍率 2 不可共存引理（UpAblAbsSumLeB C.1） *)
Check real_le_b.                 (* Bishop 形 ≤ 谓词（Set 层全称型） *)
Check RealSetoid.real_lt_le_iff_req. (* Or (lt) (eq) → le（inl 注入） *)
Check real_list_sum.             (* 原生折叠（全称载体，见 S08_RealMainlineDPO） *)

(* §1 B 形⟹逐 eps 形普适反演＋全称闭合                                   *)

(* A.1 普适 inl 反演：B 形 x ≤_B y 在 e>0 处展开为 x < y+e，
   经 real_lt_le_iff_req 左注入收 real_le x (y+e)。
   库内 uabS4_abs_list_sum_le_eps 为本引理在 abs 和形上的内联特例；
   普适命名版此前无。（注：无余量版「B 形 ⟹ Or 形」构造性不可证，
   UpRealLeB 尾注结论 2 在案——本引理的 e>0 前提正是可达与开放问题的分界线。） *)
Lemma uabS4e_bform_to_eps : forall x y e : Real,
  real_lt real_zero e ->
  real_le_b x y ->
  real_le x (real_plus y e).
Proof.
  intros x y e He Hb.
  apply (RealSetoid.real_lt_le_iff_req x (real_plus y e)). apply inl.
  exact (Hb e He).
Qed.

(* A.2 单求和形的全称闭合：|Σ_l f| ≤ Σ_l|f| + e（0<e，载体全称）。
   两步合成：B 形依赖模块＋A.1 反演。与 uabS4_abs_list_sum_le_eps 语句面
   同构（普适反演介导版 vs 内联一体版，两路线并存）。 *)
Theorem uabS4e_single_sum_eps : forall (X : Type) (f : X -> Real) (l : list X)
                                       (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x => real_abs (f x)) l) e).
Proof.
  intros X f l e He.
  apply (uabS4e_bform_to_eps _ _ e He).
  exact (uabS4_abs_list_sum_le_B X f l).
Qed.

(* §2 论文2 载体实例（S0 载体＋enum0 枚举表，minp/采样面单求和算子）       *)

Section P2EpsCarrier.

Context (S0 : Set).
Context (enum0 : list S0).

(* 论文2 单求和算子：原生折叠（minp 链同体，非适配层）。 *)
Definition uabS4e_sumf (f : S0 -> Real) : Real := real_list_sum S0 f enum0.

(* B.1 B 形实例：|Σ_enum f| ≤_B Σ_enum|f|。 *)
Theorem uabS4e_p2_abs_sum_le_B : forall f : S0 -> Real,
  real_le_b (real_abs (uabS4e_sumf f))
            (uabS4e_sumf (fun x => real_abs (f x))).
Proof.
  intros f. exact (uabS4_abs_list_sum_le_B S0 f enum0).
Qed.

(* B.2 主件（单求和形的论文2 载体闭合）：
   |Σ_enum f| ≤ Σ_enum|f| + ε（0<ε，对整个枚举表单求和一次闭合）。 *)
Theorem uabS4e_p2_single_sum_eps : forall (f : S0 -> Real) (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (uabS4e_sumf f))
          (real_plus (uabS4e_sumf (fun x => real_abs (f x))) eps).
Proof.
  intros f eps Heps.
  apply (uabS4e_bform_to_eps _ _ eps Heps).
  exact (uabS4e_p2_abs_sum_le_B f).
Qed.

(* B.3 对照件（零增量对照）：uabS4_abs_list_sum_le_eps 直接实例——与 B.2 语句面
   逐字重合（uabS4e_sumf 定义性展开即原生折叠），两读并列：
   反演介导路线 vs 上游全称件直接给出路线。 *)
Theorem uabS4e_p2_single_sum_eps_direct : forall (f : S0 -> Real) (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (uabS4e_sumf f))
          (real_plus (uabS4e_sumf (fun x => real_abs (f x))) eps).
Proof.
  intros f eps Heps.
  exact (uabS4_abs_list_sum_le_eps S0 f enum0 eps Heps).
Qed.

End P2EpsCarrier.

(* §3 余量紧性核验：主件余量不可再压半（倍率 2 不可共存的载体实例）         *)

(* 若声称比主件好一倍的严格形 Σ|f| + (ε+ε) < |Σ f|，与逐 eps 主件
   （|Σ f| ≤ Σ|f| + ε）经倍率 2 不可共存引理即刻矛盾——单求和 eps 形的余量
   在 Or 世界不可再对半压，此半径界的形式化表述。 *)
Theorem uabS4e_p2_margin_tight : forall (S0 : Set) (enum0 : list S0)
                                        (f : S0 -> Real) (eps : Real),
  real_lt real_zero eps ->
  real_lt (real_plus (real_list_sum S0 (fun x => real_abs (f x)) enum0)
                     (real_plus eps eps))
          (real_abs (real_list_sum S0 f enum0)) ->
  Empty_set.
Proof.
  intros S0 enum0 f eps Heps Hfar.
  exact (uabS4_lt_double_margin_le_half_contr
           (real_abs (real_list_sum S0 f enum0))
           (real_list_sum S0 (fun x => real_abs (f x)) enum0)
           eps Heps Hfar
           (uabS4_abs_list_sum_le_eps S0 f enum0 eps Heps)).
Qed.

(* 审计区：零外部未证假设核对（全 Closed 为判据）                         *)
Print Assumptions uabS4e_bform_to_eps.
Print Assumptions uabS4e_single_sum_eps.
Print Assumptions uabS4e_p2_abs_sum_le_B.
Print Assumptions uabS4e_p2_single_sum_eps.
Print Assumptions uabS4e_p2_single_sum_eps_direct.
Print Assumptions uabS4e_p2_margin_tight.

(* 提取区（输出目录 _tf1b_g3out）。                                        *)
(*   计算内容＝论文2 单求和算子（真折叠链）；序谓词/反演面件               *)
(*   以 Print Assumptions 审计替代提取。                                   *)
Set Extraction Output Directory "_tf1b_g3out".
Separate Extraction uabS4e_sumf.
(* ================= §2 uabf_kv_abs_triangle_list_ep 族 ================= *)
(* §1 · 供体引理在库核对：以下 Check 逐一确认供体签名在库                 *)

Check uabS4_abs_list_sum_le_B.    (* B 形：|Σ_l f| ≤_B Σ_l |f|（real_le_b 版） *)
Check uabS4_abs_list_sum_le_eps.  (* 逐 eps 全称：0 < eps ⟹ |Σ_l f| ≤ Σ_l |f| + eps *)
Check uabS4b_slot_abs_sum_le_B.   (* 抽象求和接口下的 B 形（供 uabf_kv_abs_triangle_list_B 实例化） *)
Check uabS4e_bform_to_eps.        (* 提升引理：B 形与 0 < eps ⟹ 逐 eps 形 *)
Check real_list_sum.              (* 表和定义：nil 归 real_zero，cons 递归求和 *)

(* §2 · 逐 eps 形主推论：|Σ_l f| ≤ Σ_l |f| + eps（0 < eps）              *)

Corollary uabf_kv_abs_triangle_list_eps : forall (X : Set) (f : X -> Real)
  (l : list X) (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x : X => real_abs (f x)) l) eps).
Proof.
  intros X f l eps Heps.
  exact (uabS4_abs_list_sum_le_eps X f l eps Heps).
Qed.

(* §3 · 第二路线：B 形推论与经 uabS4e_bform_to_eps 的提升                *)

(* uabf_kv_abs_triangle_list_B：将表和 real_list_sum 代入
   uabS4b_slot_abs_sum_le_B 的抽象求和接口——nil 与 cons 两方程均定义性成立，B 形直接推得。 *)
Corollary uabf_kv_abs_triangle_list_B : forall (X : Type) (f : X -> Real)
  (l : list X),
  real_le_b (real_abs (real_list_sum X f l))
            (real_list_sum X (fun x : X => real_abs (f x)) l).
Proof.
  intros X f l.
  exact (uabS4b_slot_abs_sum_le_B X (real_list_sum X)
           (fun f0 => real_eq_refl real_zero)
           (fun f0 w rest =>
              real_eq_refl (real_plus (f0 w) (real_list_sum X f0 rest)))
           f l).
Qed.

(* uabf_kv_abs_triangle_list_eps_slotroute：由 B 形经 uabS4e_bform_to_eps
   提升为逐 eps 形，与 uabf_kv_abs_triangle_list_eps 结论相同、证明路线不同。 *)
Corollary uabf_kv_abs_triangle_list_eps_slotroute :
  forall (X : Type) (f : X -> Real) (l : list X) (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x : X => real_abs (f x)) l) eps).
Proof.
  intros X f l eps Heps.
  apply (uabS4e_bform_to_eps _ _ eps Heps).
  exact (uabf_kv_abs_triangle_list_B X f l).
Qed.

(* §4 · 假设审计：三条结论的 Print Assumptions 应全为 Closed              *)
Print Assumptions uabf_kv_abs_triangle_list_eps.
Print Assumptions uabf_kv_abs_triangle_list_B.
Print Assumptions uabf_kv_abs_triangle_list_eps_slotroute.
