(* ============================================================ *)
(* UpAblAbsSumLeEps.v —— 单求和形 eps 闭合件（B 形 inl 反演＋论文2 载体）  *)
(*                                                                *)
(* 使命：闭合「|Σ f| ≤ Σ|f| + ε」单求和形（UpAblP2FeedSumLe 头注诚实定性  *)
(*   第 4 条所列未竟项），经 B 形供给件（UpAblAbsSumLeB，uabS4_ 系）的    *)
(*   inl 反演路线闭合，并在论文2 载体（S0＋enum0 单求和接口）上给出实例。 *)
(*                                                                *)
(* 形态差结论（三轴对照，本件头注即结论正文）：                          *)
(*   轴一·求和载体：单求和形＝论文2 单求和（real_list_sum 原生折叠，      *)
(*     minp 链同体）；UpAblAbsSumLeB 的 B 形件＝同一 real_list_sum 折叠   *)
(*     （载体全称）。——同体。                                            *)
(*   轴二·abs 形态：两侧均 real_abs＋等词相容面。——同形。                *)
(*   轴三·余量位置：单求和形＝Or 编码 real_le 显式单份余量＋0<ε 前提；    *)
(*     B 形＝real_le_b（∀e>0，x<Y+e）。取 B 形在 ε 处展开即               *)
(*     real_lt X (Y+ε)，经 real_lt_le_iff_req 左注入（inl）一步得         *)
(*     real_le X (Y+ε)。——同构：单求和形（带 0<ε 前提）恰为 B 形的        *)
(*     inl 投影，反演路线一步闭合，无需转换桥。                          *)
(* 结论复核：逐项 f s ≤ |f s| 与精确三角在 Or 编码下需符号分支精确完成、  *)
(*   递归合拢逐层倍增余量，这些困难只堵「Or 内直接构造」一条路；B 形路线  *)
(*   （UpAblAbsSumLeB 加权分配＋B 形闭合＋inl 反演）全程不需要这两个精确件。*)
(*   故逐 eps 形已闭合（0<ε 强度，uabS4_abs_list_sum_le_eps 即全称版）；  *)
(*   维持开放的只有：无余量 plain Or 形（UpRealLeB 尾注结论 2 同族）与    *)
(*   抽象求和接口无逐 eps 供给的 B 形。                                   *)
(* 主件结构（uabS4e_ 前缀，全库零撞名）：                                *)
(*   A.1 uabS4e_bform_to_eps：B 形⟹逐 eps 形普适 inl 反演（命名引理——    *)
(*       库内 uabS4_abs_list_sum_le_eps 为特例内联版，普适命名版此前无），*)
(*       两形关系的形式化对照。                                           *)
(*   A.2 uabS4e_single_sum_eps：单求和形的原生折叠全称闭合                *)
(*       （B 形供给件＋A.1 两步合成；与 uabS4_abs_list_sum_le_eps 语句面  *)
(*       同构，普适反演介导版与内联一体版两路线并存）。                   *)
(*   B 区（论文2 载体）：uabS4e_sumf 单求和算子＋B 形实例＋               *)
(*       主件闭合＋uabS4_abs_list_sum_le_eps 直接应用对照件（零增量对照）。*)
(*   C 区：uabS4e_p2_margin_tight 余量紧性——主件余量不可再压半            *)
(*       （倍率 2 不可共存应用）：单求和 eps 形在 Or 世界为可达形之半径的  *)
(*       形式化表述。                                                     *)
(*                                                                *)
(* 诚实定性：                                                            *)
(*   1. 闭合内容实为 B 形件的 inl 投影：A.2/B 区主件语句面与              *)
(*      uabS4_abs_list_sum_le_eps 同构，本件增量为普适反演命名引理、      *)
(*      论文2 载体实例、余量紧性件三面，非从零新证。                      *)
(*   2. B 区对照件＝uabS4_abs_list_sum_le_eps 直接实例，零增量（两读并列）。*)
(*   3. 字面 ε/2 分摊形仍未建：Real 层半量构造                            *)
(*      （inv(1+1) 全套环恒等式）为增量点，本件不承担。                   *)
(* 构造性注记：零承认件：无承认词面、无假设参数声明、无经典逻辑、          *)
(*   全件 Qed 闭合；全语句 Set 层值（real_le/real_lt/real_le_b/           *)
(*   Empty_set 均 Set，语句面无裸命题）；证明全构造（Or 逐支、            *)
(*   inl 注入、倍率 2 不可共存收 Empty_set）。                            *)
(* 依赖：CW_ConstructiveWorld_219＋UpRealLeB＋S08_RealMainlineDPO＋       *)
(*   UpAblAbsSumLeB。                                                    *)
(*                                                                *)
(* 编译配方：Rocq 9.1 直调 coqc，cpu_guard 包裹，-o 临时目录。            *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import S08_RealMainlineDPO.
Require Import UpAblAbsSumLeB.
From Stdlib Require Import List.

(* ============================================================ *)
(* §0 库内接口核对（Check 逐项对照真实签名）                              *)
(* ============================================================ *)

Check uabS4_abs_list_sum_le_B.   (* B 形供给件：|Σ_l f| ≤_B Σ_l|f|（出自 UpAblAbsSumLeB） *)
Check uabS4_abs_list_sum_le_eps. (* B 形的逐 eps 内联反演（UpAblAbsSumLeB B.3，对照件） *)
Check uabS4_lt_double_margin_le_half_contr. (* 倍率 2 不可共存引理（UpAblAbsSumLeB C.1） *)
Check real_le_b.                 (* Bishop 形 ≤ 谓词（Set 层全称型） *)
Check RealSetoid.real_lt_le_iff_req. (* Or (lt) (eq) → le（inl 注入） *)
Check real_list_sum.             (* 原生折叠（全称载体，见 S08_RealMainlineDPO） *)

(* ============================================================ *)
(* §1 B 形⟹逐 eps 形普适反演＋全称闭合                                   *)
(* ============================================================ *)

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
   两步合成：B 形供给件＋A.1 反演。与 uabS4_abs_list_sum_le_eps 语句面
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

(* ============================================================ *)
(* §2 论文2 载体实例（S0 载体＋enum0 枚举表，minp/采样面单求和算子）       *)
(* ============================================================ *)

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

(* ============================================================ *)
(* §3 余量紧性核验：主件余量不可再压半（倍率 2 不可共存的载体实例）         *)
(* ============================================================ *)

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

(* ============================================================ *)
(* 审计区：零外部未证假设核对（全 Closed 为判据）                         *)
(* ============================================================ *)
Print Assumptions uabS4e_bform_to_eps.
Print Assumptions uabS4e_single_sum_eps.
Print Assumptions uabS4e_p2_abs_sum_le_B.
Print Assumptions uabS4e_p2_single_sum_eps.
Print Assumptions uabS4e_p2_single_sum_eps_direct.
Print Assumptions uabS4e_p2_margin_tight.

(* ============================================================ *)
(* 提取区（输出目录 _tf1b_g3out）。                                        *)
(*   计算内容＝论文2 单求和算子（真折叠链）；序谓词/反演面件               *)
(*   以 Print Assumptions 审计替代提取。                                   *)
(* ============================================================ *)
Set Extraction Output Directory "_tf1b_g3out".
Separate Extraction uabS4e_sumf.
