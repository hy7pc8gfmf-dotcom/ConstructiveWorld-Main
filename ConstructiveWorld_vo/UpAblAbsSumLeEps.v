(* ============================================================ *)
(* UpAblAbsSumLeEps.v —— F1B 席：单求和形 eps 回收闭合件              *)
(*   （F1 判墙族的 B 形 inl 回收收口＋论文2 槽位直配），20260920       *)
(* ============================================================ *)
(* 【使命】闭合 F1 席显式申报的未竟项——单求和形                        *)
(*   「|Σ f| ≤ Σ|f| + ε」（UpAblP2FeedSumLe 头注诚实定性第 4 条＋      *)
(*   _tf1 报告形态差申报第 1 条），消费 S4 席 B 形供给件                *)
(*   （UpAblAbsSumLeB，uabS4_ 系四关绿）经 inl 回收路线闭合，           *)
(*   并在论文2 载体（S0＋enum0 单求和槽）上给直配件。新独立件。         *)
(* 【第一步·形态差定谳（对表三轴，本件头注即定谳正文）】                *)
(*   轴一·求和载体：F1 形=论文2 单求和（real_list_sum 原生折叠，        *)
(*     minp 链同体）；S4 B 形件=同一 real_list_sum 折叠（载体全称）。    *)
(*     ——同体。                                                       *)
(*   轴二·abs 形态：两侧均 real_abs＋等词相容面。——同形。               *)
(*   轴三·余量位置：F1 形=Or 编码 real_le 显式单份余量＋0<ε 前提；      *)
(*     S4 B 形=real_le_b（∀e>0，x<Y+e）。取 B 形在 ε 处展开即          *)
(*     real_lt X (Y+ε)，经 real_lt_le_iff_req 左注入（inl）一步得       *)
(*     real_le X (Y+ε)。——同构：F1 形（带 0<ε 前提）恰为 B 形的        *)
(*     inl 投影，回收路线一步闭合，无需转换桥。                          *)
(* 【定谳复核（F1 判词）】F1 所列堵点（逐项 f s ≤ |f s| 与精确三角      *)
(*   在 Or 编码下需符号分支精确完成；递归合拢逐层倍增余量）只堵          *)
(*   「Or 内直接构造」一条路；B 形绕道（S4 加权账目＋末端完成＋          *)
(*   inl 回收）全程不需要这两个精确件。故 F1「未闭合」判词收窄为：       *)
(*   逐 eps 形已闭合（0<ε 强度，S4 B.3 即全称版）；维持冻结的只有       *)
(*   无余量 plain Or 形（UpRealLeB 尾注结论 2 同族墙）与抽象求和槽位    *)
(*   无逐 eps 供给的 B 形（S4 报告未竟第 2 条）。                       *)
(* 【主件结构（uabS4e_ 前缀，全库实扫零撞名）】                          *)
(*   A.1 uabS4e_bform_to_eps：B 形⟹逐 eps 形普适 inl 反演（新命名       *)
(*       引理——库内 S4 B.3 为特例内联版，普适命名版此前无），           *)
(*       两形关系的形式化对照。                                         *)
(*   A.2 uabS4e_single_sum_eps：F1 判墙形的原生折叠全称收口              *)
(*       （S4 B 形件＋A.1 两步装配；与 S4 B.3 语句面同构，               *)
(*       普适反演介导版与内联一体版两路线并存）。                        *)
(*   B 区（论文2 槽位）：uabS4e_sumf 单求和算子槽＋B 形槽位直配＋        *)
(*       主件槽位收口＋S4 B.3 直喂对照件（零增量对照如实申报）。         *)
(*   C 区：uabS4e_p2_margin_tight 余量紧性对账——主件余量不可再压半       *)
(*       （倍率 2 双杀消费 S4 C.1）：单求和 eps 形为 Or 世界可达形之     *)
(*       半径账的形式化收口。                                           *)
(* 【诚实定性（红线三）】                                                *)
(*   1. 闭合内容实为 S4 B 形件的 inl 投影：A.2/B 区主件语句面与          *)
(*      S4 B.3 同构，本席增量在普适反演命名引理、论文2 槽位直配、        *)
(*      紧性对账件三面，非从零新证，如实申报。                           *)
(*   2. B 区对照件=S4 B.3 直接实例，零增量对照申报（两读并列）。          *)
(*   3. 字面 ε/2 分摊形（F1 升级方向原案）仍未建：Real 层半量簿记        *)
(*      （inv(1+1) 全套环账）为增量点，本席不冒报。                      *)
(* 【红线自检】零承认件：无承认词面、无假设槽位声明、无经典逻辑、        *)
(*   全件 Qed 闭合；全语句 Set 层值（real_le/real_lt/real_le_b/         *)
(*   Empty_set 均 Set，语句面无裸命题）；证明全构造（Or 逐支、           *)
(*   inl 注入、双杀直构收 Empty_set）；禁碰 UpAblAbsSumLeB/              *)
(*   UpAblP2FeedSumLe/任何既有文件；禁入 order.txt/_CoqProject           *)
(*   （注册归主会话）。                                                  *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import S08_RealMainlineDPO.
Require Import UpAblAbsSumLeB.
From Stdlib Require Import List.

(* ============================================================ *)
(* Part 0 · 供给件在库打表（签名漂移即响亮失败）                          *)
(* ============================================================ *)

Check uabS4_abs_list_sum_le_B.   (* S4 B.2：|Σ_l f| ≤_B Σ_l|f|（B 形供给件） *)
Check uabS4_abs_list_sum_le_eps. (* S4 B.3：B 形的逐 eps 内联回收（对照 twin） *)
Check uabS4_lt_double_margin_le_half_contr. (* S4 C.1：倍率 2 双杀引理 *)
Check real_le_b.                 (* Bishop 形 ≤ 谓词（Set 层全称型） *)
Check RealSetoid.real_lt_le_iff_req. (* Or (lt) (eq) → le（inl 回收门） *)
Check real_list_sum.             (* S08:288 原生折叠（全称载体） *)

(* ============================================================ *)
(* Part A · 形态差定谳的形式面：B 形⟹逐 eps 形普适反演＋全称收口          *)
(* ============================================================ *)

(* A.1 普适 inl 反演：B 形 x ≤_B y 在 e>0 处展开为 x < y+e，
   经 real_lt_le_iff_req 左注入收 real_le x (y+e)。
   库内 S4 B.3 为本引理在 abs 和形上的内联特例；普适命名版此前无。
   （注：无余量版「B 形 ⟹ Or 形」构造性不可证，UpRealLeB 尾注
   结论 2 在案——本引理的 e>0 前提正是可达与冻结的分界线。） *)
Lemma uabS4e_bform_to_eps : forall x y e : Real,
  real_lt real_zero e ->
  real_le_b x y ->
  real_le x (real_plus y e).
Proof.
  intros x y e He Hb.
  apply (RealSetoid.real_lt_le_iff_req x (real_plus y e)). apply inl.
  exact (Hb e He).
Qed.

(* A.2 F1 判墙形的全称收口：|Σ_l f| ≤ Σ_l|f| + e（0<e，载体全称）。
   两步装配：S4 B 形件供给＋A.1 回收。与 S4 B.3 语句面同构
   （普适反演介导版 vs 内联一体版，两路线并存）。 *)
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
(* Part B · 论文2 槽位直配（S0 载体＋enum0 枚举表，minp/采样面单求和槽）   *)
(* ============================================================ *)

Section P2EpsCarrier.

Context (S0 : Set).
Context (enum0 : list S0).

(* 论文2 单求和算子槽：原生折叠（minp 链同体，非适配包装）。 *)
Definition uabS4e_sumf (f : S0 -> Real) : Real := real_list_sum S0 f enum0.

(* B.1 B 形槽位直配：|Σ_enum f| ≤_B Σ_enum|f|。 *)
Theorem uabS4e_p2_abs_sum_le_B : forall f : S0 -> Real,
  real_le_b (real_abs (uabS4e_sumf f))
            (uabS4e_sumf (fun x => real_abs (f x))).
Proof.
  intros f. exact (uabS4_abs_list_sum_le_B S0 f enum0).
Qed.

(* B.2 主件（F1 判墙形的论文2 槽位直配收口）：
   |Σ_enum f| ≤ Σ_enum|f| + ε（0<ε，对整个枚举表单求和一次收口）。 *)
Theorem uabS4e_p2_single_sum_eps : forall (f : S0 -> Real) (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (uabS4e_sumf f))
          (real_plus (uabS4e_sumf (fun x => real_abs (f x))) eps).
Proof.
  intros f eps Heps.
  apply (uabS4e_bform_to_eps _ _ eps Heps).
  exact (uabS4e_p2_abs_sum_le_B f).
Qed.

(* B.3 对照件（零增量对照申报）：S4 B.3 直接实例——与 B.2 语句面
   逐字重合（uabS4e_sumf 定义性展开即原生折叠），两读并列：
   槽位反演介导路线 vs 上游全称件直供路线。 *)
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
(* Part C · 余量紧性对账：主件余量不可再压半（倍率 2 双杀槽位实例）         *)
(* ============================================================ *)

(* 若声称比主件好一倍的严格形 Σ|f| + (ε+ε) < |Σ f|，与逐 eps 主件
   （|Σ f| ≤ Σ|f| + ε）经 S4 C.1 即刻双杀——单求和 eps 形的余量
   在 Or 世界不可再对半压，半径账的形式化收口。 *)
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
(* 证据区：零外部未证假设审计（全 Closed 为过关判据）                     *)
(* ============================================================ *)
Print Assumptions uabS4e_bform_to_eps.
Print Assumptions uabS4e_single_sum_eps.
Print Assumptions uabS4e_p2_abs_sum_le_B.
Print Assumptions uabS4e_p2_single_sum_eps.
Print Assumptions uabS4e_p2_single_sum_eps_direct.
Print Assumptions uabS4e_p2_margin_tight.

(* ============================================================ *)
(* G3 提取区（一人一目录 _tf1b_g3out；单条命令合并）。                    *)
(*   计算内容＝论文2 单求和算子槽（真折叠链）；序谓词/回收面件           *)
(*   以 Print Assumptions 审计替代提取（F1/S4 先例同口径）。             *)
(* ============================================================ *)
Set Extraction Output Directory "_tf1b_g3out".
Separate Extraction uabS4e_sumf.
