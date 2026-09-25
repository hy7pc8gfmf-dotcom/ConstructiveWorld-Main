(* ========================================================================= *)
(*                                                                           *)
(* Require 面                                                                *)
(* 替换定理清单：rotc_perm／rotc_length／Pinf_c_perm／rotc_0／Pinf_true_id   *)
(* ／rotc_in／rotc_H_wit_mid／rotc_H_wit_min／Hsup_cyc_stable_wit／          *)
(* Hsup_cyc_frozen_value_wit／H_lam_pmid_wit_201_ends／                      *)
(* rotc_supersedes_rot_id（共 12 刀）                                        *)
(* 分式假非平凡。                                                            *)
(* 本稿零公理、零承认件、全封口、纯构造性、无经典逻辑；落件时与本次补标      *)
(* 抽验编译均验零承认。                                                      *)
(* ========================================================================= *)
(* ============================================================
   DTPT_Rotation.v — 旋转论：rotc 底座/精确闭式/锐化/λ 插值/偏差判别/
   周期律簇
   （U8 件新建；M5 归并件并入 DTPT_HsupStable.v 后定形；S5 棒并入
   DTPT_ROTC.v；S6a 棒并入 DTPT_RotSpec.v 与 DTPT_Lam.v；S6b 棒改名
   DTPT_Rotation.v 完成，DTPT_ROTC/DTPT_Entropy2 随棒退役）
   ── 标准六字段头 ──
   【一·职责】
     §0-§8（U8 原面）：firstn/skipn 保序 + rotc_two_runs 双升序段分解 +
     H_adj_app_seam 接缝分解 + H_adj (rotc k l) 三项 Qeq 精确闭式（含
     k=0 / k≥表长 / 短表边界与二分合成）+ 3·spread 上界（H_adj_rotc_ub3）
     + qmax2 真动态上确界 Hsup_cyc（单调/界/达到性）+ 数值锚 [0;1;2]。
     §M5-1 起（HsupStable 并入面）：切段四件套 + 局部周期律诚实版
     （守卫加法律/冻结形/双反例定谳）+ qmax2 吸收件 + 跨距单调链 +
     + 旗舰冻结定理 Hsup_cyc_stable + 谱有限三件 + 冻结数值锚。
     §S5 起（ROTC 并入面；S6b 前移至 §3 之前）：真循环旋转底座 rotc/Pinf_c 定义 + 置换与
     长度保底（rotc_perm/rotc_length）+ 周期律与逆元律（rotc_inv/
     rotc_full）+ 跨度下界（H_rotc_span_lb 系）+ 旗舰非退化分离
     （H_rotc_separates/rotc_Pinf_separates）。
     §S6 起（RotSpec 并入面）：接缝序 rs_seam_order + 旗舰锐化上界
     rotc_class_sharp_ub（H_adj (rotc k l) <= 2·spread，锐于 §5 的
     3·spread）+ 锐性取得 rotc_class_sharp_attained（[0;0;2] 界不可
     再降）+ 周期冻结锚形 rotc_periodic + 旋转类折回 rotc_class_folds
     + 排序最小化排列类泛化 phcyc_min_perm + 偏差检测器 phase_dev 及
     行为定理族（iff 桥/记录面/序面/数值升格/稳定面）+ k=0 面条件
     定理与双见证（有界组合律三件同语句异名件已按 U18-3 表去重，见【四】）。
     §S7 起（Lam 并入面）：H_lam 仿射差分恒等式族 + 零前提反向单调
     H_lam_anti_mono + 显式端点选择器 lam_opt 族（λ-argmin 构造性）
     + align_lambda 行为面 + 端点外插双警戒（[1;5;2]）+ 真旋转底座
     λ-相位插值族 H_lam_cyc/lam_opt_cyc（端点双件/差分恒等式/双方向
     单调/旧件分离双见证/λ-argmin_cyc）。
     §S8 起（FRUIT-1 件追加；含 AUDIT-2 改道件）：F1 拼接分解恒等式
     H_adj_app（判过时·消费 §2 H_adj_app_seam 既有件的定向包装）+
     F2'/F2 旗舰 Pmid 中相熵分解双形 H_adj_Pmid_seam /
     H_adj_Pmid_decomp（Pmid 第三相首个熵定理：中相 = 排序前缀 ×
     原始尾的接缝分解）+ F2b 排序坍缩 list 级 Pmid_sorted_collapse
     （中相零理论根因定理化）+ F3 熵坍缩精确面 H_adj_Pmid_sorted_exact
     与 2·spread 上界 H_adj_Pmid_sorted_ub2 + 无排序诚实界
     H_adj_Pmid_ub_gen（尾段不可吞入如实分项）+ 端点退化三件
     （k=0＝P∞ 相、k=length＝P0 相）+ F7 三相判定死支定理化
     phase_classify_ne_PMid（PhMid 构造子不可达）。
     §S9 起（FRUIT-3 件追加）：H_lam_pmid 三相互补熵理论最后
     一块——P0↔Pmid 真 λ-插值载体（λ 从排序相滑向真中相，
     中相端 = 有序前缀×接缝×原始尾三分量熵）+ 端点双件（λ=1 取
     P0 相、λ=0 取 Pmid 相）+ 旗舰仿射差分恒等式与标准形（消费
     §S7 lam_affine_diff_sub 泛形）+ 主件排序坍缩一致面三件
     （sorted 上全 λ 与 H_lam 逐点重合；λ=1/λ=0 双端精确坍缩到
     H_adj l，消费 §S8 Pmid_sorted_collapse / H_adj_Pmid_sorted_exact）
     + 加分 k=0 旧件重合桥（与 H_lam 逐点相等，迁移零丢旧信息）
     + k=length 常值面（λ 失效）+ 与 H_lam 分离见证（未排序
     [2;0;1]：中相端 1 ≠ 原始尾端 3，3/2 ≠ 5/2）+ 数值锚双件。
     §S10 起（CLN-1 件追加；AUDIT-2 A6 恒等簇处置）：保底处置面
     定理 rotc_supersedes_rot_id（旧 rot=firstn++skipn 恒等面的
     定谳件，firstn_skipn 直证不消费弃用件）+ 恒等簇真化覆盖面
     三件（llm_rot_id_superseded P 面零损失迁移 / rot_cyclic_
     cluster_superseded 置换·长度消费面双覆盖 / rot_H_adj_face_
     covered 熵面恒等+退化端点同值覆盖，分离面由 §4 在册）+
     主件 deprecated_consumers_map 八件逐件映射（D5_Pinf_perm /
     llm_Pmid_zero / P0_absorbs_Pmid / Hsup_mono / Hsup_bounded /
     Pinf_eq_l / H_adj_cross_phase_lb / u12_phase_side_always_zero
     ——旧名消费性质与真化替代件同成立的传递定理，旧面全绕行
     弃用名重推；helper Hsup_oldface_const：旧 Hsup 面恒常值
     = H_adj l）+ 加分消费面重定向示范双件（H_lam_anti_mono_
     real / lam_opt_cross_phase_real：§S7 两消费点同陈述新证法，
     跨相下界改经 Pinf_true_id + H_adj_P0_min 真化锚）。
     §S11 起（FRUIT-6 件追加；深水区第二件·三相互补统一族）：
     三族 λ-插值（H_lam 第二端 P∞ l s≡l / H_lam_cyc 第二端
     rotc k l / H_lam_pmid 第二端 Pmid l s k）的单一仿射族
     定理——统一载体 H_lam_gen（第一端恒 P0、第二端参数化）+
     统一仿射差分 H_lam_gen_diff 与标准形（消费 §S7
     lam_affine_diff_sub 泛形，三族差分件收编为单一实例点）+
     旗舰三特化对账（恒等端消费 §4 Pinf_true_id 真化锚、旋转/
     中相端定义展开恒等，三族逐件 = 统一族三实例）+ 主件统一
     最优性 H_lam_gen_opt（§S7 lam_opt_min 泛形族级版，对齐
     选择器 lam_opt 全族一致最优；双文件选择器同值面
     lam_opt_align_lambda_opt_eq 消费 §A7 align_lambda_opt）+
     加分端点三元对账（rotc 0 恒等端 / Pmid k=0 原始全体端 /
     k=length P0 相常值端）+ 数值锚双件（[2;0;1] λ=1/2：恒等端
     5/2 ≠ 中相端 3/2，第二端参数化实质生效）。
     数学锚：l=[a1<=…<=an]，1<=k<=n−1 时 H_adj (rotc k l) =
     (a_n−a_{k+1}) + (a_n−a_1) + (a_k−a_1) <= 3·spread（锐化面
     <= 2·spread），k=0 与 k=n 取最小值 spread（与 C_gen 排序最小
     1·spread 成对）；clamp 语义下 Hsup_cyc l n 在 n = length l 处冻结。
   【二·依赖】
     DTPT（H_adj/xq_ 工具箱/H_lam 系/P0/Pinf/align_lambda）、
     DTPT_Entropy（SortedQ/xq_ 桥，与 DTPT 同名同构，Import 序取后者）；
     stdlib：QArith/Qabs/List/Arith/Lia/Permutation（Arith 为 S6a 并入
     RotSpec 面 Nat.le_0_l 解析所需增补）。无其它 Require。S6a 注：
     RotSpec 原 Require DTPT_Entropy2/DTPT_Cyc 删（前者体面零消费——
     qn/freq_q 仅头注提名；后者系并入宿主自身）；Lam 原 Require
     DTPT_ROTC 删（rotc 系经 §S5 内联本体直引）。S6b 棒注：DTPT_ROTC
     退役（.retired_S6b 快照留存），rotc 系全指 §S5 内联副本——本棒
     将该副本前移至 §3 之前，§0-§M5-1 前段引用面（rotc/rotc_0/
     rotc_full/rotc_rot_app/rotc_perm）就地解析，头部 Require/Import
     DTPT_ROTC 与 §S6 顶后置重导共三行删，对 DTPT_ROTC/DTPT_Entropy2
     依赖归零，全树 Require 面仅 DTPT/DTPT_Entropy。
   【三·归并记录】
     M5 件：DTPT_HsupStable.v（U18-3 拆分件，U8 留账偿还件）全文并入
     本文件尾（§M5-1 分隔注起，除 Require 块外逐字保留），源文件退役
     （.retired_M5 快照留存）。其 Require DTPT/DTPT_ROTC/DTPT_Cyc 三行
     删除——ROTC 依赖经本文件现有 Require DTPT_ROTC 可达。
     S5 棒：DTPT_ROTC.v 全文并入本文件尾（§S5 分隔注起，
     除 Require 块外逐字保留，其头部职责任务注原文随行）。撞名预检：
     ROTC 顶层 17 名对本文件既有名 grep 零撞；U18-3 对账表适用面为空
     （rotc_add/rotc_periodic_full 实际在 DTPT_RotSpec.v 侧，跨文件
     二选一去重按头【四】留下游统一裁决）。源件因下游 Lam/RotSpec 在册
     保留不退役。
     S6a 棒：DTPT_RotSpec.v 全文并入本文件（§S6 分隔注
     起，剥壳除头部与 Require/Import 块外逐字搬运）；DTPT_Lam.v 全文
     并入（§S7 分隔注起，剥壳逐字搬运，其头部 Open Scope Q_scope 随
     行）。撞名预检：两源 63 顶层名（RotSpec 29 + Lam 34）对本文件
     既有 69 名整词 grep 零精确撞名；三对 U18-3 同语句异名件按任务卡
     「陈述同者删 RotSpec 侧改引 Cyc 侧」收口（rotc_add/rotc_periodic_full/
     rotc_add_unbounded_false 删，逐名裁决见【四】，删除点留注记，
     原件全文见 .retired_S6 快照）。两源实测全工作区零下游
     Require/Import，随棒退役（.retired_S6 快照留存）。
     S6b 棒（完成棒）：本件改名 DTPT_Cyc.v →
     DTPT_Rotation.v（Module DTPT_Cyc → DTPT_Rotation 同名改，头部
     职责行改「旋转论：rotc 底座/精确闭式/锐化/λ 插值/偏差判别/周期律
     簇」）。终态吸收三件：DTPT_ROTC（S5 棒）+ DTPT_RotSpec（S6a）+
     DTPT_Lam（S6a）——RotSpec/Lam 并入体零改动随行；ROTC 内联副本
     前移至 §3 之前供全件本地解析，头部 Require/Import DTPT_ROTC 与
     §S6 顶后置重导三行删（S6a 盘面注记随消化，见 §S6 顶 S6b 注）。
     DTPT_ROTC.v/DTPT_Entropy2.v 退役（各五件产物 .retired_S6b 快照
     留存；下游实测全工作区零 Require/Import）；本件下游实测零消费
     （改后无人 Require DTPT_Rotation）。改名前双快照
     DTPT_Cyc.v.bak_S6b_Cyc / DTPT_Cyc.v.snap_S6b_pre。
     FRUIT-3 件：§S9 追加（H_lam_pmid 三相互补——
     P0↔Pmid 真 λ-插值 13 件：1 Definition + 12 Qed，消费 §S7
     lam_affine_diff_sub 泛形与 §S8 Pmid_sorted_collapse /
     H_adj_Pmid_sorted_exact 既有件零重证），纯尾部追加（End 前插
     段 + 文尾审计块 + 头注职责/归并/认证三行刷新），底座零重证
     零修改。
     CLN-1 件：§S10 追加（恒等簇处置——AUDIT-2
     A6「llm_rot_id 恒等簇 + 8 件弃用注记件仍以现役名被引用」的
     处置收口：15 件全 Qed，保底 4 + 主件 9（含 helper）+ 加分 2），
     纯尾部追加（End 前插段 + 文尾审计块 + 头注三处刷新），
     §S8/§S9 与既有行零改动零触碰；旧面性质全绕行弃用名重推
     （Pinf_eq_l 弃用件不经手，一律改经 §4 Pinf_true_id）；
     依赖链前置实修一次（FRUIT-4 重编 DTPT.vo 后
     DTPT_Entropy.vo 假设不一致，_cln1_dep.cmd 补编 Entropy，
     .v 零触碰）（DTPT_CLN1_处置报告.md）。
     FRUIT-6 件：§S11 追加（三相互补统一族——
     H_lam/H_lam_cyc/H_lam_pmid 三族 λ-插值单一仿射族定理
     14 件：1 Definition + 13 Qed，消费 §S7 lam_affine_diff_sub
     / lam_opt_min 泛形、§4 Pinf_true_id、§S8 H_adj_Pmid_k0 /
     H_adj_Pmid_klen 与 DTPT_Entropy §A7 align_lambda_opt
     既有件零重证），纯尾部追加（End 前插段 + 文尾审计块 +
     头注职责/归并/认证三处刷新），§S7-§S10 与既有行零改动
     零触碰。
   【四·对账注记（周期律/锐化面逐名裁决，U18-3 表 S6a 收口）】
     U18-3 预警三对同语句（或同判反例）异名件，按任务卡裁决删 RotSpec
     侧、改引本文件 Cyc 侧：
       rotc_add（RotSpec）≡ rotc_add_local（陈述 α 等价）；
       rotc_periodic_full（RotSpec）≡ rotc_freeze_local（陈述 α 等价）；
       rotc_add_unbounded_false（RotSpec）≡ rotc_add_naive_false
       （同判反例件，见证均 [0;1;2] 仅 m,n 序异）。
     陈述不同者保留双方：rotc_periodic（RotSpec 守卫锚形）与
     rotc_periodic_naive_false（本文件无守卫 k 形反例补位）互补非
     重复；rotc_class_folds（j <= length l）与 rotc_spectrum_bound
     （k' <= length l - 1）界表述不同并存；rs_le_double（2·s）与
     cyc_le_triple（3·s）配方同型倍数不同并存。
   【五·认证】
     全件 Qed（U8 32 + M5-1 18 + S5 15 + S6 并入 25 + S7 并入 31 =
     121 件 + S8/FRUIT-1 追加 14 件 = 135 件 + S9/FRUIT-3 追加
     12 件 = 147 件 + S11/FRUIT-6 追加 13 件 = 160 件）+ 10
     定义面（9 + 1）；Print
     Assumptions 全 Closed under the global
     context；M5 一窗编译全绿（DTPT_M5_归并报告.md）；S5 棒重编全绿
     （DTPT_棒5_归并报告.md）；S6a 棒重编 8/8 全绿 + coqchk EXIT=0
     （DTPT_棒6a_归并报告.md）；底座零重证零修改。S6b 棒（改名+ROTC/
     Entropy2 退役+ROTC 副本前移）重编 6/6 全绿 + coqchk 6 模块 EXIT=0
     （DTPT_棒6b_归并报告.md）。
     FRUIT-1 件：§S8 追加 14 件（14 Qed + 0 Definition，
     F1 判过时引 seam 件 / F2'+F2 / F2b / F3 / F7 / 加分端点 /
     数值实测锚双件全交，含 AUDIT-2 改道三件），纯尾部追加+头部
     职责行/认证行刷新，底座零重证零修改；单轮编译全绿 +
     coqchk EXIT=0（DTPT_FRUIT1_果实报告.md）。
     FRUIT-3 件：§S9 追加 12 件（12 Qed + 1
     Definition：定义/端点双件/仿射差分+标准形/排序坍缩一致面三件/
     k=0 旧件重合桥/k=length 常值面/分离见证/数值锚双件全交），
     纯尾部追加+头部职责行/归并记录/认证行刷新，底座零重证零修改；
     单轮编译全绿 + coqchk EXIT=0（DTPT_FRUIT3_果实报告.md）。
     CLN-1 件：§S10 追加 15 件（15 Qed + 0
     Definition，保底处置面+覆盖面四件 / 逐件映射八件+helper /
     重定向示范双件全交），纯尾部追加+头部三处刷新；首轮编译
     一次绿，Print Assumptions 全 Closed（新增 15/15）+ coqchk
     EXIT=0（DTPT_CLN1_处置报告.md）。
   【六·纪律】
     零承认（头注不用禁词字面）；全程 Qed；nat 全显式 %nat（上游
     Q_scope 传导）；lia 只用于 nat/Z，Q 侧全走显式引理装配。
   ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Permutation.
Require DTPT.
Require DTPT_Entropy.
Import ListNotations.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.

Module DTPT_Rotation.

(* ========== §0 通用小工具 ========== *)

(* Qeq 运入 Qle 的桥：Qeq 与 Qle 展开后同为 Qnum/Qden 编码式，
   等式运进不等式由 Z 层 lia 一步收口（不经 setoid rewrite） *)
Lemma cyc_qeq_le : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros x y H. unfold Qeq in H. unfold Qle. lia.
Qed.

(* nat 全覆盖二分：le 或 gt（自证，不依赖 Compare_dec 裸名；
   归纳须先于 m 引入，IH 对 m 全称化后 S 支才可传） *)
Lemma cyc_nat_le_gt_cases : forall n m : nat, (n <= m)%nat \/ (m < n)%nat.
Proof.
  induction n as [| n IH]; intros m; destruct m as [| m].
  - left. lia.
  - left. lia.
  - right. lia.
  - destruct (IH m) as [H | H]; [ left | right ]; lia.
Qed.

(* 三倍自界：0 <= s 时 s <= 3*s（ub3 边界支的公共收口） *)
Lemma cyc_le_triple : forall s : Q, (0 <= s)%Q -> (s <= 3 * s)%Q.
Proof.
  intros s Hs.
  assert (H3 : (3 * s == s + s + s)%Q) by ring.
  apply (Qle_trans s (s + s + s) (3 * s)).
  - apply (proj2 (Qle_0_sub' s (s + s + s))).
    assert (Hr : (s + s + s - s == s + s)%Q) by ring.
    rewrite Hr. exact (qadd_nonneg s s Hs Hs).
  - apply cyc_qeq_le. apply Qeq_sym. exact H3.
Qed.

(* ========== §1 保序底座：firstn/skipn 保成员与保升序 ========== *)

Lemma firstn_incl : forall (l : list Q) (k : nat) (z : Q),
  In z (firstn k l) -> In z l.
Proof.
  induction l as [| a rest IH]; intros k z Hin.
  - destruct k; simpl in Hin; destruct Hin.
  - destruct k as [| k']; simpl in Hin.
    + destruct Hin.
    + destruct Hin as [Hin | Hin].
      * left. exact Hin.
      * right. exact (IH k' z Hin).
Qed.

Lemma skipn_incl : forall (l : list Q) (k : nat) (z : Q),
  In z (skipn k l) -> In z l.
Proof.
  induction l as [| a rest IH]; intros k z Hin.
  - destruct k; simpl in Hin; destruct Hin.
  - destruct k as [| k']; simpl in Hin.
    + exact Hin.
    + right. exact (IH k' z Hin).
Qed.

Lemma firstn_SortedQ : forall (l : list Q) (k : nat),
  SortedQ l -> SortedQ (firstn k l).
Proof.
  induction l as [| a rest IH]; intros k HS.
  - destruct k as [| k']; simpl; apply sortQ_nil.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    destruct k as [| k']; simpl.
    + apply sortQ_nil.
    + apply sortQ_cons.
      * apply IH. exact HSr.
      * apply Forall_forall. intros z Hz. apply HFa.
        exact (firstn_incl rest k' z Hz).
Qed.

Lemma skipn_SortedQ : forall (l : list Q) (k : nat),
  SortedQ l -> SortedQ (skipn k l).
Proof.
  induction l as [| a rest IH]; intros k HS.
  - destruct k as [| k']; simpl; apply sortQ_nil.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    destruct k as [| k']; simpl.
    + apply sortQ_cons;
        [ exact HSr | apply Forall_forall; exact HFa ].
    + apply IH. exact HSr.
Qed.

(* 结构主件：真循环旋转 = 第一段升序 ++ 第二段升序 *)
Theorem rotc_two_runs : forall (k : nat) (l : list Q),
  SortedQ l -> SortedQ (skipn k l) /\ SortedQ (firstn k l).
Proof.
  intros k l HS. split.
  - apply skipn_SortedQ. exact HS.
  - apply firstn_SortedQ. exact HS.
Qed.

(* ========== §2 接缝分解：u++v 熵 = 两段熵 + 接缝绝对值 ========== *)

(* 两段各自非空即可，不要求排序：熵只在接缝处多出一个绝对值 *)
Lemma H_adj_app_seam : forall (u v : list Q),
  u <> [] -> v <> [] ->
  H_adj (u ++ v) == H_adj u + H_adj v + Qabs (hd 0 v - lastq u).
Proof.
  induction u as [| a rest IH]; intros v Hne Hne2.
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [| b bs].
    + destruct v as [| c v'].
      * exfalso. apply Hne2. reflexivity.
      * change (H_adj ([a] ++ c :: v')) with (Qabs (c - a) + H_adj (c :: v'))%Q.
        change (H_adj [a]) with 0%Q.
        change (lastq [a]) with a.
        change (hd 0 (c :: v')) with c.
        ring.
    + change (H_adj ((a :: b :: bs) ++ v))
        with (Qabs (b - a) + H_adj (b :: bs ++ v))%Q.
      change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      change (lastq (a :: b :: bs)) with (lastq (b :: bs)).
      assert (Hne' : b :: bs <> []) by (intro Hcz; discriminate Hcz).
      replace (H_adj (b :: bs ++ v)) with (H_adj ((b :: bs) ++ v))
        by reflexivity.
      rewrite (IH v Hne' Hne2).
      ring.
Qed.

(* ============================================================
   §S5 归并分隔注 —— 以下为原 DTPT_ROTC.v 全文（S5 整合棒并入；S6b 前移至本位）
   除 Require 块外逐字保留（含其头部职责任务注原文，见下），声明序与
   证法零改动。头部依赖行所记 DTPT_LLM 已随棒 1 归并入 DTPT.v §11
   （llm_ 系经本文件现有 Import DTPT.DTPT 可达；棒 1 已删 ROTC 侧
   Require 两行——以盘面现态为准）。撞名预检与下游登记见本文件头
   【三·归并记录】。S6b 棒：本块整体前移至 §3 之前（原居原 §M5-§5
   之后、§S6 之前）——DTPT_ROTC 退役后，§0-§M5-1 前段引用面
   （rotc/rotc_0/rotc_full/rotc_rot_app/rotc_perm）自本块定义点起
   改指内联副本就地解析，头部 Require/Import DTPT_ROTC 删，遮蔽
   分歧消解为单一本地本体（逐字同形，语义等价）。
   ============================================================ *)
(* ============================================================
   DTPT_ROTC.v — 真循环旋转底座（X1 扫描件 A 级发现：伪定理簇真化）
   职责：Pinf 伪装簇真化层操作语义——纯增量新建真循环旋转底座
         rotc = skipn ++ firstn（取尾段接到前段，n 起转一圈），
         证明新相算子非退化：存在列表与转数使
         H_adj (rotc n l) <> H_adj l（旗舰分离件），且真旋转与
         恒等算子 Pinf 结构可分（rotc n l <> l 有闭项见证）。
   依赖：QArith（QArith/Qabs）、List、Lia、Permutation、DTPT
         （H_adj、xq_pair_dist_le 跨度下界引擎）、DTPT_LLM
         （llm_rot_cyclic_perm / llm_rot_cyclic_length 现成置换件
         与长度件——底座纪律：不重证，直接引用）。
   归并记录：无（原生成模块）。
   认证：零承认零公理；全树 coqchk EXIT=0。
   纪律：纯构造性；四关收割；温控协议；全程 Qed；
         nat 全显式 %nat（上游 Q_scope 劫持传导）。
   附注：真化动机——DTPT.v 的 rot = firstn ++ skipn 是恒等重构，
         致 Pinf ≡ id、Hsup l n ≡ H_adj l，五件定理成恒等推论伪装；
         X1 定位：DTPT_热点升级清单_X1.md 热点 4【Hsup 族伪定理簇
         真化：真循环旋转底座 rotc】保底/主件/旗舰/加分四层交付。
   ============================================================ *)

(* ========== §1 真循环旋转底座 ========== *)

(* 真循环旋转：取 l 的后段接到前段（DTPT.rot 的 firstn++skipn
   恒等重构之真化替换；X1 热点 4 定义面） *)
Definition rotc (n : nat) (l : list Q) : list Q :=
  skipn n l ++ firstn n l.

(* 真无限相：转 s+1 格（对照 DTPT.Pinf 的恒等坍缩面） *)
Definition Pinf_c (l : list Q) (s : nat) : list Q := rotc (S s) l.

(* ========== §2 保底件：置换与长度 ========== *)

(* 真旋转是置换：两步走——llm_rot_cyclic_perm（skipn++firstn 与 l
   置换等价，Permutation_app_comm + firstn_skipn 合成件）取对称 *)
Theorem rotc_perm : forall (n : nat) (l : list Q),
  Permutation l (rotc n l).
Proof.
  intros n l. unfold rotc.
  apply Permutation_sym.
  etransitivity.
  - apply Permutation_app_comm.
  - rewrite firstn_skipn. apply Permutation_refl.
Qed.

(* 长度不变：直接引用底座 llm_rot_cyclic_length（禁重证） *)
Theorem rotc_length : forall (n : nat) (l : list Q),
  length (rotc n l) = length l.
Proof.
  intros n l. unfold rotc.
  rewrite length_app, length_firstn, length_skipn.
  lia.
Qed.

Theorem Pinf_c_perm : forall (l : list Q) (s : nat),
  Permutation l (Pinf_c l s).
Proof.
  intros l s. unfold Pinf_c, rotc.
  apply Permutation_sym.
  etransitivity.
  - apply Permutation_app_comm.
  - rewrite firstn_skipn. apply Permutation_refl.
Qed.

(* ========== §3 主件：周期律与逆元律 ========== *)

(* 零转恒等（app 右零） *)
Lemma rotc_0 : forall l : list Q, rotc 0 l = l.
Proof.
  intros l. unfold rotc. simpl.
  induction l as [| a rest IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* 表长取全：skipn 吃光前段剩后段（对前段归纳） *)
Lemma skipn_all_app : forall (a b : list Q),
  skipn (length a) (a ++ b) = b.
Proof.
  intros a b. induction a as [| x xs IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.

(* 表长取全：firstn 吃光前段（对前段归纳） *)
Lemma firstn_all_app : forall (a b : list Q),
  firstn (length a) (a ++ b) = a.
Proof.
  intros a b. induction a as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* 核心引理：转「前段长」格 = 前后段换位（真旋转的交换子） *)
Lemma rotc_rot_app : forall (a b : list Q),
  rotc (length a) (a ++ b) = b ++ a.
Proof.
  intros a b. unfold rotc.
  rewrite skipn_all_app. rewrite firstn_all_app. reflexivity.
Qed.

(* 逆元律：转 n 格后回转（表长 - n）格复原。
   证法：l 分解为 firstn/skipn 两段（firstn_skipn），pose 折叠
   两段变量护住 n 的替换面，再 rotc_rot_app 两次换位收口。 *)
Theorem rotc_inv : forall (n : nat) (l : list Q),
  (n <= length l)%nat -> rotc ((length l - n)%nat) (rotc n l) = l.
Proof.
  intros n l Hn.
  pose (a := firstn n l).
  pose (b := skipn n l).
  assert (Hla : (length a = n)%nat)
    by exact (firstn_length_le l Hn).
  assert (Hsplit : l = a ++ b)
    by (unfold a, b; symmetry; apply firstn_skipn).
  assert (Hab : (length (a ++ b) - length a = length b)%nat)
    by (rewrite length_app; lia).
  rewrite Hsplit.
  rewrite <- Hla.
  rewrite Hab.
  rewrite !rotc_rot_app.
  reflexivity.
Qed.

(* 周期律：转整一圈（表长格）复原——逆元律在 n := 表长 的特例 *)
Theorem rotc_full : forall l : list Q, rotc (length l) l = l.
Proof.
  intros l.
  assert (H := rotc_inv (length l) l (le_n (length l))).
  assert (Hd : (length l - length l)%nat = 0%nat) by lia.
  rewrite Hd in H.
  rewrite rotc_0 in H.
  exact H.
Qed.

(* ========== §4 旗舰·非退化分离 ========== *)

(* 恒等算子面：DTPT.Pinf 的 rot = firstn++skipn 恒等重构
   （X1 判词的定义面事实，一行 firstn_skipn） *)
Lemma Pinf_true_id : forall (l : list Q) (s : nat), Pinf l s = l.
Proof.
  intros l. unfold Pinf, rot.
  induction l as [| a rest IH]; intros s.
  - reflexivity.
  - destruct s as [| s'].
    + reflexivity.
    + change (firstn (S (S s')) (a :: rest) ++ skipn (S (S s')) (a :: rest) = a :: rest)
        with (a :: (firstn (S s') rest ++ skipn (S s') rest) = a :: rest).
      rewrite IH. reflexivity.
Qed.

(* 成员经真旋转保持（rotc_perm 搬成员 + Permutation_in） *)
Lemma rotc_in : forall (n : nat) (l : list Q) (x : Q),
  In x l -> In x (rotc n l).
Proof.
  intros n l x Hin.
  assert (Hp : Permutation l (skipn n l ++ firstn n l)).
  { apply Permutation_sym. etransitivity.
    - apply Permutation_app_comm.
    - rewrite firstn_skipn. apply Permutation_refl. }
  apply (Permutation_in x Hp). exact Hin.
Qed.

(* 加分项：真旋转相算子的跨度下界——表内任意两元的距离
   经置换成员搬移 + xq_pair_dist_le 被 H_adj (rotc n l) 界住 *)
Theorem H_rotc_span_lb : forall (n : nat) (l : list Q) (x y : Q),
  In x l -> In y l -> (Qabs (x - y) <= H_adj (rotc n l))%Q.
Proof.
  intros n l x y Hx Hy.
  apply (xq_pair_dist_le (rotc n l) x y).
  - apply rotc_in. exact Hx.
  - apply rotc_in. exact Hy.
Qed.

(* 加分项·数值见证：见证列 [0;1;2] 上真旋转相算子恒有跨度下界 2
   （首尾差 |0-2| = 2，Qle 闭项判定 reflexivity 直收） *)
Theorem H_rotc_span_lb_wit : forall n : nat,
  (2 <= H_adj (rotc n [0;1;2]))%Q.
Proof.
  intros n.
  apply (Qle_trans 2 (Qabs (0 - 2)) (H_adj (rotc n [0;1;2]))).
  - replace (Qabs (0 - 2)) with 2%Q by reflexivity.
    apply Qle_refl.
  - apply H_rotc_span_lb.
    + simpl. left. reflexivity.
    + simpl. right. right. left. reflexivity.
Qed.

(* 旗舰：真旋转相算子非退化——存在 l 与转数 n 使 H_adj 严格改变。
   见证 [0;1;2] 转 1 格 = [1;2;0]：H_adj 从 2（|1-0|+|2-1|）
   升到 3（|2-1|+|0-2|）。闭 Q 值反例收口：vm_compute 一发 +
   discriminate（B2 卡在册配方）。此件直接反证 Pinf 伪装簇的
   「定理」在真底座下不平凡。 *)
Theorem H_rotc_separates : exists (l : list Q) (n : nat),
  H_adj (rotc n l) <> H_adj l.
Proof.
  exists [0;1;2], 1%nat.
  intro Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* 加分项：与 Pinf 的分离——真旋转与恒等算子结构可分
   （Pinf l s = l 恒等，故见证列上 rotc 1 <> l 结构不等） *)
Theorem rotc_Pinf_separates : exists (l : list Q) (n s : nat),
  rotc n l <> Pinf l s.
Proof.
  exists [0;1;2], 1%nat, 0%nat.
  rewrite Pinf_true_id.
  intro Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* ========== §3 边界判别与端元迁移 ========== *)

(* 非空判别：转点严格小于表长时 skipn 段非空 *)
Lemma skipn_ne_of_lt : forall (k : nat) (l : list Q),
  (k < length l)%nat -> skipn k l <> [].
Proof.
  intros k l Hlt Hc.
  assert (Hsplit : l = firstn k l ++ skipn k l)
    by (symmetry; apply firstn_skipn).
  rewrite Hc in Hsplit. rewrite app_nil_r in Hsplit.
  assert (Hle : (k <= length l)%nat) by lia.
  assert (Hlen : (length (firstn k l) = k)%nat)
    by (apply (firstn_length_le l Hle)).
  assert (Hcon : (length l = k)%nat) by (rewrite Hsplit; exact Hlen).
  lia.
Qed.

(* 非空判别：转数非零且不超表长时 firstn 段非空 *)
Lemma firstn_ne_of_lt : forall (k : nat) (l : list Q),
  (0 < k)%nat -> (k <= length l)%nat -> firstn k l <> [].
Proof.
  intros k l H1 H2 Hc.
  destruct l as [| a rest].
  - simpl in H2. lia.
  - destruct k as [| k'].
    + lia.
    + simpl in Hc. discriminate.
Qed.

(* 表长吃满：skipn 段吃空 *)
Lemma rotc_skipn_all : forall (l : list Q) (k : nat),
  (length l <= k)%nat -> skipn k l = [].
Proof.
  induction l as [| a rest IH]; intros k Hk.
  - destruct k; reflexivity.
  - destruct k as [| k'].
    + simpl in Hk. exfalso. lia.
    + simpl. apply IH. simpl in Hk. lia.
Qed.

(* 表长吃满：firstn 段还原全表 *)
Lemma rotc_firstn_all : forall (l : list Q) (k : nat),
  (length l <= k)%nat -> firstn k l = l.
Proof.
  induction l as [| a rest IH]; intros k Hk.
  - destruct k; reflexivity.
  - destruct k as [| k'].
    + simpl in Hk. exfalso. lia.
    + simpl. assert (Hle : (length rest <= k')%nat) by (simpl in Hk; lia).
      rewrite (IH k' Hle). reflexivity.
Qed.

(* 退化判别件：转数不小于表长时真旋转恒等（把弱点钉成定理） *)
Theorem rotc_ge_len_id : forall (k : nat) (l : list Q),
  (length l <= k)%nat -> rotc k l = l.
Proof.
  intros k l Hk. unfold rotc.
  rewrite (rotc_skipn_all l k Hk).
  rewrite (rotc_firstn_all l k Hk).
  reflexivity.
Qed.

(* 尾元迁移：转点严格小于表长时 skipn 段尾元 = 全表尾元 *)
Lemma lastq_skipn_kept : forall (l : list Q) (k : nat),
  (k < length l)%nat -> lastq (skipn k l) = lastq l.
Proof.
  induction l as [| a rest IH]; intros k Hlt.
  - simpl in Hlt. exfalso. lia.
  - destruct k as [| k'].
    + reflexivity.
    + simpl in Hlt. destruct rest as [| b bs].
      * simpl in Hlt. exfalso. lia.
      * simpl. apply IH. lia.
Qed.

(* 首元迁移：转数非零时 firstn 段首元 = 全表首元 *)
Lemma hd_firstn_kept : forall (k : nat) (l : list Q),
  (0 < k)%nat -> hd 0 (firstn k l) = hd 0 l.
Proof.
  intros k l Hk. destruct l as [| a rest].
  - destruct k; simpl; reflexivity.
  - destruct k as [| k'].
    + exfalso. lia.
    + simpl. reflexivity.
Qed.

(* 排序表首元最小：hd 0 l 不超过任意成员 *)
Lemma sorted_hd_min : forall (l : list Q), SortedQ l ->
  forall z : Q, In z l -> (hd 0 l <= z)%Q.
Proof.
  induction l as [| a rest IH]; intros HS z Hin.
  - destruct Hin.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    simpl. destruct Hin as [Hin | Hin].
    + subst. apply Qle_refl.
    + apply HFa. exact Hin.
Qed.

(* 排序表尾元最大：任意成员不超过 lastq *)
Lemma sorted_lastq_max : forall (l : list Q), SortedQ l ->
  forall z : Q, In z l -> (z <= lastq l)%Q.
Proof.
  induction l as [| a rest IH]; intros HS z Hin.
  - destruct Hin.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    destruct rest as [| b bs].
    + destruct Hin as [Hin | Hin].
      * subst. simpl. apply Qle_refl.
      * destruct Hin.
    + destruct Hin as [Hin | Hin].
      * subst. change (lastq (z :: b :: bs)) with (lastq (b :: bs)).
        apply HFa. apply xq_lastq_In. simpl. discriminate.
      * change (lastq (a :: b :: bs)) with (lastq (b :: bs)).
        exact (IH HSr z Hin).
Qed.

(* 区间引理：排序表内两元之差不超过 spread（= lastq − hd） *)
Lemma sorted_sub_le_spread : forall (l : list Q) (z w : Q),
  SortedQ l -> In z l -> In w l -> (z - w <= lastq l - hd 0 l)%Q.
Proof.
  intros l z w HS Hz Hw.
  assert (Hzm : (z <= lastq l)%Q) by (apply (sorted_lastq_max l HS z Hz)).
  assert (Hwn : (hd 0 l <= w)%Q) by (apply (sorted_hd_min l HS w Hw)).
  apply (proj2 (Qle_0_sub' (z - w) (lastq l - hd 0 l))).
  assert (Hr : (lastq l - hd 0 l - (z - w) == (lastq l - z) + (w - hd 0 l))%Q)
    by ring.
  rewrite Hr.
  apply qadd_nonneg.
  - apply (proj1 (Qle_0_sub' z (lastq l))). exact Hzm.
  - apply (proj1 (Qle_0_sub' (hd 0 l) w)). exact Hwn.
Qed.

(* ========== §4 旗舰：排序表循环旋转熵精确闭式 ========== *)

(* 中段精确式：1 <= k < 表长时，rotc k l = [a_{k+1}..a_n; a_1..a_k]，
   相邻差总和 = (尾元−转点) + (尾元−首元) + (转点回卷−首元)。
   证法 = 接缝分解 + 双望远镜（对两段各套 xq_telescope）
   + 接缝项 |hd l − lastq l| 按序褪绝对值。 *)
Theorem H_adj_rotc_exact_mid : forall (k : nat) (l : list Q),
  SortedQ l -> (1 <= k)%nat -> (k < length l)%nat ->
  H_adj (rotc k l) == (lastq l - hd 0 (skipn k l))
                    + (lastq l - hd 0 l)
                    + (lastq (firstn k l) - hd 0 l).
Proof.
  intros k l HS H1 H2.
  assert (HSs : SortedQ (skipn k l)) by (apply skipn_SortedQ; exact HS).
  assert (HSf : SortedQ (firstn k l)) by (apply firstn_SortedQ; exact HS).
  assert (Hnes : skipn k l <> []) by (apply (skipn_ne_of_lt k l H2)).
  assert (Hnef : firstn k l <> []).
  { intro Hc. destruct l as [| a rest].
    - simpl in H2. exfalso. lia.
    - destruct k as [| k'].
      + exfalso. lia.
      + simpl in Hc. discriminate. }
  assert (HE : H_adj (rotc k l) == H_adj (skipn k l ++ firstn k l))
    by reflexivity.
  rewrite HE.
  rewrite (H_adj_app_seam (skipn k l) (firstn k l) Hnes Hnef).
  rewrite (xq_telescope (skipn k l) HSs).
  rewrite (xq_telescope (firstn k l) HSf).
  rewrite (lastq_skipn_kept l k H2).
  rewrite (hd_firstn_kept k l H1).
  assert (Hab : Qabs (hd 0 l - lastq l) == lastq l - hd 0 l).
  { rewrite (xq_abs_sub_comm (hd 0 l) (lastq l)).
    apply xq_abs_id.
    apply (proj1 (Qle_0_sub' (hd 0 l) (lastq l))).
    apply xq_hd_le_lastq. exact HS. }
  rewrite Hab. ring.
Qed.

(* 边界精确式一：零转恒等 *)
Theorem H_adj_rotc_exact_0 : forall l : list Q, SortedQ l ->
  H_adj (rotc 0 l) == lastq l - hd 0 l.
Proof.
  intros l HS. rewrite rotc_0. apply xq_telescope. exact HS.
Qed.

(* 边界精确式二：转数不小于表长恒等 *)
Theorem H_adj_rotc_exact_ge : forall (k : nat) (l : list Q), SortedQ l ->
  (length l <= k)%nat -> H_adj (rotc k l) == lastq l - hd 0 l.
Proof.
  intros k l HS Hk.
  rewrite (rotc_ge_len_id k l Hk). apply xq_telescope. exact HS.
Qed.

(* 边界精确式三：短表（表长不超过 1）任意转数恒等 *)
Theorem H_adj_rotc_exact_short : forall (k : nat) (l : list Q), SortedQ l ->
  (length l <= 1)%nat -> H_adj (rotc k l) == lastq l - hd 0 l.
Proof.
  intros k l HS Hn.
  destruct (cyc_nat_le_gt_cases (length l) k) as [Hle | Hgt].
  - apply (H_adj_rotc_exact_ge k l HS Hle).
  - assert (H0 : (k = 0)%nat) by lia.
    rewrite H0. rewrite rotc_0. apply xq_telescope. exact HS.
Qed.

(* 旗舰二分精确定理：中段取三项闭式，边界取 spread 式，二者必居其一 *)
Theorem H_adj_rotc_sorted_exact : forall (k : nat) (l : list Q), SortedQ l ->
  H_adj (rotc k l) == (lastq l - hd 0 (skipn k l))
                    + (lastq l - hd 0 l)
                    + (lastq (firstn k l) - hd 0 l)
  \/ H_adj (rotc k l) == lastq l - hd 0 l.
Proof.
  intros k l HS.
  destruct (cyc_nat_le_gt_cases (length l) k) as [Hge | Hlt].
  - right. apply (H_adj_rotc_exact_ge k l HS Hge).
  - destruct k as [| k'].
    + right. rewrite rotc_0. apply xq_telescope. exact HS.
    + left.
      assert (H1 : (1 <= S k')%nat) by lia.
      apply (H_adj_rotc_exact_mid (S k') l HS H1 Hlt).
Qed.

(* ========== §5 主件：3·spread 上界（旋转代价 <= 3 倍最小代价） ========== *)

Theorem H_adj_rotc_ub3 : forall (k : nat) (l : list Q),
  SortedQ l -> l <> [] -> (H_adj (rotc k l) <= 3 * (lastq l - hd 0 l))%Q.
Proof.
  intros k l HS Hne.
  assert (Hsp : (0 <= lastq l - hd 0 l)%Q)
    by (apply (proj1 (Qle_0_sub' (hd 0 l) (lastq l)));
        apply xq_hd_le_lastq; exact HS).
  destruct (cyc_nat_le_gt_cases (length l) k) as [Hge | Hlt].
  - (* k >= 表长：恒等支 *)
    rewrite (rotc_ge_len_id k l Hge).
    apply (Qle_trans (H_adj l) (lastq l - hd 0 l) (3 * (lastq l - hd 0 l))).
    + apply cyc_qeq_le. apply xq_telescope. exact HS.
    + apply cyc_le_triple. exact Hsp.
  - destruct k as [| k'].
    + (* 零转支 *)
      rewrite rotc_0.
      apply (Qle_trans (H_adj l) (lastq l - hd 0 l) (3 * (lastq l - hd 0 l))).
      * apply cyc_qeq_le. apply xq_telescope. exact HS.
      * apply cyc_le_triple. exact Hsp.
    + (* 中段支：三项闭式逐项 spread 化后求和 *)
      assert (H1 : (1 <= S k')%nat) by lia.
      assert (Hnef : firstn (S k') l <> [])
        by (apply (firstn_ne_of_lt (S k') l H1); lia).
      assert (Hnes : skipn (S k') l <> [])
        by (apply (skipn_ne_of_lt (S k') l Hlt)).
      assert (HEm : H_adj (rotc (S k') l)
                    == (lastq l - hd 0 (skipn (S k') l))
                     + (lastq l - hd 0 l)
                     + (lastq (firstn (S k') l) - hd 0 l))
        by (apply (H_adj_rotc_exact_mid (S k') l HS H1 Hlt)).
      apply (Qle_trans _ ((lastq l - hd 0 (skipn (S k') l))
                        + (lastq l - hd 0 l)
                        + (lastq (firstn (S k') l) - hd 0 l))
                        (3 * (lastq l - hd 0 l))).
      * apply cyc_qeq_le. exact HEm.
      * assert (HT1 : ((lastq l - hd 0 (skipn (S k') l))
                       <= (lastq l - hd 0 l))%Q).
        { apply (sorted_sub_le_spread l (lastq l)
                   (hd 0 (skipn (S k') l)) HS).
          - apply xq_lastq_In. exact Hne.
          - exact (skipn_incl l (S k') (hd 0 (skipn (S k') l))
                     (xq_hd_In_gen (skipn (S k') l) Hnes)). }
        assert (HT3 : ((lastq (firstn (S k') l) - hd 0 l)
                       <= (lastq l - hd 0 l))%Q).
        { apply (sorted_sub_le_spread l (lastq (firstn (S k') l))
                   (hd 0 l) HS).
          - exact (firstn_incl l (S k') (lastq (firstn (S k') l))
                     (xq_lastq_In (firstn (S k') l) Hnef)).
          - apply xq_hd_In_gen. exact Hne. }
        assert (H3 : (3 * (lastq l - hd 0 l)
                      == (lastq l - hd 0 l) + (lastq l - hd 0 l)
                       + (lastq l - hd 0 l))%Q) by ring.
        apply (Qle_trans _ ((lastq l - hd 0 l) + (lastq l - hd 0 l)
                          + (lastq l - hd 0 l))
                          (3 * (lastq l - hd 0 l))).
        -- apply qadd_le.
           ++ apply qadd_le; [ exact HT1 | apply Qle_refl ].
           ++ exact HT3.
        -- apply cyc_qeq_le. apply Qeq_sym. exact H3.
Qed.

(* ========== §6 加分项：真动态上确界 Hsup_cyc ========== *)

(*
   上界两向只需布尔分支 + Qle_bool_iff/Qle_bool_false_le，零总序前提 *)
Definition qmax2 (x y : Q) : Q := if Qle_bool x y then y else x.

Lemma qmax2_ub_l : forall x y : Q, (x <= qmax2 x y)%Q.
Proof.
  intros x y. unfold qmax2. destruct (Qle_bool x y) eqn:E.
  - apply (proj1 (Qle_bool_iff x y)). exact E.
  - apply Qle_refl.
Qed.

Lemma qmax2_ub_r : forall x y : Q, (y <= qmax2 x y)%Q.
Proof.
  intros x y. unfold qmax2. destruct (Qle_bool x y) eqn:E.
  - apply Qle_refl.
  - apply Qle_bool_false_le. exact E.
Qed.

(* 真动态上确界：前 k+1 个转数（0..k）上 H_adj (rotc i l) 的逐点累积最大 *)
Fixpoint Hsup_cyc (l : list Q) (n : nat) : Q :=
  match n with
  | O => H_adj (rotc 0 l)
  | S n' => qmax2 (Hsup_cyc l n') (H_adj (rotc (S n') l))
  end.

(* 单调：加测一转不减（qmax2_ub_l 一步收口） *)
Theorem Hsup_cyc_mono : forall (l : list Q) (n : nat),
  (Hsup_cyc l n <= Hsup_cyc l (S n))%Q.
Proof.
  intros l n. induction n as [| n IH].
  - cbn [Hsup_cyc]. apply qmax2_ub_l.
  - cbn [Hsup_cyc]. apply qmax2_ub_l.
Qed.

(* 界：真动态上确界也不越过 3·spread *)
Theorem Hsup_cyc_ub : forall (l : list Q) (n : nat), SortedQ l -> l <> [] ->
  (Hsup_cyc l n <= 3 * (lastq l - hd 0 l))%Q.
Proof.
  intros l n HS Hne. induction n as [| n IH].
  - cbn [Hsup_cyc]. apply (H_adj_rotc_ub3 0 l HS Hne).
  - cbn [Hsup_cyc]. unfold qmax2.
    destruct (Qle_bool (Hsup_cyc l n) (H_adj (rotc (S n) l))) eqn:E.
    + apply (H_adj_rotc_ub3 (S n) l HS Hne).
    + exact IH.
Qed.

(* 达到性：上确界总在某个具体转数处取到（布尔分支直接给见证） *)
Theorem Hsup_cyc_attained : forall (l : list Q) (n : nat),
  exists i : nat, (i <= n)%nat /\ Hsup_cyc l n == H_adj (rotc i l).
Proof.
  intros l n. induction n as [| n IH].
  - exists 0%nat. split.
    + lia.
    + cbn [Hsup_cyc]. apply Qeq_refl.
  - destruct IH as [i [Hin Hval]].
    cbn [Hsup_cyc]. unfold qmax2.
    destruct (Qle_bool (Hsup_cyc l n) (H_adj (rotc (S n) l))) eqn:E.
    + exists (S n). split.
      * lia.
      * apply Qeq_refl.
    + exists i. split.
      * lia.
      * exact Hval.
Qed.

(* ========== §7 数值锚 ========== *)

(* 见证列 [0;1;2]：k=1 时 H_adj = |2−1|+|0−2| = 3（闭 Q 值一发判定） *)
Theorem rotc_H_wit_mid : H_adj (rotc 1 [0;1;2]) == 3%Q.
Proof.
  change (H_adj (skipn 1 [0;1;2] ++ firstn 1 [0;1;2]) == 3%Q).
  change (H_adj [1; 2; 0] == 3%Q).
  change (Qabs (2 - 1) + (Qabs (0 - 2) + 0) == 3%Q)%Q.
  reflexivity.
Qed.

(* 见证列 [0;1;2]：k=0 时 H_adj = spread = 2（最小值锚） *)
Theorem rotc_H_wit_min : H_adj (rotc 0 [0;1;2]) == 2%Q.
Proof.
  change (H_adj (skipn 0 [0;1;2] ++ firstn 0 [0;1;2]) == 2%Q).
  change (H_adj ([0; 1; 2] ++ []) == 2%Q).
  change (Qabs (1 - 0) + (Qabs (2 - 1) + 0) == 2%Q)%Q.
  reflexivity.
Qed.

(* ========== §8 公理面审计（G4） ========== *)

Print Assumptions rotc_two_runs.
Print Assumptions H_adj_app_seam.
Print Assumptions rotc_ge_len_id.
Print Assumptions H_adj_rotc_exact_mid.
Print Assumptions H_adj_rotc_exact_0.
Print Assumptions H_adj_rotc_exact_ge.
Print Assumptions H_adj_rotc_exact_short.
Print Assumptions H_adj_rotc_sorted_exact.
Print Assumptions H_adj_rotc_ub3.
Print Assumptions Hsup_cyc_mono.
Print Assumptions Hsup_cyc_ub.
Print Assumptions Hsup_cyc_attained.
Print Assumptions rotc_H_wit_mid.
Print Assumptions rotc_H_wit_min.

(* ============================================================
   §M5-1 归并分隔注 —— 以下为原 DTPT_HsupStable.v 全文（U18-3 件）
   M5 件追加至本文件尾：除头部与 Require 块（DTPT/DTPT_ROTC/DTPT_Cyc，
   经本文件头部现有 Require 均可达）外逐字保留，声明序与证法零改动。
   对账注记见本文件头【四】。
   ============================================================ *)
(* ========== §1 切段四件套（skipn/firstn 对 app 的分段自建，
   不赌 stdlib skipn_app/firstn_app 的 9.0 形状） ========== *)

(* m 不超过前段长：skipn m (b++c) 吃进 b 的一段，剩整段 c *)
Lemma hs_skipn_app_le : forall (b : list Q) (m : nat) (c : list Q),
  (m <= length b)%nat -> skipn m (b ++ c) = skipn m b ++ c.
Proof.
  induction b as [| x bs IH]; intros m c Hm.
  - destruct m as [| m'].
    + reflexivity.
    + cbn in Hm. exfalso. lia.
  - destruct m as [| m'].
    + reflexivity.
    + cbn. assert (Hm' : (m' <= length bs)%nat) by (cbn in Hm; lia).
      rewrite (IH m' c Hm'). reflexivity.
Qed.

(* m 不超过前段长：firstn m (b++c) 只吃前段 *)
Lemma hs_firstn_app_le : forall (b : list Q) (m : nat) (c : list Q),
  (m <= length b)%nat -> firstn m (b ++ c) = firstn m b.
Proof.
  induction b as [| x bs IH]; intros m c Hm.
  - destruct m as [| m'].
    + reflexivity.
    + cbn in Hm. exfalso. lia.
  - destruct m as [| m'].
    + reflexivity.
    + cbn. assert (Hm' : (m' <= length bs)%nat) by (cbn in Hm; lia).
      rewrite (IH m' c Hm'). reflexivity.
Qed.

(* 前段长不超过 k：skipn k (a++c) 越过 a，剩 skipn (k - |a|) c *)
Lemma hs_skipn_app_r : forall (a : list Q) (k : nat) (c : list Q),
  (length a <= k)%nat -> skipn k (a ++ c) = skipn (k - length a) c.
Proof.
  induction a as [| x as' IH]; intros k c Hk.
  - destruct k as [| k']; reflexivity.
  - destruct k as [| k'].
    + cbn in Hk. exfalso. lia.
    + cbn. assert (Hk' : (length as' <= k')%nat) by (cbn in Hk; lia).
      apply (IH k' c Hk').
Qed.

(* firstn 对 app 的一般分段（firstn_app 的同形自建件） *)
Lemma hs_firstn_app_gen : forall (a : list Q) (k : nat) (c : list Q),
  firstn k (a ++ c) = firstn k a ++ firstn (k - length a) c.
Proof.
  induction a as [| x as' IH]; intros k c.
  - destruct k as [| k']; reflexivity.
  - destruct k as [| k']; [ reflexivity | cbn; rewrite (IH k' c); reflexivity ].
Qed.

(* ========== §2 保底件·局部周期律（clamp 语义诚实版） ========== *)

(* ①a 守卫版加法律：m + n 不越过表长时旋转次数相加。
   证法：l 分解 a=firstn n l / b=skipn n l（pose 折叠护 n 的
   替换面，U3 卡配方），rotc_rot_app 把 rotc n l 换位成 b++a，
   两侧各自切段后 app_assoc 重排收口。 *)
Theorem rotc_add_local : forall (m n : nat) (l : list Q),
  (m + n <= length l)%nat -> rotc m (rotc n l) = rotc (m + n) l.
Proof.
  intros m n l Hmn.
  assert (Hnle : (n <= length l)%nat) by lia.
  pose (a := firstn n l).
  pose (b := skipn n l).
  assert (Hla : (length a = n)%nat) by exact (firstn_length_le l Hnle).
  assert (Hsplit : l = a ++ b)
    by (unfold a, b; symmetry; apply firstn_skipn).
  assert (Hrot : rotc n l = b ++ a).
  { rewrite <- Hla. rewrite Hsplit. apply rotc_rot_app. }
  assert (Hll : (length l = length a + length b)%nat)
    by (rewrite Hsplit; apply length_app).
  assert (Hmb : (m <= length b)%nat) by lia.
  assert (Hage : (length a <= m + n)%nat) by lia.
  rewrite Hrot. rewrite Hsplit.
  unfold rotc.
  rewrite (hs_skipn_app_le b m a Hmb).
  rewrite (hs_firstn_app_le b m a Hmb).
  rewrite (hs_skipn_app_r a (m + n) b Hage).
  rewrite (hs_firstn_app_gen a (m + n) b).
  rewrite (rotc_firstn_all a (m + n) Hage).
  assert (Hsub : (m + n - length a = m)%nat) by lia.
  rewrite Hsub.
  rewrite <- app_assoc.
  reflexivity.
Qed.

(* ①b 真周期面=冻结形：k + 表长 转已越界，与整一圈同值冻结在 l *)
Theorem rotc_freeze_local : forall (k : nat) (l : list Q),
  rotc (k + length l) l = rotc (length l) l.
Proof.
  intros k l.
  assert (H1 : rotc (k + length l) l = l)
    by (apply rotc_ge_len_id; lia).
  rewrite H1. rewrite rotc_full. reflexivity.
Qed.

(* ①c 诚实裁决件一：无守卫周期式为假（闭反例 [0;1;2], k=1：
   rotc 4 l = l 而 rotc 1 l = [1;2;0]，非退化旋转在） *)
Theorem rotc_periodic_naive_false :
  exists (l : list Q) (k : nat), rotc (k + length l) l <> rotc k l.
Proof.
  exists [0;1;2], 1%nat.
  intro Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* ①c 诚实裁决件二：无守卫加法律为假（闭反例 [0;1;2], m=3, n=1：
   rotc 3 (rotc 1 l) = [1;2;0] 而 rotc 4 l = l） *)
Theorem rotc_add_naive_false :
  exists (l : list Q) (m n : nat), rotc m (rotc n l) <> rotc (m + n) l.
Proof.
  exists [0;1;2], 3%nat, 1%nat.
  intro Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* ========== §3 冻结引擎与旗舰 ========== *)

(* qmax2 吸收已有值：右支不更大时最大值就是左支（Qmax 幂等面） *)
Lemma qmax2_le : forall x y : Q, (y <= x)%Q -> (qmax2 x y <= x)%Q.
Proof.
  intros x y Hy. unfold qmax2. destruct (Qle_bool x y) eqn:E.
  - exact Hy.
  - apply Qle_refl.
Qed.

(* 主件·单调面（跨距版增补）：Hsup_cyc_mono（U8 已证防重引用）
   的相邻步拉成任意跨距 a <= b 的单调链 *)
Theorem Hsup_cyc_mono_from : forall (l : list Q) (a b : nat),
  (a <= b)%nat -> (Hsup_cyc l a <= Hsup_cyc l b)%Q.
Proof.
  intros l a b. induction b as [| b IH].
  - intros Ha. assert (H0 : a = 0%nat) by lia.
    rewrite H0. apply Qle_refl.
  - intros Ha. destruct (cyc_nat_le_gt_cases a b) as [Hle | Hgt].
    + apply (Qle_trans (Hsup_cyc l a) (Hsup_cyc l b) (Hsup_cyc l (S b))).
      * apply IH. exact Hle.
      * apply Hsup_cyc_mono.
    + assert (Ha' : (a = S b)%nat) by lia.
      rewrite Ha'. apply Qle_refl.
Qed.

(* 基值面：H_adj l 就是指标 0 处的谱值（rotc_0 的换算） *)
Lemma H_adj_eq_Hsup0 : forall l : list Q, (H_adj l == Hsup_cyc l 0)%Q.
Proof.
  intros l. cbn [Hsup_cyc]. rewrite rotc_0. apply Qeq_refl.
Qed.

(* 单步冻结：指标越过表长后，加测一转不改变上确界——
   新值 H_adj (rotc (S n) l) = H_adj l（rotc_ge_len_id），
   而 H_adj l <= Hsup_cyc l n（跨距单调链），qmax2 两向吸收 *)
Theorem Hsup_cyc_step_frozen : forall (l : list Q) (n : nat),
  (length l <= n)%nat -> Hsup_cyc l (S n) == Hsup_cyc l n.
Proof.
  intros l n Hn.
  assert (Hle : (length l <= S n)%nat) by lia.
  cbn [Hsup_cyc].
  rewrite (rotc_ge_len_id (S n) l Hle).
  apply Qle_antisym.
  - apply qmax2_le.
    apply (Qle_trans (H_adj l) (Hsup_cyc l 0) (Hsup_cyc l n)).
    + apply cyc_qeq_le. apply H_adj_eq_Hsup0.
    + apply (Hsup_cyc_mono_from l 0 n). lia.
  - apply qmax2_ub_l.
Qed.

(* ========== 旗舰·冻结定理：上确界在 n = 表长 处冻结 ========== *)
(* 路线：对 n 归纳；n >= 表长 支走单步冻结 + 归纳假设（Qeq 传递），
   n < 表长 支由 length l <= S n 夹出 length l = S n（同指数恒等）。 *)
Theorem Hsup_cyc_stable : forall (l : list Q) (n : nat),
  (length l <= n)%nat -> Hsup_cyc l n == Hsup_cyc l (length l).
Proof.
  intros l n. induction n as [| n IH].
  - intros Hn. destruct l as [| a rest].
    + apply Qeq_refl.
    + cbn in Hn. exfalso. lia.
  - intros Hn.
    destruct (cyc_nat_le_gt_cases (length l) n) as [Hle | Hgt].
    + apply (Qeq_trans (Hsup_cyc l (S n)) (Hsup_cyc l n)).
      * apply (Hsup_cyc_step_frozen l n Hle).
      * apply IH. exact Hle.
    + assert (Heq : (length l = S n)%nat) by lia.
      rewrite Heq. apply Qeq_refl.
Qed.

(* ========== §4 加分·谱有限性：旋转谱至多 length l 个不同值 ========== *)

(* 构造性归约：任意转数的 rotc 值都落在前 length l 个转数的谱内
   （k < 表长取 k' = k；k >= 表长取 k' = 0，越界冻结回 rotc 0） *)
Theorem rotc_spectrum_bound : forall (k : nat) (l : list Q),
  exists k' : nat, (k' <= length l - 1)%nat /\ rotc k l = rotc k' l.
Proof.
  intros k l.
  destruct (cyc_nat_le_gt_cases (S k) (length l)) as [Hlt | Hge].
  - exists k. split.
    + lia.
    + reflexivity.
  - assert (Hge' : (length l <= k)%nat) by lia.
    exists 0%nat. split.
    + lia.
    + rewrite (rotc_ge_len_id k l Hge'). rewrite rotc_0. reflexivity.
Qed.

(* 值域面：H_adj 谱同样被前 length l 个转数穷尽 *)
Theorem H_adj_spectrum_bound : forall (k : nat) (l : list Q),
  exists k' : nat,
    (k' <= length l - 1)%nat /\ H_adj (rotc k l) == H_adj (rotc k' l).
Proof.
  intros k l. destruct (rotc_spectrum_bound k l) as [k' [Hle Heq]].
  exists k'. split.
  - exact Hle.
  - rewrite Heq. apply Qeq_refl.
Qed.

(* 谱有限推论：上确界总在 i <= length l 的具体转数处取到
   （Hsup_cyc_attained 的见证越界时换到冻结指标 length l） *)
Theorem Hsup_cyc_attained_range : forall (l : list Q) (n : nat),
  exists i : nat, (i <= length l)%nat /\ Hsup_cyc l n == H_adj (rotc i l).
Proof.
  intros l n.
  destruct (Hsup_cyc_attained l n) as [i [Hin Hval]].
  destruct (cyc_nat_le_gt_cases (S i) (length l)) as [Hlt | Hge].
  - exists i. split.
    + lia.
    + exact Hval.
  - assert (Hge' : (length l <= i)%nat) by lia.
    rewrite (rotc_ge_len_id i l Hge') in Hval.
    exists (length l). split.
    + apply le_n.
    + rewrite rotc_full. exact Hval.
Qed.

(* ========== §5 数值锚 ========== *)

(* 见证列 [0;1;2]（表长 3）：n=5 已冻结，与 n=2 同值 3
   （谱 {2;3}，最大值在 k=1,2 取到）；旗舰闭项一发判定 *)
Theorem Hsup_cyc_stable_wit : Hsup_cyc [0;1;2] 5 == Hsup_cyc [0;1;2] 2.
Proof.
  change (Hsup_cyc [0;1;2] 5)
    with (qmax2 (qmax2 (qmax2 (qmax2 (qmax2 (H_adj (rotc 0 [0;1;2]))
              (H_adj (rotc 1 [0;1;2]))) (H_adj (rotc 2 [0;1;2])))
              (H_adj (rotc 3 [0;1;2]))) (H_adj (rotc 4 [0;1;2])))
              (H_adj (rotc 5 [0;1;2]))).
  change (Hsup_cyc [0;1;2] 2)
    with (qmax2 (qmax2 (H_adj (rotc 0 [0;1;2])) (H_adj (rotc 1 [0;1;2])))
              (H_adj (rotc 2 [0;1;2]))).
  reflexivity.
Qed.

(* 冻结值就是谱最大 3（对照 rotc_H_wit_mid 的中段锚） *)
Theorem Hsup_cyc_frozen_value_wit : Hsup_cyc [0;1;2] 7 == 3%Q.
Proof.
  change (Hsup_cyc [0;1;2] 7)
    with (qmax2 (qmax2 (qmax2 (qmax2 (qmax2 (qmax2 (qmax2
              (H_adj (rotc 0 [0;1;2])) (H_adj (rotc 1 [0;1;2])))
              (H_adj (rotc 2 [0;1;2]))) (H_adj (rotc 3 [0;1;2])))
              (H_adj (rotc 4 [0;1;2]))) (H_adj (rotc 5 [0;1;2])))
              (H_adj (rotc 6 [0;1;2]))) (H_adj (rotc 7 [0;1;2]))).
  reflexivity.
Qed.

(* ============================================================
   §S6 归并分隔注 —— 以下为原 DTPT_RotSpec.v 全文（S6a 整合棒并入）
   剥壳搬运：除头部六字段与 Require/Import 块外逐字保留，声明序与
   证法零改动；Module DTPT_RotSpec 壳删除（本段居 DTPT_Rotation 壳内），
   其名经 Import DTPT_Rotation. 原样可达。三对 U18-3 同语句异名件按任务卡
   裁决删本侧（rotc_add→rotc_add_local / rotc_periodic_full→
   rotc_freeze_local / rotc_add_unbounded_false→rotc_add_naive_false，
   删除点留注记，原件全文见 .retired_S6 快照）；RotSpec 头部 S5 棒
   实修注记（Import 序 ROTC 后置）随归并消化——其面 rotc 系短名自
   本段起指 §S5 内联副本（逐字同形，语义等价）。撞名预检与逐名裁决
   见本文件头【三】【四】。
   ============================================================ *)

(* S6b 棒消化注（原 S6a 盘面注记一行 Import 后置随 ROTC 退役删除）：
   ROTC 退役后无外部 rotc 常量可指——本段与 §S7 的 rotc 系短名及所
   消费前段件（rotc_ge_len_id/H_adj_rotc_exact_mid 系）一律解析至
   §S5 内联副本（逐字同形，语义等价；常量归一后 6a 所记 rewrite
   失配根源消解）。 *)

(* ========== §0 工具件 ========== *)

(* 二倍自界：0 <= s 时 s <= 2*s（边界支公共收口，cyc_le_triple 同配方） *)
Lemma rs_le_double : forall s : Q, (0 <= s)%Q -> (s <= 2 * s)%Q.
Proof.
  intros s Hs.
  assert (H2 : (2 * s == s + s)%Q) by ring.
  apply (Qle_trans s (s + s) (2 * s)).
  - apply (proj2 (Qle_0_sub' s (s + s))).
    assert (Hr : (s + s - s == s)%Q) by ring.
    rewrite Hr. exact Hs.
  - apply cyc_qeq_le. apply Qeq_sym. exact H2.
Qed.

(* ========== §1 保底件：有界组合律与周期冻结 ========== *)

(* —— S6a 去重收口（U18-3 表）：本侧原 §1 三件同语句异名件删除——
   rotc_add ≡ rotc_add_local、rotc_periodic_full ≡ rotc_freeze_local、
   rotc_add_unbounded_false ≡ rotc_add_naive_false（同判反例件，双见证
   [0;1;2] 均在册，仅 m,n 序异），改引本文件 Cyc 侧三件；其 Print
   Assumptions 覆盖由本文件既有审计行（rotc_add_local/rotc_freeze_local/
   rotc_add_naive_false）承担；原件全文见 DTPT_RotSpec.v.retired_S6。
   以下保留本侧陈述不同件（rotc_periodic 守卫锚形等）。 —— *)


(* 周期冻结·锚形：转数不小于表长时，再转整圈仍冻结原值 *)
Theorem rotc_periodic : forall (l : list Q) (k : nat),
  (length l <= k)%nat -> rotc (k + length l) l = rotc k l.
Proof.
  intros l k Hk.
  assert (H1 : (length l <= k + length l)%nat) by lia.
  rewrite (rotc_ge_len_id (k + length l) l H1).
  rewrite (rotc_ge_len_id k l Hk).
  reflexivity.
Qed.

(* 旋转类折回：任意转数都等于基本域 0..表长 内某转数的旋转 *)
Theorem rotc_class_folds : forall (l : list Q) (k : nat),
  exists j : nat, (j <= length l)%nat /\ rotc k l = rotc j l.
Proof.
  intros l k. destruct (cyc_nat_le_gt_cases (length l) k) as [Hge | Hlt].
  - (* length l <= k：越界面，折回 0（rotc_ge_len_id + rotc_0） *)
    exists 0%nat. split.
    + apply Nat.le_0_l.
    + rewrite (rotc_ge_len_id k l Hge).
      rewrite rotc_0.
      reflexivity.
  - (* k < length l：k 本身在基本域内 *)
    exists k. split.
    + lia.
    + reflexivity.
Qed.

(* ========== §2 接缝序：锐化引擎（a_k <= a_{k+1}） ========== *)

(* 尾非空剥头：lastq 在构造子尾上定向一步（simpl 卡死面的替代） *)
Lemma rs_lastq_cons_ne : forall (x : Q) (xs : list Q),
  xs <> [] -> lastq (x :: xs) = lastq xs.
Proof.
  intros x xs Hne. destruct xs as [| y ys].
  - exfalso. apply Hne. reflexivity.
  - reflexivity.
Qed.

(* 转点等元：firstn (S j) 的尾元 = skipn j 的首元（同为第 j+1 个元素）。
   对 l 归纳（被归纳者前置，IH 对 j 全称化——U8 参数序坑规避）。 *)
Lemma rs_lastq_firstn_hd_skipn : forall (l : list Q) (j : nat),
  (j < length l)%nat -> lastq (firstn (S j) l) = hd 0 (skipn j l).
Proof.
  induction l as [| a rest IH]; intros j Hj.
  - simpl in Hj. exfalso. lia.
  - destruct j as [| j'].
    + reflexivity.
    + simpl in Hj.
      assert (Hjr : (j' < length rest)%nat) by lia.
      assert (Hne : firstn (S j') rest <> []).
      { apply firstn_ne_of_lt; lia. }
      change (lastq (firstn (S (S j')) (a :: rest)))
        with (lastq (a :: firstn (S j') rest)).
      change (hd 0 (skipn (S j') (a :: rest)))
        with (hd 0 (skipn j' rest)).
      rewrite (rs_lastq_cons_ne a (firstn (S j') rest) Hne).
      apply IH. exact Hjr.
Qed.

(* 相邻段包含：skipn (S j) l 的成员都在 skipn j l 内 *)
Lemma rs_skipn_S_incl : forall (l : list Q) (j : nat) (z : Q),
  In z (skipn (S j) l) -> In z (skipn j l).
Proof.
  induction l as [| a rest IH]; intros j z Hin.
  - destruct j; simpl in Hin; destruct Hin.
  - destruct j as [| j'].
    + simpl in Hin. right. exact Hin.
    + simpl in Hin. simpl. exact (IH j' z Hin).
Qed.

(* 接缝序：1 <= k < 表长时 lastq (firstn k l) <= hd 0 (skipn k l)
   （第 k 元 <= 第 k+1 元，由 skipn (k-1) 段的排序性 + 段包含运输） *)
Lemma rs_seam_order : forall (l : list Q) (k : nat),
  SortedQ l -> (0 < k)%nat -> (k < length l)%nat ->
  (lastq (firstn k l) <= hd 0 (skipn k l))%Q.
Proof.
  intros l k HS H0 Hlt. destruct k as [| k'].
  - exfalso. lia.
  - assert (Hk' : (k' < length l)%nat) by lia.
    assert (E : lastq (firstn (S k') l) = hd 0 (skipn k' l))
      by exact (rs_lastq_firstn_hd_skipn l k' Hk').
    rewrite E.
    apply (sorted_hd_min (skipn k' l) (skipn_SortedQ l k' HS)
                         (hd 0 (skipn (S k') l))).
    apply (rs_skipn_S_incl l k' (hd 0 (skipn (S k') l))).
    apply xq_hd_In_gen. exact (skipn_ne_of_lt (S k') l Hlt).
Qed.

(* ========== §3 旗舰：2·spread 上界（锐化 U8 的 3·spread） ========== *)

Theorem rotc_class_sharp_ub : forall (l : list Q) (k : nat),
  SortedQ l -> (H_adj (rotc k l) <= 2 * (lastq l - hd 0 l))%Q.
Proof.
  intros l k HS.
  assert (Hsp : (0 <= lastq l - hd 0 l)%Q).
  { apply (proj1 (Qle_0_sub' (hd 0 l) (lastq l))).
    apply xq_hd_le_lastq. exact HS. }
  destruct (cyc_nat_le_gt_cases (length l) k) as [Hge | Hlt].
  - (* k >= 表长：恒等支，spread <= 2*spread *)
    rewrite (rotc_ge_len_id k l Hge).
    apply (Qle_trans (H_adj l) (lastq l - hd 0 l)
                     (2 * (lastq l - hd 0 l))).
    + apply cyc_qeq_le. apply xq_telescope. exact HS.
    + apply rs_le_double. exact Hsp.
  - destruct k as [| k'].
    + (* 零转支：同恒等支 *)
      rewrite rotc_0.
      apply (Qle_trans (H_adj l) (lastq l - hd 0 l)
                       (2 * (lastq l - hd 0 l))).
      * apply cyc_qeq_le. apply xq_telescope. exact HS.
      * apply rs_le_double. exact Hsp.
    + (* 中段支：U8 三项闭式 + 接缝序收敛首尾两项 *)
      assert (H1 : (1 <= S k')%nat) by lia.
      assert (HEm : H_adj (rotc (S k') l)
                    == (lastq l - hd 0 (skipn (S k') l))
                     + (lastq l - hd 0 l)
                     + (lastq (firstn (S k') l) - hd 0 l))
        by exact (H_adj_rotc_exact_mid (S k') l HS H1 Hlt).
      assert (Hseam : (lastq (firstn (S k') l)
                       <= hd 0 (skipn (S k') l))%Q)
        by exact (rs_seam_order l (S k') HS H1 Hlt).
      (* 首尾两项之和 <= spread：(a_n−a_{k+1}) + (a_k−a_1) <= a_n−a_1
         由 a_k <= a_{k+1}（接缝序）经 Qle_0_sub' + ring 收口 *)
      assert (Hsum : ((lastq l - hd 0 (skipn (S k') l))
                     + (lastq (firstn (S k') l) - hd 0 l)
                     <= (lastq l - hd 0 l))%Q).
      { apply (proj2 (Qle_0_sub' _ _)).
        assert (Hr : (lastq l - hd 0 l
                      - ((lastq l - hd 0 (skipn (S k') l))
                         + (lastq (firstn (S k') l) - hd 0 l))
                      == hd 0 (skipn (S k') l)
                         - lastq (firstn (S k') l))%Q) by ring.
        rewrite Hr.
        apply (proj1 (Qle_0_sub' (lastq (firstn (S k') l))
                                 (hd 0 (skipn (S k') l)))).
        exact Hseam. }
      apply (Qle_trans _ ((lastq l - hd 0 (skipn (S k') l))
                        + (lastq (firstn (S k') l) - hd 0 l)
                        + (lastq l - hd 0 l))
                        (2 * (lastq l - hd 0 l))).
      * apply cyc_qeq_le. apply (Qeq_trans _ _ _ HEm). ring.
      * assert (H2s : (2 * (lastq l - hd 0 l)
                       == (lastq l - hd 0 l) + (lastq l - hd 0 l))%Q)
          by ring.
        rewrite H2s.
        apply qadd_le.
        -- exact Hsum.
        -- apply Qle_refl.
Qed.

(* ========== §4 主件：锐性取得（界不可再降） ========== *)

(* 见证列 [0;0;2] 排序性（构造子逐层装配 + 字面 Qle 布尔反射） *)
Lemma sorted_wit_002 : SortedQ [0; 0; 2].
Proof.
  apply sortQ_cons.
  - apply sortQ_cons.
    + apply sortQ_cons.
      * apply sortQ_nil.
      * apply Forall_nil.
    + apply Forall_forall. intros z Hz. simpl in Hz.
      destruct Hz as [E | []]; subst z.
      * apply xq_Qle_bool_le. vm_compute. reflexivity.
  - apply Forall_forall. intros z Hz. simpl in Hz.
    destruct Hz as [E | [E | []]]; subst z.
    + apply xq_Qle_bool_le. vm_compute. reflexivity.
    + apply xq_Qle_bool_le. vm_compute. reflexivity.
Qed.

(* 锐性取得：存在排序表与转数使 H_adj (rotc k l) 恰为 2*spread。
   [0;0;2] 转 1 格 = [0;2;0]：H_adj = 2 + 2 = 4 = 2 * (2 - 0)。
   与 rotc_class_sharp_ub 合成：常数 2 是旋转谱上界的精确值。 *)
Theorem rotc_class_sharp_attained : exists (l : list Q) (k : nat),
  SortedQ l /\ H_adj (rotc k l) == 2 * (lastq l - hd 0 l).
Proof.
  exists [0; 0; 2], 1%nat.
  split.
  - apply sorted_wit_002.
  - vm_compute. reflexivity.
Qed.

(* ========== §5 公理面审计（G4） ========== *)

(* S6a 注：原 §5 审计 8 件中 rotc_add/rotc_add_unbounded_false/
   rotc_periodic_full 三件已按 U18-3 表删除（见上【S6a 去重收口】注），
   其覆盖由本文件既有 Cyc 侧审计行承担。 *)

Print Assumptions rotc_periodic.
Print Assumptions rotc_class_folds.
Print Assumptions rs_seam_order.
Print Assumptions rotc_class_sharp_ub.
Print Assumptions rotc_class_sharp_attained.

(* —— 原件 DTPT_RotSpec.v 头部【四】逐字随行（S6a 收编为段内注，下起
   十行含原头行照录，防「见本文件头【四】」悬空指针；原件全文另见
   快照 DTPT_RotSpec.v.retired_S6）——
   【四·对账注记（phcyc_min_perm 去重取证）】
     phcyc_min_perm 与 DTPT_CGen.C_gen 同语句（U18-2 已声明本地重推，
     因 C_gen 所在件不在原件允许清单）。M5 去重取证：现役底座
     （DTPT/DTPT_ROTC/DTPT_Entropy/DTPT_Cyc/DTPT_Entropy2）中排序
     最小化仅有 DTPT.C_sorted_min_adj（Permutation l l 恒等特例：
     forall l, H_adj (P0 l) <= H_adj l），排列类全称形不可由其直推
     （须置换搬运 + 跨度下界 + Qeq 链全套骨架）；C_gen 在
     DTPT_CGen.v，位于本文件现 Require 面之外，整合令未授权新增
     Require。结论：保留本地 phcyc_min_perm 并注记，禁硬凑；后续
     若全库 Require 面收编 DTPT_CGen，可改引 C_gen 并删本地版。
   —— *)


(* ===================================================================== *)
(* 及 stdlib 导入，均与本文件现有 Require 重合可达）外逐字保留，声明序与    *)
(* 证法零改动。phcyc_min_perm 去重取证与对账注记见本文件头【四】。           *)
(* ===================================================================== *)
(* ===================================================================== *)
(* §1 排序最小化的排列类泛化（底座材料本地重构）                            *)
(* ===================================================================== *)

(* C_gen 同构重推：P0 l 是 l 的排列类上 H_adj 的最小值。
   骨架：非空表望远镜展开 H_adj (P0 l) == lastq - hd，首尾两元经置换
   搬进 p，跨度下界 xq_pair_dist_le 压住，Qeq 链收口。
   逐引理出处（全部 DTPT.v 现役）：xq_P0_cons_ne / xq_telescope /
   xq_P0_sorted / xq_abs_sub_comm / xq_abs_id / Qle_0_sub' /
   xq_hd_le_lastq / D5_P0_perm / xq_hd_In_gen / xq_lastq_In /
   xq_pair_dist_le。 *)
Lemma phcyc_min_perm : forall (l p : list Q),
  Permutation l p -> H_adj (P0 l) <= H_adj p.
Proof.
  intros l p Hperm. destruct l as [| a rest].
  - assert (Hp : p = []) by (apply Permutation_nil; exact Hperm).
    rewrite Hp. apply Qle_refl.
  - assert (Hne : P0 (a :: rest) <> []) by (apply xq_P0_cons_ne).
    assert (HP : H_adj (P0 (a :: rest))
                 == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest)))
      by (apply xq_telescope; apply xq_P0_sorted).
    assert (HP2 : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest))).
    { rewrite (xq_abs_sub_comm (hd 0 (P0 (a :: rest))) (lastq (P0 (a :: rest)))).
      apply xq_abs_id.
      apply (proj1 (Qle_0_sub' _ _)).
      apply xq_hd_le_lastq. apply xq_P0_sorted. }
    assert (Hrev : Permutation (P0 (a :: rest)) (a :: rest))
      by (apply Permutation_sym; apply D5_P0_perm).
    assert (HpermP : Permutation (P0 (a :: rest)) p).
    { apply perm_trans with (l' := a :: rest).
      - exact Hrev.
      - exact Hperm. }
    assert (Hm1 : In (hd 0 (P0 (a :: rest))) p).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - exact HpermP.
      - apply xq_hd_In_gen. exact Hne. }
    assert (Hm2 : In (lastq (P0 (a :: rest))) p).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - exact HpermP.
      - apply xq_lastq_In. exact Hne. }
    assert (HPd : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  <= H_adj p)
      by (apply xq_pair_dist_le; assumption).
    rewrite HP. rewrite <- HP2. exact HPd.
Qed.

(* ===================================================================== *)
(* §2 退化实证：Qle_bool 形判别器恒返 true（「不能比大小」的定理化）         *)
(* ===================================================================== *)

(* 仿旧 phase_side 的 cyc 判别面：Qle_bool (H_adj (P0 l)) (H_adj (rotc k l))
   由 C_gen 泛化（rotc k l 是排列）恒真——该判别器无分辨力。 *)
Theorem phase_side_cyc_side_degenerate :
  forall (l : list Q) (k : nat),
    Qle_bool (H_adj (P0 l)) (H_adj (rotc k l)) = true.
Proof.
  intros l k. apply xq_Qle_bool_true.
  apply phcyc_min_perm. apply rotc_perm.
Qed.

(* 旧式 0/1 判别器形：if Qle_bool ... then 0 else 1 恒返 0（%nat）。 *)
Theorem phase_side_cyc_side_zero :
  forall (l : list Q) (k : nat),
    (if Qle_bool (H_adj (P0 l)) (H_adj (rotc k l)) then 0 else 1)%nat = 0%nat.
Proof.
  intros l k. rewrite phase_side_cyc_side_degenerate. reflexivity.
Qed.

(* ===================================================================== *)
(* §3 旗舰：偏差检测器 phase_dev 与行为定理                                 *)
(* ===================================================================== *)

(* 偏差检测器：检测真旋转相是否（记录层）偏离排序相。
   注意 Qeq_bool 是 Q Record 的原始对比较（分子分母各判等），
   非数值 Qeq 相等——这既是本节定理的口径，也是 §4 诚实障碍的根源。 *)
Definition phase_dev (l : list Q) (k : nat) : bool :=
  negb (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l))).

(* ① 存在性见证：l = [0;1;2]，k = 1 时 H_adj 侧 2#1 与 3#1 记录不等，
   偏差被判出（vm_compute 闭式钉死）。 *)
Theorem phase_dev_witness : exists (l : list Q) (k : nat), phase_dev l k = true.
Proof.
  exists [0; 1; 2]. exists 1%nat. vm_compute. reflexivity.
Qed.

(* ①' 定义 iff 桥：偏差为真 iff 记录层 Qeq_bool 判 false。 *)
Theorem phase_dev_true_iff :
  forall (l : list Q) (k : nat),
    phase_dev l k = true <-> Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l)) = false.
Proof.
  intros l k. unfold phase_dev. split.
  - intro H. destruct (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l))) eqn:E.
    + simpl in H. discriminate H.
    + reflexivity.
  - intro H. rewrite H. reflexivity.
Qed.

(* ② 严格向·记录面：偏差给出两侧的记录层不等。 *)
Theorem phase_dev_rec_ne :
  forall (l : list Q) (k : nat),
    phase_dev l k = true -> H_adj (P0 l) <> H_adj (rotc k l).
Proof.
  intros l k H Heq. unfold phase_dev in H.
  rewrite Heq in H. rewrite Qeq_bool_refl in H. simpl in H. discriminate H.
Qed.

(* ② 严格向·序面：偏差时排序相仍不超过真旋转相（C_gen 面恒真）。 *)
Theorem phase_dev_le :
  forall (l : list Q) (k : nat),
    phase_dev l k = true -> H_adj (P0 l) <= H_adj (rotc k l).
Proof.
  intros l k _. apply phcyc_min_perm. apply rotc_perm.
Qed.

(* ② 严格向·数值升格小引理：Qle_bool 反向判 false 即数值严格小于。
   这是「≤ 且数值不等则 <」的诚实形——Qle_bool/Qlt 都是 Qeq 兼容的
   数值关系，而任务拟用的记录层 Qeq_bool = false 只给记录不等，
   与数值不等不等价（1/2 与 2/4 反例），故升格必须走数值判别面。 *)
Lemma phcyc_qle_false_lt : forall x y : Q, Qle_bool y x = false -> (x < y)%Q.
Proof.
  intros [nx dx] [ny dy]. unfold Qle_bool, Qlt; simpl. intros H.
  apply Z.leb_gt in H. exact H.
Qed.

(* ② 严格向·组合件：数值判别（Qle_bool 反向 false）一次给出
   偏差为真 与 数值严格小于 H_adj (P0 l) < H_adj (rotc k l)。 *)
Theorem phase_dev_strict_of_num :
  forall (l : list Q) (k : nat),
    Qle_bool (H_adj (rotc k l)) (H_adj (P0 l)) = false ->
    phase_dev l k = true /\ (H_adj (P0 l) < H_adj (rotc k l))%Q.
Proof.
  intros l k Hfalse.
  assert (Hlt : (H_adj (P0 l) < H_adj (rotc k l))%Q)
    by (apply phcyc_qle_false_lt; exact Hfalse).
  split.
  - unfold phase_dev.
    destruct (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l))) eqn:E.
    + exfalso.
      assert (Hba : (H_adj (rotc k l) <= H_adj (P0 l))%Q).
      { apply (xq_Qeq_le (H_adj (rotc k l)) (H_adj (P0 l))).
        exact (Qeq_sym (H_adj (P0 l)) (H_adj (rotc k l))
                       (Qeq_bool_eq (H_adj (P0 l)) (H_adj (rotc k l)) E)). }
      rewrite (xq_Qle_bool_true _ _ Hba) in Hfalse. discriminate.
    + reflexivity.
  - exact Hlt.
Qed.

(* ③ 相位稳定性（iff 的 == 侧）：不偏差时两侧数值（记录更强）相等。
   Qeq_bool = true 给记录相等，进而 Qeq 数值相等。 *)
Theorem phase_dev_stable :
  forall (l : list Q) (k : nat),
    phase_dev l k = false -> H_adj (rotc k l) == H_adj (P0 l).
Proof.
  intros l k H. unfold phase_dev in H.
  destruct (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l))) eqn:E.
  - apply Qeq_sym. apply Qeq_bool_eq. exact E.
  - simpl in H. discriminate H.
Qed.

(* ===================================================================== *)
(* §4 k=0 面：相位无旋恒等 + 诚实障碍定谳                                   *)
(* ===================================================================== *)

(* k=0 旋转恒等：rotc 0 l = l，相位（H_adj）数值不变。 *)
Lemma rotc_0_H_adj : forall l : list Q, H_adj (rotc 0 l) == H_adj l.
Proof.
  intros l. rewrite rotc_0. apply Qeq_refl.
Qed.

(* k=0 计算形：偏差化为「排序相 vs 原相位」的记录比较。 *)
Theorem phase_dev_0_eq :
  forall l : list Q,
    phase_dev l 0 = negb (Qeq_bool (H_adj (P0 l)) (H_adj l)).
Proof.
  intro l. unfold phase_dev. rewrite rotc_0. reflexivity.
Qed.

(* k=0 恒不偏差的可证形（条件版）：表已排序（P0 l = l）时零偏差。 *)
Theorem phase_dev_0_of_sorted :
  forall l : list Q, P0 l = l -> phase_dev l 0 = false.
Proof.
  intros l HP. unfold phase_dev. rewrite rotc_0, HP.
  rewrite (Qeqb_true_of (H_adj l) (H_adj l) (Qeq_refl (H_adj l))).
  reflexivity.
Qed.

(* 已排序实例见证：[0;1;2] 在 k=0 无偏差（vm_compute 闭式）。 *)
Theorem phase_dev_0_sorted_example : phase_dev [0; 1; 2] 0 = false.
Proof. vm_compute. reflexivity. Qed.

(* 诚实障碍定谳（反例见证）：任务拟述的「phase_dev l 0 = false 全称」
   在 Q Record 面为假——未排序表 [0;2;1] 在 k=0 判出偏差（其排序相
   H_adj = 2#1 与原相位 H_adj = 3#1 记录不等）。故无条件版不可立，
   以条件版 phase_dev_0_of_sorted + 本见证定谳。 *)
Theorem phase_dev_0_unsorted_counterex : phase_dev [0; 2; 1] 0 = true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   §S7 归并分隔注 —— 以下为原 DTPT_Lam.v 全文（S6a 整合棒并入）
   剥壳搬运：除头部与 Require/Import 块外逐字保留（其 M3 归并段注记
   随行零丢失），声明序与证法零改动；Module DTPT_Lam 壳删除（本段
   居 DTPT_Rotation 壳内），其名经 Import DTPT_Rotation. 原样可达。其 Require
   DTPT_ROTC 删——rotc/rotc_0 自本段起指 §S5 内联副本（逐字同形，
   语义等价）；Require DTPT/DTPT_Entropy 经本文件现有 Require 可达；
   其头部 Open Scope Q_scope 随行（本段陈述含无 %Q 标注裸项）。
   撞名预检：34 顶层名对本文件既有名零精确撞名（见本文件头【三】）。
   ============================================================ *)

(* 原件头部 Open Scope Q_scope 随行（S6a）。 *)
Open Scope Q_scope.

(* ========== 【旗舰基座】仿射差分恒等式（无前提 Qeq 代数泛形） ========== *)

(* 泛形：lam ↦ lam·h0 + (1-lam)·h1 的差分 = (lam1-lam2)·(h0-h1)。
   变量序取 λ 在前（与 H_lam 定义 lam * H_adj (P0 l) 同序，消费零换序成本）。
   防御式收口：二目 Qminus 全部 change 成 1 + - x 加法形再 ring
   （qlia 卡第 12 条配方，H_lam_mono 同款模板）。 *)
Lemma lam_affine_diff_sub : forall h0 h1 lam1 lam2 : Q,
  lam1 * h0 + (1 - lam1) * h1 - (lam2 * h0 + (1 - lam2) * h1)
  == (lam1 - lam2) * (h0 - h1).
Proof.
  intros h0 h1 lam1 lam2.
  change (1 - lam1) with (1 + - lam1)%Q.
  change (1 - lam2) with (1 + - lam2)%Q.
  change (lam1 - lam2) with (lam1 + - lam2)%Q.
  change (h0 - h1) with (h0 + - h1)%Q.
  change ((lam1 * h0 + (1 + - lam1) * h1) - (lam2 * h0 + (1 + - lam2) * h1))
    with ((lam1 * h0 + (1 + - lam1) * h1)
          + - (lam2 * h0 + (1 + - lam2) * h1))%Q.
  ring.
Qed.

(* H_lam 实形的差分恒等式：H_lam l s lam1 - H_lam l s lam2
   = (lam1 - lam2) * (H_adj (P0 l) - H_adj (Pinf l s))。 *)
Theorem H_lam_diff_sub : forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  H_lam l s lam1 - H_lam l s lam2
  == (lam1 - lam2) * (H_adj (P0 l) - H_adj (Pinf l s)).
Proof.
  intros l s lam1 lam2. unfold H_lam.
  exact (lam_affine_diff_sub (H_adj (P0 l)) (H_adj (Pinf l s)) lam1 lam2).
Qed.

(* 仿射标准形：H_lam l s lam = h1 + lam * (h0 - h1)。 *)
Theorem H_lam_affine : forall (l : list Q) (s : nat) (lam : Q),
  H_lam l s lam == H_adj (Pinf l s) + lam * (H_adj (P0 l) - H_adj (Pinf l s)).
Proof.
  intros l s lam. unfold H_lam.
  change (1 - lam) with (1 + - lam)%Q.
  change (H_adj (P0 l) - H_adj (Pinf l s))
    with (H_adj (P0 l) + - H_adj (Pinf l s))%Q.
  ring.
Qed.

(* ========== 【旗舰】反向单调：零前提真方向 ========== *)

(* 真单调方向：λ 增 ⟹ H_lam 减。斜率 h0 - h1 <= 0（跨相下界恒成立）
   × (lam1 - lam2) <= 0，两非正之积非负——经 xq_mul_nonneg 两次反号装配。 *)
Theorem H_lam_anti_mono : forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  (lam1 <= lam2)%Q -> (H_lam l s lam2 <= H_lam l s lam1)%Q.
Proof.
  intros l s lam1 lam2 Hlam.
  (* 两因子皆非正：(lam1-lam2) <= 0 且 (h0-h1) <= 0（跨相下界）
     ——先换位成两非正的反号 (lam2-lam1)·(h1-h0) 再做非负乘法装配。 *)
  assert (Hs : (0 <= (lam1 - lam2) * (H_adj (P0 l) - H_adj (Pinf l s)))%Q).
  { assert (Hr : (lam1 - lam2) * (H_adj (P0 l) - H_adj (Pinf l s))
                 == (lam2 - lam1) * (H_adj (Pinf l s) - H_adj (P0 l))).
    { change (lam1 - lam2) with (lam1 + - lam2)%Q.
      change (lam2 - lam1) with (lam2 + - lam1)%Q.
      change (H_adj (P0 l) - H_adj (Pinf l s))
        with (H_adj (P0 l) + - H_adj (Pinf l s))%Q.
      change (H_adj (Pinf l s) - H_adj (P0 l))
        with (H_adj (Pinf l s) + - H_adj (P0 l))%Q.
      ring. }
    rewrite Hr. apply xq_mul_nonneg.
    - apply (proj1 (Qle_0_sub' lam1 lam2)). exact Hlam.
    - apply (proj1 (Qle_0_sub' (H_adj (P0 l)) (H_adj (Pinf l s)))).
      apply H_adj_cross_phase_lb. }
  apply (proj2 (Qle_0_sub' _ _)).
  rewrite (H_lam_diff_sub l s lam1 lam2). exact Hs.
Qed.

(* 递增方向（h1 <= h0 前提下）：既有 H_lam_mono 的差分恒等式重述版。 *)
Theorem H_lam_mono_diff : forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  (H_adj (Pinf l s) <= H_adj (P0 l))%Q ->
  (lam1 <= lam2)%Q -> (H_lam l s lam1 <= H_lam l s lam2)%Q.
Proof.
  intros l s lam1 lam2 Hle Hlam.
  assert (Hs : (0 <= (lam2 - lam1) * (H_adj (P0 l) - H_adj (Pinf l s)))%Q).
  { apply xq_mul_nonneg.
    - apply (proj1 (Qle_0_sub' lam1 lam2)). exact Hlam.
    - apply (proj1 (Qle_0_sub' (H_adj (Pinf l s)) (H_adj (P0 l)))). exact Hle. }
  apply (proj2 (Qle_0_sub' _ _)).
  rewrite (H_lam_diff_sub l s lam2 lam1). exact Hs.
Qed.

(* 斜率为零（h0 == h1）时 H_lam 为常数——既有 mono 空洞性的显式化：
   该情形下两个方向同时成立且结论平庸。 *)
Theorem H_lam_const_when_eq : forall (l : list Q) (s : nat) (lam : Q),
  H_adj (P0 l) == H_adj (Pinf l s) -> H_lam l s lam == H_adj (P0 l).
Proof.
  intros l s lam Heq. unfold H_lam. rewrite Heq. ring.
Qed.

(* 中点凸性等式面（仿射性的对称刻画；除法目标走 field）。 *)
Theorem H_lam_midpoint : forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  H_lam l s ((lam1 + lam2) / 2) == (H_lam l s lam1 + H_lam l s lam2) / 2.
Proof.
  intros l s lam1 lam2. unfold H_lam.
  change (1 - (lam1 + lam2) / 2) with (1 + - ((lam1 + lam2) / 2))%Q.
  change (1 - lam1) with (1 + - lam1)%Q.
  change (1 - lam2) with (1 + - lam2)%Q.
  field.
Qed.

(* ========== 【主件】λ-argmin 构造性：显式端点选择器 ========== *)

(* 最优 λ 的显式选择器：h0 <= h1 时取端点 1（递减到底），否则取端点 0。 *)
Definition lam_opt (h0 h1 : Q) : Q := if Qle_bool h0 h1 then 1 else 0.

Theorem lam_opt_values : forall h0 h1 : Q,
  lam_opt h0 h1 = 1%Q \/ lam_opt h0 h1 = 0%Q.
Proof.
  intros h0 h1. unfold lam_opt.
  destruct (Qle_bool h0 h1).
  - left. reflexivity.
  - right. reflexivity.
Qed.

Theorem lam_opt_range : forall h0 h1 : Q, (0 <= lam_opt h0 h1 <= 1)%Q.
Proof.
  intros h0 h1. destruct (lam_opt_values h0 h1) as [E | E].
  - rewrite E. split.
    + exact (xq_Qle_bool_le 0 1 eq_refl).
    + apply Qle_refl.
  - rewrite E. split.
    + apply Qle_refl.
    + exact (xq_Qle_bool_le 0 1 eq_refl).
Qed.

(* 最优值定理（泛形）：端点选择器的取值不超过 [0,1] 内任意 λ 的取值。
   两分支各化归一次乘法非负装配：
   h0 <= h1 分支取 λ*=1，差 = (1-lam)·(h1-h0)；否则取 λ*=0，差 = lam·(h0-h1)。 *)
Theorem lam_opt_min : forall (h0 h1 lam : Q),
  (0 <= lam <= 1)%Q ->
  (lam_opt h0 h1 * h0 + (1 - lam_opt h0 h1) * h1
   <= lam * h0 + (1 - lam) * h1)%Q.
Proof.
  intros h0 h1 lam H01. destruct H01 as [Hlam0 Hlam1].
  unfold lam_opt. destruct (Qle_bool h0 h1) eqn:E.
  - (* h0 <= h1：λ* = 1，最优值 = h0 *)
    assert (Hd : (0 <= lam * h0 + (1 - lam) * h1 - (1 * h0 + (1 - 1) * h1))%Q).
    { assert (Er : lam * h0 + (1 - lam) * h1 - (1 * h0 + (1 - 1) * h1)
                   == (1 - lam) * (h1 - h0)) by ring.
      rewrite Er. apply xq_mul_nonneg.
      + apply (proj1 (Qle_0_sub' lam 1)). exact Hlam1.
      + apply (proj1 (Qle_0_sub' h0 h1)). apply xq_Qle_bool_le. exact E. }
    apply (proj2 (Qle_0_sub' _ _)). exact Hd.
  - (* h0 > h1：λ* = 0，最优值 = h1 *)
    assert (Hge : (h1 <= h0)%Q) by (apply Qle_bool_false_le; exact E).
    assert (Hd : (0 <= lam * h0 + (1 - lam) * h1 - (0 * h0 + (1 - 0) * h1))%Q).
    { assert (Er : lam * h0 + (1 - lam) * h1 - (0 * h0 + (1 - 0) * h1)
                   == lam * (h0 - h1)) by ring.
      rewrite Er. apply xq_mul_nonneg.
      + exact Hlam0.
      + apply (proj1 (Qle_0_sub' h1 h0)). exact Hge. }
    apply (proj2 (Qle_0_sub' _ _)). exact Hd.
Qed.

(* H_lam 消费版：端点选择器在混合熵上实现 argmin。 *)
Theorem H_lam_lam_opt_min : forall (l : list Q) (s : nat) (lam : Q),
  (0 <= lam <= 1)%Q ->
  (H_lam l s (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s)))
   <= H_lam l s lam)%Q.
Proof.
  intros l s lam H01. destruct H01 as [Hlam0 Hlam1].
  unfold H_lam. apply lam_opt_min. split; assumption.
Qed.

(* 端点求值桥：选择器的取值恒为某一端的相熵（直用底座端点件）。 *)
Theorem H_lam_lam_opt_endpoint : forall (l : list Q) (s : nat),
  H_lam l s (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))) == H_adj (P0 l)
  \/ H_lam l s (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))) == H_adj (Pinf l s).
Proof.
  intros l s. destruct (lam_opt_values (H_adj (P0 l)) (H_adj (Pinf l s)))
    as [E | E].
  - left. rewrite E. apply H_lam_lam1.
  - right. rewrite E. apply H_lam_lam0.
Qed.

(* 诚实锚：本盘跨相下界恒给出 h0 <= h1，故端点选择器恒返 1（P0 相）。
   argmin 的价值在一般代数框架（h0 h1 泛形）而非本盘特值。 *)
Theorem lam_opt_cross_phase : forall (l : list Q) (s : nat),
  lam_opt (H_adj (P0 l)) (H_adj (Pinf l s)) = 1%Q.
Proof.
  intros l s. unfold lam_opt.
  rewrite (xq_Qle_bool_true _ _ (H_adj_cross_phase_lb l s)). reflexivity.
Qed.

(* ========== 【主件】align_lambda 救活：首三个定理消费 ========== *)

(* 底座 L69 的 align_lambda 是字面恒等定义（全盘零消费）。
   本块给它补上行为面：定义即恒等的 eta 面 + 熵面不变 + argmin 稳定性。 *)

Theorem align_lambda_id : forall lam : Q, align_lambda lam == lam.
Proof.
  intro lam. unfold align_lambda. exact (Qeq_refl lam).
Qed.

Theorem align_lambda_H_lam : forall (l : list Q) (s : nat) (lam : Q),
  H_lam l s (align_lambda lam) == H_lam l s lam.
Proof.
  (* 恒等定义即 eta 面：unfold 后两侧语法同形，reflexivity 直收
     （Qeq 面内的 rewrite 也救不了 H_lam 应用实参位——该位无 Proper 实例） *)
  intros l s lam. unfold align_lambda. reflexivity.
Qed.

(* argmin 稳定性：对 λ 先 align 再求值，最优值定理照旧成立。 *)
Theorem lam_opt_min_align : forall (l : list Q) (s : nat) (lam : Q),
  (0 <= lam <= 1)%Q ->
  (H_lam l s (align_lambda (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))))
   <= H_lam l s lam)%Q.
Proof.
  intros l s lam H01. destruct H01 as [Hlam0 Hlam1].
  (* Qle 目标下 H_lam 应用实参无 Proper 实例、Qminus 实参更断 setoid 路径
     ——改走 Qeq 面中转：align_lambda_H_lam（Qeq 目标内改写合法）+ Qeq_le 桥 *)
  apply (Qle_trans _ (H_lam l s (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))))).
  - apply xq_Qeq_le. apply align_lambda_H_lam.
  - apply H_lam_lam_opt_min. split; assumption.
Qed.

(* align 保持区间：align_lambda 的像仍在 [0,1] 内。 *)
Theorem align_lambda_range : forall lam : Q,
  (0 <= lam <= 1)%Q -> (0 <= align_lambda lam <= 1)%Q.
Proof.
  intros lam Hr. destruct Hr as [H0 H1]. split.
  - exact H0.
  - exact H1.
Qed.

(* ========== 【加分项】端点外插警戒：越出 [0,1] 即可越出端点带 ========== *)

(* 1 < lam 时 H_lam 可跌破下端 min{h0,h1}：见证列 [1;5;2]
   （h0 = H_adj [1;2;5] = 4，h1 = H_adj [1;5;2] = 7，h0 <= h1 恒成立），
   取 lam = 2 得 H_lam = 2·4 + (1-2)·7 = 1 < 4 = min。vm_compute 数值面。 *)
Theorem H_lam_extrap_below_counterex : exists (l : list Q) (s : nat) (lam : Q),
  (1 < lam)%Q /\
  (H_lam l s lam < H_adj (P0 l))%Q /\
  (H_adj (P0 l) <= H_adj (Pinf l s))%Q.
Proof.
  exists [1; 5; 2], 0%nat, 2%Q. split.
  - vm_compute. reflexivity.
  - split.
    + vm_compute. reflexivity.
    + apply H_adj_cross_phase_lb.
Qed.

(* 对偶面：lam < 0 时 H_lam 可跃升越上端 max{h0,h1}：同一见证列取 lam = -1
   得 H_lam = (-1)·4 + (1-(-1))·7 = 10 > 7 = max。 *)
Theorem H_lam_extrap_above_counterex : exists (l : list Q) (s : nat) (lam : Q),
  (lam < 0)%Q /\
  (H_adj (Pinf l s) < H_lam l s lam)%Q /\
  (H_adj (P0 l) <= H_adj (Pinf l s))%Q.
Proof.
  exists [1; 5; 2], 0%nat, (-1)%Q. split.
  - vm_compute. reflexivity.
  - split.
    + vm_compute. reflexivity.
    + apply H_adj_cross_phase_lb.
Qed.

(* ############################################################
   M3 归并段【U19 件 · 真旋转底座 λ-相位插值族】
   原独立文件整体并入：内容零改动，仅删其对本文件的 Require 行
   （变同文件直引，对 DTPT / DTPT_ROTC / DTPT_Entropy 的 Require
   保留——本文件由此新增对 DTPT_ROTC 的依赖）、审计并档文尾。
   ############################################################ *)

(* ========== 【保底】定义 + 端点 ========== *)

(* 真底座 λ-相位插值：λ=1 全落排序相 P0，λ=0 全落 k 格真旋转相。 *)
Definition H_lam_cyc (l : list Q) (k : nat) (lam : Q) : Q :=
  lam * H_adj (P0 l) + (1 - lam) * H_adj (rotc k l).

(* 端点 λ=1：零乘一乘后只余 P0 相（k 无关——排序端与转数解耦）。 *)
Theorem H_lam_cyc_lam1 : forall (l : list Q) (k : nat),
  H_lam_cyc l k 1 == H_adj (P0 l).
Proof.
  intros l k. unfold H_lam_cyc.
  replace (1 - 1)%Q with 0%Q by reflexivity.
  ring.
Qed.

(* 端点 λ=0：零乘一乘后只余 k 格真旋转相。 *)
Theorem H_lam_cyc_lam0 : forall (l : list Q) (k : nat),
  H_lam_cyc l k 0 == H_adj (rotc k l).
Proof.
  intros l k. unfold H_lam_cyc.
  replace (1 - 0)%Q with 1%Q by reflexivity.
  ring.
Qed.

(* 诚实锚·旧件退化面桥：零转相点 k=0 上真底座插值与旧件 s-坍缩面
   （Pinf 恒等 ⟹ 第二端即原始序 l）完全重合——迁移不丢旧信息。 *)
Theorem H_lam_cyc_k0_oldface : forall (l : list Q) (lam : Q),
  H_lam_cyc l 0%nat lam == lam * H_adj (P0 l) + (1 - lam) * H_adj l.
Proof.
  intros l lam. unfold H_lam_cyc. rewrite rotc_0. reflexivity.
Qed.

(* ========== 【旗舰】差分恒等式 + 双方向单调 ========== *)

(*
   H_lam_cyc l k lam1 - H_lam_cyc l k lam2 = (lam1-lam2)·(h0-hk)。
   直接 exact 实例化（禁重证）。 *)
Theorem H_lam_cyc_diff : forall (l : list Q) (k : nat) (lam1 lam2 : Q),
  H_lam_cyc l k lam1 - H_lam_cyc l k lam2
  == (lam1 - lam2) * (H_adj (P0 l) - H_adj (rotc k l)).
Proof.
  intros l k lam1 lam2. unfold H_lam_cyc.
  exact (lam_affine_diff_sub (H_adj (P0 l)) (H_adj (rotc k l)) lam1 lam2).
Qed.

(* 递增方向：旋转端不高于排序端（hk <= h0）时，λ 增 ⟹ 熵增
   （区间前提显式入陈；斜率非负 × 差非负 ⟹ 差分非负）。 *)
Theorem H_lam_cyc_mono_inc : forall (l : list Q) (k : nat) (lam1 lam2 : Q),
  (H_adj (rotc k l) <= H_adj (P0 l))%Q ->
  (0 <= lam1 <= 1)%Q -> (0 <= lam2 <= 1)%Q ->
  (lam1 <= lam2)%Q ->
  (H_lam_cyc l k lam1 <= H_lam_cyc l k lam2)%Q.
Proof.
  intros l k lam1 lam2 Hle _ _ Hlam.
  assert (Hs : (0 <= (lam2 - lam1) * (H_adj (P0 l) - H_adj (rotc k l)))%Q).
  { apply xq_mul_nonneg.
    - apply (proj1 (Qle_0_sub' lam1 lam2)). exact Hlam.
    - apply (proj1 (Qle_0_sub' (H_adj (rotc k l)) (H_adj (P0 l)))). exact Hle. }
  apply (proj2 (Qle_0_sub' _ _)).
  rewrite (H_lam_cyc_diff l k lam2 lam1). exact Hs.
Qed.

(* 递减方向：排序端不高于旋转端（h0 <= hk）时，λ 增 ⟹ 熵减。
   斜率 (h0-hk) <= 0 与差 (lam1-lam2) <= 0 双非正——U5 件反号装配
   配方：先换位恒等式（change 防御 + ring）再做非负乘法。 *)
Theorem H_lam_cyc_mono_dec : forall (l : list Q) (k : nat) (lam1 lam2 : Q),
  (H_adj (P0 l) <= H_adj (rotc k l))%Q ->
  (0 <= lam1 <= 1)%Q -> (0 <= lam2 <= 1)%Q ->
  (lam1 <= lam2)%Q ->
  (H_lam_cyc l k lam2 <= H_lam_cyc l k lam1)%Q.
Proof.
  intros l k lam1 lam2 Hle _ _ Hlam.
  assert (Hs : (0 <= (lam1 - lam2) * (H_adj (P0 l) - H_adj (rotc k l)))%Q).
  { assert (Hr : (lam1 - lam2) * (H_adj (P0 l) - H_adj (rotc k l))
                 == (lam2 - lam1) * (H_adj (rotc k l) - H_adj (P0 l))).
    { change (lam1 - lam2) with (lam1 + - lam2)%Q.
      change (lam2 - lam1) with (lam2 + - lam1)%Q.
      change (H_adj (P0 l) - H_adj (rotc k l))
        with (H_adj (P0 l) + - H_adj (rotc k l))%Q.
      change (H_adj (rotc k l) - H_adj (P0 l))
        with (H_adj (rotc k l) + - H_adj (P0 l))%Q.
      ring. }
    rewrite Hr. apply xq_mul_nonneg.
    - apply (proj1 (Qle_0_sub' lam1 lam2)). exact Hlam.
    - apply (proj1 (Qle_0_sub' (H_adj (P0 l)) (H_adj (rotc k l)))). exact Hle. }
  apply (proj2 (Qle_0_sub' _ _)).
  rewrite (H_lam_cyc_diff l k lam1 lam2). exact Hs.
Qed.

(* ========== 【主件】与旧件的诚实分离 ========== *)

(* 分离件（s-坍缩面形）：存在 l k lam 使真底座插值 ≠ 旧件 s-坍缩面。
   见证复用 U3 件 H_rotc_separates 的 [0;1;2] 转 1 格：
   H_adj (P0 [0;1;2]) = 2，H_adj (rotc 1 [0;1;2]) = H_adj [1;2;0] = 3，
   lam = 1/2：左 = 1 + 3/2 = 5/2 ≠ 1 + 1 = 2 = 右。vm_compute 数值面。 *)
Theorem H_lam_cyc_oldface_separates : exists (l : list Q) (k : nat) (lam : Q),
  H_lam_cyc l k lam <> lam * H_adj (P0 l) + (1 - lam) * H_adj l.
Proof.
  exists [0; 1; 2], 1%nat, (1#2)%Q.
  intro Hc. unfold H_lam_cyc in Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* 分离件（直比形）：固定 s 后与旧 H_lam 直比——Pinf_eq_l 把旧件第二
   端归到原始序，与 s-坍缩面同面，故同一见证列照收。 *)
Theorem H_lam_cyc_H_lam_separates : exists (l : list Q) (k s : nat) (lam : Q),
  H_lam_cyc l k lam <> H_lam l s lam.
Proof.
  exists [0; 1; 2], 1%nat, 0%nat, (1#2)%Q.
  unfold H_lam. rewrite (Pinf_eq_l [0; 1; 2] 0%nat).
  intro Hc. unfold H_lam_cyc in Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* ========== 【加分】λ-argmin_cyc ========== *)

(*
   否则取 0 落旋转端）——底座纪律：禁重证。 *)
Definition lam_opt_cyc (h0 hk : Q) : Q := lam_opt h0 hk.

Theorem lam_opt_cyc_values : forall h0 hk : Q,
  lam_opt_cyc h0 hk = 1%Q \/ lam_opt_cyc h0 hk = 0%Q.
Proof.
  intros h0 hk. unfold lam_opt_cyc. exact (lam_opt_values h0 hk).
Qed.

Theorem lam_opt_cyc_range : forall h0 hk : Q,
  (0 <= lam_opt_cyc h0 hk <= 1)%Q.
Proof.
  intros h0 hk. unfold lam_opt_cyc. exact (lam_opt_range h0 hk).
Qed.

(* 最优值定理（真底座消费版）：端点选择器的取值不超过 [0,1] 内
   任意 λ 的真底座插值。unfold 后即 lam_opt_min 原形。 *)
Theorem H_lam_cyc_lam_opt_cyc_min : forall (l : list Q) (k : nat) (lam : Q),
  (0 <= lam <= 1)%Q ->
  (H_lam_cyc l k (lam_opt_cyc (H_adj (P0 l)) (H_adj (rotc k l)))
   <= H_lam_cyc l k lam)%Q.
Proof.
  intros l k lam H01. destruct H01 as [Hlam0 Hlam1].
  unfold H_lam_cyc, lam_opt_cyc.
  apply lam_opt_min. split; assumption.
Qed.

(* 端点求值桥：选择器取值恒为某一端的相熵（排序端或真旋转端）。 *)
Theorem H_lam_cyc_lam_opt_cyc_endpoint : forall (l : list Q) (k : nat),
  H_lam_cyc l k (lam_opt_cyc (H_adj (P0 l)) (H_adj (rotc k l))) == H_adj (P0 l)
  \/ H_lam_cyc l k (lam_opt_cyc (H_adj (P0 l)) (H_adj (rotc k l)))
     == H_adj (rotc k l).
Proof.
  intros l k. unfold lam_opt_cyc.
  destruct (lam_opt_values (H_adj (P0 l)) (H_adj (rotc k l))) as [E | E].
  - left. rewrite E. apply H_lam_cyc_lam1.
  - right. rewrite E. apply H_lam_cyc_lam0.
Qed.

(*
   F2' seam 定向形 / F2b 排序坍缩 list 级 / F7 三相判定死支定理化。
   分层：F1 拼接分解（判过时·引 seam 件包装）/ F2 旗舰 Pmid 中相
   熵分解（第三相首块）/ F3 排序上界 / 端点退化） ========== *)

(* F1 保底件：拼接分解恒等式——非空 l1、l2 的相邻差总和在接缝处
   恰好多出 |lastq l1 − hd 0 l2| 一项：
   H_adj (l1 ++ l2) = H_adj l1 + |lastq l1 − hd 0 l2| + H_adj l2。
   【F1 判过时（AUDIT-2 审计在案）】核心件已在本文件 §2 在盘
   （H_adj_app_seam，L215 起，对 u 归纳 + snoc 步主件，其骨架与
   DTPT.v U1 件 cgen_H_adj_snoc 同配方）——本件不重证不改原件，
   仅使用既有件做 3 行规格定向封装（Qabs 方向 xq_abs_sub_comm
   + ring 项序归一），零新数学。 *)
Lemma H_adj_app : forall (l1 l2 : list Q),
  l1 <> [] -> l2 <> [] ->
  H_adj (l1 ++ l2) == H_adj l1 + Qabs (lastq l1 - hd 0 l2) + H_adj l2.
Proof.
  intros l1 l2 H1 H2.
  rewrite (H_adj_app_seam l1 l2 H1 H2).
  rewrite (xq_abs_sub_comm (lastq l1) (hd 0 l2)).
  ring.
Qed.

(* F2'（AUDIT-2 改道件）：中相熵分解恒等式·seam 定向两步形——
   H_adj_app_seam + Pinf_true_id 逐步直组合，接缝项保持 seam 原始
   定向（hd 在前）。卫哨最简形 {k <> 0, k < length l}（P0 l <> []
   与 skipn k l <> [] 经 llm_P0_length / skipn_ne_of_lt 派生）。 *)
Theorem H_adj_Pmid_seam : forall (l : list Q) (s : nat) (k : nat),
  k <> 0%nat -> (k < length l)%nat ->
  H_adj (Pmid l s k)
  == H_adj (firstn k (P0 l)) + H_adj (skipn k l)
     + Qabs (hd 0 (skipn k l) - lastq (firstn k (P0 l))).
Proof.
  intros l s k Hk Hlt.
  unfold Pmid.
  rewrite (Pinf_true_id l s).
  apply H_adj_app_seam.
  - apply (firstn_ne_of_lt k (P0 l)).
    + lia.
    + rewrite (llm_P0_length l). lia.
  - exact (skipn_ne_of_lt k l Hlt).
Qed.

(* F2 旗舰：Pmid 中相熵分解恒等式——Pmid 第三相首个熵定理。
   Pmid l s k = firstn k (P0 l) ++ skipn k l（Pinf l s = l 恒等展开，
   消费本文件 §4 Pinf_true_id；弃用注记件 Pinf_eq_l 未消费），故
   中相 = 排序前缀 × 原始尾的拼接，F1 一步给出接缝分解——框架名义
   三相互补性的第一块拼图（P0 相 = sorted 全体、P∞ 相 = 原始全体、
   中相 = 有序前缀 × 原始尾的接缝分解）。
   卫哨取最简形 {k <> 0, k < length l}：P0 l <> [] 经 llm_P0_length
   （length (P0 l) = length l）与 l <> [] 互推，skipn k l <> [] 经
   skipn_ne_of_lt 由 k < length l 派生，均不再单列。 *)
Theorem H_adj_Pmid_decomp : forall (l : list Q) (s : nat) (k : nat),
  k <> 0%nat -> (k < length l)%nat ->
  H_adj (Pmid l s k)
  == H_adj (firstn k (P0 l))
     + Qabs (lastq (firstn k (P0 l)) - hd 0 (skipn k l))
     + H_adj (skipn k l).
Proof.
  intros l s k Hk Hlt.
  unfold Pmid.
  rewrite (Pinf_true_id l s).
  apply H_adj_app.
  - apply (firstn_ne_of_lt k (P0 l)).
    + lia.
    + rewrite (llm_P0_length l). lia.
  - exact (skipn_ne_of_lt k l Hlt).
Qed.

(* F3 接缝收口工具：排序表内两元之差取绝对值仍不超过 spread
   （= lastq − hd）。Qabs_case 符号二分支 + sorted_sub_le_spread
   正反两次套用。 *)
Lemma sorted_abs_le_spread : forall (l : list Q) (z w : Q),
  SortedQ l -> In z l -> In w l -> (Qabs (z - w) <= lastq l - hd 0 l)%Q.
Proof.
  intros l z w HS Hz Hw.
  apply (Qabs_case (z - w) (fun t => (t <= lastq l - hd 0 l)%Q)).
  - intro Hpos.
    exact (sorted_sub_le_spread l z w HS Hz Hw).
  - intro Hneg.
    assert (Hr2 : (- (z - w) == w - z)%Q) by ring.
    rewrite Hr2.
    exact (sorted_sub_le_spread l w z HS Hw Hz).
Qed.

(* F2b（AUDIT-2 改道件）：排序表上中相整体恒等坍缩——中相零理论
   根因定理化（list 级）：sorted l 时 P0 l = l（xq_sortQ_P0_id）且
   Pinf l s = l（Pinf_true_id），故 Pmid l s k = firstn k l ++ skipn k l
   = l（firstn_skipn 两步）。 *)
Theorem Pmid_sorted_collapse : forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> Pmid l s k = l.
Proof.
  intros l s k HS.
  unfold Pmid.
  rewrite (Pinf_true_id l s).
  rewrite (xq_sortQ_P0_id l HS).
  apply firstn_skipn.
Qed.

(* F3 主件·精确坍缩面：排序表下中相与 P0 相熵逐点相等——
*)
Theorem H_adj_Pmid_sorted_exact : forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> H_adj (Pmid l s k) == H_adj l.
Proof.
  intros l s k HS.
  rewrite (Pmid_sorted_collapse l s k HS).
  reflexivity.
Qed.

(* F3 主件·上界面：排序卫哨下 H_adj (Pmid l s k) <= 2·spread
   （P0 面 spread 口径与规格模板逐字对齐；实由精确坍缩 +
   xq_telescope + rs_le_double 收口——排序情形界可锐化至 1·spread） *)
Theorem H_adj_Pmid_sorted_ub2 : forall (l : list Q) (s : nat) (k : nat),
  SortedQ l ->
  (H_adj (Pmid l s k) <= 2 * (lastq (P0 l) - hd 0 (P0 l)))%Q.
Proof.
  intros l s k HS.
  rewrite (H_adj_Pmid_sorted_exact l s k HS).
  rewrite (xq_sortQ_P0_id l HS).
  rewrite (xq_telescope l HS).
  apply rs_le_double.
  apply (proj1 (Qle_0_sub' (hd 0 l) (lastq l))).
  apply xq_hd_le_lastq. exact HS.
Qed.

(* F3 副件·无排序诚实界：H_adj (Pmid l s k) <= 2·spread(P0)
   + H_adj (skipn k l)。前段经 firstn 保排序（firstn_SortedQ）
   望远镜 <= spread；接缝经 sorted_abs_le_spread <= spread（尾端
   成员 hd 0 (skipn k l) 经 D5_P0_perm 置换搬运入 P0 l）；尾段非
   排序保持原样——无排序时 H_adj (skipn k l) 可超 spread（见证
   l = [0;1;0;1]、k = 1：中相 [0;1;0;1] 熵 3 > 2·spread = 2），
   故尾段不可吞入 2·spread，如实分项。 *)
Theorem H_adj_Pmid_ub_gen : forall (l : list Q) (s : nat) (k : nat),
  k <> 0%nat -> (k < length l)%nat ->
  (H_adj (Pmid l s k)
   <= 2 * (lastq (P0 l) - hd 0 (P0 l)) + H_adj (skipn k l))%Q.
Proof.
  intros l s k Hk Hlt.
  rewrite (H_adj_Pmid_decomp l s k Hk Hlt).
  assert (Hnef : firstn k (P0 l) <> []).
  { apply (firstn_ne_of_lt k (P0 l));
      [ lia | rewrite (llm_P0_length l); lia ]. }
  assert (Hnes : skipn k l <> []) by exact (skipn_ne_of_lt k l Hlt).
  assert (HmemA : In (lastq (firstn k (P0 l))) (P0 l)).
  { apply (firstn_incl (P0 l) k). apply xq_lastq_In. exact Hnef. }
  assert (HmemB : In (hd 0 (skipn k l)) (P0 l)).
  { apply Permutation_in with (l := l).
    - exact (D5_P0_perm l).
    - apply (skipn_incl l k). apply xq_hd_In_gen. exact Hnes. }
  assert (Hpre : (H_adj (firstn k (P0 l))
                  <= lastq (P0 l) - hd 0 (P0 l))%Q).
  { rewrite (xq_telescope (firstn k (P0 l))
              (firstn_SortedQ (P0 l) k (xq_P0_sorted l))).
    exact (sorted_sub_le_spread (P0 l) (lastq (firstn k (P0 l)))
             (hd 0 (firstn k (P0 l))) (xq_P0_sorted l) HmemA
             (firstn_incl (P0 l) k (hd 0 (firstn k (P0 l)))
               (xq_hd_In_gen (firstn k (P0 l)) Hnef))). }
  assert (Hseam : (Qabs (lastq (firstn k (P0 l)) - hd 0 (skipn k l))
                   <= lastq (P0 l) - hd 0 (P0 l))%Q)
    by exact (sorted_abs_le_spread (P0 l) (lastq (firstn k (P0 l)))
                (hd 0 (skipn k l)) (xq_P0_sorted l) HmemA HmemB).
  assert (H2s : (2 * (lastq (P0 l) - hd 0 (P0 l))
                 == (lastq (P0 l) - hd 0 (P0 l))
                    + (lastq (P0 l) - hd 0 (P0 l)))%Q) by ring.
  rewrite H2s.
  apply qadd_le.
  - apply qadd_le; [ exact Hpre | exact Hseam ].
  - apply Qle_refl.
Qed.

(* 加分·端点退化面：k=0 端点＝P∞ 相（原始全体）、k=length 端点＝
   P0 相（排序全体）——消费盘上 DTPT.v §D Pmid 端点定律族
   （llm_Pmid_zero / llm_Pmid_len_endpoint，U2 件，底座纪律不重证）
   与既有端点定理对账。 *)
Theorem H_adj_Pmid_k0 : forall (l : list Q) (s : nat),
  H_adj (Pmid l s 0%nat) == H_adj l.
Proof.
  intros l s.
  rewrite (llm_Pmid_zero l s).
  rewrite (Pinf_true_id l s).
  reflexivity.
Qed.

Theorem H_adj_Pmid_klen : forall (l : list Q) (s : nat),
  H_adj (Pmid l s (length l)) == H_adj (P0 l).
Proof.
  intros l s. rewrite (llm_Pmid_len_endpoint l s). reflexivity.
Qed.

(* 端点对账·sorted：两端点熵皆收敛于 spread（与 §4 H_adj_rotc_exact_0
   的 k=0 取最小 spread 面同调——中相端点即相端点） *)
Theorem H_adj_Pmid_endpoints_sorted : forall (l : list Q) (s : nat),
  SortedQ l ->
  H_adj (Pmid l s 0%nat) == lastq l - hd 0 l
  /\ H_adj (Pmid l s (length l)) == lastq l - hd 0 l.
Proof.
  intros l s HS. split.
  - rewrite H_adj_Pmid_k0. apply xq_telescope. exact HS.
  - rewrite H_adj_Pmid_klen. rewrite (xq_sortQ_P0_id l HS).
    apply xq_telescope. exact HS.
Qed.

(* F7（AUDIT-2 改道件）：三相判定器死支定理化——phase_classify 的
   PhMid 构造子不可达。根因：Pmid l s 0 与 Pinf l s 定义性可转换
   （llm_Pmid_zero / Pinf_true_id），故判定器第二个测试
   Qeq_bool hm hi 恒真，false 支（PhMid 返回点）不可达。
   消费 DTPT.v 的 PhaseTag/phase_classify（经本文件现有
   Require DTPT 可达），证明面纯布尔分派 + Qeq_bool_refl 反证。 *)
Theorem phase_classify_ne_PMid : forall (l : list Q) (s : nat),
  phase_classify l s <> PhMid.
Proof.
  intros l s Hc.
  unfold phase_classify in Hc. cbv zeta in Hc.
  destruct (Qeq_bool (H_adj (Pmid l s 0%nat)) (H_adj (Pinf l s))) eqn:E.
  - destruct (Qeq_bool (H_adj (P0 l)) (H_adj (Pmid l s 0%nat)));
      simpl in Hc; discriminate Hc.
  - assert (Hid : H_adj (Pmid l s 0%nat) == H_adj (Pinf l s))
      by reflexivity.
    rewrite Hid in E.
    rewrite Qeq_bool_refl in E.
    discriminate E.
Qed.

(* 数值实测锚（G4 实测面）：F2b 坍缩与 F2 分解恒等式在见证列
   [0;1;2]（sorted）上 vm_compute 一步闭项判定——新件的计算面
   可执行实测，见证中相 [0] ++ [1;2] 接缝 = 全表本身。 *)
Theorem Pmid_sorted_collapse_wit_012 :
  Pmid [0; 1; 2] 0%nat 1%nat = [0; 1; 2].
Proof. vm_compute. reflexivity. Qed.

Theorem H_adj_Pmid_decomp_wit_012 :
  H_adj (Pmid [0; 1; 2] 0%nat 1%nat)
  == H_adj [0] + Qabs (lastq [0] - hd 0 [1; 2]) + H_adj [1; 2].
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   §S9 H_lam_pmid —— 三相互补熵理论最后一块（FRUIT-3 件追加）：
   P0↔Pmid 真 λ-插值。H_lam（DTPT_Entropy.v，第二端 Pinf≡l）与
   H_lam_cyc（§S7 并入段，第二端 rotc k l）之后 λ-插值族的第三块
   载体：第二端取真中相 Pmid l s k = firstn k (P0 l) ++ skipn k l
   （§S8 F2 分解面）——「λ 从排序相滑向真中相」，中相端的熵不再
   是无结构的原始尾，而是有序前缀×接缝×原始尾的三分量分解。
   分层：保底（定义 + 端点双件）/ 旗舰（仿射差分恒等式，消费
   §S7 lam_affine_diff_sub 泛形，禁重证）/ 主件（排序坍缩一致面，
   消费 §S8 Pmid_sorted_collapse + H_adj_Pmid_sorted_exact）/
   加分（k=0 旧件重合桥 + k=length 常值面 + 与 H_lam 分离见证
   + 数值锚）。
   ============================================================ *)

(* ========== 【保底】定义 + 端点 ========== *)

(* 三相互补熵载体：H_lam_pmid l s k lam = lam·H_adj (P0 l)
   + (1-lam)·H_adj (Pmid l s k)。与 H_lam / H_lam_cyc 并立为
   三相互补熵的第三块 λ-插值。nat 字面量全显式 %nat（§S7 Open
   Scope Q_scope 传导，FRUIT-1 坑①）。 *)
Definition H_lam_pmid (l : list Q) (s : nat) (k : nat) (lam : Q) : Q :=
  lam * H_adj (P0 l) + (1 - lam) * H_adj (Pmid l s k).

(* 端点 λ=1：只余排序相 P0（s、k 解耦——排序端与中相参数无关）。 *)
Theorem H_lam_pmid_lam1 : forall (l : list Q) (s : nat) (k : nat),
  H_lam_pmid l s k 1 == H_adj (P0 l).
Proof.
  intros l s k. unfold H_lam_pmid.
  replace (1 - 1)%Q with 0%Q by reflexivity.
  ring.
Qed.

(* 端点 λ=0：只余真中相 Pmid。 *)
Theorem H_lam_pmid_lam0 : forall (l : list Q) (s : nat) (k : nat),
  H_lam_pmid l s k 0 == H_adj (Pmid l s k).
Proof.
  intros l s k. unfold H_lam_pmid.
  replace (1 - 0)%Q with 1%Q by reflexivity.
  ring.
Qed.

(* ========== 【旗舰】仿射差分恒等式 ========== *)

(* 差分恒等式：§S7 泛形 lam_affine_diff_sub 的真中相实形——
   H_lam_pmid l s k lam1 - H_lam_pmid l s k lam2
   = (lam1-lam2)·(H_adj (P0 l) - H_adj (Pmid l s k))。
   exact 实例化一步（底座纪律：禁重证，H_lam_cyc_diff 同款）。 *)
Theorem H_lam_pmid_diff : forall (l : list Q) (s : nat) (k : nat) (lam1 lam2 : Q),
  H_lam_pmid l s k lam1 - H_lam_pmid l s k lam2
  == (lam1 - lam2) * (H_adj (P0 l) - H_adj (Pmid l s k)).
Proof.
  intros l s k lam1 lam2. unfold H_lam_pmid.
  exact (lam_affine_diff_sub (H_adj (P0 l)) (H_adj (Pmid l s k)) lam1 lam2).
Qed.

(* 仿射标准形：H_lam_pmid l s k lam = hmid + lam·(h0 - hmid)
   （H_lam_affine 同款模板：change 防御式收口 + ring）。 *)
Theorem H_lam_pmid_affine : forall (l : list Q) (s : nat) (k : nat) (lam : Q),
  H_lam_pmid l s k lam
  == H_adj (Pmid l s k) + lam * (H_adj (P0 l) - H_adj (Pmid l s k)).
Proof.
  intros l s k lam. unfold H_lam_pmid.
  change (1 - lam) with (1 + - lam)%Q.
  change (H_adj (P0 l) - H_adj (Pmid l s k))
    with (H_adj (P0 l) + - H_adj (Pmid l s k))%Q.
  ring.
Qed.

(* ========== 【主件】排序坍缩一致面 ========== *)

(* 一致性定理：sorted l 时 Pmid l s k = l（§S8 Pmid_sorted_collapse）
   且 Pinf l s = l（§4 Pinf_true_id），故三相互补熵在已排序输入上
   与经典 H_lam 逐点重合（全 λ 面）——「对已排序输入，三相互补熵
   与经典序列熵重合」的理论相容性面。 *)
Theorem H_lam_pmid_sorted_consistency : forall (l : list Q) (s : nat) (k : nat) (lam : Q),
  SortedQ l -> H_lam_pmid l s k lam == H_lam l s lam.
Proof.
  intros l s k lam HS. unfold H_lam_pmid, H_lam.
  rewrite (Pmid_sorted_collapse l s k HS).
  rewrite (Pinf_true_id l s).
  reflexivity.
Qed.

(*
   两步收口。 *)
Theorem H_lam_pmid_sorted_lam1 : forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> H_lam_pmid l s k 1 == H_adj l.
Proof.
  intros l s k HS.
  rewrite (H_lam_pmid_lam1 l s k).
  rewrite (xq_sortQ_P0_id l HS).
  reflexivity.
Qed.

(* λ=0 端 sorted 精确面：直接消费 §S8 H_adj_Pmid_sorted_exact
   （L2068），中相端熵零新证。 *)
Theorem H_lam_pmid_sorted_lam0 : forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> H_lam_pmid l s k 0 == H_adj l.
Proof.
  intros l s k HS.
  rewrite (H_lam_pmid_lam0 l s k).
  exact (H_adj_Pmid_sorted_exact l s k HS).
Qed.

(* ========== 【加分】端点旧件桥 + 分离面 + 数值锚 ========== *)

(* 旧件重合桥（k=0 端点）：中相 k=0 退化为 P∞ 相（llm_Pmid_zero），
   与 H_lam 的第二端（Pinf l s）重合——k=0 时三相互补熵与旧件
   逐点相等（迁移零丢旧信息，H_lam_cyc_k0_oldface 同款对账面）。 *)
Theorem H_lam_pmid_k0_oldface : forall (l : list Q) (s : nat) (lam : Q),
  H_lam_pmid l s 0%nat lam == H_lam l s lam.
Proof.
  intros l s lam. unfold H_lam_pmid, H_lam.
  rewrite (llm_Pmid_zero l s).
  reflexivity.
Qed.

(* k=length 端点：中相退化为 P0 相（llm_Pmid_len_endpoint），整条
   插值坍缩为常值 H_adj (P0 l)（两端重合，λ 失效面）。 *)
Theorem H_lam_pmid_klen_const : forall (l : list Q) (s : nat) (lam : Q),
  H_lam_pmid l s (length l) lam == H_adj (P0 l).
Proof.
  intros l s lam. unfold H_lam_pmid.
  rewrite (llm_Pmid_len_endpoint l s).
  ring.
Qed.

(* 分离见证（与 H_lam）：未排序 l 上真中相端 ≠ 原始尾端——
   见证列 [2;0;1]（未排序），k=1，s=0，lam=1/2：Pmid = [0]++[0;1]
   = [0;0;1]，H_adj (Pmid) = 1 ≠ 3 = H_adj l（Pinf≡l 原始尾端），
   左 = (1/2)·2 + (1/2)·1 = 3/2 ≠ 5/2 = (1/2)·2 + (1/2)·3 = 右。
   vm_compute 数值面（H_lam_cyc_H_lam_separates 同款配方；Pinf
   恒等坍缩经本文件 §4 Pinf_true_id，弃用注记件 Pinf_eq_l 绕行）。 *)
Theorem H_lam_pmid_H_lam_separates : exists (l : list Q) (k s : nat) (lam : Q),
  H_lam_pmid l s k lam <> H_lam l s lam.
Proof.
  exists [2; 0; 1], 1%nat, 0%nat, (1#2)%Q.
  intro Hc. unfold H_lam_pmid, H_lam in Hc.
  rewrite (Pinf_true_id [2; 0; 1] 0%nat) in Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

(* 数值实测锚（G4 实测面）：见证列 [2;0;1] 上插值值与两端熵
   vm_compute 一步闭项判定——新件的计算面可执行实测。 *)
Theorem H_lam_pmid_wit_201 :
  H_lam_pmid [2; 0; 1] 0%nat 1%nat (1#2)%Q == (3#2)%Q.
Proof. vm_compute. reflexivity. Qed.

Theorem H_lam_pmid_wit_201_ends :
  H_adj (P0 [2; 0; 1]) == 2%Q /\ H_adj (Pmid [2; 0; 1] 0%nat 1%nat) == 1%Q.
Proof.
  split.
  - change (H_adj (insert_q 2 (insert_q 0 (insert_q 1 []))) == 2%Q).
    change (H_adj [0; 1; 2] == 2%Q).
    change (Qabs (1 - 0) + (Qabs (2 - 1) + 0) == 2%Q)%Q.
    reflexivity.
  - change (H_adj (firstn 1%nat (P0 [2; 0; 1])
              ++ skipn 1%nat (Pinf [2; 0; 1] 0%nat)) == 1%Q).
    change (H_adj (firstn 1%nat (insert_q 2 (insert_q 0 (insert_q 1 [])))
              ++ skipn 1%nat (firstn 1%nat [2; 0; 1]
                  ++ skipn 1%nat [2; 0; 1])) == 1%Q).
    change (H_adj ([0] ++ skipn 1%nat ([2] ++ [0; 1])) == 1%Q).
    change (H_adj [0; 0; 1] == 1%Q).
    change (Qabs (0 - 0) + (Qabs (1 - 0) + 0) == 1%Q)%Q.
    reflexivity.
Qed.

(* ============================================================
   §S10 恒等簇处置（CLN-1 件追加；AUDIT-2 A6 条目闭合）：
   「llm_rot_id 恒等簇 + 8 件弃用注记件仍以现役名被引用」的
   处置收口——把「弃用注记」升级为「机器检查的逐件映射」。
   纪律：纯追加；既有行零改动；全部旧面性质绕行弃用名重推
   （Pinf_eq_l 弃用件不经手，一律改经 §4 Pinf_true_id）。
   分层：保底（处置面定理 + 恒等簇真化覆盖面四件）/ 主件
   （deprecated_consumers_map 八件逐件映射 + helper 一件）/
   加分（消费面重定向示范双件）。
   ============================================================ *)

(* ========== 【保底】处置面定理 + 恒等簇真化覆盖面 ========== *)

(*
   rot = firstn ++ skipn 恒等重构之恒等面在真化底座（§1 rotc 系
   在册）下的处置定谳——firstn_skipn 一步直证，不消费弃用件
   llm_rot_id（DTPT.v:1781）。此件即「恒等簇处置」的机器检查
   定谳面：旧 rot 名下的恒等重写消费全部由本件承接。 *)
Theorem rotc_supersedes_rot_id : forall (n : nat) (l : list Q),
  rot n l = l.
Proof.
  intros n l. unfold rot. revert n.
  induction l as [| a rest IH]; intros n.
  - destruct n as [| n']; reflexivity.
  - destruct n as [| n'].
    + reflexivity.
    + change (firstn (S n') (a :: rest) ++ skipn (S n') (a :: rest) = a :: rest)
        with (a :: (firstn n' rest ++ skipn n' rest) = a :: rest).
      rewrite IH. reflexivity.
Qed.

(* 真化覆盖面①·恒等重写消费（llm_rot_id/llm_rot_full/前提零消费的
   llm_rot_cyclic_inv 的消费型）：凡对 rot n l 陈述的性质 P 皆与对
   l 陈述零损失互迁（P 面透明）——恒等簇恒等重写消费场景的全部
   替代面。逐字陈述弃用件所述析取形（<> \/ ==）为可判定性平凡面、
   零内容，禁硬凑；本形为盘面可证的实质覆盖面。 *)
Theorem llm_rot_id_superseded :
  forall (n : nat) (l : list Q) (P : list Q -> Prop), P l <-> P (rot n l).
Proof.
  intros n l P. split.
  - intro H. rewrite (rotc_supersedes_rot_id n l). exact H.
  - intro H. rewrite (rotc_supersedes_rot_id n l) in H. exact H.
Qed.

(* 真化覆盖面②·置换/长度消费（llm_rot_cyclic_perm/llm_rot_cyclic_
   length 的消费型）：旧面成立（恒等底座下平凡）且真化替代件
   同形在册（§2 rotc_perm/rotc_length）——双覆盖。 *)
Theorem rot_cyclic_cluster_superseded : forall (n : nat) (l : list Q),
  Permutation l (rot n l) /\ length (rot n l) = length l
  /\ Permutation l (rotc n l) /\ length (rotc n l) = length l.
Proof.
  intros n l. rewrite (rotc_supersedes_rot_id n l). split.
  - apply Permutation_refl.
  - split.
    + reflexivity.
    + split.
      * apply rotc_perm.
      * apply rotc_length.
Qed.

(* 真化覆盖面③·熵面消费（Hsup 族/H_lam 系踩恒等底座的消费型）：
   旧熵面逐点重合（H_adj (rot n l) == H_adj l）+ 真化层退化端点
   rotc 0 同值（§S6 rotc_0_H_adj）——恒等消费在真化层的退化端点
   有同值锚；非退化端点 H_adj (rotc k l) <> H_adj l 的分离面由
   §4 H_rotc_separates 在册承接（[0;1;2] 转 1 格 2 ≠ 3）。 *)
Theorem rot_H_adj_face_covered : forall (n : nat) (l : list Q),
  H_adj (rot n l) == H_adj l /\ H_adj (rotc 0%nat l) == H_adj l.
Proof.
  intros n l. split.
  - rewrite (rotc_supersedes_rot_id n l). apply Qeq_refl.
  - apply rotc_0_H_adj.
Qed.

(* ========== 【主件】deprecated_consumers_map：八件弃用注记件
   逐件映射定理（旧名消费性质 P 与真化替代件 g args 同成立的
   传递定理；旧面一律绕行弃用名重推） ========== *)

(* helper：旧 Hsup 面恒常值 = H_adj l（恒等底座 Pinf≡l 的直接
   后果；X1 判词「Hsup l n ≡ H_adj l」的定理化）。弃用件
   Hsup_mono/Hsup_bounded 的旧面重推公共底座。归纳步经
   Hsup_S_eq（DTPT.v 在册）+ Pinf_true_id 两步，布尔分支
   两向同值。 *)
Lemma Hsup_oldface_const : forall (l : list Q) (n : nat),
  Hsup l n = H_adj l.
Proof.
  intros l n. induction n as [| n IH].
  - cbn [Hsup]. rewrite (Pinf_true_id l 0%nat). reflexivity.
  - rewrite (Hsup_S_eq l n). rewrite IH.
    rewrite (Pinf_true_id l (S n)).
    destruct (Qle_bool (H_adj l) (H_adj l)); reflexivity.
Qed.

(* 映射①：D5_Pinf_perm（DTPT.v，Pinf l s ~ l 恒等置换面）→
   真化替代 Pinf_c_perm/rotc_perm。旧面经 Pinf_true_id 承接；
   真化面为真无限相 Pinf_c 的非平凡置换。 *)
Theorem deprecated_consumers_map_D5_Pinf_perm :
  forall (l : list Q) (s : nat),
  Permutation l (Pinf l s) /\ Permutation l (Pinf_c l s).
Proof.
  intros l s. split.
  - rewrite (Pinf_true_id l s). apply Permutation_refl.
  - apply Pinf_c_perm.
Qed.

(* 映射②：llm_Pmid_zero（DTPT.v，Pmid l s 0 = Pinf l s 端点恒等面）
   → 真化替代 §S8 H_adj_Pmid_k0 同值的「k=0 端点 = 原始全体 l」
   内容面：Pmid l s 0 定义性坍缩到 Pinf l s（reflexivity 可验），
   Pinf 面经 §4 Pinf_true_id 收口为 l——端点消费的内容与熵两面
   皆由真化锚承接（弃用件 llm_Pmid_zero 不经手）。 *)
Theorem deprecated_consumers_map_llm_Pmid_zero :
  forall (l : list Q) (s : nat),
  Pmid l s 0%nat = l /\ H_adj (Pmid l s 0%nat) == H_adj l.
Proof.
  intros l s.
  assert (H0 : Pmid l s 0%nat = l).
  { replace (Pmid l s 0%nat) with (Pinf l s) by reflexivity.
    apply Pinf_true_id. }
  split.
  - exact H0.
  - rewrite H0. apply Qeq_refl.
Qed.

(* 映射③：P0_absorbs_Pmid（DTPT.v，P0 (Pmid l s 0) = P0 l 仅 k=0
   端点吸收面）→ 真化替代 §S8 Pmid_sorted_collapse：排序卫哨下
   对全部 k 的吸收 P0 (Pmid l s k) = P0 l——弃用件的平凡恒等推论
   在真化层升格为有序化不变量（卫哨 sorted 是真中相非平凡性的
   诚实代价，§S8 F2b 判词在案）。 *)
Theorem deprecated_consumers_map_P0_absorbs_Pmid :
  forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> P0 (Pmid l s k) = P0 l.
Proof.
  intros l s k HS.
  rewrite (Pmid_sorted_collapse l s k HS). reflexivity.
Qed.

(* 映射④：Hsup_mono（DTPT.v 前缀最大值单调，恒等底座下伪装）→
   真化替代 §6 Hsup_cyc_mono（真动态上确界单调）。旧面经 helper
   Hsup_oldface_const 承接（两端同值，Qle_refl），真化面为非平凡
   单调——「旧面成立且真化替代同形在册」的双覆盖。 *)
Theorem deprecated_consumers_map_Hsup_mono : forall (l : list Q) (n : nat),
  (Hsup l n <= Hsup l (S n))%Q /\ (Hsup_cyc l n <= Hsup_cyc l (S n))%Q.
Proof.
  intros l n. split.
  - rewrite (Hsup_oldface_const l n). rewrite (Hsup_oldface_const l (S n)).
    apply Qle_refl.
  - apply Hsup_cyc_mono.
Qed.

(* 映射⑤：Hsup_bounded（DTPT.v 有穷上界，恒等底座下伪装）→
   真化替代 §6 Hsup_cyc_ub（SortedQ + 非空卫哨下的 3·spread 界）。
   旧面经 helper + H_adj_bound（DTPT.v:2666 在册，弃用件证明体
   所消费的同一底座）绕行旧名重推；真化面带诚实卫哨在册。 *)
Theorem deprecated_consumers_map_Hsup_bounded :
  forall (l : list Q) (n : nat) (B : Q),
  (forall x : Q, In x l -> Qabs x <= B) -> SortedQ l -> l <> [] ->
  (Hsup l n <= (Z.of_nat (length l) # 1)%Q * B * 2)%Q
  /\ (Hsup_cyc l n <= 3 * (lastq l - hd 0 l))%Q.
Proof.
  intros l n B HB HS Hne. split.
  - rewrite (Hsup_oldface_const l n). apply H_adj_bound. exact HB.
  - apply Hsup_cyc_ub; assumption.
Qed.

(* 映射⑥：Pinf_eq_l（DTPT_Entropy.v:444 弃用件，Pinf l s = l）→
   真化替代 §4 Pinf_true_id 同语句现役件（本桩曾两度绕行消费之，
   注记在案）+ Pinf_c 定义面 + 真无限相置换面——旧名陈述由现役
   同形件零损失承接，真无限相内容由 rotc 系承接。 *)
Theorem deprecated_consumers_map_Pinf_eq_l :
  forall (l : list Q) (s : nat),
  Pinf l s = l /\ Pinf_c l s = rotc (S s) l /\ Permutation l (Pinf_c l s).
Proof.
  intros l s. split.
  - apply Pinf_true_id.
  - split.
    + reflexivity.
    + apply Pinf_c_perm.
Qed.

(* 映射⑦：H_adj_cross_phase_lb（DTPT_Entropy.v:462 弃用件，跨相
   下界 H_adj (P0 l) <= H_adj (Pinf l s)）→ 真化替代 phcyc_min_perm
   + rotc_perm（P0 是排列类上 H_adj 最小值 ⇒ 对一切真旋转 k 成立）。
   旧面经 Pinf_true_id + H_adj_P0_min（Entropy:428 现役）重推；
   真化面覆盖任意 k（含 Pinf_c = rotc (S s)）。本件同时是 §S7
   两处消费点（H_lam_anti_mono L1634 / lam_opt_cross_phase L1753）
   的重定向底座——第 3 层示范即以本件路线替置直引。 *)
Theorem deprecated_consumers_map_H_adj_cross_phase_lb :
  forall (l : list Q) (s : nat) (k : nat),
  (H_adj (P0 l) <= H_adj (Pinf l s))%Q
  /\ (H_adj (P0 l) <= H_adj (rotc k l))%Q
  /\ (H_adj (P0 l) <= H_adj (Pinf_c l s))%Q.
Proof.
  intros l s k. split.
  - rewrite (Pinf_true_id l s). apply H_adj_P0_min.
  - split.
    + apply phcyc_min_perm. apply rotc_perm.
    + apply (phcyc_min_perm l (Pinf_c l s)). apply Pinf_c_perm.
Qed.

(* 映射⑧：u12_phase_side_always_zero（DTPT_Extract.v:177 弃用件，
   旧 phase_side 判别器恒返 0）→ 真化替代 §S6 phase_side_cyc_
   side_degenerate/zero（rotc 口径判别面同样无分辨力，但系对真
   底座定理化——判别器退化的根因不是恒等底座而是 Qle 口径，见
   §S6 注）。旧面经 phase_side 定义展开 + Pinf_true_id +
   xq_Qle_bool_true + H_adj_P0_min 绕行弃用名重推；真化面在册
   直接消费（k := s）。 *)
Theorem deprecated_consumers_map_u12_phase_side_always_zero :
  forall (l : list Q) (s : nat),
  phase_side l s = 0%nat
  /\ (if Qle_bool (H_adj (P0 l)) (H_adj (rotc s l)) then 0 else 1)%nat
     = 0%nat.
Proof.
  intros l s. split.
  - unfold phase_side. rewrite (Pinf_true_id l s).
    rewrite (xq_Qle_bool_true _ _ (H_adj_P0_min l)). reflexivity.
  - apply phase_side_cyc_side_zero.
Qed.

(* ========== 【加分】消费面重定向示范（同陈述新证法变体；
   既有行零改动） ========== *)

(* 示范①：§S7 旗舰 H_lam_anti_mono（L1615）的重定向变体——原证
   在斜率非正装配处直引弃用件 H_adj_cross_phase_lb（L1634）；
   本变体同陈述同骨架，唯一改点为该步换经 Pinf_true_id +
   H_adj_P0_min 真化锚（弃用名零出现）。 *)
Theorem H_lam_anti_mono_real : forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  (lam1 <= lam2)%Q -> (H_lam l s lam2 <= H_lam l s lam1)%Q.
Proof.
  intros l s lam1 lam2 Hlam.
  assert (Hs : (0 <= (lam1 - lam2) * (H_adj (P0 l) - H_adj (Pinf l s)))%Q).
  { assert (Hr : (lam1 - lam2) * (H_adj (P0 l) - H_adj (Pinf l s))
                 == (lam2 - lam1) * (H_adj (Pinf l s) - H_adj (P0 l))).
    { change (lam1 - lam2) with (lam1 + - lam2)%Q.
      change (lam2 - lam1) with (lam2 + - lam1)%Q.
      change (H_adj (P0 l) - H_adj (Pinf l s))
        with (H_adj (P0 l) + - H_adj (Pinf l s))%Q.
      change (H_adj (Pinf l s) - H_adj (P0 l))
        with (H_adj (Pinf l s) + - H_adj (P0 l))%Q.
      ring. }
    rewrite Hr. apply xq_mul_nonneg.
    - apply (proj1 (Qle_0_sub' lam1 lam2)). exact Hlam.
    - apply (proj1 (Qle_0_sub' (H_adj (P0 l)) (H_adj (Pinf l s)))).
      rewrite (Pinf_true_id l s). apply H_adj_P0_min. }
  apply (proj2 (Qle_0_sub' _ _)).
  rewrite (H_lam_diff_sub l s lam1 lam2). exact Hs.
Qed.

(* 示范②：§S7 诚实锚 lam_opt_cross_phase（L1749）的重定向变体——
   原证 rewrite 处直引弃用件 H_adj_cross_phase_lb（L1753）；本
   变体同陈述，跨相下界改经真化锚两步装配。 *)
Theorem lam_opt_cross_phase_real : forall (l : list Q) (s : nat),
  lam_opt (H_adj (P0 l)) (H_adj (Pinf l s)) = 1%Q.
Proof.
  intros l s. unfold lam_opt.
  assert (Hlb : (H_adj (P0 l) <= H_adj (Pinf l s))%Q).
  { rewrite (Pinf_true_id l s). apply H_adj_P0_min. }
  rewrite (xq_Qle_bool_true _ _ Hlb). reflexivity.
Qed.

(* ============================================================
   §S11 三相互补统一族（FRUIT-6 件追加；深水区第二件·α 论文 §5
   完成定理位）：H_lam / H_lam_cyc / H_lam_pmid 三族 λ-插值的
   单一仿射族定理——三相插值不是三个独立理论，而是一个第二端
   参数化仿射族 H_lam_gen 的三个实例。
   分层：保底（Definition H_lam_gen + 统一仿射差分
   H_lam_gen_diff + 标准形，消费 §S7 lam_affine_diff_sub 泛形，
   禁重证——三族差分件收编为单一实例点）/ 旗舰（三特化对账：
   恒等端消费 §4 Pinf_true_id 真化锚、旋转/中相端定义展开
   恒等，三族逐件 = 统一族三实例）/ 主件（统一最优性
   H_lam_gen_opt：§S7 lam_opt_min 泛形的族级版，对齐选择器
   lam_opt 全族一致最优；双文件选择器同值面
   lam_opt_align_lambda_opt_eq，消费 DTPT_Entropy §A7
   align_lambda_opt）/ 加分（端点三元对账：rotc 0 恒等端、
   Pmid k=0 原始全体端、k=length P0 相常值端）+ 数值锚双件
   （与 §S9 分离见证 [2;0;1] 同列）。
   ============================================================ *)

(* ========== 【保底】统一族定义 + 仿射差分 ========== *)

(* 统一仿射族载体：H_lam_gen l l2 lam = lam·H_adj (P0 l)
   + (1-lam)·H_adj l2。第一端恒取排序相 P0，第二端 l2 参数化
   （l2 := l → H_lam 的 Pinf≡l 面；l2 := rotc k l → H_lam_cyc；
   l2 := Pmid l s k → H_lam_pmid）。nat 字面量全显式 %nat
   （§S7 Open Scope Q_scope 传导，FRUIT-1 坑①）。 *)
Definition H_lam_gen (l l2 : list Q) (lam : Q) : Q :=
  lam * H_adj (P0 l) + (1 - lam) * H_adj l2.

(*
   exact 实例化 §S7 泛形 lam_affine_diff_sub 一步（底座纪律：
   禁重证，H_lam_diff_sub / H_lam_cyc_diff / H_lam_pmid_diff
   同款配方）。 *)
Theorem H_lam_gen_diff :
  forall (l2 : list Q) (l : list Q) (s : nat) (lam1 lam2 : Q),
  H_lam_gen l l2 lam1 - H_lam_gen l l2 lam2
  == (lam1 - lam2) * (H_adj (P0 l) - H_adj l2).
Proof.
  intros l2 l s lam1 lam2. unfold H_lam_gen.
  exact (lam_affine_diff_sub (H_adj (P0 l)) (H_adj l2) lam1 lam2).
Qed.

(* 统一族仿射标准形：H_lam_gen l l2 lam = H_adj l2
   + lam·(H_adj (P0 l) - H_adj l2)（H_lam_affine 三族同款，
   防御式 change 后 ring）。 *)
Theorem H_lam_gen_affine :
  forall (l2 : list Q) (l : list Q) (s : nat) (lam : Q),
  H_lam_gen l l2 lam == H_adj l2 + lam * (H_adj (P0 l) - H_adj l2).
Proof.
  intros l2 l s lam. unfold H_lam_gen.
  change (1 - lam) with (1 + - lam)%Q.
  change (H_adj (P0 l) - H_adj l2) with (H_adj (P0 l) + - H_adj l2)%Q.
  ring.
Qed.

(* ========== 【旗舰】三特化对账（三族 = 统一族三实例） ========== *)

(* 特化①（恒等端）：l2 := l 时统一族与 H_lam 全 λ 逐点重合
   （k=0/恒等端特化——Pinf=id 的诚实面）。消费 §4
   Pinf_true_id 真化锚，弃用注记件 Pinf_eq_l 零出现（§S10
   同纪律）。 *)
Theorem H_lam_gen_H_lam : forall (l : list Q) (s : nat) (lam : Q),
  H_lam_gen l l lam == H_lam l s lam.
Proof.
  intros l s lam. unfold H_lam_gen, H_lam.
  rewrite (Pinf_true_id l s). reflexivity.
Qed.

(* 特化②（旋转端）：l2 := rotc k l 时与 §S7 H_lam_cyc 定义面
   逐点重合（定义展开恒等，§S7 现役件消费对账）。 *)
Theorem H_lam_gen_H_lam_cyc : forall (l : list Q) (k : nat) (lam : Q),
  H_lam_gen l (rotc k l) lam == H_lam_cyc l k lam.
Proof.
  intros l k lam. unfold H_lam_gen, H_lam_cyc. reflexivity.
Qed.

(* 特化③（中相端）：l2 := Pmid l s k 时与 §S9 H_lam_pmid 定义
   面逐点重合（定义展开恒等，§S9 现役件消费对账）。 *)
Theorem H_lam_gen_H_lam_pmid :
  forall (l : list Q) (s : nat) (k : nat) (lam : Q),
  H_lam_gen l (Pmid l s k) lam == H_lam_pmid l s k lam.
Proof.
  intros l s k lam. unfold H_lam_gen, H_lam_pmid. reflexivity.
Qed.

(* ========== 【主件】统一最优性（族级 λ-argmin） ========== *)

(* 端点选择器在全族上一致最优：λ* := lam_opt (H_adj (P0 l))
   (H_adj l2) 实现 H_lam_gen 在 [0,1] 上任意 λ 处的最小值
   （对齐选择器最优性的族级版；规格 align_opt 实测现役名
   = §S7 lam_opt）。§S7 lam_opt_min 泛形一步 unfold + apply。 *)
Theorem H_lam_gen_opt : forall (l l2 : list Q) (lam : Q),
  (0 <= lam <= 1)%Q ->
  (H_lam_gen l l2 (lam_opt (H_adj (P0 l)) (H_adj l2))
   <= H_lam_gen l l2 lam)%Q.
Proof.
  intros l l2 lam H01. unfold H_lam_gen. apply lam_opt_min. exact H01.
Qed.

(* 族级最优值只落双端：argmin 取端点值之一（H_lam_lam_opt_
   endpoint 的统一族面）。 *)
Theorem H_lam_gen_opt_endpoint : forall (l l2 : list Q),
  H_lam_gen l l2 (lam_opt (H_adj (P0 l)) (H_adj l2)) == H_adj (P0 l)
  \/ H_lam_gen l l2 (lam_opt (H_adj (P0 l)) (H_adj l2)) == H_adj l2.
Proof.
  intros l l2. unfold H_lam_gen.
  destruct (lam_opt_values (H_adj (P0 l)) (H_adj l2)) as [E | E].
  - left. rewrite E. replace (1 - 1)%Q with 0%Q by reflexivity. ring.
  - right. rewrite E. replace (1 - 0)%Q with 1%Q by reflexivity. ring.
Qed.

(* 双文件选择器同值面：§S7 lam_opt（本文件）与 DTPT_Entropy
   §A7 align_lambda_opt 定义同形（Qle_bool 二分端点选择器）——
   统一族的最优选择器在两文件口径下逐点同值（Qeq 面）。 *)
Theorem lam_opt_align_lambda_opt_eq : forall (h0 h1 : Q),
  lam_opt h0 h1 == align_lambda_opt h0 h1.
Proof.
  intros h0 h1. unfold lam_opt, align_lambda_opt. reflexivity.
Qed.

(* ========== 【加分】端点三元对账 ========== *)

(* 端点①（rotc 恒等端）：k=0 旋转端与恒等端在统一族中同值
   （消费 §S5 rotc_0）。 *)
Theorem H_lam_gen_end_rotc0 : forall (l : list Q) (lam : Q),
  H_lam_gen l (rotc 0%nat l) lam == H_lam_gen l l lam.
Proof.
  intros l lam. rewrite (rotc_0 l). reflexivity.
Qed.

(* 端点②（Pmid k=0 端）：中相 k=0 = 原始全体（P∞≡l 相），与
   恒等端同值（消费 §S8 H_adj_Pmid_k0——底座链 llm_Pmid_zero
   已由 §S8 桥内化，本件零直引）。 *)
Theorem H_lam_gen_end_pmid0 : forall (l : list Q) (s : nat) (lam : Q),
  H_lam_gen l (Pmid l s 0%nat) lam == H_lam_gen l l lam.
Proof.
  intros l s lam. unfold H_lam_gen.
  rewrite (H_adj_Pmid_k0 l s). reflexivity.
Qed.

(* 端点③（Pmid k=length 常值端）：k=length 两端重合 P0 相，
   λ 失效、统一族常值 = H_adj (P0 l)（消费 §S8 H_adj_Pmid_klen；
   H_lam_pmid_klen_const 的统一族面）。 *)
Theorem H_lam_gen_klen_const : forall (l : list Q) (s : nat) (lam : Q),
  H_lam_gen l (Pmid l s (length l)) lam == H_adj (P0 l).
Proof.
  intros l s lam. unfold H_lam_gen.
  rewrite (H_adj_Pmid_klen l s). ring.
Qed.

(* ========== 【加分】数值锚双件（与 §S9 分离见证 [2;0;1]
   同列同 λ） ========== *)

(* 同一 λ=1/2 下恒等端值 5/2 ≠ 中相端值 3/2——第二端参数化
   实质生效的族级数值面（两锚与 §S9 H_lam_pmid_wit_201 /
   分离见证逐值对账）。 *)
Theorem H_lam_gen_wit_201_id :
  H_lam_gen [2;0;1] [2;0;1] (1#2)%Q == (5#2)%Q.
Proof. vm_compute. reflexivity. Qed.

Theorem H_lam_gen_wit_201_pmid :
  H_lam_gen [2;0;1] (Pmid [2;0;1] 0%nat 1%nat) (1#2)%Q == (3#2)%Q.
Proof. vm_compute. reflexivity. Qed.

End DTPT_Rotation.
Import DTPT_Rotation.

(* ========== §6 公理面审计（G4） ========== *)

Print Assumptions rotc_add_local.
Print Assumptions rotc_freeze_local.
Print Assumptions rotc_periodic_naive_false.
Print Assumptions rotc_add_naive_false.
Print Assumptions Hsup_cyc_mono_from.
Print Assumptions Hsup_cyc_step_frozen.
Print Assumptions Hsup_cyc_stable.
Print Assumptions rotc_spectrum_bound.
Print Assumptions H_adj_spectrum_bound.
Print Assumptions Hsup_cyc_attained_range.
Print Assumptions Hsup_cyc_stable_wit.
Print Assumptions Hsup_cyc_frozen_value_wit.

(* —— 以下 8 件为原 DTPT_ROTC.v §5 公理面审计块逐字随行（S5 棒）；
   经 Import DTPT_Rotation. 解析至本文件 §S5 内联副本 —— *)

(* ========== §5 公理面审计（G4） ========== *)

Print Assumptions rotc_perm.
Print Assumptions rotc_length.
Print Assumptions rotc_inv.
Print Assumptions rotc_full.
Print Assumptions H_rotc_span_lb.
Print Assumptions H_rotc_span_lb_wit.
Print Assumptions H_rotc_separates.
Print Assumptions rotc_Pinf_separates.

(* —— 以下为原 DTPT_RotSpec.v G4 假设审计块逐字随行（S6a 棒）；
   经 Import DTPT_Rotation. 解析至本文件 §S6 并入面 —— *)

(* ===================================================================== *)
(* G4 假设审计（期望全部 Closed under the global context）                  *)
(* ===================================================================== *)

Print Assumptions phcyc_min_perm.
Print Assumptions phase_side_cyc_side_degenerate.
Print Assumptions phase_side_cyc_side_zero.
Print Assumptions phase_dev_witness.
Print Assumptions phase_dev_true_iff.
Print Assumptions phase_dev_rec_ne.
Print Assumptions phase_dev_le.
Print Assumptions phcyc_qle_false_lt.
Print Assumptions phase_dev_strict_of_num.
Print Assumptions phase_dev_stable.
Print Assumptions rotc_0_H_adj.
Print Assumptions phase_dev_0_eq.
Print Assumptions phase_dev_0_of_sorted.
Print Assumptions phase_dev_0_sorted_example.
Print Assumptions phase_dev_0_unsorted_counterex.

(* —— 以下为原 DTPT_Lam.v 旗舰假设审计块逐字随行（S6a 棒）；
   经 Import DTPT_Rotation. 解析至本文件 §S7 并入面 —— *)

(* ========== 旗舰假设审计（M3 归并后 8 件并档） ========== *)

Print Assumptions H_lam_anti_mono.
Print Assumptions H_lam_cyc_diff.
Print Assumptions H_lam_cyc_mono_inc.
Print Assumptions H_lam_cyc_mono_dec.
Print Assumptions H_lam_cyc_oldface_separates.
Print Assumptions H_lam_cyc_H_lam_separates.
Print Assumptions H_lam_cyc_lam_opt_cyc_min.
Print Assumptions H_lam_cyc_lam_opt_cyc_endpoint.

(*
   Closed under the global context） —— *)

Print Assumptions H_adj_app.
Print Assumptions H_adj_Pmid_seam.
Print Assumptions H_adj_Pmid_decomp.
Print Assumptions Pmid_sorted_collapse.
Print Assumptions sorted_abs_le_spread.
Print Assumptions H_adj_Pmid_sorted_exact.
Print Assumptions H_adj_Pmid_sorted_ub2.
Print Assumptions H_adj_Pmid_ub_gen.
Print Assumptions H_adj_Pmid_k0.
Print Assumptions H_adj_Pmid_klen.
Print Assumptions H_adj_Pmid_endpoints_sorted.
Print Assumptions phase_classify_ne_PMid.
Print Assumptions Pmid_sorted_collapse_wit_012.
Print Assumptions H_adj_Pmid_decomp_wit_012.

(*
   期望全 Closed under the global context） —— *)

Print Assumptions H_lam_pmid_lam1.
Print Assumptions H_lam_pmid_lam0.
Print Assumptions H_lam_pmid_diff.
Print Assumptions H_lam_pmid_affine.
Print Assumptions H_lam_pmid_sorted_consistency.
Print Assumptions H_lam_pmid_sorted_lam1.
Print Assumptions H_lam_pmid_sorted_lam0.
Print Assumptions H_lam_pmid_k0_oldface.
Print Assumptions H_lam_pmid_klen_const.
Print Assumptions H_lam_pmid_H_lam_separates.
Print Assumptions H_lam_pmid_wit_201.
Print Assumptions H_lam_pmid_wit_201_ends.

(*
   Closed under the global context） —— *)

Print Assumptions rotc_supersedes_rot_id.
Print Assumptions llm_rot_id_superseded.
Print Assumptions rot_cyclic_cluster_superseded.
Print Assumptions rot_H_adj_face_covered.
Print Assumptions Hsup_oldface_const.
Print Assumptions deprecated_consumers_map_D5_Pinf_perm.
Print Assumptions deprecated_consumers_map_llm_Pmid_zero.
Print Assumptions deprecated_consumers_map_P0_absorbs_Pmid.
Print Assumptions deprecated_consumers_map_Hsup_mono.
Print Assumptions deprecated_consumers_map_Hsup_bounded.
Print Assumptions deprecated_consumers_map_Pinf_eq_l.
Print Assumptions deprecated_consumers_map_H_adj_cross_phase_lb.
Print Assumptions deprecated_consumers_map_u12_phase_side_always_zero.
Print Assumptions H_lam_anti_mono_real.
Print Assumptions lam_opt_cross_phase_real.

(*
   期望全 Closed under the global context） —— *)

Print Assumptions H_lam_gen_diff.
Print Assumptions H_lam_gen_affine.
Print Assumptions H_lam_gen_H_lam.
Print Assumptions H_lam_gen_H_lam_cyc.
Print Assumptions H_lam_gen_H_lam_pmid.
Print Assumptions H_lam_gen_opt.
Print Assumptions H_lam_gen_opt_endpoint.
Print Assumptions lam_opt_align_lambda_opt_eq.
Print Assumptions H_lam_gen_end_rotc0.
Print Assumptions H_lam_gen_end_pmid0.
Print Assumptions H_lam_gen_klen_const.
Print Assumptions H_lam_gen_wit_201_id.
Print Assumptions H_lam_gen_wit_201_pmid.

Print Assumptions DTPT_Rotation.DTPT_Rotation.rotc_perm.
Print Assumptions DTPT_Rotation.DTPT_Rotation.rotc_length.
Print Assumptions DTPT_Rotation.DTPT_Rotation.Pinf_c_perm.
Print Assumptions DTPT_Rotation.DTPT_Rotation.rotc_0.
Print Assumptions DTPT_Rotation.DTPT_Rotation.Pinf_true_id.
Print Assumptions DTPT_Rotation.DTPT_Rotation.rotc_in.
Print Assumptions DTPT_Rotation.DTPT_Rotation.rotc_H_wit_mid.
Print Assumptions DTPT_Rotation.DTPT_Rotation.rotc_H_wit_min.
Print Assumptions DTPT_Rotation.DTPT_Rotation.Hsup_cyc_stable_wit.
Print Assumptions DTPT_Rotation.DTPT_Rotation.Hsup_cyc_frozen_value_wit.
Print Assumptions DTPT_Rotation.DTPT_Rotation.H_lam_pmid_wit_201_ends.
Print Assumptions DTPT_Rotation.DTPT_Rotation.rotc_supersedes_rot_id.
