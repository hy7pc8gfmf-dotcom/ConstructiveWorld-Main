(* ==========================================================================
   abl_dtr_core3.v —— DTPT_Rotation 前件参数消解供给·卷三收尾（参数 73–106）。
   ── 使命：宿主 DTPT_Rotation.v 前件参数登记序第 73–106 位（语句坐标
   :1725–:2675，20 条语句 34 参数，卷界零重叠，106 参数就此收尾）逐参数按
   形态二 T＋P′ 消解供给，卷内三区：T 产路 22 枚（使用宿主已证面全实参
   显式应用透传）；P′ 无前提精简版 10 枚（规范实例/参数族面，零前提
   入口，前提位以规范实例计算闭合）。34 参数全供给＋0 登记；合取结论位 2 处
   （H_adj_Pmid_endpoints_sorted 端点核对／deprecated_consumers_map_Hsup_
   bounded 双界）以拆分双单向供给规避并如实申报；本卷线域内 6 条在册混载
   旗（存在体或显式 Prop 位）照登记不供给。32 定理全 Qed；宿主件零字节动。
   ── 依赖：DTPT（H_adj／xq_ 工具箱／P0／Pinf／align_lambda／lastq 面）、
   DTPT_Entropy（SortedQ／xq_ 桥同名同构，Import 序取宿主同序）、
   DTPT_Rotation（本卷全部参数语句本体与 H_lam_cyc／H_lam_pmid／Hsup／
   Pmid／rotc 定义面）＋stdlib（QArith.QArith／Qabs、List、Permutation、
   Arith、Lia、Extraction）。
   ── 对标行：T＋P′ 分区工艺先例＝abl_dte_core1；合取位拆分先例＝同族
   卷一卷二。
   ── 构造性注记：零承认式声明、零悬置前提、零经典逻辑、零节变量声明位；
   供给语句面＝登记形经 dtr_c3_ 前缀映射现档逐字（零裸 exists／零否定／
   零 iff／零 sumbool／零析取位）；<> 全件 5 处＝NEQ 参数面逐字透传（非
   自造）；有界卫哨 forall x, In x l -> Qabs x <= B 照盘透传；名面全
   dtr_c3_ 前缀；尾置逐件 Print Assumptions Closed，Obj.magic 零判据。
   ── 编译配方：池 cwd＝沙箱/现役/abl_r85_supply_pool；source Live 库根
   toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 后 nice -19
   rocq c -native-compiler no
   -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
   abl_dtr_core3.v；绿判＝EXIT=0／日志零 Error／.vo 头 8 字节
   436f7121 00015ff4／.vo 新于 .v；第五证 rocq check；产物只落本池。
   ========================================================================== *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

Require DTPT.
Require DTPT_Entropy.
Require DTPT_Rotation.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.
Import DTPT_Rotation.DTPT_Rotation.

(* ============================================================ *)
(* 一 供给定理区·T 产路（22 枚；参数 73-106 全覆盖；语句面＝底册参数面    *)
(*    现档逐字经 dtr_c3_ 前缀映射，证明体＝宿主已证面全实参显式应用使用）   *)
(* ============================================================ *)

(* 〔参数 73·:1725 align_lambda_range 逐字〕align 保区间 Q-ORD 离散义务 *)
Theorem dtr_c3_align_lambda_range : forall lam : Q,
  (0 <= lam <= 1)%Q -> (0 <= align_lambda lam <= 1)%Q.
Proof.
  intros lam Hr. exact (align_lambda_range lam Hr).
Qed.

(* 〔参数 74-77·:1818 H_lam_cyc_mono_inc 逐字〕递增方向四卫哨 Q-ORD 离散义务 *)
Theorem dtr_c3_H_lam_cyc_mono_inc :
  forall (l : list Q) (k : nat) (lam1 lam2 : Q),
  (H_adj (rotc k l) <= H_adj (P0 l))%Q ->
  (0 <= lam1 <= 1)%Q -> (0 <= lam2 <= 1)%Q ->
  (lam1 <= lam2)%Q ->
  (H_lam_cyc l k lam1 <= H_lam_cyc l k lam2)%Q.
Proof.
  intros l k lam1 lam2 Hrot H01a H01b Hlam.
  exact (H_lam_cyc_mono_inc l k lam1 lam2 Hrot H01a H01b Hlam).
Qed.

(* 〔参数 78-81·:1836 H_lam_cyc_mono_dec 逐字〕递减方向四卫哨 Q-ORD 离散义务 *)
Theorem dtr_c3_H_lam_cyc_mono_dec :
  forall (l : list Q) (k : nat) (lam1 lam2 : Q),
  (H_adj (P0 l) <= H_adj (rotc k l))%Q ->
  (0 <= lam1 <= 1)%Q -> (0 <= lam2 <= 1)%Q ->
  (lam1 <= lam2)%Q ->
  (H_lam_cyc l k lam2 <= H_lam_cyc l k lam1)%Q.
Proof.
  intros l k lam1 lam2 Hrot H01a H01b Hlam.
  exact (H_lam_cyc_mono_dec l k lam1 lam2 Hrot H01a H01b Hlam).
Qed.

(* 〔参数 82·:1903 H_lam_cyc_lam_opt_cyc_min 逐字〕真基础 argmin 最优值区间卫哨 *)
Theorem dtr_c3_H_lam_cyc_lam_opt_cyc_min :
  forall (l : list Q) (k : nat) (lam : Q),
  (0 <= lam <= 1)%Q ->
  (H_lam_cyc l k (lam_opt_cyc (H_adj (P0 l)) (H_adj (rotc k l)))
   <= H_lam_cyc l k lam)%Q.
Proof.
  intros l k lam H01. exact (H_lam_cyc_lam_opt_cyc_min l k lam H01).
Qed.

(* 〔参数 83-84·:1938 H_adj_app 逐字〕拼接分解双非空卫哨 NEQ 离散义务 *)
Theorem dtr_c3_H_adj_app : forall (l1 l2 : list Q),
  l1 <> [] -> l2 <> [] ->
  H_adj (l1 ++ l2) == H_adj l1 + Qabs (lastq l1 - hd 0 l2) + H_adj l2.
Proof.
  intros l1 l2 H1 H2. exact (H_adj_app l1 l2 H1 H2).
Qed.

(* 〔参数 85-86·:1952 H_adj_Pmid_seam 逐字〕seam 定向形双卫哨 NAT+NEQ 离散义务 *)
Theorem dtr_c3_H_adj_Pmid_seam : forall (l : list Q) (s : nat) (k : nat),
  k <> 0%nat -> (k < length l)%nat ->
  H_adj (Pmid l s k)
  == H_adj (firstn k (P0 l)) + H_adj (skipn k l)
     + Qabs (hd 0 (skipn k l) - lastq (firstn k (P0 l))).
Proof.
  intros l s k Hk Hlt. exact (H_adj_Pmid_seam l s k Hk Hlt).
Qed.

(* 〔参数 87-88·:1977 H_adj_Pmid_decomp 逐字〕Pmid 中相分解双卫哨 NAT+NEQ 离散义务 *)
Theorem dtr_c3_H_adj_Pmid_decomp : forall (l : list Q) (s : nat) (k : nat),
  k <> 0%nat -> (k < length l)%nat ->
  H_adj (Pmid l s k)
  == H_adj (firstn k (P0 l))
     + Qabs (lastq (firstn k (P0 l)) - hd 0 (skipn k l))
     + H_adj (skipn k l).
Proof.
  intros l s k Hk Hlt. exact (H_adj_Pmid_decomp l s k Hk Hlt).
Qed.

(* 〔参数 89-91·:1997 sorted_abs_le_spread 逐字〕接缝闭合 SORTED+双 IN 卫哨 *)
Theorem dtr_c3_sorted_abs_le_spread :
  forall (l : list Q) (z w : Q),
  SortedQ l -> In z l -> In w l -> (Qabs (z - w) <= lastq l - hd 0 l)%Q.
Proof.
  intros l z w HS Hz Hw. exact (sorted_abs_le_spread l z w HS Hz Hw).
Qed.

(* 〔参数 92·:2014 Pmid_sorted_collapse 逐字〕排序坍缩 list 级 Leibniz 等式 *)
Theorem dtr_c3_Pmid_sorted_collapse :
  forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> Pmid l s k = l.
Proof.
  intros l s k HS. exact (Pmid_sorted_collapse l s k HS).
Qed.

(* 〔参数 93·:2026 H_adj_Pmid_sorted_exact 逐字〕精确坍缩面 SORTED 卫哨 *)
Theorem dtr_c3_H_adj_Pmid_sorted_exact :
  forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> H_adj (Pmid l s k) == H_adj l.
Proof.
  intros l s k HS. exact (H_adj_Pmid_sorted_exact l s k HS).
Qed.

(* 〔参数 94·:2037 H_adj_Pmid_sorted_ub2 逐字〕排序上界 2·spread SORTED 卫哨 *)
Theorem dtr_c3_H_adj_Pmid_sorted_ub2 :
  forall (l : list Q) (s : nat) (k : nat),
  SortedQ l ->
  (H_adj (Pmid l s k) <= 2 * (lastq (P0 l) - hd 0 (P0 l)))%Q.
Proof.
  intros l s k HS. exact (H_adj_Pmid_sorted_ub2 l s k HS).
Qed.

(* 〔参数 95-96·:2057 H_adj_Pmid_ub_gen 逐字〕无排序诚实界双卫哨 NAT+NEQ *)
Theorem dtr_c3_H_adj_Pmid_ub_gen : forall (l : list Q) (s : nat) (k : nat),
  k <> 0%nat -> (k < length l)%nat ->
  (H_adj (Pmid l s k)
   <= 2 * (lastq (P0 l) - hd 0 (P0 l)) + H_adj (skipn k l))%Q.
Proof.
  intros l s k Hk Hlt. exact (H_adj_Pmid_ub_gen l s k Hk Hlt).
Qed.

(* /〔参数 97·:2116 H_adj_Pmid_endpoints_sorted 拆分双单向〕宿主结论面
   Prop 合取位（k=0 端 /\ k=length 端）照   :2226／  :481 先例以
   proj1/proj2 抽取拆两单向供给规避——参数 97 一参数两件响亮申报。 *)
Theorem dtr_c3_H_adj_Pmid_endpoints_sorted_lo : forall (l : list Q) (s : nat),
  SortedQ l -> H_adj (Pmid l s 0%nat) == lastq l - hd 0 l.
Proof.
  intros l s HS. exact (proj1 (H_adj_Pmid_endpoints_sorted l s HS)).
Qed.

Theorem dtr_c3_H_adj_Pmid_endpoints_sorted_hi : forall (l : list Q) (s : nat),
  SortedQ l -> H_adj (Pmid l s (length l)) == lastq l - hd 0 l.
Proof.
  intros l s HS. exact (proj2 (H_adj_Pmid_endpoints_sorted l s HS)).
Qed.

(* 〔参数 98·:2234 H_lam_pmid_sorted_consistency 逐字〕排序坍缩一致面 SORTED 卫哨 *)
Theorem dtr_c3_H_lam_pmid_sorted_consistency :
  forall (l : list Q) (s : nat) (k : nat) (lam : Q),
  SortedQ l -> H_lam_pmid l s k lam == H_lam l s lam.
Proof.
  intros l s k lam HS. exact (H_lam_pmid_sorted_consistency l s k lam HS).
Qed.

(* 〔参数 99·:2245 H_lam_pmid_sorted_lam1 逐字〕λ=1 端 sorted 精确面 *)
Theorem dtr_c3_H_lam_pmid_sorted_lam1 :
  forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> H_lam_pmid l s k 1 == H_adj l.
Proof.
  intros l s k HS. exact (H_lam_pmid_sorted_lam1 l s k HS).
Qed.

(* 〔参数 100·:2256 H_lam_pmid_sorted_lam0 逐字〕λ=0 端 sorted 精确面 *)
Theorem dtr_c3_H_lam_pmid_sorted_lam0 :
  forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> H_lam_pmid l s k 0 == H_adj l.
Proof.
  intros l s k HS. exact (H_lam_pmid_sorted_lam0 l s k HS).
Qed.

(* 〔参数 101·:2454 deprecated_consumers_map_P0_absorbs_Pmid 逐字〕
   弃用件真化替代·全 k 吸收不变量 SORTED 卫哨 *)
Theorem dtr_c3_deprecated_consumers_map_P0_absorbs_Pmid :
  forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> P0 (Pmid l s k) = P0 l.
Proof.
  intros l s k HS.
  exact (deprecated_consumers_map_P0_absorbs_Pmid l s k HS).
Qed.

(* /〔参数 102-104·:2479 deprecated_consumers_map_Hsup_bounded 拆分双单向〕
   宿主结论面 Prop 合取位（旧面 2B 界 /\ 真化面 3·spread 界）同 / 配方
   proj1/proj2 抽取拆两单向；有界卫哨 (forall x : Q, In x l -> Qabs x <= B)
   照盘透传（PA_Dep:217 先例同款）——参数 102-104 三参数两件响亮申报。 *)
Theorem dtr_c3_deprecated_consumers_map_Hsup_bounded_old :
  forall (l : list Q) (n : nat) (B : Q),
  (forall x : Q, In x l -> Qabs x <= B) -> SortedQ l -> l <> [] ->
  (Hsup l n <= (Z.of_nat (length l) # 1)%Q * B * 2)%Q.
Proof.
  intros l n B HB HS Hne.
  exact (proj1 (deprecated_consumers_map_Hsup_bounded l n B HB HS Hne)).
Qed.

Theorem dtr_c3_deprecated_consumers_map_Hsup_bounded_cyc :
  forall (l : list Q) (n : nat) (B : Q),
  (forall x : Q, In x l -> Qabs x <= B) -> SortedQ l -> l <> [] ->
  (Hsup_cyc l n <= 3 * (lastq l - hd 0 l))%Q.
Proof.
  intros l n B HB HS Hne.
  exact (proj2 (deprecated_consumers_map_Hsup_bounded l n B HB HS Hne)).
Qed.

(* 〔参数 105·:2551 H_lam_anti_mono_real 逐字〕使用面重定向示范 λ 反单调 *)
Theorem dtr_c3_H_lam_anti_mono_real :
  forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  (lam1 <= lam2)%Q -> (H_lam l s lam2 <= H_lam l s lam1)%Q.
Proof.
  intros l s lam1 lam2 Hlam. exact (H_lam_anti_mono_real l s lam1 lam2 Hlam).
Qed.

(* 〔参数 106·:2675 H_lam_gen_opt 逐字〕统一族 argmin 最优性区间卫哨 *)
Theorem dtr_c3_H_lam_gen_opt : forall (l l2 : list Q) (lam : Q),
  (0 <= lam <= 1)%Q ->
  (H_lam_gen l l2 (lam_opt (H_adj (P0 l)) (H_adj l2))
   <= H_lam_gen l l2 lam)%Q.
Proof.
  intros l l2 lam H01. exact (H_lam_gen_opt l l2 lam H01).
Qed.

(* ============================================================ *)
(* 二 供给定理区·P′ 无前提精简版（10 枚；规范实例/参数族零前提入口；      *)
(*    前提位以计算闭合：unfold Qle+simpl+lia／Qle_refl／discriminate／    *)
(*    xq_P0_sorted 排序规范实例）                                     *)
(* ============================================================ *)

(* P1〔参数 73 P′〕align_lambda 于 (1#2) 规范实例（  dtd_c3_Qle_0_1 配方） *)
Theorem dtr_c3_align_lambda_range_half : (0 <= align_lambda (1#2) <= 1)%Q.
Proof.
  apply (dtr_c3_align_lambda_range (1#2)).
  split; unfold Qle; simpl; lia.
Qed.

(* P2〔参数 82 P′〕真基础 argmin 于 lam:=0 零点规范实例 *)
Theorem dtr_c3_H_lam_cyc_lam_opt_cyc_min_zero : forall (l : list Q) (k : nat),
  (H_lam_cyc l k (lam_opt_cyc (H_adj (P0 l)) (H_adj (rotc k l)))
   <= H_lam_cyc l k 0)%Q.
Proof.
  intros l k. apply (dtr_c3_H_lam_cyc_lam_opt_cyc_min l k 0).
  split; unfold Qle; simpl; lia.
Qed.

(* P3〔参数 83-84 P′〕拼接分解于双单元表参数族实例（卫哨 discriminate 一击） *)
Theorem dtr_c3_H_adj_app_pair : forall (a b : Q),
  H_adj [a; b] == H_adj [a] + Qabs (a - b) + H_adj [b].
Proof.
  intros a b. apply (dtr_c3_H_adj_app [a] [b]).
  - intro Hc. discriminate Hc.
  - intro Hc. discriminate Hc.
Qed.

(* P4〔参数 92 P′〕排序坍缩于 l:=P0 l 规范实例（xq_P0_sorted 排序卫哨规范产路） *)
Theorem dtr_c3_Pmid_P0_collapse : forall (l : list Q) (s : nat) (k : nat),
  Pmid (P0 l) s k = P0 l.
Proof.
  intros l s k. exact (Pmid_sorted_collapse (P0 l) s k (xq_P0_sorted l)).
Qed.

(* P5〔参数 93 P′〕精确坍缩面于 l:=P0 l 规范实例 *)
Theorem dtr_c3_H_adj_Pmid_P0_exact : forall (l : list Q) (s : nat) (k : nat),
  H_adj (Pmid (P0 l) s k) == H_adj (P0 l).
Proof.
  intros l s k. exact (H_adj_Pmid_sorted_exact (P0 l) s k (xq_P0_sorted l)).
Qed.

(* P6〔参数 98 P′〕排序一致面于 l:=P0 l 规范实例 *)
Theorem dtr_c3_H_lam_pmid_P0_consistency :
  forall (l : list Q) (s : nat) (k : nat) (lam : Q),
  H_lam_pmid (P0 l) s k lam == H_lam (P0 l) s lam.
Proof.
  intros l s k lam.
  exact (H_lam_pmid_sorted_consistency (P0 l) s k lam (xq_P0_sorted l)).
Qed.

(* P7〔参数 101 P′〕弃用件吸收不变量于 l:=P0 l 规范实例 *)
Theorem dtr_c3_deprecated_P0_absorbs_P0 : forall (l : list Q) (s : nat) (k : nat),
  P0 (Pmid (P0 l) s k) = P0 (P0 l).
Proof.
  intros l s k.
  exact (deprecated_consumers_map_P0_absorbs_Pmid (P0 l) s k (xq_P0_sorted l)).
Qed.

(* P8〔参数 105 P′〕λ 反单调自反实例（Qle_refl 一击；宿主 :2462 同款在册） *)
Theorem dtr_c3_H_lam_anti_mono_real_refl : forall (l : list Q) (s : nat) (lam : Q),
  (H_lam l s lam <= H_lam l s lam)%Q.
Proof.
  intros l s lam. exact (H_lam_anti_mono_real l s lam lam (Qle_refl lam)).
Qed.

(* P9〔参数 105 P′〕λ 反单调 (1#2)<=1 规范实例（Q 字面量括号位照  ） *)
Theorem dtr_c3_H_lam_anti_mono_real_half : forall (l : list Q) (s : nat),
  (H_lam l s 1 <= H_lam l s (1#2))%Q.
Proof.
  intros l s. apply (dtr_c3_H_lam_anti_mono_real l s (1#2) 1).
  unfold Qle. simpl. lia.
Qed.

(* P10〔参数 106 P′〕统一族 argmin 于 lam:=0 零点规范实例 *)
Theorem dtr_c3_H_lam_gen_opt_zero : forall (l l2 : list Q),
  (H_lam_gen l l2 (lam_opt (H_adj (P0 l)) (H_adj l2))
   <= H_lam_gen l l2 0)%Q.
Proof.
  intros l l2. apply (dtr_c3_H_lam_gen_opt l l2 0).
  split; unfold Qle; simpl; lia.
Qed.

(* ============================================================ *)
(* 三 件尾检验区：逐件承认面验印（32 枚全 Closed）＋定理桶单条          *)
(*    Separate Extraction（ ：同文件多条同名覆写禁触——      *)
(*    数据桶归独立检验件 _dtr_c3_probe.v 定向  另桶；  *)
(*    Extraction 模块 Require 先导＝  处方）                *)
(* ============================================================ *)

Print Assumptions dtr_c3_align_lambda_range.
Print Assumptions dtr_c3_H_lam_cyc_mono_inc.
Print Assumptions dtr_c3_H_lam_cyc_mono_dec.
Print Assumptions dtr_c3_H_lam_cyc_lam_opt_cyc_min.
Print Assumptions dtr_c3_H_adj_app.
Print Assumptions dtr_c3_H_adj_Pmid_seam.
Print Assumptions dtr_c3_H_adj_Pmid_decomp.
Print Assumptions dtr_c3_sorted_abs_le_spread.
Print Assumptions dtr_c3_Pmid_sorted_collapse.
Print Assumptions dtr_c3_H_adj_Pmid_sorted_exact.
Print Assumptions dtr_c3_H_adj_Pmid_sorted_ub2.
Print Assumptions dtr_c3_H_adj_Pmid_ub_gen.
Print Assumptions dtr_c3_H_adj_Pmid_endpoints_sorted_lo.
Print Assumptions dtr_c3_H_adj_Pmid_endpoints_sorted_hi.
Print Assumptions dtr_c3_H_lam_pmid_sorted_consistency.
Print Assumptions dtr_c3_H_lam_pmid_sorted_lam1.
Print Assumptions dtr_c3_H_lam_pmid_sorted_lam0.
Print Assumptions dtr_c3_deprecated_consumers_map_P0_absorbs_Pmid.
Print Assumptions dtr_c3_deprecated_consumers_map_Hsup_bounded_old.
Print Assumptions dtr_c3_deprecated_consumers_map_Hsup_bounded_cyc.
Print Assumptions dtr_c3_H_lam_anti_mono_real.
Print Assumptions dtr_c3_H_lam_gen_opt.
Print Assumptions dtr_c3_align_lambda_range_half.
Print Assumptions dtr_c3_H_lam_cyc_lam_opt_cyc_min_zero.
Print Assumptions dtr_c3_H_adj_app_pair.
Print Assumptions dtr_c3_Pmid_P0_collapse.
Print Assumptions dtr_c3_H_adj_Pmid_P0_exact.
Print Assumptions dtr_c3_H_lam_pmid_P0_consistency.
Print Assumptions dtr_c3_deprecated_P0_absorbs_P0.
Print Assumptions dtr_c3_H_lam_anti_mono_real_refl.
Print Assumptions dtr_c3_H_lam_anti_mono_real_half.
Print Assumptions dtr_c3_H_lam_gen_opt_zero.

Set Extraction Output Directory "_log/dtr_t11".

Separate Extraction
  dtr_c3_align_lambda_range
  dtr_c3_H_lam_cyc_mono_inc
  dtr_c3_H_lam_cyc_mono_dec
  dtr_c3_H_lam_cyc_lam_opt_cyc_min
  dtr_c3_H_adj_app
  dtr_c3_H_adj_Pmid_seam
  dtr_c3_H_adj_Pmid_decomp
  dtr_c3_sorted_abs_le_spread
  dtr_c3_Pmid_sorted_collapse
  dtr_c3_H_adj_Pmid_sorted_exact
  dtr_c3_H_adj_Pmid_sorted_ub2
  dtr_c3_H_adj_Pmid_ub_gen
  dtr_c3_H_adj_Pmid_endpoints_sorted_lo
  dtr_c3_H_adj_Pmid_endpoints_sorted_hi
  dtr_c3_H_lam_pmid_sorted_consistency
  dtr_c3_H_lam_pmid_sorted_lam1
  dtr_c3_H_lam_pmid_sorted_lam0
  dtr_c3_deprecated_consumers_map_P0_absorbs_Pmid
  dtr_c3_deprecated_consumers_map_Hsup_bounded_old
  dtr_c3_deprecated_consumers_map_Hsup_bounded_cyc
  dtr_c3_H_lam_anti_mono_real
  dtr_c3_H_lam_gen_opt
  dtr_c3_align_lambda_range_half
  dtr_c3_H_lam_cyc_lam_opt_cyc_min_zero
  dtr_c3_H_adj_app_pair
  dtr_c3_Pmid_P0_collapse
  dtr_c3_H_adj_Pmid_P0_exact
  dtr_c3_H_lam_pmid_P0_consistency
  dtr_c3_deprecated_P0_absorbs_P0
  dtr_c3_H_lam_anti_mono_real_refl
  dtr_c3_H_lam_anti_mono_real_half
  dtr_c3_H_lam_gen_opt_zero.
