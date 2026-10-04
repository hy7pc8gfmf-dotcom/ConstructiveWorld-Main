(* ==========================================================================
   abl_dtr_core2.v —— DTPT_Rotation 前件参数消解供给·卷二（参数 37–72）。
   ── 使命：宿主 DTPT_Rotation.v 前件参数登记序第 37–72 位（语句坐标
   :586–:1711，31 条语句 36 参数，与卷一卷界零重叠）逐参数按形态二 T＋P′
   消解供给：T＝参数面产路（SortedQ P0 规范形／P0-cons 非空卫哨／nat 长度
   自反卫哨／置换自反构造子／有序列转发／phase_dev 闭式见证／跨相下界转发
   ／Q 序平凡卫哨），P′＝宿主结论面现档逐字特化（全实参显式应用，参数消
   即出）。36 参数＝33 P′ 供给＋3 T 单独交付（H_adj_rotc_sorted_exact 析取
   位／phase_dev_rec_ne 否定形／phase_dev_strict_of_num 合取位——源结论面
   Prop 位禁入本件语句面，照三参数先例单独交付非失败位）；41 件＝13 T＋
   28 P′ 全 Qed；本卷行域内 10 条在册混载旗（零顶层前件实测）照登记不供给。
   宿主件零字节动零级联。
   ── 依赖：DTPT→DTPT_Entropy→DTPT_Rotation（与宿主件头 Require/Import
   序逐字同序，同名同构名面解析位即宿主本尊）＋stdlib（QArith.QArith／
   Qabs、List、Permutation、Lia、Extraction）。
   ── 对标行：T＋P′ 形态二先例＝abl_tbn_supply_b；同构记录法工艺先例＝
   abl_dtd_core2／abl_dtd_core4。
   ── 构造性注记：零承认式声明、零悬置前提、零经典逻辑，全部结论 Qed 真构造
   闭合；P′ 语句面零新增 Prop 逻辑词（无裸 exists／无 iff／无 -> False
   结论位／无析取合取位）；<> 全件仅 dtr_c2_P0_cons_ne 一处＝NEQ 参数面
   逐字透传（非自造）；名面全 dtr_c2_ 前缀；尾置逐件 Print Assumptions
   Closed＋Separate Extraction 归专属桶（数据层第二桶独立定向），Obj.magic
   零判据；Qed 计数 41 核对零差。
   ── 编译配方：池 cwd＝沙箱/现役/abl_r85_supply_pool；source Live 库根
   toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 后 nice -19
   rocq c -native-compiler no
   -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
   abl_dtr_core2.v；绿判＝EXIT=0／日志零 Error／.vo 头 8 字节
   436f7121 00015ff4／.vo 新于 .v；第五证 rocq check；产物只落本池。
   ========================================================================== *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Permutation.
From Stdlib Require Import Lia.
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
(* §一 共用卫哨/证书产路区（供给定理 T·13 枚）                      *)
(*    逐枚＝底册参数面的构造性产路：SortedQ P0 规范形路、P0-cons      *)
(*    非空卫哨路、nat 长度自反卫哨路、置换自反构造子路、witness     *)
(*    有序列转发路、phase_dev 闭式见证路、跨相下界转发路、Q 序      *)
(*    平凡卫哨路、判定器升证路。                                   *)
(* ============================================================ *)

(* 〔SORTED 产路·供 :586/:604/:1170 三参数〕P0 规范形恒有序：
   xq_P0_sorted 在役产路转发（普查「SortedQ 有产路（xq_P0_sorted）」锚；
   Import 序取 DTPT_Entropy 本尊，与宿主同名解析位一致；平凡转发位
   申报见交付报告） *)
Theorem dtr_c2_sorted_P0 : forall l : list Q, SortedQ (P0 l).
Proof.
  intro l. exact (xq_P0_sorted l).
Qed.

(* 〔NEQ 非空卫哨产路·供 :604/:702 两参数〕P0 cons 形：
   P0 (x :: xs) <> []（宿主 xq_P0_cons_ne 全参转发，普查「卫哨可平凡
   供给」锚；<> 系 NEQ 参数面逐字，/ 同款任务指定透传形） *)
Theorem dtr_c2_P0_cons_ne : forall (x : Q) (xs : list Q), P0 (x :: xs) <> [].
Proof.
  intros x xs. exact (xq_P0_cons_ne x xs).
Qed.

(* 〔NAT 长度自反卫哨产路·供 :779/:793/:807/:925/:1080 五参数〕
   (length l <= length l) 的 nat 层平凡产路（普查「卫哨可平凡供给」锚；
   平凡位申报见交付报告） *)
Theorem dtr_c2_nat_le_len_id : forall l : list Q, (length l <= length l)%nat.
Proof.
  intro l. apply le_n.
Qed.

(* 〔PERM 自反构造子产路·供 :1304 参数〕Permutation l l（stdlib
   Permutation_refl 构造子一击，普查「Permutation 有构造子」锚；
   平凡位申报见交付报告） *)
Theorem dtr_c2_perm_refl : forall l : list Q, Permutation l l.
Proof.
  intro l. apply Permutation_refl.
Qed.

(* 〔SORTED witness 产路·供 :1152 三参数〕宿主见证列 [0;0;2] 有序面
   转发（宿主 sorted_wit_002 在役同语句件；witness 产路＝转发形申报） *)
Theorem dtr_c2_sorted_wit_002 : SortedQ [0; 0; 2].
Proof.
  exact sorted_wit_002.
Qed.

(* 〔BOOL 闭式见证产路·供 :1392/:1401 两参数〕phase_dev 见证：
   [0;1;2] 转 1 格偏差判出（宿主 phase_dev_witness 同款 vm_compute
   一发闭式；本件供其剥存在面的裸数据卫哨形） *)
Theorem dtr_c2_phase_dev_wit_true : phase_dev [0; 1; 2] 1 = true.
Proof.
  vm_compute. reflexivity.
Qed.

(* 〔Q-ORD 反向卫哨产路·供 :1576 参数 1〕H_adj (Pinf [0;1;2] s) <=
   H_adj (P0 [0;1;2])（:1576 参数 1 系真前提位——递增方向要求 Pinf 相熵
   不越 P0 相熵，与跨相下界反向，不可由 H_adj_cross_phase_lb 消解；
   本路走见证列 [0;1;2]（P0 恒等= 面）：Pinf_true_id 换写把 Pinf 相
   归原表相，余 H_adj l <= H_adj (P0 l) 由 Qle_refl 换等直收——
   失败显式申报 申报：本参数前件非恒真式，只供见证实例位，泛形无在库消解路） *)
Theorem dtr_c2_Hadj_pinf_le_P0_wit : forall s : nat,
  (H_adj (Pinf [0; 1; 2] s) <= H_adj (P0 [0; 1; 2]))%Q.
Proof.
  intros s. rewrite (Pinf_true_id [0; 1; 2] s). apply Qle_refl.
Qed.

(* 〔Q-ORD 平凡卫哨产路·供 :1551/:1576 两参数〕(0 <= 1) 的 Q 层产路
   （Qle 展开后 Z 层 lia 一步；普查「Q 序等可判定」锚；平凡位申报见
   交付报告） *)
Theorem dtr_c2_Qle_0_1 : (0 <= 1)%Q.
Proof.
  unfold Qle. simpl. lia.
Qed.

(* 〔Q-ORD 区间卫哨产路·供 :1636/:1663/:1711 三参数〕(0 <= 0 <= 1) 的
   Q 层产路（合取双支各 Qle_refl/lia；:1636 参数 (0 <= lam <= 1) 于
   lam := 0 规范实例） *)
Theorem dtr_c2_Qle_01_bounds : (0 <= 0 <= 1)%Q.
Proof.
  split.
  - apply Qle_refl.
  - unfold Qle. simpl. lia.
Qed.

(* 〔Q-ORD 规范非负有理数产路·供 :1057 参数〕(0 <= (Z.of_nat n # 1))
   的 Q 层产路（Qle 展开后 0 <= Z.of_nat n 由 lia zify 内建支撑——
    宿主 :818 同款实证） *)
Theorem dtr_c2_Qle_0_of_nat_pos : forall n : nat,
  (0 <= (Z.of_nat n # 1)%Q)%Q.
Proof.
  intro n. unfold Qle. simpl. lia.
Qed.

(* 〔EQ 计算等产路·供 :1472 参数〕P0 [0;1;2] = [0;1;2]（P0 Fixpoint
   闭项可计算换等，exact eq_refl 一步—— 「构造子＋可换等目标
   全参 exact 形」配方） *)
Theorem dtr_c2_P0_wit_012_eq : P0 [0; 1; 2] = [0; 1; 2].
Proof.
  exact eq_refl.
Qed.

(* 〔Qeq 相位重合见证产路·供 :1591 参数〕H_adj (P0 [0;0;2]) ==
   H_adj (Pinf [0;0;2] s)（P0 [0;0;2] 闭项计算等＋Pinf_true_id 换写
   ＋Qeq_refl 三步链；:1591 参数前件于见证列重合实例的在库消解路） *)
Theorem dtr_c2_Hadj_phase_eq_wit : forall s : nat,
  H_adj (P0 [0; 0; 2]) == H_adj (Pinf [0; 0; 2] s).
Proof.
  intros s.
  assert (E : P0 [0; 0; 2] = [0; 0; 2]) by (exact eq_refl).
  rewrite E. rewrite (Pinf_true_id [0; 0; 2] s). apply Qeq_refl.
Qed.

(* 〔BOOL 判定器升证产路·供 :1420 参数〕Qle_bool (H_adj (rotc 1 [0;1;2]))
   (H_adj (P0 [0;1;2])) = false（见证列上 H_adj 3 > 2 的判定器闭式
   反向判伪；vm_compute 一发——宿主 :1420 参数前件的规范实例） *)
Theorem dtr_c2_Qle_bool_Hadj_wit_false :
  Qle_bool (H_adj (rotc 1 [0; 1; 2])) (H_adj (P0 [0; 1; 2])) = false.
Proof.
  vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* §二 P′ 无前提精简版区（28 枚·覆盖 33 参数）                        *)
(*    逐枚＝宿主定理 @ 全实参显式应用＋参数由 §一 产路（或卫哨内联）输入，    *)
(*    出无前提精简版；语句面＝宿主结论面现档逐字特化（离散承载）。    *)
(*    三参数 P′ （:586/:1392/:1420，见④）。                       *)
(* ============================================================ *)

(* P1〔:604 H_adj_rotc_ub3 参数 38-39〕3·spread 上界 P0-cons 规范形无前提
   精简版：SortedQ 参数喂 dtr_c2_sorted_P0、非空卫哨参数喂 dtr_c2_P0_cons_ne，
   出 rotc k (P0 (x::l)) 三倍界面 *)
Theorem dtr_c2_H_adj_rotc_ub3_P0cons :
  forall (k : nat) (x : Q) (l : list Q),
    (H_adj (rotc k (P0 (x :: l)))
     <= 3 * (lastq (P0 (x :: l)) - hd 0 (P0 (x :: l))))%Q.
Proof.
  intros k x l.
  exact (H_adj_rotc_ub3 k (P0 (x :: l)) (dtr_c2_sorted_P0 (x :: l))
                        (dtr_c2_P0_cons_ne x l)).
Qed.

(* P2〔:702 Hsup_cyc_ub 参数 40-41〕真动态上确界 3·spread 界 P0-cons 规范形
   无前提精简版：双参数同 P1 配方，出 Hsup_cyc (P0 (x::l)) n 界面 *)
Theorem dtr_c2_Hsup_cyc_ub_P0cons :
  forall (n : nat) (x : Q) (l : list Q),
    (Hsup_cyc (P0 (x :: l)) n
     <= 3 * (lastq (P0 (x :: l)) - hd 0 (P0 (x :: l))))%Q.
Proof.
  intros n x l.
  exact (Hsup_cyc_ub (P0 (x :: l)) n (dtr_c2_sorted_P0 (x :: l))
                     (dtr_c2_P0_cons_ne x l)).
Qed.

(* P3〔:779 hs_skipn_app_le 参数 42〕skipn 分段律长度规范形无前提精简版：
   NAT 参数于 m := length b 喂 dtr_c2_nat_le_len_id，出分段等式面 *)
Theorem dtr_c2_hs_skipn_app_le_len :
  forall (b c : list Q),
    skipn (length b) (b ++ c) = skipn (length b) b ++ c.
Proof.
  intros b c. exact (hs_skipn_app_le b (length b) c (dtr_c2_nat_le_len_id b)).
Qed.

(* P4〔:793 hs_firstn_app_le 参数 43〕firstn 分段律长度规范形无前提精简版：
   同 P3 配方 *)
Theorem dtr_c2_hs_firstn_app_le_len :
  forall (b c : list Q),
    firstn (length b) (b ++ c) = firstn (length b) b.
Proof.
  intros b c. exact (hs_firstn_app_le b (length b) c (dtr_c2_nat_le_len_id b)).
Qed.

(* P5〔:807 hs_skipn_app_r 参数 44〕skipn 越段律长度规范形无前提精简版：
   NAT 参数于 k := length a 喂 dtr_c2_nat_le_len_id，出越段面 *)
Theorem dtr_c2_hs_skipn_app_r_len :
  forall (a c : list Q),
    skipn (length a) (a ++ c) = skipn (length a - length a) c.
Proof.
  intros a c. exact (hs_skipn_app_r a (length a) c (dtr_c2_nat_le_len_id a)).
Qed.

(* P6〔:833 rotc_add_local 参数 45〕有界加法律见证形无前提精简版：
   NAT 参数于见证列 [0;1;2] 双转一（卫哨 simpl;lia 闭式内联），出
   rotc 1 (rotc 1 [0;1;2]) = rotc 2 [0;1;2] 计算面 *)
Theorem dtr_c2_rotc_add_local_wit :
  rotc 1 (rotc 1 [0; 1; 2]) = rotc 2 [0; 1; 2].
Proof.
  assert (Hg : (1 + 1 <= length [0; 1; 2])%nat) by (simpl; lia).
  exact (rotc_add_local 1 1 [0; 1; 2] Hg).
Qed.

(* P7〔:893 qmax2_le 参数 46〕qmax2 吸收自反规范形无前提精简版：
   Q-ORD 参数于 y := x 喂 Qle_refl（stdlib 内联），出 qmax2 x x <= x
   幂等面 *)
Theorem dtr_c2_qmax2_le_refl : forall x : Q, (qmax2 x x <= x)%Q.
Proof.
  intro x. apply qmax2_le. apply Qle_refl.
Qed.

(* P8〔:902 Hsup_cyc_mono_from 参数 47〕跨距单调零基规范形无前提精简版：
   NAT 参数于 a := 0 喂 Nat.le_0_l（stdlib 内联），出 Hsup_cyc l 0 不越
   任意跨距面 *)
Theorem dtr_c2_Hsup_cyc_mono_from_0 :
  forall (l : list Q) (b : nat), (Hsup_cyc l 0 <= Hsup_cyc l b)%Q.
Proof.
  intros l b. exact (Hsup_cyc_mono_from l 0 b (Nat.le_0_l b)).
Qed.

(* P9〔:925 Hsup_cyc_step_frozen 参数 48〕单步冻结边界规范形无前提精简版：
   NAT 参数于 n := length l 喂 dtr_c2_nat_le_len_id，出越界一转冻结面 *)
Theorem dtr_c2_Hsup_cyc_step_frozen_len :
  forall l : list Q, Hsup_cyc l (S (length l)) == Hsup_cyc l (length l).
Proof.
  intro l. exact (Hsup_cyc_step_frozen l (length l) (dtr_c2_nat_le_len_id l)).
Qed.

(* P10〔:943 Hsup_cyc_stable 参数 49〕冻结定理见证形无前提精简版：
   NAT 参数于见证列 n := 7（卫哨 simpl;lia 内联），出 Hsup_cyc [0;1;2] 7
   冻结于表长处面 *)
Theorem dtr_c2_Hsup_cyc_stable_wit :
  Hsup_cyc [0; 1; 2] 7 == Hsup_cyc [0; 1; 2] (length [0; 1; 2]).
Proof.
  assert (Hg : (length [0; 1; 2] <= 7)%nat) by (simpl; lia).
  exact (Hsup_cyc_stable [0; 1; 2] 7 Hg).
Qed.

(* P11〔:1057 rs_le_double 参数 50〕二倍自界规范非负族无前提精简版：
   Q-ORD 参数于 s := (Z.of_nat n # 1) 喂 dtr_c2_Qle_0_of_nat_pos，出
   规范非负有理数二倍界面 *)
Theorem dtr_c2_rs_le_double_nat : forall n : nat,
  ((Z.of_nat n # 1) <= 2 * (Z.of_nat n # 1))%Q.
Proof.
  intro n. exact (rs_le_double (Z.of_nat n # 1) (dtr_c2_Qle_0_of_nat_pos n)).
Qed.

(* P12〔:1080 rotc_periodic 参数 51〕周期冻结边界规范形无前提精简版：
   NAT 参数于 k := length l 喂 dtr_c2_nat_le_len_id，出再转整圈冻结面 *)
Theorem dtr_c2_rotc_periodic_len :
  forall l : list Q, rotc (length l + length l) l = rotc (length l) l.
Proof.
  intro l. exact (rotc_periodic l (length l) (dtr_c2_nat_le_len_id l)).
Qed.

(* P13〔:1110 rs_lastq_cons_ne 参数 52〕尾元剥头双 cons 形无前提精简版：
   NEQ 参数于 xs := y::ys 喂判别卫哨（discriminate 内联），出
   lastq (x::y::ys) = lastq (y::ys) 面 *)
Theorem dtr_c2_rs_lastq_cons_ne_cons :
  forall (x y : Q) (ys : list Q), lastq (x :: y :: ys) = lastq (y :: ys).
Proof.
  intros x y ys.
  assert (Hne : (y :: ys) <> []) by discriminate.
  exact (rs_lastq_cons_ne x (y :: ys) Hne).
Qed.

(* P14〔:1120 rs_lastq_firstn_hd_skipn 参数 53〕转点等元双 cons 形无前提
   精简版：NAT 参数于 j := 1（卫哨 simpl;lia 内联），出 firstn 2 尾元 =
   skipn 1 首元面 *)
Theorem dtr_c2_rs_lastq_firstn_hd_skipn_cons2 :
  forall (x y : Q) (l : list Q),
    lastq (firstn 2 (x :: y :: l)) = hd 0 (skipn 1 (x :: y :: l)).
Proof.
  intros x y l.
  assert (Hg : (1 < length (x :: y :: l))%nat) by (simpl; lia).
  exact (rs_lastq_firstn_hd_skipn (x :: y :: l) 1 Hg).
Qed.

(* P15〔:1140 rs_skipn_S_incl 参数 54〕相邻段包含双 cons 形无前提精简版：
   IN 参数于 z := 次元 y 经 In-cons 头构造内联输入，出 In y (skipn 0 …) 面 *)
Theorem dtr_c2_rs_skipn_S_incl_cons2 :
  forall (x y : Q) (l : list Q), In y (skipn 0 (x :: y :: l)).
Proof.
  intros x y l.
  assert (Hin : In y (skipn 1 (x :: y :: l))) by (simpl; left; reflexivity).
  exact (rs_skipn_S_incl (x :: y :: l) 0 y Hin).
Qed.

(* P16〔:1152 rs_seam_order 参数 55-57〕接缝序见证形无前提精简版：
   SORTED 参数喂 dtr_c2_sorted_wit_002、双 NAT 参数内联（Nat.lt_0_succ／
   simpl;lia），出见证列 1 格转接缝序面 *)
Theorem dtr_c2_rs_seam_order_wit :
  (lastq (firstn 1 [0; 0; 2]) <= hd 0 (skipn 1 [0; 0; 2]))%Q.
Proof.
  assert (Hlen : (1 < length [0; 0; 2])%nat) by (simpl; lia).
  exact (rs_seam_order [0; 0; 2] 1 dtr_c2_sorted_wit_002
                       (Nat.lt_0_succ 0) Hlen).
Qed.

(* P17〔:1170 rotc_class_sharp_ub 参数 58〕2·spread 锐化上界 P0-cons 规范形
   无前提精简版：SORTED 参数喂 dtr_c2_sorted_P0，出 rotc k (P0 (x::l))
   二倍界面 *)
Theorem dtr_c2_rotc_class_sharp_ub_P0cons :
  forall (k : nat) (x : Q) (l : list Q),
    (H_adj (rotc k (P0 (x :: l)))
     <= 2 * (lastq (P0 (x :: l)) - hd 0 (P0 (x :: l))))%Q.
Proof.
  intros k x l.
  exact (rotc_class_sharp_ub (P0 (x :: l)) k (dtr_c2_sorted_P0 (x :: l))).
Qed.

(* P18〔:1304 phcyc_min_perm 参数 59〕排序最小化自反规范形无前提精简版：
   PERM 参数于 p := l 喂 dtr_c2_perm_refl，出 H_adj (P0 l) <= H_adj l 面
   （宿主 C_sorted_min_adj 同语句独立重演位） *)
Theorem dtr_c2_phcyc_min_perm_refl :
  forall l : list Q, (H_adj (P0 l) <= H_adj l)%Q.
Proof.
  intro l. exact (phcyc_min_perm l l (dtr_c2_perm_refl l)).
Qed.

(* P19〔:1401 phase_dev_le 参数 61〕偏差序面见证形无前提精简版：
   BOOL 参数喂 dtr_c2_phase_dev_wit_true，出见证列排序相不越真旋转相面 *)
Theorem dtr_c2_phase_dev_le_wit :
  (H_adj (P0 [0; 1; 2]) <= H_adj (rotc 1 [0; 1; 2]))%Q.
Proof.
  exact (phase_dev_le [0; 1; 2] 1 dtr_c2_phase_dev_wit_true).
Qed.

(* P20〔:1412 phcyc_qle_false_lt 参数 62〕严格升格见证形无前提精简版：
   BOOL 参数于 (x,y) := (0,1) 喂判定器闭式（reflexivity 内联——闭项布尔
   等式一发），出 (0 < 1) 面 *)
Theorem dtr_c2_phcyc_qle_false_lt_wit : (0 < 1)%Q.
Proof.
  assert (E : Qle_bool 1 0 = false) by reflexivity.
  exact (phcyc_qle_false_lt 0 1 E).
Qed.

(* P21〔:1443 phase_dev_stable 参数 64〕相位稳定见证形无前提精简版：
   BOOL 参数于 k := 0 喂闭式卫哨（vm_compute 内联），出见证列零转相熵
   数值相等面 *)
Theorem dtr_c2_phase_dev_stable_wit :
  H_adj (rotc 0 [0; 1; 2]) == H_adj (P0 [0; 1; 2]).
Proof.
  assert (E : phase_dev [0; 1; 2] 0 = false) by (vm_compute; reflexivity).
  exact (phase_dev_stable [0; 1; 2] 0 E).
Qed.

(* P22〔:1472 phase_dev_0_of_sorted 参数 65〕零转无偏差见证形无前提精简版：
   EQ 参数喂 dtr_c2_P0_wit_012_eq，出见证列零转偏差 false 面 *)
Theorem dtr_c2_phase_dev_0_of_sorted_wit :
  phase_dev [0; 1; 2] 0 = false.
Proof.
  exact (phase_dev_0_of_sorted [0; 1; 2] dtr_c2_P0_wit_012_eq).
Qed.

(* P23〔:1551 H_lam_anti_mono 参数 66〕反向单调端点规范形无前提精简版：
   Q-ORD 参数于 (lam1,lam2) := (0,1) 喂 dtr_c2_Qle_0_1，出 λ=1 值不越
   λ=0 值面（＝跨相下界端点重演位） *)
Theorem dtr_c2_H_lam_anti_mono_01 :
  forall (l : list Q) (s : nat), (H_lam l s 1 <= H_lam l s 0)%Q.
Proof.
  intros l s. exact (H_lam_anti_mono l s 0 1 dtr_c2_Qle_0_1).
Qed.

(* P24〔:1576 H_lam_mono_diff 参数 67-68〕递增方向见证形无前提精简版：
   参数 1 喂 dtr_c2_Hadj_pinf_le_P0_wit、参数 2 喂 dtr_c2_Qle_0_1，出见证列
   λ=0 值不越 λ=1 值面（参数 1 泛形无在库消解路，见证位 失败显式申报 申报
   见  位） *)
Theorem dtr_c2_H_lam_mono_diff_wit :
  forall s : nat, (H_lam [0; 1; 2] s 0 <= H_lam [0; 1; 2] s 1)%Q.
Proof.
  intros s.
  exact (H_lam_mono_diff [0; 1; 2] s 0 1 (dtr_c2_Hadj_pinf_le_P0_wit s)
                         dtr_c2_Qle_0_1).
Qed.

(* P25〔:1591 H_lam_const_when_eq 参数 69〕斜率零常数见证形无前提精简版：
   Qeq 参数喂 dtr_c2_Hadj_phase_eq_wit（见证列相位重合实例），出
   H_lam [0;0;2] s lam 恒等于 P0 相面 *)
Theorem dtr_c2_H_lam_const_when_eq_wit :
  forall (s : nat) (lam : Q),
    H_lam [0; 0; 2] s lam == H_adj (P0 [0; 0; 2]).
Proof.
  intros s lam. exact (H_lam_const_when_eq [0; 0; 2] s lam (dtr_c2_Hadj_phase_eq_wit s)).
Qed.

(* P26〔:1636 lam_opt_min 参数 70〕argmin 泛形零端规范形无前提精简版：
   Q-ORD 参数于 lam := 0 喂 dtr_c2_Qle_01_bounds，出选择器值不越 λ=0 值面 *)
Theorem dtr_c2_lam_opt_min_0 : forall h0 h1 : Q,
  (lam_opt h0 h1 * h0 + (1 - lam_opt h0 h1) * h1
   <= 0 * h0 + (1 - 0) * h1)%Q.
Proof.
  intros h0 h1. exact (lam_opt_min h0 h1 0 dtr_c2_Qle_01_bounds).
Qed.

(* P27〔:1663 H_lam_lam_opt_min 参数 71〕H_lam 使用版零端规范形无前提精简版：
   同 P26 配方，出混合熵选择器值不越 λ=0 值面 *)
Theorem dtr_c2_H_lam_lam_opt_min_0 :
  forall (l : list Q) (s : nat),
    (H_lam l s (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s)))
     <= H_lam l s 0)%Q.
Proof.
  intros l s. exact (H_lam_lam_opt_min l s 0 dtr_c2_Qle_01_bounds).
Qed.

(* P28〔:1711 lam_opt_min_align 参数 72〕align 稳定零端规范形无前提精简版：
   同 P26 配方，出 align 后选择器值不越 λ=0 值面 *)
Theorem dtr_c2_lam_opt_min_align_0 :
  forall (l : list Q) (s : nat),
    (H_lam l s (align_lambda (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))))
     <= H_lam l s 0)%Q.
Proof.
  intros l s. exact (lam_opt_min_align l s 0 dtr_c2_Qle_01_bounds).
Qed.

(* ============================================================ *)
(* 三 查重登记块（禁重复供给声明， 先例照办）：                     *)
(*   （一）名面：本件全部顶层名 41 枚（13 供给定理 T＋28 无前提精简版   *)
(*   P′）全 dtr_c2_ 新前缀，Live 全树＋本池 grep 零命中                *)
(*   （ 防撞扫描实录），宿主在役名零触碰零别名转发。            *)
(*   （二）参数面：卷二 36 参数＝33 参数 P′ 供给＋3 参数 T 单独交付（:586 结论面  *)
(*   Prop 析取位／:1392 结论面 <> 形／:1420 结论面 Prop 合取位——红线二   *)
(*   禁入语句面，响亮申报位），参数号与普查底册 §1.4 登记序逐位核对       *)
(*   （①总表），零双供零漏账。                                        *)
(*   （三）宿主界：DTPT_Rotation.v 本体零字节不动（缓存根 .v 与 Live    *)
(*   .v 逐字节同值双面实测）；本件 Require   *)
(*   宿主＝只读引用（试批 3 同款形态二单宿主依赖位），产物只落本池不    *)
(*   回灌缓存根（ABSORB82  双影避位），宿主重编零级联于本件宿主面。  *)
(* ============================================================ *)

(* ============================================================ *)
(* 四 尾置验印区（文件最尾）：逐件承认面验印（全 Closed 判据）——        *)
(*    名清单＝13 T＋28 P′＝41 名，与 Qed 计数 41 零差                  *)
(* ============================================================ *)

Print Assumptions dtr_c2_sorted_P0.
Print Assumptions dtr_c2_P0_cons_ne.
Print Assumptions dtr_c2_nat_le_len_id.
Print Assumptions dtr_c2_perm_refl.
Print Assumptions dtr_c2_sorted_wit_002.
Print Assumptions dtr_c2_phase_dev_wit_true.
Print Assumptions dtr_c2_Hadj_pinf_le_P0_wit.
Print Assumptions dtr_c2_Qle_0_1.
Print Assumptions dtr_c2_Qle_01_bounds.
Print Assumptions dtr_c2_Qle_0_of_nat_pos.
Print Assumptions dtr_c2_P0_wit_012_eq.
Print Assumptions dtr_c2_Hadj_phase_eq_wit.
Print Assumptions dtr_c2_Qle_bool_Hadj_wit_false.
Print Assumptions dtr_c2_H_adj_rotc_ub3_P0cons.
Print Assumptions dtr_c2_Hsup_cyc_ub_P0cons.
Print Assumptions dtr_c2_hs_skipn_app_le_len.
Print Assumptions dtr_c2_hs_firstn_app_le_len.
Print Assumptions dtr_c2_hs_skipn_app_r_len.
Print Assumptions dtr_c2_rotc_add_local_wit.
Print Assumptions dtr_c2_qmax2_le_refl.
Print Assumptions dtr_c2_Hsup_cyc_mono_from_0.
Print Assumptions dtr_c2_Hsup_cyc_step_frozen_len.
Print Assumptions dtr_c2_Hsup_cyc_stable_wit.
Print Assumptions dtr_c2_rs_le_double_nat.
Print Assumptions dtr_c2_rotc_periodic_len.
Print Assumptions dtr_c2_rs_lastq_cons_ne_cons.
Print Assumptions dtr_c2_rs_lastq_firstn_hd_skipn_cons2.
Print Assumptions dtr_c2_rs_skipn_S_incl_cons2.
Print Assumptions dtr_c2_rs_seam_order_wit.
Print Assumptions dtr_c2_rotc_class_sharp_ub_P0cons.
Print Assumptions dtr_c2_phcyc_min_perm_refl.
Print Assumptions dtr_c2_phase_dev_le_wit.
Print Assumptions dtr_c2_phcyc_qle_false_lt_wit.
Print Assumptions dtr_c2_phase_dev_stable_wit.
Print Assumptions dtr_c2_phase_dev_0_of_sorted_wit.
Print Assumptions dtr_c2_H_lam_anti_mono_01.
Print Assumptions dtr_c2_H_lam_mono_diff_wit.
Print Assumptions dtr_c2_H_lam_const_when_eq_wit.
Print Assumptions dtr_c2_lam_opt_min_0.
Print Assumptions dtr_c2_H_lam_lam_opt_min_0.
Print Assumptions dtr_c2_lam_opt_min_align_0.

(* ============================================================ *)
(* 五 提取检验区（红线四：可提取验证，Obj.magic 计数＝0 判据）            *)
(*    桶一（定理面）：41 件逐件 Separate Extraction（Prop 结论面随提取   *)
(*    擦除， 口径「构造子参提取擦除」惯例；产物归  专属    *)
(*    桶）。桶二（数据层真实现）：宿主数据层承载（rotc/P0/H_adj/qmax2/   *)
(*    Hsup_cyc/phase_dev/lam_opt/H_lam/insert_q）由独立检验件           *)
(*    _dtr_c2_probe.v 定向重提取归 （  分桶      *)
(*    处方①——单文件双 Separate Extraction 同名覆写避位）。              *)
(* ============================================================ *)

Set Extraction Output Directory "_log/dtr_t9".

Separate Extraction dtr_c2_sorted_P0 dtr_c2_P0_cons_ne dtr_c2_nat_le_len_id
  dtr_c2_perm_refl dtr_c2_sorted_wit_002 dtr_c2_phase_dev_wit_true
  dtr_c2_Hadj_pinf_le_P0_wit dtr_c2_Qle_0_1 dtr_c2_Qle_01_bounds
  dtr_c2_Qle_0_of_nat_pos dtr_c2_P0_wit_012_eq dtr_c2_Hadj_phase_eq_wit
  dtr_c2_Qle_bool_Hadj_wit_false dtr_c2_H_adj_rotc_ub3_P0cons
  dtr_c2_Hsup_cyc_ub_P0cons dtr_c2_hs_skipn_app_le_len
  dtr_c2_hs_firstn_app_le_len dtr_c2_hs_skipn_app_r_len
  dtr_c2_rotc_add_local_wit dtr_c2_qmax2_le_refl
  dtr_c2_Hsup_cyc_mono_from_0 dtr_c2_Hsup_cyc_step_frozen_len
  dtr_c2_Hsup_cyc_stable_wit dtr_c2_rs_le_double_nat
  dtr_c2_rotc_periodic_len dtr_c2_rs_lastq_cons_ne_cons
  dtr_c2_rs_lastq_firstn_hd_skipn_cons2 dtr_c2_rs_skipn_S_incl_cons2
  dtr_c2_rs_seam_order_wit dtr_c2_rotc_class_sharp_ub_P0cons
  dtr_c2_phcyc_min_perm_refl dtr_c2_phase_dev_le_wit
  dtr_c2_phcyc_qle_false_lt_wit dtr_c2_phase_dev_stable_wit
  dtr_c2_phase_dev_0_of_sorted_wit dtr_c2_H_lam_anti_mono_01
  dtr_c2_H_lam_mono_diff_wit dtr_c2_H_lam_const_when_eq_wit
  dtr_c2_lam_opt_min_0 dtr_c2_H_lam_lam_opt_min_0
  dtr_c2_lam_opt_min_align_0.
