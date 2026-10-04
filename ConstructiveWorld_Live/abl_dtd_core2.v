(* ==========================================================================
   abl_dtd_core2.v —— DTPT 本体前件参数消解供给·卷二（参数 36–70）。
   ── 使命：宿主 DTPT.v 前件参数登记序第 36–70 位（语句坐标 :587–:1612，
   27 条语句 35 参数，与卷一卷界零重叠）逐参数按形态二 T＋P′ 消解供给：
   T＝参数面产路（卫哨构造子／置换构造子／成员迁移复合），P′＝宿主结论面
   现档逐字特化（全实参显式应用，参数消即出）。35 参数＝34 供给＋1 登记
   （q_fact_rate_exists，存在体嵌套面误计，实测零顶层前件）；三参数
   D8_tends_zero／perm3_cases／n9_separation_exact 源结论面含 Prop 位，以
   T 产路单独交付（红线二禁入本件语句面）。宿主件零字节动零级联。
   ── 依赖：DTPT（本卷全部参数语句与产路出处均在 DTPT 模块内）＋stdlib
   （QArith.QArith／Qabs、List、Permutation、Lia、Extraction）。
   ── 对标行：T＋P′ 形态二先例＝abl_tbn_supply_b；rev 形置换产路出处＝
   stdlib Permutation_rev＋宿主 cgen_rev_cons_ne；Qlt 产路出处＝宿主
   D8_sorted_frac_pos 定义性配方（stdlib 无 Qlt_bool 判定面）。
   ── 构造性注记：零承认式声明、零悬置前提、零经典逻辑，全部结论 Qed 真构造
   闭合；P′ 语句面零新增 Prop 逻辑词（无裸 exists／无 iff／无 -> False／无
   sumbool 位）；<> 全件仅 dtd_c2_cons_neq_nil／dtd_c2_rev_cons_ne 两处＝
   NEQ 参数面逐字透传（非自造）；名面全 dtd_c2_ 前缀；尾置逐件 Print
   Assumptions Closed＋定理桶单条 Separate Extraction，Obj.magic 零判据。
   ── 编译配方：池 cwd＝沙箱/现役/abl_r85_supply_pool；source Live 库根
   toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 后 nice -19
   rocq c -native-compiler no
   -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
   abl_dtd_core2.v；绿判＝EXIT=0／日志零 Error／.vo 头 8 字节
   436f7121 00015ff4／.vo 新于 .v；第五证 rocq check；产物只落本池。
   ========================================================================== *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

Require DTPT.
Import DTPT.DTPT.

(* ============================================================ *)
(* §一 共用卫哨/证书产路区（供给定理 T·14 枚）                     *)
(*    逐枚＝底册参数面的构造性产路：SortedQ P0 规范形产路、NEQ cons   *)
(*    判别产路、NAT/Z 层平凡卫哨产路、Qlt 规范正分数族产路、置换    *)
(*    构造子路（sym/rev/witness/refl）、逐对界卫哨产路。           *)
(* ============================================================ *)

(* 〔SORTED 产路·供 :587/:652/:666/:1058/:1069 五参数〕P0 规范形恒有序：
   xq_P0_sorted 在役产路转发（普查「SortedQ 有产路（xq_P0_sorted/P0_sorted）」锚；
   本件 DTPT 模块单依赖，副本归属即宿主本尊，检验件实拍名面解析；
   平凡转发位申报见交付报告） *)
Theorem dtd_c2_sorted_P0 : forall l : list Q, SortedQ (P0 l).
Proof.
  intro l. exact (xq_P0_sorted l).
Qed.

(* 〔NEQ 非空卫哨产路·供 :630/:639/:1137 三参数〕cons 形：
   x :: l <> [] 头构造判别（卫哨 cons 构造子路；普查「卫哨可平凡供给」锚；
   <> 系 NEQ 参数面逐字， 同款任务指定透传形） *)
Theorem dtd_c2_cons_neq_nil : forall (x : Q) (l : list Q), (x :: l) <> [].
Proof.
  intros x l H. discriminate H.
Qed.

(* 〔NAT 严格正卫哨产路·供 :776/:1504 两参数〕后继形：(0 < S k) 的
   nat 层平凡产路（普查「卫哨可平凡供给」锚；平凡位申报见交付报告） *)
Theorem dtd_c2_nat_lt_succ : forall k : nat, (0 < S k)%nat.
Proof.
  intro k. lia.
Qed.

(* 〔Q-ORD 严格序产路·供 :790 参数〕规范正分数族：0 < (1 # p) 的
   定义性产路（stdlib 无 Qlt_bool 判定面——检验件实测 QArith_base 仅
   Qle_bool；本路走宿主 D8_sorted_frac_pos :786 同款 unfold Qlt/simpl/lia
   定义性配方，eps 规范实例族 1/p） *)
Theorem dtd_c2_Qlt_pos_num : forall p : positive, (0 < (1 # p)%Q).
Proof.
  intro p. unfold Qlt. simpl. lia.
Qed.

(* 〔PERM 产路·供 :960 参数〕置换对称构造子路：Permutation p l ⟹
   Permutation l p（stdlib Permutation_sym 构造子一击，普查
   「Permutation 有构造子」锚；  dtb_perm_sym_route 同款产路） *)
Theorem dtd_c2_perm_sym : forall l p : list Q,
  Permutation p l -> Permutation l p.
Proof.
  intros l p Hperm. exact (Permutation_sym Hperm).
Qed.

(* 〔PAIRBOUND 逐对界卫哨产路·供 :1137 参数 2〕spread 面逐对界：
   全表任意两元 Qabs 距离不超过 spread（宿主 spread_pair_le 全参转发，
   :1137 参数 2 (forall x y, In x m -> In y m -> Qabs (x - y) <= k) 于
   k := spread m 的规范实例） *)
Theorem dtd_c2_pair_spread : forall (m : list Q) (x y : Q),
  In x m -> In y m -> (Qabs (x - y) <= spread m)%Q.
Proof.
  intros m x y Hx Hy. exact (spread_pair_le m x y Hx Hy).
Qed.

(* 〔PERM concrete 产路·供 :1175 参数〕长度 3 置换类构造子复合：
   Permutation [a; b; c] [a; c; b]（perm_skip＋perm_swap 两步构造，
   普查「Permutation 有构造子」锚的非平凡具例；宿主 n9_max_attained
   同款构造链） *)
Theorem dtd_c2_perm3_swap : forall a b c : Q, Permutation [a; b; c] [a; c; b].
Proof.
  intros a b c. apply perm_skip. apply perm_swap.
Qed.

(* 〔PERM witness 产路·供 :1287/:1326 两参数〕n9 见证列极大置换：
   Permutation n9_l0 [0; 2; 1]（perm_skip＋perm_swap 构造；即宿主
   n9_max_attained 紧性见证的裸数据面——宿主面为存在合取位，本件
   供其置换分量为可喂数据义务） *)
Theorem dtd_c2_n9_perm_max_wit : Permutation n9_l0 [0; 2; 1].
Proof.
  unfold n9_l0. apply perm_skip. apply perm_swap.
Qed.

(* 〔PERM refl 产路·供 :1301 参数〕n9 见证列自反置换：
   Permutation n9_l0 n9_l0（Permutation_refl 构造子；最小值在有序形
   自身取得的规范实例；平凡位申报见交付报告） *)
Theorem dtd_c2_n9_perm_refl : Permutation n9_l0 n9_l0.
Proof.
  apply Permutation_refl.
Qed.

(* 〔PERM rev 产路·供 :1342/:1360 两参数〕反转置换构造子路：
   Permutation l (rev l)（stdlib Permutation_rev 构造子转发——
   :1342/:1360 双参数 P′ rev 形的置换输入源） *)
Theorem dtd_c2_perm_rev : forall l : list Q, Permutation l (rev l).
Proof.
  intro l. apply Permutation_rev.
Qed.

(* 〔NEQ rev 非空卫哨产路·供 :1342/:1360 两参数〕cons 表反转必非空：
   rev (x :: xs) <> []（宿主 cgen_rev_cons_ne 全参转发；<> 系 NEQ
   参数面逐字， 同款任务指定透传形） *)
Theorem dtd_c2_rev_cons_ne : forall (x : Q) (xs : list Q), rev (x :: xs) <> [].
Proof.
  intros x xs. exact (cgen_rev_cons_ne x xs).
Qed.

(* 〔NAT 下界卫哨产路·供 :1464/:1480 两参数〕零下界：(0 <= k) 的
   nat 层平凡产路（普查「卫哨可平凡供给」锚；平凡位申报见交付报告） *)
Theorem dtd_c2_nat_le_0 : forall k : nat, (0 <= k)%nat.
Proof.
  intro k. lia.
Qed.

(* 〔Z 层正性卫哨产路·供 :1521 参数 1〕S 映像恒正：(0 < Z.of_nat (S n))
   的 Z 层产路（Znat.Nat2Z.inj_lt proj1 方向 nat→Z——检验件实测过签；
   先 nat 层 lia 后升 Z） *)
Theorem dtd_c2_Zpos_of_S : forall n : nat, (0 < Z.of_nat (S n))%Z.
Proof.
  intro n. apply (proj1 (Znat.Nat2Z.inj_lt 0 (S n))). lia.
Qed.

(* 〔NAT 阶乘自变元卫哨产路·供 :1601 参数〕四后继形：(4 <= S(S(S(S n))))
   的 nat 层产路（:1601 参数 (4 <= k)%nat 于 k := S(S(S(S n))) 规范实例；
   平凡位申报见交付报告） *)
Theorem dtd_c2_nat_ge4_S4 : forall n : nat, (4 <= S (S (S (S n))))%nat.
Proof.
  intro n. lia.
Qed.

(* ============================================================ *)
(* §二 P′ 无前提精简版区（23 枚·覆盖 31 参数）                       *)
(*    逐枚＝宿主定理 @ 全实参显式应用＋参数由 §一 产路（或 In/自反构造子    *)
(*    内联构造）输入，出无前提精简版；语句面＝宿主结论面现档逐字    *)
(*    特化（离散承载）。三参数 P′ （:790/:1175/:1326，见④）。     *)
(* ============================================================ *)

(* P1〔:587 xq_sortQ_insert 参数〕插入保序 P0 规范形无前提精简版：
   SortedQ 参数喂 dtd_c2_sorted_P0，出 insert_q 保序于已序 P0 面 *)
Theorem dtd_c2_xq_sortQ_insert_P0 : forall (x : Q) (l : list Q),
  SortedQ (insert_q x (P0 l)).
Proof.
  intros x l. exact (xq_sortQ_insert x (P0 l) (dtd_c2_sorted_P0 l)).
Qed.

(* P2〔:630 xq_lastq_In 参数〕尾元成员 cons 形无前提精简版：
   非空卫哨参数喂 dtd_c2_cons_neq_nil，出 In (lastq (x :: l)) (x :: l) 面 *)
Theorem dtd_c2_xq_lastq_In_cons : forall (x : Q) (l : list Q),
  In (lastq (x :: l)) (x :: l).
Proof.
  intros x l. exact (xq_lastq_In (x :: l) (dtd_c2_cons_neq_nil x l)).
Qed.

(* P3〔:639 xq_hd_In_gen 参数〕头元成员 cons 形无前提精简版：
   非空卫哨参数喂 dtd_c2_cons_neq_nil，出 In (hd 0 (x :: l)) (x :: l) 面 *)
Theorem dtd_c2_xq_hd_In_gen_cons : forall (x : Q) (l : list Q),
  In (hd 0 (x :: l)) (x :: l).
Proof.
  intros x l. exact (xq_hd_In_gen (x :: l) (dtd_c2_cons_neq_nil x l)).
Qed.

(* P4〔:652 xq_hd_le_lastq 参数〕首尾序 P0 规范形无前提精简版：
   SortedQ 参数喂 dtd_c2_sorted_P0，出 hd 0 (P0 l) <= lastq (P0 l) 面 *)
Theorem dtd_c2_xq_hd_le_lastq_P0 : forall l : list Q,
  (hd 0 (P0 l) <= lastq (P0 l))%Q.
Proof.
  intro l. exact (xq_hd_le_lastq (P0 l) (dtd_c2_sorted_P0 l)).
Qed.

(* P5〔:666 xq_telescope 参数〕望远镜方程 P0 规范形无前提精简版：
   SortedQ 参数喂 dtd_c2_sorted_P0，出 H_adj (P0 l) == lastq - hd 面 *)
Theorem dtd_c2_xq_telescope_P0 : forall l : list Q,
  H_adj (P0 l) == lastq (P0 l) - hd 0 (P0 l).
Proof.
  intro l. exact (xq_telescope (P0 l) (dtd_c2_sorted_P0 l)).
Qed.

(* P6〔:688 xq_pair_dist_le 双参数〕配对距离界双 In cons 形无前提精简版：
   双成员参数以 In-cons 头/次位构造子内联输入（开析方向检验实测：
   头位 left 自反、次位 right-left），出 Qabs (x - y) <= H_adj 面 *)
Theorem dtd_c2_xq_pair_dist_le_cons_cons : forall (x y : Q) (l : list Q),
  (Qabs (x - y) <= H_adj (x :: y :: l))%Q.
Proof.
  intros x y l.
  apply (xq_pair_dist_le (x :: y :: l) x y).
  - simpl. left. reflexivity.
  - simpl. right. left. reflexivity.
Qed.

(* P7〔:776 D8_sorted_frac_pos 参数〕计数倒数正性后继形无前提精简版：
   NAT 参数喂 dtd_c2_nat_lt_succ，出 0 < 1/(q_fact (S k)) 面 *)
Theorem dtd_c2_D8_sorted_frac_pos_S : forall k : nat,
  0 < (1 / (q_fact (S k)))%Q.
Proof.
  intro k. exact (D8_sorted_frac_pos (S k) (dtd_c2_nat_lt_succ k)).
Qed.

(* P8〔:904 cgen_H_adj_snoc 参数〕snoc 熵方程 cons 形无前提精简版：
   非空卫哨参数喂 dtd_c2_cons_neq_nil，出 snoc 相邻差总和恰增面 *)
Theorem dtd_c2_cgen_H_adj_snoc_cons : forall (y x : Q) (l : list Q),
  H_adj ((y :: l) ++ [x]) == (H_adj (y :: l) + Qabs (x - lastq (y :: l)))%Q.
Proof.
  intros y x l.
  exact (cgen_H_adj_snoc (y :: l) x (dtd_c2_cons_neq_nil y l)).
Qed.

(* P9〔:960 C_gen 参数〕定理 C 全排列类泛化对称面精简版：
   PERM 参数经 dtd_c2_perm_sym 换向后喂宿主，出 H_adj (P0 l) <= H_adj p
   面（宿主结论面现档逐字；离散 Qle 承载——  dtb_C_gen_sym 供
   Bridge :103 之 QleT 型面，本件供 DTPT :960 之本面，承载异层防撞） *)
Theorem dtd_c2_C_gen_sym : forall l p : list Q,
  Permutation p l -> (H_adj (P0 l) <= H_adj p)%Q.
Proof.
  intros l p Hperm. exact (C_gen l p (dtd_c2_perm_sym l p Hperm)).
Qed.

(* P10〔:1058 sorted_hd_le_in 双参数〕有序表头最小 P0 迁移形无前提精简版：
   SortedQ 参数喂 dtd_c2_sorted_P0、In 参数经 D5_P0_perm 置换传递＋
   In-cons 头构造复合输入，出 hd 0 (P0 (x :: l)) <= x 面（头最小性
   规范实例） *)
Theorem dtd_c2_sorted_hd_le_in_min : forall (x : Q) (l : list Q),
  (hd 0 (P0 (x :: l)) <= x)%Q.
Proof.
  intros x l.
  apply (sorted_hd_le_in (P0 (x :: l)) x).
  - exact (xq_P0_sorted (x :: l)).
  - apply Permutation_in with (l := x :: l).
    + apply D5_P0_perm.
    + simpl. left. reflexivity.
Qed.

(* P11〔:1069 sorted_in_le_last 双参数〕有序表尾最大 P0 迁移形无前提
   精简版：同 P10 配方，出 x <= lastq (P0 (x :: l)) 面（尾最大性
   规范实例） *)
Theorem dtd_c2_sorted_in_le_last_max : forall (x : Q) (l : list Q),
  (x <= lastq (P0 (x :: l)))%Q.
Proof.
  intros x l.
  apply (sorted_in_le_last (P0 (x :: l)) x).
  - exact (xq_P0_sorted (x :: l)).
  - apply Permutation_in with (l := x :: l).
    + apply D5_P0_perm.
    + simpl. left. reflexivity.
Qed.

(* P12〔:1088 spread_pair_le 双参数〕spread 两两界双 In cons 形无前提
   精简版：双成员参数以 In-cons 头/次位构造子内联输入，出
   Qabs (x - y) <= spread (x :: y :: l) 面 *)
Theorem dtd_c2_spread_pair_le_cons_cons : forall (x y : Q) (l : list Q),
  (Qabs (x - y) <= spread (x :: y :: l))%Q.
Proof.
  intros x y l.
  apply (spread_pair_le (x :: y :: l) x y).
  - simpl. left. reflexivity.
  - simpl. right. left. reflexivity.
Qed.

(* P13〔:1137 H_adj_pair_bound 双参数〕相邻差总和两两界放大 cons 形
   无前提精简版：非空卫哨参数喂 dtd_c2_cons_neq_nil、逐对界参数于
   k := spread 喂 dtd_c2_pair_spread，出 H_adj 两两界放大面 *)
Theorem dtd_c2_H_adj_pair_bound_cons_spread : forall (x y : Q) (l : list Q),
  H_adj (x :: y :: l)
  <= ((Z.of_nat (length (x :: y :: l)) - 1)%Z # 1) * spread (x :: y :: l).
Proof.
  intros x y l.
  exact (H_adj_pair_bound (x :: y :: l) (spread (x :: y :: l))
           (dtd_c2_cons_neq_nil x (y :: l))
           (dtd_c2_pair_spread (x :: y :: l))).
Qed.

(* P14〔:1287 n9_max 参数〕n9 类上极值见证形无前提精简版：
   PERM 参数喂 dtd_c2_n9_perm_max_wit，出 H_adj [0; 2; 1] <= 3 面 *)
Theorem dtd_c2_n9_max_wit : (H_adj [0; 2; 1] <= 3)%Q.
Proof.
  exact (n9_max [0; 2; 1] dtd_c2_n9_perm_max_wit).
Qed.

(* P15〔:1301 n9_min_is_sorted 参数〕n9 类下极值自反形无前提精简版：
   PERM 参数喂 dtd_c2_n9_perm_refl，出 2 <= H_adj n9_l0 面（最小值于
   有序规范形取得） *)
Theorem dtd_c2_n9_min_is_sorted_refl : (2 <= H_adj n9_l0)%Q.
Proof.
  exact (n9_min_is_sorted n9_l0 dtd_c2_n9_perm_refl).
Qed.

(* P16〔:1342 n9_naive_bound 双参数〕朴素上界 spread 面 rev 形无前提
   精简版：PERM 参数喂 dtd_c2_perm_rev、非空卫哨参数喂 dtd_c2_rev_cons_ne，
   出 H_adj (rev (a :: t)) <= (n-1)·spread l 面（rev 实例避开 p := l
   自反形与本卷 P13 面重合） *)
Theorem dtd_c2_n9_naive_bound_rev : forall (a : Q) (t : list Q),
  H_adj (rev (a :: t))
  <= ((Z.of_nat (length (a :: t)) - 1)%Z # 1) * spread (a :: t).
Proof.
  intros a t.
  exact (n9_naive_bound (a :: t) (rev (a :: t))
           (dtd_c2_perm_rev (a :: t)) (dtd_c2_rev_cons_ne a t)).
Qed.

(* P17〔:1360 n9_naive_bound_Hadj 双参数〕朴素上界 H_adj 面 rev 形
   无前提精简版：同 P16 配方，出 H_adj 面（源结论面现档逐字特化） *)
Theorem dtd_c2_n9_naive_bound_Hadj_rev : forall (a : Q) (t : list Q),
  H_adj (rev (a :: t))
  <= ((Z.of_nat (length (a :: t)) - 1)%Z # 1) * H_adj (a :: t).
Proof.
  intros a t.
  exact (n9_naive_bound_Hadj (a :: t) (rev (a :: t))
           (dtd_c2_perm_rev (a :: t)) (dtd_c2_rev_cons_ne a t)).
Qed.

(* P18〔:1464 nat_fact_mono 参数〕阶乘单调零起形无前提精简版：
   NAT 参数喂 dtd_c2_nat_le_0，出 nat_fact 0 <= nat_fact k 面 *)
Theorem dtd_c2_nat_fact_mono_0 : forall k : nat,
  (nat_fact 0 <= nat_fact k)%nat.
Proof.
  intro k. exact (nat_fact_mono 0 k (dtd_c2_nat_le_0 k)).
Qed.

(* P19〔:1480 nat_fact_le_Z 参数〕阶乘单调 Z 升面零起形无前提精简版：
   NAT 参数喂 dtd_c2_nat_le_0，出 Z 层单调面 *)
Theorem dtd_c2_nat_fact_le_Z_0 : forall k : nat,
  (Z.of_nat (nat_fact 0) <= Z.of_nat (nat_fact k))%Z.
Proof.
  intro k. exact (nat_fact_le_Z 0 k (dtd_c2_nat_le_0 k)).
Qed.

(* P20〔:1490 q_fact_recip_anti 参数〕倒数反单调零起形无前提精简版：
   NAT 参数喂 dtd_c2_nat_le_0，出 1/k! <= 1/0! = 1 面 *)
Theorem dtd_c2_q_fact_recip_anti_0 : forall k' : nat,
  (1 / q_fact k' <= 1 / q_fact 0)%Q.
Proof.
  intro k'. exact (q_fact_recip_anti 0 k' (dtd_c2_nat_le_0 k')).
Qed.

(* P21〔:1504 D8_mono 参数〕后继倒数不增后继形无前提精简版：
   NAT 参数喂 dtd_c2_nat_lt_succ（K := S k），出移位一位倒数不增面 *)
Theorem dtd_c2_D8_mono_S : forall k : nat,
  (1 / q_fact (S (S k)) <= 1 / q_fact (S k))%Q.
Proof.
  intro k. exact (D8_mono (S k) (dtd_c2_nat_lt_succ k)).
Qed.

(* P22〔:1521 q_recip_step_Z 双参数〕核心步双 Z 卫哨后继形无前提精简版：
   参数 1 喂 dtd_c2_Zpos_of_S、参数 2 以 Z.le_refl 自反构造子内联输入
   （a := 2·b 规范实例），出 2/(2b) <= 1/b 面 *)
Theorem dtd_c2_q_recip_step_Z_double : forall n : nat,
  (2 / ((2 * Z.of_nat (S n)) # 1) <= 1 / (Z.of_nat (S n) # 1))%Q.
Proof.
  intro n.
  apply (q_recip_step_Z (2 * Z.of_nat (S n)) (Z.of_nat (S n))).
  - exact (dtd_c2_Zpos_of_S n).
  - apply Z.le_refl.
Qed.

(* P23〔:1601 q_fact_rate 参数〕收敛率四后继形无前提精简版：
   NAT 参数喂 dtd_c2_nat_ge4_S4，出 1/k!·4 < 1 面（k >= 4 规范族） *)
Theorem dtd_c2_q_fact_rate_S4 : forall n : nat,
  (1 / q_fact (S (S (S (S n)))) * 4 < 1)%Q.
Proof.
  intro n.
  apply (q_fact_rate (S (S (S (S n))))).
  exact (dtd_c2_nat_ge4_S4 n).
Qed.

(* ============================================================ *)
(* §三 尾置验印区（文件最尾）：Check 印＋逐件承认面验印，          *)
(*     名清单=供给定理数=37 零差（14 T＋23 P′）                    *)
(* ============================================================ *)

Check dtd_c2_sorted_P0.
Check dtd_c2_cons_neq_nil.
Check dtd_c2_nat_lt_succ.
Check dtd_c2_Qlt_pos_num.
Check dtd_c2_perm_sym.
Check dtd_c2_pair_spread.
Check dtd_c2_perm3_swap.
Check dtd_c2_n9_perm_max_wit.
Check dtd_c2_n9_perm_refl.
Check dtd_c2_perm_rev.
Check dtd_c2_rev_cons_ne.
Check dtd_c2_nat_le_0.
Check dtd_c2_Zpos_of_S.
Check dtd_c2_nat_ge4_S4.
Check dtd_c2_xq_sortQ_insert_P0.
Check dtd_c2_xq_lastq_In_cons.
Check dtd_c2_xq_hd_In_gen_cons.
Check dtd_c2_xq_hd_le_lastq_P0.
Check dtd_c2_xq_telescope_P0.
Check dtd_c2_xq_pair_dist_le_cons_cons.
Check dtd_c2_D8_sorted_frac_pos_S.
Check dtd_c2_cgen_H_adj_snoc_cons.
Check dtd_c2_C_gen_sym.
Check dtd_c2_sorted_hd_le_in_min.
Check dtd_c2_sorted_in_le_last_max.
Check dtd_c2_spread_pair_le_cons_cons.
Check dtd_c2_H_adj_pair_bound_cons_spread.
Check dtd_c2_n9_max_wit.
Check dtd_c2_n9_min_is_sorted_refl.
Check dtd_c2_n9_naive_bound_rev.
Check dtd_c2_n9_naive_bound_Hadj_rev.
Check dtd_c2_nat_fact_mono_0.
Check dtd_c2_nat_fact_le_Z_0.
Check dtd_c2_q_fact_recip_anti_0.
Check dtd_c2_D8_mono_S.
Check dtd_c2_q_recip_step_Z_double.
Check dtd_c2_q_fact_rate_S4.

Print Assumptions dtd_c2_sorted_P0.
Print Assumptions dtd_c2_cons_neq_nil.
Print Assumptions dtd_c2_nat_lt_succ.
Print Assumptions dtd_c2_Qlt_pos_num.
Print Assumptions dtd_c2_perm_sym.
Print Assumptions dtd_c2_pair_spread.
Print Assumptions dtd_c2_perm3_swap.
Print Assumptions dtd_c2_n9_perm_max_wit.
Print Assumptions dtd_c2_n9_perm_refl.
Print Assumptions dtd_c2_perm_rev.
Print Assumptions dtd_c2_rev_cons_ne.
Print Assumptions dtd_c2_nat_le_0.
Print Assumptions dtd_c2_Zpos_of_S.
Print Assumptions dtd_c2_nat_ge4_S4.
Print Assumptions dtd_c2_xq_sortQ_insert_P0.
Print Assumptions dtd_c2_xq_lastq_In_cons.
Print Assumptions dtd_c2_xq_hd_In_gen_cons.
Print Assumptions dtd_c2_xq_hd_le_lastq_P0.
Print Assumptions dtd_c2_xq_telescope_P0.
Print Assumptions dtd_c2_xq_pair_dist_le_cons_cons.
Print Assumptions dtd_c2_D8_sorted_frac_pos_S.
Print Assumptions dtd_c2_cgen_H_adj_snoc_cons.
Print Assumptions dtd_c2_C_gen_sym.
Print Assumptions dtd_c2_sorted_hd_le_in_min.
Print Assumptions dtd_c2_sorted_in_le_last_max.
Print Assumptions dtd_c2_spread_pair_le_cons_cons.
Print Assumptions dtd_c2_H_adj_pair_bound_cons_spread.
Print Assumptions dtd_c2_n9_max_wit.
Print Assumptions dtd_c2_n9_min_is_sorted_refl.
Print Assumptions dtd_c2_n9_naive_bound_rev.
Print Assumptions dtd_c2_n9_naive_bound_Hadj_rev.
Print Assumptions dtd_c2_nat_fact_mono_0.
Print Assumptions dtd_c2_nat_fact_le_Z_0.
Print Assumptions dtd_c2_q_fact_recip_anti_0.
Print Assumptions dtd_c2_D8_mono_S.
Print Assumptions dtd_c2_q_recip_step_Z_double.
Print Assumptions dtd_c2_q_fact_rate_S4.

(* ── 提取检验区（G3 归桶： 专属桶，Separate Extraction
     逐件 .ml，Obj.magic 逐文件计数归因登记于交付报告） ── *)
Set Extraction Output Directory "_log/dtd_t3".
Separate Extraction dtd_c2_sorted_P0
  dtd_c2_cons_neq_nil dtd_c2_nat_lt_succ dtd_c2_Qlt_pos_num
  dtd_c2_perm_sym dtd_c2_pair_spread dtd_c2_perm3_swap
  dtd_c2_n9_perm_max_wit dtd_c2_n9_perm_refl dtd_c2_perm_rev
  dtd_c2_rev_cons_ne dtd_c2_nat_le_0 dtd_c2_Zpos_of_S
  dtd_c2_nat_ge4_S4 dtd_c2_xq_sortQ_insert_P0 dtd_c2_xq_lastq_In_cons
  dtd_c2_xq_hd_In_gen_cons dtd_c2_xq_hd_le_lastq_P0
  dtd_c2_xq_telescope_P0 dtd_c2_xq_pair_dist_le_cons_cons
  dtd_c2_D8_sorted_frac_pos_S dtd_c2_cgen_H_adj_snoc_cons
  dtd_c2_C_gen_sym dtd_c2_sorted_hd_le_in_min
  dtd_c2_sorted_in_le_last_max dtd_c2_spread_pair_le_cons_cons
  dtd_c2_H_adj_pair_bound_cons_spread dtd_c2_n9_max_wit
  dtd_c2_n9_min_is_sorted_refl dtd_c2_n9_naive_bound_rev
  dtd_c2_n9_naive_bound_Hadj_rev dtd_c2_nat_fact_mono_0
  dtd_c2_nat_fact_le_Z_0 dtd_c2_q_fact_recip_anti_0 dtd_c2_D8_mono_S
  dtd_c2_q_recip_step_Z_double dtd_c2_q_fact_rate_S4.
