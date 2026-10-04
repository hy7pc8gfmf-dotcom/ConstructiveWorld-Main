(* ==========================================================================
   abl_dte_core3.v —— DTPT_Entropy 前件参数消解供给·卷三（参数 77–114）。
   ── 使命：宿主 DTPT_Entropy.v 前件参数登记序第 77–114 位（语句坐标
   :1410–:2012，30 条语句；末位语句 H_max_q_all_same_zero 双参数整条供给，
   参数 115 随条溢出在本卷交付并如实登记，下卷禁重复供给）逐参数按形态二
   T＋P′ 消解供给，卷内三区：A 直供 1 枚（record-crunch 配方就地构造零宿主
   定理使用）；T 参数面产路 6 枚（Qeq 非规范同值对／Qlt 严格序实例／Qle 序
   实例／all_same 双元见证／长度正性／maxfreq 跨值序）；P′ 无前提精简版
   30 枚（含 H_chain 源结论面 Prop 三重合取位拆分三单向规避）。登记序 38 参数
   ＝36 供给＋2 登记（qdiv_norm 双否定卫哨旗，照登记不供给）。37 定理全
   Qed 真构造闭合；宿主件零字节动零级联。
   ── 依赖：DTPT（qadd_le／qopp_le／Qle_0_sub' 等基础模块面）、
   DTPT_Entropy（本卷全部参数语句本体与 qn／nsum／nmax／freq_q／sqsum／
   collide／maxfreq／H_freq 定义面）＋stdlib（QArith.QArith／Qabs、List、
   Permutation、Arith、Lia、Extraction）。
   ── 对标行：A 直供 record-crunch 配方先例＝abl_dte_core1；合取位拆分
   先例＝abl_dte_core1（H_lam_cross_phase_bounds 同族工艺）。
   ── 构造性注记：零承认式声明、零悬置前提、零经典逻辑、零节变量声明位；
   供给语句面零混载形态（零裸 exists／零否定／零等价／零析取位）；<>
   全件语句面零出现；名面全 dte_／dte_c3_ 前缀（与 dte_c1_／dte_c2_ 中缀
   隔离）；尾置逐件 Print Assumptions Closed＋定理桶单条 Separate
   Extraction，Obj.magic 零判据。
   ── 编译配方：池 cwd＝沙箱/现役/abl_r85_supply_pool；source Live 库根
   toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 后 nice -19
   rocq c -native-compiler no
   -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
   abl_dte_core3.v；绿判＝EXIT=0／日志零 Error／.vo 头 8 字节
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
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.

(* ============================================================ *)
(* 一 供给定理区·卷一 A 直供形（1 枚；参数 86；语句面＝底册参数面现档       *)
(*    逐字经 dte_ 前缀映射，证明体 就地构造 真构造——  A10      *)
(*    配方 record-crunch，零宿主定理使用）                             *)
(* ============================================================ *)

(* A1〔参数 86·:1580 qeq_le_l 逐字〕Qeq 等值弱序化（record-crunch 就地构造） *)
Theorem dte_c3_qeq_le_l : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy] Hxy. unfold Qeq in Hxy; simpl in Hxy.
  unfold Qle; simpl. lia.
Qed.

(* ============================================================ *)
(* 二 供给定理区·卷二 T 参数面产路（6 枚共用；Qeq 非规范同值对／Qlt        *)
(*    严格序宿主定义性配方／Qle 序实例／all_same 双元见证／   *)
(*    长度正性泛产路／maxfreq 跨值序产路）                              *)
(* ============================================================ *)

(* 〔Qeq 非规范同值对·供参数 77/90/96 卫哨链〕(1#1)==(2#2) 值层闭合对
   （   dte_c1_Qeq_half 配方同族，非退化反射面） *)
Theorem dte_c3_Qeq_pair : ((1 # 1) == (2 # 2))%Q.
Proof.
  reflexivity.
Qed.

(* 〔Qlt 严格序实例·供参数 90/92 卫哨〕0 < (3#2)（stdlib Qlt_bool 整体
   缺位，走  宿主定义性配方 unfold Qlt; simpl; lia） *)
Theorem dte_c3_Qlt_3_2 : (0 < (3 # 2))%Q.
Proof.
  unfold Qlt. simpl. lia.
Qed.

(* 〔Qle 序实例·供参数 92 卫哨〕(2#2) <= (3#2) 非规范真序对 *)
Theorem dte_c3_Qle_2_2_3_2 : ((2 # 2) <= (3 # 2))%Q.
Proof.
  unfold Qle. simpl. lia.
Qed.

(* 〔all_same 双元见证·供参数 106-107/114-115 卫哨〕all_same 系宿主
   本地谓词（:1195 定义面 forall a b, In a l -> In b l -> a == b），
   于非规范全同值对 [(1#1);(2#2)] 构造见证（成员构造子四分支枚举闭合） *)
Theorem dte_c3_all_same_pair : all_same [(1 # 1); (2 # 2)].
Proof.
  intros a b Ha Hb.
  simpl in Ha, Hb.
  destruct Ha as [Ha | [Ha | Ha]]; destruct Hb as [Hb | [Hb | Hb]];
    subst; try reflexivity; contradiction.
Qed.

(* 〔长度正性泛产路·供参数 103/105/106-107/112/113/114-115 卫哨〕
   双元表长度正性（宿主 qlen_pos 同款 nat 侧配方，泛化双参） *)
Theorem dte_c3_len2_pos : forall a b : Q, (0 < length [a; b])%nat.
Proof.
  intros a b. simpl. lia.
Qed.

(* 〔maxfreq 跨值序产路·供参数 111 卫哨〕异值表 maxfreq <= 全同值表
   maxfreq（宿主 maxfreq_upper 上界＋maxfreq_all_same_one 全同值取 1
   ＋A1 qeq_le_l 序桥三段组合） *)
Theorem dte_c3_maxfreq_distinct_le_eq :
  (maxfreq [(1 # 2); (1 # 3)] <= maxfreq [(1 # 1); (2 # 2)])%Q.
Proof.
  assert (Hr : maxfreq [(1 # 1); (2 # 2)] == 1).
  { exact (maxfreq_all_same_one [(1 # 1); (2 # 2)] dte_c3_all_same_pair
             (dte_c3_len2_pos (1 # 1) (2 # 2))). }
  apply (Qle_trans (maxfreq [(1 # 2); (1 # 3)]) 1 (maxfreq [(1 # 1); (2 # 2)])).
  - apply maxfreq_upper.
  - apply (dte_c3_qeq_le_l 1 (maxfreq [(1 # 1); (2 # 2)])).
    exact (Qeq_sym 1 (maxfreq [(1 # 1); (2 # 2)]) Hr).
Qed.

(* ============================================================ *)
(* 【只登记】参数 94-95＝:1646 qdiv_norm〔底册 NOT+Q-ORD×2〕——底册          *)
(* §2.3 混载旗位（:1646 在册 Entropy 20 条之列：双否定卫哨 ~ 面语句位），  *)
(* 照   :1864／  :749 先例只登记不供给不擅自扩面，失败显式申报 见     *)
(* 交付报告 §四；升级方向＝否定卫。              *)
(* ============================================================ *)

(* ============================================================ *)
(* 三 供给定理区·卷三 P′ 无前提精简版（30 枚；宿主定理 @ 全实参显式应用，       *)
(*    参数消即出；结论面＝宿主结论面现档逐字特化，全离散承载；内含          *)
(*    H_chain 合取位拆分三单向转发 3 枚）                                *)
(* ============================================================ *)

(* P1〔参数 77 P′〕减法右单调：D:=(5#2)、(A,B):=((1#1),(2#2)) 非规范
   同值对喂 A1×，出同值不减实例 *)
Theorem dte_c3_qsub_mono_r_inst :
  ((5 # 2) - (2 # 2) <= (5 # 2) - (1 # 1))%Q.
Proof.
  exact (qsub_mono_r (5 # 2) (1 # 1) (2 # 2)
           (dte_c3_qeq_le_l (1 # 1) (2 # 2) dte_c3_Qeq_pair)).
Qed.

(* P2〔参数 78-79 P′〕碰撞和单调反号：(N,A,B):=(1,0,1)，nat 双卫哨内联
   Nat.le_0_l／le_n 消解，出 qn 核形商序实例 *)
Theorem dte_c3_hfreq_core_anti_1_0_1 :
  ((qn 1 * qn 1 - qn 1) / (qn 1 * qn 1)
   <= (qn 1 * qn 1 - qn 0) / (qn 1 * qn 1))%Q.
Proof.
  exact (hfreq_core_anti 1 0 1 (Nat.le_0_l 1) (le_n 1)).
Qed.

(* P3〔参数 80 P′〕DPI 形态卫哨喂宿主 xq_abs_eq（Qabs 系真形态），
   出绝对值观测不增面 *)
Theorem dte_c3_H_freq_dpi_abs : forall l : list Q,
  (H_freq (map Qabs l) <= H_freq l)%Q.
Proof.
  intro l. exact (H_freq_dpi Qabs xq_abs_eq l).
Qed.

(* P4〔参数 81 P′〕常值映射成员像等值：双元表次位成员 in_cons∘in_eq
   构造消解，出像点等值实例 *)
Theorem dte_c3_in_map_const_mid : ((1 # 2) == (1 # 2))%Q.
Proof.
  exact (in_map_const (1 # 2) [(9 # 7); (4 # 5)] (1 # 2)
           (in_cons (1 # 2) (1 # 2) [(1 # 2)] (in_eq (1 # 2) []))).
Qed.

(* P5〔参数 82-83 P′〕迭代不衰减：双形态卫哨同喂 xq_abs_eq，出二次
   绝对值观测不增面 *)
Theorem dte_c3_H_freq_map_twice_abs : forall l : list Q,
  (H_freq (map Qabs (map Qabs l)) <= H_freq (map Qabs l))%Q.
Proof.
  intro l. exact (H_freq_map_twice Qabs Qabs xq_abs_eq xq_abs_eq l).
Qed.

(* P6〔参数 84-85 P′〕链式不衰减：双形态卫哨同喂 xq_abs_eq，出链式
   绝对值观测直达原表面 *)
Theorem dte_c3_H_freq_map_chain_abs : forall l : list Q,
  (H_freq (map Qabs (map Qabs l)) <= H_freq l)%Q.
Proof.
  intro l. exact (H_freq_map_chain Qabs Qabs xq_abs_eq xq_abs_eq l).
Qed.

(* P7〔参数 87 P′〕qn 下界：n:=2，nat 卫哨内联 le_S∘le_n 消解 *)
Theorem dte_c3_qn_ge1_2 : (1 <= qn 2)%Q.
Proof.
  exact (qn_ge1 2 (le_S 1 1 (le_n 1))).
Qed.

(* P8〔参数 88-89 P′〕qn 乘积正性：(a,b):=(2,3)，内联 Nat.lt_0_succ
   双实例 *)
Theorem dte_c3_qn_mul_pos_2_3 : (0 < qn 2 * qn 3)%Q.
Proof.
  exact (qn_mul_pos 2 3 (Nat.lt_0_succ 1) (Nat.lt_0_succ 2)).
Qed.

(* P9〔参数 90-91 P′〕同分母除法对分子单调：(A,C,B):=((2#2),(1#1),(3#2))，
   0<B 喂 、C<=A 喂 A1× *)
Theorem dte_c3_qdiv_ge_num_inst :
  ((1 # 1) / (3 # 2) <= (2 # 2) / (3 # 2))%Q.
Proof.
  exact (qdiv_ge_num (2 # 2) (1 # 1) (3 # 2) dte_c3_Qlt_3_2
           (dte_c3_qeq_le_l (1 # 1) (2 # 2) dte_c3_Qeq_pair)).
Qed.

(* P10〔参数 92-93 P′〕商不超 1：(A,B):=((2#2),(3#2))，A<=B 喂 、
   0<B 喂  *)
Theorem dte_c3_qdiv_le_1_inst : ((2 # 2) / (3 # 2) <= 1)%Q.
Proof.
  exact (qdiv_le_1 (2 # 2) (3 # 2) dte_c3_Qle_2_2_3_2 dte_c3_Qlt_3_2).
Qed.

(* P11〔参数 96 P′〕减法保序反变：(x,y,z):=((1#1),(2#2),(3#1))，卫哨
   喂 A1× *)
Theorem dte_c3_qsub_le_inst :
  ((3 # 1) - (2 # 2) <= (3 # 1) - (1 # 1))%Q.
Proof.
  exact (qsub_le (1 # 1) (2 # 2) (3 # 1)
           (dte_c3_qeq_le_l (1 # 1) (2 # 2) dte_c3_Qeq_pair)).
Qed.

(* P12〔参数 97 P′〕泛取大逐点界：const-7 函数于双元表次位成员，
   in_cons∘in_eq 构造消解 *)
Theorem dte_c3_nmax_bound_inst :
  (7 <= nmax (fun _ : Q => 7%nat) [(1 # 1); (4 # 5)])%nat.
Proof.
  exact (nmax_bound (fun _ : Q => 7%nat) [(1 # 1); (4 # 5)] (4 # 5)
           (in_cons (1 # 1) (4 # 5) [(4 # 5)] (in_eq (4 # 5) []))).
Qed.

(* P13〔参数 98 P′〕泛取大有界：逐点卫哨 le_n 内联消解 *)
Theorem dte_c3_nmax_le_bound_inst :
  (nmax (fun _ : Q => 7%nat) [(1 # 1); (4 # 5)] <= 7)%nat.
Proof.
  exact (nmax_le_bound (fun _ : Q => 7%nat) [(1 # 1); (4 # 5)] 7
           (fun (x : Q) (_ : In x [(1 # 1); (4 # 5)]) => le_n 7)).
Qed.

(* P14〔参数 99 P′〕泛取大外延：(7, 3+4) 逐点 eq_refl 计算闭合对 *)
Theorem dte_c3_nmax_ext_in_inst :
  nmax (fun _ : Q => 7%nat) [(1 # 1)]
  = nmax (fun _ : Q => (3 + 4)%nat) [(1 # 1)].
Proof.
  exact (nmax_ext_in (fun _ : Q => 7%nat) (fun _ : Q => (3 + 4)%nat)
           [(1 # 1)] (fun (x : Q) (_ : In x [(1 # 1)]) => eq_refl)).
Qed.

(* P15〔参数 100 P′〕泛取大置换不变：非常值判定面 f（Qeq_bool 分支形）
   ＋perm_swap 规范实例 *)
Theorem dte_c3_nmax_perm_inst :
  nmax (fun x : Q => if Qeq_bool x (1 # 1) then 5%nat else 3%nat)
       [(1 # 1); (2 # 1)]
  = nmax (fun x : Q => if Qeq_bool x (1 # 1) then 5%nat else 3%nat)
       [(2 # 1); (1 # 1)].
Proof.
  exact (nmax_perm
           (fun x : Q => if Qeq_bool x (1 # 1) then 5%nat else 3%nat)
           [(1 # 1); (2 # 1)] [(2 # 1); (1 # 1)]
           (perm_swap (2 # 1) (1 # 1) [])).
Qed.

(* P16〔参数 101 P′〕成员频率下界：头位成员 in_eq 构造消解 *)
Theorem dte_c3_freq_q_ge1_inst :
  (1 <= freq_q (1 # 1) [(1 # 1); (2 # 1)])%nat.
Proof.
  exact (freq_q_ge1 (1 # 1) [(1 # 1); (2 # 1)] (in_eq (1 # 1) [(2 # 1)])).
Qed.

(* P17〔参数 102 P′〕泛求和下界：逐点卫哨 le_n 内联消解 *)
Theorem dte_c3_nsum_ge_const_inst :
  (length [(1 # 1); (4 # 5)] * 7
   <= nsum (fun _ : Q => 7%nat) [(1 # 1); (4 # 5)])%nat.
Proof.
  exact (nsum_ge_const (fun _ : Q => 7%nat) [(1 # 1); (4 # 5)] 7
           (fun (x : Q) (_ : In x [(1 # 1); (4 # 5)]) => le_n 7)).
Qed.

(* P18〔参数 103 P′〕collide 下界：l:=[(1#2);(1#3)] 双元异值规范实例，
   长度卫哨喂  *)
Theorem dte_c3_collide_lower_pair :
  (1 / qn (length [(1 # 2); (1 # 3)]) <= collide [(1 # 2); (1 # 3)])%Q.
Proof.
  exact (collide_lower [(1 # 2); (1 # 3)] (dte_c3_len2_pos (1 # 2) (1 # 3))).
Qed.

(* P19〔参数 104 P′〕collide 置换不变：perm_swap 规范实例 *)
Theorem dte_c3_collide_perm_swap :
  collide [(1 # 2); (1 # 3)] == collide [(1 # 3); (1 # 2)].
Proof.
  exact (collide_perm [(1 # 2); (1 # 3)] [(1 # 3); (1 # 2)]
           (perm_swap (1 # 3) (1 # 2) [])).
Qed.

(* P20〔参数 105 P′〕maxfreq 下界：同 :1779 应用形 *)
Theorem dte_c3_maxfreq_lower_pair :
  (1 / qn (length [(1 # 2); (1 # 3)]) <= maxfreq [(1 # 2); (1 # 3)])%Q.
Proof.
  exact (maxfreq_lower [(1 # 2); (1 # 3)] (dte_c3_len2_pos (1 # 2) (1 # 3))).
Qed.

(* P21〔参数 106-107 P′〕全同值 maxfreq 取 1：l:=[(1#1);(2#2)] 非规范
   全同值对，all_same 卫哨喂 、长度卫哨喂  *)
Theorem dte_c3_maxfreq_all_same_one_pair :
  maxfreq [(1 # 1); (2 # 2)] == 1.
Proof.
  exact (maxfreq_all_same_one [(1 # 1); (2 # 2)] dte_c3_all_same_pair
           (dte_c3_len2_pos (1 # 1) (2 # 2))).
Qed.

(* P22〔参数 108 P′〕maxcount 置换不变：perm_swap 规范实例 *)
Theorem dte_c3_maxcount_perm_swap :
  maxcount [(1 # 2); (1 # 3)] = maxcount [(1 # 3); (1 # 2)].
Proof.
  exact (maxcount_perm [(1 # 2); (1 # 3)] [(1 # 3); (1 # 2)]
           (perm_swap (1 # 3) (1 # 2) [])).
Qed.

(* P23〔参数 109 P′〕maxfreq 置换不变：perm_swap 规范实例 *)
Theorem dte_c3_maxfreq_perm_swap :
  maxfreq [(1 # 2); (1 # 3)] == maxfreq [(1 # 3); (1 # 2)].
Proof.
  exact (maxfreq_perm [(1 # 2); (1 # 3)] [(1 # 3); (1 # 2)]
           (perm_swap (1 # 3) (1 # 2) [])).
Qed.

(* P24〔参数 110 拆分单向一〕H_chain 源结论面 Prop 三重合取位，拆分三
   单向供给（  :2226／  :481 合取位拆分先例同款）——前件卫哨
   逐字保留，本件＝合取支一（1/n <= collide）宿主 collide_lower 转发，
   泛合取 P′ 响亮申报（④） *)
Theorem dte_c3_H_chain_lo : forall l : list Q,
  (0 < length l)%nat -> (1 / qn (length l) <= collide l)%Q.
Proof.
  intros l Hl. exact (collide_lower l Hl).
Qed.

(* P25〔参数 110 拆分单向二〕同上合取支二（collide <= maxfreq），宿主
   collide_le_maxfreq 转发，如实申报 *)
Theorem dte_c3_H_chain_mid : forall l : list Q,
  (collide l <= maxfreq l)%Q.
Proof.
  intro l. exact (collide_le_maxfreq l).
Qed.

(* P26〔参数 110 拆分单向三〕同上合取支三（maxfreq <= 1），宿主
   maxfreq_upper 转发，如实申报 *)
Theorem dte_c3_H_chain_hi : forall l : list Q,
  (maxfreq l <= 1)%Q.
Proof.
  intro l. exact (maxfreq_upper l).
Qed.

(* P27〔参数 111 P′〕H_max_q 反变单调：序卫哨喂  跨值产路，出反变
   双实例面 *)
Theorem dte_c3_H_max_q_anti_inst :
  (H_max_q [(1 # 1); (2 # 2)] <= H_max_q [(1 # 2); (1 # 3)])%Q.
Proof.
  exact (H_max_q_anti [(1 # 2); (1 # 3)] [(1 # 1); (2 # 2)]
           dte_c3_maxfreq_distinct_le_eq).
Qed.

(* P28〔参数 112 P′〕H_max_q 下界耦合：同 :1779 应用形 *)
Theorem dte_c3_H_max_q_le_inv_pair :
  (H_max_q [(1 # 2); (1 # 3)]
   <= 1 - 1 / qn (length [(1 # 2); (1 # 3)]))%Q.
Proof.
  exact (H_max_q_le_inv [(1 # 2); (1 # 3)]
           (dte_c3_len2_pos (1 # 2) (1 # 3))).
Qed.

(* P29〔参数 113 P′〕熵族相干桥：H_freq ≡ H_min_q，同 :1779 应用形 *)
Theorem dte_c3_H_freq_eq_bridge_pair :
  H_freq [(1 # 2); (1 # 3)] == H_min_q [(1 # 2); (1 # 3)].
Proof.
  exact (H_freq_eq_bridge [(1 # 2); (1 # 3)]
           (dte_c3_len2_pos (1 # 2) (1 # 3))).
Qed.

(* P30〔参数 114-115 P′〕全同值 H_max_q 取 0：同 :1884 应用形（参数 115
   随条溢出在本卷交付，已响亮登记，下卷禁重复供给） *)
Theorem dte_c3_H_max_q_all_same_zero_pair :
  H_max_q [(1 # 1); (2 # 2)] == 0.
Proof.
  exact (H_max_q_all_same_zero [(1 # 1); (2 # 2)] dte_c3_all_same_pair
           (dte_c3_len2_pos (1 # 1) (2 # 2))).
Qed.

(* ============================================================ *)
(* 四 尾置验印区（文件最尾）：逐件承认面验印（全 Closed 判据）——          *)
(*    名清单＝37 定理，与 Qed 计数 37 零差                              *)
(* ============================================================ *)

Print Assumptions dte_c3_qeq_le_l.
Print Assumptions dte_c3_Qeq_pair.
Print Assumptions dte_c3_Qlt_3_2.
Print Assumptions dte_c3_Qle_2_2_3_2.
Print Assumptions dte_c3_all_same_pair.
Print Assumptions dte_c3_len2_pos.
Print Assumptions dte_c3_maxfreq_distinct_le_eq.
Print Assumptions dte_c3_qsub_mono_r_inst.
Print Assumptions dte_c3_hfreq_core_anti_1_0_1.
Print Assumptions dte_c3_H_freq_dpi_abs.
Print Assumptions dte_c3_in_map_const_mid.
Print Assumptions dte_c3_H_freq_map_twice_abs.
Print Assumptions dte_c3_H_freq_map_chain_abs.
Print Assumptions dte_c3_qn_ge1_2.
Print Assumptions dte_c3_qn_mul_pos_2_3.
Print Assumptions dte_c3_qdiv_ge_num_inst.
Print Assumptions dte_c3_qdiv_le_1_inst.
Print Assumptions dte_c3_qsub_le_inst.
Print Assumptions dte_c3_nmax_bound_inst.
Print Assumptions dte_c3_nmax_le_bound_inst.
Print Assumptions dte_c3_nmax_ext_in_inst.
Print Assumptions dte_c3_nmax_perm_inst.
Print Assumptions dte_c3_freq_q_ge1_inst.
Print Assumptions dte_c3_nsum_ge_const_inst.
Print Assumptions dte_c3_collide_lower_pair.
Print Assumptions dte_c3_collide_perm_swap.
Print Assumptions dte_c3_maxfreq_lower_pair.
Print Assumptions dte_c3_maxfreq_all_same_one_pair.
Print Assumptions dte_c3_maxcount_perm_swap.
Print Assumptions dte_c3_maxfreq_perm_swap.
Print Assumptions dte_c3_H_chain_lo.
Print Assumptions dte_c3_H_chain_mid.
Print Assumptions dte_c3_H_chain_hi.
Print Assumptions dte_c3_H_max_q_anti_inst.
Print Assumptions dte_c3_H_max_q_le_inv_pair.
Print Assumptions dte_c3_H_freq_eq_bridge_pair.
Print Assumptions dte_c3_H_max_q_all_same_zero_pair.

(* ============================================================ *)
(* 五 提取检验区（红线四：可提取验证，Obj.magic 计数＝0 判据）            *)
(*    定理桶：单条 Separate Extraction（  避坑——同文件      *)
(*    双命令同名覆写禁触），37 定理结论面全数 Prop 离散承载，按家族      *)
(*    提取擦除惯例归约占位；数据层真提取面＝P′ 语句面所使用宿主数据      *)
(*    承载（qn/freq_q/nsum/nmax/sqsum/collide/maxcount/maxfreq/H_freq/  *)
(*    H_max_q/H_min_q），归独立检验件 _dte_c3_probe.v 定向               *)
(*     另桶（分桶工艺执行位）。                        *)
(* ============================================================ *)

Set Extraction Output Directory "_log/dte_t10".
Separate Extraction dte_c3_qeq_le_l dte_c3_Qeq_pair dte_c3_Qlt_3_2
  dte_c3_Qle_2_2_3_2 dte_c3_all_same_pair dte_c3_len2_pos
  dte_c3_maxfreq_distinct_le_eq dte_c3_qsub_mono_r_inst
  dte_c3_hfreq_core_anti_1_0_1 dte_c3_H_freq_dpi_abs
  dte_c3_in_map_const_mid dte_c3_H_freq_map_twice_abs
  dte_c3_H_freq_map_chain_abs dte_c3_qn_ge1_2 dte_c3_qn_mul_pos_2_3
  dte_c3_qdiv_ge_num_inst dte_c3_qdiv_le_1_inst dte_c3_qsub_le_inst
  dte_c3_nmax_bound_inst dte_c3_nmax_le_bound_inst dte_c3_nmax_ext_in_inst
  dte_c3_nmax_perm_inst dte_c3_freq_q_ge1_inst dte_c3_nsum_ge_const_inst
  dte_c3_collide_lower_pair dte_c3_collide_perm_swap
  dte_c3_maxfreq_lower_pair dte_c3_maxfreq_all_same_one_pair
  dte_c3_maxcount_perm_swap dte_c3_maxfreq_perm_swap dte_c3_H_chain_lo
  dte_c3_H_chain_mid dte_c3_H_chain_hi dte_c3_H_max_q_anti_inst
  dte_c3_H_max_q_le_inv_pair dte_c3_H_freq_eq_bridge_pair
  dte_c3_H_max_q_all_same_zero_pair.
