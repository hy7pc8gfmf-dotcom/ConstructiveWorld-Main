(* ==========================================================================
   abl_dte_core1.v —— DTPT_Entropy 前件参数消解供给·卷一（参数 1–38）。
   ── 使命：宿主 DTPT_Entropy.v 本体 150 前件参数登记序第 1–38 位（语句
   坐标 :95–:843，32 条语句，卷界零重叠）逐参数按形态二 T＋P′ 消解供给，
   卷内三区：A 直供形 12 枚供 15 参数（语句面＝登记形经 dte_ 前缀映射逐字
   同构，证明体就地构造真构造、零宿主定理使用）；T 参数面产路 7 枚（卫哨
   构造子实例／置换构造子／成员构造子／排序零前提产路）；P′ 无前提精简版
   19 枚＋合取位拆分双单向 2 枚（H_lam_cross_phase_bounds 源结论面 Prop
   合取位以拆分规避）。38 参数＝37 供给＋1 登记（xq_len1_el 存在体结论位，
   照登记不供给）。宿主件零字节动零级联。
   ── 依赖：DTPT（insert_q／P0／rot／dedup／H_ms／Qmem／D5_P0_perm 等参数
   语句与产路引用面）、DTPT_Entropy（本卷全部参数语句本体定义面）＋stdlib
   （QArith.QArith／Qabs、List、Permutation、Arith、Lia、Extraction）。
   ── 对标行：A 直供形先例＝abl_dtd_core1（就地构造零宿主引用）；T＋P′
   分区工艺先例＝abl_dtd_core3／abl_dtd_core4。
   ── 构造性注记：零承认式声明、零悬置前提、零经典逻辑、零节变量声明位，
   40 定理全 Qed 真构造闭合；供给语句面零混载形态（零裸 exists／零等价／
   零假结论／零析取合取位）；<> 全件仅 dte_c1_cons_ne 一处＝NEQ 参数面
   逐字透传（非自造）；名面全 dte_／dte_c1_ 前缀；尾置逐件 Print
   Assumptions Closed＋定理桶单条 Separate Extraction，Obj.magic 零判据。
   ── 编译配方：池 cwd＝沙箱/现役/abl_r85_supply_pool；source Live 库根
   toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 后 nice -19
   rocq c -native-compiler no
   -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
   abl_dte_core1.v；绿判＝EXIT=0／日志零 Error／.vo 头 8 字节
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
(* 一 供给定理区·卷一 A 直供形（12 枚；参数 1-2/5-11/13/21-22/28-29/38；   *)
(*    语句面＝底册参数面现档逐字经 dte_ 前缀映射，证明体 就地构造     *)
(*    真构造——宿主证体重演，零宿主定理使用）                          *)
(* ============================================================ *)

(* A1〔参数 1-2·:95 qadd_nonneg 逐字〕Q 加法非负双卫哨离散义务 *)
Theorem dte_qadd_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> (0 <= a + b)%Q.
Proof.
  intros [an ad] [bn bd]; simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

(* A2〔参数 5·:171 xq_Qle_bool_true 逐字〕Qle→Qle_bool 判定面正向桥 *)
Theorem dte_xq_Qle_bool_true : forall x y : Q, (x <= y)%Q -> Qle_bool x y = true.
Proof.
  intros [nx dx] [ny dy]. unfold Qle, Qle_bool; simpl. intros H.
  destruct (Z.leb (nx * Z.pos dy) (ny * Z.pos dx)) eqn:E.
  - reflexivity.
  - apply Z.leb_gt in E. lia.
Qed.

(* A3〔参数 6·:179 xq_Qle_bool_le 逐字〕Qle_bool→Qle 判定面反向桥 *)
Theorem dte_xq_Qle_bool_le : forall x y : Q, Qle_bool x y = true -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy]. unfold Qle, Qle_bool; simpl.
  change ((nx * Z.pos dy <=? ny * Z.pos dx)%Z = true
          -> (nx * Z.pos dy <= ny * Z.pos dx)%Z).
  intros H. apply Z.leb_le. exact H.
Qed.

(* A4〔参数 7-8·:187 xq_Qle_antisym 逐字〕Q 序反对称 *)
Theorem dte_xq_Qle_antisym : forall x y : Q, (x <= y)%Q -> (y <= x)%Q -> x == y.
Proof.
  intros [nx dx] [ny dy] H1 H2. unfold Qle in H1, H2; simpl in H1, H2.
  unfold Qeq; simpl. lia.
Qed.

(* A5〔参数 9·:194 xq_abs_id 逐字〕非负自绝对值恒等（Z.abs_eq 路） *)
Theorem dte_xq_abs_id : forall x : Q, (0 <= x)%Q -> Qabs x == x.
Proof.
  intros [n d] Hx. unfold Qle in Hx; simpl in Hx.
  assert (Hn : (0 <= n)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite (Z.abs_eq n Hn). reflexivity.
Qed.

(* A6〔参数 10·:202 xq_abs_eq0 逐字〕零绝对值零化 *)
Theorem dte_xq_abs_eq0 : forall x : Q, x == 0 -> Qabs x == 0.
Proof.
  intros [n d] Hx. unfold Qeq in Hx; simpl in Hx.
  assert (Hn : (n = 0)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite Hn. reflexivity.
Qed.

(* A7〔参数 11·:220 xq_abs_eq 逐字〕等值绝对值传递（Z.abs_spec 四支） *)
Theorem dte_xq_abs_eq : forall x y : Q, x == y -> Qabs x == Qabs y.
Proof.
  intros [n1 d1] [n2 d2] Hxy.
  unfold Qeq in Hxy; simpl in Hxy.
  unfold Qabs; simpl. unfold Qeq; simpl.
  pose proof (Z.abs_spec n1) as Ha1. pose proof (Z.abs_spec n2) as Ha2.
  destruct Ha1 as [[A1 B1] | [A1 B1]];
    destruct Ha2 as [[A2 B2] | [A2 B2]];
    try rewrite B1; try rewrite B2; lia.
Qed.

(* A8〔参数 21-22·:475 xq_mul_nonneg 逐字〕Q 乘法非负双卫哨 *)
Theorem dte_xq_mul_nonneg : forall a b : Q, (0 <= a)%Q -> (0 <= b)%Q -> (0 <= a * b)%Q.
Proof.
  intros [an ad] [bn bd] Ha Hb. unfold Qle in Ha, Hb; simpl in Ha, Hb.
  unfold Qle, Qmult; simpl. lia.
Qed.

(* A9〔参数 28·:627 xq_Zlen_inj1 逐字〕长度系数单射（Z 层 lia） *)
Theorem dte_xq_Zlen_inj1 : forall n : nat, ((Z.of_nat n # 1) == 1)%Q -> n = 1%nat.
Proof.
  intros n H. unfold Qeq in H; simpl in H. lia.
Qed.

(* A10〔参数 29·:632 xq_Qeq_le 逐字〕等值弱序化 *)
Theorem dte_xq_Qeq_le : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy] Hxy. unfold Qeq in Hxy; simpl in Hxy.
  unfold Qle; simpl. lia.
Qed.

(* A11〔参数 13·:308 xq_insert_q_head_aux 逐字〕插入置首方程
   （insert_q 定义性展开＋A2 判定面重演；就地构造） *)
Theorem dte_xq_insert_q_head_aux : forall (a b : Q) (bs : list Q),
  (a <= b)%Q -> insert_q a (b :: bs) = a :: b :: bs.
Proof.
  intros a b bs H. simpl. rewrite (dte_xq_Qle_bool_true _ _ H). reflexivity.
Qed.

(* A12〔参数 38·:843 gate_low_entropy_false_le 逐字〕门控假面右向界
   （gate_low_entropy 定义性展开＋Qle_bool 假面 Z 层 就地构造 重演；
   stdlib 无 Qle_bool 假面具名反向件，走 Z.leb_gt 定义性路） *)
Theorem dte_gate_low_entropy_false_le : forall H threshold : Q,
  gate_low_entropy H threshold = false -> (threshold <= H)%Q.
Proof.
  intros H threshold E. destruct H as [nx dx]. destruct threshold as [ny dy].
  unfold gate_low_entropy in E. unfold Qle_bool in E; simpl in E.
  apply Z.leb_gt in E. unfold Qle; simpl. lia.
Qed.

(* ============================================================ *)
(* 二 供给定理区·卷二 T 参数面产路（7 枚共用；Q-ORD 规范实例／Qeq 非规范  *)
(*    值对／PERM 置换构造子路／NEQ 卫哨透传／IN 成员构造子路／SORTED    *)
(*    排序零前提产路）                                                *)
(* ============================================================ *)

(* 〔Q-ORD 规范实例·供参数 1-4/23-24 输入源〕(0 <= lam)%Q 参数于
   lam := (1#2) 非规范正实例（  dtd_c3_Qle_0_1 配方）——使用位
   实拍：P1（参数 1-2）＋P2（参数 3-4）＋P10/P11（参数 23-24） *)
Theorem dte_c1_Qle_0_half : (0 <= (1 # 2))%Q.
Proof.
  unfold Qle. simpl. lia.
Qed.

(* 〔Q-ORD 规范实例·供参数 1 P′ 第二卫哨〕lam := (1#3) 异形防 P′ 面重合 *)
Theorem dte_c1_Qle_0_third : (0 <= (1 # 3))%Q.
Proof.
  unfold Qle. simpl. lia.
Qed.

(* 〔Qeq 非规范同值对·供参数 30 卫哨〕x == y 型 Q-ORD 参数于
   (2#2, 1#1) 值层闭合对（  dtd_c3_Qeq_half 配方；非退化反射面） *)
Theorem dte_c1_Qeq_half : (2 # 2 == 1 # 1)%Q.
Proof.
  reflexivity.
Qed.

(* 〔PERM 置换构造子路·独立产路件如实申报〕Permutation l p 参数于
   p := rev l 实例（stdlib Permutation_rev 转发；/ 同款）——
   本卷 P′ 使用链零入（参数 26 实供＝P13 直接代入 Permutation_sym
   (D5_P0_perm l)，不经本件），留作后续卷 PERM 参数产路，勘正如实申报 *)
Theorem dte_c1_perm_rev : forall l : list Q, Permutation l (rev l).
Proof.
  intro l. apply Permutation_rev.
Qed.

(* 〔NEQ 卫哨透传·供参数 15/16〕m <> [] 参数面逐字（任务指定卫哨透传形，
   全件唯一 <> 语句面位）于 cons 规范实例（discriminate 一击） *)
Theorem dte_c1_cons_ne : forall (x : Q) (l : list Q), (x :: l) <> [].
Proof.
  intros x l. discriminate.
Qed.

(* 〔IN 成员构造子路·供参数 34（如实申报）〕In x l 参数于头位 cons 规范实例
   （in_eq 全参 exact 形——  处方）；参数 19-20 实供＝P9 直接代入
   stdlib in_eq/in_cons（不经本件），勘正如实申报 *)
Theorem dte_c1_in_cons : forall (x : Q) (l : list Q), In x (x :: l).
Proof.
  intros x l. exact (in_eq x l).
Qed.

(* 〔SORTED 零前提产路·供参数 12/14/17/18/25〕SortedQ l 参数于 l := P0 l
   规范实例（宿主 xq_P0_sorted 零前提产路转发——   先例；普查
   「SortedQ 有产路」锚位） *)
Theorem dte_c1_sorted_P0 : forall l : list Q, SortedQ (P0 l).
Proof.
  intro l. apply xq_P0_sorted.
Qed.

(* ============================================================ *)
(* 【只登记】参数 33＝:749 xq_len1_el〔底册 NAT〕——底册 §2.3 混载旗位      *)
(* （结论面存在体 Prop 位），照   :1864 先例只登记不供给不擅自扩面，  *)
(* 失败显式申报 见交付报告 §四；升级方向＝存在见证 sigT 。       *)
(* ============================================================ *)

(* ============================================================ *)
(* 三 供给定理区·卷三 P′ 无前提精简版（19 枚；宿主定理 @ 全实参显式应用，      *)
(*    参数消即出；结论面＝宿主结论面现档逐字特化，全离散承载）＋合取位     *)
(*    拆分双单向（2 枚）                                              *)
(* ============================================================ *)

(* P1〔参数 1-2 P′〕双卫哨规范实例无前提精简版：Q-ORD 参数喂 /
   ((1#2),(1#3))，出正数和非负面 *)
Theorem dte_c1_qadd_nonneg_half_third : (0 <= (1 # 2) + (1 # 3))%Q.
Proof.
  exact (dte_qadd_nonneg (1 # 2) (1 # 3) dte_c1_Qle_0_half dte_c1_Qle_0_third).
Qed.

(* P2〔参数 3-4 P′〕跨相单调双卫哨规范实例：l := []、s := 0 时跨相前提
   空表自反内联消解，lam := (0,1) 喂  同族，出 λ 放大 H_lam 单调面 *)
Theorem dte_c1_H_lam_mono_0_1 : (H_lam [] 0 0 <= H_lam [] 0 1)%Q.
Proof.
  assert (H1 : (H_adj (Pinf [] 0) <= H_adj (P0 []))%Q)
    by (change (0 <= 0)%Q; apply Qle_refl).
  exact (H_lam_mono [] 0 H1 0 1 dte_c1_Qle_0_half).
Qed.

(* P3〔参数 12 P′〕SortedQ 参数喂 （l := P0 l），出插入保序 P0 规范形 *)
Theorem dte_c1_sortQ_insert_P0 : forall (x : Q) (l : list Q),
  SortedQ (insert_q x (P0 l)).
Proof.
  intros x l. exact (xq_sortQ_insert x (P0 l) (dte_c1_sorted_P0 l)).
Qed.

(* P4〔参数 14 P′〕同  应用形，出 P0 幂等面 *)
Theorem dte_c1_sortQ_P0_idem : forall l : list Q, P0 (P0 l) = P0 l.
Proof.
  intro l. exact (xq_sortQ_P0_id (P0 l) (dte_c1_sorted_P0 l)).
Qed.

(* P5〔参数 15 P′〕NEQ 参数喂  头位实例，出尾元成员面 *)
Theorem dte_c1_lastq_In_cons : forall (a : Q) (l : list Q),
  In (lastq (a :: l)) (a :: l).
Proof.
  intros a l. exact (xq_lastq_In (a :: l) (dte_c1_cons_ne a l)).
Qed.

(* P6〔参数 16 P′〕同  应用形，出首元成员面 *)
Theorem dte_c1_hd_In_cons : forall (a : Q) (l : list Q),
  In (hd 0 (a :: l)) (a :: l).
Proof.
  intros a l. exact (xq_hd_In_gen (a :: l) (dte_c1_cons_ne a l)).
Qed.

(* P7〔参数 17 P′〕SortedQ 参数喂 ，出首尾序界 P0 规范形 *)
Theorem dte_c1_hd_le_lastq_P0 : forall l : list Q,
  (hd 0 (P0 l) <= lastq (P0 l))%Q.
Proof.
  intro l. exact (xq_hd_le_lastq (P0 l) (dte_c1_sorted_P0 l)).
Qed.

(* P8〔参数 18 P′〕SortedQ 参数喂 ，出望远镜方程 P0 规范形 *)
Theorem dte_c1_telescope_P0 : forall l : list Q,
  H_adj (P0 l) == lastq (P0 l) - hd 0 (P0 l).
Proof.
  intro l. exact (xq_telescope (P0 l) (dte_c1_sorted_P0 l)).
Qed.

(* P9〔参数 19-20 P′〕In 双参数喂构造子双实例（in_eq 头位＋in_cons 次位，
   全参 exact 形），出双元表配对界面 |a-b| <= H_adj [a;b] *)
Theorem dte_c1_pair_dist_cons2 : forall a b : Q,
  (Qabs (a - b) <= H_adj [a; b])%Q.
Proof.
  intros a b.
  exact (xq_pair_dist_le [a; b] a b (in_eq a [b])
           (in_cons a b [b] (in_eq b []))).
Qed.

(* P10〔参数 23 拆分单向一〕源结论面 Prop 合取位前件（H_adj (P0 l) <=
   H_lam l s lam），于 lam := 0 规范实例双卫哨内联消解（Qle_refl＋），
   出 λ=0 端点下界单向——合取位整形 P′ 响亮申报（④） *)
Theorem dte_c1_H_lam_lam0_lo : forall (l : list Q) (s : nat),
  (H_adj (P0 l) <= H_lam l s 0)%Q.
Proof.
  intros l s.
  destruct (H_lam_cross_phase_bounds l s 0 (Qle_refl 0) dte_c1_Qle_0_half)
    as [Hlo _].
  exact Hlo.
Qed.

(* P11〔参数 24 拆分单向二〕同上后件单向，出 λ=0 端点上界 *)
Theorem dte_c1_H_lam_lam0_hi : forall (l : list Q) (s : nat),
  (H_lam l s 0 <= H_adj (Pinf l s))%Q.
Proof.
  intros l s.
  destruct (H_lam_cross_phase_bounds l s 0 (Qle_refl 0) dte_c1_Qle_0_half)
    as [_ Hhi].
  exact Hhi.
Qed.

(* P12〔参数 25 P′〕SortedQ 参数喂 ，出 P0 相零化香农偏差熵面 *)
Theorem dte_c1_H_shannon_P0_zero : forall l : list Q, H_devsum (P0 l) == 0.
Proof.
  intro l. exact (xq_H_shannon_sortQ (P0 l) (dte_c1_sorted_P0 l)).
Qed.

(* P13〔参数 26 P′〕PERM 参数喂跨相置换实例（Permutation_sym (D5_P0_perm l)
   全实参显式应用），出频域计数 P0 相不变面 *)
Theorem dte_c1_count_val_P0_perm : forall (x : Q) (l : list Q),
  count_val x (P0 l) = count_val x l.
Proof.
  intros x l.
  exact (count_val_perm x (P0 l) l (Permutation_sym (D5_P0_perm l))).
Qed.

(* P14〔参数 27 P′〕守卫参数喂自反实例（ctx := l，Qle_refl），出条件熵
   自条件非负面（即宿主 H_cond_self 面） *)
Theorem dte_c1_H_cond_self_ge0 : forall l : list Q, (0 <= H_cond l l)%Q.
Proof.
  intro l. exact (H_cond_nonneg_guarded l l (Qle_refl (H_devsum l))).
Qed.

(* P15〔参数 30 P′〕Q-ORD 卫哨参数喂  非规范同值对（y := (2#2) == a :=
   (1#1)），出同值插入置首方程非退化实例 *)
Theorem dte_c1_insert_const_head_half : forall ys : list Q,
  insert_q (1 # 1) ((2 # 2) :: ys) = (1 # 1) :: (2 # 2) :: ys.
Proof.
  intro ys. exact (xq_insert_const_head (1 # 1) (2 # 2) ys dte_c1_Qeq_half).
Qed.

(* P16〔参数 31 P′〕全同值 Forall 卫哨参数于单元表 Qeq_refl 规范实例，
   出 P0 常值表恒等面 *)
Theorem dte_c1_P0_const_cons : forall a : Q, P0 [a] = [a].
Proof.
  intro a.
  exact (xq_P0_const_id a [a]
           (@Forall_cons Q (fun z : Q => z == a) a (@nil Q) (Qeq_refl a)
              (@Forall_nil Q (fun z : Q => z == a)))).
Qed.

(* P17〔参数 32 P′〕同 P16 卫哨实例，出单元表香农偏差熵零化面 *)
Theorem dte_c1_Hshannon_const_sing : forall a : Q, H_devsum [a] == 0.
Proof.
  intro a.
  exact (H_shannon_q_const_zero a [a]
           (@Forall_cons Q (fun z : Q => z == a) a (@nil Q) (Qeq_refl a)
              (@Forall_nil Q (fun z : Q => z == a)))).
Qed.

(* P18〔参数 34 P′〕IN 参数喂  头位实例，出成员面 Qmem 化（Qmem 系宿主
   成员判定以 Prop 承载（离散零数据）， 口径追加横切登记②惯例） *)
Theorem dte_c1_In_Qmem_cons : forall (z : Q) (l : list Q), Qmem z (z :: l).
Proof.
  intros z l. exact (xq_In_Qmem z (z :: l) (dte_c1_in_cons z l)).
Qed.

(* P19〔参数 35 P′〕去重单元方程参数于 [(1#2)] 规范实例（dedup 真计算闭合
   eq_refl），出全同值 Forall 面（宿主结论面现档逐字特化） *)
Theorem dte_c1_dedup1_all_eq_sing :
  Forall (fun z : Q => z == (1 # 2)) [(1 # 2)].
Proof.
  exact (xq_dedup1_all_eq [(1 # 2)] (1 # 2) eq_refl).
Qed.

(* P20〔参数 36 P′〕多重集熵退化卫哨参数于 [(1#2);(1#2)] 双元全同表规范
   实例（dedup 真计算闭合 reflexivity），出香农偏差熵零化面 *)
Theorem dte_c1_Hms1_Hsh0_pair : H_devsum [(1 # 2); (1 # 2)] == 0.
Proof.
  assert (Hp : (H_ms [(1 # 2); (1 # 2)] == 1)%Q) by reflexivity.
  exact (H_ms1_Hshannon0 [(1 # 2); (1 # 2)] Hp).
Qed.

(* P21〔参数 37 P′〕评估套件退化卫哨参数于 mkMEval [(1#2)] [(1#3)] 规范
   实例（投影往返计算闭合 reflexivity），出 me_Hsh 零化面 *)
Theorem dte_c1_mkMEval_Hsh0 :
  (me_Hsh (mkMEval [(1 # 2)] [(1 # 3)]) == 0)%Q.
Proof.
  assert (Hp : (me_Hms (mkMEval [(1 # 2)] [(1 # 3)]) == 1)%Q) by reflexivity.
  exact (mkMEval_Hms1_Hsh0 [(1 # 2)] [(1 # 3)] Hp).
Qed.

(* ============================================================ *)
(* 四 尾置验印区（文件最尾）：逐件承认面验印（全 Closed 判据）——          *)
(*    名清单＝40 定理，与 Qed 计数 40 零差                              *)
(* ============================================================ *)

Print Assumptions dte_qadd_nonneg.
Print Assumptions dte_xq_Qle_bool_true.
Print Assumptions dte_xq_Qle_bool_le.
Print Assumptions dte_xq_Qle_antisym.
Print Assumptions dte_xq_abs_id.
Print Assumptions dte_xq_abs_eq0.
Print Assumptions dte_xq_abs_eq.
Print Assumptions dte_xq_mul_nonneg.
Print Assumptions dte_xq_Zlen_inj1.
Print Assumptions dte_xq_Qeq_le.
Print Assumptions dte_xq_insert_q_head_aux.
Print Assumptions dte_gate_low_entropy_false_le.
Print Assumptions dte_c1_Qle_0_half.
Print Assumptions dte_c1_Qle_0_third.
Print Assumptions dte_c1_Qeq_half.
Print Assumptions dte_c1_perm_rev.
Print Assumptions dte_c1_cons_ne.
Print Assumptions dte_c1_in_cons.
Print Assumptions dte_c1_sorted_P0.
Print Assumptions dte_c1_qadd_nonneg_half_third.
Print Assumptions dte_c1_H_lam_mono_0_1.
Print Assumptions dte_c1_sortQ_insert_P0.
Print Assumptions dte_c1_sortQ_P0_idem.
Print Assumptions dte_c1_lastq_In_cons.
Print Assumptions dte_c1_hd_In_cons.
Print Assumptions dte_c1_hd_le_lastq_P0.
Print Assumptions dte_c1_telescope_P0.
Print Assumptions dte_c1_pair_dist_cons2.
Print Assumptions dte_c1_H_lam_lam0_lo.
Print Assumptions dte_c1_H_lam_lam0_hi.
Print Assumptions dte_c1_H_shannon_P0_zero.
Print Assumptions dte_c1_count_val_P0_perm.
Print Assumptions dte_c1_H_cond_self_ge0.
Print Assumptions dte_c1_insert_const_head_half.
Print Assumptions dte_c1_P0_const_cons.
Print Assumptions dte_c1_Hshannon_const_sing.
Print Assumptions dte_c1_In_Qmem_cons.
Print Assumptions dte_c1_dedup1_all_eq_sing.
Print Assumptions dte_c1_Hms1_Hsh0_pair.
Print Assumptions dte_c1_mkMEval_Hsh0.

(* ============================================================ *)
(* 五 提取检验区（红线四：可提取验证，Obj.magic 计数＝0 判据）            *)
(*    定理桶：单条 Separate Extraction（  避坑——同文件      *)
(*    双命令同名覆写禁触），40 定理结论面全数 Prop 离散承载，按家族      *)
(*    提取擦除惯例归约占位；数据层真提取面＝P′ 语句面所使用宿主数据      *)
(*    承载（insert_q/P0/rot/Pinf/H_adj/dedup/H_ms/count_val/H_devsum/   *)
(*    H_lam/H_cond/gate_low_entropy/mkMEval），归独立检验件              *)
(*    _dte_c1_probe.v 定向  另桶（分桶工艺执行位）。     *)
(* ============================================================ *)

Set Extraction Output Directory "_log/dte_t6".
Separate Extraction dte_qadd_nonneg dte_xq_Qle_bool_true dte_xq_Qle_bool_le
  dte_xq_Qle_antisym dte_xq_abs_id dte_xq_abs_eq0 dte_xq_abs_eq
  dte_xq_mul_nonneg dte_xq_Zlen_inj1 dte_xq_Qeq_le dte_xq_insert_q_head_aux
  dte_gate_low_entropy_false_le dte_c1_Qle_0_half dte_c1_Qle_0_third
  dte_c1_Qeq_half dte_c1_perm_rev dte_c1_cons_ne dte_c1_in_cons
  dte_c1_sorted_P0 dte_c1_qadd_nonneg_half_third dte_c1_H_lam_mono_0_1
  dte_c1_sortQ_insert_P0 dte_c1_sortQ_P0_idem dte_c1_lastq_In_cons
  dte_c1_hd_In_cons dte_c1_hd_le_lastq_P0 dte_c1_telescope_P0
  dte_c1_pair_dist_cons2 dte_c1_H_lam_lam0_lo dte_c1_H_lam_lam0_hi
  dte_c1_H_shannon_P0_zero dte_c1_count_val_P0_perm dte_c1_H_cond_self_ge0
  dte_c1_insert_const_head_half dte_c1_P0_const_cons
  dte_c1_Hshannon_const_sing dte_c1_In_Qmem_cons dte_c1_dedup1_all_eq_sing
  dte_c1_Hms1_Hsh0_pair dte_c1_mkMEval_Hsh0.
