(* ==========================================================================
   abl_dtd_core3.v —— DTPT 本体前件参数消解供给·卷三（参数 71–105）。
   ── 使命：宿主 DTPT.v 前件参数登记序第 71–105 位（语句坐标 :1663–:2673，
   30 条语句 35 参数，卷界零重叠）逐参数按形态二 T＋P′ 消解供给：T＝参数面
   产路（卫哨构造子实例／置换构造子／成员构造子／非规范零值 Qeq 产路），P′
   ＝宿主结论面现档逐字特化。35 参数＝28 供给＋7 登记（llm_Tex_fiber／
   freq_zero_of_notQmem／fiber_cozero_disjoint／fiber_cozero_compl／
   Forall_in／Forall_of_pointwise 等，存在体／否定／iff 混载旗，照登记不
   供给）；四参数 qmul_eq0_fwd／qsum_sq_zero／fiber_cozero_cover／
   in_insert_q 源结论面含 Prop 析取合取位，以 T 产路单独交付（前件参数面
   全净）。38 定理全 Qed 真构造闭合；宿主件零字节动零级联。
   ── 依赖：DTPT（本卷全部参数语句与产路出处）＋stdlib（QArith.QArith／
   Qabs、List、Permutation、Sorting.Sorted〔StronglySorted 参数面必需〕、
   Arith〔Nat.le_0_l 必需〕、Lia、Extraction）。
   ── 对标行：T＋P′ 形态二先例＝abl_tbn_supply_b；合取位拆分先例＝同池
   abl_dte_core1（H_lam_cross_phase_bounds 拆分双单向同族工艺）。
   ── 构造性注记：零承认式声明、零悬置前提、零经典逻辑、零节变量声明位；
   供给语句面零混载形态（零裸 exists／零否定／零 iff／零 sumbool 载荷位）；
   <> 全件仅 dtd_c3_cons_neq_nil 一处＝NEQ 参数面逐字透传（非自造）；名面
   全 dtd_c3_ 前缀（与 dtd_／dtd_c2_ 中缀隔离）；尾置逐件 Print Assumptions
   Closed＋定理桶单条 Separate Extraction，Obj.magic 零判据。
   ── 编译配方：池 cwd＝沙箱/现役/abl_r85_supply_pool；source Live 库根
   toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 后 nice -19
   rocq c -native-compiler no
   -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
   abl_dtd_core3.v；绿判＝EXIT=0／日志零 Error／.vo 头 8 字节
   436f7121 00015ff4／.vo 新于 .v；第五证 rocq check；产物只落本池。
   ========================================================================== *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

Require DTPT.
Import DTPT.DTPT.

(* ============================================================ *)
(* 一 供给定理区·T 产路（18 枚；参数面产路实例，就地构造 或       *)
(*    在役构造子转发；语句面＝底册参数面逐字或其构造子产路实例）        *)
(* ============================================================ *)

(* 〔NAT 表长自反卫哨·供 :1663/:1674/:1846 三参数〕
   (length l <= n)%nat 参数于 n := length l 规范实例（le_n 构造子一击） *)
Theorem dtd_c3_le_length_refl : forall l : list Q, (length l <= length l)%nat.
Proof.
  intro l. apply le_n.
Qed.

(* 〔NAT 零下界卫哨·供 :1789 参数〕(n <= length l)%nat 参数于 n := 0
   规范实例（Nat.le_0_l 一击；  dtd_c2_nat_le_0 同族实例形） *)
Theorem dtd_c3_nat_le_0_length : forall l : list Q, (0 <= length l)%nat.
Proof.
  intro l. apply Nat.le_0_l.
Qed.

(* 〔BOOL 判定面产路·供 :1739/:1750 双参数〕gate_pass t H = true 参数
   于 H := t 自反实例（Qle_bool_iff proj2 方向＋Qle_refl，检验实测
   stdlib 无 Qle_bool_refl 名面——改走 iff proj2 路线） *)
Theorem dtd_c3_gate_pass_refl : forall t : Q, gate_pass t t = true.
Proof.
  intro t. unfold gate_pass.
  assert (Ht : Qle_bool t t = true)
    by (apply (proj2 (Qle_bool_iff t t)); apply Qle_refl).
  rewrite Ht. reflexivity.
Qed.

(* 〔Q-ORD 规范实例·供 :1739 参数 1〕(t1 <= t2)%Q 参数于 (0, 1) 具体
   规范实例（unfold Qle 定义性展开＋lia） *)
Theorem dtd_c3_Qle_0_1 : (0 <= 1)%Q.
Proof.
  unfold Qle. simpl. lia.
Qed.

(* 〔Q-ORD 规范实例·供 :1750 参数 1〕(H1 <= H2)%Q 参数于 (0, 2) 具体
   规范实例（同  配方；与  异形防 P′ 面重合） *)
Theorem dtd_c3_Qle_0_2 : (0 <= 2)%Q.
Proof.
  unfold Qle. simpl. lia.
Qed.

(* 〔Qeq 自反产路·供 :2252 双参数〕a == 0 型 Q-ORD 参数于 a := 0 自反
   实例（Qeq 展开后逐字同形） *)
Theorem dtd_c3_Qeq_refl : forall x : Q, x == x.
Proof.
  intro x. unfold Qeq. reflexivity.
Qed.

(* 〔Qeq 非规范值产路·供 :1938/:2172 双参数〕x == y 型 Q-ORD 参数于
   非规范同值对 (2 # 2, 1 # 1) 规范实例——Qeq 系值层等价非字面语法
   同形（2·1 = 1·2 值层闭合），非退化反射面 *)
Theorem dtd_c3_Qeq_half : (2 # 2 == 1 # 1)%Q.
Proof.
  reflexivity.
Qed.

(* 〔Qeq 非规范零产路·供 :2188/:2196 双参数〕a == 0 型 Q-ORD 参数于
   非规范零 (0 # 3) 规范实例（0·1 = 0·3 值层闭合） *)
Theorem dtd_c3_Qeq_0_third : (0 # 3 == 0)%Q.
Proof.
  reflexivity.
Qed.

(* 〔PERM 构造子路·供 :1987/:2075 双参数〕Permutation l p 参数于
   p := rev l 实例（stdlib Permutation_rev 构造子转发； 
   dtd_c2_perm_rev 同款） *)
Theorem dtd_c3_perm_rev : forall l : list Q, Permutation l (rev l).
Proof.
  intro l. apply Permutation_rev.
Qed.

(* 〔NEQ 卫哨产路·供 :2107 参数〕l <> [] 参数面逐字（NEQ 参数透传形，
   任务指定卫哨透传，/ 同款）于 cons 规范实例
   （discriminate 一击；全件唯一 <> 语句面位） *)
Theorem dtd_c3_cons_neq_nil : forall (x : Q) (l : list Q), (x :: l) <> [].
Proof.
  intros x l. discriminate.
Qed.

(* 〔Qnodup 产路·供 :2012 参数〕Qnodup m 参数于 m := dedup l 规范
   实例（宿主 dedup_Qnodup :324 零前提产路转发——普查「SortedQ 有
   产路」同族判定） *)
Theorem dtd_c3_Qnodup_dedup : forall l : list Q, Qnodup (dedup l).
Proof.
  intro l. apply dedup_Qnodup.
Qed.

(* 〔In 构造子路·供 :2412 双参数/:2445 参数〕In x l 参数于头位 cons
   规范实例（in_eq 构造子一击） *)
Theorem dtd_c3_in_cons : forall (x : Q) (l : list Q), In x (x :: l).
Proof.
  intros x l. apply in_eq.
Qed.

(* 〔In 构造子路·供 :2625 参数〕In z (insert_q x l) 参数于
   l := [] 规范实例（insert_q 空表支归约出 [x] 头位；全参 exact 形
   避 apply 换关系回退——检验实测注意点） *)
Theorem dtd_c3_in_insert_q_nil : forall x : Q, In x (insert_q x []).
Proof.
  intro x. exact (in_eq x []).
Qed.

(* 〔零左因子产路·供 :2178 参数〕(a * b == 0)%Q 参数于 a := 0 左零
   元规范实例（就地构造：Qmult/Qeq 定义性展开＋Z 层 lia；
   P′ 申报位——源结论面 Prop 析取位，见④） *)
Theorem dtd_c3_qmul_eq0_l : forall b : Q, (0 * b == 0)%Q.
Proof.
  intro b. destruct b as [n d]. unfold Qmult, Qeq. simpl. lia.
Qed.

(* 〔零平方产路·供 :2220 参数〕(x * x == 0)%Q 参数于 x := (0 # 5)
   非规范零规范实例（Qmult/Qeq 定义性展开值层闭合；避开 x := 0 纯
   反射退化面） *)
Theorem dtd_c3_qsq0_fifth : ((0 # 5) * (0 # 5) == 0)%Q.
Proof.
  unfold Qmult, Qeq. simpl. reflexivity.
Qed.

(* 〔零平方和产路·供 :2226 参数〕(a * a + b * b == 0)%Q 参数于
   (a, b) := ((0 # 3), (0 # 5)) 非规范零对规范实例（Qplus/Qmult/Qeq
   定义性展开值层闭合；P′ 申报位——源结论面 Prop 合取位，见④） *)
Theorem dtd_c3_qsum_sq0_thirds :
  ((0 # 3) * (0 # 3) + (0 # 5) * (0 # 5) == 0)%Q.
Proof.
  unfold Qmult, Qplus, Qeq. simpl. reflexivity.
Qed.

(* 〔BOOL 判定假面产路·供 :2525 参数〕Qle_bool x y = false 参数于
   (x, y) := (2, 1) 具体规范实例（Z.leb 判定面定义性闭合） *)
Theorem dtd_c3_Qle_bool_2_1_false : Qle_bool 2 1 = false.
Proof.
  reflexivity.
Qed.

(* 〔SORTED 产路·供 :2642/:2673 双参数〕StronglySorted Qle l 参数于
   l := P0 l 规范实例（宿主 P0_sorted :2666 零前提产路转发——普查
   「SortedQ 有产路 xq_P0_sorted」锚位） *)
Theorem dtd_c3_P0_ssorted : forall l : list Q, StronglySorted Qle (P0 l).
Proof.
  intro l. apply P0_sorted.
Qed.

(* ============================================================ *)
(* 【只登记】七参数（底册 §2.3 混载旗位，照   :1612 先例只登记      *)
(* 不供给，失败显式申报 见交付报告 §四）：                               *)
(*   参数 79＝:1864 llm_Tex_fiber（exists 旗——源语句面 sigT 存在见证）    *)
(*   参数 81＝:1960 freq_zero_of_notQmem（否定旗——前件 ~ Qmem x l 位）    *)
(*   参数 96＝:2435 fiber_cozero_disjoint（否定旗——结论 ~ In 位）         *)
(*   参数 98＝:2455 fiber_cozero_compl（否定+iff 旗——结论双 Prop 位）     *)
(*   参数 100-101＝:2603 Forall_in（显式 Prop 旗——P : A -> Prop 注记位）  *)
(*   参数 102＝:2615 Forall_of_pointwise（显式 Prop 旗——同上）           *)
(* ============================================================ *)

(* ============================================================ *)
(* 二 供给定理区·P′ 无前提精简版（20 枚；宿主定理 @ 全实参显式应用，        *)
(*    参数消即出；结论面＝宿主结论面现档逐字特化，全离散承载）           *)
(* ============================================================ *)

(* P1〔:1663 llm_firstn_ge_full 参数 71〕表长自反实例无前提精简版：
   NAT 参数喂 dtd_c3_le_length_refl（n := length l），出 firstn 全表
   恒等面 *)
Theorem dtd_c3_firstn_length_id : forall l : list Q, firstn (length l) l = l.
Proof.
  intro l. exact (llm_firstn_ge_full (length l) l (dtd_c3_le_length_refl l)).
Qed.

(* P2〔:1674 llm_skipn_ge_nil 参数 72〕同 T 配方无前提精简版：出 skipn
   全舍空表面 *)
Theorem dtd_c3_skipn_length_nil : forall l : list Q, skipn (length l) l = [].
Proof.
  intro l. exact (llm_skipn_ge_nil (length l) l (dtd_c3_le_length_refl l)).
Qed.

(* P3〔:1739 llm_gate_pass_mono_thr 双参数 73-74〕阈值放宽双卫哨具体
   规范实例无前提精简版：Q-ORD 参数喂 dtd_c3_Qle_0_1（t1 := 0,
   t2 := 1）、BOOL 参数喂 dtd_c3_gate_pass_refl（H := t1 := 0），出
   阈值 0→1 放宽保通过面 gate_pass 1 0 = true *)
Theorem dtd_c3_gate_pass_mono_0_1 : gate_pass 1 0 = true.
Proof.
  exact (llm_gate_pass_mono_thr 0 0 1 dtd_c3_Qle_0_1 (dtd_c3_gate_pass_refl 0)).
Qed.

(* P4〔:1750 llm_gate_pass_anti_H 双参数 75-76〕判据量反单调双卫哨
   具体规范实例无前提精简版：Q-ORD 参数喂 dtd_c3_Qle_0_2（H1 := 0,
   H2 := 2）、BOOL 参数喂 dtd_c3_gate_pass_refl（t := H2 := 2），出
   判据量 2→0 降值保通过面 gate_pass 2 0 = true *)
Theorem dtd_c3_gate_pass_anti_0_2 : gate_pass 2 0 = true.
Proof.
  exact (llm_gate_pass_anti_H 0 2 2 dtd_c3_Qle_0_2 (dtd_c3_gate_pass_refl 2)).
Qed.

(* P5〔:1789 llm_rot_cyclic_inv 参数 77〕零切规范实例无前提精简版：
   NAT 参数喂 dtd_c3_nat_le_0_length（n := 0），出 rot 恒等面
   （rot 定义性 firstn ++ skipn 恒等于原表的循环逆元形规范实例） *)
Theorem dtd_c3_rot_cyclic_inv_0 :
  forall l : list Q, rot (length l - 0) (rot 0 l) = l.
Proof.
  intro l. exact (llm_rot_cyclic_inv 0 l (dtd_c3_nat_le_0_length l)).
Qed.

(* P6〔:1846 llm_Pmid_full 参数 78〕表长端点规范实例无前提精简版：
   NAT 参数喂 dtd_c3_le_length_refl（lam := length l），出 Pmid 满端点
   恒为 P0 面（宿主证内 assert 同款配方独立成面） *)
Theorem dtd_c3_Pmid_full_length :
  forall (l : list Q) (s : nat), Pmid l s (length l) = P0 l.
Proof.
  intros l s. exact (llm_Pmid_full l s (length l) (dtd_c3_le_length_refl l)).
Qed.

(* P7〔:1938 freq_eq_congr 参数 80〕非规范同值对实例无前提精简版：
   Q-ORD 参数喂 dtd_c3_Qeq_half（x := 2 # 2, y := 1 # 1），出判等换名
   不换频非退化面 *)
Theorem dtd_c3_freq_eq_congr_half :
  forall l : list Q, freq l (2 # 2) = freq l (1 # 1).
Proof.
  intro l. exact (freq_eq_congr (2 # 2) (1 # 1) l dtd_c3_Qeq_half).
Qed.

(* P8〔:1987 freq_perm 参数 82〕rev 实例无前提精简版：PERM 参数喂
   dtd_c3_perm_rev（p := rev l，避开 p := l 自反退化面——  P16
   同款实例形防撞纪律），出频数沿反转不变面 *)
Theorem dtd_c3_freq_perm_rev :
  forall (l : list Q) (x : Q), freq l x = freq (rev l) x.
Proof.
  intros l x. exact (freq_perm l (rev l) x (dtd_c3_perm_rev l)).
Qed.

(* P9〔:2012 sumf_dedup_aux 参数 83〕支撑面 dedup 规范实例无前提精简
   版：Qnodup 参数喂 dtd_c3_Qnodup_dedup（m := dedup l），出总质量
   Sigma_freq 搬账方程面（结论面 if/existsb 全数据位，零 Prop 逻辑词） *)
Theorem dtd_c3_sumf_dedup_aux_dedup : forall (x : Q) (l : list Q),
  sumf (dedup l) l
  = ((if existsb (fun z => Qeq_bool x z) (dedup l) then freq l x else O)
     + sumf (dedup_aux x (dedup l)) (x :: l))%nat.
Proof.
  intros x l. exact (sumf_dedup_aux (dedup l) x l (dtd_c3_Qnodup_dedup l)).
Qed.

(* P10〔:2075 mu_perm 参数 84〕rev 实例无前提精简版：PERM 参数喂
   dtd_c3_perm_rev（同 P8 防撞纪律），出均匀测度沿反转不变面 *)
Theorem dtd_c3_mu_perm_rev :
  forall (l : list Q) (x : Q), mu l x = mu (rev l) x.
Proof.
  intros l x. exact (mu_perm l (rev l) x (dtd_c3_perm_rev l)).
Qed.

(* P11〔:2107 mu_total_mass 参数 85〕单元素表规范实例无前提精简版：
   NEQ 参数喂 dtd_c3_cons_neq_nil（l := [x] 透传形），出单点分布质量
   恰一面 *)
Theorem dtd_c3_mu_total_mass_sing :
  forall x : Q, qsum (map (mu [x]) (dedup [x])) == 1.
Proof.
  intro x. exact (mu_total_mass [x] (dtd_c3_cons_neq_nil x [])).
Qed.

(* P12〔:2172 qeq_le 参数 86〕非规范同值对实例无前提精简版：Q-ORD 参数
   喂 dtd_c3_Qeq_half（同  配方），出 Qeq→Qle 桥非退化面 *)
Theorem dtd_c3_qeq_le_half : ((2 # 2) <= (1 # 1))%Q.
Proof.
  exact (qeq_le (2 # 2) (1 # 1) dtd_c3_Qeq_half).
Qed.

(* P13〔:2188 qmul_eq0_intro_l 参数 88〕非规范零左实例无前提精简版：
   Q-ORD 参数喂 dtd_c3_Qeq_0_third（a := 0 # 3），出零因子进入左位
   全称族面 *)
Theorem dtd_c3_qmul_eq0_intro_l_third : forall b : Q, ((0 # 3) * b == 0)%Q.
Proof.
  intro b. exact (qmul_eq0_intro_l (0 # 3) b dtd_c3_Qeq_0_third).
Qed.

(* P14〔:2196 qmul_eq0_intro_r 参数 89〕非规范零右实例无前提精简版：
   Q-ORD 参数喂 dtd_c3_Qeq_0_third（b := 0 # 3），出零因子进入右位
   全称族面 *)
Theorem dtd_c3_qmul_eq0_intro_r_third : forall a : Q, (a * (0 # 3) == 0)%Q.
Proof.
  intro a. exact (qmul_eq0_intro_r a (0 # 3) dtd_c3_Qeq_0_third).
Qed.

(* P15〔:2220 qsq_eq0 参数 90〕非规范零实例无前提精简版：Q-ORD 参数喂
   dtd_c3_qsq0_fifth（x := 0 # 5），出平方零 ⟹ 因子零面（结论面
   (0 # 5) == 0 系 Qeq 值层非平凡位——与  异值防面重合） *)
Theorem dtd_c3_qsq_eq0_fifth : (0 # 5 == 0)%Q.
Proof.
  exact (qsq_eq0 (0 # 5) dtd_c3_qsq0_fifth).
Qed.

(* P16〔:2252 qsum_sq_zero_intro 双参数 92-93〕双零因子具体实例无前提
   精简版：双 Q-ORD 参数喂 dtd_c3_Qeq_refl（a := b := 0 自反实例），
   出反向构造面（与  异形防 P′/T 面重合） *)
Theorem dtd_c3_qsum_sq_zero_intro_zero00 : (0 * 0 + 0 * 0 == 0)%Q.
Proof.
  exact (qsum_sq_zero_intro 0 0 (dtd_c3_Qeq_refl 0) (dtd_c3_Qeq_refl 0)).
Qed.

(* P17〔:2412 ideal_sub_closed 双参数 94-95〕单点理想规范实例无前提
   精简版：子集卫哨参数于 f := (fun _ => 0) 内联构造（fiber_in 实形
   In x w /\ Qeq_bool (f x) 0 = true 合取序——检验 Show 实拍）、
   In 参数喂 dtd_c3_in_cons 头位构造，出指示零函数纤维成员面 *)
Theorem dtd_c3_ideal_sub_closed_sing : forall a : Q,
  In a (fiber (fun y : Q => if in_dec Q_dec y [a] then 0 else 1) [a]).
Proof.
  intros a.
  apply (ideal_sub_closed [a] (fun _ : Q => 0) [a] a).
  - intros y Hy. simpl in Hy. destruct Hy as [Hy | Hf].
    + subst y. apply (proj2 (fiber_in (fun _ : Q => 0) [a] a)).
      * split.
        -- exact (in_eq a []).
        -- reflexivity.
    + destruct Hf.
  - exact (in_eq a []).
Qed.

(* P18〔:2525 Qle_bool_false_inv 参数 99〕判定假面具体实例无前提精简
   版：BOOL 参数喂 dtd_c3_Qle_bool_2_1_false（x := 2, y := 1），出
   判假反序面 (1 <= 2)%Q（与 / 异形防面重合） *)
Theorem dtd_c3_Qle_bool_false_inv_1_2 : (1 <= 2)%Q.
Proof.
  exact (Qle_bool_false_inv 2 1 dtd_c3_Qle_bool_2_1_false).
Qed.

(* P19〔:2642 insert_sorted 参数 104〕P0 规范形迁移无前提精简版：
   SORTED 参数喂 dtd_c3_P0_ssorted（l := P0 l），出插入保序 P0 面 *)
Theorem dtd_c3_insert_sorted_P0 : forall (x : Q) (l : list Q),
  StronglySorted Qle (insert_q x (P0 l)).
Proof.
  intros x l. exact (insert_sorted x (P0 l) (dtd_c3_P0_ssorted l)).
Qed.

(* P20〔:2673 sorted_P0_id 参数 105〕P0 幂等规范实例无前提精简版：
   SORTED 参数喂 dtd_c3_P0_ssorted（l := P0 l），出排序幂等面
   P0 (P0 l) = P0 l *)
Theorem dtd_c3_sorted_P0_idem : forall l : list Q, P0 (P0 l) = P0 l.
Proof.
  intro l. exact (sorted_P0_id (P0 l) (dtd_c3_P0_ssorted l)).
Qed.

(* ============================================================ *)
(* 【T 单独交付】四参数响亮申报位（非失败位， :262／ 卷二先例同款）：  *)
(*   参数 87＝:2178 qmul_eq0_fwd—— dtd_c3_qmul_eq0_l 单独交付，        *)
(*          P′ ＝源结论面 Prop 析取位（a == 0 \/ b == 0）；          *)
(*   参数 91＝:2226 qsum_sq_zero—— dtd_c3_qsum_sq0_thirds 单独交付，   *)
(*          P′ ＝源结论面 Prop 合取位（a == 0 /\ b == 0）；          *)
(*   参数 97＝:2445 fiber_cozero_cover—— dtd_c3_in_cons 单独交付，     *)
(*          P′ ＝源结论面 Prop 析取位；                             *)
(*   参数 103＝:2625 in_insert_q—— dtd_c3_in_insert_q_nil 单独交付，   *)
(*          P′ ＝源结论面 Prop 析取位（z = x \/ In z l）。           *)
(* ============================================================ *)

(* ============================================================ *)
(* 三 尾置验印区（文件最尾）：Check 印＋逐件承认面验印——              *)
(*    名清单＝38 供给定理（18 T＋20 P′）＝Qed 计数 38 零差             *)
(* ============================================================ *)

Check dtd_c3_le_length_refl.
Check dtd_c3_nat_le_0_length.
Check dtd_c3_gate_pass_refl.
Check dtd_c3_Qle_0_1.
Check dtd_c3_Qle_0_2.
Check dtd_c3_Qeq_refl.
Check dtd_c3_Qeq_half.
Check dtd_c3_Qeq_0_third.
Check dtd_c3_perm_rev.
Check dtd_c3_cons_neq_nil.
Check dtd_c3_Qnodup_dedup.
Check dtd_c3_in_cons.
Check dtd_c3_in_insert_q_nil.
Check dtd_c3_qmul_eq0_l.
Check dtd_c3_qsq0_fifth.
Check dtd_c3_qsum_sq0_thirds.
Check dtd_c3_Qle_bool_2_1_false.
Check dtd_c3_P0_ssorted.
Check dtd_c3_firstn_length_id.
Check dtd_c3_skipn_length_nil.
Check dtd_c3_gate_pass_mono_0_1.
Check dtd_c3_gate_pass_anti_0_2.
Check dtd_c3_rot_cyclic_inv_0.
Check dtd_c3_Pmid_full_length.
Check dtd_c3_freq_eq_congr_half.
Check dtd_c3_freq_perm_rev.
Check dtd_c3_sumf_dedup_aux_dedup.
Check dtd_c3_mu_perm_rev.
Check dtd_c3_mu_total_mass_sing.
Check dtd_c3_qeq_le_half.
Check dtd_c3_qmul_eq0_intro_l_third.
Check dtd_c3_qmul_eq0_intro_r_third.
Check dtd_c3_qsq_eq0_fifth.
Check dtd_c3_qsum_sq_zero_intro_zero00.
Check dtd_c3_ideal_sub_closed_sing.
Check dtd_c3_Qle_bool_false_inv_1_2.
Check dtd_c3_insert_sorted_P0.
Check dtd_c3_sorted_P0_idem.

Print Assumptions dtd_c3_le_length_refl.
Print Assumptions dtd_c3_nat_le_0_length.
Print Assumptions dtd_c3_gate_pass_refl.
Print Assumptions dtd_c3_Qle_0_1.
Print Assumptions dtd_c3_Qle_0_2.
Print Assumptions dtd_c3_Qeq_refl.
Print Assumptions dtd_c3_Qeq_half.
Print Assumptions dtd_c3_Qeq_0_third.
Print Assumptions dtd_c3_perm_rev.
Print Assumptions dtd_c3_cons_neq_nil.
Print Assumptions dtd_c3_Qnodup_dedup.
Print Assumptions dtd_c3_in_cons.
Print Assumptions dtd_c3_in_insert_q_nil.
Print Assumptions dtd_c3_qmul_eq0_l.
Print Assumptions dtd_c3_qsq0_fifth.
Print Assumptions dtd_c3_qsum_sq0_thirds.
Print Assumptions dtd_c3_Qle_bool_2_1_false.
Print Assumptions dtd_c3_P0_ssorted.
Print Assumptions dtd_c3_firstn_length_id.
Print Assumptions dtd_c3_skipn_length_nil.
Print Assumptions dtd_c3_gate_pass_mono_0_1.
Print Assumptions dtd_c3_gate_pass_anti_0_2.
Print Assumptions dtd_c3_rot_cyclic_inv_0.
Print Assumptions dtd_c3_Pmid_full_length.
Print Assumptions dtd_c3_freq_eq_congr_half.
Print Assumptions dtd_c3_freq_perm_rev.
Print Assumptions dtd_c3_sumf_dedup_aux_dedup.
Print Assumptions dtd_c3_mu_perm_rev.
Print Assumptions dtd_c3_mu_total_mass_sing.
Print Assumptions dtd_c3_qeq_le_half.
Print Assumptions dtd_c3_qmul_eq0_intro_l_third.
Print Assumptions dtd_c3_qmul_eq0_intro_r_third.
Print Assumptions dtd_c3_qsq_eq0_fifth.
Print Assumptions dtd_c3_qsum_sq_zero_intro_zero00.
Print Assumptions dtd_c3_ideal_sub_closed_sing.
Print Assumptions dtd_c3_Qle_bool_false_inv_1_2.
Print Assumptions dtd_c3_insert_sorted_P0.
Print Assumptions dtd_c3_sorted_P0_idem.

(* ============================================================ *)
(* 四 提取检验区（红线四：可提取验证，Obj.magic 计数＝0 判据）          *)
(*    定理桶：单条 Separate Extraction（  避坑——同文件      *)
(*    双命令同名覆写坑禁触），38 定理结论面全数 Prop 离散承载，按      *)
(*    家族提取擦除惯例归约 __ 占位；数据层真提取面＝P′ 语句面所使用     *)
(*    宿主数据承载（insert_q/P0/rot/Pmid/gate_pass/freq/sumf/dedup/    *)
(*    dedup_aux/mu/fiber/cozero/Q_dec），归独立检验件                   *)
(*    _dtd_c3_probe.v 定向  另桶（分桶工艺执行位）。    *)
(* ============================================================ *)

Set Extraction Output Directory "_log/dtd_t4".
Separate Extraction dtd_c3_le_length_refl
  dtd_c3_nat_le_0_length dtd_c3_gate_pass_refl dtd_c3_Qle_0_1
  dtd_c3_Qle_0_2 dtd_c3_Qeq_refl dtd_c3_Qeq_half dtd_c3_Qeq_0_third
  dtd_c3_perm_rev dtd_c3_cons_neq_nil dtd_c3_Qnodup_dedup
  dtd_c3_in_cons dtd_c3_in_insert_q_nil dtd_c3_qmul_eq0_l
  dtd_c3_qsq0_fifth dtd_c3_qsum_sq0_thirds dtd_c3_Qle_bool_2_1_false
  dtd_c3_P0_ssorted dtd_c3_firstn_length_id dtd_c3_skipn_length_nil
  dtd_c3_gate_pass_mono_0_1 dtd_c3_gate_pass_anti_0_2
  dtd_c3_rot_cyclic_inv_0 dtd_c3_Pmid_full_length
  dtd_c3_freq_eq_congr_half dtd_c3_freq_perm_rev
  dtd_c3_sumf_dedup_aux_dedup dtd_c3_mu_perm_rev
  dtd_c3_mu_total_mass_sing dtd_c3_qeq_le_half
  dtd_c3_qmul_eq0_intro_l_third dtd_c3_qmul_eq0_intro_r_third
  dtd_c3_qsq_eq0_fifth dtd_c3_qsum_sq_zero_intro_zero00
  dtd_c3_ideal_sub_closed_sing dtd_c3_Qle_bool_false_inv_1_2
  dtd_c3_insert_sorted_P0 dtd_c3_sorted_P0_idem.
