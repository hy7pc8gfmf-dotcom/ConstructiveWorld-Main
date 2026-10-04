(* ==========================================================================
   abl_dtd_core4.v —— DTPT 本体前件参数消解供给·卷四收尾（参数 106–138）。
   ── 使命：宿主 DTPT.v 前件参数登记序第 106–138 位（语句坐标 :2710–:3758，
   28 条语句 33 参数，卷界零重叠，138 参数就此收尾）逐参数按形态二 T＋P′
   消解供给：T＝参数面产路（守卫单点规范形／置换构造子 sym·rev·swap／排序
   唯一性应用形／计算性空表规范实例／成员构造子／判等门卫／外延链／恒开门
   归纳），P′＝宿主结论面现档逐字特化。33 参数＝31 供给＋2 登记
   （count_q_pos_wit 存在体旗＋真顶层前件／phase_classify_Mid_spec 否定＋
   合取旗，照登记不供给）；三参数 Tex_of_Tabs（防与宿主在册件双供）／
   OrgDiff_nonneg_transport／llm_view_PhP0_consistent（源结论面 Prop 合取
   位）以 T 产路单独交付。宿主件零字节动零级联。
   ── 依赖：DTPT（P0_sorted／count_q_perm／freq_filter_eq_all 等在役件即
   产路出处）＋stdlib（QArith.QArith／Qabs、List、Arith Lia、Permutation、
   Sorting.Sorted、Extraction）。
   ── 对标行：T＋P′ 形态二先例＝abl_tbn_supply_b；反转不变产路出处＝宿主
   C_gen_sym_rev（H_adj (rev l) == H_adj l 在役件）；stdlib 无 Qlt_bool
   判定面（本卷无严格序判定器需求位）。
   ── 构造性注记：零承认式声明、零悬置前提、零经典逻辑，全部结论 Qed 真构造
   闭合；供给语句面零混载形态（零裸 exists／零 iff／零 -> False／零 sumbool
   位）；<> 全件仅 dtd_c4_cons_neq_nil 一处＝NEQ 参数面逐字透传（非自造）；
   名面全 dtd_c4_ 前缀（与 dtd_／dtd_c2_／dtd_c3_ 中缀隔离）；尾置逐件
   Print Assumptions Closed＋定理桶单条 Separate Extraction（本件零新增
   数据层，单桶单命令），Obj.magic 零判据。
   ── 编译配方：池 cwd＝沙箱/现役/abl_r85_supply_pool；source Live 库根
   toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 后 nice -19
   rocq c -native-compiler no
   -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
   abl_dtd_core4.v；绿判＝EXIT=0／日志零 Error／.vo 头 8 字节
   436f7121 00015ff4／.vo 新于 .v；第五证 rocq check；产物只落本池。
   ========================================================================== *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

Require DTPT.
Import DTPT.DTPT.

(* ============================================================ *)
(* §一 共用卫哨/证书产路区（供给定理 T·17 枚）                     *)
(*    逐枚＝底册参数面的构造性产路：排序唯一性 SORTED 产路、置换      *)
(*    构造子路（sym/rev/swap）、计数三跳链、计算性空表规范实例路、  *)
(*    成员构造子路（fiber/dedup/cons）、判等门卫路、Qopp 外延链、   *)
(*    恒开门归纳路、OrgDiff 空表规范实例路。                       *)
(* ============================================================ *)

(* 〔SORTED 产路·供 :2987 参数 1/2〕P0 规范形强有序：P0_sorted 在役
   产路转发（普查「SortedQ 有产路」锚的 StronglySorted 面；
   平凡转发位申报见交付报告） *)
Theorem dtd_c4_P0_ssorted : forall l : list Q, StronglySorted Qle (P0 l).
Proof.
  intro l. exact (P0_sorted l).
Qed.

(* 〔EQ count 链产路·供 :2987 参数 3〕P0 与 P0(rev) 数值重数相等：
   count_q_perm 置换传递三跳链（D5_P0_perm l｜Permutation_rev l｜
   D5_P0_perm (rev l)）——排序唯一性应用形 P5 的计数等式输入源；
   非平凡位（三跳复合，非宿主别名转发） *)
Theorem dtd_c4_count_P0_P0rev : forall (l : list Q) (x : Q),
  count_q x (P0 l) = count_q x (P0 (rev l)).
Proof.
  intros l x.
  rewrite <- (count_q_perm l (P0 l) (D5_P0_perm l) x).
  rewrite (count_q_perm l (rev l) (Permutation_rev l) x).
  exact (count_q_perm (rev l) (P0 (rev l)) (D5_P0_perm (rev l)) x).
Qed.

(* 〔PERM 产路·供 :3035/:3079 两参数〕置换对称构造子路：
   Permutation p l ⟹ Permutation l p（stdlib Permutation_sym 构造子
   一击，普查「Permutation 有构造子」锚；/ 同款产路；
   平凡位申报见交付报告） *)
Theorem dtd_c4_perm_sym : forall l p : list Q,
  Permutation p l -> Permutation l p.
Proof.
  intros l p Hperm. exact (Permutation_sym Hperm).
Qed.

(* 〔Forall2 单点构造产路·供 :3050/:3074 两参数〕逐点 Qeq 的单点表
   Forall2 形：Forall2_cons＋Forall2_nil 两步构造（EQ 参数面
   Forall2 Qeq l1 l2 的规范实例输入源） *)
Theorem dtd_c4_Forall2_Qeq_single : forall x y : Q,
  x == y -> Forall2 Qeq [x] [y].
Proof.
  intros x y H. apply Forall2_cons; [exact H | apply Forall2_nil].
Qed.

(* 〔计算性空表规范实例产路·供 :3108/:3742/:3758 三参数〕空表相位
   恒判 P0：phase_classify [] s = PhP0（空表 P0/Pinf/Pmid 全退化、
   H_adj 空表为零、Qeq_bool 0 0 判真——reflexivity 定义性闭合，
   检验实测；三参数共用的判定器判真规范实例） *)
Theorem dtd_c4_phase_classify_nil_PhP0 : forall s : nat,
  phase_classify [] s = PhP0.
Proof.
  intro s. reflexivity.
Qed.

(* 〔PERM 二元素对换构造子路·供 :3144 参数 1〕长度 2 对换置换类：
   Permutation [x; y] [y; x]（perm_swap 构造子一击；普查
   「Permutation 有构造子」锚的具例） *)
Theorem dtd_c4_perm_swap_pair : forall x y : Q,
  Permutation [x; y] [y; x].
Proof.
  intros x y. apply perm_swap.
Qed.

(* 〔Q-ORD 旋转熵等式产路·供 :3144 参数 2〕二元素对换的旋转熵数值
   重合：H_adj (Pinf [x; y] 0) == H_adj (Pinf [y; x] 0)——Pinf/rot
   于 s:=0 经 firstn_skipn 退化为恒等表，反转不变由宿主在役件
   C_gen_sym_rev（:940 H_adj (rev l) == H_adj l）承载（rev [x;y] 于
   [x;y] 定义性归约；非平凡位：定义性退化＋在役件换向复合） *)
Theorem dtd_c4_H_inf_swap_pair_eq : forall x y : Q,
  (H_adj (Pinf [x; y] 0) == H_adj (Pinf [y; x] 0))%Q.
Proof.
  intros x y. unfold Pinf, rot. rewrite !firstn_skipn.
  apply Qeq_sym. exact (C_gen_sym_rev [x; y]).
Qed.

(* 〔IN 纤维成员构造产路·供 :3477 参数〕常零观测单点纤维成员：
   In x (fiber (fun _ => 0) [x])（fiber=filter 判零语义定义性展开，
   Qeq_bool 0 0 判真⟹头位成员；计算性产路，检验实测） *)
Theorem dtd_c4_in_fiber_zero_single : forall x : Q,
  In x (fiber (fun _ => 0%Q) [x]).
Proof.
  intro x. unfold fiber. simpl. left. reflexivity.
Qed.

(* 〔NEQ 非空卫哨产路·供 :3502/:3610 两参数〕cons 形：
   x :: l <> [] 头构造判别（卫哨 cons 构造子路；普查「卫哨可平凡
   供给」锚；<> 系 NEQ 参数面逐字，/ 同款任务指定透传形；
   平凡位申报见交付报告） *)
Theorem dtd_c4_cons_neq_nil : forall (x : Q) (l : list Q),
  (x :: l) <> [].
Proof.
  intros x l H. discriminate H.
Qed.

(* 〔IN dedup_aux 成员构造产路·供 :3537 参数〕判假分支头位成员：
   Qeq_bool x a = false ⟹ In a (dedup_aux x (a :: t))——dedup_aux
   判假分支保头语义（  勘注：目标侧 if 以 rewrite 判值直代换，
   非 destruct 拆析取） *)
Theorem dtd_c4_in_dedup_aux_cons_neq : forall (x a : Q) (t : list Q),
  Qeq_bool x a = false -> In a (dedup_aux x (a :: t)).
Proof.
  intros x a t H. simpl. rewrite H. simpl. left. reflexivity.
Qed.

(* 〔IN dedup 头成员构造产路·供 :3549 参数〕头位无条件成员：
   In a (dedup (a :: t))——dedup cons 支定义性展开头位恒保
   （dedup (x :: xs) = x :: dedup_aux x (dedup xs)，头位成员与
   判定分支无关；计算性产路） *)
Theorem dtd_c4_in_dedup_head : forall (a : Q) (t : list Q),
  In a (dedup (a :: t)).
Proof.
  intros a t. simpl. left. reflexivity.
Qed.

(* 〔BOOL+IN+Q-ORD 判等门卫产路·供 :3562 参数〕y 全同票开门：
   In a l -> a == y -> Qeq_bool a y = true（Qeqb_true_of 判定桥
   正向一击；门卫 face 的规范构造） *)
Theorem dtd_c4_gate_Qeq_y : forall (l : list Q) (y a : Q),
  In a l -> a == y -> Qeq_bool a y = true.
Proof.
  intros l y a _ Ha. apply Qeqb_true_of. exact Ha.
Qed.

(* 〔EXT 外延链产路·供 :3581 参数 1/:3610 参数 2〕Qopp 保 Qeq：
   x == y ⟹ - x == - y（Qminus_comp Proper 实例喂 0 - x == 0 - y，
   Qplus_0_l 双端回接——自足推导非转发；勘注：Z 直展路撞 Q 记录
   投影实名 Qden 小写 cbn 面，检验实测弃；非平凡位对照申报） *)
Theorem dtd_c4_ext_Qopp : forall x y : Q, x == y -> (- x == - y)%Q.
Proof.
  intros x y H.
  apply (Qeq_trans (- x) (0 + (- x)) (- y)).
  - apply Qeq_sym. apply Qplus_0_l.
  - apply (Qeq_trans (0 + (- x)) (0 + (- y)) (- y)).
    + change (0 - x == 0 - y)%Q.
      apply Qminus_comp; [apply Qeq_refl | exact H].
    + apply Qplus_0_l.
Qed.

(* 〔EXT 恒开门归纳产路·供 :3595 参数〕恒开门 filter 逐点保频：
   freq (filter (fun _ => true) l) y = freq l y——归纳直证（cons 支
   Qeq_bool 拆支后 lia 闭合；非平凡位：本件独立设计归纳，非宿主
   别名转发；sumf_ext 点喂的同门全开规范实例——y 门点喂对 y0≠y
   不成立之勘注见检验件实测） *)
Theorem dtd_c4_freq_filter_all_true : forall (l : list Q) (y : Q),
  freq (filter (fun _ => true) l) y = freq l y.
Proof.
  intro l. induction l as [| a t IH]; intro y; simpl.
  - reflexivity.
  - specialize (IH y). destruct (Qeq_bool a y); lia.
Qed.

(* 〔Q-ORD 计算性规范实例产路·供 :3669 参数〕空表组织差非负：
   0 <= OrgDiff [] s——OrgDiff [] s = H_adj (Pinf [] s) - H_adj (P0 [])
   定义性归约为 0 - 0 = 0（Pinf/P0/H_adj/Qminus 全退化，replace
   reflexivity 闭合；计算性产路，检验实测） *)
Theorem dtd_c4_OrgDiff_nil_nonneg : forall s : nat,
  (0 <= OrgDiff [] s)%Q.
Proof.
  intro s. replace (OrgDiff [] s) with 0%Q by reflexivity.
  apply Qle_refl.
Qed.

(* 〔PERM rev 产路·供 :2957 参数〕反转置换构造子路：
   Permutation l (rev l)（stdlib Permutation_rev 构造子转发——
   :2957 参数 P′ rev 形的置换输入源；平凡转发位申报见交付报告） *)
Theorem dtd_c4_perm_rev : forall l : list Q, Permutation l (rev l).
Proof.
  intro l. apply Permutation_rev.
Qed.

(* 〔EQ 常量证据产路·供 :2886 参数〕Tabs 常量证据族：
   forall (phi : Dig) (m' : Dig), Evidence——宿主在役件
   llm_Tabs_const（:1877，口径二显式构造）转发（Tabs phi 定义性
   展开＝参数面 forall m' : Dig, Evidence；平凡转发位申报见交付
   报告；该参数 P′ ＝应用形无条件面与在册 Tex_inhabited R-2 防双供） *)
Theorem dtd_c4_Tabs_const : forall (phi : Dig) (m' : Dig), Evidence.
Proof.
  intros phi m'. exact (llm_Tabs_const phi m').
Qed.

(* ============================================================ *)
(* §二 P′ 精简版区（23 枚·覆盖 28 参数；＋T 单独交付 3 参数＝31 参数供给）  *)
(*    逐枚＝宿主定理 @ 全实参显式应用＋参数由 §一 产路（或守卫/le_n/in_eq/  *)
(*    discriminate/gate reflexivity 内联构造）输入，出精简版；       *)
(*    语句面＝宿主结论面现档逐字特化（离散承载）。三参数 P′       *)
(*    （:2886/:3669/:3742，见④）。                                 *)
(* ============================================================ *)

(* P1〔:2710 H_adj_bound 参数〕相邻差总和单点界守卫内联无前提精简版：
   IN+Q-ORD 守卫参数以单点规范形内联输入（In x0 [x] 开析＝subst +
   Qle_refl），出 H_adj [x] 单点上界面 *)
Theorem dtd_c4_H_adj_bound_single : forall x : Q,
  (H_adj [x] <= (Z.of_nat (length [x]) # 1) * Qabs x * 2)%Q.
Proof.
  intro x. apply (H_adj_bound [x] (Qabs x)).
  intros x0 Hx. destruct Hx as [Heq | Hc].
  - subst x0. apply Qle_refl.
  - destruct Hc.
Qed.

(* P2〔:2853 Hsup_bounded 参数〕有穷上界单点界守卫内联无前提精简版：
   同 P1 守卫内联配方喂宿主，出 Hsup [x] n 单点上界面（n 全称保留
   ＝动态上确界族逐点有界） *)
Theorem dtd_c4_Hsup_bounded_single : forall (x : Q) (n : nat),
  (Hsup [x] n <= (Z.of_nat (length [x]) # 1) * Qabs x * 2)%Q.
Proof.
  intros x n. apply (Hsup_bounded [x] n (Qabs x)).
  intros x0 Hx. destruct Hx as [Heq | Hc].
  - subst x0. apply Qle_refl.
  - destruct Hc.
Qed.

(* P3〔:2917 swap_adj_oob 参数〕越界恒等界内规范形无前提精简版：
   NAT 参数以 n := length l 喂 le_n 内联，出 swap_adj l (length l) = l
   （界内边界实例：对换下标恰达表长时恒等） *)
Theorem dtd_c4_swap_adj_oob_len : forall l : list Q,
  swap_adj l (length l) = l.
Proof.
  intro l. apply (swap_adj_oob l (length l)). apply le_n.
Qed.

(* P4〔:2957 count_q_perm 参数〕置换不变 rev 形无前提精简版：
   PERM 参数喂 dtd_c4_perm_rev，出 count_q x l = count_q x (rev l)
   面（数值重数反转不变规范实例） *)
Theorem dtd_c4_count_q_perm_rev : forall (l : list Q) (x : Q),
  count_q x l = count_q x (rev l).
Proof.
  intros l x. exact (count_q_perm l (rev l) (dtd_c4_perm_rev l) x).
Qed.

(* P5〔:2987 sorted_perm_count_qeq 三参数〕排序唯一性 P0-rev 迁移形
   无前提精简版：双 SORTED 参数喂 dtd_c4_P0_ssorted、计数等式参数喂
   dtd_c4_count_P0_P0rev（三参数全消），出 Forall2 Qeq (P0 l)
   (P0 (rev l)) 面（排序形只依赖数值多重集的 rev 规范实例） *)
Theorem dtd_c4_sorted_perm_count_qeq_P0rev : forall l : list Q,
  Forall2 Qeq (P0 l) (P0 (rev l)).
Proof.
  intro l. apply (sorted_perm_count_qeq (P0 l) (P0 (rev l))).
  - exact (dtd_c4_P0_ssorted l).
  - exact (dtd_c4_P0_ssorted (rev l)).
  - intro x. exact (dtd_c4_count_P0_P0rev l x).
Qed.

(* P6〔:3035 P0_perm_inv 参数〕P0 置换不变对称换向形精简版：
   PERM 参数经 dtd_c4_perm_sym 换向后喂宿主，出 Forall2 Qeq (P0 l)
   (P0 p) 面（  P9 对称换向应用形同款——自反实例应用形出
   Forall2 (P0 l) (P0 l) 面与参数 115 语义重合，故取 sym 复合面
   避开 R-2 自dup） *)
Theorem dtd_c4_P0_perm_inv_sym : forall l p : list Q,
  Permutation p l -> Forall2 Qeq (P0 l) (P0 p).
Proof.
  intros l p Hperm. exact (P0_perm_inv l p (dtd_c4_perm_sym l p Hperm)).
Qed.

(* P7〔:3050 sum_adjdiff_qeq 参数〕相邻差总和逐点 Qeq 单点形无前提
   精简版：Forall2 参数喂 dtd_c4_Forall2_Qeq_single，出
   sum_adjdiff [x] == sum_adjdiff [y] 面 *)
Theorem dtd_c4_sum_adjdiff_qeq_single : forall x y : Q,
  x == y -> sum_adjdiff [x] == sum_adjdiff [y].
Proof.
  intros x y H. exact (sum_adjdiff_qeq [x] [y]
                         (dtd_c4_Forall2_Qeq_single x y H)).
Qed.

(* P8〔:3074 H_adj_qeq 参数〕相邻差熵逐点 Qeq 单点形无前提精简版：
   同 P7 配方喂宿主，出 H_adj [x] == H_adj [y] 面 *)
Theorem dtd_c4_H_adj_qeq_single : forall x y : Q,
  x == y -> H_adj [x] == H_adj [y].
Proof.
  intros x y H. exact (H_adj_qeq [x] [y]
                         (dtd_c4_Forall2_Qeq_single x y H)).
Qed.

(* P9〔:3079 H_adj_P0_perm 参数〕熵置换不变对称换向形精简版：
   PERM 参数经 dtd_c4_perm_sym 换向后喂宿主，出 H_adj (P0 l) ==
   H_adj (P0 p) 面（  P9 C_gen 对称面同款配方——本件供
   H_adj_P0_perm 本面之对称形，与 dtd_c2_C_gen_sym 的 Qle 承载
   C_gen 面异参数异面零撞） *)
Theorem dtd_c4_H_adj_P0_perm_sym : forall l p : list Q,
  Permutation p l -> (H_adj (P0 l) == H_adj (P0 p))%Q.
Proof.
  intros l p Hperm. exact (H_adj_P0_perm l p (dtd_c4_perm_sym l p Hperm)).
Qed.

(* P10〔:3108 phase_classify_P0_spec 参数〕判定器判 P0 熵重合空表形
   无前提精简版：EQ 参数喂 dtd_c4_phase_classify_nil_PhP0，出
   H_adj (P0 []) == H_adj (Pmid [] s 0) 面（P0 相充分条件回读的
   空表规范实例；面经计算性退化 0 == 0——平凡位申报见交付报告，
   应用形本体照宿主参数面逐字特化） *)
Theorem dtd_c4_phase_classify_P0_spec_nil : forall s : nat,
  (H_adj (P0 []) == H_adj (Pmid [] s 0))%Q.
Proof.
  intro s. apply (phase_classify_P0_spec ([] : list Q) s).
  exact (dtd_c4_phase_classify_nil_PhP0 s).
Qed.

(* P11〔:3144 phase_classify_perm_inv_cond 双参数〕相位判定置换不变
   条件形 swap 对无前提精简版：PERM 参数喂 dtd_c4_perm_swap_pair、
   Q-ORD 参数喂 dtd_c4_H_inf_swap_pair_eq（双参数全消），出
   phase_classify [x; y] 0 = phase_classify [y; x] 0 面（D12.2
   有序性本体：旋转参数熵重合条件下判定对对换不变的规范实例） *)
Theorem dtd_c4_phase_classify_perm_inv_cond_swap2 : forall x y : Q,
  phase_classify [x; y] 0 = phase_classify [y; x] 0.
Proof.
  intros x y. apply (phase_classify_perm_inv_cond [x; y] [y; x] 0).
  - exact (dtd_c4_perm_swap_pair x y).
  - exact (dtd_c4_H_inf_swap_pair_eq x y).
Qed.

(* P12〔:3290 Pmid_len_spectrum 参数〕长度谱系满长规范形无前提精简版：
   NAT 参数以 lam := length l 喂 le_n 内联，出 length (Pmid l s
   (length l)) = (length l + (length l - length l)) 面（满长端点
   谱系实例——与在册 Pmid_len_endpoint 退化面相容） *)
Theorem dtd_c4_Pmid_len_spectrum_len : forall (l : list Q) (s : nat),
  length (Pmid l s (length l)) = (length l + (length l - length l))%nat.
Proof.
  intros l s. apply (Pmid_len_spectrum l s (length l)). apply le_n.
Qed.

(* P13〔:3414 freq_pos_of_in 参数〕成员频数正性 cons 形无前提精简版：
   IN 参数以 In x (x :: l) 喂 in_eq 内联，出 1 <= freq (x :: l) x 面
   （世界表成员至少一票的 cons 规范实例） *)
Theorem dtd_c4_freq_pos_of_in_cons : forall (x : Q) (l : list Q),
  (1 <= freq (x :: l) x)%nat.
Proof.
  intros x l. apply (freq_pos_of_in (x :: l) x). apply in_eq.
Qed.

(* P14〔:3443 sumf_mono_r 参数〕sumf 逐点单调 filter 形无前提精简版：
   逐点不增参数以 freq_filter_le 内联输入，出 sumf m (filter g l) <=
   sumf m l 面（filter 子表频数不增的全表求和迁移规范实例） *)
Theorem dtd_c4_sumf_mono_r_filter : forall (g : Q -> bool) (m l : list Q),
  (sumf m (filter g l) <= sumf m l)%nat.
Proof.
  intros g m l. apply (sumf_mono_r m (filter g l) l).
  intro y. apply freq_filter_le.
Qed.

(* P15〔:3477 mu_fiber_pos 参数〕判零会员测度正性常零单点形无前提
   精简版：IN 参数喂 dtd_c4_in_fiber_zero_single，出 0 < mu [x] x 面
   （fiber 支撑上 w-测度恒正的常零观测规范实例；面经计算性退化
   0 < 1——平凡位申报见交付报告，应用形本体照宿主参数面逐字特化） *)
Theorem dtd_c4_mu_fiber_pos_single : forall x : Q, 0 < mu [x] x.
Proof.
  intro x. apply (mu_fiber_pos (fun _ => 0%Q) [x] x).
  exact (dtd_c4_in_fiber_zero_single x).
Qed.

(* P16〔:3502 mu_fiber_mass_lb 参数〕纤维质量经验频率下界 cons 形
   无前提精简版：NEQ 参数喂 dtd_c4_cons_neq_nil，出 cons 形下界面
   （每张零点票至少记一次账的 cons 规范实例；  P2 cons 应用形
   同款） *)
Theorem dtd_c4_mu_fiber_mass_lb_cons : forall (f : Q -> Q) (x : Q)
    (t : list Q),
  ((Z.of_nat (length (fiber f (x :: t))) # 1)
   / (Z.of_nat (length (x :: t)) # 1))%Q
  <= qsum (map (mu (x :: t)) (dedup (fiber f (x :: t)))).
Proof.
  intros f x t. apply (mu_fiber_mass_lb f (x :: t)).
  exact (dtd_c4_cons_neq_nil x t).
Qed.

(* P17〔:3537 dedup_aux_In_l 参数〕dedup_aux 记录级成员保持判假分支
   形精简版：IN 参数喂 dtd_c4_in_dedup_aux_cons_neq，出判假分支下
   In a (a :: t) 面（参数消解产物面照宿主结论面特化——面经 in_eq
   退化，内容承重在  的判假分支成员构造，平凡申报见交付报告） *)
Theorem dtd_c4_dedup_aux_In_l_cons_neq : forall (x a : Q) (t : list Q),
  Qeq_bool x a = false -> In a (a :: t).
Proof.
  intros x a t H. apply (dedup_aux_In_l x (a :: t) a).
  exact (dtd_c4_in_dedup_aux_cons_neq x a t H).
Qed.

(* P18〔:3549 dedup_In_l 参数〕dedup 记录级成员保持头位形无前提
   精简版：IN 参数喂 dtd_c4_in_dedup_head，出 In a (a :: t) 面
   （同 P17 口径：内容承重在  头位无条件成员构造） *)
Theorem dtd_c4_dedup_In_l_head : forall (a : Q) (t : list Q),
  In a (a :: t).
Proof.
  intros a t. apply (dedup_In_l (a :: t) a).
  exact (dtd_c4_in_dedup_head a t).
Qed.

(* P19〔:3562 freq_filter_eq_all 参数〕外延门 filter 保频 y 门形
   无前提精简版：门卫参数喂 dtd_c4_gate_Qeq_y，出 freq (filter
   (fun z => Qeq_bool z y) l) y = freq l y 面（y 的全部 Qeq-同票
   开真⟹y 票数 filter 前后不变的规范实例） *)
Theorem dtd_c4_freq_filter_Qeq_y : forall (l : list Q) (y : Q),
  freq (filter (fun z => Qeq_bool z y) l) y = freq l y.
Proof.
  intros l y. apply (freq_filter_eq_all (fun z => Qeq_bool z y) l y).
  exact (dtd_c4_gate_Qeq_y l y).
Qed.

(* P20〔:3581 freq_w_fiber_eq 双参数〕外延 φ 下 filter 保频 Qopp 形
   无前提精简版：EXT 参数喂 dtd_c4_ext_Qopp、零点门参数以
   Qeq_bool (Qopp 0) 0 = true reflexivity 内联输入（双参数全消），
   出 freq (fiber Qopp w) 0 = freq w 0 面（取负号观测的零点票
   计数守恒规范实例） *)
Theorem dtd_c4_freq_w_fiber_eq_opp : forall w : list Q,
  freq (fiber Qopp w) 0 = freq w 0.
Proof.
  intro w. apply (freq_w_fiber_eq Qopp dtd_c4_ext_Qopp w 0).
  reflexivity.
Qed.

(* P21〔:3595 sumf_ext 参数〕sumf 右侧逐点相等迁移恒开门形无前提
   精简版：点等式参数喂 dtd_c4_freq_filter_all_true（同门全开规范
   实例——y 门点喂对 y0≠y 不成立之勘注见④），出 sumf m
   (filter (fun _ => true) l) = sumf m l 面 *)
Theorem dtd_c4_sumf_ext_all_true : forall (m l : list Q),
  sumf m (filter (fun _ => true) l) = sumf m l.
Proof.
  intros m l. apply (sumf_ext m (filter (fun _ => true) l) l).
  intros y _. exact (dtd_c4_freq_filter_all_true l y).
Qed.

(* P22〔:3610 mu_fiber_mass_eq 双参数〕纤维质量守恒显式形 Qopp cons 形
   无前提精简版：NEQ 参数喂 dtd_c4_cons_neq_nil、EXT 参数喂
   dtd_c4_ext_Qopp（双参数全消），出 qsum (map (mu (x :: t))
   (dedup (fiber Qopp (x :: t)))) == 商面（零点票一张不漏全记在
   纤维名下的取负号观测 cons 规范实例） *)
Theorem dtd_c4_mu_fiber_mass_eq_opp_cons : forall (x : Q) (t : list Q),
  qsum (map (mu (x :: t)) (dedup (fiber Qopp (x :: t))))
  == ((Z.of_nat (length (fiber Qopp (x :: t))) # 1)
      / (Z.of_nat (length (x :: t)) # 1))%Q.
Proof.
  intros x t. apply (mu_fiber_mass_eq Qopp (x :: t)).
  - exact (dtd_c4_cons_neq_nil x t).
  - exact dtd_c4_ext_Qopp.
Qed.

(* P23〔:3758 llm_view_PhP0_gate_exact 参数〕判定器判 P0 门放行空表形
   无前提精简版：EQ 参数喂 dtd_c4_phase_classify_nil_PhP0，出
   gate_pass (gate_threshold (llm_view_of [] s))
   (H_adj (Pmid [] s 0)) = true 面（门判据经数值面放行的空表
   规范实例；bool 判定面离散承载） *)
Theorem dtd_c4_llm_view_PhP0_gate_exact_nil : forall s : nat,
  gate_pass (gate_threshold (llm_view_of [] s))
            (H_adj (Pmid [] s 0)) = true.
Proof.
  intro s. apply (llm_view_PhP0_gate_exact ([] : list Q) s).
  exact (dtd_c4_phase_classify_nil_PhP0 s).
Qed.

(* ============================================================ *)
(* §三 尾置验印区（文件最尾）：Check 印＋逐件承认面验印，          *)
(*     名清单=供给定理数=40 零差（17 T＋23 P′）                    *)
(* ============================================================ *)

Check dtd_c4_P0_ssorted.
Check dtd_c4_count_P0_P0rev.
Check dtd_c4_perm_sym.
Check dtd_c4_Forall2_Qeq_single.
Check dtd_c4_phase_classify_nil_PhP0.
Check dtd_c4_perm_swap_pair.
Check dtd_c4_H_inf_swap_pair_eq.
Check dtd_c4_in_fiber_zero_single.
Check dtd_c4_cons_neq_nil.
Check dtd_c4_in_dedup_aux_cons_neq.
Check dtd_c4_in_dedup_head.
Check dtd_c4_gate_Qeq_y.
Check dtd_c4_ext_Qopp.
Check dtd_c4_freq_filter_all_true.
Check dtd_c4_OrgDiff_nil_nonneg.
Check dtd_c4_perm_rev.
Check dtd_c4_Tabs_const.
Check dtd_c4_H_adj_bound_single.
Check dtd_c4_Hsup_bounded_single.
Check dtd_c4_swap_adj_oob_len.
Check dtd_c4_count_q_perm_rev.
Check dtd_c4_sorted_perm_count_qeq_P0rev.
Check dtd_c4_P0_perm_inv_sym.
Check dtd_c4_sum_adjdiff_qeq_single.
Check dtd_c4_H_adj_qeq_single.
Check dtd_c4_H_adj_P0_perm_sym.
Check dtd_c4_phase_classify_P0_spec_nil.
Check dtd_c4_phase_classify_perm_inv_cond_swap2.
Check dtd_c4_Pmid_len_spectrum_len.
Check dtd_c4_freq_pos_of_in_cons.
Check dtd_c4_sumf_mono_r_filter.
Check dtd_c4_mu_fiber_pos_single.
Check dtd_c4_mu_fiber_mass_lb_cons.
Check dtd_c4_dedup_aux_In_l_cons_neq.
Check dtd_c4_dedup_In_l_head.
Check dtd_c4_freq_filter_Qeq_y.
Check dtd_c4_freq_w_fiber_eq_opp.
Check dtd_c4_sumf_ext_all_true.
Check dtd_c4_mu_fiber_mass_eq_opp_cons.
Check dtd_c4_llm_view_PhP0_gate_exact_nil.

Print Assumptions dtd_c4_P0_ssorted.
Print Assumptions dtd_c4_count_P0_P0rev.
Print Assumptions dtd_c4_perm_sym.
Print Assumptions dtd_c4_Forall2_Qeq_single.
Print Assumptions dtd_c4_phase_classify_nil_PhP0.
Print Assumptions dtd_c4_perm_swap_pair.
Print Assumptions dtd_c4_H_inf_swap_pair_eq.
Print Assumptions dtd_c4_in_fiber_zero_single.
Print Assumptions dtd_c4_cons_neq_nil.
Print Assumptions dtd_c4_in_dedup_aux_cons_neq.
Print Assumptions dtd_c4_in_dedup_head.
Print Assumptions dtd_c4_gate_Qeq_y.
Print Assumptions dtd_c4_ext_Qopp.
Print Assumptions dtd_c4_freq_filter_all_true.
Print Assumptions dtd_c4_OrgDiff_nil_nonneg.
Print Assumptions dtd_c4_perm_rev.
Print Assumptions dtd_c4_Tabs_const.
Print Assumptions dtd_c4_H_adj_bound_single.
Print Assumptions dtd_c4_Hsup_bounded_single.
Print Assumptions dtd_c4_swap_adj_oob_len.
Print Assumptions dtd_c4_count_q_perm_rev.
Print Assumptions dtd_c4_sorted_perm_count_qeq_P0rev.
Print Assumptions dtd_c4_P0_perm_inv_sym.
Print Assumptions dtd_c4_sum_adjdiff_qeq_single.
Print Assumptions dtd_c4_H_adj_qeq_single.
Print Assumptions dtd_c4_H_adj_P0_perm_sym.
Print Assumptions dtd_c4_phase_classify_P0_spec_nil.
Print Assumptions dtd_c4_phase_classify_perm_inv_cond_swap2.
Print Assumptions dtd_c4_Pmid_len_spectrum_len.
Print Assumptions dtd_c4_freq_pos_of_in_cons.
Print Assumptions dtd_c4_sumf_mono_r_filter.
Print Assumptions dtd_c4_mu_fiber_pos_single.
Print Assumptions dtd_c4_mu_fiber_mass_lb_cons.
Print Assumptions dtd_c4_dedup_aux_In_l_cons_neq.
Print Assumptions dtd_c4_dedup_In_l_head.
Print Assumptions dtd_c4_freq_filter_Qeq_y.
Print Assumptions dtd_c4_freq_w_fiber_eq_opp.
Print Assumptions dtd_c4_sumf_ext_all_true.
Print Assumptions dtd_c4_mu_fiber_mass_eq_opp_cons.
Print Assumptions dtd_c4_llm_view_PhP0_gate_exact_nil.

(* ── 提取检验区（G3 归桶： 专属桶，Separate Extraction
     单命令单桶——本件零新增数据层承载（Require 转发形），无  
     同名覆写触发面；Obj.magic 逐文件计数归因登记于交付报告） ── *)
Set Extraction Output Directory "_log/dtd_t5".
Separate Extraction dtd_c4_P0_ssorted
  dtd_c4_count_P0_P0rev dtd_c4_perm_sym dtd_c4_Forall2_Qeq_single
  dtd_c4_phase_classify_nil_PhP0 dtd_c4_perm_swap_pair
  dtd_c4_H_inf_swap_pair_eq dtd_c4_in_fiber_zero_single
  dtd_c4_cons_neq_nil dtd_c4_in_dedup_aux_cons_neq
  dtd_c4_in_dedup_head dtd_c4_gate_Qeq_y dtd_c4_ext_Qopp
  dtd_c4_freq_filter_all_true dtd_c4_OrgDiff_nil_nonneg
  dtd_c4_perm_rev dtd_c4_Tabs_const dtd_c4_H_adj_bound_single
  dtd_c4_Hsup_bounded_single dtd_c4_swap_adj_oob_len
  dtd_c4_count_q_perm_rev dtd_c4_sorted_perm_count_qeq_P0rev
  dtd_c4_P0_perm_inv_sym dtd_c4_sum_adjdiff_qeq_single
  dtd_c4_H_adj_qeq_single dtd_c4_H_adj_P0_perm_sym
  dtd_c4_phase_classify_P0_spec_nil
  dtd_c4_phase_classify_perm_inv_cond_swap2
  dtd_c4_Pmid_len_spectrum_len dtd_c4_freq_pos_of_in_cons
  dtd_c4_sumf_mono_r_filter dtd_c4_mu_fiber_pos_single
  dtd_c4_mu_fiber_mass_lb_cons dtd_c4_dedup_aux_In_l_cons_neq
  dtd_c4_dedup_In_l_head dtd_c4_freq_filter_Qeq_y
  dtd_c4_freq_w_fiber_eq_opp dtd_c4_sumf_ext_all_true
  dtd_c4_mu_fiber_mass_eq_opp_cons dtd_c4_llm_view_PhP0_gate_exact_nil.
