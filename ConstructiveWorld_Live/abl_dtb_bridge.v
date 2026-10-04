(* ==========================================================================
   abl_dtb_bridge.v —— DTPT_Bridge／PA_DTPT_Bridge_Dep 前件参数消解供给。
   ── 使命：对宿主 DTPT_Bridge 带前件 21 条语句 26 参数（扣除真前提 2 参数
   diag_closed＝设计内登记）与 PA_DTPT_Bridge_Dep 带前件 2 条语句 4 参数，
   逐参数按形态二 T＋P′ 消解：供给定理 T（卫哨构造子路／判定器升证路／外延
   实例路）＋无前提精简版 P′（宿主定理全实参显式应用，参数消即出）；参数
   语句面＝宿主现档逐字（行号唯一凭据），宿主件零字节动零级联。27 参数供给
   ＋1 参数如实登记（liar_diag_point，bool 三律反证位，不可消解）；供给面按
   PERM／NAT／NEQ／EXT／IN／EQ／BOOL／TCERT 八类参数分路，产出 dtb_ 前缀
   定理族（逐位对照见件内语句分组）。
   ── 依赖：DTPT→DTPT_Entropy→DTPT_Rotation→DTPT_Truth→DTPT_Bridge→
   PA_DTPT_Bridge_Dep（宿主件头同序禁逆向）＋stdlib（QArith／Qabs／List／
   Permutation／Lia／Extraction）。
   ── 对标行：T＋P′ 形态二先例＝abl_tbn_supply_b（tbn_b_mtg_Hcert_2 装配
   应用形／tbn_b_abls_InT_H_wo 无前提精简版随件先例）。
   ── 构造性注记：零承认式声明、零悬置前提、零经典逻辑，全部结论 Qed 真构造
   闭合；供给语句面零混载形态（零裸 exists／零否定／零 -> False／零 sumbool
   语句位），结论承载位 QleT／QeqT／QltT／And(prod)／sigT 全 Type 面；名面
   全 dtb_ 前缀；尾置逐件 Print Assumptions Closed＋Separate Extraction。
   ── 编译配方：池 cwd＝沙箱/现役/abl_r85_supply_pool；source Live 库根
   toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 后 nice -19
   rocq c -native-compiler no
   -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
   abl_dtb_bridge.v；绿判＝EXIT=0／日志零 Error／.vo 头 8 字节
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
Require DTPT_Entropy.
Require DTPT_Rotation.
Require DTPT_Truth.
Require DTPT_Bridge.
Require PA_DTPT_Bridge_Dep.

Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.
Import DTPT_Rotation.DTPT_Rotation.
Import DTPT_Truth.DTPT_Truth.
Import DTPT_Bridge.DTPT_Bridge.

(* ============================================================ *)
(* §一 共用卫哨/证书产路区（供给定理 T·12 枚）                     *)
(*    逐枚＝底册参数面的构造性产路：卫哨 cons 构造子路（普查「卫哨   *)
(*    可平凡供给」）、置换构造子路（「Permutation 有构造子」）、    *)
(*    判定器升证路（「Q 序等可判定」）、外延实例路、成员产路。      *)
(* ============================================================ *)

(* 〔PERM 产路·供 :103/:148/:186 三参数〕置换对称构造子路：
   Permutation p l ⟹ Permutation l l 的逆向重组（stdlib
   Permutation_sym 构造子一击，普查「Permutation 有构造子」锚） *)
Theorem dtb_perm_sym_route : forall l p : list Q,
  Permutation p l -> Permutation l p.
Proof.
  intros l p Hperm. exact (Permutation_sym Hperm).
Qed.

(* 〔NAT 非空卫哨产路·供 :156/:429/:805×2/:825×2 五参数〕cons 形：
   长度卫哨 (0 < length l)%nat 于规范 cons 实例的定义性产路
   （普查「卫哨可平凡供给」锚；平凡位申报见交付报告） *)
Theorem dtb_len_pos_cons : forall (x : Q) (l : list Q),
  (0 < length (x :: l))%nat.
Proof.
  intros x l. simpl. lia.
Qed.

(* 〔NEQ 非空卫哨产路·供 :195/:641/:688＋PA_Dep :219-3 四参数〕
   cons 形：x :: l <> [] 头构造判别（卫哨 cons 构造子路） *)
Theorem dtb_cons_neq_nil : forall (x : Q) (l : list Q), (x :: l) <> [].
Proof.
  intros x l H. discriminate H.
Qed.

(* 〔EXT 外延卫哨产路·供 :515/:525×2/:535×2/:688 六参数〕
   外延实例路：Qopp 保 Qeq（Z 层定义面展开＋Z.mul_opp_l 链——
   外延卫哨的非平凡具例：负号映射保 Qeq，供给 f 的规范可应用形） *)
Theorem dtb_ext_Qopp : forall x y : Q, x == y -> (- x == - y)%Q.
Proof.
  intros [nx dx] [ny dy] H. unfold Qeq in *; simpl in *.
  rewrite Z.mul_opp_l. rewrite Z.mul_opp_l. rewrite H. reflexivity.
Qed.

(* 〔IN 成员产路·供 :651 参数〕纤维成员产路：x ∈ w 且 f x 归零
   ⟹ x ∈ fiber f w（filter_In 成员刻画＋Qeq_bool_iff 判定升证，
   DTPT.v fiber 定义面 filter 语义） *)
Theorem dtb_in_fiber_of : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x w -> (f x == 0)%Q -> In x (fiber f w).
Proof.
  intros f w x Hin H0. unfold fiber. apply filter_In. split.
  - exact Hin.
  - exact (proj2 (Qeq_bool_iff (f x) 0) H0).
Qed.

(* 〔EQ 等词产路·供 :661 参数〕Leibniz 等词的自反实例
   （eq 构造子路；平凡位申报见交付报告） *)
Theorem dtb_nat_eq_refl : forall a : nat, a = a.
Proof.
  intro a. reflexivity.
Qed.

(* 〔BOOL 判定面产路·供 :262 参数〕Lv0 规范实例：层判 t 过 Lv0 审
   的无条件真值——trLevel_geq＝level_le lv (trLevel t) 于 lv:=Lv0
   的定义性直证（DTPT_Truth level_le Lv0 支定义面，零转发跳） *)
Theorem dtb_trLevel_geq_Lv0_true : forall t : TrNode,
  trLevel_geq t Lv0 = true.
Proof.
  intro t. unfold trLevel_geq, level_le. reflexivity.
Qed.

(* 〔BOOL 判定面产路·供 :262 参数（第二路）〕Lv1 审查实例：
   audit_node 过审 ⟹ Lv1 层判过审（audit_node_iff 双向行为定理
   正向＋合取首分量抽取，DTPT_Truth :717 在册） *)
Theorem dtb_trLevel_geq_of_audit : forall t : TrNode,
  audit_node t = true -> trLevel_geq t Lv1 = true.
Proof.
  intro t. intro H.
  exact (proj1 (proj1 (audit_node_iff t) H)).
Qed.

(* 〔TCERT 证书产路·供 :452/:550 两参数〕bool 判定面升 Type 证书路：
   Qle_bool x y = true ⟹ QleT x y（Qle_bool_iff 判定器正向＋
   qleT_intro 包装，普查「Q 序等可判定」锚——vm_compute 即得的
   调用方数据义务升入 Type 证书的最短通道） *)
Theorem dtb_QleT_of_bool : forall x y : Q,
  (Qle_bool x y = true) -> QleT x y.
Proof.
  intros x y H. apply qleT_intro. exact (proj1 (Qle_bool_iff x y) H).
Qed.

(* 〔Q-ORD 产路·供 PA_Dep :255 参数〕bool 判定面升 Q 序路：
   Qle_bool x y = true ⟹ (x <= y)%Q（Qle_bool_iff 正向；判定器面
   产路，DTPT.v Qle_dec' :137 同链） *)
Theorem dtb_Qle_of_bool : forall x y : Q,
  (Qle_bool x y = true) -> (x <= y)%Q.
Proof.
  intros x y H. exact (proj1 (Qle_bool_iff x y) H).
Qed.

(* 〔In 界卫哨产路·供 PA_Dep :219-1 参数〕cons 形成员界卫哨的
   逐点装配路：头部界＋尾部界 ⟹ 全表界（In-cons 成员开析构造，
   PA_Dep :219 In 界卫哨 (forall x, In x l -> Qabs x <= B) 的
   构造性引入路） *)
Theorem dtb_in_bound_cons : forall (x : Q) (l : list Q) (B : Q),
  Qabs x <= B -> (forall z : Q, In z l -> Qabs z <= B) ->
  forall z : Q, In z (x :: l) -> Qabs z <= B.
Proof.
  intros x l B Hx Hl z Hz. simpl in Hz. destruct Hz as [Heq | Hz].
  - rewrite <- Heq. exact Hx.
  - exact (Hl z Hz).
Qed.

(* 〔SortedQ 有序产路·供 PA_Dep :219-2 参数〕P0 规范形产路：
   P0 l 恒有序（xq_P0_sorted＝insert_q 归纳产路，普查「SortedQ
   有产路（xq_P0_sorted/P0_sorted）」锚；本件位 Entropy 副本归属
   与 PA_Dep 参数面同型，检验件实拍） *)
Theorem dtb_sorted_P0 : forall l : list Q, SortedQ (P0 l).
Proof.
  intro l. exact (xq_P0_sorted l).
Qed.

(* ============================================================ *)
(* §二 DTPT_Bridge P′ 精简版区（17 枚）                           *)
(*    逐枚＝源定理 @ 全实参显式应用＋参数由 §一 产路输入，出无前提精简版    *)
(*    （或降维判定器面版）；语句面＝源结论面现档逐字特化。          *)
(* ============================================================ *)

(* P1〔:103 C_gen_set 参数〕置换对称面精简版：Permutation p l 喂
   dtb_perm_sym_route 出 QleT 面（H_adj (P0 l) <= H_adj p） *)
Theorem dtb_C_gen_sym : forall l p : list Q,
  Permutation p l -> QleT (H_adj (P0 l)) (H_adj p).
Proof.
  intros l p Hperm.
  exact (@C_gen_set l p (dtb_perm_sym_route l p Hperm)).
Qed.

(* P2〔:148 H_freq_perm_set 参数〕同款对称面精简版（H_freq 面） *)
Theorem dtb_H_freq_perm_sym : forall l p : list Q,
  Permutation p l -> QeqT (H_freq l) (H_freq p).
Proof.
  intros l p Hperm.
  exact (@H_freq_perm_set l p (dtb_perm_sym_route l p Hperm)).
Qed.

(* P3〔:186 freq_perm_set 参数〕同款对称面精简版（频数分子 Q 载值面） *)
Theorem dtb_freq_perm_sym : forall (l p : list Q) (x : Q),
  Permutation p l ->
  QeqT ((Z.of_nat (freq l x) # 1)%Q) ((Z.of_nat (freq p x) # 1)%Q).
Proof.
  intros l p x Hperm.
  exact (@freq_perm_set l p x (dtb_perm_sym_route l p Hperm)).
Qed.

(* P4〔:156 H_chain_set 参数〕Rényi 阶梯 cons 形无前提精简版：
   非空卫哨由 dtb_len_pos_cons 输入，出三段 And 型积面 *)
Theorem dtb_H_chain_cons : forall (x : Q) (l : list Q),
  And (QleT (1 / qn (length (x :: l))) (collide (x :: l)))
      (And (QleT (collide (x :: l)) (maxfreq (x :: l)))
           (QleT (maxfreq (x :: l)) 1)).
Proof.
  intros x l. exact (@H_chain_set (x :: l) (dtb_len_pos_cons x l)).
Qed.

(* P5〔:195 mu_total_mass_set 参数〕总质量一 cons 形无前提精简版 *)
Theorem dtb_mu_total_mass_cons : forall (x : Q) (l : list Q),
  QeqT (qsum (map (mu (x :: l)) (dedup (x :: l)))) 1.
Proof.
  intros x l. exact (@mu_total_mass_set (x :: l) (dtb_cons_neq_nil x l)).
Qed.

(* P6〔:429 collide_lower_set 参数〕collide 下界 cons 形无前提精简版 *)
Theorem dtb_collide_lower_cons : forall (x : Q) (l : list Q),
  QleT (1 / qn (length (x :: l))) (collide (x :: l)).
Proof.
  intros x l. exact (@collide_lower_set (x :: l) (dtb_len_pos_cons x l)).
Qed.

(* P7〔:452 H_max_q_anti_set 参数〕反变单调判定器面精简版：
   Qle_bool (maxfreq l) (maxfreq p) = true（调用方 vm_compute 即得）
   喂 dtb_QleT_of_bool 升 Type 证书后喂宿主，出 QleT 面 *)
Theorem dtb_H_max_q_anti_bool : forall l p : list Q,
  (Qle_bool (maxfreq l) (maxfreq p) = true) -> QleT (H_max_q p) (H_max_q l).
Proof.
  intros l p Hb.
  exact (@H_max_q_anti_set l p (dtb_QleT_of_bool (maxfreq l) (maxfreq p) Hb)).
Qed.

(* P8〔:515 H_freq_dpi_set 参数〕DPI 精简版·Qopp 实例：
   外延卫哨参数喂 dtb_ext_Qopp（f := 负号映射），出逐点负号粗粒化
   不增熵的 QleT 无条件面 *)
Theorem dtb_H_freq_dpi_opp : forall l : list Q,
  QleT (H_freq (map (fun x : Q => - x) l)) (H_freq l).
Proof.
  intro l.
  exact (@H_freq_dpi_set (fun x : Q => - x)
           (fun x y H => dtb_ext_Qopp x y H) l).
Qed.

(* P9〔:525 H_freq_map_twice_set 双参数〕两步复合精简版·Qopp 双实例：
   两外延卫哨参数均喂 dtb_ext_Qopp，出二次负号映射仍不增的 QleT 面 *)
Theorem dtb_H_freq_map_twice_opp : forall l : list Q,
  QleT (H_freq (map (fun x : Q => - x) (map (fun x : Q => - x) l)))
       (H_freq (map (fun x : Q => - x) l)).
Proof.
  intro l.
  exact (@H_freq_map_twice_set (fun x : Q => - x) (fun x : Q => - x)
           (fun x y H => dtb_ext_Qopp x y H)
           (fun x y H => dtb_ext_Qopp x y H) l).
Qed.

(* P10〔:535 H_freq_map_chain_set 双参数〕链式精简版·Qopp 双实例：
   出 map Qopp ∘ map Qopp 一次到底不增 H_freq 的 QleT 面 *)
Theorem dtb_H_freq_map_chain_opp : forall l : list Q,
  QleT (H_freq (map (fun x : Q => - x) (map (fun x : Q => - x) l)))
       (H_freq l).
Proof.
  intro l.
  exact (@H_freq_map_chain_set (fun x : Q => - x) (fun x : Q => - x)
           (fun x y H => dtb_ext_Qopp x y H)
           (fun x y H => dtb_ext_Qopp x y H) l).
Qed.

(* P11〔:550 H_min_q_anti_set 参数〕反变单调判定器面精简版（H_min_q 面） *)
Theorem dtb_H_min_q_anti_bool : forall l p : list Q,
  (Qle_bool (collide l) (collide p) = true) -> QleT (H_min_q p) (H_min_q l).
Proof.
  intros l p Hb.
  exact (@H_min_q_anti_set l p (dtb_QleT_of_bool (collide l) (collide p) Hb)).
Qed.

(* P12〔:641 mu_fiber_mass_lb_set 参数〕纤维质量下界 cons 形无前提精简版 *)
Theorem dtb_mu_fiber_mass_lb_cons : forall (f : Q -> Q) (x : Q) (l : list Q),
  QleT (((Z.of_nat (length (fiber f (x :: l))) # 1)
         / (Z.of_nat (length (x :: l)) # 1))%Q)
       (qsum (map (mu (x :: l)) (dedup (fiber f (x :: l))))).
Proof.
  intros f x l.
  exact (@mu_fiber_mass_lb_set f (x :: l) (dtb_cons_neq_nil x l)).
Qed.

(* P13〔:651 mu_fiber_pos_set 参数〕判零会员测度正性产路精简版：
   成员参数由 dtb_in_fiber_of 输入，出 In x w ∧ f x 归零 ⟹ 0 < mu 的
   QltT 面（卫哨降维为可构造数据义务） *)
Theorem dtb_mu_fiber_pos_of : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x w -> (f x == 0)%Q -> QltT 0 (mu w x).
Proof.
  intros f w x Hin H0.
  exact (@mu_fiber_pos_set f w x (dtb_in_fiber_of f w x Hin H0)).
Qed.

(* P14〔:661 QeqT_of_nat_eq 参数〕nat 等词自反实例的 QeqT 升证面
   （eq 参数喂 dtb_nat_eq_refl；隐式参应用形照检验实证） *)
Theorem dtb_QeqT_of_nat_refl : forall a : nat,
  QeqT ((Z.of_nat a # 1)%Q) ((Z.of_nat a # 1)%Q).
Proof.
  intro a. exact (QeqT_of_nat_eq (eq_refl a)).
Qed.

(* P15〔:688 mu_fiber_mass_eq_set 双参数〕质量守恒取等 cons+Qopp 形
   无前提精简版：非空卫哨喂 dtb_cons_neq_nil、外延卫哨喂
   dtb_ext_Qopp（f := 负号映射），出双参数全消的 QeqT 面 *)
Theorem dtb_mu_fiber_mass_eq_cons_opp : forall (x : Q) (l : list Q),
  QeqT (qsum (map (mu (x :: l)) (dedup (fiber (fun z : Q => - z) (x :: l)))))
       (((Z.of_nat (length (fiber (fun z : Q => - z) (x :: l))) # 1)
         / (Z.of_nat (length (x :: l)) # 1))%Q).
Proof.
  intros x l.
  exact (@mu_fiber_mass_eq_set (fun z : Q => - z) (x :: l)
           (dtb_cons_neq_nil x l)
           (fun a b Hab => dtb_ext_Qopp a b Hab)).
Qed.

(* P16〔:805 collide_app_eq_set 双参数〕collide 拼接卷积双 cons 形
   无前提精简版：双非空卫哨参数均喂 dtb_len_pos_cons，出双参数全消的
   加权平方组合+交叉修正 QeqT 面（源结论面现档逐字特化） *)
Theorem dtb_collide_app_eq_cons_cons : forall (a1 : Q) (t1 : list Q)
    (a2 : Q) (t2 : list Q),
  QeqT (collide ((a1 :: t1) ++ (a2 :: t2)))
    ((qn (length (a1 :: t1)) / qn (length (a1 :: t1) + length (a2 :: t2))%nat)
      * (qn (length (a1 :: t1)) / qn (length (a1 :: t1) + length (a2 :: t2))%nat)
      * collide (a1 :: t1)
    + (qn (length (a2 :: t2)) / qn (length (a1 :: t1) + length (a2 :: t2))%nat)
      * (qn (length (a2 :: t2)) / qn (length (a1 :: t1) + length (a2 :: t2))%nat)
      * collide (a2 :: t2)
    + (qn (nsum (fun x => freq_q x (a2 :: t2)) (a1 :: t1))
       + qn (nsum (fun x => freq_q x (a1 :: t1)) (a2 :: t2)))
      / (qn (length (a1 :: t1) + length (a2 :: t2))%nat
         * qn (length (a1 :: t1) + length (a2 :: t2))%nat))%Q.
Proof.
  intros a1 t1 a2 t2.
  exact (@collide_app_eq_set (a1 :: t1) (a2 :: t2)
           (dtb_len_pos_cons a1 t1) (dtb_len_pos_cons a2 t2)).
Qed.

(* P17〔:825 H_freq_app_eq_set 双参数〕熵族拼接卷积双 cons 形无前提
   精简版：同 P16 配方（源结论面现档逐字特化，w1²/w2²/2w1w2−X/n²
   完整恒等式） *)
Theorem dtb_H_freq_app_eq_cons_cons : forall (a1 : Q) (t1 : list Q)
    (a2 : Q) (t2 : list Q),
  QeqT (H_freq ((a1 :: t1) ++ (a2 :: t2)))
    ((qn (length (a1 :: t1)) / qn (length (a1 :: t1) + length (a2 :: t2))%nat)
      * (qn (length (a1 :: t1)) / qn (length (a1 :: t1) + length (a2 :: t2))%nat)
      * H_freq (a1 :: t1)
    + (qn (length (a2 :: t2)) / qn (length (a1 :: t1) + length (a2 :: t2))%nat)
      * (qn (length (a2 :: t2)) / qn (length (a1 :: t1) + length (a2 :: t2))%nat)
      * H_freq (a2 :: t2)
    + 2 * (qn (length (a1 :: t1)) / qn (length (a1 :: t1) + length (a2 :: t2))%nat)
        * (qn (length (a2 :: t2)) / qn (length (a1 :: t1) + length (a2 :: t2))%nat)
    - (qn (nsum (fun x => freq_q x (a2 :: t2)) (a1 :: t1))
       + qn (nsum (fun x => freq_q x (a1 :: t1)) (a2 :: t2)))
      / (qn (length (a1 :: t1) + length (a2 :: t2))%nat
         * qn (length (a1 :: t1) + length (a2 :: t2))%nat))%Q.
Proof.
  intros a1 t1 a2 t2.
  exact (@H_freq_app_eq_set (a1 :: t1) (a2 :: t2)
           (dtb_len_pos_cons a1 t1) (dtb_len_pos_cons a2 t2)).
Qed.

(* ============================================================ *)
(* §三 PA_DTPT_Bridge_Dep P′ 精简版区（3 枚）                      *)
(*    卫哨透传纪律（宿主件注 §4）：三卫哨不硬证，由 §一 产路        *)
(*    （//）构造输入或按更细数据义务分解透传。              *)
(* ============================================================ *)

(* P18〔PA_Dep :219 三参数〕处置完备性 cons 形精简版：
   SortedQ 参数经 sortQ_cons 分解透传（尾有序＋头界双数据义务）、
   In 界参数由 dtb_in_bound_cons 构造、非空参数由 dtb_cons_neq_nil
   构造——三卫哨全由更细数据义务构造喂定，出九分量 Type 积面
   （源结论面现档逐字特化 l := x :: l；QleT/QeqT 取宿主本地副本
   全路径名，检验件实证） *)
Theorem dtb_deprecated_cluster_cons : forall (x : Q) (l : list Q) (B : Q)
    (s k n : nat),
  SortedQ l -> (forall z : Q, In z l -> x <= z) ->
  Qabs x <= B -> (forall z : Q, In z l -> Qabs z <= B) ->
  ({w : list Q & Pinf (x :: l) s = w} *
  {w : list Q & Pinf_c (x :: l) s = w} *
  ({w : list Q & Pmid (x :: l) s 0%nat = w} *
   PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QeqT
     (H_adj (Pmid (x :: l) s 0%nat)) (H_adj (x :: l))) *
  {w : list Q & P0 (Pmid (x :: l) s k) = w} *
  PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT
    (Hsup (x :: l) n) (Hsup (x :: l) (S n)) *
  PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT
    (Hsup (x :: l) n) (((Z.of_nat (length (x :: l)) # 1)%Q * B * 2)%Q) *
  PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT
    (Hsup_cyc (x :: l) n) ((3 * (lastq (x :: l) - hd 0 (x :: l)))%Q) *
  (PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT
    (H_adj (P0 (x :: l))) (H_adj (Pinf (x :: l) s)) *
  (PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT
    (H_adj (P0 (x :: l))) (H_adj (rotc k (x :: l))) *
  PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT
    (H_adj (P0 (x :: l))) (H_adj (Pinf_c (x :: l) s)))) *
  ({v : nat & phase_side (x :: l) s = v} *
   PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT
     (H_adj (P0 (x :: l))) (H_adj (rotc s (x :: l)))))%type.
Proof.
  intros x l B s k n HSort HHead Hx Hl.
  apply (PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.deprecated_cluster_fully_covered
           (x :: l) s k n B).
  - exact (dtb_in_bound_cons x l B Hx Hl).
  - apply sortQ_cons.
    + exact HSort.
    + rewrite Forall_forall. exact HHead.
  - exact (dtb_cons_neq_nil x l).
Qed.

(* P19〔PA_Dep :219 三参数·全消主定理〕处置完备性单点形零前提精简版：
   l := [y]、B := Qabs y 规范实例——In 界参数逐点自反构造、SortedQ
   参数 sortQ_cons/nil 定义性构造、非空参数判别构造，三卫哨全消，
   出零数据前提的九分量 Type 积面（升级方向：一般有序表的
   P0 规范形实例化随 B-2 卷供应） *)
Theorem dtb_deprecated_cluster_single : forall (y : Q) (s k n : nat),
  ({w : list Q & Pinf (y :: nil) s = w} *
  {w : list Q & Pinf_c (y :: nil) s = w} *
  ({w : list Q & Pmid (y :: nil) s 0%nat = w} *
   PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QeqT
     (H_adj (Pmid (y :: nil) s 0%nat)) (H_adj (y :: nil))) *
  {w : list Q & P0 (Pmid (y :: nil) s k) = w} *
  PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT
    (Hsup (y :: nil) n) (Hsup (y :: nil) (S n)) *
  PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT
    (Hsup (y :: nil) n)
    (((Z.of_nat (length (y :: nil)) # 1)%Q * Qabs y * 2)%Q) *
  PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT
    (Hsup_cyc (y :: nil) n) ((3 * (lastq (y :: nil) - hd 0 (y :: nil)))%Q) *
  (PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT
    (H_adj (P0 (y :: nil))) (H_adj (Pinf (y :: nil) s)) *
  (PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT
    (H_adj (P0 (y :: nil))) (H_adj (rotc k (y :: nil))) *
  PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT
    (H_adj (P0 (y :: nil))) (H_adj (Pinf_c (y :: nil) s)))) *
  ({v : nat & phase_side (y :: nil) s = v} *
   PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT
     (H_adj (P0 (y :: nil))) (H_adj (rotc s (y :: nil)))))%type.
Proof.
  intros y s k n.
  apply (PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.deprecated_cluster_fully_covered
           (y :: nil) s k n (Qabs y)).
  - intros z Hz. simpl in Hz. destruct Hz as [Heq | Hc].
    + rewrite <- Heq. apply Qle_refl.
    + destruct Hc.
  - apply sortQ_cons; [ apply sortQ_nil | apply Forall_nil ].
  - intros Hc. discriminate Hc.
Qed.

(* P20〔PA_Dep :255 参数〕λ-反单调判定器面精简版：Q-ORD 参数降维为
   Qle_bool lam1 lam2 = true（调用方 vm_compute 即得）经
   dtb_Qle_of_bool 升 Q 序后喂宿主，出 QleT 信息性面（源结论面
   现档逐字；QleT 取宿主本地副本全路径名） *)
Theorem dtb_H_lam_anti_mono_bool : forall (l : list Q) (s : nat)
    (lam1 lam2 : Q),
  (Qle_bool lam1 lam2 = true) ->
  PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.QleT (H_lam l s lam2) (H_lam l s lam1).
Proof.
  intros l s lam1 lam2 Hb.
  exact (PA_DTPT_Bridge_Dep.DTPT_Bridge_Dep.H_lam_anti_mono_real_set
           l s lam1 lam2 (dtb_Qle_of_bool lam1 lam2 Hb)).
Qed.

(* ============================================================ *)
(* §四 尾置验印区（文件最尾）：Check 印＋逐件承认面验印，          *)
(*     名清单=供给定理数=32 零差                                   *)
(* ============================================================ *)

Check dtb_perm_sym_route.
Check dtb_len_pos_cons.
Check dtb_cons_neq_nil.
Check dtb_ext_Qopp.
Check dtb_in_fiber_of.
Check dtb_nat_eq_refl.
Check dtb_trLevel_geq_Lv0_true.
Check dtb_trLevel_geq_of_audit.
Check dtb_QleT_of_bool.
Check dtb_Qle_of_bool.
Check dtb_in_bound_cons.
Check dtb_sorted_P0.
Check dtb_C_gen_sym.
Check dtb_H_freq_perm_sym.
Check dtb_freq_perm_sym.
Check dtb_H_chain_cons.
Check dtb_mu_total_mass_cons.
Check dtb_collide_lower_cons.
Check dtb_H_max_q_anti_bool.
Check dtb_H_freq_dpi_opp.
Check dtb_H_freq_map_twice_opp.
Check dtb_H_freq_map_chain_opp.
Check dtb_H_min_q_anti_bool.
Check dtb_mu_fiber_mass_lb_cons.
Check dtb_mu_fiber_pos_of.
Check dtb_QeqT_of_nat_refl.
Check dtb_mu_fiber_mass_eq_cons_opp.
Check dtb_collide_app_eq_cons_cons.
Check dtb_H_freq_app_eq_cons_cons.
Check dtb_deprecated_cluster_cons.
Check dtb_deprecated_cluster_single.
Check dtb_H_lam_anti_mono_bool.

Print Assumptions dtb_perm_sym_route.
Print Assumptions dtb_len_pos_cons.
Print Assumptions dtb_cons_neq_nil.
Print Assumptions dtb_ext_Qopp.
Print Assumptions dtb_in_fiber_of.
Print Assumptions dtb_nat_eq_refl.
Print Assumptions dtb_trLevel_geq_Lv0_true.
Print Assumptions dtb_trLevel_geq_of_audit.
Print Assumptions dtb_QleT_of_bool.
Print Assumptions dtb_Qle_of_bool.
Print Assumptions dtb_in_bound_cons.
Print Assumptions dtb_sorted_P0.
Print Assumptions dtb_C_gen_sym.
Print Assumptions dtb_H_freq_perm_sym.
Print Assumptions dtb_freq_perm_sym.
Print Assumptions dtb_H_chain_cons.
Print Assumptions dtb_mu_total_mass_cons.
Print Assumptions dtb_collide_lower_cons.
Print Assumptions dtb_H_max_q_anti_bool.
Print Assumptions dtb_H_freq_dpi_opp.
Print Assumptions dtb_H_freq_map_twice_opp.
Print Assumptions dtb_H_freq_map_chain_opp.
Print Assumptions dtb_H_min_q_anti_bool.
Print Assumptions dtb_mu_fiber_mass_lb_cons.
Print Assumptions dtb_mu_fiber_pos_of.
Print Assumptions dtb_QeqT_of_nat_refl.
Print Assumptions dtb_mu_fiber_mass_eq_cons_opp.
Print Assumptions dtb_collide_app_eq_cons_cons.
Print Assumptions dtb_H_freq_app_eq_cons_cons.
Print Assumptions dtb_deprecated_cluster_cons.
Print Assumptions dtb_deprecated_cluster_single.
Print Assumptions dtb_H_lam_anti_mono_bool.

(* ── 提取检验区（G3 归桶： 专属桶，Separate Extraction
     逐件 .ml，Obj.magic 逐件计数归因登记于交付报告） ── *)
Set Extraction Output Directory "_log/dtb_t1".
Separate Extraction dtb_perm_sym_route
  dtb_len_pos_cons dtb_cons_neq_nil dtb_ext_Qopp dtb_in_fiber_of
  dtb_nat_eq_refl dtb_trLevel_geq_Lv0_true dtb_trLevel_geq_of_audit
  dtb_QleT_of_bool dtb_Qle_of_bool dtb_in_bound_cons dtb_sorted_P0
  dtb_C_gen_sym dtb_H_freq_perm_sym dtb_freq_perm_sym dtb_H_chain_cons
  dtb_mu_total_mass_cons dtb_collide_lower_cons dtb_H_max_q_anti_bool
  dtb_H_freq_dpi_opp dtb_H_freq_map_twice_opp dtb_H_freq_map_chain_opp
  dtb_H_min_q_anti_bool dtb_mu_fiber_mass_lb_cons dtb_mu_fiber_pos_of
  dtb_QeqT_of_nat_refl dtb_mu_fiber_mass_eq_cons_opp
  dtb_collide_app_eq_cons_cons dtb_H_freq_app_eq_cons_cons
  dtb_deprecated_cluster_cons dtb_deprecated_cluster_single
  dtb_H_lam_anti_mono_bool.
