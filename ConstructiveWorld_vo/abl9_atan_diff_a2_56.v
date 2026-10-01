(* ==========================================================================)
   abl9_atan_diff_a2_56.v — 主公式 A2 形闭合（甲形态新件）                 
   arctan 差公式主公式的 A2 表示层早项正规化（GAP-1 裁决 A2 形）               
   ── 模块名+数学使命：─────────────────────────────────────────────────────
   本件交付三段：
   ① A2 形主公式语句面：RHS=cauchy_real_arctan (abl9b_wc x h Hd)
     (abl9b_w_clamp_dom …)（clamp 半径 1，与件30 Hdiff 槽逐字同形；铁律：
     Hd 逐字取 abl9b_dom_pos x h Hx Hh4 同一证明项写法——real_inv_pos 定义体
     对证明项做 match，换写法则早项 match 破转换）；
   ② 内点版主公式全闭合：域加强为 |x_n|≤ρ<1（ρ 参数化）、端点 |x_n+h_n|≤ρ，
     h 域承拟文 real_lt 终近形逐字不动（w 侧走全域 clamp 代表元+尾域逐步
     界，步界槽全在尾段 n≥接合阈消解——real_lt 早段无控不破门）；内层链=
     件53 定量 φ 步界机 abl9b_phistep_rho 直供+件51 定量望远镜 abl9_chain_pt；
   ③ 闭域版接口骨架：同语句面、域拟文逐字，「层2 延拓闭合证书」作显式前件
     参数位（证书形=尾段逐 eps 界，与 real_eq 展开形逐槽同构，层2 经
     b5b_ap_uniform 路线产出即可对接）。
   ── 依赖清单：─────────────────────────────────────────────────────────────
   S01–S11（基座冻结链）；abl_arctan_diff_19（abl9_wincr_div_id，L224 使用实证）；abl_arctan_diff_20
   （abl9_q_path_den，L163 使用实证）；abl_arctan_diff_41（abl9_qs_Z/abl9_qs_pos，L399-464 使用实证）；
   abl_arctan_diff_45（abl9_arctan_arg_wd 终近逐点合同；名义性依赖注记：该名全件仅头注引述、语句体零消费，Require 保留维持依赖声明完整——件51 同款先例口径）；abl_arctan_diff_47（abl9_walk/abl9_hN_step/
   qs 剖分族+abl9_asem_move 移项件+abl9_qs_ratio_bnd/abl9_q_convex_abs）；abl9b_rho_chain_53
   （abl9b_phistep_rho 定量 φ 步界机；经其传递在链：件19 ①b、件20 传输族、件30 clamp 机与域界、件51 abl9_chain_pt 望远镜、件60 凸性核）。
   Require 链退回 S11单链，S12出锥（承前已证结论）。
   ── 对标行：───────────────────────────────────────────────────────────────
   A2 语句面铁律带：abl9b_skeleton_30.v（md5 8edf17b8）L338-343（Hdiff 槽）+L391-393（ Hd
   set-let 同证明项带）；拟文：abl_arctan_diff_16.v（md5 d2793fe6）头注 L10-21；定量望远镜：
   abl_arctan_diff_51.v（md5 9e1ffb70）abl9_chain_pt（L126 带）；φ 步界机：abl9b_rho_chain_53.v（md5 cb38c492）
   abl9b_phistep_rho（L870 带）；w 路径界：abl_arctan_diff_40.v（md5 8499f3a9）
   abl9_wpath_pt_bnd（L93 带，1/3 内部链）；w 增量恒等：abl_arctan_diff_19.v（md5 fd017e7a）
   abl9_wincr_div_id；终近逐点合同：abl_arctan_diff_45.v（md5 0fc5d49d）abl9_arctan_arg_wd
   （L68 带）；剖分族：abl_arctan_diff_41.v（md5 d79588d5）qs/abl9_walk/abl9_hN_step。
   ── 构造性注记：───────────────────────────────────────────────────────────
   本件为中文声明的零承认件：全文件零承认式声明、零悬置前提、零经典逻辑，
   全部结论逐件真构造闭合。零承认链短路策略（Q 序链走 Qlt/Qle 传递系与
   跨乘件逐链构造，链上每一环显式 witness）。语句面承载位全 Set 形
   （real_eq/real_lt/sigT/QleT'），Qle/Qlt 仅标量前提位（件19/30/51/53 同款
   口径）；主定理承认面全 Closed，提取检验判据 Obj.magic 计 0。
   数学构造注记：内点闭合的 w 侧全域证书=clamp（半径 1）代表元——对任意
   Real 实参无条件可构造（件30 abl9b_w_clamp_dom 一般形）；walk 节点 w 的
   arctan 使用位全取 clamp 形（早段无控实参经 clamp 入域），而定量步界
   （件53 机）系 Q 层纯点式，其 w 槽在尾段 n≥接合阈与 clamp 前像逐点恒等
   （件30 abl9b_wc_id_pt 点位形+|w|≤1/3 尾界），故 real_lt 形 h 前件（早段
   无控）不破门——此为本件对件47「装配域逐点收紧非可选」结论的升级点：
   clamp 全域证书化后收紧仅余尾段语义，拟文 h 域逐字保持。
   ── 编译配方：─────────────────────────────────────────────────────────────
   source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh
     && unset COQLIB ROCQLIB
   cd /Users/apple/Desktop/ConstructiveWorld/abl_a2b3_MF_pool && ulimit -s 65532
   nice -19 rocq c -native-compiler no -Q "$PWD" "" "$PWD/abl9_atan_diff_a2_56.v"
   （单道顺序 原位建成；绿判四要素：EXIT=0／真错行计 0 且主定理
   Closed under the global context／vo 头 8 字节 436f712100015ff4／vo 新于 v；
   起编前道闸 ps 计 rocq ≤1。）
   ── 续点登记（主件无剩余续点，无遗留事项）──────────────────────
   S1–S4 全出口闭合：S1 Htel=abl9b2_tel／S2 预算=abl9b2_totbnd_eq+
   gap_final+gap_eps（已核验通过）；S3 出口件       
   abl9b2_inpoint_formula（§D内点版主件：§B skel证书前件位直接匹配
   abl9b2_scaled_gap_conv，rho 参数化域加强）；S4 正名终式
   abl9_atan_diff_formula（§E1，案A 序契约面=件61
   abl9b_rehearse2_merge_check_61 参数型逐字，零前件全闭合）——
   路线=案一缩放三角合拢（X61 道一乙+道二坐标）：左肢=件54 lhs_conv
   （cv_to_tail 互译）；右肢=件59 rhs_close 前件槽（案一抽象槽，X61
   钉定）代入件54 ws_conv 真实证书；中肢=§D 内点主件@缩放对
   (xsc m0 x, xsc m0 h)（k:=km(S m0)∈(0,1)，req_to_tail 互译+§E0 桥
   abl9b2_ws_dom_eq 收 dom_pos/sca_Hd 双证书形 Representative 差）；
   m0:=max(ML,MR,1) 固定，Qabs_triangle 三肢拼装，严格肢=右肢
   （Qplus_assoc+Qplus_lt_r 闭合）。Require 新增件54+件59（依赖清单补记：件54 abl9b_ext_chain_54 实使用在案——abl9b_ext_ws/abl9b_ext_ws_conv/abl9b_ext_km_cwu/abl9b_ext_xsc/abl9b_ext_cv_to_tail/abl9b_ext_req_to_tail/abl9b_ext_lhs_conv 全家，左肢/右肢取号带 L1888-1893、§E0/§E1 缩放对逐位；件59 abl9b_rhs_chain_59 实使用在案——abl9b_rhs_close 案一抽象前提位 L1890 直接代入 abl9b_ext_ws_conv 证书，abl9b_rhs_dom1/abl9b_rhs_clamp1_proj/abl9b_rhs_wc_clamp1 收束位）。
   终验：PA 28+1 条全 Closed（零公理残留）；提取安全位检验 tel+gap_eps
   Obj.magic 计 0；正名位 witness 形提取沿件54/59 前例豁免（prod 实例
   化硬错，fail-loud 登记）。合流位=合流池一行终验
   exact (abl9b_rehearse2_merge_check_61 abl9_atan_diff_formula)
   （件61 在 RH2 池，本池不跨域 Require——S6 执行）。
   既有段落：§A 现稿 A1 凸性/wnode/winc 三件原样保真；qs_Z 与件41
   abl9_qs_Z 同形，保留自足件。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import abl_arctan_diff_19.
Require Import abl_arctan_diff_20.
Require Import abl_arctan_diff_45.
Require Import abl_arctan_diff_41.
Require Import abl_arctan_diff_47.
Require Import abl9b_skeleton_30.
Require Import abl9b_rho_chain_53.
Require Import abl9b_ext_chain_54.
Require Import abl9b_rhs_chain_59.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import QArith.Qfield.
From Stdlib Require Import ZArith Extraction.

(* ============================================================ *)
(* §A·Q 层小件（内点装配四基建）                                  *)
(* ============================================================ *)

(* A1·ρ 球凸性：|(1−λ)x+λy| ≤ ρ（|x|,|y|≤ρ、0≤λ≤1）——walk 节点 ρ 界之核 *)
Lemma abl9b2_q_convex_rho : forall (lam x y r : Q),
  Qle 0 lam -> Qle lam 1 ->
  Qle (Qabs x) r -> Qle (Qabs y) r ->
  Qle (Qabs ((1 - lam) * x + lam * y)) r.
Proof.
  intros lam x y r Hl0 Hl1 Hx Hy.
  assert (H1m : Qle 0 (1 - lam)).
  { apply (proj1 (Qle_minus_iff lam 1)). exact Hl1. }
  apply (Qle_trans (Qabs ((1 - lam) * x + lam * y))
                   ((1 - lam) * Qabs x + lam * Qabs y) r).
  - apply (Qle_trans (Qabs ((1 - lam) * x + lam * y))
                     (Qabs ((1 - lam) * x) + Qabs (lam * y))
                     ((1 - lam) * Qabs x + lam * Qabs y)).
    + apply Qabs_triangle.
    + apply Qplus_le_compat.
      * rewrite Qabs_Qmult.
        rewrite (Qabs_pos (1 - lam) H1m).
        apply Qle_refl.
      * rewrite Qabs_Qmult.
        rewrite (Qabs_pos lam Hl0).
        apply Qle_refl.
  - apply (Qle_trans ((1 - lam) * Qabs x + lam * Qabs y)
                     ((1 - lam) * r + lam * r) r).
    + apply Qplus_le_compat.
      * apply (b3_qmult_le_l (Qabs x) r (1 - lam)).
        -- exact H1m.
        -- exact Hx.
      * apply (b3_qmult_le_l (Qabs y) r lam).
        -- exact Hl0.
        -- exact Hy.
    + apply qeq_imp_qle. ring.
Qed.

(* A2·qs 与自然数 Z 形桥（望远镜端项 N·c 的 qs 换算） *)
Lemma abl9b2_qs_Z : forall N : nat, qs N == (Z.of_nat N # 1).
Proof.
  induction N as [| m IH].
  - reflexivity.
  - cbn [qs]. rewrite IH. unfold Qeq. cbn. lia.
Qed.

(* A3·w 节点界：|u−v|≤1/4、|u|,|v|≤1 ⟹ |(u−v)·inv(1+uv)| ≤ 1/3
   （件40 abl9_wpath_pt_bnd 内部 1/3 链的自足重落，导出加强形：
   wpath 导出形仅 ≤1，望远镜 w 侧 rw:=1/2 槽须 1/3） *)
Lemma abl9b2_wnode_bnd : forall (u v : Q),
  Qle (Qabs u) 1 -> Qle (Qabs v) 1 ->
  Qle (Qabs (u - v)) (1 # 4) ->
  Qle (Qabs ((u - v) * Qinv (1 + u * v))) (1 # 3).
Proof.
  intros u v Hu Hv Huv.
  assert (Ht : Qle (Qabs (v - u)) (1 # 4)).
  { apply (Qle_trans (Qabs (v - u)) (Qabs (u - v)) (1 # 4)).
    - apply qeq_imp_qle. apply abl9b_q_abs_minus.
    - exact Huv. }
  assert (HD : Qle (3 # 4) (1 + v * u)).
  { pose proof (abl9_q_path_den u (v - u) Hu Ht) as Hd.
    apply (Qle_trans (3 # 4) (1 + (u + (v - u)) * u) (1 + v * u)).
    - exact (QleT'_to_Qle _ _ Hd).
    - apply qeq_imp_qle. ring. }
  assert (HDeq : (1 + v * u == 1 + u * v)%Q) by ring.
  assert (HDq : Qle (3 # 4) (1 + u * v)).
  { rewrite <- HDeq. exact HD. }
  assert (H34 : Qlt 0 (3 # 4)) by (unfold Qlt; simpl; lia).
  assert (HDpos : Qlt 0 (1 + u * v)).
  { apply (Qlt_le_trans 0 (3 # 4) (1 + u * v)).
    - exact H34.
    - exact HDq. }
  assert (Hinv : Qle (Qinv (1 + u * v)) (4 # 3)).
  { destruct (Qle_lt_or_eq (3 # 4) (1 + u * v) HDq) as [Hlt | Heq].
    - apply Qlt_le_weak.
      exact (proj1 (Qinv_lt_contravar (3 # 4) (1 + u * v) H34 HDpos) Hlt).
    - rewrite (Qeq_sym _ _ Heq). apply Qle_refl. }
  assert (Hshape : Qabs ((u - v) * Qinv (1 + u * v))
                   == Qabs (u - v) * Qinv (1 + u * v)).
  { rewrite Qabs_Qmult. rewrite Qabs_Qinv.
    rewrite (Qabs_pos (1 + u * v) (Qlt_le_weak 0 (1 + u * v) HDpos)).
    reflexivity. }
  rewrite Hshape.
  apply (Qle_trans (Qabs (u - v) * Qinv (1 + u * v)) ((1 # 4) * (4 # 3)) (1 # 3)).
  - apply (Qmult_le_compat_nonneg (Qabs (u - v)) (1 # 4)
             (Qinv (1 + u * v)) (4 # 3)).
    + split; [apply Qabs_nonneg | exact Huv].
    + split.
      * apply Qinv_le_0_compat. apply Qlt_le_weak. exact HDpos.
      * exact Hinv.
  - apply qeq_imp_qle. ring.
Qed.

(* A4·w 增量界：|u|,|u+s|≤ρ<1、|v|≤1 ⟹ |Δw| ≤ 2|s|/((1−ρ)(1−ρ))
   （件19 abl9_wincr_div_id 除法恒等+两分母 1−ρ 下界+跨乘；w 线步界槽） *)
Lemma abl9b2_winc_bnd : forall (rho u s v : Q),
  Qle 0 rho -> Qlt rho 1 ->
  Qle (Qabs u) rho -> Qle (Qabs (u + s)) rho -> Qle (Qabs v) 1 ->
  Qle (Qabs ((u + s - v) * Qinv (1 + (u + s) * v)
             - (u - v) * Qinv (1 + u * v)))
      (2 * Qabs s * Qinv ((1 - rho) * (1 - rho))).
Proof.
  intros rho u s v Hr0 Hr1 Hu Hus Hv.
  assert (H1mr : Qlt 0 (1 - rho))
    by (apply (proj1 (Qlt_minus_iff rho 1)); exact Hr1).
  assert (Hm1 : Qle (- rho) ((u + s) * v))
    by exact (abl9b_q_mul_low rho (u + s) v Hus Hv).
  assert (Hm2 : Qle (- rho) (u * v))
    by exact (abl9b_q_mul_low rho u v Hu Hv).
  assert (Hd1 : Qle (1 - rho) (1 + (u + s) * v))
    by (apply Qplus_le_compat; [apply Qle_refl | exact Hm1]).
  assert (Hd2 : Qle (1 - rho) (1 + u * v))
    by (apply Qplus_le_compat; [apply Qle_refl | exact Hm2]).
  assert (Hnz1 : ~ (1 + (u + s) * v == 0)).
  { intro Hz. apply (Qlt_not_le 0 (1 + (u + s) * v)).
    - apply (Qlt_le_trans 0 (1 - rho) (1 + (u + s) * v)); [exact H1mr | exact Hd1].
    - apply qeq_imp_qle. exact Hz. }
  assert (Hnz2 : ~ (1 + u * v == 0)).
  { intro Hz. apply (Qlt_not_le 0 (1 + u * v)).
    - apply (Qlt_le_trans 0 (1 - rho) (1 + u * v)); [exact H1mr | exact Hd2].
    - apply qeq_imp_qle. exact Hz. }
  pose proof (abl9_wincr_div_id u v s Hnz1 Hnz2) as Hid.
  (* 除法形→Qinv 乘法形（Qdiv 定义性展开） *)
  assert (Hidd : (u + s - v) * Qinv (1 + (u + s) * v)
                 - (u - v) * Qinv (1 + u * v)
                 == s * (1 + v * v) * Qinv ((1 + (u + s) * v) * (1 + u * v))).
  { unfold Qdiv in Hid.
    exact Hid. }
  assert (HD1pos : Qlt 0 ((1 + (u + s) * v) * (1 + u * v))).
  { apply (Qmult_lt_0_compat (1 + (u + s) * v) (1 + u * v)).
    - apply (Qlt_le_trans 0 (1 - rho) (1 + (u + s) * v)); [exact H1mr | exact Hd1].
    - apply (Qlt_le_trans 0 (1 - rho) (1 + u * v)); [exact H1mr | exact Hd2]. }
  assert (Habss : Qabs (s * (1 + v * v) * Qinv ((1 + (u + s) * v) * (1 + u * v)))
                  == Qabs s * (1 + v * v) * Qinv ((1 + (u + s) * v) * (1 + u * v))).
  { rewrite !Qabs_Qmult.
    rewrite (Qabs_pos (1 + v * v)).
    - rewrite (Qabs_pos (Qinv ((1 + (u + s) * v) * (1 + u * v)))).
      + reflexivity.
      + apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HD1pos.
    - apply (Qle_trans 0 (1 + 0) (1 + v * v)).
      + unfold Qle. simpl. lia.
      + apply Qplus_le_compat; [apply Qle_refl | apply Qsquare_nonneg]. }
  assert (Hvv2 : Qle (1 + v * v) 2).
  { apply (Qle_trans (1 + v * v) (1 + Qabs v * Qabs v) 2).
    - apply Qplus_le_compat; [apply Qle_refl | apply qeq_imp_qle].
      apply (Qeq_sym _ _ (abl9b_q_abs_sq v)).
    - apply (Qle_trans (1 + Qabs v * Qabs v) (1 + 1 * 1) 2).
      + apply Qplus_le_compat; [apply Qle_refl | ].
        apply (Qle_trans (Qabs v * Qabs v) (1 * Qabs v) (1 * 1)).
        * apply (Qmult_le_compat_r (Qabs v) 1 (Qabs v)).
          -- exact Hv.
          -- apply Qabs_nonneg.
        * apply (b3_qmult_le_l (Qabs v) 1 1).
          -- exact Qle_0_1.
          -- exact Hv.
      + apply qeq_imp_qle. ring. }
  assert (Hpre : Qle (1 * ((1 - rho) * (1 - rho)))
                     ((1 + (u + s) * v) * (1 + u * v))).
  { apply (Qle_trans (1 * ((1 - rho) * (1 - rho)))
                     ((1 - rho) * (1 - rho))
                     ((1 + (u + s) * v) * (1 + u * v))).
    - apply qeq_imp_qle. ring.
    - apply (Qmult_le_compat_nonneg (1 - rho) (1 + (u + s) * v)
                                    (1 - rho) (1 + u * v)).
      + split.
        * apply Qlt_le_weak. exact H1mr.
        * exact Hd1.
      + split.
        * apply Qlt_le_weak. exact H1mr.
        * exact Hd2. }
  assert (Hinvb : Qle (Qinv ((1 + (u + s) * v) * (1 + u * v)))
                      (Qinv ((1 - rho) * (1 - rho)))).
  { apply (Qle_trans (Qinv ((1 + (u + s) * v) * (1 + u * v)))
                     (1 * Qinv ((1 + (u + s) * v) * (1 + u * v)))
                     (Qinv ((1 - rho) * (1 - rho)))).
    - apply qeq_imp_qle. ring.
    - apply (b5n_xinv_le 1 ((1 + (u + s) * v) * (1 + u * v))
               ((1 - rho) * (1 - rho))).
      + exact HD1pos.
      + apply (Qmult_lt_0_compat (1 - rho) (1 - rho)); exact H1mr.
      + exact Hpre. }
  rewrite Hidd.
  rewrite Habss.
  apply (Qle_trans (Qabs s * (1 + v * v) * Qinv ((1 + (u + s) * v) * (1 + u * v)))
                   (2 * Qabs s * Qinv ((1 - rho) * (1 - rho)))
                   (2 * Qabs s * Qinv ((1 - rho) * (1 - rho)))).
  - apply (Qmult_le_compat_nonneg (Qabs s * (1 + v * v)) (2 * Qabs s)
             (Qinv ((1 + (u + s) * v) * (1 + u * v)))
             (Qinv ((1 - rho) * (1 - rho)))).
    + split.
      * apply (Qmult_le_0_compat (Qabs s) (1 + v * v)).
        -- apply Qabs_nonneg.
        -- apply (Qle_trans 0 (1 + 0) (1 + v * v)).
           ++ unfold Qle. simpl. lia.
           ++ apply Qplus_le_compat; [apply Qle_refl | apply Qsquare_nonneg].
      * apply (Qle_trans (Qabs s * (1 + v * v)) (Qabs s * 2) (2 * Qabs s)).
        -- apply (b3_qmult_le_l (1 + v * v) 2 (Qabs s)).
           ++ apply Qabs_nonneg.
           ++ exact Hvv2.
        -- apply qeq_imp_qle. ring.
    + split.
      * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HD1pos.
      * exact Hinvb.
  - apply Qle_refl.
Qed.

(* ============================================================ *)
(* §B·A2 主公式 Q 投影差项与闭域版接口骨架（案A 量词序裁决）        *)
(*   案A 铁律：语句面量词序取件30 Hdiff 槽形基准——x Hx 前置序，      *)
(*   h Hh4 Hxh 后随（合流裁决一）；域三假设语义拟文                *)
(*   逐字不动；Hd 证明项逐字 abl9b_dom_pos x h Hx Hh4（R-T2 铁律，   *)
(*   real_inv_pos 定义体对证明项 match，禁任何等价证明项替换）。      *)
(* ============================================================ *)

(* B1·A2 主公式 Q 投影差项（闭域 |x|≤1 语句面的逐点尾差——层2 闭合   *)
(*   证书的承载位；与 real_eq 展开形逐槽同构：eps/N/n≥N/QltT 四槽）   *)
Definition abl9_atan_diff_gap_pt (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) : Q :=
  arctan_partial n (projT1 (real_plus x h) n)
  - arctan_partial n (projT1 x n)
  - arctan_partial n (projT1 (abl9b_wc x h (abl9b_dom_pos x h Hx Hh4)) n).

(* B2·闭域版接口骨架：层2 延拓闭合证书（尾段逐 eps 界）作显式前件    *)
(*   参数位——证书逐槽转译即主公式 real_eq（对接证明：投影链          *)
(*   real_plus_proj/real_opp_proj/arctan_real_proj + Qabs_wd 传输）。 *)
Lemma abl9_atan_diff_formula_skel :
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (h : Real) (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
    (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  (forall eps : Q, QltT 0 eps ->
     sigT (fun N : nat => forall n : nat, NatLe N n ->
       QltT (Qabs (abl9_atan_diff_gap_pt x h Hx Hh4 Hxh n)) eps)) ->
  real_eq (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
             (real_opp (cauchy_real_arctan x Hx)))
          (cauchy_real_arctan (abl9b_wc x h (abl9b_dom_pos x h Hx Hh4))
             (abl9b_w_clamp_dom (abl9b_w x h (abl9b_dom_pos x h Hx Hh4)))).
Proof.
  intros x Hx h Hh4 Hxh Hconv eps Heps.
  unfold real_eq.
  destruct (Hconv eps Heps) as [N HN].
  exists N. intros n Hn.
  apply (abl9_QltT_transfer_l
     (Qabs (projT1 (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                      (real_opp (cauchy_real_arctan x Hx))) n
            - projT1 (cauchy_real_arctan
                        (abl9b_wc x h (abl9b_dom_pos x h Hx Hh4))
                        (abl9b_w_clamp_dom
                           (abl9b_w x h (abl9b_dom_pos x h Hx Hh4)))) n))
     (Qabs (abl9_atan_diff_gap_pt x h Hx Hh4 Hxh n)) eps).
  - apply abl9_Qabs_wd.
    rewrite (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
               (real_opp (cauchy_real_arctan x Hx)) n).
    rewrite (arctan_real_proj (real_plus x h) Hxh n).
    rewrite (real_opp_proj (cauchy_real_arctan x Hx) n).
    rewrite (arctan_real_proj x Hx n).
    rewrite (arctan_real_proj
               (abl9b_wc x h (abl9b_dom_pos x h Hx Hh4))
               (abl9b_w_clamp_dom (abl9b_w x h (abl9b_dom_pos x h Hx Hh4))) n).
    unfold abl9_atan_diff_gap_pt. ring.
  - exact (HN n Hn).
Qed.

(* ============================================================ *)
(* §C·内点版（|x_n|≤ρ<1，ρ 参数化）全闭合                            *)
(*   走廊=固定剖分 N 的 Q 层等步 u-走廊（节点 u_k=u+qs k·t，t=s/N）   *)
(*   与 w-走廊像 w_k=(u_k−u)·inv(1+u_k·u)（v:=u 参考点，w_0=0、       *)
(*   w_N=w 恰为主公式 RHS 实参）；逐步差=件53 abl9b_phistep_rho        *)
(*   （ρ 参数化 φ 步界机）直供；节点界=§A 四件直供；端项=件51 定量     *)
(*   望远镜思想的 K 步归纳闭合。                                        *)
(* ============================================================ *)

(* C0·走廊帮件五件                                                   *)

(* C0a·qs 非负（件41 qs_pos 只给 1≤K 严格形；K=0 支自补） *)
Lemma abl9b2_qs_nonneg : forall k : nat, Qle 0 (qs k).
Proof.
  induction k as [| m IH].
  - cbn [qs]. apply Qle_refl.
  - cbn [qs]. apply (Qle_trans 0 (qs m) (qs m + 1)).
    + exact IH.
    + apply (abl9b_q_self_plus_le (qs m) 1).
      unfold Qle. simpl. lia.
Qed.

(* C0b·u 走廊节点 ρ 界（§A A1 凸性件实例化：lam:=qs k·inv(qs N)） *)
Lemma abl9b2_uk_bnd : forall (rho u s : Q) (N K : nat),
  (1 <= N)%nat -> (K <= N)%nat ->
  Qle (Qabs u) rho -> Qle (Qabs (u + s)) rho ->
  Qle (Qabs (u + qs K * (s * Qinv (Z.of_nat N # 1)))) rho.
Proof.
  intros rho u s N K HN HKN Hu Hus.
  assert (HNz : Qlt 0 (Z.of_nat N # 1)).
  { apply (abl9_Qlt_transfer_r 0 (qs N) (Z.of_nat N # 1)).
    - apply abl9_qs_Z.
    - apply abl9_qs_pos. exact HN. }
  assert (Hinv0 : Qle 0 (Qinv (Z.of_nat N # 1))).
  { apply Qinv_le_0_compat. apply Qlt_le_weak. exact HNz. }
  apply (Qle_trans (Qabs (u + qs K * (s * Qinv (Z.of_nat N # 1))))
                   (Qabs ((1 - qs K * Qinv (Z.of_nat N # 1)) * u
                          + qs K * Qinv (Z.of_nat N # 1) * (u + s))) rho).
  - apply qeq_imp_qle. apply abl9_Qabs_wd. ring.
  - apply (abl9b2_q_convex_rho (qs K * Qinv (Z.of_nat N # 1)) u (u + s) rho).
    + apply Qmult_le_0_compat.
      * exact (abl9b2_qs_nonneg K).
      * exact Hinv0.
    + apply (Qle_trans (qs K * Qinv (Z.of_nat N # 1))
                       (Qinv (Z.of_nat N # 1) * qs N) 1).
      * apply (Qle_trans (qs K * Qinv (Z.of_nat N # 1))
                         (Qinv (Z.of_nat N # 1) * qs K)
                         (Qinv (Z.of_nat N # 1) * qs N)).
        -- apply qeq_imp_qle. ring.
        -- apply (b3_qmult_le_l (qs K) (qs N) (Qinv (Z.of_nat N # 1))).
           ++ exact Hinv0.
           ++ exact (abl9_qs_mono K N HKN).
      * apply qeq_imp_qle.
        rewrite (abl9_qs_Z N).
        rewrite (Qmult_comm (Qinv (Z.of_nat N # 1))).
        rewrite (Qmult_inv_r (Z.of_nat N # 1)).
        -- ring.
        -- intro Hz. apply (Qlt_not_le 0 (Z.of_nat N # 1)).
           ++ exact HNz.
           ++ rewrite Hz. apply Qle_refl.
    + exact Hu.
    + exact Hus.
Qed.

(* C0c·|u_k−u| ≤ 1/4（|qs k·t| = qs k·|t| ≤ qs N·|t| = |s| ≤ 1/4） *)
Lemma abl9b2_uk_delta : forall (u s : Q) (N K : nat),
  (1 <= N)%nat -> (K <= N)%nat -> Qle (Qabs s) (1 # 4) ->
  Qle (Qabs ((u + qs K * (s * Qinv (Z.of_nat N # 1))) - u)) (1 # 4).
Proof.
  intros u s N K HN HKN Hs.
  assert (HNz : Qlt 0 (Z.of_nat N # 1)).
  { apply (abl9_Qlt_transfer_r 0 (qs N) (Z.of_nat N # 1)).
    - apply abl9_qs_Z.
    - apply abl9_qs_pos. exact HN. }
  apply (Qle_trans (Qabs ((u + qs K * (s * Qinv (Z.of_nat N # 1))) - u))
                   (Qabs (qs K * (s * Qinv (Z.of_nat N # 1)))) (1 # 4)).
  - apply qeq_imp_qle. apply abl9_Qabs_wd. ring.
  - apply (Qle_trans (Qabs (qs K * (s * Qinv (Z.of_nat N # 1))))
                     (qs N * (Qabs s * Qinv (Z.of_nat N # 1))) (1 # 4)).
    + apply (Qle_trans (Qabs (qs K * (s * Qinv (Z.of_nat N # 1))))
                       (qs K * Qabs (s * Qinv (Z.of_nat N # 1)))
                       (qs N * (Qabs s * Qinv (Z.of_nat N # 1)))).
      * apply qeq_imp_qle.
        rewrite Qabs_Qmult.
        rewrite (Qabs_pos (qs K) (abl9b2_qs_nonneg K)).
        ring.
      * apply (Qle_trans (qs K * Qabs (s * Qinv (Z.of_nat N # 1)))
                         (Qabs (s * Qinv (Z.of_nat N # 1)) * qs N)
                         (qs N * (Qabs s * Qinv (Z.of_nat N # 1)))).
        -- apply (Qle_trans (qs K * Qabs (s * Qinv (Z.of_nat N # 1)))
                            (Qabs (s * Qinv (Z.of_nat N # 1)) * qs K)
                            (Qabs (s * Qinv (Z.of_nat N # 1)) * qs N)).
           ++ apply qeq_imp_qle. ring.
           ++ apply (b3_qmult_le_l (qs K) (qs N)
                       (Qabs (s * Qinv (Z.of_nat N # 1)))).
              ** apply Qabs_nonneg.
              ** exact (abl9_qs_mono K N HKN).
        -- apply qeq_imp_qle.
           rewrite Qabs_Qmult.
           rewrite (Qabs_pos (Qinv (Z.of_nat N # 1))
                      (Qlt_le_weak 0 (Qinv (Z.of_nat N # 1))
                         (Qinv_lt_0_compat (Z.of_nat N # 1) HNz))).
           ring.
    + apply (Qle_trans (qs N * (Qabs s * Qinv (Z.of_nat N # 1)))
                       (Qabs s) (1 # 4)).
      * apply qeq_imp_qle.
        rewrite (abl9_qs_Z N).
        rewrite Qmult_assoc.
        rewrite (Qmult_comm (Z.of_nat N # 1) (Qabs s)).
        rewrite <- Qmult_assoc.
        rewrite (Qmult_inv_r (Z.of_nat N # 1)).
        -- ring.
        -- intro Hz. apply (Qlt_not_le 0 (Z.of_nat N # 1)).
           ++ exact HNz.
           ++ rewrite Hz. apply Qle_refl.
      * exact Hs.
Qed.

(* C0d·w 走廊节点 1/3 界（§A A3 件直供：|u_k|≤ρ≤1、|u|≤1、|u_k−u|≤1/4） *)
Lemma abl9b2_wk_bnd : forall (rho u s : Q) (N K : nat),
  (1 <= N)%nat -> (K <= N)%nat ->
  Qle (Qabs u) rho -> Qle (Qabs (u + s)) rho -> Qlt rho 1 ->
  Qle (Qabs s) (1 # 4) ->
  Qle (Qabs ((u + qs K * (s * Qinv (Z.of_nat N # 1)) - u)
             * Qinv (1 + (u + qs K * (s * Qinv (Z.of_nat N # 1))) * u)))
      (1 # 3).
Proof.
  intros rho u s N K HN HKN Hu Hus Hr1 Hs.
  apply (abl9b2_wnode_bnd (u + qs K * (s * Qinv (Z.of_nat N # 1))) u).
  - apply (Qle_trans (Qabs (u + qs K * (s * Qinv (Z.of_nat N # 1)))) rho 1).
    + apply (abl9b2_uk_bnd rho u s N K HN HKN Hu Hus).
    + exact (Qlt_le_weak rho 1 Hr1).
  - exact (Qle_trans (Qabs u) rho 1 Hu (Qlt_le_weak rho 1 Hr1)).
  - apply (abl9b2_uk_delta u s N K).
    + exact HN.
    + exact HKN.
    + exact Hs.
Qed.

(* C0e·正即非零（field 侧条件通供） *)
Lemma abl9b2_nz_of_pos : forall X : Q, Qlt 0 X -> ~ (X == 0).
Proof.
  intros X H Hz. apply (Qlt_not_le 0 X H). rewrite Hz. apply Qle_refl.
Qed.

(* C0f·Qle 左向 Qeq 传输（Qeq 换形不破门） *)
Lemma abl9b2_qle_transfer_l : forall a b c : Q, a == b -> Qle b c -> Qle a c.
Proof.
  intros a b c Hab Hbc. apply (Qle_trans a b c).
  - apply qeq_imp_qle. exact Hab.
  - exact Hbc.
Qed.

(* C1·步界带（逐步界 B 的正则形；t 为步长，rw 固定 1/3） *)
Definition abl9b2_dwb (rho t : Q) : Q :=
  2 * Qabs t * Qinv ((1 - rho) * (1 - rho)).

Definition abl9b2_stepbnd (rho t : Q) (n0 : nat) : Q :=
  b3rr_C2 ((1 # 2) * (1 + rho)) * (Qabs t * Qabs t)
  + Qabs t * q_pow rho (2 * Nat.succ n0)
  + b3rr_C2 ((1 # 2) * (1 + (1 # 3))) * (abl9b2_dwb rho t * abl9b2_dwb rho t)
  + abl9b2_dwb rho t * q_pow (1 # 3) (2 * Nat.succ n0)
  + Qinv (1 - rho) * (Qabs t * Qabs t).

(* w 走廊像函数：wf u v := (u−v)·inv(1+u·v)（phistep_rho 的 w 槽定义形） *)
Definition abl9b2_wf (u v : Q) : Q := (u - v) * Qinv (1 + u * v).

Lemma abl9b2_wf_wd : forall u1 u2 v : Q, u1 == u2 -> abl9b2_wf u1 v == abl9b2_wf u2 v.
Proof.
  intros u1 u2 v Hab. unfold abl9b2_wf. rewrite Hab. reflexivity.
Qed.

(* 步拆分恒等（抽象变量形——ring 于复合原子形失效的隔离复现对策） *)
Lemma abl9b2_arith_split : forall pa pk pu pw1 pw0 : Q,
  (pa - pu - pw1) == ((pa - pk - (pw1 - pw0)) + (pk - pu - pw0)).
Proof.
  intros pa pk pu pw1 pw0. ring.
Qed.

(*C1a·单步链：件53abl9b_phistep_rho 直接匹配（w:=w(u,v)、dw:=w(u+t,v)−w(u,v)）
   + 项界正则化（T3/T4 的 |dw| 槽与 T5 的 t·t 槽正则到 B 形） *)
Lemma abl9b2_step_chain :
  forall (rho u v t : Q) (n0 : nat),
  Qle 0 rho -> Qlt rho 1 ->
  Qle (Qabs u) rho -> Qle (Qabs (u + t)) rho ->
  Qle (Qabs t) ((1 # 2) * (1 - rho)) ->
  Qle (Qabs v) 1 ->
  Qle (Qabs ((u - v) * Qinv (1 + u * v))) (1 # 3) ->
  Qle (Qabs ((u + t - v) * Qinv (1 + (u + t) * v))) (1 # 3) ->
  Qle (Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
             - (u - v) * Qinv (1 + u * v))) (abl9b2_dwb rho t) ->
  Qle (abl9b2_dwb rho t) (1 # 3) ->
  Qle (Qabs (arctan_partial n0 (u + t) - arctan_partial n0 u
             - (arctan_partial n0 ((u + t - v) * Qinv (1 + (u + t) * v))
                - arctan_partial n0 ((u - v) * Qinv (1 + u * v)))))
      (abl9b2_stepbnd rho t n0).
Proof.
  intros rho u v t n0 Hr0 Hr1 Hu Hut Ht Hv Hwu Hwut Hdw Hdwb.
  assert (H1mr : Qlt 0 (1 - rho)).
  { apply (proj1 (Qlt_minus_iff rho 1)). exact Hr1. }
  assert (Hdw0 : Qle 0 (abl9b2_dwb rho t)).
  { apply (Qle_trans 0 (Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                              - (u - v) * Qinv (1 + u * v))) (abl9b2_dwb rho t)).
    - apply Qabs_nonneg.
    - exact Hdw. }
  assert (Hwdeq : (u - v) * Qinv (1 + u * v)
                  + ((u + t - v) * Qinv (1 + (u + t) * v)
                     - (u - v) * Qinv (1 + u * v))
                  == (u + t - v) * Qinv (1 + (u + t) * v)) by ring.
  assert (Hslot13 : Qle (abl9b2_dwb rho t) ((1 # 2) * (1 - (1 # 3)))).
  { apply (Qle_trans (abl9b2_dwb rho t) (1 # 3) ((1 # 2) * (1 - (1 # 3)))).
    - exact Hdwb.
    - unfold Qle. simpl. lia. }
  assert (Hq03 : Qle 0 (1 # 3)) by (unfold Qle; simpl; lia).
  assert (Hq131 : Qlt (1 # 3) 1) by (unfold Qlt; simpl; lia).
  assert (Hq023 : Qle 0 ((1 # 2) * (1 + (1 # 3))))
    by (unfold Qle; simpl; lia).
  assert (Hq231 : Qlt ((1 # 2) * (1 + (1 # 3))) 1)
    by (unfold Qlt; simpl; lia).
  pose proof (abl9b_phistep_rho rho (1 # 3) u t v
               ((u - v) * Qinv (1 + u * v))
               ((u + t - v) * Qinv (1 + (u + t) * v)
                  - (u - v) * Qinv (1 + u * v)) n0
               Hr0 Hr1 Hq03 Hq131
               Hu Hut Ht Hv eq_refl eq_refl
               Hwu
               (abl9b2_qle_transfer_l
                  (Qabs ((u - v) * Qinv (1 + u * v)
                           + ((u + t - v) * Qinv (1 + (u + t) * v)
                              - (u - v) * Qinv (1 + u * v))))
                  (Qabs ((u + t - v) * Qinv (1 + (u + t) * v))) (1 # 3)
                  (abl9_Qabs_wd _ _ Hwdeq) Hwut)
               (Qle_trans (Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                            - (u - v) * Qinv (1 + u * v)))
                  (abl9b2_dwb rho t) ((1 # 2) * (1 - (1 # 3))) Hdw Hslot13)) as Hps.
  unfold abl9b2_stepbnd.
  apply (Qle_trans
           (Qabs (arctan_partial n0 (u + t) - arctan_partial n0 u
                  - (arctan_partial n0 ((u + t - v) * Qinv (1 + (u + t) * v))
                     - arctan_partial n0 ((u - v) * Qinv (1 + u * v)))))
           (b3rr_C2 ((1 # 2) * (1 + rho)) * (Qabs t * Qabs t)
            + Qabs t * q_pow rho (2 * Nat.succ n0)
            + b3rr_C2 ((1 # 2) * (1 + (1 # 3)))
              * (Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                        - (u - v) * Qinv (1 + u * v))
                 * Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                         - (u - v) * Qinv (1 + u * v)))
            + Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                    - (u - v) * Qinv (1 + u * v))
              * q_pow (1 # 3) (2 * Nat.succ n0)
            + Qinv (1 - rho) * (t * t))
           (b3rr_C2 ((1 # 2) * (1 + rho)) * (Qabs t * Qabs t)
            + Qabs t * q_pow rho (2 * Nat.succ n0)
            + b3rr_C2 ((1 # 2) * (1 + (1 # 3))) * (abl9b2_dwb rho t * abl9b2_dwb rho t)
            + abl9b2_dwb rho t * q_pow (1 # 3) (2 * Nat.succ n0)
            + Qinv (1 - rho) * (Qabs t * Qabs t))).
  - apply (Qle_trans
             (Qabs (arctan_partial n0 (u + t) - arctan_partial n0 u
                    - (arctan_partial n0 ((u + t - v) * Qinv (1 + (u + t) * v))
                       - arctan_partial n0 ((u - v) * Qinv (1 + u * v)))))
             (Qabs (arctan_partial n0 (u + t) - arctan_partial n0 u
                    - (arctan_partial n0 ((u - v) * Qinv (1 + u * v)
                         + ((u + t - v) * Qinv (1 + (u + t) * v)
                            - (u - v) * Qinv (1 + u * v)))
                       - arctan_partial n0 ((u - v) * Qinv (1 + u * v)))))
             (b3rr_C2 ((1 # 2) * (1 + rho)) * (Qabs t * Qabs t)
              + Qabs t * q_pow rho (2 * Nat.succ n0)
              + b3rr_C2 ((1 # 2) * (1 + (1 # 3)))
                * (Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                          - (u - v) * Qinv (1 + u * v))
                   * Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                           - (u - v) * Qinv (1 + u * v)))
              + Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                      - (u - v) * Qinv (1 + u * v))
                * q_pow (1 # 3) (2 * Nat.succ n0)
              + Qinv (1 - rho) * (t * t))).
    + apply qeq_imp_qle. apply abl9_Qabs_wd.
      rewrite (b5c_arctan_partial_wd n0
                 ((u + t - v) * Qinv (1 + (u + t) * v))
                 ((u - v) * Qinv (1 + u * v)
                  + ((u + t - v) * Qinv (1 + (u + t) * v)
                     - (u - v) * Qinv (1 + u * v)))).
      * ring.
      * exact (Qeq_sym _ _ Hwdeq).
    + exact Hps.
  - apply Qplus_le_compat.
    + apply Qplus_le_compat.
      * apply Qplus_le_compat.
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply Qle_refl.
        -- apply (b3_qmult_le_l
                     (Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                            - (u - v) * Qinv (1 + u * v))
                      * Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                              - (u - v) * Qinv (1 + u * v)))
                     (abl9b2_dwb rho t * abl9b2_dwb rho t)
                     (b3rr_C2 ((1 # 2) * (1 + (1 # 3))))).
           ++ exact (b3rr_C2_0 ((1 # 2) * (1 + (1 # 3))) Hq023 Hq231).
           ++ apply (Qle_trans
                        (Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                               - (u - v) * Qinv (1 + u * v))
                         * Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                                 - (u - v) * Qinv (1 + u * v)))
                        (Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                               - (u - v) * Qinv (1 + u * v))
                         * abl9b2_dwb rho t)
                        (abl9b2_dwb rho t * abl9b2_dwb rho t)).
           ** apply (b3_qmult_le_l
                        (Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                               - (u - v) * Qinv (1 + u * v)))
                        (abl9b2_dwb rho t)
                        (Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                               - (u - v) * Qinv (1 + u * v)))).
              --- apply Qabs_nonneg.
              --- exact Hdw.
           ** apply (Qmult_le_compat_r
                        (Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                               - (u - v) * Qinv (1 + u * v)))
                        (abl9b2_dwb rho t) (abl9b2_dwb rho t)).
              --- exact Hdw.
              --- exact Hdw0.
      * apply (Qmult_le_compat_r
                  (Qabs ((u + t - v) * Qinv (1 + (u + t) * v)
                         - (u - v) * Qinv (1 + u * v)))
                  (abl9b2_dwb rho t) (q_pow (1 # 3) (2 * Nat.succ n0))).
        -- exact Hdw.
        -- apply q_pow_nonneg. unfold Qle. simpl. lia.
    + apply (b3_qmult_le_l (t * t) (Qabs t * Qabs t) (Qinv (1 - rho))).
      * apply Qinv_le_0_compat. apply Qlt_le_weak. exact H1mr.
      * apply qeq_imp_qle. exact (Qeq_sym _ _ (abl9b_q_abs_sq t)).
Qed.

(* C1·主件：等步 N 剖分走廊望远镜——主公式 Q 差项 ≤ N·B（B=步界带） *)

(* C1a·arctan 项/部分和在零点恒零（走廊端项 w_0=0 化简位） *)
Lemma abl9b2_at_zero : forall k : nat, arctan_term k 0 == 0.
Proof.
  intros k. unfold arctan_term, Qdiv.
  assert (Hp : q_pow 0 (2 * k + 1) == 0).
  { replace (2 * k + 1)%nat with (Datatypes.S (2 * k)) by lia.
    cbn [q_pow]. ring. }
  rewrite Hp. ring.
Qed.

Lemma abl9b2_ap_zero : forall n : nat, arctan_partial n 0 == 0.
Proof.
  induction n as [| m IH].
  - cbn [arctan_partial]. apply abl9b2_at_zero.
  - cbn [arctan_partial]. rewrite (abl9b2_at_zero (Datatypes.S m)).
    rewrite IH. ring.
Qed.

(* C1b·正因子除法换算（走廊约束 (N#1)·c ≥ 阈值 ⟹ 阈值·inv(N#1) ≤ c） *)
Lemma abl9b2_share : forall A B Y : Q,
  Qlt 0 Y -> Qle A (B * Y) -> Qle (A * Qinv Y) B.
Proof.
  intros A B Y Hy Hab.
  apply (Qle_trans (A * Qinv Y) (Qinv Y * (B * Y)) B).
  - apply (abl9b2_qle_transfer_l (A * Qinv Y) (Qinv Y * A) (Qinv Y * (B * Y))).
    + ring.
    + apply (b3_qmult_le_l A (B * Y) (Qinv Y)).
      * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hy.
      * exact Hab.
  - assert (Hnz : ~ (Y == 0)) by (apply (abl9b2_nz_of_pos Y Hy)).
    apply qeq_imp_qle.
    rewrite (Qmult_comm (Qinv Y) (B * Y)). rewrite <- Qmult_assoc.
    rewrite (Qmult_inv_r Y Hnz). apply (Qmult_1_r B).
Qed.

(* C1c'·K 步走廊望远镜（Htel 主件）：单步链沿等步剖分归纳闭合——
   |A_n0(u_K)−A_n0(u)−(A_n0(w_K)−A_n0(w_0))| ≤ qs K·B（B=步界带；
   归纳步=arith 分裂 qeq+Qabs_triangle+单步链直接匹配，两段式）   *)
Lemma abl9b2_tel : forall (rho u s : Q) (N K n0 : nat),
  Qle 0 rho -> Qlt rho 1 ->
  (1 <= N)%nat -> (K <= N)%nat ->
  Qle (Qabs u) rho -> Qle (Qabs (u + s)) rho ->
  Qle (Qabs s) (1 # 4) ->
  Qle (Qabs (s * Qinv (Z.of_nat N # 1))) ((1 # 2) * (1 - rho)) ->
  Qle (abl9b2_dwb rho (s * Qinv (Z.of_nat N # 1))) (1 # 3) ->
  Qle (Qabs (arctan_partial n0 (u + qs K * (s * Qinv (Z.of_nat N # 1)))
             - arctan_partial n0 u
             - (arctan_partial n0 (abl9b2_wf (u + qs K * (s * Qinv (Z.of_nat N # 1))) u)
                - arctan_partial n0 (abl9b2_wf u u))))
      (qs K * abl9b2_stepbnd rho (s * Qinv (Z.of_nat N # 1)) n0).
Proof.
  intros rho u s N K n0 Hr0 Hr1 HN HKN Hu Hus Hs Ht Hdwb.
  induction K as [| K IH].
  - (* K=0：gap 恒零（u_0=u、w_0=wf u u=0） *)
    apply (abl9b2_qle_transfer_l
             (Qabs (arctan_partial n0 (u + qs 0 * (s * Qinv (Z.of_nat N # 1)))
                    - arctan_partial n0 u
                    - (arctan_partial n0 (abl9b2_wf (u + qs 0 * (s * Qinv (Z.of_nat N # 1))) u)
                       - arctan_partial n0 (abl9b2_wf u u))))
             0 (qs 0 * abl9b2_stepbnd rho (s * Qinv (Z.of_nat N # 1)) n0)).
    + assert (Hu0 : (u + qs 0 * (s * Qinv (Z.of_nat N # 1))) == u)
        by (cbn [qs]; ring).
      assert (Hw0 : abl9b2_wf (u + qs 0 * (s * Qinv (Z.of_nat N # 1))) u
                    == abl9b2_wf u u).
      { unfold abl9b2_wf. cbn [qs]. ring. }
      rewrite (b5c_arctan_partial_wd n0
                 (u + qs 0 * (s * Qinv (Z.of_nat N # 1))) u Hu0).
      rewrite (b5c_arctan_partial_wd n0
                 (abl9b2_wf (u + qs 0 * (s * Qinv (Z.of_nat N # 1))) u)
                 (abl9b2_wf u u) Hw0).
      transitivity (Qabs 0%Q).
      * apply abl9_Qabs_wd. ring.
      * reflexivity.
    + apply qeq_imp_qle. cbn [qs]. ring.
  - (* S K：gap_{S K} == gap_K + step（ring 分裂）+ 三角 + 单步链 *)
    assert (HKN' : (K <= N)%nat) by lia.
    pose proof (IH HKN') as IHK.
    assert (HuK : ((u + qs K * (s * Qinv (Z.of_nat N # 1)))
                   + (s * Qinv (Z.of_nat N # 1)))
                  == u + qs (Datatypes.S K) * (s * Qinv (Z.of_nat N # 1))).
    { cbn [qs]. ring. }
    pose proof (abl9b2_uk_bnd rho u s N K HN HKN' Hu Hus) as Huk.
    pose proof (abl9b2_uk_bnd rho u s N (Datatypes.S K) HN HKN Hu Hus) as Huk1.
    pose proof (abl9b2_wk_bnd rho u s N K HN HKN' Hu Hus Hr1 Hs) as Hwk.
    pose proof (abl9b2_wk_bnd rho u s N (Datatypes.S K) HN HKN Hu Hus Hr1 Hs)
      as Hwk1.
    assert (Huk1t : Qle (Qabs ((u + qs K * (s * Qinv (Z.of_nat N # 1)))
                               + (s * Qinv (Z.of_nat N # 1)))) rho).
    { apply (abl9b2_qle_transfer_l
               (Qabs ((u + qs K * (s * Qinv (Z.of_nat N # 1)))
                      + (s * Qinv (Z.of_nat N # 1))))
               (Qabs (u + qs (Datatypes.S K) * (s * Qinv (Z.of_nat N # 1)))) rho).
      - apply abl9_Qabs_wd. exact HuK.
      - exact Huk1. }
    assert (Hv1 : Qle (Qabs u) 1)
      by exact (Qle_trans (Qabs u) rho 1 Hu (Qlt_le_weak rho 1 Hr1)).
    assert (Hwk1t : Qle (Qabs (((u + qs K * (s * Qinv (Z.of_nat N # 1)))
                                + (s * Qinv (Z.of_nat N # 1)) - u)
                         * Qinv (1 + ((u + qs K * (s * Qinv (Z.of_nat N # 1)))
                                      + (s * Qinv (Z.of_nat N # 1))) * u)))
                  (1 # 3)).
    { apply (abl9b2_qle_transfer_l
               (Qabs (((u + qs K * (s * Qinv (Z.of_nat N # 1)))
                       + (s * Qinv (Z.of_nat N # 1)) - u)
                * Qinv (1 + ((u + qs K * (s * Qinv (Z.of_nat N # 1)))
                             + (s * Qinv (Z.of_nat N # 1))) * u)))
               (Qabs ((u + qs (Datatypes.S K) * (s * Qinv (Z.of_nat N # 1)) - u)
                * Qinv (1 + (u + qs (Datatypes.S K) * (s * Qinv (Z.of_nat N # 1))) * u)))
               (1 # 3)).
      - apply abl9_Qabs_wd. rewrite <- HuK. ring.
      - exact Hwk1. }
    pose proof (abl9b2_winc_bnd rho
                 (u + qs K * (s * Qinv (Z.of_nat N # 1)))
                 (s * Qinv (Z.of_nat N # 1)) u Hr0 Hr1 Huk Huk1t Hv1) as Hwin.
    pose proof (abl9b2_step_chain rho
                 (u + qs K * (s * Qinv (Z.of_nat N # 1))) u
                 (s * Qinv (Z.of_nat N # 1)) n0
                 Hr0 Hr1 Huk Huk1t Ht Hv1 Hwk Hwk1t Hwin Hdwb) as Hstep.
    + (* 主链：|gap_{S K}| ≤ |gap_K| + |step| ≤ qs (S K)·B——
         先 unfold wf、九原子 remember（in *，主定理与 IHK/Hstep 同步原子化），
         之后全链小项 ring/Qabs_triangle 闭合 *)
      unfold abl9b2_wf in *.
      remember (arctan_partial n0 (u + qs (Datatypes.S K) * (s * Qinv (Z.of_nat N # 1)))) as aSK in *.
      remember (arctan_partial n0 ((u + qs (Datatypes.S K) * (s * Qinv (Z.of_nat N # 1)) - u)
                           * Qinv (1 + (u + qs (Datatypes.S K) * (s * Qinv (Z.of_nat N # 1))) * u))) as wSK in *.
      remember (arctan_partial n0 u) as au in *.
      remember (arctan_partial n0 ((u - u) * Qinv (1 + u * u))) as aw0 in *.
      remember (arctan_partial n0 (u + qs K * (s * Qinv (Z.of_nat N # 1)))) as auK in *.
      remember (arctan_partial n0 ((u + qs K * (s * Qinv (Z.of_nat N # 1)) - u)
                           * Qinv (1 + (u + qs K * (s * Qinv (Z.of_nat N # 1))) * u))) as pwK in *.
      remember (arctan_partial n0 ((u + qs K * (s * Qinv (Z.of_nat N # 1)))
                                   + (s * Qinv (Z.of_nat N # 1)))) as auKt in *.
      remember (arctan_partial n0 (((u + qs K * (s * Qinv (Z.of_nat N # 1)))
                                    + (s * Qinv (Z.of_nat N # 1)) - u)
                           * Qinv (1 + ((u + qs K * (s * Qinv (Z.of_nat N # 1)))
                                        + (s * Qinv (Z.of_nat N # 1))) * u))) as pwKt in *.
      assert (Hgq : aSK == auKt).
      { rewrite HeqaSK. rewrite HeqauKt. rewrite <- HuK. ring. }
      assert (Hwq : wSK == pwKt).
      { rewrite HeqwSK. rewrite HeqpwKt. rewrite <- HuK. ring. }
      rewrite Hgq. rewrite Hwq.
      apply (Qle_trans _ (Qabs (auK - au - (pwK - aw0))
                           + Qabs (auKt - auK - (pwKt - pwK)))
               (qs (Datatypes.S K) * abl9b2_stepbnd rho (s * Qinv (Z.of_nat N # 1)) n0)).
      * apply (Qle_trans _
                 (Qabs (auK - au - (pwK - aw0) + (auKt - auK - (pwKt - pwK))))
                 (Qabs (auK - au - (pwK - aw0))
                  + Qabs (auKt - auK - (pwKt - pwK)))).
        -- apply qeq_imp_qle. apply abl9_Qabs_wd. ring.
        -- apply Qabs_triangle.
      * apply (Qle_trans _
                 (qs K * abl9b2_stepbnd rho (s * Qinv (Z.of_nat N # 1)) n0
                  + abl9b2_stepbnd rho (s * Qinv (Z.of_nat N # 1)) n0) _).
        -- apply Qplus_le_compat; [exact IHK | exact Hstep].
        -- apply qeq_imp_qle. cbn [qs]. ring.
Qed.


Definition abl9b2_k123 (rho : Q) : Q :=
  b3rr_C2 ((1 # 2) * (1 + rho)) + Qinv (1 - rho)
  + 4 * b3rr_C2 ((1 # 2) * (1 + (1 # 3)))
      * Qinv ((1 - rho) * (1 - rho)) * Qinv ((1 - rho) * (1 - rho)).

Definition abl9b2_totbnd (rho s : Q) (N n0 : nat) : Q :=
  abl9b2_k123 rho * (Qabs s * Qabs s) * Qinv (Z.of_nat N # 1)
  + Qabs s * q_pow rho (2 * Nat.succ n0)
  + 2 * Qabs s * Qinv ((1 - rho) * (1 - rho)) * q_pow (1 # 3) (2 * Nat.succ n0).

(* 步带乘 N 的 inv 归一恒等（代数闭合走 field 反射项；序链仍全显式） *)
Lemma abl9b2_totbnd_eq : forall (M s h P W C2a C2b iR : Q),
  ~ (M == 0) ->
  M * (C2a * ((s * Qinv M) * (s * Qinv M)) + (s * Qinv M) * P
       + C2b * ((2 * (s * Qinv M) * h) * (2 * (s * Qinv M) * h))
       + (2 * (s * Qinv M) * h) * W + iR * ((s * Qinv M) * (s * Qinv M)))
  == (C2a + iR + 4 * C2b * h * h) * (s * s * Qinv M)
     + s * P + 2 * s * h * W.
Proof.
  intros M s h P W C2a C2b iR Hnz. field. exact Hnz.
Qed.

(* C1d·终形桥：|A_n0(u+s)−A_n0(u)−A_n0(s·inv(1+(u+s)u))| ≤ totbnd
   （tel 于 K:=N 闭合 + 端项 w_0=0/w_N=走廊像逐点恒等 + 五项归一） *)
Lemma abl9b2_gap_final : forall (rho u s : Q) (N n0 : nat),
  Qle 0 rho -> Qlt rho 1 ->
  (1 <= N)%nat ->
  Qle (Qabs u) rho -> Qle (Qabs (u + s)) rho ->
  Qle (Qabs s) (1 # 4) ->
  Qle (Qabs (s * Qinv (Z.of_nat N # 1))) ((1 # 2) * (1 - rho)) ->
  Qle (abl9b2_dwb rho (s * Qinv (Z.of_nat N # 1))) (1 # 3) ->
  Qle (Qabs (arctan_partial n0 (u + s) - arctan_partial n0 u
             - arctan_partial n0 (s * Qinv (1 + (u + s) * u))))
      (abl9b2_totbnd rho s N n0).
Proof.
  intros rho u s N n0 Hr0 Hr1 HN Hu Hus Hs Ht Hdwb.
  pose proof (abl9b2_tel rho u s N N n0 Hr0 Hr1 HN (Nat.le_refl N)
               Hu Hus Hs Ht Hdwb) as HT.
  assert (HzN : Qlt 0 (Z.of_nat N # 1)) by (unfold Qlt; simpl; lia).
  assert (Hnz : ~ (Z.of_nat N # 1 == 0))
    by (apply (abl9b2_nz_of_pos (Z.of_nat N # 1) HzN)).
  assert (HqsN : (u + qs N * (s * Qinv (Z.of_nat N # 1))) == (u + s)).
  { rewrite (abl9_qs_Z N). field. exact Hnz. }
  assert (HwN : ((u + qs N * (s * Qinv (Z.of_nat N # 1))) - u)
                * Qinv (1 + (u + qs N * (s * Qinv (Z.of_nat N # 1))) * u)
                == s * Qinv (1 + (u + s) * u)).
  { rewrite HqsN. ring. }
  assert (Hwf0 : abl9b2_wf u u == 0) by (unfold abl9b2_wf; ring).
  assert (Hz0 : arctan_partial n0 (abl9b2_wf u u) == 0).
  { apply (Qeq_trans (arctan_partial n0 (abl9b2_wf u u))
             (arctan_partial n0 0) 0).
    - apply (b5c_arctan_partial_wd n0 _ 0). exact Hwf0.
    - apply abl9b2_ap_zero. }
  assert (Habsplit : Qabs (s * Qinv (Z.of_nat N # 1))
                     == Qabs s * Qinv (Z.of_nat N # 1)).
  { rewrite Qabs_Qmult.
    rewrite (Qabs_pos (Qinv (Z.of_nat N # 1))
               (Qlt_le_weak 0 (Qinv (Z.of_nat N # 1))
                  (Qinv_lt_0_compat (Z.of_nat N # 1) HzN))).
    reflexivity. }
  (* Hgap：tel 的 gap 表达式 == 终形 gap 表达式（端点恒等改写） *)
  assert (Hgap : arctan_partial n0 (u + qs N * (s * Qinv (Z.of_nat N # 1)))
                 - arctan_partial n0 u
                 - (arctan_partial n0 (abl9b2_wf (u + qs N * (s * Qinv (Z.of_nat N # 1))) u)
                    - arctan_partial n0 (abl9b2_wf u u))
                 == arctan_partial n0 (u + s) - arctan_partial n0 u
                    - arctan_partial n0 (s * Qinv (1 + (u + s) * u))).
  { rewrite (b5c_arctan_partial_wd n0
               (u + qs N * (s * Qinv (Z.of_nat N # 1))) (u + s) HqsN).
    rewrite (b5c_arctan_partial_wd n0
               (abl9b2_wf (u + qs N * (s * Qinv (Z.of_nat N # 1))) u)
               (s * Qinv (1 + (u + s) * u)) HwN).
    rewrite Hz0. ring. }
  apply (abl9b2_qle_transfer_l
           (Qabs (arctan_partial n0 (u + s) - arctan_partial n0 u
                  - arctan_partial n0 (s * Qinv (1 + (u + s) * u))))
           (Qabs (arctan_partial n0 (u + qs N * (s * Qinv (Z.of_nat N # 1)))
                  - arctan_partial n0 u
                  - (arctan_partial n0 (abl9b2_wf (u + qs N * (s * Qinv (Z.of_nat N # 1))) u)
                     - arctan_partial n0 (abl9b2_wf u u))))
           (abl9b2_totbnd rho s N n0)).
  - apply abl9_Qabs_wd. exact (Qeq_sym _ _ Hgap).
  - apply (Qle_trans _
             (qs N * abl9b2_stepbnd rho (s * Qinv (Z.of_nat N # 1)) n0)
             (abl9b2_totbnd rho s N n0)).
    + exact HT.
    + apply qeq_imp_qle.
      rewrite (abl9_qs_Z N).
      unfold abl9b2_stepbnd, abl9b2_dwb, abl9b2_totbnd, abl9b2_k123.
      rewrite Habsplit.
      field.
      split.
      * assert (HDpos : Qlt 0 ((1 - rho) * (1 - rho)))
          by (apply (Qmult_lt_0_compat (1 - rho) (1 - rho));
              apply (proj1 (Qlt_minus_iff rho 1)); exact Hr1).
        intros Hz. apply (Qlt_not_le 0 ((1 - rho) * (1 - rho)) HDpos).
        rewrite Hz. apply Qle_refl.
      * exact Hnz.
Qed.

(* C1e·预算闭合：份额假设（多项式带 K123·s² ≤ eps·N/6 + 双衰减）下
   |gap| ≤ eps——totbnd 三份额拆分（eps/6·2 + eps/4·2 = eps） *)
Lemma abl9b2_gap_eps : forall (rho u s : Q) (eps : Q) (N n0 : nat),
  Qlt 0 eps -> Qle 0 rho -> Qlt rho 1 -> (1 <= N)%nat ->
  Qle (Qabs u) rho -> Qle (Qabs (u + s)) rho ->
  Qle (Qabs s) (1 # 4) ->
  Qle (Qabs (s * Qinv (Z.of_nat N # 1))) ((1 # 2) * (1 - rho)) ->
  Qle (abl9b2_dwb rho (s * Qinv (Z.of_nat N # 1))) (1 # 3) ->
  Qle (abl9b2_k123 rho * (Qabs s * Qabs s))
      ((1 # 6) * eps * (Z.of_nat N # 1)) ->
  Qle (q_pow rho (2 * Nat.succ n0)) eps ->
  Qle (q_pow (1 # 3) (2 * Nat.succ n0))
      ((1 # 2) * eps * ((1 - rho) * (1 - rho))) ->
  Qle (Qabs (arctan_partial n0 (u + s) - arctan_partial n0 u
             - arctan_partial n0 (s * Qinv (1 + (u + s) * u)))) eps.
Proof.
  intros rho u s eps N n0 Heps Hr0 Hr1 HN Hu Hus Hs Ht Hdwb Hpoly HT2 HT4.
  pose proof (abl9b2_gap_final rho u s N n0 Hr0 Hr1 HN Hu Hus Hs Ht Hdwb) as HG.
  assert (HzN : Qlt 0 (Z.of_nat N # 1)) by (unfold Qlt; simpl; lia).
  assert (Hq04 : Qle 0 (1 # 4)) by (unfold Qle; simpl; lia).
  assert (H1mr : Qlt 0 (1 - rho))
    by (apply (proj1 (Qlt_minus_iff rho 1)); exact Hr1).
  assert (HDpos : Qlt 0 ((1 - rho) * (1 - rho)))
    by (apply (Qmult_lt_0_compat (1 - rho) (1 - rho)); exact H1mr).
  assert (HinvD0 : Qle 0 (Qinv ((1 - rho) * (1 - rho))))
    by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HDpos).
  assert (Hq03 : Qle 0 (1 # 3)) by (unfold Qle; simpl; lia).
  assert (HW0 : Qle 0 (q_pow (1 # 3) (2 * Nat.succ n0)))
    by (apply q_pow_nonneg; apply (Qlt_le_weak 0 (1 # 3));
        unfold Qlt; simpl; lia).
  (* 份额一：多项式带（K123·s²·inv(N#1) ≤ eps/6） *)
  assert (Hshare1 : Qle (abl9b2_k123 rho * (Qabs s * Qabs s)
                          * Qinv (Z.of_nat N # 1))
                        ((1 # 6) * eps)).
  { exact (abl9b2_share (abl9b2_k123 rho * (Qabs s * Qabs s))
             ((1 # 6) * eps) (Z.of_nat N # 1) HzN Hpoly). }
  (* 份额二：|s|·ρ^{2Sn0} ≤ eps/4 *)
  assert (Hshare2 : Qle (Qabs s * q_pow rho (2 * Nat.succ n0))
                        ((1 # 4) * eps)).
  { apply (Qle_trans _ ((1 # 4) * q_pow rho (2 * Nat.succ n0)) _).
    - apply (Qmult_le_compat_r (Qabs s) (1 # 4)
               (q_pow rho (2 * Nat.succ n0)));
        [exact Hs | apply q_pow_nonneg; exact Hr0].
    - apply (b3_qmult_le_l (q_pow rho (2 * Nat.succ n0)) eps (1 # 4));
        [exact Hq04 | exact HT2]. }
  (* 份额三：2|s|·invD·(1/3)^{2Sn0} ≤ eps/4 *)
  assert (H2s : Qle (2 * Qabs s) (1 # 2)).
  { apply (Qle_trans _ (2 * (1 # 4)) _).
    - apply (b3_qmult_le_l (Qabs s) (1 # 4) 2);
        [unfold Qle; simpl; lia | exact Hs].
    - apply qeq_imp_qle. ring. }
  assert (Hshare3 : Qle (2 * Qabs s * Qinv ((1 - rho) * (1 - rho))
                          * q_pow (1 # 3) (2 * Nat.succ n0))
                        ((1 # 4) * eps)).
  { apply (Qle_trans _
             ((1 # 2) * Qinv ((1 - rho) * (1 - rho))
              * q_pow (1 # 3) (2 * Nat.succ n0)) _).
    - apply (Qle_trans _
               (Qinv ((1 - rho) * (1 - rho))
                * q_pow (1 # 3) (2 * Nat.succ n0) * (2 * Qabs s))
               ((1 # 2) * Qinv ((1 - rho) * (1 - rho))
                * q_pow (1 # 3) (2 * Nat.succ n0))).
      + apply (abl9b2_qle_transfer_l
                 (2 * Qabs s * Qinv ((1 - rho) * (1 - rho))
                  * q_pow (1 # 3) (2 * Nat.succ n0))
                 (Qinv ((1 - rho) * (1 - rho))
                  * q_pow (1 # 3) (2 * Nat.succ n0) * (2 * Qabs s))
                 (Qinv ((1 - rho) * (1 - rho))
                  * q_pow (1 # 3) (2 * Nat.succ n0) * (2 * Qabs s))).
        -- ring.
        -- apply Qle_refl.
      + apply (Qle_trans _
                 (Qinv ((1 - rho) * (1 - rho))
                  * q_pow (1 # 3) (2 * Nat.succ n0) * (1 # 2))
                 ((1 # 2) * Qinv ((1 - rho) * (1 - rho))
                  * q_pow (1 # 3) (2 * Nat.succ n0))).
        * apply (b3_qmult_le_l (2 * Qabs s) (1 # 2)
                   (Qinv ((1 - rho) * (1 - rho))
                    * q_pow (1 # 3) (2 * Nat.succ n0))).
          ++ apply (Qmult_le_0_compat (Qinv ((1 - rho) * (1 - rho)))
                      (q_pow (1 # 3) (2 * Nat.succ n0)));
             [exact HinvD0 | exact HW0].
          ++ exact H2s.
        * apply (abl9b2_qle_transfer_l
                   (Qinv ((1 - rho) * (1 - rho))
                    * q_pow (1 # 3) (2 * Nat.succ n0) * (1 # 2))
                   ((1 # 2) * Qinv ((1 - rho) * (1 - rho))
                    * q_pow (1 # 3) (2 * Nat.succ n0))
                   ((1 # 2) * Qinv ((1 - rho) * (1 - rho))
                    * q_pow (1 # 3) (2 * Nat.succ n0))).
          -- ring.
          -- apply Qle_refl.
    - apply (Qle_trans _
               ((1 # 2) * Qinv ((1 - rho) * (1 - rho))
                * ((1 # 2) * eps * ((1 - rho) * (1 - rho)))) _).
      + apply (b3_qmult_le_l (q_pow (1 # 3) (2 * Nat.succ n0))
                 ((1 # 2) * eps * ((1 - rho) * (1 - rho)))
                 ((1 # 2) * Qinv ((1 - rho) * (1 - rho)))).
        ++ apply (Qmult_le_0_compat (1 # 2)
                    (Qinv ((1 - rho) * (1 - rho))));
           [unfold Qle; simpl; lia | exact HinvD0].
        ++ exact HT4.
      + assert (Hq : ((1 # 2) * Qinv ((1 - rho) * (1 - rho)))
                       * ((1 # 2) * eps * ((1 - rho) * (1 - rho)))
                       == ((1 # 4) * eps)).
        { field. intros Hz. apply (Qlt_not_le 0 ((1 - rho) * (1 - rho))
                                    HDpos).
          rewrite Hz. apply Qle_refl. }
        apply qeq_imp_qle. exact Hq. }
  apply (Qle_trans _ ((2 # 3) * eps) eps).
  - apply (Qle_trans _
             (((1 # 6) * eps) + (((1 # 4) * eps) + ((1 # 4) * eps))) _).
    + apply (Qle_trans _ (abl9b2_totbnd rho s N n0) _).
      * exact HG.
      * apply (abl9b2_qle_transfer_l (abl9b2_totbnd rho s N n0)
                 ((abl9b2_k123 rho * (Qabs s * Qabs s)
                   * Qinv (Z.of_nat N # 1))
                  + (Qabs s * q_pow rho (2 * Nat.succ n0)
                     + (2 * Qabs s * Qinv ((1 - rho) * (1 - rho))
                        * q_pow (1 # 3) (2 * Nat.succ n0))))
                 (((1 # 6) * eps) + (((1 # 4) * eps) + ((1 # 4) * eps)))).
        -- unfold abl9b2_totbnd. ring.
        -- apply (Qplus_le_compat _ ((1 # 6) * eps) _
                    (((1 # 4) * eps) + ((1 # 4) * eps))).
           ++ exact Hshare1.
           ++ apply (Qplus_le_compat _ ((1 # 4) * eps) _ ((1 # 4) * eps)).
              ** exact Hshare2.
              ** exact Hshare3.
    + apply qeq_imp_qle. ring.
  - apply (Qle_trans _ (1 * eps) eps).
    + apply (Qmult_le_compat_r (2 # 3) 1 eps);
        [unfold Qle; simpl; lia | apply Qlt_le_weak; exact Heps].
    + apply qeq_imp_qle. ring.
Qed.

(* C1f·缩放内点逐点预算：Nc 三约束 + 双衰减假设下，单坐标 (u,x) 的
   gap ≤ eps/2（gap_eps 于 rho:=k、eps:=eps/2 的实例化闭合） *)
Lemma abl9b2_scaled_point_bnd : forall (k : Q) (Nc n0 : nat) (u x eps : Q),
  Qlt 0 eps -> Qlt 0 k -> Qlt k 1 -> (1 <= Nc)%nat ->
  Qle (Qabs x) (1 # 4) ->
  Qle (Qabs u) k -> Qle (Qabs (u + x)) k ->
  Qle ((1 # 2) * Qinv (1 - k)) (Z.of_nat Nc # 1) ->
  Qle ((3 # 2) * Qinv ((1 - k) * (1 - k))) (Z.of_nat Nc # 1) ->
  Qle (abl9b2_k123 k * ((1 # 4) * (1 # 4)))
      (((1 # 12) * eps) * (Z.of_nat Nc # 1)) ->
  Qle (q_pow k (2 * Nat.succ n0)) ((1 # 2) * eps) ->
  Qle (q_pow (1 # 3) (2 * Nat.succ n0))
      ((1 # 4) * eps * ((1 - k) * (1 - k))) ->
  Qle (Qabs (arctan_partial n0 (u + x) - arctan_partial n0 u
             - arctan_partial n0 (x * Qinv (1 + (u + x) * u))))
      ((1 # 2) * eps).
Proof.
  intros k Nc n0 u x eps Heps Hk0 Hk1 HNc Hx Hu Hux H12 H32 Hpoly HT2 HT4.
  assert (Hk0le : Qle 0 k) by (apply Qlt_le_weak; exact Hk0).
  assert (H1mk : Qlt 0 (1 - k))
    by (apply (proj1 (Qlt_minus_iff k 1)); exact Hk1).
  assert (HDk : Qlt 0 ((1 - k) * (1 - k)))
    by (apply (Qmult_lt_0_compat (1 - k) (1 - k)); exact H1mk).
  assert (Hinv1mk0 : Qle 0 (Qinv (1 - k)))
    by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact H1mk).
  assert (HinvDk0 : Qle 0 (Qinv ((1 - k) * (1 - k))))
    by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HDk).
  assert (HzNc : Qlt 0 (Z.of_nat Nc # 1)) by (unfold Qlt; simpl; lia).
  assert (HnzNc : ~ (Z.of_nat Nc # 1 == 0))
    by (apply (abl9b2_nz_of_pos (Z.of_nat Nc # 1) HzNc)).
  assert (HinvNc0 : Qle 0 (Qinv (Z.of_nat Nc # 1)))
    by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HzNc).
  assert (Hnz1mk : ~ (1 - k == 0)) by (apply (abl9b2_nz_of_pos (1 - k) H1mk)).
  assert (HnzDk : ~ ((1 - k) * (1 - k) == 0))
    by (apply (abl9b2_nz_of_pos ((1 - k) * (1 - k)) HDk)).
  (* 约束一：(1/2) ≤ Nc#1·(1−k)（H12 乘 (1−k) + inv 归一） *)
  assert (HQ1 : Qle ((1 # 2) * Qinv (1 - k) * (1 - k))
                    ((Z.of_nat Nc # 1) * (1 - k))).
  { apply (Qmult_le_compat_r ((1 # 2) * Qinv (1 - k)) ((Z.of_nat Nc # 1)) (1 - k)).
    - exact H12.
    - apply Qlt_le_weak. exact H1mk. }
  assert (HQ1e : ((1 # 2) * Qinv (1 - k) * (1 - k)) == (1 # 2)).
  { field. exact Hnz1mk. }
  assert (HQ2 : Qle (1 # 2) ((Z.of_nat Nc # 1) * (1 - k))).
  { apply (abl9b2_qle_transfer_l (1 # 2)
             ((1 # 2) * Qinv (1 - k) * (1 - k))
             ((Z.of_nat Nc # 1) * (1 - k))).
    - apply Qeq_sym. exact HQ1e.
    - exact HQ1. }
  assert (HQ3 : Qle (1 # 4) (((1 # 2) * (1 - k)) * (Z.of_nat Nc # 1))).
  { apply (Qle_trans _ ((1 # 2) * ((Z.of_nat Nc # 1) * (1 - k))) _).
    - apply (b3_qmult_le_l (1 # 2) ((Z.of_nat Nc # 1) * (1 - k)) (1 # 2)).
      + unfold Qle. simpl. lia.
      + exact HQ2.
    - apply (abl9b2_qle_transfer_l
               ((1 # 2) * ((Z.of_nat Nc # 1) * (1 - k)))
               (((1 # 2) * (1 - k)) * (Z.of_nat Nc # 1))
               (((1 # 2) * (1 - k)) * (Z.of_nat Nc # 1))).
      + ring.
      + apply Qle_refl. }
  (* 约束二：(3/2) ≤ Nc#1·Dk（H32 乘 Dk + inv 归一） *)
  assert (HQ4 : Qle ((3 # 2) * Qinv ((1 - k) * (1 - k)) * ((1 - k) * (1 - k)))
                    ((Z.of_nat Nc # 1) * ((1 - k) * (1 - k)))).
  { apply (Qmult_le_compat_r ((3 # 2) * Qinv ((1 - k) * (1 - k))) ((Z.of_nat Nc # 1)) ((1 - k) * (1 - k))).
    - exact H32.
    - apply Qlt_le_weak. exact HDk. }
  assert (HQ4e : ((3 # 2) * Qinv ((1 - k) * (1 - k)) * ((1 - k) * (1 - k)))
                 == (3 # 2)).
  { field. exact Hnz1mk. }
  assert (HQ5 : Qle (3 # 2) ((Z.of_nat Nc # 1) * ((1 - k) * (1 - k)))).
  { apply (abl9b2_qle_transfer_l (3 # 2)
             ((3 # 2) * Qinv ((1 - k) * (1 - k)) * ((1 - k) * (1 - k)))
             ((Z.of_nat Nc # 1) * ((1 - k) * (1 - k)))).
    - apply Qeq_sym. exact HQ4e.
    - exact HQ4. }
  (* gap_eps 实例化的三个 Nc 槽 *)
  assert (Hslot1 : forall x0 : Q, Qle (Qabs x0) (1 # 4) ->
    Qle (Qabs (x0 * Qinv (Z.of_nat Nc # 1))) ((1 # 2) * (1 - k))).
  { intros x0 Hx0.
    assert (Habsp : Qabs (x0 * Qinv (Z.of_nat Nc # 1))
                    == Qabs x0 * Qinv (Z.of_nat Nc # 1)).
    { rewrite Qabs_Qmult.
      rewrite (Qabs_pos (Qinv (Z.of_nat Nc # 1)) HinvNc0). reflexivity. }
    apply (abl9b2_qle_transfer_l
             (Qabs (x0 * Qinv (Z.of_nat Nc # 1)))
             (Qabs x0 * Qinv (Z.of_nat Nc # 1))
             ((1 # 2) * (1 - k))).
    - exact Habsp.
    - apply (Qle_trans _ ((1 # 4) * Qinv (Z.of_nat Nc # 1)) _).
      + apply (Qmult_le_compat_r (Qabs x0) (1 # 4)
                 (Qinv (Z.of_nat Nc # 1))); [exact Hx0 | exact HinvNc0].
      + exact (abl9b2_share (1 # 4) ((1 # 2) * (1 - k))
                 (Z.of_nat Nc # 1) HzNc HQ3). }
  assert (Hslot2 : forall x0 : Q, Qle (Qabs x0) (1 # 4) ->
    Qle (abl9b2_dwb k (x0 * Qinv (Z.of_nat Nc # 1))) (1 # 3)).
  { intros x0 Hx0.
    assert (Habsp : Qabs (x0 * Qinv (Z.of_nat Nc # 1))
                    == Qabs x0 * Qinv (Z.of_nat Nc # 1)).
    { rewrite Qabs_Qmult.
      rewrite (Qabs_pos (Qinv (Z.of_nat Nc # 1)) HinvNc0). reflexivity. }
    assert (Hx0r : Qle (Qabs x0 * Qinv (Z.of_nat Nc # 1))
                       ((1 # 4) * Qinv (Z.of_nat Nc # 1))).
    { apply (Qmult_le_compat_r (Qabs x0) (1 # 4) (Qinv (Z.of_nat Nc # 1)));
        [exact Hx0 | exact HinvNc0]. }
    assert (H2t : Qle (2 * Qabs (x0 * Qinv (Z.of_nat Nc # 1)))
                       ((1 # 2) * Qinv (Z.of_nat Nc # 1))).
    { apply (Qle_trans _ (2 * (Qabs x0 * Qinv (Z.of_nat Nc # 1))) _).
      - apply (abl9b2_qle_transfer_l
                 (2 * Qabs (x0 * Qinv (Z.of_nat Nc # 1)))
                 (2 * (Qabs x0 * Qinv (Z.of_nat Nc # 1)))
                 (2 * (Qabs x0 * Qinv (Z.of_nat Nc # 1)))).
        + assert (H2ab : (2 * Qabs (x0 * Qinv (Z.of_nat Nc # 1))
                          == 2 * (Qabs x0 * Qinv (Z.of_nat Nc # 1)))%Q).
          { rewrite Habsp. reflexivity. }
          exact H2ab.
        + apply Qle_refl.
      - apply (Qle_trans _ (2 * ((1 # 4) * Qinv (Z.of_nat Nc # 1))) _).
        + apply (b3_qmult_le_l (Qabs x0 * Qinv (Z.of_nat Nc # 1))
                   ((1 # 4) * Qinv (Z.of_nat Nc # 1)) 2).
          * unfold Qle. simpl. lia.
          * exact Hx0r.
        + apply qeq_imp_qle. ring. }
    unfold abl9b2_dwb.
    apply (Qle_trans _ ((1 # 2) * Qinv (Z.of_nat Nc # 1)
                          * Qinv ((1 - k) * (1 - k)))
                       (1 # 3)).
      + apply (Qmult_le_compat_r (2 * Qabs (x0 * Qinv (Z.of_nat Nc # 1)))
                 ((1 # 2) * Qinv (Z.of_nat Nc # 1))
                 (Qinv ((1 - k) * (1 - k)))).
        * exact H2t.
        * exact HinvDk0.
      + apply (Qle_trans _
                 (((1 # 3) * Qinv (Z.of_nat Nc # 1)
                   * Qinv ((1 - k) * (1 - k)))
                  * (3 # 2))
                 (1 # 3)).
        * assert (Hf3 : ((1 # 2) * Qinv (Z.of_nat Nc # 1)
                          * Qinv ((1 - k) * (1 - k)))
                         == (((1 # 3) * Qinv (Z.of_nat Nc # 1)
                              * Qinv ((1 - k) * (1 - k)))
                             * (3 # 2))).
          { field. split; [exact Hnz1mk | exact HnzNc]. }
          apply qeq_imp_qle. exact Hf3.
        * apply (Qle_trans _
                   (((1 # 3) * Qinv (Z.of_nat Nc # 1)
                     * Qinv ((1 - k) * (1 - k)))
                    * ((Z.of_nat Nc # 1) * ((1 - k) * (1 - k))))
                   (1 # 3)).
          -- apply (b3_qmult_le_l (3 # 2)
                       ((Z.of_nat Nc # 1) * ((1 - k) * (1 - k)))
                       ((1 # 3) * Qinv (Z.of_nat Nc # 1)
                        * Qinv ((1 - k) * (1 - k)))).
              ++ apply (Qmult_le_0_compat
                          ((1 # 3) * Qinv (Z.of_nat Nc # 1))
                          (Qinv ((1 - k) * (1 - k)))).
                 ** apply (Qmult_le_0_compat (1 # 3)
                             (Qinv (Z.of_nat Nc # 1)));
                    [unfold Qle; simpl; lia | exact HinvNc0].
                 ** exact HinvDk0.
             ++ exact HQ5.
          -- assert (Hf4 : (((1 # 3) * Qinv (Z.of_nat Nc # 1)
                              * Qinv ((1 - k) * (1 - k)))
                             * ((Z.of_nat Nc # 1) * ((1 - k) * (1 - k))))
                            == (1 # 3)).
              { field. split; [exact Hnz1mk | exact HnzNc]. }
             apply qeq_imp_qle. exact Hf4. }
  assert (Hb2 : Qlt 0 ((1 # 2) * (1 + k))).
  { apply (Qmult_lt_0_compat (1 # 2) (1 + k)).
    - unfold Qlt. simpl. lia.
    - apply (Qlt_le_trans 0 1 (1 + k)).
      + unfold Qlt. simpl. lia.
      + apply (abl9b2_qle_transfer_l 1 (1 + 0) (1 + k)).
        * ring.
        * apply (Qplus_le_compat 1 1 0 k); [apply Qle_refl | exact Hk0le]. }
  assert (Hc2 : Qlt ((1 # 2) * (1 + k)) 1).
  { apply (abl9_Qlt_transfer_r ((1 # 2) * (1 + k)) ((1 # 2) * (1 + 1)) 1).
    - ring.
    - apply (abl9_Qlt_transfer_l ((1 + k) * (1 # 2)) ((1 # 2) * (1 + k))
               ((1 # 2) * (1 + 1))).
      + ring.
      + apply (abl9_Qlt_transfer_r ((1 + k) * (1 # 2)) ((1 + 1) * (1 # 2))
                 ((1 # 2) * (1 + 1))).
        * ring.
        * apply (Qmult_lt_compat_r (1 + k) (1 + 1) (1 # 2)).
           -- unfold Qlt. simpl. lia.
           -- apply (proj2 (Qplus_lt_r k 1 1)). exact Hk1. }
  assert (Hk123_0 : Qle 0 (abl9b2_k123 k)).
  { unfold abl9b2_k123.
    apply (Qplus_le_compat 0
             (b3rr_C2 ((1 # 2) * (1 + k)) + Qinv (1 - k)) 0
             (4 * b3rr_C2 ((1 # 2) * (1 + (1 # 3)))
              * Qinv ((1 - k) * (1 - k)) * Qinv ((1 - k) * (1 - k)))).
    - apply (Qplus_le_compat 0 (b3rr_C2 ((1 # 2) * (1 + k))) 0
               (Qinv (1 - k))).
      + apply b3rr_C2_0.
        * apply Qlt_le_weak. exact Hb2.
        * exact Hc2.
      + apply Qlt_le_weak. apply Qinv_lt_0_compat. exact H1mk.
    - apply (Qmult_le_0_compat
                (4 * b3rr_C2 ((1 # 2) * (1 + (1 # 3)))
                 * Qinv ((1 - k) * (1 - k)))
                (Qinv ((1 - k) * (1 - k)))).
      + apply (Qmult_le_0_compat
                  (4 * b3rr_C2 ((1 # 2) * (1 + (1 # 3))))
                  (Qinv ((1 - k) * (1 - k)))).
        * apply (Qmult_le_0_compat 4 (b3rr_C2 ((1 # 2) * (1 + (1 # 3))))).
          -- unfold Qle. simpl. lia.
          -- apply b3rr_C2_0.
             ** unfold Qle. simpl. lia.
             ** unfold Qlt. simpl. lia.
        * exact HinvDk0.
      + exact HinvDk0. }
  assert (Hslot3 : Qle (abl9b2_k123 k * (Qabs x * Qabs x))
                       (((1 # 6) * ((1 # 2) * eps)) * (Z.of_nat Nc # 1))).
  { apply (Qle_trans _ (abl9b2_k123 k * ((1 # 4) * (1 # 4))) _).
    - apply (Qmult_le_compat_nonneg (abl9b2_k123 k) (abl9b2_k123 k)
               (Qabs x * Qabs x) ((1 # 4) * (1 # 4))).
      + split; [exact Hk123_0 | apply Qle_refl].
      + split.
        * apply (Qmult_le_0_compat (Qabs x) (Qabs x));
            [apply Qabs_nonneg | apply Qabs_nonneg].
        * apply (Qmult_le_compat_nonneg (Qabs x) (1 # 4) (Qabs x) (1 # 4)).
          ++ split; [apply Qabs_nonneg | exact Hx].
          ++ split; [apply Qabs_nonneg | exact Hx].
    - apply (Qle_trans _ (((1 # 12) * eps) * (Z.of_nat Nc # 1)) _).
      + exact Hpoly.
      + apply qeq_imp_qle. ring. }
  assert (Ht4t : (q_pow (1 # 3) (2 * Nat.succ n0)
                  <= ((1 # 2) * ((1 # 2) * eps)) * ((1 - k) * (1 - k)))%Q).
  { apply (Qle_trans _ ((1 # 4) * eps * ((1 - k) * (1 - k))) _).
    - exact HT4.
    - apply qeq_imp_qle. ring. }
  assert (Hhep : Qlt 0 ((1 # 2) * eps)).
  { apply (Qmult_lt_0_compat (1 # 2) eps).
    - unfold Qlt. simpl. lia.
    - exact Heps. }
  exact (abl9b2_gap_eps k u x ((1 # 2) * eps) Nc n0
           Hhep
           Hk0le Hk1 HNc Hu Hux
           Hx
           (Hslot1 x Hx)
           (Hslot2 x Hx)
           Hslot3
           HT2
           Ht4t).
Qed.

(* C2·缩放对 gap 一致收敛证书（§B skel 的层2 闭合证书前件槽形）：
   内点走廊+逐点预算在坐标 n 逐点实例化——n ≥ N0 后 |gap_pt n| < eps *)
Lemma abl9b2_scaled_gap_conv : forall (y hh : Real) (k : Q) (N4 : nat)
  (Hy : forall n : nat, QleT' (Qabs (projT1 y n)) 1)
  (Hh4 : real_lt (real_abs hh) (real_const (1 # 4)))
  (Hyh : forall n : nat, QleT' (Qabs (projT1 (real_plus y hh) n)) 1)
  (Hk0 : Qlt 0 k) (Hk1 : Qlt k 1)
  (Hky : forall n : nat, Qle (Qabs (projT1 y n)) k)
  (Hkyh : forall n : nat, Qle (Qabs (projT1 y n + projT1 hh n)) k),
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QltT (Qabs (abl9_atan_diff_gap_pt y hh Hy Hh4 Hyh n)) eps).
Proof.
  intros y hh k N4 Hy Hh4 Hyh Hk0 Hk1 Hky Hkyh eps Heps.
  assert (Hepsq : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hhep : Qlt 0 ((1 # 2) * eps)).
  { apply (Qmult_lt_0_compat (1 # 2) eps).
    - unfold Qlt. simpl. lia.
    - exact Hepsq. }
  destruct (abl9b_h_abs_tail hh Hh4) as [N4' HN4'].
  assert (HN4le : forall n : nat, NatLe N4' n ->
    Qle (Qabs (projT1 hh n)) (1 # 4)).
  { intros n Hn. apply Qlt_le_weak. exact (HN4' n Hn). }
  assert (Hk0le : Qle 0 k) by (apply Qlt_le_weak; exact Hk0).
  assert (H1mk : Qlt 0 (1 - k))
    by (apply (proj1 (Qlt_minus_iff k 1)); exact Hk1).
  assert (HDk : Qlt 0 ((1 - k) * (1 - k)))
    by (apply (Qmult_lt_0_compat (1 - k) (1 - k)); exact H1mk).
  assert (Hnz1mk : ~ (1 - k == 0)) by (apply (abl9b2_nz_of_pos (1 - k) H1mk)).
  assert (HnzDk : ~ ((1 - k) * (1 - k) == 0))
    by (apply (abl9b2_nz_of_pos ((1 - k) * (1 - k)) HDk)).
  assert (Hinv1mk0 : Qle 0 (Qinv (1 - k)))
    by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact H1mk).
  assert (HinvDk0 : Qle 0 (Qinv ((1 - k) * (1 - k))))
    by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HDk).
  assert (Hk123_0 : Qle 0 (abl9b2_k123 k)).
  { assert (Hb2 : Qlt 0 ((1 # 2) * (1 + k))).
    { apply (Qmult_lt_0_compat (1 # 2) (1 + k)).
      - unfold Qlt. simpl. lia.
      - apply (Qlt_le_trans 0 1 (1 + k)).
        + unfold Qlt. simpl. lia.
        + exact (abl9b_q_self_plus_le 1 k Hk0le). }
    assert (Hc2 : Qlt ((1 # 2) * (1 + k)) 1).
    { apply (abl9_Qlt_transfer_r ((1 # 2) * (1 + k)) ((1 # 2) * (1 + 1)) 1).
      - ring.
      - apply (abl9_Qlt_transfer_l ((1 + k) * (1 # 2)) ((1 # 2) * (1 + k))
                 ((1 # 2) * (1 + 1))).
        * ring.
        * apply (abl9_Qlt_transfer_r ((1 + k) * (1 # 2))
                   ((1 + 1) * (1 # 2)) ((1 # 2) * (1 + 1))).
          -- ring.
          -- apply (Qmult_lt_compat_r (1 + k) (1 + 1) (1 # 2)).
             ++ unfold Qlt. simpl. lia.
              ++ apply (proj2 (Qplus_lt_r k 1 1)). exact Hk1. }
    unfold abl9b2_k123.
    apply (Qplus_le_compat 0
             (b3rr_C2 ((1 # 2) * (1 + k)) + Qinv (1 - k)) 0
             (4 * b3rr_C2 ((1 # 2) * (1 + (1 # 3)))
              * Qinv ((1 - k) * (1 - k)) * Qinv ((1 - k) * (1 - k)))).
    - apply (Qplus_le_compat 0 (b3rr_C2 ((1 # 2) * (1 + k))) 0
               (Qinv (1 - k))).
      + apply b3rr_C2_0.
        * apply Qlt_le_weak. exact Hb2.
        * exact Hc2.
      + apply Qlt_le_weak. apply Qinv_lt_0_compat. exact H1mk.
    - apply (Qmult_le_0_compat
                (4 * b3rr_C2 ((1 # 2) * (1 + (1 # 3)))
                 * Qinv ((1 - k) * (1 - k)))
                (Qinv ((1 - k) * (1 - k)))).
      + apply (Qmult_le_0_compat
                  (4 * b3rr_C2 ((1 # 2) * (1 + (1 # 3))))
                  (Qinv ((1 - k) * (1 - k)))).
        * apply (Qmult_le_0_compat 4 (b3rr_C2 ((1 # 2) * (1 + (1 # 3))))).
          -- unfold Qle. simpl. lia.
          -- apply b3rr_C2_0.
             ** unfold Qle. simpl. lia.
             ** unfold Qlt. simpl. lia.
        * exact HinvDk0.
      + exact HinvDk0. }
  (* Nc 见证：Qarchimedean 于正请求 R := 1 + (1/2)·inv(1−k)
     + (3/2)·invDk + (3/8)·k123·inv(eps/2) *)
  assert (HRpos : Qlt 0 (1 + (1 # 2) * Qinv (1 - k)
                          + (3 # 2) * Qinv ((1 - k) * (1 - k))
                          + (3 # 8) * abl9b2_k123 k * Qinv ((1 # 2) * eps))).
  { assert (Hcomp1 : Qle 0 ((1 # 2) * Qinv (1 - k))).
    { apply (Qmult_le_0_compat (1 # 2) (Qinv (1 - k)));
        [unfold Qle; simpl; lia | exact Hinv1mk0]. }
    assert (Hcomp2 : Qle 0 ((3 # 2) * Qinv ((1 - k) * (1 - k)))).
    { apply (Qmult_le_0_compat (3 # 2) (Qinv ((1 - k) * (1 - k))));
        [unfold Qle; simpl; lia | exact HinvDk0]. }
    assert (Hinvhep0 : Qle 0 (Qinv ((1 # 2) * eps))).
    { apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hhep. }
    assert (Hcomp3 : Qle 0 ((3 # 8) * abl9b2_k123 k * Qinv ((1 # 2) * eps))).
    { apply (Qmult_le_0_compat ((3 # 8) * abl9b2_k123 k)
               (Qinv ((1 # 2) * eps))).
      - apply (Qmult_le_0_compat (3 # 8) (abl9b2_k123 k));
          [unfold Qle; simpl; lia | exact Hk123_0].
      - exact Hinvhep0. }
    apply (Qlt_le_trans 0 1
             (1 + (1 # 2) * Qinv (1 - k)
              + (3 # 2) * Qinv ((1 - k) * (1 - k))
              + (3 # 8) * abl9b2_k123 k * Qinv ((1 # 2) * eps))).
    - unfold Qlt. simpl. lia.
    - apply (abl9b2_qle_transfer_l 1 (1 + 0)
               (1 + (1 # 2) * Qinv (1 - k)
                + (3 # 2) * Qinv ((1 - k) * (1 - k))
                + (3 # 8) * abl9b2_k123 k * Qinv ((1 # 2) * eps))).
      + ring.
      + apply (Qplus_le_compat 1
                 ((1 + (1 # 2) * Qinv (1 - k))
                  + (3 # 2) * Qinv ((1 - k) * (1 - k)))
                 0 ((3 # 8) * abl9b2_k123 k * Qinv ((1 # 2) * eps))).
        * apply (Qplus_le_compat 1
                   (1 + (1 # 2) * Qinv (1 - k)) 0
                   ((3 # 2) * Qinv ((1 - k) * (1 - k)))).
          -- apply (Qplus_le_compat 1 1 0 ((1 # 2) * Qinv (1 - k))).
             ++ apply Qle_refl.
             ++ exact Hcomp1.
          -- exact Hcomp2.
        * exact Hcomp3. }
  destruct (Qarchimedean (1 + (1 # 2) * Qinv (1 - k)
                           + (3 # 2) * Qinv ((1 - k) * (1 - k))
                           + (3 # 8) * abl9b2_k123 k
                           * Qinv ((1 # 2) * eps))) as [p Hp].
  assert (HNcp : (Z.pos p # 1) == (Z.of_nat (Pos.to_nat p) # 1)).
  { rewrite (positive_nat_Z p). reflexivity. }
  assert (HRle : Qle (1 + (1 # 2) * Qinv (1 - k)
                       + (3 # 2) * Qinv ((1 - k) * (1 - k))
                       + (3 # 8) * abl9b2_k123 k * Qinv ((1 # 2) * eps))
                     ((Z.of_nat (Pos.to_nat p) # 1))).
  { apply Qlt_le_weak. apply (abl9_Qlt_transfer_r _ _ _ HNcp Hp). }
  set (Nc := Pos.to_nat p) in *.
  assert (HNc1 : (1 <= Nc)%nat).
  { unfold Nc. pose proof (Pos2Nat.is_pos p). lia. }
  assert (HzNc : Qlt 0 ((Z.of_nat Nc) # 1)) by (unfold Qlt; simpl; lia).
  assert (HnzNc : ~ ((Z.of_nat Nc) # 1 == 0))
    by (apply (abl9b2_nz_of_pos ((Z.of_nat Nc) # 1) HzNc)).
  assert (HinvNc0 : Qle 0 (Qinv ((Z.of_nat Nc) # 1)))
    by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HzNc).
  (* 三条 Nc 槽（缩放点预算的前件） *)
  assert (HRsum : forall A0 B0 C0 : Q,
    Qle 0 B0 -> Qle 0 C0 -> Qle A0 (1 + A0 + B0 + C0)).
  { intros A0 B0 C0 HB0 HC0.
    assert (HBC : Qle 0 (B0 + C0)).
    { apply (Qplus_le_compat 0 B0 0 C0); assumption. }
    apply (Qle_trans _ (A0 + (1 + B0 + C0)) _).
    - apply (abl9b_q_self_plus_le A0 (1 + B0 + C0)).
      apply (Qle_trans _ (1 + B0) _).
      + apply (Qplus_le_compat 0 1 0 B0); [unfold Qle; simpl; lia | exact HB0].
      + exact (abl9b_q_self_plus_le (1 + B0) C0 HC0).
    - apply (abl9b2_qle_transfer_l (A0 + (1 + B0 + C0))
               (1 + A0 + B0 + C0) (1 + A0 + B0 + C0)).
      + ring.
      + apply Qle_refl. }
  assert (Hcomp1 : Qle 0 ((1 # 2) * Qinv (1 - k))).
  { apply (Qmult_le_0_compat (1 # 2) (Qinv (1 - k)));
      [unfold Qle; simpl; lia | exact Hinv1mk0]. }
  assert (Hcomp2 : Qle 0 ((3 # 2) * Qinv ((1 - k) * (1 - k)))).
  { apply (Qmult_le_0_compat (3 # 2) (Qinv ((1 - k) * (1 - k))));
      [unfold Qle; simpl; lia | exact HinvDk0]. }
  assert (Hcomp3 : Qle 0 ((3 # 8) * abl9b2_k123 k * Qinv ((1 # 2) * eps))).
  { apply (Qmult_le_0_compat ((3 # 8) * abl9b2_k123 k)
             (Qinv ((1 # 2) * eps))).
    - apply (Qmult_le_0_compat (3 # 8) (abl9b2_k123 k));
        [unfold Qle; simpl; lia | exact Hk123_0].
    - apply Qlt_le_weak. apply Qinv_lt_0_compat.
      apply (Qmult_lt_0_compat (1 # 2) eps).
      + unfold Qlt. simpl. lia.
      + exact Hepsq. }
  assert (H12' : Qle ((1 # 2) * Qinv (1 - k)) ((Z.of_nat Nc) # 1)).
  { apply (Qle_trans _ (1 + (1 # 2) * Qinv (1 - k)
                          + (3 # 2) * Qinv ((1 - k) * (1 - k))
                          + (3 # 8) * abl9b2_k123 k
                          * Qinv ((1 # 2) * eps)) _).
    - exact (HRsum ((1 # 2) * Qinv (1 - k))
               ((3 # 2) * Qinv ((1 - k) * (1 - k)))
               ((3 # 8) * abl9b2_k123 k * Qinv ((1 # 2) * eps))
                Hcomp2 Hcomp3).
    - exact HRle. }
  assert (H32' : Qle ((3 # 2) * Qinv ((1 - k) * (1 - k)))
                     ((Z.of_nat Nc) # 1)).
  { apply (Qle_trans _ (1 + (3 # 2) * Qinv ((1 - k) * (1 - k))
                          + (3 # 8) * abl9b2_k123 k
                          * Qinv ((1 # 2) * eps)
                          + (1 # 2) * Qinv (1 - k)) _).
    - exact (HRsum ((3 # 2) * Qinv ((1 - k) * (1 - k)))
               ((3 # 8) * abl9b2_k123 k * Qinv ((1 # 2) * eps))
                ((1 # 2) * Qinv (1 - k)) Hcomp3 Hcomp1).
    - apply (abl9b2_qle_transfer_l
               (1 + (3 # 2) * Qinv ((1 - k) * (1 - k))
                + (3 # 8) * abl9b2_k123 k * Qinv ((1 # 2) * eps)
                + (1 # 2) * Qinv (1 - k))
               (1 + (1 # 2) * Qinv (1 - k)
                + (3 # 2) * Qinv ((1 - k) * (1 - k))
                + (3 # 8) * abl9b2_k123 k * Qinv ((1 # 2) * eps))
               ((Z.of_nat Nc) # 1)).
      + ring.
      + exact HRle. }
  assert (Hcomp3le : Qle ((3 # 4) * abl9b2_k123 k * Qinv eps)
                          ((Z.of_nat Nc) # 1)).
  { assert (HC3 : Qle 0 ((3 # 4) * abl9b2_k123 k * Qinv eps)).
    { apply (Qmult_le_0_compat ((3 # 4) * abl9b2_k123 k) (Qinv eps)).
      - apply (Qmult_le_0_compat (3 # 4) (abl9b2_k123 k));
          [unfold Qle; simpl; lia | exact Hk123_0].
      - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hepsq. }
    assert (HRle3 : Qle (1 + (3 # 4) * abl9b2_k123 k * Qinv eps
                          + (1 # 2) * Qinv (1 - k)
                          + (3 # 2) * Qinv ((1 - k) * (1 - k)))
                        ((Z.of_nat Nc) # 1)).
    { apply (abl9b2_qle_transfer_l
               (1 + (3 # 4) * abl9b2_k123 k * Qinv eps
                + (1 # 2) * Qinv (1 - k)
                + (3 # 2) * Qinv ((1 - k) * (1 - k)))
               (1 + (1 # 2) * Qinv (1 - k)
                + (3 # 2) * Qinv ((1 - k) * (1 - k))
                + (3 # 8) * abl9b2_k123 k * Qinv ((1 # 2) * eps))
               ((Z.of_nat Nc) # 1)).
      - assert (Hfe : ((3 # 4) * abl9b2_k123 k * Qinv eps)
                      == ((3 # 8) * abl9b2_k123 k * Qinv ((1 # 2) * eps))).
        { field. apply (abl9b2_nz_of_pos eps Hepsq). }
        rewrite Hfe. ring.
      - exact HRle. }
    apply (Qle_trans _ (1 + (3 # 4) * abl9b2_k123 k * Qinv eps
                          + (1 # 2) * Qinv (1 - k)
                          + (3 # 2) * Qinv ((1 - k) * (1 - k)))
                       ((Z.of_nat Nc) # 1)).
    - exact (HRsum ((3 # 4) * abl9b2_k123 k * Qinv eps)
               ((1 # 2) * Qinv (1 - k))
                ((3 # 2) * Qinv ((1 - k) * (1 - k))) Hcomp1 Hcomp2).
    - exact HRle3. }
  assert (Hpoly' : Qle (abl9b2_k123 k * ((1 # 4) * (1 # 4)))
                       (((1 # 12) * eps) * ((Z.of_nat Nc) # 1))).
  { assert (Hstep1 : Qle ((3 # 4) * abl9b2_k123 k)
                       (((Z.of_nat Nc) # 1) * eps)).
    { apply (Qle_trans _ ((3 # 4) * abl9b2_k123 k * Qinv eps * eps) _).
      - apply (abl9b2_qle_transfer_l ((3 # 4) * abl9b2_k123 k)
                 ((3 # 4) * abl9b2_k123 k * Qinv eps * eps)
                 ((3 # 4) * abl9b2_k123 k * Qinv eps * eps)).
        { assert (Hf : ((3 # 4) * abl9b2_k123 k)
                       == ((3 # 4) * abl9b2_k123 k * Qinv eps * eps)).
          { field. apply (abl9b2_nz_of_pos eps Hepsq). }
          exact Hf. }
        { apply Qle_refl. }
      - apply (Qmult_le_compat_r ((3 # 4) * abl9b2_k123 k * Qinv eps)
                 ((Z.of_nat Nc) # 1) eps);
          [exact Hcomp3le | apply Qlt_le_weak; exact Hepsq]. }
    assert (Hstep2 : Qle (abl9b2_k123 k)
                       ((4 # 3) * (((Z.of_nat Nc) # 1) * eps))).
    { apply (abl9b2_qle_transfer_l (abl9b2_k123 k)
               ((4 # 3) * ((3 # 4) * abl9b2_k123 k))
               ((4 # 3) * (((Z.of_nat Nc) # 1) * eps))).
      - ring.
      - apply (b3_qmult_le_l ((3 # 4) * abl9b2_k123 k)
                 (((Z.of_nat Nc) # 1) * eps) (4 # 3)).
        + unfold Qle. simpl. lia.
        + exact Hstep1. }
    apply (Qle_trans _ ((1 # 16) * ((4 # 3) * (((Z.of_nat Nc) # 1) * eps))) _).
    + apply (abl9b2_qle_transfer_l
               (abl9b2_k123 k * ((1 # 4) * (1 # 4)))
               ((1 # 16) * abl9b2_k123 k)
               ((1 # 16) * ((4 # 3) * (((Z.of_nat Nc) # 1) * eps)))).
      * ring.
      * apply (b3_qmult_le_l (abl9b2_k123 k)
                 ((4 # 3) * (((Z.of_nat Nc) # 1) * eps)) (1 # 16)).
        - unfold Qle. simpl. lia.
        - exact Hstep2.
    + apply qeq_imp_qle. ring. }
  destruct (b3rr_qdecay k ((1 # 2) * eps) Hk0le Hk1 Hhep) as [Nq1 Hq1].
  assert (He4 : Qlt 0 ((1 # 4) * eps * ((1 - k) * (1 - k)))).
  { apply (Qmult_lt_0_compat ((1 # 4) * eps) ((1 - k) * (1 - k))).
    - apply (Qmult_lt_0_compat (1 # 4) eps).
      + unfold Qlt. simpl. lia.
      + exact Hepsq.
    - exact HDk. }
  assert (Hq03l : Qlt 0 (1 # 3)) by (unfold Qlt; simpl; lia).
  assert (Hq032 : Qlt (1 # 3) 1) by (unfold Qlt; simpl; lia).
  destruct (b3rr_qdecay (1 # 3) ((1 # 4) * eps * ((1 - k) * (1 - k)))
              (Qlt_le_weak 0 (1 # 3) Hq03l) Hq032 He4) as [Nq2 Hq2].
  destruct (real_inv_proj (real_plus real_one
             (real_mult (real_plus y hh) y))
             (abl9b_dom_pos y hh Hy Hh4)) as [Ninv HNinv].
  exists (N4' + Ninv + Pos.to_nat p + Nq1 + Nq2)%nat. intros n Hn.
  apply (NatLe_drop (N4' + Ninv + Pos.to_nat p + Nq1 + Nq2) n) in Hn.
  assert (Hn4 : (N4' <= n)%nat) by lia.
  assert (Hninv : (Ninv <= n)%nat) by lia.
  assert (Hnc : (Pos.to_nat p <= n)%nat) by lia.
  assert (Hn4L : NatLe N4' n) by (apply NatLe_lift; exact Hn4).
  assert (HNq1 : (Nq1 <= 2 * Nat.succ n)%nat).
  { destruct n as [| n'].
    - simpl. lia.
    - simpl. lia. }
  assert (HNq2 : (Nq2 <= 2 * Nat.succ n)%nat).
  { destruct n as [| n'].
    - simpl. lia.
    - simpl. lia. }
  (* 逐点域事实与 w 点值链 *)
  assert (Hx' : Qle (Qabs (projT1 hh n)) (1 # 4)) by (exact (HN4le n Hn4L)).
  assert (Hu' : Qle (Qabs (projT1 y n)) k) by (exact (Hky n)).
  assert (Hux' : Qle (Qabs (projT1 y n + projT1 hh n)) k).
  { exact (Hkyh n). }
  assert (HDproj : projT1 (real_plus real_one
                            (real_mult (real_plus y hh) y)) n
                   == 1 + ((projT1 y n + projT1 hh n) * projT1 y n)).
  { setoid_rewrite (real_plus_proj real_one
                      (real_mult (real_plus y hh) y) n).
    setoid_rewrite (real_mult_proj (real_plus y hh) y n).
    setoid_rewrite (real_plus_proj y hh n).
    cbn [projT1 real_one]. ring. }
  assert (HD1 : Qle (Qabs (projT1 y n)) 1).
  { apply (Qle_trans _ k 1 (Hky n) (Qlt_le_weak k 1 Hk1)). }
  assert (HD34 : Qle (3 # 4) (projT1 (real_plus real_one
                          (real_mult (real_plus y hh) y)) n)).
  { rewrite HDproj.
    apply abl9b_q_dom34.
    - exact HD1.
    - exact (HN4' n Hn4L). }
  assert (Hwv : projT1 (abl9b_w y hh (abl9b_dom_pos y hh Hy Hh4)) n
                == projT1 hh n
                   * Qinv (projT1 (real_plus real_one
                        (real_mult (real_plus y hh) y)) n)).
  { unfold abl9b_w.
    rewrite (real_mult_proj hh
               (real_inv_pos (real_plus real_one
                  (real_mult (real_plus y hh) y))
                 (abl9b_dom_pos y hh Hy Hh4)) n).
    apply Qmult_comp.
    - reflexivity.
    - exact (HNinv n Hninv). }
  assert (Hw13 : Qle (Qabs (projT1 (abl9b_w y hh
                              (abl9b_dom_pos y hh Hy Hh4)) n)) (1 # 3)).
  { assert (Hab : Qabs (projT1 (abl9b_w y hh
                          (abl9b_dom_pos y hh Hy Hh4)) n)
                  == Qabs (projT1 hh n
                           * Qinv (projT1 (real_plus real_one
                                (real_mult (real_plus y hh) y)) n))).
    { apply (Qabs_wd _ _). exact Hwv. }
    destruct (abl9b_q_wbnd (projT1 hh n)
                (projT1 (real_plus real_one
                   (real_mult (real_plus y hh) y)) n)
                HD34 (HN4' n Hn4L)) as [Hb43 Hb13].
    apply (abl9b2_qle_transfer_l
             (Qabs (projT1 (abl9b_w y hh
                      (abl9b_dom_pos y hh Hy Hh4)) n))
             (Qabs (projT1 hh n
                    * Qinv (projT1 (real_plus real_one
                         (real_mult (real_plus y hh) y)) n)))
             (1 # 3)).
    - exact Hab.
    - exact Hb13. }
  assert (Hwcid : projT1 (abl9b_wc y hh (abl9b_dom_pos y hh Hy Hh4)) n
                  == projT1 (abl9b_w y hh
                       (abl9b_dom_pos y hh Hy Hh4)) n).
  { exact (abl9b_wc_id_pt (abl9b_w y hh (abl9b_dom_pos y hh Hy Hh4)) n
             Hw13). }
  assert (HT2' : Qle (q_pow k (2 * Nat.succ n)%nat) ((1 # 2) * eps)).
  { exact (Hq1 (2 * Nat.succ n)%nat HNq1). }
  assert (HT4' : Qle (q_pow (1 # 3) (2 * Nat.succ n)%nat)
                       ((1 # 4) * eps * ((1 - k) * (1 - k)))).
  { exact (Hq2 (2 * Nat.succ n)%nat HNq2). }
  assert (Hpt : Qle (Qabs (arctan_partial n
                             (projT1 y n + projT1 hh n)
                             - arctan_partial n (projT1 y n)
                             - arctan_partial n (projT1 hh n
                                 * Qinv (1 + (projT1 y n + projT1 hh n)
                                          * projT1 y n))))
                    ((1 # 2) * eps)).
  { exact (abl9b2_scaled_point_bnd k (Pos.to_nat p) n
             (projT1 y n) (projT1 hh n) eps
             Hepsq Hk0 Hk1 HNc1 Hx' Hu' Hux'
             H12' H32' Hpoly' HT2' HT4'). }
  assert (Hgapeq : abl9_atan_diff_gap_pt y hh Hy Hh4 Hyh n
                   == (arctan_partial n (projT1 y n + projT1 hh n)
                       - arctan_partial n (projT1 y n)
                       - arctan_partial n (projT1 hh n
                           * Qinv (1 + (projT1 y n + projT1 hh n)
                                    * projT1 y n)))).
  { unfold abl9_atan_diff_gap_pt.
    rewrite (b5c_arctan_partial_wd n (projT1 (real_plus y hh) n)
               (projT1 y n + projT1 hh n) (real_plus_proj y hh n)).
    rewrite Hwcid.
    rewrite Hwv.
    rewrite HDproj.
    ring. }
  assert (Hhalf : Qlt ((1 # 2) * eps) eps).
  { apply (abl9_Qlt_transfer_r ((1 # 2) * eps) (1 * eps) eps).
    - ring.
    - apply (Qmult_lt_compat_r (1 # 2) 1 eps).
      + exact Hepsq.
      + unfold Qlt. simpl. lia. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (Qabs (abl9_atan_diff_gap_pt y hh Hy Hh4 Hyh n))
           ((1 # 2) * eps) eps).
  - exact (abl9b2_qle_transfer_l
             (Qabs (abl9_atan_diff_gap_pt y hh Hy Hh4 Hyh n))
             (Qabs (arctan_partial n (projT1 y n + projT1 hh n)
                    - arctan_partial n (projT1 y n)
                    - arctan_partial n (projT1 hh n
                        * Qinv (1 + (projT1 y n + projT1 hh n)
                                 * projT1 y n))))
             ((1 # 2) * eps)
             (abl9_Qabs_wd _ _ Hgapeq) Hpt).
  - exact Hhalf.
Qed.

(* ============================================================ *)
(* §D·内点版主件（S3 出口件）：案A 语句面下域加强（|x_n|≤ρ<1 与        *)
(*   端点 |x_n+h_n|≤ρ 点式界，ρ 参数化）时主公式 real_eq 全闭合——      *)
(*   装配=§B skel 证书前件位直接匹配 C2 缩放点界证书机                    *)
(*   （abl9b2_scaled_gap_conv 证书形与 skel 前件逐槽同构）。            *)
(* ============================================================ *)
Lemma abl9b2_inpoint_formula :
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (h : Real) (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
    (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  forall (rho : Q), Qlt 0 rho -> Qlt rho 1 ->
  (forall n : nat, Qle (Qabs (projT1 x n)) rho) ->
  (forall n : nat, Qle (Qabs (projT1 x n + projT1 h n)) rho) ->
  real_eq (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
             (real_opp (cauchy_real_arctan x Hx)))
          (cauchy_real_arctan (abl9b_wc x h (abl9b_dom_pos x h Hx Hh4))
             (abl9b_w_clamp_dom (abl9b_w x h (abl9b_dom_pos x h Hx Hh4)))).
Proof.
  intros x Hx h Hh4 Hxh rho Hr0 Hr1 Hxr Hxhr.
  apply (abl9_atan_diff_formula_skel x Hx h Hh4 Hxh).
  intros eps Heps.
  exact (abl9b2_scaled_gap_conv x h rho 0%nat Hx Hh4 Hxh Hr0 Hr1 Hxr Hxhr
           eps Heps).
Qed.

(* ============================================================ *)
(* §E0·缩放对 w 双证书形点位合同（案一装配桥）：缩放对的 w 序列         *)
(*   于 dom_pos 证书形（本件 §B/§D 语句面铁律位）与件54 sca_Hd 证书形   *)
(*   （ext_ws 家族）下，于双见证尾域（N4=h 尾界见证与 Nd=real_inv_proj  *)
(*   见证之最大者）逐点相等——real_inv_proj 双拆+D_n 投影链+ring 闭合，  *)
(*   早段证书形分歧不进门（尾域语义）。                                  *)
(* ============================================================ *)
Lemma abl9b2_ws_dom_eq : forall (m : nat) (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (Hh4s : real_lt (real_abs (abl9b_ext_xsc m h)) (real_const (1 # 4)))
  (N4 : nat)
  (HN4 : forall n : nat, NatLe N4 n -> Qlt (Qabs (projT1 h n)) (1 # 4)),
  sigT (fun Nd : nat => forall n : nat, (Nat.max N4 Nd <= n)%nat ->
    projT1 (abl9b_w (abl9b_ext_xsc m x) (abl9b_ext_xsc m h)
              (abl9b_dom_pos (abl9b_ext_xsc m x) (abl9b_ext_xsc m h)
                 (abl9b_ext_km_cwu m x Hx) Hh4s)) n
    == projT1 (abl9b_ext_ws m x h N4 HN4 Hx Hxh) n).
Proof.
  intros m x h Hx Hxh Hh4s N4 HN4.
  destruct (real_inv_proj (real_plus real_one
             (real_mult (real_plus (abl9b_ext_xsc m x) (abl9b_ext_xsc m h))
                        (abl9b_ext_xsc m x)))
             (abl9b_dom_pos (abl9b_ext_xsc m x) (abl9b_ext_xsc m h)
                (abl9b_ext_km_cwu m x Hx) Hh4s)) as [Nd HNd].
  exists Nd. intros n Hn.
  assert (Hn4 : NatLe N4 n) by (apply NatLe_lift; lia).
  assert (Hnd : (Nd <= n)%nat) by lia.
  (* 左肢：dom_pos 形 w_n == k_m·h_n · inv(D_n)（real_inv_proj 直拆） *)
  assert (HL : projT1 (abl9b_w (abl9b_ext_xsc m x) (abl9b_ext_xsc m h)
                          (abl9b_dom_pos (abl9b_ext_xsc m x) (abl9b_ext_xsc m h)
                             (abl9b_ext_km_cwu m x Hx) Hh4s)) n
               == abl9b_ext_km (Datatypes.S m) * projT1 h n
                  * Qinv (projT1 (real_plus real_one
                        (real_mult (real_plus (abl9b_ext_xsc m x)
                                     (abl9b_ext_xsc m h))
                                    (abl9b_ext_xsc m x))) n)).
  { unfold abl9b_w.
    rewrite (real_mult_proj (abl9b_ext_xsc m h)
               (real_inv_pos (real_plus real_one
                  (real_mult (real_plus (abl9b_ext_xsc m x)
                               (abl9b_ext_xsc m h))
                              (abl9b_ext_xsc m x)))
                 (abl9b_dom_pos (abl9b_ext_xsc m x) (abl9b_ext_xsc m h)
                    (abl9b_ext_km_cwu m x Hx) Hh4s)) n).
    rewrite (HNd n Hnd).
    rewrite (abl9b_ext_xsc_proj m h n).
    reflexivity. }
  (* D_n 投影值（件54 sca_Hd_pt HDp 同款投影链） *)
  assert (HDp : projT1 (real_plus real_one
                   (real_mult (real_plus (abl9b_ext_xsc m x)
                                (abl9b_ext_xsc m h))
                              (abl9b_ext_xsc m x))) n
                == 1 + (abl9b_ext_km (Datatypes.S m) * projT1 x n
                        + abl9b_ext_km (Datatypes.S m) * projT1 h n)
                       * (abl9b_ext_km (Datatypes.S m) * projT1 x n)).
  { rewrite (real_plus_proj real_one
              (real_mult (real_plus (abl9b_ext_xsc m x) (abl9b_ext_xsc m h))
                         (abl9b_ext_xsc m x)) n).
    rewrite (real_mult_proj (real_plus (abl9b_ext_xsc m x) (abl9b_ext_xsc m h))
                            (abl9b_ext_xsc m x) n).
    rewrite (real_plus_proj (abl9b_ext_xsc m x) (abl9b_ext_xsc m h) n).
    rewrite (abl9b_ext_xsc_proj m x n). rewrite (abl9b_ext_xsc_proj m h n).
    rewrite (b3r_one_proj n). cbn [projT1 real_one]. ring. }
  rewrite HL. rewrite HDp.
  (* 右肢：件54 ws_proj 直拆（ witness N4 均匀）；Qinv 内界 ring 恒等闭合 *)
  rewrite (abl9b_ext_ws_proj m x h N4 HN4 Hx Hxh n Hn4).
  assert (HD2 : 1 + (abl9b_ext_km (Datatypes.S m) * projT1 x n
                     + abl9b_ext_km (Datatypes.S m) * projT1 h n)
                * (abl9b_ext_km (Datatypes.S m) * projT1 x n)
               == 1 + (abl9b_ext_km (Datatypes.S m)
                       * (projT1 x n + projT1 h n))
                      * (abl9b_ext_km (Datatypes.S m) * projT1 x n)) by ring.
  rewrite HD2. reflexivity.
Qed.

(* ============================================================ *)
(* E0-附·抽象变量拆分微引理两件（ring 于复合原子形失效的隔离复现对策，  *)
(*   沿 §C arith_split 同款工法——§E1 主证明内四点/两点拆分恒等落点）    *)
Lemma abl9b2_quad_split : forall (l s w z : Q),
  l - z == - (s - l) + ((s - w) + (w - z)).
Proof. intros l s w z. ring. Qed.

Lemma abl9b2_opp_split : forall (a b : Q), a - b == - (b - a).
Proof. intros a b. ring. Qed.

(* §E1·正名终式 abl9_atan_diff_formula（S4 出口件）：闭域 |x|≤1 语句面  *)
(*   （案A 序契约面=件61 abl9b_rehearse2_merge_check_61 参数型逐字，    *)
(*   Hd 证明项逐字 abl9b_dom_pos x h Hx Hh4——R-T2 铁律），零前件全     *)
(*   闭合。路线=案一缩放三角合拢（X61 道一乙+道二坐标）：               *)
(*   |L−Z| ≤ |L−S| + |S−W| + |W−Z| 三肢——                              *)
(*   左肢=件54 lhs_conv（cv_to_tail 互译）；右肢=件59 rhs_close 前件槽  *)
(*   （案一抽象槽，X61 钉定）直接代入件54 ws_conv 真实证书（54→59 对接面 *)
(*   终裁形）；中肢=§D 内点主件@缩放对 (xsc m0 x, xsc m0 h)（k:=km     *)
(*   (S m0)∈(0,1) 点式界，req_to_tail 互译+§E0 桥收 dom_pos/sca_Hd 双  *)
(*   证书形 Representative 差）。m0:=max(ML,MR,1) 固定后中肢见证与 m   *)
(*   无关，三角链在 n 尾域纯三肢拼装（L:=主公式左侧，S:=缩放左侧，     *)
(*   W:=缩放对 clamp 右侧，Z:=主公式右侧）。                            *)
(* ============================================================ *)
Lemma abl9_atan_diff_formula :
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (h : Real) (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
    (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  real_eq (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
             (real_opp (cauchy_real_arctan x Hx)))
          (cauchy_real_arctan (abl9b_wc x h (abl9b_dom_pos x h Hx Hh4))
             (abl9b_w_clamp_dom (abl9b_w x h (abl9b_dom_pos x h Hx Hh4)))).
Proof.
  intros x Hx h Hh4 Hxh.
  destruct (abl9b_h_abs_tail h Hh4) as [N4 HN4].
  pose proof Hh4 as Hh4c. destruct Hh4c as [e4 [He40 [N4' HN4']]].
  intros eps Heps.
  assert (Ht : QltT 0 (eps / 3)) by (apply (qltT_div_pos eps 3 Heps qltT_0_3)).
  assert (Htq : Qlt 0 (eps / 3)) by (apply QltT_to_Qlt; exact Ht).
  (* —— 案一三肢取号（左=cv_to_tail；右=rhs_close 案一槽直接代入 ws_conv）——*)
  destruct (abl9b_ext_cv_to_tail (abl9b_ext_lhs_pt x h Hx Hxh)
              (fun m : nat => abl9b_ext_lhs_sm m x h Hx Hxh)
              (abl9b_ext_lhs_conv x h Hx Hxh) (eps / 3) Htq) as [ML [NL HML]].
  destruct (abl9b_rhs_close (fun m : nat => abl9b_ext_ws m x h N4 HN4 Hx Hxh)
              (abl9b_w x h (abl9b_dom_pos x h Hx Hh4))
              (abl9b_ext_ws_conv x h N4 HN4 Hx Hxh
                 (abl9b_dom_pos x h Hx Hh4)) (eps / 3) Ht) as [MR [NR HMR]].
  assert (HML0 : (ML <= Nat.max (Nat.max ML MR) 1)%nat) by lia.
  assert (HMR0 : (MR <= Nat.max (Nat.max ML MR) 1)%nat) by lia.
  assert (Hm01 : NatLe 1 (Nat.max (Nat.max ML MR) 1)) by (apply NatLe_lift; lia).
  (* —— k:=km(S m0)∈(0,1) 严格带（m0≥1 ⟹ S m0≥2 ⟹ 1/t∈(0,1/2]） —— *)
  assert (Ht0pos : Qlt 0
             ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q)
    by (unfold Qlt; simpl; lia).
  assert (Hbinvq : Qlt 0 (1 * Qinv
             ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q)).
  { apply (Qmult_lt_0_compat 1
             (Qinv ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q)).
    - unfold Qlt. simpl. lia.
    - apply Qinv_lt_0_compat. exact Ht0pos. }
  assert (Hb0le : Qle 0 (1 * Qinv
             ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q)).
  { assert (Hm01S : NatLe 1 (Datatypes.S (Nat.max (Nat.max ML MR) 1)))
      by (apply NatLe_lift; lia).
    unfold Qdiv. apply abl9b_ext_km_pos. exact Hm01S. }
  assert (Hbinv2 : Qle (1 * Qinv
             ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q) (1 # 2))
    by (apply (b5n_xinv_le 1
               ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q 2);
        [exact Ht0pos | unfold Qlt; simpl; lia | unfold Qle; simpl; lia]).
  assert (Hblt1 : Qlt (1 * Qinv
             ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q) 1).
  { apply (Qle_lt_trans (1 * Qinv
               ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q)
               (1 # 2) 1).
    - exact Hbinv2.
    - unfold Qlt. simpl. lia. }
  assert (Hk0 : Qlt 0 (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))))
    by (unfold abl9b_ext_km, Qdiv;
        exact (proj1 (Qlt_minus_iff
                 (1 * Qinv ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q) 1)
                 Hblt1)).
  assert (Hk0le : Qle 0 (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))))
    by (apply Qlt_le_weak; exact Hk0).
  assert (Hk1 : Qle (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))) 1).
  { unfold abl9b_ext_km, Qdiv.
    apply (proj2 (Qle_minus_iff (1 - 1 * Qinv
                  ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q) 1)).
    apply (Qle_trans 0
             (1 * Qinv ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q)
             (1 + - (1 - 1 * Qinv
                  ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q))).
    - exact Hb0le.
    - apply qeq_imp_qle. ring. }
  assert (Hk1s : Qlt (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))) 1).
  { unfold abl9b_ext_km, Qdiv.
    apply (proj2 (Qlt_minus_iff (1 - 1 * Qinv
                  ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q) 1)).
    apply (Qlt_le_trans 0
             (1 * Qinv ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q)
             (1 + - (1 - 1 * Qinv
                  ((Z.of_nat (Datatypes.S (Nat.max (Nat.max ML MR) 1)))%Z # 1)%Q))).
    - exact Hbinvq.
    - apply qeq_imp_qle. ring. }
  (* —— 缩放对 h 的 1/4 域证书（e4 slack 沿 k≤1 传递） —— *)
  assert (Hh4s : real_lt (real_abs (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h))
                   (real_const (1 # 4))).
  { unfold real_lt. exists e4. split.
    - exact He40.
    - exists (Nat.max N4' N4). intros n Hn.
      apply NatLe_drop in Hn.
      assert (Hn4' : NatLe N4' n) by (apply NatLe_lift; lia).
      assert (Hn4 : NatLe N4 n) by (apply NatLe_lift; lia).
      assert (Hehq : Qlt e4 ((1 # 4) - Qabs (projT1 h n))).
      { apply QltT_to_Qlt.
        apply (qltT_eq_compat_r ((1 # 4) - Qabs (projT1 h n))
                 (projT1 (real_const (1 # 4)) n - projT1 (real_abs h) n) e4).
        - rewrite (real_const_proj (1 # 4) n). rewrite (real_abs_proj h n).
          reflexivity.
        - exact (HN4' n Hn4'). }
      assert (Habsk : Qabs (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                              * projT1 h n)
                      == abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                         * Qabs (projT1 h n)).
      { rewrite Qabs_Qmult.
        rewrite (Qabs_pos (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))
                   Hk0le).
        reflexivity. }
      { apply (qltT_eq_compat_r
               (projT1 (real_const (1 # 4)) n
                - projT1 (real_abs (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)) n)
               ((1 # 4)
                - Qabs (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                        * projT1 h n))
               e4).
        - rewrite (real_const_proj (1 # 4) n). rewrite (real_abs_proj _ n).
          rewrite (abl9b_ext_xsc_proj (Nat.max (Nat.max ML MR) 1) h n).
          rewrite Habsk. reflexivity.
        - apply Qlt_to_QltT.
        apply (abl9_Qlt_transfer_r e4
                 (((1 # 4) - Qabs (projT1 h n))
                  + (Qabs (projT1 h n)
                     - abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                       * Qabs (projT1 h n)))
                 ((1 # 4)
                  - Qabs (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                          * projT1 h n))).
        + rewrite Habsk. ring.
        + apply (Qlt_le_trans e4 ((1 # 4) - Qabs (projT1 h n))
                   (((1 # 4) - Qabs (projT1 h n))
                    + (Qabs (projT1 h n)
                       - abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                         * Qabs (projT1 h n))) Hehq).
          apply (Qle_trans ((1 # 4) - Qabs (projT1 h n))
                   ((1 # 4) - Qabs (projT1 h n) + 0)
                   ((1 # 4) - Qabs (projT1 h n)
                    + (Qabs (projT1 h n)
                       - abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                         * Qabs (projT1 h n)))).
          * apply qeq_imp_qle. ring.
          * apply (Qplus_le_compat ((1 # 4) - Qabs (projT1 h n))
                     ((1 # 4) - Qabs (projT1 h n)) 0
                     (Qabs (projT1 h n)
                      - abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                        * Qabs (projT1 h n))).
            -- apply Qle_refl.
            -- apply (Qle_trans 0
                         ((1 - abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))
                          * Qabs (projT1 h n))
                         (Qabs (projT1 h n)
                          - abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                            * Qabs (projT1 h n))).
               ++ apply (Qmult_le_0_compat
                           (1 - abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))
                           (Qabs (projT1 h n))).
                  ** apply (proj1 (Qle_minus_iff
                                     (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))
                                     1)).
                     exact Hk1.
                  ** apply Qabs_nonneg.
               ++ apply qeq_imp_qle. ring. } }
  (* —— 内点主件@缩放对 前件（k 点式界三件） —— *)
  assert (Hky : forall n : nat,
            Qle (Qabs (projT1 (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x) n))
                (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))).
  { intros n. rewrite (abl9b_ext_xsc_proj (Nat.max (Nat.max ML MR) 1) x n).
    rewrite Qabs_Qmult.
    rewrite (Qabs_pos (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))
               Hk0le).
    apply (Qle_trans _
             (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)) * 1) _).
    - apply (b3_qmult_le_l (Qabs (projT1 x n)) 1
               (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))));
        [exact Hk0le | apply QleT'_to_Qle; apply (Hx n)].
    - apply qeq_imp_qle. ring. }
  assert (Hkyh : forall n : nat,
            Qle (Qabs (projT1 (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x) n
                       + projT1 (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h) n))
                (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))).
  { intros n.
    rewrite (abl9b_ext_xsc_proj (Nat.max (Nat.max ML MR) 1) x n).
    rewrite (abl9b_ext_xsc_proj (Nat.max (Nat.max ML MR) 1) h n).
    assert (Hsum : abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                   * projT1 x n
                   + abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                   * projT1 h n
                   == abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                      * (projT1 x n + projT1 h n)) by ring.
    rewrite Hsum.
    rewrite Qabs_Qmult.
    rewrite (Qabs_pos (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))
               Hk0le).
    apply (Qle_trans _
             (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)) * 1) _).
    - apply (b3_qmult_le_l (Qabs (projT1 x n + projT1 h n)) 1
               (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))).
      + exact Hk0le.
      + assert (Hxx : Qle (Qabs (projT1 (real_plus x h) n)) 1)
          by (apply QleT'_to_Qle; apply (Hxh n)).
        rewrite (real_plus_proj x h n) in Hxx. exact Hxx.
    - apply qeq_imp_qle. ring. }
  assert (Hxh_s : forall n : nat,
            QleT' (Qabs (projT1 (real_plus
                             (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                             (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)) n)) 1).
  { intros n. apply Qle_to_QleT'.
    rewrite (real_plus_proj (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
              (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h) n).
    rewrite (abl9b_ext_xsc_proj (Nat.max (Nat.max ML MR) 1) x n).
    rewrite (abl9b_ext_xsc_proj (Nat.max (Nat.max ML MR) 1) h n).
    assert (Hsum2 : abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                    * projT1 x n
                    + abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                    * projT1 h n
                    == abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                       * (projT1 x n + projT1 h n)) by ring.
    rewrite Hsum2.
    rewrite Qabs_Qmult.
    rewrite (Qabs_pos (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))
               Hk0le).
    apply (Qle_trans _
             (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))) 1).
    - apply (Qle_trans _
               (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)) * 1) _).
      + apply (b3_qmult_le_l (Qabs (projT1 x n + projT1 h n)) 1
                 (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))).
        * exact Hk0le.
        * assert (Hxx : Qle (Qabs (projT1 (real_plus x h) n)) 1)
            by (apply QleT'_to_Qle; apply (Hxh n)).
          rewrite (real_plus_proj x h n) in Hxx. exact Hxx.
      + apply qeq_imp_qle. ring.
    - exact Hk1. }
  (* —— 中肢：内点主件@缩放对 → real_eq → (M1,Nv) 尾形 —— *)
  assert (Hreq : real_eq
            (real_plus
               (cauchy_real_arctan
                  (real_plus (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                     (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)) Hxh_s)
               (real_opp
                  (cauchy_real_arctan (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                     (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx))))
            (cauchy_real_arctan
               (abl9b_wc (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                  (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                  (abl9b_dom_pos (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                     (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                     (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx) Hh4s))
               (abl9b_w_clamp_dom
                  (abl9b_w (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                     (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                     (abl9b_dom_pos (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                        (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                        (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx)
                        Hh4s))))).
  { apply (abl9b2_inpoint_formula
             (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
             (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx)
             (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h) Hh4s Hxh_s
             (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))
             Hk0 Hk1s Hky Hkyh). }
  destruct (abl9b2_ws_dom_eq (Nat.max (Nat.max ML MR) 1) x h Hx Hxh Hh4s N4 HN4)
    as [Nd Hwdeq].
  destruct (abl9b_ext_req_to_tail _ _ Hreq (eps / 3) Htq) as [MM [NM HMmid]].
  (* —— 尾见证展开 —— *)
  unfold real_eq. exists (Nat.max NL (Nat.max NM (Nat.max NR (Nat.max N4 Nd)))).
  intros n Hn.
  apply NatLe_drop in Hn.
  assert (HnNL : (NL <= n)%nat) by lia.
  assert (HnNM : (NM <= n)%nat) by lia.
  assert (HnNR : (NR <= n)%nat) by lia.
  assert (HnN4 : (N4 <= n)%nat) by lia.
  assert (HnNd : (Nd <= n)%nat) by lia.
  assert (Hnmax : (Nat.max N4 Nd <= n)%nat) by lia.
  (* —— 四个投影恒等（中肢传输原料；arctan_real_proj 定义性） —— *)
  assert (HSM : projT1 (abl9b_ext_lhs_sm (Nat.max (Nat.max ML MR) 1) x h Hx Hxh) n
                == arctan_partial n
                     (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                      * (projT1 x n + projT1 h n))
                   - arctan_partial n
                     (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                      * projT1 x n)).
  { unfold abl9b_ext_lhs_sm.
    rewrite (real_plus_proj
              (cauchy_real_arctan
                 (real_mult (real_const (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))))
                            (real_plus x h))
                 (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) (real_plus x h) Hxh))
              (real_opp
                 (cauchy_real_arctan
                    (real_mult (real_const (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))) x)
                    (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx))) n).
    rewrite (real_opp_proj
              (cauchy_real_arctan
                 (real_mult (real_const (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))) x)
                 (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx)) n).
    rewrite (arctan_real_proj
              (real_mult (real_const (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))))
                 (real_plus x h))
              (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) (real_plus x h) Hxh) n).
    rewrite (arctan_real_proj
              (real_mult (real_const (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))) x)
              (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx) n).
    rewrite (abl9b_ext_scx_proj (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1)))
              (real_plus x h) n).
    rewrite (abl9b_ext_scx_proj (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))) x n).
    rewrite (real_plus_proj x h n). reflexivity. }
  assert (HZM : projT1 (cauchy_real_arctan
                          (abl9b_rhs_clamp1
                             (abl9b_ext_ws (Nat.max (Nat.max ML MR) 1) x h N4 HN4 Hx Hxh))
                          (abl9b_rhs_dom1
                             (abl9b_ext_ws (Nat.max (Nat.max ML MR) 1) x h N4 HN4 Hx Hxh))) n
                == arctan_partial n
                     (Qmin (Qmax (projT1 (abl9b_ext_ws (Nat.max (Nat.max ML MR) 1) x h N4 HN4 Hx Hxh) n)
                            (-1)) 1)).
  { rewrite (arctan_real_proj
               (abl9b_rhs_clamp1
                  (abl9b_ext_ws (Nat.max (Nat.max ML MR) 1) x h N4 HN4 Hx Hxh))
               (abl9b_rhs_dom1
                  (abl9b_ext_ws (Nat.max (Nat.max ML MR) 1) x h N4 HN4 Hx Hxh)) n).
    apply (b5c_arctan_partial_wd n _ _
              (abl9b_rhs_clamp1_proj
                 (abl9b_ext_ws (Nat.max (Nat.max ML MR) 1) x h N4 HN4 Hx Hxh) n)). }
  assert (HRK : projT1 (cauchy_real_arctan
                          (abl9b_wc (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                             (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                             (abl9b_dom_pos (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                                (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                                (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx)
                                Hh4s))
                          (abl9b_w_clamp_dom
                             (abl9b_w (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                                (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                                (abl9b_dom_pos (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                                   (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                                   (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx)
                                   Hh4s)))) n
                == arctan_partial n
                     (Qmin (Qmax (projT1 (abl9b_ext_ws (Nat.max (Nat.max ML MR) 1) x h N4 HN4 Hx Hxh) n)
                            (-1)) 1)).
  { rewrite (arctan_real_proj
               (abl9b_wc (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                  (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                  (abl9b_dom_pos (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                     (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                     (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx) Hh4s))
               (abl9b_w_clamp_dom
                  (abl9b_w (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                     (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                     (abl9b_dom_pos (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                        (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                        (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx)
                        Hh4s))) n).
    rewrite (abl9b_rhs_wc_clamp1 (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
               (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
               (abl9b_dom_pos (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                  (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                  (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx) Hh4s) n).
    rewrite (abl9b_rhs_clamp1_proj
               (abl9b_w (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                  (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                  (abl9b_dom_pos (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                     (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                     (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx) Hh4s)) n).
    rewrite (Hwdeq n Hnmax). reflexivity. }
  assert (HLK : projT1 (real_plus
                          (cauchy_real_arctan
                             (real_plus (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                                (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h))
                             Hxh_s)
                          (real_opp
                             (cauchy_real_arctan
                                (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                                (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx)))) n
                == arctan_partial n
                     (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                      * projT1 x n
                      + abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                      * projT1 h n)
                   - arctan_partial n
                     (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                      * projT1 x n)).
  { rewrite (real_plus_proj
              (cauchy_real_arctan
                 (real_plus (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                    (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)) Hxh_s)
              (real_opp
                 (cauchy_real_arctan (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                    (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx))) n).
    rewrite (real_opp_proj
              (cauchy_real_arctan (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                 (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx)) n).
    rewrite (arctan_real_proj
              (real_plus (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                 (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)) Hxh_s n).
    rewrite (arctan_real_proj (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
              (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx) n).
    rewrite (real_plus_proj (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
              (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h) n).
    rewrite (abl9b_ext_xsc_proj (Nat.max (Nat.max ML MR) 1) x n).
    rewrite (abl9b_ext_xsc_proj (Nat.max (Nat.max ML MR) 1) h n).
    reflexivity. }
  (* —— 三肢原形直取（a=|S−L|、b=|S−W|、c=|W−Z|） —— *)
  pose proof (HML (Nat.max (Nat.max ML MR) 1) HML0 n HnNL) as HMLleg.
  pose proof (HMR (Nat.max (Nat.max ML MR) 1) HMR0 n
                (NatLe_lift NR n HnNR)) as HMRlegT.
  pose proof (QltT_to_Qlt _ _ HMRlegT) as HMRleg.
  assert (HmM : (MM <= MM)%nat) by (apply Nat.le_refl).
  pose proof (HMmid MM HmM n HnNM) as HMleg.
  (* —— b 肢传输：|LHS_k − RHS_k| ≤ t 沿投影恒等改写为 |S − W| ≤ t —— *)
  assert (Hble : Qle (Qabs (projT1 (abl9b_ext_lhs_sm (Nat.max (Nat.max ML MR) 1) x h Hx Hxh) n
                              - projT1 (cauchy_real_arctan
                                          (abl9b_rhs_clamp1
                                             (abl9b_ext_ws (Nat.max (Nat.max ML MR) 1) x h N4 HN4 Hx Hxh))
                                          (abl9b_rhs_dom1
                                             (abl9b_ext_ws (Nat.max (Nat.max ML MR) 1) x h N4 HN4 Hx Hxh))) n))
                     (eps / 3)).
  { assert (Harg : (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                    * (projT1 x n + projT1 h n))
                   == (abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                       * projT1 x n
                       + abl9b_ext_km (Datatypes.S (Nat.max (Nat.max ML MR) 1))
                       * projT1 h n)) by ring.
    apply (abl9b2_qle_transfer_l
             (Qabs (projT1 (abl9b_ext_lhs_sm (Nat.max (Nat.max ML MR) 1) x h Hx Hxh) n
                     - projT1 (cauchy_real_arctan
                                 (abl9b_rhs_clamp1
                                    (abl9b_ext_ws (Nat.max (Nat.max ML MR) 1) x h N4 HN4 Hx Hxh))
                                 (abl9b_rhs_dom1
                                    (abl9b_ext_ws (Nat.max (Nat.max ML MR) 1) x h N4 HN4 Hx Hxh))) n))
             (Qabs (projT1 (real_plus
                              (cauchy_real_arctan
                                 (real_plus (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                                    (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)) Hxh_s)
                              (real_opp
                                 (cauchy_real_arctan
                                    (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                                    (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx)))) n
                     - projT1 (cauchy_real_arctan
                                 (abl9b_wc (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                                    (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                                    (abl9b_dom_pos (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                                       (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                                       (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx)
                                       Hh4s))
                                 (abl9b_w_clamp_dom
                                    (abl9b_w (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                                       (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                                       (abl9b_dom_pos (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) x)
                                          (abl9b_ext_xsc (Nat.max (Nat.max ML MR) 1) h)
                                          (abl9b_ext_km_cwu (Nat.max (Nat.max ML MR) 1) x Hx)
                                          Hh4s)))) n))
             (eps / 3)).
    - apply abl9_Qabs_wd.
      rewrite HSM. rewrite HLK. rewrite HZM. rewrite HRK.
      rewrite (b5c_arctan_partial_wd n _ _ Harg). reflexivity.
    - exact HMleg. }
  (* —— 终局拼装：Hsplit2拆解+Qabs_triangle 直接匹配 + 严格数值闭合 ——  *)
  (* —— 四肢名折叠（短形装配） —— *)
  set (La := projT1 (real_plus (cauchy_real_arctan (real_plus x h) Hxh) (real_opp (cauchy_real_arctan x Hx))) n).
  set (Za := projT1 (cauchy_real_arctan (abl9b_wc x h (abl9b_dom_pos x h Hx Hh4)) (abl9b_w_clamp_dom (abl9b_w x h (abl9b_dom_pos x h Hx Hh4)))) n).
  set (Sa := projT1 (abl9b_ext_lhs_sm (Nat.max (Nat.max ML MR) 1) x h Hx Hxh) n).
  set (Wa := projT1 (cauchy_real_arctan (abl9b_rhs_clamp1 (abl9b_ext_ws (Nat.max (Nat.max ML MR) 1) x h N4 HN4 Hx Hxh)) (abl9b_rhs_dom1 (abl9b_ext_ws (Nat.max (Nat.max ML MR) 1) x h N4 HN4 Hx Hxh))) n).
  set (SL := Sa - La). set (SW := Sa - Wa). set (WZ := Wa - Za).
  pose proof (abl9b2_quad_split La Sa Wa Za) as Hsplitf.
  pose proof (Qabs_triangle (- SL) (SW + WZ)) as Htri1raw.
  assert (Hm1 : Qle (Qabs (- SL)) (eps / 3)).
  { apply (Qle_trans _ (Qabs SL) (eps / 3)).
    - apply qeq_imp_qle. apply Qabs_opp.
    - exact HMLleg. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (- SL) + Qabs (SW + WZ)) eps).
  + apply (abl9b2_qle_transfer_l (Qabs (La - Za))
             (Qabs (- SL + (SW + WZ)))
             (Qabs (- SL) + Qabs (SW + WZ))).
    * apply abl9_Qabs_wd. exact Hsplitf.
    * exact Htri1raw.
  + apply (Qle_lt_trans _ (eps / 3 + (eps / 3 + Qabs WZ)) eps).
    apply (Qplus_le_compat (Qabs (- SL)) (eps / 3) (Qabs (SW + WZ)) (eps / 3 + Qabs WZ)).
    * exact Hm1.
    * apply (Qle_trans _ (Qabs SW + Qabs WZ) (eps / 3 + Qabs WZ)).
      -- apply Qabs_triangle.
      -- apply (Qplus_le_compat (Qabs SW) (eps / 3) (Qabs WZ) (Qabs WZ)).
         ++ exact Hble.
         ++ apply Qle_refl.
    * apply (abl9_Qlt_transfer_l ((eps / 3 + eps / 3) + Qabs WZ)
                                  (eps / 3 + (eps / 3 + Qabs WZ))
                                  eps).
      -- ring.
      -- apply (abl9_Qlt_transfer_r ((eps / 3 + eps / 3) + Qabs WZ)
                                     (eps / 3 + (eps / 3 + eps / 3))
                                     eps).
         ++ apply atan_third_sum.
         ++ apply (abl9_Qlt_transfer_r ((eps / 3 + eps / 3) + Qabs WZ)
                    ((eps / 3 + eps / 3) + (eps / 3))
                    (eps / 3 + (eps / 3 + eps / 3))).
            ** ring.
            ** exact (proj2 (Qplus_lt_r (Qabs WZ) (eps / 3) (eps / 3 + eps / 3)) HMRleg).
Qed.
(* ============================================================ *)
(* 终验 · 承认面 + 契约面自检 + 提取检验                              *)
(*   对账三联：Lemma 名清单 29 = Qed 计数 29 = PA 语句 29，零差；       *)
(*   契约面自检=案A 序契约面（件61 abl9b_rehearse2_merge_check_61       *)
(*   参数型逐字）的名字直耗形——正装落池后一行终验位                    *)
(*   exact (abl9b_rehearse2_merge_check_61 abl9_atan_diff_formula)     *)
(*   于合流池执行（件61 在 RH2 池，本池不跨域 Require）。               *)
(* ============================================================ *)
Print Assumptions abl9b2_q_convex_rho.
Print Assumptions abl9b2_qs_Z.
Print Assumptions abl9b2_wnode_bnd.
Print Assumptions abl9b2_winc_bnd.
Print Assumptions abl9_atan_diff_formula_skel.
Print Assumptions abl9b2_qs_nonneg.
Print Assumptions abl9b2_uk_bnd.
Print Assumptions abl9b2_uk_delta.
Print Assumptions abl9b2_wk_bnd.
Print Assumptions abl9b2_nz_of_pos.
Print Assumptions abl9b2_qle_transfer_l.
Print Assumptions abl9b2_wf_wd.
Print Assumptions abl9b2_arith_split.
Print Assumptions abl9b2_step_chain.
Print Assumptions abl9b2_at_zero.
Print Assumptions abl9b2_ap_zero.
Print Assumptions abl9b2_share.
Print Assumptions abl9b2_tel.
Print Assumptions abl9b2_totbnd_eq.
Print Assumptions abl9b2_gap_final.
Print Assumptions abl9b2_gap_eps.
Print Assumptions abl9b2_scaled_point_bnd.
Print Assumptions abl9b2_scaled_gap_conv.
Print Assumptions abl9b2_inpoint_formula.
Print Assumptions abl9b2_ws_dom_eq.
Print Assumptions abl9b2_quad_split.
Print Assumptions abl9b2_opp_split.
Print Assumptions abl9_atan_diff_formula.

(* 契约面自检：正名直耗形（案A 序=x Hx 前置+Hd 逐字 abl9b_dom_pos） *)
Lemma abl9_atan_diff_formula_contract :
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (h : Real) (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
    (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  real_eq (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
             (real_opp (cauchy_real_arctan x Hx)))
          (cauchy_real_arctan (abl9b_wc x h (abl9b_dom_pos x h Hx Hh4))
             (abl9b_w_clamp_dom (abl9b_w x h (abl9b_dom_pos x h Hx Hh4)))).
Proof. exact abl9_atan_diff_formula. Qed.

Print Assumptions abl9_atan_diff_formula_contract.

(* 提取检验（判据=Obj.magic 计 0）：正名位为 witness 形（real_lt 前件   *)
(*   And 实例化触发 prod 实例化硬错——实测实录于编译日志，沿件54/59    *)
(*   前例豁免该位提取命令（fail-loud 登记），承认面判据=上 28+1 条 PA    *)
(*   全 Closed；提取安全位取 Q 顶件两件（零 witness 位，Obj.magic 计 0）: *)
Recursive Extraction abl9b2_tel.
Recursive Extraction abl9b2_gap_eps.
