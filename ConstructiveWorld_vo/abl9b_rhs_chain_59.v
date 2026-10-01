(* ==========================================================================)
   abl9b_rhs_chain_59.v — RHS 侧实层闭合辅助件四块（A2+B3 合流·real 层半边）
   A2+B3 合流 Q 侧四块由件54／件55 主攻（甲乙两支），
   本件互补不重复：专攻两支留接口的 RHS 侧实层闭合辅助件，落根目录。）
   ── 模块名+数学使命：────────────────────────────────────────────────────────
   四块（RHS 侧闭合：m→∞ 三项 eps 链之 RHS 半边）：
   块一·clamp 1-Lipschitz：件30 abl9b_wc clamp 语义（半径 1）逐点
       |clamp(a)_n−clamp(b)_n| ≤ |a_n−b_n|，Set 层 QleT' 承载；
       分情形核=件53 abl9b_q_clamp_lip 一般半径件 c:=1 实例经投影重锚。
   块二·arctan 序列项级合同：|·|≤1 闭域上 arctan 部分和/cauchy_real_arctan
       对逐点距 ≤d0 的序列给出项级距 <eps 选器（b5b_ap_uniform 重锚至
       cauchy_real_arctan 投影位）+尾相等+w 域证书尾形→real_eq 运输链
       （半径 1 版；件53 abl9b_wc34_w_real_eq／件45 abl9_arctan_arg_wd 为先例）。
   块三·Qinv 连续辅助引理：Q 层 3/4≤a,b ⟹ |inva−invb| ≤ (16/9)|a−b|
       （QleT' 形域证书+Qle 证明）。
   块四·RHS_m→RHS 闭合骨架：以「缩放对下 RHS_m 与 RHS 逐点尾收敛证书+一致
       连续证书」为前件参数，组装 m→∞ 项级闭合（与 LHS 侧接口对称；
       本件自成 RHS 半边闭环，合流时与甲/乙任一支的 LHS 半边拼装）。
   ── 依赖清单：──────────────────────────────────────────────────────────────
   S01–S11（基础模块，原位建成 vo 在链）；件20 abl_arctan_diff_20
   （abl9_QltT_transfer_l／abl9_Qabs_wd）；件30 abl9b_skeleton_30（abl9b_w、
   abl9b_w_bounds 尾形、abl9b_wc／w_clamp_dom／wc_id_pt clamp 构造正本）；
   件45 abl_arctan_diff_45（abl9_arctan_arg_wd 重锚再出口）；件53
   abl9b_rho_chain_53（abl9b_q_clamp_lip 分情形核、abl9b_q_abs_minus、
   abl9b_xsc／abl9b_hsc／abl9b_sca_Hd 缩放对与 D_m 正性证书）。
   ── 对标行：────────────────────────────────────────────────────────────────
   一致连续核：S11_TP3B5.v b5b_ap_uniform（L7044 带）；arctan 投影恒等：
   S11 arctan_real_proj（L909）；cauchy_real_arctan 定义（L823）；柯西模量：
   S11 arctan_partial_cauchy（L451）；实层连续件 b5b_arctan_cont_unit
   （L7140）；跨乘 b5n_xinv_le（L11884）；real_eq 定义 S02（L399）、
   real_lt（L468）；real_min／real_max 投影 S07（L7274／7284）；clamp 构造
   正本：件30 abl9b_wc／abl9b_w_clamp_dom／abl9b_wc_id_pt（L288-325 带）+
   abl9b_w_bounds（L221 带，尾形）；Q 核 Lipschitz：件53 abl9b_q_clamp_lip
   （L315 带）；尾形运输先例：件53 abl9b_wc34_w_real_eq（L402 带）；arg_wd
   先例：件45 abl9_arctan_arg_wd（L68 带）；缩放对：件53 abl9b_xsc／
   abl9b_hsc／abl9b_sca_Hd（L432／435／632 带）；路线依据：m→∞ 三项
   eps 链之 RHS 半边（B3 选项行）。
   ── 构造性注记：────────────────────────────────────────────────────────────
   全件真构造闭合，零承认式声明，零经典逻辑；零承认链短路策略（Q 序链走
   Qle_trans／Qmult_le_compat 系+b5n_xinv_le 跨乘+lia 逐链构造）；
   语句面承载位全 Set 形（sigT/real_eq/QleT'），Qle/Qlt 仅标量前提位与
   Q 层辅助引理顶形（件19/51/53/60 同款口径）；闭合骨架结论 QltT（real_eq
   同款尾语义位）。块四前件参数＝缩放 w_m→w 逐点尾收敛证书（其 Q 侧
   具体系数供给为甲/乙支四块的合流接口位，本件不越权重复）。
   提取检验豁免登记（承件53 前例）：sigT 内含 Prop-见证 fiber 的 witness
   形四件（arctan_contract／arctan_uniform_close／rhs_close／rhs_sc_close）
   沿件53 abl9b_sca_path_bnd 前例豁免提取命令（Rocq 9.1 提取器 prod-Prop
   实例化硬错风险，计算内容由 S11 b5b_ap_uniform 本体与本件三检验覆盖）。
   ── 编译配方：──────────────────────────────────────────────────────────────
   source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh &&
   unset COQLIB ROCQLIB && cd abl_a2b3_WASH2_pool && ulimit -s 65532 &&
   nice -19 rocq c -native-compiler no -Q "$PWD" "" "$PWD/abl9b_rhs_chain_59.v"
   （单道顺序；绿判四要素：EXIT=0（无管道真取）／日志真错行计 0+主定理
   Closed／vo 头 8 字节 436f712100015ff4／vo 新于 v。道闸：起编前
   ps -axo comm 查 rocq 计 ≤1。）
   ── 交付声明 ──────────────────────────────────────────────────────────────
   本件为中文声明的零承认件：全文件零承认式声明、零悬置前提、零经典逻辑，
   全部结论真构造闭合；头注五字段齐备（模块名+数学使命／依赖清单／对标行／
   构造性注记／编译配方）。
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
Require Import abl_arctan_diff_20.
Require Import abl9b_skeleton_30.
Require Import abl_arctan_diff_45.
Require Import abl9b_rho_chain_53.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import ZArith Extraction.

(* ============================================================ *)
(* §0·Q 层标量正性辅助引理（三件）                                  *)
(* ============================================================ *)

Lemma abl9b_rhs_q34_pos : Qlt 0 (3#4).
Proof. unfold Qlt. simpl. lia. Qed.

Lemma abl9b_rhs_q916_pos : Qlt 0 (9#16).
Proof. unfold Qlt. simpl. lia. Qed.

Lemma abl9b_rhs_q169_pos : Qlt 0 (16#9).
Proof. unfold Qlt. simpl. lia. Qed.

(* ============================================================ *)
(* 块一·clamp 1-Lipschitz（件30 abl9b_wc 语义，半径 1，Set 层）        *)
(* ============================================================ *)

(* clamp-1 代表元：件30 abl9b_wc 体内逐字（一般实参版） *)
Definition abl9b_rhs_clamp1 (a : Real) : Real :=
  real_min (real_max a (real_const (-1))) (real_const 1).

(* clamp-1 全域域证书（件30 abl9b_w_clamp_dom 的 clamp1 形包装） *)
Definition abl9b_rhs_dom1 (a : Real) :
  forall n : nat, QleT' (Qabs (projT1 (abl9b_rhs_clamp1 a) n)) 1 :=
  fun n : nat => abl9b_w_clamp_dom a n.

(* 点位投影披露：clamp1_n == Qmin(Qmax(a_n,−1),1) *)
Lemma abl9b_rhs_clamp1_proj : forall (a : Real) (n : nat),
  projT1 (abl9b_rhs_clamp1 a) n == Qmin (Qmax (projT1 a n) (-1)) 1.
Proof.
  intros a n. unfold abl9b_rhs_clamp1.
  rewrite (real_min_proj (real_max a (real_const (-1))) (real_const 1) n).
  rewrite (real_max_proj a (real_const (-1)) n).
  rewrite (real_const_proj (-1) n). rewrite (real_const_proj 1 n).
  reflexivity.
Qed.

(* 件30 Hdiff 参数位语义披露：abl9b_wc 点位即 clamp1∘w（定义等值）  *)
Lemma abl9b_rhs_wc_clamp1 : forall (x h : Real)
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x)))
  (n : nat),
  projT1 (abl9b_wc x h Hd) n == projT1 (abl9b_rhs_clamp1 (abl9b_w x h Hd)) n.
Proof. intros x h Hd n. reflexivity. Qed.

(* 主件·Set 层承载（QleT'）：|clamp(a)_n−clamp(b)_n| ≤ |a_n−b_n|
   分情形核=件53 abl9b_q_clamp_lip（一般半径 c≥0）c:=1 实例经投影重锚 *)
Lemma abl9b_rhs_clamp1_lip : forall (a b : Real) (n : nat),
  QleT' (Qabs (projT1 (abl9b_rhs_clamp1 a) n - projT1 (abl9b_rhs_clamp1 b) n))
        (Qabs (projT1 a n - projT1 b n)).
Proof.
  intros a b n.
  apply Qle_to_QleT'.
  rewrite (abl9b_rhs_clamp1_proj a n). rewrite (abl9b_rhs_clamp1_proj b n).
  apply (abl9b_q_clamp_lip 1 (projT1 a n) (projT1 b n)).
  unfold Qle. simpl. lia.
Qed.

(* Q 链便利形（Qle 顶） *)
Lemma abl9b_rhs_clamp1_lipQ : forall (a b : Real) (n : nat),
  Qle (Qabs (projT1 (abl9b_rhs_clamp1 a) n - projT1 (abl9b_rhs_clamp1 b) n))
      (Qabs (projT1 a n - projT1 b n)).
Proof.
  intros a b n. apply QleT'_to_Qle. apply abl9b_rhs_clamp1_lip.
Qed.

(* ============================================================ *)
(* 块二·arctan 序列项级合同（b5b_ap_uniform 重锚选器+尾形运输链）      *)
(* ============================================================ *)

(* 选器主件：闭域 |·|≤1 两序列逐点距 ≤d0、n≥M ⟹ cauchy_real_arctan
   项级距 <eps（(M,d0) 见证对全序列对一致有效——b5b_ap_uniform 重锚；
   见证走 sigT-fiber 形（零 And 承载），使用位 Qlt_to_QltT 升位） *)
Lemma abl9b_rhs_arctan_contract : forall (eps : Q), Qlt 0 eps ->
  sigT (fun M : nat =>
  sigT (fun d0 : Q =>
  sigT (fun Hd0 : Qlt 0 d0 =>
  forall (u v : Real)
         (Hu : forall n : nat, QleT' (Qabs (projT1 u n)) 1)
         (Hv : forall n : nat, QleT' (Qabs (projT1 v n)) 1),
   (forall n : nat, NatLe M n -> Qle (Qabs (projT1 u n - projT1 v n)) d0) ->
   forall n : nat, NatLe M n ->
   Qlt (Qabs (projT1 (cauchy_real_arctan u Hu) n
              - projT1 (cauchy_real_arctan v Hv) n)) eps))).
Proof.
  intros eps Heps.
  destruct (b5b_ap_uniform eps Heps) as [M [d0 [Hd0 Hcore]]].
  exists M. exists d0. exists Hd0.
  intros u v Hu Hv Hclose n Hn.
  rewrite (arctan_real_proj u Hu n).
  rewrite (arctan_real_proj v Hv n).
  exact (Hcore n (projT1 u n) (projT1 v n) Hn (Hu n) (Hv n) (Hclose n Hn)).
Qed.

(* 运输链·尾形域证书→clamp-1 代表元 real_eq（半径 1 版）：
   abl9b_w_bounds 尾形（|w_n|≤1/3 于 n≥Nw）+abl9b_wc_id_pt 尾恒等
   ⟹ real_eq (abl9b_wc x h Hd) (abl9b_w x h Hd)
   （件53 abl9b_wc34_w_real_eq 半径 3/4 先例的同构直接匹配）  *)
Lemma abl9b_rhs_wc1_w_real_eq : forall (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x))),
  real_eq (abl9b_wc x h Hd) (abl9b_w x h Hd).
Proof.
  intros x h Hx Hh4 Hd e He.
  destruct (abl9b_w_bounds x h Hx Hh4 Hd) as [Nw HNw].
  exists Nw. intros n Hn.
  destruct (HNw n Hn) as [Hb43 Hb13].
  assert (Hid : projT1 (abl9b_wc x h Hd) n == projT1 (abl9b_w x h Hd) n)
    by (apply (abl9b_wc_id_pt (abl9b_w x h Hd) n);
        exact (QleT'_to_Qle _ _ Hb13)).
  apply abl9_QltT_transfer_l with (x := 0%Q)
    (y := Qabs (projT1 (abl9b_wc x h Hd) n - projT1 (abl9b_w x h Hd) n)).
  - assert (Hz : projT1 (abl9b_wc x h Hd) n - projT1 (abl9b_w x h Hd) n
                 == 0%Q)
      by (rewrite Hid; ring).
    apply Qeq_sym.
    apply (Qeq_trans _ (Qabs 0%Q) _).
    + exact (abl9_Qabs_wd _ _ Hz).
    + reflexivity.
  - exact He.
Qed.

(* 逐点相等序列合同（件45 abl9_arctan_arg_wd 重锚再出口，本件 RHS 链
   自足引用位） *)
Lemma abl9b_rhs_arctan_arg_eq : forall (u v : Real)
  (Hu : forall n : nat, QleT' (Qabs (projT1 u n)) 1)
  (Hv : forall n : nat, QleT' (Qabs (projT1 v n)) 1)
  (N : nat),
  (forall n : nat, (N <= n)%nat -> projT1 u n == projT1 v n) ->
  real_eq (cauchy_real_arctan u Hu) (cauchy_real_arctan v Hv).
Proof.
  intros u v Hu Hv N Hpt.
  exact (abl9_arctan_arg_wd u v Hu Hv N Hpt).
Qed.

(* ============================================================ *)
(* 块三·Qinv 连续辅助引理：3/4≤a,b ⟹ |inva−invb| ≤ (16/9)|a−b|       *)
(* ============================================================ *)

(* 下界乘积：3/4≤a,b ⟹ 9/16≤a·b（两侧非负 Qmult_le_compat 链） *)
Lemma abl9b_rhs_qmul_3434 : forall a b : Q,
  QleT' (3#4) a -> QleT' (3#4) b -> Qle (9#16) (a * b).
Proof.
  intros a b Ha Hb.
  assert (Ha' : Qle (3#4) a) by (exact (QleT'_to_Qle _ _ Ha)).
  assert (Hb' : Qle (3#4) b) by (exact (QleT'_to_Qle _ _ Hb)).
  assert (H1 : Qle ((3#4) * (3#4)) (a * (3#4))).
  { apply (Qmult_le_compat_r (3#4) a (3#4)).
    - exact Ha'.
    - unfold Qle. simpl. lia. }
  assert (H2 : Qle (a * (3#4)) (a * b)).
  { apply (b3_qmult_le_l (3#4) b a).
    - apply Qlt_le_weak.
      apply (Qlt_le_trans 0 (3#4) a); [exact abl9b_rhs_q34_pos | exact Ha'].
    - exact Hb'. }
  apply (Qle_trans (9#16) ((3#4) * (3#4)) (a * b)).
  - apply qeq_imp_qle. reflexivity.
  - apply (Qle_trans ((3#4) * (3#4)) (a * (3#4)) (a * b)).
    + exact H1.
    + exact H2.
Qed.

(* 差恒等：inva−invb == (b−a)·inv(a·b)（非零侧条件；件30 Hsplit 证法） *)
Lemma abl9b_rhs_qinv_diff : forall a b : Q,
  ~ (a == 0) -> ~ (b == 0) ->
  Qinv a - Qinv b == (b - a) * Qinv (a * b).
Proof.
  intros a b Ha Hb.
  assert (Hzab : ~ (a * b == 0)).
  { intro Hz. destruct (Qmult_integral a b Hz) as [Hc | Hc].
    - exact (Ha Hc).
    - exact (Hb Hc). }
  assert (Haba : Qinv a * a == 1).
  { rewrite Qmult_comm. apply Qmult_inv_r. exact Ha. }
  assert (Habb : Qinv b * b == 1).
  { rewrite Qmult_comm. apply Qmult_inv_r. exact Hb. }
  assert (Hm : a * b * Qinv (a * b) == 1) by (apply Qmult_inv_r; exact Hzab).
  assert (Hs : (Qinv a - Qinv b) * (a * b) == b - a).
  { assert (Hfac : (Qinv a - Qinv b) * (a * b)
                   == (Qinv a * a) * b - (Qinv b * b) * a) by ring.
    rewrite Hfac, Haba, Habb. ring. }
  apply (Qeq_trans _ ((Qinv a - Qinv b) * (a * b) * Qinv (a * b))).
  - assert (Hassoc : (Qinv a - Qinv b) * (a * b) * Qinv (a * b)
                     == (Qinv a - Qinv b) * ((a * b) * Qinv (a * b))) by ring.
    rewrite Hassoc, Hm. ring.
  - rewrite Hs. reflexivity.
Qed.

(* 主件·Qinv 于 [3/4,∞) Lipschitz（QleT' 形域证书+Qle 证明）：
   |inva−invb| == |a−b|·inv(a·b) ≤ |a−b|·(16/9)（inv(a·b) ≤ 16/9 由
   a·b ≥ 9/16 跨乘 b5n_xinv_le 直接引用）  *)
Lemma abl9b_rhs_qinv_lip : forall a b : Q,
  QleT' (3#4) a -> QleT' (3#4) b ->
  Qle (Qabs (Qinv a - Qinv b)) ((16#9) * Qabs (a - b)).
Proof.
  intros a b Ha Hb.
  assert (Ha' : Qle (3#4) a) by (exact (QleT'_to_Qle _ _ Ha)).
  assert (Hb' : Qle (3#4) b) by (exact (QleT'_to_Qle _ _ Hb)).
  assert (Hapos : Qlt 0 a)
    by (apply (Qlt_le_trans 0 (3#4) a); [exact abl9b_rhs_q34_pos | exact Ha']).
  assert (Hbpos : Qlt 0 b)
    by (apply (Qlt_le_trans 0 (3#4) b); [exact abl9b_rhs_q34_pos | exact Hb']).
  assert (Hnza : ~ (a == 0))
    by (intro Hz; exact (Qlt_not_eq 0 a Hapos (Qeq_sym a 0 Hz))).
  assert (Hnzb : ~ (b == 0))
    by (intro Hz; exact (Qlt_not_eq 0 b Hbpos (Qeq_sym b 0 Hz))).
  assert (Habpos : Qlt 0 (a * b)) by (apply (Qmult_lt_0_compat a b); assumption).
  assert (Habge := abl9b_rhs_qmul_3434 a b Ha Hb).
  assert (Hinvle : Qle (Qinv (a * b)) (16#9)).
  { assert (Ht1 : Qle (1 * Qinv (a * b)) (Qinv (9#16))).
    { apply (b5n_xinv_le 1 (a * b) (9#16)).
      - exact Habpos.
      - exact abl9b_rhs_q916_pos.
      - apply (Qle_trans (1 * (9#16)) (9#16) (a * b)).
        + apply qeq_imp_qle. ring.
        + exact Habge. }
    apply (Qle_trans (Qinv (a * b)) (1 * Qinv (a * b)) (16#9)).
    - apply qeq_imp_qle. ring.
    - apply (Qle_trans (1 * Qinv (a * b)) (Qinv (9#16)) (16#9)).
      + exact Ht1.
      + apply qeq_imp_qle. reflexivity. }
  assert (Hinvpos : Qabs (Qinv (a * b)) == Qinv (a * b)).
  { apply (Qabs_pos (Qinv (a * b))).
    apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Habpos. }
  assert (Habsdiff : Qabs (b - a) == Qabs (a - b)) by (apply abl9b_q_abs_minus).
  rewrite (abl9b_rhs_qinv_diff a b Hnza Hnzb).
  rewrite Qabs_Qmult. rewrite Hinvpos. rewrite Habsdiff.
  apply (Qle_trans (Qabs (a - b) * Qinv (a * b))
                   (Qabs (a - b) * (16#9))
                   ((16#9) * Qabs (a - b))).
  - apply (b3_qmult_le_l (Qinv (a * b)) (16#9) (Qabs (a - b))).
    + apply Qabs_nonneg.
    + exact Hinvle.
  - apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* 块四·RHS_m→RHS 闭合骨架（前件参数形；与 LHS 侧接口对称）            *)
(* ============================================================ *)

(* 抽象闭合骨架：闭域 arctan 实参族 u_m 逐点尾收敛于 v（前件参数位）
   ⟹ m→∞ 项级闭合（(M1,M2) 双见证形：m≥M1 一致选号、n≥M2 项级尾）。
   一致连续证书=块二选器（(M2,d0) 对全序列对一致有效）。 *)
Lemma abl9b_rhs_arctan_uniform_close :
  forall (u : nat -> Real) (v : Real)
    (Hu : forall (m n : nat), QleT' (Qabs (projT1 (u m) n)) 1)
    (Hv : forall n : nat, QleT' (Qabs (projT1 v n)) 1)
    (Hconv : forall d : Q, Qlt 0 d ->
      sigT (fun M : nat => sigT (fun Nv : nat =>
        forall m : nat, (M <= m)%nat -> forall n : nat, (Nv <= n)%nat ->
        Qle (Qabs (projT1 (u m) n - projT1 v n)) d))),
  forall (eps : Q), QltT 0 eps ->
  sigT (fun M1 : nat => sigT (fun M2 : nat =>
    forall m : nat, (M1 <= m)%nat -> forall n : nat, NatLe M2 n ->
    QltT (Qabs (projT1 (cauchy_real_arctan (u m) (Hu m)) n
                - projT1 (cauchy_real_arctan v Hv) n)) eps)).
Proof.
  intros u v Hu Hv Hconv eps Heps.
  assert (Hepsq : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  destruct (b5b_ap_uniform eps Hepsq) as [M2 [d0 [Hd0 Hcore]]].
  destruct (Hconv d0 Hd0) as [M1 [Nv HM1]].
  exists M1. exists (Nat.max M2 Nv).
  intros m Hm n Hn.
  apply NatLe_drop in Hn.
  assert (Hn2 : NatLe M2 n) by (apply NatLe_lift; lia).
  assert (Hnv : (Nv <= n)%nat) by lia.
  apply Qlt_to_QltT.
  rewrite (arctan_real_proj (u m) (Hu m) n).
  rewrite (arctan_real_proj v Hv n).
  exact (Hcore n (projT1 (u m) n) (projT1 v n) Hn2 (Hu m n) (Hv n)
                 (HM1 m Hm n Hnv)).
Qed.

(* RHS 半边实例：clamp-1 代表元形 RHS_m→RHS 闭合。前件参数＝缩放
   w_m→w0 逐点尾收敛证书（(1−1/m) 缩放代数+块三 Qinv 辅助引理的合流接口
   位，甲/乙支 Q 侧四块供给）；域证书两侧=件30 clamp 全域证书（无条件
   可构造，A2 形）；Lipschitz 桥=块一。          *)
Lemma abl9b_rhs_close :
  forall (w : nat -> Real) (w0 : Real)
    (Hconv : forall d : Q, Qlt 0 d ->
      sigT (fun M : nat => sigT (fun Nv : nat =>
        forall m : nat, (M <= m)%nat -> forall n : nat, (Nv <= n)%nat ->
        Qle (Qabs (projT1 (w m) n - projT1 w0 n)) d))),
  forall (eps : Q), QltT 0 eps ->
  sigT (fun M1 : nat => sigT (fun M2 : nat =>
    forall m : nat, (M1 <= m)%nat -> forall n : nat, NatLe M2 n ->
    QltT (Qabs (projT1 (cauchy_real_arctan (abl9b_rhs_clamp1 (w m))
                          (abl9b_rhs_dom1 (w m))) n
                - projT1 (cauchy_real_arctan (abl9b_rhs_clamp1 w0)
                          (abl9b_rhs_dom1 w0)) n)) eps)).
Proof.
  intros w w0 Hconv eps Heps.
  assert (Hcl : forall d : Q, Qlt 0 d ->
    sigT (fun M : nat => sigT (fun Nv : nat =>
      forall m : nat, (M <= m)%nat -> forall n : nat, (Nv <= n)%nat ->
      Qle (Qabs (projT1 (abl9b_rhs_clamp1 (w m)) n
                  - projT1 (abl9b_rhs_clamp1 w0) n)) d))).
  { intros d Hd. destruct (Hconv d Hd) as [M1 [Nv HM1]].
    exists M1. exists Nv. intros m Hm n Hn.
    apply (Qle_trans (Qabs (projT1 (abl9b_rhs_clamp1 (w m)) n
                              - projT1 (abl9b_rhs_clamp1 w0) n))
                     (Qabs (projT1 (w m) n - projT1 w0 n))).
    - exact (abl9b_rhs_clamp1_lipQ (w m) w0 n).
    - exact (HM1 m Hm n Hn). }
  exact (abl9b_rhs_arctan_uniform_close
           (fun m : nat => abl9b_rhs_clamp1 (w m))
           (abl9b_rhs_clamp1 w0)
           (fun m n => abl9b_rhs_dom1 (w m) n)
           (fun n => abl9b_rhs_dom1 w0 n)
           Hcl eps Heps).
Qed.

(* 缩放 RHS 族定义（接口定形）：w 侧取件53 缩放对 (k_m·x,k_m·h) 与
   abl9b_sca_Hd 之 D_m 正性证书；闭合目标=原对 w 与原 Hd。 *)
Definition abl9b_rhs_ws (m : nat) (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1) : Real :=
  abl9b_w (abl9b_xsc m x) (abl9b_hsc m h) (abl9b_sca_Hd m x h Hx Hxh).

Definition abl9b_rhs_val (w : Real) : Real :=
  cauchy_real_arctan (abl9b_rhs_clamp1 w) (abl9b_rhs_dom1 w).

Definition abl9b_rhs0 (x h : Real)
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x))) : Real :=
  abl9b_rhs_val (abl9b_w x h Hd).

Definition abl9b_rhs_sc (m : nat) (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1) : Real :=
  abl9b_rhs_val (abl9b_rhs_ws m x h Hx Hxh).

(* 缩放实例闭合：Hconv 参数位=abl9b_rhs_ws m 对 abl9b_w x h Hd 的逐点尾
   收敛证书（Q 侧合流位）；结论=abl9b_rhs_sc m→abl9b_rhs0 项级尾。 *)
Lemma abl9b_rhs_sc_close : forall (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x)))
  (Hconv : forall d : Q, Qlt 0 d ->
    sigT (fun M : nat => sigT (fun Nv : nat =>
      forall m : nat, (M <= m)%nat -> forall n : nat, (Nv <= n)%nat ->
      Qle (Qabs (projT1 (abl9b_rhs_ws m x h Hx Hxh) n
                  - projT1 (abl9b_w x h Hd) n)) d))),
  forall (eps : Q), QltT 0 eps ->
  sigT (fun M1 : nat => sigT (fun M2 : nat =>
    forall m : nat, (M1 <= m)%nat -> forall n : nat, NatLe M2 n ->
    QltT (Qabs (projT1 (abl9b_rhs_sc m x h Hx Hxh) n
                - projT1 (abl9b_rhs0 x h Hd) n)) eps)).
Proof.
  intros x h Hx Hxh Hd Hconv eps Heps.
  exact (abl9b_rhs_close (fun m : nat => abl9b_rhs_ws m x h Hx Hxh)
                         (abl9b_w x h Hd) Hconv eps Heps).
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                          *)
(*   Lemma 名清单 16 = Qed 计数 16 = PA 语句 16，零差；                *)
(*   witness 形四件提取豁免登记见头注构造性注记节（件53 前例）。       *)
(* ============================================================ *)
Print Assumptions abl9b_rhs_q34_pos.
Print Assumptions abl9b_rhs_q916_pos.
Print Assumptions abl9b_rhs_q169_pos.
Print Assumptions abl9b_rhs_clamp1_proj.
Print Assumptions abl9b_rhs_wc_clamp1.
Print Assumptions abl9b_rhs_clamp1_lip.
Print Assumptions abl9b_rhs_clamp1_lipQ.
Print Assumptions abl9b_rhs_arctan_contract.
Print Assumptions abl9b_rhs_wc1_w_real_eq.
Print Assumptions abl9b_rhs_arctan_arg_eq.
Print Assumptions abl9b_rhs_qmul_3434.
Print Assumptions abl9b_rhs_qinv_diff.
Print Assumptions abl9b_rhs_qinv_lip.
Print Assumptions abl9b_rhs_arctan_uniform_close.
Print Assumptions abl9b_rhs_close.
Print Assumptions abl9b_rhs_sc_close.

(* 提取检验（判据 = 输出 Obj.magic 计 0）：三件安全形全测——
   wc1_w_real_eq（real_eq 尾形运输件，Set 顶）／clamp1_lip（Qle 顶）／
   qinv_lip（Qle 顶）。witness 形四件豁免同头注登记。 *)
Recursive Extraction abl9b_rhs_wc1_w_real_eq.
Recursive Extraction abl9b_rhs_clamp1_lip.
Recursive Extraction abl9b_rhs_qinv_lip.
