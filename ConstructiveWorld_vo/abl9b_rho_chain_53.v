(* ==========================================================================)
   abl9b_rho_chain_53.v — 缩放内点链（ρ 参数化 phi 链步界与缩放域证书）
   缩放对 (x_m,h_m):=(1−1/m)·(x,h) 的内点链三组（Q1 步界主件／Q2 缩放域证书／Q3 clamp-3/4 代表元）
   ── 数学使命：─────────────────────────────────────────────────────────────
   Q1 件51 定量望远镜引擎的 ρ 参数化版本（签名保持式：本件 Require 件51，
       件51 原语句零字节不动；本件提供 phi 链点形步界主件 abl9b_phistep_rho——
       件51 定量望远镜全案的 ρ 参数化实施：两侧内界参 rho/rw 全参化，余项常数
       Qinv(1−rho) 替代固定 (8/3)；先例=件19 abl9_atan_deriv_uniform 形）；
   Q2 缩放域证书：缩放因子 k_m:=m/(m+1)（即 1−1/(m+1)），内界参
       rho_m:=1−1/(2(m+1))=abl9b_rhom m；由件60 凸性核 abl9_conv_bnd_pt 得
       缩放路径点逐点 ≤ k_m ≤ rho_m（abl9b_sca_path_bnd），①b 直接使用参数位
       Hu/Huh 证书、h 缩放 Hh4 同见证传递、D_m 正性证书全组在件；
   Q3 w 侧 clamp-3/4 代表元：件30 clamp 构造的 3/4 半径变体（abl9b_wc34），
       全域证书 |w̃_n|≤3/4（①b w 侧 rho_w:=3/4 参数位直接匹配）+ 1-Lipschitz 一般
       半径辅助引理 + 尾恒等 real_eq（abl9b_w_bounds 尾形 1/3<3/4 直接匹配）。
   ── 依赖清单：──────────────────────────────────────────────────────────────
   S01–S11（基础模块）；件19 abl_arctan_diff_19（wsq/wincr 环等与除法恒等、
   ①b ρ 参数化先例）；件20 abl_arctan_diff_20（abl9_Qlt_transfer_l/r、
   abl9_Qabs_wd、abl9_q_pos_sq）；件30 abl9b_skeleton_30（abl9b_w、
   abl9b_w_bounds 尾形、clamp 构造模式）；件51 abl_arctan_diff_51
   （定量望远镜引擎正本，签名保持）；件60 abl_arctan_diff_60（凸性核
   abl9_conv_bnd_pt、点形斜率恒等 abl9_slope_pt）。
   ── 对标行：────────────────────────────────────────────────────────────────
   ①b ρ 参数化先例：abl_arctan_diff_19.v abl9_atan_deriv_uniform（L376 带）；
   clamp 构造正本：abl9b_skeleton_30.v abl9b_wc/abl9b_w_clamp_dom/abl9b_wc_id_pt
   （L288-325 带）+abl9b_w_bounds（L221 带，尾形）；凸性核：abl_arctan_diff_60.v
   abl9_conv_bnd_pt（L114 带）；点形斜率恒等：abl_arctan_diff_60.v abl9_slope_pt
   （L81 带）；b3rr 核：S11_TP3B5.v b3rr_core_r（L5319 带）；步界全案：
   abl_arctan_diff_51 定量望远镜引擎全案；路线依据：两侧内界参全参
   化、余项常数 Qinv(1−rho) 替代固定 (8/3) 的参数化路线。
   ── 构造性注记：────────────────────────────────────────────────────────────
   全件 Qed 真构造，零承认式声明，零经典逻辑；
   零承认链短路策略（Q 序链走 Qlt/Qle_trans 系+b3_qmult_le_l/b5n_xinv_le 跨乘逐链构造）；
   语句面承载位全 Set 形（sigT/real_eq/real_lt/QleT'），Qle/Qlt 仅标量前提位
   （件19/51/60 同款口径）；主定理 Print Assumptions 全 Closed，Extraction
   检验判据 Obj.magic 计 0。缩放常量取 k_m:=m/(m+1)、rho_m:=1−1/(2(m+1))
   （Qmake (Z.of_nat m) (Pos.of_succ_nat m) 形——分母恒正，免 m≥1 分支）。
   ── 编译配方：──────────────────────────────────────────────────────────────
   source Live/toolchain/env.sh && unset COQLIB ROCQLIB && cd abl_a2b3_WASH_pool
   nice -19 rocq c -native-compiler no -Q "$PWD" "" "$PWD/abl9b_rho_chain_53.v"
   （单道顺序；绿判四件套：EXIT=0／日志 Closed 无 Error／vo 头 8 字节
   436f7121 00015ff4／vo 新于 v。）
   ── 交付声明 ──────────────────────────────────────────────────────────────
   本件为中文声明的零承认件：全文件零承认式声明、零悬置前提、零经典逻辑，
   全部结论 Qed 真构造闭合。
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
Require Import abl9b_skeleton_30.
Require Import abl_arctan_diff_51.
Require Import abl_arctan_diff_60.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import ZArith Extraction.

(* ============================================================ *)
(* §0·Q 层基建（单调核自建，平移分配取 Q 模块限定名）                *)
(* ============================================================ *)

Lemma abl9b_zpos_succ : forall m : nat,
  Z.pos (Pos.of_succ_nat m) = (Z.of_nat m + 1)%Z.
Proof.
  intros m. destruct m as [| m'].
  - reflexivity.
  - change (Z.pos (Pos.of_succ_nat (Datatypes.S m')))
      with (Z.of_nat (Datatypes.S (Datatypes.S m'))).
    rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma abl9b_zpos_twice : forall m : nat,
  Z.pos (2 * Pos.of_succ_nat m) = (2 * Z.of_nat m + 2)%Z.
Proof.
  intros m.
  rewrite Pos2Z.inj_mul.
  rewrite abl9b_zpos_succ.
  lia.
Qed.

Lemma abl9b_qmax_mono : forall a b c : Q, Qle a b -> Qle (Qmax a c) (Qmax b c).
Proof.
  intros a b c H.
  destruct (Qlt_le_dec b c) as [Hbc | Hcb].
  - rewrite (Q.max_r b c (Qlt_le_weak b c Hbc)).
    destruct (Qlt_le_dec a c) as [Hac | Hca].
    + rewrite (Q.max_r a c (Qlt_le_weak a c Hac)). apply Qle_refl.
    + rewrite (Q.max_l a c Hca). apply (Qle_trans a b c); [exact H | apply Qlt_le_weak; exact Hbc].
  - rewrite (Q.max_l b c Hcb).
    destruct (Qlt_le_dec a c) as [Hac | Hca].
    + rewrite (Q.max_r a c (Qlt_le_weak a c Hac)). exact Hcb.
    + rewrite (Q.max_l a c Hca). exact H.
Qed.

Lemma abl9b_qmax_mono2 : forall a b c d : Q,
  Qle a b -> Qle c d -> Qle (Qmax a c) (Qmax b d).
Proof.
  intros a b c d Hab Hcd.
  apply (Qle_trans (Qmax a c) (Qmax b c) (Qmax b d)).
  - apply (abl9b_qmax_mono a b c Hab).
  - rewrite (Q.max_comm b d).
    apply (Qle_trans (Qmax b c) (Qmax c b) (Qmax d b)).
    + apply qeq_imp_qle. apply Q.max_comm.
    + apply (abl9b_qmax_mono c d b Hcd).
Qed.

Lemma abl9b_qmin_mono : forall a b c : Q, Qle a b -> Qle (Qmin a c) (Qmin b c).
Proof.
  intros a b c H.
  destruct (Qlt_le_dec c b) as [Hcb | Hbc].
  - rewrite (Q.min_r b c (Qlt_le_weak c b Hcb)).
    destruct (Qlt_le_dec a c) as [Hac | Hca].
    + rewrite (Q.min_l a c (Qlt_le_weak a c Hac)). exact (Qlt_le_weak a c Hac).
    + rewrite (Q.min_r a c Hca). apply Qle_refl.
  - rewrite (Q.min_l b c Hbc).
    assert (Hac : Qle a c) by (apply (Qle_trans a b c); [exact H | exact Hbc]).
    rewrite (Q.min_l a c Hac). exact H.
Qed.

Lemma abl9b_qmin_mono2 : forall a b c d : Q,
  Qle a b -> Qle c d -> Qle (Qmin a c) (Qmin b d).
Proof.
  intros a b c d Hab Hcd.
  apply (Qle_trans (Qmin a c) (Qmin b c) (Qmin b d)).
  - apply (abl9b_qmin_mono a b c Hab).
  - rewrite (Q.min_comm b d).
    apply (Qle_trans (Qmin b c) (Qmin c b) (Qmin d b)).
    + apply qeq_imp_qle. apply Q.min_comm.
    + apply (abl9b_qmin_mono c d b Hcd).
Qed.

Lemma abl9b_qminus_le : forall a b c d : Q,
  Qle a b -> Qle c d -> Qle (a - d) (b - c).
Proof.
  intros a b c d Hab Hcd.
  apply (Qle_trans (a - d) (a - c) (b - c)).
  - apply Qplus_le_compat; [apply Qle_refl | apply (Qopp_le_compat c d); exact Hcd].
  - apply Qplus_le_compat; [exact Hab | apply Qle_refl].
Qed.

Lemma abl9b_q_self_plus_le : forall a d : Q, Qle 0 d -> Qle a (a + d).
Proof.
  intros a d Hd.
  apply (Qle_trans a (a + 0) (a + d)).
  - apply qeq_imp_qle. ring.
  - apply Qplus_le_compat; [apply Qle_refl | exact Hd].
Qed.

Lemma abl9b_q_abs_minus : forall a b : Q, Qabs (a - b) == Qabs (b - a).
Proof.
  intros a b.
  assert (Hr : b - a == -(a - b)) by ring.
  rewrite Hr. rewrite Qabs_opp. reflexivity.
Qed.

Lemma abl9b_q_abs_sq : forall a : Q, Qabs a * Qabs a == a * a.
Proof.
  intros a. destruct (Qlt_le_dec a 0) as [Hn | Hp].
  - assert (Habs : Qabs a == - a).
    { apply Qabs_neg. apply Qlt_le_weak. exact Hn. }
    rewrite Habs. ring.
  - assert (Habs : Qabs a == a).
    { apply (Qabs_pos a). exact Hp. }
    rewrite Habs. reflexivity.
Qed.

(* ============================================================ *)
(* §1·缩放常量 k_m:=m/(m+1) 与内界参 rho_m:=1−1/(2(m+1))：Q 序事实   *)
(* ============================================================ *)

Definition abl9b_ksc (m : nat) : Q := (Z.of_nat m) # (Pos.of_succ_nat m).

Definition abl9b_rhom (m : nat) : Q :=
  (2 * Z.of_nat m + 1)%Z # (2 * Pos.of_succ_nat m).

(* 投影披露件：Qnum/Qden 直转 reflexivity（禁 cbn——2*Z.of_nat m 会被
   展成 Z.match 断 lia；序事实一律 parts 披露+rewrite+lia 证法） *)
Lemma abl9b_ksc_parts : forall m : nat,
  Qnum (abl9b_ksc m) = Z.of_nat m /\
  Qden (abl9b_ksc m) = Pos.of_succ_nat m.
Proof. intros m. split; reflexivity. Qed.

Lemma abl9b_rhom_parts : forall m : nat,
  Qnum (abl9b_rhom m) = (2 * Z.of_nat m + 1)%Z /\
  Qden (abl9b_rhom m) = (2 * Pos.of_succ_nat m)%positive.
Proof. intros m. split; reflexivity. Qed.

Lemma abl9b_q0_parts : Qnum (0%Q) = 0%Z /\ Qden (0%Q) = 1%positive.
Proof. split; reflexivity. Qed.

Lemma abl9b_q1_parts : Qnum (1%Q) = 1%Z /\ Qden (1%Q) = 1%positive.
Proof. split; reflexivity. Qed.

Lemma abl9b_ksc0 : forall m : nat, Qle 0 (abl9b_ksc m).
Proof.
  intros m. destruct (abl9b_ksc_parts m) as [Hn Hd].
  destruct abl9b_q0_parts as [H0n H0d].
  unfold Qle. rewrite Hn, Hd, H0n, H0d. lia.
Qed.

Lemma abl9b_ksc1 : forall m : nat, Qlt (abl9b_ksc m) 1.
Proof.
  intros m. destruct (abl9b_ksc_parts m) as [Hn Hd].
  destruct abl9b_q1_parts as [H1n H1d].
  unfold Qlt. rewrite Hn, Hd, H1n, H1d.
  rewrite abl9b_zpos_succ. lia.
Qed.

Lemma abl9b_rhom0 : forall m : nat, Qle 0 (abl9b_rhom m).
Proof.
  intros m. destruct (abl9b_rhom_parts m) as [Hn Hd].
  destruct abl9b_q0_parts as [H0n H0d].
  unfold Qle. rewrite Hn, Hd, H0n, H0d. lia.
Qed.

Lemma abl9b_rhom_lt1 : forall m : nat, Qlt (abl9b_rhom m) 1.
Proof.
  intros m. destruct (abl9b_rhom_parts m) as [Hn Hd].
  destruct abl9b_q1_parts as [H1n H1d].
  unfold Qlt. rewrite Hn, Hd, H1n, H1d.
  rewrite abl9b_zpos_twice. lia.
Qed.

Lemma abl9b_ksc_le_rhom : forall m : nat, Qle (abl9b_ksc m) (abl9b_rhom m).
Proof.
  intros m.
  destruct (abl9b_ksc_parts m) as [Hn1 Hd1].
  destruct (abl9b_rhom_parts m) as [Hn2 Hd2].
  unfold Qle. rewrite Hn1, Hd1, Hn2, Hd2.
  rewrite abl9b_zpos_twice. rewrite abl9b_zpos_succ.
  assert (Hd : ((2 * Z.of_nat m + 1) * (Z.of_nat m + 1)
               - Z.of_nat m * (2 * Z.of_nat m + 2) = (Z.of_nat m + 1))%Z) by ring.
  lia.
Qed.

Lemma abl9b_ksc_sq_lt1 : forall m : nat, Qlt (abl9b_ksc m * abl9b_ksc m) 1.
Proof.
  intros m.
  assert (H0 : Qle 0 (abl9b_ksc m)) by apply abl9b_ksc0.
  assert (H1 : Qlt (abl9b_ksc m) 1) by apply abl9b_ksc1.
  assert (Hk1 : Qle (abl9b_ksc m) 1) by (apply Qlt_le_weak; exact H1).
  apply (Qle_lt_trans (abl9b_ksc m * abl9b_ksc m)
                      (1 * abl9b_ksc m) 1).
  - exact (Qmult_le_compat_r (abl9b_ksc m) 1 (abl9b_ksc m) Hk1 H0).
  - assert (Heq2 : abl9b_ksc m == 1 * abl9b_ksc m) by ring.
    exact (abl9_Qlt_transfer_l (abl9b_ksc m) (1 * abl9b_ksc m) 1 Heq2 H1).
Qed.

(* ============================================================ *)
(* §2·w 侧 clamp-3/4 代表元（件30 clamp 构造的 3/4 半径变体）        *)
(*    Q 核两件 + 1-Lipschitz 一般半径两件 + Real 层三件              *)
(* ============================================================ *)

Lemma abl9b_q_clamp34_bnd : forall a : Q,
  Qle (Qabs (Qmin (Qmax a (-(3#4))) (3#4))) (3#4).
Proof.
  intros a.
  apply Qabs_Qle_condition. split.
  - apply Q.min_glb.
    + apply Q.le_max_r.
    + unfold Qle. cbn. lia.
  - apply Q.le_min_r.
Qed.

Lemma abl9b_q_clamp34_id : forall a : Q,
  Qle (-(3#4)) a -> Qle a (3#4) ->
  Qmin (Qmax a (-(3#4))) (3#4) == a.
Proof.
  intros a H1 H2.
  rewrite (Q.max_l a (-(3#4)) H1).
  apply Q.min_l. exact H2.
Qed.

(* 1-Lipschitz 单侧界：clamp(a) ≤ clamp(b)+|a−b|（一般半径 c≥0）  *)
Lemma abl9b_q_clamp_le_add : forall c a b : Q, Qle 0 c ->
  Qle (Qmin (Qmax a (-c)) c) (Qmin (Qmax b (-c)) c + Qabs (a - b)).
Proof.
  intros c a b Hc.
  assert (Hd0 : Qle 0 (Qabs (a - b))) by apply Qabs_nonneg.
  assert (Hub : Qle a (b + Qabs (a - b))).
  { apply (Qle_trans a (b + (a - b)) (b + Qabs (a - b))).
    - apply qeq_imp_qle. ring.
    - apply Qplus_le_compat; [apply Qle_refl | exact (Qle_Qabs (a - b))]. }
  assert (Hnc : Qle (-c) ((-c) + Qabs (a - b)))
    by (apply abl9b_q_self_plus_le; exact Hd0).
  apply (Qle_trans (Qmin (Qmax a (-c)) c)
                   (Qmin (Qmax (b + Qabs (a - b)) ((-c) + Qabs (a - b)))
                         (c + Qabs (a - b)))
                   (Qmin (Qmax b (-c)) c + Qabs (a - b))).
  - apply (abl9b_qmin_mono2
             (Qmax a (-c))
             (Qmax (b + Qabs (a - b)) ((-c) + Qabs (a - b)))
             c (c + Qabs (a - b))).
    + apply (abl9b_qmax_mono2 a (b + Qabs (a - b)) (-c) ((-c) + Qabs (a - b)));
        [exact Hub | exact Hnc].
    + apply abl9b_q_self_plus_le; exact Hd0.
  - rewrite (Q.plus_max_distr_r b (-c) (Qabs (a - b))).
    rewrite (Q.plus_min_distr_r (Qmax b (-c)) c (Qabs (a - b))).
    apply Qle_refl.
Qed.

(* 1-Lipschitz 主件：|clamp(a)−clamp(b)| ≤ |a−b|（一般半径 c≥0） *)
Lemma abl9b_q_clamp_lip : forall c a b : Q, Qle 0 c ->
  Qle (Qabs (Qmin (Qmax a (-c)) c - Qmin (Qmax b (-c)) c))
      (Qabs (a - b)).
Proof.
  intros c a b Hc.
  pose proof (abl9b_q_clamp_le_add c a b Hc) as H1.
  pose proof (abl9b_q_clamp_le_add c b a Hc) as H2.
  assert (Hd0 : Qle 0 (Qabs (a - b))) by apply Qabs_nonneg.
  apply Qabs_Qle_condition. split.
  - (* −|a−b| ≤ clamp(a)−clamp(b)：由 H2（对称形）化减形后取负 *)
    assert (Habsym : Qabs (b - a) == Qabs (a - b)) by (apply abl9b_q_abs_minus).
    assert (H2' : Qle (Qmin (Qmax b (-c)) c - Qmin (Qmax a (-c)) c) (Qabs (a - b))).
    { apply (Qle_trans
               (Qmin (Qmax b (-c)) c - Qmin (Qmax a (-c)) c)
               ((Qmin (Qmax a (-c)) c + Qabs (b - a)) - Qmin (Qmax a (-c)) c)
               (Qabs (a - b))).
      - exact (abl9b_qminus_le (Qmin (Qmax b (-c)) c)
                                 (Qmin (Qmax a (-c)) c + Qabs (b - a))
                                 (Qmin (Qmax a (-c)) c) (Qmin (Qmax a (-c)) c)
                                 H2 (Qle_refl (Qmin (Qmax a (-c)) c))).
      - apply qeq_imp_qle. rewrite Habsym. ring. }
    apply (Qle_trans (-(Qabs (a - b))) (-(Qmin (Qmax b (-c)) c - Qmin (Qmax a (-c)) c))
                     (Qmin (Qmax a (-c)) c - Qmin (Qmax b (-c)) c)).
    + apply (Qopp_le_compat (Qmin (Qmax b (-c)) c - Qmin (Qmax a (-c)) c)
                            (Qabs (a - b)) H2').
    + apply qeq_imp_qle. ring.
  - (* clamp(a)−clamp(b) ≤ |a−b|：由 H1 同减 clamp(b) *)
    apply (Qle_trans
             (Qmin (Qmax a (-c)) c - Qmin (Qmax b (-c)) c)
             ((Qmin (Qmax b (-c)) c + Qabs (a - b)) - Qmin (Qmax b (-c)) c)
             (Qabs (a - b))).
    + exact (abl9b_qminus_le (Qmin (Qmax a (-c)) c)
                             (Qmin (Qmax b (-c)) c + Qabs (a - b))
                             (Qmin (Qmax b (-c)) c) (Qmin (Qmax b (-c)) c)
                             H1 (Qle_refl (Qmin (Qmax b (-c)) c))).
    + apply qeq_imp_qle. ring.
Qed.

(* Real 层：clamp-3/4 代表元定义（件30 abl9b_wc 的 3/4 半径变体） *)
Definition abl9b_wc34 (x h : Real)
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x))) : Real :=
  real_min (real_max (abl9b_w x h Hd) (real_const (-(3#4)))) (real_const (3#4)).

(* 全域证书：∀n |w̃_n| ≤ 3/4（①b w 侧内界参 rho_w:=3/4 直接匹配参数位）  *)
Lemma abl9b_w_clamp34_dom : forall (x h : Real)
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x))),
  forall n : nat,
  QleT' (Qabs (projT1 (abl9b_wc34 x h Hd) n)) (3#4).
Proof.
  intros x h Hd n.
  pose proof (real_min_proj (real_max (abl9b_w x h Hd) (real_const (-(3#4))))
                             (real_const (3#4)) n) as H1.
  pose proof (real_max_proj (abl9b_w x h Hd) (real_const (-(3#4))) n) as H2.
  rewrite H2 in H1.
  rewrite (real_const_proj (-(3#4)) n) in H1.
  rewrite (real_const_proj (3#4) n) in H1.
  apply Qle_to_QleT'. rewrite H1. apply abl9b_q_clamp34_bnd.
Qed.

(* 点位域内恒等：|w_n| ≤ 1/3 ⟹ w̃_n == w_n（1/3 < 3/4 直接匹配）  *)
Lemma abl9b_wc34_id_pt : forall (x h : Real)
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x)))
  (n : nat),
  Qle (Qabs (projT1 (abl9b_w x h Hd) n)) (1#3) ->
  projT1 (abl9b_wc34 x h Hd) n == projT1 (abl9b_w x h Hd) n.
Proof.
  intros x h Hd n Hb.
  apply Qabs_Qle_condition in Hb. destruct Hb as [Hlo Hhi].
  assert (Hp : projT1 (abl9b_wc34 x h Hd) n
               == Qmin (Qmax (projT1 (abl9b_w x h Hd) n) (-(3#4))) (3#4)).
  { pose proof (real_min_proj (real_max (abl9b_w x h Hd) (real_const (-(3#4))))
                              (real_const (3#4)) n) as H1.
    pose proof (real_max_proj (abl9b_w x h Hd) (real_const (-(3#4))) n) as H2.
    rewrite H2 in H1.
    rewrite (real_const_proj (-(3#4)) n) in H1.
    rewrite (real_const_proj (3#4) n) in H1.
    exact H1. }
  rewrite Hp. apply abl9b_q_clamp34_id.
  - apply (Qle_trans (-(3#4)) (-(1#3)) (projT1 (abl9b_w x h Hd) n)).
    + unfold Qle. cbn. lia.
    + exact Hlo.
  - apply (Qle_trans (projT1 (abl9b_w x h Hd) n) (1#3) (3#4)).
    + exact Hhi.
    + unfold Qle. cbn. lia.
Qed.

(* 尾恒等主件：abl9b_w_bounds 尾形（|w_n|≤1/3 于 n≥Nw）⟹ real_eq *)
Lemma abl9b_wc34_w_real_eq : forall (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x))),
  real_eq (abl9b_wc34 x h Hd) (abl9b_w x h Hd).
Proof.
  intros x h Hx Hh4 Hd e He.
  destruct (abl9b_w_bounds x h Hx Hh4 Hd) as [Nw HNw].
  exists Nw. intros n Hn.
  destruct (HNw n Hn) as [Hb43 Hb13].
  assert (Hid : projT1 (abl9b_wc34 x h Hd) n == projT1 (abl9b_w x h Hd) n)
    by (apply (abl9b_wc34_id_pt x h Hd n); exact (QleT'_to_Qle _ _ Hb13)).
  apply abl9_QltT_transfer_l with (x := 0%Q)
    (y := Qabs (projT1 (abl9b_wc34 x h Hd) n - projT1 (abl9b_w x h Hd) n)).
  - assert (Hz : projT1 (abl9b_wc34 x h Hd) n - projT1 (abl9b_w x h Hd) n
                 == 0%Q)
      by (rewrite Hid; ring).
    apply Qeq_sym.
    apply (Qeq_trans _ (Qabs 0%Q) _).
    + exact (abl9_Qabs_wd _ _ Hz).
    + reflexivity.
  - exact He.
Qed.

(* ============================================================ *)
(* §3·缩放域证书：缩放对 (x_m,h_m):=k_m·(x,h)，k_m:=m/(m+1)          *)
(*    凸性核 abl9_conv_bnd_pt 直接引用：路径点逐点 ≤ k_m ≤ rho_m；    *)
(*    ①b 直接使用参数位 Hu/Huh 证书 + h 缩放 Hh4 同见证传递 + D_m 正性。 *)
(* ============================================================ *)

Definition abl9b_xsc (m : nat) (x : Real) : Real :=
  real_mult (real_const (abl9b_ksc m)) x.

Definition abl9b_hsc (m : nat) (h : Real) : Real :=
  real_mult (real_const (abl9b_ksc m)) h.

Lemma abl9b_xsc_proj : forall (m : nat) (x : Real) (n : nat),
  projT1 (abl9b_xsc m x) n == abl9b_ksc m * projT1 x n.
Proof.
  intros m x n. unfold abl9b_xsc.
  rewrite (real_mult_proj (real_const (abl9b_ksc m)) x n).
  rewrite (real_const_proj (abl9b_ksc m) n). reflexivity.
Qed.

(* Q 核：缩放路径点 |k·(x+κ·t)| ≤ k（凸性核直接引用+|k|=k）  *)
Lemma abl9b_sca_path_q : forall (m : nat) (x t k0 : Q),
  Qle (Qabs x) 1 -> Qle (Qabs (x + t)) 1 ->
  Qle 0 k0 -> Qle k0 1 ->
  Qle (Qabs (abl9b_ksc m * (x + k0 * t))) (abl9b_ksc m).
Proof.
  intros m x t k0 Hx Hxt Hk0 Hk1.
  rewrite Qabs_Qmult.
  assert (Habsk : Qabs (abl9b_ksc m) == abl9b_ksc m)
    by (apply (Qabs_pos (abl9b_ksc m)); apply abl9b_ksc0).
  rewrite Habsk.
  apply (Qle_trans (abl9b_ksc m * Qabs (x + k0 * t))
                   (abl9b_ksc m * 1) (abl9b_ksc m)).
  - exact (b3_qmult_le_l (Qabs (x + k0 * t)) 1 (abl9b_ksc m)
             (abl9b_ksc0 m)
             (abl9_conv_bnd_pt x t k0 Hx Hxt Hk0 Hk1)).
  - apply qeq_imp_qle. ring.
Qed.

(* Real 主件：缩放路径点逐点 ≤ rho_m（凸性核经点形传输） *)
Lemma abl9b_sca_path_bnd : forall (m : nat) (x h t : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (Ht : forall n : nat, And (Qle 0 (projT1 t n)) (Qle (projT1 t n) 1)),
  forall n : nat,
  QleT' (Qabs (projT1 (real_plus (abl9b_xsc m x)
                                    (real_mult t (abl9b_hsc m h))) n))
        (abl9b_rhom m).
Proof.
  intros m x h t Hx Hxh Ht n.
  assert (Hpx := abl9b_xsc_proj m x n).
  assert (Hph := abl9b_xsc_proj m h n).
  assert (Hp : projT1 (real_plus (abl9b_xsc m x)
                                 (real_mult t (abl9b_hsc m h))) n
               == abl9b_ksc m * (projT1 x n + projT1 t n * projT1 h n)).
  { rewrite (real_plus_proj (abl9b_xsc m x)
                            (real_mult t (abl9b_hsc m h)) n).
    rewrite (real_mult_proj t (abl9b_hsc m h) n).
    rewrite Hpx. rewrite Hph. ring. }
  destruct (Ht n) as [Ht0 Ht1].
  apply (qleT'_trans _ (abl9b_ksc m) _).
  - apply Qle_to_QleT'. rewrite Hp.
    apply (abl9b_sca_path_q m (projT1 x n) (projT1 h n) (projT1 t n)).
    + apply QleT'_to_Qle. apply (Hx n).
    + rewrite <- (real_plus_proj x h n). apply QleT'_to_Qle. apply (Hxh n).
    + exact Ht0.
    + exact Ht1.
  - apply Qle_to_QleT'. exact (abl9b_ksc_le_rhom m).
Qed.

(* ①b 参数位 Hu（直接使用）：缩放基点逐点 ≤ rho_m  *)
Lemma abl9b_sca_Hu : forall (m : nat) (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall n : nat,
  QleT' (Qabs (projT1 (abl9b_xsc m x) n)) (abl9b_rhom m).
Proof.
  intros m x Hx n.
  assert (Hpx := abl9b_xsc_proj m x n).
  apply (qleT'_trans _ (abl9b_ksc m) _).
  - apply Qle_to_QleT'. rewrite Hpx. rewrite Qabs_Qmult.
    assert (Habsk : Qabs (abl9b_ksc m) == abl9b_ksc m)
      by (apply (Qabs_pos (abl9b_ksc m)); apply abl9b_ksc0).
    rewrite Habsk.
    apply (Qle_trans (abl9b_ksc m * Qabs (projT1 x n))
                     (abl9b_ksc m * 1) (abl9b_ksc m)).
    + exact (b3_qmult_le_l (Qabs (projT1 x n)) 1 (abl9b_ksc m)
               (abl9b_ksc0 m) (QleT'_to_Qle _ _ (Hx n))).
    + apply qeq_imp_qle. ring.
  - apply Qle_to_QleT'. exact (abl9b_ksc_le_rhom m).
Qed.

(* ①b 参数位 Huh（直接使用）：缩放端点 x_m+h_m 逐点 ≤ rho_m ≤ 1  *)
Lemma abl9b_sca_Huh : forall (m : nat) (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  forall n : nat,
  QleT' (Qabs (projT1 (real_plus (abl9b_xsc m x) (abl9b_hsc m h)) n)) 1.
Proof.
  intros m x h Hx Hxh n.
  assert (Hp : projT1 (real_plus (abl9b_xsc m x) (abl9b_hsc m h)) n
               == abl9b_ksc m * (projT1 x n + projT1 h n)).
  { rewrite (real_plus_proj (abl9b_xsc m x) (abl9b_hsc m h) n).
    rewrite (abl9b_xsc_proj m x n). rewrite (abl9b_xsc_proj m h n). ring. }
  assert (Habsk : Qabs (abl9b_ksc m) == abl9b_ksc m)
    by (apply (Qabs_pos (abl9b_ksc m)); apply abl9b_ksc0).
  assert (Hxh1 : Qle (Qabs (projT1 x n + projT1 h n)) 1).
  { rewrite <- (real_plus_proj x h n). apply QleT'_to_Qle. apply (Hxh n). }
  apply (qleT'_trans _ (abl9b_rhom m) _).
  - apply Qle_to_QleT'. rewrite Hp. rewrite Qabs_Qmult. rewrite Habsk.
    apply (Qle_trans (abl9b_ksc m * Qabs (projT1 x n + projT1 h n))
                     (abl9b_ksc m * 1) (abl9b_rhom m)).
    + exact (b3_qmult_le_l (Qabs (projT1 x n + projT1 h n)) 1 (abl9b_ksc m)
               (abl9b_ksc0 m) Hxh1).
    + apply (Qle_trans (abl9b_ksc m * 1) (abl9b_ksc m) (abl9b_rhom m)).
      * apply qeq_imp_qle. ring.
      * exact (abl9b_ksc_le_rhom m).
  - apply Qle_to_QleT'. apply Qlt_le_weak. apply abl9b_rhom_lt1.
Qed.

(* h 缩放 Hh4 同见证传递：|h_n|<1/4 终近 ⟹ |k·h_n|<1/4 终近同见证 *)
Lemma abl9b_sca_Hh4 : forall (m : nat) (h : Real),
  real_lt (real_abs h) (real_const (1 # 4)) ->
  real_lt (real_abs (abl9b_hsc m h)) (real_const (1 # 4)).
Proof.
  intros m h Hh4.
  destruct Hh4 as [e0 [He0 [N0 HN0]]].
  assert (Habsk : Qabs (abl9b_ksc m) == abl9b_ksc m)
    by (apply (Qabs_pos (abl9b_ksc m)); apply abl9b_ksc0).
  assert (Hle : forall n : nat,
           Qle (Qabs (projT1 (abl9b_hsc m h) n)) (Qabs (projT1 h n))).
  { intros n. rewrite (abl9b_xsc_proj m h n). rewrite Qabs_Qmult. rewrite Habsk.
    apply (Qle_trans (abl9b_ksc m * Qabs (projT1 h n))
                     (1 * Qabs (projT1 h n)) (Qabs (projT1 h n))).
    - apply (Qmult_le_compat_r (abl9b_ksc m) 1 (Qabs (projT1 h n))).
      + apply Qlt_le_weak. apply abl9b_ksc1.
      + apply Qabs_nonneg.
    - apply qeq_imp_qle. ring. }
  exists e0. split.
  - exact He0.
  - exists N0. intros n Hn.
    assert (H0 : Qlt e0 (Qminus (1#4) (Qabs (projT1 h n)))).
    { apply QltT_to_Qlt.
      apply (qltT_eq_compat_r (Qminus (1#4) (Qabs (projT1 h n)))
                              (Qminus (projT1 (real_const (1#4)) n)
                                      (projT1 (real_abs h) n)) e0).
      - rewrite (real_const_proj (1#4) n). rewrite (real_abs_proj h n).
        reflexivity.
      - exact (HN0 n Hn). }
    apply Qlt_to_QltT.
    apply (Qlt_le_trans e0
             (Qminus (1#4) (Qabs (projT1 h n)))
             (Qminus (projT1 (real_const (1#4)) n)
                     (projT1 (real_abs (abl9b_hsc m h)) n))).
    + exact H0.
    + apply (Qle_trans (Qminus (1#4) (Qabs (projT1 h n)))
                       (Qminus (1#4) (Qabs (projT1 (abl9b_hsc m h) n)))
                       (Qminus (projT1 (real_const (1#4)) n)
                               (projT1 (real_abs (abl9b_hsc m h)) n))).
      * apply abl9b_qminus_le; [apply Qle_refl | exact (Hle n)].
      * apply qeq_imp_qle.
        rewrite (real_const_proj (1#4) n).
        rewrite (real_abs_proj (abl9b_hsc m h) n). reflexivity.
Qed.

(* Q 核：缩放 D = 1+(k·x+k·h)(k·x) ≥ 1−k²（(x+h)x ≥ −|x+h||x| ≥ −1 链） *)
Lemma abl9b_D_sca_q : forall (m : nat) (x h : Q),
  Qle (Qabs x) 1 -> Qle (Qabs (x + h)) 1 ->
  Qle (1 - abl9b_ksc m * abl9b_ksc m)
      (1 + (abl9b_ksc m * x + abl9b_ksc m * h) * (abl9b_ksc m * x)).
Proof.
  intros m x h Hx Hxh.
  assert (Hlo : Qle (-1) ((x + h) * x)).
  { apply (Qle_trans (-1) (-(Qabs ((x + h) * x))) ((x + h) * x)).
    - apply (Qopp_le_compat (Qabs ((x + h) * x)) 1).
      apply (Qle_trans (Qabs ((x + h) * x)) (Qabs (x + h) * Qabs x) 1).
      + rewrite Qabs_Qmult. apply Qle_refl.
      + apply (Qmult_le_compat_nonneg (Qabs (x + h)) 1 (Qabs x) 1).
        * split; [apply Qabs_nonneg | exact Hxh].
        * split; [apply Qabs_nonneg | exact Hx].
    - destruct (proj1 (Qabs_Qle_condition ((x + h) * x)
                         (Qabs ((x + h) * x)))
                  (Qle_refl (Qabs ((x + h) * x)))) as [Hl _].
      exact Hl. }
  pose proof (b3_qmult_le_l (-1) ((x + h) * x) (abl9b_ksc m)
                (abl9b_ksc0 m) Hlo) as Hm1.
  pose proof (b3_qmult_le_l (abl9b_ksc m * -1)
                (abl9b_ksc m * ((x + h) * x)) (abl9b_ksc m)
                (abl9b_ksc0 m) Hm1) as Hm2.
  assert (Hm3 : Qle (abl9b_ksc m * (abl9b_ksc m * -1))
                    ((abl9b_ksc m * x + abl9b_ksc m * h)
                     * (abl9b_ksc m * x))).
  { apply (Qle_trans (abl9b_ksc m * (abl9b_ksc m * -1))
                     (abl9b_ksc m * (abl9b_ksc m * ((x + h) * x)))
                     ((abl9b_ksc m * x + abl9b_ksc m * h)
                      * (abl9b_ksc m * x))).
    - exact Hm2.
    - apply qeq_imp_qle. ring. }
  apply (Qle_trans (1 - abl9b_ksc m * abl9b_ksc m)
                   (1 + abl9b_ksc m * (abl9b_ksc m * -1))
                   (1 + (abl9b_ksc m * x + abl9b_ksc m * h)
                        * (abl9b_ksc m * x))).
  - apply qeq_imp_qle. ring.
  - apply Qplus_le_compat; [apply Qle_refl | exact Hm3].
Qed.

(* Real 证书：缩放 D_m > 0（见证 (1−k²)/2，N:=0；逐点下界 1−k²>0） *)
Lemma abl9b_sca_Hd : forall (m : nat) (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  real_lt real_zero (real_plus real_one
    (real_mult (real_plus (abl9b_xsc m x) (abl9b_hsc m h))
               (abl9b_xsc m x))).
Proof.
  intros m x h Hx Hxh.
  assert (Hklt : Qlt (abl9b_ksc m * abl9b_ksc m) 1) by apply abl9b_ksc_sq_lt1.
  assert (Hk1p : Qlt 0 (1 - abl9b_ksc m * abl9b_ksc m))
    by (apply (proj1 (Qlt_minus_iff (abl9b_ksc m * abl9b_ksc m) 1)); exact Hklt).
  exists (Qmult (1 - abl9b_ksc m * abl9b_ksc m) (Qinv 2)). split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (1 - abl9b_ksc m * abl9b_ksc m) (Qinv 2)).
    + exact Hk1p.
    + apply Qinv_lt_0_compat. unfold Qlt. simpl. lia.
  - exists 0%nat. intros n Hn.
    assert (HD : projT1 (real_plus real_one
                  (real_mult (real_plus (abl9b_xsc m x) (abl9b_hsc m h))
                             (abl9b_xsc m x))) n
                  - projT1 real_zero n
                  == 1 + (abl9b_ksc m * projT1 x n + abl9b_ksc m * projT1 h n)
                         * (abl9b_ksc m * projT1 x n)).
    { rewrite (real_plus_proj real_one
                 (real_mult (real_plus (abl9b_xsc m x) (abl9b_hsc m h))
                            (abl9b_xsc m x)) n).
      rewrite (real_mult_proj (real_plus (abl9b_xsc m x) (abl9b_hsc m h))
                              (abl9b_xsc m x) n).
      rewrite (real_plus_proj (abl9b_xsc m x) (abl9b_hsc m h) n).
      rewrite (abl9b_xsc_proj m x n). rewrite (abl9b_xsc_proj m h n).
      rewrite (b3r_one_proj n). cbn [projT1 real_zero]. ring. }
    assert (Hpt : Qle (1 - abl9b_ksc m * abl9b_ksc m)
                      (1 + (abl9b_ksc m * projT1 x n + abl9b_ksc m * projT1 h n)
                           * (abl9b_ksc m * projT1 x n))).
    { apply (abl9b_D_sca_q m).
      - apply QleT'_to_Qle. apply (Hx n).
      - rewrite <- (real_plus_proj x h n). apply QleT'_to_Qle. apply (Hxh n). }
    assert (Hhalf : Qlt (Qmult (1 - abl9b_ksc m * abl9b_ksc m) (Qinv 2))
                        (1 - abl9b_ksc m * abl9b_ksc m)).
    { assert (H2 : Qlt (Qinv 2) 1) by (unfold Qlt; simpl; lia).
      pose proof (Qmult_lt_compat_r (Qinv 2) 1
                    (1 - abl9b_ksc m * abl9b_ksc m) Hk1p H2) as Hc.
      apply (abl9_Qlt_transfer_l
               (Qmult (Qinv 2) (1 - abl9b_ksc m * abl9b_ksc m))
               (Qmult (1 - abl9b_ksc m * abl9b_ksc m) (Qinv 2))
               (1 - abl9b_ksc m * abl9b_ksc m)).
      - ring.
      - apply (Qlt_le_trans
                 (Qmult (Qinv 2) (1 - abl9b_ksc m * abl9b_ksc m))
                 (Qmult 1 (1 - abl9b_ksc m * abl9b_ksc m))
                 (1 - abl9b_ksc m * abl9b_ksc m)).
        + exact Hc.
        + apply qeq_imp_qle. ring. }
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (Qmult (1 - abl9b_ksc m * abl9b_ksc m) (Qinv 2))
                        (1 - abl9b_ksc m * abl9b_ksc m)
                        (projT1 (real_plus real_one
                           (real_mult (real_plus (abl9b_xsc m x)
                                                 (abl9b_hsc m h))
                                      (abl9b_xsc m x))) n
                         - projT1 real_zero n)).
    + exact Hhalf.
    + rewrite HD. exact Hpt.
Qed.

(* ============================================================ *)
(* §4·phi 链步界引擎·ρ 参数化（定量望远镜全案的参数化实施）             *)
(* ============================================================ *)

(* 乘积下界基建：|a|≤r、|b|≤1 ⟹ −r ≤ a·b（1+uv 与 1+(u+s)v 正性基础） *)
Lemma abl9b_q_mul_low : forall r a b : Q,
  Qle (Qabs a) r -> Qle (Qabs b) 1 -> Qle (- r) (a * b).
Proof.
  intros r a b Ha Hb.
  assert (Hab : Qle (Qabs (a * b)) r).
  { apply (Qle_trans (Qabs (a * b)) (r * 1) r).
    - rewrite Qabs_Qmult.
      apply (Qmult_le_compat_nonneg (Qabs a) r (Qabs b) 1).
      + split; [apply Qabs_nonneg | exact Ha].
      + split; [apply Qabs_nonneg | exact Hb].
    - apply qeq_imp_qle. ring. }
  apply (Qle_trans (- r) (-(Qabs (a * b))) (a * b)).
  - exact (Qopp_le_compat (Qabs (a * b)) r Hab).
  - destruct (proj1 (Qabs_Qle_condition (a * b) (Qabs (a * b)))
                (Qle_refl (Qabs (a * b)))) as [Hl _].
    exact Hl.
Qed.

(* dw·inv(1+w²) 的对齐件（wsq 环等+wincr 除法恒等经 field 收束；
   侧条件四非零：D1、D2、1+u²、1+v²） *)
Lemma abl9b_dwinv_align : forall u s v w dw : Q,
  ~ (1 + (u + s) * v == 0) -> ~ (1 + u * v == 0) ->
  w == (u - v) * Qinv (1 + u * v) ->
  dw == (u + s - v) * Qinv (1 + (u + s) * v) - w ->
  dw * Qinv (1 + w * w)
  == (s * (1 + v * v) * Qinv (1 + (u + s) * v) * Qinv (1 + u * v))
     * ((1 + u * v) * (1 + u * v)
        * Qinv ((1 + u * u) * (1 + v * v))).
Proof.
  intros u s v w dw Hnz1 Hnz2 Hwe Hdwe.
  rewrite Hdwe. rewrite Hwe.
  field.
  repeat split.
  - apply abl9_q_pos_sq.
  - apply abl9_q_pos_sq.
  - exact Hnz2.
  - exact Hnz1.
  - intro Hz.
    pose proof (abl9_wsq_ring_id u v) as Hid.
    assert (Hprod : (1 + u * u) * (1 + v * v) == 0).
    { rewrite <- Hid. exact Hz. }
    destruct (Qmult_integral (1 + u * u) (1 + v * v) Hprod) as [Hc | Hc].
    + exact (abl9_q_pos_sq u Hc).
    + exact (abl9_q_pos_sq v Hc).
Qed.

(* 余项 ρ 参数化界：|s²v·inv(D1·A)| ≤ inv(1−rho)·s²
   （固定 (8/3)|s|² 的 rho 参化替代；1+u² ≥ 1、1+(u+s)v ≥ 1−rho） *)
Lemma abl9b_rem_bnd : forall (rho u s v : Q),
  Qle 0 rho -> Qlt rho 1 ->
  Qle (Qabs u) rho -> Qle (Qabs (u + s)) rho -> Qle (Qabs v) 1 ->
  Qle (Qabs (s * s * v * Qinv ((1 + (u + s) * v) * (1 + u * u))))
      (Qinv (1 - rho) * (s * s)).
Proof.
  intros rho u s v Hr0 Hr1 Hu Hus Hv.
  assert (H1mr : Qlt 0 (1 - rho))
    by (apply (proj1 (Qlt_minus_iff rho 1)); exact Hr1).
  assert (Hmul1 := abl9b_q_mul_low rho (u + s) v Hus Hv).
  assert (Hmul2 := abl9b_q_mul_low rho u v Hu Hv).
  assert (Hd1 : Qle (1 - rho) (1 + (u + s) * v))
    by (apply Qplus_le_compat; [apply Qle_refl | exact Hmul1]).
  assert (Hd2 : Qle (1 - rho) (1 + u * v))
    by (apply Qplus_le_compat; [apply Qle_refl | exact Hmul2]).
  assert (HA : Qle 1 (1 + u * u)).
  { apply (Qle_trans 1 (1 + 0) (1 + u * u)).
    - apply qeq_imp_qle. ring.
    - apply Qplus_le_compat; [apply Qle_refl | apply Qsquare_nonneg]. }
  assert (HposD : Qlt 0 ((1 + (u + s) * v) * (1 + u * u))).
  { apply (Qmult_lt_0_compat (1 + (u + s) * v) (1 + u * u)).
    - apply (Qlt_le_trans 0 (1 - rho) (1 + (u + s) * v)); [exact H1mr | exact Hd1].
    - apply (Qlt_le_trans 0 1 (1 + u * u)).
      + unfold Qlt. simpl. lia.
      + exact HA. }
  assert (Hinvpos : Qabs (Qinv ((1 + (u + s) * v) * (1 + u * u)))
                    == Qinv ((1 + (u + s) * v) * (1 + u * u))).
  { apply (Qabs_pos (Qinv ((1 + (u + s) * v) * (1 + u * u)))).
    apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HposD. }
  assert (Habsform : Qabs (s * s * v * Qinv ((1 + (u + s) * v) * (1 + u * u)))
                     == Qabs s * Qabs s * Qabs v
                        * Qinv ((1 + (u + s) * v) * (1 + u * u))).
  { rewrite Qabs_Qmult. rewrite Hinvpos. rewrite !Qabs_Qmult. reflexivity. }
  assert (Habss : Qabs s * Qabs s == s * s) by apply abl9b_q_abs_sq.
  assert (Hinvbnd : Qle (Qinv ((1 + (u + s) * v) * (1 + u * u)))
                        (Qinv (1 - rho))).
  { apply (Qle_trans (Qinv ((1 + (u + s) * v) * (1 + u * u)))
                     (1 * Qinv ((1 + (u + s) * v) * (1 + u * u)))
                     (Qinv (1 - rho))).
    - apply qeq_imp_qle. ring.
    - assert (Hpre3 : Qle (1 * (1 - rho))
                          ((1 + (u + s) * v) * (1 + u * u))).
      { apply (Qle_trans (1 * (1 - rho)) (1 + (u + s) * v)
                           ((1 + (u + s) * v) * (1 + u * u))).
        - apply (Qle_trans (1 * (1 - rho)) (1 - rho) (1 + (u + s) * v)).
          + apply qeq_imp_qle. ring.
          + exact Hd1.
        - assert (HD1pos : Qle 0 (1 + (u + s) * v)).
          { apply (Qle_trans 0 (1 - rho) (1 + (u + s) * v));
              [apply Qlt_le_weak; exact H1mr | exact Hd1]. }
          apply (Qle_trans (1 + (u + s) * v)
                           ((1 + (u + s) * v) * 1)
                           ((1 + (u + s) * v) * (1 + u * u))).
          + apply qeq_imp_qle. ring.
          + exact (b3_qmult_le_l 1 (1 + u * u) (1 + (u + s) * v)
                     HD1pos HA). }
      exact (b5n_xinv_le 1 ((1 + (u + s) * v) * (1 + u * u)) (1 - rho)
               HposD H1mr Hpre3). }
  rewrite Habsform.
  apply (Qle_trans (Qabs s * Qabs s * Qabs v
                    * Qinv ((1 + (u + s) * v) * (1 + u * u)))
                   (s * s * Qinv (1 - rho))
                   (Qinv (1 - rho) * (s * s))).
  - apply (Qmult_le_compat_nonneg
             (Qabs s * Qabs s * Qabs v) (s * s)
             (Qinv ((1 + (u + s) * v) * (1 + u * u))) (Qinv (1 - rho))).
    + split.
      * apply (Qmult_le_0_compat (Qabs s * Qabs s) (Qabs v)).
        -- apply (Qmult_le_0_compat (Qabs s) (Qabs s));
             apply Qabs_nonneg.
        -- apply Qabs_nonneg.
      * apply (Qle_trans (Qabs s * Qabs s * Qabs v)
                         (Qabs s * Qabs s * 1) (s * s)).
        -- exact (b3_qmult_le_l (Qabs v) 1 (Qabs s * Qabs s)
                    (Qmult_le_0_compat (Qabs s) (Qabs s)
                       (Qabs_nonneg s) (Qabs_nonneg s)) Hv).
        -- apply qeq_imp_qle. rewrite Habss. ring.
    + split.
      * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HposD.
      * exact Hinvbnd.
  - apply qeq_imp_qle. ring.
Qed.

(* 加法重结合：a+(b+c) ≤ d1+(d2+d3) ⟹ (a+b)+c ≤ d1+d2+d3 *)
Lemma abl9b_qplus_reassoc : forall a b c d1 d2 d3 : Q,
  a + (b + c) <= d1 + (d2 + d3) -> (a + b) + c <= d1 + d2 + d3.
Proof.
  intros a b c d1 d2 d3 H.
  apply (Qle_trans ((a + b) + c) (a + (b + c)) (d1 + d2 + d3)).
  - apply qeq_imp_qle. ring.
  - apply (Qle_trans (a + (b + c)) (d1 + (d2 + d3)) (d1 + d2 + d3)).
    + exact H.
    + apply qeq_imp_qle. ring.
Qed.

(* 三角辅助引理：|A−B+R| ≤ |A|+|B|+|R|（Qabs_triangle 两级+Qabs_opp 配平）  *)
Lemma abl9b_qabs3 : forall A B R : Q,
  Qle (Qabs (A - B + R)) (Qabs A + Qabs B + Qabs R).
Proof.
  intros A B R.
  apply (Qle_trans (Qabs (A - B + R)) (Qabs (A - B) + Qabs R)
                   (Qabs A + Qabs B + Qabs R)).
  - apply Qabs_triangle.
  - apply Qplus_le_compat.
    + apply (Qle_trans (Qabs (A - B)) (Qabs A + Qabs (- B)) (Qabs A + Qabs B)).
      * exact (Qabs_triangle A (- B)).
      * apply Qplus_le_compat; [apply Qle_refl | apply qeq_imp_qle].
        apply Qabs_opp.
    + apply Qle_refl.
Qed.

(* ============================================================ *)
(* 主件·phi 链点形步界（ρ 参数化；固定 (8/3)|s|² 与                    *)
(* ①b 实例两枚固定内界 rho:=1/2、rw:=3/4 的全参化替代）：             *)
(*   u 侧 ①b 前提 |u|,|u+s|≤rho<1、|s|≤(1−rho)/2（b3rr_core_r 直接引用）； *)
(*   w 侧 ①b 前提 |w|,|w+dw|≤rw<1、|dw|≤(1−rw)/2（同）；              *)
(*   斜率恒等残项 R:=s²v·inv(D1·A) 经 abl9b_dwinv_align+abl9_slope_pt  *)
(*   恰等衔接，界由 abl9b_rem_bnd 给 inv(1−rho)·s²。下游以 rho:=rho_m  *)
(*   （缩放内界参）、rw:=3/4（clamp-3/4 全域证书）实例直接使用。       *)
(* ============================================================ *)
Lemma abl9b_phistep_rho :
  forall (rho rw u s v w dw : Q) (n : nat),
  Qle 0 rho -> Qlt rho 1 -> Qle 0 rw -> Qlt rw 1 ->
  Qle (Qabs u) rho -> Qle (Qabs (u + s)) rho ->
  Qle (Qabs s) ((1#2) * (1 - rho)) ->
  Qle (Qabs v) 1 ->
  w == (u - v) * Qinv (1 + u * v) ->
  dw == (u + s - v) * Qinv (1 + (u + s) * v) - w ->
  Qle (Qabs w) rw -> Qle (Qabs (w + dw)) rw ->
  Qle (Qabs dw) ((1#2) * (1 - rw)) ->
  Qle (Qabs (arctan_partial n (u + s) - arctan_partial n u
             - (arctan_partial n (w + dw) - arctan_partial n w)))
      (b3rr_C2 ((1#2) * (1 + rho)) * (Qabs s * Qabs s)
       + Qabs s * q_pow rho (2 * Datatypes.S n)
       + b3rr_C2 ((1#2) * (1 + rw)) * (Qabs dw * Qabs dw)
       + Qabs dw * q_pow rw (2 * Datatypes.S n)
       + Qinv (1 - rho) * (s * s))%Q.
Proof.
  intros rho rw u s v w dw n Hr0 Hr1 Hw0 Hw1 Hu Hus Hss Hv Hwe Hdwe Hwr Hwrp Hdwb.
  assert (H1mr : Qlt 0 (1 - rho))
    by (apply (proj1 (Qlt_minus_iff rho 1)); exact Hr1).
  assert (Hpos1 : Qlt 0 (1 + (u + s) * v)).
  { apply (Qlt_le_trans 0 (1 - rho) (1 + (u + s) * v)).
    - exact H1mr.
    - apply Qplus_le_compat;
        [apply Qle_refl | exact (abl9b_q_mul_low rho (u + s) v Hus Hv)]. }
  assert (Hpos2 : Qlt 0 (1 + u * v)).
  { apply (Qlt_le_trans 0 (1 - rho) (1 + u * v)).
    - exact H1mr.
    - apply Qplus_le_compat;
        [apply Qle_refl | exact (abl9b_q_mul_low rho u v Hu Hv)]. }
  assert (Hnz1 : ~ (1 + (u + s) * v == 0)).
  { intro Hz. apply (Qlt_not_eq 0 (1 + (u + s) * v) Hpos1).
    apply Qeq_sym. exact Hz. }
  assert (Hnz2 : ~ (1 + u * v == 0)).
  { intro Hz. apply (Qlt_not_eq 0 (1 + u * v) Hpos2).
    apply Qeq_sym. exact Hz. }
  pose proof (abl9_slope_pt u v s Hpos1 Hpos2) as Hsp.
  pose proof (abl9b_dwinv_align u s v w dw Hnz1 Hnz2 Hwe Hdwe) as Halign.
  assert (Hsp2 : s * Qinv (1 + u * u) - dw * Qinv (1 + w * w)
                 == s * s * v * Qinv ((1 + (u + s) * v) * (1 + u * u))).
  { rewrite Halign. exact Hsp. }
  assert (Hdec : arctan_partial n (u + s) - arctan_partial n u
                 - (arctan_partial n (w + dw) - arctan_partial n w)
                 == (arctan_partial n (u + s) - arctan_partial n u
                     - s * Qinv (1 + u * u))
                    - (arctan_partial n (w + dw) - arctan_partial n w
                       - dw * Qinv (1 + w * w))
                    + (s * Qinv (1 + u * u) - dw * Qinv (1 + w * w)))
    by ring.
  assert (Htri : Qle (Qabs (arctan_partial n (u + s) - arctan_partial n u
                              - (arctan_partial n (w + dw)
                                 - arctan_partial n w)))
                     (Qabs (arctan_partial n (u + s) - arctan_partial n u
                            - s * Qinv (1 + u * u))
                      + Qabs (arctan_partial n (w + dw)
                              - arctan_partial n w
                              - dw * Qinv (1 + w * w))
                      + Qabs (s * s * v
                              * Qinv ((1 + (u + s) * v) * (1 + u * u))))).
  { rewrite Hdec. rewrite Hsp2.
    apply (abl9b_qabs3
             (arctan_partial n (u + s) - arctan_partial n u
              - s * Qinv (1 + u * u))
             (arctan_partial n (w + dw) - arctan_partial n w
              - dw * Qinv (1 + w * w))
             (s * s * v * Qinv ((1 + (u + s) * v) * (1 + u * u)))). }
  pose proof (b3rr_core_r n u s rho Hr0 Hr1 Hu Hss) as Hb1.
  pose proof (b3rr_core_r n w dw rw Hw0 Hw1 Hwr Hdwb) as Hb2.
  pose proof (abl9b_rem_bnd rho u s v Hr0 Hr1 Hu Hus Hv) as Hrem.
  apply (Qle_trans
           (Qabs (arctan_partial n (u + s) - arctan_partial n u
                  - (arctan_partial n (w + dw) - arctan_partial n w)))
           (Qabs (arctan_partial n (u + s) - arctan_partial n u
                  - s * Qinv (1 + u * u))
            + Qabs (arctan_partial n (w + dw) - arctan_partial n w
                    - dw * Qinv (1 + w * w))
            + Qabs (s * s * v
                    * Qinv ((1 + (u + s) * v) * (1 + u * u))))
           (b3rr_C2 ((1#2) * (1 + rho)) * (Qabs s * Qabs s)
            + Qabs s * q_pow rho (2 * Datatypes.S n)
            + b3rr_C2 ((1#2) * (1 + rw)) * (Qabs dw * Qabs dw)
            + Qabs dw * q_pow rw (2 * Datatypes.S n)
            + Qinv (1 - rho) * (s * s))).
  - exact Htri.
  - apply (Qle_trans
             (Qabs (arctan_partial n (u + s) - arctan_partial n u
                    - s * Qinv (1 + u * u))
              + Qabs (arctan_partial n (w + dw) - arctan_partial n w
                      - dw * Qinv (1 + w * w))
              + Qabs (s * s * v
                      * Qinv ((1 + (u + s) * v) * (1 + u * u))))
             (b3rr_C2 ((1#2) * (1 + rho)) * (Qabs s * Qabs s)
              + Qabs s * q_pow rho (2 * Datatypes.S n)
              + (b3rr_C2 ((1#2) * (1 + rw)) * (Qabs dw * Qabs dw)
                 + Qabs dw * q_pow rw (2 * Datatypes.S n)
                 + Qinv (1 - rho) * (s * s)))
             (b3rr_C2 ((1#2) * (1 + rho)) * (Qabs s * Qabs s)
              + Qabs s * q_pow rho (2 * Datatypes.S n)
              + b3rr_C2 ((1#2) * (1 + rw)) * (Qabs dw * Qabs dw)
              + Qabs dw * q_pow rw (2 * Datatypes.S n)
              + Qinv (1 - rho) * (s * s))).
    + (* 配平：右结合中项和 ≤ 右结合终项（Qplus_le_compat 两级嵌套） *)
      assert (Hpair : Qabs (arctan_partial n (u + s) - arctan_partial n u
                            - s * Qinv (1 + u * u))
                      + (Qabs (arctan_partial n (w + dw)
                               - arctan_partial n w
                               - dw * Qinv (1 + w * w))
                        + Qabs (s * s * v
                                * Qinv ((1 + (u + s) * v) * (1 + u * u))))
                      <= b3rr_C2 ((1#2) * (1 + rho)) * (Qabs s * Qabs s)
                         + Qabs s * q_pow rho (2 * Datatypes.S n)
                         + (b3rr_C2 ((1#2) * (1 + rw)) * (Qabs dw * Qabs dw)
                            + Qabs dw * q_pow rw (2 * Datatypes.S n)
                            + Qinv (1 - rho) * (s * s))).
      { apply Qplus_le_compat.
        - exact Hb1.
        - apply Qplus_le_compat; [exact Hb2 | exact Hrem]. }
      apply (Qle_trans
               (Qabs (arctan_partial n (u + s) - arctan_partial n u
                      - s * Qinv (1 + u * u))
                + Qabs (arctan_partial n (w + dw) - arctan_partial n w
                        - dw * Qinv (1 + w * w))
                + Qabs (s * s * v
                        * Qinv ((1 + (u + s) * v) * (1 + u * u))))
               (Qabs (arctan_partial n (u + s) - arctan_partial n u
                      - s * Qinv (1 + u * u))
                + (Qabs (arctan_partial n (w + dw) - arctan_partial n w
                         - dw * Qinv (1 + w * w))
                  + Qabs (s * s * v
                          * Qinv ((1 + (u + s) * v) * (1 + u * u)))))
               (b3rr_C2 ((1#2) * (1 + rho)) * (Qabs s * Qabs s)
                + Qabs s * q_pow rho (2 * Datatypes.S n)
                + (b3rr_C2 ((1#2) * (1 + rw)) * (Qabs dw * Qabs dw)
                   + Qabs dw * q_pow rw (2 * Datatypes.S n)
                   + Qinv (1 - rho) * (s * s)))).
      * apply qeq_imp_qle. ring.
      * exact Hpair.
    + apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                          *)
(*   Lemma 名清单 = Qed 计数 = PA 语句数，零差；Extraction 判据       *)
(*   Obj.magic 计 0。                                                *)
(* ============================================================ *)
Print Assumptions abl9b_zpos_succ.
Print Assumptions abl9b_zpos_twice.
Print Assumptions abl9b_qmax_mono.
Print Assumptions abl9b_qmax_mono2.
Print Assumptions abl9b_qmin_mono.
Print Assumptions abl9b_qmin_mono2.
Print Assumptions abl9b_qminus_le.
Print Assumptions abl9b_q_self_plus_le.
Print Assumptions abl9b_q_abs_minus.
Print Assumptions abl9b_q_abs_sq.
Print Assumptions abl9b_ksc_parts.
Print Assumptions abl9b_rhom_parts.
Print Assumptions abl9b_q0_parts.
Print Assumptions abl9b_q1_parts.
Print Assumptions abl9b_ksc0.
Print Assumptions abl9b_ksc1.
Print Assumptions abl9b_rhom0.
Print Assumptions abl9b_rhom_lt1.
Print Assumptions abl9b_ksc_le_rhom.
Print Assumptions abl9b_ksc_sq_lt1.
Print Assumptions abl9b_q_clamp34_bnd.
Print Assumptions abl9b_q_clamp34_id.
Print Assumptions abl9b_q_clamp_le_add.
Print Assumptions abl9b_q_clamp_lip.
Print Assumptions abl9b_w_clamp34_dom.
Print Assumptions abl9b_wc34_id_pt.
Print Assumptions abl9b_wc34_w_real_eq.
Print Assumptions abl9b_xsc_proj.
Print Assumptions abl9b_sca_path_q.
Print Assumptions abl9b_sca_path_bnd.
Print Assumptions abl9b_sca_Hu.
Print Assumptions abl9b_sca_Huh.
Print Assumptions abl9b_sca_Hh4.
Print Assumptions abl9b_D_sca_q.
Print Assumptions abl9b_sca_Hd.
Print Assumptions abl9b_q_mul_low.
Print Assumptions abl9b_dwinv_align.
Print Assumptions abl9b_rem_bnd.
Print Assumptions abl9b_qplus_reassoc.
Print Assumptions abl9b_qabs3.
Print Assumptions abl9b_phistep_rho.

(* 提取检验（判据 = 输出 Obj.magic 计 0）：三件均通过（EXIT=0）——
   wc34_w_real_eq（real_eq 尾恒等件）/sca_Hd（D_m 正性证书件）/
   rem_bnd（Qinv 计算件）。abl9b_phistep_rho 系 Prop 顶形（与 S11
   b3rr_core_r、件19 abl9_atan_incr_step_cond 同款），属既定豁免形；
   abl9b_sca_path_bnd 经独立实测任何提取命令形均触 Rocq 9.1 提取器
   prod-Prop 实例化硬错（单抽与两件对抽皆 EXIT=1，独立复核复现），
   该件不设提取判据；其凸性核计算内容由件60 本体提取检验
   （abl9_conv_bnd_pt）覆盖。 *)
Recursive Extraction abl9b_wc34_w_real_eq abl9b_sca_Hd abl9b_rem_bnd.
