(* ==========================================================================)
   abl_arctan_diff_47.v — 9a-乙 主定理装配推进（X47 形：         
   ②Real 桥（X40'' 辖区）+③N 等步链（X41'' 辖区）两续作件的装配衔接）
   消融批 · 落件形态：新件 Require 件19/20/21/40/41（选型说明：         
   件40/41 皆 Require 件20——原地续写件20 将成环 20→40/41→20，故取新件；
   ②产出=件40 abl9_brg_wpath_dom/abl9_wpath_pt_bnd 直耗，③产出=件41
   qs/abl9_walk/abl9_hN_step/abl9_qs_pos 直耗，端点三件=件20 C/A/B/D1 直供）
   ── 本片范围·数学使命（装配推进，≤1h 续作纪律）：──────────────────────────────
   主定理 abl9_atan_diff_formula（件16 拟文）证明链装配：
   phi 逐节点表达式（证书随节点携带）→ 端点 phi(x)==0（件20 C 同构链）→
   N 等步 indexed telescoping（③ 节点族 abl9_walk+qs 剖分）→ 项级转移
   （②域证书：件40abl9_brg_wpath_dom 主形直接匹配）→ 移项闭合=装配版主定理
   abl9_atan_diff_formula_asem；拟文 RHS 形（real_inv_pos·h）经
   abl9_arctan_wd_real 对齐=abl9_atan_diff_formula_inv（件20 B 使用位）。
   装配域（E12 勘定·收紧）：Hh4 取逐点∀n|h_n|≤1/4（X19' 登记册 §四·1 尾
   「装配域陈述收紧」方案落地）——real_lt 形 Hh4 下拟文域证书 ∀n|W_n|≤1
   不成立（早段 |h_n| 无界×Qinv(D_N0) 常数有界 ⟹ |W_n| 无界），收紧系
   证书形态所系非可选。
   构造性（工法核心·零见证纪律）：全部real_lt 正性证书经透明Definition
   abl9_poswit 构造（见证恒 (1#2, 0%nat)——D1 逐点 3/4 下界对全 n 成立，
   eps:=1/2 全程合法）⟹ real_inv_pos 投影恒为 Qinv(D_n)（abl9_poswit_proj
   单发，免早尾两支拆解）；两 w 项（walk-N 形 vs 主形）投影逐点环等可直证。
   单步槽（②使用位）：Hstep 逐节点 real_eq 形——phi 抽象引擎
   （件41 nchain_crit/件20 const_crit 系 phi:Real→Real 抽象形）与「证书随
   节点携带」不相容（E12 判定：cauchy_real_arctan 证书槽依赖实参，无全域
   total 化），装配链走内联 indexed telescoping；le 形单步判据（const_crit
   之 phi-free 化）留②产出片，登记续点。
   ── 依赖清单：──────────────────────────────────────────────────────────────
   S01–S11 全链 + abl_arctan_diff_19 + abl_arctan_diff_20（q_path_den/
   Qabs_wd/arctan_wd_real 等）+ abl_arctan_cert_bridge_21（w 承载）+
   abl_arctan_diff_40（abl9_wpath_pt_bnd/abl9_brg_wpath_dom）+
   abl_arctan_diff_41（qs/abl9_walk/abl9_hN_step/abl9_qs_pos）。
   Require 链退回 S11 单链，S12 出锥（承前判定）。
   ── 编译配方：──────────────────────────────────────────────────────────────
   source Live/toolchain/env.sh && bash cpu_guard.sh --
     rocq c -q -native-compiler no -Q /tmp/x47pool "" /tmp/x47pool/abl_arctan_diff_47.v
   （隔离池 /tmp/x47pool=/tmp/x40pool 真拷+件41 .v/.vo（md5 对账 SAME：
   件20 d8111457/件21 c4fdf205/件40 8499f3a9/件41 d79588d5 与落件逐一 SAME；
   S11 冻结链 d571b0c0 v/vo 同 mtime 成对与 x40/x41 同构）；cwd=/tmp/x47w
   异地空目录——承 X19'' 殁因勘定；发起前 rocq 进程 <3，窗满候窗禁硬闯。）
   ========================================================================== *)
(* 【陈旧申报勘注（abl9 陈旧申报勘注补录组）】主式 abl9_atan_diff_formula 已由 abl9_atan_diff_a2_56.v L1871–2364 A2 形零前件闭合（闭合日期见注册册字段行；PA 全 Closed、件58 L231–232 活码使用、A2B3 决议136 在役）；本处系闭合当日之前陈旧申报，照录留痕禁删除；定论=abl9 主式深勘报告 §一。本件 asem/inv 装配变体仍在役可引用（abl9 主式深勘报告 §二.D），系推进中间态登记，非开口槽。 *)

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
Require Import abl_arctan_cert_bridge_21.
Require Import abl_arctan_diff_40.
Require Import abl_arctan_diff_41.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* 【Q1】qs 单调（k ≤ N ⟹ qs k ≤ qs N）——剖分分子界之基。            *)
(* ============================================================ *)
Lemma abl9_qs_mono : forall k N : nat, (k <= N)%nat -> Qle (qs k) (qs N).
Proof.
  intros k N. revert N.
  induction k as [| j IHj]; intros N Hk.
  - destruct N as [| m].
    + apply Qle_refl.
    + apply Qlt_le_weak. apply abl9_qs_pos. lia.
  - destruct N as [| m]. { lia. }
    cbn [qs].
    apply Qplus_le_compat.
    + apply IHj. lia.
    + apply Qle_refl.
Qed.

(* ============================================================ *)
(* 【Q2】剖分比率 λ := qs k / qs N ∈ [0,1]（z := qs N 正性）。        *)
(* ============================================================ *)
Lemma abl9_qs_ratio_bnd : forall k N : nat,
  (1 <= N)%nat -> (k <= N)%nat ->
  Qle 0 (qs k / qs N)%Q /\ Qle (qs k / qs N)%Q 1.
Proof.
  intros k N HN Hk.
  assert (Hz0 : Qlt 0 (qs N)) by (apply abl9_qs_pos; exact HN).
  assert (HzN0 : ~ (qs N == 0)%Q).
  { intros H0.
    assert (Hle : Qle (qs N) 0) by (apply qeq_imp_qle; exact H0).
    exact (Qlt_not_le 0 (qs N) Hz0 Hle). }
  assert (Hk0 : Qle 0 (qs k)).
  { destruct k as [| j].
    - apply Qle_refl.
    - apply Qlt_le_weak. apply abl9_qs_pos. lia. }
  split.
  - unfold Qdiv. apply Qmult_le_0_compat.
    + exact Hk0.
    + apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hz0.
  - unfold Qdiv.
    apply (Qle_trans (qs k * Qinv (qs N)) (qs N * Qinv (qs N)) 1).
    + apply Qmult_le_compat_r.
      * apply abl9_qs_mono. exact Hk.
      * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hz0.
    + apply qeq_imp_qle. apply Qmult_inv_r. exact HzN0.
Qed.

(* ============================================================ *)
(* 【Q3】凸组合绝对值界：0≤λ≤1、|a|≤1、|b|≤1 ⟹ |(1−λ)a+λb| ≤ 1。      *)
(*   （路径域证书算术核：x_n+λh_n = (1−λ)x_n+λ(x_n+h_n) 凸组合。）      *)
(* ============================================================ *)
Lemma abl9_q_convex_abs : forall l a b : Q,
  Qle 0 l -> Qle l 1 -> Qle (Qabs a) 1 -> Qle (Qabs b) 1 ->
  Qle (Qabs ((1 - l) * a + l * b)) 1.
Proof.
  intros l a b Hl0 Hl1 Ha Hb.
  assert (H0ml : Qle 0 (1 - l)).
  { apply (Qle_trans 0 (1 + -1) (1 - l)).
    - apply qeq_imp_qle. ring.
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply (Qopp_le_compat l 1). exact Hl1. }
  apply (Qle_trans (Qabs ((1 - l) * a + l * b))
                   (Qabs ((1 - l) * a) + Qabs (l * b)) 1).
  - apply Qabs_triangle.
  - apply (Qle_trans (Qabs ((1 - l) * a) + Qabs (l * b))
                     ((1 - l) * Qabs a + l * Qabs b) 1).
    + rewrite Qabs_Qmult. rewrite Qabs_Qmult.
      apply Qplus_le_compat.
      * apply (Qmult_le_compat_r (Qabs (1 - l)) (1 - l) (Qabs a)).
        -- apply (Qle_trans (Qabs (1 - l)) (1 - l) (1 - l)).
           ++ apply abl9_Qabs_le_self. exact H0ml.
           ++ apply Qle_refl.
        -- apply Qabs_nonneg.
      * apply (Qmult_le_compat_r (Qabs l) l (Qabs b)).
        -- apply (Qle_trans (Qabs l) l l).
           ++ apply abl9_Qabs_le_self. exact Hl0.
           ++ apply Qle_refl.
        -- apply Qabs_nonneg.
    + apply (Qle_trans ((1 - l) * Qabs a + l * Qabs b)
                       ((1 - l) * 1 + l * 1) 1).
      * apply Qplus_le_compat.
        -- apply (Qmult_le_compat_nonneg (1 - l) (1 - l) (Qabs a) 1).
           ++ split; [exact H0ml | apply Qle_refl].
           ++ split; [apply Qabs_nonneg | exact Ha].
        -- apply (Qmult_le_compat_nonneg l l (Qabs b) 1).
           ++ split; [exact Hl0 | apply Qle_refl].
           ++ split; [apply Qabs_nonneg | exact Hb].
      * apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* 【Q4】步长缩水：|λ·t| ≤ 1/4（λ ≤ 1、|t| ≤ 1/4）。                  *)
(* ============================================================ *)
Lemma abl9_lam_h_bnd : forall (t : Q) (k N : nat),
  (1 <= N)%nat -> (k <= N)%nat -> Qle (Qabs t) (1 # 4) ->
  Qle (Qabs ((qs k / qs N) * t)) (1 # 4).
Proof.
  intros t k N HN Hk Ht.
  destruct (abl9_qs_ratio_bnd k N HN Hk) as [Hr0 Hr1].
  rewrite Qabs_Qmult.
  apply (Qle_trans (Qabs (qs k / qs N) * Qabs t) (1 * (1 # 4)) (1 # 4)).
  - apply Qmult_le_compat_nonneg.
    + split.
      * apply Qabs_nonneg.
      * apply (Qle_trans (Qabs (qs k / qs N)) (qs k / qs N) 1).
        -- apply abl9_Qabs_le_self. exact Hr0.
        -- exact Hr1.
    + split.
      * apply Qabs_nonneg.
      * exact Ht.
  - apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* 【Q5】剖分步长 Q 点值：qs N·((1#1)/qs N·t) == t（0<qs N）。         *)
(* ============================================================ *)
Lemma abl9_hN_step_scale : forall (N : nat) (t : Q),
  (0 < qs N)%Q -> (qs N * (((1 # 1) / qs N) * t) == t)%Q.
Proof.
  intros N t Hz.
  assert (HzN0 : ~ (qs N == 0)%Q).
  { intros H0.
    assert (Hle : Qle (qs N) 0) by (apply qeq_imp_qle; exact H0).
    exact (Qlt_not_le 0 (qs N) Hz Hle). }
  assert (Hc : (qs N * ((1 # 1) / qs N)%Q == 1)%Q).
  { unfold Qdiv. field. exact HzN0. }
  rewrite Qmult_assoc. rewrite Hc. ring.
Qed.

(* ============================================================ *)
(* 【R1】walk 节点逐点投影：proj(walk b s k)_n == b_n + qs k · s_n。   *)
(* ============================================================ *)
Lemma abl9_walk_proj : forall (b s : Real) (k n : nat),
  projT1 (abl9_walk b s k) n == projT1 b n + qs k * projT1 s n.
Proof.
  intros b s k. induction k as [| j IHj]; intros n.
  - cbn [abl9_walk qs]. ring.
  - cbn [abl9_walk qs].
    rewrite (real_plus_proj (abl9_walk b s j) s n).
    rewrite IHj. ring.
Qed.

(* ============================================================ *)
(* 【R2】walk 节点域证书：|walk x step k| ≤ 1 全 n（凸组合）。          *)
(* ============================================================ *)
Lemma abl9_walk_dom : forall (x h : Real) (N k : nat),
  (1 <= N)%nat -> (k <= N)%nat ->
  (forall n : nat, QleT' (Qabs (projT1 x n)) 1) ->
  (forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4)) ->
  (forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1) ->
  forall n : nat,
  QleT' (Qabs (projT1 (abl9_walk x (abl9_hN_step h (qs N)) k) n)) 1.
Proof.
  intros x h N k HN Hk Hx Hh4 Hxh n.
  destruct (abl9_qs_ratio_bnd k N HN Hk) as [Hr0 Hr1].
  assert (Ew : projT1 (abl9_walk x (abl9_hN_step h (qs N)) k) n
               == projT1 x n + (qs k / qs N) * projT1 h n).
  { rewrite (abl9_walk_proj x (abl9_hN_step h (qs N)) k n).
    unfold abl9_hN_step.
    rewrite (real_mult_proj (real_const ((1 # 1) / qs N)%Q) h n).
    rewrite (real_const_proj ((1 # 1) / qs N)%Q n).
    unfold Qdiv. ring. }
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs (projT1 (abl9_walk x (abl9_hN_step h (qs N)) k) n))
                   (Qabs ((1 - qs k / qs N) * projT1 x n
                          + (qs k / qs N) * projT1 (real_plus x h) n)) 1).
  - apply qeq_imp_qle. apply abl9_Qabs_wd.
    rewrite Ew. rewrite (real_plus_proj x h n). ring.
  - apply (abl9_q_convex_abs (qs k / qs N)).
    + exact Hr0.
    + exact Hr1.
    + exact (QleT'_to_Qle _ _ (Hx n)).
    + exact (QleT'_to_Qle _ _ (Hxh n)).
Qed.

(* ============================================================ *)
(* 【R3】零见证正性证书工装：                                          *)
(*   abl9_poswit=透明构造（见证恒 (1#2, 0%nat)）+ 其投影单发件          *)
(*   （real_inv_pos 投影恒 Qinv(D_n)——早尾两支消解）。                  *)
(* ============================================================ *)
Definition abl9_poswit (D : Real)
  (H : forall n : nat, QltT (1 # 2)%Q (projT1 D n - projT1 real_zero n)) :
  real_lt real_zero D.
Proof.
  unfold real_lt.
  exists (1 # 2)%Q.
  split.
  - reflexivity.
  - exists 0%nat. intros n _. apply H.
Defined.

Lemma abl9_poswit_proj : forall (D : Real)
  (H : forall n : nat, QltT (1 # 2)%Q (projT1 D n - projT1 real_zero n))
  (n : nat),
  projT1 (real_inv_pos D (abl9_poswit D H)) n == Qinv (projT1 D n).
Proof.
  intros D H n.
  unfold abl9_poswit.
  destruct D as [u Hu].
  cbn [projT1 real_inv_pos Nat.leb].
  reflexivity.
Qed.

(* ============================================================ *)
(* 【R4】主正性证书（装配版）：0 < 1+(x+h)·x——逐点 D1 直证。           *)
(* ============================================================ *)
Lemma abl9_posmain_pt : forall (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4)) (n : nat),
  QltT (1 # 2)%Q
    (projT1 (real_plus real_one (real_mult (real_plus x h) x)) n
     - projT1 real_zero n).
Proof.
  intros x h Hx Hh4 n.
  apply Qlt_to_QltT.
  apply (abl9_Qlt_transfer_r (1 # 2)
           (1 + (projT1 x n + projT1 h n) * projT1 x n - 0)
           (projT1 (real_plus real_one (real_mult (real_plus x h) x)) n
            - projT1 real_zero n)).
  - rewrite (real_plus_proj real_one (real_mult (real_plus x h) x) n).
    rewrite (b3r_one_proj n).
    rewrite (real_mult_proj (real_plus x h) x n).
    rewrite (real_plus_proj x h n).
    cbn [projT1 real_zero].
    reflexivity.
  - apply (Qlt_le_trans (1 # 2) (3 # 4)
             (1 + (projT1 x n + projT1 h n) * projT1 x n - 0)).
    + unfold Qlt. simpl. lia.
    + apply (Qle_trans (3 # 4)
               (1 + (projT1 x n + projT1 h n) * projT1 x n)
               (1 + (projT1 x n + projT1 h n) * projT1 x n - 0)).
      * apply QleT'_to_Qle.
        apply abl9_q_path_den.
        -- exact (QleT'_to_Qle _ _ (Hx n)).
        -- exact (QleT'_to_Qle _ _ (Hh4 n)).
      * apply qeq_imp_qle. ring.
Qed.

Definition abl9_asem_pos_main (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4)) :
  real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x)) :=
  abl9_poswit (real_plus real_one (real_mult (real_plus x h) x))
              (abl9_posmain_pt x h Hx Hh4).

(* ============================================================ *)
(* 【R5】walk 节点正性证书：0 < 1+(walk k)·x——D1 于 (x_n, λh_n)。      *)
(* ============================================================ *)
Lemma abl9_walkpos_pt : forall (x h : Real) (N k : nat),
  (1 <= N)%nat -> (k <= N)%nat ->
  (forall n : nat, QleT' (Qabs (projT1 x n)) 1) ->
  (forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4)) ->
  forall n : nat,
  QltT (1 # 2)%Q
    (projT1 (real_plus real_one
               (real_mult (abl9_walk x (abl9_hN_step h (qs N)) k) x)) n
     - projT1 real_zero n).
Proof.
  intros x h N k HN Hk Hx Hh4 n.
  assert (Ew : projT1 (abl9_walk x (abl9_hN_step h (qs N)) k) n
               == projT1 x n + (qs k / qs N) * projT1 h n).
  { rewrite (abl9_walk_proj x (abl9_hN_step h (qs N)) k n).
    unfold abl9_hN_step.
    rewrite (real_mult_proj (real_const ((1 # 1) / qs N)%Q) h n).
    rewrite (real_const_proj ((1 # 1) / qs N)%Q n).
    unfold Qdiv. ring. }
  apply Qlt_to_QltT.
  apply (abl9_Qlt_transfer_r (1 # 2)
           (1 + (projT1 x n + (qs k / qs N) * projT1 h n) * projT1 x n - 0)
           (projT1 (real_plus real_one
                      (real_mult (abl9_walk x (abl9_hN_step h (qs N)) k) x)) n
            - projT1 real_zero n)).
  - rewrite (real_plus_proj real_one
               (real_mult (abl9_walk x (abl9_hN_step h (qs N)) k) x) n).
    rewrite (b3r_one_proj n).
    rewrite (real_mult_proj (abl9_walk x (abl9_hN_step h (qs N)) k) x n).
    rewrite Ew.
    cbn [projT1 real_zero].
    reflexivity.
  - apply (Qlt_le_trans (1 # 2) (3 # 4)
             (1 + (projT1 x n + (qs k / qs N) * projT1 h n) * projT1 x n - 0)).
    + unfold Qlt. simpl. lia.
    + apply (Qle_trans (3 # 4)
               (1 + (projT1 x n + (qs k / qs N) * projT1 h n) * projT1 x n)
               (1 + (projT1 x n + (qs k / qs N) * projT1 h n) * projT1 x n - 0)).
      * apply QleT'_to_Qle.
        apply abl9_q_path_den.
        -- exact (QleT'_to_Qle _ _ (Hx n)).
        -- apply abl9_lam_h_bnd.
           ++ exact HN.
           ++ exact Hk.
           ++ exact (QleT'_to_Qle _ _ (Hh4 n)).
      * apply qeq_imp_qle. ring.
Qed.

Definition abl9_walk_pos (x h : Real) (N k : nat)
  (HN : (1 <= N)%nat) (Hk : (k <= N)%nat)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4)) :
  real_lt real_zero
    (real_plus real_one (real_mult (abl9_walk x (abl9_hN_step h (qs N)) k) x)) :=
  abl9_poswit
    (real_plus real_one (real_mult (abl9_walk x (abl9_hN_step h (qs N)) k) x))
    (abl9_walkpos_pt x h N k HN Hk Hx Hh4).

(* ============================================================ *)
(* 【R6】两投影单发件（poswit_proj 的主形/walk 形特化——装配免展开）。  *)
(* ============================================================ *)
Lemma abl9_posmain_proj : forall (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4)) (n : nat),
  projT1 (real_inv_pos (real_plus real_one (real_mult (real_plus x h) x))
                       (abl9_asem_pos_main x h Hx Hh4)) n
  == Qinv (projT1 (real_plus real_one (real_mult (real_plus x h) x)) n).
Proof.
  intros x h Hx Hh4 n.
  unfold abl9_asem_pos_main.
  apply abl9_poswit_proj.
Qed.

Lemma abl9_walkpos_proj : forall (x h : Real) (N k : nat)
  (HN : (1 <= N)%nat) (Hk : (k <= N)%nat)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4)) (n : nat),
  projT1 (real_inv_pos
            (real_plus real_one
               (real_mult (abl9_walk x (abl9_hN_step h (qs N)) k) x))
            (abl9_walk_pos x h N k HN Hk Hx Hh4)) n
  == Qinv (projT1 (real_plus real_one
                     (real_mult (abl9_walk x (abl9_hN_step h (qs N)) k) x)) n).
Proof.
  intros x h N k HN Hk Hx Hh4 n.
  unfold abl9_walk_pos.
  apply abl9_poswit_proj.
Qed.

(* ============================================================ *)
(* 【R7】w 路径域证书（walk 节点形）：|w(walk k)_n| ≤ 1 全 n——          *)
(*   f==λh_n 经 abl9_wpath_pt_bnd（件40）单发。                         *)
(* ============================================================ *)
Lemma abl9_wwalk_dom : forall (x h : Real) (N k : nat)
  (HN : (1 <= N)%nat) (Hk : (k <= N)%nat)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4)),
  forall n : nat,
  QleT' (Qabs (projT1
    (abl9_brg_w_real (abl9_walk x (abl9_hN_step h (qs N)) k) x
                     (abl9_walk_pos x h N k HN Hk Hx Hh4)) n)) 1.
Proof.
  intros x h N k HN Hk Hx Hh4 n.
  assert (Ew : projT1 (abl9_walk x (abl9_hN_step h (qs N)) k) n
               == projT1 x n + (qs k / qs N) * projT1 h n).
  { rewrite (abl9_walk_proj x (abl9_hN_step h (qs N)) k n).
    unfold abl9_hN_step.
    rewrite (real_mult_proj (real_const ((1 # 1) / qs N)%Q) h n).
    rewrite (real_const_proj ((1 # 1) / qs N)%Q n).
    unfold Qdiv. ring. }
  assert (Hb : Qle (Qabs (projT1
    (abl9_brg_w_real (abl9_walk x (abl9_hN_step h (qs N)) k) x
                     (abl9_walk_pos x h N k HN Hk Hx Hh4)) n)) 1).
  { unfold abl9_brg_w_real.
    rewrite (real_mult_proj
               (real_plus (abl9_walk x (abl9_hN_step h (qs N)) k) (real_opp x))
               (real_inv_pos
                  (real_plus real_one
                     (real_mult (abl9_walk x (abl9_hN_step h (qs N)) k) x))
                  (abl9_walk_pos x h N k HN Hk Hx Hh4)) n).
    rewrite (real_plus_proj (abl9_walk x (abl9_hN_step h (qs N)) k)
               (real_opp x) n).
    rewrite (real_opp_proj x n).
    rewrite (abl9_walkpos_proj x h N k HN Hk Hx Hh4 n).
    rewrite (real_plus_proj real_one
               (real_mult (abl9_walk x (abl9_hN_step h (qs N)) k) x) n).
    rewrite (b3r_one_proj n).
    rewrite (real_mult_proj (abl9_walk x (abl9_hN_step h (qs N)) k) x n).
    rewrite Ew.
    apply QleT'_to_Qle.
    apply (abl9_wpath_pt_bnd
             (projT1 x n + (qs k / qs N) * projT1 h n + - projT1 x n)
             (projT1 x n) ((qs k / qs N) * projT1 h n)
             (projT1 x n) ((qs k / qs N) * projT1 h n)).
    - exact (QleT'_to_Qle _ _ (Hx n)).
    - apply abl9_lam_h_bnd.
      + exact HN.
      + exact Hk.
      + exact (QleT'_to_Qle _ _ (Hh4 n)).
    - exact (QleT'_to_Qle _ _ (Hx n)).
    - apply abl9_lam_h_bnd.
      + exact HN.
      + exact Hk.
      + exact (QleT'_to_Qle _ _ (Hh4 n)).
    - ring. }
  apply Qle_to_QleT'. exact Hb.
Qed.

(* ============================================================ *)
(* 【D0】phi 逐节点表达式（装配主链的节点项；证书随节点携带）：         *)
(*   phi_k := A(walk k) − A(x) − A(w(walk k))，A=cauchy_real_arctan。 *)
(* ============================================================ *)
Definition abl9_phi_at (x h : Real) (N : nat)
  (HN : (1 <= N)%nat)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4))
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (k : nat) (Hk : (k <= N)%nat) : Real :=
  real_plus
    (real_plus
       (cauchy_real_arctan (abl9_walk x (abl9_hN_step h (qs N)) k)
                           (abl9_walk_dom x h N k HN Hk Hx Hh4 Hxh))
       (real_opp (cauchy_real_arctan x Hx)))
    (real_opp
       (cauchy_real_arctan
          (abl9_brg_w_real (abl9_walk x (abl9_hN_step h (qs N)) k) x
                           (abl9_walk_pos x h N k HN Hk Hx Hh4))
          (abl9_wwalk_dom x h N k HN Hk Hx Hh4))).

(* ============================================================ *)
(* 【E1】端点件（正则形参数化于 0 节点证明槽 Hk0）：                    *)
(*   A(x)−A(x)−A(w(x)) == 0——real_plus_opp + 件20 C                    *)
(*   （abl9_arctan_zero_pt；w(x) 投影零因子形）。                        *)
(* ============================================================ *)
Lemma abl9_asem_endpoint : forall (x h : Real) (N : nat)
  (HN : (1 <= N)%nat)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4))
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (Hk0 : (0 <= N)%nat),
  real_eq (real_plus
             (real_plus (cauchy_real_arctan x Hx)
                        (real_opp (cauchy_real_arctan x Hx)))
             (real_opp
                (cauchy_real_arctan
                   (abl9_brg_w_real x x
                      (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4))
                   (abl9_wwalk_dom x h N 0%nat HN Hk0 Hx Hh4))))
          real_zero.
Proof.
  intros x h N HN Hx Hh4 Hxh Hk0.
  apply (real_eq_trans
           (real_plus
              (real_plus (cauchy_real_arctan x Hx)
                         (real_opp (cauchy_real_arctan x Hx)))
              (real_opp
                 (cauchy_real_arctan
                    (abl9_brg_w_real x x
                       (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4))
                    (abl9_wwalk_dom x h N 0%nat HN Hk0 Hx Hh4))))
           (real_plus real_zero (real_opp real_zero))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_plus (cauchy_real_arctan x Hx)
                        (real_opp (cauchy_real_arctan x Hx)))
             (real_opp
                (cauchy_real_arctan
                   (abl9_brg_w_real x x
                      (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4))
                   (abl9_wwalk_dom x h N 0%nat HN Hk0 Hx Hh4)))
             real_zero
             (real_opp real_zero)).
    + exact (real_plus_opp (cauchy_real_arctan x Hx)).
    + apply (RealSetoid.real_eq_opp_compat
               (cauchy_real_arctan
                  (abl9_brg_w_real x x
                     (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4))
                  (abl9_wwalk_dom x h N 0%nat HN Hk0 Hx Hh4))
               real_zero).
      * apply (abl9_arctan_zero_pt
                 (abl9_brg_w_real x x
                    (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4))
                 (abl9_wwalk_dom x h N 0%nat HN Hk0 Hx Hh4)).
        intros n.
        unfold abl9_brg_w_real.
        rewrite (real_mult_proj
                   (real_plus x (real_opp x))
                   (real_inv_pos (real_plus real_one (real_mult x x))
                      (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4)) n).
        rewrite (real_plus_proj x (real_opp x) n).
        rewrite (real_opp_proj x n).
        rewrite (abl9_walkpos_proj x h N 0%nat HN Hk0 Hx Hh4 n).
        rewrite (real_plus_proj real_one (real_mult x x) n).
        rewrite (b3r_one_proj n).
        rewrite (real_mult_proj x x n).
        cbn [projT1 real_zero].
        ring.
  - apply real_eq_of_zero_diff. intros n.
    rewrite (real_plus_proj real_zero (real_opp real_zero) n).
    rewrite (real_opp_proj real_zero n).
    cbn [projT1 real_zero].
    ring.
Qed.

(* ============================================================ *)
(* 【M0】移项件：(U−V−W == 0) ⟹ (U−V == W)（real_eq 环律重组）。       *)
(* ============================================================ *)
Lemma abl9_asem_move : forall U V W : Real,
  real_eq (real_plus (real_plus U (real_opp V)) (real_opp W)) real_zero ->
  real_eq (real_plus U (real_opp V)) W.
Proof.
  intros U V W H.
  assert (Hneg : real_eq (real_plus (real_opp W) W) real_zero).
  { apply (real_eq_trans (real_plus (real_opp W) W)
             (real_plus W (real_opp W)) real_zero).
    - apply real_eq_of_zero_diff. intros n.
      rewrite (real_plus_proj (real_opp W) W n).
      rewrite (real_plus_proj W (real_opp W) n).
      rewrite (real_opp_proj W n).
      cbn [projT1 real_zero].
      ring.
    - exact (real_plus_opp W). }
  apply (real_eq_trans (real_plus U (real_opp V))
          (real_plus (real_plus U (real_opp V)) real_zero) W).
  - exact (real_eq_sym (real_plus (real_plus U (real_opp V)) real_zero)
             (real_plus U (real_opp V))
             (real_plus_zero (real_plus U (real_opp V)))).
  - apply (real_eq_trans
             (real_plus (real_plus U (real_opp V)) real_zero)
             (real_plus (real_plus U (real_opp V))
                        (real_plus (real_opp W) W)) W).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus U (real_opp V)) real_zero
               (real_plus U (real_opp V)) (real_plus (real_opp W) W)).
      * apply real_eq_refl.
      * exact (real_eq_sym (real_plus (real_opp W) W) real_zero Hneg).
    + apply (real_eq_trans
               (real_plus (real_plus U (real_opp V))
                          (real_plus (real_opp W) W))
               (real_plus (real_plus (real_plus U (real_opp V)) (real_opp W)) W)
               W).
      * apply real_eq_of_zero_diff. intros n.
        rewrite (real_plus_proj
                   (real_plus (real_plus U (real_opp V)) (real_opp W)) W n).
        rewrite (real_plus_proj (real_plus U (real_opp V)) (real_opp W) n).
        rewrite (real_plus_proj U (real_opp V) n).
        rewrite (real_opp_proj V n).
        rewrite (real_plus_proj (real_plus U (real_opp V))
                   (real_plus (real_opp W) W) n).
        rewrite (real_plus_proj U (real_opp V) n).
        rewrite (real_opp_proj V n).
        rewrite (real_plus_proj (real_opp W) W n).
        rewrite (real_opp_proj W n).
        cbn [projT1].
        ring.
      * apply (real_eq_trans
                 (real_plus (real_plus (real_plus U (real_opp V)) (real_opp W)) W)
                 (real_plus real_zero W) W).
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_plus (real_plus U (real_opp V)) (real_opp W)) W
                     real_zero W).
           ++ exact H.
           ++ apply real_eq_refl.
        -- apply real_eq_of_zero_diff. intros n.
           rewrite (real_plus_proj real_zero W n).
           cbn [projT1 real_zero].
           ring.
Qed.

(* ============================================================ *)
(* 【M2】主定理装配版（装配推进主件）：                                *)
(*   装配域（收紧）：Hx/Hh4/Hxh 逐点形；单步槽 Hstep=phi 逐节点        *)
(*   real_eq（②使用位）；链=indexed telescoping（③：abl9_walk+qs）；   *)
(*   端点=E1；项级转移=件20 A 合同+件40 域证书主形直接匹配；移项=M0。    *)
(* ============================================================ *)
Lemma abl9_atan_diff_formula_asem : forall (x h : Real) (N : nat)
  (HN : (1 <= N)%nat)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4))
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  (forall (i : nat) (Hi : (i < N)%nat),
     real_eq (abl9_phi_at x h N HN Hx Hh4 Hxh (Datatypes.S i) Hi)
             (abl9_phi_at x h N HN Hx Hh4 Hxh i
                (Nat.le_trans i (Datatypes.S i) N (Nat.le_succ_diag_r i) Hi))) ->
  real_eq (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (cauchy_real_arctan x Hx)))
          (cauchy_real_arctan
             (abl9_brg_w_real (real_plus x h) x (abl9_asem_pos_main x h Hx Hh4))
             (abl9_brg_wpath_dom x h
                (abl9_asem_pos_main x h Hx Hh4) Hx Hh4)).
Proof.
  intros x h N HN Hx Hh4 Hxh Hstep.
  assert (HzN0 : ~ (qs N == 0)%Q).
  { intros H0.
    assert (Hlt : Qlt 0 (qs N)) by (apply abl9_qs_pos; exact HN).
    assert (Hle : Qle (qs N) 0) by (apply qeq_imp_qle; exact H0).
    exact (Qlt_not_le 0 (qs N) Hlt Hle). }
  assert (Hscale : forall t : Q,
    (qs N * (((1 # 1) / qs N) * t) == t)%Q)
    by (intros t; apply abl9_hN_step_scale; apply abl9_qs_pos; exact HN).
  (* 链：indexed telescoping（③ 节点族 abl9_walk + qs 剖分）；基座=正则端点形 *)
  assert (Hk0 : (0 <= N)%nat) by (apply Nat.le_0_l).
  assert (Htel : forall (k : nat) (Hk : (k <= N)%nat),
    real_eq (abl9_phi_at x h N HN Hx Hh4 Hxh k Hk)
            (real_plus
               (real_plus (cauchy_real_arctan x Hx)
                          (real_opp (cauchy_real_arctan x Hx)))
               (real_opp
                  (cauchy_real_arctan
                     (abl9_brg_w_real x x
                        (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4))
                     (abl9_wwalk_dom x h N 0%nat HN Hk0 Hx Hh4))))).
  { intro k. induction k as [| j IHj]; intro Hk.
    - (* k=0：A 槽证书差经 abl9_arctan_wd_real（同实参逐点 refl）；w 槽经投影逐点等 *)
      apply (real_eq_trans
               (abl9_phi_at x h N HN Hx Hh4 Hxh 0%nat Hk)
               (real_plus
                  (real_plus
                     (cauchy_real_arctan x
                        (abl9_walk_dom x h N 0%nat HN Hk Hx Hh4 Hxh))
                     (real_opp (cauchy_real_arctan x Hx)))
                  (real_opp
                     (cauchy_real_arctan
                        (abl9_brg_w_real x x
                           (abl9_walk_pos x h N 0%nat HN Hk Hx Hh4))
                        (abl9_wwalk_dom x h N 0%nat HN Hk Hx Hh4))))
               (real_plus
                  (real_plus (cauchy_real_arctan x Hx)
                             (real_opp (cauchy_real_arctan x Hx)))
                  (real_opp
                     (cauchy_real_arctan
                        (abl9_brg_w_real x x
                           (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4))
                        (abl9_wwalk_dom x h N 0%nat HN Hk0 Hx Hh4))))).
      + apply real_eq_refl.
      + apply (RealSetoid.real_eq_plus_compat
                 (real_plus
                    (cauchy_real_arctan x
                       (abl9_walk_dom x h N 0%nat HN Hk Hx Hh4 Hxh))
                    (real_opp (cauchy_real_arctan x Hx)))
                 (real_opp
                    (cauchy_real_arctan
                       (abl9_brg_w_real x x
                          (abl9_walk_pos x h N 0%nat HN Hk Hx Hh4))
                       (abl9_wwalk_dom x h N 0%nat HN Hk Hx Hh4)))
                 (real_plus (cauchy_real_arctan x Hx)
                            (real_opp (cauchy_real_arctan x Hx)))
                 (real_opp
                    (cauchy_real_arctan
                       (abl9_brg_w_real x x
                          (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4))
                       (abl9_wwalk_dom x h N 0%nat HN Hk0 Hx Hh4)))).
        * apply (RealSetoid.real_eq_plus_compat
                   (cauchy_real_arctan x
                      (abl9_walk_dom x h N 0%nat HN Hk Hx Hh4 Hxh))
                   (real_opp (cauchy_real_arctan x Hx))
                   (cauchy_real_arctan x Hx)
                   (real_opp (cauchy_real_arctan x Hx))).
          -- apply (abl9_arctan_wd_real x x
                       (abl9_walk_dom x h N 0%nat HN Hk Hx Hh4 Hxh) Hx).
             intros n. reflexivity.
          -- apply real_eq_refl.
        * apply (RealSetoid.real_eq_opp_compat
                   (cauchy_real_arctan
                      (abl9_brg_w_real x x
                         (abl9_walk_pos x h N 0%nat HN Hk Hx Hh4))
                      (abl9_wwalk_dom x h N 0%nat HN Hk Hx Hh4))
                   (cauchy_real_arctan
                      (abl9_brg_w_real x x
                         (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4))
                      (abl9_wwalk_dom x h N 0%nat HN Hk0 Hx Hh4))).
          apply (abl9_arctan_wd_real
                   (abl9_brg_w_real x x
                      (abl9_walk_pos x h N 0%nat HN Hk Hx Hh4))
                   (abl9_brg_w_real x x
                      (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4))
                   (abl9_wwalk_dom x h N 0%nat HN Hk Hx Hh4)
                   (abl9_wwalk_dom x h N 0%nat HN Hk0 Hx Hh4)).
          intros n.
          unfold abl9_brg_w_real.
          rewrite (real_mult_proj
                     (real_plus x (real_opp x))
                     (real_inv_pos (real_plus real_one (real_mult x x))
                        (abl9_walk_pos x h N 0%nat HN Hk Hx Hh4)) n).
          rewrite (real_plus_proj x (real_opp x) n).
          rewrite (real_opp_proj x n).
          rewrite (abl9_walkpos_proj x h N 0%nat HN Hk Hx Hh4 n).
          rewrite (real_mult_proj
                     (real_plus x (real_opp x))
                     (real_inv_pos (real_plus real_one (real_mult x x))
                        (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4)) n).
          rewrite (real_plus_proj x (real_opp x) n).
          rewrite (real_opp_proj x n).
          rewrite (abl9_walkpos_proj x h N 0%nat HN Hk0 Hx Hh4 n).
          rewrite (real_plus_proj real_one (real_mult x x) n).
          rewrite (b3r_one_proj n).
          rewrite (real_mult_proj x x n).
          cbn [projT1].
          ring.
    - apply (real_eq_trans
               (abl9_phi_at x h N HN Hx Hh4 Hxh (Datatypes.S j) Hk)
               (abl9_phi_at x h N HN Hx Hh4 Hxh j
                  (Nat.le_trans j (Datatypes.S j) N (Nat.le_succ_diag_r j) Hk))
               (real_plus
                  (real_plus (cauchy_real_arctan x Hx)
                             (real_opp (cauchy_real_arctan x Hx)))
                  (real_opp
                     (cauchy_real_arctan
                        (abl9_brg_w_real x x
                           (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4))
                        (abl9_wwalk_dom x h N 0%nat HN Hk0 Hx Hh4))))).
      + exact (Hstep j Hk).
      + exact (IHj (Nat.le_trans j (Datatypes.S j) N (Nat.le_succ_diag_r j) Hk)). }
  assert (HTop : real_eq (abl9_phi_at x h N HN Hx Hh4 Hxh N (Nat.le_refl N))
                         (real_plus
                            (real_plus (cauchy_real_arctan x Hx)
                                       (real_opp (cauchy_real_arctan x Hx)))
                            (real_opp
                               (cauchy_real_arctan
                                  (abl9_brg_w_real x x
                                     (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4))
                                  (abl9_wwalk_dom x h N 0%nat HN Hk0 Hx Hh4)))))
    by (apply Htel; apply Nat.le_refl).
  (* 项级转移：phi_N → 拟文 LHS+主形w（②域证书直接匹配） *)
  assert (Htr : real_eq (abl9_phi_at x h N HN Hx Hh4 Hxh N (Nat.le_refl N))
                        (real_plus
                           (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                      (real_opp (cauchy_real_arctan x Hx)))
                           (real_opp
                              (cauchy_real_arctan
                                 (abl9_brg_w_real (real_plus x h) x
                                    (abl9_asem_pos_main x h Hx Hh4))
                                 (abl9_brg_wpath_dom x h
                                    (abl9_asem_pos_main x h Hx Hh4)
                                    Hx Hh4))))).
  { apply (RealSetoid.real_eq_plus_compat
             (real_plus
                (cauchy_real_arctan (abl9_walk x (abl9_hN_step h (qs N)) N)
                   (abl9_walk_dom x h N N HN (Nat.le_refl N) Hx Hh4 Hxh))
                (real_opp (cauchy_real_arctan x Hx)))
             (real_opp
                (cauchy_real_arctan
                   (abl9_brg_w_real (abl9_walk x (abl9_hN_step h (qs N)) N) x
                      (abl9_walk_pos x h N N HN (Nat.le_refl N) Hx Hh4))
                   (abl9_wwalk_dom x h N N HN (Nat.le_refl N) Hx Hh4)))
             (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                        (real_opp (cauchy_real_arctan x Hx)))
             (real_opp
                (cauchy_real_arctan
                   (abl9_brg_w_real (real_plus x h) x
                      (abl9_asem_pos_main x h Hx Hh4))
                   (abl9_brg_wpath_dom x h
                      (abl9_asem_pos_main x h Hx Hh4) Hx Hh4)))).
    - apply (RealSetoid.real_eq_plus_compat
               (cauchy_real_arctan (abl9_walk x (abl9_hN_step h (qs N)) N)
                  (abl9_walk_dom x h N N HN (Nat.le_refl N) Hx Hh4 Hxh))
               (real_opp (cauchy_real_arctan x Hx))
               (cauchy_real_arctan (real_plus x h) Hxh)
               (real_opp (cauchy_real_arctan x Hx))).
      + apply (abl9_arctan_wd_real
                 (abl9_walk x (abl9_hN_step h (qs N)) N) (real_plus x h)
                 (abl9_walk_dom x h N N HN (Nat.le_refl N) Hx Hh4 Hxh) Hxh).
        intros n.
        transitivity (projT1 x n + projT1 h n).
        * rewrite (abl9_walk_proj x (abl9_hN_step h (qs N)) N n).
          unfold abl9_hN_step.
          rewrite (real_mult_proj (real_const ((1 # 1) / qs N)%Q) h n).
          rewrite (real_const_proj ((1 # 1) / qs N)%Q n).
          rewrite (Hscale (projT1 h n)).
          reflexivity.
        * symmetry. apply real_plus_proj.
      + apply real_eq_refl.
    - apply (RealSetoid.real_eq_opp_compat
               (cauchy_real_arctan
                  (abl9_brg_w_real (abl9_walk x (abl9_hN_step h (qs N)) N) x
                     (abl9_walk_pos x h N N HN (Nat.le_refl N) Hx Hh4))
                  (abl9_wwalk_dom x h N N HN (Nat.le_refl N) Hx Hh4))
               (cauchy_real_arctan
                  (abl9_brg_w_real (real_plus x h) x
                     (abl9_asem_pos_main x h Hx Hh4))
                  (abl9_brg_wpath_dom x h
                     (abl9_asem_pos_main x h Hx Hh4) Hx Hh4))).
      + apply (abl9_arctan_wd_real
                 (abl9_brg_w_real (abl9_walk x (abl9_hN_step h (qs N)) N) x
                    (abl9_walk_pos x h N N HN (Nat.le_refl N) Hx Hh4))
                 (abl9_brg_w_real (real_plus x h) x
                    (abl9_asem_pos_main x h Hx Hh4))
                 (abl9_wwalk_dom x h N N HN (Nat.le_refl N) Hx Hh4)
                 (abl9_brg_wpath_dom x h
                    (abl9_asem_pos_main x h Hx Hh4) Hx Hh4)).
        intros n.
        unfold abl9_brg_w_real.
        rewrite (real_mult_proj
                   (real_plus (abl9_walk x (abl9_hN_step h (qs N)) N)
                              (real_opp x))
                   (real_inv_pos
                      (real_plus real_one
                         (real_mult (abl9_walk x (abl9_hN_step h (qs N)) N) x))
                      (abl9_walk_pos x h N N HN (Nat.le_refl N) Hx Hh4)) n).
        rewrite (real_plus_proj (abl9_walk x (abl9_hN_step h (qs N)) N)
                   (real_opp x) n).
        rewrite (real_opp_proj x n).
        rewrite (abl9_walkpos_proj x h N N HN (Nat.le_refl N) Hx Hh4 n).
        rewrite (real_plus_proj real_one
                   (real_mult (abl9_walk x (abl9_hN_step h (qs N)) N) x) n).
        rewrite (b3r_one_proj n).
        rewrite (real_mult_proj (abl9_walk x (abl9_hN_step h (qs N)) N) x n).
        rewrite (real_mult_proj
                   (real_plus (real_plus x h) (real_opp x))
                   (real_inv_pos
                      (real_plus real_one (real_mult (real_plus x h) x))
                      (abl9_asem_pos_main x h Hx Hh4)) n).
        rewrite (real_plus_proj (real_plus x h) (real_opp x) n).
        rewrite (real_opp_proj x n).
        rewrite (abl9_posmain_proj x h Hx Hh4 n).
        rewrite (real_plus_proj real_one (real_mult (real_plus x h) x) n).
        rewrite (b3r_one_proj n).
        rewrite (real_mult_proj (real_plus x h) x n).
        rewrite (real_plus_proj x h n).
        rewrite (abl9_walk_proj x (abl9_hN_step h (qs N)) N n).
        unfold abl9_hN_step.
        rewrite (real_mult_proj (real_const ((1 # 1) / qs N)%Q) h n).
        rewrite (real_const_proj ((1 # 1) / qs N)%Q n).
        rewrite (Hscale (projT1 h n)).
        ring. }
  (* 闭合：LHS+主形 w == 0 *)
  assert (Hfin : real_eq
    (real_plus
       (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (cauchy_real_arctan x Hx)))
       (real_opp
          (cauchy_real_arctan
             (abl9_brg_w_real (real_plus x h) x (abl9_asem_pos_main x h Hx Hh4))
             (abl9_brg_wpath_dom x h
                (abl9_asem_pos_main x h Hx Hh4) Hx Hh4))))
    real_zero).
  { apply (real_eq_trans
             (real_plus
                (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                           (real_opp (cauchy_real_arctan x Hx)))
                (real_opp
                   (cauchy_real_arctan
                      (abl9_brg_w_real (real_plus x h) x
                         (abl9_asem_pos_main x h Hx Hh4))
                      (abl9_brg_wpath_dom x h
                         (abl9_asem_pos_main x h Hx Hh4) Hx Hh4))))
             (abl9_phi_at x h N HN Hx Hh4 Hxh N (Nat.le_refl N))).
    - apply real_eq_sym. exact Htr.
    - apply (real_eq_trans
               (abl9_phi_at x h N HN Hx Hh4 Hxh N (Nat.le_refl N))
               (real_plus
                  (real_plus (cauchy_real_arctan x Hx)
                             (real_opp (cauchy_real_arctan x Hx)))
                  (real_opp
                     (cauchy_real_arctan
                        (abl9_brg_w_real x x
                           (abl9_walk_pos x h N 0%nat HN Hk0 Hx Hh4))
                        (abl9_wwalk_dom x h N 0%nat HN Hk0 Hx Hh4))))
               real_zero).
      + exact HTop.
      + exact (abl9_asem_endpoint x h N HN Hx Hh4 Hxh Hk0). }
  exact (abl9_asem_move (cauchy_real_arctan (real_plus x h) Hxh)
                        (cauchy_real_arctan x Hx)
                        (cauchy_real_arctan
                           (abl9_brg_w_real (real_plus x h) x
                              (abl9_asem_pos_main x h Hx Hh4))
                           (abl9_brg_wpath_dom x h
                              (abl9_asem_pos_main x h Hx Hh4) Hx Hh4))
                        Hfin).
Qed.

(* ============================================================ *)
(* 【M3·域】拟文 RHS 形（real_inv_pos·h）的域证书：                    *)
(*   |Qinv(D_n)·h_n| ≤ 1 全 n（零见证直形；wpath_pt_bnd f:=h_n 单发）。 *)
(* ============================================================ *)
Lemma abl9_invform_dom : forall (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4))
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  forall n : nat,
  QleT' (Qabs (projT1
    (real_mult (real_inv_pos (real_plus real_one (real_mult (real_plus x h) x))
                             (abl9_asem_pos_main x h Hx Hh4)) h) n)) 1.
Proof.
  intros x h Hx Hh4 Hxh n.
  apply Qle_to_QleT'.
  assert (Eproj : projT1
    (real_mult (real_inv_pos (real_plus real_one (real_mult (real_plus x h) x))
                             (abl9_asem_pos_main x h Hx Hh4)) h) n
    == Qinv (1 + (projT1 x n + projT1 h n) * projT1 x n) * projT1 h n).
  { rewrite (real_mult_proj
               (real_inv_pos (real_plus real_one (real_mult (real_plus x h) x))
                             (abl9_asem_pos_main x h Hx Hh4)) h n).
    rewrite (abl9_posmain_proj x h Hx Hh4 n).
    rewrite (real_plus_proj real_one (real_mult (real_plus x h) x) n).
    rewrite (b3r_one_proj n).
    rewrite (real_mult_proj (real_plus x h) x n).
    rewrite (real_plus_proj x h n).
    reflexivity. }
  rewrite Eproj.
  apply (Qle_trans (Qabs (Qinv (1 + (projT1 x n + projT1 h n) * projT1 x n)
                             * projT1 h n))
                   (Qabs (projT1 h n
                             * Qinv (1 + (projT1 x n + projT1 h n) * projT1 x n)))
                   1).
  - apply qeq_imp_qle. apply abl9_Qabs_wd. apply Qmult_comm.
  - apply QleT'_to_Qle.
    apply (abl9_wpath_pt_bnd (projT1 h n) (projT1 x n) (projT1 h n)
             (projT1 x n) (projT1 h n)).
    + exact (QleT'_to_Qle _ _ (Hx n)).
    + exact (QleT'_to_Qle _ _ (Hh4 n)).
    + exact (QleT'_to_Qle _ _ (Hx n)).
    + exact (QleT'_to_Qle _ _ (Hh4 n)).
    + ring.
Qed.

(* ============================================================ *)
(* 【M3】拟文 RHS 形主定理（件16 拟文 RHS 对齐——件20 B 使用位闭合）：   *)
(*   A(x+h)−A(x) == A(inv(1+(x+h)x)·h)，域证书 M3·域 直接匹配。          *)
(* ============================================================ *)
Lemma abl9_atan_diff_formula_inv : forall (x h : Real) (N : nat)
  (HN : (1 <= N)%nat)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4))
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  (forall (i : nat) (Hi : (i < N)%nat),
     real_eq (abl9_phi_at x h N HN Hx Hh4 Hxh (Datatypes.S i) Hi)
             (abl9_phi_at x h N HN Hx Hh4 Hxh i
                (Nat.le_trans i (Datatypes.S i) N (Nat.le_succ_diag_r i) Hi))) ->
  real_eq (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (cauchy_real_arctan x Hx)))
          (cauchy_real_arctan
             (real_mult (real_inv_pos (real_plus real_one
                          (real_mult (real_plus x h) x))
                             (abl9_asem_pos_main x h Hx Hh4)) h)
             (abl9_invform_dom x h Hx Hh4 Hxh)).
Proof.
  intros x h N HN Hx Hh4 Hxh Hstep.
  apply (real_eq_trans
           (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                      (real_opp (cauchy_real_arctan x Hx)))
           (cauchy_real_arctan
              (abl9_brg_w_real (real_plus x h) x (abl9_asem_pos_main x h Hx Hh4))
              (abl9_brg_wpath_dom x h
                 (abl9_asem_pos_main x h Hx Hh4) Hx Hh4))
           (cauchy_real_arctan
              (real_mult (real_inv_pos (real_plus real_one
                           (real_mult (real_plus x h) x))
                              (abl9_asem_pos_main x h Hx Hh4)) h)
              (abl9_invform_dom x h Hx Hh4 Hxh))).
  - exact (abl9_atan_diff_formula_asem x h N HN Hx Hh4 Hxh Hstep).
  - apply (abl9_arctan_wd_real
             (abl9_brg_w_real (real_plus x h) x (abl9_asem_pos_main x h Hx Hh4))
             (real_mult (real_inv_pos (real_plus real_one
                          (real_mult (real_plus x h) x))
                             (abl9_asem_pos_main x h Hx Hh4)) h)
             (abl9_brg_wpath_dom x h
                (abl9_asem_pos_main x h Hx Hh4) Hx Hh4)
             (abl9_invform_dom x h Hx Hh4 Hxh)).
    intros n.
    unfold abl9_brg_w_real.
    rewrite (real_mult_proj
               (real_plus (real_plus x h) (real_opp x))
               (real_inv_pos (real_plus real_one (real_mult (real_plus x h) x))
                  (abl9_asem_pos_main x h Hx Hh4)) n).
    rewrite (real_plus_proj (real_plus x h) (real_opp x) n).
    rewrite (real_opp_proj x n).
    rewrite (real_mult_proj
               (real_inv_pos (real_plus real_one (real_mult (real_plus x h) x))
                             (abl9_asem_pos_main x h Hx Hh4)) h n).
    rewrite (abl9_posmain_proj x h Hx Hh4 n).
    rewrite (real_plus_proj real_one (real_mult (real_plus x h) x) n).
    rewrite (b3r_one_proj n).
    rewrite (real_mult_proj (real_plus x h) x n).
    rewrite (real_plus_proj x h n).
    ring.
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                            *)
(*   对账三联：Lemma 18 = Qed 18 = PA 语句 18，零差。                    *)
(*   （Definitions 3 件：abl9_poswit/abl9_asem_pos_main/abl9_walk_pos，  *)
(*    abl9_phi_at/abl9_hN_step 系上游件 定义，不计 Qed。）               *)
(* ============================================================ *)
Print Assumptions abl9_qs_mono.
Print Assumptions abl9_qs_ratio_bnd.
Print Assumptions abl9_q_convex_abs.
Print Assumptions abl9_lam_h_bnd.
Print Assumptions abl9_hN_step_scale.
Print Assumptions abl9_walk_proj.
Print Assumptions abl9_walk_dom.
Print Assumptions abl9_poswit_proj.
Print Assumptions abl9_posmain_pt.
Print Assumptions abl9_walkpos_pt.
Print Assumptions abl9_posmain_proj.
Print Assumptions abl9_walkpos_proj.
Print Assumptions abl9_wwalk_dom.
Print Assumptions abl9_asem_endpoint.
Print Assumptions abl9_asem_move.
Print Assumptions abl9_atan_diff_formula_asem.
Print Assumptions abl9_invform_dom.
Print Assumptions abl9_atan_diff_formula_inv.

(* 提取检验（判据 = 输出 Obj.magic 计数 0） *)
Recursive Extraction abl9_atan_diff_formula_asem.
Recursive Extraction abl9_atan_diff_formula_inv.
