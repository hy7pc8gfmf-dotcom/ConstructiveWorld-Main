(* ===================================================================== *)
(*  abl_kv_sat_drift.v —— T1：KV 逐出漂移界的 Doeblin 饱和形（独立导出件）  *)
(*  使命: 逐出行随机核 K + keep 掩码的逐出核 K_ev 的 n 步 TV 漂移           *)
(*        D(K_ev^n μ, K^n μ) 满足 Doeblin 饱和双支界（构造性 min-glb）：    *)
(*        支一（线性望远镜，既有）：D ≤ n·c + ε（使用 UpKVDrift_P2 金砖     *)
(*        kv_drift_bound）；支二（几何饱和板，本件新数学）：                *)
(*        D ≤ c/δ + ε——δ-minorization（δ·U ≤ K）经零质量投影吸收后的       *)
(*        单步收缩 D(Kμ,Kν) ≤ (1−δ)·D(μ,ν) + ε 与饱和板代数                *)
(*        c + (1−δ)·(c/δ) == c/δ 的联合。两支对任意 ε>0 同时成立，          *)
(*        即 Bishop 构造性 "D ≤ min(n·c, c/δ)"（库内无 Real 层 total min，  *)
(*        双支 And 即 glb 的构造性展开——min 定义展开双支的宿主口径）。      *)
(*  依赖: S01–S15 基座；UpKVDrift_P2（世界与线性支全导出面）；              *)
(*        UpTVDoeblin（tvd_le_minus_nonneg 减法非负桥）。新数学仅三砖：     *)
(*        ①零质量投影吸收（δU 项被 Σ(μ−ν)=0 精确吸收，免除残差除法——       *)
(*        不以 (1−δ) 作分母，δ=1 支零支化，较 UpTVDoeblin tv_r_kernel       *)
(*        配方更简）；②单步收缩与三砖合流单步配对界；③饱和板代数。         *)
(*  对标: AC 勘定 T1 主件（_tmine04_AC_KV量化域 §③T1）；                   *)
(*        UpTVDoeblin tv_doeblin_contraction 收缩配方在第二世界（Tok 词表   *)
(*        逐出核）的重演；G14 线性界的饱和后继。                  *)
(*  构造性: 纯构造性、零公理/零弃证/零经典逻辑；语句全 Set 层               *)
(*        （real_eq/real_lt/real_le/Id/InT/sigT/And）；文尾 Print           *)
(*        Assumptions 主件全 Closed + Extraction 检验。                     *)
(*  编译配方: SW2 全字面环境（COQLIB/ROCQLIB 置空），Rocq 9.1               *)
(*        rocq c -native-compiler no -Q <统一世界树> ""（独占沙箱池）。     *)
(* ===================================================================== *)

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
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpKVDrift_P2.
Require Import UpTVDoeblin.

Section KVSatDrift.

(* ---------- 0. 世界（与 UpKVDrift_P2 逐字同形；delta 四前提进语句） ----- *)

Variable Tok : Set.
Variable states : list Tok.
Variable states_ne : Not (Id states (@nil Tok)).
Variable K : Tok -> Tok -> Real.
Variable Krow : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K s s') states) real_one.
Variable Kpos : forall s s' : Tok, real_lt real_zero (K s s').
Variable keep : Tok -> bool.
Variable keep_nonempty :
  sigT (fun s : Tok => And (Id (keep s) true) (InT s states)).

(* 均匀分布（对齐 UpKVDrift_P2 的 U 导出面；kv_N_pos 证书直引） *)
Definition kvs_UU (s' : Tok) : Real :=
  real_inv_pos (real_of_nat (length states))
    (kv_N_pos Tok states states_ne K Krow keep keep_nonempty).

Variable delta : Real.
Variable delta_pos : real_lt real_zero delta.
Variable delta_le_one : real_le delta real_one.
Variable delta_minor : forall s s' : Tok,
  real_le (real_mult delta (kvs_UU s')) (K s s').

(* 一致行误差常数与前提（件 4 同形） *)
Variable c : Real.
Variable Hrow : forall s : Tok,
  real_le (tv_row Tok states K Kpos keep keep_nonempty s) c.

(* ---------- 1. 导出面别名与 ε 份额 ---------- *)

Definition kvs_KEV : Tok -> Tok -> Real :=
  K_ev Tok states K Kpos keep keep_nonempty.
Definition kvs_kevI : nat -> (Tok -> Real) -> Tok -> Real :=
  kev_iter Tok states K Kpos keep keep_nonempty.
Definition kvs_kI : nat -> (Tok -> Real) -> Tok -> Real :=
  k_iter Tok states K.
Definition kvs_LS : (Tok -> Tok -> Real) -> (Tok -> Real) -> Tok -> Real :=
  lstep Tok states.
Definition kvs_DD : (Tok -> Real) -> (Tok -> Real) -> Real :=
  Ddist Tok states.
Definition kvs_omd : Real := real_minus_r real_one delta.
Definition kvs_invd : Real := real_inv_pos delta delta_pos.
Definition kvs_board : Real := real_mult c kvs_invd.
Definition kvs_h3 (eps : Real) : Real :=
  real_mult (real_inv_pos (real_plus (real_plus real_one real_one)
                             real_one) kv_three_R_pos) eps.
Definition kvs_h2 (eps : Real) : Real :=
  real_mult (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) eps.

Lemma kvs_h3_pos : forall eps : Real,
  real_lt real_zero eps -> real_lt real_zero (kvs_h3 eps).
Proof.
  intros eps Heps. unfold kvs_h3. apply real_mult_pos_compat.
  - apply real_inv_pos_pos.
  - exact Heps.
Qed.

Lemma kvs_h2_pos : forall eps : Real,
  real_lt real_zero eps -> real_lt real_zero (kvs_h2 eps).
Proof.
  intros eps Heps. unfold kvs_h2. apply real_mult_pos_compat.
  - apply real_inv_pos_pos.
  - exact Heps.
Qed.

Lemma kvs_h2_nonneg : forall eps : Real,
  real_lt real_zero eps -> real_le real_zero (kvs_h2 eps).
Proof.
  intros eps Heps. apply real_le_from_lt_aux. exact (kvs_h2_pos eps Heps).
Qed.

(* ---------- 2. 支柱代数：均匀分布、行误差非负、omd 双界 ---------- *)

(* Σ U == 1（均匀分布归一：常数和 + inv 吸收） *)
Lemma kvs_U_sum_one : real_eq (real_list_sum Tok kvs_UU states) real_one.
Proof.
  apply (real_eq_trans
           (real_list_sum Tok kvs_UU states)
           (real_mult (real_of_nat (length states))
              (real_inv_pos (real_of_nat (length states))
                 (kv_N_pos Tok states states_ne K Krow keep keep_nonempty)))
           real_one).
  - exact (kv_sum_const_list Tok
             (real_inv_pos (real_of_nat (length states))
                (kv_N_pos Tok states states_ne K Krow keep keep_nonempty))
             states).
  - exact (real_inv_pos_correct (real_of_nat (length states))
             (kv_N_pos Tok states states_ne K Krow keep keep_nonempty)).
Qed.

(* 逐点残差非负：K − δ·U ≥ 0（minorization 直引 + 减法非负桥） *)
Lemma kvs_W_nonneg : forall s s' : Tok,
  real_le real_zero (real_minus_r (K s s') (real_mult delta (kvs_UU s'))).
Proof.
  intros s s'.
  exact (tvd_le_minus_nonneg (K s s') (real_mult delta (kvs_UU s'))
           (delta_minor s s')).
Qed.

(* 0 ≤ c（行 TV == 2·tail ≥ 0 与 Hrow 的传递） *)
Lemma kvs_c_nonneg : real_le real_zero c.
Proof.
  assert (Htail : forall s : Tok,
    real_le real_zero (tail_row Tok states K keep s)).
  { intro s. apply real_list_sum_nonneg. intro w. destruct (keep w).
    - apply real_le_refl.
    - apply real_le_from_lt_aux. apply Kpos. }
  pose proof keep_nonempty as Hke.
  destruct Hke as [s0 [_ Hin0]].
  assert (Hnn2 : real_le real_zero
           (real_plus (tail_row Tok states K keep s0)
                      (tail_row Tok states K keep s0))).
  { apply (RealSetoid.real_le_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus (tail_row Tok states K keep s0)
                        (tail_row Tok states K keep s0))).
    - apply real_eq_sym. apply real_plus_zero.
    - apply real_le_plus_compat.
      + exact (Htail s0).
      + exact (Htail s0). }
  apply (real_le_trans real_zero
           (tv_row Tok states K Kpos keep keep_nonempty s0) c).
  - apply (real_le_trans real_zero
             (real_plus (tail_row Tok states K keep s0)
                        (tail_row Tok states K keep s0))
             (tv_row Tok states K Kpos keep keep_nonempty s0)).
    + exact Hnn2.
    + apply RealSetoid.real_eq_le.
      exact (real_eq_sym _ _
               (kev_row_tv_exact Tok states K Krow Kpos keep keep_nonempty
                  s0)).
  - exact (Hrow s0).
Qed.

(* 0 ≤ 1−δ（Or 逐支；配方沿 UpTVDoeblin tv_omd_nonneg） *)
Lemma kvs_omd_nonneg : real_le real_zero kvs_omd.
Proof.
  destruct delta_le_one as [Hdlt | Hd1].
  - apply (RealSetoid.real_lt_le_iff_req real_zero kvs_omd). left.
    apply (RealSetoid.real_lt_id_l real_zero
             (real_plus delta (real_opp delta))
             (real_plus real_one (real_opp delta))).
    + exact (real_eq_sym (real_plus delta (real_opp delta)) real_zero
               (real_plus_opp delta)).
    + exact (real_lt_plus_compat_lt_le delta real_one (real_opp delta)
               (real_opp delta) Hdlt (real_le_refl (real_opp delta))).
  - apply RealSetoid.real_eq_le.
    apply real_eq_sym.
    apply (real_eq_trans (real_plus real_one (real_opp delta))
                         (real_plus real_one (real_opp real_one))
                         real_zero).
    + apply (RealSetoid.real_eq_plus_compat real_one (real_opp delta)
               real_one (real_opp real_one)).
      * apply real_eq_refl.
      * exact (RealSetoid.real_eq_opp_compat delta real_one Hd1).
    + exact (real_plus_opp real_one).
Qed.

(* omd + δ == 1 与 omd ≤ 1 *)
Lemma kvs_omd_plus_delta : real_eq (real_plus kvs_omd delta) real_one.
Proof.
  unfold kvs_omd, real_minus_r.
  apply (real_eq_trans
           (real_plus (real_plus real_one (real_opp delta)) delta)
           (real_plus real_one (real_plus (real_opp delta) delta))
           real_one).
  - exact (real_eq_sym _ _ (real_plus_assoc real_one (real_opp delta) delta)).
  - apply (RealSetoid.real_eq_plus_compat real_one
             (real_plus (real_opp delta) delta)
             real_one real_zero).
    + apply real_eq_refl.
    + exact (real_eq_trans (real_plus (real_opp delta) delta)
               (real_plus delta (real_opp delta)) real_zero
               (real_plus_comm (real_opp delta) delta)
               (real_plus_opp delta)).
Qed.

Lemma kvs_omd_le_one : real_le kvs_omd real_one.
Proof.
  apply (real_le_trans kvs_omd (real_plus kvs_omd delta) real_one).
  - apply real_le_plus_nonneg_r_aux.
    apply real_le_from_lt_aux. exact delta_pos.
  - apply RealSetoid.real_eq_le. exact kvs_omd_plus_delta.
Qed.

(* 乘法单边压缩：(1−δ)·t ≤ t（t > 0；δ=1 支经 omd≈0 的 eq 桥；全程零除法） *)
Lemma kvs_omd_mult_le : forall t : Real,
  real_lt real_zero t -> real_le (real_mult kvs_omd t) t.
Proof.
  intro t. intro Ht. destruct delta_le_one as [Hdlt | Hd1].
  - assert (Homd : real_lt real_zero kvs_omd).
    { apply (RealSetoid.real_lt_id_l real_zero
               (real_plus delta (real_opp delta))
               (real_plus real_one (real_opp delta))).
      - exact (real_eq_sym (real_plus delta (real_opp delta)) real_zero
                 (real_plus_opp delta)).
      - exact (real_lt_plus_compat_lt_le delta real_one (real_opp delta)
                 (real_opp delta) Hdlt (real_le_refl (real_opp delta))). }
    apply (real_le_trans (real_mult kvs_omd t) (real_mult t kvs_omd) t).
    + apply inr. apply real_mult_comm.
    + apply (real_le_trans (real_mult t kvs_omd)
               (real_mult t real_one) t).
      * exact (real_le_mult_compat_l_aux kvs_omd real_one t Ht
                 kvs_omd_le_one).
      * apply inr. apply real_mult_one.
  - apply (real_le_trans (real_mult kvs_omd t) real_zero t).
    + apply RealSetoid.real_eq_le.
      apply (real_eq_trans (real_mult kvs_omd t)
               (real_mult real_zero t) real_zero).
      * apply (RealSetoid.real_eq_mult_compat kvs_omd t real_zero t).
        -- apply (real_eq_trans kvs_omd
                     (real_plus real_one (real_opp real_one)) real_zero).
           ++ unfold kvs_omd, real_minus_r.
              apply (RealSetoid.real_eq_plus_compat real_one
                       (real_opp delta) real_one (real_opp real_one)).
              ** apply real_eq_refl.
              ** exact (RealSetoid.real_eq_opp_compat delta real_one Hd1).
           ++ exact (real_plus_opp real_one).
        -- apply real_eq_refl.
      * exact (real_eq_trans (real_mult real_zero t)
                 (real_mult t real_zero) real_zero
                 (real_mult_comm real_zero t) (real_mult_zero t)).
    + apply real_le_from_lt_aux. exact Ht.
Qed.

(* ---------- 3. 零质量投影吸收与单步收缩（新数学核心一） ---------- *)

(* Σ(μ−ν) == 0（双归一） *)
Lemma kvs_sum_minus_zero : forall mu nu : Tok -> Real,
  real_eq (real_list_sum Tok mu states) real_one ->
  real_eq (real_list_sum Tok nu states) real_one ->
  real_eq (real_list_sum Tok
             (fun s : Tok => real_minus_r (mu s) (nu s)) states) real_zero.
Proof.
  intros mu nu Hmu Hnu. unfold real_minus_r.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun s : Tok => real_plus (mu s) (real_opp (nu s))) states)
           (real_plus (real_list_sum Tok mu states)
              (real_list_sum Tok (fun s : Tok => real_opp (nu s)) states))
           real_zero).
  - apply real_list_sum_add.
  - apply (real_eq_trans
             (real_plus (real_list_sum Tok mu states)
                (real_list_sum Tok (fun s : Tok => real_opp (nu s)) states))
             (real_plus real_one (real_opp real_one)) real_zero).
    + apply (RealSetoid.real_eq_plus_compat (real_list_sum Tok mu states)
               (real_list_sum Tok (fun s : Tok => real_opp (nu s)) states)
               real_one (real_opp real_one) Hmu
               (real_eq_trans
                  (real_list_sum Tok
                     (fun w : Tok => real_opp (nu w)) states)
                  (real_opp (real_list_sum Tok nu states))
                  (real_opp real_one)
                  (real_list_sum_opp Tok nu states)
                  (RealSetoid.real_eq_opp_compat
                     (real_list_sum Tok nu states) real_one Hnu))).
    + exact (real_plus_opp real_one).
Qed.

(* 残差行和：Σ_{s'} (K − δ·U)(s,s') == 1 − δ == omd（每行） *)
Lemma kvs_W_row : forall s : Tok,
  real_eq (real_list_sum Tok
             (fun s' : Tok =>
                real_minus_r (K s s') (real_mult delta (kvs_UU s'))) states)
          kvs_omd.
Proof.
  intro s.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_minus_r (K s s') (real_mult delta (kvs_UU s'))) states)
           (real_plus real_one
              (real_opp (real_mult delta real_one)))
           kvs_omd).
  - unfold real_minus_r.
    apply (real_eq_trans
             (real_list_sum Tok
                (fun s' : Tok =>
                   real_plus (K s s')
                     (real_opp (real_mult delta (kvs_UU s')))) states)
             (real_plus
                (real_list_sum Tok (fun s' : Tok => K s s') states)
                (real_list_sum Tok
                   (fun s' : Tok =>
                      real_opp (real_mult delta (kvs_UU s'))) states))
             (real_plus real_one
                (real_opp (real_mult delta real_one)))).
    + apply real_list_sum_add.
    + apply (RealSetoid.real_eq_plus_compat
               (real_list_sum Tok (fun s' : Tok => K s s') states)
               (real_list_sum Tok
                  (fun s' : Tok => real_opp (real_mult delta (kvs_UU s')))
                  states)
               real_one
               (real_opp (real_mult delta real_one))).
      * exact (Krow s).
      * exact (real_eq_trans
                 (real_list_sum Tok
                    (fun s' : Tok =>
                       real_opp (real_mult delta (kvs_UU s'))) states)
                 (real_opp
                    (real_list_sum Tok
                       (fun s' : Tok => real_mult delta (kvs_UU s'))
                       states))
                 (real_opp (real_mult delta real_one))
                 (real_list_sum_opp Tok
                    (fun s' : Tok => real_mult delta (kvs_UU s')) states)
                 (real_eq_trans
                    (real_opp
                       (real_list_sum Tok
                          (fun s' : Tok => real_mult delta (kvs_UU s'))
                          states))
                    (real_opp
                       (real_mult delta
                          (real_list_sum Tok kvs_UU states)))
                    (real_opp (real_mult delta real_one))
                    (RealSetoid.real_eq_opp_compat
                       (real_list_sum Tok
                          (fun s' : Tok => real_mult delta (kvs_UU s'))
                          states)
                       (real_mult delta (real_list_sum Tok kvs_UU states))
                       (real_list_sum_linear Tok delta kvs_UU states))
                    (RealSetoid.real_eq_opp_compat
                       (real_mult delta (real_list_sum Tok kvs_UU states))
                       (real_mult delta real_one)
                       (RealSetoid.real_eq_mult_compat delta
                          (real_list_sum Tok kvs_UU states) delta real_one
                          (real_eq_refl _) kvs_U_sum_one)))).
  - unfold kvs_omd, real_minus_r.
    apply (RealSetoid.real_eq_plus_compat real_one
             (real_opp (real_mult delta real_one))
             real_one (real_opp delta) (real_eq_refl _)).
    apply (RealSetoid.real_eq_opp_compat (real_mult delta real_one) delta
             (real_mult_one delta)).
Qed.

(* 零质量投影吸收：Σf == 0 ⟹ Σ f·K == Σ f·(K − δ·U)（δU 项精确消没） *)
Lemma kvs_absorb : forall f : Tok -> Real,
  real_eq (real_list_sum Tok f states) real_zero ->
  forall s' : Tok,
  real_eq (real_list_sum Tok
             (fun s : Tok => real_mult (f s) (K s s')) states)
          (real_list_sum Tok
             (fun s : Tok =>
                real_mult (f s)
                  (real_minus_r (K s s') (real_mult delta (kvs_UU s'))))
             states).
Proof.
  intros f Hf0 s'.
  (* 点一：f·K == f·(δU + (K − δU))，而 δU + (K − δU) == K *)
  assert (Hpt : forall s : Tok,
    real_eq (real_mult (f s) (K s s'))
            (real_mult (f s)
               (real_plus (real_mult delta (kvs_UU s'))
                          (real_minus_r (K s s')
                             (real_mult delta (kvs_UU s')))))).
  { intro s. apply (RealSetoid.real_eq_mult_compat (f s) (K s s') (f s)
               (real_plus (real_mult delta (kvs_UU s'))
                          (real_minus_r (K s s')
                             (real_mult delta (kvs_UU s'))))).
    - apply real_eq_refl.
    - unfold real_minus_r.
      apply real_eq_sym.
      apply (real_eq_trans
               (real_plus (real_mult delta (kvs_UU s'))
                          (real_plus (K s s')
                                     (real_opp
                                        (real_mult delta (kvs_UU s')))))
               (real_plus (real_plus (real_mult delta (kvs_UU s'))
                                     (K s s'))
                          (real_opp (real_mult delta (kvs_UU s'))))
               (K s s')).
      + exact (real_plus_assoc (real_mult delta (kvs_UU s')) (K s s')
                 (real_opp (real_mult delta (kvs_UU s')))).
      + apply (real_eq_trans
                 (real_plus (real_plus (real_mult delta (kvs_UU s'))
                                       (K s s'))
                            (real_opp (real_mult delta (kvs_UU s'))))
                 (real_plus (real_plus (K s s')
                                       (real_mult delta (kvs_UU s')))
                            (real_opp (real_mult delta (kvs_UU s'))))
                 (K s s')).
        * apply (RealSetoid.real_eq_plus_compat
                   (real_plus (real_mult delta (kvs_UU s')) (K s s'))
                   (real_opp (real_mult delta (kvs_UU s')))
                   (real_plus (K s s') (real_mult delta (kvs_UU s')))
                   (real_opp (real_mult delta (kvs_UU s')))
                   (real_plus_comm (real_mult delta (kvs_UU s')) (K s s'))
                   (real_eq_refl _)).
        * apply (real_eq_trans
                   (real_plus (real_plus (K s s')
                                         (real_mult delta (kvs_UU s')))
                              (real_opp (real_mult delta (kvs_UU s'))))
                   (real_plus (K s s')
                              (real_plus (real_mult delta (kvs_UU s'))
                                         (real_opp
                                            (real_mult delta
                                                         (kvs_UU s')))))
                   (K s s')).
          -- exact (real_eq_sym _ _
                       (real_plus_assoc (K s s')
                          (real_mult delta (kvs_UU s'))
                          (real_opp (real_mult delta (kvs_UU s'))))).
          -- apply (real_eq_trans
                       (real_plus (K s s')
                          (real_plus (real_mult delta (kvs_UU s'))
                                     (real_opp
                                        (real_mult delta (kvs_UU s')))))
                       (real_plus (K s s') real_zero)
                       (K s s')).
             ++ apply (RealSetoid.real_eq_plus_compat (K s s')
                          (real_plus (real_mult delta (kvs_UU s'))
                                     (real_opp
                                        (real_mult delta (kvs_UU s'))))
                          (K s s') real_zero
                          (real_eq_refl _)
                          (real_plus_opp (real_mult delta (kvs_UU s')))).
             ++ apply real_plus_zero. }
  (* 主链：Σ f·K == Σ f·(δU+W) == Σ f·δU + Σ f·W == 0 + Σ f·W == Σ f·W *)
  apply (real_eq_trans
           (real_list_sum Tok
              (fun s : Tok => real_mult (f s) (K s s')) states)
           (real_plus
              (real_list_sum Tok
                 (fun s : Tok =>
                    real_mult (f s) (real_mult delta (kvs_UU s'))) states)
              (real_list_sum Tok
                 (fun s : Tok =>
                    real_mult (f s)
                      (real_minus_r (K s s')
                         (real_mult delta (kvs_UU s')))) states))
           (real_list_sum Tok
              (fun s : Tok =>
                 real_mult (f s)
                   (real_minus_r (K s s')
                      (real_mult delta (kvs_UU s')))) states)).
  - apply (real_eq_trans
             (real_list_sum Tok
                (fun s : Tok => real_mult (f s) (K s s')) states)
             (real_list_sum Tok
                (fun s : Tok =>
                   real_mult (f s)
                     (real_plus (real_mult delta (kvs_UU s'))
                                (real_minus_r (K s s')
                                   (real_mult delta (kvs_UU s')))))
                states)
             (real_plus
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_mult (f s) (real_mult delta (kvs_UU s'))) states)
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_mult (f s)
                        (real_minus_r (K s s')
                           (real_mult delta (kvs_UU s')))) states))).
    + apply real_list_sum_ext. exact Hpt.
    + apply (real_eq_trans
               (real_list_sum Tok
                  (fun s : Tok =>
                     real_mult (f s)
                       (real_plus (real_mult delta (kvs_UU s'))
                                  (real_minus_r (K s s')
                                     (real_mult delta (kvs_UU s')))))
                  states)
               (real_list_sum Tok
                  (fun s : Tok =>
                     real_plus
                       (real_mult (f s) (real_mult delta (kvs_UU s')))
                       (real_mult (f s)
                          (real_minus_r (K s s')
                             (real_mult delta (kvs_UU s'))))) states)
               (real_plus
                  (real_list_sum Tok
                     (fun s : Tok =>
                        real_mult (f s) (real_mult delta (kvs_UU s')))
                     states)
                  (real_list_sum Tok
                     (fun s : Tok =>
                        real_mult (f s)
                          (real_minus_r (K s s')
                             (real_mult delta (kvs_UU s')))) states))).
      * apply real_list_sum_ext. intro s. apply real_distrib.
      * apply real_list_sum_add.
  - apply (real_eq_trans
             (real_plus
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_mult (f s) (real_mult delta (kvs_UU s'))) states)
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_mult (f s)
                        (real_minus_r (K s s')
                           (real_mult delta (kvs_UU s')))) states))
             (real_plus real_zero
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_mult (f s)
                        (real_minus_r (K s s')
                           (real_mult delta (kvs_UU s')))) states))
             (real_list_sum Tok
                (fun s : Tok =>
                   real_mult (f s)
                     (real_minus_r (K s s')
                        (real_mult delta (kvs_UU s')))) states)).
    + apply (RealSetoid.real_eq_plus_compat
               (real_list_sum Tok
                  (fun s : Tok =>
                     real_mult (f s) (real_mult delta (kvs_UU s'))) states)
               (real_list_sum Tok
                  (fun s : Tok =>
                     real_mult (f s)
                       (real_minus_r (K s s')
                          (real_mult delta (kvs_UU s')))) states)
               real_zero
               (real_list_sum Tok
                  (fun s : Tok =>
                     real_mult (f s)
                       (real_minus_r (K s s')
                          (real_mult delta (kvs_UU s')))) states)
               (real_eq_trans
                  (real_list_sum Tok
                     (fun s : Tok =>
                        real_mult (f s) (real_mult delta (kvs_UU s')))
                     states)
                  (real_mult (real_mult delta (kvs_UU s'))
                     (real_list_sum Tok f states))
                  real_zero
                  (real_eq_trans
                     (real_list_sum Tok
                        (fun s : Tok =>
                           real_mult (f s) (real_mult delta (kvs_UU s')))
                        states)
                     (real_list_sum Tok
                        (fun s : Tok =>
                           real_mult (real_mult delta (kvs_UU s')) (f s))
                        states)
                     (real_mult (real_mult delta (kvs_UU s'))
                        (real_list_sum Tok f states))
                     (real_list_sum_ext Tok
                        (fun s : Tok =>
                           real_mult (f s) (real_mult delta (kvs_UU s')))
                        (fun s : Tok =>
                           real_mult (real_mult delta (kvs_UU s')) (f s))
                        states
                        (fun s : Tok =>
                           real_mult_comm (f s)
                             (real_mult delta (kvs_UU s'))))
                     (real_list_sum_linear Tok
                        (real_mult delta (kvs_UU s')) f states))
                  (real_eq_trans
                     (real_mult (real_mult delta (kvs_UU s'))
                        (real_list_sum Tok f states))
                     (real_mult (real_mult delta (kvs_UU s')) real_zero)
                     real_zero
                     (RealSetoid.real_eq_mult_compat
                        (real_mult delta (kvs_UU s'))
                        (real_list_sum Tok f states)
                        (real_mult delta (kvs_UU s')) real_zero
                        (real_eq_refl _) Hf0)
                     (real_mult_zero (real_mult delta (kvs_UU s')))))
               (real_eq_refl _)).
    + apply kv_plus_zero_l.
Qed.

(* 单步 Doeblin 收缩（Ddist 全和形，Bishop ε）：
   D(Kμ, Kν) ≤ (1−δ)·D(μ,ν) + ε —— 零质量投影吸收 + 残差行和 == 1−δ *)
Lemma kvs_step_contract : forall (mu nu : Tok -> Real) (eps : Real),
  real_eq (real_list_sum Tok mu states) real_one ->
  real_eq (real_list_sum Tok nu states) real_one ->
  real_lt real_zero eps ->
  real_le (kvs_DD (kvs_LS K mu) (kvs_LS K nu))
          (real_plus (real_mult kvs_omd (kvs_DD mu nu)) eps).
Proof.
  intros mu nu eps Hmu Hnu Heps.
  assert (Hshare : real_lt real_zero (real_mult
            (real_inv_pos (real_of_nat (length states))
               (kv_N_pos Tok states states_ne K Krow keep keep_nonempty))
            eps))
    by (apply kv_share_pos; exact Heps).
  assert (Hf0 : real_eq (real_list_sum Tok
                  (fun s : Tok => real_minus_r (mu s) (nu s)) states)
                  real_zero)
    by exact (kvs_sum_minus_zero mu nu Hmu Hnu).
  (* 单点恒等：lstep 差 == 残差加权和（kv_lstep_minus_pt2 + 吸收） *)
  assert (Habs : forall s' : Tok,
    real_eq (real_minus_r (kvs_LS K mu s') (kvs_LS K nu s'))
            (real_list_sum Tok
               (fun s : Tok =>
                  real_mult (real_minus_r (mu s) (nu s))
                            (real_minus_r (K s s')
                               (real_mult delta (kvs_UU s')))) states)).
  { intro s'.
    exact (real_eq_trans
             (real_minus_r (kvs_LS K mu s') (kvs_LS K nu s'))
             (real_list_sum Tok
                (fun s : Tok =>
                   real_mult (real_minus_r (mu s) (nu s)) (K s s')) states)
             (real_list_sum Tok
                (fun s : Tok =>
                   real_mult (real_minus_r (mu s) (nu s))
                             (real_minus_r (K s s')
                                (real_mult delta (kvs_UU s')))) states)
             (kv_lstep_minus_pt2 Tok states K mu nu s')
             (kvs_absorb (fun s : Tok => real_minus_r (mu s) (nu s))
                Hf0 s')). }
  (* |a·w| == |a|·w（w ≥ 0） *)
  assert (Habspt : forall (s s' : Tok),
    real_eq (real_abs (real_mult (real_minus_r (mu s) (nu s))
                                 (real_minus_r (K s s')
                                    (real_mult delta (kvs_UU s')))))
            (real_mult (real_abs (real_minus_r (mu s) (nu s)))
                       (real_minus_r (K s s')
                          (real_mult delta (kvs_UU s'))))).
  { intros s s'.
    apply (real_eq_trans
             (real_abs (real_mult (real_minus_r (mu s) (nu s))
                                  (real_minus_r (K s s')
                                     (real_mult delta (kvs_UU s')))))
             (real_mult (real_abs (real_minus_r (mu s) (nu s)))
                        (real_abs (real_minus_r (K s s')
                                     (real_mult delta (kvs_UU s'))))) _).
    - exact (real_abs_mult_req (real_minus_r (mu s) (nu s))
               (real_minus_r (K s s') (real_mult delta (kvs_UU s')))).
    - apply (RealSetoid.real_eq_mult_compat
               (real_abs (real_minus_r (mu s) (nu s)))
               (real_abs (real_minus_r (K s s')
                            (real_mult delta (kvs_UU s'))))
               (real_abs (real_minus_r (mu s) (nu s)))
               (real_minus_r (K s s') (real_mult delta (kvs_UU s')))
               (real_eq_refl _)
               (kv_abs_nonneg_id (real_minus_r (K s s')
                                    (real_mult delta (kvs_UU s')))
                  (kvs_W_nonneg s s'))). }
  unfold kvs_DD.
  (* 第一段（le）：逐点三角 + 常数份额 + |a·w| == |a|·w 全和化 *)
  apply (real_le_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_abs (real_minus_r (kvs_LS K mu s')
                            (kvs_LS K nu s'))) states)
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_plus
                   (real_list_sum Tok
                      (fun s : Tok =>
                         real_mult
                           (real_abs (real_minus_r (mu s) (nu s)))
                           (real_minus_r (K s s')
                              (real_mult delta (kvs_UU s')))) states)
                   (real_mult
                      (real_inv_pos (real_of_nat (length states))
                         (kv_N_pos Tok states states_ne K Krow keep
                            keep_nonempty)) eps)) states)
           (real_plus (real_mult kvs_omd (kvs_DD mu nu)) eps)).
  - apply real_list_sum_le. intro s'.
    apply (real_le_trans
             (real_abs (real_minus_r (kvs_LS K mu s') (kvs_LS K nu s')))
             (real_plus
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_abs (real_mult
                                  (real_minus_r (mu s) (nu s))
                                  (real_minus_r (K s s')
                                     (real_mult delta (kvs_UU s')))))
                   states)
                (real_mult
                   (real_inv_pos (real_of_nat (length states))
                      (kv_N_pos Tok states states_ne K Krow keep
                         keep_nonempty)) eps))
             (real_plus
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_mult
                        (real_abs (real_minus_r (mu s) (nu s)))
                        (real_minus_r (K s s')
                           (real_mult delta (kvs_UU s')))) states)
                (real_mult
                   (real_inv_pos (real_of_nat (length states))
                      (kv_N_pos Tok states states_ne K Krow keep
                         keep_nonempty)) eps))).
    + apply (real_le_trans
               (real_abs (real_minus_r (kvs_LS K mu s')
                            (kvs_LS K nu s')))
               (real_abs
                  (real_list_sum Tok
                     (fun s : Tok =>
                        real_mult (real_minus_r (mu s) (nu s))
                                  (real_minus_r (K s s')
                                     (real_mult delta (kvs_UU s'))))
                     states))
               (real_plus
                  (real_list_sum Tok
                     (fun s : Tok =>
                        real_abs (real_mult
                                    (real_minus_r (mu s) (nu s))
                                    (real_minus_r (K s s')
                                       (real_mult delta
                                                    (kvs_UU s')))))
                     states)
                  (real_mult
                     (real_inv_pos (real_of_nat (length states))
                        (kv_N_pos Tok states states_ne K Krow keep
                           keep_nonempty)) eps))).
      * apply inr. apply real_abs_eq_compat. exact (Habs s').
      * exact (kv_abs_triangle_list_eps Tok
                 (fun s : Tok =>
                    real_mult (real_minus_r (mu s) (nu s))
                              (real_minus_r (K s s')
                                 (real_mult delta (kvs_UU s'))))
                 states
                 (real_mult
                    (real_inv_pos (real_of_nat (length states))
                       (kv_N_pos Tok states states_ne K Krow keep
                          keep_nonempty)) eps)
                 Hshare).
    + apply inr.
      apply (RealSetoid.real_eq_plus_compat
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_abs (real_mult
                                  (real_minus_r (mu s) (nu s))
                                  (real_minus_r (K s s')
                                     (real_mult delta (kvs_UU s')))))
                   states)
                (real_mult
                   (real_inv_pos (real_of_nat (length states))
                      (kv_N_pos Tok states states_ne K Krow keep
                         keep_nonempty)) eps)
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_mult
                        (real_abs (real_minus_r (mu s) (nu s)))
                        (real_minus_r (K s s')
                           (real_mult delta (kvs_UU s')))) states)
                (real_mult
                   (real_inv_pos (real_of_nat (length states))
                      (kv_N_pos Tok states states_ne K Krow keep
                         keep_nonempty)) eps)
                (real_list_sum_ext Tok
                   (fun s : Tok =>
                      real_abs (real_mult
                                  (real_minus_r (mu s) (nu s))
                                  (real_minus_r (K s s')
                                     (real_mult delta
                                                  (kvs_UU s')))))
                   (fun s : Tok =>
                      real_mult
                        (real_abs (real_minus_r (mu s) (nu s)))
                        (real_minus_r (K s s')
                           (real_mult delta (kvs_UU s'))))
                   states (fun s : Tok => Habspt s s'))
                (real_eq_refl _)).
  - (* 第二段（eq）：拆常数 + 换序 + inv 吸收 + 逐行化 + comm/linear 闭合 *)
    apply inr.
    apply (real_eq_trans
             (real_list_sum Tok
                (fun s' : Tok =>
                   real_plus
                     (real_list_sum Tok
                        (fun s : Tok =>
                           real_mult
                             (real_abs (real_minus_r (mu s) (nu s)))
                             (real_minus_r (K s s')
                                (real_mult delta (kvs_UU s')))) states)
                     (real_mult
                        (real_inv_pos (real_of_nat (length states))
                           (kv_N_pos Tok states states_ne K Krow keep
                              keep_nonempty)) eps)) states)
             (real_plus
                (real_list_sum Tok
                   (fun s' : Tok =>
                      real_list_sum Tok
                        (fun s : Tok =>
                           real_mult
                             (real_abs (real_minus_r (mu s) (nu s)))
                             (real_minus_r (K s s')
                                (real_mult delta (kvs_UU s')))) states)
                   states)
                (real_mult (real_of_nat (length states))
                   (real_mult
                      (real_inv_pos (real_of_nat (length states))
                         (kv_N_pos Tok states states_ne K Krow keep
                            keep_nonempty)) eps)))).
    + apply (real_eq_trans
               (real_list_sum Tok
                  (fun s' : Tok =>
                     real_plus
                       (real_list_sum Tok
                          (fun s : Tok =>
                             real_mult
                               (real_abs (real_minus_r (mu s) (nu s)))
                               (real_minus_r (K s s')
                                  (real_mult delta (kvs_UU s')))) states)
                       (real_mult
                          (real_inv_pos (real_of_nat (length states))
                             (kv_N_pos Tok states states_ne K Krow keep
                                keep_nonempty)) eps)) states)
               (real_plus
                  (real_list_sum Tok
                     (fun s' : Tok =>
                        real_list_sum Tok
                          (fun s : Tok =>
                             real_mult
                               (real_abs (real_minus_r (mu s) (nu s)))
                               (real_minus_r (K s s')
                                  (real_mult delta (kvs_UU s')))) states)
                     states)
                  (real_list_sum Tok
                     (fun _ : Tok =>
                        real_mult
                          (real_inv_pos (real_of_nat (length states))
                             (kv_N_pos Tok states states_ne K Krow keep
                                keep_nonempty)) eps) states))).
      * apply real_list_sum_add.
      * apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum Tok
                    (fun s' : Tok =>
                       real_list_sum Tok
                         (fun s : Tok =>
                            real_mult
                              (real_abs (real_minus_r (mu s) (nu s)))
                              (real_minus_r (K s s')
                                 (real_mult delta (kvs_UU s')))) states)
                    states)
                 (real_list_sum Tok
                    (fun _ : Tok =>
                       real_mult
                         (real_inv_pos (real_of_nat (length states))
                            (kv_N_pos Tok states states_ne K Krow keep
                               keep_nonempty)) eps) states)
                 (real_list_sum Tok
                    (fun s' : Tok =>
                       real_list_sum Tok
                         (fun s : Tok =>
                            real_mult
                              (real_abs (real_minus_r (mu s) (nu s)))
                              (real_minus_r (K s s')
                                 (real_mult delta (kvs_UU s')))) states)
                    states)
                 (real_mult (real_of_nat (length states))
                    (real_mult
                       (real_inv_pos (real_of_nat (length states))
                          (kv_N_pos Tok states states_ne K Krow keep
                             keep_nonempty)) eps))
                 (real_eq_refl _)
                 (kv_sum_const_list Tok
                    (real_mult
                       (real_inv_pos (real_of_nat (length states))
                          (kv_N_pos Tok states states_ne K Krow keep
                             keep_nonempty)) eps) states)).
    + apply (real_eq_trans
             (real_plus
                (real_list_sum Tok
                   (fun s' : Tok =>
                      real_list_sum Tok
                        (fun s : Tok =>
                           real_mult
                             (real_abs (real_minus_r (mu s) (nu s)))
                             (real_minus_r (K s s')
                                (real_mult delta (kvs_UU s')))) states)
                   states)
                (real_mult (real_of_nat (length states))
                   (real_mult
                      (real_inv_pos (real_of_nat (length states))
                         (kv_N_pos Tok states states_ne K Krow keep
                            keep_nonempty)) eps)))
             (real_plus
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_list_sum Tok
                        (fun s' : Tok =>
                           real_mult
                             (real_abs (real_minus_r (mu s) (nu s)))
                             (real_minus_r (K s s')
                                (real_mult delta (kvs_UU s')))) states)
                   states)
                eps)
             (real_plus (real_mult kvs_omd (kvs_DD mu nu)) eps)).
      * (* (Σ inner) + N·share == (Σ_s Σ_{s'} F) + eps（换序 + inv 吸收） *)
      apply (RealSetoid.real_eq_plus_compat
                (real_list_sum Tok
                   (fun s' : Tok =>
                      real_list_sum Tok
                        (fun s : Tok =>
                           real_mult
                             (real_abs (real_minus_r (mu s) (nu s)))
                             (real_minus_r (K s s')
                                (real_mult delta (kvs_UU s')))) states)
                   states)
                (real_mult (real_of_nat (length states))
                   (real_mult
                      (real_inv_pos (real_of_nat (length states))
                         (kv_N_pos Tok states states_ne K Krow keep
                            keep_nonempty)) eps))
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_list_sum Tok
                        (fun s' : Tok =>
                           real_mult
                             (real_abs (real_minus_r (mu s) (nu s)))
                             (real_minus_r (K s s')
                                (real_mult delta (kvs_UU s')))) states)
                   states)
                eps
                (kv_swap_list Tok
                   (fun s s' : Tok =>
                      real_mult (real_abs (real_minus_r (mu s) (nu s)))
                                (real_minus_r (K s s')
                                   (real_mult delta (kvs_UU s'))))
                   states states)
                (kv_inv_absorb (real_of_nat (length states))
                   (kv_N_pos Tok states states_ne K Krow keep
                      keep_nonempty) eps)).
      * apply (real_eq_trans
                 (real_plus
                    (real_list_sum Tok
                       (fun s : Tok =>
                          real_list_sum Tok
                            (fun s' : Tok =>
                               real_mult
                                 (real_abs (real_minus_r (mu s) (nu s)))
                                 (real_minus_r (K s s')
                                    (real_mult delta (kvs_UU s')))) states)
                       states)
                    eps)
                 (real_plus
                    (real_list_sum Tok
                       (fun s : Tok =>
                          real_mult
                            (real_abs (real_minus_r (mu s) (nu s)))
                            kvs_omd) states)
                    eps)
                 (real_plus (real_mult kvs_omd (kvs_DD mu nu)) eps)).
        -- (* (Σ_s Σ_{s'} F) + eps == (Σ_s |μν|(s)·omd) + eps（逐行 linear + W_row） *)
      apply (RealSetoid.real_eq_plus_compat
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_list_sum Tok
                        (fun s' : Tok =>
                           real_mult
                             (real_abs (real_minus_r (mu s) (nu s)))
                             (real_minus_r (K s s')
                                (real_mult delta (kvs_UU s')))) states)
                   states)
                eps
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_mult (real_abs (real_minus_r (mu s) (nu s)))
                                kvs_omd) states)
                eps
                (real_list_sum_ext Tok
                   (fun s : Tok =>
                      real_list_sum Tok
                        (fun s' : Tok =>
                           real_mult
                             (real_abs (real_minus_r (mu s) (nu s)))
                             (real_minus_r (K s s')
                                (real_mult delta (kvs_UU s')))) states)
                   (fun s : Tok =>
                      real_mult (real_abs (real_minus_r (mu s) (nu s)))
                                kvs_omd)
                   states
                   (fun s : Tok =>
                      real_eq_trans
                        (real_list_sum Tok
                           (fun s' : Tok =>
                              real_mult
                                (real_abs (real_minus_r (mu s) (nu s)))
                                (real_minus_r (K s s')
                                   (real_mult delta (kvs_UU s')))) states)
                        (real_mult
                           (real_abs (real_minus_r (mu s) (nu s)))
                           (real_list_sum Tok
                              (fun s' : Tok =>
                                 real_minus_r (K s s')
                                   (real_mult delta (kvs_UU s'))) states))
                        (real_mult
                           (real_abs (real_minus_r (mu s) (nu s)))
                           kvs_omd)
                        (real_list_sum_linear Tok
                           (real_abs (real_minus_r (mu s) (nu s)))
                           (fun s' : Tok =>
                              real_minus_r (K s s')
                                (real_mult delta (kvs_UU s'))) states)
                        (RealSetoid.real_eq_mult_compat
                           (real_abs (real_minus_r (mu s) (nu s)))
                           (real_list_sum Tok
                              (fun s' : Tok =>
                                 real_minus_r (K s s')
                                   (real_mult delta (kvs_UU s'))) states)
                           (real_abs (real_minus_r (mu s) (nu s))) kvs_omd
                           (real_eq_refl _) (kvs_W_row s))))
                (real_eq_refl _)).
        -- (* (Σ |μν|·omd) + eps == omd·(Σ |μν|) + eps（comm + linear_r） *)
      apply (RealSetoid.real_eq_plus_compat
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_mult (real_abs (real_minus_r (mu s) (nu s)))
                                kvs_omd) states)
                eps
                (real_mult kvs_omd
                   (real_list_sum Tok
                      (fun x : Tok =>
                         real_abs (real_minus_r (mu x) (nu x))) states))
                eps
                (real_eq_trans
                   (real_list_sum Tok
                      (fun s : Tok =>
                         real_mult (real_abs (real_minus_r (mu s) (nu s)))
                                   kvs_omd) states)
                   (real_list_sum Tok
                      (fun s : Tok =>
                         real_mult kvs_omd
                           (real_abs (real_minus_r (mu s) (nu s)))) states)
                   (real_mult kvs_omd
                      (real_list_sum Tok
                         (fun x : Tok =>
                            real_abs (real_minus_r (mu x) (nu x))) states))
                   (real_list_sum_ext Tok
                      (fun s : Tok =>
                         real_mult (real_abs (real_minus_r (mu s) (nu s)))
                                   kvs_omd)
                      (fun s : Tok =>
                         real_mult kvs_omd
                           (real_abs (real_minus_r (mu s) (nu s))))
                      states
                      (fun s : Tok =>
                         real_mult_comm
                           (real_abs (real_minus_r (mu s) (nu s))) kvs_omd))
                   (real_list_sum_linear Tok kvs_omd
                      (fun x : Tok =>
                         real_abs (real_minus_r (mu x) (nu x))) states))
                (real_eq_refl eps)).
Qed.

(* ---------- 4. 饱和板代数（新数学核心二）与 ε 份额吸收 ---------- *)

(* 板代数：c + (1−δ)·(c/δ) == c/δ *)
Lemma kvs_board_eq : real_eq
  (real_plus c (real_mult kvs_omd kvs_board)) kvs_board.
Proof.
  assert (HD1 : real_eq (real_plus delta kvs_omd) real_one).
  { apply (real_eq_trans (real_plus delta kvs_omd)
             (real_plus kvs_omd delta) real_one).
    - apply real_plus_comm.
    - exact kvs_omd_plus_delta. }
  apply (real_eq_trans
           (real_plus c (real_mult kvs_omd kvs_board))
           (real_plus (real_mult delta (real_mult kvs_invd c))
                      (real_mult kvs_omd (real_mult kvs_invd c)))
           kvs_board).
  - apply (RealSetoid.real_eq_plus_compat c
             (real_mult kvs_omd kvs_board)
             (real_mult delta (real_mult kvs_invd c))
             (real_mult kvs_omd (real_mult kvs_invd c))).
    + exact (real_eq_sym (real_mult delta (real_mult kvs_invd c)) c
               (kv_inv_absorb delta delta_pos c)).
    + apply (RealSetoid.real_eq_mult_compat kvs_omd kvs_board kvs_omd
               (real_mult kvs_invd c) (real_eq_refl _)).
      apply real_eq_sym.
      apply (real_eq_trans (real_mult kvs_invd c)
               (real_mult c kvs_invd) kvs_board).
      * apply real_mult_comm.
      * apply real_eq_refl.
  - apply (real_eq_trans
             (real_plus (real_mult delta (real_mult kvs_invd c))
                        (real_mult kvs_omd (real_mult kvs_invd c)))
             (real_mult real_one (real_mult kvs_invd c))
             kvs_board).
    + apply (real_eq_trans
               (real_plus (real_mult delta (real_mult kvs_invd c))
                          (real_mult kvs_omd (real_mult kvs_invd c)))
               (real_mult (real_plus delta kvs_omd)
                          (real_mult kvs_invd c))
               (real_mult real_one (real_mult kvs_invd c))).
      * apply (real_eq_sym _ _
                 (kv_distrib_r delta kvs_omd (real_mult kvs_invd c))).
      * apply (RealSetoid.real_eq_mult_compat (real_plus delta kvs_omd)
                 (real_mult kvs_invd c) real_one (real_mult kvs_invd c)
                 HD1 (real_eq_refl _)).
    + apply (real_eq_trans
               (real_mult real_one (real_mult kvs_invd c))
               (real_mult kvs_invd c) kvs_board).
      * exact (kv_one_mult_l (real_mult kvs_invd c)).
      * apply (real_eq_trans (real_mult kvs_invd c)
                 (real_mult c kvs_invd) kvs_board).
        -- apply real_mult_comm.
        -- apply real_eq_refl.
Qed.

(* 双份 ε 吸收：h2 + h2 == ε₀ *)
Lemma kvs_two_shares : forall eps0 : Real,
  real_eq (real_plus (kvs_h2 eps0) (kvs_h2 eps0)) eps0.
Proof.
  intro eps0. unfold kvs_h2.
  apply (real_eq_trans
           (real_plus
              (real_mult (real_inv_pos (real_plus real_one real_one)
                           kv_two_R_pos) eps0)
              (real_mult (real_inv_pos (real_plus real_one real_one)
                           kv_two_R_pos) eps0))
           (real_mult (real_plus real_one real_one)
              (real_mult (real_inv_pos (real_plus real_one real_one)
                           kv_two_R_pos) eps0))
           eps0).
  - exact (kv_plus_self_two
             (real_mult (real_inv_pos (real_plus real_one real_one)
                          kv_two_R_pos) eps0)).
  - apply (real_eq_trans
             (real_mult (real_plus real_one real_one)
                (real_mult (real_inv_pos (real_plus real_one real_one)
                             kv_two_R_pos) eps0))
             (real_mult real_one eps0)
             eps0).
    + apply (real_eq_trans
               (real_mult (real_plus real_one real_one)
                  (real_mult (real_inv_pos (real_plus real_one real_one)
                               kv_two_R_pos) eps0))
               (real_mult
                  (real_mult (real_plus real_one real_one)
                     (real_inv_pos (real_plus real_one real_one)
                        kv_two_R_pos))
                  eps0)
               (real_mult real_one eps0)).
      * exact (real_mult_assoc (real_plus real_one real_one)
                 (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
                 eps0).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_plus real_one real_one)
                    (real_inv_pos (real_plus real_one real_one)
                       kv_two_R_pos))
                 eps0 real_one eps0
                 (real_inv_pos_correct (real_plus real_one real_one)
                    kv_two_R_pos)
                 (real_eq_refl eps0)).
    + exact (kv_one_mult_l eps0).
Qed.

(* 三份 ε 吸收：h3 + (h3 + h3) == ε *)
Lemma kvs_three_shares : forall eps : Real,
  real_eq (real_plus (kvs_h3 eps) (real_plus (kvs_h3 eps) (kvs_h3 eps)))
          eps.
Proof.
  intro eps. unfold kvs_h3.
  apply (real_eq_trans
           (real_plus
              (real_mult (real_inv_pos (real_plus (real_plus real_one
                                           real_one) real_one)
                           kv_three_R_pos) eps)
              (real_plus
                 (real_mult (real_inv_pos (real_plus (real_plus real_one
                                          real_one) real_one)
                              kv_three_R_pos) eps)
                 (real_mult (real_inv_pos (real_plus (real_plus real_one
                                          real_one) real_one)
                              kv_three_R_pos) eps)))
           (real_mult (real_plus (real_plus real_one real_one) real_one)
              (real_mult (real_inv_pos (real_plus (real_plus real_one
                                           real_one) real_one)
                           kv_three_R_pos) eps))
           eps).
  - apply (real_eq_trans
             (real_plus
                (real_mult (real_inv_pos (real_plus (real_plus real_one
                                             real_one) real_one)
                             kv_three_R_pos) eps)
                (real_plus
                   (real_mult (real_inv_pos (real_plus (real_plus real_one
                                            real_one) real_one)
                                kv_three_R_pos) eps)
                   (real_mult (real_inv_pos (real_plus (real_plus real_one
                                            real_one) real_one)
                                kv_three_R_pos) eps)))
             (real_plus
                (real_plus
                   (real_mult (real_inv_pos (real_plus (real_plus real_one
                                            real_one) real_one)
                                kv_three_R_pos) eps)
                   (real_mult (real_inv_pos (real_plus (real_plus real_one
                                            real_one) real_one)
                                kv_three_R_pos) eps))
                (real_mult (real_inv_pos (real_plus (real_plus real_one
                                             real_one) real_one)
                             kv_three_R_pos) eps))
             (real_mult (real_plus (real_plus real_one real_one) real_one)
                (real_mult (real_inv_pos (real_plus (real_plus real_one
                                             real_one) real_one)
                             kv_three_R_pos) eps))).
    + exact (real_plus_assoc
               (real_mult (real_inv_pos (real_plus (real_plus real_one
                                    real_one) real_one)
                            kv_three_R_pos) eps)
               (real_mult (real_inv_pos (real_plus (real_plus real_one
                                    real_one) real_one)
                            kv_three_R_pos) eps)
               (real_mult (real_inv_pos (real_plus (real_plus real_one
                                    real_one) real_one)
                            kv_three_R_pos) eps)).
    + exact (kv_plus_self_three
               (real_mult (real_inv_pos (real_plus (real_plus real_one
                                    real_one) real_one)
                            kv_three_R_pos) eps)).
  - exact (kv_inv_absorb (real_plus (real_plus real_one real_one)
                   real_one) kv_three_R_pos eps).
Qed.

(* ---------- 5. 三砖合流单步配对界（新数学核心三） ---------- *)

(* D(K_ev x, K z) ≤ (1−δ)·D(x,z) + (c + ε)：
   三角(h3) + 行误差 kv_step_drift(h3) + 收缩 kvs_step_contract(h3)，
   kvs_three_shares 精确吸收——T1 的单步引擎。 *)
Lemma kvs_step_pair : forall (x z : Tok -> Real) (eps : Real),
  real_eq (real_list_sum Tok x states) real_one ->
  (forall s : Tok, real_le real_zero (x s)) ->
  real_eq (real_list_sum Tok z states) real_one ->
  real_lt real_zero eps ->
  real_le (kvs_DD (kvs_LS kvs_KEV x) (kvs_LS K z))
          (real_plus (real_mult kvs_omd (kvs_DD x z))
                     (real_plus c eps)).
Proof.
  intros x z eps Hnx Hnnx Hnz Heps.
  assert (Hh : real_lt real_zero (kvs_h3 eps)) by exact (kvs_h3_pos eps Heps).
  assert (H3B : real_eq (real_plus (kvs_h3 eps)
                              (real_plus (kvs_h3 eps) (kvs_h3 eps))) eps)
    by exact (kvs_three_shares eps).
  assert (Htri : real_le
            (kvs_DD (kvs_LS kvs_KEV x) (kvs_LS K z))
            (real_plus (kvs_DD (kvs_LS kvs_KEV x) (kvs_LS K x))
                       (real_plus (kvs_DD (kvs_LS K x) (kvs_LS K z))
                                  (kvs_h3 eps))))
    by exact (kv_D_triangle Tok states states_ne K Krow keep keep_nonempty
                (kvs_LS kvs_KEV x) (kvs_LS K x) (kvs_LS K z) (kvs_h3 eps)
                Hh).
  assert (Hrowx : real_le (kvs_DD (kvs_LS kvs_KEV x) (kvs_LS K x))
                    (real_plus c (kvs_h3 eps)))
    by exact (kv_step_drift Tok states states_ne K Krow Kpos keep
                keep_nonempty c Hrow x (kvs_h3 eps) Hh Hnx Hnnx).
  assert (Hcon : real_le (kvs_DD (kvs_LS K x) (kvs_LS K z))
                   (real_plus (real_mult kvs_omd (kvs_DD x z))
                              (kvs_h3 eps)))
    by exact (kvs_step_contract x z (kvs_h3 eps) Hnx Hnz Hh).
  apply (real_le_trans
           (kvs_DD (kvs_LS kvs_KEV x) (kvs_LS K z))
           (real_plus (real_plus c (real_mult kvs_omd (kvs_DD x z)))
                      eps)
           (real_plus (real_mult kvs_omd (kvs_DD x z)) (real_plus c eps))).
  - apply (real_le_trans _ _ _ Htri).
    apply (real_le_trans
             (real_plus (kvs_DD (kvs_LS kvs_KEV x) (kvs_LS K x))
                        (real_plus (kvs_DD (kvs_LS K x) (kvs_LS K z))
                                   (kvs_h3 eps)))
             (real_plus (real_plus c (kvs_h3 eps))
                        (real_plus (real_plus (real_mult kvs_omd
                                    (kvs_DD x z)) (kvs_h3 eps))
                                   (kvs_h3 eps)))
             (real_plus (real_plus c (real_mult kvs_omd (kvs_DD x z)))
                        eps)).
    + apply real_le_plus_compat.
      * exact Hrowx.
      * apply real_le_plus_compat.
        -- exact Hcon.
        -- apply real_le_refl.
    + apply inr.
      exact (kv_assemble_le c (real_mult kvs_omd (kvs_DD x z))
               (kvs_h3 eps) eps H3B).
  - apply inr.
    apply (real_eq_trans
             (real_plus (real_plus c (real_mult kvs_omd (kvs_DD x z)))
                        eps)
             (real_plus (real_plus (real_mult kvs_omd (kvs_DD x z)) c)
                        eps)
             (real_plus (real_mult kvs_omd (kvs_DD x z))
                        (real_plus c eps))).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus c (real_mult kvs_omd (kvs_DD x z))) eps
               (real_plus (real_mult kvs_omd (kvs_DD x z)) c) eps
               (real_plus_comm c (real_mult kvs_omd (kvs_DD x z)))
               (real_eq_refl eps)).
    + apply (real_eq_trans
               (real_plus (real_plus (real_mult kvs_omd (kvs_DD x z)) c)
                          eps)
               (real_plus (real_mult kvs_omd (kvs_DD x z))
                          (real_plus c eps))
               (real_plus (real_mult kvs_omd (kvs_DD x z))
                          (real_plus c eps))).
      * apply (real_eq_sym _ _ (real_plus_assoc
                   (real_mult kvs_omd (kvs_DD x z)) c eps)).
      * apply real_eq_refl.
Qed.

(* ---------- 6. 主件：Doeblin 饱和形（几何支闭式） ---------- *)

(* 板非负：0 ≤ c/δ *)
Lemma kvs_board_nonneg : real_le real_zero kvs_board.
Proof.
  apply (real_le_trans real_zero
           (real_mult real_zero kvs_invd) kvs_board).
  - apply RealSetoid.real_eq_le.
    exact (real_eq_sym (real_mult real_zero kvs_invd) real_zero
             (real_eq_trans (real_mult real_zero kvs_invd)
                (real_mult kvs_invd real_zero) real_zero
                (real_mult_comm real_zero kvs_invd)
                (real_mult_zero kvs_invd))).
  - exact (real_le_mult_compat_weak real_zero c kvs_invd
             (real_le_from_lt_aux real_zero kvs_invd (real_inv_pos_pos delta delta_pos)) (kvs_c_nonneg)).
Qed.

(* 几何支主递归闭式（饱和板形）：
   D(K_ev^n μ, K^n μ) ≤ c/δ + ε 对任意 ε>0、任意 n。
   归纳：单步配对界 + IH（半份 ε=h2）+ 乘法单边压缩 + 板代数 + 双份吸收。 *)
Lemma kvs_drift_board : forall (n : nat) (mu : Tok -> Real) (eps0 : Real),
  real_eq (real_list_sum Tok mu states) real_one ->
  (forall s : Tok, real_le real_zero (mu s)) ->
  real_lt real_zero eps0 ->
  real_le (kvs_DD (kvs_kevI n mu) (kvs_kI n mu))
          (real_plus kvs_board eps0).
Proof.
  intro n. induction n as [| n IH]; intros mu eps0 Hnorm Hnn Heps0.
  - cbn [kvs_kevI kvs_kI kev_iter k_iter].
    apply (real_le_trans (kvs_DD mu mu) real_zero
             (real_plus kvs_board eps0)).
    + apply RealSetoid.real_eq_le. exact (kv_D_zero Tok states mu).
    + apply (real_le_trans real_zero kvs_board (real_plus kvs_board eps0)).
      * exact kvs_board_nonneg.
      * apply real_le_plus_nonneg_r_aux.
        apply real_le_from_lt_aux. exact Heps0.
  - assert (Hb : real_lt real_zero (kvs_h2 eps0))
      by exact (kvs_h2_pos eps0 Heps0).
    assert (Hnnb : real_le real_zero (kvs_h2 eps0))
      by exact (kvs_h2_nonneg eps0 Heps0).
    assert (HnormX : real_eq (real_list_sum Tok (kvs_kevI n mu) states)
                       real_one)
      by exact (kv_kev_iter_norm Tok states K Kpos keep keep_nonempty
                  n mu Hnorm).
    assert (HnormZ : real_eq (real_list_sum Tok (kvs_kI n mu) states)
                       real_one)
      by exact (kv_k_iter_norm Tok states K Krow n mu Hnorm).
    assert (HnnX : forall s : Tok, real_le real_zero (kvs_kevI n mu s))
      by exact (kv_kev_iter_nonneg Tok states K Kpos keep keep_nonempty
                  n mu Hnn).
    cbn [kvs_kevI kvs_kI kev_iter k_iter].
    (* 链一：单步配对界 + IH 乘入 + omd·h2 ≤ h2 *)
    assert (Hstep : real_le
              (kvs_DD (kvs_LS kvs_KEV (kvs_kevI n mu))
                      (kvs_LS K (kvs_kI n mu)))
              (real_plus (real_plus (real_mult kvs_omd kvs_board)
                                   (kvs_h2 eps0))
                         (real_plus c (kvs_h2 eps0)))).
    { apply (real_le_trans
               (kvs_DD (kvs_LS kvs_KEV (kvs_kevI n mu))
                       (kvs_LS K (kvs_kI n mu)))
               (real_plus (real_mult kvs_omd
                             (kvs_DD (kvs_kevI n mu) (kvs_kI n mu)))
                          (real_plus c (kvs_h2 eps0)))
               (real_plus (real_plus (real_mult kvs_omd kvs_board)
                                   (kvs_h2 eps0))
                          (real_plus c (kvs_h2 eps0)))).
      - exact (kvs_step_pair (kvs_kevI n mu) (kvs_kI n mu) (kvs_h2 eps0)
                 HnormX HnnX HnormZ Hb).
      - apply real_le_plus_compat.
        + apply (real_le_trans
                   (real_mult kvs_omd
                      (kvs_DD (kvs_kevI n mu) (kvs_kI n mu)))
                   (real_mult kvs_omd
                      (real_plus kvs_board (kvs_h2 eps0)))
                   (real_plus (real_mult kvs_omd kvs_board)
                              (kvs_h2 eps0))).
        ++ exact (real_le_mult_compat_r kvs_omd
                    (kvs_DD (kvs_kevI n mu) (kvs_kI n mu))
                    (real_plus kvs_board (kvs_h2 eps0))
                    kvs_omd_nonneg (IH mu (kvs_h2 eps0) Hnorm Hnn Hb)).
        ++ apply (real_le_trans
                     (real_mult kvs_omd
                        (real_plus kvs_board (kvs_h2 eps0)))
                     (real_plus (real_mult kvs_omd kvs_board)
                                (real_mult kvs_omd (kvs_h2 eps0)))
                     (real_plus (real_mult kvs_omd kvs_board)
                                (kvs_h2 eps0))).
           ** apply inr. apply real_distrib.
           ** apply real_le_plus_compat.
              --- apply real_le_refl.
              --- exact (kvs_omd_mult_le (kvs_h2 eps0) Hb).
        + apply real_le_refl. }
    (* 链二：AC 重排 + 板代数 + 双份吸收 *)
    apply (real_le_trans
             (kvs_DD (kvs_LS kvs_KEV (kvs_kevI n mu))
                     (kvs_LS K (kvs_kI n mu)))
             (real_plus (real_plus c (real_mult kvs_omd kvs_board))
                        eps0)
             (real_plus kvs_board eps0)).
    + apply (real_le_trans _ _ _ Hstep).
      apply inr.
      apply (real_eq_trans
               (real_plus (real_plus (real_mult kvs_omd kvs_board)
                          (kvs_h2 eps0))
                     (real_plus c (kvs_h2 eps0)))
               (real_plus (real_plus c (real_mult kvs_omd kvs_board))
                          eps0)
               (real_plus (real_plus c (real_mult kvs_omd kvs_board))
                          eps0)).
      * apply (real_eq_trans
                 (real_plus (real_plus (real_mult kvs_omd kvs_board)
                            (kvs_h2 eps0))
                       (real_plus c (kvs_h2 eps0)))
                 (real_plus
                    (real_plus (real_mult kvs_omd kvs_board) c)
                    (real_plus (kvs_h2 eps0) (kvs_h2 eps0)))
                 (real_plus (real_plus c (real_mult kvs_omd kvs_board))
                            eps0)).
        -- exact (kv_regroup4 (real_mult kvs_omd kvs_board) (kvs_h2 eps0)
                     c (kvs_h2 eps0)).
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_plus (real_mult kvs_omd kvs_board) c)
                     (real_plus (kvs_h2 eps0) (kvs_h2 eps0))
                     (real_plus c (real_mult kvs_omd kvs_board))
                     eps0
                     (real_plus_comm (real_mult kvs_omd kvs_board) c)
                     (kvs_two_shares eps0)).
      * apply real_eq_refl.
    + apply inr.
      apply (RealSetoid.real_eq_plus_compat
                 (real_plus c (real_mult kvs_omd kvs_board)) eps0
                 kvs_board eps0 kvs_board_eq (real_eq_refl _)).
Qed.

(* ===================== 主定理：Doeblin 饱和形 ========================
   双支 And（构造性 min-glb：min 定义展开双支的宿主口径——库内无 Real 层
   total min，双支同时成立即 "D ≤ min(n·c, c/δ)" 的全部构造性内容）：
   支一（线性望远镜，金砖 kv_drift_bound 导出使用）：D ≤ n·c + ε；
   支二（几何饱和板，本件新数学）：D ≤ c/δ + ε——n→∞ 有界，线性界的
   几何紧化。 *)
Theorem kvs_drift_sat : forall (n : nat) (mu : Tok -> Real) (eps : Real),
  real_eq (real_list_sum Tok mu states) real_one ->
  (forall s : Tok, real_le real_zero (mu s)) ->
  real_lt real_zero eps ->
  And (real_le (kvs_DD (kvs_kevI n mu) (kvs_kI n mu))
               (real_plus (real_mult (real_of_nat n) c) eps))
      (real_le (kvs_DD (kvs_kevI n mu) (kvs_kI n mu))
               (real_plus kvs_board eps)).
Proof.
  intros n mu eps Hnorm Hnn Heps.
  split.
  - exact (kv_drift_bound Tok states states_ne K Krow Kpos keep
             keep_nonempty c Hrow n mu eps Hnorm Hnn Heps).
  - exact (kvs_drift_board n mu eps Hnorm Hnn Heps).
Qed.

(* tvL 同构形态（半和口径；kv_drift_bound_tv 的几何支对偶） *)
Theorem kvs_drift_sat_tv : forall (n : nat) (mu : Tok -> Real) (eps : Real),
  real_eq (real_list_sum Tok mu states) real_one ->
  (forall s : Tok, real_le real_zero (mu s)) ->
  real_lt real_zero eps ->
  real_le (tvL Tok states (kvs_kevI n mu) (kvs_kI n mu))
          (real_mult (real_inv_pos (real_plus real_one real_one)
                       kv_two_R_pos)
                     (real_plus kvs_board eps)).
Proof.
  intros n mu eps Hnorm Hnn Heps. unfold tvL.
  apply real_le_mult_compat_r.
  - apply real_le_from_lt_aux. apply real_inv_pos_pos.
  - exact (kvs_drift_board n mu eps Hnorm Hnn Heps).
Qed.

End KVSatDrift.

(* ===================== 取证与提取检验（可提取红线） ===================== *)
Print Assumptions kvs_step_contract.
Print Assumptions kvs_step_pair.
Print Assumptions kvs_drift_board.
Print Assumptions kvs_drift_sat.
Print Assumptions kvs_drift_sat_tv.

From Stdlib Require Import Extraction.
Extraction "kvsat_probe.ml" kvs_step_contract kvs_drift_board kvs_drift_sat.