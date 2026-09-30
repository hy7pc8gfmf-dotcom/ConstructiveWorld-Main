(* ==========================================================================)
   abl_arctan_diff_51.v — 9a-乙 主公式闭合续作（X51 形）         
   消融批 · 接续件 20/21/40/41/45 断点（②③已闭合，余=phi 步界件+装配）         
   ── 供给全景勘定·依赖清单（E12 实文判定）：───────────────────────────────────
   ②Real 桥已闭合：件 21（w 构造/投影/证书无关+wsq/wincr 桥两形+8/15 域证书）
     ＋件 40（abl9_slope_id_real 斜率合成恒等 Real 升层+D1 路线域证书）；
   ③N 等步链已闭合：件 41（nchain 引擎 12 件）＋件 45（const_chain 引擎）。
   ── 本片判定·数学使命（引擎不可定量使用，望远镜须自建）：──────────────────────
   件 41/45 链引擎的假设形=abl9_const_crit 形（∀eps eps'，单步 |Δphi| ≤
   eps·|s|+eps'）；固定 s≠0 时该假设⟹单步 real_eq（phi(a+s)==phi(a) 恰等）
   ——定量装配中单步恰等不成立（斜率恒等余项 s²x·inv(D₁D₂)≈(8/3)|s|²>0），
   故引擎仅当各步恰等已备时可用=纯组合件，定量望远镜（见证随 eps 取号+
   eps 松弛逐层传播）本片自建。残项判定：单步 |Δphi| ≤ c·|s|+余项
   (8/3)|s|²——余项不熄（固定 |s|），N 等步不可省（Σ 余项=(8/3)|h|²/N→0），
   N 随 eps 取号（q_arch_inv 阿基米德，S02:L1684 在库）。
   ── 本片交付·构造性注记（≤1h 断点纪律，绿一层登记一层）：───────────────────────
   A abl9_real_le_proj_sl：real_le 的逐点投影器（松弛形——real_le 的
     real_eq 支不产一致逐点 ≤，只产终近 <Y+e；两支统一为终近松弛形）；
   B abl9_chain_pt：Q 层定量望远镜（F: nat→Real 逐步终近 |Δ|<c+e 一致界 →
     端点 |F N−F 0|<(N)·c+e）——装配主链的使用基座；
   C0 abl9_pos_cert_gen：D1 路线正性证书一般 t 形（见证 (1/4,N_t) 显式——
     装配端点对齐的同见证术：real_inv_pos 投影早项=Qinv(D_N0) 仅依赖
     (e₀,N₀) 见证值；各证书同见证⟹投影逐 n 定义性相等⟹arg_wd N:=0 直通）
     ——X45「w 点早项硬墙」的装配侧处方落地件；
   C abl9_phi_step：phi 步界件（装配最后数学硬核，X45 §四·1 勘定案的交付）
     【本片推进中断点登记，见登记册§四】。
   ── 编译配方：──────────────────────────────────────────────────────────────
   source Live/toolchain/env.sh && bash cpu_guard.sh --
     rocq c -q -native-compiler no -Q /tmp/x51pool "" /tmp/x51pool/abl_arctan_diff_51.v
   （隔离池 /tmp/x51pool=x45pool 链真拷＋件 40 born-in-place 绿验
     EXIT=0/魔数 436f7121 00015ff4/vo 新于 v；件20/21/40/45 md5 与登记册
     认证值逐一 SAME：d8111457/c4fdf205/8499f3a9/0fc5d49d。cwd=/tmp/x51work
     异地空目录——承 X19'' 殁因勘定。Require 链退回 S11 单链，S12 出锥。）
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
Require Import abl_arctan_cert_bridge_21.
Require Import abl_arctan_diff_40.
Require Import abl_arctan_diff_45.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import ZArith Extraction.

(* ============================================================ *)
(* A·real_le 的终近松弛投影器                                        *)
(*   real_le X Y = real_lt X Y ⊕ real_eq X Y（S02:L472 Or 形）：        *)
(*   lt 支产正分离见证（终近 eps<Y−X）；eq 支只产终近 |X−Y|<e——       *)
(*   两支统一升为「终近 X_n < Y_n + e」（∀e>0 可达）——real_eq 支      *)
(*   不产一致逐点 ≤（早项有限偏离与 real_eq 相容），松弛形是诚实形。  *)
(* ============================================================ *)
Lemma abl9_real_le_proj_sl : forall (X Y : Real),
  real_le X Y ->
  forall e : Q, Qlt 0 e ->
  sigT (fun M : nat => forall n : nat, (M <= n)%nat ->
    Qlt (projT1 X n) (projT1 Y n + e)%Q).
Proof.
  intros X Y H e He.
  destruct H as [Hlt | Heq].
  - (* lt 支：正分离见证 eps → X_n ≤ Y_n − eps < Y_n + e *)
    destruct Hlt as [eps [Heps [N HN]]].
    exists N. intros n Hn.
    assert (Hsep : Qlt eps (projT1 Y n - projT1 X n))
      by (apply QltT_to_Qlt; exact (HN n (NatLe_lift _ _ Hn))).
    assert (Hlt1 : Qlt (projT1 X n) (projT1 Y n - eps)%Q)
      by (exact (q_lt_minus_shift eps (projT1 Y n) (projT1 X n) Hsep)).
    apply (Qlt_le_trans (projT1 X n) (projT1 Y n - eps)%Q (projT1 Y n + e)%Q).
    + exact Hlt1.
    + assert (Hle1 : Qle (projT1 Y n - eps) (projT1 Y n + e)%Q).
      { apply (Qplus_le_compat (projT1 Y n) (projT1 Y n) (- eps) e).
        - apply Qle_refl.
        - apply (Qle_trans (- eps) (- 0) e).
          + apply (Qopp_le_compat 0 eps). apply Qlt_le_weak.
            apply QltT_to_Qlt. exact Heps.
          + apply (Qle_trans (- 0) 0 e).
            * apply qeq_imp_qle. ring.
            * apply Qlt_le_weak. exact He. }
      exact Hle1.
  - (* eq 支：终近 |X−Y|<e 直接移项（X == Y+d ≤ Y+|d| < Y+e） *)
    destruct (Heq e (Qlt_to_QltT 0 e He)) as [N HN].
    exists N. intros n Hn.
    set (d := (projT1 X n - projT1 Y n)%Q).
    assert (Hab : QltT (Qabs d) e) by (exact (HN n (NatLe_lift _ _ Hn))).
    assert (Hdabs : Qle d (Qabs d)).
    { destruct (Qlt_le_dec 0 d) as [Hpd | Hnd].
      - apply qeq_imp_qle. apply Qeq_sym.
        exact (Qabs_pos d (Qlt_le_weak 0 d Hpd)).
      - apply (Qle_trans d 0 (Qabs d)).
        + exact Hnd.
        + apply Qabs_nonneg. }
    apply (Qle_lt_trans (projT1 X n) (projT1 Y n + Qabs d)%Q
             (projT1 Y n + e)%Q).
    + apply (Qle_trans (projT1 X n) (projT1 Y n + d) (projT1 Y n + Qabs d)).
      * apply qeq_imp_qle. unfold d. ring.
      * apply Qplus_le_compat. apply Qle_refl. exact Hdabs.
    + apply (proj2 (Qlt_minus_iff (projT1 Y n + Qabs d) (projT1 Y n + e)%Q)).
      apply (abl9_Qlt_transfer_r 0 (e - Qabs d)%Q
               ((projT1 Y n + e) - (projT1 Y n + Qabs d))%Q).
      * field.
      * apply (q_lt_minus_shift (Qabs d) e 0).
        apply (abl9_Qlt_transfer_r (Qabs d) e (e - 0)%Q).
        -- field.
        -- apply QltT_to_Qlt. exact Hab.
Qed.

(* ============================================================ *)
(* B·Q 层定量望远镜（装配主链基座）                                  *)
(*   逐步一致终近界 |F(S i)_n − F i_n| < c+e（见证随 i,e 取号）→        *)
(*   端点 |F N_n − F 0_n| < (Z.of_nat N #1)·c + e。                     *)
(*   件 41/45 引擎（const_crit 形假设）不可定量使用之代位——松弛逐层    *)
(*   传播：每步吃 e/2，归纳步合计恰 e。                                 *)
(* ============================================================ *)
Lemma abl9_chain_pt : forall (F : nat -> Real) (c : Q),
  (forall i : nat, forall e : Q, Qlt 0 e ->
     sigT (fun M : nat => forall n : nat, (M <= n)%nat ->
       QltT (Qabs (projT1 (F (Datatypes.S i)) n - projT1 (F i) n))
            (c + e)%Q)) ->
  forall (N : nat) (e : Q), Qlt 0 e ->
  sigT (fun M : nat => forall n : nat, (M <= n)%nat ->
    QltT (Qabs (projT1 (F N) n - projT1 (F 0%nat) n))
         ((Z.of_nat N # 1) * c + e)%Q).
Proof.
  intros F c Hstep N.
  induction N as [| N IH].
  - intros e He. exists 0%nat. intros n Hn.
    (* |F 0_n − F 0_n| == 0 < 0·c + e == e *)
    assert (Hz : projT1 (F 0%nat) n - projT1 (F 0%nat) n == 0) by ring.
    assert (Hr : ((Z.of_nat 0 # 1) * c + e == e)%Q) by field.
    assert (Hab : Qabs (projT1 (F 0%nat) n - projT1 (F 0%nat) n) == 0)
      by (exact (abl9_Qabs_wd _ _ Hz)).
    apply abl9_QltT_transfer_l with (x := 0%Q)
      (y := Qabs (projT1 (F 0%nat) n - projT1 (F 0%nat) n)).
    + apply Qeq_sym. exact Hab.
    + apply abl9_QltT_transfer_r with (x := 0%Q) (y := e%Q).
      * apply Qeq_sym. exact Hr.
      * apply Qlt_to_QltT. exact He.
  - intros e He.
    assert (Heh : Qlt 0 (e / 2)%Q).
    { unfold Qdiv. apply Qmult_lt_0_compat.
      - exact He.
      - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
    destruct (IH (e / 2)%Q Heh) as [M1 HM1].
    destruct (Hstep N (e / 2)%Q Heh) as [M2 HM2].
    exists (Nat.max M1 M2). intros n Hn.
    assert (Hn1 : (M1 <= n)%nat) by lia.
    assert (Hn2 : (M2 <= n)%nat) by lia.
    (* 分解环等：F(S N)−F 0 == (F(S N)−F N)+(F N−F 0) *)
    assert (Hring : projT1 (F (Datatypes.S N)) n - projT1 (F 0%nat) n
                    == (projT1 (F (Datatypes.S N)) n - projT1 (F N) n)
                       + (projT1 (F N) n - projT1 (F 0%nat) n)) by ring.
    assert (Htri : Qle (Qabs (projT1 (F (Datatypes.S N)) n
                               - projT1 (F 0%nat) n))
                       (Qabs (projT1 (F (Datatypes.S N)) n
                                 - projT1 (F N) n)
                        + Qabs (projT1 (F N) n - projT1 (F 0%nat) n))).
    { rewrite Hring. apply Qabs_triangle. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (projT1 (F (Datatypes.S N)) n
                                - projT1 (F 0%nat) n))
                        (Qabs (projT1 (F (Datatypes.S N)) n
                                  - projT1 (F N) n)
                         + Qabs (projT1 (F N) n - projT1 (F 0%nat) n))
                        ((Z.of_nat (Datatypes.S N) # 1) * c + e)%Q).
    + exact Htri.
    + apply (Qlt_le_trans
               (Qabs (projT1 (F (Datatypes.S N)) n - projT1 (F N) n)
                + Qabs (projT1 (F N) n - projT1 (F 0%nat) n))%Q
               (c + e / 2 + ((Z.of_nat N # 1) * c + e / 2))%Q
               ((Z.of_nat (Datatypes.S N) # 1) * c + e)%Q).
      * apply (Qplus_lt_compat
                 (Qabs (projT1 (F (Datatypes.S N)) n - projT1 (F N) n))
                 (c + e / 2)%Q
                 (Qabs (projT1 (F N) n - projT1 (F 0%nat) n))
                 ((Z.of_nat N # 1) * c + e / 2)%Q).
        -- apply QltT_to_Qlt. exact (HM2 n Hn2).
        -- apply QltT_to_Qlt. exact (HM1 n Hn1).
      * (* c + e/2 + (Z N)#1·c + e/2 == (Z (S N))#1·c + e 恰等 → Qle *)
        assert (Heq : (c + e / 2 + ((Z.of_nat N # 1) * c + e / 2)
                       == (Z.of_nat (Datatypes.S N) # 1) * c + e)%Q).
        { assert (Hzs : ((Z.of_nat (Datatypes.S N) # 1)
                         == (Z.of_nat N # 1) + 1)%Q).
          { unfold Qeq; cbn; lia. }
          rewrite Hzs. field. }
        apply qeq_imp_qle. exact Heq.
Qed.

(* ============================================================ *)
(* C0·D1 路线正性证书（一般 t 形，见证 (1/4, N_t) 显式透传）          *)
(*   与 abl9_Hcert_real（件 45，端点形，见证 (1/2,N_h)）互补：          *)
(*   本件见证取 Ht4 之见证 N（装配以同见证手组诸 Ht4 ⟹ 诸证书         *)
(*   同见证 ⟹ real_inv_pos 投影逐 n 定义性相等——端点对齐术基座）。    *)
(* ============================================================ *)
Lemma abl9_pos_cert_gen : forall (x t : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Ht4 : real_lt (real_abs t) (real_const (1 # 4))),
  real_lt real_zero (real_plus real_one (real_mult (real_plus x t) x)).
Proof.
  intros x t Hx Ht4.
  destruct Ht4 as [e [He [N HN]]].
  exists (1 # 4). split.
  - assert (Hq : Qlt 0 (1 # 4)) by (unfold Qlt; simpl; lia).
    apply Qlt_to_QltT. exact Hq.
  - exists N. intros n Hn.
    assert (Hlt1 : Qlt e (Qminus (projT1 (real_const (1 # 4)) n)
                                  (projT1 (real_abs t) n)))
      by (apply QltT_to_Qlt; exact (HN n Hn)).
    rewrite (real_const_proj (1 # 4) n) in Hlt1.
    rewrite (real_abs_proj t n) in Hlt1.
    assert (Hlt2 : Qlt (Qabs (projT1 t n)) ((1 # 4) - e))
      by (exact (q_lt_minus_shift e (1 # 4) (Qabs (projT1 t n)) Hlt1)).
    assert (Htn4 : Qle (Qabs (projT1 t n)) (1 # 4)).
    { apply (Qle_trans (Qabs (projT1 t n)) ((1 # 4) - e) (1 # 4)).
      - apply Qlt_le_weak. exact Hlt2.
      - assert (He0 : Qle 0 e) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact He).
        apply (Qle_trans ((1 # 4) - e) (((1 # 4) - e) + 0) (1 # 4)).
        + apply qeq_imp_qle. ring.
        + apply (Qle_trans (((1 # 4) - e) + 0) (((1 # 4) - e) + e) (1 # 4)).
          * apply Qplus_le_compat. apply Qle_refl. exact He0.
          * apply qeq_imp_qle. ring. }
    assert (Hxa : Qle (Qabs (projT1 x n)) 1)
      by (apply (QleT'_to_Qle (Qabs (projT1 x n)) 1); exact (Hx n)).
    pose proof (abl9_q_path_den (projT1 x n) (projT1 t n) Hxa Htn4) as Hd.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (1 # 4) (3 # 4)
             (Qminus (projT1 (real_plus real_one
                         (real_mult (real_plus x t) x)) n)
                     (projT1 real_zero n))).
    + unfold Qlt. simpl. lia.
    + assert (HY : projT1 (real_plus real_one (real_mult (real_plus x t) x)) n
                   == 1 + (projT1 x n + projT1 t n) * projT1 x n).
      { rewrite (real_plus_proj real_one (real_mult (real_plus x t) x) n).
        rewrite (real_mult_proj (real_plus x t) x n).
        rewrite (real_plus_proj x t n).
        rewrite (b3r_one_proj n). reflexivity. }
      assert (H0 : Qminus (projT1 (real_plus real_one
                             (real_mult (real_plus x t) x)) n)
                    (projT1 real_zero n)
                   == 1 + (projT1 x n + projT1 t n) * projT1 x n).
      { rewrite HY. cbn [projT1 real_zero]. ring. }
      apply (Qle_trans (3 # 4) (1 + (projT1 x n + projT1 t n) * projT1 x n)
             (Qminus (projT1 (real_plus real_one
                         (real_mult (real_plus x t) x)) n)
                     (projT1 real_zero n))).
      * exact (QleT'_to_Qle (3 # 4)
                 (1 + (projT1 x n + projT1 t n) * projT1 x n) Hd).
      * apply qeq_imp_qle. apply Qeq_sym. exact H0.
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验（Stage A/B/C0 三件）                       *)
(* ============================================================ *)
Print Assumptions abl9_real_le_proj_sl.
Print Assumptions abl9_chain_pt.
Print Assumptions abl9_pos_cert_gen.

Recursive Extraction abl9_real_le_proj_sl abl9_chain_pt abl9_pos_cert_gen.
