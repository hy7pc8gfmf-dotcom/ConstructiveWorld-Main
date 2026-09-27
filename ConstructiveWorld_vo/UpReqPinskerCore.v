(* ==========================================================================)
   UpReqPinskerCore.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：w2t_q_p4、w2t_q_ep_mono、w2t_q_ep4、w2t_q_decay4、w2t_q_tail_struct、w2t_q_tail12、w2t_q_t4_nonneg、w2t_q_plus_le_r、w2t_q_exppartial_bound。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
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
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpRealLeB.
From Stdlib Require Import Lqa.
Require Import G07_KLWall.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import PinskerTwoPoint.
From Stdlib Require Import Lia.

(* ================= §1 w2t_q_p4 族 ================= *)
From Stdlib Require Import QArith.Qring QArith.Qabs Arith.Arith Lia.

(* Section 1：Q 层尾残差引擎（Real 层件的逐点内核）                    *)

(* Q 目标多项式：1 + t + (1/2)t² + (1/6)t³ + (1/8)t⁴（显式乘积形） *)
Definition w2t_q_p4 (t : Q) : Q :=
  (1 + t + (1#2) * (t * t) + (1#6) * (t * (t * t))
     + (1#8) * (t * (t * (t * t))))%Q.

(* 引擎 1a：exp_partial 对 n 单调（t ≥ 0） *)
Lemma w2t_q_ep_mono : forall (t : Q) (n m : nat),
  Qle 0 t -> (n <= m)%nat -> Qle (exp_partial n t) (exp_partial m t).
Proof.
  intros t n m Ht Hnm.
  induction m as [| m IH].
  - assert (Hn0 : n = 0%nat) by lia. subst n. apply Qle_refl.
  - destruct (Nat.eq_dec n (Datatypes.S m)) as [Heq | Hne].
    + subst n. apply Qle_refl.
    + assert (Hle : (n <= m)%nat) by lia.
      apply (Qle_trans _ (exp_partial m t)).
      * exact (IH Hle).
      * change (exp_partial (Datatypes.S m) t)
          with (exp_partial m t + q_pow t (Datatypes.S m) / q_fact (Datatypes.S m)).
        apply (Qle_trans _ (exp_partial m t + 0)).
        -- apply qeq_le. ring.
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply (q_pow_fact_nonneg t (Datatypes.S m)). exact Ht.
Qed.

(* 引擎 1b：exp_partial 4 的显式形状 *)
Lemma w2t_q_ep4 : forall t : Q,
  exp_partial 4 t ==
  (1 + t + (1#2) * (t * t) + (1#6) * (t * (t * t))
     + (1#24) * (t * (t * (t * t))))%Q.
Proof.
  intro t.
  change (exp_partial 4 t)
    with (exp_partial 3 t + q_pow t 4 / q_fact 4).
  change (exp_partial 3 t)
    with (exp_partial 2 t + q_pow t 3 / q_fact 3).
  change (exp_partial 2 t)
    with (exp_partial 1 t + q_pow t 2 / q_fact 2).
  change (exp_partial 1 t)
    with (exp_partial 0 t + q_pow t 1 / q_fact 1).
  change (exp_partial 0 t) with 1%Q.
  assert (Hf1 : q_fact 1 == (1#1)) by reflexivity.
  assert (Hf2 : q_fact 2 == (2#1)) by reflexivity.
  assert (Hf3 : q_fact 3 == (6#1)) by reflexivity.
  assert (Hf4 : q_fact 4 == (24#1)) by reflexivity.
  rewrite Hf1, Hf2, Hf3, Hf4.
  cbn [q_pow].
  unfold Qdiv.
  cbn [Qinv].
  field.
Qed.

(* 引擎 1c：衰减条件（t ≤ 1 ⟹ 2t ≤ u+1 对 u ≥ 4） *)
Lemma w2t_q_decay4 : forall (t : Q),
  Qle t 1 -> forall u : nat, (4 <= u)%nat -> Qle (2 * t) (Z.of_nat (u + 1) # 1).
Proof.
  intros t H1 u Hu.
  assert (H2 : Qle (t * 2) (1 * 2))
    by (apply (Qmult_le_compat_r t 1 2);
        [exact H1 | unfold Qle; cbn [Qnum Qden]; lia]).
  apply (Qle_trans _ (2 * 1)%Q).
  - assert (Hc : (2 * t == t * 2)%Q) by ring.
    assert (Hc2 : (2 * 1 == 1 * 2)%Q) by ring.
    rewrite Hc, Hc2.
    exact H2.
  - rewrite Qmult_1_r.
    unfold Qle. cbn [Qnum Qden].
    assert (Hz : (2 <= Z.of_nat (u + 1))%Z) by lia.
    lia.
Qed.

(* 引擎 1d-0：exp_tail 与 exp_tail_abs 结构同型（无前提） *)
Lemma w2t_q_tail_struct : forall (m n : nat) (x : Q),
  exp_tail m n x == exp_tail_abs m n x.
Proof.
  intros m n x.
  induction n as [| n IH].
  - reflexivity.
  - change (exp_tail m (Datatypes.S n) x)
      with (exp_tail m n x + (if Nat.leb m n then q_pow x (Datatypes.S n) / q_fact (Datatypes.S n) else 0)).
    change (exp_tail_abs m (Datatypes.S n) x)
      with (exp_tail_abs m n x + (if Nat.leb m n then q_pow x (Datatypes.S n) / q_fact (Datatypes.S n) else 0)).
    rewrite IH. reflexivity.
Qed.

(* 引擎 1d：尾和 ≤ (1/12)·t⁴（0 ≤ t ≤ 1） *)
Lemma w2t_q_tail12 : forall (t : Q) (n : nat),
  Qle 0 t -> Qle t 1 -> Qle (exp_tail 4 n t) ((1#12) * (t * (t * (t * t)))).
Proof.
  intros t n H0 H1.
  assert (Hp4 : q_pow t 4 == (t * (t * (t * t)))%Q) by (cbn [q_pow]; ring).
  assert (Hnn : Qle 0 ((1#12) * (t * (t * (t * t))))).
  { apply (Qmult_le_0_compat (1#12) (t * (t * (t * t)))).
    - unfold Qle. cbn [Qnum Qden]. lia.
    - rewrite <- Hp4. apply (q_pow_nonneg t 4). exact H0. }
  destruct (Nat.leb_spec 4 n) as [H41 | H14].
  - apply (Qle_trans _ (exp_tail_abs 4 n t)).
    + apply qeq_le. apply (w2t_q_tail_struct 4 n t).
    + apply (Qle_trans _ ((q_pow t 4 / q_fact 4) * (1 + 1)%Q)).
      * apply (exp_tail_abs_geom2 t 4 n H0 (w2t_q_decay4 t H1) H41).
      * assert (Hf4 : q_fact 4 == (24#1)) by reflexivity.
        rewrite Hp4, Hf4.
        assert (Heq : ((t * (t * (t * t)) / (24#1)) * (1 + 1)%Q ==
                       (1#12) * (t * (t * (t * t))))%Q).
        { unfold Qdiv. cbn [Qinv]. field. }
        apply qeq_le. exact Heq.
  - assert (Hn4 : (n <= 4)%nat) by lia.
    rewrite (exp_tail_le_m 4 n t Hn4).
    exact Hnn.
Qed.

(* Q 小件：t⁴ 非负（nia 数值区） *)
Lemma w2t_q_t4_nonneg : forall t : Q, Qle 0 t -> Qle 0 (t * (t * (t * t))).
Proof.
  intros t H.
  apply (Qmult_le_0_compat t (t * (t * t))).
  - exact H.
  - apply (Qmult_le_0_compat t (t * t)).
    + exact H.
    + apply (Qmult_le_0_compat t t).
      * exact H.
      * exact H.
Qed.

(* Q 小件：右加保序（显式参，消 Qplus_le_compat 分裂歧义） *)
Lemma w2t_q_plus_le_r : forall (a b c : Q),
  Qle a b -> Qle (c + a) (c + b).
Proof.
  intros a b c H.
  apply Qplus_le_compat.
  - apply Qle_refl.
  - exact H.
Qed.

(* 引擎 1e（Q 主件）：exp 部分和 ≤ 显式多项式（0 ≤ t ≤ 1，全体 n） *)
Lemma w2t_q_exppartial_bound : forall (t : Q) (n : nat),
  Qle 0 t -> Qle t 1 -> Qle (exp_partial n t) (w2t_q_p4 t).
Proof.
  intros t n H0 H1.
  destruct (Nat.leb_spec n 4) as [Hn4 | H4n].
  - apply (Qle_trans _ (exp_partial 4 t)).
    + apply (w2t_q_ep_mono t n 4 H0 Hn4).
    + rewrite (w2t_q_ep4 t).
      apply (w2t_q_plus_le_r
               ((1#24) * (t * (t * (t * t))))%Q
               ((1#8) * (t * (t * (t * t))))%Q
               (1 + t + (1#2) * (t * t) + (1#6) * (t * (t * t)))%Q).
      * apply (Qmult_le_compat_r ((1#24)%Q) ((1#8)%Q) (t * (t * (t * t)))).
        -- unfold Qle. cbn [Qnum Qden]. lia.
        -- apply w2t_q_t4_nonneg. exact H0.
  - assert (H45 : (4 <= n)%nat) by lia.
    assert (Hsplit : exp_partial n t == exp_partial 4 t + exp_tail 4 n t).
    { pose proof (exp_partial_diff_tail 4 n t H45) as Hd.
      symmetry. rewrite <- Hd. ring. }
    rewrite Hsplit.
    rewrite (w2t_q_ep4 t).
    apply (Qle_trans _ (1 + t + (1#2) * (t * t) + (1#6) * (t * (t * t))
                           + (1#24) * (t * (t * (t * t)))
                           + (1#12) * (t * (t * (t * t))))%Q).
    + apply (w2t_q_plus_le_r
               (exp_tail 4 n t)
               ((1#12) * (t * (t * (t * t))))%Q
               (1 + t + (1#2) * (t * t) + (1#6) * (t * (t * t))
                  + (1#24) * (t * (t * (t * t))))%Q).
      * exact (w2t_q_tail12 t n H0 H1).
    + unfold w2t_q_p4.
      assert (Heq : (1 + t + (1#2) * (t * t) + (1#6) * (t * (t * t))
                       + (1#24) * (t * (t * (t * t)))
                       + (1#12) * (t * (t * (t * t))) ==
                     1 + t + (1#2) * (t * t) + (1#6) * (t * (t * t))
                       + (1#8) * (t * (t * (t * t))))%Q) by ring.
      apply qeq_le. exact Heq.
Qed.

(* Q 小件：半系数序（nia 数值区） *)
Lemma w2t_q_half_lt : forall x y : Q, Qlt x y -> Qlt ((1#2) * x) ((1#2) * y).
Proof.
  intros x y H.
  rewrite (Qmult_comm (1#2) x), (Qmult_comm (1#2) y).
  apply (Qmult_lt_compat_r x y (1#2)).
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - exact H.
Qed.

Lemma w2t_q_half_pos : forall x : Q, Qlt 0 x -> Qlt 0 ((1#2) * x).
Proof.
  intros x H.
  apply (Qmult_lt_0_compat (1#2) x).
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - exact H.
Qed.
(* Section 2：Real 层 exp 上界尾残差件（target 2 主件）                *)

Definition w2t_c_half : Real := real_const (1#2).
Definition w2t_c_six : Real := real_const (1#6).
Definition w2t_c_eight : Real := real_const (1#8).

(* Real 层上界多项式 P(t) := 1 + t + (1/2)t² + (1/6)t³ + (1/8)t⁴ *)
Definition w2t_exp_bound (t : Real) : Real :=
  real_plus real_one (real_plus t
    (real_plus (real_mult w2t_c_half (real_mult t t))
      (real_plus (real_mult w2t_c_six (real_mult t (real_mult t t)))
                 (real_mult w2t_c_eight
                    (real_mult (real_mult t t) (real_mult t t)))))).

(* 投影引理：P(t) 逐点 = Q 层 p4 *)
Lemma w2t_exp_bound_proj : forall (t : Real) (n : nat),
  projT1 (w2t_exp_bound t) n ==
  (1 + projT1 t n + (1#2) * (projT1 t n * projT1 t n)
     + (1#6) * (projT1 t n * (projT1 t n * projT1 t n))
     + (1#8) * (projT1 t n * (projT1 t n * (projT1 t n * projT1 t n))))%Q.
Proof.
  intros t n.
  unfold w2t_exp_bound, w2t_c_half, w2t_c_six, w2t_c_eight.
  rewrite (real_plus_proj real_one
            (real_plus t
              (real_plus (real_mult w2t_c_half (real_mult t t))
                (real_plus (real_mult w2t_c_six (real_mult t (real_mult t t)))
                           (real_mult w2t_c_eight
                              (real_mult (real_mult t t) (real_mult t t))))))
            n).
  rewrite (real_plus_proj t
            (real_plus (real_mult w2t_c_half (real_mult t t))
              (real_plus (real_mult w2t_c_six (real_mult t (real_mult t t)))
                         (real_mult w2t_c_eight
                            (real_mult (real_mult t t) (real_mult t t)))))
            n).
  rewrite (real_plus_proj (real_mult w2t_c_half (real_mult t t))
            (real_plus (real_mult w2t_c_six (real_mult t (real_mult t t)))
                       (real_mult w2t_c_eight
                          (real_mult (real_mult t t) (real_mult t t))))
            n).
  rewrite (real_plus_proj (real_mult w2t_c_six (real_mult t (real_mult t t)))
                          (real_mult w2t_c_eight
                             (real_mult (real_mult t t) (real_mult t t)))
            n).
  rewrite (real_mult_proj (real_const (1#2)) (real_mult t t) n).
  rewrite (real_mult_proj (real_const (1#6)) (real_mult t (real_mult t t)) n).
  rewrite (real_mult_proj (real_const (1#8)) (real_mult (real_mult t t) (real_mult t t)) n).
  rewrite (real_const_proj (1#2) n).
  rewrite (real_const_proj (1#6) n).
  rewrite (real_const_proj (1#8) n).
  rewrite (real_mult_proj t t n).
  rewrite (real_mult_proj t (real_mult t t) n).
  rewrite (real_mult_proj t t n).
  rewrite (real_mult_proj (real_mult t t) (real_mult t t) n).
  rewrite (real_mult_proj t t n).
  assert (H1 : projT1 real_one n == 1%Q) by reflexivity.
  rewrite H1.
  field.
Qed.

(* cauchy_real_exp 投影（定义性） *)
Lemma w2t_cexp_proj : forall (u : Qseq) (Hu : cauchy u) (n : nat),
  projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) n
  == exp_partial n (u n).
Proof. intros u Hu n. reflexivity. Qed.

(* wd：P 对 real_eq 兼容 *)
Lemma w2t_exp_bound_wd : forall t s : Real,
  real_eq t s -> real_eq (w2t_exp_bound t) (w2t_exp_bound s).
Proof.
  intros t s Hts.
  unfold w2t_exp_bound.
  assert (E1 : real_eq (real_mult t t) (real_mult s s))
    by (apply RealSetoid.real_eq_mult_compat; exact Hts).
  assert (E2 : real_eq (real_mult t (real_mult t t))
                       (real_mult s (real_mult s s)))
    by (apply RealSetoid.real_eq_mult_compat; [exact Hts | exact E1]).
  assert (E3 : real_eq (real_mult (real_mult t t) (real_mult t t))
                       (real_mult (real_mult s s) (real_mult s s)))
    by (apply RealSetoid.real_eq_mult_compat; exact E1).
  assert (E4 : real_eq (real_mult w2t_c_half (real_mult t t))
                       (real_mult w2t_c_half (real_mult s s)))
    by (apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl | exact E1]).
  assert (E5 : real_eq (real_mult w2t_c_six (real_mult t (real_mult t t)))
                       (real_mult w2t_c_six (real_mult s (real_mult s s))))
    by (apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl | exact E2]).
  assert (E6 : real_eq (real_mult w2t_c_eight
                          (real_mult (real_mult t t) (real_mult t t)))
                       (real_mult w2t_c_eight
                          (real_mult (real_mult s s) (real_mult s s))))
    by (apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl | exact E3]).
  assert (E7 : real_eq
                 (real_plus (real_mult w2t_c_six (real_mult t (real_mult t t)))
                            (real_mult w2t_c_eight
                               (real_mult (real_mult t t) (real_mult t t))))
                 (real_plus (real_mult w2t_c_six (real_mult s (real_mult s s)))
                            (real_mult w2t_c_eight
                               (real_mult (real_mult s s) (real_mult s s)))))
    by (apply RealSetoid.real_eq_plus_compat; [exact E5 | exact E6]).
  apply RealSetoid.real_eq_plus_compat.
  - apply real_eq_refl.
  - apply RealSetoid.real_eq_plus_compat.
    + exact Hts.
    + apply RealSetoid.real_eq_plus_compat.
      * exact E4.
      * exact E7.
Qed.

Lemma w2t_exp_bound_zero : real_eq (w2t_exp_bound real_zero) real_one.
Proof.
  intros eps Heps.
  exists 0%nat. intros n Hn.
  apply (qltT_eq_compat_l
          (Qabs (w2t_q_p4 (projT1 real_zero n) - projT1 real_one n))).
  - assert (Hm : (projT1 (w2t_exp_bound real_zero) n - projT1 real_one n ==
                  w2t_q_p4 (projT1 real_zero n) - projT1 real_one n)%Q).
    { rewrite (w2t_exp_bound_proj real_zero n). unfold w2t_q_p4. ring. }
    apply Qabs_wd. exact Hm.
  - replace (projT1 real_zero n) with 0%Q by reflexivity.
    replace (projT1 real_one n) with 1%Q by reflexivity.
    assert (Hq : w2t_q_p4 0 == 1%Q) by (unfold w2t_q_p4; cbn [q_pow]; field).
    apply (qltT_eq_compat_l (Qabs (1 - 1))).
    + apply Qabs_wd.
      rewrite Hq. reflexivity.
    + replace (Qabs (1 - 1)) with 0 by reflexivity.
      exact Heps.
Qed.

(* Real 小件：lt 加法右保序 *)
Lemma w2t_lt_plus_compat_r : forall (a b c : Real),
  real_lt a b -> real_lt (real_plus c a) (real_plus c b).
Proof.
  intros a b c Hlt.
  destruct Hlt as [eps [Heps [N HN]]].
  unfold real_lt.
  exists eps. split.
  - exact Heps.
  - exists N. intros n Hn.
    specialize (HN n Hn).
    apply (qltT_eq_compat_r
            (projT1 (real_plus c b) n - projT1 (real_plus c a) n)%Q
            (projT1 b n - projT1 a n)%Q eps).
    + rewrite (real_plus_proj c b n), (real_plus_proj c a n). ring.
    + exact HN.
Qed.

(* 本段界线：以上为已验证件。                      *)
(* 未竟清单（详见交付档案）：     *)
(*   w2t_half_pos / w2t_half_lt / w2t_exp_upper_ptw /            *)
(*   w2t_exp_upper_one / w2t_exp_upper_transport / w2t_exp_upper *)
(*   —— 语句面已定稿（见报告 §伤单），全部卡在 real_lt 逐点        *)
(*   witness 样板与 Qeq→QltT 运输（无态射实例）的平台摩擦，        *)
(*   非数学缺口；Q 引擎（Section 1）全链闭合。                    *)

(* Section 3（纯追加）：target1 log 界对 + target3 trunc5 桥   *)
(*   + 三堵样板墙拆除件。前缀 w2t_ 延续；公理面零新增；              *)
(*   全部声明在本注释框之后追加，既有行零改动。                      *)
(*   路线（对 _tw2_ 报告 §四/§六 的落地化）：                         *)
(*   · (★) exp(t−t²/2) ≤_B 1+t：逐点 witness 直构——Q 层引擎 1e 施于   *)
(*     s := t−t²/2 + 余量引理 P4(s) ≤ 1+t（差 = t³/4 − 7s³/24 阶，    *)
(*     经 t²(t+s)/4 ≥ s³/2 精确闭），Or 前件 eq 支走 exp_wd/exp_zero  *)
(*     纯运输（免逐点级数分析）；                                    *)
(*   · 反射：log 严格单调 + log/exp 双侧逆 + γ-隙逐点严格化；          *)
(*   · trunc5 桥：log(1−y) = log((1−y)(1+y)) − log(1+y) 恒等式分解    *)
(*     + 上切线 real_log_le_linear_B 实例 + target1 实例。            *)


(* ---------------- 3.a Q 层内核件 ---------------- *)

(* Q 小件：平方非负（无前提） *)
Lemma w2t_q_sq_nonneg : forall t : Q, Qle 0 (t * t).
Proof.
  intro t. destruct (Qlt_le_dec 0 t) as [H | H].
  - apply (Qmult_le_0_compat t t).
    + apply Qlt_le_weak. exact H.
    + apply Qlt_le_weak. exact H.
  - assert (Hn : Qle 0 (- t)).
    { apply (Qle_trans 0 (- 0) (- t)).
      - apply qeq_le. ring.
      - exact (Qopp_le_compat t 0 H). }
    apply (Qle_trans 0 ((- t) * (- t)) (t * t)).
    + apply (Qmult_le_0_compat (- t) (- t)); exact Hn.
    + apply qeq_le. ring.
Qed.

(* Q 小件：exp_partial 1 的显式形 *)
Lemma w2t_q_ep1 : forall g : Q, exp_partial 1 g == (1 + g)%Q.
Proof.
  intro g.
  change (exp_partial 1 g) with (exp_partial 0 g + q_pow g 1 / q_fact 1).
  change (exp_partial 0 g) with 1%Q.
  assert (Hf1 : q_fact 1 == (1#1)) by reflexivity.
  rewrite Hf1.
  cbn [q_pow].
  unfold Qdiv. cbn [Qinv].
  field.
Qed.

(* Q 小件：exp ≥ 1 + g（g ≥ 0，n ≥ 1）——exp≥1+t 桥接件的 Q 内核 *)
Lemma w2t_q_ep_ge_1plus : forall (g : Q) (n : nat),
  Qle 0 g -> (1 <= n)%nat -> Qle (1 + g) (exp_partial n g).
Proof.
  intros g n H0 H1.
  apply (Qle_trans _ (exp_partial 1 g)).
  - rewrite (w2t_q_ep1 g). apply Qle_refl.
  - exact (w2t_q_ep_mono g 1 n H0 H1).
Qed.

(* Q 小件：a ≤ b ⟹ 0 ≤ b − a *)
Lemma w2t_q_sub_nonneg : forall a b : Q, Qle a b -> Qle 0 (b - a).
Proof.
  intros a b H.
  apply (Qle_trans 0 (a + -a) (b - a)).
  - assert (Hz : (a + -a == 0)%Q) by ring.
    rewrite Hz. apply Qle_refl.
  - apply (Qplus_le_compat a b (-a) (-a)); [exact H | apply Qle_refl].
Qed.

(* Q 小件：0 ≤ b − a ⟹ a ≤ b *)
Lemma w2t_q_le_sub : forall a b : Q, Qle 0 (b - a) -> Qle a b.
Proof.
  intros a b H.
  apply (Qle_trans a (a + (b - a)) b).
  - apply (Qle_trans a (a + 0%Q) (a + (b - a))).
    + apply qeq_le. ring.
    + apply (w2t_q_plus_le_r 0 (b - a) a). exact H.
  - apply qeq_le. ring.
Qed.

(* Q 小件：s := t − t²/2 ≤ t（无条件） *)
Lemma w2t_q_s_le_t : forall t : Q, Qle (t - (1#2)*(t*t)) t.
Proof.
  intro t.
  apply w2t_q_le_sub.
  apply (Qle_trans 0 ((1#2)*(t*t)) (t - (t - (1#2)*(t*t)))).
  - apply (Qmult_le_0_compat (1#2)%Q (t*t)%Q).
    + unfold Qle. cbn [Qnum Qden]. lia.
    + apply w2t_q_sq_nonneg.
  - apply qeq_le. ring.
Qed.

(* Q 小件：s := t − t²/2 ≤ 1（无条件：差 = ((t−1)²+1)/2） *)
Lemma w2t_q_s_le_1 : forall t : Q, Qle (t - (1#2)*(t*t)) 1.
Proof.
  intro t.
  apply w2t_q_le_sub.
  assert (Hsq : Qle 0 ((t - 1) * (t - 1))) by apply w2t_q_sq_nonneg.
  assert (Hsum : Qle 0 ((t - 1) * (t - 1) + 1)).
  { apply (Qle_trans 0 ((t-1)*(t-1)) ((t-1)*(t-1) + 1)).
    - exact Hsq.
    - apply (Qle_trans _ ((t-1)*(t-1) + 0%Q)).
      + apply qeq_le. ring.
      + apply (w2t_q_plus_le_r 0 1 ((t-1)*(t-1))).
        unfold Qle. cbn [Qnum Qden]. lia. }
  apply (Qle_trans 0 ((1#2)*((t-1)*(t-1) + 1))%Q).
  - apply (Qmult_le_0_compat (1#2)).
    + unfold Qle. cbn [Qnum Qden]. lia.
    + exact Hsum.
  - apply qeq_le. ring.
Qed.

(* Q 小件：s := t − t²/2 ≥ 0（0 ≤ t ≤ 2：s = t(2−t)/2） *)
Lemma w2t_q_s_nonneg : forall t : Q,
  Qle 0 t -> Qle t 2 -> Qle 0 (t - (1#2)*(t*t)).
Proof.
  intros t H0 H2.
  apply w2t_q_sub_nonneg.
  apply (Qle_trans ((1#2)*(t*t)) ((t*t)*(1#2)) t).
  - apply qeq_le. ring.
  - apply (Qle_trans ((t*t)*(1#2)) ((2*t)*(1#2)) t).
    + apply (Qmult_le_compat_r (t*t) (2*t) (1#2)%Q).
      * apply (Qmult_le_compat_r t 2 t); [exact H2 | exact H0].
      * unfold Qle. cbn [Qnum Qden]. lia.
    + apply qeq_le. ring.
Qed.

(* Q 小件：左乘保序（0 ≤ c、x ≤ y ⟹ c·x ≤ c·y） *)
Lemma w2t_q_mult_le_l : forall c x y : Q, Qle 0 c -> Qle x y -> Qle (c*x) (c*y).
Proof.
  intros c x y Hc Hxy.
  apply (Qle_trans (c*x) (x*c) (c*y)).
  - apply qeq_le. ring.
  - apply (Qle_trans (x*c) (y*c) (c*y)).
    + apply (Qmult_le_compat_r x y c); [exact Hxy | exact Hc].
    + apply qeq_le. ring.
Qed.

(* Q 关键余量引理：P4(s) ≤ 1 + t（s := t − t²/2，0 ≤ t ≤ 2）。
   差式 D = t²/2 − s²/2 − s³/6 − s⁴/8 = t²(t+s)/4 − s³(4+3s)/24，
   下界链：t²(t+s)/4 ≥ t²·2s/4 = t²s/2 ≥ s³/2；
   s³(4+3s)/24 ≤ s³·7/24 ≤ s³/2（s ≤ 1）。 *)
Lemma w2t_q_margin : forall t : Q,
  Qle 0 t -> Qle t 2 ->
  Qle (w2t_q_p4 (t - (1#2)*(t*t))) (1 + t).
Proof.
  intros t H0 H2.
  set (s := (t - (1#2)*(t*t))%Q).
  assert (Hsdef : s == (t - (1#2)*(t*t))%Q) by reflexivity.
  assert (Hs0 : Qle 0 s)
    by (unfold s; apply w2t_q_s_nonneg; [exact H0 | exact H2]).
  assert (Hst : Qle s t) by exact (w2t_q_s_le_t t).
  assert (Hs1 : Qle s 1) by exact (w2t_q_s_le_1 t).
  (* HB1：(1/2)s³ ≤ (1/4)t²(t+s) *)
  assert (Hss : Qle (s*s) (t*t)).
  { apply (Qle_trans (s*s) (s*t) (t*t)).
    - exact (w2t_q_mult_le_l s s t Hs0 Hst).
    - apply (Qle_trans (s*t) (t*s) (t*t)).
      + apply qeq_le. ring.
      + exact (w2t_q_mult_le_l t s t H0 Hst). }
  assert (Hst2 : Qle s (t + s)).
  { apply (Qle_trans s t (t + s)); [exact Hst |].
    apply (Qle_trans t (t + 0) (t + s)).
    - apply qeq_le. ring.
    - apply (w2t_q_plus_le_r 0 s t). exact Hs0. }
  assert (HB1 : Qle ((1#2)*(s*(s*s))) ((1#4)*(t*t*(t + s)))).
  { apply (Qle_trans _ ((1#2)*(t*t*s))%Q).
    - apply (w2t_q_mult_le_l (1#2)%Q (s*(s*s)) (t*t*s)).
      + unfold Qle. cbn [Qnum Qden]. lia.
      + apply (Qle_trans (s*(s*s)) (s*(t*t)) (t*t*s)).
        * exact (w2t_q_mult_le_l s (s*s) (t*t) Hs0 Hss).
        * apply qeq_le. ring.
    - apply (Qle_trans _ ((1#4)*((2#1)*(t*t*s)))%Q).
      + apply qeq_le. ring.
      + apply (w2t_q_mult_le_l (1#4)%Q ((2#1)*(t*t*s)) (t*t*(t + s))).
        * unfold Qle. cbn [Qnum Qden]. lia.
        * apply (Qle_trans ((2#1)*(t*t*s)) ((t*t)*(s + s))
                   (t*t*(t + s))).
          -- apply qeq_le. ring.
          -- apply (w2t_q_mult_le_l (t*t) (s + s) (t + s)).
             ++ apply w2t_q_sq_nonneg.
             ++ apply (Qle_trans (s + s) (s + t) (t + s)).
                ** exact (w2t_q_plus_le_r s t s Hst).
                ** apply qeq_le. ring. }
  (* HB2：s³(4+3s)/24 ≤ (1/2)s³ *)
  assert (Hlin : Qle (4 + 3*s) 12).
  { apply (Qle_trans (4 + 3*s) (4 + 3) 12).
    - apply (w2t_q_plus_le_r (3*s) 3 4).
      apply (Qle_trans (3*s) (s*3) (1*3)).
      + apply qeq_le. ring.
      + apply (Qmult_le_compat_r s 1 3); [exact Hs1|].
        unfold Qle. cbn [Qnum Qden]. lia.
    - apply (Qle_trans (4 + 3) (7#1)%Q 12%Q).
      + apply qeq_le. ring.
      + unfold Qle. cbn [Qnum Qden]. lia. }
  assert (Hs3 : Qle 0 (s*(s*s)))
    by (apply (Qmult_le_0_compat s (s*s));
        [exact Hs0 | apply w2t_q_sq_nonneg]).
  assert (HB2 : Qle ((1#24)*(s*(s*(s*(4 + 3*s))))) ((1#2)*(s*(s*s)))).
  { assert (E1 : ((1#24)*(s*(s*(s*(4 + 3*s)))) ==
                  (1#24)*((s*(s*s))*(4 + 3*s)))%Q) by ring.
    assert (E2 : ((1#2)*(s*(s*s)) == (1#24)*((s*(s*s))*12))%Q) by ring.
    rewrite E1, E2.
    apply (w2t_q_mult_le_l (1#24)%Q ((s*(s*s))*(4 + 3*s)) ((s*(s*s))*12)).
    - unfold Qle. cbn [Qnum Qden]. lia.
    - apply (w2t_q_mult_le_l (s*(s*s)) (4 + 3*s) 12).
      + exact Hs3.
      + exact Hlin. }
  (* D ≥ 0 *)
  assert (HD : Qle 0 ((1#2)*(t*t) - (1#2)*(s*s) - (1#6)*(s*(s*s))
                        - (1#8)*(s*(s*(s*s))))).
  { assert (E3 : ((1#2)*(t*t) - (1#2)*(s*s) - (1#6)*(s*(s*s))
                    - (1#8)*(s*(s*(s*s))) ==
                  ((1#4)*(t*t*(t + s)) - (1#2)*(s*(s*s)))
                  + ((1#2)*(s*(s*s))
                     - (1#24)*(s*(s*(s*(4 + 3*s))))))%Q).
    { rewrite Hsdef. ring. }
    rewrite E3.
    apply (Qplus_le_compat 0 _ 0 _).
    - apply w2t_q_sub_nonneg. exact HB1.
    - apply w2t_q_sub_nonneg. exact HB2. }
  (* R 块：(1/2)s² + s³/6 + s⁴/8 ≤ t²/2 *)
  assert (HR : Qle ((1#2)*(s*s) + (1#6)*(s*(s*s)) + (1#8)*(s*(s*(s*s))))
                   ((1#2)*(t*t))).
  { assert (E4 : ((1#2)*(t*t) == (1#2)*(s*s) + (1#6)*(s*(s*s))
                     + (1#8)*(s*(s*(s*s)))
                     + ((1#2)*(t*t) - (1#2)*(s*s) - (1#6)*(s*(s*s))
                        - (1#8)*(s*(s*(s*s)))))%Q) by ring.
    rewrite E4.
    apply (Qle_trans _ (((1#2)*(s*s) + (1#6)*(s*(s*s))
                          + (1#8)*(s*(s*(s*s)))) + 0)%Q).
    - apply qeq_le. ring.
    - apply (w2t_q_plus_le_r 0
               ((1#2)*(t*t) - (1#2)*(s*s) - (1#6)*(s*(s*s))
                - (1#8)*(s*(s*(s*s))))%Q
               ((1#2)*(s*s) + (1#6)*(s*(s*s)) + (1#8)*(s*(s*(s*s))))%Q).
      exact HD. }
  (* 闭合：P4(s) = 1 + s + R ≤ 1 + s + t²/2 = 1 + t *)
  unfold w2t_q_p4.
  apply (Qle_trans _ ((1 + s) + ((1#2)*(s*s) + (1#6)*(s*(s*s))
                                  + (1#8)*(s*(s*(s*s)))))%Q).
  - apply qeq_le. ring.
  - apply (Qle_trans _ ((1 + s) + (1#2)*(t*t))%Q).
    + apply (w2t_q_plus_le_r
               ((1#2)*(s*s) + (1#6)*(s*(s*s)) + (1#8)*(s*(s*(s*s))))%Q
               ((1#2)*(t*t))%Q (1 + s)%Q).
      exact HR.
    + apply qeq_le. rewrite Hsdef. ring.
Qed.

(* ---------------- 3.b Real 层样板墙拆除件 ---------------- *)

(* 墙#2 拆除：cexp 投影对任意 Real（destruct 后定义性） *)
Lemma w2t_cexp_proj_t : forall (x : Real) (n : nat),
  projT1 (cauchy_real_exp x) n == exp_partial n (projT1 x n).
Proof.
  intros x n. destruct x as [u Hu]. reflexivity.
Qed.

(* 墙#1/#3 拆除样板：real_const 正性逐点构造（NatLe 参直接弃用） *)
Lemma w2t_const_half_pos : real_lt real_zero (real_const (1#2)).
Proof.
  unfold real_lt.
  exists (1#4)%Q.
  split.
  - apply Qlt_to_QltT. compute. reflexivity.
  - exists 0%nat. intros n Hn.
    replace (projT1 (real_const (1#2)) n) with (1#2)%Q by reflexivity.
    replace (projT1 real_zero n) with 0%Q by reflexivity.
    apply Qlt_to_QltT. compute. reflexivity.
Qed.

(* 半缩放保正：0 < g ⟹ 0 < g·(1/2) *)
Lemma w2t_lt_half_scale : forall g : Real,
  real_lt real_zero g -> real_lt real_zero (real_mult g w2t_c_half).
Proof.
  intros g Hg.
  apply (RealSetoid.real_lt_compat (real_mult w2t_c_half real_zero) real_zero
           (real_mult w2t_c_half g) (real_mult g w2t_c_half)).
  - apply (real_eq_trans (real_mult w2t_c_half real_zero)
             (real_mult real_zero w2t_c_half) real_zero).
    + apply real_mult_comm.
    + exact (real_mult_zero w2t_c_half).
  - apply real_mult_comm.
  - exact (real_mult_lt_compat_l real_zero g w2t_c_half Hg
             w2t_const_half_pos).
Qed.

(* 0 ≤ t ⟹ 0 < 1 + t（eq 支纯等式运输——墙#1 三参序对位样板） *)
Lemma w2t_one_plus_pos : forall t : Real,
  real_le real_zero t -> real_lt real_zero (real_plus real_one t).
Proof.
  intros t H0. unfold real_le in H0. destruct H0 as [Hlt | Heq].
  - destruct Hlt as [eps [Heps [N HN]]].
    unfold real_lt. exists eps. split.
    + exact Heps.
    + exists N. intros n Hn.
      specialize (HN n Hn).
      apply (qltT_eq_compat_r
               (projT1 (real_plus real_one t) n - projT1 real_zero n)%Q
               (projT1 t n + 1)%Q eps).
      * rewrite (real_plus_proj real_one t n).
        assert (Hz1 : projT1 real_one n == 1%Q) by reflexivity.
        rewrite Hz1.
        replace (projT1 real_zero n) with 0%Q by reflexivity.
        ring.
      * apply Qlt_to_QltT.
        apply (Qlt_le_trans eps (projT1 t n - 0) (projT1 t n + 1)).
        -- apply QltT_to_Qlt. exact HN.
        -- apply (Qle_trans (projT1 t n - 0) (projT1 t n)
                    (projT1 t n + 1)).
           ++ apply qeq_le. ring.
           ++ apply (Qle_trans (projT1 t n) (projT1 t n + 0%Q)
                       (projT1 t n + 1%Q)).
              ** apply qeq_le. ring.
              ** apply (w2t_q_plus_le_r 0 1 (projT1 t n)).
                 unfold Qle. cbn [Qnum Qden]. lia.
  - apply (RealSetoid.real_lt_compat real_zero real_zero real_one
             (real_plus real_one t)).
    + apply real_eq_refl.
    + apply (real_eq_trans real_one (real_plus real_one real_zero)
               (real_plus real_one t)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (RealSetoid.real_eq_plus_compat real_one real_zero
                 real_one t).
        -- apply real_eq_refl.
        -- exact Heq.
    + exact real_lt_zero_one.
Qed.

(* 0 ≤ y < 1 ⟹ 0 < 1 − y *)
Lemma w2t_one_minus_pos : forall y : Real,
  real_le real_zero y -> real_lt y real_one ->
  real_lt real_zero (real_plus real_one (real_opp y)).
Proof.
  intros y Hy0 Hy1.
  assert (Hstep : real_lt (real_opp real_one) (real_opp y))
    by (apply (real_opp_lt_compat y real_one); exact Hy1).
  apply (real_eq_lt_lt real_zero
           (real_plus real_one (real_opp real_one))
           (real_plus real_one (real_opp y))).
  - apply real_eq_of_zero_diff. intro n.
    setoid_rewrite (real_plus_proj real_one (real_opp real_one) n).
    setoid_rewrite (real_opp_proj real_one n).
    assert (Hz : projT1 real_one n == 1%Q) by reflexivity.
    rewrite Hz. ring.
  - apply (real_lt_plus_translate real_one (real_opp real_one)
             (real_opp y)).
    exact Hstep.
Qed.

(* 墙#1/#3 拆除样板：lt 换边（a < b + e ⟹ −b < −a + e，同一 witness） *)
Lemma w2t_lt_swap_opp : forall (a b e : Real),
  real_lt a (real_plus b e) ->
  real_lt (real_opp b) (real_plus (real_opp a) e).
Proof.
  intros a b e H.
  destruct H as [eps [Heps [N HN]]].
  unfold real_lt. exists eps. split.
  - exact Heps.
  - exists N. intros n Hn.
    specialize (HN n Hn).
    apply (qltT_eq_compat_r
             (projT1 (real_plus (real_opp a) e) n
                - projT1 (real_opp b) n)%Q
             (projT1 (real_plus b e) n - projT1 a n)%Q eps).
    * rewrite (real_plus_proj (real_opp a) e n).
      rewrite (real_opp_proj a n).
      rewrite (real_opp_proj b n).
      rewrite (real_plus_proj b e n).
      ring.
    * exact HN.
Qed.

(* 0 < γ ⟹ 1 < 1 + γ（eq 支运输的基座严格不等式） *)
Lemma w2t_lt_one_add : forall g : Real,
  real_lt real_zero g -> real_lt real_one (real_plus real_one g).
Proof.
  intros g Hg. destruct Hg as [eps [Heps [N HN]]].
  unfold real_lt. exists eps. split.
  - exact Heps.
  - exists N. intros n Hn.
    specialize (HN n Hn).
    replace (projT1 real_zero n) with 0%Q in HN by reflexivity.
    apply (qltT_eq_compat_r
             (projT1 (real_plus real_one g) n - projT1 real_one n)%Q
             (projT1 g n - 0)%Q eps).
    * rewrite (real_plus_proj real_one g n).
      assert (Hz : projT1 real_one n == 1%Q) by reflexivity.
      rewrite Hz.
      ring.
    * exact HN.
Qed.

(* eq/eq 矛盾支样板：t ≈ 0 且 t ≈ 1 不相容（Qabs 三角 + lra） *)
Lemma w2t_real_eq01_contra : forall t : Real,
  real_eq real_zero t -> real_eq real_one t -> False.
Proof.
  intros t H0 H1.
  assert (Hlt2 : QltT 0 (1#4)) by (apply Qlt_to_QltT; compute; reflexivity).
  destruct (H0 (1#4) Hlt2) as [N0 HN0].
  destruct (H1 (1#4) Hlt2) as [N1 HN1].
  pose proof (HN0 (Nat.max N0 N1) (NatLe_lift _ _ (Nat.le_max_l N0 N1))) as H0N.
  pose proof (HN1 (Nat.max N0 N1) (NatLe_lift _ _ (Nat.le_max_r N0 N1))) as H1N.
  rewrite (Qabs_Qminus (projT1 real_zero (Nat.max N0 N1))
             (projT1 t (Nat.max N0 N1))) in H0N.
  replace (projT1 real_zero (Nat.max N0 N1)) with 0%Q in H0N by reflexivity.
  replace (projT1 real_one (Nat.max N0 N1)) with 1%Q in H1N by reflexivity.
  rewrite (Qabs_Qminus 1 (projT1 t (Nat.max N0 N1))) in H1N.
  exfalso.
  assert (Ht : Qlt (Qabs (projT1 t (Nat.max N0 N1) - 0)) (1#4))
    by (apply QltT_to_Qlt; exact H0N).
  assert (Hu : Qlt (Qabs (projT1 t (Nat.max N0 N1) - 1)) (1#4))
    by (apply QltT_to_Qlt; exact H1N).
  assert (Htri : Qle (Qabs 1)
                   (Qabs (projT1 t (Nat.max N0 N1) - 0)
                    + Qabs (1 - projT1 t (Nat.max N0 N1)))).
  { apply (Qle_trans (Qabs 1)
             (Qabs ((projT1 t (Nat.max N0 N1) - 0)
                    + (1 - projT1 t (Nat.max N0 N1))))).
    - apply qeq_le. apply Qabs_wd. ring.
    - apply Qabs_triangle. }
  replace (Qabs 1) with 1%Q in Htri by reflexivity.
  assert (Hmid : Qle ((1#4) + (1#4)) (1#2)) by (apply qeq_le; ring).
  pose proof Hu as Hu2.
  rewrite (Qabs_Qminus (projT1 t (Nat.max N0 N1)) 1) in Hu2.
  assert (Hsum : Qlt (Qabs (projT1 t (Nat.max N0 N1) - 0)
                      + Qabs (1 - projT1 t (Nat.max N0 N1)))
                   ((1#4) + (1#4)))
    by (apply (Qplus_lt_compat _ _ _ _); [exact Ht | exact Hu2]).
  assert (Hsum2 : Qlt (Qabs (projT1 t (Nat.max N0 N1) - 0)
                       + Qabs (1 - projT1 t (Nat.max N0 N1))) (1#2))
    by (apply (Qlt_le_trans (Qabs (projT1 t (Nat.max N0 N1) - 0)
                 + Qabs (1 - projT1 t (Nat.max N0 N1)))
                 ((1#4) + (1#4)) (1#2)%Q); [exact Hsum | exact Hmid]).
  exfalso.
  assert (Hbad : Qlt 1 (1#2))
    by (apply (Qle_lt_trans 1%Q
              (Qabs (projT1 t (Nat.max N0 N1) - 0)
               + Qabs (1 - projT1 t (Nat.max N0 N1))) (1#2)%Q);
        [exact Htri | exact Hsum2]).
  unfold Qlt in Hbad. cbn [Qnum Qden] in Hbad. lia.
Qed.

(* (★) 的 Real 语句形：s := t − t²/2 *)
Definition w2t_s_real (t : Real) : Real :=
  real_plus t (real_opp (real_mult w2t_c_half (real_mult t t))).

Lemma w2t_s_proj : forall (t : Real) (n : nat),
  projT1 (w2t_s_real t) n ==
  (projT1 t n - (1#2)*(projT1 t n * projT1 t n))%Q.
Proof.
  intros t n. unfold w2t_s_real.
  setoid_rewrite (real_plus_proj t (real_opp (real_mult w2t_c_half
             (real_mult t t))) n).
  setoid_rewrite (real_opp_proj (real_mult w2t_c_half (real_mult t t)) n).
  setoid_rewrite (real_mult_proj w2t_c_half (real_mult t t) n).
  setoid_rewrite (real_mult_proj t t n).
  unfold w2t_c_half. rewrite (real_const_proj (1#2) n).
  ring.
Qed.

(* ---------------- 3.c/3.d（未竟段——源文存 attn/_tw2b_伤单片段-） ---------------- *)
(* 以下四件语句面已定稿、证明链已写至样板层（Qminus-in-Qlt 重写墙+逐点差值链），
   完整源文含逐条注释移存伤单片段文件，后续按配方续写即可：
   w2t_exp_s_le / w2t_lt_gap_strict / w2t_log_lower_quad / w2t_log_upper_lin /
   w2t_log_bound / w2t_trunc5_bridge。本段仅交付至 3.b 样板墙拆除件。 *)
(* W2B 段界线：以上为已验证件。未竟详见                   *)
(*   交付档案 §四（未竟件清单+续写配方）。    *)

(* Section 4（纯追加）：3.c/3.d 未竟清结。                   *)
(*   六件：w2t_exp_s_le（★）/ w2t_lt_gap_strict /                   *)
(*   w2t_log_lower_quad / w2t_log_upper_lin / w2t_log_bound /       *)
(*   w2t_trunc5_bridge。配方：compat 先行拆 Qminus-in-QltT 墙；      *)
(*   lra 全数替换为显式 Q 传递链（Qle_lt_trans/Qlt_le_trans/         *)
(*   Qopp_lt_compat/Qplus_lt_r(proj2)/qeq_le 系）。                  *)

(* ---------------- 4.a Qeq-运输辅助件（替代 lra 的显式链基座） ---------------- *)

(* Qeq 左换形：a == b ⟹ b < c ⟹ a < c *)
Lemma w2t_q_lt_eq_l : forall a b c : Q, a == b -> Qlt b c -> Qlt a c.
Proof.
  intros a b c H Hlt.
  apply (Qle_lt_trans a b c).
  - apply qeq_le. exact H.
  - exact Hlt.
Qed.

(* Qeq 右换形：a < b ⟹ b == c ⟹ a < c *)
Lemma w2t_q_lt_eq_r : forall a b c : Q, Qlt a b -> b == c -> Qlt a c.
Proof.
  intros a b c H Hbc.
  apply (Qlt_le_trans a b c).
  - exact H.
  - apply qeq_le. exact Hbc.
Qed.

(* 数值：0 < 1/4 *)
Lemma w2t_q_lt_0_quarter : Qlt 0 (1#4).
Proof. compute. reflexivity. Qed.

(* 右乘保严格序：a < b、0 < c ⟹ a·c < b·c *)
Lemma w2t_q_lt_scale_r : forall a b c : Q, Qlt a b -> Qlt 0 c -> Qlt (a * c) (b * c).
Proof.
  intros a b c H Hc.
  apply (Qmult_lt_compat_r a b c).
  - exact Hc.
  - exact H.
Qed.

(* exp_partial 对 Qeq 兼容（q_pow_wd 同型归纳） *)
Lemma w2t_q_ep_wd : forall (n : nat) (x y : Q), x == y -> exp_partial n x == exp_partial n y.
Proof.
  intros n x y Hxy. induction n as [| n IH]; simpl.
  - reflexivity.
  - rewrite IH. rewrite Hxy. reflexivity.
Qed.

(* ---------------- 4.b (★) exp(t−t²/2) ≤_B 1+t（3.c 未竟段清结） ---------------- *)

(* ---------------- 3.c (★)：exp(t−t²/2) ≤_B 1 + t ---------------- *)

Lemma w2t_exp_s_le : forall t : Real,
  real_le real_zero t -> real_le t real_one ->
  real_le_b (cauchy_real_exp (w2t_s_real t)) (real_plus real_one t).
Proof.
  intros t H0 H1 gamma Hgamma.
  pose proof Hgamma as Hgamma0.
  destruct Hgamma as [epsg [Hepsg [Ng HNg]]].
  unfold real_le in H0, H1.
  destruct H0 as [H0lt | H0eq].
  - (* H0-lt：逐点引擎 + 余量引理（H1 两支统一：只用到 t_n ≤ 2） *)
    destruct H0lt as [eps0 [Heps0 [N0 HN0]]].
    assert (Hn1le : sigT (fun N1 : nat =>
      forall n : nat, NatLe N1 n -> Qle (projT1 t n) 2)).
    { unfold real_le in H1. destruct H1 as [H1lt | H1eq].
      - destruct H1lt as [eps1 [Heps1 [N1 HN1]]].
        exists N1. intros n Hn.
        specialize (HN1 n Hn).
        assert (Hq : Qlt eps1 (1 - projT1 t n))
          by (apply QltT_to_Qlt; exact HN1).
        assert (Hneg : Qlt (projT1 t n - 1) (- eps1)).
        { apply (w2t_q_lt_eq_l (projT1 t n - 1) (-(1 - projT1 t n)) (- eps1)).
          - ring.
          - exact (Qopp_lt_compat eps1 (1 - projT1 t n) Hq). }
        assert (Hsh : Qlt (1 + (projT1 t n - 1)) (1 + (- eps1)))
          by exact (proj2 (Qplus_lt_r (projT1 t n - 1) (- eps1) 1) Hneg).
        apply (Qle_trans (projT1 t n) 1 2).
        + apply Qlt_le_weak.
          apply (Qlt_le_trans (projT1 t n) (1 - eps1) 1).
          * apply (w2t_q_lt_eq_l (projT1 t n) (1 + (projT1 t n - 1)) (1 - eps1)).
            -- ring.
            -- apply (w2t_q_lt_eq_r (1 + (projT1 t n - 1)) (1 + (- eps1)) (1 - eps1)).
               ++ exact Hsh.
               ++ ring.
          * apply (Qle_trans (1 - eps1) (1 + (- eps1)) 1).
            -- apply qeq_le. ring.
            -- apply (w2t_q_plus_le_r (- eps1) 0 1).
               apply (Qopp_le_compat 0 eps1).
               apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps1.
        + unfold Qle. cbn [Qnum Qden]. lia.
      - assert (Hlt2 : QltT 0 (1#2))
          by (apply Qlt_to_QltT; compute; reflexivity).
        destruct (H1eq (1#2) Hlt2) as [N1 HN1].
        exists N1. intros n Hn. specialize (HN1 n Hn).
        replace (projT1 real_one n) with 1%Q in HN1 by reflexivity.
        rewrite (Qabs_Qminus (projT1 t n) 1) in HN1.
        assert (Hq : Qlt (Qabs (1 - projT1 t n)) (1#2))
          by (apply QltT_to_Qlt; exact HN1).
        destruct (proj1 (Qabs_Qlt_condition (1 - projT1 t n) (1#2)) Hq)
          as [HA HB].
        assert (Hopp : Qlt (-(1 - projT1 t n)) (- (-(1#2))))
          by exact (Qopp_lt_compat (-(1#2)) (1 - projT1 t n) HA).
        assert (Hneg : Qlt (projT1 t n - 1) (- (-(1#2)))).
        { apply (w2t_q_lt_eq_l (projT1 t n - 1) (-(1 - projT1 t n)) (- (-(1#2)))).
          - ring.
          - exact Hopp. }
        assert (Hsh : Qlt (1 + (projT1 t n - 1)) (1 + (- (-(1#2)))))
          by exact (proj2 (Qplus_lt_r (projT1 t n - 1) (- (-(1#2))) 1) Hneg).
        apply (Qle_trans (projT1 t n) (3#2) 2).
        + apply Qlt_le_weak.
          apply (w2t_q_lt_eq_l (projT1 t n) (1 + (projT1 t n - 1)) (3#2)).
          * ring.
          * apply (w2t_q_lt_eq_r (1 + (projT1 t n - 1))
                     (1 + (- (-(1#2)))) (3#2)).
            -- exact Hsh.
            -- ring.
        + unfold Qle. cbn [Qnum Qden]. lia. }
    destruct Hn1le as [N1 HN1b].
    unfold real_lt.
    exists epsg. split.
    + exact Hepsg.
    + exists (Nat.max (Nat.max N0 N1) Ng). intros n Hn.
      assert (Hn0 : (N0 <= n)%nat).
      { apply (Nat.le_trans _ (Nat.max N0 N1) _).
        - apply Nat.le_max_l.
        - apply (Nat.le_trans _ (Nat.max (Nat.max N0 N1) Ng) _).
          + apply Nat.le_max_l.
          + exact (NatLe_drop _ _ Hn). }
      assert (Hn1 : (N1 <= n)%nat).
      { apply (Nat.le_trans _ (Nat.max N0 N1) _).
        - apply Nat.le_max_r.
        - apply (Nat.le_trans _ (Nat.max (Nat.max N0 N1) Ng) _).
          + exact (Nat.le_max_l (Nat.max N0 N1) Ng).
          + exact (NatLe_drop _ _ Hn). }
      assert (Hng : (Ng <= n)%nat).
      { apply (Nat.le_trans _ (Nat.max (Nat.max N0 N1) Ng) _).
        - exact (Nat.le_max_r (Nat.max N0 N1) Ng).
        - exact (NatLe_drop _ _ Hn). }
      pose proof (HN0 n (NatLe_lift _ _ Hn0)) as Hq0.
      pose proof (HN1b n (NatLe_lift _ _ Hn1)) as Hb1.
      pose proof (HNg n (NatLe_lift _ _ Hng)) as Hqg.
      replace (projT1 real_zero n) with 0%Q in Hq0 by reflexivity.
      assert (Htn0 : Qle 0 (projT1 t n)).
      { apply Qlt_le_weak.
        apply (Qlt_le_trans 0 (projT1 t n - 0) (projT1 t n)).
        * apply (Qlt_le_trans 0 eps0 (projT1 t n - 0)).
          -- apply QltT_to_Qlt. exact Heps0.
          -- apply Qlt_le_weak. apply QltT_to_Qlt. exact Hq0.
        * apply qeq_le. ring. }
      assert (Htn2 : Qle (projT1 t n) 2) by exact Hb1.
      assert (Hsn0 : Qle 0 (projT1 t n - (1#2)*(projT1 t n * projT1 t n)))
        by (apply w2t_q_s_nonneg; assumption).
      assert (Hsn1 : Qle (w2t_q_p4 (projT1 t n - (1#2)*(projT1 t n * projT1 t n)))
                         (1 + projT1 t n))
        by exact (w2t_q_margin (projT1 t n) Htn0 Htn2).
      assert (Heng := w2t_q_exppartial_bound
               (projT1 t n - (1#2)*(projT1 t n * projT1 t n)) n
               Hsn0 (w2t_q_s_le_1 (projT1 t n))).
      (* 归一目标形：compat 先行，Qeq 区内投影重写（墙#1 配方） *)
      apply (qltT_eq_compat_r
               (projT1 (real_plus (real_plus real_one t) gamma) n
                  - projT1 (cauchy_real_exp (w2t_s_real t)) n)%Q
               (1 + projT1 t n + projT1 gamma n
                  - exp_partial n (projT1 t n
                      - (1#2)*(projT1 t n * projT1 t n)))%Q
               epsg).
      * rewrite (real_plus_proj (real_plus real_one t) gamma n).
        rewrite (real_plus_proj real_one t n).
        rewrite (w2t_cexp_proj_t (w2t_s_real t) n).
        assert (Hsp : exp_partial n (projT1 (w2t_s_real t) n) ==
                      exp_partial n (projT1 t n - (1#2)*(projT1 t n * projT1 t n)))
          by (apply w2t_q_ep_wd; exact (w2t_s_proj t n)).
        rewrite Hsp.
        assert (Hz1 : projT1 real_one n == 1%Q) by reflexivity.
        rewrite Hz1.
        ring.
      * replace (projT1 real_zero n) with 0%Q in Hqg by reflexivity.
        assert (Hqgl : Qlt epsg (projT1 gamma n)).
        { apply (Qlt_le_trans epsg (projT1 gamma n - 0) (projT1 gamma n)).
          - apply QltT_to_Qlt. exact Hqg.
          - apply qeq_le. ring. }
        assert (Hepub : Qle (exp_partial n (projT1 t n - (1#2)*(projT1 t n * projT1 t n)))
                           (1 + projT1 t n)).
        { apply (Qle_trans _ (w2t_q_p4 (projT1 t n - (1#2)*(projT1 t n * projT1 t n))));
            [exact Heng | exact Hsn1]. }
        apply Qlt_to_QltT.
        apply (Qlt_le_trans epsg (projT1 gamma n)
                  (1 + projT1 t n + projT1 gamma n
                     - exp_partial n (projT1 t n
                         - (1#2)*(projT1 t n * projT1 t n)))).
        -- exact Hqgl.
        -- apply (Qle_trans (projT1 gamma n)
                   (projT1 gamma n + (1 + projT1 t n
                      - exp_partial n (projT1 t n
                          - (1#2)*(projT1 t n * projT1 t n))))
                   (1 + projT1 t n + projT1 gamma n
                      - exp_partial n (projT1 t n
                          - (1#2)*(projT1 t n * projT1 t n)))).
           ++ apply w2t_q_le_sub.
              assert (Hz5 : (projT1 gamma n + (1 + projT1 t n
                             - exp_partial n (projT1 t n - (1#2)*(projT1 t n * projT1 t n)))
                             - projT1 gamma n == 1 + projT1 t n
                             - exp_partial n (projT1 t n - (1#2)*(projT1 t n * projT1 t n)))%Q)
                by ring.
              rewrite Hz5.
              apply w2t_q_sub_nonneg. exact Hepub.
           ++ apply qeq_le. ring.
  - (* H0-eq：纯等式运输（exp_wd + exp_zero + s ≈ 0 + 1+t ≈ 1） *)
    apply (RealSetoid.real_lt_compat real_one (cauchy_real_exp (w2t_s_real t))
             (real_plus real_one gamma)
             (real_plus (real_plus real_one t) gamma)).
    + apply (real_eq_trans real_one (cauchy_real_exp real_zero)
               (cauchy_real_exp (w2t_s_real t))).
      * apply real_eq_sym. exact cauchy_real_exp_zero.
      * apply (cauchy_real_exp_wd real_zero (w2t_s_real t)).
        apply real_eq_sym.
        assert (Htt : real_eq (real_mult t t) real_zero).
        { apply (real_eq_trans (real_mult t t)
                   (real_mult real_zero real_zero) real_zero).
          - apply (RealSetoid.real_eq_mult_compat t t real_zero real_zero).
            + exact (real_eq_sym real_zero t H0eq).
            + exact (real_eq_sym real_zero t H0eq).
          - exact (real_mult_zero real_zero). }
        assert (Hh : real_eq (real_mult w2t_c_half (real_mult t t)) real_zero).
        { apply (real_eq_trans (real_mult w2t_c_half (real_mult t t))
                   (real_mult w2t_c_half real_zero) real_zero).
          - apply (RealSetoid.real_eq_mult_compat w2t_c_half (real_mult t t)
                     w2t_c_half real_zero).
            + apply real_eq_refl.
            + exact Htt.
          - exact (real_mult_zero w2t_c_half). }
        assert (Ho : real_eq (real_opp (real_mult w2t_c_half (real_mult t t)))
                             (real_opp real_zero)).
        { apply (RealSetoid.real_eq_opp_compat _ _). exact Hh. }
        assert (Ho0 : real_eq (real_opp real_zero) real_zero).
        { apply real_eq_of_zero_diff. intro n.
          setoid_rewrite (real_opp_proj real_zero n).
          assert (Hz : projT1 real_zero n == 0%Q) by reflexivity.
          rewrite Hz. ring. }
        apply (real_eq_trans (w2t_s_real t)
                 (real_plus real_zero (real_opp real_zero)) real_zero).
        -- apply (RealSetoid.real_eq_plus_compat t
                    (real_opp (real_mult w2t_c_half (real_mult t t)))
                    real_zero (real_opp real_zero)).
           ++ exact (real_eq_sym real_zero t H0eq).
           ++ exact Ho.
        -- apply (real_eq_trans (real_plus real_zero (real_opp real_zero))
                    (real_plus real_zero real_zero) real_zero).
           ++ apply (RealSetoid.real_eq_plus_compat real_zero
                       (real_opp real_zero) real_zero real_zero).
              ** apply real_eq_refl.
              ** exact Ho0.
           ++ exact (real_plus_zero real_zero).
    + apply (RealSetoid.real_eq_plus_compat real_one gamma
               (real_plus real_one t) gamma).
      * apply (RealSetoid.real_eq_plus_compat real_one real_zero
                 real_one t).
        -- apply real_eq_refl.
        -- exact H0eq.
      * apply real_eq_refl.
    + exact (w2t_lt_one_add gamma Hgamma0).
Qed.

(* ---------------- 3.d 反射件 + log 界对 + trunc5 桥 ---------------- *)

(* 严格隙：1 + t + γ/2 < (1+t)·e^γ *)
Lemma w2t_lt_gap_strict : forall (t : Real) (g : Real),
  real_le real_zero t -> real_lt real_zero g ->
  real_lt (real_plus (real_plus real_one t) (real_mult g w2t_c_half))
          (real_mult (real_plus real_one t) (cauchy_real_exp g)).
Proof.
  intros t g H0 Hg.
  destruct Hg as [epsg [Hepsg [Ng HNg]]].
  assert (Hlow : sigT (fun N0 : nat =>
    forall n : nat, NatLe N0 n -> Qle (-(1#4)) (projT1 t n))).
  { unfold real_le in H0. destruct H0 as [H0lt | H0eq].
    - destruct H0lt as [eps0 [Heps0 [N0 HN0]]].
      exists N0. intros n Hn. specialize (HN0 n Hn).
      replace (projT1 real_zero n) with 0%Q in HN0 by reflexivity.
      apply Qlt_le_weak.
      apply (Qlt_le_trans (-(1#4)) (projT1 t n - 0) (projT1 t n)).
      + apply (Qle_lt_trans (-(1#4)) 0 (projT1 t n - 0)).
        * unfold Qle. cbn. lia.
        * apply (Qlt_le_trans 0 eps0 (projT1 t n - 0)).
          -- apply QltT_to_Qlt. exact Heps0.
          -- apply Qlt_le_weak. apply QltT_to_Qlt. exact HN0.
      + apply qeq_le. ring.
    - assert (Hlt4 : QltT 0 (1#4))
        by (apply Qlt_to_QltT; compute; reflexivity).
      destruct (H0eq (1#4) Hlt4) as [N0 HN0].
      exists N0. intros n Hn. specialize (HN0 n Hn).
      replace (projT1 real_zero n) with 0%Q in HN0 by reflexivity.
      assert (Hq : Qlt (Qabs (0 - projT1 t n)) (1#4))
        by (apply QltT_to_Qlt; exact HN0).
      destruct (proj1 (Qabs_Qlt_condition (0 - projT1 t n) (1#4)) Hq)
        as [HA HB].
      apply Qlt_le_weak.
      apply (w2t_q_lt_eq_r (-(1#4)) (-(0 - projT1 t n)) (projT1 t n)).
      + exact (Qopp_lt_compat (0 - projT1 t n) (1#4) HB).
      + ring. }
  destruct Hlow as [N0 HN0].
  unfold real_lt.
  exists ((1#4)*epsg)%Q. split.
  - apply Qlt_to_QltT. apply (Qmult_lt_0_compat (1#4) epsg).
    + compute. reflexivity.
    + apply QltT_to_Qlt. exact Hepsg.
  - exists (Nat.max N0 (Nat.max Ng 1%nat)). intros n Hn.
    assert (Hn0 : (N0 <= n)%nat).
    { apply (Nat.le_trans _ (Nat.max N0 (Nat.max Ng 1)) _).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hn). }
    assert (Hng : (Ng <= n)%nat).
    { apply (Nat.le_trans _ (Nat.max Ng 1) _).
      - apply Nat.le_max_l.
      - apply (Nat.le_trans _ (Nat.max N0 (Nat.max Ng 1)) _).
        + apply Nat.le_max_r.
        + exact (NatLe_drop _ _ Hn). }
    assert (Hn1 : (1 <= n)%nat).
    { apply (Nat.le_trans _ (Nat.max Ng 1) _).
      - apply Nat.le_max_r.
      - apply (Nat.le_trans _ (Nat.max N0 (Nat.max Ng 1)) _).
        + apply Nat.le_max_r.
        + exact (NatLe_drop _ _ Hn). }
    pose proof (HN0 n (NatLe_lift _ _ Hn0)) as Hlow'.
    pose proof (HNg n (NatLe_lift _ _ Hng)) as Hqg.
    replace (projT1 real_zero n) with 0%Q in Hqg by reflexivity.
    assert (Hqglt : Qlt epsg (projT1 g n)).
    { apply (Qlt_le_trans epsg (projT1 g n - 0) (projT1 g n)).
      - apply QltT_to_Qlt. exact Hqg.
      - apply qeq_le. ring. }
    assert (Hgpos : Qle 0 (projT1 g n)).
    { apply Qlt_le_weak. apply (Qlt_trans 0 epsg (projT1 g n)).
      - apply QltT_to_Qlt. exact Hepsg.
      - exact Hqglt. }
    assert (Hge := w2t_q_ep_ge_1plus (projT1 g n) n Hgpos Hn1).
    assert (Hge1 : Qle 1 (exp_partial n (projT1 g n))).
    { apply (Qle_trans 1 (1 + 0%Q) (exp_partial n (projT1 g n))).
      - apply qeq_le. ring.
      - apply (Qle_trans (1 + 0%Q) (1 + projT1 g n)
                 (exp_partial n (projT1 g n))).
        + apply (w2t_q_plus_le_r 0 (projT1 g n) 1). exact Hgpos.
        + exact Hge. }
    (* 归一形（compat 先行）：Qeq 区内投影重写 *)
    apply (qltT_eq_compat_r
             (projT1 (real_mult (real_plus real_one t) (cauchy_real_exp g)) n
                - projT1 (real_plus (real_plus real_one t)
                            (real_mult g w2t_c_half)) n)%Q
             ((1 + projT1 t n) * exp_partial n (projT1 g n)
                - (1 + projT1 t n + (1#2) * projT1 g n))%Q
             ((1#4) * epsg)%Q).
    + rewrite (real_mult_proj (real_plus real_one t) (cauchy_real_exp g) n).
      rewrite (w2t_cexp_proj_t g n).
      rewrite (real_plus_proj (real_plus real_one t) (real_mult g w2t_c_half) n).
      rewrite (real_plus_proj real_one t n).
      rewrite (real_mult_proj g w2t_c_half n).
      unfold w2t_c_half. rewrite (real_const_proj (1#2) n).
      assert (Hz1 : projT1 real_one n == 1%Q) by reflexivity.
      rewrite Hz1.
      ring.
    + assert (Hg1 : Qle (projT1 g n) (exp_partial n (projT1 g n) - 1)).
      { apply w2t_q_le_sub.
        assert (Hz : (exp_partial n (projT1 g n) - 1 - projT1 g n
                      == exp_partial n (projT1 g n) - (1 + projT1 g n))%Q) by ring.
        rewrite Hz. apply w2t_q_sub_nonneg. exact Hge. }
      assert (Hsc : Qle (3#4) (1 + projT1 t n)).
      { apply w2t_q_le_sub.
        assert (Hz2 : (1 + projT1 t n - (3#4) == projT1 t n - (-(1#4)))%Q) by ring.
        rewrite Hz2.
        apply w2t_q_sub_nonneg. exact Hlow'. }
      assert (Hfin : Qle ((3#4)*(exp_partial n (projT1 g n) - 1) - (1#2)*projT1 g n)
                         ((1 + projT1 t n)*(exp_partial n (projT1 g n) - 1)
                            - (1#2)*projT1 g n)).
      { apply w2t_q_le_sub.
        assert (Hz : ((1 + projT1 t n)*(exp_partial n (projT1 g n) - 1)
                      - (1#2)*projT1 g n
                      - ((3#4)*(exp_partial n (projT1 g n) - 1) - (1#2)*projT1 g n)
                      == (1 + projT1 t n - (3#4))*(exp_partial n (projT1 g n) - 1))%Q)
          by ring.
        rewrite Hz.
        apply (Qmult_le_0_compat (1 + projT1 t n - (3#4))%Q
                                 (exp_partial n (projT1 g n) - 1)%Q).
        * apply w2t_q_sub_nonneg. exact Hsc.
        * apply w2t_q_sub_nonneg. exact Hge1. }
      assert (Hrw : ((1 + projT1 t n) * exp_partial n (projT1 g n)
                     - (1 + projT1 t n + (1#2)*projT1 g n) ==
                     (1 + projT1 t n)*(exp_partial n (projT1 g n) - 1)
                     - (1#2)*projT1 g n)%Q) by ring.
      apply Qlt_to_QltT.
      apply (w2t_q_lt_eq_r ((1#4)*epsg)
               ((1 + projT1 t n) * (exp_partial n (projT1 g n) - 1)
                  - (1#2)*projT1 g n)
               ((1 + projT1 t n) * exp_partial n (projT1 g n)
                  - (1 + projT1 t n + (1#2) * projT1 g n))).
      * apply (Qlt_le_trans ((1#4)*epsg)
                 ((3#4)*(exp_partial n (projT1 g n) - 1) - (1#2)*projT1 g n)
                 ((1 + projT1 t n) * (exp_partial n (projT1 g n) - 1)
                    - (1#2)*projT1 g n)).
        -- apply (Qlt_le_trans ((1#4)*epsg) ((1#4)*projT1 g n)
                    ((3#4)*(exp_partial n (projT1 g n) - 1) - (1#2)*projT1 g n)).
           ++ rewrite (Qmult_comm (1#4) epsg), (Qmult_comm (1#4) (projT1 g n)).
              apply (w2t_q_lt_scale_r epsg (projT1 g n) (1#4)
                       Hqglt w2t_q_lt_0_quarter).
           ++ apply w2t_q_le_sub.
              assert (Hz3 : ((3#4)*(exp_partial n (projT1 g n) - 1)
                             - (1#2)*projT1 g n - (1#4)*projT1 g n
                             == (3#4)*(exp_partial n (projT1 g n) - 1 - projT1 g n))%Q)
                by ring.
              rewrite Hz3.
              apply (Qmult_le_0_compat (3#4)%Q
                                       (exp_partial n (projT1 g n) - 1 - projT1 g n)%Q).
              ** unfold Qle. cbn [Qnum Qden]. lia.
              ** exact (w2t_q_sub_nonneg (projT1 g n)
                          (exp_partial n (projT1 g n) - 1) Hg1).
        -- exact Hfin.
      * apply Qeq_sym. exact Hrw.
Qed.


(* target1 主件（下界）：t − t²/2 ≤_B log(1+t) *)
Lemma w2t_log_lower_quad : forall (t : Real)
  (H0 : real_le real_zero t) (H1 : real_le t real_one)
  (Hs : real_lt real_zero (real_plus real_one t)),
  real_le_b (w2t_s_real t) (real_log (real_plus real_one t) Hs).
Proof.
  intros t H0 H1 Hs gamma Hgamma.
  assert (Hgp : real_lt real_zero (real_mult gamma w2t_c_half))
    by (apply (w2t_lt_half_scale gamma Hgamma)).
  pose (Hpos2 := real_mult_positive (real_plus real_one t)
                   (cauchy_real_exp gamma) Hs
                   (cauchy_real_exp_pos gamma)).
  pose proof ((w2t_exp_s_le t H0 H1) (real_mult gamma w2t_c_half) Hgp) as HA'.
  pose proof (w2t_lt_gap_strict t gamma H0 Hgamma) as HB.
  assert (Hpos : real_lt real_zero (cauchy_real_exp (w2t_s_real t)))
    by apply cauchy_real_exp_pos.
  pose proof (real_log_lt_mono (cauchy_real_exp (w2t_s_real t))
                (real_mult (real_plus real_one t) (cauchy_real_exp gamma))
                Hpos Hpos2
                (real_lt_trans _ _ _ HA' HB)) as Hmono.
  unfold real_log.
  apply (RealSetoid.real_lt_compat
           (cw_log (cauchy_real_exp (w2t_s_real t)) Hpos) (w2t_s_real t)
           (cw_log (real_mult (real_plus real_one t) (cauchy_real_exp gamma))
              Hpos2)
           (real_plus (cw_log (real_plus real_one t) Hs) gamma)).
  - exact (log_inv_exp_neg_thm (w2t_s_real t) Hpos).
  - apply (real_eq_trans
             (cw_log (real_mult (real_plus real_one t) (cauchy_real_exp gamma))
                Hpos2)
             (real_plus (cw_log (real_plus real_one t) Hs)
                (cw_log (cauchy_real_exp gamma) (cauchy_real_exp_pos gamma)))
             (real_plus (cw_log (real_plus real_one t) Hs) gamma)).
    + exact (real_log_mult (real_plus real_one t) (cauchy_real_exp gamma)
               Hs (cauchy_real_exp_pos gamma)).
    + apply (RealSetoid.real_eq_plus_compat
               (cw_log (real_plus real_one t) Hs)
               (cw_log (cauchy_real_exp gamma) (cauchy_real_exp_pos gamma))
               (cw_log (real_plus real_one t) Hs)
               gamma).
      * apply real_eq_refl.
      * exact (log_inv_exp_neg_thm gamma (cauchy_real_exp_pos gamma)).
  - exact Hmono.
Qed.

(* target1 上界半边：log(1+t) ≤_B t（既有件直取） *)
Lemma w2t_log_upper_lin : forall (t : Real)
  (Hs : real_lt real_zero (real_plus real_one t)),
  real_le_b (real_log (real_plus real_one t) Hs) t.
Proof.
  intros t Hs. exact (real_log_one_plus_le_B t Hs).
Qed.

(* target1 闭合：log(1+x) 上下界对（Set 层 sigT 对偶） *)
Definition w2t_log_bound (t : Real)
  (H0 : real_le real_zero t) (H1 : real_le t real_one)
  (Hs : real_lt real_zero (real_plus real_one t))
  : sigT (fun _ : real_le_b (w2t_s_real t)
              (real_log (real_plus real_one t) Hs) =>
          real_le_b (real_log (real_plus real_one t) Hs) t)
  := existT _ (w2t_log_lower_quad t H0 H1 Hs) (w2t_log_upper_lin t Hs).

(* target3 trunc5 桥：y + y²/2 ≤_B −log(1−y) *)
Lemma w2t_trunc5_bridge : forall (y : Real)
  (Hy0 : real_le real_zero y) (Hy1 : real_lt y real_one)
  (Hm : real_lt real_zero (real_plus real_one (real_opp y))),
  real_le_b (real_plus y (real_mult w2t_c_half (real_mult y y)))
            (real_opp (real_log (real_plus real_one (real_opp y)) Hm)).
Proof.
  intros y Hy0 Hy1 Hm gamma Hgamma.
  assert (Hgp : real_lt real_zero (real_mult gamma w2t_c_half))
    by (apply (w2t_lt_half_scale gamma Hgamma)).
  pose (Hp := w2t_one_plus_pos y Hy0).
  pose (HM := real_mult_positive (real_plus real_one (real_opp y))
                 (real_plus real_one y) Hm Hp).
  (* A：log M < −y² + γ/2（上切线 real_log_le_linear_B 实例 + 逐点换形） *)
  pose proof (real_log_le_linear_B
               (real_mult (real_plus real_one (real_opp y))
                          (real_plus real_one y)) HM) as HA0.
  pose proof (HA0 (real_mult gamma w2t_c_half) Hgp) as HA1.
  assert (HA : real_lt (real_log (real_mult (real_plus real_one (real_opp y))
                                  (real_plus real_one y)) HM)
                (real_plus (real_opp (real_mult y y))
                   (real_mult gamma w2t_c_half))).
  { apply (RealSetoid.real_lt_compat
             (real_log (real_mult (real_plus real_one (real_opp y))
                          (real_plus real_one y)) HM)
             (real_log (real_mult (real_plus real_one (real_opp y))
                          (real_plus real_one y)) HM)
             (real_plus (real_plus (real_mult (real_plus real_one (real_opp y))
                                 (real_plus real_one y))
                          (real_opp real_one))
                    (real_mult gamma w2t_c_half))
             (real_plus (real_opp (real_mult y y))
                (real_mult gamma w2t_c_half))).
    - apply real_eq_refl.
    - apply real_eq_of_zero_diff. intro n.
      setoid_rewrite (real_plus_proj
                 (real_plus (real_mult (real_plus real_one (real_opp y))
                             (real_plus real_one y))
                            (real_opp real_one))
                 (real_mult gamma w2t_c_half) n).
      setoid_rewrite (real_plus_proj (real_mult (real_plus real_one (real_opp y))
                                (real_plus real_one y))
                 (real_opp real_one) n).
      setoid_rewrite (real_mult_proj (real_plus real_one (real_opp y))
                 (real_plus real_one y) n).
      setoid_rewrite (real_plus_proj real_one (real_opp y) n).
      setoid_rewrite (real_opp_proj y n).
      setoid_rewrite (real_plus_proj real_one y n).
      setoid_rewrite (real_opp_proj real_one n).
      setoid_rewrite (real_plus_proj (real_opp (real_mult y y))
                 (real_mult gamma w2t_c_half) n).
      setoid_rewrite (real_opp_proj (real_mult y y) n).
      setoid_rewrite (real_mult_proj y y n).
      setoid_rewrite (real_mult_proj gamma w2t_c_half n).
      unfold w2t_c_half. rewrite (real_const_proj (1#2) n).
      assert (Hd : ((projT1 real_one n + - projT1 y n) * (projT1 real_one n + projT1 y n)
                    + - projT1 real_one n + projT1 gamma n * (1#2)
                    - (- (projT1 y n * projT1 y n) + projT1 gamma n * (1#2)) == 0)%Q).
      { assert (Hz1 : projT1 real_one n == 1%Q) by reflexivity.
        rewrite Hz1. ring. }
      exact Hd.
    - exact HA1. }
  (* B：−log(1+y) < −(y − y²/2) + γ/2（target1 实例 + 换边样板） *)
  assert (Hyle : real_le y real_one).
  { unfold real_le. left. exact Hy1. }
  pose proof (w2t_log_lower_quad y Hy0 Hyle Hp
               (real_mult gamma w2t_c_half) Hgp) as HB0.
  pose proof (w2t_lt_swap_opp (w2t_s_real y)
               (real_log (real_plus real_one y) Hp)
               (real_mult gamma w2t_c_half)
               HB0) as HB.
  (* 求和 + HE 换形（log M ≈ log(1−y)+log(1+y)）+ 数值闭合 + 换边 *)
  pose proof (real_lt_plus_compat
               (real_log (real_mult (real_plus real_one (real_opp y))
                          (real_plus real_one y)) HM)
               (real_plus (real_opp (real_mult y y))
                  (real_mult gamma w2t_c_half))
               (real_opp (real_log (real_plus real_one y) Hp))
               (real_plus (real_opp (w2t_s_real y))
                  (real_mult gamma w2t_c_half))
               HA HB) as HS.
  pose (HE := real_log_mult (real_plus real_one (real_opp y))
                 (real_plus real_one y) Hm Hp).
  assert (HSL : real_lt (real_log (real_plus real_one (real_opp y)) Hm)
                (real_plus (real_plus (real_opp (real_mult y y))
                            (real_mult gamma w2t_c_half))
                     (real_plus (real_opp (w2t_s_real y))
                        (real_mult gamma w2t_c_half)))).
  { apply (RealSetoid.real_lt_compat
             (real_plus (real_log (real_mult (real_plus real_one (real_opp y))
                                 (real_plus real_one y)) HM)
                    (real_opp (real_log (real_plus real_one y) Hp)))
             (real_log (real_plus real_one (real_opp y)) Hm)
             (real_plus (real_plus (real_opp (real_mult y y))
                         (real_mult gamma w2t_c_half))
                  (real_plus (real_opp (w2t_s_real y))
                     (real_mult gamma w2t_c_half)))
             (real_plus (real_plus (real_opp (real_mult y y))
                         (real_mult gamma w2t_c_half))
                  (real_plus (real_opp (w2t_s_real y))
                     (real_mult gamma w2t_c_half)))).
    - apply (real_eq_trans
               (real_plus (real_log (real_mult (real_plus real_one (real_opp y))
                                   (real_plus real_one y)) HM)
                          (real_opp (real_log (real_plus real_one y) Hp)))
               (real_plus (real_plus (real_log (real_plus real_one (real_opp y)) Hm)
                           (real_log (real_plus real_one y) Hp))
                          (real_opp (real_log (real_plus real_one y) Hp)))
               (real_log (real_plus real_one (real_opp y)) Hm)).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_log (real_mult (real_plus real_one (real_opp y))
                             (real_plus real_one y)) HM)
                 (real_opp (real_log (real_plus real_one y) Hp))
                 (real_plus (real_log (real_plus real_one (real_opp y)) Hm)
                    (real_log (real_plus real_one y) Hp))
                 (real_opp (real_log (real_plus real_one y) Hp))).
        * exact HE.
        * apply real_eq_refl.
      + apply real_eq_of_zero_diff. intro n.
        setoid_rewrite (real_plus_proj
                   (real_plus (real_log (real_plus real_one (real_opp y)) Hm)
                    (real_log (real_plus real_one y) Hp))
                   (real_opp (real_log (real_plus real_one y) Hp)) n).
        setoid_rewrite (real_plus_proj
                   (real_log (real_plus real_one (real_opp y)) Hm)
                   (real_log (real_plus real_one y) Hp) n).
        setoid_rewrite (real_opp_proj (real_log (real_plus real_one y) Hp) n).
        ring.
    - apply real_eq_refl.
    - exact HS. }
  assert (HSR : real_lt (real_log (real_plus real_one (real_opp y)) Hm)
                (real_plus (real_opp (real_plus y
                            (real_mult w2t_c_half (real_mult y y)))) gamma)).
  { apply (RealSetoid.real_lt_compat
             (real_log (real_plus real_one (real_opp y)) Hm)
             (real_log (real_plus real_one (real_opp y)) Hm)
             (real_plus (real_plus (real_opp (real_mult y y))
                         (real_mult gamma w2t_c_half))
                  (real_plus (real_opp (w2t_s_real y))
                     (real_mult gamma w2t_c_half)))
             (real_plus (real_opp (real_plus y
                         (real_mult w2t_c_half (real_mult y y)))) gamma)).
    - apply real_eq_refl.
    - apply real_eq_of_zero_diff. intro n.
      setoid_rewrite (real_plus_proj (real_plus (real_opp (real_mult y y))
                                  (real_mult gamma w2t_c_half))
                       (real_plus (real_opp (w2t_s_real y))
                                  (real_mult gamma w2t_c_half)) n).
      setoid_rewrite (real_plus_proj (real_opp (real_mult y y))
                  (real_mult gamma w2t_c_half) n).
      setoid_rewrite (real_opp_proj (real_mult y y) n).
      setoid_rewrite (real_mult_proj y y n).
      setoid_rewrite (real_plus_proj (real_opp (w2t_s_real y))
                  (real_mult gamma w2t_c_half) n).
      setoid_rewrite (real_opp_proj (w2t_s_real y) n).
      rewrite (w2t_s_proj y n).
      setoid_rewrite (real_plus_proj (real_opp (real_plus y
                  (real_mult w2t_c_half (real_mult y y)))) gamma n).
      setoid_rewrite (real_opp_proj (real_plus y
                  (real_mult w2t_c_half (real_mult y y))) n).
      setoid_rewrite (real_plus_proj y
                  (real_mult w2t_c_half (real_mult y y)) n).
      setoid_rewrite (real_mult_proj w2t_c_half (real_mult y y) n).
      setoid_rewrite (real_mult_proj y y n).
      setoid_rewrite (real_mult_proj gamma w2t_c_half n).
      unfold w2t_c_half. rewrite (real_const_proj (1#2) n).
      ring.
    - exact HSL. }
  pose proof (w2t_lt_swap_opp (real_log (real_plus real_one (real_opp y)) Hm)
               (real_opp (real_plus y (real_mult w2t_c_half (real_mult y y))))
               gamma HSR) as HSW.
  apply (RealSetoid.real_lt_compat
           (real_opp (real_opp (real_plus y
                       (real_mult w2t_c_half (real_mult y y)))))
           (real_plus y (real_mult w2t_c_half (real_mult y y)))
           (real_plus (real_opp (real_log (real_plus real_one (real_opp y)) Hm))
              gamma)
           (real_plus (real_opp (real_log (real_plus real_one (real_opp y)) Hm))
              gamma)).
  - apply real_eq_of_zero_diff. intro n.
    setoid_rewrite (real_opp_proj (real_opp (real_plus y
                (real_mult w2t_c_half (real_mult y y)))) n).
    setoid_rewrite (real_opp_proj (real_plus y
                (real_mult w2t_c_half (real_mult y y))) n).
    setoid_rewrite (real_plus_proj y
                (real_mult w2t_c_half (real_mult y y)) n).
    setoid_rewrite (real_mult_proj w2t_c_half (real_mult y y) n).
    setoid_rewrite (real_mult_proj y y n).
    unfold w2t_c_half. rewrite (real_const_proj (1#2) n).
    ring.
  - apply real_eq_refl.
  - exact HSW.
Qed.
(* ================= §2 pnk_two 族 ================= *)
From Stdlib Require Import QArith.Qring Setoid.

(* inv 不透明化：防 cbn [projT1] 强制 delta-展开 real_inv_pos 暴露
   卡壳 match（destruct-let 病根）；ring 段以整投影原子通过。 *)
Local Opaque real_inv_pos.

(* ---- 0. 常数 ---- *)

Definition pnk_two : Real := real_plus real_one real_one.

Lemma pnk_two_pos : real_lt real_zero pnk_two.
Proof.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero) (real_plus real_one real_one)).
  - exact (real_eq_sym (real_plus real_zero real_zero) real_zero
             (real_plus_zero real_zero)).
  - exact (real_lt_plus_compat real_zero real_one real_zero real_one
             real_lt_zero_one real_lt_zero_one).
Qed.

Definition pnk_three : Real := real_plus pnk_two real_one.

(* 常数投影叶：ring 前置降元（projT1 C k → Q 字面量） *)
Lemma pnk_one_proj : forall k : nat, projT1 real_one k == 1%Q.
Proof. intro k. cbv [projT1 real_one]. reflexivity. Qed.

Lemma pnk_zero_proj : forall k : nat, projT1 real_zero k == 0%Q.
Proof. intro k. cbv [projT1 real_zero]. reflexivity. Qed.

Lemma pnk_two_proj : forall k : nat, projT1 pnk_two k == (1 + 1)%Q.
Proof. intro k. cbv [projT1 pnk_two real_plus real_one]. reflexivity. Qed.

Lemma pnk_three_proj : forall k : nat, projT1 pnk_three k == (1 + 1 + 1)%Q.
Proof. intro k. cbv [projT1 pnk_three real_plus real_one]. reflexivity. Qed.

(* ---- 1. Bishop 工具箱 ---- *)

(* 严格序入 Bishop 形 *)
Lemma pnk_lt_le_b : forall x y : Real, real_lt x y -> real_le_b x y.
Proof.
  intros x y H. apply real_le_to_le_b. unfold real_le. left. exact H.
Qed.

(* opp 的 eq 兼容（库内 grep 零命中，自建七步 setoid 链） *)
Lemma pnk_eq_opp_compat : forall a b : Real,
  real_eq a b -> real_eq (real_opp a) (real_opp b).
Proof.
  intros a b Hab.
  assert (HZ : real_eq (real_plus a (real_opp b)) real_zero).
  { apply (real_eq_trans (real_plus a (real_opp b))
             (real_plus b (real_opp b)) real_zero).
    - apply (RealSetoid.real_eq_plus_compat a (real_opp b) b (real_opp b)
               Hab (real_eq_refl (real_opp b))).
    - apply real_plus_opp. }
  apply (real_eq_trans (real_opp a)
           (real_plus (real_opp a) (real_plus a (real_opp b)))
           (real_opp b)).
  - apply (real_eq_trans (real_opp a)
             (real_plus (real_opp a) real_zero)
             (real_plus (real_opp a) (real_plus a (real_opp b)))).
    + apply real_eq_sym. apply real_plus_zero.
    + apply (RealSetoid.real_eq_plus_compat (real_opp a) real_zero
               (real_opp a) (real_plus a (real_opp b))
               (real_eq_refl (real_opp a))
               (real_eq_sym (real_plus a (real_opp b)) real_zero HZ)).
  - apply (real_eq_trans
             (real_plus (real_opp a) (real_plus a (real_opp b)))
             (real_plus real_zero (real_opp b))
             (real_opp b)).
    + apply (real_eq_trans
               (real_plus (real_opp a) (real_plus a (real_opp b)))
               (real_plus (real_plus (real_opp a) a) (real_opp b))
               (real_plus real_zero (real_opp b))).
      * apply real_plus_assoc.
      * apply (real_eq_trans
                 (real_plus (real_plus (real_opp a) a) (real_opp b))
                 (real_plus (real_plus a (real_opp a)) (real_opp b))
                 (real_plus real_zero (real_opp b))).
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_plus (real_opp a) a) (real_opp b)
                     (real_plus a (real_opp a)) (real_opp b)
                     (real_plus_comm (real_opp a) a)
                     (real_eq_refl (real_opp b))).
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_plus a (real_opp a)) (real_opp b)
                     real_zero (real_opp b)
                     (real_plus_opp a) (real_eq_refl (real_opp b))).
    + apply (real_eq_trans (real_plus real_zero (real_opp b))
               (real_plus (real_opp b) real_zero) (real_opp b)).
      * apply real_plus_comm.
      * apply real_plus_zero.
Qed.

(* Bishop 左消去：z+x ≤_B z+y ⟹ x ≤_B y *)
Lemma pnk_le_b_cancel_l : forall z x y : Real,
  real_le_b (real_plus z x) (real_plus z y) -> real_le_b x y.
Proof.
  intros z x y H eps Heps.
  assert (H1 : real_lt (real_plus z x) (real_plus z (real_plus y eps))).
  { apply (RealSetoid.real_lt_id_r (real_plus z x)
             (real_plus (real_plus z y) eps) (real_plus z (real_plus y eps))).
    - apply real_eq_sym. apply real_plus_assoc.
    - exact (H eps Heps). }
  assert (H2 : real_lt (real_plus (real_opp z) (real_plus z x))
                       (real_plus (real_opp z) (real_plus z (real_plus y eps)))).
  { apply (real_lt_plus_translate (real_opp z) (real_plus z x)
             (real_plus z (real_plus y eps))). exact H1. }
  assert (HMX : real_eq (real_plus (real_opp z) (real_plus z x)) x).
  { apply (real_eq_trans (real_plus (real_opp z) (real_plus z x))
             (real_plus (real_plus (real_opp z) z) x) x).
    - apply real_plus_assoc.
    - apply (real_eq_trans (real_plus (real_plus (real_opp z) z) x)
               (real_plus real_zero x) x).
      + apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp z) z)
                 x real_zero x).
        * exact (real_eq_trans (real_plus (real_opp z) z)
                   (real_plus z (real_opp z)) real_zero
                   (real_plus_comm (real_opp z) z) (real_plus_opp z)).
        * apply real_eq_refl.
      + exact (real_eq_trans (real_plus real_zero x)
                 (real_plus x real_zero) x
                 (real_plus_comm real_zero x) (real_plus_zero x)). }
  apply (RealSetoid.real_lt_id_l x
           (real_plus (real_opp z) (real_plus z x)) (real_plus y eps)).
  - apply real_eq_sym. exact HMX.
  - apply (RealSetoid.real_lt_id_r (real_plus (real_opp z) (real_plus z x))
             (real_plus (real_opp z) (real_plus z (real_plus y eps)))
             (real_plus y eps)).
    + apply (real_eq_trans
               (real_plus (real_opp z) (real_plus z (real_plus y eps)))
               (real_plus (real_plus (real_opp z) z) (real_plus y eps))
               (real_plus y eps)).
      * apply real_plus_assoc.
      * apply (real_eq_trans
                 (real_plus (real_plus (real_opp z) z) (real_plus y eps))
                 (real_plus real_zero (real_plus y eps)) (real_plus y eps)).
        -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp z) z)
                    (real_plus y eps) real_zero (real_plus y eps)).
           ++ apply (real_eq_trans (real_plus (real_opp z) z)
                       (real_plus z (real_opp z)) real_zero).
              ** apply real_plus_comm.
              ** apply real_plus_opp.
           ++ apply real_eq_refl.
        -- exact (real_eq_trans (real_plus real_zero (real_plus y eps))
                    (real_plus (real_plus y eps) real_zero)
                    (real_plus y eps)
                    (real_plus_comm real_zero (real_plus y eps))
                    (real_plus_zero (real_plus y eps))).
    + exact H2.
Qed.

(* ---- 2. 锐化上切线核（共轭对抽象形） ---- *)
(*   假设：t1·t2 == x；log 拆分 EQ；(x+1)·t1 == 2x；2·(x+1)·t2 == (x+1)² *)
(*   结论：(x+1)·2·log x ≤_B (x−1)(x+3)。Bishop 组装纯序组合。           *)

Lemma pnk_core_pair : forall (x t1 t2 : Real)
  (Hx : real_lt real_zero x) (Ht1 : real_lt real_zero t1)
  (Ht2 : real_lt real_zero t2),
  real_eq (real_mult t1 t2) x ->
  real_eq (real_plus (real_log t1 Ht1) (real_log t2 Ht2)) (real_log x Hx) ->
  real_eq (real_mult (real_plus x real_one) t1) (real_mult pnk_two x) ->
  real_eq (real_mult pnk_two (real_mult (real_plus x real_one) t2))
          (real_mult (real_plus x real_one) (real_plus x real_one)) ->
  real_le_b (real_mult (real_plus x real_one)
                       (real_mult pnk_two (real_log x Hx)))
            (real_mult (real_plus x (real_opp real_one))
                       (real_plus x pnk_three)).
Proof.
  intros x t1 t2 Hx Ht1 Ht2 Hprod Hsplit Hsc1 Hsc2.
  assert (Hx1 : real_lt real_zero (real_plus x real_one)).
  { apply (RealSetoid.real_lt_id_l real_zero
             (real_plus real_zero real_zero) (real_plus x real_one)).
    - exact (real_eq_sym (real_plus real_zero real_zero) real_zero
               (real_plus_zero real_zero)).
    - exact (real_lt_plus_compat real_zero x real_zero real_one
               Hx real_lt_zero_one). }
  assert (HT1 : real_le_b (real_log t1 Ht1)
                          (real_plus t1 (real_opp real_one)))
    by exact (real_log_le_linear_B t1 Ht1).
  assert (HT2 : real_le_b (real_log t2 Ht2)
                          (real_plus t2 (real_opp real_one)))
    by exact (real_log_le_linear_B t2 Ht2).
  assert (S1 : real_le_b (real_mult (real_plus x real_one)
                                    (real_mult pnk_two (real_log t1 Ht1)))
                         (real_mult (real_plus x real_one)
                                    (real_mult pnk_two
                                       (real_plus t1 (real_opp real_one))))).
  { apply (leb3_le_b_pos_scale_l _ _ (real_plus x real_one)).
    apply (leb3_le_b_pos_scale_l _ _ pnk_two).
    exact HT1.
    exact pnk_two_pos.
    exact Hx1. }
  assert (S2 : real_le_b (real_mult (real_plus x real_one)
                                    (real_mult pnk_two (real_log t2 Ht2)))
                         (real_mult (real_plus x real_one)
                                    (real_mult pnk_two
                                       (real_plus t2 (real_opp real_one))))).
  { apply (leb3_le_b_pos_scale_l _ _ (real_plus x real_one)).
    apply (leb3_le_b_pos_scale_l _ _ pnk_two).
    exact HT2.
    exact pnk_two_pos.
    exact Hx1. }
  assert (SA : real_le_b
                 (real_plus (real_mult (real_plus x real_one)
                                       (real_mult pnk_two (real_log t1 Ht1)))
                            (real_mult (real_plus x real_one)
                                       (real_mult pnk_two (real_log t2 Ht2))))
                 (real_plus (real_mult (real_plus x real_one)
                                       (real_mult pnk_two
                                          (real_plus t1 (real_opp real_one))))
                            (real_mult (real_plus x real_one)
                                       (real_mult pnk_two
                                          (real_plus t2 (real_opp real_one))))))
    by exact (real_le_b_plus_compat _ _ _ _ S1 S2).
  (* 左端：分配律收拢 log 项和 *)
  assert (EL : real_eq
                 (real_plus (real_mult (real_plus x real_one)
                                       (real_mult pnk_two (real_log t1 Ht1)))
                            (real_mult (real_plus x real_one)
                                       (real_mult pnk_two (real_log t2 Ht2))))
                 (real_mult (real_plus x real_one)
                            (real_mult pnk_two
                               (real_plus (real_log t1 Ht1)
                                          (real_log t2 Ht2))))).
  { apply (real_eq_trans
             (real_plus (real_mult (real_plus x real_one)
                                   (real_mult pnk_two (real_log t1 Ht1)))
                        (real_mult (real_plus x real_one)
                                   (real_mult pnk_two (real_log t2 Ht2))))
             (real_mult (real_plus x real_one)
                        (real_plus (real_mult pnk_two (real_log t1 Ht1))
                                   (real_mult pnk_two (real_log t2 Ht2))))
             (real_mult (real_plus x real_one)
                        (real_mult pnk_two
                           (real_plus (real_log t1 Ht1)
                                      (real_log t2 Ht2))))).
    - apply real_eq_sym. apply real_distrib.
    - apply (RealSetoid.real_eq_mult_compat (real_plus x real_one)
                (real_plus (real_mult pnk_two (real_log t1 Ht1))
                           (real_mult pnk_two (real_log t2 Ht2)))
                (real_plus x real_one)
                (real_mult pnk_two
                   (real_plus (real_log t1 Ht1) (real_log t2 Ht2)))).
      + apply real_eq_refl.
      + apply real_eq_sym. apply real_distrib. }
  (* 拆分 EQ 运输至 log x *)
  assert (ES : real_eq
                 (real_mult (real_plus x real_one)
                            (real_mult pnk_two
                               (real_plus (real_log t1 Ht1)
                                          (real_log t2 Ht2))))
                 (real_mult (real_plus x real_one)
                            (real_mult pnk_two (real_log x Hx)))).
  { apply (RealSetoid.real_eq_mult_compat (real_plus x real_one)
              (real_mult pnk_two
                 (real_plus (real_log t1 Ht1) (real_log t2 Ht2)))
              (real_plus x real_one) (real_mult pnk_two (real_log x Hx))).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_mult_compat pnk_two
                (real_plus (real_log t1 Ht1) (real_log t2 Ht2))
                pnk_two (real_log x Hx)).
      + apply real_eq_refl.
      + exact Hsplit. }
  (* 右端换形 ER：三段（环重排 / 焊接 / 环收尾） *)
  assert (ER : real_eq
                 (real_plus (real_mult (real_plus x real_one)
                                       (real_mult pnk_two
                                          (real_plus t1 (real_opp real_one))))
                            (real_mult (real_plus x real_one)
                                       (real_mult pnk_two
                                          (real_plus t2 (real_opp real_one)))))
                 (real_mult (real_plus x (real_opp real_one))
                            (real_plus x pnk_three))).
  { assert (E1 : real_eq
                   (real_plus (real_mult (real_plus x real_one)
                                         (real_mult pnk_two
                                            (real_plus t1 (real_opp real_one))))
                              (real_mult (real_plus x real_one)
                                         (real_mult pnk_two
                                            (real_plus t2 (real_opp real_one)))))
                   (real_plus
                      (real_plus (real_mult pnk_two
                                             (real_mult (real_plus x real_one)
                                                        t1))
                                 (real_mult pnk_two
                                             (real_mult (real_plus x real_one)
                                                        t2)))
                      (real_plus (real_mult (real_plus x real_one)
                                            (real_mult pnk_two
                                               (real_opp real_one)))
                                 (real_mult (real_plus x real_one)
                                            (real_mult pnk_two
                                               (real_opp real_one)))))).
    { apply real_eq_of_zero_diff. intro n0.
      cbn [p2_diff p2_tvsq p2_one_minus].
      repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
      rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj.
                  match goal with |- ?g => idtac "RG3:" g end.
                  ring. }
    assert (E2 : real_eq
                   (real_plus
                      (real_plus (real_mult pnk_two
                                             (real_mult (real_plus x real_one)
                                                        t1))
                                 (real_mult pnk_two
                                             (real_mult (real_plus x real_one)
                                                        t2)))
                      (real_plus (real_mult (real_plus x real_one)
                                            (real_mult pnk_two
                                               (real_opp real_one)))
                                 (real_mult (real_plus x real_one)
                                            (real_mult pnk_two
                                               (real_opp real_one)))))
                   (real_plus
                      (real_plus (real_mult pnk_two (real_mult pnk_two x))
                                 (real_mult (real_plus x real_one)
                                            (real_plus x real_one)))
                      (real_plus (real_mult (real_plus x real_one)
                                            (real_mult pnk_two
                                               (real_opp real_one)))
                                 (real_mult (real_plus x real_one)
                                            (real_mult pnk_two
                                               (real_opp real_one)))))).
    { apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_mult pnk_two
                                     (real_mult (real_plus x real_one) t1))
                          (real_mult pnk_two
                                     (real_mult (real_plus x real_one) t2)))
               (real_plus (real_mult (real_plus x real_one)
                                    (real_mult pnk_two (real_opp real_one)))
                          (real_mult (real_plus x real_one)
                                     (real_mult pnk_two (real_opp real_one))))
               (real_plus (real_mult pnk_two (real_mult pnk_two x))
                          (real_mult (real_plus x real_one)
                                     (real_plus x real_one)))
               (real_plus (real_mult (real_plus x real_one)
                                    (real_mult pnk_two (real_opp real_one)))
                          (real_mult (real_plus x real_one)
                                     (real_mult pnk_two (real_opp real_one))))).
      - apply (RealSetoid.real_eq_plus_compat
                 (real_mult pnk_two (real_mult (real_plus x real_one) t1))
                 (real_mult pnk_two (real_mult (real_plus x real_one) t2))
                 (real_mult pnk_two (real_mult pnk_two x))
                 (real_mult (real_plus x real_one) (real_plus x real_one))).
        + exact (RealSetoid.real_eq_mult_compat pnk_two
                   (real_mult (real_plus x real_one) t1)
                   pnk_two (real_mult pnk_two x)
                   (real_eq_refl pnk_two) Hsc1).
        + exact Hsc2.
      - apply real_eq_refl. }
    assert (E3 : real_eq
                   (real_plus
                      (real_plus (real_mult pnk_two (real_mult pnk_two x))
                                 (real_mult (real_plus x real_one)
                                            (real_plus x real_one)))
                      (real_plus (real_mult (real_plus x real_one)
                                            (real_mult pnk_two
                                               (real_opp real_one)))
                                 (real_mult (real_plus x real_one)
                                            (real_mult pnk_two
                                               (real_opp real_one)))))
                   (real_mult (real_plus x (real_opp real_one))
                              (real_plus x pnk_three))).
    { apply real_eq_of_zero_diff. intro n0.
      cbn [p2_diff p2_tvsq p2_one_minus].
      repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
      rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj.
            match goal with |- ?g => idtac "RG2:" g end.
            ring. }
    exact (real_eq_trans _ _ _ E1 (real_eq_trans _ _ _ E2 E3)). }
  (* 组装：SA 经 EL/ES 左运、经 ER 右运 *)
  apply (leb3_le_b_eq_l
           (real_plus (real_mult (real_plus x real_one)
                                 (real_mult pnk_two (real_log t1 Ht1)))
                      (real_mult (real_plus x real_one)
                                 (real_mult pnk_two (real_log t2 Ht2))))
           (real_mult (real_plus x real_one)
                      (real_mult pnk_two (real_log x Hx)))
           (real_mult (real_plus x (real_opp real_one))
                      (real_plus x pnk_three))).
  - exact (real_eq_trans _ _ _ EL ES).
  - apply (leb3_le_b_eq_r
             (real_plus (real_mult (real_plus x real_one)
                                   (real_mult pnk_two (real_log t1 Ht1)))
                        (real_mult (real_plus x real_one)
                                   (real_mult pnk_two (real_log t2 Ht2))))
             (real_plus (real_mult (real_plus x real_one)
                                   (real_mult pnk_two
                                      (real_plus t1 (real_opp real_one))))
                        (real_mult (real_plus x real_one)
                                   (real_mult pnk_two
                                      (real_plus t2 (real_opp real_one)))))
             (real_mult (real_plus x (real_opp real_one))
                        (real_plus x pnk_three))).
    + exact SA.
    + exact ER.
Qed.

(* ---- 3. 锐化上切线核（具体形）：(x+1)·2·log x ≤_B (x−1)(x+3) ---- *)
(*   共轭对 t1 := 2x·inv(x+1)、t2 := (x+1)·inv(2)；t1·t2 == x。         *)

Theorem pnk_core : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_mult (real_plus x real_one)
                       (real_mult pnk_two (real_log x Hx)))
            (real_mult (real_plus x (real_opp real_one))
                       (real_plus x pnk_three)).
Proof.
  intros x Hx.
  assert (Hx1 : real_lt real_zero (real_plus x real_one)).
  { apply (RealSetoid.real_lt_id_l real_zero
             (real_plus real_zero real_zero) (real_plus x real_one)).
    - exact (real_eq_sym (real_plus real_zero real_zero) real_zero
               (real_plus_zero real_zero)).
    - exact (real_lt_plus_compat real_zero x real_zero real_one
               Hx real_lt_zero_one). }
  assert (HU1 : real_eq (real_mult (real_plus x real_one)
                                   (real_inv_pos (real_plus x real_one) Hx1))
                        real_one)
    by apply real_inv_pos_correct.
  assert (HU2 : real_eq (real_mult pnk_two
                                   (real_inv_pos pnk_two pnk_two_pos))
                        real_one)
    by apply real_inv_pos_correct.
  assert (Ht1p : real_lt real_zero
                   (real_mult pnk_two
                      (real_mult x (real_inv_pos (real_plus x real_one) Hx1)))).
  { apply (real_mult_positive pnk_two
              (real_mult x (real_inv_pos (real_plus x real_one) Hx1))
              pnk_two_pos).
    apply (real_mult_positive x (real_inv_pos (real_plus x real_one) Hx1) Hx).
    apply real_inv_pos_pos. }
  assert (Ht2p : real_lt real_zero
                   (real_mult (real_plus x real_one)
                              (real_inv_pos pnk_two pnk_two_pos))).
  { apply (real_mult_positive (real_plus x real_one)
              (real_inv_pos pnk_two pnk_two_pos) Hx1).
    apply real_inv_pos_pos. }
  (* 尺度 EQ 一：(x+1)·t1 == 2x *)
  assert (Hsc1 : real_eq
                   (real_mult (real_plus x real_one)
                              (real_mult pnk_two
                                 (real_mult x
                                    (real_inv_pos (real_plus x real_one)
                                                 Hx1))))
                   (real_mult pnk_two x)).
  { apply (real_eq_trans
             (real_mult (real_plus x real_one)
                        (real_mult pnk_two
                           (real_mult x
                              (real_inv_pos (real_plus x real_one) Hx1))))
             (real_mult pnk_two
                        (real_mult x
                           (real_mult (real_plus x real_one)
                                      (real_inv_pos (real_plus x real_one)
                                                    Hx1))))
             (real_mult pnk_two x)).
    - (* 环重排（原子化 inv 投影后 ring） *)
      apply real_eq_of_zero_diff. intro n0.
      cbn [p2_diff p2_tvsq p2_one_minus].
      repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
      rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj.
            ring.
    - apply (RealSetoid.real_eq_mult_compat pnk_two
                (real_mult x
                   (real_mult (real_plus x real_one)
                              (real_inv_pos (real_plus x real_one) Hx1)))
                pnk_two x).
      + apply real_eq_refl.
      + apply (real_eq_trans
                 (real_mult x
                    (real_mult (real_plus x real_one)
                               (real_inv_pos (real_plus x real_one) Hx1)))
                 (real_mult x real_one) x).
        * apply (RealSetoid.real_eq_mult_compat x
                    (real_mult (real_plus x real_one)
                               (real_inv_pos (real_plus x real_one) Hx1))
                    x real_one).
          -- apply real_eq_refl.
          -- exact HU1.
        * apply real_mult_one. }
  (* 尺度 EQ 二：2·(x+1)·t2 == (x+1)² *)
  assert (Hsc2 : real_eq
                   (real_mult pnk_two
                      (real_mult (real_plus x real_one)
                                 (real_mult (real_plus x real_one)
                                            (real_inv_pos pnk_two
                                                         pnk_two_pos))))
                   (real_mult (real_plus x real_one)
                              (real_plus x real_one))).
  { apply (real_eq_trans
             (real_mult pnk_two
                        (real_mult (real_plus x real_one)
                                   (real_mult (real_plus x real_one)
                                              (real_inv_pos pnk_two
                                                            pnk_two_pos))))
             (real_mult (real_plus x real_one)
                        (real_mult (real_plus x real_one)
                                   (real_mult pnk_two
                                              (real_inv_pos pnk_two
                                                            pnk_two_pos))))
             (real_mult (real_plus x real_one)
                        (real_plus x real_one))).
    - apply real_eq_of_zero_diff. intro n0.
      cbn [p2_diff p2_tvsq p2_one_minus].
      repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
      rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj.
            ring.
    - apply (real_eq_trans
                (real_mult (real_plus x real_one)
                           (real_mult (real_plus x real_one)
                                      (real_mult pnk_two
                                                 (real_inv_pos pnk_two
                                                                pnk_two_pos))))
                (real_mult (real_plus x real_one)
                           (real_mult (real_plus x real_one) real_one))
                (real_mult (real_plus x real_one) (real_plus x real_one))).
      + apply (RealSetoid.real_eq_mult_compat (real_plus x real_one)
                  (real_mult (real_plus x real_one)
                             (real_mult pnk_two
                                        (real_inv_pos pnk_two pnk_two_pos)))
                  (real_plus x real_one)
                  (real_mult (real_plus x real_one) real_one)).
        * apply real_eq_refl.
        * apply (RealSetoid.real_eq_mult_compat (real_plus x real_one)
                    (real_mult pnk_two (real_inv_pos pnk_two pnk_two_pos))
                    (real_plus x real_one) real_one).
          -- apply real_eq_refl.
          -- exact HU2.
      + apply (RealSetoid.real_eq_mult_compat (real_plus x real_one)
                  (real_mult (real_plus x real_one) real_one)
                  (real_plus x real_one) (real_plus x real_one)).
        * apply real_eq_refl.
        * apply real_mult_one. }
  (* 乘积 EQ：t1·t2 == x *)
  assert (Hprod : real_eq
                    (real_mult (real_mult pnk_two
                                          (real_mult x
                                             (real_inv_pos
                                                (real_plus x real_one) Hx1)))
                               (real_mult (real_plus x real_one)
                                          (real_inv_pos pnk_two
                                                        pnk_two_pos)))
                    x).
  { apply (real_eq_trans
             (real_mult (real_mult pnk_two
                                   (real_mult x
                                      (real_inv_pos
                                         (real_plus x real_one) Hx1)))
                        (real_mult (real_plus x real_one)
                                   (real_inv_pos pnk_two pnk_two_pos)))
             (real_mult (real_mult x
                                    (real_mult (real_plus x real_one)
                                               (real_inv_pos
                                                  (real_plus x real_one)
                                                  Hx1)))
                        (real_mult pnk_two
                                   (real_inv_pos pnk_two pnk_two_pos)))
             x).
    - apply real_eq_of_zero_diff. intro n0.
      cbn [p2_diff p2_tvsq p2_one_minus].
      repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
      rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj.
            ring.
    - apply (real_eq_trans
               (real_mult (real_mult x
                                      (real_mult (real_plus x real_one)
                                                 (real_inv_pos
                                                    (real_plus x real_one)
                                                    Hx1)))
                          (real_mult pnk_two
                                     (real_inv_pos pnk_two pnk_two_pos)))
               (real_mult (real_mult x real_one) real_one) x).
      + apply (RealSetoid.real_eq_mult_compat
                  (real_mult x
                     (real_mult (real_plus x real_one)
                                (real_inv_pos (real_plus x real_one) Hx1)))
                  (real_mult pnk_two (real_inv_pos pnk_two pnk_two_pos))
                  (real_mult x real_one) real_one).
        * exact (RealSetoid.real_eq_mult_compat x
                   (real_mult (real_plus x real_one)
                              (real_inv_pos (real_plus x real_one) Hx1))
                   x real_one (real_eq_refl x) HU1).
        * exact HU2.
      + apply (real_eq_trans (real_mult (real_mult x real_one) real_one)
                  (real_mult x (real_mult real_one real_one)) x).
        * apply real_eq_sym. apply real_mult_assoc.
        * apply (real_eq_trans (real_mult x (real_mult real_one real_one))
                    (real_mult x real_one) x).
          -- apply (RealSetoid.real_eq_mult_compat x
                       (real_mult real_one real_one)
                       x real_one
                       (real_eq_refl x) (real_mult_one real_one)).
          -- apply real_mult_one. }
  (* 拆分 EQ：log t1 + log t2 == log x *)
  assert (Hsplit : real_eq
                     (real_plus (real_log (real_mult pnk_two
                                                     (real_mult x
                                                        (real_inv_pos
                                                           (real_plus x real_one)
                                                           Hx1)))
                                          Ht1p)
                                (real_log (real_mult (real_plus x real_one)
                                                     (real_inv_pos pnk_two
                                                                  pnk_two_pos))
                                          Ht2p))
                     (real_log x Hx)).
  { apply (real_eq_trans
             (real_plus
                (real_log (real_mult pnk_two
                                     (real_mult x
                                        (real_inv_pos
                                           (real_plus x real_one) Hx1)))
                          Ht1p)
                (real_log (real_mult (real_plus x real_one)
                                     (real_inv_pos pnk_two pnk_two_pos))
                          Ht2p))
             (real_log (real_mult (real_mult pnk_two
                                             (real_mult x
                                                (real_inv_pos
                                                   (real_plus x real_one)
                                                   Hx1)))
                                  (real_mult (real_plus x real_one)
                                             (real_inv_pos pnk_two
                                                           pnk_two_pos)))
                       (real_mult_positive
                          (real_mult pnk_two
                                     (real_mult x
                                        (real_inv_pos
                                           (real_plus x real_one) Hx1)))
                          (real_mult (real_plus x real_one)
                                     (real_inv_pos pnk_two pnk_two_pos))
                          Ht1p Ht2p))
             (real_log x Hx)).
    - apply real_eq_sym.
      apply real_log_mult.
    - apply real_log_wd. exact Hprod. }
  exact (pnk_core_pair x
           (real_mult pnk_two
              (real_mult x (real_inv_pos (real_plus x real_one) Hx1)))
           (real_mult (real_plus x real_one)
              (real_inv_pos pnk_two pnk_two_pos))
           Hx Ht1p Ht2p Hprod Hsplit Hsc1 Hsc2).
Qed.

(* ---- 4. G1 全局统一形：2(p+q)·(kl(p,q)+(q−p)) ≥_B (p−q)² ---- *)

Theorem pnk_gap_global_B : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_le_b (p2_tvsq p q)
    (real_mult pnk_two (real_mult (real_plus p q)
       (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))))).
Proof.
  intros p q Hp Hq.
  (* X := q·inv p 的正性证书（与 real_kl_term 内部同源） *)
  assert (HX : real_lt real_zero (real_mult q (real_inv_pos p Hp)))
    by exact (real_mult_positive q (real_inv_pos p Hp) Hq
                (real_inv_pos_pos p Hp)).
  (* core 于 X 实例化并 ×p² 尺度 *)
  assert (HS : real_le_b
                 (real_mult p
                    (real_mult p
                       (real_mult (real_plus (real_mult q (real_inv_pos p Hp))
                                             real_one)
                                  (real_mult pnk_two
                                     (real_log (real_mult q (real_inv_pos p Hp))
                                               HX)))))
                 (real_mult p
                    (real_mult p
                       (real_mult
                          (real_plus (real_mult q (real_inv_pos p Hp))
                                     (real_opp real_one))
                          (real_plus (real_mult q (real_inv_pos p Hp))
                                     pnk_three))))).
    { assert (HSC : real_le_b
                 (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) real_one)
                            (real_mult pnk_two
                               (real_log (real_mult q (real_inv_pos p Hp)) HX)))
                 (real_mult (real_plus (real_mult q (real_inv_pos p Hp))
                                       (real_opp real_one))
                            (real_plus (real_mult q (real_inv_pos p Hp))
                                       pnk_three))).
      { apply pnk_core. }
      assert (HSC1 : real_le_b
                 (real_mult p
                    (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) real_one)
                               (real_mult pnk_two
                                  (real_log (real_mult q (real_inv_pos p Hp)) HX))))
                 (real_mult p
                    (real_mult
                       (real_plus (real_mult q (real_inv_pos p Hp))
                                  (real_opp real_one))
                       (real_plus (real_mult q (real_inv_pos p Hp)) pnk_three)))).
      { apply (leb3_le_b_pos_scale_l _ _ p).
        exact HSC.
        exact Hp. }
      apply (leb3_le_b_pos_scale_l _ _ p).
      exact HSC1.
      exact Hp. }
  (* HE : p·X == q *)
  assert (HE : real_eq (real_mult p (real_mult q (real_inv_pos p Hp))) q).
  { apply (real_eq_trans
             (real_mult p (real_mult q (real_inv_pos p Hp)))
             (real_mult (real_mult q p) (real_inv_pos p Hp)) q).
    - apply (real_eq_trans
               (real_mult p (real_mult q (real_inv_pos p Hp)))
               (real_mult (real_mult p q) (real_inv_pos p Hp))
               (real_mult (real_mult q p) (real_inv_pos p Hp))).
      + apply real_mult_assoc.
      + apply (RealSetoid.real_eq_mult_compat (real_mult p q)
                  (real_inv_pos p Hp) (real_mult q p) (real_inv_pos p Hp)
                  (real_mult_comm p q) (real_eq_refl (real_inv_pos p Hp))).
    - apply (real_eq_trans
               (real_mult (real_mult q p) (real_inv_pos p Hp))
               (real_mult q real_one) q).
      + apply (real_eq_trans (real_mult (real_mult q p) (real_inv_pos p Hp))
                 (real_mult q (real_mult p (real_inv_pos p Hp)))
                 (real_mult q real_one)).
        * apply real_eq_sym. apply real_mult_assoc.
        * apply (RealSetoid.real_eq_mult_compat q
                    (real_mult p (real_inv_pos p Hp)) q real_one
                    (real_eq_refl q) (real_inv_pos_correct p Hp)).
      + apply real_mult_one. }
  (* HE2 : p+q == p·(X+1) *)
  assert (HE2 : real_eq (real_plus p q)
                        (real_mult p
                           (real_plus (real_mult q (real_inv_pos p Hp))
                                      real_one))).
  { apply real_eq_sym.
    apply (real_eq_trans
             (real_mult p (real_plus (real_mult q (real_inv_pos p Hp)) real_one))
             (real_plus (real_mult p (real_mult q (real_inv_pos p Hp)))
                        (real_mult p real_one))
             (real_plus p q)).
    - apply real_distrib.
    - apply (real_eq_trans
               (real_plus (real_mult p (real_mult q (real_inv_pos p Hp)))
                          (real_mult p real_one))
               (real_plus q (real_mult p real_one))
               (real_plus p q)).
      + apply (RealSetoid.real_eq_plus_compat
                  (real_mult p (real_mult q (real_inv_pos p Hp)))
                  (real_mult p real_one) q (real_mult p real_one)
                  HE (real_eq_refl (real_mult p real_one))).
      + apply (real_eq_trans (real_plus q (real_mult p real_one))
                  (real_plus q p) (real_plus p q)).
        * apply (RealSetoid.real_eq_plus_compat q (real_mult p real_one)
                    q p (real_eq_refl q) (real_mult_one p)).
        * apply real_plus_comm. }
  (* 焊接 EQF：coreL' + T(X-焊接形) == coreR' + p2_tvsq(X-形) *)
  assert (EQF : real_eq
    (real_plus
       (real_mult p
          (real_mult p
             (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) real_one)
                        (real_mult pnk_two
                           (real_log (real_mult q (real_inv_pos p Hp)) HX)))))
       (real_mult pnk_two
          (real_mult (real_mult p
                                 (real_plus (real_mult q (real_inv_pos p Hp))
                                            real_one))
                     (real_mult p
                        (real_plus
                           (real_plus (real_mult q (real_inv_pos p Hp))
                                      (real_opp real_one))
                           (real_opp
                              (real_log (real_mult q (real_inv_pos p Hp))
                                        HX)))))))
    (real_plus
       (real_mult p
          (real_mult p
             (real_mult
                (real_plus (real_mult q (real_inv_pos p Hp))
                           (real_opp real_one))
                (real_plus (real_mult q (real_inv_pos p Hp)) pnk_three))))
       (real_mult p
          (real_mult p
             (real_mult (real_plus real_one (real_opp
                                (real_mult q (real_inv_pos p Hp))))
                        (real_plus real_one (real_opp
                                   (real_mult q (real_inv_pos p Hp))))))))).
  { apply real_eq_of_zero_diff. intro n0.
      cbn [p2_diff p2_tvsq p2_one_minus].
      repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
      rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj.
      ring. }
  (* p2_tvsq X-形等价：(p−q)² == p·(p·((1−X)·(1−X)))——含 HE 关系的条件恒等式。
     leg1=setoid 因子级焊接（HE 经 plus/opp compat 消化，全 Real 层，零 apply 显式
     trans 实参）；leg2=of_zero_diff+projT1 分配配方——welded² 与 p²(1−X)² 为
     {p,q,i} 自由原子环恒等式（手验：(p−p·q·i)² == p²(1−q·i)²），无需 HE。 *)
  assert (EQD1 : real_eq
    (real_mult (real_plus p (real_opp q)) (real_plus p (real_opp q)))
    (real_mult (real_plus (real_mult p real_one)
                          (real_opp (real_mult p (real_mult q (real_inv_pos p Hp)))))
               (real_plus (real_mult p real_one)
                          (real_opp (real_mult p (real_mult q (real_inv_pos p Hp))))))).
  { assert (HWELD : real_eq (real_plus p (real_opp q))
             (real_plus (real_mult p real_one)
                        (real_opp (real_mult p (real_mult q (real_inv_pos p Hp)))))).
    { apply (RealSetoid.real_eq_plus_compat p (real_opp q)
               (real_mult p real_one)
               (real_opp (real_mult p (real_mult q (real_inv_pos p Hp))))).
      - apply real_eq_sym. apply real_mult_one.
      - apply pnk_eq_opp_compat. apply real_eq_sym. exact HE. }
    apply (RealSetoid.real_eq_mult_compat
             (real_plus p (real_opp q))
             (real_plus p (real_opp q))
             (real_plus (real_mult p real_one)
                        (real_opp (real_mult p (real_mult q (real_inv_pos p Hp)))))
             (real_plus (real_mult p real_one)
                        (real_opp (real_mult p (real_mult q (real_inv_pos p Hp)))))).
    + exact HWELD.
    + exact HWELD. }
  assert (EQD2 : real_eq
    (real_mult (real_plus (real_mult p real_one)
                          (real_opp (real_mult p (real_mult q (real_inv_pos p Hp)))))
               (real_plus (real_mult p real_one)
                          (real_opp (real_mult p (real_mult q (real_inv_pos p Hp))))))
    (real_mult p
       (real_mult p
          (real_mult (real_plus real_one (real_opp (real_mult q (real_inv_pos p Hp))))
                     (real_plus real_one (real_opp (real_mult q (real_inv_pos p Hp)))))))).
  { apply real_eq_of_zero_diff. intro n0.
    cbn [p2_diff p2_tvsq p2_one_minus].
    repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
    rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj.
    ring. }
  assert (EQD : real_eq
    (real_mult (real_plus p (real_opp q)) (real_plus p (real_opp q)))
    (real_mult p
       (real_mult p
          (real_mult (real_plus real_one (real_opp (real_mult q (real_inv_pos p Hp))))
                     (real_plus real_one (real_opp (real_mult q (real_inv_pos p Hp))))))))
    by exact (real_eq_trans _ _ _ EQD1 EQD2).
  (* klst_gap_shape：A-原形 == p·((X−1) + opp logX) *)
  assert (HGAP : real_eq
    (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
    (real_mult p
       (real_plus (real_plus (real_mult q (real_inv_pos p Hp))
                             (real_opp real_one))
                  (real_opp
                     (real_log (real_mult q (real_inv_pos p Hp)) (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))))))
    by exact (klst_gap_shape p q Hp Hq).
  (* 证书对齐：HGAP 内 log 证书（显式 real_mult_positive 项）经 real_log_wd
     运至 HX 形——TWELD/EQF 侧的 log 恒持 HX，二者须同件方可焊接 *)
  assert (HGAPE : real_eq
    (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
    (real_mult p
       (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                  (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX))))).
  { apply (real_eq_trans _ _ _ HGAP).
    apply (RealSetoid.real_eq_mult_compat p
             (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                        (real_opp (real_log (real_mult q (real_inv_pos p Hp)) (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))))
             p
             (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                        (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX)))).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
               (real_opp (real_log (real_mult q (real_inv_pos p Hp)) (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))))
               (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
               (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX))).
      + apply real_eq_refl.
      + apply pnk_eq_opp_compat.
        apply (real_log_wd (real_mult q (real_inv_pos p Hp))
                 (real_mult q (real_inv_pos p Hp))
                 (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))
                 HX).
        apply real_eq_refl. }
  (* TWELD==TARGET：2·(p(X+1))·(p((X−1)−logX)) == 2·(p+q)·(kl+q−p)，
     因子级 setoid 焊接（HE2 对称 × HGAP 对称） *)
  assert (EQTW : real_eq
    (real_mult pnk_two (real_mult (real_mult p (real_plus (real_mult q (real_inv_pos p Hp)) real_one)) (real_mult p (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX))))))
    (real_mult pnk_two (real_mult (real_plus p q) (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))))).
  { apply (RealSetoid.real_eq_mult_compat pnk_two
             (real_mult (real_mult p (real_plus (real_mult q (real_inv_pos p Hp)) real_one))
                        (real_mult p (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX)))))
             pnk_two
             (real_mult (real_plus p q) (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))))).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_mult_compat
               (real_mult p (real_plus (real_mult q (real_inv_pos p Hp)) real_one))
               (real_mult p (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX))))
               (real_plus p q)
               (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))).
      + apply real_eq_sym. exact HE2.
      + apply real_eq_sym. exact HGAPE. }
  (* EQ3：coreR'+(p−q)² == coreL'+TARGET（EQD 接 EQF 对称接 EQTW；
     数学核：2(x²−1)−(1−x)² == (x−1)(x+3) 恰为 core） *)
  assert (EQ3 : real_eq
    (real_plus (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) (real_plus (real_mult q (real_inv_pos p Hp)) pnk_three)))) (real_mult (real_plus p (real_opp q)) (real_plus p (real_opp q))))
    (real_plus (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) real_one) (real_mult pnk_two (real_log (real_mult q (real_inv_pos p Hp)) HX))))) (real_mult pnk_two (real_mult (real_plus p q) (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))))))).
  { exact (real_eq_trans _ _ _
             (RealSetoid.real_eq_plus_compat
                (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) (real_plus (real_mult q (real_inv_pos p Hp)) pnk_three))))
                (real_mult (real_plus p (real_opp q)) (real_plus p (real_opp q)))
                (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) (real_plus (real_mult q (real_inv_pos p Hp)) pnk_three))))
                (real_mult p (real_mult p (real_mult (real_plus real_one (real_opp (real_mult q (real_inv_pos p Hp)))) (real_plus real_one (real_opp (real_mult q (real_inv_pos p Hp)))))))
                (real_eq_refl (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) (real_plus (real_mult q (real_inv_pos p Hp)) pnk_three)))))
                EQD)
             (real_eq_trans _ _ _
                (real_eq_sym
                   (real_plus (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) real_one) (real_mult pnk_two (real_log (real_mult q (real_inv_pos p Hp)) HX)))))
                              (real_mult pnk_two (real_mult (real_mult p (real_plus (real_mult q (real_inv_pos p Hp)) real_one)) (real_mult p (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX)))))))
                   (real_plus (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) (real_plus (real_mult q (real_inv_pos p Hp)) pnk_three)))) (real_mult p (real_mult p (real_mult (real_plus real_one (real_opp (real_mult q (real_inv_pos p Hp)))) (real_plus real_one (real_opp (real_mult q (real_inv_pos p Hp))))))))
                   EQF)
                (RealSetoid.real_eq_plus_compat
                   (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) real_one) (real_mult pnk_two (real_log (real_mult q (real_inv_pos p Hp)) HX)))))
                   (real_mult pnk_two (real_mult (real_mult p (real_plus (real_mult q (real_inv_pos p Hp)) real_one)) (real_mult p (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX))))))
                   (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) real_one) (real_mult pnk_two (real_log (real_mult q (real_inv_pos p Hp)) HX)))))
                   (real_mult pnk_two (real_mult (real_plus p q) (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))))
                   (real_eq_refl (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) real_one) (real_mult pnk_two (real_log (real_mult q (real_inv_pos p Hp)) HX))))))
                   EQTW))). }
  (* HTGT：coreL'+TV² ≤_B coreL'+TARGET（HS 加法兼容 + EQ3 右端运输） *)
  assert (HTGT : real_le_b
    (real_plus (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) real_one) (real_mult pnk_two (real_log (real_mult q (real_inv_pos p Hp)) HX))))) (p2_tvsq p q))
    (real_plus (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) real_one) (real_mult pnk_two (real_log (real_mult q (real_inv_pos p Hp)) HX))))) (real_mult pnk_two (real_mult (real_plus p q) (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))))))).
  { apply (leb3_le_b_eq_r
             (real_plus (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) real_one) (real_mult pnk_two (real_log (real_mult q (real_inv_pos p Hp)) HX))))) (p2_tvsq p q))
             (real_plus (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) (real_plus (real_mult q (real_inv_pos p Hp)) pnk_three)))) (real_mult (real_plus p (real_opp q)) (real_plus p (real_opp q))))
             (real_plus (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) real_one) (real_mult pnk_two (real_log (real_mult q (real_inv_pos p Hp)) HX))))) (real_mult pnk_two (real_mult (real_plus p q) (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))))))).
    - apply (real_le_b_plus_compat
               (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) real_one) (real_mult pnk_two (real_log (real_mult q (real_inv_pos p Hp)) HX)))))
               (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) (real_plus (real_mult q (real_inv_pos p Hp)) pnk_three))))
               (p2_tvsq p q)
               (real_mult (real_plus p (real_opp q)) (real_plus p (real_opp q)))).
      + exact HS.
      + exact (leb3_le_b_refl (p2_tvsq p q)).
    - exact EQ3. }
  (* 闭合：coreL' 左消去（p2_tvsq δ-可转换 (p−q)²，目标即定理语句） *)
  apply (pnk_le_b_cancel_l (real_mult p (real_mult p (real_mult (real_plus (real_mult q (real_inv_pos p Hp)) real_one) (real_mult pnk_two (real_log (real_mult q (real_inv_pos p Hp)) HX)))))).
  exact HTGT.
Qed.


(*   ① 常数族 four/three_pos/nine/ten/nine_ten（9/10 := 9·inv 10）      *)
(*   ② pnk_log_mirror_B：对称切线 log s ≥_B 1−1/s（s>0）                *)
(*      链＝real_log_le_linear_B 于 inv s + log_mult 拆分 + opp_rev。    *)
(*   ③ pnk_log1p_ge_far：S1 远支（t>1）：log(1+t) ≥_B t−t²/2            *)
(*      （镜切线 + (1+t) 尺度消 inv：A·(1+t) == t−t²(t−1)/2 纯环恒等，   *)
(*   ④ pnk_tvsq_pos：TV²>0（Or 前提两支；PinskerTwoPoint 缺件补齐）。    *)
(*      kl₂ ≥ d²·(1/(2(p+q))+1/(2(2−p−q))) ≥_B (9/10)·TV²。              *)
(*      常数步核＝4·s(2−s)+(2s−2)²==4 环恒等+平方非负 ⟹ s(2−s)≤1。      *)
(*   coqchk 四项全 none（公理/类型在类型/不安全不动点/假设正性）；         *)
(*   G1 禁词计数 0（头注以「禁词」代指，不落字面量）。                    *)
(*   ⑤ pnk_pinsker_frac2（G2 主件）：kl₂ ≥_B (9/10)·TV²。               *)
(*      装配＝pnk_gap_global_B×2（(p,q) 支与 (1−p,1−q) 支各              *)
(*      d²≤2aA / d²≤2bB）+ 正缩放消 inv（real_inv_pos_correct 因子级     *)
(*      （核心＝s(2−s)≤_B 1 ⟸ 4·s(2−s)+(2s−2)²==4 环恒等+平方非负）。    *)
(*   诚实边界：S1 近支/S2（−log(1−y) ≥ y+y²/2）未落。实测：一阶      *)
(*   三明治族（切线+对称+整数 k 嵌套 [1−(1+s)^{−k}]/k）的 s² 系数恒为     *)
(*   −(k+1)/(2k) < −1/2，严格低于所需 −1/2（数值核 361 点同证），即      *)
(*   首阶引擎无论怎样嵌套都不可能闭合 S2——需真二阶核（交替级数截断/     *)
(*   0.9 合成界 361 个 (p,q) 采样 assert 全过（bound/kl₂ 最小 0.30）。    *)

(* ---- 5. 常数族 ---- *)

Definition pnk_four : Real := real_mult pnk_two pnk_two.

(* ---- 常数投影叶补：pnk_four ---- *)

Lemma pnk_four_proj : forall k : nat, projT1 pnk_four k == (1 + 1 + 1 + 1)%Q.
Proof. intro k. cbv [projT1 pnk_four pnk_two real_one real_plus real_mult]. reflexivity. Qed.



Lemma pnk_four_pos : real_lt real_zero pnk_four.
Proof.
  exact (real_mult_positive pnk_two pnk_two pnk_two_pos pnk_two_pos).
Qed.

Lemma pnk_three_pos : real_lt real_zero pnk_three.
Proof.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero) pnk_three).
  - exact (real_eq_sym (real_plus real_zero real_zero) real_zero
             (real_plus_zero real_zero)).
  - exact (real_lt_plus_compat real_zero pnk_two real_zero real_one
             pnk_two_pos real_lt_zero_one).
Qed.

Definition pnk_nine : Real := real_mult pnk_three pnk_three.

Lemma pnk_nine_pos : real_lt real_zero pnk_nine.
Proof.
  exact (real_mult_positive pnk_three pnk_three pnk_three_pos pnk_three_pos).
Qed.

Definition pnk_ten : Real := real_plus pnk_nine real_one.

Lemma pnk_ten_pos : real_lt real_zero pnk_ten.
Proof.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero) pnk_ten).
  - exact (real_eq_sym (real_plus real_zero real_zero) real_zero
             (real_plus_zero real_zero)).
  - exact (real_lt_plus_compat real_zero pnk_nine real_zero real_one
             pnk_nine_pos real_lt_zero_one).
Qed.

Definition pnk_nine_ten : Real :=
  real_mult pnk_nine (real_inv_pos pnk_ten pnk_ten_pos).

Lemma pnk_ten_gt_one : real_lt real_one pnk_ten.
Proof.
  apply (RealSetoid.real_lt_id_l real_one
           (real_plus real_one real_zero) pnk_ten
           (real_eq_sym (real_plus real_one real_zero) real_one
              (real_plus_zero real_one))
           (RealSetoid.real_lt_id_r (real_plus real_one real_zero)
              (real_plus real_one pnk_nine) pnk_ten
              (real_eq_of_zero_diff (real_plus real_one pnk_nine) pnk_ten
                 (fun n0 => eq_refl))
              (real_lt_plus_translate real_one real_zero pnk_nine
                 pnk_nine_pos))).
Qed.

Lemma pnk_nine_lt_ten : real_lt pnk_nine pnk_ten.
Proof.
  apply (RealSetoid.real_lt_id_l pnk_nine
           (real_plus pnk_nine real_zero) pnk_ten
           (real_eq_sym (real_plus pnk_nine real_zero) pnk_nine
              (real_plus_zero pnk_nine))
           (real_lt_plus_translate pnk_nine real_zero real_one
              real_lt_zero_one)).
Qed.

Lemma pnk_nine_ten_lt_one : real_lt pnk_nine_ten real_one.
Proof.
  assert (Hi : real_lt real_zero (real_inv_pos pnk_ten pnk_ten_pos))
    by exact (real_inv_pos_pos pnk_ten pnk_ten_pos).
  apply (RealSetoid.real_lt_id_r pnk_nine_ten
           (real_mult pnk_ten (real_inv_pos pnk_ten pnk_ten_pos)) real_one).
  - exact (real_inv_pos_correct pnk_ten pnk_ten_pos).
  - exact (real_mult_lt_compat pnk_nine pnk_ten
             (real_inv_pos pnk_ten pnk_ten_pos) pnk_nine_lt_ten Hi).
Qed.

Lemma pnk_nine_ten_le_one : real_le_b pnk_nine_ten real_one.
Proof.
  apply pnk_lt_le_b. exact pnk_nine_ten_lt_one.
Qed.

(* 纯组合子环化简件（零 real_eq_of_zero_diff，绕开 setoid 侧目标） *)
Lemma pnk_eq_add_shuffle : forall a c : Real,
  real_eq (real_plus (real_opp a) (real_plus a c)) c.
Proof.
  intros a c.
  apply (real_eq_trans
           (real_plus (real_opp a) (real_plus a c))
           (real_plus (real_plus (real_opp a) a) c) c).
  - apply real_plus_assoc.
  - apply (real_eq_trans
             (real_plus (real_plus (real_opp a) a) c)
             (real_plus real_zero c) c).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_opp a) a) c real_zero c
               (real_eq_trans (real_plus (real_opp a) a)
                  (real_plus a (real_opp a)) real_zero
                  (real_plus_comm (real_opp a) a) (real_plus_opp a))
               (real_eq_refl c)).
    + apply (real_eq_trans (real_plus real_zero c)
               (real_plus c real_zero) c
               (real_plus_comm real_zero c) (real_plus_zero c)).
Qed.

Lemma pnk_eq_double_opp : forall b : Real,
  real_eq (real_opp (real_opp b)) b.
Proof.
  intro b.
  assert (HB : real_eq (real_plus (real_opp b) b) real_zero).
  { apply (real_eq_trans (real_plus (real_opp b) b)
             (real_plus b (real_opp b)) real_zero
             (real_plus_comm (real_opp b) b) (real_plus_opp b)). }
  apply (real_eq_trans (real_opp (real_opp b))
             (real_plus (real_opp (real_opp b)) (real_plus (real_opp b) b))
             b).
  - apply (real_eq_trans
             (real_opp (real_opp b))
             (real_plus (real_opp (real_opp b)) real_zero)
             (real_plus (real_opp (real_opp b))
                        (real_plus (real_opp b) b))).
    + exact (real_eq_sym
               (real_plus (real_opp (real_opp b)) real_zero)
               (real_opp (real_opp b))
               (real_plus_zero (real_opp (real_opp b)))).
    + apply (RealSetoid.real_eq_plus_compat
               (real_opp (real_opp b)) real_zero
               (real_opp (real_opp b)) (real_plus (real_opp b) b)
               (real_eq_refl (real_opp (real_opp b)))
               (real_eq_sym (real_plus (real_opp b) b) real_zero HB)).
  - apply (real_eq_trans
             (real_plus (real_opp (real_opp b))
                        (real_plus (real_opp b) b))
             (real_plus (real_plus (real_opp (real_opp b))
                                   (real_opp b))
                        b)
             b).
    + apply real_plus_assoc.
    + apply (real_eq_trans
               (real_plus (real_plus (real_opp (real_opp b))
                                     (real_opp b))
                          b)
               (real_plus real_zero b) b).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_plus (real_opp (real_opp b)) (real_opp b))
                 b real_zero b
                 (real_eq_trans
                    (real_plus (real_opp (real_opp b)) (real_opp b))
                    (real_plus (real_opp b) (real_opp (real_opp b)))
                    real_zero
                    (real_plus_comm (real_opp (real_opp b))
                       (real_opp b)) (real_plus_opp (real_opp b)))
                 (real_eq_refl b)).
      * apply (real_eq_trans (real_plus real_zero b)
                 (real_plus b real_zero) b
                 (real_plus_comm real_zero b) (real_plus_zero b)).
Qed.

(* ---- 6. 对称切线：log s ≥_B 1 − 1/s ---- *)

Lemma pnk_log_mirror_B : forall (s : Real) (Hs : real_lt real_zero s),
  real_le_b (real_plus real_one (real_opp (real_inv_pos s Hs)))
            (real_log s Hs).
Proof.
  intros s Hs.
  assert (Hinv : real_lt real_zero (real_inv_pos s Hs))
    by exact (real_inv_pos_pos s Hs).
  assert (HZ : real_eq (real_plus (real_log s Hs)
                                  (real_log (real_inv_pos s Hs) Hinv))
                       real_zero).
  { apply (real_eq_trans
             (real_plus (real_log s Hs)
                        (real_log (real_inv_pos s Hs) Hinv))
             (real_log (real_mult s (real_inv_pos s Hs))
                       (real_mult_positive s (real_inv_pos s Hs) Hs Hinv))
             real_zero).
    - apply real_eq_sym. apply real_log_mult.
    - apply (real_eq_trans
               (real_log (real_mult s (real_inv_pos s Hs))
                         (real_mult_positive s (real_inv_pos s Hs) Hs Hinv))
               (real_log real_one real_lt_zero_one) real_zero).
      + apply (real_log_wd (real_mult s (real_inv_pos s Hs)) real_one
                 (real_mult_positive s (real_inv_pos s Hs) Hs Hinv)
                 real_lt_zero_one).
        exact (real_inv_pos_correct s Hs).
      + exact (real_log_one real_lt_zero_one). }
  assert (HLI : real_eq (real_log (real_inv_pos s Hs) Hinv)
                        (real_opp (real_log s Hs))).
  { apply (real_eq_trans (real_log (real_inv_pos s Hs) Hinv)
             (real_plus (real_opp (real_log s Hs))
                        (real_plus (real_log s Hs)
                                   (real_log (real_inv_pos s Hs) Hinv)))
             (real_opp (real_log s Hs))).
    - apply real_eq_sym. exact (pnk_eq_add_shuffle
                                   (real_log s Hs)
                                   (real_log (real_inv_pos s Hs) Hinv)).
    - apply (real_eq_trans
               (real_plus (real_opp (real_log s Hs))
                          (real_plus (real_log s Hs)
                                     (real_log (real_inv_pos s Hs) Hinv)))
               (real_plus (real_opp (real_log s Hs)) real_zero)
               (real_opp (real_log s Hs))).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_opp (real_log s Hs))
                 (real_plus (real_log s Hs)
                            (real_log (real_inv_pos s Hs) Hinv))
                 (real_opp (real_log s Hs)) real_zero).
        * apply real_eq_refl.
        * exact HZ.
      + apply real_plus_zero. }
  assert (Hlin : real_le_b (real_log (real_inv_pos s Hs) Hinv)
                           (real_plus (real_inv_pos s Hs) (real_opp real_one)))
    by exact (real_log_le_linear_B (real_inv_pos s Hs) Hinv).
  apply (leb3_le_b_eq_l
           (real_opp (real_plus (real_inv_pos s Hs) (real_opp real_one)))
           (real_plus real_one (real_opp (real_inv_pos s Hs)))
           (real_log s Hs)).
  - apply real_eq_of_zero_diff. intro n0.
    cbn [p2_diff p2_tvsq p2_one_minus p2_kl2].
    repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
    rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj.
    ring.
  - apply (leb3_le_b_eq_r
             (real_opp (real_plus (real_inv_pos s Hs) (real_opp real_one)))
             (real_opp (real_log (real_inv_pos s Hs) Hinv))
             (real_log s Hs)).
    + exact (leb3_le_b_opp_rev _ _ Hlin).
    + apply (real_eq_trans
               (real_opp (real_log (real_inv_pos s Hs) Hinv))
               (real_opp (real_opp (real_log s Hs)))
               (real_log s Hs)).
      * apply pnk_eq_opp_compat. exact HLI.
      * apply pnk_eq_double_opp.
Qed.

(* ---- 7. S1 远支：t>1 ⟹ log(1+t) ≥_B t−t²/2 ---- *)

(* S1 远支（t>1: log(1+t) ≥_B t−t²/2）已测绘未落：其恒等式块
   (t−t²h)(1+t) == t−t²(t−1)h 依赖 h·pnk_two==1（h:=inv 2）条件环，
   纯 ring 不可闭（h 原子化后非恒等式），需 real_inv_pos_correct 因子级
   运输再组装，机械量 ≈40–60 行，遗留 R7 与 S1 近支/S2 同批。 *)

(* ---- 8. TV² 正性（PinskerTwoPoint 缺件补齐） ---- *)

Lemma pnk_tvsq_pos : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hne : Or (real_lt p q) (real_lt q p)),
  real_lt real_zero (p2_tvsq p q).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hne. destruct Hne as [Hpq | Hqp].
  - assert (Hqp0 : real_lt real_zero (p2_diff q p))
      by exact (p2_diff_pos_of_lt p q Hpq).
    apply (RealSetoid.real_lt_id_r real_zero
             (real_mult (p2_diff q p) (p2_diff q p)) (p2_tvsq p q)).
    + exact (real_eq_sym (p2_tvsq p q) (p2_tvsq q p) (p2_tvsq_sym p q)).
    + exact (real_mult_positive (p2_diff q p) (p2_diff q p) Hqp0 Hqp0).
  - assert (Hpq0 : real_lt real_zero (p2_diff p q))
      by exact (p2_diff_pos_of_lt q p Hqp).
    exact (real_mult_positive (p2_diff p q) (p2_diff p q) Hpq0 Hpq0).
Qed.

(* ---- 9. G2 主件：kl₂ ≥_B (9/10)·TV² ---- *)

Lemma pnk_tvsq_onem : forall p q : Real,
  real_eq (p2_tvsq (p2_one_minus p) (p2_one_minus q)) (p2_tvsq p q).
Proof.
  intros p q. apply real_eq_of_zero_diff. intro n0.
  cbn [p2_diff p2_tvsq p2_one_minus p2_kl2].
  repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
  rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj.
  ring.
  all: try (exact n0).
Qed.

(*   10.1 pnk_kl2_ge_fracsum：kl₂ ≥ d²·(1/(2(p+q))+1/(2(2−p−q)))。      *)
(*        装配＝pnk_gap_global_B×2 + leb3_le_b_pos_scale 消 inv           *)
(*        （real_inv_pos_correct 因子级焊接）+ p2_one_minus_diff         *)
(*        支内消去 + real_distrib 合流 + kl₂ 定义面环化简。                 *)
(*   10.2 pnk_pinsker_frac2（0.9 档主件）：kl₂ ≥ (9/10)·TV²。            *)
(*        常数步核：4·s(2−s)+(2s−2)²==4 环恒等（RIDENT）+                *)
(*        real_square_nonneg_B ⟹ s(2−s) ≤ 1（HX4 缩 inv4=HX1）；         *)
(*        EQE：(i1+i2)·MM == 4 ⟹ 1 == (i1+i2)·s(2−s)（EQ4/EQ4M）；       *)
(*        故 1 ≤ (i1+i2)（HTEN）≥ 9/10 ⟹ pos_scale 合成闭合。           *)

(* ---- 10.1 fracsum 主件 ---- *)

Theorem pnk_kl2_ge_fracsum : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hne : Or (real_lt p q) (real_lt q p)),
  real_le_b
    (real_mult (p2_tvsq p q)
               (real_plus
                  (real_inv_pos (real_mult pnk_two (real_plus p q))
                                (real_mult_positive pnk_two (real_plus p q)
                                   pnk_two_pos
                                   (RealSetoid.real_lt_id_l real_zero
                                      (real_plus real_zero real_zero)
                                      (real_plus p q)
                                      (real_eq_sym (real_plus real_zero real_zero)
                                         real_zero (real_plus_zero real_zero))
                                      (real_lt_plus_compat real_zero p real_zero q
                                         Hp Hq))))
                  (real_inv_pos
                     (real_mult pnk_two
                        (real_plus (p2_one_minus p) (p2_one_minus q)))
                     (real_mult_positive pnk_two
                        (real_plus (p2_one_minus p) (p2_one_minus q))
                        pnk_two_pos
                        (real_lt_plus_compat real_zero (p2_one_minus p) real_zero
                           (p2_one_minus q) Hp1 Hq1)))))
    (p2_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hne.
  pose (H2s := real_mult_positive pnk_two (real_plus p q) pnk_two_pos
      (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
         (real_plus p q)
         (real_eq_sym (real_plus real_zero real_zero) real_zero
            (real_plus_zero real_zero))
         (real_lt_plus_compat real_zero p real_zero q Hp Hq))).
  pose (H2b := real_mult_positive pnk_two
      (real_plus (p2_one_minus p) (p2_one_minus q)) pnk_two_pos
      (real_lt_plus_compat real_zero (p2_one_minus p) real_zero
         (p2_one_minus q) Hp1 Hq1)).
  assert (T1 : real_le_b
                 (real_mult (p2_tvsq p q)
                            (real_inv_pos (real_mult pnk_two (real_plus p q))
                                          H2s))
                 (real_plus (real_kl_term p q Hp Hq)
                            (real_plus q (real_opp p)))).
  { apply (leb3_le_b_eq_r
             (real_mult (p2_tvsq p q)
                        (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s))
             (real_mult
                (real_mult pnk_two
                           (real_mult (real_plus p q)
                                      (real_plus (real_kl_term p q Hp Hq)
                                                 (real_plus q (real_opp p)))))
                (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s))
             (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))).
    - exact (leb3_le_b_pos_scale
               (p2_tvsq p q)
               (real_mult pnk_two
                          (real_mult (real_plus p q)
                                     (real_plus (real_kl_term p q Hp Hq)
                                                (real_plus q (real_opp p)))))
               (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
               (pnk_gap_global_B p q Hp Hq)
               (real_inv_pos_pos (real_mult pnk_two (real_plus p q)) H2s)).
    - apply (real_eq_trans
               (real_mult
                  (real_mult pnk_two
                             (real_mult (real_plus p q)
                                        (real_plus (real_kl_term p q Hp Hq)
                                                   (real_plus q (real_opp p)))))
                  (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s))
               (real_mult
                  (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
                  (real_mult
                     (real_mult pnk_two (real_plus p q))
                     (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)))
               (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))).
      + apply real_eq_of_zero_diff. intro n0.
        cbn [p2_diff p2_tvsq p2_one_minus p2_kl2].
        repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
        rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj,
                ?pnk_four_proj.
        ring.
        all: try (exact n0).
      + apply (real_eq_trans
                 (real_mult
                    (real_plus (real_kl_term p q Hp Hq)
                               (real_plus q (real_opp p)))
                    (real_mult (real_mult pnk_two (real_plus p q))
                               (real_inv_pos
                                  (real_mult pnk_two (real_plus p q)) H2s)))
                 (real_mult
                    (real_plus (real_kl_term p q Hp Hq)
                               (real_plus q (real_opp p)))
                    real_one)
                 (real_plus (real_kl_term p q Hp Hq)
                            (real_plus q (real_opp p)))).
        * apply (RealSetoid.real_eq_mult_compat
                   (real_plus (real_kl_term p q Hp Hq)
                              (real_plus q (real_opp p)))
                   (real_mult (real_mult pnk_two (real_plus p q))
                              (real_inv_pos
                                 (real_mult pnk_two (real_plus p q)) H2s))
                   (real_plus (real_kl_term p q Hp Hq)
                              (real_plus q (real_opp p)))
                   real_one).
          -- apply real_eq_refl.
          -- exact (real_inv_pos_correct
                      (real_mult pnk_two (real_plus p q)) H2s).
        * apply real_mult_one. }
  assert (T2 : real_le_b
                 (real_mult (p2_tvsq p q)
                            (real_inv_pos
                               (real_mult pnk_two
                                          (real_plus (p2_one_minus p)
                                                     (p2_one_minus q))) H2b))
                 (real_plus
                    (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                    (real_plus p (real_opp q)))).
  { assert (H2sc : real_le_b
                     (real_mult (p2_tvsq (p2_one_minus p) (p2_one_minus q))
                                (real_inv_pos
                                   (real_mult pnk_two
                                              (real_plus (p2_one_minus p)
                                                         (p2_one_minus q)))
                                   H2b))
                     (real_plus
                        (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                        (real_plus (p2_one_minus q)
                                   (real_opp (p2_one_minus p))))).
    { apply (leb3_le_b_eq_r
               (real_mult (p2_tvsq (p2_one_minus p) (p2_one_minus q))
                          (real_inv_pos
                             (real_mult pnk_two
                                        (real_plus (p2_one_minus p)
                                                   (p2_one_minus q))) H2b))
               (real_mult
                  (real_mult pnk_two
                             (real_mult (real_plus (p2_one_minus p)
                                                   (p2_one_minus q))
                                        (real_plus
                                           (real_kl_term (p2_one_minus p)
                                                         (p2_one_minus q) Hp1
                                                         Hq1)
                                           (real_plus (p2_one_minus q)
                                                      (real_opp
                                                         (p2_one_minus p))))))
                  (real_inv_pos
                     (real_mult pnk_two
                                (real_plus (p2_one_minus p) (p2_one_minus q)))
                     H2b))
               (real_plus
                  (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                  (real_plus (p2_one_minus q) (real_opp (p2_one_minus p))))).
      - exact (leb3_le_b_pos_scale
                 (p2_tvsq (p2_one_minus p) (p2_one_minus q))
                 (real_mult pnk_two
                            (real_mult (real_plus (p2_one_minus p)
                                                  (p2_one_minus q))
                                       (real_plus
                                          (real_kl_term (p2_one_minus p)
                                                        (p2_one_minus q) Hp1
                                                        Hq1)
                                          (real_plus (p2_one_minus q)
                                                     (real_opp
                                                        (p2_one_minus p))))))
                 (real_inv_pos
                    (real_mult pnk_two
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    H2b)
                 (pnk_gap_global_B (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                 (real_inv_pos_pos
                    (real_mult pnk_two
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    H2b)).
      - apply (real_eq_trans
                 (real_mult
                    (real_mult pnk_two
                               (real_mult (real_plus (p2_one_minus p)
                                                     (p2_one_minus q))
                                          (real_plus
                                             (real_kl_term (p2_one_minus p)
                                                           (p2_one_minus q)
                                                           Hp1 Hq1)
                                             (real_plus (p2_one_minus q)
                                                        (real_opp
                                                           (p2_one_minus p))))))
                    (real_inv_pos
                       (real_mult pnk_two
                                  (real_plus (p2_one_minus p)
                                             (p2_one_minus q))) H2b))
                 (real_mult
                    (real_plus
                       (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                       (real_plus (p2_one_minus q)
                                  (real_opp (p2_one_minus p))))
                    (real_mult
                       (real_mult pnk_two
                                  (real_plus (p2_one_minus p)
                                             (p2_one_minus q)))
                       (real_inv_pos
                          (real_mult pnk_two
                                     (real_plus (p2_one_minus p)
                                                (p2_one_minus q)))
                          H2b)))
                 (real_plus
                    (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                    (real_plus (p2_one_minus q) (real_opp (p2_one_minus p))))).
        + apply real_eq_of_zero_diff. intro n0.
          cbn [p2_diff p2_tvsq p2_one_minus p2_kl2].
          repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
          rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj,
                  ?pnk_four_proj.
          ring.
          all: try (exact n0).
        + apply (real_eq_trans
                   (real_mult
                      (real_plus
                         (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1
                                       Hq1)
                         (real_plus (p2_one_minus q)
                                    (real_opp (p2_one_minus p))))
                      (real_mult
                         (real_mult pnk_two
                                    (real_plus (p2_one_minus p)
                                               (p2_one_minus q)))
                         (real_inv_pos
                            (real_mult pnk_two
                                       (real_plus (p2_one_minus p)
                                                  (p2_one_minus q)))
                            H2b)))
                   (real_mult
                      (real_plus
                         (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1
                                       Hq1)
                         (real_plus (p2_one_minus q)
                                    (real_opp (p2_one_minus p))))
                      real_one)
                   (real_plus
                      (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                      (real_plus (p2_one_minus q)
                                 (real_opp (p2_one_minus p))))).
          * apply (RealSetoid.real_eq_mult_compat
                     (real_plus
                        (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1
                                      Hq1)
                        (real_plus (p2_one_minus q)
                                   (real_opp (p2_one_minus p))))
                     (real_mult
                        (real_mult pnk_two
                                   (real_plus (p2_one_minus p)
                                              (p2_one_minus q)))
                        (real_inv_pos
                           (real_mult pnk_two
                                      (real_plus (p2_one_minus p)
                                                 (p2_one_minus q)))
                           H2b))
                     (real_plus
                        (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1
                                      Hq1)
                        (real_plus (p2_one_minus q)
                                   (real_opp (p2_one_minus p))))
                     real_one).
            -- apply real_eq_refl.
            -- exact (real_inv_pos_correct
                        (real_mult pnk_two
                                   (real_plus (p2_one_minus p)
                                              (p2_one_minus q)))
                        H2b).
          * apply real_mult_one. }
    apply (leb3_le_b_eq_r
             (real_mult (p2_tvsq p q)
                        (real_inv_pos
                           (real_mult pnk_two
                                      (real_plus (p2_one_minus p)
                                                 (p2_one_minus q))) H2b))
             (real_plus
                (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                (real_plus (p2_one_minus q) (real_opp (p2_one_minus p))))
             (real_plus
                (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                (real_plus p (real_opp q)))).
    - apply (leb3_le_b_eq_l
               (real_mult (p2_tvsq (p2_one_minus p) (p2_one_minus q))
                          (real_inv_pos
                             (real_mult pnk_two
                                        (real_plus (p2_one_minus p)
                                                   (p2_one_minus q))) H2b))
               (real_mult (p2_tvsq p q)
                          (real_inv_pos
                             (real_mult pnk_two
                                        (real_plus (p2_one_minus p)
                                                   (p2_one_minus q))) H2b))
               (real_plus
                  (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                  (real_plus (p2_one_minus q) (real_opp (p2_one_minus p))))).
      + apply (RealSetoid.real_eq_mult_compat
                 (p2_tvsq (p2_one_minus p) (p2_one_minus q))
                 (real_inv_pos
                    (real_mult pnk_two
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    H2b)
                 (p2_tvsq p q)
                 (real_inv_pos
                    (real_mult pnk_two
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    H2b)
                 (pnk_tvsq_onem p q)
                 (real_eq_refl
                    (real_inv_pos
                       (real_mult pnk_two
                                  (real_plus (p2_one_minus p)
                                             (p2_one_minus q))) H2b))).
      + exact H2sc.
    - apply (RealSetoid.real_eq_plus_compat
               (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
               (real_plus (p2_one_minus q) (real_opp (p2_one_minus p)))
               (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
               (real_plus p (real_opp q))
               (real_eq_refl (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                          Hp1 Hq1))
               (p2_one_minus_diff q p)). }
  assert (T3 : real_le_b
                 (real_mult (p2_tvsq p q)
                            (real_plus
                               (real_inv_pos
                                  (real_mult pnk_two (real_plus p q)) H2s)
                               (real_inv_pos
                                  (real_mult pnk_two
                                             (real_plus (p2_one_minus p)
                                                        (p2_one_minus q)))
                                  H2b)))
                 (p2_kl2 p q Hp Hq Hp1 Hq1)).
  { apply (real_le_b_trans
             (real_mult (p2_tvsq p q)
                        (real_plus
                           (real_inv_pos
                              (real_mult pnk_two (real_plus p q)) H2s)
                           (real_inv_pos
                              (real_mult pnk_two
                                         (real_plus (p2_one_minus p)
                                                    (p2_one_minus q))) H2b)))
             (real_plus
                (real_mult (p2_tvsq p q)
                           (real_inv_pos
                              (real_mult pnk_two (real_plus p q)) H2s))
                (real_mult (p2_tvsq p q)
                           (real_inv_pos
                              (real_mult pnk_two
                                         (real_plus (p2_one_minus p)
                                                    (p2_one_minus q))) H2b)))
             (p2_kl2 p q Hp Hq Hp1 Hq1)).
    - apply (leb3_le_b_eq_r
               (real_mult (p2_tvsq p q)
                          (real_plus
                             (real_inv_pos
                                (real_mult pnk_two (real_plus p q)) H2s)
                             (real_inv_pos
                                (real_mult pnk_two
                                           (real_plus (p2_one_minus p)
                                                      (p2_one_minus q))) H2b)))
               (real_mult (p2_tvsq p q)
                          (real_plus
                             (real_inv_pos
                                (real_mult pnk_two (real_plus p q)) H2s)
                             (real_inv_pos
                                (real_mult pnk_two
                                           (real_plus (p2_one_minus p)
                                                      (p2_one_minus q))) H2b)))
               (real_plus
                  (real_mult (p2_tvsq p q)
                             (real_inv_pos
                                (real_mult pnk_two (real_plus p q)) H2s))
                  (real_mult (p2_tvsq p q)
                             (real_inv_pos
                                (real_mult pnk_two
                                           (real_plus (p2_one_minus p)
                                                      (p2_one_minus q)))
                                 H2b)))).
      + apply leb3_le_b_refl.
      + exact (real_distrib (p2_tvsq p q)
                 (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                 (real_inv_pos
                    (real_mult pnk_two
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    H2b)).
    - apply (leb3_le_b_eq_r
               (real_plus
                  (real_mult (p2_tvsq p q)
                             (real_inv_pos
                                (real_mult pnk_two (real_plus p q)) H2s))
                  (real_mult (p2_tvsq p q)
                             (real_inv_pos
                                (real_mult pnk_two
                                           (real_plus (p2_one_minus p)
                                                      (p2_one_minus q)))
                                 H2b)))
               (real_plus
                  (real_plus (real_kl_term p q Hp Hq)
                             (real_plus q (real_opp p)))
                  (real_plus
                     (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                     (real_plus p (real_opp q))))
               (p2_kl2 p q Hp Hq Hp1 Hq1)).
      + apply (real_le_b_plus_compat
                 (real_mult (p2_tvsq p q)
                            (real_inv_pos
                               (real_mult pnk_two (real_plus p q)) H2s))
                 (real_plus (real_kl_term p q Hp Hq)
                            (real_plus q (real_opp p)))
                 (real_mult (p2_tvsq p q)
                            (real_inv_pos
                               (real_mult pnk_two
                                          (real_plus (p2_one_minus p)
                                                     (p2_one_minus q))) H2b))
                 (real_plus
                    (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                    (real_plus p (real_opp q)))
                 T1 T2).
      + apply real_eq_of_zero_diff. intro n0.
        cbn [p2_kl2].
        repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
        rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj,
                ?pnk_four_proj.
        ring.
        all: try (exact n0). }
  exact T3.
Qed.

(* ---- 10.2 0.9 档主件：kl₂ ≥ (9/10)·TV² ---- *)

Theorem pnk_pinsker_frac2 : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hne : Or (real_lt p q) (real_lt q p)),
  real_le_b (real_mult pnk_nine_ten (p2_tvsq p q))
            (p2_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hne.
  pose (H2s := real_mult_positive pnk_two (real_plus p q) pnk_two_pos
      (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
         (real_plus p q)
         (real_eq_sym (real_plus real_zero real_zero) real_zero
            (real_plus_zero real_zero))
         (real_lt_plus_compat real_zero p real_zero q Hp Hq))).
  pose (H2b := real_mult_positive pnk_two
      (real_plus (p2_one_minus p) (p2_one_minus q)) pnk_two_pos
      (real_lt_plus_compat real_zero (p2_one_minus p) real_zero
         (p2_one_minus q) Hp1 Hq1)).
  assert (HSUM : real_lt real_zero
                   (real_plus
                      (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                      (real_inv_pos
                         (real_mult pnk_two
                                    (real_plus (p2_one_minus p)
                                               (p2_one_minus q))) H2b)))
    by exact (real_lt_plus_compat real_zero
                (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                real_zero
                (real_inv_pos
                   (real_mult pnk_two
                              (real_plus (p2_one_minus p) (p2_one_minus q)))
                   H2b)
                (real_inv_pos_pos (real_mult pnk_two (real_plus p q)) H2s)
                (real_inv_pos_pos
                   (real_mult pnk_two
                              (real_plus (p2_one_minus p) (p2_one_minus q)))
                   H2b)).
  assert (HPOS : real_lt real_zero (p2_tvsq p q))
    by exact (pnk_tvsq_pos p q Hp Hq Hp1 Hq1 Hne).
  (* E1：(inv B1)·(B1·B2) == B2（assoc + inv_correct + mult_one） *)
  assert (E1 : real_eq
                 (real_mult (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                            (real_mult
                               (real_mult pnk_two (real_plus p q))
                               (real_mult pnk_two
                                          (real_plus (p2_one_minus p)
                                                     (p2_one_minus q)))))
                 (real_mult pnk_two
                            (real_plus (p2_one_minus p) (p2_one_minus q)))).
  { apply (real_eq_trans
             (real_mult
                (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                (real_mult
                   (real_mult pnk_two (real_plus p q))
                   (real_mult pnk_two
                              (real_plus (p2_one_minus p) (p2_one_minus q)))))
             (real_mult
                (real_mult
                   (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                   (real_mult pnk_two (real_plus p q)))
                (real_mult pnk_two
                           (real_plus (p2_one_minus p) (p2_one_minus q))))
             (real_mult pnk_two
                        (real_plus (p2_one_minus p) (p2_one_minus q)))).
    - exact (real_mult_assoc (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
               (real_mult pnk_two (real_plus p q))
               (real_mult pnk_two
                          (real_plus (p2_one_minus p) (p2_one_minus q)))).
    - apply (real_eq_trans
               (real_mult
                  (real_mult
                     (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                     (real_mult pnk_two (real_plus p q)))
                  (real_mult pnk_two
                             (real_plus (p2_one_minus p) (p2_one_minus q))))
               (real_mult real_one
                          (real_mult pnk_two
                                     (real_plus (p2_one_minus p)
                                                (p2_one_minus q))))
               (real_mult pnk_two
                          (real_plus (p2_one_minus p) (p2_one_minus q)))).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult
                    (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                    (real_mult pnk_two (real_plus p q)))
                 (real_mult pnk_two
                            (real_plus (p2_one_minus p) (p2_one_minus q)))
                 real_one
                 (real_mult pnk_two
                            (real_plus (p2_one_minus p) (p2_one_minus q)))).
      * apply (real_eq_trans (real_mult
                                  (real_inv_pos
                                     (real_mult pnk_two (real_plus p q)) H2s)
                                  (real_mult pnk_two (real_plus p q)))
                 (real_mult (real_mult pnk_two (real_plus p q))
                            (real_inv_pos (real_mult pnk_two (real_plus p q))
                                          H2s))
                 real_one
                 (real_mult_comm
                    (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                    (real_mult pnk_two (real_plus p q)))
                 (real_inv_pos_correct (real_mult pnk_two (real_plus p q))
                    H2s)).
      * apply real_eq_refl.
      + apply (real_eq_trans
                 (real_mult real_one
                            (real_mult pnk_two
                                       (real_plus (p2_one_minus p)
                                                  (p2_one_minus q))))
                 (real_mult
                    (real_mult pnk_two
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    real_one)
                 (real_mult pnk_two
                            (real_plus (p2_one_minus p) (p2_one_minus q)))).
      * apply real_mult_comm.
      * apply real_mult_one. }
  (* E2：(inv B2)·(B1·B2) == B1 *)
  assert (E2 : real_eq
                 (real_mult
                    (real_inv_pos
                       (real_mult pnk_two
                                  (real_plus (p2_one_minus p)
                                             (p2_one_minus q))) H2b)
                    (real_mult
                       (real_mult pnk_two (real_plus p q))
                       (real_mult pnk_two
                                  (real_plus (p2_one_minus p)
                                             (p2_one_minus q)))))
                 (real_mult pnk_two (real_plus p q))).
  { apply (real_eq_trans
             (real_mult
                (real_inv_pos
                   (real_mult pnk_two
                              (real_plus (p2_one_minus p) (p2_one_minus q)))
                   H2b)
                (real_mult
                   (real_mult pnk_two (real_plus p q))
                   (real_mult pnk_two
                              (real_plus (p2_one_minus p) (p2_one_minus q)))))
             (real_mult
                (real_mult
                   (real_inv_pos
                      (real_mult pnk_two
                                 (real_plus (p2_one_minus p)
                                            (p2_one_minus q))) H2b)
                   (real_mult pnk_two
                              (real_plus (p2_one_minus p) (p2_one_minus q))))
                (real_mult pnk_two (real_plus p q)))
             (real_mult pnk_two (real_plus p q))).
    - apply real_eq_of_zero_diff. intro n0.
      cbn [p2_diff p2_tvsq p2_one_minus p2_kl2].
      repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
      rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj,
              ?pnk_four_proj.
      ring.
      all: try (exact n0).
    - apply (real_eq_trans
               (real_mult
                  (real_mult
                     (real_inv_pos
                        (real_mult pnk_two
                                   (real_plus (p2_one_minus p)
                                              (p2_one_minus q))) H2b)
                     (real_mult pnk_two
                                (real_plus (p2_one_minus p)
                                           (p2_one_minus q))))
                  (real_mult pnk_two (real_plus p q)))
               (real_mult real_one (real_mult pnk_two (real_plus p q)))
               (real_mult pnk_two (real_plus p q))).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult
                    (real_inv_pos
                       (real_mult pnk_two
                                  (real_plus (p2_one_minus p)
                                             (p2_one_minus q))) H2b)
                    (real_mult pnk_two
                               (real_plus (p2_one_minus p)
                                          (p2_one_minus q))))
                 (real_mult pnk_two (real_plus p q))
                 real_one (real_mult pnk_two (real_plus p q))).
        * apply (real_eq_trans
                   (real_mult
                      (real_inv_pos
                         (real_mult pnk_two
                                    (real_plus (p2_one_minus p)
                                               (p2_one_minus q))) H2b)
                      (real_mult pnk_two
                                 (real_plus (p2_one_minus p)
                                            (p2_one_minus q))))
                   (real_mult
                      (real_mult pnk_two
                                 (real_plus (p2_one_minus p)
                                            (p2_one_minus q)))
                      (real_inv_pos
                         (real_mult pnk_two
                                    (real_plus (p2_one_minus p)
                                               (p2_one_minus q))) H2b))
                   real_one
                   (real_mult_comm
                      (real_inv_pos
                         (real_mult pnk_two
                                    (real_plus (p2_one_minus p)
                                               (p2_one_minus q))) H2b)
                      (real_mult pnk_two
                                 (real_plus (p2_one_minus p)
                                            (p2_one_minus q))))
                   (real_inv_pos_correct
                      (real_mult pnk_two
                                 (real_plus (p2_one_minus p)
                                            (p2_one_minus q)))
                      H2b)).
        * apply real_eq_refl.
      + apply (real_eq_trans
                 (real_mult real_one (real_mult pnk_two (real_plus p q)))
                 (real_mult (real_mult pnk_two (real_plus p q)) real_one)
                 (real_mult pnk_two (real_plus p q))).
        * apply real_mult_comm.
        * apply real_mult_one. }
  (* EB：B2+B1 == 4（环化简） *)
  assert (EB : real_eq
                 (real_plus
                    (real_mult pnk_two
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    (real_mult pnk_two (real_plus p q)))
                 pnk_four).
  { apply real_eq_of_zero_diff. intro n0.
    cbn [p2_diff p2_tvsq p2_one_minus p2_kl2].
    repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
    rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj,
            ?pnk_four_proj.
    ring.
    all: try (exact n0). }
  (* EQE：(i1+i2)·(B1·B2) == 4 *)
  assert (EQE : real_eq
                  (real_mult
                     (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b))
                     (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))))
                  pnk_four).
  { apply (real_eq_trans
             (real_mult (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)) (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))))
             (real_mult (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)))
             pnk_four).
    - apply real_mult_comm.
    - apply (real_eq_trans
               (real_mult (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)))
               (real_plus (real_mult (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)) (real_mult (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)))
               pnk_four).
      + exact (real_distrib (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)).
      + apply (real_eq_trans
                 (real_plus (real_mult (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)) (real_mult (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)))
                 (real_plus (real_mult (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))))) (real_mult (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b) (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))))))
                 pnk_four).
        * apply (RealSetoid.real_eq_plus_compat
                   (real_mult (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s))
                   (real_mult (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b))
                   (real_mult (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))))
                   (real_mult (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b) (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))))
                   (real_mult_comm (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s))
                   (real_mult_comm (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b))).
        * apply (real_eq_trans
                   (real_plus (real_mult (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))))) (real_mult (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b) (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))))))
                   (real_plus (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) (real_mult pnk_two (real_plus p q)))
                   pnk_four).
          -- apply (RealSetoid.real_eq_plus_compat
               (real_mult (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))))
               (real_mult (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b) (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))))
               (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))
               (real_mult pnk_two (real_plus p q))
               E1 E2).
          -- exact EB. }

  (* EQMM：MM == 4·(s·(2−s))（环化简） *)
  assert (EQMM : real_eq
                   (real_mult
                      (real_mult pnk_two (real_plus p q))
                      (real_mult pnk_two
                                 (real_plus (p2_one_minus p)
                                            (p2_one_minus q))))
                   (real_mult pnk_four
                              (real_mult (real_plus p q)
                                         (real_plus (p2_one_minus p)
                                                    (p2_one_minus q))))).
  { apply real_eq_of_zero_diff. intro n0.
    cbn [p2_diff p2_tvsq p2_one_minus p2_kl2].
    repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
    rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj,
            ?pnk_four_proj.
    ring.
    all: try (exact n0). }
  (* RIDENT：4·s(2−s) + (2s−2)² == 4（环恒等式核） *)
  assert (RIDENT : real_eq
                     (real_plus
                        (real_mult pnk_four
                                   (real_mult (real_plus p q)
                                              (real_plus (p2_one_minus p)
                                                         (p2_one_minus q))))
                        (real_mult
                           (real_plus (real_mult pnk_two (real_plus p q))
                                      (real_opp pnk_two))
                           (real_plus (real_mult pnk_two (real_plus p q))
                                      (real_opp pnk_two))))
                     pnk_four).
  { apply real_eq_of_zero_diff. intro n0.
    cbn [p2_diff p2_tvsq p2_one_minus p2_kl2].
    repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
    rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj,
            ?pnk_four_proj.
    ring.
    all: try (exact n0). }
  (* HX4：4·s(2−s) ≤ 4（平方非负+环恒等） *)
  assert (HX4 : real_le_b
                  (real_mult pnk_four
                             (real_mult (real_plus p q)
                                        (real_plus (p2_one_minus p)
                                                   (p2_one_minus q))))
                  pnk_four).
  { apply (leb3_le_b_eq_r
             (real_mult pnk_four
                        (real_mult (real_plus p q)
                                   (real_plus (p2_one_minus p)
                                              (p2_one_minus q))))
             (real_plus
                (real_mult pnk_four
                           (real_mult (real_plus p q)
                                      (real_plus (p2_one_minus p)
                                                 (p2_one_minus q))))
                (real_mult
                   (real_plus (real_mult pnk_two (real_plus p q))
                              (real_opp pnk_two))
                   (real_plus (real_mult pnk_two (real_plus p q))
                              (real_opp pnk_two))))
             pnk_four).
    - apply (leb3_le_b_eq_l
               (real_plus
                  (real_mult pnk_four (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))))
                  real_zero)
               (real_mult pnk_four (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))))
               (real_plus
                  (real_mult pnk_four (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))))
                  (real_mult (real_plus (real_mult pnk_two (real_plus p q)) (real_opp pnk_two)) (real_plus (real_mult pnk_two (real_plus p q)) (real_opp pnk_two))))).
      + apply real_eq_of_zero_diff. intro n0.
        cbn [p2_diff p2_tvsq p2_one_minus p2_kl2].
        repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
        rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj,
                ?pnk_four_proj.
        ring.
        all: try (exact n0).
      + apply (real_le_b_plus_compat
                 (real_mult pnk_four (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))))
                 (real_mult pnk_four (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))))
                 real_zero
                 (real_mult (real_plus (real_mult pnk_two (real_plus p q)) (real_opp pnk_two)) (real_plus (real_mult pnk_two (real_plus p q)) (real_opp pnk_two)))
                 (leb3_le_b_refl (real_mult pnk_four (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q)))))
                 (real_square_nonneg_B (real_plus (real_mult pnk_two (real_plus p q)) (real_opp pnk_two)))).
    - exact RIDENT. }
  (* EQ4M：MM·inv4 == s(2−s) *)
  assert (EQ4M : real_eq
                   (real_mult
                      (real_mult
                         (real_mult pnk_two (real_plus p q))
                         (real_mult pnk_two
                                    (real_plus (p2_one_minus p)
                                               (p2_one_minus q))))
                      (real_inv_pos pnk_four pnk_four_pos))
                   (real_mult (real_plus p q)
                              (real_plus (p2_one_minus p) (p2_one_minus q)))).
  { apply (real_eq_trans
             (real_mult
                (real_mult
                   (real_mult pnk_two (real_plus p q))
                   (real_mult pnk_two
                              (real_plus (p2_one_minus p) (p2_one_minus q))))
                (real_inv_pos pnk_four pnk_four_pos))
             (real_mult
                (real_mult pnk_four
                           (real_mult (real_plus p q)
                                      (real_plus (p2_one_minus p)
                                                 (p2_one_minus q))))
                (real_inv_pos pnk_four pnk_four_pos))
             (real_mult (real_plus p q)
                        (real_plus (p2_one_minus p) (p2_one_minus q)))).
    - exact (RealSetoid.real_eq_mult_compat
               (real_mult
                  (real_mult pnk_two (real_plus p q))
                  (real_mult pnk_two
                             (real_plus (p2_one_minus p) (p2_one_minus q))))
               (real_inv_pos pnk_four pnk_four_pos)
               (real_mult pnk_four
                          (real_mult (real_plus p q)
                                     (real_plus (p2_one_minus p)
                                                (p2_one_minus q))))
               (real_inv_pos pnk_four pnk_four_pos)
               EQMM (real_eq_refl (real_inv_pos pnk_four pnk_four_pos))).
    - apply (real_eq_trans
               (real_mult
                  (real_mult pnk_four
                             (real_mult (real_plus p q)
                                        (real_plus (p2_one_minus p)
                                                   (p2_one_minus q))))
                  (real_inv_pos pnk_four pnk_four_pos))
               (real_mult
                  (real_mult (real_plus p q)
                             (real_plus (p2_one_minus p) (p2_one_minus q)))
                  (real_mult pnk_four (real_inv_pos pnk_four pnk_four_pos)))
               (real_mult (real_plus p q)
                          (real_plus (p2_one_minus p) (p2_one_minus q)))).
      + apply real_eq_of_zero_diff. intro n0.
        cbn [p2_diff p2_tvsq p2_one_minus p2_kl2].
        repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
        rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj,
                ?pnk_four_proj.
        ring.
        all: try (exact n0).
      + apply (real_eq_trans
                 (real_mult
                    (real_mult (real_plus p q)
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    (real_mult pnk_four (real_inv_pos pnk_four pnk_four_pos)))
                 (real_mult
                    (real_mult (real_plus p q)
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    real_one)
                 (real_mult (real_plus p q)
                            (real_plus (p2_one_minus p) (p2_one_minus q)))).
        * apply (RealSetoid.real_eq_mult_compat
                   (real_mult (real_plus p q)
                              (real_plus (p2_one_minus p) (p2_one_minus q)))
                   (real_mult pnk_four (real_inv_pos pnk_four pnk_four_pos))
                   (real_mult (real_plus p q)
                              (real_plus (p2_one_minus p) (p2_one_minus q)))
                   real_one).
        -- apply real_eq_refl.
        -- exact (real_inv_pos_correct pnk_four pnk_four_pos).
        * apply real_mult_one. }
  (* EQ4：1 == s(2−s)·(i1+i2) *)
  assert (EQ4 : real_eq real_one
                  (real_mult (real_mult (real_plus p q)
                                        (real_plus (p2_one_minus p)
                                                   (p2_one_minus q)))
                             (real_plus
                                (real_inv_pos
                                   (real_mult pnk_two (real_plus p q)) H2s)
                                (real_inv_pos
                                   (real_mult pnk_two
                                              (real_plus (p2_one_minus p)
                                                         (p2_one_minus q)))
                                   H2b)))).
  { apply (real_eq_trans real_one (real_mult pnk_four (real_inv_pos pnk_four pnk_four_pos)) (real_mult (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)))).
    - apply real_eq_sym. exact (real_inv_pos_correct pnk_four pnk_four_pos).
    - apply (real_eq_trans (real_mult pnk_four (real_inv_pos pnk_four pnk_four_pos)) (real_mult (real_mult (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)) (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))))) (real_inv_pos pnk_four pnk_four_pos)) (real_mult (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)))).
      + exact (RealSetoid.real_eq_mult_compat pnk_four (real_inv_pos pnk_four pnk_four_pos) (real_mult (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)) (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))))) (real_inv_pos pnk_four pnk_four_pos) (real_eq_sym (real_mult (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)) (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))))) pnk_four EQE) (real_eq_refl (real_inv_pos pnk_four pnk_four_pos))).
      + apply (real_eq_trans (real_mult (real_mult (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)) (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))))) (real_inv_pos pnk_four pnk_four_pos)) (real_mult (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)) (real_mult (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_inv_pos pnk_four pnk_four_pos))) (real_mult (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)))).
        * apply real_eq_sym. apply real_mult_assoc.
        * apply (real_eq_trans (real_mult (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)) (real_mult (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_inv_pos pnk_four pnk_four_pos))) (real_mult (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)) (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_mult (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)))).
          -- exact (RealSetoid.real_eq_mult_compat (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)) (real_mult (real_mult (real_mult pnk_two (real_plus p q)) (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_inv_pos pnk_four pnk_four_pos)) (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)) (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) (real_eq_refl (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b))) EQ4M).
          -- apply real_mult_comm. }  (* HX1：s(2−s) ≤ 1（HX4 缩 inv4） *)
  assert (HX1 : real_le_b (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) real_one).
  { apply (leb3_le_b_eq_r (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) (real_mult pnk_four (real_inv_pos pnk_four pnk_four_pos)) real_one).
    - apply (leb3_le_b_eq_l (real_mult (real_inv_pos pnk_four pnk_four_pos) (real_mult pnk_four (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))))) (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) (real_mult pnk_four (real_inv_pos pnk_four pnk_four_pos))).
      + apply (real_eq_trans (real_mult (real_inv_pos pnk_four pnk_four_pos) (real_mult pnk_four (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q)))))
                 (real_mult (real_mult (real_inv_pos pnk_four pnk_four_pos) pnk_four) (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))))
                 (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q)))).
        * apply real_eq_of_zero_diff. intro n0.
          cbn [p2_diff p2_tvsq p2_one_minus p2_kl2].
          repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
          rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj, ?pnk_three_proj,
                  ?pnk_four_proj.
          ring.
          all: try (exact n0).
        * apply (real_eq_trans
                   (real_mult (real_mult (real_inv_pos pnk_four pnk_four_pos) pnk_four) (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))))
                   (real_mult real_one (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))))
                   (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q)))).
          -- exact (RealSetoid.real_eq_mult_compat (real_mult (real_inv_pos pnk_four pnk_four_pos) pnk_four) (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) real_one (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) (real_eq_trans (real_mult (real_inv_pos pnk_four pnk_four_pos) pnk_four) (real_mult pnk_four (real_inv_pos pnk_four pnk_four_pos)) real_one (real_mult_comm (real_inv_pos pnk_four pnk_four_pos) pnk_four) (real_inv_pos_correct pnk_four pnk_four_pos)) (real_eq_refl (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))))).
          -- apply (real_eq_trans (real_mult real_one (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_mult (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) real_one) (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) (real_mult_comm real_one (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q)))) (real_mult_one (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))))).
      + apply (leb3_le_b_eq_r (real_mult (real_inv_pos pnk_four pnk_four_pos) (real_mult pnk_four (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))))) (real_mult (real_inv_pos pnk_four pnk_four_pos) pnk_four) (real_mult pnk_four (real_inv_pos pnk_four pnk_four_pos))).
        * exact (leb3_le_b_pos_scale_l (real_mult pnk_four (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q)))) pnk_four (real_inv_pos pnk_four pnk_four_pos) HX4 (real_inv_pos_pos pnk_four pnk_four_pos)).
        * apply real_mult_comm.
    - exact (real_inv_pos_correct pnk_four pnk_four_pos). }  (* HTEN：9/10 ≤ i1+i2 *)
  assert (HTEN : real_le_b pnk_nine_ten (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b))).
  { apply (real_le_b_trans pnk_nine_ten real_one (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b))).
    - exact pnk_nine_ten_le_one.
    - apply (leb3_le_b_eq_l (real_mult (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b))) real_one (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b))).
      + exact (real_eq_sym real_one (real_mult (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b))) EQ4).
      + apply (leb3_le_b_eq_r (real_mult (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b))) (real_mult real_one (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b))) (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b))).
        * exact (leb3_le_b_pos_scale (real_mult (real_plus p q) (real_plus (p2_one_minus p) (p2_one_minus q))) real_one (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)) HX1 HSUM).
        * apply (real_eq_trans (real_mult real_one (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b))) (real_mult (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)) real_one) (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)) (real_mult_comm real_one (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b))) (real_mult_one (real_plus (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s) (real_inv_pos (real_mult pnk_two (real_plus (p2_one_minus p) (p2_one_minus q))) H2b)))). }
  (* 闭合：9/10·d² ≤ (i1+i2)·d² == d²·(i1+i2) ≤ kl₂（fracsum） *)
  apply (real_le_b_trans
           (real_mult pnk_nine_ten (p2_tvsq p q))
           (real_mult
              (real_plus
                 (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                 (real_inv_pos
                    (real_mult pnk_two
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    H2b))
              (p2_tvsq p q))
           (p2_kl2 p q Hp Hq Hp1 Hq1)).
  - exact (leb3_le_b_pos_scale pnk_nine_ten
             (real_plus
                (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                (real_inv_pos
                   (real_mult pnk_two
                              (real_plus (p2_one_minus p) (p2_one_minus q)))
                   H2b))
             (p2_tvsq p q) HTEN HPOS).
  - apply (leb3_le_b_eq_l
             (real_mult (p2_tvsq p q)
                        (real_plus
                           (real_inv_pos (real_mult pnk_two (real_plus p q))
                                         H2s)
                           (real_inv_pos
                              (real_mult pnk_two
                                         (real_plus (p2_one_minus p)
                                                    (p2_one_minus q))) H2b)))
             (real_mult
                (real_plus
                   (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                   (real_inv_pos
                      (real_mult pnk_two
                                 (real_plus (p2_one_minus p)
                                            (p2_one_minus q))) H2b))
                (p2_tvsq p q))
             (p2_kl2 p q Hp Hq Hp1 Hq1)).
    + apply real_mult_comm.
    + exact (pnk_kl2_ge_fracsum p q Hp Hq Hp1 Hq1 Hne).
Qed.

(* ---- 文尾假设审计 ---- *)
Print Assumptions pnk_core.
Print Assumptions pnk_gap_global_B.
Print Assumptions pnk_log_mirror_B.
Print Assumptions pnk_tvsq_pos.
Print Assumptions pnk_tvsq_onem.
Print Assumptions pnk_kl2_ge_fracsum.
Print Assumptions pnk_pinsker_frac2.

(*   ① Q 层交替截断族（G1-Q 件）：S1 核多项式参数位 P4 := x−x²/2+x³/3−x⁴/4  *)
(*     「Q 层有限和族基建」的首块。                                   *)
(*   ② 常数 2 键石（G2 键件）：AM-GM 四倍件 4ab ≤_B (a+b)²（平方非负    *)
(*     环恒等 (a+b)² == 4ab+(a−b)² 直连）+ 支内四倍合流主件             *)
(*     装配（A ≥ d²/(2p) ⟕ B ≥ d²/(2(1−q)) 合流 (p+q−1)² ≥ 0）的       *)
(*     秩序件。                                                       *)
(*   系）；对称侧双切线合流族二阶系数 Σλᵢ²>0 恒正，数学上到不了 S2      *)
(*   _tpnska_r8_sanity.py 数值账：S1 25 点/S2 24 点/装配 342 点零违反，  *)
(*   2·TV² ≤ KL 最小余量 0.0033·d²）。常数 2 装配图：                   *)
(*   p>q 支 A := p·g(q/p) ≥ d²/(2p)（S2-核）＋ B := (1−p)·g(Y) ≥        *)
(*   d²/(2(1−q))（pnk_core 于 Y=(1−q)/(1−p)）；合流=本节 pnk_conf4_     *)



(* S1 核偶截断多项式（log(1+x) ≥ P4(x)，x∈[0,1]） *)
Definition pnk_s1_poly (x : Q) : Q :=
  x - x*x*(1#2) + x*x*x*(1#3) - x*x*x*x*(1#4).

(* Qeq ≤ 桥（DTPT_Entropy xq_Qeq_le 同款；Q 等式给非严格序） *)
Lemma pnk_qeq_le : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy] Hxy. unfold Qeq in Hxy; simpl in Hxy.
  unfold Qle; simpl.
  (* Qeq 前件即两侧交叉积的 Z 相等：目标亦为交叉积的 Z 序，            *)
  (* 等式重写后余下的相等序由 Z.le_refl 构造                            *)
  rewrite Hxy.
  apply Z.le_refl.
Qed.

(* 常数正性：0 ≤ 1/5（余项参数位系数） *)
Lemma pnk_qpos_1_5 : Qle 0 (1#5).
Proof.
  unfold Qle, Qnum, Qden; cbn [Qnum Qden].
  (* 目标即 Z 序 0·den(1/5) ≤ 1·den(0)：乘法以 Z.mul_0_l/Z.mul_1_l      *)
  (* 显式归约，余下 0 ≤ 1 由 Z.lt_le_incl 与 1 的正性见证               *)
  (* Pos2Z.is_pos 构造                                                  *)
  rewrite Z.mul_0_l, Z.mul_1_l.
  apply Z.lt_le_incl.
  exact (Pos2Z.is_pos 1%positive).
Qed.

(* 尾增量换形（纯环）：x³/3−x⁴/4 == x³·(4−3x)·(1/12) *)
Lemma pnk_s1_tail2_shape : forall x : Q,
  x*x*x*(1#3) - x*x*x*x*(1#4) == x*x*x*(4 - 3*x)*(1#12).
Proof. intros x. ring. Qed.

(* 偶截断单调尾步件（深度 2 实例）：x³(4−3x)/12 ≥ 0（x∈[0,1]）
   —— P4 ≥ P2 的尾增量非负；证法＝Q 层保号乘法显式链（Qmult_le_0_compat）：
   0 ≤ x ≤ 1 ⟹ x³ ≥ 0 且 4−3x ≥ 4−3 == 1 > 0（乘法保序与反号保序），
   逐级保号收束；深度 m 的同型件同构展开（单跳）。 *)
Lemma pnk_s1_tail2_nonneg : forall x : Q,
  Qle 0 x -> Qle x 1 -> Qle 0 (x*x*x*(4 - 3*x)*(1#12)).
Proof.
  intros x Hx0 Hx1.
  (* ① x³ ≥ 0：非负数乘法保号（Qmult_le_0_compat 两步显式实参） *)
  assert (Hx3 : Qle 0 (x*x*x)).
  { apply (Qmult_le_0_compat (x*x) x).
    - apply (Qmult_le_0_compat x x); exact Hx0.
    - exact Hx0. }
  (* ② 0 ≤ 3 与 3*x ≤ 3：乘法右单调（Qmult_le_compat_r）+ 1*3 == 3 桥 *)
  assert (H0le3 : Qle 0 3).
  { unfold Qle, Qnum, Qden; cbn [Qnum Qden].
    rewrite Z.mul_0_l, Z.mul_1_r.
    apply Z.lt_le_incl. exact (Pos2Z.is_pos 3%positive). }
  assert (H3x : Qle (3*x) 3).
  { apply (Qle_trans (3*x) (x*3) 3).
    - apply pnk_qeq_le. apply Qmult_comm.
    - apply (Qle_trans (x*3) (1*3) 3).
      + apply (Qmult_le_compat_r x 1 3); [exact Hx1 | exact H0le3].
      + apply pnk_qeq_le. apply Qmult_1_l. }
  (* ③ 3*x ≤ 3 ⟹ −3 ≤ −(3*x)（Qopp_le_compat），左加 4 保序：       *)
  (*    0 ≤ 1 == 4 + −3 ≤ 4 + −(3*x)，即 0 ≤ 4 − 3*x。               *)
  assert (HtailP : Qle 0 (4 + (-(3*x)))).
  { apply (Qle_trans 0 (4 + (-3)) (4 + (-(3*x)))).
    - apply (Qle_trans 0 1 (4 + (-3))).
      + exact Qle_0_1.
      + assert (Hz : (4 + (-3) == 1)%Q) by ring.
        apply pnk_qeq_le. exact (Qeq_sym (4 + (-3)) 1 Hz).
    - apply (Qplus_le_compat 4 4 (-3) (-(3*x))).
      + apply Qle_refl.
      + exact (Qopp_le_compat (3*x) 3 H3x). }
  assert (Htail : Qle 0 (4 - 3*x)).
  { apply (Qle_trans 0 (4 + (-(3*x))) (4 - 3*x)).
    - exact HtailP.
    - apply pnk_qeq_le. reflexivity. }
  (* ④ 0 ≤ 1/12：num/den 降 Z 显式构造（0·den(1/12) ≤ 1·den(0)） *)
  assert (Hq12 : Qle 0 (1#12)).
  { unfold Qle, Qnum, Qden; cbn [Qnum Qden].
    rewrite Z.mul_0_l, Z.mul_1_l.
    apply Z.lt_le_incl. exact (Pos2Z.is_pos 1%positive). }
  (* ⑤ 汇合：0 ≤ x³·(4−3x)·(1/12) 由保号乘法两级收束 *)
  apply (Qmult_le_0_compat (x*x*x*(4 - 3*x)) (1#12)).
  - apply (Qmult_le_0_compat (x*x*x) (4 - 3*x)).
    + exact Hx3.
    + exact Htail.
  - exact Hq12.
Qed.

(* 余项参数位非负（深度 3 实例）：x⁵/5 ≥ 0 —— P5 == P4 + x⁵/5 的显式余项
   （S1 陈述：log(1+x) ≥ P4(x) 且 P5−P4 == x⁵/5，Q 层参数位宽恒等）。 *)
Lemma pnk_s1_rem_nonneg : forall x : Q,
  Qle 0 x -> Qle 0 (x*x*x*x*x*(1#5)).
Proof.
  intros x Hx0.
  (* ① x⁴ ≥ 0：非负数乘法保号三级链（Qmult_le_0_compat 显式实参） *)
  assert (Hx4 : Qle 0 (x*x*x*x)).
  { apply (Qmult_le_0_compat (x*x*x) x).
    - apply (Qmult_le_0_compat (x*x) x).
      + apply (Qmult_le_0_compat x x); exact Hx0.
      + exact Hx0.
    - exact Hx0. }
  (* ② 0 ≤ 1/5：num/den 降 Z 显式构造（0·den(1/5) ≤ 1·den(0)） *)
  assert (Hq5 : Qle 0 (1#5)).
  { unfold Qle, Qnum, Qden; cbn [Qnum Qden].
    rewrite Z.mul_0_l, Z.mul_1_l.
    apply Z.lt_le_incl. exact (Pos2Z.is_pos 1%positive). }
  (* ③ 汇合：0 ≤ x⁵·(1/5)，x⁵ == x⁴·x 由保号乘法收束 *)
  apply (Qmult_le_0_compat (x*x*x*x*x) (1#5)).
  - apply (Qmult_le_0_compat (x*x*x*x) x); [exact Hx4 | exact Hx0].
  - exact Hq5.
Qed.


(* 环恒等式：(a+b)² == 4ab + (a−b)² *)
Lemma pnk_sq_split_eq : forall a b : Real,
  real_eq (real_mult (real_plus a b) (real_plus a b))
          (real_plus (real_mult pnk_four (real_mult a b))
                     (real_mult (real_plus a (real_opp b))
                                (real_plus a (real_opp b)))).
Proof.
  intros a b.
  apply real_eq_of_zero_diff. intro n0.
  repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
  rewrite ?pnk_four_proj.
  ring.
  all: try (exact n0).
Qed.

(* AM-GM 四倍件：4ab ≤_B (a+b)²（无前提；链=平方非负 + 环恒等式换形） *)
Lemma pnk_amgm4_B : forall a b : Real,
  real_le_b (real_mult pnk_four (real_mult a b))
            (real_mult (real_plus a b) (real_plus a b)).
Proof.
  intros a b.
  apply (leb3_le_b_eq_r (real_mult pnk_four (real_mult a b))
           (real_plus (real_mult pnk_four (real_mult a b))
                      (real_mult (real_plus a (real_opp b))
                                 (real_plus a (real_opp b))))
           (real_mult (real_plus a b) (real_plus a b))).
  - apply (leb3_le_b_eq_l (real_plus (real_mult pnk_four (real_mult a b)) real_zero)
           (real_mult pnk_four (real_mult a b))
           (real_plus (real_mult pnk_four (real_mult a b))
                      (real_mult (real_plus a (real_opp b))
                                 (real_plus a (real_opp b))))).
    + apply real_plus_zero.
    + apply (real_le_b_plus_compat (real_mult pnk_four (real_mult a b))
               (real_mult pnk_four (real_mult a b)) real_zero
               (real_mult (real_plus a (real_opp b))
                          (real_plus a (real_opp b)))).
      * apply leb3_le_b_refl.
      * apply real_square_nonneg_B.
  - apply real_eq_sym.
    apply pnk_sq_split_eq.
Qed.

(* 支内四倍合流主件（常数 2 键石）：0<q、0<1−p、q ≤_B p ⟹
   4·q·(1−p) ≤_B q+(1−p)。
   链：4q(1−p) ≤_B (q+(1−p))² [amgm4] ≤_B (q+(1−p))·1 [正尺度 pos_scale
   于 q+(1−p) ≤_B 1（q ≤_B p 右加 1−p + 换形 p+(1−p)==1）] == q+(1−p)。 *)
Theorem pnk_conf4_branch : forall p q : Real,
  real_lt real_zero q ->
  real_lt real_zero (p2_one_minus p) ->
  real_le_b q p ->
  real_le_b (real_mult pnk_four (real_mult q (p2_one_minus p)))
            (real_plus q (p2_one_minus p)).
Proof.
  intros p q Hq Hp1 Hqp.
  assert (Hcpos : real_lt real_zero (real_plus q (p2_one_minus p)))
    by (apply (real_lt_plus_compat real_zero q real_zero
                 (p2_one_minus p) Hq Hp1)).
  assert (Hsum : real_le_b (real_plus q (p2_one_minus p)) real_one).
  { apply (leb3_le_b_eq_r (real_plus q (p2_one_minus p))
             (real_plus p (p2_one_minus p)) real_one).
    - apply (real_le_b_plus_compat q p (p2_one_minus p) (p2_one_minus p)).
      + exact Hqp.
      + apply leb3_le_b_refl.
    - apply real_eq_of_zero_diff. intro n0.
      cbn [p2_one_minus].
      repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
      rewrite ?pnk_one_proj, ?pnk_zero_proj.
      ring.
      all: try (exact n0). }
  apply (real_le_b_trans (real_mult pnk_four (real_mult q (p2_one_minus p)))
           (real_mult (real_plus q (p2_one_minus p))
                      (real_plus q (p2_one_minus p)))
           (real_plus q (p2_one_minus p))).
  - apply (pnk_amgm4_B q (p2_one_minus p)).
  - apply (leb3_le_b_eq_r (real_mult (real_plus q (p2_one_minus p))
                                       (real_plus q (p2_one_minus p)))
             (real_mult real_one (real_plus q (p2_one_minus p)))
             (real_plus q (p2_one_minus p))).
    + apply (leb3_le_b_pos_scale (real_plus q (p2_one_minus p)) real_one
               (real_plus q (p2_one_minus p)) Hsum Hcpos).
    + apply real_eq_of_zero_diff. intro n0.
      cbn [p2_one_minus].
      repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
      rewrite ?pnk_one_proj, ?pnk_zero_proj.
      ring.
      all: try (exact n0).
Qed.

Print Assumptions pnk_amgm4_B.
Print Assumptions pnk_conf4_branch.
(*   相位=编译重；纯追加（af_ 冻结纪律，不动上文 35 Qed 任何一行）。    *)
(* 早期三项对照（诚实口径）：*)
(*   第 6 项（G3 阶梯）本节执行闭合：常数 1 档显式主件 pnk2_pinsker_one。 *)
(*     阶梯定位：9/10（pnk_pinsker_frac2）< 1（本节）< 2（待 W3）。    *)
(*     「数值选形」已证结论：在盘引擎（pnk_core 二阶上切线 + fracsum 全局）  *)
(*     的一致可达常数上确界=1（角点 p→1,q→0 处 1/(2p)+1/(2(1−q))→1，   *)
(*     对角线仅到 2 的下确界靠高阶尾残差，属 W3 开放解析环）。          *)
(*   第 5 项（常数 2 完整形 pnk_binary_pinsker2）本窗不落——前置缺口：   *)
(*     W3 全局解析环（Σp·L*_5(u) ≥ 2d²，EXP-D1 报告明示开放项）未闭；   *)
(*     且清单第 5 项所引支内合流式 1/(2p)+1/(2(1−q)) ≥ 2 不成立      *)
(*     （(p,q)=(0.9,0.1) 处实值≈1.11），按红线③显式申报禁硬性拼合。        *)
(*   第 4 项（S1/S2 Real 层本体）本窗不落——exp 桥所需 Real 层级数尾     *)
(*     控制基建（W2 pnk_qsum 族+几何尾）未在盘；工作量自估 ≥1 个工作段。 *)
(*   跨件组合使用：本节主件使用 pnk_kl2_ge_fracsum（本件）+             *)
(*     p2_kl2/p2_tvsq（PinskerTwoPoint）+ UpRealLeB3 序代数族；         *)
(*     cec_trunc_sup（UpReqEngineCeiling）为 Q 层常数算术层（天花板    *)
(*     常数 c*(k)=2 的 k≥5 段），与 KL 语义的桥接件（kl₂ ≥ c*(k)·TV²） *)
(*     即 W3 依赖的 pnk_pinsker_trunc5，未在盘，遗留如实登记。          *)
(* 新增件：pnk2_half（1/2 常数）；pnk2_half_mult_two / pnk2_half_expand *)
(*   / pnk2_si_half（inv 焊接三件）；pnk2_sprod_le_one（s(2−s) ≤ 1，    *)
(*   平方恒等直证，替代 frac2 的 EQ4/inv4 长链，无前提）；              *)
(*   pnk2_pinsker_one（阶梯主件：1·TV² ≤ kl₂；链=fracsum +              *)
(*   s(2−s)≤1 + HTEN 同构 pos_scale 闭合）。                            *)
(* 红线自审：纯构造性；公理面预期全 Closed；语句面 Set 纪律沿 frac2     *)
(*   （无 Prop 前提泄漏）；非平凡性=真装配定理（使用 fracsum 非重述）。 *)


Definition pnk2_half : Real :=
  real_mult pnk_two (real_inv_pos pnk_four pnk_four_pos).

(* 1/2 · 2 == 1 *)
Lemma pnk2_half_mult_two : real_eq (real_mult pnk2_half pnk_two) real_one.
Proof.
  apply (real_eq_trans
           (real_mult pnk2_half pnk_two)
           (real_mult (real_mult pnk_two pnk_two)
                      (real_inv_pos pnk_four pnk_four_pos))
           real_one).
  - apply (real_eq_trans
             (real_mult pnk2_half pnk_two)
             (real_mult pnk_two
                        (real_mult (real_inv_pos pnk_four pnk_four_pos) pnk_two))
             (real_mult (real_mult pnk_two pnk_two)
                        (real_inv_pos pnk_four pnk_four_pos))).
    + apply (real_eq_trans
               (real_mult pnk2_half pnk_two)
               (real_mult (real_mult pnk_two (real_inv_pos pnk_four pnk_four_pos))
                          pnk_two)
               (real_mult pnk_two
                          (real_mult (real_inv_pos pnk_four pnk_four_pos) pnk_two))).
      * exact (real_eq_refl
                 (real_mult (real_mult pnk_two (real_inv_pos pnk_four pnk_four_pos))
                            pnk_two)).
      * apply real_eq_sym. apply real_mult_assoc.
    + apply (real_eq_trans
               (real_mult pnk_two
                          (real_mult (real_inv_pos pnk_four pnk_four_pos) pnk_two))
               (real_mult pnk_two
                          (real_mult pnk_two (real_inv_pos pnk_four pnk_four_pos)))
               (real_mult (real_mult pnk_two pnk_two)
                          (real_inv_pos pnk_four pnk_four_pos))).
      * apply (RealSetoid.real_eq_mult_compat pnk_two
                 (real_mult (real_inv_pos pnk_four pnk_four_pos) pnk_two)
                 pnk_two
                 (real_mult pnk_two (real_inv_pos pnk_four pnk_four_pos))).
        -- apply real_eq_refl.
        -- apply real_mult_comm.
      * apply real_mult_assoc.
  - exact (real_inv_pos_correct pnk_four pnk_four_pos).
Qed.

(* 左展开形：x == 1/2·(2·x)（供 inv 焊接） *)
Lemma pnk2_half_expand : forall x : Real,
  real_eq x (real_mult pnk2_half (real_mult pnk_two x)).
Proof.
  intro x.
  apply (real_eq_trans x (real_mult real_one x)
           (real_mult pnk2_half (real_mult pnk_two x))).
  - apply (real_eq_trans x (real_mult x real_one) (real_mult real_one x)).
    + apply real_eq_sym. apply real_mult_one.
    + apply real_mult_comm.
  - apply (real_eq_trans (real_mult real_one x)
             (real_mult (real_mult pnk2_half pnk_two) x)
             (real_mult pnk2_half (real_mult pnk_two x))).
    + apply (RealSetoid.real_eq_mult_compat real_one x
               (real_mult pnk2_half pnk_two) x).
      * exact (real_eq_sym (real_mult pnk2_half pnk_two) real_one
                 pnk2_half_mult_two).
      * apply real_eq_refl.
    + apply real_eq_sym. apply real_mult_assoc.
Qed.

(* inv 焊接件：s·inv(2s) == 1/2（近支/远支共用） *)
Lemma pnk2_si_half : forall (s : Real)
  (H2s : real_lt real_zero (real_mult pnk_two s)),
  real_eq (real_mult s (real_inv_pos (real_mult pnk_two s) H2s)) pnk2_half.
Proof.
  intros s H2s.
  apply (real_eq_trans
           (real_mult s (real_inv_pos (real_mult pnk_two s) H2s))
           (real_mult pnk2_half
                      (real_mult pnk_two
                                 (real_mult s
                                            (real_inv_pos
                                               (real_mult pnk_two s) H2s))))
           pnk2_half).
  - apply pnk2_half_expand.
  - apply (real_eq_trans
             (real_mult pnk2_half
                        (real_mult pnk_two
                                   (real_mult s
                                              (real_inv_pos
                                                 (real_mult pnk_two s) H2s))))
             (real_mult pnk2_half real_one)
             pnk2_half).
    + apply (RealSetoid.real_eq_mult_compat pnk2_half
               (real_mult pnk_two
                          (real_mult s
                                     (real_inv_pos (real_mult pnk_two s) H2s)))
               pnk2_half real_one).
      * apply real_eq_refl.
      * apply (real_eq_trans
                 (real_mult pnk_two (real_mult s (real_inv_pos (real_mult pnk_two s) H2s)))
                 (real_mult (real_mult pnk_two s)
                            (real_inv_pos (real_mult pnk_two s) H2s))
                 real_one).
        -- apply real_mult_assoc.
        -- exact (real_inv_pos_correct (real_mult pnk_two s) H2s).
    + apply real_mult_one.
Qed.


Lemma pnk2_sprod_le_one : forall p q : Real,
  real_le_b (real_mult (real_plus p q)
                       (real_plus (p2_one_minus p) (p2_one_minus q)))
            real_one.
Proof.
  intros p q.
  apply (leb3_le_b_eq_r
           (real_mult (real_plus p q)
                      (real_plus (p2_one_minus p) (p2_one_minus q)))
           (real_plus
              (real_mult (real_plus p q)
                         (real_plus (p2_one_minus p) (p2_one_minus q)))
              (real_mult (real_plus (real_plus p q) (real_opp real_one))
                         (real_plus (real_plus p q) (real_opp real_one))))
           real_one).
  - apply (leb3_le_b_eq_l
             (real_plus
                (real_mult (real_plus p q)
                           (real_plus (p2_one_minus p) (p2_one_minus q)))
                real_zero)
             (real_mult (real_plus p q)
                        (real_plus (p2_one_minus p) (p2_one_minus q)))
             (real_plus
                (real_mult (real_plus p q)
                           (real_plus (p2_one_minus p) (p2_one_minus q)))
                (real_mult (real_plus (real_plus p q) (real_opp real_one))
                           (real_plus (real_plus p q) (real_opp real_one))))).
    + apply real_plus_zero.
    + apply (real_le_b_plus_compat
               (real_mult (real_plus p q)
                          (real_plus (p2_one_minus p) (p2_one_minus q)))
               (real_mult (real_plus p q)
                          (real_plus (p2_one_minus p) (p2_one_minus q)))
               real_zero
               (real_mult (real_plus (real_plus p q) (real_opp real_one))
                          (real_plus (real_plus p q) (real_opp real_one)))).
      * apply leb3_le_b_refl.
      * apply real_square_nonneg_B.
  - apply real_eq_sym.
    apply real_eq_of_zero_diff. intro n0.
    cbn [p2_one_minus].
    repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
    rewrite ?pnk_one_proj, ?pnk_zero_proj.
    ring.
    all: try (exact n0).
Qed.


Theorem pnk2_pinsker_one : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hne : Or (real_lt p q) (real_lt q p)),
  real_le_b (real_mult real_one (p2_tvsq p q))
            (p2_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hne.
  pose (H2s := real_mult_positive pnk_two (real_plus p q) pnk_two_pos
      (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
         (real_plus p q)
         (real_eq_sym (real_plus real_zero real_zero) real_zero
            (real_plus_zero real_zero))
         (real_lt_plus_compat real_zero p real_zero q Hp Hq))).
  pose (H2b := real_mult_positive pnk_two
      (real_plus (p2_one_minus p) (p2_one_minus q)) pnk_two_pos
      (real_lt_plus_compat real_zero (p2_one_minus p) real_zero
         (p2_one_minus q) Hp1 Hq1)).
  assert (HSUM : real_lt real_zero
                   (real_plus
                      (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                      (real_inv_pos
                         (real_mult pnk_two
                                    (real_plus (p2_one_minus p)
                                               (p2_one_minus q))) H2b)))
    by exact (real_lt_plus_compat real_zero
                (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                real_zero
                (real_inv_pos
                   (real_mult pnk_two
                              (real_plus (p2_one_minus p) (p2_one_minus q)))
                   H2b)
                (real_inv_pos_pos (real_mult pnk_two (real_plus p q)) H2s)
                (real_inv_pos_pos
                   (real_mult pnk_two
                              (real_plus (p2_one_minus p) (p2_one_minus q)))
                   H2b)).
  assert (HPOS : real_lt real_zero (p2_tvsq p q))
    by exact (pnk_tvsq_pos p q Hp Hq Hp1 Hq1 Hne).
  (* 支内乘积恒等：s·(2−s)·(i1+i2) == 1 的两个组成恒等式 *)
  assert (W1 : real_eq
                 (real_mult
                    (real_mult (real_plus p q)
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s))
                 (real_mult (real_plus (p2_one_minus p) (p2_one_minus q))
                            pnk2_half)).
  { apply (real_eq_trans
             (real_mult
                (real_mult (real_plus p q)
                           (real_plus (p2_one_minus p) (p2_one_minus q)))
                (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s))
             (real_mult (real_plus (p2_one_minus p) (p2_one_minus q))
                        (real_mult
                           (real_plus p q)
                           (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)))
             (real_mult (real_plus (p2_one_minus p) (p2_one_minus q))
                        pnk2_half)).
    - apply (real_eq_trans
               (real_mult
                  (real_mult (real_plus p q)
                             (real_plus (p2_one_minus p) (p2_one_minus q)))
                  (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s))
               (real_mult
                  (real_mult (real_plus (p2_one_minus p) (p2_one_minus q))
                             (real_plus p q))
                  (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s))
               (real_mult (real_plus (p2_one_minus p) (p2_one_minus q))
                          (real_mult
                             (real_plus p q)
                             (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)))).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_plus p q)
                            (real_plus (p2_one_minus p) (p2_one_minus q)))
                 (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                 (real_mult (real_plus (p2_one_minus p) (p2_one_minus q))
                            (real_plus p q))
                 (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)).
        * apply real_mult_comm.
        * apply real_eq_refl.
      + apply real_eq_sym. apply real_mult_assoc.
    - apply (RealSetoid.real_eq_mult_compat
               (real_plus (p2_one_minus p) (p2_one_minus q))
               (real_mult
                  (real_plus p q)
                  (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s))
               (real_plus (p2_one_minus p) (p2_one_minus q))
               pnk2_half).
      + apply real_eq_refl.
      + apply pnk2_si_half. }
  assert (W2 : real_eq
                 (real_mult
                    (real_mult (real_plus p q)
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    (real_inv_pos
                       (real_mult pnk_two
                                  (real_plus (p2_one_minus p)
                                             (p2_one_minus q))) H2b))
                 (real_mult (real_plus p q) pnk2_half)).
  { apply (real_eq_trans
             (real_mult
                (real_mult (real_plus p q)
                           (real_plus (p2_one_minus p) (p2_one_minus q)))
                (real_inv_pos
                   (real_mult pnk_two
                              (real_plus (p2_one_minus p)
                                         (p2_one_minus q))) H2b))
             (real_mult (real_plus p q)
                        (real_mult
                           (real_plus (p2_one_minus p) (p2_one_minus q))
                           (real_inv_pos
                              (real_mult pnk_two
                                         (real_plus (p2_one_minus p)
                                                    (p2_one_minus q))) H2b)))
             (real_mult (real_plus p q) pnk2_half)).
    - apply real_eq_sym. apply real_mult_assoc.
    - apply (RealSetoid.real_eq_mult_compat
               (real_plus p q)
               (real_mult
                  (real_plus (p2_one_minus p) (p2_one_minus q))
                  (real_inv_pos
                     (real_mult pnk_two
                                (real_plus (p2_one_minus p)
                                           (p2_one_minus q))) H2b))
               (real_plus p q)
               pnk2_half).
      + apply real_eq_refl.
      + apply pnk2_si_half. }
  (* t+s == 2（点级环恒等） *)
  assert (TS : real_eq
                 (real_plus (real_plus (p2_one_minus p) (p2_one_minus q))
                            (real_plus p q))
                 pnk_two).
  { apply real_eq_of_zero_diff. intro n0.
    cbn [p2_one_minus].
    repeat (setoid_rewrite real_mult_proj || setoid_rewrite real_plus_proj || setoid_rewrite real_opp_proj).
    rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj.
    ring.
    all: try (exact n0). }
  (* EQ4O：1 == s(2−s)·(i1+i2)（frac2 EQ4 的平方直证替代形） *)
  assert (EQ4O : real_eq real_one
                  (real_mult
                     (real_mult (real_plus p q)
                                (real_plus (p2_one_minus p) (p2_one_minus q)))
                     (real_plus
                        (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                        (real_inv_pos
                           (real_mult pnk_two
                                      (real_plus (p2_one_minus p)
                                                 (p2_one_minus q))) H2b)))).
  { apply real_eq_sym.
    apply (real_eq_trans
             (real_mult
                (real_mult (real_plus p q)
                           (real_plus (p2_one_minus p) (p2_one_minus q)))
                (real_plus
                   (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                   (real_inv_pos
                      (real_mult pnk_two
                                 (real_plus (p2_one_minus p)
                                            (p2_one_minus q))) H2b)))
             (real_plus
                (real_mult
                   (real_mult (real_plus p q)
                              (real_plus (p2_one_minus p) (p2_one_minus q)))
                   (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s))
                (real_mult
                   (real_mult (real_plus p q)
                              (real_plus (p2_one_minus p) (p2_one_minus q)))
                   (real_inv_pos
                      (real_mult pnk_two
                                 (real_plus (p2_one_minus p)
                                            (p2_one_minus q))) H2b)))
             real_one).
    - apply real_distrib.
    - apply (real_eq_trans
               (real_plus
                  (real_mult
                     (real_mult (real_plus p q)
                                (real_plus (p2_one_minus p) (p2_one_minus q)))
                     (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s))
                  (real_mult
                     (real_mult (real_plus p q)
                                (real_plus (p2_one_minus p) (p2_one_minus q)))
                     (real_inv_pos
                        (real_mult pnk_two
                                   (real_plus (p2_one_minus p)
                                              (p2_one_minus q))) H2b)))
               (real_plus
                  (real_mult (real_plus (p2_one_minus p) (p2_one_minus q))
                             pnk2_half)
                  (real_mult (real_plus p q) pnk2_half))
               real_one).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_mult
                    (real_mult (real_plus p q)
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s))
                 (real_mult
                    (real_mult (real_plus p q)
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    (real_inv_pos
                       (real_mult pnk_two
                                  (real_plus (p2_one_minus p)
                                             (p2_one_minus q))) H2b))
                 (real_mult (real_plus (p2_one_minus p) (p2_one_minus q))
                            pnk2_half)
                 (real_mult (real_plus p q) pnk2_half)
                 W1 W2).
      + apply (real_eq_trans
                 (real_plus
                    (real_mult (real_plus (p2_one_minus p) (p2_one_minus q))
                               pnk2_half)
                    (real_mult (real_plus p q) pnk2_half))
                 (real_plus
                    (real_mult pnk2_half (real_plus (p2_one_minus p) (p2_one_minus q)))
                    (real_mult pnk2_half (real_plus p q)))
                 real_one).
        * apply (RealSetoid.real_eq_plus_compat
                   (real_mult (real_plus (p2_one_minus p) (p2_one_minus q))
                              pnk2_half)
                   (real_mult (real_plus p q) pnk2_half)
                   (real_mult pnk2_half (real_plus (p2_one_minus p) (p2_one_minus q)))
                   (real_mult pnk2_half (real_plus p q))
                   (real_mult_comm (real_plus (p2_one_minus p) (p2_one_minus q)) pnk2_half)
                   (real_mult_comm (real_plus p q) pnk2_half)).
        * apply (real_eq_trans
                   (real_plus
                      (real_mult pnk2_half (real_plus (p2_one_minus p) (p2_one_minus q)))
                      (real_mult pnk2_half (real_plus p q)))
                   (real_mult pnk2_half
                              (real_plus (real_plus (p2_one_minus p) (p2_one_minus q))
                                         (real_plus p q)))
                   real_one).
          -- apply real_eq_sym. apply real_distrib.
          -- apply (real_eq_trans
                       (real_mult pnk2_half
                                  (real_plus (real_plus (p2_one_minus p) (p2_one_minus q))
                                             (real_plus p q)))
                       (real_mult pnk2_half pnk_two)
                       real_one).
            ++ apply (RealSetoid.real_eq_mult_compat pnk2_half
                        (real_plus (real_plus (p2_one_minus p) (p2_one_minus q))
                                   (real_plus p q))
                        pnk2_half pnk_two
                        (real_eq_refl pnk2_half) TS).
            ++ apply pnk2_half_mult_two. }
  (* HTEN1：1 ≤ i1+i2（HX1 缩 + EQ4O） *)
  assert (HONE : real_le_b real_one
                  (real_plus
                     (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                     (real_inv_pos
                        (real_mult pnk_two
                                   (real_plus (p2_one_minus p)
                                              (p2_one_minus q))) H2b))).
  { apply (leb3_le_b_eq_l
             (real_mult
                (real_mult (real_plus p q)
                           (real_plus (p2_one_minus p) (p2_one_minus q)))
                (real_plus
                   (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                   (real_inv_pos
                      (real_mult pnk_two
                                 (real_plus (p2_one_minus p)
                                            (p2_one_minus q))) H2b)))
             real_one
             (real_plus
                (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                (real_inv_pos
                   (real_mult pnk_two
                              (real_plus (p2_one_minus p)
                                         (p2_one_minus q))) H2b))).
    - exact (real_eq_sym real_one
               (real_mult
                  (real_mult (real_plus p q)
                             (real_plus (p2_one_minus p) (p2_one_minus q)))
                  (real_plus
                     (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                     (real_inv_pos
                        (real_mult pnk_two
                                   (real_plus (p2_one_minus p)
                                              (p2_one_minus q))) H2b)))
               EQ4O).
    - apply (leb3_le_b_eq_r
               (real_mult
                  (real_mult (real_plus p q)
                             (real_plus (p2_one_minus p) (p2_one_minus q)))
                  (real_plus
                     (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                     (real_inv_pos
                        (real_mult pnk_two
                                   (real_plus (p2_one_minus p)
                                              (p2_one_minus q))) H2b)))
               (real_mult real_one
                  (real_plus
                     (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                     (real_inv_pos
                        (real_mult pnk_two
                                   (real_plus (p2_one_minus p)
                                              (p2_one_minus q))) H2b)))
               (real_plus
                  (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                  (real_inv_pos
                     (real_mult pnk_two
                                (real_plus (p2_one_minus p)
                                           (p2_one_minus q))) H2b))).
      + exact (leb3_le_b_pos_scale
                 (real_mult (real_plus p q)
                            (real_plus (p2_one_minus p) (p2_one_minus q)))
                 real_one
                 (real_plus
                    (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                    (real_inv_pos
                       (real_mult pnk_two
                                  (real_plus (p2_one_minus p)
                                             (p2_one_minus q))) H2b))
                 (pnk2_sprod_le_one p q) HSUM).
      + apply (real_eq_trans
                 (real_mult real_one
                    (real_plus
                       (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                       (real_inv_pos
                          (real_mult pnk_two
                                     (real_plus (p2_one_minus p)
                                                (p2_one_minus q))) H2b)))
                 (real_mult
                    (real_plus
                       (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                       (real_inv_pos
                          (real_mult pnk_two
                                     (real_plus (p2_one_minus p)
                                                (p2_one_minus q))) H2b))
                    real_one)
                 (real_plus
                    (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                    (real_inv_pos
                       (real_mult pnk_two
                                  (real_plus (p2_one_minus p)
                                             (p2_one_minus q))) H2b))).
        * apply real_mult_comm.
        * apply real_mult_one. }
  (* 闭合：1·d² ≤ (i1+i2)·d² == d²·(i1+i2) ≤ kl₂（fracsum） *)
  apply (real_le_b_trans
           (real_mult real_one (p2_tvsq p q))
           (real_mult
              (real_plus
                 (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                 (real_inv_pos
                    (real_mult pnk_two
                               (real_plus (p2_one_minus p) (p2_one_minus q)))
                    H2b))
              (p2_tvsq p q))
           (p2_kl2 p q Hp Hq Hp1 Hq1)).
  - exact (leb3_le_b_pos_scale real_one
             (real_plus
                (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                (real_inv_pos
                   (real_mult pnk_two
                              (real_plus (p2_one_minus p) (p2_one_minus q)))
                   H2b))
             (p2_tvsq p q) HONE HPOS).
  - apply (leb3_le_b_eq_l
             (real_mult (p2_tvsq p q)
                        (real_plus
                           (real_inv_pos (real_mult pnk_two (real_plus p q))
                                         H2s)
                           (real_inv_pos
                              (real_mult pnk_two
                                         (real_plus (p2_one_minus p)
                                                    (p2_one_minus q))) H2b)))
             (real_mult
                (real_plus
                   (real_inv_pos (real_mult pnk_two (real_plus p q)) H2s)
                   (real_inv_pos
                      (real_mult pnk_two
                                 (real_plus (p2_one_minus p)
                                            (p2_one_minus q))) H2b))
                (p2_tvsq p q))
             (p2_kl2 p q Hp Hq Hp1 Hq1)).
    + apply real_mult_comm.
    + exact (pnk_kl2_ge_fracsum p q Hp Hq Hp1 Hq1 Hne).
Qed.

Print Assumptions pnk2_sprod_le_one.
Print Assumptions pnk2_pinsker_one.

(* PNK2B 块（纯追加）—— Pinsker 常数 2 桥接件层      *)
(* 使命：头注「已知边界」测绘的常数 2 装配路径之支内二阶砖。            *)
(*   数值已证结论（400² 网格，_tpnk2b_交付报告 §反例见证）：                    *)
(*   ① 近支砖 q<p：d² ≤ 2p·KL₂ 全域零违反——pnk2_pinsker_trunc5；        *)
(*   ② 对称件 p<q：d² ≤ 2(1−p)·KL₂ 全域零违反——mirror（经二点 KL       *)
(*      原子反射恒等式 p2_kl2(1−p,1−q)==p2_kl2(p,q) 归约到①）；          *)
(*   ③ 测绘路径的远支砖 2(1−p)·gap₂ ≥ d² 网格 79,401 处违反             *)
(*      （(0.7,0.2) 处 0.2058<0.4167）——字面合流式算术不成立；          *)
(*   ④ 即便配齐理想 harmonic 远支引擎，合流系数 (1/2)(1/p+1/(1−q))      *)
(*      全域 inf≈1.0025（角点）——逐点 log 不等式装配的一致天花板=1：     *)
(*      常数 2 需 Bregman/插值层（D″(s)=1/s+1/(1−s)≥4 即 (1−2s)²≥0，     *)
(*      积分式 KL₂=∫(p−s)D″(s)ds≥2d²——头注「逐点近似三分基建」缺位）。  *)
(*   故 2·TV² 完整形终装按红线③申报受阻（精确伤单见交付报告）；本块     *)
(*   交付装配路径中真实可达的两块支内砖（终装合流的直接前件）。         *)
(* 装配（①）：w2t_trunc5_bridge（y+y²/2 ≤_B −log(1−y)，y:=d·inv p）      *)
(*   + klst_gap_shape（kl₁+(q−p) == p·(x−1−log x)，x:=q·inv p）          *)
(*   + 换形 x−1−log x == −y−log(1−y)（pnk2_one_minus_scale+real_log_wd） *)
(*   ⟹ p·(y²/2) ≤_B gap₁；                                              *)
(*   + klst_gibbs_core_strict 于 (1−p,1−q)（(1−p)<(1−q) 支）⟹ gap₂>0     *)
(*   ⟹ gap₁ ≤_B kl₂ ⟹ p·(y²/2) ≤_B kl₂；                                *)
(*   + 尺度闭合 eq d·d == 2p·(p·(y²/2))（real_inv_pos_correct 焊接）     *)
(*   ⟹ d² ≤_B 2p·KL₂。                                                  *)
(* 红线自审：结论全 real_le_b 全称 Bishop 形（对全体正性证书点成立）；   *)
(*   前提全显式证书（real_lt/real_le Set 面，零 Prop 泄露）；公理面      *)
(*   预期全 Closed；纯追加不改既有行。                                   *)


(* ---- PNK2B.1 点级环消解与代数小件 ---- *)

Ltac pnk2_ring_eq :=
  apply real_eq_of_zero_diff; intro n0;
  unfold p2_kl2, p2_tvsq, p2_diff, p2_one_minus;
  repeat (setoid_rewrite real_plus_proj || setoid_rewrite real_mult_proj
          || setoid_rewrite real_opp_proj);
  rewrite ?pnk_one_proj, ?pnk_zero_proj, ?pnk_two_proj;
  ring.

(* (p−q)+q == p 与 q+(p−q) == p（点级环） *)
Lemma pnk2_diff_plus_r : forall p q : Real,
  real_eq (real_plus (p2_diff p q) q) p.
Proof. intros p q. pnk2_ring_eq. Qed.

Lemma pnk2_diff_plus_l : forall p q : Real,
  real_eq (real_plus q (p2_diff p q)) p.
Proof. intros p q. pnk2_ring_eq. Qed.

(* 1·z == z（点级环） *)
Lemma pnk2_mult_one_l : forall z : Real, real_eq (real_mult real_one z) z.
Proof. intros z. pnk2_ring_eq. Qed.

(* inv·y 消去：(inv y)·(y·z) == z *)
Lemma pnk2_cancel_mul : forall (y z : Real) (Hy : real_lt real_zero y),
  real_eq (real_mult (real_inv_pos y Hy) (real_mult y z)) z.
Proof.
  intros y z Hy.
  apply (real_eq_trans
           (real_mult (real_inv_pos y Hy) (real_mult y z))
           (real_mult (real_mult y (real_inv_pos y Hy)) z)
           z).
  - apply (real_eq_trans
             (real_mult (real_inv_pos y Hy) (real_mult y z))
             (real_mult (real_mult (real_inv_pos y Hy) y) z)
             (real_mult (real_mult y (real_inv_pos y Hy)) z)).
    + apply real_mult_assoc.
    + apply (RealSetoid.real_eq_mult_compat (real_mult (real_inv_pos y Hy) y) z
               (real_mult y (real_inv_pos y Hy)) z
               (real_mult_comm (real_inv_pos y Hy) y) (real_eq_refl z)).
  - apply (real_eq_trans
             (real_mult (real_mult y (real_inv_pos y Hy)) z)
             (real_mult real_one z)
             z).
    + apply (RealSetoid.real_eq_mult_compat (real_mult y (real_inv_pos y Hy)) z
               real_one z (real_inv_pos_correct y Hy) (real_eq_refl z)).
    + apply pnk2_mult_one_l.
Qed.

(* inv 对 real_eq 的兼容 *)
Lemma pnk2_inv_wd : forall (x y : Real) (Hx : real_lt real_zero x) (Hy : real_lt real_zero y),
  real_eq x y -> real_eq (real_inv_pos x Hx) (real_inv_pos y Hy).
Proof.
  intros x y Hx Hy Hxy.
  assert (H1 : real_eq (real_mult y (real_inv_pos x Hx))
                       (real_mult x (real_inv_pos x Hx)))
    by exact (RealSetoid.real_eq_mult_compat y (real_inv_pos x Hx) x (real_inv_pos x Hx)
          (real_eq_sym x y Hxy) (real_eq_refl (real_inv_pos x Hx))).
  assert (H2 : real_eq (real_mult y (real_inv_pos x Hx)) real_one)
    by exact (real_eq_trans _ _ _ H1 (real_inv_pos_correct x Hx)).
  apply (real_eq_trans (real_inv_pos x Hx)
           (real_mult (real_inv_pos y Hy) (real_mult y (real_inv_pos x Hx)))
           (real_inv_pos y Hy)).
  - exact (real_eq_sym _ _ (pnk2_cancel_mul y (real_inv_pos x Hx) Hy)).
  - apply (real_eq_trans
             (real_mult (real_inv_pos y Hy) (real_mult y (real_inv_pos x Hx)))
             (real_mult (real_inv_pos y Hy) real_one)
             (real_inv_pos y Hy)).
    + apply (RealSetoid.real_eq_mult_compat (real_inv_pos y Hy)
               (real_mult y (real_inv_pos x Hx))
               (real_inv_pos y Hy) real_one
               (real_eq_refl (real_inv_pos y Hy)) H2).
    + apply real_mult_one.
Qed.

(* −(a·b) == (−a)·b（点级环；库内 real_opp_mult 参序未测绘，自建） *)
Lemma pnk2_opp_mult : forall a b : Real,
  real_eq (real_opp (real_mult a b)) (real_mult (real_opp a) b).
Proof.
  intros a b. pnk2_ring_eq.
Qed.


(* 同因子分配归并：(u·w)+(v·w) == (u+v)·w *)
Lemma pnk2_distrib_join : forall u v w : Real,
  real_eq (real_plus (real_mult u w) (real_mult v w))
          (real_mult (real_plus u v) w).
Proof.
  intros u v w.
  apply (real_eq_trans
           (real_plus (real_mult u w) (real_mult v w))
           (real_plus (real_mult w u) (real_mult w v))
           (real_mult (real_plus u v) w)).
  - apply (RealSetoid.real_eq_plus_compat (real_mult u w) (real_mult v w)
             (real_mult w u) (real_mult w v)
             (real_mult_comm u w) (real_mult_comm v w)).
  - apply (real_eq_trans
             (real_plus (real_mult w u) (real_mult w v))
             (real_mult w (real_plus u v))
             (real_mult (real_plus u v) w)).
    + apply real_eq_sym. apply real_distrib.
    + apply real_mult_comm.
Qed.


(* 2·(1/2) == 1（w2t_c_half 常数面，供尺度闭合） *)
Lemma pnk2_c2_one : real_eq (real_mult pnk_two w2t_c_half) real_one.
Proof.
  apply real_eq_of_zero_diff. intro n0.
  repeat (setoid_rewrite real_mult_proj).
  rewrite (pnk_two_proj n0), (pnk_one_proj n0).
  assert (Hc : projT1 w2t_c_half n0 == (1#2)%Q) by (apply real_const_proj).
  rewrite Hc. ring.
Qed.


(* projT1 环恒等：(2·p)·s == 2·(p·s)（s 为任意 Real 原子） *)
Lemma pnk2_ring_eq_lscale : forall (p s : Real),
  real_eq (real_mult (real_mult pnk_two p) s)
          (real_mult pnk_two (real_mult p s)).
Proof.
  intros p s. pnk2_ring_eq.
Qed.


(* inv 焊接内层恒等式：p·(d·inv p) == d *)
Lemma pnk2_mult_inv_scale : forall (p d : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult p (real_mult d (real_inv_pos p Hp))) d.
Proof.
  intros p d Hp.
  apply (real_eq_trans
           (real_mult p (real_mult d (real_inv_pos p Hp)))
           (real_mult d (real_mult p (real_inv_pos p Hp)))
           d).
  - apply (real_eq_trans
             (real_mult p (real_mult d (real_inv_pos p Hp)))
             (real_mult (real_mult p d) (real_inv_pos p Hp))
             (real_mult d (real_mult p (real_inv_pos p Hp)))).
    + apply real_mult_assoc.
    + apply (real_eq_trans
               (real_mult (real_mult p d) (real_inv_pos p Hp))
               (real_mult (real_mult d p) (real_inv_pos p Hp))
               (real_mult d (real_mult p (real_inv_pos p Hp)))).
      * apply (RealSetoid.real_eq_mult_compat (real_mult p d) (real_inv_pos p Hp)
                 (real_mult d p) (real_inv_pos p Hp)
                 (real_mult_comm p d) (real_eq_refl (real_inv_pos p Hp))).
      * apply real_eq_sym. apply real_mult_assoc.
  - apply (real_eq_trans
             (real_mult d (real_mult p (real_inv_pos p Hp)))
             (real_mult d real_one)
             d).
    + apply (RealSetoid.real_eq_mult_compat d (real_mult p (real_inv_pos p Hp))
               d real_one
               (real_eq_refl d) (real_inv_pos_correct p Hp)).
    + apply real_mult_one.
Qed.


(* 一减尺度件：p·w == 1 且 u+v == p ⟹ 1−(u·w) == v·w *)
Lemma pnk2_one_minus_scale : forall (p u v w : Real)
  (Hw : real_eq (real_mult p w) real_one)
  (Huv : real_eq (real_plus u v) p),
  real_eq (real_plus real_one (real_opp (real_mult u w))) (real_mult v w).
Proof.
  intros p u v w Hw Huv.
  assert (Hshift : real_eq (real_plus p (real_opp u)) v).
  { apply (real_eq_trans
             (real_plus p (real_opp u))
             (real_plus (real_plus u v) (real_opp u))
             v).
    - apply (RealSetoid.real_eq_plus_compat p (real_opp u)
               (real_plus u v) (real_opp u)
               (real_eq_sym (real_plus u v) p Huv)
               (real_eq_refl (real_opp u))).
    - apply (real_eq_trans
               (real_plus (real_plus u v) (real_opp u))
               (real_plus v (real_plus u (real_opp u)))
               v).
      + apply (real_eq_trans
                 (real_plus (real_plus u v) (real_opp u))
                 (real_plus (real_plus v u) (real_opp u))
                 (real_plus v (real_plus u (real_opp u)))).
        * apply (RealSetoid.real_eq_plus_compat (real_plus u v) (real_opp u)
                   (real_plus v u) (real_opp u)
                   (real_plus_comm u v) (real_eq_refl (real_opp u))).
        * apply real_eq_sym. apply real_plus_assoc.
      + apply (real_eq_trans
                 (real_plus v (real_plus u (real_opp u)))
                 (real_plus v real_zero)
                 v).
        * apply (RealSetoid.real_eq_plus_compat v (real_plus u (real_opp u))
                   v real_zero (real_eq_refl v) (real_plus_opp u)).
        * apply real_plus_zero. }
  apply (real_eq_trans
           (real_plus real_one (real_opp (real_mult u w)))
           (real_plus (real_mult p w) (real_mult (real_opp u) w))
           (real_mult v w)).
  - apply (RealSetoid.real_eq_plus_compat real_one
             (real_opp (real_mult u w))
             (real_mult p w) (real_mult (real_opp u) w)
             (real_eq_sym (real_mult p w) real_one Hw) (pnk2_opp_mult u w)).
  - apply (real_eq_trans
             (real_plus (real_mult p w) (real_mult (real_opp u) w))
             (real_mult (real_plus p (real_opp u)) w)
             (real_mult v w)).
    + apply pnk2_distrib_join.
    + apply (RealSetoid.real_eq_mult_compat (real_plus p (real_opp u)) w v w
               Hshift (real_eq_refl w)).
Qed.


(* real_kl_term 对 real_eq 的四参兼容（real_log_wd 吸收证书项差） *)
Lemma pnk2_kl_term_refl_eq : forall (a b c d : Real)
  (Ha : real_lt real_zero a) (Hb : real_lt real_zero b)
  (Hc : real_lt real_zero c) (Hd : real_lt real_zero d),
  real_eq a c -> real_eq b d ->
  real_eq (real_kl_term a b Ha Hb) (real_kl_term c d Hc Hd).
Proof.
  intros a b c d Ha Hb Hc Hd Hac Hbd.
  unfold real_kl_term.
  apply (RealSetoid.real_eq_mult_compat a
           (real_opp (real_log (real_mult b (real_inv_pos a Ha))
                                (real_mult_positive b (real_inv_pos a Ha) Hb
                                   (real_inv_pos_pos a Ha))))
           c
           (real_opp (real_log (real_mult d (real_inv_pos c Hc))
                                (real_mult_positive d (real_inv_pos c Hc) Hd
                                   (real_inv_pos_pos c Hc))))
           Hac
           (pnk_eq_opp_compat _ _
              (real_log_wd _ _ _ _
                 (RealSetoid.real_eq_mult_compat b (real_inv_pos a Ha)
                    d (real_inv_pos c Hc)
                    Hbd (pnk2_inv_wd a c Ha Hc Hac))))).
Qed.

(* 1−p 的对合：p2_one_minus(p2_one_minus p) == p（对称前提运输用） *)
Lemma pnk2_one_minus_inv : forall p : Real,
  real_eq (p2_one_minus (p2_one_minus p)) p.
Proof. intros p. pnk2_ring_eq. Qed.

(* 二点 KL 原子反射恒等式：p2_kl2(1−p,1−q) == p2_kl2(p,q)（eq 运输版） *)
Lemma pnk2_kl2_reflect : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hpp : real_lt real_zero (p2_one_minus (p2_one_minus p)))
  (Hqq : real_lt real_zero (p2_one_minus (p2_one_minus q))),
  real_eq (p2_kl2 (p2_one_minus p) (p2_one_minus q) Hp1 Hq1 Hpp Hqq)
          (p2_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hpp Hqq.
  unfold p2_kl2.
  apply (real_eq_trans
           (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                      (real_kl_term (p2_one_minus (p2_one_minus p))
                         (p2_one_minus (p2_one_minus q)) Hpp Hqq))
           (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                      (real_kl_term p q Hp Hq))
           (real_plus (real_kl_term p q Hp Hq)
                      (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
             (real_kl_term (p2_one_minus (p2_one_minus p))
                (p2_one_minus (p2_one_minus q)) Hpp Hqq)
             (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
             (real_kl_term p q Hp Hq)
             (real_eq_refl (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1))
             (pnk2_kl_term_refl_eq (p2_one_minus (p2_one_minus p))
                (p2_one_minus (p2_one_minus q)) p q Hpp Hqq Hp Hq
                (pnk2_one_minus_inv p) (pnk2_one_minus_inv q))).
  - apply real_plus_comm.
Qed.

(* 尺度闭合：d·d == 2p·(p·(y²/2))，y := d·inv(p) *)
Lemma pnk2_close_scale : forall (p d : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult d d)
          (real_mult pnk_two (real_mult p
             (real_mult p (real_mult w2t_c_half
                (real_mult (real_mult d (real_inv_pos p Hp))
                           (real_mult d (real_inv_pos p Hp))))))).
Proof.
  intros p d Hp.
  assert (Epy : real_eq (real_mult p (real_mult d (real_inv_pos p Hp))) d)
    by exact (pnk2_mult_inv_scale p d Hp).
  apply (real_eq_trans
           (real_mult d d)
           (real_mult (real_mult p (real_mult d (real_inv_pos p Hp))) (real_mult p (real_mult d (real_inv_pos p Hp))))
           (real_mult pnk_two (real_mult p
              (real_mult p (real_mult w2t_c_half (real_mult (real_mult d (real_inv_pos p Hp))
                            (real_mult d (real_inv_pos p Hp)))))))).
  - apply (RealSetoid.real_eq_mult_compat d d (real_mult p (real_mult d (real_inv_pos p Hp))) (real_mult p (real_mult d (real_inv_pos p Hp)))
             (real_eq_sym _ _ Epy) (real_eq_sym _ _ Epy)).
  - apply (real_eq_trans
             (real_mult (real_mult p (real_mult d (real_inv_pos p Hp))) (real_mult p (real_mult d (real_inv_pos p Hp))))
             (real_mult (real_mult (real_mult p (real_mult d (real_inv_pos p Hp))) (real_mult p (real_mult d (real_inv_pos p Hp)))) (real_mult pnk_two w2t_c_half))
             (real_mult pnk_two (real_mult p
                (real_mult p (real_mult w2t_c_half (real_mult (real_mult d (real_inv_pos p Hp))
                            (real_mult d (real_inv_pos p Hp)))))))).
    + apply (real_eq_trans
               (real_mult (real_mult p (real_mult d (real_inv_pos p Hp))) (real_mult p (real_mult d (real_inv_pos p Hp))))
               (real_mult (real_mult (real_mult p (real_mult d (real_inv_pos p Hp))) (real_mult p (real_mult d (real_inv_pos p Hp)))) real_one)
               (real_mult (real_mult (real_mult p (real_mult d (real_inv_pos p Hp))) (real_mult p (real_mult d (real_inv_pos p Hp)))) (real_mult pnk_two w2t_c_half))).
      * apply real_eq_sym. apply real_mult_one.
      * apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_mult p (real_mult d (real_inv_pos p Hp))) (real_mult p (real_mult d (real_inv_pos p Hp)))) real_one
                 (real_mult (real_mult p (real_mult d (real_inv_pos p Hp))) (real_mult p (real_mult d (real_inv_pos p Hp)))) (real_mult pnk_two w2t_c_half)
                 (real_eq_refl _)
                 (real_eq_sym (real_mult pnk_two w2t_c_half) real_one pnk2_c2_one)).
    + pnk2_ring_eq.
Qed.

(* ---- PNK2B.2 桥接件（近支砖）：q<p ⟹ d² ≤ 2p·KL₂ ---- *)

Theorem pnk2_pinsker_trunc5 : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hqp : real_lt q p),
  real_le_b (p2_tvsq p q)
            (real_mult pnk_two (real_mult p (p2_kl2 p q Hp Hq Hp1 Hq1))).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hqp.
  pose proof (p2_diff_pos_of_lt q p Hqp) as HD.
  assert (HX1 : real_lt real_zero (real_mult q (real_inv_pos p Hp)))
    by exact (real_mult_positive q (real_inv_pos p Hp) Hq
                (real_inv_pos_pos p Hp)).
  assert (Hy : real_lt real_zero (real_mult (p2_diff p q) (real_inv_pos p Hp)))
    by exact (real_mult_positive (p2_diff p q) (real_inv_pos p Hp) HD
                (real_inv_pos_pos p Hp)).
  (* E1m : 1−y == X₁ *)
  assert (E1m : real_eq (real_plus real_one
                          (real_opp (real_mult (p2_diff p q) (real_inv_pos p Hp))))
                        (real_mult q (real_inv_pos p Hp)))
    by exact (pnk2_one_minus_scale p (p2_diff p q) q (real_inv_pos p Hp)
          (real_inv_pos_correct p Hp) (pnk2_diff_plus_r p q)).
  assert (Hm : real_lt real_zero
                 (real_plus real_one
                    (real_opp (real_mult (p2_diff p q) (real_inv_pos p Hp)))))
    by exact (RealSetoid.real_lt_compat real_zero real_zero
          (real_mult q (real_inv_pos p Hp))
          (real_plus real_one (real_opp (real_mult (p2_diff p q) (real_inv_pos p Hp))))
          (real_eq_refl real_zero) (real_eq_sym _ _ E1m) HX1).
  assert (Hy1 : real_lt (real_mult (p2_diff p q) (real_inv_pos p Hp)) real_one)
    by exact (real_lt_zero_minus _ _ Hm).
  assert (Hy0 : real_le real_zero (real_mult (p2_diff p q) (real_inv_pos p Hp)))
    by exact (inl Hy).
  (* E2 : log(1−y) == log X₁ *)
  assert (E2 : real_eq
                 (real_log (real_plus real_one
                              (real_opp (real_mult (p2_diff p q) (real_inv_pos p Hp)))) Hm)
                 (real_log (real_mult q (real_inv_pos p Hp)) HX1))
    by exact (real_log_wd _ _ _ _ E1m).
  (* HT' : y + y²/2 ≤_B −log X₁ *)
  assert (HT' : real_le_b
                  (real_plus (real_mult (p2_diff p q) (real_inv_pos p Hp))
                             (real_mult w2t_c_half
                                (real_mult (real_mult (p2_diff p q) (real_inv_pos p Hp))
                                           (real_mult (p2_diff p q) (real_inv_pos p Hp)))))
                  (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX1)))
    by exact (leb3_le_b_eq_r _ _ _
          (w2t_trunc5_bridge (real_mult (p2_diff p q) (real_inv_pos p Hp)) Hy0 Hy1 Hm)
          (pnk_eq_opp_compat _ _ E2)).
  (* E4 : X₁−1 == −y *)
  assert (E4 : real_eq (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                       (real_opp (real_mult (p2_diff p q) (real_inv_pos p Hp)))).
  { apply (real_eq_trans
             (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
             (real_opp (real_plus real_one (real_opp (real_mult q (real_inv_pos p Hp)))))
             (real_opp (real_mult (p2_diff p q) (real_inv_pos p Hp)))).
    - pnk2_ring_eq.
    - apply pnk_eq_opp_compat.
      exact (pnk2_one_minus_scale p q (p2_diff p q) (real_inv_pos p Hp)
               (real_inv_pos_correct p Hp) (pnk2_diff_plus_l p q)). }
  (* H9a : y²/2 ≤_B φ₁ := (X₁−1) − log X₁ *)
  assert (H9a : real_le_b
                  (real_mult w2t_c_half
                     (real_mult (real_mult (p2_diff p q) (real_inv_pos p Hp))
                                (real_mult (p2_diff p q) (real_inv_pos p Hp))))
                  (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                             (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX1)))).
  { apply (leb3_le_b_eq_l
             (real_plus (real_opp (real_mult (p2_diff p q) (real_inv_pos p Hp)))
                        (real_plus (real_mult (p2_diff p q) (real_inv_pos p Hp))
                                   (real_mult w2t_c_half
                                      (real_mult (real_mult (p2_diff p q) (real_inv_pos p Hp))
                                                 (real_mult (p2_diff p q) (real_inv_pos p Hp))))))
             (real_mult w2t_c_half
                (real_mult (real_mult (p2_diff p q) (real_inv_pos p Hp))
                           (real_mult (p2_diff p q) (real_inv_pos p Hp))))
             (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                        (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX1)))).
    - pnk2_ring_eq.
    - apply (leb3_le_b_eq_r
               (real_plus (real_opp (real_mult (p2_diff p q) (real_inv_pos p Hp)))
                          (real_plus (real_mult (p2_diff p q) (real_inv_pos p Hp))
                                     (real_mult w2t_c_half
                                        (real_mult (real_mult (p2_diff p q) (real_inv_pos p Hp))
                                                   (real_mult (p2_diff p q) (real_inv_pos p Hp))))))
               (real_plus (real_opp (real_mult (p2_diff p q) (real_inv_pos p Hp)))
                          (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX1)))
               (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                          (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX1)))).
      + exact (real_le_b_plus_compat _ _ _ _ (leb3_le_b_refl _) HT').
      + apply (real_eq_sym _ _
                 (RealSetoid.real_eq_plus_compat
                    (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                    (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX1))
                    (real_opp (real_mult (p2_diff p q) (real_inv_pos p Hp)))
                    (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX1))
                    E4 (real_eq_refl _))). }
  (* H10 : p·(y²/2) ≤_B gap₁ *)
  assert (H10 : real_le_b
                  (real_mult p (real_mult w2t_c_half
                     (real_mult (real_mult (p2_diff p q) (real_inv_pos p Hp))
                                (real_mult (p2_diff p q) (real_inv_pos p Hp)))))
                  (real_mult p (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                     (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX1)))))
    by exact (leb3_le_b_pos_scale_l _ _ p H9a Hp).
  (* gap₂ > 0（G07 严格 Gibbs 核于 (1−p,1−q) 支） *)
  assert (Hhpos : real_lt real_zero
                    (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                               (real_plus (p2_one_minus q) (real_opp (p2_one_minus p)))))
    by exact (klst_gibbs_core_strict (p2_one_minus p) (p2_one_minus q) Hp1 Hq1
          (p2_one_minus_antitone q p Hqp)).
  assert (Hh_leb : real_le_b real_zero
                     (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                                (real_plus (p2_one_minus q) (real_opp (p2_one_minus p)))))
    by exact (pnk_lt_le_b _ _ Hhpos).
  (* Hstep : kl₁+(q−p) ≤_B kl₂ *)
  assert (Hstep : real_le_b (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
                            (p2_kl2 p q Hp Hq Hp1 Hq1)).
  { apply (leb3_le_b_eq_r
             (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
             (real_plus (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
                        (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                                   (real_plus (p2_one_minus q) (real_opp (p2_one_minus p)))))
             (p2_kl2 p q Hp Hq Hp1 Hq1)).
    - apply (leb3_le_b_eq_l
               (real_plus (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))) real_zero)
               (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
               (real_plus (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
                          (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                                     (real_plus (p2_one_minus q) (real_opp (p2_one_minus p)))))).
      + apply real_plus_zero.
      + apply (real_le_b_plus_compat _ _ _ _ (leb3_le_b_refl _) Hh_leb).
    - pnk2_ring_eq. }
  (* HGL : gap₁ ≤_B kl₂ *)
  assert (HGL : real_le_b
                  (real_mult p (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                     (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                (real_mult_positive q (real_inv_pos p Hp) Hq
                                   (real_inv_pos_pos p Hp))))))
                  (p2_kl2 p q Hp Hq Hp1 Hq1))
    by exact (leb3_le_b_eq_l _ _ _ (klst_gap_shape p q Hp Hq) Hstep).
  (* HM2 : p·(y²/2) ≤_B kl₂（EW 焊接见证项差） *)
  assert (EW : real_eq (real_log (real_mult q (real_inv_pos p Hp)) HX1) (real_log (real_mult q (real_inv_pos p Hp)) (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))))
    by exact (real_log_wd _ _ _ _ (real_eq_refl (real_mult q (real_inv_pos p Hp)))).
  assert (HGL' : real_le_b
                  (real_mult p (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                     (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX1))))
                  (p2_kl2 p q Hp Hq Hp1 Hq1))
    by exact (leb3_le_b_eq_l _ _ _
                (RealSetoid.real_eq_mult_compat p
                   (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                      (real_opp (real_log (real_mult q (real_inv_pos p Hp)) (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))))
                   p (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                      (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX1)))
                   (real_eq_refl p)
                   (RealSetoid.real_eq_plus_compat
                      (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                      (real_opp (real_log (real_mult q (real_inv_pos p Hp)) (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))))
                      (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                      (real_opp (real_log (real_mult q (real_inv_pos p Hp)) HX1))
                      (real_eq_refl (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)))
                      (real_eq_sym _ _ (pnk_eq_opp_compat _ _ EW))))
                HGL).
  assert (HM2 : real_le_b
                  (real_mult p (real_mult w2t_c_half (real_mult (real_mult (p2_diff p q) (real_inv_pos p Hp))
                                (real_mult (p2_diff p q) (real_inv_pos p Hp)))))
                  (p2_kl2 p q Hp Hq Hp1 Hq1))
    by exact (real_le_b_trans _ _ _ H10 HGL').
  (* 闭合：d² ≤_B 2p·kl₂ *)
  assert (H2p : real_lt real_zero (real_mult pnk_two p))
    by exact (real_mult_positive pnk_two p pnk_two_pos Hp).
  apply (leb3_le_b_eq_l
           (real_mult pnk_two (real_mult p
              (real_mult p (real_mult w2t_c_half (real_mult (real_mult (p2_diff p q) (real_inv_pos p Hp)) (real_mult (p2_diff p q) (real_inv_pos p Hp)))))))
           (p2_tvsq p q)
           (real_mult pnk_two (real_mult p (p2_kl2 p q Hp Hq Hp1 Hq1)))).
  - exact (real_eq_sym _ _ (pnk2_close_scale p (p2_diff p q) Hp)).
  - apply (leb3_le_b_eq_r
             (real_mult pnk_two (real_mult p
                (real_mult p (real_mult w2t_c_half (real_mult (real_mult (p2_diff p q) (real_inv_pos p Hp)) (real_mult (p2_diff p q) (real_inv_pos p Hp)))))))
             (real_mult (real_mult pnk_two p) (p2_kl2 p q Hp Hq Hp1 Hq1))
             (real_mult pnk_two (real_mult p (p2_kl2 p q Hp Hq Hp1 Hq1)))).
    + apply (leb3_le_b_eq_l
               (real_mult (real_mult pnk_two p) (real_mult p (real_mult w2t_c_half (real_mult (real_mult (p2_diff p q) (real_inv_pos p Hp)) (real_mult (p2_diff p q) (real_inv_pos p Hp))))))
               (real_mult pnk_two (real_mult p
                  (real_mult p (real_mult w2t_c_half (real_mult (real_mult (p2_diff p q) (real_inv_pos p Hp)) (real_mult (p2_diff p q) (real_inv_pos p Hp)))))))
               (real_mult (real_mult pnk_two p) (p2_kl2 p q Hp Hq Hp1 Hq1))).
      * exact (pnk2_ring_eq_lscale p (real_mult p (real_mult w2t_c_half (real_mult (real_mult (p2_diff p q) (real_inv_pos p Hp)) (real_mult (p2_diff p q) (real_inv_pos p Hp)))))).
      * exact (leb3_le_b_pos_scale_l _ _ (real_mult pnk_two p) HM2 H2p).
    + exact (pnk2_ring_eq_lscale p (p2_kl2 p q Hp Hq Hp1 Hq1)).
Qed.

(* ---- PNK2B.3 对称件：p<q ⟹ d² ≤ 2(1−p)·KL₂ ---- *)
(*   经二点 KL 原子反射恒等式 p2_kl2(1−p,1−q) == p2_kl2(p,q) 与        *)
(*   TV² 反射 ((1−p)−(1−q))² == (p−q)² 归约到近支砖。                   *)

Theorem pnk2_pinsker_trunc5_mirror : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hpq : real_lt p q),
  real_le_b (p2_tvsq p q)
            (real_mult pnk_two (real_mult (p2_one_minus p) (p2_kl2 p q Hp Hq Hp1 Hq1))).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hpq.
  assert (Hpp : real_lt real_zero (p2_one_minus (p2_one_minus p))).
  { exact (RealSetoid.real_lt_compat real_zero real_zero p
             (p2_one_minus (p2_one_minus p))
             (real_eq_refl real_zero) (real_eq_sym _ _ (pnk2_one_minus_inv p)) Hp). }
  assert (Hqq : real_lt real_zero (p2_one_minus (p2_one_minus q))).
  { exact (RealSetoid.real_lt_compat real_zero real_zero q
             (p2_one_minus (p2_one_minus q))
             (real_eq_refl real_zero) (real_eq_sym _ _ (pnk2_one_minus_inv q)) Hq). }
  pose proof (pnk2_pinsker_trunc5 (p2_one_minus p) (p2_one_minus q) Hp1 Hq1 Hpp Hqq
                (p2_one_minus_antitone p q Hpq)) as H.
  apply (leb3_le_b_eq_l
           (p2_tvsq (p2_one_minus p) (p2_one_minus q))
           (p2_tvsq p q)
           (real_mult pnk_two (real_mult (p2_one_minus p) (p2_kl2 p q Hp Hq Hp1 Hq1)))).
  - pnk2_ring_eq.
  - apply (leb3_le_b_eq_r
             (p2_tvsq (p2_one_minus p) (p2_one_minus q))
             (real_mult pnk_two
                        (real_mult (p2_one_minus p)
                                   (p2_kl2 (p2_one_minus p) (p2_one_minus q) Hp1 Hq1 Hpp Hqq)))
             (real_mult pnk_two
                        (real_mult (p2_one_minus p) (p2_kl2 p q Hp Hq Hp1 Hq1)))).
    + exact H.
    + apply (RealSetoid.real_eq_mult_compat pnk_two
               (real_mult (p2_one_minus p)
                          (p2_kl2 (p2_one_minus p) (p2_one_minus q) Hp1 Hq1 Hpp Hqq))
               pnk_two
               (real_mult (p2_one_minus p) (p2_kl2 p q Hp Hq Hp1 Hq1))
               (real_eq_refl pnk_two)
               (RealSetoid.real_eq_mult_compat (p2_one_minus p)
                  (p2_kl2 (p2_one_minus p) (p2_one_minus q) Hp1 Hq1 Hpp Hqq)
                  (p2_one_minus p) (p2_kl2 p q Hp Hq Hp1 Hq1)
                  (real_eq_refl (p2_one_minus p))
                  (pnk2_kl2_reflect p q Hp Hq Hp1 Hq1 Hpp Hqq))).
Qed.

(* ---- PNK2B 假设审计 ---- *)
Print Assumptions pnk2_pinsker_trunc5.
Print Assumptions pnk2_pinsker_trunc5_mirror.
