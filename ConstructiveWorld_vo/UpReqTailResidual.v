(* ==========================================================================)
   UpReqTailResidual.v — 指数尾残差的对数界族
   使命: w2t_exp_bound（指数部分和上界）、exp ≥ 1+g 桥接件、w2t_log_lower_quad/log_upper_lin（log(1+x) 二次下界与线性上界）、w2t_log_bound/trunc5_bridge（截断五项桥）。
   依赖: CW_ConstructiveWorld_219、UpRealLeB；Stdlib QArith.Qring、Qabs、Arith、Lia、Lqa。
   对标: log(1+x) 与 exp 的截断不等式族（初等分析标准估计）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import QArith.Qring QArith.Qabs Arith.Arith Lia.
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

(* ================================================================ *)
(* Section 1：Q 层尾残差引擎（Real 层件的逐点内核）                    *)
(* ================================================================ *)

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
(* ================================================================ *)
(* Section 2：Real 层 exp 上界尾残差件（target 2 主件）                *)
(* ================================================================ *)

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

(* ============================================================ *)
(* 本段界线：以上为已验证件。                      *)
(* 未竟清单（详见交付档案）：     *)
(*   w2t_half_pos / w2t_half_lt / w2t_exp_upper_ptw /            *)
(*   w2t_exp_upper_one / w2t_exp_upper_transport / w2t_exp_upper *)
(*   —— 语句面已定稿（见报告 §伤单），全部卡在 real_lt 逐点        *)
(*   witness 样板与 Qeq→QltT 运输（无态射实例）的平台摩擦，        *)
(*   非数学缺口；Q 引擎（Section 1）全链闭合。                    *)
(* ============================================================ *)

(* ============================================================ *)
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
(* ============================================================ *)

From Stdlib Require Import Lqa.

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

(* ---------------- 3.c/3.d（未竟段——源文存 attn/_tw2b_伤单片段-3c3d.v） ---------------- *)
(* 以下四件语句面已定稿、证明链已写至样板层（Qminus-in-Qlt 重写墙+逐点差值链），
   完整源文含逐条注释移存伤单片段文件，后续按配方续写即可：
   w2t_exp_s_le / w2t_lt_gap_strict / w2t_log_lower_quad / w2t_log_upper_lin /
   w2t_log_bound / w2t_trunc5_bridge。本段仅交付至 3.b 样板墙拆除件。 *)
(* ============================================================ *)
(* W2B 段界线：以上为已验证件。未竟详见                   *)
(*   交付档案 §四（未竟件清单+续写配方）。    *)
(* ============================================================ *)

(* ============================================================ *)
(* Section 4（纯追加）：3.c/3.d 未竟清结。                   *)
(*   六件：w2t_exp_s_le（★）/ w2t_lt_gap_strict /                   *)
(*   w2t_log_lower_quad / w2t_log_upper_lin / w2t_log_bound /       *)
(*   w2t_trunc5_bridge。配方：compat 先行拆 Qminus-in-QltT 墙；      *)
(*   lra 全数替换为显式 Q 传递链（Qle_lt_trans/Qlt_le_trans/         *)
(*   Qopp_lt_compat/Qplus_lt_r(proj2)/qeq_le 系）。                  *)
(* ============================================================ *)

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
