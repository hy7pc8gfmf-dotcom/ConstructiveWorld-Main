(* UpReqGibbsE2.v —— Gibbs 等式的有限具体路线件。                 *) (* 使命： 本件形式化 gibbs_equality 的有限具体路线：KL == 0 的    *)
(*   逐项钳零刻画、逐点切点等式与 eq-linear 桥显式注入的等式件。  *) (* 依赖： CW_ConstructiveWorld_219、UpRealLeB、UpReqGibbsD。      *)
(* 构造性： Set 层零 Prop（语句序/等全 Set 值 real_eq/real_lt/    *) (*   real_le_b）；零 Or 完成、零三分、零 LPO；全 Qed 闭合；       *)
(*   零公理面；可提取。                                          *) (* 编译配方： 9.1 直调（toolchain env.sh 同源）、cpu_guard 绑核。  *)
(* 诚实边界： log_eq_linear（log 线性等价桥）需强三分/LPO，       *) (*   构造性不可证——本件取有限具体路线绕开该不可证结果：          *)
(*   主件 gibbe2_gibbs_equality_bool 以显式前提注入该桥，         *) (*   无条件形式不主张（与 UpRealLeB 尾注已知限制同源）。          *)
(* 备注： 旧 UpReqGibbsE.v 不在依存面（无 .vo，不可 Require）；   *) (*   gibbe2_ 前缀库内独占。                                      *)
(* 主件清单（Part A/B/C 依序）：                                 *) (*   [保底件族] gibbe2_le_b_antisym（逐 n 构造，零 Or 完成）；    *)
(*   gibbe2_clamp_head / _r；gibbe2_list_sum_zero_extract_bool；  *) (*   gibbe2_kl_zero_tangent_eq（KL==0 ⟹ 逐点切点等式）。          *)
(*   [主件] gibbe2_gibbs_equality_bool：KL==0 ⟹ 逐点 p==q，       *) (*     eq-linear 桥显式注入（见头注诚实边界）。                   *)
(* 侦察结论（实读判定）：                                        *) (*   1. 逐项钳零可行：real_eq/real_lt 全 Set 值逐 eps 形，        *)
(*      real_list_sum_pos 背书「逐项正 ⟹ 和正」方向。            *) (*   2. 桥依赖判定：主件完成确须 log_eq_linear 桥（log 线性等价）。*)
(*      但 u_1·u_2 == 1 互易关系对任意分布不成立（归一化不生互易），*) (*      有限具体载体亦不能绕开 eq-linear 桥。                     *)
(* 结果（分级）：                                                *)
(*   [保底件族·逐项钳零] gibbe2_le_b_antisym（核心新件，逐 n 构造，*)
(*     零 Or 完成、零 LPO、零三分）；gibbe2_clamp_head / _r；     *)
(*     gibbe2_list_sum_zero_extract_bool（有限具体载体提取）。    *)
(*     gibbe2_kl_zero_tangent_eq：KL==0 ⟹ 逐点切点等式。          *)
(*   [主件·桥注入形消解件] gibbe2_gibbs_equality_bool：KL==0 ⟹    *)
(*     逐点切点等式 ⟹（eq-linear 桥显式注入）⟹ 逐点 p==q。       *)
(*     桥无条件不可证（库内判定在案；上游件 exp 复制机属阻塞域    *)
(*     本件零碰），依兜底预案以显式前提消解——                     *)
(*     req 层 dist_log_eq_linear（UpReqDist 假设申报位）的 Real   *)
(*     实例化缺口如实呈报。                                      *)
(* 红线：Set 层零 Prop（语句序/等全 Set 值 real_eq/real_lt/       *)
(*   real_le_b；零 Or 完成、零三分、零 LPO）；全 Qed 闭合；       *)
(*   零公理；既有文件零改（依存件只读）；                         *)
(*   旧 UpReqGibbsE.v 零碰（无 .vo，不可 Require，未依存）。      *)
(*   消解件陈述与 UpFirewallReq 的 req_temp_strict_ident2 对位面  *)
(*   的同位形（minus 形），证内 unfold 换形。                    *)

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
Require Import UpReqGibbsD.
From Stdlib Require Import List QArith.QArith QArith.Qabs QArith.Qround
               Arith.Arith.
From Stdlib Require Import Lia.
Import ListNotations.

(* ============================================================ *)
(* Part A：Q 层半分 helper                                                     *)
(* ============================================================ *)

Lemma gibbe2_Q_half_pos : forall eps : Q, QltT 0 eps -> QltT 0 (eps * (1#2))%Q.
Proof.
  intros eps Heps. apply Qlt_to_QltT. apply (Qmult_lt_0_compat eps (1#2)).
  - apply QltT_to_Qlt. exact Heps.
  - reflexivity.
Qed.

Lemma gibbe2_Q_half_lt : forall eps : Q, QltT 0 eps -> Qlt (eps * (1#2))%Q eps.
Proof.
  intros eps Heps.
  assert (H1 : Qlt ((1#2) * eps) (1 * eps)).
  { apply (Qmult_lt_compat_r (1#2) 1 eps).
    - apply QltT_to_Qlt. exact Heps.
    - reflexivity. }
  rewrite Qmult_1_l in H1.
  rewrite (Qmult_comm (1#2) eps) in H1.
  exact H1.
Qed.

(* ============================================================ *)
(* Part B：le_b 补层序机                                                       *)
(* ============================================================ *)

(* B1：le_b 右端 eq 换形 *)
Lemma gibbe2_le_b_id_r : forall a b c : Real,
  real_le_b a b -> real_eq b c -> real_le_b a c.
Proof.
  intros a b c H Hbc eps Heps.
  unfold real_le_b in H.
  exact (RealSetoid.real_lt_compat a a (real_plus b eps) (real_plus c eps)           (real_eq_refl a)           (RealSetoid.real_eq_plus_compat b eps c eps Hbc (real_eq_refl eps))           (H eps Heps)).
Qed.

(* B2：le_b 右加平移 *)
Lemma gibbe2_le_b_translate_r : forall x y z : Real,
  real_le_b x y -> real_le_b (real_plus x z) (real_plus y z).
Proof.
  intros x y z H eps Heps. unfold real_le_b in H.
  apply (RealSetoid.real_lt_compat (real_plus z x) (real_plus x z)
           (real_plus z (real_plus y eps)) (real_plus (real_plus y z) eps)).
  - apply real_plus_comm.
  - apply (real_eq_trans _ (real_plus (real_plus z y) eps) _).
    + apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat (real_plus z y) eps
               (real_plus y z) eps
               (real_plus_comm z y) (real_eq_refl eps)).
  - exact (real_lt_plus_translate z x (real_plus y eps) (H eps Heps)).
Qed.

(* B3：le_b a b ⟹ le_b 0 (b−a) *)
Lemma gibbe2_le_b_nonneg_diff : forall a b : Real,
  real_le_b a b -> real_le_b real_zero (real_plus b (real_opp a)).
Proof.
  intros a b H eps Heps. unfold real_le_b in H.
  apply (RealSetoid.real_lt_compat (real_plus (real_opp a) a)
           real_zero
           (real_plus (real_opp a) (real_plus b eps))
           (real_plus (real_plus b (real_opp a)) eps)).
  - apply (real_eq_trans _ (real_plus a (real_opp a)) _).
    + apply real_plus_comm.
    + exact (real_plus_opp a).
  - apply (real_eq_trans _ (real_plus (real_plus (real_opp a) b) eps) _).
    + apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp a) b) eps
               (real_plus b (real_opp a)) eps
               (real_plus_comm (real_opp a) b) (real_eq_refl eps)).
  - exact (real_lt_plus_translate (real_opp a) a (real_plus b eps) (H eps Heps)).
Qed.

(* B4【核心新件】：le_b Bishop 序反对称（逐 n 构造，零 Or 完成、零 LPO） *)
Lemma gibbe2_le_b_antisym : forall a b : Real,
  real_le_b a b -> real_le_b b a -> real_eq a b.
Proof.
  intros a b H1 H2 eps Heps.
  assert (He2pos : real_lt real_zero (real_const (eps * (1#2))%Q))
    by (apply real_const_pos; apply gibbe2_Q_half_pos; exact Heps).
  assert (Hhe : Qlt (eps * (1#2))%Q eps) by (apply gibbe2_Q_half_lt; exact Heps).
  destruct (H1 _ He2pos) as [g1 [Hg1pos [N1 HN1]]].
  destruct (H2 _ He2pos) as [g2 [Hg2pos [N2 HN2]]].
  exists (max N1 N2).
  intros n Hn.
  assert (Hn1 : NatLe N1 n).
  { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
      [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
  assert (Hn2 : NatLe N2 n).
  { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
      [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
  specialize (HN1 n Hn1). specialize (HN2 n Hn2).
  apply QltT_to_Qlt in HN1. apply QltT_to_Qlt in HN2.
  rewrite real_plus_proj in HN1, HN2.
  rewrite real_const_proj in HN1, HN2.
  set (x := projT1 a n - projT1 b n).
  set (h := (eps * (1#2))%Q).
  assert (Hg1q : 0 < g1) by (apply QltT_to_Qlt; exact Hg1pos).
  assert (Hg2q : 0 < g2) by (apply QltT_to_Qlt; exact Hg2pos).
  (* 上界：x < h（x := a_n − b_n，环归 + lia 完成） *)
  assert (Hstep1 : projT1 a n - projT1 b n + g1
                   < projT1 a n - projT1 b n
                     + (projT1 b n + eps * (1#2) - projT1 a n)).
  { exact (proj2 (Qplus_lt_r g1 (projT1 b n + eps * (1#2) - projT1 a n)
                   (projT1 a n - projT1 b n)) HN1). }
  assert (Hring1 : projT1 a n - projT1 b n
                   + (projT1 b n + eps * (1#2) - projT1 a n)
                   == eps * (1#2)) by ring.
  rewrite Hring1 in Hstep1.
  assert (Hub : projT1 a n - projT1 b n < eps * (1#2)).
  { apply (Qle_lt_trans _ (projT1 a n - projT1 b n + g1) _).
    - rewrite <- (Qplus_0_r (projT1 a n - projT1 b n)) at 1.
      apply (proj2 (Qplus_le_r 0 g1 (projT1 a n - projT1 b n))).
      exact (b5dH_q_pos_le g1 Hg1q).
    - exact Hstep1. }
  (* 下界：−x < h *)
  assert (Hstep2 : - (projT1 a n - projT1 b n) + g2
                   < - (projT1 a n - projT1 b n)
                     + (projT1 a n + eps * (1#2) - projT1 b n)).
  { exact (proj2 (Qplus_lt_r g2 (projT1 a n + eps * (1#2) - projT1 b n)
                   (- (projT1 a n - projT1 b n))%Q) HN2). }
  assert (Hring2 : - (projT1 a n - projT1 b n)
                   + (projT1 a n + eps * (1#2) - projT1 b n)
                   == eps * (1#2)) by ring.
  rewrite Hring2 in Hstep2.
  assert (Hdn : (- (projT1 a n - projT1 b n))%Q < eps * (1#2)).
  { apply (Qle_lt_trans _ ((- (projT1 a n - projT1 b n))%Q + g2) _).
    - rewrite <- (Qplus_0_r (- (projT1 a n - projT1 b n))%Q) at 1.
      apply (proj2 (Qplus_le_r 0 g2 (- (projT1 a n - projT1 b n))%Q)).
      exact (b5dH_q_pos_le g2 Hg2q).
    - exact Hstep2. }
  (* 终判：|x| < eps（符号两案，Q 可判定，零三分律） *)
  unfold x, h.
  apply Qlt_to_QltT.
  destruct (Qlt_le_dec 0 (projT1 a n - projT1 b n)) as [Hsx | Hsx].
  - rewrite (Qabs_pos (projT1 a n - projT1 b n) (b5dH_q_pos_le _ Hsx)).
    apply (Qlt_le_trans _ (eps * (1#2)) eps Hub).
    exact (Qlt_le_weak _ _ Hhe).
  - rewrite (Qabs_neg (projT1 a n - projT1 b n) Hsx).
    apply (Qlt_le_trans (- (projT1 a n - projT1 b n))%Q (eps * (1#2)) eps Hdn).
    exact (Qlt_le_weak _ _ Hhe).
Qed.

(* ============================================================ *)
(* Part C：保底1·逐项钳零件族                                                  *)
(* ============================================================ *)

(* C1：二项和零 ⟹ 首项零 *)
Lemma gibbe2_clamp_head : forall a b : Real,
  real_le_b real_zero a -> real_le_b real_zero b ->
  real_eq (real_plus a b) real_zero -> real_eq real_zero a.
Proof.
  intros a b Ha Hb Hsum.
  apply (gibbe2_le_b_antisym real_zero a Ha).
  apply (gibbe2_le_b_id_r a (real_plus b a) real_zero).
  - apply (gibbsd_le_b_id_l a (real_plus real_zero a) (real_plus b a)
             (real_eq_trans a (real_plus a real_zero) (real_plus real_zero a)
                (real_eq_sym _ _ (real_plus_zero a)) (real_plus_comm a real_zero))
             (gibbe2_le_b_translate_r real_zero b a Hb)).
  - apply (real_eq_trans (real_plus b a) (real_plus a b) real_zero
             (real_plus_comm b a) Hsum).
Qed.

(* C2：二项和零 ⟹ 次项零（comm 副本） *)
Lemma gibbe2_clamp_head_r : forall a b : Real,
  real_le_b real_zero a -> real_le_b real_zero b ->
  real_eq (real_plus a b) real_zero -> real_eq real_zero b.
Proof.
  intros a b Ha Hb Hsum.
  apply (gibbe2_clamp_head b a Hb Ha).
  apply (real_eq_trans _ (real_plus a b) _).
  - apply real_plus_comm.
  - exact Hsum.
Qed.

(* C3【保底1 主件】：有限具体载体 [true;false] 逐项和零提取 *)
Lemma gibbe2_list_sum_zero_extract_bool :
  forall (f : bool -> Real),
    (forall s : bool, real_le_b real_zero (f s)) ->
    real_eq (real_list_sum bool f [true; false]) real_zero ->
    forall s : bool, real_eq real_zero (f s).
Proof.
  intros f Hpt Hsum s. destruct s; simpl in Hsum.
  - exact (gibbe2_clamp_head (f true) (real_plus (f false) real_zero)
             (Hpt true)
             (gibbe2_le_b_id_r real_zero (f false)
                (real_plus (f false) real_zero)
                (Hpt false) (real_eq_sym _ _ (real_plus_zero (f false))))
             Hsum).
  - apply (real_eq_trans real_zero (real_plus (f false) real_zero) (f false)).
    + exact (gibbe2_clamp_head_r (f true) (real_plus (f false) real_zero)
               (Hpt true)
               (gibbe2_le_b_id_r real_zero (f false)
                  (real_plus (f false) real_zero)
                  (Hpt false) (real_eq_sym _ _ (real_plus_zero (f false))))
               Hsum).
    + exact (real_plus_zero (f false)).
Qed.

(* ============================================================ *)

(* ============================================================ *)

(* D0：和零 ⟹ 项恒等 *)
Lemma gibbe2_kl_eq_of_w_zero : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_plus (real_kl_term p q Hp Hq)
                     (real_opp (real_plus p (real_opp q)))) real_zero ->
  real_eq (real_kl_term p q Hp Hq) (real_plus p (real_opp q)).
Proof.
  intros p q Hp Hq H.
  set (X := real_plus p (real_opp q)).
  set (K := real_kl_term p q Hp Hq).
  set (NX := real_opp X).
  (* kl == (kl + −X) + X *)
  apply (real_eq_trans K (real_plus (real_plus K NX) X) X).
  - apply (real_eq_trans K (real_plus K real_zero) (real_plus (real_plus K NX) X)).
    + exact (real_eq_sym (real_plus K real_zero) K (real_plus_zero K)).
    + apply (real_eq_trans (real_plus K real_zero)
               (real_plus K (real_plus NX X))
               (real_plus (real_plus K NX) X)).
      * apply (RealSetoid.real_eq_plus_compat K real_zero K
                 (real_plus NX X)
                 (real_eq_refl K)
                 (real_eq_trans real_zero (real_plus X NX) (real_plus NX X)
                    (real_eq_sym (real_plus X NX) real_zero (real_plus_opp X))
                    (real_plus_comm X NX))).
      * exact (real_plus_assoc K NX X).
  - (* (kl + −X) + X == 0 + X == X *)
    apply (real_eq_trans (real_plus (real_plus K NX) X)
             (real_plus real_zero X) X).
    + exact (RealSetoid.real_eq_plus_compat (real_plus K NX) X real_zero X
               H (real_eq_refl X)).
    + apply (real_eq_trans (real_plus real_zero X)
               (real_plus X real_zero) X
               (real_plus_comm real_zero X)
               (real_plus_zero X)).
Qed.


Lemma gibbe2_tangent_eq : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_kl_term p q Hp Hq) (real_plus p (real_opp q)) ->
  real_eq (real_log (real_mult q (real_inv_pos p Hp))
                    (real_mult_positive q (real_inv_pos p Hp) Hq
                       (real_inv_pos_pos p Hp)))
          (real_plus (real_mult q (real_inv_pos p Hp))
                     (real_opp real_one)).
Proof.
  intros p q Hp Hq H.
  set (u := real_mult q (real_inv_pos p Hp)).
  set (Hu := real_mult_positive q (real_inv_pos p Hp) Hq
               (real_inv_pos_pos p Hp)).
  set (L := real_log u Hu).
  (* H : p·(−L) == p + −q *)
  (* 步1：p·L == q + −p（两侧取 opp） *)
  assert (Hs1 : real_eq (real_mult p L) (real_plus q (real_opp p))).
  { apply (real_eq_trans (real_mult p L)
             (real_opp (real_mult p (real_opp L)))
             (real_plus q (real_opp p))).
    - apply (real_eq_sym (real_opp (real_mult p (real_opp L)))
               (real_mult p L)
               (real_eq_trans (real_opp (real_mult p (real_opp L)))
                  (real_mult p (real_opp (real_opp L)))
                  (real_mult p L)
                  (real_opp_mult p (real_opp L))
                  (RealSetoid.real_eq_mult_compat p
                     (real_opp (real_opp L)) p L
                     (real_eq_refl p) (real_opp_opp L)))).
    - apply (real_eq_trans (real_opp (real_mult p (real_opp L)))
               (real_opp (real_plus p (real_opp q)))
               (real_plus q (real_opp p))
               (RealSetoid.real_eq_opp_compat (real_mult p (real_opp L))
                  (real_plus p (real_opp q)) H)
               (gibbsd_minus_flip p q)).
  }
  (* 步2：L == (q−p)·inv p *)
  assert (Hs2 : real_eq L (real_mult (real_plus q (real_opp p))
                                        (real_inv_pos p Hp))).
  { apply (real_eq_trans L
             (real_mult (real_mult p L) (real_inv_pos p Hp))
             (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))).
    - apply (real_eq_trans L (real_mult L real_one)
               (real_mult (real_mult p L) (real_inv_pos p Hp))).
      + apply (real_eq_sym (real_mult L real_one) L (real_mult_one L)).
      + apply (real_eq_trans (real_mult L real_one)
                 (real_mult L (real_mult p (real_inv_pos p Hp)))
                 (real_mult (real_mult p L) (real_inv_pos p Hp))).
        * apply (RealSetoid.real_eq_mult_compat L real_one
                   L (real_mult p (real_inv_pos p Hp))
                   (real_eq_refl L)
                   (real_eq_sym (real_mult p (real_inv_pos p Hp)) real_one
                      (real_inv_pos_correct p Hp))).
        * apply (real_eq_trans
                   (real_mult L (real_mult p (real_inv_pos p Hp)))
                   (real_mult (real_mult L p) (real_inv_pos p Hp))
                   (real_mult (real_mult p L) (real_inv_pos p Hp))).
          -- exact (real_mult_assoc L p (real_inv_pos p Hp)).
          -- apply (RealSetoid.real_eq_mult_compat (real_mult L p)
                     (real_inv_pos p Hp) (real_mult p L) (real_inv_pos p Hp)
                     (real_mult_comm L p) (real_eq_refl _)).
    - apply (RealSetoid.real_eq_mult_compat (real_mult p L)
               (real_inv_pos p Hp) (real_plus q (real_opp p))
               (real_inv_pos p Hp) Hs1 (real_eq_refl _)).
  }
  (* 步3：(q−p)·inv p == q·inv p + −1 == u + −1 *)
  assert (Hs3 : real_eq (real_mult (real_plus q (real_opp p))
                                   (real_inv_pos p Hp))
                        (real_plus u (real_opp real_one))).
  { apply (real_eq_trans
             (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))
             (real_plus (real_mult (real_inv_pos p Hp) q)
                        (real_mult (real_inv_pos p Hp) (real_opp p)))
             (real_plus u (real_opp real_one))).
    - apply (real_eq_trans
               (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))
               (real_mult (real_inv_pos p Hp) (real_plus q (real_opp p)))
               (real_plus (real_mult (real_inv_pos p Hp) q)
                          (real_mult (real_inv_pos p Hp) (real_opp p)))).
      + apply (real_mult_comm (real_plus q (real_opp p)) (real_inv_pos p Hp)).
      + exact (real_distrib (real_inv_pos p Hp) q (real_opp p)).
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult (real_inv_pos p Hp) q)
               (real_mult (real_inv_pos p Hp) (real_opp p))
               (real_mult q (real_inv_pos p Hp)) (real_opp real_one)).
      + apply (real_mult_comm (real_inv_pos p Hp) q).
      + apply (real_eq_trans (real_mult (real_inv_pos p Hp) (real_opp p))
                   (real_opp (real_mult (real_inv_pos p Hp) p))
                   (real_opp real_one)).
        * apply (real_eq_sym _ _ (real_opp_mult (real_inv_pos p Hp) p)).
        * apply (RealSetoid.real_eq_opp_compat
                   (real_mult (real_inv_pos p Hp) p) real_one).
          apply (real_eq_trans (real_mult (real_inv_pos p Hp) p)
                     (real_mult p (real_inv_pos p Hp)) real_one).
          -- apply (real_mult_comm (real_inv_pos p Hp) p).
          -- exact (real_inv_pos_correct p Hp).
  }
  exact (real_eq_trans L _ _ Hs2 Hs3).
Qed.


Lemma gibbe2_kl_zero_tangent_eq :
  forall (p q : bool -> Real)
    (Hp : forall s : bool, real_lt real_zero (p s))
    (Hq : forall s : bool, real_lt real_zero (q s))
    (Hnp : real_eq (real_list_sum bool p [true; false]) real_one)
    (Hnq : real_eq (real_list_sum bool q [true; false]) real_one),
  real_eq (real_list_sum bool
             (fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s))
             [true; false])
          real_zero ->
  forall s : bool,
    real_eq (real_log (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                      (real_mult_positive (q s) (real_inv_pos (p s) (Hp s))
                         (Hq s) (real_inv_pos_pos (p s) (Hp s))))
            (real_plus (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                       (real_opp real_one)).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl.
  set (K := fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s)).
  set (G := fun s : bool => real_plus (p s) (real_opp (q s))).
  set (D := fun s : bool => real_plus (K s) (real_opp (G s))).
  (* 1. Σ(p−q) == 0 *)
  assert (HsumG0 : real_eq (real_list_sum bool G [true; false]) real_zero).
  { apply (real_eq_trans
             (real_list_sum bool G [true; false])
             (real_plus (real_list_sum bool p [true; false])
                        (real_opp (real_list_sum bool q [true; false])))
             real_zero).
    - exact (gibbsd_list_sum_minus bool p q [true; false]).
    - apply (real_eq_trans
               (real_plus (real_list_sum bool p [true; false])
                          (real_opp (real_list_sum bool q [true; false])))
               (real_plus real_one (real_opp real_one)) real_zero).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool p [true; false])
                 (real_opp (real_list_sum bool q [true; false]))
                 real_one (real_opp real_one) Hnp
                 (RealSetoid.real_eq_opp_compat
                    (real_list_sum bool q [true; false]) real_one Hnq)).
      + exact (real_plus_opp real_one).
  }
  (* 2. ΣD == 0 *)
  assert (HsumD : real_eq (real_list_sum bool D [true; false]) real_zero).
  { unfold D.
    apply (real_eq_trans
             (real_list_sum bool
                (fun s : bool => real_plus (K s) (real_opp (G s))) [true; false])
             (real_plus (real_list_sum bool K [true; false])
                        (real_opp (real_list_sum bool G [true; false])))
             real_zero).
    - apply (real_eq_trans
               (real_list_sum bool
                  (fun s : bool => real_plus (K s) (real_opp (G s))) [true; false])
               (real_plus (real_list_sum bool K [true; false])
                          (real_list_sum bool
                             (fun s : bool => real_opp (G s)) [true; false]))
               (real_plus (real_list_sum bool K [true; false])
                          (real_opp (real_list_sum bool G [true; false])))).
      + exact (real_list_sum_add bool K (fun s : bool => real_opp (G s))
                   [true; false]).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool K [true; false])
                 (real_list_sum bool (fun s : bool => real_opp (G s)) [true; false])
                 (real_list_sum bool K [true; false])
                 (real_opp (real_list_sum bool G [true; false]))
                 (real_eq_refl _)
                 (real_list_sum_opp bool G [true; false])).
    - apply (real_eq_trans
               (real_plus (real_list_sum bool K [true; false])
                          (real_opp (real_list_sum bool G [true; false])))
               (real_plus real_zero (real_opp real_zero)) real_zero).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool K [true; false])
                 (real_opp (real_list_sum bool G [true; false]))
                 real_zero (real_opp real_zero) Hkl
                 (RealSetoid.real_eq_opp_compat
                    (real_list_sum bool G [true; false]) real_zero HsumG0)).
      + apply (real_eq_trans
                 (real_plus real_zero (real_opp real_zero))
                 (real_plus real_zero real_zero) real_zero).
        * apply (RealSetoid.real_eq_plus_compat real_zero (real_opp real_zero)
                   real_zero real_zero (real_eq_refl _) (real_opp_zero)).
        * exact (real_plus_zero real_zero).
  }
  (* 3. 逐点钳零：D s == 0 *)
  assert (Hclamp : forall s : bool, real_eq (D s) real_zero).
  { intro s. apply (real_eq_sym _ _).
    apply (gibbe2_list_sum_zero_extract_bool D).
    - intro s0. exact (gibbe2_le_b_nonneg_diff _ _
                         (gibbsd_gibbs_pointwise_B bool p q s0 (Hp s0) (Hq s0))).
    - exact HsumD. }
  (* 4. 逐点：K s == G s ⟹ 切点等式 *)
  intro s. apply gibbe2_tangent_eq.
  apply gibbe2_kl_eq_of_w_zero.
  exact (Hclamp s).
Qed.

(* ============================================================ *)
(* Part E：主件·桥注入形消解件                                                 *)
(* ============================================================ *)

Theorem gibbe2_gibbs_equality_bool :
  forall (p q : bool -> Real)
    (Hp : forall s : bool, real_lt real_zero (p s))
    (Hq : forall s : bool, real_lt real_zero (q s))
    (Hnp : real_eq (real_list_sum bool p [true; false]) real_one)
    (Hnq : real_eq (real_list_sum bool q [true; false]) real_one),
  real_eq (real_list_sum bool
             (fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s))
             [true; false])
          real_zero ->
  (forall (u : Real) (Hu : real_lt real_zero u),
     real_eq (real_log u Hu) (real_plus u (real_opp real_one)) ->
     real_eq u real_one) ->
  forall s : bool, real_eq (p s) (q s).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl Heqlin s.
  assert (Htan := gibbe2_kl_zero_tangent_eq p q Hp Hq Hnp Hnq Hkl s).
  assert (Hu1 : real_eq (real_mult (q s) (real_inv_pos (p s) (Hp s))) real_one).
  { apply (Heqlin (real_mult (q s) (real_inv_pos (p s) (Hp s)))
             (real_mult_positive (q s) (real_inv_pos (p s) (Hp s))
                (Hq s) (real_inv_pos_pos (p s) (Hp s)))).
    exact Htan. }
  apply (real_eq_trans (p s)
           (real_mult (p s) (real_mult (q s) (real_inv_pos (p s) (Hp s))))
           (q s)).
  - apply (real_eq_trans (p s) (real_mult (p s) real_one)
             (real_mult (p s) (real_mult (q s) (real_inv_pos (p s) (Hp s))))).
    + apply (real_eq_sym (real_mult (p s) real_one) (p s)
               (real_mult_one (p s))).
    + apply (RealSetoid.real_eq_mult_compat (p s) real_one (p s)
               (real_mult (q s) (real_inv_pos (p s) (Hp s)))
               (real_eq_refl (p s))
               (real_eq_sym (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                  real_one Hu1)).
  - exact (gibbsd_p_mult_ratio (p s) (q s) (Hp s)).
Qed.

(* ============================================================ *)
(* 尾核：Print Assumptions（G3 零公理见证）                                    *)
(* ============================================================ *)

Print Assumptions gibbe2_le_b_antisym.
Print Assumptions gibbe2_clamp_head.
Print Assumptions gibbe2_list_sum_zero_extract_bool.
Print Assumptions gibbe2_kl_zero_tangent_eq.
Print Assumptions gibbe2_gibbs_equality_bool.

Print Assumptions gibbe2_le_b_id_r.
