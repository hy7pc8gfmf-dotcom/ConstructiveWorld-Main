(* ============================================================ *)
(* abl_div_kl_chisq_twopoint.v                                    *)
(* 模块名：abl_div_kl_chisq_twopoint                               *)
(* 数学使命：两点分布 KL₂≤χ² 上界主桥（f-散度海峡主件）——主件        *)
(*   p2_kl2 ≤_B div2_cs（Bishop 形出口，单 log 引擎 log_le_linear、  *)
(*   零 Or 分支）；配套逐点 gap 恒等（kl+(q−p)==χ项−p·E，E 为切距    *)
(*   超额）、gap 非负（klst_gap_shape 供弹）、等号侧（χ==0⟹KL₂==0，  *)
(*   gibbe2 反对称闭合）、eps 形出口、pnt 运输互认、差异⟹χ>0 供给位    *)
(*   （KL>0 生产器=在树 p2_kl2_pos，本件不重列；件 1c 与在树           *)
(*     pnk2_pinsker_one 为阶梯对照位，本件不重列）。                  *)
(* 依赖清单：件 1 abl_div_chisq_twopoint（div2_cs/d2 缩放与环件）、   *)
(*   PinskerTwoPoint（p2_kl2/p2_diff/p2_tvsq/p2_one_minus/          *)
(*   p2_diff_pos_of_lt）、G07_KLWall（klst_gap_shape）、             *)
(*   G08_Gibbs（gibbe2_le_b_antisym Bishop 反对称）、                *)
(*   UpReqTrainingEquiv（real_kl_term_expand/real_log_inv_pos_opp）、 *)
(*   UpReqPinskerTransport（pnt_kl2）、S03/S07/S08（inv/log/kl_term   *)
(*   基座）、UpRealLeB/B2/B3（real_le_b 工具族+log_le_linear_B）。    *)
(* 构造性注记：全件 Set 层出口；非严格序一律 Bishop 形 real_le_b；     *)
(*   kl 原子环闭走 remember+destruct+ring（点式 ring 仅用于无 log     *)
(*   展开的纯多项式恒等）；inv 证书项逐点穿线（沿用件 1 同款坑位）；   *)
(*   零承认式语句、零经典公理、全部 Qed 闭合。                        *)
(* 编译配方：                                                       *)
(*   source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&        *)
(*   ulimit -s 65532 && cd <池> && nice -19 rocq c -native-compiler  *)
(*   no -Q <缓存根> "" abl_div_kl_chisq_twopoint.v                   *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring QArith.Qfield.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import PinskerTwoPoint.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import G07_KLWall.
Require Import G08_Gibbs.
Require Import UpReqTrainingEquiv.
Require Import UpReqPinskerTransport.
Require Import abl_div_chisq_twopoint.

(* ---- 1. log 拆分：log(p·inv q) == log p − log q（证书逐点穿线） ---- *)

Lemma dkc_log_split : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q),
  real_eq (real_log (real_mult p (real_inv_pos q Hq))
                    (real_mult_positive p (real_inv_pos q Hq) Hp
                       (real_inv_pos_pos q Hq)))
          (real_plus (real_log p Hp) (real_opp (real_log q Hq))).
Proof.
  intros p q Hp Hq.
  apply (real_eq_trans
           (real_log (real_mult p (real_inv_pos q Hq))
                     (real_mult_positive p (real_inv_pos q Hq) Hp
                        (real_inv_pos_pos q Hq)))
           (real_plus (real_log p Hp)
                      (real_log (real_inv_pos q Hq) (real_inv_pos_pos q Hq)))
           (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
  - exact (real_log_mult p (real_inv_pos q Hq) Hp (real_inv_pos_pos q Hq)).
  - apply (RealSetoid.real_eq_plus_compat (real_log p Hp)
             (real_log (real_inv_pos q Hq) (real_inv_pos_pos q Hq))
             (real_log p Hp) (real_opp (real_log q Hq))).
    + apply real_eq_refl.
    + exact (real_log_inv_pos_opp q Hq).
Qed.

(* ---- 2. χ² 首项 s-形展开：(p−q)²·inv q == p·s − 贰p + q ---- *)
(*   （s := p·inv q；两次 inv 右消去 d2_mult_inv_r，余项纯环）        *)

Lemma dkc_cs_term_expand : forall (p q : Real) (Hq : real_lt real_zero q),
  real_eq (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
          (real_plus (real_mult p (real_mult p (real_inv_pos q Hq)))
                     (real_plus (real_mult d2_two (real_opp p)) q)).
Proof.
  intros p q Hq.
  assert (HR : real_eq (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                 (real_plus (real_mult (real_mult p p) (real_inv_pos q Hq))
                            (real_plus
                               (real_mult (real_mult (real_opp d2_two)
                                          (real_mult p q))
                                          (real_inv_pos q Hq))
                               (real_mult (real_mult q q)
                                          (real_inv_pos q Hq))))).
  { (* inv 项 remember 为变量后方可环闭（环闭原子位） *)
    remember (real_inv_pos q Hq) as iq. d2_ring_eq. }
  assert (HT1 : real_eq (real_mult (real_mult p q) (real_inv_pos q Hq)) p).
  { exact (d2_mult_inv_r p q Hq). }
  assert (HT2 : real_eq (real_mult (real_mult q q) (real_inv_pos q Hq)) q).
  { exact (d2_mult_inv_r q q Hq). }
  assert (HT3 : real_eq
                  (real_mult (real_mult (real_opp d2_two) (real_mult p q))
                             (real_inv_pos q Hq))
                  (real_mult d2_two (real_opp p))).
  { apply (real_eq_trans
             (real_mult (real_mult (real_opp d2_two) (real_mult p q))
                        (real_inv_pos q Hq))
             (real_mult (real_opp d2_two)
                        (real_mult (real_mult p q) (real_inv_pos q Hq)))
             (real_mult d2_two (real_opp p))).
    - apply real_eq_sym. apply real_mult_assoc.
    - apply (real_eq_trans
               (real_mult (real_opp d2_two)
                          (real_mult (real_mult p q) (real_inv_pos q Hq)))
               (real_mult (real_opp d2_two) p)
               (real_mult d2_two (real_opp p))).
      + apply (RealSetoid.real_eq_mult_compat (real_opp d2_two)
                 (real_mult (real_mult p q) (real_inv_pos q Hq))
                 (real_opp d2_two) p).
        * apply real_eq_refl.
        * exact HT1.
      + d2_ring_eq. }
  apply (real_eq_trans
           (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
           (real_plus (real_mult (real_mult p p) (real_inv_pos q Hq))
                      (real_plus
                         (real_mult (real_mult (real_opp d2_two)
                                    (real_mult p q))
                                    (real_inv_pos q Hq))
                         (real_mult (real_mult q q) (real_inv_pos q Hq))))
           (real_plus (real_mult p (real_mult p (real_inv_pos q Hq)))
                      (real_plus (real_mult d2_two (real_opp p)) q))).
  - exact HR.
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (real_mult p p) (real_inv_pos q Hq))
             (real_plus
                (real_mult (real_mult (real_opp d2_two) (real_mult p q))
                           (real_inv_pos q Hq))
                (real_mult (real_mult q q) (real_inv_pos q Hq)))
             (real_mult p (real_mult p (real_inv_pos q Hq)))
             (real_plus (real_mult d2_two (real_opp p)) q)).
    + apply real_eq_sym. apply real_mult_assoc.
    + apply (RealSetoid.real_eq_plus_compat
               (real_mult (real_mult (real_opp d2_two) (real_mult p q))
                          (real_inv_pos q Hq))
               (real_mult (real_mult q q) (real_inv_pos q Hq))
               (real_mult d2_two (real_opp p)) q).
      * exact HT3.
      * exact HT2.
Qed.

(* ---- 3. 切距超额 Bishop 非负：0 ≤_B (s−1) − log s（s := p·inv q） ---- *)
(*   单引擎：real_log_le_linear_B 于 s 处取逐项余量，平移换形闭合。     *)

Lemma dkc_E_nonneg : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q),
  real_le_b real_zero
    (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                          (real_opp real_one))
               (real_opp (real_log (real_mult p (real_inv_pos q Hq))
                                   (real_mult_positive p (real_inv_pos q Hq)
                                      Hp (real_inv_pos_pos q Hq))))).
Proof.
  intros p q Hp Hq.
  unfold real_le_b. intros e He.
  assert (HBe : real_lt (real_log (real_mult p (real_inv_pos q Hq))
                                  (real_mult_positive p (real_inv_pos q Hq) Hp
                                     (real_inv_pos_pos q Hq)))
                        (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                              (real_opp real_one)) e)).
  { exact (real_log_le_linear_B (real_mult p (real_inv_pos q Hq))
                                (real_mult_positive p (real_inv_pos q Hq) Hp
                                   (real_inv_pos_pos q Hq)) e He). }
  (* A := opp L + ((s−1) + e)；0 < A 经平移+对消，再重组至 B := (s−1) − L + e *)
  assert (Hlt0 : real_lt real_zero
                   (real_plus
                      (real_opp (real_log (real_mult p (real_inv_pos q Hq))
                                          (real_mult_positive p
                                             (real_inv_pos q Hq) Hp
                                             (real_inv_pos_pos q Hq))))
                      (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                            (real_opp real_one)) e))).
  { apply (RealSetoid.real_lt_id_l real_zero
             (real_plus
                (real_opp (real_log (real_mult p (real_inv_pos q Hq))
                                    (real_mult_positive p (real_inv_pos q Hq)
                                       Hp (real_inv_pos_pos q Hq))))
                (real_log (real_mult p (real_inv_pos q Hq))
                          (real_mult_positive p (real_inv_pos q Hq) Hp
                             (real_inv_pos_pos q Hq))))
             (real_plus
                (real_opp (real_log (real_mult p (real_inv_pos q Hq))
                                    (real_mult_positive p (real_inv_pos q Hq)
                                       Hp (real_inv_pos_pos q Hq))))
                (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                      (real_opp real_one)) e))).
    - apply real_eq_sym.
      apply (real_eq_trans
               (real_plus
                  (real_opp (real_log (real_mult p (real_inv_pos q Hq))
                                      (real_mult_positive p
                                         (real_inv_pos q Hq) Hp
                                         (real_inv_pos_pos q Hq))))
                  (real_log (real_mult p (real_inv_pos q Hq))
                            (real_mult_positive p (real_inv_pos q Hq) Hp
                               (real_inv_pos_pos q Hq))))
               (real_plus (real_log (real_mult p (real_inv_pos q Hq))
                                    (real_mult_positive p (real_inv_pos q Hq)
                                       Hp (real_inv_pos_pos q Hq)))
                          (real_opp (real_log (real_mult p
                                                 (real_inv_pos q Hq))
                                              (real_mult_positive p
                                                 (real_inv_pos q Hq) Hp
                                                 (real_inv_pos_pos q Hq)))))
               real_zero).
      + apply real_plus_comm.
      + apply real_plus_opp.
    - exact (real_lt_plus_translate
               (real_opp (real_log (real_mult p (real_inv_pos q Hq))
                                   (real_mult_positive p (real_inv_pos q Hq)
                                      Hp (real_inv_pos_pos q Hq))))
               (real_log (real_mult p (real_inv_pos q Hq))
                         (real_mult_positive p (real_inv_pos q Hq) Hp
                            (real_inv_pos_pos q Hq)))
               (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                     (real_opp real_one)) e) HBe). }
  apply (RealSetoid.real_lt_id_r real_zero
           (real_plus
              (real_opp (real_log (real_mult p (real_inv_pos q Hq))
                                  (real_mult_positive p
                                     (real_inv_pos q Hq) Hp
                                     (real_inv_pos_pos q Hq))))
              (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                    (real_opp real_one)) e))
           (real_plus (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                            (real_opp real_one))
                                 (real_opp (real_log
                                              (real_mult p
                                                 (real_inv_pos q Hq))
                                              (real_mult_positive p
                                                 (real_inv_pos q Hq) Hp
                                                 (real_inv_pos_pos q Hq)))))
                      e)).
  - apply (real_eq_trans
             (real_plus
                (real_opp (real_log (real_mult p (real_inv_pos q Hq))
                                    (real_mult_positive p
                                       (real_inv_pos q Hq) Hp
                                       (real_inv_pos_pos q Hq))))
                (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                      (real_opp real_one)) e))
             (real_plus
                (real_plus
                   (real_opp (real_log (real_mult p (real_inv_pos q Hq))
                                       (real_mult_positive p
                                          (real_inv_pos q Hq) Hp
                                          (real_inv_pos_pos q Hq))))
                   (real_plus (real_mult p (real_inv_pos q Hq))
                              (real_opp real_one)))
                e)
             (real_plus (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                              (real_opp real_one))
                                   (real_opp (real_log
                                                (real_mult p
                                                   (real_inv_pos q Hq))
                                                (real_mult_positive p
                                                   (real_inv_pos q Hq) Hp
                                                   (real_inv_pos_pos q Hq)))))
                        e)).
    + apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus
                  (real_opp (real_log (real_mult p (real_inv_pos q Hq))
                                      (real_mult_positive p
                                         (real_inv_pos q Hq) Hp
                                         (real_inv_pos_pos q Hq))))
                  (real_plus (real_mult p (real_inv_pos q Hq))
                             (real_opp real_one)))
               e
               (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                     (real_opp real_one))
                          (real_opp (real_log (real_mult p
                                                 (real_inv_pos q Hq))
                                              (real_mult_positive p
                                                 (real_inv_pos q Hq) Hp
                                                 (real_inv_pos_pos q Hq)))))
               e).
      * apply real_plus_comm.
      * apply real_eq_refl.
  - exact Hlt0.
Qed.

(* ---- 4. 逐点 gap 恒等：kl+(q−p) + p·E == (p−q)²·inv q ---- *)
(*   （kl == p·log s 经 real_kl_term_expand + dkc_log_split；          *)
(*     合项后 p·Ls 对消，余式纯环 + dkc_cs_term_expand 回代）           *)

Lemma dkc_gap_plus_E_eq : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q),
  real_eq (real_plus
             (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
             (real_mult p
                (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                      (real_opp real_one))
                           (real_opp (real_log
                                        (real_mult p (real_inv_pos q Hq))
                                        (real_mult_positive p
                                           (real_inv_pos q Hq) Hp
                                           (real_inv_pos_pos q Hq)))))))
          (real_mult (p2_tvsq p q) (real_inv_pos q Hq)).
Proof.
  intros p q Hp Hq.
  (* 原子化（序：LS 首记——仅现于非依赖位，用后清方程；次 iq——      *)
  (*   证书位已随 LS 抽象消失；末 s1=real_mult p iq 留方程作回代桥）  *)
  remember (real_log (real_mult p (real_inv_pos q Hq))
                     (real_mult_positive p (real_inv_pos q Hq) Hp
                        (real_inv_pos_pos q Hq))) as LS eqn:HeqLS.
  assert (HLS : real_eq LS
                  (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
  { rewrite HeqLS. exact (dkc_log_split p q Hp Hq). }
  clear HeqLS.
  remember (real_inv_pos q Hq) as iq eqn:Heqi.
  remember (real_mult p iq) as s1 eqn:Heqs1.
  assert (HG : real_eq
                 (real_plus (real_kl_term p q Hp Hq)
                            (real_plus q (real_opp p)))
                 (real_plus (real_mult p LS) (real_plus q (real_opp p)))).
  { apply (RealSetoid.real_eq_plus_compat (real_kl_term p q Hp Hq)
             (real_plus q (real_opp p)) (real_mult p LS)
             (real_plus q (real_opp p))).
    - apply (real_eq_trans (real_kl_term p q Hp Hq)
                           (real_mult p (real_plus (real_log p Hp)
                                                   (real_opp (real_log q Hq))))
                           (real_mult p LS)).
      + exact (real_kl_term_expand p q Hp Hq).
      + apply (RealSetoid.real_eq_mult_compat p
                 (real_plus (real_log p Hp) (real_opp (real_log q Hq))) p LS
                 (real_eq_refl p) (real_eq_sym LS
                                   (real_plus (real_log p Hp)
                                              (real_opp (real_log q Hq)))
                                   HLS)).
    - apply real_eq_refl. }
  apply (real_eq_trans
           (real_plus
              (real_plus (real_kl_term p q Hp Hq)
                         (real_plus q (real_opp p)))
              (real_mult p
                 (real_plus (real_plus s1 (real_opp real_one))
                            (real_opp LS))))
           (real_plus
              (real_plus (real_mult p LS) (real_plus q (real_opp p)))
              (real_mult p
                 (real_plus (real_plus s1 (real_opp real_one))
                            (real_opp LS))))
           (real_mult (p2_tvsq p q) iq)).
  - apply (RealSetoid.real_eq_plus_compat
             (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
             (real_mult p
                (real_plus (real_plus s1 (real_opp real_one))
                           (real_opp LS)))
             (real_plus (real_mult p LS) (real_plus q (real_opp p)))
             (real_mult p
                (real_plus (real_plus s1 (real_opp real_one))
                           (real_opp LS)))).
    + exact HG.
    + apply real_eq_refl.
  - apply (real_eq_trans
             (real_plus
                (real_plus (real_mult p LS) (real_plus q (real_opp p)))
                (real_mult p
                   (real_plus (real_plus s1 (real_opp real_one))
                              (real_opp LS))))
             (real_plus (real_mult p s1)
                        (real_plus (real_mult d2_two (real_opp p)) q))
             (real_mult (p2_tvsq p q) iq)).
    + d2_ring_eq.
    + apply real_eq_sym. rewrite Heqs1. rewrite Heqi.
      exact (dkc_cs_term_expand p q Hq).
Qed.

(* ---- 5. 逐点上臂（主件核心）：kl+(q−p) ≤_B (p−q)²·inv q ---- *)
(*   差元 == p·E 为 Bishop 非负（件 3 缩放），gap 恒等（件 4）回代。     *)

Lemma dkc_gap_le_term : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q),
  real_le_b (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
            (real_mult (p2_tvsq p q) (real_inv_pos q Hq)).
Proof.
  intros p q Hp Hq.
  unfold real_le_b. intros e He.
  assert (HE0 := dkc_E_nonneg p q Hp Hq).
  assert (HPE0 : real_le_b real_zero
                   (real_mult p
                      (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                            (real_opp real_one))
                                 (real_opp (real_log
                                              (real_mult p
                                                 (real_inv_pos q Hq))
                                              (real_mult_positive p
                                                 (real_inv_pos q Hq) Hp
                                                 (real_inv_pos_pos q Hq))))))).
  { apply (leb3_le_b_eq_l (real_mult p real_zero) real_zero
             (real_mult p
                (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                      (real_opp real_one))
                           (real_opp (real_log
                                        (real_mult p (real_inv_pos q Hq))
                                        (real_mult_positive p
                                           (real_inv_pos q Hq) Hp
                                           (real_inv_pos_pos q Hq))))))).
    - apply real_mult_zero.
    - exact (leb3_le_b_pos_scale_l real_zero
               (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                     (real_opp real_one))
                          (real_opp (real_log
                                       (real_mult p (real_inv_pos q Hq))
                                       (real_mult_positive p
                                          (real_inv_pos q Hq) Hp
                                          (real_inv_pos_pos q Hq)))))
               p HE0 Hp). }
  assert (HPEe : real_lt real_zero
                   (real_plus
                      (real_mult p
                         (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                               (real_opp real_one))
                                    (real_opp (real_log
                                                 (real_mult p
                                                    (real_inv_pos q Hq))
                                                 (real_mult_positive p
                                                    (real_inv_pos q Hq) Hp
                                                    (real_inv_pos_pos q Hq))))))
                      e)).
  { exact (HPE0 e He). }
  (* 链：gap < gap+(p·E+e)（HPEe）→ 结合换形 → 差元恒等回代 → 换形闭合 *)
  assert (HT1 : real_lt (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
                  (real_plus (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
                     (real_plus (real_mult p
                (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                      (real_opp real_one))
                           (real_opp (real_log
                                        (real_mult p (real_inv_pos q Hq))
                                        (real_mult_positive p
                                           (real_inv_pos q Hq) Hp
                                           (real_inv_pos_pos q Hq)))))) e))).
  { apply (real_lt_plus_r_zero (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
             (real_plus (real_mult p
                (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                      (real_opp real_one))
                           (real_opp (real_log
                                        (real_mult p (real_inv_pos q Hq))
                                        (real_mult_positive p
                                           (real_inv_pos q Hq) Hp
                                           (real_inv_pos_pos q Hq)))))) e) HPEe). }
  assert (HT1' : real_lt (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
                   (real_plus (real_plus (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))) (real_mult p
                (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                      (real_opp real_one))
                           (real_opp (real_log
                                        (real_mult p (real_inv_pos q Hq))
                                        (real_mult_positive p
                                           (real_inv_pos q Hq) Hp
                                           (real_inv_pos_pos q Hq))))))) e)).
  { apply (RealSetoid.real_lt_id_r (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
             (real_plus (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))) (real_plus (real_mult p
                (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                      (real_opp real_one))
                           (real_opp (real_log
                                        (real_mult p (real_inv_pos q Hq))
                                        (real_mult_positive p
                                           (real_inv_pos q Hq) Hp
                                           (real_inv_pos_pos q Hq)))))) e))
             (real_plus (real_plus (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))) (real_mult p
                (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                      (real_opp real_one))
                           (real_opp (real_log
                                        (real_mult p (real_inv_pos q Hq))
                                        (real_mult_positive p
                                           (real_inv_pos q Hq) Hp
                                           (real_inv_pos_pos q Hq))))))) e)).
    - apply real_plus_assoc.
    - exact HT1. }
  assert (HEQ : real_eq (real_plus (real_plus (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))) (real_mult p
                (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                      (real_opp real_one))
                           (real_opp (real_log
                                        (real_mult p (real_inv_pos q Hq))
                                        (real_mult_positive p
                                           (real_inv_pos q Hq) Hp
                                           (real_inv_pos_pos q Hq))))))) e)
                        (real_plus (real_mult (p2_tvsq p q) (real_inv_pos q Hq)) e)).
  { apply (RealSetoid.real_eq_plus_compat
             (real_plus (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))) (real_mult p
                (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                      (real_opp real_one))
                           (real_opp (real_log
                                        (real_mult p (real_inv_pos q Hq))
                                        (real_mult_positive p
                                           (real_inv_pos q Hq) Hp
                                           (real_inv_pos_pos q Hq))))))) e
             (real_mult (p2_tvsq p q) (real_inv_pos q Hq)) e).
    + exact (dkc_gap_plus_E_eq p q Hp Hq).
    + apply real_eq_refl. }
  apply (RealSetoid.real_lt_id_r (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
           (real_plus (real_plus (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))) (real_mult p
                (real_plus (real_plus (real_mult p (real_inv_pos q Hq))
                                      (real_opp real_one))
                           (real_opp (real_log
                                        (real_mult p (real_inv_pos q Hq))
                                        (real_mult_positive p
                                           (real_inv_pos q Hq) Hp
                                           (real_inv_pos_pos q Hq))))))) e)
           (real_plus (real_mult (p2_tvsq p q) (real_inv_pos q Hq)) e)).
  - exact HEQ.
  - exact HT1'.
Qed.

(* ---- 6. 逐点 gap 非负：0 ≤_B kl+(q−p)（klst_gap_shape 供弹） ---- *)
(*   gap == p·((x−1)−log x)（x := q·inv p），超额 E(q,p) 非负缩放。     *)

Lemma dkc_gap_nonneg : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q),
  real_le_b real_zero
    (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))).
Proof.
  intros p q Hp Hq.
  assert (HEx := dkc_E_nonneg q p Hq Hp).
  assert (HPE : real_le_b real_zero (real_mult p (real_plus (real_plus (real_mult q (real_inv_pos p Hp))
                                      (real_opp real_one))
                           (real_opp (real_log
                                        (real_mult q (real_inv_pos p Hp))
                                        (real_mult_positive q
                                           (real_inv_pos p Hp) Hq
                                           (real_inv_pos_pos p Hp))))))).
  { apply (leb3_le_b_eq_l (real_mult p real_zero) real_zero
             (real_mult p (real_plus (real_plus (real_mult q (real_inv_pos p Hp))
                                      (real_opp real_one))
                           (real_opp (real_log
                                        (real_mult q (real_inv_pos p Hp))
                                        (real_mult_positive q
                                           (real_inv_pos p Hp) Hq
                                           (real_inv_pos_pos p Hp))))))).
    - apply real_mult_zero.
    - exact (leb3_le_b_pos_scale_l real_zero (real_plus (real_plus (real_mult q (real_inv_pos p Hp))
                                      (real_opp real_one))
                           (real_opp (real_log
                                        (real_mult q (real_inv_pos p Hp))
                                        (real_mult_positive q
                                           (real_inv_pos p Hp) Hq
                                           (real_inv_pos_pos p Hp))))) p HEx Hp). }
  apply (leb3_le_b_eq_r real_zero (real_mult p (real_plus (real_plus (real_mult q (real_inv_pos p Hp))
                                      (real_opp real_one))
                           (real_opp (real_log
                                        (real_mult q (real_inv_pos p Hp))
                                        (real_mult_positive q
                                           (real_inv_pos p Hp) Hq
                                           (real_inv_pos_pos p Hp)))))) (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))).
  - exact HPE.
  - apply real_eq_sym. exact (klst_gap_shape p q Hp Hq).
Qed.

(* ---- 7. KL₂ 与双 gap 的归一化恒等（kl 原子环闭） ---- *)

Lemma dkc_kl2_eq_gaps : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_eq (p2_kl2 p q Hp Hq Hp1 Hq1)
          (real_plus
             (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
             (real_plus
                (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                (real_plus (p2_one_minus q)
                           (real_opp (p2_one_minus p))))).
Proof.
  intros p q Hp Hq Hp1 Hq1. unfold p2_kl2.
  remember (real_kl_term p q Hp Hq) as K1.
  remember (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) as K2.
  d2_ring_eq.
Qed.

(* ---- 8. 主件：KL₂ ≤_B χ²（两点，Bishop 形出口，零 Or 分支） ---- *)

Theorem dkc_kl2_le_cs : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_le_b (p2_kl2 p q Hp Hq Hp1 Hq1) (div2_cs p q Hq Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1.
  assert (T1 := dkc_gap_le_term p q Hp Hq).
  assert (T2 := dkc_gap_le_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1).
  assert (T2' : real_le_b
                  (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                        Hp1 Hq1)
                             (real_plus (p2_one_minus q)
                                        (real_opp (p2_one_minus p))))
                  (real_mult (p2_tvsq p q)
                             (real_inv_pos (p2_one_minus q) Hq1))).
  { apply (leb3_le_b_eq_r
             (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                    Hp1 Hq1)
                        (real_plus (p2_one_minus q)
                                   (real_opp (p2_one_minus p))))
             (real_mult (p2_tvsq (p2_one_minus p) (p2_one_minus q))
                        (real_inv_pos (p2_one_minus q) Hq1))
             (real_mult (p2_tvsq p q)
                        (real_inv_pos (p2_one_minus q) Hq1))).
    - exact T2.
    - apply (RealSetoid.real_eq_mult_compat
               (p2_tvsq (p2_one_minus p) (p2_one_minus q))
               (real_inv_pos (p2_one_minus q) Hq1)
               (p2_tvsq p q)
               (real_inv_pos (p2_one_minus q) Hq1)).
      + d2_ring_eq.
      + apply real_eq_refl. }
  apply (leb3_le_b_eq_l
           (real_plus
              (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
              (real_plus
                 (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                 (real_plus (p2_one_minus q)
                            (real_opp (p2_one_minus p)))))
           (p2_kl2 p q Hp Hq Hp1 Hq1)
           (div2_cs p q Hq Hq1)).
  - apply real_eq_sym. exact (dkc_kl2_eq_gaps p q Hp Hq Hp1 Hq1).
  - exact (real_le_b_plus_compat
             (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
             (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
             (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                  Hp1 Hq1)
                        (real_plus (p2_one_minus q)
                                   (real_opp (p2_one_minus p))))
             (real_mult (p2_tvsq p q)
                        (real_inv_pos (p2_one_minus q) Hq1)) T1 T2').
Qed.

(* ---- 9. 推论 A（下臂链）：四·TV² ≤_B KL₂（Pinsker 阶梯上界新阶供弹） ---- *)

(* ---- 9. 推论 A（eps 形出口）：KL₂ < χ²+eps 逐 eps 显式形 ---- *)
(*   （real_le_b 的定义展开形；Hne 版严格下臂 TV²≤_B KL₂ 已在树       *)
(*     pnk2_pinsker_one，本件不重列；四·TV²≤_B χ² 见件 1c。）          *)

Theorem dkc_kl2_le_cs_eps : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (eps : Real) (Heps : real_lt real_zero eps),
  real_lt (p2_kl2 p q Hp Hq Hp1 Hq1) (real_plus (div2_cs p q Hq Hq1) eps).
Proof.
  intros p q Hp Hq Hp1 Hq1 eps Heps.
  exact (dkc_kl2_le_cs p q Hp Hq Hp1 Hq1 eps Heps).
Qed.

(* ---- 10. pnt 运输互认：p2_kl2 == pnt_kl2（逐字同构副本，禁第四别名） ---- *)

Lemma dkc_kl2_pnt_eq : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_eq (p2_kl2 p q Hp Hq Hp1 Hq1) (pnt_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1.
  unfold p2_kl2, pnt_kl2, p2_one_minus, pnt_one_minus.
  apply real_eq_refl.
Qed.

(* ---- 11. 推论 B（等号侧）：χ²==0 ⟹ KL₂==0 ---- *)
(*   路线：KL₂ ≤_B χ==0（主件+eq 换形）∧ 0 ≤_B KL₂（双 gap 非负求和）   *)
(*   ⟹ Bishop 反对称（gibbe2_le_b_antisym，逐 n 构造零 Or）闭合。       *)

Theorem dkc_kl2_zero_of_cs_zero : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hcs : real_eq (div2_cs p q Hq Hq1) real_zero),
  real_eq (p2_kl2 p q Hp Hq Hp1 Hq1) real_zero.
Proof.
  intros p q Hp Hq Hp1 Hq1 Hcs.
  assert (H1 := dkc_gap_nonneg p q Hp Hq).
  assert (H2 := dkc_gap_nonneg (p2_one_minus p) (p2_one_minus q) Hp1 Hq1).
  assert (Hge : real_le_b real_zero (p2_kl2 p q Hp Hq Hp1 Hq1)).
  { apply (leb3_le_b_eq_r real_zero
             (real_plus
                (real_plus (real_kl_term p q Hp Hq)
                           (real_plus q (real_opp p)))
                (real_plus
                   (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                   (real_plus (p2_one_minus q)
                              (real_opp (p2_one_minus p)))))
             (p2_kl2 p q Hp Hq Hp1 Hq1)).
    - apply (leb3_le_b_eq_l
               (real_plus real_zero real_zero)
               real_zero
               (real_plus
                  (real_plus (real_kl_term p q Hp Hq)
                             (real_plus q (real_opp p)))
                  (real_plus
                     (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                     (real_plus (p2_one_minus q)
                                (real_opp (p2_one_minus p)))))).
      + apply real_plus_zero.
      + exact (real_le_b_plus_compat real_zero
                  (real_plus (real_kl_term p q Hp Hq)
                             (real_plus q (real_opp p)))
                  real_zero
                  (real_plus
                     (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                     (real_plus (p2_one_minus q)
                                (real_opp (p2_one_minus p)))) H1 H2).
    - apply real_eq_sym. exact (dkc_kl2_eq_gaps p q Hp Hq Hp1 Hq1). }
  assert (Hle : real_le_b (p2_kl2 p q Hp Hq Hp1 Hq1) real_zero).
  { apply (leb3_le_b_eq_r (p2_kl2 p q Hp Hq Hp1 Hq1)
             (div2_cs p q Hq Hq1) real_zero).
    - exact (dkc_kl2_le_cs p q Hp Hq Hp1 Hq1).
    - exact Hcs. }
  exact (gibbe2_le_b_antisym (p2_kl2 p q Hp Hq Hp1 Hq1) real_zero Hle Hge).
Qed.

(* ---- 12. 推论 C（KL>0 供弹位·χ 侧）：差异 ⟹ 0 < χ² ---- *)
(*   KL>0 生产器=在树 p2_kl2_pos（Or 前提形），本件不重列不另建；        *)
(*   此处新供给同证书下的 χ>0 侧，并给 sigT 配对形供 deficit 面转接。    *)

Theorem dkc_cs_pos_of_ne : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hne : Or (real_lt p q) (real_lt q p)),
  real_lt real_zero (div2_cs p q Hq Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hne. destruct Hne as [Hpq | Hqp].
  - assert (Hdp : real_lt real_zero (p2_diff q p))
      by exact (p2_diff_pos_of_lt p q Hpq).
    assert (HTV : real_lt real_zero (p2_tvsq p q)).
    { apply (RealSetoid.real_lt_id_r real_zero
               (real_mult (p2_diff q p) (p2_diff q p)) (p2_tvsq p q)).
      - d2_ring_eq.
      - exact (real_mult_positive (p2_diff q p) (p2_diff q p) Hdp Hdp). }
    apply (RealSetoid.real_lt_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus
                (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                (real_mult (p2_tvsq p q)
                           (real_inv_pos (p2_one_minus q) Hq1)))).
      + exact (real_eq_sym (real_plus real_zero real_zero) real_zero
                 (real_plus_zero real_zero)).
      + exact (real_lt_plus_compat real_zero
                  (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                  real_zero
                  (real_mult (p2_tvsq p q)
                             (real_inv_pos (p2_one_minus q) Hq1))
                  (real_mult_positive (p2_tvsq p q) (real_inv_pos q Hq) HTV
                     (real_inv_pos_pos q Hq))
                  (real_mult_positive (p2_tvsq p q)
                     (real_inv_pos (p2_one_minus q) Hq1) HTV
                     (real_inv_pos_pos (p2_one_minus q) Hq1))).
  - assert (Hdp : real_lt real_zero (p2_diff p q))
      by exact (p2_diff_pos_of_lt q p Hqp).
    assert (HTV : real_lt real_zero (p2_tvsq p q)).
    { exact (real_mult_positive (p2_diff p q) (p2_diff p q) Hdp Hdp). }
    apply (RealSetoid.real_lt_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus
                (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                (real_mult (p2_tvsq p q)
                           (real_inv_pos (p2_one_minus q) Hq1)))).
      + exact (real_eq_sym (real_plus real_zero real_zero) real_zero
                 (real_plus_zero real_zero)).
      + exact (real_lt_plus_compat real_zero
                  (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                  real_zero
                  (real_mult (p2_tvsq p q)
                             (real_inv_pos (p2_one_minus q) Hq1))
                  (real_mult_positive (p2_tvsq p q) (real_inv_pos q Hq) HTV
                     (real_inv_pos_pos q Hq))
                  (real_mult_positive (p2_tvsq p q)
                     (real_inv_pos (p2_one_minus q) Hq1) HTV
                     (real_inv_pos_pos (p2_one_minus q) Hq1))).
Qed.

(* 配对形（sigT，Set 层）：差异 ⟹ 0 < KL₂ ∧ 0 < χ² 同证书随行 *)
Definition dkc_pos_pair_of_ne : Set :=
  forall (p q : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
    (Hp1 : real_lt real_zero (p2_one_minus p))
    (Hq1 : real_lt real_zero (p2_one_minus q))
    (Hne : Or (real_lt p q) (real_lt q p)),
    sigT (fun _ : real_lt real_zero (p2_kl2 p q Hp Hq Hp1 Hq1) =>
          real_lt real_zero (div2_cs p q Hq Hq1)).

Lemma dkc_pos_pair_of_ne_def : dkc_pos_pair_of_ne.
Proof.
  intros p q Hp Hq Hp1 Hq1 Hne.
  exact (existT
           (fun _ : real_lt real_zero (p2_kl2 p q Hp Hq Hp1 Hq1) =>
            real_lt real_zero (div2_cs p q Hq Hq1))
           (p2_kl2_pos p q Hp Hq Hp1 Hq1 Hne)
           (dkc_cs_pos_of_ne p q Hp Hq Hp1 Hq1 Hne)).
Qed.

(* ---- 99. 尾检 ---- *)
Print Assumptions dkc_kl2_le_cs.
Print Assumptions dkc_kl2_le_cs_eps.
Print Assumptions dkc_kl2_pnt_eq.
Print Assumptions dkc_kl2_zero_of_cs_zero.
Print Assumptions dkc_cs_pos_of_ne.
Print Assumptions dkc_pos_pair_of_ne_def.
