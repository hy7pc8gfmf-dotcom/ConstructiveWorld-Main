(* ============================================================ *)
(* abl_div_hellinger_twopoint.v                                   *)
(* 模块名：abl_div_hellinger_twopoint                              *)
(* 数学使命：两点分布 Hellinger² ≤ KL₂ 见证形（f-散度海峡成桥接件单     *)
(*   第 3 件）——H² := (√p−√q)²+(√(1−p)−√(1−q))² 以四正 witness      *)
(*   (sp,sq,sp1,sq1)（平方方程+正性证书随件）承载，亲核 Σ√(pᵢqᵢ)      *)
(*   用 sp·sq 多项式形（见证乘法免二次开方：√(pq) 直接取 sp·sq，     *)
(*   (sp·sq)²=sp²·sq²=pq 环闭合）。主件 dhe_h2_le_kl2 路线：        *)
(*   log_le_linear 于根比 t:=sq·inv(sp) 处 ⟹ 1−t ≤ −log t，乘 p     *)
(*   求和得 KL₂ ≥ 2(1−Σ√pq) = H²（逐点 gap ≥ (√x−√y)²）；配套       *)
(*   log 方根替换桥（real_log_wd）、见证乘法闭合（real_inv_unique）、  *)
(*   kl 的二倍根比分 liar 恒等、pnt 运输互认、eps 形出口、Bishop 非负、  *)
(*   等号侧（KL₂==0⟹H²==0）、sqrt 见证提取供弹位（AttnSqrt）与        *)
(*   四见证封装推论。                                                *)
(* 依赖清单：件 1 abl_div_chisq_twopoint（d2_two/d2_two_pos/d2_ring_eq）*)
(*   +件 2 abl_div_kl_chisq_twopoint（dkc_kl2_eq_gaps/dkc_kl2_pnt_eq）, *)
(*   PinskerTwoPoint（p2_tvsq/p2_diff/p2_one_minus/p2_kl2）、        *)
(*   S03/S07/S08（inv/log 基座：real_log_mult/real_log_wd/           *)
(*   real_inv_unique/real_inv_pos_correct）、UpRealLeB（real_le_b/    *)
(*   real_log_le_linear_B/real_square_nonneg_B）、UpRealLeB2（和兼容）、  *)
(*   UpRealLeB3（leb3_eq_l/eq_r/opp_rev/pos_scale_l）、G08_Gibbs       *)
(*   （gibbe2_le_b_antisym 等号侧）、UpReqPinskerTransport（pnt_kl2）、   *)
(*   UpReqTrainingEquiv（real_log_inv_pos_opp）、AttnSqrt              *)
(*   （real_sqrt_exists 见证提取）。                                  *)
(* 构造性注记：全件 Set 层出口；非严格序一律 Bishop 形 real_le_b（零 Or  *)
(*   形出口）；inv 证书逐点穿线（real_inv_pos 证书位显式随行）；        *)
(*   零承认式语句、零经典公理、全部 Qed 闭合。                        *)
(* 编译配方：                                                       *)
(*   source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&        *)
(*   ulimit -s 65532 && cd <池> && nice -19 rocq c -native-compiler  *)
(*   no -Q <缓存根> "" abl_div_hellinger_twopoint.v                   *)
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
Require Import G08_Gibbs.
Require Import UpReqPinskerTransport.
Require Import UpReqTrainingEquiv.
Require Import AttnSqrt.
Require Import abl_div_chisq_twopoint.
Require Import abl_div_kl_chisq_twopoint.

(* ---- 1. 载件定义：H² := (√p−√q)² + (√(1−p)−√(1−q))²（见证形） ---- *)
(*   sp²==p、sq²==q、sp1²==1−p、sq1²==1−q 四见证随件（定理证书位）；   *)
(*   亲核 Σ√(pᵢqᵢ) 不出现——p2_tvsq sp sq 即 (√p−√q)² 本身。          *)

Definition dhe_h2 (p q sp sq sp1 sq1 : Real) : Real :=
  real_plus (p2_tvsq sp sq) (p2_tvsq sp1 sq1).

(* ---- 1b. 纯环重组小件：(a·b)·(c·j) == (a·c)·(b·j) ---- *)
(*   （全变量形：环闭原子位避开证书依赖位的 remember 阻断——            *)
(*     调用位以 real_inv_pos 项直取代 j，环内 j 为不透明变量）           *)

Lemma dhe_ring_shuffle4 : forall (a b c j : Real),
  real_eq (real_mult (real_mult a b) (real_mult c j))
          (real_mult (real_mult a c) (real_mult b j)).
Proof.
  intros a b c j. d2_ring_eq.
Qed.

(* ---- 2. log 方根替换桥：x == s·s ⟹ log x == log s + log s ---- *)
(*   （real_log_wd 证书桥 + real_log_mult； witnesses 替换的钥匙件）    *)

Lemma dhe_log_sq : forall (x s : Real) (Hx : real_lt real_zero x)
  (Hs : real_lt real_zero s) (Hse : real_eq (real_mult s s) x),
  real_eq (real_log x Hx)
          (real_plus (real_log s Hs) (real_log s Hs)).
Proof.
  intros x s Hx Hs Hse.
  apply (real_eq_trans (real_log x Hx)
           (real_log (real_mult s s) (real_mult_positive s s Hs Hs))
           (real_plus (real_log s Hs) (real_log s Hs))).
  - exact (real_log_wd x (real_mult s s) Hx
             (real_mult_positive s s Hs Hs)
             (real_eq_sym (real_mult s s) x Hse)).
  - exact (real_log_mult s s Hs Hs).
Qed.

(* ---- 3. 见证乘法闭合：q·inv(p) == (sq·inv(sp))·(sq·inv(sp)) ---- *)
(*   （sp²==p、sq²==q 的环闭合：inv 唯一性 real_inv_unique 闭合——      *)
(*     inv(p) == inv(sp)·inv(sp)，乘 q 后纯环重组；免二次开方的核心）   *)

Lemma dhe_wit_ratio_sq : forall (p q sp sq : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hsp : real_lt real_zero sp) (Hsq : real_lt real_zero sq)
  (Hspe : real_eq (real_mult sp sp) p) (Hsqe : real_eq (real_mult sq sq) q),
  real_eq (real_mult q (real_inv_pos p Hp))
          (real_mult (real_mult sq (real_inv_pos sp Hsp))
                     (real_mult sq (real_inv_pos sp Hsp))).
Proof.
  intros p q sp sq Hp Hq Hsp Hsq Hspe Hsqe.
  assert (H1 : real_eq (real_mult p (real_inv_pos p Hp)) real_one)
    by exact (real_inv_pos_correct p Hp).
  assert (HJ : real_eq (real_mult sp (real_inv_pos sp Hsp)) real_one)
    by exact (real_inv_pos_correct sp Hsp).
  (* p·(inv sp·inv sp) == 1：(sp·sp)·(j·j) == (sp·j)·(sp·j) == 1·1 == 1 *)
  assert (H2 : real_eq (real_mult p
                          (real_mult (real_inv_pos sp Hsp)
                                     (real_inv_pos sp Hsp)))
                       real_one).
  { apply (real_eq_trans _
             (real_mult (real_mult sp sp)
                        (real_mult (real_inv_pos sp Hsp)
                                   (real_inv_pos sp Hsp)))
             real_one).
    - apply (RealSetoid.real_eq_mult_compat p
               (real_mult (real_inv_pos sp Hsp) (real_inv_pos sp Hsp))
               (real_mult sp sp)
               (real_mult (real_inv_pos sp Hsp) (real_inv_pos sp Hsp))).
      + apply real_eq_sym. exact Hspe.
      + apply real_eq_refl.
    - apply (real_eq_trans
               (real_mult (real_mult sp sp)
                          (real_mult (real_inv_pos sp Hsp)
                                     (real_inv_pos sp Hsp)))
               (real_mult (real_mult sp (real_inv_pos sp Hsp))
                          (real_mult sp (real_inv_pos sp Hsp)))
               real_one).
      + remember (real_inv_pos sp Hsp) as j. d2_ring_eq.
      + apply (real_eq_trans
                 (real_mult (real_mult sp (real_inv_pos sp Hsp))
                            (real_mult sp (real_inv_pos sp Hsp)))
                 (real_mult real_one real_one) real_one).
        * apply (RealSetoid.real_eq_mult_compat
                   (real_mult sp (real_inv_pos sp Hsp))
                   (real_mult sp (real_inv_pos sp Hsp))
                   real_one real_one).
          -- exact HJ.
          -- exact HJ.
        * apply real_mult_one. }
  (* inv 唯一性：inv(p) == inv(sp)·inv(sp) *)
  assert (HIJ : real_eq (real_inv_pos p Hp)
                        (real_mult (real_inv_pos sp Hsp)
                                   (real_inv_pos sp Hsp))).
  { exact (real_inv_unique p (real_inv_pos p Hp)
             (real_mult (real_inv_pos sp Hsp) (real_inv_pos sp Hsp))
             H1 H2). }
  (* 主式：q·inv(p) == q·(j·j) == (sq·sq)·(j·j) == (sq·j)·(sq·j) *)
  apply (real_eq_trans
           (real_mult q (real_inv_pos p Hp))
           (real_mult q (real_mult (real_inv_pos sp Hsp)
                                   (real_inv_pos sp Hsp)))
           (real_mult (real_mult sq (real_inv_pos sp Hsp))
                      (real_mult sq (real_inv_pos sp Hsp)))).
  - apply (RealSetoid.real_eq_mult_compat q (real_inv_pos p Hp) q
             (real_mult (real_inv_pos sp Hsp) (real_inv_pos sp Hsp))).
    + apply real_eq_refl.
    + exact HIJ.
  - apply (real_eq_trans
             (real_mult q (real_mult (real_inv_pos sp Hsp)
                                     (real_inv_pos sp Hsp)))
             (real_mult (real_mult sq sq)
                        (real_mult (real_inv_pos sp Hsp)
                                   (real_inv_pos sp Hsp)))
             (real_mult (real_mult sq (real_inv_pos sp Hsp))
                        (real_mult sq (real_inv_pos sp Hsp)))).
    + apply (RealSetoid.real_eq_mult_compat q
               (real_mult (real_inv_pos sp Hsp) (real_inv_pos sp Hsp))
               (real_mult sq sq)
               (real_mult (real_inv_pos sp Hsp) (real_inv_pos sp Hsp))).
      * apply real_eq_sym. exact Hsqe.
      * apply real_eq_refl.
    + remember (real_inv_pos sp Hsp) as j. d2_ring_eq.
Qed.

(* ---- 4. log 比值二倍形：log(q/p) == L + L（L := log(√q/√p)） ---- *)
(*   （log(q·inv p) == log q − log p == 2M−2K 环闭；L+L == 2(M−K)）    *)

Lemma dhe_log_ratio_double : forall (p q sp sq : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hsp : real_lt real_zero sp) (Hsq : real_lt real_zero sq)
  (Hspe : real_eq (real_mult sp sp) p) (Hsqe : real_eq (real_mult sq sq) q),
  real_eq (real_log (real_mult q (real_inv_pos p Hp))
                    (real_mult_positive q (real_inv_pos p Hp) Hq
                       (real_inv_pos_pos p Hp)))
          (real_plus (real_log (real_mult sq (real_inv_pos sp Hsp))
                               (real_mult_positive sq (real_inv_pos sp Hsp)
                                  Hsq (real_inv_pos_pos sp Hsp)))
                     (real_log (real_mult sq (real_inv_pos sp Hsp))
                               (real_mult_positive sq (real_inv_pos sp Hsp)
                                  Hsq (real_inv_pos_pos sp Hsp)))).
Proof.
  intros p q sp sq Hp Hq Hsp Hsq Hspe Hsqe.
  assert (HL : real_eq (real_log (real_mult sq (real_inv_pos sp Hsp))
                                 (real_mult_positive sq (real_inv_pos sp Hsp)
                                    Hsq (real_inv_pos_pos sp Hsp)))
                       (real_plus (real_log sq Hsq)
                                  (real_opp (real_log sp Hsp)))).
  { apply (real_eq_trans
             (real_log (real_mult sq (real_inv_pos sp Hsp))
                       (real_mult_positive sq (real_inv_pos sp Hsp)
                          Hsq (real_inv_pos_pos sp Hsp)))
             (real_plus (real_log sq Hsq)
                        (real_log (real_inv_pos sp Hsp)
                                  (real_inv_pos_pos sp Hsp)))
             (real_plus (real_log sq Hsq) (real_opp (real_log sp Hsp)))).
    - exact (real_log_mult sq (real_inv_pos sp Hsp) Hsq
               (real_inv_pos_pos sp Hsp)).
    - apply (RealSetoid.real_eq_plus_compat (real_log sq Hsq)
               (real_log (real_inv_pos sp Hsp) (real_inv_pos_pos sp Hsp))
               (real_log sq Hsq) (real_opp (real_log sp Hsp))
               (real_eq_refl (real_log sq Hsq))
               (real_log_inv_pos_opp sp Hsp)). }
  apply (real_eq_trans
           (real_log (real_mult q (real_inv_pos p Hp))
                     (real_mult_positive q (real_inv_pos p Hp) Hq
                        (real_inv_pos_pos p Hp)))
           (real_plus (real_plus (real_log sq Hsq) (real_log sq Hsq))
                      (real_opp (real_plus (real_log sp Hsp)
                                           (real_log sp Hsp))))
           (real_plus (real_log (real_mult sq (real_inv_pos sp Hsp))
                                (real_mult_positive sq (real_inv_pos sp Hsp)
                                   Hsq (real_inv_pos_pos sp Hsp)))
                      (real_log (real_mult sq (real_inv_pos sp Hsp))
                                (real_mult_positive sq (real_inv_pos sp Hsp)
                                   Hsq (real_inv_pos_pos sp Hsp))))).
  - apply (real_eq_trans
             (real_log (real_mult q (real_inv_pos p Hp))
                       (real_mult_positive q (real_inv_pos p Hp) Hq
                          (real_inv_pos_pos p Hp)))
             (real_plus (real_log q Hq)
                        (real_log (real_inv_pos p Hp)
                                  (real_inv_pos_pos p Hp)))
             (real_plus (real_plus (real_log sq Hsq) (real_log sq Hsq))
                        (real_opp (real_plus (real_log sp Hsp)
                                             (real_log sp Hsp))))).
    + exact (real_log_mult q (real_inv_pos p Hp) Hq
               (real_inv_pos_pos p Hp)).
    + apply (RealSetoid.real_eq_plus_compat (real_log q Hq)
               (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp))
               (real_plus (real_log sq Hsq) (real_log sq Hsq))
               (real_opp (real_plus (real_log sp Hsp) (real_log sp Hsp)))).
      * exact (dhe_log_sq q sq Hq Hsq Hsqe).
      * apply (real_eq_trans
                 (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp))
                 (real_opp (real_log p Hp))
                 (real_opp (real_plus (real_log sp Hsp) (real_log sp Hsp)))).
        -- exact (real_log_inv_pos_opp p Hp).
        -- apply (RealSetoid.real_eq_opp_compat (real_log p Hp)
                     (real_plus (real_log sp Hsp) (real_log sp Hsp))).
           exact (dhe_log_sq p sp Hp Hsp Hspe).
  - apply (real_eq_trans
             (real_plus (real_plus (real_log sq Hsq) (real_log sq Hsq))
                        (real_opp (real_plus (real_log sp Hsp)
                                             (real_log sp Hsp))))
             (real_plus (real_plus (real_log sq Hsq)
                                   (real_opp (real_log sp Hsp)))
                        (real_plus (real_log sq Hsq)
                                   (real_opp (real_log sp Hsp))))
             (real_plus (real_log (real_mult sq (real_inv_pos sp Hsp))
                                  (real_mult_positive sq
                                     (real_inv_pos sp Hsp) Hsq
                                     (real_inv_pos_pos sp Hsp)))
                        (real_log (real_mult sq (real_inv_pos sp Hsp))
                                  (real_mult_positive sq
                                     (real_inv_pos sp Hsp) Hsq
                                     (real_inv_pos_pos sp Hsp))))).
    + remember (real_log sq Hsq) as M.
      remember (real_log sp Hsp) as K.
      d2_ring_eq.
    + apply real_eq_sym.
      apply (RealSetoid.real_eq_plus_compat
               (real_log (real_mult sq (real_inv_pos sp Hsp))
                         (real_mult_positive sq (real_inv_pos sp Hsp)
                            Hsq (real_inv_pos_pos sp Hsp)))
               (real_log (real_mult sq (real_inv_pos sp Hsp))
                         (real_mult_positive sq (real_inv_pos sp Hsp)
                            Hsq (real_inv_pos_pos sp Hsp)))
               (real_plus (real_log sq Hsq) (real_opp (real_log sp Hsp)))
               (real_plus (real_log sq Hsq) (real_opp (real_log sp Hsp)))
               HL HL).
Qed.

(* ---- 5. kl 的二倍根比恒等：kl == 贰·p·(−L)（主桥换形件） ---- *)

Lemma dhe_kl_twoL : forall (p q sp sq : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hsp : real_lt real_zero sp) (Hsq : real_lt real_zero sq)
  (Hspe : real_eq (real_mult sp sp) p) (Hsqe : real_eq (real_mult sq sq) q),
  real_eq (real_kl_term p q Hp Hq)
          (real_mult d2_two
             (real_mult p (real_opp
                (real_log (real_mult sq (real_inv_pos sp Hsp))
                          (real_mult_positive sq (real_inv_pos sp Hsp)
                             Hsq (real_inv_pos_pos sp Hsp)))))).
Proof.
  intros p q sp sq Hp Hq Hsp Hsq Hspe Hsqe.
  assert (HLD : real_eq (real_log (real_mult q (real_inv_pos p Hp))
                                  (real_mult_positive q (real_inv_pos p Hp)
                                     Hq (real_inv_pos_pos p Hp)))
                        (real_plus (real_log (real_mult sq
                                                (real_inv_pos sp Hsp))
                                             (real_mult_positive sq
                                                (real_inv_pos sp Hsp) Hsq
                                                (real_inv_pos_pos sp Hsp)))
                                   (real_log (real_mult sq
                                                (real_inv_pos sp Hsp))
                                             (real_mult_positive sq
                                                (real_inv_pos sp Hsp) Hsq
                                                (real_inv_pos_pos sp Hsp)))))
    by exact (dhe_log_ratio_double p q sp sq Hp Hq Hsp Hsq Hspe Hsqe).
  assert (Hneg : real_eq
                   (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                       (real_mult_positive q
                                          (real_inv_pos p Hp) Hq
                                          (real_inv_pos_pos p Hp))))
                   (real_plus
                      (real_opp (real_log (real_mult sq
                                             (real_inv_pos sp Hsp))
                                          (real_mult_positive sq
                                             (real_inv_pos sp Hsp) Hsq
                                             (real_inv_pos_pos sp Hsp))))
                      (real_opp (real_log (real_mult sq
                                             (real_inv_pos sp Hsp))
                                          (real_mult_positive sq
                                             (real_inv_pos sp Hsp) Hsq
                                             (real_inv_pos_pos sp Hsp)))))).
  { apply (real_eq_trans _
             (real_opp (real_plus
                          (real_log (real_mult sq (real_inv_pos sp Hsp))
                                    (real_mult_positive sq
                                       (real_inv_pos sp Hsp) Hsq
                                       (real_inv_pos_pos sp Hsp)))
                          (real_log (real_mult sq (real_inv_pos sp Hsp))
                                    (real_mult_positive sq
                                       (real_inv_pos sp Hsp) Hsq
                                       (real_inv_pos_pos sp Hsp))))) _).
    - exact (RealSetoid.real_eq_opp_compat _ _ HLD).
    - exact (real_opp_plus (real_log (real_mult sq (real_inv_pos sp Hsp))
                                     (real_mult_positive sq
                                        (real_inv_pos sp Hsp) Hsq
                                        (real_inv_pos_pos sp Hsp)))
                           (real_log (real_mult sq (real_inv_pos sp Hsp))
                                     (real_mult_positive sq
                                        (real_inv_pos sp Hsp) Hsq
                                        (real_inv_pos_pos sp Hsp)))). }
  unfold real_kl_term.
  apply (real_eq_trans
           (real_mult p (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                (real_mult_positive q (real_inv_pos p Hp) Hq
                                   (real_inv_pos_pos p Hp)))))
           (real_mult p
              (real_plus
                 (real_opp (real_log (real_mult sq (real_inv_pos sp Hsp))
                                     (real_mult_positive sq
                                        (real_inv_pos sp Hsp) Hsq
                                        (real_inv_pos_pos sp Hsp))))
                 (real_opp (real_log (real_mult sq (real_inv_pos sp Hsp))
                                     (real_mult_positive sq
                                        (real_inv_pos sp Hsp) Hsq
                                        (real_inv_pos_pos sp Hsp))))))
           (real_mult d2_two
              (real_mult p (real_opp
                 (real_log (real_mult sq (real_inv_pos sp Hsp))
                           (real_mult_positive sq (real_inv_pos sp Hsp)
                              Hsq (real_inv_pos_pos sp Hsp))))))).
  - apply (RealSetoid.real_eq_mult_compat p
             (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                 (real_mult_positive q (real_inv_pos p Hp)
                                    Hq (real_inv_pos_pos p Hp))))
             p
             (real_plus
                (real_opp (real_log (real_mult sq (real_inv_pos sp Hsp))
                                    (real_mult_positive sq
                                       (real_inv_pos sp Hsp) Hsq
                                       (real_inv_pos_pos sp Hsp))))
                (real_opp (real_log (real_mult sq (real_inv_pos sp Hsp))
                                    (real_mult_positive sq
                                       (real_inv_pos sp Hsp) Hsq
                                       (real_inv_pos_pos sp Hsp)))))).
    + apply real_eq_refl.
    + exact Hneg.
  - apply (real_eq_trans
             (real_mult p
                (real_plus
                   (real_opp (real_log (real_mult sq (real_inv_pos sp Hsp))
                                       (real_mult_positive sq
                                          (real_inv_pos sp Hsp) Hsq
                                          (real_inv_pos_pos sp Hsp))))
                   (real_opp (real_log (real_mult sq (real_inv_pos sp Hsp))
                                       (real_mult_positive sq
                                          (real_inv_pos sp Hsp) Hsq
                                          (real_inv_pos_pos sp Hsp))))))
             (real_plus
                (real_mult p (real_opp (real_log (real_mult sq
                                                    (real_inv_pos sp Hsp))
                                                  (real_mult_positive sq
                                                     (real_inv_pos sp Hsp)
                                                     Hsq
                                                     (real_inv_pos_pos sp Hsp)))))
                (real_mult p (real_opp (real_log (real_mult sq
                                                    (real_inv_pos sp Hsp))
                                                  (real_mult_positive sq
                                                     (real_inv_pos sp Hsp)
                                                     Hsq
                                                     (real_inv_pos_pos sp Hsp))))))
             (real_mult d2_two
                (real_mult p (real_opp
                   (real_log (real_mult sq (real_inv_pos sp Hsp))
                             (real_mult_positive sq (real_inv_pos sp Hsp)
                                Hsq (real_inv_pos_pos sp Hsp))))))).
    + exact (real_distrib p (real_opp (real_log (real_mult sq
                             (real_inv_pos sp Hsp))
                             (real_mult_positive sq (real_inv_pos sp Hsp)
                                Hsq (real_inv_pos_pos sp Hsp))))
               (real_opp (real_log (real_mult sq (real_inv_pos sp Hsp))
                                   (real_mult_positive sq
                                      (real_inv_pos sp Hsp) Hsq
                                      (real_inv_pos_pos sp Hsp))))).
    + exact (d2_double (real_mult p (real_opp
               (real_log (real_mult sq (real_inv_pos sp Hsp))
                         (real_mult_positive sq (real_inv_pos sp Hsp)
                            Hsq (real_inv_pos_pos sp Hsp)))))).
Qed.

(* ---- 6. H 项展开：(sp−sq)² == p + q − 贰·(sp·sq)（见证平方回代） ---- *)

Lemma dhe_h2_term_expand : forall (p q sp sq : Real)
  (Hspe : real_eq (real_mult sp sp) p) (Hsqe : real_eq (real_mult sq sq) q),
  real_eq (p2_tvsq sp sq)
          (real_plus (real_plus p q)
                     (real_opp (real_mult d2_two (real_mult sp sq)))).
Proof.
  intros p q sp sq Hspe Hsqe.
  apply (real_eq_trans (p2_tvsq sp sq)
           (real_plus (real_mult sp sp)
                      (real_plus (real_mult sq sq)
                                 (real_mult (real_opp d2_two)
                                            (real_mult sp sq))))
           (real_plus (real_plus p q)
                      (real_opp (real_mult d2_two (real_mult sp sq))))).
  - d2_ring_eq.
  - apply (real_eq_trans
             (real_plus (real_mult sp sp)
                        (real_plus (real_mult sq sq)
                                   (real_mult (real_opp d2_two)
                                              (real_mult sp sq))))
             (real_plus (real_plus (real_mult sp sp) (real_mult sq sq))
                        (real_mult (real_opp d2_two) (real_mult sp sq)))
             (real_plus (real_plus p q)
                        (real_opp (real_mult d2_two (real_mult sp sq))))).
    + apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_mult sp sp) (real_mult sq sq))
               (real_mult (real_opp d2_two) (real_mult sp sq))
               (real_plus p q)
               (real_opp (real_mult d2_two (real_mult sp sq)))).
      * apply (RealSetoid.real_eq_plus_compat (real_mult sp sp)
                 (real_mult sq sq) p q).
        -- exact Hspe.
        -- exact Hsqe.
      * exact (real_eq_sym
                 (real_opp (real_mult d2_two (real_mult sp sq)))
                 (real_mult (real_opp d2_two) (real_mult sp sq))
                 (real_opp_mult_r d2_two (real_mult sp sq))).
Qed.

(* ---- 7. 根比下臂（单引擎核）：−(sp·sq) + p ≤_B p·(−L) ---- *)
(*   real_log_le_linear_B 于 t := sq·inv(sp) 处：log t ≤_B t−1         *)
(*   ⟹ 1−t ≤_B −log t（leb3_le_b_opp_rev 反序）⟹ 乘 p 正缩放，        *)
(*   p·t == sp·sq 环闭（sp·inv(sp)==1 右消去）。                        *)

Lemma dhe_log_root_ratio_bound : forall (p q sp sq : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hsp : real_lt real_zero sp) (Hsq : real_lt real_zero sq)
  (Hspe : real_eq (real_mult sp sp) p) (Hsqe : real_eq (real_mult sq sq) q),
  real_le_b (real_plus (real_opp (real_mult sp sq)) p)
            (real_mult p (real_opp
               (real_log (real_mult sq (real_inv_pos sp Hsp))
                         (real_mult_positive sq (real_inv_pos sp Hsp)
                            Hsq (real_inv_pos_pos sp Hsp))))).
Proof.
  intros p q sp sq Hp Hq Hsp Hsq Hspe Hsqe.
  assert (E1 : real_le_b (real_log (real_mult sq (real_inv_pos sp Hsp))
                                   (real_mult_positive sq
                                      (real_inv_pos sp Hsp) Hsq
                                      (real_inv_pos_pos sp Hsp)))
                         (real_plus (real_mult sq (real_inv_pos sp Hsp))
                                    (real_opp real_one)))
    by exact (real_log_le_linear_B (real_mult sq (real_inv_pos sp Hsp))
                                   (real_mult_positive sq
                                      (real_inv_pos sp Hsp) Hsq
                                      (real_inv_pos_pos sp Hsp))).
  assert (E2 : real_le_b
                 (real_opp (real_plus (real_mult sq (real_inv_pos sp Hsp))
                                      (real_opp real_one)))
                 (real_opp (real_log (real_mult sq (real_inv_pos sp Hsp))
                                     (real_mult_positive sq
                                        (real_inv_pos sp Hsp) Hsq
                                        (real_inv_pos_pos sp Hsp)))))
    by exact (leb3_le_b_opp_rev _ _ E1).
  assert (E3 : real_le_b
                 (real_plus (real_opp (real_mult sq (real_inv_pos sp Hsp)))
                            real_one)
                 (real_opp (real_log (real_mult sq (real_inv_pos sp Hsp))
                                     (real_mult_positive sq
                                        (real_inv_pos sp Hsp) Hsq
                                        (real_inv_pos_pos sp Hsp))))).
  { apply (leb3_le_b_eq_l
             (real_opp (real_plus (real_mult sq (real_inv_pos sp Hsp))
                                  (real_opp real_one)))
             (real_plus (real_opp (real_mult sq (real_inv_pos sp Hsp)))
                        real_one)
             (real_opp (real_log (real_mult sq (real_inv_pos sp Hsp))
                                 (real_mult_positive sq
                                    (real_inv_pos sp Hsp) Hsq
                                    (real_inv_pos_pos sp Hsp))))).
    - apply (real_eq_trans
               (real_opp (real_plus (real_mult sq (real_inv_pos sp Hsp))
                                    (real_opp real_one)))
               (real_plus (real_opp (real_mult sq (real_inv_pos sp Hsp)))
                          (real_opp (real_opp real_one)))
               (real_plus (real_opp (real_mult sq (real_inv_pos sp Hsp)))
                          real_one)).
      + exact (real_opp_plus (real_mult sq (real_inv_pos sp Hsp))
                             (real_opp real_one)).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_opp (real_mult sq (real_inv_pos sp Hsp)))
                 (real_opp (real_opp real_one))
                 (real_opp (real_mult sq (real_inv_pos sp Hsp)))
                 real_one
                 (real_eq_refl (real_opp (real_mult sq
                                            (real_inv_pos sp Hsp))))
                 (real_opp_opp real_one)).
    - exact E2. }
  assert (E4 : real_le_b
                 (real_mult p
                    (real_plus (real_opp (real_mult sq
                                             (real_inv_pos sp Hsp)))
                               real_one))
                 (real_mult p (real_opp
                    (real_log (real_mult sq (real_inv_pos sp Hsp))
                              (real_mult_positive sq
                                 (real_inv_pos sp Hsp) Hsq
                                 (real_inv_pos_pos sp Hsp))))))
    by exact (leb3_le_b_pos_scale_l
                (real_plus (real_opp (real_mult sq (real_inv_pos sp Hsp)))
                           real_one)
                (real_opp (real_log (real_mult sq (real_inv_pos sp Hsp))
                                    (real_mult_positive sq
                                       (real_inv_pos sp Hsp) Hsq
                                       (real_inv_pos_pos sp Hsp))))
                p E3 Hp).
  (* 左端换形：p·((−t)+1) == −(p·t) + p == −(sp·sq) + p *)
  apply (leb3_le_b_eq_l
           (real_mult p
              (real_plus (real_opp (real_mult sq (real_inv_pos sp Hsp)))
                         real_one))
           (real_plus (real_opp (real_mult sp sq)) p)
           (real_mult p (real_opp
              (real_log (real_mult sq (real_inv_pos sp Hsp))
                        (real_mult_positive sq (real_inv_pos sp Hsp)
                           Hsq (real_inv_pos_pos sp Hsp)))))).
  - apply (real_eq_trans
             (real_mult p
                (real_plus (real_opp (real_mult sq (real_inv_pos sp Hsp)))
                           real_one))
             (real_plus (real_mult p
                            (real_opp (real_mult sq
                                         (real_inv_pos sp Hsp))))
                        (real_mult p real_one))
             (real_plus (real_opp (real_mult sp sq)) p)).
    + exact (real_distrib p
               (real_opp (real_mult sq (real_inv_pos sp Hsp))) real_one).
    + apply (real_eq_trans
               (real_plus (real_mult p
                              (real_opp (real_mult sq
                                           (real_inv_pos sp Hsp))))
                          (real_mult p real_one))
               (real_plus (real_opp (real_mult p
                                        (real_mult sq
                                           (real_inv_pos sp Hsp))))
                          p)
               (real_plus (real_opp (real_mult sp sq)) p)).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult p
                    (real_opp (real_mult sq (real_inv_pos sp Hsp))))
                 (real_mult p real_one)
                 (real_opp (real_mult p
                              (real_mult sq (real_inv_pos sp Hsp))))
                 p).
      -- exact (real_mult_opp_l p (real_mult sq (real_inv_pos sp Hsp))).
      -- exact (real_mult_one p).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_opp (real_mult p (real_mult sq
                                           (real_inv_pos sp Hsp))))
                 p (real_opp (real_mult sp sq)) p).
        { apply (RealSetoid.real_eq_opp_compat
                   (real_mult p (real_mult sq (real_inv_pos sp Hsp)))
                   (real_mult sp sq)).
          (* p·(sq·inv sp) == sp·sq：sp²==p 回代 + sp·inv(sp)==1 右消去 *)
          apply (real_eq_trans
                   (real_mult p (real_mult sq (real_inv_pos sp Hsp)))
                   (real_mult (real_mult sp sp)
                              (real_mult sq (real_inv_pos sp Hsp)))
                   (real_mult sp sq)).
          - apply (RealSetoid.real_eq_mult_compat p
                     (real_mult sq (real_inv_pos sp Hsp))
                     (real_mult sp sp)
                     (real_mult sq (real_inv_pos sp Hsp))).
            + apply real_eq_sym. exact Hspe.
            + apply real_eq_refl.
          - apply (real_eq_trans
                     (real_mult (real_mult sp sp)
                                (real_mult sq (real_inv_pos sp Hsp)))
                     (real_mult (real_mult sp sq)
                                (real_mult sp (real_inv_pos sp Hsp)))
                     (real_mult sp sq)).
            + exact (dhe_ring_shuffle4 sp sp sq (real_inv_pos sp Hsp)).
            + apply (real_eq_trans
                       (real_mult (real_mult sp sq)
                                  (real_mult sp (real_inv_pos sp Hsp)))
                       (real_mult (real_mult sp sq) real_one)
                       (real_mult sp sq)).
              * apply (RealSetoid.real_eq_mult_compat
                         (real_mult sp sq)
                         (real_mult sp (real_inv_pos sp Hsp))
                         (real_mult sp sq) real_one).
                -- apply real_eq_refl.
                -- exact (real_inv_pos_correct sp Hsp).
              * apply real_mult_one. }
        { apply real_eq_refl. }
  - exact E4.
Qed.

(* ---- 8. 逐点核：H 项 ≤_B gap（gap := kl + (y−x)） ---- *)
(*   差元 == 贰·(p·(−L) − (−sp·sq+p)) ≥_B 0（件 7 缩放）；              *)
(*   H 项按件 6 展开，kl 按件 5 回代贰·p·(−L) 后纯环对消。               *)

Lemma dhe_gap_ge_h2term : forall (p q sp sq : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hsp : real_lt real_zero sp) (Hsq : real_lt real_zero sq)
  (Hspe : real_eq (real_mult sp sp) p) (Hsqe : real_eq (real_mult sq sq) q),
  real_le_b (p2_tvsq sp sq)
            (real_plus (real_kl_term p q Hp Hq)
                       (real_plus q (real_opp p))).
Proof.
  intros p q sp sq Hp Hq Hsp Hsq Hspe Hsqe.
  assert (HKL : real_eq (real_kl_term p q Hp Hq)
                        (real_mult d2_two
                           (real_mult p (real_opp
                              (real_log (real_mult sq (real_inv_pos sp Hsp))
                                        (real_mult_positive sq
                                           (real_inv_pos sp Hsp) Hsq
                                           (real_inv_pos_pos sp Hsp)))))))
    by exact (dhe_kl_twoL p q sp sq Hp Hq Hsp Hsq Hspe Hsqe).
  assert (HRB : real_le_b (real_plus (real_opp (real_mult sp sq)) p)
                          (real_mult p (real_opp
                             (real_log (real_mult sq (real_inv_pos sp Hsp))
                                       (real_mult_positive sq
                                          (real_inv_pos sp Hsp) Hsq
                                          (real_inv_pos_pos sp Hsp))))))
    by exact (dhe_log_root_ratio_bound p q sp sq Hp Hq Hsp Hsq Hspe Hsqe).
  (* 贰倍缩放：贰·(−sp·sq+p) ≤_B 贰·p·(−L) *)
  assert (HE4 : real_le_b
                  (real_mult d2_two (real_plus (real_opp (real_mult sp sq)) p))
                  (real_mult d2_two
                     (real_mult p (real_opp
                        (real_log (real_mult sq (real_inv_pos sp Hsp))
                                  (real_mult_positive sq
                                     (real_inv_pos sp Hsp) Hsq
                                     (real_inv_pos_pos sp Hsp)))))))
    by exact (leb3_le_b_pos_scale_l
                (real_plus (real_opp (real_mult sp sq)) p)
                (real_mult p (real_opp
                   (real_log (real_mult sq (real_inv_pos sp Hsp))
                             (real_mult_positive sq (real_inv_pos sp Hsp)
                                Hsq (real_inv_pos_pos sp Hsp)))))
                d2_two HRB d2_two_pos).
  unfold real_le_b. intros e He.
  (* 差元非负的 eps 形：0 < (贰·p·(−L) + e) + −(贰·(−sp·sq+p)) *)
  assert (H0 : real_lt real_zero
                 (real_plus
                    (real_plus
                       (real_mult d2_two
                          (real_mult p (real_opp
                             (real_log (real_mult sq
                                          (real_inv_pos sp Hsp))
                                        (real_mult_positive sq
                                           (real_inv_pos sp Hsp) Hsq
                                           (real_inv_pos_pos sp Hsp))))))
                       e)
                    (real_opp (real_mult d2_two
                                  (real_plus (real_opp (real_mult sp sq))
                                             p))))).
  { exact (real_lt_opp_plus
             (real_mult d2_two (real_plus (real_opp (real_mult sp sq)) p))
             (real_plus
                (real_mult d2_two
                   (real_mult p (real_opp
                      (real_log (real_mult sq (real_inv_pos sp Hsp))
                                (real_mult_positive sq
                                   (real_inv_pos sp Hsp) Hsq
                                   (real_inv_pos_pos sp Hsp))))))
                e)
             (HE4 e He)). }
  (* 换形：0 < 贰·p·(−L) + (−贰·(−sp·sq+p) + e)（纯环重排） *)
  assert (H0' : real_lt real_zero
                  (real_plus
                     (real_mult d2_two
                        (real_mult p (real_opp
                           (real_log (real_mult sq (real_inv_pos sp Hsp))
                                     (real_mult_positive sq
                                        (real_inv_pos sp Hsp) Hsq
                                        (real_inv_pos_pos sp Hsp))))))
                     (real_plus
                        (real_opp (real_mult d2_two
                                      (real_plus (real_opp (real_mult sp sq))
                                                 p)))
                        e))).
  { apply (RealSetoid.real_lt_id_r real_zero
             (real_plus
                (real_plus
                   (real_mult d2_two
                      (real_mult p (real_opp
                         (real_log (real_mult sq (real_inv_pos sp Hsp))
                                   (real_mult_positive sq
                                      (real_inv_pos sp Hsp) Hsq
                                      (real_inv_pos_pos sp Hsp))))))
                e)
                (real_opp (real_mult d2_two
                              (real_plus (real_opp (real_mult sp sq))
                                         p))))
             (real_plus
                (real_mult d2_two
                   (real_mult p (real_opp
                      (real_log (real_mult sq (real_inv_pos sp Hsp))
                                (real_mult_positive sq
                                   (real_inv_pos sp Hsp) Hsq
                                   (real_inv_pos_pos sp Hsp))))))
                (real_plus
                   (real_opp (real_mult d2_two
                              (real_plus (real_opp (real_mult sp sq))
                                         p)))
                   e))).
    - remember (real_mult d2_two
                  (real_mult p (real_opp
                     (real_log (real_mult sq (real_inv_pos sp Hsp))
                               (real_mult_positive sq
                                  (real_inv_pos sp Hsp) Hsq
                                  (real_inv_pos_pos sp Hsp)))))) as XB.
      d2_ring_eq.
    - exact H0. }
  (* 平移：C + 0 < C + 差元 + e，C := p + q − 贰·sp·sq *)
  apply (RealSetoid.real_lt_id_l (p2_tvsq sp sq)
           (real_plus (real_plus p q)
                      (real_opp (real_mult d2_two (real_mult sp sq))))
           (real_plus
              (real_plus (real_kl_term p q Hp Hq)
                         (real_plus q (real_opp p)))
              e)).
  - exact (dhe_h2_term_expand p q sp sq Hspe Hsqe).
  - apply (RealSetoid.real_lt_id_r
             (real_plus (real_plus p q)
                        (real_opp (real_mult d2_two (real_mult sp sq))))
             (real_plus
                (real_plus
                   (real_plus p q)
                   (real_opp (real_mult d2_two (real_mult sp sq))))
                (real_plus
                   (real_mult d2_two
                      (real_mult p (real_opp
                         (real_log (real_mult sq (real_inv_pos sp Hsp))
                                   (real_mult_positive sq
                                      (real_inv_pos sp Hsp) Hsq
                                      (real_inv_pos_pos sp Hsp))))))
                (real_plus
                   (real_opp (real_mult d2_two
                              (real_plus (real_opp (real_mult sp sq))
                                         p)))
                   e)))
             (real_plus (real_plus (real_kl_term p q Hp Hq)
                                   (real_plus q (real_opp p))) e)).
    + apply (real_eq_trans
               (real_plus
                  (real_plus
                     (real_plus p q)
                     (real_opp (real_mult d2_two (real_mult sp sq))))
                  (real_plus
                     (real_mult d2_two
                        (real_mult p (real_opp
                           (real_log (real_mult sq (real_inv_pos sp Hsp))
                                     (real_mult_positive sq
                                        (real_inv_pos sp Hsp) Hsq
                                        (real_inv_pos_pos sp Hsp))))))
                  (real_plus
                     (real_opp (real_mult d2_two
                                (real_plus (real_opp (real_mult sp sq))
                                           p)))
                     e)))
               (real_plus
                  (real_plus
                     (real_mult d2_two
                        (real_mult p (real_opp
                           (real_log (real_mult sq (real_inv_pos sp Hsp))
                                     (real_mult_positive sq
                                        (real_inv_pos sp Hsp) Hsq
                                        (real_inv_pos_pos sp Hsp))))))
                     (real_plus q (real_opp p)))
                  e)
               (real_plus (real_plus (real_kl_term p q Hp Hq)
                                     (real_plus q (real_opp p))) e)).
      * remember (real_mult d2_two
                    (real_mult p (real_opp
                       (real_log (real_mult sq (real_inv_pos sp Hsp))
                                 (real_mult_positive sq
                                    (real_inv_pos sp Hsp) Hsq
                                    (real_inv_pos_pos sp Hsp)))))) as XB.
        d2_ring_eq.
      * apply (RealSetoid.real_eq_plus_compat
                 (real_plus
                    (real_mult d2_two
                       (real_mult p (real_opp
                          (real_log (real_mult sq (real_inv_pos sp Hsp))
                                    (real_mult_positive sq
                                       (real_inv_pos sp Hsp) Hsq
                                       (real_inv_pos_pos sp Hsp))))))
                    (real_plus q (real_opp p)))
                 e
                 (real_plus (real_kl_term p q Hp Hq)
                            (real_plus q (real_opp p)))
                 e).
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_mult d2_two
                        (real_mult p (real_opp
                           (real_log (real_mult sq (real_inv_pos sp Hsp))
                                     (real_mult_positive sq
                                        (real_inv_pos sp Hsp) Hsq
                                        (real_inv_pos_pos sp Hsp))))))
                     (real_plus q (real_opp p))
                     (real_kl_term p q Hp Hq)
                     (real_plus q (real_opp p))).
          ** apply real_eq_sym. exact HKL.
          ** apply real_eq_refl.
        -- apply real_eq_refl.
    + apply (RealSetoid.real_lt_id_l
               (real_plus (real_plus p q)
                          (real_opp (real_mult d2_two (real_mult sp sq))))
               (real_plus
                  (real_plus (real_plus p q)
                             (real_opp (real_mult d2_two
                                          (real_mult sp sq))))
                  real_zero)
               (real_plus
                  (real_plus
                     (real_plus p q)
                     (real_opp (real_mult d2_two (real_mult sp sq))))
                  (real_plus
                     (real_mult d2_two
                        (real_mult p (real_opp
                           (real_log (real_mult sq (real_inv_pos sp Hsp))
                                     (real_mult_positive sq
                                        (real_inv_pos sp Hsp) Hsq
                                        (real_inv_pos_pos sp Hsp))))))
                  (real_plus
                     (real_opp (real_mult d2_two
                                (real_plus (real_opp (real_mult sp sq))
                                           p)))
                     e)))).
      * apply real_eq_sym. apply real_plus_zero.
      * exact (real_lt_plus_translate
                 (real_plus (real_plus p q)
                            (real_opp (real_mult d2_two
                                         (real_mult sp sq))))
                 real_zero
                 (real_plus
                    (real_mult d2_two
                       (real_mult p (real_opp
                          (real_log (real_mult sq (real_inv_pos sp Hsp))
                                    (real_mult_positive sq
                                       (real_inv_pos sp Hsp) Hsq
                                       (real_inv_pos_pos sp Hsp))))))
                    (real_plus
                       (real_opp (real_mult d2_two
                          (real_plus (real_opp (real_mult sp sq)) p)))
                       e)) H0').
Qed.

(* ---- 9. 主件：H² ≤_B KL₂（两点，Bishop 形出口，零 Or 分支） ---- *)
(*   双肢逐点核（件 8）plus_compat 合流 + dkc_kl2_eq_gaps（件 2 使用）    *)
(*   回代闭合。kl₂ == gap1+gap2 与 H² == H项1+H项2 的归一化对消都在       *)
(*   各腿内部完成，主件纯组装。                                          *)

Theorem dhe_h2_le_kl2 : forall (p q sp sq sp1 sq1 : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hsp : real_lt real_zero sp) (Hsq : real_lt real_zero sq)
  (Hsp1 : real_lt real_zero sp1) (Hsq1 : real_lt real_zero sq1)
  (Hspe : real_eq (real_mult sp sp) p) (Hsqe : real_eq (real_mult sq sq) q)
  (Hsp1e : real_eq (real_mult sp1 sp1) (p2_one_minus p))
  (Hsq1e : real_eq (real_mult sq1 sq1) (p2_one_minus q)),
  real_le_b (dhe_h2 p q sp sq sp1 sq1) (p2_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q sp sq sp1 sq1 Hp Hq Hp1 Hq1 Hsp Hsq Hsp1 Hsq1
    Hspe Hsqe Hsp1e Hsq1e.
  apply (leb3_le_b_eq_r (dhe_h2 p q sp sq sp1 sq1)
           (real_plus
              (real_plus (real_kl_term p q Hp Hq)
                         (real_plus q (real_opp p)))
              (real_plus
                 (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                 (real_plus (p2_one_minus q)
                            (real_opp (p2_one_minus p)))))
           (p2_kl2 p q Hp Hq Hp1 Hq1)).
  - exact (real_le_b_plus_compat
             (p2_tvsq sp sq)
             (real_plus (real_kl_term p q Hp Hq)
                        (real_plus q (real_opp p)))
             (p2_tvsq sp1 sq1)
             (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                    Hp1 Hq1)
                        (real_plus (p2_one_minus q)
                                   (real_opp (p2_one_minus p))))
             (dhe_gap_ge_h2term p q sp sq Hp Hq Hsp Hsq Hspe Hsqe)
             (dhe_gap_ge_h2term (p2_one_minus p) (p2_one_minus q) sp1 sq1
                Hp1 Hq1 Hsp1 Hsq1 Hsp1e Hsq1e)).
  - apply real_eq_sym. exact (dkc_kl2_eq_gaps p q Hp Hq Hp1 Hq1).
Qed.

(* ---- 10. pnt 运输互认：H² ≤_B pnt_kl2（禁第四别名守约） ---- *)

Theorem dhe_h2_le_kl2_pnt : forall (p q sp sq sp1 sq1 : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hsp : real_lt real_zero sp) (Hsq : real_lt real_zero sq)
  (Hsp1 : real_lt real_zero sp1) (Hsq1 : real_lt real_zero sq1)
  (Hspe : real_eq (real_mult sp sp) p) (Hsqe : real_eq (real_mult sq sq) q)
  (Hsp1e : real_eq (real_mult sp1 sp1) (p2_one_minus p))
  (Hsq1e : real_eq (real_mult sq1 sq1) (p2_one_minus q)),
  real_le_b (dhe_h2 p q sp sq sp1 sq1) (pnt_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q sp sq sp1 sq1 Hp Hq Hp1 Hq1 Hsp Hsq Hsp1 Hsq1
    Hspe Hsqe Hsp1e Hsq1e.
  apply (leb3_le_b_eq_r (dhe_h2 p q sp sq sp1 sq1)
           (p2_kl2 p q Hp Hq Hp1 Hq1) (pnt_kl2 p q Hp Hq Hp1 Hq1)).
  - exact (dhe_h2_le_kl2 p q sp sq sp1 sq1 Hp Hq Hp1 Hq1 Hsp Hsq Hsp1 Hsq1
             Hspe Hsqe Hsp1e Hsq1e).
  - exact (dkc_kl2_pnt_eq p q Hp Hq Hp1 Hq1).
Qed.

(* ---- 11. 推论 A（eps 形出口）：H² < KL₂ + eps 逐 eps 显式形 ---- *)

Theorem dhe_h2_le_kl2_eps : forall (p q sp sq sp1 sq1 : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hsp : real_lt real_zero sp) (Hsq : real_lt real_zero sq)
  (Hsp1 : real_lt real_zero sp1) (Hsq1 : real_lt real_zero sq1)
  (Hspe : real_eq (real_mult sp sp) p) (Hsqe : real_eq (real_mult sq sq) q)
  (Hsp1e : real_eq (real_mult sp1 sp1) (p2_one_minus p))
  (Hsq1e : real_eq (real_mult sq1 sq1) (p2_one_minus q))
  (eps : Real) (Heps : real_lt real_zero eps),
  real_lt (dhe_h2 p q sp sq sp1 sq1)
          (real_plus (p2_kl2 p q Hp Hq Hp1 Hq1) eps).
Proof.
  intros p q sp sq sp1 sq1 Hp Hq Hp1 Hq1 Hsp Hsq Hsp1 Hsq1
    Hspe Hsqe Hsp1e Hsq1e eps Heps.
  exact (dhe_h2_le_kl2 p q sp sq sp1 sq1 Hp Hq Hp1 Hq1 Hsp Hsq Hsp1 Hsq1
           Hspe Hsqe Hsp1e Hsq1e eps Heps).
Qed.

(* ---- 12. H² 的 Bishop 非负（平方和，real_square_nonneg_B 完成件） ---- *)

Theorem dhe_h2_nonneg : forall (p q sp sq sp1 sq1 : Real),
  real_le_b real_zero (dhe_h2 p q sp sq sp1 sq1).
Proof.
  intros p q sp sq sp1 sq1.
  apply (leb3_le_b_eq_l (real_plus real_zero real_zero) real_zero
           (dhe_h2 p q sp sq sp1 sq1)).
  - apply real_plus_zero.
  - exact (real_le_b_plus_compat real_zero (p2_tvsq sp sq)
             real_zero (p2_tvsq sp1 sq1)
             (real_square_nonneg_B (p2_diff sp sq))
             (real_square_nonneg_B (p2_diff sp1 sq1))).
Qed.

(* ---- 13. 推论 B（等号侧）：KL₂==0 ⟹ H²==0 ---- *)
(*   H² ≤_B KL₂==0（主件+eq_r）∧ 0 ≤_B H²（件 12）⟹ Bishop 反对称闭合。  *)

Theorem dhe_kl2_zero_of_h2_zero : forall (p q sp sq sp1 sq1 : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hsp : real_lt real_zero sp) (Hsq : real_lt real_zero sq)
  (Hsp1 : real_lt real_zero sp1) (Hsq1 : real_lt real_zero sq1)
  (Hspe : real_eq (real_mult sp sp) p) (Hsqe : real_eq (real_mult sq sq) q)
  (Hsp1e : real_eq (real_mult sp1 sp1) (p2_one_minus p))
  (Hsq1e : real_eq (real_mult sq1 sq1) (p2_one_minus q))
  (Hkl : real_eq (p2_kl2 p q Hp Hq Hp1 Hq1) real_zero),
  real_eq (dhe_h2 p q sp sq sp1 sq1) real_zero.
Proof.
  intros p q sp sq sp1 sq1 Hp Hq Hp1 Hq1 Hsp Hsq Hsp1 Hsq1
    Hspe Hsqe Hsp1e Hsq1e Hkl.
  assert (Hle : real_le_b (dhe_h2 p q sp sq sp1 sq1) real_zero).
  { apply (leb3_le_b_eq_r (dhe_h2 p q sp sq sp1 sq1)
             (p2_kl2 p q Hp Hq Hp1 Hq1) real_zero).
    - exact (dhe_h2_le_kl2 p q sp sq sp1 sq1 Hp Hq Hp1 Hq1 Hsp Hsq Hsp1
               Hsq1 Hspe Hsqe Hsp1e Hsq1e).
    - exact Hkl. }
  exact (gibbe2_le_b_antisym (dhe_h2 p q sp sq sp1 sq1) real_zero Hle
           (dhe_h2_nonneg p q sp sq sp1 sq1)).
Qed.

(* ---- 14. sqrt 见证提取供弹位（AttnSqrt 使用）：0<d ⟹ 正 witness ---- *)
(*   real_sqrt_exists 给 (r, 0≤r ∧ r·r==d)；r==0 情形经 d==0 与        *)
(*   real_lt_irrefl 矛盾排除，闭合为 0<r。                              *)

Theorem dhe_sqrt_witness : forall (d : Real) (Hd : real_lt real_zero d),
  sigT (fun r : Real =>
        sigT (fun _ : real_lt real_zero r =>
              real_eq (real_mult r r) d)).
Proof.
  intros d Hd.
  destruct (real_sqrt_exists d (inl Hd)) as [r [Hr Hreq]].
  destruct Hr as [Hrlt | Hr0].
  - exact (existT (fun r : Real =>
              sigT (fun _ : real_lt real_zero r =>
                    real_eq (real_mult r r) d))
             r
             (existT (fun _ : real_lt real_zero r =>
                    real_eq (real_mult r r) d)
                Hrlt Hreq)).
  - exfalso.
    assert (Hdz : real_eq d real_zero).
    { apply (real_eq_trans d (real_mult r r) real_zero).
      - apply real_eq_sym. exact Hreq.
      - apply (real_eq_trans (real_mult r r)
                 (real_mult real_zero real_zero) real_zero).
        + apply (RealSetoid.real_eq_mult_compat r r real_zero real_zero
                   (real_eq_sym real_zero r Hr0) (real_eq_sym real_zero r Hr0)).
        + apply real_mult_zero. }
    exact (match real_lt_irrefl real_zero
             (RealSetoid.real_lt_id_r real_zero d real_zero Hdz Hd) with end).
Qed.

(* ---- 15. 四见证封装推论：正 p,q ⟹ 见证存在 ∧ H² ≤_B KL₂ 同束 ---- *)
(*   （AttnSqrt 提取四正 witness + 主件直接组装——「四见证乘法免二次       *)
(*     开方」端到端：全程只调一次 sqrt_exists/支，无再开方。）            *)

Theorem dhe_h2_le_kl2_of_sqrt : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  sigT (fun sp : Real =>
        sigT (fun sq : Real =>
        sigT (fun sp1 : Real =>
        sigT (fun sq1 : Real =>
          real_le_b (dhe_h2 p q sp sq sp1 sq1)
                    (p2_kl2 p q Hp Hq Hp1 Hq1))))).
Proof.
  intros p q Hp Hq Hp1 Hq1.
  destruct (dhe_sqrt_witness p Hp) as [sp [Hspl Hspe]].
  destruct (dhe_sqrt_witness q Hq) as [sq [Hsql Hsqe]].
  destruct (dhe_sqrt_witness (p2_one_minus p) Hp1) as [sp1 [Hsp1l Hsp1e]].
  destruct (dhe_sqrt_witness (p2_one_minus q) Hq1) as [sq1 [Hsq1l Hsq1e]].
  exact (existT
           (fun sp : Real =>
              sigT (fun sq : Real =>
                    sigT (fun sp1 : Real =>
                          sigT (fun sq1 : Real =>
                                real_le_b (dhe_h2 p q sp sq sp1 sq1)
                                          (p2_kl2 p q Hp Hq Hp1 Hq1)))))
           sp
           (existT
              (fun sq : Real =>
                 sigT (fun sp1 : Real =>
                       sigT (fun sq1 : Real =>
                             real_le_b (dhe_h2 p q sp sq sp1 sq1)
                                       (p2_kl2 p q Hp Hq Hp1 Hq1))))
              sq
              (existT
                 (fun sp1 : Real =>
                    sigT (fun sq1 : Real =>
                          real_le_b (dhe_h2 p q sp sq sp1 sq1)
                                    (p2_kl2 p q Hp Hq Hp1 Hq1)))
                 sp1
                 (existT
                    (fun sq1 : Real =>
                       real_le_b (dhe_h2 p q sp sq sp1 sq1)
                                 (p2_kl2 p q Hp Hq Hp1 Hq1))
                    sq1
                    (dhe_h2_le_kl2 p q sp sq sp1 sq1 Hp Hq Hp1 Hq1
                       Hspl Hsql Hsp1l Hsq1l Hspe Hsqe Hsp1e Hsq1e))))).
Qed.

(* ---- 99. 尾检 ---- *)
Print Assumptions dhe_h2_le_kl2.
Print Assumptions dhe_h2_le_kl2_pnt.
Print Assumptions dhe_h2_le_kl2_eps.
Print Assumptions dhe_h2_nonneg.
Print Assumptions dhe_kl2_zero_of_h2_zero.
Print Assumptions dhe_sqrt_witness.
Print Assumptions dhe_h2_le_kl2_of_sqrt.
