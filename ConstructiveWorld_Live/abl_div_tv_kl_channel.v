(* ============================================================ *)
(* abl_div_tv_kl_channel.v                                        *)
(* 模块名：abl_div_tv_kl_channel                                   *)
(* 数学使命：f-散度海峡汇合件（成桥系列第 5 件）——两点 TV²-KL 双向    *)
(*   夹逼通道：下臂 TV² ≤_B KL₂（pnk2_pinsker_one 的壹倍运输两点形）+  *)
(*   上臂 KL₂ ≤_B 贰·TV²/m（逆 Pinsker 两点形：件 2 主件 dkc_kl2_le_cs  *)
(*   与件 1d div2_cs_le_tvsq_over_m 经 real_le_b_trans 一钉合流）+     *)
(*   夹逼合并件与四件合订通道链（TV²≤KL₂≤χ²≤贰·TV²/m 逐段引用）+      *)
(*   贰·inv(肆)==捌 ¼ 档常数桥（P 草案「无条件版」修正为 q∈[¼,¾] 条件档，  *)
(*   见头注构造性注记）+ Doeblin 窗衔接位（陈述级挂点：minorization    *)
(*   迭代质量下臂 m_k 证书由后续使用方供给，本件申报窗口形状并闭合）。 *)
(* 依赖清单：件 1 abl_div_chisq_twopoint（div2_cs/div2_cs_le_tvsq_    *)
(*   over_m/d2_two/d2_four/d2_four_pos/d2_ring_eq）、件 2             *)
(*   abl_div_kl_chisq_twopoint（dkc_kl2_le_cs 主件）、PinskerTwoPoint  *)
(*   （p2_tvsq/p2_one_minus/p2_kl2）、UpReqPinskerCore（pnk2_pinsker_  *)
(*   one 下臂原件）、UpRealLeB/UpRealLeB2（real_le_b/real_le_b_trans、 *)
(*   UpRealLeB3（leb3_eq_l/eq_r 运输件族）、S01/S02/S03/S07/S08 基座。 *)
(* 构造性注记：全件 Set 层出口；非严格序一律 Bishop 形 real_le_b（零 Or  *)
(*   形平方非负位；Hne/Hmq/Hmq1 沿前件既定 Or/le 形证书随行）；合并与   *)
(*   窗衔接用嵌套 sigT 装载（And 不载 Set 分量）；零承认式语句、零经典   *)
(*   公理、全部 Qed 闭合。修正说明：P 草案件 5 草案「无条件版 m:=¼ 即     *)
(*   KL₂ ≤ 捌·TV² 无条件」不成立——q 可任意接近零时一致正 m 不存在       *)
(*   （反例 p=½、q=10⁻⁴：KL₂≈3.91 > 捌·TV²≈2.00），本件按实况交付       *)
(*   条件档（壹/肆 ≤ q ≤ 叁/肆 双质量证书），m 语义与件 1d 实文统一。    *)
(* 编译配方：                                                       *)
(*   source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&        *)
(*   ulimit -s 65532 && cd <池> && nice -19 rocq c -native-compiler  *)
(*   no -Q <缓存根> "" abl_div_tv_kl_channel.v                        *)
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
Require Import UpReqPinskerCore.
Require Import abl_div_chisq_twopoint.
Require Import abl_div_kl_chisq_twopoint.

(* ---- 1. 下臂两点形：TV² ≤_B KL₂（pnk2_pinsker_one 壹倍运输） ---- *)

(* 壹乘恒等：壹·X == X（comm + real_mult_one 纯环链） *)
Lemma dtv_one_mult_eq : forall (X : Real),
  real_eq (real_mult real_one X) X.
Proof.
  intros X.
  apply (real_eq_trans (real_mult real_one X) (real_mult X real_one) X).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

(* 下臂两点形：Hne 证书下 TV² ≤_B KL₂。
   （原件 pnk2_pinsker_one 出口带壹倍壳，leb3_le_b_eq_l 左运输剥壳；
     对照位不重列——阶梯 climb 面仍归 UpReqPinskerCore。） *)
Theorem dtv_tvsq_le_kl2 : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hne : Or (real_lt p q) (real_lt q p)),
  real_le_b (p2_tvsq p q) (p2_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hne.
  apply (leb3_le_b_eq_l (real_mult real_one (p2_tvsq p q))
           (p2_tvsq p q) (p2_kl2 p q Hp Hq Hp1 Hq1)).
  - exact (dtv_one_mult_eq (p2_tvsq p q)).
  - exact (pnk2_pinsker_one p q Hp Hq Hp1 Hq1 Hne).
Qed.

(* ---- 2. 上臂（逆 Pinsker 两点形）：KL₂ ≤_B 贰·TV²/m ---- *)
(*   两已闭臂一钉汇合：件 2 主件（KL₂ ≤_B χ²）+ 件 1d 条件上臂          *)
(*   （χ² ≤_B 贰·TV²/m）经 real_le_b_trans 合流——零新分析。m 语义与    *)
(*   件 1d 实文逐字统一（同一最小质量证书位 Hm/Hmq/Hmq1）。             *)

Theorem dtv_kl2_le_tvsq_over_m : forall (p q m : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hm : real_lt real_zero m)
  (Hmq : real_le m q) (Hmq1 : real_le m (p2_one_minus q)),
  real_le_b (p2_kl2 p q Hp Hq Hp1 Hq1)
            (real_mult d2_two
               (real_mult (p2_tvsq p q) (real_inv_pos m Hm))).
Proof.
  intros p q m Hp Hq Hp1 Hq1 Hm Hmq Hmq1.
  apply (real_le_b_trans (p2_kl2 p q Hp Hq Hp1 Hq1)
           (div2_cs p q Hq Hq1)
           (real_mult d2_two
              (real_mult (p2_tvsq p q) (real_inv_pos m Hm)))).
  - exact (dkc_kl2_le_cs p q Hp Hq Hp1 Hq1).
  - exact (div2_cs_le_tvsq_over_m p q m Hq Hq1 Hm Hmq Hmq1).
Qed.

(* ---- 3. 上臂 eps 形出口：KL₂ < 贰·TV²/m + eps 逐 eps 显式形 ---- *)

Theorem dtv_kl2_le_tvsq_over_m_eps : forall (p q m : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hm : real_lt real_zero m)
  (Hmq : real_le m q) (Hmq1 : real_le m (p2_one_minus q))
  (eps : Real) (Heps : real_lt real_zero eps),
  real_lt (p2_kl2 p q Hp Hq Hp1 Hq1)
          (real_plus (real_mult d2_two
                        (real_mult (p2_tvsq p q) (real_inv_pos m Hm)))
                     eps).
Proof.
  intros p q m Hp Hq Hp1 Hq1 Hm Hmq Hmq1 eps Heps.
  exact (dtv_kl2_le_tvsq_over_m p q m Hp Hq Hp1 Hq1 Hm Hmq Hmq1 eps Heps).
Qed.

(* ---- 4. 夹逼合并件：TV² ≤_B KL₂ ≤_B 贰·TV²/m（嵌套 sigT 装载） ---- *)

Definition dtv_sandwich : Set :=
  forall (p q m : Real)
    (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
    (Hp1 : real_lt real_zero (p2_one_minus p))
    (Hq1 : real_lt real_zero (p2_one_minus q))
    (Hne : Or (real_lt p q) (real_lt q p))
    (Hm : real_lt real_zero m)
    (Hmq : real_le m q) (Hmq1 : real_le m (p2_one_minus q)),
    sigT (fun _ : real_le_b (p2_tvsq p q) (p2_kl2 p q Hp Hq Hp1 Hq1) =>
          real_le_b (p2_kl2 p q Hp Hq Hp1 Hq1)
                    (real_mult d2_two
                       (real_mult (p2_tvsq p q) (real_inv_pos m Hm)))).

Lemma dtv_sandwich_def : dtv_sandwich.
Proof.
  intros p q m Hp Hq Hp1 Hq1 Hne Hm Hmq Hmq1.
  exact (existT
           (fun _ : real_le_b (p2_tvsq p q) (p2_kl2 p q Hp Hq Hp1 Hq1) =>
            real_le_b (p2_kl2 p q Hp Hq Hp1 Hq1)
                      (real_mult d2_two
                         (real_mult (p2_tvsq p q) (real_inv_pos m Hm))))
           (dtv_tvsq_le_kl2 p q Hp Hq Hp1 Hq1 Hne)
           (dtv_kl2_le_tvsq_over_m p q m Hp Hq Hp1 Hq1 Hm Hmq Hmq1)).
Qed.

(* ---- 5. 四件合订通道链：TV² ≤_B KL₂ ≤_B χ² ≤_B 贰·TV²/m ---- *)
(*   （件 1c/件 1d/件 2 主件/下臂原件逐段引用合订；中间跨 KL₂≤_B χ²     *)
(*     即件 2 主件原文，右跨即件 1d 原文——合订零新分析。）             *)

Definition dtv_channel_chain : Set :=
  forall (p q m : Real)
    (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
    (Hp1 : real_lt real_zero (p2_one_minus p))
    (Hq1 : real_lt real_zero (p2_one_minus q))
    (Hne : Or (real_lt p q) (real_lt q p))
    (Hm : real_lt real_zero m)
    (Hmq : real_le m q) (Hmq1 : real_le m (p2_one_minus q)),
    sigT (fun _ : real_le_b (p2_tvsq p q) (p2_kl2 p q Hp Hq Hp1 Hq1) =>
          sigT (fun _ : real_le_b (p2_kl2 p q Hp Hq Hp1 Hq1)
                             (div2_cs p q Hq Hq1) =>
                real_le_b (div2_cs p q Hq Hq1)
                          (real_mult d2_two
                             (real_mult (p2_tvsq p q) (real_inv_pos m Hm))))).

Lemma dtv_channel_chain_def : dtv_channel_chain.
Proof.
  intros p q m Hp Hq Hp1 Hq1 Hne Hm Hmq Hmq1.
  exact (existT
           (fun _ : real_le_b (p2_tvsq p q) (p2_kl2 p q Hp Hq Hp1 Hq1) =>
            sigT (fun _ : real_le_b (p2_kl2 p q Hp Hq Hp1 Hq1)
                               (div2_cs p q Hq Hq1) =>
                  real_le_b (div2_cs p q Hq Hq1)
                            (real_mult d2_two
                               (real_mult (p2_tvsq p q)
                                          (real_inv_pos m Hm)))))
           (dtv_tvsq_le_kl2 p q Hp Hq Hp1 Hq1 Hne)
           (existT
              (fun _ : real_le_b (p2_kl2 p q Hp Hq Hp1 Hq1)
                                 (div2_cs p q Hq Hq1) =>
               real_le_b (div2_cs p q Hq Hq1)
                         (real_mult d2_two
                            (real_mult (p2_tvsq p q) (real_inv_pos m Hm))))
              (dkc_kl2_le_cs p q Hp Hq Hp1 Hq1)
              (div2_cs_le_tvsq_over_m p q m Hq Hq1 Hm Hmq Hmq1))).
Qed.

(* ---- 6. ¼ 档：贰·inv(肆)==捌 常数桥与捌·TV² 条件上臂 ---- *)
(*   修正说明（头注）：P 草案「无条件版」不成立；本档实为 q∈[¼,¾]        *)
(*   条件档（壹/肆 ≤ q 且 壹/肆 ≤ 壹−q 双质量证书），常数档样例。        *)

Definition dtv_quarter : Real := real_inv_pos d2_four d2_four_pos.
Definition dtv_quarter_pos : real_lt real_zero dtv_quarter :=
  real_inv_pos_pos d2_four d2_four_pos.
Definition dtv_eight : Real := real_plus d2_four d2_four.

(* 常数桥：贰·inv(肆) == 捌。
   路线：inv(inv 肆) == 肆（inv 唯一性，公共乘子肆两侧乘出壹），
   壹/肆 恒等回代后余式纯环——inv 项全程不拆解（环闭原子位避开）。 *)
Lemma dtv_two_inv_quarter_eq :
  real_eq (real_mult d2_two (real_inv_pos dtv_quarter dtv_quarter_pos))
          dtv_eight.
Proof.
  assert (L : real_eq (real_inv_pos dtv_quarter dtv_quarter_pos) d2_four).
  { apply (real_inv_unique dtv_quarter
             (real_inv_pos dtv_quarter dtv_quarter_pos) d2_four).
    - exact (real_inv_pos_correct dtv_quarter dtv_quarter_pos).
    - (* 肆·inv(肆) == 壹 的 comm 换形（dtv_quarter·肆 == 壹） *)
      apply (real_eq_trans (real_mult dtv_quarter d2_four)
               (real_mult d2_four dtv_quarter) real_one).
      + apply real_mult_comm.
      + exact (real_inv_pos_correct d2_four d2_four_pos). }
  apply (real_eq_trans
           (real_mult d2_two (real_inv_pos dtv_quarter dtv_quarter_pos))
           (real_mult d2_two d2_four)
           dtv_eight).
  - apply (RealSetoid.real_eq_mult_compat d2_two
             (real_inv_pos dtv_quarter dtv_quarter_pos) d2_two d2_four).
    + apply real_eq_refl.
    + exact L.
  - unfold dtv_eight. d2_ring_eq.
Qed.

(* 全变量形缩放换算小件：a·(T·J) == (a·J)·T
   （环闭原子位复合项避开——沿用先例 AX 同款：全变量形独立纯环件，
     调用位以复合项直取代参；J 取 inv 项时环内为不透明原子。） *)
Lemma dtv_swap_scale : forall (a T J : Real),
  real_eq (real_mult a (real_mult T J))
          (real_mult (real_mult a J) T).
Proof.
  intros a T J. d2_ring_eq.
Qed.

(* 捌·TV² 条件上臂：壹/肆 ≤ q 且 壹/肆 ≤ 壹−q 给 KL₂ ≤_B 捌·TV²。
   （上臂 m:=壹/肆 实例化 + 常数桥右运输；d2_ring_eq 不动 inv 项。） *)
Theorem dtv_kl2_le_eight_tvsq : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hq4l : real_le dtv_quarter q)
  (Hq4r : real_le dtv_quarter (p2_one_minus q)),
  real_le_b (p2_kl2 p q Hp Hq Hp1 Hq1)
            (real_mult dtv_eight (p2_tvsq p q)).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hq4l Hq4r.
  apply (leb3_le_b_eq_r (p2_kl2 p q Hp Hq Hp1 Hq1)
           (real_mult d2_two
              (real_mult (p2_tvsq p q)
                         (real_inv_pos dtv_quarter dtv_quarter_pos)))
           (real_mult dtv_eight (p2_tvsq p q))).
  - exact (dtv_kl2_le_tvsq_over_m p q dtv_quarter Hp Hq Hp1 Hq1
             dtv_quarter_pos Hq4l Hq4r).
  - apply (real_eq_trans
             (real_mult d2_two
                (real_mult (p2_tvsq p q)
                           (real_inv_pos dtv_quarter dtv_quarter_pos)))
             (real_mult
                (real_mult d2_two
                   (real_inv_pos dtv_quarter dtv_quarter_pos))
                (p2_tvsq p q))
             (real_mult dtv_eight (p2_tvsq p q))).
    + exact (dtv_swap_scale d2_two (p2_tvsq p q)
               (real_inv_pos dtv_quarter dtv_quarter_pos)).
    + apply (RealSetoid.real_eq_mult_compat
               (real_mult d2_two
                  (real_inv_pos dtv_quarter dtv_quarter_pos))
               (p2_tvsq p q)
               dtv_eight
               (p2_tvsq p q)).
      * exact dtv_two_inv_quarter_eq.
      * apply real_eq_refl.
Qed.

(* ---- 7. Doeblin 窗衔接位（陈述级挂点，接入后续使用方） ---- *)
(*   窗形：使用方供 Doeblin minorization 迭代质量下臂 m_k 的两点逐坐标    *)
(*   证书（0<m_k、m_k≤q、m_k≤壹−q；m_k:=壹−(壹−δ)^k 的显式迭代代数在     *)
(*   tvd_/doe_ 面，本件不内置），即得三窗口同束：下臂 TV²≤_B KL₂、上臂     *)
(*   KL₂≤_B 贰·TV²/m_k、χ²≤_B 贰·TV²/m_k——UpReqDoeblinEntropy「Pinsker  *)
(*   型定量面」单侧升双侧的挂点位（直接 Require 替换点）。                *)

Definition dtv_doeblin_kl_window : Set :=
  forall (p q mk : Real)
    (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
    (Hp1 : real_lt real_zero (p2_one_minus p))
    (Hq1 : real_lt real_zero (p2_one_minus q))
    (Hne : Or (real_lt p q) (real_lt q p))
    (Hmk : real_lt real_zero mk)
    (Hmq : real_le mk q) (Hmq1 : real_le mk (p2_one_minus q)),
    sigT (fun _ : real_le_b (p2_tvsq p q) (p2_kl2 p q Hp Hq Hp1 Hq1) =>
          sigT (fun _ : real_le_b (p2_kl2 p q Hp Hq Hp1 Hq1)
                     (real_mult d2_two
                        (real_mult (p2_tvsq p q) (real_inv_pos mk Hmk))) =>
                real_le_b (div2_cs p q Hq Hq1)
                          (real_mult d2_two
                             (real_mult (p2_tvsq p q)
                                        (real_inv_pos mk Hmk))))).

Lemma dtv_doeblin_kl_window_def : dtv_doeblin_kl_window.
Proof.
  intros p q mk Hp Hq Hp1 Hq1 Hne Hmk Hmq Hmq1.
  exact (existT
           (fun _ : real_le_b (p2_tvsq p q) (p2_kl2 p q Hp Hq Hp1 Hq1) =>
            sigT (fun _ : real_le_b (p2_kl2 p q Hp Hq Hp1 Hq1)
                       (real_mult d2_two
                          (real_mult (p2_tvsq p q)
                                     (real_inv_pos mk Hmk))) =>
                  real_le_b (div2_cs p q Hq Hq1)
                            (real_mult d2_two
                               (real_mult (p2_tvsq p q)
                                          (real_inv_pos mk Hmk)))))
           (dtv_tvsq_le_kl2 p q Hp Hq Hp1 Hq1 Hne)
           (existT
              (fun _ : real_le_b (p2_kl2 p q Hp Hq Hp1 Hq1)
                          (real_mult d2_two
                             (real_mult (p2_tvsq p q)
                                        (real_inv_pos mk Hmk))) =>
               real_le_b (div2_cs p q Hq Hq1)
                         (real_mult d2_two
                            (real_mult (p2_tvsq p q)
                                       (real_inv_pos mk Hmk))))
              (dtv_kl2_le_tvsq_over_m p q mk Hp Hq Hp1 Hq1 Hmk Hmq Hmq1)
              (div2_cs_le_tvsq_over_m p q mk Hq Hq1 Hmk Hmq Hmq1))).
Qed.

(* ---- 99. 尾检 ---- *)
Print Assumptions dtv_tvsq_le_kl2.
Print Assumptions dtv_kl2_le_tvsq_over_m.
Print Assumptions dtv_kl2_le_tvsq_over_m_eps.
Print Assumptions dtv_sandwich_def.
Print Assumptions dtv_channel_chain_def.
Print Assumptions dtv_two_inv_quarter_eq.
Print Assumptions dtv_kl2_le_eight_tvsq.
Print Assumptions dtv_doeblin_kl_window_def.
