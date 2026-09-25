(* ============================================================
   EnergyTempMonoB.v — 温度-能量单调性 Bishop 档（≤_B 形）。
   使命：交付温度-能量单调性的 Real 层 Bishop 档——t1 < t2 ⟹
     real_le_b (E(t1)) (E(t2))（Bishop 形非严格序，Real 层对位
     Id energy_exp_temp_mono @S04_RealExpLogConv.v:3733 的构造性
     最强免费档）。
   路线（依存恒等档 + Bishop KL≥0 + leb3 序代数）：
     ① 主恒等式 retm_energy_temp_kl_pair_ident：
        KL(p_{t2}‖p_{t1}) + KL(p_{t1}‖p_{t2}) == (β1−β2)·(E2−E1)；
     ② real_gibbs_inequality_B（Bishop 形 KL≥0：0 ≤_B Σ kl_term，
        归一化前提由 retm_pB_norm 直供、逐点正性由 retm_pB_pos
        语句面原生证书直供）；
     ③ 两个合取肢相加得 0 ≤_B KL 对和；
     ④ 恒等式换形得 0 ≤_B (β1−β2)·(E2−E1)（无条件件）；
     ⑤ β 差正性：t1<t2 ⟹ 1/t2<1/t1 ⟹ 0<β1−β2；
     ⑥ 负系数反变：正缩放乘 inv(β1−β2) 后代数链闭合得 0 ≤_B (E2−E1)；
     ⑦ 终桥：0 ≤_B (E2−E1) ⟹ E1 ≤_B E2。
   对标：UpReqTempDual.v:40-44（严格档需 KL 严格正接口，未建）；
     UpRealLeB 结论 1（real_le_b → real_le 构造性不可证）；故本件
     无条件闭合的最强免费档＝Bishop 形 ≤_B。
   构造性：零承认件；语句面全 Set（real_le_b 为 Set 值 forall 型、
     real_lt 为 sigT 见证型），零 Or 分支、零 Prop 前提位；全件
     Qed 真证；可提取（Obj.magic=0）。
   编译配方：coqc -native-compiler no -q -Q . ""。
   依赖：CW_ConstructiveWorld_219（S01–S15）；UpRealLeB/
     UpRealLeB2/UpRealLeB3；RealEnergyTempMono（retm_ 恒等档族）。
   ============================================================ *)

From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import RealEnergyTempMono.

(* ============================================================ *)
(* Part 0：代数捷径 + 零乘左形                                        *)
(* ============================================================ *)

(* 代数恒等捷径：加/乘/负/原子项上的 real_eq 一步 ring 闭合
   （CWC 卡配方复刻，独立命名；含 inv_pos_correct/log 类 Bishop 等式
   桥的恒等不可用本捷径，须走 real_eq_trans 链） *)
Ltac etm_alg :=
  apply real_eq_of_zero_diff; intro n;
  repeat first [ rewrite real_plus_proj | rewrite real_mult_proj | rewrite real_opp_proj ];
  ring.

(* 0·a == 0（库件 real_mult_zero 是 x·0==0 形，comm 桥补左乘形） *)
Lemma etm_mult_zero_l : forall a : Real, real_eq (real_mult real_zero a) real_zero.
Proof.
  intro a. exact (real_eq_trans (real_mult real_zero a) (real_mult a real_zero) real_zero (real_mult_comm real_zero a) (real_mult_zero a)).
Qed.

(* ============================================================ *)
(* Part 1：β 差正性 + 负系数反变闭合件                                 *)
(* ============================================================ *)

(* t1 < t2 ⟹ 0 < β1−β2（β := 1/t）
   链：real_inv_lt_contra（S07 严格逆反序）给 1/t2 < 1/t1，
   real_lt_opp_plus（S07 差正性桥）给 0 < β1 + (−β2)。 *)
Lemma etm_beta_diff_pos : forall (t1 t2 : Real)
  (Ht1 : real_lt real_zero t1) (Ht2 : real_lt real_zero t2),
  real_lt t1 t2 ->
  real_lt real_zero
    (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t2 Ht2))).
Proof.
  intros t1 t2 Ht1 Ht2 Ht12.
  exact (real_lt_opp_plus (real_inv_pos t2 Ht2) (real_inv_pos t1 Ht1)
             (real_inv_lt_contra t1 t2 Ht1 Ht2 Ht12)).
Qed.

(* 正系数除闭合（负系数反变核心件）：0 < c、0 ≤_B c·D ⟹ 0 ≤_B D。
   正缩放 leb3_le_b_pos_scale（右因子形）乘 inv(c)：
   (0·inv c) ≤_B ((c·D)·inv c)，两端 real_eq 运输——左端 0·inv c == 0，
   右端 (c·D)·inv c == (c·(D·inv c)) == (c·(inv c·D)) == ((c·inv c)·D)
   == 1·D == D 五步 real_eq_trans 链（inv 处不可走 proj 捷径）。 *)
Lemma etm_le_b_scale_inv_zero : forall (c D : Real),
  real_lt real_zero c -> real_le_b real_zero (real_mult c D) ->
  real_le_b real_zero D.
Proof.
  intros c D Hc H.
  assert (Hiv : real_lt real_zero (real_inv_pos c Hc))
    by exact (real_inv_pos_pos c Hc).
  apply (leb3_le_b_eq_l (real_mult real_zero (real_inv_pos c Hc)) real_zero D).
  - exact (etm_mult_zero_l (real_inv_pos c Hc)).
  - apply (leb3_le_b_eq_r _ (real_mult (real_mult c D) (real_inv_pos c Hc)) D).
    + exact (leb3_le_b_pos_scale real_zero (real_mult c D)
               (real_inv_pos c Hc) H Hiv).
    + apply (real_eq_trans (real_mult (real_mult c D) (real_inv_pos c Hc))
                           (real_mult c (real_mult D (real_inv_pos c Hc))) _).
      * exact (real_eq_sym _ _ (real_mult_assoc c D (real_inv_pos c Hc))).
      * apply (real_eq_trans (real_mult c (real_mult D (real_inv_pos c Hc)))
                             (real_mult c (real_mult (real_inv_pos c Hc) D)) _).
        -- exact (RealSetoid.real_eq_mult_compat c (real_mult D (real_inv_pos c Hc))
                    c (real_mult (real_inv_pos c Hc) D)
                    (real_eq_refl c) (real_mult_comm D (real_inv_pos c Hc))).
        -- apply (real_eq_trans (real_mult c (real_mult (real_inv_pos c Hc) D))
                                (real_mult (real_mult c (real_inv_pos c Hc)) D) _).
           ++ exact (real_mult_assoc c (real_inv_pos c Hc) D).
           ++ apply (real_eq_trans (real_mult (real_mult c (real_inv_pos c Hc)) D)
                                   (real_mult real_one D) _).
              ** exact (RealSetoid.real_eq_mult_compat
                          (real_mult c (real_inv_pos c Hc)) D real_one D
                          (real_inv_pos_correct c Hc) (real_eq_refl D)).
              ** apply (real_eq_trans (real_mult real_one D)
                                      (real_mult D real_one) _).
                 --- exact (real_mult_comm real_one D).
                 --- exact (real_mult_one D).
Qed.

(* ============================================================ *)
(* Part 2：KL 对和 ≥_B 0 与缩放恒等式 ≥_B 0（均无条件）                *)
(* ============================================================ *)

(* 0 ≤_B KL(p_{t2}‖p_{t1}) + KL(p_{t1}‖p_{t2})（无条件件）
   real_gibbs_inequality_B（UpRealLeB E.13 Bishop 形 KL≥0）两个合取肢：
   归一化 retm_pB_norm、逐点正性 retm_pB_pos（语句面原生证书）直供；
   real_le_b_plus_compat 相加后 0+0==0 左端运输。 *)
Lemma etm_kl_pair_nonneg_b :
  forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
    (t1 : Real) (Ht1 : real_lt real_zero t1) (t2 : Real) (Ht2 : real_lt real_zero t2),
  real_le_b real_zero
    (real_plus (retm_KL X u s0 l t2 Ht2 t1 Ht1) (retm_KL X u s0 l t1 Ht1 t2 Ht2)).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2.
  assert (Hkl21 : real_le_b real_zero (retm_KL X u s0 l t2 Ht2 t1 Ht1)).
  { exact (real_gibbs_inequality_B X (s0 :: l)
             (retm_pB X u s0 l t2 Ht2) (retm_pB X u s0 l t1 Ht1)
             (retm_pB_pos X u s0 l t2 Ht2) (retm_pB_pos X u s0 l t1 Ht1)
             (retm_pB_norm X u s0 l t2 Ht2) (retm_pB_norm X u s0 l t1 Ht1)). }
  assert (Hkl12 : real_le_b real_zero (retm_KL X u s0 l t1 Ht1 t2 Ht2)).
  { exact (real_gibbs_inequality_B X (s0 :: l)
             (retm_pB X u s0 l t1 Ht1) (retm_pB X u s0 l t2 Ht2)
             (retm_pB_pos X u s0 l t1 Ht1) (retm_pB_pos X u s0 l t2 Ht2)
             (retm_pB_norm X u s0 l t1 Ht1) (retm_pB_norm X u s0 l t2 Ht2)). }
  apply (leb3_le_b_eq_l (real_plus real_zero real_zero) real_zero
           (real_plus (retm_KL X u s0 l t2 Ht2 t1 Ht1)
                      (retm_KL X u s0 l t1 Ht1 t2 Ht2))).
  - exact (real_plus_zero real_zero).
  - exact (real_le_b_plus_compat real_zero (retm_KL X u s0 l t2 Ht2 t1 Ht1)
             real_zero (retm_KL X u s0 l t1 Ht1 t2 Ht2) Hkl21 Hkl12).
Qed.

(* 0 ≤_B (β1−β2)·(E2−E1)（无条件件；恒等档 × Bishop KL≥0 直接合成）
   恒等式 retm_energy_temp_kl_pair_ident 右端换形（leb3_le_b_eq_r）。 *)
Lemma etm_energy_scaled_nonneg_b :
  forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
    (t1 : Real) (Ht1 : real_lt real_zero t1) (t2 : Real) (Ht2 : real_lt real_zero t2),
  real_le_b real_zero
    (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t2 Ht2)))
               (real_plus (retm_Eexp X u s0 l t2 Ht2)
                          (real_opp (retm_Eexp X u s0 l t1 Ht1)))).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2.
  apply (leb3_le_b_eq_r real_zero
           (real_plus (retm_KL X u s0 l t2 Ht2 t1 Ht1)
                      (retm_KL X u s0 l t1 Ht1 t2 Ht2))).
  - exact (etm_kl_pair_nonneg_b X u s0 l t1 Ht1 t2 Ht2).
  - exact (retm_energy_temp_kl_pair_ident X u s0 l t1 Ht1 t2 Ht2).
Qed.

(* ============================================================ *)
(* Part 3：主定理——温度-能量单调 Bishop 档                             *)
(* ============================================================ *)

(* t1 < t2 ⟹ E(t1) ≤_B E(t2)
   终桥（0 ≤_B (E2−E1) ⟹ E1 ≤_B E2）逐 eps 展开：
   给 eps>0，0 < (E2−E1)+eps（Hediff）右加平移 E1（real_lt_plus_compat_
   lt_le 右加形）得 0+E1 < (E2−E1)+eps+E1；两端换形——左 0+E1 == E1
   （comm + zero），右 (E2−E1)+eps+E1 == E2+eps（etm_alg 一步）；再
   E1+0 == E1 左端运输闭合。 *)
Theorem etm_energy_temp_mono_b :
  forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
    (t1 : Real) (Ht1 : real_lt real_zero t1) (t2 : Real) (Ht2 : real_lt real_zero t2),
  real_lt t1 t2 ->
  real_le_b (retm_Eexp X u s0 l t1 Ht1) (retm_Eexp X u s0 l t2 Ht2).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 Ht12.
  pose proof (etm_beta_diff_pos t1 t2 Ht1 Ht2 Ht12) as Hdb.
  pose proof (etm_energy_scaled_nonneg_b X u s0 l t1 Ht1 t2 Ht2) as Hscaled.
  pose proof (etm_le_b_scale_inv_zero
                (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t2 Ht2)))
                (real_plus (retm_Eexp X u s0 l t2 Ht2)
                           (real_opp (retm_Eexp X u s0 l t1 Ht1)))
                Hdb Hscaled) as Hediff.
  unfold real_le_b. intros eps Heps.
  pose proof (Hediff eps Heps) as H0.
  apply (RealSetoid.real_lt_id_l (retm_Eexp X u s0 l t1 Ht1)
           (real_plus real_zero (retm_Eexp X u s0 l t1 Ht1))
           (real_plus (retm_Eexp X u s0 l t2 Ht2) eps)).
  - (* E1 == 0+E1：zero 与 comm 双肢 trans（real_eq_sym 双 Real 参显式，term 式占位） *)
    exact (real_eq_trans (retm_Eexp X u s0 l t1 Ht1)
             (real_plus (retm_Eexp X u s0 l t1 Ht1) real_zero)
             (real_plus real_zero (retm_Eexp X u s0 l t1 Ht1))
             (real_eq_sym (real_plus (retm_Eexp X u s0 l t1 Ht1) real_zero)
                          (retm_Eexp X u s0 l t1 Ht1)
                          (real_plus_zero (retm_Eexp X u s0 l t1 Ht1)))
             (real_eq_sym (real_plus real_zero (retm_Eexp X u s0 l t1 Ht1))
                          (real_plus (retm_Eexp X u s0 l t1 Ht1) real_zero)
                          (real_plus_comm real_zero (retm_Eexp X u s0 l t1 Ht1)))).
  - apply (RealSetoid.real_lt_id_r
             (real_plus real_zero (retm_Eexp X u s0 l t1 Ht1))
             (real_plus (real_plus (real_plus (retm_Eexp X u s0 l t2 Ht2)
                                               (real_opp (retm_Eexp X u s0 l t1 Ht1)))
                                    eps)
                        (retm_Eexp X u s0 l t1 Ht1))
             (real_plus (retm_Eexp X u s0 l t2 Ht2) eps)).
    + (* (E2−E1)+eps+E1 == E2+eps：纯加负代数一步闭合 *)
      etm_alg.
    + apply (real_lt_plus_compat_lt_le real_zero
               (real_plus (real_plus (retm_Eexp X u s0 l t2 Ht2)
                                     (real_opp (retm_Eexp X u s0 l t1 Ht1))) eps)
               (retm_Eexp X u s0 l t1 Ht1) (retm_Eexp X u s0 l t1 Ht1)).
      * exact H0.
      * apply real_le_refl.
Qed.

(* ============================================================ *)
(* G4 证据：全件零外部未证假设                                         *)
(* ============================================================ *)
Print Assumptions etm_mult_zero_l.
Print Assumptions etm_beta_diff_pos.
Print Assumptions etm_le_b_scale_inv_zero.
Print Assumptions etm_kl_pair_nonneg_b.
Print Assumptions etm_energy_scaled_nonneg_b.
Print Assumptions etm_energy_temp_mono_b.
