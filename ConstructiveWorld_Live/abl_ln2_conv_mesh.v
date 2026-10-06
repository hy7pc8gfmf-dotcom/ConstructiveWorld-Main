(* ===================================================================== *)
(*  abl_ln2_conv_mesh.v —— ln2 逼近链·卷积基建与基准列全形组装件           *)
(*  模块名：abl_ln2_conv_mesh.                                            *)
(*  使命: 把卷积核引理面（两歧引擎所在 conv_core）与基准列 ln2i_x 组合成     *)
(*        终件，六节：                                                    *)
(*        【§1 增长估计】阶乘不超过底自乘 n! ≤ nⁿ，规范分子面               *)
(*        L_n·q̃_n ≤ (6n)ⁿ——分子增长的无条件算术账（零前提）；              *)
(*        【§2 档位估计】4/5 < 1 与 (4/5)ⁿ < 1（n ≥ 1，使用 theta_total    *)
(*        预算件）；                                                      *)
(*        【§3 规范数据组合】改型分子对 A_n/B_n 的正性证明                 *)
(*        （0 < |A_n| 沿规范面恒等传送）与线对象同一定义面证明             *)
(*        （cc_line 与 ln2b_line 定义性同一）；                           *)
(*        【§4 载体供给型】cm_supply：下界肢 clo ≤ 线、上界肢 线 ≤ (4/5)ⁿ、  *)
(*        载体正性 0 < clo 三肢——唯一开槽为恒等式腿的下上界对              *)
(*        （沿在案登记的未竟项如实悬置，到货即升格）；                 *)
(*        【§5 分离常数终件】cm_bound：供给条件下对一切有理数 u/v 显式给出  *)
(*        正分离常数 c 与终归指标 K，使 c ≤ |u/v − x_k| 对 k ≥ K 成立      *)
(*        （直调两歧引擎，读数沿基准列投影确定）；配五肢供给投影件          *)
(*        cm_pade_of_supply（档位与分子正性两肢已由本件无条件消解，        *)
(*        五肢折为三肢纯投影）；                                          *)
(*        【§6 数值锚组】q=1 带窗锚 (4/5)⁸ < 1/2、增长锚 L_1·q̃_1 ≤ 6、     *)
(*        首项链面锚 A_1 = 3 与 B_1 = 4/2。                               *)
(*  依赖: Stdlib QArith/Qabs/Arith/Factorial/ZArith/Lia；S01_BaseRing      *)
(*        S02_CauchyComplete S03_QExp；UpReqLn2Irrational（基准列）；       *)
(*        Ln2Bridge（ln2b_X/ln2b_line/ln2b_X_proj 供给面）；BeukersLists   *)
(*        （q̃_n）、HansonLcm（L_n 与 L_n ≤ n!）；池件 tail_bound           *)
(*        （lnt_leT'_eq_r 传送面）、growth_budget（q̃_n ≤ 6ⁿ、底乘幂拆）、   *)
(*        theta_total（(4/5)ⁿ < 1 预算件）、assembly（改型分子对与正性     *)
(*        三肢、首项锚）、conv_core（两歧引擎与线对象）。工艺注记：        *)
(*        Qabs 与 QleT' 无相等-尊重实例，凡相等式在其内部一律走顶层        *)
(*        Qabs_wd/lnt_leT'_eq_r 传送件，禁子项位改写。                     *)
(*  对标: Ln2Bridge ln2b_delta_of_supply 的分离常数提取形；本件三处增强：  *)
(*        带窗指标闭式化（conv_core n₀ := 8·⌊v⌋）、引擎对任意基准实数通用、  *)
(*        分离核独立成件；增长估计为无条件新算术账（n! ≤ nⁿ 系归纳新证）。   *)
(*  构造性: 纯构造性、零承认件；交付语句面全 Set（sigT/S01.And/QeqT/       *)
(*        QleT'/QltT/real_le），nat 面增长算术脚手架语句与池件同款纪律；    *)
(*        Qeq/Qle/Qlt 仅 Prop 推理面作脚手架；分离常数与指标全显式封闭项。  *)
(*  诚实面: 恒等式腿（Σ_k bterm = q̃_n·ln2 − p_n 的代数恒等式）系 campaign  *)
(*        级在案余件，本件如实不虚报闭合：cm_supply 以单开槽承载其下上界    *)
(*        对，未竟项到货即经 cm_pade_of_supply 折入 cm_bound 升格无条件分离。 *)
(*  编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*        ulimit -s 65532 && nice -19 rocq c -native-compiler no           *)
(*        -Q vo_local_world_unified_0930 "" 本件（独占池 ln2_theta_total/， *)
(*        链序：tail_bound/growth_budget/theta_total/assembly/conv_core    *)
(*        先编，道闸≤1 单道串行）。                                        *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith
  Arith.Factorial ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import UpReqLn2Irrational Ln2Bridge.
Require Import BeukersLists HansonLcm.
Require Import abl_ln2_tail_bound abl_ln2_growth_budget abl_ln2_theta_total
  abl_ln2_assembly abl_ln2_conv_core.

Open Scope nat_scope.

(* ============================================================ *)
(* §1 增长估计（无条件算术账）                                            *)
(* ============================================================ *)

(* 阶乘不超过底自乘：n! ≤ nⁿ（归纳） *)
Theorem cm_fact_le_pow : forall n : nat, fact n <= n ^ n.
Proof.
  induction n as [| n IH].
  - cbn. lia.
  - cbn [fact]. rewrite Nat.pow_succ_r'.
    apply Nat.mul_le_mono.
    + apply Nat.le_refl.
    + eapply Nat.le_trans.
      * exact IH.
      * apply Nat.pow_le_mono_l. lia.
Qed.

(* 规范分子面增长账：L_n·q̃_n ≤ (6n)ⁿ
   （链：L_n ≤ n! → n! ≤ nⁿ → q̃_n ≤ 6ⁿ → 底乘幂拆合） *)
Theorem cm_A_le : forall n : nat, hl_lcm_upto n * bk_Qn_qtilde n <= (6 * n) ^ n.
Proof.
  intro n.
  replace ((6 * n) ^ n) with ((n * 6) ^ n)
    by (f_equal; apply Nat.mul_comm).
  rewrite lng2_pow_mul_l.
  eapply Nat.le_trans.
  - apply Nat.mul_le_mono.
    + apply hl_lcm_le_fact.
    + apply lng2_qtilde_le_6pow.
  - apply Nat.mul_le_mono.
    + apply cm_fact_le_pow.
    + apply Nat.le_refl.
Qed.

(* ============================================================ *)
(* §2 档位估计                                                            *)
(* ============================================================ *)

(* 档位小于一：4/5 < 1 *)
Theorem cm_theta_lt1 : QltT (4 # 5)%Q (1 # 1)%Q.
Proof. apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. lia. Qed.

(* 预算件：n ≥ 1 处 (4/5)ⁿ < 1（使用 theta_total） *)
Theorem cm_theta_budget_lt1 : forall n : nat,
  (1 <= n)%nat -> QltT (q_pow (4 # 5)%Q n) (1 # 1)%Q.
Proof. intros n Hn. exact (lnt4_theta_budget_lt n Hn). Qed.

(* ============================================================ *)
(* §3 规范数据组合                                                        *)
(* ============================================================ *)

(* 改型分子对正性：0 < |A_n|（规范面恒等沿顶层传送件迁移） *)
Theorem cm_A_pos : forall n : nat, QltT 0 (Qabs ((lna_Amod n) # 1)%Q).
Proof.
  intro n.
  pose proof (fst (snd lna_head_three_legs) n) as Hf.
  apply QltT_to_Qlt in Hf.
  assert (Heq : (Qabs ((lna_Aface n) # 1)%Q)
                == (Qabs ((lna_Amod n) # 1)%Q)).
  { apply Qabs_wd. eapply Qeq_trans.
    - apply qeqT_imp_qeq. apply lna_Aface_eq.
    - apply qeqT_imp_qeq. apply lna_lA_z. }
  rewrite Heq in Hf.
  apply Qlt_to_QltT. exact Hf.
Qed.

(* 线对象同一定义面证明：引擎线与供给线逐字同一（定义性展开即合） *)
Lemma cm_line_dock : forall n : nat,
  cc_line ln2b_X (lna_Amod n) (lna_Bmod n) = ln2b_line lna_Amod lna_Bmod n.
Proof. intro n. unfold cc_line, ln2b_line. reflexivity. Qed.

(* ============================================================ *)
(* §4 载体供给型（单开槽＝恒等式腿下上界对，沿在案登记的未竟项）          *)
(* ============================================================ *)

(* 交付供给型：三肢（正性/下界/上界），单开槽＝下上界对 *)
Definition cm_supply : Set :=
  sigT (fun clo : nat -> Q =>
    And (forall n : nat, QltT 0 (clo n))
      (And (forall n : nat, real_le (real_const (clo n))
                                    (ln2b_line lna_Amod lna_Bmod n))
           (forall n : nat, real_le (ln2b_line lna_Amod lna_Bmod n)
                                    (real_const (q_pow (4 # 5)%Q n))))).

(* 五肢供给型（档位与分子正性两肢已由 §2/§3 无条件消解，余三肢） *)
Definition cm_pade_supply : Set :=
  sigT (fun clo : nat -> Q =>
    And (QltT (4 # 5)%Q (1 # 1)%Q)
      (And (forall n : nat, QltT 0 (Qabs ((lna_Amod n) # 1)%Q))
        (And (forall n : nat, QltT 0 (clo n))
          (And (forall n : nat, real_le (real_const (clo n))
                                        (ln2b_line lna_Amod lna_Bmod n))
               (forall n : nat, real_le (ln2b_line lna_Amod lna_Bmod n)
                                        (real_const (q_pow (4 # 5)%Q n))))))).

(* 五肢折三肢纯投影：档位与正性两肢照 §2/§3 丢弃 *)
Theorem cm_pade_of_supply : cm_pade_supply -> cm_supply.
Proof.
  intros [clo [_ [_ [Hclop [Hlo Hup]]]]].
  exists clo. split.
  - exact Hclop.
  - split.
    + exact Hlo.
    + exact Hup.
Qed.

(* ============================================================ *)
(* §5 分离常数终件                                                        *)
(* ============================================================ *)

(* 终件：供给条件下对一切有理数 u/v 显式给出正分离常数 c 与终归指标 K，
   使 c ≤ |u/v − x_k| 对 k ≥ K 成立（直调两歧引擎，读数沿基准列投影确定） *)
Theorem cm_bound : forall (Hs : cm_supply) (u : Z) (v : positive),
  sigT (fun c : Q => And (QltT 0 c)
    (sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
      QleT' c (Qabs (((u # v)%Q - ln2i_x k)%Q))))).
Proof.
  intros [clo [Hclo [Hlo Hup]]] u v.
  assert (Hup' : forall n : nat,
    real_le (cc_line ln2b_X (lna_Amod n) (lna_Bmod n))
            (real_const (q_pow (4 # 5)%Q n))).
  { intro n. rewrite cm_line_dock. exact (Hup n). }
  assert (Hlo' : forall n : nat,
    real_le (real_const (clo n))
            (cc_line ln2b_X (lna_Amod n) (lna_Bmod n))).
  { intro n. rewrite cm_line_dock. exact (Hlo n). }
  destruct (cc_engine ln2b_X lna_Amod lna_Bmod clo Hup' Hlo' Hclo
             cm_A_pos u v) as [c [Hc0 [K HK]]].
  exists c. split.
  - exact Hc0.
  - exists K. intros k Hk.
    apply (lnt_leT'_eq_r c
             (Qabs (((u # v)%Q - projT1 ln2b_X k)%Q))
             (Qabs (((u # v)%Q - ln2i_x k)%Q))).
    + apply Qabs_wd. rewrite (ln2b_X_proj k). reflexivity.
    + exact (HK k Hk).
Qed.

(* ============================================================ *)
(* §6 数值锚组                                                            *)
(* ============================================================ *)

(* 带窗锚：q = 1 处 (4/5)⁸ < 1/2（使用 conv_core 数值锚） *)
Theorem cm_anchor_band1 : QltT (q_pow (4 # 5)%Q 8) ((1 # 2)%Q).
Proof. exact cc_band_anchor1. Qed.

(* 增长锚：L_1·q̃_1 ≤ 6（vm 判谳） *)
Theorem cm_anchor_growth1 : hl_lcm_upto 1 * bk_Qn_qtilde 1 <= (6 * 1) ^ 1.
Proof. vm_compute. lia. Qed.

(* 首项链面锚：A_1 = 3 与 B_1 = 4/2（使用 assembly 首项锚对） *)
Theorem cm_anchor_chain1 :
  And (QeqT (3 # 1)%Q ((lna_Amod 1) # 1)%Q)
      (QeqT (4 # 2)%Q ((lna_Bmod 1) # 1)%Q).
Proof. split.
  - exact lna_A1_anchor.
  - exact lna_B1_anchor.
Qed.

(* ============================================================ *)
(* 提取与假设审计（零承认复核）                                            *)
(* ============================================================ *)

Separate Extraction cm_bound cm_pade_of_supply.

Print Assumptions cm_fact_le_pow.
Print Assumptions cm_A_le.
Print Assumptions cm_theta_lt1.
Print Assumptions cm_theta_budget_lt1.
Print Assumptions cm_A_pos.
Print Assumptions cm_line_dock.
Print Assumptions cm_pade_of_supply.
Print Assumptions cm_bound.
Print Assumptions cm_anchor_band1.
Print Assumptions cm_anchor_growth1.
Print Assumptions cm_anchor_chain1.
