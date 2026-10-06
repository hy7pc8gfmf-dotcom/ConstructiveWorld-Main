(* ===================================================================== *)
(*  abl_ln2_theta_total.v —— ln2 无理性链·⑦θⁿ 终界装配件（DO 五派主件）     *)
(*  模块名：abl_ln2_theta_total.                                          *)
(*  使命: DH 件（θ 上肢二次衰减核 lnt2_hquad＋θ 预算 lnt2_theta_budget＋   *)
(*        键带组合终形 lnt2_wgap_geo_quarter：尾隙 ≤ 2^{n+2}·(3/4)^{SM−2n}）*)
(*        ＋DW 二派件（层 2 主定理全容器传送 lnt3_wsum_band_total：          *)
(*        S_{M+d} ≤ SM·2ⁿ + d·2ⁿ·ρ^{SM−2n}）＋DU 件（增长预算             *)
(*        lng2_An_le_12pow：A_n := 2ⁿ·q̃_n ≤ 12ⁿ＋合成预算                  *)
(*        lng2_budget_compose：A_n·ρ^{m−2n} ≤ (64/3)ⁿ·ρ^m）三件已闭积木    *)
(*        合成 θⁿ 终界不等式——ln2 无理性「余项被增长压倒」核心步。三层：    *)
(*        【层1·终界合成】θ 尾隙常数（2^{n+2}·ρ^{m−2n}，DH）×增长预算      *)
(*        （A_n ≤ 12ⁿ，DU）竞争判定：lnt4_An_gap_compose（A_n·2^{n+2}·     *)
(*        ρ^{m−2n} ≤ 4·(128/3)ⁿ·ρ^m，κ_eff := 128/3 每n因子显式折叠）；    *)
(*        斜率闭式 lnt4_compete_exp／严格终界 lnt4_theta_lt（SM 斜率 18 >  *)
(*        log_{4/3}(128/3) ≈ 13.05：C₁₈ := (128/3)·(3/4)^18 = 3^17/2^29    *)
(*        ≈ 0.2406 < 1，A_n·余项 < 1 对全 n ≥ 1）；纯预算档 lnt4_budget_lt *)
(*        （斜率 11 > log_{4/3}(64/3) ≈ 10.64：C₁₁ := (64/3)·(3/4)^11 =    *)
(*        3^10/2^16 ≈ 0.9009 < 1——DU 头注预告的斜率判定）；DH θ 预算真使用 *)
(*        lnt4_theta_budget_consume（(7/10)ⁿ ≤ (4/5)ⁿ 沿用 lnt2_theta_    *)
(*        budget）与主项严格面 lnt4_theta_budget_lt（(4/5)ⁿ < 1）。        *)
(*        【层2·传送肢接入】DW 全容器面真使用：lnt4_total_budget          *)
(*        （A_n·S_{M+d} ≤ SM·24ⁿ + d·(128/3)ⁿ·ρ^SM：头窗 lng2_An_le_12pow *)
(*        折 24ⁿ = 2ⁿ·12ⁿ、尾窗 lng2_budget_compose 折 (128/3)ⁿ·ρ^SM——    *)
(*        终界不等式 RHS 传送）；DH 隙面互补使用 lnt4_total_gap_budget    *)
(*        （A_n·S_{M+d} ≤ A_n·S_M + 4·(128/3)ⁿ·ρ^SM，经                  *)
(*        lnt2_wgap_geo_quarter）；斜率闭式 lnt4_total_slope。            *)
(*        【层3·装配形】「余项被增长压倒」核心步 sigT/严格 Set 面：        *)
(*        lnt4_remainder_sig（见证 B := 4·C₁₈ = 3^17/2^27 < 1 的 sigT 积  *)
(*        载体）＋lnt4_theta_final（严格余项步 × 全容器斜率闭式的 S01 And *)
(*        合成闭式：余项 < 1 与 A_n·S_{M+d} ≤ SM·24ⁿ + d·C₁₈ⁿ 同框）。    *)
(*  依赖: Stdlib QArith/List/Arith/ZArith/Lia；S01_BaseRing S02_Cauchy-   *)
(*        Complete S03_QExp PolyIntegral PadeErrorIntegral BeukersLists    *)
(*        BeukersVariant PintMono PsQReindex；池内平铺链（三池件拷入，     *)
(*        链序头注实拍）：abl_ln2_numer_int → abl_qpoly_divmod →          *)
(*        abl_qpoly_divmod_gen → abl_ln2_qpoly_consume → abl_ln2_qpoly_gen *)
(*        → abl_ln2_growth_budget（DU 池 ln2_growth/ 拷入）→              *)
(*        abl_ln2_tail_bound → abl_ln2_sharp_weight → abl_ln2_theta_upper *)
(*        （DH 池 ln2_theta/ 拷入）→ abl_ln2_transfer_limb（DW 池         *)
(*        ln2_transfer/ 拷入）→ 本件。真使用清单：DH lnt2_theta_budget＋   *)
(*        lnt2_wgap_geo_quarter；DW lnt3_wsum_band_total；DU              *)
(*        lng2_An_le_12pow＋lng2_budget_compose（五件全衔接）。            *)
(*  对标: Beukers 1979 ln2 锐权变体「余项被增长压倒」核心步（AE §3.3/§3.4  *)
(*        预算合成：分母尺度 A_n ≤ 12ⁿ 被尾隙衰减 ρ^{SM−2n} 压倒的斜率     *)
(*        阈——增长不吞掉衰减的机验判定）；DP 二派完成度图剩余主峰          *)
(*        「θⁿ 终界装配件」闭合位（DP2 件 lnr2_wgap_geo 系 DH             *)
(*        lnt2_wgap_geo_quarter 的逐字使用名，本链经 theta_upper 天然覆盖）*)
(*        。诚实边界：I'_n 真 Real 积分机库内不在册，本件以有理求和容器面  *)
(*        承载传送（DW 件同口径）；ln2 无理性的收敛位（p_n/q_n 逼近形）    *)
(*        为下游缺口，本件不冒领。                                        *)
(*  构造性: 纯构造性、零承认件；语句面全 Set（QeqT/QleT'/QltT＋S01 And    *)
(*        积载体＋sigT 见证；Qeq/Qle 仅支撑面作推理）；新立假设位＝0       *)
(*        （1 ≤ n、18n ≤ m、2n ≤ M+1 等前提均为语句输入槽的当场消解形，    *)
(*        非遗漏假设）；见证全显式（lnt4_remainder_sig 的 B :=            *)
(*        3^17/2^27 封闭有理数）；文尾 Print Assumptions 取证块全 Closed   *)
(*        ＋Separate Extraction 闭合（四关证据）。                        *)
(*  编译配方: cd ConstructiveWorld && source Live/toolchain/env.sh &&     *)
(*        unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c      *)
(*        -native-compiler no -Q vo_local_world_unified_0930 "" -Q . ""   *)
(*        本件（独占沙箱池 ln2_theta_total/，链序如上先编，道闸≤1 单道     *)
(*        串行）。                                                        *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral PadeErrorIntegral BeukersLists BeukersVariant PintMono.
Require Import PsQReindex.
Require Import abl_ln2_tail_bound abl_ln2_sharp_weight.
Require Import abl_ln2_numer_int abl_ln2_qpoly_gen.
Require Import abl_ln2_growth_budget.
Require Import abl_ln2_theta_upper abl_ln2_transfer_limb.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 工器件：nat-Q 非负桥、幂正性、2 幂折叠、幂分解、幂底自界              *)
(* ============================================================ *)

(** nat 数的 Q 非负桥：QleT' 0 (k#1)。 *)
Lemma lnt4_Znat_nonneg : forall k : nat, QleT' 0 ((Z.of_nat k # 1)%Q).
Proof.
  intro k. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(** 2 幂正性（QleT' 面）。 *)
Lemma lnt4_pow2_nonneg : forall k : nat, QleT' 0 (q_pow (2 # 1)%Q k).
Proof.
  intro k. apply Qle_to_QleT'. apply Qlt_le_weak. apply lnt_pow2_pos.
Qed.

(** (64/3) 幂正性（QleT' 面）。 *)
Lemma lnt4_pow64_nonneg : forall k : nat, QleT' 0 (q_pow (64 # 3)%Q k).
Proof.
  intro k. apply Qle_to_QleT'. apply lnt2_pow_nonneg.
  unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(** (128/3) 幂正性（QleT' 面）。 *)
Lemma lnt4_pow128_nonneg : forall k : nat, QleT' 0 (q_pow (128 # 3)%Q k).
Proof.
  intro k. apply Qle_to_QleT'. apply lnt2_pow_nonneg.
  unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(** 2^{n+2} = 4·2ⁿ（θ 尾隙常数 2^{n+2} 的显式分解原子）。 *)
Lemma lnt4_pow2_SS : forall n : nat,
  q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
  == ((4 # 1)%Q * q_pow (2 # 1)%Q n)%Q.
Proof.
  intro n. replace (Datatypes.S (Datatypes.S n)) with (2 + n) by lia.
  rewrite q_pow_add. cbn [q_pow]. ring.
Qed.

(** 2 幂折叠·24 档：2ⁿ·(c·12ⁿ) == c·24ⁿ（层2 头窗折算 2ⁿ·12ⁿ）。 *)
Lemma lnt4_fold_24 : forall (n : nat) (c : Q),
  (q_pow (2 # 1)%Q n * (c * q_pow (12 # 1)%Q n))%Q == (c * q_pow (24 # 1)%Q n)%Q.
Proof.
  intros n c.
  transitivity ((c * (q_pow (2 # 1)%Q n * q_pow (12 # 1)%Q n))%Q).
  - ring.
  - rewrite <- (bk_q_pow_mul (2 # 1)%Q (12 # 1)%Q n).
    rewrite (lng_qpow_congr ((2 # 1)%Q * (12 # 1)%Q) (24 # 1)%Q n).
    + reflexivity.
    + reflexivity.
Qed.

(** 2 幂折叠·128 档：2ⁿ·(c·(64/3)ⁿ) == c·(128/3)ⁿ（层2 尾窗折算 2ⁿ·(64/3)ⁿ）。 *)
Lemma lnt4_fold_128 : forall (n : nat) (c : Q),
  (q_pow (2 # 1)%Q n * (c * q_pow (64 # 3)%Q n))%Q == (c * q_pow (128 # 3)%Q n)%Q.
Proof.
  intros n c.
  transitivity ((c * (q_pow (2 # 1)%Q n * q_pow (64 # 3)%Q n))%Q).
  - ring.
  - rewrite <- (bk_q_pow_mul (2 # 1)%Q (64 # 3)%Q n).
    rewrite (lng_qpow_congr ((2 # 1)%Q * (64 # 3)%Q) (128 # 3)%Q n).
    + reflexivity.
    + reflexivity.
Qed.

(** 2 幂折叠·128 档带尾因子：2ⁿ·(c·((64/3)ⁿ·r)) == c·((128/3)ⁿ·r)。 *)
Lemma lnt4_fold_128r : forall (n : nat) (c r : Q),
  (q_pow (2 # 1)%Q n * (c * (q_pow (64 # 3)%Q n * r)))%Q
  == (c * (q_pow (128 # 3)%Q n * r))%Q.
Proof.
  intros n c r.
  transitivity ((c * ((q_pow (2 # 1)%Q n * q_pow (64 # 3)%Q n) * r))%Q).
  - ring.
  - rewrite <- (bk_q_pow_mul (2 # 1)%Q (64 # 3)%Q n).
    rewrite (lng_qpow_congr ((2 # 1)%Q * (64 # 3)%Q) (128 # 3)%Q n).
    + reflexivity.
    + reflexivity.
Qed.

(** q_pow 与 Z 幂面的字面底桥：q_pow (2#1)ⁿ == (2ⁿ#1)（bk_Qmul_nat 归纳）。 *)
Lemma lnt4_qpow2_Z : forall n : nat,
  q_pow (2 # 1)%Q n == ((Z.of_nat (2 ^ n) # 1)%Q).
Proof.
  intro n. induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow Nat.pow]. rewrite IH.
    change (2 # 1)%Q with ((Z.of_nat 2 # 1)%Q). apply bk_Qmul_nat.
Qed.

(** q_pow 与 Z 幂面的字面底桥：q_pow (24#1)ⁿ == (24ⁿ#1)。 *)
Lemma lnt4_qpow24_Z : forall n : nat,
  q_pow (24 # 1)%Q n == ((Z.of_nat (24 ^ n) # 1)%Q).
Proof.
  intro n. induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow Nat.pow]. rewrite IH.
    change (24 # 1)%Q with ((Z.of_nat 24 # 1)%Q). apply bk_Qmul_nat.
Qed.

(** 层2 头窗折算恒等式（Z 幂面版）：c·(2ⁿ·(12ⁿ#1)) == c·24ⁿ——
    DU 增长预算 A_n ≤ 12ⁿ 的 (Z.of_nat (12^n)#1) 面与 24ⁿ = 2ⁿ·12ⁿ 的
    显式合成（头窗 SM·24ⁿ 折算的精确形）。 *)
Lemma lnt4_24fold_eq : forall (n : nat) (c : Q),
  (c * (q_pow (2 # 1)%Q n * ((Z.of_nat (12 ^ n) # 1)%Q)))%Q
  == (c * q_pow (24 # 1)%Q n)%Q.
Proof.
  intros n c.
  transitivity ((c * (((Z.of_nat (2 ^ n) # 1)%Q) *
                        ((Z.of_nat (12 ^ n) # 1)%Q)))%Q).
  - rewrite (lnt4_qpow2_Z n). reflexivity.
  - transitivity ((c * ((Z.of_nat (2 ^ n * 12 ^ n) # 1)%Q))%Q).
    + rewrite (bk_Qmul_nat (2 ^ n) (12 ^ n)). reflexivity.
    + assert (HE : 2 ^ n * 12 ^ n = 24 ^ n)
        by (symmetry; change (24 ^ n) with ((2 * 12) ^ n); apply lng2_pow_mul_l).
      rewrite HE. rewrite <- (lnt4_qpow24_Z n). reflexivity.
Qed.

(** 幂分解：q_pow (a·b^k) n == q_pow a n·q_pow b (k·n)——斜率竞争的
    「κ·ρ^c 折单底幂」核：((128/3)·ρ^18)ⁿ == (128/3)ⁿ·ρ^{18n}。 *)
Lemma lnt4_qpow_scale : forall (a b : Q) (k n : nat),
  q_pow (a * q_pow b k)%Q n == (q_pow a n * q_pow b (k * n))%Q.
Proof.
  intros a b k n. induction n as [| n IH].
  - cbn [q_pow]. rewrite Nat.mul_0_r. cbn [q_pow]. ring.
  - cbn [q_pow]. rewrite Nat.mul_succ_r, q_pow_add. rewrite IH. ring.
Qed.

(** 幂底自界：0 ≤ x ≤ 1 ⟹ x^{S k} ≤ x——衰减底幂收单因子（n ≥ 1 档）。 *)
Lemma lnt4_pow_le_self : forall (x : Q) (k : nat),
  QleT' 0 x -> QleT' x 1 -> QleT' (q_pow x (Datatypes.S k)) x.
Proof.
  intros x k H0 H1.
  assert (Hpk : Qle (q_pow x k) 1%Q).
  { pose proof (lnt2_pow_mono k x (1 # 1)%Q (QleT'_to_Qle _ _ H0)
                  (QleT'_to_Qle _ _ H1)) as Hp.
    rewrite bk_q_pow_one in Hp. exact Hp. }
  apply (lnt_leT'_eq_l ((x * q_pow x k)%Q) (q_pow x (Datatypes.S k)) x).  - apply Qeq_sym. apply q_pow_succ.
  - apply (lnt_leT'_eq_r ((x * q_pow x k)%Q) ((x * 1)%Q) x).
    + ring.
    + apply (qleT'_mult_compat_l (q_pow x k) 1%Q x H0).
      apply Qle_to_QleT'. exact Hpk.
Qed.

(** 合成预算语句级的乘法重排桥（层1 主件与层2 隙面共用）。 *)
Lemma lnt4_gap_lhs_eq : forall (n m : nat),
  ((Z.of_nat (lng2_An n) # 1)%Q *
     (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
        q_pow (3 # 4)%Q (m - 2 * n)))%Q
  == ((q_pow (3 # 4)%Q (m - 2 * n) * (Z.of_nat (lng2_An n) # 1)%Q) *
        q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q.
Proof. intros n m. ring. Qed.

(* ============================================================ *)
(* §1 层1·终界合成：θ 尾隙常数（DH）× 增长预算（DU）的竞争判定              *)
(* ============================================================ *)

(** ★合成预算·主件（层1）：2n ≤ m ⟹ A_n·2^{n+2}·ρ^{m−2n} ≤ 4·(128/3)ⁿ·ρ^m
    ——DU 件 lng2_budget_compose（A_n·ρ^{m−2n} ≤ (64/3)ⁿ·ρ^m）经 θ 尾隙
    常数 2^{n+2} 缩放、κ_eff := 128/3 = 2·(64/3) 的每 n 因子显式折叠：
    增长预算与衰减预算同框竞争的合成形。 *)
Theorem lnt4_An_gap_compose : forall (n m : nat), 2 * n <= m ->
  QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
            (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
               q_pow (3 # 4)%Q (m - 2 * n)))%Q)
        (((4 # 1)%Q * (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q m))%Q).
Proof.
  intros n m Hm.
  pose proof (lng2_budget_compose n m Hm) as Hbc.
  pose proof (lnt4_pow2_nonneg (Datatypes.S (Datatypes.S n))) as H2p.
  assert (Hsc : QleT' (((q_pow (3 # 4)%Q (m - 2 * n) *
                          (Z.of_nat (lng2_An n) # 1)%Q))%Q
                         * q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q
                      (((q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m))%Q
                         * q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q).
  { apply (qleT'_mult_compat_r
             (q_pow (3 # 4)%Q (m - 2 * n) * (Z.of_nat (lng2_An n) # 1)%Q)%Q
             (q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m)%Q
             (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))) H2p Hbc). }
  apply (qleT'_trans
          (((Z.of_nat (lng2_An n) # 1)%Q *
             (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                q_pow (3 # 4)%Q (m - 2 * n)))%Q)
          (((q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m) *
             q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q)
          (((4 # 1)%Q * (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q m))%Q)).
  - apply (lnt_leT'_eq_l
             (((q_pow (3 # 4)%Q (m - 2 * n) * (Z.of_nat (lng2_An n) # 1)%Q) *
                q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q)
             (((Z.of_nat (lng2_An n) # 1)%Q *
                (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                   q_pow (3 # 4)%Q (m - 2 * n)))%Q)
             (((q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m) *
                q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q)).
    + apply (Qeq_sym _ _ (lnt4_gap_lhs_eq n m)).
    + exact Hsc.
  - apply (lnt_leT'_eq_r
             (((q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m) *
                q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q)
             ((q_pow (2 # 1)%Q n *
                ((4 # 1)%Q * (q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m)))%Q)
             (((4 # 1)%Q * (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q m))%Q)).
    + rewrite (lnt4_fold_128r n (4 # 1)%Q (q_pow (3 # 4)%Q m)). reflexivity.
    + apply qeq_leT'. rewrite (lnt4_pow2_SS n). ring.
Qed.

(** DH θ 预算真使用：4ⁿ·(7/40)ⁿ = (7/10)ⁿ ≤ (4/5)ⁿ 的 (7/10)ⁿ 面重述
    （lnt2_theta_budget 沿 bk_q_pow_mul 底积恒等式的显式折算）。 *)
Theorem lnt4_theta_budget_consume : forall n : nat,
  QleT' (q_pow (7 # 10)%Q n) (q_pow (4 # 5)%Q n).
Proof.
  intro n.
  pose proof (lnt2_theta_budget n) as Htb.
  assert (Heq : q_pow (7 # 10)%Q n
                == (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n)%Q).
  { rewrite <- (bk_q_pow_mul (4 # 1)%Q (7 # 40)%Q n).
    apply (lng_qpow_congr (7 # 10)%Q ((4 # 1)%Q * (7 # 40)%Q)%Q n).
    reflexivity. }
  apply (lnt_leT'_eq_l
           ((q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n)%Q)
           (q_pow (7 # 10)%Q n) (q_pow (4 # 5)%Q n)).
  - exact (Qeq_sym _ _ Heq).
  - exact Htb.
Qed.

(** DH θ 主预算严格面：1 ≤ n ⟹ (4/5)ⁿ < 1（θ := 4/5 命名核的 < 1 闭合）。 *)
Theorem lnt4_theta_budget_lt : forall n : nat, 1 <= n -> QltT (q_pow (4 # 5)%Q n) 1%Q.
Proof.
  intros n Hn. destruct n as [| k].
  - exfalso. lia.
  - eapply qleT'_ltT_ltT.
    + apply (lnt4_pow_le_self _ k); vm_compute; reflexivity.
    + vm_compute. reflexivity.
Qed.

(** 层1·斜率竞争闭式：18n ≤ m ⟹ A_n·2^{n+2}·ρ^{m−2n} ≤ 4·C₁₈ⁿ
    （C₁₈ := (128/3)·(3/4)^18 = 3^17/2^29 ≈ 0.2406——衰减压倒增长的
    指数闭式：κ_eff·ρ^18 = C₁₈ < 1/4，即斜率阈 log_{4/3}(128/3) ≈ 13.05）。 *)
Theorem lnt4_compete_exp : forall (n m : nat), 18 * n <= m ->
  QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
            (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
               q_pow (3 # 4)%Q (m - 2 * n)))%Q)
        (((4 # 1)%Q * q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)%Q).
Proof.
  intros n m Hm.
  assert (Hm2 : 2 * n <= m) by lia.
  pose proof (lnt4_An_gap_compose n m Hm2) as Hg.
  pose proof (lnt3_rho_pow_anti (18 * n) m Hm) as Hra.
  pose proof (qleT'_mult_compat_l (q_pow (3 # 4)%Q m) (q_pow (3 # 4)%Q (18 * n))
                (q_pow (128 # 3)%Q n) (lnt4_pow128_nonneg n) Hra) as Hs.
  apply (qleT'_trans
          (((Z.of_nat (lng2_An n) # 1)%Q *
             (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                q_pow (3 # 4)%Q (m - 2 * n)))%Q)
          (((4 # 1)%Q * (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q m))%Q)
          (((4 # 1)%Q * q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)%Q)).
  - exact Hg.
  - apply (lnt_leT'_eq_r
             (((4 # 1)%Q * (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q m))%Q)
             (((4 # 1)%Q * (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q (18 * n)))%Q)
             (((4 # 1)%Q * q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)%Q)).
    + rewrite <- (lnt4_qpow_scale (128 # 3)%Q (3 # 4)%Q 18 n). reflexivity.
    + apply (qleT'_mult_compat_l
                (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q m)%Q
                (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q (18 * n))%Q
                (4 # 1)%Q lnt_q4_le0 Hs).
Qed.

(** 层1·斜率锚组（C₁₈ 判定，pow_le_self 与严格终界的使用位）。 *)
Lemma lnt4_anchor_C18_0 : QleT' 0 ((128 # 3)%Q * q_pow (3 # 4)%Q 18)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma lnt4_anchor_C18_le1 : QleT' ((128 # 3)%Q * q_pow (3 # 4)%Q 18) 1%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma lnt4_anchor_B18_lt1 :
  QltT (((4 # 1)%Q * ((128 # 3)%Q * q_pow (3 # 4)%Q 18))%Q) 1%Q.
Proof. vm_compute. reflexivity. Qed.

(** 层1·斜率锚组（C₁₁ 判定）。 *)
Lemma lnt4_anchor_C11_0 : QleT' 0 ((64 # 3)%Q * q_pow (3 # 4)%Q 11)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma lnt4_anchor_C11_le1 : QleT' ((64 # 3)%Q * q_pow (3 # 4)%Q 11) 1%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma lnt4_anchor_C11_lt1 : QltT ((64 # 3)%Q * q_pow (3 # 4)%Q 11) 1%Q.
Proof. vm_compute. reflexivity. Qed.

(** ★层1·严格终界（「余项被增长压倒」主判据）：1 ≤ n、18n ≤ m ⟹
    A_n·2^{n+2}·ρ^{m−2n} < 1——分母尺度增长（A_n ≤ 12ⁿ）被尾隙衰减
    （ρ^{m−2n}）压倒：增长不吞掉衰减的全 n ≥ 1 判定（斜率 18 档）。 *)
Theorem lnt4_theta_lt : forall (n m : nat), 1 <= n -> 18 * n <= m ->
  QltT (((Z.of_nat (lng2_An n) # 1)%Q *
           (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
              q_pow (3 # 4)%Q (m - 2 * n)))%Q) 1%Q.
Proof.
  intros n m Hn Hm. destruct n as [| k].
  - exfalso. lia.
  - apply (qleT'_ltT_ltT
              (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                  (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S k))) *
                     q_pow (3 # 4)%Q (m - 2 * Datatypes.S k)))%Q)
              (((4 # 1)%Q * ((128 # 3)%Q * q_pow (3 # 4)%Q 18))%Q) 1%Q).
    + apply (qleT'_trans
                (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                   (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S k))) *
                      q_pow (3 # 4)%Q (m - 2 * Datatypes.S k)))%Q)
                (((4 # 1)%Q *
                    q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) (Datatypes.S k))%Q)
                (((4 # 1)%Q * ((128 # 3)%Q * q_pow (3 # 4)%Q 18))%Q)).
      * apply (lnt4_compete_exp (Datatypes.S k) m Hm).
      * apply (qleT'_mult_compat_l
                  (q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) (Datatypes.S k))
                  ((128 # 3)%Q * q_pow (3 # 4)%Q 18) (4 # 1)%Q lnt_q4_le0).
        apply (lnt4_pow_le_self _ k).
        -- exact lnt4_anchor_C18_0.
        -- exact lnt4_anchor_C18_le1.
    + exact lnt4_anchor_B18_lt1.
Qed.

(** ★层1·纯预算档严格终界（DU 斜率判定）：1 ≤ n、11n ≤ m ⟹
    A_n·ρ^{m−2n} < 1——C₁₁ := (64/3)·(3/4)^11 = 3^10/2^16 ≈ 0.9009 < 1，
    斜率阈 log_{4/3}(64/3) ≈ 10.64（DU 头注预告档）：不抽 2^{n+2} 常数时
    衰减压倒增长的更锐斜率。 *)
Theorem lnt4_budget_lt : forall (n m : nat), 1 <= n -> 11 * n <= m ->
  QltT (((Z.of_nat (lng2_An n) # 1)%Q * q_pow (3 # 4)%Q (m - 2 * n))%Q) 1%Q.
Proof.
  intros n m Hn Hm. destruct n as [| k].
  - exfalso. lia.
  - assert (Hm2 : 2 * Datatypes.S k <= m) by lia.
    pose proof (lng2_budget_compose (Datatypes.S k) m Hm2) as Hbc.
    assert (Hm11 : 11 * Datatypes.S k <= m) by exact Hm.
    pose proof (lnt3_rho_pow_anti (11 * Datatypes.S k) m Hm11) as Hra.
    pose proof (qleT'_mult_compat_l (q_pow (3 # 4)%Q m)
                  (q_pow (3 # 4)%Q (11 * Datatypes.S k)) (q_pow (64 # 3)%Q (Datatypes.S k))
                  (lnt4_pow64_nonneg (Datatypes.S k)) Hra) as Hs.
    apply (qleT'_ltT_ltT
              (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                  q_pow (3 # 4)%Q (m - 2 * Datatypes.S k))%Q)
              ((64 # 3)%Q * q_pow (3 # 4)%Q 11)%Q 1%Q).
    + apply (qleT'_trans
                (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                    q_pow (3 # 4)%Q (m - 2 * Datatypes.S k))%Q)
                (q_pow ((64 # 3)%Q * q_pow (3 # 4)%Q 11) (Datatypes.S k))
                ((64 # 3)%Q * q_pow (3 # 4)%Q 11)%Q).
      * apply (lnt_leT'_eq_r
                  (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                      q_pow (3 # 4)%Q (m - 2 * Datatypes.S k))%Q)
                  ((q_pow (64 # 3)%Q (Datatypes.S k) * q_pow (3 # 4)%Q (11 * Datatypes.S k))%Q)
                  (q_pow ((64 # 3)%Q * q_pow (3 # 4)%Q 11) (Datatypes.S k))).
        -- rewrite <- (lnt4_qpow_scale (64 # 3)%Q (3 # 4)%Q 11 (Datatypes.S k)).
           reflexivity.
        -- apply (qleT'_trans
                     (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                        q_pow (3 # 4)%Q (m - 2 * Datatypes.S k))%Q)
                     ((q_pow (64 # 3)%Q (Datatypes.S k) * q_pow (3 # 4)%Q m)%Q)
                     ((q_pow (64 # 3)%Q (Datatypes.S k) * q_pow (3 # 4)%Q (11 * Datatypes.S k))%Q)).
           ++ apply (lnt_leT'_eq_l
                       ((q_pow (3 # 4)%Q (m - 2 * Datatypes.S k) *
                          (Z.of_nat (lng2_An (Datatypes.S k)) # 1))%Q)
                       (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                          q_pow (3 # 4)%Q (m - 2 * Datatypes.S k))%Q)
                       ((q_pow (64 # 3)%Q (Datatypes.S k) *
                           q_pow (3 # 4)%Q m)%Q)).
              ** ring.
              ** exact Hbc.
           ++ exact Hs.
      * apply (lnt4_pow_le_self _ k).
        -- exact lnt4_anchor_C11_0.
        -- exact lnt4_anchor_C11_le1.
    + exact lnt4_anchor_C11_lt1.
Qed.

(* ============================================================ *)
(* §2 层2·传送肢接入：DW 全容器面（RHS 传送）＋DH 隙面互补                 *)
(* ============================================================ *)

(** ★层2·全容器 RHS 传送（DW 件真使用）：1 ≤ n、2n ≤ M+1 ⟹
    A_n·S_{M+d} ≤ SM·24ⁿ + d·(128/3)ⁿ·ρ^SM——DW 主定理 lnt3_wsum_band_total
    （S_{M+d} ≤ SM·2ⁿ + d·2ⁿ·ρ^{SM−2n}）整体系配分母 A_n 后：头窗经
    lng2_An_le_12pow 折 24ⁿ = 2ⁿ·12ⁿ、尾窗经 lng2_budget_compose 折
    (128/3)ⁿ·ρ^SM 的显式合成。 *)
Theorem lnt4_total_budget : forall (n M d : nat), 1 <= n -> 2 * n <= M + 1 ->
  QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
            sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
        (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n
          + (Z.of_nat d # 1) *
              (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q (Datatypes.S M)))%Q).
Proof.
  intros n M d Hn HM.
  pose proof (lnt3_wsum_band_total n M d Hn HM) as Hwt.
  assert (HAn : QleT' ((Z.of_nat (lng2_An n) # 1)%Q) ((Z.of_nat (12 ^ n) # 1)%Q)).
  { apply Qle_to_QleT'. apply bk_Qle_nat. apply lng2_An_le_12pow. }
  assert (Hscale : QleT' ((q_pow (2 # 1)%Q n * (Z.of_nat (lng2_An n) # 1)%Q)%Q)
                         ((q_pow (2 # 1)%Q n * ((Z.of_nat (12 ^ n) # 1)%Q))%Q)).
  { apply (qleT'_mult_compat_l (Z.of_nat (lng2_An n) # 1) (Z.of_nat (12 ^ n) # 1)
             (q_pow (2 # 1)%Q n) (lnt4_pow2_nonneg n) HAn). }
  assert (Hsm2 : QleT' (((Z.of_nat (Datatypes.S M) # 1) *
                           (q_pow (2 # 1)%Q n * (Z.of_nat (lng2_An n) # 1)%Q))%Q)
                       (((Z.of_nat (Datatypes.S M) # 1) *
                           (q_pow (2 # 1)%Q n * ((Z.of_nat (12 ^ n) # 1)%Q)))%Q)).
  { apply (qleT'_mult_compat_l
             (q_pow (2 # 1)%Q n * (Z.of_nat (lng2_An n) # 1)%Q)%Q
             (q_pow (2 # 1)%Q n * ((Z.of_nat (12 ^ n) # 1)%Q))%Q
             (Z.of_nat (Datatypes.S M) # 1)
             (lnt4_Znat_nonneg (Datatypes.S M)) Hscale). }
  assert (Hp1 : QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
                          ((Z.of_nat (Datatypes.S M) # 1) *
                             q_pow (2 # 1)%Q n))%Q)
                      (((Z.of_nat (Datatypes.S M) # 1) *
                          q_pow (24 # 1)%Q n))%Q).
  { apply (lnt_leT'_eq_l
             (((Z.of_nat (Datatypes.S M) # 1) *
                (q_pow (2 # 1)%Q n * (Z.of_nat (lng2_An n) # 1)%Q))%Q)
             (((Z.of_nat (lng2_An n) # 1)%Q *
                ((Z.of_nat (Datatypes.S M) # 1) * q_pow (2 # 1)%Q n))%Q)
             (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n))%Q).
    - ring.
    - apply (lnt_leT'_eq_r
                (((Z.of_nat (Datatypes.S M) # 1) *
                   (q_pow (2 # 1)%Q n * (Z.of_nat (lng2_An n) # 1)%Q))%Q)
                (((Z.of_nat (Datatypes.S M) # 1) *
                   (q_pow (2 # 1)%Q n * ((Z.of_nat (12 ^ n) # 1)%Q)))%Q)
                (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n))%Q).
      + exact (lnt4_24fold_eq n (Z.of_nat (Datatypes.S M) # 1)).
      + exact Hsm2.
  }
  assert (Hbc : QleT' ((q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                          (Z.of_nat (lng2_An n) # 1)%Q)%Q)
                      ((q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q (Datatypes.S M)))%Q).
  { apply (lng2_budget_compose n (Datatypes.S M)). lia. }
  assert (Hs1 : QleT' (((Z.of_nat d # 1) *
                          (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                             (Z.of_nat (lng2_An n) # 1)%Q))%Q)
                      (((Z.of_nat d # 1) *
                          (q_pow (64 # 3)%Q n *
                             q_pow (3 # 4)%Q (Datatypes.S M)))%Q)).
  { apply (qleT'_mult_compat_l
             (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                (Z.of_nat (lng2_An n) # 1)%Q)%Q
             (q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q (Datatypes.S M))%Q
             (Z.of_nat d # 1) (lnt4_Znat_nonneg d) Hbc). }
  assert (Hs2 : QleT' ((q_pow (2 # 1)%Q n *
                          ((Z.of_nat d # 1) *
                             (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                                (Z.of_nat (lng2_An n) # 1)%Q)))%Q)
                      ((q_pow (2 # 1)%Q n *
                          ((Z.of_nat d # 1) *
                             (q_pow (64 # 3)%Q n *
                                q_pow (3 # 4)%Q (Datatypes.S M))))%Q)).
  { apply (qleT'_mult_compat_l
             ((Z.of_nat d # 1) *
                (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                   (Z.of_nat (lng2_An n) # 1)%Q))%Q
             ((Z.of_nat d # 1) *
                (q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q (Datatypes.S M)))%Q
             (q_pow (2 # 1)%Q n) (lnt4_pow2_nonneg n) Hs1). }
  assert (Hp2 : QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
                          ((Z.of_nat d # 1) *
                             (q_pow (2 # 1)%Q n *
                                q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))))%Q)
                      (((Z.of_nat d # 1) *
                          (q_pow (128 # 3)%Q n *
                             q_pow (3 # 4)%Q (Datatypes.S M)))%Q)).
  { apply (lnt_leT'_eq_l
             ((q_pow (2 # 1)%Q n *
                ((Z.of_nat d # 1) *
                   (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                      (Z.of_nat (lng2_An n) # 1)%Q)))%Q)
             (((Z.of_nat (lng2_An n) # 1)%Q *
                ((Z.of_nat d # 1) *
                   (q_pow (2 # 1)%Q n *
                      q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))))%Q)
             (((Z.of_nat d # 1) *
                (q_pow (128 # 3)%Q n *
                   q_pow (3 # 4)%Q (Datatypes.S M)))%Q)).
    - ring.
    - apply (lnt_leT'_eq_r
                ((q_pow (2 # 1)%Q n *
                   ((Z.of_nat d # 1) *
                      (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                         (Z.of_nat (lng2_An n) # 1)%Q)))%Q)
                ((q_pow (2 # 1)%Q n *
                   ((Z.of_nat d # 1) *
                      (q_pow (64 # 3)%Q n *
                         q_pow (3 # 4)%Q (Datatypes.S M))))%Q)
                (((Z.of_nat d # 1) *
                    (q_pow (128 # 3)%Q n *
                       q_pow (3 # 4)%Q (Datatypes.S M)))%Q)).
      + rewrite (lnt4_fold_128r n (Z.of_nat d # 1)
                   (q_pow (3 # 4)%Q (Datatypes.S M))). reflexivity.
      + exact Hs2.
  }
  apply (qleT'_trans
          (((Z.of_nat (lng2_An n) # 1)%Q *
              sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
          (((Z.of_nat (lng2_An n) # 1)%Q *
              ((Z.of_nat (Datatypes.S M) # 1) * q_pow (2 # 1)%Q n
               + (Z.of_nat d # 1) *
                   (q_pow (2 # 1)%Q n *
                      q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))))%Q)
          (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n
            + (Z.of_nat d # 1) *
                (q_pow (128 # 3)%Q n *
                   q_pow (3 # 4)%Q (Datatypes.S M)))%Q)).
  - apply (qleT'_mult_compat_l
              (sum_upto (Datatypes.S (M + d)) (lnw_wterm n))
              ((Z.of_nat (Datatypes.S M) # 1) * q_pow (2 # 1)%Q n
               + (Z.of_nat d # 1) *
                   (q_pow (2 # 1)%Q n *
                      q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q
              (Z.of_nat (lng2_An n) # 1)
              (lnt4_Znat_nonneg (lng2_An n)) Hwt).
  - apply (lnt_leT'_eq_l
              (((Z.of_nat (lng2_An n) # 1)%Q *
                  ((Z.of_nat (Datatypes.S M) # 1) * q_pow (2 # 1)%Q n)
                + (Z.of_nat (lng2_An n) # 1)%Q *
                    ((Z.of_nat d # 1) *
                       (q_pow (2 # 1)%Q n *
                          q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))))%Q)
              (((Z.of_nat (lng2_An n) # 1)%Q *
                  ((Z.of_nat (Datatypes.S M) # 1) * q_pow (2 # 1)%Q n
                   + (Z.of_nat d # 1) *
                       (q_pow (2 # 1)%Q n *
                          q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))))%Q)
              (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n
                + (Z.of_nat d # 1) *
                    (q_pow (128 # 3)%Q n *
                       q_pow (3 # 4)%Q (Datatypes.S M)))%Q)).
    + ring.
    + apply (qleT'_plus_compat _ _ _ _ Hp1 Hp2).
Qed.

(** ★层2·DH 隙面互补传送（DH 件真使用）：1 ≤ n、2n ≤ M+1 ⟹
    A_n·S_{M+d} ≤ A_n·S_M + 4·(128/3)ⁿ·ρ^SM——DH 组合终形
    lnt2_wgap_geo_quarter（S_{M+d} ≤ S_M + 2^{n+2}·ρ^{SM−2n}）配分母
    A_n 后，隙项经 lnt4_An_gap_compose 折算的加法隙形（与 total_budget
    的 DW 头窗形互补：此形保留 A_n·S_M 主和面）。 *)
Theorem lnt4_total_gap_budget : forall (n M d : nat), 1 <= n -> 2 * n <= M + 1 ->
  QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
            sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
        (((Z.of_nat (lng2_An n) # 1)%Q *
            sum_upto (Datatypes.S M) (lnw_wterm n)
          + ((4 # 1)%Q * (q_pow (128 # 3)%Q n *
                              q_pow (3 # 4)%Q (Datatypes.S M)))%Q)%Q).
Proof.
  intros n M d Hn HM.
  assert (Hm2 : 2 * n <= Datatypes.S M) by lia.
  pose proof (lnt2_wgap_geo_quarter n M d Hn HM) as Hgap.
  pose proof (lnt4_An_gap_compose n (Datatypes.S M) Hm2) as Hbc.
  pose proof (lnt4_Znat_nonneg (lng2_An n)) as HAn0.
  assert (H1 : QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
                          sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
                     (((Z.of_nat (lng2_An n) # 1)%Q *
                         (sum_upto (Datatypes.S M) (lnw_wterm n)
                            + (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                                 q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q)%Q)).
  { apply (qleT'_mult_compat_l _ _ _ HAn0 Hgap). }
  apply (qleT'_trans
          (((Z.of_nat (lng2_An n) # 1)%Q *
              sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
          (((Z.of_nat (lng2_An n) # 1)%Q * sum_upto (Datatypes.S M) (lnw_wterm n)
            + (Z.of_nat (lng2_An n) # 1)%Q *
                (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                   q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q)
          (((Z.of_nat (lng2_An n) # 1)%Q * sum_upto (Datatypes.S M) (lnw_wterm n)
            + ((4 # 1)%Q * (q_pow (128 # 3)%Q n *
                                q_pow (3 # 4)%Q (Datatypes.S M)))%Q)%Q)).
  - apply (lnt_leT'_eq_r
              (((Z.of_nat (lng2_An n) # 1)%Q *
                  sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
              (((Z.of_nat (lng2_An n) # 1)%Q *
                  (sum_upto (Datatypes.S M) (lnw_wterm n)
                 + q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                     q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q)
              (((Z.of_nat (lng2_An n) # 1)%Q * sum_upto (Datatypes.S M) (lnw_wterm n)
                + (Z.of_nat (lng2_An n) # 1)%Q *
                    (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                       q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q)).
    + ring.
    + exact H1.
  - apply (lnt_leT'_eq_l
              (((Z.of_nat (lng2_An n) # 1)%Q * sum_upto (Datatypes.S M) (lnw_wterm n)
                + (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                     (Z.of_nat (lng2_An n) # 1)%Q) *
                    q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q)
              (((Z.of_nat (lng2_An n) # 1)%Q * sum_upto (Datatypes.S M) (lnw_wterm n)
                + (Z.of_nat (lng2_An n) # 1)%Q *
                    (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                       q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q)
              (((Z.of_nat (lng2_An n) # 1)%Q * sum_upto (Datatypes.S M) (lnw_wterm n)
                + ((4 # 1)%Q * (q_pow (128 # 3)%Q n *
                                    q_pow (3 # 4)%Q (Datatypes.S M)))%Q)%Q)).
    + rewrite (lnt4_gap_lhs_eq n (Datatypes.S M)). ring.
    + apply (qleT'_plus_compat).
      * apply qleT'_refl.
      * apply (lnt_leT'_eq_l
                  ((Z.of_nat (lng2_An n) # 1)%Q *
                     (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                        q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q
                  (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                     (Z.of_nat (lng2_An n) # 1)%Q *
                     q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q
                  ((4 # 1)%Q * (q_pow (128 # 3)%Q n *
                                  q_pow (3 # 4)%Q (Datatypes.S M)))%Q).
        -- ring.
        -- exact Hbc.
Qed.

(** ★层2·斜率闭式：1 ≤ n、18n ≤ SM ⟹
    A_n·S_{M+d} ≤ SM·24ⁿ + d·C₁₈ⁿ（尾项纯指数形：C₁₈ ≈ 0.2406）。 *)
Theorem lnt4_total_slope : forall (n M d : nat), 1 <= n -> 18 * n <= Datatypes.S M ->
  QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
            sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
        (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n
          + (Z.of_nat d # 1) *
              q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)%Q).
Proof.
  intros n M d Hn Hm.
  assert (Hm2 : 2 * n <= M + 1) by lia.
  pose proof (lnt4_total_budget n M d Hn Hm2) as Htb.
  pose proof (lnt3_rho_pow_anti (18 * n) (Datatypes.S M) Hm) as Hra.
  apply (qleT'_trans
          (((Z.of_nat (lng2_An n) # 1)%Q *
              sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
          (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n
            + (Z.of_nat d # 1) *
                (q_pow (128 # 3)%Q n *
                   q_pow (3 # 4)%Q (Datatypes.S M)))%Q)
          (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n
            + (Z.of_nat d # 1) *
                q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)%Q)).
  - exact Htb.
  - apply (qleT'_plus_compat).
    + apply qleT'_refl.
    + apply (qleT'_mult_compat_l
                (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q (Datatypes.S M))%Q
                (q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)
                (Z.of_nat d # 1) (lnt4_Znat_nonneg d)).
      apply (lnt_leT'_eq_r
                ((q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q (Datatypes.S M))%Q)
                ((q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q (18 * n))%Q)
                (q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)).
      * rewrite <- (lnt4_qpow_scale (128 # 3)%Q (3 # 4)%Q 18 n). reflexivity.
      * apply (qleT'_mult_compat_l (q_pow (3 # 4)%Q (Datatypes.S M))
                  (q_pow (3 # 4)%Q (18 * n)) (q_pow (128 # 3)%Q n)
                  (lnt4_pow128_nonneg n) Hra).
Qed.

(* ============================================================ *)
(* §3 层3·装配形：「余项被增长压倒」核心步 sigT/严格 Set 面                *)
(* ============================================================ *)

(** ★层3·核心步 sigT 见证形：1 ≤ n、18n ≤ m ⟹ ∃ B < 1：
    A_n·2^{n+2}·ρ^{m−2n} ≤ B——见证 B := 4·C₁₈ = 3^17/2^27 封闭有理数
    （sigT/And 全 Set 积载体，无 Prop 存在）。 *)
Theorem lnt4_remainder_sig : forall (n m : nat), 1 <= n -> 18 * n <= m ->
  sigT (fun B : Q => And (QltT B 1%Q)
            (QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
                       (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                          q_pow (3 # 4)%Q (m - 2 * n)))%Q) B)).
Proof.
  intros n m Hn Hm.
  exists (((4 # 1)%Q * ((128 # 3)%Q * q_pow (3 # 4)%Q 18))%Q).
  split.
  - exact lnt4_anchor_B18_lt1.
  - destruct n as [| k].
    + exfalso. lia.
    + apply (qleT'_trans
                (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                    (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S k))) *
                       q_pow (3 # 4)%Q (m - 2 * Datatypes.S k)))%Q)
                (((4 # 1)%Q *
                    q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) (Datatypes.S k))%Q)
                (((4 # 1)%Q * ((128 # 3)%Q * q_pow (3 # 4)%Q 18))%Q)).
      * apply (lnt4_compete_exp (Datatypes.S k) m Hm).
      * apply (qleT'_mult_compat_l
                  (q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) (Datatypes.S k))
                  ((128 # 3)%Q * q_pow (3 # 4)%Q 18) (4 # 1)%Q lnt_q4_le0).
        apply (lnt4_pow_le_self _ k).
        -- exact lnt4_anchor_C18_0.
        -- exact lnt4_anchor_C18_le1.
Qed.

(** ★层3·θⁿ 终界装配闭式：1 ≤ n、18n ≤ SM ⟹
    （余项严格 < 1）×（A_n·S_{M+d} ≤ SM·24ⁿ + d·C₁₈ⁿ）——严格余项步与
    层2 全容器斜率闭式的 And 合成（S01 Set 积载体）：
    ln2 无理性「余项被增长压倒」核心步的闭式承载。 *)
Theorem lnt4_theta_final : forall (n M d : nat), 1 <= n -> 18 * n <= Datatypes.S M ->
  And (QltT (((Z.of_nat (lng2_An n) # 1)%Q *
                (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                   q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q) 1%Q)
      (QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
                  sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
             (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n
               + (Z.of_nat d # 1) *
                   q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)%Q)).
Proof.
  intros n M d Hn Hm. split.
  - apply (lnt4_theta_lt n (Datatypes.S M) Hn Hm).
  - apply (lnt4_total_slope n M d Hn Hm).
Qed.

(* ============================================================ *)
(* §4 数值锚组（vm_compute 判定；C₁₈/C₁₁ 有理值与终界实例）                 *)
(* ============================================================ *)

(** C₁₈ 有理值判定：(128/3)·(3/4)^18 = 3^17/2^29 = 129140163/536870912。 *)
Theorem lnt4_anchor_C18_val :
  QeqT ((128 # 3)%Q * q_pow (3 # 4)%Q 18)%Q ((129140163 # 536870912)%Q).
Proof. vm_compute. reflexivity. Qed.

(** C₁₁ 有理值判定：(64/3)·(3/4)^11 = 3^10/2^16 = 59049/65536。 *)
Theorem lnt4_anchor_C11_val :
  QeqT ((64 # 3)%Q * q_pow (3 # 4)%Q 11)%Q ((59049 # 65536)%Q).
Proof. vm_compute. reflexivity. Qed.

(** 终界点锚①（纯预算档实例）：n=2、m=22（11·2=22）：A_2·ρ^{20} < 1
    （A_2 = 52：52·(3/4)^20 ≈ 0.0467 < 1）。 *)
Theorem lnt4_anchor_budget :
  QltT (((Z.of_nat (lng2_An 2) # 1)%Q * q_pow (3 # 4)%Q 20)%Q) 1%Q.
Proof. vm_compute. reflexivity. Qed.

(** 终界点锚②（全常数档实例）：n=2、m=36（18·2=36）：A_2·2^4·ρ^{32} < 1
    （52·16·(3/4)^32 ≈ 0.0836 < 1）。 *)
Theorem lnt4_anchor_gap18 :
  QltT (((Z.of_nat (lng2_An 2) # 1)%Q *
           (q_pow (2 # 1)%Q 4 * q_pow (3 # 4)%Q 32))%Q) 1%Q.
Proof. vm_compute. reflexivity. Qed.

(** 终界点锚③（层2 全容器实例）：n=2、M=5、d=3（2n=4 ≤ M+1=6 在带内）：
    A_2·S_8 ≤ 6·24² + 3·(128/3)²·(3/4)^6 = 3456 + 972 = 4428
    （真值 52·S_8 ≈ 206，界松但形全真——vm_compute 判定）。 *)
Theorem lnt4_anchor_total :
  QleT' (((Z.of_nat (lng2_An 2) # 1)%Q * sum_upto 9 (lnw_wterm 2))%Q)
        ((4428 # 1)%Q).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §5 诚实边界登记（非虚报占位）                                          *)
(* ============================================================ *)
(* ① I'_n 真 Real 积分机库内不在册（在册勘定＋PolyIntegral 头注自认）：    *)
(*    本件传送面以有理求和容器承载（DW 件同口径）；ln2 无理性的收敛位      *)
(*    （p_n/q_n 逼近与 |ln2−p/q| ≤ 预算的对接）为下游缺口，不冒领。        *)
(* ② 斜率阈的谱系：纯预算档阈 log_{4/3}(64/3) ≈ 10.639（取 11）；全常数   *)
(*    档（含 2^{n+2} 与收尾因子 4）阈 log_{4/3}(128/3) ≈ 13.046（本件取   *)
(*    18 使 B := 4·C₁₈ < 1 对 n = 1 已成立）。更锐档（斜率 14 时           *)
(*    A_n·余项 ≤ 4·(3^13/2^21)ⁿ < 1 需 n ≥ 6）留后续精化件。               *)
(* ③ A_n ≤ 12ⁿ 为 DU 在册首档（K ∈ [6,12] 判定区间上沿）；K 的精化         *)
(*    （Vandermonde 卷积跳）在 DU §G ③ 登记，本件按 12ⁿ 口径使用。         *)
(* ④ DP2 件 lnr2_wgap_geo 系 DH lnt2_wgap_geo_quarter 的逐字使用名        *)
(*    （abl_ln2_theta_rehook.v L131 exact 闭合），本链经 theta_upper      *)
(*    Require 天然覆盖，无需重拷。                                        *)
(* ============================================================ *)

(* ============================================================ *)
(* 假设审计留痕（G1/G4 取证块）＋ 可执行见证提取闭合（G3）                  *)
(* ============================================================ *)

Print Assumptions lnt4_Znat_nonneg.
Print Assumptions lnt4_pow2_nonneg.
Print Assumptions lnt4_pow64_nonneg.
Print Assumptions lnt4_pow128_nonneg.
Print Assumptions lnt4_pow2_SS.
Print Assumptions lnt4_fold_24.
Print Assumptions lnt4_fold_128.
Print Assumptions lnt4_fold_128r.
Print Assumptions lnt4_qpow_scale.
Print Assumptions lnt4_pow_le_self.
Print Assumptions lnt4_gap_lhs_eq.
Print Assumptions lnt4_An_gap_compose.
Print Assumptions lnt4_theta_budget_consume.
Print Assumptions lnt4_theta_budget_lt.
Print Assumptions lnt4_compete_exp.
Print Assumptions lnt4_theta_lt.
Print Assumptions lnt4_budget_lt.
Print Assumptions lnt4_total_budget.
Print Assumptions lnt4_total_gap_budget.
Print Assumptions lnt4_total_slope.
Print Assumptions lnt4_remainder_sig.
Print Assumptions lnt4_theta_final.
Print Assumptions lnt4_anchor_C18_val.
Print Assumptions lnt4_anchor_C11_val.
Print Assumptions lnt4_anchor_budget.
Print Assumptions lnt4_anchor_gap18.
Print Assumptions lnt4_anchor_total.

From Stdlib Require Import Extraction.
Separate Extraction lnt4_An_gap_compose lnt4_compete_exp lnt4_budget_lt
  lnt4_theta_lt lnt4_total_budget lnt4_total_gap_budget lnt4_total_slope
  lnt4_remainder_sig lnt4_theta_final lnt4_theta_budget_consume
  lnt4_theta_budget_lt.
Print Assumptions lnt4_qpow2_Z.
Print Assumptions lnt4_qpow24_Z.
Print Assumptions lnt4_24fold_eq.
Print Assumptions lnt4_anchor_C18_0.
Print Assumptions lnt4_anchor_C18_le1.
Print Assumptions lnt4_anchor_B18_lt1.
Print Assumptions lnt4_anchor_C11_0.
Print Assumptions lnt4_anchor_C11_le1.
Print Assumptions lnt4_anchor_C11_lt1.
