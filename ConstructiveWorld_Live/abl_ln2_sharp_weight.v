(* ===================================================================== *)
(*  abl_ln2_sharp_weight.v —— ln2 无理性链·⑤锐权衰减 (1+t) 变体件 *)
(*  使命: Beukers 被积锐权 (1+t) 变体的衰减不等式核（有理求和版）。勘定: 库内无 Real 积分机（PolyIntegral 头注自认「库内无现成积分基建」，其 pint_integral 为 Q 系数多项式的逐项定积分机），故降档「有理求和版」交付：有限和容器与 lnt 求和容器同构。数学内容: 锐权项 w(n,k) := u(n,k)+ũ(n,k)，u=lnt_pterm=C(n+k,n)/((k+1)·2^{k+1})，ũ:=C(n+k,n)/((k+2)·2^{k+1})——即 ∫₀¹(1+t)·(t/2)^k dt 的逐项 Q 编码（归一化），权升一阶（+t 肢）而衰减率仍几何: ①ũ ≤ u（一阶权被吸收，1/(k+2) ≤ 1/(k+1)）⟹ u ≤ w ≤ 2u（(1+t) ≤ 2 在积分域有界化的 Q 面形式）；②同窗 2n ≤ k+4 内 w(n,k+j) ≤ 2·w(n,k)·(3/4)^j（几何核吸收，率 ρ=3/4 不变）；③尾项控制 Σ_{i<d} w(n,M+1+i) ≤ 8·w(n,M+1)（常数 4 的倍增）；④加法隙形；⑤峰值档 w(n,k) ≤ 2^n（2^{n−1} 的倍增）；⑥组合终形 lnw_wgap_geo: 尾隙 ≤ 2^{n+3}·(3/4)^{SM−2n}（C(n)·ρ^M 终形，ρ=3/4 不变、C 常数倍增）。诚实判定: lnw_wratio_refuted34——纯 w 比率在精确窗界 n=3,k=2 处 R=27/35 ≈ 0.771 > 3/4（vm_compute 判定），证成「常数 2 吸收」配方为必需而非冗余。pint 对接口: lnw_wcore/lnw_pint_wcore——权核 (1/(k+1)+1/(k+2))/2^{k+1} 与 PolyIntegral Q 级逐项定积分 ∫₀¹(1+t)·(1/2^{k+1})·t^k dt 的 QeqT 焊接（积分读数的库内构造性承载）；lnw_wterm_core——C(n+k,n) 因子外提恒等式。 *)
(*  依赖: Stdlib QArith/List/Arith/ZArith/Lia；S01_BaseRing S02_CauchyComplete S03_QExp PolyIntegral PadeErrorIntegral BeukersLists BeukersVariant PintMono PsQReindex；前置池拷贝 abl_ln2_tail_bound（lnt_pterm/lnt_pterm_pow/lnt_pterm_tail/lnt_pterm_peak＋工器件 lnt_leT'_eq_r/lnt_qle_mul_cancel_r/lnt_Qmult_le_compat_l/lnt_qinv_mul_cancel/lnt_qneq_of_eq0/lnt_pow2_pos/lnt_pow_pos_le/lnt_sum_le/lnt_sum_scale/lnt_sum_range 直接使用——链序池内平铺 Require）。 *)
(*  对标: Beukers 1979 ln2 无理性证明的锐权变体（|A_n·X−B_n| ≤ θ^n 上界肢的衰减预算——β 级数已机证无一致几何比率，衰减预算必走 (1+t) 变体权函数）；PolyIntegral pint_integral_pow_poly 的积分读数；Ln2Bridge ln2b_escape_of_supply 供给前提 θ 档的权侧对应件。 *)
(*  构造性: 纯构造性、零承认件；语句面全 Set（QeqT/QltT/QleT'），nat 层核全 lia/ring 显式展开；Qeq/Qle/Qlt 支撑引理仅 Prop 面作推理；==-重写一律限于 == 目标内、QleT' 目标换形走 lnt_leT'_eq_l/r 传送；文尾 Print Assumptions 全 Closed＋独立提取验证。 *)
(*  编译配方: rocq c -native-compiler no -Q vo_local_world_unified_0930 ""（编译目录 ln2_weight/，并发限 ≤1，链序 tail_bound → sharp_weight）。 *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral PadeErrorIntegral BeukersLists BeukersVariant PintMono.
Require Import PsQReindex.
Require Import abl_ln2_tail_bound.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 工器件：Z 常数非负档、除数单调核（权升一阶吸收的本体）               *)
(* ============================================================ *)

(* Z 常数非负 ⟹ QleT' 0 (z#1)（2/8/16 常数档共用工器） *)
Lemma lnw_qZ_le0 : forall z : Z, (0 <= z)%Z -> QleT' 0 (z # 1)%Q.
Proof.
  intros z Hz. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

Lemma lnw_q2_le0 : QleT' 0 (2 # 1)%Q.
Proof. apply lnw_qZ_le0. lia. Qed.

Lemma lnw_q8_le0 : QleT' 0 (8 # 1)%Q.
Proof. apply lnw_qZ_le0. lia. Qed.

(** 除数单调核：0<a、d1≤d2、0<d1、0<p ⟹ a/d2p ≤ a/d1p（Qinv 全程免归一化——
    除正消元形：双侧乘正 M=(d1·p)·(d2·p) 后对消）。 *)
Lemma lnw_qinv_den_le : forall (a d1 d2 p : Q),
  Qlt 0 a -> Qle d1 d2 -> Qlt 0 d1 -> Qlt 0 p ->
  Qle (a * Qinv (d2 * p)) (a * Qinv (d1 * p)).
Proof.
  intros a d1 d2 p Ha Hd Hd1 Hp.
  assert (Hd2 : Qlt 0 d2) by (apply (Qlt_le_trans 0%Q d1 d2); assumption).
  assert (Hc1 : Qinv (d2 * p) * (d2 * p) == 1%Q)
    by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0;
        apply Qmult_lt_0_compat; assumption).
  assert (Hc2 : Qinv (d1 * p) * (d1 * p) == 1%Q)
    by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0;
        apply Qmult_lt_0_compat; assumption).
  assert (EL : ((a * Qinv (d2 * p)) * ((d1 * p) * (d2 * p)))%Q
             == (a * (d1 * p))%Q).
  { transitivity (a * ((Qinv (d2 * p) * (d2 * p)) * (d1 * p)))%Q.
    - ring.
    - rewrite Hc1. ring. }
  assert (ER : ((a * Qinv (d1 * p)) * ((d1 * p) * (d2 * p)))%Q
             == (a * (d2 * p))%Q).
  { transitivity (a * ((Qinv (d1 * p) * (d1 * p)) * (d2 * p)))%Q.
    - ring.
    - rewrite Hc2. ring. }
  apply (lnt_qle_mul_cancel_r
    (a * Qinv (d2 * p)) (a * Qinv (d1 * p)) (((d1 * p) * (d2 * p))%Q)).
  - apply Qmult_lt_0_compat; apply Qmult_lt_0_compat; assumption.
  - apply (Qle_trans ((a * Qinv (d2 * p)) * ((d1 * p) * (d2 * p)))%Q
             (a * (d1 * p))%Q
             ((a * Qinv (d1 * p)) * ((d1 * p) * (d2 * p)))%Q).
    + apply qeq_le. exact EL.
    + apply (Qle_trans (a * (d1 * p))%Q (a * (d2 * p))%Q
               ((a * Qinv (d1 * p)) * ((d1 * p) * (d2 * p)))%Q).
      * apply lnt_Qmult_le_compat_l.
        -- apply Qlt_le_weak. exact Ha.
        -- apply Qmult_le_compat_r; [exact Hd | apply Qlt_le_weak; exact Hp].
      * apply qeq_le. symmetry. exact ER.
Qed.

(* ============================================================ *)
(* §A 锐权对象：w(n,k) = u(n,k)+ũ(n,k)——(1+t) 权升一阶项族               *)
(* ============================================================ *)

(* +t 肢：ũ(n,k) = C(n+k,n)/((k+2)·2^{k+1})——∫₀¹ t·(t/2)^k dt 的同归一化
   Q 编码（权升一阶：k 指数进一、分母 (k+2)）；照 lnt_pterm 原样取 bkC 承载。 *)
Definition lnw_uterm (n k : nat) : Q :=
  ((Z.of_nat (bkC (n + k) n) # 1) /
     ((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) *
        q_pow (2 # 1)%Q (Datatypes.S k)))%Q.

(* 锐权项：(1+t)·(t/2)^k 逐项积分的 Q 编码（归一化下）。 *)
Definition lnw_wterm (n k : nat) : Q :=
  (lnt_pterm n k + lnw_uterm n k)%Q.

(* bkC 严格正的 Z 桥（Nat2Z.inj_lt 本环境为 iff 形，取 proj1） *)
Lemma lnw_zpos_of_bkC : forall n k : nat, (0 < Z.of_nat (bkC (n + k) n))%Z.
Proof.
  intros n k.
  assert (Hb : 1 <= bkC (n + k) n) by (apply bkC_pos; lia).
  exact (proj1 (Nat2Z.inj_lt 0%nat (bkC (n + k) n)) Hb).
Qed.

Theorem lnw_uterm_pos : forall n k : nat, QltT 0 (lnw_uterm n k).
Proof.
  intros n k. apply Qlt_to_QltT. unfold lnw_uterm, Qdiv.
  apply Qmult_lt_0_compat.
  - apply rx_Qlt_Z1. apply lnw_zpos_of_bkC.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat.
    + apply rx_Qlt_Z1. lia.
    + apply lnt_pow2_pos.
Qed.

(** 核心①权升一阶被吸收：ũ(n,k) ≤ u(n,k)（1/(k+2) ≤ 1/(k+1)）——
    (1+t) 变体非平凡的最低限：+t 肢不放大基底项。 *)
Theorem lnw_uterm_le : forall n k : nat, QleT' (lnw_uterm n k) (lnt_pterm n k).
Proof.
  intros n k. apply Qle_to_QleT'.
  unfold lnw_uterm, lnt_pterm, Qdiv.
  apply lnw_qinv_den_le.
  - apply rx_Qlt_Z1. apply lnw_zpos_of_bkC.
  - apply bk_Qle_nat. lia.
  - apply rx_Qlt_Z1. lia.
  - apply lnt_pow2_pos.
Qed.

(** 核心②锐权正性（下游链支）：0 < w(n,k)。 *)
Theorem lnw_wterm_pos : forall n k : nat, QltT 0 (lnw_wterm n k).
Proof.
  intros n k. apply qltT_leT'_ltT with (y := lnw_uterm n k).
  - apply lnw_uterm_pos.
  - apply Qle_to_QleT'. unfold lnw_wterm.
    apply (Qle_trans (lnw_uterm n k) ((lnw_uterm n k + lnt_pterm n k)%Q)
             ((lnt_pterm n k + lnw_uterm n k)%Q)).
    + apply (Qle_trans (lnw_uterm n k) ((lnw_uterm n k + 0)%Q)
               ((lnw_uterm n k + lnt_pterm n k)%Q)).
      * apply qeq_le. ring.
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply QleT'_to_Qle. apply qltT_leT'. apply lnt_pterm_pos.
    + apply qeq_le. ring.
Qed.

(** 核心③下夹：u(n,k) ≤ w(n,k)（定义性，供尾项从下方换底）。 *)
Theorem lnw_wterm_ge : forall n k : nat, QleT' (lnt_pterm n k) (lnw_wterm n k).
Proof.
  intros n k. apply Qle_to_QleT'. unfold lnw_wterm.
  apply (Qle_trans (lnt_pterm n k) ((lnt_pterm n k + 0)%Q)
           ((lnt_pterm n k + lnw_uterm n k)%Q)).
  - apply qeq_le. ring.
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + apply QleT'_to_Qle. apply qltT_leT'. apply lnw_uterm_pos.
Qed.

(** 核心④上夹（(1+t)≤2 有界化的 Q 面）：w(n,k) ≤ 2·u(n,k)。
    数学：积分域 [0,1] 上 (1+t) ≤ 2，逐项化即 +t 肢 ≤ 基底肢（核心①）。 *)
Theorem lnw_wterm_le2 : forall n k : nat,
  QleT' (lnw_wterm n k) ((2 # 1)%Q * lnt_pterm n k)%Q.
Proof.
  intros n k. apply qleT'_trans with ((lnt_pterm n k + lnt_pterm n k)%Q).
  - apply qleT'_plus_compat; [apply qleT'_refl | apply lnw_uterm_le].
  - apply qeq_leT'. unfold lnw_wterm. ring.
Qed.

(* ============================================================ *)
(* §B 几何档：权升一阶、衰减率仍几何（几何核吸收，常数 2 配方）             *)
(* ============================================================ *)

(** 核心⑤幂式档：2n ≤ k+4 ⟹ w(n,k+j) ≤ 2·w(n,k)·(3/4)^j。
    配方：w(k+j) ≤ 2·u(k+j) ≤ 2·u(k)·ρ^j ≤ 2·w(k)·ρ^j——三步全使用前置件
    （lnw_wterm_le2 / lnt_pterm_pow / lnw_wterm_ge），衰减率 ρ=3/4 与
    lnt 同窗同率，仅常数倍增（权升一阶的代价显式记为因子 2）。 *)
Theorem lnw_wterm_pow : forall (n k j : nat),
  2 * n <= k + 4 ->
  QleT' (lnw_wterm n (k + j))
    ((2 # 1)%Q * (lnw_wterm n k * q_pow (3 # 4)%Q j))%Q.
Proof.
  intros n k j H.
  apply qleT'_trans with ((2 # 1)%Q * lnt_pterm n (k + j))%Q.
  - apply lnw_wterm_le2.
  - apply qleT'_trans with ((2 # 1)%Q * (lnt_pterm n k * q_pow (3 # 4)%Q j))%Q.
    + apply qleT'_mult_compat_l; [apply lnw_q2_le0 | apply lnt_pterm_pow; exact H].
    + apply qleT'_mult_compat_l; [apply lnw_q2_le0 |].
      apply (qleT'_mult_compat_r (lnt_pterm n k) (lnw_wterm n k)
               (q_pow (3 # 4)%Q j) (lnt_pow_pos_le j) (lnw_wterm_ge n k)).
Qed.

(** 核心⑥尾项控制（锐权版 Cauchy 模量核）：2n ≤ M+4 ⟹
    Σ_{i<d} w(n,M+1+i) ≤ 8·w(n,M+1)。配方：Σw ≤ 2·Σu ≤ 2·4·u = 8·u ≤ 8·w
    （lnt_pterm_tail 常数 4 的倍增）。 *)
Theorem lnw_wterm_tail : forall (n M d : nat),
  2 * n <= M + 4 ->
  QleT' (sum_upto d (fun i : nat => lnw_wterm n (M + Datatypes.S i)))
        ((8 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q.
Proof.
  intros n M d H.
  apply qleT'_trans with ((8 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q.
  - apply qleT'_trans with
      ((2 # 1)%Q * sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i)))%Q.
    + apply lnt_leT'_eq_r with
        (y := sum_upto d (fun i : nat => (2 # 1)%Q * lnt_pterm n (M + Datatypes.S i))%Q).
      * apply lnt_sum_scale.
      * apply lnt_sum_le. intros i Hi. apply lnw_wterm_le2.
    + apply lnt_leT'_eq_r with
        (y := ((2 # 1)%Q * ((4 # 1)%Q * lnt_pterm n (Datatypes.S M)))%Q).
      * ring.
      * apply qleT'_mult_compat_l;
          [apply lnw_q2_le0 | apply lnt_pterm_tail; exact H].
  - apply qleT'_mult_compat_l; [apply lnw_q8_le0 | apply lnw_wterm_ge].
Qed.

(** 核心⑦加法隙形（收敛桥 Cauchy 模量，锐权版）：
    S^w_{M+d} ≤ S^w_M + 8·w(n,M+1)。 *)
Theorem lnw_wterm_gap : forall (n M d : nat),
  2 * n <= M + 4 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnw_wterm n k))
        (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
           + (8 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q.
Proof.
  intros n M d H.
  apply (lnt_leT'_eq_l
    (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
       + sum_upto d (fun i : nat => lnw_wterm n (M + Datatypes.S i)))%Q
    (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnw_wterm n k))
    (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
       + (8 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q).
  - apply Qeq_sym. apply lnt_sum_range.
  - apply Qle_to_QleT'. apply Qplus_le_compat.
    + apply Qle_refl.
    + apply QleT'_to_Qle. apply lnw_wterm_tail. exact H.
Qed.

(** 核心⑧绝对峰值档（锐权版）：1 ≤ n ⟹ w(n,k) ≤ 2^n（2^{n−1} 的倍增）。 *)
Theorem lnw_wterm_peak : forall n k : nat,
  1 <= n -> QleT' (lnw_wterm n k) (q_pow (2 # 1)%Q n).
Proof.
  intros n k Hn.
  assert (E2n : q_pow (2 # 1)%Q n == ((2 # 1)%Q * q_pow (2 # 1)%Q (n - 1))%Q).
  { assert (Hm : exists m : nat, n = Datatypes.S m) by (exists (n - 1); lia).
    destruct Hm as [m Hm]. subst n.
    rewrite q_pow_succ.
    replace (Datatypes.S m - 1) with m by lia.
    apply Qeq_refl. }
  apply qleT'_trans with ((2 # 1)%Q * lnt_pterm n k)%Q.
  - apply lnw_wterm_le2.
  - apply lnt_leT'_eq_r with (y := ((2 # 1)%Q * q_pow (2 # 1)%Q (n - 1))%Q).
    + apply Qeq_sym. exact E2n.
    + apply qleT'_trans with ((2 # 1)%Q * q_pow (2 # 1)%Q (n - 1))%Q.
      * apply qleT'_mult_compat_l;
          [apply lnw_q2_le0 | apply lnt_pterm_peak; exact Hn].
      * apply qleT'_refl.
Qed.

(** 核心⑨组合终形（C(n)·ρ^M，锐权版）：1 ≤ n、2n ≤ M+1 ⟹
    尾隙 ≤ 2^{n+3}·(3/4)^{SM−2n}——ρ=3/4 不变，C 从 2^{n+1} 倍增至
    2^{n+3}（尾项 8/4 与峰值 2/1 两笔倍增的显式合成）。 *)
Theorem lnw_wgap_geo : forall (n M d : nat),
  1 <= n -> 2 * n <= M + 1 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnw_wterm n k))
        (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
           + (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n)))
                * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q.
Proof.
  intros n M d Hn HM.
  apply qleT'_trans with
    (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
       + ((8 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q)%Q.
  - apply lnw_wterm_gap. lia.
  - apply qleT'_plus_compat.
    + apply qleT'_refl.
    + assert (Hpow := lnt_pterm_pow n (2 * n) (Datatypes.S M - 2 * n) ltac:(lia)).
      replace (2 * n + (Datatypes.S M - 2 * n)) with (Datatypes.S M) in Hpow
        by lia.
      assert (Hpk : QleT' (lnt_pterm n (2 * n)) (q_pow (2 # 1)%Q (n - 1)))
        by (apply lnt_pterm_peak; exact Hn).
      assert (Hchain : QleT' (lnt_pterm n (Datatypes.S M))
                         (q_pow (2 # 1)%Q (n - 1)
                            * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))).
      { apply qleT'_trans with
          ((lnt_pterm n (2 * n)) * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q.
        - exact Hpow.
        - apply (qleT'_mult_compat_r (lnt_pterm n (2 * n))
                   (q_pow (2 # 1)%Q (n - 1))
                   (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))
                   (lnt_pow_pos_le (Datatypes.S M - 2 * n)) Hpk). }
      assert (Hxy : QleT' ((8 # 1)%Q * lnw_wterm n (Datatypes.S M))
                      ((16 # 1)%Q * (q_pow (2 # 1)%Q (n - 1)
                          * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q).
      { apply qleT'_trans with ((16 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q.
        - apply lnt_leT'_eq_r with
            (y := ((8 # 1)%Q * ((2 # 1)%Q * lnt_pterm n (Datatypes.S M)))%Q).
          + ring.
          + apply qleT'_mult_compat_l;
              [apply lnw_q8_le0 | apply lnw_wterm_le2].
        - apply (qleT'_mult_compat_l (lnt_pterm n (Datatypes.S M))
                   (q_pow (2 # 1)%Q (n - 1)
                      * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)) (16 # 1)%Q
                   (lnw_qZ_le0 16%Z ltac:(lia)) Hchain). }
      assert (E162 : ((16 # 1)%Q * q_pow (2 # 1)%Q (n - 1))%Q
                   == q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n)))).
      { replace (Datatypes.S (Datatypes.S (Datatypes.S n))) with (4 + (n - 1))
          by lia.
        rewrite q_pow_add. cbn [q_pow]. ring. }
      apply (lnt_leT'_eq_r
        ((8 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q
        ((16 # 1)%Q * (q_pow (2 # 1)%Q (n - 1)
            * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q
        ((q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n)))) *
            q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
      * rewrite <- E162. ring.
      * exact Hxy.
Qed.

(* ============================================================ *)
(* §C pint 对接口与诚实边界判定：积分读数的 Q 层承载＋纯比率反例                 *)
(* ============================================================ *)

(* 权核：(1/(k+1)+1/(k+2))/2^{k+1} = ∫₀¹(1+t)·(1/2^{k+1})·t^k dt 的
   Q 级逐项积分值（PolyIntegral pint_integral 语义）——无 C 的权侧对象。 *)
Definition lnw_wcore (k : nat) : Q :=
  ((1 # 1)%Q / ((Z.of_nat (Datatypes.S k) # 1) *
                  q_pow (2 # 1)%Q (Datatypes.S k)) +
   (1 # 1)%Q / ((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) *
                  q_pow (2 # 1)%Q (Datatypes.S k)))%Q.

(** 对接件①（C 因子外提）：w(n,k) == C(n+k,n)·权核——多项式×几何混合
    结构的显式配方：组合因子与权核分离，权核即 pint 逐项积分族。 *)
Theorem lnw_wterm_core : forall n k : nat,
  QeqT (lnw_wterm n k) ((Z.of_nat (bkC (n + k) n) # 1) * lnw_wcore k)%Q.
Proof.
  intros n k. apply qeq_imp_qeqT.
  unfold lnw_wterm, lnt_pterm, lnw_uterm, lnw_wcore, Qdiv. ring.
Qed.

(** 对接件②（pint 焊接）：∫₀¹(1+t)·(1/2^{k+1})·t^k dt == 权核——
    PolyIntegral Q 级逐项定积分机（pint_integral_scale/pow_poly）对
    (1+t) 权的两臂（t^k 与 t^{k+1}）各积分一次的显式焊接。 *)
Theorem lnw_pint_wcore : forall k : nat,
  QeqT (pint_integral (pint_scale (Qinv (q_pow (2 # 1)%Q (Datatypes.S k)))
                         (pint_pow_poly k)) +
        pint_integral (pint_scale (Qinv (q_pow (2 # 1)%Q (Datatypes.S k)))
                         (pint_pow_poly (Datatypes.S k))))%Q
       (lnw_wcore k).
Proof.
  intros k. apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq _ _
    (pint_integral_scale (Qinv (q_pow (2 # 1)%Q (Datatypes.S k)))
       (pint_pow_poly k))) as Hs1.
  pose proof (qeqT_imp_qeq _ _
    (pint_integral_scale (Qinv (q_pow (2 # 1)%Q (Datatypes.S k)))
       (pint_pow_poly (Datatypes.S k)))) as Hs2.
  pose proof (qeqT_imp_qeq _ _ (pint_integral_pow_poly k)) as Hp1.
  pose proof (qeqT_imp_qeq _ _ (pint_integral_pow_poly (Datatypes.S k))) as Hp2.
  rewrite Hs1, Hs2, Hp1, Hp2.
  unfold lnw_wcore, Qdiv.
  rewrite !Qinv_mult_distr.
  ring.
Qed.

(** 数值判定①：w(0,0) == 3/4（= 1/2 + 1/4，vm_compute 判定）。 *)
Theorem lnw_anchor_w00 : QeqT (lnw_wterm 0 0) (3 # 4)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(** 数值判定②：w(2,2) == 7/16（= 1/4 + 3/16，vm_compute 判定）。 *)
Theorem lnw_anchor_w22 : QeqT (lnw_wterm 2 2) (7 # 16)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(** 诚实边界判定：锐权纯比率档在精确窗界被机器证伪——
    n=3、k=2（窗界 2n=k+4=6）处 w(3,3)/w(3,2) = 27/35 ≈ 0.771 > 3/4。
    故 (1+t) 变体的一致几何率必须带常数吸收（核心⑤的 2·配方为必需
    而非冗余）——与 β 级数反例判定（lnt_beta_rho_refuted34）同型的
    改换通道判定件。 *)
Theorem lnw_wratio_refuted34 : QltT ((3 # 4)%Q * lnw_wterm 3 2)%Q (lnw_wterm 3 3).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §D 假设审计与独立提取（构造性验证位）                        *)
(* ============================================================ *)

Print Assumptions lnw_qinv_den_le.
Print Assumptions lnw_uterm_pos.
Print Assumptions lnw_uterm_le.
Print Assumptions lnw_wterm_pos.
Print Assumptions lnw_wterm_ge.
Print Assumptions lnw_wterm_le2.
Print Assumptions lnw_wterm_pow.
Print Assumptions lnw_wterm_tail.
Print Assumptions lnw_wterm_gap.
Print Assumptions lnw_wterm_peak.
Print Assumptions lnw_wgap_geo.
Print Assumptions lnw_wterm_core.
Print Assumptions lnw_pint_wcore.
Print Assumptions lnw_anchor_w00.
Print Assumptions lnw_anchor_w22.
Print Assumptions lnw_wratio_refuted34.

From Stdlib Require Import Extraction.
Separate Extraction lnw_wterm_le2 lnw_wterm_pow lnw_wterm_tail lnw_wterm_gap
  lnw_wterm_peak lnw_wgap_geo lnw_wterm_core lnw_pint_wcore
  lnw_anchor_w22 lnw_wratio_refuted34.
