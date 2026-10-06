(* ===================================================================== *)
(*  abl_ln2_theta_upper.v —— ln2 无理性链·⑤上界肢 θ:=4/5 的 Q 层二次衰减核  *)
(*  使命: BT 诚实边界清单路线⑤上界肢的 θ 上肢（BV 件闭合权函数肢后的    *)
(*        装配肢）。两大内容: (A) (7/40)ⁿ 型二次衰减界——h(t)=t(1−t)/(1+t)² *)
(*        ≤ 7/40 的正定二次型核（判别式 26²−4·47·7 = 676−1316 = −640 < 0，  *)
(*        完成平方 47t²−26t+7 = 47(t−13/47)²+160/47 > 0，纯 Q 无假设）＋    *)
(*        逐点幂迭代 ＋ θ 预算肢 4ⁿ·(7/40)ⁿ = (7/10)ⁿ ≤ (4/5)ⁿ（AE §3.4    *)
(*        预算的 Q 层闭合）；(B) ũ 肢二次窗键（BV §诚实边界 2 预告的纸面    *)
(*        算术的机验判定）: 窗键 2n(k+2) ≤ (k+1)(k+5) 恰为 ũ 肢比率        *)
(*        (n+k+1)(k+2)/(2(k+1)(k+3)) ≤ 3/4 的精确键（零余量），且 k ≥ 2n    *)
(*        全带成立——带内 w = u+ũ 两肢比率同 ≤ 3/4，纯几何率恢复（无常数    *)
(*        2；与 lnw_wratio_refuted34 反例点 2·3·4 = 24 > 21 在带外互补      *)
(*        一致），尾项常数 8 → 4 减半、组合终形 C 从 2^{n+3} 下探 2^{n+2}。  *)
(*        组合肢 lnt2_wgap_geo_quarter 与 lnw_wgap_geo 同窗同率、C 减半。   *)
(*  依赖: Stdlib QArith/List/Arith/ZArith/Lia；S01_BaseRing S02_Cauchy-    *)
(*        Complete S03_QExp PolyIntegral PadeErrorIntegral BeukersLists     *)
(*        BeukersVariant PintMono PsQReindex；前置池拷贝 abl_ln2_tail_      *)
(*        bound（lnt_bkC_step/lnt_pterm_ratio/lnt_pterm_pow/lnt_geo_        *)
(*        partial/lnt_sum_le/lnt_sum_scale/lnt_sum_range/lnt_sub_le1/       *)
(*        lnt_pow_pos_le/lnt_leT'_eq_l/lnt_leT'_eq_r 等）＋ abl_ln2_sharp_  *)
(*        weight（lnw_uterm/lnw_wterm/lnw_wterm_pos/lnw_wterm_peak/         *)
(*        lnw_wgap_geo/lnw_wratio_refuted34 等）——链序池内平铺 Require。   *)
(*  对标: Beukers 1979 ln2 锐权变体的 θⁿ 上界肢（REV20 论文3 路线⑤:       *)
(*        h(t) ≤ 7/40 正定二次型的纯 Q 化＋L_n·I'_n ≤ 4ⁿ(7/40)ⁿ ≤ θⁿ        *)
(*        预算，θ:=4/5）；BV 报告 §诚实边界 2「ũ 肢更优二次窗键             *)
(*        2n(k+2) ≤ (k+1)(k+5)」的机验收束。                                *)
(*  构造性: 纯构造性、零承认件；语句面全 Set（QeqT/QeqT'/QleT'/QltT），     *)
(*        nat 层核全 lia/ring 显式展开（monomial 原子化 lia，零 nia）；     *)
(*        Qeq/Qle/Qlt 支撑引理仅 Prop 面作推理；QleT' 目标换形走            *)
(*        lnt_leT'_eq_l/r 传送（坑卡 AP#⑦/BT#3 全程规避）；文尾 Print      *)
(*        Assumptions 全 Closed＋独立提取闭合（四件套）。                   *)
(*  编译配方: <Live 工具链 opam live>/bin/rocq c -native-compiler no -Q     *)
(*        vo_local_world_unified_0930 ""（独占沙箱池 ln2_theta/，道闸≤1，   *)
(*        链序 tail_bound → sharp_weight → theta_upper）。                  *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral PadeErrorIntegral BeukersLists BeukersVariant PintMono.
Require Import PsQReindex.
Require Import abl_ln2_tail_bound.
Require Import abl_ln2_sharp_weight.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 工器件：平方非负、nat 除正消元、二次窗键的 nat 层四原子               *)
(* ============================================================ *)

(** 平方非负（hquad 完成平方的核）：QleT' 0 (s·s)。 *)
Lemma lnt2_sq_nonneg : forall s : Q, QleT' 0 (s * s)%Q.
Proof.
  intros s. apply Qle_to_QleT'.
  destruct (Qlt_le_dec s 0) as [Hlt | Hle].
  - assert (Hn : Qlt 0 (Qopp s)) by (apply (Qopp_lt_compat s 0); exact Hlt).
    apply (Qle_trans 0%Q ((Qopp s) * (Qopp s))%Q (s * s)%Q).
    + apply Qmult_le_0_compat; apply Qlt_le_weak; exact Hn.
    + apply qeq_le. ring.
  - apply Qmult_le_0_compat; exact Hle.
Qed.

(** nat 除正消元：0 < p、a·p ≤ b·p ⟹ a ≤ b（bkC 移形链 ×(k+1) 消元用）。 *)
Lemma lnt2_nat_cancel_r : forall a b p : nat,
  0 < p -> a * p <= b * p -> a <= b.
Proof.
  intros a b p Hp H. apply (proj2 (Nat.mul_le_mono_pos_r a b p Hp)). exact H.
Qed.

(** 键带下沿：2n ≤ k ⟹ 二次窗键（峰点 k = 2n 起全带覆盖的复合原子）。 *)
Lemma lnt2_key_of_ge : forall n k : nat,
  2 * n <= k -> 2 * n * (k + 2) <= (k + 1) * (k + 5).
Proof.
  intros n k H.
  assert (H1 : 2 * n * k <= k * k) by (apply Nat.mul_le_mono_r; lia).
  assert (H2 : 2 * n * 2 <= k * 2) by (apply Nat.mul_le_mono_r; lia).
  assert (H3 : 0 <= k * k) by (apply (Nat.mul_le_mono 0 k 0 k); lia).
  lia.
Qed.

(** 键带线性推论：二次窗键 ⟹ u 肢线性窗 2n ≤ k+4
    （(k+1)(k+5) = (k+2)(k+4) − 3，故键带是线性窗的真子带）。 *)
Lemma lnt2_key_lin : forall n k : nat,
  2 * n * (k + 2) <= (k + 1) * (k + 5) -> 2 * n <= k + 4.
Proof.
  intros n k H.
  destruct (le_lt_dec (2 * n) (k + 4)) as [Hle | Hgt].
  - exact Hle.
  - exfalso.
    assert (Hlow : (k + 5) * (k + 2) <= 2 * n * (k + 2))
      by (apply Nat.mul_le_mono_r; lia).
    lia.
Qed.

(** 键带单步单调：键在 k 成立 ⟹ 键在 S k 成立（f(k) = (k+1)(k+5)/(k+2)
    递增的 nat 化：2n ≤ k+4 [lnt2_key_lin] 代入展开）。 *)
Lemma lnt2_key_mono : forall n k : nat,
  2 * n * (k + 2) <= (k + 1) * (k + 5) ->
  2 * n * (Datatypes.S k + 2) <= (Datatypes.S k + 1) * (Datatypes.S k + 5).
Proof.
  intros n k H.
  pose proof (lnt2_key_lin n k H) as Hlin.
  assert (H1 : 2 * n * k <= (k + 4) * k)
    by (apply (Nat.mul_le_mono_r (2 * n) (k + 4) k); exact Hlin).
  assert (H2 : 2 * n * 3 <= (k + 4) * 3)
    by (apply (Nat.mul_le_mono_r (2 * n) (k + 4) 3); exact Hlin).
  lia.
Qed.

(** 键带平移：键在 k 成立 ⟹ 键在 k+d 成立（沿 S 迭代，供尾项逐点取键）。 *)
Lemma lnt2_key_shift : forall (n k d : nat),
  2 * n * (k + 2) <= (k + 1) * (k + 5) ->
  2 * n * (k + d + 2) <= (k + d + 1) * (k + d + 5).
Proof.
  intros n k d H. induction d as [| d IHd].
  - rewrite !Nat.add_0_r. exact H.
  - replace (k + Datatypes.S d) with (Datatypes.S (k + d)) by lia.
    exact (lnt2_key_mono n (k + d) IHd).
Qed.

(** 键带取点：k ≤ m ⟹ 键在 k 成立给键在 m 成立（使用面友好形）。 *)
Lemma lnt2_key_at : forall (n k m : nat),
  k <= m ->
  2 * n * (k + 2) <= (k + 1) * (k + 5) ->
  2 * n * (m + 2) <= (m + 1) * (m + 5).
Proof.
  intros n k m Hkm H.
  assert (Hd := lnt2_key_shift n k (m - k) H).
  replace (k + (m - k) + 2) with (m + 2) in Hd by lia.
  replace (k + (m - k) + 1) with (m + 1) in Hd by lia.
  replace (k + (m - k) + 5) with (m + 5) in Hd by lia.
  exact Hd.
Qed.

(* ============================================================ *)
(* §A (7/40) 二次衰减界：正定二次型核＋幂迭代＋θ:=4/5 预算肢                *)
(* ============================================================ *)

Lemma lnt2_pow_nonneg : forall (n : nat) (a : Q), Qle 0 a -> Qle 0 (q_pow a n).
Proof.
  intros n a Ha. induction n as [| n IHn].
  - cbn [q_pow]. unfold Qle. cbn [Qnum Qden]. lia.
  - rewrite q_pow_succ. apply Qmult_le_0_compat; [exact Ha | exact IHn].
Qed.

Lemma lnt2_pow_mono : forall (n : nat) (a b : Q),
  Qle 0 a -> Qle a b -> Qle (q_pow a n) (q_pow b n).
Proof.
  intros n a b Ha0 Hab.
  assert (Hb0 : Qle 0 b) by (apply (Qle_trans 0%Q a b); assumption).
  induction n as [| n IHn].
  - cbn [q_pow]. apply Qle_refl.
  - rewrite q_pow_succ, q_pow_succ.
    apply (Qle_trans (a * q_pow a n)%Q (b * q_pow a n)%Q (b * q_pow b n)%Q).
    + apply Qmult_le_compat_r; [exact Hab | apply lnt2_pow_nonneg; exact Ha0].
    + apply lnt_Qmult_le_compat_l; [exact Hb0 | exact IHn].
Qed.

Lemma lnt2_pow_mul : forall (n : nat) (a b : Q),
  q_pow a n * q_pow b n == q_pow (a * b)%Q n.
Proof.
  intros n a b. induction n as [| n IHn].
  - cbn [q_pow]. ring.
  - rewrite q_pow_succ, q_pow_succ, q_pow_succ. rewrite <- IHn. ring.
Qed.

(** 核心 (7/40) 正定二次型核：40·t(1−t) ≤ 7·(1+t)²——无假设成立
    （判别式 26²−4·47·7 = 676−1316 = −640 < 0 的正定二次型 47t²−26t+7，
    完成平方 = 47(t−13/47)² + 160/47 ≥ 160/47 > 0）。
    即 h(t) = t(1−t)/(1+t)² ≤ 7/40 的免除法 Q 形（AE §3.4 预算的机验）。 *)
Theorem lnt2_hquad : forall t : Q,
  QleT' ((40 # 1)%Q * (t * (1 - t)))%Q
        ((7 # 1)%Q * ((1 + t) * (1 + t)))%Q.
Proof.
  intros t.
  assert (Hsq : Qle 0 ((47 # 1)%Q * ((t - (13 # 47)) * (t - (13 # 47)))%Q)).
  { apply Qmult_le_0_compat.
    - unfold Qle. cbn [Qnum Qden]. lia.
    - apply QleT'_to_Qle. apply lnt2_sq_nonneg. }
  assert (Hsum : Qle 0 (((47 # 1)%Q * ((t - (13 # 47)) * (t - (13 # 47)))
                           + (160 # 47))%Q)).
  { apply (Qle_trans 0%Q ((0 + 0)%Q)
             (((47 # 1)%Q * ((t - (13 # 47)) * (t - (13 # 47))))
                + (160 # 47))%Q).
    - apply qeq_le. ring.
    - apply Qplus_le_compat.
      + exact Hsq.
      + unfold Qle. cbn [Qnum Qden]. lia. }
  apply Qle_to_QleT'.
  apply (Qle_trans ((40 # 1)%Q * (t * (1 - t)))%Q
           (((40 # 1)%Q * (t * (1 - t)))
              + (((47 # 1)%Q * ((t - (13 # 47)) * (t - (13 # 47))))
                 + (160 # 47)))%Q
           ((7 # 1)%Q * ((1 + t) * (1 + t)))%Q).
  - apply (Qle_trans ((40 # 1)%Q * (t * (1 - t)))%Q
             (((40 # 1)%Q * (t * (1 - t))) + 0)%Q
             (((40 # 1)%Q * (t * (1 - t)))
                + (((47 # 1)%Q * ((t - (13 # 47)) * (t - (13 # 47))))
                   + (160 # 47)))%Q).
    + rewrite Qplus_0_r. apply Qle_refl.
    + apply Qplus_le_compat; [apply Qle_refl | exact Hsum].
  - apply qeq_le. ring.
Qed.

(** 逐点 (7/40)ⁿ 幂迭代：0 ≤ t ≤ 1 ⟹ q_pow(40·t(1−t))ⁿ ≤
    q_pow(7(1+t)²)ⁿ——二次型沿 n 的单调幂传送（积分域 [0,1] 上的逐点
    (7/40)ⁿ 界；t(1−t) ≥ 0 由 0 ≤ t ≤ 1 供）。 *)
Theorem lnt2_hquad_pow : forall (n : nat) (t : Q),
  Qle 0 t -> Qle t 1 ->
  QleT' (q_pow ((40 # 1)%Q * (t * (1 - t)))%Q n)
        (q_pow ((7 # 1)%Q * ((1 + t) * (1 + t)))%Q n).
Proof.
  intros n t Ht0 Ht1.
  assert (Hs : Qle 0 (1 - t)%Q).
  { pose proof (proj2 (Qplus_le_r t 1 (Qopp t)) Ht1) as Hm.
    apply (Qle_trans 0%Q (Qopp t + t)%Q (1 - t)%Q).
    - apply qeq_le. ring.
    - apply (Qle_trans (Qopp t + t)%Q (Qopp t + 1)%Q (1 - t)%Q).
      + exact Hm.
      + apply qeq_le. ring. }
  apply Qle_to_QleT'. apply lnt2_pow_mono.
  - apply Qmult_le_0_compat.
    + unfold Qle. cbn [Qnum Qden]. lia.
    + apply Qmult_le_0_compat; [exact Ht0 | exact Hs].
  - apply QleT'_to_Qle. apply lnt2_hquad.
Qed.

(** θ:=4/5 预算肢（θ 命名核）：4ⁿ·(7/40)ⁿ = (7/10)ⁿ ≤ (4/5)ⁿ——
    AE §3.4 预算 L_n·I'_n ≤ 4ⁿ(7/40)ⁿ = 0.7ⁿ ≤ θⁿ 的 Q 层闭合。 *)
Theorem lnt2_theta_budget : forall n : nat,
  QleT' (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n)%Q (q_pow (4 # 5)%Q n)%Q.
Proof.
  intros n.
  apply (qleT'_trans (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n)%Q
           (q_pow ((4 # 1)%Q * (7 # 40)%Q)%Q n) (q_pow (4 # 5)%Q n)).
  - apply lnt_leT'_eq_l with (x := q_pow ((4 # 1)%Q * (7 # 40)%Q)%Q n).
    + apply Qeq_sym. apply lnt2_pow_mul.
    + apply qleT'_refl.
  - apply Qle_to_QleT'. apply lnt2_pow_mono.
    + unfold Qle, Qmult. cbn [Qnum Qden]. lia.
    + unfold Qle, Qmult. cbn [Qnum Qden]. lia.
Qed.

(** 数值锚①（二次型峰点带内）：t = 13/47（真实最大点，h = 221/1800 ≈
    0.1228 ≤ 7/40 = 0.175）——vm_compute 判定。 *)
Theorem lnt2_hquad_anchor : QleT'
  ((40 # 1)%Q * ((13 # 47)%Q * ((1 # 1)%Q - (13 # 47)%Q)))%Q
  ((7 # 1)%Q * (((1 # 1)%Q + (13 # 47)%Q) * ((1 # 1)%Q + (13 # 47)%Q)))%Q.
Proof. vm_compute. reflexivity. Qed.

(** 数值锚②（θ 预算实例）：(7/10)³ = 343/1000 ≤ (4/5)³ = 64/125
    （0.343 ≤ 0.512）——vm_compute 判定。 *)
Theorem lnt2_theta_anchor : QleT' (q_pow (7 # 10)%Q 3) (q_pow (4 # 5)%Q 3).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §B ũ 肢二次窗键（BV §诚实边界 2 机验）与 w 纯比率幂式（键带一阶形）      *)
(* ============================================================ *)

(** 核心⑩ũ 肢纯比率档：2n(k+2) ≤ (k+1)(k+5) ⟹ ũ(n,k+1) ≤ (3/4)·ũ(n,k)。
    代数：ũ(n,k+1)/ũ(n,k) = (n+k+1)(k+2)/(2(k+1)(k+3))，而比率 ≤ 3/4
    ⟺ 2(n+k+1)(k+2) ≤ 3(k+1)(k+3) ⟺ 2n(k+2) ≤ (k+1)(k+5)——二次键即
    ũ 肢 3/4 窗的精确键（零余量；对照 u 肢线性键 2n ≤ k+4）。 *)
Theorem lnt2_uterm_ratio34 : forall n k : nat,
  2 * n * (k + 2) <= (k + 1) * (k + 5) ->
  QleT' (lnw_uterm n (Datatypes.S k)) ((3 # 4)%Q * lnw_uterm n k)%Q.
Proof.
  intros n k H. apply Qle_to_QleT'.
  assert (HsS : lnw_uterm n (Datatypes.S k)
    == ((Z.of_nat (bkC (Datatypes.S (n + k)) n) # 1) *
          Qinv ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S k))) # 1) *
                ((2 # 1)%Q * q_pow (2 # 1)%Q (Datatypes.S k))))%Q).
  { unfold lnw_uterm, Qdiv.
    replace (n + Datatypes.S k) with (Datatypes.S (n + k)) by lia.
    rewrite (q_pow_succ (2 # 1)%Q (Datatypes.S k)). reflexivity. }
  assert (HsT : lnw_uterm n k
    == ((Z.of_nat (bkC (n + k) n) # 1) *
          Qinv ((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) *
                q_pow (2 # 1)%Q (Datatypes.S k)))%Q).
  { unfold lnw_uterm, Qdiv. reflexivity. }
  set (C1 := (Z.of_nat (bkC (Datatypes.S (n + k)) n) # 1)%Q).
  set (C0 := (Z.of_nat (bkC (n + k) n) # 1)%Q).
  set (a1 := (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S k))) # 1)%Q).
  set (a0 := (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)%Q).
  set (Qp := q_pow (2 # 1)%Q (Datatypes.S k)).
  assert (Ha1 : Qlt 0 a1) by (apply rx_Qlt_Z1; lia).
  assert (Ha0 : Qlt 0 a0) by (apply rx_Qlt_Z1; lia).
  assert (HQp : Qlt 0 Qp) by apply lnt_pow2_pos.
  assert (Ha1HQ : Qlt 0 (a1 * ((2 # 1)%Q * Qp))%Q)
    by (apply Qmult_lt_0_compat; [exact Ha1 | apply Qmult_lt_0_compat;
         [apply rx_Qlt_Z1; lia | exact HQp]]).
  assert (Ha0Q : Qlt 0 (a0 * Qp)%Q) by (apply Qmult_lt_0_compat; assumption).
  (* nat 核：2·C1·(k+2) ≤ 3·C0·(k+3)（二次键 ＋ bkC 移形 ×(k+1) 消元） *)
  assert (Hnat : 2 * bkC (Datatypes.S (n + k)) n * Datatypes.S (Datatypes.S k)
               <= 3 * bkC (n + k) n * Datatypes.S (Datatypes.S (Datatypes.S k))).
  { pose proof (lnt_bkC_step n k) as Hstep.
    assert (Hkey : 2 * (n + Datatypes.S k) * Datatypes.S (Datatypes.S k)
                 <= 3 * Datatypes.S (Datatypes.S (Datatypes.S k)) * Datatypes.S k).
    { assert (E1 : 2 * (n + Datatypes.S k) * Datatypes.S (Datatypes.S k)
                 = 2 * n * Datatypes.S (Datatypes.S k)
                   + 2 * Datatypes.S k * Datatypes.S (Datatypes.S k)) by ring.
      rewrite E1. lia. }
    assert (Hm : bkC (n + k) n * (2 * (n + Datatypes.S k) * Datatypes.S (Datatypes.S k))
               <= bkC (n + k) n
                    * (3 * Datatypes.S (Datatypes.S (Datatypes.S k)) * Datatypes.S k))
      by (apply Nat.mul_le_mono_l; exact Hkey).
    assert (HeqL : 2 * bkC (Datatypes.S (n + k)) n * Datatypes.S (Datatypes.S k)
                     * Datatypes.S k
                 = bkC (n + k) n
                     * (2 * (n + Datatypes.S k) * Datatypes.S (Datatypes.S k))).
    { replace (2 * bkC (Datatypes.S (n + k)) n * Datatypes.S (Datatypes.S k)
                 * Datatypes.S k)
        with (2 * (bkC (Datatypes.S (n + k)) n * Datatypes.S k)
                * Datatypes.S (Datatypes.S k)) by ring.
      rewrite Hstep. ring. }
    assert (HeqR : 3 * bkC (n + k) n * Datatypes.S (Datatypes.S (Datatypes.S k))
                     * Datatypes.S k
                 = bkC (n + k) n
                     * (3 * Datatypes.S (Datatypes.S (Datatypes.S k)) * Datatypes.S k))
      by ring.
    assert (Hscaled : 2 * bkC (Datatypes.S (n + k)) n * Datatypes.S (Datatypes.S k)
                        * Datatypes.S k
                    <= 3 * bkC (n + k) n * Datatypes.S (Datatypes.S (Datatypes.S k))
                         * Datatypes.S k).
    { rewrite HeqL, HeqR. exact Hm. }
    apply (lnt2_nat_cancel_r _ _ (Datatypes.S k) ltac:(lia) Hscaled). }
  (* nat 核的 Q 桥（bk_Qle_nat ＋ bk_Qmul_nat，照 AP 比率档同款） *)
  assert (HQcore : Qle ((2 # 1)%Q * C1 * a0) ((3 # 1)%Q * C0 * a1)).
  { assert (H1 : Qle ((Z.of_nat (2 * bkC (Datatypes.S (n + k)) n
                          * Datatypes.S (Datatypes.S k)) # 1)%Q)
                     ((Z.of_nat (3 * bkC (n + k) n
                          * Datatypes.S (Datatypes.S (Datatypes.S k))) # 1)%Q))
      by (apply bk_Qle_nat; exact Hnat).
    assert (HassocL : (2 * bkC (Datatypes.S (n + k)) n * Datatypes.S (Datatypes.S k))
                    = 2 * (bkC (Datatypes.S (n + k)) n * Datatypes.S (Datatypes.S k)))
      by ring.
    assert (HassocR : (3 * bkC (n + k) n * Datatypes.S (Datatypes.S (Datatypes.S k)))
                    = 3 * (bkC (n + k) n * Datatypes.S (Datatypes.S (Datatypes.S k))))
      by ring.
    rewrite HassocL, HassocR in H1.
    assert (E1 : (Z.of_nat (bkC (Datatypes.S (n + k)) n
                    * Datatypes.S (Datatypes.S k)) # 1)%Q
                 == (C1 * a0)%Q) by (symmetry; apply bk_Qmul_nat).
    assert (E2 : (Z.of_nat (bkC (n + k) n
                    * Datatypes.S (Datatypes.S (Datatypes.S k))) # 1)%Q
                 == (C0 * a1)%Q) by (symmetry; apply bk_Qmul_nat).
    rewrite <- (bk_Qmul_nat 2 (bkC (Datatypes.S (n + k)) n
                   * Datatypes.S (Datatypes.S k))) in H1.
    rewrite <- (bk_Qmul_nat 3 (bkC (n + k) n
                   * Datatypes.S (Datatypes.S (Datatypes.S k)))) in H1.
    rewrite E1, E2 in H1.
    change (Z.of_nat 2 # 1)%Q with (2 # 1)%Q in H1.
    change (Z.of_nat 3 # 1)%Q with (3 # 1)%Q in H1.
    assert (E3 : ((2 # 1)%Q * (C1 * a0))%Q == ((2 # 1)%Q * C1 * a0)%Q) by ring.
    assert (E4 : ((3 # 1)%Q * (C0 * a1))%Q == ((3 # 1)%Q * C0 * a1)%Q) by ring.
    rewrite E3, E4 in H1. exact H1. }
  (* 爆开形除消链（照 AP lnt_pterm_ratio 同款，仅 a0/a1 换档） *)
  assert (Hmain : Qle ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q)
                      (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q)).
  { assert (Hxz : ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))
                     * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                 == (C1 * (a0 * Qp))%Q).
    { assert (Hcert : Qinv (a1 * ((2 # 1)%Q * Qp))
                        * (a1 * ((2 # 1)%Q * Qp)) == 1%Q)
        by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Ha1HQ).
      rewrite <- Qmult_assoc.
      transitivity (C1 * ((Qinv (a1 * ((2 # 1)%Q * Qp))
                            * (a1 * ((2 # 1)%Q * Qp))) * (a0 * Qp)))%Q.
      - ring.
      - rewrite Hcert. ring. }
    assert (Hyz : (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                     * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                 == ((3 # 4)%Q * C0 * a1 * ((2 # 1)%Q * Qp))%Q).
    { assert (Hcert0 : Qinv (a0 * Qp) * (a0 * Qp) == 1%Q)
        by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Ha0Q).
      rewrite <- Qmult_assoc, <- Qmult_assoc.
      transitivity ((3 # 4)%Q * C0
                      * ((Qinv (a0 * Qp) * (a0 * Qp))
                           * (a1 * ((2 # 1)%Q * Qp))))%Q.
      - ring.
      - rewrite Hcert0. ring. }
    apply (lnt_qle_mul_cancel_r
      ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q)
      (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q)
      (((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp))%Q)).
    - apply Qmult_lt_0_compat; [exact Ha1HQ | exact Ha0Q].
    - apply (Qle_trans ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))
                          * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                (C1 * (a0 * Qp))%Q
                (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                    * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q).
      + apply qeq_le. exact Hxz.
      + apply (lnt_qle_mul_cancel_r (C1 * (a0 * Qp))%Q
          (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
             * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
          (((2 # 1)%Q * Qp))%Q).
        * apply Qmult_lt_0_compat;
            [apply rx_Qlt_Z1; lia | exact HQp].
        * apply (Qle_trans ((C1 * (a0 * Qp)) * ((2 # 1)%Q * Qp))%Q
                   (((2 # 1)%Q * C1 * a0) * (Qp * Qp))%Q
                   ((((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                       * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))
                      * ((2 # 1)%Q * Qp))%Q).
          -- apply qeq_le. ring.
          -- apply (Qle_trans (((2 # 1)%Q * C1 * a0) * (Qp * Qp))%Q
                     (((3 # 1)%Q * C0 * a1) * (Qp * Qp))%Q
                     ((((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                          * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))
                        * ((2 # 1)%Q * Qp))%Q).
             ++ apply Qmult_le_compat_r.
                ** exact HQcore.
                ** apply Qlt_le_weak. apply Qmult_lt_0_compat; exact HQp.
             ++ apply qeq_le. rewrite Hyz. ring. }
  (* 三段传送：爆开形与 lnw_uterm 形的 == 桥 + Hmain *)
  apply (Qle_trans (lnw_uterm n (Datatypes.S k))
           (C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q
           ((3 # 4)%Q * lnw_uterm n k)%Q).
  - apply qeq_le. exact HsS.
  - apply (Qle_trans _ ((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q _).
    + exact Hmain.
    + apply qeq_le.
      assert (Ey : ((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q
                 == ((3 # 4)%Q * lnw_uterm n k)%Q).
      { rewrite HsT. apply Qeq_refl. }
      exact Ey.
Qed.

(** u 肢纯比率档：二次键 ⟹ 线性键（2n ≤ k+4，lnt2_key_lin）⟹ AP 比率档
    直接使用——二次键带是线性窗的真子带，u 肢零新证。 *)
Theorem lnt2_pterm_ratio34 : forall n k : nat,
  2 * n * (k + 2) <= (k + 1) * (k + 5) ->
  QleT' (lnt_pterm n (Datatypes.S k)) ((3 # 4)%Q * lnt_pterm n k)%Q.
Proof.
  intros n k H. apply lnt_pterm_ratio.
  pose proof (lnt2_key_lin n k H). lia.
Qed.

(** w 纯比率步进：二次键 ⟹ w(n,k+1) ≤ (3/4)·w(n,k)——两肢比率同时 ≤ 3/4
    （u 经线性子带、ũ 经精确二次键），(1+t) 权的无常数吸收在此带内成立。
    诚实对照：lnw_wratio_refuted34 反例点 n=3,k=2 处键 2·3·4 = 24 > 21
    在带外——反例锚与本件键带互补一致，无矛盾。 *)
Theorem lnt2_wterm_step : forall n k : nat,
  2 * n * (k + 2) <= (k + 1) * (k + 5) ->
  QleT' (lnw_wterm n (Datatypes.S k)) ((3 # 4)%Q * lnw_wterm n k)%Q.
Proof.
  intros n k H.
  apply (qleT'_trans (lnw_wterm n (Datatypes.S k))
           ((lnt_pterm n (Datatypes.S k) + lnw_uterm n (Datatypes.S k))%Q)
           ((3 # 4)%Q * lnw_wterm n k)%Q).
  - apply qeq_leT'. reflexivity.
  - apply (qleT'_trans
             ((lnt_pterm n (Datatypes.S k) + lnw_uterm n (Datatypes.S k))%Q)
             (((3 # 4)%Q * lnt_pterm n k + (3 # 4)%Q * lnw_uterm n k)%Q)
             ((3 # 4)%Q * lnw_wterm n k)%Q).
    + apply qleT'_plus_compat;
        [apply lnt2_pterm_ratio34; exact H | apply lnt2_uterm_ratio34; exact H].
    + apply qeq_leT'. unfold lnw_wterm. ring.
Qed.

(** 核心⑪纯比率幂式（θ 上肢一阶形·键带版）：二次键 ⟹ w(n,k+j) ≤
    w(n,k)·(3/4)^j——无常数 2（对照 BV 核心⑤ lnw_wterm_pow 的 2· 配方：
    线性窗上纯比率被 n=3,k=2 反例钉死，二次键带内恢复纯几何率）。 *)
Theorem lnt2_wterm_pow_pure : forall (n k j : nat),
  2 * n * (k + 2) <= (k + 1) * (k + 5) ->
  QleT' (lnw_wterm n (k + j)) (lnw_wterm n k * q_pow (3 # 4)%Q j)%Q.
Proof.
  intros n k j H. induction j as [| j IHj].
  - apply lnt_leT'_eq_r with (y := (lnw_wterm n k * 1)%Q).
    + cbn [q_pow]. ring.
    + replace (k + 0) with k by lia. apply qeq_leT'. ring.
  - replace (k + Datatypes.S j) with (Datatypes.S (k + j)) by lia.
    apply lnt_leT'_eq_r with
      (y := (lnw_wterm n k * ((3 # 4)%Q * q_pow (3 # 4)%Q j))%Q).
    + rewrite q_pow_succ. apply Qeq_refl.
    + apply (qleT'_trans (lnw_wterm n (Datatypes.S (k + j)))
               ((3 # 4)%Q * lnw_wterm n (k + j))%Q
               (lnw_wterm n k * ((3 # 4)%Q * q_pow (3 # 4)%Q j))%Q).
      * apply lnt2_wterm_step.
        apply (lnt2_key_at n k (k + j)); [lia | exact H].
      * apply lnt_leT'_eq_r with
          (y := ((3 # 4)%Q * (lnw_wterm n k * q_pow (3 # 4)%Q j))%Q).
        -- ring.
        -- apply (qleT'_mult_compat_l (lnw_wterm n (k + j))
                     (lnw_wterm n k * q_pow (3 # 4)%Q j) (3 # 4)%Q
                     lnt_rho_le0 IHj).
Qed.

(** 数值锚③（键带纯比率实证）：n=3、k=6=2n（键 2·3·8 = 48 ≤ 7·11 = 77
    在带内）处 w(3,7) ≤ (3/4)·w(3,6)——同带 BV 件 lnw_wterm_pow 需 2·
    配方，纯比率在带内成立（vm_compute 判定）。 *)
Theorem lnt2_band_wterm_anchor : QleT' (lnw_wterm 3 7)
  ((3 # 4)%Q * lnw_wterm 3 6)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §C 组合肢：键带尾项控制＋加法隙＋C(n)ρ^M 终形（与 lnw_wgap_geo 同窗）    *)
(* ============================================================ *)

(** 核心⑫尾项控制·键带版：2n ≤ M+1 ⟹ Σ_{i<d} w(n,M+1+i) ≤ 4·w(n,M+1)——
    与 lnw_wgap_geo 同窗（2n ≤ M+1），对照 BV 核心⑥ lnw_wterm_tail
    同窗常数 8：二次键带下探减半。 *)
Theorem lnt2_wterm_tail_pure : forall (n M d : nat),
  2 * n <= M + 1 ->
  QleT' (sum_upto d (fun i : nat => lnw_wterm n (M + Datatypes.S i)))
        ((4 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q.
Proof.
  intros n M d H.
  assert (Hkey : 2 * n * (Datatypes.S M + 2)
               <= (Datatypes.S M + 1) * (Datatypes.S M + 5))
    by (apply lnt2_key_of_ge; lia).
  apply qleT'_trans with
    (lnw_wterm n (Datatypes.S M)
       * ((4 # 1)%Q * (1 - q_pow (3 # 4)%Q d)%Q))%Q.
  - apply lnt_leT'_eq_r with
      (y := sum_upto d (fun i : nat =>
                              (lnw_wterm n (Datatypes.S M)
                                  * q_pow (3 # 4)%Q i)%Q)).
    + rewrite lnt_sum_scale, lnt_geo_partial. apply Qeq_refl.
    + apply lnt_sum_le. intros i Hi.
      apply (qleT'_trans (lnw_wterm n (M + Datatypes.S i))
              (lnw_wterm n (Datatypes.S M + i))
              (lnw_wterm n (Datatypes.S M) * q_pow (3 # 4)%Q i)).
      * apply qeq_leT'.
        replace (M + Datatypes.S i) with (Datatypes.S M + i) by lia.
        apply Qeq_refl.
      * apply (lnt2_wterm_pow_pure n (Datatypes.S M) i).
        exact Hkey.
  - apply qleT'_trans with
      (lnw_wterm n (Datatypes.S M) * ((4 # 1)%Q * 1)%Q)%Q.
    + apply (qleT'_mult_compat_l ((4 # 1)%Q * (1 - q_pow (3 # 4)%Q d)%Q)
               ((4 # 1)%Q * 1)%Q (lnw_wterm n (Datatypes.S M))).
      * apply qltT_leT'. apply lnw_wterm_pos.
      * apply qleT'_mult_compat_l.
        { apply lnt_q4_le0. }
        { apply lnt_sub_le1. apply lnt_pow_pos_le. }
    + apply qeq_leT'. ring.
Qed.

(** 核心⑬加法隙·键带版：2n ≤ M+1 ⟹ S^w_{M+d} ≤ S^w_M + 4·w(n,M+1)——
    lnw_wgap_geo 架构的键带合成（对照 lnw_wterm_gap 常数 8）。 *)
Theorem lnt2_wgap_pure : forall (n M d : nat),
  2 * n <= M + 1 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnw_wterm n k))
        (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
           + (4 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q.
Proof.
  intros n M d H.
  apply (lnt_leT'_eq_l
    (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
       + sum_upto d (fun i : nat => lnw_wterm n (M + Datatypes.S i)))%Q
    (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnw_wterm n k))
    (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
       + (4 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q).
  - apply Qeq_sym. apply lnt_sum_range.
  - apply Qle_to_QleT'. apply Qplus_le_compat.
    + apply Qle_refl.
    + apply QleT'_to_Qle. apply lnt2_wterm_tail_pure. exact H.
Qed.

(** 核心⑭组合终形（θ 上肢一阶形·C(n)ρ^M 键带版）：1 ≤ n、2n ≤ M+1 ⟹
    尾隙 ≤ 2^{n+2}·(3/4)^{SM−2n}——与 lnw_wgap_geo 同窗同率（ρ = 3/4），
    C 从 2^{n+3} 下探 2^{n+2}（峰值账 2/1 不变、尾项账 8/4 减半的显式
    合成）——BV §诚实边界 2 预告的「下探空间」的显式收束。 *)
Theorem lnt2_wgap_geo_quarter : forall (n M d : nat),
  1 <= n -> 2 * n <= M + 1 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnw_wterm n k))
        (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
           + (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
                * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q.
Proof.
  intros n M d Hn HM.
  apply qleT'_trans with
    (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
       + ((4 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q)%Q.
  - apply lnt2_wgap_pure. exact HM.
  - apply qleT'_plus_compat.
    + apply qleT'_refl.
    + assert (Hkey2n : 2 * n * (2 * n + 2) <= (2 * n + 1) * (2 * n + 5))
        by (apply lnt2_key_of_ge; lia).
      assert (Hpow := lnt2_wterm_pow_pure n (2 * n)
                        (Datatypes.S M - 2 * n) Hkey2n).
      replace (2 * n + (Datatypes.S M - 2 * n)) with (Datatypes.S M) in Hpow
        by lia.
      assert (Hpk : QleT' (lnw_wterm n (2 * n)) (q_pow (2 # 1)%Q n))
        by (apply lnw_wterm_peak; exact Hn).
      assert (Hchain : QleT' (lnw_wterm n (Datatypes.S M))
                         (q_pow (2 # 1)%Q n
                            * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))).
      { apply qleT'_trans with
          ((lnw_wterm n (2 * n))
             * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q.
        - exact Hpow.
        - apply (qleT'_mult_compat_r (lnw_wterm n (2 * n))
                   (q_pow (2 # 1)%Q n)
                   (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))
                   (lnt_pow_pos_le (Datatypes.S M - 2 * n)) Hpk). }
      assert (Hxy : QleT' ((4 # 1)%Q * lnw_wterm n (Datatypes.S M))
                      (((4 # 1)%Q * q_pow (2 # 1)%Q n)
                         * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
      { apply qleT'_trans with
          ((4 # 1)%Q
             * (q_pow (2 # 1)%Q n
                  * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q.
        - apply (qleT'_mult_compat_l (lnw_wterm n (Datatypes.S M))
                   (q_pow (2 # 1)%Q n
                      * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)) (4 # 1)%Q
                   (lnt_q4_le0) Hchain).
        - apply qeq_leT'. ring. }
      assert (E42 : ((4 # 1)%Q * q_pow (2 # 1)%Q n)%Q
                   == q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))).
      { replace (Datatypes.S (Datatypes.S n)) with (2 + n) by lia.
        rewrite q_pow_add. cbn [q_pow]. ring. }
      apply (lnt_leT'_eq_r
        ((4 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q
        (((4 # 1)%Q * q_pow (2 # 1)%Q n)
           * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q
        (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
           * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
      * rewrite E42. apply Qeq_refl.
      * exact Hxy.
Qed.

(* ============================================================ *)
(* §D 假设审计与独立提取（born-green 四件套闭合位）                          *)
(* ============================================================ *)

Print Assumptions lnt2_sq_nonneg.
Print Assumptions lnt2_nat_cancel_r.
Print Assumptions lnt2_key_of_ge.
Print Assumptions lnt2_key_lin.
Print Assumptions lnt2_key_mono.
Print Assumptions lnt2_key_shift.
Print Assumptions lnt2_key_at.
Print Assumptions lnt2_pow_nonneg.
Print Assumptions lnt2_pow_mono.
Print Assumptions lnt2_pow_mul.
Print Assumptions lnt2_hquad.
Print Assumptions lnt2_hquad_pow.
Print Assumptions lnt2_theta_budget.
Print Assumptions lnt2_hquad_anchor.
Print Assumptions lnt2_theta_anchor.
Print Assumptions lnt2_uterm_ratio34.
Print Assumptions lnt2_pterm_ratio34.
Print Assumptions lnt2_wterm_step.
Print Assumptions lnt2_wterm_pow_pure.
Print Assumptions lnt2_band_wterm_anchor.
Print Assumptions lnt2_wterm_tail_pure.
Print Assumptions lnt2_wgap_pure.
Print Assumptions lnt2_wgap_geo_quarter.

From Stdlib Require Import Extraction.
Separate Extraction lnt2_hquad lnt2_theta_budget lnt2_theta_anchor
  lnt2_wterm_pow_pure lnt2_wgap_pure lnt2_wgap_geo_quarter
  lnt2_band_wterm_anchor.
