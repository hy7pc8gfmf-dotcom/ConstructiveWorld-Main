(* ==========================================================================)
   SymplecticRotationSpec.v — 辛旋转的幂速率精确律
   使命: srs_rot_characterization（旋转安全刻画）、srs_power_exact/power_exact_gen/power_rate（幂的精确与速率律）、srs_power_contract（压缩）、PairId 对称/传递/同余三件与 srs_pow_closed/pow_norm_transfer/renorm_rate。
   依赖: S01_BaseRing、S02_CauchyComplete、S12_B5RecycleSF、S13_NLiveAudit、UpReqSpec2x2；Stdlib QArith、QArith.Qabs、Arith。
   对标: 辛矩阵旋转的幂收敛速率（数值线性代数中 Givens 旋转的经典估计）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.  (* 注：QleT'/QleT'_to_Qle/Qle_to_QleT' 家在 S02，S13 Require 不传递 Import —— 名对位补引 *)
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import UpReqSpec2x2.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

Open Scope Q_scope.

Section SymplecticRotationSpec.

(* ============================================================ *)
(* A. 主件 srs_rot_characterization：旋转的特征刻画                *)
(*   c²+s² == 1  ⟺  rot (c,s) 保范 ∧ 保辛（双向）                 *)
(* ============================================================ *)

(* 旋转合格面（照 NSymplectic 语句面：QId 数值等同 + Set 层 And）。 *)
Definition srs_rot_safe (c s : Q) : Set :=
  And (forall p : (Q * Q)%type, QId (norms2 (rot c s p)) (norms2 p))
      (forall p q : (Q * Q)%type,
         QId (symp2 (rot c s p) (rot c s q)) (symp2 p q)).

(* 主件：正向 = 受体 rot_preserves_norm / rot_preserves_symp 组装；
   逆向 = 单位辛对 (1,0),(0,1) 的本征对论证：ω((1,0),(0,1)) = 1，
   旋转后 ω = c²+s²，保辛强加 c²+s² == 1（行列式论证的辛形式形态）。 *)
Theorem srs_rot_characterization :
  forall c s : Q,
    And (QId (c * c + s * s) 1 -> srs_rot_safe c s)
        (srs_rot_safe c s -> QId (c * c + s * s) 1).
Proof.
  intros c s. split.
  - (* 正向：c²+s² == 1 ⟹ 保范 ∧ 保辛（受体三件组装） *)
    intro Hcs. split.
    + intro p. exact (rot_preserves_norm c s p Hcs).
    + intros p q. exact (rot_preserves_symp c s p q Hcs).
  - (* 逆向：保范 + 保辛 ⟹ c²+s² == 1（只用保辛支，单位辛对） *)
    intros Hsafe. destruct Hsafe as [Hn Hs].
    pose proof (Hs (1%Q, 0%Q) (0%Q, 1%Q)) as Hu.
    assert (Hx : symp2 (rot c s (1%Q, 0%Q)) (rot c s (0%Q, 1%Q))
                 == (c * c + s * s)).
    { unfold symp2, rot. simpl. ring. }
    assert (Hy : symp2 (1%Q, 0%Q) (0%Q, 1%Q) == 1).
    { unfold symp2. simpl. ring. }
    apply qid_intro.
    assert (He := qid_elim _ _ Hu).
    rewrite Hx in He. rewrite Hy in He.
    exact He.
Qed.

(* ============================================================ *)
(* B. 幂与 n-速率（受体侧自证：rotⁿ 保范归纳是纯 nat 归纳）         *)
(* ============================================================ *)

(* 旋转幂（按 rot 逐次迭代）。 *)
Fixpoint srs_rot_pow (n : nat) (c s : Q) (p : (Q * Q)%type) : (Q * Q)%type :=
  match n with
  | O => p
  | Datatypes.S k => rot c s (srs_rot_pow k c s p)
  end.

(* Q 的 nat 次幂（乘法递归，与 sp2_q4pow 同型的一般底版）。 *)
Fixpoint srs_qnpow (n : nat) (q : Q) : Q :=
  match n with
  | O => 1%Q
  | Datatypes.S k => q * srs_qnpow k q
  end.

(* 单步放大恒等式（无前提）：‖rot p‖² == (c²+s²)·‖p‖²。 *)
Lemma srs_rot_amp : forall (c s : Q) (p : (Q * Q)%type),
  norms2 (rot c s p) == (c * c + s * s) * norms2 p.
Proof.
  intros c s p. unfold norms2, rot. simpl. ring.
Qed.

Lemma srs_qnpow_one : forall n : nat, srs_qnpow n 1 == 1.
Proof.
  induction n as [| k IH].
  - reflexivity.
  - cbn [srs_qnpow]. rewrite IH. reflexivity.
Qed.

(* 幂速率精确律（n-速率主件）：‖rotⁿ p‖² == (c²+s²)ⁿ·‖p‖²。
   每步放大因子恰为 q := c²+s²，n 步后 qⁿ——精确速率律。 *)
Theorem srs_power_exact :
  forall (n : nat) (c s : Q) (p : (Q * Q)%type),
    QId (norms2 (srs_rot_pow n c s p))
        (srs_qnpow n (c * c + s * s) * norms2 p).
Proof.
  intros n. induction n as [| k IH]; intros c s p.
  - cbn [srs_rot_pow srs_qnpow]. apply qid_intro. ring.
  - cbn [srs_rot_pow srs_qnpow].
    assert (Hamp : norms2 (rot c s (srs_rot_pow k c s p))
                   == (c * c + s * s) * norms2 (srs_rot_pow k c s p))
      by exact (srs_rot_amp c s (srs_rot_pow k c s p)).
    assert (Hi : norms2 (srs_rot_pow k c s p)
                 == srs_qnpow k (c * c + s * s) * norms2 p)
      by exact (qid_elim _ _ (IH c s p)).
    apply qid_intro.
    rewrite Hamp, Hi. ring.
Qed.

(* 幂速率精确律的推广基座：放大因子入口 q 任意（QId 桥入）。 *)
Lemma srs_power_exact_gen :
  forall (n : nat) (c s q : Q) (p : (Q * Q)%type),
    QId (c * c + s * s) q ->
    QId (norms2 (srs_rot_pow n c s p)) (srs_qnpow n q * norms2 p).
Proof.
  intros n. induction n as [| k IH]; intros c s q p Hq.
  - cbn [srs_rot_pow srs_qnpow]. apply qid_intro. ring.
  - cbn [srs_rot_pow srs_qnpow].
    assert (Hamp : norms2 (rot c s (srs_rot_pow k c s p))
                   == (c * c + s * s) * norms2 (srs_rot_pow k c s p))
      by exact (srs_rot_amp c s (srs_rot_pow k c s p)).
    assert (Hi : norms2 (srs_rot_pow k c s p)
                 == srs_qnpow k q * norms2 p)
      by exact (qid_elim _ _ (IH c s q p Hq)).
    apply qid_intro.
    rewrite Hamp.
    rewrite (qid_elim _ _ Hq), Hi. ring.
Qed.

(* 幂速率件：c²+s² == 1 ⟹ ‖rotⁿ p‖² == ‖p‖²（n 任意，幂保长）。 *)
Theorem srs_power_rate :
  forall (n : nat) (c s : Q) (p : (Q * Q)%type),
    QId (c * c + s * s) 1 ->
    QId (norms2 (srs_rot_pow n c s p)) (norms2 p).
Proof.
  intros n c s p Hq.
  pose proof (srs_power_exact_gen n c s 1 p Hq) as Hg.
  apply qid_intro.
  assert (Hm : srs_qnpow n 1 * norms2 p == norms2 p).
  { rewrite srs_qnpow_one. apply Qmult_1_l. }
  exact (Qeq_trans _ _ _ (qid_elim _ _ Hg) Hm).
Qed.

(* Q 平方非负（自证三行；Qmult_le_compat_r 双腰同腰版）。 *)
Lemma srs_qsq_nonneg : forall q : Q, Qle 0 (q * q).
Proof.
  intro q.
  assert (Habs : (q * q == Qabs q * Qabs q)%Q).
  { destruct (Qlt_le_dec 0 q) as [Hp | Hn].
    - rewrite (Qabs_pos q (Qlt_le_weak 0 q Hp)). reflexivity.
    - rewrite (Qabs_neg q Hn). ring. }
  assert (Hm : Qle (0 * Qabs q) (Qabs q * Qabs q)).
  { apply Qmult_le_compat_r; apply Qabs_nonneg. }
  rewrite Qmult_0_l in Hm. rewrite <- Habs in Hm. exact Hm.
Qed.

(* ‖p‖² ≥ 0。 *)
Lemma srs_norms2_nonneg : forall p : (Q * Q)%type, Qle 0 (norms2 p).
Proof.
  intro p. destruct p as [x y]. unfold norms2. simpl.
  assert (Hxy : Qle (0 + 0) (x * x + y * y)).
  { apply Qplus_le_compat; apply srs_qsq_nonneg. }
  rewrite Qplus_0_l in Hxy. exact Hxy.
Qed.

(* 0 ≤ q ≤ 1 ⟹ 0 < qⁿ ≤ 1 上界半边（收缩率引擎）。 *)
Lemma srs_qnpow_bnd : forall (n : nat) (q : Q),
  Qle 0 q -> Qle q 1 -> Qle (srs_qnpow n q) 1.
Proof.
  induction n as [| k IH]; intros q H0 H1.
  - cbn [srs_qnpow]. apply Qle_refl.
  - cbn [srs_qnpow].
    (* 注：9.1 Qmult_le_compat_r 双前提（x<=y -> 0<=z），补 qⁿ 非负支
       （stdlib 前提显式化税族，QArith_base:1279 Qmult_le_0_compat）。 *)
    assert (Hz : Qle 0 (srs_qnpow k q)).
    { clear IH.  (* 外层 IH 钉 k 会劫持内层归纳泛化（assumption 找不到 0≤qʲ 形） *)
      induction k as [| j Hzn].
      - (* 0 <= 1：Qle 实形 Z.le（QArith_base:49），走 leb 布尔判定 *)
        unfold Qle. apply Z.leb_le. vm_compute. reflexivity.
      - cbn [srs_qnpow]. apply Qmult_le_0_compat; assumption. }
    assert (Hstep : Qle (q * srs_qnpow k q) (1 * srs_qnpow k q)).
    { apply Qmult_le_compat_r; assumption. }
    rewrite Qmult_1_l in Hstep.
    exact (Qle_trans _ _ _ Hstep (IH q H0 H1)).
Qed.

(* 幂收缩件：q := c²+s² ≤ 1 且 q ≥ 0 ⟹ ‖rotⁿ p‖² ≤ ‖p‖²
   （n-速率上界：非单位旋转幂的范数不增判据）。 *)
Theorem srs_power_contract :
  forall (n : nat) (c s : Q) (p : (Q * Q)%type),
    QleT' (c * c + s * s) 1 -> QleT' 0 (c * c + s * s) ->
    QleT' (norms2 (srs_rot_pow n c s p)) (norms2 p).
Proof.
  intros n c s p H1 H0.
  assert (Hq1 : Qle (c * c + s * s) 1) by (apply QleT'_to_Qle; exact H1).
  assert (Hq0 : Qle 0 (c * c + s * s)) by (apply QleT'_to_Qle; exact H0).
  apply Qle_to_QleT'.
  assert (Hid : norms2 (srs_rot_pow n c s p)
                == srs_qnpow n (c * c + s * s) * norms2 p)
    by exact (qid_elim _ _ (srs_power_exact n c s p)).
  assert (Hb : Qle (srs_qnpow n (c * c + s * s) * norms2 p) (1 * norms2 p)).
  { apply Qmult_le_compat_r.
    - exact (srs_qnpow_bnd n (c * c + s * s) Hq0 Hq1).
    - apply srs_norms2_nonneg.  (* 注：compat_r 分支2 实为 0≤z 前提（非自反） *) }
  rewrite Qmult_1_l in Hb. rewrite Hid.
  exact Hb.
Qed.

(* ============================================================ *)
(* C. 支撑件：rotⁿ 闭式（cos/sin 倍角递推）+ 合成传递             *)
(* ============================================================ *)

(* PairId 对称 / 传递 / rot 同余（QId 逐腰移植）。 *)
Lemma srs_pair_sym : forall a b : (Q * Q)%type, PairId a b -> PairId b a.
Proof.
  intros a b [Hx Hy]. split; apply qid_intro.
  - exact (Qeq_sym _ _ (qid_elim _ _ Hx)).
  - exact (Qeq_sym _ _ (qid_elim _ _ Hy)).
Qed.

Lemma srs_pair_trans :
  forall a b c0 : (Q * Q)%type, PairId a b -> PairId b c0 -> PairId a c0.
Proof.
  intros a b c0 [H1 H2] [H3 H4]. split; apply qid_intro.
  - exact (Qeq_trans _ _ _ (qid_elim _ _ H1) (qid_elim _ _ H3)).
  - exact (Qeq_trans _ _ _ (qid_elim _ _ H2) (qid_elim _ _ H4)).
Qed.

Lemma srs_pair_rot_cong : forall (c s : Q) (a b : (Q * Q)%type),
  PairId a b -> PairId (rot c s a) (rot c s b).
Proof.
  intros c s a b [Hx Hy]. unfold PairId, rot. simpl.
  split; apply qid_intro.
  - rewrite (qid_elim _ _ Hx), (qid_elim _ _ Hy). ring.
  - rewrite (qid_elim _ _ Hx), (qid_elim _ _ Hy). ring.
Qed.

(* cos/sin 幂的倍角递推（rotⁿ 的 (cₙ, sₙ) 参数闭式）。 *)
Fixpoint srs_cos_pow (c s : Q) (n : nat) : Q :=
  match n with
  | O => 1%Q
  | Datatypes.S k => c * srs_cos_pow c s k - s * srs_sin_pow c s k
  end
with srs_sin_pow (c s : Q) (n : nat) : Q :=
  match n with
  | O => 0%Q
  | Datatypes.S k => s * srs_cos_pow c s k + c * srs_sin_pow c s k
  end.

(* 支撑件 1：rotⁿ 闭式——rotⁿ p == rot (cₙ) (sₙ) p（倍角递推 + 受体
   rot_compose 的矩阵乘归纳）。 *)
Theorem srs_pow_closed : forall (n : nat) (c s : Q) (p : (Q * Q)%type),
  PairId (srs_rot_pow n c s p)
         (rot (srs_cos_pow c s n) (srs_sin_pow c s n) p).
Proof.
  induction n as [| k IH]; intros c s p.
  - cbn [srs_rot_pow srs_cos_pow srs_sin_pow].
    unfold PairId, rot. simpl. split; apply qid_intro; ring.
  - cbn [srs_rot_pow srs_cos_pow srs_sin_pow].
    apply (srs_pair_trans _ _ _ (srs_pair_rot_cong c s _ _ (IH c s p))).
    apply srs_pair_sym.
    exact (rot_compose (srs_cos_pow c s k) (srs_sin_pow c s k) c s p).
Qed.

(* 支撑件 2：保范合成传递——rotⁿ 后再转一步，放大因子仍单步 q。 *)
Theorem srs_pow_norm_transfer :
  forall (n : nat) (c s : Q) (p : (Q * Q)%type),
    QId (norms2 (srs_rot_pow n c s (rot c s p)))
        ((c * c + s * s) * norms2 (srs_rot_pow n c s p)).
Proof.
  intros n c s p.
  assert (H1 : norms2 (srs_rot_pow n c s (rot c s p))
               == srs_qnpow n (c * c + s * s) * norms2 (rot c s p))
    by exact (qid_elim _ _ (srs_power_exact n c s (rot c s p))).
  assert (H2 : norms2 (rot c s p) == (c * c + s * s) * norms2 p)
    by exact (srs_rot_amp c s p).
  assert (H3 : norms2 (srs_rot_pow n c s p)
               == srs_qnpow n (c * c + s * s) * norms2 p)
    by exact (qid_elim _ _ (srs_power_exact n c s p)).
  apply qid_intro.
  rewrite H1, H2, H3. ring.
Qed.

(* ============================================================ *)
(* D. 供体接入：UpReqSpec2x2 sp2 速率引擎（/tmp 侧编通路）          *)
(*   把供体 Newton 开方率挂到旋转放大因子 D := c²+s² 上：            *)
(*   归一化旋转 (c/xₙ, s/xₙ)（xₙ := Newton 迭代）不放大范数          *)
(*   （D ≤ xₙ²），且残差 gapₙ·4ⁿ ≤ 3 指数收敛——旋转归一化速率。      *)
(* ============================================================ *)

(* 供体核件 Qle 级出口的 QleT' 化 + 旋转放大因子实例化。 *)
Theorem srs_renorm_rate : forall c s : Q,
  QleT 1 (c * c + s * s) -> QleT' (c * c + s * s) 4 -> forall n : nat,
  And (QleT' (c * c + s * s)
              (sp2_qnewton (c * c + s * s) 2 n
               * sp2_qnewton (c * c + s * s) 2 n))
      (QleT' (sp2_qgap (c * c + s * s) (sp2_qnewton (c * c + s * s) 2 n)
              * sp2_q4pow n) 3%Q).
Proof.
  intros c s H1 H4 n.
  assert (Hq1 : Qle 1 (c * c + s * s)).
  { destruct H1 as [Hl | Hr].
    - apply Qlt_le_weak. apply QltT_to_Qlt. exact Hl.
    - destruct Hr. apply Qle_refl. }
  assert (Hq4 : Qle (c * c + s * s) 4) by (apply QleT'_to_Qle; exact H4).
  destruct (sp2_qnewton_bnd (c * c + s * s) Hq1 Hq4 n) as [_ [_ HDle]].
  split.
  - (* 归一化旋转不放大范数：D ≤ xₙ²（供体 sp2_qnewton_bnd） *)
    apply Qle_to_QleT'. exact HDle.
  - (* 供体速率引擎：gapₙ·4ⁿ ≤ 3（sp2_sqrt_rate_core） *)
    apply Qle_to_QleT'.
    exact (sp2_sqrt_rate_core (c * c + s * s) Hq1 Hq4 n).
Qed.

(* 归一化亏损恒等式：1 − D/xₙ² == gapₙ/xₙ²（亏损恰为相对 gap，
   结合 gapₙ·4ⁿ ≤ 3 即亏损的 4ⁿ 指数上界形态）。 *)
Lemma srs_deficit_eq : forall D x : Q,
  ~ (x == 0)%Q -> (1 - D / (x * x)) == ((x * x - D) / (x * x)).
Proof.
  intros D x Hx0.
  assert (Hne : ~ ((x * x) == 0)%Q).
  { intro Hz. apply Qmult_integral in Hz.
    destruct Hz as [Hc | Hc]; exact (Hx0 Hc). }
  field. exact Hx0.  (* 注：field 伴随前提经 x² 自消后为 ~ x == 0，非 x²≠0 *)
Qed.

End SymplecticRotationSpec.

(* ============================================================ *)
(* G4 审查留痕：出口件全表 Print Assumptions                       *)
(* ============================================================ *)

Print Assumptions srs_rot_characterization.
Print Assumptions srs_power_exact.
Print Assumptions srs_power_exact_gen.
Print Assumptions srs_power_rate.
Print Assumptions srs_power_contract.
Print Assumptions srs_pow_closed.
Print Assumptions srs_pow_norm_transfer.
Print Assumptions srs_renorm_rate.
Print Assumptions srs_deficit_eq.
